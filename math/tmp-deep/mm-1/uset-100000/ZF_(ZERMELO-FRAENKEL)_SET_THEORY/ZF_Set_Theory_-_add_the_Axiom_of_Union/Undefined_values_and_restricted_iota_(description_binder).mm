$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Cantor_s_Theorem.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Undefined values and restricted iota (description binder)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c Undef $.

$c iota_ $.

$(Extend class notation with undefined value function. $)

${
	$v  $.
	a_cund $a class Undef $.
$}

$(Extend class notation with restricted description binder. $)

${
	$v ph x A  $.
	f0_crio $f wff ph $.
	f1_crio $f set x $.
	f2_crio $f class A $.
	a_crio $a class ( iota_ x e. A ph ) $.
$}

$(Define the undefined value function, whose value at set ` s ` is
     guaranteed not to be a member of ` s ` (see ~ pwuninel ).  (Contributed by
     NM, 15-Sep-2011.) $)

${
	$v s  $.
	f0_df-undef $f set s $.
	a_df-undef $a |- Undef = ( s e. _V |-> ~P U. s ) $.
$}

$(Direct proof of ~ pwuninel avoiding functions and thus several ZF axioms.
     (Contributed by Stefan O'Rear, 22-Feb-2015.) $)

${
	$v A V  $.
	f0_pwuninel2 $f class A $.
	f1_pwuninel2 $f class V $.
	p_pwuninel2 $p |- ( U. A e. V -> -. ~P U. A e. A ) $= f0_pwuninel2 a_cuni f1_pwuninel2 p_pwnss f0_pwuninel2 a_cuni a_cpw f0_pwuninel2 p_elssuni f0_pwuninel2 a_cuni f1_pwuninel2 a_wcel f0_pwuninel2 a_cuni a_cpw f0_pwuninel2 a_cuni a_wss f0_pwuninel2 a_cuni a_cpw f0_pwuninel2 a_wcel p_nsyl $.
$}

$(The power set of the union of a set does not belong to the set.  This
     theorem provides a way of constructing a new set that doesn't belong to a
     given set.  See also ~ pwuninel2 .  (Contributed by NM, 27-Jun-2008.)
     (Proof shortened by Mario Carneiro, 23-Dec-2016.) $)

${
	$v A  $.
	f0_pwuninel $f class A $.
	p_pwuninel $p |- -. ~P U. A e. A $= f0_pwuninel a_cuni a_cpw f0_pwuninel p_elex f0_pwuninel a_cuni p_pwexb f0_pwuninel a_cuni a_cpw f0_pwuninel a_wcel f0_pwuninel a_cuni a_cpw a_cvv a_wcel f0_pwuninel a_cuni a_cvv a_wcel p_sylibr f0_pwuninel a_cvv p_pwuninel2 f0_pwuninel a_cuni a_cpw f0_pwuninel a_wcel f0_pwuninel a_cuni a_cvv a_wcel f0_pwuninel a_cuni a_cpw f0_pwuninel a_wcel a_wn p_syl f0_pwuninel a_cuni a_cpw f0_pwuninel a_wcel a_wn p_id f0_pwuninel a_cuni a_cpw f0_pwuninel a_wcel f0_pwuninel a_cuni a_cpw f0_pwuninel a_wcel a_wn p_pm2.61i $.
$}

$(Value of the undefined value function.  Normally we will not reference
       the explicit value but will use ~ undefnel instead.  (Contributed by NM,
       15-Sep-2011.)  (Revised by Mario Carneiro, 24-Dec-2016.) $)

${
	$v S V  $.
	$d s S  $.
	f0_undefval $f class S $.
	f1_undefval $f class V $.
	i0_undefval $f set s $.
	p_undefval $p |- ( S e. V -> ( Undef ` S ) = ~P U. S ) $= f0_undefval f1_undefval p_elex f0_undefval f1_undefval p_uniexg f0_undefval a_cuni a_cvv p_pwexg f0_undefval f1_undefval a_wcel f0_undefval a_cuni a_cvv a_wcel f0_undefval a_cuni a_cpw a_cvv a_wcel p_syl i0_undefval a_sup_set_class f0_undefval p_unieq i0_undefval a_sup_set_class f0_undefval a_wceq i0_undefval a_sup_set_class a_cuni f0_undefval a_cuni p_pweqd i0_undefval a_df-undef i0_undefval f0_undefval i0_undefval a_sup_set_class a_cuni a_cpw f0_undefval a_cuni a_cpw a_cvv a_cvv a_cund p_fvmptg f0_undefval f1_undefval a_wcel f0_undefval a_cvv a_wcel f0_undefval a_cuni a_cpw a_cvv a_wcel f0_undefval a_cund a_cfv f0_undefval a_cuni a_cpw a_wceq p_syl2anc $.
$}

$(The undefined value generated from a set is not a member of the set.
     (Contributed by NM, 15-Sep-2011.) $)

${
	$v S V  $.
	f0_undefnel2 $f class S $.
	f1_undefnel2 $f class V $.
	p_undefnel2 $p |- ( S e. V -> -. ( Undef ` S ) e. S ) $= f0_undefnel2 p_pwuninel f0_undefnel2 f1_undefnel2 p_undefval f0_undefnel2 f1_undefnel2 a_wcel f0_undefnel2 a_cund a_cfv f0_undefnel2 a_cuni a_cpw f0_undefnel2 p_eleq1d f0_undefnel2 f1_undefnel2 a_wcel f0_undefnel2 a_cund a_cfv f0_undefnel2 a_wcel f0_undefnel2 a_cuni a_cpw f0_undefnel2 a_wcel p_mtbiri $.
$}

$(The undefined value generated from a set is not a member of the set.
     (Contributed by NM, 15-Sep-2011.) $)

${
	$v S V  $.
	f0_undefnel $f class S $.
	f1_undefnel $f class V $.
	p_undefnel $p |- ( S e. V -> ( Undef ` S ) e/ S ) $= f0_undefnel f1_undefnel p_undefnel2 f0_undefnel a_cund a_cfv f0_undefnel a_df-nel f0_undefnel f1_undefnel a_wcel f0_undefnel a_cund a_cfv f0_undefnel a_wcel a_wn f0_undefnel a_cund a_cfv f0_undefnel a_wnel p_sylibr $.
$}

$(Define restricted description binder.  In case it doesn't exist, we
       return a set which is not a member of the domain of discourse ` A ` .
       See also comments for ~ df-iota .  (Contributed by NM, 15-Sep-2011.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph x A  $.
	f0_df-riota $f wff ph $.
	f1_df-riota $f set x $.
	f2_df-riota $f class A $.
	a_df-riota $a |- ( iota_ x e. A ph ) = if ( E! x e. A ph , ( iota x ( x e. A /\ ph ) ) , ( Undef ` { x | x e. A } ) ) $.
$}

$(Formula-building deduction rule for iota.  (Contributed by NM,
       15-Sep-2011.) $)

${
	$v ph ps x A B  $.
	$d x ph  $.
	f0_riotaeqdv $f wff ph $.
	f1_riotaeqdv $f wff ps $.
	f2_riotaeqdv $f set x $.
	f3_riotaeqdv $f class A $.
	f4_riotaeqdv $f class B $.
	e0_riotaeqdv $e |- ( ph -> A = B ) $.
	p_riotaeqdv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ps ) ) $= e0_riotaeqdv f0_riotaeqdv f3_riotaeqdv f4_riotaeqdv f2_riotaeqdv a_sup_set_class p_eleq2d f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv p_anbi1d f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv p_eubidv f1_riotaeqdv f2_riotaeqdv f3_riotaeqdv a_df-reu f1_riotaeqdv f2_riotaeqdv f4_riotaeqdv a_df-reu f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_weu f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_weu f1_riotaeqdv f2_riotaeqdv f3_riotaeqdv a_wreu f1_riotaeqdv f2_riotaeqdv f4_riotaeqdv a_wreu p_3bitr4g e0_riotaeqdv f0_riotaeqdv f3_riotaeqdv f4_riotaeqdv f2_riotaeqdv a_sup_set_class p_eleq2d f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv p_anbi1d f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv p_iotabidv e0_riotaeqdv f0_riotaeqdv f3_riotaeqdv f4_riotaeqdv f2_riotaeqdv a_sup_set_class p_eleq2d f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f2_riotaeqdv p_abbidv f0_riotaeqdv f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f2_riotaeqdv a_cab f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f2_riotaeqdv a_cab a_cund p_fveq2d f0_riotaeqdv f1_riotaeqdv f2_riotaeqdv f3_riotaeqdv a_wreu f1_riotaeqdv f2_riotaeqdv f4_riotaeqdv a_wreu f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_cio f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f2_riotaeqdv a_cab a_cund a_cfv f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_cio f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f2_riotaeqdv a_cab a_cund a_cfv p_ifbieq12d f1_riotaeqdv f2_riotaeqdv f3_riotaeqdv a_df-riota f1_riotaeqdv f2_riotaeqdv f4_riotaeqdv a_df-riota f0_riotaeqdv f1_riotaeqdv f2_riotaeqdv f3_riotaeqdv a_wreu f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_cio f2_riotaeqdv a_sup_set_class f3_riotaeqdv a_wcel f2_riotaeqdv a_cab a_cund a_cfv a_cif f1_riotaeqdv f2_riotaeqdv f4_riotaeqdv a_wreu f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f1_riotaeqdv a_wa f2_riotaeqdv a_cio f2_riotaeqdv a_sup_set_class f4_riotaeqdv a_wcel f2_riotaeqdv a_cab a_cund a_cfv a_cif f1_riotaeqdv f2_riotaeqdv f3_riotaeqdv a_crio f1_riotaeqdv f2_riotaeqdv f4_riotaeqdv a_crio p_3eqtr4g $.
$}

$(Formula-building deduction rule for restricted iota.  (Contributed by
       NM, 15-Sep-2011.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_riotabidv $f wff ph $.
	f1_riotabidv $f wff ps $.
	f2_riotabidv $f wff ch $.
	f3_riotabidv $f set x $.
	f4_riotabidv $f class A $.
	e0_riotabidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_riotabidv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) ) $= e0_riotabidv f0_riotabidv f1_riotabidv f2_riotabidv f3_riotabidv f4_riotabidv p_reubidv e0_riotabidv f0_riotabidv f1_riotabidv f2_riotabidv f3_riotabidv a_sup_set_class f4_riotabidv a_wcel p_anbi2d f0_riotabidv f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f1_riotabidv a_wa f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f2_riotabidv a_wa f3_riotabidv p_iotabidv f0_riotabidv f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f3_riotabidv a_cab a_cund a_cfv p_eqidd f0_riotabidv f1_riotabidv f3_riotabidv f4_riotabidv a_wreu f2_riotabidv f3_riotabidv f4_riotabidv a_wreu f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f1_riotabidv a_wa f3_riotabidv a_cio f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f3_riotabidv a_cab a_cund a_cfv f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f2_riotabidv a_wa f3_riotabidv a_cio f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f3_riotabidv a_cab a_cund a_cfv p_ifbieq12d f1_riotabidv f3_riotabidv f4_riotabidv a_df-riota f2_riotabidv f3_riotabidv f4_riotabidv a_df-riota f0_riotabidv f1_riotabidv f3_riotabidv f4_riotabidv a_wreu f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f1_riotabidv a_wa f3_riotabidv a_cio f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f3_riotabidv a_cab a_cund a_cfv a_cif f2_riotabidv f3_riotabidv f4_riotabidv a_wreu f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f2_riotabidv a_wa f3_riotabidv a_cio f3_riotabidv a_sup_set_class f4_riotabidv a_wcel f3_riotabidv a_cab a_cund a_cfv a_cif f1_riotabidv f3_riotabidv f4_riotabidv a_crio f2_riotabidv f3_riotabidv f4_riotabidv a_crio p_3eqtr4g $.
$}

$(Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 15-Sep-2011.) $)

${
	$v ph ps ch x A B  $.
	$d x ph  $.
	f0_riotaeqbidv $f wff ph $.
	f1_riotaeqbidv $f wff ps $.
	f2_riotaeqbidv $f wff ch $.
	f3_riotaeqbidv $f set x $.
	f4_riotaeqbidv $f class A $.
	f5_riotaeqbidv $f class B $.
	e0_riotaeqbidv $e |- ( ph -> A = B ) $.
	e1_riotaeqbidv $e |- ( ph -> ( ps <-> ch ) ) $.
	p_riotaeqbidv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ch ) ) $= e1_riotaeqbidv f0_riotaeqbidv f1_riotaeqbidv f2_riotaeqbidv f3_riotaeqbidv f4_riotaeqbidv p_riotabidv e0_riotaeqbidv f0_riotaeqbidv f2_riotaeqbidv f3_riotaeqbidv f4_riotaeqbidv f5_riotaeqbidv p_riotaeqdv f0_riotaeqbidv f1_riotaeqbidv f3_riotaeqbidv f4_riotaeqbidv a_crio f2_riotaeqbidv f3_riotaeqbidv f4_riotaeqbidv a_crio f2_riotaeqbidv f3_riotaeqbidv f5_riotaeqbidv a_crio p_eqtrd $.
$}

$(Restricted iota is a set.  (Contributed by NM, 15-Sep-2011.) $)

${
	$v ps x A  $.
	f0_riotaex $f wff ps $.
	f1_riotaex $f set x $.
	f2_riotaex $f class A $.
	p_riotaex $p |- ( iota_ x e. A ps ) e. _V $= f0_riotaex f1_riotaex f2_riotaex a_df-riota f1_riotaex a_sup_set_class f2_riotaex a_wcel f0_riotaex a_wa f1_riotaex p_iotaex f1_riotaex a_sup_set_class f2_riotaex a_wcel f1_riotaex a_cab a_cund p_fvex f0_riotaex f1_riotaex f2_riotaex a_wreu f1_riotaex a_sup_set_class f2_riotaex a_wcel f0_riotaex a_wa f1_riotaex a_cio f1_riotaex a_sup_set_class f2_riotaex a_wcel f1_riotaex a_cab a_cund a_cfv p_ifex f0_riotaex f1_riotaex f2_riotaex a_crio f0_riotaex f1_riotaex f2_riotaex a_wreu f1_riotaex a_sup_set_class f2_riotaex a_wcel f0_riotaex a_wa f1_riotaex a_cio f1_riotaex a_sup_set_class f2_riotaex a_wcel f1_riotaex a_cab a_cund a_cfv a_cif a_cvv p_eqeltri $.
$}

$(An iota restricted to the universe is unrestricted.  (Contributed by NM,
     18-Sep-2011.) $)

${
	$v ph x  $.
	f0_riotav $f wff ph $.
	f1_riotav $f set x $.
	p_riotav $p |- ( iota_ x e. _V ph ) = ( iota x ph ) $= f0_riotav f1_riotav a_cvv a_df-riota f0_riotav f1_riotav a_cvv a_wreu f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv p_iftrue f1_riotav p_vex f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav p_biantrur f0_riotav f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav p_iotabii f0_riotav f1_riotav a_cvv a_wreu f0_riotav f1_riotav a_cvv a_wreu f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv a_cif f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f0_riotav f1_riotav a_cio p_syl6reqr f0_riotav f1_riotav p_reuv f0_riotav f1_riotav p_iotanul f0_riotav f1_riotav a_cvv a_wreu f0_riotav f1_riotav a_weu f0_riotav f1_riotav a_cio a_c0 a_wceq p_sylnbi f1_riotav a_cvv p_abid2 f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cvv a_cund p_fveq2i p_vprc a_cvv a_cund p_fvprc a_cvv a_cvv a_wcel a_wn a_cvv a_cund a_cfv a_c0 a_wceq a_ax-mp f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv a_cvv a_cund a_cfv a_c0 p_eqtri f0_riotav f1_riotav a_cvv a_wreu a_wn f0_riotav f1_riotav a_cio a_c0 f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv p_syl6eqr f0_riotav f1_riotav a_cvv a_wreu f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv p_iffalse f0_riotav f1_riotav a_cvv a_wreu a_wn f0_riotav f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv f0_riotav f1_riotav a_cvv a_wreu f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv a_cif p_eqtr4d f0_riotav f1_riotav a_cvv a_wreu f0_riotav f1_riotav a_cio f0_riotav f1_riotav a_cvv a_wreu f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv a_cif a_wceq p_pm2.61i f0_riotav f1_riotav a_cvv a_crio f0_riotav f1_riotav a_cvv a_wreu f1_riotav a_sup_set_class a_cvv a_wcel f0_riotav a_wa f1_riotav a_cio f1_riotav a_sup_set_class a_cvv a_wcel f1_riotav a_cab a_cund a_cfv a_cif f0_riotav f1_riotav a_cio p_eqtr4i $.
$}

$(Restricted iota in terms of iota.  (Contributed by NM, 15-Sep-2011.) $)

${
	$v ph x A  $.
	f0_riotaiota $f wff ph $.
	f1_riotaiota $f set x $.
	f2_riotaiota $f class A $.
	p_riotaiota $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) ) ) $= f0_riotaiota f1_riotaiota f2_riotaiota a_df-riota f0_riotaiota f1_riotaiota f2_riotaiota a_wreu f1_riotaiota a_sup_set_class f2_riotaiota a_wcel f0_riotaiota a_wa f1_riotaiota a_cio f1_riotaiota a_sup_set_class f2_riotaiota a_wcel f1_riotaiota a_cab a_cund a_cfv p_iftrue f0_riotaiota f1_riotaiota f2_riotaiota a_wreu f0_riotaiota f1_riotaiota f2_riotaiota a_crio f0_riotaiota f1_riotaiota f2_riotaiota a_wreu f1_riotaiota a_sup_set_class f2_riotaiota a_wcel f0_riotaiota a_wa f1_riotaiota a_cio f1_riotaiota a_sup_set_class f2_riotaiota a_wcel f1_riotaiota a_cab a_cund a_cfv a_cif f1_riotaiota a_sup_set_class f2_riotaiota a_wcel f0_riotaiota a_wa f1_riotaiota a_cio p_syl5eq $.
$}

$(Restricted iota in terms of class union.  (Contributed by NM,
     11-Oct-2011.) $)

${
	$v ph x A  $.
	f0_riotauni $f wff ph $.
	f1_riotauni $f set x $.
	f2_riotauni $f class A $.
	p_riotauni $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) = U. { x e. A | ph } ) $= f0_riotauni f1_riotauni f2_riotauni p_riotaiota f0_riotauni f1_riotauni f2_riotauni a_df-reu f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni p_iotauni f0_riotauni f1_riotauni f2_riotauni a_wreu f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_weu f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_cio f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_cab a_cuni a_wceq p_sylbi f0_riotauni f1_riotauni f2_riotauni a_df-rab f0_riotauni f1_riotauni f2_riotauni a_crab f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_cab p_unieqi f0_riotauni f1_riotauni f2_riotauni a_wreu f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_cio f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_cab a_cuni f0_riotauni f1_riotauni f2_riotauni a_crab a_cuni p_syl6eqr f0_riotauni f1_riotauni f2_riotauni a_wreu f0_riotauni f1_riotauni f2_riotauni a_crio f1_riotauni a_sup_set_class f2_riotauni a_wcel f0_riotauni a_wa f1_riotauni a_cio f0_riotauni f1_riotauni f2_riotauni a_crab a_cuni p_eqtrd $.
$}

$(The abstraction variable in a restricted iota descriptor isn't free.
       (Contributed by NM, 12-Oct-2011.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d ph  $.
	f0_nfriota1 $f wff ph $.
	f1_nfriota1 $f set x $.
	f2_nfriota1 $f class A $.
	p_nfriota1 $p |- F/_ x ( iota_ x e. A ph ) $= f0_nfriota1 f1_nfriota1 f2_nfriota1 a_df-riota f0_nfriota1 f1_nfriota1 f2_nfriota1 p_nfreu1 f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f0_nfriota1 a_wa f1_nfriota1 p_nfiota1 f1_nfriota1 a_cund p_nfcv f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f1_nfriota1 p_nfab1 f1_nfriota1 f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f1_nfriota1 a_cab a_cund p_nffv f0_nfriota1 f1_nfriota1 f2_nfriota1 a_wreu f1_nfriota1 f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f0_nfriota1 a_wa f1_nfriota1 a_cio f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f1_nfriota1 a_cab a_cund a_cfv p_nfif f1_nfriota1 f0_nfriota1 f1_nfriota1 f2_nfriota1 a_crio f0_nfriota1 f1_nfriota1 f2_nfriota1 a_wreu f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f0_nfriota1 a_wa f1_nfriota1 a_cio f1_nfriota1 a_sup_set_class f2_nfriota1 a_wcel f1_nfriota1 a_cab a_cund a_cfv a_cif p_nfcxfr $.
$}

$(Deduction version of ~ nfriota .  (Contributed by NM, 18-Feb-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x y A  $.
	f0_nfriotad $f wff ph $.
	f1_nfriotad $f wff ps $.
	f2_nfriotad $f set x $.
	f3_nfriotad $f set y $.
	f4_nfriotad $f class A $.
	e0_nfriotad $e |- F/ y ph $.
	e1_nfriotad $e |- ( ph -> F/ x ps ) $.
	e2_nfriotad $e |- ( ph -> F/_ x A ) $.
	p_nfriotad $p |- ( ph -> F/_ x ( iota_ y e. A ps ) ) $= f1_nfriotad f3_nfriotad f4_nfriotad a_df-riota e0_nfriotad e2_nfriotad e1_nfriotad f0_nfriotad f1_nfriotad f2_nfriotad f3_nfriotad f4_nfriotad p_nfreud e0_nfriotad f2_nfriotad f3_nfriotad f3_nfriotad p_nfnae f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn f3_nfriotad p_nfan f2_nfriotad f3_nfriotad p_nfcvf f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn f2_nfriotad f3_nfriotad a_sup_set_class a_wnfc f0_nfriotad p_adantl e2_nfriotad f0_nfriotad f2_nfriotad f4_nfriotad a_wnfc f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn p_adantr f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn a_wa f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad p_nfeld e1_nfriotad f0_nfriotad f1_nfriotad f2_nfriotad a_wnf f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn p_adantr f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn a_wa f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad f2_nfriotad p_nfand f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn a_wa f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f2_nfriotad f3_nfriotad p_nfiotad f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio a_wnfc p_ex f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad p_nfiota1 f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio p_eqidd f2_nfriotad f3_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio p_drnfc1 f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio a_wnfc f3_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio a_wnfc p_mpbiri f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio a_wnfc p_pm2.61d2 f0_nfriotad f2_nfriotad a_cund p_nfcvd e0_nfriotad f2_nfriotad f3_nfriotad p_nfcvf f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn f2_nfriotad f3_nfriotad a_sup_set_class a_wnfc f0_nfriotad p_adantl e2_nfriotad f0_nfriotad f2_nfriotad f4_nfriotad a_wnfc f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn p_adantr f0_nfriotad f2_nfriotad a_sup_set_class f3_nfriotad a_sup_set_class a_wceq f2_nfriotad a_wal a_wn a_wa f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad p_nfeld f0_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f2_nfriotad f3_nfriotad p_nfabd2 f0_nfriotad f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f3_nfriotad a_cab a_cund p_nffvd f0_nfriotad f1_nfriotad f3_nfriotad f4_nfriotad a_wreu f2_nfriotad f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f3_nfriotad a_cab a_cund a_cfv p_nfifd f0_nfriotad f2_nfriotad f1_nfriotad f3_nfriotad f4_nfriotad a_crio f1_nfriotad f3_nfriotad f4_nfriotad a_wreu f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f1_nfriotad a_wa f3_nfriotad a_cio f3_nfriotad a_sup_set_class f4_nfriotad a_wcel f3_nfriotad a_cab a_cund a_cfv a_cif p_nfcxfrd $.
$}

$(A variable not free in a wff remains so in a restricted iota
       descriptor.  (Contributed by NM, 12-Oct-2011.) $)

${
	$v ph x y A  $.
	$d x y  $.
	$d A  $.
	$d ph  $.
	f0_nfriota $f wff ph $.
	f1_nfriota $f set x $.
	f2_nfriota $f set y $.
	f3_nfriota $f class A $.
	e0_nfriota $e |- F/ x ph $.
	e1_nfriota $e |- F/_ x A $.
	p_nfriota $p |- F/_ x ( iota_ y e. A ph ) $= f2_nfriota p_nftru e0_nfriota f0_nfriota f1_nfriota a_wnf a_wtru p_a1i e1_nfriota f1_nfriota f3_nfriota a_wnfc a_wtru p_a1i a_wtru f0_nfriota f1_nfriota f2_nfriota f3_nfriota p_nfriotad f1_nfriota f0_nfriota f2_nfriota f3_nfriota a_crio a_wnfc p_trud $.
$}

$(Change bound variable in a restricted description binder.  (Contributed
       by NM, 18-Mar-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x z A  $.
	$d y z A  $.
	$d z ph  $.
	$d z ps  $.
	f0_cbvriota $f wff ph $.
	f1_cbvriota $f wff ps $.
	f2_cbvriota $f set x $.
	f3_cbvriota $f set y $.
	f4_cbvriota $f class A $.
	i0_cbvriota $f set z $.
	e0_cbvriota $e |- F/ y ph $.
	e1_cbvriota $e |- F/ x ps $.
	e2_cbvriota $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvriota $p |- ( iota_ x e. A ph ) = ( iota_ y e. A ps ) $= e0_cbvriota e1_cbvriota e2_cbvriota f0_cbvriota f1_cbvriota f2_cbvriota f3_cbvriota f4_cbvriota p_cbvreu f2_cbvriota a_sup_set_class i0_cbvriota a_sup_set_class f4_cbvriota p_eleq1 f0_cbvriota f2_cbvriota i0_cbvriota p_sbequ12 f2_cbvriota a_sup_set_class i0_cbvriota a_sup_set_class a_wceq f2_cbvriota a_sup_set_class f4_cbvriota a_wcel i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f0_cbvriota f2_cbvriota i0_cbvriota a_wsb p_anbi12d f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota a_wa i0_cbvriota p_nfv i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f2_cbvriota p_nfv f0_cbvriota f2_cbvriota i0_cbvriota p_nfs1v i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f2_cbvriota i0_cbvriota a_wsb f2_cbvriota p_nfan f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota a_wa i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f2_cbvriota i0_cbvriota a_wsb a_wa f2_cbvriota i0_cbvriota p_cbviota i0_cbvriota a_sup_set_class f3_cbvriota a_sup_set_class f4_cbvriota p_eleq1 f0_cbvriota i0_cbvriota f3_cbvriota f2_cbvriota p_sbequ e1_cbvriota e2_cbvriota f0_cbvriota f1_cbvriota f2_cbvriota f3_cbvriota p_sbie i0_cbvriota a_sup_set_class f3_cbvriota a_sup_set_class a_wceq f0_cbvriota f2_cbvriota i0_cbvriota a_wsb f0_cbvriota f2_cbvriota f3_cbvriota a_wsb f1_cbvriota p_syl6bb i0_cbvriota a_sup_set_class f3_cbvriota a_sup_set_class a_wceq i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f2_cbvriota i0_cbvriota a_wsb f1_cbvriota p_anbi12d i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f3_cbvriota p_nfv e0_cbvriota f0_cbvriota f2_cbvriota i0_cbvriota f3_cbvriota p_nfsb i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f2_cbvriota i0_cbvriota a_wsb f3_cbvriota p_nfan f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f1_cbvriota a_wa i0_cbvriota p_nfv i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f2_cbvriota i0_cbvriota a_wsb a_wa f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f1_cbvriota a_wa i0_cbvriota f3_cbvriota p_cbviota f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota a_wa f2_cbvriota a_cio i0_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota f2_cbvriota i0_cbvriota a_wsb a_wa i0_cbvriota a_cio f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f1_cbvriota a_wa f3_cbvriota a_cio p_eqtri f2_cbvriota f4_cbvriota p_abid2 f3_cbvriota f4_cbvriota p_abid2 f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f2_cbvriota a_cab f4_cbvriota f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f3_cbvriota a_cab p_eqtr4i f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f2_cbvriota a_cab f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f3_cbvriota a_cab a_cund p_fveq2i f0_cbvriota f2_cbvriota f4_cbvriota a_wreu f1_cbvriota f3_cbvriota f4_cbvriota a_wreu f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota a_wa f2_cbvriota a_cio f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f2_cbvriota a_cab a_cund a_cfv f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f1_cbvriota a_wa f3_cbvriota a_cio f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f3_cbvriota a_cab a_cund a_cfv p_ifbieq12i f0_cbvriota f2_cbvriota f4_cbvriota a_df-riota f1_cbvriota f3_cbvriota f4_cbvriota a_df-riota f0_cbvriota f2_cbvriota f4_cbvriota a_wreu f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f0_cbvriota a_wa f2_cbvriota a_cio f2_cbvriota a_sup_set_class f4_cbvriota a_wcel f2_cbvriota a_cab a_cund a_cfv a_cif f1_cbvriota f3_cbvriota f4_cbvriota a_wreu f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f1_cbvriota a_wa f3_cbvriota a_cio f3_cbvriota a_sup_set_class f4_cbvriota a_wcel f3_cbvriota a_cab a_cund a_cfv a_cif f0_cbvriota f2_cbvriota f4_cbvriota a_crio f1_cbvriota f3_cbvriota f4_cbvriota a_crio p_3eqtr4i $.
$}

$(Change bound variable in a restricted description binder.  (Contributed
       by NM, 18-Mar-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x y A  $.
	$d x A  $.
	$d y A  $.
	$d y ph  $.
	$d x ps  $.
	f0_cbvriotav $f wff ph $.
	f1_cbvriotav $f wff ps $.
	f2_cbvriotav $f set x $.
	f3_cbvriotav $f set y $.
	f4_cbvriotav $f class A $.
	e0_cbvriotav $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_cbvriotav $p |- ( iota_ x e. A ph ) = ( iota_ y e. A ps ) $= f0_cbvriotav f3_cbvriotav p_nfv f1_cbvriotav f2_cbvriotav p_nfv e0_cbvriotav f0_cbvriotav f1_cbvriotav f2_cbvriotav f3_cbvriotav f4_cbvriotav p_cbvriota $.
$}

$(Interchange class substitution and restricted description binder.
       (Contributed by NM, 24-Feb-2013.) $)

${
	$v ph x y A B V  $.
	$d y z A  $.
	$d x z B  $.
	$d z ph  $.
	$d x y  $.
	f0_csbriotag $f wff ph $.
	f1_csbriotag $f set x $.
	f2_csbriotag $f set y $.
	f3_csbriotag $f class A $.
	f4_csbriotag $f class B $.
	f5_csbriotag $f class V $.
	i0_csbriotag $f set z $.
	p_csbriotag $p |- ( A e. V -> [_ A / x ]_ ( iota_ y e. B ph ) = ( iota_ y e. B [. A / x ]. ph ) ) $= f1_csbriotag i0_csbriotag a_sup_set_class f3_csbriotag f0_csbriotag f2_csbriotag f4_csbriotag a_crio p_csbeq1 f0_csbriotag f1_csbriotag i0_csbriotag f3_csbriotag p_dfsbcq2 i0_csbriotag a_sup_set_class f3_csbriotag a_wceq f0_csbriotag f1_csbriotag i0_csbriotag a_wsb f0_csbriotag f1_csbriotag f3_csbriotag a_wsbc f2_csbriotag f4_csbriotag p_riotabidv i0_csbriotag a_sup_set_class f3_csbriotag a_wceq f1_csbriotag i0_csbriotag a_sup_set_class f0_csbriotag f2_csbriotag f4_csbriotag a_crio a_csb f1_csbriotag f3_csbriotag f0_csbriotag f2_csbriotag f4_csbriotag a_crio a_csb f0_csbriotag f1_csbriotag i0_csbriotag a_wsb f2_csbriotag f4_csbriotag a_crio f0_csbriotag f1_csbriotag f3_csbriotag a_wsbc f2_csbriotag f4_csbriotag a_crio p_eqeq12d i0_csbriotag p_vex f0_csbriotag f1_csbriotag i0_csbriotag p_nfs1v f1_csbriotag f4_csbriotag p_nfcv f0_csbriotag f1_csbriotag i0_csbriotag a_wsb f1_csbriotag f2_csbriotag f4_csbriotag p_nfriota f0_csbriotag f1_csbriotag i0_csbriotag p_sbequ12 f1_csbriotag a_sup_set_class i0_csbriotag a_sup_set_class a_wceq f0_csbriotag f0_csbriotag f1_csbriotag i0_csbriotag a_wsb f2_csbriotag f4_csbriotag p_riotabidv f1_csbriotag i0_csbriotag a_sup_set_class f0_csbriotag f2_csbriotag f4_csbriotag a_crio f0_csbriotag f1_csbriotag i0_csbriotag a_wsb f2_csbriotag f4_csbriotag a_crio p_csbief f1_csbriotag i0_csbriotag a_sup_set_class f0_csbriotag f2_csbriotag f4_csbriotag a_crio a_csb f0_csbriotag f1_csbriotag i0_csbriotag a_wsb f2_csbriotag f4_csbriotag a_crio a_wceq f1_csbriotag f3_csbriotag f0_csbriotag f2_csbriotag f4_csbriotag a_crio a_csb f0_csbriotag f1_csbriotag f3_csbriotag a_wsbc f2_csbriotag f4_csbriotag a_crio a_wceq i0_csbriotag f3_csbriotag f5_csbriotag p_vtoclg $.
$}

$(Membership law for "the unique element in ` A ` such that ` ph ` ."

     This can useful for expanding an iota-based definition (see ~ df-iota ).
     If you have an unbounded iota, ~ iotacl may be useful.

     (Contributed by NM, 21-Aug-2011.)  (Revised by Mario Carneiro,
     23-Dec-2016.) $)

${
	$v ph x A  $.
	f0_riotacl2 $f wff ph $.
	f1_riotacl2 $f set x $.
	f2_riotacl2 $f class A $.
	p_riotacl2 $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. { x e. A | ph } ) $= f0_riotacl2 f1_riotacl2 f2_riotacl2 p_riotaiota f0_riotacl2 f1_riotacl2 f2_riotacl2 a_df-reu f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 p_iotacl f0_riotacl2 f1_riotacl2 f2_riotacl2 a_wreu f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 a_weu f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 a_cio f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 a_cab a_wcel p_sylbi f0_riotacl2 f1_riotacl2 f2_riotacl2 a_df-rab f0_riotacl2 f1_riotacl2 f2_riotacl2 a_wreu f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 a_cio f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 a_cab f0_riotacl2 f1_riotacl2 f2_riotacl2 a_crab p_syl6eleqr f0_riotacl2 f1_riotacl2 f2_riotacl2 a_wreu f0_riotacl2 f1_riotacl2 f2_riotacl2 a_crio f1_riotacl2 a_sup_set_class f2_riotacl2 a_wcel f0_riotacl2 a_wa f1_riotacl2 a_cio f0_riotacl2 f1_riotacl2 f2_riotacl2 a_crab p_eqeltrd $.
$}

$(Closure of restricted iota.  (Contributed by NM, 21-Aug-2011.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riotacl $f wff ph $.
	f1_riotacl $f set x $.
	f2_riotacl $f class A $.
	p_riotacl $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. A ) $= f0_riotacl f1_riotacl f2_riotacl p_ssrab2 f0_riotacl f1_riotacl f2_riotacl p_riotacl2 f0_riotacl f1_riotacl f2_riotacl a_wreu f0_riotacl f1_riotacl f2_riotacl a_crab f2_riotacl f0_riotacl f1_riotacl f2_riotacl a_crio p_sseldi $.
$}

$(Substitution law for descriptions.  Compare ~ iotasbc .  (Contributed by
     NM, 23-Aug-2011.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x A  $.
	f0_riotasbc $f wff ph $.
	f1_riotasbc $f set x $.
	f2_riotasbc $f class A $.
	p_riotasbc $p |- ( E! x e. A ph -> [. ( iota_ x e. A ph ) / x ]. ph ) $= f0_riotasbc f1_riotasbc f2_riotasbc p_rabssab f0_riotasbc f1_riotasbc f2_riotasbc p_riotacl2 f0_riotasbc f1_riotasbc f2_riotasbc a_wreu f0_riotasbc f1_riotasbc f2_riotasbc a_crab f0_riotasbc f1_riotasbc a_cab f0_riotasbc f1_riotasbc f2_riotasbc a_crio p_sseldi f0_riotasbc f1_riotasbc f0_riotasbc f1_riotasbc f2_riotasbc a_crio a_df-sbc f0_riotasbc f1_riotasbc f2_riotasbc a_wreu f0_riotasbc f1_riotasbc f2_riotasbc a_crio f0_riotasbc f1_riotasbc a_cab a_wcel f0_riotasbc f1_riotasbc f0_riotasbc f1_riotasbc f2_riotasbc a_crio a_wsbc p_sylibr $.
$}

$(Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  ( ~ rabbidva analog.)  (Contributed by NM, 17-Jan-2012.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_riotabidva $f wff ph $.
	f1_riotabidva $f wff ps $.
	f2_riotabidva $f wff ch $.
	f3_riotabidva $f set x $.
	f4_riotabidva $f class A $.
	e0_riotabidva $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
	p_riotabidva $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) ) $= e0_riotabidva f0_riotabidva f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f1_riotabidva f2_riotabidva p_pm5.32da f0_riotabidva f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f1_riotabidva a_wa f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva p_iotabidv f0_riotabidva f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f1_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva a_cio a_wceq f1_riotabidva f3_riotabidva f4_riotabidva a_wreu p_adantr f0_riotabidva f1_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f1_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv p_ifeq1da e0_riotabidva f0_riotabidva f1_riotabidva f2_riotabidva f3_riotabidva f4_riotabidva p_reubidva f0_riotabidva f1_riotabidva f3_riotabidva f4_riotabidva a_wreu f2_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv p_ifbid f0_riotabidva f1_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f1_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv a_cif f1_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv a_cif f2_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv a_cif p_eqtrd f1_riotabidva f3_riotabidva f4_riotabidva a_df-riota f2_riotabidva f3_riotabidva f4_riotabidva a_df-riota f0_riotabidva f1_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f1_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv a_cif f2_riotabidva f3_riotabidva f4_riotabidva a_wreu f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f2_riotabidva a_wa f3_riotabidva a_cio f3_riotabidva a_sup_set_class f4_riotabidva a_wcel f3_riotabidva a_cab a_cund a_cfv a_cif f1_riotabidva f3_riotabidva f4_riotabidva a_crio f2_riotabidva f3_riotabidva f4_riotabidva a_crio p_3eqtr4g $.
$}

$(Equivalent wff's yield equal restricted iotas (inference rule).
       ( ~ rabbiia analog.)  (Contributed by NM, 16-Jan-2012.) $)

${
	$v ph ps x A  $.
	f0_riotabiia $f wff ph $.
	f1_riotabiia $f wff ps $.
	f2_riotabiia $f set x $.
	f3_riotabiia $f class A $.
	e0_riotabiia $e |- ( x e. A -> ( ph <-> ps ) ) $.
	p_riotabiia $p |- ( iota_ x e. A ph ) = ( iota_ x e. A ps ) $= a_cvv p_eqid e0_riotabiia f2_riotabiia a_sup_set_class f3_riotabiia a_wcel f0_riotabiia f1_riotabiia a_wb a_cvv a_cvv a_wceq p_adantl a_cvv a_cvv a_wceq f0_riotabiia f1_riotabiia f2_riotabiia f3_riotabiia p_riotabidva a_cvv a_cvv a_wceq f0_riotabiia f2_riotabiia f3_riotabiia a_crio f1_riotabiia f2_riotabiia f3_riotabiia a_crio a_wceq a_ax-mp $.
$}

$(Property of restricted iota.  Compare ~ iota1 .  (Contributed by Mario
       Carneiro, 15-Oct-2016.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riota1 $f wff ph $.
	f1_riota1 $f set x $.
	f2_riota1 $f class A $.
	p_riota1 $p |- ( E! x e. A ph -> ( ( x e. A /\ ph ) <-> ( iota_ x e. A ph ) = x ) ) $= f0_riota1 f1_riota1 f2_riota1 a_df-reu f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 p_iota1 f0_riota1 f1_riota1 f2_riota1 a_wreu f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 a_weu f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 a_cio f1_riota1 a_sup_set_class a_wceq a_wb p_sylbi f0_riota1 f1_riota1 f2_riota1 p_riotaiota f0_riota1 f1_riota1 f2_riota1 a_wreu f0_riota1 f1_riota1 f2_riota1 a_crio f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 a_cio f1_riota1 a_sup_set_class p_eqeq1d f0_riota1 f1_riota1 f2_riota1 a_wreu f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 a_sup_set_class f2_riota1 a_wcel f0_riota1 a_wa f1_riota1 a_cio f1_riota1 a_sup_set_class a_wceq f0_riota1 f1_riota1 f2_riota1 a_crio f1_riota1 a_sup_set_class a_wceq p_bitr4d $.
$}

$(Property of iota.  (Contributed by NM, 23-Aug-2011.) $)

${
	$v ph x A  $.
	f0_riota1a $f wff ph $.
	f1_riota1a $f set x $.
	f2_riota1a $f class A $.
	p_riota1a $p |- ( ( x e. A /\ E! x e. A ph ) -> ( ph <-> ( iota x ( x e. A /\ ph ) ) = x ) ) $= f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a p_ibar f0_riota1a f1_riota1a f2_riota1a a_df-reu f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a a_wa f1_riota1a p_iota1 f0_riota1a f1_riota1a f2_riota1a a_wreu f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a a_wa f1_riota1a a_weu f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a a_wa f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a a_wa f1_riota1a a_cio f1_riota1a a_sup_set_class a_wceq a_wb p_sylbi f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a a_wa f0_riota1a f1_riota1a f2_riota1a a_wreu f1_riota1a a_sup_set_class f2_riota1a a_wcel f0_riota1a a_wa f1_riota1a a_cio f1_riota1a a_sup_set_class a_wceq p_sylan9bb $.
$}

$(A deduction version of ~ riota2f .  (Contributed by NM, 17-Feb-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	f0_riota2df $f wff ph $.
	f1_riota2df $f wff ps $.
	f2_riota2df $f wff ch $.
	f3_riota2df $f set x $.
	f4_riota2df $f class A $.
	f5_riota2df $f class B $.
	e0_riota2df $e |- F/ x ph $.
	e1_riota2df $e |- ( ph -> F/_ x B ) $.
	e2_riota2df $e |- ( ph -> F/ x ch ) $.
	e3_riota2df $e |- ( ph -> B e. A ) $.
	e4_riota2df $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
	p_riota2df $p |- ( ( ph /\ E! x e. A ps ) -> ( ch <-> ( iota_ x e. A ps ) = B ) ) $= e3_riota2df f0_riota2df f5_riota2df f4_riota2df a_wcel f1_riota2df f3_riota2df f4_riota2df a_wreu p_adantr f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu p_simpr f1_riota2df f3_riota2df f4_riota2df a_df-reu f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f1_riota2df f3_riota2df f4_riota2df a_wreu f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df a_wa f3_riota2df a_weu p_sylib f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f3_riota2df a_sup_set_class f5_riota2df a_wceq p_simpr e3_riota2df f0_riota2df f5_riota2df f4_riota2df a_wcel f1_riota2df f3_riota2df f4_riota2df a_wreu p_adantr f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f5_riota2df f4_riota2df a_wcel f3_riota2df a_sup_set_class f5_riota2df a_wceq p_adantr f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f3_riota2df a_sup_set_class f5_riota2df a_wceq a_wa f3_riota2df a_sup_set_class f5_riota2df f4_riota2df p_eqeltrd f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f3_riota2df a_sup_set_class f5_riota2df a_wceq a_wa f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df p_biantrurd e4_riota2df f0_riota2df f3_riota2df a_sup_set_class f5_riota2df a_wceq f1_riota2df f2_riota2df a_wb f1_riota2df f3_riota2df f4_riota2df a_wreu p_adantlr f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f3_riota2df a_sup_set_class f5_riota2df a_wceq a_wa f1_riota2df f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df a_wa f2_riota2df p_bitr3d e0_riota2df f1_riota2df f3_riota2df f4_riota2df p_nfreu1 f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu f3_riota2df p_nfan e2_riota2df f0_riota2df f2_riota2df f3_riota2df a_wnf f1_riota2df f3_riota2df f4_riota2df a_wreu p_adantr e1_riota2df f0_riota2df f3_riota2df f5_riota2df a_wnfc f1_riota2df f3_riota2df f4_riota2df a_wreu p_adantr f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df a_wa f2_riota2df f3_riota2df f5_riota2df f4_riota2df p_iota2df f1_riota2df f3_riota2df f4_riota2df p_riotaiota f1_riota2df f3_riota2df f4_riota2df a_wreu f1_riota2df f3_riota2df f4_riota2df a_crio f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df a_wa f3_riota2df a_cio a_wceq f0_riota2df p_adantl f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f1_riota2df f3_riota2df f4_riota2df a_crio f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df a_wa f3_riota2df a_cio f5_riota2df p_eqeq1d f0_riota2df f1_riota2df f3_riota2df f4_riota2df a_wreu a_wa f2_riota2df f3_riota2df a_sup_set_class f4_riota2df a_wcel f1_riota2df a_wa f3_riota2df a_cio f5_riota2df a_wceq f1_riota2df f3_riota2df f4_riota2df a_crio f5_riota2df a_wceq p_bitr4d $.
$}

$(This theorem shows a condition that allows us to represent a descriptor
       with a class expression ` B ` .  (Contributed by NM, 23-Aug-2011.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d ph  $.
	$d x A  $.
	$d B  $.
	f0_riota2f $f wff ph $.
	f1_riota2f $f wff ps $.
	f2_riota2f $f set x $.
	f3_riota2f $f class A $.
	f4_riota2f $f class B $.
	e0_riota2f $e |- F/_ x B $.
	e1_riota2f $e |- F/ x ps $.
	e2_riota2f $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_riota2f $p |- ( ( B e. A /\ E! x e. A ph ) -> ( ps <-> ( iota_ x e. A ph ) = B ) ) $= e0_riota2f f2_riota2f f4_riota2f f3_riota2f p_nfel1 e0_riota2f f2_riota2f f4_riota2f a_wnfc f4_riota2f f3_riota2f a_wcel p_a1i e1_riota2f f1_riota2f f2_riota2f a_wnf f4_riota2f f3_riota2f a_wcel p_a1i f4_riota2f f3_riota2f a_wcel p_id e2_riota2f f2_riota2f a_sup_set_class f4_riota2f a_wceq f0_riota2f f1_riota2f a_wb f4_riota2f f3_riota2f a_wcel p_adantl f4_riota2f f3_riota2f a_wcel f0_riota2f f1_riota2f f2_riota2f f3_riota2f f4_riota2f p_riota2df $.
$}

$(This theorem shows a condition that allows us to represent a descriptor
       with a class expression ` B ` .  (Contributed by NM, 23-Aug-2011.)
       (Revised by Mario Carneiro, 10-Dec-2016.) $)

${
	$v ph ps x A B  $.
	$d x ps  $.
	$d x A  $.
	$d x B  $.
	f0_riota2 $f wff ph $.
	f1_riota2 $f wff ps $.
	f2_riota2 $f set x $.
	f3_riota2 $f class A $.
	f4_riota2 $f class B $.
	e0_riota2 $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_riota2 $p |- ( ( B e. A /\ E! x e. A ph ) -> ( ps <-> ( iota_ x e. A ph ) = B ) ) $= f2_riota2 f4_riota2 p_nfcv f1_riota2 f2_riota2 p_nfv e0_riota2 f0_riota2 f1_riota2 f2_riota2 f3_riota2 f4_riota2 p_riota2f $.
$}

$(Properties of a restricted definite description operator.  Todo: can
       some uses of ~ riota2f be shortened with this?  (Contributed by NM,
       23-Nov-2013.) $)

${
	$v ph ps x A B  $.
	$d ph  $.
	$d x A  $.
	$d B  $.
	f0_riotaprop $f wff ph $.
	f1_riotaprop $f wff ps $.
	f2_riotaprop $f set x $.
	f3_riotaprop $f class A $.
	f4_riotaprop $f class B $.
	e0_riotaprop $e |- F/ x ps $.
	e1_riotaprop $e |- B = ( iota_ x e. A ph ) $.
	e2_riotaprop $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_riotaprop $p |- ( E! x e. A ph -> ( B e. A /\ ps ) ) $= e1_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop p_riotacl f0_riotaprop f2_riotaprop f3_riotaprop a_wreu f4_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop a_crio f3_riotaprop p_syl5eqel e1_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop p_riotacl f0_riotaprop f2_riotaprop f3_riotaprop a_wreu f4_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop a_crio f3_riotaprop p_syl5eqel e1_riotaprop f4_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop a_crio p_eqcomi e1_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop p_nfriota1 f2_riotaprop f4_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop a_crio p_nfcxfr e0_riotaprop e2_riotaprop f0_riotaprop f1_riotaprop f2_riotaprop f3_riotaprop f4_riotaprop p_riota2f f4_riotaprop f3_riotaprop a_wcel f0_riotaprop f2_riotaprop f3_riotaprop a_wreu a_wa f1_riotaprop f0_riotaprop f2_riotaprop f3_riotaprop a_crio f4_riotaprop a_wceq p_mpbiri f4_riotaprop f3_riotaprop a_wcel f0_riotaprop f2_riotaprop f3_riotaprop a_wreu f1_riotaprop p_mpancom f0_riotaprop f2_riotaprop f3_riotaprop a_wreu f4_riotaprop f3_riotaprop a_wcel f1_riotaprop p_jca $.
$}

$(A method for computing restricted iota.  (Contributed by NM,
       16-Apr-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x A B  $.
	$d x y A  $.
	$d y B  $.
	$d x y ph  $.
	$d y ps  $.
	f0_riota5f $f wff ph $.
	f1_riota5f $f wff ps $.
	f2_riota5f $f set x $.
	f3_riota5f $f class A $.
	f4_riota5f $f class B $.
	i0_riota5f $f set y $.
	e0_riota5f $e |- ( ph -> F/_ x B ) $.
	e1_riota5f $e |- ( ph -> B e. A ) $.
	e2_riota5f $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
	p_riota5f $p |- ( ph -> ( iota_ x e. A ps ) = B ) $= e2_riota5f f0_riota5f f1_riota5f f2_riota5f a_sup_set_class f4_riota5f a_wceq a_wb f2_riota5f f3_riota5f p_ralrimiva e1_riota5f f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa p_a1tru f1_riota5f f2_riota5f f3_riota5f i0_riota5f a_sup_set_class p_reu6i i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa f1_riota5f f2_riota5f f3_riota5f a_wreu f0_riota5f p_adantl f0_riota5f f2_riota5f p_nfv i0_riota5f a_sup_set_class f3_riota5f a_wcel f2_riota5f p_nfv f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f p_nfra1 i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f2_riota5f p_nfan f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa f2_riota5f p_nfan f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f i0_riota5f a_sup_set_class p_nfcvd f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa a_wtru f2_riota5f p_nfvd f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral p_simprl f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq p_simpr f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq p_simplrr f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq p_simpr f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq p_simplrl f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class f3_riota5f p_eqeltrd f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f p_rsp f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wa f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f2_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb p_sylc f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wa f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq p_mpbird f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wa p_a1tru f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wa f1_riota5f a_wtru p_2thd f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f1_riota5f a_wtru f2_riota5f f3_riota5f i0_riota5f a_sup_set_class p_riota2df f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa f1_riota5f f2_riota5f f3_riota5f a_wreu a_wtru f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wb p_mpdan f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral a_wa a_wa a_wtru f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq p_mpbid f0_riota5f i0_riota5f a_sup_set_class f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq p_expr f0_riota5f f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wi i0_riota5f f3_riota5f p_ralrimiva f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wi i0_riota5f f4_riota5f f3_riota5f p_rspsbc f0_riota5f f4_riota5f f3_riota5f a_wcel f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wi i0_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wi i0_riota5f f4_riota5f a_wsbc p_sylc e1_riota5f f0_riota5f f2_riota5f p_nfv f0_riota5f f2_riota5f i0_riota5f a_sup_set_class p_nfcvd e0_riota5f f0_riota5f f2_riota5f i0_riota5f a_sup_set_class f4_riota5f p_nfeqd f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq f2_riota5f p_nfan1 f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq p_simpr f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq a_wa i0_riota5f a_sup_set_class f4_riota5f f2_riota5f a_sup_set_class p_eqeq2d f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq a_wa f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq f2_riota5f a_sup_set_class f4_riota5f a_wceq f1_riota5f p_bibi2d f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq a_wa f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f1_riota5f f2_riota5f a_sup_set_class f4_riota5f a_wceq a_wb f2_riota5f f3_riota5f p_ralbid f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq p_simpr f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq a_wa i0_riota5f a_sup_set_class f4_riota5f f1_riota5f f2_riota5f f3_riota5f a_crio p_eqeq2d f0_riota5f i0_riota5f a_sup_set_class f4_riota5f a_wceq a_wa f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f a_sup_set_class f4_riota5f a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq f1_riota5f f2_riota5f f3_riota5f a_crio f4_riota5f a_wceq p_imbi12d f0_riota5f f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wi f1_riota5f f2_riota5f a_sup_set_class f4_riota5f a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio f4_riota5f a_wceq a_wi i0_riota5f f4_riota5f f3_riota5f p_sbcied f0_riota5f f1_riota5f f2_riota5f a_sup_set_class i0_riota5f a_sup_set_class a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio i0_riota5f a_sup_set_class a_wceq a_wi i0_riota5f f4_riota5f a_wsbc f1_riota5f f2_riota5f a_sup_set_class f4_riota5f a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio f4_riota5f a_wceq a_wi p_mpbid f0_riota5f f1_riota5f f2_riota5f a_sup_set_class f4_riota5f a_wceq a_wb f2_riota5f f3_riota5f a_wral f1_riota5f f2_riota5f f3_riota5f a_crio f4_riota5f a_wceq p_mpd $.
$}

$(A method for computing restricted iota.  (Contributed by NM,
       20-Oct-2011.)  (Revised by Mario Carneiro, 6-Dec-2016.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_riota5 $f wff ph $.
	f1_riota5 $f wff ps $.
	f2_riota5 $f set x $.
	f3_riota5 $f class A $.
	f4_riota5 $f class B $.
	e0_riota5 $e |- ( ph -> B e. A ) $.
	e1_riota5 $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
	p_riota5 $p |- ( ph -> ( iota_ x e. A ps ) = B ) $= f0_riota5 f2_riota5 f4_riota5 p_nfcvd e0_riota5 e1_riota5 f0_riota5 f1_riota5 f2_riota5 f3_riota5 f4_riota5 p_riota5f $.
$}

$(A method for computing restricted iota.  (Contributed by NM,
       20-Oct-2011.)  (New usage is discouraged.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	$d ps  $.
	f0_riota5OLD $f wff ph $.
	f1_riota5OLD $f wff ps $.
	f2_riota5OLD $f set x $.
	f3_riota5OLD $f class A $.
	f4_riota5OLD $f class B $.
	e0_riota5OLD $e |- ( ( ph /\ B e. A /\ x e. A ) -> ( ps <-> x = B ) ) $.
	p_riota5OLD $p |- ( ( ph /\ B e. A ) -> ( iota_ x e. A ps ) = B ) $= f0_riota5OLD f4_riota5OLD f3_riota5OLD a_wcel p_simpr e0_riota5OLD f0_riota5OLD f4_riota5OLD f3_riota5OLD a_wcel f2_riota5OLD a_sup_set_class f3_riota5OLD a_wcel f1_riota5OLD f2_riota5OLD a_sup_set_class f4_riota5OLD a_wceq a_wb p_3expa f0_riota5OLD f4_riota5OLD f3_riota5OLD a_wcel a_wa f1_riota5OLD f2_riota5OLD f3_riota5OLD f4_riota5OLD p_riota5 $.
$}

$(Restriction of a unique element to a smaller class.  (Contributed by NM,
       21-Aug-2011.)  (Revised by NM, 22-Mar-2013.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	f0_riotass2 $f wff ph $.
	f1_riotass2 $f wff ps $.
	f2_riotass2 $f set x $.
	f3_riotass2 $f class A $.
	f4_riotass2 $f class B $.
	p_riotass2 $p |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph /\ E! x e. B ps ) ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ps ) ) $= f0_riotass2 f1_riotass2 f2_riotass2 f3_riotass2 f4_riotass2 p_reuss2 f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa p_simplr f0_riotass2 f2_riotass2 f3_riotass2 p_riotasbc f0_riotass2 f2_riotass2 f3_riotass2 p_riotacl f0_riotass2 f1_riotass2 a_wi f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 p_rspsbc f0_riotass2 f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 p_sbcimg f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 a_wcel f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral f0_riotass2 f1_riotass2 a_wi f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f0_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc a_wi p_sylibd f0_riotass2 f2_riotass2 f3_riotass2 a_wreu f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 a_wcel f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral f0_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc a_wi a_wi p_syl f0_riotass2 f2_riotass2 f3_riotass2 a_wreu f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral f0_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc p_mpid f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wreu f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc p_sylc f0_riotass2 f1_riotass2 f2_riotass2 f3_riotass2 f4_riotass2 p_reuss2 f0_riotass2 f2_riotass2 f3_riotass2 p_riotacl f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wreu f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 a_wcel p_syl f3_riotass2 f4_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio p_ssel f3_riotass2 f4_riotass2 a_wss f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 a_wcel f0_riotass2 f2_riotass2 f3_riotass2 a_crio f4_riotass2 a_wcel a_wi f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa p_ad2antrr f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_crio f3_riotass2 a_wcel f0_riotass2 f2_riotass2 f3_riotass2 a_crio f4_riotass2 a_wcel p_mpd f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu p_simprr f0_riotass2 f2_riotass2 f3_riotass2 p_nfriota1 f0_riotass2 f2_riotass2 f3_riotass2 p_nfriota1 f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio p_nfsbc1 f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio p_sbceq1a f1_riotass2 f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f2_riotass2 f4_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio p_riota2f f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_crio f4_riotass2 a_wcel f1_riotass2 f2_riotass2 f4_riotass2 a_wreu f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f1_riotass2 f2_riotass2 f4_riotass2 a_crio f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wceq a_wb p_syl2anc f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa a_wa f1_riotass2 f2_riotass2 f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wsbc f1_riotass2 f2_riotass2 f4_riotass2 a_crio f0_riotass2 f2_riotass2 f3_riotass2 a_crio a_wceq p_mpbid f3_riotass2 f4_riotass2 a_wss f0_riotass2 f1_riotass2 a_wi f2_riotass2 f3_riotass2 a_wral a_wa f0_riotass2 f2_riotass2 f3_riotass2 a_wrex f1_riotass2 f2_riotass2 f4_riotass2 a_wreu a_wa a_wa f1_riotass2 f2_riotass2 f4_riotass2 a_crio f0_riotass2 f2_riotass2 f3_riotass2 a_crio p_eqcomd $.
$}

$(Restriction of a unique element to a smaller class.  (Contributed by NM,
       19-Oct-2005.)  (Revised by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	$d ph  $.
	f0_riotass $f wff ph $.
	f1_riotass $f set x $.
	f2_riotass $f class A $.
	f3_riotass $f class B $.
	p_riotass $p |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ph ) ) $= f0_riotass f1_riotass f2_riotass f3_riotass p_reuss f0_riotass f1_riotass f2_riotass p_riotasbc f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu a_w3a f0_riotass f1_riotass f2_riotass a_wreu f0_riotass f1_riotass f0_riotass f1_riotass f2_riotass a_crio a_wsbc p_syl f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu p_simp1 f0_riotass f1_riotass f2_riotass f3_riotass p_reuss f0_riotass f1_riotass f2_riotass p_riotacl f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu a_w3a f0_riotass f1_riotass f2_riotass a_wreu f0_riotass f1_riotass f2_riotass a_crio f2_riotass a_wcel p_syl f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu a_w3a f2_riotass f3_riotass f0_riotass f1_riotass f2_riotass a_crio p_sseldd f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu p_simp3 f0_riotass f1_riotass f2_riotass p_nfriota1 f0_riotass f1_riotass f2_riotass p_nfriota1 f0_riotass f1_riotass f0_riotass f1_riotass f2_riotass a_crio p_nfsbc1 f0_riotass f1_riotass f0_riotass f1_riotass f2_riotass a_crio p_sbceq1a f0_riotass f0_riotass f1_riotass f0_riotass f1_riotass f2_riotass a_crio a_wsbc f1_riotass f3_riotass f0_riotass f1_riotass f2_riotass a_crio p_riota2f f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu a_w3a f0_riotass f1_riotass f2_riotass a_crio f3_riotass a_wcel f0_riotass f1_riotass f3_riotass a_wreu f0_riotass f1_riotass f0_riotass f1_riotass f2_riotass a_crio a_wsbc f0_riotass f1_riotass f3_riotass a_crio f0_riotass f1_riotass f2_riotass a_crio a_wceq a_wb p_syl2anc f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu a_w3a f0_riotass f1_riotass f0_riotass f1_riotass f2_riotass a_crio a_wsbc f0_riotass f1_riotass f3_riotass a_crio f0_riotass f1_riotass f2_riotass a_crio a_wceq p_mpbid f2_riotass f3_riotass a_wss f0_riotass f1_riotass f2_riotass a_wrex f0_riotass f1_riotass f3_riotass a_wreu a_w3a f0_riotass f1_riotass f3_riotass a_crio f0_riotass f1_riotass f2_riotass a_crio p_eqcomd $.
$}

$(Restriction of a unique element to a smaller class.  (Contributed by NM,
       19-Feb-2006.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	$d ph  $.
	f0_moriotass $f wff ph $.
	f1_moriotass $f set x $.
	f2_moriotass $f class A $.
	f3_moriotass $f class B $.
	p_moriotass $p |- ( ( A C_ B /\ E. x e. A ph /\ E* x e. B ph ) -> ( iota_ x e. A ph ) = ( iota_ x e. B ph ) ) $= f0_moriotass f1_moriotass f2_moriotass f3_moriotass p_ssrexv f2_moriotass f3_moriotass a_wss f0_moriotass f1_moriotass f2_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrex p_imp f2_moriotass f3_moriotass a_wss f0_moriotass f1_moriotass f2_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrmo p_3adant3 f2_moriotass f3_moriotass a_wss f0_moriotass f1_moriotass f2_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrmo p_simp3 f0_moriotass f1_moriotass f3_moriotass p_reu5 f2_moriotass f3_moriotass a_wss f0_moriotass f1_moriotass f2_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrmo a_w3a f0_moriotass f1_moriotass f3_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrmo f0_moriotass f1_moriotass f3_moriotass a_wreu p_sylanbrc f0_moriotass f1_moriotass f2_moriotass f3_moriotass p_riotass f2_moriotass f3_moriotass a_wss f0_moriotass f1_moriotass f2_moriotass a_wrex f0_moriotass f1_moriotass f3_moriotass a_wrmo f0_moriotass f1_moriotass f3_moriotass a_wreu f0_moriotass f1_moriotass f2_moriotass a_crio f0_moriotass f1_moriotass f3_moriotass a_crio a_wceq p_syld3an3 $.
$}

$(A restricted class abstraction with a unique member can be expressed as
       a singleton.  (Contributed by NM, 30-May-2006.) $)

${
	$v ph x A  $.
	$d A  $.
	$d ph  $.
	$d x  $.
	f0_snriota $f wff ph $.
	f1_snriota $f set x $.
	f2_snriota $f class A $.
	p_snriota $p |- ( E! x e. A ph -> { x e. A | ph } = { ( iota_ x e. A ph ) } ) $= f0_snriota f1_snriota f2_snriota a_df-rab f0_snriota f1_snriota f2_snriota a_df-reu f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota p_sniota f0_snriota f1_snriota f2_snriota a_wreu f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_weu f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_cab f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_cio a_csn a_wceq p_sylbi f0_snriota f1_snriota f2_snriota a_wreu f0_snriota f1_snriota f2_snriota a_crab f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_cab f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_cio a_csn p_syl5eq f0_snriota f1_snriota f2_snriota p_riotaiota f0_snriota f1_snriota f2_snriota a_wreu f0_snriota f1_snriota f2_snriota a_crio f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_cio p_sneqd f0_snriota f1_snriota f2_snriota a_wreu f0_snriota f1_snriota f2_snriota a_crab f1_snriota a_sup_set_class f2_snriota a_wcel f0_snriota a_wa f1_snriota a_cio a_csn f0_snriota f1_snriota f2_snriota a_crio a_csn p_eqtr4d $.
$}

$(Change the variable ` x ` in the expression for "the unique ` x ` such
       that ` ps ` " to another variable ` y ` contained in expression ` B ` .
       Use ~ reuhypd to eliminate the last hypothesis.  (Contributed by NM,
       16-Jan-2012.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps ch x y A B C  $.
	$d x B  $.
	$d x C  $.
	$d x y A  $.
	$d x y ph  $.
	$d ps y  $.
	$d ch x  $.
	f0_riotaxfrd $f wff ph $.
	f1_riotaxfrd $f wff ps $.
	f2_riotaxfrd $f wff ch $.
	f3_riotaxfrd $f set x $.
	f4_riotaxfrd $f set y $.
	f5_riotaxfrd $f class A $.
	f6_riotaxfrd $f class B $.
	f7_riotaxfrd $f class C $.
	e0_riotaxfrd $e |- F/_ y C $.
	e1_riotaxfrd $e |- ( ( ph /\ y e. A ) -> B e. A ) $.
	e2_riotaxfrd $e |- ( ( ph /\ ( iota_ y e. A ch ) e. A ) -> C e. A ) $.
	e3_riotaxfrd $e |- ( x = B -> ( ps <-> ch ) ) $.
	e4_riotaxfrd $e |- ( y = ( iota_ y e. A ch ) -> B = C ) $.
	e5_riotaxfrd $e |- ( ( ph /\ x e. A ) -> E! y e. A x = B ) $.
	p_riotaxfrd $p |- ( ( ph /\ E! x e. A ps ) -> ( iota_ x e. A ps ) = C ) $= f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd p_rabid f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd a_sup_set_class f5_riotaxfrd a_wcel f1_riotaxfrd p_baib f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd p_riotabiia e1_riotaxfrd e5_riotaxfrd e3_riotaxfrd f0_riotaxfrd f1_riotaxfrd f2_riotaxfrd f3_riotaxfrd f4_riotaxfrd f6_riotaxfrd f5_riotaxfrd p_reuxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd p_riotacl2 f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crab a_wcel f0_riotaxfrd p_adantl f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd p_riotacl f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd p_nfriota1 e0_riotaxfrd e1_riotaxfrd e3_riotaxfrd e4_riotaxfrd f0_riotaxfrd f1_riotaxfrd f2_riotaxfrd f3_riotaxfrd f4_riotaxfrd f6_riotaxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f7_riotaxfrd f5_riotaxfrd p_rabxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu f0_riotaxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f5_riotaxfrd a_wcel f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crab a_wcel a_wb p_sylan2 f0_riotaxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu a_wa f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crab a_wcel p_mpbird f0_riotaxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel p_ex f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel p_sylbid f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel p_imp e1_riotaxfrd e5_riotaxfrd e3_riotaxfrd f0_riotaxfrd f1_riotaxfrd f2_riotaxfrd f3_riotaxfrd f4_riotaxfrd f6_riotaxfrd f5_riotaxfrd p_reuxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd p_riotacl e2_riotaxfrd f0_riotaxfrd f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f5_riotaxfrd a_wcel f7_riotaxfrd f5_riotaxfrd a_wcel p_ex f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_crio f5_riotaxfrd a_wcel f0_riotaxfrd f7_riotaxfrd f5_riotaxfrd a_wcel p_syl5 f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu f2_riotaxfrd f4_riotaxfrd f5_riotaxfrd a_wreu f7_riotaxfrd f5_riotaxfrd a_wcel p_sylbid f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu f7_riotaxfrd f5_riotaxfrd a_wcel p_imp f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd p_rabid f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd a_sup_set_class f5_riotaxfrd a_wcel f1_riotaxfrd p_baibr f1_riotaxfrd f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd p_reubiia f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd a_wreu p_biimpi f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd a_wreu f0_riotaxfrd p_adantl f3_riotaxfrd f7_riotaxfrd p_nfcv f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd p_nfrab1 f3_riotaxfrd f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab p_nfel2 f3_riotaxfrd a_sup_set_class f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab p_eleq1 f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd f7_riotaxfrd p_riota2f f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu a_wa f7_riotaxfrd f5_riotaxfrd a_wcel f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd a_wreu f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd a_crio f7_riotaxfrd a_wceq a_wb p_syl2anc f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu a_wa f7_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd a_crio f7_riotaxfrd a_wceq p_mpbid f0_riotaxfrd f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_wreu a_wa f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crio f3_riotaxfrd a_sup_set_class f1_riotaxfrd f3_riotaxfrd f5_riotaxfrd a_crab a_wcel f3_riotaxfrd f5_riotaxfrd a_crio f7_riotaxfrd p_syl5eqr $.
$}

$(Specify the same property in two ways when class ` B ( y ) ` is
       single-valued.  (Contributed by NM, 1-Nov-2010.)  (Proof shortened by
       Mario Carneiro, 24-Dec-2016.) $)

${
	$v x y A B  $.
	$d x y z A  $.
	$d x z B  $.
	f0_eusvobj2 $f set x $.
	f1_eusvobj2 $f set y $.
	f2_eusvobj2 $f class A $.
	f3_eusvobj2 $f class B $.
	i0_eusvobj2 $f set z $.
	e0_eusvobj2 $e |- B e. _V $.
	p_eusvobj2 $p |- ( E! x E. y e. A x = B -> ( E. y e. A x = B <-> A. y e. A x = B ) ) $= f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 i0_eusvobj2 p_euabsn2 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn f0_eusvobj2 a_sup_set_class p_eleq2 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 p_abid f0_eusvobj2 i0_eusvobj2 a_sup_set_class p_elsn f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq f0_eusvobj2 a_sup_set_class f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab a_wcel f0_eusvobj2 a_sup_set_class i0_eusvobj2 a_sup_set_class a_csn a_wcel f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_sup_set_class i0_eusvobj2 a_sup_set_class a_wceq p_3bitr3g f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 p_nfre1 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f1_eusvobj2 f0_eusvobj2 p_nfab f1_eusvobj2 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn p_nfeq1 e0_eusvobj2 f1_eusvobj2 f0_eusvobj2 f2_eusvobj2 f3_eusvobj2 p_elabrex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn f3_eusvobj2 p_eleq2 e0_eusvobj2 f3_eusvobj2 i0_eusvobj2 a_sup_set_class p_elsnc f3_eusvobj2 i0_eusvobj2 a_sup_set_class p_eqcom f3_eusvobj2 i0_eusvobj2 a_sup_set_class a_csn a_wcel f3_eusvobj2 i0_eusvobj2 a_sup_set_class a_wceq i0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq p_bitri f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq f3_eusvobj2 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab a_wcel f3_eusvobj2 i0_eusvobj2 a_sup_set_class a_csn a_wcel i0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq p_syl6bb f1_eusvobj2 a_sup_set_class f2_eusvobj2 a_wcel f3_eusvobj2 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab a_wcel f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq i0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq p_syl5ib f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq i0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 p_ralrimi f0_eusvobj2 a_sup_set_class i0_eusvobj2 a_sup_set_class f3_eusvobj2 p_eqeq1 f0_eusvobj2 a_sup_set_class i0_eusvobj2 a_sup_set_class a_wceq f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq i0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 p_ralbidv f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral f0_eusvobj2 a_sup_set_class i0_eusvobj2 a_sup_set_class a_wceq i0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral p_syl5ibrcom f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_sup_set_class i0_eusvobj2 a_sup_set_class a_wceq f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral p_sylbid f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral a_wi i0_eusvobj2 p_exlimiv f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_weu f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_cab i0_eusvobj2 a_sup_set_class a_csn a_wceq i0_eusvobj2 a_wex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral a_wi p_sylbi f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 p_euex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 p_rexn0 f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f2_eusvobj2 a_c0 a_wne f0_eusvobj2 p_exlimiv f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 p_r19.2z f2_eusvobj2 a_c0 a_wne f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex p_ex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_weu f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_wex f2_eusvobj2 a_c0 a_wne f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex a_wi p_3syl f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_weu f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wrex f0_eusvobj2 a_sup_set_class f3_eusvobj2 a_wceq f1_eusvobj2 f2_eusvobj2 a_wral p_impbid $.
$}

$(Specify the same object in two ways when class ` B ( y ) ` is
       single-valued.  (Contributed by NM, 1-Nov-2010.)  (Proof shortened by
       Mario Carneiro, 19-Nov-2016.) $)

${
	$v x y A B  $.
	$d x y A  $.
	$d x B  $.
	f0_eusvobj1 $f set x $.
	f1_eusvobj1 $f set y $.
	f2_eusvobj1 $f class A $.
	f3_eusvobj1 $f class B $.
	e0_eusvobj1 $e |- B e. _V $.
	p_eusvobj1 $p |- ( E! x E. y e. A x = B -> ( iota x E. y e. A x = B ) = ( iota x A. y e. A x = B ) ) $= f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 p_nfeu1 e0_eusvobj1 f0_eusvobj1 f1_eusvobj1 f2_eusvobj1 f3_eusvobj1 p_eusvobj2 f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 a_weu f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wral a_wb f0_eusvobj1 p_alrimi f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wral f0_eusvobj1 p_iotabi f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 a_weu f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wral a_wb f0_eusvobj1 a_wal f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wrex f0_eusvobj1 a_cio f0_eusvobj1 a_sup_set_class f3_eusvobj1 a_wceq f1_eusvobj1 f2_eusvobj1 a_wral f0_eusvobj1 a_cio a_wceq p_syl $.
$}

$(There is one domain element for each value of a one-to-one onto
       function.  (Contributed by NM, 26-May-2006.) $)

${
	$v x A B C F  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x F  $.
	f0_f1ofveu $f set x $.
	f1_f1ofveu $f class A $.
	f2_f1ofveu $f class B $.
	f3_f1ofveu $f class C $.
	f4_f1ofveu $f class F $.
	p_f1ofveu $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> E! x e. A ( F ` x ) = C ) $= f1_f1ofveu f2_f1ofveu f4_f1ofveu p_f1ocnv f2_f1ofveu f1_f1ofveu f4_f1ofveu a_ccnv p_f1of f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f2_f1ofveu f1_f1ofveu f4_f1ofveu a_ccnv a_wf1o f2_f1ofveu f1_f1ofveu f4_f1ofveu a_ccnv a_wf p_syl f0_f1ofveu f2_f1ofveu f1_f1ofveu f3_f1ofveu f4_f1ofveu a_ccnv p_feu f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f2_f1ofveu f1_f1ofveu f4_f1ofveu a_ccnv a_wf f3_f1ofveu f2_f1ofveu a_wcel f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel f0_f1ofveu f1_f1ofveu a_wreu p_sylan f1_f1ofveu f2_f1ofveu f0_f1ofveu a_sup_set_class f3_f1ofveu f4_f1ofveu p_f1ocnvfvb f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f0_f1ofveu a_sup_set_class f1_f1ofveu a_wcel f3_f1ofveu f2_f1ofveu a_wcel f0_f1ofveu a_sup_set_class f4_f1ofveu a_cfv f3_f1ofveu a_wceq f3_f1ofveu f4_f1ofveu a_ccnv a_cfv f0_f1ofveu a_sup_set_class a_wceq a_wb p_3com23 f1_f1ofveu f2_f1ofveu f4_f1ofveu p_dff1o4 f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f4_f1ofveu f1_f1ofveu a_wfn f4_f1ofveu a_ccnv f2_f1ofveu a_wfn p_simprbi f2_f1ofveu f3_f1ofveu f0_f1ofveu a_sup_set_class f4_f1ofveu a_ccnv p_fnopfvb f4_f1ofveu a_ccnv f2_f1ofveu a_wfn f3_f1ofveu f2_f1ofveu a_wcel f3_f1ofveu f4_f1ofveu a_ccnv a_cfv f0_f1ofveu a_sup_set_class a_wceq f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel a_wb f0_f1ofveu a_sup_set_class f1_f1ofveu a_wcel p_3adant3 f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f4_f1ofveu a_ccnv f2_f1ofveu a_wfn f3_f1ofveu f2_f1ofveu a_wcel f0_f1ofveu a_sup_set_class f1_f1ofveu a_wcel f3_f1ofveu f4_f1ofveu a_ccnv a_cfv f0_f1ofveu a_sup_set_class a_wceq f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel a_wb p_syl3an1 f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f3_f1ofveu f2_f1ofveu a_wcel f0_f1ofveu a_sup_set_class f1_f1ofveu a_wcel a_w3a f0_f1ofveu a_sup_set_class f4_f1ofveu a_cfv f3_f1ofveu a_wceq f3_f1ofveu f4_f1ofveu a_ccnv a_cfv f0_f1ofveu a_sup_set_class a_wceq f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel p_bitrd f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f3_f1ofveu f2_f1ofveu a_wcel f0_f1ofveu a_sup_set_class f1_f1ofveu a_wcel f0_f1ofveu a_sup_set_class f4_f1ofveu a_cfv f3_f1ofveu a_wceq f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel a_wb p_3expa f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f3_f1ofveu f2_f1ofveu a_wcel a_wa f0_f1ofveu a_sup_set_class f4_f1ofveu a_cfv f3_f1ofveu a_wceq f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel f0_f1ofveu f1_f1ofveu p_reubidva f1_f1ofveu f2_f1ofveu f4_f1ofveu a_wf1o f3_f1ofveu f2_f1ofveu a_wcel a_wa f0_f1ofveu a_sup_set_class f4_f1ofveu a_cfv f3_f1ofveu a_wceq f0_f1ofveu f1_f1ofveu a_wreu f3_f1ofveu f0_f1ofveu a_sup_set_class a_cop f4_f1ofveu a_ccnv a_wcel f0_f1ofveu f1_f1ofveu a_wreu p_mpbird $.
$}

$(Value of the converse of a one-to-one onto function.  (Contributed by
       NM, 26-May-2006.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)

${
	$v x A B C F  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x F  $.
	f0_f1ocnvfv3 $f set x $.
	f1_f1ocnvfv3 $f class A $.
	f2_f1ocnvfv3 $f class B $.
	f3_f1ocnvfv3 $f class C $.
	f4_f1ocnvfv3 $f class F $.
	p_f1ocnvfv3 $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> ( `' F ` C ) = ( iota_ x e. A ( F ` x ) = C ) ) $= f1_f1ocnvfv3 f2_f1ocnvfv3 f3_f1ocnvfv3 f4_f1ocnvfv3 p_f1ocnvdm f1_f1ocnvfv3 f2_f1ocnvfv3 f0_f1ocnvfv3 a_sup_set_class f3_f1ocnvfv3 f4_f1ocnvfv3 p_f1ocnvfvb f1_f1ocnvfv3 f2_f1ocnvfv3 f4_f1ocnvfv3 a_wf1o f0_f1ocnvfv3 a_sup_set_class f1_f1ocnvfv3 a_wcel f3_f1ocnvfv3 f2_f1ocnvfv3 a_wcel f0_f1ocnvfv3 a_sup_set_class f4_f1ocnvfv3 a_cfv f3_f1ocnvfv3 a_wceq f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv f0_f1ocnvfv3 a_sup_set_class a_wceq a_wb p_3expa f1_f1ocnvfv3 f2_f1ocnvfv3 f4_f1ocnvfv3 a_wf1o f0_f1ocnvfv3 a_sup_set_class f1_f1ocnvfv3 a_wcel f3_f1ocnvfv3 f2_f1ocnvfv3 a_wcel f0_f1ocnvfv3 a_sup_set_class f4_f1ocnvfv3 a_cfv f3_f1ocnvfv3 a_wceq f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv f0_f1ocnvfv3 a_sup_set_class a_wceq a_wb p_an32s f0_f1ocnvfv3 a_sup_set_class f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv p_eqcom f1_f1ocnvfv3 f2_f1ocnvfv3 f4_f1ocnvfv3 a_wf1o f3_f1ocnvfv3 f2_f1ocnvfv3 a_wcel a_wa f0_f1ocnvfv3 a_sup_set_class f1_f1ocnvfv3 a_wcel a_wa f0_f1ocnvfv3 a_sup_set_class f4_f1ocnvfv3 a_cfv f3_f1ocnvfv3 a_wceq f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv f0_f1ocnvfv3 a_sup_set_class a_wceq f0_f1ocnvfv3 a_sup_set_class f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv a_wceq p_syl6bbr f1_f1ocnvfv3 f2_f1ocnvfv3 f4_f1ocnvfv3 a_wf1o f3_f1ocnvfv3 f2_f1ocnvfv3 a_wcel a_wa f0_f1ocnvfv3 a_sup_set_class f4_f1ocnvfv3 a_cfv f3_f1ocnvfv3 a_wceq f0_f1ocnvfv3 f1_f1ocnvfv3 f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv p_riota5 f1_f1ocnvfv3 f2_f1ocnvfv3 f4_f1ocnvfv3 a_wf1o f3_f1ocnvfv3 f2_f1ocnvfv3 a_wcel a_wa f0_f1ocnvfv3 a_sup_set_class f4_f1ocnvfv3 a_cfv f3_f1ocnvfv3 a_wceq f0_f1ocnvfv3 f1_f1ocnvfv3 a_crio f3_f1ocnvfv3 f4_f1ocnvfv3 a_ccnv a_cfv p_eqcomd $.
$}

$(Restricted iota equals the undefined value of its domain of discourse
       ` A ` when not meaningful.  (Contributed by NM, 16-Jan-2012.)  (Revised
       by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riotaund $f wff ph $.
	f1_riotaund $f set x $.
	f2_riotaund $f class A $.
	p_riotaund $p |- ( -. E! x e. A ph -> ( iota_ x e. A ph ) = ( Undef ` A ) ) $= f0_riotaund f1_riotaund f2_riotaund a_wreu f1_riotaund a_sup_set_class f2_riotaund a_wcel f0_riotaund a_wa f1_riotaund a_cio f1_riotaund a_sup_set_class f2_riotaund a_wcel f1_riotaund a_cab a_cund a_cfv p_iffalse f0_riotaund f1_riotaund f2_riotaund a_df-riota f1_riotaund f2_riotaund p_abid2 f1_riotaund a_sup_set_class f2_riotaund a_wcel f1_riotaund a_cab f2_riotaund p_eqcomi f2_riotaund f1_riotaund a_sup_set_class f2_riotaund a_wcel f1_riotaund a_cab a_cund p_fveq2i f0_riotaund f1_riotaund f2_riotaund a_wreu a_wn f0_riotaund f1_riotaund f2_riotaund a_wreu f1_riotaund a_sup_set_class f2_riotaund a_wcel f0_riotaund a_wa f1_riotaund a_cio f1_riotaund a_sup_set_class f2_riotaund a_wcel f1_riotaund a_cab a_cund a_cfv a_cif f1_riotaund a_sup_set_class f2_riotaund a_wcel f1_riotaund a_cab a_cund a_cfv f0_riotaund f1_riotaund f2_riotaund a_crio f2_riotaund a_cund a_cfv p_3eqtr4g $.
$}

$(For proper classes, restricted and unrestricted iota are the same.
       (Contributed by NM, 15-Sep-2011.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riotaprc $f wff ph $.
	f1_riotaprc $f set x $.
	f2_riotaprc $f class A $.
	p_riotaprc $p |- ( -. A e. _V -> ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) ) ) $= f2_riotaprc a_cund p_fvprc f2_riotaprc a_cvv a_wcel a_wn f2_riotaprc a_cund a_cfv a_c0 a_wceq f0_riotaprc f1_riotaprc f2_riotaprc a_wreu a_wn p_adantr f0_riotaprc f1_riotaprc f2_riotaprc p_riotaund f0_riotaprc f1_riotaprc f2_riotaprc a_wreu a_wn f0_riotaprc f1_riotaprc f2_riotaprc a_crio f2_riotaprc a_cund a_cfv a_wceq f2_riotaprc a_cvv a_wcel a_wn p_adantl f0_riotaprc f1_riotaprc f2_riotaprc a_df-reu f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc p_iotanul f0_riotaprc f1_riotaprc f2_riotaprc a_wreu f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc a_weu f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc a_cio a_c0 a_wceq p_sylnbi f0_riotaprc f1_riotaprc f2_riotaprc a_wreu a_wn f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc a_cio a_c0 a_wceq f2_riotaprc a_cvv a_wcel a_wn p_adantl f2_riotaprc a_cvv a_wcel a_wn f0_riotaprc f1_riotaprc f2_riotaprc a_wreu a_wn a_wa f2_riotaprc a_cund a_cfv a_c0 f0_riotaprc f1_riotaprc f2_riotaprc a_crio f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc a_cio p_3eqtr4d f2_riotaprc a_cvv a_wcel a_wn f0_riotaprc f1_riotaprc f2_riotaprc a_wreu a_wn f0_riotaprc f1_riotaprc f2_riotaprc a_crio f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc a_cio a_wceq p_ex f0_riotaprc f1_riotaprc f2_riotaprc p_riotaiota f2_riotaprc a_cvv a_wcel a_wn f0_riotaprc f1_riotaprc f2_riotaprc a_wreu f0_riotaprc f1_riotaprc f2_riotaprc a_crio f1_riotaprc a_sup_set_class f2_riotaprc a_wcel f0_riotaprc a_wa f1_riotaprc a_cio a_wceq p_pm2.61d2 $.
$}

$(The restricted iota class is limited in size by the base set.
       (Contributed by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riotassuni $f wff ph $.
	f1_riotassuni $f set x $.
	f2_riotassuni $f class A $.
	p_riotassuni $p |- ( iota_ x e. A ph ) C_ ( ~P U. A u. U. A ) $= f0_riotassuni f1_riotassuni f2_riotassuni p_riotauni f0_riotassuni f1_riotassuni f2_riotassuni p_ssrab2 f0_riotassuni f1_riotassuni f2_riotassuni a_crab f2_riotassuni p_uniss f0_riotassuni f1_riotassuni f2_riotassuni a_crab f2_riotassuni a_wss f0_riotassuni f1_riotassuni f2_riotassuni a_crab a_cuni f2_riotassuni a_cuni a_wss a_ax-mp f2_riotassuni a_cuni f2_riotassuni a_cuni a_cpw p_ssun2 f0_riotassuni f1_riotassuni f2_riotassuni a_crab a_cuni f2_riotassuni a_cuni f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun p_sstri f0_riotassuni f1_riotassuni f2_riotassuni a_crab a_cuni f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun a_wss f0_riotassuni f1_riotassuni f2_riotassuni a_wreu p_a1i f0_riotassuni f1_riotassuni f2_riotassuni a_wreu f0_riotassuni f1_riotassuni f2_riotassuni a_crio f0_riotassuni f1_riotassuni f2_riotassuni a_crab a_cuni f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun p_eqsstrd f0_riotassuni f1_riotassuni f2_riotassuni p_riotaund f2_riotassuni a_cvv p_undefval f2_riotassuni a_cvv a_wcel f2_riotassuni a_cund a_cfv f2_riotassuni a_cuni a_cpw a_wceq f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn p_adantl f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni p_ssun1 f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun a_wss f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn f2_riotassuni a_cvv a_wcel a_wa p_a1i f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn f2_riotassuni a_cvv a_wcel a_wa f2_riotassuni a_cund a_cfv f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun p_eqsstrd f2_riotassuni a_cund p_fvprc f2_riotassuni a_cvv a_wcel a_wn f2_riotassuni a_cund a_cfv a_c0 a_wceq f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn p_adantl f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun p_0ss a_c0 f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun a_wss f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn f2_riotassuni a_cvv a_wcel a_wn a_wa p_a1i f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn f2_riotassuni a_cvv a_wcel a_wn a_wa f2_riotassuni a_cund a_cfv a_c0 f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun p_eqsstrd f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn f2_riotassuni a_cvv a_wcel f2_riotassuni a_cund a_cfv f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun a_wss p_pm2.61dan f0_riotassuni f1_riotassuni f2_riotassuni a_wreu a_wn f0_riotassuni f1_riotassuni f2_riotassuni a_crio f2_riotassuni a_cund a_cfv f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun p_eqsstrd f0_riotassuni f1_riotassuni f2_riotassuni a_wreu f0_riotassuni f1_riotassuni f2_riotassuni a_crio f2_riotassuni a_cuni a_cpw f2_riotassuni a_cuni a_cun a_wss p_pm2.61i $.
$}

$(Closure of restricted iota.  (Contributed by NM, 28-Feb-2013.)  (Revised
       by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x A V  $.
	$d x A  $.
	f0_riotaclbg $f wff ph $.
	f1_riotaclbg $f set x $.
	f2_riotaclbg $f class A $.
	f3_riotaclbg $f class V $.
	p_riotaclbg $p |- ( A e. V -> ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) ) $= f0_riotaclbg f1_riotaclbg f2_riotaclbg p_riotacl f2_riotaclbg f3_riotaclbg p_undefnel2 f0_riotaclbg f1_riotaclbg f2_riotaclbg p_riotaund f0_riotaclbg f1_riotaclbg f2_riotaclbg a_wreu a_wn f0_riotaclbg f1_riotaclbg f2_riotaclbg a_crio f2_riotaclbg a_cund a_cfv f2_riotaclbg p_eleq1d f0_riotaclbg f1_riotaclbg f2_riotaclbg a_wreu a_wn f0_riotaclbg f1_riotaclbg f2_riotaclbg a_crio f2_riotaclbg a_wcel f2_riotaclbg a_cund a_cfv f2_riotaclbg a_wcel p_notbid f2_riotaclbg f3_riotaclbg a_wcel f0_riotaclbg f1_riotaclbg f2_riotaclbg a_crio f2_riotaclbg a_wcel a_wn f0_riotaclbg f1_riotaclbg f2_riotaclbg a_wreu a_wn f2_riotaclbg a_cund a_cfv f2_riotaclbg a_wcel a_wn p_syl5ibrcom f2_riotaclbg f3_riotaclbg a_wcel f0_riotaclbg f1_riotaclbg f2_riotaclbg a_wreu f0_riotaclbg f1_riotaclbg f2_riotaclbg a_crio f2_riotaclbg a_wcel p_con4d f2_riotaclbg f3_riotaclbg a_wcel f0_riotaclbg f1_riotaclbg f2_riotaclbg a_wreu f0_riotaclbg f1_riotaclbg f2_riotaclbg a_crio f2_riotaclbg a_wcel p_impbid2 $.
$}

$(Closure of restricted iota.  (Contributed by NM, 15-Sep-2011.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riotaclb $f wff ph $.
	f1_riotaclb $f set x $.
	f2_riotaclb $f class A $.
	e0_riotaclb $e |- A e. _V $.
	p_riotaclb $p |- ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) $= e0_riotaclb f0_riotaclb f1_riotaclb f2_riotaclb a_cvv p_riotaclbg f2_riotaclb a_cvv a_wcel f0_riotaclb f1_riotaclb f2_riotaclb a_wreu f0_riotaclb f1_riotaclb f2_riotaclb a_crio f2_riotaclb a_wcel a_wb a_ax-mp $.
$}

$(Restricted iota equals the undefined value of its domain of discourse
       ` A ` when not meaningful.  (Contributed by NM, 26-Sep-2011.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_riotaundb $f wff ph $.
	f1_riotaundb $f set x $.
	f2_riotaundb $f class A $.
	e0_riotaundb $e |- A e. _V $.
	p_riotaundb $p |- ( -. E! x e. A ph <-> ( iota_ x e. A ph ) = ( Undef ` A ) ) $= f0_riotaundb f1_riotaundb f2_riotaundb p_riotaund f0_riotaundb f1_riotaundb f2_riotaundb p_riotacl e0_riotaundb f2_riotaundb a_cvv p_undefnel2 f2_riotaundb a_cvv a_wcel f2_riotaundb a_cund a_cfv f2_riotaundb a_wcel a_wn a_ax-mp f0_riotaundb f1_riotaundb f2_riotaundb a_crio f2_riotaundb a_cund a_cfv f2_riotaundb p_nelne2 f0_riotaundb f1_riotaundb f2_riotaundb a_wreu f0_riotaundb f1_riotaundb f2_riotaundb a_crio f2_riotaundb a_wcel f2_riotaundb a_cund a_cfv f2_riotaundb a_wcel a_wn f0_riotaundb f1_riotaundb f2_riotaundb a_crio f2_riotaundb a_cund a_cfv a_wne p_sylancl f0_riotaundb f1_riotaundb f2_riotaundb a_wreu f0_riotaundb f1_riotaundb f2_riotaundb a_crio f2_riotaundb a_cund a_cfv p_necon2bi f0_riotaundb f1_riotaundb f2_riotaundb a_wreu a_wn f0_riotaundb f1_riotaundb f2_riotaundb a_crio f2_riotaundb a_cund a_cfv a_wceq p_impbii $.
$}

$(Deduction version of ~ riotasv .  (Contributed by NM, 4-Mar-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)

${
	$v ph ps x y A B C D V  $.
	$d x y z A  $.
	$d x z B  $.
	$d x z C  $.
	$d z D  $.
	$d z ph  $.
	$d x z ps  $.
	f0_riotasvd $f wff ph $.
	f1_riotasvd $f wff ps $.
	f2_riotasvd $f set x $.
	f3_riotasvd $f set y $.
	f4_riotasvd $f class A $.
	f5_riotasvd $f class B $.
	f6_riotasvd $f class C $.
	f7_riotasvd $f class D $.
	f8_riotasvd $f class V $.
	i0_riotasvd $f set z $.
	e0_riotasvd $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	e1_riotasvd $e |- ( ph -> D e. A ) $.
	p_riotasvd $p |- ( ( ph /\ A e. V ) -> ( ( y e. B /\ ps ) -> D = C ) ) $= e0_riotasvd f0_riotasvd f7_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wceq f4_riotasvd f8_riotasvd a_wcel p_adantr e1_riotasvd f0_riotasvd f7_riotasvd f4_riotasvd a_wcel f4_riotasvd f8_riotasvd a_wcel p_adantr f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f7_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f4_riotasvd p_eqeltrrd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd f8_riotasvd p_riotaclbg f4_riotasvd f8_riotasvd a_wcel f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_wreu f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f4_riotasvd a_wcel a_wb f0_riotasvd p_adantl f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_wreu f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f4_riotasvd a_wcel p_mpbird f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd p_riotasbc f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_wreu f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wsbc p_syl e0_riotasvd f0_riotasvd f7_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wceq f4_riotasvd f8_riotasvd a_wcel p_adantr e1_riotasvd f0_riotasvd f7_riotasvd f4_riotasvd a_wcel f4_riotasvd f8_riotasvd a_wcel p_adantr f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f7_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f4_riotasvd p_eqeltrrd f2_riotasvd a_sup_set_class i0_riotasvd a_sup_set_class f6_riotasvd p_eqeq1 f2_riotasvd a_sup_set_class i0_riotasvd a_sup_set_class a_wceq f2_riotasvd a_sup_set_class f6_riotasvd a_wceq i0_riotasvd a_sup_set_class f6_riotasvd a_wceq f1_riotasvd p_imbi2d f2_riotasvd a_sup_set_class i0_riotasvd a_sup_set_class a_wceq f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f1_riotasvd i0_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd p_ralbidv f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd p_nfra1 f3_riotasvd f4_riotasvd p_nfcv f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f3_riotasvd f2_riotasvd f4_riotasvd p_nfriota f3_riotasvd i0_riotasvd a_sup_set_class f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio p_nfeq2 i0_riotasvd a_sup_set_class f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd p_eqeq1 i0_riotasvd a_sup_set_class f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wceq i0_riotasvd a_sup_set_class f6_riotasvd a_wceq f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq f1_riotasvd p_imbi2d i0_riotasvd a_sup_set_class f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wceq f1_riotasvd i0_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd p_ralbid f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f1_riotasvd i0_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd i0_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f4_riotasvd p_sbcie2g f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f4_riotasvd a_wcel f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wsbc f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral a_wb p_syl f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wsbc f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral p_mpbid f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd p_rsp f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f3_riotasvd a_sup_set_class f5_riotasvd a_wcel f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq a_wi a_wi p_syl f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f3_riotasvd a_sup_set_class f5_riotasvd a_wcel f1_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq p_imp3a e0_riotasvd f0_riotasvd f7_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio a_wceq f4_riotasvd f8_riotasvd a_wcel p_adantr f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f7_riotasvd f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd p_eqeq1d f0_riotasvd f4_riotasvd f8_riotasvd a_wcel a_wa f3_riotasvd a_sup_set_class f5_riotasvd a_wcel f1_riotasvd a_wa f1_riotasvd f2_riotasvd a_sup_set_class f6_riotasvd a_wceq a_wi f3_riotasvd f5_riotasvd a_wral f2_riotasvd f4_riotasvd a_crio f6_riotasvd a_wceq f7_riotasvd f6_riotasvd a_wceq p_sylibrd $.
$}

$(Deduction version of ~ riotasv .  (Contributed by NM, 1-Feb-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps x y A B C D V  $.
	$d x y A  $.
	$d x B  $.
	$d x C  $.
	$d D  $.
	$d ph  $.
	$d x ps  $.
	f0_riotasvdOLD $f wff ph $.
	f1_riotasvdOLD $f wff ps $.
	f2_riotasvdOLD $f set x $.
	f3_riotasvdOLD $f set y $.
	f4_riotasvdOLD $f class A $.
	f5_riotasvdOLD $f class B $.
	f6_riotasvdOLD $f class C $.
	f7_riotasvdOLD $f class D $.
	f8_riotasvdOLD $f class V $.
	e0_riotasvdOLD $e |- ( ph -> A. x ph ) $.
	e1_riotasvdOLD $e |- ( ph -> A. y ph ) $.
	e2_riotasvdOLD $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	p_riotasvdOLD $p |- ( ( ( ph /\ A e. V ) /\ D e. A /\ ( y e. B /\ ps ) ) -> D = C ) $= e2_riotasvdOLD f0_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio p_eqcomd f0_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f7_riotasvdOLD a_wceq f4_riotasvdOLD f8_riotasvdOLD a_wcel f7_riotasvdOLD f4_riotasvdOLD a_wcel p_ad2antrr e2_riotasvdOLD f0_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f4_riotasvdOLD p_eleq1d f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f4_riotasvdOLD a_wcel a_wb f4_riotasvdOLD f8_riotasvdOLD a_wcel p_adantr f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD p_riotaclbg f4_riotasvdOLD f8_riotasvdOLD a_wcel f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_wreu f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f4_riotasvdOLD a_wcel a_wb f0_riotasvdOLD p_adantl f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f4_riotasvdOLD a_wcel f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_wreu p_bitr4d f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_wreu p_biimpa e0_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD p_nfi f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD p_nfriota1 e0_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD p_nfi e2_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio p_nfceqdf f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD a_wnfc f2_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio a_wnfc p_mpbiri f0_riotasvdOLD f2_riotasvdOLD f4_riotasvdOLD p_nfcvd f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD p_nfeld f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel f2_riotasvdOLD p_nfan1 f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD p_nfriota1 e0_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD p_nfi e2_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio p_nfceqdf f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD a_wnfc f2_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio a_wnfc p_mpbiri f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD a_wnfc f7_riotasvdOLD f4_riotasvdOLD a_wcel p_adantr e1_riotasvdOLD f0_riotasvdOLD f3_riotasvdOLD p_nfi f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD p_nfra1 f3_riotasvdOLD f4_riotasvdOLD p_nfcv f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f3_riotasvdOLD f2_riotasvdOLD f4_riotasvdOLD p_nfriota e1_riotasvdOLD f0_riotasvdOLD f3_riotasvdOLD p_nfi e2_riotasvdOLD f0_riotasvdOLD f3_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio p_nfceqdf f0_riotasvdOLD f3_riotasvdOLD f7_riotasvdOLD a_wnfc f3_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio a_wnfc p_mpbiri f0_riotasvdOLD f3_riotasvdOLD f4_riotasvdOLD p_nfcvd f0_riotasvdOLD f3_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD p_nfeld f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel f3_riotasvdOLD p_nfan1 f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f2_riotasvdOLD f5_riotasvdOLD p_nfcvd f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f1_riotasvdOLD f2_riotasvdOLD p_nfvd f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD p_nfriota1 e0_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD p_nfi e2_riotasvdOLD f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio p_nfceqdf f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD a_wnfc f2_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio a_wnfc p_mpbiri f0_riotasvdOLD f2_riotasvdOLD f7_riotasvdOLD a_wnfc f7_riotasvdOLD f4_riotasvdOLD a_wcel p_adantr f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f2_riotasvdOLD f6_riotasvdOLD p_nfcvd f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f2_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD p_nfeqd f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq f2_riotasvdOLD p_nfimd f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f2_riotasvdOLD f3_riotasvdOLD f5_riotasvdOLD p_nfrald f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel p_simpr e1_riotasvdOLD f0_riotasvdOLD f3_riotasvdOLD p_nfi f0_riotasvdOLD f3_riotasvdOLD f2_riotasvdOLD a_sup_set_class p_nfcvd f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD p_nfra1 f3_riotasvdOLD f4_riotasvdOLD p_nfcv f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f3_riotasvdOLD f2_riotasvdOLD f4_riotasvdOLD p_nfriota e1_riotasvdOLD f0_riotasvdOLD f3_riotasvdOLD p_nfi e2_riotasvdOLD f0_riotasvdOLD f3_riotasvdOLD f7_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio p_nfceqdf f0_riotasvdOLD f3_riotasvdOLD f7_riotasvdOLD a_wnfc f3_riotasvdOLD f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio a_wnfc p_mpbiri f0_riotasvdOLD f3_riotasvdOLD f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD p_nfeqd f0_riotasvdOLD f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD a_wceq f3_riotasvdOLD p_nfan1 f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD f6_riotasvdOLD p_eqeq1 f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD a_wceq f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wb f0_riotasvdOLD p_adantl f0_riotasvdOLD f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD a_wceq a_wa f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq f7_riotasvdOLD f6_riotasvdOLD a_wceq f1_riotasvdOLD p_imbi2d f0_riotasvdOLD f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD a_wceq a_wa f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD p_ralbid f0_riotasvdOLD f2_riotasvdOLD a_sup_set_class f7_riotasvdOLD a_wceq f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral a_wb f7_riotasvdOLD f4_riotasvdOLD a_wcel p_adantlr f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD f7_riotasvdOLD p_riota2df f0_riotasvdOLD f7_riotasvdOLD f4_riotasvdOLD a_wcel f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_wreu f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f7_riotasvdOLD a_wceq a_wb f4_riotasvdOLD f8_riotasvdOLD a_wcel p_adantllr f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_wreu f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f7_riotasvdOLD a_wceq a_wb p_mpdan f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel a_wa f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f1_riotasvdOLD f2_riotasvdOLD a_sup_set_class f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f2_riotasvdOLD f4_riotasvdOLD a_crio f7_riotasvdOLD a_wceq p_mpbird f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral p_ex f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD p_rsp f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi f3_riotasvdOLD f5_riotasvdOLD a_wral f3_riotasvdOLD a_sup_set_class f5_riotasvdOLD a_wcel f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq a_wi a_wi p_syl6 f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel f3_riotasvdOLD a_sup_set_class f5_riotasvdOLD a_wcel f1_riotasvdOLD f7_riotasvdOLD f6_riotasvdOLD a_wceq p_imp4a f0_riotasvdOLD f4_riotasvdOLD f8_riotasvdOLD a_wcel a_wa f7_riotasvdOLD f4_riotasvdOLD a_wcel f3_riotasvdOLD a_sup_set_class f5_riotasvdOLD a_wcel f1_riotasvdOLD a_wa f7_riotasvdOLD f6_riotasvdOLD a_wceq p_3imp $.
$}

$(Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 2-Mar-2013.) $)

${
	$v ph ps ch x y A B C D E F V  $.
	$d x y A  $.
	$d x y B  $.
	$d x C  $.
	$d D  $.
	$d y E  $.
	$d F  $.
	$d ph  $.
	$d x ps  $.
	f0_riotasv2d $f wff ph $.
	f1_riotasv2d $f wff ps $.
	f2_riotasv2d $f wff ch $.
	f3_riotasv2d $f set x $.
	f4_riotasv2d $f set y $.
	f5_riotasv2d $f class A $.
	f6_riotasv2d $f class B $.
	f7_riotasv2d $f class C $.
	f8_riotasv2d $f class D $.
	f9_riotasv2d $f class E $.
	f10_riotasv2d $f class F $.
	f11_riotasv2d $f class V $.
	e0_riotasv2d $e |- F/ y ph $.
	e1_riotasv2d $e |- ( ph -> F/_ y F ) $.
	e2_riotasv2d $e |- ( ph -> F/ y ch ) $.
	e3_riotasv2d $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	e4_riotasv2d $e |- ( ( ph /\ y = E ) -> ( ps <-> ch ) ) $.
	e5_riotasv2d $e |- ( ( ph /\ y = E ) -> C = F ) $.
	e6_riotasv2d $e |- ( ph -> D e. A ) $.
	e7_riotasv2d $e |- ( ph -> E e. B ) $.
	e8_riotasv2d $e |- ( ph -> ch ) $.
	p_riotasv2d $p |- ( ( ph /\ A e. V ) -> D = F ) $= f5_riotasv2d f11_riotasv2d p_elex e7_riotasv2d f0_riotasv2d f9_riotasv2d f6_riotasv2d a_wcel f5_riotasv2d a_cvv a_wcel p_adantr e8_riotasv2d f0_riotasv2d f2_riotasv2d f5_riotasv2d a_cvv a_wcel p_adantr e7_riotasv2d f0_riotasv2d f9_riotasv2d f6_riotasv2d a_wcel f5_riotasv2d a_cvv a_wcel p_adantr f4_riotasv2d a_sup_set_class f9_riotasv2d f6_riotasv2d p_eleq1 f4_riotasv2d a_sup_set_class f9_riotasv2d a_wceq f4_riotasv2d a_sup_set_class f6_riotasv2d a_wcel f9_riotasv2d f6_riotasv2d a_wcel a_wb f0_riotasv2d p_adantl e4_riotasv2d f0_riotasv2d f4_riotasv2d a_sup_set_class f9_riotasv2d a_wceq a_wa f4_riotasv2d a_sup_set_class f6_riotasv2d a_wcel f9_riotasv2d f6_riotasv2d a_wcel f1_riotasv2d f2_riotasv2d p_anbi12d e5_riotasv2d f0_riotasv2d f4_riotasv2d a_sup_set_class f9_riotasv2d a_wceq a_wa f7_riotasv2d f10_riotasv2d f8_riotasv2d p_eqeq2d f0_riotasv2d f4_riotasv2d a_sup_set_class f9_riotasv2d a_wceq a_wa f4_riotasv2d a_sup_set_class f6_riotasv2d a_wcel f1_riotasv2d a_wa f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d a_wa f8_riotasv2d f7_riotasv2d a_wceq f8_riotasv2d f10_riotasv2d a_wceq p_imbi12d f0_riotasv2d f4_riotasv2d a_sup_set_class f9_riotasv2d a_wceq f4_riotasv2d a_sup_set_class f6_riotasv2d a_wcel f1_riotasv2d a_wa f8_riotasv2d f7_riotasv2d a_wceq a_wi f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d a_wa f8_riotasv2d f10_riotasv2d a_wceq a_wi a_wb f5_riotasv2d a_cvv a_wcel p_adantlr e3_riotasv2d e6_riotasv2d f0_riotasv2d f1_riotasv2d f3_riotasv2d f4_riotasv2d f5_riotasv2d f6_riotasv2d f7_riotasv2d f8_riotasv2d a_cvv p_riotasvd e0_riotasv2d f5_riotasv2d a_cvv a_wcel f4_riotasv2d p_nfv f0_riotasv2d f5_riotasv2d a_cvv a_wcel f4_riotasv2d p_nfan f0_riotasv2d f5_riotasv2d a_cvv a_wcel a_wa f4_riotasv2d f9_riotasv2d p_nfcvd f0_riotasv2d f9_riotasv2d f6_riotasv2d a_wcel f4_riotasv2d p_nfvd e2_riotasv2d f0_riotasv2d f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d f4_riotasv2d p_nfand f1_riotasv2d f3_riotasv2d a_sup_set_class f7_riotasv2d a_wceq a_wi f4_riotasv2d f6_riotasv2d p_nfra1 f4_riotasv2d f5_riotasv2d p_nfcv f1_riotasv2d f3_riotasv2d a_sup_set_class f7_riotasv2d a_wceq a_wi f4_riotasv2d f6_riotasv2d a_wral f4_riotasv2d f3_riotasv2d f5_riotasv2d p_nfriota e0_riotasv2d e3_riotasv2d f0_riotasv2d f4_riotasv2d f8_riotasv2d f1_riotasv2d f3_riotasv2d a_sup_set_class f7_riotasv2d a_wceq a_wi f4_riotasv2d f6_riotasv2d a_wral f3_riotasv2d f5_riotasv2d a_crio p_nfceqdf f0_riotasv2d f4_riotasv2d f8_riotasv2d a_wnfc f4_riotasv2d f1_riotasv2d f3_riotasv2d a_sup_set_class f7_riotasv2d a_wceq a_wi f4_riotasv2d f6_riotasv2d a_wral f3_riotasv2d f5_riotasv2d a_crio a_wnfc p_mpbiri e1_riotasv2d f0_riotasv2d f4_riotasv2d f8_riotasv2d f10_riotasv2d p_nfeqd f0_riotasv2d f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d a_wa f8_riotasv2d f10_riotasv2d a_wceq f4_riotasv2d p_nfimd f0_riotasv2d f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d a_wa f8_riotasv2d f10_riotasv2d a_wceq a_wi f4_riotasv2d a_wnf f5_riotasv2d a_cvv a_wcel p_adantr f0_riotasv2d f5_riotasv2d a_cvv a_wcel a_wa f4_riotasv2d a_sup_set_class f6_riotasv2d a_wcel f1_riotasv2d a_wa f8_riotasv2d f7_riotasv2d a_wceq a_wi f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d a_wa f8_riotasv2d f10_riotasv2d a_wceq a_wi f4_riotasv2d f9_riotasv2d f6_riotasv2d p_vtocldf f0_riotasv2d f5_riotasv2d a_cvv a_wcel a_wa f9_riotasv2d f6_riotasv2d a_wcel f2_riotasv2d f8_riotasv2d f10_riotasv2d a_wceq p_mp2and f5_riotasv2d f11_riotasv2d a_wcel f0_riotasv2d f5_riotasv2d a_cvv a_wcel f8_riotasv2d f10_riotasv2d a_wceq p_sylan2 $.
$}

$(Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 1-Feb-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch x y z A B C D E F V  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x z C  $.
	$d z D  $.
	$d y z E  $.
	$d z F  $.
	$d z ph  $.
	$d x z ps  $.
	f0_riotasv2dOLD $f wff ph $.
	f1_riotasv2dOLD $f wff ps $.
	f2_riotasv2dOLD $f wff ch $.
	f3_riotasv2dOLD $f set x $.
	f4_riotasv2dOLD $f set y $.
	f5_riotasv2dOLD $f set z $.
	f6_riotasv2dOLD $f class A $.
	f7_riotasv2dOLD $f class B $.
	f8_riotasv2dOLD $f class C $.
	f9_riotasv2dOLD $f class D $.
	f10_riotasv2dOLD $f class E $.
	f11_riotasv2dOLD $f class F $.
	f12_riotasv2dOLD $f class V $.
	e0_riotasv2dOLD $e |- ( ph -> A. x ph ) $.
	e1_riotasv2dOLD $e |- ( ph -> A. y ph ) $.
	e2_riotasv2dOLD $e |- ( ph -> ( z e. F -> A. y z e. F ) ) $.
	e3_riotasv2dOLD $e |- ( ph -> ( ch -> A. y ch ) ) $.
	e4_riotasv2dOLD $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	e5_riotasv2dOLD $e |- ( ph -> ( y = E -> ( ps <-> ch ) ) ) $.
	e6_riotasv2dOLD $e |- ( ph -> ( y = E -> C = F ) ) $.
	p_riotasv2dOLD $p |- ( ( ( ph /\ A e. V ) /\ ( D e. A /\ E e. B /\ ch ) ) -> D = F ) $= f6_riotasv2dOLD f12_riotasv2dOLD p_elex f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f10_riotasv2dOLD p_nfcvd f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD p_nfra1 f4_riotasv2dOLD f6_riotasv2dOLD p_nfcv f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f4_riotasv2dOLD f3_riotasv2dOLD f6_riotasv2dOLD p_nfriota e1_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD p_nfi f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfan f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfan e4_riotasv2dOLD f0_riotasv2dOLD f9_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f3_riotasv2dOLD f6_riotasv2dOLD a_crio a_wceq f6_riotasv2dOLD a_cvv a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_ad2antrr f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f9_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f3_riotasv2dOLD f6_riotasv2dOLD a_crio p_nfceqdf f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f9_riotasv2dOLD a_wnfc f4_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f3_riotasv2dOLD f6_riotasv2dOLD a_crio a_wnfc p_mpbiri f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f6_riotasv2dOLD p_nfcvd f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f9_riotasv2dOLD f6_riotasv2dOLD p_nfeld f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfvd e1_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD p_nfi e3_riotasv2dOLD f0_riotasv2dOLD f2_riotasv2dOLD f4_riotasv2dOLD p_nfd f0_riotasv2dOLD f2_riotasv2dOLD f4_riotasv2dOLD a_wnf f6_riotasv2dOLD a_cvv a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_ad2antrr f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD f4_riotasv2dOLD p_nf3and f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD p_nfra1 f4_riotasv2dOLD f6_riotasv2dOLD p_nfcv f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f4_riotasv2dOLD f3_riotasv2dOLD f6_riotasv2dOLD p_nfriota e1_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD p_nfi f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfan f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfan e4_riotasv2dOLD f0_riotasv2dOLD f9_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f3_riotasv2dOLD f6_riotasv2dOLD a_crio a_wceq f6_riotasv2dOLD a_cvv a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_ad2antrr f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f9_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f3_riotasv2dOLD f6_riotasv2dOLD a_crio p_nfceqdf f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f9_riotasv2dOLD a_wnfc f4_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD a_sup_set_class f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f7_riotasv2dOLD a_wral f3_riotasv2dOLD f6_riotasv2dOLD a_crio a_wnfc p_mpbiri f0_riotasv2dOLD f5_riotasv2dOLD p_nfv e1_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD p_nfi e2_riotasv2dOLD f0_riotasv2dOLD f5_riotasv2dOLD a_sup_set_class f11_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfd f0_riotasv2dOLD f4_riotasv2dOLD f5_riotasv2dOLD f11_riotasv2dOLD p_nfcd f0_riotasv2dOLD f4_riotasv2dOLD f11_riotasv2dOLD a_wnfc f6_riotasv2dOLD a_cvv a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_ad2antrr f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD p_nfeqd f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq f4_riotasv2dOLD p_nfimd e1_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD p_nfi f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfan f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f4_riotasv2dOLD p_nfan f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD f7_riotasv2dOLD p_eleq1 f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wb f0_riotasv2dOLD p_adantl e5_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f1_riotasv2dOLD f2_riotasv2dOLD a_wb p_imp f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq a_wa f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f1_riotasv2dOLD f2_riotasv2dOLD f9_riotasv2dOLD f6_riotasv2dOLD a_wcel p_3anbi23d e6_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f8_riotasv2dOLD f11_riotasv2dOLD a_wceq p_imp f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq a_wa f8_riotasv2dOLD f11_riotasv2dOLD f9_riotasv2dOLD p_eqeq2d f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq f9_riotasv2dOLD f11_riotasv2dOLD a_wceq p_imbi12d f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi a_wb p_ex f0_riotasv2dOLD f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi a_wb a_wi f6_riotasv2dOLD a_cvv a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_ad2antrr f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi a_wb a_wi f4_riotasv2dOLD p_alrimi e1_riotasv2dOLD f0_riotasv2dOLD f4_riotasv2dOLD p_nfi f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfv f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel f4_riotasv2dOLD p_nfan e0_riotasv2dOLD e1_riotasv2dOLD e4_riotasv2dOLD f0_riotasv2dOLD f1_riotasv2dOLD f3_riotasv2dOLD f4_riotasv2dOLD f6_riotasv2dOLD f7_riotasv2dOLD f8_riotasv2dOLD f9_riotasv2dOLD a_cvv p_riotasvdOLD f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_wa f9_riotasv2dOLD f8_riotasv2dOLD a_wceq p_3exp f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD f9_riotasv2dOLD f8_riotasv2dOLD a_wceq p_exp4a f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD f9_riotasv2dOLD f8_riotasv2dOLD a_wceq p_3impd f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD p_alrimi f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD a_wal f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_adantr f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel p_simpr f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD f10_riotasv2dOLD f7_riotasv2dOLD p_vtoclgft f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f4_riotasv2dOLD f10_riotasv2dOLD a_wnfc f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD a_wnf f4_riotasv2dOLD a_sup_set_class f10_riotasv2dOLD a_wceq f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi a_wb a_wi f4_riotasv2dOLD a_wal f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f4_riotasv2dOLD a_sup_set_class f7_riotasv2dOLD a_wcel f1_riotasv2dOLD a_w3a f9_riotasv2dOLD f8_riotasv2dOLD a_wceq a_wi f4_riotasv2dOLD a_wal f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi p_syl221anc f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD a_wceq p_3expd f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi p_com23 f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f2_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi a_wi a_wi p_ex f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f2_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi a_wi p_pm2.43d f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f2_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD a_wceq a_wi p_com23 f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel a_wa f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD f9_riotasv2dOLD f11_riotasv2dOLD a_wceq p_3imp2 f6_riotasv2dOLD f12_riotasv2dOLD a_wcel f0_riotasv2dOLD f6_riotasv2dOLD a_cvv a_wcel f9_riotasv2dOLD f6_riotasv2dOLD a_wcel f10_riotasv2dOLD f7_riotasv2dOLD a_wcel f2_riotasv2dOLD a_w3a f9_riotasv2dOLD f11_riotasv2dOLD a_wceq p_sylanl2 $.
$}

$(The value of description binder ` D ` for a single-valued class
       expression ` C ( y ) ` (as in e.g. ~ reusv2 ) in the form of a
       substitution instance.  Special case of ~ riota2f .  (Contributed by NM,
       3-Mar-2013.)  (Proof shortened by Mario Carneiro, 6-Dec-2016.) $)

${
	$v ph x y A B C D E V  $.
	$d x y A  $.
	$d x y B  $.
	$d x C  $.
	$d D  $.
	$d x y E  $.
	$d x ph  $.
	f0_riotasv2s $f wff ph $.
	f1_riotasv2s $f set x $.
	f2_riotasv2s $f set y $.
	f3_riotasv2s $f class A $.
	f4_riotasv2s $f class B $.
	f5_riotasv2s $f class C $.
	f6_riotasv2s $f class D $.
	f7_riotasv2s $f class E $.
	f8_riotasv2s $f class V $.
	e0_riotasv2s $e |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) ) $.
	p_riotasv2s $p |- ( ( A e. V /\ D e. A /\ ( E e. B /\ [. E / y ]. ph ) ) -> D = [_ E / y ]_ C ) $= f3_riotasv2s f8_riotasv2s a_wcel f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa p_3simpc f3_riotasv2s f8_riotasv2s a_wcel f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa p_simp1 e0_riotasv2s f0_riotasv2s f1_riotasv2s a_sup_set_class f5_riotasv2s a_wceq a_wi f2_riotasv2s f4_riotasv2s p_nfra1 f2_riotasv2s f3_riotasv2s p_nfcv f0_riotasv2s f1_riotasv2s a_sup_set_class f5_riotasv2s a_wceq a_wi f2_riotasv2s f4_riotasv2s a_wral f2_riotasv2s f1_riotasv2s f3_riotasv2s p_nfriota f2_riotasv2s f6_riotasv2s f0_riotasv2s f1_riotasv2s a_sup_set_class f5_riotasv2s a_wceq a_wi f2_riotasv2s f4_riotasv2s a_wral f1_riotasv2s f3_riotasv2s a_crio p_nfcxfr f2_riotasv2s f6_riotasv2s f3_riotasv2s p_nfel1 f7_riotasv2s f4_riotasv2s a_wcel f2_riotasv2s p_nfv f0_riotasv2s f2_riotasv2s f7_riotasv2s p_nfsbc1v f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc f2_riotasv2s p_nfan f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa f2_riotasv2s p_nfan f2_riotasv2s f7_riotasv2s f5_riotasv2s p_nfcsb1v f2_riotasv2s f2_riotasv2s f7_riotasv2s f5_riotasv2s a_csb a_wnfc f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa p_a1i f0_riotasv2s f2_riotasv2s f7_riotasv2s p_nfsbc1v f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc f2_riotasv2s a_wnf f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa p_a1i e0_riotasv2s f6_riotasv2s f0_riotasv2s f1_riotasv2s a_sup_set_class f5_riotasv2s a_wceq a_wi f2_riotasv2s f4_riotasv2s a_wral f1_riotasv2s f3_riotasv2s a_crio a_wceq f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa p_a1i f0_riotasv2s f2_riotasv2s f7_riotasv2s p_sbceq1a f2_riotasv2s a_sup_set_class f7_riotasv2s a_wceq f0_riotasv2s f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wb f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa p_adantl f2_riotasv2s f7_riotasv2s f5_riotasv2s p_csbeq1a f2_riotasv2s a_sup_set_class f7_riotasv2s a_wceq f5_riotasv2s f2_riotasv2s f7_riotasv2s f5_riotasv2s a_csb a_wceq f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa p_adantl f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa p_simpl f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc p_simprl f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc p_simprr f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa f0_riotasv2s f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc f1_riotasv2s f2_riotasv2s f3_riotasv2s f4_riotasv2s f5_riotasv2s f6_riotasv2s f7_riotasv2s f2_riotasv2s f7_riotasv2s f5_riotasv2s a_csb f8_riotasv2s p_riotasv2d f3_riotasv2s f8_riotasv2s a_wcel f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_w3a f6_riotasv2s f3_riotasv2s a_wcel f7_riotasv2s f4_riotasv2s a_wcel f0_riotasv2s f2_riotasv2s f7_riotasv2s a_wsbc a_wa a_wa f3_riotasv2s f8_riotasv2s a_wcel f6_riotasv2s f2_riotasv2s f7_riotasv2s f5_riotasv2s a_csb a_wceq p_syl2anc $.
$}

$(Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 26-Jan-2013.)  (Proof shortened by Mario Carneiro,
       6-Dec-2016.) $)

${
	$v ph x y A B C D  $.
	$d x y A  $.
	$d x B  $.
	$d x C  $.
	$d x ph  $.
	$d D  $.
	f0_riotasv $f wff ph $.
	f1_riotasv $f set x $.
	f2_riotasv $f set y $.
	f3_riotasv $f class A $.
	f4_riotasv $f class B $.
	f5_riotasv $f class C $.
	f6_riotasv $f class D $.
	e0_riotasv $e |- A e. _V $.
	e1_riotasv $e |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) ) $.
	p_riotasv $p |- ( ( D e. A /\ y e. B /\ ph ) -> D = C ) $= e0_riotasv e1_riotasv f6_riotasv f0_riotasv f1_riotasv a_sup_set_class f5_riotasv a_wceq a_wi f2_riotasv f4_riotasv a_wral f1_riotasv f3_riotasv a_crio a_wceq f6_riotasv f3_riotasv a_wcel p_a1i f6_riotasv f3_riotasv a_wcel p_id f6_riotasv f3_riotasv a_wcel f0_riotasv f1_riotasv f2_riotasv f3_riotasv f4_riotasv f5_riotasv f6_riotasv a_cvv p_riotasvd f6_riotasv f3_riotasv a_wcel f3_riotasv a_cvv a_wcel f2_riotasv a_sup_set_class f4_riotasv a_wcel f0_riotasv a_wa f6_riotasv f5_riotasv a_wceq a_wi p_mpan2 f6_riotasv f3_riotasv a_wcel f2_riotasv a_sup_set_class f4_riotasv a_wcel f0_riotasv f6_riotasv f5_riotasv a_wceq p_3impib $.
$}

$(A property ` ch ` holding for a representative of a single-valued class
       expression ` C ( y ) ` (see e.g. ~ reusv2 ) also holds for its
       description binder ` D ` (in the form of property ` th ` ).
       (Contributed by NM, 5-Mar-2013.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)

${
	$v ph ps ch th x y A B C D V  $.
	$d x y A  $.
	$d x B  $.
	$d x C  $.
	$d D  $.
	$d ph  $.
	$d x ps  $.
	f0_riotasv3d $f wff ph $.
	f1_riotasv3d $f wff ps $.
	f2_riotasv3d $f wff ch $.
	f3_riotasv3d $f wff th $.
	f4_riotasv3d $f set x $.
	f5_riotasv3d $f set y $.
	f6_riotasv3d $f class A $.
	f7_riotasv3d $f class B $.
	f8_riotasv3d $f class C $.
	f9_riotasv3d $f class D $.
	f10_riotasv3d $f class V $.
	e0_riotasv3d $e |- F/ y ph $.
	e1_riotasv3d $e |- ( ph -> F/ y th ) $.
	e2_riotasv3d $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	e3_riotasv3d $e |- ( ( ph /\ C = D ) -> ( ch <-> th ) ) $.
	e4_riotasv3d $e |- ( ph -> ( ( y e. B /\ ps ) -> ch ) ) $.
	e5_riotasv3d $e |- ( ph -> D e. A ) $.
	e6_riotasv3d $e |- ( ph -> E. y e. B ps ) $.
	p_riotasv3d $p |- ( ( ph /\ A e. V ) -> th ) $= f6_riotasv3d f10_riotasv3d p_elex e6_riotasv3d f0_riotasv3d f1_riotasv3d f5_riotasv3d f7_riotasv3d a_wrex f6_riotasv3d a_cvv a_wcel p_adantr e0_riotasv3d f6_riotasv3d a_cvv a_wcel f5_riotasv3d p_nfv e4_riotasv3d f0_riotasv3d f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d a_wa f2_riotasv3d p_imp f0_riotasv3d f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d a_wa f2_riotasv3d f6_riotasv3d a_cvv a_wcel p_adantrl e2_riotasv3d e5_riotasv3d f0_riotasv3d f1_riotasv3d f4_riotasv3d f5_riotasv3d f6_riotasv3d f7_riotasv3d f8_riotasv3d f9_riotasv3d a_cvv p_riotasvd f0_riotasv3d f6_riotasv3d a_cvv a_wcel f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d a_wa f9_riotasv3d f8_riotasv3d a_wceq p_impr f0_riotasv3d f6_riotasv3d a_cvv a_wcel f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d a_wa a_wa a_wa f9_riotasv3d f8_riotasv3d p_eqcomd e3_riotasv3d f0_riotasv3d f6_riotasv3d a_cvv a_wcel f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d a_wa a_wa f8_riotasv3d f9_riotasv3d a_wceq f2_riotasv3d f3_riotasv3d a_wb p_syldan f0_riotasv3d f6_riotasv3d a_cvv a_wcel f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d a_wa a_wa a_wa f2_riotasv3d f3_riotasv3d p_mpbid f0_riotasv3d f6_riotasv3d a_cvv a_wcel f5_riotasv3d a_sup_set_class f7_riotasv3d a_wcel f1_riotasv3d f3_riotasv3d p_exp45 f0_riotasv3d f6_riotasv3d a_cvv a_wcel f1_riotasv3d f3_riotasv3d a_wi f5_riotasv3d f7_riotasv3d p_ralrimd e1_riotasv3d f1_riotasv3d f3_riotasv3d f5_riotasv3d f7_riotasv3d p_r19.23t f0_riotasv3d f3_riotasv3d f5_riotasv3d a_wnf f1_riotasv3d f3_riotasv3d a_wi f5_riotasv3d f7_riotasv3d a_wral f1_riotasv3d f5_riotasv3d f7_riotasv3d a_wrex f3_riotasv3d a_wi a_wb p_syl f0_riotasv3d f6_riotasv3d a_cvv a_wcel f1_riotasv3d f3_riotasv3d a_wi f5_riotasv3d f7_riotasv3d a_wral f1_riotasv3d f5_riotasv3d f7_riotasv3d a_wrex f3_riotasv3d a_wi p_sylibd f0_riotasv3d f6_riotasv3d a_cvv a_wcel f1_riotasv3d f5_riotasv3d f7_riotasv3d a_wrex f3_riotasv3d a_wi p_imp f0_riotasv3d f6_riotasv3d a_cvv a_wcel a_wa f1_riotasv3d f5_riotasv3d f7_riotasv3d a_wrex f3_riotasv3d p_mpd f6_riotasv3d f10_riotasv3d a_wcel f0_riotasv3d f6_riotasv3d a_cvv a_wcel f3_riotasv3d p_sylan2 $.
$}

$(A property ` ch ` holding for a representative of a single-valued class
       expression ` C ( y ) ` (see e.g. ~ reusv2 ) also holds for its
       description binder ` D ` (in the form of property ` th ` ).
       (Contributed by NM, 1-Feb-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch th x y A B C D V  $.
	$d x y A  $.
	$d x B  $.
	$d x C  $.
	$d D  $.
	$d ph  $.
	$d x ps  $.
	f0_riotasv3dOLD $f wff ph $.
	f1_riotasv3dOLD $f wff ps $.
	f2_riotasv3dOLD $f wff ch $.
	f3_riotasv3dOLD $f wff th $.
	f4_riotasv3dOLD $f set x $.
	f5_riotasv3dOLD $f set y $.
	f6_riotasv3dOLD $f class A $.
	f7_riotasv3dOLD $f class B $.
	f8_riotasv3dOLD $f class C $.
	f9_riotasv3dOLD $f class D $.
	f10_riotasv3dOLD $f class V $.
	e0_riotasv3dOLD $e |- ( ph -> A. x ph ) $.
	e1_riotasv3dOLD $e |- ( ph -> A. y ph ) $.
	e2_riotasv3dOLD $e |- ( ph -> ( th -> A. y th ) ) $.
	e3_riotasv3dOLD $e |- ( ph -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
	e4_riotasv3dOLD $e |- ( ph -> ( C = D -> ( ch <-> th ) ) ) $.
	e5_riotasv3dOLD $e |- ( ph -> ( ( y e. B /\ ps ) -> ch ) ) $.
	p_riotasv3dOLD $p |- ( ( ph /\ ( A e. V /\ D e. A /\ E. y e. B ps ) ) -> th ) $= f6_riotasv3dOLD f10_riotasv3dOLD p_elex e1_riotasv3dOLD f0_riotasv3dOLD f5_riotasv3dOLD p_nfi e5_riotasv3dOLD f0_riotasv3dOLD f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa f2_riotasv3dOLD p_imp f0_riotasv3dOLD f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa f2_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa p_adantrl e0_riotasv3dOLD e1_riotasv3dOLD e3_riotasv3dOLD f0_riotasv3dOLD f1_riotasv3dOLD f4_riotasv3dOLD f5_riotasv3dOLD f6_riotasv3dOLD f7_riotasv3dOLD f8_riotasv3dOLD f9_riotasv3dOLD a_cvv p_riotasvdOLD f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel a_wa f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa a_w3a f9_riotasv3dOLD f8_riotasv3dOLD p_eqcomd f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel a_wa f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa f8_riotasv3dOLD f9_riotasv3dOLD a_wceq p_3exp f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa f8_riotasv3dOLD f9_riotasv3dOLD a_wceq a_wi a_wi p_ex f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa f8_riotasv3dOLD f9_riotasv3dOLD a_wceq p_imp4c e4_riotasv3dOLD f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa a_wa f8_riotasv3dOLD f9_riotasv3dOLD a_wceq f2_riotasv3dOLD f3_riotasv3dOLD a_wb p_syld f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa a_wa f2_riotasv3dOLD f3_riotasv3dOLD a_wb p_imp f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD a_wa a_wa a_wa f2_riotasv3dOLD f3_riotasv3dOLD p_mpbid f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD f3_riotasv3dOLD p_exp45 f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f5_riotasv3dOLD a_sup_set_class f7_riotasv3dOLD a_wcel f1_riotasv3dOLD f3_riotasv3dOLD a_wi p_com23 f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi a_wi f5_riotasv3dOLD f7_riotasv3dOLD p_ralrimi f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f5_riotasv3dOLD p_nfvd f1_riotasv3dOLD f4_riotasv3dOLD a_sup_set_class f8_riotasv3dOLD a_wceq a_wi f5_riotasv3dOLD f7_riotasv3dOLD p_nfra1 f5_riotasv3dOLD f6_riotasv3dOLD p_nfcv f1_riotasv3dOLD f4_riotasv3dOLD a_sup_set_class f8_riotasv3dOLD a_wceq a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f5_riotasv3dOLD f4_riotasv3dOLD f6_riotasv3dOLD p_nfriota e1_riotasv3dOLD f0_riotasv3dOLD f5_riotasv3dOLD p_nfi e3_riotasv3dOLD f0_riotasv3dOLD f5_riotasv3dOLD f9_riotasv3dOLD f1_riotasv3dOLD f4_riotasv3dOLD a_sup_set_class f8_riotasv3dOLD a_wceq a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f4_riotasv3dOLD f6_riotasv3dOLD a_crio p_nfceqdf f0_riotasv3dOLD f5_riotasv3dOLD f9_riotasv3dOLD a_wnfc f5_riotasv3dOLD f1_riotasv3dOLD f4_riotasv3dOLD a_sup_set_class f8_riotasv3dOLD a_wceq a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f4_riotasv3dOLD f6_riotasv3dOLD a_crio a_wnfc p_mpbiri f0_riotasv3dOLD f5_riotasv3dOLD f6_riotasv3dOLD p_nfcvd f0_riotasv3dOLD f5_riotasv3dOLD f9_riotasv3dOLD f6_riotasv3dOLD p_nfeld f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f5_riotasv3dOLD p_nfand f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi f5_riotasv3dOLD f7_riotasv3dOLD p_r19.21t f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f5_riotasv3dOLD a_wnf f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral a_wi a_wb p_syl f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral a_wi p_mpbid e1_riotasv3dOLD f0_riotasv3dOLD f5_riotasv3dOLD p_nfi e2_riotasv3dOLD f0_riotasv3dOLD f3_riotasv3dOLD f5_riotasv3dOLD p_nfd f1_riotasv3dOLD f3_riotasv3dOLD f5_riotasv3dOLD f7_riotasv3dOLD p_r19.23t f0_riotasv3dOLD f3_riotasv3dOLD f5_riotasv3dOLD a_wnf f1_riotasv3dOLD f3_riotasv3dOLD a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f1_riotasv3dOLD f5_riotasv3dOLD f7_riotasv3dOLD a_wrex f3_riotasv3dOLD a_wi a_wb p_syl f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel a_wa f1_riotasv3dOLD f3_riotasv3dOLD a_wi f5_riotasv3dOLD f7_riotasv3dOLD a_wral f1_riotasv3dOLD f5_riotasv3dOLD f7_riotasv3dOLD a_wrex f3_riotasv3dOLD a_wi p_sylibd f0_riotasv3dOLD f6_riotasv3dOLD a_cvv a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f1_riotasv3dOLD f5_riotasv3dOLD f7_riotasv3dOLD a_wrex f3_riotasv3dOLD a_wi p_exp3a f6_riotasv3dOLD f10_riotasv3dOLD a_wcel f6_riotasv3dOLD a_cvv a_wcel f0_riotasv3dOLD f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f1_riotasv3dOLD f5_riotasv3dOLD f7_riotasv3dOLD a_wrex f3_riotasv3dOLD a_wi a_wi p_syl5 f0_riotasv3dOLD f6_riotasv3dOLD f10_riotasv3dOLD a_wcel f9_riotasv3dOLD f6_riotasv3dOLD a_wcel f1_riotasv3dOLD f5_riotasv3dOLD f7_riotasv3dOLD a_wrex f3_riotasv3dOLD p_3imp2 $.
$}


