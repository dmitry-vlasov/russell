$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Ordered_pair_theorem.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Ordered-pair class abstractions (cont.)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(The law of concretion.  Special case of Theorem 9.5 of [Quine] p. 61.
       (Contributed by NM, 14-Apr-1995.)  (Proof shortened by Andrew Salmon,
       25-Jul-2011.) $)

${
	$v ph x y  $.
	$d x z  $.
	$d y z  $.
	$d ph z  $.
	f0_opabid $f wff ph $.
	f1_opabid $f set x $.
	f2_opabid $f set y $.
	i0_opabid $f set z $.
	p_opabid $p |- ( <. x , y >. e. { <. x , y >. | ph } <-> ph ) $= f1_opabid a_sup_set_class f2_opabid a_sup_set_class p_opex f0_opabid f1_opabid f2_opabid i0_opabid a_sup_set_class p_copsexg i0_opabid a_sup_set_class f1_opabid a_sup_set_class f2_opabid a_sup_set_class a_cop a_wceq f0_opabid i0_opabid a_sup_set_class f1_opabid a_sup_set_class f2_opabid a_sup_set_class a_cop a_wceq f0_opabid a_wa f2_opabid a_wex f1_opabid a_wex p_bicomd f0_opabid f1_opabid f2_opabid i0_opabid a_df-opab i0_opabid a_sup_set_class f1_opabid a_sup_set_class f2_opabid a_sup_set_class a_cop a_wceq f0_opabid a_wa f2_opabid a_wex f1_opabid a_wex f0_opabid i0_opabid f1_opabid a_sup_set_class f2_opabid a_sup_set_class a_cop f0_opabid f1_opabid f2_opabid a_copab p_elab2 $.
$}

$(Membership in a class abstraction of pairs.  (Contributed by NM,
       24-Mar-1998.) $)

${
	$v ph x y A  $.
	$d x z A  $.
	$d y z A  $.
	$d z ph  $.
	f0_elopab $f wff ph $.
	f1_elopab $f set x $.
	f2_elopab $f set y $.
	f3_elopab $f class A $.
	i0_elopab $f set z $.
	p_elopab $p |- ( A e. { <. x , y >. | ph } <-> E. x E. y ( A = <. x , y >. /\ ph ) ) $= f3_elopab f0_elopab f1_elopab f2_elopab a_copab p_elex f1_elopab a_sup_set_class f2_elopab a_sup_set_class p_opex f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_cvv p_eleq1 f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f3_elopab a_cvv a_wcel f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_cvv a_wcel p_mpbiri f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f3_elopab a_cvv a_wcel f0_elopab p_adantr f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab a_wa f3_elopab a_cvv a_wcel f1_elopab f2_elopab p_exlimivv i0_elopab a_sup_set_class f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop p_eqeq1 i0_elopab a_sup_set_class f3_elopab a_wceq i0_elopab a_sup_set_class f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab p_anbi1d i0_elopab a_sup_set_class f3_elopab a_wceq i0_elopab a_sup_set_class f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab a_wa f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab a_wa f1_elopab f2_elopab p_2exbidv f0_elopab f1_elopab f2_elopab i0_elopab a_df-opab i0_elopab a_sup_set_class f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab a_wa f2_elopab a_wex f1_elopab a_wex f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab a_wa f2_elopab a_wex f1_elopab a_wex i0_elopab f3_elopab f0_elopab f1_elopab f2_elopab a_copab a_cvv p_elab2g f3_elopab f0_elopab f1_elopab f2_elopab a_copab a_wcel f3_elopab a_cvv a_wcel f3_elopab f1_elopab a_sup_set_class f2_elopab a_sup_set_class a_cop a_wceq f0_elopab a_wa f2_elopab a_wex f1_elopab a_wex p_pm5.21nii $.
$}

$(The law of concretion in terms of substitutions.  (Contributed by NM,
       30-Sep-2002.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.)
       (New usage is discouraged.) $)

${
	$v ph x y z w  $.
	$d x y z  $.
	$d x y w  $.
	$d ph  $.
	f0_opelopabsbOLD $f wff ph $.
	f1_opelopabsbOLD $f set x $.
	f2_opelopabsbOLD $f set y $.
	f3_opelopabsbOLD $f set z $.
	f4_opelopabsbOLD $f set w $.
	p_opelopabsbOLD $p |- ( <. z , w >. e. { <. x , y >. | ph } <-> [ w / y ] [ z / x ] ph ) $= f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f0_opelopabsbOLD a_wa f1_opelopabsbOLD f2_opelopabsbOLD p_excom f3_opelopabsbOLD p_vex f4_opelopabsbOLD p_vex f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class p_opth f3_opelopabsbOLD f1_opelopabsbOLD p_equcom f4_opelopabsbOLD f2_opelopabsbOLD p_equcom f3_opelopabsbOLD a_sup_set_class f1_opelopabsbOLD a_sup_set_class a_wceq f1_opelopabsbOLD a_sup_set_class f3_opelopabsbOLD a_sup_set_class a_wceq f4_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_wceq f2_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_wceq p_anbi12ci f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f3_opelopabsbOLD a_sup_set_class f1_opelopabsbOLD a_sup_set_class a_wceq f4_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_wceq a_wa f2_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_wceq f1_opelopabsbOLD a_sup_set_class f3_opelopabsbOLD a_sup_set_class a_wceq a_wa p_bitri f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f2_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_wceq f1_opelopabsbOLD a_sup_set_class f3_opelopabsbOLD a_sup_set_class a_wceq a_wa f0_opelopabsbOLD p_anbi1i f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f0_opelopabsbOLD a_wa f2_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_wceq f1_opelopabsbOLD a_sup_set_class f3_opelopabsbOLD a_sup_set_class a_wceq a_wa f0_opelopabsbOLD a_wa f2_opelopabsbOLD f1_opelopabsbOLD p_2exbii f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f0_opelopabsbOLD a_wa f2_opelopabsbOLD a_wex f1_opelopabsbOLD a_wex f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f0_opelopabsbOLD a_wa f1_opelopabsbOLD a_wex f2_opelopabsbOLD a_wex f2_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_wceq f1_opelopabsbOLD a_sup_set_class f3_opelopabsbOLD a_sup_set_class a_wceq a_wa f0_opelopabsbOLD a_wa f1_opelopabsbOLD a_wex f2_opelopabsbOLD a_wex p_bitri f0_opelopabsbOLD f1_opelopabsbOLD f2_opelopabsbOLD f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop p_elopab f0_opelopabsbOLD f2_opelopabsbOLD f1_opelopabsbOLD f4_opelopabsbOLD f3_opelopabsbOLD p_2sb5 f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f1_opelopabsbOLD a_sup_set_class f2_opelopabsbOLD a_sup_set_class a_cop a_wceq f0_opelopabsbOLD a_wa f2_opelopabsbOLD a_wex f1_opelopabsbOLD a_wex f2_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_wceq f1_opelopabsbOLD a_sup_set_class f3_opelopabsbOLD a_sup_set_class a_wceq a_wa f0_opelopabsbOLD a_wa f1_opelopabsbOLD a_wex f2_opelopabsbOLD a_wex f3_opelopabsbOLD a_sup_set_class f4_opelopabsbOLD a_sup_set_class a_cop f0_opelopabsbOLD f1_opelopabsbOLD f2_opelopabsbOLD a_copab a_wcel f0_opelopabsbOLD f1_opelopabsbOLD f3_opelopabsbOLD a_wsb f2_opelopabsbOLD f4_opelopabsbOLD a_wsb p_3bitr4i $.
$}

$(The law of concretion in terms of substitutions.  (Contributed by NM,
       17-Mar-2008.)  (New usage is discouraged.) $)

${
	$v ph x y z w R  $.
	$d x y z  $.
	$d x y w  $.
	$d ph  $.
	f0_brabsbOLD $f wff ph $.
	f1_brabsbOLD $f set x $.
	f2_brabsbOLD $f set y $.
	f3_brabsbOLD $f set z $.
	f4_brabsbOLD $f set w $.
	f5_brabsbOLD $f class R $.
	e0_brabsbOLD $e |- R = { <. x , y >. | ph } $.
	p_brabsbOLD $p |- ( z R w <-> [ w / y ] [ z / x ] ph ) $= e0_brabsbOLD f3_brabsbOLD a_sup_set_class f4_brabsbOLD a_sup_set_class f5_brabsbOLD f0_brabsbOLD f1_brabsbOLD f2_brabsbOLD a_copab p_breqi f3_brabsbOLD a_sup_set_class f4_brabsbOLD a_sup_set_class f0_brabsbOLD f1_brabsbOLD f2_brabsbOLD a_copab a_df-br f0_brabsbOLD f1_brabsbOLD f2_brabsbOLD f3_brabsbOLD f4_brabsbOLD p_opelopabsbOLD f3_brabsbOLD a_sup_set_class f4_brabsbOLD a_sup_set_class f5_brabsbOLD a_wbr f3_brabsbOLD a_sup_set_class f4_brabsbOLD a_sup_set_class f0_brabsbOLD f1_brabsbOLD f2_brabsbOLD a_copab a_wbr f3_brabsbOLD a_sup_set_class f4_brabsbOLD a_sup_set_class a_cop f0_brabsbOLD f1_brabsbOLD f2_brabsbOLD a_copab a_wcel f0_brabsbOLD f1_brabsbOLD f3_brabsbOLD a_wsb f2_brabsbOLD f4_brabsbOLD a_wsb p_3bitri $.
$}

$(The law of concretion in terms of substitutions.  (Contributed by NM,
       30-Sep-2002.)  (Revised by Mario Carneiro, 18-Nov-2016.) $)

${
	$v ph x y A B  $.
	$d x y z w  $.
	$d w z A  $.
	$d w x B  $.
	$d w z ph  $.
	f0_opelopabsb $f wff ph $.
	f1_opelopabsb $f set x $.
	f2_opelopabsb $f set y $.
	f3_opelopabsb $f class A $.
	f4_opelopabsb $f class B $.
	i0_opelopabsb $f set z $.
	i1_opelopabsb $f set w $.
	p_opelopabsb $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> [. A / x ]. [. B / y ]. ph ) $= f1_opelopabsb p_vex f2_opelopabsb p_vex f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class p_opnzi a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb p_simpl a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb a_wa a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop p_eqcomd a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb a_wa f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_c0 p_necon3ai f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_c0 a_wne a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb a_wa a_wn a_ax-mp a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb a_wa f2_opelopabsb p_nex a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb a_wa f2_opelopabsb a_wex f1_opelopabsb p_nex f0_opelopabsb f1_opelopabsb f2_opelopabsb a_c0 p_elopab a_c0 f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel a_c0 f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop a_wceq f0_opelopabsb a_wa f2_opelopabsb a_wex f1_opelopabsb a_wex p_mtbir f3_opelopabsb f4_opelopabsb a_cop a_c0 f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_eleq1 f3_opelopabsb f4_opelopabsb a_cop a_c0 a_wceq f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel a_c0 f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel p_mtbiri f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f3_opelopabsb f4_opelopabsb a_cop a_c0 p_necon2ai f3_opelopabsb f4_opelopabsb p_opnz f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f3_opelopabsb f4_opelopabsb a_cop a_c0 a_wne f3_opelopabsb a_cvv a_wcel f4_opelopabsb a_cvv a_wcel a_wa p_sylib f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb p_sbcex f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb p_spesbc f0_opelopabsb f2_opelopabsb f4_opelopabsb p_sbcex f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f4_opelopabsb a_cvv a_wcel f1_opelopabsb p_exlimiv f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb a_wsbc f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb a_wex f4_opelopabsb a_cvv a_wcel p_syl f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb a_wsbc f3_opelopabsb a_cvv a_wcel f4_opelopabsb a_cvv a_wcel p_jca i0_opelopabsb a_sup_set_class f3_opelopabsb i1_opelopabsb a_sup_set_class p_opeq1 i0_opelopabsb a_sup_set_class f3_opelopabsb a_wceq i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f3_opelopabsb i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_eleq1d f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb f3_opelopabsb p_dfsbcq2 i0_opelopabsb a_sup_set_class f3_opelopabsb a_wceq i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f3_opelopabsb i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb a_wsb f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb f3_opelopabsb a_wsbc p_bibi12d i1_opelopabsb a_sup_set_class f4_opelopabsb f3_opelopabsb p_opeq2 i1_opelopabsb a_sup_set_class f4_opelopabsb a_wceq f3_opelopabsb i1_opelopabsb a_sup_set_class a_cop f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_eleq1d f0_opelopabsb f2_opelopabsb i1_opelopabsb f4_opelopabsb p_dfsbcq2 i1_opelopabsb a_sup_set_class f4_opelopabsb a_wceq f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb p_sbcbidv i1_opelopabsb a_sup_set_class f4_opelopabsb a_wceq f3_opelopabsb i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb f3_opelopabsb a_wsbc f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb a_wsbc p_bibi12d f0_opelopabsb f1_opelopabsb f2_opelopabsb p_nfopab1 f1_opelopabsb i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_nfel2 f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb p_nfs1v i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb a_wsb f1_opelopabsb p_nfbi f1_opelopabsb a_sup_set_class i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class p_opeq1 f1_opelopabsb a_sup_set_class i0_opelopabsb a_sup_set_class a_wceq f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_eleq1d f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb p_sbequ12 f1_opelopabsb a_sup_set_class i0_opelopabsb a_sup_set_class a_wceq f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb a_wsb p_bibi12d f0_opelopabsb f1_opelopabsb f2_opelopabsb p_nfopab2 f2_opelopabsb f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_nfel2 f0_opelopabsb f2_opelopabsb i1_opelopabsb p_nfs1v f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f2_opelopabsb p_nfbi f2_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class f1_opelopabsb a_sup_set_class p_opeq2 f2_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_wceq f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab p_eleq1d f0_opelopabsb f2_opelopabsb i1_opelopabsb p_sbequ12 f2_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_wceq f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb p_bibi12d f0_opelopabsb f1_opelopabsb f2_opelopabsb p_opabid f1_opelopabsb a_sup_set_class f2_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb a_wb f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb a_wb f2_opelopabsb i1_opelopabsb p_chvar f1_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb a_wb i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb a_wsb a_wb f1_opelopabsb i0_opelopabsb p_chvar i0_opelopabsb a_sup_set_class i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb i0_opelopabsb a_wsb a_wb f3_opelopabsb i1_opelopabsb a_sup_set_class a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb i1_opelopabsb a_wsb f1_opelopabsb f3_opelopabsb a_wsbc a_wb f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb a_wsbc a_wb i0_opelopabsb i1_opelopabsb f3_opelopabsb f4_opelopabsb a_cvv a_cvv p_vtocl2g f3_opelopabsb f4_opelopabsb a_cop f0_opelopabsb f1_opelopabsb f2_opelopabsb a_copab a_wcel f3_opelopabsb a_cvv a_wcel f4_opelopabsb a_cvv a_wcel a_wa f0_opelopabsb f2_opelopabsb f4_opelopabsb a_wsbc f1_opelopabsb f3_opelopabsb a_wsbc p_pm5.21nii $.
$}

$(The law of concretion in terms of substitutions.  (Contributed by NM,
       17-Mar-2008.) $)

${
	$v ph x y A B R  $.
	$d x y  $.
	$d A  $.
	$d x B  $.
	$d ph  $.
	f0_brabsb $f wff ph $.
	f1_brabsb $f set x $.
	f2_brabsb $f set y $.
	f3_brabsb $f class A $.
	f4_brabsb $f class B $.
	f5_brabsb $f class R $.
	e0_brabsb $e |- R = { <. x , y >. | ph } $.
	p_brabsb $p |- ( A R B <-> [. A / x ]. [. B / y ]. ph ) $= f3_brabsb f4_brabsb f5_brabsb a_df-br e0_brabsb f5_brabsb f0_brabsb f1_brabsb f2_brabsb a_copab f3_brabsb f4_brabsb a_cop p_eleq2i f0_brabsb f1_brabsb f2_brabsb f3_brabsb f4_brabsb p_opelopabsb f3_brabsb f4_brabsb f5_brabsb a_wbr f3_brabsb f4_brabsb a_cop f5_brabsb a_wcel f3_brabsb f4_brabsb a_cop f0_brabsb f1_brabsb f2_brabsb a_copab a_wcel f0_brabsb f2_brabsb f4_brabsb a_wsbc f1_brabsb f3_brabsb a_wsbc p_3bitri $.
$}

$(Closed theorem form of ~ opelopab .  (Contributed by NM,
       19-Feb-2013.) $)

${
	$v ph ps ch x y A B V W  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ch  $.
	$d ph  $.
	f0_opelopabt $f wff ph $.
	f1_opelopabt $f wff ps $.
	f2_opelopabt $f wff ch $.
	f3_opelopabt $f set x $.
	f4_opelopabt $f set y $.
	f5_opelopabt $f class A $.
	f6_opelopabt $f class B $.
	f7_opelopabt $f class V $.
	f8_opelopabt $f class W $.
	p_opelopabt $p |- ( ( A. x A. y ( x = A -> ( ph <-> ps ) ) /\ A. x A. y ( y = B -> ( ps <-> ch ) ) /\ ( A e. V /\ B e. W ) ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) ) $= f0_opelopabt f3_opelopabt f4_opelopabt f5_opelopabt f6_opelopabt a_cop p_elopab f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi f3_opelopabt f4_opelopabt p_19.26-2 f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb p_prth f0_opelopabt f1_opelopabt f2_opelopabt p_bitr f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi a_wa f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f4_opelopabt a_sup_set_class f6_opelopabt a_wceq a_wa f0_opelopabt f1_opelopabt a_wb f1_opelopabt f2_opelopabt a_wb a_wa f0_opelopabt f2_opelopabt a_wb p_syl6 f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi a_wa f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f4_opelopabt a_sup_set_class f6_opelopabt a_wceq a_wa f0_opelopabt f2_opelopabt a_wb a_wi f3_opelopabt f4_opelopabt p_2alimi f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal a_wa f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi a_wa f4_opelopabt a_wal f3_opelopabt a_wal f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f4_opelopabt a_sup_set_class f6_opelopabt a_wceq a_wa f0_opelopabt f2_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal p_sylbir f0_opelopabt f2_opelopabt f3_opelopabt f4_opelopabt f5_opelopabt f6_opelopabt f7_opelopabt f8_opelopabt p_copsex2t f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal a_wa f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f4_opelopabt a_sup_set_class f6_opelopabt a_wceq a_wa f0_opelopabt f2_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f5_opelopabt f7_opelopabt a_wcel f6_opelopabt f8_opelopabt a_wcel a_wa f5_opelopabt f6_opelopabt a_cop f3_opelopabt a_sup_set_class f4_opelopabt a_sup_set_class a_cop a_wceq f0_opelopabt a_wa f4_opelopabt a_wex f3_opelopabt a_wex f2_opelopabt a_wb p_sylan f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f5_opelopabt f7_opelopabt a_wcel f6_opelopabt f8_opelopabt a_wcel a_wa f5_opelopabt f6_opelopabt a_cop f3_opelopabt a_sup_set_class f4_opelopabt a_sup_set_class a_cop a_wceq f0_opelopabt a_wa f4_opelopabt a_wex f3_opelopabt a_wex f2_opelopabt a_wb p_3impa f5_opelopabt f6_opelopabt a_cop f0_opelopabt f3_opelopabt f4_opelopabt a_copab a_wcel f5_opelopabt f6_opelopabt a_cop f3_opelopabt a_sup_set_class f4_opelopabt a_sup_set_class a_cop a_wceq f0_opelopabt a_wa f4_opelopabt a_wex f3_opelopabt a_wex f3_opelopabt a_sup_set_class f5_opelopabt a_wceq f0_opelopabt f1_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f4_opelopabt a_sup_set_class f6_opelopabt a_wceq f1_opelopabt f2_opelopabt a_wb a_wi f4_opelopabt a_wal f3_opelopabt a_wal f5_opelopabt f7_opelopabt a_wcel f6_opelopabt f8_opelopabt a_wcel a_wa a_w3a f2_opelopabt p_syl5bb $.
$}

$(The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y A B V W  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_opelopabga $f wff ph $.
	f1_opelopabga $f wff ps $.
	f2_opelopabga $f set x $.
	f3_opelopabga $f set y $.
	f4_opelopabga $f class A $.
	f5_opelopabga $f class B $.
	f6_opelopabga $f class V $.
	f7_opelopabga $f class W $.
	e0_opelopabga $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_opelopabga $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) ) $= f0_opelopabga f2_opelopabga f3_opelopabga f4_opelopabga f5_opelopabga a_cop p_elopab e0_opelopabga f0_opelopabga f1_opelopabga f2_opelopabga f3_opelopabga f4_opelopabga f5_opelopabga f6_opelopabga f7_opelopabga p_copsex2g f4_opelopabga f5_opelopabga a_cop f0_opelopabga f2_opelopabga f3_opelopabga a_copab a_wcel f4_opelopabga f5_opelopabga a_cop f2_opelopabga a_sup_set_class f3_opelopabga a_sup_set_class a_cop a_wceq f0_opelopabga a_wa f3_opelopabga a_wex f2_opelopabga a_wex f4_opelopabga f6_opelopabga a_wcel f5_opelopabga f7_opelopabga a_wcel a_wa f1_opelopabga p_syl5bb $.
$}

$(The law of concretion for a binary relation.  (Contributed by Mario
         Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y A B R V W  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_brabga $f wff ph $.
	f1_brabga $f wff ps $.
	f2_brabga $f set x $.
	f3_brabga $f set y $.
	f4_brabga $f class A $.
	f5_brabga $f class B $.
	f6_brabga $f class R $.
	f7_brabga $f class V $.
	f8_brabga $f class W $.
	e0_brabga $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	e1_brabga $e |- R = { <. x , y >. | ph } $.
	p_brabga $p |- ( ( A e. V /\ B e. W ) -> ( A R B <-> ps ) ) $= f4_brabga f5_brabga f6_brabga a_df-br e1_brabga f6_brabga f0_brabga f2_brabga f3_brabga a_copab f4_brabga f5_brabga a_cop p_eleq2i f4_brabga f5_brabga f6_brabga a_wbr f4_brabga f5_brabga a_cop f6_brabga a_wcel f4_brabga f5_brabga a_cop f0_brabga f2_brabga f3_brabga a_copab a_wcel p_bitri e0_brabga f0_brabga f1_brabga f2_brabga f3_brabga f4_brabga f5_brabga f7_brabga f8_brabga p_opelopabga f4_brabga f5_brabga f6_brabga a_wbr f4_brabga f5_brabga a_cop f0_brabga f2_brabga f3_brabga a_copab a_wcel f4_brabga f7_brabga a_wcel f5_brabga f8_brabga a_wcel a_wa f1_brabga p_syl5bb $.
$}

$(Ordered pair membership in an ordered pair class abstraction.
       (Contributed by Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y A B C D  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	$d x y C  $.
	$d x y D  $.
	f0_opelopab2a $f wff ph $.
	f1_opelopab2a $f wff ps $.
	f2_opelopab2a $f set x $.
	f3_opelopab2a $f set y $.
	f4_opelopab2a $f class A $.
	f5_opelopab2a $f class B $.
	f6_opelopab2a $f class C $.
	f7_opelopab2a $f class D $.
	e0_opelopab2a $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_opelopab2a $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ps ) ) $= f2_opelopab2a a_sup_set_class f4_opelopab2a f6_opelopab2a p_eleq1 f3_opelopab2a a_sup_set_class f5_opelopab2a f7_opelopab2a p_eleq1 f2_opelopab2a a_sup_set_class f4_opelopab2a a_wceq f2_opelopab2a a_sup_set_class f6_opelopab2a a_wcel f4_opelopab2a f6_opelopab2a a_wcel f3_opelopab2a a_sup_set_class f5_opelopab2a a_wceq f3_opelopab2a a_sup_set_class f7_opelopab2a a_wcel f5_opelopab2a f7_opelopab2a a_wcel p_bi2anan9 e0_opelopab2a f2_opelopab2a a_sup_set_class f4_opelopab2a a_wceq f3_opelopab2a a_sup_set_class f5_opelopab2a a_wceq a_wa f2_opelopab2a a_sup_set_class f6_opelopab2a a_wcel f3_opelopab2a a_sup_set_class f7_opelopab2a a_wcel a_wa f4_opelopab2a f6_opelopab2a a_wcel f5_opelopab2a f7_opelopab2a a_wcel a_wa f0_opelopab2a f1_opelopab2a p_anbi12d f2_opelopab2a a_sup_set_class f6_opelopab2a a_wcel f3_opelopab2a a_sup_set_class f7_opelopab2a a_wcel a_wa f0_opelopab2a a_wa f4_opelopab2a f6_opelopab2a a_wcel f5_opelopab2a f7_opelopab2a a_wcel a_wa f1_opelopab2a a_wa f2_opelopab2a f3_opelopab2a f4_opelopab2a f5_opelopab2a f6_opelopab2a f7_opelopab2a p_opelopabga f4_opelopab2a f6_opelopab2a a_wcel f5_opelopab2a f7_opelopab2a a_wcel a_wa f4_opelopab2a f5_opelopab2a a_cop f2_opelopab2a a_sup_set_class f6_opelopab2a a_wcel f3_opelopab2a a_sup_set_class f7_opelopab2a a_wcel a_wa f0_opelopab2a a_wa f2_opelopab2a f3_opelopab2a a_copab a_wcel f1_opelopab2a p_bianabs $.
$}

$(The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_opelopaba $f wff ph $.
	f1_opelopaba $f wff ps $.
	f2_opelopaba $f set x $.
	f3_opelopaba $f set y $.
	f4_opelopaba $f class A $.
	f5_opelopaba $f class B $.
	e0_opelopaba $e |- A e. _V $.
	e1_opelopaba $e |- B e. _V $.
	e2_opelopaba $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_opelopaba $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) $= e0_opelopaba e1_opelopaba e2_opelopaba f0_opelopaba f1_opelopaba f2_opelopaba f3_opelopaba f4_opelopaba f5_opelopaba a_cvv a_cvv p_opelopabga f4_opelopaba a_cvv a_wcel f5_opelopaba a_cvv a_wcel f4_opelopaba f5_opelopaba a_cop f0_opelopaba f2_opelopaba f3_opelopaba a_copab a_wcel f1_opelopaba a_wb p_mp2an $.
$}

$(The law of concretion for a binary relation.  (Contributed by NM,
         19-Dec-2013.) $)

${
	$v ph ps x y A B R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ps  $.
	f0_braba $f wff ph $.
	f1_braba $f wff ps $.
	f2_braba $f set x $.
	f3_braba $f set y $.
	f4_braba $f class A $.
	f5_braba $f class B $.
	f6_braba $f class R $.
	e0_braba $e |- A e. _V $.
	e1_braba $e |- B e. _V $.
	e2_braba $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	e3_braba $e |- R = { <. x , y >. | ph } $.
	p_braba $p |- ( A R B <-> ps ) $= e0_braba e1_braba e2_braba e3_braba f0_braba f1_braba f2_braba f3_braba f4_braba f5_braba f6_braba a_cvv a_cvv p_brabga f4_braba a_cvv a_wcel f5_braba a_cvv a_wcel f4_braba f5_braba f6_braba a_wbr f1_braba a_wb p_mp2an $.
$}

$(The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       NM, 28-May-1995.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps ch x y A B V W  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ch  $.
	f0_opelopabg $f wff ph $.
	f1_opelopabg $f wff ps $.
	f2_opelopabg $f wff ch $.
	f3_opelopabg $f set x $.
	f4_opelopabg $f set y $.
	f5_opelopabg $f class A $.
	f6_opelopabg $f class B $.
	f7_opelopabg $f class V $.
	f8_opelopabg $f class W $.
	e0_opelopabg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_opelopabg $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_opelopabg $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) ) $= e0_opelopabg e1_opelopabg f3_opelopabg a_sup_set_class f5_opelopabg a_wceq f0_opelopabg f1_opelopabg f4_opelopabg a_sup_set_class f6_opelopabg a_wceq f2_opelopabg p_sylan9bb f0_opelopabg f2_opelopabg f3_opelopabg f4_opelopabg f5_opelopabg f6_opelopabg f7_opelopabg f8_opelopabg p_opelopabga $.
$}

$(The law of concretion for a binary relation.  (Contributed by NM,
         16-Aug-1999.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)

${
	$v ph ps ch x y A B C D R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ch  $.
	f0_brabg $f wff ph $.
	f1_brabg $f wff ps $.
	f2_brabg $f wff ch $.
	f3_brabg $f set x $.
	f4_brabg $f set y $.
	f5_brabg $f class A $.
	f6_brabg $f class B $.
	f7_brabg $f class C $.
	f8_brabg $f class D $.
	f9_brabg $f class R $.
	e0_brabg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_brabg $e |- ( y = B -> ( ps <-> ch ) ) $.
	e2_brabg $e |- R = { <. x , y >. | ph } $.
	p_brabg $p |- ( ( A e. C /\ B e. D ) -> ( A R B <-> ch ) ) $= e0_brabg e1_brabg f3_brabg a_sup_set_class f5_brabg a_wceq f0_brabg f1_brabg f4_brabg a_sup_set_class f6_brabg a_wceq f2_brabg p_sylan9bb e2_brabg f0_brabg f2_brabg f3_brabg f4_brabg f5_brabg f6_brabg f9_brabg f7_brabg f8_brabg p_brabga $.
$}

$(Ordered pair membership in an ordered pair class abstraction.
       (Contributed by NM, 14-Oct-2007.)  (Revised by Mario Carneiro,
       19-Dec-2013.) $)

${
	$v ph ps ch x y A B C D  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y D  $.
	$d x y ch  $.
	f0_opelopab2 $f wff ph $.
	f1_opelopab2 $f wff ps $.
	f2_opelopab2 $f wff ch $.
	f3_opelopab2 $f set x $.
	f4_opelopab2 $f set y $.
	f5_opelopab2 $f class A $.
	f6_opelopab2 $f class B $.
	f7_opelopab2 $f class C $.
	f8_opelopab2 $f class D $.
	e0_opelopab2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_opelopab2 $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_opelopab2 $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ch ) ) $= e0_opelopab2 e1_opelopab2 f3_opelopab2 a_sup_set_class f5_opelopab2 a_wceq f0_opelopab2 f1_opelopab2 f4_opelopab2 a_sup_set_class f6_opelopab2 a_wceq f2_opelopab2 p_sylan9bb f0_opelopab2 f2_opelopab2 f3_opelopab2 f4_opelopab2 f5_opelopab2 f6_opelopab2 f7_opelopab2 f8_opelopab2 p_opelopab2a $.
$}

$(The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       NM, 16-May-1995.) $)

${
	$v ph ps ch x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ch  $.
	f0_opelopab $f wff ph $.
	f1_opelopab $f wff ps $.
	f2_opelopab $f wff ch $.
	f3_opelopab $f set x $.
	f4_opelopab $f set y $.
	f5_opelopab $f class A $.
	f6_opelopab $f class B $.
	e0_opelopab $e |- A e. _V $.
	e1_opelopab $e |- B e. _V $.
	e2_opelopab $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_opelopab $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_opelopab $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) $= e0_opelopab e1_opelopab e2_opelopab e3_opelopab f0_opelopab f1_opelopab f2_opelopab f3_opelopab f4_opelopab f5_opelopab f6_opelopab a_cvv a_cvv p_opelopabg f5_opelopab a_cvv a_wcel f6_opelopab a_cvv a_wcel f5_opelopab f6_opelopab a_cop f0_opelopab f3_opelopab f4_opelopab a_copab a_wcel f2_opelopab a_wb p_mp2an $.
$}

$(The law of concretion for a binary relation.  (Contributed by NM,
         16-Aug-1999.) $)

${
	$v ph ps ch x y A B R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y ch  $.
	f0_brab $f wff ph $.
	f1_brab $f wff ps $.
	f2_brab $f wff ch $.
	f3_brab $f set x $.
	f4_brab $f set y $.
	f5_brab $f class A $.
	f6_brab $f class B $.
	f7_brab $f class R $.
	e0_brab $e |- A e. _V $.
	e1_brab $e |- B e. _V $.
	e2_brab $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_brab $e |- ( y = B -> ( ps <-> ch ) ) $.
	e4_brab $e |- R = { <. x , y >. | ph } $.
	p_brab $p |- ( A R B <-> ch ) $= e0_brab e1_brab e2_brab e3_brab e4_brab f0_brab f1_brab f2_brab f3_brab f4_brab f5_brab f6_brab a_cvv a_cvv f7_brab p_brabg f5_brab a_cvv a_wcel f6_brab a_cvv a_wcel f5_brab f6_brab f7_brab a_wbr f2_brab a_wb p_mp2an $.
$}

$(The law of concretion.  Theorem 9.5 of [Quine] p. 61.  This version of
       ~ opelopab uses bound-variable hypotheses in place of distinct variable
       conditions."  (Contributed by Mario Carneiro, 19-Dec-2013.)  (Proof
       shortened by Mario Carneiro, 18-Nov-2016.) $)

${
	$v ph ps x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d ph  $.
	$d ps  $.
	f0_opelopabaf $f wff ph $.
	f1_opelopabaf $f wff ps $.
	f2_opelopabaf $f set x $.
	f3_opelopabaf $f set y $.
	f4_opelopabaf $f class A $.
	f5_opelopabaf $f class B $.
	e0_opelopabaf $e |- F/ x ps $.
	e1_opelopabaf $e |- F/ y ps $.
	e2_opelopabaf $e |- A e. _V $.
	e3_opelopabaf $e |- B e. _V $.
	e4_opelopabaf $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	p_opelopabaf $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) $= f0_opelopabaf f2_opelopabaf f3_opelopabaf f4_opelopabaf f5_opelopabaf p_opelopabsb e2_opelopabaf e3_opelopabaf e0_opelopabaf e1_opelopabaf f5_opelopabaf a_cvv a_wcel f2_opelopabaf p_nfv e4_opelopabaf f0_opelopabaf f1_opelopabaf f2_opelopabaf f3_opelopabaf f4_opelopabaf f5_opelopabaf a_cvv a_cvv p_sbc2iegf f4_opelopabaf a_cvv a_wcel f5_opelopabaf a_cvv a_wcel f0_opelopabaf f3_opelopabaf f5_opelopabaf a_wsbc f2_opelopabaf f4_opelopabaf a_wsbc f1_opelopabaf a_wb p_mp2an f4_opelopabaf f5_opelopabaf a_cop f0_opelopabaf f2_opelopabaf f3_opelopabaf a_copab a_wcel f0_opelopabaf f3_opelopabaf f5_opelopabaf a_wsbc f2_opelopabaf f4_opelopabaf a_wsbc f1_opelopabaf p_bitri $.
$}

$(The law of concretion.  Theorem 9.5 of [Quine] p. 61.  This version of
       ~ opelopab uses bound-variable hypotheses in place of distinct variable
       conditions."  (Contributed by NM, 19-Dec-2008.) $)

${
	$v ph ps ch x y A B  $.
	$d x y A  $.
	$d x y B  $.
	$d ch  $.
	$d ph  $.
	f0_opelopabf $f wff ph $.
	f1_opelopabf $f wff ps $.
	f2_opelopabf $f wff ch $.
	f3_opelopabf $f set x $.
	f4_opelopabf $f set y $.
	f5_opelopabf $f class A $.
	f6_opelopabf $f class B $.
	e0_opelopabf $e |- F/ x ps $.
	e1_opelopabf $e |- F/ y ch $.
	e2_opelopabf $e |- A e. _V $.
	e3_opelopabf $e |- B e. _V $.
	e4_opelopabf $e |- ( x = A -> ( ph <-> ps ) ) $.
	e5_opelopabf $e |- ( y = B -> ( ps <-> ch ) ) $.
	p_opelopabf $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) $= f0_opelopabf f3_opelopabf f4_opelopabf f5_opelopabf f6_opelopabf p_opelopabsb e2_opelopabf f3_opelopabf f6_opelopabf p_nfcv e0_opelopabf f1_opelopabf f3_opelopabf f4_opelopabf f6_opelopabf p_nfsbc e4_opelopabf f3_opelopabf a_sup_set_class f5_opelopabf a_wceq f0_opelopabf f1_opelopabf f4_opelopabf f6_opelopabf p_sbcbidv f0_opelopabf f4_opelopabf f6_opelopabf a_wsbc f1_opelopabf f4_opelopabf f6_opelopabf a_wsbc f3_opelopabf f5_opelopabf a_cvv p_sbciegf f5_opelopabf a_cvv a_wcel f0_opelopabf f4_opelopabf f6_opelopabf a_wsbc f3_opelopabf f5_opelopabf a_wsbc f1_opelopabf f4_opelopabf f6_opelopabf a_wsbc a_wb a_ax-mp e3_opelopabf e1_opelopabf e5_opelopabf f1_opelopabf f2_opelopabf f4_opelopabf f6_opelopabf a_cvv p_sbciegf f6_opelopabf a_cvv a_wcel f1_opelopabf f4_opelopabf f6_opelopabf a_wsbc f2_opelopabf a_wb a_ax-mp f5_opelopabf f6_opelopabf a_cop f0_opelopabf f3_opelopabf f4_opelopabf a_copab a_wcel f0_opelopabf f4_opelopabf f6_opelopabf a_wsbc f3_opelopabf f5_opelopabf a_wsbc f1_opelopabf f4_opelopabf f6_opelopabf a_wsbc f2_opelopabf p_3bitri $.
$}

$(Equivalence of ordered pair abstraction subclass and implication.
       (Contributed by NM, 27-Dec-1996.)  (Revised by Mario Carneiro,
       19-May-2013.) $)

${
	$v ph ps x y  $.
	$d ph z  $.
	$d ps z  $.
	$d x z  $.
	$d y z  $.
	f0_ssopab2 $f wff ph $.
	f1_ssopab2 $f wff ps $.
	f2_ssopab2 $f set x $.
	f3_ssopab2 $f set y $.
	i0_ssopab2 $f set z $.
	p_ssopab2 $p |- ( A. x A. y ( ph -> ps ) -> { <. x , y >. | ph } C_ { <. x , y >. | ps } ) $= f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal f2_ssopab2 p_nfa1 f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 p_nfa1 f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 p_sp f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal f0_ssopab2 f1_ssopab2 i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq p_anim2d f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f0_ssopab2 a_wa i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f1_ssopab2 a_wa f3_ssopab2 p_eximd f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f0_ssopab2 a_wa f3_ssopab2 a_wex i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f1_ssopab2 a_wa f3_ssopab2 a_wex a_wi f2_ssopab2 p_sps f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal f2_ssopab2 a_wal i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f0_ssopab2 a_wa f3_ssopab2 a_wex i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f1_ssopab2 a_wa f3_ssopab2 a_wex f2_ssopab2 p_eximd f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal f2_ssopab2 a_wal i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f0_ssopab2 a_wa f3_ssopab2 a_wex f2_ssopab2 a_wex i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f1_ssopab2 a_wa f3_ssopab2 a_wex f2_ssopab2 a_wex i0_ssopab2 p_ss2abdv f0_ssopab2 f2_ssopab2 f3_ssopab2 i0_ssopab2 a_df-opab f1_ssopab2 f2_ssopab2 f3_ssopab2 i0_ssopab2 a_df-opab f0_ssopab2 f1_ssopab2 a_wi f3_ssopab2 a_wal f2_ssopab2 a_wal i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f0_ssopab2 a_wa f3_ssopab2 a_wex f2_ssopab2 a_wex i0_ssopab2 a_cab i0_ssopab2 a_sup_set_class f2_ssopab2 a_sup_set_class f3_ssopab2 a_sup_set_class a_cop a_wceq f1_ssopab2 a_wa f3_ssopab2 a_wex f2_ssopab2 a_wex i0_ssopab2 a_cab f0_ssopab2 f2_ssopab2 f3_ssopab2 a_copab f1_ssopab2 f2_ssopab2 f3_ssopab2 a_copab p_3sstr4g $.
$}

$(Equivalence of ordered pair abstraction subclass and implication.
       (Contributed by NM, 27-Dec-1996.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)

${
	$v ph ps x y  $.
	$d ph  $.
	$d ps  $.
	$d x  $.
	$d y  $.
	f0_ssopab2b $f wff ph $.
	f1_ssopab2b $f wff ps $.
	f2_ssopab2b $f set x $.
	f3_ssopab2b $f set y $.
	p_ssopab2b $p |- ( { <. x , y >. | ph } C_ { <. x , y >. | ps } <-> A. x A. y ( ph -> ps ) ) $= f0_ssopab2b f2_ssopab2b f3_ssopab2b p_nfopab1 f1_ssopab2b f2_ssopab2b f3_ssopab2b p_nfopab1 f2_ssopab2b f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab p_nfss f0_ssopab2b f2_ssopab2b f3_ssopab2b p_nfopab2 f1_ssopab2b f2_ssopab2b f3_ssopab2b p_nfopab2 f3_ssopab2b f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab p_nfss f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f2_ssopab2b a_sup_set_class f3_ssopab2b a_sup_set_class a_cop p_ssel f0_ssopab2b f2_ssopab2b f3_ssopab2b p_opabid f1_ssopab2b f2_ssopab2b f3_ssopab2b p_opabid f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab a_wss f2_ssopab2b a_sup_set_class f3_ssopab2b a_sup_set_class a_cop f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab a_wcel f2_ssopab2b a_sup_set_class f3_ssopab2b a_sup_set_class a_cop f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab a_wcel f0_ssopab2b f1_ssopab2b p_3imtr3g f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab a_wss f0_ssopab2b f1_ssopab2b a_wi f3_ssopab2b p_alrimi f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab a_wss f0_ssopab2b f1_ssopab2b a_wi f3_ssopab2b a_wal f2_ssopab2b p_alrimi f0_ssopab2b f1_ssopab2b f2_ssopab2b f3_ssopab2b p_ssopab2 f0_ssopab2b f2_ssopab2b f3_ssopab2b a_copab f1_ssopab2b f2_ssopab2b f3_ssopab2b a_copab a_wss f0_ssopab2b f1_ssopab2b a_wi f3_ssopab2b a_wal f2_ssopab2b a_wal p_impbii $.
$}

$(Inference of ordered pair abstraction subclass from implication.
       (Contributed by NM, 5-Apr-1995.) $)

${
	$v ph ps x y  $.
	f0_ssopab2i $f wff ph $.
	f1_ssopab2i $f wff ps $.
	f2_ssopab2i $f set x $.
	f3_ssopab2i $f set y $.
	e0_ssopab2i $e |- ( ph -> ps ) $.
	p_ssopab2i $p |- { <. x , y >. | ph } C_ { <. x , y >. | ps } $= f0_ssopab2i f1_ssopab2i f2_ssopab2i f3_ssopab2i p_ssopab2 e0_ssopab2i f0_ssopab2i f1_ssopab2i a_wi f3_ssopab2i a_ax-gen f0_ssopab2i f1_ssopab2i a_wi f3_ssopab2i a_wal f0_ssopab2i f2_ssopab2i f3_ssopab2i a_copab f1_ssopab2i f2_ssopab2i f3_ssopab2i a_copab a_wss f2_ssopab2i p_mpg $.
$}

$(Inference of ordered pair abstraction subclass from implication.
       (Contributed by NM, 19-Jan-2014.)  (Revised by Mario Carneiro,
       24-Jun-2014.) $)

${
	$v ph ps ch x y  $.
	$d x ph  $.
	$d y ph  $.
	f0_ssopab2dv $f wff ph $.
	f1_ssopab2dv $f wff ps $.
	f2_ssopab2dv $f wff ch $.
	f3_ssopab2dv $f set x $.
	f4_ssopab2dv $f set y $.
	e0_ssopab2dv $e |- ( ph -> ( ps -> ch ) ) $.
	p_ssopab2dv $p |- ( ph -> { <. x , y >. | ps } C_ { <. x , y >. | ch } ) $= e0_ssopab2dv f0_ssopab2dv f1_ssopab2dv f2_ssopab2dv a_wi f3_ssopab2dv f4_ssopab2dv p_alrimivv f1_ssopab2dv f2_ssopab2dv f3_ssopab2dv f4_ssopab2dv p_ssopab2 f0_ssopab2dv f1_ssopab2dv f2_ssopab2dv a_wi f4_ssopab2dv a_wal f3_ssopab2dv a_wal f1_ssopab2dv f3_ssopab2dv f4_ssopab2dv a_copab f2_ssopab2dv f3_ssopab2dv f4_ssopab2dv a_copab a_wss p_syl $.
$}

$(Equivalence of ordered pair abstraction equality and biconditional.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)

${
	$v ph ps x y  $.
	$d ph  $.
	$d ps  $.
	$d x  $.
	$d y  $.
	f0_eqopab2b $f wff ph $.
	f1_eqopab2b $f wff ps $.
	f2_eqopab2b $f set x $.
	f3_eqopab2b $f set y $.
	p_eqopab2b $p |- ( { <. x , y >. | ph } = { <. x , y >. | ps } <-> A. x A. y ( ph <-> ps ) ) $= f0_eqopab2b f1_eqopab2b f2_eqopab2b f3_eqopab2b p_ssopab2b f1_eqopab2b f0_eqopab2b f2_eqopab2b f3_eqopab2b p_ssopab2b f0_eqopab2b f2_eqopab2b f3_eqopab2b a_copab f1_eqopab2b f2_eqopab2b f3_eqopab2b a_copab a_wss f0_eqopab2b f1_eqopab2b a_wi f3_eqopab2b a_wal f2_eqopab2b a_wal f1_eqopab2b f2_eqopab2b f3_eqopab2b a_copab f0_eqopab2b f2_eqopab2b f3_eqopab2b a_copab a_wss f1_eqopab2b f0_eqopab2b a_wi f3_eqopab2b a_wal f2_eqopab2b a_wal p_anbi12i f0_eqopab2b f2_eqopab2b f3_eqopab2b a_copab f1_eqopab2b f2_eqopab2b f3_eqopab2b a_copab p_eqss f0_eqopab2b f1_eqopab2b f2_eqopab2b f3_eqopab2b p_2albiim f0_eqopab2b f2_eqopab2b f3_eqopab2b a_copab f1_eqopab2b f2_eqopab2b f3_eqopab2b a_copab a_wss f1_eqopab2b f2_eqopab2b f3_eqopab2b a_copab f0_eqopab2b f2_eqopab2b f3_eqopab2b a_copab a_wss a_wa f0_eqopab2b f1_eqopab2b a_wi f3_eqopab2b a_wal f2_eqopab2b a_wal f1_eqopab2b f0_eqopab2b a_wi f3_eqopab2b a_wal f2_eqopab2b a_wal a_wa f0_eqopab2b f2_eqopab2b f3_eqopab2b a_copab f1_eqopab2b f2_eqopab2b f3_eqopab2b a_copab a_wceq f0_eqopab2b f1_eqopab2b a_wb f3_eqopab2b a_wal f2_eqopab2b a_wal p_3bitr4i $.
$}

$(Non-empty ordered pair class abstraction.  (Contributed by NM,
       10-Oct-2007.) $)

${
	$v ph x y  $.
	$d z ph  $.
	$d z x  $.
	$d z y  $.
	f0_opabn0 $f wff ph $.
	f1_opabn0 $f set x $.
	f2_opabn0 $f set y $.
	i0_opabn0 $f set z $.
	p_opabn0 $p |- ( { <. x , y >. | ph } =/= (/) <-> E. x E. y ph ) $= i0_opabn0 f0_opabn0 f1_opabn0 f2_opabn0 a_copab p_n0 f0_opabn0 f1_opabn0 f2_opabn0 i0_opabn0 a_sup_set_class p_elopab i0_opabn0 a_sup_set_class f0_opabn0 f1_opabn0 f2_opabn0 a_copab a_wcel i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa f2_opabn0 a_wex f1_opabn0 a_wex i0_opabn0 p_exbii i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa i0_opabn0 f1_opabn0 f2_opabn0 p_exrot3 f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class p_opex i0_opabn0 f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop p_isseti i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 i0_opabn0 p_19.41v i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa i0_opabn0 a_wex i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq i0_opabn0 a_wex f0_opabn0 p_mpbiran i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa i0_opabn0 a_wex f0_opabn0 f1_opabn0 f2_opabn0 p_2exbii i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa f2_opabn0 a_wex f1_opabn0 a_wex i0_opabn0 a_wex i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa i0_opabn0 a_wex f2_opabn0 a_wex f1_opabn0 a_wex f0_opabn0 f2_opabn0 a_wex f1_opabn0 a_wex p_bitri i0_opabn0 a_sup_set_class f0_opabn0 f1_opabn0 f2_opabn0 a_copab a_wcel i0_opabn0 a_wex i0_opabn0 a_sup_set_class f1_opabn0 a_sup_set_class f2_opabn0 a_sup_set_class a_cop a_wceq f0_opabn0 a_wa f2_opabn0 a_wex f1_opabn0 a_wex i0_opabn0 a_wex f0_opabn0 f2_opabn0 a_wex f1_opabn0 a_wex p_bitri f0_opabn0 f1_opabn0 f2_opabn0 a_copab a_c0 a_wne i0_opabn0 a_sup_set_class f0_opabn0 f1_opabn0 f2_opabn0 a_copab a_wcel i0_opabn0 a_wex f0_opabn0 f2_opabn0 a_wex f1_opabn0 a_wex p_bitri $.
$}

$(Move indexed union inside an ordered-pair abstraction.  (Contributed by
       Stefan O'Rear, 20-Feb-2015.) $)

${
	$v ph x y z A  $.
	$d ph w  $.
	$d A w x  $.
	$d A y  $.
	$d w y z  $.
	$d x z  $.
	f0_iunopab $f wff ph $.
	f1_iunopab $f set x $.
	f2_iunopab $f set y $.
	f3_iunopab $f set z $.
	f4_iunopab $f class A $.
	i0_iunopab $f set w $.
	p_iunopab $p |- U_ z e. A { <. x , y >. | ph } = { <. x , y >. | E. z e. A ph } $= f0_iunopab f1_iunopab f2_iunopab i0_iunopab a_sup_set_class p_elopab i0_iunopab a_sup_set_class f0_iunopab f1_iunopab f2_iunopab a_copab a_wcel i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f1_iunopab a_wex f3_iunopab f4_iunopab p_rexbii i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f3_iunopab f1_iunopab f4_iunopab p_rexcom4 i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f3_iunopab f2_iunopab f4_iunopab p_rexcom4 i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab p_r19.42v i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab p_exbii i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f3_iunopab f4_iunopab a_wrex f2_iunopab a_wex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab a_wex p_bitri i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab a_wex f1_iunopab p_exbii i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f1_iunopab a_wex f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f3_iunopab f4_iunopab a_wrex f1_iunopab a_wex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab a_wex f1_iunopab a_wex p_bitri i0_iunopab a_sup_set_class f0_iunopab f1_iunopab f2_iunopab a_copab a_wcel f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab a_wa f2_iunopab a_wex f1_iunopab a_wex f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab a_wex f1_iunopab a_wex p_bitri i0_iunopab a_sup_set_class f0_iunopab f1_iunopab f2_iunopab a_copab a_wcel f3_iunopab f4_iunopab a_wrex i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab a_wex f1_iunopab a_wex i0_iunopab p_abbii f3_iunopab i0_iunopab f4_iunopab f0_iunopab f1_iunopab f2_iunopab a_copab a_df-iun f0_iunopab f3_iunopab f4_iunopab a_wrex f1_iunopab f2_iunopab i0_iunopab a_df-opab i0_iunopab a_sup_set_class f0_iunopab f1_iunopab f2_iunopab a_copab a_wcel f3_iunopab f4_iunopab a_wrex i0_iunopab a_cab i0_iunopab a_sup_set_class f1_iunopab a_sup_set_class f2_iunopab a_sup_set_class a_cop a_wceq f0_iunopab f3_iunopab f4_iunopab a_wrex a_wa f2_iunopab a_wex f1_iunopab a_wex i0_iunopab a_cab f3_iunopab f4_iunopab f0_iunopab f1_iunopab f2_iunopab a_copab a_ciun f0_iunopab f3_iunopab f4_iunopab a_wrex f1_iunopab f2_iunopab a_copab p_3eqtr4i $.
$}


