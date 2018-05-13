$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Theorems_requiring_subset_and_intersection_existence.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Theorems requiring empty set existence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Construct, from any class ` A ` , a set equal to it when the class
       exists and equal to the empty set when the class is proper.  This
       theorem shows that the constructed set always exists.  (Contributed by
       NM, 16-Oct-2003.) $)

${
	$v x A  $.
	$d x A  $.
	f0_class2set $f set x $.
	f1_class2set $f class A $.
	p_class2set $p |- { x e. A | A e. _V } e. _V $= f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_cvv p_rabexg f1_class2set a_cvv a_wcel a_wn f0_class2set a_sup_set_class f1_class2set a_wcel p_simpl f1_class2set a_cvv a_wcel a_wn f1_class2set a_cvv a_wcel f0_class2set f1_class2set p_nrexdv f1_class2set a_cvv a_wcel f0_class2set f1_class2set p_rabn0 f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_wrex f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_crab a_c0 p_necon1bbii f1_class2set a_cvv a_wcel a_wn f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_wrex a_wn f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_crab a_c0 a_wceq p_sylib p_0ex f1_class2set a_cvv a_wcel a_wn f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_crab a_c0 a_cvv p_syl6eqel f1_class2set a_cvv a_wcel f1_class2set a_cvv a_wcel f0_class2set f1_class2set a_crab a_cvv a_wcel p_pm2.61i $.
$}

$(Equality theorem based on ~ class2set .  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Raph Levien, 30-Jun-2006.) $)

${
	$v x A V  $.
	$d x A  $.
	f0_class2seteq $f set x $.
	f1_class2seteq $f class A $.
	f2_class2seteq $f class V $.
	p_class2seteq $p |- ( A e. V -> { x e. A | A e. _V } = A ) $= f1_class2seteq f2_class2seteq p_elex f1_class2seteq a_cvv a_wcel f0_class2seteq a_sup_set_class f1_class2seteq a_wcel a_ax-1 f1_class2seteq a_cvv a_wcel f1_class2seteq a_cvv a_wcel f0_class2seteq f1_class2seteq p_ralrimiv f1_class2seteq a_cvv a_wcel f0_class2seteq f1_class2seteq p_rabid2 f1_class2seteq a_cvv a_wcel f1_class2seteq a_cvv a_wcel f0_class2seteq f1_class2seteq a_wral f1_class2seteq f1_class2seteq a_cvv a_wcel f0_class2seteq f1_class2seteq a_crab a_wceq p_sylibr f1_class2seteq a_cvv a_wcel f1_class2seteq f1_class2seteq a_cvv a_wcel f0_class2seteq f1_class2seteq a_crab p_eqcomd f1_class2seteq f2_class2seteq a_wcel f1_class2seteq a_cvv a_wcel f1_class2seteq a_cvv a_wcel f0_class2seteq f1_class2seteq a_crab f1_class2seteq a_wceq p_syl $.
$}

$(Every power class contains the empty set.  (Contributed by NM,
     25-Oct-2007.) $)

${
	$v A  $.
	f0_0elpw $f class A $.
	p_0elpw $p |- (/) e. ~P A $= f0_0elpw p_0ss p_0ex a_c0 f0_0elpw p_elpw a_c0 f0_0elpw a_cpw a_wcel a_c0 f0_0elpw a_wss p_mpbir $.
$}

$(The empty set and its power set are not equal.  (Contributed by NM,
     23-Dec-1993.) $)

${
	$v  $.
	p_0nep0 $p |- (/) =/= { (/) } $= p_0ex a_c0 p_snnz a_c0 a_csn a_c0 p_necomi $.
$}

$(Something cannot be equal to both the null set and the power set of the
     null set.  (Contributed by NM, 30-Sep-2003.) $)

${
	$v A  $.
	f0_0inp0 $f class A $.
	p_0inp0 $p |- ( A = (/) -> -. A = { (/) } ) $= p_0nep0 f0_0inp0 a_c0 a_c0 a_csn p_neeq1 f0_0inp0 a_c0 a_wceq f0_0inp0 a_c0 a_csn a_wne a_c0 a_c0 a_csn a_wne p_mpbiri f0_0inp0 a_c0 a_wceq f0_0inp0 a_c0 a_csn p_neneqd $.
$}

$(The removal of the empty set from a class does not affect its union.
     (Contributed by NM, 22-Mar-2004.) $)

${
	$v A  $.
	f0_unidif0 $f class A $.
	p_unidif0 $p |- U. ( A \ { (/) } ) = U. A $= f0_unidif0 a_c0 a_csn a_cdif a_c0 a_csn p_uniun f0_unidif0 a_c0 a_csn p_undif1 f0_unidif0 a_c0 a_csn p_uncom f0_unidif0 a_c0 a_csn a_cdif a_c0 a_csn a_cun f0_unidif0 a_c0 a_csn a_cun a_c0 a_csn f0_unidif0 a_cun p_eqtr2i a_c0 a_csn f0_unidif0 a_cun f0_unidif0 a_c0 a_csn a_cdif a_c0 a_csn a_cun p_unieqi p_0ex a_c0 p_unisn a_c0 a_csn a_cuni a_c0 f0_unidif0 a_c0 a_csn a_cdif a_cuni p_uneq2i f0_unidif0 a_c0 a_csn a_cdif a_cuni p_un0 f0_unidif0 a_c0 a_csn a_cdif a_cuni a_c0 a_csn a_cuni a_cun f0_unidif0 a_c0 a_csn a_cdif a_cuni a_c0 a_cun f0_unidif0 a_c0 a_csn a_cdif a_cuni p_eqtr2i f0_unidif0 a_c0 a_csn a_cdif a_c0 a_csn a_cun a_cuni f0_unidif0 a_c0 a_csn a_cdif a_cuni a_c0 a_csn a_cuni a_cun a_c0 a_csn f0_unidif0 a_cun a_cuni f0_unidif0 a_c0 a_csn a_cdif a_cuni p_3eqtr4ri a_c0 a_csn f0_unidif0 p_uniun p_0ex a_c0 p_unisn a_c0 a_csn a_cuni a_c0 f0_unidif0 a_cuni p_uneq1i f0_unidif0 a_c0 a_csn a_cdif a_cuni a_c0 a_csn f0_unidif0 a_cun a_cuni a_c0 a_csn a_cuni f0_unidif0 a_cuni a_cun a_c0 f0_unidif0 a_cuni a_cun p_3eqtri a_c0 f0_unidif0 a_cuni p_uncom f0_unidif0 a_cuni p_un0 f0_unidif0 a_c0 a_csn a_cdif a_cuni a_c0 f0_unidif0 a_cuni a_cun f0_unidif0 a_cuni a_c0 a_cun f0_unidif0 a_cuni p_3eqtri $.
$}

$(An indexed intersection of the empty set, with a non-empty index set, is
       empty.  (Contributed by NM, 20-Oct-2005.) $)

${
	$v x A  $.
	$d x A  $.
	f0_iin0 $f set x $.
	f1_iin0 $f class A $.
	p_iin0 $p |- ( A =/= (/) <-> |^|_ x e. A (/) = (/) ) $= f0_iin0 f1_iin0 a_c0 p_iinconst p_0ex a_cvv a_c0 p_n0i a_c0 a_cvv a_wcel a_cvv a_c0 a_wceq a_wn a_ax-mp f0_iin0 a_c0 p_0iin f0_iin0 a_c0 a_c0 a_ciin a_cvv a_c0 p_eqeq1i f0_iin0 a_c0 a_c0 a_ciin a_c0 a_wceq a_cvv a_c0 a_wceq p_mtbir f0_iin0 f1_iin0 a_c0 a_c0 p_iineq1 f1_iin0 a_c0 a_wceq f0_iin0 f1_iin0 a_c0 a_ciin f0_iin0 a_c0 a_c0 a_ciin a_c0 p_eqeq1d f1_iin0 a_c0 a_wceq f0_iin0 f1_iin0 a_c0 a_ciin a_c0 a_wceq f0_iin0 a_c0 a_c0 a_ciin a_c0 a_wceq p_mtbiri f0_iin0 f1_iin0 a_c0 a_ciin a_c0 a_wceq f1_iin0 a_c0 p_necon2ai f1_iin0 a_c0 a_wne f0_iin0 f1_iin0 a_c0 a_ciin a_c0 a_wceq p_impbii $.
$}

$(In the Separation Scheme ~ zfauscl , we require that ` y ` not occur in
       ` ph ` (which can be generalized to "not be free in").  Here we show
       special cases of ` A ` and ` ph ` that result in a contradiction by
       violating this requirement.  (Contributed by NM, 8-Feb-2006.) $)

${
	$v ph x y A  $.
	$d x A  $.
	f0_notzfaus $f wff ph $.
	f1_notzfaus $f set x $.
	f2_notzfaus $f set y $.
	f3_notzfaus $f class A $.
	e0_notzfaus $e |- A = { (/) } $.
	e1_notzfaus $e |- ( ph <-> -. x e. y ) $.
	p_notzfaus $p |- -. E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) $= e0_notzfaus p_0ex a_c0 p_snnz f3_notzfaus a_c0 a_csn a_c0 p_eqnetri f1_notzfaus f3_notzfaus p_n0 f3_notzfaus a_c0 a_wne f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_wex p_mpbi f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel p_biimt f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel p_iman e1_notzfaus f0_notzfaus f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel a_wn f1_notzfaus a_sup_set_class f3_notzfaus a_wcel p_anbi2i f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel a_wi f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel a_wn a_wa f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa p_xchbinxr f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel a_wi f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wn p_syl6bb f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa p_xor3 f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wn a_wb f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb a_wn p_sylibr f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb a_wn f1_notzfaus p_eximi f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f1_notzfaus a_wex f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb a_wn f1_notzfaus a_wex a_ax-mp f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb f1_notzfaus p_exnal f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb a_wn f1_notzfaus a_wex f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb f1_notzfaus a_wal a_wn p_mpbi f1_notzfaus a_sup_set_class f2_notzfaus a_sup_set_class a_wcel f1_notzfaus a_sup_set_class f3_notzfaus a_wcel f0_notzfaus a_wa a_wb f1_notzfaus a_wal f2_notzfaus p_nex $.
$}

$(The intersection of the universal class is empty.  (Contributed by NM,
     11-Sep-2008.) $)

${
	$v  $.
	p_intv $p |- |^| _V = (/) $= p_0ex a_cvv p_int0el a_c0 a_cvv a_wcel a_cvv a_cint a_c0 a_wceq a_ax-mp $.
$}

$(Two equivalent ways to express the Power Set Axiom.  Note that ~ ax-pow
       is not used by the proof.  (Contributed by NM, 22-Jun-2009.) $)

${
	$v x y z A  $.
	$d x y z A  $.
	f0_axpweq $f set x $.
	f1_axpweq $f set y $.
	f2_axpweq $f set z $.
	f3_axpweq $f class A $.
	e0_axpweq $e |- A e. _V $.
	p_axpweq $p |- ( ~P A e. _V <-> E. x A. y ( A. z ( z e. y -> z e. A ) -> y e. x ) ) $= f3_axpweq a_cpw a_cvv p_pwidg f0_axpweq a_sup_set_class f3_axpweq a_cpw p_pweq f0_axpweq a_sup_set_class f3_axpweq a_cpw a_wceq f0_axpweq a_sup_set_class a_cpw f3_axpweq a_cpw a_cpw f3_axpweq a_cpw p_eleq2d f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f3_axpweq a_cpw f3_axpweq a_cpw a_cpw a_wcel f0_axpweq f3_axpweq a_cpw a_cvv p_spcegv f3_axpweq a_cpw a_cvv a_wcel f3_axpweq a_cpw f3_axpweq a_cpw a_cpw a_wcel f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f0_axpweq a_wex p_mpd f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw p_elex f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f3_axpweq a_cpw a_cvv a_wcel f0_axpweq p_exlimiv f3_axpweq a_cpw a_cvv a_wcel f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f0_axpweq a_wex p_impbii f0_axpweq p_vex f3_axpweq a_cpw f0_axpweq a_sup_set_class p_elpw2 f1_axpweq f3_axpweq f0_axpweq a_sup_set_class p_pwss f2_axpweq f1_axpweq a_sup_set_class f3_axpweq p_dfss2 f1_axpweq a_sup_set_class f3_axpweq a_wss f2_axpweq a_sup_set_class f1_axpweq a_sup_set_class a_wcel f2_axpweq a_sup_set_class f3_axpweq a_wcel a_wi f2_axpweq a_wal f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel p_imbi1i f1_axpweq a_sup_set_class f3_axpweq a_wss f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f2_axpweq a_sup_set_class f1_axpweq a_sup_set_class a_wcel f2_axpweq a_sup_set_class f3_axpweq a_wcel a_wi f2_axpweq a_wal f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f1_axpweq p_albii f3_axpweq a_cpw f0_axpweq a_sup_set_class a_wss f1_axpweq a_sup_set_class f3_axpweq a_wss f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f1_axpweq a_wal f2_axpweq a_sup_set_class f1_axpweq a_sup_set_class a_wcel f2_axpweq a_sup_set_class f3_axpweq a_wcel a_wi f2_axpweq a_wal f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f1_axpweq a_wal p_bitri f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f3_axpweq a_cpw f0_axpweq a_sup_set_class a_wss f2_axpweq a_sup_set_class f1_axpweq a_sup_set_class a_wcel f2_axpweq a_sup_set_class f3_axpweq a_wcel a_wi f2_axpweq a_wal f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f1_axpweq a_wal p_bitri f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f2_axpweq a_sup_set_class f1_axpweq a_sup_set_class a_wcel f2_axpweq a_sup_set_class f3_axpweq a_wcel a_wi f2_axpweq a_wal f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f1_axpweq a_wal f0_axpweq p_exbii f3_axpweq a_cpw a_cvv a_wcel f3_axpweq a_cpw f0_axpweq a_sup_set_class a_cpw a_wcel f0_axpweq a_wex f2_axpweq a_sup_set_class f1_axpweq a_sup_set_class a_wcel f2_axpweq a_sup_set_class f3_axpweq a_wcel a_wi f2_axpweq a_wal f1_axpweq a_sup_set_class f0_axpweq a_sup_set_class a_wcel a_wi f1_axpweq a_wal f0_axpweq a_wex p_bitri $.
$}


