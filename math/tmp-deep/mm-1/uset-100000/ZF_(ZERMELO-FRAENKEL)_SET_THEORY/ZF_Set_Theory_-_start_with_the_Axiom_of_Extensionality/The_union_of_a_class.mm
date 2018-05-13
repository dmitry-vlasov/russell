$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Unordered_and_ordered_pairs.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       The union of a class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare class union symbol. $)

$c U. $.

$(Big cup $)

$(Extend class notation to include the union of a class (read:  'union
     ` A ` ') $)

${
	$v A  $.
	f0_cuni $f class A $.
	a_cuni $a class U. A $.
$}

$(Define the union of a class i.e. the collection of all members of the
       members of the class.  Definition 5.5 of [TakeutiZaring] p. 16.  For
       example, ` U. { { 1 , 3 } , { 1 , 8 } } = { 1 , 3 , 8 } ` ( ~ ex-uni ).
       This is similar to the union of two classes ~ df-un .  (Contributed by
       NM, 23-Aug-1993.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_df-uni $f set x $.
	f1_df-uni $f set y $.
	f2_df-uni $f class A $.
	a_df-uni $a |- U. A = { x | E. y ( x e. y /\ y e. A ) } $.
$}

$(Alternate definition of class union.  (Contributed by NM,
       28-Jun-1998.) $)

${
	$v x y A  $.
	$d x y A  $.
	f0_dfuni2 $f set x $.
	f1_dfuni2 $f set y $.
	f2_dfuni2 $f class A $.
	p_dfuni2 $p |- U. A = { x | E. y e. A x e. y } $= f0_dfuni2 f1_dfuni2 f2_dfuni2 a_df-uni f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 a_sup_set_class f2_dfuni2 a_wcel f1_dfuni2 p_exancom f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 f2_dfuni2 a_df-rex f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 a_sup_set_class f2_dfuni2 a_wcel a_wa f1_dfuni2 a_wex f1_dfuni2 a_sup_set_class f2_dfuni2 a_wcel f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel a_wa f1_dfuni2 a_wex f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 f2_dfuni2 a_wrex p_bitr4i f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 a_sup_set_class f2_dfuni2 a_wcel a_wa f1_dfuni2 a_wex f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 f2_dfuni2 a_wrex f0_dfuni2 p_abbii f2_dfuni2 a_cuni f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 a_sup_set_class f2_dfuni2 a_wcel a_wa f1_dfuni2 a_wex f0_dfuni2 a_cab f0_dfuni2 a_sup_set_class f1_dfuni2 a_sup_set_class a_wcel f1_dfuni2 f2_dfuni2 a_wrex f0_dfuni2 a_cab p_eqtri $.
$}

$(Membership in class union.  (Contributed by NM, 22-May-1994.) $)

${
	$v x A B  $.
	$d x A y  $.
	$d x B y  $.
	f0_eluni $f set x $.
	f1_eluni $f class A $.
	f2_eluni $f class B $.
	i0_eluni $f set y $.
	p_eluni $p |- ( A e. U. B <-> E. x ( A e. x /\ x e. B ) ) $= f1_eluni f2_eluni a_cuni p_elex f1_eluni f0_eluni a_sup_set_class p_elex f1_eluni f0_eluni a_sup_set_class a_wcel f1_eluni a_cvv a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel p_adantr f1_eluni f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel a_wa f1_eluni a_cvv a_wcel f0_eluni p_exlimiv i0_eluni a_sup_set_class f1_eluni f0_eluni a_sup_set_class p_eleq1 i0_eluni a_sup_set_class f1_eluni a_wceq i0_eluni a_sup_set_class f0_eluni a_sup_set_class a_wcel f1_eluni f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel p_anbi1d i0_eluni a_sup_set_class f1_eluni a_wceq i0_eluni a_sup_set_class f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel a_wa f1_eluni f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel a_wa f0_eluni p_exbidv i0_eluni f0_eluni f2_eluni a_df-uni i0_eluni a_sup_set_class f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel a_wa f0_eluni a_wex f1_eluni f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel a_wa f0_eluni a_wex i0_eluni f1_eluni f2_eluni a_cuni a_cvv p_elab2g f1_eluni f2_eluni a_cuni a_wcel f1_eluni a_cvv a_wcel f1_eluni f0_eluni a_sup_set_class a_wcel f0_eluni a_sup_set_class f2_eluni a_wcel a_wa f0_eluni a_wex p_pm5.21nii $.
$}

$(Membership in class union.  Restricted quantifier version.  (Contributed
       by NM, 31-Aug-1999.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_eluni2 $f set x $.
	f1_eluni2 $f class A $.
	f2_eluni2 $f class B $.
	p_eluni2 $p |- ( A e. U. B <-> E. x e. B A e. x ) $= f1_eluni2 f0_eluni2 a_sup_set_class a_wcel f0_eluni2 a_sup_set_class f2_eluni2 a_wcel f0_eluni2 p_exancom f0_eluni2 f1_eluni2 f2_eluni2 p_eluni f1_eluni2 f0_eluni2 a_sup_set_class a_wcel f0_eluni2 f2_eluni2 a_df-rex f1_eluni2 f0_eluni2 a_sup_set_class a_wcel f0_eluni2 a_sup_set_class f2_eluni2 a_wcel a_wa f0_eluni2 a_wex f0_eluni2 a_sup_set_class f2_eluni2 a_wcel f1_eluni2 f0_eluni2 a_sup_set_class a_wcel a_wa f0_eluni2 a_wex f1_eluni2 f2_eluni2 a_cuni a_wcel f1_eluni2 f0_eluni2 a_sup_set_class a_wcel f0_eluni2 f2_eluni2 a_wrex p_3bitr4i $.
$}

$(Membership in class union.  (Contributed by NM, 24-Mar-1995.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_elunii $f class A $.
	f1_elunii $f class B $.
	f2_elunii $f class C $.
	i0_elunii $f set x $.
	p_elunii $p |- ( ( A e. B /\ B e. C ) -> A e. U. C ) $= i0_elunii a_sup_set_class f1_elunii f0_elunii p_eleq2 i0_elunii a_sup_set_class f1_elunii f2_elunii p_eleq1 i0_elunii a_sup_set_class f1_elunii a_wceq f0_elunii i0_elunii a_sup_set_class a_wcel f0_elunii f1_elunii a_wcel i0_elunii a_sup_set_class f2_elunii a_wcel f1_elunii f2_elunii a_wcel p_anbi12d f0_elunii i0_elunii a_sup_set_class a_wcel i0_elunii a_sup_set_class f2_elunii a_wcel a_wa f0_elunii f1_elunii a_wcel f1_elunii f2_elunii a_wcel a_wa i0_elunii f1_elunii f2_elunii p_spcegv f0_elunii f1_elunii a_wcel f1_elunii f2_elunii a_wcel f0_elunii i0_elunii a_sup_set_class a_wcel i0_elunii a_sup_set_class f2_elunii a_wcel a_wa i0_elunii a_wex p_anabsi7 i0_elunii f0_elunii f2_elunii p_eluni f0_elunii f1_elunii a_wcel f1_elunii f2_elunii a_wcel a_wa f0_elunii i0_elunii a_sup_set_class a_wcel i0_elunii a_sup_set_class f2_elunii a_wcel a_wa i0_elunii a_wex f0_elunii f2_elunii a_cuni a_wcel p_sylibr $.
$}

$(Bound-variable hypothesis builder for union.  (Contributed by NM,
       30-Dec-1996.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)

${
	$v x A  $.
	$d y z A  $.
	$d x y z  $.
	f0_nfuni $f set x $.
	f1_nfuni $f class A $.
	i0_nfuni $f set y $.
	i1_nfuni $f set z $.
	e0_nfuni $e |- F/_ x A $.
	p_nfuni $p |- F/_ x U. A $= i0_nfuni i1_nfuni f1_nfuni p_dfuni2 e0_nfuni i0_nfuni a_sup_set_class i1_nfuni a_sup_set_class a_wcel f0_nfuni p_nfv i0_nfuni a_sup_set_class i1_nfuni a_sup_set_class a_wcel f0_nfuni i1_nfuni f1_nfuni p_nfrex i0_nfuni a_sup_set_class i1_nfuni a_sup_set_class a_wcel i1_nfuni f1_nfuni a_wrex f0_nfuni i0_nfuni p_nfab f0_nfuni f1_nfuni a_cuni i0_nfuni a_sup_set_class i1_nfuni a_sup_set_class a_wcel i1_nfuni f1_nfuni a_wrex i0_nfuni a_cab p_nfcxfr $.
$}

$(Deduction version of ~ nfuni .  (Contributed by NM, 18-Feb-2013.) $)

${
	$v ph x A  $.
	$d y z A  $.
	$d x y z  $.
	$d y z ph  $.
	f0_nfunid $f wff ph $.
	f1_nfunid $f set x $.
	f2_nfunid $f class A $.
	i0_nfunid $f set y $.
	i1_nfunid $f set z $.
	e0_nfunid $e |- ( ph -> F/_ x A ) $.
	p_nfunid $p |- ( ph -> F/_ x U. A ) $= i0_nfunid i1_nfunid f2_nfunid p_dfuni2 f0_nfunid i0_nfunid p_nfv f0_nfunid i1_nfunid p_nfv e0_nfunid f0_nfunid i0_nfunid a_sup_set_class i1_nfunid a_sup_set_class a_wcel f1_nfunid p_nfvd f0_nfunid i0_nfunid a_sup_set_class i1_nfunid a_sup_set_class a_wcel f1_nfunid i1_nfunid f2_nfunid p_nfrexd f0_nfunid i0_nfunid a_sup_set_class i1_nfunid a_sup_set_class a_wcel i1_nfunid f2_nfunid a_wrex f1_nfunid i0_nfunid p_nfabd f0_nfunid f1_nfunid f2_nfunid a_cuni i0_nfunid a_sup_set_class i1_nfunid a_sup_set_class a_wcel i1_nfunid f2_nfunid a_wrex i0_nfunid a_cab p_nfcxfrd $.
$}

$(Distribute proper substitution through the union of a class.
       (Contributed by Alan Sare, 10-Nov-2012.) $)

${
	$v x A B V  $.
	$d A y z  $.
	$d B y z  $.
	$d V y z  $.
	$d x y z  $.
	f0_csbunig $f set x $.
	f1_csbunig $f class A $.
	f2_csbunig $f class B $.
	f3_csbunig $f class V $.
	i0_csbunig $f set y $.
	i1_csbunig $f set z $.
	p_csbunig $p |- ( A e. V -> [_ A / x ]_ U. B = U. [_ A / x ]_ B ) $= i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex f0_csbunig i1_csbunig f1_csbunig f3_csbunig p_csbabg i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig f0_csbunig f1_csbunig f3_csbunig p_sbcexg i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel f0_csbunig f1_csbunig f3_csbunig p_sbcang i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel f0_csbunig f1_csbunig f3_csbunig p_sbcg f0_csbunig f1_csbunig i0_csbunig a_sup_set_class f2_csbunig f3_csbunig p_sbcel2g f1_csbunig f3_csbunig a_wcel i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel f0_csbunig f1_csbunig a_wsbc i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel f0_csbunig f1_csbunig a_wsbc i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel p_anbi12d f1_csbunig f3_csbunig a_wcel i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa f0_csbunig f1_csbunig a_wsbc i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel f0_csbunig f1_csbunig a_wsbc i0_csbunig a_sup_set_class f2_csbunig a_wcel f0_csbunig f1_csbunig a_wsbc a_wa i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel a_wa p_bitrd f1_csbunig f3_csbunig a_wcel i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa f0_csbunig f1_csbunig a_wsbc i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel a_wa i0_csbunig p_exbidv f1_csbunig f3_csbunig a_wcel i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex f0_csbunig f1_csbunig a_wsbc i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa f0_csbunig f1_csbunig a_wsbc i0_csbunig a_wex i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel a_wa i0_csbunig a_wex p_bitrd f1_csbunig f3_csbunig a_wcel i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex f0_csbunig f1_csbunig a_wsbc i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel a_wa i0_csbunig a_wex i1_csbunig p_abbidv f1_csbunig f3_csbunig a_wcel f0_csbunig f1_csbunig i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex i1_csbunig a_cab a_csb i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex f0_csbunig f1_csbunig a_wsbc i1_csbunig a_cab i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel a_wa i0_csbunig a_wex i1_csbunig a_cab p_eqtrd i1_csbunig i0_csbunig f2_csbunig a_df-uni f0_csbunig f1_csbunig f2_csbunig a_cuni i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex i1_csbunig a_cab p_csbeq2i i1_csbunig i0_csbunig f0_csbunig f1_csbunig f2_csbunig a_csb a_df-uni f1_csbunig f3_csbunig a_wcel f0_csbunig f1_csbunig i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f2_csbunig a_wcel a_wa i0_csbunig a_wex i1_csbunig a_cab a_csb i1_csbunig a_sup_set_class i0_csbunig a_sup_set_class a_wcel i0_csbunig a_sup_set_class f0_csbunig f1_csbunig f2_csbunig a_csb a_wcel a_wa i0_csbunig a_wex i1_csbunig a_cab f0_csbunig f1_csbunig f2_csbunig a_cuni a_csb f0_csbunig f1_csbunig f2_csbunig a_csb a_cuni p_3eqtr4g $.
$}

$(Equality theorem for class union.  Exercise 15 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 10-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 29-Jun-2011.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_unieq $f class A $.
	f1_unieq $f class B $.
	i0_unieq $f set x $.
	i1_unieq $f set y $.
	p_unieq $p |- ( A = B -> U. A = U. B ) $= i1_unieq a_sup_set_class i0_unieq a_sup_set_class a_wcel i0_unieq f0_unieq f1_unieq p_rexeq f0_unieq f1_unieq a_wceq i1_unieq a_sup_set_class i0_unieq a_sup_set_class a_wcel i0_unieq f0_unieq a_wrex i1_unieq a_sup_set_class i0_unieq a_sup_set_class a_wcel i0_unieq f1_unieq a_wrex i1_unieq p_abbidv i1_unieq i0_unieq f0_unieq p_dfuni2 i1_unieq i0_unieq f1_unieq p_dfuni2 f0_unieq f1_unieq a_wceq i1_unieq a_sup_set_class i0_unieq a_sup_set_class a_wcel i0_unieq f0_unieq a_wrex i1_unieq a_cab i1_unieq a_sup_set_class i0_unieq a_sup_set_class a_wcel i0_unieq f1_unieq a_wrex i1_unieq a_cab f0_unieq a_cuni f1_unieq a_cuni p_3eqtr4g $.
$}

$(Inference of equality of two class unions.  (Contributed by NM,
       30-Aug-1993.) $)

${
	$v A B  $.
	f0_unieqi $f class A $.
	f1_unieqi $f class B $.
	e0_unieqi $e |- A = B $.
	p_unieqi $p |- U. A = U. B $= e0_unieqi f0_unieqi f1_unieqi p_unieq f0_unieqi f1_unieqi a_wceq f0_unieqi a_cuni f1_unieqi a_cuni a_wceq a_ax-mp $.
$}

$(Deduction of equality of two class unions.  (Contributed by NM,
       21-Apr-1995.) $)

${
	$v ph A B  $.
	f0_unieqd $f wff ph $.
	f1_unieqd $f class A $.
	f2_unieqd $f class B $.
	e0_unieqd $e |- ( ph -> A = B ) $.
	p_unieqd $p |- ( ph -> U. A = U. B ) $= e0_unieqd f1_unieqd f2_unieqd p_unieq f0_unieqd f1_unieqd f2_unieqd a_wceq f1_unieqd a_cuni f2_unieqd a_cuni a_wceq p_syl $.
$}

$(Membership in union of a class abstraction.  (Contributed by NM,
       11-Aug-1994.)  (Revised by Mario Carneiro, 14-Nov-2016.) $)

${
	$v ph x A  $.
	$d x A y  $.
	$d ph y  $.
	f0_eluniab $f wff ph $.
	f1_eluniab $f set x $.
	f2_eluniab $f class A $.
	i0_eluniab $f set y $.
	p_eluniab $p |- ( A e. U. { x | ph } <-> E. x ( A e. x /\ ph ) ) $= i0_eluniab f2_eluniab f0_eluniab f1_eluniab a_cab p_eluni f2_eluniab i0_eluniab a_sup_set_class a_wcel f1_eluniab p_nfv f0_eluniab f1_eluniab i0_eluniab p_nfsab1 f2_eluniab i0_eluniab a_sup_set_class a_wcel i0_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab a_wcel f1_eluniab p_nfan f2_eluniab f1_eluniab a_sup_set_class a_wcel f0_eluniab a_wa i0_eluniab p_nfv i0_eluniab a_sup_set_class f1_eluniab a_sup_set_class f2_eluniab p_eleq2 i0_eluniab a_sup_set_class f1_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab p_eleq1 f0_eluniab f1_eluniab p_abid i0_eluniab a_sup_set_class f1_eluniab a_sup_set_class a_wceq i0_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab a_wcel f1_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab a_wcel f0_eluniab p_syl6bb i0_eluniab a_sup_set_class f1_eluniab a_sup_set_class a_wceq f2_eluniab i0_eluniab a_sup_set_class a_wcel f2_eluniab f1_eluniab a_sup_set_class a_wcel i0_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab a_wcel f0_eluniab p_anbi12d f2_eluniab i0_eluniab a_sup_set_class a_wcel i0_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab a_wcel a_wa f2_eluniab f1_eluniab a_sup_set_class a_wcel f0_eluniab a_wa i0_eluniab f1_eluniab p_cbvex f2_eluniab f0_eluniab f1_eluniab a_cab a_cuni a_wcel f2_eluniab i0_eluniab a_sup_set_class a_wcel i0_eluniab a_sup_set_class f0_eluniab f1_eluniab a_cab a_wcel a_wa i0_eluniab a_wex f2_eluniab f1_eluniab a_sup_set_class a_wcel f0_eluniab a_wa f1_eluniab a_wex p_bitri $.
$}

$(Membership in union of a class abstraction.  (Contributed by NM,
       4-Oct-2006.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d ph  $.
	f0_elunirab $f wff ph $.
	f1_elunirab $f set x $.
	f2_elunirab $f class A $.
	f3_elunirab $f class B $.
	p_elunirab $p |- ( A e. U. { x e. B | ph } <-> E. x e. B ( A e. x /\ ph ) ) $= f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa f1_elunirab f2_elunirab p_eluniab f0_elunirab f1_elunirab f3_elunirab a_df-rab f0_elunirab f1_elunirab f3_elunirab a_crab f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa f1_elunirab a_cab p_unieqi f0_elunirab f1_elunirab f3_elunirab a_crab a_cuni f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa f1_elunirab a_cab a_cuni f2_elunirab p_eleq2i f2_elunirab f1_elunirab a_sup_set_class a_wcel f0_elunirab a_wa f1_elunirab f3_elunirab a_df-rex f1_elunirab a_sup_set_class f3_elunirab a_wcel f2_elunirab f1_elunirab a_sup_set_class a_wcel f0_elunirab p_an12 f1_elunirab a_sup_set_class f3_elunirab a_wcel f2_elunirab f1_elunirab a_sup_set_class a_wcel f0_elunirab a_wa a_wa f2_elunirab f1_elunirab a_sup_set_class a_wcel f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa a_wa f1_elunirab p_exbii f2_elunirab f1_elunirab a_sup_set_class a_wcel f0_elunirab a_wa f1_elunirab f3_elunirab a_wrex f1_elunirab a_sup_set_class f3_elunirab a_wcel f2_elunirab f1_elunirab a_sup_set_class a_wcel f0_elunirab a_wa a_wa f1_elunirab a_wex f2_elunirab f1_elunirab a_sup_set_class a_wcel f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa a_wa f1_elunirab a_wex p_bitri f2_elunirab f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa f1_elunirab a_cab a_cuni a_wcel f2_elunirab f1_elunirab a_sup_set_class a_wcel f1_elunirab a_sup_set_class f3_elunirab a_wcel f0_elunirab a_wa a_wa f1_elunirab a_wex f2_elunirab f0_elunirab f1_elunirab f3_elunirab a_crab a_cuni a_wcel f2_elunirab f1_elunirab a_sup_set_class a_wcel f0_elunirab a_wa f1_elunirab f3_elunirab a_wrex p_3bitr4i $.
$}

$(The union of a pair is the union of its members.  Proposition 5.7 of
       [TakeutiZaring] p. 16.  (Contributed by NM, 23-Aug-1993.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_unipr $f class A $.
	f1_unipr $f class B $.
	i0_unipr $f set x $.
	i1_unipr $f set y $.
	e0_unipr $e |- A e. _V $.
	e1_unipr $e |- B e. _V $.
	p_unipr $p |- U. { A , B } = ( A u. B ) $= i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa i1_unipr p_19.43 i1_unipr p_vex i1_unipr a_sup_set_class f0_unipr f1_unipr p_elpr i1_unipr a_sup_set_class f0_unipr f1_unipr a_cpr a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq i1_unipr a_sup_set_class f1_unipr a_wceq a_wo i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel p_anbi2i i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq i1_unipr a_sup_set_class f1_unipr a_wceq p_andi i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr f1_unipr a_cpr a_wcel a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq i1_unipr a_sup_set_class f1_unipr a_wceq a_wo a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa a_wo p_bitri i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr f1_unipr a_cpr a_wcel a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa a_wo i1_unipr p_exbii e0_unipr i1_unipr i0_unipr a_sup_set_class f0_unipr p_clel3 i1_unipr a_sup_set_class f0_unipr a_wceq i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr p_exancom i0_unipr a_sup_set_class f0_unipr a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel a_wa i1_unipr a_wex i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i1_unipr a_wex p_bitri e1_unipr i1_unipr i0_unipr a_sup_set_class f1_unipr p_clel3 i1_unipr a_sup_set_class f1_unipr a_wceq i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr p_exancom i0_unipr a_sup_set_class f1_unipr a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel a_wa i1_unipr a_wex i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa i1_unipr a_wex p_bitri i0_unipr a_sup_set_class f0_unipr a_wcel i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i1_unipr a_wex i0_unipr a_sup_set_class f1_unipr a_wcel i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa i1_unipr a_wex p_orbi12i i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa a_wo i1_unipr a_wex i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr a_wceq a_wa i1_unipr a_wex i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f1_unipr a_wceq a_wa i1_unipr a_wex a_wo i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr f1_unipr a_cpr a_wcel a_wa i1_unipr a_wex i0_unipr a_sup_set_class f0_unipr a_wcel i0_unipr a_sup_set_class f1_unipr a_wcel a_wo p_3bitr4ri i0_unipr a_sup_set_class f0_unipr a_wcel i0_unipr a_sup_set_class f1_unipr a_wcel a_wo i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr f1_unipr a_cpr a_wcel a_wa i1_unipr a_wex i0_unipr p_abbii i0_unipr f0_unipr f1_unipr a_df-un i0_unipr i1_unipr f0_unipr f1_unipr a_cpr a_df-uni i0_unipr a_sup_set_class f0_unipr a_wcel i0_unipr a_sup_set_class f1_unipr a_wcel a_wo i0_unipr a_cab i0_unipr a_sup_set_class i1_unipr a_sup_set_class a_wcel i1_unipr a_sup_set_class f0_unipr f1_unipr a_cpr a_wcel a_wa i1_unipr a_wex i0_unipr a_cab f0_unipr f1_unipr a_cun f0_unipr f1_unipr a_cpr a_cuni p_3eqtr4ri $.
$}

$(The union of a pair is the union of its members.  Proposition 5.7 of
       [TakeutiZaring] p. 16.  (Contributed by NM, 25-Aug-2006.) $)

${
	$v A B V W  $.
	$d x y A  $.
	$d y B  $.
	f0_uniprg $f class A $.
	f1_uniprg $f class B $.
	f2_uniprg $f class V $.
	f3_uniprg $f class W $.
	i0_uniprg $f set x $.
	i1_uniprg $f set y $.
	p_uniprg $p |- ( ( A e. V /\ B e. W ) -> U. { A , B } = ( A u. B ) ) $= i0_uniprg a_sup_set_class f0_uniprg i1_uniprg a_sup_set_class p_preq1 i0_uniprg a_sup_set_class f0_uniprg a_wceq i0_uniprg a_sup_set_class i1_uniprg a_sup_set_class a_cpr f0_uniprg i1_uniprg a_sup_set_class a_cpr p_unieqd i0_uniprg a_sup_set_class f0_uniprg i1_uniprg a_sup_set_class p_uneq1 i0_uniprg a_sup_set_class f0_uniprg a_wceq i0_uniprg a_sup_set_class i1_uniprg a_sup_set_class a_cpr a_cuni f0_uniprg i1_uniprg a_sup_set_class a_cpr a_cuni i0_uniprg a_sup_set_class i1_uniprg a_sup_set_class a_cun f0_uniprg i1_uniprg a_sup_set_class a_cun p_eqeq12d i1_uniprg a_sup_set_class f1_uniprg f0_uniprg p_preq2 i1_uniprg a_sup_set_class f1_uniprg a_wceq f0_uniprg i1_uniprg a_sup_set_class a_cpr f0_uniprg f1_uniprg a_cpr p_unieqd i1_uniprg a_sup_set_class f1_uniprg f0_uniprg p_uneq2 i1_uniprg a_sup_set_class f1_uniprg a_wceq f0_uniprg i1_uniprg a_sup_set_class a_cpr a_cuni f0_uniprg f1_uniprg a_cpr a_cuni f0_uniprg i1_uniprg a_sup_set_class a_cun f0_uniprg f1_uniprg a_cun p_eqeq12d i0_uniprg p_vex i1_uniprg p_vex i0_uniprg a_sup_set_class i1_uniprg a_sup_set_class p_unipr i0_uniprg a_sup_set_class i1_uniprg a_sup_set_class a_cpr a_cuni i0_uniprg a_sup_set_class i1_uniprg a_sup_set_class a_cun a_wceq f0_uniprg i1_uniprg a_sup_set_class a_cpr a_cuni f0_uniprg i1_uniprg a_sup_set_class a_cun a_wceq f0_uniprg f1_uniprg a_cpr a_cuni f0_uniprg f1_uniprg a_cun a_wceq i0_uniprg i1_uniprg f0_uniprg f1_uniprg f2_uniprg f3_uniprg p_vtocl2g $.
$}

$(A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       (Contributed by NM, 30-Aug-1993.) $)

${
	$v A  $.
	f0_unisn $f class A $.
	e0_unisn $e |- A e. _V $.
	p_unisn $p |- U. { A } = A $= f0_unisn p_dfsn2 f0_unisn a_csn f0_unisn f0_unisn a_cpr p_unieqi e0_unisn e0_unisn f0_unisn f0_unisn p_unipr f0_unisn p_unidm f0_unisn a_csn a_cuni f0_unisn f0_unisn a_cpr a_cuni f0_unisn f0_unisn a_cun f0_unisn p_3eqtri $.
$}

$(A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       (Contributed by NM, 13-Aug-2002.) $)

${
	$v A V  $.
	$d x A  $.
	f0_unisng $f class A $.
	f1_unisng $f class V $.
	i0_unisng $f set x $.
	p_unisng $p |- ( A e. V -> U. { A } = A ) $= i0_unisng a_sup_set_class f0_unisng p_sneq i0_unisng a_sup_set_class f0_unisng a_wceq i0_unisng a_sup_set_class a_csn f0_unisng a_csn p_unieqd i0_unisng a_sup_set_class f0_unisng a_wceq p_id i0_unisng a_sup_set_class f0_unisng a_wceq i0_unisng a_sup_set_class a_csn a_cuni f0_unisng a_csn a_cuni i0_unisng a_sup_set_class f0_unisng p_eqeq12d i0_unisng p_vex i0_unisng a_sup_set_class p_unisn i0_unisng a_sup_set_class a_csn a_cuni i0_unisng a_sup_set_class a_wceq f0_unisng a_csn a_cuni f0_unisng a_wceq i0_unisng f0_unisng f1_unisng p_vtoclg $.
$}

$(An alternative statement of the effective freeness of a class ` A ` ,
       when it is a set.  (Contributed by Mario Carneiro, 14-Oct-2016.) $)

${
	$v x y A V  $.
	$d x y  $.
	$d y A  $.
	f0_dfnfc2 $f set x $.
	f1_dfnfc2 $f set y $.
	f2_dfnfc2 $f class A $.
	f3_dfnfc2 $f class V $.
	p_dfnfc2 $p |- ( A. x A e. V -> ( F/_ x A <-> A. y F/ x y = A ) ) $= f0_dfnfc2 f2_dfnfc2 a_wnfc f0_dfnfc2 f1_dfnfc2 a_sup_set_class p_nfcvd f0_dfnfc2 f2_dfnfc2 a_wnfc p_id f0_dfnfc2 f2_dfnfc2 a_wnfc f0_dfnfc2 f1_dfnfc2 a_sup_set_class f2_dfnfc2 p_nfeqd f0_dfnfc2 f2_dfnfc2 a_wnfc f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 p_alrimiv f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal p_simpr f0_dfnfc2 f1_dfnfc2 f2_dfnfc2 a_csn a_df-nfc f1_dfnfc2 f2_dfnfc2 p_elsn f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_csn a_wcel f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 p_nfbii f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_csn a_wcel f0_dfnfc2 a_wnf f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 p_albii f0_dfnfc2 f2_dfnfc2 a_csn a_wnfc f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_csn a_wcel f0_dfnfc2 a_wnf f1_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal p_bitri f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal a_wa f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal f0_dfnfc2 f2_dfnfc2 a_csn a_wnfc p_sylibr f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal a_wa f0_dfnfc2 f2_dfnfc2 a_csn p_nfunid f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 p_nfa1 f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 p_nfnf1 f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f0_dfnfc2 f1_dfnfc2 p_nfal f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal f0_dfnfc2 p_nfan f2_dfnfc2 f3_dfnfc2 p_unisng f2_dfnfc2 f3_dfnfc2 a_wcel f2_dfnfc2 a_csn a_cuni f2_dfnfc2 a_wceq f0_dfnfc2 p_sps f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f2_dfnfc2 a_csn a_cuni f2_dfnfc2 a_wceq f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal p_adantr f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal a_wa f0_dfnfc2 f2_dfnfc2 a_csn a_cuni f2_dfnfc2 p_nfceqdf f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal a_wa f0_dfnfc2 f2_dfnfc2 a_csn a_cuni a_wnfc f0_dfnfc2 f2_dfnfc2 a_wnfc p_mpbid f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal f0_dfnfc2 f2_dfnfc2 a_wnfc p_ex f2_dfnfc2 f3_dfnfc2 a_wcel f0_dfnfc2 a_wal f0_dfnfc2 f2_dfnfc2 a_wnfc f1_dfnfc2 a_sup_set_class f2_dfnfc2 a_wceq f0_dfnfc2 a_wnf f1_dfnfc2 a_wal p_impbid2 $.
$}

$(The class union of the union of two classes.  Theorem 8.3 of [Quine]
       p. 53.  (Contributed by NM, 20-Aug-1993.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_uniun $f class A $.
	f1_uniun $f class B $.
	i0_uniun $f set x $.
	i1_uniun $f set y $.
	p_uniun $p |- U. ( A u. B ) = ( U. A u. U. B ) $= i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wa i1_uniun p_19.43 i1_uniun a_sup_set_class f0_uniun f1_uniun p_elun i1_uniun a_sup_set_class f0_uniun f1_uniun a_cun a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wo i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel p_anbi2i i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel p_andi i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun f1_uniun a_cun a_wcel a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wo a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wa a_wo p_bitri i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun f1_uniun a_cun a_wcel a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wa a_wo i1_uniun p_exbii i1_uniun i0_uniun a_sup_set_class f0_uniun p_eluni i1_uniun i0_uniun a_sup_set_class f1_uniun p_eluni i0_uniun a_sup_set_class f0_uniun a_cuni a_wcel i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel a_wa i1_uniun a_wex i0_uniun a_sup_set_class f1_uniun a_cuni a_wcel i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wa i1_uniun a_wex p_orbi12i i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel a_wa i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wa a_wo i1_uniun a_wex i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun a_wcel a_wa i1_uniun a_wex i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f1_uniun a_wcel a_wa i1_uniun a_wex a_wo i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun f1_uniun a_cun a_wcel a_wa i1_uniun a_wex i0_uniun a_sup_set_class f0_uniun a_cuni a_wcel i0_uniun a_sup_set_class f1_uniun a_cuni a_wcel a_wo p_3bitr4i i1_uniun i0_uniun a_sup_set_class f0_uniun f1_uniun a_cun p_eluni i0_uniun a_sup_set_class f0_uniun a_cuni f1_uniun a_cuni p_elun i0_uniun a_sup_set_class i1_uniun a_sup_set_class a_wcel i1_uniun a_sup_set_class f0_uniun f1_uniun a_cun a_wcel a_wa i1_uniun a_wex i0_uniun a_sup_set_class f0_uniun a_cuni a_wcel i0_uniun a_sup_set_class f1_uniun a_cuni a_wcel a_wo i0_uniun a_sup_set_class f0_uniun f1_uniun a_cun a_cuni a_wcel i0_uniun a_sup_set_class f0_uniun a_cuni f1_uniun a_cuni a_cun a_wcel p_3bitr4i i0_uniun f0_uniun f1_uniun a_cun a_cuni f0_uniun a_cuni f1_uniun a_cuni a_cun p_eqriv $.
$}

$(The class union of the intersection of two classes.  Exercise 4.12(n) of
       [Mendelson] p. 235.  See ~ uninqs for a condition where equality holds.
       (Contributed by NM, 4-Dec-2003.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_uniin $f class A $.
	f1_uniin $f class B $.
	i0_uniin $f set x $.
	i1_uniin $f set y $.
	p_uniin $p |- U. ( A i^i B ) C_ ( U. A i^i U. B ) $= i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa i1_uniin p_19.40 i1_uniin a_sup_set_class f0_uniin f1_uniin p_elin i1_uniin a_sup_set_class f0_uniin f1_uniin a_cin a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel p_anbi2i i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel p_anandi i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin f1_uniin a_cin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa a_wa p_bitri i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin f1_uniin a_cin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa a_wa i1_uniin p_exbii i1_uniin i0_uniin a_sup_set_class f0_uniin p_eluni i1_uniin i0_uniin a_sup_set_class f1_uniin p_eluni i0_uniin a_sup_set_class f0_uniin a_cuni a_wcel i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel a_wa i1_uniin a_wex i0_uniin a_sup_set_class f1_uniin a_cuni a_wcel i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa i1_uniin a_wex p_anbi12i i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa a_wa i1_uniin a_wex i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin a_wcel a_wa i1_uniin a_wex i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f1_uniin a_wcel a_wa i1_uniin a_wex a_wa i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin f1_uniin a_cin a_wcel a_wa i1_uniin a_wex i0_uniin a_sup_set_class f0_uniin a_cuni a_wcel i0_uniin a_sup_set_class f1_uniin a_cuni a_wcel a_wa p_3imtr4i i1_uniin i0_uniin a_sup_set_class f0_uniin f1_uniin a_cin p_eluni i0_uniin a_sup_set_class f0_uniin a_cuni f1_uniin a_cuni p_elin i0_uniin a_sup_set_class i1_uniin a_sup_set_class a_wcel i1_uniin a_sup_set_class f0_uniin f1_uniin a_cin a_wcel a_wa i1_uniin a_wex i0_uniin a_sup_set_class f0_uniin a_cuni a_wcel i0_uniin a_sup_set_class f1_uniin a_cuni a_wcel a_wa i0_uniin a_sup_set_class f0_uniin f1_uniin a_cin a_cuni a_wcel i0_uniin a_sup_set_class f0_uniin a_cuni f1_uniin a_cuni a_cin a_wcel p_3imtr4i i0_uniin f0_uniin f1_uniin a_cin a_cuni f0_uniin a_cuni f1_uniin a_cuni a_cin p_ssriv $.
$}

$(Subclass relationship for class union.  Theorem 61 of [Suppes] p. 39.
       (Contributed by NM, 22-Mar-1998.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v A B  $.
	$d x y A  $.
	$d x y B  $.
	$d x y  $.
	f0_uniss $f class A $.
	f1_uniss $f class B $.
	i0_uniss $f set x $.
	i1_uniss $f set y $.
	p_uniss $p |- ( A C_ B -> U. A C_ U. B ) $= f0_uniss f1_uniss i1_uniss a_sup_set_class p_ssel f0_uniss f1_uniss a_wss i1_uniss a_sup_set_class f0_uniss a_wcel i1_uniss a_sup_set_class f1_uniss a_wcel i0_uniss a_sup_set_class i1_uniss a_sup_set_class a_wcel p_anim2d f0_uniss f1_uniss a_wss i0_uniss a_sup_set_class i1_uniss a_sup_set_class a_wcel i1_uniss a_sup_set_class f0_uniss a_wcel a_wa i0_uniss a_sup_set_class i1_uniss a_sup_set_class a_wcel i1_uniss a_sup_set_class f1_uniss a_wcel a_wa i1_uniss p_eximdv i1_uniss i0_uniss a_sup_set_class f0_uniss p_eluni i1_uniss i0_uniss a_sup_set_class f1_uniss p_eluni f0_uniss f1_uniss a_wss i0_uniss a_sup_set_class i1_uniss a_sup_set_class a_wcel i1_uniss a_sup_set_class f0_uniss a_wcel a_wa i1_uniss a_wex i0_uniss a_sup_set_class i1_uniss a_sup_set_class a_wcel i1_uniss a_sup_set_class f1_uniss a_wcel a_wa i1_uniss a_wex i0_uniss a_sup_set_class f0_uniss a_cuni a_wcel i0_uniss a_sup_set_class f1_uniss a_cuni a_wcel p_3imtr4g f0_uniss f1_uniss a_wss i0_uniss f0_uniss a_cuni f1_uniss a_cuni p_ssrdv $.
$}

$(Subclass relationship for class union.  (Contributed by NM,
       24-May-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	f0_ssuni $f class A $.
	f1_ssuni $f class B $.
	f2_ssuni $f class C $.
	i0_ssuni $f set x $.
	i1_ssuni $f set y $.
	p_ssuni $p |- ( ( A C_ B /\ B e. C ) -> A C_ U. C ) $= i0_ssuni a_sup_set_class f1_ssuni i1_ssuni a_sup_set_class p_eleq2 i0_ssuni a_sup_set_class f1_ssuni a_wceq i1_ssuni a_sup_set_class i0_ssuni a_sup_set_class a_wcel i1_ssuni a_sup_set_class f1_ssuni a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel p_imbi1d i1_ssuni a_sup_set_class i0_ssuni a_sup_set_class f2_ssuni p_elunii i1_ssuni a_sup_set_class i0_ssuni a_sup_set_class a_wcel i0_ssuni a_sup_set_class f2_ssuni a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel p_expcom i1_ssuni a_sup_set_class i0_ssuni a_sup_set_class a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel a_wi i1_ssuni a_sup_set_class f1_ssuni a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel a_wi i0_ssuni f1_ssuni f2_ssuni p_vtoclga f1_ssuni f2_ssuni a_wcel i1_ssuni a_sup_set_class f1_ssuni a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel i1_ssuni a_sup_set_class f0_ssuni a_wcel p_imim2d f1_ssuni f2_ssuni a_wcel i1_ssuni a_sup_set_class f0_ssuni a_wcel i1_ssuni a_sup_set_class f1_ssuni a_wcel a_wi i1_ssuni a_sup_set_class f0_ssuni a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel a_wi i1_ssuni p_alimdv i1_ssuni f0_ssuni f1_ssuni p_dfss2 i1_ssuni f0_ssuni f2_ssuni a_cuni p_dfss2 f1_ssuni f2_ssuni a_wcel i1_ssuni a_sup_set_class f0_ssuni a_wcel i1_ssuni a_sup_set_class f1_ssuni a_wcel a_wi i1_ssuni a_wal i1_ssuni a_sup_set_class f0_ssuni a_wcel i1_ssuni a_sup_set_class f2_ssuni a_cuni a_wcel a_wi i1_ssuni a_wal f0_ssuni f1_ssuni a_wss f0_ssuni f2_ssuni a_cuni a_wss p_3imtr4g f1_ssuni f2_ssuni a_wcel f0_ssuni f1_ssuni a_wss f0_ssuni f2_ssuni a_cuni a_wss p_impcom $.
$}

$(Subclass relationship for subclass union.  Inference form of ~ uniss .
       (Contributed by David Moews, 1-May-2017.) $)

${
	$v A B  $.
	f0_unissi $f class A $.
	f1_unissi $f class B $.
	e0_unissi $e |- A C_ B $.
	p_unissi $p |- U. A C_ U. B $= e0_unissi f0_unissi f1_unissi p_uniss f0_unissi f1_unissi a_wss f0_unissi a_cuni f1_unissi a_cuni a_wss a_ax-mp $.
$}

$(Subclass relationship for subclass union.  Deduction form of ~ uniss .
       (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B  $.
	f0_unissd $f wff ph $.
	f1_unissd $f class A $.
	f2_unissd $f class B $.
	e0_unissd $e |- ( ph -> A C_ B ) $.
	p_unissd $p |- ( ph -> U. A C_ U. B ) $= e0_unissd f1_unissd f2_unissd p_uniss f0_unissd f1_unissd f2_unissd a_wss f1_unissd a_cuni f2_unissd a_cuni a_wss p_syl $.
$}

$(The union of a set is empty iff the set is included in the singleton of
       the empty set.  (Contributed by NM, 12-Sep-2004.) $)

${
	$v A  $.
	$d x y A  $.
	f0_uni0b $f class A $.
	i0_uni0b $f set x $.
	i1_uni0b $f set y $.
	p_uni0b $p |- ( U. A = (/) <-> A C_ { (/) } ) $= i0_uni0b a_c0 p_elsn i0_uni0b a_sup_set_class a_c0 a_csn a_wcel i0_uni0b a_sup_set_class a_c0 a_wceq i0_uni0b f0_uni0b p_ralbii i0_uni0b f0_uni0b a_c0 a_csn p_dfss3 i1_uni0b f0_uni0b a_cuni p_neq0 i1_uni0b a_sup_set_class i0_uni0b a_sup_set_class a_wcel i0_uni0b i1_uni0b f0_uni0b p_rexcom4 i1_uni0b i0_uni0b a_sup_set_class p_neq0 i0_uni0b a_sup_set_class a_c0 a_wceq a_wn i1_uni0b a_sup_set_class i0_uni0b a_sup_set_class a_wcel i1_uni0b a_wex i0_uni0b f0_uni0b p_rexbii i0_uni0b i1_uni0b a_sup_set_class f0_uni0b p_eluni2 i1_uni0b a_sup_set_class f0_uni0b a_cuni a_wcel i1_uni0b a_sup_set_class i0_uni0b a_sup_set_class a_wcel i0_uni0b f0_uni0b a_wrex i1_uni0b p_exbii i1_uni0b a_sup_set_class i0_uni0b a_sup_set_class a_wcel i1_uni0b a_wex i0_uni0b f0_uni0b a_wrex i1_uni0b a_sup_set_class i0_uni0b a_sup_set_class a_wcel i0_uni0b f0_uni0b a_wrex i1_uni0b a_wex i0_uni0b a_sup_set_class a_c0 a_wceq a_wn i0_uni0b f0_uni0b a_wrex i1_uni0b a_sup_set_class f0_uni0b a_cuni a_wcel i1_uni0b a_wex p_3bitr4ri i0_uni0b a_sup_set_class a_c0 a_wceq i0_uni0b f0_uni0b p_rexnal f0_uni0b a_cuni a_c0 a_wceq a_wn i1_uni0b a_sup_set_class f0_uni0b a_cuni a_wcel i1_uni0b a_wex i0_uni0b a_sup_set_class a_c0 a_wceq a_wn i0_uni0b f0_uni0b a_wrex i0_uni0b a_sup_set_class a_c0 a_wceq i0_uni0b f0_uni0b a_wral a_wn p_3bitri f0_uni0b a_cuni a_c0 a_wceq i0_uni0b a_sup_set_class a_c0 a_wceq i0_uni0b f0_uni0b a_wral p_con4bii i0_uni0b a_sup_set_class a_c0 a_csn a_wcel i0_uni0b f0_uni0b a_wral i0_uni0b a_sup_set_class a_c0 a_wceq i0_uni0b f0_uni0b a_wral f0_uni0b a_c0 a_csn a_wss f0_uni0b a_cuni a_c0 a_wceq p_3bitr4ri $.
$}

$(The union of a set is empty iff all of its members are empty.
       (Contributed by NM, 16-Aug-2006.) $)

${
	$v x A  $.
	$d x A  $.
	f0_uni0c $f set x $.
	f1_uni0c $f class A $.
	p_uni0c $p |- ( U. A = (/) <-> A. x e. A x = (/) ) $= f1_uni0c p_uni0b f0_uni0c f1_uni0c a_c0 a_csn p_dfss3 f0_uni0c a_c0 p_elsn f0_uni0c a_sup_set_class a_c0 a_csn a_wcel f0_uni0c a_sup_set_class a_c0 a_wceq f0_uni0c f1_uni0c p_ralbii f1_uni0c a_cuni a_c0 a_wceq f1_uni0c a_c0 a_csn a_wss f0_uni0c a_sup_set_class a_c0 a_csn a_wcel f0_uni0c f1_uni0c a_wral f0_uni0c a_sup_set_class a_c0 a_wceq f0_uni0c f1_uni0c a_wral p_3bitri $.
$}

$(The union of the empty set is the empty set.  Theorem 8.7 of [Quine]
     p. 54.  (Reproved without relying on ~ ax-nul by Eric Schmidt.)
     (Contributed by NM, 16-Sep-1993.)  (Revised by Eric Schmidt,
     4-Apr-2007.) $)

${
	$v  $.
	p_uni0 $p |- U. (/) = (/) $= a_c0 a_csn p_0ss a_c0 p_uni0b a_c0 a_cuni a_c0 a_wceq a_c0 a_c0 a_csn a_wss p_mpbir $.
$}

$(An element of a class is a subclass of its union.  Theorem 8.6 of [Quine]
     p. 54.  Also the basis for Proposition 7.20 of [TakeutiZaring] p. 40.
     (Contributed by NM, 6-Jun-1994.) $)

${
	$v A B  $.
	f0_elssuni $f class A $.
	f1_elssuni $f class B $.
	p_elssuni $p |- ( A e. B -> A C_ U. B ) $= f0_elssuni p_ssid f0_elssuni f0_elssuni f1_elssuni p_ssuni f0_elssuni f0_elssuni a_wss f0_elssuni f1_elssuni a_wcel f0_elssuni f1_elssuni a_cuni a_wss p_mpan $.
$}

$(Condition turning a subclass relationship for union into an equality.
     (Contributed by NM, 18-Jul-2006.) $)

${
	$v A B  $.
	f0_unissel $f class A $.
	f1_unissel $f class B $.
	p_unissel $p |- ( ( U. A C_ B /\ B e. A ) -> U. A = B ) $= f0_unissel a_cuni f1_unissel a_wss f1_unissel f0_unissel a_wcel p_simpl f1_unissel f0_unissel p_elssuni f1_unissel f0_unissel a_wcel f1_unissel f0_unissel a_cuni a_wss f0_unissel a_cuni f1_unissel a_wss p_adantl f0_unissel a_cuni f1_unissel a_wss f1_unissel f0_unissel a_wcel a_wa f0_unissel a_cuni f1_unissel p_eqssd $.
$}

$(Relationship involving membership, subset, and union.  Exercise 5 of
       [Enderton] p. 26 and its converse.  (Contributed by NM, 20-Sep-2003.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_unissb $f set x $.
	f1_unissb $f class A $.
	f2_unissb $f class B $.
	i0_unissb $f set y $.
	p_unissb $p |- ( U. A C_ B <-> A. x e. A x C_ B ) $= f0_unissb i0_unissb a_sup_set_class f1_unissb p_eluni i0_unissb a_sup_set_class f1_unissb a_cuni a_wcel i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa f0_unissb a_wex i0_unissb a_sup_set_class f2_unissb a_wcel p_imbi1i i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel f0_unissb p_19.23v i0_unissb a_sup_set_class f1_unissb a_cuni a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa f0_unissb a_wex i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi f0_unissb a_wal p_bitr4i i0_unissb a_sup_set_class f1_unissb a_cuni a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi f0_unissb a_wal i0_unissb p_albii i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb f0_unissb p_alcom f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb p_19.21v i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel p_impexp i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel p_bi2.04 i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi a_wi f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi a_wi p_bitri i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi a_wi i0_unissb p_albii i0_unissb f0_unissb a_sup_set_class f2_unissb p_dfss2 f0_unissb a_sup_set_class f2_unissb a_wss i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel p_imbi2i f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi a_wi i0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal a_wi i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel f0_unissb a_sup_set_class f2_unissb a_wss a_wi p_3bitr4i i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel f0_unissb a_sup_set_class f2_unissb a_wss a_wi f0_unissb p_albii i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi f0_unissb a_wal i0_unissb a_wal i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal f0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel f0_unissb a_sup_set_class f2_unissb a_wss a_wi f0_unissb a_wal p_bitri i0_unissb a_sup_set_class f1_unissb a_cuni a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal i0_unissb a_sup_set_class f0_unissb a_sup_set_class a_wcel f0_unissb a_sup_set_class f1_unissb a_wcel a_wa i0_unissb a_sup_set_class f2_unissb a_wcel a_wi f0_unissb a_wal i0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel f0_unissb a_sup_set_class f2_unissb a_wss a_wi f0_unissb a_wal p_bitri i0_unissb f1_unissb a_cuni f2_unissb p_dfss2 f0_unissb a_sup_set_class f2_unissb a_wss f0_unissb f1_unissb a_df-ral i0_unissb a_sup_set_class f1_unissb a_cuni a_wcel i0_unissb a_sup_set_class f2_unissb a_wcel a_wi i0_unissb a_wal f0_unissb a_sup_set_class f1_unissb a_wcel f0_unissb a_sup_set_class f2_unissb a_wss a_wi f0_unissb a_wal f1_unissb a_cuni f2_unissb a_wss f0_unissb a_sup_set_class f2_unissb a_wss f0_unissb f1_unissb a_wral p_3bitr4i $.
$}

$(A subclass condition on the members of two classes that implies a
       subclass relation on their unions.  Proposition 8.6 of [TakeutiZaring]
       p. 59.  See ~ iunss2 for a generalization to indexed unions.
       (Contributed by NM, 22-Mar-2004.) $)

${
	$v x y A B  $.
	$d x A  $.
	$d x y B  $.
	f0_uniss2 $f set x $.
	f1_uniss2 $f set y $.
	f2_uniss2 $f class A $.
	f3_uniss2 $f class B $.
	p_uniss2 $p |- ( A. x e. A E. y e. B x C_ y -> U. A C_ U. B ) $= f0_uniss2 a_sup_set_class f1_uniss2 a_sup_set_class f3_uniss2 p_ssuni f0_uniss2 a_sup_set_class f1_uniss2 a_sup_set_class a_wss f1_uniss2 a_sup_set_class f3_uniss2 a_wcel f0_uniss2 a_sup_set_class f3_uniss2 a_cuni a_wss p_expcom f0_uniss2 a_sup_set_class f1_uniss2 a_sup_set_class a_wss f0_uniss2 a_sup_set_class f3_uniss2 a_cuni a_wss f1_uniss2 f3_uniss2 p_rexlimiv f0_uniss2 a_sup_set_class f1_uniss2 a_sup_set_class a_wss f1_uniss2 f3_uniss2 a_wrex f0_uniss2 a_sup_set_class f3_uniss2 a_cuni a_wss f0_uniss2 f2_uniss2 p_ralimi f0_uniss2 f2_uniss2 f3_uniss2 a_cuni p_unissb f0_uniss2 a_sup_set_class f1_uniss2 a_sup_set_class a_wss f1_uniss2 f3_uniss2 a_wrex f0_uniss2 f2_uniss2 a_wral f0_uniss2 a_sup_set_class f3_uniss2 a_cuni a_wss f0_uniss2 f2_uniss2 a_wral f2_uniss2 a_cuni f3_uniss2 a_cuni a_wss p_sylibr $.
$}

$(If the difference ` A \ B ` contains the largest members of ` A ` , then
       the union of the difference is the union of ` A ` .  (Contributed by NM,
       22-Mar-2004.) $)

${
	$v x y A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_unidif $f set x $.
	f1_unidif $f set y $.
	f2_unidif $f class A $.
	f3_unidif $f class B $.
	p_unidif $p |- ( A. x e. A E. y e. ( A \ B ) x C_ y -> U. ( A \ B ) = U. A ) $= f0_unidif f1_unidif f2_unidif f2_unidif f3_unidif a_cdif p_uniss2 f2_unidif f3_unidif p_difss f2_unidif f3_unidif a_cdif f2_unidif p_uniss f2_unidif f3_unidif a_cdif f2_unidif a_wss f2_unidif f3_unidif a_cdif a_cuni f2_unidif a_cuni a_wss a_ax-mp f0_unidif a_sup_set_class f1_unidif a_sup_set_class a_wss f1_unidif f2_unidif f3_unidif a_cdif a_wrex f0_unidif f2_unidif a_wral f2_unidif a_cuni f2_unidif f3_unidif a_cdif a_cuni a_wss f2_unidif f3_unidif a_cdif a_cuni f2_unidif a_cuni a_wss p_jctil f2_unidif f3_unidif a_cdif a_cuni f2_unidif a_cuni p_eqss f0_unidif a_sup_set_class f1_unidif a_sup_set_class a_wss f1_unidif f2_unidif f3_unidif a_cdif a_wrex f0_unidif f2_unidif a_wral f2_unidif f3_unidif a_cdif a_cuni f2_unidif a_cuni a_wss f2_unidif a_cuni f2_unidif f3_unidif a_cdif a_cuni a_wss a_wa f2_unidif f3_unidif a_cdif a_cuni f2_unidif a_cuni a_wceq p_sylibr $.
$}

$(Relationship implying union.  (Contributed by NM, 10-Nov-1999.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssunieq $f set x $.
	f1_ssunieq $f class A $.
	f2_ssunieq $f class B $.
	p_ssunieq $p |- ( ( A e. B /\ A. x e. B x C_ A ) -> A = U. B ) $= f1_ssunieq f2_ssunieq p_elssuni f0_ssunieq f2_ssunieq f1_ssunieq p_unissb f2_ssunieq a_cuni f1_ssunieq a_wss f0_ssunieq a_sup_set_class f1_ssunieq a_wss f0_ssunieq f2_ssunieq a_wral p_biimpri f1_ssunieq f2_ssunieq a_wcel f1_ssunieq f2_ssunieq a_cuni a_wss f0_ssunieq a_sup_set_class f1_ssunieq a_wss f0_ssunieq f2_ssunieq a_wral f2_ssunieq a_cuni f1_ssunieq a_wss p_anim12i f1_ssunieq f2_ssunieq a_cuni p_eqss f1_ssunieq f2_ssunieq a_wcel f0_ssunieq a_sup_set_class f1_ssunieq a_wss f0_ssunieq f2_ssunieq a_wral a_wa f1_ssunieq f2_ssunieq a_cuni a_wss f2_ssunieq a_cuni f1_ssunieq a_wss a_wa f1_ssunieq f2_ssunieq a_cuni a_wceq p_sylibr $.
$}

$(Any member of a class is the largest of those members that it includes.
       (Contributed by NM, 13-Aug-2002.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_unimax $f set x $.
	f1_unimax $f class A $.
	f2_unimax $f class B $.
	i0_unimax $f set y $.
	p_unimax $p |- ( A e. B -> U. { x e. B | x C_ A } = A ) $= f1_unimax p_ssid f0_unimax a_sup_set_class f1_unimax f1_unimax p_sseq1 f0_unimax a_sup_set_class f1_unimax a_wss f1_unimax f1_unimax a_wss f0_unimax f1_unimax f2_unimax p_elrab3 f1_unimax f2_unimax a_wcel f1_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_wcel f1_unimax f1_unimax a_wss p_mpbiri f0_unimax a_sup_set_class i0_unimax a_sup_set_class f1_unimax p_sseq1 f0_unimax a_sup_set_class f1_unimax a_wss i0_unimax a_sup_set_class f1_unimax a_wss f0_unimax i0_unimax a_sup_set_class f2_unimax p_elrab i0_unimax a_sup_set_class f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_wcel i0_unimax a_sup_set_class f2_unimax a_wcel i0_unimax a_sup_set_class f1_unimax a_wss p_simprbi i0_unimax a_sup_set_class f1_unimax a_wss i0_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab p_rgen i0_unimax f1_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab p_ssunieq f1_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_wcel i0_unimax a_sup_set_class f1_unimax a_wss i0_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_wral a_wa f1_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_cuni p_eqcomd f1_unimax f2_unimax a_wcel f1_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_wcel i0_unimax a_sup_set_class f1_unimax a_wss i0_unimax f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_wral f0_unimax a_sup_set_class f1_unimax a_wss f0_unimax f2_unimax a_crab a_cuni f1_unimax a_wceq p_sylancl $.
$}


