$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/_Weak_deduction_theorem__for_set_theory.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Power classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare the symbol for power class. $)

$c ~P $.

$(Calligraphic P $)

$(Extend class notation to include power class.  (The tilde in the Metamath
     token is meant to suggest the calligraphic font of the P.) $)

${
	$v A  $.
	f0_cpw $f class A $.
	a_cpw $a class ~P A $.
$}

$(Soundness justification theorem for ~ df-pw .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v x y A  $.
	$d x A  $.
	$d y A  $.
	$d x  $.
	$d y  $.
	$d A  $.
	$d z  $.
	$d z x  $.
	$d z y  $.
	$d z A  $.
	f0_pwjust $f set x $.
	f1_pwjust $f set y $.
	f2_pwjust $f class A $.
	i0_pwjust $f set z $.
	p_pwjust $p |- { x | x C_ A } = { y | y C_ A } $= f0_pwjust a_sup_set_class i0_pwjust a_sup_set_class f2_pwjust p_sseq1 f0_pwjust a_sup_set_class f2_pwjust a_wss i0_pwjust a_sup_set_class f2_pwjust a_wss f0_pwjust i0_pwjust p_cbvabv i0_pwjust a_sup_set_class f1_pwjust a_sup_set_class f2_pwjust p_sseq1 i0_pwjust a_sup_set_class f2_pwjust a_wss f1_pwjust a_sup_set_class f2_pwjust a_wss i0_pwjust f1_pwjust p_cbvabv f0_pwjust a_sup_set_class f2_pwjust a_wss f0_pwjust a_cab i0_pwjust a_sup_set_class f2_pwjust a_wss i0_pwjust a_cab f1_pwjust a_sup_set_class f2_pwjust a_wss f1_pwjust a_cab p_eqtri $.
$}

$(Define power class.  Definition 5.10 of [TakeutiZaring] p. 17, but we
       also let it apply to proper classes, i.e. those that are not members of
       ` _V ` .  When applied to a set, this produces its power set.  A power
       set of S is the set of all subsets of S, including the empty set and S
       itself.  For example, if ` A = { 3 , 5 , 7 } ` , then
       ` ~P A = { (/) , { 3 } , { 5 } , { 7 } , { 3 , 5 } , `
       ` { 3 , 7 } , { 5 , 7 } , { 3 , 5 , 7 } } ` ( ~ ex-pw ).  We will later
       introduce the Axiom of Power Sets ~ ax-pow , which can be expressed in
       class notation per ~ pwexg .  Still later we will prove, in ~ hashpw ,
       that the size of the power set of a finite set is 2 raised to the power
       of the size of the set.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_df-pw $f set x $.
	f1_df-pw $f class A $.
	a_df-pw $a |- ~P A = { x | x C_ A } $.
$}

$(Equality theorem for power class.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_pweq $f class A $.
	f1_pweq $f class B $.
	i0_pweq $f set x $.
	p_pweq $p |- ( A = B -> ~P A = ~P B ) $= f0_pweq f1_pweq i0_pweq a_sup_set_class p_sseq2 f0_pweq f1_pweq a_wceq i0_pweq a_sup_set_class f0_pweq a_wss i0_pweq a_sup_set_class f1_pweq a_wss i0_pweq p_abbidv i0_pweq f0_pweq a_df-pw i0_pweq f1_pweq a_df-pw f0_pweq f1_pweq a_wceq i0_pweq a_sup_set_class f0_pweq a_wss i0_pweq a_cab i0_pweq a_sup_set_class f1_pweq a_wss i0_pweq a_cab f0_pweq a_cpw f1_pweq a_cpw p_3eqtr4g $.
$}

$(Equality inference for power class.  (Contributed by NM,
       27-Nov-2013.) $)

${
	$v A B  $.
	f0_pweqi $f class A $.
	f1_pweqi $f class B $.
	e0_pweqi $e |- A = B $.
	p_pweqi $p |- ~P A = ~P B $= e0_pweqi f0_pweqi f1_pweqi p_pweq f0_pweqi f1_pweqi a_wceq f0_pweqi a_cpw f1_pweqi a_cpw a_wceq a_ax-mp $.
$}

$(Equality deduction for power class.  (Contributed by NM,
       27-Nov-2013.) $)

${
	$v ph A B  $.
	f0_pweqd $f wff ph $.
	f1_pweqd $f class A $.
	f2_pweqd $f class B $.
	e0_pweqd $e |- ( ph -> A = B ) $.
	p_pweqd $p |- ( ph -> ~P A = ~P B ) $= e0_pweqd f1_pweqd f2_pweqd p_pweq f0_pweqd f1_pweqd f2_pweqd a_wceq f1_pweqd a_cpw f2_pweqd a_cpw a_wceq p_syl $.
$}

$(Membership in a power class.  Theorem 86 of [Suppes] p. 47.
         (Contributed by NM, 31-Dec-1993.) $)

${
	$v A B  $.
	$d A x  $.
	$d B x  $.
	f0_elpw $f class A $.
	f1_elpw $f class B $.
	i0_elpw $f set x $.
	e0_elpw $e |- A e. _V $.
	p_elpw $p |- ( A e. ~P B <-> A C_ B ) $= e0_elpw i0_elpw a_sup_set_class f0_elpw f1_elpw p_sseq1 i0_elpw f1_elpw a_df-pw i0_elpw a_sup_set_class f1_elpw a_wss f0_elpw f1_elpw a_wss i0_elpw f0_elpw f1_elpw a_cpw p_elab2 $.
$}

$(Membership in a power class.  Theorem 86 of [Suppes] p. 47.  See also
       ~ elpw2g .  (Contributed by NM, 6-Aug-2000.) $)

${
	$v A B V  $.
	$d A x  $.
	$d B x  $.
	f0_elpwg $f class A $.
	f1_elpwg $f class B $.
	f2_elpwg $f class V $.
	i0_elpwg $f set x $.
	p_elpwg $p |- ( A e. V -> ( A e. ~P B <-> A C_ B ) ) $= i0_elpwg a_sup_set_class f0_elpwg f1_elpwg a_cpw p_eleq1 i0_elpwg a_sup_set_class f0_elpwg f1_elpwg p_sseq1 i0_elpwg p_vex i0_elpwg a_sup_set_class f1_elpwg p_elpw i0_elpwg a_sup_set_class f1_elpwg a_cpw a_wcel i0_elpwg a_sup_set_class f1_elpwg a_wss f0_elpwg f1_elpwg a_cpw a_wcel f0_elpwg f1_elpwg a_wss i0_elpwg f0_elpwg f2_elpwg p_vtoclbg $.
$}

$(Subset relation implied by membership in a power class.  (Contributed by
     NM, 17-Feb-2007.) $)

${
	$v A B  $.
	f0_elpwi $f class A $.
	f1_elpwi $f class B $.
	p_elpwi $p |- ( A e. ~P B -> A C_ B ) $= f0_elpwi f1_elpwi f1_elpwi a_cpw p_elpwg f0_elpwi f1_elpwi a_cpw a_wcel f0_elpwi f1_elpwi a_wss p_ibi $.
$}

$(An element of a power class is a subclass.  Deduction form of ~ elpwi .
       (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B  $.
	f0_elpwid $f wff ph $.
	f1_elpwid $f class A $.
	f2_elpwid $f class B $.
	e0_elpwid $e |- ( ph -> A e. ~P B ) $.
	p_elpwid $p |- ( ph -> A C_ B ) $= e0_elpwid f1_elpwid f2_elpwid p_elpwi f0_elpwid f1_elpwid f2_elpwid a_cpw a_wcel f1_elpwid f2_elpwid a_wss p_syl $.
$}

$(If ` A ` belongs to a part of ` C ` then ` A ` belongs to ` C ` .
     (Contributed by FL, 3-Aug-2009.) $)

${
	$v A B C  $.
	f0_elelpwi $f class A $.
	f1_elelpwi $f class B $.
	f2_elelpwi $f class C $.
	p_elelpwi $p |- ( ( A e. B /\ B e. ~P C ) -> A e. C ) $= f1_elelpwi f2_elelpwi p_elpwi f1_elelpwi f2_elelpwi a_cpw a_wcel f1_elelpwi f2_elelpwi f0_elelpwi p_sseld f1_elelpwi f2_elelpwi a_cpw a_wcel f0_elelpwi f1_elelpwi a_wcel f0_elelpwi f2_elelpwi a_wcel p_impcom $.
$}

$(Bound-variable hypothesis builder for power class.  (Contributed by NM,
       28-Oct-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)

${
	$v x A  $.
	$d y A  $.
	$d x y  $.
	f0_nfpw $f set x $.
	f1_nfpw $f class A $.
	i0_nfpw $f set y $.
	e0_nfpw $e |- F/_ x A $.
	p_nfpw $p |- F/_ x ~P A $= i0_nfpw f1_nfpw a_df-pw f0_nfpw i0_nfpw a_sup_set_class p_nfcv e0_nfpw f0_nfpw i0_nfpw a_sup_set_class f1_nfpw p_nfss i0_nfpw a_sup_set_class f1_nfpw a_wss f0_nfpw i0_nfpw p_nfab f0_nfpw f1_nfpw a_cpw i0_nfpw a_sup_set_class f1_nfpw a_wss i0_nfpw a_cab p_nfcxfr $.
$}

$(Membership of the original in a power set.  (Contributed by Stefan O'Rear,
     1-Feb-2015.) $)

${
	$v A V  $.
	f0_pwidg $f class A $.
	f1_pwidg $f class V $.
	p_pwidg $p |- ( A e. V -> A e. ~P A ) $= f0_pwidg p_ssid f0_pwidg f0_pwidg f1_pwidg p_elpwg f0_pwidg f1_pwidg a_wcel f0_pwidg f0_pwidg a_cpw a_wcel f0_pwidg f0_pwidg a_wss p_mpbiri $.
$}

$(A set is a member of its power class.  Theorem 87 of [Suppes] p. 47.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	f0_pwid $f class A $.
	e0_pwid $e |- A e. _V $.
	p_pwid $p |- A e. ~P A $= e0_pwid f0_pwid a_cvv p_pwidg f0_pwid a_cvv a_wcel f0_pwid f0_pwid a_cpw a_wcel a_ax-mp $.
$}

$(Subclass relationship for power class.  (Contributed by NM,
       21-Jun-2009.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_pwss $f set x $.
	f1_pwss $f class A $.
	f2_pwss $f class B $.
	p_pwss $p |- ( ~P A C_ B <-> A. x ( x C_ A -> x e. B ) ) $= f0_pwss f1_pwss a_cpw f2_pwss p_dfss2 f0_pwss f1_pwss a_df-pw f0_pwss a_sup_set_class f1_pwss a_wss f0_pwss f1_pwss a_cpw p_abeq2i f0_pwss a_sup_set_class f1_pwss a_cpw a_wcel f0_pwss a_sup_set_class f1_pwss a_wss f0_pwss a_sup_set_class f2_pwss a_wcel p_imbi1i f0_pwss a_sup_set_class f1_pwss a_cpw a_wcel f0_pwss a_sup_set_class f2_pwss a_wcel a_wi f0_pwss a_sup_set_class f1_pwss a_wss f0_pwss a_sup_set_class f2_pwss a_wcel a_wi f0_pwss p_albii f1_pwss a_cpw f2_pwss a_wss f0_pwss a_sup_set_class f1_pwss a_cpw a_wcel f0_pwss a_sup_set_class f2_pwss a_wcel a_wi f0_pwss a_wal f0_pwss a_sup_set_class f1_pwss a_wss f0_pwss a_sup_set_class f2_pwss a_wcel a_wi f0_pwss a_wal p_bitri $.
$}


