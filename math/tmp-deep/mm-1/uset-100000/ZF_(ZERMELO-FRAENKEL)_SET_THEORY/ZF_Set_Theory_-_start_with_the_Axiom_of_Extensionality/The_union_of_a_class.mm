$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Unordered_and_ordered_pairs.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       The union of a class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare class union symbol. $)
$c U.  $.
$( Big cup $)
$( Extend class notation to include the union of a class (read:  'union
     ` A ` ') $)
${
	fcuni_0 $f class A $.
	cuni $a class U. A $.
$}
$( Define the union of a class i.e. the collection of all members of the
       members of the class.  Definition 5.5 of [TakeutiZaring] p. 16.  For
       example, ` U. { { 1 , 3 } , { 1 , 8 } } = { 1 , 3 , 8 } ` ( ~ ex-uni ).
       This is similar to the union of two classes ~ df-un .  (Contributed by
       NM, 23-Aug-1993.) $)
${
	$d x y A $.
	fdf-uni_0 $f set x $.
	fdf-uni_1 $f set y $.
	fdf-uni_2 $f class A $.
	df-uni $a |- U. A = { x | E. y ( x e. y /\ y e. A ) } $.
$}
$( Alternate definition of class union.  (Contributed by NM,
       28-Jun-1998.) $)
${
	$d x y A $.
	fdfuni2_0 $f set x $.
	fdfuni2_1 $f set y $.
	fdfuni2_2 $f class A $.
	dfuni2 $p |- U. A = { x | E. y e. A x e. y } $= fdfuni2_2 cuni fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 sup_set_class fdfuni2_2 wcel wa fdfuni2_1 wex fdfuni2_0 cab fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 fdfuni2_2 wrex fdfuni2_0 cab fdfuni2_0 fdfuni2_1 fdfuni2_2 df-uni fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 sup_set_class fdfuni2_2 wcel wa fdfuni2_1 wex fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 fdfuni2_2 wrex fdfuni2_0 fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 sup_set_class fdfuni2_2 wcel wa fdfuni2_1 wex fdfuni2_1 sup_set_class fdfuni2_2 wcel fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel wa fdfuni2_1 wex fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 fdfuni2_2 wrex fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 sup_set_class fdfuni2_2 wcel fdfuni2_1 exancom fdfuni2_0 sup_set_class fdfuni2_1 sup_set_class wcel fdfuni2_1 fdfuni2_2 df-rex bitr4i abbii eqtri $.
$}
$( Membership in class union.  (Contributed by NM, 22-May-1994.) $)
${
	$d x A y $.
	$d x B y $.
	ieluni_0 $f set y $.
	feluni_0 $f set x $.
	feluni_1 $f class A $.
	feluni_2 $f class B $.
	eluni $p |- ( A e. U. B <-> E. x ( A e. x /\ x e. B ) ) $= feluni_1 feluni_2 cuni wcel feluni_1 cvv wcel feluni_1 feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel wa feluni_0 wex feluni_1 feluni_2 cuni elex feluni_1 feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel wa feluni_1 cvv wcel feluni_0 feluni_1 feluni_0 sup_set_class wcel feluni_1 cvv wcel feluni_0 sup_set_class feluni_2 wcel feluni_1 feluni_0 sup_set_class elex adantr exlimiv ieluni_0 sup_set_class feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel wa feluni_0 wex feluni_1 feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel wa feluni_0 wex ieluni_0 feluni_1 feluni_2 cuni cvv ieluni_0 sup_set_class feluni_1 wceq ieluni_0 sup_set_class feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel wa feluni_1 feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel wa feluni_0 ieluni_0 sup_set_class feluni_1 wceq ieluni_0 sup_set_class feluni_0 sup_set_class wcel feluni_1 feluni_0 sup_set_class wcel feluni_0 sup_set_class feluni_2 wcel ieluni_0 sup_set_class feluni_1 feluni_0 sup_set_class eleq1 anbi1d exbidv ieluni_0 feluni_0 feluni_2 df-uni elab2g pm5.21nii $.
$}
$( Membership in class union.  Restricted quantifier version.  (Contributed
       by NM, 31-Aug-1999.) $)
${
	$d x A $.
	$d x B $.
	feluni2_0 $f set x $.
	feluni2_1 $f class A $.
	feluni2_2 $f class B $.
	eluni2 $p |- ( A e. U. B <-> E. x e. B A e. x ) $= feluni2_1 feluni2_0 sup_set_class wcel feluni2_0 sup_set_class feluni2_2 wcel wa feluni2_0 wex feluni2_0 sup_set_class feluni2_2 wcel feluni2_1 feluni2_0 sup_set_class wcel wa feluni2_0 wex feluni2_1 feluni2_2 cuni wcel feluni2_1 feluni2_0 sup_set_class wcel feluni2_0 feluni2_2 wrex feluni2_1 feluni2_0 sup_set_class wcel feluni2_0 sup_set_class feluni2_2 wcel feluni2_0 exancom feluni2_0 feluni2_1 feluni2_2 eluni feluni2_1 feluni2_0 sup_set_class wcel feluni2_0 feluni2_2 df-rex 3bitr4i $.
$}
$( Membership in class union.  (Contributed by NM, 24-Mar-1995.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ielunii_0 $f set x $.
	felunii_0 $f class A $.
	felunii_1 $f class B $.
	felunii_2 $f class C $.
	elunii $p |- ( ( A e. B /\ B e. C ) -> A e. U. C ) $= felunii_0 felunii_1 wcel felunii_1 felunii_2 wcel wa felunii_0 ielunii_0 sup_set_class wcel ielunii_0 sup_set_class felunii_2 wcel wa ielunii_0 wex felunii_0 felunii_2 cuni wcel felunii_0 felunii_1 wcel felunii_1 felunii_2 wcel felunii_0 ielunii_0 sup_set_class wcel ielunii_0 sup_set_class felunii_2 wcel wa ielunii_0 wex felunii_0 ielunii_0 sup_set_class wcel ielunii_0 sup_set_class felunii_2 wcel wa felunii_0 felunii_1 wcel felunii_1 felunii_2 wcel wa ielunii_0 felunii_1 felunii_2 ielunii_0 sup_set_class felunii_1 wceq felunii_0 ielunii_0 sup_set_class wcel felunii_0 felunii_1 wcel ielunii_0 sup_set_class felunii_2 wcel felunii_1 felunii_2 wcel ielunii_0 sup_set_class felunii_1 felunii_0 eleq2 ielunii_0 sup_set_class felunii_1 felunii_2 eleq1 anbi12d spcegv anabsi7 ielunii_0 felunii_0 felunii_2 eluni sylibr $.
$}
$( Bound-variable hypothesis builder for union.  (Contributed by NM,
       30-Dec-1996.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d y z A $.
	$d x y z $.
	infuni_0 $f set y $.
	infuni_1 $f set z $.
	fnfuni_0 $f set x $.
	fnfuni_1 $f class A $.
	enfuni_0 $e |- F/_ x A $.
	nfuni $p |- F/_ x U. A $= fnfuni_0 fnfuni_1 cuni infuni_0 sup_set_class infuni_1 sup_set_class wcel infuni_1 fnfuni_1 wrex infuni_0 cab infuni_0 infuni_1 fnfuni_1 dfuni2 infuni_0 sup_set_class infuni_1 sup_set_class wcel infuni_1 fnfuni_1 wrex fnfuni_0 infuni_0 infuni_0 sup_set_class infuni_1 sup_set_class wcel fnfuni_0 infuni_1 fnfuni_1 enfuni_0 infuni_0 sup_set_class infuni_1 sup_set_class wcel fnfuni_0 nfv nfrex nfab nfcxfr $.
$}
$( Deduction version of ~ nfuni .  (Contributed by NM, 18-Feb-2013.) $)
${
	$d y z A $.
	$d x y z $.
	$d y z ph $.
	infunid_0 $f set y $.
	infunid_1 $f set z $.
	fnfunid_0 $f wff ph $.
	fnfunid_1 $f set x $.
	fnfunid_2 $f class A $.
	enfunid_0 $e |- ( ph -> F/_ x A ) $.
	nfunid $p |- ( ph -> F/_ x U. A ) $= fnfunid_0 fnfunid_1 fnfunid_2 cuni infunid_0 sup_set_class infunid_1 sup_set_class wcel infunid_1 fnfunid_2 wrex infunid_0 cab infunid_0 infunid_1 fnfunid_2 dfuni2 fnfunid_0 infunid_0 sup_set_class infunid_1 sup_set_class wcel infunid_1 fnfunid_2 wrex fnfunid_1 infunid_0 fnfunid_0 infunid_0 nfv fnfunid_0 infunid_0 sup_set_class infunid_1 sup_set_class wcel fnfunid_1 infunid_1 fnfunid_2 fnfunid_0 infunid_1 nfv enfunid_0 fnfunid_0 infunid_0 sup_set_class infunid_1 sup_set_class wcel fnfunid_1 nfvd nfrexd nfabd nfcxfrd $.
$}
$( Distribute proper substitution through the union of a class.
       (Contributed by Alan Sare, 10-Nov-2012.) $)
${
	$d A y z $.
	$d B y z $.
	$d V y z $.
	$d x y z $.
	icsbunig_0 $f set y $.
	icsbunig_1 $f set z $.
	fcsbunig_0 $f set x $.
	fcsbunig_1 $f class A $.
	fcsbunig_2 $f class B $.
	fcsbunig_3 $f class V $.
	csbunig $p |- ( A e. V -> [_ A / x ]_ U. B = U. [_ A / x ]_ B ) $= fcsbunig_1 fcsbunig_3 wcel fcsbunig_0 fcsbunig_1 icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex icsbunig_1 cab csb icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel wa icsbunig_0 wex icsbunig_1 cab fcsbunig_0 fcsbunig_1 fcsbunig_2 cuni csb fcsbunig_0 fcsbunig_1 fcsbunig_2 csb cuni fcsbunig_1 fcsbunig_3 wcel fcsbunig_0 fcsbunig_1 icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex icsbunig_1 cab csb icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex fcsbunig_0 fcsbunig_1 wsbc icsbunig_1 cab icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel wa icsbunig_0 wex icsbunig_1 cab icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex fcsbunig_0 icsbunig_1 fcsbunig_1 fcsbunig_3 csbabg fcsbunig_1 fcsbunig_3 wcel icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex fcsbunig_0 fcsbunig_1 wsbc icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel wa icsbunig_0 wex icsbunig_1 fcsbunig_1 fcsbunig_3 wcel icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex fcsbunig_0 fcsbunig_1 wsbc icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa fcsbunig_0 fcsbunig_1 wsbc icsbunig_0 wex icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel wa icsbunig_0 wex icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 fcsbunig_0 fcsbunig_1 fcsbunig_3 sbcexg fcsbunig_1 fcsbunig_3 wcel icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa fcsbunig_0 fcsbunig_1 wsbc icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel wa icsbunig_0 fcsbunig_1 fcsbunig_3 wcel icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa fcsbunig_0 fcsbunig_1 wsbc icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel fcsbunig_0 fcsbunig_1 wsbc icsbunig_0 sup_set_class fcsbunig_2 wcel fcsbunig_0 fcsbunig_1 wsbc wa icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel wa icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel fcsbunig_0 fcsbunig_1 fcsbunig_3 sbcang fcsbunig_1 fcsbunig_3 wcel icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel fcsbunig_0 fcsbunig_1 wsbc icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel fcsbunig_0 fcsbunig_1 wsbc icsbunig_0 sup_set_class fcsbunig_0 fcsbunig_1 fcsbunig_2 csb wcel icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel fcsbunig_0 fcsbunig_1 fcsbunig_3 sbcg fcsbunig_0 fcsbunig_1 icsbunig_0 sup_set_class fcsbunig_2 fcsbunig_3 sbcel2g anbi12d bitrd exbidv bitrd abbidv eqtrd fcsbunig_0 fcsbunig_1 fcsbunig_2 cuni icsbunig_1 sup_set_class icsbunig_0 sup_set_class wcel icsbunig_0 sup_set_class fcsbunig_2 wcel wa icsbunig_0 wex icsbunig_1 cab icsbunig_1 icsbunig_0 fcsbunig_2 df-uni csbeq2i icsbunig_1 icsbunig_0 fcsbunig_0 fcsbunig_1 fcsbunig_2 csb df-uni 3eqtr4g $.
$}
$( Equality theorem for class union.  Exercise 15 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 10-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 29-Jun-2011.) $)
${
	$d x y A $.
	$d x y B $.
	iunieq_0 $f set x $.
	iunieq_1 $f set y $.
	funieq_0 $f class A $.
	funieq_1 $f class B $.
	unieq $p |- ( A = B -> U. A = U. B ) $= funieq_0 funieq_1 wceq iunieq_1 sup_set_class iunieq_0 sup_set_class wcel iunieq_0 funieq_0 wrex iunieq_1 cab iunieq_1 sup_set_class iunieq_0 sup_set_class wcel iunieq_0 funieq_1 wrex iunieq_1 cab funieq_0 cuni funieq_1 cuni funieq_0 funieq_1 wceq iunieq_1 sup_set_class iunieq_0 sup_set_class wcel iunieq_0 funieq_0 wrex iunieq_1 sup_set_class iunieq_0 sup_set_class wcel iunieq_0 funieq_1 wrex iunieq_1 iunieq_1 sup_set_class iunieq_0 sup_set_class wcel iunieq_0 funieq_0 funieq_1 rexeq abbidv iunieq_1 iunieq_0 funieq_0 dfuni2 iunieq_1 iunieq_0 funieq_1 dfuni2 3eqtr4g $.
$}
$( Inference of equality of two class unions.  (Contributed by NM,
       30-Aug-1993.) $)
${
	funieqi_0 $f class A $.
	funieqi_1 $f class B $.
	eunieqi_0 $e |- A = B $.
	unieqi $p |- U. A = U. B $= funieqi_0 funieqi_1 wceq funieqi_0 cuni funieqi_1 cuni wceq eunieqi_0 funieqi_0 funieqi_1 unieq ax-mp $.
$}
$( Deduction of equality of two class unions.  (Contributed by NM,
       21-Apr-1995.) $)
${
	funieqd_0 $f wff ph $.
	funieqd_1 $f class A $.
	funieqd_2 $f class B $.
	eunieqd_0 $e |- ( ph -> A = B ) $.
	unieqd $p |- ( ph -> U. A = U. B ) $= funieqd_0 funieqd_1 funieqd_2 wceq funieqd_1 cuni funieqd_2 cuni wceq eunieqd_0 funieqd_1 funieqd_2 unieq syl $.
$}
$( Membership in union of a class abstraction.  (Contributed by NM,
       11-Aug-1994.)  (Revised by Mario Carneiro, 14-Nov-2016.) $)
${
	$d x A y $.
	$d ph y $.
	ieluniab_0 $f set y $.
	feluniab_0 $f wff ph $.
	feluniab_1 $f set x $.
	feluniab_2 $f class A $.
	eluniab $p |- ( A e. U. { x | ph } <-> E. x ( A e. x /\ ph ) ) $= feluniab_2 feluniab_0 feluniab_1 cab cuni wcel feluniab_2 ieluniab_0 sup_set_class wcel ieluniab_0 sup_set_class feluniab_0 feluniab_1 cab wcel wa ieluniab_0 wex feluniab_2 feluniab_1 sup_set_class wcel feluniab_0 wa feluniab_1 wex ieluniab_0 feluniab_2 feluniab_0 feluniab_1 cab eluni feluniab_2 ieluniab_0 sup_set_class wcel ieluniab_0 sup_set_class feluniab_0 feluniab_1 cab wcel wa feluniab_2 feluniab_1 sup_set_class wcel feluniab_0 wa ieluniab_0 feluniab_1 feluniab_2 ieluniab_0 sup_set_class wcel ieluniab_0 sup_set_class feluniab_0 feluniab_1 cab wcel feluniab_1 feluniab_2 ieluniab_0 sup_set_class wcel feluniab_1 nfv feluniab_0 feluniab_1 ieluniab_0 nfsab1 nfan feluniab_2 feluniab_1 sup_set_class wcel feluniab_0 wa ieluniab_0 nfv ieluniab_0 sup_set_class feluniab_1 sup_set_class wceq feluniab_2 ieluniab_0 sup_set_class wcel feluniab_2 feluniab_1 sup_set_class wcel ieluniab_0 sup_set_class feluniab_0 feluniab_1 cab wcel feluniab_0 ieluniab_0 sup_set_class feluniab_1 sup_set_class feluniab_2 eleq2 ieluniab_0 sup_set_class feluniab_1 sup_set_class wceq ieluniab_0 sup_set_class feluniab_0 feluniab_1 cab wcel feluniab_1 sup_set_class feluniab_0 feluniab_1 cab wcel feluniab_0 ieluniab_0 sup_set_class feluniab_1 sup_set_class feluniab_0 feluniab_1 cab eleq1 feluniab_0 feluniab_1 abid syl6bb anbi12d cbvex bitri $.
$}
$( Membership in union of a class abstraction.  (Contributed by NM,
       4-Oct-2006.) $)
${
	$d x A $.
	felunirab_0 $f wff ph $.
	felunirab_1 $f set x $.
	felunirab_2 $f class A $.
	felunirab_3 $f class B $.
	elunirab $p |- ( A e. U. { x e. B | ph } <-> E. x e. B ( A e. x /\ ph ) ) $= felunirab_2 felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa felunirab_1 cab cuni wcel felunirab_2 felunirab_1 sup_set_class wcel felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa wa felunirab_1 wex felunirab_2 felunirab_0 felunirab_1 felunirab_3 crab cuni wcel felunirab_2 felunirab_1 sup_set_class wcel felunirab_0 wa felunirab_1 felunirab_3 wrex felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa felunirab_1 felunirab_2 eluniab felunirab_0 felunirab_1 felunirab_3 crab cuni felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa felunirab_1 cab cuni felunirab_2 felunirab_0 felunirab_1 felunirab_3 crab felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa felunirab_1 cab felunirab_0 felunirab_1 felunirab_3 df-rab unieqi eleq2i felunirab_2 felunirab_1 sup_set_class wcel felunirab_0 wa felunirab_1 felunirab_3 wrex felunirab_1 sup_set_class felunirab_3 wcel felunirab_2 felunirab_1 sup_set_class wcel felunirab_0 wa wa felunirab_1 wex felunirab_2 felunirab_1 sup_set_class wcel felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa wa felunirab_1 wex felunirab_2 felunirab_1 sup_set_class wcel felunirab_0 wa felunirab_1 felunirab_3 df-rex felunirab_1 sup_set_class felunirab_3 wcel felunirab_2 felunirab_1 sup_set_class wcel felunirab_0 wa wa felunirab_2 felunirab_1 sup_set_class wcel felunirab_1 sup_set_class felunirab_3 wcel felunirab_0 wa wa felunirab_1 felunirab_1 sup_set_class felunirab_3 wcel felunirab_2 felunirab_1 sup_set_class wcel felunirab_0 an12 exbii bitri 3bitr4i $.
$}
$( The union of a pair is the union of its members.  Proposition 5.7 of
       [TakeutiZaring] p. 16.  (Contributed by NM, 23-Aug-1993.) $)
${
	$d x y A $.
	$d x y B $.
	iunipr_0 $f set x $.
	iunipr_1 $f set y $.
	funipr_0 $f class A $.
	funipr_1 $f class B $.
	eunipr_0 $e |- A e. _V $.
	eunipr_1 $e |- B e. _V $.
	unipr $p |- U. { A , B } = ( A u. B ) $= iunipr_0 sup_set_class funipr_0 wcel iunipr_0 sup_set_class funipr_1 wcel wo iunipr_0 cab iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 funipr_1 cpr wcel wa iunipr_1 wex iunipr_0 cab funipr_0 funipr_1 cun funipr_0 funipr_1 cpr cuni iunipr_0 sup_set_class funipr_0 wcel iunipr_0 sup_set_class funipr_1 wcel wo iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 funipr_1 cpr wcel wa iunipr_1 wex iunipr_0 iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa wo iunipr_1 wex iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_1 wex iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa iunipr_1 wex wo iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 funipr_1 cpr wcel wa iunipr_1 wex iunipr_0 sup_set_class funipr_0 wcel iunipr_0 sup_set_class funipr_1 wcel wo iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa iunipr_1 19.43 iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 funipr_1 cpr wcel wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa wo iunipr_1 iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 funipr_1 cpr wcel wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq iunipr_1 sup_set_class funipr_1 wceq wo wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa wo iunipr_1 sup_set_class funipr_0 funipr_1 cpr wcel iunipr_1 sup_set_class funipr_0 wceq iunipr_1 sup_set_class funipr_1 wceq wo iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 funipr_1 iunipr_1 vex elpr anbi2i iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq iunipr_1 sup_set_class funipr_1 wceq andi bitri exbii iunipr_0 sup_set_class funipr_0 wcel iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_1 wex iunipr_0 sup_set_class funipr_1 wcel iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa iunipr_1 wex iunipr_0 sup_set_class funipr_0 wcel iunipr_1 sup_set_class funipr_0 wceq iunipr_0 sup_set_class iunipr_1 sup_set_class wcel wa iunipr_1 wex iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_0 wceq wa iunipr_1 wex iunipr_1 iunipr_0 sup_set_class funipr_0 eunipr_0 clel3 iunipr_1 sup_set_class funipr_0 wceq iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 exancom bitri iunipr_0 sup_set_class funipr_1 wcel iunipr_1 sup_set_class funipr_1 wceq iunipr_0 sup_set_class iunipr_1 sup_set_class wcel wa iunipr_1 wex iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 sup_set_class funipr_1 wceq wa iunipr_1 wex iunipr_1 iunipr_0 sup_set_class funipr_1 eunipr_1 clel3 iunipr_1 sup_set_class funipr_1 wceq iunipr_0 sup_set_class iunipr_1 sup_set_class wcel iunipr_1 exancom bitri orbi12i 3bitr4ri abbii iunipr_0 funipr_0 funipr_1 df-un iunipr_0 iunipr_1 funipr_0 funipr_1 cpr df-uni 3eqtr4ri $.
$}
$( The union of a pair is the union of its members.  Proposition 5.7 of
       [TakeutiZaring] p. 16.  (Contributed by NM, 25-Aug-2006.) $)
${
	$d x y A $.
	$d y B $.
	iuniprg_0 $f set x $.
	iuniprg_1 $f set y $.
	funiprg_0 $f class A $.
	funiprg_1 $f class B $.
	funiprg_2 $f class V $.
	funiprg_3 $f class W $.
	uniprg $p |- ( ( A e. V /\ B e. W ) -> U. { A , B } = ( A u. B ) ) $= iuniprg_0 sup_set_class iuniprg_1 sup_set_class cpr cuni iuniprg_0 sup_set_class iuniprg_1 sup_set_class cun wceq funiprg_0 iuniprg_1 sup_set_class cpr cuni funiprg_0 iuniprg_1 sup_set_class cun wceq funiprg_0 funiprg_1 cpr cuni funiprg_0 funiprg_1 cun wceq iuniprg_0 iuniprg_1 funiprg_0 funiprg_1 funiprg_2 funiprg_3 iuniprg_0 sup_set_class funiprg_0 wceq iuniprg_0 sup_set_class iuniprg_1 sup_set_class cpr cuni funiprg_0 iuniprg_1 sup_set_class cpr cuni iuniprg_0 sup_set_class iuniprg_1 sup_set_class cun funiprg_0 iuniprg_1 sup_set_class cun iuniprg_0 sup_set_class funiprg_0 wceq iuniprg_0 sup_set_class iuniprg_1 sup_set_class cpr funiprg_0 iuniprg_1 sup_set_class cpr iuniprg_0 sup_set_class funiprg_0 iuniprg_1 sup_set_class preq1 unieqd iuniprg_0 sup_set_class funiprg_0 iuniprg_1 sup_set_class uneq1 eqeq12d iuniprg_1 sup_set_class funiprg_1 wceq funiprg_0 iuniprg_1 sup_set_class cpr cuni funiprg_0 funiprg_1 cpr cuni funiprg_0 iuniprg_1 sup_set_class cun funiprg_0 funiprg_1 cun iuniprg_1 sup_set_class funiprg_1 wceq funiprg_0 iuniprg_1 sup_set_class cpr funiprg_0 funiprg_1 cpr iuniprg_1 sup_set_class funiprg_1 funiprg_0 preq2 unieqd iuniprg_1 sup_set_class funiprg_1 funiprg_0 uneq2 eqeq12d iuniprg_0 sup_set_class iuniprg_1 sup_set_class iuniprg_0 vex iuniprg_1 vex unipr vtocl2g $.
$}
$( A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       (Contributed by NM, 30-Aug-1993.) $)
${
	funisn_0 $f class A $.
	eunisn_0 $e |- A e. _V $.
	unisn $p |- U. { A } = A $= funisn_0 csn cuni funisn_0 funisn_0 cpr cuni funisn_0 funisn_0 cun funisn_0 funisn_0 csn funisn_0 funisn_0 cpr funisn_0 dfsn2 unieqi funisn_0 funisn_0 eunisn_0 eunisn_0 unipr funisn_0 unidm 3eqtri $.
$}
$( A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       (Contributed by NM, 13-Aug-2002.) $)
${
	$d x A $.
	iunisng_0 $f set x $.
	funisng_0 $f class A $.
	funisng_1 $f class V $.
	unisng $p |- ( A e. V -> U. { A } = A ) $= iunisng_0 sup_set_class csn cuni iunisng_0 sup_set_class wceq funisng_0 csn cuni funisng_0 wceq iunisng_0 funisng_0 funisng_1 iunisng_0 sup_set_class funisng_0 wceq iunisng_0 sup_set_class csn cuni funisng_0 csn cuni iunisng_0 sup_set_class funisng_0 iunisng_0 sup_set_class funisng_0 wceq iunisng_0 sup_set_class csn funisng_0 csn iunisng_0 sup_set_class funisng_0 sneq unieqd iunisng_0 sup_set_class funisng_0 wceq id eqeq12d iunisng_0 sup_set_class iunisng_0 vex unisn vtoclg $.
$}
$( An alternative statement of the effective freeness of a class ` A ` ,
       when it is a set.  (Contributed by Mario Carneiro, 14-Oct-2016.) $)
${
	$d x y $.
	$d y A $.
	fdfnfc2_0 $f set x $.
	fdfnfc2_1 $f set y $.
	fdfnfc2_2 $f class A $.
	fdfnfc2_3 $f class V $.
	dfnfc2 $p |- ( A. x A e. V -> ( F/_ x A <-> A. y F/ x y = A ) ) $= fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_0 fdfnfc2_2 wnfc fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_0 fdfnfc2_2 wnfc fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 fdfnfc2_0 fdfnfc2_2 wnfc fdfnfc2_0 fdfnfc2_1 sup_set_class fdfnfc2_2 fdfnfc2_0 fdfnfc2_2 wnfc fdfnfc2_0 fdfnfc2_1 sup_set_class nfcvd fdfnfc2_0 fdfnfc2_2 wnfc id nfeqd alrimiv fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_0 fdfnfc2_2 wnfc fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal wa fdfnfc2_0 fdfnfc2_2 csn cuni wnfc fdfnfc2_0 fdfnfc2_2 wnfc fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal wa fdfnfc2_0 fdfnfc2_2 csn fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal wa fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_0 fdfnfc2_2 csn wnfc fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal simpr fdfnfc2_0 fdfnfc2_2 csn wnfc fdfnfc2_1 sup_set_class fdfnfc2_2 csn wcel fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_0 fdfnfc2_1 fdfnfc2_2 csn df-nfc fdfnfc2_1 sup_set_class fdfnfc2_2 csn wcel fdfnfc2_0 wnf fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 fdfnfc2_1 sup_set_class fdfnfc2_2 csn wcel fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 fdfnfc2_1 fdfnfc2_2 elsn nfbii albii bitri sylibr nfunid fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal wa fdfnfc2_0 fdfnfc2_2 csn cuni fdfnfc2_2 fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_0 fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 nfa1 fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_0 fdfnfc2_1 fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 nfnf1 nfal nfan fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_0 wal fdfnfc2_2 csn cuni fdfnfc2_2 wceq fdfnfc2_1 sup_set_class fdfnfc2_2 wceq fdfnfc2_0 wnf fdfnfc2_1 wal fdfnfc2_2 fdfnfc2_3 wcel fdfnfc2_2 csn cuni fdfnfc2_2 wceq fdfnfc2_0 fdfnfc2_2 fdfnfc2_3 unisng sps adantr nfceqdf mpbid ex impbid2 $.
$}
$( The class union of the union of two classes.  Theorem 8.3 of [Quine]
       p. 53.  (Contributed by NM, 20-Aug-1993.) $)
${
	$d x y A $.
	$d x y B $.
	iuniun_0 $f set x $.
	iuniun_1 $f set y $.
	funiun_0 $f class A $.
	funiun_1 $f class B $.
	uniun $p |- U. ( A u. B ) = ( U. A u. U. B ) $= iuniun_0 funiun_0 funiun_1 cun cuni funiun_0 cuni funiun_1 cuni cun iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 funiun_1 cun wcel wa iuniun_1 wex iuniun_0 sup_set_class funiun_0 cuni wcel iuniun_0 sup_set_class funiun_1 cuni wcel wo iuniun_0 sup_set_class funiun_0 funiun_1 cun cuni wcel iuniun_0 sup_set_class funiun_0 cuni funiun_1 cuni cun wcel iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_1 wcel wa wo iuniun_1 wex iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel wa iuniun_1 wex iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_1 wcel wa iuniun_1 wex wo iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 funiun_1 cun wcel wa iuniun_1 wex iuniun_0 sup_set_class funiun_0 cuni wcel iuniun_0 sup_set_class funiun_1 cuni wcel wo iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_1 wcel wa iuniun_1 19.43 iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 funiun_1 cun wcel wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_1 wcel wa wo iuniun_1 iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 funiun_1 cun wcel wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel iuniun_1 sup_set_class funiun_1 wcel wo wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel wa iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_1 wcel wa wo iuniun_1 sup_set_class funiun_0 funiun_1 cun wcel iuniun_1 sup_set_class funiun_0 wcel iuniun_1 sup_set_class funiun_1 wcel wo iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 funiun_1 elun anbi2i iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel iuniun_1 sup_set_class funiun_1 wcel andi bitri exbii iuniun_0 sup_set_class funiun_0 cuni wcel iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_0 wcel wa iuniun_1 wex iuniun_0 sup_set_class funiun_1 cuni wcel iuniun_0 sup_set_class iuniun_1 sup_set_class wcel iuniun_1 sup_set_class funiun_1 wcel wa iuniun_1 wex iuniun_1 iuniun_0 sup_set_class funiun_0 eluni iuniun_1 iuniun_0 sup_set_class funiun_1 eluni orbi12i 3bitr4i iuniun_1 iuniun_0 sup_set_class funiun_0 funiun_1 cun eluni iuniun_0 sup_set_class funiun_0 cuni funiun_1 cuni elun 3bitr4i eqriv $.
$}
$( The class union of the intersection of two classes.  Exercise 4.12(n) of
       [Mendelson] p. 235.  See ~ uninqs for a condition where equality holds.
       (Contributed by NM, 4-Dec-2003.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
${
	$d x y A $.
	$d x y B $.
	iuniin_0 $f set x $.
	iuniin_1 $f set y $.
	funiin_0 $f class A $.
	funiin_1 $f class B $.
	uniin $p |- U. ( A i^i B ) C_ ( U. A i^i U. B ) $= iuniin_0 funiin_0 funiin_1 cin cuni funiin_0 cuni funiin_1 cuni cin iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 funiin_1 cin wcel wa iuniin_1 wex iuniin_0 sup_set_class funiin_0 cuni wcel iuniin_0 sup_set_class funiin_1 cuni wcel wa iuniin_0 sup_set_class funiin_0 funiin_1 cin cuni wcel iuniin_0 sup_set_class funiin_0 cuni funiin_1 cuni cin wcel iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_1 wcel wa wa iuniin_1 wex iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel wa iuniin_1 wex iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_1 wcel wa iuniin_1 wex wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 funiin_1 cin wcel wa iuniin_1 wex iuniin_0 sup_set_class funiin_0 cuni wcel iuniin_0 sup_set_class funiin_1 cuni wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_1 wcel wa iuniin_1 19.40 iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 funiin_1 cin wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_1 wcel wa wa iuniin_1 iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 funiin_1 cin wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel iuniin_1 sup_set_class funiin_1 wcel wa wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_1 wcel wa wa iuniin_1 sup_set_class funiin_0 funiin_1 cin wcel iuniin_1 sup_set_class funiin_0 wcel iuniin_1 sup_set_class funiin_1 wcel wa iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 funiin_1 elin anbi2i iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel iuniin_1 sup_set_class funiin_1 wcel anandi bitri exbii iuniin_0 sup_set_class funiin_0 cuni wcel iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_0 wcel wa iuniin_1 wex iuniin_0 sup_set_class funiin_1 cuni wcel iuniin_0 sup_set_class iuniin_1 sup_set_class wcel iuniin_1 sup_set_class funiin_1 wcel wa iuniin_1 wex iuniin_1 iuniin_0 sup_set_class funiin_0 eluni iuniin_1 iuniin_0 sup_set_class funiin_1 eluni anbi12i 3imtr4i iuniin_1 iuniin_0 sup_set_class funiin_0 funiin_1 cin eluni iuniin_0 sup_set_class funiin_0 cuni funiin_1 cuni elin 3imtr4i ssriv $.
$}
$( Subclass relationship for class union.  Theorem 61 of [Suppes] p. 39.
       (Contributed by NM, 22-Mar-1998.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	iuniss_0 $f set x $.
	iuniss_1 $f set y $.
	funiss_0 $f class A $.
	funiss_1 $f class B $.
	uniss $p |- ( A C_ B -> U. A C_ U. B ) $= funiss_0 funiss_1 wss iuniss_0 funiss_0 cuni funiss_1 cuni funiss_0 funiss_1 wss iuniss_0 sup_set_class iuniss_1 sup_set_class wcel iuniss_1 sup_set_class funiss_0 wcel wa iuniss_1 wex iuniss_0 sup_set_class iuniss_1 sup_set_class wcel iuniss_1 sup_set_class funiss_1 wcel wa iuniss_1 wex iuniss_0 sup_set_class funiss_0 cuni wcel iuniss_0 sup_set_class funiss_1 cuni wcel funiss_0 funiss_1 wss iuniss_0 sup_set_class iuniss_1 sup_set_class wcel iuniss_1 sup_set_class funiss_0 wcel wa iuniss_0 sup_set_class iuniss_1 sup_set_class wcel iuniss_1 sup_set_class funiss_1 wcel wa iuniss_1 funiss_0 funiss_1 wss iuniss_1 sup_set_class funiss_0 wcel iuniss_1 sup_set_class funiss_1 wcel iuniss_0 sup_set_class iuniss_1 sup_set_class wcel funiss_0 funiss_1 iuniss_1 sup_set_class ssel anim2d eximdv iuniss_1 iuniss_0 sup_set_class funiss_0 eluni iuniss_1 iuniss_0 sup_set_class funiss_1 eluni 3imtr4g ssrdv $.
$}
$( Subclass relationship for class union.  (Contributed by NM,
       24-May-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	issuni_0 $f set x $.
	issuni_1 $f set y $.
	fssuni_0 $f class A $.
	fssuni_1 $f class B $.
	fssuni_2 $f class C $.
	ssuni $p |- ( ( A C_ B /\ B e. C ) -> A C_ U. C ) $= fssuni_1 fssuni_2 wcel fssuni_0 fssuni_1 wss fssuni_0 fssuni_2 cuni wss fssuni_1 fssuni_2 wcel issuni_1 sup_set_class fssuni_0 wcel issuni_1 sup_set_class fssuni_1 wcel wi issuni_1 wal issuni_1 sup_set_class fssuni_0 wcel issuni_1 sup_set_class fssuni_2 cuni wcel wi issuni_1 wal fssuni_0 fssuni_1 wss fssuni_0 fssuni_2 cuni wss fssuni_1 fssuni_2 wcel issuni_1 sup_set_class fssuni_0 wcel issuni_1 sup_set_class fssuni_1 wcel wi issuni_1 sup_set_class fssuni_0 wcel issuni_1 sup_set_class fssuni_2 cuni wcel wi issuni_1 fssuni_1 fssuni_2 wcel issuni_1 sup_set_class fssuni_1 wcel issuni_1 sup_set_class fssuni_2 cuni wcel issuni_1 sup_set_class fssuni_0 wcel issuni_1 sup_set_class issuni_0 sup_set_class wcel issuni_1 sup_set_class fssuni_2 cuni wcel wi issuni_1 sup_set_class fssuni_1 wcel issuni_1 sup_set_class fssuni_2 cuni wcel wi issuni_0 fssuni_1 fssuni_2 issuni_0 sup_set_class fssuni_1 wceq issuni_1 sup_set_class issuni_0 sup_set_class wcel issuni_1 sup_set_class fssuni_1 wcel issuni_1 sup_set_class fssuni_2 cuni wcel issuni_0 sup_set_class fssuni_1 issuni_1 sup_set_class eleq2 imbi1d issuni_1 sup_set_class issuni_0 sup_set_class wcel issuni_0 sup_set_class fssuni_2 wcel issuni_1 sup_set_class fssuni_2 cuni wcel issuni_1 sup_set_class issuni_0 sup_set_class fssuni_2 elunii expcom vtoclga imim2d alimdv issuni_1 fssuni_0 fssuni_1 dfss2 issuni_1 fssuni_0 fssuni_2 cuni dfss2 3imtr4g impcom $.
$}
$( Subclass relationship for subclass union.  Inference form of ~ uniss .
       (Contributed by David Moews, 1-May-2017.) $)
${
	funissi_0 $f class A $.
	funissi_1 $f class B $.
	eunissi_0 $e |- A C_ B $.
	unissi $p |- U. A C_ U. B $= funissi_0 funissi_1 wss funissi_0 cuni funissi_1 cuni wss eunissi_0 funissi_0 funissi_1 uniss ax-mp $.
$}
$( Subclass relationship for subclass union.  Deduction form of ~ uniss .
       (Contributed by David Moews, 1-May-2017.) $)
${
	funissd_0 $f wff ph $.
	funissd_1 $f class A $.
	funissd_2 $f class B $.
	eunissd_0 $e |- ( ph -> A C_ B ) $.
	unissd $p |- ( ph -> U. A C_ U. B ) $= funissd_0 funissd_1 funissd_2 wss funissd_1 cuni funissd_2 cuni wss eunissd_0 funissd_1 funissd_2 uniss syl $.
$}
$( The union of a set is empty iff the set is included in the singleton of
       the empty set.  (Contributed by NM, 12-Sep-2004.) $)
${
	$d x y A $.
	iuni0b_0 $f set x $.
	iuni0b_1 $f set y $.
	funi0b_0 $f class A $.
	uni0b $p |- ( U. A = (/) <-> A C_ { (/) } ) $= iuni0b_0 sup_set_class c0 csn wcel iuni0b_0 funi0b_0 wral iuni0b_0 sup_set_class c0 wceq iuni0b_0 funi0b_0 wral funi0b_0 c0 csn wss funi0b_0 cuni c0 wceq iuni0b_0 sup_set_class c0 csn wcel iuni0b_0 sup_set_class c0 wceq iuni0b_0 funi0b_0 iuni0b_0 c0 elsn ralbii iuni0b_0 funi0b_0 c0 csn dfss3 funi0b_0 cuni c0 wceq iuni0b_0 sup_set_class c0 wceq iuni0b_0 funi0b_0 wral funi0b_0 cuni c0 wceq wn iuni0b_1 sup_set_class funi0b_0 cuni wcel iuni0b_1 wex iuni0b_0 sup_set_class c0 wceq wn iuni0b_0 funi0b_0 wrex iuni0b_0 sup_set_class c0 wceq iuni0b_0 funi0b_0 wral wn iuni0b_1 funi0b_0 cuni neq0 iuni0b_1 sup_set_class iuni0b_0 sup_set_class wcel iuni0b_1 wex iuni0b_0 funi0b_0 wrex iuni0b_1 sup_set_class iuni0b_0 sup_set_class wcel iuni0b_0 funi0b_0 wrex iuni0b_1 wex iuni0b_0 sup_set_class c0 wceq wn iuni0b_0 funi0b_0 wrex iuni0b_1 sup_set_class funi0b_0 cuni wcel iuni0b_1 wex iuni0b_1 sup_set_class iuni0b_0 sup_set_class wcel iuni0b_0 iuni0b_1 funi0b_0 rexcom4 iuni0b_0 sup_set_class c0 wceq wn iuni0b_1 sup_set_class iuni0b_0 sup_set_class wcel iuni0b_1 wex iuni0b_0 funi0b_0 iuni0b_1 iuni0b_0 sup_set_class neq0 rexbii iuni0b_1 sup_set_class funi0b_0 cuni wcel iuni0b_1 sup_set_class iuni0b_0 sup_set_class wcel iuni0b_0 funi0b_0 wrex iuni0b_1 iuni0b_0 iuni0b_1 sup_set_class funi0b_0 eluni2 exbii 3bitr4ri iuni0b_0 sup_set_class c0 wceq iuni0b_0 funi0b_0 rexnal 3bitri con4bii 3bitr4ri $.
$}
$( The union of a set is empty iff all of its members are empty.
       (Contributed by NM, 16-Aug-2006.) $)
${
	$d x A $.
	funi0c_0 $f set x $.
	funi0c_1 $f class A $.
	uni0c $p |- ( U. A = (/) <-> A. x e. A x = (/) ) $= funi0c_1 cuni c0 wceq funi0c_1 c0 csn wss funi0c_0 sup_set_class c0 csn wcel funi0c_0 funi0c_1 wral funi0c_0 sup_set_class c0 wceq funi0c_0 funi0c_1 wral funi0c_1 uni0b funi0c_0 funi0c_1 c0 csn dfss3 funi0c_0 sup_set_class c0 csn wcel funi0c_0 sup_set_class c0 wceq funi0c_0 funi0c_1 funi0c_0 c0 elsn ralbii 3bitri $.
$}
$( The union of the empty set is the empty set.  Theorem 8.7 of [Quine]
     p. 54.  (Reproved without relying on ~ ax-nul by Eric Schmidt.)
     (Contributed by NM, 16-Sep-1993.)  (Revised by Eric Schmidt,
     4-Apr-2007.) $)
${
	uni0 $p |- U. (/) = (/) $= c0 cuni c0 wceq c0 c0 csn wss c0 csn 0ss c0 uni0b mpbir $.
$}
$( An element of a class is a subclass of its union.  Theorem 8.6 of [Quine]
     p. 54.  Also the basis for Proposition 7.20 of [TakeutiZaring] p. 40.
     (Contributed by NM, 6-Jun-1994.) $)
${
	felssuni_0 $f class A $.
	felssuni_1 $f class B $.
	elssuni $p |- ( A e. B -> A C_ U. B ) $= felssuni_0 felssuni_0 wss felssuni_0 felssuni_1 wcel felssuni_0 felssuni_1 cuni wss felssuni_0 ssid felssuni_0 felssuni_0 felssuni_1 ssuni mpan $.
$}
$( Condition turning a subclass relationship for union into an equality.
     (Contributed by NM, 18-Jul-2006.) $)
${
	funissel_0 $f class A $.
	funissel_1 $f class B $.
	unissel $p |- ( ( U. A C_ B /\ B e. A ) -> U. A = B ) $= funissel_0 cuni funissel_1 wss funissel_1 funissel_0 wcel wa funissel_0 cuni funissel_1 funissel_0 cuni funissel_1 wss funissel_1 funissel_0 wcel simpl funissel_1 funissel_0 wcel funissel_1 funissel_0 cuni wss funissel_0 cuni funissel_1 wss funissel_1 funissel_0 elssuni adantl eqssd $.
$}
$( Relationship involving membership, subset, and union.  Exercise 5 of
       [Enderton] p. 26 and its converse.  (Contributed by NM, 20-Sep-2003.) $)
${
	$d x y A $.
	$d x y B $.
	iunissb_0 $f set y $.
	funissb_0 $f set x $.
	funissb_1 $f class A $.
	funissb_2 $f class B $.
	unissb $p |- ( U. A C_ B <-> A. x e. A x C_ B ) $= iunissb_0 sup_set_class funissb_1 cuni wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal funissb_0 sup_set_class funissb_1 wcel funissb_0 sup_set_class funissb_2 wss wi funissb_0 wal funissb_1 cuni funissb_2 wss funissb_0 sup_set_class funissb_2 wss funissb_0 funissb_1 wral iunissb_0 sup_set_class funissb_1 cuni wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi funissb_0 wal iunissb_0 wal funissb_0 sup_set_class funissb_1 wcel funissb_0 sup_set_class funissb_2 wss wi funissb_0 wal iunissb_0 sup_set_class funissb_1 cuni wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi funissb_0 wal iunissb_0 iunissb_0 sup_set_class funissb_1 cuni wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa funissb_0 wex iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi funissb_0 wal iunissb_0 sup_set_class funissb_1 cuni wcel iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa funissb_0 wex iunissb_0 sup_set_class funissb_2 wcel funissb_0 iunissb_0 sup_set_class funissb_1 eluni imbi1i iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel funissb_0 19.23v bitr4i albii iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi funissb_0 wal iunissb_0 wal iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal funissb_0 wal funissb_0 sup_set_class funissb_1 wcel funissb_0 sup_set_class funissb_2 wss wi funissb_0 wal iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 funissb_0 alcom iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal funissb_0 sup_set_class funissb_1 wcel funissb_0 sup_set_class funissb_2 wss wi funissb_0 funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_0 sup_set_class wcel iunissb_0 sup_set_class funissb_2 wcel wi wi iunissb_0 wal funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_0 sup_set_class wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal wi iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal funissb_0 sup_set_class funissb_1 wcel funissb_0 sup_set_class funissb_2 wss wi funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_0 sup_set_class wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 19.21v iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_0 sup_set_class wcel iunissb_0 sup_set_class funissb_2 wcel wi wi iunissb_0 iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel wa iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_2 wcel wi wi funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_0 sup_set_class wcel iunissb_0 sup_set_class funissb_2 wcel wi wi iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_2 wcel impexp iunissb_0 sup_set_class funissb_0 sup_set_class wcel funissb_0 sup_set_class funissb_1 wcel iunissb_0 sup_set_class funissb_2 wcel bi2.04 bitri albii funissb_0 sup_set_class funissb_2 wss iunissb_0 sup_set_class funissb_0 sup_set_class wcel iunissb_0 sup_set_class funissb_2 wcel wi iunissb_0 wal funissb_0 sup_set_class funissb_1 wcel iunissb_0 funissb_0 sup_set_class funissb_2 dfss2 imbi2i 3bitr4i albii bitri bitri iunissb_0 funissb_1 cuni funissb_2 dfss2 funissb_0 sup_set_class funissb_2 wss funissb_0 funissb_1 df-ral 3bitr4i $.
$}
$( A subclass condition on the members of two classes that implies a
       subclass relation on their unions.  Proposition 8.6 of [TakeutiZaring]
       p. 59.  See ~ iunss2 for a generalization to indexed unions.
       (Contributed by NM, 22-Mar-2004.) $)
${
	$d x A $.
	$d x y B $.
	funiss2_0 $f set x $.
	funiss2_1 $f set y $.
	funiss2_2 $f class A $.
	funiss2_3 $f class B $.
	uniss2 $p |- ( A. x e. A E. y e. B x C_ y -> U. A C_ U. B ) $= funiss2_0 sup_set_class funiss2_1 sup_set_class wss funiss2_1 funiss2_3 wrex funiss2_0 funiss2_2 wral funiss2_0 sup_set_class funiss2_3 cuni wss funiss2_0 funiss2_2 wral funiss2_2 cuni funiss2_3 cuni wss funiss2_0 sup_set_class funiss2_1 sup_set_class wss funiss2_1 funiss2_3 wrex funiss2_0 sup_set_class funiss2_3 cuni wss funiss2_0 funiss2_2 funiss2_0 sup_set_class funiss2_1 sup_set_class wss funiss2_0 sup_set_class funiss2_3 cuni wss funiss2_1 funiss2_3 funiss2_0 sup_set_class funiss2_1 sup_set_class wss funiss2_1 sup_set_class funiss2_3 wcel funiss2_0 sup_set_class funiss2_3 cuni wss funiss2_0 sup_set_class funiss2_1 sup_set_class funiss2_3 ssuni expcom rexlimiv ralimi funiss2_0 funiss2_2 funiss2_3 cuni unissb sylibr $.
$}
$( If the difference ` A \ B ` contains the largest members of ` A ` , then
       the union of the difference is the union of ` A ` .  (Contributed by NM,
       22-Mar-2004.) $)
${
	$d x y A $.
	$d x y B $.
	funidif_0 $f set x $.
	funidif_1 $f set y $.
	funidif_2 $f class A $.
	funidif_3 $f class B $.
	unidif $p |- ( A. x e. A E. y e. ( A \ B ) x C_ y -> U. ( A \ B ) = U. A ) $= funidif_0 sup_set_class funidif_1 sup_set_class wss funidif_1 funidif_2 funidif_3 cdif wrex funidif_0 funidif_2 wral funidif_2 funidif_3 cdif cuni funidif_2 cuni wss funidif_2 cuni funidif_2 funidif_3 cdif cuni wss wa funidif_2 funidif_3 cdif cuni funidif_2 cuni wceq funidif_0 sup_set_class funidif_1 sup_set_class wss funidif_1 funidif_2 funidif_3 cdif wrex funidif_0 funidif_2 wral funidif_2 cuni funidif_2 funidif_3 cdif cuni wss funidif_2 funidif_3 cdif cuni funidif_2 cuni wss funidif_0 funidif_1 funidif_2 funidif_2 funidif_3 cdif uniss2 funidif_2 funidif_3 cdif funidif_2 wss funidif_2 funidif_3 cdif cuni funidif_2 cuni wss funidif_2 funidif_3 difss funidif_2 funidif_3 cdif funidif_2 uniss ax-mp jctil funidif_2 funidif_3 cdif cuni funidif_2 cuni eqss sylibr $.
$}
$( Relationship implying union.  (Contributed by NM, 10-Nov-1999.) $)
${
	$d x A $.
	$d x B $.
	fssunieq_0 $f set x $.
	fssunieq_1 $f class A $.
	fssunieq_2 $f class B $.
	ssunieq $p |- ( ( A e. B /\ A. x e. B x C_ A ) -> A = U. B ) $= fssunieq_1 fssunieq_2 wcel fssunieq_0 sup_set_class fssunieq_1 wss fssunieq_0 fssunieq_2 wral wa fssunieq_1 fssunieq_2 cuni wss fssunieq_2 cuni fssunieq_1 wss wa fssunieq_1 fssunieq_2 cuni wceq fssunieq_1 fssunieq_2 wcel fssunieq_1 fssunieq_2 cuni wss fssunieq_0 sup_set_class fssunieq_1 wss fssunieq_0 fssunieq_2 wral fssunieq_2 cuni fssunieq_1 wss fssunieq_1 fssunieq_2 elssuni fssunieq_2 cuni fssunieq_1 wss fssunieq_0 sup_set_class fssunieq_1 wss fssunieq_0 fssunieq_2 wral fssunieq_0 fssunieq_2 fssunieq_1 unissb biimpri anim12i fssunieq_1 fssunieq_2 cuni eqss sylibr $.
$}
$( Any member of a class is the largest of those members that it includes.
       (Contributed by NM, 13-Aug-2002.) $)
${
	$d x y A $.
	$d x y B $.
	iunimax_0 $f set y $.
	funimax_0 $f set x $.
	funimax_1 $f class A $.
	funimax_2 $f class B $.
	unimax $p |- ( A e. B -> U. { x e. B | x C_ A } = A ) $= funimax_1 funimax_2 wcel funimax_1 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab wcel iunimax_0 sup_set_class funimax_1 wss iunimax_0 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab wral funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab cuni funimax_1 wceq funimax_1 funimax_2 wcel funimax_1 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab wcel funimax_1 funimax_1 wss funimax_1 ssid funimax_0 sup_set_class funimax_1 wss funimax_1 funimax_1 wss funimax_0 funimax_1 funimax_2 funimax_0 sup_set_class funimax_1 funimax_1 sseq1 elrab3 mpbiri iunimax_0 sup_set_class funimax_1 wss iunimax_0 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab iunimax_0 sup_set_class funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab wcel iunimax_0 sup_set_class funimax_2 wcel iunimax_0 sup_set_class funimax_1 wss funimax_0 sup_set_class funimax_1 wss iunimax_0 sup_set_class funimax_1 wss funimax_0 iunimax_0 sup_set_class funimax_2 funimax_0 sup_set_class iunimax_0 sup_set_class funimax_1 sseq1 elrab simprbi rgen funimax_1 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab wcel iunimax_0 sup_set_class funimax_1 wss iunimax_0 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab wral wa funimax_1 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab cuni iunimax_0 funimax_1 funimax_0 sup_set_class funimax_1 wss funimax_0 funimax_2 crab ssunieq eqcomd sylancl $.
$}

