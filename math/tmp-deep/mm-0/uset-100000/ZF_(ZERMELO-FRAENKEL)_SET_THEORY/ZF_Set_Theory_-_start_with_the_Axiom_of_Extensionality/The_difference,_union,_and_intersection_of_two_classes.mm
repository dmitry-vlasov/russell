$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Subclasses_and_subsets.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The difference, union, and intersection of two classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Equality theorem for class difference.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	idifeq1_0 $f set x $.
	fdifeq1_0 $f class A $.
	fdifeq1_1 $f class B $.
	fdifeq1_2 $f class C $.
	difeq1 $p |- ( A = B -> ( A \ C ) = ( B \ C ) ) $= fdifeq1_0 fdifeq1_1 wceq idifeq1_0 cv fdifeq1_2 wcel wn idifeq1_0 fdifeq1_0 crab idifeq1_0 cv fdifeq1_2 wcel wn idifeq1_0 fdifeq1_1 crab fdifeq1_0 fdifeq1_2 cdif fdifeq1_1 fdifeq1_2 cdif idifeq1_0 cv fdifeq1_2 wcel wn idifeq1_0 fdifeq1_0 fdifeq1_1 rabeq idifeq1_0 fdifeq1_0 fdifeq1_2 dfdif2 idifeq1_0 fdifeq1_1 fdifeq1_2 dfdif2 3eqtr4g $.
$}
$( Equality theorem for class difference.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	idifeq2_0 $f set x $.
	fdifeq2_0 $f class A $.
	fdifeq2_1 $f class B $.
	fdifeq2_2 $f class C $.
	difeq2 $p |- ( A = B -> ( C \ A ) = ( C \ B ) ) $= fdifeq2_0 fdifeq2_1 wceq idifeq2_0 cv fdifeq2_0 wcel wn idifeq2_0 fdifeq2_2 crab idifeq2_0 cv fdifeq2_1 wcel wn idifeq2_0 fdifeq2_2 crab fdifeq2_2 fdifeq2_0 cdif fdifeq2_2 fdifeq2_1 cdif fdifeq2_0 fdifeq2_1 wceq idifeq2_0 cv fdifeq2_0 wcel wn idifeq2_0 cv fdifeq2_1 wcel wn idifeq2_0 fdifeq2_2 fdifeq2_0 fdifeq2_1 wceq idifeq2_0 cv fdifeq2_0 wcel idifeq2_0 cv fdifeq2_1 wcel fdifeq2_0 fdifeq2_1 idifeq2_0 cv eleq2 notbid rabbidv idifeq2_0 fdifeq2_2 fdifeq2_0 dfdif2 idifeq2_0 fdifeq2_2 fdifeq2_1 dfdif2 3eqtr4g $.
$}
$( Equality theorem for class difference.  (Contributed by FL,
     31-Aug-2009.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fdifeq12_0 $f class A $.
	fdifeq12_1 $f class B $.
	fdifeq12_2 $f class C $.
	fdifeq12_3 $f class D $.
	difeq12 $p |- ( ( A = B /\ C = D ) -> ( A \ C ) = ( B \ D ) ) $= fdifeq12_0 fdifeq12_1 wceq fdifeq12_2 fdifeq12_3 wceq fdifeq12_0 fdifeq12_2 cdif fdifeq12_1 fdifeq12_2 cdif fdifeq12_1 fdifeq12_3 cdif fdifeq12_0 fdifeq12_1 fdifeq12_2 difeq1 fdifeq12_2 fdifeq12_3 fdifeq12_1 difeq2 sylan9eq $.
$}
$( Inference adding difference to the right in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifeq1i_0 $f class A $.
	fdifeq1i_1 $f class B $.
	fdifeq1i_2 $f class C $.
	edifeq1i_0 $e |- A = B $.
	difeq1i $p |- ( A \ C ) = ( B \ C ) $= fdifeq1i_0 fdifeq1i_1 wceq fdifeq1i_0 fdifeq1i_2 cdif fdifeq1i_1 fdifeq1i_2 cdif wceq edifeq1i_0 fdifeq1i_0 fdifeq1i_1 fdifeq1i_2 difeq1 ax-mp $.
$}
$( Inference adding difference to the left in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifeq2i_0 $f class A $.
	fdifeq2i_1 $f class B $.
	fdifeq2i_2 $f class C $.
	edifeq2i_0 $e |- A = B $.
	difeq2i $p |- ( C \ A ) = ( C \ B ) $= fdifeq2i_0 fdifeq2i_1 wceq fdifeq2i_2 fdifeq2i_0 cdif fdifeq2i_2 fdifeq2i_1 cdif wceq edifeq2i_0 fdifeq2i_0 fdifeq2i_1 fdifeq2i_2 difeq2 ax-mp $.
$}
$( Equality inference for class difference.  (Contributed by NM,
         29-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fdifeq12i_0 $f class A $.
	fdifeq12i_1 $f class B $.
	fdifeq12i_2 $f class C $.
	fdifeq12i_3 $f class D $.
	edifeq12i_0 $e |- A = B $.
	edifeq12i_1 $e |- C = D $.
	difeq12i $p |- ( A \ C ) = ( B \ D ) $= fdifeq12i_0 fdifeq12i_2 cdif fdifeq12i_1 fdifeq12i_2 cdif fdifeq12i_1 fdifeq12i_3 cdif fdifeq12i_0 fdifeq12i_1 fdifeq12i_2 edifeq12i_0 difeq1i fdifeq12i_2 fdifeq12i_3 fdifeq12i_1 edifeq12i_1 difeq2i eqtri $.
$}
$( Deduction adding difference to the right in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fdifeq1d_0 $f wff ph $.
	fdifeq1d_1 $f class A $.
	fdifeq1d_2 $f class B $.
	fdifeq1d_3 $f class C $.
	edifeq1d_0 $e |- ( ph -> A = B ) $.
	difeq1d $p |- ( ph -> ( A \ C ) = ( B \ C ) ) $= fdifeq1d_0 fdifeq1d_1 fdifeq1d_2 wceq fdifeq1d_1 fdifeq1d_3 cdif fdifeq1d_2 fdifeq1d_3 cdif wceq edifeq1d_0 fdifeq1d_1 fdifeq1d_2 fdifeq1d_3 difeq1 syl $.
$}
$( Deduction adding difference to the left in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fdifeq2d_0 $f wff ph $.
	fdifeq2d_1 $f class A $.
	fdifeq2d_2 $f class B $.
	fdifeq2d_3 $f class C $.
	edifeq2d_0 $e |- ( ph -> A = B ) $.
	difeq2d $p |- ( ph -> ( C \ A ) = ( C \ B ) ) $= fdifeq2d_0 fdifeq2d_1 fdifeq2d_2 wceq fdifeq2d_3 fdifeq2d_1 cdif fdifeq2d_3 fdifeq2d_2 cdif wceq edifeq2d_0 fdifeq2d_1 fdifeq2d_2 fdifeq2d_3 difeq2 syl $.
$}
$( Equality deduction for class difference.  (Contributed by FL,
       29-May-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fdifeq12d_0 $f wff ph $.
	fdifeq12d_1 $f class A $.
	fdifeq12d_2 $f class B $.
	fdifeq12d_3 $f class C $.
	fdifeq12d_4 $f class D $.
	edifeq12d_0 $e |- ( ph -> A = B ) $.
	edifeq12d_1 $e |- ( ph -> C = D ) $.
	difeq12d $p |- ( ph -> ( A \ C ) = ( B \ D ) ) $= fdifeq12d_0 fdifeq12d_1 fdifeq12d_3 cdif fdifeq12d_2 fdifeq12d_3 cdif fdifeq12d_2 fdifeq12d_4 cdif fdifeq12d_0 fdifeq12d_1 fdifeq12d_2 fdifeq12d_3 edifeq12d_0 difeq1d fdifeq12d_0 fdifeq12d_3 fdifeq12d_4 fdifeq12d_2 edifeq12d_1 difeq2d eqtrd $.
$}
$( Inference from membership to difference.  (Contributed by NM,
       17-May-1998.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	fdifeqri_0 $f set x $.
	fdifeqri_1 $f class A $.
	fdifeqri_2 $f class B $.
	fdifeqri_3 $f class C $.
	edifeqri_0 $e |- ( ( x e. A /\ -. x e. B ) <-> x e. C ) $.
	difeqri $p |- ( A \ B ) = C $= fdifeqri_0 fdifeqri_1 fdifeqri_2 cdif fdifeqri_3 fdifeqri_0 cv fdifeqri_1 fdifeqri_2 cdif wcel fdifeqri_0 cv fdifeqri_1 wcel fdifeqri_0 cv fdifeqri_2 wcel wn wa fdifeqri_0 cv fdifeqri_3 wcel fdifeqri_0 cv fdifeqri_1 fdifeqri_2 eldif edifeqri_0 bitri eqriv $.
$}
$( Bound-variable hypothesis builder for class difference.  (Contributed by
       NM, 3-Dec-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	infdif_0 $f set y $.
	fnfdif_0 $f set x $.
	fnfdif_1 $f class A $.
	fnfdif_2 $f class B $.
	enfdif_0 $e |- F/_ x A $.
	enfdif_1 $e |- F/_ x B $.
	nfdif $p |- F/_ x ( A \ B ) $= fnfdif_0 fnfdif_1 fnfdif_2 cdif infdif_0 cv fnfdif_2 wcel wn infdif_0 fnfdif_1 crab infdif_0 fnfdif_1 fnfdif_2 dfdif2 infdif_0 cv fnfdif_2 wcel wn fnfdif_0 infdif_0 fnfdif_1 infdif_0 cv fnfdif_2 wcel fnfdif_0 fnfdif_0 infdif_0 fnfdif_2 enfdif_1 nfcri nfn enfdif_0 nfrab nfcxfr $.
$}
$( Implication of membership in a class difference.  (Contributed by NM,
     29-Apr-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feldifi_0 $f class A $.
	feldifi_1 $f class B $.
	feldifi_2 $f class C $.
	eldifi $p |- ( A e. ( B \ C ) -> A e. B ) $= feldifi_0 feldifi_1 feldifi_2 cdif wcel feldifi_0 feldifi_1 wcel feldifi_0 feldifi_2 wcel wn feldifi_0 feldifi_1 feldifi_2 eldif simplbi $.
$}
$( Implication of membership in a class difference.  (Contributed by NM,
     3-May-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feldifn_0 $f class A $.
	feldifn_1 $f class B $.
	feldifn_2 $f class C $.
	eldifn $p |- ( A e. ( B \ C ) -> -. A e. C ) $= feldifn_0 feldifn_1 feldifn_2 cdif wcel feldifn_0 feldifn_1 wcel feldifn_0 feldifn_2 wcel wn feldifn_0 feldifn_1 feldifn_2 eldif simprbi $.
$}
$( A set does not belong to a class excluding it.  (Contributed by NM,
     27-Jun-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	felndif_0 $f class A $.
	felndif_1 $f class B $.
	felndif_2 $f class C $.
	elndif $p |- ( A e. B -> -. A e. ( C \ B ) ) $= felndif_0 felndif_2 felndif_1 cdif wcel felndif_0 felndif_1 wcel felndif_0 felndif_2 felndif_1 eldifn con2i $.
$}
$( Implication of membership in a class difference.  (Contributed by NM,
     28-Jun-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneldif_0 $f class A $.
	fneldif_1 $f class B $.
	fneldif_2 $f class C $.
	neldif $p |- ( ( A e. B /\ -. A e. ( B \ C ) ) -> A e. C ) $= fneldif_0 fneldif_1 wcel fneldif_0 fneldif_1 fneldif_2 cdif wcel wn fneldif_0 fneldif_2 wcel fneldif_0 fneldif_1 wcel fneldif_0 fneldif_2 wcel fneldif_0 fneldif_1 fneldif_2 cdif wcel fneldif_0 fneldif_1 fneldif_2 cdif wcel fneldif_0 fneldif_1 wcel fneldif_0 fneldif_2 wcel wn fneldif_0 fneldif_1 fneldif_2 eldif simplbi2 con1d imp $.
$}
$( Double class difference.  Exercise 11 of [TakeutiZaring] p. 22.
       (Contributed by NM, 17-May-1998.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	idifdif_0 $f set x $.
	fdifdif_0 $f class A $.
	fdifdif_1 $f class B $.
	difdif $p |- ( A \ ( B \ A ) ) = A $= idifdif_0 fdifdif_0 fdifdif_1 fdifdif_0 cdif fdifdif_0 idifdif_0 cv fdifdif_0 wcel idifdif_0 cv fdifdif_0 wcel idifdif_0 cv fdifdif_1 wcel idifdif_0 cv fdifdif_0 wcel wi wa idifdif_0 cv fdifdif_0 wcel idifdif_0 cv fdifdif_1 fdifdif_0 cdif wcel wn wa idifdif_0 cv fdifdif_0 wcel idifdif_0 cv fdifdif_1 wcel pm4.45im idifdif_0 cv fdifdif_1 wcel idifdif_0 cv fdifdif_0 wcel wi idifdif_0 cv fdifdif_1 fdifdif_0 cdif wcel wn idifdif_0 cv fdifdif_0 wcel idifdif_0 cv fdifdif_1 wcel idifdif_0 cv fdifdif_0 wcel wi idifdif_0 cv fdifdif_1 wcel idifdif_0 cv fdifdif_0 wcel wn wa idifdif_0 cv fdifdif_1 fdifdif_0 cdif wcel idifdif_0 cv fdifdif_1 wcel idifdif_0 cv fdifdif_0 wcel iman idifdif_0 cv fdifdif_1 fdifdif_0 eldif xchbinxr anbi2i bitr2i difeqri $.
$}
$( Subclass relationship for class difference.  Exercise 14 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 29-Apr-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	idifss_0 $f set x $.
	fdifss_0 $f class A $.
	fdifss_1 $f class B $.
	difss $p |- ( A \ B ) C_ A $= idifss_0 fdifss_0 fdifss_1 cdif fdifss_0 idifss_0 cv fdifss_0 fdifss_1 eldifi ssriv $.
$}
$( A difference of two classes is contained in the minuend.  Deduction form
     of ~ difss .  (Contributed by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fdifssd_0 $f wff ph $.
	fdifssd_1 $f class A $.
	fdifssd_2 $f class B $.
	difssd $p |- ( ph -> ( A \ B ) C_ A ) $= fdifssd_1 fdifssd_2 cdif fdifssd_1 wss fdifssd_0 fdifssd_1 fdifssd_2 difss a1i $.
$}
$( If a class is contained in a difference, it is contained in the minuend.
     (Contributed by David Moews, 1-May-2017.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifss2_0 $f class A $.
	fdifss2_1 $f class B $.
	fdifss2_2 $f class C $.
	difss2 $p |- ( A C_ ( B \ C ) -> A C_ B ) $= fdifss2_0 fdifss2_1 fdifss2_2 cdif wss fdifss2_0 fdifss2_1 fdifss2_2 cdif fdifss2_1 fdifss2_0 fdifss2_1 fdifss2_2 cdif wss id fdifss2_1 fdifss2_2 difss syl6ss $.
$}
$( If a class is contained in a difference, it is contained in the
       minuend.  Deduction form of ~ difss2 .  (Contributed by David Moews,
       1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fdifss2d_0 $f wff ph $.
	fdifss2d_1 $f class A $.
	fdifss2d_2 $f class B $.
	fdifss2d_3 $f class C $.
	edifss2d_0 $e |- ( ph -> A C_ ( B \ C ) ) $.
	difss2d $p |- ( ph -> A C_ B ) $= fdifss2d_0 fdifss2d_1 fdifss2d_2 fdifss2d_3 cdif wss fdifss2d_1 fdifss2d_2 wss edifss2d_0 fdifss2d_1 fdifss2d_2 fdifss2d_3 difss2 syl $.
$}
$( Preservation of a subclass relationship by class difference.  (Contributed
     by NM, 15-Feb-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssdifss_0 $f class A $.
	fssdifss_1 $f class B $.
	fssdifss_2 $f class C $.
	ssdifss $p |- ( A C_ B -> ( A \ C ) C_ B ) $= fssdifss_0 fssdifss_2 cdif fssdifss_0 wss fssdifss_0 fssdifss_1 wss fssdifss_0 fssdifss_2 cdif fssdifss_1 wss fssdifss_0 fssdifss_2 difss fssdifss_0 fssdifss_2 cdif fssdifss_0 fssdifss_1 sstr mpan $.
$}
$( Double complement under universal class.  Exercise 4.10(s) of
       [Mendelson] p. 231.  (Contributed by NM, 8-Jan-2002.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	iddif_0 $f set x $.
	fddif_0 $f class A $.
	ddif $p |- ( _V \ ( _V \ A ) ) = A $= iddif_0 cvv cvv fddif_0 cdif fddif_0 iddif_0 cv fddif_0 wcel iddif_0 cv cvv fddif_0 cdif wcel wn iddif_0 cv cvv wcel iddif_0 cv cvv fddif_0 cdif wcel wn wa iddif_0 cv cvv fddif_0 cdif wcel iddif_0 cv fddif_0 wcel iddif_0 cv cvv fddif_0 cdif wcel iddif_0 cv cvv wcel iddif_0 cv fddif_0 wcel wn iddif_0 vex iddif_0 cv cvv fddif_0 eldif mpbiran con2bii iddif_0 cv cvv wcel iddif_0 cv cvv fddif_0 cdif wcel wn iddif_0 vex biantrur bitr2i difeqri $.
$}
$( Contraposition law for subsets.  (Contributed by NM, 22-Mar-1998.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	issconb_0 $f set x $.
	fssconb_0 $f class A $.
	fssconb_1 $f class B $.
	fssconb_2 $f class C $.
	ssconb $p |- ( ( A C_ C /\ B C_ C ) -> ( A C_ ( C \ B ) <-> B C_ ( C \ A ) ) ) $= fssconb_0 fssconb_2 wss fssconb_1 fssconb_2 wss wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 fssconb_1 cdif wcel wi issconb_0 wal issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 fssconb_0 cdif wcel wi issconb_0 wal fssconb_0 fssconb_2 fssconb_1 cdif wss fssconb_1 fssconb_2 fssconb_0 cdif wss fssconb_0 fssconb_2 wss fssconb_1 fssconb_2 wss wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 fssconb_1 cdif wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 fssconb_0 cdif wcel wi issconb_0 fssconb_0 fssconb_2 wss fssconb_1 fssconb_2 wss wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_1 wcel wn wa wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_0 wcel wn wa wi issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 fssconb_1 cdif wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 fssconb_0 cdif wcel wi fssconb_0 fssconb_2 wss fssconb_1 fssconb_2 wss wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_1 wcel wn wi wa issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_0 wcel wn wi wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_1 wcel wn wa wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_0 wcel wn wa wi fssconb_0 fssconb_2 wss fssconb_1 fssconb_2 wss wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_1 wcel wn wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_0 wcel wn wi fssconb_0 fssconb_2 wss issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel wi wb fssconb_1 fssconb_2 wss fssconb_0 fssconb_2 issconb_0 cv ssel fssconb_1 fssconb_2 issconb_0 cv ssel issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel wi pm5.1 syl2an issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_1 wcel wn wi issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_0 wcel wn wi wb fssconb_0 fssconb_2 wss fssconb_1 fssconb_2 wss wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_1 wcel con2b a1i anbi12d issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_1 wcel wn jcab issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_0 wcel wn jcab 3bitr4g issconb_0 cv fssconb_2 fssconb_1 cdif wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_1 wcel wn wa issconb_0 cv fssconb_0 wcel issconb_0 cv fssconb_2 fssconb_1 eldif imbi2i issconb_0 cv fssconb_2 fssconb_0 cdif wcel issconb_0 cv fssconb_2 wcel issconb_0 cv fssconb_0 wcel wn wa issconb_0 cv fssconb_1 wcel issconb_0 cv fssconb_2 fssconb_0 eldif imbi2i 3bitr4g albidv issconb_0 fssconb_0 fssconb_2 fssconb_1 cdif dfss2 issconb_0 fssconb_1 fssconb_2 fssconb_0 cdif dfss2 3bitr4g $.
$}
$( Contraposition law for subsets.  Exercise 15 of [TakeutiZaring] p. 22.
       (Contributed by NM, 22-Mar-1998.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	isscon_0 $f set x $.
	fsscon_0 $f class A $.
	fsscon_1 $f class B $.
	fsscon_2 $f class C $.
	sscon $p |- ( A C_ B -> ( C \ B ) C_ ( C \ A ) ) $= fsscon_0 fsscon_1 wss isscon_0 fsscon_2 fsscon_1 cdif fsscon_2 fsscon_0 cdif fsscon_0 fsscon_1 wss isscon_0 cv fsscon_2 wcel isscon_0 cv fsscon_1 wcel wn wa isscon_0 cv fsscon_2 wcel isscon_0 cv fsscon_0 wcel wn wa isscon_0 cv fsscon_2 fsscon_1 cdif wcel isscon_0 cv fsscon_2 fsscon_0 cdif wcel fsscon_0 fsscon_1 wss isscon_0 cv fsscon_1 wcel wn isscon_0 cv fsscon_0 wcel wn isscon_0 cv fsscon_2 wcel fsscon_0 fsscon_1 wss isscon_0 cv fsscon_0 wcel isscon_0 cv fsscon_1 wcel fsscon_0 fsscon_1 isscon_0 cv ssel con3d anim2d isscon_0 cv fsscon_2 fsscon_1 eldif isscon_0 cv fsscon_2 fsscon_0 eldif 3imtr4g ssrdv $.
$}
$( Difference law for subsets.  (Contributed by NM, 28-May-1998.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	issdif_0 $f set x $.
	fssdif_0 $f class A $.
	fssdif_1 $f class B $.
	fssdif_2 $f class C $.
	ssdif $p |- ( A C_ B -> ( A \ C ) C_ ( B \ C ) ) $= fssdif_0 fssdif_1 wss issdif_0 fssdif_0 fssdif_2 cdif fssdif_1 fssdif_2 cdif fssdif_0 fssdif_1 wss issdif_0 cv fssdif_0 wcel issdif_0 cv fssdif_2 wcel wn wa issdif_0 cv fssdif_1 wcel issdif_0 cv fssdif_2 wcel wn wa issdif_0 cv fssdif_0 fssdif_2 cdif wcel issdif_0 cv fssdif_1 fssdif_2 cdif wcel fssdif_0 fssdif_1 wss issdif_0 cv fssdif_0 wcel issdif_0 cv fssdif_1 wcel issdif_0 cv fssdif_2 wcel wn fssdif_0 fssdif_1 issdif_0 cv ssel anim1d issdif_0 cv fssdif_0 fssdif_2 eldif issdif_0 cv fssdif_1 fssdif_2 eldif 3imtr4g ssrdv $.
$}
$( If ` A ` is contained in ` B ` , then ` ( A \ C ) ` is contained in
       ` ( B \ C ) ` .  Deduction form of ~ ssdif .  (Contributed by David
       Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fssdifd_0 $f wff ph $.
	fssdifd_1 $f class A $.
	fssdifd_2 $f class B $.
	fssdifd_3 $f class C $.
	essdifd_0 $e |- ( ph -> A C_ B ) $.
	ssdifd $p |- ( ph -> ( A \ C ) C_ ( B \ C ) ) $= fssdifd_0 fssdifd_1 fssdifd_2 wss fssdifd_1 fssdifd_3 cdif fssdifd_2 fssdifd_3 cdif wss essdifd_0 fssdifd_1 fssdifd_2 fssdifd_3 ssdif syl $.
$}
$( If ` A ` is contained in ` B ` , then ` ( C \ B ) ` is contained in
       ` ( C \ A ) ` .  Deduction form of ~ sscon .  (Contributed by David
       Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsscond_0 $f wff ph $.
	fsscond_1 $f class A $.
	fsscond_2 $f class B $.
	fsscond_3 $f class C $.
	esscond_0 $e |- ( ph -> A C_ B ) $.
	sscond $p |- ( ph -> ( C \ B ) C_ ( C \ A ) ) $= fsscond_0 fsscond_1 fsscond_2 wss fsscond_3 fsscond_2 cdif fsscond_3 fsscond_1 cdif wss esscond_0 fsscond_1 fsscond_2 fsscond_3 sscon syl $.
$}
$( If ` A ` is contained in ` B ` , then ` ( A \ C ) ` is also contained in
       ` B ` .  Deduction form of ~ ssdifss .  (Contributed by David Moews,
       1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fssdifssd_0 $f wff ph $.
	fssdifssd_1 $f class A $.
	fssdifssd_2 $f class B $.
	fssdifssd_3 $f class C $.
	essdifssd_0 $e |- ( ph -> A C_ B ) $.
	ssdifssd $p |- ( ph -> ( A \ C ) C_ B ) $= fssdifssd_0 fssdifssd_1 fssdifssd_2 wss fssdifssd_1 fssdifssd_3 cdif fssdifssd_2 wss essdifssd_0 fssdifssd_1 fssdifssd_2 fssdifssd_3 ssdifss syl $.
$}
$( If ` A ` is contained in ` B ` and ` C ` is contained in ` D ` , then
       ` ( A \ D ) ` is contained in ` ( B \ C ) ` .  Deduction form.
       (Contributed by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fssdif2d_0 $f wff ph $.
	fssdif2d_1 $f class A $.
	fssdif2d_2 $f class B $.
	fssdif2d_3 $f class C $.
	fssdif2d_4 $f class D $.
	essdif2d_0 $e |- ( ph -> A C_ B ) $.
	essdif2d_1 $e |- ( ph -> C C_ D ) $.
	ssdif2d $p |- ( ph -> ( A \ D ) C_ ( B \ C ) ) $= fssdif2d_0 fssdif2d_1 fssdif2d_4 cdif fssdif2d_1 fssdif2d_3 cdif fssdif2d_2 fssdif2d_3 cdif fssdif2d_0 fssdif2d_3 fssdif2d_4 fssdif2d_1 essdif2d_1 sscond fssdif2d_0 fssdif2d_1 fssdif2d_2 fssdif2d_3 essdif2d_0 ssdifd sstrd $.
$}
$( Expansion of membership in class union.  Theorem 12 of [Suppes] p. 25.
       (Contributed by NM, 7-Aug-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	ielun_0 $f set x $.
	felun_0 $f class A $.
	felun_1 $f class B $.
	felun_2 $f class C $.
	elun $p |- ( A e. ( B u. C ) <-> ( A e. B \/ A e. C ) ) $= felun_0 felun_1 felun_2 cun wcel felun_0 cvv wcel felun_0 felun_1 wcel felun_0 felun_2 wcel wo felun_0 felun_1 felun_2 cun elex felun_0 felun_1 wcel felun_0 cvv wcel felun_0 felun_2 wcel felun_0 felun_1 elex felun_0 felun_2 elex jaoi ielun_0 cv felun_1 wcel ielun_0 cv felun_2 wcel wo felun_0 felun_1 wcel felun_0 felun_2 wcel wo ielun_0 felun_0 felun_1 felun_2 cun cvv ielun_0 cv felun_0 wceq ielun_0 cv felun_1 wcel felun_0 felun_1 wcel ielun_0 cv felun_2 wcel felun_0 felun_2 wcel ielun_0 cv felun_0 felun_1 eleq1 ielun_0 cv felun_0 felun_2 eleq1 orbi12d ielun_0 felun_1 felun_2 df-un elab2g pm5.21nii $.
$}
$( Inference from membership to union.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	funeqri_0 $f set x $.
	funeqri_1 $f class A $.
	funeqri_2 $f class B $.
	funeqri_3 $f class C $.
	euneqri_0 $e |- ( ( x e. A \/ x e. B ) <-> x e. C ) $.
	uneqri $p |- ( A u. B ) = C $= funeqri_0 funeqri_1 funeqri_2 cun funeqri_3 funeqri_0 cv funeqri_1 funeqri_2 cun wcel funeqri_0 cv funeqri_1 wcel funeqri_0 cv funeqri_2 wcel wo funeqri_0 cv funeqri_3 wcel funeqri_0 cv funeqri_1 funeqri_2 elun euneqri_0 bitri eqriv $.
$}
$( Idempotent law for union of classes.  Theorem 23 of [Suppes] p. 27.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	iunidm_0 $f set x $.
	funidm_0 $f class A $.
	unidm $p |- ( A u. A ) = A $= iunidm_0 funidm_0 funidm_0 funidm_0 iunidm_0 cv funidm_0 wcel oridm uneqri $.
$}
$( Commutative law for union of classes.  Exercise 6 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	iuncom_0 $f set x $.
	funcom_0 $f class A $.
	funcom_1 $f class B $.
	uncom $p |- ( A u. B ) = ( B u. A ) $= iuncom_0 funcom_0 funcom_1 funcom_1 funcom_0 cun iuncom_0 cv funcom_0 wcel iuncom_0 cv funcom_1 wcel wo iuncom_0 cv funcom_1 wcel iuncom_0 cv funcom_0 wcel wo iuncom_0 cv funcom_1 funcom_0 cun wcel iuncom_0 cv funcom_0 wcel iuncom_0 cv funcom_1 wcel orcom iuncom_0 cv funcom_1 funcom_0 elun bitr4i uneqri $.
$}
$( If a class equals the union of two other classes, then it equals the
       union of those two classes commuted. ~ equncom was automatically derived
       from ~ equncomVD using the tools program
       translate_without_overwriting.cmd and minimizing.  (Contributed by Alan
       Sare, 18-Feb-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fequncom_0 $f class A $.
	fequncom_1 $f class B $.
	fequncom_2 $f class C $.
	equncom $p |- ( A = ( B u. C ) <-> A = ( C u. B ) ) $= fequncom_1 fequncom_2 cun fequncom_2 fequncom_1 cun fequncom_0 fequncom_1 fequncom_2 uncom eqeq2i $.
$}
$( Inference form of ~ equncom . ~ equncomi was automatically derived from
       ~ equncomiVD using the tools program translate_without_overwriting.cmd
       and minimizing.  (Contributed by Alan Sare, 18-Feb-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fequncomi_0 $f class A $.
	fequncomi_1 $f class B $.
	fequncomi_2 $f class C $.
	eequncomi_0 $e |- A = ( B u. C ) $.
	equncomi $p |- A = ( C u. B ) $= fequncomi_0 fequncomi_1 fequncomi_2 cun wceq fequncomi_0 fequncomi_2 fequncomi_1 cun wceq eequncomi_0 fequncomi_0 fequncomi_1 fequncomi_2 equncom mpbi $.
$}
$( Equality theorem for union of two classes.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iuneq1_0 $f set x $.
	funeq1_0 $f class A $.
	funeq1_1 $f class B $.
	funeq1_2 $f class C $.
	uneq1 $p |- ( A = B -> ( A u. C ) = ( B u. C ) ) $= funeq1_0 funeq1_1 wceq iuneq1_0 funeq1_0 funeq1_2 cun funeq1_1 funeq1_2 cun funeq1_0 funeq1_1 wceq iuneq1_0 cv funeq1_0 wcel iuneq1_0 cv funeq1_2 wcel wo iuneq1_0 cv funeq1_1 wcel iuneq1_0 cv funeq1_2 wcel wo iuneq1_0 cv funeq1_0 funeq1_2 cun wcel iuneq1_0 cv funeq1_1 funeq1_2 cun wcel funeq1_0 funeq1_1 wceq iuneq1_0 cv funeq1_0 wcel iuneq1_0 cv funeq1_1 wcel iuneq1_0 cv funeq1_2 wcel funeq1_0 funeq1_1 iuneq1_0 cv eleq2 orbi1d iuneq1_0 cv funeq1_0 funeq1_2 elun iuneq1_0 cv funeq1_1 funeq1_2 elun 3bitr4g eqrdv $.
$}
$( Equality theorem for the union of two classes.  (Contributed by NM,
     5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funeq2_0 $f class A $.
	funeq2_1 $f class B $.
	funeq2_2 $f class C $.
	uneq2 $p |- ( A = B -> ( C u. A ) = ( C u. B ) ) $= funeq2_0 funeq2_1 wceq funeq2_0 funeq2_2 cun funeq2_1 funeq2_2 cun funeq2_2 funeq2_0 cun funeq2_2 funeq2_1 cun funeq2_0 funeq2_1 funeq2_2 uneq1 funeq2_2 funeq2_0 uncom funeq2_2 funeq2_1 uncom 3eqtr4g $.
$}
$( Equality theorem for union of two classes.  (Contributed by NM,
     29-Mar-1998.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	funeq12_0 $f class A $.
	funeq12_1 $f class B $.
	funeq12_2 $f class C $.
	funeq12_3 $f class D $.
	uneq12 $p |- ( ( A = B /\ C = D ) -> ( A u. C ) = ( B u. D ) ) $= funeq12_0 funeq12_1 wceq funeq12_2 funeq12_3 wceq funeq12_0 funeq12_2 cun funeq12_1 funeq12_2 cun funeq12_1 funeq12_3 cun funeq12_0 funeq12_1 funeq12_2 uneq1 funeq12_2 funeq12_3 funeq12_1 uneq2 sylan9eq $.
$}
$( Inference adding union to the right in a class equality.  (Contributed
       by NM, 30-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funeq1i_0 $f class A $.
	funeq1i_1 $f class B $.
	funeq1i_2 $f class C $.
	euneq1i_0 $e |- A = B $.
	uneq1i $p |- ( A u. C ) = ( B u. C ) $= funeq1i_0 funeq1i_1 wceq funeq1i_0 funeq1i_2 cun funeq1i_1 funeq1i_2 cun wceq euneq1i_0 funeq1i_0 funeq1i_1 funeq1i_2 uneq1 ax-mp $.
$}
$( Inference adding union to the left in a class equality.  (Contributed by
       NM, 30-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funeq2i_0 $f class A $.
	funeq2i_1 $f class B $.
	funeq2i_2 $f class C $.
	euneq2i_0 $e |- A = B $.
	uneq2i $p |- ( C u. A ) = ( C u. B ) $= funeq2i_0 funeq2i_1 wceq funeq2i_2 funeq2i_0 cun funeq2i_2 funeq2i_1 cun wceq euneq2i_0 funeq2i_0 funeq2i_1 funeq2i_2 uneq2 ax-mp $.
$}
$( Equality inference for union of two classes.  (Contributed by NM,
         12-Aug-2004.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	funeq12i_0 $f class A $.
	funeq12i_1 $f class B $.
	funeq12i_2 $f class C $.
	funeq12i_3 $f class D $.
	euneq12i_0 $e |- A = B $.
	euneq12i_1 $e |- C = D $.
	uneq12i $p |- ( A u. C ) = ( B u. D ) $= funeq12i_0 funeq12i_1 wceq funeq12i_2 funeq12i_3 wceq funeq12i_0 funeq12i_2 cun funeq12i_1 funeq12i_3 cun wceq euneq12i_0 euneq12i_1 funeq12i_0 funeq12i_1 funeq12i_2 funeq12i_3 uneq12 mp2an $.
$}
$( Deduction adding union to the right in a class equality.  (Contributed
       by NM, 29-Mar-1998.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	funeq1d_0 $f wff ph $.
	funeq1d_1 $f class A $.
	funeq1d_2 $f class B $.
	funeq1d_3 $f class C $.
	euneq1d_0 $e |- ( ph -> A = B ) $.
	uneq1d $p |- ( ph -> ( A u. C ) = ( B u. C ) ) $= funeq1d_0 funeq1d_1 funeq1d_2 wceq funeq1d_1 funeq1d_3 cun funeq1d_2 funeq1d_3 cun wceq euneq1d_0 funeq1d_1 funeq1d_2 funeq1d_3 uneq1 syl $.
$}
$( Deduction adding union to the left in a class equality.  (Contributed by
       NM, 29-Mar-1998.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	funeq2d_0 $f wff ph $.
	funeq2d_1 $f class A $.
	funeq2d_2 $f class B $.
	funeq2d_3 $f class C $.
	euneq2d_0 $e |- ( ph -> A = B ) $.
	uneq2d $p |- ( ph -> ( C u. A ) = ( C u. B ) ) $= funeq2d_0 funeq2d_1 funeq2d_2 wceq funeq2d_3 funeq2d_1 cun funeq2d_3 funeq2d_2 cun wceq euneq2d_0 funeq2d_1 funeq2d_2 funeq2d_3 uneq2 syl $.
$}
$( Equality deduction for union of two classes.  (Contributed by NM,
         29-Sep-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	funeq12d_0 $f wff ph $.
	funeq12d_1 $f class A $.
	funeq12d_2 $f class B $.
	funeq12d_3 $f class C $.
	funeq12d_4 $f class D $.
	euneq12d_0 $e |- ( ph -> A = B ) $.
	euneq12d_1 $e |- ( ph -> C = D ) $.
	uneq12d $p |- ( ph -> ( A u. C ) = ( B u. D ) ) $= funeq12d_0 funeq12d_1 funeq12d_2 wceq funeq12d_3 funeq12d_4 wceq funeq12d_1 funeq12d_3 cun funeq12d_2 funeq12d_4 cun wceq euneq12d_0 euneq12d_1 funeq12d_1 funeq12d_2 funeq12d_3 funeq12d_4 uneq12 syl2anc $.
$}
$( Bound-variable hypothesis builder for the union of classes.
       (Contributed by NM, 15-Sep-2003.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	infun_0 $f set y $.
	fnfun_0 $f set x $.
	fnfun_1 $f class A $.
	fnfun_2 $f class B $.
	enfun_0 $e |- F/_ x A $.
	enfun_1 $e |- F/_ x B $.
	nfun $p |- F/_ x ( A u. B ) $= fnfun_0 fnfun_1 fnfun_2 cun infun_0 cv fnfun_1 wcel infun_0 cv fnfun_2 wcel wo infun_0 cab infun_0 fnfun_1 fnfun_2 df-un infun_0 cv fnfun_1 wcel infun_0 cv fnfun_2 wcel wo fnfun_0 infun_0 infun_0 cv fnfun_1 wcel infun_0 cv fnfun_2 wcel fnfun_0 fnfun_0 infun_0 fnfun_1 enfun_0 nfcri fnfun_0 infun_0 fnfun_2 enfun_1 nfcri nfor nfab nfcxfr $.
$}
$( Associative law for union of classes.  Exercise 8 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 3-May-1994.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d A x $.
	$d B x $.
	$d C x $.
	iunass_0 $f set x $.
	funass_0 $f class A $.
	funass_1 $f class B $.
	funass_2 $f class C $.
	unass $p |- ( ( A u. B ) u. C ) = ( A u. ( B u. C ) ) $= iunass_0 funass_0 funass_1 cun funass_2 funass_0 funass_1 funass_2 cun cun iunass_0 cv funass_0 funass_1 funass_2 cun cun wcel iunass_0 cv funass_0 wcel iunass_0 cv funass_1 funass_2 cun wcel wo iunass_0 cv funass_0 wcel iunass_0 cv funass_1 wcel iunass_0 cv funass_2 wcel wo wo iunass_0 cv funass_0 funass_1 cun wcel iunass_0 cv funass_2 wcel wo iunass_0 cv funass_0 funass_1 funass_2 cun elun iunass_0 cv funass_1 funass_2 cun wcel iunass_0 cv funass_1 wcel iunass_0 cv funass_2 wcel wo iunass_0 cv funass_0 wcel iunass_0 cv funass_1 funass_2 elun orbi2i iunass_0 cv funass_0 funass_1 cun wcel iunass_0 cv funass_2 wcel wo iunass_0 cv funass_0 wcel iunass_0 cv funass_1 wcel wo iunass_0 cv funass_2 wcel wo iunass_0 cv funass_0 wcel iunass_0 cv funass_1 wcel iunass_0 cv funass_2 wcel wo wo iunass_0 cv funass_0 funass_1 cun wcel iunass_0 cv funass_0 wcel iunass_0 cv funass_1 wcel wo iunass_0 cv funass_2 wcel iunass_0 cv funass_0 funass_1 elun orbi1i iunass_0 cv funass_0 wcel iunass_0 cv funass_1 wcel iunass_0 cv funass_2 wcel orass bitr2i 3bitrri uneqri $.
$}
$( A rearrangement of union.  (Contributed by NM, 12-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fun12_0 $f class A $.
	fun12_1 $f class B $.
	fun12_2 $f class C $.
	un12 $p |- ( A u. ( B u. C ) ) = ( B u. ( A u. C ) ) $= fun12_0 fun12_1 cun fun12_2 cun fun12_1 fun12_0 cun fun12_2 cun fun12_0 fun12_1 fun12_2 cun cun fun12_1 fun12_0 fun12_2 cun cun fun12_0 fun12_1 cun fun12_1 fun12_0 cun fun12_2 fun12_0 fun12_1 uncom uneq1i fun12_0 fun12_1 fun12_2 unass fun12_1 fun12_0 fun12_2 unass 3eqtr3i $.
$}
$( A rearrangement of union.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fun23_0 $f class A $.
	fun23_1 $f class B $.
	fun23_2 $f class C $.
	un23 $p |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. B ) $= fun23_0 fun23_1 cun fun23_2 cun fun23_0 fun23_1 fun23_2 cun cun fun23_1 fun23_0 fun23_2 cun cun fun23_0 fun23_2 cun fun23_1 cun fun23_0 fun23_1 fun23_2 unass fun23_0 fun23_1 fun23_2 un12 fun23_1 fun23_0 fun23_2 cun uncom 3eqtri $.
$}
$( A rearrangement of the union of 4 classes.  (Contributed by NM,
     12-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fun4_0 $f class A $.
	fun4_1 $f class B $.
	fun4_2 $f class C $.
	fun4_3 $f class D $.
	un4 $p |- ( ( A u. B ) u. ( C u. D ) ) = ( ( A u. C ) u. ( B u. D ) ) $= fun4_0 fun4_1 fun4_2 fun4_3 cun cun cun fun4_0 fun4_2 fun4_1 fun4_3 cun cun cun fun4_0 fun4_1 cun fun4_2 fun4_3 cun cun fun4_0 fun4_2 cun fun4_1 fun4_3 cun cun fun4_1 fun4_2 fun4_3 cun cun fun4_2 fun4_1 fun4_3 cun cun fun4_0 fun4_1 fun4_2 fun4_3 un12 uneq2i fun4_0 fun4_1 fun4_2 fun4_3 cun unass fun4_0 fun4_2 fun4_1 fun4_3 cun unass 3eqtr4i $.
$}
$( Union distributes over itself.  (Contributed by NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funundi_0 $f class A $.
	funundi_1 $f class B $.
	funundi_2 $f class C $.
	unundi $p |- ( A u. ( B u. C ) ) = ( ( A u. B ) u. ( A u. C ) ) $= funundi_0 funundi_0 cun funundi_1 funundi_2 cun cun funundi_0 funundi_1 funundi_2 cun cun funundi_0 funundi_1 cun funundi_0 funundi_2 cun cun funundi_0 funundi_0 cun funundi_0 funundi_1 funundi_2 cun funundi_0 unidm uneq1i funundi_0 funundi_0 funundi_1 funundi_2 un4 eqtr3i $.
$}
$( Union distributes over itself.  (Contributed by NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funundir_0 $f class A $.
	funundir_1 $f class B $.
	funundir_2 $f class C $.
	unundir $p |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. ( B u. C ) ) $= funundir_0 funundir_1 cun funundir_2 funundir_2 cun cun funundir_0 funundir_1 cun funundir_2 cun funundir_0 funundir_2 cun funundir_1 funundir_2 cun cun funundir_2 funundir_2 cun funundir_2 funundir_0 funundir_1 cun funundir_2 unidm uneq2i funundir_0 funundir_1 funundir_2 funundir_2 un4 eqtr3i $.
$}
$( Subclass relationship for union of classes.  Theorem 25 of [Suppes]
       p. 27.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	issun1_0 $f set x $.
	fssun1_0 $f class A $.
	fssun1_1 $f class B $.
	ssun1 $p |- A C_ ( A u. B ) $= issun1_0 fssun1_0 fssun1_0 fssun1_1 cun issun1_0 cv fssun1_0 wcel issun1_0 cv fssun1_0 wcel issun1_0 cv fssun1_1 wcel wo issun1_0 cv fssun1_0 fssun1_1 cun wcel issun1_0 cv fssun1_0 wcel issun1_0 cv fssun1_1 wcel orc issun1_0 cv fssun1_0 fssun1_1 elun sylibr ssriv $.
$}
$( Subclass relationship for union of classes.  (Contributed by NM,
     30-Aug-1993.) $)
${
	$v A $.
	$v B $.
	fssun2_0 $f class A $.
	fssun2_1 $f class B $.
	ssun2 $p |- A C_ ( B u. A ) $= fssun2_0 fssun2_0 fssun2_1 cun fssun2_1 fssun2_0 cun fssun2_0 fssun2_1 ssun1 fssun2_0 fssun2_1 uncom sseqtri $.
$}
$( Subclass law for union of classes.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssun3_0 $f class A $.
	fssun3_1 $f class B $.
	fssun3_2 $f class C $.
	ssun3 $p |- ( A C_ B -> A C_ ( B u. C ) ) $= fssun3_0 fssun3_1 wss fssun3_1 fssun3_1 fssun3_2 cun wss fssun3_0 fssun3_1 fssun3_2 cun wss fssun3_1 fssun3_2 ssun1 fssun3_0 fssun3_1 fssun3_1 fssun3_2 cun sstr2 mpi $.
$}
$( Subclass law for union of classes.  (Contributed by NM, 14-Aug-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssun4_0 $f class A $.
	fssun4_1 $f class B $.
	fssun4_2 $f class C $.
	ssun4 $p |- ( A C_ B -> A C_ ( C u. B ) ) $= fssun4_0 fssun4_1 wss fssun4_1 fssun4_2 fssun4_1 cun wss fssun4_0 fssun4_2 fssun4_1 cun wss fssun4_1 fssun4_2 ssun2 fssun4_0 fssun4_1 fssun4_2 fssun4_1 cun sstr2 mpi $.
$}
$( Membership law for union of classes.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	felun1_0 $f class A $.
	felun1_1 $f class B $.
	felun1_2 $f class C $.
	elun1 $p |- ( A e. B -> A e. ( B u. C ) ) $= felun1_1 felun1_1 felun1_2 cun felun1_0 felun1_1 felun1_2 ssun1 sseli $.
$}
$( Membership law for union of classes.  (Contributed by NM, 30-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	felun2_0 $f class A $.
	felun2_1 $f class B $.
	felun2_2 $f class C $.
	elun2 $p |- ( A e. B -> A e. ( C u. B ) ) $= felun2_1 felun2_2 felun2_1 cun felun2_0 felun2_1 felun2_2 ssun2 sseli $.
$}
$( Subclass law for union of classes.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iunss1_0 $f set x $.
	funss1_0 $f class A $.
	funss1_1 $f class B $.
	funss1_2 $f class C $.
	unss1 $p |- ( A C_ B -> ( A u. C ) C_ ( B u. C ) ) $= funss1_0 funss1_1 wss iunss1_0 funss1_0 funss1_2 cun funss1_1 funss1_2 cun funss1_0 funss1_1 wss iunss1_0 cv funss1_0 wcel iunss1_0 cv funss1_2 wcel wo iunss1_0 cv funss1_1 wcel iunss1_0 cv funss1_2 wcel wo iunss1_0 cv funss1_0 funss1_2 cun wcel iunss1_0 cv funss1_1 funss1_2 cun wcel funss1_0 funss1_1 wss iunss1_0 cv funss1_0 wcel iunss1_0 cv funss1_1 wcel iunss1_0 cv funss1_2 wcel funss1_0 funss1_1 iunss1_0 cv ssel orim1d iunss1_0 cv funss1_0 funss1_2 elun iunss1_0 cv funss1_1 funss1_2 elun 3imtr4g ssrdv $.
$}
$( A relationship between subclass and union.  Theorem 26 of [Suppes]
       p. 27.  (Contributed by NM, 30-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	issequn1_0 $f set x $.
	fssequn1_0 $f class A $.
	fssequn1_1 $f class B $.
	ssequn1 $p |- ( A C_ B <-> ( A u. B ) = B ) $= issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wi issequn1_0 wal issequn1_0 cv fssequn1_0 fssequn1_1 cun wcel issequn1_0 cv fssequn1_1 wcel wb issequn1_0 wal fssequn1_0 fssequn1_1 wss fssequn1_0 fssequn1_1 cun fssequn1_1 wceq issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wi issequn1_0 cv fssequn1_0 fssequn1_1 cun wcel issequn1_0 cv fssequn1_1 wcel wb issequn1_0 issequn1_0 cv fssequn1_1 wcel issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wo wb issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wo issequn1_0 cv fssequn1_1 wcel wb issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wi issequn1_0 cv fssequn1_0 fssequn1_1 cun wcel issequn1_0 cv fssequn1_1 wcel wb issequn1_0 cv fssequn1_1 wcel issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wo bicom issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel pm4.72 issequn1_0 cv fssequn1_0 fssequn1_1 cun wcel issequn1_0 cv fssequn1_0 wcel issequn1_0 cv fssequn1_1 wcel wo issequn1_0 cv fssequn1_1 wcel issequn1_0 cv fssequn1_0 fssequn1_1 elun bibi1i 3bitr4i albii issequn1_0 fssequn1_0 fssequn1_1 dfss2 issequn1_0 fssequn1_0 fssequn1_1 cun fssequn1_1 dfcleq 3bitr4i $.
$}
$( Subclass law for union of classes.  Exercise 7 of [TakeutiZaring] p. 18.
     (Contributed by NM, 14-Oct-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funss2_0 $f class A $.
	funss2_1 $f class B $.
	funss2_2 $f class C $.
	unss2 $p |- ( A C_ B -> ( C u. A ) C_ ( C u. B ) ) $= funss2_0 funss2_1 wss funss2_0 funss2_2 cun funss2_1 funss2_2 cun funss2_2 funss2_0 cun funss2_2 funss2_1 cun funss2_0 funss2_1 funss2_2 unss1 funss2_2 funss2_0 uncom funss2_2 funss2_1 uncom 3sstr4g $.
$}
$( Subclass law for union of classes.  (Contributed by NM, 2-Jun-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	funss12_0 $f class A $.
	funss12_1 $f class B $.
	funss12_2 $f class C $.
	funss12_3 $f class D $.
	unss12 $p |- ( ( A C_ B /\ C C_ D ) -> ( A u. C ) C_ ( B u. D ) ) $= funss12_0 funss12_1 wss funss12_2 funss12_3 wss funss12_0 funss12_2 cun funss12_1 funss12_2 cun funss12_1 funss12_3 cun funss12_0 funss12_1 funss12_2 unss1 funss12_2 funss12_3 funss12_1 unss2 sylan9ss $.
$}
$( A relationship between subclass and union.  (Contributed by NM,
     13-Jun-1994.) $)
${
	$v A $.
	$v B $.
	fssequn2_0 $f class A $.
	fssequn2_1 $f class B $.
	ssequn2 $p |- ( A C_ B <-> ( B u. A ) = B ) $= fssequn2_0 fssequn2_1 wss fssequn2_0 fssequn2_1 cun fssequn2_1 wceq fssequn2_1 fssequn2_0 cun fssequn2_1 wceq fssequn2_0 fssequn2_1 ssequn1 fssequn2_0 fssequn2_1 cun fssequn2_1 fssequn2_0 cun fssequn2_1 fssequn2_0 fssequn2_1 uncom eqeq1i bitri $.
$}
$( The union of two subclasses is a subclass.  Theorem 27 of [Suppes] p. 27
       and its converse.  (Contributed by NM, 11-Jun-2004.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iunss_0 $f set x $.
	funss_0 $f class A $.
	funss_1 $f class B $.
	funss_2 $f class C $.
	unss $p |- ( ( A C_ C /\ B C_ C ) <-> ( A u. B ) C_ C ) $= funss_0 funss_1 cun funss_2 wss iunss_0 cv funss_0 funss_1 cun wcel iunss_0 cv funss_2 wcel wi iunss_0 wal funss_0 funss_2 wss funss_1 funss_2 wss wa iunss_0 funss_0 funss_1 cun funss_2 dfss2 iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel wi iunss_0 cv funss_1 wcel iunss_0 cv funss_2 wcel wi wa iunss_0 wal iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel wi iunss_0 wal iunss_0 cv funss_1 wcel iunss_0 cv funss_2 wcel wi iunss_0 wal wa iunss_0 cv funss_0 funss_1 cun wcel iunss_0 cv funss_2 wcel wi iunss_0 wal funss_0 funss_2 wss funss_1 funss_2 wss wa iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel wi iunss_0 cv funss_1 wcel iunss_0 cv funss_2 wcel wi iunss_0 19.26 iunss_0 cv funss_0 funss_1 cun wcel iunss_0 cv funss_2 wcel wi iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel wi iunss_0 cv funss_1 wcel iunss_0 cv funss_2 wcel wi wa iunss_0 iunss_0 cv funss_0 funss_1 cun wcel iunss_0 cv funss_2 wcel wi iunss_0 cv funss_0 wcel iunss_0 cv funss_1 wcel wo iunss_0 cv funss_2 wcel wi iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel wi iunss_0 cv funss_1 wcel iunss_0 cv funss_2 wcel wi wa iunss_0 cv funss_0 funss_1 cun wcel iunss_0 cv funss_0 wcel iunss_0 cv funss_1 wcel wo iunss_0 cv funss_2 wcel iunss_0 cv funss_0 funss_1 elun imbi1i iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel iunss_0 cv funss_1 wcel jaob bitri albii funss_0 funss_2 wss iunss_0 cv funss_0 wcel iunss_0 cv funss_2 wcel wi iunss_0 wal funss_1 funss_2 wss iunss_0 cv funss_1 wcel iunss_0 cv funss_2 wcel wi iunss_0 wal iunss_0 funss_0 funss_2 dfss2 iunss_0 funss_1 funss_2 dfss2 anbi12i 3bitr4i bitr2i $.
$}
$( An inference showing the union of two subclasses is a subclass.
       (Contributed by Raph Levien, 10-Dec-2002.) $)
${
	$v A $.
	$v B $.
	$v C $.
	funssi_0 $f class A $.
	funssi_1 $f class B $.
	funssi_2 $f class C $.
	eunssi_0 $e |- A C_ C $.
	eunssi_1 $e |- B C_ C $.
	unssi $p |- ( A u. B ) C_ C $= funssi_0 funssi_2 wss funssi_1 funssi_2 wss wa funssi_0 funssi_1 cun funssi_2 wss funssi_0 funssi_2 wss funssi_1 funssi_2 wss eunssi_0 eunssi_1 pm3.2i funssi_0 funssi_1 funssi_2 unss mpbi $.
$}
$( A deduction showing the union of two subclasses is a subclass.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	funssd_0 $f wff ph $.
	funssd_1 $f class A $.
	funssd_2 $f class B $.
	funssd_3 $f class C $.
	eunssd_0 $e |- ( ph -> A C_ C ) $.
	eunssd_1 $e |- ( ph -> B C_ C ) $.
	unssd $p |- ( ph -> ( A u. B ) C_ C ) $= funssd_0 funssd_1 funssd_3 wss funssd_2 funssd_3 wss funssd_1 funssd_2 cun funssd_3 wss eunssd_0 eunssd_1 funssd_1 funssd_3 wss funssd_2 funssd_3 wss wa funssd_1 funssd_2 cun funssd_3 wss funssd_1 funssd_2 funssd_3 unss biimpi syl2anc $.
$}
$( If ` ( A u. B ) ` is contained in ` C ` , so is ` A ` .  One-way
       deduction form of ~ unss .  Partial converse of ~ unssd .  (Contributed
       by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	funssad_0 $f wff ph $.
	funssad_1 $f class A $.
	funssad_2 $f class B $.
	funssad_3 $f class C $.
	eunssad_0 $e |- ( ph -> ( A u. B ) C_ C ) $.
	unssad $p |- ( ph -> A C_ C ) $= funssad_0 funssad_1 funssad_3 wss funssad_2 funssad_3 wss funssad_0 funssad_1 funssad_2 cun funssad_3 wss funssad_1 funssad_3 wss funssad_2 funssad_3 wss wa eunssad_0 funssad_1 funssad_2 funssad_3 unss sylibr simpld $.
$}
$( If ` ( A u. B ) ` is contained in ` C ` , so is ` B ` .  One-way
       deduction form of ~ unss .  Partial converse of ~ unssd .  (Contributed
       by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	funssbd_0 $f wff ph $.
	funssbd_1 $f class A $.
	funssbd_2 $f class B $.
	funssbd_3 $f class C $.
	eunssbd_0 $e |- ( ph -> ( A u. B ) C_ C ) $.
	unssbd $p |- ( ph -> B C_ C ) $= funssbd_0 funssbd_1 funssbd_3 wss funssbd_2 funssbd_3 wss funssbd_0 funssbd_1 funssbd_2 cun funssbd_3 wss funssbd_1 funssbd_3 wss funssbd_2 funssbd_3 wss wa eunssbd_0 funssbd_1 funssbd_2 funssbd_3 unss sylibr simprd $.
$}
$( A condition that implies inclusion in the union of two classes.
     (Contributed by NM, 23-Nov-2003.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssun_0 $f class A $.
	fssun_1 $f class B $.
	fssun_2 $f class C $.
	ssun $p |- ( ( A C_ B \/ A C_ C ) -> A C_ ( B u. C ) ) $= fssun_0 fssun_1 wss fssun_0 fssun_1 fssun_2 cun wss fssun_0 fssun_2 wss fssun_0 fssun_1 fssun_2 ssun3 fssun_0 fssun_2 fssun_1 ssun4 jaoi $.
$}
$( Restricted existential quantification over union.  (Contributed by Jeff
     Madsen, 5-Jan-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	frexun_0 $f wff ph $.
	frexun_1 $f set x $.
	frexun_2 $f class A $.
	frexun_3 $f class B $.
	rexun $p |- ( E. x e. ( A u. B ) ph <-> ( E. x e. A ph \/ E. x e. B ph ) ) $= frexun_0 frexun_1 frexun_2 frexun_3 cun wrex frexun_1 cv frexun_2 frexun_3 cun wcel frexun_0 wa frexun_1 wex frexun_0 frexun_1 frexun_2 wrex frexun_0 frexun_1 frexun_3 wrex wo frexun_0 frexun_1 frexun_2 frexun_3 cun df-rex frexun_1 cv frexun_2 wcel frexun_0 wa frexun_1 cv frexun_3 wcel frexun_0 wa wo frexun_1 wex frexun_1 cv frexun_2 wcel frexun_0 wa frexun_1 wex frexun_1 cv frexun_3 wcel frexun_0 wa frexun_1 wex wo frexun_1 cv frexun_2 frexun_3 cun wcel frexun_0 wa frexun_1 wex frexun_0 frexun_1 frexun_2 wrex frexun_0 frexun_1 frexun_3 wrex wo frexun_1 cv frexun_2 wcel frexun_0 wa frexun_1 cv frexun_3 wcel frexun_0 wa frexun_1 19.43 frexun_1 cv frexun_2 frexun_3 cun wcel frexun_0 wa frexun_1 cv frexun_2 wcel frexun_0 wa frexun_1 cv frexun_3 wcel frexun_0 wa wo frexun_1 frexun_1 cv frexun_2 frexun_3 cun wcel frexun_0 wa frexun_1 cv frexun_2 wcel frexun_1 cv frexun_3 wcel wo frexun_0 wa frexun_1 cv frexun_2 wcel frexun_0 wa frexun_1 cv frexun_3 wcel frexun_0 wa wo frexun_1 cv frexun_2 frexun_3 cun wcel frexun_1 cv frexun_2 wcel frexun_1 cv frexun_3 wcel wo frexun_0 frexun_1 cv frexun_2 frexun_3 elun anbi1i frexun_1 cv frexun_2 wcel frexun_1 cv frexun_3 wcel frexun_0 andir bitri exbii frexun_0 frexun_1 frexun_2 wrex frexun_1 cv frexun_2 wcel frexun_0 wa frexun_1 wex frexun_0 frexun_1 frexun_3 wrex frexun_1 cv frexun_3 wcel frexun_0 wa frexun_1 wex frexun_0 frexun_1 frexun_2 df-rex frexun_0 frexun_1 frexun_3 df-rex orbi12i 3bitr4i bitri $.
$}
$( Restricted quantification over a union.  (Contributed by Scott Fenton,
     12-Apr-2011.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	fralunb_0 $f wff ph $.
	fralunb_1 $f set x $.
	fralunb_2 $f class A $.
	fralunb_3 $f class B $.
	ralunb $p |- ( A. x e. ( A u. B ) ph <-> ( A. x e. A ph /\ A. x e. B ph ) ) $= fralunb_1 cv fralunb_2 fralunb_3 cun wcel fralunb_0 wi fralunb_1 wal fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 wal fralunb_1 cv fralunb_3 wcel fralunb_0 wi fralunb_1 wal wa fralunb_0 fralunb_1 fralunb_2 fralunb_3 cun wral fralunb_0 fralunb_1 fralunb_2 wral fralunb_0 fralunb_1 fralunb_3 wral wa fralunb_1 cv fralunb_2 fralunb_3 cun wcel fralunb_0 wi fralunb_1 wal fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 cv fralunb_3 wcel fralunb_0 wi wa fralunb_1 wal fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 wal fralunb_1 cv fralunb_3 wcel fralunb_0 wi fralunb_1 wal wa fralunb_1 cv fralunb_2 fralunb_3 cun wcel fralunb_0 wi fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 cv fralunb_3 wcel fralunb_0 wi wa fralunb_1 fralunb_1 cv fralunb_2 fralunb_3 cun wcel fralunb_0 wi fralunb_1 cv fralunb_2 wcel fralunb_1 cv fralunb_3 wcel wo fralunb_0 wi fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 cv fralunb_3 wcel fralunb_0 wi wa fralunb_1 cv fralunb_2 fralunb_3 cun wcel fralunb_1 cv fralunb_2 wcel fralunb_1 cv fralunb_3 wcel wo fralunb_0 fralunb_1 cv fralunb_2 fralunb_3 elun imbi1i fralunb_1 cv fralunb_2 wcel fralunb_0 fralunb_1 cv fralunb_3 wcel jaob bitri albii fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 cv fralunb_3 wcel fralunb_0 wi fralunb_1 19.26 bitri fralunb_0 fralunb_1 fralunb_2 fralunb_3 cun df-ral fralunb_0 fralunb_1 fralunb_2 wral fralunb_1 cv fralunb_2 wcel fralunb_0 wi fralunb_1 wal fralunb_0 fralunb_1 fralunb_3 wral fralunb_1 cv fralunb_3 wcel fralunb_0 wi fralunb_1 wal fralunb_0 fralunb_1 fralunb_2 df-ral fralunb_0 fralunb_1 fralunb_3 df-ral anbi12i 3bitr4i $.
$}
$( Restricted quantification over union.  (Contributed by Jeff Madsen,
     2-Sep-2009.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	fralun_0 $f wff ph $.
	fralun_1 $f set x $.
	fralun_2 $f class A $.
	fralun_3 $f class B $.
	ralun $p |- ( ( A. x e. A ph /\ A. x e. B ph ) -> A. x e. ( A u. B ) ph ) $= fralun_0 fralun_1 fralun_2 fralun_3 cun wral fralun_0 fralun_1 fralun_2 wral fralun_0 fralun_1 fralun_3 wral wa fralun_0 fralun_1 fralun_2 fralun_3 ralunb biimpri $.
$}
$( Expansion of membership in an intersection of two classes.  Theorem 12
       of [Suppes] p. 25.  (Contributed by NM, 29-Apr-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	ielin_0 $f set x $.
	felin_0 $f class A $.
	felin_1 $f class B $.
	felin_2 $f class C $.
	elin $p |- ( A e. ( B i^i C ) <-> ( A e. B /\ A e. C ) ) $= felin_0 felin_1 felin_2 cin wcel felin_0 cvv wcel felin_0 felin_1 wcel felin_0 felin_2 wcel wa felin_0 felin_1 felin_2 cin elex felin_0 felin_2 wcel felin_0 cvv wcel felin_0 felin_1 wcel felin_0 felin_2 elex adantl ielin_0 cv felin_1 wcel ielin_0 cv felin_2 wcel wa felin_0 felin_1 wcel felin_0 felin_2 wcel wa ielin_0 felin_0 felin_1 felin_2 cin cvv ielin_0 cv felin_0 wceq ielin_0 cv felin_1 wcel felin_0 felin_1 wcel ielin_0 cv felin_2 wcel felin_0 felin_2 wcel ielin_0 cv felin_0 felin_1 eleq1 ielin_0 cv felin_0 felin_2 eleq1 anbi12d ielin_0 felin_1 felin_2 df-in elab2g pm5.21nii $.
$}
$( Membership in a class defined as an intersection.  (Contributed by
       Stefan O'Rear, 29-Mar-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v X $.
	felin2_0 $f class A $.
	felin2_1 $f class B $.
	felin2_2 $f class C $.
	felin2_3 $f class X $.
	eelin2_0 $e |- X = ( B i^i C ) $.
	elin2 $p |- ( A e. X <-> ( A e. B /\ A e. C ) ) $= felin2_0 felin2_3 wcel felin2_0 felin2_1 felin2_2 cin wcel felin2_0 felin2_1 wcel felin2_0 felin2_2 wcel wa felin2_3 felin2_1 felin2_2 cin felin2_0 eelin2_0 eleq2i felin2_0 felin2_1 felin2_2 elin bitri $.
$}
$( Membership in a class defined as a ternary intersection.  (Contributed
       by Stefan O'Rear, 29-Mar-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v X $.
	felin3_0 $f class A $.
	felin3_1 $f class B $.
	felin3_2 $f class C $.
	felin3_3 $f class D $.
	felin3_4 $f class X $.
	eelin3_0 $e |- X = ( ( B i^i C ) i^i D ) $.
	elin3 $p |- ( A e. X <-> ( A e. B /\ A e. C /\ A e. D ) ) $= felin3_0 felin3_1 felin3_2 cin wcel felin3_0 felin3_3 wcel wa felin3_0 felin3_1 wcel felin3_0 felin3_2 wcel wa felin3_0 felin3_3 wcel wa felin3_0 felin3_4 wcel felin3_0 felin3_1 wcel felin3_0 felin3_2 wcel felin3_0 felin3_3 wcel w3a felin3_0 felin3_1 felin3_2 cin wcel felin3_0 felin3_1 wcel felin3_0 felin3_2 wcel wa felin3_0 felin3_3 wcel felin3_0 felin3_1 felin3_2 elin anbi1i felin3_0 felin3_1 felin3_2 cin felin3_3 felin3_4 eelin3_0 elin2 felin3_0 felin3_1 wcel felin3_0 felin3_2 wcel felin3_0 felin3_3 wcel df-3an 3bitr4i $.
$}
$( Commutative law for intersection of classes.  Exercise 7 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d A x $.
	$d B x $.
	iincom_0 $f set x $.
	fincom_0 $f class A $.
	fincom_1 $f class B $.
	incom $p |- ( A i^i B ) = ( B i^i A ) $= iincom_0 fincom_0 fincom_1 cin fincom_1 fincom_0 cin iincom_0 cv fincom_0 wcel iincom_0 cv fincom_1 wcel wa iincom_0 cv fincom_1 wcel iincom_0 cv fincom_0 wcel wa iincom_0 cv fincom_0 fincom_1 cin wcel iincom_0 cv fincom_1 fincom_0 cin wcel iincom_0 cv fincom_0 wcel iincom_0 cv fincom_1 wcel ancom iincom_0 cv fincom_0 fincom_1 elin iincom_0 cv fincom_1 fincom_0 elin 3bitr4i eqriv $.
$}
$( Inference from membership to intersection.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	fineqri_0 $f set x $.
	fineqri_1 $f class A $.
	fineqri_2 $f class B $.
	fineqri_3 $f class C $.
	eineqri_0 $e |- ( ( x e. A /\ x e. B ) <-> x e. C ) $.
	ineqri $p |- ( A i^i B ) = C $= fineqri_0 fineqri_1 fineqri_2 cin fineqri_3 fineqri_0 cv fineqri_1 fineqri_2 cin wcel fineqri_0 cv fineqri_1 wcel fineqri_0 cv fineqri_2 wcel wa fineqri_0 cv fineqri_3 wcel fineqri_0 cv fineqri_1 fineqri_2 elin eineqri_0 bitri eqriv $.
$}
$( Equality theorem for intersection of two classes.  (Contributed by NM,
       14-Dec-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iineq1_0 $f set x $.
	fineq1_0 $f class A $.
	fineq1_1 $f class B $.
	fineq1_2 $f class C $.
	ineq1 $p |- ( A = B -> ( A i^i C ) = ( B i^i C ) ) $= fineq1_0 fineq1_1 wceq iineq1_0 fineq1_0 fineq1_2 cin fineq1_1 fineq1_2 cin fineq1_0 fineq1_1 wceq iineq1_0 cv fineq1_0 wcel iineq1_0 cv fineq1_2 wcel wa iineq1_0 cv fineq1_1 wcel iineq1_0 cv fineq1_2 wcel wa iineq1_0 cv fineq1_0 fineq1_2 cin wcel iineq1_0 cv fineq1_1 fineq1_2 cin wcel fineq1_0 fineq1_1 wceq iineq1_0 cv fineq1_0 wcel iineq1_0 cv fineq1_1 wcel iineq1_0 cv fineq1_2 wcel fineq1_0 fineq1_1 iineq1_0 cv eleq2 anbi1d iineq1_0 cv fineq1_0 fineq1_2 elin iineq1_0 cv fineq1_1 fineq1_2 elin 3bitr4g eqrdv $.
$}
$( Equality theorem for intersection of two classes.  (Contributed by NM,
     26-Dec-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fineq2_0 $f class A $.
	fineq2_1 $f class B $.
	fineq2_2 $f class C $.
	ineq2 $p |- ( A = B -> ( C i^i A ) = ( C i^i B ) ) $= fineq2_0 fineq2_1 wceq fineq2_0 fineq2_2 cin fineq2_1 fineq2_2 cin fineq2_2 fineq2_0 cin fineq2_2 fineq2_1 cin fineq2_0 fineq2_1 fineq2_2 ineq1 fineq2_2 fineq2_0 incom fineq2_2 fineq2_1 incom 3eqtr4g $.
$}
$( Equality theorem for intersection of two classes.  (Contributed by NM,
     8-May-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fineq12_0 $f class A $.
	fineq12_1 $f class B $.
	fineq12_2 $f class C $.
	fineq12_3 $f class D $.
	ineq12 $p |- ( ( A = B /\ C = D ) -> ( A i^i C ) = ( B i^i D ) ) $= fineq12_0 fineq12_1 wceq fineq12_2 fineq12_3 wceq fineq12_0 fineq12_2 cin fineq12_1 fineq12_2 cin fineq12_1 fineq12_3 cin fineq12_0 fineq12_1 fineq12_2 ineq1 fineq12_2 fineq12_3 fineq12_1 ineq2 sylan9eq $.
$}
$( Equality inference for intersection of two classes.  (Contributed by NM,
       26-Dec-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fineq1i_0 $f class A $.
	fineq1i_1 $f class B $.
	fineq1i_2 $f class C $.
	eineq1i_0 $e |- A = B $.
	ineq1i $p |- ( A i^i C ) = ( B i^i C ) $= fineq1i_0 fineq1i_1 wceq fineq1i_0 fineq1i_2 cin fineq1i_1 fineq1i_2 cin wceq eineq1i_0 fineq1i_0 fineq1i_1 fineq1i_2 ineq1 ax-mp $.
$}
$( Equality inference for intersection of two classes.  (Contributed by NM,
       26-Dec-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fineq2i_0 $f class A $.
	fineq2i_1 $f class B $.
	fineq2i_2 $f class C $.
	eineq2i_0 $e |- A = B $.
	ineq2i $p |- ( C i^i A ) = ( C i^i B ) $= fineq2i_0 fineq2i_1 wceq fineq2i_2 fineq2i_0 cin fineq2i_2 fineq2i_1 cin wceq eineq2i_0 fineq2i_0 fineq2i_1 fineq2i_2 ineq2 ax-mp $.
$}
$( Equality inference for intersection of two classes.  (Contributed by
         NM, 24-Jun-2004.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fineq12i_0 $f class A $.
	fineq12i_1 $f class B $.
	fineq12i_2 $f class C $.
	fineq12i_3 $f class D $.
	eineq12i_0 $e |- A = B $.
	eineq12i_1 $e |- C = D $.
	ineq12i $p |- ( A i^i C ) = ( B i^i D ) $= fineq12i_0 fineq12i_1 wceq fineq12i_2 fineq12i_3 wceq fineq12i_0 fineq12i_2 cin fineq12i_1 fineq12i_3 cin wceq eineq12i_0 eineq12i_1 fineq12i_0 fineq12i_1 fineq12i_2 fineq12i_3 ineq12 mp2an $.
$}
$( Equality deduction for intersection of two classes.  (Contributed by NM,
       10-Apr-1994.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fineq1d_0 $f wff ph $.
	fineq1d_1 $f class A $.
	fineq1d_2 $f class B $.
	fineq1d_3 $f class C $.
	eineq1d_0 $e |- ( ph -> A = B ) $.
	ineq1d $p |- ( ph -> ( A i^i C ) = ( B i^i C ) ) $= fineq1d_0 fineq1d_1 fineq1d_2 wceq fineq1d_1 fineq1d_3 cin fineq1d_2 fineq1d_3 cin wceq eineq1d_0 fineq1d_1 fineq1d_2 fineq1d_3 ineq1 syl $.
$}
$( Equality deduction for intersection of two classes.  (Contributed by NM,
       10-Apr-1994.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fineq2d_0 $f wff ph $.
	fineq2d_1 $f class A $.
	fineq2d_2 $f class B $.
	fineq2d_3 $f class C $.
	eineq2d_0 $e |- ( ph -> A = B ) $.
	ineq2d $p |- ( ph -> ( C i^i A ) = ( C i^i B ) ) $= fineq2d_0 fineq2d_1 fineq2d_2 wceq fineq2d_3 fineq2d_1 cin fineq2d_3 fineq2d_2 cin wceq eineq2d_0 fineq2d_1 fineq2d_2 fineq2d_3 ineq2 syl $.
$}
$( Equality deduction for intersection of two classes.  (Contributed by
         NM, 24-Jun-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fineq12d_0 $f wff ph $.
	fineq12d_1 $f class A $.
	fineq12d_2 $f class B $.
	fineq12d_3 $f class C $.
	fineq12d_4 $f class D $.
	eineq12d_0 $e |- ( ph -> A = B ) $.
	eineq12d_1 $e |- ( ph -> C = D ) $.
	ineq12d $p |- ( ph -> ( A i^i C ) = ( B i^i D ) ) $= fineq12d_0 fineq12d_1 fineq12d_2 wceq fineq12d_3 fineq12d_4 wceq fineq12d_1 fineq12d_3 cin fineq12d_2 fineq12d_4 cin wceq eineq12d_0 eineq12d_1 fineq12d_1 fineq12d_2 fineq12d_3 fineq12d_4 ineq12 syl2anc $.
$}
$( Equality deduction for intersection of two classes.  (Contributed by
         NM, 7-Feb-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fineqan12d_0 $f wff ph $.
	fineqan12d_1 $f wff ps $.
	fineqan12d_2 $f class A $.
	fineqan12d_3 $f class B $.
	fineqan12d_4 $f class C $.
	fineqan12d_5 $f class D $.
	eineqan12d_0 $e |- ( ph -> A = B ) $.
	eineqan12d_1 $e |- ( ps -> C = D ) $.
	ineqan12d $p |- ( ( ph /\ ps ) -> ( A i^i C ) = ( B i^i D ) ) $= fineqan12d_0 fineqan12d_2 fineqan12d_3 wceq fineqan12d_4 fineqan12d_5 wceq fineqan12d_2 fineqan12d_4 cin fineqan12d_3 fineqan12d_5 cin wceq fineqan12d_1 eineqan12d_0 eineqan12d_1 fineqan12d_2 fineqan12d_3 fineqan12d_4 fineqan12d_5 ineq12 syl2an $.
$}
$( A frequently-used variant of subclass definition ~ df-ss .  (Contributed
     by NM, 10-Jan-2015.) $)
${
	$v A $.
	$v B $.
	fdfss1_0 $f class A $.
	fdfss1_1 $f class B $.
	dfss1 $p |- ( A C_ B <-> ( B i^i A ) = A ) $= fdfss1_0 fdfss1_1 wss fdfss1_0 fdfss1_1 cin fdfss1_0 wceq fdfss1_1 fdfss1_0 cin fdfss1_0 wceq fdfss1_0 fdfss1_1 df-ss fdfss1_0 fdfss1_1 cin fdfss1_1 fdfss1_0 cin fdfss1_0 fdfss1_0 fdfss1_1 incom eqeq1i bitri $.
$}
$( Another definition of subclasshood.  Similar to ~ df-ss , ~ dfss , and
     ~ dfss1 .  (Contributed by David Moews, 1-May-2017.) $)
${
	$v A $.
	$v B $.
	fdfss5_0 $f class A $.
	fdfss5_1 $f class B $.
	dfss5 $p |- ( A C_ B <-> A = ( B i^i A ) ) $= fdfss5_0 fdfss5_1 wss fdfss5_1 fdfss5_0 cin fdfss5_0 wceq fdfss5_0 fdfss5_1 fdfss5_0 cin wceq fdfss5_0 fdfss5_1 dfss1 fdfss5_1 fdfss5_0 cin fdfss5_0 eqcom bitri $.
$}
$( Bound-variable hypothesis builder for the intersection of classes.
       (Contributed by NM, 15-Sep-2003.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$d x y $.
	$d y A $.
	$d y B $.
	infin_0 $f set y $.
	fnfin_0 $f set x $.
	fnfin_1 $f class A $.
	fnfin_2 $f class B $.
	enfin_0 $e |- F/_ x A $.
	enfin_1 $e |- F/_ x B $.
	nfin $p |- F/_ x ( A i^i B ) $= fnfin_0 fnfin_1 fnfin_2 cin infin_0 cv fnfin_2 wcel infin_0 fnfin_1 crab infin_0 fnfin_1 fnfin_2 dfin5 infin_0 cv fnfin_2 wcel fnfin_0 infin_0 fnfin_1 fnfin_0 infin_0 fnfin_2 enfin_1 nfcri enfin_0 nfrab nfcxfr $.
$}
$( Distribute proper substitution through an intersection relation.
       (Contributed by Alan Sare, 22-Jul-2012.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d A y $.
	$d C y $.
	$d D y $.
	$d x y $.
	icsbing_0 $f set y $.
	fcsbing_0 $f set x $.
	fcsbing_1 $f class A $.
	fcsbing_2 $f class B $.
	fcsbing_3 $f class C $.
	fcsbing_4 $f class D $.
	csbing $p |- ( A e. B -> [_ A / x ]_ ( C i^i D ) = ( [_ A / x ]_ C i^i [_ A / x ]_ D ) ) $= fcsbing_0 icsbing_0 cv fcsbing_3 fcsbing_4 cin csb fcsbing_0 icsbing_0 cv fcsbing_3 csb fcsbing_0 icsbing_0 cv fcsbing_4 csb cin wceq fcsbing_0 fcsbing_1 fcsbing_3 fcsbing_4 cin csb fcsbing_0 fcsbing_1 fcsbing_3 csb fcsbing_0 fcsbing_1 fcsbing_4 csb cin wceq icsbing_0 fcsbing_1 fcsbing_2 icsbing_0 cv fcsbing_1 wceq fcsbing_0 icsbing_0 cv fcsbing_3 fcsbing_4 cin csb fcsbing_0 fcsbing_1 fcsbing_3 fcsbing_4 cin csb fcsbing_0 icsbing_0 cv fcsbing_3 csb fcsbing_0 icsbing_0 cv fcsbing_4 csb cin fcsbing_0 fcsbing_1 fcsbing_3 csb fcsbing_0 fcsbing_1 fcsbing_4 csb cin fcsbing_0 icsbing_0 cv fcsbing_1 fcsbing_3 fcsbing_4 cin csbeq1 icsbing_0 cv fcsbing_1 wceq fcsbing_0 icsbing_0 cv fcsbing_3 csb fcsbing_0 fcsbing_1 fcsbing_3 csb fcsbing_0 icsbing_0 cv fcsbing_4 csb fcsbing_0 fcsbing_1 fcsbing_4 csb fcsbing_0 icsbing_0 cv fcsbing_1 fcsbing_3 csbeq1 fcsbing_0 icsbing_0 cv fcsbing_1 fcsbing_4 csbeq1 ineq12d eqeq12d fcsbing_0 icsbing_0 cv fcsbing_3 fcsbing_4 cin fcsbing_0 icsbing_0 cv fcsbing_3 csb fcsbing_0 icsbing_0 cv fcsbing_4 csb cin icsbing_0 vex fcsbing_0 fcsbing_0 icsbing_0 cv fcsbing_3 csb fcsbing_0 icsbing_0 cv fcsbing_4 csb fcsbing_0 icsbing_0 cv fcsbing_3 nfcsb1v fcsbing_0 icsbing_0 cv fcsbing_4 nfcsb1v nfin fcsbing_0 cv icsbing_0 cv wceq fcsbing_3 fcsbing_0 icsbing_0 cv fcsbing_3 csb fcsbing_4 fcsbing_0 icsbing_0 cv fcsbing_4 csb fcsbing_0 icsbing_0 cv fcsbing_3 csbeq1a fcsbing_0 icsbing_0 cv fcsbing_4 csbeq1a ineq12d csbief vtoclg $.
$}
$( Deduction from a wff to a restricted class abstraction.  (Contributed by
       NM, 14-Jan-2014.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x ph $.
	$d x A $.
	$d x B $.
	frabbi2dva_0 $f wff ph $.
	frabbi2dva_1 $f wff ps $.
	frabbi2dva_2 $f set x $.
	frabbi2dva_3 $f class A $.
	frabbi2dva_4 $f class B $.
	erabbi2dva_0 $e |- ( ( ph /\ x e. A ) -> ( x e. B <-> ps ) ) $.
	rabbi2dva $p |- ( ph -> ( A i^i B ) = { x e. A | ps } ) $= frabbi2dva_0 frabbi2dva_3 frabbi2dva_4 cin frabbi2dva_2 cv frabbi2dva_4 wcel frabbi2dva_2 frabbi2dva_3 crab frabbi2dva_1 frabbi2dva_2 frabbi2dva_3 crab frabbi2dva_2 frabbi2dva_3 frabbi2dva_4 dfin5 frabbi2dva_0 frabbi2dva_2 cv frabbi2dva_4 wcel frabbi2dva_1 frabbi2dva_2 frabbi2dva_3 erabbi2dva_0 rabbidva syl5eq $.
$}
$( Idempotent law for intersection of classes.  Theorem 15 of [Suppes]
       p. 26.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$d x A $.
	iinidm_0 $f set x $.
	finidm_0 $f class A $.
	inidm $p |- ( A i^i A ) = A $= iinidm_0 finidm_0 finidm_0 finidm_0 iinidm_0 cv finidm_0 wcel anidm ineqri $.
$}
$( Associative law for intersection of classes.  Exercise 9 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 3-May-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d A x $.
	$d B x $.
	$d C x $.
	iinass_0 $f set x $.
	finass_0 $f class A $.
	finass_1 $f class B $.
	finass_2 $f class C $.
	inass $p |- ( ( A i^i B ) i^i C ) = ( A i^i ( B i^i C ) ) $= iinass_0 finass_0 finass_1 cin finass_2 finass_0 finass_1 finass_2 cin cin iinass_0 cv finass_0 wcel iinass_0 cv finass_1 wcel wa iinass_0 cv finass_2 wcel wa iinass_0 cv finass_0 wcel iinass_0 cv finass_1 finass_2 cin wcel wa iinass_0 cv finass_0 finass_1 cin wcel iinass_0 cv finass_2 wcel wa iinass_0 cv finass_0 finass_1 finass_2 cin cin wcel iinass_0 cv finass_0 wcel iinass_0 cv finass_1 wcel wa iinass_0 cv finass_2 wcel wa iinass_0 cv finass_0 wcel iinass_0 cv finass_1 wcel iinass_0 cv finass_2 wcel wa wa iinass_0 cv finass_0 wcel iinass_0 cv finass_1 finass_2 cin wcel wa iinass_0 cv finass_0 wcel iinass_0 cv finass_1 wcel iinass_0 cv finass_2 wcel anass iinass_0 cv finass_1 finass_2 cin wcel iinass_0 cv finass_1 wcel iinass_0 cv finass_2 wcel wa iinass_0 cv finass_0 wcel iinass_0 cv finass_1 finass_2 elin anbi2i bitr4i iinass_0 cv finass_0 finass_1 cin wcel iinass_0 cv finass_0 wcel iinass_0 cv finass_1 wcel wa iinass_0 cv finass_2 wcel iinass_0 cv finass_0 finass_1 elin anbi1i iinass_0 cv finass_0 finass_1 finass_2 cin elin 3bitr4i ineqri $.
$}
$( A rearrangement of intersection.  (Contributed by NM, 21-Apr-2001.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fin12_0 $f class A $.
	fin12_1 $f class B $.
	fin12_2 $f class C $.
	in12 $p |- ( A i^i ( B i^i C ) ) = ( B i^i ( A i^i C ) ) $= fin12_0 fin12_1 cin fin12_2 cin fin12_1 fin12_0 cin fin12_2 cin fin12_0 fin12_1 fin12_2 cin cin fin12_1 fin12_0 fin12_2 cin cin fin12_0 fin12_1 cin fin12_1 fin12_0 cin fin12_2 fin12_0 fin12_1 incom ineq1i fin12_0 fin12_1 fin12_2 inass fin12_1 fin12_0 fin12_2 inass 3eqtr3i $.
$}
$( A rearrangement of intersection.  (Contributed by NM, 21-Apr-2001.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fin32_0 $f class A $.
	fin32_1 $f class B $.
	fin32_2 $f class C $.
	in32 $p |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i B ) $= fin32_0 fin32_1 cin fin32_2 cin fin32_0 fin32_1 fin32_2 cin cin fin32_1 fin32_0 fin32_2 cin cin fin32_0 fin32_2 cin fin32_1 cin fin32_0 fin32_1 fin32_2 inass fin32_0 fin32_1 fin32_2 in12 fin32_1 fin32_0 fin32_2 cin incom 3eqtri $.
$}
$( A rearrangement of intersection.  (Contributed by NM, 27-Aug-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fin13_0 $f class A $.
	fin13_1 $f class B $.
	fin13_2 $f class C $.
	in13 $p |- ( A i^i ( B i^i C ) ) = ( C i^i ( B i^i A ) ) $= fin13_1 fin13_2 cin fin13_0 cin fin13_1 fin13_0 cin fin13_2 cin fin13_0 fin13_1 fin13_2 cin cin fin13_2 fin13_1 fin13_0 cin cin fin13_1 fin13_2 fin13_0 in32 fin13_0 fin13_1 fin13_2 cin incom fin13_2 fin13_1 fin13_0 cin incom 3eqtr4i $.
$}
$( A rearrangement of intersection.  (Contributed by NM, 27-Aug-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fin31_0 $f class A $.
	fin31_1 $f class B $.
	fin31_2 $f class C $.
	in31 $p |- ( ( A i^i B ) i^i C ) = ( ( C i^i B ) i^i A ) $= fin31_2 fin31_0 fin31_1 cin cin fin31_0 fin31_2 fin31_1 cin cin fin31_0 fin31_1 cin fin31_2 cin fin31_2 fin31_1 cin fin31_0 cin fin31_2 fin31_0 fin31_1 in12 fin31_0 fin31_1 cin fin31_2 incom fin31_2 fin31_1 cin fin31_0 incom 3eqtr4i $.
$}
$( Rotate the intersection of 3 classes.  (Contributed by NM,
     27-Aug-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	finrot_0 $f class A $.
	finrot_1 $f class B $.
	finrot_2 $f class C $.
	inrot $p |- ( ( A i^i B ) i^i C ) = ( ( C i^i A ) i^i B ) $= finrot_0 finrot_1 cin finrot_2 cin finrot_2 finrot_1 cin finrot_0 cin finrot_2 finrot_0 cin finrot_1 cin finrot_0 finrot_1 finrot_2 in31 finrot_2 finrot_1 finrot_0 in32 eqtri $.
$}
$( Rearrangement of intersection of 4 classes.  (Contributed by NM,
     21-Apr-2001.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fin4_0 $f class A $.
	fin4_1 $f class B $.
	fin4_2 $f class C $.
	fin4_3 $f class D $.
	in4 $p |- ( ( A i^i B ) i^i ( C i^i D ) ) = ( ( A i^i C ) i^i ( B i^i D ) ) $= fin4_0 fin4_1 fin4_2 fin4_3 cin cin cin fin4_0 fin4_2 fin4_1 fin4_3 cin cin cin fin4_0 fin4_1 cin fin4_2 fin4_3 cin cin fin4_0 fin4_2 cin fin4_1 fin4_3 cin cin fin4_1 fin4_2 fin4_3 cin cin fin4_2 fin4_1 fin4_3 cin cin fin4_0 fin4_1 fin4_2 fin4_3 in12 ineq2i fin4_0 fin4_1 fin4_2 fin4_3 cin inass fin4_0 fin4_2 fin4_1 fin4_3 cin inass 3eqtr4i $.
$}
$( Intersection distributes over itself.  (Contributed by NM, 6-May-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	finindi_0 $f class A $.
	finindi_1 $f class B $.
	finindi_2 $f class C $.
	inindi $p |- ( A i^i ( B i^i C ) ) = ( ( A i^i B ) i^i ( A i^i C ) ) $= finindi_0 finindi_0 cin finindi_1 finindi_2 cin cin finindi_0 finindi_1 finindi_2 cin cin finindi_0 finindi_1 cin finindi_0 finindi_2 cin cin finindi_0 finindi_0 cin finindi_0 finindi_1 finindi_2 cin finindi_0 inidm ineq1i finindi_0 finindi_0 finindi_1 finindi_2 in4 eqtr3i $.
$}
$( Intersection distributes over itself.  (Contributed by NM,
     17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	finindir_0 $f class A $.
	finindir_1 $f class B $.
	finindir_2 $f class C $.
	inindir $p |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i ( B i^i C ) ) $= finindir_0 finindir_1 cin finindir_2 finindir_2 cin cin finindir_0 finindir_1 cin finindir_2 cin finindir_0 finindir_2 cin finindir_1 finindir_2 cin cin finindir_2 finindir_2 cin finindir_2 finindir_0 finindir_1 cin finindir_2 inidm ineq2i finindir_0 finindir_1 finindir_2 finindir_2 in4 eqtr3i $.
$}
$( A relationship between subclass and intersection.  Similar to Exercise 9
     of [TakeutiZaring] p. 18.  (Contributed by NM, 17-May-1994.) $)
${
	$v A $.
	$v B $.
	fsseqin2_0 $f class A $.
	fsseqin2_1 $f class B $.
	sseqin2 $p |- ( A C_ B <-> ( B i^i A ) = A ) $= fsseqin2_0 fsseqin2_1 dfss1 $.
$}
$( The intersection of two classes is a subset of one of them.  Part of
       Exercise 12 of [TakeutiZaring] p. 18.  (Contributed by NM,
       27-Apr-1994.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	iinss1_0 $f set x $.
	finss1_0 $f class A $.
	finss1_1 $f class B $.
	inss1 $p |- ( A i^i B ) C_ A $= iinss1_0 finss1_0 finss1_1 cin finss1_0 iinss1_0 cv finss1_0 finss1_1 cin wcel iinss1_0 cv finss1_0 wcel iinss1_0 cv finss1_1 wcel iinss1_0 cv finss1_0 finss1_1 elin simplbi ssriv $.
$}
$( The intersection of two classes is a subset of one of them.  Part of
     Exercise 12 of [TakeutiZaring] p. 18.  (Contributed by NM,
     27-Apr-1994.) $)
${
	$v A $.
	$v B $.
	finss2_0 $f class A $.
	finss2_1 $f class B $.
	inss2 $p |- ( A i^i B ) C_ B $= finss2_0 finss2_1 cin finss2_1 finss2_0 cin finss2_1 finss2_1 finss2_0 incom finss2_1 finss2_0 inss1 eqsstr3i $.
$}
$( Subclass of intersection.  Theorem 2.8(vii) of [Monk1] p. 26.
       (Contributed by NM, 15-Jun-2004.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	issin_0 $f set x $.
	fssin_0 $f class A $.
	fssin_1 $f class B $.
	fssin_2 $f class C $.
	ssin $p |- ( ( A C_ B /\ A C_ C ) <-> A C_ ( B i^i C ) ) $= issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel wi issin_0 wal issin_0 cv fssin_0 wcel issin_0 cv fssin_2 wcel wi issin_0 wal wa issin_0 cv fssin_0 wcel issin_0 cv fssin_1 fssin_2 cin wcel wi issin_0 wal fssin_0 fssin_1 wss fssin_0 fssin_2 wss wa fssin_0 fssin_1 fssin_2 cin wss issin_0 cv fssin_0 wcel issin_0 cv fssin_1 fssin_2 cin wcel wi issin_0 wal issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel issin_0 cv fssin_2 wcel wa wi issin_0 wal issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel wi issin_0 cv fssin_0 wcel issin_0 cv fssin_2 wcel wi wa issin_0 wal issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel wi issin_0 wal issin_0 cv fssin_0 wcel issin_0 cv fssin_2 wcel wi issin_0 wal wa issin_0 cv fssin_0 wcel issin_0 cv fssin_1 fssin_2 cin wcel wi issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel issin_0 cv fssin_2 wcel wa wi issin_0 issin_0 cv fssin_1 fssin_2 cin wcel issin_0 cv fssin_1 wcel issin_0 cv fssin_2 wcel wa issin_0 cv fssin_0 wcel issin_0 cv fssin_1 fssin_2 elin imbi2i albii issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel issin_0 cv fssin_2 wcel wa wi issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel wi issin_0 cv fssin_0 wcel issin_0 cv fssin_2 wcel wi wa issin_0 issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel issin_0 cv fssin_2 wcel jcab albii issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel wi issin_0 cv fssin_0 wcel issin_0 cv fssin_2 wcel wi issin_0 19.26 3bitrri fssin_0 fssin_1 wss issin_0 cv fssin_0 wcel issin_0 cv fssin_1 wcel wi issin_0 wal fssin_0 fssin_2 wss issin_0 cv fssin_0 wcel issin_0 cv fssin_2 wcel wi issin_0 wal issin_0 fssin_0 fssin_1 dfss2 issin_0 fssin_0 fssin_2 dfss2 anbi12i issin_0 fssin_0 fssin_1 fssin_2 cin dfss2 3bitr4i $.
$}
$( An inference showing that a subclass of two classes is a subclass of
       their intersection.  (Contributed by NM, 24-Nov-2003.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssini_0 $f class A $.
	fssini_1 $f class B $.
	fssini_2 $f class C $.
	essini_0 $e |- A C_ B $.
	essini_1 $e |- A C_ C $.
	ssini $p |- A C_ ( B i^i C ) $= fssini_0 fssini_1 wss fssini_0 fssini_2 wss wa fssini_0 fssini_1 fssini_2 cin wss fssini_0 fssini_1 wss fssini_0 fssini_2 wss essini_0 essini_1 pm3.2i fssini_0 fssini_1 fssini_2 ssin mpbi $.
$}
$( A deduction showing that a subclass of two classes is a subclass of
       their intersection.  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fssind_0 $f wff ph $.
	fssind_1 $f class A $.
	fssind_2 $f class B $.
	fssind_3 $f class C $.
	essind_0 $e |- ( ph -> A C_ B ) $.
	essind_1 $e |- ( ph -> A C_ C ) $.
	ssind $p |- ( ph -> A C_ ( B i^i C ) ) $= fssind_0 fssind_1 fssind_2 wss fssind_1 fssind_3 wss fssind_1 fssind_2 fssind_3 cin wss essind_0 essind_1 fssind_1 fssind_2 wss fssind_1 fssind_3 wss wa fssind_1 fssind_2 fssind_3 cin wss fssind_1 fssind_2 fssind_3 ssin biimpi syl2anc $.
$}
$( Add right intersection to subclass relation.  (Contributed by NM,
       16-Aug-1994.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	issrin_0 $f set x $.
	fssrin_0 $f class A $.
	fssrin_1 $f class B $.
	fssrin_2 $f class C $.
	ssrin $p |- ( A C_ B -> ( A i^i C ) C_ ( B i^i C ) ) $= fssrin_0 fssrin_1 wss issrin_0 fssrin_0 fssrin_2 cin fssrin_1 fssrin_2 cin fssrin_0 fssrin_1 wss issrin_0 cv fssrin_0 wcel issrin_0 cv fssrin_2 wcel wa issrin_0 cv fssrin_1 wcel issrin_0 cv fssrin_2 wcel wa issrin_0 cv fssrin_0 fssrin_2 cin wcel issrin_0 cv fssrin_1 fssrin_2 cin wcel fssrin_0 fssrin_1 wss issrin_0 cv fssrin_0 wcel issrin_0 cv fssrin_1 wcel issrin_0 cv fssrin_2 wcel fssrin_0 fssrin_1 issrin_0 cv ssel anim1d issrin_0 cv fssrin_0 fssrin_2 elin issrin_0 cv fssrin_1 fssrin_2 elin 3imtr4g ssrdv $.
$}
$( Add left intersection to subclass relation.  (Contributed by NM,
       19-Oct-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsslin_0 $f class A $.
	fsslin_1 $f class B $.
	fsslin_2 $f class C $.
	sslin $p |- ( A C_ B -> ( C i^i A ) C_ ( C i^i B ) ) $= fsslin_0 fsslin_1 wss fsslin_0 fsslin_2 cin fsslin_1 fsslin_2 cin fsslin_2 fsslin_0 cin fsslin_2 fsslin_1 cin fsslin_0 fsslin_1 fsslin_2 ssrin fsslin_2 fsslin_0 incom fsslin_2 fsslin_1 incom 3sstr4g $.
$}
$( Intersection of subclasses.  (Contributed by NM, 5-May-2000.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fss2in_0 $f class A $.
	fss2in_1 $f class B $.
	fss2in_2 $f class C $.
	fss2in_3 $f class D $.
	ss2in $p |- ( ( A C_ B /\ C C_ D ) -> ( A i^i C ) C_ ( B i^i D ) ) $= fss2in_0 fss2in_1 wss fss2in_2 fss2in_3 wss fss2in_0 fss2in_2 cin fss2in_1 fss2in_2 cin fss2in_1 fss2in_3 cin fss2in_0 fss2in_1 fss2in_2 ssrin fss2in_2 fss2in_3 fss2in_1 sslin sylan9ss $.
$}
$( Intersection preserves subclass relationship.  (Contributed by NM,
     14-Sep-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssinss1_0 $f class A $.
	fssinss1_1 $f class B $.
	fssinss1_2 $f class C $.
	ssinss1 $p |- ( A C_ C -> ( A i^i B ) C_ C ) $= fssinss1_0 fssinss1_1 cin fssinss1_0 wss fssinss1_0 fssinss1_2 wss fssinss1_0 fssinss1_1 cin fssinss1_2 wss wi fssinss1_0 fssinss1_1 inss1 fssinss1_0 fssinss1_1 cin fssinss1_0 fssinss1_2 sstr2 ax-mp $.
$}
$( Inclusion of an intersection of two classes.  (Contributed by NM,
     30-Oct-2014.) $)
${
	$v A $.
	$v B $.
	$v C $.
	finss_0 $f class A $.
	finss_1 $f class B $.
	finss_2 $f class C $.
	inss $p |- ( ( A C_ C \/ B C_ C ) -> ( A i^i B ) C_ C ) $= finss_0 finss_2 wss finss_0 finss_1 cin finss_2 wss finss_1 finss_2 wss finss_0 finss_1 finss_2 ssinss1 finss_1 finss_2 wss finss_0 finss_1 cin finss_1 finss_0 cin finss_2 finss_0 finss_1 incom finss_1 finss_0 finss_2 ssinss1 syl5eqss jaoi $.
$}
$( Absorption law for union.  (Contributed by NM, 16-Apr-2006.) $)
${
	$v A $.
	$v B $.
	funabs_0 $f class A $.
	funabs_1 $f class B $.
	unabs $p |- ( A u. ( A i^i B ) ) = A $= funabs_0 funabs_1 cin funabs_0 wss funabs_0 funabs_0 funabs_1 cin cun funabs_0 wceq funabs_0 funabs_1 inss1 funabs_0 funabs_1 cin funabs_0 ssequn2 mpbi $.
$}
$( Absorption law for intersection.  (Contributed by NM, 16-Apr-2006.) $)
${
	$v A $.
	$v B $.
	finabs_0 $f class A $.
	finabs_1 $f class B $.
	inabs $p |- ( A i^i ( A u. B ) ) = A $= finabs_0 finabs_0 finabs_1 cun wss finabs_0 finabs_0 finabs_1 cun cin finabs_0 wceq finabs_0 finabs_1 ssun1 finabs_0 finabs_0 finabs_1 cun df-ss mpbi $.
$}
$( Negation of subclass expressed in terms of intersection and proper
     subclass.  (Contributed by NM, 30-Jun-2004.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	fnssinpss_0 $f class A $.
	fnssinpss_1 $f class B $.
	nssinpss $p |- ( -. A C_ B <-> ( A i^i B ) C. A ) $= fnssinpss_0 fnssinpss_1 cin fnssinpss_0 wne fnssinpss_0 fnssinpss_1 cin fnssinpss_0 wss fnssinpss_0 fnssinpss_1 cin fnssinpss_0 wne wa fnssinpss_0 fnssinpss_1 wss wn fnssinpss_0 fnssinpss_1 cin fnssinpss_0 wpss fnssinpss_0 fnssinpss_1 cin fnssinpss_0 wss fnssinpss_0 fnssinpss_1 cin fnssinpss_0 wne fnssinpss_0 fnssinpss_1 inss1 biantrur fnssinpss_0 fnssinpss_1 wss fnssinpss_0 fnssinpss_1 cin fnssinpss_0 fnssinpss_0 fnssinpss_1 df-ss necon3bbii fnssinpss_0 fnssinpss_1 cin fnssinpss_0 df-pss 3bitr4i $.
$}
$( Negation of subclass expressed in terms of proper subclass and union.
     (Contributed by NM, 15-Sep-2004.) $)
${
	$v A $.
	$v B $.
	fnsspssun_0 $f class A $.
	fnsspssun_1 $f class B $.
	nsspssun $p |- ( -. A C_ B <-> B C. ( A u. B ) ) $= fnsspssun_0 fnsspssun_1 wss wn fnsspssun_1 fnsspssun_0 fnsspssun_1 cun wss fnsspssun_0 fnsspssun_1 cun fnsspssun_1 wss wn wa fnsspssun_1 fnsspssun_0 fnsspssun_1 cun wpss fnsspssun_0 fnsspssun_1 cun fnsspssun_1 wss fnsspssun_1 fnsspssun_0 fnsspssun_1 cun wss fnsspssun_0 fnsspssun_1 cun fnsspssun_1 wss wn wa fnsspssun_0 fnsspssun_1 wss fnsspssun_1 fnsspssun_0 fnsspssun_1 cun wss fnsspssun_0 fnsspssun_1 cun fnsspssun_1 wss wn fnsspssun_1 fnsspssun_0 ssun2 biantrur fnsspssun_0 fnsspssun_1 wss fnsspssun_0 fnsspssun_1 wss fnsspssun_1 fnsspssun_1 wss wa fnsspssun_0 fnsspssun_1 cun fnsspssun_1 wss fnsspssun_1 fnsspssun_1 wss fnsspssun_0 fnsspssun_1 wss fnsspssun_1 ssid biantru fnsspssun_0 fnsspssun_1 fnsspssun_1 unss bitri xchnxbir fnsspssun_1 fnsspssun_0 fnsspssun_1 cun dfpss3 bitr4i $.
$}
$( Subclass defined in terms of class difference.  See comments under
       ~ dfun2 .  (Contributed by NM, 22-Mar-1998.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	idfss4_0 $f set x $.
	fdfss4_0 $f class A $.
	fdfss4_1 $f class B $.
	dfss4 $p |- ( A C_ B <-> ( B \ ( B \ A ) ) = A ) $= fdfss4_0 fdfss4_1 wss fdfss4_1 fdfss4_0 cin fdfss4_0 wceq fdfss4_1 fdfss4_1 fdfss4_0 cdif cdif fdfss4_0 wceq fdfss4_0 fdfss4_1 sseqin2 fdfss4_1 fdfss4_1 fdfss4_0 cdif cdif fdfss4_1 fdfss4_0 cin fdfss4_0 idfss4_0 fdfss4_1 fdfss4_1 fdfss4_0 cdif fdfss4_1 fdfss4_0 cin idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_1 fdfss4_0 cdif wcel wn wa idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wn wa wn wa idfss4_0 cv fdfss4_1 fdfss4_0 cin wcel idfss4_0 cv fdfss4_1 fdfss4_0 cdif wcel wn idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wn wa wn idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_1 fdfss4_0 cdif wcel idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wn wa idfss4_0 cv fdfss4_1 fdfss4_0 eldif notbii anbi2i idfss4_0 cv fdfss4_1 fdfss4_0 cin wcel idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wa idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wi wa idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wn wa wn wa idfss4_0 cv fdfss4_1 fdfss4_0 elin idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel abai idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wi idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel wn wa wn idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_1 wcel idfss4_0 cv fdfss4_0 wcel iman anbi2i 3bitri bitr4i difeqri eqeq1i bitr4i $.
$}
$( An alternate definition of the union of two classes in terms of class
       difference, requiring no dummy variables.  Along with ~ dfin2 and
       ~ dfss4 it shows we can express union, intersection, and subset directly
       in terms of the single "primitive" operation ` \ ` (class difference).
       (Contributed by NM, 10-Jun-2004.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	idfun2_0 $f set x $.
	fdfun2_0 $f class A $.
	fdfun2_1 $f class B $.
	dfun2 $p |- ( A u. B ) = ( _V \ ( ( _V \ A ) \ B ) ) $= idfun2_0 fdfun2_0 fdfun2_1 cvv cvv fdfun2_0 cdif fdfun2_1 cdif cdif idfun2_0 cv fdfun2_0 wcel idfun2_0 cv fdfun2_1 wcel wo idfun2_0 cv cvv fdfun2_0 cdif fdfun2_1 cdif wcel wn idfun2_0 cv cvv cvv fdfun2_0 cdif fdfun2_1 cdif cdif wcel idfun2_0 cv cvv fdfun2_0 cdif fdfun2_1 cdif wcel idfun2_0 cv fdfun2_0 wcel idfun2_0 cv fdfun2_1 wcel wo idfun2_0 cv cvv fdfun2_0 cdif wcel idfun2_0 cv fdfun2_1 wcel wn wa idfun2_0 cv fdfun2_0 wcel wn idfun2_0 cv fdfun2_1 wcel wn wa idfun2_0 cv cvv fdfun2_0 cdif fdfun2_1 cdif wcel idfun2_0 cv fdfun2_0 wcel idfun2_0 cv fdfun2_1 wcel wo wn idfun2_0 cv cvv fdfun2_0 cdif wcel idfun2_0 cv fdfun2_0 wcel wn idfun2_0 cv fdfun2_1 wcel wn idfun2_0 cv cvv fdfun2_0 cdif wcel idfun2_0 cv cvv wcel idfun2_0 cv fdfun2_0 wcel wn idfun2_0 vex idfun2_0 cv cvv fdfun2_0 eldif mpbiran anbi1i idfun2_0 cv cvv fdfun2_0 cdif fdfun2_1 eldif idfun2_0 cv fdfun2_0 wcel idfun2_0 cv fdfun2_1 wcel ioran 3bitr4i con2bii idfun2_0 cv cvv cvv fdfun2_0 cdif fdfun2_1 cdif cdif wcel idfun2_0 cv cvv wcel idfun2_0 cv cvv fdfun2_0 cdif fdfun2_1 cdif wcel wn idfun2_0 vex idfun2_0 cv cvv cvv fdfun2_0 cdif fdfun2_1 cdif eldif mpbiran bitr4i uneqri $.
$}
$( An alternate definition of the intersection of two classes in terms of
       class difference, requiring no dummy variables.  See comments under
       ~ dfun2 .  Another version is given by ~ dfin4 .  (Contributed by NM,
       10-Jun-2004.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	idfin2_0 $f set x $.
	fdfin2_0 $f class A $.
	fdfin2_1 $f class B $.
	dfin2 $p |- ( A i^i B ) = ( A \ ( _V \ B ) ) $= idfin2_0 fdfin2_0 fdfin2_1 fdfin2_0 cvv fdfin2_1 cdif cdif idfin2_0 cv fdfin2_0 wcel idfin2_0 cv fdfin2_1 wcel wa idfin2_0 cv fdfin2_0 wcel idfin2_0 cv cvv fdfin2_1 cdif wcel wn wa idfin2_0 cv fdfin2_0 cvv fdfin2_1 cdif cdif wcel idfin2_0 cv fdfin2_1 wcel idfin2_0 cv cvv fdfin2_1 cdif wcel wn idfin2_0 cv fdfin2_0 wcel idfin2_0 cv cvv fdfin2_1 cdif wcel idfin2_0 cv fdfin2_1 wcel idfin2_0 cv cvv fdfin2_1 cdif wcel idfin2_0 cv cvv wcel idfin2_0 cv fdfin2_1 wcel wn idfin2_0 vex idfin2_0 cv cvv fdfin2_1 eldif mpbiran con2bii anbi2i idfin2_0 cv fdfin2_0 cvv fdfin2_1 cdif eldif bitr4i ineqri $.
$}
$( Difference with intersection.  Theorem 33 of [Suppes] p. 29.
       (Contributed by NM, 31-Mar-1998.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	idifin_0 $f set x $.
	fdifin_0 $f class A $.
	fdifin_1 $f class B $.
	difin $p |- ( A \ ( A i^i B ) ) = ( A \ B ) $= idifin_0 fdifin_0 fdifin_0 fdifin_1 cin fdifin_0 fdifin_1 cdif idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel wi wn idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel wn wa idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 fdifin_1 cin wcel wn wa idifin_0 cv fdifin_0 fdifin_1 cdif wcel idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel pm4.61 idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel wi idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 fdifin_1 cin wcel wn wa idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel wi idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel wa wi idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 fdifin_1 cin wcel wi idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 fdifin_1 cin wcel wn wa wn idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel anclb idifin_0 cv fdifin_0 fdifin_1 cin wcel idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_1 wcel wa idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 fdifin_1 elin imbi2i idifin_0 cv fdifin_0 wcel idifin_0 cv fdifin_0 fdifin_1 cin wcel iman 3bitr2i con2bii idifin_0 cv fdifin_0 fdifin_1 eldif 3bitr4i difeqri $.
$}
$( Union defined in terms of intersection (De Morgan's law).  Definition of
     union in [Mendelson] p. 231.  (Contributed by NM, 8-Jan-2002.) $)
${
	$v A $.
	$v B $.
	fdfun3_0 $f class A $.
	fdfun3_1 $f class B $.
	dfun3 $p |- ( A u. B ) = ( _V \ ( ( _V \ A ) i^i ( _V \ B ) ) ) $= fdfun3_0 fdfun3_1 cun cvv cvv fdfun3_0 cdif fdfun3_1 cdif cdif cvv cvv fdfun3_0 cdif cvv fdfun3_1 cdif cin cdif fdfun3_0 fdfun3_1 dfun2 cvv fdfun3_0 cdif fdfun3_1 cdif cvv fdfun3_0 cdif cvv fdfun3_1 cdif cin cvv cvv fdfun3_0 cdif cvv fdfun3_1 cdif cin cvv fdfun3_0 cdif cvv cvv fdfun3_1 cdif cdif cdif cvv fdfun3_0 cdif fdfun3_1 cdif cvv fdfun3_0 cdif cvv fdfun3_1 cdif dfin2 cvv cvv fdfun3_1 cdif cdif fdfun3_1 cvv fdfun3_0 cdif fdfun3_1 ddif difeq2i eqtr2i difeq2i eqtri $.
$}
$( Intersection defined in terms of union (De Morgan's law.  Similar to
     Exercise 4.10(n) of [Mendelson] p. 231.  (Contributed by NM,
     8-Jan-2002.) $)
${
	$v A $.
	$v B $.
	fdfin3_0 $f class A $.
	fdfin3_1 $f class B $.
	dfin3 $p |- ( A i^i B ) = ( _V \ ( ( _V \ A ) u. ( _V \ B ) ) ) $= cvv cvv fdfin3_0 cvv fdfin3_1 cdif cdif cdif cdif fdfin3_0 cvv fdfin3_1 cdif cdif cvv cvv fdfin3_0 cdif cvv fdfin3_1 cdif cun cdif fdfin3_0 fdfin3_1 cin fdfin3_0 cvv fdfin3_1 cdif cdif ddif cvv fdfin3_0 cdif cvv fdfin3_1 cdif cun cvv fdfin3_0 cvv fdfin3_1 cdif cdif cdif cvv cvv fdfin3_0 cdif cvv fdfin3_1 cdif cun cvv cvv cvv fdfin3_0 cdif cdif cvv fdfin3_1 cdif cdif cdif cvv fdfin3_0 cvv fdfin3_1 cdif cdif cdif cvv fdfin3_0 cdif cvv fdfin3_1 cdif dfun2 cvv cvv fdfin3_0 cdif cdif cvv fdfin3_1 cdif cdif fdfin3_0 cvv fdfin3_1 cdif cdif cvv cvv cvv fdfin3_0 cdif cdif fdfin3_0 cvv fdfin3_1 cdif fdfin3_0 ddif difeq1i difeq2i eqtri difeq2i fdfin3_0 fdfin3_1 dfin2 3eqtr4ri $.
$}
$( Alternate definition of the intersection of two classes.  Exercise 4.10(q)
     of [Mendelson] p. 231.  (Contributed by NM, 25-Nov-2003.) $)
${
	$v A $.
	$v B $.
	fdfin4_0 $f class A $.
	fdfin4_1 $f class B $.
	dfin4 $p |- ( A i^i B ) = ( A \ ( A \ B ) ) $= fdfin4_0 fdfin4_0 fdfin4_0 fdfin4_1 cin cdif cdif fdfin4_0 fdfin4_1 cin fdfin4_0 fdfin4_0 fdfin4_1 cdif cdif fdfin4_0 fdfin4_1 cin fdfin4_0 wss fdfin4_0 fdfin4_0 fdfin4_0 fdfin4_1 cin cdif cdif fdfin4_0 fdfin4_1 cin wceq fdfin4_0 fdfin4_1 inss1 fdfin4_0 fdfin4_1 cin fdfin4_0 dfss4 mpbi fdfin4_0 fdfin4_0 fdfin4_1 cin cdif fdfin4_0 fdfin4_1 cdif fdfin4_0 fdfin4_0 fdfin4_1 difin difeq2i eqtr3i $.
$}
$( Intersection with universal complement.  Remark in [Stoll] p. 20.
     (Contributed by NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	finvdif_0 $f class A $.
	finvdif_1 $f class B $.
	invdif $p |- ( A i^i ( _V \ B ) ) = ( A \ B ) $= finvdif_0 cvv finvdif_1 cdif cin finvdif_0 cvv cvv finvdif_1 cdif cdif cdif finvdif_0 finvdif_1 cdif finvdif_0 cvv finvdif_1 cdif dfin2 cvv cvv finvdif_1 cdif cdif finvdif_1 finvdif_0 finvdif_1 ddif difeq2i eqtri $.
$}
$( Intersection with class difference.  Theorem 34 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	findif_0 $f class A $.
	findif_1 $f class B $.
	indif $p |- ( A i^i ( A \ B ) ) = ( A \ B ) $= findif_0 findif_0 findif_1 cdif cin findif_0 findif_0 findif_0 findif_1 cdif cdif cdif findif_0 findif_0 findif_1 cin cdif findif_0 findif_1 cdif findif_0 findif_0 findif_1 cdif dfin4 findif_0 findif_1 cin findif_0 findif_0 findif_1 cdif cdif findif_0 findif_0 findif_1 dfin4 difeq2i findif_0 findif_1 difin 3eqtr2i $.
$}
$( Bring an intersection in and out of a class difference.  (Contributed by
     Jeff Hankins, 15-Jul-2009.) $)
${
	$v A $.
	$v B $.
	$v C $.
	findif2_0 $f class A $.
	findif2_1 $f class B $.
	findif2_2 $f class C $.
	indif2 $p |- ( A i^i ( B \ C ) ) = ( ( A i^i B ) \ C ) $= findif2_0 findif2_1 cin cvv findif2_2 cdif cin findif2_0 findif2_1 cvv findif2_2 cdif cin cin findif2_0 findif2_1 cin findif2_2 cdif findif2_0 findif2_1 findif2_2 cdif cin findif2_0 findif2_1 cvv findif2_2 cdif inass findif2_0 findif2_1 cin findif2_2 invdif findif2_1 cvv findif2_2 cdif cin findif2_1 findif2_2 cdif findif2_0 findif2_1 findif2_2 invdif ineq2i 3eqtr3ri $.
$}
$( Bring an intersection in and out of a class difference.  (Contributed by
     Mario Carneiro, 15-May-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	findif1_0 $f class A $.
	findif1_1 $f class B $.
	findif1_2 $f class C $.
	indif1 $p |- ( ( A \ C ) i^i B ) = ( ( A i^i B ) \ C ) $= findif1_1 findif1_0 findif1_2 cdif cin findif1_1 findif1_0 cin findif1_2 cdif findif1_0 findif1_2 cdif findif1_1 cin findif1_0 findif1_1 cin findif1_2 cdif findif1_1 findif1_0 findif1_2 indif2 findif1_1 findif1_0 findif1_2 cdif incom findif1_1 findif1_0 cin findif1_0 findif1_1 cin findif1_2 findif1_1 findif1_0 incom difeq1i 3eqtr3i $.
$}
$( Commutation law for intersection and difference.  (Contributed by Scott
     Fenton, 18-Feb-2013.) $)
${
	$v A $.
	$v B $.
	$v C $.
	findifcom_0 $f class A $.
	findifcom_1 $f class B $.
	findifcom_2 $f class C $.
	indifcom $p |- ( A i^i ( B \ C ) ) = ( B i^i ( A \ C ) ) $= findifcom_0 findifcom_1 cin findifcom_2 cdif findifcom_1 findifcom_0 cin findifcom_2 cdif findifcom_0 findifcom_1 findifcom_2 cdif cin findifcom_1 findifcom_0 findifcom_2 cdif cin findifcom_0 findifcom_1 cin findifcom_1 findifcom_0 cin findifcom_2 findifcom_0 findifcom_1 incom difeq1i findifcom_0 findifcom_1 findifcom_2 indif2 findifcom_1 findifcom_0 findifcom_2 indif2 3eqtr4i $.
$}
$( Distributive law for intersection over union.  Exercise 10 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 30-Sep-2002.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iindi_0 $f set x $.
	findi_0 $f class A $.
	findi_1 $f class B $.
	findi_2 $f class C $.
	indi $p |- ( A i^i ( B u. C ) ) = ( ( A i^i B ) u. ( A i^i C ) ) $= iindi_0 findi_0 findi_1 findi_2 cun findi_0 findi_1 cin findi_0 findi_2 cin cun iindi_0 cv findi_0 wcel iindi_0 cv findi_1 wcel iindi_0 cv findi_2 wcel wo wa iindi_0 cv findi_0 findi_1 cin wcel iindi_0 cv findi_0 findi_2 cin wcel wo iindi_0 cv findi_0 wcel iindi_0 cv findi_1 findi_2 cun wcel wa iindi_0 cv findi_0 findi_1 cin findi_0 findi_2 cin cun wcel iindi_0 cv findi_0 wcel iindi_0 cv findi_1 wcel iindi_0 cv findi_2 wcel wo wa iindi_0 cv findi_0 wcel iindi_0 cv findi_1 wcel wa iindi_0 cv findi_0 wcel iindi_0 cv findi_2 wcel wa wo iindi_0 cv findi_0 findi_1 cin wcel iindi_0 cv findi_0 findi_2 cin wcel wo iindi_0 cv findi_0 wcel iindi_0 cv findi_1 wcel iindi_0 cv findi_2 wcel andi iindi_0 cv findi_0 findi_1 cin wcel iindi_0 cv findi_0 wcel iindi_0 cv findi_1 wcel wa iindi_0 cv findi_0 findi_2 cin wcel iindi_0 cv findi_0 wcel iindi_0 cv findi_2 wcel wa iindi_0 cv findi_0 findi_1 elin iindi_0 cv findi_0 findi_2 elin orbi12i bitr4i iindi_0 cv findi_1 findi_2 cun wcel iindi_0 cv findi_1 wcel iindi_0 cv findi_2 wcel wo iindi_0 cv findi_0 wcel iindi_0 cv findi_1 findi_2 elun anbi2i iindi_0 cv findi_0 findi_1 cin findi_0 findi_2 cin elun 3bitr4i ineqri $.
$}
$( Distributive law for union over intersection.  Exercise 11 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 30-Sep-2002.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iundi_0 $f set x $.
	fundi_0 $f class A $.
	fundi_1 $f class B $.
	fundi_2 $f class C $.
	undi $p |- ( A u. ( B i^i C ) ) = ( ( A u. B ) i^i ( A u. C ) ) $= iundi_0 fundi_0 fundi_1 fundi_2 cin fundi_0 fundi_1 cun fundi_0 fundi_2 cun cin iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 fundi_2 cin wcel wo iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 wcel iundi_0 cv fundi_2 wcel wa wo iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 wcel wo iundi_0 cv fundi_0 wcel iundi_0 cv fundi_2 wcel wo wa iundi_0 cv fundi_0 fundi_1 cun fundi_0 fundi_2 cun cin wcel iundi_0 cv fundi_1 fundi_2 cin wcel iundi_0 cv fundi_1 wcel iundi_0 cv fundi_2 wcel wa iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 fundi_2 elin orbi2i iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 wcel iundi_0 cv fundi_2 wcel ordi iundi_0 cv fundi_0 fundi_1 cun fundi_0 fundi_2 cun cin wcel iundi_0 cv fundi_0 fundi_1 cun wcel iundi_0 cv fundi_0 fundi_2 cun wcel wa iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 wcel wo iundi_0 cv fundi_0 wcel iundi_0 cv fundi_2 wcel wo wa iundi_0 cv fundi_0 fundi_1 cun fundi_0 fundi_2 cun elin iundi_0 cv fundi_0 fundi_1 cun wcel iundi_0 cv fundi_0 wcel iundi_0 cv fundi_1 wcel wo iundi_0 cv fundi_0 fundi_2 cun wcel iundi_0 cv fundi_0 wcel iundi_0 cv fundi_2 wcel wo iundi_0 cv fundi_0 fundi_1 elun iundi_0 cv fundi_0 fundi_2 elun anbi12i bitr2i 3bitri uneqri $.
$}
$( Distributive law for intersection over union.  Theorem 28 of [Suppes]
     p. 27.  (Contributed by NM, 30-Sep-2002.) $)
${
	$v A $.
	$v B $.
	$v C $.
	findir_0 $f class A $.
	findir_1 $f class B $.
	findir_2 $f class C $.
	indir $p |- ( ( A u. B ) i^i C ) = ( ( A i^i C ) u. ( B i^i C ) ) $= findir_2 findir_0 findir_1 cun cin findir_2 findir_0 cin findir_2 findir_1 cin cun findir_0 findir_1 cun findir_2 cin findir_0 findir_2 cin findir_1 findir_2 cin cun findir_2 findir_0 findir_1 indi findir_0 findir_1 cun findir_2 incom findir_0 findir_2 cin findir_2 findir_0 cin findir_1 findir_2 cin findir_2 findir_1 cin findir_0 findir_2 incom findir_1 findir_2 incom uneq12i 3eqtr4i $.
$}
$( Distributive law for union over intersection.  Theorem 29 of [Suppes]
     p. 27.  (Contributed by NM, 30-Sep-2002.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fundir_0 $f class A $.
	fundir_1 $f class B $.
	fundir_2 $f class C $.
	undir $p |- ( ( A i^i B ) u. C ) = ( ( A u. C ) i^i ( B u. C ) ) $= fundir_2 fundir_0 fundir_1 cin cun fundir_2 fundir_0 cun fundir_2 fundir_1 cun cin fundir_0 fundir_1 cin fundir_2 cun fundir_0 fundir_2 cun fundir_1 fundir_2 cun cin fundir_2 fundir_0 fundir_1 undi fundir_0 fundir_1 cin fundir_2 uncom fundir_0 fundir_2 cun fundir_2 fundir_0 cun fundir_1 fundir_2 cun fundir_2 fundir_1 cun fundir_0 fundir_2 uncom fundir_1 fundir_2 uncom ineq12i 3eqtr4i $.
$}
$( Infer equality from equalities of union and intersection.  Exercise 20
       of [Enderton] p. 32 and its converse.  (Contributed by NM,
       10-Aug-2004.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	iunineq_0 $f set x $.
	funineq_0 $f class A $.
	funineq_1 $f class B $.
	funineq_2 $f class C $.
	unineq $p |- ( ( ( A u. C ) = ( B u. C ) /\ ( A i^i C ) = ( B i^i C ) ) <-> A = B ) $= funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq wa funineq_0 funineq_1 wceq funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq wa iunineq_0 funineq_0 funineq_1 iunineq_0 cv funineq_2 wcel funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq wa iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_1 wcel wb wi iunineq_0 cv funineq_2 wcel funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_1 wcel wb funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_1 wcel wb iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_2 wcel wa iunineq_0 cv funineq_1 wcel iunineq_0 cv funineq_2 wcel wa wb funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq iunineq_0 cv funineq_0 funineq_2 cin wcel iunineq_0 cv funineq_1 funineq_2 cin wcel iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_2 wcel wa iunineq_0 cv funineq_1 wcel iunineq_0 cv funineq_2 wcel wa funineq_0 funineq_2 cin funineq_1 funineq_2 cin iunineq_0 cv eleq2 iunineq_0 cv funineq_0 funineq_2 elin iunineq_0 cv funineq_1 funineq_2 elin 3bitr3g iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_2 wcel wa iunineq_0 cv funineq_1 wcel iunineq_0 cv funineq_1 wcel iunineq_0 cv funineq_2 wcel wa iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel iba iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_1 wcel iba bibi12d syl5ibr adantld iunineq_0 cv funineq_2 wcel wn funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_1 wcel wb funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_1 wcel wb iunineq_0 cv funineq_2 wcel wn iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel wo iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_1 wcel wo wb funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq iunineq_0 cv funineq_2 funineq_0 cun wcel iunineq_0 cv funineq_2 funineq_1 cun wcel iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel wo iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_1 wcel wo funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq funineq_2 funineq_0 cun funineq_2 funineq_1 cun wceq iunineq_0 cv funineq_2 funineq_0 cun wcel iunineq_0 cv funineq_2 funineq_1 cun wcel wb funineq_0 funineq_2 cun funineq_2 funineq_0 cun funineq_1 funineq_2 cun funineq_2 funineq_1 cun funineq_0 funineq_2 uncom funineq_1 funineq_2 uncom eqeq12i funineq_2 funineq_0 cun funineq_2 funineq_1 cun iunineq_0 cv eleq2 sylbi iunineq_0 cv funineq_2 funineq_0 elun iunineq_0 cv funineq_2 funineq_1 elun 3bitr3g iunineq_0 cv funineq_2 wcel wn iunineq_0 cv funineq_0 wcel iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel wo iunineq_0 cv funineq_1 wcel iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_1 wcel wo iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_0 wcel biorf iunineq_0 cv funineq_2 wcel iunineq_0 cv funineq_1 wcel biorf bibi12d syl5ibr adantrd pm2.61i eqrdv funineq_0 funineq_1 wceq funineq_0 funineq_2 cun funineq_1 funineq_2 cun wceq funineq_0 funineq_2 cin funineq_1 funineq_2 cin wceq funineq_0 funineq_1 funineq_2 uneq1 funineq_0 funineq_1 funineq_2 ineq1 jca impbii $.
$}
$( Equality of union and intersection implies equality of their arguments.
     (Contributed by NM, 16-Apr-2006.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	funeqin_0 $f class A $.
	funeqin_1 $f class B $.
	uneqin $p |- ( ( A u. B ) = ( A i^i B ) <-> A = B ) $= funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin wceq funeqin_0 funeqin_1 wceq funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin wceq funeqin_0 funeqin_1 wss funeqin_1 funeqin_0 wss wa funeqin_0 funeqin_1 wceq funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin wceq funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin wss funeqin_0 funeqin_1 wss funeqin_1 funeqin_0 wss wa funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin eqimss funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin wss funeqin_0 funeqin_0 funeqin_1 cin wss funeqin_1 funeqin_0 funeqin_1 cin wss wa funeqin_0 funeqin_1 wss funeqin_1 funeqin_0 wss wa funeqin_0 funeqin_1 funeqin_0 funeqin_1 cin unss funeqin_0 funeqin_0 funeqin_1 cin wss funeqin_0 funeqin_1 wss funeqin_1 funeqin_0 funeqin_1 cin wss funeqin_1 funeqin_0 wss funeqin_0 funeqin_0 funeqin_1 cin wss funeqin_0 funeqin_0 wss funeqin_0 funeqin_1 wss wa funeqin_0 funeqin_1 wss funeqin_0 funeqin_0 funeqin_1 ssin funeqin_0 funeqin_0 funeqin_1 sstr sylbir funeqin_1 funeqin_0 funeqin_1 cin wss funeqin_1 funeqin_0 wss funeqin_1 funeqin_1 wss wa funeqin_1 funeqin_0 wss funeqin_1 funeqin_0 funeqin_1 ssin funeqin_1 funeqin_0 wss funeqin_1 funeqin_1 wss simpl sylbir anim12i sylbir syl funeqin_0 funeqin_1 eqss sylibr funeqin_0 funeqin_1 wceq funeqin_0 funeqin_0 cun funeqin_0 funeqin_0 cin funeqin_0 funeqin_1 cun funeqin_0 funeqin_1 cin funeqin_0 funeqin_0 cun funeqin_0 funeqin_0 funeqin_0 cin funeqin_0 unidm funeqin_0 inidm eqtr4i funeqin_0 funeqin_1 funeqin_0 uneq2 funeqin_0 funeqin_1 funeqin_0 ineq2 3eqtr3a impbii $.
$}
$( Distributive law for class difference.  Theorem 39 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifundi_0 $f class A $.
	fdifundi_1 $f class B $.
	fdifundi_2 $f class C $.
	difundi $p |- ( A \ ( B u. C ) ) = ( ( A \ B ) i^i ( A \ C ) ) $= fdifundi_0 fdifundi_1 fdifundi_2 cun cdif fdifundi_0 cvv cvv fdifundi_1 cdif cvv fdifundi_2 cdif cin cdif cdif fdifundi_0 fdifundi_1 cdif fdifundi_0 fdifundi_2 cdif cin fdifundi_1 fdifundi_2 cun cvv cvv fdifundi_1 cdif cvv fdifundi_2 cdif cin cdif fdifundi_0 fdifundi_1 fdifundi_2 dfun3 difeq2i fdifundi_0 cvv fdifundi_1 cdif cvv fdifundi_2 cdif cin cin fdifundi_0 cvv fdifundi_1 cdif cin fdifundi_0 cvv fdifundi_2 cdif cin cin fdifundi_0 cvv cvv fdifundi_1 cdif cvv fdifundi_2 cdif cin cdif cdif fdifundi_0 fdifundi_1 cdif fdifundi_0 fdifundi_2 cdif cin fdifundi_0 cvv fdifundi_1 cdif cvv fdifundi_2 cdif inindi fdifundi_0 cvv fdifundi_1 cdif cvv fdifundi_2 cdif cin dfin2 fdifundi_0 cvv fdifundi_1 cdif cin fdifundi_0 fdifundi_1 cdif fdifundi_0 cvv fdifundi_2 cdif cin fdifundi_0 fdifundi_2 cdif fdifundi_0 fdifundi_1 invdif fdifundi_0 fdifundi_2 invdif ineq12i 3eqtr3i eqtri $.
$}
$( Distributive law for class difference.  (Contributed by NM,
     17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifundir_0 $f class A $.
	fdifundir_1 $f class B $.
	fdifundir_2 $f class C $.
	difundir $p |- ( ( A u. B ) \ C ) = ( ( A \ C ) u. ( B \ C ) ) $= fdifundir_0 fdifundir_1 cun cvv fdifundir_2 cdif cin fdifundir_0 cvv fdifundir_2 cdif cin fdifundir_1 cvv fdifundir_2 cdif cin cun fdifundir_0 fdifundir_1 cun fdifundir_2 cdif fdifundir_0 fdifundir_2 cdif fdifundir_1 fdifundir_2 cdif cun fdifundir_0 fdifundir_1 cvv fdifundir_2 cdif indir fdifundir_0 fdifundir_1 cun fdifundir_2 invdif fdifundir_0 cvv fdifundir_2 cdif cin fdifundir_0 fdifundir_2 cdif fdifundir_1 cvv fdifundir_2 cdif cin fdifundir_1 fdifundir_2 cdif fdifundir_0 fdifundir_2 invdif fdifundir_1 fdifundir_2 invdif uneq12i 3eqtr3i $.
$}
$( Distributive law for class difference.  Theorem 40 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifindi_0 $f class A $.
	fdifindi_1 $f class B $.
	fdifindi_2 $f class C $.
	difindi $p |- ( A \ ( B i^i C ) ) = ( ( A \ B ) u. ( A \ C ) ) $= fdifindi_0 fdifindi_1 fdifindi_2 cin cdif fdifindi_0 cvv cvv fdifindi_1 cdif cvv fdifindi_2 cdif cun cdif cdif fdifindi_0 fdifindi_1 cdif fdifindi_0 fdifindi_2 cdif cun fdifindi_1 fdifindi_2 cin cvv cvv fdifindi_1 cdif cvv fdifindi_2 cdif cun cdif fdifindi_0 fdifindi_1 fdifindi_2 dfin3 difeq2i fdifindi_0 cvv fdifindi_1 cdif cvv fdifindi_2 cdif cun cin fdifindi_0 cvv fdifindi_1 cdif cin fdifindi_0 cvv fdifindi_2 cdif cin cun fdifindi_0 cvv cvv fdifindi_1 cdif cvv fdifindi_2 cdif cun cdif cdif fdifindi_0 fdifindi_1 cdif fdifindi_0 fdifindi_2 cdif cun fdifindi_0 cvv fdifindi_1 cdif cvv fdifindi_2 cdif indi fdifindi_0 cvv fdifindi_1 cdif cvv fdifindi_2 cdif cun dfin2 fdifindi_0 cvv fdifindi_1 cdif cin fdifindi_0 fdifindi_1 cdif fdifindi_0 cvv fdifindi_2 cdif cin fdifindi_0 fdifindi_2 cdif fdifindi_0 fdifindi_1 invdif fdifindi_0 fdifindi_2 invdif uneq12i 3eqtr3i eqtri $.
$}
$( Distributive law for class difference.  (Contributed by NM,
     17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifindir_0 $f class A $.
	fdifindir_1 $f class B $.
	fdifindir_2 $f class C $.
	difindir $p |- ( ( A i^i B ) \ C ) = ( ( A \ C ) i^i ( B \ C ) ) $= fdifindir_0 fdifindir_1 cin cvv fdifindir_2 cdif cin fdifindir_0 cvv fdifindir_2 cdif cin fdifindir_1 cvv fdifindir_2 cdif cin cin fdifindir_0 fdifindir_1 cin fdifindir_2 cdif fdifindir_0 fdifindir_2 cdif fdifindir_1 fdifindir_2 cdif cin fdifindir_0 fdifindir_1 cvv fdifindir_2 cdif inindir fdifindir_0 fdifindir_1 cin fdifindir_2 invdif fdifindir_0 cvv fdifindir_2 cdif cin fdifindir_0 fdifindir_2 cdif fdifindir_1 cvv fdifindir_2 cdif cin fdifindir_1 fdifindir_2 cdif fdifindir_0 fdifindir_2 invdif fdifindir_1 fdifindir_2 invdif ineq12i 3eqtr3i $.
$}
$( Distribute intersection over difference.  (Contributed by Scott Fenton,
       14-Apr-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d A x $.
	$d B x $.
	$d C x $.
	iindifdir_0 $f set x $.
	findifdir_0 $f class A $.
	findifdir_1 $f class B $.
	findifdir_2 $f class C $.
	indifdir $p |- ( ( A \ B ) i^i C ) = ( ( A i^i C ) \ ( B i^i C ) ) $= iindifdir_0 findifdir_0 findifdir_1 cdif findifdir_2 cin findifdir_0 findifdir_2 cin findifdir_1 findifdir_2 cin cdif iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel wa wn wa iindifdir_0 cv findifdir_0 findifdir_1 cdif findifdir_2 cin wcel iindifdir_0 cv findifdir_0 findifdir_2 cin findifdir_1 findifdir_2 cin cdif wcel iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel wn iindifdir_0 cv findifdir_2 wcel wn wo wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel wa wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_2 wcel wn wa wo iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel wn iindifdir_0 cv findifdir_2 wcel wn wo wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_2 wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_2 wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel iindifdir_0 cv findifdir_2 wcel wn wa wa iindifdir_0 cv findifdir_2 wcel iindifdir_0 cv findifdir_2 wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel pm3.24 intnan iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel iindifdir_0 cv findifdir_2 wcel wn anass mtbir biorfi iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_1 wcel wn iindifdir_0 cv findifdir_2 wcel an32 iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel wn iindifdir_0 cv findifdir_2 wcel wn andi 3bitr4i iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel wa wn iindifdir_0 cv findifdir_1 wcel wn iindifdir_0 cv findifdir_2 wcel wn wo iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel ianor anbi2i bitr4i iindifdir_0 cv findifdir_0 findifdir_1 cdif findifdir_2 cin wcel iindifdir_0 cv findifdir_0 findifdir_1 cdif wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_0 findifdir_1 cdif findifdir_2 elin iindifdir_0 cv findifdir_0 findifdir_1 cdif wcel iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_1 wcel wn wa iindifdir_0 cv findifdir_2 wcel iindifdir_0 cv findifdir_0 findifdir_1 eldif anbi1i bitri iindifdir_0 cv findifdir_0 findifdir_2 cin findifdir_1 findifdir_2 cin cdif wcel iindifdir_0 cv findifdir_0 findifdir_2 cin wcel iindifdir_0 cv findifdir_1 findifdir_2 cin wcel wn wa iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel wa wn wa iindifdir_0 cv findifdir_0 findifdir_2 cin findifdir_1 findifdir_2 cin eldif iindifdir_0 cv findifdir_0 findifdir_2 cin wcel iindifdir_0 cv findifdir_0 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 findifdir_2 cin wcel wn iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel wa wn iindifdir_0 cv findifdir_0 findifdir_2 elin iindifdir_0 cv findifdir_1 findifdir_2 cin wcel iindifdir_0 cv findifdir_1 wcel iindifdir_0 cv findifdir_2 wcel wa iindifdir_0 cv findifdir_1 findifdir_2 elin notbii anbi12i bitri 3bitr4i eqriv $.
$}
$( De Morgan's law for union.  Theorem 5.2(13) of [Stoll] p. 19.
     (Contributed by NM, 18-Aug-2004.) $)
${
	$v A $.
	$v B $.
	fundm_0 $f class A $.
	fundm_1 $f class B $.
	undm $p |- ( _V \ ( A u. B ) ) = ( ( _V \ A ) i^i ( _V \ B ) ) $= cvv fundm_0 fundm_1 difundi $.
$}
$( De Morgan's law for intersection.  Theorem 5.2(13') of [Stoll] p. 19.
     (Contributed by NM, 18-Aug-2004.) $)
${
	$v A $.
	$v B $.
	findm_0 $f class A $.
	findm_1 $f class B $.
	indm $p |- ( _V \ ( A i^i B ) ) = ( ( _V \ A ) u. ( _V \ B ) ) $= cvv findm_0 findm_1 difindi $.
$}
$( A relationship involving double difference and union.  (Contributed by NM,
     29-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdifun1_0 $f class A $.
	fdifun1_1 $f class B $.
	fdifun1_2 $f class C $.
	difun1 $p |- ( A \ ( B u. C ) ) = ( ( A \ B ) \ C ) $= fdifun1_0 cvv fdifun1_1 cdif cin fdifun1_2 cdif fdifun1_0 fdifun1_1 fdifun1_2 cun cdif fdifun1_0 fdifun1_1 cdif fdifun1_2 cdif fdifun1_0 cvv fdifun1_1 cdif cvv fdifun1_2 cdif cin cin fdifun1_0 cvv fdifun1_1 cdif cin fdifun1_2 cdif fdifun1_0 fdifun1_1 fdifun1_2 cun cdif fdifun1_0 cvv fdifun1_1 cdif cin cvv fdifun1_2 cdif cin fdifun1_0 cvv fdifun1_1 cdif cvv fdifun1_2 cdif cin cin fdifun1_0 cvv fdifun1_1 cdif cin fdifun1_2 cdif fdifun1_0 cvv fdifun1_1 cdif cvv fdifun1_2 cdif inass fdifun1_0 cvv fdifun1_1 cdif cin fdifun1_2 invdif eqtr3i fdifun1_0 cvv fdifun1_1 fdifun1_2 cun cdif cin fdifun1_0 cvv fdifun1_1 cdif cvv fdifun1_2 cdif cin cin fdifun1_0 fdifun1_1 fdifun1_2 cun cdif cvv fdifun1_1 fdifun1_2 cun cdif cvv fdifun1_1 cdif cvv fdifun1_2 cdif cin fdifun1_0 fdifun1_1 fdifun1_2 undm ineq2i fdifun1_0 fdifun1_1 fdifun1_2 cun invdif eqtr3i eqtr3i fdifun1_0 cvv fdifun1_1 cdif cin fdifun1_0 fdifun1_1 cdif fdifun1_2 fdifun1_0 fdifun1_1 invdif difeq1i eqtr3i $.
$}
$( An equality involving class union and class difference.  The first
       equality of Exercise 13 of [TakeutiZaring] p. 22.  (Contributed by Alan
       Sare, 17-Apr-2012.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d A x $.
	$d B x $.
	$d C x $.
	iundif3_0 $f set x $.
	fundif3_0 $f class A $.
	fundif3_1 $f class B $.
	fundif3_2 $f class C $.
	undif3 $p |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C \ A ) ) $= iundif3_0 fundif3_0 fundif3_1 fundif3_2 cdif cun fundif3_0 fundif3_1 cun fundif3_2 fundif3_0 cdif cdif iundif3_0 cv fundif3_0 fundif3_1 cun wcel iundif3_0 cv fundif3_2 fundif3_0 cdif wcel wn wa iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo wa iundif3_0 cv fundif3_0 fundif3_1 cun fundif3_2 fundif3_0 cdif cdif wcel iundif3_0 cv fundif3_0 fundif3_1 fundif3_2 cdif cun wcel iundif3_0 cv fundif3_0 fundif3_1 cun wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 fundif3_0 cdif wcel wn iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo iundif3_0 cv fundif3_0 fundif3_1 elun iundif3_0 cv fundif3_2 wcel iundif3_0 cv fundif3_0 wcel wn wa iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo iundif3_0 cv fundif3_2 fundif3_0 cdif wcel iundif3_0 cv fundif3_2 wcel iundif3_0 cv fundif3_0 wcel pm4.53 iundif3_0 cv fundif3_2 fundif3_0 eldif xchnxbir anbi12i iundif3_0 cv fundif3_0 fundif3_1 cun fundif3_2 fundif3_0 cdif eldif iundif3_0 cv fundif3_0 fundif3_1 fundif3_2 cdif cun wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 fundif3_2 cdif wcel wo iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa wo iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo wa iundif3_0 cv fundif3_0 fundif3_1 fundif3_2 cdif elun iundif3_0 cv fundif3_1 fundif3_2 cdif wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 fundif3_2 eldif orbi2i iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa wo iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo wa iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo wa iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel orc iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_2 wcel wn olc jca iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel wo iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel wo iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_0 wcel olc iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_0 wcel orc anim12i jaoi iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_2 wcel wn iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa wo iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_2 wcel wn wa iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_2 wcel wn simpl orcd iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa iundif3_0 cv fundif3_0 wcel olc iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa wo iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa orc adantr iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa wo iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_0 wcel iundif3_0 cv fundif3_1 wcel iundif3_0 cv fundif3_2 wcel wn wa orc adantl ccase impbii 3bitri 3bitr4ri eqriv $.
$}
$( Represent a set difference as an intersection with a larger difference.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d A x $.
	$d B x $.
	$d C x $.
	idifin2_0 $f set x $.
	fdifin2_0 $f class A $.
	fdifin2_1 $f class B $.
	fdifin2_2 $f class C $.
	difin2 $p |- ( A C_ C -> ( A \ B ) = ( ( C \ B ) i^i A ) ) $= fdifin2_0 fdifin2_2 wss idifin2_0 fdifin2_0 fdifin2_1 cdif fdifin2_2 fdifin2_1 cdif fdifin2_0 cin fdifin2_0 fdifin2_2 wss idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel wa idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_0 fdifin2_1 cdif wcel idifin2_0 cv fdifin2_2 fdifin2_1 cdif fdifin2_0 cin wcel fdifin2_0 fdifin2_2 wss idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel wa idifin2_0 cv fdifin2_1 wcel wn fdifin2_0 fdifin2_2 wss idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel fdifin2_0 fdifin2_2 idifin2_0 cv ssel pm4.71d anbi1d idifin2_0 cv fdifin2_0 fdifin2_1 eldif idifin2_0 cv fdifin2_2 fdifin2_1 cdif fdifin2_0 cin wcel idifin2_0 cv fdifin2_2 fdifin2_1 cdif wcel idifin2_0 cv fdifin2_0 wcel wa idifin2_0 cv fdifin2_2 wcel idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_0 wcel wa idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel wa idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_2 fdifin2_1 cdif fdifin2_0 elin idifin2_0 cv fdifin2_2 fdifin2_1 cdif wcel idifin2_0 cv fdifin2_2 wcel idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 fdifin2_1 eldif anbi1i idifin2_0 cv fdifin2_2 wcel idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_0 wcel wa idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel idifin2_0 cv fdifin2_1 wcel wn wa wa idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel wa idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_2 wcel idifin2_0 cv fdifin2_1 wcel wn wa idifin2_0 cv fdifin2_0 wcel ancom idifin2_0 cv fdifin2_0 wcel idifin2_0 cv fdifin2_2 wcel idifin2_0 cv fdifin2_1 wcel wn anass bitr4i 3bitri 3bitr4g eqrdv $.
$}
$( Swap second and third argument of double difference.  (Contributed by NM,
     18-Aug-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fdif32_0 $f class A $.
	fdif32_1 $f class B $.
	fdif32_2 $f class C $.
	dif32 $p |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ B ) $= fdif32_0 fdif32_1 fdif32_2 cun cdif fdif32_0 fdif32_2 fdif32_1 cun cdif fdif32_0 fdif32_1 cdif fdif32_2 cdif fdif32_0 fdif32_2 cdif fdif32_1 cdif fdif32_1 fdif32_2 cun fdif32_2 fdif32_1 cun fdif32_0 fdif32_1 fdif32_2 uncom difeq2i fdif32_0 fdif32_1 fdif32_2 difun1 fdif32_0 fdif32_2 fdif32_1 difun1 3eqtr3i $.
$}
$( Absorption-like law for class difference: you can remove a class only
     once.  (Contributed by FL, 2-Aug-2009.) $)
${
	$v A $.
	$v B $.
	fdifabs_0 $f class A $.
	fdifabs_1 $f class B $.
	difabs $p |- ( ( A \ B ) \ B ) = ( A \ B ) $= fdifabs_0 fdifabs_1 fdifabs_1 cun cdif fdifabs_0 fdifabs_1 cdif fdifabs_1 cdif fdifabs_0 fdifabs_1 cdif fdifabs_0 fdifabs_1 fdifabs_1 difun1 fdifabs_1 fdifabs_1 cun fdifabs_1 fdifabs_0 fdifabs_1 unidm difeq2i eqtr3i $.
$}
$( Two ways to express symmetric difference.  This theorem shows the
     equivalence of the definition of symmetric difference in [Stoll] p. 13 and
     the restated definition in Example 4.1 of [Stoll] p. 262.  (Contributed by
     NM, 17-Aug-2004.) $)
${
	$v A $.
	$v B $.
	fsymdif1_0 $f class A $.
	fsymdif1_1 $f class B $.
	symdif1 $p |- ( ( A \ B ) u. ( B \ A ) ) = ( ( A u. B ) \ ( A i^i B ) ) $= fsymdif1_0 fsymdif1_1 cun fsymdif1_0 fsymdif1_1 cin cdif fsymdif1_0 fsymdif1_0 fsymdif1_1 cin cdif fsymdif1_1 fsymdif1_0 fsymdif1_1 cin cdif cun fsymdif1_0 fsymdif1_1 cdif fsymdif1_1 fsymdif1_0 cdif cun fsymdif1_0 fsymdif1_1 fsymdif1_0 fsymdif1_1 cin difundir fsymdif1_0 fsymdif1_0 fsymdif1_1 cin cdif fsymdif1_0 fsymdif1_1 cdif fsymdif1_1 fsymdif1_0 fsymdif1_1 cin cdif fsymdif1_1 fsymdif1_0 cdif fsymdif1_0 fsymdif1_1 difin fsymdif1_1 fsymdif1_0 fsymdif1_1 cin cdif fsymdif1_1 fsymdif1_1 fsymdif1_0 cin cdif fsymdif1_1 fsymdif1_0 cdif fsymdif1_0 fsymdif1_1 cin fsymdif1_1 fsymdif1_0 cin fsymdif1_1 fsymdif1_0 fsymdif1_1 incom difeq2i fsymdif1_1 fsymdif1_0 difin eqtri uneq12i eqtr2i $.
$}
$( Two ways to express symmetric difference.  (Contributed by NM,
       17-Aug-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fsymdif2_0 $f set x $.
	fsymdif2_1 $f class A $.
	fsymdif2_2 $f class B $.
	symdif2 $p |- ( ( A \ B ) u. ( B \ A ) ) = { x | -. ( x e. A <-> x e. B ) } $= fsymdif2_0 cv fsymdif2_1 wcel fsymdif2_0 cv fsymdif2_2 wcel wb wn fsymdif2_0 fsymdif2_1 fsymdif2_2 cdif fsymdif2_2 fsymdif2_1 cdif cun fsymdif2_0 cv fsymdif2_1 fsymdif2_2 cdif wcel fsymdif2_0 cv fsymdif2_2 fsymdif2_1 cdif wcel wo fsymdif2_0 cv fsymdif2_1 wcel fsymdif2_0 cv fsymdif2_2 wcel wn wa fsymdif2_0 cv fsymdif2_2 wcel fsymdif2_0 cv fsymdif2_1 wcel wn wa wo fsymdif2_0 cv fsymdif2_1 fsymdif2_2 cdif fsymdif2_2 fsymdif2_1 cdif cun wcel fsymdif2_0 cv fsymdif2_1 wcel fsymdif2_0 cv fsymdif2_2 wcel wb wn fsymdif2_0 cv fsymdif2_1 fsymdif2_2 cdif wcel fsymdif2_0 cv fsymdif2_1 wcel fsymdif2_0 cv fsymdif2_2 wcel wn wa fsymdif2_0 cv fsymdif2_2 fsymdif2_1 cdif wcel fsymdif2_0 cv fsymdif2_2 wcel fsymdif2_0 cv fsymdif2_1 wcel wn wa fsymdif2_0 cv fsymdif2_1 fsymdif2_2 eldif fsymdif2_0 cv fsymdif2_2 fsymdif2_1 eldif orbi12i fsymdif2_0 cv fsymdif2_1 fsymdif2_2 cdif fsymdif2_2 fsymdif2_1 cdif elun fsymdif2_0 cv fsymdif2_1 wcel fsymdif2_0 cv fsymdif2_2 wcel xor 3bitr4i abbi2i $.
$}
$( Union of two class abstractions.  (Contributed by NM, 29-Sep-2002.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d ph y $.
	$d ps y $.
	iunab_0 $f set y $.
	funab_0 $f wff ph $.
	funab_1 $f wff ps $.
	funab_2 $f set x $.
	unab $p |- ( { x | ph } u. { x | ps } ) = { x | ( ph \/ ps ) } $= iunab_0 funab_0 funab_2 cab funab_1 funab_2 cab funab_0 funab_1 wo funab_2 cab funab_0 funab_1 wo funab_2 iunab_0 wsb funab_0 funab_2 iunab_0 wsb funab_1 funab_2 iunab_0 wsb wo iunab_0 cv funab_0 funab_1 wo funab_2 cab wcel iunab_0 cv funab_0 funab_2 cab wcel iunab_0 cv funab_1 funab_2 cab wcel wo funab_0 funab_1 funab_2 iunab_0 sbor funab_0 funab_1 wo iunab_0 funab_2 df-clab iunab_0 cv funab_0 funab_2 cab wcel funab_0 funab_2 iunab_0 wsb iunab_0 cv funab_1 funab_2 cab wcel funab_1 funab_2 iunab_0 wsb funab_0 iunab_0 funab_2 df-clab funab_1 iunab_0 funab_2 df-clab orbi12i 3bitr4ri uneqri $.
$}
$( Intersection of two class abstractions.  (Contributed by NM,
       29-Sep-2002.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d ph y $.
	$d ps y $.
	iinab_0 $f set y $.
	finab_0 $f wff ph $.
	finab_1 $f wff ps $.
	finab_2 $f set x $.
	inab $p |- ( { x | ph } i^i { x | ps } ) = { x | ( ph /\ ps ) } $= iinab_0 finab_0 finab_2 cab finab_1 finab_2 cab finab_0 finab_1 wa finab_2 cab finab_0 finab_1 wa finab_2 iinab_0 wsb finab_0 finab_2 iinab_0 wsb finab_1 finab_2 iinab_0 wsb wa iinab_0 cv finab_0 finab_1 wa finab_2 cab wcel iinab_0 cv finab_0 finab_2 cab wcel iinab_0 cv finab_1 finab_2 cab wcel wa finab_0 finab_1 finab_2 iinab_0 sban finab_0 finab_1 wa iinab_0 finab_2 df-clab iinab_0 cv finab_0 finab_2 cab wcel finab_0 finab_2 iinab_0 wsb iinab_0 cv finab_1 finab_2 cab wcel finab_1 finab_2 iinab_0 wsb finab_0 iinab_0 finab_2 df-clab finab_1 iinab_0 finab_2 df-clab anbi12i 3bitr4ri ineqri $.
$}
$( Difference of two class abstractions.  (Contributed by NM,
       23-Oct-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v y $.
	$d x y $.
	$d ph y $.
	$d ps y $.
	idifab_0 $f set y $.
	fdifab_0 $f wff ph $.
	fdifab_1 $f wff ps $.
	fdifab_2 $f set x $.
	difab $p |- ( { x | ph } \ { x | ps } ) = { x | ( ph /\ -. ps ) } $= idifab_0 fdifab_0 fdifab_2 cab fdifab_1 fdifab_2 cab fdifab_0 fdifab_1 wn wa fdifab_2 cab idifab_0 cv fdifab_0 fdifab_1 wn wa fdifab_2 cab wcel fdifab_0 fdifab_1 wn wa fdifab_2 idifab_0 wsb fdifab_0 fdifab_2 idifab_0 wsb fdifab_1 wn fdifab_2 idifab_0 wsb wa idifab_0 cv fdifab_0 fdifab_2 cab wcel idifab_0 cv fdifab_1 fdifab_2 cab wcel wn wa fdifab_0 fdifab_1 wn wa idifab_0 fdifab_2 df-clab fdifab_0 fdifab_1 wn fdifab_2 idifab_0 sban fdifab_0 fdifab_2 idifab_0 wsb idifab_0 cv fdifab_0 fdifab_2 cab wcel fdifab_1 wn fdifab_2 idifab_0 wsb idifab_0 cv fdifab_1 fdifab_2 cab wcel wn idifab_0 cv fdifab_0 fdifab_2 cab wcel fdifab_0 fdifab_2 idifab_0 wsb fdifab_0 idifab_0 fdifab_2 df-clab bicomi fdifab_1 wn fdifab_2 idifab_0 wsb fdifab_1 fdifab_2 idifab_0 wsb idifab_0 cv fdifab_1 fdifab_2 cab wcel fdifab_1 fdifab_2 idifab_0 sbn fdifab_1 idifab_0 fdifab_2 df-clab xchbinxr anbi12i 3bitrri difeqri $.
$}
$( A class builder defined by a negation.  (Contributed by FL,
     18-Sep-2010.) $)
${
	$v ph $.
	$v x $.
	fnotab_0 $f wff ph $.
	fnotab_1 $f set x $.
	notab $p |- { x | -. ph } = ( _V \ { x | ph } ) $= fnotab_1 cv cvv wcel fnotab_0 wn wa fnotab_1 cab fnotab_0 wn fnotab_1 cab cvv fnotab_0 fnotab_1 cab cdif fnotab_0 wn fnotab_1 cvv crab fnotab_1 cv cvv wcel fnotab_0 wn wa fnotab_1 cab fnotab_0 wn fnotab_1 cab fnotab_0 wn fnotab_1 cvv df-rab fnotab_0 wn fnotab_1 rabab eqtr3i fnotab_1 cv cvv wcel fnotab_1 cab fnotab_0 fnotab_1 cab cdif fnotab_1 cv cvv wcel fnotab_0 wn wa fnotab_1 cab cvv fnotab_0 fnotab_1 cab cdif fnotab_1 cv cvv wcel fnotab_0 fnotab_1 difab fnotab_1 cv cvv wcel fnotab_1 cab cvv fnotab_0 fnotab_1 cab fnotab_1 cvv abid2 difeq1i eqtr3i eqtr3i $.
$}
$( Union of two restricted class abstractions.  (Contributed by NM,
     25-Mar-2004.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	funrab_0 $f wff ph $.
	funrab_1 $f wff ps $.
	funrab_2 $f set x $.
	funrab_3 $f class A $.
	unrab $p |- ( { x e. A | ph } u. { x e. A | ps } ) = { x e. A | ( ph \/ ps ) } $= funrab_0 funrab_2 funrab_3 crab funrab_1 funrab_2 funrab_3 crab cun funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cab funrab_2 cv funrab_3 wcel funrab_1 wa funrab_2 cab cun funrab_0 funrab_1 wo funrab_2 funrab_3 crab funrab_0 funrab_2 funrab_3 crab funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cab funrab_1 funrab_2 funrab_3 crab funrab_2 cv funrab_3 wcel funrab_1 wa funrab_2 cab funrab_0 funrab_2 funrab_3 df-rab funrab_1 funrab_2 funrab_3 df-rab uneq12i funrab_0 funrab_1 wo funrab_2 funrab_3 crab funrab_2 cv funrab_3 wcel funrab_0 funrab_1 wo wa funrab_2 cab funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cab funrab_2 cv funrab_3 wcel funrab_1 wa funrab_2 cab cun funrab_0 funrab_1 wo funrab_2 funrab_3 df-rab funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cab funrab_2 cv funrab_3 wcel funrab_1 wa funrab_2 cab cun funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cv funrab_3 wcel funrab_1 wa wo funrab_2 cab funrab_2 cv funrab_3 wcel funrab_0 funrab_1 wo wa funrab_2 cab funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cv funrab_3 wcel funrab_1 wa funrab_2 unab funrab_2 cv funrab_3 wcel funrab_0 funrab_1 wo wa funrab_2 cv funrab_3 wcel funrab_0 wa funrab_2 cv funrab_3 wcel funrab_1 wa wo funrab_2 funrab_2 cv funrab_3 wcel funrab_0 funrab_1 andi abbii eqtr4i eqtr4i eqtr4i $.
$}
$( Intersection of two restricted class abstractions.  (Contributed by NM,
     1-Sep-2006.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	finrab_0 $f wff ph $.
	finrab_1 $f wff ps $.
	finrab_2 $f set x $.
	finrab_3 $f class A $.
	inrab $p |- ( { x e. A | ph } i^i { x e. A | ps } ) = { x e. A | ( ph /\ ps ) } $= finrab_0 finrab_2 finrab_3 crab finrab_1 finrab_2 finrab_3 crab cin finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cab finrab_2 cv finrab_3 wcel finrab_1 wa finrab_2 cab cin finrab_0 finrab_1 wa finrab_2 finrab_3 crab finrab_0 finrab_2 finrab_3 crab finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cab finrab_1 finrab_2 finrab_3 crab finrab_2 cv finrab_3 wcel finrab_1 wa finrab_2 cab finrab_0 finrab_2 finrab_3 df-rab finrab_1 finrab_2 finrab_3 df-rab ineq12i finrab_0 finrab_1 wa finrab_2 finrab_3 crab finrab_2 cv finrab_3 wcel finrab_0 finrab_1 wa wa finrab_2 cab finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cab finrab_2 cv finrab_3 wcel finrab_1 wa finrab_2 cab cin finrab_0 finrab_1 wa finrab_2 finrab_3 df-rab finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cab finrab_2 cv finrab_3 wcel finrab_1 wa finrab_2 cab cin finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cv finrab_3 wcel finrab_1 wa wa finrab_2 cab finrab_2 cv finrab_3 wcel finrab_0 finrab_1 wa wa finrab_2 cab finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cv finrab_3 wcel finrab_1 wa finrab_2 inab finrab_2 cv finrab_3 wcel finrab_0 finrab_1 wa wa finrab_2 cv finrab_3 wcel finrab_0 wa finrab_2 cv finrab_3 wcel finrab_1 wa wa finrab_2 finrab_2 cv finrab_3 wcel finrab_0 finrab_1 anandi abbii eqtr4i eqtr4i eqtr4i $.
$}
$( Intersection with a restricted class abstraction.  (Contributed by NM,
       19-Nov-2007.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x B $.
	finrab2_0 $f wff ph $.
	finrab2_1 $f set x $.
	finrab2_2 $f class A $.
	finrab2_3 $f class B $.
	inrab2 $p |- ( { x e. A | ph } i^i B ) = { x e. ( A i^i B ) | ph } $= finrab2_0 finrab2_1 finrab2_2 crab finrab2_3 cin finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cab finrab2_1 cv finrab2_3 wcel finrab2_1 cab cin finrab2_0 finrab2_1 finrab2_2 finrab2_3 cin crab finrab2_0 finrab2_1 finrab2_2 crab finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cab finrab2_3 finrab2_1 cv finrab2_3 wcel finrab2_1 cab finrab2_0 finrab2_1 finrab2_2 df-rab finrab2_1 cv finrab2_3 wcel finrab2_1 cab finrab2_3 finrab2_1 finrab2_3 abid2 eqcomi ineq12i finrab2_0 finrab2_1 finrab2_2 finrab2_3 cin crab finrab2_1 cv finrab2_2 finrab2_3 cin wcel finrab2_0 wa finrab2_1 cab finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cab finrab2_1 cv finrab2_3 wcel finrab2_1 cab cin finrab2_0 finrab2_1 finrab2_2 finrab2_3 cin df-rab finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cab finrab2_1 cv finrab2_3 wcel finrab2_1 cab cin finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cv finrab2_3 wcel wa finrab2_1 cab finrab2_1 cv finrab2_2 finrab2_3 cin wcel finrab2_0 wa finrab2_1 cab finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cv finrab2_3 wcel finrab2_1 inab finrab2_1 cv finrab2_2 finrab2_3 cin wcel finrab2_0 wa finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cv finrab2_3 wcel wa finrab2_1 finrab2_1 cv finrab2_2 finrab2_3 cin wcel finrab2_0 wa finrab2_1 cv finrab2_2 wcel finrab2_1 cv finrab2_3 wcel wa finrab2_0 wa finrab2_1 cv finrab2_2 wcel finrab2_0 wa finrab2_1 cv finrab2_3 wcel wa finrab2_1 cv finrab2_2 finrab2_3 cin wcel finrab2_1 cv finrab2_2 wcel finrab2_1 cv finrab2_3 wcel wa finrab2_0 finrab2_1 cv finrab2_2 finrab2_3 elin anbi1i finrab2_1 cv finrab2_2 wcel finrab2_1 cv finrab2_3 wcel finrab2_0 an32 bitri abbii eqtr4i eqtr4i eqtr4i $.
$}
$( Difference of two restricted class abstractions.  (Contributed by NM,
     23-Oct-2004.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	fdifrab_0 $f wff ph $.
	fdifrab_1 $f wff ps $.
	fdifrab_2 $f set x $.
	fdifrab_3 $f class A $.
	difrab $p |- ( { x e. A | ph } \ { x e. A | ps } ) = { x e. A | ( ph /\ -. ps ) } $= fdifrab_0 fdifrab_2 fdifrab_3 crab fdifrab_1 fdifrab_2 fdifrab_3 crab cdif fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cab fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_2 cab cdif fdifrab_0 fdifrab_1 wn wa fdifrab_2 fdifrab_3 crab fdifrab_0 fdifrab_2 fdifrab_3 crab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cab fdifrab_1 fdifrab_2 fdifrab_3 crab fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_2 cab fdifrab_0 fdifrab_2 fdifrab_3 df-rab fdifrab_1 fdifrab_2 fdifrab_3 df-rab difeq12i fdifrab_0 fdifrab_1 wn wa fdifrab_2 fdifrab_3 crab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 fdifrab_1 wn wa wa fdifrab_2 cab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cab fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_2 cab cdif fdifrab_0 fdifrab_1 wn wa fdifrab_2 fdifrab_3 df-rab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cab fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_2 cab cdif fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wn wa fdifrab_2 cab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 fdifrab_1 wn wa wa fdifrab_2 cab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_2 difab fdifrab_2 cv fdifrab_3 wcel fdifrab_0 fdifrab_1 wn wa wa fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wn wa fdifrab_2 fdifrab_2 cv fdifrab_3 wcel fdifrab_0 fdifrab_1 wn wa wa fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_1 wn wa fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wn wa fdifrab_2 cv fdifrab_3 wcel fdifrab_0 fdifrab_1 wn anass fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_1 wn wa fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wn wa fdifrab_1 wn fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wn fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_1 fdifrab_2 cv fdifrab_3 wcel fdifrab_1 simpr con3i anim2i fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wn fdifrab_1 wn fdifrab_2 cv fdifrab_3 wcel fdifrab_0 wa fdifrab_1 fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa fdifrab_2 cv fdifrab_3 wcel fdifrab_1 fdifrab_2 cv fdifrab_3 wcel fdifrab_1 wa wi fdifrab_0 fdifrab_2 cv fdifrab_3 wcel fdifrab_1 pm3.2 adantr con3d imdistani impbii bitr3i abbii eqtr4i eqtr4i eqtr4i $.
$}
$( Alternate definition of restricted class abstraction.  (Contributed by
       NM, 20-Sep-2003.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fdfrab2_0 $f wff ph $.
	fdfrab2_1 $f set x $.
	fdfrab2_2 $f class A $.
	dfrab2 $p |- { x e. A | ph } = ( { x | ph } i^i A ) $= fdfrab2_0 fdfrab2_1 fdfrab2_2 crab fdfrab2_1 cv fdfrab2_2 wcel fdfrab2_0 wa fdfrab2_1 cab fdfrab2_2 fdfrab2_0 fdfrab2_1 cab cin fdfrab2_0 fdfrab2_1 cab fdfrab2_2 cin fdfrab2_0 fdfrab2_1 fdfrab2_2 df-rab fdfrab2_1 cv fdfrab2_2 wcel fdfrab2_1 cab fdfrab2_0 fdfrab2_1 cab cin fdfrab2_1 cv fdfrab2_2 wcel fdfrab2_0 wa fdfrab2_1 cab fdfrab2_2 fdfrab2_0 fdfrab2_1 cab cin fdfrab2_1 cv fdfrab2_2 wcel fdfrab2_0 fdfrab2_1 inab fdfrab2_1 cv fdfrab2_2 wcel fdfrab2_1 cab fdfrab2_2 fdfrab2_0 fdfrab2_1 cab fdfrab2_1 fdfrab2_2 abid2 ineq1i eqtr3i fdfrab2_2 fdfrab2_0 fdfrab2_1 cab incom 3eqtri $.
$}
$( Alternate definition of restricted class abstraction.  (Contributed by
       Mario Carneiro, 8-Sep-2013.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fdfrab3_0 $f wff ph $.
	fdfrab3_1 $f set x $.
	fdfrab3_2 $f class A $.
	dfrab3 $p |- { x e. A | ph } = ( A i^i { x | ph } ) $= fdfrab3_0 fdfrab3_1 fdfrab3_2 crab fdfrab3_1 cv fdfrab3_2 wcel fdfrab3_0 wa fdfrab3_1 cab fdfrab3_1 cv fdfrab3_2 wcel fdfrab3_1 cab fdfrab3_0 fdfrab3_1 cab cin fdfrab3_2 fdfrab3_0 fdfrab3_1 cab cin fdfrab3_0 fdfrab3_1 fdfrab3_2 df-rab fdfrab3_1 cv fdfrab3_2 wcel fdfrab3_0 fdfrab3_1 inab fdfrab3_1 cv fdfrab3_2 wcel fdfrab3_1 cab fdfrab3_2 fdfrab3_0 fdfrab3_1 cab fdfrab3_1 fdfrab3_2 abid2 ineq1i 3eqtr2i $.
$}
$( Complementation of restricted class abstractions.  (Contributed by Mario
       Carneiro, 3-Sep-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fnotrab_0 $f wff ph $.
	fnotrab_1 $f set x $.
	fnotrab_2 $f class A $.
	notrab $p |- ( A \ { x e. A | ph } ) = { x e. A | -. ph } $= fnotrab_1 cv fnotrab_2 wcel fnotrab_1 cab fnotrab_0 fnotrab_1 cab cdif fnotrab_1 cv fnotrab_2 wcel fnotrab_0 wn wa fnotrab_1 cab fnotrab_2 fnotrab_0 fnotrab_1 fnotrab_2 crab cdif fnotrab_0 wn fnotrab_1 fnotrab_2 crab fnotrab_1 cv fnotrab_2 wcel fnotrab_0 fnotrab_1 difab fnotrab_2 fnotrab_2 fnotrab_0 fnotrab_1 cab cin cdif fnotrab_2 fnotrab_0 fnotrab_1 cab cdif fnotrab_2 fnotrab_0 fnotrab_1 fnotrab_2 crab cdif fnotrab_1 cv fnotrab_2 wcel fnotrab_1 cab fnotrab_0 fnotrab_1 cab cdif fnotrab_2 fnotrab_0 fnotrab_1 cab difin fnotrab_0 fnotrab_1 fnotrab_2 crab fnotrab_2 fnotrab_0 fnotrab_1 cab cin fnotrab_2 fnotrab_0 fnotrab_1 fnotrab_2 dfrab3 difeq2i fnotrab_1 cv fnotrab_2 wcel fnotrab_1 cab fnotrab_2 fnotrab_0 fnotrab_1 cab fnotrab_1 fnotrab_2 abid2 difeq1i 3eqtr4i fnotrab_0 wn fnotrab_1 fnotrab_2 df-rab 3eqtr4i $.
$}
$( Restricted class abstraction with a common superset.  (Contributed by
       Stefan O'Rear, 12-Sep-2015.)  (Proof shortened by Mario Carneiro,
       8-Nov-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdfrab3ss_0 $f wff ph $.
	fdfrab3ss_1 $f set x $.
	fdfrab3ss_2 $f class A $.
	fdfrab3ss_3 $f class B $.
	dfrab3ss $p |- ( A C_ B -> { x e. A | ph } = ( A i^i { x e. B | ph } ) ) $= fdfrab3ss_2 fdfrab3ss_3 wss fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_0 fdfrab3ss_1 fdfrab3ss_2 crab fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 fdfrab3ss_3 crab cin fdfrab3ss_2 fdfrab3ss_3 wss fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_2 wceq fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_0 fdfrab3ss_1 cab cin wceq fdfrab3ss_2 fdfrab3ss_3 df-ss fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_2 wceq fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 cab ineq1 eqcomd sylbi fdfrab3ss_0 fdfrab3ss_1 fdfrab3ss_2 dfrab3 fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 fdfrab3ss_3 crab cin fdfrab3ss_2 fdfrab3ss_3 fdfrab3ss_0 fdfrab3ss_1 cab cin cin fdfrab3ss_2 fdfrab3ss_3 cin fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_0 fdfrab3ss_1 fdfrab3ss_3 crab fdfrab3ss_3 fdfrab3ss_0 fdfrab3ss_1 cab cin fdfrab3ss_2 fdfrab3ss_0 fdfrab3ss_1 fdfrab3ss_3 dfrab3 ineq2i fdfrab3ss_2 fdfrab3ss_3 fdfrab3ss_0 fdfrab3ss_1 cab inass eqtr4i 3eqtr4g $.
$}
$( Abstraction restricted to a union.  (Contributed by Stefan O'Rear,
     5-Feb-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	frabun2_0 $f wff ph $.
	frabun2_1 $f set x $.
	frabun2_2 $f class A $.
	frabun2_3 $f class B $.
	rabun2 $p |- { x e. ( A u. B ) | ph } = ( { x e. A | ph } u. { x e. B | ph } ) $= frabun2_0 frabun2_1 frabun2_2 frabun2_3 cun crab frabun2_1 cv frabun2_2 frabun2_3 cun wcel frabun2_0 wa frabun2_1 cab frabun2_0 frabun2_1 frabun2_2 crab frabun2_0 frabun2_1 frabun2_3 crab cun frabun2_0 frabun2_1 frabun2_2 frabun2_3 cun df-rab frabun2_0 frabun2_1 frabun2_2 crab frabun2_0 frabun2_1 frabun2_3 crab cun frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cab frabun2_1 cv frabun2_3 wcel frabun2_0 wa frabun2_1 cab cun frabun2_1 cv frabun2_2 frabun2_3 cun wcel frabun2_0 wa frabun2_1 cab frabun2_0 frabun2_1 frabun2_2 crab frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cab frabun2_0 frabun2_1 frabun2_3 crab frabun2_1 cv frabun2_3 wcel frabun2_0 wa frabun2_1 cab frabun2_0 frabun2_1 frabun2_2 df-rab frabun2_0 frabun2_1 frabun2_3 df-rab uneq12i frabun2_1 cv frabun2_2 frabun2_3 cun wcel frabun2_0 wa frabun2_1 cab frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cv frabun2_3 wcel frabun2_0 wa wo frabun2_1 cab frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cab frabun2_1 cv frabun2_3 wcel frabun2_0 wa frabun2_1 cab cun frabun2_1 cv frabun2_2 frabun2_3 cun wcel frabun2_0 wa frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cv frabun2_3 wcel frabun2_0 wa wo frabun2_1 frabun2_1 cv frabun2_2 frabun2_3 cun wcel frabun2_0 wa frabun2_1 cv frabun2_2 wcel frabun2_1 cv frabun2_3 wcel wo frabun2_0 wa frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cv frabun2_3 wcel frabun2_0 wa wo frabun2_1 cv frabun2_2 frabun2_3 cun wcel frabun2_1 cv frabun2_2 wcel frabun2_1 cv frabun2_3 wcel wo frabun2_0 frabun2_1 cv frabun2_2 frabun2_3 elun anbi1i frabun2_1 cv frabun2_2 wcel frabun2_1 cv frabun2_3 wcel frabun2_0 andir bitri abbii frabun2_1 cv frabun2_2 wcel frabun2_0 wa frabun2_1 cv frabun2_3 wcel frabun2_0 wa frabun2_1 unab eqtr4i eqtr4i eqtr4i $.
$}
$( Transfer uniqueness to a smaller subclass.  (Contributed by NM,
       20-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	freuss2_0 $f wff ph $.
	freuss2_1 $f wff ps $.
	freuss2_2 $f set x $.
	freuss2_3 $f class A $.
	freuss2_4 $f class B $.
	reuss2 $p |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph /\ E! x e. B ps ) ) -> E! x e. A ph ) $= freuss2_0 freuss2_2 freuss2_3 wrex freuss2_1 freuss2_2 freuss2_4 wreu wa freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 wral wa freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wex freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 weu wa freuss2_0 freuss2_2 freuss2_3 wreu freuss2_0 freuss2_2 freuss2_3 wrex freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wex freuss2_1 freuss2_2 freuss2_4 wreu freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 weu freuss2_0 freuss2_2 freuss2_3 df-rex freuss2_1 freuss2_2 freuss2_4 df-reu anbi12i freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 wral wa freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wex freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 weu wa wa freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 weu freuss2_0 freuss2_2 freuss2_3 wreu freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 wral wa freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wex freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 weu freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 weu freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 wral wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 weu freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wmo freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wex freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 weu freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 wral wa freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_2 wal freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 weu freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wmo wi freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 wral freuss2_3 freuss2_4 wss freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_1 wi wi freuss2_2 wal freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_2 wal freuss2_0 freuss2_1 wi freuss2_2 freuss2_3 df-ral freuss2_3 freuss2_4 wss freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_1 wi wi freuss2_2 wal freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_2 wal freuss2_3 freuss2_4 wss freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_1 wi wi freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_2 freuss2_3 freuss2_4 wss freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_1 wi wi freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_3 freuss2_4 wss freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_1 wi freuss2_0 freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_3 freuss2_4 wss freuss2_0 freuss2_1 wi freuss2_2 cv freuss2_3 wcel freuss2_0 freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_3 freuss2_4 wss freuss2_2 cv freuss2_3 wcel freuss2_2 cv freuss2_4 wcel wi freuss2_0 freuss2_1 wi freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa wi freuss2_3 freuss2_4 freuss2_2 cv ssel freuss2_2 cv freuss2_3 wcel freuss2_2 cv freuss2_4 wcel freuss2_0 freuss2_1 prth sylan exp4b com23 a2d imp4a alimdv imp sylan2b freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 cv freuss2_4 wcel freuss2_1 wa freuss2_2 euimmo syl freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 weu freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wex freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 wmo freuss2_2 cv freuss2_3 wcel freuss2_0 wa freuss2_2 eu5 simplbi2 syl9 imp32 freuss2_0 freuss2_2 freuss2_3 df-reu sylibr sylan2b $.
$}
$( Transfer uniqueness to a smaller subclass.  (Contributed by NM,
       21-Aug-1999.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	freuss_0 $f wff ph $.
	freuss_1 $f set x $.
	freuss_2 $f class A $.
	freuss_3 $f class B $.
	reuss $p |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) -> E! x e. A ph ) $= freuss_2 freuss_3 wss freuss_0 freuss_1 freuss_2 wrex freuss_0 freuss_1 freuss_3 wreu freuss_0 freuss_1 freuss_2 wreu freuss_2 freuss_3 wss freuss_0 freuss_0 wi freuss_1 freuss_2 wral freuss_0 freuss_1 freuss_2 wrex freuss_0 freuss_1 freuss_3 wreu wa freuss_0 freuss_1 freuss_2 wreu freuss_0 freuss_0 wi freuss_1 freuss_2 freuss_1 cv freuss_2 wcel freuss_0 idd rgen freuss_0 freuss_0 freuss_1 freuss_2 freuss_3 reuss2 mpanl2 3impb $.
$}
$( Transfer uniqueness to a smaller class.  (Contributed by NM,
       21-Oct-2005.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	freuun1_0 $f wff ph $.
	freuun1_1 $f wff ps $.
	freuun1_2 $f set x $.
	freuun1_3 $f class A $.
	freuun1_4 $f class B $.
	reuun1 $p |- ( ( E. x e. A ph /\ E! x e. ( A u. B ) ( ph \/ ps ) ) -> E! x e. A ph ) $= freuun1_3 freuun1_3 freuun1_4 cun wss freuun1_0 freuun1_0 freuun1_1 wo wi freuun1_2 freuun1_3 wral freuun1_0 freuun1_2 freuun1_3 wrex freuun1_0 freuun1_1 wo freuun1_2 freuun1_3 freuun1_4 cun wreu wa freuun1_0 freuun1_2 freuun1_3 wreu freuun1_3 freuun1_4 ssun1 freuun1_0 freuun1_0 freuun1_1 wo wi freuun1_2 freuun1_3 freuun1_0 freuun1_1 orc rgenw freuun1_0 freuun1_0 freuun1_1 wo freuun1_2 freuun1_3 freuun1_3 freuun1_4 cun reuss2 mpanl12 $.
$}
$( Transfer uniqueness to a smaller or larger class.  (Contributed by NM,
       21-Oct-2005.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	freuun2_0 $f wff ph $.
	freuun2_1 $f set x $.
	freuun2_2 $f class A $.
	freuun2_3 $f class B $.
	reuun2 $p |- ( -. E. x e. B ph -> ( E! x e. ( A u. B ) ph <-> E! x e. A ph ) ) $= freuun2_0 freuun2_1 freuun2_3 wrex wn freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa wo freuun2_1 weu freuun2_1 cv freuun2_2 wcel freuun2_0 wa freuun2_1 weu freuun2_0 freuun2_1 freuun2_2 freuun2_3 cun wreu freuun2_0 freuun2_1 freuun2_2 wreu freuun2_0 freuun2_1 freuun2_3 wrex freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 wex freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa wo freuun2_1 weu freuun2_1 cv freuun2_2 wcel freuun2_0 wa freuun2_1 weu wb freuun2_0 freuun2_1 freuun2_3 df-rex freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa freuun2_1 euor2 sylnbi freuun2_0 freuun2_1 freuun2_2 freuun2_3 cun wreu freuun2_1 cv freuun2_2 freuun2_3 cun wcel freuun2_0 wa freuun2_1 weu freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa wo freuun2_1 weu freuun2_0 freuun2_1 freuun2_2 freuun2_3 cun df-reu freuun2_1 cv freuun2_2 freuun2_3 cun wcel freuun2_0 wa freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa wo freuun2_1 freuun2_1 cv freuun2_2 freuun2_3 cun wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_1 cv freuun2_3 wcel wo freuun2_0 wa freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa wo freuun2_1 cv freuun2_2 freuun2_3 cun wcel freuun2_1 cv freuun2_2 wcel freuun2_1 cv freuun2_3 wcel wo freuun2_0 freuun2_1 cv freuun2_2 freuun2_3 elun anbi1i freuun2_1 cv freuun2_2 wcel freuun2_1 cv freuun2_3 wcel wo freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa freuun2_1 cv freuun2_3 wcel freuun2_0 wa wo freuun2_1 cv freuun2_3 wcel freuun2_0 wa freuun2_1 cv freuun2_2 wcel freuun2_0 wa wo freuun2_1 cv freuun2_2 wcel freuun2_1 cv freuun2_3 wcel freuun2_0 andir freuun2_1 cv freuun2_2 wcel freuun2_0 wa freuun2_1 cv freuun2_3 wcel freuun2_0 wa orcom bitri bitri eubii bitri freuun2_0 freuun2_1 freuun2_2 df-reu 3bitr4g $.
$}
$( Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       NM, 21-Aug-1999.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	freupick_0 $f wff ph $.
	freupick_1 $f set x $.
	freupick_2 $f class A $.
	freupick_3 $f class B $.
	reupick $p |- ( ( ( A C_ B /\ ( E. x e. A ph /\ E! x e. B ph ) ) /\ ph ) -> ( x e. A <-> x e. B ) ) $= freupick_2 freupick_3 wss freupick_0 freupick_1 freupick_2 wrex freupick_0 freupick_1 freupick_3 wreu wa wa freupick_0 wa freupick_1 cv freupick_2 wcel freupick_1 cv freupick_3 wcel freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_1 cv freupick_3 wcel wi freupick_0 freupick_1 freupick_2 wrex freupick_0 freupick_1 freupick_3 wreu wa freupick_0 freupick_2 freupick_3 freupick_1 cv ssel ad2antrr freupick_2 freupick_3 wss freupick_0 freupick_1 freupick_2 wrex freupick_0 freupick_1 freupick_3 wreu wa wa freupick_0 freupick_1 cv freupick_3 wcel freupick_1 cv freupick_2 wcel wi freupick_2 freupick_3 wss freupick_0 freupick_1 freupick_2 wrex freupick_0 freupick_1 freupick_3 wreu wa wa freupick_1 cv freupick_3 wcel freupick_0 freupick_1 cv freupick_2 wcel freupick_0 freupick_1 freupick_2 wrex freupick_0 freupick_1 freupick_3 wreu wa freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 wex freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 weu wa freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wi freupick_0 freupick_1 freupick_2 wrex freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 wex freupick_0 freupick_1 freupick_3 wreu freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 weu freupick_0 freupick_1 freupick_2 df-rex freupick_0 freupick_1 freupick_3 df-reu anbi12i freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 wex freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 weu freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wi freupick_2 freupick_3 wss freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 weu freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 wex freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wi freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 wex freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wa freupick_1 wex freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 weu freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wi freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wa freupick_1 freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_0 wa freupick_1 cv freupick_3 wcel freupick_1 cv freupick_2 wcel wa freupick_0 wa freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wa freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_1 cv freupick_3 wcel freupick_1 cv freupick_2 wcel wa freupick_0 freupick_2 freupick_3 wss freupick_1 cv freupick_2 wcel freupick_1 cv freupick_3 wcel freupick_2 freupick_3 freupick_1 cv ssel ancrd anim1d freupick_1 cv freupick_3 wcel freupick_1 cv freupick_2 wcel freupick_0 an32 syl6ib eximdv freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 weu freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wa freupick_1 wex freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel wi freupick_1 cv freupick_3 wcel freupick_0 wa freupick_1 cv freupick_2 wcel freupick_1 eupick ex syl9 com23 imp32 sylan2b exp3acom23 imp impbid $.
$}
$( Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       Mario Carneiro, 19-Nov-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$d x A $.
	freupick3_0 $f wff ph $.
	freupick3_1 $f wff ps $.
	freupick3_2 $f set x $.
	freupick3_3 $f class A $.
	reupick3 $p |- ( ( E! x e. A ph /\ E. x e. A ( ph /\ ps ) /\ x e. A ) -> ( ph -> ps ) ) $= freupick3_0 freupick3_2 freupick3_3 wreu freupick3_0 freupick3_1 wa freupick3_2 freupick3_3 wrex freupick3_2 cv freupick3_3 wcel freupick3_0 freupick3_1 wi freupick3_0 freupick3_2 freupick3_3 wreu freupick3_0 freupick3_1 wa freupick3_2 freupick3_3 wrex wa freupick3_2 cv freupick3_3 wcel freupick3_0 freupick3_1 freupick3_0 freupick3_2 freupick3_3 wreu freupick3_2 cv freupick3_3 wcel freupick3_0 wa freupick3_2 weu freupick3_2 cv freupick3_3 wcel freupick3_0 wa freupick3_1 wa freupick3_2 wex freupick3_2 cv freupick3_3 wcel freupick3_0 wa freupick3_1 wi freupick3_0 freupick3_1 wa freupick3_2 freupick3_3 wrex freupick3_0 freupick3_2 freupick3_3 df-reu freupick3_0 freupick3_1 wa freupick3_2 freupick3_3 wrex freupick3_2 cv freupick3_3 wcel freupick3_0 freupick3_1 wa wa freupick3_2 wex freupick3_2 cv freupick3_3 wcel freupick3_0 wa freupick3_1 wa freupick3_2 wex freupick3_0 freupick3_1 wa freupick3_2 freupick3_3 df-rex freupick3_2 cv freupick3_3 wcel freupick3_0 wa freupick3_1 wa freupick3_2 cv freupick3_3 wcel freupick3_0 freupick3_1 wa wa freupick3_2 freupick3_2 cv freupick3_3 wcel freupick3_0 freupick3_1 anass exbii bitr4i freupick3_2 cv freupick3_3 wcel freupick3_0 wa freupick3_1 freupick3_2 eupick syl2anb exp3a 3impia $.
$}
$( Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       Mario Carneiro, 15-Dec-2013.)  (Proof shortened by Mario Carneiro,
       19-Nov-2016.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$d x A $.
	freupick2_0 $f wff ph $.
	freupick2_1 $f wff ps $.
	freupick2_2 $f set x $.
	freupick2_3 $f class A $.
	reupick2 $p |- ( ( ( A. x e. A ( ps -> ph ) /\ E. x e. A ps /\ E! x e. A ph ) /\ x e. A ) -> ( ph <-> ps ) ) $= freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_2 freupick2_3 wrex freupick2_0 freupick2_2 freupick2_3 wreu w3a freupick2_2 cv freupick2_3 wcel wa freupick2_0 freupick2_1 freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_2 freupick2_3 wrex freupick2_0 freupick2_2 freupick2_3 wreu freupick2_2 cv freupick2_3 wcel freupick2_0 freupick2_1 wi freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_2 freupick2_3 wrex freupick2_0 freupick2_1 wa freupick2_2 freupick2_3 wrex freupick2_0 freupick2_2 freupick2_3 wreu freupick2_2 cv freupick2_3 wcel freupick2_0 freupick2_1 wi wi wi freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_0 freupick2_1 wa wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_2 freupick2_3 wrex freupick2_0 freupick2_1 wa freupick2_2 freupick2_3 wrex wi freupick2_1 freupick2_0 wi freupick2_1 freupick2_0 freupick2_1 wa wi freupick2_2 freupick2_3 freupick2_1 freupick2_0 ancr ralimi freupick2_1 freupick2_0 freupick2_1 wa freupick2_2 freupick2_3 rexim syl freupick2_0 freupick2_2 freupick2_3 wreu freupick2_0 freupick2_1 wa freupick2_2 freupick2_3 wrex freupick2_2 cv freupick2_3 wcel freupick2_0 freupick2_1 wi wi freupick2_0 freupick2_2 freupick2_3 wreu freupick2_0 freupick2_1 wa freupick2_2 freupick2_3 wrex freupick2_2 cv freupick2_3 wcel freupick2_0 freupick2_1 wi freupick2_0 freupick2_1 freupick2_2 freupick2_3 reupick3 3exp com12 syl6 3imp1 freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_2 freupick2_3 wrex freupick2_0 freupick2_2 freupick2_3 wreu w3a freupick2_2 cv freupick2_3 wcel freupick2_1 freupick2_0 wi freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 wral freupick2_1 freupick2_2 freupick2_3 wrex freupick2_2 cv freupick2_3 wcel freupick2_1 freupick2_0 wi wi freupick2_0 freupick2_2 freupick2_3 wreu freupick2_1 freupick2_0 wi freupick2_2 freupick2_3 rsp 3ad2ant1 imp impbid $.
$}

