$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Ordered_pair_theorem.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Ordered-pair class abstractions (cont.)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The law of concretion.  Special case of Theorem 9.5 of [Quine] p. 61.
       (Contributed by NM, 14-Apr-1995.)  (Proof shortened by Andrew Salmon,
       25-Jul-2011.) $)
${
	$d x z $.
	$d y z $.
	$d ph z $.
	iopabid_0 $f set z $.
	fopabid_0 $f wff ph $.
	fopabid_1 $f set x $.
	fopabid_2 $f set y $.
	opabid $p |- ( <. x , y >. e. { <. x , y >. | ph } <-> ph ) $= iopabid_0 cv fopabid_1 cv fopabid_2 cv cop wceq fopabid_0 wa fopabid_2 wex fopabid_1 wex fopabid_0 iopabid_0 fopabid_1 cv fopabid_2 cv cop fopabid_0 fopabid_1 fopabid_2 copab fopabid_1 cv fopabid_2 cv opex iopabid_0 cv fopabid_1 cv fopabid_2 cv cop wceq fopabid_0 iopabid_0 cv fopabid_1 cv fopabid_2 cv cop wceq fopabid_0 wa fopabid_2 wex fopabid_1 wex fopabid_0 fopabid_1 fopabid_2 iopabid_0 cv copsexg bicomd fopabid_0 fopabid_1 fopabid_2 iopabid_0 df-opab elab2 $.
$}
$( Membership in a class abstraction of pairs.  (Contributed by NM,
       24-Mar-1998.) $)
${
	$d x z A $.
	$d y z A $.
	$d z ph $.
	ielopab_0 $f set z $.
	felopab_0 $f wff ph $.
	felopab_1 $f set x $.
	felopab_2 $f set y $.
	felopab_3 $f class A $.
	elopab $p |- ( A e. { <. x , y >. | ph } <-> E. x E. y ( A = <. x , y >. /\ ph ) ) $= felopab_3 felopab_0 felopab_1 felopab_2 copab wcel felopab_3 cvv wcel felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_0 wa felopab_2 wex felopab_1 wex felopab_3 felopab_0 felopab_1 felopab_2 copab elex felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_0 wa felopab_3 cvv wcel felopab_1 felopab_2 felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_3 cvv wcel felopab_0 felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_3 cvv wcel felopab_1 cv felopab_2 cv cop cvv wcel felopab_1 cv felopab_2 cv opex felopab_3 felopab_1 cv felopab_2 cv cop cvv eleq1 mpbiri adantr exlimivv ielopab_0 cv felopab_1 cv felopab_2 cv cop wceq felopab_0 wa felopab_2 wex felopab_1 wex felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_0 wa felopab_2 wex felopab_1 wex ielopab_0 felopab_3 felopab_0 felopab_1 felopab_2 copab cvv ielopab_0 cv felopab_3 wceq ielopab_0 cv felopab_1 cv felopab_2 cv cop wceq felopab_0 wa felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_0 wa felopab_1 felopab_2 ielopab_0 cv felopab_3 wceq ielopab_0 cv felopab_1 cv felopab_2 cv cop wceq felopab_3 felopab_1 cv felopab_2 cv cop wceq felopab_0 ielopab_0 cv felopab_3 felopab_1 cv felopab_2 cv cop eqeq1 anbi1d 2exbidv felopab_0 felopab_1 felopab_2 ielopab_0 df-opab elab2g pm5.21nii $.
$}
$( The law of concretion in terms of substitutions.  (Contributed by NM,
       30-Sep-2002.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.)
       (New usage is discouraged.) $)
${
	$d x y z $.
	$d x y w $.
	fopelopabsbOLD_0 $f wff ph $.
	fopelopabsbOLD_1 $f set x $.
	fopelopabsbOLD_2 $f set y $.
	fopelopabsbOLD_3 $f set z $.
	fopelopabsbOLD_4 $f set w $.
	opelopabsbOLD $p |- ( <. z , w >. e. { <. x , y >. | ph } <-> [ w / y ] [ z / x ] ph ) $= fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_0 wa fopelopabsbOLD_2 wex fopelopabsbOLD_1 wex fopelopabsbOLD_2 cv fopelopabsbOLD_4 cv wceq fopelopabsbOLD_1 cv fopelopabsbOLD_3 cv wceq wa fopelopabsbOLD_0 wa fopelopabsbOLD_1 wex fopelopabsbOLD_2 wex fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_0 fopelopabsbOLD_1 fopelopabsbOLD_2 copab wcel fopelopabsbOLD_0 fopelopabsbOLD_1 fopelopabsbOLD_3 wsb fopelopabsbOLD_2 fopelopabsbOLD_4 wsb fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_0 wa fopelopabsbOLD_2 wex fopelopabsbOLD_1 wex fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_0 wa fopelopabsbOLD_1 wex fopelopabsbOLD_2 wex fopelopabsbOLD_2 cv fopelopabsbOLD_4 cv wceq fopelopabsbOLD_1 cv fopelopabsbOLD_3 cv wceq wa fopelopabsbOLD_0 wa fopelopabsbOLD_1 wex fopelopabsbOLD_2 wex fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_0 wa fopelopabsbOLD_1 fopelopabsbOLD_2 excom fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_0 wa fopelopabsbOLD_2 cv fopelopabsbOLD_4 cv wceq fopelopabsbOLD_1 cv fopelopabsbOLD_3 cv wceq wa fopelopabsbOLD_0 wa fopelopabsbOLD_2 fopelopabsbOLD_1 fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_2 cv fopelopabsbOLD_4 cv wceq fopelopabsbOLD_1 cv fopelopabsbOLD_3 cv wceq wa fopelopabsbOLD_0 fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv cop wceq fopelopabsbOLD_3 cv fopelopabsbOLD_1 cv wceq fopelopabsbOLD_4 cv fopelopabsbOLD_2 cv wceq wa fopelopabsbOLD_2 cv fopelopabsbOLD_4 cv wceq fopelopabsbOLD_1 cv fopelopabsbOLD_3 cv wceq wa fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv fopelopabsbOLD_1 cv fopelopabsbOLD_2 cv fopelopabsbOLD_3 vex fopelopabsbOLD_4 vex opth fopelopabsbOLD_3 cv fopelopabsbOLD_1 cv wceq fopelopabsbOLD_1 cv fopelopabsbOLD_3 cv wceq fopelopabsbOLD_4 cv fopelopabsbOLD_2 cv wceq fopelopabsbOLD_2 cv fopelopabsbOLD_4 cv wceq fopelopabsbOLD_3 fopelopabsbOLD_1 equcom fopelopabsbOLD_4 fopelopabsbOLD_2 equcom anbi12ci bitri anbi1i 2exbii bitri fopelopabsbOLD_0 fopelopabsbOLD_1 fopelopabsbOLD_2 fopelopabsbOLD_3 cv fopelopabsbOLD_4 cv cop elopab fopelopabsbOLD_0 fopelopabsbOLD_2 fopelopabsbOLD_1 fopelopabsbOLD_4 fopelopabsbOLD_3 2sb5 3bitr4i $.
$}
$( The law of concretion in terms of substitutions.  (Contributed by NM,
       17-Mar-2008.)  (New usage is discouraged.) $)
${
	$d x y z $.
	$d x y w $.
	fbrabsbOLD_0 $f wff ph $.
	fbrabsbOLD_1 $f set x $.
	fbrabsbOLD_2 $f set y $.
	fbrabsbOLD_3 $f set z $.
	fbrabsbOLD_4 $f set w $.
	fbrabsbOLD_5 $f class R $.
	ebrabsbOLD_0 $e |- R = { <. x , y >. | ph } $.
	brabsbOLD $p |- ( z R w <-> [ w / y ] [ z / x ] ph ) $= fbrabsbOLD_3 cv fbrabsbOLD_4 cv fbrabsbOLD_5 wbr fbrabsbOLD_3 cv fbrabsbOLD_4 cv fbrabsbOLD_0 fbrabsbOLD_1 fbrabsbOLD_2 copab wbr fbrabsbOLD_3 cv fbrabsbOLD_4 cv cop fbrabsbOLD_0 fbrabsbOLD_1 fbrabsbOLD_2 copab wcel fbrabsbOLD_0 fbrabsbOLD_1 fbrabsbOLD_3 wsb fbrabsbOLD_2 fbrabsbOLD_4 wsb fbrabsbOLD_3 cv fbrabsbOLD_4 cv fbrabsbOLD_5 fbrabsbOLD_0 fbrabsbOLD_1 fbrabsbOLD_2 copab ebrabsbOLD_0 breqi fbrabsbOLD_3 cv fbrabsbOLD_4 cv fbrabsbOLD_0 fbrabsbOLD_1 fbrabsbOLD_2 copab df-br fbrabsbOLD_0 fbrabsbOLD_1 fbrabsbOLD_2 fbrabsbOLD_3 fbrabsbOLD_4 opelopabsbOLD 3bitri $.
$}
$( The law of concretion in terms of substitutions.  (Contributed by NM,
       30-Sep-2002.)  (Revised by Mario Carneiro, 18-Nov-2016.) $)
${
	$d x y z w $.
	$d w z A $.
	$d w x B $.
	$d w z ph $.
	iopelopabsb_0 $f set z $.
	iopelopabsb_1 $f set w $.
	fopelopabsb_0 $f wff ph $.
	fopelopabsb_1 $f set x $.
	fopelopabsb_2 $f set y $.
	fopelopabsb_3 $f class A $.
	fopelopabsb_4 $f class B $.
	opelopabsb $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> [. A / x ]. [. B / y ]. ph ) $= fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_3 cvv wcel fopelopabsb_4 cvv wcel wa fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 wsbc fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_3 fopelopabsb_4 cop c0 wne fopelopabsb_3 cvv wcel fopelopabsb_4 cvv wcel wa fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_3 fopelopabsb_4 cop c0 fopelopabsb_3 fopelopabsb_4 cop c0 wceq fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel c0 fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel c0 fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 wa fopelopabsb_2 wex fopelopabsb_1 wex c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 wa fopelopabsb_2 wex fopelopabsb_1 c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 wa fopelopabsb_2 fopelopabsb_1 cv fopelopabsb_2 cv cop c0 wne c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 wa wn fopelopabsb_1 cv fopelopabsb_2 cv fopelopabsb_1 vex fopelopabsb_2 vex opnzi c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 wa fopelopabsb_1 cv fopelopabsb_2 cv cop c0 c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 wa c0 fopelopabsb_1 cv fopelopabsb_2 cv cop c0 fopelopabsb_1 cv fopelopabsb_2 cv cop wceq fopelopabsb_0 simpl eqcomd necon3ai ax-mp nex nex fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 c0 elopab mtbir fopelopabsb_3 fopelopabsb_4 cop c0 fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab eleq1 mtbiri necon2ai fopelopabsb_3 fopelopabsb_4 opnz sylib fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 wsbc fopelopabsb_3 cvv wcel fopelopabsb_4 cvv wcel fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 sbcex fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 wsbc fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 wex fopelopabsb_4 cvv wcel fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 spesbc fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_4 cvv wcel fopelopabsb_1 fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 sbcex exlimiv syl jca iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 wsb wb fopelopabsb_3 iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 fopelopabsb_3 wsbc wb fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 wsbc wb iopelopabsb_0 iopelopabsb_1 fopelopabsb_3 fopelopabsb_4 cvv cvv iopelopabsb_0 cv fopelopabsb_3 wceq iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_3 iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 wsb fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 fopelopabsb_3 wsbc iopelopabsb_0 cv fopelopabsb_3 wceq iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_3 iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab iopelopabsb_0 cv fopelopabsb_3 iopelopabsb_1 cv opeq1 eleq1d fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 fopelopabsb_3 dfsbcq2 bibi12d iopelopabsb_1 cv fopelopabsb_4 wceq fopelopabsb_3 iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 fopelopabsb_3 wsbc fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 wsbc iopelopabsb_1 cv fopelopabsb_4 wceq fopelopabsb_3 iopelopabsb_1 cv cop fopelopabsb_3 fopelopabsb_4 cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab iopelopabsb_1 cv fopelopabsb_4 fopelopabsb_3 opeq2 eleq1d iopelopabsb_1 cv fopelopabsb_4 wceq fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_0 fopelopabsb_2 fopelopabsb_4 wsbc fopelopabsb_1 fopelopabsb_3 fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 fopelopabsb_4 dfsbcq2 sbcbidv bibi12d fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb wb iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 wsb wb fopelopabsb_1 iopelopabsb_0 iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 wsb fopelopabsb_1 fopelopabsb_1 iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 nfopab1 nfel2 fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 nfs1v nfbi fopelopabsb_1 iopelopabsb_0 weq fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 wsb fopelopabsb_1 iopelopabsb_0 weq fopelopabsb_1 cv iopelopabsb_1 cv cop iopelopabsb_0 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab fopelopabsb_1 cv iopelopabsb_0 cv iopelopabsb_1 cv opeq1 eleq1d fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_1 iopelopabsb_0 sbequ12 bibi12d fopelopabsb_1 cv fopelopabsb_2 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 wb fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb wb fopelopabsb_2 iopelopabsb_1 fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_2 fopelopabsb_2 fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 nfopab2 nfel2 fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 nfs1v nfbi fopelopabsb_2 iopelopabsb_1 weq fopelopabsb_1 cv fopelopabsb_2 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab wcel fopelopabsb_0 fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 wsb fopelopabsb_2 iopelopabsb_1 weq fopelopabsb_1 cv fopelopabsb_2 cv cop fopelopabsb_1 cv iopelopabsb_1 cv cop fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 copab fopelopabsb_2 cv iopelopabsb_1 cv fopelopabsb_1 cv opeq2 eleq1d fopelopabsb_0 fopelopabsb_2 iopelopabsb_1 sbequ12 bibi12d fopelopabsb_0 fopelopabsb_1 fopelopabsb_2 opabid chvar chvar vtocl2g pm5.21nii $.
$}
$( The law of concretion in terms of substitutions.  (Contributed by NM,
       17-Mar-2008.) $)
${
	$d x y $.
	$d x B $.
	fbrabsb_0 $f wff ph $.
	fbrabsb_1 $f set x $.
	fbrabsb_2 $f set y $.
	fbrabsb_3 $f class A $.
	fbrabsb_4 $f class B $.
	fbrabsb_5 $f class R $.
	ebrabsb_0 $e |- R = { <. x , y >. | ph } $.
	brabsb $p |- ( A R B <-> [. A / x ]. [. B / y ]. ph ) $= fbrabsb_3 fbrabsb_4 fbrabsb_5 wbr fbrabsb_3 fbrabsb_4 cop fbrabsb_5 wcel fbrabsb_3 fbrabsb_4 cop fbrabsb_0 fbrabsb_1 fbrabsb_2 copab wcel fbrabsb_0 fbrabsb_2 fbrabsb_4 wsbc fbrabsb_1 fbrabsb_3 wsbc fbrabsb_3 fbrabsb_4 fbrabsb_5 df-br fbrabsb_5 fbrabsb_0 fbrabsb_1 fbrabsb_2 copab fbrabsb_3 fbrabsb_4 cop ebrabsb_0 eleq2i fbrabsb_0 fbrabsb_1 fbrabsb_2 fbrabsb_3 fbrabsb_4 opelopabsb 3bitri $.
$}
$( Closed theorem form of ~ opelopab .  (Contributed by NM,
       19-Feb-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ch $.
	fopelopabt_0 $f wff ph $.
	fopelopabt_1 $f wff ps $.
	fopelopabt_2 $f wff ch $.
	fopelopabt_3 $f set x $.
	fopelopabt_4 $f set y $.
	fopelopabt_5 $f class A $.
	fopelopabt_6 $f class B $.
	fopelopabt_7 $f class V $.
	fopelopabt_8 $f class W $.
	opelopabt $p |- ( ( A. x A. y ( x = A -> ( ph <-> ps ) ) /\ A. x A. y ( y = B -> ( ps <-> ch ) ) /\ ( A e. V /\ B e. W ) ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) ) $= fopelopabt_5 fopelopabt_6 cop fopelopabt_0 fopelopabt_3 fopelopabt_4 copab wcel fopelopabt_5 fopelopabt_6 cop fopelopabt_3 cv fopelopabt_4 cv cop wceq fopelopabt_0 wa fopelopabt_4 wex fopelopabt_3 wex fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_5 fopelopabt_7 wcel fopelopabt_6 fopelopabt_8 wcel wa w3a fopelopabt_2 fopelopabt_0 fopelopabt_3 fopelopabt_4 fopelopabt_5 fopelopabt_6 cop elopab fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_5 fopelopabt_7 wcel fopelopabt_6 fopelopabt_8 wcel wa fopelopabt_5 fopelopabt_6 cop fopelopabt_3 cv fopelopabt_4 cv cop wceq fopelopabt_0 wa fopelopabt_4 wex fopelopabt_3 wex fopelopabt_2 wb fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi fopelopabt_4 wal fopelopabt_3 wal wa fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_4 cv fopelopabt_6 wceq wa fopelopabt_0 fopelopabt_2 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_5 fopelopabt_7 wcel fopelopabt_6 fopelopabt_8 wcel wa fopelopabt_5 fopelopabt_6 cop fopelopabt_3 cv fopelopabt_4 cv cop wceq fopelopabt_0 wa fopelopabt_4 wex fopelopabt_3 wex fopelopabt_2 wb fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi fopelopabt_4 wal fopelopabt_3 wal wa fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi wa fopelopabt_4 wal fopelopabt_3 wal fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_4 cv fopelopabt_6 wceq wa fopelopabt_0 fopelopabt_2 wb wi fopelopabt_4 wal fopelopabt_3 wal fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi fopelopabt_3 fopelopabt_4 19.26-2 fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi wa fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_4 cv fopelopabt_6 wceq wa fopelopabt_0 fopelopabt_2 wb wi fopelopabt_3 fopelopabt_4 fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb wi fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb wi wa fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_4 cv fopelopabt_6 wceq wa fopelopabt_0 fopelopabt_1 wb fopelopabt_1 fopelopabt_2 wb wa fopelopabt_0 fopelopabt_2 wb fopelopabt_3 cv fopelopabt_5 wceq fopelopabt_0 fopelopabt_1 wb fopelopabt_4 cv fopelopabt_6 wceq fopelopabt_1 fopelopabt_2 wb prth fopelopabt_0 fopelopabt_1 fopelopabt_2 bitr syl6 2alimi sylbir fopelopabt_0 fopelopabt_2 fopelopabt_3 fopelopabt_4 fopelopabt_5 fopelopabt_6 fopelopabt_7 fopelopabt_8 copsex2t sylan 3impa syl5bb $.
$}
$( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       Mario Carneiro, 19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fopelopabga_0 $f wff ph $.
	fopelopabga_1 $f wff ps $.
	fopelopabga_2 $f set x $.
	fopelopabga_3 $f set y $.
	fopelopabga_4 $f class A $.
	fopelopabga_5 $f class B $.
	fopelopabga_6 $f class V $.
	fopelopabga_7 $f class W $.
	eopelopabga_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	opelopabga $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) ) $= fopelopabga_4 fopelopabga_5 cop fopelopabga_0 fopelopabga_2 fopelopabga_3 copab wcel fopelopabga_4 fopelopabga_5 cop fopelopabga_2 cv fopelopabga_3 cv cop wceq fopelopabga_0 wa fopelopabga_3 wex fopelopabga_2 wex fopelopabga_4 fopelopabga_6 wcel fopelopabga_5 fopelopabga_7 wcel wa fopelopabga_1 fopelopabga_0 fopelopabga_2 fopelopabga_3 fopelopabga_4 fopelopabga_5 cop elopab fopelopabga_0 fopelopabga_1 fopelopabga_2 fopelopabga_3 fopelopabga_4 fopelopabga_5 fopelopabga_6 fopelopabga_7 eopelopabga_0 copsex2g syl5bb $.
$}
$( The law of concretion for a binary relation.  (Contributed by Mario
         Carneiro, 19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fbrabga_0 $f wff ph $.
	fbrabga_1 $f wff ps $.
	fbrabga_2 $f set x $.
	fbrabga_3 $f set y $.
	fbrabga_4 $f class A $.
	fbrabga_5 $f class B $.
	fbrabga_6 $f class R $.
	fbrabga_7 $f class V $.
	fbrabga_8 $f class W $.
	ebrabga_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	ebrabga_1 $e |- R = { <. x , y >. | ph } $.
	brabga $p |- ( ( A e. V /\ B e. W ) -> ( A R B <-> ps ) ) $= fbrabga_4 fbrabga_5 fbrabga_6 wbr fbrabga_4 fbrabga_5 cop fbrabga_0 fbrabga_2 fbrabga_3 copab wcel fbrabga_4 fbrabga_7 wcel fbrabga_5 fbrabga_8 wcel wa fbrabga_1 fbrabga_4 fbrabga_5 fbrabga_6 wbr fbrabga_4 fbrabga_5 cop fbrabga_6 wcel fbrabga_4 fbrabga_5 cop fbrabga_0 fbrabga_2 fbrabga_3 copab wcel fbrabga_4 fbrabga_5 fbrabga_6 df-br fbrabga_6 fbrabga_0 fbrabga_2 fbrabga_3 copab fbrabga_4 fbrabga_5 cop ebrabga_1 eleq2i bitri fbrabga_0 fbrabga_1 fbrabga_2 fbrabga_3 fbrabga_4 fbrabga_5 fbrabga_7 fbrabga_8 ebrabga_0 opelopabga syl5bb $.
$}
$( Ordered pair membership in an ordered pair class abstraction.
       (Contributed by Mario Carneiro, 19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	$d x y C $.
	$d x y D $.
	fopelopab2a_0 $f wff ph $.
	fopelopab2a_1 $f wff ps $.
	fopelopab2a_2 $f set x $.
	fopelopab2a_3 $f set y $.
	fopelopab2a_4 $f class A $.
	fopelopab2a_5 $f class B $.
	fopelopab2a_6 $f class C $.
	fopelopab2a_7 $f class D $.
	eopelopab2a_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	opelopab2a $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ps ) ) $= fopelopab2a_4 fopelopab2a_6 wcel fopelopab2a_5 fopelopab2a_7 wcel wa fopelopab2a_4 fopelopab2a_5 cop fopelopab2a_2 cv fopelopab2a_6 wcel fopelopab2a_3 cv fopelopab2a_7 wcel wa fopelopab2a_0 wa fopelopab2a_2 fopelopab2a_3 copab wcel fopelopab2a_1 fopelopab2a_2 cv fopelopab2a_6 wcel fopelopab2a_3 cv fopelopab2a_7 wcel wa fopelopab2a_0 wa fopelopab2a_4 fopelopab2a_6 wcel fopelopab2a_5 fopelopab2a_7 wcel wa fopelopab2a_1 wa fopelopab2a_2 fopelopab2a_3 fopelopab2a_4 fopelopab2a_5 fopelopab2a_6 fopelopab2a_7 fopelopab2a_2 cv fopelopab2a_4 wceq fopelopab2a_3 cv fopelopab2a_5 wceq wa fopelopab2a_2 cv fopelopab2a_6 wcel fopelopab2a_3 cv fopelopab2a_7 wcel wa fopelopab2a_4 fopelopab2a_6 wcel fopelopab2a_5 fopelopab2a_7 wcel wa fopelopab2a_0 fopelopab2a_1 fopelopab2a_2 cv fopelopab2a_4 wceq fopelopab2a_2 cv fopelopab2a_6 wcel fopelopab2a_4 fopelopab2a_6 wcel fopelopab2a_3 cv fopelopab2a_5 wceq fopelopab2a_3 cv fopelopab2a_7 wcel fopelopab2a_5 fopelopab2a_7 wcel fopelopab2a_2 cv fopelopab2a_4 fopelopab2a_6 eleq1 fopelopab2a_3 cv fopelopab2a_5 fopelopab2a_7 eleq1 bi2anan9 eopelopab2a_0 anbi12d opelopabga bianabs $.
$}
$( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       Mario Carneiro, 19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fopelopaba_0 $f wff ph $.
	fopelopaba_1 $f wff ps $.
	fopelopaba_2 $f set x $.
	fopelopaba_3 $f set y $.
	fopelopaba_4 $f class A $.
	fopelopaba_5 $f class B $.
	eopelopaba_0 $e |- A e. _V $.
	eopelopaba_1 $e |- B e. _V $.
	eopelopaba_2 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	opelopaba $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) $= fopelopaba_4 cvv wcel fopelopaba_5 cvv wcel fopelopaba_4 fopelopaba_5 cop fopelopaba_0 fopelopaba_2 fopelopaba_3 copab wcel fopelopaba_1 wb eopelopaba_0 eopelopaba_1 fopelopaba_0 fopelopaba_1 fopelopaba_2 fopelopaba_3 fopelopaba_4 fopelopaba_5 cvv cvv eopelopaba_2 opelopabga mp2an $.
$}
$( The law of concretion for a binary relation.  (Contributed by NM,
         19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ps $.
	fbraba_0 $f wff ph $.
	fbraba_1 $f wff ps $.
	fbraba_2 $f set x $.
	fbraba_3 $f set y $.
	fbraba_4 $f class A $.
	fbraba_5 $f class B $.
	fbraba_6 $f class R $.
	ebraba_0 $e |- A e. _V $.
	ebraba_1 $e |- B e. _V $.
	ebraba_2 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	ebraba_3 $e |- R = { <. x , y >. | ph } $.
	braba $p |- ( A R B <-> ps ) $= fbraba_4 cvv wcel fbraba_5 cvv wcel fbraba_4 fbraba_5 fbraba_6 wbr fbraba_1 wb ebraba_0 ebraba_1 fbraba_0 fbraba_1 fbraba_2 fbraba_3 fbraba_4 fbraba_5 fbraba_6 cvv cvv ebraba_2 ebraba_3 brabga mp2an $.
$}
$( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       NM, 28-May-1995.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ch $.
	fopelopabg_0 $f wff ph $.
	fopelopabg_1 $f wff ps $.
	fopelopabg_2 $f wff ch $.
	fopelopabg_3 $f set x $.
	fopelopabg_4 $f set y $.
	fopelopabg_5 $f class A $.
	fopelopabg_6 $f class B $.
	fopelopabg_7 $f class V $.
	fopelopabg_8 $f class W $.
	eopelopabg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eopelopabg_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	opelopabg $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) ) $= fopelopabg_0 fopelopabg_2 fopelopabg_3 fopelopabg_4 fopelopabg_5 fopelopabg_6 fopelopabg_7 fopelopabg_8 fopelopabg_3 cv fopelopabg_5 wceq fopelopabg_0 fopelopabg_1 fopelopabg_4 cv fopelopabg_6 wceq fopelopabg_2 eopelopabg_0 eopelopabg_1 sylan9bb opelopabga $.
$}
$( The law of concretion for a binary relation.  (Contributed by NM,
         16-Aug-1999.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ch $.
	fbrabg_0 $f wff ph $.
	fbrabg_1 $f wff ps $.
	fbrabg_2 $f wff ch $.
	fbrabg_3 $f set x $.
	fbrabg_4 $f set y $.
	fbrabg_5 $f class A $.
	fbrabg_6 $f class B $.
	fbrabg_7 $f class C $.
	fbrabg_8 $f class D $.
	fbrabg_9 $f class R $.
	ebrabg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ebrabg_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	ebrabg_2 $e |- R = { <. x , y >. | ph } $.
	brabg $p |- ( ( A e. C /\ B e. D ) -> ( A R B <-> ch ) ) $= fbrabg_0 fbrabg_2 fbrabg_3 fbrabg_4 fbrabg_5 fbrabg_6 fbrabg_9 fbrabg_7 fbrabg_8 fbrabg_3 cv fbrabg_5 wceq fbrabg_0 fbrabg_1 fbrabg_4 cv fbrabg_6 wceq fbrabg_2 ebrabg_0 ebrabg_1 sylan9bb ebrabg_2 brabga $.
$}
$( Ordered pair membership in an ordered pair class abstraction.
       (Contributed by NM, 14-Oct-2007.)  (Revised by Mario Carneiro,
       19-Dec-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y ch $.
	fopelopab2_0 $f wff ph $.
	fopelopab2_1 $f wff ps $.
	fopelopab2_2 $f wff ch $.
	fopelopab2_3 $f set x $.
	fopelopab2_4 $f set y $.
	fopelopab2_5 $f class A $.
	fopelopab2_6 $f class B $.
	fopelopab2_7 $f class C $.
	fopelopab2_8 $f class D $.
	eopelopab2_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eopelopab2_1 $e |- ( y = B -> ( ps <-> ch ) ) $.
	opelopab2 $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ch ) ) $= fopelopab2_0 fopelopab2_2 fopelopab2_3 fopelopab2_4 fopelopab2_5 fopelopab2_6 fopelopab2_7 fopelopab2_8 fopelopab2_3 cv fopelopab2_5 wceq fopelopab2_0 fopelopab2_1 fopelopab2_4 cv fopelopab2_6 wceq fopelopab2_2 eopelopab2_0 eopelopab2_1 sylan9bb opelopab2a $.
$}
$( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       NM, 16-May-1995.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ch $.
	fopelopab_0 $f wff ph $.
	fopelopab_1 $f wff ps $.
	fopelopab_2 $f wff ch $.
	fopelopab_3 $f set x $.
	fopelopab_4 $f set y $.
	fopelopab_5 $f class A $.
	fopelopab_6 $f class B $.
	eopelopab_0 $e |- A e. _V $.
	eopelopab_1 $e |- B e. _V $.
	eopelopab_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eopelopab_3 $e |- ( y = B -> ( ps <-> ch ) ) $.
	opelopab $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) $= fopelopab_5 cvv wcel fopelopab_6 cvv wcel fopelopab_5 fopelopab_6 cop fopelopab_0 fopelopab_3 fopelopab_4 copab wcel fopelopab_2 wb eopelopab_0 eopelopab_1 fopelopab_0 fopelopab_1 fopelopab_2 fopelopab_3 fopelopab_4 fopelopab_5 fopelopab_6 cvv cvv eopelopab_2 eopelopab_3 opelopabg mp2an $.
$}
$( The law of concretion for a binary relation.  (Contributed by NM,
         16-Aug-1999.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ch $.
	fbrab_0 $f wff ph $.
	fbrab_1 $f wff ps $.
	fbrab_2 $f wff ch $.
	fbrab_3 $f set x $.
	fbrab_4 $f set y $.
	fbrab_5 $f class A $.
	fbrab_6 $f class B $.
	fbrab_7 $f class R $.
	ebrab_0 $e |- A e. _V $.
	ebrab_1 $e |- B e. _V $.
	ebrab_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ebrab_3 $e |- ( y = B -> ( ps <-> ch ) ) $.
	ebrab_4 $e |- R = { <. x , y >. | ph } $.
	brab $p |- ( A R B <-> ch ) $= fbrab_5 cvv wcel fbrab_6 cvv wcel fbrab_5 fbrab_6 fbrab_7 wbr fbrab_2 wb ebrab_0 ebrab_1 fbrab_0 fbrab_1 fbrab_2 fbrab_3 fbrab_4 fbrab_5 fbrab_6 cvv cvv fbrab_7 ebrab_2 ebrab_3 ebrab_4 brabg mp2an $.
$}
$( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  This version of
       ~ opelopab uses bound-variable hypotheses in place of distinct variable
       conditions."  (Contributed by Mario Carneiro, 19-Dec-2013.)  (Proof
       shortened by Mario Carneiro, 18-Nov-2016.) $)
${
	$d x y A $.
	$d x y B $.
	fopelopabaf_0 $f wff ph $.
	fopelopabaf_1 $f wff ps $.
	fopelopabaf_2 $f set x $.
	fopelopabaf_3 $f set y $.
	fopelopabaf_4 $f class A $.
	fopelopabaf_5 $f class B $.
	eopelopabaf_0 $e |- F/ x ps $.
	eopelopabaf_1 $e |- F/ y ps $.
	eopelopabaf_2 $e |- A e. _V $.
	eopelopabaf_3 $e |- B e. _V $.
	eopelopabaf_4 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	opelopabaf $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) $= fopelopabaf_4 fopelopabaf_5 cop fopelopabaf_0 fopelopabaf_2 fopelopabaf_3 copab wcel fopelopabaf_0 fopelopabaf_3 fopelopabaf_5 wsbc fopelopabaf_2 fopelopabaf_4 wsbc fopelopabaf_1 fopelopabaf_0 fopelopabaf_2 fopelopabaf_3 fopelopabaf_4 fopelopabaf_5 opelopabsb fopelopabaf_4 cvv wcel fopelopabaf_5 cvv wcel fopelopabaf_0 fopelopabaf_3 fopelopabaf_5 wsbc fopelopabaf_2 fopelopabaf_4 wsbc fopelopabaf_1 wb eopelopabaf_2 eopelopabaf_3 fopelopabaf_0 fopelopabaf_1 fopelopabaf_2 fopelopabaf_3 fopelopabaf_4 fopelopabaf_5 cvv cvv eopelopabaf_0 eopelopabaf_1 fopelopabaf_5 cvv wcel fopelopabaf_2 nfv eopelopabaf_4 sbc2iegf mp2an bitri $.
$}
$( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  This version of
       ~ opelopab uses bound-variable hypotheses in place of distinct variable
       conditions."  (Contributed by NM, 19-Dec-2008.) $)
${
	$d x y A $.
	$d x y B $.
	fopelopabf_0 $f wff ph $.
	fopelopabf_1 $f wff ps $.
	fopelopabf_2 $f wff ch $.
	fopelopabf_3 $f set x $.
	fopelopabf_4 $f set y $.
	fopelopabf_5 $f class A $.
	fopelopabf_6 $f class B $.
	eopelopabf_0 $e |- F/ x ps $.
	eopelopabf_1 $e |- F/ y ch $.
	eopelopabf_2 $e |- A e. _V $.
	eopelopabf_3 $e |- B e. _V $.
	eopelopabf_4 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eopelopabf_5 $e |- ( y = B -> ( ps <-> ch ) ) $.
	opelopabf $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) $= fopelopabf_5 fopelopabf_6 cop fopelopabf_0 fopelopabf_3 fopelopabf_4 copab wcel fopelopabf_0 fopelopabf_4 fopelopabf_6 wsbc fopelopabf_3 fopelopabf_5 wsbc fopelopabf_1 fopelopabf_4 fopelopabf_6 wsbc fopelopabf_2 fopelopabf_0 fopelopabf_3 fopelopabf_4 fopelopabf_5 fopelopabf_6 opelopabsb fopelopabf_5 cvv wcel fopelopabf_0 fopelopabf_4 fopelopabf_6 wsbc fopelopabf_3 fopelopabf_5 wsbc fopelopabf_1 fopelopabf_4 fopelopabf_6 wsbc wb eopelopabf_2 fopelopabf_0 fopelopabf_4 fopelopabf_6 wsbc fopelopabf_1 fopelopabf_4 fopelopabf_6 wsbc fopelopabf_3 fopelopabf_5 cvv fopelopabf_1 fopelopabf_3 fopelopabf_4 fopelopabf_6 fopelopabf_3 fopelopabf_6 nfcv eopelopabf_0 nfsbc fopelopabf_3 cv fopelopabf_5 wceq fopelopabf_0 fopelopabf_1 fopelopabf_4 fopelopabf_6 eopelopabf_4 sbcbidv sbciegf ax-mp fopelopabf_6 cvv wcel fopelopabf_1 fopelopabf_4 fopelopabf_6 wsbc fopelopabf_2 wb eopelopabf_3 fopelopabf_1 fopelopabf_2 fopelopabf_4 fopelopabf_6 cvv eopelopabf_1 eopelopabf_5 sbciegf ax-mp 3bitri $.
$}
$( Equivalence of ordered pair abstraction subclass and implication.
       (Contributed by NM, 27-Dec-1996.)  (Revised by Mario Carneiro,
       19-May-2013.) $)
${
	$d ph z $.
	$d ps z $.
	$d x z $.
	$d y z $.
	issopab2_0 $f set z $.
	fssopab2_0 $f wff ph $.
	fssopab2_1 $f wff ps $.
	fssopab2_2 $f set x $.
	fssopab2_3 $f set y $.
	ssopab2 $p |- ( A. x A. y ( ph -> ps ) -> { <. x , y >. | ph } C_ { <. x , y >. | ps } ) $= fssopab2_0 fssopab2_1 wi fssopab2_3 wal fssopab2_2 wal issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_0 wa fssopab2_3 wex fssopab2_2 wex issopab2_0 cab issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_1 wa fssopab2_3 wex fssopab2_2 wex issopab2_0 cab fssopab2_0 fssopab2_2 fssopab2_3 copab fssopab2_1 fssopab2_2 fssopab2_3 copab fssopab2_0 fssopab2_1 wi fssopab2_3 wal fssopab2_2 wal issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_0 wa fssopab2_3 wex fssopab2_2 wex issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_1 wa fssopab2_3 wex fssopab2_2 wex issopab2_0 fssopab2_0 fssopab2_1 wi fssopab2_3 wal fssopab2_2 wal issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_0 wa fssopab2_3 wex issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_1 wa fssopab2_3 wex fssopab2_2 fssopab2_0 fssopab2_1 wi fssopab2_3 wal fssopab2_2 nfa1 fssopab2_0 fssopab2_1 wi fssopab2_3 wal issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_0 wa fssopab2_3 wex issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_1 wa fssopab2_3 wex wi fssopab2_2 fssopab2_0 fssopab2_1 wi fssopab2_3 wal issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_0 wa issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_1 wa fssopab2_3 fssopab2_0 fssopab2_1 wi fssopab2_3 nfa1 fssopab2_0 fssopab2_1 wi fssopab2_3 wal fssopab2_0 fssopab2_1 issopab2_0 cv fssopab2_2 cv fssopab2_3 cv cop wceq fssopab2_0 fssopab2_1 wi fssopab2_3 sp anim2d eximd sps eximd ss2abdv fssopab2_0 fssopab2_2 fssopab2_3 issopab2_0 df-opab fssopab2_1 fssopab2_2 fssopab2_3 issopab2_0 df-opab 3sstr4g $.
$}
$( Equivalence of ordered pair abstraction subclass and implication.
       (Contributed by NM, 27-Dec-1996.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)
${
	fssopab2b_0 $f wff ph $.
	fssopab2b_1 $f wff ps $.
	fssopab2b_2 $f set x $.
	fssopab2b_3 $f set y $.
	ssopab2b $p |- ( { <. x , y >. | ph } C_ { <. x , y >. | ps } <-> A. x A. y ( ph -> ps ) ) $= fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab wss fssopab2b_0 fssopab2b_1 wi fssopab2b_3 wal fssopab2b_2 wal fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab wss fssopab2b_0 fssopab2b_1 wi fssopab2b_3 wal fssopab2b_2 fssopab2b_2 fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab fssopab2b_0 fssopab2b_2 fssopab2b_3 nfopab1 fssopab2b_1 fssopab2b_2 fssopab2b_3 nfopab1 nfss fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab wss fssopab2b_0 fssopab2b_1 wi fssopab2b_3 fssopab2b_3 fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab fssopab2b_0 fssopab2b_2 fssopab2b_3 nfopab2 fssopab2b_1 fssopab2b_2 fssopab2b_3 nfopab2 nfss fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab wss fssopab2b_2 cv fssopab2b_3 cv cop fssopab2b_0 fssopab2b_2 fssopab2b_3 copab wcel fssopab2b_2 cv fssopab2b_3 cv cop fssopab2b_1 fssopab2b_2 fssopab2b_3 copab wcel fssopab2b_0 fssopab2b_1 fssopab2b_0 fssopab2b_2 fssopab2b_3 copab fssopab2b_1 fssopab2b_2 fssopab2b_3 copab fssopab2b_2 cv fssopab2b_3 cv cop ssel fssopab2b_0 fssopab2b_2 fssopab2b_3 opabid fssopab2b_1 fssopab2b_2 fssopab2b_3 opabid 3imtr3g alrimi alrimi fssopab2b_0 fssopab2b_1 fssopab2b_2 fssopab2b_3 ssopab2 impbii $.
$}
$( Inference of ordered pair abstraction subclass from implication.
       (Contributed by NM, 5-Apr-1995.) $)
${
	fssopab2i_0 $f wff ph $.
	fssopab2i_1 $f wff ps $.
	fssopab2i_2 $f set x $.
	fssopab2i_3 $f set y $.
	essopab2i_0 $e |- ( ph -> ps ) $.
	ssopab2i $p |- { <. x , y >. | ph } C_ { <. x , y >. | ps } $= fssopab2i_0 fssopab2i_1 wi fssopab2i_3 wal fssopab2i_0 fssopab2i_2 fssopab2i_3 copab fssopab2i_1 fssopab2i_2 fssopab2i_3 copab wss fssopab2i_2 fssopab2i_0 fssopab2i_1 fssopab2i_2 fssopab2i_3 ssopab2 fssopab2i_0 fssopab2i_1 wi fssopab2i_3 essopab2i_0 ax-gen mpg $.
$}
$( Inference of ordered pair abstraction subclass from implication.
       (Contributed by NM, 19-Jan-2014.)  (Revised by Mario Carneiro,
       24-Jun-2014.) $)
${
	$d x ph $.
	$d y ph $.
	fssopab2dv_0 $f wff ph $.
	fssopab2dv_1 $f wff ps $.
	fssopab2dv_2 $f wff ch $.
	fssopab2dv_3 $f set x $.
	fssopab2dv_4 $f set y $.
	essopab2dv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ssopab2dv $p |- ( ph -> { <. x , y >. | ps } C_ { <. x , y >. | ch } ) $= fssopab2dv_0 fssopab2dv_1 fssopab2dv_2 wi fssopab2dv_4 wal fssopab2dv_3 wal fssopab2dv_1 fssopab2dv_3 fssopab2dv_4 copab fssopab2dv_2 fssopab2dv_3 fssopab2dv_4 copab wss fssopab2dv_0 fssopab2dv_1 fssopab2dv_2 wi fssopab2dv_3 fssopab2dv_4 essopab2dv_0 alrimivv fssopab2dv_1 fssopab2dv_2 fssopab2dv_3 fssopab2dv_4 ssopab2 syl $.
$}
$( Equivalence of ordered pair abstraction equality and biconditional.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
${
	feqopab2b_0 $f wff ph $.
	feqopab2b_1 $f wff ps $.
	feqopab2b_2 $f set x $.
	feqopab2b_3 $f set y $.
	eqopab2b $p |- ( { <. x , y >. | ph } = { <. x , y >. | ps } <-> A. x A. y ( ph <-> ps ) ) $= feqopab2b_0 feqopab2b_2 feqopab2b_3 copab feqopab2b_1 feqopab2b_2 feqopab2b_3 copab wss feqopab2b_1 feqopab2b_2 feqopab2b_3 copab feqopab2b_0 feqopab2b_2 feqopab2b_3 copab wss wa feqopab2b_0 feqopab2b_1 wi feqopab2b_3 wal feqopab2b_2 wal feqopab2b_1 feqopab2b_0 wi feqopab2b_3 wal feqopab2b_2 wal wa feqopab2b_0 feqopab2b_2 feqopab2b_3 copab feqopab2b_1 feqopab2b_2 feqopab2b_3 copab wceq feqopab2b_0 feqopab2b_1 wb feqopab2b_3 wal feqopab2b_2 wal feqopab2b_0 feqopab2b_2 feqopab2b_3 copab feqopab2b_1 feqopab2b_2 feqopab2b_3 copab wss feqopab2b_0 feqopab2b_1 wi feqopab2b_3 wal feqopab2b_2 wal feqopab2b_1 feqopab2b_2 feqopab2b_3 copab feqopab2b_0 feqopab2b_2 feqopab2b_3 copab wss feqopab2b_1 feqopab2b_0 wi feqopab2b_3 wal feqopab2b_2 wal feqopab2b_0 feqopab2b_1 feqopab2b_2 feqopab2b_3 ssopab2b feqopab2b_1 feqopab2b_0 feqopab2b_2 feqopab2b_3 ssopab2b anbi12i feqopab2b_0 feqopab2b_2 feqopab2b_3 copab feqopab2b_1 feqopab2b_2 feqopab2b_3 copab eqss feqopab2b_0 feqopab2b_1 feqopab2b_2 feqopab2b_3 2albiim 3bitr4i $.
$}
$( Non-empty ordered pair class abstraction.  (Contributed by NM,
       10-Oct-2007.) $)
${
	$d z ph $.
	$d z x $.
	$d z y $.
	iopabn0_0 $f set z $.
	fopabn0_0 $f wff ph $.
	fopabn0_1 $f set x $.
	fopabn0_2 $f set y $.
	opabn0 $p |- ( { <. x , y >. | ph } =/= (/) <-> E. x E. y ph ) $= fopabn0_0 fopabn0_1 fopabn0_2 copab c0 wne iopabn0_0 cv fopabn0_0 fopabn0_1 fopabn0_2 copab wcel iopabn0_0 wex fopabn0_0 fopabn0_2 wex fopabn0_1 wex iopabn0_0 fopabn0_0 fopabn0_1 fopabn0_2 copab n0 iopabn0_0 cv fopabn0_0 fopabn0_1 fopabn0_2 copab wcel iopabn0_0 wex iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa fopabn0_2 wex fopabn0_1 wex iopabn0_0 wex fopabn0_0 fopabn0_2 wex fopabn0_1 wex iopabn0_0 cv fopabn0_0 fopabn0_1 fopabn0_2 copab wcel iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa fopabn0_2 wex fopabn0_1 wex iopabn0_0 fopabn0_0 fopabn0_1 fopabn0_2 iopabn0_0 cv elopab exbii iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa fopabn0_2 wex fopabn0_1 wex iopabn0_0 wex iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa iopabn0_0 wex fopabn0_2 wex fopabn0_1 wex fopabn0_0 fopabn0_2 wex fopabn0_1 wex iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa iopabn0_0 fopabn0_1 fopabn0_2 exrot3 iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa iopabn0_0 wex fopabn0_0 fopabn0_1 fopabn0_2 iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 wa iopabn0_0 wex iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq iopabn0_0 wex fopabn0_0 iopabn0_0 fopabn0_1 cv fopabn0_2 cv cop fopabn0_1 cv fopabn0_2 cv opex isseti iopabn0_0 cv fopabn0_1 cv fopabn0_2 cv cop wceq fopabn0_0 iopabn0_0 19.41v mpbiran 2exbii bitri bitri bitri $.
$}
$( Move indexed union inside an ordered-pair abstraction.  (Contributed by
       Stefan O'Rear, 20-Feb-2015.) $)
${
	$d ph w $.
	$d A w x $.
	$d A y $.
	$d w y z $.
	$d x z $.
	iiunopab_0 $f set w $.
	fiunopab_0 $f wff ph $.
	fiunopab_1 $f set x $.
	fiunopab_2 $f set y $.
	fiunopab_3 $f set z $.
	fiunopab_4 $f class A $.
	iunopab $p |- U_ z e. A { <. x , y >. | ph } = { <. x , y >. | E. z e. A ph } $= iiunopab_0 cv fiunopab_0 fiunopab_1 fiunopab_2 copab wcel fiunopab_3 fiunopab_4 wrex iiunopab_0 cab iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 wex fiunopab_1 wex iiunopab_0 cab fiunopab_3 fiunopab_4 fiunopab_0 fiunopab_1 fiunopab_2 copab ciun fiunopab_0 fiunopab_3 fiunopab_4 wrex fiunopab_1 fiunopab_2 copab iiunopab_0 cv fiunopab_0 fiunopab_1 fiunopab_2 copab wcel fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 wex fiunopab_1 wex iiunopab_0 iiunopab_0 cv fiunopab_0 fiunopab_1 fiunopab_2 copab wcel fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_1 wex fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 wex fiunopab_1 wex iiunopab_0 cv fiunopab_0 fiunopab_1 fiunopab_2 copab wcel iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_1 wex fiunopab_3 fiunopab_4 fiunopab_0 fiunopab_1 fiunopab_2 iiunopab_0 cv elopab rexbii iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_1 wex fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_3 fiunopab_4 wrex fiunopab_1 wex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 wex fiunopab_1 wex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_3 fiunopab_1 fiunopab_4 rexcom4 iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 wex fiunopab_1 iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_2 wex fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_3 fiunopab_4 wrex fiunopab_2 wex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 wex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_3 fiunopab_2 fiunopab_4 rexcom4 iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 wa fiunopab_3 fiunopab_4 wrex iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 wrex wa fiunopab_2 iiunopab_0 cv fiunopab_1 cv fiunopab_2 cv cop wceq fiunopab_0 fiunopab_3 fiunopab_4 r19.42v exbii bitri exbii bitri bitri abbii fiunopab_3 iiunopab_0 fiunopab_4 fiunopab_0 fiunopab_1 fiunopab_2 copab df-iun fiunopab_0 fiunopab_3 fiunopab_4 wrex fiunopab_1 fiunopab_2 iiunopab_0 df-opab 3eqtr4i $.
$}

