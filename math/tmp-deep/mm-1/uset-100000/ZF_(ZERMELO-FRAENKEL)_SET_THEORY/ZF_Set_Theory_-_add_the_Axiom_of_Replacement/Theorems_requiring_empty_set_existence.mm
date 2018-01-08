$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Theorems_requiring_subset_and_intersection_existence.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Theorems requiring empty set existence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Construct, from any class ` A ` , a set equal to it when the class
       exists and equal to the empty set when the class is proper.  This
       theorem shows that the constructed set always exists.  (Contributed by
       NM, 16-Oct-2003.) */

$)
${
	$d x A $.
	fclass2set_0 $f set x $.
	fclass2set_1 $f class A $.
	class2set $p |- { x e. A | A e. _V } e. _V $= fclass2set_1 cvv wcel fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 crab cvv wcel fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 cvv rabexg fclass2set_1 cvv wcel wn fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 crab c0 cvv fclass2set_1 cvv wcel wn fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 wrex wn fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 crab c0 wceq fclass2set_1 cvv wcel wn fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 fclass2set_1 cvv wcel wn fclass2set_0 sup_set_class fclass2set_1 wcel simpl nrexdv fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 wrex fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 crab c0 fclass2set_1 cvv wcel fclass2set_0 fclass2set_1 rabn0 necon1bbii sylib 0ex syl6eqel pm2.61i $.
$}
$( /* Equality theorem based on ~ class2set .  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Raph Levien, 30-Jun-2006.) */

$)
${
	$d x A $.
	fclass2seteq_0 $f set x $.
	fclass2seteq_1 $f class A $.
	fclass2seteq_2 $f class V $.
	class2seteq $p |- ( A e. V -> { x e. A | A e. _V } = A ) $= fclass2seteq_1 fclass2seteq_2 wcel fclass2seteq_1 cvv wcel fclass2seteq_1 cvv wcel fclass2seteq_0 fclass2seteq_1 crab fclass2seteq_1 wceq fclass2seteq_1 fclass2seteq_2 elex fclass2seteq_1 cvv wcel fclass2seteq_1 fclass2seteq_1 cvv wcel fclass2seteq_0 fclass2seteq_1 crab fclass2seteq_1 cvv wcel fclass2seteq_1 cvv wcel fclass2seteq_0 fclass2seteq_1 wral fclass2seteq_1 fclass2seteq_1 cvv wcel fclass2seteq_0 fclass2seteq_1 crab wceq fclass2seteq_1 cvv wcel fclass2seteq_1 cvv wcel fclass2seteq_0 fclass2seteq_1 fclass2seteq_1 cvv wcel fclass2seteq_0 sup_set_class fclass2seteq_1 wcel ax-1 ralrimiv fclass2seteq_1 cvv wcel fclass2seteq_0 fclass2seteq_1 rabid2 sylibr eqcomd syl $.
$}
$( /* Every power class contains the empty set.  (Contributed by NM,
     25-Oct-2007.) */

$)
${
	f0elpw_0 $f class A $.
	0elpw $p |- (/) e. ~P A $= c0 f0elpw_0 cpw wcel c0 f0elpw_0 wss f0elpw_0 0ss c0 f0elpw_0 0ex elpw mpbir $.
$}
$( /* The empty set and its power set are not equal.  (Contributed by NM,
     23-Dec-1993.) */

$)
${
	0nep0 $p |- (/) =/= { (/) } $= c0 csn c0 c0 0ex snnz necomi $.
$}
$( /* Something cannot be equal to both the null set and the power set of the
     null set.  (Contributed by NM, 30-Sep-2003.) */

$)
${
	f0inp0_0 $f class A $.
	0inp0 $p |- ( A = (/) -> -. A = { (/) } ) $= f0inp0_0 c0 wceq f0inp0_0 c0 csn f0inp0_0 c0 wceq f0inp0_0 c0 csn wne c0 c0 csn wne 0nep0 f0inp0_0 c0 c0 csn neeq1 mpbiri neneqd $.
$}
$( /* The removal of the empty set from a class does not affect its union.
     (Contributed by NM, 22-Mar-2004.) */

$)
${
	funidif0_0 $f class A $.
	unidif0 $p |- U. ( A \ { (/) } ) = U. A $= funidif0_0 c0 csn cdif cuni c0 funidif0_0 cuni cun funidif0_0 cuni c0 cun funidif0_0 cuni funidif0_0 c0 csn cdif cuni c0 csn funidif0_0 cun cuni c0 csn cuni funidif0_0 cuni cun c0 funidif0_0 cuni cun funidif0_0 c0 csn cdif c0 csn cun cuni funidif0_0 c0 csn cdif cuni c0 csn cuni cun c0 csn funidif0_0 cun cuni funidif0_0 c0 csn cdif cuni funidif0_0 c0 csn cdif c0 csn uniun c0 csn funidif0_0 cun funidif0_0 c0 csn cdif c0 csn cun funidif0_0 c0 csn cdif c0 csn cun funidif0_0 c0 csn cun c0 csn funidif0_0 cun funidif0_0 c0 csn undif1 funidif0_0 c0 csn uncom eqtr2i unieqi funidif0_0 c0 csn cdif cuni c0 csn cuni cun funidif0_0 c0 csn cdif cuni c0 cun funidif0_0 c0 csn cdif cuni c0 csn cuni c0 funidif0_0 c0 csn cdif cuni c0 0ex unisn uneq2i funidif0_0 c0 csn cdif cuni un0 eqtr2i 3eqtr4ri c0 csn funidif0_0 uniun c0 csn cuni c0 funidif0_0 cuni c0 0ex unisn uneq1i 3eqtri c0 funidif0_0 cuni uncom funidif0_0 cuni un0 3eqtri $.
$}
$( /* An indexed intersection of the empty set, with a non-empty index set, is
       empty.  (Contributed by NM, 20-Oct-2005.) */

$)
${
	$d x A $.
	fiin0_0 $f set x $.
	fiin0_1 $f class A $.
	iin0 $p |- ( A =/= (/) <-> |^|_ x e. A (/) = (/) ) $= fiin0_1 c0 wne fiin0_0 fiin0_1 c0 ciin c0 wceq fiin0_0 fiin0_1 c0 iinconst fiin0_0 fiin0_1 c0 ciin c0 wceq fiin0_1 c0 fiin0_1 c0 wceq fiin0_0 fiin0_1 c0 ciin c0 wceq fiin0_0 c0 c0 ciin c0 wceq fiin0_0 c0 c0 ciin c0 wceq cvv c0 wceq c0 cvv wcel cvv c0 wceq wn 0ex cvv c0 n0i ax-mp fiin0_0 c0 c0 ciin cvv c0 fiin0_0 c0 0iin eqeq1i mtbir fiin0_1 c0 wceq fiin0_0 fiin0_1 c0 ciin fiin0_0 c0 c0 ciin c0 fiin0_0 fiin0_1 c0 c0 iineq1 eqeq1d mtbiri necon2ai impbii $.
$}
$( /* In the Separation Scheme ~ zfauscl , we require that ` y ` not occur in
       ` ph ` (which can be generalized to "not be free in").  Here we show
       special cases of ` A ` and ` ph ` that result in a contradiction by
       violating this requirement.  (Contributed by NM, 8-Feb-2006.) */

$)
${
	$d x A $.
	fnotzfaus_0 $f wff ph $.
	fnotzfaus_1 $f set x $.
	fnotzfaus_2 $f set y $.
	fnotzfaus_3 $f class A $.
	enotzfaus_0 $e |- A = { (/) } $.
	enotzfaus_1 $e |- ( ph <-> -. x e. y ) $.
	notzfaus $p |- -. E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) $= fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb fnotzfaus_1 wal fnotzfaus_2 fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb wn fnotzfaus_1 wex fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb fnotzfaus_1 wal wn fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 wex fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb wn fnotzfaus_1 wex fnotzfaus_3 c0 wne fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 wex fnotzfaus_3 c0 csn c0 enotzfaus_0 c0 0ex snnz eqnetri fnotzfaus_1 fnotzfaus_3 n0 mpbi fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb wn fnotzfaus_1 fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wn wb fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb wn fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel wi fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wn fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel biimt fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel wi fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel wn wa fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel iman fnotzfaus_0 fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel wn fnotzfaus_1 sup_set_class fnotzfaus_3 wcel enotzfaus_1 anbi2i xchbinxr syl6bb fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa xor3 sylibr eximi ax-mp fnotzfaus_1 sup_set_class fnotzfaus_2 sup_set_class wcel fnotzfaus_1 sup_set_class fnotzfaus_3 wcel fnotzfaus_0 wa wb fnotzfaus_1 exnal mpbi nex $.
$}
$( /* The intersection of the universal class is empty.  (Contributed by NM,
     11-Sep-2008.) */

$)
${
	intv $p |- |^| _V = (/) $= c0 cvv wcel cvv cint c0 wceq 0ex cvv int0el ax-mp $.
$}
$( /* Two equivalent ways to express the Power Set Axiom.  Note that ~ ax-pow
       is not used by the proof.  (Contributed by NM, 22-Jun-2009.) */

$)
${
	$d x y z A $.
	faxpweq_0 $f set x $.
	faxpweq_1 $f set y $.
	faxpweq_2 $f set z $.
	faxpweq_3 $f class A $.
	eaxpweq_0 $e |- A e. _V $.
	axpweq $p |- ( ~P A e. _V <-> E. x A. y ( A. z ( z e. y -> z e. A ) -> y e. x ) ) $= faxpweq_3 cpw cvv wcel faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_0 wex faxpweq_2 sup_set_class faxpweq_1 sup_set_class wcel faxpweq_2 sup_set_class faxpweq_3 wcel wi faxpweq_2 wal faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_1 wal faxpweq_0 wex faxpweq_3 cpw cvv wcel faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_0 wex faxpweq_3 cpw cvv wcel faxpweq_3 cpw faxpweq_3 cpw cpw wcel faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_0 wex faxpweq_3 cpw cvv pwidg faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_3 cpw faxpweq_3 cpw cpw wcel faxpweq_0 faxpweq_3 cpw cvv faxpweq_0 sup_set_class faxpweq_3 cpw wceq faxpweq_0 sup_set_class cpw faxpweq_3 cpw cpw faxpweq_3 cpw faxpweq_0 sup_set_class faxpweq_3 cpw pweq eleq2d spcegv mpd faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_3 cpw cvv wcel faxpweq_0 faxpweq_3 cpw faxpweq_0 sup_set_class cpw elex exlimiv impbii faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_2 sup_set_class faxpweq_1 sup_set_class wcel faxpweq_2 sup_set_class faxpweq_3 wcel wi faxpweq_2 wal faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_1 wal faxpweq_0 faxpweq_3 cpw faxpweq_0 sup_set_class cpw wcel faxpweq_3 cpw faxpweq_0 sup_set_class wss faxpweq_2 sup_set_class faxpweq_1 sup_set_class wcel faxpweq_2 sup_set_class faxpweq_3 wcel wi faxpweq_2 wal faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_1 wal faxpweq_3 cpw faxpweq_0 sup_set_class faxpweq_0 vex elpw2 faxpweq_3 cpw faxpweq_0 sup_set_class wss faxpweq_1 sup_set_class faxpweq_3 wss faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_1 wal faxpweq_2 sup_set_class faxpweq_1 sup_set_class wcel faxpweq_2 sup_set_class faxpweq_3 wcel wi faxpweq_2 wal faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_1 wal faxpweq_1 faxpweq_3 faxpweq_0 sup_set_class pwss faxpweq_1 sup_set_class faxpweq_3 wss faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_2 sup_set_class faxpweq_1 sup_set_class wcel faxpweq_2 sup_set_class faxpweq_3 wcel wi faxpweq_2 wal faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel wi faxpweq_1 faxpweq_1 sup_set_class faxpweq_3 wss faxpweq_2 sup_set_class faxpweq_1 sup_set_class wcel faxpweq_2 sup_set_class faxpweq_3 wcel wi faxpweq_2 wal faxpweq_1 sup_set_class faxpweq_0 sup_set_class wcel faxpweq_2 faxpweq_1 sup_set_class faxpweq_3 dfss2 imbi1i albii bitri bitri exbii bitri $.
$}

