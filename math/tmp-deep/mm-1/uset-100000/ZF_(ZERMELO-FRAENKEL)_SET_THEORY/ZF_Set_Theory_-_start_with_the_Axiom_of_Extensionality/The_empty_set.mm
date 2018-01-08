$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_difference,_union,_and_intersection_of_two_classes.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           The empty set

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Declare the symbol for the empty or null set. */

$)
$c (/)  $.
$( /* null set */

$)
$( /* Extend class notation to include the empty set. */

$)
${
	c0 $a class (/) $.
$}
$( /* Define the empty set.  Special case of Exercise 4.10(o) of [Mendelson]
     p. 231.  For a more traditional definition, but requiring a dummy
     variable, see ~ dfnul2 .  (Contributed by NM, 5-Aug-1993.) */

$)
${
	df-nul $a |- (/) = ( _V \ _V ) $.
$}
$( /* Alternate definition of the empty set.  Definition 5.14 of [TakeutiZaring]
     p. 20.  (Contributed by NM, 26-Dec-1996.) */

$)
${
	fdfnul2_0 $f set x $.
	dfnul2 $p |- (/) = { x | -. x = x } $= fdfnul2_0 sup_set_class fdfnul2_0 sup_set_class wceq wn fdfnul2_0 c0 fdfnul2_0 sup_set_class c0 wcel fdfnul2_0 sup_set_class cvv cvv cdif wcel fdfnul2_0 sup_set_class cvv wcel fdfnul2_0 sup_set_class cvv wcel wn wa fdfnul2_0 sup_set_class fdfnul2_0 sup_set_class wceq wn c0 cvv cvv cdif fdfnul2_0 sup_set_class df-nul eleq2i fdfnul2_0 sup_set_class cvv cvv eldif fdfnul2_0 sup_set_class fdfnul2_0 sup_set_class wceq fdfnul2_0 sup_set_class cvv wcel fdfnul2_0 sup_set_class cvv wcel wn wa fdfnul2_0 sup_set_class fdfnul2_0 sup_set_class wceq fdfnul2_0 sup_set_class cvv wcel fdfnul2_0 sup_set_class cvv wcel wn wa wn fdfnul2_0 sup_set_class eqid fdfnul2_0 sup_set_class cvv wcel pm3.24 2th con2bii 3bitri abbi2i $.
$}
$( /* Alternate definition of the empty set.  (Contributed by NM,
     25-Mar-2004.) */

$)
${
	fdfnul3_0 $f set x $.
	fdfnul3_1 $f class A $.
	dfnul3 $p |- (/) = { x e. A | -. x e. A } $= fdfnul3_0 sup_set_class fdfnul3_0 sup_set_class wceq wn fdfnul3_0 cab fdfnul3_0 sup_set_class fdfnul3_1 wcel fdfnul3_0 sup_set_class fdfnul3_1 wcel wn wa fdfnul3_0 cab c0 fdfnul3_0 sup_set_class fdfnul3_1 wcel wn fdfnul3_0 fdfnul3_1 crab fdfnul3_0 sup_set_class fdfnul3_0 sup_set_class wceq wn fdfnul3_0 sup_set_class fdfnul3_1 wcel fdfnul3_0 sup_set_class fdfnul3_1 wcel wn wa fdfnul3_0 fdfnul3_0 sup_set_class fdfnul3_1 wcel fdfnul3_0 sup_set_class fdfnul3_1 wcel wn wa fdfnul3_0 sup_set_class fdfnul3_0 sup_set_class wceq fdfnul3_0 sup_set_class fdfnul3_1 wcel fdfnul3_0 sup_set_class fdfnul3_1 wcel wn wa wn fdfnul3_0 sup_set_class fdfnul3_0 sup_set_class wceq fdfnul3_0 sup_set_class fdfnul3_1 wcel pm3.24 fdfnul3_0 sup_set_class eqid 2th con1bii abbii fdfnul3_0 dfnul2 fdfnul3_0 sup_set_class fdfnul3_1 wcel wn fdfnul3_0 fdfnul3_1 df-rab 3eqtr4i $.
$}
$( /* The empty set has no elements.  Theorem 6.14 of [Quine] p. 44.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Mario Carneiro,
     1-Sep-2015.) */

$)
${
	fnoel_0 $f class A $.
	noel $p |- -. A e. (/) $= fnoel_0 c0 wcel fnoel_0 cvv cvv cdif wcel fnoel_0 cvv cvv cdif wcel fnoel_0 cvv wcel fnoel_0 cvv cvv eldifi fnoel_0 cvv cvv eldifn pm2.65i c0 cvv cvv cdif fnoel_0 df-nul eleq2i mtbir $.
$}
$( /* If a set has elements, it is not empty.  (Contributed by NM,
     31-Dec-1993.) */

$)
${
	fn0i_0 $f class A $.
	fn0i_1 $f class B $.
	n0i $p |- ( B e. A -> -. A = (/) ) $= fn0i_0 c0 wceq fn0i_1 fn0i_0 wcel fn0i_0 c0 wceq fn0i_1 fn0i_0 wcel fn0i_1 c0 wcel fn0i_1 noel fn0i_0 c0 fn0i_1 eleq2 mtbiri con2i $.
$}
$( /* If a set has elements, it is not empty.  (Contributed by NM,
     31-Dec-1993.) */

$)
${
	fne0i_0 $f class A $.
	fne0i_1 $f class B $.
	ne0i $p |- ( B e. A -> A =/= (/) ) $= fne0i_1 fne0i_0 wcel fne0i_0 c0 wceq wn fne0i_0 c0 wne fne0i_0 fne0i_1 n0i fne0i_0 c0 df-ne sylibr $.
$}
$( /* The universal class is not equal to the empty set.  (Contributed by NM,
     11-Sep-2008.) */

$)
${
	ivn0_0 $f set x $.
	vn0 $p |- _V =/= (/) $= ivn0_0 sup_set_class cvv wcel cvv c0 wne ivn0_0 vex cvv ivn0_0 sup_set_class ne0i ax-mp $.
$}
$( /* A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  This version of ~ n0 requires only that ` x `
       not be free in, rather than not occur in, ` A ` .  (Contributed by NM,
       17-Oct-2003.) */

$)
${
	fn0f_0 $f set x $.
	fn0f_1 $f class A $.
	en0f_0 $e |- F/_ x A $.
	n0f $p |- ( A =/= (/) <-> E. x x e. A ) $= fn0f_1 c0 wne fn0f_0 sup_set_class fn0f_1 wcel wn fn0f_0 wal wn fn0f_0 sup_set_class fn0f_1 wcel fn0f_0 wex fn0f_0 sup_set_class fn0f_1 wcel wn fn0f_0 wal fn0f_1 c0 fn0f_1 c0 wceq fn0f_0 sup_set_class fn0f_1 wcel fn0f_0 sup_set_class c0 wcel wb fn0f_0 wal fn0f_0 sup_set_class fn0f_1 wcel wn fn0f_0 wal fn0f_0 fn0f_1 c0 en0f_0 fn0f_0 c0 nfcv cleqf fn0f_0 sup_set_class fn0f_1 wcel wn fn0f_0 sup_set_class fn0f_1 wcel fn0f_0 sup_set_class c0 wcel wb fn0f_0 fn0f_0 sup_set_class c0 wcel fn0f_0 sup_set_class fn0f_1 wcel fn0f_0 sup_set_class noel nbn albii bitr4i necon3abii fn0f_0 sup_set_class fn0f_1 wcel fn0f_0 df-ex bitr4i $.
$}
$( /* A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  (Contributed by NM, 29-Sep-2006.) */

$)
${
	$d x A $.
	fn0_0 $f set x $.
	fn0_1 $f class A $.
	n0 $p |- ( A =/= (/) <-> E. x x e. A ) $= fn0_0 fn0_1 fn0_0 fn0_1 nfcv n0f $.
$}
$( /* A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	fneq0_0 $f set x $.
	fneq0_1 $f class A $.
	neq0 $p |- ( -. A = (/) <-> E. x x e. A ) $= fneq0_1 c0 wceq wn fneq0_1 c0 wne fneq0_0 sup_set_class fneq0_1 wcel fneq0_0 wex fneq0_1 c0 df-ne fneq0_0 fneq0_1 n0 bitr3i $.
$}
$( /* Restricted existence deduced from non-empty class.  (Contributed by NM,
       1-Feb-2012.) */

$)
${
	$d x A $.
	$d x ph $.
	freximdva0_0 $f wff ph $.
	freximdva0_1 $f wff ps $.
	freximdva0_2 $f set x $.
	freximdva0_3 $f class A $.
	ereximdva0_0 $e |- ( ( ph /\ x e. A ) -> ps ) $.
	reximdva0 $p |- ( ( ph /\ A =/= (/) ) -> E. x e. A ps ) $= freximdva0_0 freximdva0_3 c0 wne wa freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_1 wa freximdva0_2 wex freximdva0_1 freximdva0_2 freximdva0_3 wrex freximdva0_3 c0 wne freximdva0_0 freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_2 wex freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_1 wa freximdva0_2 wex freximdva0_2 freximdva0_3 n0 freximdva0_0 freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_2 wex freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_1 wa freximdva0_2 wex freximdva0_0 freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_1 wa freximdva0_2 freximdva0_0 freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_1 freximdva0_0 freximdva0_2 sup_set_class freximdva0_3 wcel freximdva0_1 ereximdva0_0 ex ancld eximdv imp sylan2b freximdva0_1 freximdva0_2 freximdva0_3 df-rex sylibr $.
$}
$( /* A case of equivalence of "at most one" and "only one".  (Contributed by
       FL, 6-Dec-2010.) */

$)
${
	$d A x $.
	fn0moeu_0 $f set x $.
	fn0moeu_1 $f class A $.
	n0moeu $p |- ( A =/= (/) -> ( E* x x e. A <-> E! x x e. A ) ) $= fn0moeu_1 c0 wne fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 wmo fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 wex fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 wmo wa fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 weu fn0moeu_1 c0 wne fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 wex fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 wmo fn0moeu_1 c0 wne fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 wex fn0moeu_0 fn0moeu_1 n0 biimpi biantrurd fn0moeu_0 sup_set_class fn0moeu_1 wcel fn0moeu_0 eu5 syl6bbr $.
$}
$( /* Vacuous existential quantification is false.  (Contributed by NM,
     15-Oct-2003.) */

$)
${
	frex0_0 $f wff ph $.
	frex0_1 $f set x $.
	rex0 $p |- -. E. x e. (/) ph $= frex0_0 frex0_1 c0 frex0_1 sup_set_class c0 wcel frex0_0 wn frex0_1 sup_set_class noel pm2.21i nrex $.
$}
$( /* The empty set has no elements.  Theorem 2 of [Suppes] p. 22.
       (Contributed by NM, 29-Aug-1993.) */

$)
${
	$d x A $.
	feq0_0 $f set x $.
	feq0_1 $f class A $.
	eq0 $p |- ( A = (/) <-> A. x -. x e. A ) $= feq0_1 c0 wceq feq0_0 sup_set_class feq0_1 wcel wn feq0_0 wal feq0_1 c0 wceq wn feq0_0 sup_set_class feq0_1 wcel feq0_0 wex feq0_0 sup_set_class feq0_1 wcel wn feq0_0 wal wn feq0_0 feq0_1 neq0 feq0_0 sup_set_class feq0_1 wcel feq0_0 df-ex bitri con4bii $.
$}
$( /* The universe contains every set.  (Contributed by NM, 11-Sep-2006.) */

$)
${
	$d x A $.
	feqv_0 $f set x $.
	feqv_1 $f class A $.
	eqv $p |- ( A = _V <-> A. x x e. A ) $= feqv_1 cvv wceq feqv_0 sup_set_class feqv_1 wcel feqv_0 sup_set_class cvv wcel wb feqv_0 wal feqv_0 sup_set_class feqv_1 wcel feqv_0 wal feqv_0 feqv_1 cvv dfcleq feqv_0 sup_set_class feqv_1 wcel feqv_0 sup_set_class feqv_1 wcel feqv_0 sup_set_class cvv wcel wb feqv_0 feqv_0 sup_set_class cvv wcel feqv_0 sup_set_class feqv_1 wcel feqv_0 vex tbt albii bitr4i $.
$}
$( /* Membership of the empty set in another class.  (Contributed by NM,
       29-Jun-2004.) */

$)
${
	$d x A $.
	$d x y $.
	f0el_0 $f set x $.
	f0el_1 $f set y $.
	f0el_2 $f class A $.
	0el $p |- ( (/) e. A <-> E. x e. A A. y -. y e. x ) $= c0 f0el_2 wcel f0el_0 sup_set_class c0 wceq f0el_0 f0el_2 wrex f0el_1 sup_set_class f0el_0 sup_set_class wcel wn f0el_1 wal f0el_0 f0el_2 wrex f0el_0 c0 f0el_2 risset f0el_0 sup_set_class c0 wceq f0el_1 sup_set_class f0el_0 sup_set_class wcel wn f0el_1 wal f0el_0 f0el_2 f0el_1 f0el_0 sup_set_class eq0 rexbii bitri $.
$}
$( /* The class builder of a wff not containing the abstraction variable is
       either the universal class or the empty set.  (Contributed by Mario
       Carneiro, 29-Aug-2013.) */

$)
${
	$d x ph $.
	fabvor0_0 $f wff ph $.
	fabvor0_1 $f set x $.
	abvor0 $p |- ( { x | ph } = _V \/ { x | ph } = (/) ) $= fabvor0_0 fabvor0_1 cab cvv wceq fabvor0_0 fabvor0_1 cab c0 wceq fabvor0_0 fabvor0_1 cab cvv wceq wn fabvor0_0 wn fabvor0_0 fabvor0_1 cab c0 wceq fabvor0_0 fabvor0_0 fabvor0_1 cab cvv wceq fabvor0_0 fabvor0_0 fabvor0_1 cvv fabvor0_0 fabvor0_0 fabvor0_1 sup_set_class cvv wcel fabvor0_0 id fabvor0_1 sup_set_class cvv wcel fabvor0_0 fabvor0_1 vex a1i 2thd abbi1dv con3i fabvor0_0 wn fabvor0_0 fabvor0_1 c0 fabvor0_0 wn fabvor0_0 fabvor0_1 sup_set_class c0 wcel fabvor0_0 wn id fabvor0_1 sup_set_class c0 wcel wn fabvor0_0 wn fabvor0_1 sup_set_class noel a1i 2falsed abbi1dv syl orri $.
$}
$( /* Nonempty class abstraction.  (Contributed by NM, 26-Dec-1996.)  (Proof
       shortened by Mario Carneiro, 11-Nov-2016.) */

$)
${
	fabn0_0 $f wff ph $.
	fabn0_1 $f set x $.
	abn0 $p |- ( { x | ph } =/= (/) <-> E. x ph ) $= fabn0_0 fabn0_1 cab c0 wne fabn0_1 sup_set_class fabn0_0 fabn0_1 cab wcel fabn0_1 wex fabn0_0 fabn0_1 wex fabn0_1 fabn0_0 fabn0_1 cab fabn0_0 fabn0_1 nfab1 n0f fabn0_1 sup_set_class fabn0_0 fabn0_1 cab wcel fabn0_0 fabn0_1 fabn0_0 fabn0_1 abid exbii bitri $.
$}
$( /* Non-empty restricted class abstraction.  (Contributed by NM,
     29-Aug-1999.) */

$)
${
	frabn0_0 $f wff ph $.
	frabn0_1 $f set x $.
	frabn0_2 $f class A $.
	rabn0 $p |- ( { x e. A | ph } =/= (/) <-> E. x e. A ph ) $= frabn0_1 sup_set_class frabn0_2 wcel frabn0_0 wa frabn0_1 cab c0 wne frabn0_1 sup_set_class frabn0_2 wcel frabn0_0 wa frabn0_1 wex frabn0_0 frabn0_1 frabn0_2 crab c0 wne frabn0_0 frabn0_1 frabn0_2 wrex frabn0_1 sup_set_class frabn0_2 wcel frabn0_0 wa frabn0_1 abn0 frabn0_0 frabn0_1 frabn0_2 crab frabn0_1 sup_set_class frabn0_2 wcel frabn0_0 wa frabn0_1 cab c0 frabn0_0 frabn0_1 frabn0_2 df-rab neeq1i frabn0_0 frabn0_1 frabn0_2 df-rex 3bitr4i $.
$}
$( /* Any restricted class abstraction restricted to the empty set is empty.
     (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) */

$)
${
	frab0_0 $f wff ph $.
	frab0_1 $f set x $.
	rab0 $p |- { x e. (/) | ph } = (/) $= frab0_1 sup_set_class c0 wcel frab0_0 wa frab0_1 cab frab0_1 sup_set_class frab0_1 sup_set_class wceq wn frab0_1 cab frab0_0 frab0_1 c0 crab c0 frab0_1 sup_set_class c0 wcel frab0_0 wa frab0_1 sup_set_class frab0_1 sup_set_class wceq wn frab0_1 frab0_1 sup_set_class frab0_1 sup_set_class wceq frab0_1 sup_set_class c0 wcel frab0_0 wa frab0_1 sup_set_class frab0_1 sup_set_class wceq frab0_1 sup_set_class c0 wcel frab0_0 wa wn frab0_1 equid frab0_1 sup_set_class c0 wcel frab0_0 frab0_1 sup_set_class noel intnanr 2th con2bii abbii frab0_0 frab0_1 c0 df-rab frab0_1 dfnul2 3eqtr4i $.
$}
$( /* Condition for a restricted class abstraction to be empty.  (Contributed by
     Jeff Madsen, 7-Jun-2010.) */

$)
${
	frabeq0_0 $f wff ph $.
	frabeq0_1 $f set x $.
	frabeq0_2 $f class A $.
	rabeq0 $p |- ( { x e. A | ph } = (/) <-> A. x e. A -. ph ) $= frabeq0_0 wn frabeq0_1 frabeq0_2 wral frabeq0_0 frabeq0_1 frabeq0_2 wrex wn frabeq0_0 frabeq0_1 frabeq0_2 crab c0 wceq frabeq0_0 frabeq0_1 frabeq0_2 ralnex frabeq0_0 frabeq0_1 frabeq0_2 wrex frabeq0_0 frabeq0_1 frabeq0_2 crab c0 frabeq0_0 frabeq0_1 frabeq0_2 rabn0 necon1bbii bitr2i $.
$}
$( /* Law of excluded middle, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) */

$)
${
	$d A x $.
	frabxm_0 $f wff ph $.
	frabxm_1 $f set x $.
	frabxm_2 $f class A $.
	rabxm $p |- A = ( { x e. A | ph } u. { x e. A | -. ph } ) $= frabxm_2 frabxm_0 frabxm_0 wn wo frabxm_1 frabxm_2 crab frabxm_0 frabxm_1 frabxm_2 crab frabxm_0 wn frabxm_1 frabxm_2 crab cun frabxm_2 frabxm_0 frabxm_0 wn wo frabxm_1 frabxm_2 crab wceq frabxm_0 frabxm_0 wn wo frabxm_1 frabxm_2 frabxm_0 frabxm_0 wn wo frabxm_1 frabxm_2 rabid2 frabxm_0 frabxm_0 wn wo frabxm_1 sup_set_class frabxm_2 wcel frabxm_0 exmid a1i mprgbir frabxm_0 frabxm_0 wn frabxm_1 frabxm_2 unrab eqtr4i $.
$}
$( /* Law of noncontradiction, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) */

$)
${
	$d A x $.
	frabnc_0 $f wff ph $.
	frabnc_1 $f set x $.
	frabnc_2 $f class A $.
	rabnc $p |- ( { x e. A | ph } i^i { x e. A | -. ph } ) = (/) $= frabnc_0 frabnc_1 frabnc_2 crab frabnc_0 wn frabnc_1 frabnc_2 crab cin frabnc_0 frabnc_0 wn wa frabnc_1 frabnc_2 crab c0 frabnc_0 frabnc_0 wn frabnc_1 frabnc_2 inrab frabnc_0 frabnc_0 wn wa frabnc_1 frabnc_2 crab c0 wceq frabnc_0 frabnc_0 wn wa wn frabnc_1 frabnc_2 frabnc_0 frabnc_0 wn wa frabnc_1 frabnc_2 rabeq0 frabnc_0 frabnc_0 wn wa wn frabnc_1 sup_set_class frabnc_2 wcel frabnc_0 pm3.24 a1i mprgbir eqtri $.
$}
$( /* The union of a class with the empty set is itself.  Theorem 24 of
       [Suppes] p. 27.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	iun0_0 $f set x $.
	fun0_0 $f class A $.
	un0 $p |- ( A u. (/) ) = A $= iun0_0 fun0_0 c0 fun0_0 iun0_0 sup_set_class fun0_0 wcel iun0_0 sup_set_class fun0_0 wcel iun0_0 sup_set_class c0 wcel wo iun0_0 sup_set_class c0 wcel iun0_0 sup_set_class fun0_0 wcel iun0_0 sup_set_class noel biorfi bicomi uneqri $.
$}
$( /* The intersection of a class with the empty set is the empty set.
       Theorem 16 of [Suppes] p. 26.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	iin0_0 $f set x $.
	fin0_0 $f class A $.
	in0 $p |- ( A i^i (/) ) = (/) $= iin0_0 fin0_0 c0 c0 iin0_0 sup_set_class c0 wcel iin0_0 sup_set_class fin0_0 wcel iin0_0 sup_set_class c0 wcel wa iin0_0 sup_set_class c0 wcel iin0_0 sup_set_class fin0_0 wcel iin0_0 sup_set_class noel bianfi bicomi ineqri $.
$}
$( /* The intersection of a class with the universal class is itself.  Exercise
     4.10(k) of [Mendelson] p. 231.  (Contributed by NM, 17-May-1998.) */

$)
${
	finv1_0 $f class A $.
	inv1 $p |- ( A i^i _V ) = A $= finv1_0 cvv cin finv1_0 finv1_0 cvv inss1 finv1_0 finv1_0 cvv finv1_0 ssid finv1_0 ssv ssini eqssi $.
$}
$( /* The union of a class with the universal class is the universal class.
     Exercise 4.10(l) of [Mendelson] p. 231.  (Contributed by NM,
     17-May-1998.) */

$)
${
	funv_0 $f class A $.
	unv $p |- ( A u. _V ) = _V $= funv_0 cvv cun cvv funv_0 cvv cun ssv cvv funv_0 ssun2 eqssi $.
$}
$( /* The null set is a subset of any class.  Part of Exercise 1 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d A x $.
	i0ss_0 $f set x $.
	f0ss_0 $f class A $.
	0ss $p |- (/) C_ A $= i0ss_0 c0 f0ss_0 i0ss_0 sup_set_class c0 wcel i0ss_0 sup_set_class f0ss_0 wcel i0ss_0 sup_set_class noel pm2.21i ssriv $.
$}
$( /* Any subset of the empty set is empty.  Theorem 5 of [Suppes] p. 23 and its
     converse.  (Contributed by NM, 17-Sep-2003.) */

$)
${
	fss0b_0 $f class A $.
	ss0b $p |- ( A C_ (/) <-> A = (/) ) $= fss0b_0 c0 wceq fss0b_0 c0 wss fss0b_0 c0 wceq fss0b_0 c0 wss c0 fss0b_0 wss fss0b_0 0ss fss0b_0 c0 eqss mpbiran2 bicomi $.
$}
$( /* Any subset of the empty set is empty.  Theorem 5 of [Suppes] p. 23.
     (Contributed by NM, 13-Aug-1994.) */

$)
${
	fss0_0 $f class A $.
	ss0 $p |- ( A C_ (/) -> A = (/) ) $= fss0_0 c0 wss fss0_0 c0 wceq fss0_0 ss0b biimpi $.
$}
$( /* A subclass of an empty class is empty.  (Contributed by NM, 7-Mar-2007.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	fsseq0_0 $f class A $.
	fsseq0_1 $f class B $.
	sseq0 $p |- ( ( A C_ B /\ B = (/) ) -> A = (/) ) $= fsseq0_1 c0 wceq fsseq0_0 fsseq0_1 wss fsseq0_0 c0 wceq fsseq0_1 c0 wceq fsseq0_0 fsseq0_1 wss fsseq0_0 c0 wss fsseq0_0 c0 wceq fsseq0_1 c0 fsseq0_0 sseq2 fsseq0_0 ss0 syl6bi impcom $.
$}
$( /* A class with a nonempty subclass is nonempty.  (Contributed by NM,
     17-Feb-2007.) */

$)
${
	fssn0_0 $f class A $.
	fssn0_1 $f class B $.
	ssn0 $p |- ( ( A C_ B /\ A =/= (/) ) -> B =/= (/) ) $= fssn0_0 fssn0_1 wss fssn0_0 c0 wne fssn0_1 c0 wne fssn0_0 fssn0_1 wss fssn0_1 c0 fssn0_0 c0 fssn0_0 fssn0_1 wss fssn0_1 c0 wceq fssn0_0 c0 wceq fssn0_0 fssn0_1 sseq0 ex necon3d imp $.
$}
$( /* A class builder with a false argument is empty.  (Contributed by NM,
       20-Jan-2012.) */

$)
${
	fabf_0 $f wff ph $.
	fabf_1 $f set x $.
	eabf_0 $e |- -. ph $.
	abf $p |- { x | ph } = (/) $= fabf_0 fabf_1 cab c0 wss fabf_0 fabf_1 cab c0 wceq fabf_0 fabf_1 c0 fabf_0 fabf_1 sup_set_class c0 wcel eabf_0 pm2.21i abssi fabf_0 fabf_1 cab ss0 ax-mp $.
$}
$( /* Deduction rule for equality to the empty set.  (Contributed by NM,
       11-Jul-2014.) */

$)
${
	$d x A $.
	$d x ph $.
	feq0rdv_0 $f wff ph $.
	feq0rdv_1 $f set x $.
	feq0rdv_2 $f class A $.
	eeq0rdv_0 $e |- ( ph -> -. x e. A ) $.
	eq0rdv $p |- ( ph -> A = (/) ) $= feq0rdv_0 feq0rdv_2 c0 wss feq0rdv_2 c0 wceq feq0rdv_0 feq0rdv_1 feq0rdv_2 c0 feq0rdv_0 feq0rdv_1 sup_set_class feq0rdv_2 wcel feq0rdv_1 sup_set_class c0 wcel eeq0rdv_0 pm2.21d ssrdv feq0rdv_2 ss0 syl $.
$}
$( /* Two classes are empty iff their union is empty.  (Contributed by NM,
     11-Aug-2004.) */

$)
${
	fun00_0 $f class A $.
	fun00_1 $f class B $.
	un00 $p |- ( ( A = (/) /\ B = (/) ) <-> ( A u. B ) = (/) ) $= fun00_0 c0 wceq fun00_1 c0 wceq wa fun00_0 fun00_1 cun c0 wceq fun00_0 c0 wceq fun00_1 c0 wceq wa fun00_0 fun00_1 cun c0 c0 cun c0 fun00_0 c0 fun00_1 c0 uneq12 c0 un0 syl6eq fun00_0 fun00_1 cun c0 wceq fun00_0 c0 wceq fun00_1 c0 wceq fun00_0 fun00_1 cun c0 wceq fun00_0 c0 wss fun00_0 c0 wceq fun00_0 fun00_1 cun c0 wceq fun00_0 fun00_0 fun00_1 cun wss fun00_0 c0 wss fun00_0 fun00_1 ssun1 fun00_0 fun00_1 cun c0 fun00_0 sseq2 mpbii fun00_0 ss0b sylib fun00_0 fun00_1 cun c0 wceq fun00_1 c0 wss fun00_1 c0 wceq fun00_0 fun00_1 cun c0 wceq fun00_1 fun00_0 fun00_1 cun wss fun00_1 c0 wss fun00_1 fun00_0 ssun2 fun00_0 fun00_1 cun c0 fun00_1 sseq2 mpbii fun00_1 ss0b sylib jca impbii $.
$}
$( /* Only the universal class has the universal class as a subclass.
     (Contributed by NM, 17-Sep-2003.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) */

$)
${
	fvss_0 $f class A $.
	vss $p |- ( _V C_ A <-> A = _V ) $= cvv fvss_0 wss fvss_0 cvv wss cvv fvss_0 wss wa fvss_0 cvv wceq fvss_0 cvv wss cvv fvss_0 wss fvss_0 ssv biantrur fvss_0 cvv eqss bitr4i $.
$}
$( /* The null set is a proper subset of any non-empty set.  (Contributed by NM,
     27-Feb-1996.) */

$)
${
	f0pss_0 $f class A $.
	0pss $p |- ( (/) C. A <-> A =/= (/) ) $= c0 f0pss_0 wpss c0 f0pss_0 wne f0pss_0 c0 wne c0 f0pss_0 wpss c0 f0pss_0 wss c0 f0pss_0 wne f0pss_0 0ss c0 f0pss_0 df-pss mpbiran c0 f0pss_0 necom bitri $.
$}
$( /* No set is a proper subset of the empty set.  (Contributed by NM,
     17-Jun-1998.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	fnpss0_0 $f class A $.
	npss0 $p |- -. A C. (/) $= fnpss0_0 c0 wpss fnpss0_0 c0 wss c0 fnpss0_0 wss wn wa fnpss0_0 c0 wss c0 fnpss0_0 wss wi fnpss0_0 c0 wss c0 fnpss0_0 wss wn wa wn c0 fnpss0_0 wss fnpss0_0 c0 wss fnpss0_0 0ss a1i fnpss0_0 c0 wss c0 fnpss0_0 wss iman mpbi fnpss0_0 c0 dfpss3 mtbir $.
$}
$( /* Any non-universal class is a proper subclass of the universal class.
     (Contributed by NM, 17-May-1998.) */

$)
${
	fpssv_0 $f class A $.
	pssv $p |- ( A C. _V <-> -. A = _V ) $= fpssv_0 cvv wpss fpssv_0 cvv wss fpssv_0 cvv wceq wn fpssv_0 ssv fpssv_0 cvv dfpss2 mpbiran $.
$}
$( /* Two ways of saying that two classes are disjoint (have no members in
       common).  (Contributed by NM, 17-Feb-2004.) */

$)
${
	$d x A $.
	$d x B $.
	fdisj_0 $f set x $.
	fdisj_1 $f class A $.
	fdisj_2 $f class B $.
	disj $p |- ( ( A i^i B ) = (/) <-> A. x e. A -. x e. B ) $= fdisj_1 fdisj_2 cin c0 wceq fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wn wi fdisj_0 wal fdisj_0 sup_set_class fdisj_2 wcel wn fdisj_0 fdisj_1 wral fdisj_1 fdisj_2 cin c0 wceq fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 cab c0 wceq fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 sup_set_class c0 wcel wb fdisj_0 wal fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wn wi fdisj_0 wal fdisj_1 fdisj_2 cin fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 cab c0 fdisj_0 fdisj_1 fdisj_2 df-in eqeq1i fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 c0 abeq1 fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 sup_set_class c0 wcel wb fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wn wi fdisj_0 fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wn wi fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa wn fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 sup_set_class c0 wcel wb fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel imnan fdisj_0 sup_set_class c0 wcel fdisj_0 sup_set_class fdisj_1 wcel fdisj_0 sup_set_class fdisj_2 wcel wa fdisj_0 sup_set_class noel nbn bitr2i albii 3bitri fdisj_0 sup_set_class fdisj_2 wcel wn fdisj_0 fdisj_1 df-ral bitr4i $.
$}
$( /* Two ways of saying that two classes are disjoint.  (Contributed by Jeff
       Madsen, 19-Jun-2011.) */

$)
${
	$d x A $.
	$d x B $.
	fdisjr_0 $f set x $.
	fdisjr_1 $f class A $.
	fdisjr_2 $f class B $.
	disjr $p |- ( ( A i^i B ) = (/) <-> A. x e. B -. x e. A ) $= fdisjr_1 fdisjr_2 cin c0 wceq fdisjr_2 fdisjr_1 cin c0 wceq fdisjr_0 sup_set_class fdisjr_1 wcel wn fdisjr_0 fdisjr_2 wral fdisjr_1 fdisjr_2 cin fdisjr_2 fdisjr_1 cin c0 fdisjr_1 fdisjr_2 incom eqeq1i fdisjr_0 fdisjr_2 fdisjr_1 disj bitri $.
$}
$( /* Two ways of saying that two classes are disjoint (have no members in
       common).  (Contributed by NM, 19-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	fdisj1_0 $f set x $.
	fdisj1_1 $f class A $.
	fdisj1_2 $f class B $.
	disj1 $p |- ( ( A i^i B ) = (/) <-> A. x ( x e. A -> -. x e. B ) ) $= fdisj1_1 fdisj1_2 cin c0 wceq fdisj1_0 sup_set_class fdisj1_2 wcel wn fdisj1_0 fdisj1_1 wral fdisj1_0 sup_set_class fdisj1_1 wcel fdisj1_0 sup_set_class fdisj1_2 wcel wn wi fdisj1_0 wal fdisj1_0 fdisj1_1 fdisj1_2 disj fdisj1_0 sup_set_class fdisj1_2 wcel wn fdisj1_0 fdisj1_1 df-ral bitri $.
$}
$( /* Two ways of saying that two classes are disjoint, using the complement
       of ` B ` relative to a universe ` C ` .  (Contributed by NM,
       15-Feb-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ireldisj_0 $f set x $.
	freldisj_0 $f class A $.
	freldisj_1 $f class B $.
	freldisj_2 $f class C $.
	reldisj $p |- ( A C_ C -> ( ( A i^i B ) = (/) <-> A C_ ( C \ B ) ) ) $= freldisj_0 freldisj_2 wss ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wi ireldisj_0 wal ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 freldisj_1 cdif wcel wi ireldisj_0 wal freldisj_0 freldisj_1 cin c0 wceq freldisj_0 freldisj_2 freldisj_1 cdif wss freldisj_0 freldisj_2 wss ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 freldisj_1 cdif wcel wi ireldisj_0 freldisj_0 freldisj_2 wss ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 wcel wi ireldisj_0 wal ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 freldisj_1 cdif wcel wi wb ireldisj_0 freldisj_0 freldisj_2 dfss2 ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 wcel wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 freldisj_1 cdif wcel wi wb ireldisj_0 ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 wcel wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wa wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 freldisj_1 cdif wcel wi ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn pm5.44 ireldisj_0 sup_set_class freldisj_2 freldisj_1 cdif wcel ireldisj_0 sup_set_class freldisj_2 wcel ireldisj_0 sup_set_class freldisj_1 wcel wn wa ireldisj_0 sup_set_class freldisj_0 wcel ireldisj_0 sup_set_class freldisj_2 freldisj_1 eldif imbi2i syl6bbr sps sylbi albidv ireldisj_0 freldisj_0 freldisj_1 disj1 ireldisj_0 freldisj_0 freldisj_2 freldisj_1 cdif dfss2 3bitr4g $.
$}
$( /* Two ways of saying that two classes are disjoint.  (Contributed by NM,
       19-May-1998.) */

$)
${
	$d x A $.
	$d x B $.
	idisj3_0 $f set x $.
	fdisj3_0 $f class A $.
	fdisj3_1 $f class B $.
	disj3 $p |- ( ( A i^i B ) = (/) <-> A = ( A \ B ) ) $= idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_1 wcel wn wi idisj3_0 wal idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_0 fdisj3_1 cdif wcel wb idisj3_0 wal fdisj3_0 fdisj3_1 cin c0 wceq fdisj3_0 fdisj3_0 fdisj3_1 cdif wceq idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_1 wcel wn wi idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_0 fdisj3_1 cdif wcel wb idisj3_0 idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_1 wcel wn wi idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_1 wcel wn wa wb idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_0 fdisj3_1 cdif wcel wb idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_1 wcel wn pm4.71 idisj3_0 sup_set_class fdisj3_0 fdisj3_1 cdif wcel idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_1 wcel wn wa idisj3_0 sup_set_class fdisj3_0 wcel idisj3_0 sup_set_class fdisj3_0 fdisj3_1 eldif bibi2i bitr4i albii idisj3_0 fdisj3_0 fdisj3_1 disj1 idisj3_0 fdisj3_0 fdisj3_0 fdisj3_1 cdif dfcleq 3bitr4i $.
$}
$( /* Members of disjoint sets are not equal.  (Contributed by NM,
       28-Mar-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	idisjne_0 $f set x $.
	fdisjne_0 $f class A $.
	fdisjne_1 $f class B $.
	fdisjne_2 $f class C $.
	fdisjne_3 $f class D $.
	disjne $p |- ( ( ( A i^i B ) = (/) /\ C e. A /\ D e. B ) -> C =/= D ) $= fdisjne_0 fdisjne_1 cin c0 wceq fdisjne_2 fdisjne_0 wcel fdisjne_3 fdisjne_1 wcel fdisjne_2 fdisjne_3 wne fdisjne_0 fdisjne_1 cin c0 wceq idisjne_0 sup_set_class fdisjne_1 wcel wn idisjne_0 fdisjne_0 wral fdisjne_2 fdisjne_0 wcel fdisjne_3 fdisjne_1 wcel fdisjne_2 fdisjne_3 wne wi idisjne_0 fdisjne_0 fdisjne_1 disj idisjne_0 sup_set_class fdisjne_1 wcel wn idisjne_0 fdisjne_0 wral fdisjne_2 fdisjne_0 wcel wa fdisjne_2 fdisjne_1 wcel wn fdisjne_3 fdisjne_1 wcel fdisjne_2 fdisjne_3 wne idisjne_0 sup_set_class fdisjne_1 wcel wn fdisjne_2 fdisjne_1 wcel wn idisjne_0 fdisjne_2 fdisjne_0 idisjne_0 sup_set_class fdisjne_2 wceq idisjne_0 sup_set_class fdisjne_1 wcel fdisjne_2 fdisjne_1 wcel idisjne_0 sup_set_class fdisjne_2 fdisjne_1 eleq1 notbid rspccva fdisjne_3 fdisjne_1 wcel fdisjne_2 fdisjne_1 wcel fdisjne_2 fdisjne_3 fdisjne_3 fdisjne_1 fdisjne_2 eleq1a necon3bd syl5com sylanb 3impia $.
$}
$( /* A set can't belong to both members of disjoint classes.  (Contributed by
     NM, 28-Feb-2015.) */

$)
${
	fdisjel_0 $f class A $.
	fdisjel_1 $f class B $.
	fdisjel_2 $f class C $.
	disjel $p |- ( ( ( A i^i B ) = (/) /\ C e. A ) -> -. C e. B ) $= fdisjel_0 fdisjel_1 cin c0 wceq fdisjel_2 fdisjel_0 wcel fdisjel_2 fdisjel_1 wcel wn fdisjel_0 fdisjel_1 cin c0 wceq fdisjel_0 fdisjel_0 fdisjel_1 cdif wceq fdisjel_2 fdisjel_0 wcel fdisjel_2 fdisjel_1 wcel wn wi fdisjel_0 fdisjel_1 disj3 fdisjel_0 fdisjel_0 fdisjel_1 cdif wceq fdisjel_2 fdisjel_0 wcel fdisjel_2 fdisjel_0 fdisjel_1 cdif wcel fdisjel_2 fdisjel_1 wcel wn fdisjel_0 fdisjel_0 fdisjel_1 cdif fdisjel_2 eleq2 fdisjel_2 fdisjel_0 fdisjel_1 eldifn syl6bi sylbi imp $.
$}
$( /* Two ways of saying that two classes are disjoint.  (Contributed by NM,
     17-May-1998.) */

$)
${
	fdisj2_0 $f class A $.
	fdisj2_1 $f class B $.
	disj2 $p |- ( ( A i^i B ) = (/) <-> A C_ ( _V \ B ) ) $= fdisj2_0 cvv wss fdisj2_0 fdisj2_1 cin c0 wceq fdisj2_0 cvv fdisj2_1 cdif wss wb fdisj2_0 ssv fdisj2_0 fdisj2_1 cvv reldisj ax-mp $.
$}
$( /* Two ways of saying that two classes are disjoint.  (Contributed by NM,
     21-Mar-2004.) */

$)
${
	fdisj4_0 $f class A $.
	fdisj4_1 $f class B $.
	disj4 $p |- ( ( A i^i B ) = (/) <-> -. ( A \ B ) C. A ) $= fdisj4_0 fdisj4_1 cin c0 wceq fdisj4_0 fdisj4_0 fdisj4_1 cdif wceq fdisj4_0 fdisj4_1 cdif fdisj4_0 wceq fdisj4_0 fdisj4_1 cdif fdisj4_0 wpss wn fdisj4_0 fdisj4_1 disj3 fdisj4_0 fdisj4_0 fdisj4_1 cdif eqcom fdisj4_0 fdisj4_1 cdif fdisj4_0 wpss fdisj4_0 fdisj4_1 cdif fdisj4_0 wceq fdisj4_0 fdisj4_1 cdif fdisj4_0 wpss fdisj4_0 fdisj4_1 cdif fdisj4_0 wss fdisj4_0 fdisj4_1 cdif fdisj4_0 wceq wn fdisj4_0 fdisj4_1 difss fdisj4_0 fdisj4_1 cdif fdisj4_0 dfpss2 mpbiran con2bii 3bitri $.
$}
$( /* Intersection with a subclass of a disjoint class.  (Contributed by FL,
     24-Jan-2007.) */

$)
${
	fssdisj_0 $f class A $.
	fssdisj_1 $f class B $.
	fssdisj_2 $f class C $.
	ssdisj $p |- ( ( A C_ B /\ ( B i^i C ) = (/) ) -> ( A i^i C ) = (/) ) $= fssdisj_0 fssdisj_1 wss fssdisj_1 fssdisj_2 cin c0 wceq wa fssdisj_0 fssdisj_2 cin c0 wss fssdisj_0 fssdisj_2 cin c0 wceq fssdisj_0 fssdisj_1 wss fssdisj_1 fssdisj_2 cin c0 wceq fssdisj_0 fssdisj_2 cin c0 wss fssdisj_1 fssdisj_2 cin c0 wceq fssdisj_1 fssdisj_2 cin c0 wss fssdisj_0 fssdisj_1 wss fssdisj_0 fssdisj_2 cin c0 wss fssdisj_1 fssdisj_2 cin ss0b fssdisj_0 fssdisj_1 wss fssdisj_0 fssdisj_2 cin fssdisj_1 fssdisj_2 cin wss fssdisj_1 fssdisj_2 cin c0 wss fssdisj_0 fssdisj_2 cin c0 wss wi fssdisj_0 fssdisj_1 fssdisj_2 ssrin fssdisj_0 fssdisj_2 cin fssdisj_1 fssdisj_2 cin c0 sstr2 syl syl5bir imp fssdisj_0 fssdisj_2 cin ss0 syl $.
$}
$( /* A class is a proper subset of its union with a disjoint nonempty class.
     (Contributed by NM, 15-Sep-2004.) */

$)
${
	fdisjpss_0 $f class A $.
	fdisjpss_1 $f class B $.
	disjpss $p |- ( ( ( A i^i B ) = (/) /\ B =/= (/) ) -> A C. ( A u. B ) ) $= fdisjpss_0 fdisjpss_1 cin c0 wceq fdisjpss_1 c0 wne wa fdisjpss_1 fdisjpss_0 wss wn fdisjpss_0 fdisjpss_0 fdisjpss_1 cun wpss fdisjpss_0 fdisjpss_1 cin c0 wceq fdisjpss_1 c0 wne fdisjpss_1 fdisjpss_0 wss wn fdisjpss_0 fdisjpss_1 cin c0 wceq fdisjpss_1 fdisjpss_0 wss fdisjpss_1 c0 fdisjpss_0 fdisjpss_1 cin c0 wceq fdisjpss_1 fdisjpss_0 wss fdisjpss_1 c0 wss fdisjpss_1 c0 wceq fdisjpss_1 fdisjpss_0 wss fdisjpss_1 fdisjpss_0 fdisjpss_1 cin wss fdisjpss_0 fdisjpss_1 cin c0 wceq fdisjpss_1 c0 wss fdisjpss_1 fdisjpss_0 wss fdisjpss_1 fdisjpss_0 wss fdisjpss_1 fdisjpss_1 wss wa fdisjpss_1 fdisjpss_0 fdisjpss_1 cin wss fdisjpss_1 fdisjpss_1 wss fdisjpss_1 fdisjpss_0 wss fdisjpss_1 ssid biantru fdisjpss_1 fdisjpss_0 fdisjpss_1 ssin bitri fdisjpss_0 fdisjpss_1 cin c0 fdisjpss_1 sseq2 syl5bb fdisjpss_1 ss0 syl6bi necon3ad imp fdisjpss_1 fdisjpss_0 wss wn fdisjpss_0 fdisjpss_1 fdisjpss_0 cun wpss fdisjpss_0 fdisjpss_0 fdisjpss_1 cun wpss fdisjpss_1 fdisjpss_0 nsspssun fdisjpss_1 fdisjpss_0 cun fdisjpss_0 fdisjpss_1 cun fdisjpss_0 fdisjpss_1 fdisjpss_0 uncom psseq2i bitri sylib $.
$}
$( /* The union of disjoint classes is disjoint.  (Contributed by NM,
     26-Sep-2004.) */

$)
${
	fundisj1_0 $f class A $.
	fundisj1_1 $f class B $.
	fundisj1_2 $f class C $.
	undisj1 $p |- ( ( ( A i^i C ) = (/) /\ ( B i^i C ) = (/) ) <-> ( ( A u. B ) i^i C ) = (/) ) $= fundisj1_0 fundisj1_2 cin c0 wceq fundisj1_1 fundisj1_2 cin c0 wceq wa fundisj1_0 fundisj1_2 cin fundisj1_1 fundisj1_2 cin cun c0 wceq fundisj1_0 fundisj1_1 cun fundisj1_2 cin c0 wceq fundisj1_0 fundisj1_2 cin fundisj1_1 fundisj1_2 cin un00 fundisj1_0 fundisj1_1 cun fundisj1_2 cin fundisj1_0 fundisj1_2 cin fundisj1_1 fundisj1_2 cin cun c0 fundisj1_0 fundisj1_1 fundisj1_2 indir eqeq1i bitr4i $.
$}
$( /* The union of disjoint classes is disjoint.  (Contributed by NM,
     13-Sep-2004.) */

$)
${
	fundisj2_0 $f class A $.
	fundisj2_1 $f class B $.
	fundisj2_2 $f class C $.
	undisj2 $p |- ( ( ( A i^i B ) = (/) /\ ( A i^i C ) = (/) ) <-> ( A i^i ( B u. C ) ) = (/) ) $= fundisj2_0 fundisj2_1 cin c0 wceq fundisj2_0 fundisj2_2 cin c0 wceq wa fundisj2_0 fundisj2_1 cin fundisj2_0 fundisj2_2 cin cun c0 wceq fundisj2_0 fundisj2_1 fundisj2_2 cun cin c0 wceq fundisj2_0 fundisj2_1 cin fundisj2_0 fundisj2_2 cin un00 fundisj2_0 fundisj2_1 fundisj2_2 cun cin fundisj2_0 fundisj2_1 cin fundisj2_0 fundisj2_2 cin cun c0 fundisj2_0 fundisj2_1 fundisj2_2 indi eqeq1i bitr4i $.
$}
$( /* Subclass expressed in terms of intersection with difference from the
     universal class.  (Contributed by NM, 17-Sep-2003.) */

$)
${
	fssindif0_0 $f class A $.
	fssindif0_1 $f class B $.
	ssindif0 $p |- ( A C_ B <-> ( A i^i ( _V \ B ) ) = (/) ) $= fssindif0_0 cvv fssindif0_1 cdif cin c0 wceq fssindif0_0 cvv cvv fssindif0_1 cdif cdif wss fssindif0_0 fssindif0_1 wss fssindif0_0 cvv fssindif0_1 cdif disj2 cvv cvv fssindif0_1 cdif cdif fssindif0_1 fssindif0_0 fssindif0_1 ddif sseq2i bitr2i $.
$}
$( /* The intersection of classes with a common member is nonempty.
     (Contributed by NM, 7-Apr-1994.) */

$)
${
	finelcm_0 $f class A $.
	finelcm_1 $f class B $.
	finelcm_2 $f class C $.
	inelcm $p |- ( ( A e. B /\ A e. C ) -> ( B i^i C ) =/= (/) ) $= finelcm_0 finelcm_1 wcel finelcm_0 finelcm_2 wcel wa finelcm_0 finelcm_1 finelcm_2 cin wcel finelcm_1 finelcm_2 cin c0 wne finelcm_0 finelcm_1 finelcm_2 elin finelcm_1 finelcm_2 cin finelcm_0 ne0i sylbir $.
$}
$( /* A minimum element of a class has no elements in common with the class.
     (Contributed by NM, 22-Jun-1994.) */

$)
${
	fminel_0 $f class A $.
	fminel_1 $f class B $.
	fminel_2 $f class C $.
	minel $p |- ( ( A e. B /\ ( C i^i B ) = (/) ) -> -. A e. C ) $= fminel_2 fminel_1 cin c0 wceq fminel_0 fminel_1 wcel fminel_0 fminel_2 wcel wn fminel_2 fminel_1 cin c0 wceq fminel_0 fminel_2 wcel fminel_0 fminel_1 wcel fminel_2 fminel_1 cin c0 wceq fminel_0 fminel_2 wcel fminel_0 fminel_1 wcel wa wn fminel_0 fminel_2 wcel fminel_0 fminel_1 wcel wn wi fminel_0 fminel_2 wcel fminel_0 fminel_1 wcel wa fminel_2 fminel_1 cin c0 fminel_0 fminel_2 fminel_1 inelcm necon2bi fminel_0 fminel_2 wcel fminel_0 fminel_1 wcel imnan sylibr con2d impcom $.
$}
$( /* Distribute union over difference.  (Contributed by NM, 17-May-1998.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	iundif4_0 $f set x $.
	fundif4_0 $f class A $.
	fundif4_1 $f class B $.
	fundif4_2 $f class C $.
	undif4 $p |- ( ( A i^i C ) = (/) -> ( A u. ( B \ C ) ) = ( ( A u. B ) \ C ) ) $= iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wi iundif4_0 wal iundif4_0 sup_set_class fundif4_0 fundif4_1 fundif4_2 cdif cun wcel iundif4_0 sup_set_class fundif4_0 fundif4_1 cun fundif4_2 cdif wcel wb iundif4_0 wal fundif4_0 fundif4_2 cin c0 wceq fundif4_0 fundif4_1 fundif4_2 cdif cun fundif4_0 fundif4_1 cun fundif4_2 cdif wceq iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wi iundif4_0 sup_set_class fundif4_0 fundif4_1 fundif4_2 cdif cun wcel iundif4_0 sup_set_class fundif4_0 fundif4_1 cun fundif4_2 cdif wcel wb iundif4_0 iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wi iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 fundif4_2 cdif wcel wo iundif4_0 sup_set_class fundif4_0 fundif4_1 cun wcel iundif4_0 sup_set_class fundif4_2 wcel wn wa iundif4_0 sup_set_class fundif4_0 fundif4_1 fundif4_2 cdif cun wcel iundif4_0 sup_set_class fundif4_0 fundif4_1 cun fundif4_2 cdif wcel iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wi iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel wo iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wo wa iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel wo iundif4_0 sup_set_class fundif4_2 wcel wn wa iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 fundif4_2 cdif wcel wo iundif4_0 sup_set_class fundif4_0 fundif4_1 cun wcel iundif4_0 sup_set_class fundif4_2 wcel wn wa iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wi iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wo iundif4_0 sup_set_class fundif4_2 wcel wn iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel wo iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wi iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wo iundif4_0 sup_set_class fundif4_2 wcel wn iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn pm2.621 iundif4_0 sup_set_class fundif4_2 wcel wn iundif4_0 sup_set_class fundif4_0 wcel olc impbid1 anbi2d iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 fundif4_2 cdif wcel wo iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wa wo iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel wo iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wo wa iundif4_0 sup_set_class fundif4_1 fundif4_2 cdif wcel iundif4_0 sup_set_class fundif4_1 wcel iundif4_0 sup_set_class fundif4_2 wcel wn wa iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 fundif4_2 eldif orbi2i iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel iundif4_0 sup_set_class fundif4_2 wcel wn ordi bitri iundif4_0 sup_set_class fundif4_0 fundif4_1 cun wcel iundif4_0 sup_set_class fundif4_0 wcel iundif4_0 sup_set_class fundif4_1 wcel wo iundif4_0 sup_set_class fundif4_2 wcel wn iundif4_0 sup_set_class fundif4_0 fundif4_1 elun anbi1i 3bitr4g iundif4_0 sup_set_class fundif4_0 fundif4_1 fundif4_2 cdif elun iundif4_0 sup_set_class fundif4_0 fundif4_1 cun fundif4_2 eldif 3bitr4g alimi iundif4_0 fundif4_0 fundif4_2 disj1 iundif4_0 fundif4_0 fundif4_1 fundif4_2 cdif cun fundif4_0 fundif4_1 cun fundif4_2 cdif dfcleq 3imtr4i $.
$}
$( /* Subset relation for disjoint classes.  (Contributed by NM,
       25-Oct-2005.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	fdisjssun_0 $f class A $.
	fdisjssun_1 $f class B $.
	fdisjssun_2 $f class C $.
	disjssun $p |- ( ( A i^i B ) = (/) -> ( A C_ ( B u. C ) <-> A C_ C ) ) $= fdisjssun_0 fdisjssun_1 cin c0 wceq fdisjssun_0 fdisjssun_1 fdisjssun_2 cun cin fdisjssun_0 wceq fdisjssun_0 fdisjssun_2 cin fdisjssun_0 wceq fdisjssun_0 fdisjssun_1 fdisjssun_2 cun wss fdisjssun_0 fdisjssun_2 wss fdisjssun_0 fdisjssun_1 cin c0 wceq fdisjssun_0 fdisjssun_1 fdisjssun_2 cun cin fdisjssun_0 fdisjssun_2 cin fdisjssun_0 fdisjssun_0 fdisjssun_1 cin c0 wceq fdisjssun_0 fdisjssun_1 fdisjssun_2 cun cin fdisjssun_0 fdisjssun_2 cin fdisjssun_0 fdisjssun_1 cin cun fdisjssun_0 fdisjssun_2 cin fdisjssun_0 fdisjssun_1 fdisjssun_2 cun cin fdisjssun_0 fdisjssun_1 cin fdisjssun_0 fdisjssun_2 cin fdisjssun_0 fdisjssun_1 fdisjssun_2 indi equncomi fdisjssun_0 fdisjssun_1 cin c0 wceq fdisjssun_0 fdisjssun_2 cin fdisjssun_0 fdisjssun_1 cin cun fdisjssun_0 fdisjssun_2 cin c0 cun fdisjssun_0 fdisjssun_2 cin fdisjssun_0 fdisjssun_1 cin c0 fdisjssun_0 fdisjssun_2 cin uneq2 fdisjssun_0 fdisjssun_2 cin un0 syl6eq syl5eq eqeq1d fdisjssun_0 fdisjssun_1 fdisjssun_2 cun df-ss fdisjssun_0 fdisjssun_2 df-ss 3bitr4g $.
$}
$( /* Subclass expressed in terms of difference.  Exercise 7 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 29-Apr-1994.) */

$)
${
	$d x A $.
	$d x B $.
	issdif0_0 $f set x $.
	fssdif0_0 $f class A $.
	fssdif0_1 $f class B $.
	ssdif0 $p |- ( A C_ B <-> ( A \ B ) = (/) ) $= issdif0_0 sup_set_class fssdif0_0 wcel issdif0_0 sup_set_class fssdif0_1 wcel wi issdif0_0 wal issdif0_0 sup_set_class fssdif0_0 fssdif0_1 cdif wcel wn issdif0_0 wal fssdif0_0 fssdif0_1 wss fssdif0_0 fssdif0_1 cdif c0 wceq issdif0_0 sup_set_class fssdif0_0 wcel issdif0_0 sup_set_class fssdif0_1 wcel wi issdif0_0 sup_set_class fssdif0_0 fssdif0_1 cdif wcel wn issdif0_0 issdif0_0 sup_set_class fssdif0_0 wcel issdif0_0 sup_set_class fssdif0_1 wcel wi issdif0_0 sup_set_class fssdif0_0 wcel issdif0_0 sup_set_class fssdif0_1 wcel wn wa issdif0_0 sup_set_class fssdif0_0 fssdif0_1 cdif wcel issdif0_0 sup_set_class fssdif0_0 wcel issdif0_0 sup_set_class fssdif0_1 wcel iman issdif0_0 sup_set_class fssdif0_0 fssdif0_1 eldif xchbinxr albii issdif0_0 fssdif0_0 fssdif0_1 dfss2 issdif0_0 fssdif0_0 fssdif0_1 cdif eq0 3bitr4i $.
$}
$( /* Universal class equality in terms of empty difference.  (Contributed by
     NM, 17-Sep-2003.) */

$)
${
	fvdif0_0 $f class A $.
	vdif0 $p |- ( A = _V <-> ( _V \ A ) = (/) ) $= fvdif0_0 cvv wceq cvv fvdif0_0 wss cvv fvdif0_0 cdif c0 wceq fvdif0_0 vss cvv fvdif0_0 ssdif0 bitr3i $.
$}
$( /* A proper subclass has a nonempty difference.  (Contributed by NM,
     3-May-1994.) */

$)
${
	fpssdifn0_0 $f class A $.
	fpssdifn0_1 $f class B $.
	pssdifn0 $p |- ( ( A C_ B /\ A =/= B ) -> ( B \ A ) =/= (/) ) $= fpssdifn0_0 fpssdifn0_1 wss fpssdifn0_0 fpssdifn0_1 wne fpssdifn0_1 fpssdifn0_0 cdif c0 wne fpssdifn0_0 fpssdifn0_1 wss fpssdifn0_1 fpssdifn0_0 cdif c0 fpssdifn0_0 fpssdifn0_1 fpssdifn0_1 fpssdifn0_0 cdif c0 wceq fpssdifn0_1 fpssdifn0_0 wss fpssdifn0_0 fpssdifn0_1 wss fpssdifn0_0 fpssdifn0_1 wceq fpssdifn0_1 fpssdifn0_0 ssdif0 fpssdifn0_0 fpssdifn0_1 wceq fpssdifn0_0 fpssdifn0_1 wss fpssdifn0_1 fpssdifn0_0 wss fpssdifn0_0 fpssdifn0_1 eqss simplbi2 syl5bir necon3d imp $.
$}
$( /* A proper subclass has a nonempty difference.  (Contributed by Mario
     Carneiro, 27-Apr-2016.) */

$)
${
	fpssdif_0 $f class A $.
	fpssdif_1 $f class B $.
	pssdif $p |- ( A C. B -> ( B \ A ) =/= (/) ) $= fpssdif_0 fpssdif_1 wpss fpssdif_0 fpssdif_1 wss fpssdif_0 fpssdif_1 wne wa fpssdif_1 fpssdif_0 cdif c0 wne fpssdif_0 fpssdif_1 df-pss fpssdif_0 fpssdif_1 pssdifn0 sylbi $.
$}
$( /* A subclass missing a member is a proper subclass.  (Contributed by NM,
     12-Jan-2002.) */

$)
${
	fssnelpss_0 $f class A $.
	fssnelpss_1 $f class B $.
	fssnelpss_2 $f class C $.
	ssnelpss $p |- ( A C_ B -> ( ( C e. B /\ -. C e. A ) -> A C. B ) ) $= fssnelpss_2 fssnelpss_1 wcel fssnelpss_2 fssnelpss_0 wcel wn wa fssnelpss_0 fssnelpss_1 wceq wn fssnelpss_0 fssnelpss_1 wss fssnelpss_0 fssnelpss_1 wpss fssnelpss_2 fssnelpss_1 wcel fssnelpss_2 fssnelpss_0 wcel wn wa fssnelpss_1 fssnelpss_0 wceq fssnelpss_0 fssnelpss_1 wceq fssnelpss_2 fssnelpss_1 fssnelpss_0 nelneq2 fssnelpss_1 fssnelpss_0 eqcom sylnib fssnelpss_0 fssnelpss_1 wpss fssnelpss_0 fssnelpss_1 wss fssnelpss_0 fssnelpss_1 wceq wn fssnelpss_0 fssnelpss_1 dfpss2 baibr syl5ib $.
$}
$( /* Subclass inclusion with one element of the superclass missing is proper
       subclass inclusion.  Deduction form of ~ ssnelpss .  (Contributed by
       David Moews, 1-May-2017.) */

$)
${
	fssnelpssd_0 $f wff ph $.
	fssnelpssd_1 $f class A $.
	fssnelpssd_2 $f class B $.
	fssnelpssd_3 $f class C $.
	essnelpssd_0 $e |- ( ph -> A C_ B ) $.
	essnelpssd_1 $e |- ( ph -> C e. B ) $.
	essnelpssd_2 $e |- ( ph -> -. C e. A ) $.
	ssnelpssd $p |- ( ph -> A C. B ) $= fssnelpssd_0 fssnelpssd_3 fssnelpssd_2 wcel fssnelpssd_3 fssnelpssd_1 wcel wn fssnelpssd_1 fssnelpssd_2 wpss essnelpssd_1 essnelpssd_2 fssnelpssd_0 fssnelpssd_1 fssnelpssd_2 wss fssnelpssd_3 fssnelpssd_2 wcel fssnelpssd_3 fssnelpssd_1 wcel wn wa fssnelpssd_1 fssnelpssd_2 wpss wi essnelpssd_0 fssnelpssd_1 fssnelpssd_2 fssnelpssd_3 ssnelpss syl mp2and $.
$}
$( /* A proper subclass has a member in one argument that's not in both.
       (Contributed by NM, 29-Feb-1996.) */

$)
${
	$d x A $.
	$d x B $.
	fpssnel_0 $f set x $.
	fpssnel_1 $f class A $.
	fpssnel_2 $f class B $.
	pssnel $p |- ( A C. B -> E. x ( x e. B /\ -. x e. A ) ) $= fpssnel_1 fpssnel_2 wpss fpssnel_0 sup_set_class fpssnel_2 fpssnel_1 cdif wcel fpssnel_0 wex fpssnel_0 sup_set_class fpssnel_2 wcel fpssnel_0 sup_set_class fpssnel_1 wcel wn wa fpssnel_0 wex fpssnel_1 fpssnel_2 wpss fpssnel_2 fpssnel_1 cdif c0 wne fpssnel_0 sup_set_class fpssnel_2 fpssnel_1 cdif wcel fpssnel_0 wex fpssnel_1 fpssnel_2 pssdif fpssnel_0 fpssnel_2 fpssnel_1 cdif n0 sylib fpssnel_0 sup_set_class fpssnel_2 fpssnel_1 cdif wcel fpssnel_0 sup_set_class fpssnel_2 wcel fpssnel_0 sup_set_class fpssnel_1 wcel wn wa fpssnel_0 fpssnel_0 sup_set_class fpssnel_2 fpssnel_1 eldif exbii sylib $.
$}
$( /* Difference, intersection, and subclass relationship.  (Contributed by
       NM, 30-Apr-1994.)  (Proof shortened by Wolf Lammen, 30-Sep-2014.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	idifin0ss_0 $f set x $.
	fdifin0ss_0 $f class A $.
	fdifin0ss_1 $f class B $.
	fdifin0ss_2 $f class C $.
	difin0ss $p |- ( ( ( A \ B ) i^i C ) = (/) -> ( C C_ A -> C C_ B ) ) $= fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin c0 wceq idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel wn idifin0ss_0 wal fdifin0ss_2 fdifin0ss_0 wss fdifin0ss_2 fdifin0ss_1 wss wi idifin0ss_0 fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin eq0 idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel wn idifin0ss_0 wal idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel wi idifin0ss_0 wal idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi idifin0ss_0 wal fdifin0ss_2 fdifin0ss_0 wss fdifin0ss_2 fdifin0ss_1 wss idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel wn idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel wi idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi idifin0ss_0 idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel wn idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi wi idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel wi idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi wi idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi wi idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi wn wa idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi iman idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wn wa idifin0ss_0 sup_set_class fdifin0ss_2 wcel wa idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wn wa wa idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi wn wa idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 cin wcel idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif wcel idifin0ss_0 sup_set_class fdifin0ss_2 wcel wa idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wn wa idifin0ss_0 sup_set_class fdifin0ss_2 wcel wa idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif fdifin0ss_2 elin idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 cdif wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wn wa idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 fdifin0ss_1 eldif anbi1i bitri idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wn wa ancom idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wn wa idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel wi wn idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel annim anbi2i 3bitr2i xchbinxr idifin0ss_0 sup_set_class fdifin0ss_2 wcel idifin0ss_0 sup_set_class fdifin0ss_0 wcel idifin0ss_0 sup_set_class fdifin0ss_1 wcel ax-2 sylbir al2imi idifin0ss_0 fdifin0ss_2 fdifin0ss_0 dfss2 idifin0ss_0 fdifin0ss_2 fdifin0ss_1 dfss2 3imtr4g sylbi $.
$}
$( /* Intersection, subclass, and difference relationship.  (Contributed by
       NM, 27-Oct-1996.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.)
       (Proof shortened by Wolf Lammen, 30-Sep-2014.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	iinssdif0_0 $f set x $.
	finssdif0_0 $f class A $.
	finssdif0_1 $f class B $.
	finssdif0_2 $f class C $.
	inssdif0 $p |- ( ( A i^i B ) C_ C <-> ( A i^i ( B \ C ) ) = (/) ) $= iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 cin wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wi iinssdif0_0 wal iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 finssdif0_2 cdif cin wcel wn iinssdif0_0 wal finssdif0_0 finssdif0_1 cin finssdif0_2 wss finssdif0_0 finssdif0_1 finssdif0_2 cdif cin c0 wceq iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 cin wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wi iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 finssdif0_2 cdif cin wcel wn iinssdif0_0 iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 cin wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wi iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel wa iinssdif0_0 sup_set_class finssdif0_2 wcel wn wa iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 finssdif0_2 cdif cin wcel iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 cin wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wi iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel wa iinssdif0_0 sup_set_class finssdif0_2 wcel wi iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel wa iinssdif0_0 sup_set_class finssdif0_2 wcel wn wa wn iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 cin wcel iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel wa iinssdif0_0 sup_set_class finssdif0_2 wcel iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 elin imbi1i iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel wa iinssdif0_0 sup_set_class finssdif0_2 wcel iman bitri iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 finssdif0_2 cdif wcel wa iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wn wa wa iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 finssdif0_2 cdif cin wcel iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel wa iinssdif0_0 sup_set_class finssdif0_2 wcel wn wa iinssdif0_0 sup_set_class finssdif0_1 finssdif0_2 cdif wcel iinssdif0_0 sup_set_class finssdif0_1 wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wn wa iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 finssdif0_2 eldif anbi2i iinssdif0_0 sup_set_class finssdif0_0 finssdif0_1 finssdif0_2 cdif elin iinssdif0_0 sup_set_class finssdif0_0 wcel iinssdif0_0 sup_set_class finssdif0_1 wcel iinssdif0_0 sup_set_class finssdif0_2 wcel wn anass 3bitr4ri xchbinx albii iinssdif0_0 finssdif0_0 finssdif0_1 cin finssdif0_2 dfss2 iinssdif0_0 finssdif0_0 finssdif0_1 finssdif0_2 cdif cin eq0 3bitr4i $.
$}
$( /* The difference between a class and itself is the empty set.  Proposition
     5.15 of [TakeutiZaring] p. 20.  Also Theorem 32 of [Suppes] p. 28.
     (Contributed by NM, 22-Apr-2004.) */

$)
${
	fdifid_0 $f class A $.
	difid $p |- ( A \ A ) = (/) $= fdifid_0 fdifid_0 wss fdifid_0 fdifid_0 cdif c0 wceq fdifid_0 ssid fdifid_0 fdifid_0 ssdif0 mpbi $.
$}
$( /* The difference between a class and itself is the empty set.  Proposition
       5.15 of [TakeutiZaring] p. 20.  Also Theorem 32 of [Suppes] p. 28.
       Alternate proof of ~ difid .  (Contributed by David Abernethy,
       17-Jun-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) */

$)
${
	$d x A $.
	idifidALT_0 $f set x $.
	fdifidALT_0 $f class A $.
	difidALT $p |- ( A \ A ) = (/) $= fdifidALT_0 fdifidALT_0 cdif idifidALT_0 sup_set_class fdifidALT_0 wcel wn idifidALT_0 fdifidALT_0 crab c0 idifidALT_0 fdifidALT_0 fdifidALT_0 dfdif2 idifidALT_0 fdifidALT_0 dfnul3 eqtr4i $.
$}
$( /* The difference between a class and the empty set.  Part of Exercise 4.4 of
     [Stoll] p. 16.  (Contributed by NM, 17-Aug-2004.) */

$)
${
	fdif0_0 $f class A $.
	dif0 $p |- ( A \ (/) ) = A $= fdif0_0 fdif0_0 fdif0_0 cdif cdif fdif0_0 c0 cdif fdif0_0 fdif0_0 fdif0_0 cdif c0 fdif0_0 fdif0_0 difid difeq2i fdif0_0 fdif0_0 difdif eqtr3i $.
$}
$( /* The difference between the empty set and a class.  Part of Exercise 4.4 of
     [Stoll] p. 16.  (Contributed by NM, 17-Aug-2004.) */

$)
${
	f0dif_0 $f class A $.
	0dif $p |- ( (/) \ A ) = (/) $= c0 f0dif_0 cdif c0 wss c0 f0dif_0 cdif c0 wceq c0 f0dif_0 difss c0 f0dif_0 cdif ss0 ax-mp $.
$}
$( /* A class and its relative complement are disjoint.  Theorem 38 of [Suppes]
     p. 29.  (Contributed by NM, 24-Mar-1998.) */

$)
${
	fdisjdif_0 $f class A $.
	fdisjdif_1 $f class B $.
	disjdif $p |- ( A i^i ( B \ A ) ) = (/) $= fdisjdif_0 fdisjdif_1 cin fdisjdif_0 wss fdisjdif_0 fdisjdif_1 fdisjdif_0 cdif cin c0 wceq fdisjdif_0 fdisjdif_1 inss1 fdisjdif_0 fdisjdif_1 fdisjdif_0 inssdif0 mpbi $.
$}
$( /* The difference of a class from its intersection is empty.  Theorem 37 of
     [Suppes] p. 29.  (Contributed by NM, 17-Aug-2004.)  (Proof shortened by
     Andrew Salmon, 26-Jun-2011.) */

$)
${
	fdifin0_0 $f class A $.
	fdifin0_1 $f class B $.
	difin0 $p |- ( ( A i^i B ) \ B ) = (/) $= fdifin0_0 fdifin0_1 cin fdifin0_1 wss fdifin0_0 fdifin0_1 cin fdifin0_1 cdif c0 wceq fdifin0_0 fdifin0_1 inss2 fdifin0_0 fdifin0_1 cin fdifin0_1 ssdif0 mpbi $.
$}
$( /* The union of a class and its complement is the universe.  Theorem 5.1(5)
     of [Stoll] p. 17.  (Contributed by NM, 17-Aug-2004.) */

$)
${
	fundifv_0 $f class A $.
	undifv $p |- ( A u. ( _V \ A ) ) = _V $= fundifv_0 cvv fundifv_0 cdif cun cvv cvv fundifv_0 cdif cvv cvv fundifv_0 cdif cdif cin cdif cvv c0 cdif cvv fundifv_0 cvv fundifv_0 cdif dfun3 cvv fundifv_0 cdif cvv cvv fundifv_0 cdif cdif cin c0 cvv cvv fundifv_0 cdif cvv disjdif difeq2i cvv dif0 3eqtri $.
$}
$( /* Absorption of difference by union.  This decomposes a union into two
     disjoint classes (see ~ disjdif ).  Theorem 35 of [Suppes] p. 29.
     (Contributed by NM, 19-May-1998.) */

$)
${
	fundif1_0 $f class A $.
	fundif1_1 $f class B $.
	undif1 $p |- ( ( A \ B ) u. B ) = ( A u. B ) $= fundif1_0 cvv fundif1_1 cdif cin fundif1_1 cun fundif1_0 fundif1_1 cun cvv fundif1_1 cdif fundif1_1 cun cin fundif1_0 fundif1_1 cdif fundif1_1 cun fundif1_0 fundif1_1 cun fundif1_0 cvv fundif1_1 cdif fundif1_1 undir fundif1_0 cvv fundif1_1 cdif cin fundif1_0 fundif1_1 cdif fundif1_1 fundif1_0 fundif1_1 invdif uneq1i fundif1_0 fundif1_1 cun cvv fundif1_1 cdif fundif1_1 cun cin fundif1_0 fundif1_1 cun cvv cin fundif1_0 fundif1_1 cun cvv fundif1_1 cdif fundif1_1 cun cvv fundif1_0 fundif1_1 cun cvv fundif1_1 cdif fundif1_1 cun fundif1_1 cvv fundif1_1 cdif cun cvv cvv fundif1_1 cdif fundif1_1 uncom fundif1_1 undifv eqtri ineq2i fundif1_0 fundif1_1 cun inv1 eqtri 3eqtr3i $.
$}
$( /* Absorption of difference by union.  This decomposes a union into two
     disjoint classes (see ~ disjdif ).  Part of proof of Corollary 6K of
     [Enderton] p. 144.  (Contributed by NM, 19-May-1998.) */

$)
${
	fundif2_0 $f class A $.
	fundif2_1 $f class B $.
	undif2 $p |- ( A u. ( B \ A ) ) = ( A u. B ) $= fundif2_0 fundif2_1 fundif2_0 cdif cun fundif2_1 fundif2_0 cdif fundif2_0 cun fundif2_1 fundif2_0 cun fundif2_0 fundif2_1 cun fundif2_0 fundif2_1 fundif2_0 cdif uncom fundif2_1 fundif2_0 undif1 fundif2_1 fundif2_0 uncom 3eqtri $.
$}
$( /* Absorption of difference by union.  (Contributed by NM, 18-Aug-2013.) */

$)
${
	fundifabs_0 $f class A $.
	fundifabs_1 $f class B $.
	undifabs $p |- ( A u. ( A \ B ) ) = A $= fundifabs_0 fundifabs_0 fundifabs_1 cdif cun fundifabs_0 fundifabs_0 cun fundifabs_1 fundifabs_0 cdif cdif fundifabs_0 fundifabs_1 fundifabs_0 cdif cdif fundifabs_0 fundifabs_0 fundifabs_0 fundifabs_1 undif3 fundifabs_0 fundifabs_0 cun fundifabs_0 fundifabs_1 fundifabs_0 cdif fundifabs_0 unidm difeq1i fundifabs_0 fundifabs_1 difdif 3eqtri $.
$}
$( /* The intersection and class difference of a class with another class
       unite to give the original class.  (Contributed by Paul Chapman,
       5-Jun-2009.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	$d x A $.
	$d x B $.
	iinundif_0 $f set x $.
	finundif_0 $f class A $.
	finundif_1 $f class B $.
	inundif $p |- ( ( A i^i B ) u. ( A \ B ) ) = A $= iinundif_0 finundif_0 finundif_1 cin finundif_0 finundif_1 cdif finundif_0 iinundif_0 sup_set_class finundif_0 finundif_1 cin wcel iinundif_0 sup_set_class finundif_0 finundif_1 cdif wcel wo iinundif_0 sup_set_class finundif_0 wcel iinundif_0 sup_set_class finundif_1 wcel wa iinundif_0 sup_set_class finundif_0 wcel iinundif_0 sup_set_class finundif_1 wcel wn wa wo iinundif_0 sup_set_class finundif_0 wcel iinundif_0 sup_set_class finundif_0 finundif_1 cin wcel iinundif_0 sup_set_class finundif_0 wcel iinundif_0 sup_set_class finundif_1 wcel wa iinundif_0 sup_set_class finundif_0 finundif_1 cdif wcel iinundif_0 sup_set_class finundif_0 wcel iinundif_0 sup_set_class finundif_1 wcel wn wa iinundif_0 sup_set_class finundif_0 finundif_1 elin iinundif_0 sup_set_class finundif_0 finundif_1 eldif orbi12i iinundif_0 sup_set_class finundif_0 wcel iinundif_0 sup_set_class finundif_1 wcel pm4.42 bitr4i uneqri $.
$}
$( /* Absorption of union by difference.  Theorem 36 of [Suppes] p. 29.
     (Contributed by NM, 19-May-1998.) */

$)
${
	fdifun2_0 $f class A $.
	fdifun2_1 $f class B $.
	difun2 $p |- ( ( A u. B ) \ B ) = ( A \ B ) $= fdifun2_0 fdifun2_1 cun fdifun2_1 cdif fdifun2_0 fdifun2_1 cdif fdifun2_1 fdifun2_1 cdif cun fdifun2_0 fdifun2_1 cdif c0 cun fdifun2_0 fdifun2_1 cdif fdifun2_0 fdifun2_1 fdifun2_1 difundir fdifun2_1 fdifun2_1 cdif c0 fdifun2_0 fdifun2_1 cdif fdifun2_1 difid uneq2i fdifun2_0 fdifun2_1 cdif un0 3eqtri $.
$}
$( /* Union of complementary parts into whole.  (Contributed by NM,
     22-Mar-1998.) */

$)
${
	fundif_0 $f class A $.
	fundif_1 $f class B $.
	undif $p |- ( A C_ B <-> ( A u. ( B \ A ) ) = B ) $= fundif_0 fundif_1 wss fundif_0 fundif_1 cun fundif_1 wceq fundif_0 fundif_1 fundif_0 cdif cun fundif_1 wceq fundif_0 fundif_1 ssequn1 fundif_0 fundif_1 fundif_0 cdif cun fundif_0 fundif_1 cun fundif_1 fundif_0 fundif_1 undif2 eqeq1i bitr4i $.
$}
$( /* A subset of a difference does not intersect the subtrahend.  (Contributed
     by Jeff Hankins, 1-Sep-2013.)  (Proof shortened by Mario Carneiro,
     24-Aug-2015.) */

$)
${
	fssdifin0_0 $f class A $.
	fssdifin0_1 $f class B $.
	fssdifin0_2 $f class C $.
	ssdifin0 $p |- ( A C_ ( B \ C ) -> ( A i^i C ) = (/) ) $= fssdifin0_0 fssdifin0_1 fssdifin0_2 cdif wss fssdifin0_0 fssdifin0_2 cin fssdifin0_1 fssdifin0_2 cdif fssdifin0_2 cin wss fssdifin0_1 fssdifin0_2 cdif fssdifin0_2 cin c0 wceq fssdifin0_0 fssdifin0_2 cin c0 wceq fssdifin0_0 fssdifin0_1 fssdifin0_2 cdif fssdifin0_2 ssrin fssdifin0_1 fssdifin0_2 cdif fssdifin0_2 cin fssdifin0_2 fssdifin0_1 fssdifin0_2 cdif cin c0 fssdifin0_1 fssdifin0_2 cdif fssdifin0_2 incom fssdifin0_2 fssdifin0_1 disjdif eqtri fssdifin0_0 fssdifin0_2 cin fssdifin0_1 fssdifin0_2 cdif fssdifin0_2 cin sseq0 sylancl $.
$}
$( /* A class is a subclass of itself subtracted from another iff it is the
     empty set.  (Contributed by Steve Rodriguez, 20-Nov-2015.) */

$)
${
	fssdifeq0_0 $f class A $.
	fssdifeq0_1 $f class B $.
	ssdifeq0 $p |- ( A C_ ( B \ A ) <-> A = (/) ) $= fssdifeq0_0 fssdifeq0_1 fssdifeq0_0 cdif wss fssdifeq0_0 c0 wceq fssdifeq0_0 fssdifeq0_1 fssdifeq0_0 cdif wss fssdifeq0_0 fssdifeq0_0 fssdifeq0_0 cin c0 fssdifeq0_0 inidm fssdifeq0_0 fssdifeq0_1 fssdifeq0_0 ssdifin0 syl5eqr fssdifeq0_0 c0 wceq fssdifeq0_0 fssdifeq0_1 fssdifeq0_0 cdif wss c0 fssdifeq0_1 c0 cdif wss fssdifeq0_1 c0 cdif 0ss fssdifeq0_0 c0 wceq fssdifeq0_0 c0 fssdifeq0_1 fssdifeq0_0 cdif fssdifeq0_1 c0 cdif fssdifeq0_0 c0 wceq id fssdifeq0_0 c0 fssdifeq0_1 difeq2 sseq12d mpbiri impbii $.
$}
$( /* A condition equivalent to inclusion in the union of two classes.
       (Contributed by NM, 26-Mar-2007.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	issundif_0 $f set x $.
	fssundif_0 $f class A $.
	fssundif_1 $f class B $.
	fssundif_2 $f class C $.
	ssundif $p |- ( A C_ ( B u. C ) <-> ( A \ B ) C_ C ) $= issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 fssundif_2 cun wcel wi issundif_0 wal issundif_0 sup_set_class fssundif_0 fssundif_1 cdif wcel issundif_0 sup_set_class fssundif_2 wcel wi issundif_0 wal fssundif_0 fssundif_1 fssundif_2 cun wss fssundif_0 fssundif_1 cdif fssundif_2 wss issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 fssundif_2 cun wcel wi issundif_0 sup_set_class fssundif_0 fssundif_1 cdif wcel issundif_0 sup_set_class fssundif_2 wcel wi issundif_0 issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 wcel wn wa issundif_0 sup_set_class fssundif_2 wcel wi issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 wcel issundif_0 sup_set_class fssundif_2 wcel wo wi issundif_0 sup_set_class fssundif_0 fssundif_1 cdif wcel issundif_0 sup_set_class fssundif_2 wcel wi issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 fssundif_2 cun wcel wi issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 wcel issundif_0 sup_set_class fssundif_2 wcel pm5.6 issundif_0 sup_set_class fssundif_0 fssundif_1 cdif wcel issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 wcel wn wa issundif_0 sup_set_class fssundif_2 wcel issundif_0 sup_set_class fssundif_0 fssundif_1 eldif imbi1i issundif_0 sup_set_class fssundif_1 fssundif_2 cun wcel issundif_0 sup_set_class fssundif_1 wcel issundif_0 sup_set_class fssundif_2 wcel wo issundif_0 sup_set_class fssundif_0 wcel issundif_0 sup_set_class fssundif_1 fssundif_2 elun imbi2i 3bitr4ri albii issundif_0 fssundif_0 fssundif_1 fssundif_2 cun dfss2 issundif_0 fssundif_0 fssundif_1 cdif fssundif_2 dfss2 3bitr4i $.
$}
$( /* Swap the arguments of a class difference.  (Contributed by NM,
     29-Mar-2007.) */

$)
${
	fdifcom_0 $f class A $.
	fdifcom_1 $f class B $.
	fdifcom_2 $f class C $.
	difcom $p |- ( ( A \ B ) C_ C <-> ( A \ C ) C_ B ) $= fdifcom_0 fdifcom_1 fdifcom_2 cun wss fdifcom_0 fdifcom_2 fdifcom_1 cun wss fdifcom_0 fdifcom_1 cdif fdifcom_2 wss fdifcom_0 fdifcom_2 cdif fdifcom_1 wss fdifcom_1 fdifcom_2 cun fdifcom_2 fdifcom_1 cun fdifcom_0 fdifcom_1 fdifcom_2 uncom sseq2i fdifcom_0 fdifcom_1 fdifcom_2 ssundif fdifcom_0 fdifcom_2 fdifcom_1 ssundif 3bitr3i $.
$}
$( /* Two ways to express overlapping subsets.  (Contributed by Stefan O'Rear,
     31-Oct-2014.) */

$)
${
	fpssdifcom1_0 $f class A $.
	fpssdifcom1_1 $f class B $.
	fpssdifcom1_2 $f class C $.
	pssdifcom1 $p |- ( ( A C_ C /\ B C_ C ) -> ( ( C \ A ) C. B <-> ( C \ B ) C. A ) ) $= fpssdifcom1_0 fpssdifcom1_2 wss fpssdifcom1_1 fpssdifcom1_2 wss wa fpssdifcom1_2 fpssdifcom1_0 cdif fpssdifcom1_1 wss fpssdifcom1_1 fpssdifcom1_2 fpssdifcom1_0 cdif wss wn wa fpssdifcom1_2 fpssdifcom1_1 cdif fpssdifcom1_0 wss fpssdifcom1_0 fpssdifcom1_2 fpssdifcom1_1 cdif wss wn wa fpssdifcom1_2 fpssdifcom1_0 cdif fpssdifcom1_1 wpss fpssdifcom1_2 fpssdifcom1_1 cdif fpssdifcom1_0 wpss fpssdifcom1_0 fpssdifcom1_2 wss fpssdifcom1_1 fpssdifcom1_2 wss wa fpssdifcom1_2 fpssdifcom1_0 cdif fpssdifcom1_1 wss fpssdifcom1_2 fpssdifcom1_1 cdif fpssdifcom1_0 wss fpssdifcom1_1 fpssdifcom1_2 fpssdifcom1_0 cdif wss wn fpssdifcom1_0 fpssdifcom1_2 fpssdifcom1_1 cdif wss wn fpssdifcom1_2 fpssdifcom1_0 cdif fpssdifcom1_1 wss fpssdifcom1_2 fpssdifcom1_1 cdif fpssdifcom1_0 wss wb fpssdifcom1_0 fpssdifcom1_2 wss fpssdifcom1_1 fpssdifcom1_2 wss wa fpssdifcom1_2 fpssdifcom1_0 fpssdifcom1_1 difcom a1i fpssdifcom1_0 fpssdifcom1_2 wss fpssdifcom1_1 fpssdifcom1_2 wss wa fpssdifcom1_1 fpssdifcom1_2 fpssdifcom1_0 cdif wss fpssdifcom1_0 fpssdifcom1_2 fpssdifcom1_1 cdif wss fpssdifcom1_1 fpssdifcom1_2 wss fpssdifcom1_0 fpssdifcom1_2 wss fpssdifcom1_1 fpssdifcom1_2 fpssdifcom1_0 cdif wss fpssdifcom1_0 fpssdifcom1_2 fpssdifcom1_1 cdif wss wb fpssdifcom1_1 fpssdifcom1_0 fpssdifcom1_2 ssconb ancoms notbid anbi12d fpssdifcom1_2 fpssdifcom1_0 cdif fpssdifcom1_1 dfpss3 fpssdifcom1_2 fpssdifcom1_1 cdif fpssdifcom1_0 dfpss3 3bitr4g $.
$}
$( /* Two ways to express non-covering pairs of subsets.  (Contributed by Stefan
     O'Rear, 31-Oct-2014.) */

$)
${
	fpssdifcom2_0 $f class A $.
	fpssdifcom2_1 $f class B $.
	fpssdifcom2_2 $f class C $.
	pssdifcom2 $p |- ( ( A C_ C /\ B C_ C ) -> ( B C. ( C \ A ) <-> A C. ( C \ B ) ) ) $= fpssdifcom2_0 fpssdifcom2_2 wss fpssdifcom2_1 fpssdifcom2_2 wss wa fpssdifcom2_1 fpssdifcom2_2 fpssdifcom2_0 cdif wss fpssdifcom2_2 fpssdifcom2_0 cdif fpssdifcom2_1 wss wn wa fpssdifcom2_0 fpssdifcom2_2 fpssdifcom2_1 cdif wss fpssdifcom2_2 fpssdifcom2_1 cdif fpssdifcom2_0 wss wn wa fpssdifcom2_1 fpssdifcom2_2 fpssdifcom2_0 cdif wpss fpssdifcom2_0 fpssdifcom2_2 fpssdifcom2_1 cdif wpss fpssdifcom2_0 fpssdifcom2_2 wss fpssdifcom2_1 fpssdifcom2_2 wss wa fpssdifcom2_1 fpssdifcom2_2 fpssdifcom2_0 cdif wss fpssdifcom2_0 fpssdifcom2_2 fpssdifcom2_1 cdif wss fpssdifcom2_2 fpssdifcom2_0 cdif fpssdifcom2_1 wss wn fpssdifcom2_2 fpssdifcom2_1 cdif fpssdifcom2_0 wss wn fpssdifcom2_1 fpssdifcom2_2 wss fpssdifcom2_0 fpssdifcom2_2 wss fpssdifcom2_1 fpssdifcom2_2 fpssdifcom2_0 cdif wss fpssdifcom2_0 fpssdifcom2_2 fpssdifcom2_1 cdif wss wb fpssdifcom2_1 fpssdifcom2_0 fpssdifcom2_2 ssconb ancoms fpssdifcom2_0 fpssdifcom2_2 wss fpssdifcom2_1 fpssdifcom2_2 wss wa fpssdifcom2_2 fpssdifcom2_0 cdif fpssdifcom2_1 wss fpssdifcom2_2 fpssdifcom2_1 cdif fpssdifcom2_0 wss fpssdifcom2_2 fpssdifcom2_0 cdif fpssdifcom2_1 wss fpssdifcom2_2 fpssdifcom2_1 cdif fpssdifcom2_0 wss wb fpssdifcom2_0 fpssdifcom2_2 wss fpssdifcom2_1 fpssdifcom2_2 wss wa fpssdifcom2_2 fpssdifcom2_0 fpssdifcom2_1 difcom a1i notbid anbi12d fpssdifcom2_1 fpssdifcom2_2 fpssdifcom2_0 cdif dfpss3 fpssdifcom2_0 fpssdifcom2_2 fpssdifcom2_1 cdif dfpss3 3bitr4g $.
$}
$( /* Distributive law for class difference.  Exercise 4.8 of [Stoll] p. 16.
     (Contributed by NM, 18-Aug-2004.) */

$)
${
	fdifdifdir_0 $f class A $.
	fdifdifdir_1 $f class B $.
	fdifdifdir_2 $f class C $.
	difdifdir $p |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ ( B \ C ) ) $= fdifdifdir_0 fdifdifdir_1 cdif fdifdifdir_2 cdif fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif fdifdifdir_2 cun cin fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 fdifdifdir_2 cdif cdif cin fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_1 fdifdifdir_2 cdif cdif fdifdifdir_0 fdifdifdir_1 cdif fdifdifdir_2 cdif fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin c0 cun fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif fdifdifdir_2 cun cin fdifdifdir_0 fdifdifdir_1 cdif fdifdifdir_2 cdif fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin c0 cun fdifdifdir_0 fdifdifdir_1 cdif fdifdifdir_2 cdif fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_1 cdif fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin fdifdifdir_0 fdifdifdir_1 fdifdifdir_2 dif32 fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_1 invdif eqtr4i fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin un0 eqtr4i fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif fdifdifdir_2 cun cin fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_2 cin cun fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin c0 cun fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif fdifdifdir_2 indi c0 fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_2 cin fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cin fdifdifdir_2 fdifdifdir_0 fdifdifdir_2 cdif cin c0 fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_2 cin fdifdifdir_2 fdifdifdir_0 disjdif fdifdifdir_2 fdifdifdir_0 fdifdifdir_2 cdif incom eqtr3i uneq2i eqtr4i eqtr4i cvv fdifdifdir_1 cdif fdifdifdir_2 cun cvv fdifdifdir_1 fdifdifdir_2 cdif cdif fdifdifdir_0 fdifdifdir_2 cdif cvv fdifdifdir_1 cdif cvv cvv fdifdifdir_2 cdif cdif cun cvv fdifdifdir_1 cdif fdifdifdir_2 cun cvv fdifdifdir_1 fdifdifdir_2 cdif cdif cvv cvv fdifdifdir_2 cdif cdif fdifdifdir_2 cvv fdifdifdir_1 cdif fdifdifdir_2 ddif uneq2i cvv fdifdifdir_1 cvv fdifdifdir_2 cdif cin cdif cvv fdifdifdir_1 cdif cvv cvv fdifdifdir_2 cdif cdif cun cvv fdifdifdir_1 fdifdifdir_2 cdif cdif fdifdifdir_1 cvv fdifdifdir_2 cdif indm fdifdifdir_1 cvv fdifdifdir_2 cdif cin fdifdifdir_1 fdifdifdir_2 cdif cvv fdifdifdir_1 fdifdifdir_2 invdif difeq2i eqtr3i eqtr3i ineq2i fdifdifdir_0 fdifdifdir_2 cdif fdifdifdir_1 fdifdifdir_2 cdif invdif 3eqtri $.
$}
$( /* Two ways to say that ` A ` and ` B ` partition ` C ` (when ` A ` and ` B `
     don't overlap and ` A ` is a part of ` C ` ).  (Contributed by FL,
     17-Nov-2008.) */

$)
${
	funeqdifeq_0 $f class A $.
	funeqdifeq_1 $f class B $.
	funeqdifeq_2 $f class C $.
	uneqdifeq $p |- ( ( A C_ C /\ ( A i^i B ) = (/) ) -> ( ( A u. B ) = C <-> ( C \ A ) = B ) ) $= funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cin c0 wceq wa funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wi funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 funeqdifeq_1 cun wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wi funeqdifeq_1 funeqdifeq_0 uncom funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 funeqdifeq_1 cun wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq wa funeqdifeq_2 funeqdifeq_1 funeqdifeq_0 cun wceq funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wi funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 funeqdifeq_1 cun wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq wa funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_2 funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 eqtr eqcomd funeqdifeq_2 funeqdifeq_1 funeqdifeq_0 cun wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 cdif wceq funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wi funeqdifeq_2 funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 difeq1 funeqdifeq_1 funeqdifeq_0 difun2 funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 cdif wceq funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif wceq wa funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cun funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif eqtr funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_1 funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wi funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_1 funeqdifeq_0 cin c0 wceq funeqdifeq_1 funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_0 funeqdifeq_1 cin funeqdifeq_1 funeqdifeq_0 cin c0 funeqdifeq_0 funeqdifeq_1 incom eqeq1i funeqdifeq_1 funeqdifeq_0 disj3 bitri funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wi funeqdifeq_1 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif wceq funeqdifeq_1 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_0 cdif funeqdifeq_1 eqtr expcom eqcoms sylbi syl5com sylancl syl mpan com12 adantl funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cin c0 wceq wa funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wceq funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cin c0 wceq wa funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wa funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cin c0 wceq wa funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss wi funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss wi funeqdifeq_2 funeqdifeq_0 difss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_2 wss funeqdifeq_1 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss wi funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 funeqdifeq_2 sseq1 funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_1 funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_1 funeqdifeq_2 wss wa funeqdifeq_0 funeqdifeq_1 cun funeqdifeq_2 wss funeqdifeq_0 funeqdifeq_1 funeqdifeq_2 unss biimpi expcom syl6bi mpi com12 adantr imp funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 funeqdifeq_1 cun wss funeqdifeq_0 funeqdifeq_1 cin c0 wceq funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq wa funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wss funeqdifeq_2 funeqdifeq_0 funeqdifeq_1 cun wss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wceq funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 wss funeqdifeq_0 funeqdifeq_2 wss funeqdifeq_2 funeqdifeq_0 cdif funeqdifeq_1 eqimss adantl funeqdifeq_2 funeqdifeq_0 funeqdifeq_1 ssundif sylibr adantlr eqssd ex impbid $.
$}
$( /* Theorem 19.2 of [Margaris] p. 89 with restricted quantifiers (compare
       ~ 19.2 ).  The restricted version is valid only when the domain of
       quantification is not empty.  (Contributed by NM, 15-Nov-2003.) */

$)
${
	$d x A $.
	fr19.2z_0 $f wff ph $.
	fr19.2z_1 $f set x $.
	fr19.2z_2 $f class A $.
	r19.2z $p |- ( ( A =/= (/) /\ A. x e. A ph ) -> E. x e. A ph ) $= fr19.2z_0 fr19.2z_1 fr19.2z_2 wral fr19.2z_2 c0 wne fr19.2z_0 fr19.2z_1 fr19.2z_2 wrex fr19.2z_0 fr19.2z_1 fr19.2z_2 wral fr19.2z_1 sup_set_class fr19.2z_2 wcel fr19.2z_1 wex fr19.2z_1 sup_set_class fr19.2z_2 wcel fr19.2z_0 wa fr19.2z_1 wex fr19.2z_2 c0 wne fr19.2z_0 fr19.2z_1 fr19.2z_2 wrex fr19.2z_0 fr19.2z_1 fr19.2z_2 wral fr19.2z_1 sup_set_class fr19.2z_2 wcel fr19.2z_0 wi fr19.2z_1 wal fr19.2z_1 sup_set_class fr19.2z_2 wcel fr19.2z_1 wex fr19.2z_1 sup_set_class fr19.2z_2 wcel fr19.2z_0 wa fr19.2z_1 wex wi fr19.2z_0 fr19.2z_1 fr19.2z_2 df-ral fr19.2z_1 sup_set_class fr19.2z_2 wcel fr19.2z_0 fr19.2z_1 exintr sylbi fr19.2z_1 fr19.2z_2 n0 fr19.2z_0 fr19.2z_1 fr19.2z_2 df-rex 3imtr4g impcom $.
$}
$( /* A response to the notion that the condition ` A =/= (/) ` can be removed
       in ~ r19.2z .  Interestingly enough, ` ph ` does not figure in the
       left-hand side.  (Contributed by Jeff Hankins, 24-Aug-2009.) */

$)
${
	$d x A $.
	fr19.2zb_0 $f wff ph $.
	fr19.2zb_1 $f set x $.
	fr19.2zb_2 $f class A $.
	r19.2zb $p |- ( A =/= (/) <-> ( A. x e. A ph -> E. x e. A ph ) ) $= fr19.2zb_2 c0 wne fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wral fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wrex wi fr19.2zb_2 c0 wne fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wral fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wrex fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 r19.2z ex fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wral fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wrex fr19.2zb_2 c0 wne fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wral fr19.2zb_2 c0 fr19.2zb_2 c0 wceq fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wral fr19.2zb_0 fr19.2zb_1 c0 wral fr19.2zb_0 fr19.2zb_1 c0 fr19.2zb_1 sup_set_class c0 wcel fr19.2zb_0 fr19.2zb_1 sup_set_class noel pm2.21i rgen fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 c0 raleq mpbiri necon3bi fr19.2zb_1 sup_set_class fr19.2zb_2 wcel fr19.2zb_0 wa fr19.2zb_1 wex fr19.2zb_1 sup_set_class fr19.2zb_2 wcel fr19.2zb_1 wex fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 wrex fr19.2zb_2 c0 wne fr19.2zb_1 sup_set_class fr19.2zb_2 wcel fr19.2zb_0 fr19.2zb_1 exsimpl fr19.2zb_0 fr19.2zb_1 fr19.2zb_2 df-rex fr19.2zb_1 fr19.2zb_2 n0 3imtr4i ja impbii $.
$}
$( /* Restricted quantification of wff not containing quantified variable.
       (Contributed by FL, 3-Jan-2008.) */

$)
${
	$d x A $.
	fr19.3rz_0 $f wff ph $.
	fr19.3rz_1 $f set x $.
	fr19.3rz_2 $f class A $.
	er19.3rz_0 $e |- F/ x ph $.
	r19.3rz $p |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) ) $= fr19.3rz_2 c0 wne fr19.3rz_0 fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_1 wex fr19.3rz_0 wi fr19.3rz_0 fr19.3rz_1 fr19.3rz_2 wral fr19.3rz_2 c0 wne fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_1 wex fr19.3rz_0 fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_1 wex fr19.3rz_0 wi wb fr19.3rz_1 fr19.3rz_2 n0 fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_1 wex fr19.3rz_0 biimt sylbi fr19.3rz_0 fr19.3rz_1 fr19.3rz_2 wral fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_0 wi fr19.3rz_1 wal fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_1 wex fr19.3rz_0 wi fr19.3rz_0 fr19.3rz_1 fr19.3rz_2 df-ral fr19.3rz_1 sup_set_class fr19.3rz_2 wcel fr19.3rz_0 fr19.3rz_1 er19.3rz_0 19.23 bitri syl6bbr $.
$}
$( /* Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 26-Oct-2010.) */

$)
${
	$d x A $.
	fr19.28z_0 $f wff ph $.
	fr19.28z_1 $f wff ps $.
	fr19.28z_2 $f set x $.
	fr19.28z_3 $f class A $.
	er19.28z_0 $e |- F/ x ph $.
	r19.28z $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) ) $= fr19.28z_3 c0 wne fr19.28z_0 fr19.28z_1 fr19.28z_2 fr19.28z_3 wral wa fr19.28z_0 fr19.28z_2 fr19.28z_3 wral fr19.28z_1 fr19.28z_2 fr19.28z_3 wral wa fr19.28z_0 fr19.28z_1 wa fr19.28z_2 fr19.28z_3 wral fr19.28z_3 c0 wne fr19.28z_0 fr19.28z_0 fr19.28z_2 fr19.28z_3 wral fr19.28z_1 fr19.28z_2 fr19.28z_3 wral fr19.28z_0 fr19.28z_2 fr19.28z_3 er19.28z_0 r19.3rz anbi1d fr19.28z_0 fr19.28z_1 fr19.28z_2 fr19.28z_3 r19.26 syl6rbbr $.
$}
$( /* Restricted quantification of wff not containing quantified variable.
       (Contributed by NM, 10-Mar-1997.) */

$)
${
	$d x A $.
	$d x ph $.
	fr19.3rzv_0 $f wff ph $.
	fr19.3rzv_1 $f set x $.
	fr19.3rzv_2 $f class A $.
	r19.3rzv $p |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) ) $= fr19.3rzv_2 c0 wne fr19.3rzv_0 fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_1 wex fr19.3rzv_0 wi fr19.3rzv_0 fr19.3rzv_1 fr19.3rzv_2 wral fr19.3rzv_2 c0 wne fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_1 wex fr19.3rzv_0 fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_1 wex fr19.3rzv_0 wi wb fr19.3rzv_1 fr19.3rzv_2 n0 fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_1 wex fr19.3rzv_0 biimt sylbi fr19.3rzv_0 fr19.3rzv_1 fr19.3rzv_2 wral fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_0 wi fr19.3rzv_1 wal fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_1 wex fr19.3rzv_0 wi fr19.3rzv_0 fr19.3rzv_1 fr19.3rzv_2 df-ral fr19.3rzv_1 sup_set_class fr19.3rzv_2 wcel fr19.3rzv_0 fr19.3rzv_1 19.23v bitri syl6bbr $.
$}
$( /* Restricted quantification of wff not containing quantified variable.
       (Contributed by NM, 27-May-1998.) */

$)
${
	$d x A $.
	$d x ph $.
	fr19.9rzv_0 $f wff ph $.
	fr19.9rzv_1 $f set x $.
	fr19.9rzv_2 $f class A $.
	r19.9rzv $p |- ( A =/= (/) -> ( ph <-> E. x e. A ph ) ) $= fr19.9rzv_2 c0 wne fr19.9rzv_0 fr19.9rzv_0 wn fr19.9rzv_1 fr19.9rzv_2 wral wn fr19.9rzv_0 fr19.9rzv_1 fr19.9rzv_2 wrex fr19.9rzv_2 c0 wne fr19.9rzv_0 wn fr19.9rzv_1 fr19.9rzv_2 wral fr19.9rzv_0 fr19.9rzv_2 c0 wne fr19.9rzv_0 wn fr19.9rzv_0 wn fr19.9rzv_1 fr19.9rzv_2 wral fr19.9rzv_0 wn fr19.9rzv_1 fr19.9rzv_2 r19.3rzv bicomd con2bid fr19.9rzv_0 fr19.9rzv_1 fr19.9rzv_2 dfrex2 syl6bbr $.
$}
$( /* Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 19-Aug-2004.) */

$)
${
	$d x A $.
	$d x ph $.
	fr19.28zv_0 $f wff ph $.
	fr19.28zv_1 $f wff ps $.
	fr19.28zv_2 $f set x $.
	fr19.28zv_3 $f class A $.
	r19.28zv $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) ) $= fr19.28zv_3 c0 wne fr19.28zv_0 fr19.28zv_1 fr19.28zv_2 fr19.28zv_3 wral wa fr19.28zv_0 fr19.28zv_2 fr19.28zv_3 wral fr19.28zv_1 fr19.28zv_2 fr19.28zv_3 wral wa fr19.28zv_0 fr19.28zv_1 wa fr19.28zv_2 fr19.28zv_3 wral fr19.28zv_3 c0 wne fr19.28zv_0 fr19.28zv_0 fr19.28zv_2 fr19.28zv_3 wral fr19.28zv_1 fr19.28zv_2 fr19.28zv_3 wral fr19.28zv_0 fr19.28zv_2 fr19.28zv_3 r19.3rzv anbi1d fr19.28zv_0 fr19.28zv_1 fr19.28zv_2 fr19.28zv_3 r19.26 syl6rbbr $.
$}
$( /* Restricted quantifier version of Theorem 19.37 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by Paul Chapman, 8-Oct-2007.) */

$)
${
	$d x A $.
	$d x ph $.
	fr19.37zv_0 $f wff ph $.
	fr19.37zv_1 $f wff ps $.
	fr19.37zv_2 $f set x $.
	fr19.37zv_3 $f class A $.
	r19.37zv $p |- ( A =/= (/) -> ( E. x e. A ( ph -> ps ) <-> ( ph -> E. x e. A ps ) ) ) $= fr19.37zv_3 c0 wne fr19.37zv_0 fr19.37zv_1 fr19.37zv_2 fr19.37zv_3 wrex wi fr19.37zv_0 fr19.37zv_2 fr19.37zv_3 wral fr19.37zv_1 fr19.37zv_2 fr19.37zv_3 wrex wi fr19.37zv_0 fr19.37zv_1 wi fr19.37zv_2 fr19.37zv_3 wrex fr19.37zv_3 c0 wne fr19.37zv_0 fr19.37zv_0 fr19.37zv_2 fr19.37zv_3 wral fr19.37zv_1 fr19.37zv_2 fr19.37zv_3 wrex fr19.37zv_0 fr19.37zv_2 fr19.37zv_3 r19.3rzv imbi1d fr19.37zv_0 fr19.37zv_1 fr19.37zv_2 fr19.37zv_3 r19.35 syl6rbbr $.
$}
$( /* Restricted version of Theorem 19.45 of [Margaris] p. 90.  (Contributed
       by NM, 27-May-1998.) */

$)
${
	$d x A $.
	$d x ph $.
	fr19.45zv_0 $f wff ph $.
	fr19.45zv_1 $f wff ps $.
	fr19.45zv_2 $f set x $.
	fr19.45zv_3 $f class A $.
	r19.45zv $p |- ( A =/= (/) -> ( E. x e. A ( ph \/ ps ) <-> ( ph \/ E. x e. A ps ) ) ) $= fr19.45zv_3 c0 wne fr19.45zv_0 fr19.45zv_1 fr19.45zv_2 fr19.45zv_3 wrex wo fr19.45zv_0 fr19.45zv_2 fr19.45zv_3 wrex fr19.45zv_1 fr19.45zv_2 fr19.45zv_3 wrex wo fr19.45zv_0 fr19.45zv_1 wo fr19.45zv_2 fr19.45zv_3 wrex fr19.45zv_3 c0 wne fr19.45zv_0 fr19.45zv_0 fr19.45zv_2 fr19.45zv_3 wrex fr19.45zv_1 fr19.45zv_2 fr19.45zv_3 wrex fr19.45zv_0 fr19.45zv_2 fr19.45zv_3 r19.9rzv orbi1d fr19.45zv_0 fr19.45zv_1 fr19.45zv_2 fr19.45zv_3 r19.43 syl6rbbr $.
$}
$( /* Restricted quantifier version of Theorem 19.27 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 26-Oct-2010.) */

$)
${
	$d x A $.
	fr19.27z_0 $f wff ph $.
	fr19.27z_1 $f wff ps $.
	fr19.27z_2 $f set x $.
	fr19.27z_3 $f class A $.
	er19.27z_0 $e |- F/ x ps $.
	r19.27z $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) ) $= fr19.27z_3 c0 wne fr19.27z_0 fr19.27z_2 fr19.27z_3 wral fr19.27z_1 wa fr19.27z_0 fr19.27z_2 fr19.27z_3 wral fr19.27z_1 fr19.27z_2 fr19.27z_3 wral wa fr19.27z_0 fr19.27z_1 wa fr19.27z_2 fr19.27z_3 wral fr19.27z_3 c0 wne fr19.27z_1 fr19.27z_1 fr19.27z_2 fr19.27z_3 wral fr19.27z_0 fr19.27z_2 fr19.27z_3 wral fr19.27z_1 fr19.27z_2 fr19.27z_3 er19.27z_0 r19.3rz anbi2d fr19.27z_0 fr19.27z_1 fr19.27z_2 fr19.27z_3 r19.26 syl6rbbr $.
$}
$( /* Restricted quantifier version of Theorem 19.27 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 19-Aug-2004.) */

$)
${
	$d x A $.
	$d x ps $.
	fr19.27zv_0 $f wff ph $.
	fr19.27zv_1 $f wff ps $.
	fr19.27zv_2 $f set x $.
	fr19.27zv_3 $f class A $.
	r19.27zv $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) ) $= fr19.27zv_3 c0 wne fr19.27zv_0 fr19.27zv_2 fr19.27zv_3 wral fr19.27zv_1 wa fr19.27zv_0 fr19.27zv_2 fr19.27zv_3 wral fr19.27zv_1 fr19.27zv_2 fr19.27zv_3 wral wa fr19.27zv_0 fr19.27zv_1 wa fr19.27zv_2 fr19.27zv_3 wral fr19.27zv_3 c0 wne fr19.27zv_1 fr19.27zv_1 fr19.27zv_2 fr19.27zv_3 wral fr19.27zv_0 fr19.27zv_2 fr19.27zv_3 wral fr19.27zv_1 fr19.27zv_2 fr19.27zv_3 r19.3rzv anbi2d fr19.27zv_0 fr19.27zv_1 fr19.27zv_2 fr19.27zv_3 r19.26 syl6rbbr $.
$}
$( /* Restricted quantifier version of Theorem 19.36 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 20-Sep-2003.) */

$)
${
	$d x A $.
	$d x ps $.
	fr19.36zv_0 $f wff ph $.
	fr19.36zv_1 $f wff ps $.
	fr19.36zv_2 $f set x $.
	fr19.36zv_3 $f class A $.
	r19.36zv $p |- ( A =/= (/) -> ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> ps ) ) ) $= fr19.36zv_3 c0 wne fr19.36zv_0 fr19.36zv_2 fr19.36zv_3 wral fr19.36zv_1 wi fr19.36zv_0 fr19.36zv_2 fr19.36zv_3 wral fr19.36zv_1 fr19.36zv_2 fr19.36zv_3 wrex wi fr19.36zv_0 fr19.36zv_1 wi fr19.36zv_2 fr19.36zv_3 wrex fr19.36zv_3 c0 wne fr19.36zv_1 fr19.36zv_1 fr19.36zv_2 fr19.36zv_3 wrex fr19.36zv_0 fr19.36zv_2 fr19.36zv_3 wral fr19.36zv_1 fr19.36zv_2 fr19.36zv_3 r19.9rzv imbi2d fr19.36zv_0 fr19.36zv_1 fr19.36zv_2 fr19.36zv_3 r19.35 syl6rbbr $.
$}
$( /* Vacuous quantification is always true.  (Contributed by NM,
       11-Mar-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	$d x A $.
	frzal_0 $f wff ph $.
	frzal_1 $f set x $.
	frzal_2 $f class A $.
	rzal $p |- ( A = (/) -> A. x e. A ph ) $= frzal_2 c0 wceq frzal_0 frzal_1 frzal_2 frzal_2 c0 wceq frzal_1 sup_set_class frzal_2 wcel frzal_0 frzal_1 sup_set_class frzal_2 wcel frzal_2 c0 frzal_2 frzal_1 sup_set_class ne0i necon2bi pm2.21d ralrimiv $.
$}
$( /* Restricted existential quantification implies its restriction is
       nonempty.  (Contributed by Szymon Jaroszewicz, 3-Apr-2007.) */

$)
${
	$d x A $.
	frexn0_0 $f wff ph $.
	frexn0_1 $f set x $.
	frexn0_2 $f class A $.
	rexn0 $p |- ( E. x e. A ph -> A =/= (/) ) $= frexn0_0 frexn0_2 c0 wne frexn0_1 frexn0_2 frexn0_1 sup_set_class frexn0_2 wcel frexn0_2 c0 wne frexn0_0 frexn0_2 frexn0_1 sup_set_class ne0i a1d rexlimiv $.
$}
$( /* Idempotent law for restricted quantifier.  (Contributed by NM,
       28-Mar-1997.) */

$)
${
	$d x A $.
	fralidm_0 $f wff ph $.
	fralidm_1 $f set x $.
	fralidm_2 $f class A $.
	ralidm $p |- ( A. x e. A A. x e. A ph <-> A. x e. A ph ) $= fralidm_2 c0 wceq fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 wral fralidm_0 fralidm_1 fralidm_2 wral wb fralidm_2 c0 wceq fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 wral fralidm_0 fralidm_1 fralidm_2 wral fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 rzal fralidm_0 fralidm_1 fralidm_2 rzal 2thd fralidm_2 c0 wceq wn fralidm_1 sup_set_class fralidm_2 wcel fralidm_1 wex fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 wral fralidm_0 fralidm_1 fralidm_2 wral wb fralidm_1 fralidm_2 neq0 fralidm_1 sup_set_class fralidm_2 wcel fralidm_1 wex fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 sup_set_class fralidm_2 wcel fralidm_1 wex fralidm_0 fralidm_1 fralidm_2 wral wi fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 wral fralidm_1 sup_set_class fralidm_2 wcel fralidm_1 wex fralidm_0 fralidm_1 fralidm_2 wral biimt fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 wral fralidm_1 sup_set_class fralidm_2 wcel fralidm_0 fralidm_1 fralidm_2 wral wi fralidm_1 wal fralidm_1 sup_set_class fralidm_2 wcel fralidm_1 wex fralidm_0 fralidm_1 fralidm_2 wral wi fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_2 df-ral fralidm_1 sup_set_class fralidm_2 wcel fralidm_0 fralidm_1 fralidm_2 wral fralidm_1 fralidm_0 fralidm_1 fralidm_2 nfra1 19.23 bitri syl6rbbr sylbi pm2.61i $.
$}
$( /* Vacuous universal quantification is always true.  (Contributed by NM,
     20-Oct-2005.) */

$)
${
	fral0_0 $f wff ph $.
	fral0_1 $f set x $.
	ral0 $p |- A. x e. (/) ph $= fral0_0 fral0_1 c0 fral0_1 sup_set_class c0 wcel fral0_0 fral0_1 sup_set_class noel pm2.21i rgen $.
$}
$( /* Generalization rule that eliminates a non-zero class requirement.
       (Contributed by NM, 8-Dec-2012.) */

$)
${
	$d x A $.
	frgenz_0 $f wff ph $.
	frgenz_1 $f set x $.
	frgenz_2 $f class A $.
	ergenz_0 $e |- ( ( A =/= (/) /\ x e. A ) -> ph ) $.
	rgenz $p |- A. x e. A ph $= frgenz_0 frgenz_1 frgenz_2 wral frgenz_2 c0 frgenz_0 frgenz_1 frgenz_2 rzal frgenz_2 c0 wne frgenz_0 frgenz_1 frgenz_2 ergenz_0 ralrimiva pm2.61ine $.
$}
$( /* The quantification of a falsehood is vacuous when true.  (Contributed by
       NM, 26-Nov-2005.) */

$)
${
	$d x A $.
	fralf0_0 $f wff ph $.
	fralf0_1 $f set x $.
	fralf0_2 $f class A $.
	eralf0_0 $e |- -. ph $.
	ralf0 $p |- ( A. x e. A ph <-> A = (/) ) $= fralf0_0 fralf0_1 fralf0_2 wral fralf0_2 c0 wceq fralf0_1 sup_set_class fralf0_2 wcel fralf0_0 wi fralf0_1 wal fralf0_1 sup_set_class fralf0_2 wcel wn fralf0_1 wal fralf0_0 fralf0_1 fralf0_2 wral fralf0_2 c0 wceq fralf0_1 sup_set_class fralf0_2 wcel fralf0_0 wi fralf0_1 sup_set_class fralf0_2 wcel wn fralf0_1 fralf0_1 sup_set_class fralf0_2 wcel fralf0_0 wi fralf0_0 wn fralf0_1 sup_set_class fralf0_2 wcel wn eralf0_0 fralf0_1 sup_set_class fralf0_2 wcel fralf0_0 con3 mpi alimi fralf0_0 fralf0_1 fralf0_2 df-ral fralf0_1 fralf0_2 eq0 3imtr4i fralf0_0 fralf0_1 fralf0_2 rzal impbii $.
$}
$( /* TODO - shorten r19.3zv, r19.27zv, r19.28zv, raaanv w/ non-v */

$)
$( /* Rearrange restricted quantifiers.  (Contributed by NM, 26-Oct-2010.) */

$)
${
	$d x y A $.
	fraaan_0 $f wff ph $.
	fraaan_1 $f wff ps $.
	fraaan_2 $f set x $.
	fraaan_3 $f set y $.
	fraaan_4 $f class A $.
	eraaan_0 $e |- F/ y ph $.
	eraaan_1 $e |- F/ x ps $.
	raaan $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. A ps ) ) $= fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 wral fraaan_0 fraaan_2 fraaan_4 wral fraaan_1 fraaan_3 fraaan_4 wral wa wb fraaan_4 c0 fraaan_4 c0 wceq fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 wral fraaan_0 fraaan_2 fraaan_4 wral fraaan_1 fraaan_3 fraaan_4 wral fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 wral fraaan_0 fraaan_2 fraaan_4 wral fraaan_1 fraaan_3 fraaan_4 wral wa wb fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 rzal fraaan_0 fraaan_2 fraaan_4 rzal fraaan_1 fraaan_3 fraaan_4 rzal fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 wral fraaan_0 fraaan_2 fraaan_4 wral fraaan_1 fraaan_3 fraaan_4 wral wa pm5.1 syl12anc fraaan_4 c0 wne fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 wral fraaan_0 fraaan_1 fraaan_3 fraaan_4 wral wa fraaan_2 fraaan_4 wral fraaan_0 fraaan_2 fraaan_4 wral fraaan_1 fraaan_3 fraaan_4 wral wa fraaan_4 c0 wne fraaan_0 fraaan_1 wa fraaan_3 fraaan_4 wral fraaan_0 fraaan_1 fraaan_3 fraaan_4 wral wa fraaan_2 fraaan_4 fraaan_0 fraaan_1 fraaan_3 fraaan_4 eraaan_0 r19.28z ralbidv fraaan_0 fraaan_1 fraaan_3 fraaan_4 wral fraaan_2 fraaan_4 fraaan_1 fraaan_2 fraaan_3 fraaan_4 fraaan_2 fraaan_4 nfcv eraaan_1 nfral r19.27z bitrd pm2.61ine $.
$}
$( /* Rearrange restricted quantifiers.  (Contributed by NM, 11-Mar-1997.) */

$)
${
	$d y ph $.
	$d x ps $.
	$d x y A $.
	fraaanv_0 $f wff ph $.
	fraaanv_1 $f wff ps $.
	fraaanv_2 $f set x $.
	fraaanv_3 $f set y $.
	fraaanv_4 $f class A $.
	raaanv $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. A ps ) ) $= fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 wral fraaanv_0 fraaanv_2 fraaanv_4 wral fraaanv_1 fraaanv_3 fraaanv_4 wral wa wb fraaanv_4 c0 fraaanv_4 c0 wceq fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 wral fraaanv_0 fraaanv_2 fraaanv_4 wral fraaanv_1 fraaanv_3 fraaanv_4 wral fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 wral fraaanv_0 fraaanv_2 fraaanv_4 wral fraaanv_1 fraaanv_3 fraaanv_4 wral wa wb fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 rzal fraaanv_0 fraaanv_2 fraaanv_4 rzal fraaanv_1 fraaanv_3 fraaanv_4 rzal fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 wral fraaanv_0 fraaanv_2 fraaanv_4 wral fraaanv_1 fraaanv_3 fraaanv_4 wral wa pm5.1 syl12anc fraaanv_4 c0 wne fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 wral fraaanv_0 fraaanv_1 fraaanv_3 fraaanv_4 wral wa fraaanv_2 fraaanv_4 wral fraaanv_0 fraaanv_2 fraaanv_4 wral fraaanv_1 fraaanv_3 fraaanv_4 wral wa fraaanv_4 c0 wne fraaanv_0 fraaanv_1 wa fraaanv_3 fraaanv_4 wral fraaanv_0 fraaanv_1 fraaanv_3 fraaanv_4 wral wa fraaanv_2 fraaanv_4 fraaanv_0 fraaanv_1 fraaanv_3 fraaanv_4 r19.28zv ralbidv fraaanv_0 fraaanv_1 fraaanv_3 fraaanv_4 wral fraaanv_2 fraaanv_4 r19.27zv bitrd pm2.61ine $.
$}
$( /* Set substitution into the first argument of a subset relation.
       (Contributed by Rodolfo Medina, 7-Jul-2010.)  (Proof shortened by Mario
       Carneiro, 14-Nov-2016.) */

$)
${
	$d z y $.
	$d z x A $.
	isbss_0 $f set z $.
	fsbss_0 $f set x $.
	fsbss_1 $f set y $.
	fsbss_2 $f class A $.
	sbss $p |- ( [ y / x ] x C_ A <-> y C_ A ) $= fsbss_0 sup_set_class fsbss_2 wss fsbss_0 isbss_0 wsb isbss_0 sup_set_class fsbss_2 wss fsbss_0 sup_set_class fsbss_2 wss fsbss_0 fsbss_1 wsb fsbss_1 sup_set_class fsbss_2 wss isbss_0 fsbss_1 sup_set_class fsbss_1 vex fsbss_0 sup_set_class fsbss_2 wss isbss_0 fsbss_1 fsbss_0 sbequ isbss_0 sup_set_class fsbss_1 sup_set_class fsbss_2 sseq1 fsbss_0 sup_set_class fsbss_2 wss isbss_0 sup_set_class fsbss_2 wss fsbss_0 isbss_0 isbss_0 sup_set_class fsbss_2 wss fsbss_0 nfv fsbss_0 sup_set_class isbss_0 sup_set_class fsbss_2 sseq1 sbie vtoclb $.
$}
$( /* Distribute proper substitution through a subclass relation.
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Alexander
       van der Vekens, 23-Jul-2017.) */

$)
${
	$d A y $.
	$d B y $.
	$d C y $.
	$d D y $.
	$d x y $.
	isbcss_0 $f set y $.
	fsbcss_0 $f set x $.
	fsbcss_1 $f class A $.
	fsbcss_2 $f class B $.
	fsbcss_3 $f class C $.
	fsbcss_4 $f class D $.
	sbcss $p |- ( A e. B -> ( [. A / x ]. C C_ D <-> [_ A / x ]_ C C_ [_ A / x ]_ D ) ) $= fsbcss_1 fsbcss_2 wcel isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi isbcss_0 wal fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_3 csb wcel isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_4 csb wcel wi isbcss_0 wal fsbcss_3 fsbcss_4 wss fsbcss_0 fsbcss_1 wsbc fsbcss_0 fsbcss_1 fsbcss_3 csb fsbcss_0 fsbcss_1 fsbcss_4 csb wss fsbcss_1 fsbcss_2 wcel isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi isbcss_0 wal fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi fsbcss_0 fsbcss_1 wsbc isbcss_0 wal isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_3 csb wcel isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_4 csb wcel wi isbcss_0 wal isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi isbcss_0 fsbcss_0 fsbcss_1 fsbcss_2 sbcalg fsbcss_1 fsbcss_2 wcel isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_3 csb wcel isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_4 csb wcel wi isbcss_0 fsbcss_1 fsbcss_2 wcel isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_3 wcel fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_4 wcel fsbcss_0 fsbcss_1 wsbc wi isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_3 csb wcel isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_4 csb wcel wi isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel fsbcss_0 fsbcss_1 fsbcss_2 sbcimg fsbcss_1 fsbcss_2 wcel isbcss_0 sup_set_class fsbcss_3 wcel fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_3 csb wcel isbcss_0 sup_set_class fsbcss_4 wcel fsbcss_0 fsbcss_1 wsbc isbcss_0 sup_set_class fsbcss_0 fsbcss_1 fsbcss_4 csb wcel fsbcss_0 fsbcss_1 isbcss_0 sup_set_class fsbcss_3 fsbcss_2 sbcel2g fsbcss_0 fsbcss_1 isbcss_0 sup_set_class fsbcss_4 fsbcss_2 sbcel2g imbi12d bitrd albidv bitrd fsbcss_3 fsbcss_4 wss isbcss_0 sup_set_class fsbcss_3 wcel isbcss_0 sup_set_class fsbcss_4 wcel wi isbcss_0 wal fsbcss_0 fsbcss_1 isbcss_0 fsbcss_3 fsbcss_4 dfss2 sbcbii isbcss_0 fsbcss_0 fsbcss_1 fsbcss_3 csb fsbcss_0 fsbcss_1 fsbcss_4 csb dfss2 3bitr4g $.
$}

