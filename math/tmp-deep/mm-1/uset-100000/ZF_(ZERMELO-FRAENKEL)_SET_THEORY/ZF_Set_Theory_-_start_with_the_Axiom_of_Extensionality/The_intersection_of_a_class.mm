$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_union_of_a_class.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The intersection of a class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Declare class intersection symbol. */

$)
$c |^|  $.
$( /* Big cap */

$)
$( /* Extend class notation to include the intersection of a class (read:
     'intersect ` A ` '). */

$)
${
	fcint_0 $f class A $.
	cint $a class |^| A $.
$}
$( /* Define the intersection of a class.  Definition 7.35 of [TakeutiZaring]
       p. 44.  For example, ` |^| { { 1 , 3 } , { 1 , 8 } } = { 1 } ` .
       Compare this with the intersection of two classes, ~ df-in .
       (Contributed by NM, 18-Aug-1993.) */

$)
${
	$d x y A $.
	fdf-int_0 $f set x $.
	fdf-int_1 $f set y $.
	fdf-int_2 $f class A $.
	df-int $a |- |^| A = { x | A. y ( y e. A -> x e. y ) } $.
$}
$( /* Alternate definition of class intersection.  (Contributed by NM,
       28-Jun-1998.) */

$)
${
	$d x y A $.
	fdfint2_0 $f set x $.
	fdfint2_1 $f set y $.
	fdfint2_2 $f class A $.
	dfint2 $p |- |^| A = { x | A. y e. A x e. y } $= fdfint2_2 cint fdfint2_1 sup_set_class fdfint2_2 wcel fdfint2_0 sup_set_class fdfint2_1 sup_set_class wcel wi fdfint2_1 wal fdfint2_0 cab fdfint2_0 sup_set_class fdfint2_1 sup_set_class wcel fdfint2_1 fdfint2_2 wral fdfint2_0 cab fdfint2_0 fdfint2_1 fdfint2_2 df-int fdfint2_0 sup_set_class fdfint2_1 sup_set_class wcel fdfint2_1 fdfint2_2 wral fdfint2_1 sup_set_class fdfint2_2 wcel fdfint2_0 sup_set_class fdfint2_1 sup_set_class wcel wi fdfint2_1 wal fdfint2_0 fdfint2_0 sup_set_class fdfint2_1 sup_set_class wcel fdfint2_1 fdfint2_2 df-ral abbii eqtr4i $.
$}
$( /* Equality law for intersection.  (Contributed by NM, 13-Sep-1999.) */

$)
${
	$d x y A $.
	$d x y B $.
	iinteq_0 $f set x $.
	iinteq_1 $f set y $.
	finteq_0 $f class A $.
	finteq_1 $f class B $.
	inteq $p |- ( A = B -> |^| A = |^| B ) $= finteq_0 finteq_1 wceq iinteq_0 sup_set_class iinteq_1 sup_set_class wcel iinteq_1 finteq_0 wral iinteq_0 cab iinteq_0 sup_set_class iinteq_1 sup_set_class wcel iinteq_1 finteq_1 wral iinteq_0 cab finteq_0 cint finteq_1 cint finteq_0 finteq_1 wceq iinteq_0 sup_set_class iinteq_1 sup_set_class wcel iinteq_1 finteq_0 wral iinteq_0 sup_set_class iinteq_1 sup_set_class wcel iinteq_1 finteq_1 wral iinteq_0 iinteq_0 sup_set_class iinteq_1 sup_set_class wcel iinteq_1 finteq_0 finteq_1 raleq abbidv iinteq_0 iinteq_1 finteq_0 dfint2 iinteq_0 iinteq_1 finteq_1 dfint2 3eqtr4g $.
$}
$( /* Equality inference for class intersection.  (Contributed by NM,
       2-Sep-2003.) */

$)
${
	finteqi_0 $f class A $.
	finteqi_1 $f class B $.
	einteqi_0 $e |- A = B $.
	inteqi $p |- |^| A = |^| B $= finteqi_0 finteqi_1 wceq finteqi_0 cint finteqi_1 cint wceq einteqi_0 finteqi_0 finteqi_1 inteq ax-mp $.
$}
$( /* Equality deduction for class intersection.  (Contributed by NM,
       2-Sep-2003.) */

$)
${
	finteqd_0 $f wff ph $.
	finteqd_1 $f class A $.
	finteqd_2 $f class B $.
	einteqd_0 $e |- ( ph -> A = B ) $.
	inteqd $p |- ( ph -> |^| A = |^| B ) $= finteqd_0 finteqd_1 finteqd_2 wceq finteqd_1 cint finteqd_2 cint wceq einteqd_0 finteqd_1 finteqd_2 inteq syl $.
$}
$( /* Membership in class intersection.  (Contributed by NM, 21-May-1994.) */

$)
${
	$d x A y $.
	$d x B y $.
	ielint_0 $f set y $.
	felint_0 $f set x $.
	felint_1 $f class A $.
	felint_2 $f class B $.
	eelint_0 $e |- A e. _V $.
	elint $p |- ( A e. |^| B <-> A. x ( x e. B -> A e. x ) ) $= felint_0 sup_set_class felint_2 wcel ielint_0 sup_set_class felint_0 sup_set_class wcel wi felint_0 wal felint_0 sup_set_class felint_2 wcel felint_1 felint_0 sup_set_class wcel wi felint_0 wal ielint_0 felint_1 felint_2 cint eelint_0 ielint_0 sup_set_class felint_1 wceq felint_0 sup_set_class felint_2 wcel ielint_0 sup_set_class felint_0 sup_set_class wcel wi felint_0 sup_set_class felint_2 wcel felint_1 felint_0 sup_set_class wcel wi felint_0 ielint_0 sup_set_class felint_1 wceq ielint_0 sup_set_class felint_0 sup_set_class wcel felint_1 felint_0 sup_set_class wcel felint_0 sup_set_class felint_2 wcel ielint_0 sup_set_class felint_1 felint_0 sup_set_class eleq1 imbi2d albidv ielint_0 felint_0 felint_2 df-int elab2 $.
$}
$( /* Membership in class intersection.  (Contributed by NM, 14-Oct-1999.) */

$)
${
	$d x A $.
	$d x B $.
	felint2_0 $f set x $.
	felint2_1 $f class A $.
	felint2_2 $f class B $.
	eelint2_0 $e |- A e. _V $.
	elint2 $p |- ( A e. |^| B <-> A. x e. B A e. x ) $= felint2_1 felint2_2 cint wcel felint2_0 sup_set_class felint2_2 wcel felint2_1 felint2_0 sup_set_class wcel wi felint2_0 wal felint2_1 felint2_0 sup_set_class wcel felint2_0 felint2_2 wral felint2_0 felint2_1 felint2_2 eelint2_0 elint felint2_1 felint2_0 sup_set_class wcel felint2_0 felint2_2 df-ral bitr4i $.
$}
$( /* Membership in class intersection, with the sethood requirement expressed
       as an antecedent.  (Contributed by NM, 20-Nov-2003.) */

$)
${
	$d x y A $.
	$d x y B $.
	ielintg_0 $f set y $.
	felintg_0 $f set x $.
	felintg_1 $f class A $.
	felintg_2 $f class B $.
	felintg_3 $f class V $.
	elintg $p |- ( A e. V -> ( A e. |^| B <-> A. x e. B A e. x ) ) $= ielintg_0 sup_set_class felintg_2 cint wcel ielintg_0 sup_set_class felintg_0 sup_set_class wcel felintg_0 felintg_2 wral felintg_1 felintg_2 cint wcel felintg_1 felintg_0 sup_set_class wcel felintg_0 felintg_2 wral ielintg_0 felintg_1 felintg_3 ielintg_0 sup_set_class felintg_1 felintg_2 cint eleq1 ielintg_0 sup_set_class felintg_1 wceq ielintg_0 sup_set_class felintg_0 sup_set_class wcel felintg_1 felintg_0 sup_set_class wcel felintg_0 felintg_2 ielintg_0 sup_set_class felintg_1 felintg_0 sup_set_class eleq1 ralbidv felintg_0 ielintg_0 sup_set_class felintg_2 ielintg_0 vex elint2 vtoclbg $.
$}
$( /* Membership in class intersection.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 9-Jul-2011.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ielinti_0 $f set x $.
	felinti_0 $f class A $.
	felinti_1 $f class B $.
	felinti_2 $f class C $.
	elinti $p |- ( A e. |^| B -> ( C e. B -> A e. C ) ) $= felinti_0 felinti_1 cint wcel felinti_2 felinti_1 wcel felinti_0 felinti_2 wcel wi felinti_0 felinti_1 cint wcel felinti_0 felinti_1 cint wcel felinti_0 ielinti_0 sup_set_class wcel ielinti_0 felinti_1 wral felinti_2 felinti_1 wcel felinti_0 felinti_2 wcel wi ielinti_0 felinti_0 felinti_1 felinti_1 cint elintg felinti_0 ielinti_0 sup_set_class wcel felinti_0 felinti_2 wcel ielinti_0 felinti_2 felinti_1 ielinti_0 sup_set_class felinti_2 felinti_0 eleq2 rspccv syl6bi pm2.43i $.
$}
$( /* Bound-variable hypothesis builder for intersection.  (Contributed by NM,
       2-Feb-1997.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.) */

$)
${
	$d y z A $.
	$d x y z $.
	infint_0 $f set y $.
	infint_1 $f set z $.
	fnfint_0 $f set x $.
	fnfint_1 $f class A $.
	enfint_0 $e |- F/_ x A $.
	nfint $p |- F/_ x |^| A $= fnfint_0 fnfint_1 cint infint_0 sup_set_class infint_1 sup_set_class wcel infint_1 fnfint_1 wral infint_0 cab infint_0 infint_1 fnfint_1 dfint2 infint_0 sup_set_class infint_1 sup_set_class wcel infint_1 fnfint_1 wral fnfint_0 infint_0 infint_0 sup_set_class infint_1 sup_set_class wcel fnfint_0 infint_1 fnfint_1 enfint_0 infint_0 sup_set_class infint_1 sup_set_class wcel fnfint_0 nfv nfral nfab nfcxfr $.
$}
$( /* Membership in the intersection of a class abstraction.  (Contributed by
       NM, 30-Aug-1993.) */

$)
${
	$d A x y $.
	$d ph y $.
	ielintab_0 $f set y $.
	felintab_0 $f wff ph $.
	felintab_1 $f set x $.
	felintab_2 $f class A $.
	eelintab_0 $e |- A e. _V $.
	elintab $p |- ( A e. |^| { x | ph } <-> A. x ( ph -> A e. x ) ) $= felintab_2 felintab_0 felintab_1 cab cint wcel ielintab_0 sup_set_class felintab_0 felintab_1 cab wcel felintab_2 ielintab_0 sup_set_class wcel wi ielintab_0 wal felintab_0 felintab_2 felintab_1 sup_set_class wcel wi felintab_1 wal ielintab_0 felintab_2 felintab_0 felintab_1 cab eelintab_0 elint ielintab_0 sup_set_class felintab_0 felintab_1 cab wcel felintab_2 ielintab_0 sup_set_class wcel wi felintab_0 felintab_2 felintab_1 sup_set_class wcel wi ielintab_0 felintab_1 ielintab_0 sup_set_class felintab_0 felintab_1 cab wcel felintab_2 ielintab_0 sup_set_class wcel felintab_1 felintab_0 felintab_1 ielintab_0 nfsab1 felintab_2 ielintab_0 sup_set_class wcel felintab_1 nfv nfim felintab_0 felintab_2 felintab_1 sup_set_class wcel wi ielintab_0 nfv ielintab_0 sup_set_class felintab_1 sup_set_class wceq ielintab_0 sup_set_class felintab_0 felintab_1 cab wcel felintab_0 felintab_2 ielintab_0 sup_set_class wcel felintab_2 felintab_1 sup_set_class wcel ielintab_0 sup_set_class felintab_1 sup_set_class wceq ielintab_0 sup_set_class felintab_0 felintab_1 cab wcel felintab_1 sup_set_class felintab_0 felintab_1 cab wcel felintab_0 ielintab_0 sup_set_class felintab_1 sup_set_class felintab_0 felintab_1 cab eleq1 felintab_0 felintab_1 abid syl6bb ielintab_0 sup_set_class felintab_1 sup_set_class felintab_2 eleq2 imbi12d cbval bitri $.
$}
$( /* Membership in the intersection of a class abstraction.  (Contributed by
       NM, 17-Oct-1999.) */

$)
${
	$d A x $.
	felintrab_0 $f wff ph $.
	felintrab_1 $f set x $.
	felintrab_2 $f class A $.
	felintrab_3 $f class B $.
	eelintrab_0 $e |- A e. _V $.
	elintrab $p |- ( A e. |^| { x e. B | ph } <-> A. x e. B ( ph -> A e. x ) ) $= felintrab_2 felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_1 cab cint wcel felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 felintrab_2 felintrab_1 sup_set_class wcel wi wi felintrab_1 wal felintrab_2 felintrab_0 felintrab_1 felintrab_3 crab cint wcel felintrab_0 felintrab_2 felintrab_1 sup_set_class wcel wi felintrab_1 felintrab_3 wral felintrab_2 felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_1 cab cint wcel felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_2 felintrab_1 sup_set_class wcel wi felintrab_1 wal felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 felintrab_2 felintrab_1 sup_set_class wcel wi wi felintrab_1 wal felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_1 felintrab_2 eelintrab_0 elintab felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_2 felintrab_1 sup_set_class wcel wi felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 felintrab_2 felintrab_1 sup_set_class wcel wi wi felintrab_1 felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 felintrab_2 felintrab_1 sup_set_class wcel impexp albii bitri felintrab_0 felintrab_1 felintrab_3 crab cint felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_1 cab cint felintrab_2 felintrab_0 felintrab_1 felintrab_3 crab felintrab_1 sup_set_class felintrab_3 wcel felintrab_0 wa felintrab_1 cab felintrab_0 felintrab_1 felintrab_3 df-rab inteqi eleq2i felintrab_0 felintrab_2 felintrab_1 sup_set_class wcel wi felintrab_1 felintrab_3 df-ral 3bitr4i $.
$}
$( /* Membership in the intersection of a class abstraction.  (Contributed by
       NM, 17-Feb-2007.) */

$)
${
	$d x y A $.
	$d y B $.
	$d y ph $.
	ielintrabg_0 $f set y $.
	felintrabg_0 $f wff ph $.
	felintrabg_1 $f set x $.
	felintrabg_2 $f class A $.
	felintrabg_3 $f class B $.
	felintrabg_4 $f class V $.
	elintrabg $p |- ( A e. V -> ( A e. |^| { x e. B | ph } <-> A. x e. B ( ph -> A e. x ) ) ) $= ielintrabg_0 sup_set_class felintrabg_0 felintrabg_1 felintrabg_3 crab cint wcel felintrabg_0 ielintrabg_0 sup_set_class felintrabg_1 sup_set_class wcel wi felintrabg_1 felintrabg_3 wral felintrabg_2 felintrabg_0 felintrabg_1 felintrabg_3 crab cint wcel felintrabg_0 felintrabg_2 felintrabg_1 sup_set_class wcel wi felintrabg_1 felintrabg_3 wral ielintrabg_0 felintrabg_2 felintrabg_4 ielintrabg_0 sup_set_class felintrabg_2 felintrabg_0 felintrabg_1 felintrabg_3 crab cint eleq1 ielintrabg_0 sup_set_class felintrabg_2 wceq felintrabg_0 ielintrabg_0 sup_set_class felintrabg_1 sup_set_class wcel wi felintrabg_0 felintrabg_2 felintrabg_1 sup_set_class wcel wi felintrabg_1 felintrabg_3 ielintrabg_0 sup_set_class felintrabg_2 wceq ielintrabg_0 sup_set_class felintrabg_1 sup_set_class wcel felintrabg_2 felintrabg_1 sup_set_class wcel felintrabg_0 ielintrabg_0 sup_set_class felintrabg_2 felintrabg_1 sup_set_class eleq1 imbi2d ralbidv felintrabg_0 felintrabg_1 ielintrabg_0 sup_set_class felintrabg_3 ielintrabg_0 vex elintrab vtoclbg $.
$}
$( /* The intersection of the empty set is the universal class.  Exercise 2 of
       [TakeutiZaring] p. 44.  (Contributed by NM, 18-Aug-1993.) */

$)
${
	$d x y $.
	iint0_0 $f set x $.
	iint0_1 $f set y $.
	int0 $p |- |^| (/) = _V $= iint0_1 sup_set_class c0 wcel iint0_0 sup_set_class iint0_1 sup_set_class wcel wi iint0_1 wal iint0_0 cab iint0_0 sup_set_class iint0_0 sup_set_class wceq iint0_0 cab c0 cint cvv iint0_1 sup_set_class c0 wcel iint0_0 sup_set_class iint0_1 sup_set_class wcel wi iint0_1 wal iint0_0 sup_set_class iint0_0 sup_set_class wceq iint0_0 iint0_1 sup_set_class c0 wcel iint0_0 sup_set_class iint0_1 sup_set_class wcel wi iint0_1 wal iint0_0 sup_set_class iint0_0 sup_set_class wceq iint0_1 sup_set_class c0 wcel iint0_0 sup_set_class iint0_1 sup_set_class wcel wi iint0_1 iint0_1 sup_set_class c0 wcel iint0_0 sup_set_class iint0_1 sup_set_class wcel iint0_1 sup_set_class noel pm2.21i ax-gen iint0_0 sup_set_class eqid 2th abbii iint0_0 iint0_1 c0 df-int iint0_0 df-v 3eqtr4i $.
$}
$( /* An element of a class includes the intersection of the class.  Exercise
       4 of [TakeutiZaring] p. 44 (with correction), generalized to classes.
       (Contributed by NM, 18-Nov-1995.) */

$)
${
	$d x y A $.
	$d x y B $.
	iintss1_0 $f set x $.
	iintss1_1 $f set y $.
	fintss1_0 $f class A $.
	fintss1_1 $f class B $.
	intss1 $p |- ( A e. B -> |^| B C_ A ) $= fintss1_0 fintss1_1 wcel iintss1_0 fintss1_1 cint fintss1_0 iintss1_0 sup_set_class fintss1_1 cint wcel iintss1_1 sup_set_class fintss1_1 wcel iintss1_0 sup_set_class iintss1_1 sup_set_class wcel wi iintss1_1 wal fintss1_0 fintss1_1 wcel iintss1_0 sup_set_class fintss1_0 wcel iintss1_1 iintss1_0 sup_set_class fintss1_1 iintss1_0 vex elint iintss1_1 sup_set_class fintss1_1 wcel iintss1_0 sup_set_class iintss1_1 sup_set_class wcel wi iintss1_1 wal fintss1_0 fintss1_1 wcel iintss1_0 sup_set_class fintss1_0 wcel iintss1_1 sup_set_class fintss1_1 wcel iintss1_0 sup_set_class iintss1_1 sup_set_class wcel wi fintss1_0 fintss1_1 wcel iintss1_0 sup_set_class fintss1_0 wcel wi iintss1_1 fintss1_0 fintss1_1 iintss1_1 sup_set_class fintss1_0 wceq iintss1_1 sup_set_class fintss1_1 wcel fintss1_0 fintss1_1 wcel iintss1_0 sup_set_class iintss1_1 sup_set_class wcel iintss1_0 sup_set_class fintss1_0 wcel iintss1_1 sup_set_class fintss1_0 fintss1_1 eleq1 iintss1_1 sup_set_class fintss1_0 iintss1_0 sup_set_class eleq2 imbi12d spcgv pm2.43a syl5bi ssrdv $.
$}
$( /* Subclass of a class intersection.  Theorem 5.11(viii) of [Monk1] p. 52
       and its converse.  (Contributed by NM, 14-Oct-1999.) */

$)
${
	$d x y A $.
	$d x y B $.
	issint_0 $f set y $.
	fssint_0 $f set x $.
	fssint_1 $f class A $.
	fssint_2 $f class B $.
	ssint $p |- ( A C_ |^| B <-> A. x e. B A C_ x ) $= fssint_1 fssint_2 cint wss issint_0 sup_set_class fssint_2 cint wcel issint_0 fssint_1 wral issint_0 sup_set_class fssint_0 sup_set_class wcel fssint_0 fssint_2 wral issint_0 fssint_1 wral fssint_1 fssint_0 sup_set_class wss fssint_0 fssint_2 wral issint_0 fssint_1 fssint_2 cint dfss3 issint_0 sup_set_class fssint_2 cint wcel issint_0 sup_set_class fssint_0 sup_set_class wcel fssint_0 fssint_2 wral issint_0 fssint_1 fssint_0 issint_0 sup_set_class fssint_2 issint_0 vex elint2 ralbii issint_0 sup_set_class fssint_0 sup_set_class wcel fssint_0 fssint_2 wral issint_0 fssint_1 wral issint_0 sup_set_class fssint_0 sup_set_class wcel issint_0 fssint_1 wral fssint_0 fssint_2 wral fssint_1 fssint_0 sup_set_class wss fssint_0 fssint_2 wral issint_0 sup_set_class fssint_0 sup_set_class wcel issint_0 fssint_0 fssint_1 fssint_2 ralcom fssint_1 fssint_0 sup_set_class wss issint_0 sup_set_class fssint_0 sup_set_class wcel issint_0 fssint_1 wral fssint_0 fssint_2 issint_0 fssint_1 fssint_0 sup_set_class dfss3 ralbii bitr4i 3bitri $.
$}
$( /* Subclass of the intersection of a class abstraction.  (Contributed by
       NM, 31-Jul-2006.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) */

$)
${
	$d x y A $.
	$d x y $.
	$d y ph $.
	issintab_0 $f set y $.
	fssintab_0 $f wff ph $.
	fssintab_1 $f set x $.
	fssintab_2 $f class A $.
	ssintab $p |- ( A C_ |^| { x | ph } <-> A. x ( ph -> A C_ x ) ) $= fssintab_2 fssintab_0 fssintab_1 cab cint wss fssintab_2 issintab_0 sup_set_class wss issintab_0 fssintab_0 fssintab_1 cab wral fssintab_0 fssintab_2 fssintab_1 sup_set_class wss wi fssintab_1 wal issintab_0 fssintab_2 fssintab_0 fssintab_1 cab ssint fssintab_0 fssintab_2 issintab_0 sup_set_class wss fssintab_2 fssintab_1 sup_set_class wss issintab_0 fssintab_1 issintab_0 sup_set_class fssintab_1 sup_set_class fssintab_2 sseq2 ralab2 bitri $.
$}
$( /* Subclass of the least upper bound.  (Contributed by NM, 8-Aug-2000.) */

$)
${
	$d x y A $.
	$d x y B $.
	issintub_0 $f set y $.
	fssintub_0 $f set x $.
	fssintub_1 $f class A $.
	fssintub_2 $f class B $.
	ssintub $p |- A C_ |^| { x e. B | A C_ x } $= fssintub_1 fssintub_1 fssintub_0 sup_set_class wss fssintub_0 fssintub_2 crab cint wss fssintub_1 issintub_0 sup_set_class wss issintub_0 fssintub_1 fssintub_0 sup_set_class wss fssintub_0 fssintub_2 crab issintub_0 fssintub_1 fssintub_1 fssintub_0 sup_set_class wss fssintub_0 fssintub_2 crab ssint issintub_0 sup_set_class fssintub_1 fssintub_0 sup_set_class wss fssintub_0 fssintub_2 crab wcel issintub_0 sup_set_class fssintub_2 wcel fssintub_1 issintub_0 sup_set_class wss fssintub_1 fssintub_0 sup_set_class wss fssintub_1 issintub_0 sup_set_class wss fssintub_0 issintub_0 sup_set_class fssintub_2 fssintub_0 sup_set_class issintub_0 sup_set_class fssintub_1 sseq2 elrab simprbi mprgbir $.
$}
$( /* Subclass of the minimum value of class of supersets.  (Contributed by
       NM, 10-Aug-2006.) */

$)
${
	$d x A $.
	fssmin_0 $f wff ph $.
	fssmin_1 $f set x $.
	fssmin_2 $f class A $.
	ssmin $p |- A C_ |^| { x | ( A C_ x /\ ph ) } $= fssmin_2 fssmin_2 fssmin_1 sup_set_class wss fssmin_0 wa fssmin_1 cab cint wss fssmin_2 fssmin_1 sup_set_class wss fssmin_0 wa fssmin_2 fssmin_1 sup_set_class wss wi fssmin_1 fssmin_2 fssmin_1 sup_set_class wss fssmin_0 wa fssmin_1 fssmin_2 ssintab fssmin_2 fssmin_1 sup_set_class wss fssmin_0 simpl mpgbir $.
$}
$( /* Any member of a class is the smallest of those members that include it.
       (Contributed by NM, 13-Aug-2002.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) */

$)
${
	$d x y A $.
	$d x y B $.
	iintmin_0 $f set y $.
	fintmin_0 $f set x $.
	fintmin_1 $f class A $.
	fintmin_2 $f class B $.
	intmin $p |- ( A e. B -> |^| { x e. B | A C_ x } = A ) $= fintmin_1 fintmin_2 wcel fintmin_1 fintmin_0 sup_set_class wss fintmin_0 fintmin_2 crab cint fintmin_1 fintmin_1 fintmin_2 wcel iintmin_0 fintmin_1 fintmin_0 sup_set_class wss fintmin_0 fintmin_2 crab cint fintmin_1 iintmin_0 sup_set_class fintmin_1 fintmin_0 sup_set_class wss fintmin_0 fintmin_2 crab cint wcel fintmin_1 fintmin_0 sup_set_class wss iintmin_0 sup_set_class fintmin_0 sup_set_class wcel wi fintmin_0 fintmin_2 wral fintmin_1 fintmin_2 wcel iintmin_0 sup_set_class fintmin_1 wcel fintmin_1 fintmin_0 sup_set_class wss fintmin_0 iintmin_0 sup_set_class fintmin_2 iintmin_0 vex elintrab fintmin_1 fintmin_2 wcel fintmin_1 fintmin_0 sup_set_class wss iintmin_0 sup_set_class fintmin_0 sup_set_class wcel wi fintmin_0 fintmin_2 wral fintmin_1 fintmin_1 wss iintmin_0 sup_set_class fintmin_1 wcel fintmin_1 ssid fintmin_1 fintmin_0 sup_set_class wss iintmin_0 sup_set_class fintmin_0 sup_set_class wcel wi fintmin_1 fintmin_1 wss iintmin_0 sup_set_class fintmin_1 wcel wi fintmin_0 fintmin_1 fintmin_2 fintmin_0 sup_set_class fintmin_1 wceq fintmin_1 fintmin_0 sup_set_class wss fintmin_1 fintmin_1 wss iintmin_0 sup_set_class fintmin_0 sup_set_class wcel iintmin_0 sup_set_class fintmin_1 wcel fintmin_0 sup_set_class fintmin_1 fintmin_1 sseq2 fintmin_0 sup_set_class fintmin_1 iintmin_0 sup_set_class eleq2 imbi12d rspcv mpii syl5bi ssrdv fintmin_1 fintmin_1 fintmin_0 sup_set_class wss fintmin_0 fintmin_2 crab cint wss fintmin_1 fintmin_2 wcel fintmin_0 fintmin_1 fintmin_2 ssintub a1i eqssd $.
$}
$( /* Intersection of subclasses.  (Contributed by NM, 14-Oct-1999.) */

$)
${
	$d x y A $.
	$d x y B $.
	iintss_0 $f set x $.
	iintss_1 $f set y $.
	fintss_0 $f class A $.
	fintss_1 $f class B $.
	intss $p |- ( A C_ B -> |^| B C_ |^| A ) $= iintss_1 sup_set_class fintss_0 wcel iintss_1 sup_set_class fintss_1 wcel wi iintss_1 wal iintss_0 sup_set_class fintss_1 cint wcel iintss_0 sup_set_class fintss_0 cint wcel wi iintss_0 wal fintss_0 fintss_1 wss fintss_1 cint fintss_0 cint wss iintss_1 sup_set_class fintss_0 wcel iintss_1 sup_set_class fintss_1 wcel wi iintss_1 wal iintss_0 sup_set_class fintss_1 cint wcel iintss_0 sup_set_class fintss_0 cint wcel wi iintss_0 iintss_1 sup_set_class fintss_0 wcel iintss_1 sup_set_class fintss_1 wcel wi iintss_1 wal iintss_1 sup_set_class fintss_1 wcel iintss_0 sup_set_class iintss_1 sup_set_class wcel wi iintss_1 wal iintss_1 sup_set_class fintss_0 wcel iintss_0 sup_set_class iintss_1 sup_set_class wcel wi iintss_1 wal iintss_0 sup_set_class fintss_1 cint wcel iintss_0 sup_set_class fintss_0 cint wcel iintss_1 sup_set_class fintss_0 wcel iintss_1 sup_set_class fintss_1 wcel wi iintss_1 sup_set_class fintss_1 wcel iintss_0 sup_set_class iintss_1 sup_set_class wcel wi iintss_1 sup_set_class fintss_0 wcel iintss_0 sup_set_class iintss_1 sup_set_class wcel wi iintss_1 iintss_1 sup_set_class fintss_0 wcel iintss_1 sup_set_class fintss_1 wcel iintss_0 sup_set_class iintss_1 sup_set_class wcel imim1 al2imi iintss_1 iintss_0 sup_set_class fintss_1 iintss_0 vex elint iintss_1 iintss_0 sup_set_class fintss_0 iintss_0 vex elint 3imtr4g alrimiv iintss_1 fintss_0 fintss_1 dfss2 iintss_0 fintss_1 cint fintss_0 cint dfss2 3imtr4i $.
$}
$( /* The intersection of a nonempty set is a subclass of its union.
       (Contributed by NM, 29-Jul-2006.) */

$)
${
	$d x y A $.
	$d x y $.
	iintssuni_0 $f set x $.
	iintssuni_1 $f set y $.
	fintssuni_0 $f class A $.
	intssuni $p |- ( A =/= (/) -> |^| A C_ U. A ) $= fintssuni_0 c0 wne iintssuni_0 fintssuni_0 cint fintssuni_0 cuni fintssuni_0 c0 wne iintssuni_0 sup_set_class iintssuni_1 sup_set_class wcel iintssuni_1 fintssuni_0 wral iintssuni_0 sup_set_class iintssuni_1 sup_set_class wcel iintssuni_1 fintssuni_0 wrex iintssuni_0 sup_set_class fintssuni_0 cint wcel iintssuni_0 sup_set_class fintssuni_0 cuni wcel fintssuni_0 c0 wne iintssuni_0 sup_set_class iintssuni_1 sup_set_class wcel iintssuni_1 fintssuni_0 wral iintssuni_0 sup_set_class iintssuni_1 sup_set_class wcel iintssuni_1 fintssuni_0 wrex iintssuni_0 sup_set_class iintssuni_1 sup_set_class wcel iintssuni_1 fintssuni_0 r19.2z ex iintssuni_1 iintssuni_0 sup_set_class fintssuni_0 iintssuni_0 vex elint2 iintssuni_1 iintssuni_0 sup_set_class fintssuni_0 eluni2 3imtr4g ssrdv $.
$}
$( /* Subclass of the intersection of a restricted class builder.
       (Contributed by NM, 30-Jan-2015.) */

$)
${
	$d x A $.
	fssintrab_0 $f wff ph $.
	fssintrab_1 $f set x $.
	fssintrab_2 $f class A $.
	fssintrab_3 $f class B $.
	ssintrab $p |- ( A C_ |^| { x e. B | ph } <-> A. x e. B ( ph -> A C_ x ) ) $= fssintrab_2 fssintrab_0 fssintrab_1 fssintrab_3 crab cint wss fssintrab_2 fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_1 cab cint wss fssintrab_0 fssintrab_2 fssintrab_1 sup_set_class wss wi fssintrab_1 fssintrab_3 wral fssintrab_0 fssintrab_1 fssintrab_3 crab cint fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_1 cab cint fssintrab_2 fssintrab_0 fssintrab_1 fssintrab_3 crab fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_1 cab fssintrab_0 fssintrab_1 fssintrab_3 df-rab inteqi sseq2i fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_2 fssintrab_1 sup_set_class wss wi fssintrab_1 wal fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 fssintrab_2 fssintrab_1 sup_set_class wss wi wi fssintrab_1 wal fssintrab_2 fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_1 cab cint wss fssintrab_0 fssintrab_2 fssintrab_1 sup_set_class wss wi fssintrab_1 fssintrab_3 wral fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_2 fssintrab_1 sup_set_class wss wi fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 fssintrab_2 fssintrab_1 sup_set_class wss wi wi fssintrab_1 fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 fssintrab_2 fssintrab_1 sup_set_class wss impexp albii fssintrab_1 sup_set_class fssintrab_3 wcel fssintrab_0 wa fssintrab_1 fssintrab_2 ssintab fssintrab_0 fssintrab_2 fssintrab_1 sup_set_class wss wi fssintrab_1 fssintrab_3 df-ral 3bitr4i bitri $.
$}
$( /* If the union of a class is included in its intersection, the class is
     either the empty set or a singleton ( ~ uniintsn ).  (Contributed by NM,
     30-Oct-2010.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) */

$)
${
	funissint_0 $f class A $.
	unissint $p |- ( U. A C_ |^| A <-> ( A = (/) \/ U. A = |^| A ) ) $= funissint_0 cuni funissint_0 cint wss funissint_0 c0 wceq funissint_0 cuni funissint_0 cint wceq wo funissint_0 cuni funissint_0 cint wss funissint_0 c0 wceq funissint_0 cuni funissint_0 cint wceq funissint_0 cuni funissint_0 cint wss funissint_0 c0 wceq wn funissint_0 cuni funissint_0 cint wceq funissint_0 cuni funissint_0 cint wss funissint_0 c0 wceq wn wa funissint_0 cuni funissint_0 cint funissint_0 cuni funissint_0 cint wss funissint_0 c0 wceq wn simpl funissint_0 c0 wceq wn funissint_0 cint funissint_0 cuni wss funissint_0 cuni funissint_0 cint wss funissint_0 c0 wceq wn funissint_0 c0 wne funissint_0 cint funissint_0 cuni wss funissint_0 c0 df-ne funissint_0 intssuni sylbir adantl eqssd ex orrd funissint_0 c0 wceq funissint_0 cuni funissint_0 cint wss funissint_0 cuni funissint_0 cint wceq funissint_0 c0 wceq c0 cint funissint_0 cuni funissint_0 cint funissint_0 cuni cvv c0 cint funissint_0 cuni ssv int0 sseqtr4i funissint_0 c0 inteq syl5sseqr funissint_0 cuni funissint_0 cint eqimss jaoi impbii $.
$}
$( /* Subclass relationship for intersection and union.  (Contributed by NM,
     29-Jul-2006.) */

$)
${
	fintssuni2_0 $f class A $.
	fintssuni2_1 $f class B $.
	intssuni2 $p |- ( ( A C_ B /\ A =/= (/) ) -> |^| A C_ U. B ) $= fintssuni2_0 c0 wne fintssuni2_0 fintssuni2_1 wss fintssuni2_0 cint fintssuni2_0 cuni fintssuni2_1 cuni fintssuni2_0 intssuni fintssuni2_0 fintssuni2_1 uniss sylan9ssr $.
$}
$( /* Under subset ordering, the intersection of a restricted class
       abstraction is less than or equal to any of its members.  (Contributed
       by NM, 7-Sep-2013.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	fintminss_0 $f wff ph $.
	fintminss_1 $f wff ps $.
	fintminss_2 $f set x $.
	fintminss_3 $f class A $.
	fintminss_4 $f class B $.
	eintminss_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	intminss $p |- ( ( A e. B /\ ps ) -> |^| { x e. B | ph } C_ A ) $= fintminss_3 fintminss_4 wcel fintminss_1 wa fintminss_3 fintminss_0 fintminss_2 fintminss_4 crab wcel fintminss_0 fintminss_2 fintminss_4 crab cint fintminss_3 wss fintminss_0 fintminss_1 fintminss_2 fintminss_3 fintminss_4 eintminss_0 elrab fintminss_3 fintminss_0 fintminss_2 fintminss_4 crab intss1 sylbir $.
$}
$( /* Any set is the smallest of all sets that include it.  (Contributed by
       NM, 20-Sep-2003.) */

$)
${
	$d x A $.
	fintmin2_0 $f set x $.
	fintmin2_1 $f class A $.
	eintmin2_0 $e |- A e. _V $.
	intmin2 $p |- |^| { x | A C_ x } = A $= fintmin2_1 fintmin2_0 sup_set_class wss fintmin2_0 cvv crab cint fintmin2_1 fintmin2_0 sup_set_class wss fintmin2_0 cab cint fintmin2_1 fintmin2_1 fintmin2_0 sup_set_class wss fintmin2_0 cvv crab fintmin2_1 fintmin2_0 sup_set_class wss fintmin2_0 cab fintmin2_1 fintmin2_0 sup_set_class wss fintmin2_0 rabab inteqi fintmin2_1 cvv wcel fintmin2_1 fintmin2_0 sup_set_class wss fintmin2_0 cvv crab cint fintmin2_1 wceq eintmin2_0 fintmin2_0 fintmin2_1 cvv intmin ax-mp eqtr3i $.
$}
$( /* Under subset ordering, the intersection of a class abstraction is less
       than or equal to any of its members.  (Contributed by NM,
       3-Jul-2005.) */

$)
${
	$d x A $.
	$d x ps $.
	fintmin3_0 $f wff ph $.
	fintmin3_1 $f wff ps $.
	fintmin3_2 $f set x $.
	fintmin3_3 $f class A $.
	fintmin3_4 $f class V $.
	eintmin3_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eintmin3_1 $e |- ps $.
	intmin3 $p |- ( A e. V -> |^| { x | ph } C_ A ) $= fintmin3_3 fintmin3_4 wcel fintmin3_3 fintmin3_0 fintmin3_2 cab wcel fintmin3_0 fintmin3_2 cab cint fintmin3_3 wss fintmin3_3 fintmin3_4 wcel fintmin3_3 fintmin3_0 fintmin3_2 cab wcel fintmin3_1 eintmin3_1 fintmin3_0 fintmin3_1 fintmin3_2 fintmin3_3 fintmin3_4 eintmin3_0 elabg mpbiri fintmin3_3 fintmin3_0 fintmin3_2 cab intss1 syl $.
$}
$( /* Elimination of a conjunct in a class intersection.  (Contributed by NM,
       31-Jul-2006.) */

$)
${
	$d x y A $.
	$d y ph $.
	iintmin4_0 $f set y $.
	fintmin4_0 $f wff ph $.
	fintmin4_1 $f set x $.
	fintmin4_2 $f class A $.
	intmin4 $p |- ( A C_ |^| { x | ph } -> |^| { x | ( A C_ x /\ ph ) } = |^| { x | ph } ) $= fintmin4_2 fintmin4_0 fintmin4_1 cab cint wss iintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa fintmin4_1 cab cint fintmin4_0 fintmin4_1 cab cint fintmin4_2 fintmin4_0 fintmin4_1 cab cint wss fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 wal fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 wal iintmin4_0 sup_set_class fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa fintmin4_1 cab cint wcel iintmin4_0 sup_set_class fintmin4_0 fintmin4_1 cab cint wcel fintmin4_2 fintmin4_0 fintmin4_1 cab cint wss fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss wi fintmin4_1 wal fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 wal fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 wal wb fintmin4_0 fintmin4_1 fintmin4_2 ssintab fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss wi fintmin4_1 wal fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi wb fintmin4_1 wal fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 wal fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 wal wb fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss wi fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi wb fintmin4_1 fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss wi fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss wi fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 simpr fintmin4_0 fintmin4_2 fintmin4_1 sup_set_class wss ancr impbid2 imbi1d alimi fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_0 iintmin4_0 sup_set_class fintmin4_1 sup_set_class wcel wi fintmin4_1 albi syl sylbi fintmin4_2 fintmin4_1 sup_set_class wss fintmin4_0 wa fintmin4_1 iintmin4_0 sup_set_class iintmin4_0 vex elintab fintmin4_0 fintmin4_1 iintmin4_0 sup_set_class iintmin4_0 vex elintab 3bitr4g eqrdv $.
$}
$( /* The intersection of a special case of a class abstraction. ` y ` may be
       free in ` ph ` and ` A ` , which can be thought of a ` ph ( y ) ` and
       ` A ( y ) ` .  Typically, ~ abrexex2 or ~ abexssex can be used to
       satisfy the second hypothesis.  (Contributed by NM, 28-Jul-2006.)
       (Proof shortened by Mario Carneiro, 14-Nov-2016.) */

$)
${
	$d x z A $.
	$d x z ph $.
	$d x y z $.
	iintab_0 $f set z $.
	fintab_0 $f wff ph $.
	fintab_1 $f set x $.
	fintab_2 $f set y $.
	fintab_3 $f class A $.
	eintab_0 $e |- A e. _V $.
	eintab_1 $e |- { x | E. y ( ph /\ x = A ) } e. _V $.
	intab $p |- |^| { x | A. y ( ph -> A e. x ) } = { x | E. y ( ph /\ x = A ) } $= fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab cint fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 fintab_1 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_1 cab fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab cint fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab wcel fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab cint fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wss fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab wcel fintab_0 fintab_3 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wcel wi fintab_2 fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_0 fintab_3 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wcel wi fintab_2 wal fintab_1 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 fintab_1 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_1 cab cvv fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 fintab_1 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_1 iintab_0 sup_set_class fintab_1 sup_set_class wceq fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_0 fintab_1 sup_set_class fintab_3 wceq wa fintab_2 iintab_0 sup_set_class fintab_1 sup_set_class wceq iintab_0 sup_set_class fintab_3 wceq fintab_1 sup_set_class fintab_3 wceq fintab_0 iintab_0 sup_set_class fintab_1 sup_set_class fintab_3 eqeq1 anbi2d exbidv cbvabv eintab_1 eqeltri fintab_1 sup_set_class fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wceq fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_0 fintab_3 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wcel wi fintab_2 fintab_2 fintab_1 sup_set_class fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_2 iintab_0 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 nfe1 nfab nfeq2 fintab_1 sup_set_class fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wceq fintab_3 fintab_1 sup_set_class wcel fintab_3 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wcel fintab_0 fintab_1 sup_set_class fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_3 eleq2 imbi2d albid elab fintab_0 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_3 wsbc fintab_3 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab wcel fintab_0 iintab_0 sup_set_class fintab_3 wceq fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex wi iintab_0 wal fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_3 wsbc fintab_0 iintab_0 sup_set_class fintab_3 wceq fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex wi iintab_0 fintab_0 iintab_0 sup_set_class fintab_3 wceq fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 19.8a ex alrimiv fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_3 eintab_0 sbc6 sylibr fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_3 df-sbc sylib mpgbir fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 cab fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab intss1 ax-mp fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab cint fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal iintab_0 sup_set_class fintab_1 sup_set_class wcel wi fintab_1 wal iintab_0 sup_set_class fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 cab cint wcel fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal iintab_0 sup_set_class fintab_1 sup_set_class wcel wi fintab_1 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal iintab_0 sup_set_class fintab_1 sup_set_class wcel fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal wa fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_0 fintab_3 fintab_1 sup_set_class wcel wi wa fintab_2 wex iintab_0 sup_set_class fintab_1 sup_set_class wcel fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 19.29r fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_0 fintab_3 fintab_1 sup_set_class wcel wi wa iintab_0 sup_set_class fintab_1 sup_set_class wcel fintab_2 fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_0 fintab_3 fintab_1 sup_set_class wcel wi wa iintab_0 sup_set_class fintab_3 fintab_1 sup_set_class fintab_0 iintab_0 sup_set_class fintab_3 wceq fintab_0 fintab_3 fintab_1 sup_set_class wcel wi simplr fintab_0 fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_3 fintab_1 sup_set_class wcel iintab_0 sup_set_class fintab_3 wceq fintab_0 fintab_3 fintab_1 sup_set_class wcel pm3.35 adantlr eqeltrd exlimiv syl ex alrimiv fintab_0 fintab_3 fintab_1 sup_set_class wcel wi fintab_2 wal fintab_1 iintab_0 sup_set_class iintab_0 vex elintab sylibr abssi eqssi fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_2 wex fintab_0 fintab_1 sup_set_class fintab_3 wceq wa fintab_2 wex iintab_0 fintab_1 iintab_0 sup_set_class fintab_1 sup_set_class wceq fintab_0 iintab_0 sup_set_class fintab_3 wceq wa fintab_0 fintab_1 sup_set_class fintab_3 wceq wa fintab_2 iintab_0 sup_set_class fintab_1 sup_set_class wceq iintab_0 sup_set_class fintab_3 wceq fintab_1 sup_set_class fintab_3 wceq fintab_0 iintab_0 sup_set_class fintab_1 sup_set_class fintab_3 eqeq1 anbi2d exbidv cbvabv eqtri $.
$}
$( /* The intersection of a class containing the empty set is empty.
     (Contributed by NM, 24-Apr-2004.) */

$)
${
	fint0el_0 $f class A $.
	int0el $p |- ( (/) e. A -> |^| A = (/) ) $= c0 fint0el_0 wcel fint0el_0 cint c0 c0 fint0el_0 intss1 c0 fint0el_0 cint wss c0 fint0el_0 wcel fint0el_0 cint 0ss a1i eqssd $.
$}
$( /* The class intersection of the union of two classes.  Theorem 78 of
       [Suppes] p. 42.  (Contributed by NM, 22-Sep-2002.) */

$)
${
	$d x y A $.
	$d x y B $.
	iintun_0 $f set x $.
	iintun_1 $f set y $.
	fintun_0 $f class A $.
	fintun_1 $f class B $.
	intun $p |- |^| ( A u. B ) = ( |^| A i^i |^| B ) $= iintun_0 fintun_0 fintun_1 cun cint fintun_0 cint fintun_1 cint cin iintun_1 sup_set_class fintun_0 fintun_1 cun wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 wal iintun_0 sup_set_class fintun_0 cint wcel iintun_0 sup_set_class fintun_1 cint wcel wa iintun_0 sup_set_class fintun_0 fintun_1 cun cint wcel iintun_0 sup_set_class fintun_0 cint fintun_1 cint cin wcel iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_1 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi wa iintun_1 wal iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 wal iintun_1 sup_set_class fintun_1 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 wal wa iintun_1 sup_set_class fintun_0 fintun_1 cun wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 wal iintun_0 sup_set_class fintun_0 cint wcel iintun_0 sup_set_class fintun_1 cint wcel wa iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_1 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 19.26 iintun_1 sup_set_class fintun_0 fintun_1 cun wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_1 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi wa iintun_1 iintun_1 sup_set_class fintun_0 fintun_1 cun wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_0 wcel iintun_1 sup_set_class fintun_1 wcel wo iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 sup_set_class fintun_1 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi wa iintun_1 sup_set_class fintun_0 fintun_1 cun wcel iintun_1 sup_set_class fintun_0 wcel iintun_1 sup_set_class fintun_1 wcel wo iintun_0 sup_set_class iintun_1 sup_set_class wcel iintun_1 sup_set_class fintun_0 fintun_1 elun imbi1i iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel iintun_1 sup_set_class fintun_1 wcel jaob bitri albii iintun_0 sup_set_class fintun_0 cint wcel iintun_1 sup_set_class fintun_0 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 wal iintun_0 sup_set_class fintun_1 cint wcel iintun_1 sup_set_class fintun_1 wcel iintun_0 sup_set_class iintun_1 sup_set_class wcel wi iintun_1 wal iintun_1 iintun_0 sup_set_class fintun_0 iintun_0 vex elint iintun_1 iintun_0 sup_set_class fintun_1 iintun_0 vex elint anbi12i 3bitr4i iintun_1 iintun_0 sup_set_class fintun_0 fintun_1 cun iintun_0 vex elint iintun_0 sup_set_class fintun_0 cint fintun_1 cint elin 3bitr4i eqriv $.
$}
$( /* The intersection of a pair is the intersection of its members.  Theorem
       71 of [Suppes] p. 42.  (Contributed by NM, 14-Oct-1999.) */

$)
${
	$d x y A $.
	$d x y B $.
	iintpr_0 $f set x $.
	iintpr_1 $f set y $.
	fintpr_0 $f class A $.
	fintpr_1 $f class B $.
	eintpr_0 $e |- A e. _V $.
	eintpr_1 $e |- B e. _V $.
	intpr $p |- |^| { A , B } = ( A i^i B ) $= iintpr_0 fintpr_0 fintpr_1 cpr cint fintpr_0 fintpr_1 cin iintpr_1 sup_set_class fintpr_0 fintpr_1 cpr wcel iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 wal iintpr_0 sup_set_class fintpr_0 wcel iintpr_0 sup_set_class fintpr_1 wcel wa iintpr_0 sup_set_class fintpr_0 fintpr_1 cpr cint wcel iintpr_0 sup_set_class fintpr_0 fintpr_1 cin wcel iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_1 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi wa iintpr_1 wal iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 wal iintpr_1 sup_set_class fintpr_1 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 wal wa iintpr_1 sup_set_class fintpr_0 fintpr_1 cpr wcel iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 wal iintpr_0 sup_set_class fintpr_0 wcel iintpr_0 sup_set_class fintpr_1 wcel wa iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_1 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 19.26 iintpr_1 sup_set_class fintpr_0 fintpr_1 cpr wcel iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_1 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi wa iintpr_1 iintpr_1 sup_set_class fintpr_0 fintpr_1 cpr wcel iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_0 wceq iintpr_1 sup_set_class fintpr_1 wceq wo iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 sup_set_class fintpr_1 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi wa iintpr_1 sup_set_class fintpr_0 fintpr_1 cpr wcel iintpr_1 sup_set_class fintpr_0 wceq iintpr_1 sup_set_class fintpr_1 wceq wo iintpr_0 sup_set_class iintpr_1 sup_set_class wcel iintpr_1 sup_set_class fintpr_0 fintpr_1 iintpr_1 vex elpr imbi1i iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel iintpr_1 sup_set_class fintpr_1 wceq jaob bitri albii iintpr_0 sup_set_class fintpr_0 wcel iintpr_1 sup_set_class fintpr_0 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 wal iintpr_0 sup_set_class fintpr_1 wcel iintpr_1 sup_set_class fintpr_1 wceq iintpr_0 sup_set_class iintpr_1 sup_set_class wcel wi iintpr_1 wal iintpr_1 iintpr_0 sup_set_class fintpr_0 eintpr_0 clel4 iintpr_1 iintpr_0 sup_set_class fintpr_1 eintpr_1 clel4 anbi12i 3bitr4i iintpr_1 iintpr_0 sup_set_class fintpr_0 fintpr_1 cpr iintpr_0 vex elint iintpr_0 sup_set_class fintpr_0 fintpr_1 elin 3bitr4i eqriv $.
$}
$( /* The intersection of a pair is the intersection of its members.  Closed
       form of ~ intpr .  Theorem 71 of [Suppes] p. 42.  (Contributed by FL,
       27-Apr-2008.) */

$)
${
	$d x y A $.
	$d y B $.
	iintprg_0 $f set x $.
	iintprg_1 $f set y $.
	fintprg_0 $f class A $.
	fintprg_1 $f class B $.
	fintprg_2 $f class V $.
	fintprg_3 $f class W $.
	intprg $p |- ( ( A e. V /\ B e. W ) -> |^| { A , B } = ( A i^i B ) ) $= iintprg_0 sup_set_class iintprg_1 sup_set_class cpr cint iintprg_0 sup_set_class iintprg_1 sup_set_class cin wceq fintprg_0 iintprg_1 sup_set_class cpr cint fintprg_0 iintprg_1 sup_set_class cin wceq fintprg_0 fintprg_1 cpr cint fintprg_0 fintprg_1 cin wceq iintprg_0 iintprg_1 fintprg_0 fintprg_1 fintprg_2 fintprg_3 iintprg_0 sup_set_class fintprg_0 wceq iintprg_0 sup_set_class iintprg_1 sup_set_class cpr cint fintprg_0 iintprg_1 sup_set_class cpr cint iintprg_0 sup_set_class iintprg_1 sup_set_class cin fintprg_0 iintprg_1 sup_set_class cin iintprg_0 sup_set_class fintprg_0 wceq iintprg_0 sup_set_class iintprg_1 sup_set_class cpr fintprg_0 iintprg_1 sup_set_class cpr iintprg_0 sup_set_class fintprg_0 iintprg_1 sup_set_class preq1 inteqd iintprg_0 sup_set_class fintprg_0 iintprg_1 sup_set_class ineq1 eqeq12d iintprg_1 sup_set_class fintprg_1 wceq fintprg_0 iintprg_1 sup_set_class cpr cint fintprg_0 fintprg_1 cpr cint fintprg_0 iintprg_1 sup_set_class cin fintprg_0 fintprg_1 cin iintprg_1 sup_set_class fintprg_1 wceq fintprg_0 iintprg_1 sup_set_class cpr fintprg_0 fintprg_1 cpr iintprg_1 sup_set_class fintprg_1 fintprg_0 preq2 inteqd iintprg_1 sup_set_class fintprg_1 fintprg_0 ineq2 eqeq12d iintprg_0 sup_set_class iintprg_1 sup_set_class iintprg_0 vex iintprg_1 vex intpr vtocl2g $.
$}
$( /* Intersection of a singleton.  (Contributed by Stefan O'Rear,
     22-Feb-2015.) */

$)
${
	fintsng_0 $f class A $.
	fintsng_1 $f class V $.
	intsng $p |- ( A e. V -> |^| { A } = A ) $= fintsng_0 fintsng_1 wcel fintsng_0 csn cint fintsng_0 fintsng_0 cpr cint fintsng_0 fintsng_0 csn fintsng_0 fintsng_0 cpr fintsng_0 dfsn2 inteqi fintsng_0 fintsng_1 wcel fintsng_0 fintsng_0 cpr cint fintsng_0 fintsng_0 cin fintsng_0 fintsng_0 fintsng_1 wcel fintsng_0 fintsng_0 cpr cint fintsng_0 fintsng_0 cin wceq fintsng_0 fintsng_0 fintsng_1 fintsng_1 intprg anidms fintsng_0 inidm syl6eq syl5eq $.
$}
$( /* The intersection of a singleton is its member.  Theorem 70 of [Suppes]
       p. 41.  (Contributed by NM, 29-Sep-2002.) */

$)
${
	fintsn_0 $f class A $.
	eintsn_0 $e |- A e. _V $.
	intsn $p |- |^| { A } = A $= fintsn_0 cvv wcel fintsn_0 csn cint fintsn_0 wceq eintsn_0 fintsn_0 cvv intsng ax-mp $.
$}
$( /* Two ways to express " ` A ` is a singleton."  See also ~ en1 , ~ en1b ,
       ~ card1 , and ~ eusn .  (Contributed by NM, 2-Aug-2010.) */

$)
${
	$d x y A $.
	iuniintsn_0 $f set y $.
	funiintsn_0 $f set x $.
	funiintsn_1 $f class A $.
	uniintsn $p |- ( U. A = |^| A <-> E. x A = { x } ) $= funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_0 wex funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 wex funiintsn_0 sup_set_class funiintsn_1 wcel iuniintsn_0 sup_set_class funiintsn_1 wcel wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq wi iuniintsn_0 wal funiintsn_0 wal wa funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_0 wex funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 wex funiintsn_0 sup_set_class funiintsn_1 wcel iuniintsn_0 sup_set_class funiintsn_1 wcel wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq wi iuniintsn_0 wal funiintsn_0 wal funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 c0 wne funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 wex funiintsn_1 cuni funiintsn_1 cint wceq cvv c0 wne funiintsn_1 c0 wne vn0 funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 c0 cvv c0 funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 c0 wceq cvv c0 wceq funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 c0 wceq wa funiintsn_1 cint cvv c0 funiintsn_1 c0 wceq funiintsn_1 cint cvv wceq funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 c0 wceq funiintsn_1 cint c0 cint cvv funiintsn_1 c0 inteq int0 syl6eq adantl funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 c0 wceq funiintsn_1 cint c0 wceq funiintsn_1 c0 wceq funiintsn_1 cuni c0 wceq funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_1 cint c0 wceq funiintsn_1 c0 wceq funiintsn_1 cuni c0 cuni c0 funiintsn_1 c0 unieq uni0 syl6eq funiintsn_1 cuni funiintsn_1 cint c0 eqeq1 syl5ib imp eqtr3d ex necon3d mpi funiintsn_0 funiintsn_1 n0 sylib funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class funiintsn_1 wcel iuniintsn_0 sup_set_class funiintsn_1 wcel wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq wi funiintsn_0 iuniintsn_0 funiintsn_0 sup_set_class funiintsn_1 wcel iuniintsn_0 sup_set_class funiintsn_1 wcel wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class funiintsn_1 funiintsn_0 vex iuniintsn_0 vex prss funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin wss funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin wss funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun wss funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cuni funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cint funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cuni funiintsn_1 cint funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cint funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cuni funiintsn_1 cuni funiintsn_1 cint funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cuni funiintsn_1 cuni wss funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 uniss adantl funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss simpl sseqtrd funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 wss funiintsn_1 cint funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr cint wss funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cpr funiintsn_1 intss adantl sstrd funiintsn_0 sup_set_class iuniintsn_0 sup_set_class funiintsn_0 vex iuniintsn_0 vex unipr funiintsn_0 sup_set_class iuniintsn_0 sup_set_class funiintsn_0 vex iuniintsn_0 vex intpr 3sstr3g funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin funiintsn_0 sup_set_class funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class inss1 funiintsn_0 sup_set_class iuniintsn_0 sup_set_class ssun1 sstri jctir funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin wss funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun wss wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cun funiintsn_0 sup_set_class iuniintsn_0 sup_set_class cin eqss funiintsn_0 sup_set_class iuniintsn_0 sup_set_class uneqin bitr3i sylib ex syl5bi alrimivv jca funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 weu funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 cab funiintsn_0 sup_set_class csn wceq funiintsn_0 wex funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 wex funiintsn_0 sup_set_class funiintsn_1 wcel iuniintsn_0 sup_set_class funiintsn_1 wcel wa funiintsn_0 sup_set_class iuniintsn_0 sup_set_class wceq wi iuniintsn_0 wal funiintsn_0 wal wa funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_0 wex funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 euabsn funiintsn_0 sup_set_class funiintsn_1 wcel iuniintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 iuniintsn_0 funiintsn_0 sup_set_class iuniintsn_0 sup_set_class funiintsn_1 eleq1 eu4 funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 cab funiintsn_0 sup_set_class csn wceq funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_0 funiintsn_0 sup_set_class funiintsn_1 wcel funiintsn_0 cab funiintsn_1 funiintsn_0 sup_set_class csn funiintsn_0 funiintsn_1 abid2 eqeq1i exbii 3bitr3i sylib funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_1 cuni funiintsn_1 cint wceq funiintsn_0 funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_0 sup_set_class csn cuni funiintsn_0 sup_set_class funiintsn_1 cuni funiintsn_1 cint funiintsn_0 sup_set_class funiintsn_0 vex unisn funiintsn_1 funiintsn_0 sup_set_class csn unieq funiintsn_1 funiintsn_0 sup_set_class csn wceq funiintsn_1 cint funiintsn_0 sup_set_class csn cint funiintsn_0 sup_set_class funiintsn_1 funiintsn_0 sup_set_class csn inteq funiintsn_0 sup_set_class funiintsn_0 vex intsn syl6eq 3eqtr4a exlimiv impbii $.
$}
$( /* The union and the intersection of a class abstraction are equal exactly
       when there is a unique satisfying value of ` ph ( x ) ` .  (Contributed
       by Mario Carneiro, 24-Dec-2016.) */

$)
${
	$d x y $.
	$d y ph $.
	iuniintab_0 $f set y $.
	funiintab_0 $f wff ph $.
	funiintab_1 $f set x $.
	uniintab $p |- ( E! x ph <-> U. { x | ph } = |^| { x | ph } ) $= funiintab_0 funiintab_1 weu funiintab_0 funiintab_1 cab iuniintab_0 sup_set_class csn wceq iuniintab_0 wex funiintab_0 funiintab_1 cab cuni funiintab_0 funiintab_1 cab cint wceq funiintab_0 funiintab_1 iuniintab_0 euabsn2 iuniintab_0 funiintab_0 funiintab_1 cab uniintsn bitr4i $.
$}
$( /* Theorem joining a singleton to an intersection.  (Contributed by NM,
       29-Sep-2002.) */

$)
${
	fintunsn_0 $f class A $.
	fintunsn_1 $f class B $.
	eintunsn_0 $e |- B e. _V $.
	intunsn $p |- |^| ( A u. { B } ) = ( |^| A i^i B ) $= fintunsn_0 fintunsn_1 csn cun cint fintunsn_0 cint fintunsn_1 csn cint cin fintunsn_0 cint fintunsn_1 cin fintunsn_0 fintunsn_1 csn intun fintunsn_1 csn cint fintunsn_1 fintunsn_0 cint fintunsn_1 eintunsn_0 intsn ineq2i eqtri $.
$}
$( /* Relative intersection of an empty set.  (Contributed by Stefan O'Rear,
     3-Apr-2015.) */

$)
${
	frint0_0 $f class A $.
	frint0_1 $f class X $.
	rint0 $p |- ( X = (/) -> ( A i^i |^| X ) = A ) $= frint0_1 c0 wceq frint0_0 frint0_1 cint cin frint0_0 c0 cint cin frint0_0 frint0_1 c0 wceq frint0_1 cint c0 cint frint0_0 frint0_1 c0 inteq ineq2d frint0_0 c0 cint cin frint0_0 cvv cin frint0_0 c0 cint cvv frint0_0 int0 ineq2i frint0_0 inv1 eqtri syl6eq $.
$}
$( /* Membership in a restricted intersection.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) */

$)
${
	$d B y $.
	$d X y $.
	felrint_0 $f set y $.
	felrint_1 $f class A $.
	felrint_2 $f class B $.
	felrint_3 $f class X $.
	elrint $p |- ( X e. ( A i^i |^| B ) <-> ( X e. A /\ A. y e. B X e. y ) ) $= felrint_3 felrint_1 felrint_2 cint cin wcel felrint_3 felrint_1 wcel felrint_3 felrint_2 cint wcel wa felrint_3 felrint_1 wcel felrint_3 felrint_0 sup_set_class wcel felrint_0 felrint_2 wral wa felrint_3 felrint_1 felrint_2 cint elin felrint_3 felrint_1 wcel felrint_3 felrint_2 cint wcel felrint_3 felrint_0 sup_set_class wcel felrint_0 felrint_2 wral felrint_0 felrint_3 felrint_2 felrint_1 elintg pm5.32i bitri $.
$}
$( /* Membership in a restricted intersection.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) */

$)
${
	$d B y $.
	$d X y $.
	felrint2_0 $f set y $.
	felrint2_1 $f class A $.
	felrint2_2 $f class B $.
	felrint2_3 $f class X $.
	elrint2 $p |- ( X e. A -> ( X e. ( A i^i |^| B ) <-> A. y e. B X e. y ) ) $= felrint2_3 felrint2_1 felrint2_2 cint cin wcel felrint2_3 felrint2_1 wcel felrint2_3 felrint2_0 sup_set_class wcel felrint2_0 felrint2_2 wral felrint2_0 felrint2_1 felrint2_2 felrint2_3 elrint baib $.
$}

