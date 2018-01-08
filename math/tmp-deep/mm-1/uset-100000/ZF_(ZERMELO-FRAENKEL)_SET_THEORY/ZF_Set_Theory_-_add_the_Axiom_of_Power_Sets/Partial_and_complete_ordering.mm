$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Epsilon_and_identity_relations.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Partial and complete ordering

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* We have not yet defined relations ( ~ df-rel ), but here we introduce a
few related notions we will use to develop ordinals.  The class variable
` R ` is no different from other class variables, but it reminds us that
normally it represents what we will later call a "relation."
*/

$)
$( /* Declare new constant symbols. */

$)
$c Po  $.
$( /* Partial ordering predicate symbol (read: 'partial ordering'). */

$)
$c Or  $.
$( /* Strict complete ordering predicate symbol (read: 'orders'). */

$)
$( /* Extend wff notation to include the strict partial ordering predicate.
     Read:  ' ` R ` is a partial order on ` A ` .' */

$)
${
	fwpo_0 $f class A $.
	fwpo_1 $f class R $.
	wpo $a wff R Po A $.
$}
$( /* Extend wff notation to include the strict complete ordering predicate.
     Read:  ' ` R ` orders ` A ` .' */

$)
${
	fwor_0 $f class A $.
	fwor_1 $f class R $.
	wor $a wff R Or A $.
$}
$( /* Define the strict partial order predicate.  Definition of [Enderton]
       p. 168.  The expression ` R Po A ` means ` R ` is a partial order on
       ` A ` .  For example, ` < Po RR ` is true, while ` <_ Po RR ` is false
       ( ~ ex-po ).  (Contributed by NM, 16-Mar-1997.) */

$)
${
	$d x y z R $.
	$d x y z A $.
	fdf-po_0 $f set x $.
	fdf-po_1 $f set y $.
	fdf-po_2 $f set z $.
	fdf-po_3 $f class A $.
	fdf-po_4 $f class R $.
	df-po $a |- ( R Po A <-> A. x e. A A. y e. A A. z e. A ( -. x R x /\ ( ( x R y /\ y R z ) -> x R z ) ) ) $.
$}
$( /* Define the strict complete (linear) order predicate.  The expression
       ` R Or A ` is true if relationship ` R ` orders ` A ` .  For example,
       ` < Or RR ` is true ( ~ ltso ).  Equivalent to Definition 6.19(1) of
       [TakeutiZaring] p. 29.  (Contributed by NM, 21-Jan-1996.) */

$)
${
	$d x y R $.
	$d x y A $.
	fdf-so_0 $f set x $.
	fdf-so_1 $f set y $.
	fdf-so_2 $f class A $.
	fdf-so_3 $f class R $.
	df-so $a |- ( R Or A <-> ( R Po A /\ A. x e. A A. y e. A ( x R y \/ x = y \/ y R x ) ) ) $.
$}
$( /* Subset theorem for the partial ordering predicate.  (Contributed by NM,
       27-Mar-1997.)  (Proof shortened by Mario Carneiro, 18-Nov-2016.) */

$)
${
	$d x y z R $.
	$d x y z A $.
	$d x y z B $.
	iposs_0 $f set x $.
	iposs_1 $f set y $.
	iposs_2 $f set z $.
	fposs_0 $f class A $.
	fposs_1 $f class B $.
	fposs_2 $f class R $.
	poss $p |- ( A C_ B -> ( R Po B -> R Po A ) ) $= fposs_0 fposs_1 wss iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_1 wral iposs_0 fposs_1 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_0 wral iposs_1 fposs_0 wral iposs_0 fposs_0 wral fposs_1 fposs_2 wpo fposs_0 fposs_2 wpo fposs_0 fposs_1 wss iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_1 wral iposs_0 fposs_1 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_1 wral iposs_0 fposs_0 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_0 wral iposs_1 fposs_0 wral iposs_0 fposs_0 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_1 wral iposs_0 fposs_0 fposs_1 ssralv fposs_0 fposs_1 wss iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_1 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_0 wral iposs_1 fposs_0 wral iposs_0 fposs_0 fposs_0 fposs_1 wss iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_1 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_0 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_0 wral iposs_1 fposs_0 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_1 fposs_0 fposs_1 ssralv fposs_0 fposs_1 wss iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_1 wral iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_0 wral iposs_1 fposs_0 iposs_0 sup_set_class iposs_0 sup_set_class fposs_2 wbr wn iposs_0 sup_set_class iposs_1 sup_set_class fposs_2 wbr iposs_1 sup_set_class iposs_2 sup_set_class fposs_2 wbr wa iposs_0 sup_set_class iposs_2 sup_set_class fposs_2 wbr wi wa iposs_2 fposs_0 fposs_1 ssralv ralimdv syld ralimdv syld iposs_0 iposs_1 iposs_2 fposs_1 fposs_2 df-po iposs_0 iposs_1 iposs_2 fposs_0 fposs_2 df-po 3imtr4g $.
$}
$( /* Equality theorem for partial ordering predicate.  (Contributed by NM,
       27-Mar-1997.) */

$)
${
	$d x y z R $.
	$d x y z S $.
	$d x y z A $.
	ipoeq1_0 $f set x $.
	ipoeq1_1 $f set y $.
	ipoeq1_2 $f set z $.
	fpoeq1_0 $f class A $.
	fpoeq1_1 $f class R $.
	fpoeq1_2 $f class S $.
	poeq1 $p |- ( R = S -> ( R Po A <-> S Po A ) ) $= fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_1 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wi wa ipoeq1_2 fpoeq1_0 wral ipoeq1_1 fpoeq1_0 wral ipoeq1_0 fpoeq1_0 wral ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_2 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_2 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wi wa ipoeq1_2 fpoeq1_0 wral ipoeq1_1 fpoeq1_0 wral ipoeq1_0 fpoeq1_0 wral fpoeq1_0 fpoeq1_1 wpo fpoeq1_0 fpoeq1_2 wpo fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_1 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wi wa ipoeq1_2 fpoeq1_0 wral ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_2 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_2 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wi wa ipoeq1_2 fpoeq1_0 wral ipoeq1_0 ipoeq1_1 fpoeq1_0 fpoeq1_0 fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_1 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wi wa ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_2 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_2 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wi wa ipoeq1_2 fpoeq1_0 fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_1 wbr wn ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_2 wbr wn ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wi ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_2 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wi fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_1 wbr ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_2 wbr ipoeq1_0 sup_set_class ipoeq1_0 sup_set_class fpoeq1_1 fpoeq1_2 breq notbid fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr wa ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_2 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr wa ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr fpoeq1_1 fpoeq1_2 wceq ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 wbr ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_2 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 wbr ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_2 wbr ipoeq1_0 sup_set_class ipoeq1_1 sup_set_class fpoeq1_1 fpoeq1_2 breq ipoeq1_1 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 fpoeq1_2 breq anbi12d ipoeq1_0 sup_set_class ipoeq1_2 sup_set_class fpoeq1_1 fpoeq1_2 breq imbi12d anbi12d ralbidv 2ralbidv ipoeq1_0 ipoeq1_1 ipoeq1_2 fpoeq1_0 fpoeq1_1 df-po ipoeq1_0 ipoeq1_1 ipoeq1_2 fpoeq1_0 fpoeq1_2 df-po 3bitr4g $.
$}
$( /* Equality theorem for partial ordering predicate.  (Contributed by NM,
     27-Mar-1997.) */

$)
${
	fpoeq2_0 $f class A $.
	fpoeq2_1 $f class B $.
	fpoeq2_2 $f class R $.
	poeq2 $p |- ( A = B -> ( R Po A <-> R Po B ) ) $= fpoeq2_0 fpoeq2_1 wceq fpoeq2_0 fpoeq2_2 wpo fpoeq2_1 fpoeq2_2 wpo fpoeq2_0 fpoeq2_1 wceq fpoeq2_1 fpoeq2_0 wss fpoeq2_0 fpoeq2_2 wpo fpoeq2_1 fpoeq2_2 wpo wi fpoeq2_1 fpoeq2_0 eqimss2 fpoeq2_1 fpoeq2_0 fpoeq2_2 poss syl fpoeq2_0 fpoeq2_1 wceq fpoeq2_0 fpoeq2_1 wss fpoeq2_1 fpoeq2_2 wpo fpoeq2_0 fpoeq2_2 wpo wi fpoeq2_0 fpoeq2_1 eqimss fpoeq2_0 fpoeq2_1 fpoeq2_2 poss syl impbid $.
$}
$( /* Bound-variable hypothesis builder for partial orders.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) */

$)
${
	$d R a b c $.
	$d A a b c $.
	$d x a b c $.
	infpo_0 $f set a $.
	infpo_1 $f set b $.
	infpo_2 $f set c $.
	fnfpo_0 $f set x $.
	fnfpo_1 $f class A $.
	fnfpo_2 $f class R $.
	enfpo_0 $e |- F/_ x R $.
	enfpo_1 $e |- F/_ x A $.
	nfpo $p |- F/ x R Po A $= fnfpo_1 fnfpo_2 wpo infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 wbr wn infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wa infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wi wa infpo_2 fnfpo_1 wral infpo_1 fnfpo_1 wral infpo_0 fnfpo_1 wral fnfpo_0 infpo_0 infpo_1 infpo_2 fnfpo_1 fnfpo_2 df-po infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 wbr wn infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wa infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wi wa infpo_2 fnfpo_1 wral infpo_1 fnfpo_1 wral fnfpo_0 infpo_0 fnfpo_1 enfpo_1 infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 wbr wn infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wa infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wi wa infpo_2 fnfpo_1 wral fnfpo_0 infpo_1 fnfpo_1 enfpo_1 infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 wbr wn infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wa infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wi wa fnfpo_0 infpo_2 fnfpo_1 enfpo_1 infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 wbr wn infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wa infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wi fnfpo_0 infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 wbr fnfpo_0 fnfpo_0 infpo_0 sup_set_class infpo_0 sup_set_class fnfpo_2 fnfpo_0 infpo_0 sup_set_class nfcv enfpo_0 fnfpo_0 infpo_0 sup_set_class nfcv nfbr nfn infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr wa infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr fnfpo_0 infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 wbr infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 wbr fnfpo_0 fnfpo_0 infpo_0 sup_set_class infpo_1 sup_set_class fnfpo_2 fnfpo_0 infpo_0 sup_set_class nfcv enfpo_0 fnfpo_0 infpo_1 sup_set_class nfcv nfbr fnfpo_0 infpo_1 sup_set_class infpo_2 sup_set_class fnfpo_2 fnfpo_0 infpo_1 sup_set_class nfcv enfpo_0 fnfpo_0 infpo_2 sup_set_class nfcv nfbr nfan fnfpo_0 infpo_0 sup_set_class infpo_2 sup_set_class fnfpo_2 fnfpo_0 infpo_0 sup_set_class nfcv enfpo_0 fnfpo_0 infpo_2 sup_set_class nfcv nfbr nfim nfan nfral nfral nfral nfxfr $.
$}
$( /* Bound-variable hypothesis builder for total orders.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) */

$)
${
	$d R a b $.
	$d A a b $.
	$d x a b $.
	infso_0 $f set a $.
	infso_1 $f set b $.
	fnfso_0 $f set x $.
	fnfso_1 $f class A $.
	fnfso_2 $f class R $.
	enfso_0 $e |- F/_ x R $.
	enfso_1 $e |- F/_ x A $.
	nfso $p |- F/ x R Or A $= fnfso_1 fnfso_2 wor fnfso_1 fnfso_2 wpo infso_0 sup_set_class infso_1 sup_set_class fnfso_2 wbr infso_0 sup_set_class infso_1 sup_set_class wceq infso_1 sup_set_class infso_0 sup_set_class fnfso_2 wbr w3o infso_1 fnfso_1 wral infso_0 fnfso_1 wral wa fnfso_0 infso_0 infso_1 fnfso_1 fnfso_2 df-so fnfso_1 fnfso_2 wpo infso_0 sup_set_class infso_1 sup_set_class fnfso_2 wbr infso_0 sup_set_class infso_1 sup_set_class wceq infso_1 sup_set_class infso_0 sup_set_class fnfso_2 wbr w3o infso_1 fnfso_1 wral infso_0 fnfso_1 wral fnfso_0 fnfso_0 fnfso_1 fnfso_2 enfso_0 enfso_1 nfpo infso_0 sup_set_class infso_1 sup_set_class fnfso_2 wbr infso_0 sup_set_class infso_1 sup_set_class wceq infso_1 sup_set_class infso_0 sup_set_class fnfso_2 wbr w3o infso_1 fnfso_1 wral fnfso_0 infso_0 fnfso_1 enfso_1 infso_0 sup_set_class infso_1 sup_set_class fnfso_2 wbr infso_0 sup_set_class infso_1 sup_set_class wceq infso_1 sup_set_class infso_0 sup_set_class fnfso_2 wbr w3o fnfso_0 infso_1 fnfso_1 enfso_1 infso_0 sup_set_class infso_1 sup_set_class fnfso_2 wbr infso_0 sup_set_class infso_1 sup_set_class wceq infso_1 sup_set_class infso_0 sup_set_class fnfso_2 wbr fnfso_0 fnfso_0 infso_0 sup_set_class infso_1 sup_set_class fnfso_2 fnfso_0 infso_0 sup_set_class nfcv enfso_0 fnfso_0 infso_1 sup_set_class nfcv nfbr infso_0 sup_set_class infso_1 sup_set_class wceq fnfso_0 nfv fnfso_0 infso_1 sup_set_class infso_0 sup_set_class fnfso_2 fnfso_0 infso_1 sup_set_class nfcv enfso_0 fnfso_0 infso_0 sup_set_class nfcv nfbr nf3or nfral nfral nfan nfxfr $.
$}
$( /* Properties of partial order relation in class notation.  (Contributed by
       NM, 27-Mar-1997.) */

$)
${
	$d x y z R $.
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	ipocl_0 $f set x $.
	ipocl_1 $f set y $.
	ipocl_2 $f set z $.
	fpocl_0 $f class A $.
	fpocl_1 $f class B $.
	fpocl_2 $f class C $.
	fpocl_3 $f class D $.
	fpocl_4 $f class R $.
	pocl $p |- ( R Po A -> ( ( B e. A /\ C e. A /\ D e. A ) -> ( -. B R B /\ ( ( B R C /\ C R D ) -> B R D ) ) ) ) $= fpocl_1 fpocl_0 wcel fpocl_2 fpocl_0 wcel fpocl_3 fpocl_0 wcel w3a fpocl_0 fpocl_4 wpo fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 fpocl_3 fpocl_4 wbr wa fpocl_1 fpocl_3 fpocl_4 wbr wi wa fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa wi fpocl_0 fpocl_4 wpo fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi wa wi fpocl_0 fpocl_4 wpo fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi wa wi fpocl_0 fpocl_4 wpo fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 fpocl_3 fpocl_4 wbr wa fpocl_1 fpocl_3 fpocl_4 wbr wi wa wi ipocl_0 ipocl_1 ipocl_2 fpocl_1 fpocl_2 fpocl_3 fpocl_0 fpocl_0 fpocl_0 ipocl_0 sup_set_class fpocl_1 wceq ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi wa fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class fpocl_1 wceq ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn fpocl_1 fpocl_1 fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi ipocl_0 sup_set_class fpocl_1 wceq ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr fpocl_1 fpocl_1 fpocl_4 wbr ipocl_0 sup_set_class fpocl_1 wceq ipocl_0 sup_set_class fpocl_1 ipocl_0 sup_set_class fpocl_1 fpocl_4 ipocl_0 sup_set_class fpocl_1 wceq id ipocl_0 sup_set_class fpocl_1 wceq id breq12d notbid ipocl_0 sup_set_class fpocl_1 wceq ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr ipocl_0 sup_set_class fpocl_1 wceq ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr ipocl_0 sup_set_class fpocl_1 ipocl_1 sup_set_class fpocl_4 breq1 anbi1d ipocl_0 sup_set_class fpocl_1 ipocl_2 sup_set_class fpocl_4 breq1 imbi12d anbi12d imbi2d ipocl_1 sup_set_class fpocl_2 wceq fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi wa fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi wa fpocl_0 fpocl_4 wpo ipocl_1 sup_set_class fpocl_2 wceq fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi fpocl_1 fpocl_1 fpocl_4 wbr wn ipocl_1 sup_set_class fpocl_2 wceq fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class fpocl_2 wceq fpocl_1 ipocl_1 sup_set_class fpocl_4 wbr fpocl_1 fpocl_2 fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class fpocl_2 fpocl_1 fpocl_4 breq2 ipocl_1 sup_set_class fpocl_2 ipocl_2 sup_set_class fpocl_4 breq1 anbi12d imbi1d anbi2d imbi2d ipocl_2 sup_set_class fpocl_3 wceq fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi wa fpocl_1 fpocl_1 fpocl_4 wbr wn fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 fpocl_3 fpocl_4 wbr wa fpocl_1 fpocl_3 fpocl_4 wbr wi wa fpocl_0 fpocl_4 wpo ipocl_2 sup_set_class fpocl_3 wceq fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr wi fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 fpocl_3 fpocl_4 wbr wa fpocl_1 fpocl_3 fpocl_4 wbr wi fpocl_1 fpocl_1 fpocl_4 wbr wn ipocl_2 sup_set_class fpocl_3 wceq fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr wa fpocl_1 fpocl_2 fpocl_4 wbr fpocl_2 fpocl_3 fpocl_4 wbr wa fpocl_1 ipocl_2 sup_set_class fpocl_4 wbr fpocl_1 fpocl_3 fpocl_4 wbr ipocl_2 sup_set_class fpocl_3 wceq fpocl_2 ipocl_2 sup_set_class fpocl_4 wbr fpocl_2 fpocl_3 fpocl_4 wbr fpocl_1 fpocl_2 fpocl_4 wbr ipocl_2 sup_set_class fpocl_3 fpocl_2 fpocl_4 breq2 anbi2d ipocl_2 sup_set_class fpocl_3 fpocl_1 fpocl_4 breq2 imbi12d anbi2d imbi2d fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class fpocl_0 wcel ipocl_1 sup_set_class fpocl_0 wcel ipocl_2 sup_set_class fpocl_0 wcel w3a ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class fpocl_0 wcel ipocl_1 sup_set_class fpocl_0 wcel ipocl_2 sup_set_class fpocl_0 wcel w3a ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa wi ipocl_2 fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class fpocl_0 wcel ipocl_1 sup_set_class fpocl_0 wcel ipocl_2 sup_set_class fpocl_0 wcel w3a ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa wi ipocl_2 wal ipocl_0 ipocl_1 fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class fpocl_0 wcel ipocl_1 sup_set_class fpocl_0 wcel ipocl_2 sup_set_class fpocl_0 wcel w3a ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa wi ipocl_2 wal ipocl_1 wal ipocl_0 wal fpocl_0 fpocl_4 wpo ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa ipocl_2 fpocl_0 wral ipocl_1 fpocl_0 wral ipocl_0 fpocl_0 wral ipocl_0 sup_set_class fpocl_0 wcel ipocl_1 sup_set_class fpocl_0 wcel ipocl_2 sup_set_class fpocl_0 wcel w3a ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa wi ipocl_2 wal ipocl_1 wal ipocl_0 wal ipocl_0 ipocl_1 ipocl_2 fpocl_0 fpocl_4 df-po ipocl_0 sup_set_class ipocl_0 sup_set_class fpocl_4 wbr wn ipocl_0 sup_set_class ipocl_1 sup_set_class fpocl_4 wbr ipocl_1 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wa ipocl_0 sup_set_class ipocl_2 sup_set_class fpocl_4 wbr wi wa ipocl_0 ipocl_1 ipocl_2 fpocl_0 fpocl_0 fpocl_0 r3al bitri biimpi 19.21bbi 19.21bi com12 vtocl3ga com12 $.
$}
$( /* Sufficient conditions for a partial order.  (Contributed by NM,
       9-Jul-2014.) */

$)
${
	$d x y z A $.
	$d x y z R $.
	$d x y z ph $.
	fispod_0 $f wff ph $.
	fispod_1 $f set x $.
	fispod_2 $f set y $.
	fispod_3 $f set z $.
	fispod_4 $f class A $.
	fispod_5 $f class R $.
	eispod_0 $e |- ( ( ph /\ x e. A ) -> -. x R x ) $.
	eispod_1 $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( ( x R y /\ y R z ) -> x R z ) ) $.
	ispod $p |- ( ph -> R Po A ) $= fispod_0 fispod_1 sup_set_class fispod_1 sup_set_class fispod_5 wbr wn fispod_1 sup_set_class fispod_2 sup_set_class fispod_5 wbr fispod_2 sup_set_class fispod_3 sup_set_class fispod_5 wbr wa fispod_1 sup_set_class fispod_3 sup_set_class fispod_5 wbr wi wa fispod_3 fispod_4 wral fispod_2 fispod_4 wral fispod_1 fispod_4 wral fispod_4 fispod_5 wpo fispod_0 fispod_1 sup_set_class fispod_1 sup_set_class fispod_5 wbr wn fispod_1 sup_set_class fispod_2 sup_set_class fispod_5 wbr fispod_2 sup_set_class fispod_3 sup_set_class fispod_5 wbr wa fispod_1 sup_set_class fispod_3 sup_set_class fispod_5 wbr wi wa fispod_1 fispod_2 fispod_3 fispod_4 fispod_4 fispod_4 fispod_0 fispod_1 sup_set_class fispod_4 wcel fispod_2 sup_set_class fispod_4 wcel fispod_3 sup_set_class fispod_4 wcel w3a wa fispod_1 sup_set_class fispod_1 sup_set_class fispod_5 wbr wn fispod_1 sup_set_class fispod_2 sup_set_class fispod_5 wbr fispod_2 sup_set_class fispod_3 sup_set_class fispod_5 wbr wa fispod_1 sup_set_class fispod_3 sup_set_class fispod_5 wbr wi fispod_0 fispod_2 sup_set_class fispod_4 wcel fispod_1 sup_set_class fispod_4 wcel fispod_1 sup_set_class fispod_1 sup_set_class fispod_5 wbr wn fispod_3 sup_set_class fispod_4 wcel eispod_0 3ad2antr1 eispod_1 jca ralrimivvva fispod_1 fispod_2 fispod_3 fispod_4 fispod_5 df-po sylibr $.
$}
$( /* Perform the substitutions into the strict weak ordering law.
       (Contributed by Mario Carneiro, 31-Dec-2014.) */

$)
${
	$d x y z A $.
	$d x y z ph $.
	$d x y z R $.
	$d x y z X $.
	$d y z Y $.
	$d z Z $.
	fswopolem_0 $f wff ph $.
	fswopolem_1 $f set x $.
	fswopolem_2 $f set y $.
	fswopolem_3 $f set z $.
	fswopolem_4 $f class A $.
	fswopolem_5 $f class R $.
	fswopolem_6 $f class X $.
	fswopolem_7 $f class Y $.
	fswopolem_8 $f class Z $.
	eswopolem_0 $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( x R y -> ( x R z \/ z R y ) ) ) $.
	swopolem $p |- ( ( ph /\ ( X e. A /\ Y e. A /\ Z e. A ) ) -> ( X R Y -> ( X R Z \/ Z R Y ) ) ) $= fswopolem_0 fswopolem_1 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_1 sup_set_class fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo wi fswopolem_3 fswopolem_4 wral fswopolem_2 fswopolem_4 wral fswopolem_1 fswopolem_4 wral fswopolem_6 fswopolem_4 wcel fswopolem_7 fswopolem_4 wcel fswopolem_8 fswopolem_4 wcel w3a fswopolem_6 fswopolem_7 fswopolem_5 wbr fswopolem_6 fswopolem_8 fswopolem_5 wbr fswopolem_8 fswopolem_7 fswopolem_5 wbr wo wi fswopolem_0 fswopolem_1 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_1 sup_set_class fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo wi fswopolem_1 fswopolem_2 fswopolem_3 fswopolem_4 fswopolem_4 fswopolem_4 eswopolem_0 ralrimivvva fswopolem_1 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_1 sup_set_class fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo wi fswopolem_6 fswopolem_7 fswopolem_5 wbr fswopolem_6 fswopolem_8 fswopolem_5 wbr fswopolem_8 fswopolem_7 fswopolem_5 wbr wo wi fswopolem_6 fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo wi fswopolem_6 fswopolem_7 fswopolem_5 wbr fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_7 fswopolem_5 wbr wo wi fswopolem_1 fswopolem_2 fswopolem_3 fswopolem_6 fswopolem_7 fswopolem_8 fswopolem_4 fswopolem_4 fswopolem_4 fswopolem_1 sup_set_class fswopolem_6 wceq fswopolem_1 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_6 fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_1 sup_set_class fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo fswopolem_1 sup_set_class fswopolem_6 fswopolem_2 sup_set_class fswopolem_5 breq1 fswopolem_1 sup_set_class fswopolem_6 wceq fswopolem_1 sup_set_class fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_1 sup_set_class fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 breq1 orbi1d imbi12d fswopolem_2 sup_set_class fswopolem_7 wceq fswopolem_6 fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_6 fswopolem_7 fswopolem_5 wbr fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr wo fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_7 fswopolem_5 wbr wo fswopolem_2 sup_set_class fswopolem_7 fswopolem_6 fswopolem_5 breq2 fswopolem_2 sup_set_class fswopolem_7 wceq fswopolem_3 sup_set_class fswopolem_2 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_7 fswopolem_5 wbr fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_2 sup_set_class fswopolem_7 fswopolem_3 sup_set_class fswopolem_5 breq2 orbi2d imbi12d fswopolem_3 sup_set_class fswopolem_8 wceq fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_7 fswopolem_5 wbr wo fswopolem_6 fswopolem_8 fswopolem_5 wbr fswopolem_8 fswopolem_7 fswopolem_5 wbr wo fswopolem_6 fswopolem_7 fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_8 wceq fswopolem_6 fswopolem_3 sup_set_class fswopolem_5 wbr fswopolem_6 fswopolem_8 fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_7 fswopolem_5 wbr fswopolem_8 fswopolem_7 fswopolem_5 wbr fswopolem_3 sup_set_class fswopolem_8 fswopolem_6 fswopolem_5 breq2 fswopolem_3 sup_set_class fswopolem_8 fswopolem_7 fswopolem_5 breq1 orbi12d imbi2d rspc3v mpan9 $.
$}
$( /* A strict weak order is a partial order.  (Contributed by Mario Carneiro,
       9-Jul-2014.) */

$)
${
	$d x y z A $.
	$d x y z R $.
	$d x y z ph $.
	fswopo_0 $f wff ph $.
	fswopo_1 $f set x $.
	fswopo_2 $f set y $.
	fswopo_3 $f set z $.
	fswopo_4 $f class A $.
	fswopo_5 $f class R $.
	eswopo_0 $e |- ( ( ph /\ ( y e. A /\ z e. A ) ) -> ( y R z -> -. z R y ) ) $.
	eswopo_1 $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( x R y -> ( x R z \/ z R y ) ) ) $.
	swopo $p |- ( ph -> R Po A ) $= fswopo_0 fswopo_1 fswopo_2 fswopo_3 fswopo_4 fswopo_5 fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel wa fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_4 wcel fswopo_1 sup_set_class fswopo_4 wcel fswopo_1 sup_set_class fswopo_4 wcel wa fswopo_2 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn wi fswopo_3 fswopo_4 wral fswopo_2 fswopo_4 wral fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr wn wi fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel fswopo_1 sup_set_class fswopo_4 wcel fswopo_1 sup_set_class fswopo_4 wcel id ancli fswopo_0 fswopo_2 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn wi fswopo_2 fswopo_3 fswopo_4 fswopo_4 eswopo_0 ralrimivva fswopo_2 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn wi fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr wn wi fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr wn wi fswopo_2 fswopo_3 fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_4 fswopo_4 fswopo_2 sup_set_class fswopo_1 sup_set_class wceq fswopo_2 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr wn fswopo_2 sup_set_class fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 breq1 fswopo_2 sup_set_class fswopo_1 sup_set_class wceq fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_2 sup_set_class fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 breq2 notbid imbi12d fswopo_3 sup_set_class fswopo_1 sup_set_class wceq fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr wn fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr wn fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 breq2 fswopo_3 sup_set_class fswopo_1 sup_set_class wceq fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_1 sup_set_class fswopo_1 sup_set_class fswopo_5 breq1 notbid imbi12d rspc2va syl2anr pm2.01d fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel fswopo_2 sup_set_class fswopo_4 wcel fswopo_3 sup_set_class fswopo_4 wcel w3a wa fswopo_2 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn fswopo_1 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_0 fswopo_2 sup_set_class fswopo_4 wcel fswopo_3 sup_set_class fswopo_4 wcel fswopo_2 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn wi fswopo_1 sup_set_class fswopo_4 wcel eswopo_0 3adantr1 fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel fswopo_2 sup_set_class fswopo_4 wcel fswopo_3 sup_set_class fswopo_4 wcel w3a wa fswopo_1 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wn fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel fswopo_2 sup_set_class fswopo_4 wcel fswopo_3 sup_set_class fswopo_4 wcel w3a wa fswopo_1 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wa fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel fswopo_2 sup_set_class fswopo_4 wcel fswopo_3 sup_set_class fswopo_4 wcel w3a wa fswopo_1 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wa fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr fswopo_0 fswopo_1 sup_set_class fswopo_4 wcel fswopo_2 sup_set_class fswopo_4 wcel fswopo_3 sup_set_class fswopo_4 wcel w3a wa fswopo_1 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr fswopo_1 sup_set_class fswopo_3 sup_set_class fswopo_5 wbr fswopo_3 sup_set_class fswopo_2 sup_set_class fswopo_5 wbr wo eswopo_1 imp orcomd ord expimpd sylan2d ispod $.
$}
$( /* A partial order relation is irreflexive.  (Contributed by NM,
     27-Mar-1997.) */

$)
${
	fpoirr_0 $f class A $.
	fpoirr_1 $f class B $.
	fpoirr_2 $f class R $.
	poirr $p |- ( ( R Po A /\ B e. A ) -> -. B R B ) $= fpoirr_1 fpoirr_0 wcel fpoirr_0 fpoirr_2 wpo fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel w3a fpoirr_1 fpoirr_1 fpoirr_2 wbr wn fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel w3a fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel wa fpoirr_1 fpoirr_0 wcel wa fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel wa fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel df-3an fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel anabs1 fpoirr_1 fpoirr_0 wcel anidm 3bitrri fpoirr_0 fpoirr_2 wpo fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel w3a wa fpoirr_1 fpoirr_1 fpoirr_2 wbr wn fpoirr_1 fpoirr_1 fpoirr_2 wbr fpoirr_1 fpoirr_1 fpoirr_2 wbr wa fpoirr_1 fpoirr_1 fpoirr_2 wbr wi fpoirr_0 fpoirr_2 wpo fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel fpoirr_1 fpoirr_0 wcel w3a fpoirr_1 fpoirr_1 fpoirr_2 wbr wn fpoirr_1 fpoirr_1 fpoirr_2 wbr fpoirr_1 fpoirr_1 fpoirr_2 wbr wa fpoirr_1 fpoirr_1 fpoirr_2 wbr wi wa fpoirr_0 fpoirr_1 fpoirr_1 fpoirr_1 fpoirr_2 pocl imp simpld sylan2b $.
$}
$( /* A partial order relation is a transitive relation.  (Contributed by NM,
     27-Mar-1997.) */

$)
${
	fpotr_0 $f class A $.
	fpotr_1 $f class B $.
	fpotr_2 $f class C $.
	fpotr_3 $f class D $.
	fpotr_4 $f class R $.
	potr $p |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( B R C /\ C R D ) -> B R D ) ) $= fpotr_0 fpotr_4 wpo fpotr_1 fpotr_0 wcel fpotr_2 fpotr_0 wcel fpotr_3 fpotr_0 wcel w3a wa fpotr_1 fpotr_1 fpotr_4 wbr wn fpotr_1 fpotr_2 fpotr_4 wbr fpotr_2 fpotr_3 fpotr_4 wbr wa fpotr_1 fpotr_3 fpotr_4 wbr wi fpotr_0 fpotr_4 wpo fpotr_1 fpotr_0 wcel fpotr_2 fpotr_0 wcel fpotr_3 fpotr_0 wcel w3a fpotr_1 fpotr_1 fpotr_4 wbr wn fpotr_1 fpotr_2 fpotr_4 wbr fpotr_2 fpotr_3 fpotr_4 wbr wa fpotr_1 fpotr_3 fpotr_4 wbr wi wa fpotr_0 fpotr_1 fpotr_2 fpotr_3 fpotr_4 pocl imp simprd $.
$}
$( /* A partial order relation has no 2-cycle loops.  (Contributed by NM,
     27-Mar-1997.) */

$)
${
	fpo2nr_0 $f class A $.
	fpo2nr_1 $f class B $.
	fpo2nr_2 $f class C $.
	fpo2nr_3 $f class R $.
	po2nr $p |- ( ( R Po A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) ) $= fpo2nr_0 fpo2nr_3 wpo fpo2nr_1 fpo2nr_0 wcel fpo2nr_2 fpo2nr_0 wcel wa wa fpo2nr_1 fpo2nr_2 fpo2nr_3 wbr fpo2nr_2 fpo2nr_1 fpo2nr_3 wbr wa fpo2nr_1 fpo2nr_1 fpo2nr_3 wbr fpo2nr_0 fpo2nr_3 wpo fpo2nr_1 fpo2nr_0 wcel fpo2nr_1 fpo2nr_1 fpo2nr_3 wbr wn fpo2nr_2 fpo2nr_0 wcel fpo2nr_0 fpo2nr_1 fpo2nr_3 poirr adantrr fpo2nr_0 fpo2nr_3 wpo fpo2nr_1 fpo2nr_0 wcel fpo2nr_2 fpo2nr_0 wcel fpo2nr_1 fpo2nr_2 fpo2nr_3 wbr fpo2nr_2 fpo2nr_1 fpo2nr_3 wbr wa fpo2nr_1 fpo2nr_1 fpo2nr_3 wbr wi fpo2nr_0 fpo2nr_3 wpo fpo2nr_1 fpo2nr_0 wcel fpo2nr_2 fpo2nr_0 wcel fpo2nr_1 fpo2nr_2 fpo2nr_3 wbr fpo2nr_2 fpo2nr_1 fpo2nr_3 wbr wa fpo2nr_1 fpo2nr_1 fpo2nr_3 wbr wi wi fpo2nr_0 fpo2nr_3 wpo fpo2nr_1 fpo2nr_0 wcel fpo2nr_2 fpo2nr_0 wcel fpo2nr_1 fpo2nr_0 wcel fpo2nr_1 fpo2nr_2 fpo2nr_3 wbr fpo2nr_2 fpo2nr_1 fpo2nr_3 wbr wa fpo2nr_1 fpo2nr_1 fpo2nr_3 wbr wi fpo2nr_0 fpo2nr_3 wpo fpo2nr_1 fpo2nr_0 wcel fpo2nr_2 fpo2nr_0 wcel fpo2nr_1 fpo2nr_0 wcel fpo2nr_1 fpo2nr_2 fpo2nr_3 wbr fpo2nr_2 fpo2nr_1 fpo2nr_3 wbr wa fpo2nr_1 fpo2nr_1 fpo2nr_3 wbr wi fpo2nr_0 fpo2nr_1 fpo2nr_2 fpo2nr_1 fpo2nr_3 potr 3exp2 com34 pm2.43d imp32 mtod $.
$}
$( /* A partial order relation has no 3-cycle loops.  (Contributed by NM,
     27-Mar-1997.) */

$)
${
	fpo3nr_0 $f class A $.
	fpo3nr_1 $f class B $.
	fpo3nr_2 $f class C $.
	fpo3nr_3 $f class D $.
	fpo3nr_4 $f class R $.
	po3nr $p |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) ) $= fpo3nr_0 fpo3nr_4 wpo fpo3nr_1 fpo3nr_0 wcel fpo3nr_2 fpo3nr_0 wcel fpo3nr_3 fpo3nr_0 wcel w3a wa fpo3nr_1 fpo3nr_2 fpo3nr_4 wbr fpo3nr_2 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr w3a fpo3nr_1 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr wa fpo3nr_0 fpo3nr_4 wpo fpo3nr_1 fpo3nr_0 wcel fpo3nr_3 fpo3nr_0 wcel fpo3nr_1 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr wa wn fpo3nr_2 fpo3nr_0 wcel fpo3nr_0 fpo3nr_1 fpo3nr_3 fpo3nr_4 po2nr 3adantr2 fpo3nr_1 fpo3nr_2 fpo3nr_4 wbr fpo3nr_2 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr w3a fpo3nr_1 fpo3nr_2 fpo3nr_4 wbr fpo3nr_2 fpo3nr_3 fpo3nr_4 wbr wa fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr wa fpo3nr_0 fpo3nr_4 wpo fpo3nr_1 fpo3nr_0 wcel fpo3nr_2 fpo3nr_0 wcel fpo3nr_3 fpo3nr_0 wcel w3a wa fpo3nr_1 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr wa fpo3nr_1 fpo3nr_2 fpo3nr_4 wbr fpo3nr_2 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr df-3an fpo3nr_0 fpo3nr_4 wpo fpo3nr_1 fpo3nr_0 wcel fpo3nr_2 fpo3nr_0 wcel fpo3nr_3 fpo3nr_0 wcel w3a wa fpo3nr_1 fpo3nr_2 fpo3nr_4 wbr fpo3nr_2 fpo3nr_3 fpo3nr_4 wbr wa fpo3nr_1 fpo3nr_3 fpo3nr_4 wbr fpo3nr_3 fpo3nr_1 fpo3nr_4 wbr fpo3nr_0 fpo3nr_1 fpo3nr_2 fpo3nr_3 fpo3nr_4 potr anim1d syl5bi mtod $.
$}
$( /* Any relation is a partial ordering of the empty set.  (Contributed by
       NM, 28-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) */

$)
${
	$d x y z R $.
	ipo0_0 $f set x $.
	ipo0_1 $f set y $.
	ipo0_2 $f set z $.
	fpo0_0 $f class R $.
	po0 $p |- R Po (/) $= c0 fpo0_0 wpo ipo0_0 sup_set_class ipo0_0 sup_set_class fpo0_0 wbr wn ipo0_0 sup_set_class ipo0_1 sup_set_class fpo0_0 wbr ipo0_1 sup_set_class ipo0_2 sup_set_class fpo0_0 wbr wa ipo0_0 sup_set_class ipo0_2 sup_set_class fpo0_0 wbr wi wa ipo0_2 c0 wral ipo0_1 c0 wral ipo0_0 c0 wral ipo0_0 sup_set_class ipo0_0 sup_set_class fpo0_0 wbr wn ipo0_0 sup_set_class ipo0_1 sup_set_class fpo0_0 wbr ipo0_1 sup_set_class ipo0_2 sup_set_class fpo0_0 wbr wa ipo0_0 sup_set_class ipo0_2 sup_set_class fpo0_0 wbr wi wa ipo0_2 c0 wral ipo0_1 c0 wral ipo0_0 ral0 ipo0_0 ipo0_1 ipo0_2 c0 fpo0_0 df-po mpbir $.
$}
$( /* A function preserves a partial order relation.  (Contributed by Jeff
       Madsen, 18-Jun-2011.) */

$)
${
	$d R v w x y z $.
	$d S v w z $.
	$d X v w y z $.
	$d Y x z $.
	$d A v w x z $.
	$d B v w x z $.
	ipofun_0 $f set z $.
	ipofun_1 $f set w $.
	ipofun_2 $f set v $.
	fpofun_0 $f set x $.
	fpofun_1 $f set y $.
	fpofun_2 $f class A $.
	fpofun_3 $f class B $.
	fpofun_4 $f class R $.
	fpofun_5 $f class S $.
	fpofun_6 $f class X $.
	fpofun_7 $f class Y $.
	epofun_0 $e |- S = { <. x , y >. | X R Y } $.
	epofun_1 $e |- ( x = y -> X = Y ) $.
	pofun $p |- ( ( R Po B /\ A. x e. A X e. B ) -> S Po A ) $= fpofun_3 fpofun_4 wpo fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral wa ipofun_2 ipofun_1 ipofun_0 fpofun_2 fpofun_5 fpofun_3 fpofun_4 wpo fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral ipofun_2 sup_set_class fpofun_2 wcel ipofun_2 sup_set_class ipofun_2 sup_set_class fpofun_5 wbr wn fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral ipofun_2 sup_set_class fpofun_2 wcel wa fpofun_3 fpofun_4 wpo fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel ipofun_2 sup_set_class ipofun_2 sup_set_class fpofun_5 wbr wn ipofun_2 sup_set_class fpofun_2 wcel fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_6 fpofun_3 wcel fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_2 sup_set_class fpofun_2 fpofun_0 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_2 sup_set_class fpofun_6 nfcsb1v nfel1 fpofun_0 sup_set_class ipofun_2 sup_set_class wceq fpofun_6 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_2 sup_set_class fpofun_6 csbeq1a eleq1d rspc impcom fpofun_3 fpofun_4 wpo fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel wa fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_2 sup_set_class ipofun_2 sup_set_class fpofun_5 wbr fpofun_3 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 poirr ipofun_2 sup_set_class ipofun_2 sup_set_class fpofun_5 wbr ipofun_2 sup_set_class ipofun_2 sup_set_class cop fpofun_5 wcel ipofun_2 sup_set_class ipofun_2 sup_set_class cop fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab wcel fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_2 sup_set_class ipofun_2 sup_set_class fpofun_5 df-br fpofun_5 fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab ipofun_2 sup_set_class ipofun_2 sup_set_class cop epofun_0 eleq2i fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_0 fpofun_1 ipofun_2 sup_set_class ipofun_2 sup_set_class fpofun_0 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_2 sup_set_class fpofun_6 nfcsb1v fpofun_0 fpofun_4 nfcv fpofun_0 fpofun_7 nfcv nfbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_1 nfv ipofun_2 vex ipofun_2 vex fpofun_0 sup_set_class ipofun_2 sup_set_class wceq fpofun_6 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_2 sup_set_class fpofun_6 csbeq1a breq1d fpofun_1 sup_set_class ipofun_2 sup_set_class wceq fpofun_7 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 fpofun_1 sup_set_class ipofun_2 sup_set_class wceq fpofun_7 fpofun_0 fpofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 fpofun_1 sup_set_class fpofun_6 fpofun_7 fpofun_1 vex fpofun_0 fpofun_7 nfcv epofun_1 csbief fpofun_0 fpofun_1 sup_set_class ipofun_2 sup_set_class fpofun_6 csbeq1 syl5eqr breq2d opelopabf 3bitri sylnibr sylan2 anassrs fpofun_3 fpofun_4 wpo fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral wa ipofun_2 sup_set_class fpofun_2 wcel ipofun_1 sup_set_class fpofun_2 wcel ipofun_0 sup_set_class fpofun_2 wcel w3a fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel w3a ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_5 wbr ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr wa ipofun_2 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr wi fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral ipofun_2 sup_set_class fpofun_2 wcel ipofun_1 sup_set_class fpofun_2 wcel ipofun_0 sup_set_class fpofun_2 wcel w3a fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel w3a fpofun_3 fpofun_4 wpo fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral ipofun_2 sup_set_class fpofun_2 wcel ipofun_1 sup_set_class fpofun_2 wcel ipofun_0 sup_set_class fpofun_2 wcel w3a fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel w3a fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral ipofun_2 sup_set_class fpofun_2 wcel fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel ipofun_1 sup_set_class fpofun_2 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel ipofun_0 sup_set_class fpofun_2 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel ipofun_2 sup_set_class fpofun_2 wcel fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_6 fpofun_3 wcel fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_2 sup_set_class fpofun_2 fpofun_0 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_2 sup_set_class fpofun_6 nfcsb1v nfel1 fpofun_0 sup_set_class ipofun_2 sup_set_class wceq fpofun_6 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_2 sup_set_class fpofun_6 csbeq1a eleq1d rspc com12 ipofun_1 sup_set_class fpofun_2 wcel fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_6 fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_2 fpofun_0 fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_1 sup_set_class fpofun_6 nfcsb1v nfel1 fpofun_0 sup_set_class ipofun_1 sup_set_class wceq fpofun_6 fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_1 sup_set_class fpofun_6 csbeq1a eleq1d rspc com12 ipofun_0 sup_set_class fpofun_2 wcel fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_6 fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_2 fpofun_0 fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_0 sup_set_class fpofun_6 nfcsb1v nfel1 fpofun_0 sup_set_class ipofun_0 sup_set_class wceq fpofun_6 fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 fpofun_0 ipofun_0 sup_set_class fpofun_6 csbeq1a eleq1d rspc com12 3anim123d imp adantll fpofun_3 fpofun_4 wpo fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel w3a ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_5 wbr ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr wa ipofun_2 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr wi fpofun_6 fpofun_3 wcel fpofun_0 fpofun_2 wral fpofun_3 fpofun_4 wpo fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_3 wcel fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_3 wcel w3a wa fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr wa fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_5 wbr ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr wa ipofun_2 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr fpofun_3 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 potr ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_5 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_5 wbr ipofun_2 sup_set_class ipofun_1 sup_set_class cop fpofun_5 wcel ipofun_2 sup_set_class ipofun_1 sup_set_class cop fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab wcel fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_5 df-br fpofun_5 fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab ipofun_2 sup_set_class ipofun_1 sup_set_class cop epofun_0 eleq2i fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_0 fpofun_1 ipofun_2 sup_set_class ipofun_1 sup_set_class fpofun_0 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_2 sup_set_class fpofun_6 nfcsb1v fpofun_0 fpofun_4 nfcv fpofun_0 fpofun_7 nfcv nfbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_1 nfv ipofun_2 vex ipofun_1 vex fpofun_0 sup_set_class ipofun_2 sup_set_class wceq fpofun_6 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_2 sup_set_class fpofun_6 csbeq1a breq1d fpofun_1 sup_set_class ipofun_1 sup_set_class wceq fpofun_7 fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 fpofun_1 sup_set_class ipofun_1 sup_set_class wceq fpofun_7 fpofun_0 fpofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 fpofun_1 sup_set_class fpofun_6 fpofun_7 fpofun_1 vex fpofun_0 fpofun_7 nfcv epofun_1 csbief fpofun_0 fpofun_1 sup_set_class ipofun_1 sup_set_class fpofun_6 csbeq1 syl5eqr breq2d opelopabf 3bitri ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr ipofun_1 sup_set_class ipofun_0 sup_set_class cop fpofun_5 wcel ipofun_1 sup_set_class ipofun_0 sup_set_class cop fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab wcel fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_5 df-br fpofun_5 fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab ipofun_1 sup_set_class ipofun_0 sup_set_class cop epofun_0 eleq2i fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 wbr fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_0 fpofun_1 ipofun_1 sup_set_class ipofun_0 sup_set_class fpofun_0 fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_1 sup_set_class fpofun_6 nfcsb1v fpofun_0 fpofun_4 nfcv fpofun_0 fpofun_7 nfcv nfbr fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_1 nfv ipofun_1 vex ipofun_0 vex fpofun_0 sup_set_class ipofun_1 sup_set_class wceq fpofun_6 fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_1 sup_set_class fpofun_6 csbeq1a breq1d fpofun_1 sup_set_class ipofun_0 sup_set_class wceq fpofun_7 fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_0 ipofun_1 sup_set_class fpofun_6 csb fpofun_4 fpofun_1 sup_set_class ipofun_0 sup_set_class wceq fpofun_7 fpofun_0 fpofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_0 fpofun_1 sup_set_class fpofun_6 fpofun_7 fpofun_1 vex fpofun_0 fpofun_7 nfcv epofun_1 csbief fpofun_0 fpofun_1 sup_set_class ipofun_0 sup_set_class fpofun_6 csbeq1 syl5eqr breq2d opelopabf 3bitri anbi12i ipofun_2 sup_set_class ipofun_0 sup_set_class fpofun_5 wbr ipofun_2 sup_set_class ipofun_0 sup_set_class cop fpofun_5 wcel ipofun_2 sup_set_class ipofun_0 sup_set_class cop fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab wcel fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr ipofun_2 sup_set_class ipofun_0 sup_set_class fpofun_5 df-br fpofun_5 fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 fpofun_1 copab ipofun_2 sup_set_class ipofun_0 sup_set_class cop epofun_0 eleq2i fpofun_6 fpofun_7 fpofun_4 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 wbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_0 fpofun_1 ipofun_2 sup_set_class ipofun_0 sup_set_class fpofun_0 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_2 sup_set_class fpofun_6 nfcsb1v fpofun_0 fpofun_4 nfcv fpofun_0 fpofun_7 nfcv nfbr fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_4 wbr fpofun_1 nfv ipofun_2 vex ipofun_0 vex fpofun_0 sup_set_class ipofun_2 sup_set_class wceq fpofun_6 fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_7 fpofun_4 fpofun_0 ipofun_2 sup_set_class fpofun_6 csbeq1a breq1d fpofun_1 sup_set_class ipofun_0 sup_set_class wceq fpofun_7 fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_0 ipofun_2 sup_set_class fpofun_6 csb fpofun_4 fpofun_1 sup_set_class ipofun_0 sup_set_class wceq fpofun_7 fpofun_0 fpofun_1 sup_set_class fpofun_6 csb fpofun_0 ipofun_0 sup_set_class fpofun_6 csb fpofun_0 fpofun_1 sup_set_class fpofun_6 fpofun_7 fpofun_1 vex fpofun_0 fpofun_7 nfcv epofun_1 csbief fpofun_0 fpofun_1 sup_set_class ipofun_0 sup_set_class fpofun_6 csbeq1 syl5eqr breq2d opelopabf 3bitri 3imtr4g adantlr syldan ispod $.
$}
$( /* A strict linear order is a strict partial order.  (Contributed by NM,
       28-Mar-1997.) */

$)
${
	$d x y R $.
	$d x y A $.
	isopo_0 $f set x $.
	isopo_1 $f set y $.
	fsopo_0 $f class A $.
	fsopo_1 $f class R $.
	sopo $p |- ( R Or A -> R Po A ) $= fsopo_0 fsopo_1 wor fsopo_0 fsopo_1 wpo isopo_0 sup_set_class isopo_1 sup_set_class fsopo_1 wbr isopo_0 sup_set_class isopo_1 sup_set_class wceq isopo_1 sup_set_class isopo_0 sup_set_class fsopo_1 wbr w3o isopo_1 fsopo_0 wral isopo_0 fsopo_0 wral isopo_0 isopo_1 fsopo_0 fsopo_1 df-so simplbi $.
$}
$( /* Subset theorem for the strict ordering predicate.  (Contributed by NM,
       16-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) */

$)
${
	$d x y R $.
	$d x y A $.
	$d x y B $.
	isoss_0 $f set x $.
	isoss_1 $f set y $.
	fsoss_0 $f class A $.
	fsoss_1 $f class B $.
	fsoss_2 $f class R $.
	soss $p |- ( A C_ B -> ( R Or B -> R Or A ) ) $= fsoss_0 fsoss_1 wss fsoss_1 fsoss_2 wpo isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_1 fsoss_1 wral isoss_0 fsoss_1 wral wa fsoss_0 fsoss_2 wpo isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_1 fsoss_0 wral isoss_0 fsoss_0 wral wa fsoss_1 fsoss_2 wor fsoss_0 fsoss_2 wor fsoss_0 fsoss_1 wss fsoss_1 fsoss_2 wpo fsoss_0 fsoss_2 wpo isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_1 fsoss_1 wral isoss_0 fsoss_1 wral isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_1 fsoss_0 wral isoss_0 fsoss_0 wral fsoss_0 fsoss_1 fsoss_2 poss fsoss_0 fsoss_1 wss isoss_0 sup_set_class fsoss_1 wcel isoss_1 sup_set_class fsoss_1 wcel wa isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o wi isoss_1 wal isoss_0 wal isoss_0 sup_set_class fsoss_0 wcel isoss_1 sup_set_class fsoss_0 wcel wa isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o wi isoss_1 wal isoss_0 wal isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_1 fsoss_1 wral isoss_0 fsoss_1 wral isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_1 fsoss_0 wral isoss_0 fsoss_0 wral fsoss_0 fsoss_1 wss isoss_0 sup_set_class fsoss_1 wcel isoss_1 sup_set_class fsoss_1 wcel wa isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o wi isoss_0 sup_set_class fsoss_0 wcel isoss_1 sup_set_class fsoss_0 wcel wa isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o wi isoss_0 isoss_1 fsoss_0 fsoss_1 wss isoss_0 sup_set_class fsoss_0 wcel isoss_1 sup_set_class fsoss_0 wcel wa isoss_0 sup_set_class fsoss_1 wcel isoss_1 sup_set_class fsoss_1 wcel wa isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o fsoss_0 fsoss_1 wss isoss_0 sup_set_class fsoss_0 wcel isoss_0 sup_set_class fsoss_1 wcel isoss_1 sup_set_class fsoss_0 wcel isoss_1 sup_set_class fsoss_1 wcel fsoss_0 fsoss_1 isoss_0 sup_set_class ssel fsoss_0 fsoss_1 isoss_1 sup_set_class ssel anim12d imim1d 2alimdv isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_0 isoss_1 fsoss_1 fsoss_1 r2al isoss_0 sup_set_class isoss_1 sup_set_class fsoss_2 wbr isoss_0 sup_set_class isoss_1 sup_set_class wceq isoss_1 sup_set_class isoss_0 sup_set_class fsoss_2 wbr w3o isoss_0 isoss_1 fsoss_0 fsoss_0 r2al 3imtr4g anim12d isoss_0 isoss_1 fsoss_1 fsoss_2 df-so isoss_0 isoss_1 fsoss_0 fsoss_2 df-so 3imtr4g $.
$}
$( /* Equality theorem for the strict ordering predicate.  (Contributed by NM,
       16-Mar-1997.) */

$)
${
	$d x y R $.
	$d x y S $.
	$d x y A $.
	isoeq1_0 $f set x $.
	isoeq1_1 $f set y $.
	fsoeq1_0 $f class A $.
	fsoeq1_1 $f class R $.
	fsoeq1_2 $f class S $.
	soeq1 $p |- ( R = S -> ( R Or A <-> S Or A ) ) $= fsoeq1_1 fsoeq1_2 wceq fsoeq1_0 fsoeq1_1 wpo isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_1 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_1 wbr w3o isoeq1_1 fsoeq1_0 wral isoeq1_0 fsoeq1_0 wral wa fsoeq1_0 fsoeq1_2 wpo isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_2 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_2 wbr w3o isoeq1_1 fsoeq1_0 wral isoeq1_0 fsoeq1_0 wral wa fsoeq1_0 fsoeq1_1 wor fsoeq1_0 fsoeq1_2 wor fsoeq1_1 fsoeq1_2 wceq fsoeq1_0 fsoeq1_1 wpo fsoeq1_0 fsoeq1_2 wpo isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_1 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_1 wbr w3o isoeq1_1 fsoeq1_0 wral isoeq1_0 fsoeq1_0 wral isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_2 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_2 wbr w3o isoeq1_1 fsoeq1_0 wral isoeq1_0 fsoeq1_0 wral fsoeq1_0 fsoeq1_1 fsoeq1_2 poeq1 fsoeq1_1 fsoeq1_2 wceq isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_1 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_1 wbr w3o isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_2 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_2 wbr w3o isoeq1_0 isoeq1_1 fsoeq1_0 fsoeq1_0 fsoeq1_1 fsoeq1_2 wceq isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_1 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_2 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_1 wbr isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_2 wbr isoeq1_0 sup_set_class isoeq1_1 sup_set_class fsoeq1_1 fsoeq1_2 breq fsoeq1_1 fsoeq1_2 wceq isoeq1_0 sup_set_class isoeq1_1 sup_set_class wceq biidd isoeq1_1 sup_set_class isoeq1_0 sup_set_class fsoeq1_1 fsoeq1_2 breq 3orbi123d 2ralbidv anbi12d isoeq1_0 isoeq1_1 fsoeq1_0 fsoeq1_1 df-so isoeq1_0 isoeq1_1 fsoeq1_0 fsoeq1_2 df-so 3bitr4g $.
$}
$( /* Equality theorem for the strict ordering predicate.  (Contributed by NM,
     16-Mar-1997.) */

$)
${
	fsoeq2_0 $f class A $.
	fsoeq2_1 $f class B $.
	fsoeq2_2 $f class R $.
	soeq2 $p |- ( A = B -> ( R Or A <-> R Or B ) ) $= fsoeq2_0 fsoeq2_1 wceq fsoeq2_1 fsoeq2_2 wor fsoeq2_0 fsoeq2_2 wor fsoeq2_0 fsoeq2_1 wss fsoeq2_1 fsoeq2_0 wss wa fsoeq2_1 fsoeq2_2 wor fsoeq2_0 fsoeq2_2 wor wi fsoeq2_0 fsoeq2_2 wor fsoeq2_1 fsoeq2_2 wor wi wa fsoeq2_0 fsoeq2_1 wceq fsoeq2_1 fsoeq2_2 wor fsoeq2_0 fsoeq2_2 wor wb fsoeq2_0 fsoeq2_1 wss fsoeq2_1 fsoeq2_2 wor fsoeq2_0 fsoeq2_2 wor wi fsoeq2_1 fsoeq2_0 wss fsoeq2_0 fsoeq2_2 wor fsoeq2_1 fsoeq2_2 wor wi fsoeq2_0 fsoeq2_1 fsoeq2_2 soss fsoeq2_1 fsoeq2_0 fsoeq2_2 soss anim12i fsoeq2_0 fsoeq2_1 eqss fsoeq2_1 fsoeq2_2 wor fsoeq2_0 fsoeq2_2 wor dfbi2 3imtr4i bicomd $.
$}
$( /* A strict order relation is irreflexive.  (Contributed by NM,
     24-Nov-1995.) */

$)
${
	fsonr_0 $f class A $.
	fsonr_1 $f class B $.
	fsonr_2 $f class R $.
	sonr $p |- ( ( R Or A /\ B e. A ) -> -. B R B ) $= fsonr_0 fsonr_2 wor fsonr_0 fsonr_2 wpo fsonr_1 fsonr_0 wcel fsonr_1 fsonr_1 fsonr_2 wbr wn fsonr_0 fsonr_2 sopo fsonr_0 fsonr_1 fsonr_2 poirr sylan $.
$}
$( /* A strict order relation is a transitive relation.  (Contributed by NM,
     21-Jan-1996.) */

$)
${
	fsotr_0 $f class A $.
	fsotr_1 $f class B $.
	fsotr_2 $f class C $.
	fsotr_3 $f class D $.
	fsotr_4 $f class R $.
	sotr $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( B R C /\ C R D ) -> B R D ) ) $= fsotr_0 fsotr_4 wor fsotr_0 fsotr_4 wpo fsotr_1 fsotr_0 wcel fsotr_2 fsotr_0 wcel fsotr_3 fsotr_0 wcel w3a fsotr_1 fsotr_2 fsotr_4 wbr fsotr_2 fsotr_3 fsotr_4 wbr wa fsotr_1 fsotr_3 fsotr_4 wbr wi fsotr_0 fsotr_4 sopo fsotr_0 fsotr_1 fsotr_2 fsotr_3 fsotr_4 potr sylan $.
$}
$( /* A strict order relation is linear (satisfies trichotomy).  (Contributed
       by NM, 21-Jan-1996.) */

$)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y R $.
	isolin_0 $f set x $.
	isolin_1 $f set y $.
	fsolin_0 $f class A $.
	fsolin_1 $f class B $.
	fsolin_2 $f class C $.
	fsolin_3 $f class R $.
	solin $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B R C \/ B = C \/ C R B ) ) $= fsolin_1 fsolin_0 wcel fsolin_2 fsolin_0 wcel wa fsolin_0 fsolin_3 wor fsolin_1 fsolin_2 fsolin_3 wbr fsolin_1 fsolin_2 wceq fsolin_2 fsolin_1 fsolin_3 wbr w3o fsolin_0 fsolin_3 wor isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o wi fsolin_0 fsolin_3 wor fsolin_1 isolin_1 sup_set_class fsolin_3 wbr fsolin_1 isolin_1 sup_set_class wceq isolin_1 sup_set_class fsolin_1 fsolin_3 wbr w3o wi fsolin_0 fsolin_3 wor fsolin_1 fsolin_2 fsolin_3 wbr fsolin_1 fsolin_2 wceq fsolin_2 fsolin_1 fsolin_3 wbr w3o wi isolin_0 isolin_1 fsolin_1 fsolin_2 fsolin_0 fsolin_0 isolin_0 sup_set_class fsolin_1 wceq isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o fsolin_1 isolin_1 sup_set_class fsolin_3 wbr fsolin_1 isolin_1 sup_set_class wceq isolin_1 sup_set_class fsolin_1 fsolin_3 wbr w3o fsolin_0 fsolin_3 wor isolin_0 sup_set_class fsolin_1 wceq isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr fsolin_1 isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq fsolin_1 isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr isolin_1 sup_set_class fsolin_1 fsolin_3 wbr isolin_0 sup_set_class fsolin_1 isolin_1 sup_set_class fsolin_3 breq1 isolin_0 sup_set_class fsolin_1 isolin_1 sup_set_class eqeq1 isolin_0 sup_set_class fsolin_1 isolin_1 sup_set_class fsolin_3 breq2 3orbi123d imbi2d isolin_1 sup_set_class fsolin_2 wceq fsolin_1 isolin_1 sup_set_class fsolin_3 wbr fsolin_1 isolin_1 sup_set_class wceq isolin_1 sup_set_class fsolin_1 fsolin_3 wbr w3o fsolin_1 fsolin_2 fsolin_3 wbr fsolin_1 fsolin_2 wceq fsolin_2 fsolin_1 fsolin_3 wbr w3o fsolin_0 fsolin_3 wor isolin_1 sup_set_class fsolin_2 wceq fsolin_1 isolin_1 sup_set_class fsolin_3 wbr fsolin_1 fsolin_2 fsolin_3 wbr fsolin_1 isolin_1 sup_set_class wceq fsolin_1 fsolin_2 wceq isolin_1 sup_set_class fsolin_1 fsolin_3 wbr fsolin_2 fsolin_1 fsolin_3 wbr isolin_1 sup_set_class fsolin_2 fsolin_1 fsolin_3 breq2 isolin_1 sup_set_class fsolin_2 fsolin_1 eqeq2 isolin_1 sup_set_class fsolin_2 fsolin_1 fsolin_3 breq1 3orbi123d imbi2d fsolin_0 fsolin_3 wor isolin_0 sup_set_class fsolin_0 wcel isolin_1 sup_set_class fsolin_0 wcel wa isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o fsolin_0 fsolin_3 wor fsolin_0 fsolin_3 wpo isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o isolin_1 fsolin_0 wral isolin_0 fsolin_0 wral wa isolin_0 sup_set_class fsolin_0 wcel isolin_1 sup_set_class fsolin_0 wcel wa isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o wi isolin_0 isolin_1 fsolin_0 fsolin_3 df-so isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o isolin_1 fsolin_0 wral isolin_0 fsolin_0 wral isolin_0 sup_set_class fsolin_0 wcel isolin_1 sup_set_class fsolin_0 wcel wa isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o wi fsolin_0 fsolin_3 wpo isolin_0 sup_set_class isolin_1 sup_set_class fsolin_3 wbr isolin_0 sup_set_class isolin_1 sup_set_class wceq isolin_1 sup_set_class isolin_0 sup_set_class fsolin_3 wbr w3o isolin_0 isolin_1 fsolin_0 fsolin_0 rsp2 adantl sylbi com12 vtocl2ga impcom $.
$}
$( /* A strict order relation has no 2-cycle loops.  (Contributed by NM,
     21-Jan-1996.) */

$)
${
	fso2nr_0 $f class A $.
	fso2nr_1 $f class B $.
	fso2nr_2 $f class C $.
	fso2nr_3 $f class R $.
	so2nr $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) ) $= fso2nr_0 fso2nr_3 wor fso2nr_0 fso2nr_3 wpo fso2nr_1 fso2nr_0 wcel fso2nr_2 fso2nr_0 wcel wa fso2nr_1 fso2nr_2 fso2nr_3 wbr fso2nr_2 fso2nr_1 fso2nr_3 wbr wa wn fso2nr_0 fso2nr_3 sopo fso2nr_0 fso2nr_1 fso2nr_2 fso2nr_3 po2nr sylan $.
$}
$( /* A strict order relation has no 3-cycle loops.  (Contributed by NM,
     21-Jan-1996.) */

$)
${
	fso3nr_0 $f class A $.
	fso3nr_1 $f class B $.
	fso3nr_2 $f class C $.
	fso3nr_3 $f class D $.
	fso3nr_4 $f class R $.
	so3nr $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) ) $= fso3nr_0 fso3nr_4 wor fso3nr_0 fso3nr_4 wpo fso3nr_1 fso3nr_0 wcel fso3nr_2 fso3nr_0 wcel fso3nr_3 fso3nr_0 wcel w3a fso3nr_1 fso3nr_2 fso3nr_4 wbr fso3nr_2 fso3nr_3 fso3nr_4 wbr fso3nr_3 fso3nr_1 fso3nr_4 wbr w3a wn fso3nr_0 fso3nr_4 sopo fso3nr_0 fso3nr_1 fso3nr_2 fso3nr_3 fso3nr_4 po3nr sylan $.
$}
$( /* A strict order relation satisfies strict trichotomy.  (Contributed by NM,
     19-Feb-1996.) */

$)
${
	fsotric_0 $f class A $.
	fsotric_1 $f class B $.
	fsotric_2 $f class C $.
	fsotric_3 $f class R $.
	sotric $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B R C <-> -. ( B = C \/ C R B ) ) ) $= fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_2 fsotric_0 wcel wa wa fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr wo fsotric_1 fsotric_2 fsotric_3 wbr fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_2 fsotric_0 wcel wa wa fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr wo fsotric_1 fsotric_2 fsotric_3 wbr wn fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_2 fsotric_0 wcel wa wa fsotric_1 fsotric_2 wceq fsotric_1 fsotric_2 fsotric_3 wbr wn fsotric_2 fsotric_1 fsotric_3 wbr fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_1 fsotric_2 wceq fsotric_1 fsotric_2 fsotric_3 wbr wn wi fsotric_2 fsotric_0 wcel fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel wa fsotric_1 fsotric_1 fsotric_3 wbr wn fsotric_1 fsotric_2 wceq fsotric_1 fsotric_2 fsotric_3 wbr wn fsotric_0 fsotric_1 fsotric_3 sonr fsotric_1 fsotric_2 wceq fsotric_1 fsotric_1 fsotric_3 wbr fsotric_1 fsotric_2 fsotric_3 wbr fsotric_1 fsotric_2 fsotric_1 fsotric_3 breq2 notbid syl5ibcom adantrr fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_2 fsotric_0 wcel wa wa fsotric_1 fsotric_2 fsotric_3 wbr fsotric_2 fsotric_1 fsotric_3 wbr fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_2 fsotric_0 wcel wa wa fsotric_1 fsotric_2 fsotric_3 wbr fsotric_2 fsotric_1 fsotric_3 wbr wa wn fsotric_1 fsotric_2 fsotric_3 wbr fsotric_2 fsotric_1 fsotric_3 wbr wn wi fsotric_0 fsotric_1 fsotric_2 fsotric_3 so2nr fsotric_1 fsotric_2 fsotric_3 wbr fsotric_2 fsotric_1 fsotric_3 wbr imnan sylibr con2d jaod fsotric_0 fsotric_3 wor fsotric_1 fsotric_0 wcel fsotric_2 fsotric_0 wcel wa wa fsotric_1 fsotric_2 fsotric_3 wbr fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr w3o fsotric_1 fsotric_2 fsotric_3 wbr wn fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr wo wi fsotric_0 fsotric_1 fsotric_2 fsotric_3 solin fsotric_1 fsotric_2 fsotric_3 wbr fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr w3o fsotric_1 fsotric_2 fsotric_3 wbr fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr wo wo fsotric_1 fsotric_2 fsotric_3 wbr wn fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr wo wi fsotric_1 fsotric_2 fsotric_3 wbr fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr 3orass fsotric_1 fsotric_2 fsotric_3 wbr fsotric_1 fsotric_2 wceq fsotric_2 fsotric_1 fsotric_3 wbr wo df-or bitri sylib impbid con2bid $.
$}
$( /* Trichotomy law for strict order relation.  (Contributed by NM,
     9-Apr-1996.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) */

$)
${
	fsotrieq_0 $f class A $.
	fsotrieq_1 $f class B $.
	fsotrieq_2 $f class C $.
	fsotrieq_3 $f class R $.
	sotrieq $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B = C <-> -. ( B R C \/ C R B ) ) ) $= fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_2 fsotrieq_0 wcel wa wa fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo fsotrieq_1 fsotrieq_2 wceq fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_2 fsotrieq_0 wcel wa wa fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo fsotrieq_1 fsotrieq_2 wceq wn fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_2 fsotrieq_0 wcel wa wa fsotrieq_1 fsotrieq_2 wceq fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_2 fsotrieq_0 wcel wa wa fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr wo wn fsotrieq_1 fsotrieq_2 wceq fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo wn fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_2 fsotrieq_0 wcel wa wa fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr wo fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr wn fsotrieq_2 fsotrieq_0 wcel fsotrieq_0 fsotrieq_1 fsotrieq_3 sonr adantrr fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr pm1.2 nsyl fsotrieq_1 fsotrieq_2 wceq fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr wo fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo fsotrieq_1 fsotrieq_2 wceq fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_1 fsotrieq_1 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 fsotrieq_1 fsotrieq_3 breq2 fsotrieq_1 fsotrieq_2 fsotrieq_1 fsotrieq_3 breq1 orbi12d notbid syl5ibcom con2d fsotrieq_0 fsotrieq_3 wor fsotrieq_1 fsotrieq_0 wcel fsotrieq_2 fsotrieq_0 wcel wa wa fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 wceq fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr w3o fsotrieq_1 fsotrieq_2 wceq wn fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo wi fsotrieq_0 fsotrieq_1 fsotrieq_2 fsotrieq_3 solin fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 wceq fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr w3o fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 wceq fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo wo fsotrieq_1 fsotrieq_2 wceq fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo wo fsotrieq_1 fsotrieq_2 wceq wn fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo wi fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 wceq fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr 3orass fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_1 fsotrieq_2 wceq fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr or12 fsotrieq_1 fsotrieq_2 wceq fsotrieq_1 fsotrieq_2 fsotrieq_3 wbr fsotrieq_2 fsotrieq_1 fsotrieq_3 wbr wo df-or 3bitri sylib impbid con2bid $.
$}
$( /* Trichotomy law for strict order relation.  (Contributed by NM,
     5-May-1999.) */

$)
${
	fsotrieq2_0 $f class A $.
	fsotrieq2_1 $f class B $.
	fsotrieq2_2 $f class C $.
	fsotrieq2_3 $f class R $.
	sotrieq2 $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B = C <-> ( -. B R C /\ -. C R B ) ) ) $= fsotrieq2_0 fsotrieq2_3 wor fsotrieq2_1 fsotrieq2_0 wcel fsotrieq2_2 fsotrieq2_0 wcel wa wa fsotrieq2_1 fsotrieq2_2 wceq fsotrieq2_1 fsotrieq2_2 fsotrieq2_3 wbr fsotrieq2_2 fsotrieq2_1 fsotrieq2_3 wbr wo wn fsotrieq2_1 fsotrieq2_2 fsotrieq2_3 wbr wn fsotrieq2_2 fsotrieq2_1 fsotrieq2_3 wbr wn wa fsotrieq2_0 fsotrieq2_1 fsotrieq2_2 fsotrieq2_3 sotrieq fsotrieq2_1 fsotrieq2_2 fsotrieq2_3 wbr fsotrieq2_2 fsotrieq2_1 fsotrieq2_3 wbr ioran syl6bb $.
$}
$( /* A transitivity relation.  (Read ` B <_ C ` and ` C < D ` implies
     ` B < D ` .)  (Contributed by Mario Carneiro, 10-May-2013.) */

$)
${
	fsotr2_0 $f class A $.
	fsotr2_1 $f class B $.
	fsotr2_2 $f class C $.
	fsotr2_3 $f class D $.
	fsotr2_4 $f class R $.
	sotr2 $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( -. C R B /\ C R D ) -> B R D ) ) $= fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_3 fsotr2_0 wcel w3a wa fsotr2_2 fsotr2_1 fsotr2_4 wbr wn fsotr2_2 fsotr2_3 fsotr2_4 wbr fsotr2_1 fsotr2_3 fsotr2_4 wbr fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_3 fsotr2_0 wcel w3a wa fsotr2_2 fsotr2_1 fsotr2_4 wbr wn fsotr2_2 fsotr2_1 wceq fsotr2_1 fsotr2_2 fsotr2_4 wbr wo fsotr2_2 fsotr2_3 fsotr2_4 wbr fsotr2_1 fsotr2_3 fsotr2_4 wbr wi fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_3 fsotr2_0 wcel w3a wa fsotr2_2 fsotr2_1 fsotr2_4 wbr fsotr2_2 fsotr2_1 wceq fsotr2_1 fsotr2_2 fsotr2_4 wbr wo fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_2 fsotr2_1 fsotr2_4 wbr fsotr2_2 fsotr2_1 wceq fsotr2_1 fsotr2_2 fsotr2_4 wbr wo wn wb fsotr2_3 fsotr2_0 wcel fsotr2_0 fsotr2_4 wor fsotr2_2 fsotr2_0 wcel fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_1 fsotr2_4 wbr fsotr2_2 fsotr2_1 wceq fsotr2_1 fsotr2_2 fsotr2_4 wbr wo wn wb fsotr2_0 fsotr2_2 fsotr2_1 fsotr2_4 sotric ancom2s 3adantr3 con2bid fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_3 fsotr2_0 wcel w3a wa fsotr2_2 fsotr2_1 wceq fsotr2_2 fsotr2_3 fsotr2_4 wbr fsotr2_1 fsotr2_3 fsotr2_4 wbr wi fsotr2_1 fsotr2_2 fsotr2_4 wbr fsotr2_2 fsotr2_1 wceq fsotr2_2 fsotr2_3 fsotr2_4 wbr fsotr2_1 fsotr2_3 fsotr2_4 wbr wi wi fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_3 fsotr2_0 wcel w3a wa fsotr2_2 fsotr2_1 wceq fsotr2_2 fsotr2_3 fsotr2_4 wbr fsotr2_1 fsotr2_3 fsotr2_4 wbr fsotr2_2 fsotr2_1 fsotr2_3 fsotr2_4 breq1 biimpd a1i fsotr2_0 fsotr2_4 wor fsotr2_1 fsotr2_0 wcel fsotr2_2 fsotr2_0 wcel fsotr2_3 fsotr2_0 wcel w3a wa fsotr2_1 fsotr2_2 fsotr2_4 wbr fsotr2_2 fsotr2_3 fsotr2_4 wbr fsotr2_1 fsotr2_3 fsotr2_4 wbr fsotr2_0 fsotr2_1 fsotr2_2 fsotr2_3 fsotr2_4 sotr exp3a jaod sylbird imp3a $.
$}
$( /* An irreflexive, transitive, linear relation is a strict ordering.
       (Contributed by NM, 21-Jan-1996.)  (Revised by Mario Carneiro,
       9-Jul-2014.) */

$)
${
	$d x y R $.
	$d x y A $.
	$d x y ph $.
	fissod_0 $f wff ph $.
	fissod_1 $f set x $.
	fissod_2 $f set y $.
	fissod_3 $f class A $.
	fissod_4 $f class R $.
	eissod_0 $e |- ( ph -> R Po A ) $.
	eissod_1 $e |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x R y \/ x = y \/ y R x ) ) $.
	issod $p |- ( ph -> R Or A ) $= fissod_0 fissod_3 fissod_4 wpo fissod_1 sup_set_class fissod_2 sup_set_class fissod_4 wbr fissod_1 sup_set_class fissod_2 sup_set_class wceq fissod_2 sup_set_class fissod_1 sup_set_class fissod_4 wbr w3o fissod_2 fissod_3 wral fissod_1 fissod_3 wral fissod_3 fissod_4 wor eissod_0 fissod_0 fissod_1 sup_set_class fissod_2 sup_set_class fissod_4 wbr fissod_1 sup_set_class fissod_2 sup_set_class wceq fissod_2 sup_set_class fissod_1 sup_set_class fissod_4 wbr w3o fissod_1 fissod_2 fissod_3 fissod_3 eissod_1 ralrimivva fissod_1 fissod_2 fissod_3 fissod_4 df-so sylanbrc $.
$}
$( /* An irreflexive, transitive, linear relation is a strict ordering.
       (Contributed by NM, 21-Jan-1996.)  (Revised by Mario Carneiro,
       9-Jul-2014.) */

$)
${
	$d x y z R $.
	$d x y z A $.
	fissoi_0 $f set x $.
	fissoi_1 $f set y $.
	fissoi_2 $f set z $.
	fissoi_3 $f class A $.
	fissoi_4 $f class R $.
	eissoi_0 $e |- ( x e. A -> -. x R x ) $.
	eissoi_1 $e |- ( ( x e. A /\ y e. A /\ z e. A ) -> ( ( x R y /\ y R z ) -> x R z ) ) $.
	eissoi_2 $e |- ( ( x e. A /\ y e. A ) -> ( x R y \/ x = y \/ y R x ) ) $.
	issoi $p |- R Or A $= fissoi_3 fissoi_4 wor wtru fissoi_0 fissoi_1 fissoi_3 fissoi_4 wtru fissoi_0 fissoi_1 fissoi_2 fissoi_3 fissoi_4 fissoi_0 sup_set_class fissoi_3 wcel fissoi_0 sup_set_class fissoi_0 sup_set_class fissoi_4 wbr wn wtru eissoi_0 adantl fissoi_0 sup_set_class fissoi_3 wcel fissoi_1 sup_set_class fissoi_3 wcel fissoi_2 sup_set_class fissoi_3 wcel w3a fissoi_0 sup_set_class fissoi_1 sup_set_class fissoi_4 wbr fissoi_1 sup_set_class fissoi_2 sup_set_class fissoi_4 wbr wa fissoi_0 sup_set_class fissoi_2 sup_set_class fissoi_4 wbr wi wtru eissoi_1 adantl ispod fissoi_0 sup_set_class fissoi_3 wcel fissoi_1 sup_set_class fissoi_3 wcel wa fissoi_0 sup_set_class fissoi_1 sup_set_class fissoi_4 wbr fissoi_0 sup_set_class fissoi_1 sup_set_class wceq fissoi_1 sup_set_class fissoi_0 sup_set_class fissoi_4 wbr w3o wtru eissoi_2 adantl issod trud $.
$}
$( /* Deduce strict ordering from its properties.  (Contributed by NM,
       29-Jan-1996.)  (Revised by Mario Carneiro, 9-Jul-2014.) */

$)
${
	$d x y z R $.
	$d x y z A $.
	fisso2i_0 $f set x $.
	fisso2i_1 $f set y $.
	fisso2i_2 $f set z $.
	fisso2i_3 $f class A $.
	fisso2i_4 $f class R $.
	eisso2i_0 $e |- ( ( x e. A /\ y e. A ) -> ( x R y <-> -. ( x = y \/ y R x ) ) ) $.
	eisso2i_1 $e |- ( ( x e. A /\ y e. A /\ z e. A ) -> ( ( x R y /\ y R z ) -> x R z ) ) $.
	isso2i $p |- R Or A $= fisso2i_0 fisso2i_1 fisso2i_2 fisso2i_3 fisso2i_4 fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wn fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_0 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wn fisso2i_0 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class eqid orci fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr wn wb wi fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_0 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wn wb wi fisso2i_1 fisso2i_0 fisso2i_1 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_0 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr wn wb fisso2i_0 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wn wb fisso2i_1 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_3 wcel fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_3 eleq1 anbi2d fisso2i_1 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr wn fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wn fisso2i_1 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_0 sup_set_class eqeq2 fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 breq1 orbi12d fisso2i_1 sup_set_class fisso2i_0 sup_set_class wceq fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_0 sup_set_class fisso2i_4 breq2 notbid bibi12d imbi12d fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo eisso2i_0 con2bid chvarv mpbii anidms eisso2i_1 fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr wn fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo wi fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr w3o fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr wn fisso2i_0 sup_set_class fisso2i_3 wcel fisso2i_1 sup_set_class fisso2i_3 wcel wa fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo eisso2i_0 con2bid biimprd fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr w3o fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo wo fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr wn fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo wi fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr 3orass fisso2i_0 sup_set_class fisso2i_1 sup_set_class fisso2i_4 wbr fisso2i_0 sup_set_class fisso2i_1 sup_set_class wceq fisso2i_1 sup_set_class fisso2i_0 sup_set_class fisso2i_4 wbr wo df-or bitri sylibr issoi $.
$}
$( /* Any relation is a strict ordering of the empty set.  (Contributed by NM,
       16-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) */

$)
${
	$d x y R $.
	iso0_0 $f set x $.
	iso0_1 $f set y $.
	fso0_0 $f class R $.
	so0 $p |- R Or (/) $= c0 fso0_0 wor c0 fso0_0 wpo iso0_0 sup_set_class iso0_1 sup_set_class fso0_0 wbr iso0_0 sup_set_class iso0_1 sup_set_class wceq iso0_1 sup_set_class iso0_0 sup_set_class fso0_0 wbr w3o iso0_1 c0 wral iso0_0 c0 wral fso0_0 po0 iso0_0 sup_set_class iso0_1 sup_set_class fso0_0 wbr iso0_0 sup_set_class iso0_1 sup_set_class wceq iso0_1 sup_set_class iso0_0 sup_set_class fso0_0 wbr w3o iso0_1 c0 wral iso0_0 ral0 iso0_0 iso0_1 c0 fso0_0 df-so mpbir2an $.
$}
$( /* A totally ordered set has at most one minimal element.  (Contributed by
       Mario Carneiro, 24-Jun-2015.)  (Revised by NM, 16-Jun-2017.) */

$)
${
	$d x y z A $.
	$d x y z R $.
	isomo_0 $f set z $.
	fsomo_0 $f set x $.
	fsomo_1 $f set y $.
	fsomo_2 $f class A $.
	fsomo_3 $f class R $.
	somo $p |- ( R Or A -> E* x e. A A. y e. A -. y R x ) $= fsomo_2 fsomo_3 wor fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral wa fsomo_0 sup_set_class isomo_0 sup_set_class wceq wi isomo_0 fsomo_2 wral fsomo_0 fsomo_2 wral fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_0 fsomo_2 wrmo fsomo_2 fsomo_3 wor fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral wa fsomo_0 sup_set_class isomo_0 sup_set_class wceq wi fsomo_0 isomo_0 fsomo_2 fsomo_2 fsomo_2 fsomo_3 wor fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral wa fsomo_0 sup_set_class isomo_0 sup_set_class wceq wi fsomo_2 fsomo_3 wor fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral wa fsomo_0 sup_set_class isomo_0 sup_set_class wceq fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral wa wa fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn wa fsomo_2 fsomo_3 wor fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa wa fsomo_0 sup_set_class isomo_0 sup_set_class wceq fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral wa fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn wa fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn wa fsomo_0 sup_set_class fsomo_2 wcel fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn isomo_0 sup_set_class fsomo_2 wcel fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_0 sup_set_class fsomo_2 fsomo_1 sup_set_class fsomo_0 sup_set_class wceq fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_1 sup_set_class fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 breq1 notbid rspcv fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 isomo_0 sup_set_class fsomo_2 fsomo_1 sup_set_class isomo_0 sup_set_class wceq fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 breq1 notbid rspcv im2anan9 ancomsd imp fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn wa fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wo wn fsomo_2 fsomo_3 wor fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa wa fsomo_0 sup_set_class isomo_0 sup_set_class wceq fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr ioran fsomo_2 fsomo_3 wor fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa wa fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wo fsomo_0 sup_set_class isomo_0 sup_set_class wceq fsomo_2 fsomo_3 wor fsomo_0 sup_set_class fsomo_2 wcel isomo_0 sup_set_class fsomo_2 wcel wa wa fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class wceq isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr w3o fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wo fsomo_0 sup_set_class isomo_0 sup_set_class wceq wo fsomo_2 fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 solin fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class wceq isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr w3o fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class wceq wo isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wo fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wo fsomo_0 sup_set_class isomo_0 sup_set_class wceq wo fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class wceq isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr df-3or fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class wceq isomo_0 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr or32 bitri sylib ord syl5bir syl5 exp4b pm2.43d ralrimivv fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 wral fsomo_0 isomo_0 fsomo_2 fsomo_0 sup_set_class isomo_0 sup_set_class wceq fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr wn fsomo_1 fsomo_2 fsomo_0 sup_set_class isomo_0 sup_set_class wceq fsomo_1 sup_set_class fsomo_0 sup_set_class fsomo_3 wbr fsomo_1 sup_set_class isomo_0 sup_set_class fsomo_3 wbr fsomo_0 sup_set_class isomo_0 sup_set_class fsomo_1 sup_set_class fsomo_3 breq2 notbid ralbidv rmo4 sylibr $.
$}

