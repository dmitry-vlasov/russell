$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Epsilon_and_identity_relations.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Partial and complete ordering

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(We have not yet defined relations ( ~ df-rel ), but here we introduce a
few related notions we will use to develop ordinals.  The class variable
` R ` is no different from other class variables, but it reminds us that
normally it represents what we will later call a "relation."
$)

$(Declare new constant symbols. $)

$c Po $.

$(Partial ordering predicate symbol (read: 'partial ordering'). $)

$c Or $.

$(Strict complete ordering predicate symbol (read: 'orders'). $)

$(Extend wff notation to include the strict partial ordering predicate.
     Read:  ' ` R ` is a partial order on ` A ` .' $)

${
	$v A R  $.
	f0_wpo $f class A $.
	f1_wpo $f class R $.
	a_wpo $a wff R Po A $.
$}

$(Extend wff notation to include the strict complete ordering predicate.
     Read:  ' ` R ` orders ` A ` .' $)

${
	$v A R  $.
	f0_wor $f class A $.
	f1_wor $f class R $.
	a_wor $a wff R Or A $.
$}

$(Define the strict partial order predicate.  Definition of [Enderton]
       p. 168.  The expression ` R Po A ` means ` R ` is a partial order on
       ` A ` .  For example, ` < Po RR ` is true, while ` <_ Po RR ` is false
       ( ~ ex-po ).  (Contributed by NM, 16-Mar-1997.) $)

${
	$v x y z A R  $.
	$d x y z R  $.
	$d x y z A  $.
	f0_df-po $f set x $.
	f1_df-po $f set y $.
	f2_df-po $f set z $.
	f3_df-po $f class A $.
	f4_df-po $f class R $.
	a_df-po $a |- ( R Po A <-> A. x e. A A. y e. A A. z e. A ( -. x R x /\ ( ( x R y /\ y R z ) -> x R z ) ) ) $.
$}

$(Define the strict complete (linear) order predicate.  The expression
       ` R Or A ` is true if relationship ` R ` orders ` A ` .  For example,
       ` < Or RR ` is true ( ~ ltso ).  Equivalent to Definition 6.19(1) of
       [TakeutiZaring] p. 29.  (Contributed by NM, 21-Jan-1996.) $)

${
	$v x y A R  $.
	$d x y R  $.
	$d x y A  $.
	f0_df-so $f set x $.
	f1_df-so $f set y $.
	f2_df-so $f class A $.
	f3_df-so $f class R $.
	a_df-so $a |- ( R Or A <-> ( R Po A /\ A. x e. A A. y e. A ( x R y \/ x = y \/ y R x ) ) ) $.
$}

$(Subset theorem for the partial ordering predicate.  (Contributed by NM,
       27-Mar-1997.)  (Proof shortened by Mario Carneiro, 18-Nov-2016.) $)

${
	$v A B R  $.
	$d x y z R  $.
	$d x y z A  $.
	$d x y z B  $.
	f0_poss $f class A $.
	f1_poss $f class B $.
	f2_poss $f class R $.
	i0_poss $f set x $.
	i1_poss $f set y $.
	i2_poss $f set z $.
	p_poss $p |- ( A C_ B -> ( R Po B -> R Po A ) ) $= i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f1_poss a_wral i0_poss f0_poss f1_poss p_ssralv i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f0_poss f1_poss p_ssralv i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f0_poss f1_poss p_ssralv f0_poss f1_poss a_wss i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f0_poss a_wral i1_poss f0_poss p_ralimdv f0_poss f1_poss a_wss i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f1_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f0_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f0_poss a_wral i1_poss f0_poss a_wral p_syld f0_poss f1_poss a_wss i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f1_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f0_poss a_wral i1_poss f0_poss a_wral i0_poss f0_poss p_ralimdv f0_poss f1_poss a_wss i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f1_poss a_wral i0_poss f1_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f1_poss a_wral i0_poss f0_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f0_poss a_wral i1_poss f0_poss a_wral i0_poss f0_poss a_wral p_syld i0_poss i1_poss i2_poss f1_poss f2_poss a_df-po i0_poss i1_poss i2_poss f0_poss f2_poss a_df-po f0_poss f1_poss a_wss i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f1_poss a_wral i1_poss f1_poss a_wral i0_poss f1_poss a_wral i0_poss a_sup_set_class i0_poss a_sup_set_class f2_poss a_wbr a_wn i0_poss a_sup_set_class i1_poss a_sup_set_class f2_poss a_wbr i1_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wa i0_poss a_sup_set_class i2_poss a_sup_set_class f2_poss a_wbr a_wi a_wa i2_poss f0_poss a_wral i1_poss f0_poss a_wral i0_poss f0_poss a_wral f1_poss f2_poss a_wpo f0_poss f2_poss a_wpo p_3imtr4g $.
$}

$(Equality theorem for partial ordering predicate.  (Contributed by NM,
       27-Mar-1997.) $)

${
	$v A R S  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z A  $.
	f0_poeq1 $f class A $.
	f1_poeq1 $f class R $.
	f2_poeq1 $f class S $.
	i0_poeq1 $f set x $.
	i1_poeq1 $f set y $.
	i2_poeq1 $f set z $.
	p_poeq1 $p |- ( R = S -> ( R Po A <-> S Po A ) ) $= i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f1_poeq1 f2_poeq1 p_breq f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f1_poeq1 a_wbr i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f2_poeq1 a_wbr p_notbid i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 f2_poeq1 p_breq i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 f2_poeq1 p_breq f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 a_wbr i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f2_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr p_anbi12d i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 f2_poeq1 p_breq f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f2_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr p_imbi12d f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wi i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f2_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wi p_anbi12d f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wi a_wa i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f2_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wi a_wa i2_poeq1 f0_poeq1 p_ralbidv f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wi a_wa i2_poeq1 f0_poeq1 a_wral i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f2_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wi a_wa i2_poeq1 f0_poeq1 a_wral i0_poeq1 i1_poeq1 f0_poeq1 f0_poeq1 p_2ralbidv i0_poeq1 i1_poeq1 i2_poeq1 f0_poeq1 f1_poeq1 a_df-po i0_poeq1 i1_poeq1 i2_poeq1 f0_poeq1 f2_poeq1 a_df-po f1_poeq1 f2_poeq1 a_wceq i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f1_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f1_poeq1 a_wbr a_wi a_wa i2_poeq1 f0_poeq1 a_wral i1_poeq1 f0_poeq1 a_wral i0_poeq1 f0_poeq1 a_wral i0_poeq1 a_sup_set_class i0_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wn i0_poeq1 a_sup_set_class i1_poeq1 a_sup_set_class f2_poeq1 a_wbr i1_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wa i0_poeq1 a_sup_set_class i2_poeq1 a_sup_set_class f2_poeq1 a_wbr a_wi a_wa i2_poeq1 f0_poeq1 a_wral i1_poeq1 f0_poeq1 a_wral i0_poeq1 f0_poeq1 a_wral f0_poeq1 f1_poeq1 a_wpo f0_poeq1 f2_poeq1 a_wpo p_3bitr4g $.
$}

$(Equality theorem for partial ordering predicate.  (Contributed by NM,
     27-Mar-1997.) $)

${
	$v A B R  $.
	f0_poeq2 $f class A $.
	f1_poeq2 $f class B $.
	f2_poeq2 $f class R $.
	p_poeq2 $p |- ( A = B -> ( R Po A <-> R Po B ) ) $= f1_poeq2 f0_poeq2 p_eqimss2 f1_poeq2 f0_poeq2 f2_poeq2 p_poss f0_poeq2 f1_poeq2 a_wceq f1_poeq2 f0_poeq2 a_wss f0_poeq2 f2_poeq2 a_wpo f1_poeq2 f2_poeq2 a_wpo a_wi p_syl f0_poeq2 f1_poeq2 p_eqimss f0_poeq2 f1_poeq2 f2_poeq2 p_poss f0_poeq2 f1_poeq2 a_wceq f0_poeq2 f1_poeq2 a_wss f1_poeq2 f2_poeq2 a_wpo f0_poeq2 f2_poeq2 a_wpo a_wi p_syl f0_poeq2 f1_poeq2 a_wceq f0_poeq2 f2_poeq2 a_wpo f1_poeq2 f2_poeq2 a_wpo p_impbid $.
$}

$(Bound-variable hypothesis builder for partial orders.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) $)

${
	$v x A R  $.
	$d R a b c  $.
	$d A a b c  $.
	$d x a b c  $.
	f0_nfpo $f set x $.
	f1_nfpo $f class A $.
	f2_nfpo $f class R $.
	i0_nfpo $f set a $.
	i1_nfpo $f set b $.
	i2_nfpo $f set c $.
	e0_nfpo $e |- F/_ x R $.
	e1_nfpo $e |- F/_ x A $.
	p_nfpo $p |- F/ x R Po A $= i0_nfpo i1_nfpo i2_nfpo f1_nfpo f2_nfpo a_df-po e1_nfpo e1_nfpo e1_nfpo f0_nfpo i0_nfpo a_sup_set_class p_nfcv e0_nfpo f0_nfpo i0_nfpo a_sup_set_class p_nfcv f0_nfpo i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo p_nfbr i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo a_wbr f0_nfpo p_nfn f0_nfpo i0_nfpo a_sup_set_class p_nfcv e0_nfpo f0_nfpo i1_nfpo a_sup_set_class p_nfcv f0_nfpo i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo p_nfbr f0_nfpo i1_nfpo a_sup_set_class p_nfcv e0_nfpo f0_nfpo i2_nfpo a_sup_set_class p_nfcv f0_nfpo i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo p_nfbr i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr f0_nfpo p_nfan f0_nfpo i0_nfpo a_sup_set_class p_nfcv e0_nfpo f0_nfpo i2_nfpo a_sup_set_class p_nfcv f0_nfpo i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo p_nfbr i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wa i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr f0_nfpo p_nfim i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo a_wbr a_wn i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wa i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wi f0_nfpo p_nfan i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo a_wbr a_wn i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wa i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wi a_wa f0_nfpo i2_nfpo f1_nfpo p_nfral i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo a_wbr a_wn i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wa i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wi a_wa i2_nfpo f1_nfpo a_wral f0_nfpo i1_nfpo f1_nfpo p_nfral i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo a_wbr a_wn i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wa i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wi a_wa i2_nfpo f1_nfpo a_wral i1_nfpo f1_nfpo a_wral f0_nfpo i0_nfpo f1_nfpo p_nfral f1_nfpo f2_nfpo a_wpo i0_nfpo a_sup_set_class i0_nfpo a_sup_set_class f2_nfpo a_wbr a_wn i0_nfpo a_sup_set_class i1_nfpo a_sup_set_class f2_nfpo a_wbr i1_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wa i0_nfpo a_sup_set_class i2_nfpo a_sup_set_class f2_nfpo a_wbr a_wi a_wa i2_nfpo f1_nfpo a_wral i1_nfpo f1_nfpo a_wral i0_nfpo f1_nfpo a_wral f0_nfpo p_nfxfr $.
$}

$(Bound-variable hypothesis builder for total orders.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) $)

${
	$v x A R  $.
	$d R a b  $.
	$d A a b  $.
	$d x a b  $.
	f0_nfso $f set x $.
	f1_nfso $f class A $.
	f2_nfso $f class R $.
	i0_nfso $f set a $.
	i1_nfso $f set b $.
	e0_nfso $e |- F/_ x R $.
	e1_nfso $e |- F/_ x A $.
	p_nfso $p |- F/ x R Or A $= i0_nfso i1_nfso f1_nfso f2_nfso a_df-so e0_nfso e1_nfso f0_nfso f1_nfso f2_nfso p_nfpo e1_nfso e1_nfso f0_nfso i0_nfso a_sup_set_class p_nfcv e0_nfso f0_nfso i1_nfso a_sup_set_class p_nfcv f0_nfso i0_nfso a_sup_set_class i1_nfso a_sup_set_class f2_nfso p_nfbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class a_wceq f0_nfso p_nfv f0_nfso i1_nfso a_sup_set_class p_nfcv e0_nfso f0_nfso i0_nfso a_sup_set_class p_nfcv f0_nfso i1_nfso a_sup_set_class i0_nfso a_sup_set_class f2_nfso p_nfbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class f2_nfso a_wbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class a_wceq i1_nfso a_sup_set_class i0_nfso a_sup_set_class f2_nfso a_wbr f0_nfso p_nf3or i0_nfso a_sup_set_class i1_nfso a_sup_set_class f2_nfso a_wbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class a_wceq i1_nfso a_sup_set_class i0_nfso a_sup_set_class f2_nfso a_wbr a_w3o f0_nfso i1_nfso f1_nfso p_nfral i0_nfso a_sup_set_class i1_nfso a_sup_set_class f2_nfso a_wbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class a_wceq i1_nfso a_sup_set_class i0_nfso a_sup_set_class f2_nfso a_wbr a_w3o i1_nfso f1_nfso a_wral f0_nfso i0_nfso f1_nfso p_nfral f1_nfso f2_nfso a_wpo i0_nfso a_sup_set_class i1_nfso a_sup_set_class f2_nfso a_wbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class a_wceq i1_nfso a_sup_set_class i0_nfso a_sup_set_class f2_nfso a_wbr a_w3o i1_nfso f1_nfso a_wral i0_nfso f1_nfso a_wral f0_nfso p_nfan f1_nfso f2_nfso a_wor f1_nfso f2_nfso a_wpo i0_nfso a_sup_set_class i1_nfso a_sup_set_class f2_nfso a_wbr i0_nfso a_sup_set_class i1_nfso a_sup_set_class a_wceq i1_nfso a_sup_set_class i0_nfso a_sup_set_class f2_nfso a_wbr a_w3o i1_nfso f1_nfso a_wral i0_nfso f1_nfso a_wral a_wa f0_nfso p_nfxfr $.
$}

$(Properties of partial order relation in class notation.  (Contributed by
       NM, 27-Mar-1997.) $)

${
	$v A B C D R  $.
	$d x y z R  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z C  $.
	$d x y z D  $.
	f0_pocl $f class A $.
	f1_pocl $f class B $.
	f2_pocl $f class C $.
	f3_pocl $f class D $.
	f4_pocl $f class R $.
	i0_pocl $f set x $.
	i1_pocl $f set y $.
	i2_pocl $f set z $.
	p_pocl $p |- ( R Po A -> ( ( B e. A /\ C e. A /\ D e. A ) -> ( -. B R B /\ ( ( B R C /\ C R D ) -> B R D ) ) ) ) $= i0_pocl a_sup_set_class f1_pocl a_wceq p_id i0_pocl a_sup_set_class f1_pocl a_wceq p_id i0_pocl a_sup_set_class f1_pocl a_wceq i0_pocl a_sup_set_class f1_pocl i0_pocl a_sup_set_class f1_pocl f4_pocl p_breq12d i0_pocl a_sup_set_class f1_pocl a_wceq i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr f1_pocl f1_pocl f4_pocl a_wbr p_notbid i0_pocl a_sup_set_class f1_pocl i1_pocl a_sup_set_class f4_pocl p_breq1 i0_pocl a_sup_set_class f1_pocl a_wceq i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr p_anbi1d i0_pocl a_sup_set_class f1_pocl i2_pocl a_sup_set_class f4_pocl p_breq1 i0_pocl a_sup_set_class f1_pocl a_wceq i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr p_imbi12d i0_pocl a_sup_set_class f1_pocl a_wceq i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn f1_pocl f1_pocl f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi p_anbi12d i0_pocl a_sup_set_class f1_pocl a_wceq i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa f0_pocl f4_pocl a_wpo p_imbi2d i1_pocl a_sup_set_class f2_pocl f1_pocl f4_pocl p_breq2 i1_pocl a_sup_set_class f2_pocl i2_pocl a_sup_set_class f4_pocl p_breq1 i1_pocl a_sup_set_class f2_pocl a_wceq f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr f1_pocl f2_pocl f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr p_anbi12d i1_pocl a_sup_set_class f2_pocl a_wceq f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr p_imbi1d i1_pocl a_sup_set_class f2_pocl a_wceq f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi f1_pocl f1_pocl f4_pocl a_wbr a_wn p_anbi2d i1_pocl a_sup_set_class f2_pocl a_wceq f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa f0_pocl f4_pocl a_wpo p_imbi2d i2_pocl a_sup_set_class f3_pocl f2_pocl f4_pocl p_breq2 i2_pocl a_sup_set_class f3_pocl a_wceq f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr f2_pocl f3_pocl f4_pocl a_wbr f1_pocl f2_pocl f4_pocl a_wbr p_anbi2d i2_pocl a_sup_set_class f3_pocl f1_pocl f4_pocl p_breq2 i2_pocl a_sup_set_class f3_pocl a_wceq f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl f2_pocl f4_pocl a_wbr f2_pocl f3_pocl f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr f1_pocl f3_pocl f4_pocl a_wbr p_imbi12d i2_pocl a_sup_set_class f3_pocl a_wceq f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi f1_pocl f2_pocl f4_pocl a_wbr f2_pocl f3_pocl f4_pocl a_wbr a_wa f1_pocl f3_pocl f4_pocl a_wbr a_wi f1_pocl f1_pocl f4_pocl a_wbr a_wn p_anbi2d i2_pocl a_sup_set_class f3_pocl a_wceq f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl f2_pocl f4_pocl a_wbr f2_pocl f3_pocl f4_pocl a_wbr a_wa f1_pocl f3_pocl f4_pocl a_wbr a_wi a_wa f0_pocl f4_pocl a_wpo p_imbi2d i0_pocl i1_pocl i2_pocl f0_pocl f4_pocl a_df-po i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa i0_pocl i1_pocl i2_pocl f0_pocl f0_pocl f0_pocl p_r3al f0_pocl f4_pocl a_wpo i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa i2_pocl f0_pocl a_wral i1_pocl f0_pocl a_wral i0_pocl f0_pocl a_wral i0_pocl a_sup_set_class f0_pocl a_wcel i1_pocl a_sup_set_class f0_pocl a_wcel i2_pocl a_sup_set_class f0_pocl a_wcel a_w3a i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi i2_pocl a_wal i1_pocl a_wal i0_pocl a_wal p_bitri f0_pocl f4_pocl a_wpo i0_pocl a_sup_set_class f0_pocl a_wcel i1_pocl a_sup_set_class f0_pocl a_wcel i2_pocl a_sup_set_class f0_pocl a_wcel a_w3a i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi i2_pocl a_wal i1_pocl a_wal i0_pocl a_wal p_biimpi f0_pocl f4_pocl a_wpo i0_pocl a_sup_set_class f0_pocl a_wcel i1_pocl a_sup_set_class f0_pocl a_wcel i2_pocl a_sup_set_class f0_pocl a_wcel a_w3a i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi i2_pocl a_wal i0_pocl i1_pocl p_19.21bbi f0_pocl f4_pocl a_wpo i0_pocl a_sup_set_class f0_pocl a_wcel i1_pocl a_sup_set_class f0_pocl a_wcel i2_pocl a_sup_set_class f0_pocl a_wcel a_w3a i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi i2_pocl p_19.21bi f0_pocl f4_pocl a_wpo i0_pocl a_sup_set_class f0_pocl a_wcel i1_pocl a_sup_set_class f0_pocl a_wcel i2_pocl a_sup_set_class f0_pocl a_wcel a_w3a i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa p_com12 f0_pocl f4_pocl a_wpo i0_pocl a_sup_set_class i0_pocl a_sup_set_class f4_pocl a_wbr a_wn i0_pocl a_sup_set_class i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa i0_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi f0_pocl f4_pocl a_wpo f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl i1_pocl a_sup_set_class f4_pocl a_wbr i1_pocl a_sup_set_class i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi f0_pocl f4_pocl a_wpo f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl f2_pocl f4_pocl a_wbr f2_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wa f1_pocl i2_pocl a_sup_set_class f4_pocl a_wbr a_wi a_wa a_wi f0_pocl f4_pocl a_wpo f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl f2_pocl f4_pocl a_wbr f2_pocl f3_pocl f4_pocl a_wbr a_wa f1_pocl f3_pocl f4_pocl a_wbr a_wi a_wa a_wi i0_pocl i1_pocl i2_pocl f1_pocl f2_pocl f3_pocl f0_pocl f0_pocl f0_pocl p_vtocl3ga f1_pocl f0_pocl a_wcel f2_pocl f0_pocl a_wcel f3_pocl f0_pocl a_wcel a_w3a f0_pocl f4_pocl a_wpo f1_pocl f1_pocl f4_pocl a_wbr a_wn f1_pocl f2_pocl f4_pocl a_wbr f2_pocl f3_pocl f4_pocl a_wbr a_wa f1_pocl f3_pocl f4_pocl a_wbr a_wi a_wa p_com12 $.
$}

$(Sufficient conditions for a partial order.  (Contributed by NM,
       9-Jul-2014.) $)

${
	$v ph x y z A R  $.
	$d x y z A  $.
	$d x y z R  $.
	$d x y z ph  $.
	f0_ispod $f wff ph $.
	f1_ispod $f set x $.
	f2_ispod $f set y $.
	f3_ispod $f set z $.
	f4_ispod $f class A $.
	f5_ispod $f class R $.
	e0_ispod $e |- ( ( ph /\ x e. A ) -> -. x R x ) $.
	e1_ispod $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( ( x R y /\ y R z ) -> x R z ) ) $.
	p_ispod $p |- ( ph -> R Po A ) $= e0_ispod f0_ispod f2_ispod a_sup_set_class f4_ispod a_wcel f1_ispod a_sup_set_class f4_ispod a_wcel f1_ispod a_sup_set_class f1_ispod a_sup_set_class f5_ispod a_wbr a_wn f3_ispod a_sup_set_class f4_ispod a_wcel p_3ad2antr1 e1_ispod f0_ispod f1_ispod a_sup_set_class f4_ispod a_wcel f2_ispod a_sup_set_class f4_ispod a_wcel f3_ispod a_sup_set_class f4_ispod a_wcel a_w3a a_wa f1_ispod a_sup_set_class f1_ispod a_sup_set_class f5_ispod a_wbr a_wn f1_ispod a_sup_set_class f2_ispod a_sup_set_class f5_ispod a_wbr f2_ispod a_sup_set_class f3_ispod a_sup_set_class f5_ispod a_wbr a_wa f1_ispod a_sup_set_class f3_ispod a_sup_set_class f5_ispod a_wbr a_wi p_jca f0_ispod f1_ispod a_sup_set_class f1_ispod a_sup_set_class f5_ispod a_wbr a_wn f1_ispod a_sup_set_class f2_ispod a_sup_set_class f5_ispod a_wbr f2_ispod a_sup_set_class f3_ispod a_sup_set_class f5_ispod a_wbr a_wa f1_ispod a_sup_set_class f3_ispod a_sup_set_class f5_ispod a_wbr a_wi a_wa f1_ispod f2_ispod f3_ispod f4_ispod f4_ispod f4_ispod p_ralrimivvva f1_ispod f2_ispod f3_ispod f4_ispod f5_ispod a_df-po f0_ispod f1_ispod a_sup_set_class f1_ispod a_sup_set_class f5_ispod a_wbr a_wn f1_ispod a_sup_set_class f2_ispod a_sup_set_class f5_ispod a_wbr f2_ispod a_sup_set_class f3_ispod a_sup_set_class f5_ispod a_wbr a_wa f1_ispod a_sup_set_class f3_ispod a_sup_set_class f5_ispod a_wbr a_wi a_wa f3_ispod f4_ispod a_wral f2_ispod f4_ispod a_wral f1_ispod f4_ispod a_wral f4_ispod f5_ispod a_wpo p_sylibr $.
$}

$(Perform the substitutions into the strict weak ordering law.
       (Contributed by Mario Carneiro, 31-Dec-2014.) $)

${
	$v ph x y z A R X Y Z  $.
	$d x y z A  $.
	$d x y z ph  $.
	$d x y z R  $.
	$d x y z X  $.
	$d y z Y  $.
	$d z Z  $.
	f0_swopolem $f wff ph $.
	f1_swopolem $f set x $.
	f2_swopolem $f set y $.
	f3_swopolem $f set z $.
	f4_swopolem $f class A $.
	f5_swopolem $f class R $.
	f6_swopolem $f class X $.
	f7_swopolem $f class Y $.
	f8_swopolem $f class Z $.
	e0_swopolem $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( x R y -> ( x R z \/ z R y ) ) ) $.
	p_swopolem $p |- ( ( ph /\ ( X e. A /\ Y e. A /\ Z e. A ) ) -> ( X R Y -> ( X R Z \/ Z R Y ) ) ) $= e0_swopolem f0_swopolem f1_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr f1_swopolem a_sup_set_class f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo a_wi f1_swopolem f2_swopolem f3_swopolem f4_swopolem f4_swopolem f4_swopolem p_ralrimivvva f1_swopolem a_sup_set_class f6_swopolem f2_swopolem a_sup_set_class f5_swopolem p_breq1 f1_swopolem a_sup_set_class f6_swopolem f3_swopolem a_sup_set_class f5_swopolem p_breq1 f1_swopolem a_sup_set_class f6_swopolem a_wceq f1_swopolem a_sup_set_class f3_swopolem a_sup_set_class f5_swopolem a_wbr f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr p_orbi1d f1_swopolem a_sup_set_class f6_swopolem a_wceq f1_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr f6_swopolem f2_swopolem a_sup_set_class f5_swopolem a_wbr f1_swopolem a_sup_set_class f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo p_imbi12d f2_swopolem a_sup_set_class f7_swopolem f6_swopolem f5_swopolem p_breq2 f2_swopolem a_sup_set_class f7_swopolem f3_swopolem a_sup_set_class f5_swopolem p_breq2 f2_swopolem a_sup_set_class f7_swopolem a_wceq f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f7_swopolem f5_swopolem a_wbr f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr p_orbi2d f2_swopolem a_sup_set_class f7_swopolem a_wceq f6_swopolem f2_swopolem a_sup_set_class f5_swopolem a_wbr f6_swopolem f7_swopolem f5_swopolem a_wbr f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f7_swopolem f5_swopolem a_wbr a_wo p_imbi12d f3_swopolem a_sup_set_class f8_swopolem f6_swopolem f5_swopolem p_breq2 f3_swopolem a_sup_set_class f8_swopolem f7_swopolem f5_swopolem p_breq1 f3_swopolem a_sup_set_class f8_swopolem a_wceq f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f6_swopolem f8_swopolem f5_swopolem a_wbr f3_swopolem a_sup_set_class f7_swopolem f5_swopolem a_wbr f8_swopolem f7_swopolem f5_swopolem a_wbr p_orbi12d f3_swopolem a_sup_set_class f8_swopolem a_wceq f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f7_swopolem f5_swopolem a_wbr a_wo f6_swopolem f8_swopolem f5_swopolem a_wbr f8_swopolem f7_swopolem f5_swopolem a_wbr a_wo f6_swopolem f7_swopolem f5_swopolem a_wbr p_imbi2d f1_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr f1_swopolem a_sup_set_class f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo a_wi f6_swopolem f7_swopolem f5_swopolem a_wbr f6_swopolem f8_swopolem f5_swopolem a_wbr f8_swopolem f7_swopolem f5_swopolem a_wbr a_wo a_wi f6_swopolem f2_swopolem a_sup_set_class f5_swopolem a_wbr f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo a_wi f6_swopolem f7_swopolem f5_swopolem a_wbr f6_swopolem f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f7_swopolem f5_swopolem a_wbr a_wo a_wi f1_swopolem f2_swopolem f3_swopolem f6_swopolem f7_swopolem f8_swopolem f4_swopolem f4_swopolem f4_swopolem p_rspc3v f0_swopolem f1_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr f1_swopolem a_sup_set_class f3_swopolem a_sup_set_class f5_swopolem a_wbr f3_swopolem a_sup_set_class f2_swopolem a_sup_set_class f5_swopolem a_wbr a_wo a_wi f3_swopolem f4_swopolem a_wral f2_swopolem f4_swopolem a_wral f1_swopolem f4_swopolem a_wral f6_swopolem f4_swopolem a_wcel f7_swopolem f4_swopolem a_wcel f8_swopolem f4_swopolem a_wcel a_w3a f6_swopolem f7_swopolem f5_swopolem a_wbr f6_swopolem f8_swopolem f5_swopolem a_wbr f8_swopolem f7_swopolem f5_swopolem a_wbr a_wo a_wi p_mpan9 $.
$}

$(A strict weak order is a partial order.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)

${
	$v ph x y z A R  $.
	$d x y z A  $.
	$d x y z R  $.
	$d x y z ph  $.
	f0_swopo $f wff ph $.
	f1_swopo $f set x $.
	f2_swopo $f set y $.
	f3_swopo $f set z $.
	f4_swopo $f class A $.
	f5_swopo $f class R $.
	e0_swopo $e |- ( ( ph /\ ( y e. A /\ z e. A ) ) -> ( y R z -> -. z R y ) ) $.
	e1_swopo $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( x R y -> ( x R z \/ z R y ) ) ) $.
	p_swopo $p |- ( ph -> R Po A ) $= f1_swopo a_sup_set_class f4_swopo a_wcel p_id f1_swopo a_sup_set_class f4_swopo a_wcel f1_swopo a_sup_set_class f4_swopo a_wcel p_ancli e0_swopo f0_swopo f2_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f2_swopo f3_swopo f4_swopo f4_swopo p_ralrimivva f2_swopo a_sup_set_class f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo p_breq1 f2_swopo a_sup_set_class f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo p_breq2 f2_swopo a_sup_set_class f1_swopo a_sup_set_class a_wceq f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr p_notbid f2_swopo a_sup_set_class f1_swopo a_sup_set_class a_wceq f2_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn f3_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr a_wn p_imbi12d f3_swopo a_sup_set_class f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo p_breq2 f3_swopo a_sup_set_class f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo p_breq1 f3_swopo a_sup_set_class f1_swopo a_sup_set_class a_wceq f3_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr p_notbid f3_swopo a_sup_set_class f1_swopo a_sup_set_class a_wceq f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr a_wn f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr a_wn p_imbi12d f2_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f2_swopo f3_swopo f1_swopo a_sup_set_class f1_swopo a_sup_set_class f4_swopo f4_swopo p_rspc2va f1_swopo a_sup_set_class f4_swopo a_wcel f1_swopo a_sup_set_class f4_swopo a_wcel f1_swopo a_sup_set_class f4_swopo a_wcel a_wa f2_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f3_swopo f4_swopo a_wral f2_swopo f4_swopo a_wral f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f0_swopo p_syl2anr f0_swopo f1_swopo a_sup_set_class f4_swopo a_wcel a_wa f1_swopo a_sup_set_class f1_swopo a_sup_set_class f5_swopo a_wbr p_pm2.01d e0_swopo f0_swopo f2_swopo a_sup_set_class f4_swopo a_wcel f3_swopo a_sup_set_class f4_swopo a_wcel f2_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn a_wi f1_swopo a_sup_set_class f4_swopo a_wcel p_3adantr1 e1_swopo f0_swopo f1_swopo a_sup_set_class f4_swopo a_wcel f2_swopo a_sup_set_class f4_swopo a_wcel f3_swopo a_sup_set_class f4_swopo a_wcel a_w3a a_wa f1_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wo p_imp f0_swopo f1_swopo a_sup_set_class f4_swopo a_wcel f2_swopo a_sup_set_class f4_swopo a_wcel f3_swopo a_sup_set_class f4_swopo a_wcel a_w3a a_wa f1_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wa f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr p_orcomd f0_swopo f1_swopo a_sup_set_class f4_swopo a_wcel f2_swopo a_sup_set_class f4_swopo a_wcel f3_swopo a_sup_set_class f4_swopo a_wcel a_w3a a_wa f1_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wa f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr p_ord f0_swopo f1_swopo a_sup_set_class f4_swopo a_wcel f2_swopo a_sup_set_class f4_swopo a_wcel f3_swopo a_sup_set_class f4_swopo a_wcel a_w3a a_wa f1_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr p_expimpd f0_swopo f1_swopo a_sup_set_class f4_swopo a_wcel f2_swopo a_sup_set_class f4_swopo a_wcel f3_swopo a_sup_set_class f4_swopo a_wcel a_w3a a_wa f2_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr f3_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr a_wn f1_swopo a_sup_set_class f2_swopo a_sup_set_class f5_swopo a_wbr f1_swopo a_sup_set_class f3_swopo a_sup_set_class f5_swopo a_wbr p_sylan2d f0_swopo f1_swopo f2_swopo f3_swopo f4_swopo f5_swopo p_ispod $.
$}

$(A partial order relation is irreflexive.  (Contributed by NM,
     27-Mar-1997.) $)

${
	$v A B R  $.
	f0_poirr $f class A $.
	f1_poirr $f class B $.
	f2_poirr $f class R $.
	p_poirr $p |- ( ( R Po A /\ B e. A ) -> -. B R B ) $= f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_df-3an f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel p_anabs1 f1_poirr f0_poirr a_wcel p_anidm f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_w3a f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_wa f1_poirr f0_poirr a_wcel a_wa f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_wa f1_poirr f0_poirr a_wcel p_3bitrri f0_poirr f1_poirr f1_poirr f1_poirr f2_poirr p_pocl f0_poirr f2_poirr a_wpo f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_w3a f1_poirr f1_poirr f2_poirr a_wbr a_wn f1_poirr f1_poirr f2_poirr a_wbr f1_poirr f1_poirr f2_poirr a_wbr a_wa f1_poirr f1_poirr f2_poirr a_wbr a_wi a_wa p_imp f0_poirr f2_poirr a_wpo f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_w3a a_wa f1_poirr f1_poirr f2_poirr a_wbr a_wn f1_poirr f1_poirr f2_poirr a_wbr f1_poirr f1_poirr f2_poirr a_wbr a_wa f1_poirr f1_poirr f2_poirr a_wbr a_wi p_simpld f1_poirr f0_poirr a_wcel f0_poirr f2_poirr a_wpo f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel f1_poirr f0_poirr a_wcel a_w3a f1_poirr f1_poirr f2_poirr a_wbr a_wn p_sylan2b $.
$}

$(A partial order relation is a transitive relation.  (Contributed by NM,
     27-Mar-1997.) $)

${
	$v A B C D R  $.
	f0_potr $f class A $.
	f1_potr $f class B $.
	f2_potr $f class C $.
	f3_potr $f class D $.
	f4_potr $f class R $.
	p_potr $p |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( B R C /\ C R D ) -> B R D ) ) $= f0_potr f1_potr f2_potr f3_potr f4_potr p_pocl f0_potr f4_potr a_wpo f1_potr f0_potr a_wcel f2_potr f0_potr a_wcel f3_potr f0_potr a_wcel a_w3a f1_potr f1_potr f4_potr a_wbr a_wn f1_potr f2_potr f4_potr a_wbr f2_potr f3_potr f4_potr a_wbr a_wa f1_potr f3_potr f4_potr a_wbr a_wi a_wa p_imp f0_potr f4_potr a_wpo f1_potr f0_potr a_wcel f2_potr f0_potr a_wcel f3_potr f0_potr a_wcel a_w3a a_wa f1_potr f1_potr f4_potr a_wbr a_wn f1_potr f2_potr f4_potr a_wbr f2_potr f3_potr f4_potr a_wbr a_wa f1_potr f3_potr f4_potr a_wbr a_wi p_simprd $.
$}

$(A partial order relation has no 2-cycle loops.  (Contributed by NM,
     27-Mar-1997.) $)

${
	$v A B C R  $.
	f0_po2nr $f class A $.
	f1_po2nr $f class B $.
	f2_po2nr $f class C $.
	f3_po2nr $f class R $.
	p_po2nr $p |- ( ( R Po A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) ) $= f0_po2nr f1_po2nr f3_po2nr p_poirr f0_po2nr f3_po2nr a_wpo f1_po2nr f0_po2nr a_wcel f1_po2nr f1_po2nr f3_po2nr a_wbr a_wn f2_po2nr f0_po2nr a_wcel p_adantrr f0_po2nr f1_po2nr f2_po2nr f1_po2nr f3_po2nr p_potr f0_po2nr f3_po2nr a_wpo f1_po2nr f0_po2nr a_wcel f2_po2nr f0_po2nr a_wcel f1_po2nr f0_po2nr a_wcel f1_po2nr f2_po2nr f3_po2nr a_wbr f2_po2nr f1_po2nr f3_po2nr a_wbr a_wa f1_po2nr f1_po2nr f3_po2nr a_wbr a_wi p_3exp2 f0_po2nr f3_po2nr a_wpo f1_po2nr f0_po2nr a_wcel f2_po2nr f0_po2nr a_wcel f1_po2nr f0_po2nr a_wcel f1_po2nr f2_po2nr f3_po2nr a_wbr f2_po2nr f1_po2nr f3_po2nr a_wbr a_wa f1_po2nr f1_po2nr f3_po2nr a_wbr a_wi p_com34 f0_po2nr f3_po2nr a_wpo f1_po2nr f0_po2nr a_wcel f2_po2nr f0_po2nr a_wcel f1_po2nr f2_po2nr f3_po2nr a_wbr f2_po2nr f1_po2nr f3_po2nr a_wbr a_wa f1_po2nr f1_po2nr f3_po2nr a_wbr a_wi a_wi p_pm2.43d f0_po2nr f3_po2nr a_wpo f1_po2nr f0_po2nr a_wcel f2_po2nr f0_po2nr a_wcel f1_po2nr f2_po2nr f3_po2nr a_wbr f2_po2nr f1_po2nr f3_po2nr a_wbr a_wa f1_po2nr f1_po2nr f3_po2nr a_wbr a_wi p_imp32 f0_po2nr f3_po2nr a_wpo f1_po2nr f0_po2nr a_wcel f2_po2nr f0_po2nr a_wcel a_wa a_wa f1_po2nr f2_po2nr f3_po2nr a_wbr f2_po2nr f1_po2nr f3_po2nr a_wbr a_wa f1_po2nr f1_po2nr f3_po2nr a_wbr p_mtod $.
$}

$(A partial order relation has no 3-cycle loops.  (Contributed by NM,
     27-Mar-1997.) $)

${
	$v A B C D R  $.
	f0_po3nr $f class A $.
	f1_po3nr $f class B $.
	f2_po3nr $f class C $.
	f3_po3nr $f class D $.
	f4_po3nr $f class R $.
	p_po3nr $p |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) ) $= f0_po3nr f1_po3nr f3_po3nr f4_po3nr p_po2nr f0_po3nr f4_po3nr a_wpo f1_po3nr f0_po3nr a_wcel f3_po3nr f0_po3nr a_wcel f1_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr a_wa a_wn f2_po3nr f0_po3nr a_wcel p_3adantr2 f1_po3nr f2_po3nr f4_po3nr a_wbr f2_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr a_df-3an f0_po3nr f1_po3nr f2_po3nr f3_po3nr f4_po3nr p_potr f0_po3nr f4_po3nr a_wpo f1_po3nr f0_po3nr a_wcel f2_po3nr f0_po3nr a_wcel f3_po3nr f0_po3nr a_wcel a_w3a a_wa f1_po3nr f2_po3nr f4_po3nr a_wbr f2_po3nr f3_po3nr f4_po3nr a_wbr a_wa f1_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr p_anim1d f1_po3nr f2_po3nr f4_po3nr a_wbr f2_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr a_w3a f1_po3nr f2_po3nr f4_po3nr a_wbr f2_po3nr f3_po3nr f4_po3nr a_wbr a_wa f3_po3nr f1_po3nr f4_po3nr a_wbr a_wa f0_po3nr f4_po3nr a_wpo f1_po3nr f0_po3nr a_wcel f2_po3nr f0_po3nr a_wcel f3_po3nr f0_po3nr a_wcel a_w3a a_wa f1_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr a_wa p_syl5bi f0_po3nr f4_po3nr a_wpo f1_po3nr f0_po3nr a_wcel f2_po3nr f0_po3nr a_wcel f3_po3nr f0_po3nr a_wcel a_w3a a_wa f1_po3nr f2_po3nr f4_po3nr a_wbr f2_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr a_w3a f1_po3nr f3_po3nr f4_po3nr a_wbr f3_po3nr f1_po3nr f4_po3nr a_wbr a_wa p_mtod $.
$}

$(Any relation is a partial ordering of the empty set.  (Contributed by
       NM, 28-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v R  $.
	$d x y z R  $.
	f0_po0 $f class R $.
	i0_po0 $f set x $.
	i1_po0 $f set y $.
	i2_po0 $f set z $.
	p_po0 $p |- R Po (/) $= i0_po0 a_sup_set_class i0_po0 a_sup_set_class f0_po0 a_wbr a_wn i0_po0 a_sup_set_class i1_po0 a_sup_set_class f0_po0 a_wbr i1_po0 a_sup_set_class i2_po0 a_sup_set_class f0_po0 a_wbr a_wa i0_po0 a_sup_set_class i2_po0 a_sup_set_class f0_po0 a_wbr a_wi a_wa i2_po0 a_c0 a_wral i1_po0 a_c0 a_wral i0_po0 p_ral0 i0_po0 i1_po0 i2_po0 a_c0 f0_po0 a_df-po a_c0 f0_po0 a_wpo i0_po0 a_sup_set_class i0_po0 a_sup_set_class f0_po0 a_wbr a_wn i0_po0 a_sup_set_class i1_po0 a_sup_set_class f0_po0 a_wbr i1_po0 a_sup_set_class i2_po0 a_sup_set_class f0_po0 a_wbr a_wa i0_po0 a_sup_set_class i2_po0 a_sup_set_class f0_po0 a_wbr a_wi a_wa i2_po0 a_c0 a_wral i1_po0 a_c0 a_wral i0_po0 a_c0 a_wral p_mpbir $.
$}

$(A function preserves a partial order relation.  (Contributed by Jeff
       Madsen, 18-Jun-2011.) $)

${
	$v x y A B R S X Y  $.
	$d R v w x y z  $.
	$d S v w z  $.
	$d X v w y z  $.
	$d Y x z  $.
	$d A v w x z  $.
	$d B v w x z  $.
	f0_pofun $f set x $.
	f1_pofun $f set y $.
	f2_pofun $f class A $.
	f3_pofun $f class B $.
	f4_pofun $f class R $.
	f5_pofun $f class S $.
	f6_pofun $f class X $.
	f7_pofun $f class Y $.
	i0_pofun $f set z $.
	i1_pofun $f set w $.
	i2_pofun $f set v $.
	e0_pofun $e |- S = { <. x , y >. | X R Y } $.
	e1_pofun $e |- ( x = y -> X = Y ) $.
	p_pofun $p |- ( ( R Po B /\ A. x e. A X e. B ) -> S Po A ) $= f0_pofun i2_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_nfel1 f0_pofun i2_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_eleq1d f6_pofun f3_pofun a_wcel f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i2_pofun a_sup_set_class f2_pofun p_rspc i2_pofun a_sup_set_class f2_pofun a_wcel f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel p_impcom f3_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun p_poirr i2_pofun a_sup_set_class i2_pofun a_sup_set_class f5_pofun a_df-br e0_pofun f5_pofun f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab i2_pofun a_sup_set_class i2_pofun a_sup_set_class a_cop p_eleq2i f0_pofun i2_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f4_pofun p_nfcv f0_pofun f7_pofun p_nfcv f0_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_nfbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f1_pofun p_nfv i2_pofun p_vex i2_pofun p_vex f0_pofun i2_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_breq1d f1_pofun p_vex f0_pofun f7_pofun p_nfcv e1_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun f7_pofun p_csbief f0_pofun f1_pofun a_sup_set_class i2_pofun a_sup_set_class f6_pofun p_csbeq1 f1_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f7_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb p_syl5eqr f1_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f7_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun p_breq2d f6_pofun f7_pofun f4_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f0_pofun f1_pofun i2_pofun a_sup_set_class i2_pofun a_sup_set_class p_opelopabf i2_pofun a_sup_set_class i2_pofun a_sup_set_class f5_pofun a_wbr i2_pofun a_sup_set_class i2_pofun a_sup_set_class a_cop f5_pofun a_wcel i2_pofun a_sup_set_class i2_pofun a_sup_set_class a_cop f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab a_wcel f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr p_3bitri f3_pofun f4_pofun a_wpo f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel a_wa f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr i2_pofun a_sup_set_class i2_pofun a_sup_set_class f5_pofun a_wbr p_sylnibr f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral i2_pofun a_sup_set_class f2_pofun a_wcel a_wa f3_pofun f4_pofun a_wpo f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel i2_pofun a_sup_set_class i2_pofun a_sup_set_class f5_pofun a_wbr a_wn p_sylan2 f3_pofun f4_pofun a_wpo f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral i2_pofun a_sup_set_class f2_pofun a_wcel i2_pofun a_sup_set_class i2_pofun a_sup_set_class f5_pofun a_wbr a_wn p_anassrs f0_pofun i2_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_nfel1 f0_pofun i2_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_eleq1d f6_pofun f3_pofun a_wcel f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i2_pofun a_sup_set_class f2_pofun p_rspc i2_pofun a_sup_set_class f2_pofun a_wcel f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel p_com12 f0_pofun i1_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_nfel1 f0_pofun i1_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i1_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_eleq1d f6_pofun f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f2_pofun p_rspc i1_pofun a_sup_set_class f2_pofun a_wcel f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel p_com12 f0_pofun i0_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_nfel1 f0_pofun i0_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i0_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun p_eleq1d f6_pofun f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f2_pofun p_rspc i0_pofun a_sup_set_class f2_pofun a_wcel f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel p_com12 f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral i2_pofun a_sup_set_class f2_pofun a_wcel f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel i1_pofun a_sup_set_class f2_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel i0_pofun a_sup_set_class f2_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel p_3anim123d f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral i2_pofun a_sup_set_class f2_pofun a_wcel i1_pofun a_sup_set_class f2_pofun a_wcel i0_pofun a_sup_set_class f2_pofun a_wcel a_w3a f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel a_w3a p_imp f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral i2_pofun a_sup_set_class f2_pofun a_wcel i1_pofun a_sup_set_class f2_pofun a_wcel i0_pofun a_sup_set_class f2_pofun a_wcel a_w3a f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel a_w3a f3_pofun f4_pofun a_wpo p_adantll f3_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun p_potr i2_pofun a_sup_set_class i1_pofun a_sup_set_class f5_pofun a_df-br e0_pofun f5_pofun f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab i2_pofun a_sup_set_class i1_pofun a_sup_set_class a_cop p_eleq2i f0_pofun i2_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f4_pofun p_nfcv f0_pofun f7_pofun p_nfcv f0_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_nfbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f1_pofun p_nfv i2_pofun p_vex i1_pofun p_vex f0_pofun i2_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_breq1d f1_pofun p_vex f0_pofun f7_pofun p_nfcv e1_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun f7_pofun p_csbief f0_pofun f1_pofun a_sup_set_class i1_pofun a_sup_set_class f6_pofun p_csbeq1 f1_pofun a_sup_set_class i1_pofun a_sup_set_class a_wceq f7_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb p_syl5eqr f1_pofun a_sup_set_class i1_pofun a_sup_set_class a_wceq f7_pofun f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun p_breq2d f6_pofun f7_pofun f4_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f0_pofun f1_pofun i2_pofun a_sup_set_class i1_pofun a_sup_set_class p_opelopabf i2_pofun a_sup_set_class i1_pofun a_sup_set_class f5_pofun a_wbr i2_pofun a_sup_set_class i1_pofun a_sup_set_class a_cop f5_pofun a_wcel i2_pofun a_sup_set_class i1_pofun a_sup_set_class a_cop f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab a_wcel f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr p_3bitri i1_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_df-br e0_pofun f5_pofun f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab i1_pofun a_sup_set_class i0_pofun a_sup_set_class a_cop p_eleq2i f0_pofun i1_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f4_pofun p_nfcv f0_pofun f7_pofun p_nfcv f0_pofun f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_nfbr f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f1_pofun p_nfv i1_pofun p_vex i0_pofun p_vex f0_pofun i1_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i1_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_breq1d f1_pofun p_vex f0_pofun f7_pofun p_nfcv e1_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun f7_pofun p_csbief f0_pofun f1_pofun a_sup_set_class i0_pofun a_sup_set_class f6_pofun p_csbeq1 f1_pofun a_sup_set_class i0_pofun a_sup_set_class a_wceq f7_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb p_syl5eqr f1_pofun a_sup_set_class i0_pofun a_sup_set_class a_wceq f7_pofun f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f4_pofun p_breq2d f6_pofun f7_pofun f4_pofun a_wbr f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun a_wbr f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f0_pofun f1_pofun i1_pofun a_sup_set_class i0_pofun a_sup_set_class p_opelopabf i1_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr i1_pofun a_sup_set_class i0_pofun a_sup_set_class a_cop f5_pofun a_wcel i1_pofun a_sup_set_class i0_pofun a_sup_set_class a_cop f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr p_3bitri i2_pofun a_sup_set_class i1_pofun a_sup_set_class f5_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr i1_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr p_anbi12i i2_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_df-br e0_pofun f5_pofun f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab i2_pofun a_sup_set_class i0_pofun a_sup_set_class a_cop p_eleq2i f0_pofun i2_pofun a_sup_set_class f6_pofun p_nfcsb1v f0_pofun f4_pofun p_nfcv f0_pofun f7_pofun p_nfcv f0_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_nfbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f1_pofun p_nfv i2_pofun p_vex i0_pofun p_vex f0_pofun i2_pofun a_sup_set_class f6_pofun p_csbeq1a f0_pofun a_sup_set_class i2_pofun a_sup_set_class a_wceq f6_pofun f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun p_breq1d f1_pofun p_vex f0_pofun f7_pofun p_nfcv e1_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun f7_pofun p_csbief f0_pofun f1_pofun a_sup_set_class i0_pofun a_sup_set_class f6_pofun p_csbeq1 f1_pofun a_sup_set_class i0_pofun a_sup_set_class a_wceq f7_pofun f0_pofun f1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb p_syl5eqr f1_pofun a_sup_set_class i0_pofun a_sup_set_class a_wceq f7_pofun f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f4_pofun p_breq2d f6_pofun f7_pofun f4_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f7_pofun f4_pofun a_wbr f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f0_pofun f1_pofun i2_pofun a_sup_set_class i0_pofun a_sup_set_class p_opelopabf i2_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr i2_pofun a_sup_set_class i0_pofun a_sup_set_class a_cop f5_pofun a_wcel i2_pofun a_sup_set_class i0_pofun a_sup_set_class a_cop f6_pofun f7_pofun f4_pofun a_wbr f0_pofun f1_pofun a_copab a_wcel f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr p_3bitri f3_pofun f4_pofun a_wpo f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel a_w3a a_wa f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr a_wa f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f4_pofun a_wbr i2_pofun a_sup_set_class i1_pofun a_sup_set_class f5_pofun a_wbr i1_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr a_wa i2_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr p_3imtr4g f3_pofun f4_pofun a_wpo f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel a_w3a i2_pofun a_sup_set_class i1_pofun a_sup_set_class f5_pofun a_wbr i1_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr a_wa i2_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr a_wi f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral p_adantlr f3_pofun f4_pofun a_wpo f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral a_wa i2_pofun a_sup_set_class f2_pofun a_wcel i1_pofun a_sup_set_class f2_pofun a_wcel i0_pofun a_sup_set_class f2_pofun a_wcel a_w3a f0_pofun i2_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i1_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel f0_pofun i0_pofun a_sup_set_class f6_pofun a_csb f3_pofun a_wcel a_w3a i2_pofun a_sup_set_class i1_pofun a_sup_set_class f5_pofun a_wbr i1_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr a_wa i2_pofun a_sup_set_class i0_pofun a_sup_set_class f5_pofun a_wbr a_wi p_syldan f3_pofun f4_pofun a_wpo f6_pofun f3_pofun a_wcel f0_pofun f2_pofun a_wral a_wa i2_pofun i1_pofun i0_pofun f2_pofun f5_pofun p_ispod $.
$}

$(A strict linear order is a strict partial order.  (Contributed by NM,
       28-Mar-1997.) $)

${
	$v A R  $.
	$d x y R  $.
	$d x y A  $.
	f0_sopo $f class A $.
	f1_sopo $f class R $.
	i0_sopo $f set x $.
	i1_sopo $f set y $.
	p_sopo $p |- ( R Or A -> R Po A ) $= i0_sopo i1_sopo f0_sopo f1_sopo a_df-so f0_sopo f1_sopo a_wor f0_sopo f1_sopo a_wpo i0_sopo a_sup_set_class i1_sopo a_sup_set_class f1_sopo a_wbr i0_sopo a_sup_set_class i1_sopo a_sup_set_class a_wceq i1_sopo a_sup_set_class i0_sopo a_sup_set_class f1_sopo a_wbr a_w3o i1_sopo f0_sopo a_wral i0_sopo f0_sopo a_wral p_simplbi $.
$}

$(Subset theorem for the strict ordering predicate.  (Contributed by NM,
       16-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B R  $.
	$d x y R  $.
	$d x y A  $.
	$d x y B  $.
	f0_soss $f class A $.
	f1_soss $f class B $.
	f2_soss $f class R $.
	i0_soss $f set x $.
	i1_soss $f set y $.
	p_soss $p |- ( A C_ B -> ( R Or B -> R Or A ) ) $= f0_soss f1_soss f2_soss p_poss f0_soss f1_soss i0_soss a_sup_set_class p_ssel f0_soss f1_soss i1_soss a_sup_set_class p_ssel f0_soss f1_soss a_wss i0_soss a_sup_set_class f0_soss a_wcel i0_soss a_sup_set_class f1_soss a_wcel i1_soss a_sup_set_class f0_soss a_wcel i1_soss a_sup_set_class f1_soss a_wcel p_anim12d f0_soss f1_soss a_wss i0_soss a_sup_set_class f0_soss a_wcel i1_soss a_sup_set_class f0_soss a_wcel a_wa i0_soss a_sup_set_class f1_soss a_wcel i1_soss a_sup_set_class f1_soss a_wcel a_wa i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o p_imim1d f0_soss f1_soss a_wss i0_soss a_sup_set_class f1_soss a_wcel i1_soss a_sup_set_class f1_soss a_wcel a_wa i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o a_wi i0_soss a_sup_set_class f0_soss a_wcel i1_soss a_sup_set_class f0_soss a_wcel a_wa i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o a_wi i0_soss i1_soss p_2alimdv i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i0_soss i1_soss f1_soss f1_soss p_r2al i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i0_soss i1_soss f0_soss f0_soss p_r2al f0_soss f1_soss a_wss i0_soss a_sup_set_class f1_soss a_wcel i1_soss a_sup_set_class f1_soss a_wcel a_wa i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o a_wi i1_soss a_wal i0_soss a_wal i0_soss a_sup_set_class f0_soss a_wcel i1_soss a_sup_set_class f0_soss a_wcel a_wa i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o a_wi i1_soss a_wal i0_soss a_wal i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i1_soss f1_soss a_wral i0_soss f1_soss a_wral i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i1_soss f0_soss a_wral i0_soss f0_soss a_wral p_3imtr4g f0_soss f1_soss a_wss f1_soss f2_soss a_wpo f0_soss f2_soss a_wpo i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i1_soss f1_soss a_wral i0_soss f1_soss a_wral i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i1_soss f0_soss a_wral i0_soss f0_soss a_wral p_anim12d i0_soss i1_soss f1_soss f2_soss a_df-so i0_soss i1_soss f0_soss f2_soss a_df-so f0_soss f1_soss a_wss f1_soss f2_soss a_wpo i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i1_soss f1_soss a_wral i0_soss f1_soss a_wral a_wa f0_soss f2_soss a_wpo i0_soss a_sup_set_class i1_soss a_sup_set_class f2_soss a_wbr i0_soss a_sup_set_class i1_soss a_sup_set_class a_wceq i1_soss a_sup_set_class i0_soss a_sup_set_class f2_soss a_wbr a_w3o i1_soss f0_soss a_wral i0_soss f0_soss a_wral a_wa f1_soss f2_soss a_wor f0_soss f2_soss a_wor p_3imtr4g $.
$}

$(Equality theorem for the strict ordering predicate.  (Contributed by NM,
       16-Mar-1997.) $)

${
	$v A R S  $.
	$d x y R  $.
	$d x y S  $.
	$d x y A  $.
	f0_soeq1 $f class A $.
	f1_soeq1 $f class R $.
	f2_soeq1 $f class S $.
	i0_soeq1 $f set x $.
	i1_soeq1 $f set y $.
	p_soeq1 $p |- ( R = S -> ( R Or A <-> S Or A ) ) $= f0_soeq1 f1_soeq1 f2_soeq1 p_poeq1 i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f1_soeq1 f2_soeq1 p_breq f1_soeq1 f2_soeq1 a_wceq i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq p_biidd i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f1_soeq1 f2_soeq1 p_breq f1_soeq1 f2_soeq1 a_wceq i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f1_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f2_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f1_soeq1 a_wbr i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f2_soeq1 a_wbr p_3orbi123d f1_soeq1 f2_soeq1 a_wceq i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f1_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f1_soeq1 a_wbr a_w3o i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f2_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f2_soeq1 a_wbr a_w3o i0_soeq1 i1_soeq1 f0_soeq1 f0_soeq1 p_2ralbidv f1_soeq1 f2_soeq1 a_wceq f0_soeq1 f1_soeq1 a_wpo f0_soeq1 f2_soeq1 a_wpo i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f1_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f1_soeq1 a_wbr a_w3o i1_soeq1 f0_soeq1 a_wral i0_soeq1 f0_soeq1 a_wral i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f2_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f2_soeq1 a_wbr a_w3o i1_soeq1 f0_soeq1 a_wral i0_soeq1 f0_soeq1 a_wral p_anbi12d i0_soeq1 i1_soeq1 f0_soeq1 f1_soeq1 a_df-so i0_soeq1 i1_soeq1 f0_soeq1 f2_soeq1 a_df-so f1_soeq1 f2_soeq1 a_wceq f0_soeq1 f1_soeq1 a_wpo i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f1_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f1_soeq1 a_wbr a_w3o i1_soeq1 f0_soeq1 a_wral i0_soeq1 f0_soeq1 a_wral a_wa f0_soeq1 f2_soeq1 a_wpo i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class f2_soeq1 a_wbr i0_soeq1 a_sup_set_class i1_soeq1 a_sup_set_class a_wceq i1_soeq1 a_sup_set_class i0_soeq1 a_sup_set_class f2_soeq1 a_wbr a_w3o i1_soeq1 f0_soeq1 a_wral i0_soeq1 f0_soeq1 a_wral a_wa f0_soeq1 f1_soeq1 a_wor f0_soeq1 f2_soeq1 a_wor p_3bitr4g $.
$}

$(Equality theorem for the strict ordering predicate.  (Contributed by NM,
     16-Mar-1997.) $)

${
	$v A B R  $.
	f0_soeq2 $f class A $.
	f1_soeq2 $f class B $.
	f2_soeq2 $f class R $.
	p_soeq2 $p |- ( A = B -> ( R Or A <-> R Or B ) ) $= f0_soeq2 f1_soeq2 f2_soeq2 p_soss f1_soeq2 f0_soeq2 f2_soeq2 p_soss f0_soeq2 f1_soeq2 a_wss f1_soeq2 f2_soeq2 a_wor f0_soeq2 f2_soeq2 a_wor a_wi f1_soeq2 f0_soeq2 a_wss f0_soeq2 f2_soeq2 a_wor f1_soeq2 f2_soeq2 a_wor a_wi p_anim12i f0_soeq2 f1_soeq2 p_eqss f1_soeq2 f2_soeq2 a_wor f0_soeq2 f2_soeq2 a_wor p_dfbi2 f0_soeq2 f1_soeq2 a_wss f1_soeq2 f0_soeq2 a_wss a_wa f1_soeq2 f2_soeq2 a_wor f0_soeq2 f2_soeq2 a_wor a_wi f0_soeq2 f2_soeq2 a_wor f1_soeq2 f2_soeq2 a_wor a_wi a_wa f0_soeq2 f1_soeq2 a_wceq f1_soeq2 f2_soeq2 a_wor f0_soeq2 f2_soeq2 a_wor a_wb p_3imtr4i f0_soeq2 f1_soeq2 a_wceq f1_soeq2 f2_soeq2 a_wor f0_soeq2 f2_soeq2 a_wor p_bicomd $.
$}

$(A strict order relation is irreflexive.  (Contributed by NM,
     24-Nov-1995.) $)

${
	$v A B R  $.
	f0_sonr $f class A $.
	f1_sonr $f class B $.
	f2_sonr $f class R $.
	p_sonr $p |- ( ( R Or A /\ B e. A ) -> -. B R B ) $= f0_sonr f2_sonr p_sopo f0_sonr f1_sonr f2_sonr p_poirr f0_sonr f2_sonr a_wor f0_sonr f2_sonr a_wpo f1_sonr f0_sonr a_wcel f1_sonr f1_sonr f2_sonr a_wbr a_wn p_sylan $.
$}

$(A strict order relation is a transitive relation.  (Contributed by NM,
     21-Jan-1996.) $)

${
	$v A B C D R  $.
	f0_sotr $f class A $.
	f1_sotr $f class B $.
	f2_sotr $f class C $.
	f3_sotr $f class D $.
	f4_sotr $f class R $.
	p_sotr $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( B R C /\ C R D ) -> B R D ) ) $= f0_sotr f4_sotr p_sopo f0_sotr f1_sotr f2_sotr f3_sotr f4_sotr p_potr f0_sotr f4_sotr a_wor f0_sotr f4_sotr a_wpo f1_sotr f0_sotr a_wcel f2_sotr f0_sotr a_wcel f3_sotr f0_sotr a_wcel a_w3a f1_sotr f2_sotr f4_sotr a_wbr f2_sotr f3_sotr f4_sotr a_wbr a_wa f1_sotr f3_sotr f4_sotr a_wbr a_wi p_sylan $.
$}

$(A strict order relation is linear (satisfies trichotomy).  (Contributed
       by NM, 21-Jan-1996.) $)

${
	$v A B C R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y R  $.
	f0_solin $f class A $.
	f1_solin $f class B $.
	f2_solin $f class C $.
	f3_solin $f class R $.
	i0_solin $f set x $.
	i1_solin $f set y $.
	p_solin $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B R C \/ B = C \/ C R B ) ) $= i0_solin a_sup_set_class f1_solin i1_solin a_sup_set_class f3_solin p_breq1 i0_solin a_sup_set_class f1_solin i1_solin a_sup_set_class p_eqeq1 i0_solin a_sup_set_class f1_solin i1_solin a_sup_set_class f3_solin p_breq2 i0_solin a_sup_set_class f1_solin a_wceq i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr f1_solin i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq f1_solin i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr i1_solin a_sup_set_class f1_solin f3_solin a_wbr p_3orbi123d i0_solin a_sup_set_class f1_solin a_wceq i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o f1_solin i1_solin a_sup_set_class f3_solin a_wbr f1_solin i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class f1_solin f3_solin a_wbr a_w3o f0_solin f3_solin a_wor p_imbi2d i1_solin a_sup_set_class f2_solin f1_solin f3_solin p_breq2 i1_solin a_sup_set_class f2_solin f1_solin p_eqeq2 i1_solin a_sup_set_class f2_solin f1_solin f3_solin p_breq1 i1_solin a_sup_set_class f2_solin a_wceq f1_solin i1_solin a_sup_set_class f3_solin a_wbr f1_solin f2_solin f3_solin a_wbr f1_solin i1_solin a_sup_set_class a_wceq f1_solin f2_solin a_wceq i1_solin a_sup_set_class f1_solin f3_solin a_wbr f2_solin f1_solin f3_solin a_wbr p_3orbi123d i1_solin a_sup_set_class f2_solin a_wceq f1_solin i1_solin a_sup_set_class f3_solin a_wbr f1_solin i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class f1_solin f3_solin a_wbr a_w3o f1_solin f2_solin f3_solin a_wbr f1_solin f2_solin a_wceq f2_solin f1_solin f3_solin a_wbr a_w3o f0_solin f3_solin a_wor p_imbi2d i0_solin i1_solin f0_solin f3_solin a_df-so i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o i0_solin i1_solin f0_solin f0_solin p_rsp2 i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o i1_solin f0_solin a_wral i0_solin f0_solin a_wral i0_solin a_sup_set_class f0_solin a_wcel i1_solin a_sup_set_class f0_solin a_wcel a_wa i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o a_wi f0_solin f3_solin a_wpo p_adantl f0_solin f3_solin a_wor f0_solin f3_solin a_wpo i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o i1_solin f0_solin a_wral i0_solin f0_solin a_wral a_wa i0_solin a_sup_set_class f0_solin a_wcel i1_solin a_sup_set_class f0_solin a_wcel a_wa i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o a_wi p_sylbi f0_solin f3_solin a_wor i0_solin a_sup_set_class f0_solin a_wcel i1_solin a_sup_set_class f0_solin a_wcel a_wa i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o p_com12 f0_solin f3_solin a_wor i0_solin a_sup_set_class i1_solin a_sup_set_class f3_solin a_wbr i0_solin a_sup_set_class i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class i0_solin a_sup_set_class f3_solin a_wbr a_w3o a_wi f0_solin f3_solin a_wor f1_solin i1_solin a_sup_set_class f3_solin a_wbr f1_solin i1_solin a_sup_set_class a_wceq i1_solin a_sup_set_class f1_solin f3_solin a_wbr a_w3o a_wi f0_solin f3_solin a_wor f1_solin f2_solin f3_solin a_wbr f1_solin f2_solin a_wceq f2_solin f1_solin f3_solin a_wbr a_w3o a_wi i0_solin i1_solin f1_solin f2_solin f0_solin f0_solin p_vtocl2ga f1_solin f0_solin a_wcel f2_solin f0_solin a_wcel a_wa f0_solin f3_solin a_wor f1_solin f2_solin f3_solin a_wbr f1_solin f2_solin a_wceq f2_solin f1_solin f3_solin a_wbr a_w3o p_impcom $.
$}

$(A strict order relation has no 2-cycle loops.  (Contributed by NM,
     21-Jan-1996.) $)

${
	$v A B C R  $.
	f0_so2nr $f class A $.
	f1_so2nr $f class B $.
	f2_so2nr $f class C $.
	f3_so2nr $f class R $.
	p_so2nr $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) ) $= f0_so2nr f3_so2nr p_sopo f0_so2nr f1_so2nr f2_so2nr f3_so2nr p_po2nr f0_so2nr f3_so2nr a_wor f0_so2nr f3_so2nr a_wpo f1_so2nr f0_so2nr a_wcel f2_so2nr f0_so2nr a_wcel a_wa f1_so2nr f2_so2nr f3_so2nr a_wbr f2_so2nr f1_so2nr f3_so2nr a_wbr a_wa a_wn p_sylan $.
$}

$(A strict order relation has no 3-cycle loops.  (Contributed by NM,
     21-Jan-1996.) $)

${
	$v A B C D R  $.
	f0_so3nr $f class A $.
	f1_so3nr $f class B $.
	f2_so3nr $f class C $.
	f3_so3nr $f class D $.
	f4_so3nr $f class R $.
	p_so3nr $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> -. ( B R C /\ C R D /\ D R B ) ) $= f0_so3nr f4_so3nr p_sopo f0_so3nr f1_so3nr f2_so3nr f3_so3nr f4_so3nr p_po3nr f0_so3nr f4_so3nr a_wor f0_so3nr f4_so3nr a_wpo f1_so3nr f0_so3nr a_wcel f2_so3nr f0_so3nr a_wcel f3_so3nr f0_so3nr a_wcel a_w3a f1_so3nr f2_so3nr f4_so3nr a_wbr f2_so3nr f3_so3nr f4_so3nr a_wbr f3_so3nr f1_so3nr f4_so3nr a_wbr a_w3a a_wn p_sylan $.
$}

$(A strict order relation satisfies strict trichotomy.  (Contributed by NM,
     19-Feb-1996.) $)

${
	$v A B C R  $.
	f0_sotric $f class A $.
	f1_sotric $f class B $.
	f2_sotric $f class C $.
	f3_sotric $f class R $.
	p_sotric $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B R C <-> -. ( B = C \/ C R B ) ) ) $= f0_sotric f1_sotric f3_sotric p_sonr f1_sotric f2_sotric f1_sotric f3_sotric p_breq2 f1_sotric f2_sotric a_wceq f1_sotric f1_sotric f3_sotric a_wbr f1_sotric f2_sotric f3_sotric a_wbr p_notbid f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel a_wa f1_sotric f1_sotric f3_sotric a_wbr a_wn f1_sotric f2_sotric a_wceq f1_sotric f2_sotric f3_sotric a_wbr a_wn p_syl5ibcom f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f1_sotric f2_sotric a_wceq f1_sotric f2_sotric f3_sotric a_wbr a_wn a_wi f2_sotric f0_sotric a_wcel p_adantrr f0_sotric f1_sotric f2_sotric f3_sotric p_so2nr f1_sotric f2_sotric f3_sotric a_wbr f2_sotric f1_sotric f3_sotric a_wbr p_imnan f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f2_sotric f0_sotric a_wcel a_wa a_wa f1_sotric f2_sotric f3_sotric a_wbr f2_sotric f1_sotric f3_sotric a_wbr a_wa a_wn f1_sotric f2_sotric f3_sotric a_wbr f2_sotric f1_sotric f3_sotric a_wbr a_wn a_wi p_sylibr f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f2_sotric f0_sotric a_wcel a_wa a_wa f1_sotric f2_sotric f3_sotric a_wbr f2_sotric f1_sotric f3_sotric a_wbr p_con2d f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f2_sotric f0_sotric a_wcel a_wa a_wa f1_sotric f2_sotric a_wceq f1_sotric f2_sotric f3_sotric a_wbr a_wn f2_sotric f1_sotric f3_sotric a_wbr p_jaod f0_sotric f1_sotric f2_sotric f3_sotric p_solin f1_sotric f2_sotric f3_sotric a_wbr f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr p_3orass f1_sotric f2_sotric f3_sotric a_wbr f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_wo a_df-or f1_sotric f2_sotric f3_sotric a_wbr f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_w3o f1_sotric f2_sotric f3_sotric a_wbr f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_wo a_wo f1_sotric f2_sotric f3_sotric a_wbr a_wn f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_wo a_wi p_bitri f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f2_sotric f0_sotric a_wcel a_wa a_wa f1_sotric f2_sotric f3_sotric a_wbr f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_w3o f1_sotric f2_sotric f3_sotric a_wbr a_wn f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_wo a_wi p_sylib f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f2_sotric f0_sotric a_wcel a_wa a_wa f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_wo f1_sotric f2_sotric f3_sotric a_wbr a_wn p_impbid f0_sotric f3_sotric a_wor f1_sotric f0_sotric a_wcel f2_sotric f0_sotric a_wcel a_wa a_wa f1_sotric f2_sotric a_wceq f2_sotric f1_sotric f3_sotric a_wbr a_wo f1_sotric f2_sotric f3_sotric a_wbr p_con2bid $.
$}

$(Trichotomy law for strict order relation.  (Contributed by NM,
     9-Apr-1996.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B C R  $.
	f0_sotrieq $f class A $.
	f1_sotrieq $f class B $.
	f2_sotrieq $f class C $.
	f3_sotrieq $f class R $.
	p_sotrieq $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B = C <-> -. ( B R C \/ C R B ) ) ) $= f0_sotrieq f1_sotrieq f3_sotrieq p_sonr f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f1_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wn f2_sotrieq f0_sotrieq a_wcel p_adantrr f1_sotrieq f1_sotrieq f3_sotrieq a_wbr p_pm1.2 f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f2_sotrieq f0_sotrieq a_wcel a_wa a_wa f1_sotrieq f1_sotrieq f3_sotrieq a_wbr f1_sotrieq f1_sotrieq f3_sotrieq a_wbr f1_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo p_nsyl f1_sotrieq f2_sotrieq f1_sotrieq f3_sotrieq p_breq2 f1_sotrieq f2_sotrieq f1_sotrieq f3_sotrieq p_breq1 f1_sotrieq f2_sotrieq a_wceq f1_sotrieq f1_sotrieq f3_sotrieq a_wbr f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f1_sotrieq f1_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr p_orbi12d f1_sotrieq f2_sotrieq a_wceq f1_sotrieq f1_sotrieq f3_sotrieq a_wbr f1_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo p_notbid f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f2_sotrieq f0_sotrieq a_wcel a_wa a_wa f1_sotrieq f1_sotrieq f3_sotrieq a_wbr f1_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_wn f1_sotrieq f2_sotrieq a_wceq f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_wn p_syl5ibcom f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f2_sotrieq f0_sotrieq a_wcel a_wa a_wa f1_sotrieq f2_sotrieq a_wceq f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo p_con2d f0_sotrieq f1_sotrieq f2_sotrieq f3_sotrieq p_solin f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f1_sotrieq f2_sotrieq a_wceq f2_sotrieq f1_sotrieq f3_sotrieq a_wbr p_3orass f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f1_sotrieq f2_sotrieq a_wceq f2_sotrieq f1_sotrieq f3_sotrieq a_wbr p_or12 f1_sotrieq f2_sotrieq a_wceq f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_df-or f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f1_sotrieq f2_sotrieq a_wceq f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_w3o f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f1_sotrieq f2_sotrieq a_wceq f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_wo f1_sotrieq f2_sotrieq a_wceq f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_wo f1_sotrieq f2_sotrieq a_wceq a_wn f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_wi p_3bitri f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f2_sotrieq f0_sotrieq a_wcel a_wa a_wa f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f1_sotrieq f2_sotrieq a_wceq f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_w3o f1_sotrieq f2_sotrieq a_wceq a_wn f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo a_wi p_sylib f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f2_sotrieq f0_sotrieq a_wcel a_wa a_wa f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo f1_sotrieq f2_sotrieq a_wceq a_wn p_impbid f0_sotrieq f3_sotrieq a_wor f1_sotrieq f0_sotrieq a_wcel f2_sotrieq f0_sotrieq a_wcel a_wa a_wa f1_sotrieq f2_sotrieq f3_sotrieq a_wbr f2_sotrieq f1_sotrieq f3_sotrieq a_wbr a_wo f1_sotrieq f2_sotrieq a_wceq p_con2bid $.
$}

$(Trichotomy law for strict order relation.  (Contributed by NM,
     5-May-1999.) $)

${
	$v A B C R  $.
	f0_sotrieq2 $f class A $.
	f1_sotrieq2 $f class B $.
	f2_sotrieq2 $f class C $.
	f3_sotrieq2 $f class R $.
	p_sotrieq2 $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) -> ( B = C <-> ( -. B R C /\ -. C R B ) ) ) $= f0_sotrieq2 f1_sotrieq2 f2_sotrieq2 f3_sotrieq2 p_sotrieq f1_sotrieq2 f2_sotrieq2 f3_sotrieq2 a_wbr f2_sotrieq2 f1_sotrieq2 f3_sotrieq2 a_wbr p_ioran f0_sotrieq2 f3_sotrieq2 a_wor f1_sotrieq2 f0_sotrieq2 a_wcel f2_sotrieq2 f0_sotrieq2 a_wcel a_wa a_wa f1_sotrieq2 f2_sotrieq2 a_wceq f1_sotrieq2 f2_sotrieq2 f3_sotrieq2 a_wbr f2_sotrieq2 f1_sotrieq2 f3_sotrieq2 a_wbr a_wo a_wn f1_sotrieq2 f2_sotrieq2 f3_sotrieq2 a_wbr a_wn f2_sotrieq2 f1_sotrieq2 f3_sotrieq2 a_wbr a_wn a_wa p_syl6bb $.
$}

$(A transitivity relation.  (Read ` B <_ C ` and ` C < D ` implies
     ` B < D ` .)  (Contributed by Mario Carneiro, 10-May-2013.) $)

${
	$v A B C D R  $.
	f0_sotr2 $f class A $.
	f1_sotr2 $f class B $.
	f2_sotr2 $f class C $.
	f3_sotr2 $f class D $.
	f4_sotr2 $f class R $.
	p_sotr2 $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( -. C R B /\ C R D ) -> B R D ) ) $= f0_sotr2 f2_sotr2 f1_sotr2 f4_sotr2 p_sotric f0_sotr2 f4_sotr2 a_wor f2_sotr2 f0_sotr2 a_wcel f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f1_sotr2 f4_sotr2 a_wbr f2_sotr2 f1_sotr2 a_wceq f1_sotr2 f2_sotr2 f4_sotr2 a_wbr a_wo a_wn a_wb p_ancom2s f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f2_sotr2 f1_sotr2 f4_sotr2 a_wbr f2_sotr2 f1_sotr2 a_wceq f1_sotr2 f2_sotr2 f4_sotr2 a_wbr a_wo a_wn a_wb f3_sotr2 f0_sotr2 a_wcel p_3adantr3 f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f3_sotr2 f0_sotr2 a_wcel a_w3a a_wa f2_sotr2 f1_sotr2 f4_sotr2 a_wbr f2_sotr2 f1_sotr2 a_wceq f1_sotr2 f2_sotr2 f4_sotr2 a_wbr a_wo p_con2bid f2_sotr2 f1_sotr2 f3_sotr2 f4_sotr2 p_breq1 f2_sotr2 f1_sotr2 a_wceq f2_sotr2 f3_sotr2 f4_sotr2 a_wbr f1_sotr2 f3_sotr2 f4_sotr2 a_wbr p_biimpd f2_sotr2 f1_sotr2 a_wceq f2_sotr2 f3_sotr2 f4_sotr2 a_wbr f1_sotr2 f3_sotr2 f4_sotr2 a_wbr a_wi a_wi f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f3_sotr2 f0_sotr2 a_wcel a_w3a a_wa p_a1i f0_sotr2 f1_sotr2 f2_sotr2 f3_sotr2 f4_sotr2 p_sotr f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f3_sotr2 f0_sotr2 a_wcel a_w3a a_wa f1_sotr2 f2_sotr2 f4_sotr2 a_wbr f2_sotr2 f3_sotr2 f4_sotr2 a_wbr f1_sotr2 f3_sotr2 f4_sotr2 a_wbr p_exp3a f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f3_sotr2 f0_sotr2 a_wcel a_w3a a_wa f2_sotr2 f1_sotr2 a_wceq f2_sotr2 f3_sotr2 f4_sotr2 a_wbr f1_sotr2 f3_sotr2 f4_sotr2 a_wbr a_wi f1_sotr2 f2_sotr2 f4_sotr2 a_wbr p_jaod f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f3_sotr2 f0_sotr2 a_wcel a_w3a a_wa f2_sotr2 f1_sotr2 f4_sotr2 a_wbr a_wn f2_sotr2 f1_sotr2 a_wceq f1_sotr2 f2_sotr2 f4_sotr2 a_wbr a_wo f2_sotr2 f3_sotr2 f4_sotr2 a_wbr f1_sotr2 f3_sotr2 f4_sotr2 a_wbr a_wi p_sylbird f0_sotr2 f4_sotr2 a_wor f1_sotr2 f0_sotr2 a_wcel f2_sotr2 f0_sotr2 a_wcel f3_sotr2 f0_sotr2 a_wcel a_w3a a_wa f2_sotr2 f1_sotr2 f4_sotr2 a_wbr a_wn f2_sotr2 f3_sotr2 f4_sotr2 a_wbr f1_sotr2 f3_sotr2 f4_sotr2 a_wbr p_imp3a $.
$}

$(An irreflexive, transitive, linear relation is a strict ordering.
       (Contributed by NM, 21-Jan-1996.)  (Revised by Mario Carneiro,
       9-Jul-2014.) $)

${
	$v ph x y A R  $.
	$d x y R  $.
	$d x y A  $.
	$d x y ph  $.
	f0_issod $f wff ph $.
	f1_issod $f set x $.
	f2_issod $f set y $.
	f3_issod $f class A $.
	f4_issod $f class R $.
	e0_issod $e |- ( ph -> R Po A ) $.
	e1_issod $e |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x R y \/ x = y \/ y R x ) ) $.
	p_issod $p |- ( ph -> R Or A ) $= e0_issod e1_issod f0_issod f1_issod a_sup_set_class f2_issod a_sup_set_class f4_issod a_wbr f1_issod a_sup_set_class f2_issod a_sup_set_class a_wceq f2_issod a_sup_set_class f1_issod a_sup_set_class f4_issod a_wbr a_w3o f1_issod f2_issod f3_issod f3_issod p_ralrimivva f1_issod f2_issod f3_issod f4_issod a_df-so f0_issod f3_issod f4_issod a_wpo f1_issod a_sup_set_class f2_issod a_sup_set_class f4_issod a_wbr f1_issod a_sup_set_class f2_issod a_sup_set_class a_wceq f2_issod a_sup_set_class f1_issod a_sup_set_class f4_issod a_wbr a_w3o f2_issod f3_issod a_wral f1_issod f3_issod a_wral f3_issod f4_issod a_wor p_sylanbrc $.
$}

$(An irreflexive, transitive, linear relation is a strict ordering.
       (Contributed by NM, 21-Jan-1996.)  (Revised by Mario Carneiro,
       9-Jul-2014.) $)

${
	$v x y z A R  $.
	$d x y z R  $.
	$d x y z A  $.
	f0_issoi $f set x $.
	f1_issoi $f set y $.
	f2_issoi $f set z $.
	f3_issoi $f class A $.
	f4_issoi $f class R $.
	e0_issoi $e |- ( x e. A -> -. x R x ) $.
	e1_issoi $e |- ( ( x e. A /\ y e. A /\ z e. A ) -> ( ( x R y /\ y R z ) -> x R z ) ) $.
	e2_issoi $e |- ( ( x e. A /\ y e. A ) -> ( x R y \/ x = y \/ y R x ) ) $.
	p_issoi $p |- R Or A $= e0_issoi f0_issoi a_sup_set_class f3_issoi a_wcel f0_issoi a_sup_set_class f0_issoi a_sup_set_class f4_issoi a_wbr a_wn a_wtru p_adantl e1_issoi f0_issoi a_sup_set_class f3_issoi a_wcel f1_issoi a_sup_set_class f3_issoi a_wcel f2_issoi a_sup_set_class f3_issoi a_wcel a_w3a f0_issoi a_sup_set_class f1_issoi a_sup_set_class f4_issoi a_wbr f1_issoi a_sup_set_class f2_issoi a_sup_set_class f4_issoi a_wbr a_wa f0_issoi a_sup_set_class f2_issoi a_sup_set_class f4_issoi a_wbr a_wi a_wtru p_adantl a_wtru f0_issoi f1_issoi f2_issoi f3_issoi f4_issoi p_ispod e2_issoi f0_issoi a_sup_set_class f3_issoi a_wcel f1_issoi a_sup_set_class f3_issoi a_wcel a_wa f0_issoi a_sup_set_class f1_issoi a_sup_set_class f4_issoi a_wbr f0_issoi a_sup_set_class f1_issoi a_sup_set_class a_wceq f1_issoi a_sup_set_class f0_issoi a_sup_set_class f4_issoi a_wbr a_w3o a_wtru p_adantl a_wtru f0_issoi f1_issoi f3_issoi f4_issoi p_issod f3_issoi f4_issoi a_wor p_trud $.
$}

$(Deduce strict ordering from its properties.  (Contributed by NM,
       29-Jan-1996.)  (Revised by Mario Carneiro, 9-Jul-2014.) $)

${
	$v x y z A R  $.
	$d x y z R  $.
	$d x y z A  $.
	f0_isso2i $f set x $.
	f1_isso2i $f set y $.
	f2_isso2i $f set z $.
	f3_isso2i $f class A $.
	f4_isso2i $f class R $.
	e0_isso2i $e |- ( ( x e. A /\ y e. A ) -> ( x R y <-> -. ( x = y \/ y R x ) ) ) $.
	e1_isso2i $e |- ( ( x e. A /\ y e. A /\ z e. A ) -> ( ( x R y /\ y R z ) -> x R z ) ) $.
	p_isso2i $p |- R Or A $= f0_isso2i a_sup_set_class p_eqid f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr p_orci f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f3_isso2i p_eleq1 f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f3_isso2i a_wcel f0_isso2i a_sup_set_class f3_isso2i a_wcel f0_isso2i a_sup_set_class f3_isso2i a_wcel p_anbi2d f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class p_eqeq2 f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i p_breq1 f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr p_orbi12d f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i p_breq2 f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr p_notbid f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr a_wn f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wn p_bibi12d f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f3_isso2i a_wcel f1_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f3_isso2i a_wcel f0_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr a_wn a_wb f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wn a_wb p_imbi12d e0_isso2i f0_isso2i a_sup_set_class f3_isso2i a_wcel f1_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo p_con2bid f0_isso2i a_sup_set_class f3_isso2i a_wcel f1_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr a_wn a_wb a_wi f0_isso2i a_sup_set_class f3_isso2i a_wcel f0_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wn a_wb a_wi f1_isso2i f0_isso2i p_chvarv f0_isso2i a_sup_set_class f3_isso2i a_wcel f0_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class a_wceq f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wn p_mpbii f0_isso2i a_sup_set_class f3_isso2i a_wcel f0_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wn p_anidms e1_isso2i e0_isso2i f0_isso2i a_sup_set_class f3_isso2i a_wcel f1_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo p_con2bid f0_isso2i a_sup_set_class f3_isso2i a_wcel f1_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr a_wn p_biimprd f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr p_3orass f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo a_df-or f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_w3o f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo a_wo f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr a_wn f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo a_wi p_bitri f0_isso2i a_sup_set_class f3_isso2i a_wcel f1_isso2i a_sup_set_class f3_isso2i a_wcel a_wa f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr a_wn f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_wo a_wi f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class f4_isso2i a_wbr f0_isso2i a_sup_set_class f1_isso2i a_sup_set_class a_wceq f1_isso2i a_sup_set_class f0_isso2i a_sup_set_class f4_isso2i a_wbr a_w3o p_sylibr f0_isso2i f1_isso2i f2_isso2i f3_isso2i f4_isso2i p_issoi $.
$}

$(Any relation is a strict ordering of the empty set.  (Contributed by NM,
       16-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v R  $.
	$d x y R  $.
	f0_so0 $f class R $.
	i0_so0 $f set x $.
	i1_so0 $f set y $.
	p_so0 $p |- R Or (/) $= f0_so0 p_po0 i0_so0 a_sup_set_class i1_so0 a_sup_set_class f0_so0 a_wbr i0_so0 a_sup_set_class i1_so0 a_sup_set_class a_wceq i1_so0 a_sup_set_class i0_so0 a_sup_set_class f0_so0 a_wbr a_w3o i1_so0 a_c0 a_wral i0_so0 p_ral0 i0_so0 i1_so0 a_c0 f0_so0 a_df-so a_c0 f0_so0 a_wor a_c0 f0_so0 a_wpo i0_so0 a_sup_set_class i1_so0 a_sup_set_class f0_so0 a_wbr i0_so0 a_sup_set_class i1_so0 a_sup_set_class a_wceq i1_so0 a_sup_set_class i0_so0 a_sup_set_class f0_so0 a_wbr a_w3o i1_so0 a_c0 a_wral i0_so0 a_c0 a_wral p_mpbir2an $.
$}

$(A totally ordered set has at most one minimal element.  (Contributed by
       Mario Carneiro, 24-Jun-2015.)  (Revised by NM, 16-Jun-2017.) $)

${
	$v x y A R  $.
	$d x y z A  $.
	$d x y z R  $.
	f0_somo $f set x $.
	f1_somo $f set y $.
	f2_somo $f class A $.
	f3_somo $f class R $.
	i0_somo $f set z $.
	p_somo $p |- ( R Or A -> E* x e. A A. y e. A -. y R x ) $= f1_somo a_sup_set_class f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo p_breq1 f1_somo a_sup_set_class f0_somo a_sup_set_class a_wceq f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr p_notbid f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f0_somo a_sup_set_class f2_somo p_rspcv f1_somo a_sup_set_class i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo p_breq1 f1_somo a_sup_set_class i0_somo a_sup_set_class a_wceq f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr p_notbid f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo i0_somo a_sup_set_class f2_somo p_rspcv f0_somo a_sup_set_class f2_somo a_wcel f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn i0_somo a_sup_set_class f2_somo a_wcel f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn p_im2anan9 f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn a_wa p_ancomsd f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn a_wa p_imp f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr p_ioran f2_somo f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo p_solin f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_df-3or f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr p_or32 f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_w3o f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq a_wo i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wo f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wo f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq a_wo p_bitri f2_somo f3_somo a_wor f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_w3o f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wo f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq a_wo p_sylib f2_somo f3_somo a_wor f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wo f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq p_ord f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wo a_wn f2_somo f3_somo a_wor f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq p_syl5bir f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral a_wa a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn i0_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn a_wa f2_somo f3_somo a_wor f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq p_syl5 f2_somo f3_somo a_wor f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq p_exp4b f2_somo f3_somo a_wor f0_somo a_sup_set_class f2_somo a_wcel i0_somo a_sup_set_class f2_somo a_wcel a_wa f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq a_wi p_pm2.43d f2_somo f3_somo a_wor f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq a_wi f0_somo i0_somo f2_somo f2_somo p_ralrimivv f0_somo a_sup_set_class i0_somo a_sup_set_class f1_somo a_sup_set_class f3_somo p_breq2 f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr p_notbid f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo p_ralbidv f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f0_somo i0_somo f2_somo p_rmo4 f2_somo f3_somo a_wor f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f1_somo a_sup_set_class i0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral a_wa f0_somo a_sup_set_class i0_somo a_sup_set_class a_wceq a_wi i0_somo f2_somo a_wral f0_somo f2_somo a_wral f1_somo a_sup_set_class f0_somo a_sup_set_class f3_somo a_wbr a_wn f1_somo f2_somo a_wral f0_somo f2_somo a_wrmo p_sylibr $.
$}


