$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Partial_and_complete_ordering.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Founded and well-ordering relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new constant symbols. $)

$c Fr $.

$(Well-founded predicate symbol (read: 'well-founded'). $)

$c Se $.

$(Set-like predicate symbol (read: 'set-like'). $)

$c We $.

$(Well-ordering predicate symbol (read: 'well-orders') $)

$(Extend wff notation to include the well-founded predicate.  Read:  ' ` R `
     is a well-founded relation on ` A ` .' $)

${
	$v A R  $.
	f0_wfr $f class A $.
	f1_wfr $f class R $.
	a_wfr $a wff R Fr A $.
$}

$(Extend wff notation to include the set-like predicate.  Read:  ' ` R ` is
     set-like on ` A ` .' $)

${
	$v A R  $.
	f0_wse $f class A $.
	f1_wse $f class R $.
	a_wse $a wff R Se A $.
$}

$(Extend wff notation to include the well-ordering predicate.
     Read:  ' ` R ` well-orders ` A ` .' $)

${
	$v A R  $.
	f0_wwe $f class A $.
	f1_wwe $f class R $.
	a_wwe $a wff R We A $.
$}

$(Define the well-founded relation predicate.  Definition 6.24(1) of
       [TakeutiZaring] p. 30.  For alternate definitions, see ~ dffr2 and
       ~ dffr3 .  (Contributed by NM, 3-Apr-1994.) $)

${
	$v x y z A R  $.
	$d x y z R  $.
	$d x y z A  $.
	f0_df-fr $f set x $.
	f1_df-fr $f set y $.
	f2_df-fr $f set z $.
	f3_df-fr $f class A $.
	f4_df-fr $f class R $.
	a_df-fr $a |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x A. z e. x -. z R y ) ) $.
$}

$(Define the set-like predicate.  (Contributed by Mario Carneiro,
       19-Nov-2014.) $)

${
	$v x y A R  $.
	$d x y R  $.
	$d x y A  $.
	f0_df-se $f set x $.
	f1_df-se $f set y $.
	f2_df-se $f class A $.
	f3_df-se $f class R $.
	a_df-se $a |- ( R Se A <-> A. x e. A { y e. A | y R x } e. _V ) $.
$}

$(Define the well-ordering predicate.  For an alternate definition, see
     ~ dfwe2 .  (Contributed by NM, 3-Apr-1994.) $)

${
	$v A R  $.
	f0_df-we $f class A $.
	f1_df-we $f class R $.
	a_df-we $a |- ( R We A <-> ( R Fr A /\ R Or A ) ) $.
$}

$(Property of well-founded relation (one direction of definition).
       (Contributed by NM, 18-Mar-1997.) $)

${
	$v x y A B C R  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z R  $.
	$d x y  $.
	f0_fri $f set x $.
	f1_fri $f set y $.
	f2_fri $f class A $.
	f3_fri $f class B $.
	f4_fri $f class C $.
	f5_fri $f class R $.
	i0_fri $f set z $.
	p_fri $p |- ( ( ( B e. C /\ R Fr A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E. x e. B A. y e. B -. y R x ) $= i0_fri f0_fri f1_fri f2_fri f5_fri a_df-fr i0_fri a_sup_set_class f3_fri f2_fri p_sseq1 i0_fri a_sup_set_class f3_fri a_c0 p_neeq1 i0_fri a_sup_set_class f3_fri a_wceq i0_fri a_sup_set_class f2_fri a_wss f3_fri f2_fri a_wss i0_fri a_sup_set_class a_c0 a_wne f3_fri a_c0 a_wne p_anbi12d f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri i0_fri a_sup_set_class f3_fri p_raleq f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri i0_fri a_sup_set_class a_wral f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri f3_fri a_wral f0_fri i0_fri a_sup_set_class f3_fri p_rexeqbi1dv i0_fri a_sup_set_class f3_fri a_wceq i0_fri a_sup_set_class f2_fri a_wss i0_fri a_sup_set_class a_c0 a_wne a_wa f3_fri f2_fri a_wss f3_fri a_c0 a_wne a_wa f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri i0_fri a_sup_set_class a_wral f0_fri i0_fri a_sup_set_class a_wrex f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri f3_fri a_wral f0_fri f3_fri a_wrex p_imbi12d i0_fri a_sup_set_class f2_fri a_wss i0_fri a_sup_set_class a_c0 a_wne a_wa f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri i0_fri a_sup_set_class a_wral f0_fri i0_fri a_sup_set_class a_wrex a_wi f3_fri f2_fri a_wss f3_fri a_c0 a_wne a_wa f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri f3_fri a_wral f0_fri f3_fri a_wrex a_wi i0_fri f3_fri f4_fri p_spcgv f2_fri f5_fri a_wfr i0_fri a_sup_set_class f2_fri a_wss i0_fri a_sup_set_class a_c0 a_wne a_wa f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri i0_fri a_sup_set_class a_wral f0_fri i0_fri a_sup_set_class a_wrex a_wi i0_fri a_wal f3_fri f4_fri a_wcel f3_fri f2_fri a_wss f3_fri a_c0 a_wne a_wa f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri f3_fri a_wral f0_fri f3_fri a_wrex a_wi p_syl5bi f3_fri f4_fri a_wcel f2_fri f5_fri a_wfr f3_fri f2_fri a_wss f3_fri a_c0 a_wne a_wa f1_fri a_sup_set_class f0_fri a_sup_set_class f5_fri a_wbr a_wn f1_fri f3_fri a_wral f0_fri f3_fri a_wrex p_imp31 $.
$}

$(The ` R ` -preimage of an element of the base set in a set-like relation
       is a set.  (Contributed by Mario Carneiro, 19-Nov-2014.) $)

${
	$v x A B R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y R  $.
	$d x y  $.
	f0_seex $f set x $.
	f1_seex $f class A $.
	f2_seex $f class B $.
	f3_seex $f class R $.
	i0_seex $f set y $.
	p_seex $p |- ( ( R Se A /\ B e. A ) -> { x e. A | x R B } e. _V ) $= i0_seex f0_seex f1_seex f3_seex a_df-se i0_seex a_sup_set_class f2_seex f0_seex a_sup_set_class f3_seex p_breq2 i0_seex a_sup_set_class f2_seex a_wceq f0_seex a_sup_set_class i0_seex a_sup_set_class f3_seex a_wbr f0_seex a_sup_set_class f2_seex f3_seex a_wbr f0_seex f1_seex p_rabbidv i0_seex a_sup_set_class f2_seex a_wceq f0_seex a_sup_set_class i0_seex a_sup_set_class f3_seex a_wbr f0_seex f1_seex a_crab f0_seex a_sup_set_class f2_seex f3_seex a_wbr f0_seex f1_seex a_crab a_cvv p_eleq1d f0_seex a_sup_set_class i0_seex a_sup_set_class f3_seex a_wbr f0_seex f1_seex a_crab a_cvv a_wcel f0_seex a_sup_set_class f2_seex f3_seex a_wbr f0_seex f1_seex a_crab a_cvv a_wcel i0_seex f2_seex f1_seex p_rspccva f1_seex f3_seex a_wse f0_seex a_sup_set_class i0_seex a_sup_set_class f3_seex a_wbr f0_seex f1_seex a_crab a_cvv a_wcel i0_seex f1_seex a_wral f2_seex f1_seex a_wcel f0_seex a_sup_set_class f2_seex f3_seex a_wbr f0_seex f1_seex a_crab a_cvv a_wcel p_sylanb $.
$}

$(Any relation on a set is set-like on it.  (Contributed by Mario
       Carneiro, 22-Jun-2015.) $)

${
	$v A R V  $.
	$d x y A  $.
	$d x y  $.
	$d x y R  $.
	$d x y V  $.
	f0_exse $f class A $.
	f1_exse $f class R $.
	f2_exse $f class V $.
	i0_exse $f set x $.
	i1_exse $f set y $.
	p_exse $p |- ( A e. V -> R Se A ) $= i1_exse a_sup_set_class i0_exse a_sup_set_class f1_exse a_wbr i1_exse f0_exse f2_exse p_rabexg f0_exse f2_exse a_wcel i1_exse a_sup_set_class i0_exse a_sup_set_class f1_exse a_wbr i1_exse f0_exse a_crab a_cvv a_wcel i0_exse f0_exse p_ralrimivw i0_exse i1_exse f0_exse f1_exse a_df-se f0_exse f2_exse a_wcel i1_exse a_sup_set_class i0_exse a_sup_set_class f1_exse a_wbr i1_exse f0_exse a_crab a_cvv a_wcel i0_exse f0_exse a_wral f0_exse f1_exse a_wse p_sylibr $.
$}

$(Alternate definition of well-founded relation.  Similar to Definition
       6.21 of [TakeutiZaring] p. 30.  (Contributed by NM, 17-Feb-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.)  (Proof shortened by
       Mario Carneiro, 23-Jun-2015.) $)

${
	$v x y z A R  $.
	$d x y z A  $.
	$d x y z R  $.
	f0_dffr2 $f set x $.
	f1_dffr2 $f set y $.
	f2_dffr2 $f set z $.
	f3_dffr2 $f class A $.
	f4_dffr2 $f class R $.
	p_dffr2 $p |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x { z e. x | z R y } = (/) ) ) $= f0_dffr2 f1_dffr2 f2_dffr2 f3_dffr2 f4_dffr2 a_df-fr f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr f2_dffr2 f0_dffr2 a_sup_set_class p_rabeq0 f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr f2_dffr2 f0_dffr2 a_sup_set_class a_crab a_c0 a_wceq f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr a_wn f2_dffr2 f0_dffr2 a_sup_set_class a_wral f1_dffr2 f0_dffr2 a_sup_set_class p_rexbii f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr f2_dffr2 f0_dffr2 a_sup_set_class a_crab a_c0 a_wceq f1_dffr2 f0_dffr2 a_sup_set_class a_wrex f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr a_wn f2_dffr2 f0_dffr2 a_sup_set_class a_wral f1_dffr2 f0_dffr2 a_sup_set_class a_wrex f0_dffr2 a_sup_set_class f3_dffr2 a_wss f0_dffr2 a_sup_set_class a_c0 a_wne a_wa p_imbi2i f0_dffr2 a_sup_set_class f3_dffr2 a_wss f0_dffr2 a_sup_set_class a_c0 a_wne a_wa f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr f2_dffr2 f0_dffr2 a_sup_set_class a_crab a_c0 a_wceq f1_dffr2 f0_dffr2 a_sup_set_class a_wrex a_wi f0_dffr2 a_sup_set_class f3_dffr2 a_wss f0_dffr2 a_sup_set_class a_c0 a_wne a_wa f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr a_wn f2_dffr2 f0_dffr2 a_sup_set_class a_wral f1_dffr2 f0_dffr2 a_sup_set_class a_wrex a_wi f0_dffr2 p_albii f3_dffr2 f4_dffr2 a_wfr f0_dffr2 a_sup_set_class f3_dffr2 a_wss f0_dffr2 a_sup_set_class a_c0 a_wne a_wa f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr a_wn f2_dffr2 f0_dffr2 a_sup_set_class a_wral f1_dffr2 f0_dffr2 a_sup_set_class a_wrex a_wi f0_dffr2 a_wal f0_dffr2 a_sup_set_class f3_dffr2 a_wss f0_dffr2 a_sup_set_class a_c0 a_wne a_wa f2_dffr2 a_sup_set_class f1_dffr2 a_sup_set_class f4_dffr2 a_wbr f2_dffr2 f0_dffr2 a_sup_set_class a_crab a_c0 a_wceq f1_dffr2 f0_dffr2 a_sup_set_class a_wrex a_wi f0_dffr2 a_wal p_bitr4i $.
$}

$(Property of well-founded relation (one direction of definition using
       class variables).  (Contributed by NM, 17-Feb-2004.)  (Revised by Mario
       Carneiro, 19-Nov-2014.) $)

${
	$v x y A B R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y R  $.
	f0_frc $f set x $.
	f1_frc $f set y $.
	f2_frc $f class A $.
	f3_frc $f class B $.
	f4_frc $f class R $.
	e0_frc $e |- B e. _V $.
	p_frc $p |- ( ( R Fr A /\ B C_ A /\ B =/= (/) ) -> E. x e. B { y e. B | y R x } = (/) ) $= e0_frc f0_frc f1_frc f2_frc f3_frc a_cvv f4_frc p_fri f3_frc a_cvv a_wcel f2_frc f4_frc a_wfr f3_frc f2_frc a_wss f3_frc a_c0 a_wne a_wa f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr a_wn f1_frc f3_frc a_wral f0_frc f3_frc a_wrex p_mpanl1 f2_frc f4_frc a_wfr f3_frc f2_frc a_wss f3_frc a_c0 a_wne f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr a_wn f1_frc f3_frc a_wral f0_frc f3_frc a_wrex p_3impb f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr f1_frc f3_frc p_rabeq0 f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr f1_frc f3_frc a_crab a_c0 a_wceq f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr a_wn f1_frc f3_frc a_wral f0_frc f3_frc p_rexbii f2_frc f4_frc a_wfr f3_frc f2_frc a_wss f3_frc a_c0 a_wne a_w3a f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr a_wn f1_frc f3_frc a_wral f0_frc f3_frc a_wrex f1_frc a_sup_set_class f0_frc a_sup_set_class f4_frc a_wbr f1_frc f3_frc a_crab a_c0 a_wceq f0_frc f3_frc a_wrex p_sylibr $.
$}

$(Subset theorem for the well-founded predicate.  Exercise 1 of
       [TakeutiZaring] p. 31.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)

${
	$v A B R  $.
	$d x y z A  $.
	$d x y z B  $.
	$d x y z R  $.
	$d x y  $.
	f0_frss $f class A $.
	f1_frss $f class B $.
	f2_frss $f class R $.
	i0_frss $f set x $.
	i1_frss $f set y $.
	i2_frss $f set z $.
	p_frss $p |- ( A C_ B -> ( R Fr B -> R Fr A ) ) $= i0_frss a_sup_set_class f0_frss f1_frss p_sstr2 i0_frss a_sup_set_class f0_frss a_wss f0_frss f1_frss a_wss i0_frss a_sup_set_class f1_frss a_wss p_com12 f0_frss f1_frss a_wss i0_frss a_sup_set_class f0_frss a_wss i0_frss a_sup_set_class f1_frss a_wss i0_frss a_sup_set_class a_c0 a_wne p_anim1d f0_frss f1_frss a_wss i0_frss a_sup_set_class f0_frss a_wss i0_frss a_sup_set_class a_c0 a_wne a_wa i0_frss a_sup_set_class f1_frss a_wss i0_frss a_sup_set_class a_c0 a_wne a_wa i2_frss a_sup_set_class i1_frss a_sup_set_class f2_frss a_wbr a_wn i2_frss i0_frss a_sup_set_class a_wral i1_frss i0_frss a_sup_set_class a_wrex p_imim1d f0_frss f1_frss a_wss i0_frss a_sup_set_class f1_frss a_wss i0_frss a_sup_set_class a_c0 a_wne a_wa i2_frss a_sup_set_class i1_frss a_sup_set_class f2_frss a_wbr a_wn i2_frss i0_frss a_sup_set_class a_wral i1_frss i0_frss a_sup_set_class a_wrex a_wi i0_frss a_sup_set_class f0_frss a_wss i0_frss a_sup_set_class a_c0 a_wne a_wa i2_frss a_sup_set_class i1_frss a_sup_set_class f2_frss a_wbr a_wn i2_frss i0_frss a_sup_set_class a_wral i1_frss i0_frss a_sup_set_class a_wrex a_wi i0_frss p_alimdv i0_frss i1_frss i2_frss f1_frss f2_frss a_df-fr i0_frss i1_frss i2_frss f0_frss f2_frss a_df-fr f0_frss f1_frss a_wss i0_frss a_sup_set_class f1_frss a_wss i0_frss a_sup_set_class a_c0 a_wne a_wa i2_frss a_sup_set_class i1_frss a_sup_set_class f2_frss a_wbr a_wn i2_frss i0_frss a_sup_set_class a_wral i1_frss i0_frss a_sup_set_class a_wrex a_wi i0_frss a_wal i0_frss a_sup_set_class f0_frss a_wss i0_frss a_sup_set_class a_c0 a_wne a_wa i2_frss a_sup_set_class i1_frss a_sup_set_class f2_frss a_wbr a_wn i2_frss i0_frss a_sup_set_class a_wral i1_frss i0_frss a_sup_set_class a_wrex a_wi i0_frss a_wal f1_frss f2_frss a_wfr f0_frss f2_frss a_wfr p_3imtr4g $.
$}

$(Subset theorem for the set-like predicate.  (Contributed by Mario
       Carneiro, 24-Jun-2015.) $)

${
	$v A R S  $.
	$d x y A  $.
	$d x y  $.
	$d x y R  $.
	$d x y S  $.
	f0_sess1 $f class A $.
	f1_sess1 $f class R $.
	f2_sess1 $f class S $.
	i0_sess1 $f set x $.
	i1_sess1 $f set y $.
	p_sess1 $p |- ( R C_ S -> ( S Se A -> R Se A ) ) $= f1_sess1 f2_sess1 a_wss i1_sess1 a_sup_set_class f0_sess1 a_wcel p_simpl f1_sess1 f2_sess1 a_wss i1_sess1 a_sup_set_class f0_sess1 a_wcel a_wa f1_sess1 f2_sess1 i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class p_ssbrd f1_sess1 f2_sess1 a_wss i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 p_ss2rabdv i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv p_ssexg i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_wss i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel p_ex f1_sess1 f2_sess1 a_wss i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_wss i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel a_wi p_syl f1_sess1 f2_sess1 a_wss i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel i0_sess1 f0_sess1 p_ralimdv i0_sess1 i1_sess1 f0_sess1 f2_sess1 a_df-se i0_sess1 i1_sess1 f0_sess1 f1_sess1 a_df-se f1_sess1 f2_sess1 a_wss i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f2_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel i0_sess1 f0_sess1 a_wral i1_sess1 a_sup_set_class i0_sess1 a_sup_set_class f1_sess1 a_wbr i1_sess1 f0_sess1 a_crab a_cvv a_wcel i0_sess1 f0_sess1 a_wral f0_sess1 f2_sess1 a_wse f0_sess1 f1_sess1 a_wse p_3imtr4g $.
$}

$(Subset theorem for the set-like predicate.  (Contributed by Mario
       Carneiro, 24-Jun-2015.) $)

${
	$v A B R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y R  $.
	$d x y  $.
	f0_sess2 $f class A $.
	f1_sess2 $f class B $.
	f2_sess2 $f class R $.
	i0_sess2 $f set x $.
	i1_sess2 $f set y $.
	p_sess2 $p |- ( A C_ B -> ( R Se B -> R Se A ) ) $= i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i0_sess2 f0_sess2 f1_sess2 p_ssralv i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 f1_sess2 p_rabss2 i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv p_ssexg i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_wss i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab a_cvv a_wcel p_ex f0_sess2 f1_sess2 a_wss i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_wss i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab a_cvv a_wcel a_wi p_syl f0_sess2 f1_sess2 a_wss i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab a_cvv a_wcel i0_sess2 f0_sess2 p_ralimdv f0_sess2 f1_sess2 a_wss i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i0_sess2 f1_sess2 a_wral i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i0_sess2 f0_sess2 a_wral i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab a_cvv a_wcel i0_sess2 f0_sess2 a_wral p_syld i0_sess2 i1_sess2 f1_sess2 f2_sess2 a_df-se i0_sess2 i1_sess2 f0_sess2 f2_sess2 a_df-se f0_sess2 f1_sess2 a_wss i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f1_sess2 a_crab a_cvv a_wcel i0_sess2 f1_sess2 a_wral i1_sess2 a_sup_set_class i0_sess2 a_sup_set_class f2_sess2 a_wbr i1_sess2 f0_sess2 a_crab a_cvv a_wcel i0_sess2 f0_sess2 a_wral f1_sess2 f2_sess2 a_wse f0_sess2 f2_sess2 a_wse p_3imtr4g $.
$}

$(Equality theorem for the well-founded predicate.  (Contributed by NM,
       9-Mar-1997.) $)

${
	$v A R S  $.
	$d x y z R  $.
	$d x y z S  $.
	$d x y z A  $.
	f0_freq1 $f class A $.
	f1_freq1 $f class R $.
	f2_freq1 $f class S $.
	i0_freq1 $f set x $.
	i1_freq1 $f set y $.
	i2_freq1 $f set z $.
	p_freq1 $p |- ( R = S -> ( R Fr A <-> S Fr A ) ) $= i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f1_freq1 f2_freq1 p_breq f1_freq1 f2_freq1 a_wceq i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f1_freq1 a_wbr i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f2_freq1 a_wbr p_notbid f1_freq1 f2_freq1 a_wceq i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f1_freq1 a_wbr a_wn i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f2_freq1 a_wbr a_wn i1_freq1 i2_freq1 i0_freq1 a_sup_set_class i0_freq1 a_sup_set_class p_rexralbidv f1_freq1 f2_freq1 a_wceq i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f1_freq1 a_wbr a_wn i2_freq1 i0_freq1 a_sup_set_class a_wral i1_freq1 i0_freq1 a_sup_set_class a_wrex i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f2_freq1 a_wbr a_wn i2_freq1 i0_freq1 a_sup_set_class a_wral i1_freq1 i0_freq1 a_sup_set_class a_wrex i0_freq1 a_sup_set_class f0_freq1 a_wss i0_freq1 a_sup_set_class a_c0 a_wne a_wa p_imbi2d f1_freq1 f2_freq1 a_wceq i0_freq1 a_sup_set_class f0_freq1 a_wss i0_freq1 a_sup_set_class a_c0 a_wne a_wa i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f1_freq1 a_wbr a_wn i2_freq1 i0_freq1 a_sup_set_class a_wral i1_freq1 i0_freq1 a_sup_set_class a_wrex a_wi i0_freq1 a_sup_set_class f0_freq1 a_wss i0_freq1 a_sup_set_class a_c0 a_wne a_wa i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f2_freq1 a_wbr a_wn i2_freq1 i0_freq1 a_sup_set_class a_wral i1_freq1 i0_freq1 a_sup_set_class a_wrex a_wi i0_freq1 p_albidv i0_freq1 i1_freq1 i2_freq1 f0_freq1 f1_freq1 a_df-fr i0_freq1 i1_freq1 i2_freq1 f0_freq1 f2_freq1 a_df-fr f1_freq1 f2_freq1 a_wceq i0_freq1 a_sup_set_class f0_freq1 a_wss i0_freq1 a_sup_set_class a_c0 a_wne a_wa i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f1_freq1 a_wbr a_wn i2_freq1 i0_freq1 a_sup_set_class a_wral i1_freq1 i0_freq1 a_sup_set_class a_wrex a_wi i0_freq1 a_wal i0_freq1 a_sup_set_class f0_freq1 a_wss i0_freq1 a_sup_set_class a_c0 a_wne a_wa i2_freq1 a_sup_set_class i1_freq1 a_sup_set_class f2_freq1 a_wbr a_wn i2_freq1 i0_freq1 a_sup_set_class a_wral i1_freq1 i0_freq1 a_sup_set_class a_wrex a_wi i0_freq1 a_wal f0_freq1 f1_freq1 a_wfr f0_freq1 f2_freq1 a_wfr p_3bitr4g $.
$}

$(Equality theorem for the well-founded predicate.  (Contributed by NM,
     3-Apr-1994.) $)

${
	$v A B R  $.
	f0_freq2 $f class A $.
	f1_freq2 $f class B $.
	f2_freq2 $f class R $.
	p_freq2 $p |- ( A = B -> ( R Fr A <-> R Fr B ) ) $= f1_freq2 f0_freq2 p_eqimss2 f1_freq2 f0_freq2 f2_freq2 p_frss f0_freq2 f1_freq2 a_wceq f1_freq2 f0_freq2 a_wss f0_freq2 f2_freq2 a_wfr f1_freq2 f2_freq2 a_wfr a_wi p_syl f0_freq2 f1_freq2 p_eqimss f0_freq2 f1_freq2 f2_freq2 p_frss f0_freq2 f1_freq2 a_wceq f0_freq2 f1_freq2 a_wss f1_freq2 f2_freq2 a_wfr f0_freq2 f2_freq2 a_wfr a_wi p_syl f0_freq2 f1_freq2 a_wceq f0_freq2 f2_freq2 a_wfr f1_freq2 f2_freq2 a_wfr p_impbid $.
$}

$(Equality theorem for the set-like predicate.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)

${
	$v A R S  $.
	f0_seeq1 $f class A $.
	f1_seeq1 $f class R $.
	f2_seeq1 $f class S $.
	p_seeq1 $p |- ( R = S -> ( R Se A <-> S Se A ) ) $= f2_seeq1 f1_seeq1 p_eqimss2 f0_seeq1 f2_seeq1 f1_seeq1 p_sess1 f1_seeq1 f2_seeq1 a_wceq f2_seeq1 f1_seeq1 a_wss f0_seeq1 f1_seeq1 a_wse f0_seeq1 f2_seeq1 a_wse a_wi p_syl f1_seeq1 f2_seeq1 p_eqimss f0_seeq1 f1_seeq1 f2_seeq1 p_sess1 f1_seeq1 f2_seeq1 a_wceq f1_seeq1 f2_seeq1 a_wss f0_seeq1 f2_seeq1 a_wse f0_seeq1 f1_seeq1 a_wse a_wi p_syl f1_seeq1 f2_seeq1 a_wceq f0_seeq1 f1_seeq1 a_wse f0_seeq1 f2_seeq1 a_wse p_impbid $.
$}

$(Equality theorem for the set-like predicate.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)

${
	$v A B R  $.
	f0_seeq2 $f class A $.
	f1_seeq2 $f class B $.
	f2_seeq2 $f class R $.
	p_seeq2 $p |- ( A = B -> ( R Se A <-> R Se B ) ) $= f1_seeq2 f0_seeq2 p_eqimss2 f1_seeq2 f0_seeq2 f2_seeq2 p_sess2 f0_seeq2 f1_seeq2 a_wceq f1_seeq2 f0_seeq2 a_wss f0_seeq2 f2_seeq2 a_wse f1_seeq2 f2_seeq2 a_wse a_wi p_syl f0_seeq2 f1_seeq2 p_eqimss f0_seeq2 f1_seeq2 f2_seeq2 p_sess2 f0_seeq2 f1_seeq2 a_wceq f0_seeq2 f1_seeq2 a_wss f1_seeq2 f2_seeq2 a_wse f0_seeq2 f2_seeq2 a_wse a_wi p_syl f0_seeq2 f1_seeq2 a_wceq f0_seeq2 f2_seeq2 a_wse f1_seeq2 f2_seeq2 a_wse p_impbid $.
$}

$(Bound-variable hypothesis builder for well-founded relations.
       (Contributed by Stefan O'Rear, 20-Jan-2015.)  (Revised by Mario
       Carneiro, 14-Oct-2016.) $)

${
	$v x A R  $.
	$d R a b c  $.
	$d A a b c  $.
	$d x a b c  $.
	f0_nffr $f set x $.
	f1_nffr $f class A $.
	f2_nffr $f class R $.
	i0_nffr $f set a $.
	i1_nffr $f set b $.
	i2_nffr $f set c $.
	e0_nffr $e |- F/_ x R $.
	e1_nffr $e |- F/_ x A $.
	p_nffr $p |- F/ x R Fr A $= i0_nffr i1_nffr i2_nffr f1_nffr f2_nffr a_df-fr f0_nffr i0_nffr a_sup_set_class p_nfcv e1_nffr f0_nffr i0_nffr a_sup_set_class f1_nffr p_nfss i0_nffr a_sup_set_class a_c0 a_wne f0_nffr p_nfv i0_nffr a_sup_set_class f1_nffr a_wss i0_nffr a_sup_set_class a_c0 a_wne f0_nffr p_nfan f0_nffr i0_nffr a_sup_set_class p_nfcv f0_nffr i0_nffr a_sup_set_class p_nfcv f0_nffr i2_nffr a_sup_set_class p_nfcv e0_nffr f0_nffr i1_nffr a_sup_set_class p_nfcv f0_nffr i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr p_nfbr i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr a_wbr f0_nffr p_nfn i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr a_wbr a_wn f0_nffr i2_nffr i0_nffr a_sup_set_class p_nfral i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr a_wbr a_wn i2_nffr i0_nffr a_sup_set_class a_wral f0_nffr i1_nffr i0_nffr a_sup_set_class p_nfrex i0_nffr a_sup_set_class f1_nffr a_wss i0_nffr a_sup_set_class a_c0 a_wne a_wa i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr a_wbr a_wn i2_nffr i0_nffr a_sup_set_class a_wral i1_nffr i0_nffr a_sup_set_class a_wrex f0_nffr p_nfim i0_nffr a_sup_set_class f1_nffr a_wss i0_nffr a_sup_set_class a_c0 a_wne a_wa i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr a_wbr a_wn i2_nffr i0_nffr a_sup_set_class a_wral i1_nffr i0_nffr a_sup_set_class a_wrex a_wi f0_nffr i0_nffr p_nfal f1_nffr f2_nffr a_wfr i0_nffr a_sup_set_class f1_nffr a_wss i0_nffr a_sup_set_class a_c0 a_wne a_wa i2_nffr a_sup_set_class i1_nffr a_sup_set_class f2_nffr a_wbr a_wn i2_nffr i0_nffr a_sup_set_class a_wral i1_nffr i0_nffr a_sup_set_class a_wrex a_wi i0_nffr a_wal f0_nffr p_nfxfr $.
$}

$(Bound-variable hypothesis builder for set-like relations.  (Contributed
       by Mario Carneiro, 24-Jun-2015.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v x A R  $.
	$d R a b  $.
	$d A a b  $.
	$d x a b  $.
	f0_nfse $f set x $.
	f1_nfse $f class A $.
	f2_nfse $f class R $.
	i0_nfse $f set a $.
	i1_nfse $f set b $.
	e0_nfse $e |- F/_ x R $.
	e1_nfse $e |- F/_ x A $.
	p_nfse $p |- F/ x R Se A $= i1_nfse i0_nfse f1_nfse f2_nfse a_df-se e1_nfse f0_nfse i0_nfse a_sup_set_class p_nfcv e0_nfse f0_nfse i1_nfse a_sup_set_class p_nfcv f0_nfse i0_nfse a_sup_set_class i1_nfse a_sup_set_class f2_nfse p_nfbr e1_nfse i0_nfse a_sup_set_class i1_nfse a_sup_set_class f2_nfse a_wbr f0_nfse i0_nfse f1_nfse p_nfrab f0_nfse i0_nfse a_sup_set_class i1_nfse a_sup_set_class f2_nfse a_wbr i0_nfse f1_nfse a_crab a_cvv p_nfel1 i0_nfse a_sup_set_class i1_nfse a_sup_set_class f2_nfse a_wbr i0_nfse f1_nfse a_crab a_cvv a_wcel f0_nfse i1_nfse f1_nfse p_nfral f1_nfse f2_nfse a_wse i0_nfse a_sup_set_class i1_nfse a_sup_set_class f2_nfse a_wbr i0_nfse f1_nfse a_crab a_cvv a_wcel i1_nfse f1_nfse a_wral f0_nfse p_nfxfr $.
$}

$(Bound-variable hypothesis builder for well-orderings.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v x A R  $.
	$d R  $.
	$d A  $.
	$d x  $.
	f0_nfwe $f set x $.
	f1_nfwe $f class A $.
	f2_nfwe $f class R $.
	e0_nfwe $e |- F/_ x R $.
	e1_nfwe $e |- F/_ x A $.
	p_nfwe $p |- F/ x R We A $= f1_nfwe f2_nfwe a_df-we e0_nfwe e1_nfwe f0_nfwe f1_nfwe f2_nfwe p_nffr e0_nfwe e1_nfwe f0_nfwe f1_nfwe f2_nfwe p_nfso f1_nfwe f2_nfwe a_wfr f1_nfwe f2_nfwe a_wor f0_nfwe p_nfan f1_nfwe f2_nfwe a_wwe f1_nfwe f2_nfwe a_wfr f1_nfwe f2_nfwe a_wor a_wa f0_nfwe p_nfxfr $.
$}

$(A well-founded relation is irreflexive.  Special case of Proposition
       6.23 of [TakeutiZaring] p. 30.  (Contributed by NM, 2-Jan-1994.)
       (Revised by Mario Carneiro, 22-Jun-2015.) $)

${
	$v A B R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y R  $.
	f0_frirr $f class A $.
	f1_frirr $f class B $.
	f2_frirr $f class R $.
	i0_frirr $f set x $.
	i1_frirr $f set y $.
	p_frirr $p |- ( ( R Fr A /\ B e. A ) -> -. B R B ) $= f0_frirr f2_frirr a_wfr f1_frirr f0_frirr a_wcel p_simpl f0_frirr f2_frirr a_wfr f1_frirr f0_frirr a_wcel p_simpr f0_frirr f2_frirr a_wfr f1_frirr f0_frirr a_wcel a_wa f1_frirr f0_frirr p_snssd f1_frirr f0_frirr p_snnzg f1_frirr f0_frirr a_wcel f1_frirr a_csn a_c0 a_wne f0_frirr f2_frirr a_wfr p_adantl f1_frirr p_snex i1_frirr i0_frirr f0_frirr f1_frirr a_csn f2_frirr p_frc f0_frirr f2_frirr a_wfr f1_frirr f0_frirr a_wcel a_wa f0_frirr f2_frirr a_wfr f1_frirr a_csn f0_frirr a_wss f1_frirr a_csn a_c0 a_wne i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn a_crab a_c0 a_wceq i1_frirr f1_frirr a_csn a_wrex p_syl3anc i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn p_rabeq0 i1_frirr a_sup_set_class f1_frirr i0_frirr a_sup_set_class f2_frirr p_breq2 i1_frirr a_sup_set_class f1_frirr a_wceq i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr p_notbid i1_frirr a_sup_set_class f1_frirr a_wceq i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr a_wn i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr a_wn i0_frirr f1_frirr a_csn p_ralbidv i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn a_crab a_c0 a_wceq i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr a_wn i0_frirr f1_frirr a_csn a_wral i1_frirr a_sup_set_class f1_frirr a_wceq i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr a_wn i0_frirr f1_frirr a_csn a_wral p_syl5bb i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn a_crab a_c0 a_wceq i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr a_wn i0_frirr f1_frirr a_csn a_wral i1_frirr f1_frirr f0_frirr p_rexsng i0_frirr a_sup_set_class f1_frirr f1_frirr f2_frirr p_breq1 i0_frirr a_sup_set_class f1_frirr a_wceq i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr f1_frirr f1_frirr f2_frirr a_wbr p_notbid i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr a_wn f1_frirr f1_frirr f2_frirr a_wbr a_wn i0_frirr f1_frirr f0_frirr p_ralsng f1_frirr f0_frirr a_wcel i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn a_crab a_c0 a_wceq i1_frirr f1_frirr a_csn a_wrex i0_frirr a_sup_set_class f1_frirr f2_frirr a_wbr a_wn i0_frirr f1_frirr a_csn a_wral f1_frirr f1_frirr f2_frirr a_wbr a_wn p_bitrd f1_frirr f0_frirr a_wcel i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn a_crab a_c0 a_wceq i1_frirr f1_frirr a_csn a_wrex f1_frirr f1_frirr f2_frirr a_wbr a_wn a_wb f0_frirr f2_frirr a_wfr p_adantl f0_frirr f2_frirr a_wfr f1_frirr f0_frirr a_wcel a_wa i0_frirr a_sup_set_class i1_frirr a_sup_set_class f2_frirr a_wbr i0_frirr f1_frirr a_csn a_crab a_c0 a_wceq i1_frirr f1_frirr a_csn a_wrex f1_frirr f1_frirr f2_frirr a_wbr a_wn p_mpbid $.
$}

$(A well-founded relation has no 2-cycle loops.  Special case of
       Proposition 6.23 of [TakeutiZaring] p. 30.  (Contributed by NM,
       30-May-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)

${
	$v A B C R  $.
	$d x y A  $.
	$d x y B  $.
	$d x y C  $.
	$d x y R  $.
	f0_fr2nr $f class A $.
	f1_fr2nr $f class B $.
	f2_fr2nr $f class C $.
	f3_fr2nr $f class R $.
	i0_fr2nr $f set x $.
	i1_fr2nr $f set y $.
	p_fr2nr $p |- ( ( R Fr A /\ ( B e. A /\ C e. A ) ) -> -. ( B R C /\ C R B ) ) $= f1_fr2nr f2_fr2nr p_prex f1_fr2nr f2_fr2nr a_cpr a_cvv a_wcel f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa p_a1i f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa p_simpl f1_fr2nr f2_fr2nr f0_fr2nr p_prssi f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa f1_fr2nr f2_fr2nr a_cpr f0_fr2nr a_wss f0_fr2nr f3_fr2nr a_wfr p_adantl f1_fr2nr f2_fr2nr f0_fr2nr p_prnzg f1_fr2nr f0_fr2nr a_wcel f1_fr2nr f2_fr2nr a_cpr a_c0 a_wne f0_fr2nr f3_fr2nr a_wfr f2_fr2nr f0_fr2nr a_wcel p_ad2antrl i1_fr2nr i0_fr2nr f0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_cvv f3_fr2nr p_fri f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa f1_fr2nr f2_fr2nr a_cpr a_cvv a_wcel f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f2_fr2nr a_cpr f0_fr2nr a_wss f1_fr2nr f2_fr2nr a_cpr a_c0 a_wne i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i1_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wrex p_syl22anc i1_fr2nr a_sup_set_class f1_fr2nr i0_fr2nr a_sup_set_class f3_fr2nr p_breq2 i1_fr2nr a_sup_set_class f1_fr2nr a_wceq i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr p_notbid i1_fr2nr a_sup_set_class f1_fr2nr a_wceq i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr a_wn i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr p_ralbidv i1_fr2nr a_sup_set_class f2_fr2nr i0_fr2nr a_sup_set_class f3_fr2nr p_breq2 i1_fr2nr a_sup_set_class f2_fr2nr a_wceq i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr p_notbid i1_fr2nr a_sup_set_class f2_fr2nr a_wceq i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr a_wn i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr p_ralbidv i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i1_fr2nr f1_fr2nr f2_fr2nr f0_fr2nr f0_fr2nr p_rexprg f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i1_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wrex i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral a_wo a_wb f0_fr2nr f3_fr2nr a_wfr p_adantl f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa i0_fr2nr a_sup_set_class i1_fr2nr a_sup_set_class f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i1_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wrex i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral a_wo p_mpbid f1_fr2nr f2_fr2nr f0_fr2nr p_prid2g f2_fr2nr f0_fr2nr a_wcel f2_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wcel f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel p_ad2antll i0_fr2nr a_sup_set_class f2_fr2nr f1_fr2nr f3_fr2nr p_breq1 i0_fr2nr a_sup_set_class f2_fr2nr a_wceq i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr f2_fr2nr f1_fr2nr f3_fr2nr a_wbr p_notbid i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f2_fr2nr f1_fr2nr f2_fr2nr a_cpr p_rspcv f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa f2_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wcel i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wn a_wi p_syl f1_fr2nr f2_fr2nr f0_fr2nr p_prid1g f1_fr2nr f0_fr2nr a_wcel f1_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wcel f0_fr2nr f3_fr2nr a_wfr f2_fr2nr f0_fr2nr a_wcel p_ad2antrl i0_fr2nr a_sup_set_class f1_fr2nr f2_fr2nr f3_fr2nr p_breq1 i0_fr2nr a_sup_set_class f1_fr2nr a_wceq i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr f1_fr2nr f2_fr2nr f3_fr2nr a_wbr p_notbid i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn f1_fr2nr f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f1_fr2nr f2_fr2nr a_cpr p_rspcv f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa f1_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wcel i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral f1_fr2nr f2_fr2nr f3_fr2nr a_wbr a_wn a_wi p_syl f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral f1_fr2nr f2_fr2nr f3_fr2nr a_wbr a_wn p_orim12d f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa i0_fr2nr a_sup_set_class f1_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral i0_fr2nr a_sup_set_class f2_fr2nr f3_fr2nr a_wbr a_wn i0_fr2nr f1_fr2nr f2_fr2nr a_cpr a_wral a_wo f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wn f1_fr2nr f2_fr2nr f3_fr2nr a_wbr a_wn a_wo p_mpd f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wn f1_fr2nr f2_fr2nr f3_fr2nr a_wbr a_wn p_orcomd f1_fr2nr f2_fr2nr f3_fr2nr a_wbr f2_fr2nr f1_fr2nr f3_fr2nr a_wbr p_ianor f0_fr2nr f3_fr2nr a_wfr f1_fr2nr f0_fr2nr a_wcel f2_fr2nr f0_fr2nr a_wcel a_wa a_wa f1_fr2nr f2_fr2nr f3_fr2nr a_wbr a_wn f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wn a_wo f1_fr2nr f2_fr2nr f3_fr2nr a_wbr f2_fr2nr f1_fr2nr f3_fr2nr a_wbr a_wa a_wn p_sylibr $.
$}

$(Any relation is well-founded on the empty set.  (Contributed by NM,
       17-Sep-1993.) $)

${
	$v R  $.
	$d x y z R  $.
	f0_fr0 $f class R $.
	i0_fr0 $f set x $.
	i1_fr0 $f set y $.
	i2_fr0 $f set z $.
	p_fr0 $p |- R Fr (/) $= i0_fr0 i1_fr0 i2_fr0 a_c0 f0_fr0 p_dffr2 i0_fr0 a_sup_set_class p_ss0 i0_fr0 a_sup_set_class a_c0 a_wss i0_fr0 a_sup_set_class a_c0 a_wceq i2_fr0 a_sup_set_class i1_fr0 a_sup_set_class f0_fr0 a_wbr i2_fr0 i0_fr0 a_sup_set_class a_crab a_c0 a_wceq i1_fr0 i0_fr0 a_sup_set_class a_wrex a_wn p_a1d i0_fr0 a_sup_set_class a_c0 a_wss i2_fr0 a_sup_set_class i1_fr0 a_sup_set_class f0_fr0 a_wbr i2_fr0 i0_fr0 a_sup_set_class a_crab a_c0 a_wceq i1_fr0 i0_fr0 a_sup_set_class a_wrex i0_fr0 a_sup_set_class a_c0 p_necon1ad i0_fr0 a_sup_set_class a_c0 a_wss i0_fr0 a_sup_set_class a_c0 a_wne i2_fr0 a_sup_set_class i1_fr0 a_sup_set_class f0_fr0 a_wbr i2_fr0 i0_fr0 a_sup_set_class a_crab a_c0 a_wceq i1_fr0 i0_fr0 a_sup_set_class a_wrex p_imp a_c0 f0_fr0 a_wfr i0_fr0 a_sup_set_class a_c0 a_wss i0_fr0 a_sup_set_class a_c0 a_wne a_wa i2_fr0 a_sup_set_class i1_fr0 a_sup_set_class f0_fr0 a_wbr i2_fr0 i0_fr0 a_sup_set_class a_crab a_c0 a_wceq i1_fr0 i0_fr0 a_sup_set_class a_wrex a_wi i0_fr0 p_mpgbir $.
$}

$(If an element of a well-founded set satisfies a property ` ph ` , then
       there is a minimal element that satisfies ` ph ` .  (Contributed by Jeff
       Madsen, 18-Jun-2010.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)

${
	$v ph ps x y A R  $.
	$d A x y z  $.
	$d R x y z  $.
	$d ph y z  $.
	$d ps x z  $.
	f0_frminex $f wff ph $.
	f1_frminex $f wff ps $.
	f2_frminex $f set x $.
	f3_frminex $f set y $.
	f4_frminex $f class A $.
	f5_frminex $f class R $.
	i0_frminex $f set z $.
	e0_frminex $e |- A e. _V $.
	e1_frminex $e |- ( x = y -> ( ph <-> ps ) ) $.
	p_frminex $p |- ( R Fr A -> ( E. x e. A ph -> E. x e. A ( ph /\ A. y e. A ( ps -> -. y R x ) ) ) ) $= f0_frminex f2_frminex f4_frminex p_rabn0 e0_frminex f0_frminex f2_frminex f4_frminex p_rabex f0_frminex f2_frminex f4_frminex p_ssrab2 i0_frminex f3_frminex f4_frminex f0_frminex f2_frminex f4_frminex a_crab a_cvv f5_frminex p_fri e1_frminex f0_frminex f1_frminex f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn f3_frminex f2_frminex f4_frminex p_ralrab f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn f3_frminex f0_frminex f2_frminex f4_frminex a_crab a_wral f1_frminex f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral i0_frminex f0_frminex f2_frminex f4_frminex a_crab p_rexbii i0_frminex a_sup_set_class f2_frminex a_sup_set_class f3_frminex a_sup_set_class f5_frminex p_breq2 i0_frminex a_sup_set_class f2_frminex a_sup_set_class a_wceq f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr p_notbid i0_frminex a_sup_set_class f2_frminex a_sup_set_class a_wceq f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn f1_frminex p_imbi2d i0_frminex a_sup_set_class f2_frminex a_sup_set_class a_wceq f1_frminex f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex p_ralbidv f0_frminex f1_frminex f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral i0_frminex f2_frminex f4_frminex p_rexrab2 f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn f3_frminex f0_frminex f2_frminex f4_frminex a_crab a_wral i0_frminex f0_frminex f2_frminex f4_frminex a_crab a_wrex f1_frminex f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral i0_frminex f0_frminex f2_frminex f4_frminex a_crab a_wrex f0_frminex f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral a_wa f2_frminex f4_frminex a_wrex p_bitri f0_frminex f2_frminex f4_frminex a_crab a_cvv a_wcel f4_frminex f5_frminex a_wfr a_wa f0_frminex f2_frminex f4_frminex a_crab f4_frminex a_wss f0_frminex f2_frminex f4_frminex a_crab a_c0 a_wne a_wa a_wa f3_frminex a_sup_set_class i0_frminex a_sup_set_class f5_frminex a_wbr a_wn f3_frminex f0_frminex f2_frminex f4_frminex a_crab a_wral i0_frminex f0_frminex f2_frminex f4_frminex a_crab a_wrex f0_frminex f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral a_wa f2_frminex f4_frminex a_wrex p_sylib f0_frminex f2_frminex f4_frminex a_crab a_cvv a_wcel f4_frminex f5_frminex a_wfr f0_frminex f2_frminex f4_frminex a_crab f4_frminex a_wss f0_frminex f2_frminex f4_frminex a_crab a_c0 a_wne f0_frminex f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral a_wa f2_frminex f4_frminex a_wrex p_an4s f0_frminex f2_frminex f4_frminex a_crab a_cvv a_wcel f0_frminex f2_frminex f4_frminex a_crab f4_frminex a_wss f4_frminex f5_frminex a_wfr f0_frminex f2_frminex f4_frminex a_crab a_c0 a_wne a_wa f0_frminex f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral a_wa f2_frminex f4_frminex a_wrex p_mpanl12 f4_frminex f5_frminex a_wfr f0_frminex f2_frminex f4_frminex a_crab a_c0 a_wne f0_frminex f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral a_wa f2_frminex f4_frminex a_wrex p_ex f0_frminex f2_frminex f4_frminex a_wrex f0_frminex f2_frminex f4_frminex a_crab a_c0 a_wne f4_frminex f5_frminex a_wfr f0_frminex f1_frminex f3_frminex a_sup_set_class f2_frminex a_sup_set_class f5_frminex a_wbr a_wn a_wi f3_frminex f4_frminex a_wral a_wa f2_frminex f4_frminex a_wrex p_syl5bir $.
$}

$(Irreflexivity of the epsilon relation: a class founded by epsilon is not
       a member of itself.  (Contributed by NM, 18-Apr-1994.)  (Revised by
       Mario Carneiro, 22-Jun-2015.) $)

${
	$v A  $.
	$d A  $.
	f0_efrirr $f class A $.
	p_efrirr $p |- ( _E Fr A -> -. A e. A ) $= f0_efrirr f0_efrirr a_cep p_frirr f0_efrirr f0_efrirr f0_efrirr p_epelg f0_efrirr f0_efrirr a_wcel f0_efrirr f0_efrirr a_cep a_wbr f0_efrirr f0_efrirr a_wcel a_wb f0_efrirr a_cep a_wfr p_adantl f0_efrirr a_cep a_wfr f0_efrirr f0_efrirr a_wcel a_wa f0_efrirr f0_efrirr a_cep a_wbr f0_efrirr f0_efrirr a_wcel p_mtbid f0_efrirr a_cep a_wfr f0_efrirr f0_efrirr a_wcel f0_efrirr f0_efrirr a_wcel a_wn p_ex f0_efrirr a_cep a_wfr f0_efrirr f0_efrirr a_wcel p_pm2.01d $.
$}

$(A set founded by epsilon contains no 2-cycle loops.  (Contributed by NM,
     19-Apr-1994.) $)

${
	$v A B C  $.
	f0_efrn2lp $f class A $.
	f1_efrn2lp $f class B $.
	f2_efrn2lp $f class C $.
	p_efrn2lp $p |- ( ( _E Fr A /\ ( B e. A /\ C e. A ) ) -> -. ( B e. C /\ C e. B ) ) $= f0_efrn2lp f1_efrn2lp f2_efrn2lp a_cep p_fr2nr f1_efrn2lp f2_efrn2lp f0_efrn2lp p_epelg f2_efrn2lp f1_efrn2lp f0_efrn2lp p_epelg f2_efrn2lp f0_efrn2lp a_wcel f1_efrn2lp f2_efrn2lp a_cep a_wbr f1_efrn2lp f2_efrn2lp a_wcel f1_efrn2lp f0_efrn2lp a_wcel f2_efrn2lp f1_efrn2lp a_cep a_wbr f2_efrn2lp f1_efrn2lp a_wcel p_bi2anan9r f1_efrn2lp f0_efrn2lp a_wcel f2_efrn2lp f0_efrn2lp a_wcel a_wa f1_efrn2lp f2_efrn2lp a_cep a_wbr f2_efrn2lp f1_efrn2lp a_cep a_wbr a_wa f1_efrn2lp f2_efrn2lp a_wcel f2_efrn2lp f1_efrn2lp a_wcel a_wa a_wb f0_efrn2lp a_cep a_wfr p_adantl f0_efrn2lp a_cep a_wfr f1_efrn2lp f0_efrn2lp a_wcel f2_efrn2lp f0_efrn2lp a_wcel a_wa a_wa f1_efrn2lp f2_efrn2lp a_cep a_wbr f2_efrn2lp f1_efrn2lp a_cep a_wbr a_wa f1_efrn2lp f2_efrn2lp a_wcel f2_efrn2lp f1_efrn2lp a_wcel a_wa p_mtbid $.
$}

$(The epsilon relation is set-like on any class.  (This is the origin of
       the term "set-like": a set-like relation "acts like" the epsilon
       relation of sets and their elements.)  (Contributed by Mario Carneiro,
       22-Jun-2015.) $)

${
	$v A  $.
	$d x y A  $.
	f0_epse $f class A $.
	i0_epse $f set x $.
	i1_epse $f set y $.
	p_epse $p |- _E Se A $= i1_epse i0_epse p_epel i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse a_sup_set_class i0_epse a_sup_set_class a_wcel p_bicomi i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse i0_epse a_sup_set_class p_abbi2i i0_epse p_vex i0_epse a_sup_set_class i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse a_cab a_cvv p_eqeltrri i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse f0_epse p_dfrab2 i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse a_cab f0_epse p_inss1 i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse f0_epse a_crab i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse a_cab f0_epse a_cin i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse a_cab p_eqsstri i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse f0_epse a_crab i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse a_cab p_ssexi i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse f0_epse a_crab a_cvv a_wcel i0_epse f0_epse p_rgenw i0_epse i1_epse f0_epse a_cep a_df-se f0_epse a_cep a_wse i1_epse a_sup_set_class i0_epse a_sup_set_class a_cep a_wbr i1_epse f0_epse a_crab a_cvv a_wcel i0_epse f0_epse a_wral p_mpbir $.
$}

$(Similar to Theorem 7.2 of [TakeutiZaring] p. 35, of except that the Axiom
     of Regularity is not required due to antecedent ` _E Fr A ` .
     (Contributed by NM, 4-May-1994.) $)

${
	$v A B  $.
	f0_tz7.2 $f class A $.
	f1_tz7.2 $f class B $.
	p_tz7.2 $p |- ( ( Tr A /\ _E Fr A /\ B e. A ) -> ( B C_ A /\ B =/= A ) ) $= f0_tz7.2 f1_tz7.2 p_trss f0_tz7.2 p_efrirr f1_tz7.2 f0_tz7.2 f0_tz7.2 p_eleq1 f1_tz7.2 f0_tz7.2 a_wceq f1_tz7.2 f0_tz7.2 a_wcel f0_tz7.2 f0_tz7.2 a_wcel p_notbid f0_tz7.2 a_cep a_wfr f1_tz7.2 f0_tz7.2 a_wcel a_wn f1_tz7.2 f0_tz7.2 a_wceq f0_tz7.2 f0_tz7.2 a_wcel a_wn p_syl5ibrcom f0_tz7.2 a_cep a_wfr f1_tz7.2 f0_tz7.2 a_wcel f1_tz7.2 f0_tz7.2 p_necon2ad f0_tz7.2 a_wtr f1_tz7.2 f0_tz7.2 a_wcel f1_tz7.2 f0_tz7.2 a_wss f0_tz7.2 a_cep a_wfr f1_tz7.2 f0_tz7.2 a_wne p_anim12ii f0_tz7.2 a_wtr f0_tz7.2 a_cep a_wfr f1_tz7.2 f0_tz7.2 a_wcel f1_tz7.2 f0_tz7.2 a_wss f1_tz7.2 f0_tz7.2 a_wne a_wa p_3impia $.
$}

$(An alternate way of saying that the epsilon relation is well-founded.
       (Contributed by NM, 17-Feb-2004.)  (Revised by Mario Carneiro,
       23-Jun-2015.) $)

${
	$v x y A  $.
	$d x y z A  $.
	f0_dfepfr $f set x $.
	f1_dfepfr $f set y $.
	f2_dfepfr $f class A $.
	i0_dfepfr $f set z $.
	p_dfepfr $p |- ( _E Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x ( x i^i y ) = (/) ) ) $= f0_dfepfr f1_dfepfr i0_dfepfr f2_dfepfr a_cep p_dffr2 i0_dfepfr f1_dfepfr p_epel i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_wcel a_wb i0_dfepfr a_sup_set_class f0_dfepfr a_sup_set_class a_wcel p_a1i i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_wcel i0_dfepfr f0_dfepfr a_sup_set_class p_rabbiia i0_dfepfr f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class p_dfin5 i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr f0_dfepfr a_sup_set_class a_crab i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_wcel i0_dfepfr f0_dfepfr a_sup_set_class a_crab f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cin p_eqtr4i i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr f0_dfepfr a_sup_set_class a_crab f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cin a_c0 p_eqeq1i i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr f0_dfepfr a_sup_set_class a_crab a_c0 a_wceq f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cin a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class p_rexbii i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr f0_dfepfr a_sup_set_class a_crab a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class a_wrex f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cin a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class a_wrex f0_dfepfr a_sup_set_class f2_dfepfr a_wss f0_dfepfr a_sup_set_class a_c0 a_wne a_wa p_imbi2i f0_dfepfr a_sup_set_class f2_dfepfr a_wss f0_dfepfr a_sup_set_class a_c0 a_wne a_wa i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr f0_dfepfr a_sup_set_class a_crab a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class a_wrex a_wi f0_dfepfr a_sup_set_class f2_dfepfr a_wss f0_dfepfr a_sup_set_class a_c0 a_wne a_wa f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cin a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class a_wrex a_wi f0_dfepfr p_albii f2_dfepfr a_cep a_wfr f0_dfepfr a_sup_set_class f2_dfepfr a_wss f0_dfepfr a_sup_set_class a_c0 a_wne a_wa i0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cep a_wbr i0_dfepfr f0_dfepfr a_sup_set_class a_crab a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class a_wrex a_wi f0_dfepfr a_wal f0_dfepfr a_sup_set_class f2_dfepfr a_wss f0_dfepfr a_sup_set_class a_c0 a_wne a_wa f0_dfepfr a_sup_set_class f1_dfepfr a_sup_set_class a_cin a_c0 a_wceq f1_dfepfr f0_dfepfr a_sup_set_class a_wrex a_wi f0_dfepfr a_wal p_bitri $.
$}

$(A subset of an epsilon-founded class has a minimal element.
       (Contributed by NM, 17-Feb-2004.)  (Revised by David Abernethy,
       22-Feb-2011.) $)

${
	$v x A B  $.
	$d x y A  $.
	$d x y B  $.
	f0_epfrc $f set x $.
	f1_epfrc $f class A $.
	f2_epfrc $f class B $.
	i0_epfrc $f set y $.
	e0_epfrc $e |- B e. _V $.
	p_epfrc $p |- ( ( _E Fr A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) ) $= e0_epfrc f0_epfrc i0_epfrc f1_epfrc f2_epfrc a_cep p_frc i0_epfrc f2_epfrc f0_epfrc a_sup_set_class p_dfin5 i0_epfrc f0_epfrc p_epel i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_cep a_wbr i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_wcel a_wb i0_epfrc a_sup_set_class f2_epfrc a_wcel p_a1i i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_cep a_wbr i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_wcel i0_epfrc f2_epfrc p_rabbiia f2_epfrc f0_epfrc a_sup_set_class a_cin i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_wcel i0_epfrc f2_epfrc a_crab i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_cep a_wbr i0_epfrc f2_epfrc a_crab p_eqtr4i f2_epfrc f0_epfrc a_sup_set_class a_cin i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_cep a_wbr i0_epfrc f2_epfrc a_crab a_c0 p_eqeq1i f2_epfrc f0_epfrc a_sup_set_class a_cin a_c0 a_wceq i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_cep a_wbr i0_epfrc f2_epfrc a_crab a_c0 a_wceq f0_epfrc f2_epfrc p_rexbii f1_epfrc a_cep a_wfr f2_epfrc f1_epfrc a_wss f2_epfrc a_c0 a_wne a_w3a i0_epfrc a_sup_set_class f0_epfrc a_sup_set_class a_cep a_wbr i0_epfrc f2_epfrc a_crab a_c0 a_wceq f0_epfrc f2_epfrc a_wrex f2_epfrc f0_epfrc a_sup_set_class a_cin a_c0 a_wceq f0_epfrc f2_epfrc a_wrex p_sylibr $.
$}

$(Subset theorem for the well-ordering predicate.  Exercise 4 of
     [TakeutiZaring] p. 31.  (Contributed by NM, 19-Apr-1994.) $)

${
	$v A B R  $.
	f0_wess $f class A $.
	f1_wess $f class B $.
	f2_wess $f class R $.
	p_wess $p |- ( A C_ B -> ( R We B -> R We A ) ) $= f0_wess f1_wess f2_wess p_frss f0_wess f1_wess f2_wess p_soss f0_wess f1_wess a_wss f1_wess f2_wess a_wfr f0_wess f2_wess a_wfr f1_wess f2_wess a_wor f0_wess f2_wess a_wor p_anim12d f1_wess f2_wess a_df-we f0_wess f2_wess a_df-we f0_wess f1_wess a_wss f1_wess f2_wess a_wfr f1_wess f2_wess a_wor a_wa f0_wess f2_wess a_wfr f0_wess f2_wess a_wor a_wa f1_wess f2_wess a_wwe f0_wess f2_wess a_wwe p_3imtr4g $.
$}

$(Equality theorem for the well-ordering predicate.  (Contributed by NM,
     9-Mar-1997.) $)

${
	$v A R S  $.
	f0_weeq1 $f class A $.
	f1_weeq1 $f class R $.
	f2_weeq1 $f class S $.
	p_weeq1 $p |- ( R = S -> ( R We A <-> S We A ) ) $= f0_weeq1 f1_weeq1 f2_weeq1 p_freq1 f0_weeq1 f1_weeq1 f2_weeq1 p_soeq1 f1_weeq1 f2_weeq1 a_wceq f0_weeq1 f1_weeq1 a_wfr f0_weeq1 f2_weeq1 a_wfr f0_weeq1 f1_weeq1 a_wor f0_weeq1 f2_weeq1 a_wor p_anbi12d f0_weeq1 f1_weeq1 a_df-we f0_weeq1 f2_weeq1 a_df-we f1_weeq1 f2_weeq1 a_wceq f0_weeq1 f1_weeq1 a_wfr f0_weeq1 f1_weeq1 a_wor a_wa f0_weeq1 f2_weeq1 a_wfr f0_weeq1 f2_weeq1 a_wor a_wa f0_weeq1 f1_weeq1 a_wwe f0_weeq1 f2_weeq1 a_wwe p_3bitr4g $.
$}

$(Equality theorem for the well-ordering predicate.  (Contributed by NM,
     3-Apr-1994.) $)

${
	$v A B R  $.
	f0_weeq2 $f class A $.
	f1_weeq2 $f class B $.
	f2_weeq2 $f class R $.
	p_weeq2 $p |- ( A = B -> ( R We A <-> R We B ) ) $= f0_weeq2 f1_weeq2 f2_weeq2 p_freq2 f0_weeq2 f1_weeq2 f2_weeq2 p_soeq2 f0_weeq2 f1_weeq2 a_wceq f0_weeq2 f2_weeq2 a_wfr f1_weeq2 f2_weeq2 a_wfr f0_weeq2 f2_weeq2 a_wor f1_weeq2 f2_weeq2 a_wor p_anbi12d f0_weeq2 f2_weeq2 a_df-we f1_weeq2 f2_weeq2 a_df-we f0_weeq2 f1_weeq2 a_wceq f0_weeq2 f2_weeq2 a_wfr f0_weeq2 f2_weeq2 a_wor a_wa f1_weeq2 f2_weeq2 a_wfr f1_weeq2 f2_weeq2 a_wor a_wa f0_weeq2 f2_weeq2 a_wwe f1_weeq2 f2_weeq2 a_wwe p_3bitr4g $.
$}

$(A well-ordering is well-founded.  (Contributed by NM, 22-Apr-1994.) $)

${
	$v A R  $.
	f0_wefr $f class A $.
	f1_wefr $f class R $.
	p_wefr $p |- ( R We A -> R Fr A ) $= f0_wefr f1_wefr a_df-we f0_wefr f1_wefr a_wwe f0_wefr f1_wefr a_wfr f0_wefr f1_wefr a_wor p_simplbi $.
$}

$(A well-ordering is a strict ordering.  (Contributed by NM,
     16-Mar-1997.) $)

${
	$v A R  $.
	f0_weso $f class A $.
	f1_weso $f class R $.
	p_weso $p |- ( R We A -> R Or A ) $= f0_weso f1_weso a_df-we f0_weso f1_weso a_wwe f0_weso f1_weso a_wfr f0_weso f1_weso a_wor p_simprbi $.
$}

$(The elements of an epsilon well-ordering are comparable.  (Contributed by
     NM, 17-May-1994.) $)

${
	$v x y A  $.
	f0_wecmpep $f set x $.
	f1_wecmpep $f set y $.
	f2_wecmpep $f class A $.
	p_wecmpep $p |- ( ( _E We A /\ ( x e. A /\ y e. A ) ) -> ( x e. y \/ x = y \/ y e. x ) ) $= f2_wecmpep a_cep p_weso f2_wecmpep f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_cep p_solin f0_wecmpep f1_wecmpep p_epel f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wceq p_biid f1_wecmpep f0_wecmpep p_epel f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_cep a_wbr f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wcel f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wceq f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wceq f1_wecmpep a_sup_set_class f0_wecmpep a_sup_set_class a_cep a_wbr f1_wecmpep a_sup_set_class f0_wecmpep a_sup_set_class a_wcel p_3orbi123i f2_wecmpep a_cep a_wor f0_wecmpep a_sup_set_class f2_wecmpep a_wcel f1_wecmpep a_sup_set_class f2_wecmpep a_wcel a_wa a_wa f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_cep a_wbr f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wceq f1_wecmpep a_sup_set_class f0_wecmpep a_sup_set_class a_cep a_wbr a_w3o f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wcel f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wceq f1_wecmpep a_sup_set_class f0_wecmpep a_sup_set_class a_wcel a_w3o p_sylib f2_wecmpep a_cep a_wwe f2_wecmpep a_cep a_wor f0_wecmpep a_sup_set_class f2_wecmpep a_wcel f1_wecmpep a_sup_set_class f2_wecmpep a_wcel a_wa f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wcel f0_wecmpep a_sup_set_class f1_wecmpep a_sup_set_class a_wceq f1_wecmpep a_sup_set_class f0_wecmpep a_sup_set_class a_wcel a_w3o p_sylan $.
$}

$(An epsilon well-ordering is a transitive relation.  (Contributed by NM,
     22-Apr-1994.) $)

${
	$v x y z A  $.
	f0_wetrep $f set x $.
	f1_wetrep $f set y $.
	f2_wetrep $f set z $.
	f3_wetrep $f class A $.
	p_wetrep $p |- ( ( _E We A /\ ( x e. A /\ y e. A /\ z e. A ) ) -> ( ( x e. y /\ y e. z ) -> x e. z ) ) $= f3_wetrep a_cep p_weso f3_wetrep f0_wetrep a_sup_set_class f1_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_cep p_sotr f3_wetrep a_cep a_wwe f3_wetrep a_cep a_wor f0_wetrep a_sup_set_class f3_wetrep a_wcel f1_wetrep a_sup_set_class f3_wetrep a_wcel f2_wetrep a_sup_set_class f3_wetrep a_wcel a_w3a f0_wetrep a_sup_set_class f1_wetrep a_sup_set_class a_cep a_wbr f1_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_cep a_wbr a_wa f0_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_cep a_wbr a_wi p_sylan f0_wetrep f1_wetrep p_epel f1_wetrep f2_wetrep p_epel f0_wetrep a_sup_set_class f1_wetrep a_sup_set_class a_cep a_wbr f0_wetrep a_sup_set_class f1_wetrep a_sup_set_class a_wcel f1_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_cep a_wbr f1_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_wcel p_anbi12i f0_wetrep f2_wetrep p_epel f3_wetrep a_cep a_wwe f0_wetrep a_sup_set_class f3_wetrep a_wcel f1_wetrep a_sup_set_class f3_wetrep a_wcel f2_wetrep a_sup_set_class f3_wetrep a_wcel a_w3a a_wa f0_wetrep a_sup_set_class f1_wetrep a_sup_set_class a_cep a_wbr f1_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_cep a_wbr a_wa f0_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_cep a_wbr f0_wetrep a_sup_set_class f1_wetrep a_sup_set_class a_wcel f1_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_wcel a_wa f0_wetrep a_sup_set_class f2_wetrep a_sup_set_class a_wcel p_3imtr3g $.
$}

$(A non-empty (possibly proper) subclass of a class well-ordered by ` _E `
       has a minimal element.  Special case of Proposition 6.26 of
       [TakeutiZaring] p. 31.  (Contributed by NM, 17-Feb-2004.) $)

${
	$v x A B  $.
	$d x y z  $.
	$d y z A  $.
	$d x y z B  $.
	f0_wefrc $f set x $.
	f1_wefrc $f class A $.
	f2_wefrc $f class B $.
	i0_wefrc $f set y $.
	i1_wefrc $f set z $.
	p_wefrc $p |- ( ( _E We A /\ B C_ A /\ B =/= (/) ) -> E. x e. B ( B i^i x ) = (/) ) $= f2_wefrc f1_wefrc a_cep p_wess i0_wefrc f2_wefrc p_n0 f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class f2_wefrc p_ineq2 f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 p_eqeq1d f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc i0_wefrc a_sup_set_class f2_wefrc p_rspcev i0_wefrc a_sup_set_class f2_wefrc a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex p_ex i0_wefrc a_sup_set_class f2_wefrc a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex a_wi f2_wefrc a_cep a_wwe p_adantl f2_wefrc i0_wefrc a_sup_set_class p_inss1 f2_wefrc a_cep p_wefr i0_wefrc p_vex i0_wefrc a_sup_set_class f2_wefrc p_inex2 f0_wefrc f2_wefrc f2_wefrc i0_wefrc a_sup_set_class a_cin p_epfrc f2_wefrc a_cep a_wwe f2_wefrc a_cep a_wfr f2_wefrc i0_wefrc a_sup_set_class a_cin f2_wefrc a_wss f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wne f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc i0_wefrc a_sup_set_class a_cin a_wrex p_syl3an1 f2_wefrc a_cep a_wwe f2_wefrc i0_wefrc a_sup_set_class a_cin f2_wefrc a_wss f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wne f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc i0_wefrc a_sup_set_class a_cin a_wrex p_3exp f2_wefrc a_cep a_wwe f2_wefrc i0_wefrc a_sup_set_class a_cin f2_wefrc a_wss f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wne f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc i0_wefrc a_sup_set_class a_cin a_wrex a_wi p_mpi f0_wefrc a_sup_set_class f2_wefrc i0_wefrc a_sup_set_class p_elin f0_wefrc a_sup_set_class f2_wefrc i0_wefrc a_sup_set_class a_cin a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wa f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq p_anbi1i f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq p_anass f0_wefrc a_sup_set_class f2_wefrc i0_wefrc a_sup_set_class a_cin a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wa f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa a_wa p_bitri f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f0_wefrc f2_wefrc i0_wefrc a_sup_set_class a_cin f2_wefrc p_rexbii2 f2_wefrc a_cep a_wwe f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wne f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc i0_wefrc a_sup_set_class a_cin a_wrex f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f0_wefrc f2_wefrc a_wrex p_syl6ib f2_wefrc a_cep a_wwe f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wne f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f0_wefrc f2_wefrc a_wrex a_wi i0_wefrc a_sup_set_class f2_wefrc a_wcel p_adantr i1_wefrc a_sup_set_class f2_wefrc f0_wefrc a_sup_set_class p_elin i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel a_df-3an i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel p_3anrot i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel a_w3a i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel i0_wefrc a_sup_set_class f2_wefrc a_wcel a_w3a p_bitr3i i1_wefrc f0_wefrc i0_wefrc f2_wefrc p_wetrep f2_wefrc a_cep a_wwe i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel i0_wefrc a_sup_set_class f2_wefrc a_wcel a_w3a a_wa i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel p_exp3a i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f2_wefrc a_cep a_wwe i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel i0_wefrc a_sup_set_class f2_wefrc a_wcel a_w3a i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wi a_wi p_sylan2b f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wi a_wi p_exp44 f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wi a_wi a_wi a_wi p_imp f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa i1_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wi p_com34 f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa i1_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wi a_wi p_imp3a i1_wefrc a_sup_set_class f2_wefrc f0_wefrc a_sup_set_class a_cin a_wcel i1_wefrc a_sup_set_class f2_wefrc a_wcel i1_wefrc a_sup_set_class f0_wefrc a_sup_set_class a_wcel a_wa f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wi a_wi p_syl5bi f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa i1_wefrc a_sup_set_class f2_wefrc f0_wefrc a_sup_set_class a_cin a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel p_imp4a f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa i1_wefrc a_sup_set_class f2_wefrc f0_wefrc a_sup_set_class a_cin a_wcel f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wa i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel p_com23 f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wa i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc f2_wefrc f0_wefrc a_sup_set_class a_cin p_ralrimdv i1_wefrc f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class p_dfss3 f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wa i1_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel i1_wefrc f2_wefrc f0_wefrc a_sup_set_class a_cin a_wral f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_wss p_syl6ibr f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class p_dfss f2_wefrc f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class p_in32 f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_cin f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin f2_wefrc f0_wefrc a_sup_set_class a_cin p_eqeq2i f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_wss f2_wefrc f0_wefrc a_sup_set_class a_cin f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_cin a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_wceq p_bitri f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_wss f2_wefrc f0_wefrc a_sup_set_class a_cin f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_wceq p_biimpi f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_wss f2_wefrc f0_wefrc a_sup_set_class a_cin f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 p_eqeq1d f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_wss f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq p_biimprd f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel a_wa f2_wefrc f0_wefrc a_sup_set_class a_cin i0_wefrc a_sup_set_class a_wss f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wi p_syl6 f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wi p_exp3a f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class f2_wefrc a_wcel f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq p_imp4a f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc p_reximdvai f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 a_wne f0_wefrc a_sup_set_class i0_wefrc a_sup_set_class a_wcel f2_wefrc i0_wefrc a_sup_set_class a_cin f0_wefrc a_sup_set_class a_cin a_c0 a_wceq a_wa f0_wefrc f2_wefrc a_wrex f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex p_syld f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel a_wa f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex f2_wefrc i0_wefrc a_sup_set_class a_cin a_c0 p_pm2.61dne f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex p_ex f2_wefrc a_cep a_wwe i0_wefrc a_sup_set_class f2_wefrc a_wcel f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex i0_wefrc p_exlimdv f2_wefrc a_c0 a_wne i0_wefrc a_sup_set_class f2_wefrc a_wcel i0_wefrc a_wex f2_wefrc a_cep a_wwe f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex p_syl5bi f2_wefrc f1_wefrc a_wss f1_wefrc a_cep a_wwe f2_wefrc a_cep a_wwe f2_wefrc a_c0 a_wne f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex a_wi p_syl6com f1_wefrc a_cep a_wwe f2_wefrc f1_wefrc a_wss f2_wefrc a_c0 a_wne f2_wefrc f0_wefrc a_sup_set_class a_cin a_c0 a_wceq f0_wefrc f2_wefrc a_wrex p_3imp $.
$}

$(Any relation is a well-ordering of the empty set.  (Contributed by NM,
     16-Mar-1997.) $)

${
	$v R  $.
	f0_we0 $f class R $.
	p_we0 $p |- R We (/) $= f0_we0 p_fr0 f0_we0 p_so0 a_c0 f0_we0 a_df-we a_c0 f0_we0 a_wwe a_c0 f0_we0 a_wfr a_c0 f0_we0 a_wor p_mpbir2an $.
$}

$(A subset of a well-ordered set has a unique minimal element.
       (Contributed by NM, 18-Mar-1997.)  (Revised by Mario Carneiro,
       28-Apr-2015.) $)

${
	$v x y A B R V  $.
	$d x y A  $.
	$d x y B  $.
	$d x y R  $.
	f0_wereu $f set x $.
	f1_wereu $f set y $.
	f2_wereu $f class A $.
	f3_wereu $f class B $.
	f4_wereu $f class R $.
	f5_wereu $f class V $.
	p_wereu $p |- ( ( R We A /\ ( B e. V /\ B C_ A /\ B =/= (/) ) ) -> E! x e. B A. y e. B -. y R x ) $= f2_wereu f4_wereu p_wefr f0_wereu f1_wereu f2_wereu f3_wereu f5_wereu f4_wereu p_fri f3_wereu f5_wereu a_wcel f2_wereu f4_wereu a_wfr a_wa f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrex p_exp32 f3_wereu f5_wereu a_wcel f2_wereu f4_wereu a_wfr f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrex a_wi a_wi p_expcom f2_wereu f4_wereu a_wfr f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrex p_3imp2 f2_wereu f4_wereu a_wwe f2_wereu f4_wereu a_wfr f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne a_w3a f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrex p_sylan f2_wereu f4_wereu a_wwe f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne p_simpr2 f2_wereu f4_wereu p_weso f2_wereu f4_wereu a_wwe f2_wereu f4_wereu a_wor f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne a_w3a p_adantr f3_wereu f2_wereu f4_wereu p_soss f2_wereu f4_wereu a_wwe f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne a_w3a a_wa f3_wereu f2_wereu a_wss f2_wereu f4_wereu a_wor f3_wereu f4_wereu a_wor p_sylc f0_wereu f1_wereu f3_wereu f4_wereu p_somo f2_wereu f4_wereu a_wwe f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne a_w3a a_wa f3_wereu f4_wereu a_wor f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrmo p_syl f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu p_reu5 f2_wereu f4_wereu a_wwe f3_wereu f5_wereu a_wcel f3_wereu f2_wereu a_wss f3_wereu a_c0 a_wne a_w3a a_wa f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrex f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wrmo f1_wereu a_sup_set_class f0_wereu a_sup_set_class f4_wereu a_wbr a_wn f1_wereu f3_wereu a_wral f0_wereu f3_wereu a_wreu p_sylanbrc $.
$}

$(All nonempty (possibly proper) subclasses of ` A ` , which has a
       well-founded relation ` R ` , have ` R `-minimal elements.  Proposition
       6.26 of [TakeutiZaring] p. 31.  (Contributed by Scott Fenton,
       29-Jan-2011.)  (Revised by Mario Carneiro, 24-Jun-2015.) $)

${
	$v x y A B R  $.
	$d x y z A  $.
	$d w x y z B  $.
	$d w x y z R  $.
	f0_wereu2 $f set x $.
	f1_wereu2 $f set y $.
	f2_wereu2 $f class A $.
	f3_wereu2 $f class B $.
	f4_wereu2 $f class R $.
	i0_wereu2 $f set z $.
	i1_wereu2 $f set w $.
	p_wereu2 $p |- ( ( ( R We A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) -> E! x e. B A. y e. B -. y R x ) $= i0_wereu2 f3_wereu2 p_n0 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 p_rabeq0 f1_wereu2 a_sup_set_class i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 p_breq1 f1_wereu2 a_sup_set_class i1_wereu2 a_sup_set_class a_wceq f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr p_notbid f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 f3_wereu2 p_cbvralv f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class i1_wereu2 a_sup_set_class f4_wereu2 p_breq2 f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class a_wceq i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr p_notbid f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class a_wceq i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 p_ralbidv f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 a_wral f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class a_wceq i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 a_wral p_syl5bb f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 a_wral f0_wereu2 i0_wereu2 a_sup_set_class f3_wereu2 p_rspcev i0_wereu2 a_sup_set_class f3_wereu2 a_wcel i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 a_wral f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_ex i0_wereu2 a_sup_set_class f3_wereu2 a_wcel i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 a_wral f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex a_wi f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss p_ad2antll i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_c0 a_wceq i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn i1_wereu2 f3_wereu2 a_wral f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_syl5bi f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simprl f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa p_simplr f3_wereu2 f2_wereu2 f4_wereu2 p_sess2 f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f3_wereu2 f2_wereu2 a_wss f2_wereu2 f4_wereu2 a_wse f3_wereu2 f4_wereu2 a_wse p_sylc f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simprr i1_wereu2 f3_wereu2 i0_wereu2 a_sup_set_class f4_wereu2 p_seex f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f3_wereu2 f4_wereu2 a_wse i0_wereu2 a_sup_set_class f3_wereu2 a_wcel i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_cvv a_wcel p_syl2anc f2_wereu2 f4_wereu2 p_wefr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wfr f2_wereu2 f4_wereu2 a_wse f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa p_ad2antrr i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 p_ssrab2 f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simprl f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab f3_wereu2 f2_wereu2 p_syl5ss f0_wereu2 f1_wereu2 f2_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_cvv f4_wereu2 p_fri i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_cvv a_wcel f2_wereu2 f4_wereu2 a_wfr a_wa i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab f2_wereu2 a_wss i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_c0 a_wne f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f0_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wrex p_expr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_cvv a_wcel f2_wereu2 f4_wereu2 a_wfr i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab f2_wereu2 a_wss i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_c0 a_wne f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f0_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wrex a_wi p_syl21anc i1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 p_breq1 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f0_wereu2 i1_wereu2 f3_wereu2 p_rexrab i1_wereu2 a_sup_set_class f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 p_breq1 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 f3_wereu2 p_ralrab f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simprl f2_wereu2 f4_wereu2 p_weso f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wor f2_wereu2 f4_wereu2 a_wse f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa p_ad2antrr f3_wereu2 f2_wereu2 f4_wereu2 p_soss f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f3_wereu2 f2_wereu2 a_wss f2_wereu2 f4_wereu2 a_wor f3_wereu2 f4_wereu2 a_wor p_sylc f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f3_wereu2 f4_wereu2 a_wor f0_wereu2 a_sup_set_class f3_wereu2 a_wcel f1_wereu2 a_sup_set_class f3_wereu2 a_wcel p_ad2antrr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simpr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel f1_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simplr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel p_simprr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa i0_wereu2 a_sup_set_class f3_wereu2 a_wcel f0_wereu2 a_sup_set_class f3_wereu2 a_wcel f1_wereu2 a_sup_set_class f3_wereu2 a_wcel p_ad2antrr f3_wereu2 f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 p_sotr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f3_wereu2 f4_wereu2 a_wor f1_wereu2 a_sup_set_class f3_wereu2 a_wcel f0_wereu2 a_sup_set_class f3_wereu2 a_wcel i0_wereu2 a_sup_set_class f3_wereu2 a_wcel f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wa f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wi p_syl13anc f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr p_ancomsd f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr p_expdimp f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wi p_an32s f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr p_con3d f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn p_idd f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wa f1_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn p_jad f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wa f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn a_wi f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 p_ralimdva f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn a_wi f1_wereu2 f3_wereu2 a_wral f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral p_syl5bi f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral p_expimpd f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 p_reximdva f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f0_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wrex f0_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral a_wa f0_wereu2 f3_wereu2 a_wrex f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_syl5bi f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_c0 a_wne f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wral f0_wereu2 i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_wrex f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_syld f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel a_wa a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex i1_wereu2 a_sup_set_class i0_wereu2 a_sup_set_class f4_wereu2 a_wbr i1_wereu2 f3_wereu2 a_crab a_c0 p_pm2.61dne f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss i0_wereu2 a_sup_set_class f3_wereu2 a_wcel f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_expr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss a_wa i0_wereu2 a_sup_set_class f3_wereu2 a_wcel f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex i0_wereu2 p_exlimdv f3_wereu2 a_c0 a_wne i0_wereu2 a_sup_set_class f3_wereu2 a_wcel i0_wereu2 a_wex f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_syl5bi f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss f3_wereu2 a_c0 a_wne f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex p_impr f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss f3_wereu2 a_c0 a_wne p_simprl f2_wereu2 f4_wereu2 p_weso f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wor f2_wereu2 f4_wereu2 a_wse f3_wereu2 f2_wereu2 a_wss f3_wereu2 a_c0 a_wne a_wa p_ad2antrr f3_wereu2 f2_wereu2 f4_wereu2 p_soss f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss f3_wereu2 a_c0 a_wne a_wa a_wa f3_wereu2 f2_wereu2 a_wss f2_wereu2 f4_wereu2 a_wor f3_wereu2 f4_wereu2 a_wor p_sylc f0_wereu2 f1_wereu2 f3_wereu2 f4_wereu2 p_somo f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss f3_wereu2 a_c0 a_wne a_wa a_wa f3_wereu2 f4_wereu2 a_wor f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrmo p_syl f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 p_reu5 f2_wereu2 f4_wereu2 a_wwe f2_wereu2 f4_wereu2 a_wse a_wa f3_wereu2 f2_wereu2 a_wss f3_wereu2 a_c0 a_wne a_wa a_wa f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrex f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wrmo f1_wereu2 a_sup_set_class f0_wereu2 a_sup_set_class f4_wereu2 a_wbr a_wn f1_wereu2 f3_wereu2 a_wral f0_wereu2 f3_wereu2 a_wreu p_sylanbrc $.
$}


