$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_difference,_union,_and_intersection_of_two_classes.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           The empty set

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare the symbol for the empty or null set. $)

$c (/) $.

$(null set $)

$(Extend class notation to include the empty set. $)

${
	$v  $.
	a_c0 $a class (/) $.
$}

$(Define the empty set.  Special case of Exercise 4.10(o) of [Mendelson]
     p. 231.  For a more traditional definition, but requiring a dummy
     variable, see ~ dfnul2 .  (Contributed by NM, 5-Aug-1993.) $)

${
	$v  $.
	a_df-nul $a |- (/) = ( _V \ _V ) $.
$}

$(Alternate definition of the empty set.  Definition 5.14 of [TakeutiZaring]
     p. 20.  (Contributed by NM, 26-Dec-1996.) $)

${
	$v x  $.
	f0_dfnul2 $f set x $.
	p_dfnul2 $p |- (/) = { x | -. x = x } $= a_df-nul a_c0 a_cvv a_cvv a_cdif f0_dfnul2 a_sup_set_class p_eleq2i f0_dfnul2 a_sup_set_class a_cvv a_cvv p_eldif f0_dfnul2 a_sup_set_class p_eqid f0_dfnul2 a_sup_set_class a_cvv a_wcel p_pm3.24 f0_dfnul2 a_sup_set_class f0_dfnul2 a_sup_set_class a_wceq f0_dfnul2 a_sup_set_class a_cvv a_wcel f0_dfnul2 a_sup_set_class a_cvv a_wcel a_wn a_wa a_wn p_2th f0_dfnul2 a_sup_set_class f0_dfnul2 a_sup_set_class a_wceq f0_dfnul2 a_sup_set_class a_cvv a_wcel f0_dfnul2 a_sup_set_class a_cvv a_wcel a_wn a_wa p_con2bii f0_dfnul2 a_sup_set_class a_c0 a_wcel f0_dfnul2 a_sup_set_class a_cvv a_cvv a_cdif a_wcel f0_dfnul2 a_sup_set_class a_cvv a_wcel f0_dfnul2 a_sup_set_class a_cvv a_wcel a_wn a_wa f0_dfnul2 a_sup_set_class f0_dfnul2 a_sup_set_class a_wceq a_wn p_3bitri f0_dfnul2 a_sup_set_class f0_dfnul2 a_sup_set_class a_wceq a_wn f0_dfnul2 a_c0 p_abbi2i $.
$}

$(Alternate definition of the empty set.  (Contributed by NM,
     25-Mar-2004.) $)

${
	$v x A  $.
	f0_dfnul3 $f set x $.
	f1_dfnul3 $f class A $.
	p_dfnul3 $p |- (/) = { x e. A | -. x e. A } $= f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel p_pm3.24 f0_dfnul3 a_sup_set_class p_eqid f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel a_wn a_wa a_wn f0_dfnul3 a_sup_set_class f0_dfnul3 a_sup_set_class a_wceq p_2th f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel a_wn a_wa f0_dfnul3 a_sup_set_class f0_dfnul3 a_sup_set_class a_wceq p_con1bii f0_dfnul3 a_sup_set_class f0_dfnul3 a_sup_set_class a_wceq a_wn f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel a_wn a_wa f0_dfnul3 p_abbii f0_dfnul3 p_dfnul2 f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel a_wn f0_dfnul3 f1_dfnul3 a_df-rab f0_dfnul3 a_sup_set_class f0_dfnul3 a_sup_set_class a_wceq a_wn f0_dfnul3 a_cab f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel a_wn a_wa f0_dfnul3 a_cab a_c0 f0_dfnul3 a_sup_set_class f1_dfnul3 a_wcel a_wn f0_dfnul3 f1_dfnul3 a_crab p_3eqtr4i $.
$}

$(The empty set has no elements.  Theorem 6.14 of [Quine] p. 44.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Mario Carneiro,
     1-Sep-2015.) $)

${
	$v A  $.
	f0_noel $f class A $.
	p_noel $p |- -. A e. (/) $= f0_noel a_cvv a_cvv p_eldifi f0_noel a_cvv a_cvv p_eldifn f0_noel a_cvv a_cvv a_cdif a_wcel f0_noel a_cvv a_wcel p_pm2.65i a_df-nul a_c0 a_cvv a_cvv a_cdif f0_noel p_eleq2i f0_noel a_c0 a_wcel f0_noel a_cvv a_cvv a_cdif a_wcel p_mtbir $.
$}

$(If a set has elements, it is not empty.  (Contributed by NM,
     31-Dec-1993.) $)

${
	$v A B  $.
	f0_n0i $f class A $.
	f1_n0i $f class B $.
	p_n0i $p |- ( B e. A -> -. A = (/) ) $= f1_n0i p_noel f0_n0i a_c0 f1_n0i p_eleq2 f0_n0i a_c0 a_wceq f1_n0i f0_n0i a_wcel f1_n0i a_c0 a_wcel p_mtbiri f0_n0i a_c0 a_wceq f1_n0i f0_n0i a_wcel p_con2i $.
$}

$(If a set has elements, it is not empty.  (Contributed by NM,
     31-Dec-1993.) $)

${
	$v A B  $.
	f0_ne0i $f class A $.
	f1_ne0i $f class B $.
	p_ne0i $p |- ( B e. A -> A =/= (/) ) $= f0_ne0i f1_ne0i p_n0i f0_ne0i a_c0 a_df-ne f1_ne0i f0_ne0i a_wcel f0_ne0i a_c0 a_wceq a_wn f0_ne0i a_c0 a_wne p_sylibr $.
$}

$(The universal class is not equal to the empty set.  (Contributed by NM,
     11-Sep-2008.) $)

${
	$v  $.
	i0_vn0 $f set x $.
	p_vn0 $p |- _V =/= (/) $= i0_vn0 p_vex a_cvv i0_vn0 a_sup_set_class p_ne0i i0_vn0 a_sup_set_class a_cvv a_wcel a_cvv a_c0 a_wne a_ax-mp $.
$}

$(A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  This version of ~ n0 requires only that ` x `
       not be free in, rather than not occur in, ` A ` .  (Contributed by NM,
       17-Oct-2003.) $)

${
	$v x A  $.
	$d x  $.
	$d A  $.
	f0_n0f $f set x $.
	f1_n0f $f class A $.
	e0_n0f $e |- F/_ x A $.
	p_n0f $p |- ( A =/= (/) <-> E. x x e. A ) $= e0_n0f f0_n0f a_c0 p_nfcv f0_n0f f1_n0f a_c0 p_cleqf f0_n0f a_sup_set_class p_noel f0_n0f a_sup_set_class a_c0 a_wcel f0_n0f a_sup_set_class f1_n0f a_wcel p_nbn f0_n0f a_sup_set_class f1_n0f a_wcel a_wn f0_n0f a_sup_set_class f1_n0f a_wcel f0_n0f a_sup_set_class a_c0 a_wcel a_wb f0_n0f p_albii f1_n0f a_c0 a_wceq f0_n0f a_sup_set_class f1_n0f a_wcel f0_n0f a_sup_set_class a_c0 a_wcel a_wb f0_n0f a_wal f0_n0f a_sup_set_class f1_n0f a_wcel a_wn f0_n0f a_wal p_bitr4i f0_n0f a_sup_set_class f1_n0f a_wcel a_wn f0_n0f a_wal f1_n0f a_c0 p_necon3abii f0_n0f a_sup_set_class f1_n0f a_wcel f0_n0f a_df-ex f1_n0f a_c0 a_wne f0_n0f a_sup_set_class f1_n0f a_wcel a_wn f0_n0f a_wal a_wn f0_n0f a_sup_set_class f1_n0f a_wcel f0_n0f a_wex p_bitr4i $.
$}

$(A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  (Contributed by NM, 29-Sep-2006.) $)

${
	$v x A  $.
	$d x A  $.
	f0_n0 $f set x $.
	f1_n0 $f class A $.
	p_n0 $p |- ( A =/= (/) <-> E. x x e. A ) $= f0_n0 f1_n0 p_nfcv f0_n0 f1_n0 p_n0f $.
$}

$(A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_neq0 $f set x $.
	f1_neq0 $f class A $.
	p_neq0 $p |- ( -. A = (/) <-> E. x x e. A ) $= f1_neq0 a_c0 a_df-ne f0_neq0 f1_neq0 p_n0 f1_neq0 a_c0 a_wceq a_wn f1_neq0 a_c0 a_wne f0_neq0 a_sup_set_class f1_neq0 a_wcel f0_neq0 a_wex p_bitr3i $.
$}

$(Restricted existence deduced from non-empty class.  (Contributed by NM,
       1-Feb-2012.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ph  $.
	f0_reximdva0 $f wff ph $.
	f1_reximdva0 $f wff ps $.
	f2_reximdva0 $f set x $.
	f3_reximdva0 $f class A $.
	e0_reximdva0 $e |- ( ( ph /\ x e. A ) -> ps ) $.
	p_reximdva0 $p |- ( ( ph /\ A =/= (/) ) -> E. x e. A ps ) $= f2_reximdva0 f3_reximdva0 p_n0 e0_reximdva0 f0_reximdva0 f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f1_reximdva0 p_ex f0_reximdva0 f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f1_reximdva0 p_ancld f0_reximdva0 f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f1_reximdva0 a_wa f2_reximdva0 p_eximdv f0_reximdva0 f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f2_reximdva0 a_wex f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f1_reximdva0 a_wa f2_reximdva0 a_wex p_imp f3_reximdva0 a_c0 a_wne f0_reximdva0 f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f2_reximdva0 a_wex f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f1_reximdva0 a_wa f2_reximdva0 a_wex p_sylan2b f1_reximdva0 f2_reximdva0 f3_reximdva0 a_df-rex f0_reximdva0 f3_reximdva0 a_c0 a_wne a_wa f2_reximdva0 a_sup_set_class f3_reximdva0 a_wcel f1_reximdva0 a_wa f2_reximdva0 a_wex f1_reximdva0 f2_reximdva0 f3_reximdva0 a_wrex p_sylibr $.
$}

$(A case of equivalence of "at most one" and "only one".  (Contributed by
       FL, 6-Dec-2010.) $)

${
	$v x A  $.
	$d A x  $.
	f0_n0moeu $f set x $.
	f1_n0moeu $f class A $.
	p_n0moeu $p |- ( A =/= (/) -> ( E* x x e. A <-> E! x x e. A ) ) $= f0_n0moeu f1_n0moeu p_n0 f1_n0moeu a_c0 a_wne f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_wex p_biimpi f1_n0moeu a_c0 a_wne f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_wex f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_wmo p_biantrurd f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu p_eu5 f1_n0moeu a_c0 a_wne f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_wmo f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_wex f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_wmo a_wa f0_n0moeu a_sup_set_class f1_n0moeu a_wcel f0_n0moeu a_weu p_syl6bbr $.
$}

$(Vacuous existential quantification is false.  (Contributed by NM,
     15-Oct-2003.) $)

${
	$v ph x  $.
	f0_rex0 $f wff ph $.
	f1_rex0 $f set x $.
	p_rex0 $p |- -. E. x e. (/) ph $= f1_rex0 a_sup_set_class p_noel f1_rex0 a_sup_set_class a_c0 a_wcel f0_rex0 a_wn p_pm2.21i f0_rex0 f1_rex0 a_c0 p_nrex $.
$}

$(The empty set has no elements.  Theorem 2 of [Suppes] p. 22.
       (Contributed by NM, 29-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_eq0 $f set x $.
	f1_eq0 $f class A $.
	p_eq0 $p |- ( A = (/) <-> A. x -. x e. A ) $= f0_eq0 f1_eq0 p_neq0 f0_eq0 a_sup_set_class f1_eq0 a_wcel f0_eq0 a_df-ex f1_eq0 a_c0 a_wceq a_wn f0_eq0 a_sup_set_class f1_eq0 a_wcel f0_eq0 a_wex f0_eq0 a_sup_set_class f1_eq0 a_wcel a_wn f0_eq0 a_wal a_wn p_bitri f1_eq0 a_c0 a_wceq f0_eq0 a_sup_set_class f1_eq0 a_wcel a_wn f0_eq0 a_wal p_con4bii $.
$}

$(The universe contains every set.  (Contributed by NM, 11-Sep-2006.) $)

${
	$v x A  $.
	$d x A  $.
	f0_eqv $f set x $.
	f1_eqv $f class A $.
	p_eqv $p |- ( A = _V <-> A. x x e. A ) $= f0_eqv f1_eqv a_cvv p_dfcleq f0_eqv p_vex f0_eqv a_sup_set_class a_cvv a_wcel f0_eqv a_sup_set_class f1_eqv a_wcel p_tbt f0_eqv a_sup_set_class f1_eqv a_wcel f0_eqv a_sup_set_class f1_eqv a_wcel f0_eqv a_sup_set_class a_cvv a_wcel a_wb f0_eqv p_albii f1_eqv a_cvv a_wceq f0_eqv a_sup_set_class f1_eqv a_wcel f0_eqv a_sup_set_class a_cvv a_wcel a_wb f0_eqv a_wal f0_eqv a_sup_set_class f1_eqv a_wcel f0_eqv a_wal p_bitr4i $.
$}

$(Membership of the empty set in another class.  (Contributed by NM,
       29-Jun-2004.) $)

${
	$v x y A  $.
	$d x A  $.
	$d x y  $.
	f0_0el $f set x $.
	f1_0el $f set y $.
	f2_0el $f class A $.
	p_0el $p |- ( (/) e. A <-> E. x e. A A. y -. y e. x ) $= f0_0el a_c0 f2_0el p_risset f1_0el f0_0el a_sup_set_class p_eq0 f0_0el a_sup_set_class a_c0 a_wceq f1_0el a_sup_set_class f0_0el a_sup_set_class a_wcel a_wn f1_0el a_wal f0_0el f2_0el p_rexbii a_c0 f2_0el a_wcel f0_0el a_sup_set_class a_c0 a_wceq f0_0el f2_0el a_wrex f1_0el a_sup_set_class f0_0el a_sup_set_class a_wcel a_wn f1_0el a_wal f0_0el f2_0el a_wrex p_bitri $.
$}

$(The class builder of a wff not containing the abstraction variable is
       either the universal class or the empty set.  (Contributed by Mario
       Carneiro, 29-Aug-2013.) $)

${
	$v ph x  $.
	$d x ph  $.
	f0_abvor0 $f wff ph $.
	f1_abvor0 $f set x $.
	p_abvor0 $p |- ( { x | ph } = _V \/ { x | ph } = (/) ) $= f0_abvor0 p_id f1_abvor0 p_vex f1_abvor0 a_sup_set_class a_cvv a_wcel f0_abvor0 p_a1i f0_abvor0 f0_abvor0 f1_abvor0 a_sup_set_class a_cvv a_wcel p_2thd f0_abvor0 f0_abvor0 f1_abvor0 a_cvv p_abbi1dv f0_abvor0 f0_abvor0 f1_abvor0 a_cab a_cvv a_wceq p_con3i f0_abvor0 a_wn p_id f1_abvor0 a_sup_set_class p_noel f1_abvor0 a_sup_set_class a_c0 a_wcel a_wn f0_abvor0 a_wn p_a1i f0_abvor0 a_wn f0_abvor0 f1_abvor0 a_sup_set_class a_c0 a_wcel p_2falsed f0_abvor0 a_wn f0_abvor0 f1_abvor0 a_c0 p_abbi1dv f0_abvor0 f1_abvor0 a_cab a_cvv a_wceq a_wn f0_abvor0 a_wn f0_abvor0 f1_abvor0 a_cab a_c0 a_wceq p_syl f0_abvor0 f1_abvor0 a_cab a_cvv a_wceq f0_abvor0 f1_abvor0 a_cab a_c0 a_wceq p_orri $.
$}

$(Nonempty class abstraction.  (Contributed by NM, 26-Dec-1996.)  (Proof
       shortened by Mario Carneiro, 11-Nov-2016.) $)

${
	$v ph x  $.
	$d x  $.
	$d ph  $.
	f0_abn0 $f wff ph $.
	f1_abn0 $f set x $.
	p_abn0 $p |- ( { x | ph } =/= (/) <-> E. x ph ) $= f0_abn0 f1_abn0 p_nfab1 f1_abn0 f0_abn0 f1_abn0 a_cab p_n0f f0_abn0 f1_abn0 p_abid f1_abn0 a_sup_set_class f0_abn0 f1_abn0 a_cab a_wcel f0_abn0 f1_abn0 p_exbii f0_abn0 f1_abn0 a_cab a_c0 a_wne f1_abn0 a_sup_set_class f0_abn0 f1_abn0 a_cab a_wcel f1_abn0 a_wex f0_abn0 f1_abn0 a_wex p_bitri $.
$}

$(Non-empty restricted class abstraction.  (Contributed by NM,
     29-Aug-1999.) $)

${
	$v ph x A  $.
	f0_rabn0 $f wff ph $.
	f1_rabn0 $f set x $.
	f2_rabn0 $f class A $.
	p_rabn0 $p |- ( { x e. A | ph } =/= (/) <-> E. x e. A ph ) $= f1_rabn0 a_sup_set_class f2_rabn0 a_wcel f0_rabn0 a_wa f1_rabn0 p_abn0 f0_rabn0 f1_rabn0 f2_rabn0 a_df-rab f0_rabn0 f1_rabn0 f2_rabn0 a_crab f1_rabn0 a_sup_set_class f2_rabn0 a_wcel f0_rabn0 a_wa f1_rabn0 a_cab a_c0 p_neeq1i f0_rabn0 f1_rabn0 f2_rabn0 a_df-rex f1_rabn0 a_sup_set_class f2_rabn0 a_wcel f0_rabn0 a_wa f1_rabn0 a_cab a_c0 a_wne f1_rabn0 a_sup_set_class f2_rabn0 a_wcel f0_rabn0 a_wa f1_rabn0 a_wex f0_rabn0 f1_rabn0 f2_rabn0 a_crab a_c0 a_wne f0_rabn0 f1_rabn0 f2_rabn0 a_wrex p_3bitr4i $.
$}

$(Any restricted class abstraction restricted to the empty set is empty.
     (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)

${
	$v ph x  $.
	f0_rab0 $f wff ph $.
	f1_rab0 $f set x $.
	p_rab0 $p |- { x e. (/) | ph } = (/) $= f1_rab0 p_equid f1_rab0 a_sup_set_class p_noel f1_rab0 a_sup_set_class a_c0 a_wcel f0_rab0 p_intnanr f1_rab0 a_sup_set_class f1_rab0 a_sup_set_class a_wceq f1_rab0 a_sup_set_class a_c0 a_wcel f0_rab0 a_wa a_wn p_2th f1_rab0 a_sup_set_class f1_rab0 a_sup_set_class a_wceq f1_rab0 a_sup_set_class a_c0 a_wcel f0_rab0 a_wa p_con2bii f1_rab0 a_sup_set_class a_c0 a_wcel f0_rab0 a_wa f1_rab0 a_sup_set_class f1_rab0 a_sup_set_class a_wceq a_wn f1_rab0 p_abbii f0_rab0 f1_rab0 a_c0 a_df-rab f1_rab0 p_dfnul2 f1_rab0 a_sup_set_class a_c0 a_wcel f0_rab0 a_wa f1_rab0 a_cab f1_rab0 a_sup_set_class f1_rab0 a_sup_set_class a_wceq a_wn f1_rab0 a_cab f0_rab0 f1_rab0 a_c0 a_crab a_c0 p_3eqtr4i $.
$}

$(Condition for a restricted class abstraction to be empty.  (Contributed by
     Jeff Madsen, 7-Jun-2010.) $)

${
	$v ph x A  $.
	f0_rabeq0 $f wff ph $.
	f1_rabeq0 $f set x $.
	f2_rabeq0 $f class A $.
	p_rabeq0 $p |- ( { x e. A | ph } = (/) <-> A. x e. A -. ph ) $= f0_rabeq0 f1_rabeq0 f2_rabeq0 p_ralnex f0_rabeq0 f1_rabeq0 f2_rabeq0 p_rabn0 f0_rabeq0 f1_rabeq0 f2_rabeq0 a_wrex f0_rabeq0 f1_rabeq0 f2_rabeq0 a_crab a_c0 p_necon1bbii f0_rabeq0 a_wn f1_rabeq0 f2_rabeq0 a_wral f0_rabeq0 f1_rabeq0 f2_rabeq0 a_wrex a_wn f0_rabeq0 f1_rabeq0 f2_rabeq0 a_crab a_c0 a_wceq p_bitr2i $.
$}

$(Law of excluded middle, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) $)

${
	$v ph x A  $.
	$d A x  $.
	f0_rabxm $f wff ph $.
	f1_rabxm $f set x $.
	f2_rabxm $f class A $.
	p_rabxm $p |- A = ( { x e. A | ph } u. { x e. A | -. ph } ) $= f0_rabxm f0_rabxm a_wn a_wo f1_rabxm f2_rabxm p_rabid2 f0_rabxm p_exmid f0_rabxm f0_rabxm a_wn a_wo f1_rabxm a_sup_set_class f2_rabxm a_wcel p_a1i f2_rabxm f0_rabxm f0_rabxm a_wn a_wo f1_rabxm f2_rabxm a_crab a_wceq f0_rabxm f0_rabxm a_wn a_wo f1_rabxm f2_rabxm p_mprgbir f0_rabxm f0_rabxm a_wn f1_rabxm f2_rabxm p_unrab f2_rabxm f0_rabxm f0_rabxm a_wn a_wo f1_rabxm f2_rabxm a_crab f0_rabxm f1_rabxm f2_rabxm a_crab f0_rabxm a_wn f1_rabxm f2_rabxm a_crab a_cun p_eqtr4i $.
$}

$(Law of noncontradiction, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) $)

${
	$v ph x A  $.
	$d A x  $.
	f0_rabnc $f wff ph $.
	f1_rabnc $f set x $.
	f2_rabnc $f class A $.
	p_rabnc $p |- ( { x e. A | ph } i^i { x e. A | -. ph } ) = (/) $= f0_rabnc f0_rabnc a_wn f1_rabnc f2_rabnc p_inrab f0_rabnc f0_rabnc a_wn a_wa f1_rabnc f2_rabnc p_rabeq0 f0_rabnc p_pm3.24 f0_rabnc f0_rabnc a_wn a_wa a_wn f1_rabnc a_sup_set_class f2_rabnc a_wcel p_a1i f0_rabnc f0_rabnc a_wn a_wa f1_rabnc f2_rabnc a_crab a_c0 a_wceq f0_rabnc f0_rabnc a_wn a_wa a_wn f1_rabnc f2_rabnc p_mprgbir f0_rabnc f1_rabnc f2_rabnc a_crab f0_rabnc a_wn f1_rabnc f2_rabnc a_crab a_cin f0_rabnc f0_rabnc a_wn a_wa f1_rabnc f2_rabnc a_crab a_c0 p_eqtri $.
$}

$(The union of a class with the empty set is itself.  Theorem 24 of
       [Suppes] p. 27.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d x A  $.
	f0_un0 $f class A $.
	i0_un0 $f set x $.
	p_un0 $p |- ( A u. (/) ) = A $= i0_un0 a_sup_set_class p_noel i0_un0 a_sup_set_class a_c0 a_wcel i0_un0 a_sup_set_class f0_un0 a_wcel p_biorfi i0_un0 a_sup_set_class f0_un0 a_wcel i0_un0 a_sup_set_class f0_un0 a_wcel i0_un0 a_sup_set_class a_c0 a_wcel a_wo p_bicomi i0_un0 f0_un0 a_c0 f0_un0 p_uneqri $.
$}

$(The intersection of a class with the empty set is the empty set.
       Theorem 16 of [Suppes] p. 26.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d x A  $.
	f0_in0 $f class A $.
	i0_in0 $f set x $.
	p_in0 $p |- ( A i^i (/) ) = (/) $= i0_in0 a_sup_set_class p_noel i0_in0 a_sup_set_class a_c0 a_wcel i0_in0 a_sup_set_class f0_in0 a_wcel p_bianfi i0_in0 a_sup_set_class a_c0 a_wcel i0_in0 a_sup_set_class f0_in0 a_wcel i0_in0 a_sup_set_class a_c0 a_wcel a_wa p_bicomi i0_in0 f0_in0 a_c0 a_c0 p_ineqri $.
$}

$(The intersection of a class with the universal class is itself.  Exercise
     4.10(k) of [Mendelson] p. 231.  (Contributed by NM, 17-May-1998.) $)

${
	$v A  $.
	f0_inv1 $f class A $.
	p_inv1 $p |- ( A i^i _V ) = A $= f0_inv1 a_cvv p_inss1 f0_inv1 p_ssid f0_inv1 p_ssv f0_inv1 f0_inv1 a_cvv p_ssini f0_inv1 a_cvv a_cin f0_inv1 p_eqssi $.
$}

$(The union of a class with the universal class is the universal class.
     Exercise 4.10(l) of [Mendelson] p. 231.  (Contributed by NM,
     17-May-1998.) $)

${
	$v A  $.
	f0_unv $f class A $.
	p_unv $p |- ( A u. _V ) = _V $= f0_unv a_cvv a_cun p_ssv a_cvv f0_unv p_ssun2 f0_unv a_cvv a_cun a_cvv p_eqssi $.
$}

$(The null set is a subset of any class.  Part of Exercise 1 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d A x  $.
	f0_0ss $f class A $.
	i0_0ss $f set x $.
	p_0ss $p |- (/) C_ A $= i0_0ss a_sup_set_class p_noel i0_0ss a_sup_set_class a_c0 a_wcel i0_0ss a_sup_set_class f0_0ss a_wcel p_pm2.21i i0_0ss a_c0 f0_0ss p_ssriv $.
$}

$(Any subset of the empty set is empty.  Theorem 5 of [Suppes] p. 23 and its
     converse.  (Contributed by NM, 17-Sep-2003.) $)

${
	$v A  $.
	f0_ss0b $f class A $.
	p_ss0b $p |- ( A C_ (/) <-> A = (/) ) $= f0_ss0b p_0ss f0_ss0b a_c0 p_eqss f0_ss0b a_c0 a_wceq f0_ss0b a_c0 a_wss a_c0 f0_ss0b a_wss p_mpbiran2 f0_ss0b a_c0 a_wceq f0_ss0b a_c0 a_wss p_bicomi $.
$}

$(Any subset of the empty set is empty.  Theorem 5 of [Suppes] p. 23.
     (Contributed by NM, 13-Aug-1994.) $)

${
	$v A  $.
	f0_ss0 $f class A $.
	p_ss0 $p |- ( A C_ (/) -> A = (/) ) $= f0_ss0 p_ss0b f0_ss0 a_c0 a_wss f0_ss0 a_c0 a_wceq p_biimpi $.
$}

$(A subclass of an empty class is empty.  (Contributed by NM, 7-Mar-2007.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	f0_sseq0 $f class A $.
	f1_sseq0 $f class B $.
	p_sseq0 $p |- ( ( A C_ B /\ B = (/) ) -> A = (/) ) $= f1_sseq0 a_c0 f0_sseq0 p_sseq2 f0_sseq0 p_ss0 f1_sseq0 a_c0 a_wceq f0_sseq0 f1_sseq0 a_wss f0_sseq0 a_c0 a_wss f0_sseq0 a_c0 a_wceq p_syl6bi f1_sseq0 a_c0 a_wceq f0_sseq0 f1_sseq0 a_wss f0_sseq0 a_c0 a_wceq p_impcom $.
$}

$(A class with a nonempty subclass is nonempty.  (Contributed by NM,
     17-Feb-2007.) $)

${
	$v A B  $.
	f0_ssn0 $f class A $.
	f1_ssn0 $f class B $.
	p_ssn0 $p |- ( ( A C_ B /\ A =/= (/) ) -> B =/= (/) ) $= f0_ssn0 f1_ssn0 p_sseq0 f0_ssn0 f1_ssn0 a_wss f1_ssn0 a_c0 a_wceq f0_ssn0 a_c0 a_wceq p_ex f0_ssn0 f1_ssn0 a_wss f1_ssn0 a_c0 f0_ssn0 a_c0 p_necon3d f0_ssn0 f1_ssn0 a_wss f0_ssn0 a_c0 a_wne f1_ssn0 a_c0 a_wne p_imp $.
$}

$(A class builder with a false argument is empty.  (Contributed by NM,
       20-Jan-2012.) $)

${
	$v ph x  $.
	f0_abf $f wff ph $.
	f1_abf $f set x $.
	e0_abf $e |- -. ph $.
	p_abf $p |- { x | ph } = (/) $= e0_abf f0_abf f1_abf a_sup_set_class a_c0 a_wcel p_pm2.21i f0_abf f1_abf a_c0 p_abssi f0_abf f1_abf a_cab p_ss0 f0_abf f1_abf a_cab a_c0 a_wss f0_abf f1_abf a_cab a_c0 a_wceq a_ax-mp $.
$}

$(Deduction rule for equality to the empty set.  (Contributed by NM,
       11-Jul-2014.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x ph  $.
	f0_eq0rdv $f wff ph $.
	f1_eq0rdv $f set x $.
	f2_eq0rdv $f class A $.
	e0_eq0rdv $e |- ( ph -> -. x e. A ) $.
	p_eq0rdv $p |- ( ph -> A = (/) ) $= e0_eq0rdv f0_eq0rdv f1_eq0rdv a_sup_set_class f2_eq0rdv a_wcel f1_eq0rdv a_sup_set_class a_c0 a_wcel p_pm2.21d f0_eq0rdv f1_eq0rdv f2_eq0rdv a_c0 p_ssrdv f2_eq0rdv p_ss0 f0_eq0rdv f2_eq0rdv a_c0 a_wss f2_eq0rdv a_c0 a_wceq p_syl $.
$}

$(Two classes are empty iff their union is empty.  (Contributed by NM,
     11-Aug-2004.) $)

${
	$v A B  $.
	f0_un00 $f class A $.
	f1_un00 $f class B $.
	p_un00 $p |- ( ( A = (/) /\ B = (/) ) <-> ( A u. B ) = (/) ) $= f0_un00 a_c0 f1_un00 a_c0 p_uneq12 a_c0 p_un0 f0_un00 a_c0 a_wceq f1_un00 a_c0 a_wceq a_wa f0_un00 f1_un00 a_cun a_c0 a_c0 a_cun a_c0 p_syl6eq f0_un00 f1_un00 p_ssun1 f0_un00 f1_un00 a_cun a_c0 f0_un00 p_sseq2 f0_un00 f1_un00 a_cun a_c0 a_wceq f0_un00 f0_un00 f1_un00 a_cun a_wss f0_un00 a_c0 a_wss p_mpbii f0_un00 p_ss0b f0_un00 f1_un00 a_cun a_c0 a_wceq f0_un00 a_c0 a_wss f0_un00 a_c0 a_wceq p_sylib f1_un00 f0_un00 p_ssun2 f0_un00 f1_un00 a_cun a_c0 f1_un00 p_sseq2 f0_un00 f1_un00 a_cun a_c0 a_wceq f1_un00 f0_un00 f1_un00 a_cun a_wss f1_un00 a_c0 a_wss p_mpbii f1_un00 p_ss0b f0_un00 f1_un00 a_cun a_c0 a_wceq f1_un00 a_c0 a_wss f1_un00 a_c0 a_wceq p_sylib f0_un00 f1_un00 a_cun a_c0 a_wceq f0_un00 a_c0 a_wceq f1_un00 a_c0 a_wceq p_jca f0_un00 a_c0 a_wceq f1_un00 a_c0 a_wceq a_wa f0_un00 f1_un00 a_cun a_c0 a_wceq p_impbii $.
$}

$(Only the universal class has the universal class as a subclass.
     (Contributed by NM, 17-Sep-2003.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)

${
	$v A  $.
	f0_vss $f class A $.
	p_vss $p |- ( _V C_ A <-> A = _V ) $= f0_vss p_ssv f0_vss a_cvv a_wss a_cvv f0_vss a_wss p_biantrur f0_vss a_cvv p_eqss a_cvv f0_vss a_wss f0_vss a_cvv a_wss a_cvv f0_vss a_wss a_wa f0_vss a_cvv a_wceq p_bitr4i $.
$}

$(The null set is a proper subset of any non-empty set.  (Contributed by NM,
     27-Feb-1996.) $)

${
	$v A  $.
	f0_0pss $f class A $.
	p_0pss $p |- ( (/) C. A <-> A =/= (/) ) $= f0_0pss p_0ss a_c0 f0_0pss a_df-pss a_c0 f0_0pss a_wpss a_c0 f0_0pss a_wss a_c0 f0_0pss a_wne p_mpbiran a_c0 f0_0pss p_necom a_c0 f0_0pss a_wpss a_c0 f0_0pss a_wne f0_0pss a_c0 a_wne p_bitri $.
$}

$(No set is a proper subset of the empty set.  (Contributed by NM,
     17-Jun-1998.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A  $.
	f0_npss0 $f class A $.
	p_npss0 $p |- -. A C. (/) $= f0_npss0 p_0ss a_c0 f0_npss0 a_wss f0_npss0 a_c0 a_wss p_a1i f0_npss0 a_c0 a_wss a_c0 f0_npss0 a_wss p_iman f0_npss0 a_c0 a_wss a_c0 f0_npss0 a_wss a_wi f0_npss0 a_c0 a_wss a_c0 f0_npss0 a_wss a_wn a_wa a_wn p_mpbi f0_npss0 a_c0 p_dfpss3 f0_npss0 a_c0 a_wpss f0_npss0 a_c0 a_wss a_c0 f0_npss0 a_wss a_wn a_wa p_mtbir $.
$}

$(Any non-universal class is a proper subclass of the universal class.
     (Contributed by NM, 17-May-1998.) $)

${
	$v A  $.
	f0_pssv $f class A $.
	p_pssv $p |- ( A C. _V <-> -. A = _V ) $= f0_pssv p_ssv f0_pssv a_cvv p_dfpss2 f0_pssv a_cvv a_wpss f0_pssv a_cvv a_wss f0_pssv a_cvv a_wceq a_wn p_mpbiran $.
$}

$(Two ways of saying that two classes are disjoint (have no members in
       common).  (Contributed by NM, 17-Feb-2004.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_disj $f set x $.
	f1_disj $f class A $.
	f2_disj $f class B $.
	p_disj $p |- ( ( A i^i B ) = (/) <-> A. x e. A -. x e. B ) $= f0_disj f1_disj f2_disj a_df-in f1_disj f2_disj a_cin f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa f0_disj a_cab a_c0 p_eqeq1i f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa f0_disj a_c0 p_abeq1 f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel p_imnan f0_disj a_sup_set_class p_noel f0_disj a_sup_set_class a_c0 a_wcel f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa p_nbn f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wn a_wi f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa a_wn f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa f0_disj a_sup_set_class a_c0 a_wcel a_wb p_bitr2i f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa f0_disj a_sup_set_class a_c0 a_wcel a_wb f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wn a_wi f0_disj p_albii f1_disj f2_disj a_cin a_c0 a_wceq f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa f0_disj a_cab a_c0 a_wceq f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wa f0_disj a_sup_set_class a_c0 a_wcel a_wb f0_disj a_wal f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wn a_wi f0_disj a_wal p_3bitri f0_disj a_sup_set_class f2_disj a_wcel a_wn f0_disj f1_disj a_df-ral f1_disj f2_disj a_cin a_c0 a_wceq f0_disj a_sup_set_class f1_disj a_wcel f0_disj a_sup_set_class f2_disj a_wcel a_wn a_wi f0_disj a_wal f0_disj a_sup_set_class f2_disj a_wcel a_wn f0_disj f1_disj a_wral p_bitr4i $.
$}

$(Two ways of saying that two classes are disjoint.  (Contributed by Jeff
       Madsen, 19-Jun-2011.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_disjr $f set x $.
	f1_disjr $f class A $.
	f2_disjr $f class B $.
	p_disjr $p |- ( ( A i^i B ) = (/) <-> A. x e. B -. x e. A ) $= f1_disjr f2_disjr p_incom f1_disjr f2_disjr a_cin f2_disjr f1_disjr a_cin a_c0 p_eqeq1i f0_disjr f2_disjr f1_disjr p_disj f1_disjr f2_disjr a_cin a_c0 a_wceq f2_disjr f1_disjr a_cin a_c0 a_wceq f0_disjr a_sup_set_class f1_disjr a_wcel a_wn f0_disjr f2_disjr a_wral p_bitri $.
$}

$(Two ways of saying that two classes are disjoint (have no members in
       common).  (Contributed by NM, 19-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_disj1 $f set x $.
	f1_disj1 $f class A $.
	f2_disj1 $f class B $.
	p_disj1 $p |- ( ( A i^i B ) = (/) <-> A. x ( x e. A -> -. x e. B ) ) $= f0_disj1 f1_disj1 f2_disj1 p_disj f0_disj1 a_sup_set_class f2_disj1 a_wcel a_wn f0_disj1 f1_disj1 a_df-ral f1_disj1 f2_disj1 a_cin a_c0 a_wceq f0_disj1 a_sup_set_class f2_disj1 a_wcel a_wn f0_disj1 f1_disj1 a_wral f0_disj1 a_sup_set_class f1_disj1 a_wcel f0_disj1 a_sup_set_class f2_disj1 a_wcel a_wn a_wi f0_disj1 a_wal p_bitri $.
$}

$(Two ways of saying that two classes are disjoint, using the complement
       of ` B ` relative to a universe ` C ` .  (Contributed by NM,
       15-Feb-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_reldisj $f class A $.
	f1_reldisj $f class B $.
	f2_reldisj $f class C $.
	i0_reldisj $f set x $.
	p_reldisj $p |- ( A C_ C -> ( ( A i^i B ) = (/) <-> A C_ ( C \ B ) ) ) $= i0_reldisj f0_reldisj f2_reldisj p_dfss2 i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn p_pm5.44 i0_reldisj a_sup_set_class f2_reldisj f1_reldisj p_eldif i0_reldisj a_sup_set_class f2_reldisj f1_reldisj a_cdif a_wcel i0_reldisj a_sup_set_class f2_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wa i0_reldisj a_sup_set_class f0_reldisj a_wcel p_imbi2i i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj a_wcel a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wa a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj f1_reldisj a_cdif a_wcel a_wi p_syl6bbr i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj a_wcel a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj f1_reldisj a_cdif a_wcel a_wi a_wb i0_reldisj p_sps f0_reldisj f2_reldisj a_wss i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj a_wcel a_wi i0_reldisj a_wal i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj f1_reldisj a_cdif a_wcel a_wi a_wb p_sylbi f0_reldisj f2_reldisj a_wss i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wi i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj f1_reldisj a_cdif a_wcel a_wi i0_reldisj p_albidv i0_reldisj f0_reldisj f1_reldisj p_disj1 i0_reldisj f0_reldisj f2_reldisj f1_reldisj a_cdif p_dfss2 f0_reldisj f2_reldisj a_wss i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f1_reldisj a_wcel a_wn a_wi i0_reldisj a_wal i0_reldisj a_sup_set_class f0_reldisj a_wcel i0_reldisj a_sup_set_class f2_reldisj f1_reldisj a_cdif a_wcel a_wi i0_reldisj a_wal f0_reldisj f1_reldisj a_cin a_c0 a_wceq f0_reldisj f2_reldisj f1_reldisj a_cdif a_wss p_3bitr4g $.
$}

$(Two ways of saying that two classes are disjoint.  (Contributed by NM,
       19-May-1998.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_disj3 $f class A $.
	f1_disj3 $f class B $.
	i0_disj3 $f set x $.
	p_disj3 $p |- ( ( A i^i B ) = (/) <-> A = ( A \ B ) ) $= i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f1_disj3 a_wcel a_wn p_pm4.71 i0_disj3 a_sup_set_class f0_disj3 f1_disj3 p_eldif i0_disj3 a_sup_set_class f0_disj3 f1_disj3 a_cdif a_wcel i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f1_disj3 a_wcel a_wn a_wa i0_disj3 a_sup_set_class f0_disj3 a_wcel p_bibi2i i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f1_disj3 a_wcel a_wn a_wi i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f1_disj3 a_wcel a_wn a_wa a_wb i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f0_disj3 f1_disj3 a_cdif a_wcel a_wb p_bitr4i i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f1_disj3 a_wcel a_wn a_wi i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f0_disj3 f1_disj3 a_cdif a_wcel a_wb i0_disj3 p_albii i0_disj3 f0_disj3 f1_disj3 p_disj1 i0_disj3 f0_disj3 f0_disj3 f1_disj3 a_cdif p_dfcleq i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f1_disj3 a_wcel a_wn a_wi i0_disj3 a_wal i0_disj3 a_sup_set_class f0_disj3 a_wcel i0_disj3 a_sup_set_class f0_disj3 f1_disj3 a_cdif a_wcel a_wb i0_disj3 a_wal f0_disj3 f1_disj3 a_cin a_c0 a_wceq f0_disj3 f0_disj3 f1_disj3 a_cdif a_wceq p_3bitr4i $.
$}

$(Members of disjoint sets are not equal.  (Contributed by NM,
       28-Mar-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C D  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_disjne $f class A $.
	f1_disjne $f class B $.
	f2_disjne $f class C $.
	f3_disjne $f class D $.
	i0_disjne $f set x $.
	p_disjne $p |- ( ( ( A i^i B ) = (/) /\ C e. A /\ D e. B ) -> C =/= D ) $= i0_disjne f0_disjne f1_disjne p_disj i0_disjne a_sup_set_class f2_disjne f1_disjne p_eleq1 i0_disjne a_sup_set_class f2_disjne a_wceq i0_disjne a_sup_set_class f1_disjne a_wcel f2_disjne f1_disjne a_wcel p_notbid i0_disjne a_sup_set_class f1_disjne a_wcel a_wn f2_disjne f1_disjne a_wcel a_wn i0_disjne f2_disjne f0_disjne p_rspccva f3_disjne f1_disjne f2_disjne p_eleq1a f3_disjne f1_disjne a_wcel f2_disjne f1_disjne a_wcel f2_disjne f3_disjne p_necon3bd i0_disjne a_sup_set_class f1_disjne a_wcel a_wn i0_disjne f0_disjne a_wral f2_disjne f0_disjne a_wcel a_wa f2_disjne f1_disjne a_wcel a_wn f3_disjne f1_disjne a_wcel f2_disjne f3_disjne a_wne p_syl5com f0_disjne f1_disjne a_cin a_c0 a_wceq i0_disjne a_sup_set_class f1_disjne a_wcel a_wn i0_disjne f0_disjne a_wral f2_disjne f0_disjne a_wcel f3_disjne f1_disjne a_wcel f2_disjne f3_disjne a_wne a_wi p_sylanb f0_disjne f1_disjne a_cin a_c0 a_wceq f2_disjne f0_disjne a_wcel f3_disjne f1_disjne a_wcel f2_disjne f3_disjne a_wne p_3impia $.
$}

$(A set can't belong to both members of disjoint classes.  (Contributed by
     NM, 28-Feb-2015.) $)

${
	$v A B C  $.
	f0_disjel $f class A $.
	f1_disjel $f class B $.
	f2_disjel $f class C $.
	p_disjel $p |- ( ( ( A i^i B ) = (/) /\ C e. A ) -> -. C e. B ) $= f0_disjel f1_disjel p_disj3 f0_disjel f0_disjel f1_disjel a_cdif f2_disjel p_eleq2 f2_disjel f0_disjel f1_disjel p_eldifn f0_disjel f0_disjel f1_disjel a_cdif a_wceq f2_disjel f0_disjel a_wcel f2_disjel f0_disjel f1_disjel a_cdif a_wcel f2_disjel f1_disjel a_wcel a_wn p_syl6bi f0_disjel f1_disjel a_cin a_c0 a_wceq f0_disjel f0_disjel f1_disjel a_cdif a_wceq f2_disjel f0_disjel a_wcel f2_disjel f1_disjel a_wcel a_wn a_wi p_sylbi f0_disjel f1_disjel a_cin a_c0 a_wceq f2_disjel f0_disjel a_wcel f2_disjel f1_disjel a_wcel a_wn p_imp $.
$}

$(Two ways of saying that two classes are disjoint.  (Contributed by NM,
     17-May-1998.) $)

${
	$v A B  $.
	f0_disj2 $f class A $.
	f1_disj2 $f class B $.
	p_disj2 $p |- ( ( A i^i B ) = (/) <-> A C_ ( _V \ B ) ) $= f0_disj2 p_ssv f0_disj2 f1_disj2 a_cvv p_reldisj f0_disj2 a_cvv a_wss f0_disj2 f1_disj2 a_cin a_c0 a_wceq f0_disj2 a_cvv f1_disj2 a_cdif a_wss a_wb a_ax-mp $.
$}

$(Two ways of saying that two classes are disjoint.  (Contributed by NM,
     21-Mar-2004.) $)

${
	$v A B  $.
	f0_disj4 $f class A $.
	f1_disj4 $f class B $.
	p_disj4 $p |- ( ( A i^i B ) = (/) <-> -. ( A \ B ) C. A ) $= f0_disj4 f1_disj4 p_disj3 f0_disj4 f0_disj4 f1_disj4 a_cdif p_eqcom f0_disj4 f1_disj4 p_difss f0_disj4 f1_disj4 a_cdif f0_disj4 p_dfpss2 f0_disj4 f1_disj4 a_cdif f0_disj4 a_wpss f0_disj4 f1_disj4 a_cdif f0_disj4 a_wss f0_disj4 f1_disj4 a_cdif f0_disj4 a_wceq a_wn p_mpbiran f0_disj4 f1_disj4 a_cdif f0_disj4 a_wpss f0_disj4 f1_disj4 a_cdif f0_disj4 a_wceq p_con2bii f0_disj4 f1_disj4 a_cin a_c0 a_wceq f0_disj4 f0_disj4 f1_disj4 a_cdif a_wceq f0_disj4 f1_disj4 a_cdif f0_disj4 a_wceq f0_disj4 f1_disj4 a_cdif f0_disj4 a_wpss a_wn p_3bitri $.
$}

$(Intersection with a subclass of a disjoint class.  (Contributed by FL,
     24-Jan-2007.) $)

${
	$v A B C  $.
	f0_ssdisj $f class A $.
	f1_ssdisj $f class B $.
	f2_ssdisj $f class C $.
	p_ssdisj $p |- ( ( A C_ B /\ ( B i^i C ) = (/) ) -> ( A i^i C ) = (/) ) $= f1_ssdisj f2_ssdisj a_cin p_ss0b f0_ssdisj f1_ssdisj f2_ssdisj p_ssrin f0_ssdisj f2_ssdisj a_cin f1_ssdisj f2_ssdisj a_cin a_c0 p_sstr2 f0_ssdisj f1_ssdisj a_wss f0_ssdisj f2_ssdisj a_cin f1_ssdisj f2_ssdisj a_cin a_wss f1_ssdisj f2_ssdisj a_cin a_c0 a_wss f0_ssdisj f2_ssdisj a_cin a_c0 a_wss a_wi p_syl f1_ssdisj f2_ssdisj a_cin a_c0 a_wceq f1_ssdisj f2_ssdisj a_cin a_c0 a_wss f0_ssdisj f1_ssdisj a_wss f0_ssdisj f2_ssdisj a_cin a_c0 a_wss p_syl5bir f0_ssdisj f1_ssdisj a_wss f1_ssdisj f2_ssdisj a_cin a_c0 a_wceq f0_ssdisj f2_ssdisj a_cin a_c0 a_wss p_imp f0_ssdisj f2_ssdisj a_cin p_ss0 f0_ssdisj f1_ssdisj a_wss f1_ssdisj f2_ssdisj a_cin a_c0 a_wceq a_wa f0_ssdisj f2_ssdisj a_cin a_c0 a_wss f0_ssdisj f2_ssdisj a_cin a_c0 a_wceq p_syl $.
$}

$(A class is a proper subset of its union with a disjoint nonempty class.
     (Contributed by NM, 15-Sep-2004.) $)

${
	$v A B  $.
	f0_disjpss $f class A $.
	f1_disjpss $f class B $.
	p_disjpss $p |- ( ( ( A i^i B ) = (/) /\ B =/= (/) ) -> A C. ( A u. B ) ) $= f1_disjpss p_ssid f1_disjpss f1_disjpss a_wss f1_disjpss f0_disjpss a_wss p_biantru f1_disjpss f0_disjpss f1_disjpss p_ssin f1_disjpss f0_disjpss a_wss f1_disjpss f0_disjpss a_wss f1_disjpss f1_disjpss a_wss a_wa f1_disjpss f0_disjpss f1_disjpss a_cin a_wss p_bitri f0_disjpss f1_disjpss a_cin a_c0 f1_disjpss p_sseq2 f1_disjpss f0_disjpss a_wss f1_disjpss f0_disjpss f1_disjpss a_cin a_wss f0_disjpss f1_disjpss a_cin a_c0 a_wceq f1_disjpss a_c0 a_wss p_syl5bb f1_disjpss p_ss0 f0_disjpss f1_disjpss a_cin a_c0 a_wceq f1_disjpss f0_disjpss a_wss f1_disjpss a_c0 a_wss f1_disjpss a_c0 a_wceq p_syl6bi f0_disjpss f1_disjpss a_cin a_c0 a_wceq f1_disjpss f0_disjpss a_wss f1_disjpss a_c0 p_necon3ad f0_disjpss f1_disjpss a_cin a_c0 a_wceq f1_disjpss a_c0 a_wne f1_disjpss f0_disjpss a_wss a_wn p_imp f1_disjpss f0_disjpss p_nsspssun f1_disjpss f0_disjpss p_uncom f1_disjpss f0_disjpss a_cun f0_disjpss f1_disjpss a_cun f0_disjpss p_psseq2i f1_disjpss f0_disjpss a_wss a_wn f0_disjpss f1_disjpss f0_disjpss a_cun a_wpss f0_disjpss f0_disjpss f1_disjpss a_cun a_wpss p_bitri f0_disjpss f1_disjpss a_cin a_c0 a_wceq f1_disjpss a_c0 a_wne a_wa f1_disjpss f0_disjpss a_wss a_wn f0_disjpss f0_disjpss f1_disjpss a_cun a_wpss p_sylib $.
$}

$(The union of disjoint classes is disjoint.  (Contributed by NM,
     26-Sep-2004.) $)

${
	$v A B C  $.
	f0_undisj1 $f class A $.
	f1_undisj1 $f class B $.
	f2_undisj1 $f class C $.
	p_undisj1 $p |- ( ( ( A i^i C ) = (/) /\ ( B i^i C ) = (/) ) <-> ( ( A u. B ) i^i C ) = (/) ) $= f0_undisj1 f2_undisj1 a_cin f1_undisj1 f2_undisj1 a_cin p_un00 f0_undisj1 f1_undisj1 f2_undisj1 p_indir f0_undisj1 f1_undisj1 a_cun f2_undisj1 a_cin f0_undisj1 f2_undisj1 a_cin f1_undisj1 f2_undisj1 a_cin a_cun a_c0 p_eqeq1i f0_undisj1 f2_undisj1 a_cin a_c0 a_wceq f1_undisj1 f2_undisj1 a_cin a_c0 a_wceq a_wa f0_undisj1 f2_undisj1 a_cin f1_undisj1 f2_undisj1 a_cin a_cun a_c0 a_wceq f0_undisj1 f1_undisj1 a_cun f2_undisj1 a_cin a_c0 a_wceq p_bitr4i $.
$}

$(The union of disjoint classes is disjoint.  (Contributed by NM,
     13-Sep-2004.) $)

${
	$v A B C  $.
	f0_undisj2 $f class A $.
	f1_undisj2 $f class B $.
	f2_undisj2 $f class C $.
	p_undisj2 $p |- ( ( ( A i^i B ) = (/) /\ ( A i^i C ) = (/) ) <-> ( A i^i ( B u. C ) ) = (/) ) $= f0_undisj2 f1_undisj2 a_cin f0_undisj2 f2_undisj2 a_cin p_un00 f0_undisj2 f1_undisj2 f2_undisj2 p_indi f0_undisj2 f1_undisj2 f2_undisj2 a_cun a_cin f0_undisj2 f1_undisj2 a_cin f0_undisj2 f2_undisj2 a_cin a_cun a_c0 p_eqeq1i f0_undisj2 f1_undisj2 a_cin a_c0 a_wceq f0_undisj2 f2_undisj2 a_cin a_c0 a_wceq a_wa f0_undisj2 f1_undisj2 a_cin f0_undisj2 f2_undisj2 a_cin a_cun a_c0 a_wceq f0_undisj2 f1_undisj2 f2_undisj2 a_cun a_cin a_c0 a_wceq p_bitr4i $.
$}

$(Subclass expressed in terms of intersection with difference from the
     universal class.  (Contributed by NM, 17-Sep-2003.) $)

${
	$v A B  $.
	f0_ssindif0 $f class A $.
	f1_ssindif0 $f class B $.
	p_ssindif0 $p |- ( A C_ B <-> ( A i^i ( _V \ B ) ) = (/) ) $= f0_ssindif0 a_cvv f1_ssindif0 a_cdif p_disj2 f1_ssindif0 p_ddif a_cvv a_cvv f1_ssindif0 a_cdif a_cdif f1_ssindif0 f0_ssindif0 p_sseq2i f0_ssindif0 a_cvv f1_ssindif0 a_cdif a_cin a_c0 a_wceq f0_ssindif0 a_cvv a_cvv f1_ssindif0 a_cdif a_cdif a_wss f0_ssindif0 f1_ssindif0 a_wss p_bitr2i $.
$}

$(The intersection of classes with a common member is nonempty.
     (Contributed by NM, 7-Apr-1994.) $)

${
	$v A B C  $.
	f0_inelcm $f class A $.
	f1_inelcm $f class B $.
	f2_inelcm $f class C $.
	p_inelcm $p |- ( ( A e. B /\ A e. C ) -> ( B i^i C ) =/= (/) ) $= f0_inelcm f1_inelcm f2_inelcm p_elin f1_inelcm f2_inelcm a_cin f0_inelcm p_ne0i f0_inelcm f1_inelcm a_wcel f0_inelcm f2_inelcm a_wcel a_wa f0_inelcm f1_inelcm f2_inelcm a_cin a_wcel f1_inelcm f2_inelcm a_cin a_c0 a_wne p_sylbir $.
$}

$(A minimum element of a class has no elements in common with the class.
     (Contributed by NM, 22-Jun-1994.) $)

${
	$v A B C  $.
	f0_minel $f class A $.
	f1_minel $f class B $.
	f2_minel $f class C $.
	p_minel $p |- ( ( A e. B /\ ( C i^i B ) = (/) ) -> -. A e. C ) $= f0_minel f2_minel f1_minel p_inelcm f0_minel f2_minel a_wcel f0_minel f1_minel a_wcel a_wa f2_minel f1_minel a_cin a_c0 p_necon2bi f0_minel f2_minel a_wcel f0_minel f1_minel a_wcel p_imnan f2_minel f1_minel a_cin a_c0 a_wceq f0_minel f2_minel a_wcel f0_minel f1_minel a_wcel a_wa a_wn f0_minel f2_minel a_wcel f0_minel f1_minel a_wcel a_wn a_wi p_sylibr f2_minel f1_minel a_cin a_c0 a_wceq f0_minel f2_minel a_wcel f0_minel f1_minel a_wcel p_con2d f2_minel f1_minel a_cin a_c0 a_wceq f0_minel f1_minel a_wcel f0_minel f2_minel a_wcel a_wn p_impcom $.
$}

$(Distribute union over difference.  (Contributed by NM, 17-May-1998.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_undif4 $f class A $.
	f1_undif4 $f class B $.
	f2_undif4 $f class C $.
	i0_undif4 $f set x $.
	p_undif4 $p |- ( ( A i^i C ) = (/) -> ( A u. ( B \ C ) ) = ( ( A u. B ) \ C ) ) $= i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn p_pm2.621 i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn i0_undif4 a_sup_set_class f0_undif4 a_wcel p_olc i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wi i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wo i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn p_impbid1 i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wi i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wo i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel a_wo p_anbi2d i0_undif4 a_sup_set_class f1_undif4 f2_undif4 p_eldif i0_undif4 a_sup_set_class f1_undif4 f2_undif4 a_cdif a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wa i0_undif4 a_sup_set_class f0_undif4 a_wcel p_orbi2i i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn p_ordi i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 f2_undif4 a_cdif a_wcel a_wo i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wa a_wo i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel a_wo i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wo a_wa p_bitri i0_undif4 a_sup_set_class f0_undif4 f1_undif4 p_elun i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun a_wcel i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel a_wo i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn p_anbi1i i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wi i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel a_wo i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wo a_wa i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 a_wcel a_wo i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wa i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 f2_undif4 a_cdif a_wcel a_wo i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wa p_3bitr4g i0_undif4 a_sup_set_class f0_undif4 f1_undif4 f2_undif4 a_cdif p_elun i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun f2_undif4 p_eldif i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wi i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f1_undif4 f2_undif4 a_cdif a_wcel a_wo i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wa i0_undif4 a_sup_set_class f0_undif4 f1_undif4 f2_undif4 a_cdif a_cun a_wcel i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun f2_undif4 a_cdif a_wcel p_3bitr4g i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wi i0_undif4 a_sup_set_class f0_undif4 f1_undif4 f2_undif4 a_cdif a_cun a_wcel i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun f2_undif4 a_cdif a_wcel a_wb i0_undif4 p_alimi i0_undif4 f0_undif4 f2_undif4 p_disj1 i0_undif4 f0_undif4 f1_undif4 f2_undif4 a_cdif a_cun f0_undif4 f1_undif4 a_cun f2_undif4 a_cdif p_dfcleq i0_undif4 a_sup_set_class f0_undif4 a_wcel i0_undif4 a_sup_set_class f2_undif4 a_wcel a_wn a_wi i0_undif4 a_wal i0_undif4 a_sup_set_class f0_undif4 f1_undif4 f2_undif4 a_cdif a_cun a_wcel i0_undif4 a_sup_set_class f0_undif4 f1_undif4 a_cun f2_undif4 a_cdif a_wcel a_wb i0_undif4 a_wal f0_undif4 f2_undif4 a_cin a_c0 a_wceq f0_undif4 f1_undif4 f2_undif4 a_cdif a_cun f0_undif4 f1_undif4 a_cun f2_undif4 a_cdif a_wceq p_3imtr4i $.
$}

$(Subset relation for disjoint classes.  (Contributed by NM,
       25-Oct-2005.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_disjssun $f class A $.
	f1_disjssun $f class B $.
	f2_disjssun $f class C $.
	p_disjssun $p |- ( ( A i^i B ) = (/) -> ( A C_ ( B u. C ) <-> A C_ C ) ) $= f0_disjssun f1_disjssun f2_disjssun p_indi f0_disjssun f1_disjssun f2_disjssun a_cun a_cin f0_disjssun f1_disjssun a_cin f0_disjssun f2_disjssun a_cin p_equncomi f0_disjssun f1_disjssun a_cin a_c0 f0_disjssun f2_disjssun a_cin p_uneq2 f0_disjssun f2_disjssun a_cin p_un0 f0_disjssun f1_disjssun a_cin a_c0 a_wceq f0_disjssun f2_disjssun a_cin f0_disjssun f1_disjssun a_cin a_cun f0_disjssun f2_disjssun a_cin a_c0 a_cun f0_disjssun f2_disjssun a_cin p_syl6eq f0_disjssun f1_disjssun a_cin a_c0 a_wceq f0_disjssun f1_disjssun f2_disjssun a_cun a_cin f0_disjssun f2_disjssun a_cin f0_disjssun f1_disjssun a_cin a_cun f0_disjssun f2_disjssun a_cin p_syl5eq f0_disjssun f1_disjssun a_cin a_c0 a_wceq f0_disjssun f1_disjssun f2_disjssun a_cun a_cin f0_disjssun f2_disjssun a_cin f0_disjssun p_eqeq1d f0_disjssun f1_disjssun f2_disjssun a_cun a_df-ss f0_disjssun f2_disjssun a_df-ss f0_disjssun f1_disjssun a_cin a_c0 a_wceq f0_disjssun f1_disjssun f2_disjssun a_cun a_cin f0_disjssun a_wceq f0_disjssun f2_disjssun a_cin f0_disjssun a_wceq f0_disjssun f1_disjssun f2_disjssun a_cun a_wss f0_disjssun f2_disjssun a_wss p_3bitr4g $.
$}

$(Subclass expressed in terms of difference.  Exercise 7 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 29-Apr-1994.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssdif0 $f class A $.
	f1_ssdif0 $f class B $.
	i0_ssdif0 $f set x $.
	p_ssdif0 $p |- ( A C_ B <-> ( A \ B ) = (/) ) $= i0_ssdif0 a_sup_set_class f0_ssdif0 a_wcel i0_ssdif0 a_sup_set_class f1_ssdif0 a_wcel p_iman i0_ssdif0 a_sup_set_class f0_ssdif0 f1_ssdif0 p_eldif i0_ssdif0 a_sup_set_class f0_ssdif0 a_wcel i0_ssdif0 a_sup_set_class f1_ssdif0 a_wcel a_wi i0_ssdif0 a_sup_set_class f0_ssdif0 a_wcel i0_ssdif0 a_sup_set_class f1_ssdif0 a_wcel a_wn a_wa i0_ssdif0 a_sup_set_class f0_ssdif0 f1_ssdif0 a_cdif a_wcel p_xchbinxr i0_ssdif0 a_sup_set_class f0_ssdif0 a_wcel i0_ssdif0 a_sup_set_class f1_ssdif0 a_wcel a_wi i0_ssdif0 a_sup_set_class f0_ssdif0 f1_ssdif0 a_cdif a_wcel a_wn i0_ssdif0 p_albii i0_ssdif0 f0_ssdif0 f1_ssdif0 p_dfss2 i0_ssdif0 f0_ssdif0 f1_ssdif0 a_cdif p_eq0 i0_ssdif0 a_sup_set_class f0_ssdif0 a_wcel i0_ssdif0 a_sup_set_class f1_ssdif0 a_wcel a_wi i0_ssdif0 a_wal i0_ssdif0 a_sup_set_class f0_ssdif0 f1_ssdif0 a_cdif a_wcel a_wn i0_ssdif0 a_wal f0_ssdif0 f1_ssdif0 a_wss f0_ssdif0 f1_ssdif0 a_cdif a_c0 a_wceq p_3bitr4i $.
$}

$(Universal class equality in terms of empty difference.  (Contributed by
     NM, 17-Sep-2003.) $)

${
	$v A  $.
	f0_vdif0 $f class A $.
	p_vdif0 $p |- ( A = _V <-> ( _V \ A ) = (/) ) $= f0_vdif0 p_vss a_cvv f0_vdif0 p_ssdif0 f0_vdif0 a_cvv a_wceq a_cvv f0_vdif0 a_wss a_cvv f0_vdif0 a_cdif a_c0 a_wceq p_bitr3i $.
$}

$(A proper subclass has a nonempty difference.  (Contributed by NM,
     3-May-1994.) $)

${
	$v A B  $.
	f0_pssdifn0 $f class A $.
	f1_pssdifn0 $f class B $.
	p_pssdifn0 $p |- ( ( A C_ B /\ A =/= B ) -> ( B \ A ) =/= (/) ) $= f1_pssdifn0 f0_pssdifn0 p_ssdif0 f0_pssdifn0 f1_pssdifn0 p_eqss f0_pssdifn0 f1_pssdifn0 a_wceq f0_pssdifn0 f1_pssdifn0 a_wss f1_pssdifn0 f0_pssdifn0 a_wss p_simplbi2 f1_pssdifn0 f0_pssdifn0 a_cdif a_c0 a_wceq f1_pssdifn0 f0_pssdifn0 a_wss f0_pssdifn0 f1_pssdifn0 a_wss f0_pssdifn0 f1_pssdifn0 a_wceq p_syl5bir f0_pssdifn0 f1_pssdifn0 a_wss f1_pssdifn0 f0_pssdifn0 a_cdif a_c0 f0_pssdifn0 f1_pssdifn0 p_necon3d f0_pssdifn0 f1_pssdifn0 a_wss f0_pssdifn0 f1_pssdifn0 a_wne f1_pssdifn0 f0_pssdifn0 a_cdif a_c0 a_wne p_imp $.
$}

$(A proper subclass has a nonempty difference.  (Contributed by Mario
     Carneiro, 27-Apr-2016.) $)

${
	$v A B  $.
	f0_pssdif $f class A $.
	f1_pssdif $f class B $.
	p_pssdif $p |- ( A C. B -> ( B \ A ) =/= (/) ) $= f0_pssdif f1_pssdif a_df-pss f0_pssdif f1_pssdif p_pssdifn0 f0_pssdif f1_pssdif a_wpss f0_pssdif f1_pssdif a_wss f0_pssdif f1_pssdif a_wne a_wa f1_pssdif f0_pssdif a_cdif a_c0 a_wne p_sylbi $.
$}

$(A subclass missing a member is a proper subclass.  (Contributed by NM,
     12-Jan-2002.) $)

${
	$v A B C  $.
	f0_ssnelpss $f class A $.
	f1_ssnelpss $f class B $.
	f2_ssnelpss $f class C $.
	p_ssnelpss $p |- ( A C_ B -> ( ( C e. B /\ -. C e. A ) -> A C. B ) ) $= f2_ssnelpss f1_ssnelpss f0_ssnelpss p_nelneq2 f1_ssnelpss f0_ssnelpss p_eqcom f2_ssnelpss f1_ssnelpss a_wcel f2_ssnelpss f0_ssnelpss a_wcel a_wn a_wa f1_ssnelpss f0_ssnelpss a_wceq f0_ssnelpss f1_ssnelpss a_wceq p_sylnib f0_ssnelpss f1_ssnelpss p_dfpss2 f0_ssnelpss f1_ssnelpss a_wpss f0_ssnelpss f1_ssnelpss a_wss f0_ssnelpss f1_ssnelpss a_wceq a_wn p_baibr f2_ssnelpss f1_ssnelpss a_wcel f2_ssnelpss f0_ssnelpss a_wcel a_wn a_wa f0_ssnelpss f1_ssnelpss a_wceq a_wn f0_ssnelpss f1_ssnelpss a_wss f0_ssnelpss f1_ssnelpss a_wpss p_syl5ib $.
$}

$(Subclass inclusion with one element of the superclass missing is proper
       subclass inclusion.  Deduction form of ~ ssnelpss .  (Contributed by
       David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_ssnelpssd $f wff ph $.
	f1_ssnelpssd $f class A $.
	f2_ssnelpssd $f class B $.
	f3_ssnelpssd $f class C $.
	e0_ssnelpssd $e |- ( ph -> A C_ B ) $.
	e1_ssnelpssd $e |- ( ph -> C e. B ) $.
	e2_ssnelpssd $e |- ( ph -> -. C e. A ) $.
	p_ssnelpssd $p |- ( ph -> A C. B ) $= e1_ssnelpssd e2_ssnelpssd e0_ssnelpssd f1_ssnelpssd f2_ssnelpssd f3_ssnelpssd p_ssnelpss f0_ssnelpssd f1_ssnelpssd f2_ssnelpssd a_wss f3_ssnelpssd f2_ssnelpssd a_wcel f3_ssnelpssd f1_ssnelpssd a_wcel a_wn a_wa f1_ssnelpssd f2_ssnelpssd a_wpss a_wi p_syl f0_ssnelpssd f3_ssnelpssd f2_ssnelpssd a_wcel f3_ssnelpssd f1_ssnelpssd a_wcel a_wn f1_ssnelpssd f2_ssnelpssd a_wpss p_mp2and $.
$}

$(A proper subclass has a member in one argument that's not in both.
       (Contributed by NM, 29-Feb-1996.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_pssnel $f set x $.
	f1_pssnel $f class A $.
	f2_pssnel $f class B $.
	p_pssnel $p |- ( A C. B -> E. x ( x e. B /\ -. x e. A ) ) $= f1_pssnel f2_pssnel p_pssdif f0_pssnel f2_pssnel f1_pssnel a_cdif p_n0 f1_pssnel f2_pssnel a_wpss f2_pssnel f1_pssnel a_cdif a_c0 a_wne f0_pssnel a_sup_set_class f2_pssnel f1_pssnel a_cdif a_wcel f0_pssnel a_wex p_sylib f0_pssnel a_sup_set_class f2_pssnel f1_pssnel p_eldif f0_pssnel a_sup_set_class f2_pssnel f1_pssnel a_cdif a_wcel f0_pssnel a_sup_set_class f2_pssnel a_wcel f0_pssnel a_sup_set_class f1_pssnel a_wcel a_wn a_wa f0_pssnel p_exbii f1_pssnel f2_pssnel a_wpss f0_pssnel a_sup_set_class f2_pssnel f1_pssnel a_cdif a_wcel f0_pssnel a_wex f0_pssnel a_sup_set_class f2_pssnel a_wcel f0_pssnel a_sup_set_class f1_pssnel a_wcel a_wn a_wa f0_pssnel a_wex p_sylib $.
$}

$(Difference, intersection, and subclass relationship.  (Contributed by
       NM, 30-Apr-1994.)  (Proof shortened by Wolf Lammen, 30-Sep-2014.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_difin0ss $f class A $.
	f1_difin0ss $f class B $.
	f2_difin0ss $f class C $.
	i0_difin0ss $f set x $.
	p_difin0ss $p |- ( ( ( A \ B ) i^i C ) = (/) -> ( C C_ A -> C C_ B ) ) $= i0_difin0ss f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin p_eq0 i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi p_iman i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss p_elin i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss p_eldif i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wn a_wa i0_difin0ss a_sup_set_class f2_difin0ss a_wcel p_anbi1i i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif a_wcel i0_difin0ss a_sup_set_class f2_difin0ss a_wcel a_wa i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wn a_wa i0_difin0ss a_sup_set_class f2_difin0ss a_wcel a_wa p_bitri i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wn a_wa p_ancom i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel p_annim i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wn a_wa i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi a_wn i0_difin0ss a_sup_set_class f2_difin0ss a_wcel p_anbi2i i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wn a_wa i0_difin0ss a_sup_set_class f2_difin0ss a_wcel a_wa i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wn a_wa a_wa i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi a_wn a_wa p_3bitr2i i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi a_wi i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi a_wn a_wa i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel p_xchbinxr i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_ax-2 i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel a_wn i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi a_wi i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel a_wi i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi a_wi p_sylbir i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel a_wn i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel a_wi i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi i0_difin0ss p_al2imi i0_difin0ss f2_difin0ss f0_difin0ss p_dfss2 i0_difin0ss f2_difin0ss f1_difin0ss p_dfss2 i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel a_wn i0_difin0ss a_wal i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f0_difin0ss a_wcel a_wi i0_difin0ss a_wal i0_difin0ss a_sup_set_class f2_difin0ss a_wcel i0_difin0ss a_sup_set_class f1_difin0ss a_wcel a_wi i0_difin0ss a_wal f2_difin0ss f0_difin0ss a_wss f2_difin0ss f1_difin0ss a_wss p_3imtr4g f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_c0 a_wceq i0_difin0ss a_sup_set_class f0_difin0ss f1_difin0ss a_cdif f2_difin0ss a_cin a_wcel a_wn i0_difin0ss a_wal f2_difin0ss f0_difin0ss a_wss f2_difin0ss f1_difin0ss a_wss a_wi p_sylbi $.
$}

$(Intersection, subclass, and difference relationship.  (Contributed by
       NM, 27-Oct-1996.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.)
       (Proof shortened by Wolf Lammen, 30-Sep-2014.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_inssdif0 $f class A $.
	f1_inssdif0 $f class B $.
	f2_inssdif0 $f class C $.
	i0_inssdif0 $f set x $.
	p_inssdif0 $p |- ( ( A i^i B ) C_ C <-> ( A i^i ( B \ C ) ) = (/) ) $= i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 p_elin i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 a_cin a_wcel i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel a_wa i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel p_imbi1i i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel a_wa i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel p_iman i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 a_cin a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wi i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel a_wa i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wi i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel a_wa i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wn a_wa a_wn p_bitri i0_inssdif0 a_sup_set_class f1_inssdif0 f2_inssdif0 p_eldif i0_inssdif0 a_sup_set_class f1_inssdif0 f2_inssdif0 a_cdif a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wn a_wa i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel p_anbi2i i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif p_elin i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wn p_anass i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 f2_inssdif0 a_cdif a_wcel a_wa i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wn a_wa a_wa i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif a_cin a_wcel i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel a_wa i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wn a_wa p_3bitr4ri i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 a_cin a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wi i0_inssdif0 a_sup_set_class f0_inssdif0 a_wcel i0_inssdif0 a_sup_set_class f1_inssdif0 a_wcel a_wa i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wn a_wa i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif a_cin a_wcel p_xchbinx i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 a_cin a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wi i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif a_cin a_wcel a_wn i0_inssdif0 p_albii i0_inssdif0 f0_inssdif0 f1_inssdif0 a_cin f2_inssdif0 p_dfss2 i0_inssdif0 f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif a_cin p_eq0 i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 a_cin a_wcel i0_inssdif0 a_sup_set_class f2_inssdif0 a_wcel a_wi i0_inssdif0 a_wal i0_inssdif0 a_sup_set_class f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif a_cin a_wcel a_wn i0_inssdif0 a_wal f0_inssdif0 f1_inssdif0 a_cin f2_inssdif0 a_wss f0_inssdif0 f1_inssdif0 f2_inssdif0 a_cdif a_cin a_c0 a_wceq p_3bitr4i $.
$}

$(The difference between a class and itself is the empty set.  Proposition
     5.15 of [TakeutiZaring] p. 20.  Also Theorem 32 of [Suppes] p. 28.
     (Contributed by NM, 22-Apr-2004.) $)

${
	$v A  $.
	f0_difid $f class A $.
	p_difid $p |- ( A \ A ) = (/) $= f0_difid p_ssid f0_difid f0_difid p_ssdif0 f0_difid f0_difid a_wss f0_difid f0_difid a_cdif a_c0 a_wceq p_mpbi $.
$}

$(The difference between a class and itself is the empty set.  Proposition
       5.15 of [TakeutiZaring] p. 20.  Also Theorem 32 of [Suppes] p. 28.
       Alternate proof of ~ difid .  (Contributed by David Abernethy,
       17-Jun-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v A  $.
	$d x A  $.
	f0_difidALT $f class A $.
	i0_difidALT $f set x $.
	p_difidALT $p |- ( A \ A ) = (/) $= i0_difidALT f0_difidALT f0_difidALT p_dfdif2 i0_difidALT f0_difidALT p_dfnul3 f0_difidALT f0_difidALT a_cdif i0_difidALT a_sup_set_class f0_difidALT a_wcel a_wn i0_difidALT f0_difidALT a_crab a_c0 p_eqtr4i $.
$}

$(The difference between a class and the empty set.  Part of Exercise 4.4 of
     [Stoll] p. 16.  (Contributed by NM, 17-Aug-2004.) $)

${
	$v A  $.
	f0_dif0 $f class A $.
	p_dif0 $p |- ( A \ (/) ) = A $= f0_dif0 p_difid f0_dif0 f0_dif0 a_cdif a_c0 f0_dif0 p_difeq2i f0_dif0 f0_dif0 p_difdif f0_dif0 f0_dif0 f0_dif0 a_cdif a_cdif f0_dif0 a_c0 a_cdif f0_dif0 p_eqtr3i $.
$}

$(The difference between the empty set and a class.  Part of Exercise 4.4 of
     [Stoll] p. 16.  (Contributed by NM, 17-Aug-2004.) $)

${
	$v A  $.
	f0_0dif $f class A $.
	p_0dif $p |- ( (/) \ A ) = (/) $= a_c0 f0_0dif p_difss a_c0 f0_0dif a_cdif p_ss0 a_c0 f0_0dif a_cdif a_c0 a_wss a_c0 f0_0dif a_cdif a_c0 a_wceq a_ax-mp $.
$}

$(A class and its relative complement are disjoint.  Theorem 38 of [Suppes]
     p. 29.  (Contributed by NM, 24-Mar-1998.) $)

${
	$v A B  $.
	f0_disjdif $f class A $.
	f1_disjdif $f class B $.
	p_disjdif $p |- ( A i^i ( B \ A ) ) = (/) $= f0_disjdif f1_disjdif p_inss1 f0_disjdif f1_disjdif f0_disjdif p_inssdif0 f0_disjdif f1_disjdif a_cin f0_disjdif a_wss f0_disjdif f1_disjdif f0_disjdif a_cdif a_cin a_c0 a_wceq p_mpbi $.
$}

$(The difference of a class from its intersection is empty.  Theorem 37 of
     [Suppes] p. 29.  (Contributed by NM, 17-Aug-2004.)  (Proof shortened by
     Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	f0_difin0 $f class A $.
	f1_difin0 $f class B $.
	p_difin0 $p |- ( ( A i^i B ) \ B ) = (/) $= f0_difin0 f1_difin0 p_inss2 f0_difin0 f1_difin0 a_cin f1_difin0 p_ssdif0 f0_difin0 f1_difin0 a_cin f1_difin0 a_wss f0_difin0 f1_difin0 a_cin f1_difin0 a_cdif a_c0 a_wceq p_mpbi $.
$}

$(The union of a class and its complement is the universe.  Theorem 5.1(5)
     of [Stoll] p. 17.  (Contributed by NM, 17-Aug-2004.) $)

${
	$v A  $.
	f0_undifv $f class A $.
	p_undifv $p |- ( A u. ( _V \ A ) ) = _V $= f0_undifv a_cvv f0_undifv a_cdif p_dfun3 a_cvv f0_undifv a_cdif a_cvv p_disjdif a_cvv f0_undifv a_cdif a_cvv a_cvv f0_undifv a_cdif a_cdif a_cin a_c0 a_cvv p_difeq2i a_cvv p_dif0 f0_undifv a_cvv f0_undifv a_cdif a_cun a_cvv a_cvv f0_undifv a_cdif a_cvv a_cvv f0_undifv a_cdif a_cdif a_cin a_cdif a_cvv a_c0 a_cdif a_cvv p_3eqtri $.
$}

$(Absorption of difference by union.  This decomposes a union into two
     disjoint classes (see ~ disjdif ).  Theorem 35 of [Suppes] p. 29.
     (Contributed by NM, 19-May-1998.) $)

${
	$v A B  $.
	f0_undif1 $f class A $.
	f1_undif1 $f class B $.
	p_undif1 $p |- ( ( A \ B ) u. B ) = ( A u. B ) $= f0_undif1 a_cvv f1_undif1 a_cdif f1_undif1 p_undir f0_undif1 f1_undif1 p_invdif f0_undif1 a_cvv f1_undif1 a_cdif a_cin f0_undif1 f1_undif1 a_cdif f1_undif1 p_uneq1i a_cvv f1_undif1 a_cdif f1_undif1 p_uncom f1_undif1 p_undifv a_cvv f1_undif1 a_cdif f1_undif1 a_cun f1_undif1 a_cvv f1_undif1 a_cdif a_cun a_cvv p_eqtri a_cvv f1_undif1 a_cdif f1_undif1 a_cun a_cvv f0_undif1 f1_undif1 a_cun p_ineq2i f0_undif1 f1_undif1 a_cun p_inv1 f0_undif1 f1_undif1 a_cun a_cvv f1_undif1 a_cdif f1_undif1 a_cun a_cin f0_undif1 f1_undif1 a_cun a_cvv a_cin f0_undif1 f1_undif1 a_cun p_eqtri f0_undif1 a_cvv f1_undif1 a_cdif a_cin f1_undif1 a_cun f0_undif1 f1_undif1 a_cun a_cvv f1_undif1 a_cdif f1_undif1 a_cun a_cin f0_undif1 f1_undif1 a_cdif f1_undif1 a_cun f0_undif1 f1_undif1 a_cun p_3eqtr3i $.
$}

$(Absorption of difference by union.  This decomposes a union into two
     disjoint classes (see ~ disjdif ).  Part of proof of Corollary 6K of
     [Enderton] p. 144.  (Contributed by NM, 19-May-1998.) $)

${
	$v A B  $.
	f0_undif2 $f class A $.
	f1_undif2 $f class B $.
	p_undif2 $p |- ( A u. ( B \ A ) ) = ( A u. B ) $= f0_undif2 f1_undif2 f0_undif2 a_cdif p_uncom f1_undif2 f0_undif2 p_undif1 f1_undif2 f0_undif2 p_uncom f0_undif2 f1_undif2 f0_undif2 a_cdif a_cun f1_undif2 f0_undif2 a_cdif f0_undif2 a_cun f1_undif2 f0_undif2 a_cun f0_undif2 f1_undif2 a_cun p_3eqtri $.
$}

$(Absorption of difference by union.  (Contributed by NM, 18-Aug-2013.) $)

${
	$v A B  $.
	f0_undifabs $f class A $.
	f1_undifabs $f class B $.
	p_undifabs $p |- ( A u. ( A \ B ) ) = A $= f0_undifabs f0_undifabs f1_undifabs p_undif3 f0_undifabs p_unidm f0_undifabs f0_undifabs a_cun f0_undifabs f1_undifabs f0_undifabs a_cdif p_difeq1i f0_undifabs f1_undifabs p_difdif f0_undifabs f0_undifabs f1_undifabs a_cdif a_cun f0_undifabs f0_undifabs a_cun f1_undifabs f0_undifabs a_cdif a_cdif f0_undifabs f1_undifabs f0_undifabs a_cdif a_cdif f0_undifabs p_3eqtri $.
$}

$(The intersection and class difference of a class with another class
       unite to give the original class.  (Contributed by Paul Chapman,
       5-Jun-2009.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_inundif $f class A $.
	f1_inundif $f class B $.
	i0_inundif $f set x $.
	p_inundif $p |- ( ( A i^i B ) u. ( A \ B ) ) = A $= i0_inundif a_sup_set_class f0_inundif f1_inundif p_elin i0_inundif a_sup_set_class f0_inundif f1_inundif p_eldif i0_inundif a_sup_set_class f0_inundif f1_inundif a_cin a_wcel i0_inundif a_sup_set_class f0_inundif a_wcel i0_inundif a_sup_set_class f1_inundif a_wcel a_wa i0_inundif a_sup_set_class f0_inundif f1_inundif a_cdif a_wcel i0_inundif a_sup_set_class f0_inundif a_wcel i0_inundif a_sup_set_class f1_inundif a_wcel a_wn a_wa p_orbi12i i0_inundif a_sup_set_class f0_inundif a_wcel i0_inundif a_sup_set_class f1_inundif a_wcel p_pm4.42 i0_inundif a_sup_set_class f0_inundif f1_inundif a_cin a_wcel i0_inundif a_sup_set_class f0_inundif f1_inundif a_cdif a_wcel a_wo i0_inundif a_sup_set_class f0_inundif a_wcel i0_inundif a_sup_set_class f1_inundif a_wcel a_wa i0_inundif a_sup_set_class f0_inundif a_wcel i0_inundif a_sup_set_class f1_inundif a_wcel a_wn a_wa a_wo i0_inundif a_sup_set_class f0_inundif a_wcel p_bitr4i i0_inundif f0_inundif f1_inundif a_cin f0_inundif f1_inundif a_cdif f0_inundif p_uneqri $.
$}

$(Absorption of union by difference.  Theorem 36 of [Suppes] p. 29.
     (Contributed by NM, 19-May-1998.) $)

${
	$v A B  $.
	f0_difun2 $f class A $.
	f1_difun2 $f class B $.
	p_difun2 $p |- ( ( A u. B ) \ B ) = ( A \ B ) $= f0_difun2 f1_difun2 f1_difun2 p_difundir f1_difun2 p_difid f1_difun2 f1_difun2 a_cdif a_c0 f0_difun2 f1_difun2 a_cdif p_uneq2i f0_difun2 f1_difun2 a_cdif p_un0 f0_difun2 f1_difun2 a_cun f1_difun2 a_cdif f0_difun2 f1_difun2 a_cdif f1_difun2 f1_difun2 a_cdif a_cun f0_difun2 f1_difun2 a_cdif a_c0 a_cun f0_difun2 f1_difun2 a_cdif p_3eqtri $.
$}

$(Union of complementary parts into whole.  (Contributed by NM,
     22-Mar-1998.) $)

${
	$v A B  $.
	f0_undif $f class A $.
	f1_undif $f class B $.
	p_undif $p |- ( A C_ B <-> ( A u. ( B \ A ) ) = B ) $= f0_undif f1_undif p_ssequn1 f0_undif f1_undif p_undif2 f0_undif f1_undif f0_undif a_cdif a_cun f0_undif f1_undif a_cun f1_undif p_eqeq1i f0_undif f1_undif a_wss f0_undif f1_undif a_cun f1_undif a_wceq f0_undif f1_undif f0_undif a_cdif a_cun f1_undif a_wceq p_bitr4i $.
$}

$(A subset of a difference does not intersect the subtrahend.  (Contributed
     by Jeff Hankins, 1-Sep-2013.)  (Proof shortened by Mario Carneiro,
     24-Aug-2015.) $)

${
	$v A B C  $.
	f0_ssdifin0 $f class A $.
	f1_ssdifin0 $f class B $.
	f2_ssdifin0 $f class C $.
	p_ssdifin0 $p |- ( A C_ ( B \ C ) -> ( A i^i C ) = (/) ) $= f0_ssdifin0 f1_ssdifin0 f2_ssdifin0 a_cdif f2_ssdifin0 p_ssrin f1_ssdifin0 f2_ssdifin0 a_cdif f2_ssdifin0 p_incom f2_ssdifin0 f1_ssdifin0 p_disjdif f1_ssdifin0 f2_ssdifin0 a_cdif f2_ssdifin0 a_cin f2_ssdifin0 f1_ssdifin0 f2_ssdifin0 a_cdif a_cin a_c0 p_eqtri f0_ssdifin0 f2_ssdifin0 a_cin f1_ssdifin0 f2_ssdifin0 a_cdif f2_ssdifin0 a_cin p_sseq0 f0_ssdifin0 f1_ssdifin0 f2_ssdifin0 a_cdif a_wss f0_ssdifin0 f2_ssdifin0 a_cin f1_ssdifin0 f2_ssdifin0 a_cdif f2_ssdifin0 a_cin a_wss f1_ssdifin0 f2_ssdifin0 a_cdif f2_ssdifin0 a_cin a_c0 a_wceq f0_ssdifin0 f2_ssdifin0 a_cin a_c0 a_wceq p_sylancl $.
$}

$(A class is a subclass of itself subtracted from another iff it is the
     empty set.  (Contributed by Steve Rodriguez, 20-Nov-2015.) $)

${
	$v A B  $.
	f0_ssdifeq0 $f class A $.
	f1_ssdifeq0 $f class B $.
	p_ssdifeq0 $p |- ( A C_ ( B \ A ) <-> A = (/) ) $= f0_ssdifeq0 p_inidm f0_ssdifeq0 f1_ssdifeq0 f0_ssdifeq0 p_ssdifin0 f0_ssdifeq0 f1_ssdifeq0 f0_ssdifeq0 a_cdif a_wss f0_ssdifeq0 f0_ssdifeq0 f0_ssdifeq0 a_cin a_c0 p_syl5eqr f1_ssdifeq0 a_c0 a_cdif p_0ss f0_ssdifeq0 a_c0 a_wceq p_id f0_ssdifeq0 a_c0 f1_ssdifeq0 p_difeq2 f0_ssdifeq0 a_c0 a_wceq f0_ssdifeq0 a_c0 f1_ssdifeq0 f0_ssdifeq0 a_cdif f1_ssdifeq0 a_c0 a_cdif p_sseq12d f0_ssdifeq0 a_c0 a_wceq f0_ssdifeq0 f1_ssdifeq0 f0_ssdifeq0 a_cdif a_wss a_c0 f1_ssdifeq0 a_c0 a_cdif a_wss p_mpbiri f0_ssdifeq0 f1_ssdifeq0 f0_ssdifeq0 a_cdif a_wss f0_ssdifeq0 a_c0 a_wceq p_impbii $.
$}

$(A condition equivalent to inclusion in the union of two classes.
       (Contributed by NM, 26-Mar-2007.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ssundif $f class A $.
	f1_ssundif $f class B $.
	f2_ssundif $f class C $.
	i0_ssundif $f set x $.
	p_ssundif $p |- ( A C_ ( B u. C ) <-> ( A \ B ) C_ C ) $= i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif a_wcel i0_ssundif a_sup_set_class f2_ssundif a_wcel p_pm5.6 i0_ssundif a_sup_set_class f0_ssundif f1_ssundif p_eldif i0_ssundif a_sup_set_class f0_ssundif f1_ssundif a_cdif a_wcel i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif a_wcel a_wn a_wa i0_ssundif a_sup_set_class f2_ssundif a_wcel p_imbi1i i0_ssundif a_sup_set_class f1_ssundif f2_ssundif p_elun i0_ssundif a_sup_set_class f1_ssundif f2_ssundif a_cun a_wcel i0_ssundif a_sup_set_class f1_ssundif a_wcel i0_ssundif a_sup_set_class f2_ssundif a_wcel a_wo i0_ssundif a_sup_set_class f0_ssundif a_wcel p_imbi2i i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif a_wcel a_wn a_wa i0_ssundif a_sup_set_class f2_ssundif a_wcel a_wi i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif a_wcel i0_ssundif a_sup_set_class f2_ssundif a_wcel a_wo a_wi i0_ssundif a_sup_set_class f0_ssundif f1_ssundif a_cdif a_wcel i0_ssundif a_sup_set_class f2_ssundif a_wcel a_wi i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif f2_ssundif a_cun a_wcel a_wi p_3bitr4ri i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif f2_ssundif a_cun a_wcel a_wi i0_ssundif a_sup_set_class f0_ssundif f1_ssundif a_cdif a_wcel i0_ssundif a_sup_set_class f2_ssundif a_wcel a_wi i0_ssundif p_albii i0_ssundif f0_ssundif f1_ssundif f2_ssundif a_cun p_dfss2 i0_ssundif f0_ssundif f1_ssundif a_cdif f2_ssundif p_dfss2 i0_ssundif a_sup_set_class f0_ssundif a_wcel i0_ssundif a_sup_set_class f1_ssundif f2_ssundif a_cun a_wcel a_wi i0_ssundif a_wal i0_ssundif a_sup_set_class f0_ssundif f1_ssundif a_cdif a_wcel i0_ssundif a_sup_set_class f2_ssundif a_wcel a_wi i0_ssundif a_wal f0_ssundif f1_ssundif f2_ssundif a_cun a_wss f0_ssundif f1_ssundif a_cdif f2_ssundif a_wss p_3bitr4i $.
$}

$(Swap the arguments of a class difference.  (Contributed by NM,
     29-Mar-2007.) $)

${
	$v A B C  $.
	f0_difcom $f class A $.
	f1_difcom $f class B $.
	f2_difcom $f class C $.
	p_difcom $p |- ( ( A \ B ) C_ C <-> ( A \ C ) C_ B ) $= f1_difcom f2_difcom p_uncom f1_difcom f2_difcom a_cun f2_difcom f1_difcom a_cun f0_difcom p_sseq2i f0_difcom f1_difcom f2_difcom p_ssundif f0_difcom f2_difcom f1_difcom p_ssundif f0_difcom f1_difcom f2_difcom a_cun a_wss f0_difcom f2_difcom f1_difcom a_cun a_wss f0_difcom f1_difcom a_cdif f2_difcom a_wss f0_difcom f2_difcom a_cdif f1_difcom a_wss p_3bitr3i $.
$}

$(Two ways to express overlapping subsets.  (Contributed by Stefan O'Rear,
     31-Oct-2014.) $)

${
	$v A B C  $.
	f0_pssdifcom1 $f class A $.
	f1_pssdifcom1 $f class B $.
	f2_pssdifcom1 $f class C $.
	p_pssdifcom1 $p |- ( ( A C_ C /\ B C_ C ) -> ( ( C \ A ) C. B <-> ( C \ B ) C. A ) ) $= f2_pssdifcom1 f0_pssdifcom1 f1_pssdifcom1 p_difcom f2_pssdifcom1 f0_pssdifcom1 a_cdif f1_pssdifcom1 a_wss f2_pssdifcom1 f1_pssdifcom1 a_cdif f0_pssdifcom1 a_wss a_wb f0_pssdifcom1 f2_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 a_wss a_wa p_a1i f1_pssdifcom1 f0_pssdifcom1 f2_pssdifcom1 p_ssconb f1_pssdifcom1 f2_pssdifcom1 a_wss f0_pssdifcom1 f2_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 f0_pssdifcom1 a_cdif a_wss f0_pssdifcom1 f2_pssdifcom1 f1_pssdifcom1 a_cdif a_wss a_wb p_ancoms f0_pssdifcom1 f2_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 a_wss a_wa f1_pssdifcom1 f2_pssdifcom1 f0_pssdifcom1 a_cdif a_wss f0_pssdifcom1 f2_pssdifcom1 f1_pssdifcom1 a_cdif a_wss p_notbid f0_pssdifcom1 f2_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 a_wss a_wa f2_pssdifcom1 f0_pssdifcom1 a_cdif f1_pssdifcom1 a_wss f2_pssdifcom1 f1_pssdifcom1 a_cdif f0_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 f0_pssdifcom1 a_cdif a_wss a_wn f0_pssdifcom1 f2_pssdifcom1 f1_pssdifcom1 a_cdif a_wss a_wn p_anbi12d f2_pssdifcom1 f0_pssdifcom1 a_cdif f1_pssdifcom1 p_dfpss3 f2_pssdifcom1 f1_pssdifcom1 a_cdif f0_pssdifcom1 p_dfpss3 f0_pssdifcom1 f2_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 a_wss a_wa f2_pssdifcom1 f0_pssdifcom1 a_cdif f1_pssdifcom1 a_wss f1_pssdifcom1 f2_pssdifcom1 f0_pssdifcom1 a_cdif a_wss a_wn a_wa f2_pssdifcom1 f1_pssdifcom1 a_cdif f0_pssdifcom1 a_wss f0_pssdifcom1 f2_pssdifcom1 f1_pssdifcom1 a_cdif a_wss a_wn a_wa f2_pssdifcom1 f0_pssdifcom1 a_cdif f1_pssdifcom1 a_wpss f2_pssdifcom1 f1_pssdifcom1 a_cdif f0_pssdifcom1 a_wpss p_3bitr4g $.
$}

$(Two ways to express non-covering pairs of subsets.  (Contributed by Stefan
     O'Rear, 31-Oct-2014.) $)

${
	$v A B C  $.
	f0_pssdifcom2 $f class A $.
	f1_pssdifcom2 $f class B $.
	f2_pssdifcom2 $f class C $.
	p_pssdifcom2 $p |- ( ( A C_ C /\ B C_ C ) -> ( B C. ( C \ A ) <-> A C. ( C \ B ) ) ) $= f1_pssdifcom2 f0_pssdifcom2 f2_pssdifcom2 p_ssconb f1_pssdifcom2 f2_pssdifcom2 a_wss f0_pssdifcom2 f2_pssdifcom2 a_wss f1_pssdifcom2 f2_pssdifcom2 f0_pssdifcom2 a_cdif a_wss f0_pssdifcom2 f2_pssdifcom2 f1_pssdifcom2 a_cdif a_wss a_wb p_ancoms f2_pssdifcom2 f0_pssdifcom2 f1_pssdifcom2 p_difcom f2_pssdifcom2 f0_pssdifcom2 a_cdif f1_pssdifcom2 a_wss f2_pssdifcom2 f1_pssdifcom2 a_cdif f0_pssdifcom2 a_wss a_wb f0_pssdifcom2 f2_pssdifcom2 a_wss f1_pssdifcom2 f2_pssdifcom2 a_wss a_wa p_a1i f0_pssdifcom2 f2_pssdifcom2 a_wss f1_pssdifcom2 f2_pssdifcom2 a_wss a_wa f2_pssdifcom2 f0_pssdifcom2 a_cdif f1_pssdifcom2 a_wss f2_pssdifcom2 f1_pssdifcom2 a_cdif f0_pssdifcom2 a_wss p_notbid f0_pssdifcom2 f2_pssdifcom2 a_wss f1_pssdifcom2 f2_pssdifcom2 a_wss a_wa f1_pssdifcom2 f2_pssdifcom2 f0_pssdifcom2 a_cdif a_wss f0_pssdifcom2 f2_pssdifcom2 f1_pssdifcom2 a_cdif a_wss f2_pssdifcom2 f0_pssdifcom2 a_cdif f1_pssdifcom2 a_wss a_wn f2_pssdifcom2 f1_pssdifcom2 a_cdif f0_pssdifcom2 a_wss a_wn p_anbi12d f1_pssdifcom2 f2_pssdifcom2 f0_pssdifcom2 a_cdif p_dfpss3 f0_pssdifcom2 f2_pssdifcom2 f1_pssdifcom2 a_cdif p_dfpss3 f0_pssdifcom2 f2_pssdifcom2 a_wss f1_pssdifcom2 f2_pssdifcom2 a_wss a_wa f1_pssdifcom2 f2_pssdifcom2 f0_pssdifcom2 a_cdif a_wss f2_pssdifcom2 f0_pssdifcom2 a_cdif f1_pssdifcom2 a_wss a_wn a_wa f0_pssdifcom2 f2_pssdifcom2 f1_pssdifcom2 a_cdif a_wss f2_pssdifcom2 f1_pssdifcom2 a_cdif f0_pssdifcom2 a_wss a_wn a_wa f1_pssdifcom2 f2_pssdifcom2 f0_pssdifcom2 a_cdif a_wpss f0_pssdifcom2 f2_pssdifcom2 f1_pssdifcom2 a_cdif a_wpss p_3bitr4g $.
$}

$(Distributive law for class difference.  Exercise 4.8 of [Stoll] p. 16.
     (Contributed by NM, 18-Aug-2004.) $)

${
	$v A B C  $.
	f0_difdifdir $f class A $.
	f1_difdifdir $f class B $.
	f2_difdifdir $f class C $.
	p_difdifdir $p |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ ( B \ C ) ) $= f0_difdifdir f1_difdifdir f2_difdifdir p_dif32 f0_difdifdir f2_difdifdir a_cdif f1_difdifdir p_invdif f0_difdifdir f1_difdifdir a_cdif f2_difdifdir a_cdif f0_difdifdir f2_difdifdir a_cdif f1_difdifdir a_cdif f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin p_eqtr4i f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin p_un0 f0_difdifdir f1_difdifdir a_cdif f2_difdifdir a_cdif f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin a_c0 a_cun p_eqtr4i f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif f2_difdifdir p_indi f2_difdifdir f0_difdifdir p_disjdif f2_difdifdir f0_difdifdir f2_difdifdir a_cdif p_incom f2_difdifdir f0_difdifdir f2_difdifdir a_cdif a_cin a_c0 f0_difdifdir f2_difdifdir a_cdif f2_difdifdir a_cin p_eqtr3i a_c0 f0_difdifdir f2_difdifdir a_cdif f2_difdifdir a_cin f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin p_uneq2i f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif f2_difdifdir a_cun a_cin f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin f0_difdifdir f2_difdifdir a_cdif f2_difdifdir a_cin a_cun f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin a_c0 a_cun p_eqtr4i f0_difdifdir f1_difdifdir a_cdif f2_difdifdir a_cdif f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif a_cin a_c0 a_cun f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif f2_difdifdir a_cun a_cin p_eqtr4i f2_difdifdir p_ddif a_cvv a_cvv f2_difdifdir a_cdif a_cdif f2_difdifdir a_cvv f1_difdifdir a_cdif p_uneq2i f1_difdifdir a_cvv f2_difdifdir a_cdif p_indm f1_difdifdir f2_difdifdir p_invdif f1_difdifdir a_cvv f2_difdifdir a_cdif a_cin f1_difdifdir f2_difdifdir a_cdif a_cvv p_difeq2i a_cvv f1_difdifdir a_cvv f2_difdifdir a_cdif a_cin a_cdif a_cvv f1_difdifdir a_cdif a_cvv a_cvv f2_difdifdir a_cdif a_cdif a_cun a_cvv f1_difdifdir f2_difdifdir a_cdif a_cdif p_eqtr3i a_cvv f1_difdifdir a_cdif a_cvv a_cvv f2_difdifdir a_cdif a_cdif a_cun a_cvv f1_difdifdir a_cdif f2_difdifdir a_cun a_cvv f1_difdifdir f2_difdifdir a_cdif a_cdif p_eqtr3i a_cvv f1_difdifdir a_cdif f2_difdifdir a_cun a_cvv f1_difdifdir f2_difdifdir a_cdif a_cdif f0_difdifdir f2_difdifdir a_cdif p_ineq2i f0_difdifdir f2_difdifdir a_cdif f1_difdifdir f2_difdifdir a_cdif p_invdif f0_difdifdir f1_difdifdir a_cdif f2_difdifdir a_cdif f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir a_cdif f2_difdifdir a_cun a_cin f0_difdifdir f2_difdifdir a_cdif a_cvv f1_difdifdir f2_difdifdir a_cdif a_cdif a_cin f0_difdifdir f2_difdifdir a_cdif f1_difdifdir f2_difdifdir a_cdif a_cdif p_3eqtri $.
$}

$(Two ways to say that ` A ` and ` B ` partition ` C ` (when ` A ` and ` B `
     don't overlap and ` A ` is a part of ` C ` ).  (Contributed by FL,
     17-Nov-2008.) $)

${
	$v A B C  $.
	f0_uneqdifeq $f class A $.
	f1_uneqdifeq $f class B $.
	f2_uneqdifeq $f class C $.
	p_uneqdifeq $p |- ( ( A C_ C /\ ( A i^i B ) = (/) ) -> ( ( A u. B ) = C <-> ( C \ A ) = B ) ) $= f1_uneqdifeq f0_uneqdifeq p_uncom f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq p_eqtr f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq f1_uneqdifeq a_cun a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq a_wa f1_uneqdifeq f0_uneqdifeq a_cun f2_uneqdifeq p_eqcomd f2_uneqdifeq f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq p_difeq1 f1_uneqdifeq f0_uneqdifeq p_difun2 f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif p_eqtr f0_uneqdifeq f1_uneqdifeq p_incom f0_uneqdifeq f1_uneqdifeq a_cin f1_uneqdifeq f0_uneqdifeq a_cin a_c0 p_eqeq1i f1_uneqdifeq f0_uneqdifeq p_disj3 f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f1_uneqdifeq f0_uneqdifeq a_cin a_c0 a_wceq f1_uneqdifeq f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq p_bitri f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq p_eqtr f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq f1_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq p_expcom f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wi f1_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq p_eqcoms f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f1_uneqdifeq f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wi p_sylbi f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq a_cdif a_wceq f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq a_wa f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq p_syl5com f2_uneqdifeq f1_uneqdifeq f0_uneqdifeq a_cun a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq a_cdif a_wceq f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq a_cdif f1_uneqdifeq f0_uneqdifeq a_cdif a_wceq f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wi p_sylancl f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq f1_uneqdifeq a_cun a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq a_wa f2_uneqdifeq f1_uneqdifeq f0_uneqdifeq a_cun a_wceq f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wi p_syl f1_uneqdifeq f0_uneqdifeq a_cun f0_uneqdifeq f1_uneqdifeq a_cun a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wi p_mpan f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq p_com12 f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wi f0_uneqdifeq f2_uneqdifeq a_wss p_adantl f2_uneqdifeq f0_uneqdifeq p_difss f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq f2_uneqdifeq p_sseq1 f0_uneqdifeq f1_uneqdifeq f2_uneqdifeq p_unss f0_uneqdifeq f2_uneqdifeq a_wss f1_uneqdifeq f2_uneqdifeq a_wss a_wa f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss p_biimpi f0_uneqdifeq f2_uneqdifeq a_wss f1_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss p_expcom f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f2_uneqdifeq a_wss f1_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss a_wi p_syl6bi f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f2_uneqdifeq a_wss f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss a_wi p_mpi f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss p_com12 f0_uneqdifeq f2_uneqdifeq a_wss f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss a_wi f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq p_adantr f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq a_wa f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wss p_imp f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq p_eqimss f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wss f0_uneqdifeq f2_uneqdifeq a_wss p_adantl f2_uneqdifeq f0_uneqdifeq f1_uneqdifeq p_ssundif f0_uneqdifeq f2_uneqdifeq a_wss f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wa f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wss f2_uneqdifeq f0_uneqdifeq f1_uneqdifeq a_cun a_wss p_sylibr f0_uneqdifeq f2_uneqdifeq a_wss f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq f1_uneqdifeq a_cun a_wss f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq p_adantlr f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq a_wa f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq a_wa f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq p_eqssd f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq a_wa f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq p_ex f0_uneqdifeq f2_uneqdifeq a_wss f0_uneqdifeq f1_uneqdifeq a_cin a_c0 a_wceq a_wa f0_uneqdifeq f1_uneqdifeq a_cun f2_uneqdifeq a_wceq f2_uneqdifeq f0_uneqdifeq a_cdif f1_uneqdifeq a_wceq p_impbid $.
$}

$(Theorem 19.2 of [Margaris] p. 89 with restricted quantifiers (compare
       ~ 19.2 ).  The restricted version is valid only when the domain of
       quantification is not empty.  (Contributed by NM, 15-Nov-2003.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_r19.2z $f wff ph $.
	f1_r19.2z $f set x $.
	f2_r19.2z $f class A $.
	p_r19.2z $p |- ( ( A =/= (/) /\ A. x e. A ph ) -> E. x e. A ph ) $= f0_r19.2z f1_r19.2z f2_r19.2z a_df-ral f1_r19.2z a_sup_set_class f2_r19.2z a_wcel f0_r19.2z f1_r19.2z p_exintr f0_r19.2z f1_r19.2z f2_r19.2z a_wral f1_r19.2z a_sup_set_class f2_r19.2z a_wcel f0_r19.2z a_wi f1_r19.2z a_wal f1_r19.2z a_sup_set_class f2_r19.2z a_wcel f1_r19.2z a_wex f1_r19.2z a_sup_set_class f2_r19.2z a_wcel f0_r19.2z a_wa f1_r19.2z a_wex a_wi p_sylbi f1_r19.2z f2_r19.2z p_n0 f0_r19.2z f1_r19.2z f2_r19.2z a_df-rex f0_r19.2z f1_r19.2z f2_r19.2z a_wral f1_r19.2z a_sup_set_class f2_r19.2z a_wcel f1_r19.2z a_wex f1_r19.2z a_sup_set_class f2_r19.2z a_wcel f0_r19.2z a_wa f1_r19.2z a_wex f2_r19.2z a_c0 a_wne f0_r19.2z f1_r19.2z f2_r19.2z a_wrex p_3imtr4g f0_r19.2z f1_r19.2z f2_r19.2z a_wral f2_r19.2z a_c0 a_wne f0_r19.2z f1_r19.2z f2_r19.2z a_wrex p_impcom $.
$}

$(A response to the notion that the condition ` A =/= (/) ` can be removed
       in ~ r19.2z .  Interestingly enough, ` ph ` does not figure in the
       left-hand side.  (Contributed by Jeff Hankins, 24-Aug-2009.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_r19.2zb $f wff ph $.
	f1_r19.2zb $f set x $.
	f2_r19.2zb $f class A $.
	p_r19.2zb $p |- ( A =/= (/) <-> ( A. x e. A ph -> E. x e. A ph ) ) $= f0_r19.2zb f1_r19.2zb f2_r19.2zb p_r19.2z f2_r19.2zb a_c0 a_wne f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wral f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wrex p_ex f1_r19.2zb a_sup_set_class p_noel f1_r19.2zb a_sup_set_class a_c0 a_wcel f0_r19.2zb p_pm2.21i f0_r19.2zb f1_r19.2zb a_c0 p_rgen f0_r19.2zb f1_r19.2zb f2_r19.2zb a_c0 p_raleq f2_r19.2zb a_c0 a_wceq f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wral f0_r19.2zb f1_r19.2zb a_c0 a_wral p_mpbiri f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wral f2_r19.2zb a_c0 p_necon3bi f1_r19.2zb a_sup_set_class f2_r19.2zb a_wcel f0_r19.2zb f1_r19.2zb p_exsimpl f0_r19.2zb f1_r19.2zb f2_r19.2zb a_df-rex f1_r19.2zb f2_r19.2zb p_n0 f1_r19.2zb a_sup_set_class f2_r19.2zb a_wcel f0_r19.2zb a_wa f1_r19.2zb a_wex f1_r19.2zb a_sup_set_class f2_r19.2zb a_wcel f1_r19.2zb a_wex f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wrex f2_r19.2zb a_c0 a_wne p_3imtr4i f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wral f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wrex f2_r19.2zb a_c0 a_wne p_ja f2_r19.2zb a_c0 a_wne f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wral f0_r19.2zb f1_r19.2zb f2_r19.2zb a_wrex a_wi p_impbii $.
$}

$(Restricted quantification of wff not containing quantified variable.
       (Contributed by FL, 3-Jan-2008.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_r19.3rz $f wff ph $.
	f1_r19.3rz $f set x $.
	f2_r19.3rz $f class A $.
	e0_r19.3rz $e |- F/ x ph $.
	p_r19.3rz $p |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) ) $= f1_r19.3rz f2_r19.3rz p_n0 f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f1_r19.3rz a_wex f0_r19.3rz p_biimt f2_r19.3rz a_c0 a_wne f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f1_r19.3rz a_wex f0_r19.3rz f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f1_r19.3rz a_wex f0_r19.3rz a_wi a_wb p_sylbi f0_r19.3rz f1_r19.3rz f2_r19.3rz a_df-ral e0_r19.3rz f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f0_r19.3rz f1_r19.3rz p_19.23 f0_r19.3rz f1_r19.3rz f2_r19.3rz a_wral f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f0_r19.3rz a_wi f1_r19.3rz a_wal f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f1_r19.3rz a_wex f0_r19.3rz a_wi p_bitri f2_r19.3rz a_c0 a_wne f0_r19.3rz f1_r19.3rz a_sup_set_class f2_r19.3rz a_wcel f1_r19.3rz a_wex f0_r19.3rz a_wi f0_r19.3rz f1_r19.3rz f2_r19.3rz a_wral p_syl6bbr $.
$}

$(Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 26-Oct-2010.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	f0_r19.28z $f wff ph $.
	f1_r19.28z $f wff ps $.
	f2_r19.28z $f set x $.
	f3_r19.28z $f class A $.
	e0_r19.28z $e |- F/ x ph $.
	p_r19.28z $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) ) $= e0_r19.28z f0_r19.28z f2_r19.28z f3_r19.28z p_r19.3rz f3_r19.28z a_c0 a_wne f0_r19.28z f0_r19.28z f2_r19.28z f3_r19.28z a_wral f1_r19.28z f2_r19.28z f3_r19.28z a_wral p_anbi1d f0_r19.28z f1_r19.28z f2_r19.28z f3_r19.28z p_r19.26 f3_r19.28z a_c0 a_wne f0_r19.28z f1_r19.28z f2_r19.28z f3_r19.28z a_wral a_wa f0_r19.28z f2_r19.28z f3_r19.28z a_wral f1_r19.28z f2_r19.28z f3_r19.28z a_wral a_wa f0_r19.28z f1_r19.28z a_wa f2_r19.28z f3_r19.28z a_wral p_syl6rbbr $.
$}

$(Restricted quantification of wff not containing quantified variable.
       (Contributed by NM, 10-Mar-1997.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x ph  $.
	f0_r19.3rzv $f wff ph $.
	f1_r19.3rzv $f set x $.
	f2_r19.3rzv $f class A $.
	p_r19.3rzv $p |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) ) $= f1_r19.3rzv f2_r19.3rzv p_n0 f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f1_r19.3rzv a_wex f0_r19.3rzv p_biimt f2_r19.3rzv a_c0 a_wne f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f1_r19.3rzv a_wex f0_r19.3rzv f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f1_r19.3rzv a_wex f0_r19.3rzv a_wi a_wb p_sylbi f0_r19.3rzv f1_r19.3rzv f2_r19.3rzv a_df-ral f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f0_r19.3rzv f1_r19.3rzv p_19.23v f0_r19.3rzv f1_r19.3rzv f2_r19.3rzv a_wral f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f0_r19.3rzv a_wi f1_r19.3rzv a_wal f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f1_r19.3rzv a_wex f0_r19.3rzv a_wi p_bitri f2_r19.3rzv a_c0 a_wne f0_r19.3rzv f1_r19.3rzv a_sup_set_class f2_r19.3rzv a_wcel f1_r19.3rzv a_wex f0_r19.3rzv a_wi f0_r19.3rzv f1_r19.3rzv f2_r19.3rzv a_wral p_syl6bbr $.
$}

$(Restricted quantification of wff not containing quantified variable.
       (Contributed by NM, 27-May-1998.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x ph  $.
	f0_r19.9rzv $f wff ph $.
	f1_r19.9rzv $f set x $.
	f2_r19.9rzv $f class A $.
	p_r19.9rzv $p |- ( A =/= (/) -> ( ph <-> E. x e. A ph ) ) $= f0_r19.9rzv a_wn f1_r19.9rzv f2_r19.9rzv p_r19.3rzv f2_r19.9rzv a_c0 a_wne f0_r19.9rzv a_wn f0_r19.9rzv a_wn f1_r19.9rzv f2_r19.9rzv a_wral p_bicomd f2_r19.9rzv a_c0 a_wne f0_r19.9rzv a_wn f1_r19.9rzv f2_r19.9rzv a_wral f0_r19.9rzv p_con2bid f0_r19.9rzv f1_r19.9rzv f2_r19.9rzv p_dfrex2 f2_r19.9rzv a_c0 a_wne f0_r19.9rzv f0_r19.9rzv a_wn f1_r19.9rzv f2_r19.9rzv a_wral a_wn f0_r19.9rzv f1_r19.9rzv f2_r19.9rzv a_wrex p_syl6bbr $.
$}

$(Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 19-Aug-2004.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ph  $.
	f0_r19.28zv $f wff ph $.
	f1_r19.28zv $f wff ps $.
	f2_r19.28zv $f set x $.
	f3_r19.28zv $f class A $.
	p_r19.28zv $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) ) $= f0_r19.28zv f2_r19.28zv f3_r19.28zv p_r19.3rzv f3_r19.28zv a_c0 a_wne f0_r19.28zv f0_r19.28zv f2_r19.28zv f3_r19.28zv a_wral f1_r19.28zv f2_r19.28zv f3_r19.28zv a_wral p_anbi1d f0_r19.28zv f1_r19.28zv f2_r19.28zv f3_r19.28zv p_r19.26 f3_r19.28zv a_c0 a_wne f0_r19.28zv f1_r19.28zv f2_r19.28zv f3_r19.28zv a_wral a_wa f0_r19.28zv f2_r19.28zv f3_r19.28zv a_wral f1_r19.28zv f2_r19.28zv f3_r19.28zv a_wral a_wa f0_r19.28zv f1_r19.28zv a_wa f2_r19.28zv f3_r19.28zv a_wral p_syl6rbbr $.
$}

$(Restricted quantifier version of Theorem 19.37 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by Paul Chapman, 8-Oct-2007.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ph  $.
	f0_r19.37zv $f wff ph $.
	f1_r19.37zv $f wff ps $.
	f2_r19.37zv $f set x $.
	f3_r19.37zv $f class A $.
	p_r19.37zv $p |- ( A =/= (/) -> ( E. x e. A ( ph -> ps ) <-> ( ph -> E. x e. A ps ) ) ) $= f0_r19.37zv f2_r19.37zv f3_r19.37zv p_r19.3rzv f3_r19.37zv a_c0 a_wne f0_r19.37zv f0_r19.37zv f2_r19.37zv f3_r19.37zv a_wral f1_r19.37zv f2_r19.37zv f3_r19.37zv a_wrex p_imbi1d f0_r19.37zv f1_r19.37zv f2_r19.37zv f3_r19.37zv p_r19.35 f3_r19.37zv a_c0 a_wne f0_r19.37zv f1_r19.37zv f2_r19.37zv f3_r19.37zv a_wrex a_wi f0_r19.37zv f2_r19.37zv f3_r19.37zv a_wral f1_r19.37zv f2_r19.37zv f3_r19.37zv a_wrex a_wi f0_r19.37zv f1_r19.37zv a_wi f2_r19.37zv f3_r19.37zv a_wrex p_syl6rbbr $.
$}

$(Restricted version of Theorem 19.45 of [Margaris] p. 90.  (Contributed
       by NM, 27-May-1998.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ph  $.
	f0_r19.45zv $f wff ph $.
	f1_r19.45zv $f wff ps $.
	f2_r19.45zv $f set x $.
	f3_r19.45zv $f class A $.
	p_r19.45zv $p |- ( A =/= (/) -> ( E. x e. A ( ph \/ ps ) <-> ( ph \/ E. x e. A ps ) ) ) $= f0_r19.45zv f2_r19.45zv f3_r19.45zv p_r19.9rzv f3_r19.45zv a_c0 a_wne f0_r19.45zv f0_r19.45zv f2_r19.45zv f3_r19.45zv a_wrex f1_r19.45zv f2_r19.45zv f3_r19.45zv a_wrex p_orbi1d f0_r19.45zv f1_r19.45zv f2_r19.45zv f3_r19.45zv p_r19.43 f3_r19.45zv a_c0 a_wne f0_r19.45zv f1_r19.45zv f2_r19.45zv f3_r19.45zv a_wrex a_wo f0_r19.45zv f2_r19.45zv f3_r19.45zv a_wrex f1_r19.45zv f2_r19.45zv f3_r19.45zv a_wrex a_wo f0_r19.45zv f1_r19.45zv a_wo f2_r19.45zv f3_r19.45zv a_wrex p_syl6rbbr $.
$}

$(Restricted quantifier version of Theorem 19.27 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 26-Oct-2010.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	f0_r19.27z $f wff ph $.
	f1_r19.27z $f wff ps $.
	f2_r19.27z $f set x $.
	f3_r19.27z $f class A $.
	e0_r19.27z $e |- F/ x ps $.
	p_r19.27z $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) ) $= e0_r19.27z f1_r19.27z f2_r19.27z f3_r19.27z p_r19.3rz f3_r19.27z a_c0 a_wne f1_r19.27z f1_r19.27z f2_r19.27z f3_r19.27z a_wral f0_r19.27z f2_r19.27z f3_r19.27z a_wral p_anbi2d f0_r19.27z f1_r19.27z f2_r19.27z f3_r19.27z p_r19.26 f3_r19.27z a_c0 a_wne f0_r19.27z f2_r19.27z f3_r19.27z a_wral f1_r19.27z a_wa f0_r19.27z f2_r19.27z f3_r19.27z a_wral f1_r19.27z f2_r19.27z f3_r19.27z a_wral a_wa f0_r19.27z f1_r19.27z a_wa f2_r19.27z f3_r19.27z a_wral p_syl6rbbr $.
$}

$(Restricted quantifier version of Theorem 19.27 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 19-Aug-2004.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_r19.27zv $f wff ph $.
	f1_r19.27zv $f wff ps $.
	f2_r19.27zv $f set x $.
	f3_r19.27zv $f class A $.
	p_r19.27zv $p |- ( A =/= (/) -> ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) ) $= f1_r19.27zv f2_r19.27zv f3_r19.27zv p_r19.3rzv f3_r19.27zv a_c0 a_wne f1_r19.27zv f1_r19.27zv f2_r19.27zv f3_r19.27zv a_wral f0_r19.27zv f2_r19.27zv f3_r19.27zv a_wral p_anbi2d f0_r19.27zv f1_r19.27zv f2_r19.27zv f3_r19.27zv p_r19.26 f3_r19.27zv a_c0 a_wne f0_r19.27zv f2_r19.27zv f3_r19.27zv a_wral f1_r19.27zv a_wa f0_r19.27zv f2_r19.27zv f3_r19.27zv a_wral f1_r19.27zv f2_r19.27zv f3_r19.27zv a_wral a_wa f0_r19.27zv f1_r19.27zv a_wa f2_r19.27zv f3_r19.27zv a_wral p_syl6rbbr $.
$}

$(Restricted quantifier version of Theorem 19.36 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 20-Sep-2003.) $)

${
	$v ph ps x A  $.
	$d x A  $.
	$d x ps  $.
	f0_r19.36zv $f wff ph $.
	f1_r19.36zv $f wff ps $.
	f2_r19.36zv $f set x $.
	f3_r19.36zv $f class A $.
	p_r19.36zv $p |- ( A =/= (/) -> ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> ps ) ) ) $= f1_r19.36zv f2_r19.36zv f3_r19.36zv p_r19.9rzv f3_r19.36zv a_c0 a_wne f1_r19.36zv f1_r19.36zv f2_r19.36zv f3_r19.36zv a_wrex f0_r19.36zv f2_r19.36zv f3_r19.36zv a_wral p_imbi2d f0_r19.36zv f1_r19.36zv f2_r19.36zv f3_r19.36zv p_r19.35 f3_r19.36zv a_c0 a_wne f0_r19.36zv f2_r19.36zv f3_r19.36zv a_wral f1_r19.36zv a_wi f0_r19.36zv f2_r19.36zv f3_r19.36zv a_wral f1_r19.36zv f2_r19.36zv f3_r19.36zv a_wrex a_wi f0_r19.36zv f1_r19.36zv a_wi f2_r19.36zv f3_r19.36zv a_wrex p_syl6rbbr $.
$}

$(Vacuous quantification is always true.  (Contributed by NM,
       11-Mar-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_rzal $f wff ph $.
	f1_rzal $f set x $.
	f2_rzal $f class A $.
	p_rzal $p |- ( A = (/) -> A. x e. A ph ) $= f2_rzal f1_rzal a_sup_set_class p_ne0i f1_rzal a_sup_set_class f2_rzal a_wcel f2_rzal a_c0 p_necon2bi f2_rzal a_c0 a_wceq f1_rzal a_sup_set_class f2_rzal a_wcel f0_rzal p_pm2.21d f2_rzal a_c0 a_wceq f0_rzal f1_rzal f2_rzal p_ralrimiv $.
$}

$(Restricted existential quantification implies its restriction is
       nonempty.  (Contributed by Szymon Jaroszewicz, 3-Apr-2007.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_rexn0 $f wff ph $.
	f1_rexn0 $f set x $.
	f2_rexn0 $f class A $.
	p_rexn0 $p |- ( E. x e. A ph -> A =/= (/) ) $= f2_rexn0 f1_rexn0 a_sup_set_class p_ne0i f1_rexn0 a_sup_set_class f2_rexn0 a_wcel f2_rexn0 a_c0 a_wne f0_rexn0 p_a1d f0_rexn0 f2_rexn0 a_c0 a_wne f1_rexn0 f2_rexn0 p_rexlimiv $.
$}

$(Idempotent law for restricted quantifier.  (Contributed by NM,
       28-Mar-1997.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_ralidm $f wff ph $.
	f1_ralidm $f set x $.
	f2_ralidm $f class A $.
	p_ralidm $p |- ( A. x e. A A. x e. A ph <-> A. x e. A ph ) $= f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm p_rzal f0_ralidm f1_ralidm f2_ralidm p_rzal f2_ralidm a_c0 a_wceq f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm a_wral f0_ralidm f1_ralidm f2_ralidm a_wral p_2thd f1_ralidm f2_ralidm p_neq0 f1_ralidm a_sup_set_class f2_ralidm a_wcel f1_ralidm a_wex f0_ralidm f1_ralidm f2_ralidm a_wral p_biimt f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm a_df-ral f0_ralidm f1_ralidm f2_ralidm p_nfra1 f1_ralidm a_sup_set_class f2_ralidm a_wcel f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm p_19.23 f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm a_wral f1_ralidm a_sup_set_class f2_ralidm a_wcel f0_ralidm f1_ralidm f2_ralidm a_wral a_wi f1_ralidm a_wal f1_ralidm a_sup_set_class f2_ralidm a_wcel f1_ralidm a_wex f0_ralidm f1_ralidm f2_ralidm a_wral a_wi p_bitri f1_ralidm a_sup_set_class f2_ralidm a_wcel f1_ralidm a_wex f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm a_sup_set_class f2_ralidm a_wcel f1_ralidm a_wex f0_ralidm f1_ralidm f2_ralidm a_wral a_wi f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm a_wral p_syl6rbbr f2_ralidm a_c0 a_wceq a_wn f1_ralidm a_sup_set_class f2_ralidm a_wcel f1_ralidm a_wex f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm a_wral f0_ralidm f1_ralidm f2_ralidm a_wral a_wb p_sylbi f2_ralidm a_c0 a_wceq f0_ralidm f1_ralidm f2_ralidm a_wral f1_ralidm f2_ralidm a_wral f0_ralidm f1_ralidm f2_ralidm a_wral a_wb p_pm2.61i $.
$}

$(Vacuous universal quantification is always true.  (Contributed by NM,
     20-Oct-2005.) $)

${
	$v ph x  $.
	f0_ral0 $f wff ph $.
	f1_ral0 $f set x $.
	p_ral0 $p |- A. x e. (/) ph $= f1_ral0 a_sup_set_class p_noel f1_ral0 a_sup_set_class a_c0 a_wcel f0_ral0 p_pm2.21i f0_ral0 f1_ral0 a_c0 p_rgen $.
$}

$(Generalization rule that eliminates a non-zero class requirement.
       (Contributed by NM, 8-Dec-2012.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_rgenz $f wff ph $.
	f1_rgenz $f set x $.
	f2_rgenz $f class A $.
	e0_rgenz $e |- ( ( A =/= (/) /\ x e. A ) -> ph ) $.
	p_rgenz $p |- A. x e. A ph $= f0_rgenz f1_rgenz f2_rgenz p_rzal e0_rgenz f2_rgenz a_c0 a_wne f0_rgenz f1_rgenz f2_rgenz p_ralrimiva f0_rgenz f1_rgenz f2_rgenz a_wral f2_rgenz a_c0 p_pm2.61ine $.
$}

$(The quantification of a falsehood is vacuous when true.  (Contributed by
       NM, 26-Nov-2005.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_ralf0 $f wff ph $.
	f1_ralf0 $f set x $.
	f2_ralf0 $f class A $.
	e0_ralf0 $e |- -. ph $.
	p_ralf0 $p |- ( A. x e. A ph <-> A = (/) ) $= e0_ralf0 f1_ralf0 a_sup_set_class f2_ralf0 a_wcel f0_ralf0 p_con3 f1_ralf0 a_sup_set_class f2_ralf0 a_wcel f0_ralf0 a_wi f0_ralf0 a_wn f1_ralf0 a_sup_set_class f2_ralf0 a_wcel a_wn p_mpi f1_ralf0 a_sup_set_class f2_ralf0 a_wcel f0_ralf0 a_wi f1_ralf0 a_sup_set_class f2_ralf0 a_wcel a_wn f1_ralf0 p_alimi f0_ralf0 f1_ralf0 f2_ralf0 a_df-ral f1_ralf0 f2_ralf0 p_eq0 f1_ralf0 a_sup_set_class f2_ralf0 a_wcel f0_ralf0 a_wi f1_ralf0 a_wal f1_ralf0 a_sup_set_class f2_ralf0 a_wcel a_wn f1_ralf0 a_wal f0_ralf0 f1_ralf0 f2_ralf0 a_wral f2_ralf0 a_c0 a_wceq p_3imtr4i f0_ralf0 f1_ralf0 f2_ralf0 p_rzal f0_ralf0 f1_ralf0 f2_ralf0 a_wral f2_ralf0 a_c0 a_wceq p_impbii $.
$}

$(TODO - shorten r19.3zv, r19.27zv, r19.28zv, raaanv w/ non-v $)

$(Rearrange restricted quantifiers.  (Contributed by NM, 26-Oct-2010.) $)

${
	$v ph ps x y A  $.
	$d x y A  $.
	f0_raaan $f wff ph $.
	f1_raaan $f wff ps $.
	f2_raaan $f set x $.
	f3_raaan $f set y $.
	f4_raaan $f class A $.
	e0_raaan $e |- F/ y ph $.
	e1_raaan $e |- F/ x ps $.
	p_raaan $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. A ps ) ) $= f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f2_raaan f4_raaan p_rzal f0_raaan f2_raaan f4_raaan p_rzal f1_raaan f3_raaan f4_raaan p_rzal f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f2_raaan f4_raaan a_wral f0_raaan f2_raaan f4_raaan a_wral f1_raaan f3_raaan f4_raaan a_wral a_wa p_pm5.1 f4_raaan a_c0 a_wceq f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f2_raaan f4_raaan a_wral f0_raaan f2_raaan f4_raaan a_wral f1_raaan f3_raaan f4_raaan a_wral f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f2_raaan f4_raaan a_wral f0_raaan f2_raaan f4_raaan a_wral f1_raaan f3_raaan f4_raaan a_wral a_wa a_wb p_syl12anc e0_raaan f0_raaan f1_raaan f3_raaan f4_raaan p_r19.28z f4_raaan a_c0 a_wne f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f0_raaan f1_raaan f3_raaan f4_raaan a_wral a_wa f2_raaan f4_raaan p_ralbidv f2_raaan f4_raaan p_nfcv e1_raaan f1_raaan f2_raaan f3_raaan f4_raaan p_nfral f0_raaan f1_raaan f3_raaan f4_raaan a_wral f2_raaan f4_raaan p_r19.27z f4_raaan a_c0 a_wne f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f2_raaan f4_raaan a_wral f0_raaan f1_raaan f3_raaan f4_raaan a_wral a_wa f2_raaan f4_raaan a_wral f0_raaan f2_raaan f4_raaan a_wral f1_raaan f3_raaan f4_raaan a_wral a_wa p_bitrd f0_raaan f1_raaan a_wa f3_raaan f4_raaan a_wral f2_raaan f4_raaan a_wral f0_raaan f2_raaan f4_raaan a_wral f1_raaan f3_raaan f4_raaan a_wral a_wa a_wb f4_raaan a_c0 p_pm2.61ine $.
$}

$(Rearrange restricted quantifiers.  (Contributed by NM, 11-Mar-1997.) $)

${
	$v ph ps x y A  $.
	$d y ph  $.
	$d x ps  $.
	$d x y A  $.
	f0_raaanv $f wff ph $.
	f1_raaanv $f wff ps $.
	f2_raaanv $f set x $.
	f3_raaanv $f set y $.
	f4_raaanv $f class A $.
	p_raaanv $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ A. y e. A ps ) ) $= f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv p_rzal f0_raaanv f2_raaanv f4_raaanv p_rzal f1_raaanv f3_raaanv f4_raaanv p_rzal f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv a_wral f0_raaanv f2_raaanv f4_raaanv a_wral f1_raaanv f3_raaanv f4_raaanv a_wral a_wa p_pm5.1 f4_raaanv a_c0 a_wceq f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv a_wral f0_raaanv f2_raaanv f4_raaanv a_wral f1_raaanv f3_raaanv f4_raaanv a_wral f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv a_wral f0_raaanv f2_raaanv f4_raaanv a_wral f1_raaanv f3_raaanv f4_raaanv a_wral a_wa a_wb p_syl12anc f0_raaanv f1_raaanv f3_raaanv f4_raaanv p_r19.28zv f4_raaanv a_c0 a_wne f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f0_raaanv f1_raaanv f3_raaanv f4_raaanv a_wral a_wa f2_raaanv f4_raaanv p_ralbidv f0_raaanv f1_raaanv f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv p_r19.27zv f4_raaanv a_c0 a_wne f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv a_wral f0_raaanv f1_raaanv f3_raaanv f4_raaanv a_wral a_wa f2_raaanv f4_raaanv a_wral f0_raaanv f2_raaanv f4_raaanv a_wral f1_raaanv f3_raaanv f4_raaanv a_wral a_wa p_bitrd f0_raaanv f1_raaanv a_wa f3_raaanv f4_raaanv a_wral f2_raaanv f4_raaanv a_wral f0_raaanv f2_raaanv f4_raaanv a_wral f1_raaanv f3_raaanv f4_raaanv a_wral a_wa a_wb f4_raaanv a_c0 p_pm2.61ine $.
$}

$(Set substitution into the first argument of a subset relation.
       (Contributed by Rodolfo Medina, 7-Jul-2010.)  (Proof shortened by Mario
       Carneiro, 14-Nov-2016.) $)

${
	$v x y A  $.
	$d z y  $.
	$d z x A  $.
	f0_sbss $f set x $.
	f1_sbss $f set y $.
	f2_sbss $f class A $.
	i0_sbss $f set z $.
	p_sbss $p |- ( [ y / x ] x C_ A <-> y C_ A ) $= f1_sbss p_vex f0_sbss a_sup_set_class f2_sbss a_wss i0_sbss f1_sbss f0_sbss p_sbequ i0_sbss a_sup_set_class f1_sbss a_sup_set_class f2_sbss p_sseq1 i0_sbss a_sup_set_class f2_sbss a_wss f0_sbss p_nfv f0_sbss a_sup_set_class i0_sbss a_sup_set_class f2_sbss p_sseq1 f0_sbss a_sup_set_class f2_sbss a_wss i0_sbss a_sup_set_class f2_sbss a_wss f0_sbss i0_sbss p_sbie f0_sbss a_sup_set_class f2_sbss a_wss f0_sbss i0_sbss a_wsb i0_sbss a_sup_set_class f2_sbss a_wss f0_sbss a_sup_set_class f2_sbss a_wss f0_sbss f1_sbss a_wsb f1_sbss a_sup_set_class f2_sbss a_wss i0_sbss f1_sbss a_sup_set_class p_vtoclb $.
$}

$(Distribute proper substitution through a subclass relation.
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Alexander
       van der Vekens, 23-Jul-2017.) $)

${
	$v x A B C D  $.
	$d A y  $.
	$d B y  $.
	$d C y  $.
	$d D y  $.
	$d x y  $.
	f0_sbcss $f set x $.
	f1_sbcss $f class A $.
	f2_sbcss $f class B $.
	f3_sbcss $f class C $.
	f4_sbcss $f class D $.
	i0_sbcss $f set y $.
	p_sbcss $p |- ( A e. B -> ( [. A / x ]. C C_ D <-> [_ A / x ]_ C C_ [_ A / x ]_ D ) ) $= i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi i0_sbcss f0_sbcss f1_sbcss f2_sbcss p_sbcalg i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel f0_sbcss f1_sbcss f2_sbcss p_sbcimg f0_sbcss f1_sbcss i0_sbcss a_sup_set_class f3_sbcss f2_sbcss p_sbcel2g f0_sbcss f1_sbcss i0_sbcss a_sup_set_class f4_sbcss f2_sbcss p_sbcel2g f1_sbcss f2_sbcss a_wcel i0_sbcss a_sup_set_class f3_sbcss a_wcel f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f3_sbcss a_csb a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f4_sbcss a_csb a_wcel p_imbi12d f1_sbcss f2_sbcss a_wcel i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f3_sbcss a_wcel f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f4_sbcss a_wcel f0_sbcss f1_sbcss a_wsbc a_wi i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f3_sbcss a_csb a_wcel i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f4_sbcss a_csb a_wcel a_wi p_bitrd f1_sbcss f2_sbcss a_wcel i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f3_sbcss a_csb a_wcel i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f4_sbcss a_csb a_wcel a_wi i0_sbcss p_albidv f1_sbcss f2_sbcss a_wcel i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi i0_sbcss a_wal f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi f0_sbcss f1_sbcss a_wsbc i0_sbcss a_wal i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f3_sbcss a_csb a_wcel i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f4_sbcss a_csb a_wcel a_wi i0_sbcss a_wal p_bitrd i0_sbcss f3_sbcss f4_sbcss p_dfss2 f3_sbcss f4_sbcss a_wss i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi i0_sbcss a_wal f0_sbcss f1_sbcss p_sbcbii i0_sbcss f0_sbcss f1_sbcss f3_sbcss a_csb f0_sbcss f1_sbcss f4_sbcss a_csb p_dfss2 f1_sbcss f2_sbcss a_wcel i0_sbcss a_sup_set_class f3_sbcss a_wcel i0_sbcss a_sup_set_class f4_sbcss a_wcel a_wi i0_sbcss a_wal f0_sbcss f1_sbcss a_wsbc i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f3_sbcss a_csb a_wcel i0_sbcss a_sup_set_class f0_sbcss f1_sbcss f4_sbcss a_csb a_wcel a_wi i0_sbcss a_wal f3_sbcss f4_sbcss a_wss f0_sbcss f1_sbcss a_wsbc f0_sbcss f1_sbcss f3_sbcss a_csb f0_sbcss f1_sbcss f4_sbcss a_csb a_wss p_3bitr4g $.
$}


