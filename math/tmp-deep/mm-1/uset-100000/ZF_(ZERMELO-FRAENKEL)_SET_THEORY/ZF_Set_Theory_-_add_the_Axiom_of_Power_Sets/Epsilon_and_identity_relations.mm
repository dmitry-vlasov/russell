$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Power_class_of_union_and_intersection.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Epsilon and identity relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new constant symbols. $)

$c _E $.

$(Letter E (for epsilon relation) $)

$c _I $.

$(Letter I (for identity relation) $)

$(Extend class notation to include the epsilon relation. $)

${
	$v  $.
	a_cep $a class _E $.
$}

$(Extend the definition of a class to include identity relation. $)

${
	$v  $.
	a_cid $a class _I $.
$}

$(Define the epsilon relation.  Similar to Definition 6.22 of
       [TakeutiZaring] p. 30.  The epsilon relation and set membership are the
       same, that is, ` ( A _E B <-> A e. B ) ` when ` B ` is a set by
       ~ epelg .  Thus, ` 5 _E { 1 , 5 } ` ( ~ ex-eprel ).  (Contributed by NM,
       13-Aug-1995.) $)

${
	$v x y  $.
	$d x y  $.
	f0_df-eprel $f set x $.
	f1_df-eprel $f set y $.
	a_df-eprel $a |- _E = { <. x , y >. | x e. y } $.
$}

$(The epsilon relation and membership are the same.  General version of
       ~ epel .  (Contributed by Scott Fenton, 27-Mar-2011.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)

${
	$v A B V  $.
	$d A x y  $.
	$d B x y  $.
	f0_epelg $f class A $.
	f1_epelg $f class B $.
	f2_epelg $f class V $.
	i0_epelg $f set x $.
	i1_epelg $f set y $.
	p_epelg $p |- ( B e. V -> ( A _E B <-> A e. B ) ) $= f0_epelg f1_epelg a_cep a_df-br i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel i0_epelg i1_epelg f0_epelg f1_epelg a_cop p_elopab i0_epelg p_vex i1_epelg p_vex i0_epelg a_sup_set_class a_cvv a_wcel i1_epelg a_sup_set_class a_cvv a_wcel p_pm3.2i f0_epelg f1_epelg i0_epelg a_sup_set_class i1_epelg a_sup_set_class p_opeqex f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_cop a_wceq f0_epelg a_cvv a_wcel f1_epelg a_cvv a_wcel a_wa i0_epelg a_sup_set_class a_cvv a_wcel i1_epelg a_sup_set_class a_cvv a_wcel a_wa p_mpbiri f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_cop a_wceq f0_epelg a_cvv a_wcel f1_epelg a_cvv a_wcel p_simpld f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_cop a_wceq f0_epelg a_cvv a_wcel i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel p_adantr f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_cop a_wceq i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel a_wa f0_epelg a_cvv a_wcel i0_epelg i1_epelg p_exlimivv f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel i0_epelg i1_epelg a_copab a_wcel f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_cop a_wceq i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel a_wa i1_epelg a_wex i0_epelg a_wex f0_epelg a_cvv a_wcel p_sylbi i0_epelg i1_epelg a_df-eprel f0_epelg a_cvv a_wcel f0_epelg f1_epelg a_cop i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel i0_epelg i1_epelg a_copab a_cep p_eleq2s f0_epelg f1_epelg a_cep a_wbr f0_epelg f1_epelg a_cop a_cep a_wcel f0_epelg a_cvv a_wcel p_sylbi f0_epelg f1_epelg a_cep a_wbr f0_epelg a_cvv a_wcel a_wi f1_epelg f2_epelg a_wcel p_a1i f0_epelg f1_epelg p_elex f0_epelg f1_epelg a_wcel f0_epelg a_cvv a_wcel a_wi f1_epelg f2_epelg a_wcel p_a1i i0_epelg a_sup_set_class f0_epelg i1_epelg a_sup_set_class f1_epelg p_eleq12 i0_epelg i1_epelg a_df-eprel i0_epelg a_sup_set_class i1_epelg a_sup_set_class a_wcel f0_epelg f1_epelg a_wcel i0_epelg i1_epelg f0_epelg f1_epelg a_cep a_cvv f2_epelg p_brabga f0_epelg a_cvv a_wcel f1_epelg f2_epelg a_wcel f0_epelg f1_epelg a_cep a_wbr f0_epelg f1_epelg a_wcel a_wb p_expcom f1_epelg f2_epelg a_wcel f0_epelg a_cvv a_wcel f0_epelg f1_epelg a_cep a_wbr f0_epelg f1_epelg a_wcel p_pm5.21ndd $.
$}

$(The epsilon relationship and the membership relation are the same.
       (Contributed by Scott Fenton, 11-Apr-2012.) $)

${
	$v A B  $.
	f0_epelc $f class A $.
	f1_epelc $f class B $.
	e0_epelc $e |- B e. _V $.
	p_epelc $p |- ( A _E B <-> A e. B ) $= e0_epelc f0_epelc f1_epelc a_cvv p_epelg f1_epelc a_cvv a_wcel f0_epelc f1_epelc a_cep a_wbr f0_epelc f1_epelc a_wcel a_wb a_ax-mp $.
$}

$(The epsilon relation and the membership relation are the same.
     (Contributed by NM, 13-Aug-1995.) $)

${
	$v x y  $.
	f0_epel $f set x $.
	f1_epel $f set y $.
	p_epel $p |- ( x _E y <-> x e. y ) $= f1_epel p_vex f0_epel a_sup_set_class f1_epel a_sup_set_class p_epelc $.
$}

$(Define the identity relation.  Definition 9.15 of [Quine] p. 64.  For
       example, ` 5 _I 5 ` and ` -. 4 _I 5 ` ( ~ ex-id ).  (Contributed by NM,
       13-Aug-1995.) $)

${
	$v x y  $.
	$d x y  $.
	f0_df-id $f set x $.
	f1_df-id $f set y $.
	a_df-id $a |- _I = { <. x , y >. | x = y } $.
$}

$(A stronger version of ~ df-id that doesn't require ` x ` and ` y ` to be
       distinct.  Ordinarily, we wouldn't use this as a definition, since
       non-distinct dummy variables would make soundness verification more
       difficult (as the proof here shows).  The proof can be instructive in
       showing how distinct variable requirements may be eliminated, a task
       that is not necessarily obvious.  (Contributed by NM, 5-Feb-2008.)
       (Revised by Mario Carneiro, 18-Nov-2016.) $)

${
	$v x y  $.
	$d w z x  $.
	$d w z y  $.
	f0_dfid3 $f set x $.
	f1_dfid3 $f set y $.
	i0_dfid3 $f set z $.
	i1_dfid3 $f set w $.
	p_dfid3 $p |- _I = { <. x , y >. | x = y } $= f0_dfid3 i0_dfid3 a_df-id i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq p_ancom f0_dfid3 i0_dfid3 p_equcom f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq i0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq p_anbi1i i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq a_wa i0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq a_wa p_bitri i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq a_wa i0_dfid3 p_exbii f0_dfid3 p_vex i0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class p_opeq2 i0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop i1_dfid3 a_sup_set_class p_eqeq2d i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq i0_dfid3 f0_dfid3 a_sup_set_class p_ceqsexv f0_dfid3 p_equid f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq p_biantru i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex i0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq a_wa i0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa p_3bitri i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 p_exbii i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 p_nfe1 i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 a_wex f0_dfid3 p_19.9 i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 a_wex f0_dfid3 a_wex p_bitr4i f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class p_opeq2 f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop i1_dfid3 a_sup_set_class p_eqeq2d f0_dfid3 f1_dfid3 f0_dfid3 p_equequ2 f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq p_anbi12d f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa a_wb f0_dfid3 p_sps i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 f1_dfid3 p_drex1 i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f1_dfid3 a_wex f0_dfid3 f1_dfid3 f0_dfid3 p_drex2 i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class a_wceq a_wa f0_dfid3 a_wex f0_dfid3 a_wex f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f1_dfid3 a_wex f0_dfid3 a_wex p_syl5bb f0_dfid3 f1_dfid3 f0_dfid3 p_nfnae f0_dfid3 f1_dfid3 f1_dfid3 p_nfnae f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn f1_dfid3 i1_dfid3 a_sup_set_class p_nfcvd f0_dfid3 f1_dfid3 p_nfcvf2 f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn f1_dfid3 i0_dfid3 a_sup_set_class p_nfcvd f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn f1_dfid3 f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class p_nfopd f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn f1_dfid3 i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop p_nfeqd f0_dfid3 f1_dfid3 p_nfcvf2 f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn f1_dfid3 i0_dfid3 a_sup_set_class p_nfcvd f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn f1_dfid3 f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class p_nfeqd f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq f1_dfid3 p_nfand i0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class p_opeq2 i0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop i1_dfid3 a_sup_set_class p_eqeq2d i0_dfid3 f1_dfid3 f0_dfid3 p_equequ2 i0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq p_anbi12d i0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa a_wb a_wi f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn p_a1i f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 f1_dfid3 p_cbvexd f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal a_wn i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f1_dfid3 a_wex f0_dfid3 p_exbid f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 a_wal i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f1_dfid3 a_wex f0_dfid3 a_wex a_wb p_pm2.61i i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f1_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 p_abbii f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq f0_dfid3 i0_dfid3 i1_dfid3 a_df-opab f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 f1_dfid3 i1_dfid3 a_df-opab i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq a_wa i0_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 a_cab i1_dfid3 a_sup_set_class f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_cop a_wceq f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq a_wa f1_dfid3 a_wex f0_dfid3 a_wex i1_dfid3 a_cab f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq f0_dfid3 i0_dfid3 a_copab f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 f1_dfid3 a_copab p_3eqtr4i a_cid f0_dfid3 a_sup_set_class i0_dfid3 a_sup_set_class a_wceq f0_dfid3 i0_dfid3 a_copab f0_dfid3 a_sup_set_class f1_dfid3 a_sup_set_class a_wceq f0_dfid3 f1_dfid3 a_copab p_eqtri $.
$}

$(Alternate definition of the identity relation.  (Contributed by NM,
     15-Mar-2007.) $)

${
	$v x  $.
	f0_dfid2 $f set x $.
	p_dfid2 $p |- _I = { <. x , x >. | x = x } $= f0_dfid2 f0_dfid2 p_dfid3 $.
$}


