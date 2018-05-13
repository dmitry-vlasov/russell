$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Operations.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        "Maps to" notation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(If a two-parameter class is not empty, constrain the implicit pair.
       (Contributed by Stefan O'Rear, 7-Mar-2015.) $)

${
	$v x y A B C S T F X  $.
	$d A x y z  $.
	$d B x y z  $.
	$d C z  $.
	f0_elmpt2cl $f set x $.
	f1_elmpt2cl $f set y $.
	f2_elmpt2cl $f class A $.
	f3_elmpt2cl $f class B $.
	f4_elmpt2cl $f class C $.
	f5_elmpt2cl $f class S $.
	f6_elmpt2cl $f class T $.
	f7_elmpt2cl $f class F $.
	f8_elmpt2cl $f class X $.
	i0_elmpt2cl $f set z $.
	e0_elmpt2cl $e |- F = ( x e. A , y e. B |-> C ) $.
	p_elmpt2cl $p |- ( X e. ( S F T ) -> ( S e. A /\ T e. B ) ) $= e0_elmpt2cl f0_elmpt2cl f1_elmpt2cl i0_elmpt2cl f2_elmpt2cl f3_elmpt2cl f4_elmpt2cl a_df-mpt2 f7_elmpt2cl f0_elmpt2cl f1_elmpt2cl f2_elmpt2cl f3_elmpt2cl f4_elmpt2cl a_cmpt2 f0_elmpt2cl a_sup_set_class f2_elmpt2cl a_wcel f1_elmpt2cl a_sup_set_class f3_elmpt2cl a_wcel a_wa i0_elmpt2cl a_sup_set_class f4_elmpt2cl a_wceq a_wa f0_elmpt2cl f1_elmpt2cl i0_elmpt2cl a_coprab p_eqtri f7_elmpt2cl f0_elmpt2cl a_sup_set_class f2_elmpt2cl a_wcel f1_elmpt2cl a_sup_set_class f3_elmpt2cl a_wcel a_wa i0_elmpt2cl a_sup_set_class f4_elmpt2cl a_wceq a_wa f0_elmpt2cl f1_elmpt2cl i0_elmpt2cl a_coprab p_dmeqi i0_elmpt2cl a_sup_set_class f4_elmpt2cl a_wceq f0_elmpt2cl f1_elmpt2cl i0_elmpt2cl f2_elmpt2cl f3_elmpt2cl p_dmoprabss f7_elmpt2cl a_cdm f0_elmpt2cl a_sup_set_class f2_elmpt2cl a_wcel f1_elmpt2cl a_sup_set_class f3_elmpt2cl a_wcel a_wa i0_elmpt2cl a_sup_set_class f4_elmpt2cl a_wceq a_wa f0_elmpt2cl f1_elmpt2cl i0_elmpt2cl a_coprab a_cdm f2_elmpt2cl f3_elmpt2cl a_cxp p_eqsstri f8_elmpt2cl f5_elmpt2cl f6_elmpt2cl a_cop f7_elmpt2cl p_elfvdm f5_elmpt2cl f6_elmpt2cl f7_elmpt2cl a_df-ov f5_elmpt2cl f6_elmpt2cl a_cop f7_elmpt2cl a_cdm a_wcel f8_elmpt2cl f5_elmpt2cl f6_elmpt2cl a_cop f7_elmpt2cl a_cfv f5_elmpt2cl f6_elmpt2cl f7_elmpt2cl a_co p_eleq2s f8_elmpt2cl f5_elmpt2cl f6_elmpt2cl f7_elmpt2cl a_co a_wcel f7_elmpt2cl a_cdm f2_elmpt2cl f3_elmpt2cl a_cxp f5_elmpt2cl f6_elmpt2cl a_cop p_sseldi f5_elmpt2cl f6_elmpt2cl f2_elmpt2cl f3_elmpt2cl p_opelxp f8_elmpt2cl f5_elmpt2cl f6_elmpt2cl f7_elmpt2cl a_co a_wcel f5_elmpt2cl f6_elmpt2cl a_cop f2_elmpt2cl f3_elmpt2cl a_cxp a_wcel f5_elmpt2cl f2_elmpt2cl a_wcel f6_elmpt2cl f3_elmpt2cl a_wcel a_wa p_sylib $.
$}

$(If a two-parameter class is not empty, the first argument is in its
       nominal domain.  (Contributed by FL, 15-Oct-2012.)  (Revised by Stefan
       O'Rear, 7-Mar-2015.) $)

${
	$v x y A B C S T F X  $.
	$d A x y  $.
	$d B x y  $.
	$d C  $.
	f0_elmpt2cl1 $f set x $.
	f1_elmpt2cl1 $f set y $.
	f2_elmpt2cl1 $f class A $.
	f3_elmpt2cl1 $f class B $.
	f4_elmpt2cl1 $f class C $.
	f5_elmpt2cl1 $f class S $.
	f6_elmpt2cl1 $f class T $.
	f7_elmpt2cl1 $f class F $.
	f8_elmpt2cl1 $f class X $.
	e0_elmpt2cl1 $e |- F = ( x e. A , y e. B |-> C ) $.
	p_elmpt2cl1 $p |- ( X e. ( S F T ) -> S e. A ) $= e0_elmpt2cl1 f0_elmpt2cl1 f1_elmpt2cl1 f2_elmpt2cl1 f3_elmpt2cl1 f4_elmpt2cl1 f5_elmpt2cl1 f6_elmpt2cl1 f7_elmpt2cl1 f8_elmpt2cl1 p_elmpt2cl f8_elmpt2cl1 f5_elmpt2cl1 f6_elmpt2cl1 f7_elmpt2cl1 a_co a_wcel f5_elmpt2cl1 f2_elmpt2cl1 a_wcel f6_elmpt2cl1 f3_elmpt2cl1 a_wcel p_simpld $.
$}

$(If a two-parameter class is not empty, the second argument is in its
       nominal domain.  (Contributed by FL, 15-Oct-2012.)  (Revised by Stefan
       O'Rear, 7-Mar-2015.) $)

${
	$v x y A B C S T F X  $.
	$d A x y  $.
	$d B x y  $.
	$d C  $.
	f0_elmpt2cl2 $f set x $.
	f1_elmpt2cl2 $f set y $.
	f2_elmpt2cl2 $f class A $.
	f3_elmpt2cl2 $f class B $.
	f4_elmpt2cl2 $f class C $.
	f5_elmpt2cl2 $f class S $.
	f6_elmpt2cl2 $f class T $.
	f7_elmpt2cl2 $f class F $.
	f8_elmpt2cl2 $f class X $.
	e0_elmpt2cl2 $e |- F = ( x e. A , y e. B |-> C ) $.
	p_elmpt2cl2 $p |- ( X e. ( S F T ) -> T e. B ) $= e0_elmpt2cl2 f0_elmpt2cl2 f1_elmpt2cl2 f2_elmpt2cl2 f3_elmpt2cl2 f4_elmpt2cl2 f5_elmpt2cl2 f6_elmpt2cl2 f7_elmpt2cl2 f8_elmpt2cl2 p_elmpt2cl f8_elmpt2cl2 f5_elmpt2cl2 f6_elmpt2cl2 f7_elmpt2cl2 a_co a_wcel f5_elmpt2cl2 f2_elmpt2cl2 a_wcel f6_elmpt2cl2 f3_elmpt2cl2 a_wcel p_simprd $.
$}

$(Utility lemma for two-parameter classes.

       _EDITORIAL_: can simplify ~ isghm , ~ islmhm .  (Contributed by Stefan
       O'Rear, 21-Jan-2015.) $)

${
	$v A B C D E F X Y a b  $.
	$d A a b  $.
	$d B a b  $.
	$d E a b  $.
	$d F a b  $.
	$d X a b  $.
	$d Y a b  $.
	$d a b  $.
	f0_elovmpt2 $f class A $.
	f1_elovmpt2 $f class B $.
	f2_elovmpt2 $f class C $.
	f3_elovmpt2 $f class D $.
	f4_elovmpt2 $f class E $.
	f5_elovmpt2 $f class F $.
	f6_elovmpt2 $f class X $.
	f7_elovmpt2 $f class Y $.
	f8_elovmpt2 $f set a $.
	f9_elovmpt2 $f set b $.
	e0_elovmpt2 $e |- D = ( a e. A , b e. B |-> C ) $.
	e1_elovmpt2 $e |- C e. _V $.
	e2_elovmpt2 $e |- ( ( a = X /\ b = Y ) -> C = E ) $.
	p_elovmpt2 $p |- ( F e. ( X D Y ) <-> ( X e. A /\ Y e. B /\ F e. E ) ) $= e0_elovmpt2 f8_elovmpt2 f9_elovmpt2 f0_elovmpt2 f1_elovmpt2 f2_elovmpt2 f6_elovmpt2 f7_elovmpt2 f3_elovmpt2 f5_elovmpt2 p_elmpt2cl e1_elovmpt2 f2_elovmpt2 a_cvv a_wcel f8_elovmpt2 f9_elovmpt2 p_gen2 e2_elovmpt2 f8_elovmpt2 a_sup_set_class f6_elovmpt2 a_wceq f9_elovmpt2 a_sup_set_class f7_elovmpt2 a_wceq a_wa f2_elovmpt2 f4_elovmpt2 a_cvv p_eleq1d f2_elovmpt2 a_cvv a_wcel f4_elovmpt2 a_cvv a_wcel f8_elovmpt2 f9_elovmpt2 f6_elovmpt2 f7_elovmpt2 f0_elovmpt2 f1_elovmpt2 p_spc2gv f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel a_wa f2_elovmpt2 a_cvv a_wcel f9_elovmpt2 a_wal f8_elovmpt2 a_wal f4_elovmpt2 a_cvv a_wcel p_mpi e2_elovmpt2 e0_elovmpt2 f8_elovmpt2 f9_elovmpt2 f6_elovmpt2 f7_elovmpt2 f0_elovmpt2 f1_elovmpt2 f2_elovmpt2 f4_elovmpt2 f3_elovmpt2 a_cvv p_ovmpt2ga f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel f4_elovmpt2 a_cvv a_wcel f6_elovmpt2 f7_elovmpt2 f3_elovmpt2 a_co f4_elovmpt2 a_wceq p_mpd3an3 f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel a_wa f6_elovmpt2 f7_elovmpt2 f3_elovmpt2 a_co f4_elovmpt2 f5_elovmpt2 p_eleq2d f5_elovmpt2 f6_elovmpt2 f7_elovmpt2 f3_elovmpt2 a_co a_wcel f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel a_wa f5_elovmpt2 f4_elovmpt2 a_wcel p_biadan2 f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel f5_elovmpt2 f4_elovmpt2 a_wcel a_df-3an f5_elovmpt2 f6_elovmpt2 f7_elovmpt2 f3_elovmpt2 a_co a_wcel f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel a_wa f5_elovmpt2 f4_elovmpt2 a_wcel a_wa f6_elovmpt2 f0_elovmpt2 a_wcel f7_elovmpt2 f1_elovmpt2 a_wcel f5_elovmpt2 f4_elovmpt2 a_wcel a_w3a p_bitr4i $.
$}

$(Any function to sets of ordered pairs produces a relation on function
       value unconditionally.  (Contributed by Mario Carneiro, 7-Aug-2014.)
       (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)

${
	$v ph x y z A B F  $.
	$d x A  $.
	$d B  $.
	$d F  $.
	f0_relmptopab $f wff ph $.
	f1_relmptopab $f set x $.
	f2_relmptopab $f set y $.
	f3_relmptopab $f set z $.
	f4_relmptopab $f class A $.
	f5_relmptopab $f class B $.
	f6_relmptopab $f class F $.
	e0_relmptopab $e |- F = ( x e. A |-> { <. y , z >. | ph } ) $.
	p_relmptopab $p |- Rel ( F ` B ) $= e0_relmptopab f1_relmptopab f4_relmptopab f0_relmptopab f2_relmptopab f3_relmptopab a_copab a_cvv a_cvv a_cxp f5_relmptopab f6_relmptopab p_fvmptss f0_relmptopab f2_relmptopab f3_relmptopab p_relopab f0_relmptopab f2_relmptopab f3_relmptopab a_copab a_df-rel f0_relmptopab f2_relmptopab f3_relmptopab a_copab a_wrel f0_relmptopab f2_relmptopab f3_relmptopab a_copab a_cvv a_cvv a_cxp a_wss p_mpbi f0_relmptopab f2_relmptopab f3_relmptopab a_copab a_cvv a_cvv a_cxp a_wss f1_relmptopab a_sup_set_class f4_relmptopab a_wcel p_a1i f0_relmptopab f2_relmptopab f3_relmptopab a_copab a_cvv a_cvv a_cxp a_wss f5_relmptopab f6_relmptopab a_cfv a_cvv a_cvv a_cxp a_wss f1_relmptopab f4_relmptopab p_mprg f5_relmptopab f6_relmptopab a_cfv a_df-rel f5_relmptopab f6_relmptopab a_cfv a_wrel f5_relmptopab f6_relmptopab a_cfv a_cvv a_cvv a_cxp a_wss p_mpbir $.
$}

$(Describe an implicit one-to-one onto function.  (Contributed by Mario
         Carneiro, 30-Apr-2015.) $)

${
	$v ph x y A B C D F W X  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	$d x D  $.
	$d x y ph  $.
	f0_f1ocnvd $f wff ph $.
	f1_f1ocnvd $f set x $.
	f2_f1ocnvd $f set y $.
	f3_f1ocnvd $f class A $.
	f4_f1ocnvd $f class B $.
	f5_f1ocnvd $f class C $.
	f6_f1ocnvd $f class D $.
	f7_f1ocnvd $f class F $.
	f8_f1ocnvd $f class W $.
	f9_f1ocnvd $f class X $.
	e0_f1ocnvd $e |- F = ( x e. A |-> C ) $.
	e1_f1ocnvd $e |- ( ( ph /\ x e. A ) -> C e. W ) $.
	e2_f1ocnvd $e |- ( ( ph /\ y e. B ) -> D e. X ) $.
	e3_f1ocnvd $e |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) ) $.
	p_f1ocnvd $p |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $= e1_f1ocnvd f0_f1ocnvd f5_f1ocnvd f8_f1ocnvd a_wcel f1_f1ocnvd f3_f1ocnvd p_ralrimiva e0_f1ocnvd f1_f1ocnvd f3_f1ocnvd f5_f1ocnvd f7_f1ocnvd f8_f1ocnvd p_fnmpt f0_f1ocnvd f5_f1ocnvd f8_f1ocnvd a_wcel f1_f1ocnvd f3_f1ocnvd a_wral f7_f1ocnvd f3_f1ocnvd a_wfn p_syl e2_f1ocnvd f0_f1ocnvd f6_f1ocnvd f9_f1ocnvd a_wcel f2_f1ocnvd f4_f1ocnvd p_ralrimiva f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt p_eqid f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt f9_f1ocnvd p_fnmpt f0_f1ocnvd f6_f1ocnvd f9_f1ocnvd a_wcel f2_f1ocnvd f4_f1ocnvd a_wral f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt f4_f1ocnvd a_wfn p_syl e3_f1ocnvd f0_f1ocnvd f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f2_f1ocnvd a_sup_set_class f4_f1ocnvd a_wcel f1_f1ocnvd a_sup_set_class f6_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd p_opabbidv e0_f1ocnvd f1_f1ocnvd f2_f1ocnvd f3_f1ocnvd f5_f1ocnvd a_df-mpt f7_f1ocnvd f1_f1ocnvd f3_f1ocnvd f5_f1ocnvd a_cmpt f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd a_copab p_eqtri f7_f1ocnvd f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd a_copab p_cnveqi f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd p_cnvopab f7_f1ocnvd a_ccnv f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd a_copab a_ccnv f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd a_copab p_eqtri f2_f1ocnvd f1_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_df-mpt f0_f1ocnvd f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd a_copab f2_f1ocnvd a_sup_set_class f4_f1ocnvd a_wcel f1_f1ocnvd a_sup_set_class f6_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd a_copab f7_f1ocnvd a_ccnv f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt p_3eqtr4g f0_f1ocnvd f4_f1ocnvd f7_f1ocnvd a_ccnv f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt p_fneq1d f0_f1ocnvd f7_f1ocnvd a_ccnv f4_f1ocnvd a_wfn f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt f4_f1ocnvd a_wfn p_mpbird f3_f1ocnvd f4_f1ocnvd f7_f1ocnvd p_dff1o4 f0_f1ocnvd f7_f1ocnvd f3_f1ocnvd a_wfn f7_f1ocnvd a_ccnv f4_f1ocnvd a_wfn f3_f1ocnvd f4_f1ocnvd f7_f1ocnvd a_wf1o p_sylanbrc e3_f1ocnvd f0_f1ocnvd f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f2_f1ocnvd a_sup_set_class f4_f1ocnvd a_wcel f1_f1ocnvd a_sup_set_class f6_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd p_opabbidv e0_f1ocnvd f1_f1ocnvd f2_f1ocnvd f3_f1ocnvd f5_f1ocnvd a_df-mpt f7_f1ocnvd f1_f1ocnvd f3_f1ocnvd f5_f1ocnvd a_cmpt f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd a_copab p_eqtri f7_f1ocnvd f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd a_copab p_cnveqi f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd p_cnvopab f7_f1ocnvd a_ccnv f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f1_f1ocnvd f2_f1ocnvd a_copab a_ccnv f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd a_copab p_eqtri f2_f1ocnvd f1_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_df-mpt f0_f1ocnvd f1_f1ocnvd a_sup_set_class f3_f1ocnvd a_wcel f2_f1ocnvd a_sup_set_class f5_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd a_copab f2_f1ocnvd a_sup_set_class f4_f1ocnvd a_wcel f1_f1ocnvd a_sup_set_class f6_f1ocnvd a_wceq a_wa f2_f1ocnvd f1_f1ocnvd a_copab f7_f1ocnvd a_ccnv f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt p_3eqtr4g f0_f1ocnvd f3_f1ocnvd f4_f1ocnvd f7_f1ocnvd a_wf1o f7_f1ocnvd a_ccnv f2_f1ocnvd f4_f1ocnvd f6_f1ocnvd a_cmpt a_wceq p_jca $.
$}

$(Describe an implicit one-to-one onto function.  (Contributed by Mario
         Carneiro, 12-May-2014.) $)

${
	$v ph x y A B C D F W X  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	$d x D  $.
	$d x y ph  $.
	f0_f1od $f wff ph $.
	f1_f1od $f set x $.
	f2_f1od $f set y $.
	f3_f1od $f class A $.
	f4_f1od $f class B $.
	f5_f1od $f class C $.
	f6_f1od $f class D $.
	f7_f1od $f class F $.
	f8_f1od $f class W $.
	f9_f1od $f class X $.
	e0_f1od $e |- F = ( x e. A |-> C ) $.
	e1_f1od $e |- ( ( ph /\ x e. A ) -> C e. W ) $.
	e2_f1od $e |- ( ( ph /\ y e. B ) -> D e. X ) $.
	e3_f1od $e |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) ) $.
	p_f1od $p |- ( ph -> F : A -1-1-onto-> B ) $= e0_f1od e1_f1od e2_f1od e3_f1od f0_f1od f1_f1od f2_f1od f3_f1od f4_f1od f5_f1od f6_f1od f7_f1od f8_f1od f9_f1od p_f1ocnvd f0_f1od f3_f1od f4_f1od f7_f1od a_wf1o f7_f1od a_ccnv f2_f1od f4_f1od f6_f1od a_cmpt a_wceq p_simpld $.
$}

$(Describe an implicit one-to-one onto function.  (Contributed by Mario
       Carneiro, 30-Apr-2015.) $)

${
	$v ph x y A B C D F  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	$d x D  $.
	$d x y ph  $.
	f0_f1ocnv2d $f wff ph $.
	f1_f1ocnv2d $f set x $.
	f2_f1ocnv2d $f set y $.
	f3_f1ocnv2d $f class A $.
	f4_f1ocnv2d $f class B $.
	f5_f1ocnv2d $f class C $.
	f6_f1ocnv2d $f class D $.
	f7_f1ocnv2d $f class F $.
	e0_f1ocnv2d $e |- F = ( x e. A |-> C ) $.
	e1_f1ocnv2d $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
	e2_f1ocnv2d $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
	e3_f1ocnv2d $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) ) $.
	p_f1ocnv2d $p |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $= e0_f1ocnv2d e1_f1ocnv2d e2_f1ocnv2d e1_f1ocnv2d f5_f1ocnv2d f4_f1ocnv2d f2_f1ocnv2d a_sup_set_class p_eleq1a f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel a_wa f5_f1ocnv2d f4_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel a_wi p_syl f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel p_impr e3_f1ocnv2d f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel a_wa a_wa f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq p_biimpar f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq p_exp42 f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq p_com34 f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq a_wi p_imp32 f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq a_wa a_wa f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq p_jcai e2_f1ocnv2d f6_f1ocnv2d f3_f1ocnv2d f1_f1ocnv2d a_sup_set_class p_eleq1a f0_f1ocnv2d f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel a_wa f6_f1ocnv2d f3_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel a_wi p_syl f0_f1ocnv2d f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel p_impr e3_f1ocnv2d f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel a_wa a_wa f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq p_biimpa f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq p_exp42 f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq a_wi p_com23 f0_f1ocnv2d f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq p_com34 f0_f1ocnv2d f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq a_wi p_imp32 f0_f1ocnv2d f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq a_wa a_wa f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq p_jcai f0_f1ocnv2d f1_f1ocnv2d a_sup_set_class f3_f1ocnv2d a_wcel f2_f1ocnv2d a_sup_set_class f5_f1ocnv2d a_wceq a_wa f2_f1ocnv2d a_sup_set_class f4_f1ocnv2d a_wcel f1_f1ocnv2d a_sup_set_class f6_f1ocnv2d a_wceq a_wa p_impbida f0_f1ocnv2d f1_f1ocnv2d f2_f1ocnv2d f3_f1ocnv2d f4_f1ocnv2d f5_f1ocnv2d f6_f1ocnv2d f7_f1ocnv2d f4_f1ocnv2d f3_f1ocnv2d p_f1ocnvd $.
$}

$(Describe an implicit one-to-one onto function.  (Contributed by Mario
       Carneiro, 12-May-2014.) $)

${
	$v ph x y A B C D F  $.
	$d x y A  $.
	$d x y B  $.
	$d y C  $.
	$d x D  $.
	$d x y ph  $.
	f0_f1o2d $f wff ph $.
	f1_f1o2d $f set x $.
	f2_f1o2d $f set y $.
	f3_f1o2d $f class A $.
	f4_f1o2d $f class B $.
	f5_f1o2d $f class C $.
	f6_f1o2d $f class D $.
	f7_f1o2d $f class F $.
	e0_f1o2d $e |- F = ( x e. A |-> C ) $.
	e1_f1o2d $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
	e2_f1o2d $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
	e3_f1o2d $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) ) $.
	p_f1o2d $p |- ( ph -> F : A -1-1-onto-> B ) $= e0_f1o2d e1_f1o2d e2_f1o2d e3_f1o2d f0_f1o2d f1_f1o2d f2_f1o2d f3_f1o2d f4_f1o2d f5_f1o2d f6_f1o2d f7_f1o2d p_f1ocnv2d f0_f1o2d f3_f1o2d f4_f1o2d f7_f1o2d a_wf1o f7_f1o2d a_ccnv f2_f1o2d f4_f1o2d f6_f1o2d a_cmpt a_wceq p_simpld $.
$}

$(The cross product of two sets is a set.  Proposition 6.2 of
       [TakeutiZaring] p. 23.  This version is proven using Replacement; see
       ~ xpexg for a version that uses the Power Set axiom instead.
       (Contributed by Mario Carneiro, 20-May-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v A B V W  $.
	$d A x y  $.
	$d B x y  $.
	$d V y  $.
	f0_xpexgALT $f class A $.
	f1_xpexgALT $f class B $.
	f2_xpexgALT $f class V $.
	f3_xpexgALT $f class W $.
	i0_xpexgALT $f set x $.
	i1_xpexgALT $f set y $.
	p_xpexgALT $p |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V ) $= i1_xpexgALT f1_xpexgALT p_iunid i1_xpexgALT f1_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_ciun f1_xpexgALT f0_xpexgALT p_xpeq2i i1_xpexgALT f1_xpexgALT i1_xpexgALT a_sup_set_class a_csn f0_xpexgALT p_xpiundi f0_xpexgALT i1_xpexgALT f1_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_ciun a_cxp f0_xpexgALT f1_xpexgALT a_cxp i1_xpexgALT f1_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp a_ciun p_eqtr3i f1_xpexgALT f3_xpexgALT a_wcel p_id i0_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class p_fconstmpt i0_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class f2_xpexgALT p_mptexg f0_xpexgALT f2_xpexgALT a_wcel f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp i0_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class a_cmpt a_cvv p_syl5eqel f0_xpexgALT f2_xpexgALT a_wcel f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp a_cvv a_wcel i1_xpexgALT f1_xpexgALT p_ralrimivw i1_xpexgALT f1_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp f3_xpexgALT a_cvv p_iunexg f1_xpexgALT f3_xpexgALT a_wcel f1_xpexgALT f3_xpexgALT a_wcel f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp a_cvv a_wcel i1_xpexgALT f1_xpexgALT a_wral i1_xpexgALT f1_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp a_ciun a_cvv a_wcel f0_xpexgALT f2_xpexgALT a_wcel p_syl2anr f0_xpexgALT f2_xpexgALT a_wcel f1_xpexgALT f3_xpexgALT a_wcel a_wa f0_xpexgALT f1_xpexgALT a_cxp i1_xpexgALT f1_xpexgALT f0_xpexgALT i1_xpexgALT a_sup_set_class a_csn a_cxp a_ciun a_cvv p_syl5eqel $.
$}

$(A one-to-one mapping induces a one-to-one mapping on power sets.  This
       version of ~ f1opw avoids the Axiom of Replacement.  (Contributed by
       Mario Carneiro, 26-Jun-2015.) $)

${
	$v ph A B F a b  $.
	$d a b A  $.
	$d a b B  $.
	$d a b F  $.
	$d a b ph  $.
	f0_f1opw2 $f wff ph $.
	f1_f1opw2 $f class A $.
	f2_f1opw2 $f class B $.
	f3_f1opw2 $f class F $.
	f4_f1opw2 $f set a $.
	f5_f1opw2 $f set b $.
	e0_f1opw2 $e |- ( ph -> F : A -1-1-onto-> B ) $.
	e1_f1opw2 $e |- ( ph -> ( `' F " a ) e. _V ) $.
	e2_f1opw2 $e |- ( ph -> ( F " b ) e. _V ) $.
	p_f1opw2 $p |- ( ph -> ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B ) $= f5_f1opw2 f1_f1opw2 a_cpw f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cmpt p_eqid f3_f1opw2 f5_f1opw2 a_sup_set_class p_imassrn e0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 p_f1ofo f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wf1o f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wfo p_syl f1_f1opw2 f2_f1opw2 f3_f1opw2 p_forn f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wfo f3_f1opw2 a_crn f2_f1opw2 a_wceq p_syl f0_f1opw2 f3_f1opw2 a_crn f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 p_syl5sseq e2_f1opw2 f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 a_cvv p_elpwg f0_f1opw2 f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cvv a_wcel f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 a_cpw a_wcel f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 a_wss a_wb p_syl f0_f1opw2 f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 a_cpw a_wcel f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 a_wss p_mpbird f0_f1opw2 f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f2_f1opw2 a_cpw a_wcel f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel p_adantr f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class p_imassrn f3_f1opw2 p_dfdm4 e0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 p_f1odm f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wf1o f3_f1opw2 a_cdm f1_f1opw2 a_wceq p_syl f0_f1opw2 f3_f1opw2 a_ccnv a_crn f3_f1opw2 a_cdm f1_f1opw2 p_syl5eqr f0_f1opw2 f3_f1opw2 a_ccnv a_crn f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 p_syl5sseq e1_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 a_cvv p_elpwg f0_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_cvv a_wcel f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 a_cpw a_wcel f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 a_wss a_wb p_syl f0_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 a_cpw a_wcel f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 a_wss p_mpbird f0_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel p_adantr e0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 p_f1ofo f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wf1o f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wfo p_syl f4_f1opw2 a_sup_set_class f2_f1opw2 p_elpwi f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_wss f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel p_adantl f1_f1opw2 f2_f1opw2 f4_f1opw2 a_sup_set_class f3_f1opw2 p_foimacnv f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wfo f4_f1opw2 a_sup_set_class f2_f1opw2 a_wss f3_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_cima f4_f1opw2 a_sup_set_class a_wceq f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa p_syl2an f0_f1opw2 f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa a_wa f3_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_cima f4_f1opw2 a_sup_set_class p_eqcomd f5_f1opw2 a_sup_set_class f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f3_f1opw2 p_imaeq2 f5_f1opw2 a_sup_set_class f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_wceq f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f3_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_cima f4_f1opw2 a_sup_set_class p_eqeq2d f0_f1opw2 f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa a_wa f4_f1opw2 a_sup_set_class f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_wceq f5_f1opw2 a_sup_set_class f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_wceq f4_f1opw2 a_sup_set_class f3_f1opw2 f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_cima a_wceq p_syl5ibrcom e0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 p_f1of1 f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wf1o f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wf1 p_syl f5_f1opw2 a_sup_set_class f1_f1opw2 p_elpwi f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f5_f1opw2 a_sup_set_class f1_f1opw2 a_wss f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel p_adantr f1_f1opw2 f2_f1opw2 f5_f1opw2 a_sup_set_class f3_f1opw2 p_f1imacnv f0_f1opw2 f1_f1opw2 f2_f1opw2 f3_f1opw2 a_wf1 f5_f1opw2 a_sup_set_class f1_f1opw2 a_wss f3_f1opw2 a_ccnv f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cima f5_f1opw2 a_sup_set_class a_wceq f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa p_syl2an f0_f1opw2 f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa a_wa f3_f1opw2 a_ccnv f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cima f5_f1opw2 a_sup_set_class p_eqcomd f4_f1opw2 a_sup_set_class f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f3_f1opw2 a_ccnv p_imaeq2 f4_f1opw2 a_sup_set_class f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_wceq f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f3_f1opw2 a_ccnv f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cima f5_f1opw2 a_sup_set_class p_eqeq2d f0_f1opw2 f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa a_wa f5_f1opw2 a_sup_set_class f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_wceq f4_f1opw2 a_sup_set_class f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_wceq f5_f1opw2 a_sup_set_class f3_f1opw2 a_ccnv f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cima a_wceq p_syl5ibrcom f0_f1opw2 f5_f1opw2 a_sup_set_class f1_f1opw2 a_cpw a_wcel f4_f1opw2 a_sup_set_class f2_f1opw2 a_cpw a_wcel a_wa a_wa f5_f1opw2 a_sup_set_class f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima a_wceq f4_f1opw2 a_sup_set_class f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_wceq p_impbid f0_f1opw2 f5_f1opw2 f4_f1opw2 f1_f1opw2 a_cpw f2_f1opw2 a_cpw f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima f3_f1opw2 a_ccnv f4_f1opw2 a_sup_set_class a_cima f5_f1opw2 f1_f1opw2 a_cpw f3_f1opw2 f5_f1opw2 a_sup_set_class a_cima a_cmpt p_f1o2d $.
$}

$(A one-to-one mapping induces a one-to-one mapping on power sets.
       (Contributed by Stefan O'Rear, 18-Nov-2014.)  (Revised by Mario
       Carneiro, 26-Jun-2015.) $)

${
	$v A B F b  $.
	$d a b A  $.
	$d a b B  $.
	$d a b F  $.
	f0_f1opw $f class A $.
	f1_f1opw $f class B $.
	f2_f1opw $f class F $.
	f3_f1opw $f set b $.
	i0_f1opw $f set a $.
	p_f1opw $p |- ( F : A -1-1-onto-> B -> ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B ) $= f0_f1opw f1_f1opw f2_f1opw a_wf1o p_id f0_f1opw f1_f1opw f2_f1opw p_dff1o3 f0_f1opw f1_f1opw f2_f1opw a_wf1o f0_f1opw f1_f1opw f2_f1opw a_wfo f2_f1opw a_ccnv a_wfun p_simprbi i0_f1opw p_vex f2_f1opw a_ccnv i0_f1opw a_sup_set_class p_funimaex f0_f1opw f1_f1opw f2_f1opw a_wf1o f2_f1opw a_ccnv a_wfun f2_f1opw a_ccnv i0_f1opw a_sup_set_class a_cima a_cvv a_wcel p_syl f0_f1opw f1_f1opw f2_f1opw p_f1ofun f3_f1opw p_vex f2_f1opw f3_f1opw a_sup_set_class p_funimaex f0_f1opw f1_f1opw f2_f1opw a_wf1o f2_f1opw a_wfun f2_f1opw f3_f1opw a_sup_set_class a_cima a_cvv a_wcel p_syl f0_f1opw f1_f1opw f2_f1opw a_wf1o f0_f1opw f1_f1opw f2_f1opw i0_f1opw f3_f1opw p_f1opw2 $.
$}

$(Show that the support of a function is contained in a set.  (Contributed
       by Mario Carneiro, 19-Dec-2014.)  (Revised by Mario Carneiro,
       22-Mar-2015.) $)

${
	$v ph A B k W Z  $.
	$d k A  $.
	$d B  $.
	$d k ph  $.
	$d k W  $.
	$d k Z  $.
	f0_suppss2 $f wff ph $.
	f1_suppss2 $f class A $.
	f2_suppss2 $f class B $.
	f3_suppss2 $f set k $.
	f4_suppss2 $f class W $.
	f5_suppss2 $f class Z $.
	e0_suppss2 $e |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z ) $.
	p_suppss2 $p |- ( ph -> ( `' ( k e. A |-> B ) " ( _V \ { Z } ) ) C_ W ) $= f3_suppss2 f1_suppss2 f2_suppss2 a_cmpt p_eqid f3_suppss2 f1_suppss2 f2_suppss2 a_cvv f5_suppss2 a_csn a_cdif f3_suppss2 f1_suppss2 f2_suppss2 a_cmpt p_mptpreima f2_suppss2 a_cvv f5_suppss2 p_eldifsni f3_suppss2 a_sup_set_class f1_suppss2 f4_suppss2 p_eldif e0_suppss2 f3_suppss2 a_sup_set_class f1_suppss2 a_wcel f3_suppss2 a_sup_set_class f4_suppss2 a_wcel a_wn a_wa f0_suppss2 f3_suppss2 a_sup_set_class f1_suppss2 f4_suppss2 a_cdif a_wcel f2_suppss2 f5_suppss2 a_wceq p_sylan2br f0_suppss2 f3_suppss2 a_sup_set_class f1_suppss2 a_wcel f3_suppss2 a_sup_set_class f4_suppss2 a_wcel a_wn f2_suppss2 f5_suppss2 a_wceq p_expr f0_suppss2 f3_suppss2 a_sup_set_class f1_suppss2 a_wcel a_wa f3_suppss2 a_sup_set_class f4_suppss2 a_wcel f2_suppss2 f5_suppss2 p_necon1ad f2_suppss2 a_cvv f5_suppss2 a_csn a_cdif a_wcel f2_suppss2 f5_suppss2 a_wne f0_suppss2 f3_suppss2 a_sup_set_class f1_suppss2 a_wcel a_wa f3_suppss2 a_sup_set_class f4_suppss2 a_wcel p_syl5 f0_suppss2 f3_suppss2 a_sup_set_class f1_suppss2 a_wcel f2_suppss2 a_cvv f5_suppss2 a_csn a_cdif a_wcel f3_suppss2 a_sup_set_class f4_suppss2 a_wcel p_3impia f0_suppss2 f2_suppss2 a_cvv f5_suppss2 a_csn a_cdif a_wcel f3_suppss2 f1_suppss2 f4_suppss2 p_rabssdv f0_suppss2 f3_suppss2 f1_suppss2 f2_suppss2 a_cmpt a_ccnv a_cvv f5_suppss2 a_csn a_cdif a_cima f2_suppss2 a_cvv f5_suppss2 a_csn a_cdif a_wcel f3_suppss2 f1_suppss2 a_crab f4_suppss2 p_syl5eqss $.
$}

$(Formula building theorem for support restriction, on a function which
       preserves zero.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)

${
	$v ph x A D F L V Y Z  $.
	$d ph x  $.
	$d Y x  $.
	$d Z x  $.
	f0_suppssfv $f wff ph $.
	f1_suppssfv $f set x $.
	f2_suppssfv $f class A $.
	f3_suppssfv $f class D $.
	f4_suppssfv $f class F $.
	f5_suppssfv $f class L $.
	f6_suppssfv $f class V $.
	f7_suppssfv $f class Y $.
	f8_suppssfv $f class Z $.
	e0_suppssfv $e |- ( ph -> ( `' ( x e. D |-> A ) " ( _V \ { Y } ) ) C_ L ) $.
	e1_suppssfv $e |- ( ph -> ( F ` Y ) = Z ) $.
	e2_suppssfv $e |- ( ( ph /\ x e. D ) -> A e. V ) $.
	p_suppssfv $p |- ( ph -> ( `' ( x e. D |-> ( F ` A ) ) " ( _V \ { Z } ) ) C_ L ) $= f2_suppssfv f4_suppssfv a_cfv a_cvv f8_suppssfv p_eldifsni e2_suppssfv f2_suppssfv f6_suppssfv p_elex f0_suppssfv f1_suppssfv a_sup_set_class f3_suppssfv a_wcel a_wa f2_suppssfv f6_suppssfv a_wcel f2_suppssfv a_cvv a_wcel p_syl f0_suppssfv f1_suppssfv a_sup_set_class f3_suppssfv a_wcel a_wa f2_suppssfv a_cvv a_wcel f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wne p_adantr e1_suppssfv f2_suppssfv f7_suppssfv f4_suppssfv p_fveq2 f2_suppssfv f7_suppssfv a_wceq f2_suppssfv f4_suppssfv a_cfv f7_suppssfv f4_suppssfv a_cfv f8_suppssfv p_eqeq1d f0_suppssfv f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wceq f2_suppssfv f7_suppssfv a_wceq f7_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wceq p_syl5ibrcom f0_suppssfv f2_suppssfv f7_suppssfv f2_suppssfv f4_suppssfv a_cfv f8_suppssfv p_necon3d f0_suppssfv f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wne f2_suppssfv f7_suppssfv a_wne a_wi f1_suppssfv a_sup_set_class f3_suppssfv a_wcel p_adantr f0_suppssfv f1_suppssfv a_sup_set_class f3_suppssfv a_wcel a_wa f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wne f2_suppssfv f7_suppssfv a_wne p_imp f2_suppssfv a_cvv f7_suppssfv p_eldifsn f0_suppssfv f1_suppssfv a_sup_set_class f3_suppssfv a_wcel a_wa f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wne a_wa f2_suppssfv a_cvv a_wcel f2_suppssfv f7_suppssfv a_wne f2_suppssfv a_cvv f7_suppssfv a_csn a_cdif a_wcel p_sylanbrc f0_suppssfv f1_suppssfv a_sup_set_class f3_suppssfv a_wcel a_wa f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wne f2_suppssfv a_cvv f7_suppssfv a_csn a_cdif a_wcel p_ex f2_suppssfv f4_suppssfv a_cfv a_cvv f8_suppssfv a_csn a_cdif a_wcel f2_suppssfv f4_suppssfv a_cfv f8_suppssfv a_wne f0_suppssfv f1_suppssfv a_sup_set_class f3_suppssfv a_wcel a_wa f2_suppssfv a_cvv f7_suppssfv a_csn a_cdif a_wcel p_syl5 f0_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cvv f8_suppssfv a_csn a_cdif a_wcel f2_suppssfv a_cvv f7_suppssfv a_csn a_cdif a_wcel f1_suppssfv f3_suppssfv p_ss2rabdv f1_suppssfv f3_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cmpt p_eqid f1_suppssfv f3_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cvv f8_suppssfv a_csn a_cdif f1_suppssfv f3_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cmpt p_mptpreima f1_suppssfv f3_suppssfv f2_suppssfv a_cmpt p_eqid f1_suppssfv f3_suppssfv f2_suppssfv a_cvv f7_suppssfv a_csn a_cdif f1_suppssfv f3_suppssfv f2_suppssfv a_cmpt p_mptpreima f0_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cvv f8_suppssfv a_csn a_cdif a_wcel f1_suppssfv f3_suppssfv a_crab f2_suppssfv a_cvv f7_suppssfv a_csn a_cdif a_wcel f1_suppssfv f3_suppssfv a_crab f1_suppssfv f3_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cmpt a_ccnv a_cvv f8_suppssfv a_csn a_cdif a_cima f1_suppssfv f3_suppssfv f2_suppssfv a_cmpt a_ccnv a_cvv f7_suppssfv a_csn a_cdif a_cima p_3sstr4g e0_suppssfv f0_suppssfv f1_suppssfv f3_suppssfv f2_suppssfv f4_suppssfv a_cfv a_cmpt a_ccnv a_cvv f8_suppssfv a_csn a_cdif a_cima f1_suppssfv f3_suppssfv f2_suppssfv a_cmpt a_ccnv a_cvv f7_suppssfv a_csn a_cdif a_cima f5_suppssfv p_sstrd $.
$}

$(Formula building theorem for support restrictions: operator with left
       annihilator.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)

${
	$v ph x v A B D R L O V Y Z  $.
	$d ph v  $.
	$d ph x  $.
	$d B v  $.
	$d O v  $.
	$d R v  $.
	$d Y v  $.
	$d Y x  $.
	$d Z v  $.
	$d Z x  $.
	f0_suppssov1 $f wff ph $.
	f1_suppssov1 $f set x $.
	f2_suppssov1 $f set v $.
	f3_suppssov1 $f class A $.
	f4_suppssov1 $f class B $.
	f5_suppssov1 $f class D $.
	f6_suppssov1 $f class R $.
	f7_suppssov1 $f class L $.
	f8_suppssov1 $f class O $.
	f9_suppssov1 $f class V $.
	f10_suppssov1 $f class Y $.
	f11_suppssov1 $f class Z $.
	e0_suppssov1 $e |- ( ph -> ( `' ( x e. D |-> A ) " ( _V \ { Y } ) ) C_ L ) $.
	e1_suppssov1 $e |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z ) $.
	e2_suppssov1 $e |- ( ( ph /\ x e. D ) -> A e. V ) $.
	e3_suppssov1 $e |- ( ( ph /\ x e. D ) -> B e. R ) $.
	p_suppssov1 $p |- ( ph -> ( `' ( x e. D |-> ( A O B ) ) " ( _V \ { Z } ) ) C_ L ) $= e2_suppssov1 f3_suppssov1 f9_suppssov1 p_elex f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f9_suppssov1 a_wcel f3_suppssov1 a_cvv a_wcel p_syl f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 a_cvv a_wcel f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel p_adantr f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 p_eldifsni e3_suppssov1 e1_suppssov1 f0_suppssov1 f10_suppssov1 f2_suppssov1 a_sup_set_class f8_suppssov1 a_co f11_suppssov1 a_wceq f2_suppssov1 f6_suppssov1 p_ralrimiva f0_suppssov1 f10_suppssov1 f2_suppssov1 a_sup_set_class f8_suppssov1 a_co f11_suppssov1 a_wceq f2_suppssov1 f6_suppssov1 a_wral f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel p_adantr f2_suppssov1 a_sup_set_class f4_suppssov1 f10_suppssov1 f8_suppssov1 p_oveq2 f2_suppssov1 a_sup_set_class f4_suppssov1 a_wceq f10_suppssov1 f2_suppssov1 a_sup_set_class f8_suppssov1 a_co f10_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 p_eqeq1d f10_suppssov1 f2_suppssov1 a_sup_set_class f8_suppssov1 a_co f11_suppssov1 a_wceq f10_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 a_wceq f2_suppssov1 f4_suppssov1 f6_suppssov1 p_rspcva f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f4_suppssov1 f6_suppssov1 a_wcel f10_suppssov1 f2_suppssov1 a_sup_set_class f8_suppssov1 a_co f11_suppssov1 a_wceq f2_suppssov1 f6_suppssov1 a_wral f10_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 a_wceq p_syl2anc f3_suppssov1 f10_suppssov1 f4_suppssov1 f8_suppssov1 p_oveq1 f3_suppssov1 f10_suppssov1 a_wceq f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co f10_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 p_eqeq1d f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 a_wceq f3_suppssov1 f10_suppssov1 a_wceq f10_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 a_wceq p_syl5ibrcom f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f10_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 p_necon3d f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co f11_suppssov1 a_wne f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f10_suppssov1 a_wne p_syl5 f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel f3_suppssov1 f10_suppssov1 a_wne p_imp f3_suppssov1 a_cvv f10_suppssov1 p_eldifsn f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel a_wa f3_suppssov1 a_cvv a_wcel f3_suppssov1 f10_suppssov1 a_wne f3_suppssov1 a_cvv f10_suppssov1 a_csn a_cdif a_wcel p_sylanbrc f0_suppssov1 f1_suppssov1 a_sup_set_class f5_suppssov1 a_wcel a_wa f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel f3_suppssov1 a_cvv f10_suppssov1 a_csn a_cdif a_wcel p_ex f0_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel f3_suppssov1 a_cvv f10_suppssov1 a_csn a_cdif a_wcel f1_suppssov1 f5_suppssov1 p_ss2rabdv f1_suppssov1 f5_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cmpt p_eqid f1_suppssov1 f5_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif f1_suppssov1 f5_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cmpt p_mptpreima f1_suppssov1 f5_suppssov1 f3_suppssov1 a_cmpt p_eqid f1_suppssov1 f5_suppssov1 f3_suppssov1 a_cvv f10_suppssov1 a_csn a_cdif f1_suppssov1 f5_suppssov1 f3_suppssov1 a_cmpt p_mptpreima f0_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cvv f11_suppssov1 a_csn a_cdif a_wcel f1_suppssov1 f5_suppssov1 a_crab f3_suppssov1 a_cvv f10_suppssov1 a_csn a_cdif a_wcel f1_suppssov1 f5_suppssov1 a_crab f1_suppssov1 f5_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cmpt a_ccnv a_cvv f11_suppssov1 a_csn a_cdif a_cima f1_suppssov1 f5_suppssov1 f3_suppssov1 a_cmpt a_ccnv a_cvv f10_suppssov1 a_csn a_cdif a_cima p_3sstr4g e0_suppssov1 f0_suppssov1 f1_suppssov1 f5_suppssov1 f3_suppssov1 f4_suppssov1 f8_suppssov1 a_co a_cmpt a_ccnv a_cvv f11_suppssov1 a_csn a_cdif a_cima f1_suppssov1 f5_suppssov1 f3_suppssov1 a_cmpt a_ccnv a_cvv f10_suppssov1 a_csn a_cdif a_cima f7_suppssov1 p_sstrd $.
$}


