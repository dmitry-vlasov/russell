$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Operations.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        "Maps to" notation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( If a two-parameter class is not empty, constrain the implicit pair.
       (Contributed by Stefan O'Rear, 7-Mar-2015.) $)
${
	$d A x y z $.
	$d B x y z $.
	$d C z $.
	ielmpt2cl_0 $f set z $.
	felmpt2cl_0 $f set x $.
	felmpt2cl_1 $f set y $.
	felmpt2cl_2 $f class A $.
	felmpt2cl_3 $f class B $.
	felmpt2cl_4 $f class C $.
	felmpt2cl_5 $f class S $.
	felmpt2cl_6 $f class T $.
	felmpt2cl_7 $f class F $.
	felmpt2cl_8 $f class X $.
	eelmpt2cl_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	elmpt2cl $p |- ( X e. ( S F T ) -> ( S e. A /\ T e. B ) ) $= felmpt2cl_8 felmpt2cl_5 felmpt2cl_6 felmpt2cl_7 co wcel felmpt2cl_5 felmpt2cl_6 cop felmpt2cl_2 felmpt2cl_3 cxp wcel felmpt2cl_5 felmpt2cl_2 wcel felmpt2cl_6 felmpt2cl_3 wcel wa felmpt2cl_8 felmpt2cl_5 felmpt2cl_6 felmpt2cl_7 co wcel felmpt2cl_7 cdm felmpt2cl_2 felmpt2cl_3 cxp felmpt2cl_5 felmpt2cl_6 cop felmpt2cl_7 cdm felmpt2cl_0 sup_set_class felmpt2cl_2 wcel felmpt2cl_1 sup_set_class felmpt2cl_3 wcel wa ielmpt2cl_0 sup_set_class felmpt2cl_4 wceq wa felmpt2cl_0 felmpt2cl_1 ielmpt2cl_0 coprab cdm felmpt2cl_2 felmpt2cl_3 cxp felmpt2cl_7 felmpt2cl_0 sup_set_class felmpt2cl_2 wcel felmpt2cl_1 sup_set_class felmpt2cl_3 wcel wa ielmpt2cl_0 sup_set_class felmpt2cl_4 wceq wa felmpt2cl_0 felmpt2cl_1 ielmpt2cl_0 coprab felmpt2cl_7 felmpt2cl_0 felmpt2cl_1 felmpt2cl_2 felmpt2cl_3 felmpt2cl_4 cmpt2 felmpt2cl_0 sup_set_class felmpt2cl_2 wcel felmpt2cl_1 sup_set_class felmpt2cl_3 wcel wa ielmpt2cl_0 sup_set_class felmpt2cl_4 wceq wa felmpt2cl_0 felmpt2cl_1 ielmpt2cl_0 coprab eelmpt2cl_0 felmpt2cl_0 felmpt2cl_1 ielmpt2cl_0 felmpt2cl_2 felmpt2cl_3 felmpt2cl_4 df-mpt2 eqtri dmeqi ielmpt2cl_0 sup_set_class felmpt2cl_4 wceq felmpt2cl_0 felmpt2cl_1 ielmpt2cl_0 felmpt2cl_2 felmpt2cl_3 dmoprabss eqsstri felmpt2cl_5 felmpt2cl_6 cop felmpt2cl_7 cdm wcel felmpt2cl_8 felmpt2cl_5 felmpt2cl_6 cop felmpt2cl_7 cfv felmpt2cl_5 felmpt2cl_6 felmpt2cl_7 co felmpt2cl_8 felmpt2cl_5 felmpt2cl_6 cop felmpt2cl_7 elfvdm felmpt2cl_5 felmpt2cl_6 felmpt2cl_7 df-ov eleq2s sseldi felmpt2cl_5 felmpt2cl_6 felmpt2cl_2 felmpt2cl_3 opelxp sylib $.
$}
$( If a two-parameter class is not empty, the first argument is in its
       nominal domain.  (Contributed by FL, 15-Oct-2012.)  (Revised by Stefan
       O'Rear, 7-Mar-2015.) $)
${
	$d A x y $.
	$d B x y $.
	felmpt2cl1_0 $f set x $.
	felmpt2cl1_1 $f set y $.
	felmpt2cl1_2 $f class A $.
	felmpt2cl1_3 $f class B $.
	felmpt2cl1_4 $f class C $.
	felmpt2cl1_5 $f class S $.
	felmpt2cl1_6 $f class T $.
	felmpt2cl1_7 $f class F $.
	felmpt2cl1_8 $f class X $.
	eelmpt2cl1_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	elmpt2cl1 $p |- ( X e. ( S F T ) -> S e. A ) $= felmpt2cl1_8 felmpt2cl1_5 felmpt2cl1_6 felmpt2cl1_7 co wcel felmpt2cl1_5 felmpt2cl1_2 wcel felmpt2cl1_6 felmpt2cl1_3 wcel felmpt2cl1_0 felmpt2cl1_1 felmpt2cl1_2 felmpt2cl1_3 felmpt2cl1_4 felmpt2cl1_5 felmpt2cl1_6 felmpt2cl1_7 felmpt2cl1_8 eelmpt2cl1_0 elmpt2cl simpld $.
$}
$( If a two-parameter class is not empty, the second argument is in its
       nominal domain.  (Contributed by FL, 15-Oct-2012.)  (Revised by Stefan
       O'Rear, 7-Mar-2015.) $)
${
	$d A x y $.
	$d B x y $.
	felmpt2cl2_0 $f set x $.
	felmpt2cl2_1 $f set y $.
	felmpt2cl2_2 $f class A $.
	felmpt2cl2_3 $f class B $.
	felmpt2cl2_4 $f class C $.
	felmpt2cl2_5 $f class S $.
	felmpt2cl2_6 $f class T $.
	felmpt2cl2_7 $f class F $.
	felmpt2cl2_8 $f class X $.
	eelmpt2cl2_0 $e |- F = ( x e. A , y e. B |-> C ) $.
	elmpt2cl2 $p |- ( X e. ( S F T ) -> T e. B ) $= felmpt2cl2_8 felmpt2cl2_5 felmpt2cl2_6 felmpt2cl2_7 co wcel felmpt2cl2_5 felmpt2cl2_2 wcel felmpt2cl2_6 felmpt2cl2_3 wcel felmpt2cl2_0 felmpt2cl2_1 felmpt2cl2_2 felmpt2cl2_3 felmpt2cl2_4 felmpt2cl2_5 felmpt2cl2_6 felmpt2cl2_7 felmpt2cl2_8 eelmpt2cl2_0 elmpt2cl simprd $.
$}
$( Utility lemma for two-parameter classes.

       _EDITORIAL_: can simplify ~ isghm , ~ islmhm .  (Contributed by Stefan
       O'Rear, 21-Jan-2015.) $)
${
	$d A a b $.
	$d B a b $.
	$d E a b $.
	$d F a b $.
	$d X a b $.
	$d Y a b $.
	$d a b $.
	felovmpt2_0 $f class A $.
	felovmpt2_1 $f class B $.
	felovmpt2_2 $f class C $.
	felovmpt2_3 $f class D $.
	felovmpt2_4 $f class E $.
	felovmpt2_5 $f class F $.
	felovmpt2_6 $f class X $.
	felovmpt2_7 $f class Y $.
	felovmpt2_8 $f set a $.
	felovmpt2_9 $f set b $.
	eelovmpt2_0 $e |- D = ( a e. A , b e. B |-> C ) $.
	eelovmpt2_1 $e |- C e. _V $.
	eelovmpt2_2 $e |- ( ( a = X /\ b = Y ) -> C = E ) $.
	elovmpt2 $p |- ( F e. ( X D Y ) <-> ( X e. A /\ Y e. B /\ F e. E ) ) $= felovmpt2_5 felovmpt2_6 felovmpt2_7 felovmpt2_3 co wcel felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel wa felovmpt2_5 felovmpt2_4 wcel wa felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel felovmpt2_5 felovmpt2_4 wcel w3a felovmpt2_5 felovmpt2_6 felovmpt2_7 felovmpt2_3 co wcel felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel wa felovmpt2_5 felovmpt2_4 wcel felovmpt2_8 felovmpt2_9 felovmpt2_0 felovmpt2_1 felovmpt2_2 felovmpt2_6 felovmpt2_7 felovmpt2_3 felovmpt2_5 eelovmpt2_0 elmpt2cl felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel wa felovmpt2_6 felovmpt2_7 felovmpt2_3 co felovmpt2_4 felovmpt2_5 felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel felovmpt2_4 cvv wcel felovmpt2_6 felovmpt2_7 felovmpt2_3 co felovmpt2_4 wceq felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel wa felovmpt2_2 cvv wcel felovmpt2_9 wal felovmpt2_8 wal felovmpt2_4 cvv wcel felovmpt2_2 cvv wcel felovmpt2_8 felovmpt2_9 eelovmpt2_1 gen2 felovmpt2_2 cvv wcel felovmpt2_4 cvv wcel felovmpt2_8 felovmpt2_9 felovmpt2_6 felovmpt2_7 felovmpt2_0 felovmpt2_1 felovmpt2_8 sup_set_class felovmpt2_6 wceq felovmpt2_9 sup_set_class felovmpt2_7 wceq wa felovmpt2_2 felovmpt2_4 cvv eelovmpt2_2 eleq1d spc2gv mpi felovmpt2_8 felovmpt2_9 felovmpt2_6 felovmpt2_7 felovmpt2_0 felovmpt2_1 felovmpt2_2 felovmpt2_4 felovmpt2_3 cvv eelovmpt2_2 eelovmpt2_0 ovmpt2ga mpd3an3 eleq2d biadan2 felovmpt2_6 felovmpt2_0 wcel felovmpt2_7 felovmpt2_1 wcel felovmpt2_5 felovmpt2_4 wcel df-3an bitr4i $.
$}
$( Any function to sets of ordered pairs produces a relation on function
       value unconditionally.  (Contributed by Mario Carneiro, 7-Aug-2014.)
       (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)
${
	$d x A $.
	frelmptopab_0 $f wff ph $.
	frelmptopab_1 $f set x $.
	frelmptopab_2 $f set y $.
	frelmptopab_3 $f set z $.
	frelmptopab_4 $f class A $.
	frelmptopab_5 $f class B $.
	frelmptopab_6 $f class F $.
	erelmptopab_0 $e |- F = ( x e. A |-> { <. y , z >. | ph } ) $.
	relmptopab $p |- Rel ( F ` B ) $= frelmptopab_5 frelmptopab_6 cfv wrel frelmptopab_5 frelmptopab_6 cfv cvv cvv cxp wss frelmptopab_0 frelmptopab_2 frelmptopab_3 copab cvv cvv cxp wss frelmptopab_5 frelmptopab_6 cfv cvv cvv cxp wss frelmptopab_1 frelmptopab_4 frelmptopab_1 frelmptopab_4 frelmptopab_0 frelmptopab_2 frelmptopab_3 copab cvv cvv cxp frelmptopab_5 frelmptopab_6 erelmptopab_0 fvmptss frelmptopab_0 frelmptopab_2 frelmptopab_3 copab cvv cvv cxp wss frelmptopab_1 sup_set_class frelmptopab_4 wcel frelmptopab_0 frelmptopab_2 frelmptopab_3 copab wrel frelmptopab_0 frelmptopab_2 frelmptopab_3 copab cvv cvv cxp wss frelmptopab_0 frelmptopab_2 frelmptopab_3 relopab frelmptopab_0 frelmptopab_2 frelmptopab_3 copab df-rel mpbi a1i mprg frelmptopab_5 frelmptopab_6 cfv df-rel mpbir $.
$}
$( Describe an implicit one-to-one onto function.  (Contributed by Mario
         Carneiro, 30-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d y C $.
	$d x D $.
	$d x y ph $.
	ff1ocnvd_0 $f wff ph $.
	ff1ocnvd_1 $f set x $.
	ff1ocnvd_2 $f set y $.
	ff1ocnvd_3 $f class A $.
	ff1ocnvd_4 $f class B $.
	ff1ocnvd_5 $f class C $.
	ff1ocnvd_6 $f class D $.
	ff1ocnvd_7 $f class F $.
	ff1ocnvd_8 $f class W $.
	ff1ocnvd_9 $f class X $.
	ef1ocnvd_0 $e |- F = ( x e. A |-> C ) $.
	ef1ocnvd_1 $e |- ( ( ph /\ x e. A ) -> C e. W ) $.
	ef1ocnvd_2 $e |- ( ( ph /\ y e. B ) -> D e. X ) $.
	ef1ocnvd_3 $e |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) ) $.
	f1ocnvd $p |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $= ff1ocnvd_0 ff1ocnvd_3 ff1ocnvd_4 ff1ocnvd_7 wf1o ff1ocnvd_7 ccnv ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt wceq ff1ocnvd_0 ff1ocnvd_7 ff1ocnvd_3 wfn ff1ocnvd_7 ccnv ff1ocnvd_4 wfn ff1ocnvd_3 ff1ocnvd_4 ff1ocnvd_7 wf1o ff1ocnvd_0 ff1ocnvd_5 ff1ocnvd_8 wcel ff1ocnvd_1 ff1ocnvd_3 wral ff1ocnvd_7 ff1ocnvd_3 wfn ff1ocnvd_0 ff1ocnvd_5 ff1ocnvd_8 wcel ff1ocnvd_1 ff1ocnvd_3 ef1ocnvd_1 ralrimiva ff1ocnvd_1 ff1ocnvd_3 ff1ocnvd_5 ff1ocnvd_7 ff1ocnvd_8 ef1ocnvd_0 fnmpt syl ff1ocnvd_0 ff1ocnvd_7 ccnv ff1ocnvd_4 wfn ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt ff1ocnvd_4 wfn ff1ocnvd_0 ff1ocnvd_6 ff1ocnvd_9 wcel ff1ocnvd_2 ff1ocnvd_4 wral ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt ff1ocnvd_4 wfn ff1ocnvd_0 ff1ocnvd_6 ff1ocnvd_9 wcel ff1ocnvd_2 ff1ocnvd_4 ef1ocnvd_2 ralrimiva ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt ff1ocnvd_9 ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt eqid fnmpt syl ff1ocnvd_0 ff1ocnvd_4 ff1ocnvd_7 ccnv ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt ff1ocnvd_0 ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_2 ff1ocnvd_1 copab ff1ocnvd_2 sup_set_class ff1ocnvd_4 wcel ff1ocnvd_1 sup_set_class ff1ocnvd_6 wceq wa ff1ocnvd_2 ff1ocnvd_1 copab ff1ocnvd_7 ccnv ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt ff1ocnvd_0 ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_2 sup_set_class ff1ocnvd_4 wcel ff1ocnvd_1 sup_set_class ff1ocnvd_6 wceq wa ff1ocnvd_2 ff1ocnvd_1 ef1ocnvd_3 opabbidv ff1ocnvd_7 ccnv ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 copab ccnv ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_2 ff1ocnvd_1 copab ff1ocnvd_7 ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 copab ff1ocnvd_7 ff1ocnvd_1 ff1ocnvd_3 ff1ocnvd_5 cmpt ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 copab ef1ocnvd_0 ff1ocnvd_1 ff1ocnvd_2 ff1ocnvd_3 ff1ocnvd_5 df-mpt eqtri cnveqi ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 cnvopab eqtri ff1ocnvd_2 ff1ocnvd_1 ff1ocnvd_4 ff1ocnvd_6 df-mpt 3eqtr4g fneq1d mpbird ff1ocnvd_3 ff1ocnvd_4 ff1ocnvd_7 dff1o4 sylanbrc ff1ocnvd_0 ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_2 ff1ocnvd_1 copab ff1ocnvd_2 sup_set_class ff1ocnvd_4 wcel ff1ocnvd_1 sup_set_class ff1ocnvd_6 wceq wa ff1ocnvd_2 ff1ocnvd_1 copab ff1ocnvd_7 ccnv ff1ocnvd_2 ff1ocnvd_4 ff1ocnvd_6 cmpt ff1ocnvd_0 ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_2 sup_set_class ff1ocnvd_4 wcel ff1ocnvd_1 sup_set_class ff1ocnvd_6 wceq wa ff1ocnvd_2 ff1ocnvd_1 ef1ocnvd_3 opabbidv ff1ocnvd_7 ccnv ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 copab ccnv ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_2 ff1ocnvd_1 copab ff1ocnvd_7 ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 copab ff1ocnvd_7 ff1ocnvd_1 ff1ocnvd_3 ff1ocnvd_5 cmpt ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 copab ef1ocnvd_0 ff1ocnvd_1 ff1ocnvd_2 ff1ocnvd_3 ff1ocnvd_5 df-mpt eqtri cnveqi ff1ocnvd_1 sup_set_class ff1ocnvd_3 wcel ff1ocnvd_2 sup_set_class ff1ocnvd_5 wceq wa ff1ocnvd_1 ff1ocnvd_2 cnvopab eqtri ff1ocnvd_2 ff1ocnvd_1 ff1ocnvd_4 ff1ocnvd_6 df-mpt 3eqtr4g jca $.
$}
$( Describe an implicit one-to-one onto function.  (Contributed by Mario
         Carneiro, 12-May-2014.) $)
${
	$d x y A $.
	$d x y B $.
	$d y C $.
	$d x D $.
	$d x y ph $.
	ff1od_0 $f wff ph $.
	ff1od_1 $f set x $.
	ff1od_2 $f set y $.
	ff1od_3 $f class A $.
	ff1od_4 $f class B $.
	ff1od_5 $f class C $.
	ff1od_6 $f class D $.
	ff1od_7 $f class F $.
	ff1od_8 $f class W $.
	ff1od_9 $f class X $.
	ef1od_0 $e |- F = ( x e. A |-> C ) $.
	ef1od_1 $e |- ( ( ph /\ x e. A ) -> C e. W ) $.
	ef1od_2 $e |- ( ( ph /\ y e. B ) -> D e. X ) $.
	ef1od_3 $e |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) ) $.
	f1od $p |- ( ph -> F : A -1-1-onto-> B ) $= ff1od_0 ff1od_3 ff1od_4 ff1od_7 wf1o ff1od_7 ccnv ff1od_2 ff1od_4 ff1od_6 cmpt wceq ff1od_0 ff1od_1 ff1od_2 ff1od_3 ff1od_4 ff1od_5 ff1od_6 ff1od_7 ff1od_8 ff1od_9 ef1od_0 ef1od_1 ef1od_2 ef1od_3 f1ocnvd simpld $.
$}
$( Describe an implicit one-to-one onto function.  (Contributed by Mario
       Carneiro, 30-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d y C $.
	$d x D $.
	$d x y ph $.
	ff1ocnv2d_0 $f wff ph $.
	ff1ocnv2d_1 $f set x $.
	ff1ocnv2d_2 $f set y $.
	ff1ocnv2d_3 $f class A $.
	ff1ocnv2d_4 $f class B $.
	ff1ocnv2d_5 $f class C $.
	ff1ocnv2d_6 $f class D $.
	ff1ocnv2d_7 $f class F $.
	ef1ocnv2d_0 $e |- F = ( x e. A |-> C ) $.
	ef1ocnv2d_1 $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
	ef1ocnv2d_2 $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
	ef1ocnv2d_3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) ) $.
	f1ocnv2d $p |- ( ph -> ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $= ff1ocnv2d_0 ff1ocnv2d_1 ff1ocnv2d_2 ff1ocnv2d_3 ff1ocnv2d_4 ff1ocnv2d_5 ff1ocnv2d_6 ff1ocnv2d_7 ff1ocnv2d_4 ff1ocnv2d_3 ef1ocnv2d_0 ef1ocnv2d_1 ef1ocnv2d_2 ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq wa ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq wa ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq wa wa ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel wa ff1ocnv2d_5 ff1ocnv2d_4 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel wi ef1ocnv2d_1 ff1ocnv2d_5 ff1ocnv2d_4 ff1ocnv2d_2 sup_set_class eleq1a syl impr ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq wi ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel wa wa ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ef1ocnv2d_3 biimpar exp42 com34 imp32 jcai ff1ocnv2d_0 ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq wa wa ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_0 ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_0 ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel wa ff1ocnv2d_6 ff1ocnv2d_3 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel wi ef1ocnv2d_2 ff1ocnv2d_6 ff1ocnv2d_3 ff1ocnv2d_1 sup_set_class eleq1a syl impr ff1ocnv2d_0 ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq wi ff1ocnv2d_0 ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq wi ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ff1ocnv2d_0 ff1ocnv2d_1 sup_set_class ff1ocnv2d_3 wcel ff1ocnv2d_2 sup_set_class ff1ocnv2d_4 wcel wa wa ff1ocnv2d_1 sup_set_class ff1ocnv2d_6 wceq ff1ocnv2d_2 sup_set_class ff1ocnv2d_5 wceq ef1ocnv2d_3 biimpa exp42 com23 com34 imp32 jcai impbida f1ocnvd $.
$}
$( Describe an implicit one-to-one onto function.  (Contributed by Mario
       Carneiro, 12-May-2014.) $)
${
	$d x y A $.
	$d x y B $.
	$d y C $.
	$d x D $.
	$d x y ph $.
	ff1o2d_0 $f wff ph $.
	ff1o2d_1 $f set x $.
	ff1o2d_2 $f set y $.
	ff1o2d_3 $f class A $.
	ff1o2d_4 $f class B $.
	ff1o2d_5 $f class C $.
	ff1o2d_6 $f class D $.
	ff1o2d_7 $f class F $.
	ef1o2d_0 $e |- F = ( x e. A |-> C ) $.
	ef1o2d_1 $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
	ef1o2d_2 $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
	ef1o2d_3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( x = D <-> y = C ) ) $.
	f1o2d $p |- ( ph -> F : A -1-1-onto-> B ) $= ff1o2d_0 ff1o2d_3 ff1o2d_4 ff1o2d_7 wf1o ff1o2d_7 ccnv ff1o2d_2 ff1o2d_4 ff1o2d_6 cmpt wceq ff1o2d_0 ff1o2d_1 ff1o2d_2 ff1o2d_3 ff1o2d_4 ff1o2d_5 ff1o2d_6 ff1o2d_7 ef1o2d_0 ef1o2d_1 ef1o2d_2 ef1o2d_3 f1ocnv2d simpld $.
$}
$( The cross product of two sets is a set.  Proposition 6.2 of
       [TakeutiZaring] p. 23.  This version is proven using Replacement; see
       ~ xpexg for a version that uses the Power Set axiom instead.
       (Contributed by Mario Carneiro, 20-May-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d A x y $.
	$d B x y $.
	$d V y $.
	ixpexgALT_0 $f set x $.
	ixpexgALT_1 $f set y $.
	fxpexgALT_0 $f class A $.
	fxpexgALT_1 $f class B $.
	fxpexgALT_2 $f class V $.
	fxpexgALT_3 $f class W $.
	xpexgALT $p |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V ) $= fxpexgALT_0 fxpexgALT_2 wcel fxpexgALT_1 fxpexgALT_3 wcel wa fxpexgALT_0 fxpexgALT_1 cxp ixpexgALT_1 fxpexgALT_1 fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp ciun cvv fxpexgALT_0 ixpexgALT_1 fxpexgALT_1 ixpexgALT_1 sup_set_class csn ciun cxp fxpexgALT_0 fxpexgALT_1 cxp ixpexgALT_1 fxpexgALT_1 fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp ciun ixpexgALT_1 fxpexgALT_1 ixpexgALT_1 sup_set_class csn ciun fxpexgALT_1 fxpexgALT_0 ixpexgALT_1 fxpexgALT_1 iunid xpeq2i ixpexgALT_1 fxpexgALT_1 ixpexgALT_1 sup_set_class csn fxpexgALT_0 xpiundi eqtr3i fxpexgALT_1 fxpexgALT_3 wcel fxpexgALT_1 fxpexgALT_3 wcel fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp cvv wcel ixpexgALT_1 fxpexgALT_1 wral ixpexgALT_1 fxpexgALT_1 fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp ciun cvv wcel fxpexgALT_0 fxpexgALT_2 wcel fxpexgALT_1 fxpexgALT_3 wcel id fxpexgALT_0 fxpexgALT_2 wcel fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp cvv wcel ixpexgALT_1 fxpexgALT_1 fxpexgALT_0 fxpexgALT_2 wcel fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp ixpexgALT_0 fxpexgALT_0 ixpexgALT_1 sup_set_class cmpt cvv ixpexgALT_0 fxpexgALT_0 ixpexgALT_1 sup_set_class fconstmpt ixpexgALT_0 fxpexgALT_0 ixpexgALT_1 sup_set_class fxpexgALT_2 mptexg syl5eqel ralrimivw ixpexgALT_1 fxpexgALT_1 fxpexgALT_0 ixpexgALT_1 sup_set_class csn cxp fxpexgALT_3 cvv iunexg syl2anr syl5eqel $.
$}
$( A one-to-one mapping induces a one-to-one mapping on power sets.  This
       version of ~ f1opw avoids the Axiom of Replacement.  (Contributed by
       Mario Carneiro, 26-Jun-2015.) $)
${
	$d a b A $.
	$d a b B $.
	$d a b F $.
	$d a b ph $.
	ff1opw2_0 $f wff ph $.
	ff1opw2_1 $f class A $.
	ff1opw2_2 $f class B $.
	ff1opw2_3 $f class F $.
	ff1opw2_4 $f set a $.
	ff1opw2_5 $f set b $.
	ef1opw2_0 $e |- ( ph -> F : A -1-1-onto-> B ) $.
	ef1opw2_1 $e |- ( ph -> ( `' F " a ) e. _V ) $.
	ef1opw2_2 $e |- ( ph -> ( F " b ) e. _V ) $.
	f1opw2 $p |- ( ph -> ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B ) $= ff1opw2_0 ff1opw2_5 ff1opw2_4 ff1opw2_1 cpw ff1opw2_2 cpw ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_5 ff1opw2_1 cpw ff1opw2_3 ff1opw2_5 sup_set_class cima cmpt ff1opw2_5 ff1opw2_1 cpw ff1opw2_3 ff1opw2_5 sup_set_class cima cmpt eqid ff1opw2_0 ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 cpw wcel ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_0 ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 cpw wcel ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 wss ff1opw2_0 ff1opw2_3 crn ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 ff1opw2_3 ff1opw2_5 sup_set_class imassrn ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wfo ff1opw2_3 crn ff1opw2_2 wceq ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wf1o ff1opw2_1 ff1opw2_2 ff1opw2_3 wfo ef1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 f1ofo syl ff1opw2_1 ff1opw2_2 ff1opw2_3 forn syl syl5sseq ff1opw2_0 ff1opw2_3 ff1opw2_5 sup_set_class cima cvv wcel ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 cpw wcel ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 wss wb ef1opw2_2 ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_2 cvv elpwg syl mpbird adantr ff1opw2_0 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel ff1opw2_0 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 cpw wcel ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 wss ff1opw2_0 ff1opw2_3 ccnv crn ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 ff1opw2_3 ccnv ff1opw2_4 sup_set_class imassrn ff1opw2_0 ff1opw2_3 ccnv crn ff1opw2_3 cdm ff1opw2_1 ff1opw2_3 dfdm4 ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wf1o ff1opw2_3 cdm ff1opw2_1 wceq ef1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 f1odm syl syl5eqr syl5sseq ff1opw2_0 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima cvv wcel ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 cpw wcel ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 wss wb ef1opw2_1 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_1 cvv elpwg syl mpbird adantr ff1opw2_0 ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa wa ff1opw2_5 sup_set_class ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima wceq ff1opw2_4 sup_set_class ff1opw2_3 ff1opw2_5 sup_set_class cima wceq ff1opw2_0 ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa wa ff1opw2_4 sup_set_class ff1opw2_3 ff1opw2_5 sup_set_class cima wceq ff1opw2_5 sup_set_class ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima wceq ff1opw2_4 sup_set_class ff1opw2_3 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima cima wceq ff1opw2_0 ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa wa ff1opw2_3 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima cima ff1opw2_4 sup_set_class ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wfo ff1opw2_4 sup_set_class ff1opw2_2 wss ff1opw2_3 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima cima ff1opw2_4 sup_set_class wceq ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wf1o ff1opw2_1 ff1opw2_2 ff1opw2_3 wfo ef1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 f1ofo syl ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 wss ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 elpwi adantl ff1opw2_1 ff1opw2_2 ff1opw2_4 sup_set_class ff1opw2_3 foimacnv syl2an eqcomd ff1opw2_5 sup_set_class ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima wceq ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_3 ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima cima ff1opw2_4 sup_set_class ff1opw2_5 sup_set_class ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_3 imaeq2 eqeq2d syl5ibrcom ff1opw2_0 ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa wa ff1opw2_5 sup_set_class ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima wceq ff1opw2_4 sup_set_class ff1opw2_3 ff1opw2_5 sup_set_class cima wceq ff1opw2_5 sup_set_class ff1opw2_3 ccnv ff1opw2_3 ff1opw2_5 sup_set_class cima cima wceq ff1opw2_0 ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa wa ff1opw2_3 ccnv ff1opw2_3 ff1opw2_5 sup_set_class cima cima ff1opw2_5 sup_set_class ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wf1 ff1opw2_5 sup_set_class ff1opw2_1 wss ff1opw2_3 ccnv ff1opw2_3 ff1opw2_5 sup_set_class cima cima ff1opw2_5 sup_set_class wceq ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel wa ff1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 wf1o ff1opw2_1 ff1opw2_2 ff1opw2_3 wf1 ef1opw2_0 ff1opw2_1 ff1opw2_2 ff1opw2_3 f1of1 syl ff1opw2_5 sup_set_class ff1opw2_1 cpw wcel ff1opw2_5 sup_set_class ff1opw2_1 wss ff1opw2_4 sup_set_class ff1opw2_2 cpw wcel ff1opw2_5 sup_set_class ff1opw2_1 elpwi adantr ff1opw2_1 ff1opw2_2 ff1opw2_5 sup_set_class ff1opw2_3 f1imacnv syl2an eqcomd ff1opw2_4 sup_set_class ff1opw2_3 ff1opw2_5 sup_set_class cima wceq ff1opw2_3 ccnv ff1opw2_4 sup_set_class cima ff1opw2_3 ccnv ff1opw2_3 ff1opw2_5 sup_set_class cima cima ff1opw2_5 sup_set_class ff1opw2_4 sup_set_class ff1opw2_3 ff1opw2_5 sup_set_class cima ff1opw2_3 ccnv imaeq2 eqeq2d syl5ibrcom impbid f1o2d $.
$}
$( A one-to-one mapping induces a one-to-one mapping on power sets.
       (Contributed by Stefan O'Rear, 18-Nov-2014.)  (Revised by Mario
       Carneiro, 26-Jun-2015.) $)
${
	$d a b A $.
	$d a b B $.
	$d a b F $.
	if1opw_0 $f set a $.
	ff1opw_0 $f class A $.
	ff1opw_1 $f class B $.
	ff1opw_2 $f class F $.
	ff1opw_3 $f set b $.
	f1opw $p |- ( F : A -1-1-onto-> B -> ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B ) $= ff1opw_0 ff1opw_1 ff1opw_2 wf1o ff1opw_0 ff1opw_1 ff1opw_2 if1opw_0 ff1opw_3 ff1opw_0 ff1opw_1 ff1opw_2 wf1o id ff1opw_0 ff1opw_1 ff1opw_2 wf1o ff1opw_2 ccnv wfun ff1opw_2 ccnv if1opw_0 sup_set_class cima cvv wcel ff1opw_0 ff1opw_1 ff1opw_2 wf1o ff1opw_0 ff1opw_1 ff1opw_2 wfo ff1opw_2 ccnv wfun ff1opw_0 ff1opw_1 ff1opw_2 dff1o3 simprbi ff1opw_2 ccnv if1opw_0 sup_set_class if1opw_0 vex funimaex syl ff1opw_0 ff1opw_1 ff1opw_2 wf1o ff1opw_2 wfun ff1opw_2 ff1opw_3 sup_set_class cima cvv wcel ff1opw_0 ff1opw_1 ff1opw_2 f1ofun ff1opw_2 ff1opw_3 sup_set_class ff1opw_3 vex funimaex syl f1opw2 $.
$}
$( Show that the support of a function is contained in a set.  (Contributed
       by Mario Carneiro, 19-Dec-2014.)  (Revised by Mario Carneiro,
       22-Mar-2015.) $)
${
	$d k A $.
	$d k ph $.
	$d k W $.
	$d k Z $.
	fsuppss2_0 $f wff ph $.
	fsuppss2_1 $f class A $.
	fsuppss2_2 $f class B $.
	fsuppss2_3 $f set k $.
	fsuppss2_4 $f class W $.
	fsuppss2_5 $f class Z $.
	esuppss2_0 $e |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z ) $.
	suppss2 $p |- ( ph -> ( `' ( k e. A |-> B ) " ( _V \ { Z } ) ) C_ W ) $= fsuppss2_0 fsuppss2_3 fsuppss2_1 fsuppss2_2 cmpt ccnv cvv fsuppss2_5 csn cdif cima fsuppss2_2 cvv fsuppss2_5 csn cdif wcel fsuppss2_3 fsuppss2_1 crab fsuppss2_4 fsuppss2_3 fsuppss2_1 fsuppss2_2 cvv fsuppss2_5 csn cdif fsuppss2_3 fsuppss2_1 fsuppss2_2 cmpt fsuppss2_3 fsuppss2_1 fsuppss2_2 cmpt eqid mptpreima fsuppss2_0 fsuppss2_2 cvv fsuppss2_5 csn cdif wcel fsuppss2_3 fsuppss2_1 fsuppss2_4 fsuppss2_0 fsuppss2_3 sup_set_class fsuppss2_1 wcel fsuppss2_2 cvv fsuppss2_5 csn cdif wcel fsuppss2_3 sup_set_class fsuppss2_4 wcel fsuppss2_2 cvv fsuppss2_5 csn cdif wcel fsuppss2_2 fsuppss2_5 wne fsuppss2_0 fsuppss2_3 sup_set_class fsuppss2_1 wcel wa fsuppss2_3 sup_set_class fsuppss2_4 wcel fsuppss2_2 cvv fsuppss2_5 eldifsni fsuppss2_0 fsuppss2_3 sup_set_class fsuppss2_1 wcel wa fsuppss2_3 sup_set_class fsuppss2_4 wcel fsuppss2_2 fsuppss2_5 fsuppss2_0 fsuppss2_3 sup_set_class fsuppss2_1 wcel fsuppss2_3 sup_set_class fsuppss2_4 wcel wn fsuppss2_2 fsuppss2_5 wceq fsuppss2_3 sup_set_class fsuppss2_1 wcel fsuppss2_3 sup_set_class fsuppss2_4 wcel wn wa fsuppss2_0 fsuppss2_3 sup_set_class fsuppss2_1 fsuppss2_4 cdif wcel fsuppss2_2 fsuppss2_5 wceq fsuppss2_3 sup_set_class fsuppss2_1 fsuppss2_4 eldif esuppss2_0 sylan2br expr necon1ad syl5 3impia rabssdv syl5eqss $.
$}
$( Formula building theorem for support restriction, on a function which
       preserves zero.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
${
	$d ph x $.
	$d Y x $.
	$d Z x $.
	fsuppssfv_0 $f wff ph $.
	fsuppssfv_1 $f set x $.
	fsuppssfv_2 $f class A $.
	fsuppssfv_3 $f class D $.
	fsuppssfv_4 $f class F $.
	fsuppssfv_5 $f class L $.
	fsuppssfv_6 $f class V $.
	fsuppssfv_7 $f class Y $.
	fsuppssfv_8 $f class Z $.
	esuppssfv_0 $e |- ( ph -> ( `' ( x e. D |-> A ) " ( _V \ { Y } ) ) C_ L ) $.
	esuppssfv_1 $e |- ( ph -> ( F ` Y ) = Z ) $.
	esuppssfv_2 $e |- ( ( ph /\ x e. D ) -> A e. V ) $.
	suppssfv $p |- ( ph -> ( `' ( x e. D |-> ( F ` A ) ) " ( _V \ { Z } ) ) C_ L ) $= fsuppssfv_0 fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 fsuppssfv_4 cfv cmpt ccnv cvv fsuppssfv_8 csn cdif cima fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 cmpt ccnv cvv fsuppssfv_7 csn cdif cima fsuppssfv_5 fsuppssfv_0 fsuppssfv_2 fsuppssfv_4 cfv cvv fsuppssfv_8 csn cdif wcel fsuppssfv_1 fsuppssfv_3 crab fsuppssfv_2 cvv fsuppssfv_7 csn cdif wcel fsuppssfv_1 fsuppssfv_3 crab fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 fsuppssfv_4 cfv cmpt ccnv cvv fsuppssfv_8 csn cdif cima fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 cmpt ccnv cvv fsuppssfv_7 csn cdif cima fsuppssfv_0 fsuppssfv_2 fsuppssfv_4 cfv cvv fsuppssfv_8 csn cdif wcel fsuppssfv_2 cvv fsuppssfv_7 csn cdif wcel fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 fsuppssfv_4 cfv cvv fsuppssfv_8 csn cdif wcel fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wne fsuppssfv_0 fsuppssfv_1 sup_set_class fsuppssfv_3 wcel wa fsuppssfv_2 cvv fsuppssfv_7 csn cdif wcel fsuppssfv_2 fsuppssfv_4 cfv cvv fsuppssfv_8 eldifsni fsuppssfv_0 fsuppssfv_1 sup_set_class fsuppssfv_3 wcel wa fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wne fsuppssfv_2 cvv fsuppssfv_7 csn cdif wcel fsuppssfv_0 fsuppssfv_1 sup_set_class fsuppssfv_3 wcel wa fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wne wa fsuppssfv_2 cvv wcel fsuppssfv_2 fsuppssfv_7 wne fsuppssfv_2 cvv fsuppssfv_7 csn cdif wcel fsuppssfv_0 fsuppssfv_1 sup_set_class fsuppssfv_3 wcel wa fsuppssfv_2 cvv wcel fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wne fsuppssfv_0 fsuppssfv_1 sup_set_class fsuppssfv_3 wcel wa fsuppssfv_2 fsuppssfv_6 wcel fsuppssfv_2 cvv wcel esuppssfv_2 fsuppssfv_2 fsuppssfv_6 elex syl adantr fsuppssfv_0 fsuppssfv_1 sup_set_class fsuppssfv_3 wcel wa fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wne fsuppssfv_2 fsuppssfv_7 wne fsuppssfv_0 fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wne fsuppssfv_2 fsuppssfv_7 wne wi fsuppssfv_1 sup_set_class fsuppssfv_3 wcel fsuppssfv_0 fsuppssfv_2 fsuppssfv_7 fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 fsuppssfv_0 fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_8 wceq fsuppssfv_2 fsuppssfv_7 wceq fsuppssfv_7 fsuppssfv_4 cfv fsuppssfv_8 wceq esuppssfv_1 fsuppssfv_2 fsuppssfv_7 wceq fsuppssfv_2 fsuppssfv_4 cfv fsuppssfv_7 fsuppssfv_4 cfv fsuppssfv_8 fsuppssfv_2 fsuppssfv_7 fsuppssfv_4 fveq2 eqeq1d syl5ibrcom necon3d adantr imp fsuppssfv_2 cvv fsuppssfv_7 eldifsn sylanbrc ex syl5 ss2rabdv fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 fsuppssfv_4 cfv cvv fsuppssfv_8 csn cdif fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 fsuppssfv_4 cfv cmpt fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 fsuppssfv_4 cfv cmpt eqid mptpreima fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 cvv fsuppssfv_7 csn cdif fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 cmpt fsuppssfv_1 fsuppssfv_3 fsuppssfv_2 cmpt eqid mptpreima 3sstr4g esuppssfv_0 sstrd $.
$}
$( Formula building theorem for support restrictions: operator with left
       annihilator.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
${
	$d ph v $.
	$d ph x $.
	$d B v $.
	$d O v $.
	$d R v $.
	$d Y v $.
	$d Y x $.
	$d Z v $.
	$d Z x $.
	fsuppssov1_0 $f wff ph $.
	fsuppssov1_1 $f set x $.
	fsuppssov1_2 $f set v $.
	fsuppssov1_3 $f class A $.
	fsuppssov1_4 $f class B $.
	fsuppssov1_5 $f class D $.
	fsuppssov1_6 $f class R $.
	fsuppssov1_7 $f class L $.
	fsuppssov1_8 $f class O $.
	fsuppssov1_9 $f class V $.
	fsuppssov1_10 $f class Y $.
	fsuppssov1_11 $f class Z $.
	esuppssov1_0 $e |- ( ph -> ( `' ( x e. D |-> A ) " ( _V \ { Y } ) ) C_ L ) $.
	esuppssov1_1 $e |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z ) $.
	esuppssov1_2 $e |- ( ( ph /\ x e. D ) -> A e. V ) $.
	esuppssov1_3 $e |- ( ( ph /\ x e. D ) -> B e. R ) $.
	suppssov1 $p |- ( ph -> ( `' ( x e. D |-> ( A O B ) ) " ( _V \ { Z } ) ) C_ L ) $= fsuppssov1_0 fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cmpt ccnv cvv fsuppssov1_11 csn cdif cima fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 cmpt ccnv cvv fsuppssov1_10 csn cdif cima fsuppssov1_7 fsuppssov1_0 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel fsuppssov1_1 fsuppssov1_5 crab fsuppssov1_3 cvv fsuppssov1_10 csn cdif wcel fsuppssov1_1 fsuppssov1_5 crab fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cmpt ccnv cvv fsuppssov1_11 csn cdif cima fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 cmpt ccnv cvv fsuppssov1_10 csn cdif cima fsuppssov1_0 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel fsuppssov1_3 cvv fsuppssov1_10 csn cdif wcel fsuppssov1_1 fsuppssov1_5 fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel fsuppssov1_3 cvv fsuppssov1_10 csn cdif wcel fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel wa fsuppssov1_3 cvv wcel fsuppssov1_3 fsuppssov1_10 wne fsuppssov1_3 cvv fsuppssov1_10 csn cdif wcel fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 cvv wcel fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_9 wcel fsuppssov1_3 cvv wcel esuppssov1_2 fsuppssov1_3 fsuppssov1_9 elex syl adantr fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel fsuppssov1_3 fsuppssov1_10 wne fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif wcel fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 wne fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_10 wne fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 eldifsni fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_10 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_3 fsuppssov1_10 wceq fsuppssov1_10 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_0 fsuppssov1_1 sup_set_class fsuppssov1_5 wcel wa fsuppssov1_4 fsuppssov1_6 wcel fsuppssov1_10 fsuppssov1_2 sup_set_class fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_2 fsuppssov1_6 wral fsuppssov1_10 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 wceq esuppssov1_3 fsuppssov1_0 fsuppssov1_10 fsuppssov1_2 sup_set_class fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_2 fsuppssov1_6 wral fsuppssov1_1 sup_set_class fsuppssov1_5 wcel fsuppssov1_0 fsuppssov1_10 fsuppssov1_2 sup_set_class fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_2 fsuppssov1_6 esuppssov1_1 ralrimiva adantr fsuppssov1_10 fsuppssov1_2 sup_set_class fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_10 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 wceq fsuppssov1_2 fsuppssov1_4 fsuppssov1_6 fsuppssov1_2 sup_set_class fsuppssov1_4 wceq fsuppssov1_10 fsuppssov1_2 sup_set_class fsuppssov1_8 co fsuppssov1_10 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 fsuppssov1_2 sup_set_class fsuppssov1_4 fsuppssov1_10 fsuppssov1_8 oveq2 eqeq1d rspcva syl2anc fsuppssov1_3 fsuppssov1_10 wceq fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_10 fsuppssov1_4 fsuppssov1_8 co fsuppssov1_11 fsuppssov1_3 fsuppssov1_10 fsuppssov1_4 fsuppssov1_8 oveq1 eqeq1d syl5ibrcom necon3d syl5 imp fsuppssov1_3 cvv fsuppssov1_10 eldifsn sylanbrc ex ss2rabdv fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cvv fsuppssov1_11 csn cdif fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cmpt fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 fsuppssov1_4 fsuppssov1_8 co cmpt eqid mptpreima fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 cvv fsuppssov1_10 csn cdif fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 cmpt fsuppssov1_1 fsuppssov1_5 fsuppssov1_3 cmpt eqid mptpreima 3sstr4g esuppssov1_0 sstrd $.
$}

