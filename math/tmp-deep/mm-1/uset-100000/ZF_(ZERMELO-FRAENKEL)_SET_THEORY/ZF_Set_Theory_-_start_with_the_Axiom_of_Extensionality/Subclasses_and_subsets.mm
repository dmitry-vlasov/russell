$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Define_basic_set_operations_and_relations.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Subclasses and subsets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Define the subclass relationship.  Exercise 9 of [TakeutiZaring] p. 18.
     For example, ` { 1 , 2 } C_ { 1 , 2 , 3 } ` ( ~ ex-ss ).  Note that
     ` A C_ A ` (proved in ~ ssid ).  Contrast this relationship with the
     relationship ` A C. B ` (as will be defined in ~ df-pss ).  For a more
     traditional definition, but requiring a dummy variable, see ~ dfss2 .
     Other possible definitions are given by ~ dfss3 , ~ dfss4 , ~ sspss ,
     ~ ssequn1 , ~ ssequn2 , ~ sseqin2 , and ~ ssdif0 .  (Contributed by NM,
     27-Apr-1994.) $)

${
	$v A B  $.
	f0_df-ss $f class A $.
	f1_df-ss $f class B $.
	a_df-ss $a |- ( A C_ B <-> ( A i^i B ) = A ) $.
$}

$(Variant of subclass definition ~ df-ss .  (Contributed by NM,
     3-Sep-2004.) $)

${
	$v A B  $.
	f0_dfss $f class A $.
	f1_dfss $f class B $.
	p_dfss $p |- ( A C_ B <-> A = ( A i^i B ) ) $= f0_dfss f1_dfss a_df-ss f0_dfss f1_dfss a_cin f0_dfss p_eqcom f0_dfss f1_dfss a_wss f0_dfss f1_dfss a_cin f0_dfss a_wceq f0_dfss f0_dfss f1_dfss a_cin a_wceq p_bitri $.
$}

$(Define proper subclass relationship between two classes.  Definition 5.9
     of [TakeutiZaring] p. 17.  For example, ` { 1 , 2 } C. { 1 , 2 , 3 } `
     ( ~ ex-pss ).  Note that ` -. A C. A ` (proved in ~ pssirr ).  Contrast
     this relationship with the relationship ` A C_ B ` (as defined in
     ~ df-ss ).  Other possible definitions are given by ~ dfpss2 and
     ~ dfpss3 .  (Contributed by NM, 7-Feb-1996.) $)

${
	$v A B  $.
	f0_df-pss $f class A $.
	f1_df-pss $f class B $.
	a_df-pss $a |- ( A C. B <-> ( A C_ B /\ A =/= B ) ) $.
$}

$(Alternate definition of the subclass relationship between two classes.
       Definition 5.9 of [TakeutiZaring] p. 17.  (Contributed by NM,
       8-Jan-2002.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfss2 $f set x $.
	f1_dfss2 $f class A $.
	f2_dfss2 $f class B $.
	p_dfss2 $p |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $= f1_dfss2 f2_dfss2 p_dfss f0_dfss2 f1_dfss2 f2_dfss2 a_df-in f1_dfss2 f2_dfss2 a_cin f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wa f0_dfss2 a_cab f1_dfss2 p_eqeq2i f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wa f0_dfss2 f1_dfss2 p_abeq2 f1_dfss2 f2_dfss2 a_wss f1_dfss2 f1_dfss2 f2_dfss2 a_cin a_wceq f1_dfss2 f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wa f0_dfss2 a_cab a_wceq f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wa a_wb f0_dfss2 a_wal p_3bitri f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel p_pm4.71 f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wi f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wa a_wb f0_dfss2 p_albii f1_dfss2 f2_dfss2 a_wss f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wa a_wb f0_dfss2 a_wal f0_dfss2 a_sup_set_class f1_dfss2 a_wcel f0_dfss2 a_sup_set_class f2_dfss2 a_wcel a_wi f0_dfss2 a_wal p_bitr4i $.
$}

$(Alternate definition of subclass relationship.  (Contributed by NM,
       14-Oct-1999.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfss3 $f set x $.
	f1_dfss3 $f class A $.
	f2_dfss3 $f class B $.
	p_dfss3 $p |- ( A C_ B <-> A. x e. A x e. B ) $= f0_dfss3 f1_dfss3 f2_dfss3 p_dfss2 f0_dfss3 a_sup_set_class f2_dfss3 a_wcel f0_dfss3 f1_dfss3 a_df-ral f1_dfss3 f2_dfss3 a_wss f0_dfss3 a_sup_set_class f1_dfss3 a_wcel f0_dfss3 a_sup_set_class f2_dfss3 a_wcel a_wi f0_dfss3 a_wal f0_dfss3 a_sup_set_class f2_dfss3 a_wcel f0_dfss3 f1_dfss3 a_wral p_bitr4i $.
$}

$(Equivalence for subclass relation, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       3-Jul-1994.)  (Revised by Andrew Salmon, 27-Aug-2011.) $)

${
	$v x A B  $.
	$d z A  $.
	$d z B  $.
	$d x z  $.
	f0_dfss2f $f set x $.
	f1_dfss2f $f class A $.
	f2_dfss2f $f class B $.
	i0_dfss2f $f set z $.
	e0_dfss2f $e |- F/_ x A $.
	e1_dfss2f $e |- F/_ x B $.
	p_dfss2f $p |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $= i0_dfss2f f1_dfss2f f2_dfss2f p_dfss2 e0_dfss2f f0_dfss2f i0_dfss2f f1_dfss2f p_nfcri e1_dfss2f f0_dfss2f i0_dfss2f f2_dfss2f p_nfcri i0_dfss2f a_sup_set_class f1_dfss2f a_wcel i0_dfss2f a_sup_set_class f2_dfss2f a_wcel f0_dfss2f p_nfim f0_dfss2f a_sup_set_class f1_dfss2f a_wcel f0_dfss2f a_sup_set_class f2_dfss2f a_wcel a_wi i0_dfss2f p_nfv i0_dfss2f a_sup_set_class f0_dfss2f a_sup_set_class f1_dfss2f p_eleq1 i0_dfss2f a_sup_set_class f0_dfss2f a_sup_set_class f2_dfss2f p_eleq1 i0_dfss2f a_sup_set_class f0_dfss2f a_sup_set_class a_wceq i0_dfss2f a_sup_set_class f1_dfss2f a_wcel f0_dfss2f a_sup_set_class f1_dfss2f a_wcel i0_dfss2f a_sup_set_class f2_dfss2f a_wcel f0_dfss2f a_sup_set_class f2_dfss2f a_wcel p_imbi12d i0_dfss2f a_sup_set_class f1_dfss2f a_wcel i0_dfss2f a_sup_set_class f2_dfss2f a_wcel a_wi f0_dfss2f a_sup_set_class f1_dfss2f a_wcel f0_dfss2f a_sup_set_class f2_dfss2f a_wcel a_wi i0_dfss2f f0_dfss2f p_cbval f1_dfss2f f2_dfss2f a_wss i0_dfss2f a_sup_set_class f1_dfss2f a_wcel i0_dfss2f a_sup_set_class f2_dfss2f a_wcel a_wi i0_dfss2f a_wal f0_dfss2f a_sup_set_class f1_dfss2f a_wcel f0_dfss2f a_sup_set_class f2_dfss2f a_wcel a_wi f0_dfss2f a_wal p_bitri $.
$}

$(Equivalence for subclass relation, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       20-Mar-2004.) $)

${
	$v x A B  $.
	$d A  $.
	$d B  $.
	$d x  $.
	$d A  $.
	$d B  $.
	f0_dfss3f $f set x $.
	f1_dfss3f $f class A $.
	f2_dfss3f $f class B $.
	e0_dfss3f $e |- F/_ x A $.
	e1_dfss3f $e |- F/_ x B $.
	p_dfss3f $p |- ( A C_ B <-> A. x e. A x e. B ) $= e0_dfss3f e1_dfss3f f0_dfss3f f1_dfss3f f2_dfss3f p_dfss2f f0_dfss3f a_sup_set_class f2_dfss3f a_wcel f0_dfss3f f1_dfss3f a_df-ral f1_dfss3f f2_dfss3f a_wss f0_dfss3f a_sup_set_class f1_dfss3f a_wcel f0_dfss3f a_sup_set_class f2_dfss3f a_wcel a_wi f0_dfss3f a_wal f0_dfss3f a_sup_set_class f2_dfss3f a_wcel f0_dfss3f f1_dfss3f a_wral p_bitr4i $.
$}

$(If ` x ` is not free in ` A ` and ` B ` , it is not free in
       ` A C_ B ` .  (Contributed by NM, 27-Dec-1996.) $)

${
	$v x A B  $.
	$d A  $.
	$d B  $.
	$d x  $.
	$d A  $.
	$d B  $.
	f0_nfss $f set x $.
	f1_nfss $f class A $.
	f2_nfss $f class B $.
	e0_nfss $e |- F/_ x A $.
	e1_nfss $e |- F/_ x B $.
	p_nfss $p |- F/ x A C_ B $= e0_nfss e1_nfss f0_nfss f1_nfss f2_nfss p_dfss3f f0_nfss a_sup_set_class f2_nfss a_wcel f0_nfss f1_nfss p_nfra1 f1_nfss f2_nfss a_wss f0_nfss a_sup_set_class f2_nfss a_wcel f0_nfss f1_nfss a_wral f0_nfss p_nfxfr $.
$}

$(Membership relationships follow from a subclass relationship.
       (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_ssel $f class A $.
	f1_ssel $f class B $.
	f2_ssel $f class C $.
	i0_ssel $f set x $.
	p_ssel $p |- ( A C_ B -> ( C e. A -> C e. B ) ) $= i0_ssel f0_ssel f1_ssel p_dfss2 f0_ssel f1_ssel a_wss i0_ssel a_sup_set_class f0_ssel a_wcel i0_ssel a_sup_set_class f1_ssel a_wcel a_wi i0_ssel a_wal p_biimpi f0_ssel f1_ssel a_wss i0_ssel a_sup_set_class f0_ssel a_wcel i0_ssel a_sup_set_class f1_ssel a_wcel a_wi i0_ssel p_19.21bi f0_ssel f1_ssel a_wss i0_ssel a_sup_set_class f0_ssel a_wcel i0_ssel a_sup_set_class f1_ssel a_wcel i0_ssel a_sup_set_class f2_ssel a_wceq p_anim2d f0_ssel f1_ssel a_wss i0_ssel a_sup_set_class f2_ssel a_wceq i0_ssel a_sup_set_class f0_ssel a_wcel a_wa i0_ssel a_sup_set_class f2_ssel a_wceq i0_ssel a_sup_set_class f1_ssel a_wcel a_wa i0_ssel p_eximdv i0_ssel f2_ssel f0_ssel a_df-clel i0_ssel f2_ssel f1_ssel a_df-clel f0_ssel f1_ssel a_wss i0_ssel a_sup_set_class f2_ssel a_wceq i0_ssel a_sup_set_class f0_ssel a_wcel a_wa i0_ssel a_wex i0_ssel a_sup_set_class f2_ssel a_wceq i0_ssel a_sup_set_class f1_ssel a_wcel a_wa i0_ssel a_wex f2_ssel f0_ssel a_wcel f2_ssel f1_ssel a_wcel p_3imtr4g $.
$}

$(Membership relationships follow from a subclass relationship.
     (Contributed by NM, 7-Jun-2004.) $)

${
	$v A B C  $.
	f0_ssel2 $f class A $.
	f1_ssel2 $f class B $.
	f2_ssel2 $f class C $.
	p_ssel2 $p |- ( ( A C_ B /\ C e. A ) -> C e. B ) $= f0_ssel2 f1_ssel2 f2_ssel2 p_ssel f0_ssel2 f1_ssel2 a_wss f2_ssel2 f0_ssel2 a_wcel f2_ssel2 f1_ssel2 a_wcel p_imp $.
$}

$(Membership inference from subclass relationship.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v A B C  $.
	f0_sseli $f class A $.
	f1_sseli $f class B $.
	f2_sseli $f class C $.
	e0_sseli $e |- A C_ B $.
	p_sseli $p |- ( C e. A -> C e. B ) $= e0_sseli f0_sseli f1_sseli f2_sseli p_ssel f0_sseli f1_sseli a_wss f2_sseli f0_sseli a_wcel f2_sseli f1_sseli a_wcel a_wi a_ax-mp $.
$}

$(Membership inference from subclass relationship.  (Contributed by NM,
         31-May-1999.) $)

${
	$v A B C  $.
	f0_sselii $f class A $.
	f1_sselii $f class B $.
	f2_sselii $f class C $.
	e0_sselii $e |- A C_ B $.
	e1_sselii $e |- C e. A $.
	p_sselii $p |- C e. B $= e1_sselii e0_sselii f0_sselii f1_sselii f2_sselii p_sseli f2_sselii f0_sselii a_wcel f2_sselii f1_sselii a_wcel a_ax-mp $.
$}

$(Membership inference from subclass relationship.  (Contributed by NM,
         25-Jun-2014.) $)

${
	$v ph A B C  $.
	f0_sseldi $f wff ph $.
	f1_sseldi $f class A $.
	f2_sseldi $f class B $.
	f3_sseldi $f class C $.
	e0_sseldi $e |- A C_ B $.
	e1_sseldi $e |- ( ph -> C e. A ) $.
	p_sseldi $p |- ( ph -> C e. B ) $= e1_sseldi e0_sseldi f1_sseldi f2_sseldi f3_sseldi p_sseli f0_sseldi f3_sseldi f1_sseldi a_wcel f3_sseldi f2_sseldi a_wcel p_syl $.
$}

$(Membership deduction from subclass relationship.  (Contributed by NM,
       15-Nov-1995.) $)

${
	$v ph A B C  $.
	f0_sseld $f wff ph $.
	f1_sseld $f class A $.
	f2_sseld $f class B $.
	f3_sseld $f class C $.
	e0_sseld $e |- ( ph -> A C_ B ) $.
	p_sseld $p |- ( ph -> ( C e. A -> C e. B ) ) $= e0_sseld f1_sseld f2_sseld f3_sseld p_ssel f0_sseld f1_sseld f2_sseld a_wss f3_sseld f1_sseld a_wcel f3_sseld f2_sseld a_wcel a_wi p_syl $.
$}

$(Membership deduction from subclass relationship.  (Contributed by NM,
       26-Jun-2014.) $)

${
	$v ph A B C  $.
	f0_sselda $f wff ph $.
	f1_sselda $f class A $.
	f2_sselda $f class B $.
	f3_sselda $f class C $.
	e0_sselda $e |- ( ph -> A C_ B ) $.
	p_sselda $p |- ( ( ph /\ C e. A ) -> C e. B ) $= e0_sselda f0_sselda f1_sselda f2_sselda f3_sselda p_sseld f0_sselda f3_sselda f1_sselda a_wcel f3_sselda f2_sselda a_wcel p_imp $.
$}

$(Membership inference from subclass relationship.  (Contributed by NM,
         14-Dec-2004.) $)

${
	$v ph A B C  $.
	f0_sseldd $f wff ph $.
	f1_sseldd $f class A $.
	f2_sseldd $f class B $.
	f3_sseldd $f class C $.
	e0_sseldd $e |- ( ph -> A C_ B ) $.
	e1_sseldd $e |- ( ph -> C e. A ) $.
	p_sseldd $p |- ( ph -> C e. B ) $= e1_sseldd e0_sseldd f0_sseldd f1_sseldd f2_sseldd f3_sseldd p_sseld f0_sseldd f3_sseldd f1_sseldd a_wcel f3_sseldd f2_sseldd a_wcel p_mpd $.
$}

$(If a class is not in another class, it is also not in a subclass of that
       class.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_ssneld $f wff ph $.
	f1_ssneld $f class A $.
	f2_ssneld $f class B $.
	f3_ssneld $f class C $.
	e0_ssneld $e |- ( ph -> A C_ B ) $.
	p_ssneld $p |- ( ph -> ( -. C e. B -> -. C e. A ) ) $= e0_ssneld f0_ssneld f1_ssneld f2_ssneld f3_ssneld p_sseld f0_ssneld f3_ssneld f1_ssneld a_wcel f3_ssneld f2_ssneld a_wcel p_con3d $.
$}

$(If an element is not in a class, it is also not in a subclass of that
       class.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_ssneldd $f wff ph $.
	f1_ssneldd $f class A $.
	f2_ssneldd $f class B $.
	f3_ssneldd $f class C $.
	e0_ssneldd $e |- ( ph -> A C_ B ) $.
	e1_ssneldd $e |- ( ph -> -. C e. B ) $.
	p_ssneldd $p |- ( ph -> -. C e. A ) $= e1_ssneldd e0_ssneldd f0_ssneldd f1_ssneldd f2_ssneldd f3_ssneldd p_ssneld f0_ssneldd f3_ssneldd f2_ssneldd a_wcel a_wn f3_ssneldd f1_ssneldd a_wcel a_wn p_mpd $.
$}

$(Inference rule based on subclass definition.  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssriv $f set x $.
	f1_ssriv $f class A $.
	f2_ssriv $f class B $.
	e0_ssriv $e |- ( x e. A -> x e. B ) $.
	p_ssriv $p |- A C_ B $= f0_ssriv f1_ssriv f2_ssriv p_dfss2 e0_ssriv f1_ssriv f2_ssriv a_wss f0_ssriv a_sup_set_class f1_ssriv a_wcel f0_ssriv a_sup_set_class f2_ssriv a_wcel a_wi f0_ssriv p_mpgbir $.
$}

$(Deduction rule based on subclass definition.  (Contributed by NM,
       15-Nov-1995.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_ssrdv $f wff ph $.
	f1_ssrdv $f set x $.
	f2_ssrdv $f class A $.
	f3_ssrdv $f class B $.
	e0_ssrdv $e |- ( ph -> ( x e. A -> x e. B ) ) $.
	p_ssrdv $p |- ( ph -> A C_ B ) $= e0_ssrdv f0_ssrdv f1_ssrdv a_sup_set_class f2_ssrdv a_wcel f1_ssrdv a_sup_set_class f3_ssrdv a_wcel a_wi f1_ssrdv p_alrimiv f1_ssrdv f2_ssrdv f3_ssrdv p_dfss2 f0_ssrdv f1_ssrdv a_sup_set_class f2_ssrdv a_wcel f1_ssrdv a_sup_set_class f3_ssrdv a_wcel a_wi f1_ssrdv a_wal f2_ssrdv f3_ssrdv a_wss p_sylibr $.
$}

$(Transitivity of subclasses.  Exercise 5 of [TakeutiZaring] p. 17.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_sstr2 $f class A $.
	f1_sstr2 $f class B $.
	f2_sstr2 $f class C $.
	i0_sstr2 $f set x $.
	p_sstr2 $p |- ( A C_ B -> ( B C_ C -> A C_ C ) ) $= f0_sstr2 f1_sstr2 i0_sstr2 a_sup_set_class p_ssel f0_sstr2 f1_sstr2 a_wss i0_sstr2 a_sup_set_class f0_sstr2 a_wcel i0_sstr2 a_sup_set_class f1_sstr2 a_wcel i0_sstr2 a_sup_set_class f2_sstr2 a_wcel p_imim1d f0_sstr2 f1_sstr2 a_wss i0_sstr2 a_sup_set_class f1_sstr2 a_wcel i0_sstr2 a_sup_set_class f2_sstr2 a_wcel a_wi i0_sstr2 a_sup_set_class f0_sstr2 a_wcel i0_sstr2 a_sup_set_class f2_sstr2 a_wcel a_wi i0_sstr2 p_alimdv i0_sstr2 f1_sstr2 f2_sstr2 p_dfss2 i0_sstr2 f0_sstr2 f2_sstr2 p_dfss2 f0_sstr2 f1_sstr2 a_wss i0_sstr2 a_sup_set_class f1_sstr2 a_wcel i0_sstr2 a_sup_set_class f2_sstr2 a_wcel a_wi i0_sstr2 a_wal i0_sstr2 a_sup_set_class f0_sstr2 a_wcel i0_sstr2 a_sup_set_class f2_sstr2 a_wcel a_wi i0_sstr2 a_wal f1_sstr2 f2_sstr2 a_wss f0_sstr2 f2_sstr2 a_wss p_3imtr4g $.
$}

$(Transitivity of subclasses.  Theorem 6 of [Suppes] p. 23.  (Contributed by
     NM, 5-Sep-2003.) $)

${
	$v A B C  $.
	f0_sstr $f class A $.
	f1_sstr $f class B $.
	f2_sstr $f class C $.
	p_sstr $p |- ( ( A C_ B /\ B C_ C ) -> A C_ C ) $= f0_sstr f1_sstr f2_sstr p_sstr2 f0_sstr f1_sstr a_wss f1_sstr f2_sstr a_wss f0_sstr f2_sstr a_wss p_imp $.
$}

$(Subclass transitivity inference.  (Contributed by NM, 5-May-2000.) $)

${
	$v A B C  $.
	f0_sstri $f class A $.
	f1_sstri $f class B $.
	f2_sstri $f class C $.
	e0_sstri $e |- A C_ B $.
	e1_sstri $e |- B C_ C $.
	p_sstri $p |- A C_ C $= e0_sstri e1_sstri f0_sstri f1_sstri f2_sstri p_sstr2 f0_sstri f1_sstri a_wss f1_sstri f2_sstri a_wss f0_sstri f2_sstri a_wss p_mp2 $.
$}

$(Subclass transitivity deduction.  (Contributed by NM, 2-Jun-2004.) $)

${
	$v ph A B C  $.
	f0_sstrd $f wff ph $.
	f1_sstrd $f class A $.
	f2_sstrd $f class B $.
	f3_sstrd $f class C $.
	e0_sstrd $e |- ( ph -> A C_ B ) $.
	e1_sstrd $e |- ( ph -> B C_ C ) $.
	p_sstrd $p |- ( ph -> A C_ C ) $= e0_sstrd e1_sstrd f1_sstrd f2_sstrd f3_sstrd p_sstr f0_sstrd f1_sstrd f2_sstrd a_wss f2_sstrd f3_sstrd a_wss f1_sstrd f3_sstrd a_wss p_syl2anc $.
$}

$(Subclass transitivity deduction.  (Contributed by NM, 6-Feb-2014.) $)

${
	$v ph A B C  $.
	f0_syl5ss $f wff ph $.
	f1_syl5ss $f class A $.
	f2_syl5ss $f class B $.
	f3_syl5ss $f class C $.
	e0_syl5ss $e |- A C_ B $.
	e1_syl5ss $e |- ( ph -> B C_ C ) $.
	p_syl5ss $p |- ( ph -> A C_ C ) $= e0_syl5ss f1_syl5ss f2_syl5ss a_wss f0_syl5ss p_a1i e1_syl5ss f0_syl5ss f1_syl5ss f2_syl5ss f3_syl5ss p_sstrd $.
$}

$(Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)

${
	$v ph A B C  $.
	f0_syl6ss $f wff ph $.
	f1_syl6ss $f class A $.
	f2_syl6ss $f class B $.
	f3_syl6ss $f class C $.
	e0_syl6ss $e |- ( ph -> A C_ B ) $.
	e1_syl6ss $e |- B C_ C $.
	p_syl6ss $p |- ( ph -> A C_ C ) $= e0_syl6ss e1_syl6ss f2_syl6ss f3_syl6ss a_wss f0_syl6ss p_a1i f0_syl6ss f1_syl6ss f2_syl6ss f3_syl6ss p_sstrd $.
$}

$(A subclass transitivity deduction.  (Contributed by NM, 27-Sep-2004.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)

${
	$v ph ps A B C  $.
	f0_sylan9ss $f wff ph $.
	f1_sylan9ss $f wff ps $.
	f2_sylan9ss $f class A $.
	f3_sylan9ss $f class B $.
	f4_sylan9ss $f class C $.
	e0_sylan9ss $e |- ( ph -> A C_ B ) $.
	e1_sylan9ss $e |- ( ps -> B C_ C ) $.
	p_sylan9ss $p |- ( ( ph /\ ps ) -> A C_ C ) $= e0_sylan9ss e1_sylan9ss f2_sylan9ss f3_sylan9ss f4_sylan9ss p_sstr f0_sylan9ss f2_sylan9ss f3_sylan9ss a_wss f3_sylan9ss f4_sylan9ss a_wss f2_sylan9ss f4_sylan9ss a_wss f1_sylan9ss p_syl2an $.
$}

$(A subclass transitivity deduction.  (Contributed by NM, 27-Sep-2004.) $)

${
	$v ph ps A B C  $.
	f0_sylan9ssr $f wff ph $.
	f1_sylan9ssr $f wff ps $.
	f2_sylan9ssr $f class A $.
	f3_sylan9ssr $f class B $.
	f4_sylan9ssr $f class C $.
	e0_sylan9ssr $e |- ( ph -> A C_ B ) $.
	e1_sylan9ssr $e |- ( ps -> B C_ C ) $.
	p_sylan9ssr $p |- ( ( ps /\ ph ) -> A C_ C ) $= e0_sylan9ssr e1_sylan9ssr f0_sylan9ssr f1_sylan9ssr f2_sylan9ssr f3_sylan9ssr f4_sylan9ssr p_sylan9ss f0_sylan9ssr f1_sylan9ssr f2_sylan9ssr f4_sylan9ssr a_wss p_ancoms $.
$}

$(The subclass relationship is antisymmetric.  Compare Theorem 4 of
       [Suppes] p. 22.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_eqss $f class A $.
	f1_eqss $f class B $.
	i0_eqss $f set x $.
	p_eqss $p |- ( A = B <-> ( A C_ B /\ B C_ A ) ) $= i0_eqss a_sup_set_class f0_eqss a_wcel i0_eqss a_sup_set_class f1_eqss a_wcel i0_eqss p_albiim i0_eqss f0_eqss f1_eqss p_dfcleq i0_eqss f0_eqss f1_eqss p_dfss2 i0_eqss f1_eqss f0_eqss p_dfss2 f0_eqss f1_eqss a_wss i0_eqss a_sup_set_class f0_eqss a_wcel i0_eqss a_sup_set_class f1_eqss a_wcel a_wi i0_eqss a_wal f1_eqss f0_eqss a_wss i0_eqss a_sup_set_class f1_eqss a_wcel i0_eqss a_sup_set_class f0_eqss a_wcel a_wi i0_eqss a_wal p_anbi12i i0_eqss a_sup_set_class f0_eqss a_wcel i0_eqss a_sup_set_class f1_eqss a_wcel a_wb i0_eqss a_wal i0_eqss a_sup_set_class f0_eqss a_wcel i0_eqss a_sup_set_class f1_eqss a_wcel a_wi i0_eqss a_wal i0_eqss a_sup_set_class f1_eqss a_wcel i0_eqss a_sup_set_class f0_eqss a_wcel a_wi i0_eqss a_wal a_wa f0_eqss f1_eqss a_wceq f0_eqss f1_eqss a_wss f1_eqss f0_eqss a_wss a_wa p_3bitr4i $.
$}

$(Infer equality from two subclass relationships.  Compare Theorem 4 of
       [Suppes] p. 22.  (Contributed by NM, 9-Sep-1993.) $)

${
	$v A B  $.
	f0_eqssi $f class A $.
	f1_eqssi $f class B $.
	e0_eqssi $e |- A C_ B $.
	e1_eqssi $e |- B C_ A $.
	p_eqssi $p |- A = B $= e0_eqssi e1_eqssi f0_eqssi f1_eqssi p_eqss f0_eqssi f1_eqssi a_wceq f0_eqssi f1_eqssi a_wss f1_eqssi f0_eqssi a_wss p_mpbir2an $.
$}

$(Equality deduction from two subclass relationships.  Compare Theorem 4
       of [Suppes] p. 22.  (Contributed by NM, 27-Jun-2004.) $)

${
	$v ph A B  $.
	f0_eqssd $f wff ph $.
	f1_eqssd $f class A $.
	f2_eqssd $f class B $.
	e0_eqssd $e |- ( ph -> A C_ B ) $.
	e1_eqssd $e |- ( ph -> B C_ A ) $.
	p_eqssd $p |- ( ph -> A = B ) $= e0_eqssd e1_eqssd f1_eqssd f2_eqssd p_eqss f0_eqssd f1_eqssd f2_eqssd a_wss f2_eqssd f1_eqssd a_wss f1_eqssd f2_eqssd a_wceq p_sylanbrc $.
$}

$(Any class is a subclass of itself.  Exercise 10 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 14-Jun-2011.) $)

${
	$v A  $.
	$d A x  $.
	f0_ssid $f class A $.
	i0_ssid $f set x $.
	p_ssid $p |- A C_ A $= i0_ssid a_sup_set_class f0_ssid a_wcel p_id i0_ssid f0_ssid f0_ssid p_ssriv $.
$}

$(Any class is a subclass of the universal class.  (Contributed by NM,
       31-Oct-1995.) $)

${
	$v A  $.
	$d A x  $.
	f0_ssv $f class A $.
	i0_ssv $f set x $.
	p_ssv $p |- A C_ _V $= i0_ssv a_sup_set_class f0_ssv p_elex i0_ssv f0_ssv a_cvv p_ssriv $.
$}

$(Equality theorem for subclasses.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 21-Jun-2011.) $)

${
	$v A B C  $.
	f0_sseq1 $f class A $.
	f1_sseq1 $f class B $.
	f2_sseq1 $f class C $.
	p_sseq1 $p |- ( A = B -> ( A C_ C <-> B C_ C ) ) $= f0_sseq1 f1_sseq1 p_eqss f1_sseq1 f0_sseq1 f2_sseq1 p_sstr2 f1_sseq1 f0_sseq1 a_wss f0_sseq1 f2_sseq1 a_wss f1_sseq1 f2_sseq1 a_wss a_wi f0_sseq1 f1_sseq1 a_wss p_adantl f0_sseq1 f1_sseq1 f2_sseq1 p_sstr2 f0_sseq1 f1_sseq1 a_wss f1_sseq1 f2_sseq1 a_wss f0_sseq1 f2_sseq1 a_wss a_wi f1_sseq1 f0_sseq1 a_wss p_adantr f0_sseq1 f1_sseq1 a_wss f1_sseq1 f0_sseq1 a_wss a_wa f0_sseq1 f2_sseq1 a_wss f1_sseq1 f2_sseq1 a_wss p_impbid f0_sseq1 f1_sseq1 a_wceq f0_sseq1 f1_sseq1 a_wss f1_sseq1 f0_sseq1 a_wss a_wa f0_sseq1 f2_sseq1 a_wss f1_sseq1 f2_sseq1 a_wss a_wb p_sylbi $.
$}

$(Equality theorem for the subclass relationship.  (Contributed by NM,
     25-Jun-1998.) $)

${
	$v A B C  $.
	f0_sseq2 $f class A $.
	f1_sseq2 $f class B $.
	f2_sseq2 $f class C $.
	p_sseq2 $p |- ( A = B -> ( C C_ A <-> C C_ B ) ) $= f2_sseq2 f0_sseq2 f1_sseq2 p_sstr2 f2_sseq2 f0_sseq2 a_wss f0_sseq2 f1_sseq2 a_wss f2_sseq2 f1_sseq2 a_wss p_com12 f2_sseq2 f1_sseq2 f0_sseq2 p_sstr2 f2_sseq2 f1_sseq2 a_wss f1_sseq2 f0_sseq2 a_wss f2_sseq2 f0_sseq2 a_wss p_com12 f0_sseq2 f1_sseq2 a_wss f2_sseq2 f0_sseq2 a_wss f2_sseq2 f1_sseq2 a_wss a_wi f1_sseq2 f0_sseq2 a_wss f2_sseq2 f1_sseq2 a_wss f2_sseq2 f0_sseq2 a_wss a_wi p_anim12i f0_sseq2 f1_sseq2 p_eqss f2_sseq2 f0_sseq2 a_wss f2_sseq2 f1_sseq2 a_wss p_dfbi2 f0_sseq2 f1_sseq2 a_wss f1_sseq2 f0_sseq2 a_wss a_wa f2_sseq2 f0_sseq2 a_wss f2_sseq2 f1_sseq2 a_wss a_wi f2_sseq2 f1_sseq2 a_wss f2_sseq2 f0_sseq2 a_wss a_wi a_wa f0_sseq2 f1_sseq2 a_wceq f2_sseq2 f0_sseq2 a_wss f2_sseq2 f1_sseq2 a_wss a_wb p_3imtr4i $.
$}

$(Equality theorem for the subclass relationship.  (Contributed by NM,
     31-May-1999.) $)

${
	$v A B C D  $.
	f0_sseq12 $f class A $.
	f1_sseq12 $f class B $.
	f2_sseq12 $f class C $.
	f3_sseq12 $f class D $.
	p_sseq12 $p |- ( ( A = B /\ C = D ) -> ( A C_ C <-> B C_ D ) ) $= f0_sseq12 f1_sseq12 f2_sseq12 p_sseq1 f2_sseq12 f3_sseq12 f1_sseq12 p_sseq2 f0_sseq12 f1_sseq12 a_wceq f0_sseq12 f2_sseq12 a_wss f1_sseq12 f2_sseq12 a_wss f2_sseq12 f3_sseq12 a_wceq f1_sseq12 f3_sseq12 a_wss p_sylan9bb $.
$}

$(An equality inference for the subclass relationship.  (Contributed by
       NM, 18-Aug-1993.) $)

${
	$v A B C  $.
	f0_sseq1i $f class A $.
	f1_sseq1i $f class B $.
	f2_sseq1i $f class C $.
	e0_sseq1i $e |- A = B $.
	p_sseq1i $p |- ( A C_ C <-> B C_ C ) $= e0_sseq1i f0_sseq1i f1_sseq1i f2_sseq1i p_sseq1 f0_sseq1i f1_sseq1i a_wceq f0_sseq1i f2_sseq1i a_wss f1_sseq1i f2_sseq1i a_wss a_wb a_ax-mp $.
$}

$(An equality inference for the subclass relationship.  (Contributed by
       NM, 30-Aug-1993.) $)

${
	$v A B C  $.
	f0_sseq2i $f class A $.
	f1_sseq2i $f class B $.
	f2_sseq2i $f class C $.
	e0_sseq2i $e |- A = B $.
	p_sseq2i $p |- ( C C_ A <-> C C_ B ) $= e0_sseq2i f0_sseq2i f1_sseq2i f2_sseq2i p_sseq2 f0_sseq2i f1_sseq2i a_wceq f2_sseq2i f0_sseq2i a_wss f2_sseq2i f1_sseq2i a_wss a_wb a_ax-mp $.
$}

$(An equality inference for the subclass relationship.  (Contributed by
         NM, 31-May-1999.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)

${
	$v A B C D  $.
	f0_sseq12i $f class A $.
	f1_sseq12i $f class B $.
	f2_sseq12i $f class C $.
	f3_sseq12i $f class D $.
	e0_sseq12i $e |- A = B $.
	e1_sseq12i $e |- C = D $.
	p_sseq12i $p |- ( A C_ C <-> B C_ D ) $= e0_sseq12i e1_sseq12i f0_sseq12i f1_sseq12i f2_sseq12i f3_sseq12i p_sseq12 f0_sseq12i f1_sseq12i a_wceq f2_sseq12i f3_sseq12i a_wceq f0_sseq12i f2_sseq12i a_wss f1_sseq12i f3_sseq12i a_wss a_wb p_mp2an $.
$}

$(An equality deduction for the subclass relationship.  (Contributed by
       NM, 14-Aug-1994.) $)

${
	$v ph A B C  $.
	f0_sseq1d $f wff ph $.
	f1_sseq1d $f class A $.
	f2_sseq1d $f class B $.
	f3_sseq1d $f class C $.
	e0_sseq1d $e |- ( ph -> A = B ) $.
	p_sseq1d $p |- ( ph -> ( A C_ C <-> B C_ C ) ) $= e0_sseq1d f1_sseq1d f2_sseq1d f3_sseq1d p_sseq1 f0_sseq1d f1_sseq1d f2_sseq1d a_wceq f1_sseq1d f3_sseq1d a_wss f2_sseq1d f3_sseq1d a_wss a_wb p_syl $.
$}

$(An equality deduction for the subclass relationship.  (Contributed by
       NM, 14-Aug-1994.) $)

${
	$v ph A B C  $.
	f0_sseq2d $f wff ph $.
	f1_sseq2d $f class A $.
	f2_sseq2d $f class B $.
	f3_sseq2d $f class C $.
	e0_sseq2d $e |- ( ph -> A = B ) $.
	p_sseq2d $p |- ( ph -> ( C C_ A <-> C C_ B ) ) $= e0_sseq2d f1_sseq2d f2_sseq2d f3_sseq2d p_sseq2 f0_sseq2d f1_sseq2d f2_sseq2d a_wceq f3_sseq2d f1_sseq2d a_wss f3_sseq2d f2_sseq2d a_wss a_wb p_syl $.
$}

$(An equality deduction for the subclass relationship.  (Contributed by
         NM, 31-May-1999.) $)

${
	$v ph A B C D  $.
	f0_sseq12d $f wff ph $.
	f1_sseq12d $f class A $.
	f2_sseq12d $f class B $.
	f3_sseq12d $f class C $.
	f4_sseq12d $f class D $.
	e0_sseq12d $e |- ( ph -> A = B ) $.
	e1_sseq12d $e |- ( ph -> C = D ) $.
	p_sseq12d $p |- ( ph -> ( A C_ C <-> B C_ D ) ) $= e0_sseq12d f0_sseq12d f1_sseq12d f2_sseq12d f3_sseq12d p_sseq1d e1_sseq12d f0_sseq12d f3_sseq12d f4_sseq12d f2_sseq12d p_sseq2d f0_sseq12d f1_sseq12d f3_sseq12d a_wss f2_sseq12d f3_sseq12d a_wss f2_sseq12d f4_sseq12d a_wss p_bitrd $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 16-Jul-1995.) $)

${
	$v A B C  $.
	f0_eqsstri $f class A $.
	f1_eqsstri $f class B $.
	f2_eqsstri $f class C $.
	e0_eqsstri $e |- A = B $.
	e1_eqsstri $e |- B C_ C $.
	p_eqsstri $p |- A C_ C $= e1_eqsstri e0_eqsstri f0_eqsstri f1_eqsstri f2_eqsstri p_sseq1i f0_eqsstri f2_eqsstri a_wss f1_eqsstri f2_eqsstri a_wss p_mpbir $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 19-Oct-1999.) $)

${
	$v A B C  $.
	f0_eqsstr3i $f class A $.
	f1_eqsstr3i $f class B $.
	f2_eqsstr3i $f class C $.
	e0_eqsstr3i $e |- B = A $.
	e1_eqsstr3i $e |- B C_ C $.
	p_eqsstr3i $p |- A C_ C $= e0_eqsstr3i f1_eqsstr3i f0_eqsstr3i p_eqcomi e1_eqsstr3i f0_eqsstr3i f1_eqsstr3i f2_eqsstr3i p_eqsstri $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 28-Jul-1995.) $)

${
	$v A B C  $.
	f0_sseqtri $f class A $.
	f1_sseqtri $f class B $.
	f2_sseqtri $f class C $.
	e0_sseqtri $e |- A C_ B $.
	e1_sseqtri $e |- B = C $.
	p_sseqtri $p |- A C_ C $= e0_sseqtri e1_sseqtri f1_sseqtri f2_sseqtri f0_sseqtri p_sseq2i f0_sseqtri f1_sseqtri a_wss f0_sseqtri f2_sseqtri a_wss p_mpbi $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 4-Apr-1995.) $)

${
	$v A B C  $.
	f0_sseqtr4i $f class A $.
	f1_sseqtr4i $f class B $.
	f2_sseqtr4i $f class C $.
	e0_sseqtr4i $e |- A C_ B $.
	e1_sseqtr4i $e |- C = B $.
	p_sseqtr4i $p |- A C_ C $= e0_sseqtr4i e1_sseqtr4i f2_sseqtr4i f1_sseqtr4i p_eqcomi f0_sseqtr4i f1_sseqtr4i f2_sseqtr4i p_sseqtri $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_eqsstrd $f wff ph $.
	f1_eqsstrd $f class A $.
	f2_eqsstrd $f class B $.
	f3_eqsstrd $f class C $.
	e0_eqsstrd $e |- ( ph -> A = B ) $.
	e1_eqsstrd $e |- ( ph -> B C_ C ) $.
	p_eqsstrd $p |- ( ph -> A C_ C ) $= e1_eqsstrd e0_eqsstrd f0_eqsstrd f1_eqsstrd f2_eqsstrd f3_eqsstrd p_sseq1d f0_eqsstrd f1_eqsstrd f3_eqsstrd a_wss f2_eqsstrd f3_eqsstrd a_wss p_mpbird $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_eqsstr3d $f wff ph $.
	f1_eqsstr3d $f class A $.
	f2_eqsstr3d $f class B $.
	f3_eqsstr3d $f class C $.
	e0_eqsstr3d $e |- ( ph -> B = A ) $.
	e1_eqsstr3d $e |- ( ph -> B C_ C ) $.
	p_eqsstr3d $p |- ( ph -> A C_ C ) $= e0_eqsstr3d f0_eqsstr3d f2_eqsstr3d f1_eqsstr3d p_eqcomd e1_eqsstr3d f0_eqsstr3d f1_eqsstr3d f2_eqsstr3d f3_eqsstr3d p_eqsstrd $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_sseqtrd $f wff ph $.
	f1_sseqtrd $f class A $.
	f2_sseqtrd $f class B $.
	f3_sseqtrd $f class C $.
	e0_sseqtrd $e |- ( ph -> A C_ B ) $.
	e1_sseqtrd $e |- ( ph -> B = C ) $.
	p_sseqtrd $p |- ( ph -> A C_ C ) $= e0_sseqtrd e1_sseqtrd f0_sseqtrd f2_sseqtrd f3_sseqtrd f1_sseqtrd p_sseq2d f0_sseqtrd f1_sseqtrd f2_sseqtrd a_wss f1_sseqtrd f3_sseqtrd a_wss p_mpbid $.
$}

$(Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_sseqtr4d $f wff ph $.
	f1_sseqtr4d $f class A $.
	f2_sseqtr4d $f class B $.
	f3_sseqtr4d $f class C $.
	e0_sseqtr4d $e |- ( ph -> A C_ B ) $.
	e1_sseqtr4d $e |- ( ph -> C = B ) $.
	p_sseqtr4d $p |- ( ph -> A C_ C ) $= e0_sseqtr4d e1_sseqtr4d f0_sseqtr4d f3_sseqtr4d f2_sseqtr4d p_eqcomd f0_sseqtr4d f1_sseqtr4d f2_sseqtr4d f3_sseqtr4d p_sseqtrd $.
$}

$(Substitution of equality in both sides of a subclass relationship.
       (Contributed by NM, 13-Jan-1996.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)

${
	$v A B C D  $.
	f0_3sstr3i $f class A $.
	f1_3sstr3i $f class B $.
	f2_3sstr3i $f class C $.
	f3_3sstr3i $f class D $.
	e0_3sstr3i $e |- A C_ B $.
	e1_3sstr3i $e |- A = C $.
	e2_3sstr3i $e |- B = D $.
	p_3sstr3i $p |- C C_ D $= e0_3sstr3i e1_3sstr3i e2_3sstr3i f0_3sstr3i f2_3sstr3i f1_3sstr3i f3_3sstr3i p_sseq12i f0_3sstr3i f1_3sstr3i a_wss f2_3sstr3i f3_3sstr3i a_wss p_mpbi $.
$}

$(Substitution of equality in both sides of a subclass relationship.
       (Contributed by NM, 13-Jan-1996.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)

${
	$v A B C D  $.
	f0_3sstr4i $f class A $.
	f1_3sstr4i $f class B $.
	f2_3sstr4i $f class C $.
	f3_3sstr4i $f class D $.
	e0_3sstr4i $e |- A C_ B $.
	e1_3sstr4i $e |- C = A $.
	e2_3sstr4i $e |- D = B $.
	p_3sstr4i $p |- C C_ D $= e0_3sstr4i e1_3sstr4i e2_3sstr4i f2_3sstr4i f0_3sstr4i f3_3sstr4i f1_3sstr4i p_sseq12i f2_3sstr4i f3_3sstr4i a_wss f0_3sstr4i f1_3sstr4i a_wss p_mpbir $.
$}

$(Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 1-Oct-2000.) $)

${
	$v ph A B C D  $.
	f0_3sstr3g $f wff ph $.
	f1_3sstr3g $f class A $.
	f2_3sstr3g $f class B $.
	f3_3sstr3g $f class C $.
	f4_3sstr3g $f class D $.
	e0_3sstr3g $e |- ( ph -> A C_ B ) $.
	e1_3sstr3g $e |- A = C $.
	e2_3sstr3g $e |- B = D $.
	p_3sstr3g $p |- ( ph -> C C_ D ) $= e0_3sstr3g e1_3sstr3g e2_3sstr3g f1_3sstr3g f3_3sstr3g f2_3sstr3g f4_3sstr3g p_sseq12i f0_3sstr3g f1_3sstr3g f2_3sstr3g a_wss f3_3sstr3g f4_3sstr3g a_wss p_sylib $.
$}

$(Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 16-Aug-1994.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)

${
	$v ph A B C D  $.
	f0_3sstr4g $f wff ph $.
	f1_3sstr4g $f class A $.
	f2_3sstr4g $f class B $.
	f3_3sstr4g $f class C $.
	f4_3sstr4g $f class D $.
	e0_3sstr4g $e |- ( ph -> A C_ B ) $.
	e1_3sstr4g $e |- C = A $.
	e2_3sstr4g $e |- D = B $.
	p_3sstr4g $p |- ( ph -> C C_ D ) $= e0_3sstr4g e1_3sstr4g e2_3sstr4g f3_3sstr4g f1_3sstr4g f4_3sstr4g f2_3sstr4g p_sseq12i f0_3sstr4g f1_3sstr4g f2_3sstr4g a_wss f3_3sstr4g f4_3sstr4g a_wss p_sylibr $.
$}

$(Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 1-Oct-2000.) $)

${
	$v ph A B C D  $.
	f0_3sstr3d $f wff ph $.
	f1_3sstr3d $f class A $.
	f2_3sstr3d $f class B $.
	f3_3sstr3d $f class C $.
	f4_3sstr3d $f class D $.
	e0_3sstr3d $e |- ( ph -> A C_ B ) $.
	e1_3sstr3d $e |- ( ph -> A = C ) $.
	e2_3sstr3d $e |- ( ph -> B = D ) $.
	p_3sstr3d $p |- ( ph -> C C_ D ) $= e0_3sstr3d e1_3sstr3d e2_3sstr3d f0_3sstr3d f1_3sstr3d f3_3sstr3d f2_3sstr3d f4_3sstr3d p_sseq12d f0_3sstr3d f1_3sstr3d f2_3sstr3d a_wss f3_3sstr3d f4_3sstr3d a_wss p_mpbid $.
$}

$(Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 30-Nov-1995.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)

${
	$v ph A B C D  $.
	f0_3sstr4d $f wff ph $.
	f1_3sstr4d $f class A $.
	f2_3sstr4d $f class B $.
	f3_3sstr4d $f class C $.
	f4_3sstr4d $f class D $.
	e0_3sstr4d $e |- ( ph -> A C_ B ) $.
	e1_3sstr4d $e |- ( ph -> C = A ) $.
	e2_3sstr4d $e |- ( ph -> D = B ) $.
	p_3sstr4d $p |- ( ph -> C C_ D ) $= e0_3sstr4d e1_3sstr4d e2_3sstr4d f0_3sstr4d f3_3sstr4d f1_3sstr4d f4_3sstr4d f2_3sstr4d p_sseq12d f0_3sstr4d f3_3sstr4d f4_3sstr4d a_wss f1_3sstr4d f2_3sstr4d a_wss p_mpbird $.
$}

$(B chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_syl5eqss $f wff ph $.
	f1_syl5eqss $f class A $.
	f2_syl5eqss $f class B $.
	f3_syl5eqss $f class C $.
	e0_syl5eqss $e |- A = B $.
	e1_syl5eqss $e |- ( ph -> B C_ C ) $.
	p_syl5eqss $p |- ( ph -> A C_ C ) $= e1_syl5eqss e0_syl5eqss f1_syl5eqss f2_syl5eqss f3_syl5eqss p_sseq1i f0_syl5eqss f2_syl5eqss f3_syl5eqss a_wss f1_syl5eqss f3_syl5eqss a_wss p_sylibr $.
$}

$(B chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_syl5eqssr $f wff ph $.
	f1_syl5eqssr $f class A $.
	f2_syl5eqssr $f class B $.
	f3_syl5eqssr $f class C $.
	e0_syl5eqssr $e |- B = A $.
	e1_syl5eqssr $e |- ( ph -> B C_ C ) $.
	p_syl5eqssr $p |- ( ph -> A C_ C ) $= e0_syl5eqssr f2_syl5eqssr f1_syl5eqssr p_eqcomi e1_syl5eqssr f0_syl5eqssr f1_syl5eqssr f2_syl5eqssr f3_syl5eqssr p_syl5eqss $.
$}

$(A chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_syl6sseq $f wff ph $.
	f1_syl6sseq $f class A $.
	f2_syl6sseq $f class B $.
	f3_syl6sseq $f class C $.
	e0_syl6sseq $e |- ( ph -> A C_ B ) $.
	e1_syl6sseq $e |- B = C $.
	p_syl6sseq $p |- ( ph -> A C_ C ) $= e0_syl6sseq e1_syl6sseq f2_syl6sseq f3_syl6sseq f1_syl6sseq p_sseq2i f0_syl6sseq f1_syl6sseq f2_syl6sseq a_wss f1_syl6sseq f3_syl6sseq a_wss p_sylib $.
$}

$(A chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)

${
	$v ph A B C  $.
	f0_syl6sseqr $f wff ph $.
	f1_syl6sseqr $f class A $.
	f2_syl6sseqr $f class B $.
	f3_syl6sseqr $f class C $.
	e0_syl6sseqr $e |- ( ph -> A C_ B ) $.
	e1_syl6sseqr $e |- C = B $.
	p_syl6sseqr $p |- ( ph -> A C_ C ) $= e0_syl6sseqr e1_syl6sseqr f3_syl6sseqr f2_syl6sseqr p_eqcomi f0_syl6sseqr f1_syl6sseqr f2_syl6sseqr f3_syl6sseqr p_syl6sseq $.
$}

$(Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)

${
	$v ph A B C  $.
	f0_syl5sseq $f wff ph $.
	f1_syl5sseq $f class A $.
	f2_syl5sseq $f class B $.
	f3_syl5sseq $f class C $.
	e0_syl5sseq $e |- B C_ A $.
	e1_syl5sseq $e |- ( ph -> A = C ) $.
	p_syl5sseq $p |- ( ph -> B C_ C ) $= e1_syl5sseq e0_syl5sseq f1_syl5sseq f3_syl5sseq f2_syl5sseq p_sseq2 f1_syl5sseq f3_syl5sseq a_wceq f2_syl5sseq f1_syl5sseq a_wss f2_syl5sseq f3_syl5sseq a_wss p_biimpa f0_syl5sseq f1_syl5sseq f3_syl5sseq a_wceq f2_syl5sseq f1_syl5sseq a_wss f2_syl5sseq f3_syl5sseq a_wss p_sylancl $.
$}

$(Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)

${
	$v ph A B C  $.
	f0_syl5sseqr $f wff ph $.
	f1_syl5sseqr $f class A $.
	f2_syl5sseqr $f class B $.
	f3_syl5sseqr $f class C $.
	e0_syl5sseqr $e |- B C_ A $.
	e1_syl5sseqr $e |- ( ph -> C = A ) $.
	p_syl5sseqr $p |- ( ph -> B C_ C ) $= e0_syl5sseqr f2_syl5sseqr f1_syl5sseqr a_wss f0_syl5sseqr p_a1i e1_syl5sseqr f0_syl5sseqr f2_syl5sseqr f1_syl5sseqr f3_syl5sseqr p_sseqtr4d $.
$}

$(A chained subclass and equality deduction.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)

${
	$v ph A B C  $.
	f0_syl6eqss $f wff ph $.
	f1_syl6eqss $f class A $.
	f2_syl6eqss $f class B $.
	f3_syl6eqss $f class C $.
	e0_syl6eqss $e |- ( ph -> A = B ) $.
	e1_syl6eqss $e |- B C_ C $.
	p_syl6eqss $p |- ( ph -> A C_ C ) $= e0_syl6eqss e1_syl6eqss f2_syl6eqss f3_syl6eqss a_wss f0_syl6eqss p_a1i f0_syl6eqss f1_syl6eqss f2_syl6eqss f3_syl6eqss p_eqsstrd $.
$}

$(A chained subclass and equality deduction.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)

${
	$v ph A B C  $.
	f0_syl6eqssr $f wff ph $.
	f1_syl6eqssr $f class A $.
	f2_syl6eqssr $f class B $.
	f3_syl6eqssr $f class C $.
	e0_syl6eqssr $e |- ( ph -> B = A ) $.
	e1_syl6eqssr $e |- B C_ C $.
	p_syl6eqssr $p |- ( ph -> A C_ C ) $= e0_syl6eqssr f0_syl6eqssr f2_syl6eqssr f1_syl6eqssr p_eqcomd e1_syl6eqssr f0_syl6eqssr f1_syl6eqssr f2_syl6eqssr f3_syl6eqssr p_syl6eqss $.
$}

$(Equality implies the subclass relation.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)

${
	$v A B  $.
	f0_eqimss $f class A $.
	f1_eqimss $f class B $.
	p_eqimss $p |- ( A = B -> A C_ B ) $= f0_eqimss f1_eqimss p_eqss f0_eqimss f1_eqimss a_wceq f0_eqimss f1_eqimss a_wss f1_eqimss f0_eqimss a_wss p_simplbi $.
$}

$(Equality implies the subclass relation.  (Contributed by NM,
     23-Nov-2003.) $)

${
	$v A B  $.
	f0_eqimss2 $f class A $.
	f1_eqimss2 $f class B $.
	p_eqimss2 $p |- ( B = A -> A C_ B ) $= f0_eqimss2 f1_eqimss2 p_eqimss f0_eqimss2 f1_eqimss2 a_wss f0_eqimss2 f1_eqimss2 p_eqcoms $.
$}

$(Infer subclass relationship from equality.  (Contributed by NM,
       6-Jan-2007.) $)

${
	$v A B  $.
	f0_eqimssi $f class A $.
	f1_eqimssi $f class B $.
	e0_eqimssi $e |- A = B $.
	p_eqimssi $p |- A C_ B $= f0_eqimssi p_ssid e0_eqimssi f0_eqimssi f0_eqimssi f1_eqimssi p_sseqtri $.
$}

$(Infer subclass relationship from equality.  (Contributed by NM,
       7-Jan-2007.) $)

${
	$v A B  $.
	f0_eqimss2i $f class A $.
	f1_eqimss2i $f class B $.
	e0_eqimss2i $e |- A = B $.
	p_eqimss2i $p |- B C_ A $= f1_eqimss2i p_ssid e0_eqimss2i f1_eqimss2i f1_eqimss2i f0_eqimss2i p_sseqtr4i $.
$}

$(Two classes are different if they don't include the same class.
     (Contributed by NM, 23-Apr-2015.) $)

${
	$v A B C  $.
	f0_nssne1 $f class A $.
	f1_nssne1 $f class B $.
	f2_nssne1 $f class C $.
	p_nssne1 $p |- ( ( A C_ B /\ -. A C_ C ) -> B =/= C ) $= f1_nssne1 f2_nssne1 f0_nssne1 p_sseq2 f1_nssne1 f2_nssne1 a_wceq f0_nssne1 f1_nssne1 a_wss f0_nssne1 f2_nssne1 a_wss p_biimpcd f0_nssne1 f1_nssne1 a_wss f0_nssne1 f2_nssne1 a_wss f1_nssne1 f2_nssne1 p_necon3bd f0_nssne1 f1_nssne1 a_wss f0_nssne1 f2_nssne1 a_wss a_wn f1_nssne1 f2_nssne1 a_wne p_imp $.
$}

$(Two classes are different if they are not subclasses of the same class.
     (Contributed by NM, 23-Apr-2015.) $)

${
	$v A B C  $.
	f0_nssne2 $f class A $.
	f1_nssne2 $f class B $.
	f2_nssne2 $f class C $.
	p_nssne2 $p |- ( ( A C_ C /\ -. B C_ C ) -> A =/= B ) $= f0_nssne2 f1_nssne2 f2_nssne2 p_sseq1 f0_nssne2 f1_nssne2 a_wceq f0_nssne2 f2_nssne2 a_wss f1_nssne2 f2_nssne2 a_wss p_biimpcd f0_nssne2 f2_nssne2 a_wss f1_nssne2 f2_nssne2 a_wss f0_nssne2 f1_nssne2 p_necon3bd f0_nssne2 f2_nssne2 a_wss f1_nssne2 f2_nssne2 a_wss a_wn f0_nssne2 f1_nssne2 a_wne p_imp $.
$}

$(Negation of subclass relationship.  Exercise 13 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 25-Feb-1996.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_nss $f set x $.
	f1_nss $f class A $.
	f2_nss $f class B $.
	p_nss $p |- ( -. A C_ B <-> E. x ( x e. A /\ -. x e. B ) ) $= f0_nss a_sup_set_class f1_nss a_wcel f0_nss a_sup_set_class f2_nss a_wcel f0_nss p_exanali f0_nss f1_nss f2_nss p_dfss2 f0_nss a_sup_set_class f1_nss a_wcel f0_nss a_sup_set_class f2_nss a_wcel a_wn a_wa f0_nss a_wex f0_nss a_sup_set_class f1_nss a_wcel f0_nss a_sup_set_class f2_nss a_wcel a_wi f0_nss a_wal f1_nss f2_nss a_wss p_xchbinxr f0_nss a_sup_set_class f1_nss a_wcel f0_nss a_sup_set_class f2_nss a_wcel a_wn a_wa f0_nss a_wex f1_nss f2_nss a_wss a_wn p_bicomi $.
$}

$(Quantification restricted to a subclass.  (Contributed by NM,
       11-Mar-2006.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssralv $f wff ph $.
	f1_ssralv $f set x $.
	f2_ssralv $f class A $.
	f3_ssralv $f class B $.
	p_ssralv $p |- ( A C_ B -> ( A. x e. B ph -> A. x e. A ph ) ) $= f2_ssralv f3_ssralv f1_ssralv a_sup_set_class p_ssel f2_ssralv f3_ssralv a_wss f1_ssralv a_sup_set_class f2_ssralv a_wcel f1_ssralv a_sup_set_class f3_ssralv a_wcel f0_ssralv p_imim1d f2_ssralv f3_ssralv a_wss f0_ssralv f0_ssralv f1_ssralv f3_ssralv f2_ssralv p_ralimdv2 $.
$}

$(Existential quantification restricted to a subclass.  (Contributed by
       NM, 11-Jan-2007.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssrexv $f wff ph $.
	f1_ssrexv $f set x $.
	f2_ssrexv $f class A $.
	f3_ssrexv $f class B $.
	p_ssrexv $p |- ( A C_ B -> ( E. x e. A ph -> E. x e. B ph ) ) $= f2_ssrexv f3_ssrexv f1_ssrexv a_sup_set_class p_ssel f2_ssrexv f3_ssrexv a_wss f1_ssrexv a_sup_set_class f2_ssrexv a_wcel f1_ssrexv a_sup_set_class f3_ssrexv a_wcel f0_ssrexv p_anim1d f2_ssrexv f3_ssrexv a_wss f0_ssrexv f0_ssrexv f1_ssrexv f2_ssrexv f3_ssrexv p_reximdv2 $.
$}

$(Restricted universal quantification on a subset in terms of superset.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)

${
	$v ph x A B  $.
	$d A x  $.
	$d B x  $.
	f0_ralss $f wff ph $.
	f1_ralss $f set x $.
	f2_ralss $f class A $.
	f3_ralss $f class B $.
	p_ralss $p |- ( A C_ B -> ( A. x e. A ph <-> A. x e. B ( x e. A -> ph ) ) ) $= f2_ralss f3_ralss f1_ralss a_sup_set_class p_ssel f2_ralss f3_ralss a_wss f1_ralss a_sup_set_class f2_ralss a_wcel f1_ralss a_sup_set_class f3_ralss a_wcel p_pm4.71rd f2_ralss f3_ralss a_wss f1_ralss a_sup_set_class f2_ralss a_wcel f1_ralss a_sup_set_class f3_ralss a_wcel f1_ralss a_sup_set_class f2_ralss a_wcel a_wa f0_ralss p_imbi1d f1_ralss a_sup_set_class f3_ralss a_wcel f1_ralss a_sup_set_class f2_ralss a_wcel f0_ralss p_impexp f2_ralss f3_ralss a_wss f1_ralss a_sup_set_class f2_ralss a_wcel f0_ralss a_wi f1_ralss a_sup_set_class f3_ralss a_wcel f1_ralss a_sup_set_class f2_ralss a_wcel a_wa f0_ralss a_wi f1_ralss a_sup_set_class f3_ralss a_wcel f1_ralss a_sup_set_class f2_ralss a_wcel f0_ralss a_wi a_wi p_syl6bb f2_ralss f3_ralss a_wss f0_ralss f1_ralss a_sup_set_class f2_ralss a_wcel f0_ralss a_wi f1_ralss f2_ralss f3_ralss p_ralbidv2 $.
$}

$(Restricted existential quantification on a subset in terms of superset.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)

${
	$v ph x A B  $.
	$d A x  $.
	$d B x  $.
	f0_rexss $f wff ph $.
	f1_rexss $f set x $.
	f2_rexss $f class A $.
	f3_rexss $f class B $.
	p_rexss $p |- ( A C_ B -> ( E. x e. A ph <-> E. x e. B ( x e. A /\ ph ) ) ) $= f2_rexss f3_rexss f1_rexss a_sup_set_class p_ssel f2_rexss f3_rexss a_wss f1_rexss a_sup_set_class f2_rexss a_wcel f1_rexss a_sup_set_class f3_rexss a_wcel p_pm4.71rd f2_rexss f3_rexss a_wss f1_rexss a_sup_set_class f2_rexss a_wcel f1_rexss a_sup_set_class f3_rexss a_wcel f1_rexss a_sup_set_class f2_rexss a_wcel a_wa f0_rexss p_anbi1d f1_rexss a_sup_set_class f3_rexss a_wcel f1_rexss a_sup_set_class f2_rexss a_wcel f0_rexss p_anass f2_rexss f3_rexss a_wss f1_rexss a_sup_set_class f2_rexss a_wcel f0_rexss a_wa f1_rexss a_sup_set_class f3_rexss a_wcel f1_rexss a_sup_set_class f2_rexss a_wcel a_wa f0_rexss a_wa f1_rexss a_sup_set_class f3_rexss a_wcel f1_rexss a_sup_set_class f2_rexss a_wcel f0_rexss a_wa a_wa p_syl6bb f2_rexss f3_rexss a_wss f0_rexss f1_rexss a_sup_set_class f2_rexss a_wcel f0_rexss a_wa f1_rexss f2_rexss f3_rexss p_rexbidv2 $.
$}

$(Class abstractions in a subclass relationship.  (Contributed by NM,
       3-Jul-1994.) $)

${
	$v ph ps x  $.
	$d ph  $.
	$d ps  $.
	$d x  $.
	f0_ss2ab $f wff ph $.
	f1_ss2ab $f wff ps $.
	f2_ss2ab $f set x $.
	p_ss2ab $p |- ( { x | ph } C_ { x | ps } <-> A. x ( ph -> ps ) ) $= f0_ss2ab f2_ss2ab p_nfab1 f1_ss2ab f2_ss2ab p_nfab1 f2_ss2ab f0_ss2ab f2_ss2ab a_cab f1_ss2ab f2_ss2ab a_cab p_dfss2f f0_ss2ab f2_ss2ab p_abid f1_ss2ab f2_ss2ab p_abid f2_ss2ab a_sup_set_class f0_ss2ab f2_ss2ab a_cab a_wcel f0_ss2ab f2_ss2ab a_sup_set_class f1_ss2ab f2_ss2ab a_cab a_wcel f1_ss2ab p_imbi12i f2_ss2ab a_sup_set_class f0_ss2ab f2_ss2ab a_cab a_wcel f2_ss2ab a_sup_set_class f1_ss2ab f2_ss2ab a_cab a_wcel a_wi f0_ss2ab f1_ss2ab a_wi f2_ss2ab p_albii f0_ss2ab f2_ss2ab a_cab f1_ss2ab f2_ss2ab a_cab a_wss f2_ss2ab a_sup_set_class f0_ss2ab f2_ss2ab a_cab a_wcel f2_ss2ab a_sup_set_class f1_ss2ab f2_ss2ab a_cab a_wcel a_wi f2_ss2ab a_wal f0_ss2ab f1_ss2ab a_wi f2_ss2ab a_wal p_bitri $.
$}

$(Class abstraction in a subclass relationship.  (Contributed by NM,
       16-Aug-2006.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_abss $f wff ph $.
	f1_abss $f set x $.
	f2_abss $f class A $.
	p_abss $p |- ( { x | ph } C_ A <-> A. x ( ph -> x e. A ) ) $= f1_abss f2_abss p_abid2 f1_abss a_sup_set_class f2_abss a_wcel f1_abss a_cab f2_abss f0_abss f1_abss a_cab p_sseq2i f0_abss f1_abss a_sup_set_class f2_abss a_wcel f1_abss p_ss2ab f0_abss f1_abss a_cab f2_abss a_wss f0_abss f1_abss a_cab f1_abss a_sup_set_class f2_abss a_wcel f1_abss a_cab a_wss f0_abss f1_abss a_sup_set_class f2_abss a_wcel a_wi f1_abss a_wal p_bitr3i $.
$}

$(Subclass of a class abstraction.  (Contributed by NM, 16-Aug-2006.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_ssab $f wff ph $.
	f1_ssab $f set x $.
	f2_ssab $f class A $.
	p_ssab $p |- ( A C_ { x | ph } <-> A. x ( x e. A -> ph ) ) $= f1_ssab f2_ssab p_abid2 f1_ssab a_sup_set_class f2_ssab a_wcel f1_ssab a_cab f2_ssab f0_ssab f1_ssab a_cab p_sseq1i f1_ssab a_sup_set_class f2_ssab a_wcel f0_ssab f1_ssab p_ss2ab f2_ssab f0_ssab f1_ssab a_cab a_wss f1_ssab a_sup_set_class f2_ssab a_wcel f1_ssab a_cab f0_ssab f1_ssab a_cab a_wss f1_ssab a_sup_set_class f2_ssab a_wcel f0_ssab a_wi f1_ssab a_wal p_bitr3i $.
$}

$(The relation for a subclass of a class abstraction is equivalent to
       restricted quantification.  (Contributed by NM, 6-Sep-2006.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_ssabral $f wff ph $.
	f1_ssabral $f set x $.
	f2_ssabral $f class A $.
	p_ssabral $p |- ( A C_ { x | ph } <-> A. x e. A ph ) $= f0_ssabral f1_ssabral f2_ssabral p_ssab f0_ssabral f1_ssabral f2_ssabral a_df-ral f2_ssabral f0_ssabral f1_ssabral a_cab a_wss f1_ssabral a_sup_set_class f2_ssabral a_wcel f0_ssabral a_wi f1_ssabral a_wal f0_ssabral f1_ssabral f2_ssabral a_wral p_bitr4i $.
$}

$(Inference of abstraction subclass from implication.  (Contributed by NM,
       31-Mar-1995.) $)

${
	$v ph ps x  $.
	f0_ss2abi $f wff ph $.
	f1_ss2abi $f wff ps $.
	f2_ss2abi $f set x $.
	e0_ss2abi $e |- ( ph -> ps ) $.
	p_ss2abi $p |- { x | ph } C_ { x | ps } $= f0_ss2abi f1_ss2abi f2_ss2abi p_ss2ab e0_ss2abi f0_ss2abi f2_ss2abi a_cab f1_ss2abi f2_ss2abi a_cab a_wss f0_ss2abi f1_ss2abi a_wi f2_ss2abi p_mpgbir $.
$}

$(Deduction of abstraction subclass from implication.  (Contributed by NM,
       29-Jul-2011.) $)

${
	$v ph ps ch x  $.
	$d x ph  $.
	f0_ss2abdv $f wff ph $.
	f1_ss2abdv $f wff ps $.
	f2_ss2abdv $f wff ch $.
	f3_ss2abdv $f set x $.
	e0_ss2abdv $e |- ( ph -> ( ps -> ch ) ) $.
	p_ss2abdv $p |- ( ph -> { x | ps } C_ { x | ch } ) $= e0_ss2abdv f0_ss2abdv f1_ss2abdv f2_ss2abdv a_wi f3_ss2abdv p_alrimiv f1_ss2abdv f2_ss2abdv f3_ss2abdv p_ss2ab f0_ss2abdv f1_ss2abdv f2_ss2abdv a_wi f3_ss2abdv a_wal f1_ss2abdv f3_ss2abdv a_cab f2_ss2abdv f3_ss2abdv a_cab a_wss p_sylibr $.
$}

$(Deduction of abstraction subclass from implication.  (Contributed by NM,
       20-Jan-2006.) $)

${
	$v ph ps x A  $.
	$d x ph  $.
	$d x A  $.
	f0_abssdv $f wff ph $.
	f1_abssdv $f wff ps $.
	f2_abssdv $f set x $.
	f3_abssdv $f class A $.
	e0_abssdv $e |- ( ph -> ( ps -> x e. A ) ) $.
	p_abssdv $p |- ( ph -> { x | ps } C_ A ) $= e0_abssdv f0_abssdv f1_abssdv f2_abssdv a_sup_set_class f3_abssdv a_wcel a_wi f2_abssdv p_alrimiv f1_abssdv f2_abssdv f3_abssdv p_abss f0_abssdv f1_abssdv f2_abssdv a_sup_set_class f3_abssdv a_wcel a_wi f2_abssdv a_wal f1_abssdv f2_abssdv a_cab f3_abssdv a_wss p_sylibr $.
$}

$(Inference of abstraction subclass from implication.  (Contributed by NM,
       20-Jan-2006.) $)

${
	$v ph x A  $.
	$d x A  $.
	f0_abssi $f wff ph $.
	f1_abssi $f set x $.
	f2_abssi $f class A $.
	e0_abssi $e |- ( ph -> x e. A ) $.
	p_abssi $p |- { x | ph } C_ A $= e0_abssi f0_abssi f1_abssi a_sup_set_class f2_abssi a_wcel f1_abssi p_ss2abi f1_abssi f2_abssi p_abid2 f0_abssi f1_abssi a_cab f1_abssi a_sup_set_class f2_abssi a_wcel f1_abssi a_cab f2_abssi p_sseqtri $.
$}

$(Restricted abstraction classes in a subclass relationship.  (Contributed
     by NM, 30-May-1999.) $)

${
	$v ph ps x A  $.
	f0_ss2rab $f wff ph $.
	f1_ss2rab $f wff ps $.
	f2_ss2rab $f set x $.
	f3_ss2rab $f class A $.
	p_ss2rab $p |- ( { x e. A | ph } C_ { x e. A | ps } <-> A. x e. A ( ph -> ps ) ) $= f0_ss2rab f2_ss2rab f3_ss2rab a_df-rab f1_ss2rab f2_ss2rab f3_ss2rab a_df-rab f0_ss2rab f2_ss2rab f3_ss2rab a_crab f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab a_wa f2_ss2rab a_cab f1_ss2rab f2_ss2rab f3_ss2rab a_crab f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f1_ss2rab a_wa f2_ss2rab a_cab p_sseq12i f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab a_wa f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f1_ss2rab a_wa f2_ss2rab p_ss2ab f0_ss2rab f1_ss2rab a_wi f2_ss2rab f3_ss2rab a_df-ral f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab f1_ss2rab p_imdistan f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab f1_ss2rab a_wi a_wi f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab a_wa f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f1_ss2rab a_wa a_wi f2_ss2rab p_albii f0_ss2rab f1_ss2rab a_wi f2_ss2rab f3_ss2rab a_wral f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab f1_ss2rab a_wi a_wi f2_ss2rab a_wal f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab a_wa f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f1_ss2rab a_wa a_wi f2_ss2rab a_wal p_bitr2i f0_ss2rab f2_ss2rab f3_ss2rab a_crab f1_ss2rab f2_ss2rab f3_ss2rab a_crab a_wss f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab a_wa f2_ss2rab a_cab f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f1_ss2rab a_wa f2_ss2rab a_cab a_wss f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f0_ss2rab a_wa f2_ss2rab a_sup_set_class f3_ss2rab a_wcel f1_ss2rab a_wa a_wi f2_ss2rab a_wal f0_ss2rab f1_ss2rab a_wi f2_ss2rab f3_ss2rab a_wral p_3bitri $.
$}

$(Restricted class abstraction in a subclass relationship.  (Contributed
       by NM, 16-Aug-2006.) $)

${
	$v ph x A B  $.
	$d x B  $.
	f0_rabss $f wff ph $.
	f1_rabss $f set x $.
	f2_rabss $f class A $.
	f3_rabss $f class B $.
	p_rabss $p |- ( { x e. A | ph } C_ B <-> A. x e. A ( ph -> x e. B ) ) $= f0_rabss f1_rabss f2_rabss a_df-rab f0_rabss f1_rabss f2_rabss a_crab f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss a_wa f1_rabss a_cab f3_rabss p_sseq1i f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss a_wa f1_rabss f3_rabss p_abss f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss f1_rabss a_sup_set_class f3_rabss a_wcel p_impexp f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss a_wa f1_rabss a_sup_set_class f3_rabss a_wcel a_wi f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss f1_rabss a_sup_set_class f3_rabss a_wcel a_wi a_wi f1_rabss p_albii f0_rabss f1_rabss a_sup_set_class f3_rabss a_wcel a_wi f1_rabss f2_rabss a_df-ral f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss a_wa f1_rabss a_sup_set_class f3_rabss a_wcel a_wi f1_rabss a_wal f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss f1_rabss a_sup_set_class f3_rabss a_wcel a_wi a_wi f1_rabss a_wal f0_rabss f1_rabss a_sup_set_class f3_rabss a_wcel a_wi f1_rabss f2_rabss a_wral p_bitr4i f0_rabss f1_rabss f2_rabss a_crab f3_rabss a_wss f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss a_wa f1_rabss a_cab f3_rabss a_wss f1_rabss a_sup_set_class f2_rabss a_wcel f0_rabss a_wa f1_rabss a_sup_set_class f3_rabss a_wcel a_wi f1_rabss a_wal f0_rabss f1_rabss a_sup_set_class f3_rabss a_wcel a_wi f1_rabss f2_rabss a_wral p_3bitri $.
$}

$(Subclass of a restricted class abstraction.  (Contributed by NM,
       16-Aug-2006.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_ssrab $f wff ph $.
	f1_ssrab $f set x $.
	f2_ssrab $f class A $.
	f3_ssrab $f class B $.
	p_ssrab $p |- ( B C_ { x e. A | ph } <-> ( B C_ A /\ A. x e. B ph ) ) $= f0_ssrab f1_ssrab f2_ssrab a_df-rab f0_ssrab f1_ssrab f2_ssrab a_crab f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa f1_ssrab a_cab f3_ssrab p_sseq2i f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa f1_ssrab f3_ssrab p_ssab f1_ssrab f3_ssrab f2_ssrab p_dfss3 f3_ssrab f2_ssrab a_wss f1_ssrab a_sup_set_class f2_ssrab a_wcel f1_ssrab f3_ssrab a_wral f0_ssrab f1_ssrab f3_ssrab a_wral p_anbi1i f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab f1_ssrab f3_ssrab p_r19.26 f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa f1_ssrab f3_ssrab a_df-ral f3_ssrab f2_ssrab a_wss f0_ssrab f1_ssrab f3_ssrab a_wral a_wa f1_ssrab a_sup_set_class f2_ssrab a_wcel f1_ssrab f3_ssrab a_wral f0_ssrab f1_ssrab f3_ssrab a_wral a_wa f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa f1_ssrab f3_ssrab a_wral f1_ssrab a_sup_set_class f3_ssrab a_wcel f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa a_wi f1_ssrab a_wal p_3bitr2ri f3_ssrab f0_ssrab f1_ssrab f2_ssrab a_crab a_wss f3_ssrab f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa f1_ssrab a_cab a_wss f1_ssrab a_sup_set_class f3_ssrab a_wcel f1_ssrab a_sup_set_class f2_ssrab a_wcel f0_ssrab a_wa a_wi f1_ssrab a_wal f3_ssrab f2_ssrab a_wss f0_ssrab f1_ssrab f3_ssrab a_wral a_wa p_3bitri $.
$}

$(Subclass of a restricted class abstraction (deduction rule).
       (Contributed by NM, 31-Aug-2006.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ph  $.
	f0_ssrabdv $f wff ph $.
	f1_ssrabdv $f wff ps $.
	f2_ssrabdv $f set x $.
	f3_ssrabdv $f class A $.
	f4_ssrabdv $f class B $.
	e0_ssrabdv $e |- ( ph -> B C_ A ) $.
	e1_ssrabdv $e |- ( ( ph /\ x e. B ) -> ps ) $.
	p_ssrabdv $p |- ( ph -> B C_ { x e. A | ps } ) $= e0_ssrabdv e1_ssrabdv f0_ssrabdv f1_ssrabdv f2_ssrabdv f4_ssrabdv p_ralrimiva f1_ssrabdv f2_ssrabdv f3_ssrabdv f4_ssrabdv p_ssrab f0_ssrabdv f4_ssrabdv f3_ssrabdv a_wss f1_ssrabdv f2_ssrabdv f4_ssrabdv a_wral f4_ssrabdv f1_ssrabdv f2_ssrabdv f3_ssrabdv a_crab a_wss p_sylanbrc $.
$}

$(Subclass of a restricted class abstraction (deduction rule).
       (Contributed by NM, 2-Feb-2015.) $)

${
	$v ph ps x A B  $.
	$d x B  $.
	$d x ph  $.
	f0_rabssdv $f wff ph $.
	f1_rabssdv $f wff ps $.
	f2_rabssdv $f set x $.
	f3_rabssdv $f class A $.
	f4_rabssdv $f class B $.
	e0_rabssdv $e |- ( ( ph /\ x e. A /\ ps ) -> x e. B ) $.
	p_rabssdv $p |- ( ph -> { x e. A | ps } C_ B ) $= e0_rabssdv f0_rabssdv f2_rabssdv a_sup_set_class f3_rabssdv a_wcel f1_rabssdv f2_rabssdv a_sup_set_class f4_rabssdv a_wcel p_3exp f0_rabssdv f1_rabssdv f2_rabssdv a_sup_set_class f4_rabssdv a_wcel a_wi f2_rabssdv f3_rabssdv p_ralrimiv f1_rabssdv f2_rabssdv f3_rabssdv f4_rabssdv p_rabss f0_rabssdv f1_rabssdv f2_rabssdv a_sup_set_class f4_rabssdv a_wcel a_wi f2_rabssdv f3_rabssdv a_wral f1_rabssdv f2_rabssdv f3_rabssdv a_crab f4_rabssdv a_wss p_sylibr $.
$}

$(Deduction of restricted abstraction subclass from implication.
       (Contributed by NM, 30-May-2006.) $)

${
	$v ph ps ch x A  $.
	$d x ph  $.
	f0_ss2rabdv $f wff ph $.
	f1_ss2rabdv $f wff ps $.
	f2_ss2rabdv $f wff ch $.
	f3_ss2rabdv $f set x $.
	f4_ss2rabdv $f class A $.
	e0_ss2rabdv $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	p_ss2rabdv $p |- ( ph -> { x e. A | ps } C_ { x e. A | ch } ) $= e0_ss2rabdv f0_ss2rabdv f1_ss2rabdv f2_ss2rabdv a_wi f3_ss2rabdv f4_ss2rabdv p_ralrimiva f1_ss2rabdv f2_ss2rabdv f3_ss2rabdv f4_ss2rabdv p_ss2rab f0_ss2rabdv f1_ss2rabdv f2_ss2rabdv a_wi f3_ss2rabdv f4_ss2rabdv a_wral f1_ss2rabdv f3_ss2rabdv f4_ss2rabdv a_crab f2_ss2rabdv f3_ss2rabdv f4_ss2rabdv a_crab a_wss p_sylibr $.
$}

$(Inference of restricted abstraction subclass from implication.
       (Contributed by NM, 14-Oct-1999.) $)

${
	$v ph ps x A  $.
	f0_ss2rabi $f wff ph $.
	f1_ss2rabi $f wff ps $.
	f2_ss2rabi $f set x $.
	f3_ss2rabi $f class A $.
	e0_ss2rabi $e |- ( x e. A -> ( ph -> ps ) ) $.
	p_ss2rabi $p |- { x e. A | ph } C_ { x e. A | ps } $= f0_ss2rabi f1_ss2rabi f2_ss2rabi f3_ss2rabi p_ss2rab e0_ss2rabi f0_ss2rabi f2_ss2rabi f3_ss2rabi a_crab f1_ss2rabi f2_ss2rabi f3_ss2rabi a_crab a_wss f0_ss2rabi f1_ss2rabi a_wi f2_ss2rabi f3_ss2rabi p_mprgbir $.
$}

$(Subclass law for restricted abstraction.  (Contributed by NM,
       18-Dec-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v ph x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rabss2 $f wff ph $.
	f1_rabss2 $f set x $.
	f2_rabss2 $f class A $.
	f3_rabss2 $f class B $.
	p_rabss2 $p |- ( A C_ B -> { x e. A | ph } C_ { x e. B | ph } ) $= f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f1_rabss2 a_sup_set_class f3_rabss2 a_wcel f0_rabss2 p_pm3.45 f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f1_rabss2 a_sup_set_class f3_rabss2 a_wcel a_wi f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_sup_set_class f3_rabss2 a_wcel f0_rabss2 a_wa a_wi f1_rabss2 p_alimi f1_rabss2 f2_rabss2 f3_rabss2 p_dfss2 f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_sup_set_class f3_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 p_ss2ab f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f1_rabss2 a_sup_set_class f3_rabss2 a_wcel a_wi f1_rabss2 a_wal f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_sup_set_class f3_rabss2 a_wcel f0_rabss2 a_wa a_wi f1_rabss2 a_wal f2_rabss2 f3_rabss2 a_wss f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_cab f1_rabss2 a_sup_set_class f3_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_cab a_wss p_3imtr4i f0_rabss2 f1_rabss2 f2_rabss2 a_df-rab f0_rabss2 f1_rabss2 f3_rabss2 a_df-rab f2_rabss2 f3_rabss2 a_wss f1_rabss2 a_sup_set_class f2_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_cab f1_rabss2 a_sup_set_class f3_rabss2 a_wcel f0_rabss2 a_wa f1_rabss2 a_cab f0_rabss2 f1_rabss2 f2_rabss2 a_crab f0_rabss2 f1_rabss2 f3_rabss2 a_crab p_3sstr4g $.
$}

$(Subclass relation for the restriction of a class abstraction.
       (Contributed by NM, 31-Mar-1995.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x  $.
	f0_ssab2 $f wff ph $.
	f1_ssab2 $f set x $.
	f2_ssab2 $f class A $.
	p_ssab2 $p |- { x | ( x e. A /\ ph ) } C_ A $= f1_ssab2 a_sup_set_class f2_ssab2 a_wcel f0_ssab2 p_simpl f1_ssab2 a_sup_set_class f2_ssab2 a_wcel f0_ssab2 a_wa f1_ssab2 f2_ssab2 p_abssi $.
$}

$(Subclass relation for a restricted class.  (Contributed by NM,
       19-Mar-1997.) $)

${
	$v ph x A  $.
	$d x A  $.
	$d x  $.
	f0_ssrab2 $f wff ph $.
	f1_ssrab2 $f set x $.
	f2_ssrab2 $f class A $.
	p_ssrab2 $p |- { x e. A | ph } C_ A $= f0_ssrab2 f1_ssrab2 f2_ssrab2 a_df-rab f0_ssrab2 f1_ssrab2 f2_ssrab2 p_ssab2 f0_ssrab2 f1_ssrab2 f2_ssrab2 a_crab f1_ssrab2 a_sup_set_class f2_ssrab2 a_wcel f0_ssrab2 a_wa f1_ssrab2 a_cab f2_ssrab2 p_eqsstri $.
$}

$(A restricted class is a subclass of the corresponding unrestricted class.
     (Contributed by Mario Carneiro, 23-Dec-2016.) $)

${
	$v ph x A  $.
	f0_rabssab $f wff ph $.
	f1_rabssab $f set x $.
	f2_rabssab $f class A $.
	p_rabssab $p |- { x e. A | ph } C_ { x | ph } $= f0_rabssab f1_rabssab f2_rabssab a_df-rab f1_rabssab a_sup_set_class f2_rabssab a_wcel f0_rabssab p_simpr f1_rabssab a_sup_set_class f2_rabssab a_wcel f0_rabssab a_wa f0_rabssab f1_rabssab p_ss2abi f0_rabssab f1_rabssab f2_rabssab a_crab f1_rabssab a_sup_set_class f2_rabssab a_wcel f0_rabssab a_wa f1_rabssab a_cab f0_rabssab f1_rabssab a_cab p_eqsstri $.
$}

$(A subset relationship useful for converting union to indexed union using
       ~ dfiun2 or ~ dfiun2g and intersection to indexed intersection using
       ~ dfiin2 .  (Contributed by NM, 5-Oct-2006.)  (Proof shortened by Mario
       Carneiro, 26-Sep-2015.) $)

${
	$v x y A B C D  $.
	$d x y  $.
	$d y z A  $.
	$d y z B  $.
	$d x z C  $.
	f0_uniiunlem $f set x $.
	f1_uniiunlem $f set y $.
	f2_uniiunlem $f class A $.
	f3_uniiunlem $f class B $.
	f4_uniiunlem $f class C $.
	f5_uniiunlem $f class D $.
	i0_uniiunlem $f set z $.
	p_uniiunlem $p |- ( A. x e. A B e. D -> ( A. x e. A B e. C <-> { y | E. x e. A y = B } C_ C ) ) $= f1_uniiunlem a_sup_set_class i0_uniiunlem a_sup_set_class f3_uniiunlem p_eqeq1 f1_uniiunlem a_sup_set_class i0_uniiunlem a_sup_set_class a_wceq f1_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem p_rexbidv f1_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex f1_uniiunlem i0_uniiunlem p_cbvabv f1_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex f1_uniiunlem a_cab i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem a_cab f4_uniiunlem p_sseq1i i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel f0_uniiunlem f2_uniiunlem p_r19.23v i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi f0_uniiunlem f2_uniiunlem a_wral i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem p_albii i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi f0_uniiunlem i0_uniiunlem f2_uniiunlem p_ralcom4 i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem f4_uniiunlem p_abss i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi f0_uniiunlem f2_uniiunlem a_wral i0_uniiunlem a_wal i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f0_uniiunlem f2_uniiunlem a_wral i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem a_cab f4_uniiunlem a_wss p_3bitr4i f1_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex f1_uniiunlem a_cab f4_uniiunlem a_wss i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex i0_uniiunlem a_cab f4_uniiunlem a_wss i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f0_uniiunlem f2_uniiunlem a_wral p_bitr4i f3_uniiunlem f4_uniiunlem a_wcel i0_uniiunlem p_nfv i0_uniiunlem a_sup_set_class f3_uniiunlem f4_uniiunlem p_eleq1 i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel f3_uniiunlem f4_uniiunlem a_wcel i0_uniiunlem f3_uniiunlem f5_uniiunlem p_ceqsalg f3_uniiunlem f5_uniiunlem a_wcel i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f3_uniiunlem f4_uniiunlem a_wcel a_wb f0_uniiunlem f2_uniiunlem p_ralimi i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f3_uniiunlem f4_uniiunlem a_wcel f0_uniiunlem f2_uniiunlem p_ralbi f3_uniiunlem f5_uniiunlem a_wcel f0_uniiunlem f2_uniiunlem a_wral i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f3_uniiunlem f4_uniiunlem a_wcel a_wb f0_uniiunlem f2_uniiunlem a_wral i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f0_uniiunlem f2_uniiunlem a_wral f3_uniiunlem f4_uniiunlem a_wcel f0_uniiunlem f2_uniiunlem a_wral a_wb p_syl f1_uniiunlem a_sup_set_class f3_uniiunlem a_wceq f0_uniiunlem f2_uniiunlem a_wrex f1_uniiunlem a_cab f4_uniiunlem a_wss i0_uniiunlem a_sup_set_class f3_uniiunlem a_wceq i0_uniiunlem a_sup_set_class f4_uniiunlem a_wcel a_wi i0_uniiunlem a_wal f0_uniiunlem f2_uniiunlem a_wral f3_uniiunlem f5_uniiunlem a_wcel f0_uniiunlem f2_uniiunlem a_wral f3_uniiunlem f4_uniiunlem a_wcel f0_uniiunlem f2_uniiunlem a_wral p_syl5rbb $.
$}

$(Alternate definition of proper subclass.  (Contributed by NM,
     7-Feb-1996.) $)

${
	$v A B  $.
	f0_dfpss2 $f class A $.
	f1_dfpss2 $f class B $.
	p_dfpss2 $p |- ( A C. B <-> ( A C_ B /\ -. A = B ) ) $= f0_dfpss2 f1_dfpss2 a_df-pss f0_dfpss2 f1_dfpss2 a_df-ne f0_dfpss2 f1_dfpss2 a_wne f0_dfpss2 f1_dfpss2 a_wceq a_wn f0_dfpss2 f1_dfpss2 a_wss p_anbi2i f0_dfpss2 f1_dfpss2 a_wpss f0_dfpss2 f1_dfpss2 a_wss f0_dfpss2 f1_dfpss2 a_wne a_wa f0_dfpss2 f1_dfpss2 a_wss f0_dfpss2 f1_dfpss2 a_wceq a_wn a_wa p_bitri $.
$}

$(Alternate definition of proper subclass.  (Contributed by NM,
     7-Feb-1996.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	f0_dfpss3 $f class A $.
	f1_dfpss3 $f class B $.
	p_dfpss3 $p |- ( A C. B <-> ( A C_ B /\ -. B C_ A ) ) $= f0_dfpss3 f1_dfpss3 p_dfpss2 f0_dfpss3 f1_dfpss3 p_eqss f0_dfpss3 f1_dfpss3 a_wceq f0_dfpss3 f1_dfpss3 a_wss f1_dfpss3 f0_dfpss3 a_wss p_baib f0_dfpss3 f1_dfpss3 a_wss f0_dfpss3 f1_dfpss3 a_wceq f1_dfpss3 f0_dfpss3 a_wss p_notbid f0_dfpss3 f1_dfpss3 a_wss f0_dfpss3 f1_dfpss3 a_wceq a_wn f1_dfpss3 f0_dfpss3 a_wss a_wn p_pm5.32i f0_dfpss3 f1_dfpss3 a_wpss f0_dfpss3 f1_dfpss3 a_wss f0_dfpss3 f1_dfpss3 a_wceq a_wn a_wa f0_dfpss3 f1_dfpss3 a_wss f1_dfpss3 f0_dfpss3 a_wss a_wn a_wa p_bitri $.
$}

$(Equality theorem for proper subclass.  (Contributed by NM, 7-Feb-1996.) $)

${
	$v A B C  $.
	f0_psseq1 $f class A $.
	f1_psseq1 $f class B $.
	f2_psseq1 $f class C $.
	p_psseq1 $p |- ( A = B -> ( A C. C <-> B C. C ) ) $= f0_psseq1 f1_psseq1 f2_psseq1 p_sseq1 f0_psseq1 f1_psseq1 f2_psseq1 p_neeq1 f0_psseq1 f1_psseq1 a_wceq f0_psseq1 f2_psseq1 a_wss f1_psseq1 f2_psseq1 a_wss f0_psseq1 f2_psseq1 a_wne f1_psseq1 f2_psseq1 a_wne p_anbi12d f0_psseq1 f2_psseq1 a_df-pss f1_psseq1 f2_psseq1 a_df-pss f0_psseq1 f1_psseq1 a_wceq f0_psseq1 f2_psseq1 a_wss f0_psseq1 f2_psseq1 a_wne a_wa f1_psseq1 f2_psseq1 a_wss f1_psseq1 f2_psseq1 a_wne a_wa f0_psseq1 f2_psseq1 a_wpss f1_psseq1 f2_psseq1 a_wpss p_3bitr4g $.
$}

$(Equality theorem for proper subclass.  (Contributed by NM, 7-Feb-1996.) $)

${
	$v A B C  $.
	f0_psseq2 $f class A $.
	f1_psseq2 $f class B $.
	f2_psseq2 $f class C $.
	p_psseq2 $p |- ( A = B -> ( C C. A <-> C C. B ) ) $= f0_psseq2 f1_psseq2 f2_psseq2 p_sseq2 f0_psseq2 f1_psseq2 f2_psseq2 p_neeq2 f0_psseq2 f1_psseq2 a_wceq f2_psseq2 f0_psseq2 a_wss f2_psseq2 f1_psseq2 a_wss f2_psseq2 f0_psseq2 a_wne f2_psseq2 f1_psseq2 a_wne p_anbi12d f2_psseq2 f0_psseq2 a_df-pss f2_psseq2 f1_psseq2 a_df-pss f0_psseq2 f1_psseq2 a_wceq f2_psseq2 f0_psseq2 a_wss f2_psseq2 f0_psseq2 a_wne a_wa f2_psseq2 f1_psseq2 a_wss f2_psseq2 f1_psseq2 a_wne a_wa f2_psseq2 f0_psseq2 a_wpss f2_psseq2 f1_psseq2 a_wpss p_3bitr4g $.
$}

$(An equality inference for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)

${
	$v A B C  $.
	f0_psseq1i $f class A $.
	f1_psseq1i $f class B $.
	f2_psseq1i $f class C $.
	e0_psseq1i $e |- A = B $.
	p_psseq1i $p |- ( A C. C <-> B C. C ) $= e0_psseq1i f0_psseq1i f1_psseq1i f2_psseq1i p_psseq1 f0_psseq1i f1_psseq1i a_wceq f0_psseq1i f2_psseq1i a_wpss f1_psseq1i f2_psseq1i a_wpss a_wb a_ax-mp $.
$}

$(An equality inference for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)

${
	$v A B C  $.
	f0_psseq2i $f class A $.
	f1_psseq2i $f class B $.
	f2_psseq2i $f class C $.
	e0_psseq2i $e |- A = B $.
	p_psseq2i $p |- ( C C. A <-> C C. B ) $= e0_psseq2i f0_psseq2i f1_psseq2i f2_psseq2i p_psseq2 f0_psseq2i f1_psseq2i a_wceq f2_psseq2i f0_psseq2i a_wpss f2_psseq2i f1_psseq2i a_wpss a_wb a_ax-mp $.
$}

$(An equality inference for the proper subclass relationship.
         (Contributed by NM, 9-Jun-2004.) $)

${
	$v A B C D  $.
	f0_psseq12i $f class A $.
	f1_psseq12i $f class B $.
	f2_psseq12i $f class C $.
	f3_psseq12i $f class D $.
	e0_psseq12i $e |- A = B $.
	e1_psseq12i $e |- C = D $.
	p_psseq12i $p |- ( A C. C <-> B C. D ) $= e0_psseq12i f0_psseq12i f1_psseq12i f2_psseq12i p_psseq1i e1_psseq12i f2_psseq12i f3_psseq12i f1_psseq12i p_psseq2i f0_psseq12i f2_psseq12i a_wpss f1_psseq12i f2_psseq12i a_wpss f1_psseq12i f3_psseq12i a_wpss p_bitri $.
$}

$(An equality deduction for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)

${
	$v ph A B C  $.
	f0_psseq1d $f wff ph $.
	f1_psseq1d $f class A $.
	f2_psseq1d $f class B $.
	f3_psseq1d $f class C $.
	e0_psseq1d $e |- ( ph -> A = B ) $.
	p_psseq1d $p |- ( ph -> ( A C. C <-> B C. C ) ) $= e0_psseq1d f1_psseq1d f2_psseq1d f3_psseq1d p_psseq1 f0_psseq1d f1_psseq1d f2_psseq1d a_wceq f1_psseq1d f3_psseq1d a_wpss f2_psseq1d f3_psseq1d a_wpss a_wb p_syl $.
$}

$(An equality deduction for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)

${
	$v ph A B C  $.
	f0_psseq2d $f wff ph $.
	f1_psseq2d $f class A $.
	f2_psseq2d $f class B $.
	f3_psseq2d $f class C $.
	e0_psseq2d $e |- ( ph -> A = B ) $.
	p_psseq2d $p |- ( ph -> ( C C. A <-> C C. B ) ) $= e0_psseq2d f1_psseq2d f2_psseq2d f3_psseq2d p_psseq2 f0_psseq2d f1_psseq2d f2_psseq2d a_wceq f3_psseq2d f1_psseq2d a_wpss f3_psseq2d f2_psseq2d a_wpss a_wb p_syl $.
$}

$(An equality deduction for the proper subclass relationship.
         (Contributed by NM, 9-Jun-2004.) $)

${
	$v ph A B C D  $.
	f0_psseq12d $f wff ph $.
	f1_psseq12d $f class A $.
	f2_psseq12d $f class B $.
	f3_psseq12d $f class C $.
	f4_psseq12d $f class D $.
	e0_psseq12d $e |- ( ph -> A = B ) $.
	e1_psseq12d $e |- ( ph -> C = D ) $.
	p_psseq12d $p |- ( ph -> ( A C. C <-> B C. D ) ) $= e0_psseq12d f0_psseq12d f1_psseq12d f2_psseq12d f3_psseq12d p_psseq1d e1_psseq12d f0_psseq12d f3_psseq12d f4_psseq12d f2_psseq12d p_psseq2d f0_psseq12d f1_psseq12d f3_psseq12d a_wpss f2_psseq12d f3_psseq12d a_wpss f2_psseq12d f4_psseq12d a_wpss p_bitrd $.
$}

$(A proper subclass is a subclass.  Theorem 10 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)

${
	$v A B  $.
	f0_pssss $f class A $.
	f1_pssss $f class B $.
	p_pssss $p |- ( A C. B -> A C_ B ) $= f0_pssss f1_pssss a_df-pss f0_pssss f1_pssss a_wpss f0_pssss f1_pssss a_wss f0_pssss f1_pssss a_wne p_simplbi $.
$}

$(Two classes in a proper subclass relationship are not equal.  (Contributed
     by NM, 16-Feb-2015.) $)

${
	$v A B  $.
	f0_pssne $f class A $.
	f1_pssne $f class B $.
	p_pssne $p |- ( A C. B -> A =/= B ) $= f0_pssne f1_pssne a_df-pss f0_pssne f1_pssne a_wpss f0_pssne f1_pssne a_wss f0_pssne f1_pssne a_wne p_simprbi $.
$}

$(Deduce subclass from proper subclass.  (Contributed by NM,
       29-Feb-1996.) $)

${
	$v ph A B  $.
	f0_pssssd $f wff ph $.
	f1_pssssd $f class A $.
	f2_pssssd $f class B $.
	e0_pssssd $e |- ( ph -> A C. B ) $.
	p_pssssd $p |- ( ph -> A C_ B ) $= e0_pssssd f1_pssssd f2_pssssd p_pssss f0_pssssd f1_pssssd f2_pssssd a_wpss f1_pssssd f2_pssssd a_wss p_syl $.
$}

$(Proper subclasses are unequal.  Deduction form of ~ pssne .
       (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B  $.
	f0_pssned $f wff ph $.
	f1_pssned $f class A $.
	f2_pssned $f class B $.
	e0_pssned $e |- ( ph -> A C. B ) $.
	p_pssned $p |- ( ph -> A =/= B ) $= e0_pssned f1_pssned f2_pssned p_pssne f0_pssned f1_pssned f2_pssned a_wpss f1_pssned f2_pssned a_wne p_syl $.
$}

$(Subclass in terms of proper subclass.  (Contributed by NM,
     25-Feb-1996.) $)

${
	$v A B  $.
	f0_sspss $f class A $.
	f1_sspss $f class B $.
	p_sspss $p |- ( A C_ B <-> ( A C. B \/ A = B ) ) $= f0_sspss f1_sspss p_dfpss2 f0_sspss f1_sspss a_wpss f0_sspss f1_sspss a_wss f0_sspss f1_sspss a_wceq a_wn p_simplbi2 f0_sspss f1_sspss a_wss f0_sspss f1_sspss a_wceq f0_sspss f1_sspss a_wpss p_con1d f0_sspss f1_sspss a_wss f0_sspss f1_sspss a_wpss f0_sspss f1_sspss a_wceq p_orrd f0_sspss f1_sspss p_pssss f0_sspss f1_sspss p_eqimss f0_sspss f1_sspss a_wpss f0_sspss f1_sspss a_wss f0_sspss f1_sspss a_wceq p_jaoi f0_sspss f1_sspss a_wss f0_sspss f1_sspss a_wpss f0_sspss f1_sspss a_wceq a_wo p_impbii $.
$}

$(Proper subclass is irreflexive.  Theorem 7 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)

${
	$v A  $.
	f0_pssirr $f class A $.
	p_pssirr $p |- -. A C. A $= f0_pssirr f0_pssirr a_wss p_pm3.24 f0_pssirr f0_pssirr p_dfpss3 f0_pssirr f0_pssirr a_wpss f0_pssirr f0_pssirr a_wss f0_pssirr f0_pssirr a_wss a_wn a_wa p_mtbir $.
$}

$(Proper subclass has no 2-cycle loops.  Compare Theorem 8 of [Suppes]
     p. 23.  (Contributed by NM, 7-Feb-1996.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	f0_pssn2lp $f class A $.
	f1_pssn2lp $f class B $.
	p_pssn2lp $p |- -. ( A C. B /\ B C. A ) $= f0_pssn2lp f1_pssn2lp p_dfpss3 f0_pssn2lp f1_pssn2lp a_wpss f0_pssn2lp f1_pssn2lp a_wss f1_pssn2lp f0_pssn2lp a_wss a_wn p_simprbi f1_pssn2lp f0_pssn2lp p_pssss f0_pssn2lp f1_pssn2lp a_wpss f1_pssn2lp f0_pssn2lp a_wss f1_pssn2lp f0_pssn2lp a_wpss p_nsyl f0_pssn2lp f1_pssn2lp a_wpss f1_pssn2lp f0_pssn2lp a_wpss p_imnan f0_pssn2lp f1_pssn2lp a_wpss f1_pssn2lp f0_pssn2lp a_wpss a_wn a_wi f0_pssn2lp f1_pssn2lp a_wpss f1_pssn2lp f0_pssn2lp a_wpss a_wa a_wn p_mpbi $.
$}

$(Two ways of stating trichotomy with respect to inclusion.  (Contributed by
     NM, 12-Aug-2004.) $)

${
	$v A B  $.
	f0_sspsstri $f class A $.
	f1_sspsstri $f class B $.
	p_sspsstri $p |- ( ( A C_ B \/ B C_ A ) <-> ( A C. B \/ A = B \/ B C. A ) ) $= f0_sspsstri f1_sspsstri a_wpss f1_sspsstri f0_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq p_or32 f0_sspsstri f1_sspsstri p_sspss f1_sspsstri f0_sspsstri p_sspss f1_sspsstri f0_sspsstri p_eqcom f1_sspsstri f0_sspsstri a_wceq f0_sspsstri f1_sspsstri a_wceq f1_sspsstri f0_sspsstri a_wpss p_orbi2i f1_sspsstri f0_sspsstri a_wss f1_sspsstri f0_sspsstri a_wpss f1_sspsstri f0_sspsstri a_wceq a_wo f1_sspsstri f0_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq a_wo p_bitri f0_sspsstri f1_sspsstri a_wss f0_sspsstri f1_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq a_wo f1_sspsstri f0_sspsstri a_wss f1_sspsstri f0_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq a_wo p_orbi12i f0_sspsstri f1_sspsstri a_wpss f1_sspsstri f0_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq p_orordir f0_sspsstri f1_sspsstri a_wss f1_sspsstri f0_sspsstri a_wss a_wo f0_sspsstri f1_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq a_wo f1_sspsstri f0_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq a_wo a_wo f0_sspsstri f1_sspsstri a_wpss f1_sspsstri f0_sspsstri a_wpss a_wo f0_sspsstri f1_sspsstri a_wceq a_wo p_bitr4i f0_sspsstri f1_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq f1_sspsstri f0_sspsstri a_wpss a_df-3or f0_sspsstri f1_sspsstri a_wpss f1_sspsstri f0_sspsstri a_wpss a_wo f0_sspsstri f1_sspsstri a_wceq a_wo f0_sspsstri f1_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq a_wo f1_sspsstri f0_sspsstri a_wpss a_wo f0_sspsstri f1_sspsstri a_wss f1_sspsstri f0_sspsstri a_wss a_wo f0_sspsstri f1_sspsstri a_wpss f0_sspsstri f1_sspsstri a_wceq f1_sspsstri f0_sspsstri a_wpss a_w3o p_3bitr4i $.
$}

$(Partial trichotomy law for subclasses.  (Contributed by NM, 16-May-1996.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B  $.
	f0_ssnpss $f class A $.
	f1_ssnpss $f class B $.
	p_ssnpss $p |- ( A C_ B -> -. B C. A ) $= f1_ssnpss f0_ssnpss p_dfpss3 f1_ssnpss f0_ssnpss a_wpss f1_ssnpss f0_ssnpss a_wss f0_ssnpss f1_ssnpss a_wss a_wn p_simprbi f1_ssnpss f0_ssnpss a_wpss f0_ssnpss f1_ssnpss a_wss p_con2i $.
$}

$(Transitive law for proper subclass.  Theorem 9 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)

${
	$v A B C  $.
	f0_psstr $f class A $.
	f1_psstr $f class B $.
	f2_psstr $f class C $.
	p_psstr $p |- ( ( A C. B /\ B C. C ) -> A C. C ) $= f0_psstr f1_psstr p_pssss f1_psstr f2_psstr p_pssss f0_psstr f1_psstr a_wpss f1_psstr f2_psstr a_wpss f0_psstr f1_psstr f2_psstr p_sylan9ss f2_psstr f1_psstr p_pssn2lp f0_psstr f2_psstr f1_psstr p_psseq1 f0_psstr f2_psstr a_wceq f0_psstr f1_psstr a_wpss f2_psstr f1_psstr a_wpss f1_psstr f2_psstr a_wpss p_anbi1d f0_psstr f2_psstr a_wceq f0_psstr f1_psstr a_wpss f1_psstr f2_psstr a_wpss a_wa f2_psstr f1_psstr a_wpss f1_psstr f2_psstr a_wpss a_wa p_mtbiri f0_psstr f2_psstr a_wceq f0_psstr f1_psstr a_wpss f1_psstr f2_psstr a_wpss a_wa p_con2i f0_psstr f2_psstr p_dfpss2 f0_psstr f1_psstr a_wpss f1_psstr f2_psstr a_wpss a_wa f0_psstr f2_psstr a_wss f0_psstr f2_psstr a_wceq a_wn f0_psstr f2_psstr a_wpss p_sylanbrc $.
$}

$(Transitive law for subclass and proper subclass.  (Contributed by NM,
     3-Apr-1996.) $)

${
	$v A B C  $.
	f0_sspsstr $f class A $.
	f1_sspsstr $f class B $.
	f2_sspsstr $f class C $.
	p_sspsstr $p |- ( ( A C_ B /\ B C. C ) -> A C. C ) $= f0_sspsstr f1_sspsstr p_sspss f0_sspsstr f1_sspsstr f2_sspsstr p_psstr f0_sspsstr f1_sspsstr a_wpss f1_sspsstr f2_sspsstr a_wpss f0_sspsstr f2_sspsstr a_wpss p_ex f0_sspsstr f1_sspsstr f2_sspsstr p_psseq1 f0_sspsstr f1_sspsstr a_wceq f0_sspsstr f2_sspsstr a_wpss f1_sspsstr f2_sspsstr a_wpss p_biimprd f0_sspsstr f1_sspsstr a_wpss f1_sspsstr f2_sspsstr a_wpss f0_sspsstr f2_sspsstr a_wpss a_wi f0_sspsstr f1_sspsstr a_wceq p_jaoi f0_sspsstr f1_sspsstr a_wpss f0_sspsstr f1_sspsstr a_wceq a_wo f1_sspsstr f2_sspsstr a_wpss f0_sspsstr f2_sspsstr a_wpss p_imp f0_sspsstr f1_sspsstr a_wss f0_sspsstr f1_sspsstr a_wpss f0_sspsstr f1_sspsstr a_wceq a_wo f1_sspsstr f2_sspsstr a_wpss f0_sspsstr f2_sspsstr a_wpss p_sylanb $.
$}

$(Transitive law for subclass and proper subclass.  (Contributed by NM,
     3-Apr-1996.) $)

${
	$v A B C  $.
	f0_psssstr $f class A $.
	f1_psssstr $f class B $.
	f2_psssstr $f class C $.
	p_psssstr $p |- ( ( A C. B /\ B C_ C ) -> A C. C ) $= f1_psssstr f2_psssstr p_sspss f0_psssstr f1_psssstr f2_psssstr p_psstr f0_psssstr f1_psssstr a_wpss f1_psssstr f2_psssstr a_wpss f0_psssstr f2_psssstr a_wpss p_ex f1_psssstr f2_psssstr f0_psssstr p_psseq2 f1_psssstr f2_psssstr a_wceq f0_psssstr f1_psssstr a_wpss f0_psssstr f2_psssstr a_wpss p_biimpcd f0_psssstr f1_psssstr a_wpss f1_psssstr f2_psssstr a_wpss f0_psssstr f2_psssstr a_wpss f1_psssstr f2_psssstr a_wceq p_jaod f0_psssstr f1_psssstr a_wpss f1_psssstr f2_psssstr a_wpss f1_psssstr f2_psssstr a_wceq a_wo f0_psssstr f2_psssstr a_wpss p_imp f1_psssstr f2_psssstr a_wss f0_psssstr f1_psssstr a_wpss f1_psssstr f2_psssstr a_wpss f1_psssstr f2_psssstr a_wceq a_wo f0_psssstr f2_psssstr a_wpss p_sylan2b $.
$}

$(Proper subclass inclusion is transitive.  Deduction form of ~ psstr .
       (Contributed by David Moews, 1-May-2017.) $)

${
	$v ph A B C  $.
	f0_psstrd $f wff ph $.
	f1_psstrd $f class A $.
	f2_psstrd $f class B $.
	f3_psstrd $f class C $.
	e0_psstrd $e |- ( ph -> A C. B ) $.
	e1_psstrd $e |- ( ph -> B C. C ) $.
	p_psstrd $p |- ( ph -> A C. C ) $= e0_psstrd e1_psstrd f1_psstrd f2_psstrd f3_psstrd p_psstr f0_psstrd f1_psstrd f2_psstrd a_wpss f2_psstrd f3_psstrd a_wpss f1_psstrd f3_psstrd a_wpss p_syl2anc $.
$}

$(Transitivity involving subclass and proper subclass inclusion.
       Deduction form of ~ sspsstr .  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_sspsstrd $f wff ph $.
	f1_sspsstrd $f class A $.
	f2_sspsstrd $f class B $.
	f3_sspsstrd $f class C $.
	e0_sspsstrd $e |- ( ph -> A C_ B ) $.
	e1_sspsstrd $e |- ( ph -> B C. C ) $.
	p_sspsstrd $p |- ( ph -> A C. C ) $= e0_sspsstrd e1_sspsstrd f1_sspsstrd f2_sspsstrd f3_sspsstrd p_sspsstr f0_sspsstrd f1_sspsstrd f2_sspsstrd a_wss f2_sspsstrd f3_sspsstrd a_wpss f1_sspsstrd f3_sspsstrd a_wpss p_syl2anc $.
$}

$(Transitivity involving subclass and proper subclass inclusion.
       Deduction form of ~ psssstr .  (Contributed by David Moews,
       1-May-2017.) $)

${
	$v ph A B C  $.
	f0_psssstrd $f wff ph $.
	f1_psssstrd $f class A $.
	f2_psssstrd $f class B $.
	f3_psssstrd $f class C $.
	e0_psssstrd $e |- ( ph -> A C. B ) $.
	e1_psssstrd $e |- ( ph -> B C_ C ) $.
	p_psssstrd $p |- ( ph -> A C. C ) $= e0_psssstrd e1_psssstrd f1_psssstrd f2_psssstrd f3_psssstrd p_psssstr f0_psssstrd f1_psssstrd f2_psssstrd a_wpss f2_psssstrd f3_psssstrd a_wss f1_psssstrd f3_psssstrd a_wpss p_syl2anc $.
$}

$(A class is not a proper subclass of another iff it satisfies a
     one-directional form of ~ eqss .  (Contributed by Mario Carneiro,
     15-May-2015.) $)

${
	$v A B  $.
	f0_npss $f class A $.
	f1_npss $f class B $.
	p_npss $p |- ( -. A C. B <-> ( A C_ B -> A = B ) ) $= f0_npss f1_npss a_wss f0_npss f1_npss a_wceq p_pm4.61 f0_npss f1_npss p_dfpss2 f0_npss f1_npss a_wss f0_npss f1_npss a_wceq a_wi a_wn f0_npss f1_npss a_wss f0_npss f1_npss a_wceq a_wn a_wa f0_npss f1_npss a_wpss p_bitr4i f0_npss f1_npss a_wss f0_npss f1_npss a_wceq a_wi f0_npss f1_npss a_wpss p_con1bii $.
$}


