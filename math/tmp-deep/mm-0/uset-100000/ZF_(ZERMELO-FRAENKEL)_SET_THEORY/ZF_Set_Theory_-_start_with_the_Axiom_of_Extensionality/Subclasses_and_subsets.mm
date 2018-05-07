$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Define_basic_set_operations_and_relations.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Subclasses and subsets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Define the subclass relationship.  Exercise 9 of [TakeutiZaring] p. 18.
     For example, ` { 1 , 2 } C_ { 1 , 2 , 3 } ` ( ~ ex-ss ).  Note that
     ` A C_ A ` (proved in ~ ssid ).  Contrast this relationship with the
     relationship ` A C. B ` (as will be defined in ~ df-pss ).  For a more
     traditional definition, but requiring a dummy variable, see ~ dfss2 .
     Other possible definitions are given by ~ dfss3 , ~ dfss4 , ~ sspss ,
     ~ ssequn1 , ~ ssequn2 , ~ sseqin2 , and ~ ssdif0 .  (Contributed by NM,
     27-Apr-1994.) $)
${
	$v A $.
	$v B $.
	fdf-ss_0 $f class A $.
	fdf-ss_1 $f class B $.
	df-ss $a |- ( A C_ B <-> ( A i^i B ) = A ) $.
$}
$( Variant of subclass definition ~ df-ss .  (Contributed by NM,
     3-Sep-2004.) $)
${
	$v A $.
	$v B $.
	fdfss_0 $f class A $.
	fdfss_1 $f class B $.
	dfss $p |- ( A C_ B <-> A = ( A i^i B ) ) $= fdfss_0 fdfss_1 wss fdfss_0 fdfss_1 cin fdfss_0 wceq fdfss_0 fdfss_0 fdfss_1 cin wceq fdfss_0 fdfss_1 df-ss fdfss_0 fdfss_1 cin fdfss_0 eqcom bitri $.
$}
$( Define proper subclass relationship between two classes.  Definition 5.9
     of [TakeutiZaring] p. 17.  For example, ` { 1 , 2 } C. { 1 , 2 , 3 } `
     ( ~ ex-pss ).  Note that ` -. A C. A ` (proved in ~ pssirr ).  Contrast
     this relationship with the relationship ` A C_ B ` (as defined in
     ~ df-ss ).  Other possible definitions are given by ~ dfpss2 and
     ~ dfpss3 .  (Contributed by NM, 7-Feb-1996.) $)
${
	$v A $.
	$v B $.
	fdf-pss_0 $f class A $.
	fdf-pss_1 $f class B $.
	df-pss $a |- ( A C. B <-> ( A C_ B /\ A =/= B ) ) $.
$}
$( Alternate definition of the subclass relationship between two classes.
       Definition 5.9 of [TakeutiZaring] p. 17.  (Contributed by NM,
       8-Jan-2002.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdfss2_0 $f set x $.
	fdfss2_1 $f class A $.
	fdfss2_2 $f class B $.
	dfss2 $p |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $= fdfss2_1 fdfss2_2 wss fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wa wb fdfss2_0 wal fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wi fdfss2_0 wal fdfss2_1 fdfss2_2 wss fdfss2_1 fdfss2_1 fdfss2_2 cin wceq fdfss2_1 fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wa fdfss2_0 cab wceq fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wa wb fdfss2_0 wal fdfss2_1 fdfss2_2 dfss fdfss2_1 fdfss2_2 cin fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wa fdfss2_0 cab fdfss2_1 fdfss2_0 fdfss2_1 fdfss2_2 df-in eqeq2i fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wa fdfss2_0 fdfss2_1 abeq2 3bitri fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wi fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel wa wb fdfss2_0 fdfss2_0 cv fdfss2_1 wcel fdfss2_0 cv fdfss2_2 wcel pm4.71 albii bitr4i $.
$}
$( Alternate definition of subclass relationship.  (Contributed by NM,
       14-Oct-1999.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fdfss3_0 $f set x $.
	fdfss3_1 $f class A $.
	fdfss3_2 $f class B $.
	dfss3 $p |- ( A C_ B <-> A. x e. A x e. B ) $= fdfss3_1 fdfss3_2 wss fdfss3_0 cv fdfss3_1 wcel fdfss3_0 cv fdfss3_2 wcel wi fdfss3_0 wal fdfss3_0 cv fdfss3_2 wcel fdfss3_0 fdfss3_1 wral fdfss3_0 fdfss3_1 fdfss3_2 dfss2 fdfss3_0 cv fdfss3_2 wcel fdfss3_0 fdfss3_1 df-ral bitr4i $.
$}
$( Equivalence for subclass relation, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       3-Jul-1994.)  (Revised by Andrew Salmon, 27-Aug-2011.) $)
${
	$v x $.
	$v z $.
	$v A $.
	$v B $.
	$d z A $.
	$d z B $.
	$d x z $.
	idfss2f_0 $f set z $.
	fdfss2f_0 $f set x $.
	fdfss2f_1 $f class A $.
	fdfss2f_2 $f class B $.
	edfss2f_0 $e |- F/_ x A $.
	edfss2f_1 $e |- F/_ x B $.
	dfss2f $p |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $= fdfss2f_1 fdfss2f_2 wss idfss2f_0 cv fdfss2f_1 wcel idfss2f_0 cv fdfss2f_2 wcel wi idfss2f_0 wal fdfss2f_0 cv fdfss2f_1 wcel fdfss2f_0 cv fdfss2f_2 wcel wi fdfss2f_0 wal idfss2f_0 fdfss2f_1 fdfss2f_2 dfss2 idfss2f_0 cv fdfss2f_1 wcel idfss2f_0 cv fdfss2f_2 wcel wi fdfss2f_0 cv fdfss2f_1 wcel fdfss2f_0 cv fdfss2f_2 wcel wi idfss2f_0 fdfss2f_0 idfss2f_0 cv fdfss2f_1 wcel idfss2f_0 cv fdfss2f_2 wcel fdfss2f_0 fdfss2f_0 idfss2f_0 fdfss2f_1 edfss2f_0 nfcri fdfss2f_0 idfss2f_0 fdfss2f_2 edfss2f_1 nfcri nfim fdfss2f_0 cv fdfss2f_1 wcel fdfss2f_0 cv fdfss2f_2 wcel wi idfss2f_0 nfv idfss2f_0 cv fdfss2f_0 cv wceq idfss2f_0 cv fdfss2f_1 wcel fdfss2f_0 cv fdfss2f_1 wcel idfss2f_0 cv fdfss2f_2 wcel fdfss2f_0 cv fdfss2f_2 wcel idfss2f_0 cv fdfss2f_0 cv fdfss2f_1 eleq1 idfss2f_0 cv fdfss2f_0 cv fdfss2f_2 eleq1 imbi12d cbval bitri $.
$}
$( Equivalence for subclass relation, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       20-Mar-2004.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fdfss3f_0 $f set x $.
	fdfss3f_1 $f class A $.
	fdfss3f_2 $f class B $.
	edfss3f_0 $e |- F/_ x A $.
	edfss3f_1 $e |- F/_ x B $.
	dfss3f $p |- ( A C_ B <-> A. x e. A x e. B ) $= fdfss3f_1 fdfss3f_2 wss fdfss3f_0 cv fdfss3f_1 wcel fdfss3f_0 cv fdfss3f_2 wcel wi fdfss3f_0 wal fdfss3f_0 cv fdfss3f_2 wcel fdfss3f_0 fdfss3f_1 wral fdfss3f_0 fdfss3f_1 fdfss3f_2 edfss3f_0 edfss3f_1 dfss2f fdfss3f_0 cv fdfss3f_2 wcel fdfss3f_0 fdfss3f_1 df-ral bitr4i $.
$}
$( If ` x ` is not free in ` A ` and ` B ` , it is not free in
       ` A C_ B ` .  (Contributed by NM, 27-Dec-1996.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fnfss_0 $f set x $.
	fnfss_1 $f class A $.
	fnfss_2 $f class B $.
	enfss_0 $e |- F/_ x A $.
	enfss_1 $e |- F/_ x B $.
	nfss $p |- F/ x A C_ B $= fnfss_1 fnfss_2 wss fnfss_0 cv fnfss_2 wcel fnfss_0 fnfss_1 wral fnfss_0 fnfss_0 fnfss_1 fnfss_2 enfss_0 enfss_1 dfss3f fnfss_0 cv fnfss_2 wcel fnfss_0 fnfss_1 nfra1 nfxfr $.
$}
$( Membership relationships follow from a subclass relationship.
       (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	issel_0 $f set x $.
	fssel_0 $f class A $.
	fssel_1 $f class B $.
	fssel_2 $f class C $.
	ssel $p |- ( A C_ B -> ( C e. A -> C e. B ) ) $= fssel_0 fssel_1 wss issel_0 cv fssel_2 wceq issel_0 cv fssel_0 wcel wa issel_0 wex issel_0 cv fssel_2 wceq issel_0 cv fssel_1 wcel wa issel_0 wex fssel_2 fssel_0 wcel fssel_2 fssel_1 wcel fssel_0 fssel_1 wss issel_0 cv fssel_2 wceq issel_0 cv fssel_0 wcel wa issel_0 cv fssel_2 wceq issel_0 cv fssel_1 wcel wa issel_0 fssel_0 fssel_1 wss issel_0 cv fssel_0 wcel issel_0 cv fssel_1 wcel issel_0 cv fssel_2 wceq fssel_0 fssel_1 wss issel_0 cv fssel_0 wcel issel_0 cv fssel_1 wcel wi issel_0 fssel_0 fssel_1 wss issel_0 cv fssel_0 wcel issel_0 cv fssel_1 wcel wi issel_0 wal issel_0 fssel_0 fssel_1 dfss2 biimpi 19.21bi anim2d eximdv issel_0 fssel_2 fssel_0 df-clel issel_0 fssel_2 fssel_1 df-clel 3imtr4g $.
$}
$( Membership relationships follow from a subclass relationship.
     (Contributed by NM, 7-Jun-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fssel2_0 $f class A $.
	fssel2_1 $f class B $.
	fssel2_2 $f class C $.
	ssel2 $p |- ( ( A C_ B /\ C e. A ) -> C e. B ) $= fssel2_0 fssel2_1 wss fssel2_2 fssel2_0 wcel fssel2_2 fssel2_1 wcel fssel2_0 fssel2_1 fssel2_2 ssel imp $.
$}
$( Membership inference from subclass relationship.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseli_0 $f class A $.
	fsseli_1 $f class B $.
	fsseli_2 $f class C $.
	esseli_0 $e |- A C_ B $.
	sseli $p |- ( C e. A -> C e. B ) $= fsseli_0 fsseli_1 wss fsseli_2 fsseli_0 wcel fsseli_2 fsseli_1 wcel wi esseli_0 fsseli_0 fsseli_1 fsseli_2 ssel ax-mp $.
$}
$( Membership inference from subclass relationship.  (Contributed by NM,
         31-May-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsselii_0 $f class A $.
	fsselii_1 $f class B $.
	fsselii_2 $f class C $.
	esselii_0 $e |- A C_ B $.
	esselii_1 $e |- C e. A $.
	sselii $p |- C e. B $= fsselii_2 fsselii_0 wcel fsselii_2 fsselii_1 wcel esselii_1 fsselii_0 fsselii_1 fsselii_2 esselii_0 sseli ax-mp $.
$}
$( Membership inference from subclass relationship.  (Contributed by NM,
         25-Jun-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseldi_0 $f wff ph $.
	fsseldi_1 $f class A $.
	fsseldi_2 $f class B $.
	fsseldi_3 $f class C $.
	esseldi_0 $e |- A C_ B $.
	esseldi_1 $e |- ( ph -> C e. A ) $.
	sseldi $p |- ( ph -> C e. B ) $= fsseldi_0 fsseldi_3 fsseldi_1 wcel fsseldi_3 fsseldi_2 wcel esseldi_1 fsseldi_1 fsseldi_2 fsseldi_3 esseldi_0 sseli syl $.
$}
$( Membership deduction from subclass relationship.  (Contributed by NM,
       15-Nov-1995.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseld_0 $f wff ph $.
	fsseld_1 $f class A $.
	fsseld_2 $f class B $.
	fsseld_3 $f class C $.
	esseld_0 $e |- ( ph -> A C_ B ) $.
	sseld $p |- ( ph -> ( C e. A -> C e. B ) ) $= fsseld_0 fsseld_1 fsseld_2 wss fsseld_3 fsseld_1 wcel fsseld_3 fsseld_2 wcel wi esseld_0 fsseld_1 fsseld_2 fsseld_3 ssel syl $.
$}
$( Membership deduction from subclass relationship.  (Contributed by NM,
       26-Jun-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsselda_0 $f wff ph $.
	fsselda_1 $f class A $.
	fsselda_2 $f class B $.
	fsselda_3 $f class C $.
	esselda_0 $e |- ( ph -> A C_ B ) $.
	sselda $p |- ( ( ph /\ C e. A ) -> C e. B ) $= fsselda_0 fsselda_3 fsselda_1 wcel fsselda_3 fsselda_2 wcel fsselda_0 fsselda_1 fsselda_2 fsselda_3 esselda_0 sseld imp $.
$}
$( Membership inference from subclass relationship.  (Contributed by NM,
         14-Dec-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseldd_0 $f wff ph $.
	fsseldd_1 $f class A $.
	fsseldd_2 $f class B $.
	fsseldd_3 $f class C $.
	esseldd_0 $e |- ( ph -> A C_ B ) $.
	esseldd_1 $e |- ( ph -> C e. A ) $.
	sseldd $p |- ( ph -> C e. B ) $= fsseldd_0 fsseldd_3 fsseldd_1 wcel fsseldd_3 fsseldd_2 wcel esseldd_1 fsseldd_0 fsseldd_1 fsseldd_2 fsseldd_3 esseldd_0 sseld mpd $.
$}
$( If a class is not in another class, it is also not in a subclass of that
       class.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fssneld_0 $f wff ph $.
	fssneld_1 $f class A $.
	fssneld_2 $f class B $.
	fssneld_3 $f class C $.
	essneld_0 $e |- ( ph -> A C_ B ) $.
	ssneld $p |- ( ph -> ( -. C e. B -> -. C e. A ) ) $= fssneld_0 fssneld_3 fssneld_1 wcel fssneld_3 fssneld_2 wcel fssneld_0 fssneld_1 fssneld_2 fssneld_3 essneld_0 sseld con3d $.
$}
$( If an element is not in a class, it is also not in a subclass of that
       class.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fssneldd_0 $f wff ph $.
	fssneldd_1 $f class A $.
	fssneldd_2 $f class B $.
	fssneldd_3 $f class C $.
	essneldd_0 $e |- ( ph -> A C_ B ) $.
	essneldd_1 $e |- ( ph -> -. C e. B ) $.
	ssneldd $p |- ( ph -> -. C e. A ) $= fssneldd_0 fssneldd_3 fssneldd_2 wcel wn fssneldd_3 fssneldd_1 wcel wn essneldd_1 fssneldd_0 fssneldd_1 fssneldd_2 fssneldd_3 essneldd_0 ssneld mpd $.
$}
$( Inference rule based on subclass definition.  (Contributed by NM,
       5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fssriv_0 $f set x $.
	fssriv_1 $f class A $.
	fssriv_2 $f class B $.
	essriv_0 $e |- ( x e. A -> x e. B ) $.
	ssriv $p |- A C_ B $= fssriv_1 fssriv_2 wss fssriv_0 cv fssriv_1 wcel fssriv_0 cv fssriv_2 wcel wi fssriv_0 fssriv_0 fssriv_1 fssriv_2 dfss2 essriv_0 mpgbir $.
$}
$( Deduction rule based on subclass definition.  (Contributed by NM,
       15-Nov-1995.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d x ph $.
	fssrdv_0 $f wff ph $.
	fssrdv_1 $f set x $.
	fssrdv_2 $f class A $.
	fssrdv_3 $f class B $.
	essrdv_0 $e |- ( ph -> ( x e. A -> x e. B ) ) $.
	ssrdv $p |- ( ph -> A C_ B ) $= fssrdv_0 fssrdv_1 cv fssrdv_2 wcel fssrdv_1 cv fssrdv_3 wcel wi fssrdv_1 wal fssrdv_2 fssrdv_3 wss fssrdv_0 fssrdv_1 cv fssrdv_2 wcel fssrdv_1 cv fssrdv_3 wcel wi fssrdv_1 essrdv_0 alrimiv fssrdv_1 fssrdv_2 fssrdv_3 dfss2 sylibr $.
$}
$( Transitivity of subclasses.  Exercise 5 of [TakeutiZaring] p. 17.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$d x A $.
	$d x B $.
	$d x C $.
	isstr2_0 $f set x $.
	fsstr2_0 $f class A $.
	fsstr2_1 $f class B $.
	fsstr2_2 $f class C $.
	sstr2 $p |- ( A C_ B -> ( B C_ C -> A C_ C ) ) $= fsstr2_0 fsstr2_1 wss isstr2_0 cv fsstr2_1 wcel isstr2_0 cv fsstr2_2 wcel wi isstr2_0 wal isstr2_0 cv fsstr2_0 wcel isstr2_0 cv fsstr2_2 wcel wi isstr2_0 wal fsstr2_1 fsstr2_2 wss fsstr2_0 fsstr2_2 wss fsstr2_0 fsstr2_1 wss isstr2_0 cv fsstr2_1 wcel isstr2_0 cv fsstr2_2 wcel wi isstr2_0 cv fsstr2_0 wcel isstr2_0 cv fsstr2_2 wcel wi isstr2_0 fsstr2_0 fsstr2_1 wss isstr2_0 cv fsstr2_0 wcel isstr2_0 cv fsstr2_1 wcel isstr2_0 cv fsstr2_2 wcel fsstr2_0 fsstr2_1 isstr2_0 cv ssel imim1d alimdv isstr2_0 fsstr2_1 fsstr2_2 dfss2 isstr2_0 fsstr2_0 fsstr2_2 dfss2 3imtr4g $.
$}
$( Transitivity of subclasses.  Theorem 6 of [Suppes] p. 23.  (Contributed by
     NM, 5-Sep-2003.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsstr_0 $f class A $.
	fsstr_1 $f class B $.
	fsstr_2 $f class C $.
	sstr $p |- ( ( A C_ B /\ B C_ C ) -> A C_ C ) $= fsstr_0 fsstr_1 wss fsstr_1 fsstr_2 wss fsstr_0 fsstr_2 wss fsstr_0 fsstr_1 fsstr_2 sstr2 imp $.
$}
$( Subclass transitivity inference.  (Contributed by NM, 5-May-2000.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsstri_0 $f class A $.
	fsstri_1 $f class B $.
	fsstri_2 $f class C $.
	esstri_0 $e |- A C_ B $.
	esstri_1 $e |- B C_ C $.
	sstri $p |- A C_ C $= fsstri_0 fsstri_1 wss fsstri_1 fsstri_2 wss fsstri_0 fsstri_2 wss esstri_0 esstri_1 fsstri_0 fsstri_1 fsstri_2 sstr2 mp2 $.
$}
$( Subclass transitivity deduction.  (Contributed by NM, 2-Jun-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsstrd_0 $f wff ph $.
	fsstrd_1 $f class A $.
	fsstrd_2 $f class B $.
	fsstrd_3 $f class C $.
	esstrd_0 $e |- ( ph -> A C_ B ) $.
	esstrd_1 $e |- ( ph -> B C_ C ) $.
	sstrd $p |- ( ph -> A C_ C ) $= fsstrd_0 fsstrd_1 fsstrd_2 wss fsstrd_2 fsstrd_3 wss fsstrd_1 fsstrd_3 wss esstrd_0 esstrd_1 fsstrd_1 fsstrd_2 fsstrd_3 sstr syl2anc $.
$}
$( Subclass transitivity deduction.  (Contributed by NM, 6-Feb-2014.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl5ss_0 $f wff ph $.
	fsyl5ss_1 $f class A $.
	fsyl5ss_2 $f class B $.
	fsyl5ss_3 $f class C $.
	esyl5ss_0 $e |- A C_ B $.
	esyl5ss_1 $e |- ( ph -> B C_ C ) $.
	syl5ss $p |- ( ph -> A C_ C ) $= fsyl5ss_0 fsyl5ss_1 fsyl5ss_2 fsyl5ss_3 fsyl5ss_1 fsyl5ss_2 wss fsyl5ss_0 esyl5ss_0 a1i esyl5ss_1 sstrd $.
$}
$( Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl6ss_0 $f wff ph $.
	fsyl6ss_1 $f class A $.
	fsyl6ss_2 $f class B $.
	fsyl6ss_3 $f class C $.
	esyl6ss_0 $e |- ( ph -> A C_ B ) $.
	esyl6ss_1 $e |- B C_ C $.
	syl6ss $p |- ( ph -> A C_ C ) $= fsyl6ss_0 fsyl6ss_1 fsyl6ss_2 fsyl6ss_3 esyl6ss_0 fsyl6ss_2 fsyl6ss_3 wss fsyl6ss_0 esyl6ss_1 a1i sstrd $.
$}
$( A subclass transitivity deduction.  (Contributed by NM, 27-Sep-2004.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	fsylan9ss_0 $f wff ph $.
	fsylan9ss_1 $f wff ps $.
	fsylan9ss_2 $f class A $.
	fsylan9ss_3 $f class B $.
	fsylan9ss_4 $f class C $.
	esylan9ss_0 $e |- ( ph -> A C_ B ) $.
	esylan9ss_1 $e |- ( ps -> B C_ C ) $.
	sylan9ss $p |- ( ( ph /\ ps ) -> A C_ C ) $= fsylan9ss_0 fsylan9ss_2 fsylan9ss_3 wss fsylan9ss_3 fsylan9ss_4 wss fsylan9ss_2 fsylan9ss_4 wss fsylan9ss_1 esylan9ss_0 esylan9ss_1 fsylan9ss_2 fsylan9ss_3 fsylan9ss_4 sstr syl2an $.
$}
$( A subclass transitivity deduction.  (Contributed by NM, 27-Sep-2004.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	fsylan9ssr_0 $f wff ph $.
	fsylan9ssr_1 $f wff ps $.
	fsylan9ssr_2 $f class A $.
	fsylan9ssr_3 $f class B $.
	fsylan9ssr_4 $f class C $.
	esylan9ssr_0 $e |- ( ph -> A C_ B ) $.
	esylan9ssr_1 $e |- ( ps -> B C_ C ) $.
	sylan9ssr $p |- ( ( ps /\ ph ) -> A C_ C ) $= fsylan9ssr_0 fsylan9ssr_1 fsylan9ssr_2 fsylan9ssr_4 wss fsylan9ssr_0 fsylan9ssr_1 fsylan9ssr_2 fsylan9ssr_3 fsylan9ssr_4 esylan9ssr_0 esylan9ssr_1 sylan9ss ancoms $.
$}
$( The subclass relationship is antisymmetric.  Compare Theorem 4 of
       [Suppes] p. 22.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	ieqss_0 $f set x $.
	feqss_0 $f class A $.
	feqss_1 $f class B $.
	eqss $p |- ( A = B <-> ( A C_ B /\ B C_ A ) ) $= ieqss_0 cv feqss_0 wcel ieqss_0 cv feqss_1 wcel wb ieqss_0 wal ieqss_0 cv feqss_0 wcel ieqss_0 cv feqss_1 wcel wi ieqss_0 wal ieqss_0 cv feqss_1 wcel ieqss_0 cv feqss_0 wcel wi ieqss_0 wal wa feqss_0 feqss_1 wceq feqss_0 feqss_1 wss feqss_1 feqss_0 wss wa ieqss_0 cv feqss_0 wcel ieqss_0 cv feqss_1 wcel ieqss_0 albiim ieqss_0 feqss_0 feqss_1 dfcleq feqss_0 feqss_1 wss ieqss_0 cv feqss_0 wcel ieqss_0 cv feqss_1 wcel wi ieqss_0 wal feqss_1 feqss_0 wss ieqss_0 cv feqss_1 wcel ieqss_0 cv feqss_0 wcel wi ieqss_0 wal ieqss_0 feqss_0 feqss_1 dfss2 ieqss_0 feqss_1 feqss_0 dfss2 anbi12i 3bitr4i $.
$}
$( Infer equality from two subclass relationships.  Compare Theorem 4 of
       [Suppes] p. 22.  (Contributed by NM, 9-Sep-1993.) $)
${
	$v A $.
	$v B $.
	feqssi_0 $f class A $.
	feqssi_1 $f class B $.
	eeqssi_0 $e |- A C_ B $.
	eeqssi_1 $e |- B C_ A $.
	eqssi $p |- A = B $= feqssi_0 feqssi_1 wceq feqssi_0 feqssi_1 wss feqssi_1 feqssi_0 wss eeqssi_0 eeqssi_1 feqssi_0 feqssi_1 eqss mpbir2an $.
$}
$( Equality deduction from two subclass relationships.  Compare Theorem 4
       of [Suppes] p. 22.  (Contributed by NM, 27-Jun-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	feqssd_0 $f wff ph $.
	feqssd_1 $f class A $.
	feqssd_2 $f class B $.
	eeqssd_0 $e |- ( ph -> A C_ B ) $.
	eeqssd_1 $e |- ( ph -> B C_ A ) $.
	eqssd $p |- ( ph -> A = B ) $= feqssd_0 feqssd_1 feqssd_2 wss feqssd_2 feqssd_1 wss feqssd_1 feqssd_2 wceq eeqssd_0 eeqssd_1 feqssd_1 feqssd_2 eqss sylanbrc $.
$}
$( Any class is a subclass of itself.  Exercise 10 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 14-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$d A x $.
	issid_0 $f set x $.
	fssid_0 $f class A $.
	ssid $p |- A C_ A $= issid_0 fssid_0 fssid_0 issid_0 cv fssid_0 wcel id ssriv $.
$}
$( Any class is a subclass of the universal class.  (Contributed by NM,
       31-Oct-1995.) $)
${
	$v x $.
	$v A $.
	$d A x $.
	issv_0 $f set x $.
	fssv_0 $f class A $.
	ssv $p |- A C_ _V $= issv_0 fssv_0 cvv issv_0 cv fssv_0 elex ssriv $.
$}
$( Equality theorem for subclasses.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 21-Jun-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseq1_0 $f class A $.
	fsseq1_1 $f class B $.
	fsseq1_2 $f class C $.
	sseq1 $p |- ( A = B -> ( A C_ C <-> B C_ C ) ) $= fsseq1_0 fsseq1_1 wceq fsseq1_0 fsseq1_1 wss fsseq1_1 fsseq1_0 wss wa fsseq1_0 fsseq1_2 wss fsseq1_1 fsseq1_2 wss wb fsseq1_0 fsseq1_1 eqss fsseq1_0 fsseq1_1 wss fsseq1_1 fsseq1_0 wss wa fsseq1_0 fsseq1_2 wss fsseq1_1 fsseq1_2 wss fsseq1_1 fsseq1_0 wss fsseq1_0 fsseq1_2 wss fsseq1_1 fsseq1_2 wss wi fsseq1_0 fsseq1_1 wss fsseq1_1 fsseq1_0 fsseq1_2 sstr2 adantl fsseq1_0 fsseq1_1 wss fsseq1_1 fsseq1_2 wss fsseq1_0 fsseq1_2 wss wi fsseq1_1 fsseq1_0 wss fsseq1_0 fsseq1_1 fsseq1_2 sstr2 adantr impbid sylbi $.
$}
$( Equality theorem for the subclass relationship.  (Contributed by NM,
     25-Jun-1998.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseq2_0 $f class A $.
	fsseq2_1 $f class B $.
	fsseq2_2 $f class C $.
	sseq2 $p |- ( A = B -> ( C C_ A <-> C C_ B ) ) $= fsseq2_0 fsseq2_1 wss fsseq2_1 fsseq2_0 wss wa fsseq2_2 fsseq2_0 wss fsseq2_2 fsseq2_1 wss wi fsseq2_2 fsseq2_1 wss fsseq2_2 fsseq2_0 wss wi wa fsseq2_0 fsseq2_1 wceq fsseq2_2 fsseq2_0 wss fsseq2_2 fsseq2_1 wss wb fsseq2_0 fsseq2_1 wss fsseq2_2 fsseq2_0 wss fsseq2_2 fsseq2_1 wss wi fsseq2_1 fsseq2_0 wss fsseq2_2 fsseq2_1 wss fsseq2_2 fsseq2_0 wss wi fsseq2_2 fsseq2_0 wss fsseq2_0 fsseq2_1 wss fsseq2_2 fsseq2_1 wss fsseq2_2 fsseq2_0 fsseq2_1 sstr2 com12 fsseq2_2 fsseq2_1 wss fsseq2_1 fsseq2_0 wss fsseq2_2 fsseq2_0 wss fsseq2_2 fsseq2_1 fsseq2_0 sstr2 com12 anim12i fsseq2_0 fsseq2_1 eqss fsseq2_2 fsseq2_0 wss fsseq2_2 fsseq2_1 wss dfbi2 3imtr4i $.
$}
$( Equality theorem for the subclass relationship.  (Contributed by NM,
     31-May-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fsseq12_0 $f class A $.
	fsseq12_1 $f class B $.
	fsseq12_2 $f class C $.
	fsseq12_3 $f class D $.
	sseq12 $p |- ( ( A = B /\ C = D ) -> ( A C_ C <-> B C_ D ) ) $= fsseq12_0 fsseq12_1 wceq fsseq12_0 fsseq12_2 wss fsseq12_1 fsseq12_2 wss fsseq12_2 fsseq12_3 wceq fsseq12_1 fsseq12_3 wss fsseq12_0 fsseq12_1 fsseq12_2 sseq1 fsseq12_2 fsseq12_3 fsseq12_1 sseq2 sylan9bb $.
$}
$( An equality inference for the subclass relationship.  (Contributed by
       NM, 18-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseq1i_0 $f class A $.
	fsseq1i_1 $f class B $.
	fsseq1i_2 $f class C $.
	esseq1i_0 $e |- A = B $.
	sseq1i $p |- ( A C_ C <-> B C_ C ) $= fsseq1i_0 fsseq1i_1 wceq fsseq1i_0 fsseq1i_2 wss fsseq1i_1 fsseq1i_2 wss wb esseq1i_0 fsseq1i_0 fsseq1i_1 fsseq1i_2 sseq1 ax-mp $.
$}
$( An equality inference for the subclass relationship.  (Contributed by
       NM, 30-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseq2i_0 $f class A $.
	fsseq2i_1 $f class B $.
	fsseq2i_2 $f class C $.
	esseq2i_0 $e |- A = B $.
	sseq2i $p |- ( C C_ A <-> C C_ B ) $= fsseq2i_0 fsseq2i_1 wceq fsseq2i_2 fsseq2i_0 wss fsseq2i_2 fsseq2i_1 wss wb esseq2i_0 fsseq2i_0 fsseq2i_1 fsseq2i_2 sseq2 ax-mp $.
$}
$( An equality inference for the subclass relationship.  (Contributed by
         NM, 31-May-1999.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fsseq12i_0 $f class A $.
	fsseq12i_1 $f class B $.
	fsseq12i_2 $f class C $.
	fsseq12i_3 $f class D $.
	esseq12i_0 $e |- A = B $.
	esseq12i_1 $e |- C = D $.
	sseq12i $p |- ( A C_ C <-> B C_ D ) $= fsseq12i_0 fsseq12i_1 wceq fsseq12i_2 fsseq12i_3 wceq fsseq12i_0 fsseq12i_2 wss fsseq12i_1 fsseq12i_3 wss wb esseq12i_0 esseq12i_1 fsseq12i_0 fsseq12i_1 fsseq12i_2 fsseq12i_3 sseq12 mp2an $.
$}
$( An equality deduction for the subclass relationship.  (Contributed by
       NM, 14-Aug-1994.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseq1d_0 $f wff ph $.
	fsseq1d_1 $f class A $.
	fsseq1d_2 $f class B $.
	fsseq1d_3 $f class C $.
	esseq1d_0 $e |- ( ph -> A = B ) $.
	sseq1d $p |- ( ph -> ( A C_ C <-> B C_ C ) ) $= fsseq1d_0 fsseq1d_1 fsseq1d_2 wceq fsseq1d_1 fsseq1d_3 wss fsseq1d_2 fsseq1d_3 wss wb esseq1d_0 fsseq1d_1 fsseq1d_2 fsseq1d_3 sseq1 syl $.
$}
$( An equality deduction for the subclass relationship.  (Contributed by
       NM, 14-Aug-1994.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseq2d_0 $f wff ph $.
	fsseq2d_1 $f class A $.
	fsseq2d_2 $f class B $.
	fsseq2d_3 $f class C $.
	esseq2d_0 $e |- ( ph -> A = B ) $.
	sseq2d $p |- ( ph -> ( C C_ A <-> C C_ B ) ) $= fsseq2d_0 fsseq2d_1 fsseq2d_2 wceq fsseq2d_3 fsseq2d_1 wss fsseq2d_3 fsseq2d_2 wss wb esseq2d_0 fsseq2d_1 fsseq2d_2 fsseq2d_3 sseq2 syl $.
$}
$( An equality deduction for the subclass relationship.  (Contributed by
         NM, 31-May-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fsseq12d_0 $f wff ph $.
	fsseq12d_1 $f class A $.
	fsseq12d_2 $f class B $.
	fsseq12d_3 $f class C $.
	fsseq12d_4 $f class D $.
	esseq12d_0 $e |- ( ph -> A = B ) $.
	esseq12d_1 $e |- ( ph -> C = D ) $.
	sseq12d $p |- ( ph -> ( A C_ C <-> B C_ D ) ) $= fsseq12d_0 fsseq12d_1 fsseq12d_3 wss fsseq12d_2 fsseq12d_3 wss fsseq12d_2 fsseq12d_4 wss fsseq12d_0 fsseq12d_1 fsseq12d_2 fsseq12d_3 esseq12d_0 sseq1d fsseq12d_0 fsseq12d_3 fsseq12d_4 fsseq12d_2 esseq12d_1 sseq2d bitrd $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 16-Jul-1995.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feqsstri_0 $f class A $.
	feqsstri_1 $f class B $.
	feqsstri_2 $f class C $.
	eeqsstri_0 $e |- A = B $.
	eeqsstri_1 $e |- B C_ C $.
	eqsstri $p |- A C_ C $= feqsstri_0 feqsstri_2 wss feqsstri_1 feqsstri_2 wss eeqsstri_1 feqsstri_0 feqsstri_1 feqsstri_2 eeqsstri_0 sseq1i mpbir $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 19-Oct-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feqsstr3i_0 $f class A $.
	feqsstr3i_1 $f class B $.
	feqsstr3i_2 $f class C $.
	eeqsstr3i_0 $e |- B = A $.
	eeqsstr3i_1 $e |- B C_ C $.
	eqsstr3i $p |- A C_ C $= feqsstr3i_0 feqsstr3i_1 feqsstr3i_2 feqsstr3i_1 feqsstr3i_0 eeqsstr3i_0 eqcomi eeqsstr3i_1 eqsstri $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 28-Jul-1995.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseqtri_0 $f class A $.
	fsseqtri_1 $f class B $.
	fsseqtri_2 $f class C $.
	esseqtri_0 $e |- A C_ B $.
	esseqtri_1 $e |- B = C $.
	sseqtri $p |- A C_ C $= fsseqtri_0 fsseqtri_1 wss fsseqtri_0 fsseqtri_2 wss esseqtri_0 fsseqtri_1 fsseqtri_2 fsseqtri_0 esseqtri_1 sseq2i mpbi $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 4-Apr-1995.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsseqtr4i_0 $f class A $.
	fsseqtr4i_1 $f class B $.
	fsseqtr4i_2 $f class C $.
	esseqtr4i_0 $e |- A C_ B $.
	esseqtr4i_1 $e |- C = B $.
	sseqtr4i $p |- A C_ C $= fsseqtr4i_0 fsseqtr4i_1 fsseqtr4i_2 esseqtr4i_0 fsseqtr4i_2 fsseqtr4i_1 esseqtr4i_1 eqcomi sseqtri $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feqsstrd_0 $f wff ph $.
	feqsstrd_1 $f class A $.
	feqsstrd_2 $f class B $.
	feqsstrd_3 $f class C $.
	eeqsstrd_0 $e |- ( ph -> A = B ) $.
	eeqsstrd_1 $e |- ( ph -> B C_ C ) $.
	eqsstrd $p |- ( ph -> A C_ C ) $= feqsstrd_0 feqsstrd_1 feqsstrd_3 wss feqsstrd_2 feqsstrd_3 wss eeqsstrd_1 feqsstrd_0 feqsstrd_1 feqsstrd_2 feqsstrd_3 eeqsstrd_0 sseq1d mpbird $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feqsstr3d_0 $f wff ph $.
	feqsstr3d_1 $f class A $.
	feqsstr3d_2 $f class B $.
	feqsstr3d_3 $f class C $.
	eeqsstr3d_0 $e |- ( ph -> B = A ) $.
	eeqsstr3d_1 $e |- ( ph -> B C_ C ) $.
	eqsstr3d $p |- ( ph -> A C_ C ) $= feqsstr3d_0 feqsstr3d_1 feqsstr3d_2 feqsstr3d_3 feqsstr3d_0 feqsstr3d_2 feqsstr3d_1 eeqsstr3d_0 eqcomd eeqsstr3d_1 eqsstrd $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseqtrd_0 $f wff ph $.
	fsseqtrd_1 $f class A $.
	fsseqtrd_2 $f class B $.
	fsseqtrd_3 $f class C $.
	esseqtrd_0 $e |- ( ph -> A C_ B ) $.
	esseqtrd_1 $e |- ( ph -> B = C ) $.
	sseqtrd $p |- ( ph -> A C_ C ) $= fsseqtrd_0 fsseqtrd_1 fsseqtrd_2 wss fsseqtrd_1 fsseqtrd_3 wss esseqtrd_0 fsseqtrd_0 fsseqtrd_2 fsseqtrd_3 fsseqtrd_1 esseqtrd_1 sseq2d mpbid $.
$}
$( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsseqtr4d_0 $f wff ph $.
	fsseqtr4d_1 $f class A $.
	fsseqtr4d_2 $f class B $.
	fsseqtr4d_3 $f class C $.
	esseqtr4d_0 $e |- ( ph -> A C_ B ) $.
	esseqtr4d_1 $e |- ( ph -> C = B ) $.
	sseqtr4d $p |- ( ph -> A C_ C ) $= fsseqtr4d_0 fsseqtr4d_1 fsseqtr4d_2 fsseqtr4d_3 esseqtr4d_0 fsseqtr4d_0 fsseqtr4d_3 fsseqtr4d_2 esseqtr4d_1 eqcomd sseqtrd $.
$}
$( Substitution of equality in both sides of a subclass relationship.
       (Contributed by NM, 13-Jan-1996.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3sstr3i_0 $f class A $.
	f3sstr3i_1 $f class B $.
	f3sstr3i_2 $f class C $.
	f3sstr3i_3 $f class D $.
	e3sstr3i_0 $e |- A C_ B $.
	e3sstr3i_1 $e |- A = C $.
	e3sstr3i_2 $e |- B = D $.
	3sstr3i $p |- C C_ D $= f3sstr3i_0 f3sstr3i_1 wss f3sstr3i_2 f3sstr3i_3 wss e3sstr3i_0 f3sstr3i_0 f3sstr3i_2 f3sstr3i_1 f3sstr3i_3 e3sstr3i_1 e3sstr3i_2 sseq12i mpbi $.
$}
$( Substitution of equality in both sides of a subclass relationship.
       (Contributed by NM, 13-Jan-1996.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3sstr4i_0 $f class A $.
	f3sstr4i_1 $f class B $.
	f3sstr4i_2 $f class C $.
	f3sstr4i_3 $f class D $.
	e3sstr4i_0 $e |- A C_ B $.
	e3sstr4i_1 $e |- C = A $.
	e3sstr4i_2 $e |- D = B $.
	3sstr4i $p |- C C_ D $= f3sstr4i_2 f3sstr4i_3 wss f3sstr4i_0 f3sstr4i_1 wss e3sstr4i_0 f3sstr4i_2 f3sstr4i_0 f3sstr4i_3 f3sstr4i_1 e3sstr4i_1 e3sstr4i_2 sseq12i mpbir $.
$}
$( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 1-Oct-2000.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3sstr3g_0 $f wff ph $.
	f3sstr3g_1 $f class A $.
	f3sstr3g_2 $f class B $.
	f3sstr3g_3 $f class C $.
	f3sstr3g_4 $f class D $.
	e3sstr3g_0 $e |- ( ph -> A C_ B ) $.
	e3sstr3g_1 $e |- A = C $.
	e3sstr3g_2 $e |- B = D $.
	3sstr3g $p |- ( ph -> C C_ D ) $= f3sstr3g_0 f3sstr3g_1 f3sstr3g_2 wss f3sstr3g_3 f3sstr3g_4 wss e3sstr3g_0 f3sstr3g_1 f3sstr3g_3 f3sstr3g_2 f3sstr3g_4 e3sstr3g_1 e3sstr3g_2 sseq12i sylib $.
$}
$( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 16-Aug-1994.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3sstr4g_0 $f wff ph $.
	f3sstr4g_1 $f class A $.
	f3sstr4g_2 $f class B $.
	f3sstr4g_3 $f class C $.
	f3sstr4g_4 $f class D $.
	e3sstr4g_0 $e |- ( ph -> A C_ B ) $.
	e3sstr4g_1 $e |- C = A $.
	e3sstr4g_2 $e |- D = B $.
	3sstr4g $p |- ( ph -> C C_ D ) $= f3sstr4g_0 f3sstr4g_1 f3sstr4g_2 wss f3sstr4g_3 f3sstr4g_4 wss e3sstr4g_0 f3sstr4g_3 f3sstr4g_1 f3sstr4g_4 f3sstr4g_2 e3sstr4g_1 e3sstr4g_2 sseq12i sylibr $.
$}
$( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 1-Oct-2000.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3sstr3d_0 $f wff ph $.
	f3sstr3d_1 $f class A $.
	f3sstr3d_2 $f class B $.
	f3sstr3d_3 $f class C $.
	f3sstr3d_4 $f class D $.
	e3sstr3d_0 $e |- ( ph -> A C_ B ) $.
	e3sstr3d_1 $e |- ( ph -> A = C ) $.
	e3sstr3d_2 $e |- ( ph -> B = D ) $.
	3sstr3d $p |- ( ph -> C C_ D ) $= f3sstr3d_0 f3sstr3d_1 f3sstr3d_2 wss f3sstr3d_3 f3sstr3d_4 wss e3sstr3d_0 f3sstr3d_0 f3sstr3d_1 f3sstr3d_3 f3sstr3d_2 f3sstr3d_4 e3sstr3d_1 e3sstr3d_2 sseq12d mpbid $.
$}
$( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 30-Nov-1995.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3sstr4d_0 $f wff ph $.
	f3sstr4d_1 $f class A $.
	f3sstr4d_2 $f class B $.
	f3sstr4d_3 $f class C $.
	f3sstr4d_4 $f class D $.
	e3sstr4d_0 $e |- ( ph -> A C_ B ) $.
	e3sstr4d_1 $e |- ( ph -> C = A ) $.
	e3sstr4d_2 $e |- ( ph -> D = B ) $.
	3sstr4d $p |- ( ph -> C C_ D ) $= f3sstr4d_0 f3sstr4d_3 f3sstr4d_4 wss f3sstr4d_1 f3sstr4d_2 wss e3sstr4d_0 f3sstr4d_0 f3sstr4d_3 f3sstr4d_1 f3sstr4d_4 f3sstr4d_2 e3sstr4d_1 e3sstr4d_2 sseq12d mpbird $.
$}
$( B chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl5eqss_0 $f wff ph $.
	fsyl5eqss_1 $f class A $.
	fsyl5eqss_2 $f class B $.
	fsyl5eqss_3 $f class C $.
	esyl5eqss_0 $e |- A = B $.
	esyl5eqss_1 $e |- ( ph -> B C_ C ) $.
	syl5eqss $p |- ( ph -> A C_ C ) $= fsyl5eqss_0 fsyl5eqss_2 fsyl5eqss_3 wss fsyl5eqss_1 fsyl5eqss_3 wss esyl5eqss_1 fsyl5eqss_1 fsyl5eqss_2 fsyl5eqss_3 esyl5eqss_0 sseq1i sylibr $.
$}
$( B chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl5eqssr_0 $f wff ph $.
	fsyl5eqssr_1 $f class A $.
	fsyl5eqssr_2 $f class B $.
	fsyl5eqssr_3 $f class C $.
	esyl5eqssr_0 $e |- B = A $.
	esyl5eqssr_1 $e |- ( ph -> B C_ C ) $.
	syl5eqssr $p |- ( ph -> A C_ C ) $= fsyl5eqssr_0 fsyl5eqssr_1 fsyl5eqssr_2 fsyl5eqssr_3 fsyl5eqssr_2 fsyl5eqssr_1 esyl5eqssr_0 eqcomi esyl5eqssr_1 syl5eqss $.
$}
$( A chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl6sseq_0 $f wff ph $.
	fsyl6sseq_1 $f class A $.
	fsyl6sseq_2 $f class B $.
	fsyl6sseq_3 $f class C $.
	esyl6sseq_0 $e |- ( ph -> A C_ B ) $.
	esyl6sseq_1 $e |- B = C $.
	syl6sseq $p |- ( ph -> A C_ C ) $= fsyl6sseq_0 fsyl6sseq_1 fsyl6sseq_2 wss fsyl6sseq_1 fsyl6sseq_3 wss esyl6sseq_0 fsyl6sseq_2 fsyl6sseq_3 fsyl6sseq_1 esyl6sseq_1 sseq2i sylib $.
$}
$( A chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl6sseqr_0 $f wff ph $.
	fsyl6sseqr_1 $f class A $.
	fsyl6sseqr_2 $f class B $.
	fsyl6sseqr_3 $f class C $.
	esyl6sseqr_0 $e |- ( ph -> A C_ B ) $.
	esyl6sseqr_1 $e |- C = B $.
	syl6sseqr $p |- ( ph -> A C_ C ) $= fsyl6sseqr_0 fsyl6sseqr_1 fsyl6sseqr_2 fsyl6sseqr_3 esyl6sseqr_0 fsyl6sseqr_3 fsyl6sseqr_2 esyl6sseqr_1 eqcomi syl6sseq $.
$}
$( Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl5sseq_0 $f wff ph $.
	fsyl5sseq_1 $f class A $.
	fsyl5sseq_2 $f class B $.
	fsyl5sseq_3 $f class C $.
	esyl5sseq_0 $e |- B C_ A $.
	esyl5sseq_1 $e |- ( ph -> A = C ) $.
	syl5sseq $p |- ( ph -> B C_ C ) $= fsyl5sseq_0 fsyl5sseq_1 fsyl5sseq_3 wceq fsyl5sseq_2 fsyl5sseq_1 wss fsyl5sseq_2 fsyl5sseq_3 wss esyl5sseq_1 esyl5sseq_0 fsyl5sseq_1 fsyl5sseq_3 wceq fsyl5sseq_2 fsyl5sseq_1 wss fsyl5sseq_2 fsyl5sseq_3 wss fsyl5sseq_1 fsyl5sseq_3 fsyl5sseq_2 sseq2 biimpa sylancl $.
$}
$( Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl5sseqr_0 $f wff ph $.
	fsyl5sseqr_1 $f class A $.
	fsyl5sseqr_2 $f class B $.
	fsyl5sseqr_3 $f class C $.
	esyl5sseqr_0 $e |- B C_ A $.
	esyl5sseqr_1 $e |- ( ph -> C = A ) $.
	syl5sseqr $p |- ( ph -> B C_ C ) $= fsyl5sseqr_0 fsyl5sseqr_2 fsyl5sseqr_1 fsyl5sseqr_3 fsyl5sseqr_2 fsyl5sseqr_1 wss fsyl5sseqr_0 esyl5sseqr_0 a1i esyl5sseqr_1 sseqtr4d $.
$}
$( A chained subclass and equality deduction.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl6eqss_0 $f wff ph $.
	fsyl6eqss_1 $f class A $.
	fsyl6eqss_2 $f class B $.
	fsyl6eqss_3 $f class C $.
	esyl6eqss_0 $e |- ( ph -> A = B ) $.
	esyl6eqss_1 $e |- B C_ C $.
	syl6eqss $p |- ( ph -> A C_ C ) $= fsyl6eqss_0 fsyl6eqss_1 fsyl6eqss_2 fsyl6eqss_3 esyl6eqss_0 fsyl6eqss_2 fsyl6eqss_3 wss fsyl6eqss_0 esyl6eqss_1 a1i eqsstrd $.
$}
$( A chained subclass and equality deduction.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl6eqssr_0 $f wff ph $.
	fsyl6eqssr_1 $f class A $.
	fsyl6eqssr_2 $f class B $.
	fsyl6eqssr_3 $f class C $.
	esyl6eqssr_0 $e |- ( ph -> B = A ) $.
	esyl6eqssr_1 $e |- B C_ C $.
	syl6eqssr $p |- ( ph -> A C_ C ) $= fsyl6eqssr_0 fsyl6eqssr_1 fsyl6eqssr_2 fsyl6eqssr_3 fsyl6eqssr_0 fsyl6eqssr_2 fsyl6eqssr_1 esyl6eqssr_0 eqcomd esyl6eqssr_1 syl6eqss $.
$}
$( Equality implies the subclass relation.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
${
	$v A $.
	$v B $.
	feqimss_0 $f class A $.
	feqimss_1 $f class B $.
	eqimss $p |- ( A = B -> A C_ B ) $= feqimss_0 feqimss_1 wceq feqimss_0 feqimss_1 wss feqimss_1 feqimss_0 wss feqimss_0 feqimss_1 eqss simplbi $.
$}
$( Equality implies the subclass relation.  (Contributed by NM,
     23-Nov-2003.) $)
${
	$v A $.
	$v B $.
	feqimss2_0 $f class A $.
	feqimss2_1 $f class B $.
	eqimss2 $p |- ( B = A -> A C_ B ) $= feqimss2_0 feqimss2_1 wss feqimss2_0 feqimss2_1 feqimss2_0 feqimss2_1 eqimss eqcoms $.
$}
$( Infer subclass relationship from equality.  (Contributed by NM,
       6-Jan-2007.) $)
${
	$v A $.
	$v B $.
	feqimssi_0 $f class A $.
	feqimssi_1 $f class B $.
	eeqimssi_0 $e |- A = B $.
	eqimssi $p |- A C_ B $= feqimssi_0 feqimssi_0 feqimssi_1 feqimssi_0 ssid eeqimssi_0 sseqtri $.
$}
$( Infer subclass relationship from equality.  (Contributed by NM,
       7-Jan-2007.) $)
${
	$v A $.
	$v B $.
	feqimss2i_0 $f class A $.
	feqimss2i_1 $f class B $.
	eeqimss2i_0 $e |- A = B $.
	eqimss2i $p |- B C_ A $= feqimss2i_1 feqimss2i_1 feqimss2i_0 feqimss2i_1 ssid eeqimss2i_0 sseqtr4i $.
$}
$( Two classes are different if they don't include the same class.
     (Contributed by NM, 23-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fnssne1_0 $f class A $.
	fnssne1_1 $f class B $.
	fnssne1_2 $f class C $.
	nssne1 $p |- ( ( A C_ B /\ -. A C_ C ) -> B =/= C ) $= fnssne1_0 fnssne1_1 wss fnssne1_0 fnssne1_2 wss wn fnssne1_1 fnssne1_2 wne fnssne1_0 fnssne1_1 wss fnssne1_0 fnssne1_2 wss fnssne1_1 fnssne1_2 fnssne1_1 fnssne1_2 wceq fnssne1_0 fnssne1_1 wss fnssne1_0 fnssne1_2 wss fnssne1_1 fnssne1_2 fnssne1_0 sseq2 biimpcd necon3bd imp $.
$}
$( Two classes are different if they are not subclasses of the same class.
     (Contributed by NM, 23-Apr-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fnssne2_0 $f class A $.
	fnssne2_1 $f class B $.
	fnssne2_2 $f class C $.
	nssne2 $p |- ( ( A C_ C /\ -. B C_ C ) -> A =/= B ) $= fnssne2_0 fnssne2_2 wss fnssne2_1 fnssne2_2 wss wn fnssne2_0 fnssne2_1 wne fnssne2_0 fnssne2_2 wss fnssne2_1 fnssne2_2 wss fnssne2_0 fnssne2_1 fnssne2_0 fnssne2_1 wceq fnssne2_0 fnssne2_2 wss fnssne2_1 fnssne2_2 wss fnssne2_0 fnssne2_1 fnssne2_2 sseq1 biimpcd necon3bd imp $.
$}
$( Negation of subclass relationship.  Exercise 13 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 25-Feb-1996.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fnss_0 $f set x $.
	fnss_1 $f class A $.
	fnss_2 $f class B $.
	nss $p |- ( -. A C_ B <-> E. x ( x e. A /\ -. x e. B ) ) $= fnss_0 cv fnss_1 wcel fnss_0 cv fnss_2 wcel wn wa fnss_0 wex fnss_1 fnss_2 wss wn fnss_0 cv fnss_1 wcel fnss_0 cv fnss_2 wcel wn wa fnss_0 wex fnss_0 cv fnss_1 wcel fnss_0 cv fnss_2 wcel wi fnss_0 wal fnss_1 fnss_2 wss fnss_0 cv fnss_1 wcel fnss_0 cv fnss_2 wcel fnss_0 exanali fnss_0 fnss_1 fnss_2 dfss2 xchbinxr bicomi $.
$}
$( Quantification restricted to a subclass.  (Contributed by NM,
       11-Mar-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fssralv_0 $f wff ph $.
	fssralv_1 $f set x $.
	fssralv_2 $f class A $.
	fssralv_3 $f class B $.
	ssralv $p |- ( A C_ B -> ( A. x e. B ph -> A. x e. A ph ) ) $= fssralv_2 fssralv_3 wss fssralv_0 fssralv_0 fssralv_1 fssralv_3 fssralv_2 fssralv_2 fssralv_3 wss fssralv_1 cv fssralv_2 wcel fssralv_1 cv fssralv_3 wcel fssralv_0 fssralv_2 fssralv_3 fssralv_1 cv ssel imim1d ralimdv2 $.
$}
$( Existential quantification restricted to a subclass.  (Contributed by
       NM, 11-Jan-2007.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fssrexv_0 $f wff ph $.
	fssrexv_1 $f set x $.
	fssrexv_2 $f class A $.
	fssrexv_3 $f class B $.
	ssrexv $p |- ( A C_ B -> ( E. x e. A ph -> E. x e. B ph ) ) $= fssrexv_2 fssrexv_3 wss fssrexv_0 fssrexv_0 fssrexv_1 fssrexv_2 fssrexv_3 fssrexv_2 fssrexv_3 wss fssrexv_1 cv fssrexv_2 wcel fssrexv_1 cv fssrexv_3 wcel fssrexv_0 fssrexv_2 fssrexv_3 fssrexv_1 cv ssel anim1d reximdv2 $.
$}
$( Restricted universal quantification on a subset in terms of superset.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d A x $.
	$d B x $.
	fralss_0 $f wff ph $.
	fralss_1 $f set x $.
	fralss_2 $f class A $.
	fralss_3 $f class B $.
	ralss $p |- ( A C_ B -> ( A. x e. A ph <-> A. x e. B ( x e. A -> ph ) ) ) $= fralss_2 fralss_3 wss fralss_0 fralss_1 cv fralss_2 wcel fralss_0 wi fralss_1 fralss_2 fralss_3 fralss_2 fralss_3 wss fralss_1 cv fralss_2 wcel fralss_0 wi fralss_1 cv fralss_3 wcel fralss_1 cv fralss_2 wcel wa fralss_0 wi fralss_1 cv fralss_3 wcel fralss_1 cv fralss_2 wcel fralss_0 wi wi fralss_2 fralss_3 wss fralss_1 cv fralss_2 wcel fralss_1 cv fralss_3 wcel fralss_1 cv fralss_2 wcel wa fralss_0 fralss_2 fralss_3 wss fralss_1 cv fralss_2 wcel fralss_1 cv fralss_3 wcel fralss_2 fralss_3 fralss_1 cv ssel pm4.71rd imbi1d fralss_1 cv fralss_3 wcel fralss_1 cv fralss_2 wcel fralss_0 impexp syl6bb ralbidv2 $.
$}
$( Restricted existential quantification on a subset in terms of superset.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d A x $.
	$d B x $.
	frexss_0 $f wff ph $.
	frexss_1 $f set x $.
	frexss_2 $f class A $.
	frexss_3 $f class B $.
	rexss $p |- ( A C_ B -> ( E. x e. A ph <-> E. x e. B ( x e. A /\ ph ) ) ) $= frexss_2 frexss_3 wss frexss_0 frexss_1 cv frexss_2 wcel frexss_0 wa frexss_1 frexss_2 frexss_3 frexss_2 frexss_3 wss frexss_1 cv frexss_2 wcel frexss_0 wa frexss_1 cv frexss_3 wcel frexss_1 cv frexss_2 wcel wa frexss_0 wa frexss_1 cv frexss_3 wcel frexss_1 cv frexss_2 wcel frexss_0 wa wa frexss_2 frexss_3 wss frexss_1 cv frexss_2 wcel frexss_1 cv frexss_3 wcel frexss_1 cv frexss_2 wcel wa frexss_0 frexss_2 frexss_3 wss frexss_1 cv frexss_2 wcel frexss_1 cv frexss_3 wcel frexss_2 frexss_3 frexss_1 cv ssel pm4.71rd anbi1d frexss_1 cv frexss_3 wcel frexss_1 cv frexss_2 wcel frexss_0 anass syl6bb rexbidv2 $.
$}
$( Class abstractions in a subclass relationship.  (Contributed by NM,
       3-Jul-1994.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fss2ab_0 $f wff ph $.
	fss2ab_1 $f wff ps $.
	fss2ab_2 $f set x $.
	ss2ab $p |- ( { x | ph } C_ { x | ps } <-> A. x ( ph -> ps ) ) $= fss2ab_0 fss2ab_2 cab fss2ab_1 fss2ab_2 cab wss fss2ab_2 cv fss2ab_0 fss2ab_2 cab wcel fss2ab_2 cv fss2ab_1 fss2ab_2 cab wcel wi fss2ab_2 wal fss2ab_0 fss2ab_1 wi fss2ab_2 wal fss2ab_2 fss2ab_0 fss2ab_2 cab fss2ab_1 fss2ab_2 cab fss2ab_0 fss2ab_2 nfab1 fss2ab_1 fss2ab_2 nfab1 dfss2f fss2ab_2 cv fss2ab_0 fss2ab_2 cab wcel fss2ab_2 cv fss2ab_1 fss2ab_2 cab wcel wi fss2ab_0 fss2ab_1 wi fss2ab_2 fss2ab_2 cv fss2ab_0 fss2ab_2 cab wcel fss2ab_0 fss2ab_2 cv fss2ab_1 fss2ab_2 cab wcel fss2ab_1 fss2ab_0 fss2ab_2 abid fss2ab_1 fss2ab_2 abid imbi12i albii bitri $.
$}
$( Class abstraction in a subclass relationship.  (Contributed by NM,
       16-Aug-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fabss_0 $f wff ph $.
	fabss_1 $f set x $.
	fabss_2 $f class A $.
	abss $p |- ( { x | ph } C_ A <-> A. x ( ph -> x e. A ) ) $= fabss_0 fabss_1 cab fabss_2 wss fabss_0 fabss_1 cab fabss_1 cv fabss_2 wcel fabss_1 cab wss fabss_0 fabss_1 cv fabss_2 wcel wi fabss_1 wal fabss_1 cv fabss_2 wcel fabss_1 cab fabss_2 fabss_0 fabss_1 cab fabss_1 fabss_2 abid2 sseq2i fabss_0 fabss_1 cv fabss_2 wcel fabss_1 ss2ab bitr3i $.
$}
$( Subclass of a class abstraction.  (Contributed by NM, 16-Aug-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fssab_0 $f wff ph $.
	fssab_1 $f set x $.
	fssab_2 $f class A $.
	ssab $p |- ( A C_ { x | ph } <-> A. x ( x e. A -> ph ) ) $= fssab_2 fssab_0 fssab_1 cab wss fssab_1 cv fssab_2 wcel fssab_1 cab fssab_0 fssab_1 cab wss fssab_1 cv fssab_2 wcel fssab_0 wi fssab_1 wal fssab_1 cv fssab_2 wcel fssab_1 cab fssab_2 fssab_0 fssab_1 cab fssab_1 fssab_2 abid2 sseq1i fssab_1 cv fssab_2 wcel fssab_0 fssab_1 ss2ab bitr3i $.
$}
$( The relation for a subclass of a class abstraction is equivalent to
       restricted quantification.  (Contributed by NM, 6-Sep-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fssabral_0 $f wff ph $.
	fssabral_1 $f set x $.
	fssabral_2 $f class A $.
	ssabral $p |- ( A C_ { x | ph } <-> A. x e. A ph ) $= fssabral_2 fssabral_0 fssabral_1 cab wss fssabral_1 cv fssabral_2 wcel fssabral_0 wi fssabral_1 wal fssabral_0 fssabral_1 fssabral_2 wral fssabral_0 fssabral_1 fssabral_2 ssab fssabral_0 fssabral_1 fssabral_2 df-ral bitr4i $.
$}
$( Inference of abstraction subclass from implication.  (Contributed by NM,
       31-Mar-1995.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	fss2abi_0 $f wff ph $.
	fss2abi_1 $f wff ps $.
	fss2abi_2 $f set x $.
	ess2abi_0 $e |- ( ph -> ps ) $.
	ss2abi $p |- { x | ph } C_ { x | ps } $= fss2abi_0 fss2abi_2 cab fss2abi_1 fss2abi_2 cab wss fss2abi_0 fss2abi_1 wi fss2abi_2 fss2abi_0 fss2abi_1 fss2abi_2 ss2ab ess2abi_0 mpgbir $.
$}
$( Deduction of abstraction subclass from implication.  (Contributed by NM,
       29-Jul-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$d x ph $.
	fss2abdv_0 $f wff ph $.
	fss2abdv_1 $f wff ps $.
	fss2abdv_2 $f wff ch $.
	fss2abdv_3 $f set x $.
	ess2abdv_0 $e |- ( ph -> ( ps -> ch ) ) $.
	ss2abdv $p |- ( ph -> { x | ps } C_ { x | ch } ) $= fss2abdv_0 fss2abdv_1 fss2abdv_2 wi fss2abdv_3 wal fss2abdv_1 fss2abdv_3 cab fss2abdv_2 fss2abdv_3 cab wss fss2abdv_0 fss2abdv_1 fss2abdv_2 wi fss2abdv_3 ess2abdv_0 alrimiv fss2abdv_1 fss2abdv_2 fss2abdv_3 ss2ab sylibr $.
$}
$( Deduction of abstraction subclass from implication.  (Contributed by NM,
       20-Jan-2006.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$d x ph $.
	$d x A $.
	fabssdv_0 $f wff ph $.
	fabssdv_1 $f wff ps $.
	fabssdv_2 $f set x $.
	fabssdv_3 $f class A $.
	eabssdv_0 $e |- ( ph -> ( ps -> x e. A ) ) $.
	abssdv $p |- ( ph -> { x | ps } C_ A ) $= fabssdv_0 fabssdv_1 fabssdv_2 cv fabssdv_3 wcel wi fabssdv_2 wal fabssdv_1 fabssdv_2 cab fabssdv_3 wss fabssdv_0 fabssdv_1 fabssdv_2 cv fabssdv_3 wcel wi fabssdv_2 eabssdv_0 alrimiv fabssdv_1 fabssdv_2 fabssdv_3 abss sylibr $.
$}
$( Inference of abstraction subclass from implication.  (Contributed by NM,
       20-Jan-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fabssi_0 $f wff ph $.
	fabssi_1 $f set x $.
	fabssi_2 $f class A $.
	eabssi_0 $e |- ( ph -> x e. A ) $.
	abssi $p |- { x | ph } C_ A $= fabssi_0 fabssi_1 cab fabssi_1 cv fabssi_2 wcel fabssi_1 cab fabssi_2 fabssi_0 fabssi_1 cv fabssi_2 wcel fabssi_1 eabssi_0 ss2abi fabssi_1 fabssi_2 abid2 sseqtri $.
$}
$( Restricted abstraction classes in a subclass relationship.  (Contributed
     by NM, 30-May-1999.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	fss2rab_0 $f wff ph $.
	fss2rab_1 $f wff ps $.
	fss2rab_2 $f set x $.
	fss2rab_3 $f class A $.
	ss2rab $p |- ( { x e. A | ph } C_ { x e. A | ps } <-> A. x e. A ( ph -> ps ) ) $= fss2rab_0 fss2rab_2 fss2rab_3 crab fss2rab_1 fss2rab_2 fss2rab_3 crab wss fss2rab_2 cv fss2rab_3 wcel fss2rab_0 wa fss2rab_2 cab fss2rab_2 cv fss2rab_3 wcel fss2rab_1 wa fss2rab_2 cab wss fss2rab_2 cv fss2rab_3 wcel fss2rab_0 wa fss2rab_2 cv fss2rab_3 wcel fss2rab_1 wa wi fss2rab_2 wal fss2rab_0 fss2rab_1 wi fss2rab_2 fss2rab_3 wral fss2rab_0 fss2rab_2 fss2rab_3 crab fss2rab_2 cv fss2rab_3 wcel fss2rab_0 wa fss2rab_2 cab fss2rab_1 fss2rab_2 fss2rab_3 crab fss2rab_2 cv fss2rab_3 wcel fss2rab_1 wa fss2rab_2 cab fss2rab_0 fss2rab_2 fss2rab_3 df-rab fss2rab_1 fss2rab_2 fss2rab_3 df-rab sseq12i fss2rab_2 cv fss2rab_3 wcel fss2rab_0 wa fss2rab_2 cv fss2rab_3 wcel fss2rab_1 wa fss2rab_2 ss2ab fss2rab_0 fss2rab_1 wi fss2rab_2 fss2rab_3 wral fss2rab_2 cv fss2rab_3 wcel fss2rab_0 fss2rab_1 wi wi fss2rab_2 wal fss2rab_2 cv fss2rab_3 wcel fss2rab_0 wa fss2rab_2 cv fss2rab_3 wcel fss2rab_1 wa wi fss2rab_2 wal fss2rab_0 fss2rab_1 wi fss2rab_2 fss2rab_3 df-ral fss2rab_2 cv fss2rab_3 wcel fss2rab_0 fss2rab_1 wi wi fss2rab_2 cv fss2rab_3 wcel fss2rab_0 wa fss2rab_2 cv fss2rab_3 wcel fss2rab_1 wa wi fss2rab_2 fss2rab_2 cv fss2rab_3 wcel fss2rab_0 fss2rab_1 imdistan albii bitr2i 3bitri $.
$}
$( Restricted class abstraction in a subclass relationship.  (Contributed
       by NM, 16-Aug-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x B $.
	frabss_0 $f wff ph $.
	frabss_1 $f set x $.
	frabss_2 $f class A $.
	frabss_3 $f class B $.
	rabss $p |- ( { x e. A | ph } C_ B <-> A. x e. A ( ph -> x e. B ) ) $= frabss_0 frabss_1 frabss_2 crab frabss_3 wss frabss_1 cv frabss_2 wcel frabss_0 wa frabss_1 cab frabss_3 wss frabss_1 cv frabss_2 wcel frabss_0 wa frabss_1 cv frabss_3 wcel wi frabss_1 wal frabss_0 frabss_1 cv frabss_3 wcel wi frabss_1 frabss_2 wral frabss_0 frabss_1 frabss_2 crab frabss_1 cv frabss_2 wcel frabss_0 wa frabss_1 cab frabss_3 frabss_0 frabss_1 frabss_2 df-rab sseq1i frabss_1 cv frabss_2 wcel frabss_0 wa frabss_1 frabss_3 abss frabss_1 cv frabss_2 wcel frabss_0 wa frabss_1 cv frabss_3 wcel wi frabss_1 wal frabss_1 cv frabss_2 wcel frabss_0 frabss_1 cv frabss_3 wcel wi wi frabss_1 wal frabss_0 frabss_1 cv frabss_3 wcel wi frabss_1 frabss_2 wral frabss_1 cv frabss_2 wcel frabss_0 wa frabss_1 cv frabss_3 wcel wi frabss_1 cv frabss_2 wcel frabss_0 frabss_1 cv frabss_3 wcel wi wi frabss_1 frabss_1 cv frabss_2 wcel frabss_0 frabss_1 cv frabss_3 wcel impexp albii frabss_0 frabss_1 cv frabss_3 wcel wi frabss_1 frabss_2 df-ral bitr4i 3bitri $.
$}
$( Subclass of a restricted class abstraction.  (Contributed by NM,
       16-Aug-2006.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	fssrab_0 $f wff ph $.
	fssrab_1 $f set x $.
	fssrab_2 $f class A $.
	fssrab_3 $f class B $.
	ssrab $p |- ( B C_ { x e. A | ph } <-> ( B C_ A /\ A. x e. B ph ) ) $= fssrab_3 fssrab_0 fssrab_1 fssrab_2 crab wss fssrab_3 fssrab_1 cv fssrab_2 wcel fssrab_0 wa fssrab_1 cab wss fssrab_1 cv fssrab_3 wcel fssrab_1 cv fssrab_2 wcel fssrab_0 wa wi fssrab_1 wal fssrab_3 fssrab_2 wss fssrab_0 fssrab_1 fssrab_3 wral wa fssrab_0 fssrab_1 fssrab_2 crab fssrab_1 cv fssrab_2 wcel fssrab_0 wa fssrab_1 cab fssrab_3 fssrab_0 fssrab_1 fssrab_2 df-rab sseq2i fssrab_1 cv fssrab_2 wcel fssrab_0 wa fssrab_1 fssrab_3 ssab fssrab_3 fssrab_2 wss fssrab_0 fssrab_1 fssrab_3 wral wa fssrab_1 cv fssrab_2 wcel fssrab_1 fssrab_3 wral fssrab_0 fssrab_1 fssrab_3 wral wa fssrab_1 cv fssrab_2 wcel fssrab_0 wa fssrab_1 fssrab_3 wral fssrab_1 cv fssrab_3 wcel fssrab_1 cv fssrab_2 wcel fssrab_0 wa wi fssrab_1 wal fssrab_3 fssrab_2 wss fssrab_1 cv fssrab_2 wcel fssrab_1 fssrab_3 wral fssrab_0 fssrab_1 fssrab_3 wral fssrab_1 fssrab_3 fssrab_2 dfss3 anbi1i fssrab_1 cv fssrab_2 wcel fssrab_0 fssrab_1 fssrab_3 r19.26 fssrab_1 cv fssrab_2 wcel fssrab_0 wa fssrab_1 fssrab_3 df-ral 3bitr2ri 3bitri $.
$}
$( Subclass of a restricted class abstraction (deduction rule).
       (Contributed by NM, 31-Aug-2006.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	$d x ph $.
	fssrabdv_0 $f wff ph $.
	fssrabdv_1 $f wff ps $.
	fssrabdv_2 $f set x $.
	fssrabdv_3 $f class A $.
	fssrabdv_4 $f class B $.
	essrabdv_0 $e |- ( ph -> B C_ A ) $.
	essrabdv_1 $e |- ( ( ph /\ x e. B ) -> ps ) $.
	ssrabdv $p |- ( ph -> B C_ { x e. A | ps } ) $= fssrabdv_0 fssrabdv_4 fssrabdv_3 wss fssrabdv_1 fssrabdv_2 fssrabdv_4 wral fssrabdv_4 fssrabdv_1 fssrabdv_2 fssrabdv_3 crab wss essrabdv_0 fssrabdv_0 fssrabdv_1 fssrabdv_2 fssrabdv_4 essrabdv_1 ralrimiva fssrabdv_1 fssrabdv_2 fssrabdv_3 fssrabdv_4 ssrab sylanbrc $.
$}
$( Subclass of a restricted class abstraction (deduction rule).
       (Contributed by NM, 2-Feb-2015.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	$v B $.
	$d x B $.
	$d x ph $.
	frabssdv_0 $f wff ph $.
	frabssdv_1 $f wff ps $.
	frabssdv_2 $f set x $.
	frabssdv_3 $f class A $.
	frabssdv_4 $f class B $.
	erabssdv_0 $e |- ( ( ph /\ x e. A /\ ps ) -> x e. B ) $.
	rabssdv $p |- ( ph -> { x e. A | ps } C_ B ) $= frabssdv_0 frabssdv_1 frabssdv_2 cv frabssdv_4 wcel wi frabssdv_2 frabssdv_3 wral frabssdv_1 frabssdv_2 frabssdv_3 crab frabssdv_4 wss frabssdv_0 frabssdv_1 frabssdv_2 cv frabssdv_4 wcel wi frabssdv_2 frabssdv_3 frabssdv_0 frabssdv_2 cv frabssdv_3 wcel frabssdv_1 frabssdv_2 cv frabssdv_4 wcel erabssdv_0 3exp ralrimiv frabssdv_1 frabssdv_2 frabssdv_3 frabssdv_4 rabss sylibr $.
$}
$( Deduction of restricted abstraction subclass from implication.
       (Contributed by NM, 30-May-2006.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v x $.
	$v A $.
	$d x ph $.
	fss2rabdv_0 $f wff ph $.
	fss2rabdv_1 $f wff ps $.
	fss2rabdv_2 $f wff ch $.
	fss2rabdv_3 $f set x $.
	fss2rabdv_4 $f class A $.
	ess2rabdv_0 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
	ss2rabdv $p |- ( ph -> { x e. A | ps } C_ { x e. A | ch } ) $= fss2rabdv_0 fss2rabdv_1 fss2rabdv_2 wi fss2rabdv_3 fss2rabdv_4 wral fss2rabdv_1 fss2rabdv_3 fss2rabdv_4 crab fss2rabdv_2 fss2rabdv_3 fss2rabdv_4 crab wss fss2rabdv_0 fss2rabdv_1 fss2rabdv_2 wi fss2rabdv_3 fss2rabdv_4 ess2rabdv_0 ralrimiva fss2rabdv_1 fss2rabdv_2 fss2rabdv_3 fss2rabdv_4 ss2rab sylibr $.
$}
$( Inference of restricted abstraction subclass from implication.
       (Contributed by NM, 14-Oct-1999.) $)
${
	$v ph $.
	$v ps $.
	$v x $.
	$v A $.
	fss2rabi_0 $f wff ph $.
	fss2rabi_1 $f wff ps $.
	fss2rabi_2 $f set x $.
	fss2rabi_3 $f class A $.
	ess2rabi_0 $e |- ( x e. A -> ( ph -> ps ) ) $.
	ss2rabi $p |- { x e. A | ph } C_ { x e. A | ps } $= fss2rabi_0 fss2rabi_2 fss2rabi_3 crab fss2rabi_1 fss2rabi_2 fss2rabi_3 crab wss fss2rabi_0 fss2rabi_1 wi fss2rabi_2 fss2rabi_3 fss2rabi_0 fss2rabi_1 fss2rabi_2 fss2rabi_3 ss2rab ess2rabi_0 mprgbir $.
$}
$( Subclass law for restricted abstraction.  (Contributed by NM,
       18-Dec-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$d x A $.
	$d x B $.
	frabss2_0 $f wff ph $.
	frabss2_1 $f set x $.
	frabss2_2 $f class A $.
	frabss2_3 $f class B $.
	rabss2 $p |- ( A C_ B -> { x e. A | ph } C_ { x e. B | ph } ) $= frabss2_2 frabss2_3 wss frabss2_1 cv frabss2_2 wcel frabss2_0 wa frabss2_1 cab frabss2_1 cv frabss2_3 wcel frabss2_0 wa frabss2_1 cab frabss2_0 frabss2_1 frabss2_2 crab frabss2_0 frabss2_1 frabss2_3 crab frabss2_1 cv frabss2_2 wcel frabss2_1 cv frabss2_3 wcel wi frabss2_1 wal frabss2_1 cv frabss2_2 wcel frabss2_0 wa frabss2_1 cv frabss2_3 wcel frabss2_0 wa wi frabss2_1 wal frabss2_2 frabss2_3 wss frabss2_1 cv frabss2_2 wcel frabss2_0 wa frabss2_1 cab frabss2_1 cv frabss2_3 wcel frabss2_0 wa frabss2_1 cab wss frabss2_1 cv frabss2_2 wcel frabss2_1 cv frabss2_3 wcel wi frabss2_1 cv frabss2_2 wcel frabss2_0 wa frabss2_1 cv frabss2_3 wcel frabss2_0 wa wi frabss2_1 frabss2_1 cv frabss2_2 wcel frabss2_1 cv frabss2_3 wcel frabss2_0 pm3.45 alimi frabss2_1 frabss2_2 frabss2_3 dfss2 frabss2_1 cv frabss2_2 wcel frabss2_0 wa frabss2_1 cv frabss2_3 wcel frabss2_0 wa frabss2_1 ss2ab 3imtr4i frabss2_0 frabss2_1 frabss2_2 df-rab frabss2_0 frabss2_1 frabss2_3 df-rab 3sstr4g $.
$}
$( Subclass relation for the restriction of a class abstraction.
       (Contributed by NM, 31-Mar-1995.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fssab2_0 $f wff ph $.
	fssab2_1 $f set x $.
	fssab2_2 $f class A $.
	ssab2 $p |- { x | ( x e. A /\ ph ) } C_ A $= fssab2_1 cv fssab2_2 wcel fssab2_0 wa fssab2_1 fssab2_2 fssab2_1 cv fssab2_2 wcel fssab2_0 simpl abssi $.
$}
$( Subclass relation for a restricted class.  (Contributed by NM,
       19-Mar-1997.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$d x A $.
	fssrab2_0 $f wff ph $.
	fssrab2_1 $f set x $.
	fssrab2_2 $f class A $.
	ssrab2 $p |- { x e. A | ph } C_ A $= fssrab2_0 fssrab2_1 fssrab2_2 crab fssrab2_1 cv fssrab2_2 wcel fssrab2_0 wa fssrab2_1 cab fssrab2_2 fssrab2_0 fssrab2_1 fssrab2_2 df-rab fssrab2_0 fssrab2_1 fssrab2_2 ssab2 eqsstri $.
$}
$( A restricted class is a subclass of the corresponding unrestricted class.
     (Contributed by Mario Carneiro, 23-Dec-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	frabssab_0 $f wff ph $.
	frabssab_1 $f set x $.
	frabssab_2 $f class A $.
	rabssab $p |- { x e. A | ph } C_ { x | ph } $= frabssab_0 frabssab_1 frabssab_2 crab frabssab_1 cv frabssab_2 wcel frabssab_0 wa frabssab_1 cab frabssab_0 frabssab_1 cab frabssab_0 frabssab_1 frabssab_2 df-rab frabssab_1 cv frabssab_2 wcel frabssab_0 wa frabssab_0 frabssab_1 frabssab_1 cv frabssab_2 wcel frabssab_0 simpr ss2abi eqsstri $.
$}
$( A subset relationship useful for converting union to indexed union using
       ~ dfiun2 or ~ dfiun2g and intersection to indexed intersection using
       ~ dfiin2 .  (Contributed by NM, 5-Oct-2006.)  (Proof shortened by Mario
       Carneiro, 26-Sep-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$d x y $.
	$d y z A $.
	$d y z B $.
	$d x z C $.
	iuniiunlem_0 $f set z $.
	funiiunlem_0 $f set x $.
	funiiunlem_1 $f set y $.
	funiiunlem_2 $f class A $.
	funiiunlem_3 $f class B $.
	funiiunlem_4 $f class C $.
	funiiunlem_5 $f class D $.
	uniiunlem $p |- ( A. x e. A B e. D -> ( A. x e. A B e. C <-> { y | E. x e. A y = B } C_ C ) ) $= funiiunlem_1 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex funiiunlem_1 cab funiiunlem_4 wss iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_0 funiiunlem_2 wral funiiunlem_3 funiiunlem_5 wcel funiiunlem_0 funiiunlem_2 wral funiiunlem_3 funiiunlem_4 wcel funiiunlem_0 funiiunlem_2 wral funiiunlem_1 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex funiiunlem_1 cab funiiunlem_4 wss iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 cab funiiunlem_4 wss iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_0 funiiunlem_2 wral funiiunlem_1 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex funiiunlem_1 cab iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 cab funiiunlem_4 funiiunlem_1 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex funiiunlem_1 iuniiunlem_0 funiiunlem_1 cv iuniiunlem_0 cv wceq funiiunlem_1 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 funiiunlem_1 cv iuniiunlem_0 cv funiiunlem_3 eqeq1 rexbidv cbvabv sseq1i iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi funiiunlem_0 funiiunlem_2 wral iuniiunlem_0 wal iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_0 funiiunlem_2 wral iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 cab funiiunlem_4 wss iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi funiiunlem_0 funiiunlem_2 wral iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel funiiunlem_0 funiiunlem_2 r19.23v albii iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi funiiunlem_0 iuniiunlem_0 funiiunlem_2 ralcom4 iuniiunlem_0 cv funiiunlem_3 wceq funiiunlem_0 funiiunlem_2 wrex iuniiunlem_0 funiiunlem_4 abss 3bitr4i bitr4i funiiunlem_3 funiiunlem_5 wcel funiiunlem_0 funiiunlem_2 wral iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_3 funiiunlem_4 wcel wb funiiunlem_0 funiiunlem_2 wral iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_0 funiiunlem_2 wral funiiunlem_3 funiiunlem_4 wcel funiiunlem_0 funiiunlem_2 wral wb funiiunlem_3 funiiunlem_5 wcel iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_3 funiiunlem_4 wcel wb funiiunlem_0 funiiunlem_2 iuniiunlem_0 cv funiiunlem_4 wcel funiiunlem_3 funiiunlem_4 wcel iuniiunlem_0 funiiunlem_3 funiiunlem_5 funiiunlem_3 funiiunlem_4 wcel iuniiunlem_0 nfv iuniiunlem_0 cv funiiunlem_3 funiiunlem_4 eleq1 ceqsalg ralimi iuniiunlem_0 cv funiiunlem_3 wceq iuniiunlem_0 cv funiiunlem_4 wcel wi iuniiunlem_0 wal funiiunlem_3 funiiunlem_4 wcel funiiunlem_0 funiiunlem_2 ralbi syl syl5rbb $.
$}
$( Alternate definition of proper subclass.  (Contributed by NM,
     7-Feb-1996.) $)
${
	$v A $.
	$v B $.
	fdfpss2_0 $f class A $.
	fdfpss2_1 $f class B $.
	dfpss2 $p |- ( A C. B <-> ( A C_ B /\ -. A = B ) ) $= fdfpss2_0 fdfpss2_1 wpss fdfpss2_0 fdfpss2_1 wss fdfpss2_0 fdfpss2_1 wne wa fdfpss2_0 fdfpss2_1 wss fdfpss2_0 fdfpss2_1 wceq wn wa fdfpss2_0 fdfpss2_1 df-pss fdfpss2_0 fdfpss2_1 wne fdfpss2_0 fdfpss2_1 wceq wn fdfpss2_0 fdfpss2_1 wss fdfpss2_0 fdfpss2_1 df-ne anbi2i bitri $.
$}
$( Alternate definition of proper subclass.  (Contributed by NM,
     7-Feb-1996.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	fdfpss3_0 $f class A $.
	fdfpss3_1 $f class B $.
	dfpss3 $p |- ( A C. B <-> ( A C_ B /\ -. B C_ A ) ) $= fdfpss3_0 fdfpss3_1 wpss fdfpss3_0 fdfpss3_1 wss fdfpss3_0 fdfpss3_1 wceq wn wa fdfpss3_0 fdfpss3_1 wss fdfpss3_1 fdfpss3_0 wss wn wa fdfpss3_0 fdfpss3_1 dfpss2 fdfpss3_0 fdfpss3_1 wss fdfpss3_0 fdfpss3_1 wceq wn fdfpss3_1 fdfpss3_0 wss wn fdfpss3_0 fdfpss3_1 wss fdfpss3_0 fdfpss3_1 wceq fdfpss3_1 fdfpss3_0 wss fdfpss3_0 fdfpss3_1 wceq fdfpss3_0 fdfpss3_1 wss fdfpss3_1 fdfpss3_0 wss fdfpss3_0 fdfpss3_1 eqss baib notbid pm5.32i bitri $.
$}
$( Equality theorem for proper subclass.  (Contributed by NM, 7-Feb-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpsseq1_0 $f class A $.
	fpsseq1_1 $f class B $.
	fpsseq1_2 $f class C $.
	psseq1 $p |- ( A = B -> ( A C. C <-> B C. C ) ) $= fpsseq1_0 fpsseq1_1 wceq fpsseq1_0 fpsseq1_2 wss fpsseq1_0 fpsseq1_2 wne wa fpsseq1_1 fpsseq1_2 wss fpsseq1_1 fpsseq1_2 wne wa fpsseq1_0 fpsseq1_2 wpss fpsseq1_1 fpsseq1_2 wpss fpsseq1_0 fpsseq1_1 wceq fpsseq1_0 fpsseq1_2 wss fpsseq1_1 fpsseq1_2 wss fpsseq1_0 fpsseq1_2 wne fpsseq1_1 fpsseq1_2 wne fpsseq1_0 fpsseq1_1 fpsseq1_2 sseq1 fpsseq1_0 fpsseq1_1 fpsseq1_2 neeq1 anbi12d fpsseq1_0 fpsseq1_2 df-pss fpsseq1_1 fpsseq1_2 df-pss 3bitr4g $.
$}
$( Equality theorem for proper subclass.  (Contributed by NM, 7-Feb-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpsseq2_0 $f class A $.
	fpsseq2_1 $f class B $.
	fpsseq2_2 $f class C $.
	psseq2 $p |- ( A = B -> ( C C. A <-> C C. B ) ) $= fpsseq2_0 fpsseq2_1 wceq fpsseq2_2 fpsseq2_0 wss fpsseq2_2 fpsseq2_0 wne wa fpsseq2_2 fpsseq2_1 wss fpsseq2_2 fpsseq2_1 wne wa fpsseq2_2 fpsseq2_0 wpss fpsseq2_2 fpsseq2_1 wpss fpsseq2_0 fpsseq2_1 wceq fpsseq2_2 fpsseq2_0 wss fpsseq2_2 fpsseq2_1 wss fpsseq2_2 fpsseq2_0 wne fpsseq2_2 fpsseq2_1 wne fpsseq2_0 fpsseq2_1 fpsseq2_2 sseq2 fpsseq2_0 fpsseq2_1 fpsseq2_2 neeq2 anbi12d fpsseq2_2 fpsseq2_0 df-pss fpsseq2_2 fpsseq2_1 df-pss 3bitr4g $.
$}
$( An equality inference for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpsseq1i_0 $f class A $.
	fpsseq1i_1 $f class B $.
	fpsseq1i_2 $f class C $.
	epsseq1i_0 $e |- A = B $.
	psseq1i $p |- ( A C. C <-> B C. C ) $= fpsseq1i_0 fpsseq1i_1 wceq fpsseq1i_0 fpsseq1i_2 wpss fpsseq1i_1 fpsseq1i_2 wpss wb epsseq1i_0 fpsseq1i_0 fpsseq1i_1 fpsseq1i_2 psseq1 ax-mp $.
$}
$( An equality inference for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpsseq2i_0 $f class A $.
	fpsseq2i_1 $f class B $.
	fpsseq2i_2 $f class C $.
	epsseq2i_0 $e |- A = B $.
	psseq2i $p |- ( C C. A <-> C C. B ) $= fpsseq2i_0 fpsseq2i_1 wceq fpsseq2i_2 fpsseq2i_0 wpss fpsseq2i_2 fpsseq2i_1 wpss wb epsseq2i_0 fpsseq2i_0 fpsseq2i_1 fpsseq2i_2 psseq2 ax-mp $.
$}
$( An equality inference for the proper subclass relationship.
         (Contributed by NM, 9-Jun-2004.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fpsseq12i_0 $f class A $.
	fpsseq12i_1 $f class B $.
	fpsseq12i_2 $f class C $.
	fpsseq12i_3 $f class D $.
	epsseq12i_0 $e |- A = B $.
	epsseq12i_1 $e |- C = D $.
	psseq12i $p |- ( A C. C <-> B C. D ) $= fpsseq12i_0 fpsseq12i_2 wpss fpsseq12i_1 fpsseq12i_2 wpss fpsseq12i_1 fpsseq12i_3 wpss fpsseq12i_0 fpsseq12i_1 fpsseq12i_2 epsseq12i_0 psseq1i fpsseq12i_2 fpsseq12i_3 fpsseq12i_1 epsseq12i_1 psseq2i bitri $.
$}
$( An equality deduction for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fpsseq1d_0 $f wff ph $.
	fpsseq1d_1 $f class A $.
	fpsseq1d_2 $f class B $.
	fpsseq1d_3 $f class C $.
	epsseq1d_0 $e |- ( ph -> A = B ) $.
	psseq1d $p |- ( ph -> ( A C. C <-> B C. C ) ) $= fpsseq1d_0 fpsseq1d_1 fpsseq1d_2 wceq fpsseq1d_1 fpsseq1d_3 wpss fpsseq1d_2 fpsseq1d_3 wpss wb epsseq1d_0 fpsseq1d_1 fpsseq1d_2 fpsseq1d_3 psseq1 syl $.
$}
$( An equality deduction for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fpsseq2d_0 $f wff ph $.
	fpsseq2d_1 $f class A $.
	fpsseq2d_2 $f class B $.
	fpsseq2d_3 $f class C $.
	epsseq2d_0 $e |- ( ph -> A = B ) $.
	psseq2d $p |- ( ph -> ( C C. A <-> C C. B ) ) $= fpsseq2d_0 fpsseq2d_1 fpsseq2d_2 wceq fpsseq2d_3 fpsseq2d_1 wpss fpsseq2d_3 fpsseq2d_2 wpss wb epsseq2d_0 fpsseq2d_1 fpsseq2d_2 fpsseq2d_3 psseq2 syl $.
$}
$( An equality deduction for the proper subclass relationship.
         (Contributed by NM, 9-Jun-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fpsseq12d_0 $f wff ph $.
	fpsseq12d_1 $f class A $.
	fpsseq12d_2 $f class B $.
	fpsseq12d_3 $f class C $.
	fpsseq12d_4 $f class D $.
	epsseq12d_0 $e |- ( ph -> A = B ) $.
	epsseq12d_1 $e |- ( ph -> C = D ) $.
	psseq12d $p |- ( ph -> ( A C. C <-> B C. D ) ) $= fpsseq12d_0 fpsseq12d_1 fpsseq12d_3 wpss fpsseq12d_2 fpsseq12d_3 wpss fpsseq12d_2 fpsseq12d_4 wpss fpsseq12d_0 fpsseq12d_1 fpsseq12d_2 fpsseq12d_3 epsseq12d_0 psseq1d fpsseq12d_0 fpsseq12d_3 fpsseq12d_4 fpsseq12d_2 epsseq12d_1 psseq2d bitrd $.
$}
$( A proper subclass is a subclass.  Theorem 10 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)
${
	$v A $.
	$v B $.
	fpssss_0 $f class A $.
	fpssss_1 $f class B $.
	pssss $p |- ( A C. B -> A C_ B ) $= fpssss_0 fpssss_1 wpss fpssss_0 fpssss_1 wss fpssss_0 fpssss_1 wne fpssss_0 fpssss_1 df-pss simplbi $.
$}
$( Two classes in a proper subclass relationship are not equal.  (Contributed
     by NM, 16-Feb-2015.) $)
${
	$v A $.
	$v B $.
	fpssne_0 $f class A $.
	fpssne_1 $f class B $.
	pssne $p |- ( A C. B -> A =/= B ) $= fpssne_0 fpssne_1 wpss fpssne_0 fpssne_1 wss fpssne_0 fpssne_1 wne fpssne_0 fpssne_1 df-pss simprbi $.
$}
$( Deduce subclass from proper subclass.  (Contributed by NM,
       29-Feb-1996.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fpssssd_0 $f wff ph $.
	fpssssd_1 $f class A $.
	fpssssd_2 $f class B $.
	epssssd_0 $e |- ( ph -> A C. B ) $.
	pssssd $p |- ( ph -> A C_ B ) $= fpssssd_0 fpssssd_1 fpssssd_2 wpss fpssssd_1 fpssssd_2 wss epssssd_0 fpssssd_1 fpssssd_2 pssss syl $.
$}
$( Proper subclasses are unequal.  Deduction form of ~ pssne .
       (Contributed by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fpssned_0 $f wff ph $.
	fpssned_1 $f class A $.
	fpssned_2 $f class B $.
	epssned_0 $e |- ( ph -> A C. B ) $.
	pssned $p |- ( ph -> A =/= B ) $= fpssned_0 fpssned_1 fpssned_2 wpss fpssned_1 fpssned_2 wne epssned_0 fpssned_1 fpssned_2 pssne syl $.
$}
$( Subclass in terms of proper subclass.  (Contributed by NM,
     25-Feb-1996.) $)
${
	$v A $.
	$v B $.
	fsspss_0 $f class A $.
	fsspss_1 $f class B $.
	sspss $p |- ( A C_ B <-> ( A C. B \/ A = B ) ) $= fsspss_0 fsspss_1 wss fsspss_0 fsspss_1 wpss fsspss_0 fsspss_1 wceq wo fsspss_0 fsspss_1 wss fsspss_0 fsspss_1 wpss fsspss_0 fsspss_1 wceq fsspss_0 fsspss_1 wss fsspss_0 fsspss_1 wceq fsspss_0 fsspss_1 wpss fsspss_0 fsspss_1 wpss fsspss_0 fsspss_1 wss fsspss_0 fsspss_1 wceq wn fsspss_0 fsspss_1 dfpss2 simplbi2 con1d orrd fsspss_0 fsspss_1 wpss fsspss_0 fsspss_1 wss fsspss_0 fsspss_1 wceq fsspss_0 fsspss_1 pssss fsspss_0 fsspss_1 eqimss jaoi impbii $.
$}
$( Proper subclass is irreflexive.  Theorem 7 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)
${
	$v A $.
	fpssirr_0 $f class A $.
	pssirr $p |- -. A C. A $= fpssirr_0 fpssirr_0 wpss fpssirr_0 fpssirr_0 wss fpssirr_0 fpssirr_0 wss wn wa fpssirr_0 fpssirr_0 wss pm3.24 fpssirr_0 fpssirr_0 dfpss3 mtbir $.
$}
$( Proper subclass has no 2-cycle loops.  Compare Theorem 8 of [Suppes]
     p. 23.  (Contributed by NM, 7-Feb-1996.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	fpssn2lp_0 $f class A $.
	fpssn2lp_1 $f class B $.
	pssn2lp $p |- -. ( A C. B /\ B C. A ) $= fpssn2lp_0 fpssn2lp_1 wpss fpssn2lp_1 fpssn2lp_0 wpss wn wi fpssn2lp_0 fpssn2lp_1 wpss fpssn2lp_1 fpssn2lp_0 wpss wa wn fpssn2lp_0 fpssn2lp_1 wpss fpssn2lp_1 fpssn2lp_0 wss fpssn2lp_1 fpssn2lp_0 wpss fpssn2lp_0 fpssn2lp_1 wpss fpssn2lp_0 fpssn2lp_1 wss fpssn2lp_1 fpssn2lp_0 wss wn fpssn2lp_0 fpssn2lp_1 dfpss3 simprbi fpssn2lp_1 fpssn2lp_0 pssss nsyl fpssn2lp_0 fpssn2lp_1 wpss fpssn2lp_1 fpssn2lp_0 wpss imnan mpbi $.
$}
$( Two ways of stating trichotomy with respect to inclusion.  (Contributed by
     NM, 12-Aug-2004.) $)
${
	$v A $.
	$v B $.
	fsspsstri_0 $f class A $.
	fsspsstri_1 $f class B $.
	sspsstri $p |- ( ( A C_ B \/ B C_ A ) <-> ( A C. B \/ A = B \/ B C. A ) ) $= fsspsstri_0 fsspsstri_1 wpss fsspsstri_1 fsspsstri_0 wpss wo fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_0 fsspsstri_1 wpss fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_1 fsspsstri_0 wpss wo fsspsstri_0 fsspsstri_1 wss fsspsstri_1 fsspsstri_0 wss wo fsspsstri_0 fsspsstri_1 wpss fsspsstri_0 fsspsstri_1 wceq fsspsstri_1 fsspsstri_0 wpss w3o fsspsstri_0 fsspsstri_1 wpss fsspsstri_1 fsspsstri_0 wpss fsspsstri_0 fsspsstri_1 wceq or32 fsspsstri_0 fsspsstri_1 wss fsspsstri_1 fsspsstri_0 wss wo fsspsstri_0 fsspsstri_1 wpss fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_1 fsspsstri_0 wpss fsspsstri_0 fsspsstri_1 wceq wo wo fsspsstri_0 fsspsstri_1 wpss fsspsstri_1 fsspsstri_0 wpss wo fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_0 fsspsstri_1 wss fsspsstri_0 fsspsstri_1 wpss fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_1 fsspsstri_0 wss fsspsstri_1 fsspsstri_0 wpss fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_0 fsspsstri_1 sspss fsspsstri_1 fsspsstri_0 wss fsspsstri_1 fsspsstri_0 wpss fsspsstri_1 fsspsstri_0 wceq wo fsspsstri_1 fsspsstri_0 wpss fsspsstri_0 fsspsstri_1 wceq wo fsspsstri_1 fsspsstri_0 sspss fsspsstri_1 fsspsstri_0 wceq fsspsstri_0 fsspsstri_1 wceq fsspsstri_1 fsspsstri_0 wpss fsspsstri_1 fsspsstri_0 eqcom orbi2i bitri orbi12i fsspsstri_0 fsspsstri_1 wpss fsspsstri_1 fsspsstri_0 wpss fsspsstri_0 fsspsstri_1 wceq orordir bitr4i fsspsstri_0 fsspsstri_1 wpss fsspsstri_0 fsspsstri_1 wceq fsspsstri_1 fsspsstri_0 wpss df-3or 3bitr4i $.
$}
$( Partial trichotomy law for subclasses.  (Contributed by NM, 16-May-1996.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
${
	$v A $.
	$v B $.
	fssnpss_0 $f class A $.
	fssnpss_1 $f class B $.
	ssnpss $p |- ( A C_ B -> -. B C. A ) $= fssnpss_1 fssnpss_0 wpss fssnpss_0 fssnpss_1 wss fssnpss_1 fssnpss_0 wpss fssnpss_1 fssnpss_0 wss fssnpss_0 fssnpss_1 wss wn fssnpss_1 fssnpss_0 dfpss3 simprbi con2i $.
$}
$( Transitive law for proper subclass.  Theorem 9 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpsstr_0 $f class A $.
	fpsstr_1 $f class B $.
	fpsstr_2 $f class C $.
	psstr $p |- ( ( A C. B /\ B C. C ) -> A C. C ) $= fpsstr_0 fpsstr_1 wpss fpsstr_1 fpsstr_2 wpss wa fpsstr_0 fpsstr_2 wss fpsstr_0 fpsstr_2 wceq wn fpsstr_0 fpsstr_2 wpss fpsstr_0 fpsstr_1 wpss fpsstr_1 fpsstr_2 wpss fpsstr_0 fpsstr_1 fpsstr_2 fpsstr_0 fpsstr_1 pssss fpsstr_1 fpsstr_2 pssss sylan9ss fpsstr_0 fpsstr_2 wceq fpsstr_0 fpsstr_1 wpss fpsstr_1 fpsstr_2 wpss wa fpsstr_0 fpsstr_2 wceq fpsstr_0 fpsstr_1 wpss fpsstr_1 fpsstr_2 wpss wa fpsstr_2 fpsstr_1 wpss fpsstr_1 fpsstr_2 wpss wa fpsstr_2 fpsstr_1 pssn2lp fpsstr_0 fpsstr_2 wceq fpsstr_0 fpsstr_1 wpss fpsstr_2 fpsstr_1 wpss fpsstr_1 fpsstr_2 wpss fpsstr_0 fpsstr_2 fpsstr_1 psseq1 anbi1d mtbiri con2i fpsstr_0 fpsstr_2 dfpss2 sylanbrc $.
$}
$( Transitive law for subclass and proper subclass.  (Contributed by NM,
     3-Apr-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fsspsstr_0 $f class A $.
	fsspsstr_1 $f class B $.
	fsspsstr_2 $f class C $.
	sspsstr $p |- ( ( A C_ B /\ B C. C ) -> A C. C ) $= fsspsstr_0 fsspsstr_1 wss fsspsstr_0 fsspsstr_1 wpss fsspsstr_0 fsspsstr_1 wceq wo fsspsstr_1 fsspsstr_2 wpss fsspsstr_0 fsspsstr_2 wpss fsspsstr_0 fsspsstr_1 sspss fsspsstr_0 fsspsstr_1 wpss fsspsstr_0 fsspsstr_1 wceq wo fsspsstr_1 fsspsstr_2 wpss fsspsstr_0 fsspsstr_2 wpss fsspsstr_0 fsspsstr_1 wpss fsspsstr_1 fsspsstr_2 wpss fsspsstr_0 fsspsstr_2 wpss wi fsspsstr_0 fsspsstr_1 wceq fsspsstr_0 fsspsstr_1 wpss fsspsstr_1 fsspsstr_2 wpss fsspsstr_0 fsspsstr_2 wpss fsspsstr_0 fsspsstr_1 fsspsstr_2 psstr ex fsspsstr_0 fsspsstr_1 wceq fsspsstr_0 fsspsstr_2 wpss fsspsstr_1 fsspsstr_2 wpss fsspsstr_0 fsspsstr_1 fsspsstr_2 psseq1 biimprd jaoi imp sylanb $.
$}
$( Transitive law for subclass and proper subclass.  (Contributed by NM,
     3-Apr-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpsssstr_0 $f class A $.
	fpsssstr_1 $f class B $.
	fpsssstr_2 $f class C $.
	psssstr $p |- ( ( A C. B /\ B C_ C ) -> A C. C ) $= fpsssstr_1 fpsssstr_2 wss fpsssstr_0 fpsssstr_1 wpss fpsssstr_1 fpsssstr_2 wpss fpsssstr_1 fpsssstr_2 wceq wo fpsssstr_0 fpsssstr_2 wpss fpsssstr_1 fpsssstr_2 sspss fpsssstr_0 fpsssstr_1 wpss fpsssstr_1 fpsssstr_2 wpss fpsssstr_1 fpsssstr_2 wceq wo fpsssstr_0 fpsssstr_2 wpss fpsssstr_0 fpsssstr_1 wpss fpsssstr_1 fpsssstr_2 wpss fpsssstr_0 fpsssstr_2 wpss fpsssstr_1 fpsssstr_2 wceq fpsssstr_0 fpsssstr_1 wpss fpsssstr_1 fpsssstr_2 wpss fpsssstr_0 fpsssstr_2 wpss fpsssstr_0 fpsssstr_1 fpsssstr_2 psstr ex fpsssstr_1 fpsssstr_2 wceq fpsssstr_0 fpsssstr_1 wpss fpsssstr_0 fpsssstr_2 wpss fpsssstr_1 fpsssstr_2 fpsssstr_0 psseq2 biimpcd jaod imp sylan2b $.
$}
$( Proper subclass inclusion is transitive.  Deduction form of ~ psstr .
       (Contributed by David Moews, 1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fpsstrd_0 $f wff ph $.
	fpsstrd_1 $f class A $.
	fpsstrd_2 $f class B $.
	fpsstrd_3 $f class C $.
	epsstrd_0 $e |- ( ph -> A C. B ) $.
	epsstrd_1 $e |- ( ph -> B C. C ) $.
	psstrd $p |- ( ph -> A C. C ) $= fpsstrd_0 fpsstrd_1 fpsstrd_2 wpss fpsstrd_2 fpsstrd_3 wpss fpsstrd_1 fpsstrd_3 wpss epsstrd_0 epsstrd_1 fpsstrd_1 fpsstrd_2 fpsstrd_3 psstr syl2anc $.
$}
$( Transitivity involving subclass and proper subclass inclusion.
       Deduction form of ~ sspsstr .  (Contributed by David Moews,
       1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsspsstrd_0 $f wff ph $.
	fsspsstrd_1 $f class A $.
	fsspsstrd_2 $f class B $.
	fsspsstrd_3 $f class C $.
	esspsstrd_0 $e |- ( ph -> A C_ B ) $.
	esspsstrd_1 $e |- ( ph -> B C. C ) $.
	sspsstrd $p |- ( ph -> A C. C ) $= fsspsstrd_0 fsspsstrd_1 fsspsstrd_2 wss fsspsstrd_2 fsspsstrd_3 wpss fsspsstrd_1 fsspsstrd_3 wpss esspsstrd_0 esspsstrd_1 fsspsstrd_1 fsspsstrd_2 fsspsstrd_3 sspsstr syl2anc $.
$}
$( Transitivity involving subclass and proper subclass inclusion.
       Deduction form of ~ psssstr .  (Contributed by David Moews,
       1-May-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fpsssstrd_0 $f wff ph $.
	fpsssstrd_1 $f class A $.
	fpsssstrd_2 $f class B $.
	fpsssstrd_3 $f class C $.
	epsssstrd_0 $e |- ( ph -> A C. B ) $.
	epsssstrd_1 $e |- ( ph -> B C_ C ) $.
	psssstrd $p |- ( ph -> A C. C ) $= fpsssstrd_0 fpsssstrd_1 fpsssstrd_2 wpss fpsssstrd_2 fpsssstrd_3 wss fpsssstrd_1 fpsssstrd_3 wpss epsssstrd_0 epsssstrd_1 fpsssstrd_1 fpsssstrd_2 fpsssstrd_3 psssstr syl2anc $.
$}
$( A class is not a proper subclass of another iff it satisfies a
     one-directional form of ~ eqss .  (Contributed by Mario Carneiro,
     15-May-2015.) $)
${
	$v A $.
	$v B $.
	fnpss_0 $f class A $.
	fnpss_1 $f class B $.
	npss $p |- ( -. A C. B <-> ( A C_ B -> A = B ) ) $= fnpss_0 fnpss_1 wss fnpss_0 fnpss_1 wceq wi fnpss_0 fnpss_1 wpss fnpss_0 fnpss_1 wss fnpss_0 fnpss_1 wceq wi wn fnpss_0 fnpss_1 wss fnpss_0 fnpss_1 wceq wn wa fnpss_0 fnpss_1 wpss fnpss_0 fnpss_1 wss fnpss_0 fnpss_1 wceq pm4.61 fnpss_0 fnpss_1 dfpss2 bitr4i con1bii $.
$}

