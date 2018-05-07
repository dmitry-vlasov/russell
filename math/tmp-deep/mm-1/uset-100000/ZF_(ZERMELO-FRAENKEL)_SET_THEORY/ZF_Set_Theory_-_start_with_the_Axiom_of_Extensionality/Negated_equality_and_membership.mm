$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Class_form_not-free_predicate.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Negated equality and membership

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare new connectives. $)
$c =/=  $.
$( Not equal to (equal sign with slash through it). $)
$c e/  $.
$( Not an element of (epsilon with slash through it). $)
$( Extend wff notation to include inequality. $)
${
	$v A $.
	$v B $.
	fwne_0 $f class A $.
	fwne_1 $f class B $.
	wne $a wff A =/= B $.
$}
$( Extend wff notation to include negated membership. $)
${
	$v A $.
	$v B $.
	fwnel_0 $f class A $.
	fwnel_1 $f class B $.
	wnel $a wff A e/ B $.
$}
$( Define inequality.  (Contributed by NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	fdf-ne_0 $f class A $.
	fdf-ne_1 $f class B $.
	df-ne $a |- ( A =/= B <-> -. A = B ) $.
$}
$( Define negated membership.  (Contributed by NM, 7-Aug-1994.) $)
${
	$v A $.
	$v B $.
	fdf-nel_0 $f class A $.
	fdf-nel_1 $f class B $.
	df-nel $a |- ( A e/ B <-> -. A e. B ) $.
$}
$( Negation of inequality.  (Contributed by NM, 9-Jun-2006.) $)
${
	$v A $.
	$v B $.
	fnne_0 $f class A $.
	fnne_1 $f class B $.
	nne $p |- ( -. A =/= B <-> A = B ) $= fnne_0 fnne_1 wceq fnne_0 fnne_1 wne wn fnne_0 fnne_1 wne fnne_0 fnne_1 wceq fnne_0 fnne_1 df-ne con2bii bicomi $.
$}
$( No class is unequal to itself.  (Contributed by Stefan O'Rear,
     1-Jan-2015.) $)
${
	$v A $.
	fneirr_0 $f class A $.
	neirr $p |- -. A =/= A $= fneirr_0 fneirr_0 wne wn fneirr_0 fneirr_0 wceq fneirr_0 eqid fneirr_0 fneirr_0 nne mpbir $.
$}
$( Excluded middle with equality and inequality.  (Contributed by NM,
     3-Feb-2012.) $)
${
	$v A $.
	$v B $.
	fexmidne_0 $f class A $.
	fexmidne_1 $f class B $.
	exmidne $p |- ( A = B \/ A =/= B ) $= fexmidne_0 fexmidne_1 wceq fexmidne_0 fexmidne_1 wne wo fexmidne_0 fexmidne_1 wceq fexmidne_0 fexmidne_1 wceq wn wo fexmidne_0 fexmidne_1 wceq exmid fexmidne_0 fexmidne_1 wne fexmidne_0 fexmidne_1 wceq wn fexmidne_0 fexmidne_1 wceq fexmidne_0 fexmidne_1 df-ne orbi2i mpbir $.
$}
$( Law of noncontradiction with equality and inequality.  (Contributed by NM,
     3-Feb-2012.) $)
${
	$v A $.
	$v B $.
	fnonconne_0 $f class A $.
	fnonconne_1 $f class B $.
	nonconne $p |- -. ( A = B /\ A =/= B ) $= fnonconne_0 fnonconne_1 wceq fnonconne_0 fnonconne_1 wne wa fnonconne_0 fnonconne_1 wceq fnonconne_0 fnonconne_1 wceq wn wa fnonconne_0 fnonconne_1 wceq pm3.24 fnonconne_0 fnonconne_1 wne fnonconne_0 fnonconne_1 wceq wn fnonconne_0 fnonconne_1 wceq fnonconne_0 fnonconne_1 df-ne anbi2i mtbir $.
$}
$( Equality theorem for inequality.  (Contributed by NM, 19-Nov-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneeq1_0 $f class A $.
	fneeq1_1 $f class B $.
	fneeq1_2 $f class C $.
	neeq1 $p |- ( A = B -> ( A =/= C <-> B =/= C ) ) $= fneeq1_0 fneeq1_1 wceq fneeq1_0 fneeq1_2 wceq wn fneeq1_1 fneeq1_2 wceq wn fneeq1_0 fneeq1_2 wne fneeq1_1 fneeq1_2 wne fneeq1_0 fneeq1_1 wceq fneeq1_0 fneeq1_2 wceq fneeq1_1 fneeq1_2 wceq fneeq1_0 fneeq1_1 fneeq1_2 eqeq1 notbid fneeq1_0 fneeq1_2 df-ne fneeq1_1 fneeq1_2 df-ne 3bitr4g $.
$}
$( Equality theorem for inequality.  (Contributed by NM, 19-Nov-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneeq2_0 $f class A $.
	fneeq2_1 $f class B $.
	fneeq2_2 $f class C $.
	neeq2 $p |- ( A = B -> ( C =/= A <-> C =/= B ) ) $= fneeq2_0 fneeq2_1 wceq fneeq2_2 fneeq2_0 wceq wn fneeq2_2 fneeq2_1 wceq wn fneeq2_2 fneeq2_0 wne fneeq2_2 fneeq2_1 wne fneeq2_0 fneeq2_1 wceq fneeq2_2 fneeq2_0 wceq fneeq2_2 fneeq2_1 wceq fneeq2_0 fneeq2_1 fneeq2_2 eqeq2 notbid fneeq2_2 fneeq2_0 df-ne fneeq2_2 fneeq2_1 df-ne 3bitr4g $.
$}
$( Inference for inequality.  (Contributed by NM, 29-Apr-2005.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneeq1i_0 $f class A $.
	fneeq1i_1 $f class B $.
	fneeq1i_2 $f class C $.
	eneeq1i_0 $e |- A = B $.
	neeq1i $p |- ( A =/= C <-> B =/= C ) $= fneeq1i_0 fneeq1i_1 wceq fneeq1i_0 fneeq1i_2 wne fneeq1i_1 fneeq1i_2 wne wb eneeq1i_0 fneeq1i_0 fneeq1i_1 fneeq1i_2 neeq1 ax-mp $.
$}
$( Inference for inequality.  (Contributed by NM, 29-Apr-2005.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneeq2i_0 $f class A $.
	fneeq2i_1 $f class B $.
	fneeq2i_2 $f class C $.
	eneeq2i_0 $e |- A = B $.
	neeq2i $p |- ( C =/= A <-> C =/= B ) $= fneeq2i_0 fneeq2i_1 wceq fneeq2i_2 fneeq2i_0 wne fneeq2i_2 fneeq2i_1 wne wb eneeq2i_0 fneeq2i_0 fneeq2i_1 fneeq2i_2 neeq2 ax-mp $.
$}
$( Inference for inequality.  (Contributed by NM, 24-Jul-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fneeq12i_0 $f class A $.
	fneeq12i_1 $f class B $.
	fneeq12i_2 $f class C $.
	fneeq12i_3 $f class D $.
	eneeq12i_0 $e |- A = B $.
	eneeq12i_1 $e |- C = D $.
	neeq12i $p |- ( A =/= C <-> B =/= D ) $= fneeq12i_0 fneeq12i_2 wne fneeq12i_0 fneeq12i_3 wne fneeq12i_1 fneeq12i_3 wne fneeq12i_2 fneeq12i_3 fneeq12i_0 eneeq12i_1 neeq2i fneeq12i_0 fneeq12i_1 fneeq12i_3 eneeq12i_0 neeq1i bitri $.
$}
$( Deduction for inequality.  (Contributed by NM, 25-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fneeq1d_0 $f wff ph $.
	fneeq1d_1 $f class A $.
	fneeq1d_2 $f class B $.
	fneeq1d_3 $f class C $.
	eneeq1d_0 $e |- ( ph -> A = B ) $.
	neeq1d $p |- ( ph -> ( A =/= C <-> B =/= C ) ) $= fneeq1d_0 fneeq1d_1 fneeq1d_2 wceq fneeq1d_1 fneeq1d_3 wne fneeq1d_2 fneeq1d_3 wne wb eneeq1d_0 fneeq1d_1 fneeq1d_2 fneeq1d_3 neeq1 syl $.
$}
$( Deduction for inequality.  (Contributed by NM, 25-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fneeq2d_0 $f wff ph $.
	fneeq2d_1 $f class A $.
	fneeq2d_2 $f class B $.
	fneeq2d_3 $f class C $.
	eneeq2d_0 $e |- ( ph -> A = B ) $.
	neeq2d $p |- ( ph -> ( C =/= A <-> C =/= B ) ) $= fneeq2d_0 fneeq2d_1 fneeq2d_2 wceq fneeq2d_3 fneeq2d_1 wne fneeq2d_3 fneeq2d_2 wne wb eneeq2d_0 fneeq2d_1 fneeq2d_2 fneeq2d_3 neeq2 syl $.
$}
$( Deduction for inequality.  (Contributed by NM, 24-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fneeq12d_0 $f wff ph $.
	fneeq12d_1 $f class A $.
	fneeq12d_2 $f class B $.
	fneeq12d_3 $f class C $.
	fneeq12d_4 $f class D $.
	eneeq12d_0 $e |- ( ph -> A = B ) $.
	eneeq12d_1 $e |- ( ph -> C = D ) $.
	neeq12d $p |- ( ph -> ( A =/= C <-> B =/= D ) ) $= fneeq12d_0 fneeq12d_1 fneeq12d_3 wne fneeq12d_2 fneeq12d_3 wne fneeq12d_2 fneeq12d_4 wne fneeq12d_0 fneeq12d_1 fneeq12d_2 fneeq12d_3 eneeq12d_0 neeq1d fneeq12d_0 fneeq12d_3 fneeq12d_4 fneeq12d_2 eneeq12d_1 neeq2d bitrd $.
$}
$( Deduction eliminating inequality definition.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fneneqd_0 $f wff ph $.
	fneneqd_1 $f class A $.
	fneneqd_2 $f class B $.
	eneneqd_0 $e |- ( ph -> A =/= B ) $.
	neneqd $p |- ( ph -> -. A = B ) $= fneneqd_0 fneneqd_1 fneneqd_2 wne fneneqd_1 fneneqd_2 wceq wn eneneqd_0 fneneqd_1 fneneqd_2 df-ne sylib $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feqnetri_0 $f class A $.
	feqnetri_1 $f class B $.
	feqnetri_2 $f class C $.
	eeqnetri_0 $e |- A = B $.
	eeqnetri_1 $e |- B =/= C $.
	eqnetri $p |- A =/= C $= feqnetri_0 feqnetri_2 wne feqnetri_1 feqnetri_2 wne eeqnetri_1 feqnetri_0 feqnetri_1 feqnetri_2 eeqnetri_0 neeq1i mpbir $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feqnetrd_0 $f wff ph $.
	feqnetrd_1 $f class A $.
	feqnetrd_2 $f class B $.
	feqnetrd_3 $f class C $.
	eeqnetrd_0 $e |- ( ph -> A = B ) $.
	eeqnetrd_1 $e |- ( ph -> B =/= C ) $.
	eqnetrd $p |- ( ph -> A =/= C ) $= feqnetrd_0 feqnetrd_1 feqnetrd_3 wne feqnetrd_2 feqnetrd_3 wne eeqnetrd_1 feqnetrd_0 feqnetrd_1 feqnetrd_2 feqnetrd_3 eeqnetrd_0 neeq1d mpbird $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	feqnetrri_0 $f class A $.
	feqnetrri_1 $f class B $.
	feqnetrri_2 $f class C $.
	eeqnetrri_0 $e |- A = B $.
	eeqnetrri_1 $e |- A =/= C $.
	eqnetrri $p |- B =/= C $= feqnetrri_1 feqnetrri_0 feqnetrri_2 feqnetrri_0 feqnetrri_1 eeqnetrri_0 eqcomi eeqnetrri_1 eqnetri $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	feqnetrrd_0 $f wff ph $.
	feqnetrrd_1 $f class A $.
	feqnetrrd_2 $f class B $.
	feqnetrrd_3 $f class C $.
	eeqnetrrd_0 $e |- ( ph -> A = B ) $.
	eeqnetrrd_1 $e |- ( ph -> A =/= C ) $.
	eqnetrrd $p |- ( ph -> B =/= C ) $= feqnetrrd_0 feqnetrrd_2 feqnetrrd_1 feqnetrrd_3 feqnetrrd_0 feqnetrrd_1 feqnetrrd_2 eeqnetrrd_0 eqcomd eeqnetrrd_1 eqnetrd $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneeqtri_0 $f class A $.
	fneeqtri_1 $f class B $.
	fneeqtri_2 $f class C $.
	eneeqtri_0 $e |- A =/= B $.
	eneeqtri_1 $e |- B = C $.
	neeqtri $p |- A =/= C $= fneeqtri_0 fneeqtri_1 wne fneeqtri_0 fneeqtri_2 wne eneeqtri_0 fneeqtri_1 fneeqtri_2 fneeqtri_0 eneeqtri_1 neeq2i mpbi $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fneeqtrd_0 $f wff ph $.
	fneeqtrd_1 $f class A $.
	fneeqtrd_2 $f class B $.
	fneeqtrd_3 $f class C $.
	eneeqtrd_0 $e |- ( ph -> A =/= B ) $.
	eneeqtrd_1 $e |- ( ph -> B = C ) $.
	neeqtrd $p |- ( ph -> A =/= C ) $= fneeqtrd_0 fneeqtrd_1 fneeqtrd_2 wne fneeqtrd_1 fneeqtrd_3 wne eneeqtrd_0 fneeqtrd_0 fneeqtrd_2 fneeqtrd_3 fneeqtrd_1 eneeqtrd_1 neeq2d mpbid $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneeqtrri_0 $f class A $.
	fneeqtrri_1 $f class B $.
	fneeqtrri_2 $f class C $.
	eneeqtrri_0 $e |- A =/= B $.
	eneeqtrri_1 $e |- C = B $.
	neeqtrri $p |- A =/= C $= fneeqtrri_0 fneeqtrri_1 fneeqtrri_2 eneeqtrri_0 fneeqtrri_2 fneeqtrri_1 eneeqtrri_1 eqcomi neeqtri $.
$}
$( Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fneeqtrrd_0 $f wff ph $.
	fneeqtrrd_1 $f class A $.
	fneeqtrrd_2 $f class B $.
	fneeqtrrd_3 $f class C $.
	eneeqtrrd_0 $e |- ( ph -> A =/= B ) $.
	eneeqtrrd_1 $e |- ( ph -> C = B ) $.
	neeqtrrd $p |- ( ph -> A =/= C ) $= fneeqtrrd_0 fneeqtrrd_1 fneeqtrrd_2 fneeqtrrd_3 eneeqtrrd_0 fneeqtrrd_0 fneeqtrrd_3 fneeqtrrd_2 eneeqtrrd_1 eqcomd neeqtrd $.
$}
$( B chained equality inference for inequality.  (Contributed by NM,
       6-Jun-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	fsyl5eqner_0 $f wff ph $.
	fsyl5eqner_1 $f class A $.
	fsyl5eqner_2 $f class B $.
	fsyl5eqner_3 $f class C $.
	esyl5eqner_0 $e |- B = A $.
	esyl5eqner_1 $e |- ( ph -> B =/= C ) $.
	syl5eqner $p |- ( ph -> A =/= C ) $= fsyl5eqner_0 fsyl5eqner_2 fsyl5eqner_3 wne fsyl5eqner_1 fsyl5eqner_3 wne esyl5eqner_1 fsyl5eqner_2 fsyl5eqner_1 fsyl5eqner_3 esyl5eqner_0 neeq1i sylib $.
$}
$( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3netr3d_0 $f wff ph $.
	f3netr3d_1 $f class A $.
	f3netr3d_2 $f class B $.
	f3netr3d_3 $f class C $.
	f3netr3d_4 $f class D $.
	e3netr3d_0 $e |- ( ph -> A =/= B ) $.
	e3netr3d_1 $e |- ( ph -> A = C ) $.
	e3netr3d_2 $e |- ( ph -> B = D ) $.
	3netr3d $p |- ( ph -> C =/= D ) $= f3netr3d_0 f3netr3d_1 f3netr3d_2 wne f3netr3d_3 f3netr3d_4 wne e3netr3d_0 f3netr3d_0 f3netr3d_1 f3netr3d_3 f3netr3d_2 f3netr3d_4 e3netr3d_1 e3netr3d_2 neeq12d mpbid $.
$}
$( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3netr4d_0 $f wff ph $.
	f3netr4d_1 $f class A $.
	f3netr4d_2 $f class B $.
	f3netr4d_3 $f class C $.
	f3netr4d_4 $f class D $.
	e3netr4d_0 $e |- ( ph -> A =/= B ) $.
	e3netr4d_1 $e |- ( ph -> C = A ) $.
	e3netr4d_2 $e |- ( ph -> D = B ) $.
	3netr4d $p |- ( ph -> C =/= D ) $= f3netr4d_0 f3netr4d_3 f3netr4d_4 wne f3netr4d_1 f3netr4d_2 wne e3netr4d_0 f3netr4d_0 f3netr4d_3 f3netr4d_1 f3netr4d_4 f3netr4d_2 e3netr4d_1 e3netr4d_2 neeq12d mpbird $.
$}
$( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3netr3g_0 $f wff ph $.
	f3netr3g_1 $f class A $.
	f3netr3g_2 $f class B $.
	f3netr3g_3 $f class C $.
	f3netr3g_4 $f class D $.
	e3netr3g_0 $e |- ( ph -> A =/= B ) $.
	e3netr3g_1 $e |- A = C $.
	e3netr3g_2 $e |- B = D $.
	3netr3g $p |- ( ph -> C =/= D ) $= f3netr3g_0 f3netr3g_1 f3netr3g_2 wne f3netr3g_3 f3netr3g_4 wne e3netr3g_0 f3netr3g_1 f3netr3g_3 f3netr3g_2 f3netr3g_4 e3netr3g_1 e3netr3g_2 neeq12i sylib $.
$}
$( Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 14-Jun-2012.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	f3netr4g_0 $f wff ph $.
	f3netr4g_1 $f class A $.
	f3netr4g_2 $f class B $.
	f3netr4g_3 $f class C $.
	f3netr4g_4 $f class D $.
	e3netr4g_0 $e |- ( ph -> A =/= B ) $.
	e3netr4g_1 $e |- C = A $.
	e3netr4g_2 $e |- D = B $.
	3netr4g $p |- ( ph -> C =/= D ) $= f3netr4g_0 f3netr4g_1 f3netr4g_2 wne f3netr4g_3 f3netr4g_4 wne e3netr4g_0 f3netr4g_3 f3netr4g_1 f3netr4g_4 f3netr4g_2 e3netr4g_1 e3netr4g_2 neeq12i sylibr $.
$}
$( Deduction from equality to inequality.  (Contributed by NM,
       9-Nov-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon3abii_0 $f wff ph $.
	fnecon3abii_1 $f class A $.
	fnecon3abii_2 $f class B $.
	enecon3abii_0 $e |- ( A = B <-> ph ) $.
	necon3abii $p |- ( A =/= B <-> -. ph ) $= fnecon3abii_1 fnecon3abii_2 wne fnecon3abii_1 fnecon3abii_2 wceq fnecon3abii_0 fnecon3abii_1 fnecon3abii_2 df-ne enecon3abii_0 xchbinx $.
$}
$( Deduction from equality to inequality.  (Contributed by NM,
       13-Apr-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon3bbii_0 $f wff ph $.
	fnecon3bbii_1 $f class A $.
	fnecon3bbii_2 $f class B $.
	enecon3bbii_0 $e |- ( ph <-> A = B ) $.
	necon3bbii $p |- ( -. ph <-> A =/= B ) $= fnecon3bbii_1 fnecon3bbii_2 wne fnecon3bbii_0 wn fnecon3bbii_0 fnecon3bbii_1 fnecon3bbii_2 fnecon3bbii_0 fnecon3bbii_1 fnecon3bbii_2 wceq enecon3bbii_0 bicomi necon3abii bicomi $.
$}
$( Inference from equality to inequality.  (Contributed by NM,
       23-Feb-2005.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon3bii_0 $f class A $.
	fnecon3bii_1 $f class B $.
	fnecon3bii_2 $f class C $.
	fnecon3bii_3 $f class D $.
	enecon3bii_0 $e |- ( A = B <-> C = D ) $.
	necon3bii $p |- ( A =/= B <-> C =/= D ) $= fnecon3bii_0 fnecon3bii_1 wne fnecon3bii_2 fnecon3bii_3 wceq wn fnecon3bii_2 fnecon3bii_3 wne fnecon3bii_2 fnecon3bii_3 wceq fnecon3bii_0 fnecon3bii_1 enecon3bii_0 necon3abii fnecon3bii_2 fnecon3bii_3 df-ne bitr4i $.
$}
$( Deduction from equality to inequality.  (Contributed by NM,
       21-Mar-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon3abid_0 $f wff ph $.
	fnecon3abid_1 $f wff ps $.
	fnecon3abid_2 $f class A $.
	fnecon3abid_3 $f class B $.
	enecon3abid_0 $e |- ( ph -> ( A = B <-> ps ) ) $.
	necon3abid $p |- ( ph -> ( A =/= B <-> -. ps ) ) $= fnecon3abid_2 fnecon3abid_3 wne fnecon3abid_2 fnecon3abid_3 wceq wn fnecon3abid_0 fnecon3abid_1 wn fnecon3abid_2 fnecon3abid_3 df-ne fnecon3abid_0 fnecon3abid_2 fnecon3abid_3 wceq fnecon3abid_1 enecon3abid_0 notbid syl5bb $.
$}
$( Deduction from equality to inequality.  (Contributed by NM,
       2-Jun-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon3bbid_0 $f wff ph $.
	fnecon3bbid_1 $f wff ps $.
	fnecon3bbid_2 $f class A $.
	fnecon3bbid_3 $f class B $.
	enecon3bbid_0 $e |- ( ph -> ( ps <-> A = B ) ) $.
	necon3bbid $p |- ( ph -> ( -. ps <-> A =/= B ) ) $= fnecon3bbid_0 fnecon3bbid_2 fnecon3bbid_3 wne fnecon3bbid_1 wn fnecon3bbid_0 fnecon3bbid_1 fnecon3bbid_2 fnecon3bbid_3 fnecon3bbid_0 fnecon3bbid_1 fnecon3bbid_2 fnecon3bbid_3 wceq enecon3bbid_0 bicomd necon3abid bicomd $.
$}
$( Deduction from equality to inequality.  (Contributed by NM,
       23-Feb-2005.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon3bid_0 $f wff ph $.
	fnecon3bid_1 $f class A $.
	fnecon3bid_2 $f class B $.
	fnecon3bid_3 $f class C $.
	fnecon3bid_4 $f class D $.
	enecon3bid_0 $e |- ( ph -> ( A = B <-> C = D ) ) $.
	necon3bid $p |- ( ph -> ( A =/= B <-> C =/= D ) ) $= fnecon3bid_1 fnecon3bid_2 wne fnecon3bid_1 fnecon3bid_2 wceq wn fnecon3bid_0 fnecon3bid_3 fnecon3bid_4 wne fnecon3bid_1 fnecon3bid_2 df-ne fnecon3bid_0 fnecon3bid_1 fnecon3bid_2 wceq fnecon3bid_3 fnecon3bid_4 enecon3bid_0 necon3bbid syl5bb $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon3ad_0 $f wff ph $.
	fnecon3ad_1 $f wff ps $.
	fnecon3ad_2 $f class A $.
	fnecon3ad_3 $f class B $.
	enecon3ad_0 $e |- ( ph -> ( ps -> A = B ) ) $.
	necon3ad $p |- ( ph -> ( A =/= B -> -. ps ) ) $= fnecon3ad_0 fnecon3ad_1 fnecon3ad_2 fnecon3ad_3 wne fnecon3ad_0 fnecon3ad_1 fnecon3ad_2 fnecon3ad_3 wceq fnecon3ad_2 fnecon3ad_3 wne wn enecon3ad_0 fnecon3ad_2 fnecon3ad_3 nne syl6ibr con2d $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon3bd_0 $f wff ph $.
	fnecon3bd_1 $f wff ps $.
	fnecon3bd_2 $f class A $.
	fnecon3bd_3 $f class B $.
	enecon3bd_0 $e |- ( ph -> ( A = B -> ps ) ) $.
	necon3bd $p |- ( ph -> ( -. ps -> A =/= B ) ) $= fnecon3bd_0 fnecon3bd_2 fnecon3bd_3 wne fnecon3bd_1 fnecon3bd_2 fnecon3bd_3 wne wn fnecon3bd_2 fnecon3bd_3 wceq fnecon3bd_0 fnecon3bd_1 fnecon3bd_2 fnecon3bd_3 nne enecon3bd_0 syl5bi con1d $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       10-Jun-2006.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon3d_0 $f wff ph $.
	fnecon3d_1 $f class A $.
	fnecon3d_2 $f class B $.
	fnecon3d_3 $f class C $.
	fnecon3d_4 $f class D $.
	enecon3d_0 $e |- ( ph -> ( A = B -> C = D ) ) $.
	necon3d $p |- ( ph -> ( C =/= D -> A =/= B ) ) $= fnecon3d_0 fnecon3d_3 fnecon3d_4 wne fnecon3d_1 fnecon3d_2 wceq wn fnecon3d_1 fnecon3d_2 wne fnecon3d_0 fnecon3d_1 fnecon3d_2 wceq fnecon3d_3 fnecon3d_4 enecon3d_0 necon3ad fnecon3d_1 fnecon3d_2 df-ne syl6ibr $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       9-Aug-2006.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon3i_0 $f class A $.
	fnecon3i_1 $f class B $.
	fnecon3i_2 $f class C $.
	fnecon3i_3 $f class D $.
	enecon3i_0 $e |- ( A = B -> C = D ) $.
	necon3i $p |- ( C =/= D -> A =/= B ) $= fnecon3i_0 fnecon3i_1 wceq fnecon3i_2 fnecon3i_3 wceq wi fnecon3i_2 fnecon3i_3 wne fnecon3i_0 fnecon3i_1 wne wi enecon3i_0 fnecon3i_0 fnecon3i_1 wceq fnecon3i_2 fnecon3i_3 wceq wi fnecon3i_0 fnecon3i_1 fnecon3i_2 fnecon3i_3 fnecon3i_0 fnecon3i_1 wceq fnecon3i_2 fnecon3i_3 wceq wi id necon3d ax-mp $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       23-May-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon3ai_0 $f wff ph $.
	fnecon3ai_1 $f class A $.
	fnecon3ai_2 $f class B $.
	enecon3ai_0 $e |- ( ph -> A = B ) $.
	necon3ai $p |- ( A =/= B -> -. ph ) $= fnecon3ai_0 fnecon3ai_1 fnecon3ai_2 wne fnecon3ai_0 fnecon3ai_1 fnecon3ai_2 wceq fnecon3ai_1 fnecon3ai_2 wne wn enecon3ai_0 fnecon3ai_1 fnecon3ai_2 nne sylibr con2i $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon3bi_0 $f wff ph $.
	fnecon3bi_1 $f class A $.
	fnecon3bi_2 $f class B $.
	enecon3bi_0 $e |- ( A = B -> ph ) $.
	necon3bi $p |- ( -. ph -> A =/= B ) $= fnecon3bi_1 fnecon3bi_2 wne fnecon3bi_0 fnecon3bi_1 fnecon3bi_2 wne wn fnecon3bi_1 fnecon3bi_2 wceq fnecon3bi_0 fnecon3bi_1 fnecon3bi_2 nne enecon3bi_0 sylbi con1i $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       12-Feb-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon1ai_0 $f wff ph $.
	fnecon1ai_1 $f class A $.
	fnecon1ai_2 $f class B $.
	enecon1ai_0 $e |- ( -. ph -> A = B ) $.
	necon1ai $p |- ( A =/= B -> ph ) $= fnecon1ai_1 fnecon1ai_2 wne fnecon1ai_1 fnecon1ai_2 wceq wn fnecon1ai_0 fnecon1ai_1 fnecon1ai_2 df-ne fnecon1ai_0 fnecon1ai_1 fnecon1ai_2 wceq enecon1ai_0 con1i sylbi $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon1bi_0 $f wff ph $.
	fnecon1bi_1 $f class A $.
	fnecon1bi_2 $f class B $.
	enecon1bi_0 $e |- ( A =/= B -> ph ) $.
	necon1bi $p |- ( -. ph -> A = B ) $= fnecon1bi_0 wn fnecon1bi_1 fnecon1bi_2 wne wn fnecon1bi_1 fnecon1bi_2 wceq fnecon1bi_1 fnecon1bi_2 wne fnecon1bi_0 enecon1bi_0 con3i fnecon1bi_1 fnecon1bi_2 nne sylib $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon1i_0 $f class A $.
	fnecon1i_1 $f class B $.
	fnecon1i_2 $f class C $.
	fnecon1i_3 $f class D $.
	enecon1i_0 $e |- ( A =/= B -> C = D ) $.
	necon1i $p |- ( C =/= D -> A = B ) $= fnecon1i_0 fnecon1i_1 wceq fnecon1i_2 fnecon1i_3 fnecon1i_0 fnecon1i_1 wceq wn fnecon1i_0 fnecon1i_1 wne fnecon1i_2 fnecon1i_3 wceq fnecon1i_0 fnecon1i_1 df-ne enecon1i_0 sylbir necon1ai $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon2ai_0 $f wff ph $.
	fnecon2ai_1 $f class A $.
	fnecon2ai_2 $f class B $.
	enecon2ai_0 $e |- ( A = B -> -. ph ) $.
	necon2ai $p |- ( ph -> A =/= B ) $= fnecon2ai_1 fnecon2ai_2 wne fnecon2ai_0 fnecon2ai_1 fnecon2ai_2 wne wn fnecon2ai_1 fnecon2ai_2 wceq fnecon2ai_0 wn fnecon2ai_1 fnecon2ai_2 nne enecon2ai_0 sylbi con4i $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       1-Apr-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon2bi_0 $f wff ph $.
	fnecon2bi_1 $f class A $.
	fnecon2bi_2 $f class B $.
	enecon2bi_0 $e |- ( ph -> A =/= B ) $.
	necon2bi $p |- ( A = B -> -. ph ) $= fnecon2bi_0 fnecon2bi_1 fnecon2bi_2 wceq fnecon2bi_0 fnecon2bi_1 fnecon2bi_2 enecon2bi_0 neneqd con2i $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon2i_0 $f class A $.
	fnecon2i_1 $f class B $.
	fnecon2i_2 $f class C $.
	fnecon2i_3 $f class D $.
	enecon2i_0 $e |- ( A = B -> C =/= D ) $.
	necon2i $p |- ( C = D -> A =/= B ) $= fnecon2i_2 fnecon2i_3 wceq fnecon2i_0 fnecon2i_1 fnecon2i_0 fnecon2i_1 wceq fnecon2i_2 fnecon2i_3 enecon2i_0 neneqd necon2ai $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       19-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon2ad_0 $f wff ph $.
	fnecon2ad_1 $f wff ps $.
	fnecon2ad_2 $f class A $.
	fnecon2ad_3 $f class B $.
	enecon2ad_0 $e |- ( ph -> ( A = B -> -. ps ) ) $.
	necon2ad $p |- ( ph -> ( ps -> A =/= B ) ) $= fnecon2ad_0 fnecon2ad_2 fnecon2ad_3 wne fnecon2ad_1 fnecon2ad_2 fnecon2ad_3 wne wn fnecon2ad_2 fnecon2ad_3 wceq fnecon2ad_0 fnecon2ad_1 wn fnecon2ad_2 fnecon2ad_3 nne enecon2ad_0 syl5bi con4d $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon2bd_0 $f wff ph $.
	fnecon2bd_1 $f wff ps $.
	fnecon2bd_2 $f class A $.
	fnecon2bd_3 $f class B $.
	enecon2bd_0 $e |- ( ph -> ( ps -> A =/= B ) ) $.
	necon2bd $p |- ( ph -> ( A = B -> -. ps ) ) $= fnecon2bd_0 fnecon2bd_1 fnecon2bd_2 fnecon2bd_3 wceq fnecon2bd_0 fnecon2bd_1 fnecon2bd_2 fnecon2bd_3 wne fnecon2bd_2 fnecon2bd_3 wceq wn enecon2bd_0 fnecon2bd_2 fnecon2bd_3 df-ne syl6ib con2d $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       28-Dec-2008.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon2d_0 $f wff ph $.
	fnecon2d_1 $f class A $.
	fnecon2d_2 $f class B $.
	fnecon2d_3 $f class C $.
	fnecon2d_4 $f class D $.
	enecon2d_0 $e |- ( ph -> ( A = B -> C =/= D ) ) $.
	necon2d $p |- ( ph -> ( C = D -> A =/= B ) ) $= fnecon2d_0 fnecon2d_3 fnecon2d_4 wceq fnecon2d_1 fnecon2d_2 fnecon2d_0 fnecon2d_1 fnecon2d_2 wceq fnecon2d_3 fnecon2d_4 wne fnecon2d_3 fnecon2d_4 wceq wn enecon2d_0 fnecon2d_3 fnecon2d_4 df-ne syl6ib necon2ad $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon1abii_0 $f wff ph $.
	fnecon1abii_1 $f class A $.
	fnecon1abii_2 $f class B $.
	enecon1abii_0 $e |- ( -. ph <-> A = B ) $.
	necon1abii $p |- ( A =/= B <-> ph ) $= fnecon1abii_1 fnecon1abii_2 wne fnecon1abii_1 fnecon1abii_2 wceq wn fnecon1abii_0 fnecon1abii_1 fnecon1abii_2 df-ne fnecon1abii_0 fnecon1abii_1 fnecon1abii_2 wceq enecon1abii_0 con1bii bitri $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon1bbii_0 $f wff ph $.
	fnecon1bbii_1 $f class A $.
	fnecon1bbii_2 $f class B $.
	enecon1bbii_0 $e |- ( A =/= B <-> ph ) $.
	necon1bbii $p |- ( -. ph <-> A = B ) $= fnecon1bbii_1 fnecon1bbii_2 wceq fnecon1bbii_0 fnecon1bbii_1 fnecon1bbii_2 wceq wn fnecon1bbii_1 fnecon1bbii_2 wne fnecon1bbii_0 fnecon1bbii_1 fnecon1bbii_2 df-ne enecon1bbii_0 bitr3i con1bii $.
$}
$( Contrapositive deduction for inequality.  (Contributed by NM,
       21-Aug-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon1abid_0 $f wff ph $.
	fnecon1abid_1 $f wff ps $.
	fnecon1abid_2 $f class A $.
	fnecon1abid_3 $f class B $.
	enecon1abid_0 $e |- ( ph -> ( -. ps <-> A = B ) ) $.
	necon1abid $p |- ( ph -> ( A =/= B <-> ps ) ) $= fnecon1abid_2 fnecon1abid_3 wne fnecon1abid_2 fnecon1abid_3 wceq wn fnecon1abid_0 fnecon1abid_1 fnecon1abid_2 fnecon1abid_3 df-ne fnecon1abid_0 fnecon1abid_1 fnecon1abid_2 fnecon1abid_3 wceq enecon1abid_0 con1bid syl5bb $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       31-Jan-2008.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon1bbid_0 $f wff ph $.
	fnecon1bbid_1 $f wff ps $.
	fnecon1bbid_2 $f class A $.
	fnecon1bbid_3 $f class B $.
	enecon1bbid_0 $e |- ( ph -> ( A =/= B <-> ps ) ) $.
	necon1bbid $p |- ( ph -> ( -. ps <-> A = B ) ) $= fnecon1bbid_0 fnecon1bbid_2 fnecon1bbid_3 wceq fnecon1bbid_1 fnecon1bbid_2 fnecon1bbid_3 wceq wn fnecon1bbid_2 fnecon1bbid_3 wne fnecon1bbid_0 fnecon1bbid_1 fnecon1bbid_2 fnecon1bbid_3 df-ne enecon1bbid_0 syl5bbr con1bid $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       2-Mar-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon2abii_0 $f wff ph $.
	fnecon2abii_1 $f class A $.
	fnecon2abii_2 $f class B $.
	enecon2abii_0 $e |- ( A = B <-> -. ph ) $.
	necon2abii $p |- ( ph <-> A =/= B ) $= fnecon2abii_1 fnecon2abii_2 wne fnecon2abii_0 fnecon2abii_0 fnecon2abii_1 fnecon2abii_2 fnecon2abii_1 fnecon2abii_2 wceq fnecon2abii_0 wn enecon2abii_0 bicomi necon1abii bicomi $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon2bbii_0 $f wff ph $.
	fnecon2bbii_1 $f class A $.
	fnecon2bbii_2 $f class B $.
	enecon2bbii_0 $e |- ( ph <-> A =/= B ) $.
	necon2bbii $p |- ( A = B <-> -. ph ) $= fnecon2bbii_0 wn fnecon2bbii_1 fnecon2bbii_2 wceq fnecon2bbii_0 fnecon2bbii_1 fnecon2bbii_2 fnecon2bbii_0 fnecon2bbii_1 fnecon2bbii_2 wne enecon2bbii_0 bicomi necon1bbii bicomi $.
$}
$( Contrapositive deduction for inequality.  (Contributed by NM,
       18-Jul-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon2abid_0 $f wff ph $.
	fnecon2abid_1 $f wff ps $.
	fnecon2abid_2 $f class A $.
	fnecon2abid_3 $f class B $.
	enecon2abid_0 $e |- ( ph -> ( A = B <-> -. ps ) ) $.
	necon2abid $p |- ( ph -> ( ps <-> A =/= B ) ) $= fnecon2abid_0 fnecon2abid_1 fnecon2abid_2 fnecon2abid_3 wceq wn fnecon2abid_2 fnecon2abid_3 wne fnecon2abid_0 fnecon2abid_2 fnecon2abid_3 wceq fnecon2abid_1 enecon2abid_0 con2bid fnecon2abid_2 fnecon2abid_3 df-ne syl6bbr $.
$}
$( Contrapositive deduction for inequality.  (Contributed by NM,
       13-Apr-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon2bbid_0 $f wff ph $.
	fnecon2bbid_1 $f wff ps $.
	fnecon2bbid_2 $f class A $.
	fnecon2bbid_3 $f class B $.
	enecon2bbid_0 $e |- ( ph -> ( ps <-> A =/= B ) ) $.
	necon2bbid $p |- ( ph -> ( A = B <-> -. ps ) ) $= fnecon2bbid_0 fnecon2bbid_1 fnecon2bbid_2 fnecon2bbid_3 wceq fnecon2bbid_0 fnecon2bbid_1 fnecon2bbid_2 fnecon2bbid_3 wne fnecon2bbid_2 fnecon2bbid_3 wceq wn enecon2bbid_0 fnecon2bbid_2 fnecon2bbid_3 df-ne syl6bb con2bid $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecon4ai_0 $f wff ph $.
	fnecon4ai_1 $f class A $.
	fnecon4ai_2 $f class B $.
	enecon4ai_0 $e |- ( A =/= B -> -. ph ) $.
	necon4ai $p |- ( ph -> A = B ) $= fnecon4ai_0 fnecon4ai_1 fnecon4ai_2 wne wn fnecon4ai_1 fnecon4ai_2 wceq fnecon4ai_1 fnecon4ai_2 wne fnecon4ai_0 enecon4ai_0 con2i fnecon4ai_1 fnecon4ai_2 nne sylib $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon4i_0 $f class A $.
	fnecon4i_1 $f class B $.
	fnecon4i_2 $f class C $.
	fnecon4i_3 $f class D $.
	enecon4i_0 $e |- ( A =/= B -> C =/= D ) $.
	necon4i $p |- ( C = D -> A = B ) $= fnecon4i_2 fnecon4i_3 wceq fnecon4i_0 fnecon4i_1 wne wn fnecon4i_0 fnecon4i_1 wceq fnecon4i_0 fnecon4i_1 wne fnecon4i_2 fnecon4i_3 enecon4i_0 necon2bi fnecon4i_0 fnecon4i_1 nne sylib $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon4ad_0 $f wff ph $.
	fnecon4ad_1 $f wff ps $.
	fnecon4ad_2 $f class A $.
	fnecon4ad_3 $f class B $.
	enecon4ad_0 $e |- ( ph -> ( A =/= B -> -. ps ) ) $.
	necon4ad $p |- ( ph -> ( ps -> A = B ) ) $= fnecon4ad_0 fnecon4ad_1 fnecon4ad_2 fnecon4ad_3 wne wn fnecon4ad_2 fnecon4ad_3 wceq fnecon4ad_0 fnecon4ad_2 fnecon4ad_3 wne fnecon4ad_1 enecon4ad_0 con2d fnecon4ad_2 fnecon4ad_3 nne syl6ib $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon4bd_0 $f wff ph $.
	fnecon4bd_1 $f wff ps $.
	fnecon4bd_2 $f class A $.
	fnecon4bd_3 $f class B $.
	enecon4bd_0 $e |- ( ph -> ( -. ps -> A =/= B ) ) $.
	necon4bd $p |- ( ph -> ( A = B -> ps ) ) $= fnecon4bd_2 fnecon4bd_3 wceq fnecon4bd_2 fnecon4bd_3 wne wn fnecon4bd_0 fnecon4bd_1 fnecon4bd_2 fnecon4bd_3 nne fnecon4bd_0 fnecon4bd_1 fnecon4bd_2 fnecon4bd_3 wne enecon4bd_0 con1d syl5bir $.
$}
$( Contrapositive inference for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon4d_0 $f wff ph $.
	fnecon4d_1 $f class A $.
	fnecon4d_2 $f class B $.
	fnecon4d_3 $f class C $.
	fnecon4d_4 $f class D $.
	enecon4d_0 $e |- ( ph -> ( A =/= B -> C =/= D ) ) $.
	necon4d $p |- ( ph -> ( C = D -> A = B ) ) $= fnecon4d_0 fnecon4d_3 fnecon4d_4 wceq fnecon4d_1 fnecon4d_2 wne wn fnecon4d_1 fnecon4d_2 wceq fnecon4d_0 fnecon4d_1 fnecon4d_2 wne fnecon4d_3 fnecon4d_4 enecon4d_0 necon2bd fnecon4d_1 fnecon4d_2 nne syl6ib $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       11-Jan-2008.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon4abid_0 $f wff ph $.
	fnecon4abid_1 $f wff ps $.
	fnecon4abid_2 $f class A $.
	fnecon4abid_3 $f class B $.
	enecon4abid_0 $e |- ( ph -> ( A =/= B <-> -. ps ) ) $.
	necon4abid $p |- ( ph -> ( A = B <-> ps ) ) $= fnecon4abid_0 fnecon4abid_2 fnecon4abid_3 wceq fnecon4abid_1 fnecon4abid_2 fnecon4abid_3 wceq wn fnecon4abid_2 fnecon4abid_3 wne fnecon4abid_0 fnecon4abid_1 wn fnecon4abid_2 fnecon4abid_3 df-ne enecon4abid_0 syl5bbr con4bid $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       9-May-2012.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon4bbid_0 $f wff ph $.
	fnecon4bbid_1 $f wff ps $.
	fnecon4bbid_2 $f class A $.
	fnecon4bbid_3 $f class B $.
	enecon4bbid_0 $e |- ( ph -> ( -. ps <-> A =/= B ) ) $.
	necon4bbid $p |- ( ph -> ( ps <-> A = B ) ) $= fnecon4bbid_0 fnecon4bbid_2 fnecon4bbid_3 wceq fnecon4bbid_1 fnecon4bbid_0 fnecon4bbid_1 fnecon4bbid_2 fnecon4bbid_3 fnecon4bbid_0 fnecon4bbid_1 wn fnecon4bbid_2 fnecon4bbid_3 wne enecon4bbid_0 bicomd necon4abid bicomd $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       29-Jun-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon4bid_0 $f wff ph $.
	fnecon4bid_1 $f class A $.
	fnecon4bid_2 $f class B $.
	fnecon4bid_3 $f class C $.
	fnecon4bid_4 $f class D $.
	enecon4bid_0 $e |- ( ph -> ( A =/= B <-> C =/= D ) ) $.
	necon4bid $p |- ( ph -> ( A = B <-> C = D ) ) $= fnecon4bid_0 fnecon4bid_3 fnecon4bid_4 wceq fnecon4bid_1 fnecon4bid_2 wne wn fnecon4bid_1 fnecon4bid_2 wceq fnecon4bid_0 fnecon4bid_1 fnecon4bid_2 wne fnecon4bid_3 fnecon4bid_4 enecon4bid_0 necon2bbid fnecon4bid_1 fnecon4bid_2 nne syl6rbb $.
$}
$( Contrapositive deduction for inequality.  (Contributed by NM,
       2-Apr-2007.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon1ad_0 $f wff ph $.
	fnecon1ad_1 $f wff ps $.
	fnecon1ad_2 $f class A $.
	fnecon1ad_3 $f class B $.
	enecon1ad_0 $e |- ( ph -> ( -. ps -> A = B ) ) $.
	necon1ad $p |- ( ph -> ( A =/= B -> ps ) ) $= fnecon1ad_2 fnecon1ad_3 wne fnecon1ad_2 fnecon1ad_3 wceq wn fnecon1ad_0 fnecon1ad_1 fnecon1ad_2 fnecon1ad_3 df-ne fnecon1ad_0 fnecon1ad_1 fnecon1ad_2 fnecon1ad_3 wceq enecon1ad_0 con1d syl5bi $.
$}
$( Contrapositive deduction for inequality.  (Contributed by NM,
       21-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fnecon1bd_0 $f wff ph $.
	fnecon1bd_1 $f wff ps $.
	fnecon1bd_2 $f class A $.
	fnecon1bd_3 $f class B $.
	enecon1bd_0 $e |- ( ph -> ( A =/= B -> ps ) ) $.
	necon1bd $p |- ( ph -> ( -. ps -> A = B ) ) $= fnecon1bd_0 fnecon1bd_1 wn fnecon1bd_2 fnecon1bd_3 wne wn fnecon1bd_2 fnecon1bd_3 wceq fnecon1bd_0 fnecon1bd_2 fnecon1bd_3 wne fnecon1bd_1 enecon1bd_0 con3d fnecon1bd_2 fnecon1bd_3 nne syl6ib $.
$}
$( Contrapositive law deduction for inequality.  (Contributed by NM,
       28-Dec-2008.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnecon1d_0 $f wff ph $.
	fnecon1d_1 $f class A $.
	fnecon1d_2 $f class B $.
	fnecon1d_3 $f class C $.
	fnecon1d_4 $f class D $.
	enecon1d_0 $e |- ( ph -> ( A =/= B -> C = D ) ) $.
	necon1d $p |- ( ph -> ( C =/= D -> A = B ) ) $= fnecon1d_0 fnecon1d_3 fnecon1d_4 wne fnecon1d_1 fnecon1d_2 fnecon1d_0 fnecon1d_1 fnecon1d_2 wne fnecon1d_3 fnecon1d_4 wceq fnecon1d_3 fnecon1d_4 wne wn enecon1d_0 fnecon1d_3 fnecon1d_4 nne syl6ibr necon4ad $.
$}
$( If it is not the case that two classes are equal, they are unequal.
       Converse of ~ neneqd .  One-way deduction form of ~ df-ne .
       (Contributed by David Moews, 28-Feb-2017.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fneneqad_0 $f wff ph $.
	fneneqad_1 $f class A $.
	fneneqad_2 $f class B $.
	eneneqad_0 $e |- ( ph -> -. A = B ) $.
	neneqad $p |- ( ph -> A =/= B ) $= fneneqad_0 fneneqad_1 fneneqad_2 fneneqad_0 fneneqad_1 fneneqad_2 wceq eneneqad_0 con2i necon2ai $.
$}
$( Contraposition law for inequality.  (Contributed by NM, 28-Dec-2008.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fnebi_0 $f class A $.
	fnebi_1 $f class B $.
	fnebi_2 $f class C $.
	fnebi_3 $f class D $.
	nebi $p |- ( ( A = B <-> C = D ) <-> ( A =/= B <-> C =/= D ) ) $= fnebi_0 fnebi_1 wceq fnebi_2 fnebi_3 wceq wb fnebi_0 fnebi_1 wne fnebi_2 fnebi_3 wne wb fnebi_0 fnebi_1 wceq fnebi_2 fnebi_3 wceq wb fnebi_0 fnebi_1 fnebi_2 fnebi_3 fnebi_0 fnebi_1 wceq fnebi_2 fnebi_3 wceq wb id necon3bid fnebi_0 fnebi_1 wne fnebi_2 fnebi_3 wne wb fnebi_0 fnebi_1 fnebi_2 fnebi_3 fnebi_0 fnebi_1 wne fnebi_2 fnebi_3 wne wb id necon4bid impbii $.
$}
$( Theorem *13.18 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpm13.18_0 $f class A $.
	fpm13.18_1 $f class B $.
	fpm13.18_2 $f class C $.
	pm13.18 $p |- ( ( A = B /\ A =/= C ) -> B =/= C ) $= fpm13.18_0 fpm13.18_1 wceq fpm13.18_0 fpm13.18_2 wne fpm13.18_1 fpm13.18_2 wne fpm13.18_0 fpm13.18_1 wceq fpm13.18_1 fpm13.18_2 fpm13.18_0 fpm13.18_2 fpm13.18_0 fpm13.18_1 wceq fpm13.18_0 fpm13.18_2 wceq fpm13.18_1 fpm13.18_2 wceq fpm13.18_0 fpm13.18_1 fpm13.18_2 eqeq1 biimprd necon3d imp $.
$}
$( Theorem *13.181 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fpm13.181_0 $f class A $.
	fpm13.181_1 $f class B $.
	fpm13.181_2 $f class C $.
	pm13.181 $p |- ( ( A = B /\ B =/= C ) -> A =/= C ) $= fpm13.181_0 fpm13.181_1 wceq fpm13.181_1 fpm13.181_0 wceq fpm13.181_1 fpm13.181_2 wne fpm13.181_0 fpm13.181_2 wne fpm13.181_0 fpm13.181_1 eqcom fpm13.181_1 fpm13.181_0 fpm13.181_2 pm13.18 sylanb $.
$}
$( A contradiction implies anything.  Equality/inequality deduction form.
       (Contributed by David Moews, 28-Feb-2017.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fpm2.21ddne_0 $f wff ph $.
	fpm2.21ddne_1 $f wff ps $.
	fpm2.21ddne_2 $f class A $.
	fpm2.21ddne_3 $f class B $.
	epm2.21ddne_0 $e |- ( ph -> A = B ) $.
	epm2.21ddne_1 $e |- ( ph -> A =/= B ) $.
	pm2.21ddne $p |- ( ph -> ps ) $= fpm2.21ddne_0 fpm2.21ddne_2 fpm2.21ddne_3 wceq fpm2.21ddne_1 epm2.21ddne_0 fpm2.21ddne_0 fpm2.21ddne_2 fpm2.21ddne_3 epm2.21ddne_1 neneqd pm2.21dd $.
$}
$( Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v A $.
	$v B $.
	fpm2.61ne_0 $f wff ph $.
	fpm2.61ne_1 $f wff ps $.
	fpm2.61ne_2 $f wff ch $.
	fpm2.61ne_3 $f class A $.
	fpm2.61ne_4 $f class B $.
	epm2.61ne_0 $e |- ( A = B -> ( ps <-> ch ) ) $.
	epm2.61ne_1 $e |- ( ( ph /\ A =/= B ) -> ps ) $.
	epm2.61ne_2 $e |- ( ph -> ch ) $.
	pm2.61ne $p |- ( ph -> ps ) $= fpm2.61ne_3 fpm2.61ne_4 wne fpm2.61ne_0 fpm2.61ne_1 wi fpm2.61ne_0 fpm2.61ne_3 fpm2.61ne_4 wne fpm2.61ne_1 epm2.61ne_1 expcom fpm2.61ne_3 fpm2.61ne_4 wne wn fpm2.61ne_3 fpm2.61ne_4 wceq fpm2.61ne_0 fpm2.61ne_1 wi fpm2.61ne_3 fpm2.61ne_4 nne fpm2.61ne_0 fpm2.61ne_1 fpm2.61ne_3 fpm2.61ne_4 wceq fpm2.61ne_2 epm2.61ne_2 epm2.61ne_0 syl5ibr sylbi pm2.61i $.
$}
$( Inference eliminating an inequality in an antecedent.  (Contributed by
       NM, 16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fpm2.61ine_0 $f wff ph $.
	fpm2.61ine_1 $f class A $.
	fpm2.61ine_2 $f class B $.
	epm2.61ine_0 $e |- ( A = B -> ph ) $.
	epm2.61ine_1 $e |- ( A =/= B -> ph ) $.
	pm2.61ine $p |- ph $= fpm2.61ine_1 fpm2.61ine_2 wne fpm2.61ine_0 epm2.61ine_1 fpm2.61ine_1 fpm2.61ine_2 wne wn fpm2.61ine_1 fpm2.61ine_2 wceq fpm2.61ine_0 fpm2.61ine_1 fpm2.61ine_2 nne epm2.61ine_0 sylbi pm2.61i $.
$}
$( Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fpm2.61dne_0 $f wff ph $.
	fpm2.61dne_1 $f wff ps $.
	fpm2.61dne_2 $f class A $.
	fpm2.61dne_3 $f class B $.
	epm2.61dne_0 $e |- ( ph -> ( A = B -> ps ) ) $.
	epm2.61dne_1 $e |- ( ph -> ( A =/= B -> ps ) ) $.
	pm2.61dne $p |- ( ph -> ps ) $= fpm2.61dne_0 fpm2.61dne_2 fpm2.61dne_3 wne fpm2.61dne_1 epm2.61dne_1 fpm2.61dne_2 fpm2.61dne_3 wne wn fpm2.61dne_2 fpm2.61dne_3 wceq fpm2.61dne_0 fpm2.61dne_1 fpm2.61dne_2 fpm2.61dne_3 nne epm2.61dne_0 syl5bi pm2.61d $.
$}
$( Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 30-Nov-2011.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	fpm2.61dane_0 $f wff ph $.
	fpm2.61dane_1 $f wff ps $.
	fpm2.61dane_2 $f class A $.
	fpm2.61dane_3 $f class B $.
	epm2.61dane_0 $e |- ( ( ph /\ A = B ) -> ps ) $.
	epm2.61dane_1 $e |- ( ( ph /\ A =/= B ) -> ps ) $.
	pm2.61dane $p |- ( ph -> ps ) $= fpm2.61dane_0 fpm2.61dane_1 fpm2.61dane_2 fpm2.61dane_3 fpm2.61dane_0 fpm2.61dane_2 fpm2.61dane_3 wceq fpm2.61dane_1 epm2.61dane_0 ex fpm2.61dane_0 fpm2.61dane_2 fpm2.61dane_3 wne fpm2.61dane_1 epm2.61dane_1 ex pm2.61dne $.
$}
$( Deduction eliminating two inequalities in an antecedent.  (Contributed
       by NM, 29-May-2013.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fpm2.61da2ne_0 $f wff ph $.
	fpm2.61da2ne_1 $f wff ps $.
	fpm2.61da2ne_2 $f class A $.
	fpm2.61da2ne_3 $f class B $.
	fpm2.61da2ne_4 $f class C $.
	fpm2.61da2ne_5 $f class D $.
	epm2.61da2ne_0 $e |- ( ( ph /\ A = B ) -> ps ) $.
	epm2.61da2ne_1 $e |- ( ( ph /\ C = D ) -> ps ) $.
	epm2.61da2ne_2 $e |- ( ( ph /\ ( A =/= B /\ C =/= D ) ) -> ps ) $.
	pm2.61da2ne $p |- ( ph -> ps ) $= fpm2.61da2ne_0 fpm2.61da2ne_1 fpm2.61da2ne_2 fpm2.61da2ne_3 epm2.61da2ne_0 fpm2.61da2ne_0 fpm2.61da2ne_2 fpm2.61da2ne_3 wne wa fpm2.61da2ne_1 fpm2.61da2ne_4 fpm2.61da2ne_5 fpm2.61da2ne_0 fpm2.61da2ne_4 fpm2.61da2ne_5 wceq fpm2.61da2ne_1 fpm2.61da2ne_2 fpm2.61da2ne_3 wne epm2.61da2ne_1 adantlr fpm2.61da2ne_0 fpm2.61da2ne_2 fpm2.61da2ne_3 wne fpm2.61da2ne_4 fpm2.61da2ne_5 wne fpm2.61da2ne_1 epm2.61da2ne_2 anassrs pm2.61dane pm2.61dane $.
$}
$( Deduction eliminating three inequalities in an antecedent.  (Contributed
       by NM, 15-Jun-2013.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v E $.
	$v F $.
	fpm2.61da3ne_0 $f wff ph $.
	fpm2.61da3ne_1 $f wff ps $.
	fpm2.61da3ne_2 $f class A $.
	fpm2.61da3ne_3 $f class B $.
	fpm2.61da3ne_4 $f class C $.
	fpm2.61da3ne_5 $f class D $.
	fpm2.61da3ne_6 $f class E $.
	fpm2.61da3ne_7 $f class F $.
	epm2.61da3ne_0 $e |- ( ( ph /\ A = B ) -> ps ) $.
	epm2.61da3ne_1 $e |- ( ( ph /\ C = D ) -> ps ) $.
	epm2.61da3ne_2 $e |- ( ( ph /\ E = F ) -> ps ) $.
	epm2.61da3ne_3 $e |- ( ( ph /\ ( A =/= B /\ C =/= D /\ E =/= F ) ) -> ps ) $.
	pm2.61da3ne $p |- ( ph -> ps ) $= fpm2.61da3ne_0 fpm2.61da3ne_1 fpm2.61da3ne_2 fpm2.61da3ne_3 fpm2.61da3ne_4 fpm2.61da3ne_5 epm2.61da3ne_0 epm2.61da3ne_1 fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne wa wa fpm2.61da3ne_1 fpm2.61da3ne_6 fpm2.61da3ne_7 fpm2.61da3ne_0 fpm2.61da3ne_6 fpm2.61da3ne_7 wceq fpm2.61da3ne_1 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne wa epm2.61da3ne_2 adantlr fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne wa wa fpm2.61da3ne_6 fpm2.61da3ne_7 wne wa fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne fpm2.61da3ne_6 fpm2.61da3ne_7 wne fpm2.61da3ne_1 fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne wa fpm2.61da3ne_6 fpm2.61da3ne_7 wne simpll fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne fpm2.61da3ne_6 fpm2.61da3ne_7 wne simplrl fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne fpm2.61da3ne_6 fpm2.61da3ne_7 wne simplrr fpm2.61da3ne_0 fpm2.61da3ne_2 fpm2.61da3ne_3 wne fpm2.61da3ne_4 fpm2.61da3ne_5 wne wa wa fpm2.61da3ne_6 fpm2.61da3ne_7 wne simpr epm2.61da3ne_3 syl13anc pm2.61dane pm2.61da2ne $.
$}
$( Commutation of inequality.  (Contributed by NM, 14-May-1999.) $)
${
	$v A $.
	$v B $.
	fnecom_0 $f class A $.
	fnecom_1 $f class B $.
	necom $p |- ( A =/= B <-> B =/= A ) $= fnecom_0 fnecom_1 fnecom_1 fnecom_0 fnecom_0 fnecom_1 eqcom necon3bii $.
$}
$( Inference from commutative law for inequality.  (Contributed by NM,
       17-Oct-2012.) $)
${
	$v A $.
	$v B $.
	fnecomi_0 $f class A $.
	fnecomi_1 $f class B $.
	enecomi_0 $e |- A =/= B $.
	necomi $p |- B =/= A $= fnecomi_0 fnecomi_1 wne fnecomi_1 fnecomi_0 wne enecomi_0 fnecomi_0 fnecomi_1 necom mpbi $.
$}
$( Deduction from commutative law for inequality.  (Contributed by NM,
       12-Feb-2008.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnecomd_0 $f wff ph $.
	fnecomd_1 $f class A $.
	fnecomd_2 $f class B $.
	enecomd_0 $e |- ( ph -> A =/= B ) $.
	necomd $p |- ( ph -> B =/= A ) $= fnecomd_0 fnecomd_1 fnecomd_2 wne fnecomd_2 fnecomd_1 wne enecomd_0 fnecomd_1 fnecomd_2 necom sylib $.
$}
$( Logical OR with an equality.  (Contributed by NM, 29-Apr-2007.) $)
${
	$v ps $.
	$v A $.
	$v B $.
	fneor_0 $f wff ps $.
	fneor_1 $f class A $.
	fneor_2 $f class B $.
	neor $p |- ( ( A = B \/ ps ) <-> ( A =/= B -> ps ) ) $= fneor_1 fneor_2 wceq fneor_0 wo fneor_1 fneor_2 wceq wn fneor_0 wi fneor_1 fneor_2 wne fneor_0 wi fneor_1 fneor_2 wceq fneor_0 df-or fneor_1 fneor_2 wne fneor_1 fneor_2 wceq wn fneor_0 fneor_1 fneor_2 df-ne imbi1i bitr4i $.
$}
$( A De Morgan's law for inequality.  (Contributed by NM, 18-May-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fneanior_0 $f class A $.
	fneanior_1 $f class B $.
	fneanior_2 $f class C $.
	fneanior_3 $f class D $.
	neanior $p |- ( ( A =/= B /\ C =/= D ) <-> -. ( A = B \/ C = D ) ) $= fneanior_0 fneanior_1 wne fneanior_2 fneanior_3 wne wa fneanior_0 fneanior_1 wceq wn fneanior_2 fneanior_3 wceq wn wa fneanior_0 fneanior_1 wceq fneanior_2 fneanior_3 wceq wo wn fneanior_0 fneanior_1 wne fneanior_0 fneanior_1 wceq wn fneanior_2 fneanior_3 wne fneanior_2 fneanior_3 wceq wn fneanior_0 fneanior_1 df-ne fneanior_2 fneanior_3 df-ne anbi12i fneanior_0 fneanior_1 wceq fneanior_2 fneanior_3 wceq pm4.56 bitri $.
$}
$( A De Morgan's law for inequality.  (Contributed by NM, 30-Sep-2013.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v E $.
	$v F $.
	fne3anior_0 $f class A $.
	fne3anior_1 $f class B $.
	fne3anior_2 $f class C $.
	fne3anior_3 $f class D $.
	fne3anior_4 $f class E $.
	fne3anior_5 $f class F $.
	ne3anior $p |- ( ( A =/= B /\ C =/= D /\ E =/= F ) <-> -. ( A = B \/ C = D \/ E = F ) ) $= fne3anior_0 fne3anior_1 wne fne3anior_2 fne3anior_3 wne fne3anior_4 fne3anior_5 wne w3a fne3anior_0 fne3anior_1 wne wn fne3anior_2 fne3anior_3 wne wn fne3anior_4 fne3anior_5 wne wn w3o fne3anior_0 fne3anior_1 wceq fne3anior_2 fne3anior_3 wceq fne3anior_4 fne3anior_5 wceq w3o fne3anior_0 fne3anior_1 wne fne3anior_2 fne3anior_3 wne fne3anior_4 fne3anior_5 wne 3anor fne3anior_0 fne3anior_1 wne wn fne3anior_0 fne3anior_1 wceq fne3anior_2 fne3anior_3 wne wn fne3anior_2 fne3anior_3 wceq fne3anior_4 fne3anior_5 wne wn fne3anior_4 fne3anior_5 wceq fne3anior_0 fne3anior_1 nne fne3anior_2 fne3anior_3 nne fne3anior_4 fne3anior_5 nne 3orbi123i xchbinx $.
$}
$( A De Morgan's law for inequality.  (Contributed by NM, 18-May-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fneorian_0 $f class A $.
	fneorian_1 $f class B $.
	fneorian_2 $f class C $.
	fneorian_3 $f class D $.
	neorian $p |- ( ( A =/= B \/ C =/= D ) <-> -. ( A = B /\ C = D ) ) $= fneorian_0 fneorian_1 wne fneorian_2 fneorian_3 wne wo fneorian_0 fneorian_1 wceq wn fneorian_2 fneorian_3 wceq wn wo fneorian_0 fneorian_1 wceq fneorian_2 fneorian_3 wceq wa wn fneorian_0 fneorian_1 wne fneorian_0 fneorian_1 wceq wn fneorian_2 fneorian_3 wne fneorian_2 fneorian_3 wceq wn fneorian_0 fneorian_1 df-ne fneorian_2 fneorian_3 df-ne orbi12i fneorian_0 fneorian_1 wceq fneorian_2 fneorian_3 wceq ianor bitr4i $.
$}
$( An inference from an inequality, related to modus tollens.  (Contributed
       by NM, 13-Apr-2007.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	fnemtbir_0 $f wff ph $.
	fnemtbir_1 $f class A $.
	fnemtbir_2 $f class B $.
	enemtbir_0 $e |- A =/= B $.
	enemtbir_1 $e |- ( ph <-> A = B ) $.
	nemtbir $p |- -. ph $= fnemtbir_0 fnemtbir_1 fnemtbir_2 wceq fnemtbir_1 fnemtbir_2 wne fnemtbir_1 fnemtbir_2 wceq wn enemtbir_0 fnemtbir_1 fnemtbir_2 df-ne mpbi enemtbir_1 mtbir $.
$}
$( Two classes are different if they don't contain the same element.
     (Contributed by NM, 3-Feb-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fnelne1_0 $f class A $.
	fnelne1_1 $f class B $.
	fnelne1_2 $f class C $.
	nelne1 $p |- ( ( A e. B /\ -. A e. C ) -> B =/= C ) $= fnelne1_0 fnelne1_1 wcel fnelne1_0 fnelne1_2 wcel wn fnelne1_1 fnelne1_2 wne fnelne1_0 fnelne1_1 wcel fnelne1_0 fnelne1_2 wcel fnelne1_1 fnelne1_2 fnelne1_1 fnelne1_2 wceq fnelne1_0 fnelne1_1 wcel fnelne1_0 fnelne1_2 wcel fnelne1_1 fnelne1_2 fnelne1_0 eleq2 biimpcd necon3bd imp $.
$}
$( Two classes are different if they don't belong to the same class.
     (Contributed by NM, 25-Jun-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fnelne2_0 $f class A $.
	fnelne2_1 $f class B $.
	fnelne2_2 $f class C $.
	nelne2 $p |- ( ( A e. C /\ -. B e. C ) -> A =/= B ) $= fnelne2_0 fnelne2_2 wcel fnelne2_1 fnelne2_2 wcel wn fnelne2_0 fnelne2_1 wne fnelne2_0 fnelne2_2 wcel fnelne2_1 fnelne2_2 wcel fnelne2_0 fnelne2_1 fnelne2_0 fnelne2_1 wceq fnelne2_0 fnelne2_2 wcel fnelne2_1 fnelne2_2 wcel fnelne2_0 fnelne2_1 fnelne2_2 eleq1 biimpcd necon3bd imp $.
$}
$( Equality theorem for negated membership.  (Contributed by NM,
     20-Nov-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneleq1_0 $f class A $.
	fneleq1_1 $f class B $.
	fneleq1_2 $f class C $.
	neleq1 $p |- ( A = B -> ( A e/ C <-> B e/ C ) ) $= fneleq1_0 fneleq1_1 wceq fneleq1_0 fneleq1_2 wcel wn fneleq1_1 fneleq1_2 wcel wn fneleq1_0 fneleq1_2 wnel fneleq1_1 fneleq1_2 wnel fneleq1_0 fneleq1_1 wceq fneleq1_0 fneleq1_2 wcel fneleq1_1 fneleq1_2 wcel fneleq1_0 fneleq1_1 fneleq1_2 eleq1 notbid fneleq1_0 fneleq1_2 df-nel fneleq1_1 fneleq1_2 df-nel 3bitr4g $.
$}
$( Equality theorem for negated membership.  (Contributed by NM,
     20-Nov-1994.) $)
${
	$v A $.
	$v B $.
	$v C $.
	fneleq2_0 $f class A $.
	fneleq2_1 $f class B $.
	fneleq2_2 $f class C $.
	neleq2 $p |- ( A = B -> ( C e/ A <-> C e/ B ) ) $= fneleq2_0 fneleq2_1 wceq fneleq2_2 fneleq2_0 wcel wn fneleq2_2 fneleq2_1 wcel wn fneleq2_2 fneleq2_0 wnel fneleq2_2 fneleq2_1 wnel fneleq2_0 fneleq2_1 wceq fneleq2_2 fneleq2_0 wcel fneleq2_2 fneleq2_1 wcel fneleq2_0 fneleq2_1 fneleq2_2 eleq2 notbid fneleq2_2 fneleq2_0 df-nel fneleq2_2 fneleq2_1 df-nel 3bitr4g $.
$}
$( Bound-variable hypothesis builder for inequality.  (Contributed by NM,
       10-Nov-2007.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fnfne_0 $f set x $.
	fnfne_1 $f class A $.
	fnfne_2 $f class B $.
	enfne_0 $e |- F/_ x A $.
	enfne_1 $e |- F/_ x B $.
	nfne $p |- F/ x A =/= B $= fnfne_1 fnfne_2 wne fnfne_1 fnfne_2 wceq wn fnfne_0 fnfne_1 fnfne_2 df-ne fnfne_1 fnfne_2 wceq fnfne_0 fnfne_0 fnfne_1 fnfne_2 enfne_0 enfne_1 nfeq nfn nfxfr $.
$}
$( Bound-variable hypothesis builder for inequality.  (Contributed by David
       Abernethy, 26-Jun-2011.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	fnfnel_0 $f set x $.
	fnfnel_1 $f class A $.
	fnfnel_2 $f class B $.
	enfnel_0 $e |- F/_ x A $.
	enfnel_1 $e |- F/_ x B $.
	nfnel $p |- F/ x A e/ B $= fnfnel_1 fnfnel_2 wnel fnfnel_1 fnfnel_2 wcel wn fnfnel_0 fnfnel_1 fnfnel_2 df-nel fnfnel_1 fnfnel_2 wcel fnfnel_0 fnfnel_0 fnfnel_1 fnfnel_2 enfnel_0 enfnel_1 nfel nfn nfxfr $.
$}
$( Bound-variable hypothesis builder for inequality.  (Contributed by NM,
       10-Nov-2007.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	fnfned_0 $f wff ph $.
	fnfned_1 $f set x $.
	fnfned_2 $f class A $.
	fnfned_3 $f class B $.
	enfned_0 $e |- ( ph -> F/_ x A ) $.
	enfned_1 $e |- ( ph -> F/_ x B ) $.
	nfned $p |- ( ph -> F/ x A =/= B ) $= fnfned_2 fnfned_3 wne fnfned_2 fnfned_3 wceq wn fnfned_0 fnfned_1 fnfned_2 fnfned_3 df-ne fnfned_0 fnfned_2 fnfned_3 wceq fnfned_1 fnfned_0 fnfned_1 fnfned_2 fnfned_3 enfned_0 enfned_1 nfeqd nfnd nfxfrd $.
$}
$( Bound-variable hypothesis builder for inequality.  (Contributed by David
       Abernethy, 26-Jun-2011.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	fnfneld_0 $f wff ph $.
	fnfneld_1 $f set x $.
	fnfneld_2 $f class A $.
	fnfneld_3 $f class B $.
	enfneld_0 $e |- ( ph -> F/_ x A ) $.
	enfneld_1 $e |- ( ph -> F/_ x B ) $.
	nfneld $p |- ( ph -> F/ x A e/ B ) $= fnfneld_2 fnfneld_3 wnel fnfneld_2 fnfneld_3 wcel wn fnfneld_0 fnfneld_1 fnfneld_2 fnfneld_3 df-nel fnfneld_0 fnfneld_2 fnfneld_3 wcel fnfneld_1 fnfneld_0 fnfneld_1 fnfneld_2 fnfneld_3 enfneld_0 enfneld_1 nfeld nfnd nfxfrd $.
$}

