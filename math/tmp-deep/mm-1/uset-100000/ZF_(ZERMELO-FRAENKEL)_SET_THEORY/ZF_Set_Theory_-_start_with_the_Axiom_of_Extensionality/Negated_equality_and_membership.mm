$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Class_form_not-free_predicate.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Negated equality and membership

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new connectives. $)

$c =/= $.

$(Not equal to (equal sign with slash through it). $)

$c e/ $.

$(Not an element of (epsilon with slash through it). $)

$(Extend wff notation to include inequality. $)

${
	$v A B  $.
	f0_wne $f class A $.
	f1_wne $f class B $.
	a_wne $a wff A =/= B $.
$}

$(Extend wff notation to include negated membership. $)

${
	$v A B  $.
	f0_wnel $f class A $.
	f1_wnel $f class B $.
	a_wnel $a wff A e/ B $.
$}

$(Define inequality.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	f0_df-ne $f class A $.
	f1_df-ne $f class B $.
	a_df-ne $a |- ( A =/= B <-> -. A = B ) $.
$}

$(Define negated membership.  (Contributed by NM, 7-Aug-1994.) $)

${
	$v A B  $.
	f0_df-nel $f class A $.
	f1_df-nel $f class B $.
	a_df-nel $a |- ( A e/ B <-> -. A e. B ) $.
$}

$(Negation of inequality.  (Contributed by NM, 9-Jun-2006.) $)

${
	$v A B  $.
	f0_nne $f class A $.
	f1_nne $f class B $.
	p_nne $p |- ( -. A =/= B <-> A = B ) $= f0_nne f1_nne a_df-ne f0_nne f1_nne a_wne f0_nne f1_nne a_wceq p_con2bii f0_nne f1_nne a_wceq f0_nne f1_nne a_wne a_wn p_bicomi $.
$}

$(No class is unequal to itself.  (Contributed by Stefan O'Rear,
     1-Jan-2015.) $)

${
	$v A  $.
	f0_neirr $f class A $.
	p_neirr $p |- -. A =/= A $= f0_neirr p_eqid f0_neirr f0_neirr p_nne f0_neirr f0_neirr a_wne a_wn f0_neirr f0_neirr a_wceq p_mpbir $.
$}

$(Excluded middle with equality and inequality.  (Contributed by NM,
     3-Feb-2012.) $)

${
	$v A B  $.
	f0_exmidne $f class A $.
	f1_exmidne $f class B $.
	p_exmidne $p |- ( A = B \/ A =/= B ) $= f0_exmidne f1_exmidne a_wceq p_exmid f0_exmidne f1_exmidne a_df-ne f0_exmidne f1_exmidne a_wne f0_exmidne f1_exmidne a_wceq a_wn f0_exmidne f1_exmidne a_wceq p_orbi2i f0_exmidne f1_exmidne a_wceq f0_exmidne f1_exmidne a_wne a_wo f0_exmidne f1_exmidne a_wceq f0_exmidne f1_exmidne a_wceq a_wn a_wo p_mpbir $.
$}

$(Law of noncontradiction with equality and inequality.  (Contributed by NM,
     3-Feb-2012.) $)

${
	$v A B  $.
	f0_nonconne $f class A $.
	f1_nonconne $f class B $.
	p_nonconne $p |- -. ( A = B /\ A =/= B ) $= f0_nonconne f1_nonconne a_wceq p_pm3.24 f0_nonconne f1_nonconne a_df-ne f0_nonconne f1_nonconne a_wne f0_nonconne f1_nonconne a_wceq a_wn f0_nonconne f1_nonconne a_wceq p_anbi2i f0_nonconne f1_nonconne a_wceq f0_nonconne f1_nonconne a_wne a_wa f0_nonconne f1_nonconne a_wceq f0_nonconne f1_nonconne a_wceq a_wn a_wa p_mtbir $.
$}

$(Equality theorem for inequality.  (Contributed by NM, 19-Nov-1994.) $)

${
	$v A B C  $.
	f0_neeq1 $f class A $.
	f1_neeq1 $f class B $.
	f2_neeq1 $f class C $.
	p_neeq1 $p |- ( A = B -> ( A =/= C <-> B =/= C ) ) $= f0_neeq1 f1_neeq1 f2_neeq1 p_eqeq1 f0_neeq1 f1_neeq1 a_wceq f0_neeq1 f2_neeq1 a_wceq f1_neeq1 f2_neeq1 a_wceq p_notbid f0_neeq1 f2_neeq1 a_df-ne f1_neeq1 f2_neeq1 a_df-ne f0_neeq1 f1_neeq1 a_wceq f0_neeq1 f2_neeq1 a_wceq a_wn f1_neeq1 f2_neeq1 a_wceq a_wn f0_neeq1 f2_neeq1 a_wne f1_neeq1 f2_neeq1 a_wne p_3bitr4g $.
$}

$(Equality theorem for inequality.  (Contributed by NM, 19-Nov-1994.) $)

${
	$v A B C  $.
	f0_neeq2 $f class A $.
	f1_neeq2 $f class B $.
	f2_neeq2 $f class C $.
	p_neeq2 $p |- ( A = B -> ( C =/= A <-> C =/= B ) ) $= f0_neeq2 f1_neeq2 f2_neeq2 p_eqeq2 f0_neeq2 f1_neeq2 a_wceq f2_neeq2 f0_neeq2 a_wceq f2_neeq2 f1_neeq2 a_wceq p_notbid f2_neeq2 f0_neeq2 a_df-ne f2_neeq2 f1_neeq2 a_df-ne f0_neeq2 f1_neeq2 a_wceq f2_neeq2 f0_neeq2 a_wceq a_wn f2_neeq2 f1_neeq2 a_wceq a_wn f2_neeq2 f0_neeq2 a_wne f2_neeq2 f1_neeq2 a_wne p_3bitr4g $.
$}

$(Inference for inequality.  (Contributed by NM, 29-Apr-2005.) $)

${
	$v A B C  $.
	f0_neeq1i $f class A $.
	f1_neeq1i $f class B $.
	f2_neeq1i $f class C $.
	e0_neeq1i $e |- A = B $.
	p_neeq1i $p |- ( A =/= C <-> B =/= C ) $= e0_neeq1i f0_neeq1i f1_neeq1i f2_neeq1i p_neeq1 f0_neeq1i f1_neeq1i a_wceq f0_neeq1i f2_neeq1i a_wne f1_neeq1i f2_neeq1i a_wne a_wb a_ax-mp $.
$}

$(Inference for inequality.  (Contributed by NM, 29-Apr-2005.) $)

${
	$v A B C  $.
	f0_neeq2i $f class A $.
	f1_neeq2i $f class B $.
	f2_neeq2i $f class C $.
	e0_neeq2i $e |- A = B $.
	p_neeq2i $p |- ( C =/= A <-> C =/= B ) $= e0_neeq2i f0_neeq2i f1_neeq2i f2_neeq2i p_neeq2 f0_neeq2i f1_neeq2i a_wceq f2_neeq2i f0_neeq2i a_wne f2_neeq2i f1_neeq2i a_wne a_wb a_ax-mp $.
$}

$(Inference for inequality.  (Contributed by NM, 24-Jul-2012.) $)

${
	$v A B C D  $.
	f0_neeq12i $f class A $.
	f1_neeq12i $f class B $.
	f2_neeq12i $f class C $.
	f3_neeq12i $f class D $.
	e0_neeq12i $e |- A = B $.
	e1_neeq12i $e |- C = D $.
	p_neeq12i $p |- ( A =/= C <-> B =/= D ) $= e1_neeq12i f2_neeq12i f3_neeq12i f0_neeq12i p_neeq2i e0_neeq12i f0_neeq12i f1_neeq12i f3_neeq12i p_neeq1i f0_neeq12i f2_neeq12i a_wne f0_neeq12i f3_neeq12i a_wne f1_neeq12i f3_neeq12i a_wne p_bitri $.
$}

$(Deduction for inequality.  (Contributed by NM, 25-Oct-1999.) $)

${
	$v ph A B C  $.
	f0_neeq1d $f wff ph $.
	f1_neeq1d $f class A $.
	f2_neeq1d $f class B $.
	f3_neeq1d $f class C $.
	e0_neeq1d $e |- ( ph -> A = B ) $.
	p_neeq1d $p |- ( ph -> ( A =/= C <-> B =/= C ) ) $= e0_neeq1d f1_neeq1d f2_neeq1d f3_neeq1d p_neeq1 f0_neeq1d f1_neeq1d f2_neeq1d a_wceq f1_neeq1d f3_neeq1d a_wne f2_neeq1d f3_neeq1d a_wne a_wb p_syl $.
$}

$(Deduction for inequality.  (Contributed by NM, 25-Oct-1999.) $)

${
	$v ph A B C  $.
	f0_neeq2d $f wff ph $.
	f1_neeq2d $f class A $.
	f2_neeq2d $f class B $.
	f3_neeq2d $f class C $.
	e0_neeq2d $e |- ( ph -> A = B ) $.
	p_neeq2d $p |- ( ph -> ( C =/= A <-> C =/= B ) ) $= e0_neeq2d f1_neeq2d f2_neeq2d f3_neeq2d p_neeq2 f0_neeq2d f1_neeq2d f2_neeq2d a_wceq f3_neeq2d f1_neeq2d a_wne f3_neeq2d f2_neeq2d a_wne a_wb p_syl $.
$}

$(Deduction for inequality.  (Contributed by NM, 24-Jul-2012.) $)

${
	$v ph A B C D  $.
	f0_neeq12d $f wff ph $.
	f1_neeq12d $f class A $.
	f2_neeq12d $f class B $.
	f3_neeq12d $f class C $.
	f4_neeq12d $f class D $.
	e0_neeq12d $e |- ( ph -> A = B ) $.
	e1_neeq12d $e |- ( ph -> C = D ) $.
	p_neeq12d $p |- ( ph -> ( A =/= C <-> B =/= D ) ) $= e0_neeq12d f0_neeq12d f1_neeq12d f2_neeq12d f3_neeq12d p_neeq1d e1_neeq12d f0_neeq12d f3_neeq12d f4_neeq12d f2_neeq12d p_neeq2d f0_neeq12d f1_neeq12d f3_neeq12d a_wne f2_neeq12d f3_neeq12d a_wne f2_neeq12d f4_neeq12d a_wne p_bitrd $.
$}

$(Deduction eliminating inequality definition.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)

${
	$v ph A B  $.
	f0_neneqd $f wff ph $.
	f1_neneqd $f class A $.
	f2_neneqd $f class B $.
	e0_neneqd $e |- ( ph -> A =/= B ) $.
	p_neneqd $p |- ( ph -> -. A = B ) $= e0_neneqd f1_neneqd f2_neneqd a_df-ne f0_neneqd f1_neneqd f2_neneqd a_wne f1_neneqd f2_neneqd a_wceq a_wn p_sylib $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v A B C  $.
	f0_eqnetri $f class A $.
	f1_eqnetri $f class B $.
	f2_eqnetri $f class C $.
	e0_eqnetri $e |- A = B $.
	e1_eqnetri $e |- B =/= C $.
	p_eqnetri $p |- A =/= C $= e1_eqnetri e0_eqnetri f0_eqnetri f1_eqnetri f2_eqnetri p_neeq1i f0_eqnetri f2_eqnetri a_wne f1_eqnetri f2_eqnetri a_wne p_mpbir $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v ph A B C  $.
	f0_eqnetrd $f wff ph $.
	f1_eqnetrd $f class A $.
	f2_eqnetrd $f class B $.
	f3_eqnetrd $f class C $.
	e0_eqnetrd $e |- ( ph -> A = B ) $.
	e1_eqnetrd $e |- ( ph -> B =/= C ) $.
	p_eqnetrd $p |- ( ph -> A =/= C ) $= e1_eqnetrd e0_eqnetrd f0_eqnetrd f1_eqnetrd f2_eqnetrd f3_eqnetrd p_neeq1d f0_eqnetrd f1_eqnetrd f3_eqnetrd a_wne f2_eqnetrd f3_eqnetrd a_wne p_mpbird $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v A B C  $.
	f0_eqnetrri $f class A $.
	f1_eqnetrri $f class B $.
	f2_eqnetrri $f class C $.
	e0_eqnetrri $e |- A = B $.
	e1_eqnetrri $e |- A =/= C $.
	p_eqnetrri $p |- B =/= C $= e0_eqnetrri f0_eqnetrri f1_eqnetrri p_eqcomi e1_eqnetrri f1_eqnetrri f0_eqnetrri f2_eqnetrri p_eqnetri $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v ph A B C  $.
	f0_eqnetrrd $f wff ph $.
	f1_eqnetrrd $f class A $.
	f2_eqnetrrd $f class B $.
	f3_eqnetrrd $f class C $.
	e0_eqnetrrd $e |- ( ph -> A = B ) $.
	e1_eqnetrrd $e |- ( ph -> A =/= C ) $.
	p_eqnetrrd $p |- ( ph -> B =/= C ) $= e0_eqnetrrd f0_eqnetrrd f1_eqnetrrd f2_eqnetrrd p_eqcomd e1_eqnetrrd f0_eqnetrrd f2_eqnetrrd f1_eqnetrrd f3_eqnetrrd p_eqnetrd $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v A B C  $.
	f0_neeqtri $f class A $.
	f1_neeqtri $f class B $.
	f2_neeqtri $f class C $.
	e0_neeqtri $e |- A =/= B $.
	e1_neeqtri $e |- B = C $.
	p_neeqtri $p |- A =/= C $= e0_neeqtri e1_neeqtri f1_neeqtri f2_neeqtri f0_neeqtri p_neeq2i f0_neeqtri f1_neeqtri a_wne f0_neeqtri f2_neeqtri a_wne p_mpbi $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v ph A B C  $.
	f0_neeqtrd $f wff ph $.
	f1_neeqtrd $f class A $.
	f2_neeqtrd $f class B $.
	f3_neeqtrd $f class C $.
	e0_neeqtrd $e |- ( ph -> A =/= B ) $.
	e1_neeqtrd $e |- ( ph -> B = C ) $.
	p_neeqtrd $p |- ( ph -> A =/= C ) $= e0_neeqtrd e1_neeqtrd f0_neeqtrd f2_neeqtrd f3_neeqtrd f1_neeqtrd p_neeq2d f0_neeqtrd f1_neeqtrd f2_neeqtrd a_wne f1_neeqtrd f3_neeqtrd a_wne p_mpbid $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v A B C  $.
	f0_neeqtrri $f class A $.
	f1_neeqtrri $f class B $.
	f2_neeqtrri $f class C $.
	e0_neeqtrri $e |- A =/= B $.
	e1_neeqtrri $e |- C = B $.
	p_neeqtrri $p |- A =/= C $= e0_neeqtrri e1_neeqtrri f2_neeqtrri f1_neeqtrri p_eqcomi f0_neeqtrri f1_neeqtrri f2_neeqtrri p_neeqtri $.
$}

$(Substitution of equal classes into an inequality.  (Contributed by NM,
       4-Jul-2012.) $)

${
	$v ph A B C  $.
	f0_neeqtrrd $f wff ph $.
	f1_neeqtrrd $f class A $.
	f2_neeqtrrd $f class B $.
	f3_neeqtrrd $f class C $.
	e0_neeqtrrd $e |- ( ph -> A =/= B ) $.
	e1_neeqtrrd $e |- ( ph -> C = B ) $.
	p_neeqtrrd $p |- ( ph -> A =/= C ) $= e0_neeqtrrd e1_neeqtrrd f0_neeqtrrd f3_neeqtrrd f2_neeqtrrd p_eqcomd f0_neeqtrrd f1_neeqtrrd f2_neeqtrrd f3_neeqtrrd p_neeqtrd $.
$}

$(B chained equality inference for inequality.  (Contributed by NM,
       6-Jun-2012.) $)

${
	$v ph A B C  $.
	f0_syl5eqner $f wff ph $.
	f1_syl5eqner $f class A $.
	f2_syl5eqner $f class B $.
	f3_syl5eqner $f class C $.
	e0_syl5eqner $e |- B = A $.
	e1_syl5eqner $e |- ( ph -> B =/= C ) $.
	p_syl5eqner $p |- ( ph -> A =/= C ) $= e1_syl5eqner e0_syl5eqner f2_syl5eqner f1_syl5eqner f3_syl5eqner p_neeq1i f0_syl5eqner f2_syl5eqner f3_syl5eqner a_wne f1_syl5eqner f3_syl5eqner a_wne p_sylib $.
$}

$(Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)

${
	$v ph A B C D  $.
	f0_3netr3d $f wff ph $.
	f1_3netr3d $f class A $.
	f2_3netr3d $f class B $.
	f3_3netr3d $f class C $.
	f4_3netr3d $f class D $.
	e0_3netr3d $e |- ( ph -> A =/= B ) $.
	e1_3netr3d $e |- ( ph -> A = C ) $.
	e2_3netr3d $e |- ( ph -> B = D ) $.
	p_3netr3d $p |- ( ph -> C =/= D ) $= e0_3netr3d e1_3netr3d e2_3netr3d f0_3netr3d f1_3netr3d f3_3netr3d f2_3netr3d f4_3netr3d p_neeq12d f0_3netr3d f1_3netr3d f2_3netr3d a_wne f3_3netr3d f4_3netr3d a_wne p_mpbid $.
$}

$(Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)

${
	$v ph A B C D  $.
	f0_3netr4d $f wff ph $.
	f1_3netr4d $f class A $.
	f2_3netr4d $f class B $.
	f3_3netr4d $f class C $.
	f4_3netr4d $f class D $.
	e0_3netr4d $e |- ( ph -> A =/= B ) $.
	e1_3netr4d $e |- ( ph -> C = A ) $.
	e2_3netr4d $e |- ( ph -> D = B ) $.
	p_3netr4d $p |- ( ph -> C =/= D ) $= e0_3netr4d e1_3netr4d e2_3netr4d f0_3netr4d f3_3netr4d f1_3netr4d f4_3netr4d f2_3netr4d p_neeq12d f0_3netr4d f3_3netr4d f4_3netr4d a_wne f1_3netr4d f2_3netr4d a_wne p_mpbird $.
$}

$(Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 24-Jul-2012.) $)

${
	$v ph A B C D  $.
	f0_3netr3g $f wff ph $.
	f1_3netr3g $f class A $.
	f2_3netr3g $f class B $.
	f3_3netr3g $f class C $.
	f4_3netr3g $f class D $.
	e0_3netr3g $e |- ( ph -> A =/= B ) $.
	e1_3netr3g $e |- A = C $.
	e2_3netr3g $e |- B = D $.
	p_3netr3g $p |- ( ph -> C =/= D ) $= e0_3netr3g e1_3netr3g e2_3netr3g f1_3netr3g f3_3netr3g f2_3netr3g f4_3netr3g p_neeq12i f0_3netr3g f1_3netr3g f2_3netr3g a_wne f3_3netr3g f4_3netr3g a_wne p_sylib $.
$}

$(Substitution of equality into both sides of an inequality.  (Contributed
       by NM, 14-Jun-2012.) $)

${
	$v ph A B C D  $.
	f0_3netr4g $f wff ph $.
	f1_3netr4g $f class A $.
	f2_3netr4g $f class B $.
	f3_3netr4g $f class C $.
	f4_3netr4g $f class D $.
	e0_3netr4g $e |- ( ph -> A =/= B ) $.
	e1_3netr4g $e |- C = A $.
	e2_3netr4g $e |- D = B $.
	p_3netr4g $p |- ( ph -> C =/= D ) $= e0_3netr4g e1_3netr4g e2_3netr4g f3_3netr4g f1_3netr4g f4_3netr4g f2_3netr4g p_neeq12i f0_3netr4g f1_3netr4g f2_3netr4g a_wne f3_3netr4g f4_3netr4g a_wne p_sylibr $.
$}

$(Deduction from equality to inequality.  (Contributed by NM,
       9-Nov-2007.) $)

${
	$v ph A B  $.
	f0_necon3abii $f wff ph $.
	f1_necon3abii $f class A $.
	f2_necon3abii $f class B $.
	e0_necon3abii $e |- ( A = B <-> ph ) $.
	p_necon3abii $p |- ( A =/= B <-> -. ph ) $= f1_necon3abii f2_necon3abii a_df-ne e0_necon3abii f1_necon3abii f2_necon3abii a_wne f1_necon3abii f2_necon3abii a_wceq f0_necon3abii p_xchbinx $.
$}

$(Deduction from equality to inequality.  (Contributed by NM,
       13-Apr-2007.) $)

${
	$v ph A B  $.
	f0_necon3bbii $f wff ph $.
	f1_necon3bbii $f class A $.
	f2_necon3bbii $f class B $.
	e0_necon3bbii $e |- ( ph <-> A = B ) $.
	p_necon3bbii $p |- ( -. ph <-> A =/= B ) $= e0_necon3bbii f0_necon3bbii f1_necon3bbii f2_necon3bbii a_wceq p_bicomi f0_necon3bbii f1_necon3bbii f2_necon3bbii p_necon3abii f1_necon3bbii f2_necon3bbii a_wne f0_necon3bbii a_wn p_bicomi $.
$}

$(Inference from equality to inequality.  (Contributed by NM,
       23-Feb-2005.) $)

${
	$v A B C D  $.
	f0_necon3bii $f class A $.
	f1_necon3bii $f class B $.
	f2_necon3bii $f class C $.
	f3_necon3bii $f class D $.
	e0_necon3bii $e |- ( A = B <-> C = D ) $.
	p_necon3bii $p |- ( A =/= B <-> C =/= D ) $= e0_necon3bii f2_necon3bii f3_necon3bii a_wceq f0_necon3bii f1_necon3bii p_necon3abii f2_necon3bii f3_necon3bii a_df-ne f0_necon3bii f1_necon3bii a_wne f2_necon3bii f3_necon3bii a_wceq a_wn f2_necon3bii f3_necon3bii a_wne p_bitr4i $.
$}

$(Deduction from equality to inequality.  (Contributed by NM,
       21-Mar-2007.) $)

${
	$v ph ps A B  $.
	f0_necon3abid $f wff ph $.
	f1_necon3abid $f wff ps $.
	f2_necon3abid $f class A $.
	f3_necon3abid $f class B $.
	e0_necon3abid $e |- ( ph -> ( A = B <-> ps ) ) $.
	p_necon3abid $p |- ( ph -> ( A =/= B <-> -. ps ) ) $= f2_necon3abid f3_necon3abid a_df-ne e0_necon3abid f0_necon3abid f2_necon3abid f3_necon3abid a_wceq f1_necon3abid p_notbid f2_necon3abid f3_necon3abid a_wne f2_necon3abid f3_necon3abid a_wceq a_wn f0_necon3abid f1_necon3abid a_wn p_syl5bb $.
$}

$(Deduction from equality to inequality.  (Contributed by NM,
       2-Jun-2007.) $)

${
	$v ph ps A B  $.
	f0_necon3bbid $f wff ph $.
	f1_necon3bbid $f wff ps $.
	f2_necon3bbid $f class A $.
	f3_necon3bbid $f class B $.
	e0_necon3bbid $e |- ( ph -> ( ps <-> A = B ) ) $.
	p_necon3bbid $p |- ( ph -> ( -. ps <-> A =/= B ) ) $= e0_necon3bbid f0_necon3bbid f1_necon3bbid f2_necon3bbid f3_necon3bbid a_wceq p_bicomd f0_necon3bbid f1_necon3bbid f2_necon3bbid f3_necon3bbid p_necon3abid f0_necon3bbid f2_necon3bbid f3_necon3bbid a_wne f1_necon3bbid a_wn p_bicomd $.
$}

$(Deduction from equality to inequality.  (Contributed by NM,
       23-Feb-2005.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_necon3bid $f wff ph $.
	f1_necon3bid $f class A $.
	f2_necon3bid $f class B $.
	f3_necon3bid $f class C $.
	f4_necon3bid $f class D $.
	e0_necon3bid $e |- ( ph -> ( A = B <-> C = D ) ) $.
	p_necon3bid $p |- ( ph -> ( A =/= B <-> C =/= D ) ) $= f1_necon3bid f2_necon3bid a_df-ne e0_necon3bid f0_necon3bid f1_necon3bid f2_necon3bid a_wceq f3_necon3bid f4_necon3bid p_necon3bbid f1_necon3bid f2_necon3bid a_wne f1_necon3bid f2_necon3bid a_wceq a_wn f0_necon3bid f3_necon3bid f4_necon3bid a_wne p_syl5bb $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_necon3ad $f wff ph $.
	f1_necon3ad $f wff ps $.
	f2_necon3ad $f class A $.
	f3_necon3ad $f class B $.
	e0_necon3ad $e |- ( ph -> ( ps -> A = B ) ) $.
	p_necon3ad $p |- ( ph -> ( A =/= B -> -. ps ) ) $= e0_necon3ad f2_necon3ad f3_necon3ad p_nne f0_necon3ad f1_necon3ad f2_necon3ad f3_necon3ad a_wceq f2_necon3ad f3_necon3ad a_wne a_wn p_syl6ibr f0_necon3ad f1_necon3ad f2_necon3ad f3_necon3ad a_wne p_con2d $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_necon3bd $f wff ph $.
	f1_necon3bd $f wff ps $.
	f2_necon3bd $f class A $.
	f3_necon3bd $f class B $.
	e0_necon3bd $e |- ( ph -> ( A = B -> ps ) ) $.
	p_necon3bd $p |- ( ph -> ( -. ps -> A =/= B ) ) $= f2_necon3bd f3_necon3bd p_nne e0_necon3bd f2_necon3bd f3_necon3bd a_wne a_wn f2_necon3bd f3_necon3bd a_wceq f0_necon3bd f1_necon3bd p_syl5bi f0_necon3bd f2_necon3bd f3_necon3bd a_wne f1_necon3bd p_con1d $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       10-Jun-2006.) $)

${
	$v ph A B C D  $.
	f0_necon3d $f wff ph $.
	f1_necon3d $f class A $.
	f2_necon3d $f class B $.
	f3_necon3d $f class C $.
	f4_necon3d $f class D $.
	e0_necon3d $e |- ( ph -> ( A = B -> C = D ) ) $.
	p_necon3d $p |- ( ph -> ( C =/= D -> A =/= B ) ) $= e0_necon3d f0_necon3d f1_necon3d f2_necon3d a_wceq f3_necon3d f4_necon3d p_necon3ad f1_necon3d f2_necon3d a_df-ne f0_necon3d f3_necon3d f4_necon3d a_wne f1_necon3d f2_necon3d a_wceq a_wn f1_necon3d f2_necon3d a_wne p_syl6ibr $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       9-Aug-2006.) $)

${
	$v A B C D  $.
	f0_necon3i $f class A $.
	f1_necon3i $f class B $.
	f2_necon3i $f class C $.
	f3_necon3i $f class D $.
	e0_necon3i $e |- ( A = B -> C = D ) $.
	p_necon3i $p |- ( C =/= D -> A =/= B ) $= e0_necon3i f0_necon3i f1_necon3i a_wceq f2_necon3i f3_necon3i a_wceq a_wi p_id f0_necon3i f1_necon3i a_wceq f2_necon3i f3_necon3i a_wceq a_wi f0_necon3i f1_necon3i f2_necon3i f3_necon3i p_necon3d f0_necon3i f1_necon3i a_wceq f2_necon3i f3_necon3i a_wceq a_wi f2_necon3i f3_necon3i a_wne f0_necon3i f1_necon3i a_wne a_wi a_ax-mp $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       23-May-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B  $.
	f0_necon3ai $f wff ph $.
	f1_necon3ai $f class A $.
	f2_necon3ai $f class B $.
	e0_necon3ai $e |- ( ph -> A = B ) $.
	p_necon3ai $p |- ( A =/= B -> -. ph ) $= e0_necon3ai f1_necon3ai f2_necon3ai p_nne f0_necon3ai f1_necon3ai f2_necon3ai a_wceq f1_necon3ai f2_necon3ai a_wne a_wn p_sylibr f0_necon3ai f1_necon3ai f2_necon3ai a_wne p_con2i $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B  $.
	f0_necon3bi $f wff ph $.
	f1_necon3bi $f class A $.
	f2_necon3bi $f class B $.
	e0_necon3bi $e |- ( A = B -> ph ) $.
	p_necon3bi $p |- ( -. ph -> A =/= B ) $= f1_necon3bi f2_necon3bi p_nne e0_necon3bi f1_necon3bi f2_necon3bi a_wne a_wn f1_necon3bi f2_necon3bi a_wceq f0_necon3bi p_sylbi f1_necon3bi f2_necon3bi a_wne f0_necon3bi p_con1i $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       12-Feb-2007.) $)

${
	$v ph A B  $.
	f0_necon1ai $f wff ph $.
	f1_necon1ai $f class A $.
	f2_necon1ai $f class B $.
	e0_necon1ai $e |- ( -. ph -> A = B ) $.
	p_necon1ai $p |- ( A =/= B -> ph ) $= f1_necon1ai f2_necon1ai a_df-ne e0_necon1ai f0_necon1ai f1_necon1ai f2_necon1ai a_wceq p_con1i f1_necon1ai f2_necon1ai a_wne f1_necon1ai f2_necon1ai a_wceq a_wn f0_necon1ai p_sylbi $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B  $.
	f0_necon1bi $f wff ph $.
	f1_necon1bi $f class A $.
	f2_necon1bi $f class B $.
	e0_necon1bi $e |- ( A =/= B -> ph ) $.
	p_necon1bi $p |- ( -. ph -> A = B ) $= e0_necon1bi f1_necon1bi f2_necon1bi a_wne f0_necon1bi p_con3i f1_necon1bi f2_necon1bi p_nne f0_necon1bi a_wn f1_necon1bi f2_necon1bi a_wne a_wn f1_necon1bi f2_necon1bi a_wceq p_sylib $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.) $)

${
	$v A B C D  $.
	f0_necon1i $f class A $.
	f1_necon1i $f class B $.
	f2_necon1i $f class C $.
	f3_necon1i $f class D $.
	e0_necon1i $e |- ( A =/= B -> C = D ) $.
	p_necon1i $p |- ( C =/= D -> A = B ) $= f0_necon1i f1_necon1i a_df-ne e0_necon1i f0_necon1i f1_necon1i a_wceq a_wn f0_necon1i f1_necon1i a_wne f2_necon1i f3_necon1i a_wceq p_sylbir f0_necon1i f1_necon1i a_wceq f2_necon1i f3_necon1i p_necon1ai $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B  $.
	f0_necon2ai $f wff ph $.
	f1_necon2ai $f class A $.
	f2_necon2ai $f class B $.
	e0_necon2ai $e |- ( A = B -> -. ph ) $.
	p_necon2ai $p |- ( ph -> A =/= B ) $= f1_necon2ai f2_necon2ai p_nne e0_necon2ai f1_necon2ai f2_necon2ai a_wne a_wn f1_necon2ai f2_necon2ai a_wceq f0_necon2ai a_wn p_sylbi f1_necon2ai f2_necon2ai a_wne f0_necon2ai p_con4i $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       1-Apr-2007.) $)

${
	$v ph A B  $.
	f0_necon2bi $f wff ph $.
	f1_necon2bi $f class A $.
	f2_necon2bi $f class B $.
	e0_necon2bi $e |- ( ph -> A =/= B ) $.
	p_necon2bi $p |- ( A = B -> -. ph ) $= e0_necon2bi f0_necon2bi f1_necon2bi f2_necon2bi p_neneqd f0_necon2bi f1_necon2bi f2_necon2bi a_wceq p_con2i $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       18-Mar-2007.) $)

${
	$v A B C D  $.
	f0_necon2i $f class A $.
	f1_necon2i $f class B $.
	f2_necon2i $f class C $.
	f3_necon2i $f class D $.
	e0_necon2i $e |- ( A = B -> C =/= D ) $.
	p_necon2i $p |- ( C = D -> A =/= B ) $= e0_necon2i f0_necon2i f1_necon2i a_wceq f2_necon2i f3_necon2i p_neneqd f2_necon2i f3_necon2i a_wceq f0_necon2i f1_necon2i p_necon2ai $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       19-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_necon2ad $f wff ph $.
	f1_necon2ad $f wff ps $.
	f2_necon2ad $f class A $.
	f3_necon2ad $f class B $.
	e0_necon2ad $e |- ( ph -> ( A = B -> -. ps ) ) $.
	p_necon2ad $p |- ( ph -> ( ps -> A =/= B ) ) $= f2_necon2ad f3_necon2ad p_nne e0_necon2ad f2_necon2ad f3_necon2ad a_wne a_wn f2_necon2ad f3_necon2ad a_wceq f0_necon2ad f1_necon2ad a_wn p_syl5bi f0_necon2ad f2_necon2ad f3_necon2ad a_wne f1_necon2ad p_con4d $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)

${
	$v ph ps A B  $.
	f0_necon2bd $f wff ph $.
	f1_necon2bd $f wff ps $.
	f2_necon2bd $f class A $.
	f3_necon2bd $f class B $.
	e0_necon2bd $e |- ( ph -> ( ps -> A =/= B ) ) $.
	p_necon2bd $p |- ( ph -> ( A = B -> -. ps ) ) $= e0_necon2bd f2_necon2bd f3_necon2bd a_df-ne f0_necon2bd f1_necon2bd f2_necon2bd f3_necon2bd a_wne f2_necon2bd f3_necon2bd a_wceq a_wn p_syl6ib f0_necon2bd f1_necon2bd f2_necon2bd f3_necon2bd a_wceq p_con2d $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       28-Dec-2008.) $)

${
	$v ph A B C D  $.
	f0_necon2d $f wff ph $.
	f1_necon2d $f class A $.
	f2_necon2d $f class B $.
	f3_necon2d $f class C $.
	f4_necon2d $f class D $.
	e0_necon2d $e |- ( ph -> ( A = B -> C =/= D ) ) $.
	p_necon2d $p |- ( ph -> ( C = D -> A =/= B ) ) $= e0_necon2d f3_necon2d f4_necon2d a_df-ne f0_necon2d f1_necon2d f2_necon2d a_wceq f3_necon2d f4_necon2d a_wne f3_necon2d f4_necon2d a_wceq a_wn p_syl6ib f0_necon2d f3_necon2d f4_necon2d a_wceq f1_necon2d f2_necon2d p_necon2ad $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.) $)

${
	$v ph A B  $.
	f0_necon1abii $f wff ph $.
	f1_necon1abii $f class A $.
	f2_necon1abii $f class B $.
	e0_necon1abii $e |- ( -. ph <-> A = B ) $.
	p_necon1abii $p |- ( A =/= B <-> ph ) $= f1_necon1abii f2_necon1abii a_df-ne e0_necon1abii f0_necon1abii f1_necon1abii f2_necon1abii a_wceq p_con1bii f1_necon1abii f2_necon1abii a_wne f1_necon1abii f2_necon1abii a_wceq a_wn f0_necon1abii p_bitri $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.) $)

${
	$v ph A B  $.
	f0_necon1bbii $f wff ph $.
	f1_necon1bbii $f class A $.
	f2_necon1bbii $f class B $.
	e0_necon1bbii $e |- ( A =/= B <-> ph ) $.
	p_necon1bbii $p |- ( -. ph <-> A = B ) $= f1_necon1bbii f2_necon1bbii a_df-ne e0_necon1bbii f1_necon1bbii f2_necon1bbii a_wceq a_wn f1_necon1bbii f2_necon1bbii a_wne f0_necon1bbii p_bitr3i f1_necon1bbii f2_necon1bbii a_wceq f0_necon1bbii p_con1bii $.
$}

$(Contrapositive deduction for inequality.  (Contributed by NM,
       21-Aug-2007.) $)

${
	$v ph ps A B  $.
	f0_necon1abid $f wff ph $.
	f1_necon1abid $f wff ps $.
	f2_necon1abid $f class A $.
	f3_necon1abid $f class B $.
	e0_necon1abid $e |- ( ph -> ( -. ps <-> A = B ) ) $.
	p_necon1abid $p |- ( ph -> ( A =/= B <-> ps ) ) $= f2_necon1abid f3_necon1abid a_df-ne e0_necon1abid f0_necon1abid f1_necon1abid f2_necon1abid f3_necon1abid a_wceq p_con1bid f2_necon1abid f3_necon1abid a_wne f2_necon1abid f3_necon1abid a_wceq a_wn f0_necon1abid f1_necon1abid p_syl5bb $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       31-Jan-2008.) $)

${
	$v ph ps A B  $.
	f0_necon1bbid $f wff ph $.
	f1_necon1bbid $f wff ps $.
	f2_necon1bbid $f class A $.
	f3_necon1bbid $f class B $.
	e0_necon1bbid $e |- ( ph -> ( A =/= B <-> ps ) ) $.
	p_necon1bbid $p |- ( ph -> ( -. ps <-> A = B ) ) $= f2_necon1bbid f3_necon1bbid a_df-ne e0_necon1bbid f2_necon1bbid f3_necon1bbid a_wceq a_wn f2_necon1bbid f3_necon1bbid a_wne f0_necon1bbid f1_necon1bbid p_syl5bbr f0_necon1bbid f2_necon1bbid f3_necon1bbid a_wceq f1_necon1bbid p_con1bid $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       2-Mar-2007.) $)

${
	$v ph A B  $.
	f0_necon2abii $f wff ph $.
	f1_necon2abii $f class A $.
	f2_necon2abii $f class B $.
	e0_necon2abii $e |- ( A = B <-> -. ph ) $.
	p_necon2abii $p |- ( ph <-> A =/= B ) $= e0_necon2abii f1_necon2abii f2_necon2abii a_wceq f0_necon2abii a_wn p_bicomi f0_necon2abii f1_necon2abii f2_necon2abii p_necon1abii f1_necon2abii f2_necon2abii a_wne f0_necon2abii p_bicomi $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       13-Apr-2007.) $)

${
	$v ph A B  $.
	f0_necon2bbii $f wff ph $.
	f1_necon2bbii $f class A $.
	f2_necon2bbii $f class B $.
	e0_necon2bbii $e |- ( ph <-> A =/= B ) $.
	p_necon2bbii $p |- ( A = B <-> -. ph ) $= e0_necon2bbii f0_necon2bbii f1_necon2bbii f2_necon2bbii a_wne p_bicomi f0_necon2bbii f1_necon2bbii f2_necon2bbii p_necon1bbii f0_necon2bbii a_wn f1_necon2bbii f2_necon2bbii a_wceq p_bicomi $.
$}

$(Contrapositive deduction for inequality.  (Contributed by NM,
       18-Jul-2007.) $)

${
	$v ph ps A B  $.
	f0_necon2abid $f wff ph $.
	f1_necon2abid $f wff ps $.
	f2_necon2abid $f class A $.
	f3_necon2abid $f class B $.
	e0_necon2abid $e |- ( ph -> ( A = B <-> -. ps ) ) $.
	p_necon2abid $p |- ( ph -> ( ps <-> A =/= B ) ) $= e0_necon2abid f0_necon2abid f2_necon2abid f3_necon2abid a_wceq f1_necon2abid p_con2bid f2_necon2abid f3_necon2abid a_df-ne f0_necon2abid f1_necon2abid f2_necon2abid f3_necon2abid a_wceq a_wn f2_necon2abid f3_necon2abid a_wne p_syl6bbr $.
$}

$(Contrapositive deduction for inequality.  (Contributed by NM,
       13-Apr-2007.) $)

${
	$v ph ps A B  $.
	f0_necon2bbid $f wff ph $.
	f1_necon2bbid $f wff ps $.
	f2_necon2bbid $f class A $.
	f3_necon2bbid $f class B $.
	e0_necon2bbid $e |- ( ph -> ( ps <-> A =/= B ) ) $.
	p_necon2bbid $p |- ( ph -> ( A = B <-> -. ps ) ) $= e0_necon2bbid f2_necon2bbid f3_necon2bbid a_df-ne f0_necon2bbid f1_necon2bbid f2_necon2bbid f3_necon2bbid a_wne f2_necon2bbid f3_necon2bbid a_wceq a_wn p_syl6bb f0_necon2bbid f1_necon2bbid f2_necon2bbid f3_necon2bbid a_wceq p_con2bid $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B  $.
	f0_necon4ai $f wff ph $.
	f1_necon4ai $f class A $.
	f2_necon4ai $f class B $.
	e0_necon4ai $e |- ( A =/= B -> -. ph ) $.
	p_necon4ai $p |- ( ph -> A = B ) $= e0_necon4ai f1_necon4ai f2_necon4ai a_wne f0_necon4ai p_con2i f1_necon4ai f2_necon4ai p_nne f0_necon4ai f1_necon4ai f2_necon4ai a_wne a_wn f1_necon4ai f2_necon4ai a_wceq p_sylib $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       17-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v A B C D  $.
	f0_necon4i $f class A $.
	f1_necon4i $f class B $.
	f2_necon4i $f class C $.
	f3_necon4i $f class D $.
	e0_necon4i $e |- ( A =/= B -> C =/= D ) $.
	p_necon4i $p |- ( C = D -> A = B ) $= e0_necon4i f0_necon4i f1_necon4i a_wne f2_necon4i f3_necon4i p_necon2bi f0_necon4i f1_necon4i p_nne f2_necon4i f3_necon4i a_wceq f0_necon4i f1_necon4i a_wne a_wn f0_necon4i f1_necon4i a_wceq p_sylib $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_necon4ad $f wff ph $.
	f1_necon4ad $f wff ps $.
	f2_necon4ad $f class A $.
	f3_necon4ad $f class B $.
	e0_necon4ad $e |- ( ph -> ( A =/= B -> -. ps ) ) $.
	p_necon4ad $p |- ( ph -> ( ps -> A = B ) ) $= e0_necon4ad f0_necon4ad f2_necon4ad f3_necon4ad a_wne f1_necon4ad p_con2d f2_necon4ad f3_necon4ad p_nne f0_necon4ad f1_necon4ad f2_necon4ad f3_necon4ad a_wne a_wn f2_necon4ad f3_necon4ad a_wceq p_syl6ib $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_necon4bd $f wff ph $.
	f1_necon4bd $f wff ps $.
	f2_necon4bd $f class A $.
	f3_necon4bd $f class B $.
	e0_necon4bd $e |- ( ph -> ( -. ps -> A =/= B ) ) $.
	p_necon4bd $p |- ( ph -> ( A = B -> ps ) ) $= f2_necon4bd f3_necon4bd p_nne e0_necon4bd f0_necon4bd f1_necon4bd f2_necon4bd f3_necon4bd a_wne p_con1d f2_necon4bd f3_necon4bd a_wceq f2_necon4bd f3_necon4bd a_wne a_wn f0_necon4bd f1_necon4bd p_syl5bir $.
$}

$(Contrapositive inference for inequality.  (Contributed by NM,
       2-Apr-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_necon4d $f wff ph $.
	f1_necon4d $f class A $.
	f2_necon4d $f class B $.
	f3_necon4d $f class C $.
	f4_necon4d $f class D $.
	e0_necon4d $e |- ( ph -> ( A =/= B -> C =/= D ) ) $.
	p_necon4d $p |- ( ph -> ( C = D -> A = B ) ) $= e0_necon4d f0_necon4d f1_necon4d f2_necon4d a_wne f3_necon4d f4_necon4d p_necon2bd f1_necon4d f2_necon4d p_nne f0_necon4d f3_necon4d f4_necon4d a_wceq f1_necon4d f2_necon4d a_wne a_wn f1_necon4d f2_necon4d a_wceq p_syl6ib $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       11-Jan-2008.) $)

${
	$v ph ps A B  $.
	f0_necon4abid $f wff ph $.
	f1_necon4abid $f wff ps $.
	f2_necon4abid $f class A $.
	f3_necon4abid $f class B $.
	e0_necon4abid $e |- ( ph -> ( A =/= B <-> -. ps ) ) $.
	p_necon4abid $p |- ( ph -> ( A = B <-> ps ) ) $= f2_necon4abid f3_necon4abid a_df-ne e0_necon4abid f2_necon4abid f3_necon4abid a_wceq a_wn f2_necon4abid f3_necon4abid a_wne f0_necon4abid f1_necon4abid a_wn p_syl5bbr f0_necon4abid f2_necon4abid f3_necon4abid a_wceq f1_necon4abid p_con4bid $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       9-May-2012.) $)

${
	$v ph ps A B  $.
	f0_necon4bbid $f wff ph $.
	f1_necon4bbid $f wff ps $.
	f2_necon4bbid $f class A $.
	f3_necon4bbid $f class B $.
	e0_necon4bbid $e |- ( ph -> ( -. ps <-> A =/= B ) ) $.
	p_necon4bbid $p |- ( ph -> ( ps <-> A = B ) ) $= e0_necon4bbid f0_necon4bbid f1_necon4bbid a_wn f2_necon4bbid f3_necon4bbid a_wne p_bicomd f0_necon4bbid f1_necon4bbid f2_necon4bbid f3_necon4bbid p_necon4abid f0_necon4bbid f2_necon4bbid f3_necon4bbid a_wceq f1_necon4bbid p_bicomd $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       29-Jun-2007.) $)

${
	$v ph A B C D  $.
	f0_necon4bid $f wff ph $.
	f1_necon4bid $f class A $.
	f2_necon4bid $f class B $.
	f3_necon4bid $f class C $.
	f4_necon4bid $f class D $.
	e0_necon4bid $e |- ( ph -> ( A =/= B <-> C =/= D ) ) $.
	p_necon4bid $p |- ( ph -> ( A = B <-> C = D ) ) $= e0_necon4bid f0_necon4bid f1_necon4bid f2_necon4bid a_wne f3_necon4bid f4_necon4bid p_necon2bbid f1_necon4bid f2_necon4bid p_nne f0_necon4bid f3_necon4bid f4_necon4bid a_wceq f1_necon4bid f2_necon4bid a_wne a_wn f1_necon4bid f2_necon4bid a_wceq p_syl6rbb $.
$}

$(Contrapositive deduction for inequality.  (Contributed by NM,
       2-Apr-2007.) $)

${
	$v ph ps A B  $.
	f0_necon1ad $f wff ph $.
	f1_necon1ad $f wff ps $.
	f2_necon1ad $f class A $.
	f3_necon1ad $f class B $.
	e0_necon1ad $e |- ( ph -> ( -. ps -> A = B ) ) $.
	p_necon1ad $p |- ( ph -> ( A =/= B -> ps ) ) $= f2_necon1ad f3_necon1ad a_df-ne e0_necon1ad f0_necon1ad f1_necon1ad f2_necon1ad f3_necon1ad a_wceq p_con1d f2_necon1ad f3_necon1ad a_wne f2_necon1ad f3_necon1ad a_wceq a_wn f0_necon1ad f1_necon1ad p_syl5bi $.
$}

$(Contrapositive deduction for inequality.  (Contributed by NM,
       21-Mar-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_necon1bd $f wff ph $.
	f1_necon1bd $f wff ps $.
	f2_necon1bd $f class A $.
	f3_necon1bd $f class B $.
	e0_necon1bd $e |- ( ph -> ( A =/= B -> ps ) ) $.
	p_necon1bd $p |- ( ph -> ( -. ps -> A = B ) ) $= e0_necon1bd f0_necon1bd f2_necon1bd f3_necon1bd a_wne f1_necon1bd p_con3d f2_necon1bd f3_necon1bd p_nne f0_necon1bd f1_necon1bd a_wn f2_necon1bd f3_necon1bd a_wne a_wn f2_necon1bd f3_necon1bd a_wceq p_syl6ib $.
$}

$(Contrapositive law deduction for inequality.  (Contributed by NM,
       28-Dec-2008.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B C D  $.
	f0_necon1d $f wff ph $.
	f1_necon1d $f class A $.
	f2_necon1d $f class B $.
	f3_necon1d $f class C $.
	f4_necon1d $f class D $.
	e0_necon1d $e |- ( ph -> ( A =/= B -> C = D ) ) $.
	p_necon1d $p |- ( ph -> ( C =/= D -> A = B ) ) $= e0_necon1d f3_necon1d f4_necon1d p_nne f0_necon1d f1_necon1d f2_necon1d a_wne f3_necon1d f4_necon1d a_wceq f3_necon1d f4_necon1d a_wne a_wn p_syl6ibr f0_necon1d f3_necon1d f4_necon1d a_wne f1_necon1d f2_necon1d p_necon4ad $.
$}

$(If it is not the case that two classes are equal, they are unequal.
       Converse of ~ neneqd .  One-way deduction form of ~ df-ne .
       (Contributed by David Moews, 28-Feb-2017.) $)

${
	$v ph A B  $.
	f0_neneqad $f wff ph $.
	f1_neneqad $f class A $.
	f2_neneqad $f class B $.
	e0_neneqad $e |- ( ph -> -. A = B ) $.
	p_neneqad $p |- ( ph -> A =/= B ) $= e0_neneqad f0_neneqad f1_neneqad f2_neneqad a_wceq p_con2i f0_neneqad f1_neneqad f2_neneqad p_necon2ai $.
$}

$(Contraposition law for inequality.  (Contributed by NM, 28-Dec-2008.) $)

${
	$v A B C D  $.
	f0_nebi $f class A $.
	f1_nebi $f class B $.
	f2_nebi $f class C $.
	f3_nebi $f class D $.
	p_nebi $p |- ( ( A = B <-> C = D ) <-> ( A =/= B <-> C =/= D ) ) $= f0_nebi f1_nebi a_wceq f2_nebi f3_nebi a_wceq a_wb p_id f0_nebi f1_nebi a_wceq f2_nebi f3_nebi a_wceq a_wb f0_nebi f1_nebi f2_nebi f3_nebi p_necon3bid f0_nebi f1_nebi a_wne f2_nebi f3_nebi a_wne a_wb p_id f0_nebi f1_nebi a_wne f2_nebi f3_nebi a_wne a_wb f0_nebi f1_nebi f2_nebi f3_nebi p_necon4bid f0_nebi f1_nebi a_wceq f2_nebi f3_nebi a_wceq a_wb f0_nebi f1_nebi a_wne f2_nebi f3_nebi a_wne a_wb p_impbii $.
$}

$(Theorem *13.18 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)

${
	$v A B C  $.
	f0_pm13.18 $f class A $.
	f1_pm13.18 $f class B $.
	f2_pm13.18 $f class C $.
	p_pm13.18 $p |- ( ( A = B /\ A =/= C ) -> B =/= C ) $= f0_pm13.18 f1_pm13.18 f2_pm13.18 p_eqeq1 f0_pm13.18 f1_pm13.18 a_wceq f0_pm13.18 f2_pm13.18 a_wceq f1_pm13.18 f2_pm13.18 a_wceq p_biimprd f0_pm13.18 f1_pm13.18 a_wceq f1_pm13.18 f2_pm13.18 f0_pm13.18 f2_pm13.18 p_necon3d f0_pm13.18 f1_pm13.18 a_wceq f0_pm13.18 f2_pm13.18 a_wne f1_pm13.18 f2_pm13.18 a_wne p_imp $.
$}

$(Theorem *13.181 in [WhiteheadRussell] p. 178.  (Contributed by Andrew
     Salmon, 3-Jun-2011.) $)

${
	$v A B C  $.
	f0_pm13.181 $f class A $.
	f1_pm13.181 $f class B $.
	f2_pm13.181 $f class C $.
	p_pm13.181 $p |- ( ( A = B /\ B =/= C ) -> A =/= C ) $= f0_pm13.181 f1_pm13.181 p_eqcom f1_pm13.181 f0_pm13.181 f2_pm13.181 p_pm13.18 f0_pm13.181 f1_pm13.181 a_wceq f1_pm13.181 f0_pm13.181 a_wceq f1_pm13.181 f2_pm13.181 a_wne f0_pm13.181 f2_pm13.181 a_wne p_sylanb $.
$}

$(A contradiction implies anything.  Equality/inequality deduction form.
       (Contributed by David Moews, 28-Feb-2017.) $)

${
	$v ph ps A B  $.
	f0_pm2.21ddne $f wff ph $.
	f1_pm2.21ddne $f wff ps $.
	f2_pm2.21ddne $f class A $.
	f3_pm2.21ddne $f class B $.
	e0_pm2.21ddne $e |- ( ph -> A = B ) $.
	e1_pm2.21ddne $e |- ( ph -> A =/= B ) $.
	p_pm2.21ddne $p |- ( ph -> ps ) $= e0_pm2.21ddne e1_pm2.21ddne f0_pm2.21ddne f2_pm2.21ddne f3_pm2.21ddne p_neneqd f0_pm2.21ddne f2_pm2.21ddne f3_pm2.21ddne a_wceq f1_pm2.21ddne p_pm2.21dd $.
$}

$(Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 24-May-2006.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps ch A B  $.
	f0_pm2.61ne $f wff ph $.
	f1_pm2.61ne $f wff ps $.
	f2_pm2.61ne $f wff ch $.
	f3_pm2.61ne $f class A $.
	f4_pm2.61ne $f class B $.
	e0_pm2.61ne $e |- ( A = B -> ( ps <-> ch ) ) $.
	e1_pm2.61ne $e |- ( ( ph /\ A =/= B ) -> ps ) $.
	e2_pm2.61ne $e |- ( ph -> ch ) $.
	p_pm2.61ne $p |- ( ph -> ps ) $= e1_pm2.61ne f0_pm2.61ne f3_pm2.61ne f4_pm2.61ne a_wne f1_pm2.61ne p_expcom f3_pm2.61ne f4_pm2.61ne p_nne e2_pm2.61ne e0_pm2.61ne f0_pm2.61ne f1_pm2.61ne f3_pm2.61ne f4_pm2.61ne a_wceq f2_pm2.61ne p_syl5ibr f3_pm2.61ne f4_pm2.61ne a_wne a_wn f3_pm2.61ne f4_pm2.61ne a_wceq f0_pm2.61ne f1_pm2.61ne a_wi p_sylbi f3_pm2.61ne f4_pm2.61ne a_wne f0_pm2.61ne f1_pm2.61ne a_wi p_pm2.61i $.
$}

$(Inference eliminating an inequality in an antecedent.  (Contributed by
       NM, 16-Jan-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph A B  $.
	f0_pm2.61ine $f wff ph $.
	f1_pm2.61ine $f class A $.
	f2_pm2.61ine $f class B $.
	e0_pm2.61ine $e |- ( A = B -> ph ) $.
	e1_pm2.61ine $e |- ( A =/= B -> ph ) $.
	p_pm2.61ine $p |- ph $= e1_pm2.61ine f1_pm2.61ine f2_pm2.61ine p_nne e0_pm2.61ine f1_pm2.61ine f2_pm2.61ine a_wne a_wn f1_pm2.61ine f2_pm2.61ine a_wceq f0_pm2.61ine p_sylbi f1_pm2.61ine f2_pm2.61ine a_wne f0_pm2.61ine p_pm2.61i $.
$}

$(Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 1-Jun-2007.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)

${
	$v ph ps A B  $.
	f0_pm2.61dne $f wff ph $.
	f1_pm2.61dne $f wff ps $.
	f2_pm2.61dne $f class A $.
	f3_pm2.61dne $f class B $.
	e0_pm2.61dne $e |- ( ph -> ( A = B -> ps ) ) $.
	e1_pm2.61dne $e |- ( ph -> ( A =/= B -> ps ) ) $.
	p_pm2.61dne $p |- ( ph -> ps ) $= e1_pm2.61dne f2_pm2.61dne f3_pm2.61dne p_nne e0_pm2.61dne f2_pm2.61dne f3_pm2.61dne a_wne a_wn f2_pm2.61dne f3_pm2.61dne a_wceq f0_pm2.61dne f1_pm2.61dne p_syl5bi f0_pm2.61dne f2_pm2.61dne f3_pm2.61dne a_wne f1_pm2.61dne p_pm2.61d $.
$}

$(Deduction eliminating an inequality in an antecedent.  (Contributed by
       NM, 30-Nov-2011.) $)

${
	$v ph ps A B  $.
	f0_pm2.61dane $f wff ph $.
	f1_pm2.61dane $f wff ps $.
	f2_pm2.61dane $f class A $.
	f3_pm2.61dane $f class B $.
	e0_pm2.61dane $e |- ( ( ph /\ A = B ) -> ps ) $.
	e1_pm2.61dane $e |- ( ( ph /\ A =/= B ) -> ps ) $.
	p_pm2.61dane $p |- ( ph -> ps ) $= e0_pm2.61dane f0_pm2.61dane f2_pm2.61dane f3_pm2.61dane a_wceq f1_pm2.61dane p_ex e1_pm2.61dane f0_pm2.61dane f2_pm2.61dane f3_pm2.61dane a_wne f1_pm2.61dane p_ex f0_pm2.61dane f1_pm2.61dane f2_pm2.61dane f3_pm2.61dane p_pm2.61dne $.
$}

$(Deduction eliminating two inequalities in an antecedent.  (Contributed
       by NM, 29-May-2013.) $)

${
	$v ph ps A B C D  $.
	f0_pm2.61da2ne $f wff ph $.
	f1_pm2.61da2ne $f wff ps $.
	f2_pm2.61da2ne $f class A $.
	f3_pm2.61da2ne $f class B $.
	f4_pm2.61da2ne $f class C $.
	f5_pm2.61da2ne $f class D $.
	e0_pm2.61da2ne $e |- ( ( ph /\ A = B ) -> ps ) $.
	e1_pm2.61da2ne $e |- ( ( ph /\ C = D ) -> ps ) $.
	e2_pm2.61da2ne $e |- ( ( ph /\ ( A =/= B /\ C =/= D ) ) -> ps ) $.
	p_pm2.61da2ne $p |- ( ph -> ps ) $= e0_pm2.61da2ne e1_pm2.61da2ne f0_pm2.61da2ne f4_pm2.61da2ne f5_pm2.61da2ne a_wceq f1_pm2.61da2ne f2_pm2.61da2ne f3_pm2.61da2ne a_wne p_adantlr e2_pm2.61da2ne f0_pm2.61da2ne f2_pm2.61da2ne f3_pm2.61da2ne a_wne f4_pm2.61da2ne f5_pm2.61da2ne a_wne f1_pm2.61da2ne p_anassrs f0_pm2.61da2ne f2_pm2.61da2ne f3_pm2.61da2ne a_wne a_wa f1_pm2.61da2ne f4_pm2.61da2ne f5_pm2.61da2ne p_pm2.61dane f0_pm2.61da2ne f1_pm2.61da2ne f2_pm2.61da2ne f3_pm2.61da2ne p_pm2.61dane $.
$}

$(Deduction eliminating three inequalities in an antecedent.  (Contributed
       by NM, 15-Jun-2013.) $)

${
	$v ph ps A B C D E F  $.
	f0_pm2.61da3ne $f wff ph $.
	f1_pm2.61da3ne $f wff ps $.
	f2_pm2.61da3ne $f class A $.
	f3_pm2.61da3ne $f class B $.
	f4_pm2.61da3ne $f class C $.
	f5_pm2.61da3ne $f class D $.
	f6_pm2.61da3ne $f class E $.
	f7_pm2.61da3ne $f class F $.
	e0_pm2.61da3ne $e |- ( ( ph /\ A = B ) -> ps ) $.
	e1_pm2.61da3ne $e |- ( ( ph /\ C = D ) -> ps ) $.
	e2_pm2.61da3ne $e |- ( ( ph /\ E = F ) -> ps ) $.
	e3_pm2.61da3ne $e |- ( ( ph /\ ( A =/= B /\ C =/= D /\ E =/= F ) ) -> ps ) $.
	p_pm2.61da3ne $p |- ( ph -> ps ) $= e0_pm2.61da3ne e1_pm2.61da3ne e2_pm2.61da3ne f0_pm2.61da3ne f6_pm2.61da3ne f7_pm2.61da3ne a_wceq f1_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne a_wa p_adantlr f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne a_wa f6_pm2.61da3ne f7_pm2.61da3ne a_wne p_simpll f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne f6_pm2.61da3ne f7_pm2.61da3ne a_wne p_simplrl f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne f6_pm2.61da3ne f7_pm2.61da3ne a_wne p_simplrr f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne a_wa a_wa f6_pm2.61da3ne f7_pm2.61da3ne a_wne p_simpr e3_pm2.61da3ne f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne a_wa a_wa f6_pm2.61da3ne f7_pm2.61da3ne a_wne a_wa f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne f6_pm2.61da3ne f7_pm2.61da3ne a_wne f1_pm2.61da3ne p_syl13anc f0_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne a_wne f4_pm2.61da3ne f5_pm2.61da3ne a_wne a_wa a_wa f1_pm2.61da3ne f6_pm2.61da3ne f7_pm2.61da3ne p_pm2.61dane f0_pm2.61da3ne f1_pm2.61da3ne f2_pm2.61da3ne f3_pm2.61da3ne f4_pm2.61da3ne f5_pm2.61da3ne p_pm2.61da2ne $.
$}

$(Commutation of inequality.  (Contributed by NM, 14-May-1999.) $)

${
	$v A B  $.
	f0_necom $f class A $.
	f1_necom $f class B $.
	p_necom $p |- ( A =/= B <-> B =/= A ) $= f0_necom f1_necom p_eqcom f0_necom f1_necom f1_necom f0_necom p_necon3bii $.
$}

$(Inference from commutative law for inequality.  (Contributed by NM,
       17-Oct-2012.) $)

${
	$v A B  $.
	f0_necomi $f class A $.
	f1_necomi $f class B $.
	e0_necomi $e |- A =/= B $.
	p_necomi $p |- B =/= A $= e0_necomi f0_necomi f1_necomi p_necom f0_necomi f1_necomi a_wne f1_necomi f0_necomi a_wne p_mpbi $.
$}

$(Deduction from commutative law for inequality.  (Contributed by NM,
       12-Feb-2008.) $)

${
	$v ph A B  $.
	f0_necomd $f wff ph $.
	f1_necomd $f class A $.
	f2_necomd $f class B $.
	e0_necomd $e |- ( ph -> A =/= B ) $.
	p_necomd $p |- ( ph -> B =/= A ) $= e0_necomd f1_necomd f2_necomd p_necom f0_necomd f1_necomd f2_necomd a_wne f2_necomd f1_necomd a_wne p_sylib $.
$}

$(Logical OR with an equality.  (Contributed by NM, 29-Apr-2007.) $)

${
	$v ps A B  $.
	f0_neor $f wff ps $.
	f1_neor $f class A $.
	f2_neor $f class B $.
	p_neor $p |- ( ( A = B \/ ps ) <-> ( A =/= B -> ps ) ) $= f1_neor f2_neor a_wceq f0_neor a_df-or f1_neor f2_neor a_df-ne f1_neor f2_neor a_wne f1_neor f2_neor a_wceq a_wn f0_neor p_imbi1i f1_neor f2_neor a_wceq f0_neor a_wo f1_neor f2_neor a_wceq a_wn f0_neor a_wi f1_neor f2_neor a_wne f0_neor a_wi p_bitr4i $.
$}

$(A De Morgan's law for inequality.  (Contributed by NM, 18-May-2007.) $)

${
	$v A B C D  $.
	f0_neanior $f class A $.
	f1_neanior $f class B $.
	f2_neanior $f class C $.
	f3_neanior $f class D $.
	p_neanior $p |- ( ( A =/= B /\ C =/= D ) <-> -. ( A = B \/ C = D ) ) $= f0_neanior f1_neanior a_df-ne f2_neanior f3_neanior a_df-ne f0_neanior f1_neanior a_wne f0_neanior f1_neanior a_wceq a_wn f2_neanior f3_neanior a_wne f2_neanior f3_neanior a_wceq a_wn p_anbi12i f0_neanior f1_neanior a_wceq f2_neanior f3_neanior a_wceq p_pm4.56 f0_neanior f1_neanior a_wne f2_neanior f3_neanior a_wne a_wa f0_neanior f1_neanior a_wceq a_wn f2_neanior f3_neanior a_wceq a_wn a_wa f0_neanior f1_neanior a_wceq f2_neanior f3_neanior a_wceq a_wo a_wn p_bitri $.
$}

$(A De Morgan's law for inequality.  (Contributed by NM, 30-Sep-2013.) $)

${
	$v A B C D E F  $.
	f0_ne3anior $f class A $.
	f1_ne3anior $f class B $.
	f2_ne3anior $f class C $.
	f3_ne3anior $f class D $.
	f4_ne3anior $f class E $.
	f5_ne3anior $f class F $.
	p_ne3anior $p |- ( ( A =/= B /\ C =/= D /\ E =/= F ) <-> -. ( A = B \/ C = D \/ E = F ) ) $= f0_ne3anior f1_ne3anior a_wne f2_ne3anior f3_ne3anior a_wne f4_ne3anior f5_ne3anior a_wne p_3anor f0_ne3anior f1_ne3anior p_nne f2_ne3anior f3_ne3anior p_nne f4_ne3anior f5_ne3anior p_nne f0_ne3anior f1_ne3anior a_wne a_wn f0_ne3anior f1_ne3anior a_wceq f2_ne3anior f3_ne3anior a_wne a_wn f2_ne3anior f3_ne3anior a_wceq f4_ne3anior f5_ne3anior a_wne a_wn f4_ne3anior f5_ne3anior a_wceq p_3orbi123i f0_ne3anior f1_ne3anior a_wne f2_ne3anior f3_ne3anior a_wne f4_ne3anior f5_ne3anior a_wne a_w3a f0_ne3anior f1_ne3anior a_wne a_wn f2_ne3anior f3_ne3anior a_wne a_wn f4_ne3anior f5_ne3anior a_wne a_wn a_w3o f0_ne3anior f1_ne3anior a_wceq f2_ne3anior f3_ne3anior a_wceq f4_ne3anior f5_ne3anior a_wceq a_w3o p_xchbinx $.
$}

$(A De Morgan's law for inequality.  (Contributed by NM, 18-May-2007.) $)

${
	$v A B C D  $.
	f0_neorian $f class A $.
	f1_neorian $f class B $.
	f2_neorian $f class C $.
	f3_neorian $f class D $.
	p_neorian $p |- ( ( A =/= B \/ C =/= D ) <-> -. ( A = B /\ C = D ) ) $= f0_neorian f1_neorian a_df-ne f2_neorian f3_neorian a_df-ne f0_neorian f1_neorian a_wne f0_neorian f1_neorian a_wceq a_wn f2_neorian f3_neorian a_wne f2_neorian f3_neorian a_wceq a_wn p_orbi12i f0_neorian f1_neorian a_wceq f2_neorian f3_neorian a_wceq p_ianor f0_neorian f1_neorian a_wne f2_neorian f3_neorian a_wne a_wo f0_neorian f1_neorian a_wceq a_wn f2_neorian f3_neorian a_wceq a_wn a_wo f0_neorian f1_neorian a_wceq f2_neorian f3_neorian a_wceq a_wa a_wn p_bitr4i $.
$}

$(An inference from an inequality, related to modus tollens.  (Contributed
       by NM, 13-Apr-2007.) $)

${
	$v ph A B  $.
	f0_nemtbir $f wff ph $.
	f1_nemtbir $f class A $.
	f2_nemtbir $f class B $.
	e0_nemtbir $e |- A =/= B $.
	e1_nemtbir $e |- ( ph <-> A = B ) $.
	p_nemtbir $p |- -. ph $= e0_nemtbir f1_nemtbir f2_nemtbir a_df-ne f1_nemtbir f2_nemtbir a_wne f1_nemtbir f2_nemtbir a_wceq a_wn p_mpbi e1_nemtbir f0_nemtbir f1_nemtbir f2_nemtbir a_wceq p_mtbir $.
$}

$(Two classes are different if they don't contain the same element.
     (Contributed by NM, 3-Feb-2012.) $)

${
	$v A B C  $.
	f0_nelne1 $f class A $.
	f1_nelne1 $f class B $.
	f2_nelne1 $f class C $.
	p_nelne1 $p |- ( ( A e. B /\ -. A e. C ) -> B =/= C ) $= f1_nelne1 f2_nelne1 f0_nelne1 p_eleq2 f1_nelne1 f2_nelne1 a_wceq f0_nelne1 f1_nelne1 a_wcel f0_nelne1 f2_nelne1 a_wcel p_biimpcd f0_nelne1 f1_nelne1 a_wcel f0_nelne1 f2_nelne1 a_wcel f1_nelne1 f2_nelne1 p_necon3bd f0_nelne1 f1_nelne1 a_wcel f0_nelne1 f2_nelne1 a_wcel a_wn f1_nelne1 f2_nelne1 a_wne p_imp $.
$}

$(Two classes are different if they don't belong to the same class.
     (Contributed by NM, 25-Jun-2012.) $)

${
	$v A B C  $.
	f0_nelne2 $f class A $.
	f1_nelne2 $f class B $.
	f2_nelne2 $f class C $.
	p_nelne2 $p |- ( ( A e. C /\ -. B e. C ) -> A =/= B ) $= f0_nelne2 f1_nelne2 f2_nelne2 p_eleq1 f0_nelne2 f1_nelne2 a_wceq f0_nelne2 f2_nelne2 a_wcel f1_nelne2 f2_nelne2 a_wcel p_biimpcd f0_nelne2 f2_nelne2 a_wcel f1_nelne2 f2_nelne2 a_wcel f0_nelne2 f1_nelne2 p_necon3bd f0_nelne2 f2_nelne2 a_wcel f1_nelne2 f2_nelne2 a_wcel a_wn f0_nelne2 f1_nelne2 a_wne p_imp $.
$}

$(Equality theorem for negated membership.  (Contributed by NM,
     20-Nov-1994.) $)

${
	$v A B C  $.
	f0_neleq1 $f class A $.
	f1_neleq1 $f class B $.
	f2_neleq1 $f class C $.
	p_neleq1 $p |- ( A = B -> ( A e/ C <-> B e/ C ) ) $= f0_neleq1 f1_neleq1 f2_neleq1 p_eleq1 f0_neleq1 f1_neleq1 a_wceq f0_neleq1 f2_neleq1 a_wcel f1_neleq1 f2_neleq1 a_wcel p_notbid f0_neleq1 f2_neleq1 a_df-nel f1_neleq1 f2_neleq1 a_df-nel f0_neleq1 f1_neleq1 a_wceq f0_neleq1 f2_neleq1 a_wcel a_wn f1_neleq1 f2_neleq1 a_wcel a_wn f0_neleq1 f2_neleq1 a_wnel f1_neleq1 f2_neleq1 a_wnel p_3bitr4g $.
$}

$(Equality theorem for negated membership.  (Contributed by NM,
     20-Nov-1994.) $)

${
	$v A B C  $.
	f0_neleq2 $f class A $.
	f1_neleq2 $f class B $.
	f2_neleq2 $f class C $.
	p_neleq2 $p |- ( A = B -> ( C e/ A <-> C e/ B ) ) $= f0_neleq2 f1_neleq2 f2_neleq2 p_eleq2 f0_neleq2 f1_neleq2 a_wceq f2_neleq2 f0_neleq2 a_wcel f2_neleq2 f1_neleq2 a_wcel p_notbid f2_neleq2 f0_neleq2 a_df-nel f2_neleq2 f1_neleq2 a_df-nel f0_neleq2 f1_neleq2 a_wceq f2_neleq2 f0_neleq2 a_wcel a_wn f2_neleq2 f1_neleq2 a_wcel a_wn f2_neleq2 f0_neleq2 a_wnel f2_neleq2 f1_neleq2 a_wnel p_3bitr4g $.
$}

$(Bound-variable hypothesis builder for inequality.  (Contributed by NM,
       10-Nov-2007.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v x A B  $.
	$d A  $.
	$d B  $.
	f0_nfne $f set x $.
	f1_nfne $f class A $.
	f2_nfne $f class B $.
	e0_nfne $e |- F/_ x A $.
	e1_nfne $e |- F/_ x B $.
	p_nfne $p |- F/ x A =/= B $= f1_nfne f2_nfne a_df-ne e0_nfne e1_nfne f0_nfne f1_nfne f2_nfne p_nfeq f1_nfne f2_nfne a_wceq f0_nfne p_nfn f1_nfne f2_nfne a_wne f1_nfne f2_nfne a_wceq a_wn f0_nfne p_nfxfr $.
$}

$(Bound-variable hypothesis builder for inequality.  (Contributed by David
       Abernethy, 26-Jun-2011.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v x A B  $.
	$d A  $.
	$d B  $.
	f0_nfnel $f set x $.
	f1_nfnel $f class A $.
	f2_nfnel $f class B $.
	e0_nfnel $e |- F/_ x A $.
	e1_nfnel $e |- F/_ x B $.
	p_nfnel $p |- F/ x A e/ B $= f1_nfnel f2_nfnel a_df-nel e0_nfnel e1_nfnel f0_nfnel f1_nfnel f2_nfnel p_nfel f1_nfnel f2_nfnel a_wcel f0_nfnel p_nfn f1_nfnel f2_nfnel a_wnel f1_nfnel f2_nfnel a_wcel a_wn f0_nfnel p_nfxfr $.
$}

$(Bound-variable hypothesis builder for inequality.  (Contributed by NM,
       10-Nov-2007.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_nfned $f wff ph $.
	f1_nfned $f set x $.
	f2_nfned $f class A $.
	f3_nfned $f class B $.
	e0_nfned $e |- ( ph -> F/_ x A ) $.
	e1_nfned $e |- ( ph -> F/_ x B ) $.
	p_nfned $p |- ( ph -> F/ x A =/= B ) $= f2_nfned f3_nfned a_df-ne e0_nfned e1_nfned f0_nfned f1_nfned f2_nfned f3_nfned p_nfeqd f0_nfned f2_nfned f3_nfned a_wceq f1_nfned p_nfnd f2_nfned f3_nfned a_wne f2_nfned f3_nfned a_wceq a_wn f0_nfned f1_nfned p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for inequality.  (Contributed by David
       Abernethy, 26-Jun-2011.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)

${
	$v ph x A B  $.
	$d A  $.
	$d B  $.
	f0_nfneld $f wff ph $.
	f1_nfneld $f set x $.
	f2_nfneld $f class A $.
	f3_nfneld $f class B $.
	e0_nfneld $e |- ( ph -> F/_ x A ) $.
	e1_nfneld $e |- ( ph -> F/_ x B ) $.
	p_nfneld $p |- ( ph -> F/ x A e/ B ) $= f2_nfneld f3_nfneld a_df-nel e0_nfneld e1_nfneld f0_nfneld f1_nfneld f2_nfneld f3_nfneld p_nfeld f0_nfneld f2_nfneld f3_nfneld a_wcel f1_nfneld p_nfnd f2_nfneld f3_nfneld a_wnel f2_nfneld f3_nfneld a_wcel a_wn f0_nfneld f1_nfneld p_nfxfrd $.
$}


