$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Disjointness.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Binary relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Extend wff notation to include the general binary relation predicate.
     Note that the syntax is simply three class symbols in a row.  Since binary
     relations are the only possible wff expressions consisting of three class
     expressions in a row, the syntax is unambiguous.  (For an example of how
     syntax could become ambiguous if we are not careful, see the comment in
     ~ cneg .) $)
${
	$v A $.
	$v B $.
	$v R $.
	fwbr_0 $f class A $.
	fwbr_1 $f class B $.
	fwbr_2 $f class R $.
	wbr $a wff A R B $.
$}
$( Define a general binary relation.  Note that the syntax is simply three
     class symbols in a row.  Definition 6.18 of [TakeutiZaring] p. 29
     generalized to arbitrary classes.  Class ` R ` often denotes a relation
     such as " ` < ` " that compares two classes ` A ` and ` B ` , which might
     be numbers such as ` 1 ` and ` 2 ` (see ~ df-ltxr for the specific
     definition of ` < ` ).  As a wff, relations are true or false.  For
     example, ` ( R = { <. 2 , 6 >. , <. 3 , 9 >. } -> 3 R 9 ) ` ( ~ ex-br ).
     Often class ` R ` meets the ` Rel ` criteria to be defined in ~ df-rel ,
     and in particular ` R ` may be a function (see ~ df-fun ).  This
     definition of relations is well-defined, although not very meaningful,
     when classes ` A ` and/or ` B ` are proper classes (i.e. are not sets).
     On the other hand, we often find uses for this definition when ` R ` is a
     proper class.  (Contributed by NM, 31-Dec-1993.) $)
${
	$v A $.
	$v B $.
	$v R $.
	fdf-br_0 $f class A $.
	fdf-br_1 $f class B $.
	fdf-br_2 $f class R $.
	df-br $a |- ( A R B <-> <. A , B >. e. R ) $.
$}
$( Equality theorem for binary relations.  (Contributed by NM,
     4-Jun-1995.) $)
${
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	fbreq_0 $f class A $.
	fbreq_1 $f class B $.
	fbreq_2 $f class R $.
	fbreq_3 $f class S $.
	breq $p |- ( R = S -> ( A R B <-> A S B ) ) $= fbreq_2 fbreq_3 wceq fbreq_0 fbreq_1 cop fbreq_2 wcel fbreq_0 fbreq_1 cop fbreq_3 wcel fbreq_0 fbreq_1 fbreq_2 wbr fbreq_0 fbreq_1 fbreq_3 wbr fbreq_2 fbreq_3 fbreq_0 fbreq_1 cop eleq2 fbreq_0 fbreq_1 fbreq_2 df-br fbreq_0 fbreq_1 fbreq_3 df-br 3bitr4g $.
$}
$( Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreq1_0 $f class A $.
	fbreq1_1 $f class B $.
	fbreq1_2 $f class C $.
	fbreq1_3 $f class R $.
	breq1 $p |- ( A = B -> ( A R C <-> B R C ) ) $= fbreq1_0 fbreq1_1 wceq fbreq1_0 fbreq1_2 cop fbreq1_3 wcel fbreq1_1 fbreq1_2 cop fbreq1_3 wcel fbreq1_0 fbreq1_2 fbreq1_3 wbr fbreq1_1 fbreq1_2 fbreq1_3 wbr fbreq1_0 fbreq1_1 wceq fbreq1_0 fbreq1_2 cop fbreq1_1 fbreq1_2 cop fbreq1_3 fbreq1_0 fbreq1_1 fbreq1_2 opeq1 eleq1d fbreq1_0 fbreq1_2 fbreq1_3 df-br fbreq1_1 fbreq1_2 fbreq1_3 df-br 3bitr4g $.
$}
$( Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreq2_0 $f class A $.
	fbreq2_1 $f class B $.
	fbreq2_2 $f class C $.
	fbreq2_3 $f class R $.
	breq2 $p |- ( A = B -> ( C R A <-> C R B ) ) $= fbreq2_0 fbreq2_1 wceq fbreq2_2 fbreq2_0 cop fbreq2_3 wcel fbreq2_2 fbreq2_1 cop fbreq2_3 wcel fbreq2_2 fbreq2_0 fbreq2_3 wbr fbreq2_2 fbreq2_1 fbreq2_3 wbr fbreq2_0 fbreq2_1 wceq fbreq2_2 fbreq2_0 cop fbreq2_2 fbreq2_1 cop fbreq2_3 fbreq2_0 fbreq2_1 fbreq2_2 opeq2 eleq1d fbreq2_2 fbreq2_0 fbreq2_3 df-br fbreq2_2 fbreq2_1 fbreq2_3 df-br 3bitr4g $.
$}
$( Equality theorem for a binary relation.  (Contributed by NM,
     8-Feb-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	fbreq12_0 $f class A $.
	fbreq12_1 $f class B $.
	fbreq12_2 $f class C $.
	fbreq12_3 $f class D $.
	fbreq12_4 $f class R $.
	breq12 $p |- ( ( A = B /\ C = D ) -> ( A R C <-> B R D ) ) $= fbreq12_0 fbreq12_1 wceq fbreq12_0 fbreq12_2 fbreq12_4 wbr fbreq12_1 fbreq12_2 fbreq12_4 wbr fbreq12_2 fbreq12_3 wceq fbreq12_1 fbreq12_3 fbreq12_4 wbr fbreq12_0 fbreq12_1 fbreq12_2 fbreq12_4 breq1 fbreq12_2 fbreq12_3 fbreq12_1 fbreq12_4 breq2 sylan9bb $.
$}
$( Equality inference for binary relations.  (Contributed by NM,
       19-Feb-2005.) $)
${
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	fbreqi_0 $f class A $.
	fbreqi_1 $f class B $.
	fbreqi_2 $f class R $.
	fbreqi_3 $f class S $.
	ebreqi_0 $e |- R = S $.
	breqi $p |- ( A R B <-> A S B ) $= fbreqi_2 fbreqi_3 wceq fbreqi_0 fbreqi_1 fbreqi_2 wbr fbreqi_0 fbreqi_1 fbreqi_3 wbr wb ebreqi_0 fbreqi_0 fbreqi_1 fbreqi_2 fbreqi_3 breq ax-mp $.
$}
$( Equality inference for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreq1i_0 $f class A $.
	fbreq1i_1 $f class B $.
	fbreq1i_2 $f class C $.
	fbreq1i_3 $f class R $.
	ebreq1i_0 $e |- A = B $.
	breq1i $p |- ( A R C <-> B R C ) $= fbreq1i_0 fbreq1i_1 wceq fbreq1i_0 fbreq1i_2 fbreq1i_3 wbr fbreq1i_1 fbreq1i_2 fbreq1i_3 wbr wb ebreq1i_0 fbreq1i_0 fbreq1i_1 fbreq1i_2 fbreq1i_3 breq1 ax-mp $.
$}
$( Equality inference for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreq2i_0 $f class A $.
	fbreq2i_1 $f class B $.
	fbreq2i_2 $f class C $.
	fbreq2i_3 $f class R $.
	ebreq2i_0 $e |- A = B $.
	breq2i $p |- ( C R A <-> C R B ) $= fbreq2i_0 fbreq2i_1 wceq fbreq2i_2 fbreq2i_0 fbreq2i_3 wbr fbreq2i_2 fbreq2i_1 fbreq2i_3 wbr wb ebreq2i_0 fbreq2i_0 fbreq2i_1 fbreq2i_2 fbreq2i_3 breq2 ax-mp $.
$}
$( Equality inference for a binary relation.  (Contributed by NM,
         8-Feb-1996.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	fbreq12i_0 $f class A $.
	fbreq12i_1 $f class B $.
	fbreq12i_2 $f class C $.
	fbreq12i_3 $f class D $.
	fbreq12i_4 $f class R $.
	ebreq12i_0 $e |- A = B $.
	ebreq12i_1 $e |- C = D $.
	breq12i $p |- ( A R C <-> B R D ) $= fbreq12i_0 fbreq12i_1 wceq fbreq12i_2 fbreq12i_3 wceq fbreq12i_0 fbreq12i_2 fbreq12i_4 wbr fbreq12i_1 fbreq12i_3 fbreq12i_4 wbr wb ebreq12i_0 ebreq12i_1 fbreq12i_0 fbreq12i_1 fbreq12i_2 fbreq12i_3 fbreq12i_4 breq12 mp2an $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreq1d_0 $f wff ph $.
	fbreq1d_1 $f class A $.
	fbreq1d_2 $f class B $.
	fbreq1d_3 $f class C $.
	fbreq1d_4 $f class R $.
	ebreq1d_0 $e |- ( ph -> A = B ) $.
	breq1d $p |- ( ph -> ( A R C <-> B R C ) ) $= fbreq1d_0 fbreq1d_1 fbreq1d_2 wceq fbreq1d_1 fbreq1d_3 fbreq1d_4 wbr fbreq1d_2 fbreq1d_3 fbreq1d_4 wbr wb ebreq1d_0 fbreq1d_1 fbreq1d_2 fbreq1d_3 fbreq1d_4 breq1 syl $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
       29-Oct-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fbreqd_0 $f wff ph $.
	fbreqd_1 $f class A $.
	fbreqd_2 $f class B $.
	fbreqd_3 $f class C $.
	fbreqd_4 $f class D $.
	ebreqd_0 $e |- ( ph -> A = B ) $.
	breqd $p |- ( ph -> ( C A D <-> C B D ) ) $= fbreqd_0 fbreqd_1 fbreqd_2 wceq fbreqd_3 fbreqd_4 fbreqd_1 wbr fbreqd_3 fbreqd_4 fbreqd_2 wbr wb ebreqd_0 fbreqd_3 fbreqd_4 fbreqd_1 fbreqd_2 breq syl $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreq2d_0 $f wff ph $.
	fbreq2d_1 $f class A $.
	fbreq2d_2 $f class B $.
	fbreq2d_3 $f class C $.
	fbreq2d_4 $f class R $.
	ebreq2d_0 $e |- ( ph -> A = B ) $.
	breq2d $p |- ( ph -> ( C R A <-> C R B ) ) $= fbreq2d_0 fbreq2d_1 fbreq2d_2 wceq fbreq2d_3 fbreq2d_1 fbreq2d_4 wbr fbreq2d_3 fbreq2d_2 fbreq2d_4 wbr wb ebreq2d_0 fbreq2d_1 fbreq2d_2 fbreq2d_3 fbreq2d_4 breq2 syl $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	fbreq12d_0 $f wff ph $.
	fbreq12d_1 $f class A $.
	fbreq12d_2 $f class B $.
	fbreq12d_3 $f class C $.
	fbreq12d_4 $f class D $.
	fbreq12d_5 $f class R $.
	ebreq12d_0 $e |- ( ph -> A = B ) $.
	ebreq12d_1 $e |- ( ph -> C = D ) $.
	breq12d $p |- ( ph -> ( A R C <-> B R D ) ) $= fbreq12d_0 fbreq12d_1 fbreq12d_2 wceq fbreq12d_3 fbreq12d_4 wceq fbreq12d_1 fbreq12d_3 fbreq12d_5 wbr fbreq12d_2 fbreq12d_4 fbreq12d_5 wbr wb ebreq12d_0 ebreq12d_1 fbreq12d_1 fbreq12d_2 fbreq12d_3 fbreq12d_4 fbreq12d_5 breq12 syl2anc $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
         29-Oct-2011.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$v S $.
	fbreq123d_0 $f wff ph $.
	fbreq123d_1 $f class A $.
	fbreq123d_2 $f class B $.
	fbreq123d_3 $f class C $.
	fbreq123d_4 $f class D $.
	fbreq123d_5 $f class R $.
	fbreq123d_6 $f class S $.
	ebreq123d_0 $e |- ( ph -> A = B ) $.
	ebreq123d_1 $e |- ( ph -> R = S ) $.
	ebreq123d_2 $e |- ( ph -> C = D ) $.
	breq123d $p |- ( ph -> ( A R C <-> B S D ) ) $= fbreq123d_0 fbreq123d_1 fbreq123d_3 fbreq123d_5 wbr fbreq123d_2 fbreq123d_4 fbreq123d_5 wbr fbreq123d_2 fbreq123d_4 fbreq123d_6 wbr fbreq123d_0 fbreq123d_1 fbreq123d_2 fbreq123d_3 fbreq123d_4 fbreq123d_5 ebreq123d_0 ebreq123d_2 breq12d fbreq123d_0 fbreq123d_5 fbreq123d_6 fbreq123d_2 fbreq123d_4 ebreq123d_1 breqd bitrd $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	fbreqan12d_0 $f wff ph $.
	fbreqan12d_1 $f wff ps $.
	fbreqan12d_2 $f class A $.
	fbreqan12d_3 $f class B $.
	fbreqan12d_4 $f class C $.
	fbreqan12d_5 $f class D $.
	fbreqan12d_6 $f class R $.
	ebreqan12d_0 $e |- ( ph -> A = B ) $.
	ebreqan12d_1 $e |- ( ps -> C = D ) $.
	breqan12d $p |- ( ( ph /\ ps ) -> ( A R C <-> B R D ) ) $= fbreqan12d_0 fbreqan12d_2 fbreqan12d_3 wceq fbreqan12d_4 fbreqan12d_5 wceq fbreqan12d_2 fbreqan12d_4 fbreqan12d_6 wbr fbreqan12d_3 fbreqan12d_5 fbreqan12d_6 wbr wb fbreqan12d_1 ebreqan12d_0 ebreqan12d_1 fbreqan12d_2 fbreqan12d_3 fbreqan12d_4 fbreqan12d_5 fbreqan12d_6 breq12 syl2an $.
$}
$( Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.) $)
${
	$v ph $.
	$v ps $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	fbreqan12rd_0 $f wff ph $.
	fbreqan12rd_1 $f wff ps $.
	fbreqan12rd_2 $f class A $.
	fbreqan12rd_3 $f class B $.
	fbreqan12rd_4 $f class C $.
	fbreqan12rd_5 $f class D $.
	fbreqan12rd_6 $f class R $.
	ebreqan12rd_0 $e |- ( ph -> A = B ) $.
	ebreqan12rd_1 $e |- ( ps -> C = D ) $.
	breqan12rd $p |- ( ( ps /\ ph ) -> ( A R C <-> B R D ) ) $= fbreqan12rd_0 fbreqan12rd_1 fbreqan12rd_2 fbreqan12rd_4 fbreqan12rd_6 wbr fbreqan12rd_3 fbreqan12rd_5 fbreqan12rd_6 wbr wb fbreqan12rd_0 fbreqan12rd_1 fbreqan12rd_2 fbreqan12rd_3 fbreqan12rd_4 fbreqan12rd_5 fbreqan12rd_6 ebreqan12rd_0 ebreqan12rd_1 breqan12d ancoms $.
$}
$( Two classes are different if they don't have the same relationship to a
     third class.  (Contributed by NM, 3-Jun-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fnbrne1_0 $f class A $.
	fnbrne1_1 $f class B $.
	fnbrne1_2 $f class C $.
	fnbrne1_3 $f class R $.
	nbrne1 $p |- ( ( A R B /\ -. A R C ) -> B =/= C ) $= fnbrne1_0 fnbrne1_1 fnbrne1_3 wbr fnbrne1_0 fnbrne1_2 fnbrne1_3 wbr wn fnbrne1_1 fnbrne1_2 wne fnbrne1_0 fnbrne1_1 fnbrne1_3 wbr fnbrne1_0 fnbrne1_2 fnbrne1_3 wbr fnbrne1_1 fnbrne1_2 fnbrne1_1 fnbrne1_2 wceq fnbrne1_0 fnbrne1_1 fnbrne1_3 wbr fnbrne1_0 fnbrne1_2 fnbrne1_3 wbr fnbrne1_1 fnbrne1_2 fnbrne1_0 fnbrne1_3 breq2 biimpcd necon3bd imp $.
$}
$( Two classes are different if they don't have the same relationship to a
     third class.  (Contributed by NM, 3-Jun-2012.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fnbrne2_0 $f class A $.
	fnbrne2_1 $f class B $.
	fnbrne2_2 $f class C $.
	fnbrne2_3 $f class R $.
	nbrne2 $p |- ( ( A R C /\ -. B R C ) -> A =/= B ) $= fnbrne2_0 fnbrne2_2 fnbrne2_3 wbr fnbrne2_1 fnbrne2_2 fnbrne2_3 wbr wn fnbrne2_0 fnbrne2_1 wne fnbrne2_0 fnbrne2_2 fnbrne2_3 wbr fnbrne2_1 fnbrne2_2 fnbrne2_3 wbr fnbrne2_0 fnbrne2_1 fnbrne2_0 fnbrne2_1 wceq fnbrne2_0 fnbrne2_2 fnbrne2_3 wbr fnbrne2_1 fnbrne2_2 fnbrne2_3 wbr fnbrne2_0 fnbrne2_1 fnbrne2_2 fnbrne2_3 breq1 biimpcd necon3bd imp $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	feqbrtri_0 $f class A $.
	feqbrtri_1 $f class B $.
	feqbrtri_2 $f class C $.
	feqbrtri_3 $f class R $.
	eeqbrtri_0 $e |- A = B $.
	eeqbrtri_1 $e |- B R C $.
	eqbrtri $p |- A R C $= feqbrtri_0 feqbrtri_2 feqbrtri_3 wbr feqbrtri_1 feqbrtri_2 feqbrtri_3 wbr eeqbrtri_1 feqbrtri_0 feqbrtri_1 feqbrtri_2 feqbrtri_3 eeqbrtri_0 breq1i mpbir $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 8-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	feqbrtrd_0 $f wff ph $.
	feqbrtrd_1 $f class A $.
	feqbrtrd_2 $f class B $.
	feqbrtrd_3 $f class C $.
	feqbrtrd_4 $f class R $.
	eeqbrtrd_0 $e |- ( ph -> A = B ) $.
	eeqbrtrd_1 $e |- ( ph -> B R C ) $.
	eqbrtrd $p |- ( ph -> A R C ) $= feqbrtrd_0 feqbrtrd_1 feqbrtrd_3 feqbrtrd_4 wbr feqbrtrd_2 feqbrtrd_3 feqbrtrd_4 wbr eeqbrtrd_1 feqbrtrd_0 feqbrtrd_1 feqbrtrd_2 feqbrtrd_3 feqbrtrd_4 eeqbrtrd_0 breq1d mpbird $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	feqbrtrri_0 $f class A $.
	feqbrtrri_1 $f class B $.
	feqbrtrri_2 $f class C $.
	feqbrtrri_3 $f class R $.
	eeqbrtrri_0 $e |- A = B $.
	eeqbrtrri_1 $e |- A R C $.
	eqbrtrri $p |- B R C $= feqbrtrri_1 feqbrtrri_0 feqbrtrri_2 feqbrtrri_3 feqbrtrri_0 feqbrtrri_1 eeqbrtrri_0 eqcomi eeqbrtrri_1 eqbrtri $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	feqbrtrrd_0 $f wff ph $.
	feqbrtrrd_1 $f class A $.
	feqbrtrrd_2 $f class B $.
	feqbrtrrd_3 $f class C $.
	feqbrtrrd_4 $f class R $.
	eeqbrtrrd_0 $e |- ( ph -> A = B ) $.
	eeqbrtrrd_1 $e |- ( ph -> A R C ) $.
	eqbrtrrd $p |- ( ph -> B R C ) $= feqbrtrrd_0 feqbrtrrd_2 feqbrtrrd_1 feqbrtrrd_3 feqbrtrrd_4 feqbrtrrd_0 feqbrtrrd_1 feqbrtrrd_2 eeqbrtrrd_0 eqcomd eeqbrtrrd_1 eqbrtrd $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreqtri_0 $f class A $.
	fbreqtri_1 $f class B $.
	fbreqtri_2 $f class C $.
	fbreqtri_3 $f class R $.
	ebreqtri_0 $e |- A R B $.
	ebreqtri_1 $e |- B = C $.
	breqtri $p |- A R C $= fbreqtri_0 fbreqtri_1 fbreqtri_3 wbr fbreqtri_0 fbreqtri_2 fbreqtri_3 wbr ebreqtri_0 fbreqtri_1 fbreqtri_2 fbreqtri_0 fbreqtri_3 ebreqtri_1 breq2i mpbi $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreqtrd_0 $f wff ph $.
	fbreqtrd_1 $f class A $.
	fbreqtrd_2 $f class B $.
	fbreqtrd_3 $f class C $.
	fbreqtrd_4 $f class R $.
	ebreqtrd_0 $e |- ( ph -> A R B ) $.
	ebreqtrd_1 $e |- ( ph -> B = C ) $.
	breqtrd $p |- ( ph -> A R C ) $= fbreqtrd_0 fbreqtrd_1 fbreqtrd_2 fbreqtrd_4 wbr fbreqtrd_1 fbreqtrd_3 fbreqtrd_4 wbr ebreqtrd_0 fbreqtrd_0 fbreqtrd_2 fbreqtrd_3 fbreqtrd_1 fbreqtrd_4 ebreqtrd_1 breq2d mpbid $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreqtrri_0 $f class A $.
	fbreqtrri_1 $f class B $.
	fbreqtrri_2 $f class C $.
	fbreqtrri_3 $f class R $.
	ebreqtrri_0 $e |- A R B $.
	ebreqtrri_1 $e |- C = B $.
	breqtrri $p |- A R C $= fbreqtrri_0 fbreqtrri_1 fbreqtrri_2 fbreqtrri_3 ebreqtrri_0 fbreqtrri_2 fbreqtrri_1 ebreqtrri_1 eqcomi breqtri $.
$}
$( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fbreqtrrd_0 $f wff ph $.
	fbreqtrrd_1 $f class A $.
	fbreqtrrd_2 $f class B $.
	fbreqtrrd_3 $f class C $.
	fbreqtrrd_4 $f class R $.
	ebreqtrrd_0 $e |- ( ph -> A R B ) $.
	ebreqtrrd_1 $e |- ( ph -> C = B ) $.
	breqtrrd $p |- ( ph -> A R C ) $= fbreqtrrd_0 fbreqtrrd_1 fbreqtrrd_2 fbreqtrrd_3 fbreqtrrd_4 ebreqtrrd_0 fbreqtrrd_0 fbreqtrrd_3 fbreqtrrd_2 ebreqtrrd_1 eqcomd breqtrd $.
$}
$( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 11-Aug-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	f3brtr3i_0 $f class A $.
	f3brtr3i_1 $f class B $.
	f3brtr3i_2 $f class C $.
	f3brtr3i_3 $f class D $.
	f3brtr3i_4 $f class R $.
	e3brtr3i_0 $e |- A R B $.
	e3brtr3i_1 $e |- A = C $.
	e3brtr3i_2 $e |- B = D $.
	3brtr3i $p |- C R D $= f3brtr3i_2 f3brtr3i_1 f3brtr3i_3 f3brtr3i_4 f3brtr3i_0 f3brtr3i_2 f3brtr3i_1 f3brtr3i_4 e3brtr3i_1 e3brtr3i_0 eqbrtrri e3brtr3i_2 breqtri $.
$}
$( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 11-Aug-1999.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	f3brtr4i_0 $f class A $.
	f3brtr4i_1 $f class B $.
	f3brtr4i_2 $f class C $.
	f3brtr4i_3 $f class D $.
	f3brtr4i_4 $f class R $.
	e3brtr4i_0 $e |- A R B $.
	e3brtr4i_1 $e |- C = A $.
	e3brtr4i_2 $e |- D = B $.
	3brtr4i $p |- C R D $= f3brtr4i_2 f3brtr4i_1 f3brtr4i_3 f3brtr4i_4 f3brtr4i_2 f3brtr4i_0 f3brtr4i_1 f3brtr4i_4 e3brtr4i_1 e3brtr4i_0 eqbrtri e3brtr4i_2 breqtrri $.
$}
$( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 18-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	f3brtr3d_0 $f wff ph $.
	f3brtr3d_1 $f class A $.
	f3brtr3d_2 $f class B $.
	f3brtr3d_3 $f class C $.
	f3brtr3d_4 $f class D $.
	f3brtr3d_5 $f class R $.
	e3brtr3d_0 $e |- ( ph -> A R B ) $.
	e3brtr3d_1 $e |- ( ph -> A = C ) $.
	e3brtr3d_2 $e |- ( ph -> B = D ) $.
	3brtr3d $p |- ( ph -> C R D ) $= f3brtr3d_0 f3brtr3d_1 f3brtr3d_2 f3brtr3d_5 wbr f3brtr3d_3 f3brtr3d_4 f3brtr3d_5 wbr e3brtr3d_0 f3brtr3d_0 f3brtr3d_1 f3brtr3d_3 f3brtr3d_2 f3brtr3d_4 f3brtr3d_5 e3brtr3d_1 e3brtr3d_2 breq12d mpbid $.
$}
$( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 21-Feb-2005.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	f3brtr4d_0 $f wff ph $.
	f3brtr4d_1 $f class A $.
	f3brtr4d_2 $f class B $.
	f3brtr4d_3 $f class C $.
	f3brtr4d_4 $f class D $.
	f3brtr4d_5 $f class R $.
	e3brtr4d_0 $e |- ( ph -> A R B ) $.
	e3brtr4d_1 $e |- ( ph -> C = A ) $.
	e3brtr4d_2 $e |- ( ph -> D = B ) $.
	3brtr4d $p |- ( ph -> C R D ) $= f3brtr4d_0 f3brtr4d_3 f3brtr4d_4 f3brtr4d_5 wbr f3brtr4d_1 f3brtr4d_2 f3brtr4d_5 wbr e3brtr4d_0 f3brtr4d_0 f3brtr4d_3 f3brtr4d_1 f3brtr4d_4 f3brtr4d_2 f3brtr4d_5 e3brtr4d_1 e3brtr4d_2 breq12d mpbird $.
$}
$( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 16-Jan-1997.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	f3brtr3g_0 $f wff ph $.
	f3brtr3g_1 $f class A $.
	f3brtr3g_2 $f class B $.
	f3brtr3g_3 $f class C $.
	f3brtr3g_4 $f class D $.
	f3brtr3g_5 $f class R $.
	e3brtr3g_0 $e |- ( ph -> A R B ) $.
	e3brtr3g_1 $e |- A = C $.
	e3brtr3g_2 $e |- B = D $.
	3brtr3g $p |- ( ph -> C R D ) $= f3brtr3g_0 f3brtr3g_1 f3brtr3g_2 f3brtr3g_5 wbr f3brtr3g_3 f3brtr3g_4 f3brtr3g_5 wbr e3brtr3g_0 f3brtr3g_1 f3brtr3g_3 f3brtr3g_2 f3brtr3g_4 f3brtr3g_5 e3brtr3g_1 e3brtr3g_2 breq12i sylib $.
$}
$( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 16-Jan-1997.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	f3brtr4g_0 $f wff ph $.
	f3brtr4g_1 $f class A $.
	f3brtr4g_2 $f class B $.
	f3brtr4g_3 $f class C $.
	f3brtr4g_4 $f class D $.
	f3brtr4g_5 $f class R $.
	e3brtr4g_0 $e |- ( ph -> A R B ) $.
	e3brtr4g_1 $e |- C = A $.
	e3brtr4g_2 $e |- D = B $.
	3brtr4g $p |- ( ph -> C R D ) $= f3brtr4g_0 f3brtr4g_1 f3brtr4g_2 f3brtr4g_5 wbr f3brtr4g_3 f3brtr4g_4 f3brtr4g_5 wbr e3brtr4g_0 f3brtr4g_3 f3brtr4g_1 f3brtr4g_4 f3brtr4g_2 f3brtr4g_5 e3brtr4g_1 e3brtr4g_2 breq12i sylibr $.
$}
$( B chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl5eqbr_0 $f wff ph $.
	fsyl5eqbr_1 $f class A $.
	fsyl5eqbr_2 $f class B $.
	fsyl5eqbr_3 $f class C $.
	fsyl5eqbr_4 $f class R $.
	esyl5eqbr_0 $e |- A = B $.
	esyl5eqbr_1 $e |- ( ph -> B R C ) $.
	syl5eqbr $p |- ( ph -> A R C ) $= fsyl5eqbr_0 fsyl5eqbr_2 fsyl5eqbr_3 fsyl5eqbr_1 fsyl5eqbr_3 fsyl5eqbr_4 esyl5eqbr_1 esyl5eqbr_0 fsyl5eqbr_3 eqid 3brtr4g $.
$}
$( B chained equality inference for a binary relation.  (Contributed by NM,
       17-Sep-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl5eqbrr_0 $f wff ph $.
	fsyl5eqbrr_1 $f class A $.
	fsyl5eqbrr_2 $f class B $.
	fsyl5eqbrr_3 $f class C $.
	fsyl5eqbrr_4 $f class R $.
	esyl5eqbrr_0 $e |- B = A $.
	esyl5eqbrr_1 $e |- ( ph -> B R C ) $.
	syl5eqbrr $p |- ( ph -> A R C ) $= fsyl5eqbrr_0 fsyl5eqbrr_2 fsyl5eqbrr_3 fsyl5eqbrr_1 fsyl5eqbrr_3 fsyl5eqbrr_4 esyl5eqbrr_1 esyl5eqbrr_0 fsyl5eqbrr_3 eqid 3brtr3g $.
$}
$( B chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl5breq_0 $f wff ph $.
	fsyl5breq_1 $f class A $.
	fsyl5breq_2 $f class B $.
	fsyl5breq_3 $f class C $.
	fsyl5breq_4 $f class R $.
	esyl5breq_0 $e |- A R B $.
	esyl5breq_1 $e |- ( ph -> B = C ) $.
	syl5breq $p |- ( ph -> A R C ) $= fsyl5breq_0 fsyl5breq_1 fsyl5breq_2 fsyl5breq_3 fsyl5breq_4 fsyl5breq_1 fsyl5breq_2 fsyl5breq_4 wbr fsyl5breq_0 esyl5breq_0 a1i esyl5breq_1 breqtrd $.
$}
$( B chained equality inference for a binary relation.  (Contributed by NM,
       24-Apr-2005.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl5breqr_0 $f wff ph $.
	fsyl5breqr_1 $f class A $.
	fsyl5breqr_2 $f class B $.
	fsyl5breqr_3 $f class C $.
	fsyl5breqr_4 $f class R $.
	esyl5breqr_0 $e |- A R B $.
	esyl5breqr_1 $e |- ( ph -> C = B ) $.
	syl5breqr $p |- ( ph -> A R C ) $= fsyl5breqr_0 fsyl5breqr_1 fsyl5breqr_2 fsyl5breqr_3 fsyl5breqr_4 esyl5breqr_0 fsyl5breqr_0 fsyl5breqr_3 fsyl5breqr_2 esyl5breqr_1 eqcomd syl5breq $.
$}
$( A chained equality inference for a binary relation.  (Contributed by NM,
       12-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl6eqbr_0 $f wff ph $.
	fsyl6eqbr_1 $f class A $.
	fsyl6eqbr_2 $f class B $.
	fsyl6eqbr_3 $f class C $.
	fsyl6eqbr_4 $f class R $.
	esyl6eqbr_0 $e |- ( ph -> A = B ) $.
	esyl6eqbr_1 $e |- B R C $.
	syl6eqbr $p |- ( ph -> A R C ) $= fsyl6eqbr_0 fsyl6eqbr_1 fsyl6eqbr_3 fsyl6eqbr_4 wbr fsyl6eqbr_2 fsyl6eqbr_3 fsyl6eqbr_4 wbr esyl6eqbr_1 fsyl6eqbr_0 fsyl6eqbr_1 fsyl6eqbr_2 fsyl6eqbr_3 fsyl6eqbr_4 esyl6eqbr_0 breq1d mpbiri $.
$}
$( A chained equality inference for a binary relation.  (Contributed by NM,
       4-Jan-2006.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl6eqbrr_0 $f wff ph $.
	fsyl6eqbrr_1 $f class A $.
	fsyl6eqbrr_2 $f class B $.
	fsyl6eqbrr_3 $f class C $.
	fsyl6eqbrr_4 $f class R $.
	esyl6eqbrr_0 $e |- ( ph -> B = A ) $.
	esyl6eqbrr_1 $e |- B R C $.
	syl6eqbrr $p |- ( ph -> A R C ) $= fsyl6eqbrr_0 fsyl6eqbrr_1 fsyl6eqbrr_2 fsyl6eqbrr_3 fsyl6eqbrr_4 fsyl6eqbrr_0 fsyl6eqbrr_2 fsyl6eqbrr_1 esyl6eqbrr_0 eqcomd esyl6eqbrr_1 syl6eqbr $.
$}
$( A chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl6breq_0 $f wff ph $.
	fsyl6breq_1 $f class A $.
	fsyl6breq_2 $f class B $.
	fsyl6breq_3 $f class C $.
	fsyl6breq_4 $f class R $.
	esyl6breq_0 $e |- ( ph -> A R B ) $.
	esyl6breq_1 $e |- B = C $.
	syl6breq $p |- ( ph -> A R C ) $= fsyl6breq_0 fsyl6breq_1 fsyl6breq_2 fsyl6breq_1 fsyl6breq_3 fsyl6breq_4 esyl6breq_0 fsyl6breq_1 eqid esyl6breq_1 3brtr3g $.
$}
$( A chained equality inference for a binary relation.  (Contributed by NM,
       24-Apr-2005.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v R $.
	fsyl6breqr_0 $f wff ph $.
	fsyl6breqr_1 $f class A $.
	fsyl6breqr_2 $f class B $.
	fsyl6breqr_3 $f class C $.
	fsyl6breqr_4 $f class R $.
	esyl6breqr_0 $e |- ( ph -> A R B ) $.
	esyl6breqr_1 $e |- C = B $.
	syl6breqr $p |- ( ph -> A R C ) $= fsyl6breqr_0 fsyl6breqr_1 fsyl6breqr_2 fsyl6breqr_3 fsyl6breqr_4 esyl6breqr_0 fsyl6breqr_3 fsyl6breqr_2 esyl6breqr_1 eqcomi syl6breq $.
$}
$( Deduction from a subclass relationship of binary relations.
       (Contributed by NM, 30-Apr-2004.) $)
${
	$v ph $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fssbrd_0 $f wff ph $.
	fssbrd_1 $f class A $.
	fssbrd_2 $f class B $.
	fssbrd_3 $f class C $.
	fssbrd_4 $f class D $.
	essbrd_0 $e |- ( ph -> A C_ B ) $.
	ssbrd $p |- ( ph -> ( C A D -> C B D ) ) $= fssbrd_0 fssbrd_3 fssbrd_4 cop fssbrd_1 wcel fssbrd_3 fssbrd_4 cop fssbrd_2 wcel fssbrd_3 fssbrd_4 fssbrd_1 wbr fssbrd_3 fssbrd_4 fssbrd_2 wbr fssbrd_0 fssbrd_1 fssbrd_2 fssbrd_3 fssbrd_4 cop essbrd_0 sseld fssbrd_3 fssbrd_4 fssbrd_1 df-br fssbrd_3 fssbrd_4 fssbrd_2 df-br 3imtr4g $.
$}
$( Inference from a subclass relationship of binary relations.
       (Contributed by NM, 28-Mar-2007.)  (Revised by Mario Carneiro,
       8-Feb-2015.) $)
${
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	fssbri_0 $f class A $.
	fssbri_1 $f class B $.
	fssbri_2 $f class C $.
	fssbri_3 $f class D $.
	essbri_0 $e |- A C_ B $.
	ssbri $p |- ( C A D -> C B D ) $= fssbri_2 fssbri_3 fssbri_0 wbr fssbri_2 fssbri_3 fssbri_1 wbr wi wtru fssbri_0 fssbri_1 fssbri_2 fssbri_3 fssbri_0 fssbri_1 wss wtru essbri_0 a1i ssbrd trud $.
$}
$( Deduction version of bound-variable hypothesis builder ~ nfbr .
       (Contributed by NM, 13-Dec-2005.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
${
	$v ph $.
	$v x $.
	$v A $.
	$v B $.
	$v R $.
	fnfbrd_0 $f wff ph $.
	fnfbrd_1 $f set x $.
	fnfbrd_2 $f class A $.
	fnfbrd_3 $f class B $.
	fnfbrd_4 $f class R $.
	enfbrd_0 $e |- ( ph -> F/_ x A ) $.
	enfbrd_1 $e |- ( ph -> F/_ x R ) $.
	enfbrd_2 $e |- ( ph -> F/_ x B ) $.
	nfbrd $p |- ( ph -> F/ x A R B ) $= fnfbrd_2 fnfbrd_3 fnfbrd_4 wbr fnfbrd_2 fnfbrd_3 cop fnfbrd_4 wcel fnfbrd_0 fnfbrd_1 fnfbrd_2 fnfbrd_3 fnfbrd_4 df-br fnfbrd_0 fnfbrd_1 fnfbrd_2 fnfbrd_3 cop fnfbrd_4 fnfbrd_0 fnfbrd_1 fnfbrd_2 fnfbrd_3 enfbrd_0 enfbrd_2 nfopd enfbrd_1 nfeld nfxfrd $.
$}
$( Bound-variable hypothesis builder for binary relation.  (Contributed by
       NM, 1-Sep-1999.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v R $.
	fnfbr_0 $f set x $.
	fnfbr_1 $f class A $.
	fnfbr_2 $f class B $.
	fnfbr_3 $f class R $.
	enfbr_0 $e |- F/_ x A $.
	enfbr_1 $e |- F/_ x R $.
	enfbr_2 $e |- F/_ x B $.
	nfbr $p |- F/ x A R B $= fnfbr_1 fnfbr_2 fnfbr_3 wbr fnfbr_0 wnf wtru fnfbr_0 fnfbr_1 fnfbr_2 fnfbr_3 fnfbr_0 fnfbr_1 wnfc wtru enfbr_0 a1i fnfbr_0 fnfbr_3 wnfc wtru enfbr_1 a1i fnfbr_0 fnfbr_2 wnfc wtru enfbr_2 a1i nfbrd trud $.
$}
$( Relationship between a binary relation and a class abstraction.
       (Contributed by Andrew Salmon, 8-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$v A $.
	$v R $.
	$d x y $.
	$d y z A $.
	$d y z R $.
	ibrab1_0 $f set y $.
	fbrab1_0 $f set x $.
	fbrab1_1 $f set z $.
	fbrab1_2 $f class A $.
	fbrab1_3 $f class R $.
	brab1 $p |- ( x R A <-> x e. { z | z R A } ) $= fbrab1_0 cv fbrab1_2 fbrab1_3 wbr fbrab1_1 cv fbrab1_2 fbrab1_3 wbr fbrab1_1 fbrab1_0 cv wsbc fbrab1_0 cv fbrab1_1 cv fbrab1_2 fbrab1_3 wbr fbrab1_1 cab wcel fbrab1_0 cv cvv wcel fbrab1_1 cv fbrab1_2 fbrab1_3 wbr fbrab1_1 fbrab1_0 cv wsbc fbrab1_0 cv fbrab1_2 fbrab1_3 wbr wb fbrab1_0 vex fbrab1_1 cv fbrab1_2 fbrab1_3 wbr ibrab1_0 cv fbrab1_2 fbrab1_3 wbr fbrab1_0 cv fbrab1_2 fbrab1_3 wbr fbrab1_1 ibrab1_0 fbrab1_0 cv cvv fbrab1_1 cv ibrab1_0 cv fbrab1_2 fbrab1_3 breq1 ibrab1_0 cv fbrab1_0 cv fbrab1_2 fbrab1_3 breq1 sbcie2g ax-mp fbrab1_1 cv fbrab1_2 fbrab1_3 wbr fbrab1_1 fbrab1_0 cv df-sbc bitr3i $.
$}
$( The union of two binary relations.  (Contributed by NM, 21-Dec-2008.) $)
${
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	fbrun_0 $f class A $.
	fbrun_1 $f class B $.
	fbrun_2 $f class R $.
	fbrun_3 $f class S $.
	brun $p |- ( A ( R u. S ) B <-> ( A R B \/ A S B ) ) $= fbrun_0 fbrun_1 cop fbrun_2 fbrun_3 cun wcel fbrun_0 fbrun_1 cop fbrun_2 wcel fbrun_0 fbrun_1 cop fbrun_3 wcel wo fbrun_0 fbrun_1 fbrun_2 fbrun_3 cun wbr fbrun_0 fbrun_1 fbrun_2 wbr fbrun_0 fbrun_1 fbrun_3 wbr wo fbrun_0 fbrun_1 cop fbrun_2 fbrun_3 elun fbrun_0 fbrun_1 fbrun_2 fbrun_3 cun df-br fbrun_0 fbrun_1 fbrun_2 wbr fbrun_0 fbrun_1 cop fbrun_2 wcel fbrun_0 fbrun_1 fbrun_3 wbr fbrun_0 fbrun_1 cop fbrun_3 wcel fbrun_0 fbrun_1 fbrun_2 df-br fbrun_0 fbrun_1 fbrun_3 df-br orbi12i 3bitr4i $.
$}
$( The intersection of two relations.  (Contributed by FL, 7-Oct-2008.) $)
${
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	fbrin_0 $f class A $.
	fbrin_1 $f class B $.
	fbrin_2 $f class R $.
	fbrin_3 $f class S $.
	brin $p |- ( A ( R i^i S ) B <-> ( A R B /\ A S B ) ) $= fbrin_0 fbrin_1 cop fbrin_2 fbrin_3 cin wcel fbrin_0 fbrin_1 cop fbrin_2 wcel fbrin_0 fbrin_1 cop fbrin_3 wcel wa fbrin_0 fbrin_1 fbrin_2 fbrin_3 cin wbr fbrin_0 fbrin_1 fbrin_2 wbr fbrin_0 fbrin_1 fbrin_3 wbr wa fbrin_0 fbrin_1 cop fbrin_2 fbrin_3 elin fbrin_0 fbrin_1 fbrin_2 fbrin_3 cin df-br fbrin_0 fbrin_1 fbrin_2 wbr fbrin_0 fbrin_1 cop fbrin_2 wcel fbrin_0 fbrin_1 fbrin_3 wbr fbrin_0 fbrin_1 cop fbrin_3 wcel fbrin_0 fbrin_1 fbrin_2 df-br fbrin_0 fbrin_1 fbrin_3 df-br anbi12i 3bitr4i $.
$}
$( The difference of two binary relations.  (Contributed by Scott Fenton,
     11-Apr-2011.) $)
${
	$v A $.
	$v B $.
	$v R $.
	$v S $.
	fbrdif_0 $f class A $.
	fbrdif_1 $f class B $.
	fbrdif_2 $f class R $.
	fbrdif_3 $f class S $.
	brdif $p |- ( A ( R \ S ) B <-> ( A R B /\ -. A S B ) ) $= fbrdif_0 fbrdif_1 cop fbrdif_2 fbrdif_3 cdif wcel fbrdif_0 fbrdif_1 cop fbrdif_2 wcel fbrdif_0 fbrdif_1 cop fbrdif_3 wcel wn wa fbrdif_0 fbrdif_1 fbrdif_2 fbrdif_3 cdif wbr fbrdif_0 fbrdif_1 fbrdif_2 wbr fbrdif_0 fbrdif_1 fbrdif_3 wbr wn wa fbrdif_0 fbrdif_1 cop fbrdif_2 fbrdif_3 eldif fbrdif_0 fbrdif_1 fbrdif_2 fbrdif_3 cdif df-br fbrdif_0 fbrdif_1 fbrdif_2 wbr fbrdif_0 fbrdif_1 cop fbrdif_2 wcel fbrdif_0 fbrdif_1 fbrdif_3 wbr wn fbrdif_0 fbrdif_1 cop fbrdif_3 wcel wn fbrdif_0 fbrdif_1 fbrdif_2 df-br fbrdif_0 fbrdif_1 fbrdif_3 wbr fbrdif_0 fbrdif_1 cop fbrdif_3 wcel fbrdif_0 fbrdif_1 fbrdif_3 df-br notbii anbi12i 3bitr4i $.
$}
$( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
${
	$v x $.
	$v y $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$d y A $.
	$d y B $.
	$d y C $.
	$d y D $.
	$d y R $.
	$d x y $.
	isbcbrg_0 $f set y $.
	fsbcbrg_0 $f set x $.
	fsbcbrg_1 $f class A $.
	fsbcbrg_2 $f class B $.
	fsbcbrg_3 $f class C $.
	fsbcbrg_4 $f class D $.
	fsbcbrg_5 $f class R $.
	sbcbrg $p |- ( A e. D -> ( [. A / x ]. B R C <-> [_ A / x ]_ B [_ A / x ]_ R [_ A / x ]_ C ) ) $= fsbcbrg_2 fsbcbrg_3 fsbcbrg_5 wbr fsbcbrg_0 isbcbrg_0 wsb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 csb wbr fsbcbrg_2 fsbcbrg_3 fsbcbrg_5 wbr fsbcbrg_0 fsbcbrg_1 wsbc fsbcbrg_0 fsbcbrg_1 fsbcbrg_2 csb fsbcbrg_0 fsbcbrg_1 fsbcbrg_3 csb fsbcbrg_0 fsbcbrg_1 fsbcbrg_5 csb wbr isbcbrg_0 fsbcbrg_1 fsbcbrg_4 fsbcbrg_2 fsbcbrg_3 fsbcbrg_5 wbr fsbcbrg_0 isbcbrg_0 fsbcbrg_1 dfsbcq2 isbcbrg_0 cv fsbcbrg_1 wceq fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 csb fsbcbrg_0 fsbcbrg_1 fsbcbrg_2 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 csb fsbcbrg_0 fsbcbrg_1 fsbcbrg_3 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 csb fsbcbrg_0 fsbcbrg_1 fsbcbrg_5 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_1 fsbcbrg_2 csbeq1 fsbcbrg_0 isbcbrg_0 cv fsbcbrg_1 fsbcbrg_5 csbeq1 fsbcbrg_0 isbcbrg_0 cv fsbcbrg_1 fsbcbrg_3 csbeq1 breq123d fsbcbrg_2 fsbcbrg_3 fsbcbrg_5 wbr fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 csb wbr fsbcbrg_0 isbcbrg_0 fsbcbrg_0 fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 nfcsb1v fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 nfcsb1v fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 nfcsb1v nfbr fsbcbrg_0 isbcbrg_0 weq fsbcbrg_2 fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 csb fsbcbrg_3 fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 csb fsbcbrg_5 fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 csb fsbcbrg_0 isbcbrg_0 cv fsbcbrg_2 csbeq1a fsbcbrg_0 isbcbrg_0 cv fsbcbrg_5 csbeq1a fsbcbrg_0 isbcbrg_0 cv fsbcbrg_3 csbeq1a breq123d sbie vtoclbg $.
$}
$( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$d x R $.
	fsbcbr12g_0 $f set x $.
	fsbcbr12g_1 $f class A $.
	fsbcbr12g_2 $f class B $.
	fsbcbr12g_3 $f class C $.
	fsbcbr12g_4 $f class D $.
	fsbcbr12g_5 $f class R $.
	sbcbr12g $p |- ( A e. D -> ( [. A / x ]. B R C <-> [_ A / x ]_ B R [_ A / x ]_ C ) ) $= fsbcbr12g_1 fsbcbr12g_4 wcel fsbcbr12g_2 fsbcbr12g_3 fsbcbr12g_5 wbr fsbcbr12g_0 fsbcbr12g_1 wsbc fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_2 csb fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_3 csb fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_5 csb wbr fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_2 csb fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_3 csb fsbcbr12g_5 wbr fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_2 fsbcbr12g_3 fsbcbr12g_4 fsbcbr12g_5 sbcbrg fsbcbr12g_1 fsbcbr12g_4 wcel fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_5 csb fsbcbr12g_5 fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_2 csb fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_3 csb fsbcbr12g_0 fsbcbr12g_1 fsbcbr12g_5 fsbcbr12g_4 csbconstg breqd bitrd $.
$}
$( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$d x C $.
	$d x R $.
	fsbcbr1g_0 $f set x $.
	fsbcbr1g_1 $f class A $.
	fsbcbr1g_2 $f class B $.
	fsbcbr1g_3 $f class C $.
	fsbcbr1g_4 $f class D $.
	fsbcbr1g_5 $f class R $.
	sbcbr1g $p |- ( A e. D -> ( [. A / x ]. B R C <-> [_ A / x ]_ B R C ) ) $= fsbcbr1g_1 fsbcbr1g_4 wcel fsbcbr1g_2 fsbcbr1g_3 fsbcbr1g_5 wbr fsbcbr1g_0 fsbcbr1g_1 wsbc fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_2 csb fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_3 csb fsbcbr1g_5 wbr fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_2 csb fsbcbr1g_3 fsbcbr1g_5 wbr fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_2 fsbcbr1g_3 fsbcbr1g_4 fsbcbr1g_5 sbcbr12g fsbcbr1g_1 fsbcbr1g_4 wcel fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_3 csb fsbcbr1g_3 fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_2 csb fsbcbr1g_5 fsbcbr1g_0 fsbcbr1g_1 fsbcbr1g_3 fsbcbr1g_4 csbconstg breq2d bitrd $.
$}
$( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)
${
	$v x $.
	$v A $.
	$v B $.
	$v C $.
	$v D $.
	$v R $.
	$d x B $.
	$d x R $.
	fsbcbr2g_0 $f set x $.
	fsbcbr2g_1 $f class A $.
	fsbcbr2g_2 $f class B $.
	fsbcbr2g_3 $f class C $.
	fsbcbr2g_4 $f class D $.
	fsbcbr2g_5 $f class R $.
	sbcbr2g $p |- ( A e. D -> ( [. A / x ]. B R C <-> B R [_ A / x ]_ C ) ) $= fsbcbr2g_1 fsbcbr2g_4 wcel fsbcbr2g_2 fsbcbr2g_3 fsbcbr2g_5 wbr fsbcbr2g_0 fsbcbr2g_1 wsbc fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_2 csb fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_3 csb fsbcbr2g_5 wbr fsbcbr2g_2 fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_3 csb fsbcbr2g_5 wbr fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_2 fsbcbr2g_3 fsbcbr2g_4 fsbcbr2g_5 sbcbr12g fsbcbr2g_1 fsbcbr2g_4 wcel fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_2 csb fsbcbr2g_2 fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_3 csb fsbcbr2g_5 fsbcbr2g_0 fsbcbr2g_1 fsbcbr2g_2 fsbcbr2g_4 csbconstg breq1d bitrd $.
$}

