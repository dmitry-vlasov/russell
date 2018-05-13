$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Disjointness.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Binary relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Extend wff notation to include the general binary relation predicate.
     Note that the syntax is simply three class symbols in a row.  Since binary
     relations are the only possible wff expressions consisting of three class
     expressions in a row, the syntax is unambiguous.  (For an example of how
     syntax could become ambiguous if we are not careful, see the comment in
     ~ cneg .) $)

${
	$v A B R  $.
	f0_wbr $f class A $.
	f1_wbr $f class B $.
	f2_wbr $f class R $.
	a_wbr $a wff A R B $.
$}

$(Define a general binary relation.  Note that the syntax is simply three
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
	$v A B R  $.
	f0_df-br $f class A $.
	f1_df-br $f class B $.
	f2_df-br $f class R $.
	a_df-br $a |- ( A R B <-> <. A , B >. e. R ) $.
$}

$(Equality theorem for binary relations.  (Contributed by NM,
     4-Jun-1995.) $)

${
	$v A B R S  $.
	f0_breq $f class A $.
	f1_breq $f class B $.
	f2_breq $f class R $.
	f3_breq $f class S $.
	p_breq $p |- ( R = S -> ( A R B <-> A S B ) ) $= f2_breq f3_breq f0_breq f1_breq a_cop p_eleq2 f0_breq f1_breq f2_breq a_df-br f0_breq f1_breq f3_breq a_df-br f2_breq f3_breq a_wceq f0_breq f1_breq a_cop f2_breq a_wcel f0_breq f1_breq a_cop f3_breq a_wcel f0_breq f1_breq f2_breq a_wbr f0_breq f1_breq f3_breq a_wbr p_3bitr4g $.
$}

$(Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)

${
	$v A B C R  $.
	f0_breq1 $f class A $.
	f1_breq1 $f class B $.
	f2_breq1 $f class C $.
	f3_breq1 $f class R $.
	p_breq1 $p |- ( A = B -> ( A R C <-> B R C ) ) $= f0_breq1 f1_breq1 f2_breq1 p_opeq1 f0_breq1 f1_breq1 a_wceq f0_breq1 f2_breq1 a_cop f1_breq1 f2_breq1 a_cop f3_breq1 p_eleq1d f0_breq1 f2_breq1 f3_breq1 a_df-br f1_breq1 f2_breq1 f3_breq1 a_df-br f0_breq1 f1_breq1 a_wceq f0_breq1 f2_breq1 a_cop f3_breq1 a_wcel f1_breq1 f2_breq1 a_cop f3_breq1 a_wcel f0_breq1 f2_breq1 f3_breq1 a_wbr f1_breq1 f2_breq1 f3_breq1 a_wbr p_3bitr4g $.
$}

$(Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)

${
	$v A B C R  $.
	f0_breq2 $f class A $.
	f1_breq2 $f class B $.
	f2_breq2 $f class C $.
	f3_breq2 $f class R $.
	p_breq2 $p |- ( A = B -> ( C R A <-> C R B ) ) $= f0_breq2 f1_breq2 f2_breq2 p_opeq2 f0_breq2 f1_breq2 a_wceq f2_breq2 f0_breq2 a_cop f2_breq2 f1_breq2 a_cop f3_breq2 p_eleq1d f2_breq2 f0_breq2 f3_breq2 a_df-br f2_breq2 f1_breq2 f3_breq2 a_df-br f0_breq2 f1_breq2 a_wceq f2_breq2 f0_breq2 a_cop f3_breq2 a_wcel f2_breq2 f1_breq2 a_cop f3_breq2 a_wcel f2_breq2 f0_breq2 f3_breq2 a_wbr f2_breq2 f1_breq2 f3_breq2 a_wbr p_3bitr4g $.
$}

$(Equality theorem for a binary relation.  (Contributed by NM,
     8-Feb-1996.) $)

${
	$v A B C D R  $.
	f0_breq12 $f class A $.
	f1_breq12 $f class B $.
	f2_breq12 $f class C $.
	f3_breq12 $f class D $.
	f4_breq12 $f class R $.
	p_breq12 $p |- ( ( A = B /\ C = D ) -> ( A R C <-> B R D ) ) $= f0_breq12 f1_breq12 f2_breq12 f4_breq12 p_breq1 f2_breq12 f3_breq12 f1_breq12 f4_breq12 p_breq2 f0_breq12 f1_breq12 a_wceq f0_breq12 f2_breq12 f4_breq12 a_wbr f1_breq12 f2_breq12 f4_breq12 a_wbr f2_breq12 f3_breq12 a_wceq f1_breq12 f3_breq12 f4_breq12 a_wbr p_sylan9bb $.
$}

$(Equality inference for binary relations.  (Contributed by NM,
       19-Feb-2005.) $)

${
	$v A B R S  $.
	f0_breqi $f class A $.
	f1_breqi $f class B $.
	f2_breqi $f class R $.
	f3_breqi $f class S $.
	e0_breqi $e |- R = S $.
	p_breqi $p |- ( A R B <-> A S B ) $= e0_breqi f0_breqi f1_breqi f2_breqi f3_breqi p_breq f2_breqi f3_breqi a_wceq f0_breqi f1_breqi f2_breqi a_wbr f0_breqi f1_breqi f3_breqi a_wbr a_wb a_ax-mp $.
$}

$(Equality inference for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)

${
	$v A B C R  $.
	f0_breq1i $f class A $.
	f1_breq1i $f class B $.
	f2_breq1i $f class C $.
	f3_breq1i $f class R $.
	e0_breq1i $e |- A = B $.
	p_breq1i $p |- ( A R C <-> B R C ) $= e0_breq1i f0_breq1i f1_breq1i f2_breq1i f3_breq1i p_breq1 f0_breq1i f1_breq1i a_wceq f0_breq1i f2_breq1i f3_breq1i a_wbr f1_breq1i f2_breq1i f3_breq1i a_wbr a_wb a_ax-mp $.
$}

$(Equality inference for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)

${
	$v A B C R  $.
	f0_breq2i $f class A $.
	f1_breq2i $f class B $.
	f2_breq2i $f class C $.
	f3_breq2i $f class R $.
	e0_breq2i $e |- A = B $.
	p_breq2i $p |- ( C R A <-> C R B ) $= e0_breq2i f0_breq2i f1_breq2i f2_breq2i f3_breq2i p_breq2 f0_breq2i f1_breq2i a_wceq f2_breq2i f0_breq2i f3_breq2i a_wbr f2_breq2i f1_breq2i f3_breq2i a_wbr a_wb a_ax-mp $.
$}

$(Equality inference for a binary relation.  (Contributed by NM,
         8-Feb-1996.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)

${
	$v A B C D R  $.
	f0_breq12i $f class A $.
	f1_breq12i $f class B $.
	f2_breq12i $f class C $.
	f3_breq12i $f class D $.
	f4_breq12i $f class R $.
	e0_breq12i $e |- A = B $.
	e1_breq12i $e |- C = D $.
	p_breq12i $p |- ( A R C <-> B R D ) $= e0_breq12i e1_breq12i f0_breq12i f1_breq12i f2_breq12i f3_breq12i f4_breq12i p_breq12 f0_breq12i f1_breq12i a_wceq f2_breq12i f3_breq12i a_wceq f0_breq12i f2_breq12i f4_breq12i a_wbr f1_breq12i f3_breq12i f4_breq12i a_wbr a_wb p_mp2an $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)

${
	$v ph A B C R  $.
	f0_breq1d $f wff ph $.
	f1_breq1d $f class A $.
	f2_breq1d $f class B $.
	f3_breq1d $f class C $.
	f4_breq1d $f class R $.
	e0_breq1d $e |- ( ph -> A = B ) $.
	p_breq1d $p |- ( ph -> ( A R C <-> B R C ) ) $= e0_breq1d f1_breq1d f2_breq1d f3_breq1d f4_breq1d p_breq1 f0_breq1d f1_breq1d f2_breq1d a_wceq f1_breq1d f3_breq1d f4_breq1d a_wbr f2_breq1d f3_breq1d f4_breq1d a_wbr a_wb p_syl $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
       29-Oct-2011.) $)

${
	$v ph A B C D  $.
	f0_breqd $f wff ph $.
	f1_breqd $f class A $.
	f2_breqd $f class B $.
	f3_breqd $f class C $.
	f4_breqd $f class D $.
	e0_breqd $e |- ( ph -> A = B ) $.
	p_breqd $p |- ( ph -> ( C A D <-> C B D ) ) $= e0_breqd f3_breqd f4_breqd f1_breqd f2_breqd p_breq f0_breqd f1_breqd f2_breqd a_wceq f3_breqd f4_breqd f1_breqd a_wbr f3_breqd f4_breqd f2_breqd a_wbr a_wb p_syl $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)

${
	$v ph A B C R  $.
	f0_breq2d $f wff ph $.
	f1_breq2d $f class A $.
	f2_breq2d $f class B $.
	f3_breq2d $f class C $.
	f4_breq2d $f class R $.
	e0_breq2d $e |- ( ph -> A = B ) $.
	p_breq2d $p |- ( ph -> ( C R A <-> C R B ) ) $= e0_breq2d f1_breq2d f2_breq2d f3_breq2d f4_breq2d p_breq2 f0_breq2d f1_breq2d f2_breq2d a_wceq f3_breq2d f1_breq2d f4_breq2d a_wbr f3_breq2d f2_breq2d f4_breq2d a_wbr a_wb p_syl $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v ph A B C D R  $.
	f0_breq12d $f wff ph $.
	f1_breq12d $f class A $.
	f2_breq12d $f class B $.
	f3_breq12d $f class C $.
	f4_breq12d $f class D $.
	f5_breq12d $f class R $.
	e0_breq12d $e |- ( ph -> A = B ) $.
	e1_breq12d $e |- ( ph -> C = D ) $.
	p_breq12d $p |- ( ph -> ( A R C <-> B R D ) ) $= e0_breq12d e1_breq12d f1_breq12d f2_breq12d f3_breq12d f4_breq12d f5_breq12d p_breq12 f0_breq12d f1_breq12d f2_breq12d a_wceq f3_breq12d f4_breq12d a_wceq f1_breq12d f3_breq12d f5_breq12d a_wbr f2_breq12d f4_breq12d f5_breq12d a_wbr a_wb p_syl2anc $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
         29-Oct-2011.) $)

${
	$v ph A B C D R S  $.
	f0_breq123d $f wff ph $.
	f1_breq123d $f class A $.
	f2_breq123d $f class B $.
	f3_breq123d $f class C $.
	f4_breq123d $f class D $.
	f5_breq123d $f class R $.
	f6_breq123d $f class S $.
	e0_breq123d $e |- ( ph -> A = B ) $.
	e1_breq123d $e |- ( ph -> R = S ) $.
	e2_breq123d $e |- ( ph -> C = D ) $.
	p_breq123d $p |- ( ph -> ( A R C <-> B S D ) ) $= e0_breq123d e2_breq123d f0_breq123d f1_breq123d f2_breq123d f3_breq123d f4_breq123d f5_breq123d p_breq12d e1_breq123d f0_breq123d f5_breq123d f6_breq123d f2_breq123d f4_breq123d p_breqd f0_breq123d f1_breq123d f3_breq123d f5_breq123d a_wbr f2_breq123d f4_breq123d f5_breq123d a_wbr f2_breq123d f4_breq123d f6_breq123d a_wbr p_bitrd $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.) $)

${
	$v ph ps A B C D R  $.
	f0_breqan12d $f wff ph $.
	f1_breqan12d $f wff ps $.
	f2_breqan12d $f class A $.
	f3_breqan12d $f class B $.
	f4_breqan12d $f class C $.
	f5_breqan12d $f class D $.
	f6_breqan12d $f class R $.
	e0_breqan12d $e |- ( ph -> A = B ) $.
	e1_breqan12d $e |- ( ps -> C = D ) $.
	p_breqan12d $p |- ( ( ph /\ ps ) -> ( A R C <-> B R D ) ) $= e0_breqan12d e1_breqan12d f2_breqan12d f3_breqan12d f4_breqan12d f5_breqan12d f6_breqan12d p_breq12 f0_breqan12d f2_breqan12d f3_breqan12d a_wceq f4_breqan12d f5_breqan12d a_wceq f2_breqan12d f4_breqan12d f6_breqan12d a_wbr f3_breqan12d f5_breqan12d f6_breqan12d a_wbr a_wb f1_breqan12d p_syl2an $.
$}

$(Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.) $)

${
	$v ph ps A B C D R  $.
	f0_breqan12rd $f wff ph $.
	f1_breqan12rd $f wff ps $.
	f2_breqan12rd $f class A $.
	f3_breqan12rd $f class B $.
	f4_breqan12rd $f class C $.
	f5_breqan12rd $f class D $.
	f6_breqan12rd $f class R $.
	e0_breqan12rd $e |- ( ph -> A = B ) $.
	e1_breqan12rd $e |- ( ps -> C = D ) $.
	p_breqan12rd $p |- ( ( ps /\ ph ) -> ( A R C <-> B R D ) ) $= e0_breqan12rd e1_breqan12rd f0_breqan12rd f1_breqan12rd f2_breqan12rd f3_breqan12rd f4_breqan12rd f5_breqan12rd f6_breqan12rd p_breqan12d f0_breqan12rd f1_breqan12rd f2_breqan12rd f4_breqan12rd f6_breqan12rd a_wbr f3_breqan12rd f5_breqan12rd f6_breqan12rd a_wbr a_wb p_ancoms $.
$}

$(Two classes are different if they don't have the same relationship to a
     third class.  (Contributed by NM, 3-Jun-2012.) $)

${
	$v A B C R  $.
	f0_nbrne1 $f class A $.
	f1_nbrne1 $f class B $.
	f2_nbrne1 $f class C $.
	f3_nbrne1 $f class R $.
	p_nbrne1 $p |- ( ( A R B /\ -. A R C ) -> B =/= C ) $= f1_nbrne1 f2_nbrne1 f0_nbrne1 f3_nbrne1 p_breq2 f1_nbrne1 f2_nbrne1 a_wceq f0_nbrne1 f1_nbrne1 f3_nbrne1 a_wbr f0_nbrne1 f2_nbrne1 f3_nbrne1 a_wbr p_biimpcd f0_nbrne1 f1_nbrne1 f3_nbrne1 a_wbr f0_nbrne1 f2_nbrne1 f3_nbrne1 a_wbr f1_nbrne1 f2_nbrne1 p_necon3bd f0_nbrne1 f1_nbrne1 f3_nbrne1 a_wbr f0_nbrne1 f2_nbrne1 f3_nbrne1 a_wbr a_wn f1_nbrne1 f2_nbrne1 a_wne p_imp $.
$}

$(Two classes are different if they don't have the same relationship to a
     third class.  (Contributed by NM, 3-Jun-2012.) $)

${
	$v A B C R  $.
	f0_nbrne2 $f class A $.
	f1_nbrne2 $f class B $.
	f2_nbrne2 $f class C $.
	f3_nbrne2 $f class R $.
	p_nbrne2 $p |- ( ( A R C /\ -. B R C ) -> A =/= B ) $= f0_nbrne2 f1_nbrne2 f2_nbrne2 f3_nbrne2 p_breq1 f0_nbrne2 f1_nbrne2 a_wceq f0_nbrne2 f2_nbrne2 f3_nbrne2 a_wbr f1_nbrne2 f2_nbrne2 f3_nbrne2 a_wbr p_biimpcd f0_nbrne2 f2_nbrne2 f3_nbrne2 a_wbr f1_nbrne2 f2_nbrne2 f3_nbrne2 a_wbr f0_nbrne2 f1_nbrne2 p_necon3bd f0_nbrne2 f2_nbrne2 f3_nbrne2 a_wbr f1_nbrne2 f2_nbrne2 f3_nbrne2 a_wbr a_wn f0_nbrne2 f1_nbrne2 a_wne p_imp $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C R  $.
	f0_eqbrtri $f class A $.
	f1_eqbrtri $f class B $.
	f2_eqbrtri $f class C $.
	f3_eqbrtri $f class R $.
	e0_eqbrtri $e |- A = B $.
	e1_eqbrtri $e |- B R C $.
	p_eqbrtri $p |- A R C $= e1_eqbrtri e0_eqbrtri f0_eqbrtri f1_eqbrtri f2_eqbrtri f3_eqbrtri p_breq1i f0_eqbrtri f2_eqbrtri f3_eqbrtri a_wbr f1_eqbrtri f2_eqbrtri f3_eqbrtri a_wbr p_mpbir $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 8-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_eqbrtrd $f wff ph $.
	f1_eqbrtrd $f class A $.
	f2_eqbrtrd $f class B $.
	f3_eqbrtrd $f class C $.
	f4_eqbrtrd $f class R $.
	e0_eqbrtrd $e |- ( ph -> A = B ) $.
	e1_eqbrtrd $e |- ( ph -> B R C ) $.
	p_eqbrtrd $p |- ( ph -> A R C ) $= e1_eqbrtrd e0_eqbrtrd f0_eqbrtrd f1_eqbrtrd f2_eqbrtrd f3_eqbrtrd f4_eqbrtrd p_breq1d f0_eqbrtrd f1_eqbrtrd f3_eqbrtrd f4_eqbrtrd a_wbr f2_eqbrtrd f3_eqbrtrd f4_eqbrtrd a_wbr p_mpbird $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C R  $.
	f0_eqbrtrri $f class A $.
	f1_eqbrtrri $f class B $.
	f2_eqbrtrri $f class C $.
	f3_eqbrtrri $f class R $.
	e0_eqbrtrri $e |- A = B $.
	e1_eqbrtrri $e |- A R C $.
	p_eqbrtrri $p |- B R C $= e0_eqbrtrri f0_eqbrtrri f1_eqbrtrri p_eqcomi e1_eqbrtrri f1_eqbrtrri f0_eqbrtrri f2_eqbrtrri f3_eqbrtrri p_eqbrtri $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_eqbrtrrd $f wff ph $.
	f1_eqbrtrrd $f class A $.
	f2_eqbrtrrd $f class B $.
	f3_eqbrtrrd $f class C $.
	f4_eqbrtrrd $f class R $.
	e0_eqbrtrrd $e |- ( ph -> A = B ) $.
	e1_eqbrtrrd $e |- ( ph -> A R C ) $.
	p_eqbrtrrd $p |- ( ph -> B R C ) $= e0_eqbrtrrd f0_eqbrtrrd f1_eqbrtrrd f2_eqbrtrrd p_eqcomd e1_eqbrtrrd f0_eqbrtrrd f2_eqbrtrrd f1_eqbrtrrd f3_eqbrtrrd f4_eqbrtrrd p_eqbrtrd $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C R  $.
	f0_breqtri $f class A $.
	f1_breqtri $f class B $.
	f2_breqtri $f class C $.
	f3_breqtri $f class R $.
	e0_breqtri $e |- A R B $.
	e1_breqtri $e |- B = C $.
	p_breqtri $p |- A R C $= e0_breqtri e1_breqtri f1_breqtri f2_breqtri f0_breqtri f3_breqtri p_breq2i f0_breqtri f1_breqtri f3_breqtri a_wbr f0_breqtri f2_breqtri f3_breqtri a_wbr p_mpbi $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_breqtrd $f wff ph $.
	f1_breqtrd $f class A $.
	f2_breqtrd $f class B $.
	f3_breqtrd $f class C $.
	f4_breqtrd $f class R $.
	e0_breqtrd $e |- ( ph -> A R B ) $.
	e1_breqtrd $e |- ( ph -> B = C ) $.
	p_breqtrd $p |- ( ph -> A R C ) $= e0_breqtrd e1_breqtrd f0_breqtrd f2_breqtrd f3_breqtrd f1_breqtrd f4_breqtrd p_breq2d f0_breqtrd f1_breqtrd f2_breqtrd f4_breqtrd a_wbr f1_breqtrd f3_breqtrd f4_breqtrd a_wbr p_mpbid $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C R  $.
	f0_breqtrri $f class A $.
	f1_breqtrri $f class B $.
	f2_breqtrri $f class C $.
	f3_breqtrri $f class R $.
	e0_breqtrri $e |- A R B $.
	e1_breqtrri $e |- C = B $.
	p_breqtrri $p |- A R C $= e0_breqtrri e1_breqtrri f2_breqtrri f1_breqtrri p_eqcomi f0_breqtrri f1_breqtrri f2_breqtrri f3_breqtrri p_breqtri $.
$}

$(Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_breqtrrd $f wff ph $.
	f1_breqtrrd $f class A $.
	f2_breqtrrd $f class B $.
	f3_breqtrrd $f class C $.
	f4_breqtrrd $f class R $.
	e0_breqtrrd $e |- ( ph -> A R B ) $.
	e1_breqtrrd $e |- ( ph -> C = B ) $.
	p_breqtrrd $p |- ( ph -> A R C ) $= e0_breqtrrd e1_breqtrrd f0_breqtrrd f3_breqtrrd f2_breqtrrd p_eqcomd f0_breqtrrd f1_breqtrrd f2_breqtrrd f3_breqtrrd f4_breqtrrd p_breqtrd $.
$}

$(Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 11-Aug-1999.) $)

${
	$v A B C D R  $.
	f0_3brtr3i $f class A $.
	f1_3brtr3i $f class B $.
	f2_3brtr3i $f class C $.
	f3_3brtr3i $f class D $.
	f4_3brtr3i $f class R $.
	e0_3brtr3i $e |- A R B $.
	e1_3brtr3i $e |- A = C $.
	e2_3brtr3i $e |- B = D $.
	p_3brtr3i $p |- C R D $= e1_3brtr3i e0_3brtr3i f0_3brtr3i f2_3brtr3i f1_3brtr3i f4_3brtr3i p_eqbrtrri e2_3brtr3i f2_3brtr3i f1_3brtr3i f3_3brtr3i f4_3brtr3i p_breqtri $.
$}

$(Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 11-Aug-1999.) $)

${
	$v A B C D R  $.
	f0_3brtr4i $f class A $.
	f1_3brtr4i $f class B $.
	f2_3brtr4i $f class C $.
	f3_3brtr4i $f class D $.
	f4_3brtr4i $f class R $.
	e0_3brtr4i $e |- A R B $.
	e1_3brtr4i $e |- C = A $.
	e2_3brtr4i $e |- D = B $.
	p_3brtr4i $p |- C R D $= e1_3brtr4i e0_3brtr4i f2_3brtr4i f0_3brtr4i f1_3brtr4i f4_3brtr4i p_eqbrtri e2_3brtr4i f2_3brtr4i f1_3brtr4i f3_3brtr4i f4_3brtr4i p_breqtrri $.
$}

$(Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 18-Oct-1999.) $)

${
	$v ph A B C D R  $.
	f0_3brtr3d $f wff ph $.
	f1_3brtr3d $f class A $.
	f2_3brtr3d $f class B $.
	f3_3brtr3d $f class C $.
	f4_3brtr3d $f class D $.
	f5_3brtr3d $f class R $.
	e0_3brtr3d $e |- ( ph -> A R B ) $.
	e1_3brtr3d $e |- ( ph -> A = C ) $.
	e2_3brtr3d $e |- ( ph -> B = D ) $.
	p_3brtr3d $p |- ( ph -> C R D ) $= e0_3brtr3d e1_3brtr3d e2_3brtr3d f0_3brtr3d f1_3brtr3d f3_3brtr3d f2_3brtr3d f4_3brtr3d f5_3brtr3d p_breq12d f0_3brtr3d f1_3brtr3d f2_3brtr3d f5_3brtr3d a_wbr f3_3brtr3d f4_3brtr3d f5_3brtr3d a_wbr p_mpbid $.
$}

$(Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 21-Feb-2005.) $)

${
	$v ph A B C D R  $.
	f0_3brtr4d $f wff ph $.
	f1_3brtr4d $f class A $.
	f2_3brtr4d $f class B $.
	f3_3brtr4d $f class C $.
	f4_3brtr4d $f class D $.
	f5_3brtr4d $f class R $.
	e0_3brtr4d $e |- ( ph -> A R B ) $.
	e1_3brtr4d $e |- ( ph -> C = A ) $.
	e2_3brtr4d $e |- ( ph -> D = B ) $.
	p_3brtr4d $p |- ( ph -> C R D ) $= e0_3brtr4d e1_3brtr4d e2_3brtr4d f0_3brtr4d f3_3brtr4d f1_3brtr4d f4_3brtr4d f2_3brtr4d f5_3brtr4d p_breq12d f0_3brtr4d f3_3brtr4d f4_3brtr4d f5_3brtr4d a_wbr f1_3brtr4d f2_3brtr4d f5_3brtr4d a_wbr p_mpbird $.
$}

$(Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 16-Jan-1997.) $)

${
	$v ph A B C D R  $.
	f0_3brtr3g $f wff ph $.
	f1_3brtr3g $f class A $.
	f2_3brtr3g $f class B $.
	f3_3brtr3g $f class C $.
	f4_3brtr3g $f class D $.
	f5_3brtr3g $f class R $.
	e0_3brtr3g $e |- ( ph -> A R B ) $.
	e1_3brtr3g $e |- A = C $.
	e2_3brtr3g $e |- B = D $.
	p_3brtr3g $p |- ( ph -> C R D ) $= e0_3brtr3g e1_3brtr3g e2_3brtr3g f1_3brtr3g f3_3brtr3g f2_3brtr3g f4_3brtr3g f5_3brtr3g p_breq12i f0_3brtr3g f1_3brtr3g f2_3brtr3g f5_3brtr3g a_wbr f3_3brtr3g f4_3brtr3g f5_3brtr3g a_wbr p_sylib $.
$}

$(Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 16-Jan-1997.) $)

${
	$v ph A B C D R  $.
	f0_3brtr4g $f wff ph $.
	f1_3brtr4g $f class A $.
	f2_3brtr4g $f class B $.
	f3_3brtr4g $f class C $.
	f4_3brtr4g $f class D $.
	f5_3brtr4g $f class R $.
	e0_3brtr4g $e |- ( ph -> A R B ) $.
	e1_3brtr4g $e |- C = A $.
	e2_3brtr4g $e |- D = B $.
	p_3brtr4g $p |- ( ph -> C R D ) $= e0_3brtr4g e1_3brtr4g e2_3brtr4g f3_3brtr4g f1_3brtr4g f4_3brtr4g f2_3brtr4g f5_3brtr4g p_breq12i f0_3brtr4g f1_3brtr4g f2_3brtr4g f5_3brtr4g a_wbr f3_3brtr4g f4_3brtr4g f5_3brtr4g a_wbr p_sylibr $.
$}

$(B chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_syl5eqbr $f wff ph $.
	f1_syl5eqbr $f class A $.
	f2_syl5eqbr $f class B $.
	f3_syl5eqbr $f class C $.
	f4_syl5eqbr $f class R $.
	e0_syl5eqbr $e |- A = B $.
	e1_syl5eqbr $e |- ( ph -> B R C ) $.
	p_syl5eqbr $p |- ( ph -> A R C ) $= e1_syl5eqbr e0_syl5eqbr f3_syl5eqbr p_eqid f0_syl5eqbr f2_syl5eqbr f3_syl5eqbr f1_syl5eqbr f3_syl5eqbr f4_syl5eqbr p_3brtr4g $.
$}

$(B chained equality inference for a binary relation.  (Contributed by NM,
       17-Sep-2004.) $)

${
	$v ph A B C R  $.
	f0_syl5eqbrr $f wff ph $.
	f1_syl5eqbrr $f class A $.
	f2_syl5eqbrr $f class B $.
	f3_syl5eqbrr $f class C $.
	f4_syl5eqbrr $f class R $.
	e0_syl5eqbrr $e |- B = A $.
	e1_syl5eqbrr $e |- ( ph -> B R C ) $.
	p_syl5eqbrr $p |- ( ph -> A R C ) $= e1_syl5eqbrr e0_syl5eqbrr f3_syl5eqbrr p_eqid f0_syl5eqbrr f2_syl5eqbrr f3_syl5eqbrr f1_syl5eqbrr f3_syl5eqbrr f4_syl5eqbrr p_3brtr3g $.
$}

$(B chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_syl5breq $f wff ph $.
	f1_syl5breq $f class A $.
	f2_syl5breq $f class B $.
	f3_syl5breq $f class C $.
	f4_syl5breq $f class R $.
	e0_syl5breq $e |- A R B $.
	e1_syl5breq $e |- ( ph -> B = C ) $.
	p_syl5breq $p |- ( ph -> A R C ) $= e0_syl5breq f1_syl5breq f2_syl5breq f4_syl5breq a_wbr f0_syl5breq p_a1i e1_syl5breq f0_syl5breq f1_syl5breq f2_syl5breq f3_syl5breq f4_syl5breq p_breqtrd $.
$}

$(B chained equality inference for a binary relation.  (Contributed by NM,
       24-Apr-2005.) $)

${
	$v ph A B C R  $.
	f0_syl5breqr $f wff ph $.
	f1_syl5breqr $f class A $.
	f2_syl5breqr $f class B $.
	f3_syl5breqr $f class C $.
	f4_syl5breqr $f class R $.
	e0_syl5breqr $e |- A R B $.
	e1_syl5breqr $e |- ( ph -> C = B ) $.
	p_syl5breqr $p |- ( ph -> A R C ) $= e0_syl5breqr e1_syl5breqr f0_syl5breqr f3_syl5breqr f2_syl5breqr p_eqcomd f0_syl5breqr f1_syl5breqr f2_syl5breqr f3_syl5breqr f4_syl5breqr p_syl5breq $.
$}

$(A chained equality inference for a binary relation.  (Contributed by NM,
       12-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_syl6eqbr $f wff ph $.
	f1_syl6eqbr $f class A $.
	f2_syl6eqbr $f class B $.
	f3_syl6eqbr $f class C $.
	f4_syl6eqbr $f class R $.
	e0_syl6eqbr $e |- ( ph -> A = B ) $.
	e1_syl6eqbr $e |- B R C $.
	p_syl6eqbr $p |- ( ph -> A R C ) $= e1_syl6eqbr e0_syl6eqbr f0_syl6eqbr f1_syl6eqbr f2_syl6eqbr f3_syl6eqbr f4_syl6eqbr p_breq1d f0_syl6eqbr f1_syl6eqbr f3_syl6eqbr f4_syl6eqbr a_wbr f2_syl6eqbr f3_syl6eqbr f4_syl6eqbr a_wbr p_mpbiri $.
$}

$(A chained equality inference for a binary relation.  (Contributed by NM,
       4-Jan-2006.) $)

${
	$v ph A B C R  $.
	f0_syl6eqbrr $f wff ph $.
	f1_syl6eqbrr $f class A $.
	f2_syl6eqbrr $f class B $.
	f3_syl6eqbrr $f class C $.
	f4_syl6eqbrr $f class R $.
	e0_syl6eqbrr $e |- ( ph -> B = A ) $.
	e1_syl6eqbrr $e |- B R C $.
	p_syl6eqbrr $p |- ( ph -> A R C ) $= e0_syl6eqbrr f0_syl6eqbrr f2_syl6eqbrr f1_syl6eqbrr p_eqcomd e1_syl6eqbrr f0_syl6eqbrr f1_syl6eqbrr f2_syl6eqbrr f3_syl6eqbrr f4_syl6eqbrr p_syl6eqbr $.
$}

$(A chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)

${
	$v ph A B C R  $.
	f0_syl6breq $f wff ph $.
	f1_syl6breq $f class A $.
	f2_syl6breq $f class B $.
	f3_syl6breq $f class C $.
	f4_syl6breq $f class R $.
	e0_syl6breq $e |- ( ph -> A R B ) $.
	e1_syl6breq $e |- B = C $.
	p_syl6breq $p |- ( ph -> A R C ) $= e0_syl6breq f1_syl6breq p_eqid e1_syl6breq f0_syl6breq f1_syl6breq f2_syl6breq f1_syl6breq f3_syl6breq f4_syl6breq p_3brtr3g $.
$}

$(A chained equality inference for a binary relation.  (Contributed by NM,
       24-Apr-2005.) $)

${
	$v ph A B C R  $.
	f0_syl6breqr $f wff ph $.
	f1_syl6breqr $f class A $.
	f2_syl6breqr $f class B $.
	f3_syl6breqr $f class C $.
	f4_syl6breqr $f class R $.
	e0_syl6breqr $e |- ( ph -> A R B ) $.
	e1_syl6breqr $e |- C = B $.
	p_syl6breqr $p |- ( ph -> A R C ) $= e0_syl6breqr e1_syl6breqr f3_syl6breqr f2_syl6breqr p_eqcomi f0_syl6breqr f1_syl6breqr f2_syl6breqr f3_syl6breqr f4_syl6breqr p_syl6breq $.
$}

$(Deduction from a subclass relationship of binary relations.
       (Contributed by NM, 30-Apr-2004.) $)

${
	$v ph A B C D  $.
	f0_ssbrd $f wff ph $.
	f1_ssbrd $f class A $.
	f2_ssbrd $f class B $.
	f3_ssbrd $f class C $.
	f4_ssbrd $f class D $.
	e0_ssbrd $e |- ( ph -> A C_ B ) $.
	p_ssbrd $p |- ( ph -> ( C A D -> C B D ) ) $= e0_ssbrd f0_ssbrd f1_ssbrd f2_ssbrd f3_ssbrd f4_ssbrd a_cop p_sseld f3_ssbrd f4_ssbrd f1_ssbrd a_df-br f3_ssbrd f4_ssbrd f2_ssbrd a_df-br f0_ssbrd f3_ssbrd f4_ssbrd a_cop f1_ssbrd a_wcel f3_ssbrd f4_ssbrd a_cop f2_ssbrd a_wcel f3_ssbrd f4_ssbrd f1_ssbrd a_wbr f3_ssbrd f4_ssbrd f2_ssbrd a_wbr p_3imtr4g $.
$}

$(Inference from a subclass relationship of binary relations.
       (Contributed by NM, 28-Mar-2007.)  (Revised by Mario Carneiro,
       8-Feb-2015.) $)

${
	$v A B C D  $.
	f0_ssbri $f class A $.
	f1_ssbri $f class B $.
	f2_ssbri $f class C $.
	f3_ssbri $f class D $.
	e0_ssbri $e |- A C_ B $.
	p_ssbri $p |- ( C A D -> C B D ) $= e0_ssbri f0_ssbri f1_ssbri a_wss a_wtru p_a1i a_wtru f0_ssbri f1_ssbri f2_ssbri f3_ssbri p_ssbrd f2_ssbri f3_ssbri f0_ssbri a_wbr f2_ssbri f3_ssbri f1_ssbri a_wbr a_wi p_trud $.
$}

$(Deduction version of bound-variable hypothesis builder ~ nfbr .
       (Contributed by NM, 13-Dec-2005.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)

${
	$v ph x A B R  $.
	$d A  $.
	$d B  $.
	$d R  $.
	$d x  $.
	$d ph  $.
	f0_nfbrd $f wff ph $.
	f1_nfbrd $f set x $.
	f2_nfbrd $f class A $.
	f3_nfbrd $f class B $.
	f4_nfbrd $f class R $.
	e0_nfbrd $e |- ( ph -> F/_ x A ) $.
	e1_nfbrd $e |- ( ph -> F/_ x R ) $.
	e2_nfbrd $e |- ( ph -> F/_ x B ) $.
	p_nfbrd $p |- ( ph -> F/ x A R B ) $= f2_nfbrd f3_nfbrd f4_nfbrd a_df-br e0_nfbrd e2_nfbrd f0_nfbrd f1_nfbrd f2_nfbrd f3_nfbrd p_nfopd e1_nfbrd f0_nfbrd f1_nfbrd f2_nfbrd f3_nfbrd a_cop f4_nfbrd p_nfeld f2_nfbrd f3_nfbrd f4_nfbrd a_wbr f2_nfbrd f3_nfbrd a_cop f4_nfbrd a_wcel f0_nfbrd f1_nfbrd p_nfxfrd $.
$}

$(Bound-variable hypothesis builder for binary relation.  (Contributed by
       NM, 1-Sep-1999.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)

${
	$v x A B R  $.
	$d A  $.
	$d B  $.
	$d R  $.
	$d x  $.
	f0_nfbr $f set x $.
	f1_nfbr $f class A $.
	f2_nfbr $f class B $.
	f3_nfbr $f class R $.
	e0_nfbr $e |- F/_ x A $.
	e1_nfbr $e |- F/_ x R $.
	e2_nfbr $e |- F/_ x B $.
	p_nfbr $p |- F/ x A R B $= e0_nfbr f0_nfbr f1_nfbr a_wnfc a_wtru p_a1i e1_nfbr f0_nfbr f3_nfbr a_wnfc a_wtru p_a1i e2_nfbr f0_nfbr f2_nfbr a_wnfc a_wtru p_a1i a_wtru f0_nfbr f1_nfbr f2_nfbr f3_nfbr p_nfbrd f1_nfbr f2_nfbr f3_nfbr a_wbr f0_nfbr a_wnf p_trud $.
$}

$(Relationship between a binary relation and a class abstraction.
       (Contributed by Andrew Salmon, 8-Jul-2011.) $)

${
	$v x z A R  $.
	$d x y  $.
	$d y z A  $.
	$d y z R  $.
	f0_brab1 $f set x $.
	f1_brab1 $f set z $.
	f2_brab1 $f class A $.
	f3_brab1 $f class R $.
	i0_brab1 $f set y $.
	p_brab1 $p |- ( x R A <-> x e. { z | z R A } ) $= f0_brab1 p_vex f1_brab1 a_sup_set_class i0_brab1 a_sup_set_class f2_brab1 f3_brab1 p_breq1 i0_brab1 a_sup_set_class f0_brab1 a_sup_set_class f2_brab1 f3_brab1 p_breq1 f1_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr i0_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f0_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f1_brab1 i0_brab1 f0_brab1 a_sup_set_class a_cvv p_sbcie2g f0_brab1 a_sup_set_class a_cvv a_wcel f1_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f1_brab1 f0_brab1 a_sup_set_class a_wsbc f0_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr a_wb a_ax-mp f1_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f1_brab1 f0_brab1 a_sup_set_class a_df-sbc f0_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f1_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f1_brab1 f0_brab1 a_sup_set_class a_wsbc f0_brab1 a_sup_set_class f1_brab1 a_sup_set_class f2_brab1 f3_brab1 a_wbr f1_brab1 a_cab a_wcel p_bitr3i $.
$}

$(The union of two binary relations.  (Contributed by NM, 21-Dec-2008.) $)

${
	$v A B R S  $.
	f0_brun $f class A $.
	f1_brun $f class B $.
	f2_brun $f class R $.
	f3_brun $f class S $.
	p_brun $p |- ( A ( R u. S ) B <-> ( A R B \/ A S B ) ) $= f0_brun f1_brun a_cop f2_brun f3_brun p_elun f0_brun f1_brun f2_brun f3_brun a_cun a_df-br f0_brun f1_brun f2_brun a_df-br f0_brun f1_brun f3_brun a_df-br f0_brun f1_brun f2_brun a_wbr f0_brun f1_brun a_cop f2_brun a_wcel f0_brun f1_brun f3_brun a_wbr f0_brun f1_brun a_cop f3_brun a_wcel p_orbi12i f0_brun f1_brun a_cop f2_brun f3_brun a_cun a_wcel f0_brun f1_brun a_cop f2_brun a_wcel f0_brun f1_brun a_cop f3_brun a_wcel a_wo f0_brun f1_brun f2_brun f3_brun a_cun a_wbr f0_brun f1_brun f2_brun a_wbr f0_brun f1_brun f3_brun a_wbr a_wo p_3bitr4i $.
$}

$(The intersection of two relations.  (Contributed by FL, 7-Oct-2008.) $)

${
	$v A B R S  $.
	f0_brin $f class A $.
	f1_brin $f class B $.
	f2_brin $f class R $.
	f3_brin $f class S $.
	p_brin $p |- ( A ( R i^i S ) B <-> ( A R B /\ A S B ) ) $= f0_brin f1_brin a_cop f2_brin f3_brin p_elin f0_brin f1_brin f2_brin f3_brin a_cin a_df-br f0_brin f1_brin f2_brin a_df-br f0_brin f1_brin f3_brin a_df-br f0_brin f1_brin f2_brin a_wbr f0_brin f1_brin a_cop f2_brin a_wcel f0_brin f1_brin f3_brin a_wbr f0_brin f1_brin a_cop f3_brin a_wcel p_anbi12i f0_brin f1_brin a_cop f2_brin f3_brin a_cin a_wcel f0_brin f1_brin a_cop f2_brin a_wcel f0_brin f1_brin a_cop f3_brin a_wcel a_wa f0_brin f1_brin f2_brin f3_brin a_cin a_wbr f0_brin f1_brin f2_brin a_wbr f0_brin f1_brin f3_brin a_wbr a_wa p_3bitr4i $.
$}

$(The difference of two binary relations.  (Contributed by Scott Fenton,
     11-Apr-2011.) $)

${
	$v A B R S  $.
	f0_brdif $f class A $.
	f1_brdif $f class B $.
	f2_brdif $f class R $.
	f3_brdif $f class S $.
	p_brdif $p |- ( A ( R \ S ) B <-> ( A R B /\ -. A S B ) ) $= f0_brdif f1_brdif a_cop f2_brdif f3_brdif p_eldif f0_brdif f1_brdif f2_brdif f3_brdif a_cdif a_df-br f0_brdif f1_brdif f2_brdif a_df-br f0_brdif f1_brdif f3_brdif a_df-br f0_brdif f1_brdif f3_brdif a_wbr f0_brdif f1_brdif a_cop f3_brdif a_wcel p_notbii f0_brdif f1_brdif f2_brdif a_wbr f0_brdif f1_brdif a_cop f2_brdif a_wcel f0_brdif f1_brdif f3_brdif a_wbr a_wn f0_brdif f1_brdif a_cop f3_brdif a_wcel a_wn p_anbi12i f0_brdif f1_brdif a_cop f2_brdif f3_brdif a_cdif a_wcel f0_brdif f1_brdif a_cop f2_brdif a_wcel f0_brdif f1_brdif a_cop f3_brdif a_wcel a_wn a_wa f0_brdif f1_brdif f2_brdif f3_brdif a_cdif a_wbr f0_brdif f1_brdif f2_brdif a_wbr f0_brdif f1_brdif f3_brdif a_wbr a_wn a_wa p_3bitr4i $.
$}

$(Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)

${
	$v x A B C D R  $.
	$d y A  $.
	$d y B  $.
	$d y C  $.
	$d y D  $.
	$d y R  $.
	$d x y  $.
	f0_sbcbrg $f set x $.
	f1_sbcbrg $f class A $.
	f2_sbcbrg $f class B $.
	f3_sbcbrg $f class C $.
	f4_sbcbrg $f class D $.
	f5_sbcbrg $f class R $.
	i0_sbcbrg $f set y $.
	p_sbcbrg $p |- ( A e. D -> ( [. A / x ]. B R C <-> [_ A / x ]_ B [_ A / x ]_ R [_ A / x ]_ C ) ) $= f2_sbcbrg f3_sbcbrg f5_sbcbrg a_wbr f0_sbcbrg i0_sbcbrg f1_sbcbrg p_dfsbcq2 f0_sbcbrg i0_sbcbrg a_sup_set_class f1_sbcbrg f2_sbcbrg p_csbeq1 f0_sbcbrg i0_sbcbrg a_sup_set_class f1_sbcbrg f5_sbcbrg p_csbeq1 f0_sbcbrg i0_sbcbrg a_sup_set_class f1_sbcbrg f3_sbcbrg p_csbeq1 i0_sbcbrg a_sup_set_class f1_sbcbrg a_wceq f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg a_csb f0_sbcbrg f1_sbcbrg f2_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg a_csb f0_sbcbrg f1_sbcbrg f3_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg a_csb f0_sbcbrg f1_sbcbrg f5_sbcbrg a_csb p_breq123d f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg p_nfcsb1v f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg p_nfcsb1v f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg p_nfcsb1v f0_sbcbrg f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg a_csb p_nfbr f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg p_csbeq1a f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg p_csbeq1a f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg p_csbeq1a f0_sbcbrg a_sup_set_class i0_sbcbrg a_sup_set_class a_wceq f2_sbcbrg f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg a_csb f3_sbcbrg f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg a_csb f5_sbcbrg f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg a_csb p_breq123d f2_sbcbrg f3_sbcbrg f5_sbcbrg a_wbr f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg a_csb a_wbr f0_sbcbrg i0_sbcbrg p_sbie f2_sbcbrg f3_sbcbrg f5_sbcbrg a_wbr f0_sbcbrg i0_sbcbrg a_wsb f0_sbcbrg i0_sbcbrg a_sup_set_class f2_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f3_sbcbrg a_csb f0_sbcbrg i0_sbcbrg a_sup_set_class f5_sbcbrg a_csb a_wbr f2_sbcbrg f3_sbcbrg f5_sbcbrg a_wbr f0_sbcbrg f1_sbcbrg a_wsbc f0_sbcbrg f1_sbcbrg f2_sbcbrg a_csb f0_sbcbrg f1_sbcbrg f3_sbcbrg a_csb f0_sbcbrg f1_sbcbrg f5_sbcbrg a_csb a_wbr i0_sbcbrg f1_sbcbrg f4_sbcbrg p_vtoclbg $.
$}

$(Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)

${
	$v x A B C D R  $.
	$d A  $.
	$d C  $.
	$d D  $.
	$d x R  $.
	f0_sbcbr12g $f set x $.
	f1_sbcbr12g $f class A $.
	f2_sbcbr12g $f class B $.
	f3_sbcbr12g $f class C $.
	f4_sbcbr12g $f class D $.
	f5_sbcbr12g $f class R $.
	p_sbcbr12g $p |- ( A e. D -> ( [. A / x ]. B R C <-> [_ A / x ]_ B R [_ A / x ]_ C ) ) $= f0_sbcbr12g f1_sbcbr12g f2_sbcbr12g f3_sbcbr12g f4_sbcbr12g f5_sbcbr12g p_sbcbrg f0_sbcbr12g f1_sbcbr12g f5_sbcbr12g f4_sbcbr12g p_csbconstg f1_sbcbr12g f4_sbcbr12g a_wcel f0_sbcbr12g f1_sbcbr12g f5_sbcbr12g a_csb f5_sbcbr12g f0_sbcbr12g f1_sbcbr12g f2_sbcbr12g a_csb f0_sbcbr12g f1_sbcbr12g f3_sbcbr12g a_csb p_breqd f1_sbcbr12g f4_sbcbr12g a_wcel f2_sbcbr12g f3_sbcbr12g f5_sbcbr12g a_wbr f0_sbcbr12g f1_sbcbr12g a_wsbc f0_sbcbr12g f1_sbcbr12g f2_sbcbr12g a_csb f0_sbcbr12g f1_sbcbr12g f3_sbcbr12g a_csb f0_sbcbr12g f1_sbcbr12g f5_sbcbr12g a_csb a_wbr f0_sbcbr12g f1_sbcbr12g f2_sbcbr12g a_csb f0_sbcbr12g f1_sbcbr12g f3_sbcbr12g a_csb f5_sbcbr12g a_wbr p_bitrd $.
$}

$(Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)

${
	$v x A B C D R  $.
	$d A  $.
	$d x C  $.
	$d D  $.
	$d x R  $.
	f0_sbcbr1g $f set x $.
	f1_sbcbr1g $f class A $.
	f2_sbcbr1g $f class B $.
	f3_sbcbr1g $f class C $.
	f4_sbcbr1g $f class D $.
	f5_sbcbr1g $f class R $.
	p_sbcbr1g $p |- ( A e. D -> ( [. A / x ]. B R C <-> [_ A / x ]_ B R C ) ) $= f0_sbcbr1g f1_sbcbr1g f2_sbcbr1g f3_sbcbr1g f4_sbcbr1g f5_sbcbr1g p_sbcbr12g f0_sbcbr1g f1_sbcbr1g f3_sbcbr1g f4_sbcbr1g p_csbconstg f1_sbcbr1g f4_sbcbr1g a_wcel f0_sbcbr1g f1_sbcbr1g f3_sbcbr1g a_csb f3_sbcbr1g f0_sbcbr1g f1_sbcbr1g f2_sbcbr1g a_csb f5_sbcbr1g p_breq2d f1_sbcbr1g f4_sbcbr1g a_wcel f2_sbcbr1g f3_sbcbr1g f5_sbcbr1g a_wbr f0_sbcbr1g f1_sbcbr1g a_wsbc f0_sbcbr1g f1_sbcbr1g f2_sbcbr1g a_csb f0_sbcbr1g f1_sbcbr1g f3_sbcbr1g a_csb f5_sbcbr1g a_wbr f0_sbcbr1g f1_sbcbr1g f2_sbcbr1g a_csb f3_sbcbr1g f5_sbcbr1g a_wbr p_bitrd $.
$}

$(Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)

${
	$v x A B C D R  $.
	$d A  $.
	$d x B  $.
	$d D  $.
	$d x R  $.
	f0_sbcbr2g $f set x $.
	f1_sbcbr2g $f class A $.
	f2_sbcbr2g $f class B $.
	f3_sbcbr2g $f class C $.
	f4_sbcbr2g $f class D $.
	f5_sbcbr2g $f class R $.
	p_sbcbr2g $p |- ( A e. D -> ( [. A / x ]. B R C <-> B R [_ A / x ]_ C ) ) $= f0_sbcbr2g f1_sbcbr2g f2_sbcbr2g f3_sbcbr2g f4_sbcbr2g f5_sbcbr2g p_sbcbr12g f0_sbcbr2g f1_sbcbr2g f2_sbcbr2g f4_sbcbr2g p_csbconstg f1_sbcbr2g f4_sbcbr2g a_wcel f0_sbcbr2g f1_sbcbr2g f2_sbcbr2g a_csb f2_sbcbr2g f0_sbcbr2g f1_sbcbr2g f3_sbcbr2g a_csb f5_sbcbr2g p_breq1d f1_sbcbr2g f4_sbcbr2g a_wcel f2_sbcbr2g f3_sbcbr2g f5_sbcbr2g a_wbr f0_sbcbr2g f1_sbcbr2g a_wsbc f0_sbcbr2g f1_sbcbr2g f2_sbcbr2g a_csb f0_sbcbr2g f1_sbcbr2g f3_sbcbr2g a_csb f5_sbcbr2g a_wbr f2_sbcbr2g f0_sbcbr2g f1_sbcbr2g f3_sbcbr2g a_csb f5_sbcbr2g a_wbr p_bitrd $.
$}


