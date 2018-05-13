$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Power_classes.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Unordered and ordered pairs

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare new symbols needed. $)

$c <. $.

$(Bracket (the period distinguishes it from 'less than') $)

$c >. $.

$(Bracket (the period distinguishes it from 'greater than') $)

$(Extend class notation to include singleton. $)

${
	$v A  $.
	f0_csn $f class A $.
	a_csn $a class { A } $.
$}

$(Extend class notation to include unordered pair. $)

${
	$v A B  $.
	f0_cpr $f class A $.
	f1_cpr $f class B $.
	a_cpr $a class { A , B } $.
$}

$(Extend class notation to include unordered triplet. $)

${
	$v A B C  $.
	f0_ctp $f class A $.
	f1_ctp $f class B $.
	f2_ctp $f class C $.
	a_ctp $a class { A , B , C } $.
$}

$(Extend class notation to include ordered pair. $)

${
	$v A B  $.
	f0_cop $f class A $.
	f1_cop $f class B $.
	a_cop $a class <. A , B >. $.
$}

$(Extend class notation to include ordered triple. $)

${
	$v A B C  $.
	f0_cotp $f class A $.
	f1_cotp $f class B $.
	f2_cotp $f class C $.
	a_cotp $a class <. A , B , C >. $.
$}

$(Soundness justification theorem for ~ df-sn .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v x y A  $.
	$d x A  $.
	$d y A  $.
	$d z x  $.
	$d z y  $.
	$d z A  $.
	f0_snjust $f set x $.
	f1_snjust $f set y $.
	f2_snjust $f class A $.
	i0_snjust $f set z $.
	p_snjust $p |- { x | x = A } = { y | y = A } $= f0_snjust a_sup_set_class i0_snjust a_sup_set_class f2_snjust p_eqeq1 f0_snjust a_sup_set_class f2_snjust a_wceq i0_snjust a_sup_set_class f2_snjust a_wceq f0_snjust i0_snjust p_cbvabv i0_snjust a_sup_set_class f1_snjust a_sup_set_class f2_snjust p_eqeq1 i0_snjust a_sup_set_class f2_snjust a_wceq f1_snjust a_sup_set_class f2_snjust a_wceq i0_snjust f1_snjust p_cbvabv f0_snjust a_sup_set_class f2_snjust a_wceq f0_snjust a_cab i0_snjust a_sup_set_class f2_snjust a_wceq i0_snjust a_cab f1_snjust a_sup_set_class f2_snjust a_wceq f1_snjust a_cab p_eqtri $.
$}

$(Define the singleton of a class.  Definition 7.1 of [Quine] p. 48.  For
       convenience, it is well-defined for proper classes, i.e., those that are
       not elements of ` _V ` , although it is not very meaningful in this
       case.  For an alternate definition see ~ dfsn2 .  (Contributed by NM,
       5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_df-sn $f set x $.
	f1_df-sn $f class A $.
	a_df-sn $a |- { A } = { x | x = A } $.
$}

$(Define unordered pair of classes.  Definition 7.1 of [Quine] p. 48.  For
     example, ` A e. { 1 , -u 1 } -> ( A ^ 2 ) = 1 ` ( ~ ex-pr ).  They are
     unordered, so ` { A , B } = { B , A } ` as proven by ~ prcom .  For a more
     traditional definition, but requiring a dummy variable, see ~ dfpr2 .
     (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	f0_df-pr $f class A $.
	f1_df-pr $f class B $.
	a_df-pr $a |- { A , B } = ( { A } u. { B } ) $.
$}

$(Define unordered triple of classes.  Definition of [Enderton] p. 19.
     (Contributed by NM, 9-Apr-1994.) $)

${
	$v A B C  $.
	f0_df-tp $f class A $.
	f1_df-tp $f class B $.
	f2_df-tp $f class C $.
	a_df-tp $a |- { A , B , C } = ( { A , B } u. { C } ) $.
$}

$(Definition of an ordered pair, equivalent to Kuratowski's definition
       ` { { A } , { A , B } } ` when the arguments are sets.  Since the
       behavior of Kuratowski definition is not very useful for proper classes,
       we define it to be empty in this case (see ~ opprc1 , ~ opprc2 , and
       ~ 0nelop ).  For Kuratowski's actual definition when the arguments are
       sets, see ~ dfop .  For the justifying theorem (for sets) see ~ opth .
       See ~ dfopif for an equivalent formulation using the ` if ` operation.

       Definition 9.1 of [Quine] p. 58 defines an ordered pair unconditionally
       as ` <. A , B >. = { { A } , { A , B } } ` , which has different
       behavior from our ~ df-op when the arguments are proper classes.
       Ordinarily this difference is not important, since neither definition is
       meaningful in that case.  Our ~ df-op was chosen because it often makes
       proofs shorter by eliminating unnecessary sethood hypotheses.

       There are other ways to define ordered pairs.  The basic requirement is
       that two ordered pairs are equal iff their respective members are
       equal.  In 1914 Norbert Wiener gave the first successful definition
       ` <. A , B >. ` _2 ` = { { { A } , (/) } , { { B } } } ` , justified by
       ~ opthwiener .  This was simplified by Kazimierz Kuratowski in 1921 to
       our present definition.  An even simpler definition ` <. A , B >. ` _3
       ` = { A , { A , B } } ` is justified by ~ opthreg , but it requires the
       Axiom of Regularity for its justification and is not commonly used.  A
       definition that also works for proper classes is ` <. A , B >. ` _4
       ` = ( ( A X. { (/) } ) u. ( B X. { { (/) } } ) ) ` , justified by
       ~ opthprc .  If we restrict our sets to nonnegative integers, an ordered
       pair definition that involves only elementary arithmetic is provided by
       ~ nn0opthi .  Finally, an ordered pair of real numbers can be
       represented by a complex number as shown by ~ cru .  (Contributed by NM,
       28-May-1995.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_df-op $f set x $.
	f1_df-op $f class A $.
	f2_df-op $f class B $.
	a_df-op $a |- <. A , B >. = { x | ( A e. _V /\ B e. _V /\ x e. { { A } , { A , B } } ) } $.
$}

$(Define ordered triple of classes.  Definition of ordered triple in [Stoll]
     p. 25.  (Contributed by NM, 3-Apr-2015.) $)

${
	$v A B C  $.
	f0_df-ot $f class A $.
	f1_df-ot $f class B $.
	f2_df-ot $f class C $.
	a_df-ot $a |- <. A , B , C >. = <. <. A , B >. , C >. $.
$}

$(Equality theorem for singletons.  Part of Exercise 4 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_sneq $f class A $.
	f1_sneq $f class B $.
	i0_sneq $f set x $.
	p_sneq $p |- ( A = B -> { A } = { B } ) $= f0_sneq f1_sneq i0_sneq a_sup_set_class p_eqeq2 f0_sneq f1_sneq a_wceq i0_sneq a_sup_set_class f0_sneq a_wceq i0_sneq a_sup_set_class f1_sneq a_wceq i0_sneq p_abbidv i0_sneq f0_sneq a_df-sn i0_sneq f1_sneq a_df-sn f0_sneq f1_sneq a_wceq i0_sneq a_sup_set_class f0_sneq a_wceq i0_sneq a_cab i0_sneq a_sup_set_class f1_sneq a_wceq i0_sneq a_cab f0_sneq a_csn f1_sneq a_csn p_3eqtr4g $.
$}

$(Equality inference for singletons.  (Contributed by NM, 22-Jan-2004.) $)

${
	$v A B  $.
	f0_sneqi $f class A $.
	f1_sneqi $f class B $.
	e0_sneqi $e |- A = B $.
	p_sneqi $p |- { A } = { B } $= e0_sneqi f0_sneqi f1_sneqi p_sneq f0_sneqi f1_sneqi a_wceq f0_sneqi a_csn f1_sneqi a_csn a_wceq a_ax-mp $.
$}

$(Equality deduction for singletons.  (Contributed by NM, 22-Jan-2004.) $)

${
	$v ph A B  $.
	f0_sneqd $f wff ph $.
	f1_sneqd $f class A $.
	f2_sneqd $f class B $.
	e0_sneqd $e |- ( ph -> A = B ) $.
	p_sneqd $p |- ( ph -> { A } = { B } ) $= e0_sneqd f1_sneqd f2_sneqd p_sneq f0_sneqd f1_sneqd f2_sneqd a_wceq f1_sneqd a_csn f2_sneqd a_csn a_wceq p_syl $.
$}

$(Alternate definition of singleton.  Definition 5.1 of [TakeutiZaring]
     p. 15.  (Contributed by NM, 24-Apr-1994.) $)

${
	$v A  $.
	f0_dfsn2 $f class A $.
	p_dfsn2 $p |- { A } = { A , A } $= f0_dfsn2 f0_dfsn2 a_df-pr f0_dfsn2 a_csn p_unidm f0_dfsn2 f0_dfsn2 a_cpr f0_dfsn2 a_csn f0_dfsn2 a_csn a_cun f0_dfsn2 a_csn p_eqtr2i $.
$}

$(There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v x A  $.
	$d x A  $.
	f0_elsn $f set x $.
	f1_elsn $f class A $.
	p_elsn $p |- ( x e. { A } <-> x = A ) $= f0_elsn f1_elsn a_df-sn f0_elsn a_sup_set_class f1_elsn a_wceq f0_elsn f1_elsn a_csn p_abeq2i $.
$}

$(Alternate definition of unordered pair.  Definition 5.1 of
       [TakeutiZaring] p. 15.  (Contributed by NM, 24-Apr-1994.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfpr2 $f set x $.
	f1_dfpr2 $f class A $.
	f2_dfpr2 $f class B $.
	p_dfpr2 $p |- { A , B } = { x | ( x = A \/ x = B ) } $= f1_dfpr2 f2_dfpr2 a_df-pr f0_dfpr2 a_sup_set_class f1_dfpr2 a_csn f2_dfpr2 a_csn p_elun f0_dfpr2 f1_dfpr2 p_elsn f0_dfpr2 f2_dfpr2 p_elsn f0_dfpr2 a_sup_set_class f1_dfpr2 a_csn a_wcel f0_dfpr2 a_sup_set_class f1_dfpr2 a_wceq f0_dfpr2 a_sup_set_class f2_dfpr2 a_csn a_wcel f0_dfpr2 a_sup_set_class f2_dfpr2 a_wceq p_orbi12i f0_dfpr2 a_sup_set_class f1_dfpr2 a_csn f2_dfpr2 a_csn a_cun a_wcel f0_dfpr2 a_sup_set_class f1_dfpr2 a_csn a_wcel f0_dfpr2 a_sup_set_class f2_dfpr2 a_csn a_wcel a_wo f0_dfpr2 a_sup_set_class f1_dfpr2 a_wceq f0_dfpr2 a_sup_set_class f2_dfpr2 a_wceq a_wo p_bitri f0_dfpr2 a_sup_set_class f1_dfpr2 a_wceq f0_dfpr2 a_sup_set_class f2_dfpr2 a_wceq a_wo f0_dfpr2 f1_dfpr2 a_csn f2_dfpr2 a_csn a_cun p_abbi2i f1_dfpr2 f2_dfpr2 a_cpr f1_dfpr2 a_csn f2_dfpr2 a_csn a_cun f0_dfpr2 a_sup_set_class f1_dfpr2 a_wceq f0_dfpr2 a_sup_set_class f2_dfpr2 a_wceq a_wo f0_dfpr2 a_cab p_eqtri $.
$}

$(A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15, generalized.  (Contributed by NM,
       13-Sep-1995.) $)

${
	$v A B C V  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_elprg $f class A $.
	f1_elprg $f class B $.
	f2_elprg $f class C $.
	f3_elprg $f class V $.
	i0_elprg $f set x $.
	p_elprg $p |- ( A e. V -> ( A e. { B , C } <-> ( A = B \/ A = C ) ) ) $= i0_elprg a_sup_set_class f0_elprg f1_elprg p_eqeq1 i0_elprg a_sup_set_class f0_elprg f2_elprg p_eqeq1 i0_elprg a_sup_set_class f0_elprg a_wceq i0_elprg a_sup_set_class f1_elprg a_wceq f0_elprg f1_elprg a_wceq i0_elprg a_sup_set_class f2_elprg a_wceq f0_elprg f2_elprg a_wceq p_orbi12d i0_elprg f1_elprg f2_elprg p_dfpr2 i0_elprg a_sup_set_class f1_elprg a_wceq i0_elprg a_sup_set_class f2_elprg a_wceq a_wo f0_elprg f1_elprg a_wceq f0_elprg f2_elprg a_wceq a_wo i0_elprg f0_elprg f1_elprg f2_elprg a_cpr f3_elprg p_elab2g $.
$}

$(A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15.  (Contributed by NM,
       13-Sep-1995.) $)

${
	$v A B C  $.
	f0_elpr $f class A $.
	f1_elpr $f class B $.
	f2_elpr $f class C $.
	e0_elpr $e |- A e. _V $.
	p_elpr $p |- ( A e. { B , C } <-> ( A = B \/ A = C ) ) $= e0_elpr f0_elpr f1_elpr f2_elpr a_cvv p_elprg f0_elpr a_cvv a_wcel f0_elpr f1_elpr f2_elpr a_cpr a_wcel f0_elpr f1_elpr a_wceq f0_elpr f2_elpr a_wceq a_wo a_wb a_ax-mp $.
$}

$(A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15.  (Contributed by NM,
       14-Oct-2005.) $)

${
	$v A B C  $.
	f0_elpr2 $f class A $.
	f1_elpr2 $f class B $.
	f2_elpr2 $f class C $.
	e0_elpr2 $e |- B e. _V $.
	e1_elpr2 $e |- C e. _V $.
	p_elpr2 $p |- ( A e. { B , C } <-> ( A = B \/ A = C ) ) $= f0_elpr2 f1_elpr2 f2_elpr2 f1_elpr2 f2_elpr2 a_cpr p_elprg f0_elpr2 f1_elpr2 f2_elpr2 a_cpr a_wcel f0_elpr2 f1_elpr2 a_wceq f0_elpr2 f2_elpr2 a_wceq a_wo p_ibi e0_elpr2 f0_elpr2 f1_elpr2 a_cvv p_eleq1 f0_elpr2 f1_elpr2 a_wceq f0_elpr2 a_cvv a_wcel f1_elpr2 a_cvv a_wcel p_mpbiri e1_elpr2 f0_elpr2 f2_elpr2 a_cvv p_eleq1 f0_elpr2 f2_elpr2 a_wceq f0_elpr2 a_cvv a_wcel f2_elpr2 a_cvv a_wcel p_mpbiri f0_elpr2 f1_elpr2 a_wceq f0_elpr2 a_cvv a_wcel f0_elpr2 f2_elpr2 a_wceq p_jaoi f0_elpr2 f1_elpr2 f2_elpr2 a_cvv p_elprg f0_elpr2 f1_elpr2 a_wceq f0_elpr2 f2_elpr2 a_wceq a_wo f0_elpr2 a_cvv a_wcel f0_elpr2 f1_elpr2 f2_elpr2 a_cpr a_wcel f0_elpr2 f1_elpr2 a_wceq f0_elpr2 f2_elpr2 a_wceq a_wo a_wb p_syl f0_elpr2 f1_elpr2 a_wceq f0_elpr2 f2_elpr2 a_wceq a_wo f0_elpr2 f1_elpr2 f2_elpr2 a_cpr a_wcel p_ibir f0_elpr2 f1_elpr2 f2_elpr2 a_cpr a_wcel f0_elpr2 f1_elpr2 a_wceq f0_elpr2 f2_elpr2 a_wceq a_wo p_impbii $.
$}

$(If a class is an element of a pair, then it is one of the two paired
     elements.  (Contributed by Scott Fenton, 1-Apr-2011.) $)

${
	$v A B C  $.
	f0_elpri $f class A $.
	f1_elpri $f class B $.
	f2_elpri $f class C $.
	p_elpri $p |- ( A e. { B , C } -> ( A = B \/ A = C ) ) $= f0_elpri f1_elpri f2_elpri f1_elpri f2_elpri a_cpr p_elprg f0_elpri f1_elpri f2_elpri a_cpr a_wcel f0_elpri f1_elpri a_wceq f0_elpri f2_elpri a_wceq a_wo p_ibi $.
$}

$(If an element doesn't match the items in an unordered pair, it is not in
       the unordered pair.  (Contributed by David A. Wheeler, 10-May-2015.) $)

${
	$v A B C  $.
	f0_nelpri $f class A $.
	f1_nelpri $f class B $.
	f2_nelpri $f class C $.
	e0_nelpri $e |- A =/= B $.
	e1_nelpri $e |- A =/= C $.
	p_nelpri $p |- -. A e. { B , C } $= e0_nelpri e1_nelpri f0_nelpri f1_nelpri f0_nelpri f2_nelpri p_neanior f0_nelpri f1_nelpri f2_nelpri p_elpri f0_nelpri f1_nelpri f2_nelpri a_cpr a_wcel f0_nelpri f1_nelpri a_wceq f0_nelpri f2_nelpri a_wceq a_wo p_con3i f0_nelpri f1_nelpri a_wne f0_nelpri f2_nelpri a_wne a_wa f0_nelpri f1_nelpri a_wceq f0_nelpri f2_nelpri a_wceq a_wo a_wn f0_nelpri f1_nelpri f2_nelpri a_cpr a_wcel a_wn p_sylbi f0_nelpri f1_nelpri a_wne f0_nelpri f2_nelpri a_wne f0_nelpri f1_nelpri f2_nelpri a_cpr a_wcel a_wn p_mp2an $.
$}

$(There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15 (generalized).  (Contributed by NM, 13-Sep-1995.)  (Proof
       shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B V  $.
	$d A x  $.
	$d B x  $.
	f0_elsncg $f class A $.
	f1_elsncg $f class B $.
	f2_elsncg $f class V $.
	i0_elsncg $f set x $.
	p_elsncg $p |- ( A e. V -> ( A e. { B } <-> A = B ) ) $= i0_elsncg a_sup_set_class f0_elsncg f1_elsncg p_eqeq1 i0_elsncg f1_elsncg a_df-sn i0_elsncg a_sup_set_class f1_elsncg a_wceq f0_elsncg f1_elsncg a_wceq i0_elsncg f0_elsncg f1_elsncg a_csn f2_elsncg p_elab2g $.
$}

$(There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 13-Sep-1995.) $)

${
	$v A B  $.
	f0_elsnc $f class A $.
	f1_elsnc $f class B $.
	e0_elsnc $e |- A e. _V $.
	p_elsnc $p |- ( A e. { B } <-> A = B ) $= e0_elsnc f0_elsnc f1_elsnc a_cvv p_elsncg f0_elsnc a_cvv a_wcel f0_elsnc f1_elsnc a_csn a_wcel f0_elsnc f1_elsnc a_wceq a_wb a_ax-mp $.
$}

$(There is only one element in a singleton.  (Contributed by NM,
     5-Jun-1994.) $)

${
	$v A B  $.
	f0_elsni $f class A $.
	f1_elsni $f class B $.
	p_elsni $p |- ( A e. { B } -> A = B ) $= f0_elsni f1_elsni f1_elsni a_csn p_elsncg f0_elsni f1_elsni a_csn a_wcel f0_elsni f1_elsni a_wceq p_ibi $.
$}

$(A set is a member of its singleton.  Part of Theorem 7.6 of [Quine]
     p. 49.  (Contributed by NM, 28-Oct-2003.) $)

${
	$v A V  $.
	f0_snidg $f class A $.
	f1_snidg $f class V $.
	p_snidg $p |- ( A e. V -> A e. { A } ) $= f0_snidg p_eqid f0_snidg f0_snidg f1_snidg p_elsncg f0_snidg f1_snidg a_wcel f0_snidg f0_snidg a_csn a_wcel f0_snidg f0_snidg a_wceq p_mpbiri $.
$}

$(A class is a set iff it is a member of its singleton.  (Contributed by NM,
     5-Apr-2004.) $)

${
	$v A  $.
	f0_snidb $f class A $.
	p_snidb $p |- ( A e. _V <-> A e. { A } ) $= f0_snidb a_cvv p_snidg f0_snidb f0_snidb a_csn p_elex f0_snidb a_cvv a_wcel f0_snidb f0_snidb a_csn a_wcel p_impbii $.
$}

$(A set is a member of its singleton.  Part of Theorem 7.6 of [Quine]
       p. 49.  (Contributed by NM, 31-Dec-1993.) $)

${
	$v A  $.
	f0_snid $f class A $.
	e0_snid $e |- A e. _V $.
	p_snid $p |- A e. { A } $= e0_snid f0_snid p_snidb f0_snid a_cvv a_wcel f0_snid f0_snid a_csn a_wcel p_mpbi $.
$}

$(There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
     p. 15.  This variation requires only that ` B ` , rather than ` A ` , be a
     set.  (Contributed by NM, 28-Oct-2003.) $)

${
	$v A B V  $.
	f0_elsnc2g $f class A $.
	f1_elsnc2g $f class B $.
	f2_elsnc2g $f class V $.
	p_elsnc2g $p |- ( B e. V -> ( A e. { B } <-> A = B ) ) $= f0_elsnc2g f1_elsnc2g p_elsni f1_elsnc2g f2_elsnc2g p_snidg f0_elsnc2g f1_elsnc2g f1_elsnc2g a_csn p_eleq1 f1_elsnc2g f2_elsnc2g a_wcel f0_elsnc2g f1_elsnc2g a_csn a_wcel f0_elsnc2g f1_elsnc2g a_wceq f1_elsnc2g f1_elsnc2g a_csn a_wcel p_syl5ibrcom f1_elsnc2g f2_elsnc2g a_wcel f0_elsnc2g f1_elsnc2g a_csn a_wcel f0_elsnc2g f1_elsnc2g a_wceq p_impbid2 $.
$}

$(There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  This variation requires only that ` B ` , rather than ` A ` , be
       a set.  (Contributed by NM, 12-Jun-1994.) $)

${
	$v A B  $.
	f0_elsnc2 $f class A $.
	f1_elsnc2 $f class B $.
	e0_elsnc2 $e |- B e. _V $.
	p_elsnc2 $p |- ( A e. { B } <-> A = B ) $= e0_elsnc2 f0_elsnc2 f1_elsnc2 a_cvv p_elsnc2g f1_elsnc2 a_cvv a_wcel f0_elsnc2 f1_elsnc2 a_csn a_wcel f0_elsnc2 f1_elsnc2 a_wceq a_wb a_ax-mp $.
$}

$(Substitution expressed in terms of quantification over a singleton.
       (Contributed by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph x A V  $.
	$d A x  $.
	$d x  $.
	f0_ralsns $f wff ph $.
	f1_ralsns $f set x $.
	f2_ralsns $f class A $.
	f3_ralsns $f class V $.
	p_ralsns $p |- ( A e. V -> ( A. x e. { A } ph <-> [. A / x ]. ph ) ) $= f0_ralsns f1_ralsns f2_ralsns f3_ralsns p_sbc6g f0_ralsns f1_ralsns f2_ralsns a_csn a_df-ral f1_ralsns f2_ralsns p_elsn f1_ralsns a_sup_set_class f2_ralsns a_csn a_wcel f1_ralsns a_sup_set_class f2_ralsns a_wceq f0_ralsns p_imbi1i f1_ralsns a_sup_set_class f2_ralsns a_csn a_wcel f0_ralsns a_wi f1_ralsns a_sup_set_class f2_ralsns a_wceq f0_ralsns a_wi f1_ralsns p_albii f0_ralsns f1_ralsns f2_ralsns a_csn a_wral f1_ralsns a_sup_set_class f2_ralsns a_csn a_wcel f0_ralsns a_wi f1_ralsns a_wal f1_ralsns a_sup_set_class f2_ralsns a_wceq f0_ralsns a_wi f1_ralsns a_wal p_bitri f2_ralsns f3_ralsns a_wcel f0_ralsns f1_ralsns f2_ralsns a_wsbc f1_ralsns a_sup_set_class f2_ralsns a_wceq f0_ralsns a_wi f1_ralsns a_wal f0_ralsns f1_ralsns f2_ralsns a_csn a_wral p_syl6rbbr $.
$}

$(Restricted existential quantification over a singleton.  (Contributed by
       Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph x A V  $.
	$d A x  $.
	$d x  $.
	f0_rexsns $f wff ph $.
	f1_rexsns $f set x $.
	f2_rexsns $f class A $.
	f3_rexsns $f class V $.
	p_rexsns $p |- ( A e. V -> ( E. x e. { A } ph <-> [. A / x ]. ph ) ) $= f0_rexsns f1_rexsns f2_rexsns p_sbc5 f0_rexsns f1_rexsns f2_rexsns a_wsbc f1_rexsns a_sup_set_class f2_rexsns a_wceq f0_rexsns a_wa f1_rexsns a_wex a_wb f2_rexsns f3_rexsns a_wcel p_a1i f0_rexsns f1_rexsns f2_rexsns a_csn a_df-rex f1_rexsns f2_rexsns p_elsn f1_rexsns a_sup_set_class f2_rexsns a_csn a_wcel f1_rexsns a_sup_set_class f2_rexsns a_wceq f0_rexsns p_anbi1i f1_rexsns a_sup_set_class f2_rexsns a_csn a_wcel f0_rexsns a_wa f1_rexsns a_sup_set_class f2_rexsns a_wceq f0_rexsns a_wa f1_rexsns p_exbii f0_rexsns f1_rexsns f2_rexsns a_csn a_wrex f1_rexsns a_sup_set_class f2_rexsns a_csn a_wcel f0_rexsns a_wa f1_rexsns a_wex f1_rexsns a_sup_set_class f2_rexsns a_wceq f0_rexsns a_wa f1_rexsns a_wex p_bitri f2_rexsns f3_rexsns a_wcel f0_rexsns f1_rexsns f2_rexsns a_wsbc f1_rexsns a_sup_set_class f2_rexsns a_wceq f0_rexsns a_wa f1_rexsns a_wex f0_rexsns f1_rexsns f2_rexsns a_csn a_wrex p_syl6rbbr $.
$}

$(Substitution expressed in terms of quantification over a singleton.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       23-Apr-2015.) $)

${
	$v ph ps x A V  $.
	$d A x  $.
	$d ps x  $.
	f0_ralsng $f wff ph $.
	f1_ralsng $f wff ps $.
	f2_ralsng $f set x $.
	f3_ralsng $f class A $.
	f4_ralsng $f class V $.
	e0_ralsng $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ralsng $p |- ( A e. V -> ( A. x e. { A } ph <-> ps ) ) $= f0_ralsng f2_ralsng f3_ralsng f4_ralsng p_ralsns e0_ralsng f0_ralsng f1_ralsng f2_ralsng f3_ralsng f4_ralsng p_sbcieg f3_ralsng f4_ralsng a_wcel f0_ralsng f2_ralsng f3_ralsng a_csn a_wral f0_ralsng f2_ralsng f3_ralsng a_wsbc f1_ralsng p_bitrd $.
$}

$(Restricted existential quantification over a singleton.  (Contributed by
       NM, 29-Jan-2012.) $)

${
	$v ph ps x A V  $.
	$d A x  $.
	$d ps x  $.
	f0_rexsng $f wff ph $.
	f1_rexsng $f wff ps $.
	f2_rexsng $f set x $.
	f3_rexsng $f class A $.
	f4_rexsng $f class V $.
	e0_rexsng $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rexsng $p |- ( A e. V -> ( E. x e. { A } ph <-> ps ) ) $= f0_rexsng f2_rexsng f3_rexsng f4_rexsng p_rexsns e0_rexsng f0_rexsng f1_rexsng f2_rexsng f3_rexsng f4_rexsng p_sbcieg f3_rexsng f4_rexsng a_wcel f0_rexsng f2_rexsng f3_rexsng a_csn a_wrex f0_rexsng f2_rexsng f3_rexsng a_wsbc f1_rexsng p_bitrd $.
$}

$(Convert a quantification over a singleton to a substitution.
       (Contributed by NM, 27-Apr-2009.) $)

${
	$v ph ps x A  $.
	$d A x  $.
	$d ps x  $.
	f0_ralsn $f wff ph $.
	f1_ralsn $f wff ps $.
	f2_ralsn $f set x $.
	f3_ralsn $f class A $.
	e0_ralsn $e |- A e. _V $.
	e1_ralsn $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_ralsn $p |- ( A. x e. { A } ph <-> ps ) $= e0_ralsn e1_ralsn f0_ralsn f1_ralsn f2_ralsn f3_ralsn a_cvv p_ralsng f3_ralsn a_cvv a_wcel f0_ralsn f2_ralsn f3_ralsn a_csn a_wral f1_ralsn a_wb a_ax-mp $.
$}

$(Restricted existential quantification over a singleton.  (Contributed by
       Jeff Madsen, 5-Jan-2011.) $)

${
	$v ph ps x A  $.
	$d A x  $.
	$d ps x  $.
	f0_rexsn $f wff ph $.
	f1_rexsn $f wff ps $.
	f2_rexsn $f set x $.
	f3_rexsn $f class A $.
	e0_rexsn $e |- A e. _V $.
	e1_rexsn $e |- ( x = A -> ( ph <-> ps ) ) $.
	p_rexsn $p |- ( E. x e. { A } ph <-> ps ) $= e0_rexsn e1_rexsn f0_rexsn f1_rexsn f2_rexsn f3_rexsn a_cvv p_rexsng f3_rexsn a_cvv a_wcel f0_rexsn f2_rexsn f3_rexsn a_csn a_wrex f1_rexsn a_wb a_ax-mp $.
$}

$(Members of an unordered triple of classes.  (Contributed by FL,
       2-Feb-2014.)  (Proof shortened by Mario Carneiro, 11-Feb-2015.) $)

${
	$v A B C D V  $.
	f0_eltpg $f class A $.
	f1_eltpg $f class B $.
	f2_eltpg $f class C $.
	f3_eltpg $f class D $.
	f4_eltpg $f class V $.
	p_eltpg $p |- ( A e. V -> ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) ) ) $= f0_eltpg f1_eltpg f2_eltpg f4_eltpg p_elprg f0_eltpg f3_eltpg f4_eltpg p_elsncg f0_eltpg f4_eltpg a_wcel f0_eltpg f1_eltpg f2_eltpg a_cpr a_wcel f0_eltpg f1_eltpg a_wceq f0_eltpg f2_eltpg a_wceq a_wo f0_eltpg f3_eltpg a_csn a_wcel f0_eltpg f3_eltpg a_wceq p_orbi12d f1_eltpg f2_eltpg f3_eltpg a_df-tp f1_eltpg f2_eltpg f3_eltpg a_ctp f1_eltpg f2_eltpg a_cpr f3_eltpg a_csn a_cun f0_eltpg p_eleq2i f0_eltpg f1_eltpg f2_eltpg a_cpr f3_eltpg a_csn p_elun f0_eltpg f1_eltpg f2_eltpg f3_eltpg a_ctp a_wcel f0_eltpg f1_eltpg f2_eltpg a_cpr f3_eltpg a_csn a_cun a_wcel f0_eltpg f1_eltpg f2_eltpg a_cpr a_wcel f0_eltpg f3_eltpg a_csn a_wcel a_wo p_bitri f0_eltpg f1_eltpg a_wceq f0_eltpg f2_eltpg a_wceq f0_eltpg f3_eltpg a_wceq a_df-3or f0_eltpg f4_eltpg a_wcel f0_eltpg f1_eltpg f2_eltpg a_cpr a_wcel f0_eltpg f3_eltpg a_csn a_wcel a_wo f0_eltpg f1_eltpg a_wceq f0_eltpg f2_eltpg a_wceq a_wo f0_eltpg f3_eltpg a_wceq a_wo f0_eltpg f1_eltpg f2_eltpg f3_eltpg a_ctp a_wcel f0_eltpg f1_eltpg a_wceq f0_eltpg f2_eltpg a_wceq f0_eltpg f3_eltpg a_wceq a_w3o p_3bitr4g $.
$}

$(A member of an unordered triple of classes is one of them.  (Contributed
       by Mario Carneiro, 11-Feb-2015.) $)

${
	$v A B C D  $.
	f0_eltpi $f class A $.
	f1_eltpi $f class B $.
	f2_eltpi $f class C $.
	f3_eltpi $f class D $.
	p_eltpi $p |- ( A e. { B , C , D } -> ( A = B \/ A = C \/ A = D ) ) $= f0_eltpi f1_eltpi f2_eltpi f3_eltpi f1_eltpi f2_eltpi f3_eltpi a_ctp p_eltpg f0_eltpi f1_eltpi f2_eltpi f3_eltpi a_ctp a_wcel f0_eltpi f1_eltpi a_wceq f0_eltpi f2_eltpi a_wceq f0_eltpi f3_eltpi a_wceq a_w3o p_ibi $.
$}

$(A member of an unordered triple of classes is one of them.  Special case
       of Exercise 1 of [TakeutiZaring] p. 17.  (Contributed by NM,
       8-Apr-1994.)  (Revised by Mario Carneiro, 11-Feb-2015.) $)

${
	$v A B C D  $.
	f0_eltp $f class A $.
	f1_eltp $f class B $.
	f2_eltp $f class C $.
	f3_eltp $f class D $.
	e0_eltp $e |- A e. _V $.
	p_eltp $p |- ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) ) $= e0_eltp f0_eltp f1_eltp f2_eltp f3_eltp a_cvv p_eltpg f0_eltp a_cvv a_wcel f0_eltp f1_eltp f2_eltp f3_eltp a_ctp a_wcel f0_eltp f1_eltp a_wceq f0_eltp f2_eltp a_wceq f0_eltp f3_eltp a_wceq a_w3o a_wb a_ax-mp $.
$}

$(Alternate definition of unordered triple of classes.  Special case of
       Definition 5.3 of [TakeutiZaring] p. 16.  (Contributed by NM,
       8-Apr-1994.) $)

${
	$v x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_dftp2 $f set x $.
	f1_dftp2 $f class A $.
	f2_dftp2 $f class B $.
	f3_dftp2 $f class C $.
	p_dftp2 $p |- { A , B , C } = { x | ( x = A \/ x = B \/ x = C ) } $= f0_dftp2 p_vex f0_dftp2 a_sup_set_class f1_dftp2 f2_dftp2 f3_dftp2 p_eltp f0_dftp2 a_sup_set_class f1_dftp2 a_wceq f0_dftp2 a_sup_set_class f2_dftp2 a_wceq f0_dftp2 a_sup_set_class f3_dftp2 a_wceq a_w3o f0_dftp2 f1_dftp2 f2_dftp2 f3_dftp2 a_ctp p_abbi2i $.
$}

$(Bound-variable hypothesis builder for unordered pairs.  (Contributed by
       NM, 14-Nov-1995.) $)

${
	$v x A B  $.
	$d y A  $.
	$d y B  $.
	$d x y  $.
	f0_nfpr $f set x $.
	f1_nfpr $f class A $.
	f2_nfpr $f class B $.
	i0_nfpr $f set y $.
	e0_nfpr $e |- F/_ x A $.
	e1_nfpr $e |- F/_ x B $.
	p_nfpr $p |- F/_ x { A , B } $= i0_nfpr f1_nfpr f2_nfpr p_dfpr2 e0_nfpr f0_nfpr i0_nfpr a_sup_set_class f1_nfpr p_nfeq2 e1_nfpr f0_nfpr i0_nfpr a_sup_set_class f2_nfpr p_nfeq2 i0_nfpr a_sup_set_class f1_nfpr a_wceq i0_nfpr a_sup_set_class f2_nfpr a_wceq f0_nfpr p_nfor i0_nfpr a_sup_set_class f1_nfpr a_wceq i0_nfpr a_sup_set_class f2_nfpr a_wceq a_wo f0_nfpr i0_nfpr p_nfab f0_nfpr f1_nfpr f2_nfpr a_cpr i0_nfpr a_sup_set_class f1_nfpr a_wceq i0_nfpr a_sup_set_class f2_nfpr a_wceq a_wo i0_nfpr a_cab p_nfcxfr $.
$}

$(Membership of a conditional operator in an unordered pair.  (Contributed
     by NM, 17-Jun-2007.) $)

${
	$v ph A B C D  $.
	f0_ifpr $f wff ph $.
	f1_ifpr $f class A $.
	f2_ifpr $f class B $.
	f3_ifpr $f class C $.
	f4_ifpr $f class D $.
	p_ifpr $p |- ( ( A e. C /\ B e. D ) -> if ( ph , A , B ) e. { A , B } ) $= f1_ifpr f3_ifpr p_elex f2_ifpr f4_ifpr p_elex f0_ifpr f1_ifpr f2_ifpr a_cvv p_ifcl f0_ifpr f1_ifpr f2_ifpr p_ifeqor f0_ifpr f1_ifpr f2_ifpr a_cif f1_ifpr f2_ifpr a_cvv p_elprg f0_ifpr f1_ifpr f2_ifpr a_cif a_cvv a_wcel f0_ifpr f1_ifpr f2_ifpr a_cif f1_ifpr f2_ifpr a_cpr a_wcel f0_ifpr f1_ifpr f2_ifpr a_cif f1_ifpr a_wceq f0_ifpr f1_ifpr f2_ifpr a_cif f2_ifpr a_wceq a_wo p_mpbiri f1_ifpr a_cvv a_wcel f2_ifpr a_cvv a_wcel a_wa f0_ifpr f1_ifpr f2_ifpr a_cif a_cvv a_wcel f0_ifpr f1_ifpr f2_ifpr a_cif f1_ifpr f2_ifpr a_cpr a_wcel p_syl f1_ifpr f3_ifpr a_wcel f1_ifpr a_cvv a_wcel f2_ifpr a_cvv a_wcel f0_ifpr f1_ifpr f2_ifpr a_cif f1_ifpr f2_ifpr a_cpr a_wcel f2_ifpr f4_ifpr a_wcel p_syl2an $.
$}

$(Convert a quantification over a pair to a conjunction.  (Contributed by
       NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch x A B V W  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	$d x ps  $.
	$d x ch  $.
	$d x  $.
	f0_ralprg $f wff ph $.
	f1_ralprg $f wff ps $.
	f2_ralprg $f wff ch $.
	f3_ralprg $f set x $.
	f4_ralprg $f class A $.
	f5_ralprg $f class B $.
	f6_ralprg $f class V $.
	f7_ralprg $f class W $.
	e0_ralprg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_ralprg $e |- ( x = B -> ( ph <-> ch ) ) $.
	p_ralprg $p |- ( ( A e. V /\ B e. W ) -> ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) ) $= f4_ralprg f5_ralprg a_df-pr f0_ralprg f3_ralprg f4_ralprg f5_ralprg a_cpr f4_ralprg a_csn f5_ralprg a_csn a_cun p_raleqi f0_ralprg f3_ralprg f4_ralprg a_csn f5_ralprg a_csn p_ralunb f0_ralprg f3_ralprg f4_ralprg f5_ralprg a_cpr a_wral f0_ralprg f3_ralprg f4_ralprg a_csn f5_ralprg a_csn a_cun a_wral f0_ralprg f3_ralprg f4_ralprg a_csn a_wral f0_ralprg f3_ralprg f5_ralprg a_csn a_wral a_wa p_bitri e0_ralprg f0_ralprg f1_ralprg f3_ralprg f4_ralprg f6_ralprg p_ralsng e1_ralprg f0_ralprg f2_ralprg f3_ralprg f5_ralprg f7_ralprg p_ralsng f4_ralprg f6_ralprg a_wcel f0_ralprg f3_ralprg f4_ralprg a_csn a_wral f1_ralprg f5_ralprg f7_ralprg a_wcel f0_ralprg f3_ralprg f5_ralprg a_csn a_wral f2_ralprg p_bi2anan9 f0_ralprg f3_ralprg f4_ralprg f5_ralprg a_cpr a_wral f0_ralprg f3_ralprg f4_ralprg a_csn a_wral f0_ralprg f3_ralprg f5_ralprg a_csn a_wral a_wa f4_ralprg f6_ralprg a_wcel f5_ralprg f7_ralprg a_wcel a_wa f1_ralprg f2_ralprg a_wa p_syl5bb $.
$}

$(Convert a quantification over a pair to a disjunction.  (Contributed by
       NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch x A B V W  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	$d x ps  $.
	$d x ch  $.
	$d x  $.
	f0_rexprg $f wff ph $.
	f1_rexprg $f wff ps $.
	f2_rexprg $f wff ch $.
	f3_rexprg $f set x $.
	f4_rexprg $f class A $.
	f5_rexprg $f class B $.
	f6_rexprg $f class V $.
	f7_rexprg $f class W $.
	e0_rexprg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_rexprg $e |- ( x = B -> ( ph <-> ch ) ) $.
	p_rexprg $p |- ( ( A e. V /\ B e. W ) -> ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) ) $= f4_rexprg f5_rexprg a_df-pr f0_rexprg f3_rexprg f4_rexprg f5_rexprg a_cpr f4_rexprg a_csn f5_rexprg a_csn a_cun p_rexeqi f0_rexprg f3_rexprg f4_rexprg a_csn f5_rexprg a_csn p_rexun f0_rexprg f3_rexprg f4_rexprg f5_rexprg a_cpr a_wrex f0_rexprg f3_rexprg f4_rexprg a_csn f5_rexprg a_csn a_cun a_wrex f0_rexprg f3_rexprg f4_rexprg a_csn a_wrex f0_rexprg f3_rexprg f5_rexprg a_csn a_wrex a_wo p_bitri e0_rexprg f0_rexprg f1_rexprg f3_rexprg f4_rexprg f6_rexprg p_rexsng f4_rexprg f6_rexprg a_wcel f0_rexprg f3_rexprg f4_rexprg a_csn a_wrex f1_rexprg f0_rexprg f3_rexprg f5_rexprg a_csn a_wrex p_orbi1d e1_rexprg f0_rexprg f2_rexprg f3_rexprg f5_rexprg f7_rexprg p_rexsng f5_rexprg f7_rexprg a_wcel f0_rexprg f3_rexprg f5_rexprg a_csn a_wrex f2_rexprg f1_rexprg p_orbi2d f4_rexprg f6_rexprg a_wcel f0_rexprg f3_rexprg f4_rexprg a_csn a_wrex f0_rexprg f3_rexprg f5_rexprg a_csn a_wrex a_wo f1_rexprg f0_rexprg f3_rexprg f5_rexprg a_csn a_wrex a_wo f5_rexprg f7_rexprg a_wcel f1_rexprg f2_rexprg a_wo p_sylan9bb f0_rexprg f3_rexprg f4_rexprg f5_rexprg a_cpr a_wrex f0_rexprg f3_rexprg f4_rexprg a_csn a_wrex f0_rexprg f3_rexprg f5_rexprg a_csn a_wrex a_wo f4_rexprg f6_rexprg a_wcel f5_rexprg f7_rexprg a_wcel a_wa f1_rexprg f2_rexprg a_wo p_syl5bb $.
$}

$(Convert a quantification over a triple to a conjunction.  (Contributed
       by NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch th x A B C V W X  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	f0_raltpg $f wff ph $.
	f1_raltpg $f wff ps $.
	f2_raltpg $f wff ch $.
	f3_raltpg $f wff th $.
	f4_raltpg $f set x $.
	f5_raltpg $f class A $.
	f6_raltpg $f class B $.
	f7_raltpg $f class C $.
	f8_raltpg $f class V $.
	f9_raltpg $f class W $.
	f10_raltpg $f class X $.
	e0_raltpg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_raltpg $e |- ( x = B -> ( ph <-> ch ) ) $.
	e2_raltpg $e |- ( x = C -> ( ph <-> th ) ) $.
	p_raltpg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) ) $= e0_raltpg e1_raltpg f0_raltpg f1_raltpg f2_raltpg f4_raltpg f5_raltpg f6_raltpg f8_raltpg f9_raltpg p_ralprg e2_raltpg f0_raltpg f3_raltpg f4_raltpg f7_raltpg f10_raltpg p_ralsng f5_raltpg f8_raltpg a_wcel f6_raltpg f9_raltpg a_wcel a_wa f0_raltpg f4_raltpg f5_raltpg f6_raltpg a_cpr a_wral f1_raltpg f2_raltpg a_wa f7_raltpg f10_raltpg a_wcel f0_raltpg f4_raltpg f7_raltpg a_csn a_wral f3_raltpg p_bi2anan9 f5_raltpg f8_raltpg a_wcel f6_raltpg f9_raltpg a_wcel f7_raltpg f10_raltpg a_wcel f0_raltpg f4_raltpg f5_raltpg f6_raltpg a_cpr a_wral f0_raltpg f4_raltpg f7_raltpg a_csn a_wral a_wa f1_raltpg f2_raltpg a_wa f3_raltpg a_wa a_wb p_3impa f5_raltpg f6_raltpg f7_raltpg a_df-tp f0_raltpg f4_raltpg f5_raltpg f6_raltpg f7_raltpg a_ctp f5_raltpg f6_raltpg a_cpr f7_raltpg a_csn a_cun p_raleqi f0_raltpg f4_raltpg f5_raltpg f6_raltpg a_cpr f7_raltpg a_csn p_ralunb f0_raltpg f4_raltpg f5_raltpg f6_raltpg f7_raltpg a_ctp a_wral f0_raltpg f4_raltpg f5_raltpg f6_raltpg a_cpr f7_raltpg a_csn a_cun a_wral f0_raltpg f4_raltpg f5_raltpg f6_raltpg a_cpr a_wral f0_raltpg f4_raltpg f7_raltpg a_csn a_wral a_wa p_bitri f1_raltpg f2_raltpg f3_raltpg a_df-3an f5_raltpg f8_raltpg a_wcel f6_raltpg f9_raltpg a_wcel f7_raltpg f10_raltpg a_wcel a_w3a f0_raltpg f4_raltpg f5_raltpg f6_raltpg a_cpr a_wral f0_raltpg f4_raltpg f7_raltpg a_csn a_wral a_wa f1_raltpg f2_raltpg a_wa f3_raltpg a_wa f0_raltpg f4_raltpg f5_raltpg f6_raltpg f7_raltpg a_ctp a_wral f1_raltpg f2_raltpg f3_raltpg a_w3a p_3bitr4g $.
$}

$(Convert a quantification over a triple to a disjunction.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch th x A B C V W X  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	f0_rextpg $f wff ph $.
	f1_rextpg $f wff ps $.
	f2_rextpg $f wff ch $.
	f3_rextpg $f wff th $.
	f4_rextpg $f set x $.
	f5_rextpg $f class A $.
	f6_rextpg $f class B $.
	f7_rextpg $f class C $.
	f8_rextpg $f class V $.
	f9_rextpg $f class W $.
	f10_rextpg $f class X $.
	e0_rextpg $e |- ( x = A -> ( ph <-> ps ) ) $.
	e1_rextpg $e |- ( x = B -> ( ph <-> ch ) ) $.
	e2_rextpg $e |- ( x = C -> ( ph <-> th ) ) $.
	p_rextpg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) ) $= e0_rextpg e1_rextpg f0_rextpg f1_rextpg f2_rextpg f4_rextpg f5_rextpg f6_rextpg f8_rextpg f9_rextpg p_rexprg f5_rextpg f8_rextpg a_wcel f6_rextpg f9_rextpg a_wcel a_wa f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr a_wrex f1_rextpg f2_rextpg a_wo f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex p_orbi1d e2_rextpg f0_rextpg f3_rextpg f4_rextpg f7_rextpg f10_rextpg p_rexsng f7_rextpg f10_rextpg a_wcel f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex f3_rextpg f1_rextpg f2_rextpg a_wo p_orbi2d f5_rextpg f8_rextpg a_wcel f6_rextpg f9_rextpg a_wcel a_wa f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr a_wrex f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex a_wo f1_rextpg f2_rextpg a_wo f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex a_wo f7_rextpg f10_rextpg a_wcel f1_rextpg f2_rextpg a_wo f3_rextpg a_wo p_sylan9bb f5_rextpg f8_rextpg a_wcel f6_rextpg f9_rextpg a_wcel f7_rextpg f10_rextpg a_wcel f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr a_wrex f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex a_wo f1_rextpg f2_rextpg a_wo f3_rextpg a_wo a_wb p_3impa f5_rextpg f6_rextpg f7_rextpg a_df-tp f0_rextpg f4_rextpg f5_rextpg f6_rextpg f7_rextpg a_ctp f5_rextpg f6_rextpg a_cpr f7_rextpg a_csn a_cun p_rexeqi f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr f7_rextpg a_csn p_rexun f0_rextpg f4_rextpg f5_rextpg f6_rextpg f7_rextpg a_ctp a_wrex f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr f7_rextpg a_csn a_cun a_wrex f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr a_wrex f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex a_wo p_bitri f1_rextpg f2_rextpg f3_rextpg a_df-3or f5_rextpg f8_rextpg a_wcel f6_rextpg f9_rextpg a_wcel f7_rextpg f10_rextpg a_wcel a_w3a f0_rextpg f4_rextpg f5_rextpg f6_rextpg a_cpr a_wrex f0_rextpg f4_rextpg f7_rextpg a_csn a_wrex a_wo f1_rextpg f2_rextpg a_wo f3_rextpg a_wo f0_rextpg f4_rextpg f5_rextpg f6_rextpg f7_rextpg a_ctp a_wrex f1_rextpg f2_rextpg f3_rextpg a_w3o p_3bitr4g $.
$}

$(Convert a quantification over a pair to a conjunction.  (Contributed by
       NM, 3-Jun-2007.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	$d x ch  $.
	f0_ralpr $f wff ph $.
	f1_ralpr $f wff ps $.
	f2_ralpr $f wff ch $.
	f3_ralpr $f set x $.
	f4_ralpr $f class A $.
	f5_ralpr $f class B $.
	e0_ralpr $e |- A e. _V $.
	e1_ralpr $e |- B e. _V $.
	e2_ralpr $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_ralpr $e |- ( x = B -> ( ph <-> ch ) ) $.
	p_ralpr $p |- ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) $= e0_ralpr e1_ralpr e2_ralpr e3_ralpr f0_ralpr f1_ralpr f2_ralpr f3_ralpr f4_ralpr f5_ralpr a_cvv a_cvv p_ralprg f4_ralpr a_cvv a_wcel f5_ralpr a_cvv a_wcel f0_ralpr f3_ralpr f4_ralpr f5_ralpr a_cpr a_wral f1_ralpr f2_ralpr a_wa a_wb p_mp2an $.
$}

$(Convert an existential quantification over a pair to a disjunction.
       (Contributed by NM, 3-Jun-2007.)  (Revised by Mario Carneiro,
       23-Apr-2015.) $)

${
	$v ph ps ch x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	$d x ch  $.
	f0_rexpr $f wff ph $.
	f1_rexpr $f wff ps $.
	f2_rexpr $f wff ch $.
	f3_rexpr $f set x $.
	f4_rexpr $f class A $.
	f5_rexpr $f class B $.
	e0_rexpr $e |- A e. _V $.
	e1_rexpr $e |- B e. _V $.
	e2_rexpr $e |- ( x = A -> ( ph <-> ps ) ) $.
	e3_rexpr $e |- ( x = B -> ( ph <-> ch ) ) $.
	p_rexpr $p |- ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) $= e0_rexpr e1_rexpr e2_rexpr e3_rexpr f0_rexpr f1_rexpr f2_rexpr f3_rexpr f4_rexpr f5_rexpr a_cvv a_cvv p_rexprg f4_rexpr a_cvv a_wcel f5_rexpr a_cvv a_wcel f0_rexpr f3_rexpr f4_rexpr f5_rexpr a_cpr a_wrex f1_rexpr f2_rexpr a_wo a_wb p_mp2an $.
$}

$(Convert a quantification over a triple to a conjunction.  (Contributed
       by NM, 13-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch th x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	f0_raltp $f wff ph $.
	f1_raltp $f wff ps $.
	f2_raltp $f wff ch $.
	f3_raltp $f wff th $.
	f4_raltp $f set x $.
	f5_raltp $f class A $.
	f6_raltp $f class B $.
	f7_raltp $f class C $.
	e0_raltp $e |- A e. _V $.
	e1_raltp $e |- B e. _V $.
	e2_raltp $e |- C e. _V $.
	e3_raltp $e |- ( x = A -> ( ph <-> ps ) ) $.
	e4_raltp $e |- ( x = B -> ( ph <-> ch ) ) $.
	e5_raltp $e |- ( x = C -> ( ph <-> th ) ) $.
	p_raltp $p |- ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) $= e0_raltp e1_raltp e2_raltp e3_raltp e4_raltp e5_raltp f0_raltp f1_raltp f2_raltp f3_raltp f4_raltp f5_raltp f6_raltp f7_raltp a_cvv a_cvv a_cvv p_raltpg f5_raltp a_cvv a_wcel f6_raltp a_cvv a_wcel f7_raltp a_cvv a_wcel f0_raltp f4_raltp f5_raltp f6_raltp f7_raltp a_ctp a_wral f1_raltp f2_raltp f3_raltp a_w3a a_wb p_mp3an $.
$}

$(Convert a quantification over a triple to a disjunction.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps ch th x A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x ps  $.
	$d x ch  $.
	$d x th  $.
	f0_rextp $f wff ph $.
	f1_rextp $f wff ps $.
	f2_rextp $f wff ch $.
	f3_rextp $f wff th $.
	f4_rextp $f set x $.
	f5_rextp $f class A $.
	f6_rextp $f class B $.
	f7_rextp $f class C $.
	e0_rextp $e |- A e. _V $.
	e1_rextp $e |- B e. _V $.
	e2_rextp $e |- C e. _V $.
	e3_rextp $e |- ( x = A -> ( ph <-> ps ) ) $.
	e4_rextp $e |- ( x = B -> ( ph <-> ch ) ) $.
	e5_rextp $e |- ( x = C -> ( ph <-> th ) ) $.
	p_rextp $p |- ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) $= e0_rextp e1_rextp e2_rextp e3_rextp e4_rextp e5_rextp f0_rextp f1_rextp f2_rextp f3_rextp f4_rextp f5_rextp f6_rextp f7_rextp a_cvv a_cvv a_cvv p_rextpg f5_rextp a_cvv a_wcel f6_rextp a_cvv a_wcel f7_rextp a_cvv a_wcel f0_rextp f4_rextp f5_rextp f6_rextp f7_rextp a_ctp a_wrex f1_rextp f2_rextp f3_rextp a_w3o a_wb p_mp3an $.
$}

$(TODO - make obsolete; use ralsnsSBC instead - also,
       shorten posn w/ ralsn or ralsng $)

$(Substitution expressed in terms of quantification over a singleton.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       23-Apr-2015.) $)

${
	$v ph x A V  $.
	$d x A  $.
	$d ph  $.
	f0_sbcsng $f wff ph $.
	f1_sbcsng $f set x $.
	f2_sbcsng $f class A $.
	f3_sbcsng $f class V $.
	p_sbcsng $p |- ( A e. V -> ( [. A / x ]. ph <-> A. x e. { A } ph ) ) $= f0_sbcsng f1_sbcsng f2_sbcsng f3_sbcsng p_ralsns f2_sbcsng f3_sbcsng a_wcel f0_sbcsng f1_sbcsng f2_sbcsng a_csn a_wral f0_sbcsng f1_sbcsng f2_sbcsng a_wsbc p_bicomd $.
$}

$(Bound-variable hypothesis builder for singletons.  (Contributed by NM,
       14-Nov-1995.) $)

${
	$v x A  $.
	f0_nfsn $f set x $.
	f1_nfsn $f class A $.
	e0_nfsn $e |- F/_ x A $.
	p_nfsn $p |- F/_ x { A } $= f1_nfsn p_dfsn2 e0_nfsn e0_nfsn f0_nfsn f1_nfsn f1_nfsn p_nfpr f0_nfsn f1_nfsn a_csn f1_nfsn f1_nfsn a_cpr p_nfcxfr $.
$}

$(Distribute proper substitution through the singleton of a class.
       ~ csbsng is derived from the virtual deduction proof ~ csbsngVD .
       (Contributed by Alan Sare, 10-Nov-2012.) $)

${
	$v x A B V  $.
	$d A y  $.
	$d B y  $.
	$d V y  $.
	$d x y  $.
	f0_csbsng $f set x $.
	f1_csbsng $f class A $.
	f2_csbsng $f class B $.
	f3_csbsng $f class V $.
	i0_csbsng $f set y $.
	p_csbsng $p |- ( A e. V -> [_ A / x ]_ { B } = { [_ A / x ]_ B } ) $= i0_csbsng a_sup_set_class f2_csbsng a_wceq f0_csbsng i0_csbsng f1_csbsng f3_csbsng p_csbabg f0_csbsng f1_csbsng i0_csbsng a_sup_set_class f2_csbsng f3_csbsng p_sbceq2g f1_csbsng f3_csbsng a_wcel i0_csbsng a_sup_set_class f2_csbsng a_wceq f0_csbsng f1_csbsng a_wsbc i0_csbsng a_sup_set_class f0_csbsng f1_csbsng f2_csbsng a_csb a_wceq i0_csbsng p_abbidv f1_csbsng f3_csbsng a_wcel f0_csbsng f1_csbsng i0_csbsng a_sup_set_class f2_csbsng a_wceq i0_csbsng a_cab a_csb i0_csbsng a_sup_set_class f2_csbsng a_wceq f0_csbsng f1_csbsng a_wsbc i0_csbsng a_cab i0_csbsng a_sup_set_class f0_csbsng f1_csbsng f2_csbsng a_csb a_wceq i0_csbsng a_cab p_eqtrd i0_csbsng f2_csbsng a_df-sn f0_csbsng f1_csbsng f2_csbsng a_csn i0_csbsng a_sup_set_class f2_csbsng a_wceq i0_csbsng a_cab p_csbeq2i i0_csbsng f0_csbsng f1_csbsng f2_csbsng a_csb a_df-sn f1_csbsng f3_csbsng a_wcel f0_csbsng f1_csbsng i0_csbsng a_sup_set_class f2_csbsng a_wceq i0_csbsng a_cab a_csb i0_csbsng a_sup_set_class f0_csbsng f1_csbsng f2_csbsng a_csb a_wceq i0_csbsng a_cab f0_csbsng f1_csbsng f2_csbsng a_csn a_csb f0_csbsng f1_csbsng f2_csbsng a_csb a_csn p_3eqtr4g $.
$}

$(Intersection with the singleton of a non-member is disjoint.
       (Contributed by NM, 22-May-1998.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.)  (Proof shortened by Wolf Lammen, 30-Sep-2014.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_disjsn $f class A $.
	f1_disjsn $f class B $.
	i0_disjsn $f set x $.
	p_disjsn $p |- ( ( A i^i { B } ) = (/) <-> -. B e. A ) $= i0_disjsn f0_disjsn f1_disjsn a_csn p_disj1 i0_disjsn a_sup_set_class f0_disjsn a_wcel i0_disjsn a_sup_set_class f1_disjsn a_csn a_wcel p_con2b i0_disjsn f1_disjsn p_elsn i0_disjsn a_sup_set_class f1_disjsn a_csn a_wcel i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wn p_imbi1i i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel p_imnan i0_disjsn a_sup_set_class f0_disjsn a_wcel i0_disjsn a_sup_set_class f1_disjsn a_csn a_wcel a_wn a_wi i0_disjsn a_sup_set_class f1_disjsn a_csn a_wcel i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wn a_wi i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wn a_wi i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wa a_wn p_3bitri i0_disjsn a_sup_set_class f0_disjsn a_wcel i0_disjsn a_sup_set_class f1_disjsn a_csn a_wcel a_wn a_wi i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wa a_wn i0_disjsn p_albii i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wa i0_disjsn p_alnex i0_disjsn f1_disjsn f0_disjsn a_df-clel i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wa a_wn i0_disjsn a_wal i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wa i0_disjsn a_wex f1_disjsn f0_disjsn a_wcel p_xchbinxr f0_disjsn f1_disjsn a_csn a_cin a_c0 a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel i0_disjsn a_sup_set_class f1_disjsn a_csn a_wcel a_wn a_wi i0_disjsn a_wal i0_disjsn a_sup_set_class f1_disjsn a_wceq i0_disjsn a_sup_set_class f0_disjsn a_wcel a_wa a_wn i0_disjsn a_wal f1_disjsn f0_disjsn a_wcel a_wn p_3bitri $.
$}

$(Intersection of distinct singletons is disjoint.  (Contributed by NM,
     25-May-1998.) $)

${
	$v A B  $.
	f0_disjsn2 $f class A $.
	f1_disjsn2 $f class B $.
	p_disjsn2 $p |- ( A =/= B -> ( { A } i^i { B } ) = (/) ) $= f1_disjsn2 f0_disjsn2 p_elsni f1_disjsn2 f0_disjsn2 a_csn a_wcel f1_disjsn2 f0_disjsn2 p_eqcomd f1_disjsn2 f0_disjsn2 a_csn a_wcel f0_disjsn2 f1_disjsn2 p_necon3ai f0_disjsn2 a_csn f1_disjsn2 p_disjsn f0_disjsn2 f1_disjsn2 a_wne f1_disjsn2 f0_disjsn2 a_csn a_wcel a_wn f0_disjsn2 a_csn f1_disjsn2 a_csn a_cin a_c0 a_wceq p_sylibr $.
$}

$(The singleton of a proper class (one that doesn't exist) is the empty
       set.  Theorem 7.2 of [Quine] p. 48.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d x A  $.
	f0_snprc $f class A $.
	i0_snprc $f set x $.
	p_snprc $p |- ( -. A e. _V <-> { A } = (/) ) $= i0_snprc f0_snprc p_elsn i0_snprc a_sup_set_class f0_snprc a_csn a_wcel i0_snprc a_sup_set_class f0_snprc a_wceq i0_snprc p_exbii i0_snprc f0_snprc a_csn p_neq0 i0_snprc f0_snprc p_isset i0_snprc a_sup_set_class f0_snprc a_csn a_wcel i0_snprc a_wex i0_snprc a_sup_set_class f0_snprc a_wceq i0_snprc a_wex f0_snprc a_csn a_c0 a_wceq a_wn f0_snprc a_cvv a_wcel p_3bitr4i f0_snprc a_csn a_c0 a_wceq f0_snprc a_cvv a_wcel p_con1bii $.
$}

$(Special case of ~ r19.12 where its converse holds.  (Contributed by NM,
       19-May-2008.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph x y A B  $.
	$d x y A  $.
	$d x B  $.
	f0_r19.12sn $f wff ph $.
	f1_r19.12sn $f set x $.
	f2_r19.12sn $f set y $.
	f3_r19.12sn $f class A $.
	f4_r19.12sn $f class B $.
	e0_r19.12sn $e |- A e. _V $.
	p_r19.12sn $p |- ( E. x e. { A } A. y e. B ph <-> A. y e. B E. x e. { A } ph ) $= e0_r19.12sn f0_r19.12sn f1_r19.12sn f2_r19.12sn f3_r19.12sn f4_r19.12sn a_cvv p_sbcralg f0_r19.12sn f2_r19.12sn f4_r19.12sn a_wral f1_r19.12sn f3_r19.12sn a_cvv p_rexsns f0_r19.12sn f1_r19.12sn f3_r19.12sn a_cvv p_rexsns f3_r19.12sn a_cvv a_wcel f0_r19.12sn f1_r19.12sn f3_r19.12sn a_csn a_wrex f0_r19.12sn f1_r19.12sn f3_r19.12sn a_wsbc f2_r19.12sn f4_r19.12sn p_ralbidv f3_r19.12sn a_cvv a_wcel f0_r19.12sn f2_r19.12sn f4_r19.12sn a_wral f1_r19.12sn f3_r19.12sn a_wsbc f0_r19.12sn f1_r19.12sn f3_r19.12sn a_wsbc f2_r19.12sn f4_r19.12sn a_wral f0_r19.12sn f2_r19.12sn f4_r19.12sn a_wral f1_r19.12sn f3_r19.12sn a_csn a_wrex f0_r19.12sn f1_r19.12sn f3_r19.12sn a_csn a_wrex f2_r19.12sn f4_r19.12sn a_wral p_3bitr4d f3_r19.12sn a_cvv a_wcel f0_r19.12sn f2_r19.12sn f4_r19.12sn a_wral f1_r19.12sn f3_r19.12sn a_csn a_wrex f0_r19.12sn f1_r19.12sn f3_r19.12sn a_csn a_wrex f2_r19.12sn f4_r19.12sn a_wral a_wb a_ax-mp $.
$}

$(Condition where a restricted class abstraction is a singleton.
       (Contributed by NM, 28-May-2006.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_rabsn $f set x $.
	f1_rabsn $f class A $.
	f2_rabsn $f class B $.
	p_rabsn $p |- ( B e. A -> { x e. A | x = B } = { B } ) $= f0_rabsn a_sup_set_class f2_rabsn f1_rabsn p_eleq1 f0_rabsn a_sup_set_class f2_rabsn a_wceq f0_rabsn a_sup_set_class f1_rabsn a_wcel f2_rabsn f1_rabsn a_wcel p_pm5.32ri f0_rabsn a_sup_set_class f1_rabsn a_wcel f0_rabsn a_sup_set_class f2_rabsn a_wceq a_wa f2_rabsn f1_rabsn a_wcel f0_rabsn a_sup_set_class f2_rabsn a_wceq p_baib f2_rabsn f1_rabsn a_wcel f0_rabsn a_sup_set_class f1_rabsn a_wcel f0_rabsn a_sup_set_class f2_rabsn a_wceq a_wa f0_rabsn a_sup_set_class f2_rabsn a_wceq f0_rabsn p_abbidv f0_rabsn a_sup_set_class f2_rabsn a_wceq f0_rabsn f1_rabsn a_df-rab f0_rabsn f2_rabsn a_df-sn f2_rabsn f1_rabsn a_wcel f0_rabsn a_sup_set_class f1_rabsn a_wcel f0_rabsn a_sup_set_class f2_rabsn a_wceq a_wa f0_rabsn a_cab f0_rabsn a_sup_set_class f2_rabsn a_wceq f0_rabsn a_cab f0_rabsn a_sup_set_class f2_rabsn a_wceq f0_rabsn f1_rabsn a_crab f2_rabsn a_csn p_3eqtr4g $.
$}

$(Another way to express existential uniqueness of a wff: its class
       abstraction is a singleton.  (Contributed by Mario Carneiro,
       14-Nov-2016.) $)

${
	$v ph x y  $.
	$d x y  $.
	$d y ph  $.
	$d y  $.
	f0_euabsn2 $f wff ph $.
	f1_euabsn2 $f set x $.
	f2_euabsn2 $f set y $.
	p_euabsn2 $p |- ( E! x ph <-> E. y { x | ph } = { y } ) $= f0_euabsn2 f1_euabsn2 f2_euabsn2 a_df-eu f0_euabsn2 f1_euabsn2 f2_euabsn2 a_sup_set_class a_csn p_abeq1 f1_euabsn2 f2_euabsn2 a_sup_set_class p_elsn f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_csn a_wcel f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_wceq f0_euabsn2 p_bibi2i f0_euabsn2 f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_csn a_wcel a_wb f0_euabsn2 f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_wceq a_wb f1_euabsn2 p_albii f0_euabsn2 f1_euabsn2 a_cab f2_euabsn2 a_sup_set_class a_csn a_wceq f0_euabsn2 f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_csn a_wcel a_wb f1_euabsn2 a_wal f0_euabsn2 f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_wceq a_wb f1_euabsn2 a_wal p_bitri f0_euabsn2 f1_euabsn2 a_cab f2_euabsn2 a_sup_set_class a_csn a_wceq f0_euabsn2 f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_wceq a_wb f1_euabsn2 a_wal f2_euabsn2 p_exbii f0_euabsn2 f1_euabsn2 a_weu f0_euabsn2 f1_euabsn2 a_sup_set_class f2_euabsn2 a_sup_set_class a_wceq a_wb f1_euabsn2 a_wal f2_euabsn2 a_wex f0_euabsn2 f1_euabsn2 a_cab f2_euabsn2 a_sup_set_class a_csn a_wceq f2_euabsn2 a_wex p_bitr4i $.
$}

$(Another way to express existential uniqueness of a wff: its class
       abstraction is a singleton.  (Contributed by NM, 22-Feb-2004.) $)

${
	$v ph x  $.
	$d x y  $.
	$d y ph  $.
	$d y  $.
	f0_euabsn $f wff ph $.
	f1_euabsn $f set x $.
	i0_euabsn $f set y $.
	p_euabsn $p |- ( E! x ph <-> E. x { x | ph } = { x } ) $= f0_euabsn f1_euabsn i0_euabsn p_euabsn2 f0_euabsn f1_euabsn a_cab f1_euabsn a_sup_set_class a_csn a_wceq i0_euabsn p_nfv f0_euabsn f1_euabsn p_nfab1 f1_euabsn f0_euabsn f1_euabsn a_cab i0_euabsn a_sup_set_class a_csn p_nfeq1 f1_euabsn a_sup_set_class i0_euabsn a_sup_set_class p_sneq f1_euabsn a_sup_set_class i0_euabsn a_sup_set_class a_wceq f1_euabsn a_sup_set_class a_csn i0_euabsn a_sup_set_class a_csn f0_euabsn f1_euabsn a_cab p_eqeq2d f0_euabsn f1_euabsn a_cab f1_euabsn a_sup_set_class a_csn a_wceq f0_euabsn f1_euabsn a_cab i0_euabsn a_sup_set_class a_csn a_wceq f1_euabsn i0_euabsn p_cbvex f0_euabsn f1_euabsn a_weu f0_euabsn f1_euabsn a_cab i0_euabsn a_sup_set_class a_csn a_wceq i0_euabsn a_wex f0_euabsn f1_euabsn a_cab f1_euabsn a_sup_set_class a_csn a_wceq f1_euabsn a_wex p_bitr4i $.
$}

$(A way to express restricted existential uniqueness of a wff: its
       restricted class abstraction is a singleton.  (Contributed by NM,
       30-May-2006.)  (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)

${
	$v ph x y A  $.
	$d x y  $.
	$d y ph  $.
	$d y A  $.
	f0_reusn $f wff ph $.
	f1_reusn $f set x $.
	f2_reusn $f set y $.
	f3_reusn $f class A $.
	p_reusn $p |- ( E! x e. A ph <-> E. y { x e. A | ph } = { y } ) $= f1_reusn a_sup_set_class f3_reusn a_wcel f0_reusn a_wa f1_reusn f2_reusn p_euabsn2 f0_reusn f1_reusn f3_reusn a_df-reu f0_reusn f1_reusn f3_reusn a_df-rab f0_reusn f1_reusn f3_reusn a_crab f1_reusn a_sup_set_class f3_reusn a_wcel f0_reusn a_wa f1_reusn a_cab f2_reusn a_sup_set_class a_csn p_eqeq1i f0_reusn f1_reusn f3_reusn a_crab f2_reusn a_sup_set_class a_csn a_wceq f1_reusn a_sup_set_class f3_reusn a_wcel f0_reusn a_wa f1_reusn a_cab f2_reusn a_sup_set_class a_csn a_wceq f2_reusn p_exbii f1_reusn a_sup_set_class f3_reusn a_wcel f0_reusn a_wa f1_reusn a_weu f1_reusn a_sup_set_class f3_reusn a_wcel f0_reusn a_wa f1_reusn a_cab f2_reusn a_sup_set_class a_csn a_wceq f2_reusn a_wex f0_reusn f1_reusn f3_reusn a_wreu f0_reusn f1_reusn f3_reusn a_crab f2_reusn a_sup_set_class a_csn a_wceq f2_reusn a_wex p_3bitr4i $.
$}

$(Restricted existential uniqueness determined by a singleton.
       (Contributed by NM, 29-May-2006.) $)

${
	$v ph x A V  $.
	$d x y  $.
	$d y ph  $.
	$d y A  $.
	f0_absneu $f wff ph $.
	f1_absneu $f set x $.
	f2_absneu $f class A $.
	f3_absneu $f class V $.
	i0_absneu $f set y $.
	p_absneu $p |- ( ( A e. V /\ { x | ph } = { A } ) -> E! x ph ) $= i0_absneu a_sup_set_class f2_absneu p_sneq i0_absneu a_sup_set_class f2_absneu a_wceq i0_absneu a_sup_set_class a_csn f2_absneu a_csn f0_absneu f1_absneu a_cab p_eqeq2d f0_absneu f1_absneu a_cab i0_absneu a_sup_set_class a_csn a_wceq f0_absneu f1_absneu a_cab f2_absneu a_csn a_wceq i0_absneu f2_absneu f3_absneu p_spcegv f2_absneu f3_absneu a_wcel f0_absneu f1_absneu a_cab f2_absneu a_csn a_wceq f0_absneu f1_absneu a_cab i0_absneu a_sup_set_class a_csn a_wceq i0_absneu a_wex p_imp f0_absneu f1_absneu i0_absneu p_euabsn2 f2_absneu f3_absneu a_wcel f0_absneu f1_absneu a_cab f2_absneu a_csn a_wceq a_wa f0_absneu f1_absneu a_cab i0_absneu a_sup_set_class a_csn a_wceq i0_absneu a_wex f0_absneu f1_absneu a_weu p_sylibr $.
$}

$(Restricted existential uniqueness determined by a singleton.
       (Contributed by NM, 29-May-2006.)  (Revised by Mario Carneiro,
       23-Dec-2016.) $)

${
	$v ph x A B V  $.
	$d x  $.
	$d ph  $.
	$d A  $.
	f0_rabsneu $f wff ph $.
	f1_rabsneu $f set x $.
	f2_rabsneu $f class A $.
	f3_rabsneu $f class B $.
	f4_rabsneu $f class V $.
	p_rabsneu $p |- ( ( A e. V /\ { x e. B | ph } = { A } ) -> E! x e. B ph ) $= f0_rabsneu f1_rabsneu f3_rabsneu a_df-rab f0_rabsneu f1_rabsneu f3_rabsneu a_crab f1_rabsneu a_sup_set_class f3_rabsneu a_wcel f0_rabsneu a_wa f1_rabsneu a_cab f2_rabsneu a_csn p_eqeq1i f1_rabsneu a_sup_set_class f3_rabsneu a_wcel f0_rabsneu a_wa f1_rabsneu f2_rabsneu f4_rabsneu p_absneu f0_rabsneu f1_rabsneu f3_rabsneu a_crab f2_rabsneu a_csn a_wceq f2_rabsneu f4_rabsneu a_wcel f1_rabsneu a_sup_set_class f3_rabsneu a_wcel f0_rabsneu a_wa f1_rabsneu a_cab f2_rabsneu a_csn a_wceq f1_rabsneu a_sup_set_class f3_rabsneu a_wcel f0_rabsneu a_wa f1_rabsneu a_weu p_sylan2b f0_rabsneu f1_rabsneu f3_rabsneu a_df-reu f2_rabsneu f4_rabsneu a_wcel f0_rabsneu f1_rabsneu f3_rabsneu a_crab f2_rabsneu a_csn a_wceq a_wa f1_rabsneu a_sup_set_class f3_rabsneu a_wcel f0_rabsneu a_wa f1_rabsneu a_weu f0_rabsneu f1_rabsneu f3_rabsneu a_wreu p_sylibr $.
$}

$(Two ways to express " ` A ` is a singleton."  (Contributed by NM,
       30-Oct-2010.) $)

${
	$v x A  $.
	$d x A  $.
	f0_eusn $f set x $.
	f1_eusn $f class A $.
	p_eusn $p |- ( E! x x e. A <-> E. x A = { x } ) $= f0_eusn a_sup_set_class f1_eusn a_wcel f0_eusn p_euabsn f0_eusn f1_eusn p_abid2 f0_eusn a_sup_set_class f1_eusn a_wcel f0_eusn a_cab f1_eusn f0_eusn a_sup_set_class a_csn p_eqeq1i f0_eusn a_sup_set_class f1_eusn a_wcel f0_eusn a_cab f0_eusn a_sup_set_class a_csn a_wceq f1_eusn f0_eusn a_sup_set_class a_csn a_wceq f0_eusn p_exbii f0_eusn a_sup_set_class f1_eusn a_wcel f0_eusn a_weu f0_eusn a_sup_set_class f1_eusn a_wcel f0_eusn a_cab f0_eusn a_sup_set_class a_csn a_wceq f0_eusn a_wex f1_eusn f0_eusn a_sup_set_class a_csn a_wceq f0_eusn a_wex p_bitri $.
$}

$(Truth implied by equality of a restricted class abstraction and a
       singleton.  (Contributed by NM, 29-May-2006.)  (Proof shortened by Mario
       Carneiro, 23-Dec-2016.) $)

${
	$v ph ps x A B  $.
	$d x A  $.
	$d x B  $.
	$d x ps  $.
	f0_rabsnt $f wff ph $.
	f1_rabsnt $f wff ps $.
	f2_rabsnt $f set x $.
	f3_rabsnt $f class A $.
	f4_rabsnt $f class B $.
	e0_rabsnt $e |- B e. _V $.
	e1_rabsnt $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_rabsnt $p |- ( { x e. A | ph } = { B } -> ps ) $= e0_rabsnt f4_rabsnt p_snid f0_rabsnt f2_rabsnt f3_rabsnt a_crab f4_rabsnt a_csn a_wceq p_id f0_rabsnt f2_rabsnt f3_rabsnt a_crab f4_rabsnt a_csn a_wceq f4_rabsnt f4_rabsnt a_csn f0_rabsnt f2_rabsnt f3_rabsnt a_crab p_syl5eleqr e1_rabsnt f0_rabsnt f1_rabsnt f2_rabsnt f4_rabsnt f3_rabsnt p_elrab f4_rabsnt f0_rabsnt f2_rabsnt f3_rabsnt a_crab a_wcel f4_rabsnt f3_rabsnt a_wcel f1_rabsnt p_simprbi f0_rabsnt f2_rabsnt f3_rabsnt a_crab f4_rabsnt a_csn a_wceq f4_rabsnt f0_rabsnt f2_rabsnt f3_rabsnt a_crab a_wcel f1_rabsnt p_syl $.
$}

$(Commutative law for unordered pairs.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	f0_prcom $f class A $.
	f1_prcom $f class B $.
	p_prcom $p |- { A , B } = { B , A } $= f0_prcom a_csn f1_prcom a_csn p_uncom f0_prcom f1_prcom a_df-pr f1_prcom f0_prcom a_df-pr f0_prcom a_csn f1_prcom a_csn a_cun f1_prcom a_csn f0_prcom a_csn a_cun f0_prcom f1_prcom a_cpr f1_prcom f0_prcom a_cpr p_3eqtr4i $.
$}

$(Equality theorem for unordered pairs.  (Contributed by NM,
     29-Mar-1998.) $)

${
	$v A B C  $.
	f0_preq1 $f class A $.
	f1_preq1 $f class B $.
	f2_preq1 $f class C $.
	p_preq1 $p |- ( A = B -> { A , C } = { B , C } ) $= f0_preq1 f1_preq1 p_sneq f0_preq1 f1_preq1 a_wceq f0_preq1 a_csn f1_preq1 a_csn f2_preq1 a_csn p_uneq1d f0_preq1 f2_preq1 a_df-pr f1_preq1 f2_preq1 a_df-pr f0_preq1 f1_preq1 a_wceq f0_preq1 a_csn f2_preq1 a_csn a_cun f1_preq1 a_csn f2_preq1 a_csn a_cun f0_preq1 f2_preq1 a_cpr f1_preq1 f2_preq1 a_cpr p_3eqtr4g $.
$}

$(Equality theorem for unordered pairs.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_preq2 $f class A $.
	f1_preq2 $f class B $.
	f2_preq2 $f class C $.
	p_preq2 $p |- ( A = B -> { C , A } = { C , B } ) $= f0_preq2 f1_preq2 f2_preq2 p_preq1 f2_preq2 f0_preq2 p_prcom f2_preq2 f1_preq2 p_prcom f0_preq2 f1_preq2 a_wceq f0_preq2 f2_preq2 a_cpr f1_preq2 f2_preq2 a_cpr f2_preq2 f0_preq2 a_cpr f2_preq2 f1_preq2 a_cpr p_3eqtr4g $.
$}

$(Equality theorem for unordered pairs.  (Contributed by NM,
     19-Oct-2012.) $)

${
	$v A B C D  $.
	f0_preq12 $f class A $.
	f1_preq12 $f class B $.
	f2_preq12 $f class C $.
	f3_preq12 $f class D $.
	p_preq12 $p |- ( ( A = C /\ B = D ) -> { A , B } = { C , D } ) $= f0_preq12 f2_preq12 f1_preq12 p_preq1 f1_preq12 f3_preq12 f2_preq12 p_preq2 f0_preq12 f2_preq12 a_wceq f1_preq12 f3_preq12 a_wceq f0_preq12 f1_preq12 a_cpr f2_preq12 f1_preq12 a_cpr f2_preq12 f3_preq12 a_cpr p_sylan9eq $.
$}

$(Equality inference for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)

${
	$v A B C  $.
	f0_preq1i $f class A $.
	f1_preq1i $f class B $.
	f2_preq1i $f class C $.
	e0_preq1i $e |- A = B $.
	p_preq1i $p |- { A , C } = { B , C } $= e0_preq1i f0_preq1i f1_preq1i f2_preq1i p_preq1 f0_preq1i f1_preq1i a_wceq f0_preq1i f2_preq1i a_cpr f1_preq1i f2_preq1i a_cpr a_wceq a_ax-mp $.
$}

$(Equality inference for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)

${
	$v A B C  $.
	f0_preq2i $f class A $.
	f1_preq2i $f class B $.
	f2_preq2i $f class C $.
	e0_preq2i $e |- A = B $.
	p_preq2i $p |- { C , A } = { C , B } $= e0_preq2i f0_preq2i f1_preq2i f2_preq2i p_preq2 f0_preq2i f1_preq2i a_wceq f2_preq2i f0_preq2i a_cpr f2_preq2i f1_preq2i a_cpr a_wceq a_ax-mp $.
$}

$(Equality inference for unordered pairs.  (Contributed by NM,
         19-Oct-2012.) $)

${
	$v A B C D  $.
	f0_preq12i $f class A $.
	f1_preq12i $f class B $.
	f2_preq12i $f class C $.
	f3_preq12i $f class D $.
	e0_preq12i $e |- A = B $.
	e1_preq12i $e |- C = D $.
	p_preq12i $p |- { A , C } = { B , D } $= e0_preq12i e1_preq12i f0_preq12i f2_preq12i f1_preq12i f3_preq12i p_preq12 f0_preq12i f1_preq12i a_wceq f2_preq12i f3_preq12i a_wceq f0_preq12i f2_preq12i a_cpr f1_preq12i f3_preq12i a_cpr a_wceq p_mp2an $.
$}

$(Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)

${
	$v ph A B C  $.
	f0_preq1d $f wff ph $.
	f1_preq1d $f class A $.
	f2_preq1d $f class B $.
	f3_preq1d $f class C $.
	e0_preq1d $e |- ( ph -> A = B ) $.
	p_preq1d $p |- ( ph -> { A , C } = { B , C } ) $= e0_preq1d f1_preq1d f2_preq1d f3_preq1d p_preq1 f0_preq1d f1_preq1d f2_preq1d a_wceq f1_preq1d f3_preq1d a_cpr f2_preq1d f3_preq1d a_cpr a_wceq p_syl $.
$}

$(Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)

${
	$v ph A B C  $.
	f0_preq2d $f wff ph $.
	f1_preq2d $f class A $.
	f2_preq2d $f class B $.
	f3_preq2d $f class C $.
	e0_preq2d $e |- ( ph -> A = B ) $.
	p_preq2d $p |- ( ph -> { C , A } = { C , B } ) $= e0_preq2d f1_preq2d f2_preq2d f3_preq2d p_preq2 f0_preq2d f1_preq2d f2_preq2d a_wceq f3_preq2d f1_preq2d a_cpr f3_preq2d f2_preq2d a_cpr a_wceq p_syl $.
$}

$(Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)

${
	$v ph A B C D  $.
	f0_preq12d $f wff ph $.
	f1_preq12d $f class A $.
	f2_preq12d $f class B $.
	f3_preq12d $f class C $.
	f4_preq12d $f class D $.
	e0_preq12d $e |- ( ph -> A = B ) $.
	e1_preq12d $e |- ( ph -> C = D ) $.
	p_preq12d $p |- ( ph -> { A , C } = { B , D } ) $= e0_preq12d e1_preq12d f1_preq12d f3_preq12d f2_preq12d f4_preq12d p_preq12 f0_preq12d f1_preq12d f2_preq12d a_wceq f3_preq12d f4_preq12d a_wceq f1_preq12d f3_preq12d a_cpr f2_preq12d f4_preq12d a_cpr a_wceq p_syl2anc $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) $)

${
	$v A B C D  $.
	f0_tpeq1 $f class A $.
	f1_tpeq1 $f class B $.
	f2_tpeq1 $f class C $.
	f3_tpeq1 $f class D $.
	p_tpeq1 $p |- ( A = B -> { A , C , D } = { B , C , D } ) $= f0_tpeq1 f1_tpeq1 f2_tpeq1 p_preq1 f0_tpeq1 f1_tpeq1 a_wceq f0_tpeq1 f2_tpeq1 a_cpr f1_tpeq1 f2_tpeq1 a_cpr f3_tpeq1 a_csn p_uneq1d f0_tpeq1 f2_tpeq1 f3_tpeq1 a_df-tp f1_tpeq1 f2_tpeq1 f3_tpeq1 a_df-tp f0_tpeq1 f1_tpeq1 a_wceq f0_tpeq1 f2_tpeq1 a_cpr f3_tpeq1 a_csn a_cun f1_tpeq1 f2_tpeq1 a_cpr f3_tpeq1 a_csn a_cun f0_tpeq1 f2_tpeq1 f3_tpeq1 a_ctp f1_tpeq1 f2_tpeq1 f3_tpeq1 a_ctp p_3eqtr4g $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) $)

${
	$v A B C D  $.
	f0_tpeq2 $f class A $.
	f1_tpeq2 $f class B $.
	f2_tpeq2 $f class C $.
	f3_tpeq2 $f class D $.
	p_tpeq2 $p |- ( A = B -> { C , A , D } = { C , B , D } ) $= f0_tpeq2 f1_tpeq2 f2_tpeq2 p_preq2 f0_tpeq2 f1_tpeq2 a_wceq f2_tpeq2 f0_tpeq2 a_cpr f2_tpeq2 f1_tpeq2 a_cpr f3_tpeq2 a_csn p_uneq1d f2_tpeq2 f0_tpeq2 f3_tpeq2 a_df-tp f2_tpeq2 f1_tpeq2 f3_tpeq2 a_df-tp f0_tpeq2 f1_tpeq2 a_wceq f2_tpeq2 f0_tpeq2 a_cpr f3_tpeq2 a_csn a_cun f2_tpeq2 f1_tpeq2 a_cpr f3_tpeq2 a_csn a_cun f2_tpeq2 f0_tpeq2 f3_tpeq2 a_ctp f2_tpeq2 f1_tpeq2 f3_tpeq2 a_ctp p_3eqtr4g $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) $)

${
	$v A B C D  $.
	f0_tpeq3 $f class A $.
	f1_tpeq3 $f class B $.
	f2_tpeq3 $f class C $.
	f3_tpeq3 $f class D $.
	p_tpeq3 $p |- ( A = B -> { C , D , A } = { C , D , B } ) $= f0_tpeq3 f1_tpeq3 p_sneq f0_tpeq3 f1_tpeq3 a_wceq f0_tpeq3 a_csn f1_tpeq3 a_csn f2_tpeq3 f3_tpeq3 a_cpr p_uneq2d f2_tpeq3 f3_tpeq3 f0_tpeq3 a_df-tp f2_tpeq3 f3_tpeq3 f1_tpeq3 a_df-tp f0_tpeq3 f1_tpeq3 a_wceq f2_tpeq3 f3_tpeq3 a_cpr f0_tpeq3 a_csn a_cun f2_tpeq3 f3_tpeq3 a_cpr f1_tpeq3 a_csn a_cun f2_tpeq3 f3_tpeq3 f0_tpeq3 a_ctp f2_tpeq3 f3_tpeq3 f1_tpeq3 a_ctp p_3eqtr4g $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)

${
	$v ph A B C D  $.
	f0_tpeq1d $f wff ph $.
	f1_tpeq1d $f class A $.
	f2_tpeq1d $f class B $.
	f3_tpeq1d $f class C $.
	f4_tpeq1d $f class D $.
	e0_tpeq1d $e |- ( ph -> A = B ) $.
	p_tpeq1d $p |- ( ph -> { A , C , D } = { B , C , D } ) $= e0_tpeq1d f1_tpeq1d f2_tpeq1d f3_tpeq1d f4_tpeq1d p_tpeq1 f0_tpeq1d f1_tpeq1d f2_tpeq1d a_wceq f1_tpeq1d f3_tpeq1d f4_tpeq1d a_ctp f2_tpeq1d f3_tpeq1d f4_tpeq1d a_ctp a_wceq p_syl $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)

${
	$v ph A B C D  $.
	f0_tpeq2d $f wff ph $.
	f1_tpeq2d $f class A $.
	f2_tpeq2d $f class B $.
	f3_tpeq2d $f class C $.
	f4_tpeq2d $f class D $.
	e0_tpeq2d $e |- ( ph -> A = B ) $.
	p_tpeq2d $p |- ( ph -> { C , A , D } = { C , B , D } ) $= e0_tpeq2d f1_tpeq2d f2_tpeq2d f3_tpeq2d f4_tpeq2d p_tpeq2 f0_tpeq2d f1_tpeq2d f2_tpeq2d a_wceq f3_tpeq2d f1_tpeq2d f4_tpeq2d a_ctp f3_tpeq2d f2_tpeq2d f4_tpeq2d a_ctp a_wceq p_syl $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)

${
	$v ph A B C D  $.
	f0_tpeq3d $f wff ph $.
	f1_tpeq3d $f class A $.
	f2_tpeq3d $f class B $.
	f3_tpeq3d $f class C $.
	f4_tpeq3d $f class D $.
	e0_tpeq3d $e |- ( ph -> A = B ) $.
	p_tpeq3d $p |- ( ph -> { C , D , A } = { C , D , B } ) $= e0_tpeq3d f1_tpeq3d f2_tpeq3d f3_tpeq3d f4_tpeq3d p_tpeq3 f0_tpeq3d f1_tpeq3d f2_tpeq3d a_wceq f3_tpeq3d f4_tpeq3d f1_tpeq3d a_ctp f3_tpeq3d f4_tpeq3d f2_tpeq3d a_ctp a_wceq p_syl $.
$}

$(Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)

${
	$v ph A B C D E F  $.
	f0_tpeq123d $f wff ph $.
	f1_tpeq123d $f class A $.
	f2_tpeq123d $f class B $.
	f3_tpeq123d $f class C $.
	f4_tpeq123d $f class D $.
	f5_tpeq123d $f class E $.
	f6_tpeq123d $f class F $.
	e0_tpeq123d $e |- ( ph -> A = B ) $.
	e1_tpeq123d $e |- ( ph -> C = D ) $.
	e2_tpeq123d $e |- ( ph -> E = F ) $.
	p_tpeq123d $p |- ( ph -> { A , C , E } = { B , D , F } ) $= e0_tpeq123d f0_tpeq123d f1_tpeq123d f2_tpeq123d f3_tpeq123d f5_tpeq123d p_tpeq1d e1_tpeq123d f0_tpeq123d f3_tpeq123d f4_tpeq123d f2_tpeq123d f5_tpeq123d p_tpeq2d e2_tpeq123d f0_tpeq123d f5_tpeq123d f6_tpeq123d f2_tpeq123d f4_tpeq123d p_tpeq3d f0_tpeq123d f1_tpeq123d f3_tpeq123d f5_tpeq123d a_ctp f2_tpeq123d f3_tpeq123d f5_tpeq123d a_ctp f2_tpeq123d f4_tpeq123d f5_tpeq123d a_ctp f2_tpeq123d f4_tpeq123d f6_tpeq123d a_ctp p_3eqtrd $.
$}

$(Rotation of the elements of an unordered triple.  (Contributed by Alan
       Sare, 24-Oct-2011.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	f0_tprot $f class A $.
	f1_tprot $f class B $.
	f2_tprot $f class C $.
	i0_tprot $f set x $.
	p_tprot $p |- { A , B , C } = { B , C , A } $= i0_tprot a_sup_set_class f0_tprot a_wceq i0_tprot a_sup_set_class f1_tprot a_wceq i0_tprot a_sup_set_class f2_tprot a_wceq p_3orrot i0_tprot a_sup_set_class f0_tprot a_wceq i0_tprot a_sup_set_class f1_tprot a_wceq i0_tprot a_sup_set_class f2_tprot a_wceq a_w3o i0_tprot a_sup_set_class f1_tprot a_wceq i0_tprot a_sup_set_class f2_tprot a_wceq i0_tprot a_sup_set_class f0_tprot a_wceq a_w3o i0_tprot p_abbii i0_tprot f0_tprot f1_tprot f2_tprot p_dftp2 i0_tprot f1_tprot f2_tprot f0_tprot p_dftp2 i0_tprot a_sup_set_class f0_tprot a_wceq i0_tprot a_sup_set_class f1_tprot a_wceq i0_tprot a_sup_set_class f2_tprot a_wceq a_w3o i0_tprot a_cab i0_tprot a_sup_set_class f1_tprot a_wceq i0_tprot a_sup_set_class f2_tprot a_wceq i0_tprot a_sup_set_class f0_tprot a_wceq a_w3o i0_tprot a_cab f0_tprot f1_tprot f2_tprot a_ctp f1_tprot f2_tprot f0_tprot a_ctp p_3eqtr4i $.
$}

$(Swap 1st and 2nd members of an undordered triple.  (Contributed by NM,
     22-May-2015.) $)

${
	$v A B C  $.
	f0_tpcoma $f class A $.
	f1_tpcoma $f class B $.
	f2_tpcoma $f class C $.
	p_tpcoma $p |- { A , B , C } = { B , A , C } $= f0_tpcoma f1_tpcoma p_prcom f0_tpcoma f1_tpcoma a_cpr f1_tpcoma f0_tpcoma a_cpr f2_tpcoma a_csn p_uneq1i f0_tpcoma f1_tpcoma f2_tpcoma a_df-tp f1_tpcoma f0_tpcoma f2_tpcoma a_df-tp f0_tpcoma f1_tpcoma a_cpr f2_tpcoma a_csn a_cun f1_tpcoma f0_tpcoma a_cpr f2_tpcoma a_csn a_cun f0_tpcoma f1_tpcoma f2_tpcoma a_ctp f1_tpcoma f0_tpcoma f2_tpcoma a_ctp p_3eqtr4i $.
$}

$(Swap 2nd and 3rd members of an undordered triple.  (Contributed by NM,
     22-May-2015.) $)

${
	$v A B C  $.
	f0_tpcomb $f class A $.
	f1_tpcomb $f class B $.
	f2_tpcomb $f class C $.
	p_tpcomb $p |- { A , B , C } = { A , C , B } $= f1_tpcomb f2_tpcomb f0_tpcomb p_tpcoma f0_tpcomb f1_tpcomb f2_tpcomb p_tprot f0_tpcomb f2_tpcomb f1_tpcomb p_tprot f1_tpcomb f2_tpcomb f0_tpcomb a_ctp f2_tpcomb f1_tpcomb f0_tpcomb a_ctp f0_tpcomb f1_tpcomb f2_tpcomb a_ctp f0_tpcomb f2_tpcomb f1_tpcomb a_ctp p_3eqtr4i $.
$}

$(Split off the first element of an unordered triple.  (Contributed by Mario
     Carneiro, 5-Jan-2016.) $)

${
	$v A B C  $.
	f0_tpass $f class A $.
	f1_tpass $f class B $.
	f2_tpass $f class C $.
	p_tpass $p |- { A , B , C } = ( { A } u. { B , C } ) $= f1_tpass f2_tpass f0_tpass a_df-tp f0_tpass f1_tpass f2_tpass p_tprot f0_tpass a_csn f1_tpass f2_tpass a_cpr p_uncom f1_tpass f2_tpass f0_tpass a_ctp f1_tpass f2_tpass a_cpr f0_tpass a_csn a_cun f0_tpass f1_tpass f2_tpass a_ctp f0_tpass a_csn f1_tpass f2_tpass a_cpr a_cun p_3eqtr4i $.
$}

$(Two ways to write an unordered quadruple.  (Contributed by Mario Carneiro,
     5-Jan-2016.) $)

${
	$v A B C D  $.
	f0_qdass $f class A $.
	f1_qdass $f class B $.
	f2_qdass $f class C $.
	f3_qdass $f class D $.
	p_qdass $p |- ( { A , B } u. { C , D } ) = ( { A , B , C } u. { D } ) $= f0_qdass f1_qdass a_cpr f2_qdass a_csn f3_qdass a_csn p_unass f0_qdass f1_qdass f2_qdass a_df-tp f0_qdass f1_qdass f2_qdass a_ctp f0_qdass f1_qdass a_cpr f2_qdass a_csn a_cun f3_qdass a_csn p_uneq1i f2_qdass f3_qdass a_df-pr f2_qdass f3_qdass a_cpr f2_qdass a_csn f3_qdass a_csn a_cun f0_qdass f1_qdass a_cpr p_uneq2i f0_qdass f1_qdass a_cpr f2_qdass a_csn a_cun f3_qdass a_csn a_cun f0_qdass f1_qdass a_cpr f2_qdass a_csn f3_qdass a_csn a_cun a_cun f0_qdass f1_qdass f2_qdass a_ctp f3_qdass a_csn a_cun f0_qdass f1_qdass a_cpr f2_qdass f3_qdass a_cpr a_cun p_3eqtr4ri $.
$}

$(Two ways to write an unordered quadruple.  (Contributed by Mario Carneiro,
     5-Jan-2016.) $)

${
	$v A B C D  $.
	f0_qdassr $f class A $.
	f1_qdassr $f class B $.
	f2_qdassr $f class C $.
	f3_qdassr $f class D $.
	p_qdassr $p |- ( { A , B } u. { C , D } ) = ( { A } u. { B , C , D } ) $= f0_qdassr a_csn f1_qdassr a_csn f2_qdassr f3_qdassr a_cpr p_unass f0_qdassr f1_qdassr a_df-pr f0_qdassr f1_qdassr a_cpr f0_qdassr a_csn f1_qdassr a_csn a_cun f2_qdassr f3_qdassr a_cpr p_uneq1i f1_qdassr f2_qdassr f3_qdassr p_tpass f1_qdassr f2_qdassr f3_qdassr a_ctp f1_qdassr a_csn f2_qdassr f3_qdassr a_cpr a_cun f0_qdassr a_csn p_uneq2i f0_qdassr a_csn f1_qdassr a_csn a_cun f2_qdassr f3_qdassr a_cpr a_cun f0_qdassr a_csn f1_qdassr a_csn f2_qdassr f3_qdassr a_cpr a_cun a_cun f0_qdassr f1_qdassr a_cpr f2_qdassr f3_qdassr a_cpr a_cun f0_qdassr a_csn f1_qdassr f2_qdassr f3_qdassr a_ctp a_cun p_3eqtr4i $.
$}

$(Unordered triple ` { A , A , B } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)

${
	$v A B  $.
	f0_tpidm12 $f class A $.
	f1_tpidm12 $f class B $.
	p_tpidm12 $p |- { A , A , B } = { A , B } $= f0_tpidm12 p_dfsn2 f0_tpidm12 a_csn f0_tpidm12 f0_tpidm12 a_cpr f1_tpidm12 a_csn p_uneq1i f0_tpidm12 f1_tpidm12 a_df-pr f0_tpidm12 f0_tpidm12 f1_tpidm12 a_df-tp f0_tpidm12 a_csn f1_tpidm12 a_csn a_cun f0_tpidm12 f0_tpidm12 a_cpr f1_tpidm12 a_csn a_cun f0_tpidm12 f1_tpidm12 a_cpr f0_tpidm12 f0_tpidm12 f1_tpidm12 a_ctp p_3eqtr4ri $.
$}

$(Unordered triple ` { A , B , A } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)

${
	$v A B  $.
	f0_tpidm13 $f class A $.
	f1_tpidm13 $f class B $.
	p_tpidm13 $p |- { A , B , A } = { A , B } $= f0_tpidm13 f0_tpidm13 f1_tpidm13 p_tprot f0_tpidm13 f1_tpidm13 p_tpidm12 f0_tpidm13 f0_tpidm13 f1_tpidm13 a_ctp f0_tpidm13 f1_tpidm13 f0_tpidm13 a_ctp f0_tpidm13 f1_tpidm13 a_cpr p_eqtr3i $.
$}

$(Unordered triple ` { A , B , B } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)

${
	$v A B  $.
	f0_tpidm23 $f class A $.
	f1_tpidm23 $f class B $.
	p_tpidm23 $p |- { A , B , B } = { A , B } $= f0_tpidm23 f1_tpidm23 f1_tpidm23 p_tprot f1_tpidm23 f0_tpidm23 p_tpidm12 f1_tpidm23 f0_tpidm23 p_prcom f0_tpidm23 f1_tpidm23 f1_tpidm23 a_ctp f1_tpidm23 f1_tpidm23 f0_tpidm23 a_ctp f1_tpidm23 f0_tpidm23 a_cpr f0_tpidm23 f1_tpidm23 a_cpr p_3eqtri $.
$}

$(Unordered triple ` { A , A , A } ` is just an overlong way to write
     ` { A } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)

${
	$v A  $.
	f0_tpidm $f class A $.
	p_tpidm $p |- { A , A , A } = { A } $= f0_tpidm f0_tpidm p_tpidm12 f0_tpidm p_dfsn2 f0_tpidm f0_tpidm f0_tpidm a_ctp f0_tpidm f0_tpidm a_cpr f0_tpidm a_csn p_eqtr4i $.
$}

$(An unordered pair contains its first member.  Part of Theorem 7.6 of
     [Quine] p. 49.  (Contributed by Stefan Allan, 8-Nov-2008.) $)

${
	$v A B V  $.
	f0_prid1g $f class A $.
	f1_prid1g $f class B $.
	f2_prid1g $f class V $.
	p_prid1g $p |- ( A e. V -> A e. { A , B } ) $= f0_prid1g p_eqid f0_prid1g f0_prid1g a_wceq f0_prid1g f1_prid1g a_wceq p_orci f0_prid1g f0_prid1g f1_prid1g f2_prid1g p_elprg f0_prid1g f2_prid1g a_wcel f0_prid1g f0_prid1g f1_prid1g a_cpr a_wcel f0_prid1g f0_prid1g a_wceq f0_prid1g f1_prid1g a_wceq a_wo p_mpbiri $.
$}

$(An unordered pair contains its second member.  Part of Theorem 7.6 of
     [Quine] p. 49.  (Contributed by Stefan Allan, 8-Nov-2008.) $)

${
	$v A B V  $.
	f0_prid2g $f class A $.
	f1_prid2g $f class B $.
	f2_prid2g $f class V $.
	p_prid2g $p |- ( B e. V -> B e. { A , B } ) $= f1_prid2g f0_prid2g f2_prid2g p_prid1g f1_prid2g f0_prid2g p_prcom f1_prid2g f2_prid2g a_wcel f1_prid2g f1_prid2g f0_prid2g a_cpr f0_prid2g f1_prid2g a_cpr p_syl6eleq $.
$}

$(An unordered pair contains its first member.  Part of Theorem 7.6 of
       [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	f0_prid1 $f class A $.
	f1_prid1 $f class B $.
	e0_prid1 $e |- A e. _V $.
	p_prid1 $p |- A e. { A , B } $= e0_prid1 f0_prid1 f1_prid1 a_cvv p_prid1g f0_prid1 a_cvv a_wcel f0_prid1 f0_prid1 f1_prid1 a_cpr a_wcel a_ax-mp $.
$}

$(An unordered pair contains its second member.  Part of Theorem 7.6 of
       [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	f0_prid2 $f class A $.
	f1_prid2 $f class B $.
	e0_prid2 $e |- B e. _V $.
	p_prid2 $p |- B e. { A , B } $= e0_prid2 f1_prid2 f0_prid2 p_prid1 f1_prid2 f0_prid2 p_prcom f1_prid2 f1_prid2 f0_prid2 a_cpr f0_prid2 f1_prid2 a_cpr p_eleqtri $.
$}

$(A proper class vanishes in an unordered pair.  (Contributed by NM,
     5-Aug-1993.) $)

${
	$v A B  $.
	f0_prprc1 $f class A $.
	f1_prprc1 $f class B $.
	p_prprc1 $p |- ( -. A e. _V -> { A , B } = { B } ) $= f0_prprc1 p_snprc f0_prprc1 a_csn a_c0 f1_prprc1 a_csn p_uneq1 f0_prprc1 f1_prprc1 a_df-pr a_c0 f1_prprc1 a_csn p_uncom f1_prprc1 a_csn p_un0 a_c0 f1_prprc1 a_csn a_cun f1_prprc1 a_csn a_c0 a_cun f1_prprc1 a_csn p_eqtr2i f0_prprc1 a_csn a_c0 a_wceq f0_prprc1 a_csn f1_prprc1 a_csn a_cun a_c0 f1_prprc1 a_csn a_cun f0_prprc1 f1_prprc1 a_cpr f1_prprc1 a_csn p_3eqtr4g f0_prprc1 a_cvv a_wcel a_wn f0_prprc1 a_csn a_c0 a_wceq f0_prprc1 f1_prprc1 a_cpr f1_prprc1 a_csn a_wceq p_sylbi $.
$}

$(A proper class vanishes in an unordered pair.  (Contributed by NM,
     22-Mar-2006.) $)

${
	$v A B  $.
	f0_prprc2 $f class A $.
	f1_prprc2 $f class B $.
	p_prprc2 $p |- ( -. B e. _V -> { A , B } = { A } ) $= f0_prprc2 f1_prprc2 p_prcom f1_prprc2 f0_prprc2 p_prprc1 f1_prprc2 a_cvv a_wcel a_wn f0_prprc2 f1_prprc2 a_cpr f1_prprc2 f0_prprc2 a_cpr f0_prprc2 a_csn p_syl5eq $.
$}

$(An unordered pair containing two proper classes is the empty set.
     (Contributed by NM, 22-Mar-2006.) $)

${
	$v A B  $.
	f0_prprc $f class A $.
	f1_prprc $f class B $.
	p_prprc $p |- ( ( -. A e. _V /\ -. B e. _V ) -> { A , B } = (/) ) $= f0_prprc f1_prprc p_prprc1 f1_prprc p_snprc f1_prprc a_cvv a_wcel a_wn f1_prprc a_csn a_c0 a_wceq p_biimpi f0_prprc a_cvv a_wcel a_wn f1_prprc a_cvv a_wcel a_wn f0_prprc f1_prprc a_cpr f1_prprc a_csn a_c0 p_sylan9eq $.
$}

$(One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C  $.
	f0_tpid1 $f class A $.
	f1_tpid1 $f class B $.
	f2_tpid1 $f class C $.
	e0_tpid1 $e |- A e. _V $.
	p_tpid1 $p |- A e. { A , B , C } $= f0_tpid1 p_eqid f0_tpid1 f0_tpid1 a_wceq f0_tpid1 f1_tpid1 a_wceq f0_tpid1 f2_tpid1 a_wceq p_3mix1i e0_tpid1 f0_tpid1 f0_tpid1 f1_tpid1 f2_tpid1 p_eltp f0_tpid1 f0_tpid1 f1_tpid1 f2_tpid1 a_ctp a_wcel f0_tpid1 f0_tpid1 a_wceq f0_tpid1 f1_tpid1 a_wceq f0_tpid1 f2_tpid1 a_wceq a_w3o p_mpbir $.
$}

$(One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C  $.
	f0_tpid2 $f class A $.
	f1_tpid2 $f class B $.
	f2_tpid2 $f class C $.
	e0_tpid2 $e |- B e. _V $.
	p_tpid2 $p |- B e. { A , B , C } $= f1_tpid2 p_eqid f1_tpid2 f1_tpid2 a_wceq f1_tpid2 f0_tpid2 a_wceq f1_tpid2 f2_tpid2 a_wceq p_3mix2i e0_tpid2 f1_tpid2 f0_tpid2 f1_tpid2 f2_tpid2 p_eltp f1_tpid2 f0_tpid2 f1_tpid2 f2_tpid2 a_ctp a_wcel f1_tpid2 f0_tpid2 a_wceq f1_tpid2 f1_tpid2 a_wceq f1_tpid2 f2_tpid2 a_wceq a_w3o p_mpbir $.
$}

$(Closed theorem form of ~ tpid3 .  This proof was automatically generated
       from the virtual deduction proof ~ tpid3gVD using a translation
       program.  (Contributed by Alan Sare, 24-Oct-2011.) $)

${
	$v A B C D  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x D  $.
	$d x  $.
	f0_tpid3g $f class A $.
	f1_tpid3g $f class B $.
	f2_tpid3g $f class C $.
	f3_tpid3g $f class D $.
	i0_tpid3g $f set x $.
	p_tpid3g $p |- ( A e. B -> A e. { C , D , A } ) $= i0_tpid3g f0_tpid3g f1_tpid3g p_elisset i0_tpid3g a_sup_set_class f0_tpid3g a_wceq i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq p_3mix3 i0_tpid3g a_sup_set_class f0_tpid3g a_wceq i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq i0_tpid3g a_sup_set_class f0_tpid3g a_wceq a_w3o a_wi f0_tpid3g f1_tpid3g a_wcel p_a1i i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq i0_tpid3g a_sup_set_class f0_tpid3g a_wceq a_w3o i0_tpid3g p_abid f0_tpid3g f1_tpid3g a_wcel i0_tpid3g a_sup_set_class f0_tpid3g a_wceq i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq i0_tpid3g a_sup_set_class f0_tpid3g a_wceq a_w3o i0_tpid3g a_sup_set_class i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq i0_tpid3g a_sup_set_class f0_tpid3g a_wceq a_w3o i0_tpid3g a_cab a_wcel p_syl6ibr i0_tpid3g f2_tpid3g f3_tpid3g f0_tpid3g p_dftp2 f2_tpid3g f3_tpid3g f0_tpid3g a_ctp i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq i0_tpid3g a_sup_set_class f0_tpid3g a_wceq a_w3o i0_tpid3g a_cab i0_tpid3g a_sup_set_class p_eleq2i f0_tpid3g f1_tpid3g a_wcel i0_tpid3g a_sup_set_class f0_tpid3g a_wceq i0_tpid3g a_sup_set_class i0_tpid3g a_sup_set_class f2_tpid3g a_wceq i0_tpid3g a_sup_set_class f3_tpid3g a_wceq i0_tpid3g a_sup_set_class f0_tpid3g a_wceq a_w3o i0_tpid3g a_cab a_wcel i0_tpid3g a_sup_set_class f2_tpid3g f3_tpid3g f0_tpid3g a_ctp a_wcel p_syl6ibr i0_tpid3g a_sup_set_class f0_tpid3g f2_tpid3g f3_tpid3g f0_tpid3g a_ctp p_eleq1 i0_tpid3g a_sup_set_class f0_tpid3g a_wceq i0_tpid3g a_sup_set_class f2_tpid3g f3_tpid3g f0_tpid3g a_ctp a_wcel f0_tpid3g f2_tpid3g f3_tpid3g f0_tpid3g a_ctp a_wcel f0_tpid3g f1_tpid3g a_wcel p_mpbidi f0_tpid3g f1_tpid3g a_wcel i0_tpid3g a_sup_set_class f0_tpid3g a_wceq f0_tpid3g f2_tpid3g f3_tpid3g f0_tpid3g a_ctp a_wcel i0_tpid3g p_exlimdv f0_tpid3g f1_tpid3g a_wcel i0_tpid3g a_sup_set_class f0_tpid3g a_wceq i0_tpid3g a_wex f0_tpid3g f2_tpid3g f3_tpid3g f0_tpid3g a_ctp a_wcel p_mpd $.
$}

$(One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C  $.
	f0_tpid3 $f class A $.
	f1_tpid3 $f class B $.
	f2_tpid3 $f class C $.
	e0_tpid3 $e |- C e. _V $.
	p_tpid3 $p |- C e. { A , B , C } $= f2_tpid3 p_eqid f2_tpid3 f2_tpid3 a_wceq f2_tpid3 f0_tpid3 a_wceq f2_tpid3 f1_tpid3 a_wceq p_3mix3i e0_tpid3 f2_tpid3 f0_tpid3 f1_tpid3 f2_tpid3 p_eltp f2_tpid3 f0_tpid3 f1_tpid3 f2_tpid3 a_ctp a_wcel f2_tpid3 f0_tpid3 a_wceq f2_tpid3 f1_tpid3 a_wceq f2_tpid3 f2_tpid3 a_wceq a_w3o p_mpbir $.
$}

$(The singleton of a set is not empty.  (Contributed by NM, 14-Dec-2008.) $)

${
	$v A V  $.
	f0_snnzg $f class A $.
	f1_snnzg $f class V $.
	p_snnzg $p |- ( A e. V -> { A } =/= (/) ) $= f0_snnzg f1_snnzg p_snidg f0_snnzg a_csn f0_snnzg p_ne0i f0_snnzg f1_snnzg a_wcel f0_snnzg f0_snnzg a_csn a_wcel f0_snnzg a_csn a_c0 a_wne p_syl $.
$}

$(The singleton of a set is not empty.  (Contributed by NM,
       10-Apr-1994.) $)

${
	$v A  $.
	f0_snnz $f class A $.
	e0_snnz $e |- A e. _V $.
	p_snnz $p |- { A } =/= (/) $= e0_snnz f0_snnz a_cvv p_snnzg f0_snnz a_cvv a_wcel f0_snnz a_csn a_c0 a_wne a_ax-mp $.
$}

$(A pair containing a set is not empty.  (Contributed by NM,
       9-Apr-1994.) $)

${
	$v A B  $.
	f0_prnz $f class A $.
	f1_prnz $f class B $.
	e0_prnz $e |- A e. _V $.
	p_prnz $p |- { A , B } =/= (/) $= e0_prnz f0_prnz f1_prnz p_prid1 f0_prnz f1_prnz a_cpr f0_prnz p_ne0i f0_prnz f0_prnz f1_prnz a_cpr a_wcel f0_prnz f1_prnz a_cpr a_c0 a_wne a_ax-mp $.
$}

$(A pair containing a set is not empty.  (Contributed by FL,
       19-Sep-2011.) $)

${
	$v A B V  $.
	$d x A  $.
	$d x B  $.
	f0_prnzg $f class A $.
	f1_prnzg $f class B $.
	f2_prnzg $f class V $.
	i0_prnzg $f set x $.
	p_prnzg $p |- ( A e. V -> { A , B } =/= (/) ) $= i0_prnzg a_sup_set_class f0_prnzg f1_prnzg p_preq1 i0_prnzg a_sup_set_class f0_prnzg a_wceq i0_prnzg a_sup_set_class f1_prnzg a_cpr f0_prnzg f1_prnzg a_cpr a_c0 p_neeq1d i0_prnzg p_vex i0_prnzg a_sup_set_class f1_prnzg p_prnz i0_prnzg a_sup_set_class f1_prnzg a_cpr a_c0 a_wne f0_prnzg f1_prnzg a_cpr a_c0 a_wne i0_prnzg f0_prnzg f2_prnzg p_vtoclg $.
$}

$(A triplet containing a set is not empty.  (Contributed by NM,
       10-Apr-1994.) $)

${
	$v A B C  $.
	f0_tpnz $f class A $.
	f1_tpnz $f class B $.
	f2_tpnz $f class C $.
	e0_tpnz $e |- A e. _V $.
	p_tpnz $p |- { A , B , C } =/= (/) $= e0_tpnz f0_tpnz f1_tpnz f2_tpnz p_tpid1 f0_tpnz f1_tpnz f2_tpnz a_ctp f0_tpnz p_ne0i f0_tpnz f0_tpnz f1_tpnz f2_tpnz a_ctp a_wcel f0_tpnz f1_tpnz f2_tpnz a_ctp a_c0 a_wne a_ax-mp $.
$}

$(The singleton of an element of a class is a subset of the class.
       Theorem 7.4 of [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) $)

${
	$v A B  $.
	$d A x  $.
	$d B x  $.
	f0_snss $f class A $.
	f1_snss $f class B $.
	i0_snss $f set x $.
	e0_snss $e |- A e. _V $.
	p_snss $p |- ( A e. B <-> { A } C_ B ) $= i0_snss f0_snss p_elsn i0_snss a_sup_set_class f0_snss a_csn a_wcel i0_snss a_sup_set_class f0_snss a_wceq i0_snss a_sup_set_class f1_snss a_wcel p_imbi1i i0_snss a_sup_set_class f0_snss a_csn a_wcel i0_snss a_sup_set_class f1_snss a_wcel a_wi i0_snss a_sup_set_class f0_snss a_wceq i0_snss a_sup_set_class f1_snss a_wcel a_wi i0_snss p_albii i0_snss f0_snss a_csn f1_snss p_dfss2 e0_snss i0_snss f0_snss f1_snss p_clel2 i0_snss a_sup_set_class f0_snss a_csn a_wcel i0_snss a_sup_set_class f1_snss a_wcel a_wi i0_snss a_wal i0_snss a_sup_set_class f0_snss a_wceq i0_snss a_sup_set_class f1_snss a_wcel a_wi i0_snss a_wal f0_snss a_csn f1_snss a_wss f0_snss f1_snss a_wcel p_3bitr4ri $.
$}

$(Membership in a set with an element removed.  (Contributed by NM,
     10-Oct-2007.) $)

${
	$v A B C  $.
	f0_eldifsn $f class A $.
	f1_eldifsn $f class B $.
	f2_eldifsn $f class C $.
	p_eldifsn $p |- ( A e. ( B \ { C } ) <-> ( A e. B /\ A =/= C ) ) $= f0_eldifsn f1_eldifsn f2_eldifsn a_csn p_eldif f0_eldifsn f2_eldifsn f1_eldifsn p_elsncg f0_eldifsn f1_eldifsn a_wcel f0_eldifsn f2_eldifsn a_csn a_wcel f0_eldifsn f2_eldifsn p_necon3bbid f0_eldifsn f1_eldifsn a_wcel f0_eldifsn f2_eldifsn a_csn a_wcel a_wn f0_eldifsn f2_eldifsn a_wne p_pm5.32i f0_eldifsn f1_eldifsn f2_eldifsn a_csn a_cdif a_wcel f0_eldifsn f1_eldifsn a_wcel f0_eldifsn f2_eldifsn a_csn a_wcel a_wn a_wa f0_eldifsn f1_eldifsn a_wcel f0_eldifsn f2_eldifsn a_wne a_wa p_bitri $.
$}

$(Membership in a set with an element removed.  (Contributed by NM,
     10-Mar-2015.) $)

${
	$v A B C  $.
	f0_eldifsni $f class A $.
	f1_eldifsni $f class B $.
	f2_eldifsni $f class C $.
	p_eldifsni $p |- ( A e. ( B \ { C } ) -> A =/= C ) $= f0_eldifsni f1_eldifsni f2_eldifsni p_eldifsn f0_eldifsni f1_eldifsni f2_eldifsni a_csn a_cdif a_wcel f0_eldifsni f1_eldifsni a_wcel f0_eldifsni f2_eldifsni a_wne p_simprbi $.
$}

$(` A ` is not in ` ( B \ { A } ) ` .  (Contributed by David Moews,
     1-May-2017.) $)

${
	$v A B  $.
	f0_neldifsn $f class A $.
	f1_neldifsn $f class B $.
	p_neldifsn $p |- -. A e. ( B \ { A } ) $= f0_neldifsn p_neirr f0_neldifsn f1_neldifsn f0_neldifsn p_eldifsni f0_neldifsn f1_neldifsn f0_neldifsn a_csn a_cdif a_wcel f0_neldifsn f0_neldifsn a_wne p_mto $.
$}

$(` A ` is not in ` ( B \ { A } ) ` .  Deduction form.  (Contributed by
     David Moews, 1-May-2017.) $)

${
	$v ph A B  $.
	f0_neldifsnd $f wff ph $.
	f1_neldifsnd $f class A $.
	f2_neldifsnd $f class B $.
	p_neldifsnd $p |- ( ph -> -. A e. ( B \ { A } ) ) $= f1_neldifsnd f2_neldifsnd p_neldifsn f1_neldifsnd f2_neldifsnd f1_neldifsnd a_csn a_cdif a_wcel a_wn f0_neldifsnd p_a1i $.
$}

$(Restricted existential quantification over a set with an element removed.
     (Contributed by NM, 4-Feb-2015.) $)

${
	$v ph x A B  $.
	f0_rexdifsn $f wff ph $.
	f1_rexdifsn $f set x $.
	f2_rexdifsn $f class A $.
	f3_rexdifsn $f class B $.
	p_rexdifsn $p |- ( E. x e. ( A \ { B } ) ph <-> E. x e. A ( x =/= B /\ ph ) ) $= f1_rexdifsn a_sup_set_class f2_rexdifsn f3_rexdifsn p_eldifsn f1_rexdifsn a_sup_set_class f2_rexdifsn f3_rexdifsn a_csn a_cdif a_wcel f1_rexdifsn a_sup_set_class f2_rexdifsn a_wcel f1_rexdifsn a_sup_set_class f3_rexdifsn a_wne a_wa f0_rexdifsn p_anbi1i f1_rexdifsn a_sup_set_class f2_rexdifsn a_wcel f1_rexdifsn a_sup_set_class f3_rexdifsn a_wne f0_rexdifsn p_anass f1_rexdifsn a_sup_set_class f2_rexdifsn f3_rexdifsn a_csn a_cdif a_wcel f0_rexdifsn a_wa f1_rexdifsn a_sup_set_class f2_rexdifsn a_wcel f1_rexdifsn a_sup_set_class f3_rexdifsn a_wne a_wa f0_rexdifsn a_wa f1_rexdifsn a_sup_set_class f2_rexdifsn a_wcel f1_rexdifsn a_sup_set_class f3_rexdifsn a_wne f0_rexdifsn a_wa a_wa p_bitri f0_rexdifsn f1_rexdifsn a_sup_set_class f3_rexdifsn a_wne f0_rexdifsn a_wa f1_rexdifsn f2_rexdifsn f3_rexdifsn a_csn a_cdif f2_rexdifsn p_rexbii2 $.
$}

$(The singleton of an element of a class is a subset of the class.
       Theorem 7.4 of [Quine] p. 49.  (Contributed by NM, 22-Jul-2001.) $)

${
	$v A B V  $.
	$d A x  $.
	$d B x  $.
	f0_snssg $f class A $.
	f1_snssg $f class B $.
	f2_snssg $f class V $.
	i0_snssg $f set x $.
	p_snssg $p |- ( A e. V -> ( A e. B <-> { A } C_ B ) ) $= i0_snssg a_sup_set_class f0_snssg f1_snssg p_eleq1 i0_snssg a_sup_set_class f0_snssg p_sneq i0_snssg a_sup_set_class f0_snssg a_wceq i0_snssg a_sup_set_class a_csn f0_snssg a_csn f1_snssg p_sseq1d i0_snssg p_vex i0_snssg a_sup_set_class f1_snssg p_snss i0_snssg a_sup_set_class f1_snssg a_wcel i0_snssg a_sup_set_class a_csn f1_snssg a_wss f0_snssg f1_snssg a_wcel f0_snssg a_csn f1_snssg a_wss i0_snssg f0_snssg f2_snssg p_vtoclbg $.
$}

$(An element not in a set can be removed without affecting the set.
       (Contributed by NM, 16-Mar-2006.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)

${
	$v A B  $.
	$d A x  $.
	$d B x  $.
	f0_difsn $f class A $.
	f1_difsn $f class B $.
	i0_difsn $f set x $.
	p_difsn $p |- ( -. A e. B -> ( B \ { A } ) = B ) $= i0_difsn a_sup_set_class f1_difsn f0_difsn p_eldifsn i0_difsn a_sup_set_class f1_difsn a_wcel i0_difsn a_sup_set_class f0_difsn a_wne p_simpl i0_difsn a_sup_set_class f0_difsn f1_difsn p_eleq1 i0_difsn a_sup_set_class f0_difsn a_wceq i0_difsn a_sup_set_class f1_difsn a_wcel f0_difsn f1_difsn a_wcel p_biimpcd i0_difsn a_sup_set_class f1_difsn a_wcel f0_difsn f1_difsn a_wcel i0_difsn a_sup_set_class f0_difsn p_necon3bd i0_difsn a_sup_set_class f1_difsn a_wcel f0_difsn f1_difsn a_wcel a_wn i0_difsn a_sup_set_class f0_difsn a_wne p_com12 f0_difsn f1_difsn a_wcel a_wn i0_difsn a_sup_set_class f1_difsn a_wcel i0_difsn a_sup_set_class f0_difsn a_wne p_ancld f0_difsn f1_difsn a_wcel a_wn i0_difsn a_sup_set_class f1_difsn a_wcel i0_difsn a_sup_set_class f0_difsn a_wne a_wa i0_difsn a_sup_set_class f1_difsn a_wcel p_impbid2 i0_difsn a_sup_set_class f1_difsn f0_difsn a_csn a_cdif a_wcel i0_difsn a_sup_set_class f1_difsn a_wcel i0_difsn a_sup_set_class f0_difsn a_wne a_wa f0_difsn f1_difsn a_wcel a_wn i0_difsn a_sup_set_class f1_difsn a_wcel p_syl5bb f0_difsn f1_difsn a_wcel a_wn i0_difsn f1_difsn f0_difsn a_csn a_cdif f1_difsn p_eqrdv $.
$}

$(Removal of a singleton from an unordered pair.  (Contributed by NM,
       16-Mar-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B  $.
	$d A x  $.
	$d B x  $.
	f0_difprsn $f class A $.
	f1_difprsn $f class B $.
	i0_difprsn $f set x $.
	p_difprsn $p |- ( { A , B } \ { A } ) C_ { B } $= i0_difprsn p_vex i0_difprsn a_sup_set_class f0_difprsn f1_difprsn p_elpr i0_difprsn f0_difprsn p_elsn i0_difprsn a_sup_set_class f0_difprsn a_csn a_wcel i0_difprsn a_sup_set_class f0_difprsn a_wceq p_notbii i0_difprsn a_sup_set_class f0_difprsn a_wceq i0_difprsn a_sup_set_class f1_difprsn a_wceq p_biorf i0_difprsn a_sup_set_class f0_difprsn a_wceq a_wn i0_difprsn a_sup_set_class f1_difprsn a_wceq i0_difprsn a_sup_set_class f0_difprsn a_wceq i0_difprsn a_sup_set_class f1_difprsn a_wceq a_wo p_biimparc i0_difprsn a_sup_set_class f0_difprsn f1_difprsn a_cpr a_wcel i0_difprsn a_sup_set_class f0_difprsn a_wceq i0_difprsn a_sup_set_class f1_difprsn a_wceq a_wo i0_difprsn a_sup_set_class f0_difprsn a_wceq a_wn i0_difprsn a_sup_set_class f1_difprsn a_wceq i0_difprsn a_sup_set_class f0_difprsn a_csn a_wcel a_wn p_syl2anb i0_difprsn a_sup_set_class f0_difprsn f1_difprsn a_cpr f0_difprsn a_csn p_eldif i0_difprsn f1_difprsn p_elsn i0_difprsn a_sup_set_class f0_difprsn f1_difprsn a_cpr a_wcel i0_difprsn a_sup_set_class f0_difprsn a_csn a_wcel a_wn a_wa i0_difprsn a_sup_set_class f1_difprsn a_wceq i0_difprsn a_sup_set_class f0_difprsn f1_difprsn a_cpr f0_difprsn a_csn a_cdif a_wcel i0_difprsn a_sup_set_class f1_difprsn a_csn a_wcel p_3imtr4i i0_difprsn f0_difprsn f1_difprsn a_cpr f0_difprsn a_csn a_cdif f1_difprsn a_csn p_ssriv $.
$}

$(` ( B \ { A } ) ` equals ` B ` if and only if ` A ` is not a member of
     ` B ` .  Generalization of ~ difsn .  (Contributed by David Moews,
     1-May-2017.) $)

${
	$v A B  $.
	f0_difsneq $f class A $.
	f1_difsneq $f class B $.
	p_difsneq $p |- ( -. A e. B <-> ( B \ { A } ) = B ) $= f0_difsneq f1_difsneq p_difsn f0_difsneq f1_difsneq a_wcel f0_difsneq f1_difsneq p_neldifsnd f0_difsneq f1_difsneq f1_difsneq f0_difsneq a_csn a_cdif p_nelne1 f0_difsneq f1_difsneq a_wcel f0_difsneq f1_difsneq f0_difsneq a_csn a_cdif a_wcel a_wn f1_difsneq f1_difsneq f0_difsneq a_csn a_cdif a_wne p_mpdan f0_difsneq f1_difsneq a_wcel f1_difsneq f1_difsneq f0_difsneq a_csn a_cdif p_necomd f0_difsneq f1_difsneq a_wcel f1_difsneq f0_difsneq a_csn a_cdif f1_difsneq p_necon2bi f0_difsneq f1_difsneq a_wcel a_wn f1_difsneq f0_difsneq a_csn a_cdif f1_difsneq a_wceq p_impbii $.
$}

$(` ( B \ { A } ) ` is a proper subclass of ` B ` if and only if ` A ` is a
     member of ` B ` .  (Contributed by David Moews, 1-May-2017.) $)

${
	$v A B  $.
	f0_difsnpss $f class A $.
	f1_difsnpss $f class B $.
	p_difsnpss $p |- ( A e. B <-> ( B \ { A } ) C. B ) $= f0_difsnpss f1_difsnpss a_wcel p_notnot f1_difsnpss f0_difsnpss a_csn p_difss f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wss f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wne p_biantrur f0_difsnpss f1_difsnpss p_difsneq f0_difsnpss f1_difsnpss a_wcel a_wn f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss p_necon3bbii f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_df-pss f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wne f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wss f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wne a_wa f0_difsnpss f1_difsnpss a_wcel a_wn a_wn f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wpss p_3bitr4i f0_difsnpss f1_difsnpss a_wcel f0_difsnpss f1_difsnpss a_wcel a_wn a_wn f1_difsnpss f0_difsnpss a_csn a_cdif f1_difsnpss a_wpss p_bitri $.
$}

$(The singleton of an element of a class is a subset of the class.
     (Contributed by NM, 6-Jun-1994.) $)

${
	$v A B  $.
	f0_snssi $f class A $.
	f1_snssi $f class B $.
	p_snssi $p |- ( A e. B -> { A } C_ B ) $= f0_snssi f1_snssi f1_snssi p_snssg f0_snssi f1_snssi a_wcel f0_snssi a_csn f1_snssi a_wss p_ibi $.
$}

$(The singleton of an element of a class is a subset of the class
       (deduction rule).  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)

${
	$v ph A B  $.
	f0_snssd $f wff ph $.
	f1_snssd $f class A $.
	f2_snssd $f class B $.
	e0_snssd $e |- ( ph -> A e. B ) $.
	p_snssd $p |- ( ph -> { A } C_ B ) $= e0_snssd e0_snssd f1_snssd f2_snssd f2_snssd p_snssg f0_snssd f1_snssd f2_snssd a_wcel f1_snssd f2_snssd a_wcel f1_snssd a_csn f2_snssd a_wss a_wb p_syl f0_snssd f1_snssd f2_snssd a_wcel f1_snssd a_csn f2_snssd a_wss p_mpbid $.
$}

$(If we remove a single element from a class then put it back in, we end up
     with the original class.  (Contributed by NM, 2-Oct-2006.) $)

${
	$v A B  $.
	f0_difsnid $f class A $.
	f1_difsnid $f class B $.
	p_difsnid $p |- ( B e. A -> ( ( A \ { B } ) u. { B } ) = A ) $= f0_difsnid f1_difsnid a_csn a_cdif f1_difsnid a_csn p_uncom f1_difsnid f0_difsnid p_snssi f1_difsnid a_csn f0_difsnid p_undif f1_difsnid f0_difsnid a_wcel f1_difsnid a_csn f0_difsnid a_wss f1_difsnid a_csn f0_difsnid f1_difsnid a_csn a_cdif a_cun f0_difsnid a_wceq p_sylib f1_difsnid f0_difsnid a_wcel f0_difsnid f1_difsnid a_csn a_cdif f1_difsnid a_csn a_cun f1_difsnid a_csn f0_difsnid f1_difsnid a_csn a_cdif a_cun f0_difsnid p_syl5eq $.
$}

$(Note that ` x ` is a dummy variable in the proof below. $)

$(Compute the power set of the empty set.  Theorem 89 of [Suppes] p. 47.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)

${
	$v  $.
	i0_pw0 $f set x $.
	p_pw0 $p |- ~P (/) = { (/) } $= i0_pw0 a_sup_set_class p_ss0b i0_pw0 a_sup_set_class a_c0 a_wss i0_pw0 a_sup_set_class a_c0 a_wceq i0_pw0 p_abbii i0_pw0 a_c0 a_df-pw i0_pw0 a_c0 a_df-sn i0_pw0 a_sup_set_class a_c0 a_wss i0_pw0 a_cab i0_pw0 a_sup_set_class a_c0 a_wceq i0_pw0 a_cab a_c0 a_cpw a_c0 a_csn p_3eqtr4i $.
$}

$(Compute the power set of the power set of the empty set.  (See ~ pw0 for
       the power set of the empty set.)  Theorem 90 of [Suppes] p. 48.
       Although this theorem is a special case of ~ pwsn , we have chosen to
       show a direct elementary proof.  (Contributed by NM, 7-Aug-1994.) $)

${
	$v  $.
	$d x y  $.
	i0_pwpw0 $f set x $.
	i1_pwpw0 $f set y $.
	p_pwpw0 $p |- ~P { (/) } = { (/) , { (/) } } $= i1_pwpw0 i0_pwpw0 a_sup_set_class a_c0 a_csn p_dfss2 i1_pwpw0 a_c0 p_elsn i1_pwpw0 a_sup_set_class a_c0 a_csn a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel p_imbi2i i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_csn a_wcel a_wi i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wi i1_pwpw0 p_albii i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_csn a_wcel a_wi i1_pwpw0 a_wal i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wi i1_pwpw0 a_wal p_bitri i1_pwpw0 i0_pwpw0 a_sup_set_class p_neq0 i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq i1_pwpw0 p_exintr i0_pwpw0 a_sup_set_class a_c0 a_wceq a_wn i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_wex i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wi i1_pwpw0 a_wal i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wa i1_pwpw0 a_wex p_syl5bi i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq i1_pwpw0 p_exancom i1_pwpw0 a_c0 i0_pwpw0 a_sup_set_class a_df-clel i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wa i1_pwpw0 a_wex i1_pwpw0 a_sup_set_class a_c0 a_wceq i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel a_wa i1_pwpw0 a_wex a_c0 i0_pwpw0 a_sup_set_class a_wcel p_bitr4i a_c0 i0_pwpw0 a_sup_set_class p_snssi i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wa i1_pwpw0 a_wex a_c0 i0_pwpw0 a_sup_set_class a_wcel a_c0 a_csn i0_pwpw0 a_sup_set_class a_wss p_sylbi i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wi i1_pwpw0 a_wal i0_pwpw0 a_sup_set_class a_c0 a_wceq a_wn i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wa i1_pwpw0 a_wex a_c0 a_csn i0_pwpw0 a_sup_set_class a_wss p_syl6 i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i1_pwpw0 a_sup_set_class i0_pwpw0 a_sup_set_class a_wcel i1_pwpw0 a_sup_set_class a_c0 a_wceq a_wi i1_pwpw0 a_wal i0_pwpw0 a_sup_set_class a_c0 a_wceq a_wn a_c0 a_csn i0_pwpw0 a_sup_set_class a_wss a_wi p_sylbi i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_sup_set_class a_c0 a_wceq a_wn a_c0 a_csn i0_pwpw0 a_sup_set_class a_wss p_anc2li i0_pwpw0 a_sup_set_class a_c0 a_csn p_eqss i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_sup_set_class a_c0 a_wceq a_wn i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss a_c0 a_csn i0_pwpw0 a_sup_set_class a_wss a_wa i0_pwpw0 a_sup_set_class a_c0 a_csn a_wceq p_syl6ibr i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_sup_set_class a_c0 a_wceq i0_pwpw0 a_sup_set_class a_c0 a_csn a_wceq p_orrd a_c0 a_csn p_0ss i0_pwpw0 a_sup_set_class a_c0 a_c0 a_csn p_sseq1 i0_pwpw0 a_sup_set_class a_c0 a_wceq i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss a_c0 a_c0 a_csn a_wss p_mpbiri i0_pwpw0 a_sup_set_class a_c0 a_csn p_eqimss i0_pwpw0 a_sup_set_class a_c0 a_wceq i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_sup_set_class a_c0 a_csn a_wceq p_jaoi i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_sup_set_class a_c0 a_wceq i0_pwpw0 a_sup_set_class a_c0 a_csn a_wceq a_wo p_impbii i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_sup_set_class a_c0 a_wceq i0_pwpw0 a_sup_set_class a_c0 a_csn a_wceq a_wo i0_pwpw0 p_abbii i0_pwpw0 a_c0 a_csn a_df-pw i0_pwpw0 a_c0 a_c0 a_csn p_dfpr2 i0_pwpw0 a_sup_set_class a_c0 a_csn a_wss i0_pwpw0 a_cab i0_pwpw0 a_sup_set_class a_c0 a_wceq i0_pwpw0 a_sup_set_class a_c0 a_csn a_wceq a_wo i0_pwpw0 a_cab a_c0 a_csn a_cpw a_c0 a_c0 a_csn a_cpr p_3eqtr4i $.
$}

$(A singleton is a subset of an unordered pair containing its member.
     (Contributed by NM, 27-Aug-2004.) $)

${
	$v A B  $.
	f0_snsspr1 $f class A $.
	f1_snsspr1 $f class B $.
	p_snsspr1 $p |- { A } C_ { A , B } $= f0_snsspr1 a_csn f1_snsspr1 a_csn p_ssun1 f0_snsspr1 f1_snsspr1 a_df-pr f0_snsspr1 a_csn f0_snsspr1 a_csn f1_snsspr1 a_csn a_cun f0_snsspr1 f1_snsspr1 a_cpr p_sseqtr4i $.
$}

$(A singleton is a subset of an unordered pair containing its member.
     (Contributed by NM, 2-May-2009.) $)

${
	$v A B  $.
	f0_snsspr2 $f class A $.
	f1_snsspr2 $f class B $.
	p_snsspr2 $p |- { B } C_ { A , B } $= f1_snsspr2 a_csn f0_snsspr2 a_csn p_ssun2 f0_snsspr2 f1_snsspr2 a_df-pr f1_snsspr2 a_csn f0_snsspr2 a_csn f1_snsspr2 a_csn a_cun f0_snsspr2 f1_snsspr2 a_cpr p_sseqtr4i $.
$}

$(A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) $)

${
	$v A B C  $.
	f0_snsstp1 $f class A $.
	f1_snsstp1 $f class B $.
	f2_snsstp1 $f class C $.
	p_snsstp1 $p |- { A } C_ { A , B , C } $= f0_snsstp1 f1_snsstp1 p_snsspr1 f0_snsstp1 f1_snsstp1 a_cpr f2_snsstp1 a_csn p_ssun1 f0_snsstp1 a_csn f0_snsstp1 f1_snsstp1 a_cpr f0_snsstp1 f1_snsstp1 a_cpr f2_snsstp1 a_csn a_cun p_sstri f0_snsstp1 f1_snsstp1 f2_snsstp1 a_df-tp f0_snsstp1 a_csn f0_snsstp1 f1_snsstp1 a_cpr f2_snsstp1 a_csn a_cun f0_snsstp1 f1_snsstp1 f2_snsstp1 a_ctp p_sseqtr4i $.
$}

$(A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) $)

${
	$v A B C  $.
	f0_snsstp2 $f class A $.
	f1_snsstp2 $f class B $.
	f2_snsstp2 $f class C $.
	p_snsstp2 $p |- { B } C_ { A , B , C } $= f0_snsstp2 f1_snsstp2 p_snsspr2 f0_snsstp2 f1_snsstp2 a_cpr f2_snsstp2 a_csn p_ssun1 f1_snsstp2 a_csn f0_snsstp2 f1_snsstp2 a_cpr f0_snsstp2 f1_snsstp2 a_cpr f2_snsstp2 a_csn a_cun p_sstri f0_snsstp2 f1_snsstp2 f2_snsstp2 a_df-tp f1_snsstp2 a_csn f0_snsstp2 f1_snsstp2 a_cpr f2_snsstp2 a_csn a_cun f0_snsstp2 f1_snsstp2 f2_snsstp2 a_ctp p_sseqtr4i $.
$}

$(A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) $)

${
	$v A B C  $.
	f0_snsstp3 $f class A $.
	f1_snsstp3 $f class B $.
	f2_snsstp3 $f class C $.
	p_snsstp3 $p |- { C } C_ { A , B , C } $= f2_snsstp3 a_csn f0_snsstp3 f1_snsstp3 a_cpr p_ssun2 f0_snsstp3 f1_snsstp3 f2_snsstp3 a_df-tp f2_snsstp3 a_csn f0_snsstp3 f1_snsstp3 a_cpr f2_snsstp3 a_csn a_cun f0_snsstp3 f1_snsstp3 f2_snsstp3 a_ctp p_sseqtr4i $.
$}

$(A pair of elements of a class is a subset of the class.  Theorem 7.5 of
       [Quine] p. 49.  (Contributed by NM, 30-May-1994.)  (Proof shortened by
       Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_prss $f class A $.
	f1_prss $f class B $.
	f2_prss $f class C $.
	e0_prss $e |- A e. _V $.
	e1_prss $e |- B e. _V $.
	p_prss $p |- ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) $= f0_prss a_csn f1_prss a_csn f2_prss p_unss e0_prss f0_prss f2_prss p_snss e1_prss f1_prss f2_prss p_snss f0_prss f2_prss a_wcel f0_prss a_csn f2_prss a_wss f1_prss f2_prss a_wcel f1_prss a_csn f2_prss a_wss p_anbi12i f0_prss f1_prss a_df-pr f0_prss f1_prss a_cpr f0_prss a_csn f1_prss a_csn a_cun f2_prss p_sseq1i f0_prss a_csn f2_prss a_wss f1_prss a_csn f2_prss a_wss a_wa f0_prss a_csn f1_prss a_csn a_cun f2_prss a_wss f0_prss f2_prss a_wcel f1_prss f2_prss a_wcel a_wa f0_prss f1_prss a_cpr f2_prss a_wss p_3bitr4i $.
$}

$(A pair of elements of a class is a subset of the class.  Theorem 7.5 of
       [Quine] p. 49.  (Contributed by NM, 22-Mar-2006.)  (Proof shortened by
       Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C V W  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_prssg $f class A $.
	f1_prssg $f class B $.
	f2_prssg $f class C $.
	f3_prssg $f class V $.
	f4_prssg $f class W $.
	p_prssg $p |- ( ( A e. V /\ B e. W ) -> ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) ) $= f0_prssg f2_prssg f3_prssg p_snssg f1_prssg f2_prssg f4_prssg p_snssg f0_prssg f3_prssg a_wcel f0_prssg f2_prssg a_wcel f0_prssg a_csn f2_prssg a_wss f1_prssg f4_prssg a_wcel f1_prssg f2_prssg a_wcel f1_prssg a_csn f2_prssg a_wss p_bi2anan9 f0_prssg a_csn f1_prssg a_csn f2_prssg p_unss f0_prssg f1_prssg a_df-pr f0_prssg f1_prssg a_cpr f0_prssg a_csn f1_prssg a_csn a_cun f2_prssg p_sseq1i f0_prssg a_csn f2_prssg a_wss f1_prssg a_csn f2_prssg a_wss a_wa f0_prssg a_csn f1_prssg a_csn a_cun f2_prssg a_wss f0_prssg f1_prssg a_cpr f2_prssg a_wss p_bitr4i f0_prssg f3_prssg a_wcel f1_prssg f4_prssg a_wcel a_wa f0_prssg f2_prssg a_wcel f1_prssg f2_prssg a_wcel a_wa f0_prssg a_csn f2_prssg a_wss f1_prssg a_csn f2_prssg a_wss a_wa f0_prssg f1_prssg a_cpr f2_prssg a_wss p_syl6bb $.
$}

$(A pair of elements of a class is a subset of the class.  (Contributed by
     NM, 16-Jan-2015.) $)

${
	$v A B C  $.
	f0_prssi $f class A $.
	f1_prssi $f class B $.
	f2_prssi $f class C $.
	p_prssi $p |- ( ( A e. C /\ B e. C ) -> { A , B } C_ C ) $= f0_prssi f1_prssi f2_prssi f2_prssi f2_prssi p_prssg f0_prssi f2_prssi a_wcel f1_prssi f2_prssi a_wcel a_wa f0_prssi f1_prssi a_cpr f2_prssi a_wss p_ibi $.
$}

$(The subsets of a singleton.  (Contributed by NM, 24-Apr-2004.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_sssn $f class A $.
	f1_sssn $f class B $.
	i0_sssn $f set x $.
	p_sssn $p |- ( A C_ { B } <-> ( A = (/) \/ A = { B } ) ) $= i0_sssn f0_sssn p_neq0 f0_sssn f1_sssn a_csn i0_sssn a_sup_set_class p_ssel i0_sssn a_sup_set_class f1_sssn p_elsni f0_sssn f1_sssn a_csn a_wss i0_sssn a_sup_set_class f0_sssn a_wcel i0_sssn a_sup_set_class f1_sssn a_csn a_wcel i0_sssn a_sup_set_class f1_sssn a_wceq p_syl6 i0_sssn a_sup_set_class f1_sssn f0_sssn p_eleq1 f0_sssn f1_sssn a_csn a_wss i0_sssn a_sup_set_class f0_sssn a_wcel i0_sssn a_sup_set_class f1_sssn a_wceq i0_sssn a_sup_set_class f0_sssn a_wcel f1_sssn f0_sssn a_wcel a_wb p_syl6 f0_sssn f1_sssn a_csn a_wss i0_sssn a_sup_set_class f0_sssn a_wcel f1_sssn f0_sssn a_wcel p_ibd f0_sssn f1_sssn a_csn a_wss i0_sssn a_sup_set_class f0_sssn a_wcel f1_sssn f0_sssn a_wcel i0_sssn p_exlimdv f0_sssn a_c0 a_wceq a_wn i0_sssn a_sup_set_class f0_sssn a_wcel i0_sssn a_wex f0_sssn f1_sssn a_csn a_wss f1_sssn f0_sssn a_wcel p_syl5bi f1_sssn f0_sssn p_snssi f0_sssn f1_sssn a_csn a_wss f0_sssn a_c0 a_wceq a_wn f1_sssn f0_sssn a_wcel f1_sssn a_csn f0_sssn a_wss p_syl6 f0_sssn f1_sssn a_csn a_wss f0_sssn a_c0 a_wceq a_wn f1_sssn a_csn f0_sssn a_wss p_anc2li f0_sssn f1_sssn a_csn p_eqss f0_sssn f1_sssn a_csn a_wss f0_sssn a_c0 a_wceq a_wn f0_sssn f1_sssn a_csn a_wss f1_sssn a_csn f0_sssn a_wss a_wa f0_sssn f1_sssn a_csn a_wceq p_syl6ibr f0_sssn f1_sssn a_csn a_wss f0_sssn a_c0 a_wceq f0_sssn f1_sssn a_csn a_wceq p_orrd f1_sssn a_csn p_0ss f0_sssn a_c0 f1_sssn a_csn p_sseq1 f0_sssn a_c0 a_wceq f0_sssn f1_sssn a_csn a_wss a_c0 f1_sssn a_csn a_wss p_mpbiri f0_sssn f1_sssn a_csn p_eqimss f0_sssn a_c0 a_wceq f0_sssn f1_sssn a_csn a_wss f0_sssn f1_sssn a_csn a_wceq p_jaoi f0_sssn f1_sssn a_csn a_wss f0_sssn a_c0 a_wceq f0_sssn f1_sssn a_csn a_wceq a_wo p_impbii $.
$}

$(The property of being sandwiched between two sets naturally splits under
       union with a singleton.  This is the induction hypothesis for the
       determination of large powersets such as ~ pwtp .  (Contributed by Mario
       Carneiro, 2-Jul-2016.) $)

${
	$v A B C D  $.
	$d A  $.
	$d B  $.
	f0_ssunsn2 $f class A $.
	f1_ssunsn2 $f class B $.
	f2_ssunsn2 $f class C $.
	f3_ssunsn2 $f class D $.
	p_ssunsn2 $p |- ( ( B C_ A /\ A C_ ( C u. { D } ) ) <-> ( ( B C_ A /\ A C_ C ) \/ ( ( B u. { D } ) C_ A /\ A C_ ( C u. { D } ) ) ) ) $= f3_ssunsn2 f0_ssunsn2 p_snssi f1_ssunsn2 f3_ssunsn2 a_csn f0_ssunsn2 p_unss f1_ssunsn2 f0_ssunsn2 a_wss f3_ssunsn2 a_csn f0_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss p_bicomi f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss f3_ssunsn2 a_csn f0_ssunsn2 a_wss p_rbaibr f3_ssunsn2 f0_ssunsn2 a_wcel f3_ssunsn2 a_csn f0_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss a_wb p_syl f3_ssunsn2 f0_ssunsn2 a_wcel f1_ssunsn2 f0_ssunsn2 a_wss f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss p_anbi1d f3_ssunsn2 f0_ssunsn2 p_snssi f1_ssunsn2 f3_ssunsn2 a_csn f0_ssunsn2 p_unss f1_ssunsn2 f0_ssunsn2 a_wss f3_ssunsn2 a_csn f0_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss p_biimpi f1_ssunsn2 f0_ssunsn2 a_wss f3_ssunsn2 a_csn f0_ssunsn2 a_wss f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss p_expcom f3_ssunsn2 f0_ssunsn2 a_wcel f3_ssunsn2 a_csn f0_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss a_wi p_syl f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn p_ssun3 f0_ssunsn2 f2_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wi f3_ssunsn2 f0_ssunsn2 a_wcel p_a1i f3_ssunsn2 f0_ssunsn2 a_wcel f1_ssunsn2 f0_ssunsn2 a_wss f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss p_anim12d f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa p_pm4.72 f3_ssunsn2 f0_ssunsn2 a_wcel f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa a_wi f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa a_wo a_wb p_sylib f3_ssunsn2 f0_ssunsn2 a_wcel f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa a_wo p_bitrd f0_ssunsn2 f3_ssunsn2 p_disjsn f0_ssunsn2 f3_ssunsn2 a_csn p_disj3 f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f3_ssunsn2 a_csn a_cin a_c0 a_wceq f0_ssunsn2 f0_ssunsn2 f3_ssunsn2 a_csn a_cdif a_wceq p_bitr3i f0_ssunsn2 f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 p_sseq1 f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f0_ssunsn2 f3_ssunsn2 a_csn a_cdif a_wceq f0_ssunsn2 f2_ssunsn2 a_wss f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 a_wss a_wb p_sylbi f3_ssunsn2 a_csn f2_ssunsn2 p_uncom f3_ssunsn2 a_csn f2_ssunsn2 a_cun f2_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 p_sseq2i f0_ssunsn2 f3_ssunsn2 a_csn f2_ssunsn2 p_ssundif f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss f0_ssunsn2 f3_ssunsn2 a_csn f2_ssunsn2 a_cun a_wss f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 a_wss p_bitr3i f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f2_ssunsn2 a_wss f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss p_syl6rbbr f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss f0_ssunsn2 f2_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss p_anbi2d f1_ssunsn2 f3_ssunsn2 a_csn f0_ssunsn2 p_unss f1_ssunsn2 f0_ssunsn2 a_wss f3_ssunsn2 a_csn f0_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss p_bicomi f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss f3_ssunsn2 a_csn f0_ssunsn2 a_wss p_simplbi f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss a_wi f3_ssunsn2 f0_ssunsn2 a_wcel a_wn p_a1i f0_ssunsn2 f3_ssunsn2 p_disjsn f0_ssunsn2 f3_ssunsn2 a_csn p_disj3 f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f3_ssunsn2 a_csn a_cin a_c0 a_wceq f0_ssunsn2 f0_ssunsn2 f3_ssunsn2 a_csn a_cdif a_wceq p_bitr3i f0_ssunsn2 f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 p_sseq1 f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f0_ssunsn2 f3_ssunsn2 a_csn a_cdif a_wceq f0_ssunsn2 f2_ssunsn2 a_wss f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 a_wss a_wb p_sylbi f3_ssunsn2 a_csn f2_ssunsn2 p_uncom f3_ssunsn2 a_csn f2_ssunsn2 a_cun f2_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 p_sseq2i f0_ssunsn2 f3_ssunsn2 a_csn f2_ssunsn2 p_ssundif f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss f0_ssunsn2 f3_ssunsn2 a_csn f2_ssunsn2 a_cun a_wss f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 a_wss p_bitr3i f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f2_ssunsn2 a_wss f0_ssunsn2 f3_ssunsn2 a_csn a_cdif f2_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss p_syl6rbbr f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss f0_ssunsn2 f2_ssunsn2 a_wss p_biimpd f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss f0_ssunsn2 f2_ssunsn2 a_wss p_anim12d f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa p_pm4.72 f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa a_wi f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa a_wo a_wb p_sylib f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa p_orcom f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa a_wo f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa a_wo p_syl6bb f3_ssunsn2 f0_ssunsn2 a_wcel a_wn f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa a_wo p_bitrd f3_ssunsn2 f0_ssunsn2 a_wcel f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa f1_ssunsn2 f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 a_wss a_wa f1_ssunsn2 f3_ssunsn2 a_csn a_cun f0_ssunsn2 a_wss f0_ssunsn2 f2_ssunsn2 f3_ssunsn2 a_csn a_cun a_wss a_wa a_wo a_wb p_pm2.61i $.
$}

$(Possible values for a set sandwiched between another set and it plus a
       singleton.  (Contributed by Mario Carneiro, 2-Jul-2016.) $)

${
	$v A B C  $.
	$d A  $.
	$d B  $.
	f0_ssunsn $f class A $.
	f1_ssunsn $f class B $.
	f2_ssunsn $f class C $.
	p_ssunsn $p |- ( ( B C_ A /\ A C_ ( B u. { C } ) ) <-> ( A = B \/ A = ( B u. { C } ) ) ) $= f0_ssunsn f1_ssunsn f1_ssunsn f2_ssunsn p_ssunsn2 f1_ssunsn f0_ssunsn a_wss f0_ssunsn f1_ssunsn a_wss p_ancom f0_ssunsn f1_ssunsn p_eqss f1_ssunsn f0_ssunsn a_wss f0_ssunsn f1_ssunsn a_wss a_wa f0_ssunsn f1_ssunsn a_wss f1_ssunsn f0_ssunsn a_wss a_wa f0_ssunsn f1_ssunsn a_wceq p_bitr4i f1_ssunsn f2_ssunsn a_csn a_cun f0_ssunsn a_wss f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wss p_ancom f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun p_eqss f1_ssunsn f2_ssunsn a_csn a_cun f0_ssunsn a_wss f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wss a_wa f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wss f1_ssunsn f2_ssunsn a_csn a_cun f0_ssunsn a_wss a_wa f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wceq p_bitr4i f1_ssunsn f0_ssunsn a_wss f0_ssunsn f1_ssunsn a_wss a_wa f0_ssunsn f1_ssunsn a_wceq f1_ssunsn f2_ssunsn a_csn a_cun f0_ssunsn a_wss f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wss a_wa f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wceq p_orbi12i f1_ssunsn f0_ssunsn a_wss f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wss a_wa f1_ssunsn f0_ssunsn a_wss f0_ssunsn f1_ssunsn a_wss a_wa f1_ssunsn f2_ssunsn a_csn a_cun f0_ssunsn a_wss f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wss a_wa a_wo f0_ssunsn f1_ssunsn a_wceq f0_ssunsn f1_ssunsn f2_ssunsn a_csn a_cun a_wceq a_wo p_bitri $.
$}

$(Two ways to express that a nonempty set equals a singleton.
       (Contributed by NM, 15-Dec-2007.) $)

${
	$v x A B  $.
	$d x A  $.
	$d x B  $.
	f0_eqsn $f set x $.
	f1_eqsn $f class A $.
	f2_eqsn $f class B $.
	p_eqsn $p |- ( A =/= (/) -> ( A = { B } <-> A. x e. A x = B ) ) $= f1_eqsn f2_eqsn a_csn p_eqimss f1_eqsn a_c0 a_df-ne f1_eqsn f2_eqsn p_sssn f1_eqsn f2_eqsn a_csn a_wss f1_eqsn a_c0 a_wceq f1_eqsn f2_eqsn a_csn a_wceq a_wo p_biimpi f1_eqsn f2_eqsn a_csn a_wss f1_eqsn a_c0 a_wceq f1_eqsn f2_eqsn a_csn a_wceq p_ord f1_eqsn a_c0 a_wne f1_eqsn a_c0 a_wceq a_wn f1_eqsn f2_eqsn a_csn a_wss f1_eqsn f2_eqsn a_csn a_wceq p_syl5bi f1_eqsn f2_eqsn a_csn a_wss f1_eqsn a_c0 a_wne f1_eqsn f2_eqsn a_csn a_wceq p_com12 f1_eqsn a_c0 a_wne f1_eqsn f2_eqsn a_csn a_wceq f1_eqsn f2_eqsn a_csn a_wss p_impbid2 f0_eqsn f1_eqsn f2_eqsn a_csn p_dfss3 f0_eqsn f2_eqsn p_elsn f0_eqsn a_sup_set_class f2_eqsn a_csn a_wcel f0_eqsn a_sup_set_class f2_eqsn a_wceq f0_eqsn f1_eqsn p_ralbii f1_eqsn f2_eqsn a_csn a_wss f0_eqsn a_sup_set_class f2_eqsn a_csn a_wcel f0_eqsn f1_eqsn a_wral f0_eqsn a_sup_set_class f2_eqsn a_wceq f0_eqsn f1_eqsn a_wral p_bitri f1_eqsn a_c0 a_wne f1_eqsn f2_eqsn a_csn a_wceq f1_eqsn f2_eqsn a_csn a_wss f0_eqsn a_sup_set_class f2_eqsn a_wceq f0_eqsn f1_eqsn a_wral p_syl6bb $.
$}

$(Possible values for a set sandwiched between another set and it plus a
       singleton.  (Contributed by Mario Carneiro, 2-Jul-2016.) $)

${
	$v A B C D  $.
	f0_ssunpr $f class A $.
	f1_ssunpr $f class B $.
	f2_ssunpr $f class C $.
	f3_ssunpr $f class D $.
	p_ssunpr $p |- ( ( B C_ A /\ A C_ ( B u. { C , D } ) ) <-> ( ( A = B \/ A = ( B u. { C } ) ) \/ ( A = ( B u. { D } ) \/ A = ( B u. { C , D } ) ) ) ) $= f2_ssunpr f3_ssunpr a_df-pr f2_ssunpr f3_ssunpr a_cpr f2_ssunpr a_csn f3_ssunpr a_csn a_cun f1_ssunpr p_uneq2i f1_ssunpr f2_ssunpr a_csn f3_ssunpr a_csn p_unass f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun f1_ssunpr f2_ssunpr a_csn f3_ssunpr a_csn a_cun a_cun f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun p_eqtr4i f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun f0_ssunpr p_sseq2i f0_ssunpr f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun a_wss f1_ssunpr f0_ssunpr a_wss p_anbi2i f0_ssunpr f1_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr p_ssunsn2 f0_ssunpr f1_ssunpr f2_ssunpr p_ssunsn f1_ssunpr f2_ssunpr a_csn f3_ssunpr a_csn p_un23 f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun f0_ssunpr p_sseq2i f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun a_wss f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun a_wss f1_ssunpr f3_ssunpr a_csn a_cun f0_ssunpr a_wss p_anbi2i f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr p_ssunsn f2_ssunpr f3_ssunpr a_df-pr f2_ssunpr f3_ssunpr a_cpr f2_ssunpr a_csn f3_ssunpr a_csn a_cun f1_ssunpr p_uneq2i f1_ssunpr f2_ssunpr a_csn f3_ssunpr a_csn p_unass f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun f1_ssunpr f2_ssunpr a_csn f3_ssunpr a_csn a_cun a_cun f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun p_eqtr4i f1_ssunpr f2_ssunpr a_csn f3_ssunpr a_csn p_un23 f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun p_eqtr2i f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun f0_ssunpr p_eqeq2i f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun a_wceq f0_ssunpr f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun a_wceq f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun a_wceq p_orbi2i f1_ssunpr f3_ssunpr a_csn a_cun f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun a_wss a_wa f1_ssunpr f3_ssunpr a_csn a_cun f0_ssunpr a_wss f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun a_wss a_wa f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun a_wceq f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun f2_ssunpr a_csn a_cun a_wceq a_wo f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun a_wceq f0_ssunpr f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun a_wceq a_wo p_3bitri f1_ssunpr f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun a_wss a_wa f0_ssunpr f1_ssunpr a_wceq f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun a_wceq a_wo f1_ssunpr f3_ssunpr a_csn a_cun f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun a_wss a_wa f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun a_wceq f0_ssunpr f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun a_wceq a_wo p_orbi12i f1_ssunpr f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun a_wss a_wa f1_ssunpr f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun a_wss a_wa f1_ssunpr f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun a_wss a_wa f1_ssunpr f3_ssunpr a_csn a_cun f0_ssunpr a_wss f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun f3_ssunpr a_csn a_cun a_wss a_wa a_wo f0_ssunpr f1_ssunpr a_wceq f0_ssunpr f1_ssunpr f2_ssunpr a_csn a_cun a_wceq a_wo f0_ssunpr f1_ssunpr f3_ssunpr a_csn a_cun a_wceq f0_ssunpr f1_ssunpr f2_ssunpr f3_ssunpr a_cpr a_cun a_wceq a_wo a_wo p_3bitri $.
$}

$(The subsets of a pair.  (Contributed by NM, 16-Mar-2006.)  (Proof
       shortened by Mario Carneiro, 2-Jul-2016.) $)

${
	$v A B C  $.
	f0_sspr $f class A $.
	f1_sspr $f class B $.
	f2_sspr $f class C $.
	p_sspr $p |- ( A C_ { B , C } <-> ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) ) $= a_c0 f1_sspr f2_sspr a_cpr p_uncom f1_sspr f2_sspr a_cpr p_un0 a_c0 f1_sspr f2_sspr a_cpr a_cun f1_sspr f2_sspr a_cpr a_c0 a_cun f1_sspr f2_sspr a_cpr p_eqtri a_c0 f1_sspr f2_sspr a_cpr a_cun f1_sspr f2_sspr a_cpr f0_sspr p_sseq2i f0_sspr p_0ss a_c0 f0_sspr a_wss f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wss p_biantrur f0_sspr f1_sspr f2_sspr a_cpr a_wss f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wss a_c0 f0_sspr a_wss f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wss a_wa p_bitr3i f0_sspr a_c0 f1_sspr f2_sspr p_ssunpr a_c0 f1_sspr a_csn p_uncom f1_sspr a_csn p_un0 a_c0 f1_sspr a_csn a_cun f1_sspr a_csn a_c0 a_cun f1_sspr a_csn p_eqtri a_c0 f1_sspr a_csn a_cun f1_sspr a_csn f0_sspr p_eqeq2i f0_sspr a_c0 f1_sspr a_csn a_cun a_wceq f0_sspr f1_sspr a_csn a_wceq f0_sspr a_c0 a_wceq p_orbi2i a_c0 f2_sspr a_csn p_uncom f2_sspr a_csn p_un0 a_c0 f2_sspr a_csn a_cun f2_sspr a_csn a_c0 a_cun f2_sspr a_csn p_eqtri a_c0 f2_sspr a_csn a_cun f2_sspr a_csn f0_sspr p_eqeq2i a_c0 f1_sspr f2_sspr a_cpr p_uncom f1_sspr f2_sspr a_cpr p_un0 a_c0 f1_sspr f2_sspr a_cpr a_cun f1_sspr f2_sspr a_cpr a_c0 a_cun f1_sspr f2_sspr a_cpr p_eqtri a_c0 f1_sspr f2_sspr a_cpr a_cun f1_sspr f2_sspr a_cpr f0_sspr p_eqeq2i f0_sspr a_c0 f2_sspr a_csn a_cun a_wceq f0_sspr f2_sspr a_csn a_wceq f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wceq f0_sspr f1_sspr f2_sspr a_cpr a_wceq p_orbi12i f0_sspr a_c0 a_wceq f0_sspr a_c0 f1_sspr a_csn a_cun a_wceq a_wo f0_sspr a_c0 a_wceq f0_sspr f1_sspr a_csn a_wceq a_wo f0_sspr a_c0 f2_sspr a_csn a_cun a_wceq f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wceq a_wo f0_sspr f2_sspr a_csn a_wceq f0_sspr f1_sspr f2_sspr a_cpr a_wceq a_wo p_orbi12i f0_sspr f1_sspr f2_sspr a_cpr a_wss a_c0 f0_sspr a_wss f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wss a_wa f0_sspr a_c0 a_wceq f0_sspr a_c0 f1_sspr a_csn a_cun a_wceq a_wo f0_sspr a_c0 f2_sspr a_csn a_cun a_wceq f0_sspr a_c0 f1_sspr f2_sspr a_cpr a_cun a_wceq a_wo a_wo f0_sspr a_c0 a_wceq f0_sspr f1_sspr a_csn a_wceq a_wo f0_sspr f2_sspr a_csn a_wceq f0_sspr f1_sspr f2_sspr a_cpr a_wceq a_wo a_wo p_3bitri $.
$}

$(The subsets of a triple.  (Contributed by Mario Carneiro,
       2-Jul-2016.) $)

${
	$v A B C D  $.
	f0_sstp $f class A $.
	f1_sstp $f class B $.
	f2_sstp $f class C $.
	f3_sstp $f class D $.
	p_sstp $p |- ( A C_ { B , C , D } <-> ( ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) \/ ( ( A = { D } \/ A = { B , D } ) \/ ( A = { C , D } \/ A = { B , C , D } ) ) ) ) $= f1_sstp f2_sstp f3_sstp a_df-tp f1_sstp f2_sstp f3_sstp a_ctp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun f0_sstp p_sseq2i f0_sstp p_0ss a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss p_biantrur f0_sstp a_c0 f1_sstp f2_sstp a_cpr f3_sstp p_ssunsn2 f0_sstp p_0ss a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr a_wss p_biantrur f0_sstp f1_sstp f2_sstp p_sspr a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr a_wss a_wa f0_sstp f1_sstp f2_sstp a_cpr a_wss f0_sstp a_c0 a_wceq f0_sstp f1_sstp a_csn a_wceq a_wo f0_sstp f2_sstp a_csn a_wceq f0_sstp f1_sstp f2_sstp a_cpr a_wceq a_wo a_wo p_bitr3i a_c0 f3_sstp a_csn p_uncom f3_sstp a_csn p_un0 a_c0 f3_sstp a_csn a_cun f3_sstp a_csn a_c0 a_cun f3_sstp a_csn p_eqtri a_c0 f3_sstp a_csn a_cun f3_sstp a_csn f0_sstp p_sseq1i f1_sstp f2_sstp a_cpr f3_sstp a_csn p_uncom f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun f0_sstp p_sseq2i a_c0 f3_sstp a_csn a_cun f0_sstp a_wss f3_sstp a_csn f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss f0_sstp f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun a_wss p_anbi12i f0_sstp f3_sstp a_csn f1_sstp f2_sstp p_ssunpr f3_sstp a_csn f1_sstp a_csn p_uncom f1_sstp f3_sstp a_df-pr f3_sstp a_csn f1_sstp a_csn a_cun f1_sstp a_csn f3_sstp a_csn a_cun f1_sstp f3_sstp a_cpr p_eqtr4i f3_sstp a_csn f1_sstp a_csn a_cun f1_sstp f3_sstp a_cpr f0_sstp p_eqeq2i f0_sstp f3_sstp a_csn f1_sstp a_csn a_cun a_wceq f0_sstp f1_sstp f3_sstp a_cpr a_wceq f0_sstp f3_sstp a_csn a_wceq p_orbi2i f3_sstp a_csn f2_sstp a_csn p_uncom f2_sstp f3_sstp a_df-pr f3_sstp a_csn f2_sstp a_csn a_cun f2_sstp a_csn f3_sstp a_csn a_cun f2_sstp f3_sstp a_cpr p_eqtr4i f3_sstp a_csn f2_sstp a_csn a_cun f2_sstp f3_sstp a_cpr f0_sstp p_eqeq2i f1_sstp f2_sstp f3_sstp a_df-tp f1_sstp f2_sstp a_cpr f3_sstp a_csn p_uncom f1_sstp f2_sstp f3_sstp a_ctp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun p_eqtr2i f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun f1_sstp f2_sstp f3_sstp a_ctp f0_sstp p_eqeq2i f0_sstp f3_sstp a_csn f2_sstp a_csn a_cun a_wceq f0_sstp f2_sstp f3_sstp a_cpr a_wceq f0_sstp f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun a_wceq f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wceq p_orbi12i f0_sstp f3_sstp a_csn a_wceq f0_sstp f3_sstp a_csn f1_sstp a_csn a_cun a_wceq a_wo f0_sstp f3_sstp a_csn a_wceq f0_sstp f1_sstp f3_sstp a_cpr a_wceq a_wo f0_sstp f3_sstp a_csn f2_sstp a_csn a_cun a_wceq f0_sstp f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun a_wceq a_wo f0_sstp f2_sstp f3_sstp a_cpr a_wceq f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wceq a_wo p_orbi12i a_c0 f3_sstp a_csn a_cun f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss a_wa f3_sstp a_csn f0_sstp a_wss f0_sstp f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun a_wss a_wa f0_sstp f3_sstp a_csn a_wceq f0_sstp f3_sstp a_csn f1_sstp a_csn a_cun a_wceq a_wo f0_sstp f3_sstp a_csn f2_sstp a_csn a_cun a_wceq f0_sstp f3_sstp a_csn f1_sstp f2_sstp a_cpr a_cun a_wceq a_wo a_wo f0_sstp f3_sstp a_csn a_wceq f0_sstp f1_sstp f3_sstp a_cpr a_wceq a_wo f0_sstp f2_sstp f3_sstp a_cpr a_wceq f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wceq a_wo a_wo p_3bitri a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr a_wss a_wa f0_sstp a_c0 a_wceq f0_sstp f1_sstp a_csn a_wceq a_wo f0_sstp f2_sstp a_csn a_wceq f0_sstp f1_sstp f2_sstp a_cpr a_wceq a_wo a_wo a_c0 f3_sstp a_csn a_cun f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss a_wa f0_sstp f3_sstp a_csn a_wceq f0_sstp f1_sstp f3_sstp a_cpr a_wceq a_wo f0_sstp f2_sstp f3_sstp a_cpr a_wceq f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wceq a_wo a_wo p_orbi12i a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss a_wa a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr a_wss a_wa a_c0 f3_sstp a_csn a_cun f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss a_wa a_wo f0_sstp a_c0 a_wceq f0_sstp f1_sstp a_csn a_wceq a_wo f0_sstp f2_sstp a_csn a_wceq f0_sstp f1_sstp f2_sstp a_cpr a_wceq a_wo a_wo f0_sstp f3_sstp a_csn a_wceq f0_sstp f1_sstp f3_sstp a_cpr a_wceq a_wo f0_sstp f2_sstp f3_sstp a_cpr a_wceq f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wceq a_wo a_wo a_wo p_bitri f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss a_c0 f0_sstp a_wss f0_sstp f1_sstp f2_sstp a_cpr f3_sstp a_csn a_cun a_wss a_wa f0_sstp a_c0 a_wceq f0_sstp f1_sstp a_csn a_wceq a_wo f0_sstp f2_sstp a_csn a_wceq f0_sstp f1_sstp f2_sstp a_cpr a_wceq a_wo a_wo f0_sstp f3_sstp a_csn a_wceq f0_sstp f1_sstp f3_sstp a_cpr a_wceq a_wo f0_sstp f2_sstp f3_sstp a_cpr a_wceq f0_sstp f1_sstp f2_sstp f3_sstp a_ctp a_wceq a_wo a_wo a_wo p_3bitri $.
$}

$(A triplet of elements of a class is a subset of the class.  (Contributed
       by NM, 9-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v A B C D  $.
	$d A  $.
	$d B  $.
	$d C  $.
	$d D  $.
	f0_tpss $f class A $.
	f1_tpss $f class B $.
	f2_tpss $f class C $.
	f3_tpss $f class D $.
	e0_tpss $e |- A e. _V $.
	e1_tpss $e |- B e. _V $.
	e2_tpss $e |- C e. _V $.
	p_tpss $p |- ( ( A e. D /\ B e. D /\ C e. D ) <-> { A , B , C } C_ D ) $= f0_tpss f1_tpss a_cpr f2_tpss a_csn f3_tpss p_unss f0_tpss f3_tpss a_wcel f1_tpss f3_tpss a_wcel f2_tpss f3_tpss a_wcel a_df-3an e0_tpss e1_tpss f0_tpss f1_tpss f3_tpss p_prss e2_tpss f2_tpss f3_tpss p_snss f0_tpss f3_tpss a_wcel f1_tpss f3_tpss a_wcel a_wa f0_tpss f1_tpss a_cpr f3_tpss a_wss f2_tpss f3_tpss a_wcel f2_tpss a_csn f3_tpss a_wss p_anbi12i f0_tpss f3_tpss a_wcel f1_tpss f3_tpss a_wcel f2_tpss f3_tpss a_wcel a_w3a f0_tpss f3_tpss a_wcel f1_tpss f3_tpss a_wcel a_wa f2_tpss f3_tpss a_wcel a_wa f0_tpss f1_tpss a_cpr f3_tpss a_wss f2_tpss a_csn f3_tpss a_wss a_wa p_bitri f0_tpss f1_tpss f2_tpss a_df-tp f0_tpss f1_tpss f2_tpss a_ctp f0_tpss f1_tpss a_cpr f2_tpss a_csn a_cun f3_tpss p_sseq1i f0_tpss f1_tpss a_cpr f3_tpss a_wss f2_tpss a_csn f3_tpss a_wss a_wa f0_tpss f1_tpss a_cpr f2_tpss a_csn a_cun f3_tpss a_wss f0_tpss f3_tpss a_wcel f1_tpss f3_tpss a_wcel f2_tpss f3_tpss a_wcel a_w3a f0_tpss f1_tpss f2_tpss a_ctp f3_tpss a_wss p_3bitr4i $.
$}

$(If the singletons of two sets are equal, the two sets are equal.  Part
       of Exercise 4 of [TakeutiZaring] p. 15.  (Contributed by NM,
       27-Aug-1993.) $)

${
	$v A B  $.
	f0_sneqr $f class A $.
	f1_sneqr $f class B $.
	e0_sneqr $e |- A e. _V $.
	p_sneqr $p |- ( { A } = { B } -> A = B ) $= e0_sneqr f0_sneqr p_snid f0_sneqr a_csn f1_sneqr a_csn f0_sneqr p_eleq2 f0_sneqr a_csn f1_sneqr a_csn a_wceq f0_sneqr f0_sneqr a_csn a_wcel f0_sneqr f1_sneqr a_csn a_wcel p_mpbii e0_sneqr f0_sneqr f1_sneqr p_elsnc f0_sneqr a_csn f1_sneqr a_csn a_wceq f0_sneqr f1_sneqr a_csn a_wcel f0_sneqr f1_sneqr a_wceq p_sylib $.
$}

$(If a singleton is a subset of another, their members are equal.
       (Contributed by NM, 28-May-2006.) $)

${
	$v A B  $.
	f0_snsssn $f class A $.
	f1_snsssn $f class B $.
	e0_snsssn $e |- A e. _V $.
	p_snsssn $p |- ( { A } C_ { B } -> A = B ) $= f0_snsssn a_csn f1_snsssn p_sssn e0_snsssn f0_snsssn p_snnz f0_snsssn a_csn a_c0 a_df-ne f0_snsssn a_csn a_c0 a_wne f0_snsssn a_csn a_c0 a_wceq a_wn p_mpbi f0_snsssn a_csn a_c0 a_wceq f0_snsssn f1_snsssn a_wceq p_pm2.21i e0_snsssn f0_snsssn f1_snsssn p_sneqr f0_snsssn a_csn a_c0 a_wceq f0_snsssn f1_snsssn a_wceq f0_snsssn a_csn f1_snsssn a_csn a_wceq p_jaoi f0_snsssn a_csn f1_snsssn a_csn a_wss f0_snsssn a_csn a_c0 a_wceq f0_snsssn a_csn f1_snsssn a_csn a_wceq a_wo f0_snsssn f1_snsssn a_wceq p_sylbi $.
$}

$(Closed form of ~ sneqr .  (Contributed by Scott Fenton, 1-Apr-2011.) $)

${
	$v A B V  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	f0_sneqrg $f class A $.
	f1_sneqrg $f class B $.
	f2_sneqrg $f class V $.
	i0_sneqrg $f set x $.
	p_sneqrg $p |- ( A e. V -> ( { A } = { B } -> A = B ) ) $= i0_sneqrg a_sup_set_class f0_sneqrg p_sneq i0_sneqrg a_sup_set_class f0_sneqrg a_wceq i0_sneqrg a_sup_set_class a_csn f0_sneqrg a_csn f1_sneqrg a_csn p_eqeq1d i0_sneqrg a_sup_set_class f0_sneqrg f1_sneqrg p_eqeq1 i0_sneqrg a_sup_set_class f0_sneqrg a_wceq i0_sneqrg a_sup_set_class a_csn f1_sneqrg a_csn a_wceq f0_sneqrg a_csn f1_sneqrg a_csn a_wceq i0_sneqrg a_sup_set_class f1_sneqrg a_wceq f0_sneqrg f1_sneqrg a_wceq p_imbi12d i0_sneqrg p_vex i0_sneqrg a_sup_set_class f1_sneqrg p_sneqr i0_sneqrg a_sup_set_class a_csn f1_sneqrg a_csn a_wceq i0_sneqrg a_sup_set_class f1_sneqrg a_wceq a_wi f0_sneqrg a_csn f1_sneqrg a_csn a_wceq f0_sneqrg f1_sneqrg a_wceq a_wi i0_sneqrg f0_sneqrg f2_sneqrg p_vtoclg $.
$}

$(Two singletons of sets are equal iff their elements are equal.
     (Contributed by Scott Fenton, 16-Apr-2012.) $)

${
	$v A B V  $.
	f0_sneqbg $f class A $.
	f1_sneqbg $f class B $.
	f2_sneqbg $f class V $.
	p_sneqbg $p |- ( A e. V -> ( { A } = { B } <-> A = B ) ) $= f0_sneqbg f1_sneqbg f2_sneqbg p_sneqrg f0_sneqbg f1_sneqbg p_sneq f0_sneqbg f2_sneqbg a_wcel f0_sneqbg a_csn f1_sneqbg a_csn a_wceq f0_sneqbg f1_sneqbg a_wceq p_impbid1 $.
$}

$(The singleton of a class is a subset of its power class.  (Contributed
       by NM, 5-Aug-1993.) $)

${
	$v A  $.
	$d x A  $.
	f0_snsspw $f class A $.
	i0_snsspw $f set x $.
	p_snsspw $p |- { A } C_ ~P A $= i0_snsspw a_sup_set_class f0_snsspw p_eqimss i0_snsspw f0_snsspw p_elsn i0_snsspw f0_snsspw a_df-pw i0_snsspw a_sup_set_class f0_snsspw a_wss i0_snsspw f0_snsspw a_cpw p_abeq2i i0_snsspw a_sup_set_class f0_snsspw a_wceq i0_snsspw a_sup_set_class f0_snsspw a_wss i0_snsspw a_sup_set_class f0_snsspw a_csn a_wcel i0_snsspw a_sup_set_class f0_snsspw a_cpw a_wcel p_3imtr4i i0_snsspw f0_snsspw a_csn f0_snsspw a_cpw p_ssriv $.
$}

$(An unordered pair belongs to the power class of a class iff each member
       belongs to the class.  (Contributed by NM, 10-Dec-2003.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)

${
	$v A B C  $.
	$d A  $.
	$d B  $.
	$d C  $.
	f0_prsspw $f class A $.
	f1_prsspw $f class B $.
	f2_prsspw $f class C $.
	e0_prsspw $e |- A e. _V $.
	e1_prsspw $e |- B e. _V $.
	p_prsspw $p |- ( { A , B } C_ ~P C <-> ( A C_ C /\ B C_ C ) ) $= e0_prsspw e1_prsspw f0_prsspw f1_prsspw f2_prsspw a_cpw p_prss e0_prsspw f0_prsspw f2_prsspw p_elpw e1_prsspw f1_prsspw f2_prsspw p_elpw f0_prsspw f2_prsspw a_cpw a_wcel f0_prsspw f2_prsspw a_wss f1_prsspw f2_prsspw a_cpw a_wcel f1_prsspw f2_prsspw a_wss p_anbi12i f0_prsspw f1_prsspw a_cpr f2_prsspw a_cpw a_wss f0_prsspw f2_prsspw a_cpw a_wcel f1_prsspw f2_prsspw a_cpw a_wcel a_wa f0_prsspw f2_prsspw a_wss f1_prsspw f2_prsspw a_wss a_wa p_bitr3i $.
$}

$(Reverse equality lemma for unordered pairs.  If two unordered pairs have
       the same second element, the first elements are equal.  (Contributed by
       NM, 18-Oct-1995.) $)

${
	$v A B C  $.
	f0_preqr1 $f class A $.
	f1_preqr1 $f class B $.
	f2_preqr1 $f class C $.
	e0_preqr1 $e |- A e. _V $.
	e1_preqr1 $e |- B e. _V $.
	p_preqr1 $p |- ( { A , C } = { B , C } -> A = B ) $= e0_preqr1 f0_preqr1 f2_preqr1 p_prid1 f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr f0_preqr1 p_eleq2 f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr a_wceq f0_preqr1 f0_preqr1 f2_preqr1 a_cpr a_wcel f0_preqr1 f1_preqr1 f2_preqr1 a_cpr a_wcel p_mpbii e0_preqr1 f0_preqr1 f1_preqr1 f2_preqr1 p_elpr f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr a_wceq f0_preqr1 f1_preqr1 f2_preqr1 a_cpr a_wcel f0_preqr1 f1_preqr1 a_wceq f0_preqr1 f2_preqr1 a_wceq a_wo p_sylib e1_preqr1 f1_preqr1 f2_preqr1 p_prid1 f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr f1_preqr1 p_eleq2 f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr a_wceq f1_preqr1 f0_preqr1 f2_preqr1 a_cpr a_wcel f1_preqr1 f1_preqr1 f2_preqr1 a_cpr a_wcel p_mpbiri e1_preqr1 f1_preqr1 f0_preqr1 f2_preqr1 p_elpr f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr a_wceq f1_preqr1 f0_preqr1 f2_preqr1 a_cpr a_wcel f1_preqr1 f0_preqr1 a_wceq f1_preqr1 f2_preqr1 a_wceq a_wo p_sylib f0_preqr1 f1_preqr1 p_eqcom f0_preqr1 f2_preqr1 f1_preqr1 p_eqeq2 f0_preqr1 f2_preqr1 a_cpr f1_preqr1 f2_preqr1 a_cpr a_wceq f0_preqr1 f1_preqr1 a_wceq f0_preqr1 f2_preqr1 a_wceq f1_preqr1 f0_preqr1 a_wceq f1_preqr1 f2_preqr1 a_wceq p_oplem1 $.
$}

$(Reverse equality lemma for unordered pairs.  If two unordered pairs have
       the same first element, the second elements are equal.  (Contributed by
       NM, 5-Aug-1993.) $)

${
	$v A B C  $.
	f0_preqr2 $f class A $.
	f1_preqr2 $f class B $.
	f2_preqr2 $f class C $.
	e0_preqr2 $e |- A e. _V $.
	e1_preqr2 $e |- B e. _V $.
	p_preqr2 $p |- ( { C , A } = { C , B } -> A = B ) $= f2_preqr2 f0_preqr2 p_prcom f2_preqr2 f1_preqr2 p_prcom f2_preqr2 f0_preqr2 a_cpr f0_preqr2 f2_preqr2 a_cpr f2_preqr2 f1_preqr2 a_cpr f1_preqr2 f2_preqr2 a_cpr p_eqeq12i e0_preqr2 e1_preqr2 f0_preqr2 f1_preqr2 f2_preqr2 p_preqr1 f2_preqr2 f0_preqr2 a_cpr f2_preqr2 f1_preqr2 a_cpr a_wceq f0_preqr2 f2_preqr2 a_cpr f1_preqr2 f2_preqr2 a_cpr a_wceq f0_preqr2 f1_preqr2 a_wceq p_sylbi $.
$}

$(Equality relationship for two unordered pairs.  (Contributed by NM,
       17-Oct-1996.) $)

${
	$v A B C D  $.
	f0_preq12b $f class A $.
	f1_preq12b $f class B $.
	f2_preq12b $f class C $.
	f3_preq12b $f class D $.
	e0_preq12b $e |- A e. _V $.
	e1_preq12b $e |- B e. _V $.
	e2_preq12b $e |- C e. _V $.
	e3_preq12b $e |- D e. _V $.
	p_preq12b $p |- ( { A , B } = { C , D } <-> ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) $= e0_preq12b f0_preq12b f1_preq12b p_prid1 f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr f0_preq12b p_eleq2 f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f0_preq12b f1_preq12b a_cpr a_wcel f0_preq12b f2_preq12b f3_preq12b a_cpr a_wcel p_mpbii e0_preq12b f0_preq12b f2_preq12b f3_preq12b p_elpr f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f2_preq12b f3_preq12b a_cpr a_wcel f0_preq12b f2_preq12b a_wceq f0_preq12b f3_preq12b a_wceq a_wo p_sylib f0_preq12b f2_preq12b f1_preq12b p_preq1 f0_preq12b f2_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f2_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr p_eqeq1d e1_preq12b e3_preq12b f1_preq12b f3_preq12b f2_preq12b p_preqr2 f0_preq12b f2_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f2_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f1_preq12b f3_preq12b a_wceq p_syl6bi f0_preq12b f2_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f1_preq12b f3_preq12b a_wceq p_com12 f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f2_preq12b a_wceq f1_preq12b f3_preq12b a_wceq p_ancld f2_preq12b f3_preq12b p_prcom f2_preq12b f3_preq12b a_cpr f3_preq12b f2_preq12b a_cpr f0_preq12b f1_preq12b a_cpr p_eqeq2i f0_preq12b f3_preq12b f1_preq12b p_preq1 f0_preq12b f3_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f3_preq12b f1_preq12b a_cpr f3_preq12b f2_preq12b a_cpr p_eqeq1d e1_preq12b e2_preq12b f1_preq12b f2_preq12b f3_preq12b p_preqr2 f0_preq12b f3_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f3_preq12b f2_preq12b a_cpr a_wceq f3_preq12b f1_preq12b a_cpr f3_preq12b f2_preq12b a_cpr a_wceq f1_preq12b f2_preq12b a_wceq p_syl6bi f0_preq12b f3_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f3_preq12b f2_preq12b a_cpr a_wceq f1_preq12b f2_preq12b a_wceq p_com12 f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f1_preq12b a_cpr f3_preq12b f2_preq12b a_cpr a_wceq f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq a_wi p_sylbi f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq p_ancld f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f2_preq12b a_wceq f0_preq12b f2_preq12b a_wceq f1_preq12b f3_preq12b a_wceq a_wa f0_preq12b f3_preq12b a_wceq f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq a_wa p_orim12d f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f2_preq12b a_wceq f0_preq12b f3_preq12b a_wceq a_wo f0_preq12b f2_preq12b a_wceq f1_preq12b f3_preq12b a_wceq a_wa f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq a_wa a_wo p_mpd f0_preq12b f1_preq12b f2_preq12b f3_preq12b p_preq12 f0_preq12b f3_preq12b f1_preq12b p_preq1 f3_preq12b f1_preq12b p_prcom f0_preq12b f3_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f3_preq12b f1_preq12b a_cpr f1_preq12b f3_preq12b a_cpr p_syl6eq f1_preq12b f2_preq12b f3_preq12b p_preq1 f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq f0_preq12b f1_preq12b a_cpr f1_preq12b f3_preq12b a_cpr f2_preq12b f3_preq12b a_cpr p_sylan9eq f0_preq12b f2_preq12b a_wceq f1_preq12b f3_preq12b a_wceq a_wa f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq a_wa p_jaoi f0_preq12b f1_preq12b a_cpr f2_preq12b f3_preq12b a_cpr a_wceq f0_preq12b f2_preq12b a_wceq f1_preq12b f3_preq12b a_wceq a_wa f0_preq12b f3_preq12b a_wceq f1_preq12b f2_preq12b a_wceq a_wa a_wo p_impbii $.
$}

$(Equality of two unordered pairs.  (Contributed by NM, 17-Oct-1996.) $)

${
	$v A B C D  $.
	f0_prel12 $f class A $.
	f1_prel12 $f class B $.
	f2_prel12 $f class C $.
	f3_prel12 $f class D $.
	e0_prel12 $e |- A e. _V $.
	e1_prel12 $e |- B e. _V $.
	e2_prel12 $e |- C e. _V $.
	e3_prel12 $e |- D e. _V $.
	p_prel12 $p |- ( -. A = B -> ( { A , B } = { C , D } <-> ( A e. { C , D } /\ B e. { C , D } ) ) ) $= e0_prel12 f0_prel12 f1_prel12 p_prid1 f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr f0_prel12 p_eleq2 f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq f0_prel12 f0_prel12 f1_prel12 a_cpr a_wcel f0_prel12 f2_prel12 f3_prel12 a_cpr a_wcel p_mpbii e1_prel12 f0_prel12 f1_prel12 p_prid2 f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr f1_prel12 p_eleq2 f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq f1_prel12 f0_prel12 f1_prel12 a_cpr a_wcel f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel p_mpbii f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq f0_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel p_jca e0_prel12 f0_prel12 f2_prel12 f3_prel12 p_elpr f1_prel12 f3_prel12 f0_prel12 p_eqeq2 f1_prel12 f3_prel12 a_wceq f0_prel12 f1_prel12 a_wceq f0_prel12 f3_prel12 a_wceq p_notbid f0_prel12 f3_prel12 a_wceq f0_prel12 f2_prel12 a_wceq p_orel2 f1_prel12 f3_prel12 a_wceq f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f3_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f0_prel12 f2_prel12 a_wceq a_wi p_syl6bi f1_prel12 f3_prel12 a_wceq f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f0_prel12 f2_prel12 a_wceq p_com3l f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f1_prel12 f3_prel12 a_wceq f0_prel12 f2_prel12 a_wceq a_wi p_imp f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo a_wa f1_prel12 f3_prel12 a_wceq f0_prel12 f2_prel12 a_wceq p_ancrd f1_prel12 f2_prel12 f0_prel12 p_eqeq2 f1_prel12 f2_prel12 a_wceq f0_prel12 f1_prel12 a_wceq f0_prel12 f2_prel12 a_wceq p_notbid f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq p_orel1 f1_prel12 f2_prel12 a_wceq f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f0_prel12 f3_prel12 a_wceq a_wi p_syl6bi f1_prel12 f2_prel12 a_wceq f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f0_prel12 f3_prel12 a_wceq p_com3l f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f1_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wi p_imp f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo a_wa f1_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq p_ancrd f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo a_wa f1_prel12 f3_prel12 a_wceq f0_prel12 f2_prel12 a_wceq f1_prel12 f3_prel12 a_wceq a_wa f1_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq f1_prel12 f2_prel12 a_wceq a_wa p_orim12d e1_prel12 f1_prel12 f2_prel12 f3_prel12 p_elpr f1_prel12 f2_prel12 a_wceq f1_prel12 f3_prel12 a_wceq p_orcom f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f1_prel12 f2_prel12 a_wceq f1_prel12 f3_prel12 a_wceq a_wo f1_prel12 f3_prel12 a_wceq f1_prel12 f2_prel12 a_wceq a_wo p_bitri e0_prel12 e1_prel12 e2_prel12 e3_prel12 f0_prel12 f1_prel12 f2_prel12 f3_prel12 p_preq12b f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo a_wa f1_prel12 f3_prel12 a_wceq f1_prel12 f2_prel12 a_wceq a_wo f0_prel12 f2_prel12 a_wceq f1_prel12 f3_prel12 a_wceq a_wa f0_prel12 f3_prel12 a_wceq f1_prel12 f2_prel12 a_wceq a_wa a_wo f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq p_3imtr4g f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq a_wi p_ex f0_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f0_prel12 f2_prel12 a_wceq f0_prel12 f3_prel12 a_wceq a_wo f0_prel12 f1_prel12 a_wceq a_wn f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq a_wi p_syl5bi f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq p_imp3a f0_prel12 f1_prel12 a_wceq a_wn f0_prel12 f1_prel12 a_cpr f2_prel12 f3_prel12 a_cpr a_wceq f0_prel12 f2_prel12 f3_prel12 a_cpr a_wcel f1_prel12 f2_prel12 f3_prel12 a_cpr a_wcel a_wa p_impbid2 $.
$}

$(A way to represent ordered pairs using unordered pairs with distinct
       members.  (Contributed by NM, 27-Mar-2007.) $)

${
	$v A B C D  $.
	f0_opthpr $f class A $.
	f1_opthpr $f class B $.
	f2_opthpr $f class C $.
	f3_opthpr $f class D $.
	e0_opthpr $e |- A e. _V $.
	e1_opthpr $e |- B e. _V $.
	e2_opthpr $e |- C e. _V $.
	e3_opthpr $e |- D e. _V $.
	p_opthpr $p |- ( A =/= D -> ( { A , B } = { C , D } <-> ( A = C /\ B = D ) ) ) $= e0_opthpr e1_opthpr e2_opthpr e3_opthpr f0_opthpr f1_opthpr f2_opthpr f3_opthpr p_preq12b f0_opthpr f3_opthpr a_wne f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa p_idd f0_opthpr f3_opthpr a_df-ne f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa a_wi p_pm2.21 f0_opthpr f3_opthpr a_wne f0_opthpr f3_opthpr a_wceq a_wn f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa a_wi a_wi p_sylbi f0_opthpr f3_opthpr a_wne f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa p_imp3a f0_opthpr f3_opthpr a_wne f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq a_wa p_jaod f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq a_wa p_orc f0_opthpr f3_opthpr a_wne f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq a_wa a_wo f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa p_impbid1 f0_opthpr f1_opthpr a_cpr f2_opthpr f3_opthpr a_cpr a_wceq f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa f0_opthpr f3_opthpr a_wceq f1_opthpr f2_opthpr a_wceq a_wa a_wo f0_opthpr f3_opthpr a_wne f0_opthpr f2_opthpr a_wceq f1_opthpr f3_opthpr a_wceq a_wa p_syl5bb $.
$}

$(Closed form of ~ preq12b .  (Contributed by Scott Fenton,
       28-Mar-2014.) $)

${
	$v A B C D V W X Y  $.
	$d A x y z w  $.
	$d B x y z w  $.
	$d C x y z w  $.
	$d D x y z w  $.
	$d V x y z w  $.
	$d W x y z w  $.
	$d X x y z w  $.
	$d Y x y z w  $.
	f0_preq12bg $f class A $.
	f1_preq12bg $f class B $.
	f2_preq12bg $f class C $.
	f3_preq12bg $f class D $.
	f4_preq12bg $f class V $.
	f5_preq12bg $f class W $.
	f6_preq12bg $f class X $.
	f7_preq12bg $f class Y $.
	i0_preq12bg $f set x $.
	i1_preq12bg $f set y $.
	i2_preq12bg $f set z $.
	i3_preq12bg $f set w $.
	p_preq12bg $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) -> ( { A , B } = { C , D } <-> ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) ) $= i0_preq12bg a_sup_set_class f0_preq12bg i1_preq12bg a_sup_set_class p_preq1 i0_preq12bg a_sup_set_class f0_preq12bg a_wceq i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr f0_preq12bg i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr p_eqeq1d i0_preq12bg a_sup_set_class f0_preq12bg i2_preq12bg a_sup_set_class p_eqeq1 i0_preq12bg a_sup_set_class f0_preq12bg a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq p_anbi1d i0_preq12bg a_sup_set_class f0_preq12bg f3_preq12bg p_eqeq1 i0_preq12bg a_sup_set_class f0_preq12bg a_wceq i0_preq12bg a_sup_set_class f3_preq12bg a_wceq f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq p_anbi1d i0_preq12bg a_sup_set_class f0_preq12bg a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa p_orbi12d i0_preq12bg a_sup_set_class f0_preq12bg a_wceq i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo p_bibi12d i0_preq12bg a_sup_set_class f0_preq12bg a_wceq i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb f0_preq12bg i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb f3_preq12bg f7_preq12bg a_wcel p_imbi2d i1_preq12bg a_sup_set_class f1_preq12bg f0_preq12bg p_preq2 i1_preq12bg a_sup_set_class f1_preq12bg a_wceq f0_preq12bg i1_preq12bg a_sup_set_class a_cpr f0_preq12bg f1_preq12bg a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr p_eqeq1d i1_preq12bg a_sup_set_class f1_preq12bg f3_preq12bg p_eqeq1 i1_preq12bg a_sup_set_class f1_preq12bg a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq p_anbi2d i1_preq12bg a_sup_set_class f1_preq12bg i2_preq12bg a_sup_set_class p_eqeq1 i1_preq12bg a_sup_set_class f1_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq f0_preq12bg f3_preq12bg a_wceq p_anbi2d i1_preq12bg a_sup_set_class f1_preq12bg a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa p_orbi12d i1_preq12bg a_sup_set_class f1_preq12bg a_wceq f0_preq12bg i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg f1_preq12bg a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa a_wo p_bibi12d i1_preq12bg a_sup_set_class f1_preq12bg a_wceq f0_preq12bg i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb f0_preq12bg f1_preq12bg a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb f3_preq12bg f7_preq12bg a_wcel p_imbi2d i2_preq12bg a_sup_set_class f2_preq12bg f3_preq12bg p_preq1 i2_preq12bg a_sup_set_class f2_preq12bg a_wceq i2_preq12bg a_sup_set_class f3_preq12bg a_cpr f2_preq12bg f3_preq12bg a_cpr f0_preq12bg f1_preq12bg a_cpr p_eqeq2d i2_preq12bg a_sup_set_class f2_preq12bg f0_preq12bg p_eqeq2 i2_preq12bg a_sup_set_class f2_preq12bg a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq p_anbi1d i2_preq12bg a_sup_set_class f2_preq12bg f1_preq12bg p_eqeq2 i2_preq12bg a_sup_set_class f2_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f2_preq12bg a_wceq f0_preq12bg f3_preq12bg a_wceq p_anbi2d i2_preq12bg a_sup_set_class f2_preq12bg a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg f2_preq12bg a_wceq a_wa p_orbi12d i2_preq12bg a_sup_set_class f2_preq12bg a_wceq f0_preq12bg f1_preq12bg a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg f1_preq12bg a_cpr f2_preq12bg f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa a_wo f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg f2_preq12bg a_wceq a_wa a_wo p_bibi12d i2_preq12bg a_sup_set_class f2_preq12bg a_wceq f0_preq12bg f1_preq12bg a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb f0_preq12bg f1_preq12bg a_cpr f2_preq12bg f3_preq12bg a_cpr a_wceq f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg f2_preq12bg a_wceq a_wa a_wo a_wb f3_preq12bg f7_preq12bg a_wcel p_imbi2d i3_preq12bg a_sup_set_class f3_preq12bg i2_preq12bg a_sup_set_class p_preq2 i3_preq12bg a_sup_set_class f3_preq12bg a_wceq i2_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr p_eqeq2d i3_preq12bg a_sup_set_class f3_preq12bg i1_preq12bg a_sup_set_class p_eqeq2 i3_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq p_anbi2d i3_preq12bg a_sup_set_class f3_preq12bg i0_preq12bg a_sup_set_class p_eqeq2 i3_preq12bg a_sup_set_class f3_preq12bg a_wceq i0_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_wceq i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq p_anbi1d i3_preq12bg a_sup_set_class f3_preq12bg a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_wceq a_wa i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa p_orbi12d i0_preq12bg p_vex i1_preq12bg p_vex i2_preq12bg p_vex i3_preq12bg p_vex i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class p_preq12b i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_cpr a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_wceq a_wa i0_preq12bg a_sup_set_class i3_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo i3_preq12bg f3_preq12bg f7_preq12bg p_vtoclbg f3_preq12bg f7_preq12bg a_wcel i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb a_wi i0_preq12bg a_sup_set_class f4_preq12bg a_wcel i1_preq12bg a_sup_set_class f5_preq12bg a_wcel i2_preq12bg a_sup_set_class f6_preq12bg a_wcel a_w3a p_a1i f3_preq12bg f7_preq12bg a_wcel i0_preq12bg a_sup_set_class i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq i0_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa i0_preq12bg a_sup_set_class f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb a_wi f3_preq12bg f7_preq12bg a_wcel f0_preq12bg i1_preq12bg a_sup_set_class a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq i1_preq12bg a_sup_set_class f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq i1_preq12bg a_sup_set_class i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb a_wi f3_preq12bg f7_preq12bg a_wcel f0_preq12bg f1_preq12bg a_cpr i2_preq12bg a_sup_set_class f3_preq12bg a_cpr a_wceq f0_preq12bg i2_preq12bg a_sup_set_class a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg i2_preq12bg a_sup_set_class a_wceq a_wa a_wo a_wb a_wi f3_preq12bg f7_preq12bg a_wcel f0_preq12bg f1_preq12bg a_cpr f2_preq12bg f3_preq12bg a_cpr a_wceq f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg f2_preq12bg a_wceq a_wa a_wo a_wb a_wi i0_preq12bg i1_preq12bg i2_preq12bg f0_preq12bg f1_preq12bg f2_preq12bg f4_preq12bg f5_preq12bg f6_preq12bg p_vtocl3ga f0_preq12bg f4_preq12bg a_wcel f1_preq12bg f5_preq12bg a_wcel f2_preq12bg f6_preq12bg a_wcel f3_preq12bg f7_preq12bg a_wcel f0_preq12bg f1_preq12bg a_cpr f2_preq12bg f3_preq12bg a_cpr a_wceq f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg f2_preq12bg a_wceq a_wa a_wo a_wb a_wi p_3expa f0_preq12bg f4_preq12bg a_wcel f1_preq12bg f5_preq12bg a_wcel a_wa f2_preq12bg f6_preq12bg a_wcel f3_preq12bg f7_preq12bg a_wcel f0_preq12bg f1_preq12bg a_cpr f2_preq12bg f3_preq12bg a_cpr a_wceq f0_preq12bg f2_preq12bg a_wceq f1_preq12bg f3_preq12bg a_wceq a_wa f0_preq12bg f3_preq12bg a_wceq f1_preq12bg f2_preq12bg a_wceq a_wa a_wo a_wb p_impr $.
$}

$(Equivalence for a pair equal to a singleton.  (Contributed by NM,
       3-Jun-2008.) $)

${
	$v A B C  $.
	f0_preqsn $f class A $.
	f1_preqsn $f class B $.
	f2_preqsn $f class C $.
	e0_preqsn $e |- A e. _V $.
	e1_preqsn $e |- B e. _V $.
	e2_preqsn $e |- C e. _V $.
	p_preqsn $p |- ( { A , B } = { C } <-> ( A = B /\ B = C ) ) $= f2_preqsn p_dfsn2 f2_preqsn a_csn f2_preqsn f2_preqsn a_cpr f0_preqsn f1_preqsn a_cpr p_eqeq2i e0_preqsn e1_preqsn e2_preqsn e2_preqsn f0_preqsn f1_preqsn f2_preqsn f2_preqsn p_preq12b f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa p_oridm f0_preqsn f1_preqsn f2_preqsn p_eqtr3 f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq p_simpr f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq p_jca f0_preqsn f1_preqsn f2_preqsn p_eqtr f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq p_simpr f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq p_jca f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa p_impbii f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa a_wo f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa p_bitri f0_preqsn f1_preqsn a_cpr f2_preqsn f2_preqsn a_cpr a_wceq f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa f0_preqsn f2_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa a_wo f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa p_bitri f0_preqsn f1_preqsn a_cpr f2_preqsn a_csn a_wceq f0_preqsn f1_preqsn a_cpr f2_preqsn f2_preqsn a_cpr a_wceq f0_preqsn f1_preqsn a_wceq f1_preqsn f2_preqsn a_wceq a_wa p_bitri $.
$}

$(Rewrite ~ df-op using ` if ` .  When both arguments are sets, it reduces
       to the standard Kuratowski definition; otherwise, it is defined to be
       the empty set.  (Contributed by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	f0_dfopif $f class A $.
	f1_dfopif $f class B $.
	i0_dfopif $f set x $.
	p_dfopif $p |- <. A , B >. = if ( ( A e. _V /\ B e. _V ) , { { A } , { A , B } } , (/) ) $= i0_dfopif f0_dfopif f1_dfopif a_df-op f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_df-3an f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_w3a f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif p_abbii f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_c0 p_iftrue f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel p_ibar f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr p_abbi2dv f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_c0 a_cif f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab p_eqtr2d f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class a_c0 a_wcel p_pm2.21 f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa a_wn f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class a_c0 a_wcel i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel p_adantrd f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa a_wn f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_c0 p_abssdv f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab p_ss0 f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa a_wn f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab a_c0 a_wss f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab a_c0 a_wceq p_syl f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_c0 p_iffalse f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa a_wn f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab a_c0 f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_c0 a_cif p_eqtr4d f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_c0 a_cif a_wceq p_pm2.61i f0_dfopif f1_dfopif a_cop f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_w3a i0_dfopif a_cab f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa i0_dfopif a_sup_set_class f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_wcel a_wa i0_dfopif a_cab f0_dfopif a_cvv a_wcel f1_dfopif a_cvv a_wcel a_wa f0_dfopif a_csn f0_dfopif f1_dfopif a_cpr a_cpr a_c0 a_cif p_3eqtri $.
$}

$(Value of the ordered pair when the arguments are sets.  (Contributed by
     Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B V W  $.
	f0_dfopg $f class A $.
	f1_dfopg $f class B $.
	f2_dfopg $f class V $.
	f3_dfopg $f class W $.
	p_dfopg $p |- ( ( A e. V /\ B e. W ) -> <. A , B >. = { { A } , { A , B } } ) $= f0_dfopg f2_dfopg p_elex f1_dfopg f3_dfopg p_elex f0_dfopg f1_dfopg p_dfopif f0_dfopg a_cvv a_wcel f1_dfopg a_cvv a_wcel a_wa f0_dfopg a_csn f0_dfopg f1_dfopg a_cpr a_cpr a_c0 p_iftrue f0_dfopg a_cvv a_wcel f1_dfopg a_cvv a_wcel a_wa f0_dfopg f1_dfopg a_cop f0_dfopg a_cvv a_wcel f1_dfopg a_cvv a_wcel a_wa f0_dfopg a_csn f0_dfopg f1_dfopg a_cpr a_cpr a_c0 a_cif f0_dfopg a_csn f0_dfopg f1_dfopg a_cpr a_cpr p_syl5eq f0_dfopg f2_dfopg a_wcel f0_dfopg a_cvv a_wcel f1_dfopg a_cvv a_wcel f0_dfopg f1_dfopg a_cop f0_dfopg a_csn f0_dfopg f1_dfopg a_cpr a_cpr a_wceq f1_dfopg f3_dfopg a_wcel p_syl2an $.
$}

$(Value of an ordered pair when the arguments are sets, with the
       conclusion corresponding to Kuratowski's original definition.
       (Contributed by NM, 25-Jun-1998.) $)

${
	$v A B  $.
	f0_dfop $f class A $.
	f1_dfop $f class B $.
	e0_dfop $e |- A e. _V $.
	e1_dfop $e |- B e. _V $.
	p_dfop $p |- <. A , B >. = { { A } , { A , B } } $= e0_dfop e1_dfop f0_dfop f1_dfop a_cvv a_cvv p_dfopg f0_dfop a_cvv a_wcel f1_dfop a_cvv a_wcel f0_dfop f1_dfop a_cop f0_dfop a_csn f0_dfop f1_dfop a_cpr a_cpr a_wceq p_mp2an $.
$}

$(Equality theorem for ordered pairs.  (Contributed by NM, 25-Jun-1998.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B C  $.
	f0_opeq1 $f class A $.
	f1_opeq1 $f class B $.
	f2_opeq1 $f class C $.
	p_opeq1 $p |- ( A = B -> <. A , C >. = <. B , C >. ) $= f0_opeq1 f1_opeq1 a_cvv p_eleq1 f0_opeq1 f1_opeq1 a_wceq f0_opeq1 a_cvv a_wcel f1_opeq1 a_cvv a_wcel f2_opeq1 a_cvv a_wcel p_anbi1d f0_opeq1 f1_opeq1 p_sneq f0_opeq1 f1_opeq1 f2_opeq1 p_preq1 f0_opeq1 f1_opeq1 a_wceq f0_opeq1 a_csn f1_opeq1 a_csn f0_opeq1 f2_opeq1 a_cpr f1_opeq1 f2_opeq1 a_cpr p_preq12d f0_opeq1 f1_opeq1 a_wceq a_c0 p_eqidd f0_opeq1 f1_opeq1 a_wceq f0_opeq1 a_cvv a_wcel f2_opeq1 a_cvv a_wcel a_wa f1_opeq1 a_cvv a_wcel f2_opeq1 a_cvv a_wcel a_wa f0_opeq1 a_csn f0_opeq1 f2_opeq1 a_cpr a_cpr a_c0 f1_opeq1 a_csn f1_opeq1 f2_opeq1 a_cpr a_cpr a_c0 p_ifbieq12d f0_opeq1 f2_opeq1 p_dfopif f1_opeq1 f2_opeq1 p_dfopif f0_opeq1 f1_opeq1 a_wceq f0_opeq1 a_cvv a_wcel f2_opeq1 a_cvv a_wcel a_wa f0_opeq1 a_csn f0_opeq1 f2_opeq1 a_cpr a_cpr a_c0 a_cif f1_opeq1 a_cvv a_wcel f2_opeq1 a_cvv a_wcel a_wa f1_opeq1 a_csn f1_opeq1 f2_opeq1 a_cpr a_cpr a_c0 a_cif f0_opeq1 f2_opeq1 a_cop f1_opeq1 f2_opeq1 a_cop p_3eqtr4g $.
$}

$(Equality theorem for ordered pairs.  (Contributed by NM, 25-Jun-1998.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B C  $.
	f0_opeq2 $f class A $.
	f1_opeq2 $f class B $.
	f2_opeq2 $f class C $.
	p_opeq2 $p |- ( A = B -> <. C , A >. = <. C , B >. ) $= f0_opeq2 f1_opeq2 a_cvv p_eleq1 f0_opeq2 f1_opeq2 a_wceq f0_opeq2 a_cvv a_wcel f1_opeq2 a_cvv a_wcel f2_opeq2 a_cvv a_wcel p_anbi2d f0_opeq2 f1_opeq2 f2_opeq2 p_preq2 f0_opeq2 f1_opeq2 a_wceq f2_opeq2 f0_opeq2 a_cpr f2_opeq2 f1_opeq2 a_cpr f2_opeq2 a_csn p_preq2d f0_opeq2 f1_opeq2 a_wceq a_c0 p_eqidd f0_opeq2 f1_opeq2 a_wceq f2_opeq2 a_cvv a_wcel f0_opeq2 a_cvv a_wcel a_wa f2_opeq2 a_cvv a_wcel f1_opeq2 a_cvv a_wcel a_wa f2_opeq2 a_csn f2_opeq2 f0_opeq2 a_cpr a_cpr a_c0 f2_opeq2 a_csn f2_opeq2 f1_opeq2 a_cpr a_cpr a_c0 p_ifbieq12d f2_opeq2 f0_opeq2 p_dfopif f2_opeq2 f1_opeq2 p_dfopif f0_opeq2 f1_opeq2 a_wceq f2_opeq2 a_cvv a_wcel f0_opeq2 a_cvv a_wcel a_wa f2_opeq2 a_csn f2_opeq2 f0_opeq2 a_cpr a_cpr a_c0 a_cif f2_opeq2 a_cvv a_wcel f1_opeq2 a_cvv a_wcel a_wa f2_opeq2 a_csn f2_opeq2 f1_opeq2 a_cpr a_cpr a_c0 a_cif f2_opeq2 f0_opeq2 a_cop f2_opeq2 f1_opeq2 a_cop p_3eqtr4g $.
$}

$(Equality theorem for ordered pairs.  (Contributed by NM, 28-May-1995.) $)

${
	$v A B C D  $.
	f0_opeq12 $f class A $.
	f1_opeq12 $f class B $.
	f2_opeq12 $f class C $.
	f3_opeq12 $f class D $.
	p_opeq12 $p |- ( ( A = C /\ B = D ) -> <. A , B >. = <. C , D >. ) $= f0_opeq12 f2_opeq12 f1_opeq12 p_opeq1 f1_opeq12 f3_opeq12 f2_opeq12 p_opeq2 f0_opeq12 f2_opeq12 a_wceq f1_opeq12 f3_opeq12 a_wceq f0_opeq12 f1_opeq12 a_cop f2_opeq12 f1_opeq12 a_cop f2_opeq12 f3_opeq12 a_cop p_sylan9eq $.
$}

$(Equality inference for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)

${
	$v A B C  $.
	f0_opeq1i $f class A $.
	f1_opeq1i $f class B $.
	f2_opeq1i $f class C $.
	e0_opeq1i $e |- A = B $.
	p_opeq1i $p |- <. A , C >. = <. B , C >. $= e0_opeq1i f0_opeq1i f1_opeq1i f2_opeq1i p_opeq1 f0_opeq1i f1_opeq1i a_wceq f0_opeq1i f2_opeq1i a_cop f1_opeq1i f2_opeq1i a_cop a_wceq a_ax-mp $.
$}

$(Equality inference for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)

${
	$v A B C  $.
	f0_opeq2i $f class A $.
	f1_opeq2i $f class B $.
	f2_opeq2i $f class C $.
	e0_opeq2i $e |- A = B $.
	p_opeq2i $p |- <. C , A >. = <. C , B >. $= e0_opeq2i f0_opeq2i f1_opeq2i f2_opeq2i p_opeq2 f0_opeq2i f1_opeq2i a_wceq f2_opeq2i f0_opeq2i a_cop f2_opeq2i f1_opeq2i a_cop a_wceq a_ax-mp $.
$}

$(Equality inference for ordered pairs.  (Contributed by NM,
         16-Dec-2006.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)

${
	$v A B C D  $.
	f0_opeq12i $f class A $.
	f1_opeq12i $f class B $.
	f2_opeq12i $f class C $.
	f3_opeq12i $f class D $.
	e0_opeq12i $e |- A = B $.
	e1_opeq12i $e |- C = D $.
	p_opeq12i $p |- <. A , C >. = <. B , D >. $= e0_opeq12i e1_opeq12i f0_opeq12i f2_opeq12i f1_opeq12i f3_opeq12i p_opeq12 f0_opeq12i f1_opeq12i a_wceq f2_opeq12i f3_opeq12i a_wceq f0_opeq12i f2_opeq12i a_cop f1_opeq12i f3_opeq12i a_cop a_wceq p_mp2an $.
$}

$(Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)

${
	$v ph A B C  $.
	f0_opeq1d $f wff ph $.
	f1_opeq1d $f class A $.
	f2_opeq1d $f class B $.
	f3_opeq1d $f class C $.
	e0_opeq1d $e |- ( ph -> A = B ) $.
	p_opeq1d $p |- ( ph -> <. A , C >. = <. B , C >. ) $= e0_opeq1d f1_opeq1d f2_opeq1d f3_opeq1d p_opeq1 f0_opeq1d f1_opeq1d f2_opeq1d a_wceq f1_opeq1d f3_opeq1d a_cop f2_opeq1d f3_opeq1d a_cop a_wceq p_syl $.
$}

$(Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)

${
	$v ph A B C  $.
	f0_opeq2d $f wff ph $.
	f1_opeq2d $f class A $.
	f2_opeq2d $f class B $.
	f3_opeq2d $f class C $.
	e0_opeq2d $e |- ( ph -> A = B ) $.
	p_opeq2d $p |- ( ph -> <. C , A >. = <. C , B >. ) $= e0_opeq2d f1_opeq2d f2_opeq2d f3_opeq2d p_opeq2 f0_opeq2d f1_opeq2d f2_opeq2d a_wceq f3_opeq2d f1_opeq2d a_cop f3_opeq2d f2_opeq2d a_cop a_wceq p_syl $.
$}

$(Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)

${
	$v ph A B C D  $.
	f0_opeq12d $f wff ph $.
	f1_opeq12d $f class A $.
	f2_opeq12d $f class B $.
	f3_opeq12d $f class C $.
	f4_opeq12d $f class D $.
	e0_opeq12d $e |- ( ph -> A = B ) $.
	e1_opeq12d $e |- ( ph -> C = D ) $.
	p_opeq12d $p |- ( ph -> <. A , C >. = <. B , D >. ) $= e0_opeq12d e1_opeq12d f1_opeq12d f3_opeq12d f2_opeq12d f4_opeq12d p_opeq12 f0_opeq12d f1_opeq12d f2_opeq12d a_wceq f3_opeq12d f4_opeq12d a_wceq f1_opeq12d f3_opeq12d a_cop f2_opeq12d f4_opeq12d a_cop a_wceq p_syl2anc $.
$}

$(Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) $)

${
	$v A B C D  $.
	f0_oteq1 $f class A $.
	f1_oteq1 $f class B $.
	f2_oteq1 $f class C $.
	f3_oteq1 $f class D $.
	p_oteq1 $p |- ( A = B -> <. A , C , D >. = <. B , C , D >. ) $= f0_oteq1 f1_oteq1 f2_oteq1 p_opeq1 f0_oteq1 f1_oteq1 a_wceq f0_oteq1 f2_oteq1 a_cop f1_oteq1 f2_oteq1 a_cop f3_oteq1 p_opeq1d f0_oteq1 f2_oteq1 f3_oteq1 a_df-ot f1_oteq1 f2_oteq1 f3_oteq1 a_df-ot f0_oteq1 f1_oteq1 a_wceq f0_oteq1 f2_oteq1 a_cop f3_oteq1 a_cop f1_oteq1 f2_oteq1 a_cop f3_oteq1 a_cop f0_oteq1 f2_oteq1 f3_oteq1 a_cotp f1_oteq1 f2_oteq1 f3_oteq1 a_cotp p_3eqtr4g $.
$}

$(Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) $)

${
	$v A B C D  $.
	f0_oteq2 $f class A $.
	f1_oteq2 $f class B $.
	f2_oteq2 $f class C $.
	f3_oteq2 $f class D $.
	p_oteq2 $p |- ( A = B -> <. C , A , D >. = <. C , B , D >. ) $= f0_oteq2 f1_oteq2 f2_oteq2 p_opeq2 f0_oteq2 f1_oteq2 a_wceq f2_oteq2 f0_oteq2 a_cop f2_oteq2 f1_oteq2 a_cop f3_oteq2 p_opeq1d f2_oteq2 f0_oteq2 f3_oteq2 a_df-ot f2_oteq2 f1_oteq2 f3_oteq2 a_df-ot f0_oteq2 f1_oteq2 a_wceq f2_oteq2 f0_oteq2 a_cop f3_oteq2 a_cop f2_oteq2 f1_oteq2 a_cop f3_oteq2 a_cop f2_oteq2 f0_oteq2 f3_oteq2 a_cotp f2_oteq2 f1_oteq2 f3_oteq2 a_cotp p_3eqtr4g $.
$}

$(Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) $)

${
	$v A B C D  $.
	f0_oteq3 $f class A $.
	f1_oteq3 $f class B $.
	f2_oteq3 $f class C $.
	f3_oteq3 $f class D $.
	p_oteq3 $p |- ( A = B -> <. C , D , A >. = <. C , D , B >. ) $= f0_oteq3 f1_oteq3 f2_oteq3 f3_oteq3 a_cop p_opeq2 f2_oteq3 f3_oteq3 f0_oteq3 a_df-ot f2_oteq3 f3_oteq3 f1_oteq3 a_df-ot f0_oteq3 f1_oteq3 a_wceq f2_oteq3 f3_oteq3 a_cop f0_oteq3 a_cop f2_oteq3 f3_oteq3 a_cop f1_oteq3 a_cop f2_oteq3 f3_oteq3 f0_oteq3 a_cotp f2_oteq3 f3_oteq3 f1_oteq3 a_cotp p_3eqtr4g $.
$}

$(Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_oteq1d $f wff ph $.
	f1_oteq1d $f class A $.
	f2_oteq1d $f class B $.
	f3_oteq1d $f class C $.
	f4_oteq1d $f class D $.
	e0_oteq1d $e |- ( ph -> A = B ) $.
	p_oteq1d $p |- ( ph -> <. A , C , D >. = <. B , C , D >. ) $= e0_oteq1d f1_oteq1d f2_oteq1d f3_oteq1d f4_oteq1d p_oteq1 f0_oteq1d f1_oteq1d f2_oteq1d a_wceq f1_oteq1d f3_oteq1d f4_oteq1d a_cotp f2_oteq1d f3_oteq1d f4_oteq1d a_cotp a_wceq p_syl $.
$}

$(Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_oteq2d $f wff ph $.
	f1_oteq2d $f class A $.
	f2_oteq2d $f class B $.
	f3_oteq2d $f class C $.
	f4_oteq2d $f class D $.
	e0_oteq2d $e |- ( ph -> A = B ) $.
	p_oteq2d $p |- ( ph -> <. C , A , D >. = <. C , B , D >. ) $= e0_oteq2d f1_oteq2d f2_oteq2d f3_oteq2d f4_oteq2d p_oteq2 f0_oteq2d f1_oteq2d f2_oteq2d a_wceq f3_oteq2d f1_oteq2d f4_oteq2d a_cotp f3_oteq2d f2_oteq2d f4_oteq2d a_cotp a_wceq p_syl $.
$}

$(Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)

${
	$v ph A B C D  $.
	f0_oteq3d $f wff ph $.
	f1_oteq3d $f class A $.
	f2_oteq3d $f class B $.
	f3_oteq3d $f class C $.
	f4_oteq3d $f class D $.
	e0_oteq3d $e |- ( ph -> A = B ) $.
	p_oteq3d $p |- ( ph -> <. C , D , A >. = <. C , D , B >. ) $= e0_oteq3d f1_oteq3d f2_oteq3d f3_oteq3d f4_oteq3d p_oteq3 f0_oteq3d f1_oteq3d f2_oteq3d a_wceq f3_oteq3d f4_oteq3d f1_oteq3d a_cotp f3_oteq3d f4_oteq3d f2_oteq3d a_cotp a_wceq p_syl $.
$}

$(Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)

${
	$v ph A B C D E F  $.
	f0_oteq123d $f wff ph $.
	f1_oteq123d $f class A $.
	f2_oteq123d $f class B $.
	f3_oteq123d $f class C $.
	f4_oteq123d $f class D $.
	f5_oteq123d $f class E $.
	f6_oteq123d $f class F $.
	e0_oteq123d $e |- ( ph -> A = B ) $.
	e1_oteq123d $e |- ( ph -> C = D ) $.
	e2_oteq123d $e |- ( ph -> E = F ) $.
	p_oteq123d $p |- ( ph -> <. A , C , E >. = <. B , D , F >. ) $= e0_oteq123d f0_oteq123d f1_oteq123d f2_oteq123d f3_oteq123d f5_oteq123d p_oteq1d e1_oteq123d f0_oteq123d f3_oteq123d f4_oteq123d f2_oteq123d f5_oteq123d p_oteq2d e2_oteq123d f0_oteq123d f5_oteq123d f6_oteq123d f2_oteq123d f4_oteq123d p_oteq3d f0_oteq123d f1_oteq123d f3_oteq123d f5_oteq123d a_cotp f2_oteq123d f3_oteq123d f5_oteq123d a_cotp f2_oteq123d f4_oteq123d f5_oteq123d a_cotp f2_oteq123d f4_oteq123d f6_oteq123d a_cotp p_3eqtrd $.
$}

$(Bound-variable hypothesis builder for ordered pairs.  (Contributed by
       NM, 14-Nov-1995.) $)

${
	$v x A B  $.
	f0_nfop $f set x $.
	f1_nfop $f class A $.
	f2_nfop $f class B $.
	e0_nfop $e |- F/_ x A $.
	e1_nfop $e |- F/_ x B $.
	p_nfop $p |- F/_ x <. A , B >. $= f1_nfop f2_nfop p_dfopif e0_nfop f0_nfop f1_nfop a_cvv p_nfel1 e1_nfop f0_nfop f2_nfop a_cvv p_nfel1 f1_nfop a_cvv a_wcel f2_nfop a_cvv a_wcel f0_nfop p_nfan e0_nfop f0_nfop f1_nfop p_nfsn e0_nfop e1_nfop f0_nfop f1_nfop f2_nfop p_nfpr f0_nfop f1_nfop a_csn f1_nfop f2_nfop a_cpr p_nfpr f0_nfop a_c0 p_nfcv f1_nfop a_cvv a_wcel f2_nfop a_cvv a_wcel a_wa f0_nfop f1_nfop a_csn f1_nfop f2_nfop a_cpr a_cpr a_c0 p_nfif f0_nfop f1_nfop f2_nfop a_cop f1_nfop a_cvv a_wcel f2_nfop a_cvv a_wcel a_wa f1_nfop a_csn f1_nfop f2_nfop a_cpr a_cpr a_c0 a_cif p_nfcxfr $.
$}

$(Deduction version of bound-variable hypothesis builder ~ nfop .  This
       shows how the deduction version of a not-free theorem such as ~ nfop can
       be created from the corresponding not-free inference theorem.
       (Contributed by NM, 4-Feb-2008.) $)

${
	$v ph x A B  $.
	$d z B  $.
	$d z A  $.
	$d x z  $.
	f0_nfopd $f wff ph $.
	f1_nfopd $f set x $.
	f2_nfopd $f class A $.
	f3_nfopd $f class B $.
	i0_nfopd $f set z $.
	e0_nfopd $e |- ( ph -> F/_ x A ) $.
	e1_nfopd $e |- ( ph -> F/_ x B ) $.
	p_nfopd $p |- ( ph -> F/_ x <. A , B >. ) $= i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd i0_nfopd p_nfaba1 i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd i0_nfopd p_nfaba1 f1_nfopd i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab p_nfop e0_nfopd e1_nfopd f1_nfopd f2_nfopd p_nfnfc1 f1_nfopd f3_nfopd p_nfnfc1 f1_nfopd f2_nfopd a_wnfc f1_nfopd f3_nfopd a_wnfc f1_nfopd p_nfan f1_nfopd i0_nfopd f2_nfopd p_abidnf f1_nfopd f2_nfopd a_wnfc i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab f2_nfopd a_wceq f1_nfopd f3_nfopd a_wnfc p_adantr f1_nfopd i0_nfopd f3_nfopd p_abidnf f1_nfopd f3_nfopd a_wnfc i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab f3_nfopd a_wceq f1_nfopd f2_nfopd a_wnfc p_adantl f1_nfopd f2_nfopd a_wnfc f1_nfopd f3_nfopd a_wnfc a_wa i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab f2_nfopd i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab f3_nfopd p_opeq12d f1_nfopd f2_nfopd a_wnfc f1_nfopd f3_nfopd a_wnfc a_wa f1_nfopd i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab a_cop f2_nfopd f3_nfopd a_cop p_nfceqdf f0_nfopd f1_nfopd f2_nfopd a_wnfc f1_nfopd f3_nfopd a_wnfc f1_nfopd i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab a_cop a_wnfc f1_nfopd f2_nfopd f3_nfopd a_cop a_wnfc a_wb p_syl2anc f0_nfopd f1_nfopd i0_nfopd a_sup_set_class f2_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab i0_nfopd a_sup_set_class f3_nfopd a_wcel f1_nfopd a_wal i0_nfopd a_cab a_cop a_wnfc f1_nfopd f2_nfopd f3_nfopd a_cop a_wnfc p_mpbii $.
$}

$(The ordered pair ` <. A , A >. ` in Kuratowski's representation.
       (Contributed by FL, 28-Dec-2011.) $)

${
	$v A  $.
	f0_opid $f class A $.
	e0_opid $e |- A e. _V $.
	p_opid $p |- <. A , A >. = { { A } } $= f0_opid p_dfsn2 f0_opid a_csn f0_opid f0_opid a_cpr p_eqcomi f0_opid f0_opid a_cpr f0_opid a_csn f0_opid a_csn p_preq2i e0_opid e0_opid f0_opid f0_opid p_dfop f0_opid a_csn p_dfsn2 f0_opid a_csn f0_opid f0_opid a_cpr a_cpr f0_opid a_csn f0_opid a_csn a_cpr f0_opid f0_opid a_cop f0_opid a_csn a_csn p_3eqtr4i $.
$}

$(Restricted quantification over the union of a set and a singleton, using
       implicit substitution.  (Contributed by Paul Chapman, 17-Nov-2012.)
       (Revised by Mario Carneiro, 23-Apr-2015.) $)

${
	$v ph ps x A B C  $.
	$d B x  $.
	$d ps x  $.
	f0_ralunsn $f wff ph $.
	f1_ralunsn $f wff ps $.
	f2_ralunsn $f set x $.
	f3_ralunsn $f class A $.
	f4_ralunsn $f class B $.
	f5_ralunsn $f class C $.
	e0_ralunsn $e |- ( x = B -> ( ph <-> ps ) ) $.
	p_ralunsn $p |- ( B e. C -> ( A. x e. ( A u. { B } ) ph <-> ( A. x e. A ph /\ ps ) ) ) $= f0_ralunsn f2_ralunsn f3_ralunsn f4_ralunsn a_csn p_ralunb e0_ralunsn f0_ralunsn f1_ralunsn f2_ralunsn f4_ralunsn f5_ralunsn p_ralsng f4_ralunsn f5_ralunsn a_wcel f0_ralunsn f2_ralunsn f4_ralunsn a_csn a_wral f1_ralunsn f0_ralunsn f2_ralunsn f3_ralunsn a_wral p_anbi2d f0_ralunsn f2_ralunsn f3_ralunsn f4_ralunsn a_csn a_cun a_wral f0_ralunsn f2_ralunsn f3_ralunsn a_wral f0_ralunsn f2_ralunsn f4_ralunsn a_csn a_wral a_wa f4_ralunsn f5_ralunsn a_wcel f0_ralunsn f2_ralunsn f3_ralunsn a_wral f1_ralunsn a_wa p_syl5bb $.
$}

$(Double restricted quantification over the union of a set and a
       singleton, using implicit substitution.  (Contributed by Paul Chapman,
       17-Nov-2012.) $)

${
	$v ph ps ch th x y A B C  $.
	$d A x  $.
	$d B x y  $.
	$d C x  $.
	$d ch x  $.
	$d ps y  $.
	$d th x  $.
	f0_2ralunsn $f wff ph $.
	f1_2ralunsn $f wff ps $.
	f2_2ralunsn $f wff ch $.
	f3_2ralunsn $f wff th $.
	f4_2ralunsn $f set x $.
	f5_2ralunsn $f set y $.
	f6_2ralunsn $f class A $.
	f7_2ralunsn $f class B $.
	f8_2ralunsn $f class C $.
	e0_2ralunsn $e |- ( x = B -> ( ph <-> ch ) ) $.
	e1_2ralunsn $e |- ( y = B -> ( ph <-> ps ) ) $.
	e2_2ralunsn $e |- ( x = B -> ( ps <-> th ) ) $.
	p_2ralunsn $p |- ( B e. C -> ( A. x e. ( A u. { B } ) A. y e. ( A u. { B } ) ph <-> ( ( A. x e. A A. y e. A ph /\ A. x e. A ps ) /\ ( A. y e. A ch /\ th ) ) ) ) $= e1_2ralunsn f0_2ralunsn f1_2ralunsn f5_2ralunsn f6_2ralunsn f7_2ralunsn f8_2ralunsn p_ralunsn f7_2ralunsn f8_2ralunsn a_wcel f0_2ralunsn f5_2ralunsn f6_2ralunsn f7_2ralunsn a_csn a_cun a_wral f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn a_wa f4_2ralunsn f6_2ralunsn f7_2ralunsn a_csn a_cun p_ralbidv e0_2ralunsn f4_2ralunsn a_sup_set_class f7_2ralunsn a_wceq f0_2ralunsn f2_2ralunsn f5_2ralunsn f6_2ralunsn p_ralbidv e2_2ralunsn f4_2ralunsn a_sup_set_class f7_2ralunsn a_wceq f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f2_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn f3_2ralunsn p_anbi12d f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn a_wa f2_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f3_2ralunsn a_wa f4_2ralunsn f6_2ralunsn f7_2ralunsn f8_2ralunsn p_ralunsn f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn f4_2ralunsn f6_2ralunsn p_r19.26 f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn a_wa f4_2ralunsn f6_2ralunsn a_wral f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f4_2ralunsn f6_2ralunsn a_wral f1_2ralunsn f4_2ralunsn f6_2ralunsn a_wral a_wa f2_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f3_2ralunsn a_wa p_anbi1i f7_2ralunsn f8_2ralunsn a_wcel f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn a_wa f4_2ralunsn f6_2ralunsn f7_2ralunsn a_csn a_cun a_wral f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn a_wa f4_2ralunsn f6_2ralunsn a_wral f2_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f3_2ralunsn a_wa a_wa f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f4_2ralunsn f6_2ralunsn a_wral f1_2ralunsn f4_2ralunsn f6_2ralunsn a_wral a_wa f2_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f3_2ralunsn a_wa a_wa p_syl6bb f7_2ralunsn f8_2ralunsn a_wcel f0_2ralunsn f5_2ralunsn f6_2ralunsn f7_2ralunsn a_csn a_cun a_wral f4_2ralunsn f6_2ralunsn f7_2ralunsn a_csn a_cun a_wral f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f1_2ralunsn a_wa f4_2ralunsn f6_2ralunsn f7_2ralunsn a_csn a_cun a_wral f0_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f4_2ralunsn f6_2ralunsn a_wral f1_2ralunsn f4_2ralunsn f6_2ralunsn a_wral a_wa f2_2ralunsn f5_2ralunsn f6_2ralunsn a_wral f3_2ralunsn a_wa a_wa p_bitrd $.
$}

$(Expansion of an ordered pair when either member is a proper class.
     (Contributed by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B  $.
	f0_opprc $f class A $.
	f1_opprc $f class B $.
	p_opprc $p |- ( -. ( A e. _V /\ B e. _V ) -> <. A , B >. = (/) ) $= f0_opprc f1_opprc p_dfopif f0_opprc a_cvv a_wcel f1_opprc a_cvv a_wcel a_wa f0_opprc a_csn f0_opprc f1_opprc a_cpr a_cpr a_c0 p_iffalse f0_opprc a_cvv a_wcel f1_opprc a_cvv a_wcel a_wa a_wn f0_opprc f1_opprc a_cop f0_opprc a_cvv a_wcel f1_opprc a_cvv a_wcel a_wa f0_opprc a_csn f0_opprc f1_opprc a_cpr a_cpr a_c0 a_cif a_c0 p_syl5eq $.
$}

$(Expansion of an ordered pair when the first member is a proper class.  See
     also ~ opprc .  (Contributed by NM, 10-Apr-2004.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) $)

${
	$v A B  $.
	f0_opprc1 $f class A $.
	f1_opprc1 $f class B $.
	p_opprc1 $p |- ( -. A e. _V -> <. A , B >. = (/) ) $= f0_opprc1 a_cvv a_wcel f1_opprc1 a_cvv a_wcel p_simpl f0_opprc1 a_cvv a_wcel f1_opprc1 a_cvv a_wcel a_wa f0_opprc1 a_cvv a_wcel p_con3i f0_opprc1 f1_opprc1 p_opprc f0_opprc1 a_cvv a_wcel a_wn f0_opprc1 a_cvv a_wcel f1_opprc1 a_cvv a_wcel a_wa a_wn f0_opprc1 f1_opprc1 a_cop a_c0 a_wceq p_syl $.
$}

$(Expansion of an ordered pair when the second member is a proper class.
     See also ~ opprc .  (Contributed by NM, 15-Nov-1994.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) $)

${
	$v A B  $.
	f0_opprc2 $f class A $.
	f1_opprc2 $f class B $.
	p_opprc2 $p |- ( -. B e. _V -> <. A , B >. = (/) ) $= f0_opprc2 a_cvv a_wcel f1_opprc2 a_cvv a_wcel p_simpr f0_opprc2 a_cvv a_wcel f1_opprc2 a_cvv a_wcel a_wa f1_opprc2 a_cvv a_wcel p_con3i f0_opprc2 f1_opprc2 p_opprc f1_opprc2 a_cvv a_wcel a_wn f0_opprc2 a_cvv a_wcel f1_opprc2 a_cvv a_wcel a_wa a_wn f0_opprc2 f1_opprc2 a_cop a_c0 a_wceq p_syl $.
$}

$(If an ordered pair has an element, then its arguments are sets.
     (Contributed by Mario Carneiro, 26-Apr-2015.) $)

${
	$v A B C  $.
	f0_oprcl $f class A $.
	f1_oprcl $f class B $.
	f2_oprcl $f class C $.
	p_oprcl $p |- ( C e. <. A , B >. -> ( A e. _V /\ B e. _V ) ) $= f0_oprcl f1_oprcl a_cop f2_oprcl p_n0i f0_oprcl f1_oprcl p_opprc f2_oprcl f0_oprcl f1_oprcl a_cop a_wcel f0_oprcl f1_oprcl a_cop a_c0 a_wceq f0_oprcl a_cvv a_wcel f1_oprcl a_cvv a_wcel a_wa p_nsyl2 $.
$}

$(The power set of a singleton.  (Contributed by NM, 5-Jun-2006.) $)

${
	$v A  $.
	$d x A  $.
	$d x  $.
	$d x  $.
	f0_pwsn $f class A $.
	i0_pwsn $f set x $.
	p_pwsn $p |- ~P { A } = { (/) , { A } } $= i0_pwsn a_sup_set_class f0_pwsn p_sssn i0_pwsn a_sup_set_class f0_pwsn a_csn a_wss i0_pwsn a_sup_set_class a_c0 a_wceq i0_pwsn a_sup_set_class f0_pwsn a_csn a_wceq a_wo i0_pwsn p_abbii i0_pwsn f0_pwsn a_csn a_df-pw i0_pwsn a_c0 f0_pwsn a_csn p_dfpr2 i0_pwsn a_sup_set_class f0_pwsn a_csn a_wss i0_pwsn a_cab i0_pwsn a_sup_set_class a_c0 a_wceq i0_pwsn a_sup_set_class f0_pwsn a_csn a_wceq a_wo i0_pwsn a_cab f0_pwsn a_csn a_cpw a_c0 f0_pwsn a_csn a_cpr p_3eqtr4i $.
$}

$(The power set of a singleton (direct proof).  TO DO - should we keep
       this?  (Contributed by NM, 5-Jun-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v A  $.
	$d x A  $.
	$d x  $.
	$d x  $.
	$d x y  $.
	$d y A  $.
	f0_pwsnALT $f class A $.
	i0_pwsnALT $f set x $.
	i1_pwsnALT $f set y $.
	p_pwsnALT $p |- ~P { A } = { (/) , { A } } $= i1_pwsnALT i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn p_dfss2 i1_pwsnALT f0_pwsnALT p_elsn i1_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel p_imbi2i i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wcel a_wi i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wi i1_pwsnALT p_albii i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wcel a_wi i1_pwsnALT a_wal i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wi i1_pwsnALT a_wal p_bitri i1_pwsnALT i0_pwsnALT a_sup_set_class p_neq0 i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq i1_pwsnALT p_exintr i0_pwsnALT a_sup_set_class a_c0 a_wceq a_wn i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_wex i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wi i1_pwsnALT a_wal i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wa i1_pwsnALT a_wex p_syl5bi i1_pwsnALT f0_pwsnALT i0_pwsnALT a_sup_set_class a_df-clel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT p_exancom f0_pwsnALT i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel a_wa i1_pwsnALT a_wex i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wa i1_pwsnALT a_wex p_bitr2i f0_pwsnALT i0_pwsnALT a_sup_set_class p_snssi i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wa i1_pwsnALT a_wex f0_pwsnALT i0_pwsnALT a_sup_set_class a_wcel f0_pwsnALT a_csn i0_pwsnALT a_sup_set_class a_wss p_sylbi i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wi i1_pwsnALT a_wal i0_pwsnALT a_sup_set_class a_c0 a_wceq a_wn i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wa i1_pwsnALT a_wex f0_pwsnALT a_csn i0_pwsnALT a_sup_set_class a_wss p_syl6 i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i1_pwsnALT a_sup_set_class i0_pwsnALT a_sup_set_class a_wcel i1_pwsnALT a_sup_set_class f0_pwsnALT a_wceq a_wi i1_pwsnALT a_wal i0_pwsnALT a_sup_set_class a_c0 a_wceq a_wn f0_pwsnALT a_csn i0_pwsnALT a_sup_set_class a_wss a_wi p_sylbi i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_sup_set_class a_c0 a_wceq a_wn f0_pwsnALT a_csn i0_pwsnALT a_sup_set_class a_wss p_anc2li i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn p_eqss i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_sup_set_class a_c0 a_wceq a_wn i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss f0_pwsnALT a_csn i0_pwsnALT a_sup_set_class a_wss a_wa i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wceq p_syl6ibr i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_sup_set_class a_c0 a_wceq i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wceq p_orrd f0_pwsnALT a_csn p_0ss i0_pwsnALT a_sup_set_class a_c0 f0_pwsnALT a_csn p_sseq1 i0_pwsnALT a_sup_set_class a_c0 a_wceq i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss a_c0 f0_pwsnALT a_csn a_wss p_mpbiri i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn p_eqimss i0_pwsnALT a_sup_set_class a_c0 a_wceq i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wceq p_jaoi i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_sup_set_class a_c0 a_wceq i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wceq a_wo p_impbii i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_sup_set_class a_c0 a_wceq i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wceq a_wo i0_pwsnALT p_abbii i0_pwsnALT f0_pwsnALT a_csn a_df-pw i0_pwsnALT a_c0 f0_pwsnALT a_csn p_dfpr2 i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wss i0_pwsnALT a_cab i0_pwsnALT a_sup_set_class a_c0 a_wceq i0_pwsnALT a_sup_set_class f0_pwsnALT a_csn a_wceq a_wo i0_pwsnALT a_cab f0_pwsnALT a_csn a_cpw a_c0 f0_pwsnALT a_csn a_cpr p_3eqtr4i $.
$}

$(The power set of an unordered pair.  (Contributed by NM, 1-May-2009.) $)

${
	$v A B  $.
	$d x A  $.
	$d x B  $.
	$d x  $.
	$d x  $.
	$d A  $.
	f0_pwpr $f class A $.
	f1_pwpr $f class B $.
	i0_pwpr $f set x $.
	p_pwpr $p |- ~P { A , B } = ( { (/) , { A } } u. { { B } , { A , B } } ) $= i0_pwpr a_sup_set_class f0_pwpr f1_pwpr p_sspr i0_pwpr p_vex i0_pwpr a_sup_set_class a_c0 f0_pwpr a_csn p_elpr i0_pwpr p_vex i0_pwpr a_sup_set_class f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr p_elpr i0_pwpr a_sup_set_class a_c0 f0_pwpr a_csn a_cpr a_wcel i0_pwpr a_sup_set_class a_c0 a_wceq i0_pwpr a_sup_set_class f0_pwpr a_csn a_wceq a_wo i0_pwpr a_sup_set_class f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr a_cpr a_wcel i0_pwpr a_sup_set_class f1_pwpr a_csn a_wceq i0_pwpr a_sup_set_class f0_pwpr f1_pwpr a_cpr a_wceq a_wo p_orbi12i i0_pwpr a_sup_set_class f0_pwpr f1_pwpr a_cpr a_wss i0_pwpr a_sup_set_class a_c0 a_wceq i0_pwpr a_sup_set_class f0_pwpr a_csn a_wceq a_wo i0_pwpr a_sup_set_class f1_pwpr a_csn a_wceq i0_pwpr a_sup_set_class f0_pwpr f1_pwpr a_cpr a_wceq a_wo a_wo i0_pwpr a_sup_set_class a_c0 f0_pwpr a_csn a_cpr a_wcel i0_pwpr a_sup_set_class f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr a_cpr a_wcel a_wo p_bitr4i i0_pwpr p_vex i0_pwpr a_sup_set_class f0_pwpr f1_pwpr a_cpr p_elpw i0_pwpr a_sup_set_class a_c0 f0_pwpr a_csn a_cpr f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr a_cpr p_elun i0_pwpr a_sup_set_class f0_pwpr f1_pwpr a_cpr a_wss i0_pwpr a_sup_set_class a_c0 f0_pwpr a_csn a_cpr a_wcel i0_pwpr a_sup_set_class f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr a_cpr a_wcel a_wo i0_pwpr a_sup_set_class f0_pwpr f1_pwpr a_cpr a_cpw a_wcel i0_pwpr a_sup_set_class a_c0 f0_pwpr a_csn a_cpr f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr a_cpr a_cun a_wcel p_3bitr4i i0_pwpr f0_pwpr f1_pwpr a_cpr a_cpw a_c0 f0_pwpr a_csn a_cpr f1_pwpr a_csn f0_pwpr f1_pwpr a_cpr a_cpr a_cun p_eqriv $.
$}

$(The power set of an unordered triple.  (Contributed by Mario Carneiro,
       2-Jul-2016.) $)

${
	$v A B C  $.
	$d x A  $.
	$d x B  $.
	$d x C  $.
	$d x  $.
	$d A  $.
	f0_pwtp $f class A $.
	f1_pwtp $f class B $.
	f2_pwtp $f class C $.
	i0_pwtp $f set x $.
	p_pwtp $p |- ~P { A , B , C } = ( ( { (/) , { A } } u. { { B } , { A , B } } ) u. ( { { C } , { A , C } } u. { { B , C } , { A , B , C } } ) ) $= i0_pwtp p_vex i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp p_elpw i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr p_elun i0_pwtp p_vex i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn p_elpr i0_pwtp p_vex i0_pwtp a_sup_set_class f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr p_elpr i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr a_wcel i0_pwtp a_sup_set_class a_c0 a_wceq i0_pwtp a_sup_set_class f0_pwtp a_csn a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_wcel i0_pwtp a_sup_set_class f1_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp a_cpr a_wceq a_wo p_orbi12i i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun a_wcel i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr a_wcel i0_pwtp a_sup_set_class f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_wcel a_wo i0_pwtp a_sup_set_class a_c0 a_wceq i0_pwtp a_sup_set_class f0_pwtp a_csn a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp a_cpr a_wceq a_wo a_wo p_bitri i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr p_elun i0_pwtp p_vex i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr p_elpr i0_pwtp p_vex i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp p_elpr i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr a_wcel i0_pwtp a_sup_set_class f2_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f2_pwtp a_cpr a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_wcel i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_wceq a_wo p_orbi12i i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun a_wcel i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr a_wcel i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_wcel a_wo i0_pwtp a_sup_set_class f2_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f2_pwtp a_cpr a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_wceq a_wo a_wo p_bitri i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun a_wcel i0_pwtp a_sup_set_class a_c0 a_wceq i0_pwtp a_sup_set_class f0_pwtp a_csn a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp a_cpr a_wceq a_wo a_wo i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun a_wcel i0_pwtp a_sup_set_class f2_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f2_pwtp a_cpr a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_wceq a_wo a_wo p_orbi12i i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun p_elun i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp p_sstp i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun a_wcel i0_pwtp a_sup_set_class f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun a_wcel a_wo i0_pwtp a_sup_set_class a_c0 a_wceq i0_pwtp a_sup_set_class f0_pwtp a_csn a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp a_cpr a_wceq a_wo a_wo i0_pwtp a_sup_set_class f2_pwtp a_csn a_wceq i0_pwtp a_sup_set_class f0_pwtp f2_pwtp a_cpr a_wceq a_wo i0_pwtp a_sup_set_class f1_pwtp f2_pwtp a_cpr a_wceq i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_wceq a_wo a_wo a_wo i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun a_cun a_wcel i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_wss p_3bitr4ri i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpw a_wcel i0_pwtp a_sup_set_class f0_pwtp f1_pwtp f2_pwtp a_ctp a_wss i0_pwtp a_sup_set_class a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun a_cun a_wcel p_bitri i0_pwtp f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpw a_c0 f0_pwtp a_csn a_cpr f1_pwtp a_csn f0_pwtp f1_pwtp a_cpr a_cpr a_cun f2_pwtp a_csn f0_pwtp f2_pwtp a_cpr a_cpr f1_pwtp f2_pwtp a_cpr f0_pwtp f1_pwtp f2_pwtp a_ctp a_cpr a_cun a_cun p_eqriv $.
$}

$(Compute the power set of the power set of the power set of the empty
       set.  (See also ~ pw0 and ~ pwpw0 .)  (Contributed by NM,
       2-May-2009.) $)

${
	$v  $.
	p_pwpwpw0 $p |- ~P { (/) , { (/) } } = ( { (/) , { (/) } } u. { { { (/) } } , { (/) , { (/) } } } ) $= a_c0 a_c0 a_csn p_pwpr $.
$}

$(The power class of the universe is the universe.  Exercise 4.12(d) of
       [Mendelson] p. 235.  (Contributed by NM, 14-Sep-2003.) $)

${
	$v  $.
	i0_pwv $f set x $.
	p_pwv $p |- ~P _V = _V $= i0_pwv a_sup_set_class p_ssv i0_pwv p_vex i0_pwv a_sup_set_class a_cvv p_elpw i0_pwv a_sup_set_class a_cvv a_cpw a_wcel i0_pwv a_sup_set_class a_cvv a_wss p_mpbir i0_pwv p_vex i0_pwv a_sup_set_class a_cvv a_cpw a_wcel i0_pwv a_sup_set_class a_cvv a_wcel p_2th i0_pwv a_cvv a_cpw a_cvv p_eqriv $.
$}


