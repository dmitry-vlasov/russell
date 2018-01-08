$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Power_classes.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Unordered and ordered pairs

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Declare new symbols needed. */

$)
$c <.  $.
$( /* Bracket (the period distinguishes it from 'less than') */

$)
$c >.  $.
$( /* Bracket (the period distinguishes it from 'greater than') */

$)
$( /* Extend class notation to include singleton. */

$)
${
	fcsn_0 $f class A $.
	csn $a class { A } $.
$}
$( /* Extend class notation to include unordered pair. */

$)
${
	fcpr_0 $f class A $.
	fcpr_1 $f class B $.
	cpr $a class { A , B } $.
$}
$( /* Extend class notation to include unordered triplet. */

$)
${
	fctp_0 $f class A $.
	fctp_1 $f class B $.
	fctp_2 $f class C $.
	ctp $a class { A , B , C } $.
$}
$( /* Extend class notation to include ordered pair. */

$)
${
	fcop_0 $f class A $.
	fcop_1 $f class B $.
	cop $a class <. A , B >. $.
$}
$( /* Extend class notation to include ordered triple. */

$)
${
	fcotp_0 $f class A $.
	fcotp_1 $f class B $.
	fcotp_2 $f class C $.
	cotp $a class <. A , B , C >. $.
$}
$( /* Soundness justification theorem for ~ df-sn .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	$d x A $.
	$d y A $.
	$d z x $.
	$d z y $.
	$d z A $.
	isnjust_0 $f set z $.
	fsnjust_0 $f set x $.
	fsnjust_1 $f set y $.
	fsnjust_2 $f class A $.
	snjust $p |- { x | x = A } = { y | y = A } $= fsnjust_0 sup_set_class fsnjust_2 wceq fsnjust_0 cab isnjust_0 sup_set_class fsnjust_2 wceq isnjust_0 cab fsnjust_1 sup_set_class fsnjust_2 wceq fsnjust_1 cab fsnjust_0 sup_set_class fsnjust_2 wceq isnjust_0 sup_set_class fsnjust_2 wceq fsnjust_0 isnjust_0 fsnjust_0 sup_set_class isnjust_0 sup_set_class fsnjust_2 eqeq1 cbvabv isnjust_0 sup_set_class fsnjust_2 wceq fsnjust_1 sup_set_class fsnjust_2 wceq isnjust_0 fsnjust_1 isnjust_0 sup_set_class fsnjust_1 sup_set_class fsnjust_2 eqeq1 cbvabv eqtri $.
$}
$( /* Define the singleton of a class.  Definition 7.1 of [Quine] p. 48.  For
       convenience, it is well-defined for proper classes, i.e., those that are
       not elements of ` _V ` , although it is not very meaningful in this
       case.  For an alternate definition see ~ dfsn2 .  (Contributed by NM,
       5-Aug-1993.) */

$)
${
	$d x A $.
	fdf-sn_0 $f set x $.
	fdf-sn_1 $f class A $.
	df-sn $a |- { A } = { x | x = A } $.
$}
$( /* Define unordered pair of classes.  Definition 7.1 of [Quine] p. 48.  For
     example, ` A e. { 1 , -u 1 } -> ( A ^ 2 ) = 1 ` ( ~ ex-pr ).  They are
     unordered, so ` { A , B } = { B , A } ` as proven by ~ prcom .  For a more
     traditional definition, but requiring a dummy variable, see ~ dfpr2 .
     (Contributed by NM, 5-Aug-1993.) */

$)
${
	fdf-pr_0 $f class A $.
	fdf-pr_1 $f class B $.
	df-pr $a |- { A , B } = ( { A } u. { B } ) $.
$}
$( /* Define unordered triple of classes.  Definition of [Enderton] p. 19.
     (Contributed by NM, 9-Apr-1994.) */

$)
${
	fdf-tp_0 $f class A $.
	fdf-tp_1 $f class B $.
	fdf-tp_2 $f class C $.
	df-tp $a |- { A , B , C } = ( { A , B } u. { C } ) $.
$}
$( /* Definition of an ordered pair, equivalent to Kuratowski's definition
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
       28-May-1995.)  (Revised by Mario Carneiro, 26-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	fdf-op_0 $f set x $.
	fdf-op_1 $f class A $.
	fdf-op_2 $f class B $.
	df-op $a |- <. A , B >. = { x | ( A e. _V /\ B e. _V /\ x e. { { A } , { A , B } } ) } $.
$}
$( /* Define ordered triple of classes.  Definition of ordered triple in [Stoll]
     p. 25.  (Contributed by NM, 3-Apr-2015.) */

$)
${
	fdf-ot_0 $f class A $.
	fdf-ot_1 $f class B $.
	fdf-ot_2 $f class C $.
	df-ot $a |- <. A , B , C >. = <. <. A , B >. , C >. $.
$}
$( /* Equality theorem for singletons.  Part of Exercise 4 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	$d x B $.
	isneq_0 $f set x $.
	fsneq_0 $f class A $.
	fsneq_1 $f class B $.
	sneq $p |- ( A = B -> { A } = { B } ) $= fsneq_0 fsneq_1 wceq isneq_0 sup_set_class fsneq_0 wceq isneq_0 cab isneq_0 sup_set_class fsneq_1 wceq isneq_0 cab fsneq_0 csn fsneq_1 csn fsneq_0 fsneq_1 wceq isneq_0 sup_set_class fsneq_0 wceq isneq_0 sup_set_class fsneq_1 wceq isneq_0 fsneq_0 fsneq_1 isneq_0 sup_set_class eqeq2 abbidv isneq_0 fsneq_0 df-sn isneq_0 fsneq_1 df-sn 3eqtr4g $.
$}
$( /* Equality inference for singletons.  (Contributed by NM, 22-Jan-2004.) */

$)
${
	fsneqi_0 $f class A $.
	fsneqi_1 $f class B $.
	esneqi_0 $e |- A = B $.
	sneqi $p |- { A } = { B } $= fsneqi_0 fsneqi_1 wceq fsneqi_0 csn fsneqi_1 csn wceq esneqi_0 fsneqi_0 fsneqi_1 sneq ax-mp $.
$}
$( /* Equality deduction for singletons.  (Contributed by NM, 22-Jan-2004.) */

$)
${
	fsneqd_0 $f wff ph $.
	fsneqd_1 $f class A $.
	fsneqd_2 $f class B $.
	esneqd_0 $e |- ( ph -> A = B ) $.
	sneqd $p |- ( ph -> { A } = { B } ) $= fsneqd_0 fsneqd_1 fsneqd_2 wceq fsneqd_1 csn fsneqd_2 csn wceq esneqd_0 fsneqd_1 fsneqd_2 sneq syl $.
$}
$( /* Alternate definition of singleton.  Definition 5.1 of [TakeutiZaring]
     p. 15.  (Contributed by NM, 24-Apr-1994.) */

$)
${
	fdfsn2_0 $f class A $.
	dfsn2 $p |- { A } = { A , A } $= fdfsn2_0 fdfsn2_0 cpr fdfsn2_0 csn fdfsn2_0 csn cun fdfsn2_0 csn fdfsn2_0 fdfsn2_0 df-pr fdfsn2_0 csn unidm eqtr2i $.
$}
$( /* There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	felsn_0 $f set x $.
	felsn_1 $f class A $.
	elsn $p |- ( x e. { A } <-> x = A ) $= felsn_0 sup_set_class felsn_1 wceq felsn_0 felsn_1 csn felsn_0 felsn_1 df-sn abeq2i $.
$}
$( /* Alternate definition of unordered pair.  Definition 5.1 of
       [TakeutiZaring] p. 15.  (Contributed by NM, 24-Apr-1994.) */

$)
${
	$d x A $.
	$d x B $.
	fdfpr2_0 $f set x $.
	fdfpr2_1 $f class A $.
	fdfpr2_2 $f class B $.
	dfpr2 $p |- { A , B } = { x | ( x = A \/ x = B ) } $= fdfpr2_1 fdfpr2_2 cpr fdfpr2_1 csn fdfpr2_2 csn cun fdfpr2_0 sup_set_class fdfpr2_1 wceq fdfpr2_0 sup_set_class fdfpr2_2 wceq wo fdfpr2_0 cab fdfpr2_1 fdfpr2_2 df-pr fdfpr2_0 sup_set_class fdfpr2_1 wceq fdfpr2_0 sup_set_class fdfpr2_2 wceq wo fdfpr2_0 fdfpr2_1 csn fdfpr2_2 csn cun fdfpr2_0 sup_set_class fdfpr2_1 csn fdfpr2_2 csn cun wcel fdfpr2_0 sup_set_class fdfpr2_1 csn wcel fdfpr2_0 sup_set_class fdfpr2_2 csn wcel wo fdfpr2_0 sup_set_class fdfpr2_1 wceq fdfpr2_0 sup_set_class fdfpr2_2 wceq wo fdfpr2_0 sup_set_class fdfpr2_1 csn fdfpr2_2 csn elun fdfpr2_0 sup_set_class fdfpr2_1 csn wcel fdfpr2_0 sup_set_class fdfpr2_1 wceq fdfpr2_0 sup_set_class fdfpr2_2 csn wcel fdfpr2_0 sup_set_class fdfpr2_2 wceq fdfpr2_0 fdfpr2_1 elsn fdfpr2_0 fdfpr2_2 elsn orbi12i bitri abbi2i eqtri $.
$}
$( /* A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15, generalized.  (Contributed by NM,
       13-Sep-1995.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ielprg_0 $f set x $.
	felprg_0 $f class A $.
	felprg_1 $f class B $.
	felprg_2 $f class C $.
	felprg_3 $f class V $.
	elprg $p |- ( A e. V -> ( A e. { B , C } <-> ( A = B \/ A = C ) ) ) $= ielprg_0 sup_set_class felprg_1 wceq ielprg_0 sup_set_class felprg_2 wceq wo felprg_0 felprg_1 wceq felprg_0 felprg_2 wceq wo ielprg_0 felprg_0 felprg_1 felprg_2 cpr felprg_3 ielprg_0 sup_set_class felprg_0 wceq ielprg_0 sup_set_class felprg_1 wceq felprg_0 felprg_1 wceq ielprg_0 sup_set_class felprg_2 wceq felprg_0 felprg_2 wceq ielprg_0 sup_set_class felprg_0 felprg_1 eqeq1 ielprg_0 sup_set_class felprg_0 felprg_2 eqeq1 orbi12d ielprg_0 felprg_1 felprg_2 dfpr2 elab2g $.
$}
$( /* A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15.  (Contributed by NM,
       13-Sep-1995.) */

$)
${
	felpr_0 $f class A $.
	felpr_1 $f class B $.
	felpr_2 $f class C $.
	eelpr_0 $e |- A e. _V $.
	elpr $p |- ( A e. { B , C } <-> ( A = B \/ A = C ) ) $= felpr_0 cvv wcel felpr_0 felpr_1 felpr_2 cpr wcel felpr_0 felpr_1 wceq felpr_0 felpr_2 wceq wo wb eelpr_0 felpr_0 felpr_1 felpr_2 cvv elprg ax-mp $.
$}
$( /* A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15.  (Contributed by NM,
       14-Oct-2005.) */

$)
${
	felpr2_0 $f class A $.
	felpr2_1 $f class B $.
	felpr2_2 $f class C $.
	eelpr2_0 $e |- B e. _V $.
	eelpr2_1 $e |- C e. _V $.
	elpr2 $p |- ( A e. { B , C } <-> ( A = B \/ A = C ) ) $= felpr2_0 felpr2_1 felpr2_2 cpr wcel felpr2_0 felpr2_1 wceq felpr2_0 felpr2_2 wceq wo felpr2_0 felpr2_1 felpr2_2 cpr wcel felpr2_0 felpr2_1 wceq felpr2_0 felpr2_2 wceq wo felpr2_0 felpr2_1 felpr2_2 felpr2_1 felpr2_2 cpr elprg ibi felpr2_0 felpr2_1 wceq felpr2_0 felpr2_2 wceq wo felpr2_0 felpr2_1 felpr2_2 cpr wcel felpr2_0 felpr2_1 wceq felpr2_0 felpr2_2 wceq wo felpr2_0 cvv wcel felpr2_0 felpr2_1 felpr2_2 cpr wcel felpr2_0 felpr2_1 wceq felpr2_0 felpr2_2 wceq wo wb felpr2_0 felpr2_1 wceq felpr2_0 cvv wcel felpr2_0 felpr2_2 wceq felpr2_0 felpr2_1 wceq felpr2_0 cvv wcel felpr2_1 cvv wcel eelpr2_0 felpr2_0 felpr2_1 cvv eleq1 mpbiri felpr2_0 felpr2_2 wceq felpr2_0 cvv wcel felpr2_2 cvv wcel eelpr2_1 felpr2_0 felpr2_2 cvv eleq1 mpbiri jaoi felpr2_0 felpr2_1 felpr2_2 cvv elprg syl ibir impbii $.
$}
$( /* If a class is an element of a pair, then it is one of the two paired
     elements.  (Contributed by Scott Fenton, 1-Apr-2011.) */

$)
${
	felpri_0 $f class A $.
	felpri_1 $f class B $.
	felpri_2 $f class C $.
	elpri $p |- ( A e. { B , C } -> ( A = B \/ A = C ) ) $= felpri_0 felpri_1 felpri_2 cpr wcel felpri_0 felpri_1 wceq felpri_0 felpri_2 wceq wo felpri_0 felpri_1 felpri_2 felpri_1 felpri_2 cpr elprg ibi $.
$}
$( /* If an element doesn't match the items in an unordered pair, it is not in
       the unordered pair.  (Contributed by David A. Wheeler, 10-May-2015.) */

$)
${
	fnelpri_0 $f class A $.
	fnelpri_1 $f class B $.
	fnelpri_2 $f class C $.
	enelpri_0 $e |- A =/= B $.
	enelpri_1 $e |- A =/= C $.
	nelpri $p |- -. A e. { B , C } $= fnelpri_0 fnelpri_1 wne fnelpri_0 fnelpri_2 wne fnelpri_0 fnelpri_1 fnelpri_2 cpr wcel wn enelpri_0 enelpri_1 fnelpri_0 fnelpri_1 wne fnelpri_0 fnelpri_2 wne wa fnelpri_0 fnelpri_1 wceq fnelpri_0 fnelpri_2 wceq wo wn fnelpri_0 fnelpri_1 fnelpri_2 cpr wcel wn fnelpri_0 fnelpri_1 fnelpri_0 fnelpri_2 neanior fnelpri_0 fnelpri_1 fnelpri_2 cpr wcel fnelpri_0 fnelpri_1 wceq fnelpri_0 fnelpri_2 wceq wo fnelpri_0 fnelpri_1 fnelpri_2 elpri con3i sylbi mp2an $.
$}
$( /* There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15 (generalized).  (Contributed by NM, 13-Sep-1995.)  (Proof
       shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	$d A x $.
	$d B x $.
	ielsncg_0 $f set x $.
	felsncg_0 $f class A $.
	felsncg_1 $f class B $.
	felsncg_2 $f class V $.
	elsncg $p |- ( A e. V -> ( A e. { B } <-> A = B ) ) $= ielsncg_0 sup_set_class felsncg_1 wceq felsncg_0 felsncg_1 wceq ielsncg_0 felsncg_0 felsncg_1 csn felsncg_2 ielsncg_0 sup_set_class felsncg_0 felsncg_1 eqeq1 ielsncg_0 felsncg_1 df-sn elab2g $.
$}
$( /* There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 13-Sep-1995.) */

$)
${
	felsnc_0 $f class A $.
	felsnc_1 $f class B $.
	eelsnc_0 $e |- A e. _V $.
	elsnc $p |- ( A e. { B } <-> A = B ) $= felsnc_0 cvv wcel felsnc_0 felsnc_1 csn wcel felsnc_0 felsnc_1 wceq wb eelsnc_0 felsnc_0 felsnc_1 cvv elsncg ax-mp $.
$}
$( /* There is only one element in a singleton.  (Contributed by NM,
     5-Jun-1994.) */

$)
${
	felsni_0 $f class A $.
	felsni_1 $f class B $.
	elsni $p |- ( A e. { B } -> A = B ) $= felsni_0 felsni_1 csn wcel felsni_0 felsni_1 wceq felsni_0 felsni_1 felsni_1 csn elsncg ibi $.
$}
$( /* A set is a member of its singleton.  Part of Theorem 7.6 of [Quine]
     p. 49.  (Contributed by NM, 28-Oct-2003.) */

$)
${
	fsnidg_0 $f class A $.
	fsnidg_1 $f class V $.
	snidg $p |- ( A e. V -> A e. { A } ) $= fsnidg_0 fsnidg_1 wcel fsnidg_0 fsnidg_0 csn wcel fsnidg_0 fsnidg_0 wceq fsnidg_0 eqid fsnidg_0 fsnidg_0 fsnidg_1 elsncg mpbiri $.
$}
$( /* A class is a set iff it is a member of its singleton.  (Contributed by NM,
     5-Apr-2004.) */

$)
${
	fsnidb_0 $f class A $.
	snidb $p |- ( A e. _V <-> A e. { A } ) $= fsnidb_0 cvv wcel fsnidb_0 fsnidb_0 csn wcel fsnidb_0 cvv snidg fsnidb_0 fsnidb_0 csn elex impbii $.
$}
$( /* A set is a member of its singleton.  Part of Theorem 7.6 of [Quine]
       p. 49.  (Contributed by NM, 31-Dec-1993.) */

$)
${
	fsnid_0 $f class A $.
	esnid_0 $e |- A e. _V $.
	snid $p |- A e. { A } $= fsnid_0 cvv wcel fsnid_0 fsnid_0 csn wcel esnid_0 fsnid_0 snidb mpbi $.
$}
$( /* There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
     p. 15.  This variation requires only that ` B ` , rather than ` A ` , be a
     set.  (Contributed by NM, 28-Oct-2003.) */

$)
${
	felsnc2g_0 $f class A $.
	felsnc2g_1 $f class B $.
	felsnc2g_2 $f class V $.
	elsnc2g $p |- ( B e. V -> ( A e. { B } <-> A = B ) ) $= felsnc2g_1 felsnc2g_2 wcel felsnc2g_0 felsnc2g_1 csn wcel felsnc2g_0 felsnc2g_1 wceq felsnc2g_0 felsnc2g_1 elsni felsnc2g_1 felsnc2g_2 wcel felsnc2g_0 felsnc2g_1 csn wcel felsnc2g_0 felsnc2g_1 wceq felsnc2g_1 felsnc2g_1 csn wcel felsnc2g_1 felsnc2g_2 snidg felsnc2g_0 felsnc2g_1 felsnc2g_1 csn eleq1 syl5ibrcom impbid2 $.
$}
$( /* There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  This variation requires only that ` B ` , rather than ` A ` , be
       a set.  (Contributed by NM, 12-Jun-1994.) */

$)
${
	felsnc2_0 $f class A $.
	felsnc2_1 $f class B $.
	eelsnc2_0 $e |- B e. _V $.
	elsnc2 $p |- ( A e. { B } <-> A = B ) $= felsnc2_1 cvv wcel felsnc2_0 felsnc2_1 csn wcel felsnc2_0 felsnc2_1 wceq wb eelsnc2_0 felsnc2_0 felsnc2_1 cvv elsnc2g ax-mp $.
$}
$( /* Substitution expressed in terms of quantification over a singleton.
       (Contributed by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d A x $.
	fralsns_0 $f wff ph $.
	fralsns_1 $f set x $.
	fralsns_2 $f class A $.
	fralsns_3 $f class V $.
	ralsns $p |- ( A e. V -> ( A. x e. { A } ph <-> [. A / x ]. ph ) ) $= fralsns_2 fralsns_3 wcel fralsns_0 fralsns_1 fralsns_2 wsbc fralsns_1 sup_set_class fralsns_2 wceq fralsns_0 wi fralsns_1 wal fralsns_0 fralsns_1 fralsns_2 csn wral fralsns_0 fralsns_1 fralsns_2 fralsns_3 sbc6g fralsns_0 fralsns_1 fralsns_2 csn wral fralsns_1 sup_set_class fralsns_2 csn wcel fralsns_0 wi fralsns_1 wal fralsns_1 sup_set_class fralsns_2 wceq fralsns_0 wi fralsns_1 wal fralsns_0 fralsns_1 fralsns_2 csn df-ral fralsns_1 sup_set_class fralsns_2 csn wcel fralsns_0 wi fralsns_1 sup_set_class fralsns_2 wceq fralsns_0 wi fralsns_1 fralsns_1 sup_set_class fralsns_2 csn wcel fralsns_1 sup_set_class fralsns_2 wceq fralsns_0 fralsns_1 fralsns_2 elsn imbi1i albii bitri syl6rbbr $.
$}
$( /* Restricted existential quantification over a singleton.  (Contributed by
       Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d A x $.
	frexsns_0 $f wff ph $.
	frexsns_1 $f set x $.
	frexsns_2 $f class A $.
	frexsns_3 $f class V $.
	rexsns $p |- ( A e. V -> ( E. x e. { A } ph <-> [. A / x ]. ph ) ) $= frexsns_2 frexsns_3 wcel frexsns_0 frexsns_1 frexsns_2 wsbc frexsns_1 sup_set_class frexsns_2 wceq frexsns_0 wa frexsns_1 wex frexsns_0 frexsns_1 frexsns_2 csn wrex frexsns_0 frexsns_1 frexsns_2 wsbc frexsns_1 sup_set_class frexsns_2 wceq frexsns_0 wa frexsns_1 wex wb frexsns_2 frexsns_3 wcel frexsns_0 frexsns_1 frexsns_2 sbc5 a1i frexsns_0 frexsns_1 frexsns_2 csn wrex frexsns_1 sup_set_class frexsns_2 csn wcel frexsns_0 wa frexsns_1 wex frexsns_1 sup_set_class frexsns_2 wceq frexsns_0 wa frexsns_1 wex frexsns_0 frexsns_1 frexsns_2 csn df-rex frexsns_1 sup_set_class frexsns_2 csn wcel frexsns_0 wa frexsns_1 sup_set_class frexsns_2 wceq frexsns_0 wa frexsns_1 frexsns_1 sup_set_class frexsns_2 csn wcel frexsns_1 sup_set_class frexsns_2 wceq frexsns_0 frexsns_1 frexsns_2 elsn anbi1i exbii bitri syl6rbbr $.
$}
$( /* Substitution expressed in terms of quantification over a singleton.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       23-Apr-2015.) */

$)
${
	$d A x $.
	$d ps x $.
	fralsng_0 $f wff ph $.
	fralsng_1 $f wff ps $.
	fralsng_2 $f set x $.
	fralsng_3 $f class A $.
	fralsng_4 $f class V $.
	eralsng_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ralsng $p |- ( A e. V -> ( A. x e. { A } ph <-> ps ) ) $= fralsng_3 fralsng_4 wcel fralsng_0 fralsng_2 fralsng_3 csn wral fralsng_0 fralsng_2 fralsng_3 wsbc fralsng_1 fralsng_0 fralsng_2 fralsng_3 fralsng_4 ralsns fralsng_0 fralsng_1 fralsng_2 fralsng_3 fralsng_4 eralsng_0 sbcieg bitrd $.
$}
$( /* Restricted existential quantification over a singleton.  (Contributed by
       NM, 29-Jan-2012.) */

$)
${
	$d A x $.
	$d ps x $.
	frexsng_0 $f wff ph $.
	frexsng_1 $f wff ps $.
	frexsng_2 $f set x $.
	frexsng_3 $f class A $.
	frexsng_4 $f class V $.
	erexsng_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rexsng $p |- ( A e. V -> ( E. x e. { A } ph <-> ps ) ) $= frexsng_3 frexsng_4 wcel frexsng_0 frexsng_2 frexsng_3 csn wrex frexsng_0 frexsng_2 frexsng_3 wsbc frexsng_1 frexsng_0 frexsng_2 frexsng_3 frexsng_4 rexsns frexsng_0 frexsng_1 frexsng_2 frexsng_3 frexsng_4 erexsng_0 sbcieg bitrd $.
$}
$( /* Convert a quantification over a singleton to a substitution.
       (Contributed by NM, 27-Apr-2009.) */

$)
${
	$d A x $.
	$d ps x $.
	fralsn_0 $f wff ph $.
	fralsn_1 $f wff ps $.
	fralsn_2 $f set x $.
	fralsn_3 $f class A $.
	eralsn_0 $e |- A e. _V $.
	eralsn_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	ralsn $p |- ( A. x e. { A } ph <-> ps ) $= fralsn_3 cvv wcel fralsn_0 fralsn_2 fralsn_3 csn wral fralsn_1 wb eralsn_0 fralsn_0 fralsn_1 fralsn_2 fralsn_3 cvv eralsn_1 ralsng ax-mp $.
$}
$( /* Restricted existential quantification over a singleton.  (Contributed by
       Jeff Madsen, 5-Jan-2011.) */

$)
${
	$d A x $.
	$d ps x $.
	frexsn_0 $f wff ph $.
	frexsn_1 $f wff ps $.
	frexsn_2 $f set x $.
	frexsn_3 $f class A $.
	erexsn_0 $e |- A e. _V $.
	erexsn_1 $e |- ( x = A -> ( ph <-> ps ) ) $.
	rexsn $p |- ( E. x e. { A } ph <-> ps ) $= frexsn_3 cvv wcel frexsn_0 frexsn_2 frexsn_3 csn wrex frexsn_1 wb erexsn_0 frexsn_0 frexsn_1 frexsn_2 frexsn_3 cvv erexsn_1 rexsng ax-mp $.
$}
$( /* Members of an unordered triple of classes.  (Contributed by FL,
       2-Feb-2014.)  (Proof shortened by Mario Carneiro, 11-Feb-2015.) */

$)
${
	feltpg_0 $f class A $.
	feltpg_1 $f class B $.
	feltpg_2 $f class C $.
	feltpg_3 $f class D $.
	feltpg_4 $f class V $.
	eltpg $p |- ( A e. V -> ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) ) ) $= feltpg_0 feltpg_4 wcel feltpg_0 feltpg_1 feltpg_2 cpr wcel feltpg_0 feltpg_3 csn wcel wo feltpg_0 feltpg_1 wceq feltpg_0 feltpg_2 wceq wo feltpg_0 feltpg_3 wceq wo feltpg_0 feltpg_1 feltpg_2 feltpg_3 ctp wcel feltpg_0 feltpg_1 wceq feltpg_0 feltpg_2 wceq feltpg_0 feltpg_3 wceq w3o feltpg_0 feltpg_4 wcel feltpg_0 feltpg_1 feltpg_2 cpr wcel feltpg_0 feltpg_1 wceq feltpg_0 feltpg_2 wceq wo feltpg_0 feltpg_3 csn wcel feltpg_0 feltpg_3 wceq feltpg_0 feltpg_1 feltpg_2 feltpg_4 elprg feltpg_0 feltpg_3 feltpg_4 elsncg orbi12d feltpg_0 feltpg_1 feltpg_2 feltpg_3 ctp wcel feltpg_0 feltpg_1 feltpg_2 cpr feltpg_3 csn cun wcel feltpg_0 feltpg_1 feltpg_2 cpr wcel feltpg_0 feltpg_3 csn wcel wo feltpg_1 feltpg_2 feltpg_3 ctp feltpg_1 feltpg_2 cpr feltpg_3 csn cun feltpg_0 feltpg_1 feltpg_2 feltpg_3 df-tp eleq2i feltpg_0 feltpg_1 feltpg_2 cpr feltpg_3 csn elun bitri feltpg_0 feltpg_1 wceq feltpg_0 feltpg_2 wceq feltpg_0 feltpg_3 wceq df-3or 3bitr4g $.
$}
$( /* A member of an unordered triple of classes is one of them.  (Contributed
       by Mario Carneiro, 11-Feb-2015.) */

$)
${
	feltpi_0 $f class A $.
	feltpi_1 $f class B $.
	feltpi_2 $f class C $.
	feltpi_3 $f class D $.
	eltpi $p |- ( A e. { B , C , D } -> ( A = B \/ A = C \/ A = D ) ) $= feltpi_0 feltpi_1 feltpi_2 feltpi_3 ctp wcel feltpi_0 feltpi_1 wceq feltpi_0 feltpi_2 wceq feltpi_0 feltpi_3 wceq w3o feltpi_0 feltpi_1 feltpi_2 feltpi_3 feltpi_1 feltpi_2 feltpi_3 ctp eltpg ibi $.
$}
$( /* A member of an unordered triple of classes is one of them.  Special case
       of Exercise 1 of [TakeutiZaring] p. 17.  (Contributed by NM,
       8-Apr-1994.)  (Revised by Mario Carneiro, 11-Feb-2015.) */

$)
${
	feltp_0 $f class A $.
	feltp_1 $f class B $.
	feltp_2 $f class C $.
	feltp_3 $f class D $.
	eeltp_0 $e |- A e. _V $.
	eltp $p |- ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) ) $= feltp_0 cvv wcel feltp_0 feltp_1 feltp_2 feltp_3 ctp wcel feltp_0 feltp_1 wceq feltp_0 feltp_2 wceq feltp_0 feltp_3 wceq w3o wb eeltp_0 feltp_0 feltp_1 feltp_2 feltp_3 cvv eltpg ax-mp $.
$}
$( /* Alternate definition of unordered triple of classes.  Special case of
       Definition 5.3 of [TakeutiZaring] p. 16.  (Contributed by NM,
       8-Apr-1994.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	fdftp2_0 $f set x $.
	fdftp2_1 $f class A $.
	fdftp2_2 $f class B $.
	fdftp2_3 $f class C $.
	dftp2 $p |- { A , B , C } = { x | ( x = A \/ x = B \/ x = C ) } $= fdftp2_0 sup_set_class fdftp2_1 wceq fdftp2_0 sup_set_class fdftp2_2 wceq fdftp2_0 sup_set_class fdftp2_3 wceq w3o fdftp2_0 fdftp2_1 fdftp2_2 fdftp2_3 ctp fdftp2_0 sup_set_class fdftp2_1 fdftp2_2 fdftp2_3 fdftp2_0 vex eltp abbi2i $.
$}
$( /* Bound-variable hypothesis builder for unordered pairs.  (Contributed by
       NM, 14-Nov-1995.) */

$)
${
	$d y A $.
	$d y B $.
	$d x y $.
	infpr_0 $f set y $.
	fnfpr_0 $f set x $.
	fnfpr_1 $f class A $.
	fnfpr_2 $f class B $.
	enfpr_0 $e |- F/_ x A $.
	enfpr_1 $e |- F/_ x B $.
	nfpr $p |- F/_ x { A , B } $= fnfpr_0 fnfpr_1 fnfpr_2 cpr infpr_0 sup_set_class fnfpr_1 wceq infpr_0 sup_set_class fnfpr_2 wceq wo infpr_0 cab infpr_0 fnfpr_1 fnfpr_2 dfpr2 infpr_0 sup_set_class fnfpr_1 wceq infpr_0 sup_set_class fnfpr_2 wceq wo fnfpr_0 infpr_0 infpr_0 sup_set_class fnfpr_1 wceq infpr_0 sup_set_class fnfpr_2 wceq fnfpr_0 fnfpr_0 infpr_0 sup_set_class fnfpr_1 enfpr_0 nfeq2 fnfpr_0 infpr_0 sup_set_class fnfpr_2 enfpr_1 nfeq2 nfor nfab nfcxfr $.
$}
$( /* Membership of a conditional operator in an unordered pair.  (Contributed
     by NM, 17-Jun-2007.) */

$)
${
	fifpr_0 $f wff ph $.
	fifpr_1 $f class A $.
	fifpr_2 $f class B $.
	fifpr_3 $f class C $.
	fifpr_4 $f class D $.
	ifpr $p |- ( ( A e. C /\ B e. D ) -> if ( ph , A , B ) e. { A , B } ) $= fifpr_1 fifpr_3 wcel fifpr_1 cvv wcel fifpr_2 cvv wcel fifpr_0 fifpr_1 fifpr_2 cif fifpr_1 fifpr_2 cpr wcel fifpr_2 fifpr_4 wcel fifpr_1 fifpr_3 elex fifpr_2 fifpr_4 elex fifpr_1 cvv wcel fifpr_2 cvv wcel wa fifpr_0 fifpr_1 fifpr_2 cif cvv wcel fifpr_0 fifpr_1 fifpr_2 cif fifpr_1 fifpr_2 cpr wcel fifpr_0 fifpr_1 fifpr_2 cvv ifcl fifpr_0 fifpr_1 fifpr_2 cif cvv wcel fifpr_0 fifpr_1 fifpr_2 cif fifpr_1 fifpr_2 cpr wcel fifpr_0 fifpr_1 fifpr_2 cif fifpr_1 wceq fifpr_0 fifpr_1 fifpr_2 cif fifpr_2 wceq wo fifpr_0 fifpr_1 fifpr_2 ifeqor fifpr_0 fifpr_1 fifpr_2 cif fifpr_1 fifpr_2 cvv elprg mpbiri syl syl2an $.
$}
$( /* Convert a quantification over a pair to a conjunction.  (Contributed by
       NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	$d x ch $.
	fralprg_0 $f wff ph $.
	fralprg_1 $f wff ps $.
	fralprg_2 $f wff ch $.
	fralprg_3 $f set x $.
	fralprg_4 $f class A $.
	fralprg_5 $f class B $.
	fralprg_6 $f class V $.
	fralprg_7 $f class W $.
	eralprg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eralprg_1 $e |- ( x = B -> ( ph <-> ch ) ) $.
	ralprg $p |- ( ( A e. V /\ B e. W ) -> ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) ) $= fralprg_0 fralprg_3 fralprg_4 fralprg_5 cpr wral fralprg_0 fralprg_3 fralprg_4 csn wral fralprg_0 fralprg_3 fralprg_5 csn wral wa fralprg_4 fralprg_6 wcel fralprg_5 fralprg_7 wcel wa fralprg_1 fralprg_2 wa fralprg_0 fralprg_3 fralprg_4 fralprg_5 cpr wral fralprg_0 fralprg_3 fralprg_4 csn fralprg_5 csn cun wral fralprg_0 fralprg_3 fralprg_4 csn wral fralprg_0 fralprg_3 fralprg_5 csn wral wa fralprg_0 fralprg_3 fralprg_4 fralprg_5 cpr fralprg_4 csn fralprg_5 csn cun fralprg_4 fralprg_5 df-pr raleqi fralprg_0 fralprg_3 fralprg_4 csn fralprg_5 csn ralunb bitri fralprg_4 fralprg_6 wcel fralprg_0 fralprg_3 fralprg_4 csn wral fralprg_1 fralprg_5 fralprg_7 wcel fralprg_0 fralprg_3 fralprg_5 csn wral fralprg_2 fralprg_0 fralprg_1 fralprg_3 fralprg_4 fralprg_6 eralprg_0 ralsng fralprg_0 fralprg_2 fralprg_3 fralprg_5 fralprg_7 eralprg_1 ralsng bi2anan9 syl5bb $.
$}
$( /* Convert a quantification over a pair to a disjunction.  (Contributed by
       NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	$d x ch $.
	frexprg_0 $f wff ph $.
	frexprg_1 $f wff ps $.
	frexprg_2 $f wff ch $.
	frexprg_3 $f set x $.
	frexprg_4 $f class A $.
	frexprg_5 $f class B $.
	frexprg_6 $f class V $.
	frexprg_7 $f class W $.
	erexprg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	erexprg_1 $e |- ( x = B -> ( ph <-> ch ) ) $.
	rexprg $p |- ( ( A e. V /\ B e. W ) -> ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) ) $= frexprg_0 frexprg_3 frexprg_4 frexprg_5 cpr wrex frexprg_0 frexprg_3 frexprg_4 csn wrex frexprg_0 frexprg_3 frexprg_5 csn wrex wo frexprg_4 frexprg_6 wcel frexprg_5 frexprg_7 wcel wa frexprg_1 frexprg_2 wo frexprg_0 frexprg_3 frexprg_4 frexprg_5 cpr wrex frexprg_0 frexprg_3 frexprg_4 csn frexprg_5 csn cun wrex frexprg_0 frexprg_3 frexprg_4 csn wrex frexprg_0 frexprg_3 frexprg_5 csn wrex wo frexprg_0 frexprg_3 frexprg_4 frexprg_5 cpr frexprg_4 csn frexprg_5 csn cun frexprg_4 frexprg_5 df-pr rexeqi frexprg_0 frexprg_3 frexprg_4 csn frexprg_5 csn rexun bitri frexprg_4 frexprg_6 wcel frexprg_0 frexprg_3 frexprg_4 csn wrex frexprg_0 frexprg_3 frexprg_5 csn wrex wo frexprg_1 frexprg_0 frexprg_3 frexprg_5 csn wrex wo frexprg_5 frexprg_7 wcel frexprg_1 frexprg_2 wo frexprg_4 frexprg_6 wcel frexprg_0 frexprg_3 frexprg_4 csn wrex frexprg_1 frexprg_0 frexprg_3 frexprg_5 csn wrex frexprg_0 frexprg_1 frexprg_3 frexprg_4 frexprg_6 erexprg_0 rexsng orbi1d frexprg_5 frexprg_7 wcel frexprg_0 frexprg_3 frexprg_5 csn wrex frexprg_2 frexprg_1 frexprg_0 frexprg_2 frexprg_3 frexprg_5 frexprg_7 erexprg_1 rexsng orbi2d sylan9bb syl5bb $.
$}
$( /* Convert a quantification over a triple to a conjunction.  (Contributed
       by NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	fraltpg_0 $f wff ph $.
	fraltpg_1 $f wff ps $.
	fraltpg_2 $f wff ch $.
	fraltpg_3 $f wff th $.
	fraltpg_4 $f set x $.
	fraltpg_5 $f class A $.
	fraltpg_6 $f class B $.
	fraltpg_7 $f class C $.
	fraltpg_8 $f class V $.
	fraltpg_9 $f class W $.
	fraltpg_10 $f class X $.
	eraltpg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eraltpg_1 $e |- ( x = B -> ( ph <-> ch ) ) $.
	eraltpg_2 $e |- ( x = C -> ( ph <-> th ) ) $.
	raltpg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) ) $= fraltpg_5 fraltpg_8 wcel fraltpg_6 fraltpg_9 wcel fraltpg_7 fraltpg_10 wcel w3a fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 cpr wral fraltpg_0 fraltpg_4 fraltpg_7 csn wral wa fraltpg_1 fraltpg_2 wa fraltpg_3 wa fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 fraltpg_7 ctp wral fraltpg_1 fraltpg_2 fraltpg_3 w3a fraltpg_5 fraltpg_8 wcel fraltpg_6 fraltpg_9 wcel fraltpg_7 fraltpg_10 wcel fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 cpr wral fraltpg_0 fraltpg_4 fraltpg_7 csn wral wa fraltpg_1 fraltpg_2 wa fraltpg_3 wa wb fraltpg_5 fraltpg_8 wcel fraltpg_6 fraltpg_9 wcel wa fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 cpr wral fraltpg_1 fraltpg_2 wa fraltpg_7 fraltpg_10 wcel fraltpg_0 fraltpg_4 fraltpg_7 csn wral fraltpg_3 fraltpg_0 fraltpg_1 fraltpg_2 fraltpg_4 fraltpg_5 fraltpg_6 fraltpg_8 fraltpg_9 eraltpg_0 eraltpg_1 ralprg fraltpg_0 fraltpg_3 fraltpg_4 fraltpg_7 fraltpg_10 eraltpg_2 ralsng bi2anan9 3impa fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 fraltpg_7 ctp wral fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 cpr fraltpg_7 csn cun wral fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 cpr wral fraltpg_0 fraltpg_4 fraltpg_7 csn wral wa fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 fraltpg_7 ctp fraltpg_5 fraltpg_6 cpr fraltpg_7 csn cun fraltpg_5 fraltpg_6 fraltpg_7 df-tp raleqi fraltpg_0 fraltpg_4 fraltpg_5 fraltpg_6 cpr fraltpg_7 csn ralunb bitri fraltpg_1 fraltpg_2 fraltpg_3 df-3an 3bitr4g $.
$}
$( /* Convert a quantification over a triple to a disjunction.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	frextpg_0 $f wff ph $.
	frextpg_1 $f wff ps $.
	frextpg_2 $f wff ch $.
	frextpg_3 $f wff th $.
	frextpg_4 $f set x $.
	frextpg_5 $f class A $.
	frextpg_6 $f class B $.
	frextpg_7 $f class C $.
	frextpg_8 $f class V $.
	frextpg_9 $f class W $.
	frextpg_10 $f class X $.
	erextpg_0 $e |- ( x = A -> ( ph <-> ps ) ) $.
	erextpg_1 $e |- ( x = B -> ( ph <-> ch ) ) $.
	erextpg_2 $e |- ( x = C -> ( ph <-> th ) ) $.
	rextpg $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) ) $= frextpg_5 frextpg_8 wcel frextpg_6 frextpg_9 wcel frextpg_7 frextpg_10 wcel w3a frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr wrex frextpg_0 frextpg_4 frextpg_7 csn wrex wo frextpg_1 frextpg_2 wo frextpg_3 wo frextpg_0 frextpg_4 frextpg_5 frextpg_6 frextpg_7 ctp wrex frextpg_1 frextpg_2 frextpg_3 w3o frextpg_5 frextpg_8 wcel frextpg_6 frextpg_9 wcel frextpg_7 frextpg_10 wcel frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr wrex frextpg_0 frextpg_4 frextpg_7 csn wrex wo frextpg_1 frextpg_2 wo frextpg_3 wo wb frextpg_5 frextpg_8 wcel frextpg_6 frextpg_9 wcel wa frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr wrex frextpg_0 frextpg_4 frextpg_7 csn wrex wo frextpg_1 frextpg_2 wo frextpg_0 frextpg_4 frextpg_7 csn wrex wo frextpg_7 frextpg_10 wcel frextpg_1 frextpg_2 wo frextpg_3 wo frextpg_5 frextpg_8 wcel frextpg_6 frextpg_9 wcel wa frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr wrex frextpg_1 frextpg_2 wo frextpg_0 frextpg_4 frextpg_7 csn wrex frextpg_0 frextpg_1 frextpg_2 frextpg_4 frextpg_5 frextpg_6 frextpg_8 frextpg_9 erextpg_0 erextpg_1 rexprg orbi1d frextpg_7 frextpg_10 wcel frextpg_0 frextpg_4 frextpg_7 csn wrex frextpg_3 frextpg_1 frextpg_2 wo frextpg_0 frextpg_3 frextpg_4 frextpg_7 frextpg_10 erextpg_2 rexsng orbi2d sylan9bb 3impa frextpg_0 frextpg_4 frextpg_5 frextpg_6 frextpg_7 ctp wrex frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr frextpg_7 csn cun wrex frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr wrex frextpg_0 frextpg_4 frextpg_7 csn wrex wo frextpg_0 frextpg_4 frextpg_5 frextpg_6 frextpg_7 ctp frextpg_5 frextpg_6 cpr frextpg_7 csn cun frextpg_5 frextpg_6 frextpg_7 df-tp rexeqi frextpg_0 frextpg_4 frextpg_5 frextpg_6 cpr frextpg_7 csn rexun bitri frextpg_1 frextpg_2 frextpg_3 df-3or 3bitr4g $.
$}
$( /* Convert a quantification over a pair to a conjunction.  (Contributed by
       NM, 3-Jun-2007.)  (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	$d x ch $.
	fralpr_0 $f wff ph $.
	fralpr_1 $f wff ps $.
	fralpr_2 $f wff ch $.
	fralpr_3 $f set x $.
	fralpr_4 $f class A $.
	fralpr_5 $f class B $.
	eralpr_0 $e |- A e. _V $.
	eralpr_1 $e |- B e. _V $.
	eralpr_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eralpr_3 $e |- ( x = B -> ( ph <-> ch ) ) $.
	ralpr $p |- ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) $= fralpr_4 cvv wcel fralpr_5 cvv wcel fralpr_0 fralpr_3 fralpr_4 fralpr_5 cpr wral fralpr_1 fralpr_2 wa wb eralpr_0 eralpr_1 fralpr_0 fralpr_1 fralpr_2 fralpr_3 fralpr_4 fralpr_5 cvv cvv eralpr_2 eralpr_3 ralprg mp2an $.
$}
$( /* Convert an existential quantification over a pair to a disjunction.
       (Contributed by NM, 3-Jun-2007.)  (Revised by Mario Carneiro,
       23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	$d x ch $.
	frexpr_0 $f wff ph $.
	frexpr_1 $f wff ps $.
	frexpr_2 $f wff ch $.
	frexpr_3 $f set x $.
	frexpr_4 $f class A $.
	frexpr_5 $f class B $.
	erexpr_0 $e |- A e. _V $.
	erexpr_1 $e |- B e. _V $.
	erexpr_2 $e |- ( x = A -> ( ph <-> ps ) ) $.
	erexpr_3 $e |- ( x = B -> ( ph <-> ch ) ) $.
	rexpr $p |- ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) $= frexpr_4 cvv wcel frexpr_5 cvv wcel frexpr_0 frexpr_3 frexpr_4 frexpr_5 cpr wrex frexpr_1 frexpr_2 wo wb erexpr_0 erexpr_1 frexpr_0 frexpr_1 frexpr_2 frexpr_3 frexpr_4 frexpr_5 cvv cvv erexpr_2 erexpr_3 rexprg mp2an $.
$}
$( /* Convert a quantification over a triple to a conjunction.  (Contributed
       by NM, 13-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	fraltp_0 $f wff ph $.
	fraltp_1 $f wff ps $.
	fraltp_2 $f wff ch $.
	fraltp_3 $f wff th $.
	fraltp_4 $f set x $.
	fraltp_5 $f class A $.
	fraltp_6 $f class B $.
	fraltp_7 $f class C $.
	eraltp_0 $e |- A e. _V $.
	eraltp_1 $e |- B e. _V $.
	eraltp_2 $e |- C e. _V $.
	eraltp_3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	eraltp_4 $e |- ( x = B -> ( ph <-> ch ) ) $.
	eraltp_5 $e |- ( x = C -> ( ph <-> th ) ) $.
	raltp $p |- ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) $= fraltp_5 cvv wcel fraltp_6 cvv wcel fraltp_7 cvv wcel fraltp_0 fraltp_4 fraltp_5 fraltp_6 fraltp_7 ctp wral fraltp_1 fraltp_2 fraltp_3 w3a wb eraltp_0 eraltp_1 eraltp_2 fraltp_0 fraltp_1 fraltp_2 fraltp_3 fraltp_4 fraltp_5 fraltp_6 fraltp_7 cvv cvv cvv eraltp_3 eraltp_4 eraltp_5 raltpg mp3an $.
$}
$( /* Convert a quantification over a triple to a disjunction.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x ps $.
	$d x ch $.
	$d x th $.
	frextp_0 $f wff ph $.
	frextp_1 $f wff ps $.
	frextp_2 $f wff ch $.
	frextp_3 $f wff th $.
	frextp_4 $f set x $.
	frextp_5 $f class A $.
	frextp_6 $f class B $.
	frextp_7 $f class C $.
	erextp_0 $e |- A e. _V $.
	erextp_1 $e |- B e. _V $.
	erextp_2 $e |- C e. _V $.
	erextp_3 $e |- ( x = A -> ( ph <-> ps ) ) $.
	erextp_4 $e |- ( x = B -> ( ph <-> ch ) ) $.
	erextp_5 $e |- ( x = C -> ( ph <-> th ) ) $.
	rextp $p |- ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) $= frextp_5 cvv wcel frextp_6 cvv wcel frextp_7 cvv wcel frextp_0 frextp_4 frextp_5 frextp_6 frextp_7 ctp wrex frextp_1 frextp_2 frextp_3 w3o wb erextp_0 erextp_1 erextp_2 frextp_0 frextp_1 frextp_2 frextp_3 frextp_4 frextp_5 frextp_6 frextp_7 cvv cvv cvv erextp_3 erextp_4 erextp_5 rextpg mp3an $.
$}
$( /* TODO - make obsolete; use ralsnsSBC instead - also,
       shorten posn w/ ralsn or ralsng */

$)
$( /* Substitution expressed in terms of quantification over a singleton.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       23-Apr-2015.) */

$)
${
	$d x A $.
	fsbcsng_0 $f wff ph $.
	fsbcsng_1 $f set x $.
	fsbcsng_2 $f class A $.
	fsbcsng_3 $f class V $.
	sbcsng $p |- ( A e. V -> ( [. A / x ]. ph <-> A. x e. { A } ph ) ) $= fsbcsng_2 fsbcsng_3 wcel fsbcsng_0 fsbcsng_1 fsbcsng_2 csn wral fsbcsng_0 fsbcsng_1 fsbcsng_2 wsbc fsbcsng_0 fsbcsng_1 fsbcsng_2 fsbcsng_3 ralsns bicomd $.
$}
$( /* Bound-variable hypothesis builder for singletons.  (Contributed by NM,
       14-Nov-1995.) */

$)
${
	fnfsn_0 $f set x $.
	fnfsn_1 $f class A $.
	enfsn_0 $e |- F/_ x A $.
	nfsn $p |- F/_ x { A } $= fnfsn_0 fnfsn_1 csn fnfsn_1 fnfsn_1 cpr fnfsn_1 dfsn2 fnfsn_0 fnfsn_1 fnfsn_1 enfsn_0 enfsn_0 nfpr nfcxfr $.
$}
$( /* Distribute proper substitution through the singleton of a class.
       ~ csbsng is derived from the virtual deduction proof ~ csbsngVD .
       (Contributed by Alan Sare, 10-Nov-2012.) */

$)
${
	$d A y $.
	$d B y $.
	$d V y $.
	$d x y $.
	icsbsng_0 $f set y $.
	fcsbsng_0 $f set x $.
	fcsbsng_1 $f class A $.
	fcsbsng_2 $f class B $.
	fcsbsng_3 $f class V $.
	csbsng $p |- ( A e. V -> [_ A / x ]_ { B } = { [_ A / x ]_ B } ) $= fcsbsng_1 fcsbsng_3 wcel fcsbsng_0 fcsbsng_1 icsbsng_0 sup_set_class fcsbsng_2 wceq icsbsng_0 cab csb icsbsng_0 sup_set_class fcsbsng_0 fcsbsng_1 fcsbsng_2 csb wceq icsbsng_0 cab fcsbsng_0 fcsbsng_1 fcsbsng_2 csn csb fcsbsng_0 fcsbsng_1 fcsbsng_2 csb csn fcsbsng_1 fcsbsng_3 wcel fcsbsng_0 fcsbsng_1 icsbsng_0 sup_set_class fcsbsng_2 wceq icsbsng_0 cab csb icsbsng_0 sup_set_class fcsbsng_2 wceq fcsbsng_0 fcsbsng_1 wsbc icsbsng_0 cab icsbsng_0 sup_set_class fcsbsng_0 fcsbsng_1 fcsbsng_2 csb wceq icsbsng_0 cab icsbsng_0 sup_set_class fcsbsng_2 wceq fcsbsng_0 icsbsng_0 fcsbsng_1 fcsbsng_3 csbabg fcsbsng_1 fcsbsng_3 wcel icsbsng_0 sup_set_class fcsbsng_2 wceq fcsbsng_0 fcsbsng_1 wsbc icsbsng_0 sup_set_class fcsbsng_0 fcsbsng_1 fcsbsng_2 csb wceq icsbsng_0 fcsbsng_0 fcsbsng_1 icsbsng_0 sup_set_class fcsbsng_2 fcsbsng_3 sbceq2g abbidv eqtrd fcsbsng_0 fcsbsng_1 fcsbsng_2 csn icsbsng_0 sup_set_class fcsbsng_2 wceq icsbsng_0 cab icsbsng_0 fcsbsng_2 df-sn csbeq2i icsbsng_0 fcsbsng_0 fcsbsng_1 fcsbsng_2 csb df-sn 3eqtr4g $.
$}
$( /* Intersection with the singleton of a non-member is disjoint.
       (Contributed by NM, 22-May-1998.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.)  (Proof shortened by Wolf Lammen, 30-Sep-2014.) */

$)
${
	$d x A $.
	$d x B $.
	idisjsn_0 $f set x $.
	fdisjsn_0 $f class A $.
	fdisjsn_1 $f class B $.
	disjsn $p |- ( ( A i^i { B } ) = (/) <-> -. B e. A ) $= fdisjsn_0 fdisjsn_1 csn cin c0 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel idisjsn_0 sup_set_class fdisjsn_1 csn wcel wn wi idisjsn_0 wal idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wa wn idisjsn_0 wal fdisjsn_1 fdisjsn_0 wcel wn idisjsn_0 fdisjsn_0 fdisjsn_1 csn disj1 idisjsn_0 sup_set_class fdisjsn_0 wcel idisjsn_0 sup_set_class fdisjsn_1 csn wcel wn wi idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wa wn idisjsn_0 idisjsn_0 sup_set_class fdisjsn_0 wcel idisjsn_0 sup_set_class fdisjsn_1 csn wcel wn wi idisjsn_0 sup_set_class fdisjsn_1 csn wcel idisjsn_0 sup_set_class fdisjsn_0 wcel wn wi idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wn wi idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wa wn idisjsn_0 sup_set_class fdisjsn_0 wcel idisjsn_0 sup_set_class fdisjsn_1 csn wcel con2b idisjsn_0 sup_set_class fdisjsn_1 csn wcel idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wn idisjsn_0 fdisjsn_1 elsn imbi1i idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel imnan 3bitri albii idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wa wn idisjsn_0 wal idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wa idisjsn_0 wex fdisjsn_1 fdisjsn_0 wcel idisjsn_0 sup_set_class fdisjsn_1 wceq idisjsn_0 sup_set_class fdisjsn_0 wcel wa idisjsn_0 alnex idisjsn_0 fdisjsn_1 fdisjsn_0 df-clel xchbinxr 3bitri $.
$}
$( /* Intersection of distinct singletons is disjoint.  (Contributed by NM,
     25-May-1998.) */

$)
${
	fdisjsn2_0 $f class A $.
	fdisjsn2_1 $f class B $.
	disjsn2 $p |- ( A =/= B -> ( { A } i^i { B } ) = (/) ) $= fdisjsn2_0 fdisjsn2_1 wne fdisjsn2_1 fdisjsn2_0 csn wcel wn fdisjsn2_0 csn fdisjsn2_1 csn cin c0 wceq fdisjsn2_1 fdisjsn2_0 csn wcel fdisjsn2_0 fdisjsn2_1 fdisjsn2_1 fdisjsn2_0 csn wcel fdisjsn2_1 fdisjsn2_0 fdisjsn2_1 fdisjsn2_0 elsni eqcomd necon3ai fdisjsn2_0 csn fdisjsn2_1 disjsn sylibr $.
$}
$( /* The singleton of a proper class (one that doesn't exist) is the empty
       set.  Theorem 7.2 of [Quine] p. 48.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	isnprc_0 $f set x $.
	fsnprc_0 $f class A $.
	snprc $p |- ( -. A e. _V <-> { A } = (/) ) $= fsnprc_0 csn c0 wceq fsnprc_0 cvv wcel isnprc_0 sup_set_class fsnprc_0 csn wcel isnprc_0 wex isnprc_0 sup_set_class fsnprc_0 wceq isnprc_0 wex fsnprc_0 csn c0 wceq wn fsnprc_0 cvv wcel isnprc_0 sup_set_class fsnprc_0 csn wcel isnprc_0 sup_set_class fsnprc_0 wceq isnprc_0 isnprc_0 fsnprc_0 elsn exbii isnprc_0 fsnprc_0 csn neq0 isnprc_0 fsnprc_0 isset 3bitr4i con1bii $.
$}
$( /* Special case of ~ r19.12 where its converse holds.  (Contributed by NM,
       19-May-2008.)  (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d x y A $.
	$d x B $.
	fr19.12sn_0 $f wff ph $.
	fr19.12sn_1 $f set x $.
	fr19.12sn_2 $f set y $.
	fr19.12sn_3 $f class A $.
	fr19.12sn_4 $f class B $.
	er19.12sn_0 $e |- A e. _V $.
	r19.12sn $p |- ( E. x e. { A } A. y e. B ph <-> A. y e. B E. x e. { A } ph ) $= fr19.12sn_3 cvv wcel fr19.12sn_0 fr19.12sn_2 fr19.12sn_4 wral fr19.12sn_1 fr19.12sn_3 csn wrex fr19.12sn_0 fr19.12sn_1 fr19.12sn_3 csn wrex fr19.12sn_2 fr19.12sn_4 wral wb er19.12sn_0 fr19.12sn_3 cvv wcel fr19.12sn_0 fr19.12sn_2 fr19.12sn_4 wral fr19.12sn_1 fr19.12sn_3 wsbc fr19.12sn_0 fr19.12sn_1 fr19.12sn_3 wsbc fr19.12sn_2 fr19.12sn_4 wral fr19.12sn_0 fr19.12sn_2 fr19.12sn_4 wral fr19.12sn_1 fr19.12sn_3 csn wrex fr19.12sn_0 fr19.12sn_1 fr19.12sn_3 csn wrex fr19.12sn_2 fr19.12sn_4 wral fr19.12sn_0 fr19.12sn_1 fr19.12sn_2 fr19.12sn_3 fr19.12sn_4 cvv sbcralg fr19.12sn_0 fr19.12sn_2 fr19.12sn_4 wral fr19.12sn_1 fr19.12sn_3 cvv rexsns fr19.12sn_3 cvv wcel fr19.12sn_0 fr19.12sn_1 fr19.12sn_3 csn wrex fr19.12sn_0 fr19.12sn_1 fr19.12sn_3 wsbc fr19.12sn_2 fr19.12sn_4 fr19.12sn_0 fr19.12sn_1 fr19.12sn_3 cvv rexsns ralbidv 3bitr4d ax-mp $.
$}
$( /* Condition where a restricted class abstraction is a singleton.
       (Contributed by NM, 28-May-2006.) */

$)
${
	$d x A $.
	$d x B $.
	frabsn_0 $f set x $.
	frabsn_1 $f class A $.
	frabsn_2 $f class B $.
	rabsn $p |- ( B e. A -> { x e. A | x = B } = { B } ) $= frabsn_2 frabsn_1 wcel frabsn_0 sup_set_class frabsn_1 wcel frabsn_0 sup_set_class frabsn_2 wceq wa frabsn_0 cab frabsn_0 sup_set_class frabsn_2 wceq frabsn_0 cab frabsn_0 sup_set_class frabsn_2 wceq frabsn_0 frabsn_1 crab frabsn_2 csn frabsn_2 frabsn_1 wcel frabsn_0 sup_set_class frabsn_1 wcel frabsn_0 sup_set_class frabsn_2 wceq wa frabsn_0 sup_set_class frabsn_2 wceq frabsn_0 frabsn_0 sup_set_class frabsn_1 wcel frabsn_0 sup_set_class frabsn_2 wceq wa frabsn_2 frabsn_1 wcel frabsn_0 sup_set_class frabsn_2 wceq frabsn_0 sup_set_class frabsn_2 wceq frabsn_0 sup_set_class frabsn_1 wcel frabsn_2 frabsn_1 wcel frabsn_0 sup_set_class frabsn_2 frabsn_1 eleq1 pm5.32ri baib abbidv frabsn_0 sup_set_class frabsn_2 wceq frabsn_0 frabsn_1 df-rab frabsn_0 frabsn_2 df-sn 3eqtr4g $.
$}
$( /* Another way to express existential uniqueness of a wff: its class
       abstraction is a singleton.  (Contributed by Mario Carneiro,
       14-Nov-2016.) */

$)
${
	$d x y $.
	$d y ph $.
	feuabsn2_0 $f wff ph $.
	feuabsn2_1 $f set x $.
	feuabsn2_2 $f set y $.
	euabsn2 $p |- ( E! x ph <-> E. y { x | ph } = { y } ) $= feuabsn2_0 feuabsn2_1 weu feuabsn2_0 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class wceq wb feuabsn2_1 wal feuabsn2_2 wex feuabsn2_0 feuabsn2_1 cab feuabsn2_2 sup_set_class csn wceq feuabsn2_2 wex feuabsn2_0 feuabsn2_1 feuabsn2_2 df-eu feuabsn2_0 feuabsn2_1 cab feuabsn2_2 sup_set_class csn wceq feuabsn2_0 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class wceq wb feuabsn2_1 wal feuabsn2_2 feuabsn2_0 feuabsn2_1 cab feuabsn2_2 sup_set_class csn wceq feuabsn2_0 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class csn wcel wb feuabsn2_1 wal feuabsn2_0 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class wceq wb feuabsn2_1 wal feuabsn2_0 feuabsn2_1 feuabsn2_2 sup_set_class csn abeq1 feuabsn2_0 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class csn wcel wb feuabsn2_0 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class wceq wb feuabsn2_1 feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class csn wcel feuabsn2_1 sup_set_class feuabsn2_2 sup_set_class wceq feuabsn2_0 feuabsn2_1 feuabsn2_2 sup_set_class elsn bibi2i albii bitri exbii bitr4i $.
$}
$( /* Another way to express existential uniqueness of a wff: its class
       abstraction is a singleton.  (Contributed by NM, 22-Feb-2004.) */

$)
${
	$d x y $.
	$d y ph $.
	ieuabsn_0 $f set y $.
	feuabsn_0 $f wff ph $.
	feuabsn_1 $f set x $.
	euabsn $p |- ( E! x ph <-> E. x { x | ph } = { x } ) $= feuabsn_0 feuabsn_1 weu feuabsn_0 feuabsn_1 cab ieuabsn_0 sup_set_class csn wceq ieuabsn_0 wex feuabsn_0 feuabsn_1 cab feuabsn_1 sup_set_class csn wceq feuabsn_1 wex feuabsn_0 feuabsn_1 ieuabsn_0 euabsn2 feuabsn_0 feuabsn_1 cab feuabsn_1 sup_set_class csn wceq feuabsn_0 feuabsn_1 cab ieuabsn_0 sup_set_class csn wceq feuabsn_1 ieuabsn_0 feuabsn_0 feuabsn_1 cab feuabsn_1 sup_set_class csn wceq ieuabsn_0 nfv feuabsn_1 feuabsn_0 feuabsn_1 cab ieuabsn_0 sup_set_class csn feuabsn_0 feuabsn_1 nfab1 nfeq1 feuabsn_1 sup_set_class ieuabsn_0 sup_set_class wceq feuabsn_1 sup_set_class csn ieuabsn_0 sup_set_class csn feuabsn_0 feuabsn_1 cab feuabsn_1 sup_set_class ieuabsn_0 sup_set_class sneq eqeq2d cbvex bitr4i $.
$}
$( /* A way to express restricted existential uniqueness of a wff: its
       restricted class abstraction is a singleton.  (Contributed by NM,
       30-May-2006.)  (Proof shortened by Mario Carneiro, 14-Nov-2016.) */

$)
${
	$d x y $.
	$d y ph $.
	$d y A $.
	freusn_0 $f wff ph $.
	freusn_1 $f set x $.
	freusn_2 $f set y $.
	freusn_3 $f class A $.
	reusn $p |- ( E! x e. A ph <-> E. y { x e. A | ph } = { y } ) $= freusn_1 sup_set_class freusn_3 wcel freusn_0 wa freusn_1 weu freusn_1 sup_set_class freusn_3 wcel freusn_0 wa freusn_1 cab freusn_2 sup_set_class csn wceq freusn_2 wex freusn_0 freusn_1 freusn_3 wreu freusn_0 freusn_1 freusn_3 crab freusn_2 sup_set_class csn wceq freusn_2 wex freusn_1 sup_set_class freusn_3 wcel freusn_0 wa freusn_1 freusn_2 euabsn2 freusn_0 freusn_1 freusn_3 df-reu freusn_0 freusn_1 freusn_3 crab freusn_2 sup_set_class csn wceq freusn_1 sup_set_class freusn_3 wcel freusn_0 wa freusn_1 cab freusn_2 sup_set_class csn wceq freusn_2 freusn_0 freusn_1 freusn_3 crab freusn_1 sup_set_class freusn_3 wcel freusn_0 wa freusn_1 cab freusn_2 sup_set_class csn freusn_0 freusn_1 freusn_3 df-rab eqeq1i exbii 3bitr4i $.
$}
$( /* Restricted existential uniqueness determined by a singleton.
       (Contributed by NM, 29-May-2006.) */

$)
${
	$d x y $.
	$d y ph $.
	$d y A $.
	iabsneu_0 $f set y $.
	fabsneu_0 $f wff ph $.
	fabsneu_1 $f set x $.
	fabsneu_2 $f class A $.
	fabsneu_3 $f class V $.
	absneu $p |- ( ( A e. V /\ { x | ph } = { A } ) -> E! x ph ) $= fabsneu_2 fabsneu_3 wcel fabsneu_0 fabsneu_1 cab fabsneu_2 csn wceq wa fabsneu_0 fabsneu_1 cab iabsneu_0 sup_set_class csn wceq iabsneu_0 wex fabsneu_0 fabsneu_1 weu fabsneu_2 fabsneu_3 wcel fabsneu_0 fabsneu_1 cab fabsneu_2 csn wceq fabsneu_0 fabsneu_1 cab iabsneu_0 sup_set_class csn wceq iabsneu_0 wex fabsneu_0 fabsneu_1 cab iabsneu_0 sup_set_class csn wceq fabsneu_0 fabsneu_1 cab fabsneu_2 csn wceq iabsneu_0 fabsneu_2 fabsneu_3 iabsneu_0 sup_set_class fabsneu_2 wceq iabsneu_0 sup_set_class csn fabsneu_2 csn fabsneu_0 fabsneu_1 cab iabsneu_0 sup_set_class fabsneu_2 sneq eqeq2d spcegv imp fabsneu_0 fabsneu_1 iabsneu_0 euabsn2 sylibr $.
$}
$( /* Restricted existential uniqueness determined by a singleton.
       (Contributed by NM, 29-May-2006.)  (Revised by Mario Carneiro,
       23-Dec-2016.) */

$)
${
	frabsneu_0 $f wff ph $.
	frabsneu_1 $f set x $.
	frabsneu_2 $f class A $.
	frabsneu_3 $f class B $.
	frabsneu_4 $f class V $.
	rabsneu $p |- ( ( A e. V /\ { x e. B | ph } = { A } ) -> E! x e. B ph ) $= frabsneu_2 frabsneu_4 wcel frabsneu_0 frabsneu_1 frabsneu_3 crab frabsneu_2 csn wceq wa frabsneu_1 sup_set_class frabsneu_3 wcel frabsneu_0 wa frabsneu_1 weu frabsneu_0 frabsneu_1 frabsneu_3 wreu frabsneu_0 frabsneu_1 frabsneu_3 crab frabsneu_2 csn wceq frabsneu_2 frabsneu_4 wcel frabsneu_1 sup_set_class frabsneu_3 wcel frabsneu_0 wa frabsneu_1 cab frabsneu_2 csn wceq frabsneu_1 sup_set_class frabsneu_3 wcel frabsneu_0 wa frabsneu_1 weu frabsneu_0 frabsneu_1 frabsneu_3 crab frabsneu_1 sup_set_class frabsneu_3 wcel frabsneu_0 wa frabsneu_1 cab frabsneu_2 csn frabsneu_0 frabsneu_1 frabsneu_3 df-rab eqeq1i frabsneu_1 sup_set_class frabsneu_3 wcel frabsneu_0 wa frabsneu_1 frabsneu_2 frabsneu_4 absneu sylan2b frabsneu_0 frabsneu_1 frabsneu_3 df-reu sylibr $.
$}
$( /* Two ways to express " ` A ` is a singleton."  (Contributed by NM,
       30-Oct-2010.) */

$)
${
	$d x A $.
	feusn_0 $f set x $.
	feusn_1 $f class A $.
	eusn $p |- ( E! x x e. A <-> E. x A = { x } ) $= feusn_0 sup_set_class feusn_1 wcel feusn_0 weu feusn_0 sup_set_class feusn_1 wcel feusn_0 cab feusn_0 sup_set_class csn wceq feusn_0 wex feusn_1 feusn_0 sup_set_class csn wceq feusn_0 wex feusn_0 sup_set_class feusn_1 wcel feusn_0 euabsn feusn_0 sup_set_class feusn_1 wcel feusn_0 cab feusn_0 sup_set_class csn wceq feusn_1 feusn_0 sup_set_class csn wceq feusn_0 feusn_0 sup_set_class feusn_1 wcel feusn_0 cab feusn_1 feusn_0 sup_set_class csn feusn_0 feusn_1 abid2 eqeq1i exbii bitri $.
$}
$( /* Truth implied by equality of a restricted class abstraction and a
       singleton.  (Contributed by NM, 29-May-2006.)  (Proof shortened by Mario
       Carneiro, 23-Dec-2016.) */

$)
${
	$d x A $.
	$d x B $.
	$d x ps $.
	frabsnt_0 $f wff ph $.
	frabsnt_1 $f wff ps $.
	frabsnt_2 $f set x $.
	frabsnt_3 $f class A $.
	frabsnt_4 $f class B $.
	erabsnt_0 $e |- B e. _V $.
	erabsnt_1 $e |- ( x = B -> ( ph <-> ps ) ) $.
	rabsnt $p |- ( { x e. A | ph } = { B } -> ps ) $= frabsnt_0 frabsnt_2 frabsnt_3 crab frabsnt_4 csn wceq frabsnt_4 frabsnt_0 frabsnt_2 frabsnt_3 crab wcel frabsnt_1 frabsnt_0 frabsnt_2 frabsnt_3 crab frabsnt_4 csn wceq frabsnt_4 frabsnt_4 csn frabsnt_0 frabsnt_2 frabsnt_3 crab frabsnt_4 erabsnt_0 snid frabsnt_0 frabsnt_2 frabsnt_3 crab frabsnt_4 csn wceq id syl5eleqr frabsnt_4 frabsnt_0 frabsnt_2 frabsnt_3 crab wcel frabsnt_4 frabsnt_3 wcel frabsnt_1 frabsnt_0 frabsnt_1 frabsnt_2 frabsnt_4 frabsnt_3 erabsnt_1 elrab simprbi syl $.
$}
$( /* Commutative law for unordered pairs.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fprcom_0 $f class A $.
	fprcom_1 $f class B $.
	prcom $p |- { A , B } = { B , A } $= fprcom_0 csn fprcom_1 csn cun fprcom_1 csn fprcom_0 csn cun fprcom_0 fprcom_1 cpr fprcom_1 fprcom_0 cpr fprcom_0 csn fprcom_1 csn uncom fprcom_0 fprcom_1 df-pr fprcom_1 fprcom_0 df-pr 3eqtr4i $.
$}
$( /* Equality theorem for unordered pairs.  (Contributed by NM,
     29-Mar-1998.) */

$)
${
	fpreq1_0 $f class A $.
	fpreq1_1 $f class B $.
	fpreq1_2 $f class C $.
	preq1 $p |- ( A = B -> { A , C } = { B , C } ) $= fpreq1_0 fpreq1_1 wceq fpreq1_0 csn fpreq1_2 csn cun fpreq1_1 csn fpreq1_2 csn cun fpreq1_0 fpreq1_2 cpr fpreq1_1 fpreq1_2 cpr fpreq1_0 fpreq1_1 wceq fpreq1_0 csn fpreq1_1 csn fpreq1_2 csn fpreq1_0 fpreq1_1 sneq uneq1d fpreq1_0 fpreq1_2 df-pr fpreq1_1 fpreq1_2 df-pr 3eqtr4g $.
$}
$( /* Equality theorem for unordered pairs.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fpreq2_0 $f class A $.
	fpreq2_1 $f class B $.
	fpreq2_2 $f class C $.
	preq2 $p |- ( A = B -> { C , A } = { C , B } ) $= fpreq2_0 fpreq2_1 wceq fpreq2_0 fpreq2_2 cpr fpreq2_1 fpreq2_2 cpr fpreq2_2 fpreq2_0 cpr fpreq2_2 fpreq2_1 cpr fpreq2_0 fpreq2_1 fpreq2_2 preq1 fpreq2_2 fpreq2_0 prcom fpreq2_2 fpreq2_1 prcom 3eqtr4g $.
$}
$( /* Equality theorem for unordered pairs.  (Contributed by NM,
     19-Oct-2012.) */

$)
${
	fpreq12_0 $f class A $.
	fpreq12_1 $f class B $.
	fpreq12_2 $f class C $.
	fpreq12_3 $f class D $.
	preq12 $p |- ( ( A = C /\ B = D ) -> { A , B } = { C , D } ) $= fpreq12_0 fpreq12_2 wceq fpreq12_1 fpreq12_3 wceq fpreq12_0 fpreq12_1 cpr fpreq12_2 fpreq12_1 cpr fpreq12_2 fpreq12_3 cpr fpreq12_0 fpreq12_2 fpreq12_1 preq1 fpreq12_1 fpreq12_3 fpreq12_2 preq2 sylan9eq $.
$}
$( /* Equality inference for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) */

$)
${
	fpreq1i_0 $f class A $.
	fpreq1i_1 $f class B $.
	fpreq1i_2 $f class C $.
	epreq1i_0 $e |- A = B $.
	preq1i $p |- { A , C } = { B , C } $= fpreq1i_0 fpreq1i_1 wceq fpreq1i_0 fpreq1i_2 cpr fpreq1i_1 fpreq1i_2 cpr wceq epreq1i_0 fpreq1i_0 fpreq1i_1 fpreq1i_2 preq1 ax-mp $.
$}
$( /* Equality inference for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) */

$)
${
	fpreq2i_0 $f class A $.
	fpreq2i_1 $f class B $.
	fpreq2i_2 $f class C $.
	epreq2i_0 $e |- A = B $.
	preq2i $p |- { C , A } = { C , B } $= fpreq2i_0 fpreq2i_1 wceq fpreq2i_2 fpreq2i_0 cpr fpreq2i_2 fpreq2i_1 cpr wceq epreq2i_0 fpreq2i_0 fpreq2i_1 fpreq2i_2 preq2 ax-mp $.
$}
$( /* Equality inference for unordered pairs.  (Contributed by NM,
         19-Oct-2012.) */

$)
${
	fpreq12i_0 $f class A $.
	fpreq12i_1 $f class B $.
	fpreq12i_2 $f class C $.
	fpreq12i_3 $f class D $.
	epreq12i_0 $e |- A = B $.
	epreq12i_1 $e |- C = D $.
	preq12i $p |- { A , C } = { B , D } $= fpreq12i_0 fpreq12i_1 wceq fpreq12i_2 fpreq12i_3 wceq fpreq12i_0 fpreq12i_2 cpr fpreq12i_1 fpreq12i_3 cpr wceq epreq12i_0 epreq12i_1 fpreq12i_0 fpreq12i_2 fpreq12i_1 fpreq12i_3 preq12 mp2an $.
$}
$( /* Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) */

$)
${
	fpreq1d_0 $f wff ph $.
	fpreq1d_1 $f class A $.
	fpreq1d_2 $f class B $.
	fpreq1d_3 $f class C $.
	epreq1d_0 $e |- ( ph -> A = B ) $.
	preq1d $p |- ( ph -> { A , C } = { B , C } ) $= fpreq1d_0 fpreq1d_1 fpreq1d_2 wceq fpreq1d_1 fpreq1d_3 cpr fpreq1d_2 fpreq1d_3 cpr wceq epreq1d_0 fpreq1d_1 fpreq1d_2 fpreq1d_3 preq1 syl $.
$}
$( /* Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) */

$)
${
	fpreq2d_0 $f wff ph $.
	fpreq2d_1 $f class A $.
	fpreq2d_2 $f class B $.
	fpreq2d_3 $f class C $.
	epreq2d_0 $e |- ( ph -> A = B ) $.
	preq2d $p |- ( ph -> { C , A } = { C , B } ) $= fpreq2d_0 fpreq2d_1 fpreq2d_2 wceq fpreq2d_3 fpreq2d_1 cpr fpreq2d_3 fpreq2d_2 cpr wceq epreq2d_0 fpreq2d_1 fpreq2d_2 fpreq2d_3 preq2 syl $.
$}
$( /* Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) */

$)
${
	fpreq12d_0 $f wff ph $.
	fpreq12d_1 $f class A $.
	fpreq12d_2 $f class B $.
	fpreq12d_3 $f class C $.
	fpreq12d_4 $f class D $.
	epreq12d_0 $e |- ( ph -> A = B ) $.
	epreq12d_1 $e |- ( ph -> C = D ) $.
	preq12d $p |- ( ph -> { A , C } = { B , D } ) $= fpreq12d_0 fpreq12d_1 fpreq12d_2 wceq fpreq12d_3 fpreq12d_4 wceq fpreq12d_1 fpreq12d_3 cpr fpreq12d_2 fpreq12d_4 cpr wceq epreq12d_0 epreq12d_1 fpreq12d_1 fpreq12d_3 fpreq12d_2 fpreq12d_4 preq12 syl2anc $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) */

$)
${
	ftpeq1_0 $f class A $.
	ftpeq1_1 $f class B $.
	ftpeq1_2 $f class C $.
	ftpeq1_3 $f class D $.
	tpeq1 $p |- ( A = B -> { A , C , D } = { B , C , D } ) $= ftpeq1_0 ftpeq1_1 wceq ftpeq1_0 ftpeq1_2 cpr ftpeq1_3 csn cun ftpeq1_1 ftpeq1_2 cpr ftpeq1_3 csn cun ftpeq1_0 ftpeq1_2 ftpeq1_3 ctp ftpeq1_1 ftpeq1_2 ftpeq1_3 ctp ftpeq1_0 ftpeq1_1 wceq ftpeq1_0 ftpeq1_2 cpr ftpeq1_1 ftpeq1_2 cpr ftpeq1_3 csn ftpeq1_0 ftpeq1_1 ftpeq1_2 preq1 uneq1d ftpeq1_0 ftpeq1_2 ftpeq1_3 df-tp ftpeq1_1 ftpeq1_2 ftpeq1_3 df-tp 3eqtr4g $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) */

$)
${
	ftpeq2_0 $f class A $.
	ftpeq2_1 $f class B $.
	ftpeq2_2 $f class C $.
	ftpeq2_3 $f class D $.
	tpeq2 $p |- ( A = B -> { C , A , D } = { C , B , D } ) $= ftpeq2_0 ftpeq2_1 wceq ftpeq2_2 ftpeq2_0 cpr ftpeq2_3 csn cun ftpeq2_2 ftpeq2_1 cpr ftpeq2_3 csn cun ftpeq2_2 ftpeq2_0 ftpeq2_3 ctp ftpeq2_2 ftpeq2_1 ftpeq2_3 ctp ftpeq2_0 ftpeq2_1 wceq ftpeq2_2 ftpeq2_0 cpr ftpeq2_2 ftpeq2_1 cpr ftpeq2_3 csn ftpeq2_0 ftpeq2_1 ftpeq2_2 preq2 uneq1d ftpeq2_2 ftpeq2_0 ftpeq2_3 df-tp ftpeq2_2 ftpeq2_1 ftpeq2_3 df-tp 3eqtr4g $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) */

$)
${
	ftpeq3_0 $f class A $.
	ftpeq3_1 $f class B $.
	ftpeq3_2 $f class C $.
	ftpeq3_3 $f class D $.
	tpeq3 $p |- ( A = B -> { C , D , A } = { C , D , B } ) $= ftpeq3_0 ftpeq3_1 wceq ftpeq3_2 ftpeq3_3 cpr ftpeq3_0 csn cun ftpeq3_2 ftpeq3_3 cpr ftpeq3_1 csn cun ftpeq3_2 ftpeq3_3 ftpeq3_0 ctp ftpeq3_2 ftpeq3_3 ftpeq3_1 ctp ftpeq3_0 ftpeq3_1 wceq ftpeq3_0 csn ftpeq3_1 csn ftpeq3_2 ftpeq3_3 cpr ftpeq3_0 ftpeq3_1 sneq uneq2d ftpeq3_2 ftpeq3_3 ftpeq3_0 df-tp ftpeq3_2 ftpeq3_3 ftpeq3_1 df-tp 3eqtr4g $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) */

$)
${
	ftpeq1d_0 $f wff ph $.
	ftpeq1d_1 $f class A $.
	ftpeq1d_2 $f class B $.
	ftpeq1d_3 $f class C $.
	ftpeq1d_4 $f class D $.
	etpeq1d_0 $e |- ( ph -> A = B ) $.
	tpeq1d $p |- ( ph -> { A , C , D } = { B , C , D } ) $= ftpeq1d_0 ftpeq1d_1 ftpeq1d_2 wceq ftpeq1d_1 ftpeq1d_3 ftpeq1d_4 ctp ftpeq1d_2 ftpeq1d_3 ftpeq1d_4 ctp wceq etpeq1d_0 ftpeq1d_1 ftpeq1d_2 ftpeq1d_3 ftpeq1d_4 tpeq1 syl $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) */

$)
${
	ftpeq2d_0 $f wff ph $.
	ftpeq2d_1 $f class A $.
	ftpeq2d_2 $f class B $.
	ftpeq2d_3 $f class C $.
	ftpeq2d_4 $f class D $.
	etpeq2d_0 $e |- ( ph -> A = B ) $.
	tpeq2d $p |- ( ph -> { C , A , D } = { C , B , D } ) $= ftpeq2d_0 ftpeq2d_1 ftpeq2d_2 wceq ftpeq2d_3 ftpeq2d_1 ftpeq2d_4 ctp ftpeq2d_3 ftpeq2d_2 ftpeq2d_4 ctp wceq etpeq2d_0 ftpeq2d_1 ftpeq2d_2 ftpeq2d_3 ftpeq2d_4 tpeq2 syl $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) */

$)
${
	ftpeq3d_0 $f wff ph $.
	ftpeq3d_1 $f class A $.
	ftpeq3d_2 $f class B $.
	ftpeq3d_3 $f class C $.
	ftpeq3d_4 $f class D $.
	etpeq3d_0 $e |- ( ph -> A = B ) $.
	tpeq3d $p |- ( ph -> { C , D , A } = { C , D , B } ) $= ftpeq3d_0 ftpeq3d_1 ftpeq3d_2 wceq ftpeq3d_3 ftpeq3d_4 ftpeq3d_1 ctp ftpeq3d_3 ftpeq3d_4 ftpeq3d_2 ctp wceq etpeq3d_0 ftpeq3d_1 ftpeq3d_2 ftpeq3d_3 ftpeq3d_4 tpeq3 syl $.
$}
$( /* Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) */

$)
${
	ftpeq123d_0 $f wff ph $.
	ftpeq123d_1 $f class A $.
	ftpeq123d_2 $f class B $.
	ftpeq123d_3 $f class C $.
	ftpeq123d_4 $f class D $.
	ftpeq123d_5 $f class E $.
	ftpeq123d_6 $f class F $.
	etpeq123d_0 $e |- ( ph -> A = B ) $.
	etpeq123d_1 $e |- ( ph -> C = D ) $.
	etpeq123d_2 $e |- ( ph -> E = F ) $.
	tpeq123d $p |- ( ph -> { A , C , E } = { B , D , F } ) $= ftpeq123d_0 ftpeq123d_1 ftpeq123d_3 ftpeq123d_5 ctp ftpeq123d_2 ftpeq123d_3 ftpeq123d_5 ctp ftpeq123d_2 ftpeq123d_4 ftpeq123d_5 ctp ftpeq123d_2 ftpeq123d_4 ftpeq123d_6 ctp ftpeq123d_0 ftpeq123d_1 ftpeq123d_2 ftpeq123d_3 ftpeq123d_5 etpeq123d_0 tpeq1d ftpeq123d_0 ftpeq123d_3 ftpeq123d_4 ftpeq123d_2 ftpeq123d_5 etpeq123d_1 tpeq2d ftpeq123d_0 ftpeq123d_5 ftpeq123d_6 ftpeq123d_2 ftpeq123d_4 etpeq123d_2 tpeq3d 3eqtrd $.
$}
$( /* Rotation of the elements of an unordered triple.  (Contributed by Alan
       Sare, 24-Oct-2011.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	itprot_0 $f set x $.
	ftprot_0 $f class A $.
	ftprot_1 $f class B $.
	ftprot_2 $f class C $.
	tprot $p |- { A , B , C } = { B , C , A } $= itprot_0 sup_set_class ftprot_0 wceq itprot_0 sup_set_class ftprot_1 wceq itprot_0 sup_set_class ftprot_2 wceq w3o itprot_0 cab itprot_0 sup_set_class ftprot_1 wceq itprot_0 sup_set_class ftprot_2 wceq itprot_0 sup_set_class ftprot_0 wceq w3o itprot_0 cab ftprot_0 ftprot_1 ftprot_2 ctp ftprot_1 ftprot_2 ftprot_0 ctp itprot_0 sup_set_class ftprot_0 wceq itprot_0 sup_set_class ftprot_1 wceq itprot_0 sup_set_class ftprot_2 wceq w3o itprot_0 sup_set_class ftprot_1 wceq itprot_0 sup_set_class ftprot_2 wceq itprot_0 sup_set_class ftprot_0 wceq w3o itprot_0 itprot_0 sup_set_class ftprot_0 wceq itprot_0 sup_set_class ftprot_1 wceq itprot_0 sup_set_class ftprot_2 wceq 3orrot abbii itprot_0 ftprot_0 ftprot_1 ftprot_2 dftp2 itprot_0 ftprot_1 ftprot_2 ftprot_0 dftp2 3eqtr4i $.
$}
$( /* Swap 1st and 2nd members of an undordered triple.  (Contributed by NM,
     22-May-2015.) */

$)
${
	ftpcoma_0 $f class A $.
	ftpcoma_1 $f class B $.
	ftpcoma_2 $f class C $.
	tpcoma $p |- { A , B , C } = { B , A , C } $= ftpcoma_0 ftpcoma_1 cpr ftpcoma_2 csn cun ftpcoma_1 ftpcoma_0 cpr ftpcoma_2 csn cun ftpcoma_0 ftpcoma_1 ftpcoma_2 ctp ftpcoma_1 ftpcoma_0 ftpcoma_2 ctp ftpcoma_0 ftpcoma_1 cpr ftpcoma_1 ftpcoma_0 cpr ftpcoma_2 csn ftpcoma_0 ftpcoma_1 prcom uneq1i ftpcoma_0 ftpcoma_1 ftpcoma_2 df-tp ftpcoma_1 ftpcoma_0 ftpcoma_2 df-tp 3eqtr4i $.
$}
$( /* Swap 2nd and 3rd members of an undordered triple.  (Contributed by NM,
     22-May-2015.) */

$)
${
	ftpcomb_0 $f class A $.
	ftpcomb_1 $f class B $.
	ftpcomb_2 $f class C $.
	tpcomb $p |- { A , B , C } = { A , C , B } $= ftpcomb_1 ftpcomb_2 ftpcomb_0 ctp ftpcomb_2 ftpcomb_1 ftpcomb_0 ctp ftpcomb_0 ftpcomb_1 ftpcomb_2 ctp ftpcomb_0 ftpcomb_2 ftpcomb_1 ctp ftpcomb_1 ftpcomb_2 ftpcomb_0 tpcoma ftpcomb_0 ftpcomb_1 ftpcomb_2 tprot ftpcomb_0 ftpcomb_2 ftpcomb_1 tprot 3eqtr4i $.
$}
$( /* Split off the first element of an unordered triple.  (Contributed by Mario
     Carneiro, 5-Jan-2016.) */

$)
${
	ftpass_0 $f class A $.
	ftpass_1 $f class B $.
	ftpass_2 $f class C $.
	tpass $p |- { A , B , C } = ( { A } u. { B , C } ) $= ftpass_1 ftpass_2 ftpass_0 ctp ftpass_1 ftpass_2 cpr ftpass_0 csn cun ftpass_0 ftpass_1 ftpass_2 ctp ftpass_0 csn ftpass_1 ftpass_2 cpr cun ftpass_1 ftpass_2 ftpass_0 df-tp ftpass_0 ftpass_1 ftpass_2 tprot ftpass_0 csn ftpass_1 ftpass_2 cpr uncom 3eqtr4i $.
$}
$( /* Two ways to write an unordered quadruple.  (Contributed by Mario Carneiro,
     5-Jan-2016.) */

$)
${
	fqdass_0 $f class A $.
	fqdass_1 $f class B $.
	fqdass_2 $f class C $.
	fqdass_3 $f class D $.
	qdass $p |- ( { A , B } u. { C , D } ) = ( { A , B , C } u. { D } ) $= fqdass_0 fqdass_1 cpr fqdass_2 csn cun fqdass_3 csn cun fqdass_0 fqdass_1 cpr fqdass_2 csn fqdass_3 csn cun cun fqdass_0 fqdass_1 fqdass_2 ctp fqdass_3 csn cun fqdass_0 fqdass_1 cpr fqdass_2 fqdass_3 cpr cun fqdass_0 fqdass_1 cpr fqdass_2 csn fqdass_3 csn unass fqdass_0 fqdass_1 fqdass_2 ctp fqdass_0 fqdass_1 cpr fqdass_2 csn cun fqdass_3 csn fqdass_0 fqdass_1 fqdass_2 df-tp uneq1i fqdass_2 fqdass_3 cpr fqdass_2 csn fqdass_3 csn cun fqdass_0 fqdass_1 cpr fqdass_2 fqdass_3 df-pr uneq2i 3eqtr4ri $.
$}
$( /* Two ways to write an unordered quadruple.  (Contributed by Mario Carneiro,
     5-Jan-2016.) */

$)
${
	fqdassr_0 $f class A $.
	fqdassr_1 $f class B $.
	fqdassr_2 $f class C $.
	fqdassr_3 $f class D $.
	qdassr $p |- ( { A , B } u. { C , D } ) = ( { A } u. { B , C , D } ) $= fqdassr_0 csn fqdassr_1 csn cun fqdassr_2 fqdassr_3 cpr cun fqdassr_0 csn fqdassr_1 csn fqdassr_2 fqdassr_3 cpr cun cun fqdassr_0 fqdassr_1 cpr fqdassr_2 fqdassr_3 cpr cun fqdassr_0 csn fqdassr_1 fqdassr_2 fqdassr_3 ctp cun fqdassr_0 csn fqdassr_1 csn fqdassr_2 fqdassr_3 cpr unass fqdassr_0 fqdassr_1 cpr fqdassr_0 csn fqdassr_1 csn cun fqdassr_2 fqdassr_3 cpr fqdassr_0 fqdassr_1 df-pr uneq1i fqdassr_1 fqdassr_2 fqdassr_3 ctp fqdassr_1 csn fqdassr_2 fqdassr_3 cpr cun fqdassr_0 csn fqdassr_1 fqdassr_2 fqdassr_3 tpass uneq2i 3eqtr4i $.
$}
$( /* Unordered triple ` { A , A , B } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) */

$)
${
	ftpidm12_0 $f class A $.
	ftpidm12_1 $f class B $.
	tpidm12 $p |- { A , A , B } = { A , B } $= ftpidm12_0 csn ftpidm12_1 csn cun ftpidm12_0 ftpidm12_0 cpr ftpidm12_1 csn cun ftpidm12_0 ftpidm12_1 cpr ftpidm12_0 ftpidm12_0 ftpidm12_1 ctp ftpidm12_0 csn ftpidm12_0 ftpidm12_0 cpr ftpidm12_1 csn ftpidm12_0 dfsn2 uneq1i ftpidm12_0 ftpidm12_1 df-pr ftpidm12_0 ftpidm12_0 ftpidm12_1 df-tp 3eqtr4ri $.
$}
$( /* Unordered triple ` { A , B , A } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) */

$)
${
	ftpidm13_0 $f class A $.
	ftpidm13_1 $f class B $.
	tpidm13 $p |- { A , B , A } = { A , B } $= ftpidm13_0 ftpidm13_0 ftpidm13_1 ctp ftpidm13_0 ftpidm13_1 ftpidm13_0 ctp ftpidm13_0 ftpidm13_1 cpr ftpidm13_0 ftpidm13_0 ftpidm13_1 tprot ftpidm13_0 ftpidm13_1 tpidm12 eqtr3i $.
$}
$( /* Unordered triple ` { A , B , B } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) */

$)
${
	ftpidm23_0 $f class A $.
	ftpidm23_1 $f class B $.
	tpidm23 $p |- { A , B , B } = { A , B } $= ftpidm23_0 ftpidm23_1 ftpidm23_1 ctp ftpidm23_1 ftpidm23_1 ftpidm23_0 ctp ftpidm23_1 ftpidm23_0 cpr ftpidm23_0 ftpidm23_1 cpr ftpidm23_0 ftpidm23_1 ftpidm23_1 tprot ftpidm23_1 ftpidm23_0 tpidm12 ftpidm23_1 ftpidm23_0 prcom 3eqtri $.
$}
$( /* Unordered triple ` { A , A , A } ` is just an overlong way to write
     ` { A } ` .  (Contributed by David A. Wheeler, 10-May-2015.) */

$)
${
	ftpidm_0 $f class A $.
	tpidm $p |- { A , A , A } = { A } $= ftpidm_0 ftpidm_0 ftpidm_0 ctp ftpidm_0 ftpidm_0 cpr ftpidm_0 csn ftpidm_0 ftpidm_0 tpidm12 ftpidm_0 dfsn2 eqtr4i $.
$}
$( /* An unordered pair contains its first member.  Part of Theorem 7.6 of
     [Quine] p. 49.  (Contributed by Stefan Allan, 8-Nov-2008.) */

$)
${
	fprid1g_0 $f class A $.
	fprid1g_1 $f class B $.
	fprid1g_2 $f class V $.
	prid1g $p |- ( A e. V -> A e. { A , B } ) $= fprid1g_0 fprid1g_2 wcel fprid1g_0 fprid1g_0 fprid1g_1 cpr wcel fprid1g_0 fprid1g_0 wceq fprid1g_0 fprid1g_1 wceq wo fprid1g_0 fprid1g_0 wceq fprid1g_0 fprid1g_1 wceq fprid1g_0 eqid orci fprid1g_0 fprid1g_0 fprid1g_1 fprid1g_2 elprg mpbiri $.
$}
$( /* An unordered pair contains its second member.  Part of Theorem 7.6 of
     [Quine] p. 49.  (Contributed by Stefan Allan, 8-Nov-2008.) */

$)
${
	fprid2g_0 $f class A $.
	fprid2g_1 $f class B $.
	fprid2g_2 $f class V $.
	prid2g $p |- ( B e. V -> B e. { A , B } ) $= fprid2g_1 fprid2g_2 wcel fprid2g_1 fprid2g_1 fprid2g_0 cpr fprid2g_0 fprid2g_1 cpr fprid2g_1 fprid2g_0 fprid2g_2 prid1g fprid2g_1 fprid2g_0 prcom syl6eleq $.
$}
$( /* An unordered pair contains its first member.  Part of Theorem 7.6 of
       [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fprid1_0 $f class A $.
	fprid1_1 $f class B $.
	eprid1_0 $e |- A e. _V $.
	prid1 $p |- A e. { A , B } $= fprid1_0 cvv wcel fprid1_0 fprid1_0 fprid1_1 cpr wcel eprid1_0 fprid1_0 fprid1_1 cvv prid1g ax-mp $.
$}
$( /* An unordered pair contains its second member.  Part of Theorem 7.6 of
       [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	fprid2_0 $f class A $.
	fprid2_1 $f class B $.
	eprid2_0 $e |- B e. _V $.
	prid2 $p |- B e. { A , B } $= fprid2_1 fprid2_1 fprid2_0 cpr fprid2_0 fprid2_1 cpr fprid2_1 fprid2_0 eprid2_0 prid1 fprid2_1 fprid2_0 prcom eleqtri $.
$}
$( /* A proper class vanishes in an unordered pair.  (Contributed by NM,
     5-Aug-1993.) */

$)
${
	fprprc1_0 $f class A $.
	fprprc1_1 $f class B $.
	prprc1 $p |- ( -. A e. _V -> { A , B } = { B } ) $= fprprc1_0 cvv wcel wn fprprc1_0 csn c0 wceq fprprc1_0 fprprc1_1 cpr fprprc1_1 csn wceq fprprc1_0 snprc fprprc1_0 csn c0 wceq fprprc1_0 csn fprprc1_1 csn cun c0 fprprc1_1 csn cun fprprc1_0 fprprc1_1 cpr fprprc1_1 csn fprprc1_0 csn c0 fprprc1_1 csn uneq1 fprprc1_0 fprprc1_1 df-pr c0 fprprc1_1 csn cun fprprc1_1 csn c0 cun fprprc1_1 csn c0 fprprc1_1 csn uncom fprprc1_1 csn un0 eqtr2i 3eqtr4g sylbi $.
$}
$( /* A proper class vanishes in an unordered pair.  (Contributed by NM,
     22-Mar-2006.) */

$)
${
	fprprc2_0 $f class A $.
	fprprc2_1 $f class B $.
	prprc2 $p |- ( -. B e. _V -> { A , B } = { A } ) $= fprprc2_1 cvv wcel wn fprprc2_0 fprprc2_1 cpr fprprc2_1 fprprc2_0 cpr fprprc2_0 csn fprprc2_0 fprprc2_1 prcom fprprc2_1 fprprc2_0 prprc1 syl5eq $.
$}
$( /* An unordered pair containing two proper classes is the empty set.
     (Contributed by NM, 22-Mar-2006.) */

$)
${
	fprprc_0 $f class A $.
	fprprc_1 $f class B $.
	prprc $p |- ( ( -. A e. _V /\ -. B e. _V ) -> { A , B } = (/) ) $= fprprc_0 cvv wcel wn fprprc_1 cvv wcel wn fprprc_0 fprprc_1 cpr fprprc_1 csn c0 fprprc_0 fprprc_1 prprc1 fprprc_1 cvv wcel wn fprprc_1 csn c0 wceq fprprc_1 snprc biimpi sylan9eq $.
$}
$( /* One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	ftpid1_0 $f class A $.
	ftpid1_1 $f class B $.
	ftpid1_2 $f class C $.
	etpid1_0 $e |- A e. _V $.
	tpid1 $p |- A e. { A , B , C } $= ftpid1_0 ftpid1_0 ftpid1_1 ftpid1_2 ctp wcel ftpid1_0 ftpid1_0 wceq ftpid1_0 ftpid1_1 wceq ftpid1_0 ftpid1_2 wceq w3o ftpid1_0 ftpid1_0 wceq ftpid1_0 ftpid1_1 wceq ftpid1_0 ftpid1_2 wceq ftpid1_0 eqid 3mix1i ftpid1_0 ftpid1_0 ftpid1_1 ftpid1_2 etpid1_0 eltp mpbir $.
$}
$( /* One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	ftpid2_0 $f class A $.
	ftpid2_1 $f class B $.
	ftpid2_2 $f class C $.
	etpid2_0 $e |- B e. _V $.
	tpid2 $p |- B e. { A , B , C } $= ftpid2_1 ftpid2_0 ftpid2_1 ftpid2_2 ctp wcel ftpid2_1 ftpid2_0 wceq ftpid2_1 ftpid2_1 wceq ftpid2_1 ftpid2_2 wceq w3o ftpid2_1 ftpid2_1 wceq ftpid2_1 ftpid2_0 wceq ftpid2_1 ftpid2_2 wceq ftpid2_1 eqid 3mix2i ftpid2_1 ftpid2_0 ftpid2_1 ftpid2_2 etpid2_0 eltp mpbir $.
$}
$( /* Closed theorem form of ~ tpid3 .  This proof was automatically generated
       from the virtual deduction proof ~ tpid3gVD using a translation
       program.  (Contributed by Alan Sare, 24-Oct-2011.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	itpid3g_0 $f set x $.
	ftpid3g_0 $f class A $.
	ftpid3g_1 $f class B $.
	ftpid3g_2 $f class C $.
	ftpid3g_3 $f class D $.
	tpid3g $p |- ( A e. B -> A e. { C , D , A } ) $= ftpid3g_0 ftpid3g_1 wcel itpid3g_0 sup_set_class ftpid3g_0 wceq itpid3g_0 wex ftpid3g_0 ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp wcel itpid3g_0 ftpid3g_0 ftpid3g_1 elisset ftpid3g_0 ftpid3g_1 wcel itpid3g_0 sup_set_class ftpid3g_0 wceq ftpid3g_0 ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp wcel itpid3g_0 itpid3g_0 sup_set_class ftpid3g_0 wceq itpid3g_0 sup_set_class ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp wcel ftpid3g_0 ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp wcel ftpid3g_0 ftpid3g_1 wcel ftpid3g_0 ftpid3g_1 wcel itpid3g_0 sup_set_class ftpid3g_0 wceq itpid3g_0 sup_set_class itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq itpid3g_0 sup_set_class ftpid3g_0 wceq w3o itpid3g_0 cab wcel itpid3g_0 sup_set_class ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp wcel ftpid3g_0 ftpid3g_1 wcel itpid3g_0 sup_set_class ftpid3g_0 wceq itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq itpid3g_0 sup_set_class ftpid3g_0 wceq w3o itpid3g_0 sup_set_class itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq itpid3g_0 sup_set_class ftpid3g_0 wceq w3o itpid3g_0 cab wcel itpid3g_0 sup_set_class ftpid3g_0 wceq itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq itpid3g_0 sup_set_class ftpid3g_0 wceq w3o wi ftpid3g_0 ftpid3g_1 wcel itpid3g_0 sup_set_class ftpid3g_0 wceq itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq 3mix3 a1i itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq itpid3g_0 sup_set_class ftpid3g_0 wceq w3o itpid3g_0 abid syl6ibr ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp itpid3g_0 sup_set_class ftpid3g_2 wceq itpid3g_0 sup_set_class ftpid3g_3 wceq itpid3g_0 sup_set_class ftpid3g_0 wceq w3o itpid3g_0 cab itpid3g_0 sup_set_class itpid3g_0 ftpid3g_2 ftpid3g_3 ftpid3g_0 dftp2 eleq2i syl6ibr itpid3g_0 sup_set_class ftpid3g_0 ftpid3g_2 ftpid3g_3 ftpid3g_0 ctp eleq1 mpbidi exlimdv mpd $.
$}
$( /* One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	ftpid3_0 $f class A $.
	ftpid3_1 $f class B $.
	ftpid3_2 $f class C $.
	etpid3_0 $e |- C e. _V $.
	tpid3 $p |- C e. { A , B , C } $= ftpid3_2 ftpid3_0 ftpid3_1 ftpid3_2 ctp wcel ftpid3_2 ftpid3_0 wceq ftpid3_2 ftpid3_1 wceq ftpid3_2 ftpid3_2 wceq w3o ftpid3_2 ftpid3_2 wceq ftpid3_2 ftpid3_0 wceq ftpid3_2 ftpid3_1 wceq ftpid3_2 eqid 3mix3i ftpid3_2 ftpid3_0 ftpid3_1 ftpid3_2 etpid3_0 eltp mpbir $.
$}
$( /* The singleton of a set is not empty.  (Contributed by NM, 14-Dec-2008.) */

$)
${
	fsnnzg_0 $f class A $.
	fsnnzg_1 $f class V $.
	snnzg $p |- ( A e. V -> { A } =/= (/) ) $= fsnnzg_0 fsnnzg_1 wcel fsnnzg_0 fsnnzg_0 csn wcel fsnnzg_0 csn c0 wne fsnnzg_0 fsnnzg_1 snidg fsnnzg_0 csn fsnnzg_0 ne0i syl $.
$}
$( /* The singleton of a set is not empty.  (Contributed by NM,
       10-Apr-1994.) */

$)
${
	fsnnz_0 $f class A $.
	esnnz_0 $e |- A e. _V $.
	snnz $p |- { A } =/= (/) $= fsnnz_0 cvv wcel fsnnz_0 csn c0 wne esnnz_0 fsnnz_0 cvv snnzg ax-mp $.
$}
$( /* A pair containing a set is not empty.  (Contributed by NM,
       9-Apr-1994.) */

$)
${
	fprnz_0 $f class A $.
	fprnz_1 $f class B $.
	eprnz_0 $e |- A e. _V $.
	prnz $p |- { A , B } =/= (/) $= fprnz_0 fprnz_0 fprnz_1 cpr wcel fprnz_0 fprnz_1 cpr c0 wne fprnz_0 fprnz_1 eprnz_0 prid1 fprnz_0 fprnz_1 cpr fprnz_0 ne0i ax-mp $.
$}
$( /* A pair containing a set is not empty.  (Contributed by FL,
       19-Sep-2011.) */

$)
${
	$d x A $.
	$d x B $.
	iprnzg_0 $f set x $.
	fprnzg_0 $f class A $.
	fprnzg_1 $f class B $.
	fprnzg_2 $f class V $.
	prnzg $p |- ( A e. V -> { A , B } =/= (/) ) $= iprnzg_0 sup_set_class fprnzg_1 cpr c0 wne fprnzg_0 fprnzg_1 cpr c0 wne iprnzg_0 fprnzg_0 fprnzg_2 iprnzg_0 sup_set_class fprnzg_0 wceq iprnzg_0 sup_set_class fprnzg_1 cpr fprnzg_0 fprnzg_1 cpr c0 iprnzg_0 sup_set_class fprnzg_0 fprnzg_1 preq1 neeq1d iprnzg_0 sup_set_class fprnzg_1 iprnzg_0 vex prnz vtoclg $.
$}
$( /* A triplet containing a set is not empty.  (Contributed by NM,
       10-Apr-1994.) */

$)
${
	ftpnz_0 $f class A $.
	ftpnz_1 $f class B $.
	ftpnz_2 $f class C $.
	etpnz_0 $e |- A e. _V $.
	tpnz $p |- { A , B , C } =/= (/) $= ftpnz_0 ftpnz_0 ftpnz_1 ftpnz_2 ctp wcel ftpnz_0 ftpnz_1 ftpnz_2 ctp c0 wne ftpnz_0 ftpnz_1 ftpnz_2 etpnz_0 tpid1 ftpnz_0 ftpnz_1 ftpnz_2 ctp ftpnz_0 ne0i ax-mp $.
$}
$( /* The singleton of an element of a class is a subset of the class.
       Theorem 7.4 of [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) */

$)
${
	$d A x $.
	$d B x $.
	isnss_0 $f set x $.
	fsnss_0 $f class A $.
	fsnss_1 $f class B $.
	esnss_0 $e |- A e. _V $.
	snss $p |- ( A e. B <-> { A } C_ B ) $= isnss_0 sup_set_class fsnss_0 csn wcel isnss_0 sup_set_class fsnss_1 wcel wi isnss_0 wal isnss_0 sup_set_class fsnss_0 wceq isnss_0 sup_set_class fsnss_1 wcel wi isnss_0 wal fsnss_0 csn fsnss_1 wss fsnss_0 fsnss_1 wcel isnss_0 sup_set_class fsnss_0 csn wcel isnss_0 sup_set_class fsnss_1 wcel wi isnss_0 sup_set_class fsnss_0 wceq isnss_0 sup_set_class fsnss_1 wcel wi isnss_0 isnss_0 sup_set_class fsnss_0 csn wcel isnss_0 sup_set_class fsnss_0 wceq isnss_0 sup_set_class fsnss_1 wcel isnss_0 fsnss_0 elsn imbi1i albii isnss_0 fsnss_0 csn fsnss_1 dfss2 isnss_0 fsnss_0 fsnss_1 esnss_0 clel2 3bitr4ri $.
$}
$( /* Membership in a set with an element removed.  (Contributed by NM,
     10-Oct-2007.) */

$)
${
	feldifsn_0 $f class A $.
	feldifsn_1 $f class B $.
	feldifsn_2 $f class C $.
	eldifsn $p |- ( A e. ( B \ { C } ) <-> ( A e. B /\ A =/= C ) ) $= feldifsn_0 feldifsn_1 feldifsn_2 csn cdif wcel feldifsn_0 feldifsn_1 wcel feldifsn_0 feldifsn_2 csn wcel wn wa feldifsn_0 feldifsn_1 wcel feldifsn_0 feldifsn_2 wne wa feldifsn_0 feldifsn_1 feldifsn_2 csn eldif feldifsn_0 feldifsn_1 wcel feldifsn_0 feldifsn_2 csn wcel wn feldifsn_0 feldifsn_2 wne feldifsn_0 feldifsn_1 wcel feldifsn_0 feldifsn_2 csn wcel feldifsn_0 feldifsn_2 feldifsn_0 feldifsn_2 feldifsn_1 elsncg necon3bbid pm5.32i bitri $.
$}
$( /* Membership in a set with an element removed.  (Contributed by NM,
     10-Mar-2015.) */

$)
${
	feldifsni_0 $f class A $.
	feldifsni_1 $f class B $.
	feldifsni_2 $f class C $.
	eldifsni $p |- ( A e. ( B \ { C } ) -> A =/= C ) $= feldifsni_0 feldifsni_1 feldifsni_2 csn cdif wcel feldifsni_0 feldifsni_1 wcel feldifsni_0 feldifsni_2 wne feldifsni_0 feldifsni_1 feldifsni_2 eldifsn simprbi $.
$}
$( /* ` A ` is not in ` ( B \ { A } ) ` .  (Contributed by David Moews,
     1-May-2017.) */

$)
${
	fneldifsn_0 $f class A $.
	fneldifsn_1 $f class B $.
	neldifsn $p |- -. A e. ( B \ { A } ) $= fneldifsn_0 fneldifsn_1 fneldifsn_0 csn cdif wcel fneldifsn_0 fneldifsn_0 wne fneldifsn_0 neirr fneldifsn_0 fneldifsn_1 fneldifsn_0 eldifsni mto $.
$}
$( /* ` A ` is not in ` ( B \ { A } ) ` .  Deduction form.  (Contributed by
     David Moews, 1-May-2017.) */

$)
${
	fneldifsnd_0 $f wff ph $.
	fneldifsnd_1 $f class A $.
	fneldifsnd_2 $f class B $.
	neldifsnd $p |- ( ph -> -. A e. ( B \ { A } ) ) $= fneldifsnd_1 fneldifsnd_2 fneldifsnd_1 csn cdif wcel wn fneldifsnd_0 fneldifsnd_1 fneldifsnd_2 neldifsn a1i $.
$}
$( /* Restricted existential quantification over a set with an element removed.
     (Contributed by NM, 4-Feb-2015.) */

$)
${
	frexdifsn_0 $f wff ph $.
	frexdifsn_1 $f set x $.
	frexdifsn_2 $f class A $.
	frexdifsn_3 $f class B $.
	rexdifsn $p |- ( E. x e. ( A \ { B } ) ph <-> E. x e. A ( x =/= B /\ ph ) ) $= frexdifsn_0 frexdifsn_1 sup_set_class frexdifsn_3 wne frexdifsn_0 wa frexdifsn_1 frexdifsn_2 frexdifsn_3 csn cdif frexdifsn_2 frexdifsn_1 sup_set_class frexdifsn_2 frexdifsn_3 csn cdif wcel frexdifsn_0 wa frexdifsn_1 sup_set_class frexdifsn_2 wcel frexdifsn_1 sup_set_class frexdifsn_3 wne wa frexdifsn_0 wa frexdifsn_1 sup_set_class frexdifsn_2 wcel frexdifsn_1 sup_set_class frexdifsn_3 wne frexdifsn_0 wa wa frexdifsn_1 sup_set_class frexdifsn_2 frexdifsn_3 csn cdif wcel frexdifsn_1 sup_set_class frexdifsn_2 wcel frexdifsn_1 sup_set_class frexdifsn_3 wne wa frexdifsn_0 frexdifsn_1 sup_set_class frexdifsn_2 frexdifsn_3 eldifsn anbi1i frexdifsn_1 sup_set_class frexdifsn_2 wcel frexdifsn_1 sup_set_class frexdifsn_3 wne frexdifsn_0 anass bitri rexbii2 $.
$}
$( /* The singleton of an element of a class is a subset of the class.
       Theorem 7.4 of [Quine] p. 49.  (Contributed by NM, 22-Jul-2001.) */

$)
${
	$d A x $.
	$d B x $.
	isnssg_0 $f set x $.
	fsnssg_0 $f class A $.
	fsnssg_1 $f class B $.
	fsnssg_2 $f class V $.
	snssg $p |- ( A e. V -> ( A e. B <-> { A } C_ B ) ) $= isnssg_0 sup_set_class fsnssg_1 wcel isnssg_0 sup_set_class csn fsnssg_1 wss fsnssg_0 fsnssg_1 wcel fsnssg_0 csn fsnssg_1 wss isnssg_0 fsnssg_0 fsnssg_2 isnssg_0 sup_set_class fsnssg_0 fsnssg_1 eleq1 isnssg_0 sup_set_class fsnssg_0 wceq isnssg_0 sup_set_class csn fsnssg_0 csn fsnssg_1 isnssg_0 sup_set_class fsnssg_0 sneq sseq1d isnssg_0 sup_set_class fsnssg_1 isnssg_0 vex snss vtoclbg $.
$}
$( /* An element not in a set can be removed without affecting the set.
       (Contributed by NM, 16-Mar-2006.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) */

$)
${
	$d A x $.
	$d B x $.
	idifsn_0 $f set x $.
	fdifsn_0 $f class A $.
	fdifsn_1 $f class B $.
	difsn $p |- ( -. A e. B -> ( B \ { A } ) = B ) $= fdifsn_0 fdifsn_1 wcel wn idifsn_0 fdifsn_1 fdifsn_0 csn cdif fdifsn_1 idifsn_0 sup_set_class fdifsn_1 fdifsn_0 csn cdif wcel idifsn_0 sup_set_class fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_0 wne wa fdifsn_0 fdifsn_1 wcel wn idifsn_0 sup_set_class fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_1 fdifsn_0 eldifsn fdifsn_0 fdifsn_1 wcel wn idifsn_0 sup_set_class fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_0 wne wa idifsn_0 sup_set_class fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_0 wne simpl fdifsn_0 fdifsn_1 wcel wn idifsn_0 sup_set_class fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_0 wne idifsn_0 sup_set_class fdifsn_1 wcel fdifsn_0 fdifsn_1 wcel wn idifsn_0 sup_set_class fdifsn_0 wne idifsn_0 sup_set_class fdifsn_1 wcel fdifsn_0 fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_0 idifsn_0 sup_set_class fdifsn_0 wceq idifsn_0 sup_set_class fdifsn_1 wcel fdifsn_0 fdifsn_1 wcel idifsn_0 sup_set_class fdifsn_0 fdifsn_1 eleq1 biimpcd necon3bd com12 ancld impbid2 syl5bb eqrdv $.
$}
$( /* Removal of a singleton from an unordered pair.  (Contributed by NM,
       16-Mar-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	$d A x $.
	$d B x $.
	idifprsn_0 $f set x $.
	fdifprsn_0 $f class A $.
	fdifprsn_1 $f class B $.
	difprsn $p |- ( { A , B } \ { A } ) C_ { B } $= idifprsn_0 fdifprsn_0 fdifprsn_1 cpr fdifprsn_0 csn cdif fdifprsn_1 csn idifprsn_0 sup_set_class fdifprsn_0 fdifprsn_1 cpr wcel idifprsn_0 sup_set_class fdifprsn_0 csn wcel wn wa idifprsn_0 sup_set_class fdifprsn_1 wceq idifprsn_0 sup_set_class fdifprsn_0 fdifprsn_1 cpr fdifprsn_0 csn cdif wcel idifprsn_0 sup_set_class fdifprsn_1 csn wcel idifprsn_0 sup_set_class fdifprsn_0 fdifprsn_1 cpr wcel idifprsn_0 sup_set_class fdifprsn_0 wceq idifprsn_0 sup_set_class fdifprsn_1 wceq wo idifprsn_0 sup_set_class fdifprsn_0 wceq wn idifprsn_0 sup_set_class fdifprsn_1 wceq idifprsn_0 sup_set_class fdifprsn_0 csn wcel wn idifprsn_0 sup_set_class fdifprsn_0 fdifprsn_1 idifprsn_0 vex elpr idifprsn_0 sup_set_class fdifprsn_0 csn wcel idifprsn_0 sup_set_class fdifprsn_0 wceq idifprsn_0 fdifprsn_0 elsn notbii idifprsn_0 sup_set_class fdifprsn_0 wceq wn idifprsn_0 sup_set_class fdifprsn_1 wceq idifprsn_0 sup_set_class fdifprsn_0 wceq idifprsn_0 sup_set_class fdifprsn_1 wceq wo idifprsn_0 sup_set_class fdifprsn_0 wceq idifprsn_0 sup_set_class fdifprsn_1 wceq biorf biimparc syl2anb idifprsn_0 sup_set_class fdifprsn_0 fdifprsn_1 cpr fdifprsn_0 csn eldif idifprsn_0 fdifprsn_1 elsn 3imtr4i ssriv $.
$}
$( /* ` ( B \ { A } ) ` equals ` B ` if and only if ` A ` is not a member of
     ` B ` .  Generalization of ~ difsn .  (Contributed by David Moews,
     1-May-2017.) */

$)
${
	fdifsneq_0 $f class A $.
	fdifsneq_1 $f class B $.
	difsneq $p |- ( -. A e. B <-> ( B \ { A } ) = B ) $= fdifsneq_0 fdifsneq_1 wcel wn fdifsneq_1 fdifsneq_0 csn cdif fdifsneq_1 wceq fdifsneq_0 fdifsneq_1 difsn fdifsneq_0 fdifsneq_1 wcel fdifsneq_1 fdifsneq_0 csn cdif fdifsneq_1 fdifsneq_0 fdifsneq_1 wcel fdifsneq_1 fdifsneq_1 fdifsneq_0 csn cdif fdifsneq_0 fdifsneq_1 wcel fdifsneq_0 fdifsneq_1 fdifsneq_0 csn cdif wcel wn fdifsneq_1 fdifsneq_1 fdifsneq_0 csn cdif wne fdifsneq_0 fdifsneq_1 wcel fdifsneq_0 fdifsneq_1 neldifsnd fdifsneq_0 fdifsneq_1 fdifsneq_1 fdifsneq_0 csn cdif nelne1 mpdan necomd necon2bi impbii $.
$}
$( /* ` ( B \ { A } ) ` is a proper subclass of ` B ` if and only if ` A ` is a
     member of ` B ` .  (Contributed by David Moews, 1-May-2017.) */

$)
${
	fdifsnpss_0 $f class A $.
	fdifsnpss_1 $f class B $.
	difsnpss $p |- ( A e. B <-> ( B \ { A } ) C. B ) $= fdifsnpss_0 fdifsnpss_1 wcel fdifsnpss_0 fdifsnpss_1 wcel wn wn fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wpss fdifsnpss_0 fdifsnpss_1 wcel notnot fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wne fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wss fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wne wa fdifsnpss_0 fdifsnpss_1 wcel wn wn fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wpss fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wss fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 wne fdifsnpss_1 fdifsnpss_0 csn difss biantrur fdifsnpss_0 fdifsnpss_1 wcel wn fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 fdifsnpss_0 fdifsnpss_1 difsneq necon3bbii fdifsnpss_1 fdifsnpss_0 csn cdif fdifsnpss_1 df-pss 3bitr4i bitri $.
$}
$( /* The singleton of an element of a class is a subset of the class.
     (Contributed by NM, 6-Jun-1994.) */

$)
${
	fsnssi_0 $f class A $.
	fsnssi_1 $f class B $.
	snssi $p |- ( A e. B -> { A } C_ B ) $= fsnssi_0 fsnssi_1 wcel fsnssi_0 csn fsnssi_1 wss fsnssi_0 fsnssi_1 fsnssi_1 snssg ibi $.
$}
$( /* The singleton of an element of a class is a subset of the class
       (deduction rule).  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) */

$)
${
	fsnssd_0 $f wff ph $.
	fsnssd_1 $f class A $.
	fsnssd_2 $f class B $.
	esnssd_0 $e |- ( ph -> A e. B ) $.
	snssd $p |- ( ph -> { A } C_ B ) $= fsnssd_0 fsnssd_1 fsnssd_2 wcel fsnssd_1 csn fsnssd_2 wss esnssd_0 fsnssd_0 fsnssd_1 fsnssd_2 wcel fsnssd_1 fsnssd_2 wcel fsnssd_1 csn fsnssd_2 wss wb esnssd_0 fsnssd_1 fsnssd_2 fsnssd_2 snssg syl mpbid $.
$}
$( /* If we remove a single element from a class then put it back in, we end up
     with the original class.  (Contributed by NM, 2-Oct-2006.) */

$)
${
	fdifsnid_0 $f class A $.
	fdifsnid_1 $f class B $.
	difsnid $p |- ( B e. A -> ( ( A \ { B } ) u. { B } ) = A ) $= fdifsnid_1 fdifsnid_0 wcel fdifsnid_0 fdifsnid_1 csn cdif fdifsnid_1 csn cun fdifsnid_1 csn fdifsnid_0 fdifsnid_1 csn cdif cun fdifsnid_0 fdifsnid_0 fdifsnid_1 csn cdif fdifsnid_1 csn uncom fdifsnid_1 fdifsnid_0 wcel fdifsnid_1 csn fdifsnid_0 wss fdifsnid_1 csn fdifsnid_0 fdifsnid_1 csn cdif cun fdifsnid_0 wceq fdifsnid_1 fdifsnid_0 snssi fdifsnid_1 csn fdifsnid_0 undif sylib syl5eq $.
$}
$( /* Note that ` x ` is a dummy variable in the proof below. */

$)
$( /* Compute the power set of the empty set.  Theorem 89 of [Suppes] p. 47.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) */

$)
${
	ipw0_0 $f set x $.
	pw0 $p |- ~P (/) = { (/) } $= ipw0_0 sup_set_class c0 wss ipw0_0 cab ipw0_0 sup_set_class c0 wceq ipw0_0 cab c0 cpw c0 csn ipw0_0 sup_set_class c0 wss ipw0_0 sup_set_class c0 wceq ipw0_0 ipw0_0 sup_set_class ss0b abbii ipw0_0 c0 df-pw ipw0_0 c0 df-sn 3eqtr4i $.
$}
$( /* Compute the power set of the power set of the empty set.  (See ~ pw0 for
       the power set of the empty set.)  Theorem 90 of [Suppes] p. 48.
       Although this theorem is a special case of ~ pwsn , we have chosen to
       show a direct elementary proof.  (Contributed by NM, 7-Aug-1994.) */

$)
${
	$d x y $.
	ipwpw0_0 $f set x $.
	ipwpw0_1 $f set y $.
	pwpw0 $p |- ~P { (/) } = { (/) , { (/) } } $= ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 cab ipwpw0_0 sup_set_class c0 wceq ipwpw0_0 sup_set_class c0 csn wceq wo ipwpw0_0 cab c0 csn cpw c0 c0 csn cpr ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 sup_set_class c0 wceq ipwpw0_0 sup_set_class c0 csn wceq wo ipwpw0_0 ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 sup_set_class c0 wceq ipwpw0_0 sup_set_class c0 csn wceq wo ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 sup_set_class c0 wceq ipwpw0_0 sup_set_class c0 csn wceq ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 sup_set_class c0 wceq wn ipwpw0_0 sup_set_class c0 csn wss c0 csn ipwpw0_0 sup_set_class wss wa ipwpw0_0 sup_set_class c0 csn wceq ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 sup_set_class c0 wceq wn c0 csn ipwpw0_0 sup_set_class wss ipwpw0_0 sup_set_class c0 csn wss ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wi ipwpw0_1 wal ipwpw0_0 sup_set_class c0 wceq wn c0 csn ipwpw0_0 sup_set_class wss wi ipwpw0_0 sup_set_class c0 csn wss ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 csn wcel wi ipwpw0_1 wal ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wi ipwpw0_1 wal ipwpw0_1 ipwpw0_0 sup_set_class c0 csn dfss2 ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 csn wcel wi ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wi ipwpw0_1 ipwpw0_1 sup_set_class c0 csn wcel ipwpw0_1 sup_set_class c0 wceq ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 c0 elsn imbi2i albii bitri ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wi ipwpw0_1 wal ipwpw0_0 sup_set_class c0 wceq wn ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wa ipwpw0_1 wex c0 csn ipwpw0_0 sup_set_class wss ipwpw0_0 sup_set_class c0 wceq wn ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 wex ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wi ipwpw0_1 wal ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wa ipwpw0_1 wex ipwpw0_1 ipwpw0_0 sup_set_class neq0 ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq ipwpw0_1 exintr syl5bi ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wa ipwpw0_1 wex c0 ipwpw0_0 sup_set_class wcel c0 csn ipwpw0_0 sup_set_class wss ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq wa ipwpw0_1 wex ipwpw0_1 sup_set_class c0 wceq ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel wa ipwpw0_1 wex c0 ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class ipwpw0_0 sup_set_class wcel ipwpw0_1 sup_set_class c0 wceq ipwpw0_1 exancom ipwpw0_1 c0 ipwpw0_0 sup_set_class df-clel bitr4i c0 ipwpw0_0 sup_set_class snssi sylbi syl6 sylbi anc2li ipwpw0_0 sup_set_class c0 csn eqss syl6ibr orrd ipwpw0_0 sup_set_class c0 wceq ipwpw0_0 sup_set_class c0 csn wss ipwpw0_0 sup_set_class c0 csn wceq ipwpw0_0 sup_set_class c0 wceq ipwpw0_0 sup_set_class c0 csn wss c0 c0 csn wss c0 csn 0ss ipwpw0_0 sup_set_class c0 c0 csn sseq1 mpbiri ipwpw0_0 sup_set_class c0 csn eqimss jaoi impbii abbii ipwpw0_0 c0 csn df-pw ipwpw0_0 c0 c0 csn dfpr2 3eqtr4i $.
$}
$( /* A singleton is a subset of an unordered pair containing its member.
     (Contributed by NM, 27-Aug-2004.) */

$)
${
	fsnsspr1_0 $f class A $.
	fsnsspr1_1 $f class B $.
	snsspr1 $p |- { A } C_ { A , B } $= fsnsspr1_0 csn fsnsspr1_0 csn fsnsspr1_1 csn cun fsnsspr1_0 fsnsspr1_1 cpr fsnsspr1_0 csn fsnsspr1_1 csn ssun1 fsnsspr1_0 fsnsspr1_1 df-pr sseqtr4i $.
$}
$( /* A singleton is a subset of an unordered pair containing its member.
     (Contributed by NM, 2-May-2009.) */

$)
${
	fsnsspr2_0 $f class A $.
	fsnsspr2_1 $f class B $.
	snsspr2 $p |- { B } C_ { A , B } $= fsnsspr2_1 csn fsnsspr2_0 csn fsnsspr2_1 csn cun fsnsspr2_0 fsnsspr2_1 cpr fsnsspr2_1 csn fsnsspr2_0 csn ssun2 fsnsspr2_0 fsnsspr2_1 df-pr sseqtr4i $.
$}
$( /* A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) */

$)
${
	fsnsstp1_0 $f class A $.
	fsnsstp1_1 $f class B $.
	fsnsstp1_2 $f class C $.
	snsstp1 $p |- { A } C_ { A , B , C } $= fsnsstp1_0 csn fsnsstp1_0 fsnsstp1_1 cpr fsnsstp1_2 csn cun fsnsstp1_0 fsnsstp1_1 fsnsstp1_2 ctp fsnsstp1_0 csn fsnsstp1_0 fsnsstp1_1 cpr fsnsstp1_0 fsnsstp1_1 cpr fsnsstp1_2 csn cun fsnsstp1_0 fsnsstp1_1 snsspr1 fsnsstp1_0 fsnsstp1_1 cpr fsnsstp1_2 csn ssun1 sstri fsnsstp1_0 fsnsstp1_1 fsnsstp1_2 df-tp sseqtr4i $.
$}
$( /* A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) */

$)
${
	fsnsstp2_0 $f class A $.
	fsnsstp2_1 $f class B $.
	fsnsstp2_2 $f class C $.
	snsstp2 $p |- { B } C_ { A , B , C } $= fsnsstp2_1 csn fsnsstp2_0 fsnsstp2_1 cpr fsnsstp2_2 csn cun fsnsstp2_0 fsnsstp2_1 fsnsstp2_2 ctp fsnsstp2_1 csn fsnsstp2_0 fsnsstp2_1 cpr fsnsstp2_0 fsnsstp2_1 cpr fsnsstp2_2 csn cun fsnsstp2_0 fsnsstp2_1 snsspr2 fsnsstp2_0 fsnsstp2_1 cpr fsnsstp2_2 csn ssun1 sstri fsnsstp2_0 fsnsstp2_1 fsnsstp2_2 df-tp sseqtr4i $.
$}
$( /* A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) */

$)
${
	fsnsstp3_0 $f class A $.
	fsnsstp3_1 $f class B $.
	fsnsstp3_2 $f class C $.
	snsstp3 $p |- { C } C_ { A , B , C } $= fsnsstp3_2 csn fsnsstp3_0 fsnsstp3_1 cpr fsnsstp3_2 csn cun fsnsstp3_0 fsnsstp3_1 fsnsstp3_2 ctp fsnsstp3_2 csn fsnsstp3_0 fsnsstp3_1 cpr ssun2 fsnsstp3_0 fsnsstp3_1 fsnsstp3_2 df-tp sseqtr4i $.
$}
$( /* A pair of elements of a class is a subset of the class.  Theorem 7.5 of
       [Quine] p. 49.  (Contributed by NM, 30-May-1994.)  (Proof shortened by
       Andrew Salmon, 29-Jun-2011.) */

$)
${
	fprss_0 $f class A $.
	fprss_1 $f class B $.
	fprss_2 $f class C $.
	eprss_0 $e |- A e. _V $.
	eprss_1 $e |- B e. _V $.
	prss $p |- ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) $= fprss_0 csn fprss_2 wss fprss_1 csn fprss_2 wss wa fprss_0 csn fprss_1 csn cun fprss_2 wss fprss_0 fprss_2 wcel fprss_1 fprss_2 wcel wa fprss_0 fprss_1 cpr fprss_2 wss fprss_0 csn fprss_1 csn fprss_2 unss fprss_0 fprss_2 wcel fprss_0 csn fprss_2 wss fprss_1 fprss_2 wcel fprss_1 csn fprss_2 wss fprss_0 fprss_2 eprss_0 snss fprss_1 fprss_2 eprss_1 snss anbi12i fprss_0 fprss_1 cpr fprss_0 csn fprss_1 csn cun fprss_2 fprss_0 fprss_1 df-pr sseq1i 3bitr4i $.
$}
$( /* A pair of elements of a class is a subset of the class.  Theorem 7.5 of
       [Quine] p. 49.  (Contributed by NM, 22-Mar-2006.)  (Proof shortened by
       Andrew Salmon, 29-Jun-2011.) */

$)
${
	fprssg_0 $f class A $.
	fprssg_1 $f class B $.
	fprssg_2 $f class C $.
	fprssg_3 $f class V $.
	fprssg_4 $f class W $.
	prssg $p |- ( ( A e. V /\ B e. W ) -> ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) ) $= fprssg_0 fprssg_3 wcel fprssg_1 fprssg_4 wcel wa fprssg_0 fprssg_2 wcel fprssg_1 fprssg_2 wcel wa fprssg_0 csn fprssg_2 wss fprssg_1 csn fprssg_2 wss wa fprssg_0 fprssg_1 cpr fprssg_2 wss fprssg_0 fprssg_3 wcel fprssg_0 fprssg_2 wcel fprssg_0 csn fprssg_2 wss fprssg_1 fprssg_4 wcel fprssg_1 fprssg_2 wcel fprssg_1 csn fprssg_2 wss fprssg_0 fprssg_2 fprssg_3 snssg fprssg_1 fprssg_2 fprssg_4 snssg bi2anan9 fprssg_0 csn fprssg_2 wss fprssg_1 csn fprssg_2 wss wa fprssg_0 csn fprssg_1 csn cun fprssg_2 wss fprssg_0 fprssg_1 cpr fprssg_2 wss fprssg_0 csn fprssg_1 csn fprssg_2 unss fprssg_0 fprssg_1 cpr fprssg_0 csn fprssg_1 csn cun fprssg_2 fprssg_0 fprssg_1 df-pr sseq1i bitr4i syl6bb $.
$}
$( /* A pair of elements of a class is a subset of the class.  (Contributed by
     NM, 16-Jan-2015.) */

$)
${
	fprssi_0 $f class A $.
	fprssi_1 $f class B $.
	fprssi_2 $f class C $.
	prssi $p |- ( ( A e. C /\ B e. C ) -> { A , B } C_ C ) $= fprssi_0 fprssi_2 wcel fprssi_1 fprssi_2 wcel wa fprssi_0 fprssi_1 cpr fprssi_2 wss fprssi_0 fprssi_1 fprssi_2 fprssi_2 fprssi_2 prssg ibi $.
$}
$( /* The subsets of a singleton.  (Contributed by NM, 24-Apr-2004.) */

$)
${
	$d x A $.
	$d x B $.
	isssn_0 $f set x $.
	fsssn_0 $f class A $.
	fsssn_1 $f class B $.
	sssn $p |- ( A C_ { B } <-> ( A = (/) \/ A = { B } ) ) $= fsssn_0 fsssn_1 csn wss fsssn_0 c0 wceq fsssn_0 fsssn_1 csn wceq wo fsssn_0 fsssn_1 csn wss fsssn_0 c0 wceq fsssn_0 fsssn_1 csn wceq fsssn_0 fsssn_1 csn wss fsssn_0 c0 wceq wn fsssn_0 fsssn_1 csn wss fsssn_1 csn fsssn_0 wss wa fsssn_0 fsssn_1 csn wceq fsssn_0 fsssn_1 csn wss fsssn_0 c0 wceq wn fsssn_1 csn fsssn_0 wss fsssn_0 fsssn_1 csn wss fsssn_0 c0 wceq wn fsssn_1 fsssn_0 wcel fsssn_1 csn fsssn_0 wss fsssn_0 c0 wceq wn isssn_0 sup_set_class fsssn_0 wcel isssn_0 wex fsssn_0 fsssn_1 csn wss fsssn_1 fsssn_0 wcel isssn_0 fsssn_0 neq0 fsssn_0 fsssn_1 csn wss isssn_0 sup_set_class fsssn_0 wcel fsssn_1 fsssn_0 wcel isssn_0 fsssn_0 fsssn_1 csn wss isssn_0 sup_set_class fsssn_0 wcel fsssn_1 fsssn_0 wcel fsssn_0 fsssn_1 csn wss isssn_0 sup_set_class fsssn_0 wcel isssn_0 sup_set_class fsssn_1 wceq isssn_0 sup_set_class fsssn_0 wcel fsssn_1 fsssn_0 wcel wb fsssn_0 fsssn_1 csn wss isssn_0 sup_set_class fsssn_0 wcel isssn_0 sup_set_class fsssn_1 csn wcel isssn_0 sup_set_class fsssn_1 wceq fsssn_0 fsssn_1 csn isssn_0 sup_set_class ssel isssn_0 sup_set_class fsssn_1 elsni syl6 isssn_0 sup_set_class fsssn_1 fsssn_0 eleq1 syl6 ibd exlimdv syl5bi fsssn_1 fsssn_0 snssi syl6 anc2li fsssn_0 fsssn_1 csn eqss syl6ibr orrd fsssn_0 c0 wceq fsssn_0 fsssn_1 csn wss fsssn_0 fsssn_1 csn wceq fsssn_0 c0 wceq fsssn_0 fsssn_1 csn wss c0 fsssn_1 csn wss fsssn_1 csn 0ss fsssn_0 c0 fsssn_1 csn sseq1 mpbiri fsssn_0 fsssn_1 csn eqimss jaoi impbii $.
$}
$( /* The property of being sandwiched between two sets naturally splits under
       union with a singleton.  This is the induction hypothesis for the
       determination of large powersets such as ~ pwtp .  (Contributed by Mario
       Carneiro, 2-Jul-2016.) */

$)
${
	fssunsn2_0 $f class A $.
	fssunsn2_1 $f class B $.
	fssunsn2_2 $f class C $.
	fssunsn2_3 $f class D $.
	ssunsn2 $p |- ( ( B C_ A /\ A C_ ( C u. { D } ) ) <-> ( ( B C_ A /\ A C_ C ) \/ ( ( B u. { D } ) C_ A /\ A C_ ( C u. { D } ) ) ) ) $= fssunsn2_3 fssunsn2_0 wcel fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa wo wb fssunsn2_3 fssunsn2_0 wcel fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa wo fssunsn2_3 fssunsn2_0 wcel fssunsn2_1 fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_3 fssunsn2_0 wcel fssunsn2_3 csn fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss wb fssunsn2_3 fssunsn2_0 snssi fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_3 csn fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_3 csn fssunsn2_0 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn fssunsn2_0 unss bicomi rbaibr syl anbi1d fssunsn2_3 fssunsn2_0 wcel fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa wi fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa wo wb fssunsn2_3 fssunsn2_0 wcel fssunsn2_1 fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_3 fssunsn2_0 wcel fssunsn2_3 csn fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss wi fssunsn2_3 fssunsn2_0 snssi fssunsn2_1 fssunsn2_0 wss fssunsn2_3 csn fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_3 csn fssunsn2_0 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn fssunsn2_0 unss biimpi expcom syl fssunsn2_0 fssunsn2_2 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wi fssunsn2_3 fssunsn2_0 wcel fssunsn2_0 fssunsn2_2 fssunsn2_3 csn ssun3 a1i anim12d fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa pm4.72 sylib bitrd fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa wo fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_0 fssunsn2_2 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_2 wss fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_0 fssunsn2_3 csn cdif wceq fssunsn2_0 fssunsn2_2 wss fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 wss wb fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_3 csn cin c0 wceq fssunsn2_0 fssunsn2_0 fssunsn2_3 csn cdif wceq fssunsn2_0 fssunsn2_3 disjsn fssunsn2_0 fssunsn2_3 csn disj3 bitr3i fssunsn2_0 fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 sseq1 sylbi fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_0 fssunsn2_3 csn fssunsn2_2 cun wss fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 wss fssunsn2_3 csn fssunsn2_2 cun fssunsn2_2 fssunsn2_3 csn cun fssunsn2_0 fssunsn2_3 csn fssunsn2_2 uncom sseq2i fssunsn2_0 fssunsn2_3 csn fssunsn2_2 ssundif bitr3i syl6rbbr anbi2d fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa wo fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa wo fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa wi fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa wo wb fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_0 fssunsn2_2 wss fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss wi fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_3 csn fssunsn2_0 wss fssunsn2_1 fssunsn2_0 wss fssunsn2_3 csn fssunsn2_0 wss wa fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_1 fssunsn2_3 csn fssunsn2_0 unss bicomi simplbi a1i fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_0 fssunsn2_2 wss fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_2 wss fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_0 fssunsn2_3 csn cdif wceq fssunsn2_0 fssunsn2_2 wss fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 wss wb fssunsn2_3 fssunsn2_0 wcel wn fssunsn2_0 fssunsn2_3 csn cin c0 wceq fssunsn2_0 fssunsn2_0 fssunsn2_3 csn cdif wceq fssunsn2_0 fssunsn2_3 disjsn fssunsn2_0 fssunsn2_3 csn disj3 bitr3i fssunsn2_0 fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 sseq1 sylbi fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss fssunsn2_0 fssunsn2_3 csn fssunsn2_2 cun wss fssunsn2_0 fssunsn2_3 csn cdif fssunsn2_2 wss fssunsn2_3 csn fssunsn2_2 cun fssunsn2_2 fssunsn2_3 csn cun fssunsn2_0 fssunsn2_3 csn fssunsn2_2 uncom sseq2i fssunsn2_0 fssunsn2_3 csn fssunsn2_2 ssundif bitr3i syl6rbbr biimpd anim12d fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa pm4.72 sylib fssunsn2_1 fssunsn2_3 csn cun fssunsn2_0 wss fssunsn2_0 fssunsn2_2 fssunsn2_3 csn cun wss wa fssunsn2_1 fssunsn2_0 wss fssunsn2_0 fssunsn2_2 wss wa orcom syl6bb bitrd pm2.61i $.
$}
$( /* Possible values for a set sandwiched between another set and it plus a
       singleton.  (Contributed by Mario Carneiro, 2-Jul-2016.) */

$)
${
	fssunsn_0 $f class A $.
	fssunsn_1 $f class B $.
	fssunsn_2 $f class C $.
	ssunsn $p |- ( ( B C_ A /\ A C_ ( B u. { C } ) ) <-> ( A = B \/ A = ( B u. { C } ) ) ) $= fssunsn_1 fssunsn_0 wss fssunsn_0 fssunsn_1 fssunsn_2 csn cun wss wa fssunsn_1 fssunsn_0 wss fssunsn_0 fssunsn_1 wss wa fssunsn_1 fssunsn_2 csn cun fssunsn_0 wss fssunsn_0 fssunsn_1 fssunsn_2 csn cun wss wa wo fssunsn_0 fssunsn_1 wceq fssunsn_0 fssunsn_1 fssunsn_2 csn cun wceq wo fssunsn_0 fssunsn_1 fssunsn_1 fssunsn_2 ssunsn2 fssunsn_1 fssunsn_0 wss fssunsn_0 fssunsn_1 wss wa fssunsn_0 fssunsn_1 wceq fssunsn_1 fssunsn_2 csn cun fssunsn_0 wss fssunsn_0 fssunsn_1 fssunsn_2 csn cun wss wa fssunsn_0 fssunsn_1 fssunsn_2 csn cun wceq fssunsn_1 fssunsn_0 wss fssunsn_0 fssunsn_1 wss wa fssunsn_0 fssunsn_1 wss fssunsn_1 fssunsn_0 wss wa fssunsn_0 fssunsn_1 wceq fssunsn_1 fssunsn_0 wss fssunsn_0 fssunsn_1 wss ancom fssunsn_0 fssunsn_1 eqss bitr4i fssunsn_1 fssunsn_2 csn cun fssunsn_0 wss fssunsn_0 fssunsn_1 fssunsn_2 csn cun wss wa fssunsn_0 fssunsn_1 fssunsn_2 csn cun wss fssunsn_1 fssunsn_2 csn cun fssunsn_0 wss wa fssunsn_0 fssunsn_1 fssunsn_2 csn cun wceq fssunsn_1 fssunsn_2 csn cun fssunsn_0 wss fssunsn_0 fssunsn_1 fssunsn_2 csn cun wss ancom fssunsn_0 fssunsn_1 fssunsn_2 csn cun eqss bitr4i orbi12i bitri $.
$}
$( /* Two ways to express that a nonempty set equals a singleton.
       (Contributed by NM, 15-Dec-2007.) */

$)
${
	$d x A $.
	$d x B $.
	feqsn_0 $f set x $.
	feqsn_1 $f class A $.
	feqsn_2 $f class B $.
	eqsn $p |- ( A =/= (/) -> ( A = { B } <-> A. x e. A x = B ) ) $= feqsn_1 c0 wne feqsn_1 feqsn_2 csn wceq feqsn_1 feqsn_2 csn wss feqsn_0 sup_set_class feqsn_2 wceq feqsn_0 feqsn_1 wral feqsn_1 c0 wne feqsn_1 feqsn_2 csn wceq feqsn_1 feqsn_2 csn wss feqsn_1 feqsn_2 csn eqimss feqsn_1 feqsn_2 csn wss feqsn_1 c0 wne feqsn_1 feqsn_2 csn wceq feqsn_1 c0 wne feqsn_1 c0 wceq wn feqsn_1 feqsn_2 csn wss feqsn_1 feqsn_2 csn wceq feqsn_1 c0 df-ne feqsn_1 feqsn_2 csn wss feqsn_1 c0 wceq feqsn_1 feqsn_2 csn wceq feqsn_1 feqsn_2 csn wss feqsn_1 c0 wceq feqsn_1 feqsn_2 csn wceq wo feqsn_1 feqsn_2 sssn biimpi ord syl5bi com12 impbid2 feqsn_1 feqsn_2 csn wss feqsn_0 sup_set_class feqsn_2 csn wcel feqsn_0 feqsn_1 wral feqsn_0 sup_set_class feqsn_2 wceq feqsn_0 feqsn_1 wral feqsn_0 feqsn_1 feqsn_2 csn dfss3 feqsn_0 sup_set_class feqsn_2 csn wcel feqsn_0 sup_set_class feqsn_2 wceq feqsn_0 feqsn_1 feqsn_0 feqsn_2 elsn ralbii bitri syl6bb $.
$}
$( /* Possible values for a set sandwiched between another set and it plus a
       singleton.  (Contributed by Mario Carneiro, 2-Jul-2016.) */

$)
${
	fssunpr_0 $f class A $.
	fssunpr_1 $f class B $.
	fssunpr_2 $f class C $.
	fssunpr_3 $f class D $.
	ssunpr $p |- ( ( B C_ A /\ A C_ ( B u. { C , D } ) ) <-> ( ( A = B \/ A = ( B u. { C } ) ) \/ ( A = ( B u. { D } ) \/ A = ( B u. { C , D } ) ) ) ) $= fssunpr_1 fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun wss wa fssunpr_1 fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun wss wa fssunpr_1 fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun wss wa fssunpr_1 fssunpr_3 csn cun fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun wss wa wo fssunpr_0 fssunpr_1 wceq fssunpr_0 fssunpr_1 fssunpr_2 csn cun wceq wo fssunpr_0 fssunpr_1 fssunpr_3 csn cun wceq fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun wceq wo wo fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun wss fssunpr_1 fssunpr_0 wss fssunpr_1 fssunpr_2 fssunpr_3 cpr cun fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun fssunpr_1 fssunpr_2 csn fssunpr_3 csn cun cun fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun fssunpr_2 fssunpr_3 cpr fssunpr_2 csn fssunpr_3 csn cun fssunpr_1 fssunpr_2 fssunpr_3 df-pr uneq2i fssunpr_1 fssunpr_2 csn fssunpr_3 csn unass eqtr4i sseq2i anbi2i fssunpr_0 fssunpr_1 fssunpr_1 fssunpr_2 csn cun fssunpr_3 ssunsn2 fssunpr_1 fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun wss wa fssunpr_0 fssunpr_1 wceq fssunpr_0 fssunpr_1 fssunpr_2 csn cun wceq wo fssunpr_1 fssunpr_3 csn cun fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun wss wa fssunpr_0 fssunpr_1 fssunpr_3 csn cun wceq fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun wceq wo fssunpr_0 fssunpr_1 fssunpr_2 ssunsn fssunpr_1 fssunpr_3 csn cun fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun wss wa fssunpr_1 fssunpr_3 csn cun fssunpr_0 wss fssunpr_0 fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun wss wa fssunpr_0 fssunpr_1 fssunpr_3 csn cun wceq fssunpr_0 fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun wceq wo fssunpr_0 fssunpr_1 fssunpr_3 csn cun wceq fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun wceq wo fssunpr_0 fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun wss fssunpr_0 fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun wss fssunpr_1 fssunpr_3 csn cun fssunpr_0 wss fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun fssunpr_0 fssunpr_1 fssunpr_2 csn fssunpr_3 csn un23 sseq2i anbi2i fssunpr_0 fssunpr_1 fssunpr_3 csn cun fssunpr_2 ssunsn fssunpr_0 fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun wceq fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun wceq fssunpr_0 fssunpr_1 fssunpr_3 csn cun wceq fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun fssunpr_1 fssunpr_2 fssunpr_3 cpr cun fssunpr_0 fssunpr_1 fssunpr_2 fssunpr_3 cpr cun fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun fssunpr_1 fssunpr_3 csn cun fssunpr_2 csn cun fssunpr_1 fssunpr_2 fssunpr_3 cpr cun fssunpr_1 fssunpr_2 csn fssunpr_3 csn cun cun fssunpr_1 fssunpr_2 csn cun fssunpr_3 csn cun fssunpr_2 fssunpr_3 cpr fssunpr_2 csn fssunpr_3 csn cun fssunpr_1 fssunpr_2 fssunpr_3 df-pr uneq2i fssunpr_1 fssunpr_2 csn fssunpr_3 csn unass eqtr4i fssunpr_1 fssunpr_2 csn fssunpr_3 csn un23 eqtr2i eqeq2i orbi2i 3bitri orbi12i 3bitri $.
$}
$( /* The subsets of a pair.  (Contributed by NM, 16-Mar-2006.)  (Proof
       shortened by Mario Carneiro, 2-Jul-2016.) */

$)
${
	fsspr_0 $f class A $.
	fsspr_1 $f class B $.
	fsspr_2 $f class C $.
	sspr $p |- ( A C_ { B , C } <-> ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) ) $= fsspr_0 fsspr_1 fsspr_2 cpr wss c0 fsspr_0 wss fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wss wa fsspr_0 c0 wceq fsspr_0 c0 fsspr_1 csn cun wceq wo fsspr_0 c0 fsspr_2 csn cun wceq fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wceq wo wo fsspr_0 c0 wceq fsspr_0 fsspr_1 csn wceq wo fsspr_0 fsspr_2 csn wceq fsspr_0 fsspr_1 fsspr_2 cpr wceq wo wo fsspr_0 fsspr_1 fsspr_2 cpr wss fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wss c0 fsspr_0 wss fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wss wa c0 fsspr_1 fsspr_2 cpr cun fsspr_1 fsspr_2 cpr fsspr_0 c0 fsspr_1 fsspr_2 cpr cun fsspr_1 fsspr_2 cpr c0 cun fsspr_1 fsspr_2 cpr c0 fsspr_1 fsspr_2 cpr uncom fsspr_1 fsspr_2 cpr un0 eqtri sseq2i c0 fsspr_0 wss fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wss fsspr_0 0ss biantrur bitr3i fsspr_0 c0 fsspr_1 fsspr_2 ssunpr fsspr_0 c0 wceq fsspr_0 c0 fsspr_1 csn cun wceq wo fsspr_0 c0 wceq fsspr_0 fsspr_1 csn wceq wo fsspr_0 c0 fsspr_2 csn cun wceq fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wceq wo fsspr_0 fsspr_2 csn wceq fsspr_0 fsspr_1 fsspr_2 cpr wceq wo fsspr_0 c0 fsspr_1 csn cun wceq fsspr_0 fsspr_1 csn wceq fsspr_0 c0 wceq c0 fsspr_1 csn cun fsspr_1 csn fsspr_0 c0 fsspr_1 csn cun fsspr_1 csn c0 cun fsspr_1 csn c0 fsspr_1 csn uncom fsspr_1 csn un0 eqtri eqeq2i orbi2i fsspr_0 c0 fsspr_2 csn cun wceq fsspr_0 fsspr_2 csn wceq fsspr_0 c0 fsspr_1 fsspr_2 cpr cun wceq fsspr_0 fsspr_1 fsspr_2 cpr wceq c0 fsspr_2 csn cun fsspr_2 csn fsspr_0 c0 fsspr_2 csn cun fsspr_2 csn c0 cun fsspr_2 csn c0 fsspr_2 csn uncom fsspr_2 csn un0 eqtri eqeq2i c0 fsspr_1 fsspr_2 cpr cun fsspr_1 fsspr_2 cpr fsspr_0 c0 fsspr_1 fsspr_2 cpr cun fsspr_1 fsspr_2 cpr c0 cun fsspr_1 fsspr_2 cpr c0 fsspr_1 fsspr_2 cpr uncom fsspr_1 fsspr_2 cpr un0 eqtri eqeq2i orbi12i orbi12i 3bitri $.
$}
$( /* The subsets of a triple.  (Contributed by Mario Carneiro,
       2-Jul-2016.) */

$)
${
	fsstp_0 $f class A $.
	fsstp_1 $f class B $.
	fsstp_2 $f class C $.
	fsstp_3 $f class D $.
	sstp $p |- ( A C_ { B , C , D } <-> ( ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) \/ ( ( A = { D } \/ A = { B , D } ) \/ ( A = { C , D } \/ A = { B , C , D } ) ) ) ) $= fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss wa fsstp_0 c0 wceq fsstp_0 fsstp_1 csn wceq wo fsstp_0 fsstp_2 csn wceq fsstp_0 fsstp_1 fsstp_2 cpr wceq wo wo fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_1 fsstp_3 cpr wceq wo fsstp_0 fsstp_2 fsstp_3 cpr wceq fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wceq wo wo wo fsstp_1 fsstp_2 fsstp_3 ctp fsstp_1 fsstp_2 cpr fsstp_3 csn cun fsstp_0 fsstp_1 fsstp_2 fsstp_3 df-tp sseq2i c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss fsstp_0 0ss biantrur c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss wa c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr wss wa c0 fsstp_3 csn cun fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss wa wo fsstp_0 c0 wceq fsstp_0 fsstp_1 csn wceq wo fsstp_0 fsstp_2 csn wceq fsstp_0 fsstp_1 fsstp_2 cpr wceq wo wo fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_1 fsstp_3 cpr wceq wo fsstp_0 fsstp_2 fsstp_3 cpr wceq fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wceq wo wo wo fsstp_0 c0 fsstp_1 fsstp_2 cpr fsstp_3 ssunsn2 c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr wss wa fsstp_0 c0 wceq fsstp_0 fsstp_1 csn wceq wo fsstp_0 fsstp_2 csn wceq fsstp_0 fsstp_1 fsstp_2 cpr wceq wo wo c0 fsstp_3 csn cun fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss wa fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_1 fsstp_3 cpr wceq wo fsstp_0 fsstp_2 fsstp_3 cpr wceq fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wceq wo wo c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr wss wa fsstp_0 fsstp_1 fsstp_2 cpr wss fsstp_0 c0 wceq fsstp_0 fsstp_1 csn wceq wo fsstp_0 fsstp_2 csn wceq fsstp_0 fsstp_1 fsstp_2 cpr wceq wo wo c0 fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr wss fsstp_0 0ss biantrur fsstp_0 fsstp_1 fsstp_2 sspr bitr3i c0 fsstp_3 csn cun fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss wa fsstp_3 csn fsstp_0 wss fsstp_0 fsstp_3 csn fsstp_1 fsstp_2 cpr cun wss wa fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_3 csn fsstp_1 csn cun wceq wo fsstp_0 fsstp_3 csn fsstp_2 csn cun wceq fsstp_0 fsstp_3 csn fsstp_1 fsstp_2 cpr cun wceq wo wo fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_1 fsstp_3 cpr wceq wo fsstp_0 fsstp_2 fsstp_3 cpr wceq fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wceq wo wo c0 fsstp_3 csn cun fsstp_0 wss fsstp_3 csn fsstp_0 wss fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn cun wss fsstp_0 fsstp_3 csn fsstp_1 fsstp_2 cpr cun wss c0 fsstp_3 csn cun fsstp_3 csn fsstp_0 c0 fsstp_3 csn cun fsstp_3 csn c0 cun fsstp_3 csn c0 fsstp_3 csn uncom fsstp_3 csn un0 eqtri sseq1i fsstp_1 fsstp_2 cpr fsstp_3 csn cun fsstp_3 csn fsstp_1 fsstp_2 cpr cun fsstp_0 fsstp_1 fsstp_2 cpr fsstp_3 csn uncom sseq2i anbi12i fsstp_0 fsstp_3 csn fsstp_1 fsstp_2 ssunpr fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_3 csn fsstp_1 csn cun wceq wo fsstp_0 fsstp_3 csn wceq fsstp_0 fsstp_1 fsstp_3 cpr wceq wo fsstp_0 fsstp_3 csn fsstp_2 csn cun wceq fsstp_0 fsstp_3 csn fsstp_1 fsstp_2 cpr cun wceq wo fsstp_0 fsstp_2 fsstp_3 cpr wceq fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wceq wo fsstp_0 fsstp_3 csn fsstp_1 csn cun wceq fsstp_0 fsstp_1 fsstp_3 cpr wceq fsstp_0 fsstp_3 csn wceq fsstp_3 csn fsstp_1 csn cun fsstp_1 fsstp_3 cpr fsstp_0 fsstp_3 csn fsstp_1 csn cun fsstp_1 csn fsstp_3 csn cun fsstp_1 fsstp_3 cpr fsstp_3 csn fsstp_1 csn uncom fsstp_1 fsstp_3 df-pr eqtr4i eqeq2i orbi2i fsstp_0 fsstp_3 csn fsstp_2 csn cun wceq fsstp_0 fsstp_2 fsstp_3 cpr wceq fsstp_0 fsstp_3 csn fsstp_1 fsstp_2 cpr cun wceq fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp wceq fsstp_3 csn fsstp_2 csn cun fsstp_2 fsstp_3 cpr fsstp_0 fsstp_3 csn fsstp_2 csn cun fsstp_2 csn fsstp_3 csn cun fsstp_2 fsstp_3 cpr fsstp_3 csn fsstp_2 csn uncom fsstp_2 fsstp_3 df-pr eqtr4i eqeq2i fsstp_3 csn fsstp_1 fsstp_2 cpr cun fsstp_1 fsstp_2 fsstp_3 ctp fsstp_0 fsstp_1 fsstp_2 fsstp_3 ctp fsstp_1 fsstp_2 cpr fsstp_3 csn cun fsstp_3 csn fsstp_1 fsstp_2 cpr cun fsstp_1 fsstp_2 fsstp_3 df-tp fsstp_1 fsstp_2 cpr fsstp_3 csn uncom eqtr2i eqeq2i orbi12i orbi12i 3bitri orbi12i bitri 3bitri $.
$}
$( /* A triplet of elements of a class is a subset of the class.  (Contributed
       by NM, 9-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	ftpss_0 $f class A $.
	ftpss_1 $f class B $.
	ftpss_2 $f class C $.
	ftpss_3 $f class D $.
	etpss_0 $e |- A e. _V $.
	etpss_1 $e |- B e. _V $.
	etpss_2 $e |- C e. _V $.
	tpss $p |- ( ( A e. D /\ B e. D /\ C e. D ) <-> { A , B , C } C_ D ) $= ftpss_0 ftpss_1 cpr ftpss_3 wss ftpss_2 csn ftpss_3 wss wa ftpss_0 ftpss_1 cpr ftpss_2 csn cun ftpss_3 wss ftpss_0 ftpss_3 wcel ftpss_1 ftpss_3 wcel ftpss_2 ftpss_3 wcel w3a ftpss_0 ftpss_1 ftpss_2 ctp ftpss_3 wss ftpss_0 ftpss_1 cpr ftpss_2 csn ftpss_3 unss ftpss_0 ftpss_3 wcel ftpss_1 ftpss_3 wcel ftpss_2 ftpss_3 wcel w3a ftpss_0 ftpss_3 wcel ftpss_1 ftpss_3 wcel wa ftpss_2 ftpss_3 wcel wa ftpss_0 ftpss_1 cpr ftpss_3 wss ftpss_2 csn ftpss_3 wss wa ftpss_0 ftpss_3 wcel ftpss_1 ftpss_3 wcel ftpss_2 ftpss_3 wcel df-3an ftpss_0 ftpss_3 wcel ftpss_1 ftpss_3 wcel wa ftpss_0 ftpss_1 cpr ftpss_3 wss ftpss_2 ftpss_3 wcel ftpss_2 csn ftpss_3 wss ftpss_0 ftpss_1 ftpss_3 etpss_0 etpss_1 prss ftpss_2 ftpss_3 etpss_2 snss anbi12i bitri ftpss_0 ftpss_1 ftpss_2 ctp ftpss_0 ftpss_1 cpr ftpss_2 csn cun ftpss_3 ftpss_0 ftpss_1 ftpss_2 df-tp sseq1i 3bitr4i $.
$}
$( /* If the singletons of two sets are equal, the two sets are equal.  Part
       of Exercise 4 of [TakeutiZaring] p. 15.  (Contributed by NM,
       27-Aug-1993.) */

$)
${
	fsneqr_0 $f class A $.
	fsneqr_1 $f class B $.
	esneqr_0 $e |- A e. _V $.
	sneqr $p |- ( { A } = { B } -> A = B ) $= fsneqr_0 csn fsneqr_1 csn wceq fsneqr_0 fsneqr_1 csn wcel fsneqr_0 fsneqr_1 wceq fsneqr_0 csn fsneqr_1 csn wceq fsneqr_0 fsneqr_0 csn wcel fsneqr_0 fsneqr_1 csn wcel fsneqr_0 esneqr_0 snid fsneqr_0 csn fsneqr_1 csn fsneqr_0 eleq2 mpbii fsneqr_0 fsneqr_1 esneqr_0 elsnc sylib $.
$}
$( /* If a singleton is a subset of another, their members are equal.
       (Contributed by NM, 28-May-2006.) */

$)
${
	fsnsssn_0 $f class A $.
	fsnsssn_1 $f class B $.
	esnsssn_0 $e |- A e. _V $.
	snsssn $p |- ( { A } C_ { B } -> A = B ) $= fsnsssn_0 csn fsnsssn_1 csn wss fsnsssn_0 csn c0 wceq fsnsssn_0 csn fsnsssn_1 csn wceq wo fsnsssn_0 fsnsssn_1 wceq fsnsssn_0 csn fsnsssn_1 sssn fsnsssn_0 csn c0 wceq fsnsssn_0 fsnsssn_1 wceq fsnsssn_0 csn fsnsssn_1 csn wceq fsnsssn_0 csn c0 wceq fsnsssn_0 fsnsssn_1 wceq fsnsssn_0 csn c0 wne fsnsssn_0 csn c0 wceq wn fsnsssn_0 esnsssn_0 snnz fsnsssn_0 csn c0 df-ne mpbi pm2.21i fsnsssn_0 fsnsssn_1 esnsssn_0 sneqr jaoi sylbi $.
$}
$( /* Closed form of ~ sneqr .  (Contributed by Scott Fenton, 1-Apr-2011.) */

$)
${
	$d x A $.
	$d x B $.
	isneqrg_0 $f set x $.
	fsneqrg_0 $f class A $.
	fsneqrg_1 $f class B $.
	fsneqrg_2 $f class V $.
	sneqrg $p |- ( A e. V -> ( { A } = { B } -> A = B ) ) $= isneqrg_0 sup_set_class csn fsneqrg_1 csn wceq isneqrg_0 sup_set_class fsneqrg_1 wceq wi fsneqrg_0 csn fsneqrg_1 csn wceq fsneqrg_0 fsneqrg_1 wceq wi isneqrg_0 fsneqrg_0 fsneqrg_2 isneqrg_0 sup_set_class fsneqrg_0 wceq isneqrg_0 sup_set_class csn fsneqrg_1 csn wceq fsneqrg_0 csn fsneqrg_1 csn wceq isneqrg_0 sup_set_class fsneqrg_1 wceq fsneqrg_0 fsneqrg_1 wceq isneqrg_0 sup_set_class fsneqrg_0 wceq isneqrg_0 sup_set_class csn fsneqrg_0 csn fsneqrg_1 csn isneqrg_0 sup_set_class fsneqrg_0 sneq eqeq1d isneqrg_0 sup_set_class fsneqrg_0 fsneqrg_1 eqeq1 imbi12d isneqrg_0 sup_set_class fsneqrg_1 isneqrg_0 vex sneqr vtoclg $.
$}
$( /* Two singletons of sets are equal iff their elements are equal.
     (Contributed by Scott Fenton, 16-Apr-2012.) */

$)
${
	fsneqbg_0 $f class A $.
	fsneqbg_1 $f class B $.
	fsneqbg_2 $f class V $.
	sneqbg $p |- ( A e. V -> ( { A } = { B } <-> A = B ) ) $= fsneqbg_0 fsneqbg_2 wcel fsneqbg_0 csn fsneqbg_1 csn wceq fsneqbg_0 fsneqbg_1 wceq fsneqbg_0 fsneqbg_1 fsneqbg_2 sneqrg fsneqbg_0 fsneqbg_1 sneq impbid1 $.
$}
$( /* The singleton of a class is a subset of its power class.  (Contributed
       by NM, 5-Aug-1993.) */

$)
${
	$d x A $.
	isnsspw_0 $f set x $.
	fsnsspw_0 $f class A $.
	snsspw $p |- { A } C_ ~P A $= isnsspw_0 fsnsspw_0 csn fsnsspw_0 cpw isnsspw_0 sup_set_class fsnsspw_0 wceq isnsspw_0 sup_set_class fsnsspw_0 wss isnsspw_0 sup_set_class fsnsspw_0 csn wcel isnsspw_0 sup_set_class fsnsspw_0 cpw wcel isnsspw_0 sup_set_class fsnsspw_0 eqimss isnsspw_0 fsnsspw_0 elsn isnsspw_0 sup_set_class fsnsspw_0 wss isnsspw_0 fsnsspw_0 cpw isnsspw_0 fsnsspw_0 df-pw abeq2i 3imtr4i ssriv $.
$}
$( /* An unordered pair belongs to the power class of a class iff each member
       belongs to the class.  (Contributed by NM, 10-Dec-2003.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	fprsspw_0 $f class A $.
	fprsspw_1 $f class B $.
	fprsspw_2 $f class C $.
	eprsspw_0 $e |- A e. _V $.
	eprsspw_1 $e |- B e. _V $.
	prsspw $p |- ( { A , B } C_ ~P C <-> ( A C_ C /\ B C_ C ) ) $= fprsspw_0 fprsspw_1 cpr fprsspw_2 cpw wss fprsspw_0 fprsspw_2 cpw wcel fprsspw_1 fprsspw_2 cpw wcel wa fprsspw_0 fprsspw_2 wss fprsspw_1 fprsspw_2 wss wa fprsspw_0 fprsspw_1 fprsspw_2 cpw eprsspw_0 eprsspw_1 prss fprsspw_0 fprsspw_2 cpw wcel fprsspw_0 fprsspw_2 wss fprsspw_1 fprsspw_2 cpw wcel fprsspw_1 fprsspw_2 wss fprsspw_0 fprsspw_2 eprsspw_0 elpw fprsspw_1 fprsspw_2 eprsspw_1 elpw anbi12i bitr3i $.
$}
$( /* Reverse equality lemma for unordered pairs.  If two unordered pairs have
       the same second element, the first elements are equal.  (Contributed by
       NM, 18-Oct-1995.) */

$)
${
	fpreqr1_0 $f class A $.
	fpreqr1_1 $f class B $.
	fpreqr1_2 $f class C $.
	epreqr1_0 $e |- A e. _V $.
	epreqr1_1 $e |- B e. _V $.
	preqr1 $p |- ( { A , C } = { B , C } -> A = B ) $= fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr wceq fpreqr1_0 fpreqr1_1 wceq fpreqr1_0 fpreqr1_2 wceq fpreqr1_1 fpreqr1_0 wceq fpreqr1_1 fpreqr1_2 wceq fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr wceq fpreqr1_0 fpreqr1_1 fpreqr1_2 cpr wcel fpreqr1_0 fpreqr1_1 wceq fpreqr1_0 fpreqr1_2 wceq wo fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr wceq fpreqr1_0 fpreqr1_0 fpreqr1_2 cpr wcel fpreqr1_0 fpreqr1_1 fpreqr1_2 cpr wcel fpreqr1_0 fpreqr1_2 epreqr1_0 prid1 fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr fpreqr1_0 eleq2 mpbii fpreqr1_0 fpreqr1_1 fpreqr1_2 epreqr1_0 elpr sylib fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr wceq fpreqr1_1 fpreqr1_0 fpreqr1_2 cpr wcel fpreqr1_1 fpreqr1_0 wceq fpreqr1_1 fpreqr1_2 wceq wo fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr wceq fpreqr1_1 fpreqr1_0 fpreqr1_2 cpr wcel fpreqr1_1 fpreqr1_1 fpreqr1_2 cpr wcel fpreqr1_1 fpreqr1_2 epreqr1_1 prid1 fpreqr1_0 fpreqr1_2 cpr fpreqr1_1 fpreqr1_2 cpr fpreqr1_1 eleq2 mpbiri fpreqr1_1 fpreqr1_0 fpreqr1_2 epreqr1_1 elpr sylib fpreqr1_0 fpreqr1_1 eqcom fpreqr1_0 fpreqr1_2 fpreqr1_1 eqeq2 oplem1 $.
$}
$( /* Reverse equality lemma for unordered pairs.  If two unordered pairs have
       the same first element, the second elements are equal.  (Contributed by
       NM, 5-Aug-1993.) */

$)
${
	fpreqr2_0 $f class A $.
	fpreqr2_1 $f class B $.
	fpreqr2_2 $f class C $.
	epreqr2_0 $e |- A e. _V $.
	epreqr2_1 $e |- B e. _V $.
	preqr2 $p |- ( { C , A } = { C , B } -> A = B ) $= fpreqr2_2 fpreqr2_0 cpr fpreqr2_2 fpreqr2_1 cpr wceq fpreqr2_0 fpreqr2_2 cpr fpreqr2_1 fpreqr2_2 cpr wceq fpreqr2_0 fpreqr2_1 wceq fpreqr2_2 fpreqr2_0 cpr fpreqr2_0 fpreqr2_2 cpr fpreqr2_2 fpreqr2_1 cpr fpreqr2_1 fpreqr2_2 cpr fpreqr2_2 fpreqr2_0 prcom fpreqr2_2 fpreqr2_1 prcom eqeq12i fpreqr2_0 fpreqr2_1 fpreqr2_2 epreqr2_0 epreqr2_1 preqr1 sylbi $.
$}
$( /* Equality relationship for two unordered pairs.  (Contributed by NM,
       17-Oct-1996.) */

$)
${
	fpreq12b_0 $f class A $.
	fpreq12b_1 $f class B $.
	fpreq12b_2 $f class C $.
	fpreq12b_3 $f class D $.
	epreq12b_0 $e |- A e. _V $.
	epreq12b_1 $e |- B e. _V $.
	epreq12b_2 $e |- C e. _V $.
	epreq12b_3 $e |- D e. _V $.
	preq12b $p |- ( { A , B } = { C , D } <-> ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) $= fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_1 fpreq12b_3 wceq wa fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq wa wo fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_0 fpreq12b_3 wceq wo fpreq12b_0 fpreq12b_2 wceq fpreq12b_1 fpreq12b_3 wceq wa fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq wa wo fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_2 fpreq12b_3 cpr wcel fpreq12b_0 fpreq12b_2 wceq fpreq12b_0 fpreq12b_3 wceq wo fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_0 fpreq12b_1 cpr wcel fpreq12b_0 fpreq12b_2 fpreq12b_3 cpr wcel fpreq12b_0 fpreq12b_1 epreq12b_0 prid1 fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr fpreq12b_0 eleq2 mpbii fpreq12b_0 fpreq12b_2 fpreq12b_3 epreq12b_0 elpr sylib fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_1 fpreq12b_3 wceq wa fpreq12b_0 fpreq12b_3 wceq fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq wa fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_1 fpreq12b_3 wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_1 fpreq12b_3 wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_2 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_1 fpreq12b_3 wceq fpreq12b_0 fpreq12b_2 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr fpreq12b_0 fpreq12b_2 fpreq12b_1 preq1 eqeq1d fpreq12b_1 fpreq12b_3 fpreq12b_2 epreq12b_1 epreq12b_3 preqr2 syl6bi com12 ancld fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_3 fpreq12b_2 cpr wceq fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq wi fpreq12b_2 fpreq12b_3 cpr fpreq12b_3 fpreq12b_2 cpr fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 prcom eqeq2i fpreq12b_0 fpreq12b_3 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_3 fpreq12b_2 cpr wceq fpreq12b_1 fpreq12b_2 wceq fpreq12b_0 fpreq12b_3 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_3 fpreq12b_2 cpr wceq fpreq12b_3 fpreq12b_1 cpr fpreq12b_3 fpreq12b_2 cpr wceq fpreq12b_1 fpreq12b_2 wceq fpreq12b_0 fpreq12b_3 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_3 fpreq12b_1 cpr fpreq12b_3 fpreq12b_2 cpr fpreq12b_0 fpreq12b_3 fpreq12b_1 preq1 eqeq1d fpreq12b_1 fpreq12b_2 fpreq12b_3 epreq12b_1 epreq12b_2 preqr2 syl6bi com12 sylbi ancld orim12d mpd fpreq12b_0 fpreq12b_2 wceq fpreq12b_1 fpreq12b_3 wceq wa fpreq12b_0 fpreq12b_1 cpr fpreq12b_2 fpreq12b_3 cpr wceq fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq wa fpreq12b_0 fpreq12b_1 fpreq12b_2 fpreq12b_3 preq12 fpreq12b_0 fpreq12b_3 wceq fpreq12b_1 fpreq12b_2 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_1 fpreq12b_3 cpr fpreq12b_2 fpreq12b_3 cpr fpreq12b_0 fpreq12b_3 wceq fpreq12b_0 fpreq12b_1 cpr fpreq12b_3 fpreq12b_1 cpr fpreq12b_1 fpreq12b_3 cpr fpreq12b_0 fpreq12b_3 fpreq12b_1 preq1 fpreq12b_3 fpreq12b_1 prcom syl6eq fpreq12b_1 fpreq12b_2 fpreq12b_3 preq1 sylan9eq jaoi impbii $.
$}
$( /* Equality of two unordered pairs.  (Contributed by NM, 17-Oct-1996.) */

$)
${
	fprel12_0 $f class A $.
	fprel12_1 $f class B $.
	fprel12_2 $f class C $.
	fprel12_3 $f class D $.
	eprel12_0 $e |- A e. _V $.
	eprel12_1 $e |- B e. _V $.
	eprel12_2 $e |- C e. _V $.
	eprel12_3 $e |- D e. _V $.
	prel12 $p |- ( -. A = B -> ( { A , B } = { C , D } <-> ( A e. { C , D } /\ B e. { C , D } ) ) ) $= fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq fprel12_0 fprel12_2 fprel12_3 cpr wcel fprel12_1 fprel12_2 fprel12_3 cpr wcel wa fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq fprel12_0 fprel12_2 fprel12_3 cpr wcel fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq fprel12_0 fprel12_0 fprel12_1 cpr wcel fprel12_0 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 eprel12_0 prid1 fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr fprel12_0 eleq2 mpbii fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq fprel12_1 fprel12_0 fprel12_1 cpr wcel fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 eprel12_1 prid2 fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr fprel12_1 eleq2 mpbii jca fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 fprel12_3 cpr wcel fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq fprel12_0 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_0 fprel12_1 wceq wn fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq wi fprel12_0 fprel12_2 fprel12_3 eprel12_0 elpr fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq wi fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo wa fprel12_1 fprel12_3 wceq fprel12_1 fprel12_2 wceq wo fprel12_0 fprel12_2 wceq fprel12_1 fprel12_3 wceq wa fprel12_0 fprel12_3 wceq fprel12_1 fprel12_2 wceq wa wo fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_0 fprel12_1 cpr fprel12_2 fprel12_3 cpr wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo wa fprel12_1 fprel12_3 wceq fprel12_0 fprel12_2 wceq fprel12_1 fprel12_3 wceq wa fprel12_1 fprel12_2 wceq fprel12_0 fprel12_3 wceq fprel12_1 fprel12_2 wceq wa fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo wa fprel12_1 fprel12_3 wceq fprel12_0 fprel12_2 wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_1 fprel12_3 wceq fprel12_0 fprel12_2 wceq wi fprel12_1 fprel12_3 wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_0 fprel12_2 wceq fprel12_1 fprel12_3 wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_3 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_0 fprel12_2 wceq wi fprel12_1 fprel12_3 wceq fprel12_0 fprel12_1 wceq fprel12_0 fprel12_3 wceq fprel12_1 fprel12_3 fprel12_0 eqeq2 notbid fprel12_0 fprel12_3 wceq fprel12_0 fprel12_2 wceq orel2 syl6bi com3l imp ancrd fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo wa fprel12_1 fprel12_2 wceq fprel12_0 fprel12_3 wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_1 fprel12_2 wceq fprel12_0 fprel12_3 wceq wi fprel12_1 fprel12_2 wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_0 fprel12_3 wceq fprel12_1 fprel12_2 wceq fprel12_0 fprel12_1 wceq wn fprel12_0 fprel12_2 wceq wn fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq wo fprel12_0 fprel12_3 wceq wi fprel12_1 fprel12_2 wceq fprel12_0 fprel12_1 wceq fprel12_0 fprel12_2 wceq fprel12_1 fprel12_2 fprel12_0 eqeq2 notbid fprel12_0 fprel12_2 wceq fprel12_0 fprel12_3 wceq orel1 syl6bi com3l imp ancrd orim12d fprel12_1 fprel12_2 fprel12_3 cpr wcel fprel12_1 fprel12_2 wceq fprel12_1 fprel12_3 wceq wo fprel12_1 fprel12_3 wceq fprel12_1 fprel12_2 wceq wo fprel12_1 fprel12_2 fprel12_3 eprel12_1 elpr fprel12_1 fprel12_2 wceq fprel12_1 fprel12_3 wceq orcom bitri fprel12_0 fprel12_1 fprel12_2 fprel12_3 eprel12_0 eprel12_1 eprel12_2 eprel12_3 preq12b 3imtr4g ex syl5bi imp3a impbid2 $.
$}
$( /* A way to represent ordered pairs using unordered pairs with distinct
       members.  (Contributed by NM, 27-Mar-2007.) */

$)
${
	fopthpr_0 $f class A $.
	fopthpr_1 $f class B $.
	fopthpr_2 $f class C $.
	fopthpr_3 $f class D $.
	eopthpr_0 $e |- A e. _V $.
	eopthpr_1 $e |- B e. _V $.
	eopthpr_2 $e |- C e. _V $.
	eopthpr_3 $e |- D e. _V $.
	opthpr $p |- ( A =/= D -> ( { A , B } = { C , D } <-> ( A = C /\ B = D ) ) ) $= fopthpr_0 fopthpr_1 cpr fopthpr_2 fopthpr_3 cpr wceq fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq wa wo fopthpr_0 fopthpr_3 wne fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_1 fopthpr_2 fopthpr_3 eopthpr_0 eopthpr_1 eopthpr_2 eopthpr_3 preq12b fopthpr_0 fopthpr_3 wne fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq wa wo fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_3 wne fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq wa fopthpr_0 fopthpr_3 wne fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa idd fopthpr_0 fopthpr_3 wne fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_3 wne fopthpr_0 fopthpr_3 wceq wn fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa wi wi fopthpr_0 fopthpr_3 df-ne fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa wi pm2.21 sylbi imp3a jaod fopthpr_0 fopthpr_2 wceq fopthpr_1 fopthpr_3 wceq wa fopthpr_0 fopthpr_3 wceq fopthpr_1 fopthpr_2 wceq wa orc impbid1 syl5bb $.
$}
$( /* Closed form of ~ preq12b .  (Contributed by Scott Fenton,
       28-Mar-2014.) */

$)
$v Y $.
${
	$d A x y z w $.
	$d B x y z w $.
	$d C x y z w $.
	$d D x y z w $.
	$d V x y z w $.
	$d W x y z w $.
	$d X x y z w $.
	$d Y x y z w $.
	ipreq12bg_0 $f set x $.
	ipreq12bg_1 $f set y $.
	ipreq12bg_2 $f set z $.
	ipreq12bg_3 $f set w $.
	fpreq12bg_0 $f class A $.
	fpreq12bg_1 $f class B $.
	fpreq12bg_2 $f class C $.
	fpreq12bg_3 $f class D $.
	fpreq12bg_4 $f class V $.
	fpreq12bg_5 $f class W $.
	fpreq12bg_6 $f class X $.
	fpreq12bg_7 $f class Y $.
	preq12bg $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) -> ( { A , B } = { C , D } <-> ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) ) $= fpreq12bg_0 fpreq12bg_4 wcel fpreq12bg_1 fpreq12bg_5 wcel wa fpreq12bg_2 fpreq12bg_6 wcel fpreq12bg_3 fpreq12bg_7 wcel fpreq12bg_0 fpreq12bg_1 cpr fpreq12bg_2 fpreq12bg_3 cpr wceq fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_2 wceq wa wo wb fpreq12bg_0 fpreq12bg_4 wcel fpreq12bg_1 fpreq12bg_5 wcel fpreq12bg_2 fpreq12bg_6 wcel fpreq12bg_3 fpreq12bg_7 wcel fpreq12bg_0 fpreq12bg_1 cpr fpreq12bg_2 fpreq12bg_3 cpr wceq fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_2 wceq wa wo wb wi fpreq12bg_3 fpreq12bg_7 wcel ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo wb wi fpreq12bg_3 fpreq12bg_7 wcel fpreq12bg_0 ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo wb wi fpreq12bg_3 fpreq12bg_7 wcel fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa wo wb wi fpreq12bg_3 fpreq12bg_7 wcel fpreq12bg_0 fpreq12bg_1 cpr fpreq12bg_2 fpreq12bg_3 cpr wceq fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_2 wceq wa wo wb wi ipreq12bg_0 ipreq12bg_1 ipreq12bg_2 fpreq12bg_0 fpreq12bg_1 fpreq12bg_2 fpreq12bg_4 fpreq12bg_5 fpreq12bg_6 ipreq12bg_0 sup_set_class fpreq12bg_0 wceq ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo wb fpreq12bg_0 ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo wb fpreq12bg_3 fpreq12bg_7 wcel ipreq12bg_0 sup_set_class fpreq12bg_0 wceq ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo ipreq12bg_0 sup_set_class fpreq12bg_0 wceq ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr fpreq12bg_0 ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr ipreq12bg_0 sup_set_class fpreq12bg_0 ipreq12bg_1 sup_set_class preq1 eqeq1d ipreq12bg_0 sup_set_class fpreq12bg_0 wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa ipreq12bg_0 sup_set_class fpreq12bg_0 wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq ipreq12bg_0 sup_set_class fpreq12bg_0 ipreq12bg_2 sup_set_class eqeq1 anbi1d ipreq12bg_0 sup_set_class fpreq12bg_0 wceq ipreq12bg_0 sup_set_class fpreq12bg_3 wceq fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_0 sup_set_class fpreq12bg_0 fpreq12bg_3 eqeq1 anbi1d orbi12d bibi12d imbi2d ipreq12bg_1 sup_set_class fpreq12bg_1 wceq fpreq12bg_0 ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo wb fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa wo wb fpreq12bg_3 fpreq12bg_7 wcel ipreq12bg_1 sup_set_class fpreq12bg_1 wceq fpreq12bg_0 ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa wo ipreq12bg_1 sup_set_class fpreq12bg_1 wceq fpreq12bg_0 ipreq12bg_1 sup_set_class cpr fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr ipreq12bg_1 sup_set_class fpreq12bg_1 fpreq12bg_0 preq2 eqeq1d ipreq12bg_1 sup_set_class fpreq12bg_1 wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa ipreq12bg_1 sup_set_class fpreq12bg_1 wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_3 wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_1 fpreq12bg_3 eqeq1 anbi2d ipreq12bg_1 sup_set_class fpreq12bg_1 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_1 sup_set_class fpreq12bg_1 ipreq12bg_2 sup_set_class eqeq1 anbi2d orbi12d bibi12d imbi2d ipreq12bg_2 sup_set_class fpreq12bg_2 wceq fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa wo wb fpreq12bg_0 fpreq12bg_1 cpr fpreq12bg_2 fpreq12bg_3 cpr wceq fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_2 wceq wa wo wb fpreq12bg_3 fpreq12bg_7 wcel ipreq12bg_2 sup_set_class fpreq12bg_2 wceq fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq fpreq12bg_0 fpreq12bg_1 cpr fpreq12bg_2 fpreq12bg_3 cpr wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa wo fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_2 wceq wa wo ipreq12bg_2 sup_set_class fpreq12bg_2 wceq ipreq12bg_2 sup_set_class fpreq12bg_3 cpr fpreq12bg_2 fpreq12bg_3 cpr fpreq12bg_0 fpreq12bg_1 cpr ipreq12bg_2 sup_set_class fpreq12bg_2 fpreq12bg_3 preq1 eqeq2d ipreq12bg_2 sup_set_class fpreq12bg_2 wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq wa fpreq12bg_0 fpreq12bg_3 wceq fpreq12bg_1 fpreq12bg_2 wceq wa ipreq12bg_2 sup_set_class fpreq12bg_2 wceq fpreq12bg_0 ipreq12bg_2 sup_set_class wceq fpreq12bg_0 fpreq12bg_2 wceq fpreq12bg_1 fpreq12bg_3 wceq ipreq12bg_2 sup_set_class fpreq12bg_2 fpreq12bg_0 eqeq2 anbi1d ipreq12bg_2 sup_set_class fpreq12bg_2 wceq fpreq12bg_1 ipreq12bg_2 sup_set_class wceq fpreq12bg_1 fpreq12bg_2 wceq fpreq12bg_0 fpreq12bg_3 wceq ipreq12bg_2 sup_set_class fpreq12bg_2 fpreq12bg_1 eqeq2 anbi2d orbi12d bibi12d imbi2d fpreq12bg_3 fpreq12bg_7 wcel ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo wb wi ipreq12bg_0 sup_set_class fpreq12bg_4 wcel ipreq12bg_1 sup_set_class fpreq12bg_5 wcel ipreq12bg_2 sup_set_class fpreq12bg_6 wcel w3a ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class ipreq12bg_3 sup_set_class cpr wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class ipreq12bg_3 sup_set_class wceq wa ipreq12bg_0 sup_set_class ipreq12bg_3 sup_set_class wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa wo ipreq12bg_3 fpreq12bg_3 fpreq12bg_7 ipreq12bg_3 sup_set_class fpreq12bg_3 wceq ipreq12bg_2 sup_set_class ipreq12bg_3 sup_set_class cpr ipreq12bg_2 sup_set_class fpreq12bg_3 cpr ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class cpr ipreq12bg_3 sup_set_class fpreq12bg_3 ipreq12bg_2 sup_set_class preq2 eqeq2d ipreq12bg_3 sup_set_class fpreq12bg_3 wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class ipreq12bg_3 sup_set_class wceq wa ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq wa ipreq12bg_0 sup_set_class ipreq12bg_3 sup_set_class wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq wa ipreq12bg_3 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_3 sup_set_class wceq ipreq12bg_1 sup_set_class fpreq12bg_3 wceq ipreq12bg_0 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_3 sup_set_class fpreq12bg_3 ipreq12bg_1 sup_set_class eqeq2 anbi2d ipreq12bg_3 sup_set_class fpreq12bg_3 wceq ipreq12bg_0 sup_set_class ipreq12bg_3 sup_set_class wceq ipreq12bg_0 sup_set_class fpreq12bg_3 wceq ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class wceq ipreq12bg_3 sup_set_class fpreq12bg_3 ipreq12bg_0 sup_set_class eqeq2 anbi1d orbi12d ipreq12bg_0 sup_set_class ipreq12bg_1 sup_set_class ipreq12bg_2 sup_set_class ipreq12bg_3 sup_set_class ipreq12bg_0 vex ipreq12bg_1 vex ipreq12bg_2 vex ipreq12bg_3 vex preq12b vtoclbg a1i vtocl3ga 3expa impr $.
$}
$( /* Equivalence for a pair equal to a singleton.  (Contributed by NM,
       3-Jun-2008.) */

$)
${
	fpreqsn_0 $f class A $.
	fpreqsn_1 $f class B $.
	fpreqsn_2 $f class C $.
	epreqsn_0 $e |- A e. _V $.
	epreqsn_1 $e |- B e. _V $.
	epreqsn_2 $e |- C e. _V $.
	preqsn $p |- ( { A , B } = { C } <-> ( A = B /\ B = C ) ) $= fpreqsn_0 fpreqsn_1 cpr fpreqsn_2 csn wceq fpreqsn_0 fpreqsn_1 cpr fpreqsn_2 fpreqsn_2 cpr wceq fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_2 csn fpreqsn_2 fpreqsn_2 cpr fpreqsn_0 fpreqsn_1 cpr fpreqsn_2 dfsn2 eqeq2i fpreqsn_0 fpreqsn_1 cpr fpreqsn_2 fpreqsn_2 cpr wceq fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa wo fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_1 fpreqsn_2 fpreqsn_2 epreqsn_0 epreqsn_1 epreqsn_2 epreqsn_2 preq12b fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa wo fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa oridm fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq fpreqsn_0 fpreqsn_1 fpreqsn_2 eqtr3 fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq simpr jca fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq wa fpreqsn_0 fpreqsn_2 wceq fpreqsn_1 fpreqsn_2 wceq fpreqsn_0 fpreqsn_1 fpreqsn_2 eqtr fpreqsn_0 fpreqsn_1 wceq fpreqsn_1 fpreqsn_2 wceq simpr jca impbii bitri bitri bitri $.
$}
$( /* Rewrite ~ df-op using ` if ` .  When both arguments are sets, it reduces
       to the standard Kuratowski definition; otherwise, it is defined to be
       the empty set.  (Contributed by Mario Carneiro, 26-Apr-2015.) */

$)
${
	$d x A $.
	$d x B $.
	idfopif_0 $f set x $.
	fdfopif_0 $f class A $.
	fdfopif_1 $f class B $.
	dfopif $p |- <. A , B >. = if ( ( A e. _V /\ B e. _V ) , { { A } , { A , B } } , (/) ) $= fdfopif_0 fdfopif_1 cop fdfopif_0 cvv wcel fdfopif_1 cvv wcel idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel w3a idfopif_0 cab fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr c0 cif idfopif_0 fdfopif_0 fdfopif_1 df-op fdfopif_0 cvv wcel fdfopif_1 cvv wcel idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel w3a fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 fdfopif_0 cvv wcel fdfopif_1 cvv wcel idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel df-3an abbii fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr c0 cif wceq fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr c0 cif fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr c0 iftrue fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel ibar abbi2dv eqtr2d fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa wn fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab c0 fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr c0 cif fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa wn fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab c0 wss fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab c0 wceq fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa wn fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 c0 fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa wn fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class c0 wcel idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class c0 wcel pm2.21 adantrd abssdv fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa idfopif_0 sup_set_class fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr wcel wa idfopif_0 cab ss0 syl fdfopif_0 cvv wcel fdfopif_1 cvv wcel wa fdfopif_0 csn fdfopif_0 fdfopif_1 cpr cpr c0 iffalse eqtr4d pm2.61i 3eqtri $.
$}
$( /* Value of the ordered pair when the arguments are sets.  (Contributed by
     Mario Carneiro, 26-Apr-2015.) */

$)
${
	fdfopg_0 $f class A $.
	fdfopg_1 $f class B $.
	fdfopg_2 $f class V $.
	fdfopg_3 $f class W $.
	dfopg $p |- ( ( A e. V /\ B e. W ) -> <. A , B >. = { { A } , { A , B } } ) $= fdfopg_0 fdfopg_2 wcel fdfopg_0 cvv wcel fdfopg_1 cvv wcel fdfopg_0 fdfopg_1 cop fdfopg_0 csn fdfopg_0 fdfopg_1 cpr cpr wceq fdfopg_1 fdfopg_3 wcel fdfopg_0 fdfopg_2 elex fdfopg_1 fdfopg_3 elex fdfopg_0 cvv wcel fdfopg_1 cvv wcel wa fdfopg_0 fdfopg_1 cop fdfopg_0 cvv wcel fdfopg_1 cvv wcel wa fdfopg_0 csn fdfopg_0 fdfopg_1 cpr cpr c0 cif fdfopg_0 csn fdfopg_0 fdfopg_1 cpr cpr fdfopg_0 fdfopg_1 dfopif fdfopg_0 cvv wcel fdfopg_1 cvv wcel wa fdfopg_0 csn fdfopg_0 fdfopg_1 cpr cpr c0 iftrue syl5eq syl2an $.
$}
$( /* Value of an ordered pair when the arguments are sets, with the
       conclusion corresponding to Kuratowski's original definition.
       (Contributed by NM, 25-Jun-1998.) */

$)
${
	fdfop_0 $f class A $.
	fdfop_1 $f class B $.
	edfop_0 $e |- A e. _V $.
	edfop_1 $e |- B e. _V $.
	dfop $p |- <. A , B >. = { { A } , { A , B } } $= fdfop_0 cvv wcel fdfop_1 cvv wcel fdfop_0 fdfop_1 cop fdfop_0 csn fdfop_0 fdfop_1 cpr cpr wceq edfop_0 edfop_1 fdfop_0 fdfop_1 cvv cvv dfopg mp2an $.
$}
$( /* Equality theorem for ordered pairs.  (Contributed by NM, 25-Jun-1998.)
     (Revised by Mario Carneiro, 26-Apr-2015.) */

$)
${
	fopeq1_0 $f class A $.
	fopeq1_1 $f class B $.
	fopeq1_2 $f class C $.
	opeq1 $p |- ( A = B -> <. A , C >. = <. B , C >. ) $= fopeq1_0 fopeq1_1 wceq fopeq1_0 cvv wcel fopeq1_2 cvv wcel wa fopeq1_0 csn fopeq1_0 fopeq1_2 cpr cpr c0 cif fopeq1_1 cvv wcel fopeq1_2 cvv wcel wa fopeq1_1 csn fopeq1_1 fopeq1_2 cpr cpr c0 cif fopeq1_0 fopeq1_2 cop fopeq1_1 fopeq1_2 cop fopeq1_0 fopeq1_1 wceq fopeq1_0 cvv wcel fopeq1_2 cvv wcel wa fopeq1_1 cvv wcel fopeq1_2 cvv wcel wa fopeq1_0 csn fopeq1_0 fopeq1_2 cpr cpr c0 fopeq1_1 csn fopeq1_1 fopeq1_2 cpr cpr c0 fopeq1_0 fopeq1_1 wceq fopeq1_0 cvv wcel fopeq1_1 cvv wcel fopeq1_2 cvv wcel fopeq1_0 fopeq1_1 cvv eleq1 anbi1d fopeq1_0 fopeq1_1 wceq fopeq1_0 csn fopeq1_1 csn fopeq1_0 fopeq1_2 cpr fopeq1_1 fopeq1_2 cpr fopeq1_0 fopeq1_1 sneq fopeq1_0 fopeq1_1 fopeq1_2 preq1 preq12d fopeq1_0 fopeq1_1 wceq c0 eqidd ifbieq12d fopeq1_0 fopeq1_2 dfopif fopeq1_1 fopeq1_2 dfopif 3eqtr4g $.
$}
$( /* Equality theorem for ordered pairs.  (Contributed by NM, 25-Jun-1998.)
     (Revised by Mario Carneiro, 26-Apr-2015.) */

$)
${
	fopeq2_0 $f class A $.
	fopeq2_1 $f class B $.
	fopeq2_2 $f class C $.
	opeq2 $p |- ( A = B -> <. C , A >. = <. C , B >. ) $= fopeq2_0 fopeq2_1 wceq fopeq2_2 cvv wcel fopeq2_0 cvv wcel wa fopeq2_2 csn fopeq2_2 fopeq2_0 cpr cpr c0 cif fopeq2_2 cvv wcel fopeq2_1 cvv wcel wa fopeq2_2 csn fopeq2_2 fopeq2_1 cpr cpr c0 cif fopeq2_2 fopeq2_0 cop fopeq2_2 fopeq2_1 cop fopeq2_0 fopeq2_1 wceq fopeq2_2 cvv wcel fopeq2_0 cvv wcel wa fopeq2_2 cvv wcel fopeq2_1 cvv wcel wa fopeq2_2 csn fopeq2_2 fopeq2_0 cpr cpr c0 fopeq2_2 csn fopeq2_2 fopeq2_1 cpr cpr c0 fopeq2_0 fopeq2_1 wceq fopeq2_0 cvv wcel fopeq2_1 cvv wcel fopeq2_2 cvv wcel fopeq2_0 fopeq2_1 cvv eleq1 anbi2d fopeq2_0 fopeq2_1 wceq fopeq2_2 fopeq2_0 cpr fopeq2_2 fopeq2_1 cpr fopeq2_2 csn fopeq2_0 fopeq2_1 fopeq2_2 preq2 preq2d fopeq2_0 fopeq2_1 wceq c0 eqidd ifbieq12d fopeq2_2 fopeq2_0 dfopif fopeq2_2 fopeq2_1 dfopif 3eqtr4g $.
$}
$( /* Equality theorem for ordered pairs.  (Contributed by NM, 28-May-1995.) */

$)
${
	fopeq12_0 $f class A $.
	fopeq12_1 $f class B $.
	fopeq12_2 $f class C $.
	fopeq12_3 $f class D $.
	opeq12 $p |- ( ( A = C /\ B = D ) -> <. A , B >. = <. C , D >. ) $= fopeq12_0 fopeq12_2 wceq fopeq12_1 fopeq12_3 wceq fopeq12_0 fopeq12_1 cop fopeq12_2 fopeq12_1 cop fopeq12_2 fopeq12_3 cop fopeq12_0 fopeq12_2 fopeq12_1 opeq1 fopeq12_1 fopeq12_3 fopeq12_2 opeq2 sylan9eq $.
$}
$( /* Equality inference for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) */

$)
${
	fopeq1i_0 $f class A $.
	fopeq1i_1 $f class B $.
	fopeq1i_2 $f class C $.
	eopeq1i_0 $e |- A = B $.
	opeq1i $p |- <. A , C >. = <. B , C >. $= fopeq1i_0 fopeq1i_1 wceq fopeq1i_0 fopeq1i_2 cop fopeq1i_1 fopeq1i_2 cop wceq eopeq1i_0 fopeq1i_0 fopeq1i_1 fopeq1i_2 opeq1 ax-mp $.
$}
$( /* Equality inference for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) */

$)
${
	fopeq2i_0 $f class A $.
	fopeq2i_1 $f class B $.
	fopeq2i_2 $f class C $.
	eopeq2i_0 $e |- A = B $.
	opeq2i $p |- <. C , A >. = <. C , B >. $= fopeq2i_0 fopeq2i_1 wceq fopeq2i_2 fopeq2i_0 cop fopeq2i_2 fopeq2i_1 cop wceq eopeq2i_0 fopeq2i_0 fopeq2i_1 fopeq2i_2 opeq2 ax-mp $.
$}
$( /* Equality inference for ordered pairs.  (Contributed by NM,
         16-Dec-2006.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) */

$)
${
	fopeq12i_0 $f class A $.
	fopeq12i_1 $f class B $.
	fopeq12i_2 $f class C $.
	fopeq12i_3 $f class D $.
	eopeq12i_0 $e |- A = B $.
	eopeq12i_1 $e |- C = D $.
	opeq12i $p |- <. A , C >. = <. B , D >. $= fopeq12i_0 fopeq12i_1 wceq fopeq12i_2 fopeq12i_3 wceq fopeq12i_0 fopeq12i_2 cop fopeq12i_1 fopeq12i_3 cop wceq eopeq12i_0 eopeq12i_1 fopeq12i_0 fopeq12i_2 fopeq12i_1 fopeq12i_3 opeq12 mp2an $.
$}
$( /* Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) */

$)
${
	fopeq1d_0 $f wff ph $.
	fopeq1d_1 $f class A $.
	fopeq1d_2 $f class B $.
	fopeq1d_3 $f class C $.
	eopeq1d_0 $e |- ( ph -> A = B ) $.
	opeq1d $p |- ( ph -> <. A , C >. = <. B , C >. ) $= fopeq1d_0 fopeq1d_1 fopeq1d_2 wceq fopeq1d_1 fopeq1d_3 cop fopeq1d_2 fopeq1d_3 cop wceq eopeq1d_0 fopeq1d_1 fopeq1d_2 fopeq1d_3 opeq1 syl $.
$}
$( /* Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) */

$)
${
	fopeq2d_0 $f wff ph $.
	fopeq2d_1 $f class A $.
	fopeq2d_2 $f class B $.
	fopeq2d_3 $f class C $.
	eopeq2d_0 $e |- ( ph -> A = B ) $.
	opeq2d $p |- ( ph -> <. C , A >. = <. C , B >. ) $= fopeq2d_0 fopeq2d_1 fopeq2d_2 wceq fopeq2d_3 fopeq2d_1 cop fopeq2d_3 fopeq2d_2 cop wceq eopeq2d_0 fopeq2d_1 fopeq2d_2 fopeq2d_3 opeq2 syl $.
$}
$( /* Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) */

$)
${
	fopeq12d_0 $f wff ph $.
	fopeq12d_1 $f class A $.
	fopeq12d_2 $f class B $.
	fopeq12d_3 $f class C $.
	fopeq12d_4 $f class D $.
	eopeq12d_0 $e |- ( ph -> A = B ) $.
	eopeq12d_1 $e |- ( ph -> C = D ) $.
	opeq12d $p |- ( ph -> <. A , C >. = <. B , D >. ) $= fopeq12d_0 fopeq12d_1 fopeq12d_2 wceq fopeq12d_3 fopeq12d_4 wceq fopeq12d_1 fopeq12d_3 cop fopeq12d_2 fopeq12d_4 cop wceq eopeq12d_0 eopeq12d_1 fopeq12d_1 fopeq12d_3 fopeq12d_2 fopeq12d_4 opeq12 syl2anc $.
$}
$( /* Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) */

$)
${
	foteq1_0 $f class A $.
	foteq1_1 $f class B $.
	foteq1_2 $f class C $.
	foteq1_3 $f class D $.
	oteq1 $p |- ( A = B -> <. A , C , D >. = <. B , C , D >. ) $= foteq1_0 foteq1_1 wceq foteq1_0 foteq1_2 cop foteq1_3 cop foteq1_1 foteq1_2 cop foteq1_3 cop foteq1_0 foteq1_2 foteq1_3 cotp foteq1_1 foteq1_2 foteq1_3 cotp foteq1_0 foteq1_1 wceq foteq1_0 foteq1_2 cop foteq1_1 foteq1_2 cop foteq1_3 foteq1_0 foteq1_1 foteq1_2 opeq1 opeq1d foteq1_0 foteq1_2 foteq1_3 df-ot foteq1_1 foteq1_2 foteq1_3 df-ot 3eqtr4g $.
$}
$( /* Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) */

$)
${
	foteq2_0 $f class A $.
	foteq2_1 $f class B $.
	foteq2_2 $f class C $.
	foteq2_3 $f class D $.
	oteq2 $p |- ( A = B -> <. C , A , D >. = <. C , B , D >. ) $= foteq2_0 foteq2_1 wceq foteq2_2 foteq2_0 cop foteq2_3 cop foteq2_2 foteq2_1 cop foteq2_3 cop foteq2_2 foteq2_0 foteq2_3 cotp foteq2_2 foteq2_1 foteq2_3 cotp foteq2_0 foteq2_1 wceq foteq2_2 foteq2_0 cop foteq2_2 foteq2_1 cop foteq2_3 foteq2_0 foteq2_1 foteq2_2 opeq2 opeq1d foteq2_2 foteq2_0 foteq2_3 df-ot foteq2_2 foteq2_1 foteq2_3 df-ot 3eqtr4g $.
$}
$( /* Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) */

$)
${
	foteq3_0 $f class A $.
	foteq3_1 $f class B $.
	foteq3_2 $f class C $.
	foteq3_3 $f class D $.
	oteq3 $p |- ( A = B -> <. C , D , A >. = <. C , D , B >. ) $= foteq3_0 foteq3_1 wceq foteq3_2 foteq3_3 cop foteq3_0 cop foteq3_2 foteq3_3 cop foteq3_1 cop foteq3_2 foteq3_3 foteq3_0 cotp foteq3_2 foteq3_3 foteq3_1 cotp foteq3_0 foteq3_1 foteq3_2 foteq3_3 cop opeq2 foteq3_2 foteq3_3 foteq3_0 df-ot foteq3_2 foteq3_3 foteq3_1 df-ot 3eqtr4g $.
$}
$( /* Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) */

$)
${
	foteq1d_0 $f wff ph $.
	foteq1d_1 $f class A $.
	foteq1d_2 $f class B $.
	foteq1d_3 $f class C $.
	foteq1d_4 $f class D $.
	eoteq1d_0 $e |- ( ph -> A = B ) $.
	oteq1d $p |- ( ph -> <. A , C , D >. = <. B , C , D >. ) $= foteq1d_0 foteq1d_1 foteq1d_2 wceq foteq1d_1 foteq1d_3 foteq1d_4 cotp foteq1d_2 foteq1d_3 foteq1d_4 cotp wceq eoteq1d_0 foteq1d_1 foteq1d_2 foteq1d_3 foteq1d_4 oteq1 syl $.
$}
$( /* Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) */

$)
${
	foteq2d_0 $f wff ph $.
	foteq2d_1 $f class A $.
	foteq2d_2 $f class B $.
	foteq2d_3 $f class C $.
	foteq2d_4 $f class D $.
	eoteq2d_0 $e |- ( ph -> A = B ) $.
	oteq2d $p |- ( ph -> <. C , A , D >. = <. C , B , D >. ) $= foteq2d_0 foteq2d_1 foteq2d_2 wceq foteq2d_3 foteq2d_1 foteq2d_4 cotp foteq2d_3 foteq2d_2 foteq2d_4 cotp wceq eoteq2d_0 foteq2d_1 foteq2d_2 foteq2d_3 foteq2d_4 oteq2 syl $.
$}
$( /* Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) */

$)
${
	foteq3d_0 $f wff ph $.
	foteq3d_1 $f class A $.
	foteq3d_2 $f class B $.
	foteq3d_3 $f class C $.
	foteq3d_4 $f class D $.
	eoteq3d_0 $e |- ( ph -> A = B ) $.
	oteq3d $p |- ( ph -> <. C , D , A >. = <. C , D , B >. ) $= foteq3d_0 foteq3d_1 foteq3d_2 wceq foteq3d_3 foteq3d_4 foteq3d_1 cotp foteq3d_3 foteq3d_4 foteq3d_2 cotp wceq eoteq3d_0 foteq3d_1 foteq3d_2 foteq3d_3 foteq3d_4 oteq3 syl $.
$}
$( /* Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) */

$)
${
	foteq123d_0 $f wff ph $.
	foteq123d_1 $f class A $.
	foteq123d_2 $f class B $.
	foteq123d_3 $f class C $.
	foteq123d_4 $f class D $.
	foteq123d_5 $f class E $.
	foteq123d_6 $f class F $.
	eoteq123d_0 $e |- ( ph -> A = B ) $.
	eoteq123d_1 $e |- ( ph -> C = D ) $.
	eoteq123d_2 $e |- ( ph -> E = F ) $.
	oteq123d $p |- ( ph -> <. A , C , E >. = <. B , D , F >. ) $= foteq123d_0 foteq123d_1 foteq123d_3 foteq123d_5 cotp foteq123d_2 foteq123d_3 foteq123d_5 cotp foteq123d_2 foteq123d_4 foteq123d_5 cotp foteq123d_2 foteq123d_4 foteq123d_6 cotp foteq123d_0 foteq123d_1 foteq123d_2 foteq123d_3 foteq123d_5 eoteq123d_0 oteq1d foteq123d_0 foteq123d_3 foteq123d_4 foteq123d_2 foteq123d_5 eoteq123d_1 oteq2d foteq123d_0 foteq123d_5 foteq123d_6 foteq123d_2 foteq123d_4 eoteq123d_2 oteq3d 3eqtrd $.
$}
$( /* Bound-variable hypothesis builder for ordered pairs.  (Contributed by
       NM, 14-Nov-1995.) */

$)
${
	fnfop_0 $f set x $.
	fnfop_1 $f class A $.
	fnfop_2 $f class B $.
	enfop_0 $e |- F/_ x A $.
	enfop_1 $e |- F/_ x B $.
	nfop $p |- F/_ x <. A , B >. $= fnfop_0 fnfop_1 fnfop_2 cop fnfop_1 cvv wcel fnfop_2 cvv wcel wa fnfop_1 csn fnfop_1 fnfop_2 cpr cpr c0 cif fnfop_1 fnfop_2 dfopif fnfop_1 cvv wcel fnfop_2 cvv wcel wa fnfop_0 fnfop_1 csn fnfop_1 fnfop_2 cpr cpr c0 fnfop_1 cvv wcel fnfop_2 cvv wcel fnfop_0 fnfop_0 fnfop_1 cvv enfop_0 nfel1 fnfop_0 fnfop_2 cvv enfop_1 nfel1 nfan fnfop_0 fnfop_1 csn fnfop_1 fnfop_2 cpr fnfop_0 fnfop_1 enfop_0 nfsn fnfop_0 fnfop_1 fnfop_2 enfop_0 enfop_1 nfpr nfpr fnfop_0 c0 nfcv nfif nfcxfr $.
$}
$( /* Deduction version of bound-variable hypothesis builder ~ nfop .  This
       shows how the deduction version of a not-free theorem such as ~ nfop can
       be created from the corresponding not-free inference theorem.
       (Contributed by NM, 4-Feb-2008.) */

$)
${
	$d z B $.
	$d z A $.
	$d x z $.
	infopd_0 $f set z $.
	fnfopd_0 $f wff ph $.
	fnfopd_1 $f set x $.
	fnfopd_2 $f class A $.
	fnfopd_3 $f class B $.
	enfopd_0 $e |- ( ph -> F/_ x A ) $.
	enfopd_1 $e |- ( ph -> F/_ x B ) $.
	nfopd $p |- ( ph -> F/_ x <. A , B >. ) $= fnfopd_0 fnfopd_1 infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 wal infopd_0 cab infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 wal infopd_0 cab cop wnfc fnfopd_1 fnfopd_2 fnfopd_3 cop wnfc fnfopd_1 infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 wal infopd_0 cab infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 wal infopd_0 cab infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 infopd_0 nfaba1 infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 infopd_0 nfaba1 nfop fnfopd_0 fnfopd_1 fnfopd_2 wnfc fnfopd_1 fnfopd_3 wnfc fnfopd_1 infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 wal infopd_0 cab infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 wal infopd_0 cab cop wnfc fnfopd_1 fnfopd_2 fnfopd_3 cop wnfc wb enfopd_0 enfopd_1 fnfopd_1 fnfopd_2 wnfc fnfopd_1 fnfopd_3 wnfc wa fnfopd_1 infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 wal infopd_0 cab infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 wal infopd_0 cab cop fnfopd_2 fnfopd_3 cop fnfopd_1 fnfopd_2 wnfc fnfopd_1 fnfopd_3 wnfc fnfopd_1 fnfopd_1 fnfopd_2 nfnfc1 fnfopd_1 fnfopd_3 nfnfc1 nfan fnfopd_1 fnfopd_2 wnfc fnfopd_1 fnfopd_3 wnfc wa infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 wal infopd_0 cab fnfopd_2 infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 wal infopd_0 cab fnfopd_3 fnfopd_1 fnfopd_2 wnfc infopd_0 sup_set_class fnfopd_2 wcel fnfopd_1 wal infopd_0 cab fnfopd_2 wceq fnfopd_1 fnfopd_3 wnfc fnfopd_1 infopd_0 fnfopd_2 abidnf adantr fnfopd_1 fnfopd_3 wnfc infopd_0 sup_set_class fnfopd_3 wcel fnfopd_1 wal infopd_0 cab fnfopd_3 wceq fnfopd_1 fnfopd_2 wnfc fnfopd_1 infopd_0 fnfopd_3 abidnf adantl opeq12d nfceqdf syl2anc mpbii $.
$}
$( /* The ordered pair ` <. A , A >. ` in Kuratowski's representation.
       (Contributed by FL, 28-Dec-2011.) */

$)
${
	fopid_0 $f class A $.
	eopid_0 $e |- A e. _V $.
	opid $p |- <. A , A >. = { { A } } $= fopid_0 csn fopid_0 fopid_0 cpr cpr fopid_0 csn fopid_0 csn cpr fopid_0 fopid_0 cop fopid_0 csn csn fopid_0 fopid_0 cpr fopid_0 csn fopid_0 csn fopid_0 csn fopid_0 fopid_0 cpr fopid_0 dfsn2 eqcomi preq2i fopid_0 fopid_0 eopid_0 eopid_0 dfop fopid_0 csn dfsn2 3eqtr4i $.
$}
$( /* Restricted quantification over the union of a set and a singleton, using
       implicit substitution.  (Contributed by Paul Chapman, 17-Nov-2012.)
       (Revised by Mario Carneiro, 23-Apr-2015.) */

$)
${
	$d B x $.
	$d ps x $.
	fralunsn_0 $f wff ph $.
	fralunsn_1 $f wff ps $.
	fralunsn_2 $f set x $.
	fralunsn_3 $f class A $.
	fralunsn_4 $f class B $.
	fralunsn_5 $f class C $.
	eralunsn_0 $e |- ( x = B -> ( ph <-> ps ) ) $.
	ralunsn $p |- ( B e. C -> ( A. x e. ( A u. { B } ) ph <-> ( A. x e. A ph /\ ps ) ) ) $= fralunsn_0 fralunsn_2 fralunsn_3 fralunsn_4 csn cun wral fralunsn_0 fralunsn_2 fralunsn_3 wral fralunsn_0 fralunsn_2 fralunsn_4 csn wral wa fralunsn_4 fralunsn_5 wcel fralunsn_0 fralunsn_2 fralunsn_3 wral fralunsn_1 wa fralunsn_0 fralunsn_2 fralunsn_3 fralunsn_4 csn ralunb fralunsn_4 fralunsn_5 wcel fralunsn_0 fralunsn_2 fralunsn_4 csn wral fralunsn_1 fralunsn_0 fralunsn_2 fralunsn_3 wral fralunsn_0 fralunsn_1 fralunsn_2 fralunsn_4 fralunsn_5 eralunsn_0 ralsng anbi2d syl5bb $.
$}
$( /* Double restricted quantification over the union of a set and a
       singleton, using implicit substitution.  (Contributed by Paul Chapman,
       17-Nov-2012.) */

$)
${
	$d A x $.
	$d B x y $.
	$d C x $.
	$d ch x $.
	$d ps y $.
	$d th x $.
	f2ralunsn_0 $f wff ph $.
	f2ralunsn_1 $f wff ps $.
	f2ralunsn_2 $f wff ch $.
	f2ralunsn_3 $f wff th $.
	f2ralunsn_4 $f set x $.
	f2ralunsn_5 $f set y $.
	f2ralunsn_6 $f class A $.
	f2ralunsn_7 $f class B $.
	f2ralunsn_8 $f class C $.
	e2ralunsn_0 $e |- ( x = B -> ( ph <-> ch ) ) $.
	e2ralunsn_1 $e |- ( y = B -> ( ph <-> ps ) ) $.
	e2ralunsn_2 $e |- ( x = B -> ( ps <-> th ) ) $.
	2ralunsn $p |- ( B e. C -> ( A. x e. ( A u. { B } ) A. y e. ( A u. { B } ) ph <-> ( ( A. x e. A A. y e. A ph /\ A. x e. A ps ) /\ ( A. y e. A ch /\ th ) ) ) ) $= f2ralunsn_7 f2ralunsn_8 wcel f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 f2ralunsn_7 csn cun wral f2ralunsn_4 f2ralunsn_6 f2ralunsn_7 csn cun wral f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 wa f2ralunsn_4 f2ralunsn_6 f2ralunsn_7 csn cun wral f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_4 f2ralunsn_6 wral f2ralunsn_1 f2ralunsn_4 f2ralunsn_6 wral wa f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_3 wa wa f2ralunsn_7 f2ralunsn_8 wcel f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 f2ralunsn_7 csn cun wral f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 wa f2ralunsn_4 f2ralunsn_6 f2ralunsn_7 csn cun f2ralunsn_0 f2ralunsn_1 f2ralunsn_5 f2ralunsn_6 f2ralunsn_7 f2ralunsn_8 e2ralunsn_1 ralunsn ralbidv f2ralunsn_7 f2ralunsn_8 wcel f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 wa f2ralunsn_4 f2ralunsn_6 f2ralunsn_7 csn cun wral f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 wa f2ralunsn_4 f2ralunsn_6 wral f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_3 wa wa f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_4 f2ralunsn_6 wral f2ralunsn_1 f2ralunsn_4 f2ralunsn_6 wral wa f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_3 wa wa f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 wa f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_3 wa f2ralunsn_4 f2ralunsn_6 f2ralunsn_7 f2ralunsn_8 f2ralunsn_4 sup_set_class f2ralunsn_7 wceq f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 f2ralunsn_3 f2ralunsn_4 sup_set_class f2ralunsn_7 wceq f2ralunsn_0 f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 e2ralunsn_0 ralbidv e2ralunsn_2 anbi12d ralunsn f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 wa f2ralunsn_4 f2ralunsn_6 wral f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_4 f2ralunsn_6 wral f2ralunsn_1 f2ralunsn_4 f2ralunsn_6 wral wa f2ralunsn_2 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_3 wa f2ralunsn_0 f2ralunsn_5 f2ralunsn_6 wral f2ralunsn_1 f2ralunsn_4 f2ralunsn_6 r19.26 anbi1i syl6bb bitrd $.
$}
$( /* Expansion of an ordered pair when either member is a proper class.
     (Contributed by Mario Carneiro, 26-Apr-2015.) */

$)
${
	fopprc_0 $f class A $.
	fopprc_1 $f class B $.
	opprc $p |- ( -. ( A e. _V /\ B e. _V ) -> <. A , B >. = (/) ) $= fopprc_0 cvv wcel fopprc_1 cvv wcel wa wn fopprc_0 fopprc_1 cop fopprc_0 cvv wcel fopprc_1 cvv wcel wa fopprc_0 csn fopprc_0 fopprc_1 cpr cpr c0 cif c0 fopprc_0 fopprc_1 dfopif fopprc_0 cvv wcel fopprc_1 cvv wcel wa fopprc_0 csn fopprc_0 fopprc_1 cpr cpr c0 iffalse syl5eq $.
$}
$( /* Expansion of an ordered pair when the first member is a proper class.  See
     also ~ opprc .  (Contributed by NM, 10-Apr-2004.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) */

$)
${
	fopprc1_0 $f class A $.
	fopprc1_1 $f class B $.
	opprc1 $p |- ( -. A e. _V -> <. A , B >. = (/) ) $= fopprc1_0 cvv wcel wn fopprc1_0 cvv wcel fopprc1_1 cvv wcel wa wn fopprc1_0 fopprc1_1 cop c0 wceq fopprc1_0 cvv wcel fopprc1_1 cvv wcel wa fopprc1_0 cvv wcel fopprc1_0 cvv wcel fopprc1_1 cvv wcel simpl con3i fopprc1_0 fopprc1_1 opprc syl $.
$}
$( /* Expansion of an ordered pair when the second member is a proper class.
     See also ~ opprc .  (Contributed by NM, 15-Nov-1994.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) */

$)
${
	fopprc2_0 $f class A $.
	fopprc2_1 $f class B $.
	opprc2 $p |- ( -. B e. _V -> <. A , B >. = (/) ) $= fopprc2_1 cvv wcel wn fopprc2_0 cvv wcel fopprc2_1 cvv wcel wa wn fopprc2_0 fopprc2_1 cop c0 wceq fopprc2_0 cvv wcel fopprc2_1 cvv wcel wa fopprc2_1 cvv wcel fopprc2_0 cvv wcel fopprc2_1 cvv wcel simpr con3i fopprc2_0 fopprc2_1 opprc syl $.
$}
$( /* If an ordered pair has an element, then its arguments are sets.
     (Contributed by Mario Carneiro, 26-Apr-2015.) */

$)
${
	foprcl_0 $f class A $.
	foprcl_1 $f class B $.
	foprcl_2 $f class C $.
	oprcl $p |- ( C e. <. A , B >. -> ( A e. _V /\ B e. _V ) ) $= foprcl_2 foprcl_0 foprcl_1 cop wcel foprcl_0 foprcl_1 cop c0 wceq foprcl_0 cvv wcel foprcl_1 cvv wcel wa foprcl_0 foprcl_1 cop foprcl_2 n0i foprcl_0 foprcl_1 opprc nsyl2 $.
$}
$( /* The power set of a singleton.  (Contributed by NM, 5-Jun-2006.) */

$)
${
	$d x A $.
	ipwsn_0 $f set x $.
	fpwsn_0 $f class A $.
	pwsn $p |- ~P { A } = { (/) , { A } } $= ipwsn_0 sup_set_class fpwsn_0 csn wss ipwsn_0 cab ipwsn_0 sup_set_class c0 wceq ipwsn_0 sup_set_class fpwsn_0 csn wceq wo ipwsn_0 cab fpwsn_0 csn cpw c0 fpwsn_0 csn cpr ipwsn_0 sup_set_class fpwsn_0 csn wss ipwsn_0 sup_set_class c0 wceq ipwsn_0 sup_set_class fpwsn_0 csn wceq wo ipwsn_0 ipwsn_0 sup_set_class fpwsn_0 sssn abbii ipwsn_0 fpwsn_0 csn df-pw ipwsn_0 c0 fpwsn_0 csn dfpr2 3eqtr4i $.
$}
$( /* The power set of a singleton (direct proof).  TO DO - should we keep
       this?  (Contributed by NM, 5-Jun-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) */

$)
${
	$d x A $.
	$d x y $.
	$d y A $.
	ipwsnALT_0 $f set x $.
	ipwsnALT_1 $f set y $.
	fpwsnALT_0 $f class A $.
	pwsnALT $p |- ~P { A } = { (/) , { A } } $= ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 cab ipwsnALT_0 sup_set_class c0 wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wceq wo ipwsnALT_0 cab fpwsnALT_0 csn cpw c0 fpwsnALT_0 csn cpr ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 sup_set_class c0 wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wceq wo ipwsnALT_0 ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 sup_set_class c0 wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wceq wo ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 sup_set_class c0 wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 sup_set_class c0 wceq wn ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss fpwsnALT_0 csn ipwsnALT_0 sup_set_class wss wa ipwsnALT_0 sup_set_class fpwsnALT_0 csn wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 sup_set_class c0 wceq wn fpwsnALT_0 csn ipwsnALT_0 sup_set_class wss ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wi ipwsnALT_1 wal ipwsnALT_0 sup_set_class c0 wceq wn fpwsnALT_0 csn ipwsnALT_0 sup_set_class wss wi ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 csn wcel wi ipwsnALT_1 wal ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wi ipwsnALT_1 wal ipwsnALT_1 ipwsnALT_0 sup_set_class fpwsnALT_0 csn dfss2 ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 csn wcel wi ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wi ipwsnALT_1 ipwsnALT_1 sup_set_class fpwsnALT_0 csn wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 fpwsnALT_0 elsn imbi2i albii bitri ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wi ipwsnALT_1 wal ipwsnALT_0 sup_set_class c0 wceq wn ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wa ipwsnALT_1 wex fpwsnALT_0 csn ipwsnALT_0 sup_set_class wss ipwsnALT_0 sup_set_class c0 wceq wn ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 wex ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wi ipwsnALT_1 wal ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wa ipwsnALT_1 wex ipwsnALT_1 ipwsnALT_0 sup_set_class neq0 ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq ipwsnALT_1 exintr syl5bi ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wa ipwsnALT_1 wex fpwsnALT_0 ipwsnALT_0 sup_set_class wcel fpwsnALT_0 csn ipwsnALT_0 sup_set_class wss fpwsnALT_0 ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel wa ipwsnALT_1 wex ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq wa ipwsnALT_1 wex ipwsnALT_1 fpwsnALT_0 ipwsnALT_0 sup_set_class df-clel ipwsnALT_1 sup_set_class fpwsnALT_0 wceq ipwsnALT_1 sup_set_class ipwsnALT_0 sup_set_class wcel ipwsnALT_1 exancom bitr2i fpwsnALT_0 ipwsnALT_0 sup_set_class snssi sylbi syl6 sylbi anc2li ipwsnALT_0 sup_set_class fpwsnALT_0 csn eqss syl6ibr orrd ipwsnALT_0 sup_set_class c0 wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss ipwsnALT_0 sup_set_class fpwsnALT_0 csn wceq ipwsnALT_0 sup_set_class c0 wceq ipwsnALT_0 sup_set_class fpwsnALT_0 csn wss c0 fpwsnALT_0 csn wss fpwsnALT_0 csn 0ss ipwsnALT_0 sup_set_class c0 fpwsnALT_0 csn sseq1 mpbiri ipwsnALT_0 sup_set_class fpwsnALT_0 csn eqimss jaoi impbii abbii ipwsnALT_0 fpwsnALT_0 csn df-pw ipwsnALT_0 c0 fpwsnALT_0 csn dfpr2 3eqtr4i $.
$}
$( /* The power set of an unordered pair.  (Contributed by NM, 1-May-2009.) */

$)
${
	$d x A $.
	$d x B $.
	ipwpr_0 $f set x $.
	fpwpr_0 $f class A $.
	fpwpr_1 $f class B $.
	pwpr $p |- ~P { A , B } = ( { (/) , { A } } u. { { B } , { A , B } } ) $= ipwpr_0 fpwpr_0 fpwpr_1 cpr cpw c0 fpwpr_0 csn cpr fpwpr_1 csn fpwpr_0 fpwpr_1 cpr cpr cun ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 cpr wss ipwpr_0 sup_set_class c0 fpwpr_0 csn cpr wcel ipwpr_0 sup_set_class fpwpr_1 csn fpwpr_0 fpwpr_1 cpr cpr wcel wo ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 cpr cpw wcel ipwpr_0 sup_set_class c0 fpwpr_0 csn cpr fpwpr_1 csn fpwpr_0 fpwpr_1 cpr cpr cun wcel ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 cpr wss ipwpr_0 sup_set_class c0 wceq ipwpr_0 sup_set_class fpwpr_0 csn wceq wo ipwpr_0 sup_set_class fpwpr_1 csn wceq ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 cpr wceq wo wo ipwpr_0 sup_set_class c0 fpwpr_0 csn cpr wcel ipwpr_0 sup_set_class fpwpr_1 csn fpwpr_0 fpwpr_1 cpr cpr wcel wo ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 sspr ipwpr_0 sup_set_class c0 fpwpr_0 csn cpr wcel ipwpr_0 sup_set_class c0 wceq ipwpr_0 sup_set_class fpwpr_0 csn wceq wo ipwpr_0 sup_set_class fpwpr_1 csn fpwpr_0 fpwpr_1 cpr cpr wcel ipwpr_0 sup_set_class fpwpr_1 csn wceq ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 cpr wceq wo ipwpr_0 sup_set_class c0 fpwpr_0 csn ipwpr_0 vex elpr ipwpr_0 sup_set_class fpwpr_1 csn fpwpr_0 fpwpr_1 cpr ipwpr_0 vex elpr orbi12i bitr4i ipwpr_0 sup_set_class fpwpr_0 fpwpr_1 cpr ipwpr_0 vex elpw ipwpr_0 sup_set_class c0 fpwpr_0 csn cpr fpwpr_1 csn fpwpr_0 fpwpr_1 cpr cpr elun 3bitr4i eqriv $.
$}
$( /* The power set of an unordered triple.  (Contributed by Mario Carneiro,
       2-Jul-2016.) */

$)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ipwtp_0 $f set x $.
	fpwtp_0 $f class A $.
	fpwtp_1 $f class B $.
	fpwtp_2 $f class C $.
	pwtp $p |- ~P { A , B , C } = ( ( { (/) , { A } } u. { { B } , { A , B } } ) u. ( { { C } , { A , C } } u. { { B , C } , { A , B , C } } ) ) $= ipwtp_0 fpwtp_0 fpwtp_1 fpwtp_2 ctp cpw c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun cun ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp cpw wcel ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp wss ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun cun wcel ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp ipwtp_0 vex elpw ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun wcel ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun wcel wo ipwtp_0 sup_set_class c0 wceq ipwtp_0 sup_set_class fpwtp_0 csn wceq wo ipwtp_0 sup_set_class fpwtp_1 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 cpr wceq wo wo ipwtp_0 sup_set_class fpwtp_2 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_2 cpr wceq wo ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp wceq wo wo wo ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun cun wcel ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp wss ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun wcel ipwtp_0 sup_set_class c0 wceq ipwtp_0 sup_set_class fpwtp_0 csn wceq wo ipwtp_0 sup_set_class fpwtp_1 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 cpr wceq wo wo ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun wcel ipwtp_0 sup_set_class fpwtp_2 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_2 cpr wceq wo ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp wceq wo wo ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun wcel ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr wcel ipwtp_0 sup_set_class fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr wcel wo ipwtp_0 sup_set_class c0 wceq ipwtp_0 sup_set_class fpwtp_0 csn wceq wo ipwtp_0 sup_set_class fpwtp_1 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 cpr wceq wo wo ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr elun ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr wcel ipwtp_0 sup_set_class c0 wceq ipwtp_0 sup_set_class fpwtp_0 csn wceq wo ipwtp_0 sup_set_class fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr wcel ipwtp_0 sup_set_class fpwtp_1 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 cpr wceq wo ipwtp_0 sup_set_class c0 fpwtp_0 csn ipwtp_0 vex elpr ipwtp_0 sup_set_class fpwtp_1 csn fpwtp_0 fpwtp_1 cpr ipwtp_0 vex elpr orbi12i bitri ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun wcel ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr wcel ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr wcel wo ipwtp_0 sup_set_class fpwtp_2 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_2 cpr wceq wo ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp wceq wo wo ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr elun ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr wcel ipwtp_0 sup_set_class fpwtp_2 csn wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_2 cpr wceq wo ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr wcel ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr wceq ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 ctp wceq wo ipwtp_0 sup_set_class fpwtp_2 csn fpwtp_0 fpwtp_2 cpr ipwtp_0 vex elpr ipwtp_0 sup_set_class fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp ipwtp_0 vex elpr orbi12i bitri orbi12i ipwtp_0 sup_set_class c0 fpwtp_0 csn cpr fpwtp_1 csn fpwtp_0 fpwtp_1 cpr cpr cun fpwtp_2 csn fpwtp_0 fpwtp_2 cpr cpr fpwtp_1 fpwtp_2 cpr fpwtp_0 fpwtp_1 fpwtp_2 ctp cpr cun elun ipwtp_0 sup_set_class fpwtp_0 fpwtp_1 fpwtp_2 sstp 3bitr4ri bitri eqriv $.
$}
$( /* Compute the power set of the power set of the power set of the empty
       set.  (See also ~ pw0 and ~ pwpw0 .)  (Contributed by NM,
       2-May-2009.) */

$)
${
	pwpwpw0 $p |- ~P { (/) , { (/) } } = ( { (/) , { (/) } } u. { { { (/) } } , { (/) , { (/) } } } ) $= c0 c0 csn pwpr $.
$}
$( /* The power class of the universe is the universe.  Exercise 4.12(d) of
       [Mendelson] p. 235.  (Contributed by NM, 14-Sep-2003.) */

$)
${
	ipwv_0 $f set x $.
	pwv $p |- ~P _V = _V $= ipwv_0 cvv cpw cvv ipwv_0 sup_set_class cvv cpw wcel ipwv_0 sup_set_class cvv wcel ipwv_0 sup_set_class cvv cpw wcel ipwv_0 sup_set_class cvv wss ipwv_0 sup_set_class ssv ipwv_0 sup_set_class cvv ipwv_0 vex elpw mpbir ipwv_0 vex 2th eqriv $.
$}

