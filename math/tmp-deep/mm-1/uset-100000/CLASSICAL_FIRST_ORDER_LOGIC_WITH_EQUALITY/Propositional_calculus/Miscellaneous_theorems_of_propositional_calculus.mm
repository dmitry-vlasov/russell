$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical_disjunction_and_conjunction.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Miscellaneous theorems of propositional calculus

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Eliminate an antecedent implied by each side of a biconditional.
       (Contributed by NM, 20-Nov-2005.)  (Proof shortened by Wolf Lammen,
       4-Nov-2013.) */

$)
${
	fpm5.21nd_0 $f wff ph $.
	fpm5.21nd_1 $f wff ps $.
	fpm5.21nd_2 $f wff ch $.
	fpm5.21nd_3 $f wff th $.
	epm5.21nd_0 $e |- ( ( ph /\ ps ) -> th ) $.
	epm5.21nd_1 $e |- ( ( ph /\ ch ) -> th ) $.
	epm5.21nd_2 $e |- ( th -> ( ps <-> ch ) ) $.
	pm5.21nd $p |- ( ph -> ( ps <-> ch ) ) $= fpm5.21nd_0 fpm5.21nd_3 fpm5.21nd_1 fpm5.21nd_2 fpm5.21nd_0 fpm5.21nd_1 fpm5.21nd_3 epm5.21nd_0 ex fpm5.21nd_0 fpm5.21nd_2 fpm5.21nd_3 epm5.21nd_1 ex fpm5.21nd_3 fpm5.21nd_1 fpm5.21nd_2 wb wi fpm5.21nd_0 epm5.21nd_2 a1i pm5.21ndd $.
$}
$( /* Theorem *5.35 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) */

$)
${
	fpm5.35_0 $f wff ph $.
	fpm5.35_1 $f wff ps $.
	fpm5.35_2 $f wff ch $.
	pm5.35 $p |- ( ( ( ph -> ps ) /\ ( ph -> ch ) ) -> ( ph -> ( ps <-> ch ) ) ) $= fpm5.35_0 fpm5.35_1 wi fpm5.35_0 fpm5.35_2 wi wa fpm5.35_0 fpm5.35_1 fpm5.35_2 fpm5.35_0 fpm5.35_1 wi fpm5.35_0 fpm5.35_2 wi pm5.1 pm5.74rd $.
$}
$( /* Theorem *5.54 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 7-Nov-2013.) */

$)
${
	fpm5.54_0 $f wff ph $.
	fpm5.54_1 $f wff ps $.
	pm5.54 $p |- ( ( ( ph /\ ps ) <-> ph ) \/ ( ( ph /\ ps ) <-> ps ) ) $= fpm5.54_0 fpm5.54_1 wa fpm5.54_0 wb fpm5.54_0 fpm5.54_1 wa fpm5.54_1 wb fpm5.54_0 fpm5.54_1 wa fpm5.54_0 fpm5.54_1 wa fpm5.54_0 wb fpm5.54_1 fpm5.54_1 fpm5.54_0 fpm5.54_1 wa fpm5.54_0 wb fpm5.54_0 fpm5.54_1 fpm5.54_0 fpm5.54_0 fpm5.54_1 wa fpm5.54_1 fpm5.54_0 iba bicomd adantl fpm5.54_1 fpm5.54_0 fpm5.54_0 fpm5.54_1 wa fpm5.54_1 fpm5.54_0 iba bicomd pm5.21ni orri $.
$}
$( /* Move conjunction outside of biconditional.  (Contributed by NM,
       13-May-1999.) */

$)
${
	fbaib_0 $f wff ph $.
	fbaib_1 $f wff ps $.
	fbaib_2 $f wff ch $.
	ebaib_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	baib $p |- ( ps -> ( ph <-> ch ) ) $= fbaib_1 fbaib_2 fbaib_1 fbaib_2 wa fbaib_0 fbaib_1 fbaib_2 ibar ebaib_0 syl6rbbr $.
$}
$( /* Move conjunction outside of biconditional.  (Contributed by NM,
       11-Jul-1994.) */

$)
${
	fbaibr_0 $f wff ph $.
	fbaibr_1 $f wff ps $.
	fbaibr_2 $f wff ch $.
	ebaibr_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	baibr $p |- ( ps -> ( ch <-> ph ) ) $= fbaibr_1 fbaibr_0 fbaibr_2 fbaibr_0 fbaibr_1 fbaibr_2 ebaibr_0 baib bicomd $.
$}
$( /* Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) */

$)
${
	frbaib_0 $f wff ph $.
	frbaib_1 $f wff ps $.
	frbaib_2 $f wff ch $.
	erbaib_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	rbaib $p |- ( ch -> ( ph <-> ps ) ) $= frbaib_0 frbaib_2 frbaib_1 frbaib_0 frbaib_1 frbaib_2 wa frbaib_2 frbaib_1 wa erbaib_0 frbaib_1 frbaib_2 ancom bitri baib $.
$}
$( /* Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) */

$)
${
	frbaibr_0 $f wff ph $.
	frbaibr_1 $f wff ps $.
	frbaibr_2 $f wff ch $.
	erbaibr_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	rbaibr $p |- ( ch -> ( ps <-> ph ) ) $= frbaibr_0 frbaibr_2 frbaibr_1 frbaibr_0 frbaibr_1 frbaibr_2 wa frbaibr_2 frbaibr_1 wa erbaibr_0 frbaibr_1 frbaibr_2 ancom bitri baibr $.
$}
$( /* Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) */

$)
${
	fbaibd_0 $f wff ph $.
	fbaibd_1 $f wff ps $.
	fbaibd_2 $f wff ch $.
	fbaibd_3 $f wff th $.
	ebaibd_0 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	baibd $p |- ( ( ph /\ ch ) -> ( ps <-> th ) ) $= fbaibd_0 fbaibd_1 fbaibd_2 fbaibd_3 wa fbaibd_2 fbaibd_3 ebaibd_0 fbaibd_2 fbaibd_3 fbaibd_2 fbaibd_3 wa fbaibd_2 fbaibd_3 ibar bicomd sylan9bb $.
$}
$( /* Move conjunction outside of biconditional.  (Contributed by Mario
       Carneiro, 11-Sep-2015.) */

$)
${
	frbaibd_0 $f wff ph $.
	frbaibd_1 $f wff ps $.
	frbaibd_2 $f wff ch $.
	frbaibd_3 $f wff th $.
	erbaibd_0 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	rbaibd $p |- ( ( ph /\ th ) -> ( ps <-> ch ) ) $= frbaibd_0 frbaibd_1 frbaibd_2 frbaibd_3 wa frbaibd_3 frbaibd_2 erbaibd_0 frbaibd_3 frbaibd_2 frbaibd_2 frbaibd_3 wa frbaibd_3 frbaibd_2 iba bicomd sylan9bb $.
$}
$( /* Theorem *5.44 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.) */

$)
${
	fpm5.44_0 $f wff ph $.
	fpm5.44_1 $f wff ps $.
	fpm5.44_2 $f wff ch $.
	pm5.44 $p |- ( ( ph -> ps ) -> ( ( ph -> ch ) <-> ( ph -> ( ps /\ ch ) ) ) ) $= fpm5.44_0 fpm5.44_1 fpm5.44_2 wa wi fpm5.44_0 fpm5.44_1 wi fpm5.44_0 fpm5.44_2 wi fpm5.44_0 fpm5.44_1 fpm5.44_2 jcab baibr $.
$}
$( /* Conjunction in antecedent versus disjunction in consequent.  Theorem *5.6
     of [WhiteheadRussell] p. 125.  (Contributed by NM, 8-Jun-1994.) */

$)
${
	fpm5.6_0 $f wff ph $.
	fpm5.6_1 $f wff ps $.
	fpm5.6_2 $f wff ch $.
	pm5.6 $p |- ( ( ( ph /\ -. ps ) -> ch ) <-> ( ph -> ( ps \/ ch ) ) ) $= fpm5.6_0 fpm5.6_1 wn wa fpm5.6_2 wi fpm5.6_0 fpm5.6_1 wn fpm5.6_2 wi wi fpm5.6_0 fpm5.6_1 fpm5.6_2 wo wi fpm5.6_0 fpm5.6_1 wn fpm5.6_2 impexp fpm5.6_1 fpm5.6_2 wo fpm5.6_1 wn fpm5.6_2 wi fpm5.6_0 fpm5.6_1 fpm5.6_2 df-or imbi2i bitr4i $.
$}
$( /* Change disjunction in consequent to conjunction in antecedent.
       (Contributed by NM, 8-Jun-1994.) */

$)
${
	forcanai_0 $f wff ph $.
	forcanai_1 $f wff ps $.
	forcanai_2 $f wff ch $.
	eorcanai_0 $e |- ( ph -> ( ps \/ ch ) ) $.
	orcanai $p |- ( ( ph /\ -. ps ) -> ch ) $= forcanai_0 forcanai_1 wn forcanai_2 forcanai_0 forcanai_1 forcanai_2 eorcanai_0 ord imp $.
$}
$( /* Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       16-Sep-1993.) */

$)
${
	fintnan_0 $f wff ph $.
	fintnan_1 $f wff ps $.
	eintnan_0 $e |- -. ph $.
	intnan $p |- -. ( ps /\ ph ) $= fintnan_1 fintnan_0 wa fintnan_0 eintnan_0 fintnan_1 fintnan_0 simpr mto $.
$}
$( /* Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       3-Apr-1995.) */

$)
${
	fintnanr_0 $f wff ph $.
	fintnanr_1 $f wff ps $.
	eintnanr_0 $e |- -. ph $.
	intnanr $p |- -. ( ph /\ ps ) $= fintnanr_0 fintnanr_1 wa fintnanr_0 eintnanr_0 fintnanr_0 fintnanr_1 simpl mto $.
$}
$( /* Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) */

$)
${
	fintnand_0 $f wff ph $.
	fintnand_1 $f wff ps $.
	fintnand_2 $f wff ch $.
	eintnand_0 $e |- ( ph -> -. ps ) $.
	intnand $p |- ( ph -> -. ( ch /\ ps ) ) $= fintnand_0 fintnand_1 fintnand_2 fintnand_1 wa eintnand_0 fintnand_2 fintnand_1 simpr nsyl $.
$}
$( /* Introduction of conjunct inside of a contradiction.  (Contributed by NM,
       10-Jul-2005.) */

$)
${
	fintnanrd_0 $f wff ph $.
	fintnanrd_1 $f wff ps $.
	fintnanrd_2 $f wff ch $.
	eintnanrd_0 $e |- ( ph -> -. ps ) $.
	intnanrd $p |- ( ph -> -. ( ps /\ ch ) ) $= fintnanrd_0 fintnanrd_1 fintnanrd_1 fintnanrd_2 wa eintnanrd_0 fintnanrd_1 fintnanrd_2 simpl nsyl $.
$}
$( /* Detach truth from conjunction in biconditional.  (Contributed by NM,
       27-Feb-1996.) */

$)
${
	fmpbiran_0 $f wff ph $.
	fmpbiran_1 $f wff ps $.
	fmpbiran_2 $f wff ch $.
	empbiran_0 $e |- ps $.
	empbiran_1 $e |- ( ph <-> ( ps /\ ch ) ) $.
	mpbiran $p |- ( ph <-> ch ) $= fmpbiran_0 fmpbiran_1 fmpbiran_2 wa fmpbiran_2 empbiran_1 fmpbiran_1 fmpbiran_2 empbiran_0 biantrur bitr4i $.
$}
$( /* Detach truth from conjunction in biconditional.  (Contributed by NM,
       22-Feb-1996.) */

$)
${
	fmpbiran2_0 $f wff ph $.
	fmpbiran2_1 $f wff ps $.
	fmpbiran2_2 $f wff ch $.
	empbiran2_0 $e |- ch $.
	empbiran2_1 $e |- ( ph <-> ( ps /\ ch ) ) $.
	mpbiran2 $p |- ( ph <-> ps ) $= fmpbiran2_0 fmpbiran2_1 fmpbiran2_2 wa fmpbiran2_1 empbiran2_1 fmpbiran2_2 fmpbiran2_1 empbiran2_0 biantru bitr4i $.
$}
$( /* Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       10-May-2005.) */

$)
${
	fmpbir2an_0 $f wff ph $.
	fmpbir2an_1 $f wff ps $.
	fmpbir2an_2 $f wff ch $.
	empbir2an_0 $e |- ps $.
	empbir2an_1 $e |- ch $.
	empbir2an_2 $e |- ( ph <-> ( ps /\ ch ) ) $.
	mpbir2an $p |- ph $= fmpbir2an_0 fmpbir2an_2 empbir2an_1 fmpbir2an_0 fmpbir2an_1 fmpbir2an_2 empbir2an_0 empbir2an_2 mpbiran mpbir $.
$}
$( /* Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) */

$)
${
	fmpbi2and_0 $f wff ph $.
	fmpbi2and_1 $f wff ps $.
	fmpbi2and_2 $f wff ch $.
	fmpbi2and_3 $f wff th $.
	empbi2and_0 $e |- ( ph -> ps ) $.
	empbi2and_1 $e |- ( ph -> ch ) $.
	empbi2and_2 $e |- ( ph -> ( ( ps /\ ch ) <-> th ) ) $.
	mpbi2and $p |- ( ph -> th ) $= fmpbi2and_0 fmpbi2and_1 fmpbi2and_2 wa fmpbi2and_3 fmpbi2and_0 fmpbi2and_1 fmpbi2and_2 empbi2and_0 empbi2and_1 jca empbi2and_2 mpbid $.
$}
$( /* Detach a conjunction of truths in a biconditional.  (Contributed by NM,
       6-Nov-2011.)  (Proof shortened by Wolf Lammen, 24-Nov-2012.) */

$)
${
	fmpbir2and_0 $f wff ph $.
	fmpbir2and_1 $f wff ps $.
	fmpbir2and_2 $f wff ch $.
	fmpbir2and_3 $f wff th $.
	empbir2and_0 $e |- ( ph -> ch ) $.
	empbir2and_1 $e |- ( ph -> th ) $.
	empbir2and_2 $e |- ( ph -> ( ps <-> ( ch /\ th ) ) ) $.
	mpbir2and $p |- ( ph -> ps ) $= fmpbir2and_0 fmpbir2and_1 fmpbir2and_2 fmpbir2and_3 wa fmpbir2and_0 fmpbir2and_2 fmpbir2and_3 empbir2and_0 empbir2and_1 jca empbir2and_2 mpbird $.
$}
$( /* Theorem *5.62 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) */

$)
${
	fpm5.62_0 $f wff ph $.
	fpm5.62_1 $f wff ps $.
	pm5.62 $p |- ( ( ( ph /\ ps ) \/ -. ps ) <-> ( ph \/ -. ps ) ) $= fpm5.62_0 fpm5.62_1 wa fpm5.62_1 wn wo fpm5.62_0 fpm5.62_1 wn wo fpm5.62_1 fpm5.62_1 wn wo fpm5.62_1 exmid fpm5.62_0 fpm5.62_1 fpm5.62_1 wn ordir mpbiran2 $.
$}
$( /* Theorem *5.63 of [WhiteheadRussell] p. 125.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 25-Dec-2012.) */

$)
${
	fpm5.63_0 $f wff ph $.
	fpm5.63_1 $f wff ps $.
	pm5.63 $p |- ( ( ph \/ ps ) <-> ( ph \/ ( -. ph /\ ps ) ) ) $= fpm5.63_0 fpm5.63_0 wn fpm5.63_1 wa wo fpm5.63_0 fpm5.63_1 wo fpm5.63_0 fpm5.63_0 wn fpm5.63_1 wa wo fpm5.63_0 fpm5.63_0 wn wo fpm5.63_0 fpm5.63_1 wo fpm5.63_0 exmid fpm5.63_0 fpm5.63_0 wn fpm5.63_1 ordi mpbiran bicomi $.
$}
$( /* A wff conjoined with falsehood is false.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) */

$)
${
	fbianfi_0 $f wff ph $.
	fbianfi_1 $f wff ps $.
	ebianfi_0 $e |- -. ph $.
	bianfi $p |- ( ph <-> ( ps /\ ph ) ) $= fbianfi_0 fbianfi_1 fbianfi_0 wa ebianfi_0 fbianfi_0 fbianfi_1 ebianfi_0 intnan 2false $.
$}
$( /* A wff conjoined with falsehood is false.  (Contributed by NM,
       27-Mar-1995.)  (Proof shortened by Wolf Lammen, 5-Nov-2013.) */

$)
${
	fbianfd_0 $f wff ph $.
	fbianfd_1 $f wff ps $.
	fbianfd_2 $f wff ch $.
	ebianfd_0 $e |- ( ph -> -. ps ) $.
	bianfd $p |- ( ph -> ( ps <-> ( ps /\ ch ) ) ) $= fbianfd_0 fbianfd_1 fbianfd_1 fbianfd_2 wa ebianfd_0 fbianfd_0 fbianfd_1 fbianfd_2 ebianfd_0 intnanrd 2falsed $.
$}
$( /* Theorem *4.43 of [WhiteheadRussell] p. 119.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Wolf Lammen, 26-Nov-2012.) */

$)
${
	fpm4.43_0 $f wff ph $.
	fpm4.43_1 $f wff ps $.
	pm4.43 $p |- ( ph <-> ( ( ph \/ ps ) /\ ( ph \/ -. ps ) ) ) $= fpm4.43_0 fpm4.43_0 fpm4.43_1 fpm4.43_1 wn wa wo fpm4.43_0 fpm4.43_1 wo fpm4.43_0 fpm4.43_1 wn wo wa fpm4.43_1 fpm4.43_1 wn wa fpm4.43_0 fpm4.43_1 pm3.24 biorfi fpm4.43_0 fpm4.43_1 fpm4.43_1 wn ordi bitri $.
$}
$( /* Theorem *4.82 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) */

$)
${
	fpm4.82_0 $f wff ph $.
	fpm4.82_1 $f wff ps $.
	pm4.82 $p |- ( ( ( ph -> ps ) /\ ( ph -> -. ps ) ) <-> -. ph ) $= fpm4.82_0 fpm4.82_1 wi fpm4.82_0 fpm4.82_1 wn wi wa fpm4.82_0 wn fpm4.82_0 fpm4.82_1 wi fpm4.82_0 fpm4.82_1 wn wi fpm4.82_0 wn fpm4.82_0 fpm4.82_1 pm2.65 imp fpm4.82_0 wn fpm4.82_0 fpm4.82_1 wi fpm4.82_0 fpm4.82_1 wn wi fpm4.82_0 fpm4.82_1 pm2.21 fpm4.82_0 fpm4.82_1 wn pm2.21 jca impbii $.
$}
$( /* Theorem *4.83 of [WhiteheadRussell] p. 122.  (Contributed by NM,
     3-Jan-2005.) */

$)
${
	fpm4.83_0 $f wff ph $.
	fpm4.83_1 $f wff ps $.
	pm4.83 $p |- ( ( ( ph -> ps ) /\ ( -. ph -> ps ) ) <-> ps ) $= fpm4.83_1 fpm4.83_0 fpm4.83_0 wn wo fpm4.83_1 wi fpm4.83_0 fpm4.83_1 wi fpm4.83_0 wn fpm4.83_1 wi wa fpm4.83_0 fpm4.83_0 wn wo fpm4.83_1 fpm4.83_0 exmid a1bi fpm4.83_0 fpm4.83_1 fpm4.83_0 wn jaob bitr2i $.
$}
$( /* Negation inferred from embedded conjunct.  (Contributed by NM,
     20-Aug-1993.)  (Proof shortened by Wolf Lammen, 25-Nov-2012.) */

$)
${
	fpclem6_0 $f wff ph $.
	fpclem6_1 $f wff ps $.
	pclem6 $p |- ( ( ph <-> ( ps /\ -. ph ) ) -> -. ps ) $= fpclem6_1 fpclem6_0 fpclem6_1 fpclem6_0 wn wa wb fpclem6_1 fpclem6_0 wn fpclem6_1 fpclem6_0 wn wa wb fpclem6_0 fpclem6_1 fpclem6_0 wn wa wb wn fpclem6_1 fpclem6_0 wn ibar fpclem6_0 fpclem6_1 fpclem6_0 wn wa nbbn sylib con2i $.
$}
$( /* A transitive law of equivalence.  Compare Theorem *4.22 of
     [WhiteheadRussell] p. 117.  (Contributed by NM, 18-Aug-1993.) */

$)
${
	fbiantr_0 $f wff ph $.
	fbiantr_1 $f wff ps $.
	fbiantr_2 $f wff ch $.
	biantr $p |- ( ( ( ph <-> ps ) /\ ( ch <-> ps ) ) -> ( ph <-> ch ) ) $= fbiantr_2 fbiantr_1 wb fbiantr_0 fbiantr_2 wb fbiantr_0 fbiantr_1 wb fbiantr_2 fbiantr_1 wb fbiantr_2 fbiantr_1 fbiantr_0 fbiantr_2 fbiantr_1 wb id bibi2d biimparc $.
$}
$( /* Disjunction distributes over the biconditional.  An axiom of system DS in
     Vladimir Lifschitz, "On calculational proofs" (1998),
     ~ http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.3384 .
     (Contributed by NM, 8-Jan-2005.)  (Proof shortened by Wolf Lammen,
     4-Feb-2013.) */

$)
${
	forbidi_0 $f wff ph $.
	forbidi_1 $f wff ps $.
	forbidi_2 $f wff ch $.
	orbidi $p |- ( ( ph \/ ( ps <-> ch ) ) <-> ( ( ph \/ ps ) <-> ( ph \/ ch ) ) ) $= forbidi_0 wn forbidi_1 forbidi_2 wb wi forbidi_0 wn forbidi_1 wi forbidi_0 wn forbidi_2 wi wb forbidi_0 forbidi_1 forbidi_2 wb wo forbidi_0 forbidi_1 wo forbidi_0 forbidi_2 wo wb forbidi_0 wn forbidi_1 forbidi_2 pm5.74 forbidi_0 forbidi_1 forbidi_2 wb df-or forbidi_0 forbidi_1 wo forbidi_0 wn forbidi_1 wi forbidi_0 forbidi_2 wo forbidi_0 wn forbidi_2 wi forbidi_0 forbidi_1 df-or forbidi_0 forbidi_2 df-or bibi12i 3bitr4i $.
$}
$( /* Lukasiewicz's shortest axiom for equivalential calculus.  Storrs McCall,
     ed., _Polish Logic 1920-1939_ (Oxford, 1967), p. 96.  (Contributed by NM,
     10-Jan-2005.) */

$)
${
	fbiluk_0 $f wff ph $.
	fbiluk_1 $f wff ps $.
	fbiluk_2 $f wff ch $.
	biluk $p |- ( ( ph <-> ps ) <-> ( ( ch <-> ps ) <-> ( ph <-> ch ) ) ) $= fbiluk_0 fbiluk_1 wb fbiluk_2 fbiluk_1 fbiluk_0 fbiluk_2 wb wb wb fbiluk_2 fbiluk_1 wb fbiluk_0 fbiluk_2 wb wb fbiluk_0 fbiluk_1 wb fbiluk_2 wb fbiluk_1 fbiluk_0 fbiluk_2 wb wb wb fbiluk_0 fbiluk_1 wb fbiluk_2 fbiluk_1 fbiluk_0 fbiluk_2 wb wb wb wb fbiluk_0 fbiluk_1 wb fbiluk_2 wb fbiluk_1 fbiluk_0 wb fbiluk_2 wb fbiluk_1 fbiluk_0 fbiluk_2 wb wb fbiluk_0 fbiluk_1 wb fbiluk_1 fbiluk_0 wb fbiluk_2 fbiluk_0 fbiluk_1 bicom bibi1i fbiluk_1 fbiluk_0 fbiluk_2 biass bitri fbiluk_0 fbiluk_1 wb fbiluk_2 fbiluk_1 fbiluk_0 fbiluk_2 wb wb biass mpbi fbiluk_2 fbiluk_1 fbiluk_0 fbiluk_2 wb biass bitr4i $.
$}
$( /* Disjunction distributes over the biconditional.  Theorem *5.7 of
     [WhiteheadRussell] p. 125.  This theorem is similar to ~ orbidi .
     (Contributed by Roy F. Longton, 21-Jun-2005.) */

$)
${
	fpm5.7_0 $f wff ph $.
	fpm5.7_1 $f wff ps $.
	fpm5.7_2 $f wff ch $.
	pm5.7 $p |- ( ( ( ph \/ ch ) <-> ( ps \/ ch ) ) <-> ( ch \/ ( ph <-> ps ) ) ) $= fpm5.7_2 fpm5.7_0 fpm5.7_1 wb wo fpm5.7_2 fpm5.7_0 wo fpm5.7_2 fpm5.7_1 wo wb fpm5.7_0 fpm5.7_2 wo fpm5.7_1 fpm5.7_2 wo wb fpm5.7_2 fpm5.7_0 fpm5.7_1 orbidi fpm5.7_2 fpm5.7_0 wo fpm5.7_0 fpm5.7_2 wo fpm5.7_2 fpm5.7_1 wo fpm5.7_1 fpm5.7_2 wo fpm5.7_2 fpm5.7_0 orcom fpm5.7_2 fpm5.7_1 orcom bibi12i bitr2i $.
$}
$( /* Dijkstra-Scholten's Golden Rule for calculational proofs.  (Contributed by
     NM, 10-Jan-2005.) */

$)
${
	fbigolden_0 $f wff ph $.
	fbigolden_1 $f wff ps $.
	bigolden $p |- ( ( ( ph /\ ps ) <-> ph ) <-> ( ps <-> ( ph \/ ps ) ) ) $= fbigolden_0 fbigolden_1 wi fbigolden_0 fbigolden_0 fbigolden_1 wa wb fbigolden_1 fbigolden_0 fbigolden_1 wo wb fbigolden_0 fbigolden_1 wa fbigolden_0 wb fbigolden_0 fbigolden_1 pm4.71 fbigolden_0 fbigolden_1 pm4.72 fbigolden_0 fbigolden_0 fbigolden_1 wa bicom 3bitr3ri $.
$}
$( /* Theorem *5.71 of [WhiteheadRussell] p. 125.  (Contributed by Roy F.
     Longton, 23-Jun-2005.) */

$)
${
	fpm5.71_0 $f wff ph $.
	fpm5.71_1 $f wff ps $.
	fpm5.71_2 $f wff ch $.
	pm5.71 $p |- ( ( ps -> -. ch ) -> ( ( ( ph \/ ps ) /\ ch ) <-> ( ph /\ ch ) ) ) $= fpm5.71_1 fpm5.71_2 wn fpm5.71_0 fpm5.71_1 wo fpm5.71_2 wa fpm5.71_0 fpm5.71_2 wa wb fpm5.71_1 wn fpm5.71_0 fpm5.71_1 wo fpm5.71_0 fpm5.71_2 fpm5.71_1 wn fpm5.71_0 fpm5.71_1 wo fpm5.71_0 fpm5.71_1 fpm5.71_0 orel2 fpm5.71_0 fpm5.71_1 orc impbid1 anbi1d fpm5.71_2 wn fpm5.71_2 fpm5.71_0 fpm5.71_1 wo fpm5.71_0 fpm5.71_2 fpm5.71_0 fpm5.71_1 wo fpm5.71_0 wb pm2.21 pm5.32rd ja $.
$}
$( /* Theorem *5.75 of [WhiteheadRussell] p. 126.  (Contributed by NM,
     3-Jan-2005.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 23-Dec-2012.) */

$)
${
	fpm5.75_0 $f wff ph $.
	fpm5.75_1 $f wff ps $.
	fpm5.75_2 $f wff ch $.
	pm5.75 $p |- ( ( ( ch -> -. ps ) /\ ( ph <-> ( ps \/ ch ) ) ) -> ( ( ph /\ -. ps ) <-> ch ) ) $= fpm5.75_0 fpm5.75_1 fpm5.75_2 wo wb fpm5.75_0 fpm5.75_1 wn wa fpm5.75_2 fpm5.75_1 wn wa fpm5.75_2 fpm5.75_1 wn wi fpm5.75_2 fpm5.75_0 fpm5.75_1 fpm5.75_2 wo wb fpm5.75_0 fpm5.75_1 wn wa fpm5.75_1 fpm5.75_2 wo fpm5.75_1 wn wa fpm5.75_2 fpm5.75_1 wn wa fpm5.75_0 fpm5.75_1 fpm5.75_2 wo fpm5.75_1 wn anbi1 fpm5.75_1 fpm5.75_2 wo fpm5.75_1 wn wa fpm5.75_2 fpm5.75_1 wo fpm5.75_1 wn wa fpm5.75_2 fpm5.75_1 wn wa fpm5.75_1 fpm5.75_2 wo fpm5.75_2 fpm5.75_1 wo fpm5.75_1 wn fpm5.75_1 fpm5.75_2 orcom anbi1i fpm5.75_2 fpm5.75_1 pm5.61 bitri syl6bb fpm5.75_2 fpm5.75_1 wn wi fpm5.75_2 fpm5.75_2 fpm5.75_1 wn wa fpm5.75_2 fpm5.75_1 wn wi fpm5.75_2 fpm5.75_2 fpm5.75_1 wn wa wb fpm5.75_2 fpm5.75_1 wn pm4.71 biimpi bicomd sylan9bbr $.
$}
$( /* Removal of conjunct from one side of an equivalence.  (Contributed by NM,
     5-Aug-1993.) */

$)
${
	fbimsc1_0 $f wff ph $.
	fbimsc1_1 $f wff ps $.
	fbimsc1_2 $f wff ch $.
	bimsc1 $p |- ( ( ( ph -> ps ) /\ ( ch <-> ( ps /\ ph ) ) ) -> ( ch <-> ph ) ) $= fbimsc1_0 fbimsc1_1 wi fbimsc1_2 fbimsc1_1 fbimsc1_0 wa wb fbimsc1_2 fbimsc1_0 wb fbimsc1_0 fbimsc1_1 wi fbimsc1_1 fbimsc1_0 wa fbimsc1_0 fbimsc1_2 fbimsc1_0 fbimsc1_1 wi fbimsc1_1 fbimsc1_0 wa fbimsc1_0 fbimsc1_1 fbimsc1_0 simpr fbimsc1_0 fbimsc1_1 ancr impbid2 bibi2d biimpa $.
$}
$( /* The disjunction of the four possible combinations of two wffs and their
     negations is always true.  (Contributed by David Abernethy,
     28-Jan-2014.) */

$)
${
	f4exmid_0 $f wff ph $.
	f4exmid_1 $f wff ps $.
	4exmid $p |- ( ( ( ph /\ ps ) \/ ( -. ph /\ -. ps ) ) \/ ( ( ph /\ -. ps ) \/ ( ps /\ -. ph ) ) ) $= f4exmid_0 f4exmid_1 wb f4exmid_0 f4exmid_1 wb wn wo f4exmid_0 f4exmid_1 wa f4exmid_0 wn f4exmid_1 wn wa wo f4exmid_0 f4exmid_1 wn wa f4exmid_1 f4exmid_0 wn wa wo wo f4exmid_0 f4exmid_1 wb exmid f4exmid_0 f4exmid_1 wb f4exmid_0 f4exmid_1 wa f4exmid_0 wn f4exmid_1 wn wa wo f4exmid_0 f4exmid_1 wb wn f4exmid_0 f4exmid_1 wn wa f4exmid_1 f4exmid_0 wn wa wo f4exmid_0 f4exmid_1 dfbi3 f4exmid_0 f4exmid_1 xor orbi12i mpbi $.
$}
$( /* Deduction for elimination by cases.  (Contributed by NM, 21-Apr-1994.)
       (Proof shortened by Wolf Lammen, 22-Dec-2012.) */

$)
${
	fecase2d_0 $f wff ph $.
	fecase2d_1 $f wff ps $.
	fecase2d_2 $f wff ch $.
	fecase2d_3 $f wff th $.
	fecase2d_4 $f wff ta $.
	eecase2d_0 $e |- ( ph -> ps ) $.
	eecase2d_1 $e |- ( ph -> -. ( ps /\ ch ) ) $.
	eecase2d_2 $e |- ( ph -> -. ( ps /\ th ) ) $.
	eecase2d_3 $e |- ( ph -> ( ta \/ ( ch \/ th ) ) ) $.
	ecase2d $p |- ( ph -> ta ) $= fecase2d_0 fecase2d_4 fecase2d_4 fecase2d_2 fecase2d_3 wo fecase2d_0 fecase2d_4 idd fecase2d_0 fecase2d_2 fecase2d_4 fecase2d_3 fecase2d_0 fecase2d_1 fecase2d_2 fecase2d_4 eecase2d_0 fecase2d_0 fecase2d_1 fecase2d_2 wa fecase2d_4 eecase2d_1 pm2.21d mpand fecase2d_0 fecase2d_1 fecase2d_3 fecase2d_4 eecase2d_0 fecase2d_0 fecase2d_1 fecase2d_3 wa fecase2d_4 eecase2d_2 pm2.21d mpand jaod eecase2d_3 mpjaod $.
$}
$( /* Inference for elimination by cases.  (Contributed by NM, 23-Mar-1995.)
       (Proof shortened by Wolf Lammen, 26-Nov-2012.) */

$)
${
	fecase3_0 $f wff ph $.
	fecase3_1 $f wff ps $.
	fecase3_2 $f wff ch $.
	eecase3_0 $e |- ( ph -> ch ) $.
	eecase3_1 $e |- ( ps -> ch ) $.
	eecase3_2 $e |- ( -. ( ph \/ ps ) -> ch ) $.
	ecase3 $p |- ch $= fecase3_0 fecase3_1 wo fecase3_2 fecase3_0 fecase3_2 fecase3_1 eecase3_0 eecase3_1 jaoi eecase3_2 pm2.61i $.
$}
$( /* Inference for elimination by cases.  (Contributed by NM,
       13-Jul-2005.) */

$)
${
	fecase_0 $f wff ph $.
	fecase_1 $f wff ps $.
	fecase_2 $f wff ch $.
	eecase_0 $e |- ( -. ph -> ch ) $.
	eecase_1 $e |- ( -. ps -> ch ) $.
	eecase_2 $e |- ( ( ph /\ ps ) -> ch ) $.
	ecase $p |- ch $= fecase_0 fecase_1 fecase_2 fecase_0 fecase_1 fecase_2 eecase_2 ex eecase_0 eecase_1 pm2.61nii $.
$}
$( /* Deduction for elimination by cases.  (Contributed by NM, 2-May-1996.)
       (Proof shortened by Andrew Salmon, 7-May-2011.) */

$)
${
	fecase3d_0 $f wff ph $.
	fecase3d_1 $f wff ps $.
	fecase3d_2 $f wff ch $.
	fecase3d_3 $f wff th $.
	eecase3d_0 $e |- ( ph -> ( ps -> th ) ) $.
	eecase3d_1 $e |- ( ph -> ( ch -> th ) ) $.
	eecase3d_2 $e |- ( ph -> ( -. ( ps \/ ch ) -> th ) ) $.
	ecase3d $p |- ( ph -> th ) $= fecase3d_0 fecase3d_1 fecase3d_2 wo fecase3d_3 fecase3d_0 fecase3d_1 fecase3d_3 fecase3d_2 eecase3d_0 eecase3d_1 jaod eecase3d_2 pm2.61d $.
$}
$( /* Deduction for elimination by cases.  (Contributed by NM, 8-Oct-2012.) */

$)
${
	fecased_0 $f wff ph $.
	fecased_1 $f wff ps $.
	fecased_2 $f wff ch $.
	fecased_3 $f wff th $.
	eecased_0 $e |- ( ph -> ( -. ps -> th ) ) $.
	eecased_1 $e |- ( ph -> ( -. ch -> th ) ) $.
	eecased_2 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	ecased $p |- ( ph -> th ) $= fecased_0 fecased_1 wn fecased_2 wn fecased_3 eecased_0 eecased_1 fecased_1 wn fecased_2 wn wo wn fecased_1 fecased_2 wa fecased_0 fecased_3 fecased_1 fecased_2 pm3.11 eecased_2 syl5 ecase3d $.
$}
$( /* Deduction for elimination by cases.  (Contributed by NM,
       24-May-2013.) */

$)
${
	fecase3ad_0 $f wff ph $.
	fecase3ad_1 $f wff ps $.
	fecase3ad_2 $f wff ch $.
	fecase3ad_3 $f wff th $.
	eecase3ad_0 $e |- ( ph -> ( ps -> th ) ) $.
	eecase3ad_1 $e |- ( ph -> ( ch -> th ) ) $.
	eecase3ad_2 $e |- ( ph -> ( ( -. ps /\ -. ch ) -> th ) ) $.
	ecase3ad $p |- ( ph -> th ) $= fecase3ad_0 fecase3ad_1 wn fecase3ad_2 wn fecase3ad_3 fecase3ad_1 wn wn fecase3ad_1 fecase3ad_0 fecase3ad_3 fecase3ad_1 notnot2 eecase3ad_0 syl5 fecase3ad_2 wn wn fecase3ad_2 fecase3ad_0 fecase3ad_3 fecase3ad_2 notnot2 eecase3ad_1 syl5 eecase3ad_2 ecased $.
$}
$( /* Inference for combining cases.  (Contributed by NM, 29-Jul-1999.)
       (Proof shortened by Wolf Lammen, 6-Jan-2013.) */

$)
${
	fccase_0 $f wff ph $.
	fccase_1 $f wff ps $.
	fccase_2 $f wff ch $.
	fccase_3 $f wff th $.
	fccase_4 $f wff ta $.
	eccase_0 $e |- ( ( ph /\ ps ) -> ta ) $.
	eccase_1 $e |- ( ( ch /\ ps ) -> ta ) $.
	eccase_2 $e |- ( ( ph /\ th ) -> ta ) $.
	eccase_3 $e |- ( ( ch /\ th ) -> ta ) $.
	ccase $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $= fccase_0 fccase_2 wo fccase_1 fccase_4 fccase_3 fccase_0 fccase_1 fccase_4 fccase_2 eccase_0 eccase_1 jaoian fccase_0 fccase_3 fccase_4 fccase_2 eccase_2 eccase_3 jaoian jaodan $.
$}
$( /* Deduction for combining cases.  (Contributed by NM, 9-May-2004.) */

$)
${
	fccased_0 $f wff ph $.
	fccased_1 $f wff ps $.
	fccased_2 $f wff ch $.
	fccased_3 $f wff th $.
	fccased_4 $f wff ta $.
	fccased_5 $f wff et $.
	eccased_0 $e |- ( ph -> ( ( ps /\ ch ) -> et ) ) $.
	eccased_1 $e |- ( ph -> ( ( th /\ ch ) -> et ) ) $.
	eccased_2 $e |- ( ph -> ( ( ps /\ ta ) -> et ) ) $.
	eccased_3 $e |- ( ph -> ( ( th /\ ta ) -> et ) ) $.
	ccased $p |- ( ph -> ( ( ( ps \/ th ) /\ ( ch \/ ta ) ) -> et ) ) $= fccased_1 fccased_3 wo fccased_2 fccased_4 wo wa fccased_0 fccased_5 fccased_1 fccased_2 fccased_3 fccased_4 fccased_0 fccased_5 wi fccased_0 fccased_1 fccased_2 wa fccased_5 eccased_0 com12 fccased_0 fccased_3 fccased_2 wa fccased_5 eccased_1 com12 fccased_0 fccased_1 fccased_4 wa fccased_5 eccased_2 com12 fccased_0 fccased_3 fccased_4 wa fccased_5 eccased_3 com12 ccase com12 $.
$}
$( /* Inference for combining cases.  (Contributed by NM, 29-Jul-1999.) */

$)
${
	fccase2_0 $f wff ph $.
	fccase2_1 $f wff ps $.
	fccase2_2 $f wff ch $.
	fccase2_3 $f wff th $.
	fccase2_4 $f wff ta $.
	eccase2_0 $e |- ( ( ph /\ ps ) -> ta ) $.
	eccase2_1 $e |- ( ch -> ta ) $.
	eccase2_2 $e |- ( th -> ta ) $.
	ccase2 $p |- ( ( ( ph \/ ch ) /\ ( ps \/ th ) ) -> ta ) $= fccase2_0 fccase2_1 fccase2_2 fccase2_3 fccase2_4 eccase2_0 fccase2_2 fccase2_4 fccase2_1 eccase2_1 adantr fccase2_3 fccase2_4 fccase2_0 eccase2_2 adantl fccase2_3 fccase2_4 fccase2_2 eccase2_2 adantl ccase $.
$}
$( /* Inference eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       25-Oct-2003.) */

$)
${
	f4cases_0 $f wff ph $.
	f4cases_1 $f wff ps $.
	f4cases_2 $f wff ch $.
	e4cases_0 $e |- ( ( ph /\ ps ) -> ch ) $.
	e4cases_1 $e |- ( ( ph /\ -. ps ) -> ch ) $.
	e4cases_2 $e |- ( ( -. ph /\ ps ) -> ch ) $.
	e4cases_3 $e |- ( ( -. ph /\ -. ps ) -> ch ) $.
	4cases $p |- ch $= f4cases_1 f4cases_2 f4cases_0 f4cases_1 f4cases_2 e4cases_0 e4cases_2 pm2.61ian f4cases_0 f4cases_1 wn f4cases_2 e4cases_1 e4cases_3 pm2.61ian pm2.61i $.
$}
$( /* Deduction eliminating two antecedents from the four possible cases that
       result from their true/false combinations.  (Contributed by NM,
       19-Mar-2013.) */

$)
${
	f4casesdan_0 $f wff ph $.
	f4casesdan_1 $f wff ps $.
	f4casesdan_2 $f wff ch $.
	f4casesdan_3 $f wff th $.
	e4casesdan_0 $e |- ( ( ph /\ ( ps /\ ch ) ) -> th ) $.
	e4casesdan_1 $e |- ( ( ph /\ ( ps /\ -. ch ) ) -> th ) $.
	e4casesdan_2 $e |- ( ( ph /\ ( -. ps /\ ch ) ) -> th ) $.
	e4casesdan_3 $e |- ( ( ph /\ ( -. ps /\ -. ch ) ) -> th ) $.
	4casesdan $p |- ( ph -> th ) $= f4casesdan_1 f4casesdan_2 f4casesdan_0 f4casesdan_3 wi f4casesdan_0 f4casesdan_1 f4casesdan_2 wa f4casesdan_3 e4casesdan_0 expcom f4casesdan_0 f4casesdan_1 f4casesdan_2 wn wa f4casesdan_3 e4casesdan_1 expcom f4casesdan_0 f4casesdan_1 wn f4casesdan_2 wa f4casesdan_3 e4casesdan_2 expcom f4casesdan_0 f4casesdan_1 wn f4casesdan_2 wn wa f4casesdan_3 e4casesdan_3 expcom 4cases $.
$}
$( /* Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) */

$)
${
	fniabn_0 $f wff ph $.
	fniabn_1 $f wff ps $.
	fniabn_2 $f wff ch $.
	eniabn_0 $e |- ph $.
	niabn $p |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) ) $= fniabn_2 fniabn_1 wa fniabn_1 fniabn_0 wn fniabn_2 fniabn_1 simpr fniabn_0 fniabn_1 eniabn_0 pm2.24i pm5.21ni $.
$}
$( /* Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.)  (Proof shortened by Andrew Salmon, 7-May-2011.)  (Proof
     shortened by Wolf Lammen, 4-Dec-2012.) */

$)
${
	fdedlem0a_0 $f wff ph $.
	fdedlem0a_1 $f wff ps $.
	fdedlem0a_2 $f wff ch $.
	dedlem0a $p |- ( ph -> ( ps <-> ( ( ch -> ph ) -> ( ps /\ ph ) ) ) ) $= fdedlem0a_0 fdedlem0a_1 fdedlem0a_1 fdedlem0a_0 wa fdedlem0a_2 fdedlem0a_0 wi fdedlem0a_1 fdedlem0a_0 wa wi fdedlem0a_0 fdedlem0a_1 iba fdedlem0a_0 fdedlem0a_2 fdedlem0a_0 wi fdedlem0a_1 fdedlem0a_0 wa fdedlem0a_2 fdedlem0a_0 wi fdedlem0a_1 fdedlem0a_0 wa wi wb fdedlem0a_0 fdedlem0a_2 ax-1 fdedlem0a_2 fdedlem0a_0 wi fdedlem0a_1 fdedlem0a_0 wa biimt syl bitrd $.
$}
$( /* Lemma for an alternate version of weak deduction theorem.  (Contributed by
     NM, 2-Apr-1994.) */

$)
${
	fdedlem0b_0 $f wff ph $.
	fdedlem0b_1 $f wff ps $.
	fdedlem0b_2 $f wff ch $.
	dedlem0b $p |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) ) $= fdedlem0b_0 wn fdedlem0b_1 fdedlem0b_1 fdedlem0b_0 wi fdedlem0b_2 fdedlem0b_0 wa wi fdedlem0b_0 wn fdedlem0b_1 fdedlem0b_0 wi fdedlem0b_1 fdedlem0b_2 fdedlem0b_0 wa fdedlem0b_0 wn fdedlem0b_0 fdedlem0b_2 fdedlem0b_0 wa fdedlem0b_1 fdedlem0b_0 fdedlem0b_2 fdedlem0b_0 wa pm2.21 imim2d com23 fdedlem0b_1 fdedlem0b_0 wi fdedlem0b_2 fdedlem0b_0 wa wi fdedlem0b_0 wn fdedlem0b_1 fdedlem0b_1 fdedlem0b_0 wi fdedlem0b_2 fdedlem0b_0 wa wi fdedlem0b_1 fdedlem0b_0 fdedlem0b_1 wn fdedlem0b_1 fdedlem0b_0 wi fdedlem0b_2 fdedlem0b_0 wa fdedlem0b_0 fdedlem0b_1 fdedlem0b_0 pm2.21 fdedlem0b_2 fdedlem0b_0 simpr imim12i con1d com12 impbid $.
$}
$( /* Lemma for weak deduction theorem.  (Contributed by NM, 26-Jun-2002.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) */

$)
${
	fdedlema_0 $f wff ph $.
	fdedlema_1 $f wff ps $.
	fdedlema_2 $f wff ch $.
	dedlema $p |- ( ph -> ( ps <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $= fdedlema_0 fdedlema_1 fdedlema_1 fdedlema_0 wa fdedlema_2 fdedlema_0 wn wa wo fdedlema_1 fdedlema_0 fdedlema_1 fdedlema_0 wa fdedlema_2 fdedlema_0 wn wa wo fdedlema_1 fdedlema_0 wa fdedlema_2 fdedlema_0 wn wa orc expcom fdedlema_0 fdedlema_1 fdedlema_0 wa fdedlema_1 fdedlema_2 fdedlema_0 wn wa fdedlema_1 fdedlema_0 wa fdedlema_1 wi fdedlema_0 fdedlema_1 fdedlema_0 simpl a1i fdedlema_0 fdedlema_0 wn fdedlema_1 fdedlema_2 fdedlema_0 fdedlema_1 pm2.24 adantld jaod impbid $.
$}
$( /* Lemma for weak deduction theorem.  (Contributed by NM, 15-May-1999.)
     (Proof shortened by Andrew Salmon, 7-May-2011.) */

$)
${
	fdedlemb_0 $f wff ph $.
	fdedlemb_1 $f wff ps $.
	fdedlemb_2 $f wff ch $.
	dedlemb $p |- ( -. ph -> ( ch <-> ( ( ps /\ ph ) \/ ( ch /\ -. ph ) ) ) ) $= fdedlemb_0 wn fdedlemb_2 fdedlemb_1 fdedlemb_0 wa fdedlemb_2 fdedlemb_0 wn wa wo fdedlemb_2 fdedlemb_0 wn fdedlemb_1 fdedlemb_0 wa fdedlemb_2 fdedlemb_0 wn wa wo fdedlemb_2 fdedlemb_0 wn wa fdedlemb_1 fdedlemb_0 wa olc expcom fdedlemb_0 wn fdedlemb_1 fdedlemb_0 wa fdedlemb_2 fdedlemb_2 fdedlemb_0 wn wa fdedlemb_0 wn fdedlemb_0 fdedlemb_2 fdedlemb_1 fdedlemb_0 fdedlemb_2 pm2.21 adantld fdedlemb_2 fdedlemb_0 wn wa fdedlemb_2 wi fdedlemb_0 wn fdedlemb_2 fdedlemb_0 wn simpl a1i jaod impbid $.
$}
$( /* Hypothesis builder for weak deduction theorem.  For more information,
       see the Deduction Theorem link on the Metamath Proof Explorer home
       page.  (Contributed by NM, 26-Jun-2002.) */

$)
${
	felimh_0 $f wff ph $.
	felimh_1 $f wff ps $.
	felimh_2 $f wff ch $.
	felimh_3 $f wff th $.
	felimh_4 $f wff ta $.
	eelimh_0 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) -> ( ch <-> ta ) ) $.
	eelimh_1 $e |- ( ( ps <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) -> ( th <-> ta ) ) $.
	eelimh_2 $e |- th $.
	elimh $p |- ta $= felimh_2 felimh_4 felimh_2 felimh_4 felimh_2 felimh_0 felimh_0 felimh_2 wa felimh_1 felimh_2 wn wa wo wb felimh_2 felimh_4 wb felimh_2 felimh_0 felimh_1 dedlema eelimh_0 syl ibi felimh_2 wn felimh_3 felimh_4 eelimh_2 felimh_2 wn felimh_1 felimh_0 felimh_2 wa felimh_1 felimh_2 wn wa wo wb felimh_3 felimh_4 wb felimh_2 felimh_0 felimh_1 dedlemb eelimh_1 syl mpbii pm2.61i $.
$}
$( /* The weak deduction theorem.  For more information, see the Deduction
       Theorem link on the Metamath Proof Explorer home page.  (Contributed by
       NM, 26-Jun-2002.) */

$)
${
	fdedt_0 $f wff ph $.
	fdedt_1 $f wff ps $.
	fdedt_2 $f wff ch $.
	fdedt_3 $f wff th $.
	fdedt_4 $f wff ta $.
	ededt_0 $e |- ( ( ph <-> ( ( ph /\ ch ) \/ ( ps /\ -. ch ) ) ) -> ( th <-> ta ) ) $.
	ededt_1 $e |- ta $.
	dedt $p |- ( ch -> th ) $= fdedt_2 fdedt_0 fdedt_0 fdedt_2 wa fdedt_1 fdedt_2 wn wa wo wb fdedt_3 fdedt_2 fdedt_0 fdedt_1 dedlema fdedt_0 fdedt_0 fdedt_2 wa fdedt_1 fdedt_2 wn wa wo wb fdedt_3 fdedt_4 ededt_1 ededt_0 mpbiri syl $.
$}
$( /* Contraposition.  Theorem *2.16 of [WhiteheadRussell] p. 103.  This version
     of ~ con3 demonstrates the use of the weak deduction theorem ~ dedt to
     derive it from ~ con3i .  (Contributed by NM, 27-Jun-2002.)
     (Proof modification is discouraged.) */

$)
${
	fcon3th_0 $f wff ph $.
	fcon3th_1 $f wff ps $.
	con3th $p |- ( ( ph -> ps ) -> ( -. ps -> -. ph ) ) $= fcon3th_1 fcon3th_0 fcon3th_0 fcon3th_1 wi fcon3th_1 wn fcon3th_0 wn wi fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wn fcon3th_0 wn wi fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb fcon3th_1 wn fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wn fcon3th_0 wn fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb id notbid imbi1d fcon3th_0 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo fcon3th_1 fcon3th_0 fcon3th_0 fcon3th_1 wi fcon3th_0 fcon3th_0 wi fcon3th_0 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wi fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo fcon3th_0 fcon3th_1 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb id imbi2d fcon3th_0 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb fcon3th_0 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo fcon3th_0 fcon3th_0 fcon3th_1 fcon3th_0 fcon3th_1 wi wa fcon3th_0 fcon3th_0 fcon3th_1 wi wn wa wo wb id imbi2d fcon3th_0 id elimh con3i dedt $.
$}
$( /* The consensus theorem.  This theorem and its dual (with ` \/ ` and ` /\ `
     interchanged) are commonly used in computer logic design to eliminate
     redundant terms from Boolean expressions.  Specifically, we prove that the
     term ` ( ps /\ ch ) ` on the left-hand side is redundant.  (Contributed by
     NM, 16-May-2003.)  (Proof shortened by Andrew Salmon, 13-May-2011.)
     (Proof shortened by Wolf Lammen, 20-Jan-2013.) */

$)
${
	fconsensus_0 $f wff ph $.
	fconsensus_1 $f wff ps $.
	fconsensus_2 $f wff ch $.
	consensus $p |- ( ( ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) \/ ( ps /\ ch ) ) <-> ( ( ph /\ ps ) \/ ( -. ph /\ ch ) ) ) $= fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_1 fconsensus_2 wa wo fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_1 fconsensus_2 wa fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo id fconsensus_0 fconsensus_1 fconsensus_2 wa fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_0 fconsensus_1 fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_2 fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa orc adantrr fconsensus_0 wn fconsensus_2 fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_1 fconsensus_0 wn fconsensus_2 wa fconsensus_0 fconsensus_1 wa olc adantrl pm2.61ian jaoi fconsensus_0 fconsensus_1 wa fconsensus_0 wn fconsensus_2 wa wo fconsensus_1 fconsensus_2 wa orc impbii $.
$}
$( /* Theorem *4.42 of [WhiteheadRussell] p. 119.  (Contributed by Roy F.
     Longton, 21-Jun-2005.) */

$)
${
	fpm4.42_0 $f wff ph $.
	fpm4.42_1 $f wff ps $.
	pm4.42 $p |- ( ph <-> ( ( ph /\ ps ) \/ ( ph /\ -. ps ) ) ) $= fpm4.42_1 fpm4.42_0 fpm4.42_0 fpm4.42_1 wa fpm4.42_0 fpm4.42_1 wn wa wo wb fpm4.42_1 fpm4.42_0 fpm4.42_0 dedlema fpm4.42_1 fpm4.42_0 fpm4.42_0 dedlemb pm2.61i $.
$}
$( /* Miscellaneous inference relating falsehoods.  (Contributed by NM,
       31-Mar-1994.) */

$)
${
	fninba_0 $f wff ph $.
	fninba_1 $f wff ps $.
	fninba_2 $f wff ch $.
	eninba_0 $e |- ph $.
	ninba $p |- ( -. ps -> ( -. ph <-> ( ch /\ ps ) ) ) $= fninba_1 wn fninba_2 fninba_1 wa fninba_0 wn fninba_0 fninba_1 fninba_2 eninba_0 niabn bicomd $.
$}
$( /* A specialized lemma for set theory (to derive the Axiom of Pairing).
       (Contributed by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       13-May-2011.)  (Proof shortened by Wolf Lammen, 5-Jan-2013.) */

$)
${
	fprlem1_0 $f wff ph $.
	fprlem1_1 $f wff ps $.
	fprlem1_2 $f wff ch $.
	fprlem1_3 $f wff th $.
	fprlem1_4 $f wff ta $.
	fprlem1_5 $f wff et $.
	eprlem1_0 $e |- ( ph -> ( et <-> ch ) ) $.
	eprlem1_1 $e |- ( ps -> -. th ) $.
	prlem1 $p |- ( ph -> ( ps -> ( ( ( ps /\ ch ) \/ ( th /\ ta ) ) -> et ) ) ) $= fprlem1_0 fprlem1_1 fprlem1_1 fprlem1_2 wa fprlem1_3 fprlem1_4 wa wo fprlem1_5 wi fprlem1_0 fprlem1_1 fprlem1_2 wa fprlem1_5 fprlem1_1 fprlem1_3 fprlem1_4 wa fprlem1_0 fprlem1_2 fprlem1_5 fprlem1_1 fprlem1_0 fprlem1_5 fprlem1_2 eprlem1_0 biimprd adantld fprlem1_1 fprlem1_3 fprlem1_5 fprlem1_4 fprlem1_1 fprlem1_3 fprlem1_5 eprlem1_1 pm2.21d adantrd jaao ex $.
$}
$( /* A specialized lemma for set theory (to derive the Axiom of Pairing).
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     13-May-2011.)  (Proof shortened by Wolf Lammen, 9-Dec-2012.) */

$)
${
	fprlem2_0 $f wff ph $.
	fprlem2_1 $f wff ps $.
	fprlem2_2 $f wff ch $.
	fprlem2_3 $f wff th $.
	prlem2 $p |- ( ( ( ph /\ ps ) \/ ( ch /\ th ) ) <-> ( ( ph \/ ch ) /\ ( ( ph /\ ps ) \/ ( ch /\ th ) ) ) ) $= fprlem2_0 fprlem2_1 wa fprlem2_2 fprlem2_3 wa wo fprlem2_0 fprlem2_2 wo fprlem2_0 fprlem2_1 wa fprlem2_0 fprlem2_2 fprlem2_3 wa fprlem2_2 fprlem2_0 fprlem2_1 simpl fprlem2_2 fprlem2_3 simpl orim12i pm4.71ri $.
$}
$( /* A specialized lemma for set theory (ordered pair theorem).  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Wolf Lammen, 8-Dec-2012.) */

$)
${
	foplem1_0 $f wff ph $.
	foplem1_1 $f wff ps $.
	foplem1_2 $f wff ch $.
	foplem1_3 $f wff th $.
	foplem1_4 $f wff ta $.
	eoplem1_0 $e |- ( ph -> ( ps \/ ch ) ) $.
	eoplem1_1 $e |- ( ph -> ( th \/ ta ) ) $.
	eoplem1_2 $e |- ( ps <-> th ) $.
	eoplem1_3 $e |- ( ch -> ( th <-> ta ) ) $.
	oplem1 $p |- ( ph -> ps ) $= foplem1_0 foplem1_3 foplem1_1 foplem1_0 foplem1_3 foplem1_0 foplem1_3 wn foplem1_2 foplem1_4 wa foplem1_3 foplem1_0 foplem1_3 wn foplem1_2 foplem1_4 foplem1_3 wn foplem1_1 wn foplem1_0 foplem1_2 foplem1_1 foplem1_3 eoplem1_2 notbii foplem1_0 foplem1_1 foplem1_2 eoplem1_0 ord syl5bir foplem1_0 foplem1_3 foplem1_4 eoplem1_1 ord jcad foplem1_2 foplem1_3 foplem1_4 eoplem1_3 biimpar syl6 pm2.18d eoplem1_2 sylibr $.
$}
$( /* Lemma used in construction of real numbers.  (Contributed by NM,
     4-Sep-1995.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) */

$)
${
	frnlem_0 $f wff ph $.
	frnlem_1 $f wff ps $.
	frnlem_2 $f wff ch $.
	frnlem_3 $f wff th $.
	rnlem $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) <-> ( ( ( ph /\ ch ) /\ ( ps /\ th ) ) /\ ( ( ph /\ th ) /\ ( ps /\ ch ) ) ) ) $= frnlem_0 frnlem_1 wa frnlem_2 frnlem_3 wa wa frnlem_0 frnlem_2 wa frnlem_1 frnlem_3 wa wa frnlem_0 frnlem_3 wa frnlem_1 frnlem_2 wa wa wa frnlem_0 frnlem_1 wa frnlem_2 frnlem_3 wa wa frnlem_0 frnlem_2 wa frnlem_1 frnlem_3 wa wa frnlem_0 frnlem_3 wa frnlem_1 frnlem_2 wa wa frnlem_0 frnlem_1 wa frnlem_2 frnlem_3 wa wa frnlem_0 frnlem_2 wa frnlem_1 frnlem_3 wa wa frnlem_0 frnlem_1 frnlem_2 frnlem_3 an4 biimpi frnlem_0 frnlem_3 wa frnlem_1 frnlem_2 wa wa frnlem_0 frnlem_1 wa frnlem_2 frnlem_3 wa wa frnlem_0 frnlem_3 frnlem_1 frnlem_2 an42 biimpri jca frnlem_0 frnlem_3 wa frnlem_1 frnlem_2 wa wa frnlem_0 frnlem_1 wa frnlem_2 frnlem_3 wa wa frnlem_0 frnlem_2 wa frnlem_1 frnlem_3 wa wa frnlem_0 frnlem_3 wa frnlem_1 frnlem_2 wa wa frnlem_0 frnlem_1 wa frnlem_2 frnlem_3 wa wa frnlem_0 frnlem_3 frnlem_1 frnlem_2 an42 biimpi adantl impbii $.
$}
$( /* A single axiom for Boolean algebra known as DN_1.  See
     ~ http://www-unix.mcs.anl.gov/~~mccune/papers/basax/v12.pdf .
     (Contributed by Jeffrey Hankins, 3-Jul-2009.)  (Proof shortened by Andrew
     Salmon, 13-May-2011.)  (Proof shortened by Wolf Lammen, 6-Jan-2013.) */

$)
${
	fdn1_0 $f wff ph $.
	fdn1_1 $f wff ps $.
	fdn1_2 $f wff ch $.
	fdn1_3 $f wff th $.
	dn1 $p |- ( -. ( -. ( -. ( ph \/ ps ) \/ ch ) \/ -. ( ph \/ -. ( -. ch \/ -. ( ch \/ th ) ) ) ) <-> ch ) $= fdn1_2 fdn1_0 fdn1_1 wo wn fdn1_2 wo fdn1_0 fdn1_2 wo wa fdn1_0 fdn1_1 wo wn fdn1_2 wo fdn1_0 fdn1_2 wn fdn1_2 fdn1_3 wo wn wo wn wo wa fdn1_0 fdn1_1 wo wn fdn1_2 wo wn fdn1_0 fdn1_2 wn fdn1_2 fdn1_3 wo wn wo wn wo wn wo wn fdn1_2 fdn1_2 fdn1_0 fdn1_1 wo wn fdn1_0 wa wo fdn1_0 fdn1_1 wo wn fdn1_2 wo fdn1_0 fdn1_2 wo wa fdn1_0 fdn1_1 wo wn fdn1_0 wa fdn1_2 fdn1_0 fdn1_1 wo wn fdn1_0 wn wi fdn1_0 fdn1_1 wo wn fdn1_0 wa wn fdn1_0 fdn1_1 pm2.45 fdn1_0 fdn1_1 wo wn fdn1_0 imnan mpbi biorfi fdn1_2 fdn1_0 fdn1_1 wo wn fdn1_0 wa wo fdn1_0 fdn1_1 wo wn fdn1_0 wa fdn1_2 wo fdn1_0 fdn1_1 wo wn fdn1_2 wo fdn1_0 fdn1_2 wo wa fdn1_2 fdn1_0 fdn1_1 wo wn fdn1_0 wa orcom fdn1_0 fdn1_1 wo wn fdn1_0 fdn1_2 ordir bitri bitri fdn1_0 fdn1_2 wo fdn1_0 fdn1_2 wn fdn1_2 fdn1_3 wo wn wo wn wo fdn1_0 fdn1_1 wo wn fdn1_2 wo fdn1_2 fdn1_2 wn fdn1_2 fdn1_3 wo wn wo wn fdn1_0 fdn1_2 fdn1_2 fdn1_2 fdn1_3 wo wa fdn1_2 wn fdn1_2 fdn1_3 wo wn wo wn fdn1_2 fdn1_3 pm4.45 fdn1_2 fdn1_2 fdn1_3 wo anor bitri orbi2i anbi2i fdn1_0 fdn1_1 wo wn fdn1_2 wo fdn1_0 fdn1_2 wn fdn1_2 fdn1_3 wo wn wo wn wo anor 3bitrri $.
$}

