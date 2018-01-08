$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Truth_tables.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Auxiliary theorems for Alan Sare's virtual deduction tool, part 1

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
*/

$)
$( /* Virtual deduction rule ~ e22 without virtual deduction connectives.
       Special theorem needed for Alan Sare's virtual deduction translation
       tool.  (Contributed by Alan Sare, 2-May-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. */

$)
${
	fee22_0 $f wff ph $.
	fee22_1 $f wff ps $.
	fee22_2 $f wff ch $.
	fee22_3 $f wff th $.
	fee22_4 $f wff ta $.
	eee22_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eee22_1 $e |- ( ph -> ( ps -> th ) ) $.
	eee22_2 $e |- ( ch -> ( th -> ta ) ) $.
	ee22 $p |- ( ph -> ( ps -> ta ) ) $= fee22_0 fee22_1 fee22_2 fee22_3 fee22_4 eee22_0 eee22_1 eee22_2 syl6c $.
$}
$( /* ~ e12an without virtual deduction connectives.  Special theorem needed
       for Alan Sare's virtual deduction translation tool.  (Contributed by
       Alan Sare, 28-Oct-2011.)  TODO: this is frequently used; come up with
       better label. */

$)
${
	fee12an_0 $f wff ph $.
	fee12an_1 $f wff ps $.
	fee12an_2 $f wff ch $.
	fee12an_3 $f wff th $.
	fee12an_4 $f wff ta $.
	eee12an_0 $e |- ( ph -> ps ) $.
	eee12an_1 $e |- ( ph -> ( ch -> th ) ) $.
	eee12an_2 $e |- ( ( ps /\ th ) -> ta ) $.
	ee12an $p |- ( ph -> ( ch -> ta ) ) $= fee12an_0 fee12an_2 fee12an_1 fee12an_3 wa fee12an_4 fee12an_0 fee12an_2 fee12an_3 fee12an_1 eee12an_1 eee12an_0 jctild eee12an_2 syl6 $.
$}
$( /* ~ e23 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. */

$)
${
	fee23_0 $f wff ph $.
	fee23_1 $f wff ps $.
	fee23_2 $f wff ch $.
	fee23_3 $f wff th $.
	fee23_4 $f wff ta $.
	fee23_5 $f wff et $.
	eee23_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eee23_1 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
	eee23_2 $e |- ( ch -> ( ta -> et ) ) $.
	ee23 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $= fee23_0 fee23_1 fee23_3 fee23_4 fee23_5 eee23_1 fee23_0 fee23_1 fee23_2 fee23_4 fee23_5 wi eee23_0 eee23_2 syl6 syldd $.
$}
$( /* Exportation implication also converting head from biconditional to
     conditional.  This proof is ~ exbirVD automatically translated and
     minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
     (New usage is discouraged.)  TODO: decide if this is worth keeping. */

$)
${
	fexbir_0 $f wff ph $.
	fexbir_1 $f wff ps $.
	fexbir_2 $f wff ch $.
	fexbir_3 $f wff th $.
	exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $= fexbir_0 fexbir_1 wa fexbir_2 fexbir_3 wb wi fexbir_0 fexbir_1 fexbir_3 fexbir_2 wi fexbir_2 fexbir_3 wb fexbir_3 fexbir_2 wi fexbir_0 fexbir_1 wa fexbir_2 fexbir_3 bi2 imim2i exp3a $.
$}
$( /* ~ impexp with a 3-conjunct antecedent.  (Contributed by Alan Sare,
     31-Dec-2011.) */

$)
${
	f3impexp_0 $f wff ph $.
	f3impexp_1 $f wff ps $.
	f3impexp_2 $f wff ch $.
	f3impexp_3 $f wff th $.
	3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) ) $= f3impexp_0 f3impexp_1 f3impexp_2 w3a f3impexp_3 wi f3impexp_0 f3impexp_1 f3impexp_2 f3impexp_3 wi wi wi f3impexp_0 f3impexp_1 f3impexp_2 w3a f3impexp_3 wi f3impexp_0 f3impexp_1 f3impexp_2 f3impexp_3 f3impexp_0 f3impexp_1 f3impexp_2 w3a f3impexp_3 wi id 3expd f3impexp_0 f3impexp_1 f3impexp_2 f3impexp_3 wi wi wi f3impexp_0 f3impexp_1 f3impexp_2 f3impexp_3 f3impexp_0 f3impexp_1 f3impexp_2 f3impexp_3 wi wi wi id 3impd impbii $.
$}
$( /* ~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  Derived automatically from ~ 3impexpVD .  (Contributed by
     Alan Sare, 31-Dec-2011.)  (New usage is discouraged.)  TODO: decide if
     this is worth keeping. */

$)
${
	f3impexpbicom_0 $f wff ph $.
	f3impexpbicom_1 $f wff ps $.
	f3impexpbicom_2 $f wff ch $.
	f3impexpbicom_3 $f wff th $.
	f3impexpbicom_4 $f wff ta $.
	3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <-> ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $= f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_3 f3impexpbicom_4 wb wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 f3impexpbicom_4 f3impexpbicom_3 wb wi wi wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_3 f3impexpbicom_4 wb wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 f3impexpbicom_4 f3impexpbicom_3 wb f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_3 f3impexpbicom_4 wb wi f3impexpbicom_3 f3impexpbicom_4 wb f3impexpbicom_4 f3impexpbicom_3 wb wb f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_4 f3impexpbicom_3 wb wi f3impexpbicom_3 f3impexpbicom_4 bicom f3impexpbicom_3 f3impexpbicom_4 wb f3impexpbicom_4 f3impexpbicom_3 wb wb f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_3 f3impexpbicom_4 wb wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_4 f3impexpbicom_3 wb wi f3impexpbicom_3 f3impexpbicom_4 wb f3impexpbicom_4 f3impexpbicom_3 wb f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a imbi2 biimpcd mpi 3expd f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 f3impexpbicom_4 f3impexpbicom_3 wb wi wi wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_4 f3impexpbicom_3 wb f3impexpbicom_3 f3impexpbicom_4 wb f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 w3a f3impexpbicom_4 f3impexpbicom_3 wb wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 f3impexpbicom_4 f3impexpbicom_3 wb wi wi wi f3impexpbicom_0 f3impexpbicom_1 f3impexpbicom_2 f3impexpbicom_4 f3impexpbicom_3 wb 3impexp biimpri f3impexpbicom_3 f3impexpbicom_4 bicom syl6ibr impbii $.
$}
$( /* Deduction form of ~ 3impexpbicom .  Derived automatically from
       ~ 3impexpbicomiVD .  (Contributed by Alan Sare, 31-Dec-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. */

$)
${
	f3impexpbicomi_0 $f wff ph $.
	f3impexpbicomi_1 $f wff ps $.
	f3impexpbicomi_2 $f wff ch $.
	f3impexpbicomi_3 $f wff th $.
	f3impexpbicomi_4 $f wff ta $.
	e3impexpbicomi_0 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
	3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $= f3impexpbicomi_0 f3impexpbicomi_1 f3impexpbicomi_2 f3impexpbicomi_4 f3impexpbicomi_3 wb f3impexpbicomi_0 f3impexpbicomi_1 f3impexpbicomi_2 w3a f3impexpbicomi_3 f3impexpbicomi_4 e3impexpbicomi_0 bicomd 3exp $.
$}
$( /* Closed form of ~ ancoms .  Derived automatically from ~ ancomsimpVD .
     (Contributed by Alan Sare, 31-Dec-2011.) */

$)
${
	fancomsimp_0 $f wff ph $.
	fancomsimp_1 $f wff ps $.
	fancomsimp_2 $f wff ch $.
	ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $= fancomsimp_0 fancomsimp_1 wa fancomsimp_1 fancomsimp_0 wa fancomsimp_2 fancomsimp_0 fancomsimp_1 ancom imbi1i $.
$}
$( /* Export and commute antecedents.  (Contributed by Alan Sare,
       18-Mar-2012.) */

$)
${
	fexp3acom3r_0 $f wff ph $.
	fexp3acom3r_1 $f wff ps $.
	fexp3acom3r_2 $f wff ch $.
	fexp3acom3r_3 $f wff th $.
	eexp3acom3r_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	exp3acom3r $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $= fexp3acom3r_0 fexp3acom3r_1 fexp3acom3r_2 fexp3acom3r_3 fexp3acom3r_0 fexp3acom3r_1 fexp3acom3r_2 fexp3acom3r_3 eexp3acom3r_0 exp3a com3l $.
$}
$( /* Implication form of ~ exp3acom23 .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. */

$)
${
	fexp3acom23g_0 $f wff ph $.
	fexp3acom23g_1 $f wff ps $.
	fexp3acom23g_2 $f wff ch $.
	fexp3acom23g_3 $f wff th $.
	exp3acom23g $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <-> ( ph -> ( ch -> ( ps -> th ) ) ) ) $= fexp3acom23g_1 fexp3acom23g_2 wa fexp3acom23g_3 wi fexp3acom23g_2 fexp3acom23g_1 fexp3acom23g_3 wi wi fexp3acom23g_0 fexp3acom23g_1 fexp3acom23g_2 wa fexp3acom23g_3 wi fexp3acom23g_2 fexp3acom23g_1 wa fexp3acom23g_3 wi fexp3acom23g_2 fexp3acom23g_1 fexp3acom23g_3 wi wi fexp3acom23g_1 fexp3acom23g_2 fexp3acom23g_3 ancomsimp fexp3acom23g_2 fexp3acom23g_1 fexp3acom23g_3 impexp bitri imbi2i $.
$}
$( /* The exportation deduction ~ exp3a with commutation of the conjoined
       wwfs.  (Contributed by Alan Sare, 22-Jul-2012.) */

$)
${
	fexp3acom23_0 $f wff ph $.
	fexp3acom23_1 $f wff ps $.
	fexp3acom23_2 $f wff ch $.
	fexp3acom23_3 $f wff th $.
	eexp3acom23_0 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	exp3acom23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $= fexp3acom23_0 fexp3acom23_1 fexp3acom23_2 fexp3acom23_3 fexp3acom23_0 fexp3acom23_1 fexp3acom23_2 fexp3acom23_3 eexp3acom23_0 exp3a com23 $.
$}
$( /* Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. */

$)
${
	fsimplbi2comg_0 $f wff ph $.
	fsimplbi2comg_1 $f wff ps $.
	fsimplbi2comg_2 $f wff ch $.
	simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $= fsimplbi2comg_0 fsimplbi2comg_1 fsimplbi2comg_2 wa wb fsimplbi2comg_1 fsimplbi2comg_2 fsimplbi2comg_0 fsimplbi2comg_0 fsimplbi2comg_1 fsimplbi2comg_2 wa bi2 exp3acom23 $.
$}
$( /* A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2012.) */

$)
${
	fsimplbi2com_0 $f wff ph $.
	fsimplbi2com_1 $f wff ps $.
	fsimplbi2com_2 $f wff ch $.
	esimplbi2com_0 $e |- ( ph <-> ( ps /\ ch ) ) $.
	simplbi2com $p |- ( ch -> ( ps -> ph ) ) $= fsimplbi2com_1 fsimplbi2com_2 fsimplbi2com_0 fsimplbi2com_0 fsimplbi2com_1 fsimplbi2com_2 esimplbi2com_0 simplbi2 com12 $.
$}
$( /* ~ e21 without virtual deductions.  (Contributed by Alan Sare,
       18-Mar-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. */

$)
${
	fee21_0 $f wff ph $.
	fee21_1 $f wff ps $.
	fee21_2 $f wff ch $.
	fee21_3 $f wff th $.
	fee21_4 $f wff ta $.
	eee21_0 $e |- ( ph -> ( ps -> ch ) ) $.
	eee21_1 $e |- ( ph -> th ) $.
	eee21_2 $e |- ( ch -> ( th -> ta ) ) $.
	ee21 $p |- ( ph -> ( ps -> ta ) ) $= fee21_0 fee21_1 fee21_2 fee21_3 fee21_4 eee21_0 fee21_0 fee21_3 fee21_1 eee21_1 a1d eee21_2 ee22 $.
$}
$( /* ~ e10 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  TODO: this is frequently used; come up with better
       label. */

$)
${
	fee10_0 $f wff ph $.
	fee10_1 $f wff ps $.
	fee10_2 $f wff ch $.
	fee10_3 $f wff th $.
	eee10_0 $e |- ( ph -> ps ) $.
	eee10_1 $e |- ch $.
	eee10_2 $e |- ( ps -> ( ch -> th ) ) $.
	ee10 $p |- ( ph -> th ) $= fee10_0 fee10_1 fee10_3 eee10_0 fee10_1 fee10_2 fee10_3 eee10_1 eee10_2 mpi syl $.
$}
$( /* ~ e02 without virtual deductions.  (Contributed by Alan Sare,
       22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. */

$)
${
	fee02_0 $f wff ph $.
	fee02_1 $f wff ps $.
	fee02_2 $f wff ch $.
	fee02_3 $f wff th $.
	fee02_4 $f wff ta $.
	eee02_0 $e |- ph $.
	eee02_1 $e |- ( ps -> ( ch -> th ) ) $.
	eee02_2 $e |- ( ph -> ( th -> ta ) ) $.
	ee02 $p |- ( ps -> ( ch -> ta ) ) $= fee02_1 fee02_0 fee02_2 fee02_3 fee02_4 fee02_0 fee02_1 eee02_0 a1i eee02_1 eee02_2 sylsyld $.
$}
$( /* End of auxiliary theorems for Alan Sare's virtual deduction tool, part 1 */


$)

