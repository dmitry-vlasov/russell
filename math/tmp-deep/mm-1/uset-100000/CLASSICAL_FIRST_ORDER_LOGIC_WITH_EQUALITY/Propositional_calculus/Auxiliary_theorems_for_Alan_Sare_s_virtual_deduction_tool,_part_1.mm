$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Truth_tables.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Auxiliary theorems for Alan Sare's virtual deduction tool, part 1

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Virtual deduction rule ~ e22 without virtual deduction connectives.
       Special theorem needed for Alan Sare's virtual deduction translation
       tool.  (Contributed by Alan Sare, 2-May-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. $)

${
	$v ph ps ch th ta  $.
	f0_ee22 $f wff ph $.
	f1_ee22 $f wff ps $.
	f2_ee22 $f wff ch $.
	f3_ee22 $f wff th $.
	f4_ee22 $f wff ta $.
	e0_ee22 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_ee22 $e |- ( ph -> ( ps -> th ) ) $.
	e2_ee22 $e |- ( ch -> ( th -> ta ) ) $.
	p_ee22 $p |- ( ph -> ( ps -> ta ) ) $= e0_ee22 e1_ee22 e2_ee22 f0_ee22 f1_ee22 f2_ee22 f3_ee22 f4_ee22 p_syl6c $.
$}

$(~ e12an without virtual deduction connectives.  Special theorem needed
       for Alan Sare's virtual deduction translation tool.  (Contributed by
       Alan Sare, 28-Oct-2011.)  TODO: this is frequently used; come up with
       better label. $)

${
	$v ph ps ch th ta  $.
	f0_ee12an $f wff ph $.
	f1_ee12an $f wff ps $.
	f2_ee12an $f wff ch $.
	f3_ee12an $f wff th $.
	f4_ee12an $f wff ta $.
	e0_ee12an $e |- ( ph -> ps ) $.
	e1_ee12an $e |- ( ph -> ( ch -> th ) ) $.
	e2_ee12an $e |- ( ( ps /\ th ) -> ta ) $.
	p_ee12an $p |- ( ph -> ( ch -> ta ) ) $= e1_ee12an e0_ee12an f0_ee12an f2_ee12an f3_ee12an f1_ee12an p_jctild e2_ee12an f0_ee12an f2_ee12an f1_ee12an f3_ee12an a_wa f4_ee12an p_syl6 $.
$}

$(~ e23 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)

${
	$v ph ps ch th ta et  $.
	f0_ee23 $f wff ph $.
	f1_ee23 $f wff ps $.
	f2_ee23 $f wff ch $.
	f3_ee23 $f wff th $.
	f4_ee23 $f wff ta $.
	f5_ee23 $f wff et $.
	e0_ee23 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_ee23 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
	e2_ee23 $e |- ( ch -> ( ta -> et ) ) $.
	p_ee23 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $= e1_ee23 e0_ee23 e2_ee23 f0_ee23 f1_ee23 f2_ee23 f4_ee23 f5_ee23 a_wi p_syl6 f0_ee23 f1_ee23 f3_ee23 f4_ee23 f5_ee23 p_syldd $.
$}

$(Exportation implication also converting head from biconditional to
     conditional.  This proof is ~ exbirVD automatically translated and
     minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
     (New usage is discouraged.)  TODO: decide if this is worth keeping. $)

${
	$v ph ps ch th  $.
	f0_exbir $f wff ph $.
	f1_exbir $f wff ps $.
	f2_exbir $f wff ch $.
	f3_exbir $f wff th $.
	p_exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) -> ( ph -> ( ps -> ( th -> ch ) ) ) ) $= f2_exbir f3_exbir p_bi2 f2_exbir f3_exbir a_wb f3_exbir f2_exbir a_wi f0_exbir f1_exbir a_wa p_imim2i f0_exbir f1_exbir a_wa f2_exbir f3_exbir a_wb a_wi f0_exbir f1_exbir f3_exbir f2_exbir a_wi p_exp3a $.
$}

$(~ impexp with a 3-conjunct antecedent.  (Contributed by Alan Sare,
     31-Dec-2011.) $)

${
	$v ph ps ch th  $.
	f0_3impexp $f wff ph $.
	f1_3impexp $f wff ps $.
	f2_3impexp $f wff ch $.
	f3_3impexp $f wff th $.
	p_3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) ) $= f0_3impexp f1_3impexp f2_3impexp a_w3a f3_3impexp a_wi p_id f0_3impexp f1_3impexp f2_3impexp a_w3a f3_3impexp a_wi f0_3impexp f1_3impexp f2_3impexp f3_3impexp p_3expd f0_3impexp f1_3impexp f2_3impexp f3_3impexp a_wi a_wi a_wi p_id f0_3impexp f1_3impexp f2_3impexp f3_3impexp a_wi a_wi a_wi f0_3impexp f1_3impexp f2_3impexp f3_3impexp p_3impd f0_3impexp f1_3impexp f2_3impexp a_w3a f3_3impexp a_wi f0_3impexp f1_3impexp f2_3impexp f3_3impexp a_wi a_wi a_wi p_impbii $.
$}

$(~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  Derived automatically from ~ 3impexpVD .  (Contributed by
     Alan Sare, 31-Dec-2011.)  (New usage is discouraged.)  TODO: decide if
     this is worth keeping. $)

${
	$v ph ps ch th ta  $.
	f0_3impexpbicom $f wff ph $.
	f1_3impexpbicom $f wff ps $.
	f2_3impexpbicom $f wff ch $.
	f3_3impexpbicom $f wff th $.
	f4_3impexpbicom $f wff ta $.
	p_3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <-> ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $= f3_3impexpbicom f4_3impexpbicom p_bicom f3_3impexpbicom f4_3impexpbicom a_wb f4_3impexpbicom f3_3impexpbicom a_wb f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a p_imbi2 f3_3impexpbicom f4_3impexpbicom a_wb f4_3impexpbicom f3_3impexpbicom a_wb a_wb f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f3_3impexpbicom f4_3impexpbicom a_wb a_wi f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f4_3impexpbicom f3_3impexpbicom a_wb a_wi p_biimpcd f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f3_3impexpbicom f4_3impexpbicom a_wb a_wi f3_3impexpbicom f4_3impexpbicom a_wb f4_3impexpbicom f3_3impexpbicom a_wb a_wb f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f4_3impexpbicom f3_3impexpbicom a_wb a_wi p_mpi f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f3_3impexpbicom f4_3impexpbicom a_wb a_wi f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom f4_3impexpbicom f3_3impexpbicom a_wb p_3expd f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom f4_3impexpbicom f3_3impexpbicom a_wb p_3impexp f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f4_3impexpbicom f3_3impexpbicom a_wb a_wi f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom f4_3impexpbicom f3_3impexpbicom a_wb a_wi a_wi a_wi p_biimpri f3_3impexpbicom f4_3impexpbicom p_bicom f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom f4_3impexpbicom f3_3impexpbicom a_wb a_wi a_wi a_wi f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f4_3impexpbicom f3_3impexpbicom a_wb f3_3impexpbicom f4_3impexpbicom a_wb p_syl6ibr f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom a_w3a f3_3impexpbicom f4_3impexpbicom a_wb a_wi f0_3impexpbicom f1_3impexpbicom f2_3impexpbicom f4_3impexpbicom f3_3impexpbicom a_wb a_wi a_wi a_wi p_impbii $.
$}

$(Deduction form of ~ 3impexpbicom .  Derived automatically from
       ~ 3impexpbicomiVD .  (Contributed by Alan Sare, 31-Dec-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. $)

${
	$v ph ps ch th ta  $.
	f0_3impexpbicomi $f wff ph $.
	f1_3impexpbicomi $f wff ps $.
	f2_3impexpbicomi $f wff ch $.
	f3_3impexpbicomi $f wff th $.
	f4_3impexpbicomi $f wff ta $.
	e0_3impexpbicomi $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
	p_3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $= e0_3impexpbicomi f0_3impexpbicomi f1_3impexpbicomi f2_3impexpbicomi a_w3a f3_3impexpbicomi f4_3impexpbicomi p_bicomd f0_3impexpbicomi f1_3impexpbicomi f2_3impexpbicomi f4_3impexpbicomi f3_3impexpbicomi a_wb p_3exp $.
$}

$(Closed form of ~ ancoms .  Derived automatically from ~ ancomsimpVD .
     (Contributed by Alan Sare, 31-Dec-2011.) $)

${
	$v ph ps ch  $.
	f0_ancomsimp $f wff ph $.
	f1_ancomsimp $f wff ps $.
	f2_ancomsimp $f wff ch $.
	p_ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $= f0_ancomsimp f1_ancomsimp p_ancom f0_ancomsimp f1_ancomsimp a_wa f1_ancomsimp f0_ancomsimp a_wa f2_ancomsimp p_imbi1i $.
$}

$(Export and commute antecedents.  (Contributed by Alan Sare,
       18-Mar-2012.) $)

${
	$v ph ps ch th  $.
	f0_exp3acom3r $f wff ph $.
	f1_exp3acom3r $f wff ps $.
	f2_exp3acom3r $f wff ch $.
	f3_exp3acom3r $f wff th $.
	e0_exp3acom3r $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_exp3acom3r $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $= e0_exp3acom3r f0_exp3acom3r f1_exp3acom3r f2_exp3acom3r f3_exp3acom3r p_exp3a f0_exp3acom3r f1_exp3acom3r f2_exp3acom3r f3_exp3acom3r p_com3l $.
$}

$(Implication form of ~ exp3acom23 .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. $)

${
	$v ph ps ch th  $.
	f0_exp3acom23g $f wff ph $.
	f1_exp3acom23g $f wff ps $.
	f2_exp3acom23g $f wff ch $.
	f3_exp3acom23g $f wff th $.
	p_exp3acom23g $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <-> ( ph -> ( ch -> ( ps -> th ) ) ) ) $= f1_exp3acom23g f2_exp3acom23g f3_exp3acom23g p_ancomsimp f2_exp3acom23g f1_exp3acom23g f3_exp3acom23g p_impexp f1_exp3acom23g f2_exp3acom23g a_wa f3_exp3acom23g a_wi f2_exp3acom23g f1_exp3acom23g a_wa f3_exp3acom23g a_wi f2_exp3acom23g f1_exp3acom23g f3_exp3acom23g a_wi a_wi p_bitri f1_exp3acom23g f2_exp3acom23g a_wa f3_exp3acom23g a_wi f2_exp3acom23g f1_exp3acom23g f3_exp3acom23g a_wi a_wi f0_exp3acom23g p_imbi2i $.
$}

$(The exportation deduction ~ exp3a with commutation of the conjoined
       wwfs.  (Contributed by Alan Sare, 22-Jul-2012.) $)

${
	$v ph ps ch th  $.
	f0_exp3acom23 $f wff ph $.
	f1_exp3acom23 $f wff ps $.
	f2_exp3acom23 $f wff ch $.
	f3_exp3acom23 $f wff th $.
	e0_exp3acom23 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
	p_exp3acom23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $= e0_exp3acom23 f0_exp3acom23 f1_exp3acom23 f2_exp3acom23 f3_exp3acom23 p_exp3a f0_exp3acom23 f1_exp3acom23 f2_exp3acom23 f3_exp3acom23 p_com23 $.
$}

$(Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. $)

${
	$v ph ps ch  $.
	f0_simplbi2comg $f wff ph $.
	f1_simplbi2comg $f wff ps $.
	f2_simplbi2comg $f wff ch $.
	p_simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $= f0_simplbi2comg f1_simplbi2comg f2_simplbi2comg a_wa p_bi2 f0_simplbi2comg f1_simplbi2comg f2_simplbi2comg a_wa a_wb f1_simplbi2comg f2_simplbi2comg f0_simplbi2comg p_exp3acom23 $.
$}

$(A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2012.) $)

${
	$v ph ps ch  $.
	f0_simplbi2com $f wff ph $.
	f1_simplbi2com $f wff ps $.
	f2_simplbi2com $f wff ch $.
	e0_simplbi2com $e |- ( ph <-> ( ps /\ ch ) ) $.
	p_simplbi2com $p |- ( ch -> ( ps -> ph ) ) $= e0_simplbi2com f0_simplbi2com f1_simplbi2com f2_simplbi2com p_simplbi2 f1_simplbi2com f2_simplbi2com f0_simplbi2com p_com12 $.
$}

$(~ e21 without virtual deductions.  (Contributed by Alan Sare,
       18-Mar-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)

${
	$v ph ps ch th ta  $.
	f0_ee21 $f wff ph $.
	f1_ee21 $f wff ps $.
	f2_ee21 $f wff ch $.
	f3_ee21 $f wff th $.
	f4_ee21 $f wff ta $.
	e0_ee21 $e |- ( ph -> ( ps -> ch ) ) $.
	e1_ee21 $e |- ( ph -> th ) $.
	e2_ee21 $e |- ( ch -> ( th -> ta ) ) $.
	p_ee21 $p |- ( ph -> ( ps -> ta ) ) $= e0_ee21 e1_ee21 f0_ee21 f3_ee21 f1_ee21 p_a1d e2_ee21 f0_ee21 f1_ee21 f2_ee21 f3_ee21 f4_ee21 p_ee22 $.
$}

$(~ e10 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  TODO: this is frequently used; come up with better
       label. $)

${
	$v ph ps ch th  $.
	f0_ee10 $f wff ph $.
	f1_ee10 $f wff ps $.
	f2_ee10 $f wff ch $.
	f3_ee10 $f wff th $.
	e0_ee10 $e |- ( ph -> ps ) $.
	e1_ee10 $e |- ch $.
	e2_ee10 $e |- ( ps -> ( ch -> th ) ) $.
	p_ee10 $p |- ( ph -> th ) $= e0_ee10 e1_ee10 e2_ee10 f1_ee10 f2_ee10 f3_ee10 p_mpi f0_ee10 f1_ee10 f3_ee10 p_syl $.
$}

$(~ e02 without virtual deductions.  (Contributed by Alan Sare,
       22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)

${
	$v ph ps ch th ta  $.
	f0_ee02 $f wff ph $.
	f1_ee02 $f wff ps $.
	f2_ee02 $f wff ch $.
	f3_ee02 $f wff th $.
	f4_ee02 $f wff ta $.
	e0_ee02 $e |- ph $.
	e1_ee02 $e |- ( ps -> ( ch -> th ) ) $.
	e2_ee02 $e |- ( ph -> ( th -> ta ) ) $.
	p_ee02 $p |- ( ps -> ( ch -> ta ) ) $= e0_ee02 f0_ee02 f1_ee02 p_a1i e1_ee02 e2_ee02 f1_ee02 f0_ee02 f2_ee02 f3_ee02 f4_ee02 p_sylsyld $.
$}

$(End of auxiliary theorems for Alan Sare's virtual deduction tool, part 1 $)


