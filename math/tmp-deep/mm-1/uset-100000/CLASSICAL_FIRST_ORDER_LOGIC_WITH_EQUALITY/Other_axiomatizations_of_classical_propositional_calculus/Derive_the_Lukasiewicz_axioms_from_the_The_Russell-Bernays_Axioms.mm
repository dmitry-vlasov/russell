$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Tarski-Bernays-Wajsberg_axioms_from_Meredith_s_Second_CO_Axiom.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Derive the Lukasiewicz axioms from the The Russell-Bernays Axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Justification for ~ rb-imdf .  (Contributed by Anthony Hart,
     17-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rb-bijust $f wff ph $.
	f1_rb-bijust $f wff ps $.
	p_rb-bijust $p |- ( ( ph <-> ps ) <-> -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) ) $= f0_rb-bijust f1_rb-bijust p_dfbi1 f0_rb-bijust f1_rb-bijust p_imor f1_rb-bijust f0_rb-bijust p_imor f1_rb-bijust f0_rb-bijust a_wi f1_rb-bijust a_wn f0_rb-bijust a_wo p_notbii f0_rb-bijust f1_rb-bijust a_wi f0_rb-bijust a_wn f1_rb-bijust a_wo f1_rb-bijust f0_rb-bijust a_wi a_wn f1_rb-bijust a_wn f0_rb-bijust a_wo a_wn p_imbi12i f0_rb-bijust f1_rb-bijust a_wi f1_rb-bijust f0_rb-bijust a_wi a_wn a_wi f0_rb-bijust a_wn f1_rb-bijust a_wo f1_rb-bijust a_wn f0_rb-bijust a_wo a_wn a_wi p_notbii f0_rb-bijust a_wn f1_rb-bijust a_wo f1_rb-bijust a_wn f0_rb-bijust a_wo p_pm4.62 f0_rb-bijust a_wn f1_rb-bijust a_wo f1_rb-bijust a_wn f0_rb-bijust a_wo a_wn a_wi f0_rb-bijust a_wn f1_rb-bijust a_wo a_wn f1_rb-bijust a_wn f0_rb-bijust a_wo a_wn a_wo p_notbii f0_rb-bijust f1_rb-bijust a_wb f0_rb-bijust f1_rb-bijust a_wi f1_rb-bijust f0_rb-bijust a_wi a_wn a_wi a_wn f0_rb-bijust a_wn f1_rb-bijust a_wo f1_rb-bijust a_wn f0_rb-bijust a_wo a_wn a_wi a_wn f0_rb-bijust a_wn f1_rb-bijust a_wo a_wn f1_rb-bijust a_wn f0_rb-bijust a_wo a_wn a_wo a_wn p_3bitri $.
$}

$(The definition of implication, in terms of ` \/ ` and ` -. ` .
     (Contributed by Anthony Hart, 17-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rb-imdf $f wff ph $.
	f1_rb-imdf $f wff ps $.
	p_rb-imdf $p |- -. ( -. ( -. ( ph -> ps ) \/ ( -. ph \/ ps ) ) \/ -. ( -. ( -. ph \/ ps ) \/ ( ph -> ps ) ) ) $= f0_rb-imdf f1_rb-imdf p_imor f0_rb-imdf f1_rb-imdf a_wi f0_rb-imdf a_wn f1_rb-imdf a_wo p_rb-bijust f0_rb-imdf f1_rb-imdf a_wi f0_rb-imdf a_wn f1_rb-imdf a_wo a_wb f0_rb-imdf f1_rb-imdf a_wi a_wn f0_rb-imdf a_wn f1_rb-imdf a_wo a_wo a_wn f0_rb-imdf a_wn f1_rb-imdf a_wo a_wn f0_rb-imdf f1_rb-imdf a_wi a_wo a_wn a_wo a_wn p_mpbi $.
$}

$(Modus ponens for ` \/ ` ` -. ` axiom systems.  (Contributed by Anthony
       Hart, 12-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_anmp $f wff ph $.
	f1_anmp $f wff ps $.
	e0_anmp $e |- ph $.
	e1_anmp $e |- ( -. ph \/ ps ) $.
	p_anmp $p |- ps $= e0_anmp e1_anmp f0_anmp f1_anmp p_imorri f0_anmp f1_anmp a_ax-mp $.
$}

$(The first of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_rb-ax1 $f wff ph $.
	f1_rb-ax1 $f wff ps $.
	f2_rb-ax1 $f wff ch $.
	p_rb-ax1 $p |- ( -. ( -. ps \/ ch ) \/ ( -. ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $= f0_rb-ax1 f1_rb-ax1 f2_rb-ax1 p_orim2 f1_rb-ax1 f2_rb-ax1 p_imor f0_rb-ax1 f1_rb-ax1 a_wo f0_rb-ax1 f2_rb-ax1 a_wo p_imor f1_rb-ax1 f2_rb-ax1 a_wi f0_rb-ax1 f1_rb-ax1 a_wo f0_rb-ax1 f2_rb-ax1 a_wo a_wi f1_rb-ax1 a_wn f2_rb-ax1 a_wo f0_rb-ax1 f1_rb-ax1 a_wo a_wn f0_rb-ax1 f2_rb-ax1 a_wo a_wo p_3imtr3i f1_rb-ax1 a_wn f2_rb-ax1 a_wo f0_rb-ax1 f1_rb-ax1 a_wo a_wn f0_rb-ax1 f2_rb-ax1 a_wo a_wo p_imori $.
$}

$(The second of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rb-ax2 $f wff ph $.
	f1_rb-ax2 $f wff ps $.
	p_rb-ax2 $p |- ( -. ( ph \/ ps ) \/ ( ps \/ ph ) ) $= f0_rb-ax2 f1_rb-ax2 p_pm1.4 f0_rb-ax2 f1_rb-ax2 a_wo f1_rb-ax2 f0_rb-ax2 a_wo p_con3i f1_rb-ax2 f0_rb-ax2 a_wo f0_rb-ax2 f1_rb-ax2 a_wo a_wn p_con1i f0_rb-ax2 f1_rb-ax2 a_wo a_wn f1_rb-ax2 f0_rb-ax2 a_wo p_orri $.
$}

$(The third of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rb-ax3 $f wff ph $.
	f1_rb-ax3 $f wff ps $.
	p_rb-ax3 $p |- ( -. ph \/ ( ps \/ ph ) ) $= f1_rb-ax3 f0_rb-ax3 p_pm2.46 f1_rb-ax3 f0_rb-ax3 a_wo f0_rb-ax3 a_wn p_con1i f0_rb-ax3 a_wn f1_rb-ax3 f0_rb-ax3 a_wo p_orri $.
$}

$(The fourth of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph  $.
	f0_rb-ax4 $f wff ph $.
	p_rb-ax4 $p |- ( -. ( ph \/ ph ) \/ ph ) $= f0_rb-ax4 p_pm1.2 f0_rb-ax4 f0_rb-ax4 a_wo f0_rb-ax4 p_con3i f0_rb-ax4 f0_rb-ax4 f0_rb-ax4 a_wo a_wn p_con1i f0_rb-ax4 f0_rb-ax4 a_wo a_wn f0_rb-ax4 p_orri $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_rbsyl $f wff ph $.
	f1_rbsyl $f wff ps $.
	f2_rbsyl $f wff ch $.
	e0_rbsyl $e |- ( -. ps \/ ch ) $.
	e1_rbsyl $e |- ( ph \/ ps ) $.
	p_rbsyl $p |- ( ph \/ ch ) $= e1_rbsyl e0_rbsyl f0_rbsyl f1_rbsyl f2_rbsyl p_rb-ax1 f1_rbsyl a_wn f2_rbsyl a_wo f0_rbsyl f1_rbsyl a_wo a_wn f0_rbsyl f2_rbsyl a_wo a_wo p_anmp f0_rbsyl f1_rbsyl a_wo f0_rbsyl f2_rbsyl a_wo p_anmp $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_rblem1 $f wff ph $.
	f1_rblem1 $f wff ps $.
	f2_rblem1 $f wff ch $.
	f3_rblem1 $f wff th $.
	e0_rblem1 $e |- ( -. ph \/ ps ) $.
	e1_rblem1 $e |- ( -. ch \/ th ) $.
	p_rblem1 $p |- ( -. ( ph \/ ch ) \/ ( ps \/ th ) ) $= e1_rblem1 f1_rblem1 f2_rblem1 f3_rblem1 p_rb-ax1 f2_rblem1 a_wn f3_rblem1 a_wo f1_rblem1 f2_rblem1 a_wo a_wn f1_rblem1 f3_rblem1 a_wo a_wo p_anmp f2_rblem1 f1_rblem1 p_rb-ax2 e0_rblem1 f2_rblem1 f0_rblem1 f1_rblem1 p_rb-ax1 f0_rblem1 a_wn f1_rblem1 a_wo f2_rblem1 f0_rblem1 a_wo a_wn f2_rblem1 f1_rblem1 a_wo a_wo p_anmp f0_rblem1 f2_rblem1 p_rb-ax2 f0_rblem1 f2_rblem1 a_wo a_wn f2_rblem1 f0_rblem1 a_wo f2_rblem1 f1_rblem1 a_wo p_rbsyl f0_rblem1 f2_rblem1 a_wo a_wn f2_rblem1 f1_rblem1 a_wo f1_rblem1 f2_rblem1 a_wo p_rbsyl f0_rblem1 f2_rblem1 a_wo a_wn f1_rblem1 f2_rblem1 a_wo f1_rblem1 f3_rblem1 a_wo p_rbsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_rblem2 $f wff ph $.
	f1_rblem2 $f wff ps $.
	f2_rblem2 $f wff ch $.
	p_rblem2 $p |- ( -. ( ch \/ ph ) \/ ( ch \/ ( ph \/ ps ) ) ) $= f1_rblem2 f0_rblem2 p_rb-ax2 f0_rblem2 f1_rblem2 p_rb-ax3 f0_rblem2 a_wn f1_rblem2 f0_rblem2 a_wo f0_rblem2 f1_rblem2 a_wo p_rbsyl f2_rblem2 f0_rblem2 f0_rblem2 f1_rblem2 a_wo p_rb-ax1 f0_rblem2 a_wn f0_rblem2 f1_rblem2 a_wo a_wo f2_rblem2 f0_rblem2 a_wo a_wn f2_rblem2 f0_rblem2 f1_rblem2 a_wo a_wo a_wo p_anmp $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_rblem3 $f wff ph $.
	f1_rblem3 $f wff ps $.
	f2_rblem3 $f wff ch $.
	p_rblem3 $p |- ( -. ( ch \/ ph ) \/ ( ( ch \/ ps ) \/ ph ) ) $= f0_rblem3 f2_rblem3 f1_rblem3 a_wo p_rb-ax2 f2_rblem3 f1_rblem3 f0_rblem3 p_rblem2 f2_rblem3 f0_rblem3 p_rb-ax2 f2_rblem3 f0_rblem3 a_wo a_wn f0_rblem3 f2_rblem3 a_wo f0_rblem3 f2_rblem3 f1_rblem3 a_wo a_wo p_rbsyl f2_rblem3 f0_rblem3 a_wo a_wn f0_rblem3 f2_rblem3 f1_rblem3 a_wo a_wo f2_rblem3 f1_rblem3 a_wo f0_rblem3 a_wo p_rbsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th ta et  $.
	f0_rblem4 $f wff ph $.
	f1_rblem4 $f wff ps $.
	f2_rblem4 $f wff ch $.
	f3_rblem4 $f wff th $.
	f4_rblem4 $f wff ta $.
	f5_rblem4 $f wff et $.
	e0_rblem4 $e |- ( -. ph \/ th ) $.
	e1_rblem4 $e |- ( -. ps \/ ta ) $.
	e2_rblem4 $e |- ( -. ch \/ et ) $.
	p_rblem4 $p |- ( -. ( ( ph \/ ps ) \/ ch ) \/ ( ( et \/ ta ) \/ th ) ) $= e2_rblem4 e1_rblem4 f2_rblem4 f5_rblem4 f1_rblem4 f4_rblem4 p_rblem1 e0_rblem4 f2_rblem4 f1_rblem4 a_wo f5_rblem4 f4_rblem4 a_wo f0_rblem4 f3_rblem4 p_rblem1 f0_rblem4 f2_rblem4 f1_rblem4 a_wo p_rb-ax2 f1_rblem4 f2_rblem4 p_rb-ax2 f0_rblem4 f1_rblem4 f2_rblem4 a_wo f2_rblem4 f1_rblem4 a_wo p_rb-ax1 f1_rblem4 f2_rblem4 a_wo a_wn f2_rblem4 f1_rblem4 a_wo a_wo f0_rblem4 f1_rblem4 f2_rblem4 a_wo a_wo a_wn f0_rblem4 f2_rblem4 f1_rblem4 a_wo a_wo a_wo p_anmp f1_rblem4 f2_rblem4 a_wo f0_rblem4 p_rb-ax2 f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo a_wn f0_rblem4 f1_rblem4 f2_rblem4 a_wo a_wo f0_rblem4 f2_rblem4 f1_rblem4 a_wo a_wo p_rbsyl f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo a_wn f0_rblem4 f2_rblem4 f1_rblem4 a_wo a_wo f2_rblem4 f1_rblem4 a_wo f0_rblem4 a_wo p_rbsyl f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo p_rb-ax4 f0_rblem4 f1_rblem4 f2_rblem4 a_wo p_rb-ax2 f1_rblem4 f2_rblem4 f0_rblem4 p_rblem2 f0_rblem4 f1_rblem4 a_wo a_wn f0_rblem4 f1_rblem4 f2_rblem4 a_wo a_wo f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo p_rbsyl f2_rblem4 f1_rblem4 p_rb-ax3 f1_rblem4 f2_rblem4 a_wo f0_rblem4 f2_rblem4 a_wn p_rblem2 f2_rblem4 a_wn f1_rblem4 f2_rblem4 a_wo a_wo f2_rblem4 a_wn f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo a_wo p_anmp f0_rblem4 f1_rblem4 a_wo f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo f2_rblem4 f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo p_rblem1 f0_rblem4 f1_rblem4 a_wo f2_rblem4 a_wo a_wn f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo a_wo f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo p_rbsyl f0_rblem4 f1_rblem4 a_wo f2_rblem4 a_wo a_wn f1_rblem4 f2_rblem4 a_wo f0_rblem4 a_wo f2_rblem4 f1_rblem4 a_wo f0_rblem4 a_wo p_rbsyl f0_rblem4 f1_rblem4 a_wo f2_rblem4 a_wo a_wn f2_rblem4 f1_rblem4 a_wo f0_rblem4 a_wo f5_rblem4 f4_rblem4 a_wo f3_rblem4 a_wo p_rbsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 19-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rblem5 $f wff ph $.
	f1_rblem5 $f wff ps $.
	p_rblem5 $p |- ( -. ( -. -. ph \/ ps ) \/ ( -. -. ps \/ ph ) ) $= f0_rblem5 f1_rblem5 a_wn a_wn p_rb-ax2 f0_rblem5 p_rb-ax4 f0_rblem5 f0_rblem5 p_rb-ax3 f0_rblem5 a_wn f0_rblem5 f0_rblem5 a_wo f0_rblem5 p_rbsyl f0_rblem5 a_wn a_wn p_rb-ax4 f0_rblem5 a_wn a_wn f0_rblem5 a_wn a_wn p_rb-ax3 f0_rblem5 a_wn a_wn a_wn f0_rblem5 a_wn a_wn f0_rblem5 a_wn a_wn a_wo f0_rblem5 a_wn a_wn p_rbsyl f0_rblem5 a_wn a_wn a_wn f0_rblem5 a_wn a_wn p_rb-ax2 f0_rblem5 a_wn a_wn a_wn f0_rblem5 a_wn a_wn a_wo f0_rblem5 a_wn a_wn f0_rblem5 a_wn a_wn a_wn a_wo p_anmp f0_rblem5 p_rb-ax4 f0_rblem5 f0_rblem5 p_rb-ax3 f0_rblem5 a_wn f0_rblem5 f0_rblem5 a_wo f0_rblem5 p_rbsyl f0_rblem5 a_wn f0_rblem5 a_wn a_wn a_wn f0_rblem5 f0_rblem5 p_rblem1 f0_rblem5 a_wn f0_rblem5 a_wo f0_rblem5 a_wn a_wn a_wn f0_rblem5 a_wo p_anmp f1_rblem5 a_wn p_rb-ax4 f1_rblem5 a_wn f1_rblem5 a_wn p_rb-ax3 f1_rblem5 a_wn a_wn f1_rblem5 a_wn f1_rblem5 a_wn a_wo f1_rblem5 a_wn p_rbsyl f1_rblem5 a_wn a_wn f1_rblem5 a_wn p_rb-ax2 f1_rblem5 a_wn a_wn f1_rblem5 a_wn a_wo f1_rblem5 a_wn f1_rblem5 a_wn a_wn a_wo p_anmp f0_rblem5 a_wn a_wn f0_rblem5 f1_rblem5 f1_rblem5 a_wn a_wn p_rblem1 f0_rblem5 a_wn a_wn f1_rblem5 a_wo a_wn f0_rblem5 f1_rblem5 a_wn a_wn a_wo f1_rblem5 a_wn a_wn f0_rblem5 a_wo p_rbsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rblem6 $f wff ph $.
	f1_rblem6 $f wff ps $.
	e0_rblem6 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
	p_rblem6 $p |- ( -. ph \/ ps ) $= e0_rblem6 f0_rblem6 a_wn f1_rblem6 a_wo a_wn p_rb-ax4 f0_rblem6 a_wn f1_rblem6 a_wo a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn p_rb-ax3 f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn p_rbsyl f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn p_rb-ax2 f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn a_wo p_anmp f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn p_rblem3 f0_rblem6 a_wn f1_rblem6 a_wo a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn a_wo p_anmp f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn p_rb-ax2 f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo a_wo p_anmp f0_rblem6 a_wn f1_rblem6 a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo p_rblem5 f0_rblem6 a_wn f1_rblem6 a_wo a_wn a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo a_wo f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo a_wn a_wn f0_rblem6 a_wn f1_rblem6 a_wo a_wo p_anmp f0_rblem6 a_wn f1_rblem6 a_wo a_wn f1_rblem6 a_wn f0_rblem6 a_wo a_wn a_wo a_wn f0_rblem6 a_wn f1_rblem6 a_wo p_anmp $.
$}

$(Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_rblem7 $f wff ph $.
	f1_rblem7 $f wff ps $.
	e0_rblem7 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
	p_rblem7 $p |- ( -. ps \/ ph ) $= e0_rblem7 f1_rblem7 a_wn f0_rblem7 a_wo a_wn f0_rblem7 a_wn f1_rblem7 a_wo a_wn p_rb-ax3 f1_rblem7 a_wn f0_rblem7 a_wo f0_rblem7 a_wn f1_rblem7 a_wo a_wn f1_rblem7 a_wn f0_rblem7 a_wo a_wn a_wo p_rblem5 f1_rblem7 a_wn f0_rblem7 a_wo a_wn a_wn f0_rblem7 a_wn f1_rblem7 a_wo a_wn f1_rblem7 a_wn f0_rblem7 a_wo a_wn a_wo a_wo f0_rblem7 a_wn f1_rblem7 a_wo a_wn f1_rblem7 a_wn f0_rblem7 a_wo a_wn a_wo a_wn a_wn f1_rblem7 a_wn f0_rblem7 a_wo a_wo p_anmp f0_rblem7 a_wn f1_rblem7 a_wo a_wn f1_rblem7 a_wn f0_rblem7 a_wo a_wn a_wo a_wn f1_rblem7 a_wn f0_rblem7 a_wo p_anmp $.
$}

$(~ ax-mp derived from Russell-Bernays'.  (Contributed by Anthony Hart,
       19-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_re1axmp $f wff ph $.
	f1_re1axmp $f wff ps $.
	e0_re1axmp $e |- ph $.
	e1_re1axmp $e |- ( ph -> ps ) $.
	p_re1axmp $p |- ps $= e0_re1axmp e1_re1axmp f0_re1axmp f1_re1axmp p_rb-imdf f0_re1axmp f1_re1axmp a_wi f0_re1axmp a_wn f1_re1axmp a_wo p_rblem6 f0_re1axmp f1_re1axmp a_wi f0_re1axmp a_wn f1_re1axmp a_wo p_anmp f0_re1axmp f1_re1axmp p_anmp $.
$}

$(~ luk-1 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_re2luk1 $f wff ph $.
	f1_re2luk1 $f wff ps $.
	f2_re2luk1 $f wff ch $.
	p_re2luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi p_rb-imdf f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi f1_re2luk1 f2_re2luk1 a_wi a_wn f0_re2luk1 f2_re2luk1 a_wi a_wo p_rblem7 f1_re2luk1 f2_re2luk1 p_rb-imdf f1_re2luk1 f2_re2luk1 a_wi f1_re2luk1 a_wn f2_re2luk1 a_wo p_rblem6 f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn p_rb-ax2 f1_re2luk1 f2_re2luk1 a_wi a_wn p_rb-ax4 f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn p_rb-ax3 f1_re2luk1 f2_re2luk1 a_wi a_wn a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn a_wo f1_re2luk1 f2_re2luk1 a_wi a_wn p_rbsyl f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rb-ax4 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rb-ax3 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rbsyl f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rb-ax2 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn a_wo p_anmp f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn p_rblem1 f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wo a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn a_wo p_rbsyl f1_re2luk1 f2_re2luk1 a_wi a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn a_wo p_anmp f0_re2luk1 f2_re2luk1 p_rb-imdf f0_re2luk1 f2_re2luk1 a_wi f0_re2luk1 a_wn f2_re2luk1 a_wo p_rblem7 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo f0_re2luk1 f2_re2luk1 a_wi p_rblem1 f0_re2luk1 a_wn f1_re2luk1 f2_re2luk1 p_rb-ax1 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn p_rb-ax2 f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn p_rb-ax4 f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn p_rb-ax3 f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn a_wo f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn p_rbsyl f0_re2luk1 a_wn f2_re2luk1 a_wo p_rb-ax4 f0_re2luk1 a_wn f2_re2luk1 a_wo f0_re2luk1 a_wn f2_re2luk1 a_wo p_rb-ax3 f0_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo f0_re2luk1 a_wn f2_re2luk1 a_wo p_rbsyl f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rb-ax4 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rb-ax3 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rbsyl f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn p_rblem4 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo p_rb-ax2 f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn a_wo f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn a_wo p_rbsyl f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn a_wo f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo a_wo p_rbsyl f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo a_wo f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo a_wo p_anmp f0_re2luk1 a_wn f1_re2luk1 a_wo a_wn f1_re2luk1 a_wn f2_re2luk1 a_wo a_wn f0_re2luk1 a_wn f2_re2luk1 a_wo a_wo f1_re2luk1 f2_re2luk1 a_wi a_wn f0_re2luk1 f2_re2luk1 a_wi a_wo p_rbsyl f0_re2luk1 f1_re2luk1 p_rb-imdf f0_re2luk1 f1_re2luk1 a_wi f0_re2luk1 a_wn f1_re2luk1 a_wo p_rblem6 f0_re2luk1 f1_re2luk1 a_wi a_wn f0_re2luk1 a_wn f1_re2luk1 a_wo f1_re2luk1 f2_re2luk1 a_wi a_wn f0_re2luk1 f2_re2luk1 a_wi a_wo p_rbsyl f0_re2luk1 f1_re2luk1 a_wi a_wn f1_re2luk1 f2_re2luk1 a_wi a_wn f0_re2luk1 f2_re2luk1 a_wi a_wo f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi p_rbsyl f0_re2luk1 f1_re2luk1 a_wi f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi p_rb-imdf f0_re2luk1 f1_re2luk1 a_wi f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi a_wi f0_re2luk1 f1_re2luk1 a_wi a_wn f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi a_wo p_rblem7 f0_re2luk1 f1_re2luk1 a_wi a_wn f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi a_wo f0_re2luk1 f1_re2luk1 a_wi f1_re2luk1 f2_re2luk1 a_wi f0_re2luk1 f2_re2luk1 a_wi a_wi a_wi p_anmp $.
$}

$(~ luk-2 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph  $.
	f0_re2luk2 $f wff ph $.
	p_re2luk2 $p |- ( ( -. ph -> ph ) -> ph ) $= f0_re2luk2 p_rb-ax4 f0_re2luk2 p_rb-ax4 f0_re2luk2 f0_re2luk2 p_rb-ax3 f0_re2luk2 a_wn f0_re2luk2 f0_re2luk2 a_wo f0_re2luk2 p_rbsyl f0_re2luk2 a_wn a_wn p_rb-ax4 f0_re2luk2 a_wn a_wn f0_re2luk2 a_wn a_wn p_rb-ax3 f0_re2luk2 a_wn a_wn a_wn f0_re2luk2 a_wn a_wn f0_re2luk2 a_wn a_wn a_wo f0_re2luk2 a_wn a_wn p_rbsyl f0_re2luk2 a_wn a_wn a_wn f0_re2luk2 a_wn a_wn p_rb-ax2 f0_re2luk2 a_wn a_wn a_wn f0_re2luk2 a_wn a_wn a_wo f0_re2luk2 a_wn a_wn f0_re2luk2 a_wn a_wn a_wn a_wo p_anmp f0_re2luk2 p_rb-ax4 f0_re2luk2 f0_re2luk2 p_rb-ax3 f0_re2luk2 a_wn f0_re2luk2 f0_re2luk2 a_wo f0_re2luk2 p_rbsyl f0_re2luk2 a_wn f0_re2luk2 a_wn a_wn a_wn f0_re2luk2 f0_re2luk2 p_rblem1 f0_re2luk2 a_wn f0_re2luk2 a_wo f0_re2luk2 a_wn a_wn a_wn f0_re2luk2 a_wo p_anmp f0_re2luk2 p_rb-ax4 f0_re2luk2 f0_re2luk2 p_rb-ax3 f0_re2luk2 a_wn f0_re2luk2 f0_re2luk2 a_wo f0_re2luk2 p_rbsyl f0_re2luk2 a_wn a_wn f0_re2luk2 f0_re2luk2 f0_re2luk2 p_rblem1 f0_re2luk2 a_wn a_wn f0_re2luk2 a_wo a_wn f0_re2luk2 f0_re2luk2 a_wo f0_re2luk2 p_rbsyl f0_re2luk2 a_wn f0_re2luk2 p_rb-imdf f0_re2luk2 a_wn f0_re2luk2 a_wi f0_re2luk2 a_wn a_wn f0_re2luk2 a_wo p_rblem6 f0_re2luk2 a_wn f0_re2luk2 a_wi a_wn f0_re2luk2 a_wn a_wn f0_re2luk2 a_wo f0_re2luk2 p_rbsyl f0_re2luk2 a_wn f0_re2luk2 a_wi f0_re2luk2 p_rb-imdf f0_re2luk2 a_wn f0_re2luk2 a_wi f0_re2luk2 a_wi f0_re2luk2 a_wn f0_re2luk2 a_wi a_wn f0_re2luk2 a_wo p_rblem7 f0_re2luk2 a_wn f0_re2luk2 a_wi a_wn f0_re2luk2 a_wo f0_re2luk2 a_wn f0_re2luk2 a_wi f0_re2luk2 a_wi p_anmp $.
$}

$(~ luk-3 derived from Russell-Bernays'.

     This theorem, along with ~ re1axmp , ~ re2luk1 , and ~ re2luk2 shows that
     ~ rb-ax1 , ~ rb-ax2 , ~ rb-ax3 , and ~ rb-ax4 , along with ~ anmp , can be
     used as a complete axiomatization of propositional calculus.  (Contributed
     by Anthony Hart, 19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_re2luk3 $f wff ph $.
	f1_re2luk3 $f wff ps $.
	p_re2luk3 $p |- ( ph -> ( -. ph -> ps ) ) $= f0_re2luk3 a_wn f1_re2luk3 p_rb-imdf f0_re2luk3 a_wn f1_re2luk3 a_wi f0_re2luk3 a_wn a_wn f1_re2luk3 a_wo p_rblem7 f0_re2luk3 a_wn p_rb-ax4 f0_re2luk3 a_wn f0_re2luk3 a_wn p_rb-ax3 f0_re2luk3 a_wn a_wn f0_re2luk3 a_wn f0_re2luk3 a_wn a_wo f0_re2luk3 a_wn p_rbsyl f0_re2luk3 a_wn a_wn f0_re2luk3 a_wn p_rb-ax2 f0_re2luk3 a_wn a_wn f0_re2luk3 a_wn a_wo f0_re2luk3 a_wn f0_re2luk3 a_wn a_wn a_wo p_anmp f0_re2luk3 a_wn a_wn f1_re2luk3 f0_re2luk3 a_wn p_rblem2 f0_re2luk3 a_wn f0_re2luk3 a_wn a_wn a_wo f0_re2luk3 a_wn f0_re2luk3 a_wn a_wn f1_re2luk3 a_wo a_wo p_anmp f0_re2luk3 a_wn f0_re2luk3 a_wn a_wn f1_re2luk3 a_wo f0_re2luk3 a_wn f1_re2luk3 a_wi p_rbsyl f0_re2luk3 f0_re2luk3 a_wn f1_re2luk3 a_wi p_rb-imdf f0_re2luk3 f0_re2luk3 a_wn f1_re2luk3 a_wi a_wi f0_re2luk3 a_wn f0_re2luk3 a_wn f1_re2luk3 a_wi a_wo p_rblem7 f0_re2luk3 a_wn f0_re2luk3 a_wn f1_re2luk3 a_wi a_wo f0_re2luk3 f0_re2luk3 a_wn f1_re2luk3 a_wi a_wi p_anmp $.
$}


