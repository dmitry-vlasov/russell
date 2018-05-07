$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Tarski-Bernays-Wajsberg_axioms_from_Meredith_s_Second_CO_Axiom.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Derive the Lukasiewicz axioms from the The Russell-Bernays Axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Justification for ~ rb-imdf .  (Contributed by Anthony Hart,
     17-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frb-bijust_0 $f wff ph $.
	frb-bijust_1 $f wff ps $.
	rb-bijust $p |- ( ( ph <-> ps ) <-> -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) ) $= frb-bijust_0 frb-bijust_1 wb frb-bijust_0 frb-bijust_1 wi frb-bijust_1 frb-bijust_0 wi wn wi wn frb-bijust_0 wn frb-bijust_1 wo frb-bijust_1 wn frb-bijust_0 wo wn wi wn frb-bijust_0 wn frb-bijust_1 wo wn frb-bijust_1 wn frb-bijust_0 wo wn wo wn frb-bijust_0 frb-bijust_1 dfbi1 frb-bijust_0 frb-bijust_1 wi frb-bijust_1 frb-bijust_0 wi wn wi frb-bijust_0 wn frb-bijust_1 wo frb-bijust_1 wn frb-bijust_0 wo wn wi frb-bijust_0 frb-bijust_1 wi frb-bijust_0 wn frb-bijust_1 wo frb-bijust_1 frb-bijust_0 wi wn frb-bijust_1 wn frb-bijust_0 wo wn frb-bijust_0 frb-bijust_1 imor frb-bijust_1 frb-bijust_0 wi frb-bijust_1 wn frb-bijust_0 wo frb-bijust_1 frb-bijust_0 imor notbii imbi12i notbii frb-bijust_0 wn frb-bijust_1 wo frb-bijust_1 wn frb-bijust_0 wo wn wi frb-bijust_0 wn frb-bijust_1 wo wn frb-bijust_1 wn frb-bijust_0 wo wn wo frb-bijust_0 wn frb-bijust_1 wo frb-bijust_1 wn frb-bijust_0 wo pm4.62 notbii 3bitri $.
$}
$( The definition of implication, in terms of ` \/ ` and ` -. ` .
     (Contributed by Anthony Hart, 17-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frb-imdf_0 $f wff ph $.
	frb-imdf_1 $f wff ps $.
	rb-imdf $p |- -. ( -. ( -. ( ph -> ps ) \/ ( -. ph \/ ps ) ) \/ -. ( -. ( -. ph \/ ps ) \/ ( ph -> ps ) ) ) $= frb-imdf_0 frb-imdf_1 wi frb-imdf_0 wn frb-imdf_1 wo wb frb-imdf_0 frb-imdf_1 wi wn frb-imdf_0 wn frb-imdf_1 wo wo wn frb-imdf_0 wn frb-imdf_1 wo wn frb-imdf_0 frb-imdf_1 wi wo wn wo wn frb-imdf_0 frb-imdf_1 imor frb-imdf_0 frb-imdf_1 wi frb-imdf_0 wn frb-imdf_1 wo rb-bijust mpbi $.
$}
$( Modus ponens for ` \/ ` ` -. ` axiom systems.  (Contributed by Anthony
       Hart, 12-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fanmp_0 $f wff ph $.
	fanmp_1 $f wff ps $.
	eanmp_0 $e |- ph $.
	eanmp_1 $e |- ( -. ph \/ ps ) $.
	anmp $p |- ps $= fanmp_0 fanmp_1 eanmp_0 fanmp_0 fanmp_1 eanmp_1 imorri ax-mp $.
$}
$( The first of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	frb-ax1_0 $f wff ph $.
	frb-ax1_1 $f wff ps $.
	frb-ax1_2 $f wff ch $.
	rb-ax1 $p |- ( -. ( -. ps \/ ch ) \/ ( -. ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $= frb-ax1_1 wn frb-ax1_2 wo frb-ax1_0 frb-ax1_1 wo wn frb-ax1_0 frb-ax1_2 wo wo frb-ax1_1 frb-ax1_2 wi frb-ax1_0 frb-ax1_1 wo frb-ax1_0 frb-ax1_2 wo wi frb-ax1_1 wn frb-ax1_2 wo frb-ax1_0 frb-ax1_1 wo wn frb-ax1_0 frb-ax1_2 wo wo frb-ax1_0 frb-ax1_1 frb-ax1_2 orim2 frb-ax1_1 frb-ax1_2 imor frb-ax1_0 frb-ax1_1 wo frb-ax1_0 frb-ax1_2 wo imor 3imtr3i imori $.
$}
$( The second of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frb-ax2_0 $f wff ph $.
	frb-ax2_1 $f wff ps $.
	rb-ax2 $p |- ( -. ( ph \/ ps ) \/ ( ps \/ ph ) ) $= frb-ax2_0 frb-ax2_1 wo wn frb-ax2_1 frb-ax2_0 wo frb-ax2_1 frb-ax2_0 wo frb-ax2_0 frb-ax2_1 wo wn frb-ax2_0 frb-ax2_1 wo frb-ax2_1 frb-ax2_0 wo frb-ax2_0 frb-ax2_1 pm1.4 con3i con1i orri $.
$}
$( The third of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frb-ax3_0 $f wff ph $.
	frb-ax3_1 $f wff ps $.
	rb-ax3 $p |- ( -. ph \/ ( ps \/ ph ) ) $= frb-ax3_0 wn frb-ax3_1 frb-ax3_0 wo frb-ax3_1 frb-ax3_0 wo frb-ax3_0 wn frb-ax3_1 frb-ax3_0 pm2.46 con1i orri $.
$}
$( The fourth of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	frb-ax4_0 $f wff ph $.
	rb-ax4 $p |- ( -. ( ph \/ ph ) \/ ph ) $= frb-ax4_0 frb-ax4_0 wo wn frb-ax4_0 frb-ax4_0 frb-ax4_0 frb-ax4_0 wo wn frb-ax4_0 frb-ax4_0 wo frb-ax4_0 frb-ax4_0 pm1.2 con3i con1i orri $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	frbsyl_0 $f wff ph $.
	frbsyl_1 $f wff ps $.
	frbsyl_2 $f wff ch $.
	erbsyl_0 $e |- ( -. ps \/ ch ) $.
	erbsyl_1 $e |- ( ph \/ ps ) $.
	rbsyl $p |- ( ph \/ ch ) $= frbsyl_0 frbsyl_1 wo frbsyl_0 frbsyl_2 wo erbsyl_1 frbsyl_1 wn frbsyl_2 wo frbsyl_0 frbsyl_1 wo wn frbsyl_0 frbsyl_2 wo wo erbsyl_0 frbsyl_0 frbsyl_1 frbsyl_2 rb-ax1 anmp anmp $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	frblem1_0 $f wff ph $.
	frblem1_1 $f wff ps $.
	frblem1_2 $f wff ch $.
	frblem1_3 $f wff th $.
	erblem1_0 $e |- ( -. ph \/ ps ) $.
	erblem1_1 $e |- ( -. ch \/ th ) $.
	rblem1 $p |- ( -. ( ph \/ ch ) \/ ( ps \/ th ) ) $= frblem1_0 frblem1_2 wo wn frblem1_1 frblem1_2 wo frblem1_1 frblem1_3 wo frblem1_2 wn frblem1_3 wo frblem1_1 frblem1_2 wo wn frblem1_1 frblem1_3 wo wo erblem1_1 frblem1_1 frblem1_2 frblem1_3 rb-ax1 anmp frblem1_0 frblem1_2 wo wn frblem1_2 frblem1_1 wo frblem1_1 frblem1_2 wo frblem1_2 frblem1_1 rb-ax2 frblem1_0 frblem1_2 wo wn frblem1_2 frblem1_0 wo frblem1_2 frblem1_1 wo frblem1_0 wn frblem1_1 wo frblem1_2 frblem1_0 wo wn frblem1_2 frblem1_1 wo wo erblem1_0 frblem1_2 frblem1_0 frblem1_1 rb-ax1 anmp frblem1_0 frblem1_2 rb-ax2 rbsyl rbsyl rbsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	frblem2_0 $f wff ph $.
	frblem2_1 $f wff ps $.
	frblem2_2 $f wff ch $.
	rblem2 $p |- ( -. ( ch \/ ph ) \/ ( ch \/ ( ph \/ ps ) ) ) $= frblem2_0 wn frblem2_0 frblem2_1 wo wo frblem2_2 frblem2_0 wo wn frblem2_2 frblem2_0 frblem2_1 wo wo wo frblem2_0 wn frblem2_1 frblem2_0 wo frblem2_0 frblem2_1 wo frblem2_1 frblem2_0 rb-ax2 frblem2_0 frblem2_1 rb-ax3 rbsyl frblem2_2 frblem2_0 frblem2_0 frblem2_1 wo rb-ax1 anmp $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	frblem3_0 $f wff ph $.
	frblem3_1 $f wff ps $.
	frblem3_2 $f wff ch $.
	rblem3 $p |- ( -. ( ch \/ ph ) \/ ( ( ch \/ ps ) \/ ph ) ) $= frblem3_2 frblem3_0 wo wn frblem3_0 frblem3_2 frblem3_1 wo wo frblem3_2 frblem3_1 wo frblem3_0 wo frblem3_0 frblem3_2 frblem3_1 wo rb-ax2 frblem3_2 frblem3_0 wo wn frblem3_0 frblem3_2 wo frblem3_0 frblem3_2 frblem3_1 wo wo frblem3_2 frblem3_1 frblem3_0 rblem2 frblem3_2 frblem3_0 rb-ax2 rbsyl rbsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	frblem4_0 $f wff ph $.
	frblem4_1 $f wff ps $.
	frblem4_2 $f wff ch $.
	frblem4_3 $f wff th $.
	frblem4_4 $f wff ta $.
	frblem4_5 $f wff et $.
	erblem4_0 $e |- ( -. ph \/ th ) $.
	erblem4_1 $e |- ( -. ps \/ ta ) $.
	erblem4_2 $e |- ( -. ch \/ et ) $.
	rblem4 $p |- ( -. ( ( ph \/ ps ) \/ ch ) \/ ( ( et \/ ta ) \/ th ) ) $= frblem4_0 frblem4_1 wo frblem4_2 wo wn frblem4_2 frblem4_1 wo frblem4_0 wo frblem4_5 frblem4_4 wo frblem4_3 wo frblem4_2 frblem4_1 wo frblem4_5 frblem4_4 wo frblem4_0 frblem4_3 frblem4_2 frblem4_5 frblem4_1 frblem4_4 erblem4_2 erblem4_1 rblem1 erblem4_0 rblem1 frblem4_0 frblem4_1 wo frblem4_2 wo wn frblem4_1 frblem4_2 wo frblem4_0 wo frblem4_2 frblem4_1 wo frblem4_0 wo frblem4_1 frblem4_2 wo frblem4_0 wo wn frblem4_0 frblem4_2 frblem4_1 wo wo frblem4_2 frblem4_1 wo frblem4_0 wo frblem4_0 frblem4_2 frblem4_1 wo rb-ax2 frblem4_1 frblem4_2 wo frblem4_0 wo wn frblem4_0 frblem4_1 frblem4_2 wo wo frblem4_0 frblem4_2 frblem4_1 wo wo frblem4_1 frblem4_2 wo wn frblem4_2 frblem4_1 wo wo frblem4_0 frblem4_1 frblem4_2 wo wo wn frblem4_0 frblem4_2 frblem4_1 wo wo wo frblem4_1 frblem4_2 rb-ax2 frblem4_0 frblem4_1 frblem4_2 wo frblem4_2 frblem4_1 wo rb-ax1 anmp frblem4_1 frblem4_2 wo frblem4_0 rb-ax2 rbsyl rbsyl frblem4_0 frblem4_1 wo frblem4_2 wo wn frblem4_1 frblem4_2 wo frblem4_0 wo frblem4_1 frblem4_2 wo frblem4_0 wo wo frblem4_1 frblem4_2 wo frblem4_0 wo frblem4_1 frblem4_2 wo frblem4_0 wo rb-ax4 frblem4_0 frblem4_1 wo frblem4_1 frblem4_2 wo frblem4_0 wo frblem4_2 frblem4_1 frblem4_2 wo frblem4_0 wo frblem4_0 frblem4_1 wo wn frblem4_0 frblem4_1 frblem4_2 wo wo frblem4_1 frblem4_2 wo frblem4_0 wo frblem4_0 frblem4_1 frblem4_2 wo rb-ax2 frblem4_1 frblem4_2 frblem4_0 rblem2 rbsyl frblem4_2 wn frblem4_1 frblem4_2 wo wo frblem4_2 wn frblem4_1 frblem4_2 wo frblem4_0 wo wo frblem4_2 frblem4_1 rb-ax3 frblem4_1 frblem4_2 wo frblem4_0 frblem4_2 wn rblem2 anmp rblem1 rbsyl rbsyl rbsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 19-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frblem5_0 $f wff ph $.
	frblem5_1 $f wff ps $.
	rblem5 $p |- ( -. ( -. -. ph \/ ps ) \/ ( -. -. ps \/ ph ) ) $= frblem5_0 wn wn frblem5_1 wo wn frblem5_0 frblem5_1 wn wn wo frblem5_1 wn wn frblem5_0 wo frblem5_0 frblem5_1 wn wn rb-ax2 frblem5_0 wn wn frblem5_0 frblem5_1 frblem5_1 wn wn frblem5_0 wn frblem5_0 wo frblem5_0 wn wn wn frblem5_0 wo frblem5_0 wn frblem5_0 frblem5_0 wo frblem5_0 frblem5_0 rb-ax4 frblem5_0 frblem5_0 rb-ax3 rbsyl frblem5_0 wn frblem5_0 wn wn wn frblem5_0 frblem5_0 frblem5_0 wn wn wn frblem5_0 wn wn wo frblem5_0 wn wn frblem5_0 wn wn wn wo frblem5_0 wn wn wn frblem5_0 wn wn frblem5_0 wn wn wo frblem5_0 wn wn frblem5_0 wn wn rb-ax4 frblem5_0 wn wn frblem5_0 wn wn rb-ax3 rbsyl frblem5_0 wn wn wn frblem5_0 wn wn rb-ax2 anmp frblem5_0 wn frblem5_0 frblem5_0 wo frblem5_0 frblem5_0 rb-ax4 frblem5_0 frblem5_0 rb-ax3 rbsyl rblem1 anmp frblem5_1 wn wn frblem5_1 wn wo frblem5_1 wn frblem5_1 wn wn wo frblem5_1 wn wn frblem5_1 wn frblem5_1 wn wo frblem5_1 wn frblem5_1 wn rb-ax4 frblem5_1 wn frblem5_1 wn rb-ax3 rbsyl frblem5_1 wn wn frblem5_1 wn rb-ax2 anmp rblem1 rbsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frblem6_0 $f wff ph $.
	frblem6_1 $f wff ps $.
	erblem6_0 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
	rblem6 $p |- ( -. ph \/ ps ) $= frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo wn frblem6_0 wn frblem6_1 wo erblem6_0 frblem6_0 wn frblem6_1 wo wn wn frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo wo frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo wn wn frblem6_0 wn frblem6_1 wo wo frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo frblem6_0 wn frblem6_1 wo wn wn wo frblem6_0 wn frblem6_1 wo wn wn frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo wo frblem6_0 wn frblem6_1 wo wn frblem6_0 wn frblem6_1 wo wn wn wo frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo frblem6_0 wn frblem6_1 wo wn wn wo frblem6_0 wn frblem6_1 wo wn wn frblem6_0 wn frblem6_1 wo wn wo frblem6_0 wn frblem6_1 wo wn frblem6_0 wn frblem6_1 wo wn wn wo frblem6_0 wn frblem6_1 wo wn wn frblem6_0 wn frblem6_1 wo wn frblem6_0 wn frblem6_1 wo wn wo frblem6_0 wn frblem6_1 wo wn frblem6_0 wn frblem6_1 wo wn rb-ax4 frblem6_0 wn frblem6_1 wo wn frblem6_0 wn frblem6_1 wo wn rb-ax3 rbsyl frblem6_0 wn frblem6_1 wo wn wn frblem6_0 wn frblem6_1 wo wn rb-ax2 anmp frblem6_0 wn frblem6_1 wo wn wn frblem6_1 wn frblem6_0 wo wn frblem6_0 wn frblem6_1 wo wn rblem3 anmp frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo frblem6_0 wn frblem6_1 wo wn wn rb-ax2 anmp frblem6_0 wn frblem6_1 wo frblem6_0 wn frblem6_1 wo wn frblem6_1 wn frblem6_0 wo wn wo rblem5 anmp anmp $.
$}
$( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	frblem7_0 $f wff ph $.
	frblem7_1 $f wff ps $.
	erblem7_0 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
	rblem7 $p |- ( -. ps \/ ph ) $= frblem7_0 wn frblem7_1 wo wn frblem7_1 wn frblem7_0 wo wn wo wn frblem7_1 wn frblem7_0 wo erblem7_0 frblem7_1 wn frblem7_0 wo wn wn frblem7_0 wn frblem7_1 wo wn frblem7_1 wn frblem7_0 wo wn wo wo frblem7_0 wn frblem7_1 wo wn frblem7_1 wn frblem7_0 wo wn wo wn wn frblem7_1 wn frblem7_0 wo wo frblem7_1 wn frblem7_0 wo wn frblem7_0 wn frblem7_1 wo wn rb-ax3 frblem7_1 wn frblem7_0 wo frblem7_0 wn frblem7_1 wo wn frblem7_1 wn frblem7_0 wo wn wo rblem5 anmp anmp $.
$}
$( ~ ax-mp derived from Russell-Bernays'.  (Contributed by Anthony Hart,
       19-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fre1axmp_0 $f wff ph $.
	fre1axmp_1 $f wff ps $.
	ere1axmp_0 $e |- ph $.
	ere1axmp_1 $e |- ( ph -> ps ) $.
	re1axmp $p |- ps $= fre1axmp_0 fre1axmp_1 ere1axmp_0 fre1axmp_0 fre1axmp_1 wi fre1axmp_0 wn fre1axmp_1 wo ere1axmp_1 fre1axmp_0 fre1axmp_1 wi fre1axmp_0 wn fre1axmp_1 wo fre1axmp_0 fre1axmp_1 rb-imdf rblem6 anmp anmp $.
$}
$( ~ luk-1 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fre2luk1_0 $f wff ph $.
	fre2luk1_1 $f wff ps $.
	fre2luk1_2 $f wff ch $.
	re2luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= fre2luk1_0 fre2luk1_1 wi wn fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi wo fre2luk1_0 fre2luk1_1 wi fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi wi fre2luk1_0 fre2luk1_1 wi wn fre2luk1_1 fre2luk1_2 wi wn fre2luk1_0 fre2luk1_2 wi wo fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi fre2luk1_1 fre2luk1_2 wi wn fre2luk1_0 fre2luk1_2 wi wo fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi rb-imdf rblem7 fre2luk1_0 fre2luk1_1 wi wn fre2luk1_0 wn fre2luk1_1 wo fre2luk1_1 fre2luk1_2 wi wn fre2luk1_0 fre2luk1_2 wi wo fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo wo fre2luk1_1 fre2luk1_2 wi wn fre2luk1_0 fre2luk1_2 wi wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 fre2luk1_2 wi wn fre2luk1_0 wn fre2luk1_2 wo fre2luk1_0 fre2luk1_2 wi fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 wn fre2luk1_2 wo wo fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 fre2luk1_2 wi wn wo fre2luk1_1 fre2luk1_2 wi fre2luk1_1 wn fre2luk1_2 wo fre2luk1_1 fre2luk1_2 rb-imdf rblem6 fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 wn fre2luk1_2 wo wo wn fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 wn fre2luk1_2 wo wn wn wo fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 fre2luk1_2 wi wn wo fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 wn fre2luk1_2 wo wn wn rb-ax2 fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 wn fre2luk1_2 wo fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 fre2luk1_2 wi wn wn fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 fre2luk1_2 wi wn wo fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 fre2luk1_2 wi wn rb-ax4 fre2luk1_1 fre2luk1_2 wi wn fre2luk1_1 fre2luk1_2 wi wn rb-ax3 rbsyl fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 wn fre2luk1_2 wo wn wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn wn wo fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn rb-ax4 fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn rb-ax3 rbsyl fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 wn fre2luk1_2 wo wn rb-ax2 anmp rblem1 rbsyl anmp fre2luk1_0 fre2luk1_2 wi fre2luk1_0 wn fre2luk1_2 wo fre2luk1_0 fre2luk1_2 rb-imdf rblem7 rblem1 fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo wo wo fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo wo wo fre2luk1_0 wn fre2luk1_1 fre2luk1_2 rb-ax1 fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo wo wo wn fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo wo fre2luk1_0 wn fre2luk1_1 wo wn wo fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo wo wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo wo fre2luk1_0 wn fre2luk1_1 wo wn rb-ax2 fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo wo wo wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo wo fre2luk1_1 wn fre2luk1_2 wo wn wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo wo fre2luk1_0 wn fre2luk1_1 wo wn wo fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_1 wo wn wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_1 wo wn wo fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_1 wo wn rb-ax4 fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_1 wo wn rb-ax3 rbsyl fre2luk1_0 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_2 wo fre2luk1_0 wn fre2luk1_2 wo wo fre2luk1_0 wn fre2luk1_2 wo fre2luk1_0 wn fre2luk1_2 wo rb-ax4 fre2luk1_0 wn fre2luk1_2 wo fre2luk1_0 wn fre2luk1_2 wo rb-ax3 rbsyl fre2luk1_1 wn fre2luk1_2 wo wn wn fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn wo fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn rb-ax4 fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_1 wn fre2luk1_2 wo wn rb-ax3 rbsyl rblem4 fre2luk1_1 wn fre2luk1_2 wo wn fre2luk1_0 wn fre2luk1_1 wo wn fre2luk1_0 wn fre2luk1_2 wo wo rb-ax2 rbsyl rbsyl anmp rbsyl fre2luk1_0 fre2luk1_1 wi fre2luk1_0 wn fre2luk1_1 wo fre2luk1_0 fre2luk1_1 rb-imdf rblem6 rbsyl rbsyl fre2luk1_0 fre2luk1_1 wi fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi wi fre2luk1_0 fre2luk1_1 wi wn fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi wo fre2luk1_0 fre2luk1_1 wi fre2luk1_1 fre2luk1_2 wi fre2luk1_0 fre2luk1_2 wi wi rb-imdf rblem7 anmp $.
$}
$( ~ luk-2 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	fre2luk2_0 $f wff ph $.
	re2luk2 $p |- ( ( -. ph -> ph ) -> ph ) $= fre2luk2_0 wn fre2luk2_0 wi wn fre2luk2_0 wo fre2luk2_0 wn fre2luk2_0 wi fre2luk2_0 wi fre2luk2_0 wn fre2luk2_0 wi wn fre2luk2_0 wn wn fre2luk2_0 wo fre2luk2_0 fre2luk2_0 wn wn fre2luk2_0 wo wn fre2luk2_0 fre2luk2_0 wo fre2luk2_0 fre2luk2_0 rb-ax4 fre2luk2_0 wn wn fre2luk2_0 fre2luk2_0 fre2luk2_0 fre2luk2_0 wn fre2luk2_0 wo fre2luk2_0 wn wn wn fre2luk2_0 wo fre2luk2_0 wn fre2luk2_0 fre2luk2_0 wo fre2luk2_0 fre2luk2_0 rb-ax4 fre2luk2_0 fre2luk2_0 rb-ax3 rbsyl fre2luk2_0 wn fre2luk2_0 wn wn wn fre2luk2_0 fre2luk2_0 fre2luk2_0 wn wn wn fre2luk2_0 wn wn wo fre2luk2_0 wn wn fre2luk2_0 wn wn wn wo fre2luk2_0 wn wn wn fre2luk2_0 wn wn fre2luk2_0 wn wn wo fre2luk2_0 wn wn fre2luk2_0 wn wn rb-ax4 fre2luk2_0 wn wn fre2luk2_0 wn wn rb-ax3 rbsyl fre2luk2_0 wn wn wn fre2luk2_0 wn wn rb-ax2 anmp fre2luk2_0 wn fre2luk2_0 fre2luk2_0 wo fre2luk2_0 fre2luk2_0 rb-ax4 fre2luk2_0 fre2luk2_0 rb-ax3 rbsyl rblem1 anmp fre2luk2_0 wn fre2luk2_0 fre2luk2_0 wo fre2luk2_0 fre2luk2_0 rb-ax4 fre2luk2_0 fre2luk2_0 rb-ax3 rbsyl rblem1 rbsyl fre2luk2_0 wn fre2luk2_0 wi fre2luk2_0 wn wn fre2luk2_0 wo fre2luk2_0 wn fre2luk2_0 rb-imdf rblem6 rbsyl fre2luk2_0 wn fre2luk2_0 wi fre2luk2_0 wi fre2luk2_0 wn fre2luk2_0 wi wn fre2luk2_0 wo fre2luk2_0 wn fre2luk2_0 wi fre2luk2_0 rb-imdf rblem7 anmp $.
$}
$( ~ luk-3 derived from Russell-Bernays'.

     This theorem, along with ~ re1axmp , ~ re2luk1 , and ~ re2luk2 shows that
     ~ rb-ax1 , ~ rb-ax2 , ~ rb-ax3 , and ~ rb-ax4 , along with ~ anmp , can be
     used as a complete axiomatization of propositional calculus.  (Contributed
     by Anthony Hart, 19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fre2luk3_0 $f wff ph $.
	fre2luk3_1 $f wff ps $.
	re2luk3 $p |- ( ph -> ( -. ph -> ps ) ) $= fre2luk3_0 wn fre2luk3_0 wn fre2luk3_1 wi wo fre2luk3_0 fre2luk3_0 wn fre2luk3_1 wi wi fre2luk3_0 wn fre2luk3_0 wn wn fre2luk3_1 wo fre2luk3_0 wn fre2luk3_1 wi fre2luk3_0 wn fre2luk3_1 wi fre2luk3_0 wn wn fre2luk3_1 wo fre2luk3_0 wn fre2luk3_1 rb-imdf rblem7 fre2luk3_0 wn fre2luk3_0 wn wn wo fre2luk3_0 wn fre2luk3_0 wn wn fre2luk3_1 wo wo fre2luk3_0 wn wn fre2luk3_0 wn wo fre2luk3_0 wn fre2luk3_0 wn wn wo fre2luk3_0 wn wn fre2luk3_0 wn fre2luk3_0 wn wo fre2luk3_0 wn fre2luk3_0 wn rb-ax4 fre2luk3_0 wn fre2luk3_0 wn rb-ax3 rbsyl fre2luk3_0 wn wn fre2luk3_0 wn rb-ax2 anmp fre2luk3_0 wn wn fre2luk3_1 fre2luk3_0 wn rblem2 anmp rbsyl fre2luk3_0 fre2luk3_0 wn fre2luk3_1 wi wi fre2luk3_0 wn fre2luk3_0 wn fre2luk3_1 wi wo fre2luk3_0 fre2luk3_0 wn fre2luk3_1 wi rb-imdf rblem7 anmp $.
$}

