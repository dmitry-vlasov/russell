$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_Nicod_s_Axiom_from_Lukasiewicz_s_First_Sheffer_Stroke_Axiom.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz Axioms from the Tarski-Bernays-Wajsberg Axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Justification for ~ tbw-negdf .  (Contributed by Anthony Hart,
     15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	ftbw-bijust_0 $f wff ph $.
	ftbw-bijust_1 $f wff ps $.
	tbw-bijust $p |- ( ( ph <-> ps ) <-> ( ( ( ph -> ps ) -> ( ( ps -> ph ) -> F. ) ) -> F. ) ) $= ftbw-bijust_0 ftbw-bijust_1 wb ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wn wi wn ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wn ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal wi ftbw-bijust_0 ftbw-bijust_1 dfbi1 ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wn wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wn wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi ftbw-bijust_1 ftbw-bijust_0 wi wn ftbw-bijust_1 ftbw-bijust_0 wi wfal wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal pm2.21 imim2i ftbw-bijust_1 ftbw-bijust_0 wi wfal wi ftbw-bijust_1 ftbw-bijust_0 wi wn ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal ftbw-bijust_1 ftbw-bijust_0 wi wn ftbw-bijust_1 ftbw-bijust_0 wi wn id ftbw-bijust_1 ftbw-bijust_0 wi wn falim ja imim2i impbii notbii ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wn ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal pm2.21 ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wn ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wn wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wn ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal wi ax-1 ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wfal wi ftbw-bijust_0 ftbw-bijust_1 wi ftbw-bijust_1 ftbw-bijust_0 wi wfal wi wi wn wi falim ja pm2.43i impbii 3bitri $.
$}
$( The definition of negation, in terms of ` -> ` and ` F. ` .  (Contributed
     by Anthony Hart, 15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	ftbw-negdf_0 $f wff ph $.
	tbw-negdf $p |- ( ( ( -. ph -> ( ph -> F. ) ) -> ( ( ( ph -> F. ) -> -. ph ) -> F. ) ) -> F. ) $= ftbw-negdf_0 wn ftbw-negdf_0 wfal wi wb ftbw-negdf_0 wn ftbw-negdf_0 wfal wi wi ftbw-negdf_0 wfal wi ftbw-negdf_0 wn wi wfal wi wi wfal wi ftbw-negdf_0 wn ftbw-negdf_0 wfal wi ftbw-negdf_0 wfal pm2.21 ftbw-negdf_0 wfal wi ftbw-negdf_0 wn ftbw-negdf_0 wfal ftbw-negdf_0 wfal wi ftbw-negdf_0 wn wi ftbw-negdf_0 wn ftbw-negdf_0 wfal wi ax-1 ftbw-negdf_0 wfal wi ftbw-negdf_0 wn wi falim ja pm2.43i impbii ftbw-negdf_0 wn ftbw-negdf_0 wfal wi tbw-bijust mpbi $.
$}
$( The first of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbw-ax1_0 $f wff ph $.
	ftbw-ax1_1 $f wff ps $.
	ftbw-ax1_2 $f wff ch $.
	tbw-ax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= ftbw-ax1_0 ftbw-ax1_1 ftbw-ax1_2 imim1 $.
$}
$( The second of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbw-ax2_0 $f wff ph $.
	ftbw-ax2_1 $f wff ps $.
	tbw-ax2 $p |- ( ph -> ( ps -> ph ) ) $= ftbw-ax2_0 ftbw-ax2_1 ax-1 $.
$}
$( The third of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbw-ax3_0 $f wff ph $.
	ftbw-ax3_1 $f wff ps $.
	tbw-ax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $= ftbw-ax3_0 ftbw-ax3_1 peirce $.
$}
$( The fourth of four axioms in the Tarski-Bernays-Wajsberg system.

     This axiom was added to the Tarski-Bernays axiom system ( see ~ tb-ax1 ,
     ~ tb-ax2 , and ~ tb-ax3 ) by Wajsberg for completeness.  (Contributed by
     Anthony Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	ftbw-ax4_0 $f wff ph $.
	tbw-ax4 $p |- ( F. -> ph ) $= ftbw-ax4_0 falim $.
$}
$( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
       (Contributed by Anthony Hart, 16-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbwsyl_0 $f wff ph $.
	ftbwsyl_1 $f wff ps $.
	ftbwsyl_2 $f wff ch $.
	etbwsyl_0 $e |- ( ph -> ps ) $.
	etbwsyl_1 $e |- ( ps -> ch ) $.
	tbwsyl $p |- ( ph -> ch ) $= ftbwsyl_1 ftbwsyl_2 wi ftbwsyl_0 ftbwsyl_2 wi etbwsyl_1 ftbwsyl_0 ftbwsyl_1 wi ftbwsyl_1 ftbwsyl_2 wi ftbwsyl_0 ftbwsyl_2 wi wi etbwsyl_0 ftbwsyl_0 ftbwsyl_1 ftbwsyl_2 tbw-ax1 ax-mp ax-mp $.
$}
$( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbwlem1_0 $f wff ph $.
	ftbwlem1_1 $f wff ps $.
	ftbwlem1_2 $f wff ch $.
	tbwlem1 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= ftbwlem1_1 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi wi ftbwlem1_0 ftbwlem1_1 ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_0 ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_0 ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_1 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_1 ftbwlem1_2 wi tbw-ax2 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 tbw-ax1 tbwsyl ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_2 tbw-ax1 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_2 tbw-ax3 tbwsyl tbwsyl ftbwlem1_0 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 tbw-ax1 ftbwlem1_1 ftbwlem1_1 ftbwlem1_2 wi ftbwlem1_2 wi ftbwlem1_0 ftbwlem1_2 wi tbw-ax1 mpsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbwlem2_0 $f wff ph $.
	ftbwlem2_1 $f wff ps $.
	ftbwlem2_2 $f wff ch $.
	ftbwlem2_3 $f wff th $.
	tbwlem2 $p |- ( ( ph -> ( ps -> F. ) ) -> ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $= ftbwlem2_0 ftbwlem2_1 wfal wi wi ftbwlem2_1 ftbwlem2_0 ftbwlem2_2 wi wi ftbwlem2_0 ftbwlem2_2 wi ftbwlem2_3 wi ftbwlem2_1 ftbwlem2_3 wi wi ftbwlem2_1 ftbwlem2_1 wfal wi ftbwlem2_2 wi wi ftbwlem2_0 ftbwlem2_1 wfal wi wi ftbwlem2_1 wfal wi ftbwlem2_2 wi ftbwlem2_0 ftbwlem2_2 wi wi ftbwlem2_1 ftbwlem2_0 ftbwlem2_2 wi wi ftbwlem2_1 wfal wi ftbwlem2_1 ftbwlem2_2 wi wi ftbwlem2_1 ftbwlem2_1 wfal wi ftbwlem2_2 wi wi wfal ftbwlem2_2 wi ftbwlem2_1 wfal wi ftbwlem2_1 ftbwlem2_2 wi wi ftbwlem2_2 tbw-ax4 ftbwlem2_1 wfal wi wfal ftbwlem2_2 wi ftbwlem2_1 ftbwlem2_2 wi wi wi wfal ftbwlem2_2 wi ftbwlem2_1 wfal wi ftbwlem2_1 ftbwlem2_2 wi wi wi ftbwlem2_1 wfal ftbwlem2_2 tbw-ax1 ftbwlem2_1 wfal wi wfal ftbwlem2_2 wi ftbwlem2_1 ftbwlem2_2 wi tbwlem1 ax-mp ax-mp ftbwlem2_1 wfal wi ftbwlem2_1 ftbwlem2_2 tbwlem1 ax-mp ftbwlem2_0 ftbwlem2_1 wfal wi ftbwlem2_2 tbw-ax1 ftbwlem2_1 ftbwlem2_1 wfal wi ftbwlem2_2 wi ftbwlem2_0 ftbwlem2_2 wi tbw-ax1 mpsyl ftbwlem2_1 ftbwlem2_0 ftbwlem2_2 wi ftbwlem2_3 tbw-ax1 tbwsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbwlem3_0 $f wff ph $.
	ftbwlem3_1 $f wff ps $.
	tbwlem3 $p |- ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps ) $= ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi wi ftbwlem3_0 wfal tbw-ax3 ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi tbw-ax2 ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 tbw-ax1 tbwsyl ax-mp ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi ftbwlem3_1 tbw-ax1 ftbwlem3_0 wfal wi ftbwlem3_0 wi ftbwlem3_0 wi ftbwlem3_1 wi ftbwlem3_1 wi ftbwlem3_1 tbw-ax3 tbwsyl ax-mp $.
$}
$( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbwlem4_0 $f wff ph $.
	ftbwlem4_1 $f wff ps $.
	tbwlem4 $p |- ( ( ( ph -> F. ) -> ps ) -> ( ( ps -> F. ) -> ph ) ) $= ftbwlem4_0 wfal wi ftbwlem4_1 wi ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi wfal wi wi ftbwlem4_1 wfal wi ftbwlem4_0 wi ftbwlem4_1 ftbwlem4_1 wfal wi wfal wi wi ftbwlem4_0 wfal wi ftbwlem4_1 wi ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi wfal wi wi wi ftbwlem4_1 wfal wi ftbwlem4_1 wfal wi wi ftbwlem4_1 ftbwlem4_1 wfal wi wfal wi wi wfal wfal wi ftbwlem4_1 wfal wi ftbwlem4_1 wfal wi wi wfal tbw-ax4 ftbwlem4_1 wfal wi wfal wfal wi ftbwlem4_1 wfal wi wi wi wfal wfal wi ftbwlem4_1 wfal wi ftbwlem4_1 wfal wi wi wi ftbwlem4_1 wfal wfal tbw-ax1 ftbwlem4_1 wfal wi wfal wfal wi ftbwlem4_1 wfal wi tbwlem1 ax-mp ax-mp ftbwlem4_1 wfal wi ftbwlem4_1 wfal tbwlem1 ax-mp ftbwlem4_0 wfal wi ftbwlem4_1 wi ftbwlem4_1 ftbwlem4_1 wfal wi wfal wi wi ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi wfal wi wi wi wi ftbwlem4_1 ftbwlem4_1 wfal wi wfal wi wi ftbwlem4_0 wfal wi ftbwlem4_1 wi ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi wfal wi wi wi wi ftbwlem4_0 wfal wi ftbwlem4_1 ftbwlem4_1 wfal wi wfal wi tbw-ax1 ftbwlem4_0 wfal wi ftbwlem4_1 wi ftbwlem4_1 ftbwlem4_1 wfal wi wfal wi wi ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi wfal wi wi tbwlem1 ax-mp ax-mp ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi wfal wi wi ftbwlem4_0 wfal wi ftbwlem4_0 wi ftbwlem4_0 wi ftbwlem4_1 wfal wi ftbwlem4_0 wi wi ftbwlem4_1 wfal wi ftbwlem4_0 wi ftbwlem4_0 wfal wi ftbwlem4_1 wfal wi ftbwlem4_0 ftbwlem4_0 tbwlem2 ftbwlem4_0 ftbwlem4_1 wfal wi ftbwlem4_0 wi tbwlem3 tbwsyl tbwsyl $.
$}
$( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	ftbwlem5_0 $f wff ph $.
	ftbwlem5_1 $f wff ps $.
	tbwlem5 $p |- ( ( ( ph -> ( ps -> F. ) ) -> F. ) -> ph ) $= ftbwlem5_0 wfal wi ftbwlem5_0 ftbwlem5_1 wfal wi wi wi ftbwlem5_0 ftbwlem5_1 wfal wi wi wfal wi ftbwlem5_0 wi ftbwlem5_0 ftbwlem5_0 wfal wi ftbwlem5_1 wfal wi wi wi ftbwlem5_0 wfal wi ftbwlem5_0 ftbwlem5_1 wfal wi wi wi ftbwlem5_0 ftbwlem5_1 ftbwlem5_0 wi ftbwlem5_0 wfal wi ftbwlem5_1 wfal wi wi ftbwlem5_0 ftbwlem5_1 tbw-ax2 ftbwlem5_1 ftbwlem5_0 wfal tbw-ax1 tbwsyl ftbwlem5_0 ftbwlem5_0 wfal wi ftbwlem5_1 wfal wi tbwlem1 ax-mp ftbwlem5_0 ftbwlem5_0 ftbwlem5_1 wfal wi wi tbwlem4 ax-mp $.
$}
$( ~ luk-1 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fre1luk1_0 $f wff ph $.
	fre1luk1_1 $f wff ps $.
	fre1luk1_2 $f wff ch $.
	re1luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= fre1luk1_0 fre1luk1_1 fre1luk1_2 tbw-ax1 $.
$}
$( ~ luk-2 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fre1luk2_0 $f wff ph $.
	re1luk2 $p |- ( ( -. ph -> ph ) -> ph ) $= fre1luk2_0 wn fre1luk2_0 wi fre1luk2_0 wfal wi fre1luk2_0 wi fre1luk2_0 fre1luk2_0 wfal wi fre1luk2_0 wn wi fre1luk2_0 wn fre1luk2_0 wi fre1luk2_0 wfal wi fre1luk2_0 wi wi fre1luk2_0 wn fre1luk2_0 wfal wi wi fre1luk2_0 wfal wi fre1luk2_0 wn wi wfal wi wi wfal wi fre1luk2_0 wfal wi fre1luk2_0 wn wi fre1luk2_0 tbw-negdf fre1luk2_0 wfal wi fre1luk2_0 wn wi wfal wi fre1luk2_0 wn fre1luk2_0 wfal wi wi fre1luk2_0 wfal wi fre1luk2_0 wn wi wfal wi wi wi fre1luk2_0 wn fre1luk2_0 wfal wi wi fre1luk2_0 wfal wi fre1luk2_0 wn wi wfal wi wi wfal wi fre1luk2_0 wfal wi fre1luk2_0 wn wi wi fre1luk2_0 wfal wi fre1luk2_0 wn wi wfal wi fre1luk2_0 wn fre1luk2_0 wfal wi wi tbw-ax2 fre1luk2_0 wfal wi fre1luk2_0 wn wi fre1luk2_0 wn fre1luk2_0 wfal wi wi fre1luk2_0 wfal wi fre1luk2_0 wn wi wfal wi wi tbwlem4 ax-mp ax-mp fre1luk2_0 wfal wi fre1luk2_0 wn fre1luk2_0 tbw-ax1 ax-mp fre1luk2_0 wfal tbw-ax3 tbwsyl $.
$}
$( ~ luk-3 derived from the Tarski-Bernays-Wajsberg axioms.

     This theorem, along with ~ re1luk1 and ~ re1luk2 proves that ~ tbw-ax1 ,
     ~ tbw-ax2 , ~ tbw-ax3 , and ~ tbw-ax4 , with ~ ax-mp can be used as a
     complete axiom system for all of propositional calculus.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fre1luk3_0 $f wff ph $.
	fre1luk3_1 $f wff ps $.
	re1luk3 $p |- ( ph -> ( -. ph -> ps ) ) $= fre1luk3_0 wn fre1luk3_0 wfal wi wi fre1luk3_0 fre1luk3_0 wfal wi fre1luk3_1 wi fre1luk3_0 wn fre1luk3_1 wi fre1luk3_0 wn fre1luk3_0 wfal wi wi fre1luk3_0 wfal wi fre1luk3_0 wn wi wfal wi wi wfal wi fre1luk3_0 wn fre1luk3_0 wfal wi wi fre1luk3_0 tbw-negdf fre1luk3_0 wn fre1luk3_0 wfal wi wi fre1luk3_0 wfal wi fre1luk3_0 wn wi tbwlem5 ax-mp fre1luk3_0 wfal wi fre1luk3_0 fre1luk3_1 wi wi fre1luk3_0 fre1luk3_0 wfal wi fre1luk3_1 wi wi wfal fre1luk3_1 wi fre1luk3_0 wfal wi fre1luk3_0 fre1luk3_1 wi wi fre1luk3_1 tbw-ax4 fre1luk3_0 wfal wi wfal fre1luk3_1 wi fre1luk3_0 fre1luk3_1 wi wi wi wfal fre1luk3_1 wi fre1luk3_0 wfal wi fre1luk3_0 fre1luk3_1 wi wi wi fre1luk3_0 wfal fre1luk3_1 tbw-ax1 fre1luk3_0 wfal wi wfal fre1luk3_1 wi fre1luk3_0 fre1luk3_1 wi tbwlem1 ax-mp ax-mp fre1luk3_0 wfal wi fre1luk3_0 fre1luk3_1 tbwlem1 ax-mp fre1luk3_0 wn fre1luk3_0 wfal wi fre1luk3_1 tbw-ax1 mpsyl $.
$}

