$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_Nicod_s_Axiom_from_Lukasiewicz_s_First_Sheffer_Stroke_Axiom.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz Axioms from the Tarski-Bernays-Wajsberg Axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Justification for ~ tbw-negdf .  (Contributed by Anthony Hart,
     15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_tbw-bijust $f wff ph $.
	f1_tbw-bijust $f wff ps $.
	p_tbw-bijust $p |- ( ( ph <-> ps ) <-> ( ( ( ph -> ps ) -> ( ( ps -> ph ) -> F. ) ) -> F. ) ) $= f0_tbw-bijust f1_tbw-bijust p_dfbi1 f1_tbw-bijust f0_tbw-bijust a_wi a_wfal p_pm2.21 f1_tbw-bijust f0_tbw-bijust a_wi a_wn f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi f0_tbw-bijust f1_tbw-bijust a_wi p_imim2i f1_tbw-bijust f0_tbw-bijust a_wi a_wn p_id f1_tbw-bijust f0_tbw-bijust a_wi a_wn p_falim f1_tbw-bijust f0_tbw-bijust a_wi a_wfal f1_tbw-bijust f0_tbw-bijust a_wi a_wn p_ja f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wn f0_tbw-bijust f1_tbw-bijust a_wi p_imim2i f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wn a_wi f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi p_impbii f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wn a_wi f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi p_notbii f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal p_pm2.21 f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wn f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal a_wi a_ax-1 f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal a_wi f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wn a_wi p_falim f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal a_wi f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wn a_wi p_ja f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal a_wi f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wn p_pm2.43i f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wn f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal a_wi p_impbii f0_tbw-bijust f1_tbw-bijust a_wb f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wn a_wi a_wn f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wn f0_tbw-bijust f1_tbw-bijust a_wi f1_tbw-bijust f0_tbw-bijust a_wi a_wfal a_wi a_wi a_wfal a_wi p_3bitri $.
$}

$(The definition of negation, in terms of ` -> ` and ` F. ` .  (Contributed
     by Anthony Hart, 15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph  $.
	f0_tbw-negdf $f wff ph $.
	p_tbw-negdf $p |- ( ( ( -. ph -> ( ph -> F. ) ) -> ( ( ( ph -> F. ) -> -. ph ) -> F. ) ) -> F. ) $= f0_tbw-negdf a_wfal p_pm2.21 f0_tbw-negdf a_wn f0_tbw-negdf a_wfal a_wi a_ax-1 f0_tbw-negdf a_wfal a_wi f0_tbw-negdf a_wn a_wi p_falim f0_tbw-negdf a_wfal f0_tbw-negdf a_wfal a_wi f0_tbw-negdf a_wn a_wi p_ja f0_tbw-negdf a_wfal a_wi f0_tbw-negdf a_wn p_pm2.43i f0_tbw-negdf a_wn f0_tbw-negdf a_wfal a_wi p_impbii f0_tbw-negdf a_wn f0_tbw-negdf a_wfal a_wi p_tbw-bijust f0_tbw-negdf a_wn f0_tbw-negdf a_wfal a_wi a_wb f0_tbw-negdf a_wn f0_tbw-negdf a_wfal a_wi a_wi f0_tbw-negdf a_wfal a_wi f0_tbw-negdf a_wn a_wi a_wfal a_wi a_wi a_wfal a_wi p_mpbi $.
$}

$(The first of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_tbw-ax1 $f wff ph $.
	f1_tbw-ax1 $f wff ps $.
	f2_tbw-ax1 $f wff ch $.
	p_tbw-ax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= f0_tbw-ax1 f1_tbw-ax1 f2_tbw-ax1 p_imim1 $.
$}

$(The second of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_tbw-ax2 $f wff ph $.
	f1_tbw-ax2 $f wff ps $.
	p_tbw-ax2 $p |- ( ph -> ( ps -> ph ) ) $= f0_tbw-ax2 f1_tbw-ax2 a_ax-1 $.
$}

$(The third of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_tbw-ax3 $f wff ph $.
	f1_tbw-ax3 $f wff ps $.
	p_tbw-ax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $= f0_tbw-ax3 f1_tbw-ax3 p_peirce $.
$}

$(The fourth of four axioms in the Tarski-Bernays-Wajsberg system.

     This axiom was added to the Tarski-Bernays axiom system ( see ~ tb-ax1 ,
     ~ tb-ax2 , and ~ tb-ax3 ) by Wajsberg for completeness.  (Contributed by
     Anthony Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph  $.
	f0_tbw-ax4 $f wff ph $.
	p_tbw-ax4 $p |- ( F. -> ph ) $= f0_tbw-ax4 p_falim $.
$}

$(Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
       (Contributed by Anthony Hart, 16-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_tbwsyl $f wff ph $.
	f1_tbwsyl $f wff ps $.
	f2_tbwsyl $f wff ch $.
	e0_tbwsyl $e |- ( ph -> ps ) $.
	e1_tbwsyl $e |- ( ps -> ch ) $.
	p_tbwsyl $p |- ( ph -> ch ) $= e1_tbwsyl e0_tbwsyl f0_tbwsyl f1_tbwsyl f2_tbwsyl p_tbw-ax1 f0_tbwsyl f1_tbwsyl a_wi f1_tbwsyl f2_tbwsyl a_wi f0_tbwsyl f2_tbwsyl a_wi a_wi a_ax-mp f1_tbwsyl f2_tbwsyl a_wi f0_tbwsyl f2_tbwsyl a_wi a_ax-mp $.
$}

$(Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_tbwlem1 $f wff ph $.
	f1_tbwlem1 $f wff ps $.
	f2_tbwlem1 $f wff ch $.
	p_tbwlem1 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= f1_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi p_tbw-ax2 f1_tbwlem1 f2_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 p_tbw-ax1 f1_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi f1_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi a_wi p_tbwsyl f1_tbwlem1 f2_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi f2_tbwlem1 p_tbw-ax1 f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi f2_tbwlem1 p_tbw-ax3 f1_tbwlem1 f2_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi f2_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi p_tbwsyl f1_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi p_tbwsyl f0_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 p_tbw-ax1 f1_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi f0_tbwlem1 f2_tbwlem1 a_wi p_tbw-ax1 f1_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi a_wi f0_tbwlem1 f1_tbwlem1 f2_tbwlem1 a_wi a_wi f1_tbwlem1 f2_tbwlem1 a_wi f2_tbwlem1 a_wi f0_tbwlem1 f2_tbwlem1 a_wi a_wi f1_tbwlem1 f0_tbwlem1 f2_tbwlem1 a_wi a_wi p_mpsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_tbwlem2 $f wff ph $.
	f1_tbwlem2 $f wff ps $.
	f2_tbwlem2 $f wff ch $.
	f3_tbwlem2 $f wff th $.
	p_tbwlem2 $p |- ( ( ph -> ( ps -> F. ) ) -> ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $= f2_tbwlem2 p_tbw-ax4 f1_tbwlem2 a_wfal f2_tbwlem2 p_tbw-ax1 f1_tbwlem2 a_wfal a_wi a_wfal f2_tbwlem2 a_wi f1_tbwlem2 f2_tbwlem2 a_wi p_tbwlem1 f1_tbwlem2 a_wfal a_wi a_wfal f2_tbwlem2 a_wi f1_tbwlem2 f2_tbwlem2 a_wi a_wi a_wi a_wfal f2_tbwlem2 a_wi f1_tbwlem2 a_wfal a_wi f1_tbwlem2 f2_tbwlem2 a_wi a_wi a_wi a_ax-mp a_wfal f2_tbwlem2 a_wi f1_tbwlem2 a_wfal a_wi f1_tbwlem2 f2_tbwlem2 a_wi a_wi a_ax-mp f1_tbwlem2 a_wfal a_wi f1_tbwlem2 f2_tbwlem2 p_tbwlem1 f1_tbwlem2 a_wfal a_wi f1_tbwlem2 f2_tbwlem2 a_wi a_wi f1_tbwlem2 f1_tbwlem2 a_wfal a_wi f2_tbwlem2 a_wi a_wi a_ax-mp f0_tbwlem2 f1_tbwlem2 a_wfal a_wi f2_tbwlem2 p_tbw-ax1 f1_tbwlem2 f1_tbwlem2 a_wfal a_wi f2_tbwlem2 a_wi f0_tbwlem2 f2_tbwlem2 a_wi p_tbw-ax1 f1_tbwlem2 f1_tbwlem2 a_wfal a_wi f2_tbwlem2 a_wi a_wi f0_tbwlem2 f1_tbwlem2 a_wfal a_wi a_wi f1_tbwlem2 a_wfal a_wi f2_tbwlem2 a_wi f0_tbwlem2 f2_tbwlem2 a_wi a_wi f1_tbwlem2 f0_tbwlem2 f2_tbwlem2 a_wi a_wi p_mpsyl f1_tbwlem2 f0_tbwlem2 f2_tbwlem2 a_wi f3_tbwlem2 p_tbw-ax1 f0_tbwlem2 f1_tbwlem2 a_wfal a_wi a_wi f1_tbwlem2 f0_tbwlem2 f2_tbwlem2 a_wi a_wi f0_tbwlem2 f2_tbwlem2 a_wi f3_tbwlem2 a_wi f1_tbwlem2 f3_tbwlem2 a_wi a_wi p_tbwsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_tbwlem3 $f wff ph $.
	f1_tbwlem3 $f wff ps $.
	p_tbwlem3 $p |- ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps ) $= f0_tbwlem3 a_wfal p_tbw-ax3 f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi p_tbw-ax2 f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 p_tbw-ax1 f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi a_wi p_tbwsyl f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi a_wi a_ax-mp f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 p_tbw-ax1 f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 p_tbw-ax3 f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi p_tbwsyl f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi a_wi f0_tbwlem3 a_wfal a_wi f0_tbwlem3 a_wi f0_tbwlem3 a_wi f1_tbwlem3 a_wi f1_tbwlem3 a_wi a_ax-mp $.
$}

$(Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_tbwlem4 $f wff ph $.
	f1_tbwlem4 $f wff ps $.
	p_tbwlem4 $p |- ( ( ( ph -> F. ) -> ps ) -> ( ( ps -> F. ) -> ph ) ) $= a_wfal p_tbw-ax4 f1_tbwlem4 a_wfal a_wfal p_tbw-ax1 f1_tbwlem4 a_wfal a_wi a_wfal a_wfal a_wi f1_tbwlem4 a_wfal a_wi p_tbwlem1 f1_tbwlem4 a_wfal a_wi a_wfal a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wi a_wi a_wfal a_wfal a_wi f1_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wi a_wi a_ax-mp a_wfal a_wfal a_wi f1_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wi a_ax-mp f1_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal p_tbwlem1 f1_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wi f1_tbwlem4 f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi a_ax-mp f0_tbwlem4 a_wfal a_wi f1_tbwlem4 f1_tbwlem4 a_wfal a_wi a_wfal a_wi p_tbw-ax1 f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wi f1_tbwlem4 f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi p_tbwlem1 f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wi f1_tbwlem4 f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi a_wi a_wi f1_tbwlem4 f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi a_wi a_wi a_ax-mp f1_tbwlem4 f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi a_wi a_ax-mp f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi f0_tbwlem4 f0_tbwlem4 p_tbwlem2 f0_tbwlem4 f1_tbwlem4 a_wfal a_wi f0_tbwlem4 a_wi p_tbwlem3 f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi f0_tbwlem4 a_wfal a_wi f0_tbwlem4 a_wi f0_tbwlem4 a_wi f1_tbwlem4 a_wfal a_wi f0_tbwlem4 a_wi a_wi f1_tbwlem4 a_wfal a_wi f0_tbwlem4 a_wi p_tbwsyl f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wi f0_tbwlem4 a_wfal a_wi f1_tbwlem4 a_wfal a_wi a_wfal a_wi a_wi f1_tbwlem4 a_wfal a_wi f0_tbwlem4 a_wi p_tbwsyl $.
$}

$(Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_tbwlem5 $f wff ph $.
	f1_tbwlem5 $f wff ps $.
	p_tbwlem5 $p |- ( ( ( ph -> ( ps -> F. ) ) -> F. ) -> ph ) $= f0_tbwlem5 f1_tbwlem5 p_tbw-ax2 f1_tbwlem5 f0_tbwlem5 a_wfal p_tbw-ax1 f0_tbwlem5 f1_tbwlem5 f0_tbwlem5 a_wi f0_tbwlem5 a_wfal a_wi f1_tbwlem5 a_wfal a_wi a_wi p_tbwsyl f0_tbwlem5 f0_tbwlem5 a_wfal a_wi f1_tbwlem5 a_wfal a_wi p_tbwlem1 f0_tbwlem5 f0_tbwlem5 a_wfal a_wi f1_tbwlem5 a_wfal a_wi a_wi a_wi f0_tbwlem5 a_wfal a_wi f0_tbwlem5 f1_tbwlem5 a_wfal a_wi a_wi a_wi a_ax-mp f0_tbwlem5 f0_tbwlem5 f1_tbwlem5 a_wfal a_wi a_wi p_tbwlem4 f0_tbwlem5 a_wfal a_wi f0_tbwlem5 f1_tbwlem5 a_wfal a_wi a_wi a_wi f0_tbwlem5 f1_tbwlem5 a_wfal a_wi a_wi a_wfal a_wi f0_tbwlem5 a_wi a_ax-mp $.
$}

$(~ luk-1 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_re1luk1 $f wff ph $.
	f1_re1luk1 $f wff ps $.
	f2_re1luk1 $f wff ch $.
	p_re1luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= f0_re1luk1 f1_re1luk1 f2_re1luk1 p_tbw-ax1 $.
$}

$(~ luk-2 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph  $.
	f0_re1luk2 $f wff ph $.
	p_re1luk2 $p |- ( ( -. ph -> ph ) -> ph ) $= f0_re1luk2 p_tbw-negdf f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wfal a_wi f0_re1luk2 a_wn f0_re1luk2 a_wfal a_wi a_wi p_tbw-ax2 f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi f0_re1luk2 a_wn f0_re1luk2 a_wfal a_wi a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wfal a_wi a_wi p_tbwlem4 f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wfal a_wi f0_re1luk2 a_wn f0_re1luk2 a_wfal a_wi a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wfal a_wi a_wi a_wi f0_re1luk2 a_wn f0_re1luk2 a_wfal a_wi a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wfal a_wi a_wi a_wfal a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wi a_ax-mp f0_re1luk2 a_wn f0_re1luk2 a_wfal a_wi a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_wfal a_wi a_wi a_wfal a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi a_ax-mp f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn f0_re1luk2 p_tbw-ax1 f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wn a_wi f0_re1luk2 a_wn f0_re1luk2 a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wi a_wi a_ax-mp f0_re1luk2 a_wfal p_tbw-ax3 f0_re1luk2 a_wn f0_re1luk2 a_wi f0_re1luk2 a_wfal a_wi f0_re1luk2 a_wi f0_re1luk2 p_tbwsyl $.
$}

$(~ luk-3 derived from the Tarski-Bernays-Wajsberg axioms.

     This theorem, along with ~ re1luk1 and ~ re1luk2 proves that ~ tbw-ax1 ,
     ~ tbw-ax2 , ~ tbw-ax3 , and ~ tbw-ax4 , with ~ ax-mp can be used as a
     complete axiom system for all of propositional calculus.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_re1luk3 $f wff ph $.
	f1_re1luk3 $f wff ps $.
	p_re1luk3 $p |- ( ph -> ( -. ph -> ps ) ) $= f0_re1luk3 p_tbw-negdf f0_re1luk3 a_wn f0_re1luk3 a_wfal a_wi a_wi f0_re1luk3 a_wfal a_wi f0_re1luk3 a_wn a_wi p_tbwlem5 f0_re1luk3 a_wn f0_re1luk3 a_wfal a_wi a_wi f0_re1luk3 a_wfal a_wi f0_re1luk3 a_wn a_wi a_wfal a_wi a_wi a_wfal a_wi f0_re1luk3 a_wn f0_re1luk3 a_wfal a_wi a_wi a_ax-mp f1_re1luk3 p_tbw-ax4 f0_re1luk3 a_wfal f1_re1luk3 p_tbw-ax1 f0_re1luk3 a_wfal a_wi a_wfal f1_re1luk3 a_wi f0_re1luk3 f1_re1luk3 a_wi p_tbwlem1 f0_re1luk3 a_wfal a_wi a_wfal f1_re1luk3 a_wi f0_re1luk3 f1_re1luk3 a_wi a_wi a_wi a_wfal f1_re1luk3 a_wi f0_re1luk3 a_wfal a_wi f0_re1luk3 f1_re1luk3 a_wi a_wi a_wi a_ax-mp a_wfal f1_re1luk3 a_wi f0_re1luk3 a_wfal a_wi f0_re1luk3 f1_re1luk3 a_wi a_wi a_ax-mp f0_re1luk3 a_wfal a_wi f0_re1luk3 f1_re1luk3 p_tbwlem1 f0_re1luk3 a_wfal a_wi f0_re1luk3 f1_re1luk3 a_wi a_wi f0_re1luk3 f0_re1luk3 a_wfal a_wi f1_re1luk3 a_wi a_wi a_ax-mp f0_re1luk3 a_wn f0_re1luk3 a_wfal a_wi f1_re1luk3 p_tbw-ax1 f0_re1luk3 a_wn f0_re1luk3 a_wfal a_wi a_wi f0_re1luk3 f0_re1luk3 a_wfal a_wi f1_re1luk3 a_wi f0_re1luk3 a_wn f1_re1luk3 a_wi p_mpsyl $.
$}


