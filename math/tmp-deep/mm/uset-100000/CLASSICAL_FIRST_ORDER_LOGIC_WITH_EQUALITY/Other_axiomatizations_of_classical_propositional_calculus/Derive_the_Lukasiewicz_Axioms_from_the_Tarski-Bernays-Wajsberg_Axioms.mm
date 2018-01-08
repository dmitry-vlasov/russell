
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_Nicod_s_Axiom_from_Lukasiewicz_s_First_Sheffer_Stroke_Axiom.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz Axioms from the Tarski-Bernays-Wajsberg Axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Justification for ~ tbw-negdf .  (Contributed by Anthony Hart,
     15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-bijust $p |- ( ( ph <-> ps ) <-> ( ( ( ph -> ps )
    -> ( ( ps -> ph ) -> F. ) ) -> F. ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wps wi wps wph wi wfal wi wi
    wn wph wps wi wps wph wi wfal wi wi wfal wi wph wps dfbi1 wph wps wi wps
    wph wi wn wi wph wps wi wps wph wi wfal wi wi wph wps wi wps wph wi wn wi
    wph wps wi wps wph wi wfal wi wi wps wph wi wn wps wph wi wfal wi wph wps
    wi wps wph wi wfal pm2.21 imim2i wps wph wi wfal wi wps wph wi wn wph wps
    wi wps wph wi wfal wps wph wi wn wps wph wi wn id wps wph wi wn falim ja
    imim2i impbii notbii wph wps wi wps wph wi wfal wi wi wn wph wps wi wps wph
    wi wfal wi wi wfal wi wph wps wi wps wph wi wfal wi wi wfal pm2.21 wph wps
    wi wps wph wi wfal wi wi wfal wi wph wps wi wps wph wi wfal wi wi wn wph
    wps wi wps wph wi wfal wi wi wfal wph wps wi wps wph wi wfal wi wi wfal wi
    wph wps wi wps wph wi wfal wi wi wn wi wph wps wi wps wph wi wfal wi wi wn
    wph wps wi wps wph wi wfal wi wi wfal wi ax-1 wph wps wi wps wph wi wfal wi
    wi wfal wi wph wps wi wps wph wi wfal wi wi wn wi falim ja pm2.43i impbii
    3bitri $.

  $( The definition of negation, in terms of ` -> ` and ` F. ` .  (Contributed
     by Anthony Hart, 15-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-negdf $p |- ( ( ( -. ph -> ( ph -> F. ) )
    -> ( ( ( ph -> F. ) -> -. ph ) -> F. ) ) -> F. ) $=
    wph wn wph wfal wi wb wph wn wph wfal wi wi wph wfal wi wph wn wi wfal wi
    wi wfal wi wph wn wph wfal wi wph wfal pm2.21 wph wfal wi wph wn wph wfal
    wph wfal wi wph wn wi wph wn wph wfal wi ax-1 wph wfal wi wph wn wi falim
    ja pm2.43i impbii wph wn wph wfal wi tbw-bijust mpbi $.

  $( The first of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wph wps wch imim1 $.

  $( The second of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax2 $p |- ( ph -> ( ps -> ph ) ) $=
    wph wps ax-1 $.

  $( The third of four axioms in the Tarski-Bernays-Wajsberg system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbw-ax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    wph wps peirce $.

  $( The fourth of four axioms in the Tarski-Bernays-Wajsberg system.

     This axiom was added to the Tarski-Bernays axiom system ( see ~ tb-ax1 ,
     ~ tb-ax2 , and ~ tb-ax3 ) by Wajsberg for completeness.  (Contributed by
     Anthony Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  tbw-ax4 $p |- ( F. -> ph ) $=
    wph falim $.

  ${
    tbwsyl.1 $e |- ( ph -> ps ) $.
    tbwsyl.2 $e |- ( ps -> ch ) $.
    $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
       (Contributed by Anthony Hart, 16-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    tbwsyl $p |- ( ph -> ch ) $=
      wps wch wi wph wch wi tbwsyl.2 wph wps wi wps wch wi wph wch wi wi
      tbwsyl.1 wph wps wch tbw-ax1 ax-mp ax-mp $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem1 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wps wps wch wi wch wi wi wph wps wch wi wi wps wch wi wch wi wph wch wi wi
    wps wph wch wi wi wps wps wch wi wps wch wi wch wi wi wps wch wi wch wi wps
    wps wch wi wps wi wps wch wi wps wch wi wch wi wi wps wps wch wi tbw-ax2
    wps wch wi wps wch tbw-ax1 tbwsyl wps wch wi wps wch wi wch wi wi wps wch
    wi wch wi wch wi wps wch wi wch wi wi wps wch wi wch wi wps wch wi wps wch
    wi wch wi wch tbw-ax1 wps wch wi wch wi wch tbw-ax3 tbwsyl tbwsyl wph wps
    wch wi wch tbw-ax1 wps wps wch wi wch wi wph wch wi tbw-ax1 mpsyl $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem2 $p |- ( ( ph -> ( ps -> F. ) ) -> ( ( ( ph -> ch ) -> th )
    -> ( ps -> th ) ) ) $=
    wph wps wfal wi wi wps wph wch wi wi wph wch wi wth wi wps wth wi wi wps
    wps wfal wi wch wi wi wph wps wfal wi wi wps wfal wi wch wi wph wch wi wi
    wps wph wch wi wi wps wfal wi wps wch wi wi wps wps wfal wi wch wi wi wfal
    wch wi wps wfal wi wps wch wi wi wch tbw-ax4 wps wfal wi wfal wch wi wps
    wch wi wi wi wfal wch wi wps wfal wi wps wch wi wi wi wps wfal wch tbw-ax1
    wps wfal wi wfal wch wi wps wch wi tbwlem1 ax-mp ax-mp wps wfal wi wps wch
    tbwlem1 ax-mp wph wps wfal wi wch tbw-ax1 wps wps wfal wi wch wi wph wch wi
    tbw-ax1 mpsyl wps wph wch wi wth tbw-ax1 tbwsyl $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem3 $p |- ( ( ( ( ( ph -> F. ) -> ph ) -> ph ) -> ps ) -> ps ) $=
    wph wfal wi wph wi wph wi wps wi wph wfal wi wph wi wph wi wps wi wps wi wi
    wph wfal wi wph wi wph wi wps wi wps wi wph wfal wi wph wi wph wi wph wfal
    wi wph wi wph wi wps wi wph wfal wi wph wi wph wi wps wi wps wi wi wph wfal
    tbw-ax3 wph wfal wi wph wi wph wi wph wfal wi wph wi wph wi wps wi wph wfal
    wi wph wi wph wi wi wph wfal wi wph wi wph wi wps wi wph wfal wi wph wi wph
    wi wps wi wps wi wi wph wfal wi wph wi wph wi wph wfal wi wph wi wph wi wps
    wi tbw-ax2 wph wfal wi wph wi wph wi wps wi wph wfal wi wph wi wph wi wps
    tbw-ax1 tbwsyl ax-mp wph wfal wi wph wi wph wi wps wi wph wfal wi wph wi
    wph wi wps wi wps wi wi wph wfal wi wph wi wph wi wps wi wps wi wps wi wph
    wfal wi wph wi wph wi wps wi wps wi wi wph wfal wi wph wi wph wi wps wi wps
    wi wph wfal wi wph wi wph wi wps wi wph wfal wi wph wi wph wi wps wi wps wi
    wps tbw-ax1 wph wfal wi wph wi wph wi wps wi wps wi wps tbw-ax3 tbwsyl
    ax-mp $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem4 $p |- ( ( ( ph -> F. ) -> ps ) -> ( ( ps -> F. ) -> ph ) ) $=
    wph wfal wi wps wi wph wfal wi wps wfal wi wfal wi wi wps wfal wi wph wi
    wps wps wfal wi wfal wi wi wph wfal wi wps wi wph wfal wi wps wfal wi wfal
    wi wi wi wps wfal wi wps wfal wi wi wps wps wfal wi wfal wi wi wfal wfal wi
    wps wfal wi wps wfal wi wi wfal tbw-ax4 wps wfal wi wfal wfal wi wps wfal
    wi wi wi wfal wfal wi wps wfal wi wps wfal wi wi wi wps wfal wfal tbw-ax1
    wps wfal wi wfal wfal wi wps wfal wi tbwlem1 ax-mp ax-mp wps wfal wi wps
    wfal tbwlem1 ax-mp wph wfal wi wps wi wps wps wfal wi wfal wi wi wph wfal
    wi wps wfal wi wfal wi wi wi wi wps wps wfal wi wfal wi wi wph wfal wi wps
    wi wph wfal wi wps wfal wi wfal wi wi wi wi wph wfal wi wps wps wfal wi
    wfal wi tbw-ax1 wph wfal wi wps wi wps wps wfal wi wfal wi wi wph wfal wi
    wps wfal wi wfal wi wi tbwlem1 ax-mp ax-mp wph wfal wi wps wfal wi wfal wi
    wi wph wfal wi wph wi wph wi wps wfal wi wph wi wi wps wfal wi wph wi wph
    wfal wi wps wfal wi wph wph tbwlem2 wph wps wfal wi wph wi tbwlem3 tbwsyl
    tbwsyl $.

  $( Used to rederive the Lukasiewicz axioms from Tarski-Bernays-Wajsberg'.
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  tbwlem5 $p |- ( ( ( ph -> ( ps -> F. ) ) -> F. ) -> ph ) $=
    wph wfal wi wph wps wfal wi wi wi wph wps wfal wi wi wfal wi wph wi wph wph
    wfal wi wps wfal wi wi wi wph wfal wi wph wps wfal wi wi wi wph wps wph wi
    wph wfal wi wps wfal wi wi wph wps tbw-ax2 wps wph wfal tbw-ax1 tbwsyl wph
    wph wfal wi wps wfal wi tbwlem1 ax-mp wph wph wps wfal wi wi tbwlem4 ax-mp
    $.

  $( ~ luk-1 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wph wps wch tbw-ax1 $.

  $( ~ luk-2 derived from the Tarski-Bernays-Wajsberg axioms.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wph wfal wi wph wi wph wph wfal wi wph wn wi wph wn wph wi
    wph wfal wi wph wi wi wph wn wph wfal wi wi wph wfal wi wph wn wi wfal wi
    wi wfal wi wph wfal wi wph wn wi wph tbw-negdf wph wfal wi wph wn wi wfal
    wi wph wn wph wfal wi wi wph wfal wi wph wn wi wfal wi wi wi wph wn wph
    wfal wi wi wph wfal wi wph wn wi wfal wi wi wfal wi wph wfal wi wph wn wi
    wi wph wfal wi wph wn wi wfal wi wph wn wph wfal wi wi tbw-ax2 wph wfal wi
    wph wn wi wph wn wph wfal wi wi wph wfal wi wph wn wi wfal wi wi tbwlem4
    ax-mp ax-mp wph wfal wi wph wn wph tbw-ax1 ax-mp wph wfal tbw-ax3 tbwsyl $.

  $( ~ luk-3 derived from the Tarski-Bernays-Wajsberg axioms.

     This theorem, along with ~ re1luk1 and ~ re1luk2 proves that ~ tbw-ax1 ,
     ~ tbw-ax2 , ~ tbw-ax3 , and ~ tbw-ax4 , with ~ ax-mp can be used as a
     complete axiom system for all of propositional calculus.  (Contributed by
     Anthony Hart, 16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wn wph wfal wi wi wph wph wfal wi wps wi wph wn wps wi wph wn wph wfal
    wi wi wph wfal wi wph wn wi wfal wi wi wfal wi wph wn wph wfal wi wi wph
    tbw-negdf wph wn wph wfal wi wi wph wfal wi wph wn wi tbwlem5 ax-mp wph
    wfal wi wph wps wi wi wph wph wfal wi wps wi wi wfal wps wi wph wfal wi wph
    wps wi wi wps tbw-ax4 wph wfal wi wfal wps wi wph wps wi wi wi wfal wps wi
    wph wfal wi wph wps wi wi wi wph wfal wps tbw-ax1 wph wfal wi wfal wps wi
    wph wps wi tbwlem1 ax-mp ax-mp wph wfal wi wph wps tbwlem1 ax-mp wph wn wph
    wfal wi wps tbw-ax1 mpsyl $.


