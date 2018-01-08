
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Tarski-Bernays-Wajsberg_axioms_from_Meredith_s_Second_CO_Axiom.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Derive the Lukasiewicz axioms from the The Russell-Bernays Axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Justification for ~ rb-imdf .  (Contributed by Anthony Hart,
     17-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  rb-bijust $p |- ( ( ph <-> ps ) <-> -. ( -. ( -. ph \/ ps )
    \/ -. ( -. ps \/ ph ) ) ) $=
    wph wps wb wph wps wi wps wph wi wn wi wn wph wn wps wo wps wn wph wo wn wi
    wn wph wn wps wo wn wps wn wph wo wn wo wn wph wps dfbi1 wph wps wi wps wph
    wi wn wi wph wn wps wo wps wn wph wo wn wi wph wps wi wph wn wps wo wps wph
    wi wn wps wn wph wo wn wph wps imor wps wph wi wps wn wph wo wps wph imor
    notbii imbi12i notbii wph wn wps wo wps wn wph wo wn wi wph wn wps wo wn
    wps wn wph wo wn wo wph wn wps wo wps wn wph wo pm4.62 notbii 3bitri $.

  $( The definition of implication, in terms of ` \/ ` and ` -. ` .
     (Contributed by Anthony Hart, 17-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-imdf $p |- -. ( -. ( -. ( ph -> ps ) \/ ( -. ph \/ ps ) )
    \/ -. ( -. ( -. ph \/ ps ) \/ ( ph -> ps ) ) ) $=
    wph wps wi wph wn wps wo wb wph wps wi wn wph wn wps wo wo wn wph wn wps wo
    wn wph wps wi wo wn wo wn wph wps imor wph wps wi wph wn wps wo rb-bijust
    mpbi $.

  ${
    anmp.min $e |- ph $.
    anmp.maj $e |- ( -. ph \/ ps ) $.
    $( Modus ponens for ` \/ ` ` -. ` axiom systems.  (Contributed by Anthony
       Hart, 12-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    anmp $p |- ps $=
      wph wps anmp.min wph wps anmp.maj imorri ax-mp $.
  $}

  $( The first of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax1 $p |- ( -. ( -. ps \/ ch ) \/ ( -. ( ph \/ ps ) \/ ( ph \/ ch ) ) ) $=
    wps wn wch wo wph wps wo wn wph wch wo wo wps wch wi wph wps wo wph wch wo
    wi wps wn wch wo wph wps wo wn wph wch wo wo wph wps wch orim2 wps wch imor
    wph wps wo wph wch wo imor 3imtr3i imori $.

  $( The second of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax2 $p |- ( -. ( ph \/ ps ) \/ ( ps \/ ph ) ) $=
    wph wps wo wn wps wph wo wps wph wo wph wps wo wn wph wps wo wps wph wo wph
    wps pm1.4 con3i con1i orri $.

  $( The third of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax3 $p |- ( -. ph \/ ( ps \/ ph ) ) $=
    wph wn wps wph wo wps wph wo wph wn wps wph pm2.46 con1i orri $.

  $( The fourth of four axioms in the Russell-Bernays axiom system.
     (Contributed by Anthony Hart, 13-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rb-ax4 $p |- ( -. ( ph \/ ph ) \/ ph ) $=
    wph wph wo wn wph wph wph wph wo wn wph wph wo wph wph pm1.2 con3i con1i
    orri $.

  ${
    rbsyl.1 $e |- ( -. ps \/ ch ) $.
    rbsyl.2 $e |- ( ph \/ ps ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rbsyl $p |- ( ph \/ ch ) $=
      wph wps wo wph wch wo rbsyl.2 wps wn wch wo wph wps wo wn wph wch wo wo
      rbsyl.1 wph wps wch rb-ax1 anmp anmp $.
  $}

  ${
    rblem1.1 $e |- ( -. ph \/ ps ) $.
    rblem1.2 $e |- ( -. ch \/ th ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem1 $p |- ( -. ( ph \/ ch ) \/ ( ps \/ th ) ) $=
      wph wch wo wn wps wch wo wps wth wo wch wn wth wo wps wch wo wn wps wth
      wo wo rblem1.2 wps wch wth rb-ax1 anmp wph wch wo wn wch wps wo wps wch
      wo wch wps rb-ax2 wph wch wo wn wch wph wo wch wps wo wph wn wps wo wch
      wph wo wn wch wps wo wo rblem1.1 wch wph wps rb-ax1 anmp wph wch rb-ax2
      rbsyl rbsyl rbsyl $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem2 $p |- ( -. ( ch \/ ph ) \/ ( ch \/ ( ph \/ ps ) ) ) $=
    wph wn wph wps wo wo wch wph wo wn wch wph wps wo wo wo wph wn wps wph wo
    wph wps wo wps wph rb-ax2 wph wps rb-ax3 rbsyl wch wph wph wps wo rb-ax1
    anmp $.

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 18-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem3 $p |- ( -. ( ch \/ ph ) \/ ( ( ch \/ ps ) \/ ph ) ) $=
    wch wph wo wn wph wch wps wo wo wch wps wo wph wo wph wch wps wo rb-ax2 wch
    wph wo wn wph wch wo wph wch wps wo wo wch wps wph rblem2 wch wph rb-ax2
    rbsyl rbsyl $.

  ${
    rblem4.1 $e |- ( -. ph \/ th ) $.
    rblem4.2 $e |- ( -. ps \/ ta ) $.
    rblem4.3 $e |- ( -. ch \/ et ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 18-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem4 $p |- ( -. ( ( ph \/ ps ) \/ ch ) \/ ( ( et \/ ta ) \/ th ) ) $=
      wph wps wo wch wo wn wch wps wo wph wo wet wta wo wth wo wch wps wo wet
      wta wo wph wth wch wet wps wta rblem4.3 rblem4.2 rblem1 rblem4.1 rblem1
      wph wps wo wch wo wn wps wch wo wph wo wch wps wo wph wo wps wch wo wph
      wo wn wph wch wps wo wo wch wps wo wph wo wph wch wps wo rb-ax2 wps wch
      wo wph wo wn wph wps wch wo wo wph wch wps wo wo wps wch wo wn wch wps wo
      wo wph wps wch wo wo wn wph wch wps wo wo wo wps wch rb-ax2 wph wps wch
      wo wch wps wo rb-ax1 anmp wps wch wo wph rb-ax2 rbsyl rbsyl wph wps wo
      wch wo wn wps wch wo wph wo wps wch wo wph wo wo wps wch wo wph wo wps
      wch wo wph wo rb-ax4 wph wps wo wps wch wo wph wo wch wps wch wo wph wo
      wph wps wo wn wph wps wch wo wo wps wch wo wph wo wph wps wch wo rb-ax2
      wps wch wph rblem2 rbsyl wch wn wps wch wo wo wch wn wps wch wo wph wo wo
      wch wps rb-ax3 wps wch wo wph wch wn rblem2 anmp rblem1 rbsyl rbsyl rbsyl
      $.
  $}

  $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
     (Contributed by Anthony Hart, 19-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  rblem5 $p |- ( -. ( -. -. ph \/ ps ) \/ ( -. -. ps \/ ph ) ) $=
    wph wn wn wps wo wn wph wps wn wn wo wps wn wn wph wo wph wps wn wn rb-ax2
    wph wn wn wph wps wps wn wn wph wn wph wo wph wn wn wn wph wo wph wn wph
    wph wo wph wph rb-ax4 wph wph rb-ax3 rbsyl wph wn wph wn wn wn wph wph wph
    wn wn wn wph wn wn wo wph wn wn wph wn wn wn wo wph wn wn wn wph wn wn wph
    wn wn wo wph wn wn wph wn wn rb-ax4 wph wn wn wph wn wn rb-ax3 rbsyl wph wn
    wn wn wph wn wn rb-ax2 anmp wph wn wph wph wo wph wph rb-ax4 wph wph rb-ax3
    rbsyl rblem1 anmp wps wn wn wps wn wo wps wn wps wn wn wo wps wn wn wps wn
    wps wn wo wps wn wps wn rb-ax4 wps wn wps wn rb-ax3 rbsyl wps wn wn wps wn
    rb-ax2 anmp rblem1 rbsyl $.

  ${
    rblem6.1 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem6 $p |- ( -. ph \/ ps ) $=
      wph wn wps wo wn wps wn wph wo wn wo wn wph wn wps wo rblem6.1 wph wn wps
      wo wn wn wph wn wps wo wn wps wn wph wo wn wo wo wph wn wps wo wn wps wn
      wph wo wn wo wn wn wph wn wps wo wo wph wn wps wo wn wps wn wph wo wn wo
      wph wn wps wo wn wn wo wph wn wps wo wn wn wph wn wps wo wn wps wn wph wo
      wn wo wo wph wn wps wo wn wph wn wps wo wn wn wo wph wn wps wo wn wps wn
      wph wo wn wo wph wn wps wo wn wn wo wph wn wps wo wn wn wph wn wps wo wn
      wo wph wn wps wo wn wph wn wps wo wn wn wo wph wn wps wo wn wn wph wn wps
      wo wn wph wn wps wo wn wo wph wn wps wo wn wph wn wps wo wn rb-ax4 wph wn
      wps wo wn wph wn wps wo wn rb-ax3 rbsyl wph wn wps wo wn wn wph wn wps wo
      wn rb-ax2 anmp wph wn wps wo wn wn wps wn wph wo wn wph wn wps wo wn
      rblem3 anmp wph wn wps wo wn wps wn wph wo wn wo wph wn wps wo wn wn
      rb-ax2 anmp wph wn wps wo wph wn wps wo wn wps wn wph wo wn wo rblem5
      anmp anmp $.
  $}

  ${
    rblem7.1 $e |- -. ( -. ( -. ph \/ ps ) \/ -. ( -. ps \/ ph ) ) $.
    $( Used to rederive the Lukasiewicz axioms from Russell-Bernays'.
       (Contributed by Anthony Hart, 19-Aug-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    rblem7 $p |- ( -. ps \/ ph ) $=
      wph wn wps wo wn wps wn wph wo wn wo wn wps wn wph wo rblem7.1 wps wn wph
      wo wn wn wph wn wps wo wn wps wn wph wo wn wo wo wph wn wps wo wn wps wn
      wph wo wn wo wn wn wps wn wph wo wo wps wn wph wo wn wph wn wps wo wn
      rb-ax3 wps wn wph wo wph wn wps wo wn wps wn wph wo wn wo rblem5 anmp
      anmp $.
  $}

  ${
    re1axmp.min $e |- ph $.
    re1axmp.maj $e |- ( ph -> ps ) $.
    $( ~ ax-mp derived from Russell-Bernays'.  (Contributed by Anthony Hart,
       19-Aug-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    re1axmp $p |- ps $=
      wph wps re1axmp.min wph wps wi wph wn wps wo re1axmp.maj wph wps wi wph
      wn wps wo wph wps rb-imdf rblem6 anmp anmp $.
  $}

  $( ~ luk-1 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wph wps wi wn wps wch wi wph wch wi wi wo wph wps wi wps wch wi wph wch wi
    wi wi wph wps wi wn wps wch wi wn wph wch wi wo wps wch wi wph wch wi wi
    wps wch wi wph wch wi wi wps wch wi wn wph wch wi wo wps wch wi wph wch wi
    rb-imdf rblem7 wph wps wi wn wph wn wps wo wps wch wi wn wph wch wi wo wph
    wn wps wo wn wps wn wch wo wn wph wn wch wo wo wps wch wi wn wph wch wi wo
    wps wn wch wo wn wps wch wi wn wph wn wch wo wph wch wi wps wch wi wn wps
    wn wch wo wo wps wn wch wo wn wn wps wch wi wn wo wps wch wi wps wn wch wo
    wps wch rb-imdf rblem6 wps wch wi wn wps wn wch wo wo wn wps wch wi wn wps
    wn wch wo wn wn wo wps wn wch wo wn wn wps wch wi wn wo wps wch wi wn wps
    wn wch wo wn wn rb-ax2 wps wch wi wn wps wch wi wn wps wn wch wo wps wn wch
    wo wn wn wps wch wi wn wn wps wch wi wn wps wch wi wn wo wps wch wi wn wps
    wch wi wn rb-ax4 wps wch wi wn wps wch wi wn rb-ax3 rbsyl wps wn wch wo wn
    wn wps wn wch wo wn wo wps wn wch wo wn wps wn wch wo wn wn wo wps wn wch
    wo wn wn wps wn wch wo wn wps wn wch wo wn wo wps wn wch wo wn wps wn wch
    wo wn rb-ax4 wps wn wch wo wn wps wn wch wo wn rb-ax3 rbsyl wps wn wch wo
    wn wn wps wn wch wo wn rb-ax2 anmp rblem1 rbsyl anmp wph wch wi wph wn wch
    wo wph wch rb-imdf rblem7 rblem1 wps wn wch wo wn wph wn wps wo wn wph wn
    wch wo wo wo wph wn wps wo wn wps wn wch wo wn wph wn wch wo wo wo wph wn
    wps wch rb-ax1 wps wn wch wo wn wph wn wps wo wn wph wn wch wo wo wo wn wps
    wn wch wo wn wph wn wch wo wo wph wn wps wo wn wo wph wn wps wo wn wps wn
    wch wo wn wph wn wch wo wo wo wps wn wch wo wn wph wn wch wo wo wph wn wps
    wo wn rb-ax2 wps wn wch wo wn wph wn wps wo wn wph wn wch wo wo wo wn wph
    wn wps wo wn wph wn wch wo wo wps wn wch wo wn wo wps wn wch wo wn wph wn
    wch wo wo wph wn wps wo wn wo wph wn wps wo wn wph wn wch wo wps wn wch wo
    wn wph wn wps wo wn wph wn wch wo wps wn wch wo wn wph wn wps wo wn wn wph
    wn wps wo wn wph wn wps wo wn wo wph wn wps wo wn wph wn wps wo wn rb-ax4
    wph wn wps wo wn wph wn wps wo wn rb-ax3 rbsyl wph wn wch wo wn wph wn wch
    wo wph wn wch wo wo wph wn wch wo wph wn wch wo rb-ax4 wph wn wch wo wph wn
    wch wo rb-ax3 rbsyl wps wn wch wo wn wn wps wn wch wo wn wps wn wch wo wn
    wo wps wn wch wo wn wps wn wch wo wn rb-ax4 wps wn wch wo wn wps wn wch wo
    wn rb-ax3 rbsyl rblem4 wps wn wch wo wn wph wn wps wo wn wph wn wch wo wo
    rb-ax2 rbsyl rbsyl anmp rbsyl wph wps wi wph wn wps wo wph wps rb-imdf
    rblem6 rbsyl rbsyl wph wps wi wps wch wi wph wch wi wi wi wph wps wi wn wps
    wch wi wph wch wi wi wo wph wps wi wps wch wi wph wch wi wi rb-imdf rblem7
    anmp $.

  $( ~ luk-2 derived from Russell-Bernays'.  (Contributed by Anthony Hart,
     19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wn wph wo wph wn wph wi wph wi wph wn wph wi wn wph wn wn wph
    wo wph wph wn wn wph wo wn wph wph wo wph wph rb-ax4 wph wn wn wph wph wph
    wph wn wph wo wph wn wn wn wph wo wph wn wph wph wo wph wph rb-ax4 wph wph
    rb-ax3 rbsyl wph wn wph wn wn wn wph wph wph wn wn wn wph wn wn wo wph wn
    wn wph wn wn wn wo wph wn wn wn wph wn wn wph wn wn wo wph wn wn wph wn wn
    rb-ax4 wph wn wn wph wn wn rb-ax3 rbsyl wph wn wn wn wph wn wn rb-ax2 anmp
    wph wn wph wph wo wph wph rb-ax4 wph wph rb-ax3 rbsyl rblem1 anmp wph wn
    wph wph wo wph wph rb-ax4 wph wph rb-ax3 rbsyl rblem1 rbsyl wph wn wph wi
    wph wn wn wph wo wph wn wph rb-imdf rblem6 rbsyl wph wn wph wi wph wi wph
    wn wph wi wn wph wo wph wn wph wi wph rb-imdf rblem7 anmp $.

  $( ~ luk-3 derived from Russell-Bernays'.

     This theorem, along with ~ re1axmp , ~ re2luk1 , and ~ re2luk2 shows that
     ~ rb-ax1 , ~ rb-ax2 , ~ rb-ax3 , and ~ rb-ax4 , along with ~ anmp , can be
     used as a complete axiomatization of propositional calculus.  (Contributed
     by Anthony Hart, 19-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re2luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wn wph wn wps wi wo wph wph wn wps wi wi wph wn wph wn wn wps wo wph wn
    wps wi wph wn wps wi wph wn wn wps wo wph wn wps rb-imdf rblem7 wph wn wph
    wn wn wo wph wn wph wn wn wps wo wo wph wn wn wph wn wo wph wn wph wn wn wo
    wph wn wn wph wn wph wn wo wph wn wph wn rb-ax4 wph wn wph wn rb-ax3 rbsyl
    wph wn wn wph wn rb-ax2 anmp wph wn wn wps wph wn rblem2 anmp rbsyl wph wph
    wn wps wi wi wph wn wph wn wps wi wo wph wph wn wps wi rb-imdf rblem7 anmp
    $.


