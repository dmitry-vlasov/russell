
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Tarski-Bernays-Wajsberg_axioms_from_Meredith_s_First_CO_Axiom.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's Second CO Axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus offered by Meredith.

     This axiom has 19 symbols, sans auxiliaries.  See notes in ~ merco1 .
     (Contributed by Anthony Hart, 7-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco2 $p |- ( ( ( ph -> ps ) -> ( ( F. -> ch ) -> th ) ) -> ( ( th
         -> ph ) -> ( ta -> ( et -> ph ) ) ) ) $=
    wet wph wps wi wfal wch wi wth wi wi wth wph wi wta wph wph wps wi wfal wch
    wi wth wi wi wth wph wi wta wph wi wi wi wet wph wps wi wfal wch wi wth wi
    wi wth wph wi wph wta wph wps wi wfal wch wi wth wi wi wph wps wi wth wi
    wph wth wi wth wi wth wph wi wph wi wph wps wi wfal wch wi wth wi wi wfal
    wch wi wph wps wi wth wi wch falim wph wps wi wfal wch wi wth pm2.04 mpi
    wph wps wi wth wi wph wth wth wph wps wth jarl wph wps wi wth wi wth idd
    jad wph wth looinv 3syl a1dd a1i com4l $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem1 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ( th -> ch ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps
    wi wch wi wps wth wch wi wi wi wph wph wph wph wph wph merco2 wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wi wch wi wps
    wth wch wi wi wi wi wph wph wph wph wph wph merco2 wch wph wi wfal wph wi
    wph wps wi wi wi wph wps wi wch wi wps wth wch wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wi wch wi wps wth wch
    wi wi wi wi wi wch wph wph wph wps wi wps wth merco2 wph wps wi wch wi wps
    wth wch wi wi wi wfal wph wi wph wps wi wi wi wfal wph wi wch wph wi wfal
    wph wi wph wps wi wi wi wi wi wch wph wi wfal wph wi wph wps wi wi wi wph
    wps wi wch wi wps wth wch wi wi wi wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wps wi wch wi wps wth wch wi wi wi wi wi wi
    wfal wph wi wph wps wi wi wps wth wch wi wi wi wfal wph wi wph wps wi wch
    wi wps wth wch wi wi wi wi wi wph wps wi wch wi wps wth wch wi wi wi wfal
    wph wi wph wps wi wi wi wfal wph wi wch wph wi wfal wph wi wph wps wi wi wi
    wi wi wps wth wch wi wi wfal wph wi wfal wi wi wfal wps wi wfal wph wi wph
    wps wi wi wi wi wfal wph wi wph wps wi wi wps wth wch wi wi wi wfal wph wi
    wph wps wi wch wi wps wth wch wi wi wi wi wi wps wth wch wi wph wfal wfal
    wph wi wph merco2 wps wth wch wi wi wfal wph wi wfal wi wps wfal wph wi wph
    wps wi wi wfal wph wi wph wps wi wch wi merco2 ax-mp wfal wph wi wph wps wi
    wi wps wth wch wi wi wph wph wps wi wch wi wps wth wch wi wi wi wfal wph wi
    wch wph wi merco2 ax-mp wph wps wi wch wi wps wth wch wi wi wi wfal wph wi
    wph wps wi wi wph wch wph wi wfal wph wi wph wps wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi merco2 ax-mp ax-mp ax-mp ax-mp
    $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem2 $p |- ( ( ( ph -> ps ) -> ph ) -> ( ch -> ( th -> ph ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps
    wi wph wi wch wth wph wi wi wi wph wph wph wph wph wph merco2 wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wi wph wi wch
    wth wph wi wi wi wi wph wph wph wph wph wph merco2 wph wph wi wfal wph wi
    wph wps wi wi wi wph wps wi wph wi wch wth wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wi wph wi wch wth wph
    wi wi wi wi wi wph wph wph wph wps wi wch wth merco2 wph wps wi wph wi wch
    wth wph wi wi wi wfal wph wi wph wps wi wi wi wfal wph wi wph wph wi wfal
    wph wi wph wps wi wi wi wi wi wph wph wi wfal wph wi wph wps wi wi wi wph
    wps wi wph wi wch wth wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wps wi wph wi wch wth wph wi wi wi wi wi wi
    wfal wph wi wph wps wi wi wch wth wph wi wi wi wfal wph wi wph wps wi wph
    wi wch wth wph wi wi wi wi wi wph wps wi wph wi wch wth wph wi wi wi wfal
    wph wi wph wps wi wi wi wfal wph wi wph wph wi wfal wph wi wph wps wi wi wi
    wi wi wch wth wph wi wi wph wps wi wi wfal wph wi wfal wph wi wph wps wi wi
    wi wi wfal wph wi wph wps wi wi wch wth wph wi wi wi wfal wph wi wph wps wi
    wph wi wch wth wph wi wi wi wi wi wph wps wi wfal wph wi wfal wi wi wfal
    wph wi wch wth wph wi wi wi wi wch wth wph wi wi wph wps wi wi wfal wph wi
    wfal wph wi wph wps wi wi wi wi wph wps wph wfal wch wth merco2 wph wps wi
    wfal wph wi wfal wi wph wch wth wph wi wi wfal wph wi wfal wph wi merco2
    ax-mp wch wth wph wi wi wph wps wi wph wfal wph wi wph wps wi wi wfal wph
    wi wph wps wi wph wi merco2 ax-mp wfal wph wi wph wps wi wi wch wth wph wi
    wi wph wph wps wi wph wi wch wth wph wi wi wi wfal wph wi wph wph wi merco2
    ax-mp wph wps wi wph wi wch wth wph wi wi wi wfal wph wi wph wps wi wi wph
    wph wph wi wfal wph wi wph wps wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi merco2 ax-mp ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem3 $p |- ( ( ps -> ch ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wps wch
    wi wps wph wch wi wi wi wph wph wph wph wph wph merco2 wph wph wi wfal wph
    wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph
    wi wi wph wph wi wph wph wph wi wi wi wi wps wch wi wps wph wch wi wi wi wi
    wph wph wph wph wph wph merco2 wch wph wi wfal wph wi wps wi wi wps wch wi
    wps wph wch wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi
    wi wi wi wps wch wi wps wph wch wi wi wi wi wi wch wph wph wps wps wph
    merco2 wps wch wi wps wph wch wi wi wi wfal wph wi wps wi wi wfal wph wi
    wch wph wi wfal wph wi wps wi wi wi wi wch wph wi wfal wph wi wps wi wi wps
    wch wi wps wph wch wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wps wch wi wps wph wch wi wi wi wi wi wi wfal wph wi wps wi
    wps wph wch wi wi wi wfal wph wi wps wch wi wps wph wch wi wi wi wi wi wps
    wch wi wps wph wch wi wi wi wfal wph wi wps wi wi wfal wph wi wch wph wi
    wfal wph wi wps wi wi wi wi wps wph wch wi wi wps wi wfal wph wi wfal wph
    wi wps wi wi wi wfal wph wi wps wi wps wph wch wi wi wi wfal wph wi wps wch
    wi wps wph wch wi wi wi wi wi wps wph wch wi wfal wph wi wfal wph wi
    mercolem2 wps wph wch wi wi wps wph wfal wph wi wps wi wfal wph wi wps wch
    wi merco2 ax-mp wfal wph wi wps wi wps wph wch wi wi wph wps wch wi wps wph
    wch wi wi wi wfal wph wi wch wph wi merco2 ax-mp wps wch wi wps wph wch wi
    wi wi wfal wph wi wps wi wph wch wph wi wfal wph wi wps wi wi wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi merco2 ax-mp ax-mp
    ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem4 $p |- ( ( th -> ( et -> ph ) ) -> ( ( ( th -> ch )
  -> ph ) -> ( ta -> ( et -> ph ) ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wth wet
    wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wph wph wph wph wph wph
    merco2 wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wth wet
    wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wi wph wph wph wph wph
    wph merco2 wet wph wi wph wi wfal wph wi wth wi wi wth wet wph wi wi wth
    wch wi wph wi wta wet wph wi wi wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wth wet wph wi wi wth wch wi wph wi wta wet wph
    wi wi wi wi wi wi wet wph wi wph wph wth wth wch wi wph wi wta merco2 wth
    wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wth wi wfal wph wi
    wet wph wi wph wi wfal wph wi wth wi wi wi wi wet wph wi wph wi wfal wph wi
    wth wi wi wth wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wi
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph
    wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wth wet wph wi
    wi wth wch wi wph wi wta wet wph wi wi wi wi wi wi wi wth wet wph wi wi wth
    wch wi wph wi wta wet wph wi wi wi wi wth wi wet wph wi wph wi wfal wph wi
    wth wi wi wi wth wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi
    wth wi wfal wph wi wet wph wi wph wi wfal wph wi wth wi wi wi wi wth wch wi
    wfal wph wi wth wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wi
    wi wth wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wth wi wet
    wph wi wph wi wfal wph wi wth wi wi wi wfal wph wi wth wch wi wi wth wet
    wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wi wth wch wi wfal wph
    wi wth wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wi wi wph
    wph wi wfal wph wi wth wch wi wi wi wth wch wi wph wi wta wet wph wi wi wi
    wi wfal wph wi wth wch wi wi wth wet wph wi wi wth wch wi wph wi wta wet
    wph wi wi wi wi wi wph wph wph wth wch wi wta wet merco2 wph wph wi wfal
    wph wi wth wch wi wi wth wch wi wph wi wta wet wph wi wi wi wth wet wph wi
    wi mercolem1 ax-mp wfal wph wi wth wch wi wth wet wph wi wi wth wch wi wph
    wi wta wet wph wi wi wi wi wfal wph wi mercolem1 ax-mp wth wch wph wth wet
    wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wet wph wi wph wi wfal
    wph wi merco2 ax-mp wfal wph wi wth wet wph wi wi wth wch wi wph wi wta wet
    wph wi wi wi wi wth wi wet wph wi wph wi wfal wph wi wth wi wi mercolem3
    ax-mp wth wet wph wi wi wth wch wi wph wi wta wet wph wi wi wi wi wth wph
    wet wph wi wph wi wfal wph wi wth wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi merco2 ax-mp ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem5 $p |- ( th -> ( ( th -> ph ) -> ( ta -> ( ch -> ph ) ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wth wth
    wph wi wta wch wph wi wi wi wi wph wph wph wph wph wph merco2 wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wth wth wph wi wta wch
    wph wi wi wi wi wi wph wph wph wph wph wph merco2 wfal wph wi wth wi wth
    wth wph wi wta wch wph wi wi wi wi wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wth wth wph wi wta wch wph wi wi wi wi wi wi wph
    wph wi wfal wph wi wth wi wi wth wph wi wta wch wph wi wi wi wi wfal wph wi
    wth wi wth wth wph wi wta wch wph wi wi wi wi wi wph wph wph wth wta wch
    merco2 wph wph wi wfal wph wi wth wi wth wph wi wta wch wph wi wi wi wth
    mercolem1 ax-mp wth wth wph wi wta wch wph wi wi wi wi wth wi wfal wph wi
    wfal wph wi wth wi wi wi wfal wph wi wth wi wth wth wph wi wta wch wph wi
    wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi
    wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wth wth wph wi wta wch wph wi wi wi wi wi wi wi wth wth wph wi wta wch wph
    wi wi wi wfal wph wi wfal wph wi mercolem2 wth wth wph wi wta wch wph wi wi
    wi wi wth wph wfal wph wi wth wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi merco2 ax-mp ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem6 $p |- ( ( ph -> ( ps -> ( ph -> ch ) ) )
  -> ( ps -> ( ph -> ch ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps
    wph wch wi wi wi wps wph wch wi wi wi wph wph wph wph wph wph merco2 wph
    wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi
    wi wi wps wph wch wi wi wi wi wph wph wph wph wph wph merco2 wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps
    wph wch wi wi wi wi wi wph wph wph wph wph wph merco2 wph wps wph wch wi wi
    wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph
    wps wph wch wi wi wi wps wph wch wi wi wi wi wi wph wph wi wfal wph wi wph
    wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi
    wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wph wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wph
    wph wph wph wph wph merco2 wph wch wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi
    wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi
    wi wph wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wi
    wph wph wps wph wch wi wi wi wi wph wch wi wi wph wps wph wch wi wi wi wps
    wph wch wi wi wi wi wph wch wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi
    wph wph wps wph wch wi wi wi wph wch wi wps mercolem1 wph wph wps wph wch
    wi wi wi wi wph wch wi wph wps wph wch wi wi wi wps wph wch wi wi wi wph
    wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi mercolem1
    ax-mp wph wph wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi
    wi wi wph wch wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi
    wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi
    wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wi wi wps wph wch wi wi
    wph wps wph wch wi wi wi wph wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi mercolem5 wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi
    wch wph wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wph wps wph wch wi wi wi mercolem4 ax-mp ax-mp ax-mp wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wph
    wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph
    wch wi wi wi wps wph wch wi wi wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wi
    wi wph wph wph wph wph wph merco2 wph wps wph wch wi wi wi wps wph wch wi
    wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph
    wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch
    wi wi wi wps wph wch wi wi wi wi wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi
    wi wps wph wch wi wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi
    wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wi wi wi wph
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wi wph
    wps wph wch wi wi wi wps wph wch wi wi wi wi wph wph wi wfal wph wi wph wi
    wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi
    wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi
    wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch
    wi wi wi wi wi wi wi wph wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wph wph
    wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi mercolem1 wph
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wi wph
    wps wph wch wi wi wi wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi
    wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    mercolem1 ax-mp wph wps wph wch wi wi wi wph wps wph wch wi wi wi wph wph
    wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch
    wi wi wi wps wph wch wi wi wi wi wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wi wi
    wi wph wps wph wch wi wi wi wps wph wch wi wi wi wph wph wi wfal wph wi wph
    wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph
    wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi
    wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi
    wi wph wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wph
    wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi
    wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal
    wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi
    wi wps wph wch wi wi wi wi wi wi wi wi wi wph wph wi wfal wph wi wph wi wi
    wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph wch wi
    wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi
    wi wph wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph
    wph wph wi wi wi wi mercolem5 wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi
    wi wi wi wph wps wph wch wi wi wi wps wph wch wi wi wi wi wi wi wps wph wch
    wi wi wph wps wph wch wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi wph wps wph wch wi wi wi wph wph wi wfal wph wi wph
    wi wi wph wph wi wph wph wph wi wi wi wi wph wps wph wch wi wi wi wps wph
    wch wi wi wi wi wi mercolem4 ax-mp ax-mp ax-mp ax-mp ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem7 $p |- ( ( ph -> ps ) -> ( ( ( ph -> ch )
  -> ( th -> ps ) ) -> ( th -> ps ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps
    wi wph wch wi wth wps wi wi wth wps wi wi wi wph wph wph wph wph wph merco2
    wph wch wi wph wch wi wth wps wi wi wth wps wi wi wi wph wph wi wfal wph wi
    wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps wi wph wch wi wth wps
    wi wi wth wps wi wi wi wi wph wch wi wth wps wi wi wph wch wi wph wch wi
    wth wps wi wi wth wps wi wi wi wi wph wch wi wph wch wi wth wps wi wi wth
    wps wi wi wi wph wch wi wth wps wi wi wph wch wi wth wps wi mercolem3 wph
    wch wi wth wps wi wi wph wch wi wth wps wi mercolem6 ax-mp wph wph wps wi
    wph wch wi wth wps wi wi wth wps wi wi wi wi wph wch wi wph wch wi wth wps
    wi wi wth wps wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wph wps wi wph wch wi wth wps wi wi wth wps wi wi wi wi wi
    wps wth wph wph wch wi wth wps wi wi mercolem5 wph wch wi wth wps wi wi wth
    wps wi wi wch wph wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph
    wi wi wi wi wph wps wi mercolem4 ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco2 .
     (Contributed by Anthony Hart, 16-Aug-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  mercolem8 $p |- ( ( ph -> ps ) -> ( ( ps -> ( ph -> ch ) )
  -> ( ta -> ( th -> ( ph -> ch ) ) ) ) ) $=
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps
    wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wph wph wph wph wph wph
    merco2 wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi
    wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wps
    wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wi wph wph wph wph wph
    wph merco2 wph wch wi wfal wph wi wps wi wi wfal wph wi wps wi wi wph wps
    wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wi wph wph wi wfal wph
    wi wph wi wi wph wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph
    wi wi wph wph wi wph wph wph wi wi wi wi wph wps wi wps wph wch wi wi wta
    wth wph wch wi wi wi wi wi wi wi wph wch wi wfal wph wi wps wi wi wfal wph
    wi wps wi wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wph wch wi
    wfal wph wi wps wi wi wfal wph wi wps wi wi wph wps wi wps wph wch wi wi
    wta wth wph wch wi wi wi wi wi wi wph wch wi wfal wph wi wps wi wph wps wta
    wth merco2 wph wps wi wph wch wi wfal wph wi wps wi wi wfal wph wi wps wi
    wi wps wph wch wi wi wta wth wph wch wi wi wi wi mercolem3 ax-mp wph wps wi
    wps wph wch wi wi wta wth wph wch wi wi wi wi wi wfal wph wi wph wch wi
    wfal wph wi wps wi wi wfal wph wi wps wi wi wi wi wfal wph wi wph wch wi
    wfal wph wi wps wi wi wfal wph wi wps wi wi wi wi wph wch wi wfal wph wi
    wps wi wi wfal wph wi wps wi wi wph wps wi wps wph wch wi wi wta wth wph
    wch wi wi wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph
    wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi wph wph wph wi
    wi wi wi wph wps wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wi wi
    wi wph wps wi wph wch wi wfal wph wi wps wi wi wfal wph wi wps wi wi wi wph
    wps wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wfal wph wi wph wch
    wi wfal wph wi wps wi wi wfal wph wi wps wi wi wi wi wfal wph wi wph wch wi
    wfal wph wi wps wi wi wfal wph wi wps wi wi wi wi wph wps wch wfal wph wi
    mercolem7 wph wps wi wph wch wi wfal wph wi wps wi wi wfal wph wi wps wi wi
    wps wph wch wi wi wta wth wph wch wi wi wi wi wfal wph wi mercolem7 ax-mp
    wph wps wi wps wph wch wi wi wta wth wph wch wi wi wi wi wi wfal wph wi wph
    wch wi wfal wph wi wps wi wi wfal wph wi wps wi wi wi wph wph wch wi wfal
    wph wi wps wi wi wfal wph wi wps wi wi wph wph wi wfal wph wi wph wi wi wph
    wph wi wph wph wph wi wi wi wi wph wph wi wfal wph wi wph wi wi wph wph wi
    wph wph wph wi wi wi wi merco2 ax-mp ax-mp ax-mp ax-mp $.

  $( ~ tbw-ax1 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wps wch wi wph wps wi wps wch wi wph wch wi wi wi wi wph wps wi wps wch wi
    wph wch wi wi wi wph wps wi wps wph wch wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wps wch wi wps wph wch wi wi wph wps wi wps wch wi wph wch
    wi wi wi wph wps wch wps wch wi wph wps wi mercolem8 wph wps wch mercolem3
    wph wps wi wps wph wch wi wi wps wch wi wph wch wi wi mercolem6 mpsyl wps
    wch wi wph wps wi wph wch wi mercolem6 ax-mp $.

  $( ~ tbw-ax2 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw2 $p |- ( ph -> ( ps -> ph ) ) $=
    wps wph wps wph wi wi wi wph wps wph wi wi wph wps wph wps wph wi wi wi wi
    wps wph wps wph wi wi wi wph wph wi wph wi wph wps wph wi wi wi wph wps wph
    wps wph wi wi wi wi wph wph wph wps mercolem1 wph wph wi wph wph wps wph wi
    wi wps mercolem1 ax-mp wph wps wps wph wi mercolem6 ax-mp wps wph wph
    mercolem6 ax-mp $.

  $( ~ tbw-ax3 rederived from ~ merco2 .  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    wph wph wi wph wi wph wph wph wi wi wi wph wps wi wph wi wph wi wph wph wph
    wph mercolem2 wph wps wi wph wi wph wph wi wph wi wph wph wph wi wi wi wph
    wps wi wph wi wph wi wi wi wph wph wi wph wi wph wph wph wi wi wi wph wps
    wi wph wi wph wi wi wph wps wph wph wi wph wi wph wph wph wi wi wi wph wps
    wi wph wi mercolem2 wph wps wi wph wi wph wph wi wph wi wph wph wph wi wi
    wi wph mercolem6 ax-mp ax-mp $.

  $( ~ tbw-ax4 rederived from ~ merco2 .

     This theorem, along with ~ re1tbw1 , ~ re1tbw2 , and ~ re1tbw3 , shows
     that ~ merco2 , along with ~ ax-mp , can be used as a complete
     axiomatization of propositional calculus.  (Contributed by Anthony Hart,
     16-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  re1tbw4 $p |- ( F. -> ph ) $=
    wph wph wi wfal wph wi wph wph wi wph wi wph wi wph wph wi wph wph re1tbw3
    wph wph wph wi wph wi wi wph wph wi wph wi wph wi wph wph wi wi wph wph wph
    wi re1tbw2 wph wph wph wi wph wi wph re1tbw1 ax-mp ax-mp wph wph wi wph wph
    wi wfal wph wi wi wph wph wi wph wi wph wi wph wph wi wph wph re1tbw3 wph
    wph wph wi wph wi wi wph wph wi wph wi wph wi wph wph wi wi wph wph wph wi
    re1tbw2 wph wph wph wi wph wi wph re1tbw1 ax-mp ax-mp wfal wph wi wfal wph
    wi wi wph wph wi wph wph wi wfal wph wi wi wi wfal wph wi wph wi wfal wph
    wi wi wfal wph wi wi wfal wph wi wfal wph wi wi wfal wph wi wph re1tbw3
    wfal wph wi wfal wph wi wph wi wfal wph wi wi wi wfal wph wi wph wi wfal
    wph wi wi wfal wph wi wi wfal wph wi wfal wph wi wi wi wfal wph wi wfal wph
    wi wph wi re1tbw2 wfal wph wi wfal wph wi wph wi wfal wph wi wi wfal wph wi
    re1tbw1 ax-mp ax-mp wfal wph wi wph wi wfal wph wi wfal wph wi wi wi wfal
    wph wi wfal wph wi wi wph wph wi wph wph wi wfal wph wi wi wi wi wfal wfal
    wph wi wph mercolem3 wfal wph wi wph wph wfal wph wi wph wph wi wph wph wi
    merco2 ax-mp ax-mp ax-mp ax-mp $.


