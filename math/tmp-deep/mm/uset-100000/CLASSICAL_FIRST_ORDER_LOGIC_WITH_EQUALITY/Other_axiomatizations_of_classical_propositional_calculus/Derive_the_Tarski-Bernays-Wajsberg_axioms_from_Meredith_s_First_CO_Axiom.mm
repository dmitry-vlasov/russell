
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_Axioms_from_the_Tarski-Bernays-Wajsberg_Axioms.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Derive the Tarski-Bernays-Wajsberg axioms from Meredith's First CO Axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( A single axiom for propositional calculus offered by Meredith.

     This axiom is worthy of note, due to it having only 19 symbols, not
     counting parentheses.  The more well-known ~ meredith has 21 symbols, sans
     parentheses.

     See ~ merco2 for another axiom of equal length.  (Contributed by Anthony
     Hart, 13-Aug-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merco1 $p |- ( ( ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> th ) -> ta )
         -> ( ( ta -> ph ) -> ( ch -> ph ) ) ) $=
    wph wps wi wch wfal wi wi wth wi wta wi wph wps wi wth wn wch wn wi wi wth
    wi wta wi wta wph wi wch wph wi wi wph wps wi wth wn wch wn wi wi wth wi
    wph wps wi wch wfal wi wi wth wi wta wph wps wi wch wfal wi wi wph wps wi
    wth wn wch wn wi wi wth wch wfal wi wth wn wch wn wi wph wps wi wch wfal
    wth wn wch wn wi wch wn wth wn ax-1 wth wn wch wn wi falim ja imim2i imim1i
    imim1i wph wps wth wch wta meredith syl $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem1 $p |- ( ph -> ( F. -> ch ) ) $=
    wph wph wfal wph wi wi wi wph wfal wch wi wi wph wfal wph wi wi wfal wph wi
    wi wph wfal wph wi wi wi wph wph wfal wph wi wi wi wfal wph wi wfal wi wph
    wfal wi wi wfal wph wi wi wph wfal wph wi wi wi wph wfal wph wi wi wfal wph
    wi wi wph wfal wph wi wi wi wfal wph wi wph wfal wi wi wph wfal wi wi wfal
    wph wi wi wfal wph wi wfal wi wph wfal wi wi wi wfal wph wi wfal wi wph
    wfal wi wi wfal wph wi wi wph wfal wph wi wi wi wfal wph wph wph wfal wi
    wfal wph wi merco1 wfal wph wi wph wfal wi wph wfal wph wi wfal wph wi wfal
    wi wph wfal wi wi merco1 ax-mp wfal wph wi wfal wph wfal wph wi wph wfal
    wph wi wi merco1 ax-mp wph wfal wph wi wi wfal wi wph wfal wi wi wfal wph
    wi wi wph wfal wph wi wi wfal wph wi wi wi wph wfal wph wi wi wfal wph wi
    wi wph wfal wph wi wi wi wph wph wfal wph wi wi wi wi wfal wph wi wph wfal
    wi wi wph wfal wph wi wi wfal wi wi wph wfal wph wi wi wi wph wfal wph wi
    wi wfal wi wph wfal wi wi wi wph wfal wph wi wi wfal wi wph wfal wi wi wfal
    wph wi wi wph wfal wph wi wi wfal wph wi wi wi wfal wph wph wph wfal wph wi
    wi wfal wi wph wfal wph wi wi merco1 wfal wph wi wph wfal wi wph wfal wph
    wi wi wph wfal wph wi wi wph wfal wph wi wi wfal wi wph wfal wi wi merco1
    ax-mp wph wfal wph wi wi wfal wph wfal wph wi wph wfal wph wi wi wfal wph
    wi wi merco1 ax-mp ax-mp wph wfal wph wi wi wfal wch wi wi wph wfal wch wi
    wi wi wph wph wfal wph wi wi wi wph wfal wch wi wi wi wfal wch wi wfal wi
    wph wfal wi wi wfal wph wi wi wph wfal wph wi wi wi wph wfal wph wi wi wfal
    wch wi wi wph wfal wch wi wi wi wfal wph wi wph wfal wi wi wph wfal wi wi
    wfal wch wi wi wfal wch wi wfal wi wph wfal wi wi wi wfal wch wi wfal wi
    wph wfal wi wi wfal wph wi wi wph wfal wph wi wi wi wfal wph wph wph wfal
    wi wfal wch wi merco1 wfal wph wi wph wfal wi wph wfal wch wi wfal wch wi
    wfal wi wph wfal wi wi merco1 ax-mp wfal wch wi wfal wph wfal wph wi wph
    wfal wph wi wi merco1 ax-mp wph wfal wch wi wi wfal wi wph wph wfal wph wi
    wi wi wfal wi wi wfal wch wi wi wph wfal wph wi wi wfal wch wi wi wi wph
    wfal wph wi wi wfal wch wi wi wph wfal wch wi wi wi wph wph wfal wph wi wi
    wi wph wfal wch wi wi wi wi wfal wch wi wph wph wfal wph wi wi wi wfal wi
    wi wph wfal wph wi wi wfal wi wi wph wfal wch wi wi wi wph wfal wch wi wi
    wfal wi wph wph wfal wph wi wi wi wfal wi wi wi wph wfal wch wi wi wfal wi
    wph wph wfal wph wi wi wi wfal wi wi wfal wch wi wi wph wfal wph wi wi wfal
    wch wi wi wi wfal wch wph wph wfal wph wi wi wi wph wfal wph wi wi wfal wi
    wph wfal wch wi wi merco1 wfal wch wi wph wph wfal wph wi wi wi wfal wi wph
    wfal wph wi wi wph wfal wch wi wi wph wfal wch wi wi wfal wi wph wph wfal
    wph wi wi wi wfal wi wi merco1 ax-mp wph wfal wch wi wi wfal wph wph wfal
    wph wi wi wi wfal wch wi wph wfal wph wi wi wfal wch wi wi merco1 ax-mp
    ax-mp ax-mp $.

  $( ~ tbw-ax4 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax4 $p |- ( F. -> ph ) $=
    wph wfal wph wi wi wfal wph wi wph wph merco1lem1 wph wfal wph wi wi wph
    merco1lem1 ax-mp $.

  $( ~ tbw-ax2 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax2 $p |- ( ph -> ( ps -> ph ) ) $=
    wph wph wph wph wi wi wi wph wps wph wi wi wfal wph wi wph wph wi wi wph
    wph wph wi wi wi wph wph wph wph wi wi wi wph wph wi wph wi wph wfal wi wi
    wph wi wfal wph wi wi wfal wph wi wph wph wi wi wph wph wph wi wi wi wph
    wph wi wph wi wph wfal wi wi wph wi wph merco1lem1 wph wph wi wph wph wph
    wfal wph wi merco1 ax-mp wph wph wph wi wi wph wfal wi wi wph wfal wi wi
    wfal wi wfal wph wi wph wph wi wi wi wfal wph wi wph wph wi wi wph wph wph
    wi wi wi wph wph wph wph wi wi wi wi wph wph wph wi wph wph wfal wi wfal
    merco1 wph wph wph wi wi wph wfal wi wph wfal wfal wph wi wph wph wi wi
    merco1 ax-mp ax-mp wfal wph wi wps wph wi wi wph wps wph wi wi wi wph wph
    wph wph wi wi wi wph wps wph wi wi wi wps wph wi wph wi wph wfal wi wi wph
    wi wfal wph wi wi wfal wph wi wps wph wi wi wph wps wph wi wi wi wps wph wi
    wph wi wph wfal wi wi wph wi wph merco1lem1 wps wph wi wph wph wph wfal wph
    wi merco1 ax-mp wph wps wph wi wi wps wfal wi wi wph wph wph wph wi wi wi
    wfal wi wi wfal wi wfal wph wi wps wph wi wi wi wfal wph wi wps wph wi wi
    wph wps wph wi wi wi wph wph wph wph wi wi wi wph wps wph wi wi wi wi wph
    wps wph wi wps wph wph wph wph wi wi wi wfal wi wfal merco1 wph wps wph wi
    wi wps wfal wi wph wph wph wph wi wi wi wfal wfal wph wi wps wph wi wi
    merco1 ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem2 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ( ( ps -> ta ) -> ( ph ->
    F. ) ) -> ch ) ) $=
    wch wph wi wps wta wi wph wfal wi wi wfal wi wi wps wi wph wps wi wi wph
    wps wi wch wi wps wta wi wph wfal wi wi wch wi wi wps wta wi wph wfal wi wi
    wfal wi wch wph wi wps wta wi wph wfal wi wi wfal wi wi wi wch wph wi wps
    wta wi wph wfal wi wi wfal wi wi wps wi wph wps wi wi wps wta wi wph wfal
    wi wi wfal wi wch wph wi retbwax2 wps wta wph wfal wch wph wi wps wta wi
    wph wfal wi wi wfal wi wi merco1 ax-mp wch wph wps wta wi wph wfal wi wi
    wps wph wps wi merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem3 $p |- ( ( ( ph -> ps ) -> ( ch -> F. ) ) -> ( ch -> ph ) ) $=
    wph wph wph wi wph wfal wi wi wph wph wi wi wi wph wps wi wch wfal wi wi
    wch wph wi wi wph wph wi wfal wi wph wph wi wph wfal wi wi wfal wi wi wph
    wph wph wi wph wfal wi wi wph wph wi wi wi wph wph wfal wph merco1lem2 wph
    wph wi wph wfal wi wi wph wph wi wi wph wph wph wi wph wfal wi wi wph wph
    wi wi wi wi wph wph wi wfal wi wph wph wi wph wfal wi wi wfal wi wi wph wph
    wph wi wph wfal wi wi wph wph wi wi wi wi wph wph wi wph wfal wi wi wph wph
    wi wi wph retbwax2 wph wph wi wph wfal wi wi wph wph wi wph wph wph wi wph
    wfal wi wi wph wph wi wi wi wfal merco1lem2 ax-mp ax-mp wch wph wi wfal wi
    wph wps wi wch wfal wi wi wfal wi wi wph wph wph wi wph wfal wi wi wph wph
    wi wi wi wph wps wi wch wfal wi wi wch wph wi wi wi wch wph wfal wps
    merco1lem2 wph wps wi wch wfal wi wi wch wph wi wi wph wph wph wi wph wfal
    wi wi wph wph wi wi wi wph wps wi wch wfal wi wi wch wph wi wi wi wi wch
    wph wi wfal wi wph wps wi wch wfal wi wi wfal wi wi wph wph wph wi wph wfal
    wi wi wph wph wi wi wi wph wps wi wch wfal wi wi wch wph wi wi wi wi wph
    wps wi wch wfal wi wi wch wph wi wi wph wph wph wi wph wfal wi wi wph wph
    wi wi wi retbwax2 wph wps wi wch wfal wi wi wch wph wi wph wph wph wi wph
    wfal wi wi wph wph wi wi wi wph wps wi wch wfal wi wi wch wph wi wi wi wfal
    merco1lem2 ax-mp ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem4 $p |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) ) $=
    wch wph wi wps wfal wi wi wps wi wph wps wi wi wph wps wi wch wi wps wch wi
    wi wps wfal wi wph wfal wi wi wch wph wi wfal wi wi wch wph wi wps wfal wi
    wi wi wch wph wi wps wfal wi wi wps wi wph wps wi wi wps wfal wi wph wfal
    wi wch wph wi merco1lem3 wps wfal wph wch wph wi wfal wi wch wph wi wps
    wfal wi wi merco1 ax-mp wch wph wps wps wph wps wi merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem5 $p |- ( ( ( ( ph -> F. ) -> ch ) -> ta ) -> ( ph -> ta ) ) $=
    wta wph wi wph wfal wi wi wch wi wph wfal wi wch wi wi wph wfal wi wch wi
    wta wi wph wta wi wi wta wph wi wph wfal wi wch merco1lem4 wta wph wph wch
    wph wfal wi wch wi merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ch -> ( ph -> ps ) ) ) $=
    wph wps wi wfal wi wch wfal wi wi wfal wi wph wi wph wph wps wi wi wch wph
    wps wi wi wi wph wps wi wph wps wi wfal wi wch wfal wi wi wfal wi wfal wi
    wi wph wps wi wfal wi wch wfal wi wi wfal wi wph wi wph wps wi wfal wi wch
    wfal wi wi wph wps wi wfal wi wch wfal wi wi wfal wi wfal wi wi wph wps wi
    wph wps wi wfal wi wch wfal wi wi wfal wi wfal wi wi wph wps wi wfal wi wch
    wfal wi wi wfal wi wfal wi wfal wi wph wps wi wfal wi wch wfal wi wi wfal
    wi wi wph wps wi wfal wi wch wfal wi wi wph wps wi wfal wi wch wfal wi wi
    wfal wi wfal wi wi wph wps wi wfal wi wch wfal wi wi wfal wfal merco1lem5
    wph wps wi wfal wi wch wfal wi wi wfal wi wfal wi wfal wph wps wi wfal wi
    wch wfal wi wi merco1lem3 ax-mp wph wps wi wch wfal wi wph wps wi wfal wi
    wch wfal wi wi wfal wi wfal wi merco1lem5 ax-mp wph wps wph wps wi wfal wi
    wch wfal wi wi wfal wi merco1lem3 ax-mp wph wps wi wfal wch wfal wph merco1
    ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem7 $p |- ( ph -> ( ( ( ps -> ch ) -> ps ) -> ps ) ) $=
    wps wch wi wps wi wps wch wi wps wi wps wi wi wph wps wch wi wps wi wps wi
    wi wps wfal wi wps wch wi wps wi wfal wi wi wch wi wps wch wi wi wps wch wi
    wps wi wps wch wi wps wi wps wi wi wps wps wch wi wps wi wfal wi wch
    merco1lem5 wps wfal wps wch wi wps wi wch wps wch wi merco1 ax-mp wps wch
    wi wps wi wps wph merco1lem6 ax-mp $.

  $( ~ tbw-ax3 rederived from ~ merco1 .  (Contributed by Anthony Hart,
     17-Sep-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  retbwax3 $p |- ( ( ( ph -> ps ) -> ph ) -> ph ) $=
    wph wph wph wi wi wph wps wi wph wi wph wi wph wph retbwax2 wph wph wph wi
    wi wph wps merco1lem7 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 17-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem8 $p |- ( ph -> ( ( ps -> ( ps -> ch ) ) -> ( ps -> ch ) ) ) $=
    wps wps wch wi wi wps wps wch wi wi wps wch wi wi wi wph wps wps wch wi wi
    wps wch wi wi wi wps wch wps wps wch wi wi merco1lem6 wps wps wch wi wi wps
    wch wi wph merco1lem6 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem9 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    wfal wph wi wph wph wps wi wi wph wps wi wi wi wph wph wps wi wi wph wps wi
    wi wfal wph wi wph wps merco1lem8 wfal wph wi wph wph wps wi wi wph wps wi
    wi wi wph wps merco1lem8 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem10 $p |- ( ( ( ( ( ph -> ps ) -> ch ) -> ( ta -> ch ) ) -> ph ) ->
    ( th -> ph ) ) $=
    wph wps wi wth wfal wi wi wch wph wi wta wfal wi wi wph wi wfal wi wi wph
    wps wi wch wi wta wch wi wi wi wph wps wi wch wi wta wch wi wi wph wi wth
    wph wi wi wch wph wi wta wfal wi wi wph wi wph wps wi wi wph wps wi wch wi
    wta wch wi wi wi wph wps wi wth wfal wi wi wch wph wi wta wfal wi wi wph wi
    wfal wi wi wph wps wi wch wi wta wch wi wi wi wch wph wta wph wph wps wi
    merco1 wch wph wi wta wfal wi wi wph wi wph wps wi wph wps wi wch wi wta
    wch wi wi wth wfal wi merco1lem2 ax-mp wph wps wth wch wph wi wta wfal wi
    wi wph wi wfal wi wph wps wi wch wi wta wch wi wi merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem11 $p |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> F. ) -> ps
    ) ) $=
    wph wta wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi wfal wi wfal wi
    wi wph wps wi wch wph wta wi wi wfal wi wps wi wi wch wph wta wi wi wps wph
    wi wch wph wta wi wi wfal wi wfal wi wi wfal wi wfal wi wi wph wta wi wps
    wph wi wch wph wta wi wi wfal wi wfal wi wi wfal wi wfal wi wi wch wph wta
    wi wi wfal wi wfal wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi wfal
    wi wfal wi wi wch wph wta wi wi wps wph wi wch wph wta wi wi wfal wi wfal
    wi wi wfal wi wfal wi wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi
    wps wph wi wch wph wta wi wi wfal wi wfal wi wi wfal wi wfal wi wi wch wph
    wta wi wi wfal wi wfal wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi
    wfal wi wfal wi wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi wfal wi
    wfal wi wfal wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi wfal wi wi
    wps wph wi wch wph wta wi wi wfal wi wfal wi wi wps wph wi wch wph wta wi
    wi wfal wi wfal wi wi wfal wi wfal wi wi wps wph wi wch wph wta wi wi wfal
    wi wfal wi wi wfal wfal merco1lem5 wps wph wi wch wph wta wi wi wfal wi
    wfal wi wi wfal wi wfal wi wfal wps wph wi wch wph wta wi wi wfal wi wfal
    wi wi merco1lem3 ax-mp wps wph wi wch wph wta wi wi wfal wi wfal wi wps wph
    wi wch wph wta wi wi wfal wi wfal wi wi wfal wi wfal wi merco1lem4 ax-mp
    wch wph wta wi wi wfal wps wph wi wch wph wta wi wi wfal wi wfal wi wi wfal
    wi wfal wi merco1lem5 ax-mp wch wph wta wi wps wph wi wch wph wta wi wi
    wfal wi wfal wi wi wfal wi wfal wi merco1lem4 ax-mp wps wph wi wch wph wta
    wi wi wfal wi wfal wi wi wfal wi wph wi wph wps wi wch wph wta wi wi wfal
    wi wps wi wi wi wph wta wi wps wph wi wch wph wta wi wi wfal wi wfal wi wi
    wfal wi wfal wi wi wph wps wi wch wph wta wi wi wfal wi wps wi wi wi wps
    wph wch wph wta wi wi wfal wi wfal wph merco1 wps wph wi wch wph wta wi wi
    wfal wi wfal wi wi wfal wi wph wph wps wi wch wph wta wi wi wfal wi wps wi
    wi wta merco1lem2 ax-mp ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem12 $p |- ( ( ph -> ps ) -> ( ( ( ch -> ( ph -> ta ) ) -> ph ) -> ps
    ) ) $=
    wps wph wi wch wph wta wi wi wph wi wfal wi wi wfal wi wph wi wph wps wi
    wch wph wta wi wi wph wi wps wi wi wch wph wta wi wi wph wi wph wi wps wph
    wi wch wph wta wi wi wph wi wfal wi wi wfal wi wph wi wch wph wta wi wi wph
    wi wch wph wta wi wi wph wi wph wi wi wch wph wta wi wi wph wi wph wi wph
    wta wi wch wph wta wi wi wph wi wfal wi wi wch wfal wi wi wch wph wta wi wi
    wi wch wph wta wi wi wph wi wch wph wta wi wi wph wi wph wi wi wph wta wi
    wch wph wta wi wi wph wi wfal wi wch merco1lem3 wph wta wch wph wta wi wi
    wph wi wch wfal wi wch wph wta wi wi merco1 ax-mp wch wph wta wi wi wph wi
    wph merco1lem9 ax-mp wch wph wta wi wi wph wi wph wps wph wi wfal
    merco1lem11 ax-mp wps wph wch wph wta wi wi wph wi wfal wph merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem13 $p |- ( ( ( ( ph -> ps ) -> ( ch -> ps ) ) -> ta ) -> ( ph ->
    ta ) ) $=
    wta wph wi wph wfal wi wi wph wi wph wps wi wch wps wi wi wi wph wps wi wch
    wps wi wi wta wi wph wta wi wi wph wph wps wi wch wps wi wi wi wta wph wi
    wph wfal wi wi wph wi wph wps wi wch wps wi wi wi wps wph wi wch wfal wi wi
    wph wi wph wi wph wps wi wch wps wi wi wi wph wph wps wi wch wps wi wi wi
    wps wph wch wph wph merco1 wps wph wi wch wfal wi wi wph wi wph wph wps wi
    wch wps wi wi merco1lem4 ax-mp wph wph wps wi wch wps wi wi wta wph wi wfal
    merco1lem12 ax-mp wta wph wph wph wph wps wi wch wps wi wi merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem14 $p |- ( ( ( ( ph -> ps ) -> ps ) -> ch ) -> ( ph -> ch ) ) $=
    wch wph wi wph wfal wi wi wph wi wph wps wi wps wi wi wph wps wi wps wi wch
    wi wph wch wi wi wph wph wps wi wps wi wi wch wph wi wph wfal wi wi wph wi
    wph wps wi wps wi wi wph wps wi wph wps wi wps wi wi wph wps wi wps wi wi
    wph wph wps wi wps wi wi wi wph wph wps wi wps wi wi wph wps wph wps wi wph
    wps wi wps wi merco1lem13 wph wps wi wph wps wi wps wi wi wph wps wi wps wi
    wi wph wph wps wi wps wi wi wi wph wps wi wph wps wi wps wi wi wph wps wi
    wps wi wi wph wph wps wi wps wi wi wi wph wph wps wi wps wi wi wi wi wph
    wps wi wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps wi wi
    wi wph wph wps wi wps wi wi wi wph wph wps wi wps wi wi wph wi wph wps wi
    wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps wi wi wi wfal
    wi wi wph wi wph wps wi wph wps wi wps wi wi wph wps wi wps wi wi wi wph
    wps wi wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps wi wi
    wi wph wps wi wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps
    wi wi wi wph wph wps wi wps wi wi wi wi wph wph wps wi wps wi wi wph wi wph
    wps wi wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps wi wi
    wi wfal wi wi wph wi wph wps wi wps merco1lem8 wph wph wps wi wps wi wi wph
    wph wps wi wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps wi
    wi wi wph wph wps wi wph wps wi wps wi wi wph wps wi wps wi wi merco1 ax-mp
    wph wps wi wph wps wi wps wi wi wph wps wi wps wi wi wph wph wps wi wps wi
    wi wi wph wph wps wi wps wi wi merco1lem9 ax-mp ax-mp wph wph wps wi wps wi
    wch wph wi wfal merco1lem12 ax-mp wch wph wph wph wph wps wi wps wi merco1
    ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem15 $p |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) ) $=
    wph wps wi wps wi wch wps wi wi wph wch wps wi wi wi wph wps wi wph wch wps
    wi wi wi wph wps wch wps wi merco1lem14 wph wps wi wps wch wph wch wps wi
    wi merco1lem13 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem16 $p |- ( ( ( ph -> ( ps -> ch ) ) -> ta ) -> ( ( ph -> ch ) -> ta
    ) ) $=
    wta wph wi wph wch wi wfal wi wi wfal wi wph wps wch wi wi wi wph wps wch
    wi wi wta wi wph wch wi wta wi wi wph wch wi wph wps wch wi wi wi wta wph
    wi wph wch wi wfal wi wi wfal wi wph wps wch wi wi wi wph wch wps
    merco1lem15 wph wch wi wph wps wch wi wi wta wph wi wfal merco1lem11 ax-mp
    wta wph wph wch wi wfal wph wps wch wi wi merco1 ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem17 $p |- ( ( ( ( ( ph -> ps ) -> ph ) -> ch ) -> ta ) -> ( ( ph ->
    ch ) -> ta ) ) $=
    wta wph wi wph wch wi wfal wi wi wch wi wph wps wi wph wi wch wi wi wph wps
    wi wph wi wch wi wta wi wph wch wi wta wi wi wph wch wi wfal wi wph wch wi
    wi wph wps wi wph wi wch wi wi wta wph wi wph wch wi wfal wi wi wch wi wph
    wch wi wfal wi wch wi wph wps wi wph wi wch wi wph wch wi wph wps wi wph wi
    wch wi wi wph wch wi wfal wi wph wch wi wi wph wps wi wph wi wch wi wi wch
    wph wi wph wps wi wph wi wfal wi wi wfal wi wph wi wph wch wi wph wps wi
    wph wi wch wi wi wph wps wi wph wi wph wi wch wph wi wph wps wi wph wi wfal
    wi wi wfal wi wph wi wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi wph
    wi wph wps wi wph wi wph wch wph wi wfal merco1lem11 wph wps wi wph wi wph
    wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi wph wi wi wph wps wi wph
    wi wph wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi wph wi wi wch wph
    wi wph wps wi wph wi wfal wi wi wfal wi wph wi wi wi wph wps wi wph wi wph
    wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi wph wi wi wch wph wi wph
    wps wi wph wi wfal wi wi wfal wi wph wi wi wch wph wi wph wps wi wph wi
    wfal wi wi wfal wi wph wi wph wi wph wps wi wph wi wph wi wch wph wi wph
    wps wi wph wi wfal wi wi wfal wi wph wi wi wfal wi wi wph wi wph wps wi wph
    wi wph wi wi wph wps wi wph wi wph wi wch wph wi wph wps wi wph wi wfal wi
    wi wfal wi wph wi wi wph wps wi wph wi wph wi wch wph wi wph wps wi wph wi
    wfal wi wi wfal wi wph wi wi wch wph wi wph wps wi wph wi wfal wi wi wfal
    wi wph wi wi wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi wph wi wph
    wi wph wps wi wph wi wph wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi
    wph wi wi wfal wi wi wph wi wph wps merco1lem7 wch wph wi wph wps wi wph wi
    wfal wi wi wfal wi wph wi wph wph wps wi wph wi wph wi wch wph wi wph wps
    wi wph wi wfal wi wi wfal wi wph wi wi wph wph wps wi wph wi wph wi merco1
    ax-mp wph wps wi wph wi wph wi wch wph wi wph wps wi wph wi wfal wi wi wfal
    wi wph wi wi wch wph wi wph wps wi wph wi wfal wi wi wfal wi wph wi
    merco1lem9 ax-mp ax-mp wch wph wph wps wi wph wi wfal wph merco1 ax-mp wph
    wps wi wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi
    wfal wi wph wch wi wi wph wch wi wph wps wi wph wi wch wi wi wph wch wi
    wfal wi wph wch wi wi wph wps wi wph wi wch wi wi wi wph wch wi wfal wi wph
    wch wi wi wph wch wi wi wph wps wi wph wi wch wi wph wi wph wch wi wfal wi
    wph wch wi wi wfal wi wi wfal wi wph wch wi wi wi wph wps wi wph wi wch wi
    wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi
    wph wch wi wfal wi wph wch wi wi wph wch wi wph wps wi wph wi wch wi wph wi
    wfal merco1lem11 wph wch wi wfal wi wph wch wi wi wph wch wi wi wph wps wi
    wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi
    wph wch wi wi wi wph wch wi wfal wi wph wch wi wi wph wch wi wi wph wps wi
    wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi
    wph wch wi wi wi wph wps wi wph wi wch wi wph wi wph wch wi wfal wi wph wch
    wi wi wfal wi wi wfal wi wph wch wi wi wi wi wph wch wi wfal wi wph wch wi
    wi wph wch wi wi wph wps wi wph wi wch wi wph wi wph wch wi wfal wi wph wch
    wi wi wfal wi wi wfal wi wph wch wi wi wi wph wps wi wph wi wch wi wph wi
    wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi wi wph
    wps wi wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi
    wfal wi wph wch wi wi wph wi wph wch wi wfal wi wph wch wi wi wph wch wi wi
    wph wps wi wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi
    wfal wi wph wch wi wi wi wfal wi wi wph wi wph wch wi wfal wi wph wch wi wi
    wph wch wi wi wi wph wch wi wfal wi wph wch wi wi wph wch wi wi wph wps wi
    wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi
    wph wch wi wi wi wph wch wi wfal wi wph wch wi wi wph wch wi wi wph wps wi
    wph wi wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi
    wph wch wi wi wi wph wps wi wph wi wch wi wph wi wph wch wi wfal wi wph wch
    wi wi wfal wi wi wfal wi wph wch wi wi wi wi wph wps wi wph wi wch wi wph
    wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi wph wi
    wph wch wi wfal wi wph wch wi wi wph wch wi wi wph wps wi wph wi wch wi wph
    wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi wi
    wfal wi wi wph wi wph wch wi wfal merco1lem7 wph wps wi wph wi wch wi wph
    wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi wph
    wph wch wi wfal wi wph wch wi wi wph wch wi wi wph wps wi wph wi wch wi wph
    wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi wi wph
    wph wch wi wfal wi wph wch wi wi wph wch wi wi merco1 ax-mp wph wch wi wfal
    wi wph wch wi wi wph wch wi wi wph wps wi wph wi wch wi wph wi wph wch wi
    wfal wi wph wch wi wi wfal wi wi wfal wi wph wch wi wi wi wph wps wi wph wi
    wch wi wph wi wph wch wi wfal wi wph wch wi wi wfal wi wi wfal wi wph wch
    wi wi merco1lem9 ax-mp ax-mp wph wps wi wph wi wch wi wph wph wch wi wfal
    wi wph wch wi wi wfal wph wch wi merco1 ax-mp ax-mp wta wph wi wph wch wi
    wfal wi wch merco1lem4 wph wch wi wfal wi wph wch wph wps wi wph wi wch wi
    merco1lem16 mpsyl wta wph wph wch wi wch wph wps wi wph wi wch wi merco1
    ax-mp $.

  $( Used to rederive the Tarski-Bernays-Wajsberg axioms from ~ merco1 .
     (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merco1lem18 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ps -> ph ) -> ( ps ->
    ch ) ) ) $=
    wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wph wps wch wi
    wi wps wph wi wps wch wi wi wi wps wch wi wps wi wph wi wph wps wch wi wi
    wps wph wi wps wch wi wi wi wi wps wph wi wph wps wch wi wi wps wph wi wps
    wch wi wi wi wi wps wch wi wps wi wps wph wi wfal wi wi wps wch wi wps wi
    wi wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wps wch wi wps
    wi wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wps wch wi wps
    wps wph wi wps wch wi wps wi wph merco1 wps wch wi wps wi wps wph wi wfal
    wi wph wph wps wch wi wi wps wph wi wps wch wi wi wi merco1lem17 ax-mp wps
    wch wph wph wps wch wi wi wps wph wi wps wch wi wi wi merco1lem17 ax-mp wps
    wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wps wph wi wph wps
    wch wi wi wps wph wi wps wch wi wi wi wi wph wps wch wi wi wps wph wi wps
    wch wi wi wi wi wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi
    wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wps wph wi wps wch wi
    wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi wph wps
    wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi wfal wi wi wps
    wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wps wph wi wph wps
    wch wi wi wps wph wi wps wch wi wi wi wi wph wps wch wi wi wps wph wi wps
    wch wi wi wi wi wi wph wps wch wi wi wps wph wi wps wch wi wi wi wph wps
    wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi wph wps wch wi wi
    wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi wfal wi wi wps wph wi wps
    wch wi wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi
    wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi wfal wi
    wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi wph wps
    wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wph wps wch wi wi wps
    wph wi wps wch wi wi wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps
    wch wi wi wi wi wfal wi wi wfal wi wfal wi wi wph wps wch wi wi wps wph wi
    wps wch wi wi wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps
    wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi
    wfal wi wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi
    wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi wfal wi
    wfal wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi
    wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi wi wph
    wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi wph wps wch wi
    wi wps wph wi wps wch wi wi wi wi wfal wi wi wph wps wch wi wi wps wph wi
    wps wch wi wi wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi
    wi wi wi wfal wi wi wfal wi wfal wi wi wph wps wch wi wi wps wph wi wps wch
    wi wi wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi
    wi wfal wi wi wfal wfal merco1lem5 wph wps wch wi wi wps wph wi wps wch wi
    wi wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi
    wfal wi wi wfal wi wfal wi wfal wph wps wch wi wi wps wph wi wps wch wi wi
    wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal
    wi wi merco1lem3 ax-mp wph wps wch wi wi wps wph wi wps wch wi wi wi wps
    wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wph wps wch
    wi wi wps wph wi wps wch wi wi wi wfal wi wps wph wi wph wps wch wi wi wps
    wph wi wps wch wi wi wi wi wfal wi wi wfal wi wfal wi merco1lem5 ax-mp wph
    wps wch wi wi wps wph wi wps wch wi wi wph wps wch wi wi wps wph wi wps wch
    wi wi wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi
    wi wfal wi wi wfal wi wfal wi merco1lem4 ax-mp wph wps wch wi wi wps wph wi
    wps wch wi wi wi wfal wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi
    wi wi wi wfal wi wi wfal wi wps wph wi wi wps wph wi wph wps wch wi wi wps
    wph wi wps wch wi wi wi wi wps wph wi wph wps wch wi wi wps wph wi wps wch
    wi wi wi wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wi wi wps wph
    wi wps wch wi wi wph wps wch wi wi wps wph wi wps wch wi wi wi wfal wi wps
    wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi wfal wi
    wfal wi wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wps
    wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wph wps wch wi wi
    wps wph wi wps wch wi wi wi wi wi wi wph wps wch wi wi wps wph wi wps wch
    wi wi wi wfal wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi
    wfal wps wph wi merco1 wph wps wch wi wi wps wph wi wps wch wi wi wi wfal
    wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wfal wi wi
    wfal wi wps wph wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi
    wi wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wph wps wch
    wi wi wps wph wi wps wch wi wi wi wi wi wps wch wi merco1lem2 ax-mp ax-mp
    wps wph wi wph wps wch wi wi wps wph wi wps wch wi wi wi wi wph wps wch wi
    wi wps wph wi wps wch wi wi wi merco1lem9 ax-mp ax-mp $.

  $( ~ tbw-ax1 rederived from ~ merco1 .

     This theorem, along with ~ retbwax2 , ~ retbwax3 , and ~ retbwax4 , shows
     that ~ merco1 with ~ ax-mp can be used as a complete axiomatization of
     propositional calculus.  (Contributed by Anthony Hart, 18-Sep-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  retbwax1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wps wph wch wi wi wph wps wi wph wch wi wi wi wps wch wi wph wps wi wph
    wch wi wi wi wps wph wch merco1lem18 wps wph wch wph wps wi wph wch wi wi
    merco1lem16 ax-mp wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps
    wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi wph wps wi wph wch wi
    wi wi wph wps wi wph wch wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wps wch wi wph wps
    wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wph wps wi
    wph wch wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi
    wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wph wch wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch
    wi wph wch wi wi wi wi wi wph wps wi wph wch wi wi wph wps wi wps wch wi
    wph wch wi wi wi wi wph wps wi wph wch wi wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wph wps wi wph wch wi
    wps wch wi merco1lem15 wph wps wi wph wch wi wi wph wps wi wps wch wi wph
    wch wi wi wi wps wch wi wph wps wi wph wch wi wi wi merco1lem15 ax-mp wph
    wps wi wph wch wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi merco1lem18 ax-mp wps wch wi wph wps wi wph wch wi
    wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi
    wi wi wi merco1lem14 ax-mp wps wch wi wps wch wi wph wps wi wph wch wi wi
    wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph
    wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wph wps
    wi wps wch wi wph wch wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi
    wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wfal wi wps wch wi wph wch wi wi wi wps wch wi wps wch
    wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wfal wi wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wph wch wi wi wps wch wi wph wch wi wi wi wps wch wi wps wch
    wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wfal wi wps wch wi wph wch wi wi wi wps wch wi wps wch wi wph wps
    wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wph wch wi
    merco1lem14 wps wch wi wph wch wi wi wph wi wps wch wi wps wch wi wph wps
    wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wfal wi wfal wi wi wph wch wi wi wps wch wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi
    wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wph wch wi wi
    wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi
    wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wph wch wi wi wps wch wi wph wch wi wi wi
    wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wfal wi wps wch wi wph wch wi wi wi wi wph
    wch wi wph wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wi wps wch wi wps wch
    wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wfal wi wfal wi wi wps wch wi wph wch wi wi wph wi wps wch wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wfal wi wfal wi wi wi wps wch wi wph wch wi wi wph wi wps
    wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi
    wph wch wi wi wi wi wi wfal wi wfal wi wi wph wch wi wi wps wch wi wps wch
    wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wph wch wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wfal wi wfal
    wi wps wch wi wph wch wi wi wph wi wfal wi wi wps wch wi wps wch wi wph wps
    wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wfal wi wi wph wch wi wph wi wps wch wi wps wch wi wph wps wi wph wch wi wi
    wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph
    wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wi wi wph
    wch wi wph wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wi wps wch wi wps wch
    wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wfal wi wfal wi wi wps wch wi wph wch wi wi wph wi wps wch wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wfal wi wfal wi wi wi wps wch wi wps wch wi wph wps wi wph
    wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph
    wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal
    wi wfal wfal wph wch wi wph wi wps wch wi wph wch wi wi wph wi merco1lem10
    wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wfal wi wfal wi wfal wps wch wi wph wch wi wi
    wph wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch
    wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wfal wi wph wch wi wph wi wps wch wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wfal wi wi merco1 ax-mp wph wch wi wph wps wch wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph
    wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wfal wi wps wch wi wph wch
    wi wi wph wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wfal wi wi merco1
    ax-mp wps wch wi wph wch wi wi wph wps wch wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi
    wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wph
    wch wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch
    wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wph wch wi wi merco1 ax-mp ax-mp wps wch
    wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi
    wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi
    wph wch wi wi wi wi wi wfal wi wps wch wi wph wch wi wi wph wps wi
    merco1lem15 ax-mp wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps
    wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wph wps wi wps wch wi
    wph wch wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi
    wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi
    wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wi wps wch wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph
    wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi
    wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wph wps wi wps
    wch wi wph wch wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi wi
    wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph
    wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wi wps wch wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wfal wi wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi
    wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wph
    wps wi wps wch wi wph wch wi wi wi wi wps wch wi wph wps wi wph wch wi wi
    wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wps wch wi wph
    wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph
    wps wi wps wch wi wph wch wi wi wi wi wi wi wi wps wch wi wps wch wi wph
    wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps
    wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wi wi wfal wi wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi wph wps
    wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph
    wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi
    wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wi wps wch wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wfal wph wps wi wps wch wi wph wch wi wi wi wps wch wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wfal wi wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi wph
    wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps
    wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch
    wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi
    wph wch wi wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    merco1lem10 wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi
    wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi
    wph wps wi wps wch wi wph wch wi wi wi wi wi wfal wi wph wps wi wps wch wi
    wph wch wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi wps wch wi wps wch wi wph wps wi wph wch wi
    wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph wps wi
    wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wi wps wch wi
    wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi
    wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi merco1lem9 ax-mp wps wch wi wps wch wi wph wps wi wph
    wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wps wch wi wph
    wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi wfal
    wi wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi wph wps wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wps wch wi wps wch wi
    wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wi
    wps wch wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps wch wi wph
    wch wi wi wi wi wi wps wch wi wph wps wi wph wch wi wi wi wph wps wi wps
    wch wi wph wch wi wi wi wi wi merco1lem13 ax-mp ax-mp ax-mp ax-mp $.


