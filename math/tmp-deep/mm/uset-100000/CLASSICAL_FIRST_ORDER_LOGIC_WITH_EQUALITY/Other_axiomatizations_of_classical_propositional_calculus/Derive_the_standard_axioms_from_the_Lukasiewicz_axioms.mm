
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_Meredith_s_sole_axiom.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    luklem1.1 $e |- ( ph -> ps ) $.
    luklem1.2 $e |- ( ps -> ch ) $.
    $( Used to rederive standard propositional axioms from Lukasiewicz'.
       (Contributed by NM, 23-Dec-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    luklem1 $p |- ( ph -> ch ) $=
      wps wch wi wph wch wi luklem1.2 wph wps wi wps wch wi wph wch wi wi
      luklem1.1 wph wps wch luk-1 ax-mp ax-mp $.
  $}

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem2 $p |- ( ( ph -> -. ps ) ->
                ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $=
    wph wps wn wi wps wph wch wi wi wph wch wi wth wi wps wth wi wi wph wps wn
    wi wps wn wch wi wph wch wi wi wps wph wch wi wi wph wps wn wch luk-1 wps
    wps wn wch wi wi wps wn wch wi wph wch wi wi wps wph wch wi wi wi wps wch
    luk-3 wps wps wn wch wi wph wch wi luk-1 ax-mp luklem1 wps wph wch wi wth
    luk-1 luklem1 $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $=
    wph wph wn wth wn wi wph wn wps wi wch wi wth wch wi wi wph wth wn luk-3
    wph wn wth wps wch luklem2 luklem1 $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $=
    wph wn wph wi wph wi wps wi wps wn wps wi wps wps wn wph wn wph wi wph wi
    wi wph wn wph wi wph wi wps wi wps wn wps wi wi wph wn wph wi wph wi wn wph
    wn wph wi wph wi wi wph wn wph wi wph wi wi wps wn wph wn wph wi wph wi wi
    wph wn wph wi wph wi luk-2 wph wn wph wi wph wi wph wn wph wi wph wi wn wph
    wn wph wi wph wi wi wph wn wph wi wph wi wi wps wn wph wn wph wi wph wi wi
    wi wph luk-2 wph wn wph wi wph wi wph wn wph wi wph wi wph wn wph wi wph wi
    wps wn luklem3 ax-mp ax-mp wps wn wph wn wph wi wph wi wps luk-1 ax-mp wps
    luk-2 luklem1 $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem5 $p |- ( ph -> ( ps -> ph ) ) $=
    wph wph wn wph wi wph wi wps wph wi wi wps wph wi wph wph wph wps luklem3
    wph wps wph wi luklem4 luklem1 $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    wph wph wps wi wi wph wps wi wps wi wph wps wi wi wph wps wi wph wph wps wi
    wps luk-1 wph wps wi wn wph wps wi wi wph wps wi wi wph wps wi wps wi wph
    wps wi wi wph wps wi wi wi wph wps wi wps wi wph wps wi wi wph wps wi wi
    wph wps wi wps wi wph wps wi wi wph wps wi wn wph wps wi wi wi wph wps wi
    wn wph wps wi wi wph wps wi wi wph wps wi wps wi wph wps wi wi wph wps wi
    wi wi wph wps wi wn wph wps wi wps wi wi wph wps wi wps wi wph wps wi wi
    wph wps wi wn wph wps wi wi wi wph wps wi wn wps wn wph wps wi wn wi wph
    wps wi wps wi wph wps wi wn wps wn luklem5 wps wn wph wps wi wn wi wps wn
    wps wi wps wi wph wps wi wps wi wi wph wps wi wps wi wps wn wph wps wi wps
    wps luklem2 wps wph wps wi wps wi luklem4 luklem1 luklem1 wph wps wi wn wph
    wps wi wps wi wph wps wi luk-1 ax-mp wph wps wi wps wi wph wps wi wi wph
    wps wi wn wph wps wi wi wph wps wi luk-1 ax-mp wph wps wi wph wps wi wps wi
    wph wps wi wi wph wps wi wi luklem4 ax-mp luklem1 $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wch wi wch wi wph wch wi wi wps wph wch wi wi wph wps
    wch wi wch luk-1 wps wps wch wi wch wi wi wps wch wi wch wi wph wch wi wi
    wps wph wch wi wi wi wps wps wch wi wps wch wi wch wi wi wps wch wi wch wi
    wps wps wch wi wps wi wps wch wi wps wch wi wch wi wi wps wps wch wi
    luklem5 wps wch wi wps wch luk-1 luklem1 wps wch wi wch luklem6 luklem1 wps
    wps wch wi wch wi wph wch wi luk-1 ax-mp luklem1 $.

  $( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $=
    wch wph wi wph wps wi wch wps wi wi wi wph wps wi wch wph wi wch wps wi wi
    wi wch wph wps luk-1 wch wph wi wph wps wi wch wps wi luklem7 ax-mp $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax1 $p |- ( ph -> ( ps -> ph ) ) $=
    wph wps luklem5 $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $=
    wph wps wch wi wi wps wph wch wi wi wph wps wi wph wch wi wi wph wps wch
    luklem7 wps wph wch wi wi wph wps wi wph wph wch wi wi wi wph wps wi wph
    wch wi wi wps wph wch wi wph luklem8 wph wph wch wi wi wph wch wi wi wph
    wps wi wph wph wch wi wi wi wph wps wi wph wch wi wi wi wph wch luklem6 wph
    wph wch wi wi wph wch wi wph wps wi luklem8 ax-mp luklem1 luklem1 $.

  $( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $=
    wph wn wps wn wi wph wn wph wi wph wi wps wph wi wi wps wph wi wph wn wps
    wph wph luklem2 wph wps wph wi luklem4 luklem1 $.


