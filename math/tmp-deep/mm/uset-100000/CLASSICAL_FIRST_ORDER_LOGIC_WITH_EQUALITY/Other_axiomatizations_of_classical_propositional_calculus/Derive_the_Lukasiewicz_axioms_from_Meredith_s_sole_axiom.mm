
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the Lukasiewicz axioms from Meredith's sole axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Carew Meredith's sole axiom for propositional calculus.  This amazing
     formula is thought to be the shortest possible single axiom for
     propositional calculus with inference rule ~ ax-mp , where negation and
     implication are primitive.  Here we prove Meredith's axiom from ~ ax-1 ,
     ~ ax-2 , and ~ ax-3 .  Then from it we derive the Lukasiewicz axioms
     ~ luk-1 , ~ luk-2 , and ~ luk-3 .  Using these we finally re-derive our
     axioms as ~ ax1 , ~ ax2 , and ~ ax3 , thus proving the equivalence of all
     three systems.  C. A. Meredith, "Single Axioms for the Systems (C,N),
     (C,O) and (A,N) of the Two-Valued Propositional Calculus," _The Journal of
     Computing Systems_ vol. 1 (1953), pp. 155-164.  Meredith claimed to be
     close to a proof that this axiom is the shortest possible, but the proof
     was apparently never completed.

     An obscure Irish lecturer, Meredith (1904-1976) became enamored with logic
     somewhat late in life after attending talks by Lukasiewicz and produced
     many remarkable results such as this axiom.  From his obituary:  "He did
     logic whenever time and opportunity presented themselves, and he did it on
     whatever materials came to hand: in a pub, his favored pint of porter
     within reach, he would use the inside of cigarette packs to write proofs
     for logical colleagues."  (Contributed by NM, 14-Dec-2002.)  (Proof
     shortened by Andrew Salmon, 25-Jul-2011.)  (Proof shortened by Wolf
     Lammen, 28-May-2013.) $)
  meredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    wph wps wi wch wn wth wn wi wi wch wi wta wta wph wi wth wph wi wi wph wps
    wi wch wn wth wn wi wi wch wi wn wth wph wi wta wph wi wth wph wps wi wch
    wn wth wn wi wi wch wi wn wph wth wph wph wps wi wch wn wth wn wi wi wch wi
    wph wps wi wch wn wth wn wi wi wph wn wth wch wph wn wph wps wi wch wn wth
    wn wi wth wch wi wph wps pm2.21 wch wth ax-3 imim12i com13 con1d com12 a1d
    wta wth wta wph wta wth ax-1 imim1d ja $.

  $( Alias for ~ meredith which "verify markup *" will match to
     ~ ax-meredith .  (Contributed by NM, 21-Aug-2017.)
     (New usage is discouraged.) $)
  axmeredith $p |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    wph wps wch wth wta meredith $.

  $( Theorem ~ meredith restated as an axiom.  This will allow us to ensure
     that the rederivation of ~ ax1 , ~ ax2 , and ~ ax3 below depend only on
     Meredith's sole axiom and not accidentally on a previous theorem above.
     Outside of this section, we will not make use of this axiom.  (Contributed
     by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax-meredith $a |- ( ( ( ( ( ph -> ps ) -> ( -. ch -> -. th ) ) -> ch ) ->
       ta ) -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $.

  $( Step 3 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (The step numbers refer to Meredith's original paper.)  (Contributed by
     NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem1 $p |- ( ( ( ch -> ( -. ph -> ps ) ) -> ta ) -> ( ph -> ta ) ) $=
    wta wph wn wi wph wn wps wi wn wph wn wi wi wph wn wps wi wi wch wph wn wps
    wi wi wi wch wph wn wps wi wi wta wi wph wta wi wi wph wn wps wi wta wn wch
    wn wi wn wph wn wps wi wn wn wi wi wta wn wch wn wi wi wta wi wta wph wn wi
    wph wn wps wi wn wph wn wi wi wi wta wph wn wi wph wn wps wi wn wph wn wi
    wi wph wn wps wi wi wch wph wn wps wi wi wi wph wn wps wta wn wch wn wi wph
    wn wps wi wn wta ax-meredith wph wn wps wi wta wn wch wn wi wn wph wn wps
    wi wn wn wi wta wch wta wph wn wi wph wn wps wi wn wph wn wi wi ax-meredith
    ax-mp wta wph wn wph wn wps wi wph wch wph wn wps wi wi ax-meredith ax-mp
    $.

  $( Step 4 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem2 $p |- ( ( ( ph -> ph ) -> ch ) -> ( th -> ch ) ) $=
    wch wch wi wph wn wth wn wi wi wph wi wph wph wi wi wph wph wi wch wi wth
    wch wi wi wph wth wn wch wch wi wph merlem1 wch wch wph wth wph wph wi
    ax-meredith ax-mp $.

  $( Step 7 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem3 $p |- ( ( ( ps -> ch ) -> ph ) -> ( ch -> ph ) ) $=
    wph wph wi wch wn wch wn wi wi wch wi wps wch wi wi wps wch wi wph wi wch
    wph wi wi wch wph wi wps wn wps wn wi wi wps wi wph wph wi wch wn wch wn wi
    wi wi wph wph wi wch wn wch wn wi wi wch wi wps wch wi wi wch wn wch wn wi
    wch wn wch wn wi wi wph wph wi wch wn wch wn wi wi wi wch wph wi wps wn wps
    wn wi wi wps wi wph wph wi wch wn wch wn wi wi wi wch wn wch wn wch wn wi
    wph wph wi merlem2 wch wn wch wn wi wph wph wi wch wn wch wn wi wi wch wph
    wi wps wn wps wn wi wi wps wi merlem2 ax-mp wch wph wps wps wph wph wi wch
    wn wch wn wi wi ax-meredith ax-mp wph wph wch wch wps wch wi ax-meredith
    ax-mp $.

  $( Step 8 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem4 $p |- ( ta -> ( ( ta -> ph ) -> ( th -> ph ) ) ) $=
    wph wph wi wth wn wth wn wi wi wth wi wta wi wta wph wi wth wph wi wi wi
    wta wta wph wi wth wph wi wi wi wph wph wth wth wta ax-meredith wta wph wi
    wth wph wi wi wph wph wi wth wn wth wn wi wi wth wi wta merlem3 ax-mp $.

  $( Step 11 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem5 $p |- ( ( ph -> ps ) -> ( -. -. ph -> ps ) ) $=
    wps wps wi wps wn wps wn wi wi wps wi wps wi wps wps wi wps wps wi wi wi
    wph wps wi wph wn wn wps wi wi wps wps wps wps wps ax-meredith wps wps wi
    wps wn wph wn wn wn wi wi wps wi wph wi wph wps wi wph wn wn wps wi wi wi
    wps wps wi wps wn wps wn wi wi wps wi wps wi wps wps wi wps wps wi wi wi
    wph wps wi wph wn wn wps wi wi wi wps wps wps wph wn wn wph ax-meredith wph
    wps wi wph wn wn wps wi wi wps wps wi wps wn wps wn wi wi wps wi wps wi wps
    wps wi wps wps wi wi wi wn wi wph wn wps wps wi wps wn wps wn wi wi wps wi
    wps wi wps wps wi wps wps wi wi wi wn wi wi wph wi wps wps wi wps wn wph wn
    wn wn wi wi wps wi wph wi wi wps wps wi wps wn wph wn wn wn wi wi wps wi
    wph wi wph wps wi wph wn wn wps wi wi wi wps wps wi wps wn wps wn wi wi wps
    wi wps wi wps wps wi wps wps wi wi wi wph wps wi wph wn wn wps wi wi wi wi
    wph wps wi wph wn wn wps wi wi wps wps wi wps wn wps wn wi wi wps wi wps wi
    wps wps wi wps wps wi wi wi wn wi wph wn wps wps wi wps wn wps wn wi wi wps
    wi wps wi wps wps wi wps wps wi wi wi wn wi wi wph wps wi wph wn wn wps wi
    wi wps wps wi wps wn wps wn wi wi wps wi wps wi wps wps wi wps wps wi wi wi
    wn wi wph wn wps wps wi wps wn wps wn wi wi wps wi wps wi wps wps wi wps
    wps wi wi wi wn wi wi wph wi wps wps wi wps wn wph wn wn wn wi wi wps wi
    wph wi wi wph wn wps wph wps wi wps wps wi wps wn wps wn wi wi wps wi wps
    wi wps wps wi wps wps wi wi wi wn merlem1 wph wps wps wi wps wn wph wn wn
    wn wi wi wps wi wph wps wi wph wn wn wps wi wi wps wps wi wps wn wps wn wi
    wi wps wi wps wi wps wps wi wps wps wi wi wi wn wi wph wn wps wps wi wps wn
    wps wn wi wi wps wi wps wi wps wps wi wps wps wi wi wi wn wi wi merlem4
    ax-mp wph wps wi wph wn wn wps wi wi wps wps wi wps wn wps wn wi wi wps wi
    wps wi wps wps wi wps wps wi wi wi wn wph wps wps wi wps wn wps wn wi wi
    wps wi wps wi wps wps wi wps wps wi wi wi wps wps wi wps wn wph wn wn wn wi
    wi wps wi wph wi ax-meredith ax-mp ax-mp ax-mp $.

  $( Step 12 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem6 $p |- ( ch -> ( ( ( ps -> ch ) -> ph ) -> ( th -> ph ) ) ) $=
    wps wch wi wps wch wi wph wi wth wph wi wi wi wch wps wch wi wph wi wth wph
    wi wi wi wph wth wps wch wi merlem4 wps wch wi wph wi wth wph wi wi wps wch
    merlem3 ax-mp $.

  $( Between steps 14 and 15 of Meredith's proof of Lukasiewicz axioms from his
     sole axiom.  (Contributed by NM, 22-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  merlem7 $p |- ( ph -> ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) ) $=
    wps wch wi wps wch wi wth wi wch wta wi wth wn wps wn wi wi wth wi wi wi
    wph wps wch wi wth wi wch wta wi wth wn wps wn wi wi wth wi wi wi wth wch
    wta wi wth wn wps wn wi wi wps wch wi merlem4 wps wch wi wth wi wch wta wi
    wth wn wps wn wi wi wth wi wi wph wn wi wch wn wph wn wi wi wch wi wps wch
    wi wi wps wch wi wps wch wi wth wi wch wta wi wth wn wps wn wi wi wth wi wi
    wi wph wps wch wi wth wi wch wta wi wth wn wps wn wi wi wth wi wi wi wi wch
    wta wi wth wn wps wn wi wi wth wi wps wch wi wth wi wch wta wi wth wn wps
    wn wi wi wth wi wi wph wn wi wch wn wph wn wi wi wi wps wch wi wth wi wch
    wta wi wth wn wps wn wi wi wth wi wi wph wn wi wch wn wph wn wi wi wch wi
    wps wch wi wi wph wn wps wch wi wth wi wch wta wi wth wn wps wn wi wi wth
    wi wch wn merlem6 wch wta wth wps wps wch wi wth wi wch wta wi wth wn wps
    wn wi wi wth wi wi wph wn wi wch wn wph wn wi wi ax-meredith ax-mp wps wch
    wi wth wi wch wta wi wth wn wps wn wi wi wth wi wi wph wn wch wph wps wch
    wi ax-meredith ax-mp ax-mp $.

  $( Step 15 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem8 $p |- ( ( ( ps -> ch ) -> th ) -> ( ( ( ch -> ta ) ->
                  ( -. th -> -. ps ) ) -> th ) ) $=
    wph wph wi wph wn wph wn wi wi wph wi wph wi wph wph wi wph wph wi wi wi
    wps wch wi wth wi wch wta wi wth wn wps wn wi wi wth wi wi wph wph wph wph
    wph ax-meredith wph wph wi wph wn wph wn wi wi wph wi wph wi wph wph wi wph
    wph wi wi wi wps wch wth wta merlem7 ax-mp $.

  $( Step 18 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem9 $p |- ( ( ( ph -> ps ) -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ->
                    ( et -> ( ch -> ( th -> ( ps -> ta ) ) ) ) ) $=
    wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wps wi wph wps wi wi
    wph wps wi wch wth wps wta wi wi wi wi wet wch wth wps wta wi wi wi wi wi
    wps wta wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wn wth wn
    wi wn wph wn wi wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi
    wn wth wn wi wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wi
    wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wps wi wph wps wi wi
    wth wps wta wi wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wi
    wps wta wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wn wth wn
    wi wn wph wn wi wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi
    wn wth wn wi wi wch wth wps wta wi wi wi wet wn wi wps wn wet wn wi wi wi
    wet wn wch wth wps wta wi wi wps wn merlem6 wth wps wta wi wch wth wps wta
    wi wi wi wet wn wi wps wn wet wn wi wi wch wth wps wta wi wi wi wet wn wi
    wps wn wet wn wi wi wn wth wn wi wn wph wn wi merlem8 ax-mp wps wta wch wth
    wps wta wi wi wi wet wn wi wps wn wet wn wi wi wn wth wn wi wph wch wth wps
    wta wi wi wi wet wn wi wps wn wet wn wi wi ax-meredith ax-mp wch wth wps
    wta wi wi wi wet wn wps wet wph wps wi ax-meredith ax-mp $.

  $( Step 19 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem10 $p |- ( ( ph -> ( ph -> ps ) ) -> ( th -> ( ph -> ps ) ) ) $=
    wph wph wi wph wn wph wn wi wi wph wi wph wi wph wph wi wph wph wi wi wi
    wph wph wps wi wi wth wph wps wi wi wi wph wph wph wph wph ax-meredith wph
    wps wi wph wi wph wn wth wn wi wi wph wi wph wi wph wph wps wi wi wth wph
    wps wi wi wi wi wph wph wi wph wn wph wn wi wi wph wi wph wi wph wph wi wph
    wph wi wi wi wph wph wps wi wi wth wph wps wi wi wi wi wph wps wi wph wph
    wth wph ax-meredith wph wps wi wph wi wph wn wth wn wi wi wph wi wph wph
    wph wps wi wi wth wps wph wph wi wph wn wph wn wi wi wph wi wph wi wph wph
    wi wph wph wi wi wi merlem9 ax-mp ax-mp $.

  $( Step 20 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem11 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $=
    wph wph wi wph wn wph wn wi wi wph wi wph wi wph wph wi wph wph wi wi wi
    wph wph wps wi wi wph wps wi wi wph wph wph wph wph ax-meredith wph wph wps
    wi wi wph wph wps wi wi wph wps wi wi wi wph wph wi wph wn wph wn wi wi wph
    wi wph wi wph wph wi wph wph wi wi wi wph wph wps wi wi wph wps wi wi wi
    wph wps wph wph wps wi wi merlem10 wph wph wps wi wi wph wps wi wph wph wi
    wph wn wph wn wi wi wph wi wph wi wph wph wi wph wph wi wi wi merlem10
    ax-mp ax-mp $.

  $( Step 28 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem12 $p |- ( ( ( th -> ( -. -. ch -> ch ) ) -> ph ) -> ph ) $=
    wth wch wn wn wch wi wi wph wi wth wch wn wn wch wi wi wph wi wph wi wi wth
    wch wn wn wch wi wi wph wi wph wi wth wch wn wn wch wi wi wth wch wn wn wch
    wi wi wph wi wth wch wn wn wch wi wi wph wi wph wi wi wch wch wi wch wn wn
    wch wi wi wth wch wn wn wch wi wi wch wch merlem5 wch wch wn wn wch wi wth
    merlem2 ax-mp wph wth wch wn wn wch wi wi wph wi wth wch wn wn wch wi wi
    merlem4 ax-mp wth wch wn wn wch wi wi wph wi wph merlem11 ax-mp $.

  $( Step 35 of Meredith's proof of Lukasiewicz axioms from his sole axiom.
     (Contributed by NM, 14-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  merlem13 $p |- ( ( ph -> ps ) ->
              ( ( ( th -> ( -. -. ch -> ch ) ) -> -. -. ph ) -> ps ) ) $=
    wps wps wi wph wn wth wch wn wn wch wi wi wph wn wn wi wn wi wi wph wi wph
    wi wph wps wi wth wch wn wn wch wi wi wph wn wn wi wps wi wi wps wps wi wph
    wn wth wch wn wn wch wi wi wph wn wn wi wn wi wi wph wi wps wps wi wph wn
    wth wch wn wn wch wi wi wph wn wn wi wn wi wi wph wi wph wi wi wps wps wi
    wph wn wth wch wn wn wch wi wi wph wn wn wi wn wi wi wph wi wph wi wph wn
    wth wch wn wn wch wi wi wph wn wn wi wn wi wps wps wi wph wn wth wch wn wn
    wch wi wi wph wn wn wi wn wi wi wph wi wps wps wi wph wn wth wch wn wn wch
    wi wi wph wn wn wi wn wi wi wph wi wph wi wi wth wch wn wn wch wi wi wth
    wch wn wn wch wi wi wph wn wn wi wn wi wth wch wn wn wch wi wi wph wn wn wi
    wn wi wph wn wth wch wn wn wch wi wi wph wn wn wi wn wi wth wch wn wn wch
    wi wi wph wn wn wi wn wch wth merlem12 wth wch wn wn wch wi wi wph wn wn wi
    wn wps wi wth wch wn wn wch wi wi wph wn wn wi wn wn wph wn wn wi wi wth
    wch wn wn wch wi wi wph wn wn wi wn wi wth wch wn wn wch wi wi wth wch wn
    wn wch wi wi wph wn wn wi wn wi wi wth wch wn wn wch wi wi wth wch wn wn
    wch wi wi wph wn wn wi wn wi wth wch wn wn wch wi wi wph wn wn wi wn wi wph
    wn wth wch wn wn wch wi wi wph wn wn wi wn wi wi wth wch wn wn wch wi wi
    wph wn wn wi wn wn wph wn wn wi wth wch wn wn wch wi wi wph wn wn wi wn wps
    wi wth wch wn wn wch wi wi wph wn wn wi wn wn wph wn wn wi wi wth wch wn wn
    wch wi wi wph wn wn wi wn wi wth wch wn wn wch wi wi wth wch wn wn wch wi
    wi wph wn wn wi wn wi wi wth wch wn wn wch wi wi wph wn wn wi wph wn wn wi
    wth wch wn wn wch wi wi wph wn wn wi wn wn wph wn wn wi wph wn wn wch wth
    merlem12 wth wch wn wn wch wi wi wph wn wn wi wph wn wn merlem5 ax-mp wth
    wch wn wn wch wi wi wph wn wn wi wn wth wch wn wn wch wi wi wph wn wn wi wn
    wps wi wth wch wn wn wch wi wi wph wn wn wi wn wn wph wn wn wi wth wch wn
    wn wch wi wi merlem6 ax-mp wth wch wn wn wch wi wi wph wn wn wi wn wps wth
    wch wn wn wch wi wi wph wn wn wi wn wph wn wth wch wn wn wch wi wi wth wch
    wn wn wch wi wi wph wn wn wi wn wi ax-meredith ax-mp ax-mp wph wps wps wi
    wph wn wth wch wn wn wch wi wi wph wn wn wi wn wi wps wps wi wph wn wth wch
    wn wn wch wi wi wph wn wn wi wn wi wi wph wi merlem6 ax-mp wps wps wi wph
    wn wth wch wn wn wch wi wi wph wn wn wi wn wi wi wph wi wph merlem11 ax-mp
    wps wps wph wth wch wn wn wch wi wi wph wn wn wi wph ax-meredith ax-mp $.

  $( 1 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wch wch wi wph wn wn wn wph wn wi wi wph wn wn wi wps wi wps wch wi wph wch
    wi wi wi wph wps wi wps wch wi wph wch wi wi wi wch wch wph wn wn wph wps
    ax-meredith wps wch wi wph wch wi wi wph wi wph wps wi wn wn wn wph wps wi
    wn wi wi wph wps wi wn wn wi wch wch wi wph wn wn wn wph wn wi wi wph wn wn
    wi wps wi wi wch wch wi wph wn wn wn wph wn wi wi wph wn wn wi wps wi wps
    wch wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi wi wph wps
    wi wch wch wi wph wn wn wn wph wn wi wi wph wn wn wi wps wi wi wps wch wi
    wph wch wi wi wph wi wph wps wi wn wn wn wph wps wi wn wi wi wph wps wi wn
    wn wi wch wch wi wph wn wn wn wph wn wi wi wph wn wn wi wps wi wi wph wps
    wph wn wch wch wi merlem13 wph wps wi wch wch wi wph wn wn wn wph wn wi wi
    wph wn wn wi wps wi wph wps wi wn wps wch wi wph wch wi wi wph wi merlem13
    ax-mp wps wch wi wph wch wi wi wph wph wps wi wn wn wph wps wi wch wch wi
    wph wn wn wn wph wn wi wi wph wn wn wi wps wi ax-meredith ax-mp ax-mp $.

  $( 2 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wph wn wph wi wph wi wi wph wn wph wi wph wi wph wph wn wph
    wi wn wi wph wn wn wph wn wph wi wn wi wi wph wn wi wph wn wi wph wn wph wi
    wph wn wph wi wph wi wi wph wph wn wph wi wn wi wph wn wn wph wn wph wi wn
    wi wi wph wn wi wph wph wn wph wi wn wi wph wn wn wph wn wph wi wn wi wi
    wph wn wi wph wn wi wi wph wph wn wph wi wn wi wph wn wn wph wn wph wi wn
    wi wi wph wn wi wph wn wi wph wph wn wph wi wn wi wph wn wn wph wn wph wi
    wn wi wi wph wph wn wph wi wn wi wph wn wn wph wn wph wi wn wi wi wph wn wi
    wph wph wn wph wi wn wi wph wn wn wph wn wph wi wn wi wi wph wn wi wph wn
    wi wi wph wph wn wph wi wn merlem5 wph wn wph wph wn wph wi wn wi wph wn wn
    wph wn wph wi wn wi wi wph wn wi wph wph wn wph wi wn wi wph wn wn wph wn
    wph wi wn wi wi merlem4 ax-mp wph wph wn wph wi wn wi wph wn wn wph wn wph
    wi wn wi wi wph wn wi wph wn merlem11 ax-mp wph wph wn wph wi wn wph wn wph
    wn wph wi wph wn ax-meredith ax-mp wph wn wph wi wph merlem11 ax-mp $.

  $( 3 of 3 axioms for propositional calculus due to Lukasiewicz, derived from
     Meredith's sole axiom.  (Contributed by NM, 14-Dec-2002.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  luk-3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wn wph wn wps wi wi wph wn wps wi wi wph wph wn wps wi wi wph wn wps
    merlem11 wph wps wph wn wph wn wps wi merlem1 ax-mp $.


