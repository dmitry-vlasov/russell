
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_standard_axioms_from_the_Lukasiewicz_axioms.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Derive Nicod's axiom from the standard axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

Prove Nicod's axiom and implication and negation definitions.

$)

  $( Define implication in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ( ps -/\ ps ) ) <-> ( ph -> ps ) ) ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     a definition ($a statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-dfim $p |- ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -> ps ) ) -/\
                   ( ( ( ph -/\ ( ps -/\ ps ) ) -/\ ( ph -/\ ( ps -/\ ps ) ) )
                          -/\
                     ( ( ph -> ps ) -/\ ( ph -> ps ) ) ) ) $=
    wph wps wps wnan wnan wph wps wi wb wph wps wps wnan wnan wph wps wi wnan
    wph wps wps wnan wnan wph wps wps wnan wnan wnan wph wps wi wph wps wi wnan
    wnan wnan wph wps wi wph wps wps wnan wnan wph wps nanim bicomi wph wps wps
    wnan wnan wph wps wi nanbi mpbi $.

  $( Define negation in terms of 'nand'.  Analogous to
     ` ( ( ph -/\ ph ) <-> -. ph ) ` .  In a pure (standalone) treatment of
     Nicod's axiom, this theorem would be changed to a definition ($a
     statement).  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-dfneg $p |- ( ( ( ph -/\ ph ) -/\ -. ph ) -/\
                    ( ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) -/\
                      ( -. ph -/\ -. ph ) ) ) $=
    wph wph wnan wph wn wb wph wph wnan wph wn wnan wph wph wnan wph wph wnan
    wnan wph wn wph wn wnan wnan wnan wph wn wph wph wnan wph nannot bicomi wph
    wph wnan wph wn nanbi mpbi $.

  ${
    $( Minor premise. $)
    nic-jmin $e |- ph $.
    $( Major premise. $)
    nic-jmaj $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Derive Nicod's rule of modus ponens using 'nand', from the standard
       one.  Although the major and minor premise together also imply ` ch ` ,
       this form is necessary for useful derivations from ~ nic-ax .  In a pure
       (standalone) treatment of Nicod's axiom, this theorem would be changed
       to an axiom ($a statement).  (Contributed by Jeff Hoffman,
       19-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-mp $p |- ps $=
      wph wps nic-jmin wph wch wps wph wch wps wnan wnan wph wch wps wa wi
      nic-jmaj wph wps wch nannan mpbi simprd ax-mp $.

    $( A direct proof of ~ nic-mp .  (Contributed by NM, 30-Dec-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-mpALT $p |- ps $=
      wph wps nic-jmin wph wch wps wph wch wps wa wi wph wch wps wa wn wa wn
      wph wch wps wnan wnan wph wch wps wa wn wa wn nic-jmaj wph wch wps wnan
      wnan wph wch wps wnan wa wph wch wps wa wn wa wph wch wps wnan df-nan wch
      wps wnan wch wps wa wn wph wch wps df-nan anbi2i xchbinx mpbi wph wch wps
      wa iman mpbir simprd ax-mp $.
  $}

  $( Nicod's axiom derived from the standard ones.  See _Intro. to Math.
     Phil._ by B. Russell, p. 152.  Like ~ meredith , the usual axioms can be
     derived from this and vice versa.  Unlike ~ meredith , Nicod uses a
     different connective ('nand'), so another form of modus ponens must be
     used in proofs, e.g. ` { ` ~ nic-ax , ~ nic-mp ` } ` is equivalent to
     ` { ` ~ luk-1 , ~ luk-2 , ~ luk-3 , ~ ax-mp ` } ` .  In a pure
     (standalone) treatment of Nicod's axiom, this theorem would be changed to
     an axiom ($a statement).  (Contributed by Jeff Hoffman, 19-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-ax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\
                   ( ( ta -/\ ( ta -/\ ta ) ) -/\
                     ( ( th -/\ ch ) -/\
                       ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    wph wch wps wnan wnan wta wta wta wnan wnan wth wch wnan wph wth wnan wph
    wth wnan wnan wnan wnan wnan wph wch wps wnan wnan wta wta wta wnan wnan
    wth wch wnan wph wth wnan wph wth wnan wnan wnan wa wi wph wch wps wnan
    wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan
    wph wch wps wnan wnan wph wch wps wa wi wph wch wi wth wch wnan wph wth
    wnan wph wth wnan wnan wnan wph wch wps wnan wnan wph wch wps wa wi wph wps
    wch nannan biimpi wch wps wa wch wph wch wps simpl imim2i wph wch wi wth
    wch wnan wph wth wnan wi wth wch wnan wph wth wnan wph wth wnan wnan wnan
    wth wch wnan wth wch wn wi wph wch wi wph wth wnan wth wch wn wi wth wch wa
    wn wth wch wnan wth wch imnan wth wch df-nan bitr4i wph wch wi wth wch wn
    wi wth wph wn wi wph wth wnan wph wch wi wch wn wph wn wth wph wch con3
    imim2d wph wth wn wi wph wth wa wn wth wph wn wi wph wth wnan wph wth imnan
    wth wph con2b wph wth df-nan 3bitr4ri syl6ibr syl5bir wth wch wnan wph wth
    wnan nanim sylib 3syl wta wta wta wnan wnan wta wta wta wa wi wta wta wta
    wa wta pm4.24 biimpi wta wta wta nannan mpbir jctil wph wch wps wnan wnan
    wth wch wnan wph wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan
    nannan mpbir $.

  $( A direct proof of ~ nic-ax .  (Contributed by NM, 11-Dec-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-axALT $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    wph wch wps wnan wnan wta wta wta wnan wnan wth wch wnan wph wth wnan wph
    wth wnan wnan wnan wnan wnan wph wch wps wnan wnan wta wta wta wnan wnan
    wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wa wn wph wch wps
    wnan wnan wta wta wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan
    wnan wnan wa wn wph wch wps wa wi wta wta wta wa wi wth wch wn wi wth wph
    wn wi wi wa wi wph wch wps wa wi wth wch wn wi wth wph wn wi wi wta wta wta
    wa wi wph wch wps wa wi wph wch wi wth wch wn wi wth wph wn wi wi wch wps
    wa wch wph wch wps simpl imim2i wph wch wi wch wn wph wn wth wph wch con3
    imim2d syl wta wta wa wta wta anidm biimpri jctil wph wch wps wnan wnan wta
    wta wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wa
    wn wph wch wps wa wi wta wta wta wa wi wth wch wn wi wth wph wn wi wi wa wn
    wa wn wph wch wps wa wi wta wta wta wa wi wth wch wn wi wth wph wn wi wi wa
    wi wph wch wps wnan wnan wta wta wta wnan wnan wth wch wnan wph wth wnan
    wph wth wnan wnan wnan wnan wa wph wch wps wa wi wta wta wta wa wi wth wch
    wn wi wth wph wn wi wi wa wn wa wph wch wps wnan wnan wph wch wps wa wi wta
    wta wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wta
    wta wta wa wi wth wch wn wi wth wph wn wi wi wa wn wph wch wps wnan wa wn
    wph wch wps wa wn wa wn wph wch wps wnan wnan wph wch wps wa wi wph wch wps
    wnan wa wph wch wps wa wn wa wch wps wnan wch wps wa wn wph wch wps df-nan
    anbi2i notbii wph wch wps wnan df-nan wph wch wps wa iman 3bitr4i wta wta
    wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wta wta
    wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wa wta wta
    wta wa wi wth wch wn wi wth wph wn wi wi wa wta wta wta wnan wnan wth wch
    wnan wph wth wnan wph wth wnan wnan wnan df-nan wta wta wta wnan wnan wta
    wta wta wa wi wth wch wnan wph wth wnan wph wth wnan wnan wnan wth wch wn
    wi wth wph wn wi wi wta wta wta wnan wa wn wta wta wta wa wn wa wn wta wta
    wta wnan wnan wta wta wta wa wi wta wta wta wnan wa wta wta wta wa wn wa
    wta wta wnan wta wta wa wn wta wta wta df-nan anbi2i notbii wta wta wta
    wnan df-nan wta wta wta wa iman 3bitr4i wth wch wnan wph wth wnan wph wth
    wnan wnan wa wn wth wch wn wi wth wph wn wi wn wa wn wth wch wnan wph wth
    wnan wph wth wnan wnan wnan wth wch wn wi wth wph wn wi wi wth wch wnan wph
    wth wnan wph wth wnan wnan wa wth wch wn wi wth wph wn wi wn wa wth wch
    wnan wth wch wn wi wph wth wnan wph wth wnan wnan wth wph wn wi wn wth wch
    wnan wth wch wa wn wth wch wn wi wth wch df-nan wth wch imnan bitr4i wph
    wth wnan wph wth wnan wnan wph wth wnan wph wth wnan wa wth wph wn wi wph
    wth wnan wph wth wnan df-nan wph wth wnan wph wth wnan wa wph wth wnan wph
    wth wa wn wth wph wn wi wph wth wnan anidm wph wth df-nan wph wth wa wn wph
    wth wn wi wth wph wn wi wph wth imnan wph wth con2b bitr3i 3bitri xchbinx
    anbi12i notbii wth wch wnan wph wth wnan wph wth wnan wnan df-nan wth wch
    wn wi wth wph wn wi iman 3bitr4i anbi12i xchbinx anbi12i notbii wph wch wps
    wa wi wta wta wta wa wi wth wch wn wi wth wph wn wi wi wa iman bitr4i mpbir
    wph wch wps wnan wnan wta wta wta wnan wnan wth wch wnan wph wth wnan wph
    wth wnan wnan wnan wnan df-nan mpbir $.



