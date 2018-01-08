
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_Nicod_s_axiom_from_the_standard_axioms.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-imp.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
      wph wch wps wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan
      wta wta wta wnan wnan nic-imp.1 wph wps wch wth wta nic-ax nic-mp $.
  $}

  $( Lemma for ~ nic-id .  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\
                 ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\
                   ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $=
    wph wch wps wnan wnan wph wch wnan wph wph wnan wph wph wnan wnan wnan wta
    wta wta wnan wnan wth wph wps wch wph wta nic-ax nic-imp $.

  ${
    nic-idlem2.1 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
    $( Lemma for ~ nic-id .  Inference used by ~ nic-id .  (Contributed by Jeff
       Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $=
      wet wph wch wps wnan wnan wth wnan wnan wth wta wta wta wnan wnan wnan
      wet wnan wth wta wta wta wnan wnan wnan wet wnan nic-idlem2.1 wth wta wta
      wta wnan wnan wnan wph wch wps wnan wnan wth wnan wph wch wps wnan wnan
      wth wnan wet wph wch wps wnan wnan wph wch wnan wph wph wnan wph wph wnan
      wnan wnan wta wta wta wnan wnan wth wph wps wch wph wta nic-ax nic-imp
      nic-imp nic-mp $.
  $}

  $( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $=
    wph wps wnan wps wph wnan wps wph wnan wnan wnan wch wch wch wnan wnan wnan
    wps wps wps wnan wnan wnan wta wta wta wnan wnan wch wch wch wnan wnan wth
    wth wth wph wps wnan wps wph wnan wps wph wnan wnan wnan wch wps wps wps
    wnan wnan wps wps wps wph wth nic-ax nic-idlem2 wph wps wnan wps wph wnan
    wps wph wnan wnan wnan wch wch wnan wch wph wps wnan wps wph wnan wps wph
    wnan wnan wnan wch wch wch wnan wnan wnan wps wch wch wch wnan wnan wta wta
    wta wnan wnan wnan wph wps wnan wps wph wnan wps wph wnan wch wch wch wnan
    wnan wta nic-idlem1 nic-idlem2 nic-mp $.

  $( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $=
    wph wph wph wnan wnan wth wph wnan wph wth wnan wph wth wnan wnan wnan wta
    wta wta wnan wnan wph nic-id wph wph wph wth wta nic-ax nic-mp $.

  ${
    nic-isw1.1 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-isw1 $p |- ( ph -/\ th ) $=
      wth wph wnan wph wth wnan wph wth wnan nic-isw1.1 wph wth nic-swap nic-mp
      $.
  $}

  ${
    nic-isw2.1 $e |- ( ps -/\ ( th -/\ ph ) ) $.
    $( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $=
      wps wph wth wnan wps wth wph wnan wnan wph wth wnan wps wnan wph wth wnan
      wps wnan nic-isw2.1 wph wth wnan wth wph wnan wth wph wnan wps wth wph
      nic-swap nic-imp nic-mp nic-isw1 $.
  $}

  ${
    nic-iimp1.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    nic-iimp1.2 $e |- ( th -/\ ch ) $.
    $( Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-iimp1 $p |- ( th -/\ ph ) $=
      wth wph wth wch wnan wph wth wnan wph wth wnan nic-iimp1.2 wph wps wch
      wth nic-iimp1.1 nic-imp nic-mp nic-isw1 $.
  $}

  ${
    nic-iimp2.1 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
    nic-iimp2.2 $e |- ( th -/\ ph ) $.
    $( Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $=
      wch wch wnan wps wph wth wch wch wnan wph wps wnan nic-iimp2.1 nic-isw1
      nic-iimp2.2 nic-iimp1 $.
  $}

  ${
    nic-idel.1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
    $( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      wch wch wnan wch wnan wph wch wch wnan wnan wph wch wch wnan wnan wch wch
      wnan wch wch nic-id nic-isw1 wph wps wch wch wch wnan nic-idel.1 nic-imp
      nic-mp $.
  $}

  ${
    nic-ich.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    nic-ich.2 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
    $( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $=
      wch wch wnan wps wnan wph wch wch wnan wnan wph wch wch wnan wnan wch wch
      wnan wps nic-ich.2 nic-isw1 wph wps wps wch wch wnan nic-ich.1 nic-imp
      nic-mp $.
  $}

  ${
    nic-idbl.1 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
    $( Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $=
      wps wps wnan wph wps wnan wph wph wnan wph wps wps wps nic-idbl.1 nic-imp
      wph wps wps wph nic-idbl.1 nic-imp nic-ich $.
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form. ~ nic-bi1 and ~ nic-bi2 are used
     to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $=
    wta wta nic-swap $.

  ${
    $( 'Biconditional' premise. $)
    nic-bi1.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract one side of an implication from a definition.
       (Contributed by Jeff Hoffman, 18-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $=
      wph wph wps wps wph wph wph wps wnan wps wps wnan wph wph wnan wph
      nic-bi1.1 wph nic-id nic-iimp1 nic-isw2 nic-idel $.
  $}

  ${
    $( 'Biconditional' premise.  $)
    nic-bi2.1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph )
         -/\ ( ps -/\ ps ) ) ) $.
    $( Inference to extract the other side of an implication from a
       'biconditional' definition.  (Contributed by Jeff Hoffman,
       18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $=
      wps wps wph wph wps wnan wph wph wnan wps wps wnan wps wps wps wnan wph
      wps wnan wph wph wnan nic-bi2.1 nic-isw2 wps nic-id nic-iimp1 nic-idel $.
  $}

$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( Minor premise. $)
    nic-smin $e |- ph $.
    $( Major premise. $)
    nic-smaj $e |- ( ph -> ps ) $.
    $( Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    nic-stdmp $p |- ps $=
      wph wps wps nic-smin wph wps wi wph wps wps wnan wnan wph wps wps wnan
      wnan nic-smaj wph wps wps wnan wnan wph wps wi wph wps nic-dfim nic-bi2
      nic-mp nic-mp $.
  $}

  $( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $=
    wph wps wi wps wch wi wph wch wi wi wps wch wi wph wch wi wi wnan wnan wph
    wps wi wps wch wi wph wch wi wi wi wph wps wi wps wch wi wph wch wi wi wi
    wph wps wi wph wps wps wnan wnan wps wch wi wph wch wi wi wph wps wps wnan
    wnan wph wps wi wph wps nic-dfim nic-bi2 wph wps wps wnan wnan wps wch wi
    wph wch wi wph wch wi wnan wnan wps wch wi wph wch wi wi wph wps wps wnan
    wnan wch wch wnan wps wnan wph wch wch wnan wnan wph wch wch wnan wnan wnan
    wnan wps wch wi wph wch wi wph wch wi wnan wnan wph wps wps wnan wnan wta
    wta wta wnan wnan wch wch wnan wps wnan wph wch wch wnan wnan wph wch wch
    wnan wnan wnan wnan wch wch wnan wps wnan wph wch wch wnan wnan wph wch wch
    wnan wnan wnan wnan wph wps wps wnan wnan wta wta wta wnan wnan wph wps wps
    wch wch wnan wta nic-ax nic-isw2 nic-idel wch wch wnan wps wnan wph wch wch
    wnan wnan wph wch wch wnan wnan wnan wnan wph wch wi wph wch wi wnan wch
    wch wnan wps wnan wnan wps wch wi wph wch wi wph wch wi wnan wnan wph wch
    wi wph wch wi wnan wph wch wch wnan wnan wph wch wch wnan wnan wnan wph wch
    wch wnan wnan wph wch wch wnan wnan wnan wch wch wnan wps wnan wph wch wch
    wnan wnan wph wch wi wph wch wch wnan wnan wph wch wi wph wch nic-dfim
    nic-bi1 nic-idbl nic-imp wps wch wi wch wch wnan wps wnan wch wch wnan wps
    wnan wph wch wi wph wch wi wnan wps wch wi wps wch wch wnan wnan wch wch
    wnan wps wnan wps wch wch wnan wnan wps wch wi wps wch nic-dfim nic-bi2 wch
    wch wnan wps nic-swap nic-ich nic-imp nic-ich nic-ich wps wch wi wph wch wi
    wph wch wi wnan wnan wps wch wi wph wch wi wi wps wch wi wph wch wi
    nic-dfim nic-bi1 nic-ich nic-ich wph wps wi wps wch wi wph wch wi wi wps
    wch wi wph wch wi wi wnan wnan wph wps wi wps wch wi wph wch wi wi wi wph
    wps wi wps wch wi wph wch wi wi nic-dfim nic-bi1 nic-mp $.

  $( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $=
    wph wn wph wi wph wph wnan wnan wph wn wph wi wph wi wph wn wph wi wph wi
    wph wn wph wi wph wph wnan wph wn wph wi wph wn wph wph wnan wnan wph wn
    wph wph wnan wnan wph wph wnan wph wn wph wph wnan wnan wph wn wph wi wph
    wn wph nic-dfim nic-bi2 wph wn wph wph wnan wph wph wnan wph wph wnan wph
    wn wnan wph wn wph wn wnan wph wph wnan wph wph wnan wnan wph wph wnan wph
    nic-dfneg wph wph wnan nic-id nic-iimp1 nic-isw2 nic-iimp1 nic-isw1 wph wn
    wph wi wph wph wnan wnan wph wn wph wi wph wi wph wn wph wi wph nic-dfim
    nic-bi1 nic-mp $.

  $( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $=
    wph wph wn wps wi wph wn wps wi wnan wnan wph wph wn wps wi wi wph wph wn
    wps wi wi wph wn wps wps wnan wph wn wps wi wph wph wn wps wps wnan wnan
    wph wn wps wi wph wn wps nic-dfim nic-bi1 wph wn wph wph wnan wph wph wnan
    wph wph wph wnan wph wn wph nic-dfneg nic-bi2 wph nic-id nic-iimp1
    nic-iimp2 wph wph wn wps wi wph wn wps wi wnan wnan wph wph wn wps wi wi
    wph wph wn wps wi nic-dfim nic-bi1 nic-mp $.


