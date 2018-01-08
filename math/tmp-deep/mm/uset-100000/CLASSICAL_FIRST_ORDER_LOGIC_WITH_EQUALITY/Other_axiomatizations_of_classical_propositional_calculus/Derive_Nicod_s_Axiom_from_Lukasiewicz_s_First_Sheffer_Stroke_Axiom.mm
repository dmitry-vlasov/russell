
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_Nicod_s_axiom.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Derive Nicod's Axiom from Lukasiewicz's First Sheffer Stroke Axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( This alternative axiom for propositional calculus using the Sheffer Stroke
     was offered by Lukasiewicz in his Selected Works.  It improves on Nicod's
     axiom by reducing its number of variables by one.

     This axiom also uses ~ nic-mp for its constructions.

     Here, the axiom is proved as a substitution instance of ~ nic-ax .
     (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshef-ax1 $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( th -/\ ( th -/\ th ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    wph wps wch wth wth nic-ax $.

  $( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshefth1 $p |- ( ( ( ( ta -/\ ps ) -/\ ( ( ph -/\ ta ) -/\ ( ph
          -/\ ta ) ) ) -/\ ( th -/\ ( th -/\ th ) ) ) -/\ ( ph -/\ ( ps
          -/\ ch ) ) ) $=
    wph wps wch wnan wnan wta wta wta wnan wnan wta wps wnan wph wta wnan wph
    wta wnan wnan wnan wnan wnan wta wps wnan wph wta wnan wph wta wnan wnan
    wnan wth wth wth wnan wnan wnan wph wps wch wnan wnan wnan wta wps wnan wph
    wta wnan wph wta wnan wnan wnan wth wth wth wnan wnan wnan wph wps wch wnan
    wnan wnan wph wch wps wta lukshef-ax1 wta wps wnan wph wta wnan wph wta
    wnan wnan wnan wth wth wth wnan wnan wnan wta wta wta wnan wnan wta wps
    wnan wph wta wnan wph wta wnan wnan wnan wnan wta wta wta wnan wnan wta wps
    wnan wph wta wnan wph wta wnan wnan wnan wnan wnan wnan wph wps wch wnan
    wnan wta wta wta wnan wnan wta wps wnan wph wta wnan wph wta wnan wnan wnan
    wnan wnan wta wps wnan wph wta wnan wph wta wnan wnan wnan wth wth wth wnan
    wnan wnan wph wps wch wnan wnan wnan wta wps wnan wph wta wnan wph wta wnan
    wnan wnan wth wth wth wnan wnan wnan wph wps wch wnan wnan wnan wnan wnan
    wph wps wch wnan wnan wph wps wch wnan wnan wph wps wch wnan wnan wnan wnan
    wta wta wta wnan wnan wth wth wth wnan wnan wth wta wnan wta wth wnan wta
    wth wnan wnan wnan wnan wnan wta wps wnan wph wta wnan wph wta wnan wnan
    wnan wth wth wth wnan wnan wnan wta wta wta wnan wnan wta wps wnan wph wta
    wnan wph wta wnan wnan wnan wnan wta wta wta wnan wnan wta wps wnan wph wta
    wnan wph wta wnan wnan wnan wnan wnan wnan wta wps wnan wph wta wnan wph
    wta wnan wnan wnan wta wps wnan wph wta wnan wph wta wnan wnan wnan wta wps
    wnan wph wta wnan wph wta wnan wnan wnan wnan wnan wta wta wta wth
    lukshef-ax1 wta wta wta wnan wnan wth wta wnan wta wth wnan wta wth wnan
    wnan wnan wth wth wth wnan wnan wta wps wnan wph wta wnan wph wta wnan wnan
    wnan lukshef-ax1 nic-mp wta wps wnan wph wta wnan wph wta wnan wnan wnan
    wth wth wth wnan wnan wnan wta wta wta wnan wnan wta wps wnan wph wta wnan
    wph wta wnan wnan wnan wnan wta wta wta wnan wnan wta wps wnan wph wta wnan
    wph wta wnan wnan wnan wnan wph wps wch wnan wnan lukshef-ax1 nic-mp nic-mp
    $.

  $( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  lukshefth2 $p |- ( ( ta -/\ th ) -/\ ( ( th -/\ ta ) -/\ ( th
          -/\ ta ) ) ) $=
    wth wth wth wnan wnan wta wth wnan wth wta wnan wth wta wnan wnan wnan wta
    wta wta wnan wnan wth wth wth wth wnan wnan wnan wps wch wph wnan wnan wth
    wnan wps wch wph wnan wnan wth wnan wnan wnan wth wth wth wnan wnan wta wph
    wnan wph wta wnan wph wta wnan wnan wnan wps wch wph wnan wnan wth wth wth
    wnan wnan wth wch wnan wps wth wnan wps wth wnan wnan wnan wnan wnan wth
    wth wth wth wnan wnan wnan wps wch wph wnan wnan wth wnan wps wch wph wnan
    wnan wth wnan wnan wnan wth wth wth wnan wnan wps wph wch wth lukshef-ax1
    wps wch wph wnan wnan wth wch wnan wps wth wnan wps wth wnan wnan wnan wth
    wth wth wnan wnan wth lukshef-ax1 nic-mp wta wph wnan wph wta wnan wph wta
    wnan wnan wnan wth wth wth wnan wnan wnan wph wph wph wnan wnan wnan wth
    wth wth wth wnan wnan wnan wps wch wph wnan wnan wth wnan wps wch wph wnan
    wnan wth wnan wnan wnan wta wph wnan wph wta wnan wph wta wnan wnan wnan
    wth wth wth wnan wnan wnan wnan wth wth wth wth wnan wnan wnan wps wch wph
    wnan wnan wth wnan wps wch wph wnan wnan wth wnan wnan wnan wta wph wnan
    wph wta wnan wph wta wnan wnan wnan wth wth wth wnan wnan wnan wnan wph wph
    wph wth wta lukshefth1 wth wth wth wth wnan wnan wnan wps wch wph wnan wnan
    wth wnan wps wch wph wnan wnan wth wnan wnan wnan wph wph wph wnan wnan wph
    wps wch wph wnan wnan wth wnan wnan wth wth wth wth wnan wnan wnan wph wnan
    wth wth wth wth wnan wnan wnan wph wnan wnan wnan wnan wnan wta wph wnan
    wph wta wnan wph wta wnan wnan wnan wth wth wth wnan wnan wnan wph wph wph
    wnan wnan wnan wth wth wth wth wnan wnan wnan wps wch wph wnan wnan wth
    wnan wps wch wph wnan wnan wth wnan wnan wnan wta wph wnan wph wta wnan wph
    wta wnan wnan wnan wth wth wth wnan wnan wnan wnan wth wth wth wth wnan
    wnan wnan wps wch wph wnan wnan wth wnan wps wch wph wnan wnan wth wnan
    wnan wnan wta wph wnan wph wta wnan wph wta wnan wnan wnan wth wth wth wnan
    wnan wnan wnan wnan wnan wta wph wnan wph wta wnan wph wta wnan wnan wnan
    wth wth wth wnan wnan wnan wta wph wnan wph wta wnan wph wta wnan wnan wnan
    wth wth wth wnan wnan wnan wta wph wnan wph wta wnan wph wta wnan wnan wnan
    wth wth wth wnan wnan wnan wnan wnan wth wth wth wth wnan wnan wnan wps wch
    wph wnan wnan wth wnan wps wch wph wnan wnan wth wnan wph lukshef-ax1 wth
    wth wth wth wnan wnan wnan wps wch wph wnan wnan wth wnan wps wch wph wnan
    wnan wth wnan wnan wnan wph wps wch wph wnan wnan wth wnan wnan wth wth wth
    wth wnan wnan wnan wph wnan wth wth wth wth wnan wnan wnan wph wnan wnan
    wnan wph wph wph wnan wnan wta wph wnan wph wta wnan wph wta wnan wnan wnan
    wth wth wth wnan wnan wnan lukshef-ax1 nic-mp nic-mp nic-mp wth wth wth wta
    lukshef-ax1 nic-mp $.

  $( A rederivation of ~ nic-ax from ~ lukshef-ax1 , proving that ~ lukshef-ax1
     with ~ nic-mp can be used as a complete axiomatization of propositional
     calculus.  (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  renicax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) )
          -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $=
    wta wta wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan
    wph wch wps wnan wnan wnan wph wch wps wnan wnan wta wta wta wnan wnan wth
    wch wnan wph wth wnan wph wth wnan wnan wnan wnan wnan wph wch wps wnan
    wnan wta wta wta wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan
    wnan wnan wph wch wps wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan
    wnan wta wta wta wnan wnan wnan wnan wta wta wta wnan wnan wth wch wnan wph
    wth wnan wph wth wnan wnan wnan wnan wph wch wps wnan wnan wnan wta wta wta
    wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wph wch wps
    wnan wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wta wta wta
    wnan wnan wnan wph wch wps wnan wnan wnan wph wch wps wnan wnan wth wch
    wnan wph wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan wnan wnan
    wph wch wps wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wta
    wta wta wnan wnan wnan wnan wph wch wps wta wth lukshefth1 wph wch wps wnan
    wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan
    wnan lukshefth2 nic-mp wta wta wta wnan wnan wth wch wnan wph wth wnan wph
    wth wnan wnan wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan
    wta wta wta wnan wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan
    wta wta wta wnan wnan wnan wnan wnan wph wch wps wnan wnan wth wch wnan wph
    wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan wnan wnan wta wta wta
    wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wph wch wps
    wnan wnan wnan wta wta wta wnan wnan wth wch wnan wph wth wnan wph wth wnan
    wnan wnan wnan wph wch wps wnan wnan wnan wnan wnan wph wch wps wnan wnan
    wph wch wps wnan wnan wph wch wps wnan wnan wnan wnan wth wch wnan wph wth
    wnan wph wth wnan wnan wnan wta wta wta wnan wnan lukshefth2 wta wta wta
    wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan wth wch
    wnan wph wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan wnan wth wch
    wnan wph wth wnan wph wth wnan wnan wnan wta wta wta wnan wnan wnan wph wch
    wps wnan wnan lukshef-ax1 nic-mp nic-mp wph wch wps wnan wnan wta wta wta
    wnan wnan wth wch wnan wph wth wnan wph wth wnan wnan wnan wnan lukshefth2
    nic-mp $.


