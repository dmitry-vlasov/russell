$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_Nicod_s_axiom.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
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
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	flukshef-ax1_0 $f wff ph $.
	flukshef-ax1_1 $f wff ps $.
	flukshef-ax1_2 $f wff ch $.
	flukshef-ax1_3 $f wff th $.
	lukshef-ax1 $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( th -/\ ( th -/\ th ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $= flukshef-ax1_0 flukshef-ax1_1 flukshef-ax1_2 flukshef-ax1_3 flukshef-ax1_3 nic-ax $.
$}
$( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	flukshefth1_0 $f wff ph $.
	flukshefth1_1 $f wff ps $.
	flukshefth1_2 $f wff ch $.
	flukshefth1_3 $f wff th $.
	flukshefth1_4 $f wff ta $.
	lukshefth1 $p |- ( ( ( ( ta -/\ ps ) -/\ ( ( ph -/\ ta ) -/\ ( ph -/\ ta ) ) ) -/\ ( th -/\ ( th -/\ th ) ) ) -/\ ( ph -/\ ( ps -/\ ch ) ) ) $= flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan wnan flukshefth1_0 flukshefth1_2 flukshefth1_1 flukshefth1_4 lukshef-ax1 flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan flukshefth1_3 flukshefth1_4 wnan flukshefth1_4 flukshefth1_3 wnan flukshefth1_4 flukshefth1_3 wnan wnan wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 flukshefth1_3 lukshef-ax1 flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_3 flukshefth1_4 wnan flukshefth1_4 flukshefth1_3 wnan flukshefth1_4 flukshefth1_3 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan lukshef-ax1 nic-mp flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan flukshefth1_3 flukshefth1_3 flukshefth1_3 wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan flukshefth1_4 flukshefth1_4 flukshefth1_4 wnan wnan flukshefth1_4 flukshefth1_1 wnan flukshefth1_0 flukshefth1_4 wnan flukshefth1_0 flukshefth1_4 wnan wnan wnan wnan flukshefth1_0 flukshefth1_1 flukshefth1_2 wnan wnan lukshef-ax1 nic-mp nic-mp $.
$}
$( Lemma for ~ renicax .  (Contributed by NM, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	ilukshefth2_0 $f wff ph $.
	ilukshefth2_1 $f wff ps $.
	ilukshefth2_2 $f wff ch $.
	flukshefth2_0 $f wff th $.
	flukshefth2_1 $f wff ta $.
	lukshefth2 $p |- ( ( ta -/\ th ) -/\ ( ( th -/\ ta ) -/\ ( th -/\ ta ) ) ) $= flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan flukshefth2_1 flukshefth2_0 wnan flukshefth2_0 flukshefth2_1 wnan flukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_1 flukshefth2_1 flukshefth2_1 wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan flukshefth2_0 ilukshefth2_2 wnan ilukshefth2_1 flukshefth2_0 wnan ilukshefth2_1 flukshefth2_0 wnan wnan wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan ilukshefth2_1 ilukshefth2_0 ilukshefth2_2 flukshefth2_0 lukshef-ax1 ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 ilukshefth2_2 wnan ilukshefth2_1 flukshefth2_0 wnan ilukshefth2_1 flukshefth2_0 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan flukshefth2_0 lukshef-ax1 nic-mp flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_0 ilukshefth2_0 ilukshefth2_0 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan wnan ilukshefth2_0 ilukshefth2_0 ilukshefth2_0 flukshefth2_0 flukshefth2_1 lukshefth1 flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan ilukshefth2_0 ilukshefth2_0 ilukshefth2_0 wnan wnan ilukshefth2_0 ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_0 wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_0 wnan wnan wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_0 ilukshefth2_0 ilukshefth2_0 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_0 lukshef-ax1 flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan wnan ilukshefth2_0 ilukshefth2_1 ilukshefth2_2 ilukshefth2_0 wnan wnan flukshefth2_0 wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_0 wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan ilukshefth2_0 wnan wnan wnan ilukshefth2_0 ilukshefth2_0 ilukshefth2_0 wnan wnan flukshefth2_1 ilukshefth2_0 wnan ilukshefth2_0 flukshefth2_1 wnan ilukshefth2_0 flukshefth2_1 wnan wnan wnan flukshefth2_0 flukshefth2_0 flukshefth2_0 wnan wnan wnan lukshef-ax1 nic-mp nic-mp nic-mp flukshefth2_0 flukshefth2_0 flukshefth2_0 flukshefth2_1 lukshef-ax1 nic-mp $.
$}
$( A rederivation of ~ nic-ax from ~ lukshef-ax1 , proving that ~ lukshef-ax1
     with ~ nic-mp can be used as a complete axiomatization of propositional
     calculus.  (Contributed by Anthony Hart, 31-Jul-2011.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	frenicax_0 $f wff ph $.
	frenicax_1 $f wff ps $.
	frenicax_2 $f wff ch $.
	frenicax_3 $f wff th $.
	frenicax_4 $f wff ta $.
	renicax $p |- ( ( ph -/\ ( ch -/\ ps ) ) -/\ ( ( ta -/\ ( ta -/\ ta ) ) -/\ ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) ) ) $= frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 frenicax_4 frenicax_3 lukshefth1 frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan lukshefth2 nic-mp frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan lukshefth2 frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan wnan frenicax_0 frenicax_2 frenicax_1 wnan wnan lukshef-ax1 nic-mp nic-mp frenicax_0 frenicax_2 frenicax_1 wnan wnan frenicax_4 frenicax_4 frenicax_4 wnan wnan frenicax_3 frenicax_2 wnan frenicax_0 frenicax_3 wnan frenicax_0 frenicax_3 wnan wnan wnan wnan lukshefth2 nic-mp $.
$}

