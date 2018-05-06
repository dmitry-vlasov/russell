$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_the_Lukasiewicz_axioms_from_Meredith_s_sole_axiom.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Derive the standard axioms from the Lukasiewicz axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Used to rederive standard propositional axioms from Lukasiewicz'.
       (Contributed by NM, 23-Dec-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	fluklem1_0 $f wff ph $.
	fluklem1_1 $f wff ps $.
	fluklem1_2 $f wff ch $.
	eluklem1_0 $e |- ( ph -> ps ) $.
	eluklem1_1 $e |- ( ps -> ch ) $.
	luklem1 $p |- ( ph -> ch ) $= fluklem1_1 fluklem1_2 wi fluklem1_0 fluklem1_2 wi eluklem1_1 fluklem1_0 fluklem1_1 wi fluklem1_1 fluklem1_2 wi fluklem1_0 fluklem1_2 wi wi eluklem1_0 fluklem1_0 fluklem1_1 fluklem1_2 luk-1 ax-mp ax-mp $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem2_0 $f wff ph $.
	fluklem2_1 $f wff ps $.
	fluklem2_2 $f wff ch $.
	fluklem2_3 $f wff th $.
	luklem2 $p |- ( ( ph -> -. ps ) -> ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) ) $= fluklem2_0 fluklem2_1 wn wi fluklem2_1 fluklem2_0 fluklem2_2 wi wi fluklem2_0 fluklem2_2 wi fluklem2_3 wi fluklem2_1 fluklem2_3 wi wi fluklem2_0 fluklem2_1 wn wi fluklem2_1 wn fluklem2_2 wi fluklem2_0 fluklem2_2 wi wi fluklem2_1 fluklem2_0 fluklem2_2 wi wi fluklem2_0 fluklem2_1 wn fluklem2_2 luk-1 fluklem2_1 fluklem2_1 wn fluklem2_2 wi wi fluklem2_1 wn fluklem2_2 wi fluklem2_0 fluklem2_2 wi wi fluklem2_1 fluklem2_0 fluklem2_2 wi wi wi fluklem2_1 fluklem2_2 luk-3 fluklem2_1 fluklem2_1 wn fluklem2_2 wi fluklem2_0 fluklem2_2 wi luk-1 ax-mp luklem1 fluklem2_1 fluklem2_0 fluklem2_2 wi fluklem2_3 luk-1 luklem1 $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem3_0 $f wff ph $.
	fluklem3_1 $f wff ps $.
	fluklem3_2 $f wff ch $.
	fluklem3_3 $f wff th $.
	luklem3 $p |- ( ph -> ( ( ( -. ph -> ps ) -> ch ) -> ( th -> ch ) ) ) $= fluklem3_0 fluklem3_0 wn fluklem3_3 wn wi fluklem3_0 wn fluklem3_1 wi fluklem3_2 wi fluklem3_3 fluklem3_2 wi wi fluklem3_0 fluklem3_3 wn luk-3 fluklem3_0 wn fluklem3_3 fluklem3_1 fluklem3_2 luklem2 luklem1 $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem4_0 $f wff ph $.
	fluklem4_1 $f wff ps $.
	luklem4 $p |- ( ( ( ( -. ph -> ph ) -> ph ) -> ps ) -> ps ) $= fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_1 wi fluklem4_1 wn fluklem4_1 wi fluklem4_1 fluklem4_1 wn fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_1 wi fluklem4_1 wn fluklem4_1 wi wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wn fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi fluklem4_1 wn fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi luk-2 fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wn fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi fluklem4_1 wn fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi wi wi fluklem4_0 luk-2 fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_1 wn luklem3 ax-mp ax-mp fluklem4_1 wn fluklem4_0 wn fluklem4_0 wi fluklem4_0 wi fluklem4_1 luk-1 ax-mp fluklem4_1 luk-2 luklem1 $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem5_0 $f wff ph $.
	fluklem5_1 $f wff ps $.
	luklem5 $p |- ( ph -> ( ps -> ph ) ) $= fluklem5_0 fluklem5_0 wn fluklem5_0 wi fluklem5_0 wi fluklem5_1 fluklem5_0 wi wi fluklem5_1 fluklem5_0 wi fluklem5_0 fluklem5_0 fluklem5_0 fluklem5_1 luklem3 fluklem5_0 fluklem5_1 fluklem5_0 wi luklem4 luklem1 $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem6_0 $f wff ph $.
	fluklem6_1 $f wff ps $.
	luklem6 $p |- ( ( ph -> ( ph -> ps ) ) -> ( ph -> ps ) ) $= fluklem6_0 fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_0 fluklem6_0 fluklem6_1 wi fluklem6_1 luk-1 fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi wi wi fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wi wi fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi wi wi fluklem6_0 fluklem6_1 wi wn fluklem6_1 wn fluklem6_0 fluklem6_1 wi wn wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wn fluklem6_1 wn luklem5 fluklem6_1 wn fluklem6_0 fluklem6_1 wi wn wi fluklem6_1 wn fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_1 wn fluklem6_0 fluklem6_1 wi fluklem6_1 fluklem6_1 luklem2 fluklem6_1 fluklem6_0 fluklem6_1 wi fluklem6_1 wi luklem4 luklem1 luklem1 fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi luk-1 ax-mp fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wn fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi luk-1 ax-mp fluklem6_0 fluklem6_1 wi fluklem6_0 fluklem6_1 wi fluklem6_1 wi fluklem6_0 fluklem6_1 wi wi fluklem6_0 fluklem6_1 wi wi luklem4 ax-mp luklem1 $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem7_0 $f wff ph $.
	fluklem7_1 $f wff ps $.
	fluklem7_2 $f wff ch $.
	luklem7 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) ) $= fluklem7_0 fluklem7_1 fluklem7_2 wi wi fluklem7_1 fluklem7_2 wi fluklem7_2 wi fluklem7_0 fluklem7_2 wi wi fluklem7_1 fluklem7_0 fluklem7_2 wi wi fluklem7_0 fluklem7_1 fluklem7_2 wi fluklem7_2 luk-1 fluklem7_1 fluklem7_1 fluklem7_2 wi fluklem7_2 wi wi fluklem7_1 fluklem7_2 wi fluklem7_2 wi fluklem7_0 fluklem7_2 wi wi fluklem7_1 fluklem7_0 fluklem7_2 wi wi wi fluklem7_1 fluklem7_1 fluklem7_2 wi fluklem7_1 fluklem7_2 wi fluklem7_2 wi wi fluklem7_1 fluklem7_2 wi fluklem7_2 wi fluklem7_1 fluklem7_1 fluklem7_2 wi fluklem7_1 wi fluklem7_1 fluklem7_2 wi fluklem7_1 fluklem7_2 wi fluklem7_2 wi wi fluklem7_1 fluklem7_1 fluklem7_2 wi luklem5 fluklem7_1 fluklem7_2 wi fluklem7_1 fluklem7_2 luk-1 luklem1 fluklem7_1 fluklem7_2 wi fluklem7_2 luklem6 luklem1 fluklem7_1 fluklem7_1 fluklem7_2 wi fluklem7_2 wi fluklem7_0 fluklem7_2 wi luk-1 ax-mp luklem1 $.
$}
$( Used to rederive standard propositional axioms from Lukasiewicz'.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fluklem8_0 $f wff ph $.
	fluklem8_1 $f wff ps $.
	fluklem8_2 $f wff ch $.
	luklem8 $p |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) $= fluklem8_2 fluklem8_0 wi fluklem8_0 fluklem8_1 wi fluklem8_2 fluklem8_1 wi wi wi fluklem8_0 fluklem8_1 wi fluklem8_2 fluklem8_0 wi fluklem8_2 fluklem8_1 wi wi wi fluklem8_2 fluklem8_0 fluklem8_1 luk-1 fluklem8_2 fluklem8_0 wi fluklem8_0 fluklem8_1 wi fluklem8_2 fluklem8_1 wi luklem7 ax-mp $.
$}
$( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax1_0 $f wff ph $.
	fax1_1 $f wff ps $.
	ax1 $p |- ( ph -> ( ps -> ph ) ) $= fax1_0 fax1_1 luklem5 $.
$}
$( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax2_0 $f wff ph $.
	fax2_1 $f wff ps $.
	fax2_2 $f wff ch $.
	ax2 $p |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) ) $= fax2_0 fax2_1 fax2_2 wi wi fax2_1 fax2_0 fax2_2 wi wi fax2_0 fax2_1 wi fax2_0 fax2_2 wi wi fax2_0 fax2_1 fax2_2 luklem7 fax2_1 fax2_0 fax2_2 wi wi fax2_0 fax2_1 wi fax2_0 fax2_0 fax2_2 wi wi wi fax2_0 fax2_1 wi fax2_0 fax2_2 wi wi fax2_1 fax2_0 fax2_2 wi fax2_0 luklem8 fax2_0 fax2_0 fax2_2 wi wi fax2_0 fax2_2 wi wi fax2_0 fax2_1 wi fax2_0 fax2_0 fax2_2 wi wi wi fax2_0 fax2_1 wi fax2_0 fax2_2 wi wi wi fax2_0 fax2_2 luklem6 fax2_0 fax2_0 fax2_2 wi wi fax2_0 fax2_2 wi fax2_0 fax2_1 wi luklem8 ax-mp luklem1 luklem1 $.
$}
$( Standard propositional axiom derived from Lukasiewicz axioms.
     (Contributed by NM, 22-Dec-2002.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	fax3_0 $f wff ph $.
	fax3_1 $f wff ps $.
	ax3 $p |- ( ( -. ph -> -. ps ) -> ( ps -> ph ) ) $= fax3_0 wn fax3_1 wn wi fax3_0 wn fax3_0 wi fax3_0 wi fax3_1 fax3_0 wi wi fax3_1 fax3_0 wi fax3_0 wn fax3_1 fax3_0 fax3_0 luklem2 fax3_0 fax3_1 fax3_0 wi luklem4 luklem1 $.
$}

