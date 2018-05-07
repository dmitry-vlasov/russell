$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_Nicod_s_axiom_from_the_standard_axioms.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Minor premise. $)
$( Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	inic-imp_0 $f wff ta $.
	fnic-imp_0 $f wff ph $.
	fnic-imp_1 $f wff ps $.
	fnic-imp_2 $f wff ch $.
	fnic-imp_3 $f wff th $.
	enic-imp_0 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $= fnic-imp_0 fnic-imp_2 fnic-imp_1 wnan wnan fnic-imp_3 fnic-imp_2 wnan fnic-imp_0 fnic-imp_3 wnan fnic-imp_0 fnic-imp_3 wnan wnan wnan inic-imp_0 inic-imp_0 inic-imp_0 wnan wnan enic-imp_0 fnic-imp_0 fnic-imp_1 fnic-imp_2 fnic-imp_3 inic-imp_0 nic-ax nic-mp $.
$}
$( Lemma for ~ nic-id .  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	fnic-idlem1_0 $f wff ph $.
	fnic-idlem1_1 $f wff ps $.
	fnic-idlem1_2 $f wff ch $.
	fnic-idlem1_3 $f wff th $.
	fnic-idlem1_4 $f wff ta $.
	nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $= fnic-idlem1_0 fnic-idlem1_2 fnic-idlem1_1 wnan wnan fnic-idlem1_0 fnic-idlem1_2 wnan fnic-idlem1_0 fnic-idlem1_0 wnan fnic-idlem1_0 fnic-idlem1_0 wnan wnan wnan fnic-idlem1_4 fnic-idlem1_4 fnic-idlem1_4 wnan wnan fnic-idlem1_3 fnic-idlem1_0 fnic-idlem1_1 fnic-idlem1_2 fnic-idlem1_0 fnic-idlem1_4 nic-ax nic-imp $.
$}
$( Lemma for ~ nic-id .  Inference used by ~ nic-id .  (Contributed by Jeff
       Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	$v et $.
	fnic-idlem2_0 $f wff ph $.
	fnic-idlem2_1 $f wff ps $.
	fnic-idlem2_2 $f wff ch $.
	fnic-idlem2_3 $f wff th $.
	fnic-idlem2_4 $f wff ta $.
	fnic-idlem2_5 $f wff et $.
	enic-idlem2_0 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
	nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $= fnic-idlem2_5 fnic-idlem2_0 fnic-idlem2_2 fnic-idlem2_1 wnan wnan fnic-idlem2_3 wnan wnan fnic-idlem2_3 fnic-idlem2_4 fnic-idlem2_4 fnic-idlem2_4 wnan wnan wnan fnic-idlem2_5 wnan fnic-idlem2_3 fnic-idlem2_4 fnic-idlem2_4 fnic-idlem2_4 wnan wnan wnan fnic-idlem2_5 wnan enic-idlem2_0 fnic-idlem2_3 fnic-idlem2_4 fnic-idlem2_4 fnic-idlem2_4 wnan wnan wnan fnic-idlem2_0 fnic-idlem2_2 fnic-idlem2_1 wnan wnan fnic-idlem2_3 wnan fnic-idlem2_0 fnic-idlem2_2 fnic-idlem2_1 wnan wnan fnic-idlem2_3 wnan fnic-idlem2_5 fnic-idlem2_0 fnic-idlem2_2 fnic-idlem2_1 wnan wnan fnic-idlem2_0 fnic-idlem2_2 wnan fnic-idlem2_0 fnic-idlem2_0 wnan fnic-idlem2_0 fnic-idlem2_0 wnan wnan wnan fnic-idlem2_4 fnic-idlem2_4 fnic-idlem2_4 wnan wnan fnic-idlem2_3 fnic-idlem2_0 fnic-idlem2_1 fnic-idlem2_2 fnic-idlem2_0 fnic-idlem2_4 nic-ax nic-imp nic-imp nic-mp $.
$}
$( Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	$v ta $.
	inic-id_0 $f wff ph $.
	inic-id_1 $f wff ps $.
	inic-id_2 $f wff ch $.
	inic-id_3 $f wff th $.
	fnic-id_0 $f wff ta $.
	nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $= inic-id_0 inic-id_1 wnan inic-id_1 inic-id_0 wnan inic-id_1 inic-id_0 wnan wnan wnan inic-id_2 inic-id_2 inic-id_2 wnan wnan wnan inic-id_1 inic-id_1 inic-id_1 wnan wnan wnan fnic-id_0 fnic-id_0 fnic-id_0 wnan wnan inic-id_2 inic-id_2 inic-id_2 wnan wnan inic-id_3 inic-id_3 inic-id_3 inic-id_0 inic-id_1 wnan inic-id_1 inic-id_0 wnan inic-id_1 inic-id_0 wnan wnan wnan inic-id_2 inic-id_1 inic-id_1 inic-id_1 wnan wnan inic-id_1 inic-id_1 inic-id_1 inic-id_0 inic-id_3 nic-ax nic-idlem2 inic-id_0 inic-id_1 wnan inic-id_1 inic-id_0 wnan inic-id_1 inic-id_0 wnan wnan wnan inic-id_2 inic-id_2 wnan inic-id_2 inic-id_0 inic-id_1 wnan inic-id_1 inic-id_0 wnan inic-id_1 inic-id_0 wnan wnan wnan inic-id_2 inic-id_2 inic-id_2 wnan wnan wnan inic-id_1 inic-id_2 inic-id_2 inic-id_2 wnan wnan fnic-id_0 fnic-id_0 fnic-id_0 wnan wnan wnan inic-id_0 inic-id_1 wnan inic-id_1 inic-id_0 wnan inic-id_1 inic-id_0 wnan inic-id_2 inic-id_2 inic-id_2 wnan wnan fnic-id_0 nic-idlem1 nic-idlem2 nic-mp $.
$}
$( ` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v th $.
	$v ta $.
	inic-swap_0 $f wff ta $.
	fnic-swap_0 $f wff ph $.
	fnic-swap_1 $f wff th $.
	nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $= fnic-swap_0 fnic-swap_0 fnic-swap_0 wnan wnan fnic-swap_1 fnic-swap_0 wnan fnic-swap_0 fnic-swap_1 wnan fnic-swap_0 fnic-swap_1 wnan wnan wnan inic-swap_0 inic-swap_0 inic-swap_0 wnan wnan fnic-swap_0 nic-id fnic-swap_0 fnic-swap_0 fnic-swap_0 fnic-swap_1 inic-swap_0 nic-ax nic-mp $.
$}
$( Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v th $.
	fnic-isw1_0 $f wff ph $.
	fnic-isw1_1 $f wff th $.
	enic-isw1_0 $e |- ( th -/\ ph ) $.
	nic-isw1 $p |- ( ph -/\ th ) $= fnic-isw1_1 fnic-isw1_0 wnan fnic-isw1_0 fnic-isw1_1 wnan fnic-isw1_0 fnic-isw1_1 wnan enic-isw1_0 fnic-isw1_0 fnic-isw1_1 nic-swap nic-mp $.
$}
$( Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v th $.
	fnic-isw2_0 $f wff ph $.
	fnic-isw2_1 $f wff ps $.
	fnic-isw2_2 $f wff th $.
	enic-isw2_0 $e |- ( ps -/\ ( th -/\ ph ) ) $.
	nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $= fnic-isw2_1 fnic-isw2_0 fnic-isw2_2 wnan fnic-isw2_1 fnic-isw2_2 fnic-isw2_0 wnan wnan fnic-isw2_0 fnic-isw2_2 wnan fnic-isw2_1 wnan fnic-isw2_0 fnic-isw2_2 wnan fnic-isw2_1 wnan enic-isw2_0 fnic-isw2_0 fnic-isw2_2 wnan fnic-isw2_2 fnic-isw2_0 wnan fnic-isw2_2 fnic-isw2_0 wnan fnic-isw2_1 fnic-isw2_2 fnic-isw2_0 nic-swap nic-imp nic-mp nic-isw1 $.
$}
$( Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fnic-iimp1_0 $f wff ph $.
	fnic-iimp1_1 $f wff ps $.
	fnic-iimp1_2 $f wff ch $.
	fnic-iimp1_3 $f wff th $.
	enic-iimp1_0 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	enic-iimp1_1 $e |- ( th -/\ ch ) $.
	nic-iimp1 $p |- ( th -/\ ph ) $= fnic-iimp1_3 fnic-iimp1_0 fnic-iimp1_3 fnic-iimp1_2 wnan fnic-iimp1_0 fnic-iimp1_3 wnan fnic-iimp1_0 fnic-iimp1_3 wnan enic-iimp1_1 fnic-iimp1_0 fnic-iimp1_1 fnic-iimp1_2 fnic-iimp1_3 enic-iimp1_0 nic-imp nic-mp nic-isw1 $.
$}
$( Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v th $.
	fnic-iimp2_0 $f wff ph $.
	fnic-iimp2_1 $f wff ps $.
	fnic-iimp2_2 $f wff ch $.
	fnic-iimp2_3 $f wff th $.
	enic-iimp2_0 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
	enic-iimp2_1 $e |- ( th -/\ ph ) $.
	nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $= fnic-iimp2_2 fnic-iimp2_2 wnan fnic-iimp2_1 fnic-iimp2_0 fnic-iimp2_3 fnic-iimp2_2 fnic-iimp2_2 wnan fnic-iimp2_0 fnic-iimp2_1 wnan enic-iimp2_0 nic-isw1 enic-iimp2_1 nic-iimp1 $.
$}
$( Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnic-idel_0 $f wff ph $.
	fnic-idel_1 $f wff ps $.
	fnic-idel_2 $f wff ch $.
	enic-idel_0 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $= fnic-idel_2 fnic-idel_2 wnan fnic-idel_2 wnan fnic-idel_0 fnic-idel_2 fnic-idel_2 wnan wnan fnic-idel_0 fnic-idel_2 fnic-idel_2 wnan wnan fnic-idel_2 fnic-idel_2 wnan fnic-idel_2 fnic-idel_2 nic-id nic-isw1 fnic-idel_0 fnic-idel_1 fnic-idel_2 fnic-idel_2 fnic-idel_2 wnan enic-idel_0 nic-imp nic-mp $.
$}
$( Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	fnic-ich_0 $f wff ph $.
	fnic-ich_1 $f wff ps $.
	fnic-ich_2 $f wff ch $.
	enic-ich_0 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
	enic-ich_1 $e |- ( ps -/\ ( ch -/\ ch ) ) $.
	nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $= fnic-ich_2 fnic-ich_2 wnan fnic-ich_1 wnan fnic-ich_0 fnic-ich_2 fnic-ich_2 wnan wnan fnic-ich_0 fnic-ich_2 fnic-ich_2 wnan wnan fnic-ich_2 fnic-ich_2 wnan fnic-ich_1 enic-ich_1 nic-isw1 fnic-ich_0 fnic-ich_1 fnic-ich_1 fnic-ich_2 fnic-ich_2 wnan enic-ich_0 nic-imp nic-mp $.
$}
$( Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fnic-idbl_0 $f wff ph $.
	fnic-idbl_1 $f wff ps $.
	enic-idbl_0 $e |- ( ph -/\ ( ps -/\ ps ) ) $.
	nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $= fnic-idbl_1 fnic-idbl_1 wnan fnic-idbl_0 fnic-idbl_1 wnan fnic-idbl_0 fnic-idbl_0 wnan fnic-idbl_0 fnic-idbl_1 fnic-idbl_1 fnic-idbl_1 enic-idbl_0 nic-imp fnic-idbl_0 fnic-idbl_1 fnic-idbl_1 fnic-idbl_0 enic-idbl_0 nic-imp nic-ich $.
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
${
	$v ta $.
	fnic-bijust_0 $f wff ta $.
	nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $= fnic-bijust_0 fnic-bijust_0 nic-swap $.
$}
$( 'Biconditional' premise. $)
$( Inference to extract one side of an implication from a definition.
       (Contributed by Jeff Hoffman, 18-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fnic-bi1_0 $f wff ph $.
	fnic-bi1_1 $f wff ps $.
	enic-bi1_0 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $.
	nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $= fnic-bi1_0 fnic-bi1_0 fnic-bi1_1 fnic-bi1_1 fnic-bi1_0 fnic-bi1_0 fnic-bi1_0 fnic-bi1_1 wnan fnic-bi1_1 fnic-bi1_1 wnan fnic-bi1_0 fnic-bi1_0 wnan fnic-bi1_0 enic-bi1_0 fnic-bi1_0 nic-id nic-iimp1 nic-isw2 nic-idel $.
$}
$( 'Biconditional' premise.  $)
$( Inference to extract the other side of an implication from a
       'biconditional' definition.  (Contributed by Jeff Hoffman,
       18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fnic-bi2_0 $f wff ph $.
	fnic-bi2_1 $f wff ps $.
	enic-bi2_0 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $.
	nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $= fnic-bi2_1 fnic-bi2_1 fnic-bi2_0 fnic-bi2_0 fnic-bi2_1 wnan fnic-bi2_0 fnic-bi2_0 wnan fnic-bi2_1 fnic-bi2_1 wnan fnic-bi2_1 fnic-bi2_1 fnic-bi2_1 wnan fnic-bi2_0 fnic-bi2_1 wnan fnic-bi2_0 fnic-bi2_0 wnan enic-bi2_0 nic-isw2 fnic-bi2_1 nic-id nic-iimp1 nic-idel $.
$}
$( (not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Minor premise. $)
$( Major premise. $)
$( Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fnic-stdmp_0 $f wff ph $.
	fnic-stdmp_1 $f wff ps $.
	enic-stdmp_0 $e |- ph $.
	enic-stdmp_1 $e |- ( ph -> ps ) $.
	nic-stdmp $p |- ps $= fnic-stdmp_0 fnic-stdmp_1 fnic-stdmp_1 enic-stdmp_0 fnic-stdmp_0 fnic-stdmp_1 wi fnic-stdmp_0 fnic-stdmp_1 fnic-stdmp_1 wnan wnan fnic-stdmp_0 fnic-stdmp_1 fnic-stdmp_1 wnan wnan enic-stdmp_1 fnic-stdmp_0 fnic-stdmp_1 fnic-stdmp_1 wnan wnan fnic-stdmp_0 fnic-stdmp_1 wi fnic-stdmp_0 fnic-stdmp_1 nic-dfim nic-bi2 nic-mp nic-mp $.
$}
$( Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	$v ch $.
	$v ta $.
	inic-luk1_0 $f wff ta $.
	fnic-luk1_0 $f wff ph $.
	fnic-luk1_1 $f wff ps $.
	fnic-luk1_2 $f wff ch $.
	nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi wnan wnan fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi wi fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi wi fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 wnan wnan fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_0 fnic-luk1_1 nic-dfim nic-bi2 fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 wnan wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan wnan fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 wnan wnan inic-luk1_0 inic-luk1_0 inic-luk1_0 wnan wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan wnan wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan wnan wnan fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 wnan wnan inic-luk1_0 inic-luk1_0 inic-luk1_0 wnan wnan fnic-luk1_0 fnic-luk1_1 fnic-luk1_1 fnic-luk1_2 fnic-luk1_2 wnan inic-luk1_0 nic-ax nic-isw2 nic-idel fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan wnan wnan fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan wnan fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 nic-dfim nic-bi1 nic-idbl nic-imp fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_1 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 wnan fnic-luk1_1 fnic-luk1_2 fnic-luk1_2 wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_1 fnic-luk1_2 nic-dfim nic-bi2 fnic-luk1_2 fnic-luk1_2 wnan fnic-luk1_1 nic-swap nic-ich nic-imp nic-ich nic-ich fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wnan wnan fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi nic-dfim nic-bi1 nic-ich nic-ich fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi wnan wnan fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi wi fnic-luk1_0 fnic-luk1_1 wi fnic-luk1_1 fnic-luk1_2 wi fnic-luk1_0 fnic-luk1_2 wi wi nic-dfim nic-bi1 nic-mp $.
$}
$( Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	fnic-luk2_0 $f wff ph $.
	nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $= fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 fnic-luk2_0 wnan wnan fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 wi fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 wi fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 wn fnic-luk2_0 fnic-luk2_0 wnan wnan fnic-luk2_0 wn fnic-luk2_0 fnic-luk2_0 wnan wnan fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 wn fnic-luk2_0 fnic-luk2_0 wnan wnan fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 wn fnic-luk2_0 nic-dfim nic-bi2 fnic-luk2_0 wn fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 wn wnan fnic-luk2_0 wn fnic-luk2_0 wn wnan fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 fnic-luk2_0 wnan wnan fnic-luk2_0 fnic-luk2_0 wnan fnic-luk2_0 nic-dfneg fnic-luk2_0 fnic-luk2_0 wnan nic-id nic-iimp1 nic-isw2 nic-iimp1 nic-isw1 fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 fnic-luk2_0 wnan wnan fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 wi fnic-luk2_0 wn fnic-luk2_0 wi fnic-luk2_0 nic-dfim nic-bi1 nic-mp $.
$}
$( Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
${
	$v ph $.
	$v ps $.
	fnic-luk3_0 $f wff ph $.
	fnic-luk3_1 $f wff ps $.
	nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $= fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 wi fnic-luk3_0 wn fnic-luk3_1 wi wnan wnan fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 wi wi fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 wi wi fnic-luk3_0 wn fnic-luk3_1 fnic-luk3_1 wnan fnic-luk3_0 wn fnic-luk3_1 wi fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 fnic-luk3_1 wnan wnan fnic-luk3_0 wn fnic-luk3_1 wi fnic-luk3_0 wn fnic-luk3_1 nic-dfim nic-bi1 fnic-luk3_0 wn fnic-luk3_0 fnic-luk3_0 wnan fnic-luk3_0 fnic-luk3_0 wnan fnic-luk3_0 fnic-luk3_0 fnic-luk3_0 wnan fnic-luk3_0 wn fnic-luk3_0 nic-dfneg nic-bi2 fnic-luk3_0 nic-id nic-iimp1 nic-iimp2 fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 wi fnic-luk3_0 wn fnic-luk3_1 wi wnan wnan fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 wi wi fnic-luk3_0 fnic-luk3_0 wn fnic-luk3_1 wi nic-dfim nic-bi1 nic-mp $.
$}

