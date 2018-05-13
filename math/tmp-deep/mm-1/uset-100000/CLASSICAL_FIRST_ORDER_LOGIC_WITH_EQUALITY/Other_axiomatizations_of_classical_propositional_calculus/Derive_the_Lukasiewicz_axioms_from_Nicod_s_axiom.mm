$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Other_axiomatizations_of_classical_propositional_calculus/Derive_Nicod_s_axiom_from_the_standard_axioms.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Derive the Lukasiewicz axioms from Nicod's axiom

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Minor premise. $)

$(Inference for ~ nic-mp using ~ nic-ax as major premise.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_nic-imp $f wff ph $.
	f1_nic-imp $f wff ps $.
	f2_nic-imp $f wff ch $.
	f3_nic-imp $f wff th $.
	i0_nic-imp $f wff ta $.
	e0_nic-imp $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	p_nic-imp $p |- ( ( th -/\ ch ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $= e0_nic-imp f0_nic-imp f1_nic-imp f2_nic-imp f3_nic-imp i0_nic-imp p_nic-ax f0_nic-imp f2_nic-imp f1_nic-imp a_wnan a_wnan f3_nic-imp f2_nic-imp a_wnan f0_nic-imp f3_nic-imp a_wnan f0_nic-imp f3_nic-imp a_wnan a_wnan a_wnan i0_nic-imp i0_nic-imp i0_nic-imp a_wnan a_wnan p_nic-mp $.
$}

$(Lemma for ~ nic-id .  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch th ta  $.
	f0_nic-idlem1 $f wff ph $.
	f1_nic-idlem1 $f wff ps $.
	f2_nic-idlem1 $f wff ch $.
	f3_nic-idlem1 $f wff th $.
	f4_nic-idlem1 $f wff ta $.
	p_nic-idlem1 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ ( ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) ) $= f0_nic-idlem1 f1_nic-idlem1 f2_nic-idlem1 f0_nic-idlem1 f4_nic-idlem1 p_nic-ax f0_nic-idlem1 f2_nic-idlem1 f1_nic-idlem1 a_wnan a_wnan f0_nic-idlem1 f2_nic-idlem1 a_wnan f0_nic-idlem1 f0_nic-idlem1 a_wnan f0_nic-idlem1 f0_nic-idlem1 a_wnan a_wnan a_wnan f4_nic-idlem1 f4_nic-idlem1 f4_nic-idlem1 a_wnan a_wnan f3_nic-idlem1 p_nic-imp $.
$}

$(Lemma for ~ nic-id .  Inference used by ~ nic-id .  (Contributed by Jeff
       Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch th ta et  $.
	f0_nic-idlem2 $f wff ph $.
	f1_nic-idlem2 $f wff ps $.
	f2_nic-idlem2 $f wff ch $.
	f3_nic-idlem2 $f wff th $.
	f4_nic-idlem2 $f wff ta $.
	f5_nic-idlem2 $f wff et $.
	e0_nic-idlem2 $e |- ( et -/\ ( ( ph -/\ ( ch -/\ ps ) ) -/\ th ) ) $.
	p_nic-idlem2 $p |- ( ( th -/\ ( ta -/\ ( ta -/\ ta ) ) ) -/\ et ) $= e0_nic-idlem2 f0_nic-idlem2 f1_nic-idlem2 f2_nic-idlem2 f0_nic-idlem2 f4_nic-idlem2 p_nic-ax f0_nic-idlem2 f2_nic-idlem2 f1_nic-idlem2 a_wnan a_wnan f0_nic-idlem2 f2_nic-idlem2 a_wnan f0_nic-idlem2 f0_nic-idlem2 a_wnan f0_nic-idlem2 f0_nic-idlem2 a_wnan a_wnan a_wnan f4_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 a_wnan a_wnan f3_nic-idlem2 p_nic-imp f3_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 a_wnan a_wnan a_wnan f0_nic-idlem2 f2_nic-idlem2 f1_nic-idlem2 a_wnan a_wnan f3_nic-idlem2 a_wnan f0_nic-idlem2 f2_nic-idlem2 f1_nic-idlem2 a_wnan a_wnan f3_nic-idlem2 a_wnan f5_nic-idlem2 p_nic-imp f5_nic-idlem2 f0_nic-idlem2 f2_nic-idlem2 f1_nic-idlem2 a_wnan a_wnan f3_nic-idlem2 a_wnan a_wnan f3_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 a_wnan a_wnan a_wnan f5_nic-idlem2 a_wnan f3_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 f4_nic-idlem2 a_wnan a_wnan a_wnan f5_nic-idlem2 a_wnan p_nic-mp $.
$}

$(Theorem ~ id expressed with ` -/\ ` .  (Contributed by Jeff Hoffman,
     17-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ta  $.
	f0_nic-id $f wff ta $.
	i0_nic-id $f wff ph $.
	i1_nic-id $f wff ps $.
	i2_nic-id $f wff ch $.
	i3_nic-id $f wff th $.
	p_nic-id $p |- ( ta -/\ ( ta -/\ ta ) ) $= i1_nic-id i1_nic-id i1_nic-id i0_nic-id i3_nic-id p_nic-ax i3_nic-id i3_nic-id i3_nic-id i0_nic-id i1_nic-id a_wnan i1_nic-id i0_nic-id a_wnan i1_nic-id i0_nic-id a_wnan a_wnan a_wnan i2_nic-id i1_nic-id i1_nic-id i1_nic-id a_wnan a_wnan p_nic-idlem2 i0_nic-id i1_nic-id a_wnan i1_nic-id i0_nic-id a_wnan i1_nic-id i0_nic-id a_wnan i2_nic-id i2_nic-id i2_nic-id a_wnan a_wnan f0_nic-id p_nic-idlem1 i0_nic-id i1_nic-id a_wnan i1_nic-id i0_nic-id a_wnan i1_nic-id i0_nic-id a_wnan a_wnan a_wnan i2_nic-id i2_nic-id a_wnan i2_nic-id i0_nic-id i1_nic-id a_wnan i1_nic-id i0_nic-id a_wnan i1_nic-id i0_nic-id a_wnan a_wnan a_wnan i2_nic-id i2_nic-id i2_nic-id a_wnan a_wnan a_wnan i1_nic-id i2_nic-id i2_nic-id i2_nic-id a_wnan a_wnan f0_nic-id f0_nic-id f0_nic-id a_wnan a_wnan a_wnan p_nic-idlem2 i0_nic-id i1_nic-id a_wnan i1_nic-id i0_nic-id a_wnan i1_nic-id i0_nic-id a_wnan a_wnan a_wnan i2_nic-id i2_nic-id i2_nic-id a_wnan a_wnan a_wnan i1_nic-id i1_nic-id i1_nic-id a_wnan a_wnan a_wnan f0_nic-id f0_nic-id f0_nic-id a_wnan a_wnan i2_nic-id i2_nic-id i2_nic-id a_wnan a_wnan p_nic-mp $.
$}

$(` -/\ ` is symmetric.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph th  $.
	f0_nic-swap $f wff ph $.
	f1_nic-swap $f wff th $.
	i0_nic-swap $f wff ta $.
	p_nic-swap $p |- ( ( th -/\ ph ) -/\ ( ( ph -/\ th ) -/\ ( ph -/\ th ) ) ) $= f0_nic-swap p_nic-id f0_nic-swap f0_nic-swap f0_nic-swap f1_nic-swap i0_nic-swap p_nic-ax f0_nic-swap f0_nic-swap f0_nic-swap a_wnan a_wnan f1_nic-swap f0_nic-swap a_wnan f0_nic-swap f1_nic-swap a_wnan f0_nic-swap f1_nic-swap a_wnan a_wnan a_wnan i0_nic-swap i0_nic-swap i0_nic-swap a_wnan a_wnan p_nic-mp $.
$}

$(Inference version of ~ nic-swap .  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph th  $.
	f0_nic-isw1 $f wff ph $.
	f1_nic-isw1 $f wff th $.
	e0_nic-isw1 $e |- ( th -/\ ph ) $.
	p_nic-isw1 $p |- ( ph -/\ th ) $= e0_nic-isw1 f0_nic-isw1 f1_nic-isw1 p_nic-swap f1_nic-isw1 f0_nic-isw1 a_wnan f0_nic-isw1 f1_nic-isw1 a_wnan f0_nic-isw1 f1_nic-isw1 a_wnan p_nic-mp $.
$}

$(Inference for swapping nested terms.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps th  $.
	f0_nic-isw2 $f wff ph $.
	f1_nic-isw2 $f wff ps $.
	f2_nic-isw2 $f wff th $.
	e0_nic-isw2 $e |- ( ps -/\ ( th -/\ ph ) ) $.
	p_nic-isw2 $p |- ( ps -/\ ( ph -/\ th ) ) $= e0_nic-isw2 f2_nic-isw2 f0_nic-isw2 p_nic-swap f0_nic-isw2 f2_nic-isw2 a_wnan f2_nic-isw2 f0_nic-isw2 a_wnan f2_nic-isw2 f0_nic-isw2 a_wnan f1_nic-isw2 p_nic-imp f1_nic-isw2 f2_nic-isw2 f0_nic-isw2 a_wnan a_wnan f0_nic-isw2 f2_nic-isw2 a_wnan f1_nic-isw2 a_wnan f0_nic-isw2 f2_nic-isw2 a_wnan f1_nic-isw2 a_wnan p_nic-mp f1_nic-isw2 f0_nic-isw2 f2_nic-isw2 a_wnan p_nic-isw1 $.
$}

$(Inference version of ~ nic-imp using right-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_nic-iimp1 $f wff ph $.
	f1_nic-iimp1 $f wff ps $.
	f2_nic-iimp1 $f wff ch $.
	f3_nic-iimp1 $f wff th $.
	e0_nic-iimp1 $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	e1_nic-iimp1 $e |- ( th -/\ ch ) $.
	p_nic-iimp1 $p |- ( th -/\ ph ) $= e1_nic-iimp1 e0_nic-iimp1 f0_nic-iimp1 f1_nic-iimp1 f2_nic-iimp1 f3_nic-iimp1 p_nic-imp f3_nic-iimp1 f2_nic-iimp1 a_wnan f0_nic-iimp1 f3_nic-iimp1 a_wnan f0_nic-iimp1 f3_nic-iimp1 a_wnan p_nic-mp f3_nic-iimp1 f0_nic-iimp1 p_nic-isw1 $.
$}

$(Inference version of ~ nic-imp using left-handed term.  (Contributed by
       Jeff Hoffman, 17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch th  $.
	f0_nic-iimp2 $f wff ph $.
	f1_nic-iimp2 $f wff ps $.
	f2_nic-iimp2 $f wff ch $.
	f3_nic-iimp2 $f wff th $.
	e0_nic-iimp2 $e |- ( ( ph -/\ ps ) -/\ ( ch -/\ ch ) ) $.
	e1_nic-iimp2 $e |- ( th -/\ ph ) $.
	p_nic-iimp2 $p |- ( th -/\ ( ch -/\ ch ) ) $= e0_nic-iimp2 f2_nic-iimp2 f2_nic-iimp2 a_wnan f0_nic-iimp2 f1_nic-iimp2 a_wnan p_nic-isw1 e1_nic-iimp2 f2_nic-iimp2 f2_nic-iimp2 a_wnan f1_nic-iimp2 f0_nic-iimp2 f3_nic-iimp2 p_nic-iimp1 $.
$}

$(Inference to remove the trailing term.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_nic-idel $f wff ph $.
	f1_nic-idel $f wff ps $.
	f2_nic-idel $f wff ch $.
	e0_nic-idel $e |- ( ph -/\ ( ch -/\ ps ) ) $.
	p_nic-idel $p |- ( ph -/\ ( ch -/\ ch ) ) $= f2_nic-idel p_nic-id f2_nic-idel f2_nic-idel a_wnan f2_nic-idel p_nic-isw1 e0_nic-idel f0_nic-idel f1_nic-idel f2_nic-idel f2_nic-idel f2_nic-idel a_wnan p_nic-imp f2_nic-idel f2_nic-idel a_wnan f2_nic-idel a_wnan f0_nic-idel f2_nic-idel f2_nic-idel a_wnan a_wnan f0_nic-idel f2_nic-idel f2_nic-idel a_wnan a_wnan p_nic-mp $.
$}

$(Chained inference.  (Contributed by Jeff Hoffman, 17-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_nic-ich $f wff ph $.
	f1_nic-ich $f wff ps $.
	f2_nic-ich $f wff ch $.
	e0_nic-ich $e |- ( ph -/\ ( ps -/\ ps ) ) $.
	e1_nic-ich $e |- ( ps -/\ ( ch -/\ ch ) ) $.
	p_nic-ich $p |- ( ph -/\ ( ch -/\ ch ) ) $= e1_nic-ich f2_nic-ich f2_nic-ich a_wnan f1_nic-ich p_nic-isw1 e0_nic-ich f0_nic-ich f1_nic-ich f1_nic-ich f2_nic-ich f2_nic-ich a_wnan p_nic-imp f2_nic-ich f2_nic-ich a_wnan f1_nic-ich a_wnan f0_nic-ich f2_nic-ich f2_nic-ich a_wnan a_wnan f0_nic-ich f2_nic-ich f2_nic-ich a_wnan a_wnan p_nic-mp $.
$}

$(Double the terms.  Since doubling is the same as negation, this can be
       viewed as a contraposition inference.  (Contributed by Jeff Hoffman,
       17-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_nic-idbl $f wff ph $.
	f1_nic-idbl $f wff ps $.
	e0_nic-idbl $e |- ( ph -/\ ( ps -/\ ps ) ) $.
	p_nic-idbl $p |- ( ( ps -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ph -/\ ph ) ) ) $= e0_nic-idbl f0_nic-idbl f1_nic-idbl f1_nic-idbl f1_nic-idbl p_nic-imp e0_nic-idbl f0_nic-idbl f1_nic-idbl f1_nic-idbl f0_nic-idbl p_nic-imp f1_nic-idbl f1_nic-idbl a_wnan f0_nic-idbl f1_nic-idbl a_wnan f0_nic-idbl f0_nic-idbl a_wnan p_nic-ich $.
$}

$((not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Biconditional justification from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(For nic-* definitions, the biconditional connective is not used.  Instead,
     definitions are made based on this form. ~ nic-bi1 and ~ nic-bi2 are used
     to convert the definitions into usable theorems about one side of the
     implication.  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ta  $.
	f0_nic-bijust $f wff ta $.
	p_nic-bijust $p |- ( ( ta -/\ ta ) -/\ ( ( ta -/\ ta ) -/\ ( ta -/\ ta ) ) ) $= f0_nic-bijust f0_nic-bijust p_nic-swap $.
$}

$('Biconditional' premise. $)

$(Inference to extract one side of an implication from a definition.
       (Contributed by Jeff Hoffman, 18-Nov-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_nic-bi1 $f wff ph $.
	f1_nic-bi1 $f wff ps $.
	e0_nic-bi1 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $.
	p_nic-bi1 $p |- ( ph -/\ ( ps -/\ ps ) ) $= e0_nic-bi1 f0_nic-bi1 p_nic-id f0_nic-bi1 f1_nic-bi1 a_wnan f1_nic-bi1 f1_nic-bi1 a_wnan f0_nic-bi1 f0_nic-bi1 a_wnan f0_nic-bi1 p_nic-iimp1 f1_nic-bi1 f0_nic-bi1 f0_nic-bi1 p_nic-isw2 f0_nic-bi1 f0_nic-bi1 f1_nic-bi1 p_nic-idel $.
$}

$('Biconditional' premise.  $)

$(Inference to extract the other side of an implication from a
       'biconditional' definition.  (Contributed by Jeff Hoffman,
       18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_nic-bi2 $f wff ph $.
	f1_nic-bi2 $f wff ps $.
	e0_nic-bi2 $e |- ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) $.
	p_nic-bi2 $p |- ( ps -/\ ( ph -/\ ph ) ) $= e0_nic-bi2 f1_nic-bi2 f1_nic-bi2 a_wnan f0_nic-bi2 f1_nic-bi2 a_wnan f0_nic-bi2 f0_nic-bi2 a_wnan p_nic-isw2 f1_nic-bi2 p_nic-id f0_nic-bi2 f1_nic-bi2 a_wnan f0_nic-bi2 f0_nic-bi2 a_wnan f1_nic-bi2 f1_nic-bi2 a_wnan f1_nic-bi2 p_nic-iimp1 f1_nic-bi2 f1_nic-bi2 f0_nic-bi2 p_nic-idel $.
$}

$((not in Table of Contents)
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
             Prove the Lukasiewicz axioms from Nicod's axiom
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Minor premise. $)

$(Major premise. $)

$(Derive the standard modus ponens from ~ nic-mp .  (Contributed by Jeff
       Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_nic-stdmp $f wff ph $.
	f1_nic-stdmp $f wff ps $.
	e0_nic-stdmp $e |- ph $.
	e1_nic-stdmp $e |- ( ph -> ps ) $.
	p_nic-stdmp $p |- ps $= e0_nic-stdmp e1_nic-stdmp f0_nic-stdmp f1_nic-stdmp p_nic-dfim f0_nic-stdmp f1_nic-stdmp f1_nic-stdmp a_wnan a_wnan f0_nic-stdmp f1_nic-stdmp a_wi p_nic-bi2 f0_nic-stdmp f1_nic-stdmp a_wi f0_nic-stdmp f1_nic-stdmp f1_nic-stdmp a_wnan a_wnan f0_nic-stdmp f1_nic-stdmp f1_nic-stdmp a_wnan a_wnan p_nic-mp f0_nic-stdmp f1_nic-stdmp f1_nic-stdmp p_nic-mp $.
$}

$(Proof of ~ luk-1 from ~ nic-ax and ~ nic-mp (and definitions ~ nic-dfim
     and ~ nic-dfneg ).  Note that the standard axioms ~ ax-1 , ~ ax-2 , and
     ~ ax-3 are proved from the Lukasiewicz axioms by theorems ~ ax1 , ~ ax2 ,
     and ~ ax3 .  (Contributed by Jeff Hoffman, 18-Nov-2007.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)

${
	$v ph ps ch  $.
	f0_nic-luk1 $f wff ph $.
	f1_nic-luk1 $f wff ps $.
	f2_nic-luk1 $f wff ch $.
	i0_nic-luk1 $f wff ta $.
	p_nic-luk1 $p |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) ) $= f0_nic-luk1 f1_nic-luk1 p_nic-dfim f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 a_wnan a_wnan f0_nic-luk1 f1_nic-luk1 a_wi p_nic-bi2 f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan i0_nic-luk1 p_nic-ax f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan a_wnan a_wnan f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 a_wnan a_wnan i0_nic-luk1 i0_nic-luk1 i0_nic-luk1 a_wnan a_wnan p_nic-isw2 f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 a_wnan a_wnan i0_nic-luk1 i0_nic-luk1 i0_nic-luk1 a_wnan a_wnan f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan a_wnan a_wnan p_nic-idel f0_nic-luk1 f2_nic-luk1 p_nic-dfim f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 a_wi p_nic-bi1 f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 a_wi p_nic-idbl f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan a_wnan f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan p_nic-imp f1_nic-luk1 f2_nic-luk1 p_nic-dfim f1_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi p_nic-bi2 f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 p_nic-swap f1_nic-luk1 f2_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan p_nic-ich f1_nic-luk1 f2_nic-luk1 a_wi f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan p_nic-imp f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan a_wnan p_nic-ich f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 a_wnan a_wnan f2_nic-luk1 f2_nic-luk1 a_wnan f1_nic-luk1 a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan f0_nic-luk1 f2_nic-luk1 f2_nic-luk1 a_wnan a_wnan a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan a_wnan p_nic-ich f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi p_nic-dfim f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi p_nic-bi1 f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi p_nic-ich f0_nic-luk1 f1_nic-luk1 a_wi f0_nic-luk1 f1_nic-luk1 f1_nic-luk1 a_wnan a_wnan f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi p_nic-ich f0_nic-luk1 f1_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi p_nic-dfim f0_nic-luk1 f1_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi a_wnan a_wnan f0_nic-luk1 f1_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi a_wi p_nic-bi1 f0_nic-luk1 f1_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi a_wnan a_wnan f0_nic-luk1 f1_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi a_wi f0_nic-luk1 f1_nic-luk1 a_wi f1_nic-luk1 f2_nic-luk1 a_wi f0_nic-luk1 f2_nic-luk1 a_wi a_wi a_wi p_nic-mp $.
$}

$(Proof of ~ luk-2 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph  $.
	f0_nic-luk2 $f wff ph $.
	p_nic-luk2 $p |- ( ( -. ph -> ph ) -> ph ) $= f0_nic-luk2 a_wn f0_nic-luk2 p_nic-dfim f0_nic-luk2 a_wn f0_nic-luk2 f0_nic-luk2 a_wnan a_wnan f0_nic-luk2 a_wn f0_nic-luk2 a_wi p_nic-bi2 f0_nic-luk2 p_nic-dfneg f0_nic-luk2 f0_nic-luk2 a_wnan p_nic-id f0_nic-luk2 f0_nic-luk2 a_wnan f0_nic-luk2 a_wn a_wnan f0_nic-luk2 a_wn f0_nic-luk2 a_wn a_wnan f0_nic-luk2 f0_nic-luk2 a_wnan f0_nic-luk2 f0_nic-luk2 a_wnan a_wnan f0_nic-luk2 f0_nic-luk2 a_wnan p_nic-iimp1 f0_nic-luk2 a_wn f0_nic-luk2 f0_nic-luk2 a_wnan f0_nic-luk2 f0_nic-luk2 a_wnan p_nic-isw2 f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 a_wn f0_nic-luk2 f0_nic-luk2 a_wnan a_wnan f0_nic-luk2 a_wn f0_nic-luk2 f0_nic-luk2 a_wnan a_wnan f0_nic-luk2 f0_nic-luk2 a_wnan p_nic-iimp1 f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 f0_nic-luk2 a_wnan p_nic-isw1 f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 p_nic-dfim f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 f0_nic-luk2 a_wnan a_wnan f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 a_wi p_nic-bi1 f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 f0_nic-luk2 a_wnan a_wnan f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 a_wi f0_nic-luk2 a_wn f0_nic-luk2 a_wi f0_nic-luk2 a_wi p_nic-mp $.
$}

$(Proof of ~ luk-3 from ~ nic-ax and ~ nic-mp .  (Contributed by Jeff
     Hoffman, 18-Nov-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)

${
	$v ph ps  $.
	f0_nic-luk3 $f wff ph $.
	f1_nic-luk3 $f wff ps $.
	p_nic-luk3 $p |- ( ph -> ( -. ph -> ps ) ) $= f0_nic-luk3 a_wn f1_nic-luk3 p_nic-dfim f0_nic-luk3 a_wn f1_nic-luk3 f1_nic-luk3 a_wnan a_wnan f0_nic-luk3 a_wn f1_nic-luk3 a_wi p_nic-bi1 f0_nic-luk3 p_nic-dfneg f0_nic-luk3 f0_nic-luk3 a_wnan f0_nic-luk3 a_wn p_nic-bi2 f0_nic-luk3 p_nic-id f0_nic-luk3 a_wn f0_nic-luk3 f0_nic-luk3 a_wnan f0_nic-luk3 f0_nic-luk3 a_wnan f0_nic-luk3 p_nic-iimp1 f0_nic-luk3 a_wn f1_nic-luk3 f1_nic-luk3 a_wnan f0_nic-luk3 a_wn f1_nic-luk3 a_wi f0_nic-luk3 p_nic-iimp2 f0_nic-luk3 f0_nic-luk3 a_wn f1_nic-luk3 a_wi p_nic-dfim f0_nic-luk3 f0_nic-luk3 a_wn f1_nic-luk3 a_wi f0_nic-luk3 a_wn f1_nic-luk3 a_wi a_wnan a_wnan f0_nic-luk3 f0_nic-luk3 a_wn f1_nic-luk3 a_wi a_wi p_nic-bi1 f0_nic-luk3 f0_nic-luk3 a_wn f1_nic-luk3 a_wi f0_nic-luk3 a_wn f1_nic-luk3 a_wi a_wnan a_wnan f0_nic-luk3 f0_nic-luk3 a_wn f1_nic-luk3 a_wi a_wi f0_nic-luk3 f0_nic-luk3 a_wn f1_nic-luk3 a_wi a_wi p_nic-mp $.
$}


