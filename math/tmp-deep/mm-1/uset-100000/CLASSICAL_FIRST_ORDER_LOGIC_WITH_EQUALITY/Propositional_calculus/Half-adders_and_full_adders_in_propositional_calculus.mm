$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Auxiliary_theorems_for_Alan_Sare_s_virtual_deduction_tool,_part_1.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Half-adders and full adders in propositional calculus

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus deals with truth values, which can be interpreted as
  bits. Using this, we can define the half-adder in pure propositional
  calculus, and show its basic properties.

$)

$c hadd $.

$c cadd $.

$c , $.

$(Comma (also used for unordered pair notation later) $)

$(Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_whad $f wff ph $.
	f1_whad $f wff ps $.
	f2_whad $f wff ch $.
	a_whad $a wff hadd ( ph , ps , ch ) $.
$}

$(Define the half adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_wcad $f wff ph $.
	f1_wcad $f wff ps $.
	f2_wcad $f wff ch $.
	a_wcad $a wff cadd ( ph , ps , ch ) $.
$}

$(Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_df-had $f wff ph $.
	f1_df-had $f wff ps $.
	f2_df-had $f wff ch $.
	a_df-had $a |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $.
$}

$(Define the half adder carry, which is true when at least two arguments are
     true.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_df-cad $f wff ph $.
	f1_df-cad $f wff ps $.
	f2_df-cad $f wff ch $.
	a_df-cad $a |- ( cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $.
$}

$(Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_hadbi123d $f wff ph $.
	f1_hadbi123d $f wff ps $.
	f2_hadbi123d $f wff ch $.
	f3_hadbi123d $f wff th $.
	f4_hadbi123d $f wff ta $.
	f5_hadbi123d $f wff et $.
	f6_hadbi123d $f wff ze $.
	e0_hadbi123d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_hadbi123d $e |- ( ph -> ( th <-> ta ) ) $.
	e2_hadbi123d $e |- ( ph -> ( et <-> ze ) ) $.
	p_hadbi123d $p |- ( ph -> ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) ) $= e0_hadbi123d e1_hadbi123d f0_hadbi123d f1_hadbi123d f2_hadbi123d f3_hadbi123d f4_hadbi123d p_xorbi12d e2_hadbi123d f0_hadbi123d f1_hadbi123d f3_hadbi123d a_wxo f2_hadbi123d f4_hadbi123d a_wxo f5_hadbi123d f6_hadbi123d p_xorbi12d f1_hadbi123d f3_hadbi123d f5_hadbi123d a_df-had f2_hadbi123d f4_hadbi123d f6_hadbi123d a_df-had f0_hadbi123d f1_hadbi123d f3_hadbi123d a_wxo f5_hadbi123d a_wxo f2_hadbi123d f4_hadbi123d a_wxo f6_hadbi123d a_wxo f1_hadbi123d f3_hadbi123d f5_hadbi123d a_whad f2_hadbi123d f4_hadbi123d f6_hadbi123d a_whad p_3bitr4g $.
$}

$(Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)

${
	$v ph ps ch th ta et ze  $.
	f0_cadbi123d $f wff ph $.
	f1_cadbi123d $f wff ps $.
	f2_cadbi123d $f wff ch $.
	f3_cadbi123d $f wff th $.
	f4_cadbi123d $f wff ta $.
	f5_cadbi123d $f wff et $.
	f6_cadbi123d $f wff ze $.
	e0_cadbi123d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_cadbi123d $e |- ( ph -> ( th <-> ta ) ) $.
	e2_cadbi123d $e |- ( ph -> ( et <-> ze ) ) $.
	p_cadbi123d $p |- ( ph -> ( cadd ( ps , th , et ) <-> cadd ( ch , ta , ze ) ) ) $= e0_cadbi123d e1_cadbi123d f0_cadbi123d f1_cadbi123d f2_cadbi123d f3_cadbi123d f4_cadbi123d p_anbi12d e2_cadbi123d e0_cadbi123d e1_cadbi123d f0_cadbi123d f1_cadbi123d f2_cadbi123d f3_cadbi123d f4_cadbi123d p_xorbi12d f0_cadbi123d f5_cadbi123d f6_cadbi123d f1_cadbi123d f3_cadbi123d a_wxo f2_cadbi123d f4_cadbi123d a_wxo p_anbi12d f0_cadbi123d f1_cadbi123d f3_cadbi123d a_wa f2_cadbi123d f4_cadbi123d a_wa f5_cadbi123d f1_cadbi123d f3_cadbi123d a_wxo a_wa f6_cadbi123d f2_cadbi123d f4_cadbi123d a_wxo a_wa p_orbi12d f1_cadbi123d f3_cadbi123d f5_cadbi123d a_df-cad f2_cadbi123d f4_cadbi123d f6_cadbi123d a_df-cad f0_cadbi123d f1_cadbi123d f3_cadbi123d a_wa f5_cadbi123d f1_cadbi123d f3_cadbi123d a_wxo a_wa a_wo f2_cadbi123d f4_cadbi123d a_wa f6_cadbi123d f2_cadbi123d f4_cadbi123d a_wxo a_wa a_wo f1_cadbi123d f3_cadbi123d f5_cadbi123d a_wcad f2_cadbi123d f4_cadbi123d f6_cadbi123d a_wcad p_3bitr4g $.
$}

$(Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)

${
	$v ph ps ch th ta et  $.
	f0_hadbi123i $f wff ph $.
	f1_hadbi123i $f wff ps $.
	f2_hadbi123i $f wff ch $.
	f3_hadbi123i $f wff th $.
	f4_hadbi123i $f wff ta $.
	f5_hadbi123i $f wff et $.
	e0_hadbi123i $e |- ( ph <-> ps ) $.
	e1_hadbi123i $e |- ( ch <-> th ) $.
	e2_hadbi123i $e |- ( ta <-> et ) $.
	p_hadbi123i $p |- ( hadd ( ph , ch , ta ) <-> hadd ( ps , th , et ) ) $= e0_hadbi123i f0_hadbi123i f1_hadbi123i a_wb a_wtru p_a1i e1_hadbi123i f2_hadbi123i f3_hadbi123i a_wb a_wtru p_a1i e2_hadbi123i f4_hadbi123i f5_hadbi123i a_wb a_wtru p_a1i a_wtru f0_hadbi123i f1_hadbi123i f2_hadbi123i f3_hadbi123i f4_hadbi123i f5_hadbi123i p_hadbi123d f0_hadbi123i f2_hadbi123i f4_hadbi123i a_whad f1_hadbi123i f3_hadbi123i f5_hadbi123i a_whad a_wb p_trud $.
$}

$(Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)

${
	$v ph ps ch th ta et  $.
	f0_cadbi123i $f wff ph $.
	f1_cadbi123i $f wff ps $.
	f2_cadbi123i $f wff ch $.
	f3_cadbi123i $f wff th $.
	f4_cadbi123i $f wff ta $.
	f5_cadbi123i $f wff et $.
	e0_cadbi123i $e |- ( ph <-> ps ) $.
	e1_cadbi123i $e |- ( ch <-> th ) $.
	e2_cadbi123i $e |- ( ta <-> et ) $.
	p_cadbi123i $p |- ( cadd ( ph , ch , ta ) <-> cadd ( ps , th , et ) ) $= e0_cadbi123i f0_cadbi123i f1_cadbi123i a_wb a_wtru p_a1i e1_cadbi123i f2_cadbi123i f3_cadbi123i a_wb a_wtru p_a1i e2_cadbi123i f4_cadbi123i f5_cadbi123i a_wb a_wtru p_a1i a_wtru f0_cadbi123i f1_cadbi123i f2_cadbi123i f3_cadbi123i f4_cadbi123i f5_cadbi123i p_cadbi123d f0_cadbi123i f2_cadbi123i f4_cadbi123i a_wcad f1_cadbi123i f3_cadbi123i f5_cadbi123i a_wcad a_wb p_trud $.
$}

$(Associative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_hadass $f wff ph $.
	f1_hadass $f wff ps $.
	f2_hadass $f wff ch $.
	p_hadass $p |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $= f0_hadass f1_hadass f2_hadass a_df-had f0_hadass f1_hadass f2_hadass p_xorass f0_hadass f1_hadass f2_hadass a_whad f0_hadass f1_hadass a_wxo f2_hadass a_wxo f0_hadass f1_hadass f2_hadass a_wxo a_wxo p_bitri $.
$}

$(The half adder is the same as the triple biconditional.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_hadbi $f wff ph $.
	f1_hadbi $f wff ps $.
	f2_hadbi $f wff ch $.
	p_hadbi $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) ) $= f0_hadbi f1_hadbi a_wxo f2_hadbi a_df-xor f0_hadbi f1_hadbi f2_hadbi a_df-had f0_hadbi f1_hadbi p_xnor f0_hadbi f1_hadbi a_wb f0_hadbi f1_hadbi a_wxo a_wn f2_hadbi p_bibi1i f0_hadbi f1_hadbi a_wxo f2_hadbi p_nbbn f0_hadbi f1_hadbi a_wb f2_hadbi a_wb f0_hadbi f1_hadbi a_wxo a_wn f2_hadbi a_wb f0_hadbi f1_hadbi a_wxo f2_hadbi a_wb a_wn p_bitri f0_hadbi f1_hadbi a_wxo f2_hadbi a_wxo f0_hadbi f1_hadbi a_wxo f2_hadbi a_wb a_wn f0_hadbi f1_hadbi f2_hadbi a_whad f0_hadbi f1_hadbi a_wb f2_hadbi a_wb p_3bitr4i $.
$}

$(Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_hadcoma $f wff ph $.
	f1_hadcoma $f wff ps $.
	f2_hadcoma $f wff ch $.
	p_hadcoma $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) ) $= f0_hadcoma f1_hadcoma p_xorcom f2_hadcoma p_biid f0_hadcoma f1_hadcoma a_wxo f1_hadcoma f0_hadcoma a_wxo f2_hadcoma f2_hadcoma p_xorbi12i f0_hadcoma f1_hadcoma f2_hadcoma a_df-had f1_hadcoma f0_hadcoma f2_hadcoma a_df-had f0_hadcoma f1_hadcoma a_wxo f2_hadcoma a_wxo f1_hadcoma f0_hadcoma a_wxo f2_hadcoma a_wxo f0_hadcoma f1_hadcoma f2_hadcoma a_whad f1_hadcoma f0_hadcoma f2_hadcoma a_whad p_3bitr4i $.
$}

$(Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_hadcomb $f wff ph $.
	f1_hadcomb $f wff ps $.
	f2_hadcomb $f wff ch $.
	p_hadcomb $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) ) $= f0_hadcomb p_biid f1_hadcomb f2_hadcomb p_xorcom f0_hadcomb f0_hadcomb f1_hadcomb f2_hadcomb a_wxo f2_hadcomb f1_hadcomb a_wxo p_xorbi12i f0_hadcomb f1_hadcomb f2_hadcomb p_hadass f0_hadcomb f2_hadcomb f1_hadcomb p_hadass f0_hadcomb f1_hadcomb f2_hadcomb a_wxo a_wxo f0_hadcomb f2_hadcomb f1_hadcomb a_wxo a_wxo f0_hadcomb f1_hadcomb f2_hadcomb a_whad f0_hadcomb f2_hadcomb f1_hadcomb a_whad p_3bitr4i $.
$}

$(Rotation law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_hadrot $f wff ph $.
	f1_hadrot $f wff ps $.
	f2_hadrot $f wff ch $.
	p_hadrot $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) ) $= f0_hadrot f1_hadrot f2_hadrot p_hadcoma f1_hadrot f0_hadrot f2_hadrot p_hadcomb f0_hadrot f1_hadrot f2_hadrot a_whad f1_hadrot f0_hadrot f2_hadrot a_whad f1_hadrot f2_hadrot f0_hadrot a_whad p_bitri $.
$}

$(Write the adder carry in disjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cador $f wff ph $.
	f1_cador $f wff ps $.
	f2_cador $f wff ch $.
	p_cador $p |- ( cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $= f0_cador f1_cador f2_cador a_df-cad f0_cador f1_cador p_xor2 f0_cador f1_cador a_wxo f0_cador f1_cador a_wo f0_cador f1_cador a_wa a_wn p_rbaib f0_cador f1_cador a_wa a_wn f0_cador f1_cador a_wxo f0_cador f1_cador a_wo f2_cador p_anbi1d f0_cador f1_cador a_wxo f2_cador p_ancom f0_cador f1_cador f2_cador p_andir f0_cador f1_cador a_wa a_wn f0_cador f1_cador a_wxo f2_cador a_wa f0_cador f1_cador a_wo f2_cador a_wa f2_cador f0_cador f1_cador a_wxo a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_wo p_3bitr3g f0_cador f1_cador a_wa a_wn f2_cador f0_cador f1_cador a_wxo a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_wo p_pm5.74i f0_cador f1_cador a_wa f2_cador f0_cador f1_cador a_wxo a_wa a_df-or f0_cador f1_cador a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa p_3orass f0_cador f1_cador a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_wo a_df-or f0_cador f1_cador a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_w3o f0_cador f1_cador a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_wo a_wo f0_cador f1_cador a_wa a_wn f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_wo a_wi p_bitri f0_cador f1_cador a_wa a_wn f2_cador f0_cador f1_cador a_wxo a_wa a_wi f0_cador f1_cador a_wa a_wn f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_wo a_wi f0_cador f1_cador a_wa f2_cador f0_cador f1_cador a_wxo a_wa a_wo f0_cador f1_cador a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_w3o p_3bitr4i f0_cador f1_cador f2_cador a_wcad f0_cador f1_cador a_wa f2_cador f0_cador f1_cador a_wxo a_wa a_wo f0_cador f1_cador a_wa f0_cador f2_cador a_wa f1_cador f2_cador a_wa a_w3o p_bitri $.
$}

$(Write the adder carry in conjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cadan $f wff ph $.
	f1_cadan $f wff ps $.
	f2_cadan $f wff ch $.
	p_cadan $p |- ( cadd ( ph , ps , ch ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $= f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan f2_cadan p_ordi f0_cadan f2_cadan f1_cadan p_ordir f0_cadan f1_cadan p_simpr f0_cadan f1_cadan a_wa f1_cadan p_con3i f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa p_biorf f1_cadan a_wn f0_cadan f1_cadan a_wa a_wn f0_cadan f2_cadan a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wb p_syl f1_cadan a_wn f0_cadan f2_cadan a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo p_pm5.74i f1_cadan f0_cadan f2_cadan a_wa a_df-or f1_cadan f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_df-or f1_cadan a_wn f0_cadan f2_cadan a_wa a_wi f1_cadan a_wn f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wi f1_cadan f0_cadan f2_cadan a_wa a_wo f1_cadan f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wo p_3bitr4i f0_cadan f2_cadan a_wa f1_cadan p_orcom f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan p_orcom f1_cadan f0_cadan f2_cadan a_wa a_wo f1_cadan f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wo f0_cadan f2_cadan a_wa f1_cadan a_wo f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan a_wo p_3bitr4i f2_cadan f1_cadan p_orcom f2_cadan f1_cadan a_wo f1_cadan f2_cadan a_wo f0_cadan f1_cadan a_wo p_anbi2i f0_cadan f2_cadan a_wa f1_cadan a_wo f0_cadan f1_cadan a_wo f2_cadan f1_cadan a_wo a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan a_wo f0_cadan f1_cadan a_wo f1_cadan f2_cadan a_wo a_wa p_3bitr3i f0_cadan f2_cadan p_simpr f0_cadan f2_cadan a_wa f2_cadan p_con3i f0_cadan f2_cadan a_wa f0_cadan f1_cadan a_wa p_biorf f0_cadan f2_cadan a_wa f0_cadan f1_cadan a_wa p_orcom f0_cadan f2_cadan a_wa a_wn f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa f0_cadan f1_cadan a_wa a_wo f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo p_syl6bb f2_cadan a_wn f0_cadan f2_cadan a_wa a_wn f0_cadan f1_cadan a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wb p_syl f2_cadan a_wn f0_cadan f1_cadan a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo p_pm5.74i f2_cadan f0_cadan f1_cadan a_wa a_df-or f2_cadan f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_df-or f2_cadan a_wn f0_cadan f1_cadan a_wa a_wi f2_cadan a_wn f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wi f2_cadan f0_cadan f1_cadan a_wa a_wo f2_cadan f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wo p_3bitr4i f0_cadan f1_cadan a_wa f2_cadan p_orcom f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f2_cadan p_orcom f2_cadan f0_cadan f1_cadan a_wa a_wo f2_cadan f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo a_wo f0_cadan f1_cadan a_wa f2_cadan a_wo f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f2_cadan a_wo p_3bitr4i f0_cadan f1_cadan f2_cadan p_ordir f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f2_cadan a_wo f0_cadan f1_cadan a_wa f2_cadan a_wo f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo a_wa p_bitr3i f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan a_wo f0_cadan f1_cadan a_wo f1_cadan f2_cadan a_wo a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f2_cadan a_wo f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo a_wa p_anbi12i f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan f2_cadan a_wa a_wo f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan a_wo f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f2_cadan a_wo a_wa f0_cadan f1_cadan a_wo f1_cadan f2_cadan a_wo a_wa f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo a_wa a_wa p_bitri f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa f1_cadan f2_cadan a_wa a_df-3or f0_cadan f1_cadan a_wo f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo p_anandir f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa a_wo f1_cadan f2_cadan a_wa a_wo f0_cadan f1_cadan a_wo f1_cadan f2_cadan a_wo a_wa f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo a_wa a_wa f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa f1_cadan f2_cadan a_wa a_w3o f0_cadan f1_cadan a_wo f0_cadan f2_cadan a_wo a_wa f1_cadan f2_cadan a_wo a_wa p_3bitr4i f0_cadan f1_cadan f2_cadan p_cador f0_cadan f1_cadan a_wo f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo a_df-3an f0_cadan f1_cadan a_wa f0_cadan f2_cadan a_wa f1_cadan f2_cadan a_wa a_w3o f0_cadan f1_cadan a_wo f0_cadan f2_cadan a_wo a_wa f1_cadan f2_cadan a_wo a_wa f0_cadan f1_cadan f2_cadan a_wcad f0_cadan f1_cadan a_wo f0_cadan f2_cadan a_wo f1_cadan f2_cadan a_wo a_w3a p_3bitr4i $.
$}

$(The half adder distributes over negation.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_hadnot $f wff ph $.
	f1_hadnot $f wff ps $.
	f2_hadnot $f wff ch $.
	p_hadnot $p |- ( -. hadd ( ph , ps , ch ) <-> hadd ( -. ph , -. ps , -. ch ) ) $= f0_hadnot f1_hadnot p_xorneg f2_hadnot a_wn p_biid f0_hadnot a_wn f1_hadnot a_wn a_wxo f0_hadnot f1_hadnot a_wxo f2_hadnot a_wn f2_hadnot a_wn p_xorbi12i f0_hadnot f1_hadnot a_wxo f2_hadnot p_xorneg2 f0_hadnot a_wn f1_hadnot a_wn a_wxo f2_hadnot a_wn a_wxo f0_hadnot f1_hadnot a_wxo f2_hadnot a_wn a_wxo f0_hadnot f1_hadnot a_wxo f2_hadnot a_wxo a_wn p_bitr2i f0_hadnot f1_hadnot f2_hadnot a_df-had f0_hadnot f1_hadnot f2_hadnot a_whad f0_hadnot f1_hadnot a_wxo f2_hadnot a_wxo p_notbii f0_hadnot a_wn f1_hadnot a_wn f2_hadnot a_wn a_df-had f0_hadnot f1_hadnot a_wxo f2_hadnot a_wxo a_wn f0_hadnot a_wn f1_hadnot a_wn a_wxo f2_hadnot a_wn a_wxo f0_hadnot f1_hadnot f2_hadnot a_whad a_wn f0_hadnot a_wn f1_hadnot a_wn f2_hadnot a_wn a_whad p_3bitr4i $.
$}

$(The adder carry distributes over negation.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cadnot $f wff ph $.
	f1_cadnot $f wff ps $.
	f2_cadnot $f wff ch $.
	p_cadnot $p |- ( -. cadd ( ph , ps , ch ) <-> cadd ( -. ph , -. ps , -. ch ) ) $= f0_cadnot f1_cadnot a_wa f0_cadnot f2_cadnot a_wa f1_cadnot f2_cadnot a_wa p_3ioran f0_cadnot f1_cadnot p_ianor f0_cadnot f2_cadnot p_ianor f1_cadnot f2_cadnot p_ianor f0_cadnot f1_cadnot a_wa a_wn f0_cadnot a_wn f1_cadnot a_wn a_wo f0_cadnot f2_cadnot a_wa a_wn f0_cadnot a_wn f2_cadnot a_wn a_wo f1_cadnot f2_cadnot a_wa a_wn f1_cadnot a_wn f2_cadnot a_wn a_wo p_3anbi123i f0_cadnot f1_cadnot a_wa f0_cadnot f2_cadnot a_wa f1_cadnot f2_cadnot a_wa a_w3o a_wn f0_cadnot f1_cadnot a_wa a_wn f0_cadnot f2_cadnot a_wa a_wn f1_cadnot f2_cadnot a_wa a_wn a_w3a f0_cadnot a_wn f1_cadnot a_wn a_wo f0_cadnot a_wn f2_cadnot a_wn a_wo f1_cadnot a_wn f2_cadnot a_wn a_wo a_w3a p_bitri f0_cadnot f1_cadnot f2_cadnot p_cador f0_cadnot f1_cadnot f2_cadnot a_wcad f0_cadnot f1_cadnot a_wa f0_cadnot f2_cadnot a_wa f1_cadnot f2_cadnot a_wa a_w3o p_notbii f0_cadnot a_wn f1_cadnot a_wn f2_cadnot a_wn p_cadan f0_cadnot f1_cadnot a_wa f0_cadnot f2_cadnot a_wa f1_cadnot f2_cadnot a_wa a_w3o a_wn f0_cadnot a_wn f1_cadnot a_wn a_wo f0_cadnot a_wn f2_cadnot a_wn a_wo f1_cadnot a_wn f2_cadnot a_wn a_wo a_w3a f0_cadnot f1_cadnot f2_cadnot a_wcad a_wn f0_cadnot a_wn f1_cadnot a_wn f2_cadnot a_wn a_wcad p_3bitr4i $.
$}

$(Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cadcoma $f wff ph $.
	f1_cadcoma $f wff ps $.
	f2_cadcoma $f wff ch $.
	p_cadcoma $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ph , ch ) ) $= f0_cadcoma f1_cadcoma p_ancom f0_cadcoma f1_cadcoma p_xorcom f0_cadcoma f1_cadcoma a_wxo f1_cadcoma f0_cadcoma a_wxo f2_cadcoma p_anbi2i f0_cadcoma f1_cadcoma a_wa f1_cadcoma f0_cadcoma a_wa f2_cadcoma f0_cadcoma f1_cadcoma a_wxo a_wa f2_cadcoma f1_cadcoma f0_cadcoma a_wxo a_wa p_orbi12i f0_cadcoma f1_cadcoma f2_cadcoma a_df-cad f1_cadcoma f0_cadcoma f2_cadcoma a_df-cad f0_cadcoma f1_cadcoma a_wa f2_cadcoma f0_cadcoma f1_cadcoma a_wxo a_wa a_wo f1_cadcoma f0_cadcoma a_wa f2_cadcoma f1_cadcoma f0_cadcoma a_wxo a_wa a_wo f0_cadcoma f1_cadcoma f2_cadcoma a_wcad f1_cadcoma f0_cadcoma f2_cadcoma a_wcad p_3bitr4i $.
$}

$(Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cadcomb $f wff ph $.
	f1_cadcomb $f wff ps $.
	f2_cadcomb $f wff ch $.
	p_cadcomb $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ph , ch , ps ) ) $= f0_cadcomb f1_cadcomb a_wa f0_cadcomb f2_cadcomb a_wa f1_cadcomb f2_cadcomb a_wa p_3orcoma f0_cadcomb f2_cadcomb a_wa p_biid f0_cadcomb f1_cadcomb a_wa p_biid f1_cadcomb f2_cadcomb p_ancom f0_cadcomb f2_cadcomb a_wa f0_cadcomb f2_cadcomb a_wa f0_cadcomb f1_cadcomb a_wa f0_cadcomb f1_cadcomb a_wa f1_cadcomb f2_cadcomb a_wa f2_cadcomb f1_cadcomb a_wa p_3orbi123i f0_cadcomb f1_cadcomb a_wa f0_cadcomb f2_cadcomb a_wa f1_cadcomb f2_cadcomb a_wa a_w3o f0_cadcomb f2_cadcomb a_wa f0_cadcomb f1_cadcomb a_wa f1_cadcomb f2_cadcomb a_wa a_w3o f0_cadcomb f2_cadcomb a_wa f0_cadcomb f1_cadcomb a_wa f2_cadcomb f1_cadcomb a_wa a_w3o p_bitri f0_cadcomb f1_cadcomb f2_cadcomb p_cador f0_cadcomb f2_cadcomb f1_cadcomb p_cador f0_cadcomb f1_cadcomb a_wa f0_cadcomb f2_cadcomb a_wa f1_cadcomb f2_cadcomb a_wa a_w3o f0_cadcomb f2_cadcomb a_wa f0_cadcomb f1_cadcomb a_wa f2_cadcomb f1_cadcomb a_wa a_w3o f0_cadcomb f1_cadcomb f2_cadcomb a_wcad f0_cadcomb f2_cadcomb f1_cadcomb a_wcad p_3bitr4i $.
$}

$(Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cadrot $f wff ph $.
	f1_cadrot $f wff ps $.
	f2_cadrot $f wff ch $.
	p_cadrot $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ch , ph ) ) $= f0_cadrot f1_cadrot f2_cadrot p_cadcoma f1_cadrot f0_cadrot f2_cadrot p_cadcomb f0_cadrot f1_cadrot f2_cadrot a_wcad f1_cadrot f0_cadrot f2_cadrot a_wcad f1_cadrot f2_cadrot f0_cadrot a_wcad p_bitri $.
$}

$(If one parameter is true, the adder carry is true exactly when at least
     one of the other parameters is true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cad1 $f wff ph $.
	f1_cad1 $f wff ps $.
	f2_cad1 $f wff ch $.
	p_cad1 $p |- ( ch -> ( cadd ( ph , ps , ch ) <-> ( ph \/ ps ) ) ) $= f2_cad1 f0_cad1 f1_cad1 a_wxo p_ibar f2_cad1 f0_cad1 f1_cad1 a_wxo f2_cad1 f0_cad1 f1_cad1 a_wxo a_wa p_bicomd f2_cad1 f2_cad1 f0_cad1 f1_cad1 a_wxo a_wa f0_cad1 f1_cad1 a_wxo f0_cad1 f1_cad1 a_wa p_orbi2d f0_cad1 f1_cad1 f2_cad1 a_df-cad f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wo p_pm5.63 f0_cad1 f1_cad1 a_wo f0_cad1 f1_cad1 a_wa p_olc f0_cad1 f1_cad1 p_orc f0_cad1 f0_cad1 f1_cad1 a_wo f1_cad1 p_adantr f0_cad1 f1_cad1 a_wo p_id f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wo f0_cad1 f1_cad1 a_wo p_jaoi f0_cad1 f1_cad1 a_wo f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wo a_wo p_impbii f0_cad1 f1_cad1 p_xor2 f0_cad1 f1_cad1 a_wo f0_cad1 f1_cad1 a_wa a_wn p_ancom f0_cad1 f1_cad1 a_wxo f0_cad1 f1_cad1 a_wo f0_cad1 f1_cad1 a_wa a_wn a_wa f0_cad1 f1_cad1 a_wa a_wn f0_cad1 f1_cad1 a_wo a_wa p_bitri f0_cad1 f1_cad1 a_wxo f0_cad1 f1_cad1 a_wa a_wn f0_cad1 f1_cad1 a_wo a_wa f0_cad1 f1_cad1 a_wa p_orbi2i f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wo a_wo f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wa a_wn f0_cad1 f1_cad1 a_wo a_wa a_wo f0_cad1 f1_cad1 a_wo f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wxo a_wo p_3bitr4i f2_cad1 f0_cad1 f1_cad1 a_wa f2_cad1 f0_cad1 f1_cad1 a_wxo a_wa a_wo f0_cad1 f1_cad1 a_wa f0_cad1 f1_cad1 a_wxo a_wo f0_cad1 f1_cad1 f2_cad1 a_wcad f0_cad1 f1_cad1 a_wo p_3bitr4g $.
$}

$(If two parameters are true, the adder carry is true.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cad11 $f wff ph $.
	f1_cad11 $f wff ps $.
	f2_cad11 $f wff ch $.
	p_cad11 $p |- ( ( ph /\ ps ) -> cadd ( ph , ps , ch ) ) $= f0_cad11 f1_cad11 a_wa f2_cad11 f0_cad11 f1_cad11 a_wxo a_wa p_orc f0_cad11 f1_cad11 f2_cad11 a_df-cad f0_cad11 f1_cad11 a_wa f0_cad11 f1_cad11 a_wa f2_cad11 f0_cad11 f1_cad11 a_wxo a_wa a_wo f0_cad11 f1_cad11 f2_cad11 a_wcad p_sylibr $.
$}

$(If one parameter is false, the adder carry is true exactly when both of
     the other two parameters are true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_cad0 $f wff ph $.
	f1_cad0 $f wff ps $.
	f2_cad0 $f wff ch $.
	p_cad0 $p |- ( -. ch -> ( cadd ( ph , ps , ch ) <-> ( ph /\ ps ) ) ) $= f0_cad0 f1_cad0 f2_cad0 a_df-cad f2_cad0 a_wn f0_cad0 f1_cad0 a_wa p_idd f2_cad0 f0_cad0 f1_cad0 a_wa p_pm2.21 f2_cad0 a_wn f2_cad0 f0_cad0 f1_cad0 a_wa f0_cad0 f1_cad0 a_wxo p_adantrd f2_cad0 a_wn f0_cad0 f1_cad0 a_wa f0_cad0 f1_cad0 a_wa f2_cad0 f0_cad0 f1_cad0 a_wxo a_wa p_jaod f0_cad0 f1_cad0 a_wa f2_cad0 f0_cad0 f1_cad0 a_wxo a_wa p_orc f2_cad0 a_wn f0_cad0 f1_cad0 a_wa f2_cad0 f0_cad0 f1_cad0 a_wxo a_wa a_wo f0_cad0 f1_cad0 a_wa p_impbid1 f0_cad0 f1_cad0 f2_cad0 a_wcad f0_cad0 f1_cad0 a_wa f2_cad0 f0_cad0 f1_cad0 a_wxo a_wa a_wo f2_cad0 a_wn f0_cad0 f1_cad0 a_wa p_syl5bb $.
$}

$(Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph  $.
	f0_cadtru $f wff ph $.
	p_cadtru $p |- cadd ( T. , T. , ph ) $= p_tru p_tru a_wtru a_wtru f0_cadtru p_cad11 a_wtru a_wtru a_wtru a_wtru f0_cadtru a_wcad p_mp2an $.
$}

$(If the first parameter is true, the half adder is equivalent to the
     equality of the other two inputs.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_had1 $f wff ph $.
	f1_had1 $f wff ps $.
	f2_had1 $f wff ch $.
	p_had1 $p |- ( ph -> ( hadd ( ph , ps , ch ) <-> ( ps <-> ch ) ) ) $= f0_had1 f1_had1 f2_had1 p_hadbi f0_had1 f1_had1 f2_had1 p_biass f0_had1 f1_had1 f2_had1 a_whad f0_had1 f1_had1 a_wb f2_had1 a_wb f0_had1 f1_had1 f2_had1 a_wb a_wb p_bitri f0_had1 p_id f0_had1 f1_had1 f2_had1 a_wb p_biidd f0_had1 f0_had1 f1_had1 f2_had1 a_wb f1_had1 f2_had1 a_wb a_wb p_2thd f0_had1 f1_had1 f2_had1 a_wb f1_had1 f2_had1 a_wb p_biass f0_had1 f0_had1 f1_had1 f2_had1 a_wb f1_had1 f2_had1 a_wb a_wb a_wb f0_had1 f1_had1 f2_had1 a_wb a_wb f1_had1 f2_had1 a_wb a_wb p_sylibr f0_had1 f1_had1 f2_had1 a_whad f0_had1 f1_had1 f2_had1 a_wb a_wb f0_had1 f1_had1 f2_had1 a_wb p_syl5bb $.
$}

$(If the first parameter is false, the half adder is equivalent to the XOR
     of the other two inputs.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps ch  $.
	f0_had0 $f wff ph $.
	f1_had0 $f wff ps $.
	f2_had0 $f wff ch $.
	p_had0 $p |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) ) $= f0_had0 a_wn f1_had0 a_wn f2_had0 a_wn p_had1 f0_had0 f1_had0 f2_had0 p_hadnot f1_had0 a_wn f2_had0 a_wn a_df-xor f1_had0 f2_had0 p_xorneg f1_had0 a_wn f2_had0 a_wn a_wb a_wn f1_had0 a_wn f2_had0 a_wn a_wxo f1_had0 f2_had0 a_wxo p_bitr3i f1_had0 a_wn f2_had0 a_wn a_wb f1_had0 f2_had0 a_wxo p_con1bii f0_had0 a_wn f0_had0 a_wn f1_had0 a_wn f2_had0 a_wn a_whad f1_had0 a_wn f2_had0 a_wn a_wb f0_had0 f1_had0 f2_had0 a_whad a_wn f1_had0 f2_had0 a_wxo a_wn p_3bitr4g f0_had0 a_wn f0_had0 f1_had0 f2_had0 a_whad f1_had0 f2_had0 a_wxo p_con4bid $.
$}


