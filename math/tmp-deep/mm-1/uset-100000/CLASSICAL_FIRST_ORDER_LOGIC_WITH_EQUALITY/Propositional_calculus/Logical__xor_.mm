$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical__nand__(Sheffer_stroke).mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'xor'

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Declare connective for exclusive disjunction ('xor'). $)

$c \/_ $.

$(Underlined 'vee' (read:  'xor') $)

$(Extend wff definition to include exclusive disjunction ('xor'). $)

${
	$v ph ps  $.
	f0_wxo $f wff ph $.
	f1_wxo $f wff ps $.
	a_wxo $a wff ( ph \/_ ps ) $.
$}

$(Define exclusive disjunction (logical 'xor').  Return true if either the
     left or right, but not both, are true.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. \/_ T. ) <-> F. ) `
     ( ~ truxortru ), ` ( ( T. \/_ F. ) <-> T. ) ` ( ~ truxorfal ),
     ` ( ( F. \/_ T. ) <-> T. ) ` ( ~ falxortru ), and
     ` ( ( F. \/_ F. ) <-> F. ) ` ( ~ falxorfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` -/\ `
     ( ~ df-nan ) .  (Contributed by FL, 22-Nov-2010.) $)

${
	$v ph ps  $.
	f0_df-xor $f wff ph $.
	f1_df-xor $f wff ps $.
	a_df-xor $a |- ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) ) $.
$}

$(Two ways to write XNOR. (Contributed by Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps  $.
	f0_xnor $f wff ph $.
	f1_xnor $f wff ps $.
	p_xnor $p |- ( ( ph <-> ps ) <-> -. ( ph \/_ ps ) ) $= f0_xnor f1_xnor a_df-xor f0_xnor f1_xnor a_wxo f0_xnor f1_xnor a_wb p_con2bii $.
$}

$(` \/_ ` is commutative.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps  $.
	f0_xorcom $f wff ph $.
	f1_xorcom $f wff ps $.
	p_xorcom $p |- ( ( ph \/_ ps ) <-> ( ps \/_ ph ) ) $= f0_xorcom f1_xorcom p_bicom f0_xorcom f1_xorcom a_wb f1_xorcom f0_xorcom a_wb p_notbii f0_xorcom f1_xorcom a_df-xor f1_xorcom f0_xorcom a_df-xor f0_xorcom f1_xorcom a_wb a_wn f1_xorcom f0_xorcom a_wb a_wn f0_xorcom f1_xorcom a_wxo f1_xorcom f0_xorcom a_wxo p_3bitr4i $.
$}

$(` \/_ ` is associative.  (Contributed by FL, 22-Nov-2010.)  (Proof
     shortened by Andrew Salmon, 8-Jun-2011.) $)

${
	$v ph ps ch  $.
	f0_xorass $f wff ph $.
	f1_xorass $f wff ps $.
	f2_xorass $f wff ch $.
	p_xorass $p |- ( ( ( ph \/_ ps ) \/_ ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $= f0_xorass f1_xorass f2_xorass p_biass f0_xorass f1_xorass a_wb f2_xorass a_wb f0_xorass f1_xorass f2_xorass a_wb a_wb p_notbii f0_xorass f1_xorass a_wb f2_xorass p_nbbn f0_xorass f1_xorass f2_xorass a_wb p_pm5.18 f0_xorass f1_xorass f2_xorass a_wb a_wb f0_xorass f1_xorass f2_xorass a_wb a_wn a_wb p_con2bii f0_xorass f1_xorass a_wb f2_xorass a_wb a_wn f0_xorass f1_xorass f2_xorass a_wb a_wb a_wn f0_xorass f1_xorass a_wb a_wn f2_xorass a_wb f0_xorass f1_xorass f2_xorass a_wb a_wn a_wb p_3bitr4i f0_xorass f1_xorass a_df-xor f0_xorass f1_xorass a_wxo f0_xorass f1_xorass a_wb a_wn f2_xorass p_bibi1i f1_xorass f2_xorass a_df-xor f1_xorass f2_xorass a_wxo f1_xorass f2_xorass a_wb a_wn f0_xorass p_bibi2i f0_xorass f1_xorass a_wb a_wn f2_xorass a_wb f0_xorass f1_xorass f2_xorass a_wb a_wn a_wb f0_xorass f1_xorass a_wxo f2_xorass a_wb f0_xorass f1_xorass f2_xorass a_wxo a_wb p_3bitr4i f0_xorass f1_xorass a_wxo f2_xorass a_wb f0_xorass f1_xorass f2_xorass a_wxo a_wb p_notbii f0_xorass f1_xorass a_wxo f2_xorass a_df-xor f0_xorass f1_xorass f2_xorass a_wxo a_df-xor f0_xorass f1_xorass a_wxo f2_xorass a_wb a_wn f0_xorass f1_xorass f2_xorass a_wxo a_wb a_wn f0_xorass f1_xorass a_wxo f2_xorass a_wxo f0_xorass f1_xorass f2_xorass a_wxo a_wxo p_3bitr4i $.
$}

$(This tautology shows that xor is really exclusive.  (Contributed by FL,
     22-Nov-2010.) $)

${
	$v ph ps  $.
	f0_excxor $f wff ph $.
	f1_excxor $f wff ps $.
	p_excxor $p |- ( ( ph \/_ ps ) <-> ( ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) ) $= f0_excxor f1_excxor a_df-xor f0_excxor f1_excxor p_xor f1_excxor f0_excxor a_wn p_ancom f1_excxor f0_excxor a_wn a_wa f0_excxor a_wn f1_excxor a_wa f0_excxor f1_excxor a_wn a_wa p_orbi2i f0_excxor f1_excxor a_wxo f0_excxor f1_excxor a_wb a_wn f0_excxor f1_excxor a_wn a_wa f1_excxor f0_excxor a_wn a_wa a_wo f0_excxor f1_excxor a_wn a_wa f0_excxor a_wn f1_excxor a_wa a_wo p_3bitri $.
$}

$(Two ways to express "exclusive or."  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)

${
	$v ph ps  $.
	f0_xor2 $f wff ph $.
	f1_xor2 $f wff ps $.
	p_xor2 $p |- ( ( ph \/_ ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $= f0_xor2 f1_xor2 a_df-xor f0_xor2 f1_xor2 p_nbi2 f0_xor2 f1_xor2 a_wxo f0_xor2 f1_xor2 a_wb a_wn f0_xor2 f1_xor2 a_wo f0_xor2 f1_xor2 a_wa a_wn a_wa p_bitri $.
$}

$(` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)

${
	$v ph ps  $.
	f0_xorneg1 $f wff ph $.
	f1_xorneg1 $f wff ps $.
	p_xorneg1 $p |- ( ( -. ph \/_ ps ) <-> -. ( ph \/_ ps ) ) $= f0_xorneg1 a_wn f1_xorneg1 a_df-xor f0_xorneg1 f1_xorneg1 p_nbbn f0_xorneg1 a_wn f1_xorneg1 a_wb f0_xorneg1 f1_xorneg1 a_wb p_con2bii f0_xorneg1 f1_xorneg1 p_xnor f0_xorneg1 a_wn f1_xorneg1 a_wxo f0_xorneg1 a_wn f1_xorneg1 a_wb a_wn f0_xorneg1 f1_xorneg1 a_wb f0_xorneg1 f1_xorneg1 a_wxo a_wn p_3bitr2i $.
$}

$(` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)

${
	$v ph ps  $.
	f0_xorneg2 $f wff ph $.
	f1_xorneg2 $f wff ps $.
	p_xorneg2 $p |- ( ( ph \/_ -. ps ) <-> -. ( ph \/_ ps ) ) $= f1_xorneg2 f0_xorneg2 p_xorneg1 f0_xorneg2 f1_xorneg2 a_wn p_xorcom f0_xorneg2 f1_xorneg2 p_xorcom f0_xorneg2 f1_xorneg2 a_wxo f1_xorneg2 f0_xorneg2 a_wxo p_notbii f1_xorneg2 a_wn f0_xorneg2 a_wxo f1_xorneg2 f0_xorneg2 a_wxo a_wn f0_xorneg2 f1_xorneg2 a_wn a_wxo f0_xorneg2 f1_xorneg2 a_wxo a_wn p_3bitr4i $.
$}

$(` \/_ ` is unchanged under negation of both arguments.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)

${
	$v ph ps  $.
	f0_xorneg $f wff ph $.
	f1_xorneg $f wff ps $.
	p_xorneg $p |- ( ( -. ph \/_ -. ps ) <-> ( ph \/_ ps ) ) $= f0_xorneg f1_xorneg a_wn p_xorneg1 f0_xorneg f1_xorneg p_xorneg2 f0_xorneg f1_xorneg a_wn a_wxo f0_xorneg f1_xorneg a_wxo p_con2bii f0_xorneg a_wn f1_xorneg a_wn a_wxo f0_xorneg f1_xorneg a_wn a_wxo a_wn f0_xorneg f1_xorneg a_wxo p_bitr4i $.
$}

$(Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)

${
	$v ph ps ch th  $.
	f0_xorbi12i $f wff ph $.
	f1_xorbi12i $f wff ps $.
	f2_xorbi12i $f wff ch $.
	f3_xorbi12i $f wff th $.
	e0_xorbi12i $e |- ( ph <-> ps ) $.
	e1_xorbi12i $e |- ( ch <-> th ) $.
	p_xorbi12i $p |- ( ( ph \/_ ch ) <-> ( ps \/_ th ) ) $= e0_xorbi12i e1_xorbi12i f0_xorbi12i f1_xorbi12i f2_xorbi12i f3_xorbi12i p_bibi12i f0_xorbi12i f2_xorbi12i a_wb f1_xorbi12i f3_xorbi12i a_wb p_notbii f0_xorbi12i f2_xorbi12i a_df-xor f1_xorbi12i f3_xorbi12i a_df-xor f0_xorbi12i f2_xorbi12i a_wb a_wn f1_xorbi12i f3_xorbi12i a_wb a_wn f0_xorbi12i f2_xorbi12i a_wxo f1_xorbi12i f3_xorbi12i a_wxo p_3bitr4i $.
$}

$(Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)

${
	$v ph ps ch th ta  $.
	f0_xorbi12d $f wff ph $.
	f1_xorbi12d $f wff ps $.
	f2_xorbi12d $f wff ch $.
	f3_xorbi12d $f wff th $.
	f4_xorbi12d $f wff ta $.
	e0_xorbi12d $e |- ( ph -> ( ps <-> ch ) ) $.
	e1_xorbi12d $e |- ( ph -> ( th <-> ta ) ) $.
	p_xorbi12d $p |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ ta ) ) ) $= e0_xorbi12d e1_xorbi12d f0_xorbi12d f1_xorbi12d f2_xorbi12d f3_xorbi12d f4_xorbi12d p_bibi12d f0_xorbi12d f1_xorbi12d f3_xorbi12d a_wb f2_xorbi12d f4_xorbi12d a_wb p_notbid f1_xorbi12d f3_xorbi12d a_df-xor f2_xorbi12d f4_xorbi12d a_df-xor f0_xorbi12d f1_xorbi12d f3_xorbi12d a_wb a_wn f2_xorbi12d f4_xorbi12d a_wb a_wn f1_xorbi12d f3_xorbi12d a_wxo f2_xorbi12d f4_xorbi12d a_wxo p_3bitr4g $.
$}


