$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical__nand__(Sheffer_stroke).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'xor'

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Declare connective for exclusive disjunction ('xor'). $)
$c \/_  $.
$( Underlined 'vee' (read:  'xor') $)
$( Extend wff definition to include exclusive disjunction ('xor'). $)
${
	fwxo_0 $f wff ph $.
	fwxo_1 $f wff ps $.
	wxo $a wff ( ph \/_ ps ) $.
$}
$( Define exclusive disjunction (logical 'xor').  Return true if either the
     left or right, but not both, are true.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. \/_ T. ) <-> F. ) `
     ( ~ truxortru ), ` ( ( T. \/_ F. ) <-> T. ) ` ( ~ truxorfal ),
     ` ( ( F. \/_ T. ) <-> T. ) ` ( ~ falxortru ), and
     ` ( ( F. \/_ F. ) <-> F. ) ` ( ~ falxorfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` -/\ `
     ( ~ df-nan ) .  (Contributed by FL, 22-Nov-2010.) $)
${
	fdf-xor_0 $f wff ph $.
	fdf-xor_1 $f wff ps $.
	df-xor $a |- ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) ) $.
$}
$( Two ways to write XNOR. (Contributed by Mario Carneiro, 4-Sep-2016.) $)
${
	fxnor_0 $f wff ph $.
	fxnor_1 $f wff ps $.
	xnor $p |- ( ( ph <-> ps ) <-> -. ( ph \/_ ps ) ) $= fxnor_0 fxnor_1 wxo fxnor_0 fxnor_1 wb fxnor_0 fxnor_1 df-xor con2bii $.
$}
$( ` \/_ ` is commutative.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
${
	fxorcom_0 $f wff ph $.
	fxorcom_1 $f wff ps $.
	xorcom $p |- ( ( ph \/_ ps ) <-> ( ps \/_ ph ) ) $= fxorcom_0 fxorcom_1 wb wn fxorcom_1 fxorcom_0 wb wn fxorcom_0 fxorcom_1 wxo fxorcom_1 fxorcom_0 wxo fxorcom_0 fxorcom_1 wb fxorcom_1 fxorcom_0 wb fxorcom_0 fxorcom_1 bicom notbii fxorcom_0 fxorcom_1 df-xor fxorcom_1 fxorcom_0 df-xor 3bitr4i $.
$}
$( ` \/_ ` is associative.  (Contributed by FL, 22-Nov-2010.)  (Proof
     shortened by Andrew Salmon, 8-Jun-2011.) $)
${
	fxorass_0 $f wff ph $.
	fxorass_1 $f wff ps $.
	fxorass_2 $f wff ch $.
	xorass $p |- ( ( ( ph \/_ ps ) \/_ ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $= fxorass_0 fxorass_1 wxo fxorass_2 wb wn fxorass_0 fxorass_1 fxorass_2 wxo wb wn fxorass_0 fxorass_1 wxo fxorass_2 wxo fxorass_0 fxorass_1 fxorass_2 wxo wxo fxorass_0 fxorass_1 wxo fxorass_2 wb fxorass_0 fxorass_1 fxorass_2 wxo wb fxorass_0 fxorass_1 wb wn fxorass_2 wb fxorass_0 fxorass_1 fxorass_2 wb wn wb fxorass_0 fxorass_1 wxo fxorass_2 wb fxorass_0 fxorass_1 fxorass_2 wxo wb fxorass_0 fxorass_1 wb fxorass_2 wb wn fxorass_0 fxorass_1 fxorass_2 wb wb wn fxorass_0 fxorass_1 wb wn fxorass_2 wb fxorass_0 fxorass_1 fxorass_2 wb wn wb fxorass_0 fxorass_1 wb fxorass_2 wb fxorass_0 fxorass_1 fxorass_2 wb wb fxorass_0 fxorass_1 fxorass_2 biass notbii fxorass_0 fxorass_1 wb fxorass_2 nbbn fxorass_0 fxorass_1 fxorass_2 wb wb fxorass_0 fxorass_1 fxorass_2 wb wn wb fxorass_0 fxorass_1 fxorass_2 wb pm5.18 con2bii 3bitr4i fxorass_0 fxorass_1 wxo fxorass_0 fxorass_1 wb wn fxorass_2 fxorass_0 fxorass_1 df-xor bibi1i fxorass_1 fxorass_2 wxo fxorass_1 fxorass_2 wb wn fxorass_0 fxorass_1 fxorass_2 df-xor bibi2i 3bitr4i notbii fxorass_0 fxorass_1 wxo fxorass_2 df-xor fxorass_0 fxorass_1 fxorass_2 wxo df-xor 3bitr4i $.
$}
$( This tautology shows that xor is really exclusive.  (Contributed by FL,
     22-Nov-2010.) $)
${
	fexcxor_0 $f wff ph $.
	fexcxor_1 $f wff ps $.
	excxor $p |- ( ( ph \/_ ps ) <-> ( ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) ) $= fexcxor_0 fexcxor_1 wxo fexcxor_0 fexcxor_1 wb wn fexcxor_0 fexcxor_1 wn wa fexcxor_1 fexcxor_0 wn wa wo fexcxor_0 fexcxor_1 wn wa fexcxor_0 wn fexcxor_1 wa wo fexcxor_0 fexcxor_1 df-xor fexcxor_0 fexcxor_1 xor fexcxor_1 fexcxor_0 wn wa fexcxor_0 wn fexcxor_1 wa fexcxor_0 fexcxor_1 wn wa fexcxor_1 fexcxor_0 wn ancom orbi2i 3bitri $.
$}
$( Two ways to express "exclusive or."  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
${
	fxor2_0 $f wff ph $.
	fxor2_1 $f wff ps $.
	xor2 $p |- ( ( ph \/_ ps ) <-> ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $= fxor2_0 fxor2_1 wxo fxor2_0 fxor2_1 wb wn fxor2_0 fxor2_1 wo fxor2_0 fxor2_1 wa wn wa fxor2_0 fxor2_1 df-xor fxor2_0 fxor2_1 nbi2 bitri $.
$}
$( ` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
${
	fxorneg1_0 $f wff ph $.
	fxorneg1_1 $f wff ps $.
	xorneg1 $p |- ( ( -. ph \/_ ps ) <-> -. ( ph \/_ ps ) ) $= fxorneg1_0 wn fxorneg1_1 wxo fxorneg1_0 wn fxorneg1_1 wb wn fxorneg1_0 fxorneg1_1 wb fxorneg1_0 fxorneg1_1 wxo wn fxorneg1_0 wn fxorneg1_1 df-xor fxorneg1_0 wn fxorneg1_1 wb fxorneg1_0 fxorneg1_1 wb fxorneg1_0 fxorneg1_1 nbbn con2bii fxorneg1_0 fxorneg1_1 xnor 3bitr2i $.
$}
$( ` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
${
	fxorneg2_0 $f wff ph $.
	fxorneg2_1 $f wff ps $.
	xorneg2 $p |- ( ( ph \/_ -. ps ) <-> -. ( ph \/_ ps ) ) $= fxorneg2_1 wn fxorneg2_0 wxo fxorneg2_1 fxorneg2_0 wxo wn fxorneg2_0 fxorneg2_1 wn wxo fxorneg2_0 fxorneg2_1 wxo wn fxorneg2_1 fxorneg2_0 xorneg1 fxorneg2_0 fxorneg2_1 wn xorcom fxorneg2_0 fxorneg2_1 wxo fxorneg2_1 fxorneg2_0 wxo fxorneg2_0 fxorneg2_1 xorcom notbii 3bitr4i $.
$}
$( ` \/_ ` is unchanged under negation of both arguments.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
${
	fxorneg_0 $f wff ph $.
	fxorneg_1 $f wff ps $.
	xorneg $p |- ( ( -. ph \/_ -. ps ) <-> ( ph \/_ ps ) ) $= fxorneg_0 wn fxorneg_1 wn wxo fxorneg_0 fxorneg_1 wn wxo wn fxorneg_0 fxorneg_1 wxo fxorneg_0 fxorneg_1 wn xorneg1 fxorneg_0 fxorneg_1 wn wxo fxorneg_0 fxorneg_1 wxo fxorneg_0 fxorneg_1 xorneg2 con2bii bitr4i $.
$}
$( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
${
	fxorbi12i_0 $f wff ph $.
	fxorbi12i_1 $f wff ps $.
	fxorbi12i_2 $f wff ch $.
	fxorbi12i_3 $f wff th $.
	exorbi12i_0 $e |- ( ph <-> ps ) $.
	exorbi12i_1 $e |- ( ch <-> th ) $.
	xorbi12i $p |- ( ( ph \/_ ch ) <-> ( ps \/_ th ) ) $= fxorbi12i_0 fxorbi12i_2 wb wn fxorbi12i_1 fxorbi12i_3 wb wn fxorbi12i_0 fxorbi12i_2 wxo fxorbi12i_1 fxorbi12i_3 wxo fxorbi12i_0 fxorbi12i_2 wb fxorbi12i_1 fxorbi12i_3 wb fxorbi12i_0 fxorbi12i_1 fxorbi12i_2 fxorbi12i_3 exorbi12i_0 exorbi12i_1 bibi12i notbii fxorbi12i_0 fxorbi12i_2 df-xor fxorbi12i_1 fxorbi12i_3 df-xor 3bitr4i $.
$}
$( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
${
	fxorbi12d_0 $f wff ph $.
	fxorbi12d_1 $f wff ps $.
	fxorbi12d_2 $f wff ch $.
	fxorbi12d_3 $f wff th $.
	fxorbi12d_4 $f wff ta $.
	exorbi12d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	exorbi12d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	xorbi12d $p |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ ta ) ) ) $= fxorbi12d_0 fxorbi12d_1 fxorbi12d_3 wb wn fxorbi12d_2 fxorbi12d_4 wb wn fxorbi12d_1 fxorbi12d_3 wxo fxorbi12d_2 fxorbi12d_4 wxo fxorbi12d_0 fxorbi12d_1 fxorbi12d_3 wb fxorbi12d_2 fxorbi12d_4 wb fxorbi12d_0 fxorbi12d_1 fxorbi12d_2 fxorbi12d_3 fxorbi12d_4 exorbi12d_0 exorbi12d_1 bibi12d notbid fxorbi12d_1 fxorbi12d_3 df-xor fxorbi12d_2 fxorbi12d_4 df-xor 3bitr4g $.
$}

