$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Auxiliary_theorems_for_Alan_Sare_s_virtual_deduction_tool,_part_1.mm $]
$( /* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Half-adders and full adders in propositional calculus

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus deals with truth values, which can be interpreted as
  bits. Using this, we can define the half-adder in pure propositional
  calculus, and show its basic properties.

*/

$)
$c hadd  $.
$c cadd  $.
$c ,  $.
$( /* Comma (also used for unordered pair notation later) */

$)
$( /* Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fwhad_0 $f wff ph $.
	fwhad_1 $f wff ps $.
	fwhad_2 $f wff ch $.
	whad $a wff hadd ( ph , ps , ch ) $.
$}
$( /* Define the half adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fwcad_0 $f wff ph $.
	fwcad_1 $f wff ps $.
	fwcad_2 $f wff ch $.
	wcad $a wff cadd ( ph , ps , ch ) $.
$}
$( /* Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fdf-had_0 $f wff ph $.
	fdf-had_1 $f wff ps $.
	fdf-had_2 $f wff ch $.
	df-had $a |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $.
$}
$( /* Define the half adder carry, which is true when at least two arguments are
     true.  (Contributed by Mario Carneiro, 4-Sep-2016.) */

$)
${
	fdf-cad_0 $f wff ph $.
	fdf-cad_1 $f wff ps $.
	fdf-cad_2 $f wff ch $.
	df-cad $a |- ( cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $.
$}
$( /* Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) */

$)
${
	fhadbi123d_0 $f wff ph $.
	fhadbi123d_1 $f wff ps $.
	fhadbi123d_2 $f wff ch $.
	fhadbi123d_3 $f wff th $.
	fhadbi123d_4 $f wff ta $.
	fhadbi123d_5 $f wff et $.
	fhadbi123d_6 $f wff ze $.
	ehadbi123d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ehadbi123d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	ehadbi123d_2 $e |- ( ph -> ( et <-> ze ) ) $.
	hadbi123d $p |- ( ph -> ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) ) $= fhadbi123d_0 fhadbi123d_1 fhadbi123d_3 wxo fhadbi123d_5 wxo fhadbi123d_2 fhadbi123d_4 wxo fhadbi123d_6 wxo fhadbi123d_1 fhadbi123d_3 fhadbi123d_5 whad fhadbi123d_2 fhadbi123d_4 fhadbi123d_6 whad fhadbi123d_0 fhadbi123d_1 fhadbi123d_3 wxo fhadbi123d_2 fhadbi123d_4 wxo fhadbi123d_5 fhadbi123d_6 fhadbi123d_0 fhadbi123d_1 fhadbi123d_2 fhadbi123d_3 fhadbi123d_4 ehadbi123d_0 ehadbi123d_1 xorbi12d ehadbi123d_2 xorbi12d fhadbi123d_1 fhadbi123d_3 fhadbi123d_5 df-had fhadbi123d_2 fhadbi123d_4 fhadbi123d_6 df-had 3bitr4g $.
$}
$( /* Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) */

$)
${
	fcadbi123d_0 $f wff ph $.
	fcadbi123d_1 $f wff ps $.
	fcadbi123d_2 $f wff ch $.
	fcadbi123d_3 $f wff th $.
	fcadbi123d_4 $f wff ta $.
	fcadbi123d_5 $f wff et $.
	fcadbi123d_6 $f wff ze $.
	ecadbi123d_0 $e |- ( ph -> ( ps <-> ch ) ) $.
	ecadbi123d_1 $e |- ( ph -> ( th <-> ta ) ) $.
	ecadbi123d_2 $e |- ( ph -> ( et <-> ze ) ) $.
	cadbi123d $p |- ( ph -> ( cadd ( ps , th , et ) <-> cadd ( ch , ta , ze ) ) ) $= fcadbi123d_0 fcadbi123d_1 fcadbi123d_3 wa fcadbi123d_5 fcadbi123d_1 fcadbi123d_3 wxo wa wo fcadbi123d_2 fcadbi123d_4 wa fcadbi123d_6 fcadbi123d_2 fcadbi123d_4 wxo wa wo fcadbi123d_1 fcadbi123d_3 fcadbi123d_5 wcad fcadbi123d_2 fcadbi123d_4 fcadbi123d_6 wcad fcadbi123d_0 fcadbi123d_1 fcadbi123d_3 wa fcadbi123d_2 fcadbi123d_4 wa fcadbi123d_5 fcadbi123d_1 fcadbi123d_3 wxo wa fcadbi123d_6 fcadbi123d_2 fcadbi123d_4 wxo wa fcadbi123d_0 fcadbi123d_1 fcadbi123d_2 fcadbi123d_3 fcadbi123d_4 ecadbi123d_0 ecadbi123d_1 anbi12d fcadbi123d_0 fcadbi123d_5 fcadbi123d_6 fcadbi123d_1 fcadbi123d_3 wxo fcadbi123d_2 fcadbi123d_4 wxo ecadbi123d_2 fcadbi123d_0 fcadbi123d_1 fcadbi123d_2 fcadbi123d_3 fcadbi123d_4 ecadbi123d_0 ecadbi123d_1 xorbi12d anbi12d orbi12d fcadbi123d_1 fcadbi123d_3 fcadbi123d_5 df-cad fcadbi123d_2 fcadbi123d_4 fcadbi123d_6 df-cad 3bitr4g $.
$}
$( /* Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) */

$)
${
	fhadbi123i_0 $f wff ph $.
	fhadbi123i_1 $f wff ps $.
	fhadbi123i_2 $f wff ch $.
	fhadbi123i_3 $f wff th $.
	fhadbi123i_4 $f wff ta $.
	fhadbi123i_5 $f wff et $.
	ehadbi123i_0 $e |- ( ph <-> ps ) $.
	ehadbi123i_1 $e |- ( ch <-> th ) $.
	ehadbi123i_2 $e |- ( ta <-> et ) $.
	hadbi123i $p |- ( hadd ( ph , ch , ta ) <-> hadd ( ps , th , et ) ) $= fhadbi123i_0 fhadbi123i_2 fhadbi123i_4 whad fhadbi123i_1 fhadbi123i_3 fhadbi123i_5 whad wb wtru fhadbi123i_0 fhadbi123i_1 fhadbi123i_2 fhadbi123i_3 fhadbi123i_4 fhadbi123i_5 fhadbi123i_0 fhadbi123i_1 wb wtru ehadbi123i_0 a1i fhadbi123i_2 fhadbi123i_3 wb wtru ehadbi123i_1 a1i fhadbi123i_4 fhadbi123i_5 wb wtru ehadbi123i_2 a1i hadbi123d trud $.
$}
$( /* Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) */

$)
${
	fcadbi123i_0 $f wff ph $.
	fcadbi123i_1 $f wff ps $.
	fcadbi123i_2 $f wff ch $.
	fcadbi123i_3 $f wff th $.
	fcadbi123i_4 $f wff ta $.
	fcadbi123i_5 $f wff et $.
	ecadbi123i_0 $e |- ( ph <-> ps ) $.
	ecadbi123i_1 $e |- ( ch <-> th ) $.
	ecadbi123i_2 $e |- ( ta <-> et ) $.
	cadbi123i $p |- ( cadd ( ph , ch , ta ) <-> cadd ( ps , th , et ) ) $= fcadbi123i_0 fcadbi123i_2 fcadbi123i_4 wcad fcadbi123i_1 fcadbi123i_3 fcadbi123i_5 wcad wb wtru fcadbi123i_0 fcadbi123i_1 fcadbi123i_2 fcadbi123i_3 fcadbi123i_4 fcadbi123i_5 fcadbi123i_0 fcadbi123i_1 wb wtru ecadbi123i_0 a1i fcadbi123i_2 fcadbi123i_3 wb wtru ecadbi123i_1 a1i fcadbi123i_4 fcadbi123i_5 wb wtru ecadbi123i_2 a1i cadbi123d trud $.
$}
$( /* Associative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fhadass_0 $f wff ph $.
	fhadass_1 $f wff ps $.
	fhadass_2 $f wff ch $.
	hadass $p |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $= fhadass_0 fhadass_1 fhadass_2 whad fhadass_0 fhadass_1 wxo fhadass_2 wxo fhadass_0 fhadass_1 fhadass_2 wxo wxo fhadass_0 fhadass_1 fhadass_2 df-had fhadass_0 fhadass_1 fhadass_2 xorass bitri $.
$}
$( /* The half adder is the same as the triple biconditional.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) */

$)
${
	fhadbi_0 $f wff ph $.
	fhadbi_1 $f wff ps $.
	fhadbi_2 $f wff ch $.
	hadbi $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) ) $= fhadbi_0 fhadbi_1 wxo fhadbi_2 wxo fhadbi_0 fhadbi_1 wxo fhadbi_2 wb wn fhadbi_0 fhadbi_1 fhadbi_2 whad fhadbi_0 fhadbi_1 wb fhadbi_2 wb fhadbi_0 fhadbi_1 wxo fhadbi_2 df-xor fhadbi_0 fhadbi_1 fhadbi_2 df-had fhadbi_0 fhadbi_1 wb fhadbi_2 wb fhadbi_0 fhadbi_1 wxo wn fhadbi_2 wb fhadbi_0 fhadbi_1 wxo fhadbi_2 wb wn fhadbi_0 fhadbi_1 wb fhadbi_0 fhadbi_1 wxo wn fhadbi_2 fhadbi_0 fhadbi_1 xnor bibi1i fhadbi_0 fhadbi_1 wxo fhadbi_2 nbbn bitri 3bitr4i $.
$}
$( /* Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fhadcoma_0 $f wff ph $.
	fhadcoma_1 $f wff ps $.
	fhadcoma_2 $f wff ch $.
	hadcoma $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) ) $= fhadcoma_0 fhadcoma_1 wxo fhadcoma_2 wxo fhadcoma_1 fhadcoma_0 wxo fhadcoma_2 wxo fhadcoma_0 fhadcoma_1 fhadcoma_2 whad fhadcoma_1 fhadcoma_0 fhadcoma_2 whad fhadcoma_0 fhadcoma_1 wxo fhadcoma_1 fhadcoma_0 wxo fhadcoma_2 fhadcoma_2 fhadcoma_0 fhadcoma_1 xorcom fhadcoma_2 biid xorbi12i fhadcoma_0 fhadcoma_1 fhadcoma_2 df-had fhadcoma_1 fhadcoma_0 fhadcoma_2 df-had 3bitr4i $.
$}
$( /* Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fhadcomb_0 $f wff ph $.
	fhadcomb_1 $f wff ps $.
	fhadcomb_2 $f wff ch $.
	hadcomb $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) ) $= fhadcomb_0 fhadcomb_1 fhadcomb_2 wxo wxo fhadcomb_0 fhadcomb_2 fhadcomb_1 wxo wxo fhadcomb_0 fhadcomb_1 fhadcomb_2 whad fhadcomb_0 fhadcomb_2 fhadcomb_1 whad fhadcomb_0 fhadcomb_0 fhadcomb_1 fhadcomb_2 wxo fhadcomb_2 fhadcomb_1 wxo fhadcomb_0 biid fhadcomb_1 fhadcomb_2 xorcom xorbi12i fhadcomb_0 fhadcomb_1 fhadcomb_2 hadass fhadcomb_0 fhadcomb_2 fhadcomb_1 hadass 3bitr4i $.
$}
$( /* Rotation law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fhadrot_0 $f wff ph $.
	fhadrot_1 $f wff ps $.
	fhadrot_2 $f wff ch $.
	hadrot $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) ) $= fhadrot_0 fhadrot_1 fhadrot_2 whad fhadrot_1 fhadrot_0 fhadrot_2 whad fhadrot_1 fhadrot_2 fhadrot_0 whad fhadrot_0 fhadrot_1 fhadrot_2 hadcoma fhadrot_1 fhadrot_0 fhadrot_2 hadcomb bitri $.
$}
$( /* Write the adder carry in disjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) */

$)
${
	fcador_0 $f wff ph $.
	fcador_1 $f wff ps $.
	fcador_2 $f wff ch $.
	cador $p |- ( cadd ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $= fcador_0 fcador_1 fcador_2 wcad fcador_0 fcador_1 wa fcador_2 fcador_0 fcador_1 wxo wa wo fcador_0 fcador_1 wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa w3o fcador_0 fcador_1 fcador_2 df-cad fcador_0 fcador_1 wa wn fcador_2 fcador_0 fcador_1 wxo wa wi fcador_0 fcador_1 wa wn fcador_0 fcador_2 wa fcador_1 fcador_2 wa wo wi fcador_0 fcador_1 wa fcador_2 fcador_0 fcador_1 wxo wa wo fcador_0 fcador_1 wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa w3o fcador_0 fcador_1 wa wn fcador_2 fcador_0 fcador_1 wxo wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa wo fcador_0 fcador_1 wa wn fcador_0 fcador_1 wxo fcador_2 wa fcador_0 fcador_1 wo fcador_2 wa fcador_2 fcador_0 fcador_1 wxo wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa wo fcador_0 fcador_1 wa wn fcador_0 fcador_1 wxo fcador_0 fcador_1 wo fcador_2 fcador_0 fcador_1 wxo fcador_0 fcador_1 wo fcador_0 fcador_1 wa wn fcador_0 fcador_1 xor2 rbaib anbi1d fcador_0 fcador_1 wxo fcador_2 ancom fcador_0 fcador_1 fcador_2 andir 3bitr3g pm5.74i fcador_0 fcador_1 wa fcador_2 fcador_0 fcador_1 wxo wa df-or fcador_0 fcador_1 wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa w3o fcador_0 fcador_1 wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa wo wo fcador_0 fcador_1 wa wn fcador_0 fcador_2 wa fcador_1 fcador_2 wa wo wi fcador_0 fcador_1 wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa 3orass fcador_0 fcador_1 wa fcador_0 fcador_2 wa fcador_1 fcador_2 wa wo df-or bitri 3bitr4i bitri $.
$}
$( /* Write the adder carry in conjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) */

$)
${
	fcadan_0 $f wff ph $.
	fcadan_1 $f wff ps $.
	fcadan_2 $f wff ch $.
	cadan $p |- ( cadd ( ph , ps , ch ) <-> ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $= fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa fcadan_1 fcadan_2 wa w3o fcadan_0 fcadan_1 wo fcadan_0 fcadan_2 wo wa fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_1 fcadan_2 wcad fcadan_0 fcadan_1 wo fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo w3a fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 fcadan_2 wa wo fcadan_0 fcadan_1 wo fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo wa wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa fcadan_1 fcadan_2 wa w3o fcadan_0 fcadan_1 wo fcadan_0 fcadan_2 wo wa fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 fcadan_2 wa wo fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 wo fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_2 wo wa fcadan_0 fcadan_1 wo fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo wa wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 fcadan_2 ordi fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 wo fcadan_0 fcadan_1 wo fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_2 wo fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_2 wa fcadan_1 wo fcadan_0 fcadan_1 wo fcadan_2 fcadan_1 wo wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 wo fcadan_0 fcadan_1 wo fcadan_1 fcadan_2 wo wa fcadan_0 fcadan_2 fcadan_1 ordir fcadan_1 fcadan_0 fcadan_2 wa wo fcadan_1 fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wo fcadan_0 fcadan_2 wa fcadan_1 wo fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 wo fcadan_1 wn fcadan_0 fcadan_2 wa wi fcadan_1 wn fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wi fcadan_1 fcadan_0 fcadan_2 wa wo fcadan_1 fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wo fcadan_1 wn fcadan_0 fcadan_2 wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 wn fcadan_0 fcadan_1 wa wn fcadan_0 fcadan_2 wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wb fcadan_0 fcadan_1 wa fcadan_1 fcadan_0 fcadan_1 simpr con3i fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa biorf syl pm5.74i fcadan_1 fcadan_0 fcadan_2 wa df-or fcadan_1 fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo df-or 3bitr4i fcadan_0 fcadan_2 wa fcadan_1 orcom fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_1 orcom 3bitr4i fcadan_2 fcadan_1 wo fcadan_1 fcadan_2 wo fcadan_0 fcadan_1 wo fcadan_2 fcadan_1 orcom anbi2i 3bitr3i fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_2 wo fcadan_0 fcadan_1 wa fcadan_2 wo fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo wa fcadan_2 fcadan_0 fcadan_1 wa wo fcadan_2 fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wo fcadan_0 fcadan_1 wa fcadan_2 wo fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_2 wo fcadan_2 wn fcadan_0 fcadan_1 wa wi fcadan_2 wn fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wi fcadan_2 fcadan_0 fcadan_1 wa wo fcadan_2 fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wo fcadan_2 wn fcadan_0 fcadan_1 wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_2 wn fcadan_0 fcadan_2 wa wn fcadan_0 fcadan_1 wa fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo wb fcadan_0 fcadan_2 wa fcadan_2 fcadan_0 fcadan_2 simpr con3i fcadan_0 fcadan_2 wa wn fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa fcadan_0 fcadan_1 wa wo fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_0 fcadan_2 wa fcadan_0 fcadan_1 wa biorf fcadan_0 fcadan_2 wa fcadan_0 fcadan_1 wa orcom syl6bb syl pm5.74i fcadan_2 fcadan_0 fcadan_1 wa df-or fcadan_2 fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo df-or 3bitr4i fcadan_0 fcadan_1 wa fcadan_2 orcom fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa wo fcadan_2 orcom 3bitr4i fcadan_0 fcadan_1 fcadan_2 ordir bitr3i anbi12i bitri fcadan_0 fcadan_1 wa fcadan_0 fcadan_2 wa fcadan_1 fcadan_2 wa df-3or fcadan_0 fcadan_1 wo fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo anandir 3bitr4i fcadan_0 fcadan_1 fcadan_2 cador fcadan_0 fcadan_1 wo fcadan_0 fcadan_2 wo fcadan_1 fcadan_2 wo df-3an 3bitr4i $.
$}
$( /* The half adder distributes over negation.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fhadnot_0 $f wff ph $.
	fhadnot_1 $f wff ps $.
	fhadnot_2 $f wff ch $.
	hadnot $p |- ( -. hadd ( ph , ps , ch ) <-> hadd ( -. ph , -. ps , -. ch ) ) $= fhadnot_0 fhadnot_1 wxo fhadnot_2 wxo wn fhadnot_0 wn fhadnot_1 wn wxo fhadnot_2 wn wxo fhadnot_0 fhadnot_1 fhadnot_2 whad wn fhadnot_0 wn fhadnot_1 wn fhadnot_2 wn whad fhadnot_0 wn fhadnot_1 wn wxo fhadnot_2 wn wxo fhadnot_0 fhadnot_1 wxo fhadnot_2 wn wxo fhadnot_0 fhadnot_1 wxo fhadnot_2 wxo wn fhadnot_0 wn fhadnot_1 wn wxo fhadnot_0 fhadnot_1 wxo fhadnot_2 wn fhadnot_2 wn fhadnot_0 fhadnot_1 xorneg fhadnot_2 wn biid xorbi12i fhadnot_0 fhadnot_1 wxo fhadnot_2 xorneg2 bitr2i fhadnot_0 fhadnot_1 fhadnot_2 whad fhadnot_0 fhadnot_1 wxo fhadnot_2 wxo fhadnot_0 fhadnot_1 fhadnot_2 df-had notbii fhadnot_0 wn fhadnot_1 wn fhadnot_2 wn df-had 3bitr4i $.
$}
$( /* The adder carry distributes over negation.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) */

$)
${
	fcadnot_0 $f wff ph $.
	fcadnot_1 $f wff ps $.
	fcadnot_2 $f wff ch $.
	cadnot $p |- ( -. cadd ( ph , ps , ch ) <-> cadd ( -. ph , -. ps , -. ch ) ) $= fcadnot_0 fcadnot_1 wa fcadnot_0 fcadnot_2 wa fcadnot_1 fcadnot_2 wa w3o wn fcadnot_0 wn fcadnot_1 wn wo fcadnot_0 wn fcadnot_2 wn wo fcadnot_1 wn fcadnot_2 wn wo w3a fcadnot_0 fcadnot_1 fcadnot_2 wcad wn fcadnot_0 wn fcadnot_1 wn fcadnot_2 wn wcad fcadnot_0 fcadnot_1 wa fcadnot_0 fcadnot_2 wa fcadnot_1 fcadnot_2 wa w3o wn fcadnot_0 fcadnot_1 wa wn fcadnot_0 fcadnot_2 wa wn fcadnot_1 fcadnot_2 wa wn w3a fcadnot_0 wn fcadnot_1 wn wo fcadnot_0 wn fcadnot_2 wn wo fcadnot_1 wn fcadnot_2 wn wo w3a fcadnot_0 fcadnot_1 wa fcadnot_0 fcadnot_2 wa fcadnot_1 fcadnot_2 wa 3ioran fcadnot_0 fcadnot_1 wa wn fcadnot_0 wn fcadnot_1 wn wo fcadnot_0 fcadnot_2 wa wn fcadnot_0 wn fcadnot_2 wn wo fcadnot_1 fcadnot_2 wa wn fcadnot_1 wn fcadnot_2 wn wo fcadnot_0 fcadnot_1 ianor fcadnot_0 fcadnot_2 ianor fcadnot_1 fcadnot_2 ianor 3anbi123i bitri fcadnot_0 fcadnot_1 fcadnot_2 wcad fcadnot_0 fcadnot_1 wa fcadnot_0 fcadnot_2 wa fcadnot_1 fcadnot_2 wa w3o fcadnot_0 fcadnot_1 fcadnot_2 cador notbii fcadnot_0 wn fcadnot_1 wn fcadnot_2 wn cadan 3bitr4i $.
$}
$( /* Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fcadcoma_0 $f wff ph $.
	fcadcoma_1 $f wff ps $.
	fcadcoma_2 $f wff ch $.
	cadcoma $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ph , ch ) ) $= fcadcoma_0 fcadcoma_1 wa fcadcoma_2 fcadcoma_0 fcadcoma_1 wxo wa wo fcadcoma_1 fcadcoma_0 wa fcadcoma_2 fcadcoma_1 fcadcoma_0 wxo wa wo fcadcoma_0 fcadcoma_1 fcadcoma_2 wcad fcadcoma_1 fcadcoma_0 fcadcoma_2 wcad fcadcoma_0 fcadcoma_1 wa fcadcoma_1 fcadcoma_0 wa fcadcoma_2 fcadcoma_0 fcadcoma_1 wxo wa fcadcoma_2 fcadcoma_1 fcadcoma_0 wxo wa fcadcoma_0 fcadcoma_1 ancom fcadcoma_0 fcadcoma_1 wxo fcadcoma_1 fcadcoma_0 wxo fcadcoma_2 fcadcoma_0 fcadcoma_1 xorcom anbi2i orbi12i fcadcoma_0 fcadcoma_1 fcadcoma_2 df-cad fcadcoma_1 fcadcoma_0 fcadcoma_2 df-cad 3bitr4i $.
$}
$( /* Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fcadcomb_0 $f wff ph $.
	fcadcomb_1 $f wff ps $.
	fcadcomb_2 $f wff ch $.
	cadcomb $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ph , ch , ps ) ) $= fcadcomb_0 fcadcomb_1 wa fcadcomb_0 fcadcomb_2 wa fcadcomb_1 fcadcomb_2 wa w3o fcadcomb_0 fcadcomb_2 wa fcadcomb_0 fcadcomb_1 wa fcadcomb_2 fcadcomb_1 wa w3o fcadcomb_0 fcadcomb_1 fcadcomb_2 wcad fcadcomb_0 fcadcomb_2 fcadcomb_1 wcad fcadcomb_0 fcadcomb_1 wa fcadcomb_0 fcadcomb_2 wa fcadcomb_1 fcadcomb_2 wa w3o fcadcomb_0 fcadcomb_2 wa fcadcomb_0 fcadcomb_1 wa fcadcomb_1 fcadcomb_2 wa w3o fcadcomb_0 fcadcomb_2 wa fcadcomb_0 fcadcomb_1 wa fcadcomb_2 fcadcomb_1 wa w3o fcadcomb_0 fcadcomb_1 wa fcadcomb_0 fcadcomb_2 wa fcadcomb_1 fcadcomb_2 wa 3orcoma fcadcomb_0 fcadcomb_2 wa fcadcomb_0 fcadcomb_2 wa fcadcomb_0 fcadcomb_1 wa fcadcomb_0 fcadcomb_1 wa fcadcomb_1 fcadcomb_2 wa fcadcomb_2 fcadcomb_1 wa fcadcomb_0 fcadcomb_2 wa biid fcadcomb_0 fcadcomb_1 wa biid fcadcomb_1 fcadcomb_2 ancom 3orbi123i bitri fcadcomb_0 fcadcomb_1 fcadcomb_2 cador fcadcomb_0 fcadcomb_2 fcadcomb_1 cador 3bitr4i $.
$}
$( /* Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fcadrot_0 $f wff ph $.
	fcadrot_1 $f wff ps $.
	fcadrot_2 $f wff ch $.
	cadrot $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ch , ph ) ) $= fcadrot_0 fcadrot_1 fcadrot_2 wcad fcadrot_1 fcadrot_0 fcadrot_2 wcad fcadrot_1 fcadrot_2 fcadrot_0 wcad fcadrot_0 fcadrot_1 fcadrot_2 cadcoma fcadrot_1 fcadrot_0 fcadrot_2 cadcomb bitri $.
$}
$( /* If one parameter is true, the adder carry is true exactly when at least
     one of the other parameters is true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) */

$)
${
	fcad1_0 $f wff ph $.
	fcad1_1 $f wff ps $.
	fcad1_2 $f wff ch $.
	cad1 $p |- ( ch -> ( cadd ( ph , ps , ch ) <-> ( ph \/ ps ) ) ) $= fcad1_2 fcad1_0 fcad1_1 wa fcad1_2 fcad1_0 fcad1_1 wxo wa wo fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wxo wo fcad1_0 fcad1_1 fcad1_2 wcad fcad1_0 fcad1_1 wo fcad1_2 fcad1_2 fcad1_0 fcad1_1 wxo wa fcad1_0 fcad1_1 wxo fcad1_0 fcad1_1 wa fcad1_2 fcad1_0 fcad1_1 wxo fcad1_2 fcad1_0 fcad1_1 wxo wa fcad1_2 fcad1_0 fcad1_1 wxo ibar bicomd orbi2d fcad1_0 fcad1_1 fcad1_2 df-cad fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wo wo fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wa wn fcad1_0 fcad1_1 wo wa wo fcad1_0 fcad1_1 wo fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wxo wo fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wo pm5.63 fcad1_0 fcad1_1 wo fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wo wo fcad1_0 fcad1_1 wo fcad1_0 fcad1_1 wa olc fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wo fcad1_0 fcad1_1 wo fcad1_0 fcad1_0 fcad1_1 wo fcad1_1 fcad1_0 fcad1_1 orc adantr fcad1_0 fcad1_1 wo id jaoi impbii fcad1_0 fcad1_1 wxo fcad1_0 fcad1_1 wa wn fcad1_0 fcad1_1 wo wa fcad1_0 fcad1_1 wa fcad1_0 fcad1_1 wxo fcad1_0 fcad1_1 wo fcad1_0 fcad1_1 wa wn wa fcad1_0 fcad1_1 wa wn fcad1_0 fcad1_1 wo wa fcad1_0 fcad1_1 xor2 fcad1_0 fcad1_1 wo fcad1_0 fcad1_1 wa wn ancom bitri orbi2i 3bitr4i 3bitr4g $.
$}
$( /* If two parameters are true, the adder carry is true.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) */

$)
${
	fcad11_0 $f wff ph $.
	fcad11_1 $f wff ps $.
	fcad11_2 $f wff ch $.
	cad11 $p |- ( ( ph /\ ps ) -> cadd ( ph , ps , ch ) ) $= fcad11_0 fcad11_1 wa fcad11_0 fcad11_1 wa fcad11_2 fcad11_0 fcad11_1 wxo wa wo fcad11_0 fcad11_1 fcad11_2 wcad fcad11_0 fcad11_1 wa fcad11_2 fcad11_0 fcad11_1 wxo wa orc fcad11_0 fcad11_1 fcad11_2 df-cad sylibr $.
$}
$( /* If one parameter is false, the adder carry is true exactly when both of
     the other two parameters are true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) */

$)
${
	fcad0_0 $f wff ph $.
	fcad0_1 $f wff ps $.
	fcad0_2 $f wff ch $.
	cad0 $p |- ( -. ch -> ( cadd ( ph , ps , ch ) <-> ( ph /\ ps ) ) ) $= fcad0_0 fcad0_1 fcad0_2 wcad fcad0_0 fcad0_1 wa fcad0_2 fcad0_0 fcad0_1 wxo wa wo fcad0_2 wn fcad0_0 fcad0_1 wa fcad0_0 fcad0_1 fcad0_2 df-cad fcad0_2 wn fcad0_0 fcad0_1 wa fcad0_2 fcad0_0 fcad0_1 wxo wa wo fcad0_0 fcad0_1 wa fcad0_2 wn fcad0_0 fcad0_1 wa fcad0_0 fcad0_1 wa fcad0_2 fcad0_0 fcad0_1 wxo wa fcad0_2 wn fcad0_0 fcad0_1 wa idd fcad0_2 wn fcad0_2 fcad0_0 fcad0_1 wa fcad0_0 fcad0_1 wxo fcad0_2 fcad0_0 fcad0_1 wa pm2.21 adantrd jaod fcad0_0 fcad0_1 wa fcad0_2 fcad0_0 fcad0_1 wxo wa orc impbid1 syl5bb $.
$}
$( /* Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fcadtru_0 $f wff ph $.
	cadtru $p |- cadd ( T. , T. , ph ) $= wtru wtru wtru wtru fcadtru_0 wcad tru tru wtru wtru fcadtru_0 cad11 mp2an $.
$}
$( /* If the first parameter is true, the half adder is equivalent to the
     equality of the other two inputs.  (Contributed by Mario Carneiro,
     4-Sep-2016.) */

$)
${
	fhad1_0 $f wff ph $.
	fhad1_1 $f wff ps $.
	fhad1_2 $f wff ch $.
	had1 $p |- ( ph -> ( hadd ( ph , ps , ch ) <-> ( ps <-> ch ) ) ) $= fhad1_0 fhad1_1 fhad1_2 whad fhad1_0 fhad1_1 fhad1_2 wb wb fhad1_0 fhad1_1 fhad1_2 wb fhad1_0 fhad1_1 fhad1_2 whad fhad1_0 fhad1_1 wb fhad1_2 wb fhad1_0 fhad1_1 fhad1_2 wb wb fhad1_0 fhad1_1 fhad1_2 hadbi fhad1_0 fhad1_1 fhad1_2 biass bitri fhad1_0 fhad1_0 fhad1_1 fhad1_2 wb fhad1_1 fhad1_2 wb wb wb fhad1_0 fhad1_1 fhad1_2 wb wb fhad1_1 fhad1_2 wb wb fhad1_0 fhad1_0 fhad1_1 fhad1_2 wb fhad1_1 fhad1_2 wb wb fhad1_0 id fhad1_0 fhad1_1 fhad1_2 wb biidd 2thd fhad1_0 fhad1_1 fhad1_2 wb fhad1_1 fhad1_2 wb biass sylibr syl5bb $.
$}
$( /* If the first parameter is false, the half adder is equivalent to the XOR
     of the other two inputs.  (Contributed by Mario Carneiro, 4-Sep-2016.) */

$)
${
	fhad0_0 $f wff ph $.
	fhad0_1 $f wff ps $.
	fhad0_2 $f wff ch $.
	had0 $p |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) ) $= fhad0_0 wn fhad0_0 fhad0_1 fhad0_2 whad fhad0_1 fhad0_2 wxo fhad0_0 wn fhad0_0 wn fhad0_1 wn fhad0_2 wn whad fhad0_1 wn fhad0_2 wn wb fhad0_0 fhad0_1 fhad0_2 whad wn fhad0_1 fhad0_2 wxo wn fhad0_0 wn fhad0_1 wn fhad0_2 wn had1 fhad0_0 fhad0_1 fhad0_2 hadnot fhad0_1 wn fhad0_2 wn wb fhad0_1 fhad0_2 wxo fhad0_1 wn fhad0_2 wn wb wn fhad0_1 wn fhad0_2 wn wxo fhad0_1 fhad0_2 wxo fhad0_1 wn fhad0_2 wn df-xor fhad0_1 fhad0_2 xorneg bitr3i con1bii 3bitr4g con4bid $.
$}

