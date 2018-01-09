$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Ordered-pair_class_abstractions_(cont_).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Power class of union and intersection

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( The power class of the intersection of two classes is the intersection
       of their power classes.  Exercise 4.12(j) of [Mendelson] p. 235.
       (Contributed by NM, 23-Nov-2003.) $)
${
	$d A x $.
	$d B x $.
	ipwin_0 $f set x $.
	fpwin_0 $f class A $.
	fpwin_1 $f class B $.
	pwin $p |- ~P ( A i^i B ) = ( ~P A i^i ~P B ) $= fpwin_0 cpw fpwin_1 cpw cin fpwin_0 fpwin_1 cin cpw ipwin_0 fpwin_0 cpw fpwin_1 cpw fpwin_0 fpwin_1 cin cpw ipwin_0 sup_set_class fpwin_0 wss ipwin_0 sup_set_class fpwin_1 wss wa ipwin_0 sup_set_class fpwin_0 fpwin_1 cin wss ipwin_0 sup_set_class fpwin_0 cpw wcel ipwin_0 sup_set_class fpwin_1 cpw wcel wa ipwin_0 sup_set_class fpwin_0 fpwin_1 cin cpw wcel ipwin_0 sup_set_class fpwin_0 fpwin_1 ssin ipwin_0 sup_set_class fpwin_0 cpw wcel ipwin_0 sup_set_class fpwin_0 wss ipwin_0 sup_set_class fpwin_1 cpw wcel ipwin_0 sup_set_class fpwin_1 wss ipwin_0 sup_set_class fpwin_0 ipwin_0 vex elpw ipwin_0 sup_set_class fpwin_1 ipwin_0 vex elpw anbi12i ipwin_0 sup_set_class fpwin_0 fpwin_1 cin ipwin_0 vex elpw 3bitr4i ineqri eqcomi $.
$}
$( The power class of the union of two classes includes the union of their
       power classes.  Exercise 4.12(k) of [Mendelson] p. 235.  (Contributed by
       NM, 23-Nov-2003.) $)
${
	$d A x $.
	$d B x $.
	ipwunss_0 $f set x $.
	fpwunss_0 $f class A $.
	fpwunss_1 $f class B $.
	pwunss $p |- ( ~P A u. ~P B ) C_ ~P ( A u. B ) $= ipwunss_0 fpwunss_0 cpw fpwunss_1 cpw cun fpwunss_0 fpwunss_1 cun cpw ipwunss_0 sup_set_class fpwunss_0 wss ipwunss_0 sup_set_class fpwunss_1 wss wo ipwunss_0 sup_set_class fpwunss_0 fpwunss_1 cun wss ipwunss_0 sup_set_class fpwunss_0 cpw fpwunss_1 cpw cun wcel ipwunss_0 sup_set_class fpwunss_0 fpwunss_1 cun cpw wcel ipwunss_0 sup_set_class fpwunss_0 fpwunss_1 ssun ipwunss_0 sup_set_class fpwunss_0 cpw fpwunss_1 cpw cun wcel ipwunss_0 sup_set_class fpwunss_0 cpw wcel ipwunss_0 sup_set_class fpwunss_1 cpw wcel wo ipwunss_0 sup_set_class fpwunss_0 wss ipwunss_0 sup_set_class fpwunss_1 wss wo ipwunss_0 sup_set_class fpwunss_0 cpw fpwunss_1 cpw elun ipwunss_0 sup_set_class fpwunss_0 cpw wcel ipwunss_0 sup_set_class fpwunss_0 wss ipwunss_0 sup_set_class fpwunss_1 cpw wcel ipwunss_0 sup_set_class fpwunss_1 wss ipwunss_0 sup_set_class fpwunss_0 ipwunss_0 vex elpw ipwunss_0 sup_set_class fpwunss_1 ipwunss_0 vex elpw orbi12i bitri ipwunss_0 sup_set_class fpwunss_0 fpwunss_1 cun ipwunss_0 vex elpw 3imtr4i ssriv $.
$}
$( The power class of the union of two classes is a subset of the union of
       their power classes, iff one class is a subclass of the other.  Exercise
       4.12(l) of [Mendelson] p. 235.  (Contributed by NM, 23-Nov-2003.) $)
${
	$d A x y $.
	$d B x y $.
	ipwssun_0 $f set x $.
	ipwssun_1 $f set y $.
	fpwssun_0 $f class A $.
	fpwssun_1 $f class B $.
	pwssun $p |- ( ( A C_ B \/ B C_ A ) <-> ~P ( A u. B ) C_ ( ~P A u. ~P B ) ) $= fpwssun_0 fpwssun_1 wss fpwssun_1 fpwssun_0 wss wo fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss fpwssun_0 fpwssun_1 wss fpwssun_1 fpwssun_0 wss wo fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw wss fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw wss wo fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss fpwssun_1 fpwssun_0 wss fpwssun_0 fpwssun_1 wss fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw wss fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw wss wo fpwssun_1 fpwssun_0 wss fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw wss fpwssun_0 fpwssun_1 wss fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw wss fpwssun_1 fpwssun_0 wss fpwssun_0 fpwssun_1 cun fpwssun_0 wceq fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw wss fpwssun_1 fpwssun_0 ssequn2 fpwssun_0 fpwssun_1 cun fpwssun_0 wceq fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw wceq fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw wss fpwssun_0 fpwssun_1 cun fpwssun_0 pweq fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw eqimss syl sylbi fpwssun_0 fpwssun_1 wss fpwssun_0 fpwssun_1 cun fpwssun_1 wceq fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw wss fpwssun_0 fpwssun_1 ssequn1 fpwssun_0 fpwssun_1 cun fpwssun_1 wceq fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw wceq fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw wss fpwssun_0 fpwssun_1 cun fpwssun_1 pweq fpwssun_0 fpwssun_1 cun cpw fpwssun_1 cpw eqimss syl sylbi orim12i orcoms fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw ssun syl fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss fpwssun_0 fpwssun_1 wss fpwssun_1 fpwssun_0 wss fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss fpwssun_0 fpwssun_1 wss wn fpwssun_1 fpwssun_0 wss fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss fpwssun_0 fpwssun_1 wss wn wa ipwssun_1 fpwssun_1 fpwssun_0 fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss fpwssun_0 fpwssun_1 wss wn ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_1 sup_set_class fpwssun_0 wcel wi fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel fpwssun_0 fpwssun_1 wss wn ipwssun_1 sup_set_class fpwssun_0 wcel fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_1 sup_set_class fpwssun_0 wcel wn fpwssun_0 fpwssun_1 wss wi fpwssun_0 fpwssun_1 wss wn ipwssun_1 sup_set_class fpwssun_0 wcel wi fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_1 sup_set_class fpwssun_0 wcel wn fpwssun_0 fpwssun_1 wss fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_1 sup_set_class fpwssun_0 wcel wn wa ipwssun_0 fpwssun_0 fpwssun_1 fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_1 sup_set_class fpwssun_0 wcel wn ipwssun_0 sup_set_class fpwssun_1 wcel fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class fpwssun_0 wcel wa ipwssun_1 sup_set_class fpwssun_0 wcel ipwssun_0 sup_set_class fpwssun_1 wcel fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class fpwssun_0 wcel wa ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 cpw wcel wo ipwssun_1 sup_set_class fpwssun_0 wcel ipwssun_0 sup_set_class fpwssun_1 wcel wo fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class fpwssun_0 wcel wa ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw fpwssun_1 cpw cun wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 cpw wcel wo fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw fpwssun_1 cpw cun wcel fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw fpwssun_1 cpw cun wcel ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 fpwssun_1 cun cpw wcel fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun wss ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw fpwssun_1 cpw cun wcel ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class csn ipwssun_1 sup_set_class csn cun fpwssun_0 fpwssun_1 cun wss ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 fpwssun_1 cun cpw wcel ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_0 sup_set_class csn fpwssun_0 wss ipwssun_1 sup_set_class csn fpwssun_1 wss ipwssun_0 sup_set_class csn ipwssun_1 sup_set_class csn cun fpwssun_0 fpwssun_1 cun wss ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_0 sup_set_class fpwssun_0 ipwssun_0 vex snss ipwssun_1 sup_set_class fpwssun_1 ipwssun_1 vex snss ipwssun_0 sup_set_class csn fpwssun_0 ipwssun_1 sup_set_class csn fpwssun_1 unss12 syl2anb ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 fpwssun_1 cun cpw wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 fpwssun_1 cun wss ipwssun_0 sup_set_class csn ipwssun_1 sup_set_class csn cun fpwssun_0 fpwssun_1 cun wss ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 fpwssun_1 cun ipwssun_0 ipwssun_1 zfpair2 elpw ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr ipwssun_0 sup_set_class csn ipwssun_1 sup_set_class csn cun fpwssun_0 fpwssun_1 cun ipwssun_0 sup_set_class ipwssun_1 sup_set_class df-pr sseq1i bitr2i sylib fpwssun_0 fpwssun_1 cun cpw fpwssun_0 cpw fpwssun_1 cpw cun ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr ssel syl5 exp3acom23 imp31 ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw fpwssun_1 cpw elun sylib ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw wcel ipwssun_1 sup_set_class fpwssun_0 wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 cpw wcel ipwssun_0 sup_set_class fpwssun_1 wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw wcel ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_1 sup_set_class fpwssun_0 wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 cpw wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 wss ipwssun_0 sup_set_class fpwssun_0 wcel ipwssun_1 sup_set_class fpwssun_0 wcel wa ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_0 ipwssun_0 ipwssun_1 zfpair2 elpw ipwssun_0 sup_set_class ipwssun_1 sup_set_class fpwssun_0 ipwssun_0 vex ipwssun_1 vex prss bitr4i simprbi ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 cpw wcel ipwssun_0 sup_set_class fpwssun_1 wcel ipwssun_1 sup_set_class fpwssun_1 wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 cpw wcel ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 wss ipwssun_0 sup_set_class fpwssun_1 wcel ipwssun_1 sup_set_class fpwssun_1 wcel wa ipwssun_0 sup_set_class ipwssun_1 sup_set_class cpr fpwssun_1 ipwssun_0 ipwssun_1 zfpair2 elpw ipwssun_0 sup_set_class ipwssun_1 sup_set_class fpwssun_1 ipwssun_0 vex ipwssun_1 vex prss bitr4i simplbi orim12i syl ord impancom ssrdv exp31 ipwssun_1 sup_set_class fpwssun_0 wcel fpwssun_0 fpwssun_1 wss con1b syl6ib com23 imp ssrdv ex orrd impbii $.
$}
$( Break up the power class of a union into a union of smaller classes.
       (Contributed by NM, 25-Mar-2007.)  (Proof shortened by Thierry Arnoux,
       20-Dec-2016.) $)
${
	fpwundif_0 $f class A $.
	fpwundif_1 $f class B $.
	pwundif $p |- ~P ( A u. B ) = ( ( ~P ( A u. B ) \ ~P A ) u. ~P A ) $= fpwundif_0 fpwundif_1 cun cpw fpwundif_0 cpw cdif fpwundif_0 cpw cun fpwundif_0 fpwundif_1 cun cpw fpwundif_0 cpw cun fpwundif_0 fpwundif_1 cun cpw fpwundif_0 fpwundif_1 cun cpw fpwundif_0 cpw undif1 fpwundif_0 cpw fpwundif_0 fpwundif_1 cun cpw wss fpwundif_0 fpwundif_1 cun cpw fpwundif_0 cpw cun fpwundif_0 fpwundif_1 cun cpw wceq fpwundif_0 cpw fpwundif_0 fpwundif_1 cun cpw wss fpwundif_1 cpw fpwundif_0 fpwundif_1 cun cpw wss fpwundif_0 cpw fpwundif_0 fpwundif_1 cun cpw wss fpwundif_1 cpw fpwundif_0 fpwundif_1 cun cpw wss wa fpwundif_0 cpw fpwundif_1 cpw cun fpwundif_0 fpwundif_1 cun cpw wss fpwundif_0 fpwundif_1 pwunss fpwundif_0 cpw fpwundif_1 cpw fpwundif_0 fpwundif_1 cun cpw unss mpbir simpli fpwundif_0 cpw fpwundif_0 fpwundif_1 cun cpw ssequn2 mpbi eqtr2i $.
$}
$( Break up the power class of a union into a union of smaller classes.
       Obsolete as of 20-Dec-2016.  (Contributed by NM, 25-Mar-2007.)
       (New usage is discouraged.) $)
${
	$d A x $.
	$d B x $.
	ipwundifOLD_0 $f set x $.
	fpwundifOLD_0 $f class A $.
	fpwundifOLD_1 $f class B $.
	pwundifOLD $p |- ~P ( A u. B ) = ( ( ~P ( A u. B ) \ ~P A ) u. ~P A ) $= ipwundifOLD_0 fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif fpwundifOLD_0 cpw cun ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif fpwundifOLD_0 cpw cun wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun ipwundifOLD_0 vex elpw ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn wa ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif fpwundifOLD_0 cpw cun wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn wa ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss pm2.1 ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss ordir mpbiran2 ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif fpwundifOLD_0 cpw cun wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 cpw wcel wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn wa ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif fpwundifOLD_0 cpw elun ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn wa ipwundifOLD_0 sup_set_class fpwundifOLD_0 cpw wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw cdif wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 cpw wcel wn wa ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn wa ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw fpwundifOLD_0 cpw eldif ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun cpw wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 cpw wcel wn ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wn ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun ipwundifOLD_0 vex elpw ipwundifOLD_0 sup_set_class fpwundifOLD_0 cpw wcel ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 ipwundifOLD_0 vex elpw notbii anbi12i bitri ipwundifOLD_0 sup_set_class fpwundifOLD_0 ipwundifOLD_0 vex elpw orbi12i bitr2i ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss wo ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss id ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 ssun3 jaoi ipwundifOLD_0 sup_set_class fpwundifOLD_0 fpwundifOLD_1 cun wss ipwundifOLD_0 sup_set_class fpwundifOLD_0 wss orc impbii 3bitr3ri bitri eqriv $.
$}
$( The power class of the union of two classes equals the union of their
     power classes, iff one class is a subclass of the other.  Part of Exercise
     7(b) of [Enderton] p. 28.  (Contributed by NM, 23-Nov-2003.) $)
${
	fpwun_0 $f class A $.
	fpwun_1 $f class B $.
	pwun $p |- ( ( A C_ B \/ B C_ A ) <-> ~P ( A u. B ) = ( ~P A u. ~P B ) ) $= fpwun_0 fpwun_1 cun cpw fpwun_0 cpw fpwun_1 cpw cun wss fpwun_0 fpwun_1 cun cpw fpwun_0 cpw fpwun_1 cpw cun wss fpwun_0 cpw fpwun_1 cpw cun fpwun_0 fpwun_1 cun cpw wss wa fpwun_0 fpwun_1 wss fpwun_1 fpwun_0 wss wo fpwun_0 fpwun_1 cun cpw fpwun_0 cpw fpwun_1 cpw cun wceq fpwun_0 cpw fpwun_1 cpw cun fpwun_0 fpwun_1 cun cpw wss fpwun_0 fpwun_1 cun cpw fpwun_0 cpw fpwun_1 cpw cun wss fpwun_0 fpwun_1 pwunss biantru fpwun_0 fpwun_1 pwssun fpwun_0 fpwun_1 cun cpw fpwun_0 cpw fpwun_1 cpw cun eqss 3bitr4i $.
$}

