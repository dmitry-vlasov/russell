$[ turnstile_special_source.mm $]
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Finite_induction_(for_finite_ordinals).mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                              Relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Introduce new constant symbols. $)
$c X.  $.
$( Times symbol (cross product symbol) (read: 'cross') $)
$c `'  $.
$( Small elevated smiley (converse operation) $)
$c dom  $.
$( Domain $)
$c ran  $.
$( Range $)
$c |`  $.
$( Right hook (restriction symbol) $)
$c "  $.
$( Left quote (image symbol) $)
$c o.  $.
$( Small circle (composition symbol) $)
$c Rel  $.
$( Relation predicate $)
$( Extend the definition of a class to include the cross product. $)
${
	fcxp_0 $f class A $.
	fcxp_1 $f class B $.
	cxp $a class ( A X. B ) $.
$}
$( Extend the definition of a class to include the converse of a class. $)
${
	fccnv_0 $f class A $.
	ccnv $a class `' A $.
$}
$( Extend the definition of a class to include the domain of a class. $)
${
	fcdm_0 $f class A $.
	cdm $a class dom A $.
$}
$( Extend the definition of a class to include the range of a class. $)
${
	fcrn_0 $f class A $.
	crn $a class ran A $.
$}
$( Extend the definition of a class to include the restriction of a class.
     (Read:  The restriction of ` A ` to ` B ` .) $)
${
	fcres_0 $f class A $.
	fcres_1 $f class B $.
	cres $a class ( A |` B ) $.
$}
$( Extend the definition of a class to include the image of a class.  (Read:
     The image of ` B ` under ` A ` .) $)
${
	fcima_0 $f class A $.
	fcima_1 $f class B $.
	cima $a class ( A " B ) $.
$}
$( Extend the definition of a class to include the composition of two
     classes.  (Read:  The composition of ` A ` and ` B ` .) $)
${
	fccom_0 $f class A $.
	fccom_1 $f class B $.
	ccom $a class ( A o. B ) $.
$}
$( Extend the definition of a wff to include the relation predicate.  (Read:
     ` A ` is a relation.) $)
${
	fwrel_0 $f class A $.
	wrel $a wff Rel A $.
$}
$( Define the cross product of two classes.  Definition 9.11 of [Quine]
       p. 64.  For example, ` ( { 1 , 5 } X. { 2 , 7 } ) = `
       ` ( { <. 1 , 2 >. , <. 1 , 7 >. } u. { <. 5 , 2 >. , <. 5 , 7 >. } ) `
       ( ~ ex-xp ).  Another example is that the set of rational numbers are
       defined in ~ df-q using the cross-product ` ( ZZ X. NN ) ` ; the left-
       and right-hand sides of the cross-product represent the top (integer)
       and bottom (natural) numbers of a fraction.  (Contributed by NM,
       4-Jul-1994.) $)
${
	$d x y A $.
	$d x y B $.
	fdf-xp_0 $f set x $.
	fdf-xp_1 $f set y $.
	fdf-xp_2 $f class A $.
	fdf-xp_3 $f class B $.
	df-xp $a |- ( A X. B ) = { <. x , y >. | ( x e. A /\ y e. B ) } $.
$}
$( Define the relation predicate.  Definition 6.4(1) of [TakeutiZaring]
       p. 23.  For alternate definitions, see ~ dfrel2 and ~ dfrel3 .
       (Contributed by NM, 1-Aug-1994.) $)
${
	fdf-rel_0 $f class A $.
	df-rel $a |- ( Rel A <-> A C_ ( _V X. _V ) ) $.
$}
$( Define the converse of a class.  Definition 9.12 of [Quine] p. 64.  The
       converse of a binary relation swaps its arguments, i.e., if ` A e. _V `
       and ` B e. _V ` then ` ( A ``' R B <-> B R A ) ` , as proven in ~ brcnv
       (see ~ df-br and ~ df-rel for more on relations).  For example,
       ` ``' { <. 2 , 6 >. , <. 3 , 9 >. } = { <. 6 , 2 >. , <. 9 , 3 >. } `
       ( ~ ex-cnv ).  We use Quine's breve accent (smile) notation.  Like
       Quine, we use it as a prefix, which eliminates the need for
       parentheses.  Many authors use the postfix superscript "to the minus
       one."  "Converse" is Quine's terminology; some authors call it
       "inverse," especially when the argument is a function.  (Contributed by
       NM, 4-Jul-1994.) $)
${
	$d x y A $.
	$d x y $.
	fdf-cnv_0 $f set x $.
	fdf-cnv_1 $f set y $.
	fdf-cnv_2 $f class A $.
	df-cnv $a |- `' A = { <. x , y >. | y A x } $.
$}
$( Define the composition of two classes.  Definition 6.6(3) of
       [TakeutiZaring] p. 24.  For example, ` ( ( exp o. cos ) `` 0 ) = _e `
       ( ~ ex-co ) because ` ( cos `` 0 ) = 1 ` (see ~ cos0 ) and
       ` ( exp `` 1 ) = _e ` (see ~ df-e ).  Note that Definition 7 of [Suppes]
       p. 63 reverses ` A ` and ` B ` , uses ` /. ` instead of ` o. ` , and
       calls the operation "relative product."  (Contributed by NM,
       4-Jul-1994.) $)
${
	$d x y z A $.
	$d x y z B $.
	fdf-co_0 $f set x $.
	fdf-co_1 $f set y $.
	fdf-co_2 $f set z $.
	fdf-co_3 $f class A $.
	fdf-co_4 $f class B $.
	df-co $a |- ( A o. B ) = { <. x , y >. | E. z ( x B z /\ z A y ) } $.
$}
$( Define the domain of a class.  Definition 3 of [Suppes] p. 59.  For
       example, ` F = { <. 2 , 6 >. , <. 3 , 9 >. } -> dom F = { 2 , 3 } `
       ( ~ ex-dm ).  Another example is the domain of the complex arctangent,
       ` ( A e. dom arctan <-> ( A e. CC /\ A =/= -u _i /\ A =/= _i ) ) ` (for
       proof see ~ atandm ).  Contrast with range (defined in ~ df-rn ).  For
       alternate definitions see ~ dfdm2 , ~ dfdm3 , and ~ dfdm4 .  The
       notation " ` dom ` " is used by Enderton; other authors sometimes use
       script D. (Contributed by NM, 1-Aug-1994.) $)
${
	$d x y A $.
	$d x y $.
	fdf-dm_0 $f set x $.
	fdf-dm_1 $f set y $.
	fdf-dm_2 $f class A $.
	df-dm $a |- dom A = { x | E. y x A y } $.
$}
$( Define the range of a class.  For example,
       ` F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ran F = { 6 , 9 } ` ( ~ ex-rn ).
       Contrast with domain (defined in ~ df-dm ).  For alternate definitions,
       see ~ dfrn2 , ~ dfrn3 , and ~ dfrn4 .  The notation " ` ran ` " is used
       by Enderton; other authors sometimes use script R or script W.
       (Contributed by NM, 1-Aug-1994.) $)
${
	fdf-rn_0 $f class A $.
	df-rn $a |- ran A = dom `' A $.
$}
$( Define the restriction of a class.  Definition 6.6(1) of [TakeutiZaring]
       p. 24.  For example, the expression ` ( exp |`` RR ) ` (used in
       ~ reeff1 ) means "the exponential function e to the x, but the exponent
       x must be in the reals" ( ~ df-ef defines the exponential function,
       which normally allows the exponent to be a complex number).  Another
       example is that ` ( F = { <. 2 , 6 >. , <. 3 , 9 >. } `
       ` /\ B = { 1 , 2 } ) -> ( F |`` B ) = { <. 2 , 6 >. } ` ( ~ ex-res ).
       (Contributed by NM, 2-Aug-1994.) $)
${
	fdf-res_0 $f class A $.
	fdf-res_1 $f class B $.
	df-res $a |- ( A |` B ) = ( A i^i ( B X. _V ) ) $.
$}
$( Define the image of a class (as restricted by another class).
       Definition 6.6(2) of [TakeutiZaring] p. 24.  For example,
` ( F = { <. 2 , 6 >. , <. 3 , 9 >. } /\ B = { 1 , 2 } ) -> ( F " B ) = { 6 } `
       ( ~ ex-ima ).  Contrast with restriction ( ~ df-res ) and range
       ( ~ df-rn ).  For an alternate definition, see ~ dfima2 .  (Contributed
       by NM, 2-Aug-1994.) $)
${
	fdf-ima_0 $f class A $.
	fdf-ima_1 $f class B $.
	df-ima $a |- ( A " B ) = ran ( A |` B ) $.
$}
$( Equality theorem for cross product.  (Contributed by NM, 4-Jul-1994.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ixpeq1_0 $f set x $.
	ixpeq1_1 $f set y $.
	fxpeq1_0 $f class A $.
	fxpeq1_1 $f class B $.
	fxpeq1_2 $f class C $.
	xpeq1 $p |- ( A = B -> ( A X. C ) = ( B X. C ) ) $= fxpeq1_0 fxpeq1_1 wceq ixpeq1_0 sup_set_class fxpeq1_0 wcel ixpeq1_1 sup_set_class fxpeq1_2 wcel wa ixpeq1_0 ixpeq1_1 copab ixpeq1_0 sup_set_class fxpeq1_1 wcel ixpeq1_1 sup_set_class fxpeq1_2 wcel wa ixpeq1_0 ixpeq1_1 copab fxpeq1_0 fxpeq1_2 cxp fxpeq1_1 fxpeq1_2 cxp fxpeq1_0 fxpeq1_1 wceq ixpeq1_0 sup_set_class fxpeq1_0 wcel ixpeq1_1 sup_set_class fxpeq1_2 wcel wa ixpeq1_0 sup_set_class fxpeq1_1 wcel ixpeq1_1 sup_set_class fxpeq1_2 wcel wa ixpeq1_0 ixpeq1_1 fxpeq1_0 fxpeq1_1 wceq ixpeq1_0 sup_set_class fxpeq1_0 wcel ixpeq1_0 sup_set_class fxpeq1_1 wcel ixpeq1_1 sup_set_class fxpeq1_2 wcel fxpeq1_0 fxpeq1_1 ixpeq1_0 sup_set_class eleq2 anbi1d opabbidv ixpeq1_0 ixpeq1_1 fxpeq1_0 fxpeq1_2 df-xp ixpeq1_0 ixpeq1_1 fxpeq1_1 fxpeq1_2 df-xp 3eqtr4g $.
$}
$( Equality theorem for cross product.  (Contributed by NM, 5-Jul-1994.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ixpeq2_0 $f set x $.
	ixpeq2_1 $f set y $.
	fxpeq2_0 $f class A $.
	fxpeq2_1 $f class B $.
	fxpeq2_2 $f class C $.
	xpeq2 $p |- ( A = B -> ( C X. A ) = ( C X. B ) ) $= fxpeq2_0 fxpeq2_1 wceq ixpeq2_0 sup_set_class fxpeq2_2 wcel ixpeq2_1 sup_set_class fxpeq2_0 wcel wa ixpeq2_0 ixpeq2_1 copab ixpeq2_0 sup_set_class fxpeq2_2 wcel ixpeq2_1 sup_set_class fxpeq2_1 wcel wa ixpeq2_0 ixpeq2_1 copab fxpeq2_2 fxpeq2_0 cxp fxpeq2_2 fxpeq2_1 cxp fxpeq2_0 fxpeq2_1 wceq ixpeq2_0 sup_set_class fxpeq2_2 wcel ixpeq2_1 sup_set_class fxpeq2_0 wcel wa ixpeq2_0 sup_set_class fxpeq2_2 wcel ixpeq2_1 sup_set_class fxpeq2_1 wcel wa ixpeq2_0 ixpeq2_1 fxpeq2_0 fxpeq2_1 wceq ixpeq2_1 sup_set_class fxpeq2_0 wcel ixpeq2_1 sup_set_class fxpeq2_1 wcel ixpeq2_0 sup_set_class fxpeq2_2 wcel fxpeq2_0 fxpeq2_1 ixpeq2_1 sup_set_class eleq2 anbi2d opabbidv ixpeq2_0 ixpeq2_1 fxpeq2_2 fxpeq2_0 df-xp ixpeq2_0 ixpeq2_1 fxpeq2_2 fxpeq2_1 df-xp 3eqtr4g $.
$}
$( Membership in a cross product.  Uses fewer axioms than ~ elxp .
       (Contributed by NM, 4-Jul-1994.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	ielxpi_0 $f set z $.
	felxpi_0 $f set x $.
	felxpi_1 $f set y $.
	felxpi_2 $f class A $.
	felxpi_3 $f class B $.
	felxpi_4 $f class C $.
	elxpi $p |- ( A e. ( B X. C ) -> E. x E. y ( A = <. x , y >. /\ ( x e. B /\ y e. C ) ) ) $= felxpi_2 felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex felxpi_2 ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex ielxpi_0 cab felxpi_3 felxpi_4 cxp felxpi_2 ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex ielxpi_0 cab wcel felxpi_2 felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex felxpi_2 felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex ielxpi_0 felxpi_2 ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex ielxpi_0 cab ielxpi_0 sup_set_class felxpi_2 wceq ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_2 felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_0 felxpi_1 ielxpi_0 sup_set_class felxpi_2 wceq ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_2 felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa ielxpi_0 sup_set_class felxpi_2 felxpi_0 sup_set_class felxpi_1 sup_set_class cop eqeq1 anbi1d 2exbidv elabg ibi felxpi_3 felxpi_4 cxp felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa felxpi_0 felxpi_1 copab ielxpi_0 sup_set_class felxpi_0 sup_set_class felxpi_1 sup_set_class cop wceq felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa wa felxpi_1 wex felxpi_0 wex ielxpi_0 cab felxpi_0 felxpi_1 felxpi_3 felxpi_4 df-xp felxpi_0 sup_set_class felxpi_3 wcel felxpi_1 sup_set_class felxpi_4 wcel wa felxpi_0 felxpi_1 ielxpi_0 df-opab eqtri eleq2s $.
$}
$( Membership in a cross product.  (Contributed by NM, 4-Jul-1994.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	felxp_0 $f set x $.
	felxp_1 $f set y $.
	felxp_2 $f class A $.
	felxp_3 $f class B $.
	felxp_4 $f class C $.
	elxp $p |- ( A e. ( B X. C ) <-> E. x E. y ( A = <. x , y >. /\ ( x e. B /\ y e. C ) ) ) $= felxp_2 felxp_3 felxp_4 cxp wcel felxp_2 felxp_0 sup_set_class felxp_3 wcel felxp_1 sup_set_class felxp_4 wcel wa felxp_0 felxp_1 copab wcel felxp_2 felxp_0 sup_set_class felxp_1 sup_set_class cop wceq felxp_0 sup_set_class felxp_3 wcel felxp_1 sup_set_class felxp_4 wcel wa wa felxp_1 wex felxp_0 wex felxp_3 felxp_4 cxp felxp_0 sup_set_class felxp_3 wcel felxp_1 sup_set_class felxp_4 wcel wa felxp_0 felxp_1 copab felxp_2 felxp_0 felxp_1 felxp_3 felxp_4 df-xp eleq2i felxp_0 sup_set_class felxp_3 wcel felxp_1 sup_set_class felxp_4 wcel wa felxp_0 felxp_1 felxp_2 elopab bitri $.
$}
$( Membership in a cross product.  (Contributed by NM, 23-Feb-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	felxp2_0 $f set x $.
	felxp2_1 $f set y $.
	felxp2_2 $f class A $.
	felxp2_3 $f class B $.
	felxp2_4 $f class C $.
	elxp2 $p |- ( A e. ( B X. C ) <-> E. x e. B E. y e. C A = <. x , y >. ) $= felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_1 felxp2_4 wrex wa felxp2_0 wex felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_0 sup_set_class felxp2_3 wcel felxp2_1 sup_set_class felxp2_4 wcel wa wa felxp2_1 wex felxp2_0 wex felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_1 felxp2_4 wrex felxp2_0 felxp2_3 wrex felxp2_2 felxp2_3 felxp2_4 cxp wcel felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_1 felxp2_4 wrex wa felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_0 sup_set_class felxp2_3 wcel felxp2_1 sup_set_class felxp2_4 wcel wa wa felxp2_1 wex felxp2_0 felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq wa felxp2_1 felxp2_4 wrex felxp2_1 sup_set_class felxp2_4 wcel felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq wa wa felxp2_1 wex felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_1 felxp2_4 wrex wa felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_0 sup_set_class felxp2_3 wcel felxp2_1 sup_set_class felxp2_4 wcel wa wa felxp2_1 wex felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq wa felxp2_1 felxp2_4 df-rex felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_1 felxp2_4 r19.42v felxp2_1 sup_set_class felxp2_4 wcel felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq wa wa felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_0 sup_set_class felxp2_3 wcel felxp2_1 sup_set_class felxp2_4 wcel wa wa felxp2_1 felxp2_1 sup_set_class felxp2_4 wcel felxp2_0 sup_set_class felxp2_3 wcel felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq an13 exbii 3bitr3i exbii felxp2_2 felxp2_0 sup_set_class felxp2_1 sup_set_class cop wceq felxp2_1 felxp2_4 wrex felxp2_0 felxp2_3 df-rex felxp2_0 felxp2_1 felxp2_2 felxp2_3 felxp2_4 elxp 3bitr4ri $.
$}
$( Equality theorem for cross product.  (Contributed by FL, 31-Aug-2009.) $)
${
	fxpeq12_0 $f class A $.
	fxpeq12_1 $f class B $.
	fxpeq12_2 $f class C $.
	fxpeq12_3 $f class D $.
	xpeq12 $p |- ( ( A = B /\ C = D ) -> ( A X. C ) = ( B X. D ) ) $= fxpeq12_0 fxpeq12_1 wceq fxpeq12_2 fxpeq12_3 wceq fxpeq12_0 fxpeq12_2 cxp fxpeq12_1 fxpeq12_2 cxp fxpeq12_1 fxpeq12_3 cxp fxpeq12_0 fxpeq12_1 fxpeq12_2 xpeq1 fxpeq12_2 fxpeq12_3 fxpeq12_1 xpeq2 sylan9eq $.
$}
$( Equality inference for cross product.  (Contributed by NM,
       21-Dec-2008.) $)
${
	fxpeq1i_0 $f class A $.
	fxpeq1i_1 $f class B $.
	fxpeq1i_2 $f class C $.
	expeq1i_0 $e |- A = B $.
	xpeq1i $p |- ( A X. C ) = ( B X. C ) $= fxpeq1i_0 fxpeq1i_1 wceq fxpeq1i_0 fxpeq1i_2 cxp fxpeq1i_1 fxpeq1i_2 cxp wceq expeq1i_0 fxpeq1i_0 fxpeq1i_1 fxpeq1i_2 xpeq1 ax-mp $.
$}
$( Equality inference for cross product.  (Contributed by NM,
       21-Dec-2008.) $)
${
	fxpeq2i_0 $f class A $.
	fxpeq2i_1 $f class B $.
	fxpeq2i_2 $f class C $.
	expeq2i_0 $e |- A = B $.
	xpeq2i $p |- ( C X. A ) = ( C X. B ) $= fxpeq2i_0 fxpeq2i_1 wceq fxpeq2i_2 fxpeq2i_0 cxp fxpeq2i_2 fxpeq2i_1 cxp wceq expeq2i_0 fxpeq2i_0 fxpeq2i_1 fxpeq2i_2 xpeq2 ax-mp $.
$}
$( Equality inference for cross product.  (Contributed by FL,
       31-Aug-2009.) $)
${
	fxpeq12i_0 $f class A $.
	fxpeq12i_1 $f class B $.
	fxpeq12i_2 $f class C $.
	fxpeq12i_3 $f class D $.
	expeq12i_0 $e |- A = B $.
	expeq12i_1 $e |- C = D $.
	xpeq12i $p |- ( A X. C ) = ( B X. D ) $= fxpeq12i_0 fxpeq12i_1 wceq fxpeq12i_2 fxpeq12i_3 wceq fxpeq12i_0 fxpeq12i_2 cxp fxpeq12i_1 fxpeq12i_3 cxp wceq expeq12i_0 expeq12i_1 fxpeq12i_0 fxpeq12i_1 fxpeq12i_2 fxpeq12i_3 xpeq12 mp2an $.
$}
$( Equality deduction for cross product.  (Contributed by Jeff Madsen,
       17-Jun-2010.) $)
${
	fxpeq1d_0 $f wff ph $.
	fxpeq1d_1 $f class A $.
	fxpeq1d_2 $f class B $.
	fxpeq1d_3 $f class C $.
	expeq1d_0 $e |- ( ph -> A = B ) $.
	xpeq1d $p |- ( ph -> ( A X. C ) = ( B X. C ) ) $= fxpeq1d_0 fxpeq1d_1 fxpeq1d_2 wceq fxpeq1d_1 fxpeq1d_3 cxp fxpeq1d_2 fxpeq1d_3 cxp wceq expeq1d_0 fxpeq1d_1 fxpeq1d_2 fxpeq1d_3 xpeq1 syl $.
$}
$( Equality deduction for cross product.  (Contributed by Jeff Madsen,
       17-Jun-2010.) $)
${
	fxpeq2d_0 $f wff ph $.
	fxpeq2d_1 $f class A $.
	fxpeq2d_2 $f class B $.
	fxpeq2d_3 $f class C $.
	expeq2d_0 $e |- ( ph -> A = B ) $.
	xpeq2d $p |- ( ph -> ( C X. A ) = ( C X. B ) ) $= fxpeq2d_0 fxpeq2d_1 fxpeq2d_2 wceq fxpeq2d_3 fxpeq2d_1 cxp fxpeq2d_3 fxpeq2d_2 cxp wceq expeq2d_0 fxpeq2d_1 fxpeq2d_2 fxpeq2d_3 xpeq2 syl $.
$}
$( Equality deduction for cross product.  (Contributed by NM,
       8-Dec-2013.) $)
${
	fxpeq12d_0 $f wff ph $.
	fxpeq12d_1 $f class A $.
	fxpeq12d_2 $f class B $.
	fxpeq12d_3 $f class C $.
	fxpeq12d_4 $f class D $.
	expeq12d_0 $e |- ( ph -> A = B ) $.
	expeq12d_1 $e |- ( ph -> C = D ) $.
	xpeq12d $p |- ( ph -> ( A X. C ) = ( B X. D ) ) $= fxpeq12d_0 fxpeq12d_1 fxpeq12d_2 wceq fxpeq12d_3 fxpeq12d_4 wceq fxpeq12d_1 fxpeq12d_3 cxp fxpeq12d_2 fxpeq12d_4 cxp wceq expeq12d_0 expeq12d_1 fxpeq12d_1 fxpeq12d_2 fxpeq12d_3 fxpeq12d_4 xpeq12 syl2anc $.
$}
$( Bound-variable hypothesis builder for cross product.  (Contributed by
       NM, 15-Sep-2003.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$d y z A $.
	$d y z B $.
	$d x y z $.
	infxp_0 $f set y $.
	infxp_1 $f set z $.
	fnfxp_0 $f set x $.
	fnfxp_1 $f class A $.
	fnfxp_2 $f class B $.
	enfxp_0 $e |- F/_ x A $.
	enfxp_1 $e |- F/_ x B $.
	nfxp $p |- F/_ x ( A X. B ) $= fnfxp_0 fnfxp_1 fnfxp_2 cxp infxp_0 sup_set_class fnfxp_1 wcel infxp_1 sup_set_class fnfxp_2 wcel wa infxp_0 infxp_1 copab infxp_0 infxp_1 fnfxp_1 fnfxp_2 df-xp infxp_0 sup_set_class fnfxp_1 wcel infxp_1 sup_set_class fnfxp_2 wcel wa infxp_0 infxp_1 fnfxp_0 infxp_0 sup_set_class fnfxp_1 wcel infxp_1 sup_set_class fnfxp_2 wcel fnfxp_0 fnfxp_0 infxp_0 fnfxp_1 enfxp_0 nfcri fnfxp_0 infxp_1 fnfxp_2 enfxp_1 nfcri nfan nfopab nfcxfr $.
$}
$( Distribute proper substitution through the cross product of two
       classes.  (Contributed by Alan Sare, 10-Nov-2012.) $)
${
	$d A w y z $.
	$d B w y z $.
	$d C w y z $.
	$d D w y z $.
	$d w x y z $.
	icsbxpg_0 $f set y $.
	icsbxpg_1 $f set z $.
	icsbxpg_2 $f set w $.
	fcsbxpg_0 $f set x $.
	fcsbxpg_1 $f class A $.
	fcsbxpg_2 $f class B $.
	fcsbxpg_3 $f class C $.
	fcsbxpg_4 $f class D $.
	csbxpg $p |- ( A e. D -> [_ A / x ]_ ( B X. C ) = ( [_ A / x ]_ B X. [_ A / x ]_ C ) ) $= fcsbxpg_1 fcsbxpg_4 wcel fcsbxpg_0 fcsbxpg_1 icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab csb icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 fcsbxpg_3 cxp csb fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb cxp fcsbxpg_1 fcsbxpg_4 wcel fcsbxpg_0 fcsbxpg_1 icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab csb icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 cab icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex fcsbxpg_0 icsbxpg_1 fcsbxpg_1 fcsbxpg_4 csbabg fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_2 wex icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 fcsbxpg_0 fcsbxpg_1 fcsbxpg_4 sbcexg fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_2 fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_0 wex icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 fcsbxpg_0 fcsbxpg_1 fcsbxpg_4 sbcexg fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa fcsbxpg_0 fcsbxpg_1 wsbc wa icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa fcsbxpg_0 fcsbxpg_1 fcsbxpg_4 sbcang fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq fcsbxpg_0 fcsbxpg_1 fcsbxpg_4 sbcg fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_2 sup_set_class fcsbxpg_2 wcel fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_0 sup_set_class fcsbxpg_3 wcel fcsbxpg_0 fcsbxpg_1 wsbc wa icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel fcsbxpg_0 fcsbxpg_1 fcsbxpg_4 sbcang fcsbxpg_1 fcsbxpg_4 wcel icsbxpg_2 sup_set_class fcsbxpg_2 wcel fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel fcsbxpg_0 fcsbxpg_1 wsbc icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel fcsbxpg_0 fcsbxpg_1 icsbxpg_2 sup_set_class fcsbxpg_2 fcsbxpg_4 sbcel2g fcsbxpg_0 fcsbxpg_1 icsbxpg_0 sup_set_class fcsbxpg_3 fcsbxpg_4 sbcel2g anbi12d bitrd anbi12d bitrd exbidv bitrd exbidv bitrd abbidv eqtrd fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 fcsbxpg_3 cxp icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab fcsbxpg_2 fcsbxpg_3 cxp icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa icsbxpg_2 icsbxpg_0 copab icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab icsbxpg_2 icsbxpg_0 fcsbxpg_2 fcsbxpg_3 df-xp icsbxpg_2 sup_set_class fcsbxpg_2 wcel icsbxpg_0 sup_set_class fcsbxpg_3 wcel wa icsbxpg_2 icsbxpg_0 icsbxpg_1 df-opab eqtri csbeq2i fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb cxp icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa icsbxpg_2 icsbxpg_0 copab icsbxpg_1 sup_set_class icsbxpg_2 sup_set_class icsbxpg_0 sup_set_class cop wceq icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa wa icsbxpg_0 wex icsbxpg_2 wex icsbxpg_1 cab icsbxpg_2 icsbxpg_0 fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb df-xp icsbxpg_2 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_2 csb wcel icsbxpg_0 sup_set_class fcsbxpg_0 fcsbxpg_1 fcsbxpg_3 csb wcel wa icsbxpg_2 icsbxpg_0 icsbxpg_1 df-opab eqtri 3eqtr4g $.
$}
$( The empty set is not a member of a cross product.  (Contributed by NM,
       2-May-1996.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	i0nelxp_0 $f set x $.
	i0nelxp_1 $f set y $.
	f0nelxp_0 $f class A $.
	f0nelxp_1 $f class B $.
	0nelxp $p |- -. (/) e. ( A X. B ) $= c0 f0nelxp_0 f0nelxp_1 cxp wcel c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa wa i0nelxp_1 wex i0nelxp_0 wex c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa wa i0nelxp_1 wex i0nelxp_0 c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa wa i0nelxp_1 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop c0 wne c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa wa wn i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class i0nelxp_0 vex i0nelxp_1 vex opnzi c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa wa i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop c0 c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa wa c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop c0 i0nelxp_0 sup_set_class i0nelxp_1 sup_set_class cop wceq i0nelxp_0 sup_set_class f0nelxp_0 wcel i0nelxp_1 sup_set_class f0nelxp_1 wcel wa simpl eqcomd necon3ai ax-mp nex nex i0nelxp_0 i0nelxp_1 c0 f0nelxp_0 f0nelxp_1 elxp mtbir $.
$}
$( A member of a cross product (ordered pair) doesn't contain the empty
       set.  (Contributed by NM, 15-Dec-2008.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	i0nelelxp_0 $f set x $.
	i0nelelxp_1 $f set y $.
	f0nelelxp_0 $f class A $.
	f0nelelxp_1 $f class B $.
	f0nelelxp_2 $f class C $.
	0nelelxp $p |- ( C e. ( A X. B ) -> -. (/) e. C ) $= f0nelelxp_2 f0nelelxp_0 f0nelelxp_1 cxp wcel f0nelelxp_2 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop wceq i0nelelxp_0 sup_set_class f0nelelxp_0 wcel i0nelelxp_1 sup_set_class f0nelelxp_1 wcel wa wa i0nelelxp_1 wex i0nelelxp_0 wex c0 f0nelelxp_2 wcel wn i0nelelxp_0 i0nelelxp_1 f0nelelxp_2 f0nelelxp_0 f0nelelxp_1 elxp f0nelelxp_2 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop wceq i0nelelxp_0 sup_set_class f0nelelxp_0 wcel i0nelelxp_1 sup_set_class f0nelelxp_1 wcel wa wa c0 f0nelelxp_2 wcel wn i0nelelxp_0 i0nelelxp_1 f0nelelxp_2 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop wceq i0nelelxp_0 sup_set_class f0nelelxp_0 wcel i0nelelxp_1 sup_set_class f0nelelxp_1 wcel wa wa c0 f0nelelxp_2 wcel c0 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop wcel i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class 0nelop f0nelelxp_2 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop wceq i0nelelxp_0 sup_set_class f0nelelxp_0 wcel i0nelelxp_1 sup_set_class f0nelelxp_1 wcel wa wa f0nelelxp_2 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop c0 f0nelelxp_2 i0nelelxp_0 sup_set_class i0nelelxp_1 sup_set_class cop wceq i0nelelxp_0 sup_set_class f0nelelxp_0 wcel i0nelelxp_1 sup_set_class f0nelelxp_1 wcel wa simpl eleq2d mtbiri exlimivv sylbi $.
$}
$( Ordered pair membership in a cross product.  (Contributed by NM,
       15-Nov-1994.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)
       (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	iopelxp_0 $f set x $.
	iopelxp_1 $f set y $.
	fopelxp_0 $f class A $.
	fopelxp_1 $f class B $.
	fopelxp_2 $f class C $.
	fopelxp_3 $f class D $.
	opelxp $p |- ( <. A , B >. e. ( C X. D ) <-> ( A e. C /\ B e. D ) ) $= fopelxp_0 fopelxp_1 cop fopelxp_2 fopelxp_3 cxp wcel fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq iopelxp_1 fopelxp_3 wrex iopelxp_0 fopelxp_2 wrex fopelxp_0 fopelxp_2 wcel fopelxp_1 fopelxp_3 wcel wa iopelxp_0 iopelxp_1 fopelxp_0 fopelxp_1 cop fopelxp_2 fopelxp_3 elxp2 fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq iopelxp_1 fopelxp_3 wrex iopelxp_0 fopelxp_2 wrex fopelxp_0 fopelxp_2 wcel fopelxp_1 fopelxp_3 wcel wa fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq fopelxp_0 fopelxp_2 wcel fopelxp_1 fopelxp_3 wcel wa iopelxp_0 iopelxp_1 fopelxp_2 fopelxp_3 fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq fopelxp_0 fopelxp_2 wcel fopelxp_1 fopelxp_3 wcel wa iopelxp_0 sup_set_class fopelxp_2 wcel iopelxp_1 sup_set_class fopelxp_3 wcel wa fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq fopelxp_0 iopelxp_0 sup_set_class wceq fopelxp_1 iopelxp_1 sup_set_class wceq wa fopelxp_0 fopelxp_2 wcel fopelxp_1 fopelxp_3 wcel wa iopelxp_0 sup_set_class fopelxp_2 wcel iopelxp_1 sup_set_class fopelxp_3 wcel wa wb fopelxp_0 fopelxp_1 iopelxp_0 sup_set_class iopelxp_1 sup_set_class iopelxp_0 vex iopelxp_1 vex opth2 fopelxp_0 iopelxp_0 sup_set_class wceq fopelxp_0 fopelxp_2 wcel iopelxp_0 sup_set_class fopelxp_2 wcel fopelxp_1 iopelxp_1 sup_set_class wceq fopelxp_1 fopelxp_3 wcel iopelxp_1 sup_set_class fopelxp_3 wcel fopelxp_0 iopelxp_0 sup_set_class fopelxp_2 eleq1 fopelxp_1 iopelxp_1 sup_set_class fopelxp_3 eleq1 bi2anan9 sylbi biimprcd rexlimivv fopelxp_0 fopelxp_2 wcel fopelxp_1 fopelxp_3 wcel fopelxp_0 fopelxp_1 cop fopelxp_0 fopelxp_1 cop wceq fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq iopelxp_1 fopelxp_3 wrex iopelxp_0 fopelxp_2 wrex fopelxp_0 fopelxp_1 cop eqid fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop wceq fopelxp_0 fopelxp_1 cop fopelxp_0 fopelxp_1 cop wceq fopelxp_0 fopelxp_1 cop fopelxp_0 iopelxp_1 sup_set_class cop wceq iopelxp_0 iopelxp_1 fopelxp_0 fopelxp_1 fopelxp_2 fopelxp_3 iopelxp_0 sup_set_class fopelxp_0 wceq iopelxp_0 sup_set_class iopelxp_1 sup_set_class cop fopelxp_0 iopelxp_1 sup_set_class cop fopelxp_0 fopelxp_1 cop iopelxp_0 sup_set_class fopelxp_0 iopelxp_1 sup_set_class opeq1 eqeq2d iopelxp_1 sup_set_class fopelxp_1 wceq fopelxp_0 iopelxp_1 sup_set_class cop fopelxp_0 fopelxp_1 cop fopelxp_0 fopelxp_1 cop iopelxp_1 sup_set_class fopelxp_1 fopelxp_0 opeq2 eqeq2d rspc2ev mp3an3 impbii bitri $.
$}
$( Binary relation on a cross product.  (Contributed by NM,
       22-Apr-2004.) $)
${
	fbrxp_0 $f class A $.
	fbrxp_1 $f class B $.
	fbrxp_2 $f class C $.
	fbrxp_3 $f class D $.
	brxp $p |- ( A ( C X. D ) B <-> ( A e. C /\ B e. D ) ) $= fbrxp_0 fbrxp_1 fbrxp_2 fbrxp_3 cxp wbr fbrxp_0 fbrxp_1 cop fbrxp_2 fbrxp_3 cxp wcel fbrxp_0 fbrxp_2 wcel fbrxp_1 fbrxp_3 wcel wa fbrxp_0 fbrxp_1 fbrxp_2 fbrxp_3 cxp df-br fbrxp_0 fbrxp_1 fbrxp_2 fbrxp_3 opelxp bitri $.
$}
$( Ordered pair membership in a cross product (implication).  (Contributed by
     NM, 28-May-1995.) $)
${
	fopelxpi_0 $f class A $.
	fopelxpi_1 $f class B $.
	fopelxpi_2 $f class C $.
	fopelxpi_3 $f class D $.
	opelxpi $p |- ( ( A e. C /\ B e. D ) -> <. A , B >. e. ( C X. D ) ) $= fopelxpi_0 fopelxpi_1 cop fopelxpi_2 fopelxpi_3 cxp wcel fopelxpi_0 fopelxpi_2 wcel fopelxpi_1 fopelxpi_3 wcel wa fopelxpi_0 fopelxpi_1 fopelxpi_2 fopelxpi_3 opelxp biimpri $.
$}
$( The first member of an ordered pair of classes in a cross product belongs
     to first cross product argument.  (Contributed by NM, 28-May-2008.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	fopelxp1_0 $f class A $.
	fopelxp1_1 $f class B $.
	fopelxp1_2 $f class C $.
	fopelxp1_3 $f class D $.
	opelxp1 $p |- ( <. A , B >. e. ( C X. D ) -> A e. C ) $= fopelxp1_0 fopelxp1_1 cop fopelxp1_2 fopelxp1_3 cxp wcel fopelxp1_0 fopelxp1_2 wcel fopelxp1_1 fopelxp1_3 wcel fopelxp1_0 fopelxp1_1 fopelxp1_2 fopelxp1_3 opelxp simplbi $.
$}
$( The second member of an ordered pair of classes in a cross product belongs
     to second cross product argument.  (Contributed by Mario Carneiro,
     26-Apr-2015.) $)
${
	fopelxp2_0 $f class A $.
	fopelxp2_1 $f class B $.
	fopelxp2_2 $f class C $.
	fopelxp2_3 $f class D $.
	opelxp2 $p |- ( <. A , B >. e. ( C X. D ) -> B e. D ) $= fopelxp2_0 fopelxp2_1 cop fopelxp2_2 fopelxp2_3 cxp wcel fopelxp2_0 fopelxp2_2 wcel fopelxp2_1 fopelxp2_3 wcel fopelxp2_0 fopelxp2_1 fopelxp2_2 fopelxp2_3 opelxp simprbi $.
$}
$( The first member of an ordered triple of classes in a cross product
     belongs to first cross product argument.  (Contributed by NM,
     28-May-2008.) $)
${
	fotelxp1_0 $f class A $.
	fotelxp1_1 $f class B $.
	fotelxp1_2 $f class C $.
	fotelxp1_3 $f class R $.
	fotelxp1_4 $f class S $.
	fotelxp1_5 $f class T $.
	otelxp1 $p |- ( <. <. A , B >. , C >. e. ( ( R X. S ) X. T ) -> A e. R ) $= fotelxp1_0 fotelxp1_1 cop fotelxp1_2 cop fotelxp1_3 fotelxp1_4 cxp fotelxp1_5 cxp wcel fotelxp1_0 fotelxp1_1 cop fotelxp1_3 fotelxp1_4 cxp wcel fotelxp1_0 fotelxp1_3 wcel fotelxp1_0 fotelxp1_1 cop fotelxp1_2 fotelxp1_3 fotelxp1_4 cxp fotelxp1_5 opelxp1 fotelxp1_0 fotelxp1_1 fotelxp1_3 fotelxp1_4 opelxp1 syl $.
$}
$( Membership in a class builder restricted to a cross product.
       (Contributed by NM, 20-Feb-2014.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d y z ph $.
	$d x ps $.
	frabxp_0 $f wff ph $.
	frabxp_1 $f wff ps $.
	frabxp_2 $f set x $.
	frabxp_3 $f set y $.
	frabxp_4 $f set z $.
	frabxp_5 $f class A $.
	frabxp_6 $f class B $.
	erabxp_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	rabxp $p |- { x e. ( A X. B ) | ph } = { <. y , z >. | ( y e. A /\ z e. B /\ ps ) } $= frabxp_2 sup_set_class frabxp_5 frabxp_6 cxp wcel frabxp_0 wa frabxp_2 cab frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a wa frabxp_4 wex frabxp_3 wex frabxp_2 cab frabxp_0 frabxp_2 frabxp_5 frabxp_6 cxp crab frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a frabxp_3 frabxp_4 copab frabxp_2 sup_set_class frabxp_5 frabxp_6 cxp wcel frabxp_0 wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a wa frabxp_4 wex frabxp_3 wex frabxp_2 frabxp_2 sup_set_class frabxp_5 frabxp_6 cxp wcel frabxp_0 wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa wa frabxp_4 wex frabxp_3 wex frabxp_0 wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa wa frabxp_0 wa frabxp_4 wex frabxp_3 wex frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a wa frabxp_4 wex frabxp_3 wex frabxp_2 sup_set_class frabxp_5 frabxp_6 cxp wcel frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa wa frabxp_4 wex frabxp_3 wex frabxp_0 frabxp_3 frabxp_4 frabxp_2 sup_set_class frabxp_5 frabxp_6 elxp anbi1i frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa wa frabxp_0 frabxp_3 frabxp_4 19.41vv frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa wa frabxp_0 wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a wa frabxp_3 frabxp_4 frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa wa frabxp_0 wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa frabxp_0 wa wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a wa frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa frabxp_0 anass frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa frabxp_0 wa frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa frabxp_0 wa frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa frabxp_1 wa frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a frabxp_2 sup_set_class frabxp_3 sup_set_class frabxp_4 sup_set_class cop wceq frabxp_0 frabxp_1 frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel wa erabxp_0 anbi2d frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 df-3an syl6bbr pm5.32i bitri 2exbii 3bitr2i abbii frabxp_0 frabxp_2 frabxp_5 frabxp_6 cxp df-rab frabxp_3 sup_set_class frabxp_5 wcel frabxp_4 sup_set_class frabxp_6 wcel frabxp_1 w3a frabxp_3 frabxp_4 frabxp_2 df-opab 3eqtr4i $.
$}
$( A true binary relation on a relation implies the arguments are sets.
     (This is a property of our ordered pair definition.)  (Contributed by
     Mario Carneiro, 26-Apr-2015.) $)
${
	fbrrelex12_0 $f class A $.
	fbrrelex12_1 $f class B $.
	fbrrelex12_2 $f class R $.
	brrelex12 $p |- ( ( Rel R /\ A R B ) -> ( A e. _V /\ B e. _V ) ) $= fbrrelex12_2 wrel fbrrelex12_0 fbrrelex12_1 fbrrelex12_2 wbr wa fbrrelex12_0 fbrrelex12_1 cvv cvv cxp wbr fbrrelex12_0 cvv wcel fbrrelex12_1 cvv wcel wa fbrrelex12_2 wrel fbrrelex12_0 fbrrelex12_1 fbrrelex12_2 wbr fbrrelex12_0 fbrrelex12_1 cvv cvv cxp wbr fbrrelex12_2 wrel fbrrelex12_2 cvv cvv cxp fbrrelex12_0 fbrrelex12_1 fbrrelex12_2 wrel fbrrelex12_2 cvv cvv cxp wss fbrrelex12_2 df-rel biimpi ssbrd imp fbrrelex12_0 fbrrelex12_1 cvv cvv brxp sylib $.
$}
$( A true binary relation on a relation implies the first argument is a set.
     (This is a property of our ordered pair definition.)  (Contributed by NM,
     18-May-2004.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	fbrrelex_0 $f class A $.
	fbrrelex_1 $f class B $.
	fbrrelex_2 $f class R $.
	brrelex $p |- ( ( Rel R /\ A R B ) -> A e. _V ) $= fbrrelex_2 wrel fbrrelex_0 fbrrelex_1 fbrrelex_2 wbr wa fbrrelex_0 cvv wcel fbrrelex_1 cvv wcel fbrrelex_0 fbrrelex_1 fbrrelex_2 brrelex12 simpld $.
$}
$( A true binary relation on a relation implies the second argument is a
     set.  (This is a property of our ordered pair definition.)  (Contributed
     by Mario Carneiro, 26-Apr-2015.) $)
${
	fbrrelex2_0 $f class A $.
	fbrrelex2_1 $f class B $.
	fbrrelex2_2 $f class R $.
	brrelex2 $p |- ( ( Rel R /\ A R B ) -> B e. _V ) $= fbrrelex2_2 wrel fbrrelex2_0 fbrrelex2_1 fbrrelex2_2 wbr wa fbrrelex2_0 cvv wcel fbrrelex2_1 cvv wcel fbrrelex2_0 fbrrelex2_1 fbrrelex2_2 brrelex12 simprd $.
$}
$( The first argument of a binary relation exists.  (An artifact of our
       ordered pair definition.)  (Contributed by NM, 4-Jun-1998.) $)
${
	fbrrelexi_0 $f class A $.
	fbrrelexi_1 $f class B $.
	fbrrelexi_2 $f class R $.
	ebrrelexi_0 $e |- Rel R $.
	brrelexi $p |- ( A R B -> A e. _V ) $= fbrrelexi_2 wrel fbrrelexi_0 fbrrelexi_1 fbrrelexi_2 wbr fbrrelexi_0 cvv wcel ebrrelexi_0 fbrrelexi_0 fbrrelexi_1 fbrrelexi_2 brrelex mpan $.
$}
$( The second argument of a binary relation exists.  (An artifact of our
       ordered pair definition.)  (Contributed by Mario Carneiro,
       26-Apr-2015.) $)
${
	fbrrelex2i_0 $f class A $.
	fbrrelex2i_1 $f class B $.
	fbrrelex2i_2 $f class R $.
	ebrrelex2i_0 $e |- Rel R $.
	brrelex2i $p |- ( A R B -> B e. _V ) $= fbrrelex2i_2 wrel fbrrelex2i_0 fbrrelex2i_1 fbrrelex2i_2 wbr fbrrelex2i_1 cvv wcel ebrrelex2i_0 fbrrelex2i_0 fbrrelex2i_1 fbrrelex2i_2 brrelex2 mpan $.
$}
$( No proper class is related to anything via any relation.  (Contributed
       by Roy F. Longton, 30-Jul-2005.) $)
${
	fnprrel_0 $f class A $.
	fnprrel_1 $f class B $.
	fnprrel_2 $f class R $.
	enprrel_0 $e |- Rel R $.
	enprrel_1 $e |- -. A e. _V $.
	nprrel $p |- -. A R B $= fnprrel_0 fnprrel_1 fnprrel_2 wbr fnprrel_0 cvv wcel enprrel_1 fnprrel_0 fnprrel_1 fnprrel_2 enprrel_0 brrelexi mto $.
$}
$( Representation of a constant function using the mapping operation.
       (Note that ` x ` cannot appear free in ` B ` .)  (Contributed by NM,
       12-Oct-1999.)  (Revised by Mario Carneiro, 16-Nov-2013.) $)
${
	$d x y A $.
	$d x y B $.
	ifconstmpt_0 $f set y $.
	ffconstmpt_0 $f set x $.
	ffconstmpt_1 $f class A $.
	ffconstmpt_2 $f class B $.
	fconstmpt $p |- ( A X. { B } ) = ( x e. A |-> B ) $= ffconstmpt_0 sup_set_class ffconstmpt_1 wcel ifconstmpt_0 sup_set_class ffconstmpt_2 csn wcel wa ffconstmpt_0 ifconstmpt_0 copab ffconstmpt_0 sup_set_class ffconstmpt_1 wcel ifconstmpt_0 sup_set_class ffconstmpt_2 wceq wa ffconstmpt_0 ifconstmpt_0 copab ffconstmpt_1 ffconstmpt_2 csn cxp ffconstmpt_0 ffconstmpt_1 ffconstmpt_2 cmpt ffconstmpt_0 sup_set_class ffconstmpt_1 wcel ifconstmpt_0 sup_set_class ffconstmpt_2 csn wcel wa ffconstmpt_0 sup_set_class ffconstmpt_1 wcel ifconstmpt_0 sup_set_class ffconstmpt_2 wceq wa ffconstmpt_0 ifconstmpt_0 ifconstmpt_0 sup_set_class ffconstmpt_2 csn wcel ifconstmpt_0 sup_set_class ffconstmpt_2 wceq ffconstmpt_0 sup_set_class ffconstmpt_1 wcel ifconstmpt_0 ffconstmpt_2 elsn anbi2i opabbii ffconstmpt_0 ifconstmpt_0 ffconstmpt_1 ffconstmpt_2 csn df-xp ffconstmpt_0 ifconstmpt_0 ffconstmpt_1 ffconstmpt_2 df-mpt 3eqtr4i $.
$}
$( Variable to class conversion of transitive relation.  (Contributed by
       NM, 9-Jun-1998.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	$d x y A $.
	$d y B $.
	$d x y z C $.
	$d x y z R $.
	fvtoclr_0 $f set x $.
	fvtoclr_1 $f set y $.
	fvtoclr_2 $f set z $.
	fvtoclr_3 $f class A $.
	fvtoclr_4 $f class B $.
	fvtoclr_5 $f class C $.
	fvtoclr_6 $f class R $.
	evtoclr_0 $e |- Rel R $.
	evtoclr_1 $e |- ( ( x R y /\ y R z ) -> x R z ) $.
	vtoclr $p |- ( ( A R B /\ B R C ) -> A R C ) $= fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_3 cvv wcel fvtoclr_4 cvv wcel wa fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr fvtoclr_5 cvv wcel fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_3 cvv wcel fvtoclr_4 cvv wcel fvtoclr_3 fvtoclr_4 fvtoclr_6 evtoclr_0 brrelexi fvtoclr_3 fvtoclr_4 fvtoclr_6 evtoclr_0 brrelex2i jca fvtoclr_4 fvtoclr_5 fvtoclr_6 evtoclr_0 brrelex2i fvtoclr_5 cvv wcel fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_5 fvtoclr_6 wbr wi wi fvtoclr_5 cvv wcel fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi wi fvtoclr_5 cvv wcel fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi wi fvtoclr_0 fvtoclr_1 fvtoclr_3 fvtoclr_4 cvv cvv fvtoclr_0 sup_set_class fvtoclr_3 wceq fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_5 cvv wcel fvtoclr_0 sup_set_class fvtoclr_3 wceq fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_5 fvtoclr_6 wbr fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr fvtoclr_0 sup_set_class fvtoclr_3 wceq fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr fvtoclr_0 sup_set_class fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 breq1 anbi1d fvtoclr_0 sup_set_class fvtoclr_3 fvtoclr_5 fvtoclr_6 breq1 imbi12d imbi2d fvtoclr_1 sup_set_class fvtoclr_4 wceq fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_5 cvv wcel fvtoclr_1 sup_set_class fvtoclr_4 wceq fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_3 fvtoclr_5 fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_4 wceq fvtoclr_3 fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_3 fvtoclr_4 fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr fvtoclr_4 fvtoclr_5 fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_4 fvtoclr_3 fvtoclr_6 breq2 fvtoclr_1 sup_set_class fvtoclr_4 fvtoclr_5 fvtoclr_6 breq1 anbi12d imbi1d imbi2d fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_2 sup_set_class fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_2 sup_set_class fvtoclr_6 wbr wi fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_5 fvtoclr_6 wbr wi fvtoclr_2 fvtoclr_5 cvv fvtoclr_2 sup_set_class fvtoclr_5 wceq fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_2 sup_set_class fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr wa fvtoclr_0 sup_set_class fvtoclr_2 sup_set_class fvtoclr_6 wbr fvtoclr_0 sup_set_class fvtoclr_5 fvtoclr_6 wbr fvtoclr_2 sup_set_class fvtoclr_5 wceq fvtoclr_1 sup_set_class fvtoclr_2 sup_set_class fvtoclr_6 wbr fvtoclr_1 sup_set_class fvtoclr_5 fvtoclr_6 wbr fvtoclr_0 sup_set_class fvtoclr_1 sup_set_class fvtoclr_6 wbr fvtoclr_2 sup_set_class fvtoclr_5 fvtoclr_1 sup_set_class fvtoclr_6 breq2 anbi2d fvtoclr_2 sup_set_class fvtoclr_5 fvtoclr_0 sup_set_class fvtoclr_6 breq2 imbi12d evtoclr_1 vtoclg vtocl2g syl2im imp pm2.43i $.
$}
$( Ordered pair membership in the universal class of ordered pairs.
     (Contributed by Mario Carneiro, 3-May-2015.) $)
${
	fopelvvg_0 $f class A $.
	fopelvvg_1 $f class B $.
	fopelvvg_2 $f class V $.
	fopelvvg_3 $f class W $.
	opelvvg $p |- ( ( A e. V /\ B e. W ) -> <. A , B >. e. ( _V X. _V ) ) $= fopelvvg_0 fopelvvg_2 wcel fopelvvg_0 cvv wcel fopelvvg_1 cvv wcel fopelvvg_0 fopelvvg_1 cop cvv cvv cxp wcel fopelvvg_1 fopelvvg_3 wcel fopelvvg_0 fopelvvg_2 elex fopelvvg_1 fopelvvg_3 elex fopelvvg_0 fopelvvg_1 cvv cvv opelxpi syl2an $.
$}
$( Ordered pair membership in the universal class of ordered pairs.
       (Contributed by NM, 22-Aug-2013.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	fopelvv_0 $f class A $.
	fopelvv_1 $f class B $.
	eopelvv_0 $e |- A e. _V $.
	eopelvv_1 $e |- B e. _V $.
	opelvv $p |- <. A , B >. e. ( _V X. _V ) $= fopelvv_0 cvv wcel fopelvv_1 cvv wcel fopelvv_0 fopelvv_1 cop cvv cvv cxp wcel eopelvv_0 eopelvv_1 fopelvv_0 fopelvv_1 cvv cvv opelxpi mp2an $.
$}
$( Justification theorem for an ordered pair definition that works for any
       classes, including proper classes.  This is a possible definition
       implied by the footnote in [Jech] p. 78, which says, "The sophisticated
       reader will not object to our use of a pair of classes."  (Contributed
       by NM, 28-Sep-2003.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	iopthprc_0 $f set x $.
	fopthprc_0 $f class A $.
	fopthprc_1 $f class B $.
	fopthprc_2 $f class C $.
	fopthprc_3 $f class D $.
	opthprc $p |- ( ( ( A X. { (/) } ) u. ( B X. { { (/) } } ) ) = ( ( C X. { (/) } ) u. ( D X. { { (/) } } ) ) <-> ( A = C /\ B = D ) ) $= fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq fopthprc_0 fopthprc_2 wceq fopthprc_1 fopthprc_3 wceq wa fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq fopthprc_0 fopthprc_2 wceq fopthprc_1 fopthprc_3 wceq fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq iopthprc_0 fopthprc_0 fopthprc_2 fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq iopthprc_0 sup_set_class c0 cop fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class c0 cop fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class fopthprc_0 wcel iopthprc_0 sup_set_class fopthprc_2 wcel fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun iopthprc_0 sup_set_class c0 cop eleq2 iopthprc_0 sup_set_class c0 cop fopthprc_0 c0 csn cxp wcel iopthprc_0 sup_set_class c0 cop fopthprc_1 c0 csn csn cxp wcel wo iopthprc_0 sup_set_class fopthprc_0 wcel c0 c0 csn csn wcel wo iopthprc_0 sup_set_class c0 cop fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class fopthprc_0 wcel iopthprc_0 sup_set_class c0 cop fopthprc_0 c0 csn cxp wcel iopthprc_0 sup_set_class fopthprc_0 wcel iopthprc_0 sup_set_class c0 cop fopthprc_1 c0 csn csn cxp wcel c0 c0 csn csn wcel iopthprc_0 sup_set_class c0 cop fopthprc_0 c0 csn cxp wcel iopthprc_0 sup_set_class fopthprc_0 wcel c0 c0 csn wcel c0 0ex snid iopthprc_0 sup_set_class c0 fopthprc_0 c0 csn opelxp mpbiran2 iopthprc_0 sup_set_class c0 cop fopthprc_1 c0 csn csn cxp wcel iopthprc_0 sup_set_class fopthprc_1 wcel c0 c0 csn csn wcel wa c0 c0 csn csn wcel iopthprc_0 sup_set_class c0 fopthprc_1 c0 csn csn opelxp c0 c0 csn csn wcel iopthprc_0 sup_set_class fopthprc_1 wcel c0 c0 csn csn wcel c0 c0 csn 0nep0 c0 c0 csn 0ex elsnc nemtbir bianfi bitr4i orbi12i iopthprc_0 sup_set_class c0 cop fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp elun c0 c0 csn csn wcel iopthprc_0 sup_set_class fopthprc_0 wcel c0 c0 csn csn wcel c0 c0 csn 0nep0 c0 c0 csn 0ex elsnc nemtbir biorfi 3bitr4ri iopthprc_0 sup_set_class c0 cop fopthprc_2 c0 csn cxp wcel iopthprc_0 sup_set_class c0 cop fopthprc_3 c0 csn csn cxp wcel wo iopthprc_0 sup_set_class fopthprc_2 wcel c0 c0 csn csn wcel wo iopthprc_0 sup_set_class c0 cop fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class fopthprc_2 wcel iopthprc_0 sup_set_class c0 cop fopthprc_2 c0 csn cxp wcel iopthprc_0 sup_set_class fopthprc_2 wcel iopthprc_0 sup_set_class c0 cop fopthprc_3 c0 csn csn cxp wcel c0 c0 csn csn wcel iopthprc_0 sup_set_class c0 cop fopthprc_2 c0 csn cxp wcel iopthprc_0 sup_set_class fopthprc_2 wcel c0 c0 csn wcel c0 0ex snid iopthprc_0 sup_set_class c0 fopthprc_2 c0 csn opelxp mpbiran2 iopthprc_0 sup_set_class c0 cop fopthprc_3 c0 csn csn cxp wcel iopthprc_0 sup_set_class fopthprc_3 wcel c0 c0 csn csn wcel wa c0 c0 csn csn wcel iopthprc_0 sup_set_class c0 fopthprc_3 c0 csn csn opelxp c0 c0 csn csn wcel iopthprc_0 sup_set_class fopthprc_3 wcel c0 c0 csn csn wcel c0 c0 csn 0nep0 c0 c0 csn 0ex elsnc nemtbir bianfi bitr4i orbi12i iopthprc_0 sup_set_class c0 cop fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp elun c0 c0 csn csn wcel iopthprc_0 sup_set_class fopthprc_2 wcel c0 c0 csn csn wcel c0 c0 csn 0nep0 c0 c0 csn 0ex elsnc nemtbir biorfi 3bitr4ri 3bitr4g eqrdv fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq iopthprc_0 fopthprc_1 fopthprc_3 fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq iopthprc_0 sup_set_class c0 csn cop fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class fopthprc_1 wcel iopthprc_0 sup_set_class fopthprc_3 wcel fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun iopthprc_0 sup_set_class c0 csn cop eleq2 iopthprc_0 sup_set_class c0 csn cop fopthprc_0 c0 csn cxp wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_1 c0 csn csn cxp wcel wo c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_1 wcel wo iopthprc_0 sup_set_class c0 csn cop fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class fopthprc_1 wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_0 c0 csn cxp wcel c0 csn c0 csn wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_1 c0 csn csn cxp wcel iopthprc_0 sup_set_class fopthprc_1 wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_0 c0 csn cxp wcel iopthprc_0 sup_set_class fopthprc_0 wcel c0 csn c0 csn wcel wa c0 csn c0 csn wcel iopthprc_0 sup_set_class c0 csn fopthprc_0 c0 csn opelxp c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_0 wcel c0 csn c0 csn wcel c0 c0 csn 0nep0 c0 csn c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0 csn c0 eqcom bitri nemtbir bianfi bitr4i iopthprc_0 sup_set_class c0 csn cop fopthprc_1 c0 csn csn cxp wcel iopthprc_0 sup_set_class fopthprc_1 wcel c0 csn c0 csn csn wcel c0 csn p0ex snid iopthprc_0 sup_set_class c0 csn fopthprc_1 c0 csn csn opelxp mpbiran2 orbi12i iopthprc_0 sup_set_class c0 csn cop fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp elun c0 csn c0 csn wcel wn iopthprc_0 sup_set_class fopthprc_1 wcel c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_1 wcel wo wb c0 csn c0 csn wcel c0 c0 csn 0nep0 c0 csn c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0 csn c0 eqcom bitri nemtbir c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_1 wcel biorf ax-mp 3bitr4ri iopthprc_0 sup_set_class c0 csn cop fopthprc_2 c0 csn cxp wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_3 c0 csn csn cxp wcel wo c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_3 wcel wo iopthprc_0 sup_set_class c0 csn cop fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wcel iopthprc_0 sup_set_class fopthprc_3 wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_2 c0 csn cxp wcel c0 csn c0 csn wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_3 c0 csn csn cxp wcel iopthprc_0 sup_set_class fopthprc_3 wcel iopthprc_0 sup_set_class c0 csn cop fopthprc_2 c0 csn cxp wcel iopthprc_0 sup_set_class fopthprc_2 wcel c0 csn c0 csn wcel wa c0 csn c0 csn wcel iopthprc_0 sup_set_class c0 csn fopthprc_2 c0 csn opelxp c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_2 wcel c0 csn c0 csn wcel c0 c0 csn 0nep0 c0 csn c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0 csn c0 eqcom bitri nemtbir bianfi bitr4i iopthprc_0 sup_set_class c0 csn cop fopthprc_3 c0 csn csn cxp wcel iopthprc_0 sup_set_class fopthprc_3 wcel c0 csn c0 csn csn wcel c0 csn p0ex snid iopthprc_0 sup_set_class c0 csn fopthprc_3 c0 csn csn opelxp mpbiran2 orbi12i iopthprc_0 sup_set_class c0 csn cop fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp elun c0 csn c0 csn wcel wn iopthprc_0 sup_set_class fopthprc_3 wcel c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_3 wcel wo wb c0 csn c0 csn wcel c0 c0 csn 0nep0 c0 csn c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0 csn c0 eqcom bitri nemtbir c0 csn c0 csn wcel iopthprc_0 sup_set_class fopthprc_3 wcel biorf ax-mp 3bitr4ri 3bitr4g eqrdv jca fopthprc_0 fopthprc_2 wceq fopthprc_0 c0 csn cxp fopthprc_2 c0 csn cxp wceq fopthprc_1 c0 csn csn cxp fopthprc_3 c0 csn csn cxp wceq fopthprc_0 c0 csn cxp fopthprc_1 c0 csn csn cxp cun fopthprc_2 c0 csn cxp fopthprc_3 c0 csn csn cxp cun wceq fopthprc_1 fopthprc_3 wceq fopthprc_0 fopthprc_2 c0 csn xpeq1 fopthprc_1 fopthprc_3 c0 csn csn xpeq1 fopthprc_0 c0 csn cxp fopthprc_2 c0 csn cxp fopthprc_1 c0 csn csn cxp fopthprc_3 c0 csn csn cxp uneq12 syl2an impbii $.
$}
$( Two things in a binary relation belong to the relation's domain.
       (Contributed by NM, 17-May-1996.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	fbrel_0 $f class A $.
	fbrel_1 $f class B $.
	fbrel_2 $f class C $.
	fbrel_3 $f class D $.
	fbrel_4 $f class R $.
	ebrel_0 $e |- R C_ ( C X. D ) $.
	brel $p |- ( A R B -> ( A e. C /\ B e. D ) ) $= fbrel_0 fbrel_1 fbrel_4 wbr fbrel_0 fbrel_1 fbrel_2 fbrel_3 cxp wbr fbrel_0 fbrel_2 wcel fbrel_1 fbrel_3 wcel wa fbrel_4 fbrel_2 fbrel_3 cxp fbrel_0 fbrel_1 ebrel_0 ssbri fbrel_0 fbrel_1 fbrel_2 fbrel_3 brxp sylib $.
$}
$( Ordered pair membership in an ordered pair class abstraction.
       (Contributed by Mario Carneiro, 9-Nov-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y ps $.
	fbrab2a_0 $f wff ph $.
	fbrab2a_1 $f wff ps $.
	fbrab2a_2 $f set x $.
	fbrab2a_3 $f set y $.
	fbrab2a_4 $f class A $.
	fbrab2a_5 $f class B $.
	fbrab2a_6 $f class C $.
	fbrab2a_7 $f class D $.
	fbrab2a_8 $f class R $.
	ebrab2a_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	ebrab2a_1 $e |- R = { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } $.
	brab2a $p |- ( A R B <-> ( ( A e. C /\ B e. D ) /\ ps ) ) $= fbrab2a_4 fbrab2a_5 fbrab2a_8 wbr fbrab2a_4 fbrab2a_6 wcel fbrab2a_5 fbrab2a_7 wcel wa fbrab2a_1 fbrab2a_4 fbrab2a_5 fbrab2a_6 fbrab2a_7 fbrab2a_8 fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_0 wa fbrab2a_2 fbrab2a_3 copab fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_2 fbrab2a_3 copab fbrab2a_8 fbrab2a_6 fbrab2a_7 cxp fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_0 wa fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_2 fbrab2a_3 fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_0 simpl ssopab2i ebrab2a_1 fbrab2a_2 fbrab2a_3 fbrab2a_6 fbrab2a_7 df-xp 3sstr4i brel fbrab2a_4 fbrab2a_5 fbrab2a_8 wbr fbrab2a_4 fbrab2a_5 cop fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_0 wa fbrab2a_2 fbrab2a_3 copab wcel fbrab2a_4 fbrab2a_6 wcel fbrab2a_5 fbrab2a_7 wcel wa fbrab2a_1 fbrab2a_4 fbrab2a_5 fbrab2a_8 wbr fbrab2a_4 fbrab2a_5 cop fbrab2a_8 wcel fbrab2a_4 fbrab2a_5 cop fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_0 wa fbrab2a_2 fbrab2a_3 copab wcel fbrab2a_4 fbrab2a_5 fbrab2a_8 df-br fbrab2a_8 fbrab2a_2 sup_set_class fbrab2a_6 wcel fbrab2a_3 sup_set_class fbrab2a_7 wcel wa fbrab2a_0 wa fbrab2a_2 fbrab2a_3 copab fbrab2a_4 fbrab2a_5 cop ebrab2a_1 eleq2i bitri fbrab2a_0 fbrab2a_1 fbrab2a_2 fbrab2a_3 fbrab2a_4 fbrab2a_5 fbrab2a_6 fbrab2a_7 ebrab2a_0 opelopab2a syl5bb biadan2 $.
$}
$( Membership in a cross product.  (Contributed by NM, 5-Mar-1995.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	felxp3_0 $f set x $.
	felxp3_1 $f set y $.
	felxp3_2 $f class A $.
	felxp3_3 $f class B $.
	felxp3_4 $f class C $.
	elxp3 $p |- ( A e. ( B X. C ) <-> E. x E. y ( <. x , y >. = A /\ <. x , y >. e. ( B X. C ) ) ) $= felxp3_2 felxp3_3 felxp3_4 cxp wcel felxp3_2 felxp3_0 sup_set_class felxp3_1 sup_set_class cop wceq felxp3_0 sup_set_class felxp3_3 wcel felxp3_1 sup_set_class felxp3_4 wcel wa wa felxp3_1 wex felxp3_0 wex felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_2 wceq felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_3 felxp3_4 cxp wcel wa felxp3_1 wex felxp3_0 wex felxp3_0 felxp3_1 felxp3_2 felxp3_3 felxp3_4 elxp felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_2 wceq felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_3 felxp3_4 cxp wcel wa felxp3_2 felxp3_0 sup_set_class felxp3_1 sup_set_class cop wceq felxp3_0 sup_set_class felxp3_3 wcel felxp3_1 sup_set_class felxp3_4 wcel wa wa felxp3_0 felxp3_1 felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_2 wceq felxp3_2 felxp3_0 sup_set_class felxp3_1 sup_set_class cop wceq felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_3 felxp3_4 cxp wcel felxp3_0 sup_set_class felxp3_3 wcel felxp3_1 sup_set_class felxp3_4 wcel wa felxp3_0 sup_set_class felxp3_1 sup_set_class cop felxp3_2 eqcom felxp3_0 sup_set_class felxp3_1 sup_set_class felxp3_3 felxp3_4 opelxp anbi12i 2exbii bitr4i $.
$}
$( Membership in a union of cross products.  (Contributed by Mario
       Carneiro, 29-Dec-2014.)  (Revised by Mario Carneiro, 1-Jan-2017.) $)
${
	$d y z A $.
	$d y z B $.
	$d y z C $.
	$d x y z $.
	iopeliunxp_0 $f set y $.
	iopeliunxp_1 $f set z $.
	fopeliunxp_0 $f set x $.
	fopeliunxp_1 $f class A $.
	fopeliunxp_2 $f class B $.
	fopeliunxp_3 $f class C $.
	opeliunxp $p |- ( <. x , C >. e. U_ x e. A ( { x } X. B ) <-> ( x e. A /\ C e. B ) ) $= fopeliunxp_0 sup_set_class fopeliunxp_3 cop fopeliunxp_0 fopeliunxp_1 fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp ciun wcel fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel fopeliunxp_0 fopeliunxp_1 wrex iopeliunxp_0 cab wcel fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 wex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_3 fopeliunxp_2 wcel wa fopeliunxp_0 fopeliunxp_1 fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp ciun iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel fopeliunxp_0 fopeliunxp_1 wrex iopeliunxp_0 cab fopeliunxp_0 sup_set_class fopeliunxp_3 cop fopeliunxp_0 iopeliunxp_0 fopeliunxp_1 fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp df-iun eleq2i iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel fopeliunxp_0 fopeliunxp_1 wrex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 wex iopeliunxp_0 fopeliunxp_0 sup_set_class fopeliunxp_3 cop fopeliunxp_0 sup_set_class fopeliunxp_3 opex iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel fopeliunxp_0 fopeliunxp_1 wrex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 wex iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class fopeliunxp_3 cop wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 wex iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel fopeliunxp_0 fopeliunxp_1 wrex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel wa fopeliunxp_0 wex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 wex iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel fopeliunxp_0 fopeliunxp_1 df-rex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel wa fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa fopeliunxp_0 iopeliunxp_1 fopeliunxp_0 sup_set_class fopeliunxp_1 wcel iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel wa iopeliunxp_1 nfv fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel fopeliunxp_0 fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 nfs1v fopeliunxp_0 iopeliunxp_0 iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp fopeliunxp_0 iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb fopeliunxp_0 iopeliunxp_1 sup_set_class csn nfcv fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 nfcsb1v nfxp nfcri nfan fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp wcel iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 sbequ12 fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class wceq fopeliunxp_0 sup_set_class csn fopeliunxp_2 cxp iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class wceq fopeliunxp_0 sup_set_class csn iopeliunxp_1 sup_set_class csn fopeliunxp_2 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class sneq fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csbeq1a xpeq12d eleq2d anbi12d cbvex bitri iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class fopeliunxp_3 cop wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class fopeliunxp_3 cop wceq iopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb iopeliunxp_0 sup_set_class fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp eleq1 anbi2d exbidv syl5bb elab fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 wex iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa wa iopeliunxp_1 wex fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_3 fopeliunxp_2 wcel wa fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa wa iopeliunxp_1 fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel wa fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn wcel fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa wa fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn wcel fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa wa iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa wa fopeliunxp_0 sup_set_class fopeliunxp_3 cop iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb cxp wcel fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn wcel fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_3 iopeliunxp_1 sup_set_class csn fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb opelxp anbi2i fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn wcel fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel an12 fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn wcel iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class csn wcel fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class wceq iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 iopeliunxp_1 sup_set_class elsn fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class eqcom bitri anbi1i 3bitri exbii fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel wa fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_3 fopeliunxp_2 wcel wa iopeliunxp_1 fopeliunxp_0 sup_set_class fopeliunxp_0 vex iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_0 iopeliunxp_1 wsb fopeliunxp_0 sup_set_class fopeliunxp_1 wcel fopeliunxp_3 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wcel fopeliunxp_3 fopeliunxp_2 wcel fopeliunxp_0 sup_set_class fopeliunxp_1 wcel iopeliunxp_1 fopeliunxp_0 sbequ12r iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb fopeliunxp_2 fopeliunxp_3 iopeliunxp_1 sup_set_class fopeliunxp_0 sup_set_class wceq fopeliunxp_2 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb fopeliunxp_2 fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csb wceq fopeliunxp_0 sup_set_class iopeliunxp_1 sup_set_class fopeliunxp_0 iopeliunxp_1 sup_set_class fopeliunxp_2 csbeq1a eqcoms eqcomd eleq2d anbi12d ceqsexv bitri 3bitri $.
$}
$( Distributive law for cross product over union.  Theorem 103 of [Suppes]
       p. 52.  (Contributed by NM, 12-Aug-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ixpundi_0 $f set x $.
	ixpundi_1 $f set y $.
	fxpundi_0 $f class A $.
	fxpundi_1 $f class B $.
	fxpundi_2 $f class C $.
	xpundi $p |- ( A X. ( B u. C ) ) = ( ( A X. B ) u. ( A X. C ) ) $= fxpundi_0 fxpundi_1 fxpundi_2 cun cxp ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 cun wcel wa ixpundi_0 ixpundi_1 copab fxpundi_0 fxpundi_1 cxp fxpundi_0 fxpundi_2 cxp cun ixpundi_0 ixpundi_1 fxpundi_0 fxpundi_1 fxpundi_2 cun df-xp fxpundi_0 fxpundi_1 cxp fxpundi_0 fxpundi_2 cxp cun ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 ixpundi_1 copab ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa ixpundi_0 ixpundi_1 copab cun ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 cun wcel wa ixpundi_0 ixpundi_1 copab fxpundi_0 fxpundi_1 cxp ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 ixpundi_1 copab fxpundi_0 fxpundi_2 cxp ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa ixpundi_0 ixpundi_1 copab ixpundi_0 ixpundi_1 fxpundi_0 fxpundi_1 df-xp ixpundi_0 ixpundi_1 fxpundi_0 fxpundi_2 df-xp uneq12i ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 cun wcel wa ixpundi_0 ixpundi_1 copab ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa wo ixpundi_0 ixpundi_1 copab ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 ixpundi_1 copab ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa ixpundi_0 ixpundi_1 copab cun ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 cun wcel wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa wo ixpundi_0 ixpundi_1 ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 cun wcel wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wo wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa wo ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 cun wcel ixpundi_1 sup_set_class fxpundi_1 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wo ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 fxpundi_2 elun anbi2i ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel ixpundi_1 sup_set_class fxpundi_2 wcel andi bitri opabbii ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_1 wcel wa ixpundi_0 sup_set_class fxpundi_0 wcel ixpundi_1 sup_set_class fxpundi_2 wcel wa ixpundi_0 ixpundi_1 unopab eqtr4i eqtr4i eqtr4i $.
$}
$( Distributive law for cross product over union.  Similar to Theorem 103
       of [Suppes] p. 52.  (Contributed by NM, 30-Sep-2002.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ixpundir_0 $f set x $.
	ixpundir_1 $f set y $.
	fxpundir_0 $f class A $.
	fxpundir_1 $f class B $.
	fxpundir_2 $f class C $.
	xpundir $p |- ( ( A u. B ) X. C ) = ( ( A X. C ) u. ( B X. C ) ) $= fxpundir_0 fxpundir_1 cun fxpundir_2 cxp ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 cun wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab fxpundir_0 fxpundir_2 cxp fxpundir_1 fxpundir_2 cxp cun ixpundir_0 ixpundir_1 fxpundir_0 fxpundir_1 cun fxpundir_2 df-xp fxpundir_0 fxpundir_2 cxp fxpundir_1 fxpundir_2 cxp cun ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab cun ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 cun wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab fxpundir_0 fxpundir_2 cxp ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab fxpundir_1 fxpundir_2 cxp ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab ixpundir_0 ixpundir_1 fxpundir_0 fxpundir_2 df-xp ixpundir_0 ixpundir_1 fxpundir_1 fxpundir_2 df-xp uneq12i ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 cun wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa wo ixpundir_0 ixpundir_1 copab ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 copab cun ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 cun wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa wo ixpundir_0 ixpundir_1 ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 cun wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_0 sup_set_class fxpundir_1 wcel wo ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa wo ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 cun wcel ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_0 sup_set_class fxpundir_1 wcel wo ixpundir_1 sup_set_class fxpundir_2 wcel ixpundir_0 sup_set_class fxpundir_0 fxpundir_1 elun anbi1i ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel andir bitri opabbii ixpundir_0 sup_set_class fxpundir_0 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 sup_set_class fxpundir_1 wcel ixpundir_1 sup_set_class fxpundir_2 wcel wa ixpundir_0 ixpundir_1 unopab eqtr4i eqtr4i eqtr4i $.
$}
$( Distributive law for cross product over indexed union.  (Contributed by
       Mario Carneiro, 27-Apr-2014.) $)
${
	$d w y z A $.
	$d w y z B $.
	$d w x y z C $.
	ixpiundi_0 $f set y $.
	ixpiundi_1 $f set z $.
	ixpiundi_2 $f set w $.
	fxpiundi_0 $f set x $.
	fxpiundi_1 $f class A $.
	fxpiundi_2 $f class B $.
	fxpiundi_3 $f class C $.
	xpiundi $p |- ( C X. U_ x e. A B ) = U_ x e. A ( C X. B ) $= ixpiundi_1 fxpiundi_3 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun cxp fxpiundi_0 fxpiundi_1 fxpiundi_3 fxpiundi_2 cxp ciun ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wrex ixpiundi_2 fxpiundi_3 wrex ixpiundi_1 sup_set_class fxpiundi_3 fxpiundi_2 cxp wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class fxpiundi_3 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun cxp wcel ixpiundi_1 sup_set_class fxpiundi_0 fxpiundi_1 fxpiundi_3 fxpiundi_2 cxp ciun wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex fxpiundi_0 fxpiundi_1 wrex ixpiundi_2 fxpiundi_3 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex ixpiundi_2 fxpiundi_3 wrex fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wrex ixpiundi_2 fxpiundi_3 wrex ixpiundi_1 sup_set_class fxpiundi_3 fxpiundi_2 cxp wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex ixpiundi_2 fxpiundi_0 fxpiundi_3 fxpiundi_1 rexcom ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex fxpiundi_0 fxpiundi_1 wrex ixpiundi_2 fxpiundi_3 ixpiundi_0 sup_set_class fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 wex ixpiundi_0 sup_set_class fxpiundi_2 wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 wex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex fxpiundi_0 fxpiundi_1 wrex ixpiundi_0 sup_set_class fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 sup_set_class fxpiundi_2 wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 ixpiundi_0 sup_set_class fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun wcel ixpiundi_0 sup_set_class fxpiundi_2 wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq fxpiundi_0 ixpiundi_0 sup_set_class fxpiundi_1 fxpiundi_2 eliun anbi1i exbii ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun df-rex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex fxpiundi_0 fxpiundi_1 wrex ixpiundi_0 sup_set_class fxpiundi_2 wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 wex fxpiundi_0 fxpiundi_1 wrex ixpiundi_0 sup_set_class fxpiundi_2 wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa fxpiundi_0 fxpiundi_1 wrex ixpiundi_0 wex ixpiundi_0 sup_set_class fxpiundi_2 wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 wex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex ixpiundi_0 sup_set_class fxpiundi_2 wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 wex fxpiundi_0 fxpiundi_1 ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 df-rex rexbii ixpiundi_0 sup_set_class fxpiundi_2 wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa fxpiundi_0 ixpiundi_0 fxpiundi_1 rexcom4 ixpiundi_0 sup_set_class fxpiundi_2 wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa fxpiundi_0 fxpiundi_1 wrex ixpiundi_0 sup_set_class fxpiundi_2 wcel fxpiundi_0 fxpiundi_1 wrex ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq wa ixpiundi_0 ixpiundi_0 sup_set_class fxpiundi_2 wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq fxpiundi_0 fxpiundi_1 r19.41v exbii 3bitri 3bitr4i rexbii ixpiundi_1 sup_set_class fxpiundi_3 fxpiundi_2 cxp wcel ixpiundi_1 sup_set_class ixpiundi_2 sup_set_class ixpiundi_0 sup_set_class cop wceq ixpiundi_0 fxpiundi_2 wrex ixpiundi_2 fxpiundi_3 wrex fxpiundi_0 fxpiundi_1 ixpiundi_2 ixpiundi_0 ixpiundi_1 sup_set_class fxpiundi_3 fxpiundi_2 elxp2 rexbii 3bitr4i ixpiundi_2 ixpiundi_0 ixpiundi_1 sup_set_class fxpiundi_3 fxpiundi_0 fxpiundi_1 fxpiundi_2 ciun elxp2 fxpiundi_0 ixpiundi_1 sup_set_class fxpiundi_1 fxpiundi_3 fxpiundi_2 cxp eliun 3bitr4i eqriv $.
$}
$( Distributive law for cross product over indexed union.  (Contributed by
       Mario Carneiro, 27-Apr-2014.) $)
${
	$d w y z A $.
	$d w y z B $.
	$d w x y z C $.
	ixpiundir_0 $f set y $.
	ixpiundir_1 $f set z $.
	ixpiundir_2 $f set w $.
	fxpiundir_0 $f set x $.
	fxpiundir_1 $f class A $.
	fxpiundir_2 $f class B $.
	fxpiundir_3 $f class C $.
	xpiundir $p |- ( U_ x e. A B X. C ) = U_ x e. A ( B X. C ) $= ixpiundir_1 fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun fxpiundir_3 cxp fxpiundir_0 fxpiundir_1 fxpiundir_2 fxpiundir_3 cxp ciun ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wrex ixpiundir_1 sup_set_class fxpiundir_2 fxpiundir_3 cxp wcel fxpiundir_0 fxpiundir_1 wrex ixpiundir_1 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun fxpiundir_3 cxp wcel ixpiundir_1 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 fxpiundir_3 cxp ciun wcel ixpiundir_0 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 wex ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_2 wrex fxpiundir_0 fxpiundir_1 wrex ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wrex ixpiundir_1 sup_set_class fxpiundir_2 fxpiundir_3 cxp wcel fxpiundir_0 fxpiundir_1 wrex ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 wex fxpiundir_0 fxpiundir_1 wrex ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa fxpiundir_0 fxpiundir_1 wrex ixpiundir_0 wex ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_2 wrex fxpiundir_0 fxpiundir_1 wrex ixpiundir_0 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 wex ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa fxpiundir_0 ixpiundir_0 fxpiundir_1 rexcom4 ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_2 wrex ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 wex fxpiundir_0 fxpiundir_1 ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_2 df-rex rexbii ixpiundir_0 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa fxpiundir_0 fxpiundir_1 wrex ixpiundir_0 ixpiundir_0 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 sup_set_class fxpiundir_2 wcel fxpiundir_0 fxpiundir_1 wrex ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex wa fxpiundir_0 fxpiundir_1 wrex ixpiundir_0 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun wcel ixpiundir_0 sup_set_class fxpiundir_2 wcel fxpiundir_0 fxpiundir_1 wrex ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex fxpiundir_0 ixpiundir_0 sup_set_class fxpiundir_1 fxpiundir_2 eliun anbi1i ixpiundir_0 sup_set_class fxpiundir_2 wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex fxpiundir_0 fxpiundir_1 r19.41v bitr4i exbii 3bitr4ri ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun df-rex ixpiundir_1 sup_set_class fxpiundir_2 fxpiundir_3 cxp wcel ixpiundir_1 sup_set_class ixpiundir_0 sup_set_class ixpiundir_2 sup_set_class cop wceq ixpiundir_2 fxpiundir_3 wrex ixpiundir_0 fxpiundir_2 wrex fxpiundir_0 fxpiundir_1 ixpiundir_0 ixpiundir_2 ixpiundir_1 sup_set_class fxpiundir_2 fxpiundir_3 elxp2 rexbii 3bitr4i ixpiundir_0 ixpiundir_2 ixpiundir_1 sup_set_class fxpiundir_0 fxpiundir_1 fxpiundir_2 ciun fxpiundir_3 elxp2 fxpiundir_0 ixpiundir_1 sup_set_class fxpiundir_1 fxpiundir_2 fxpiundir_3 cxp eliun 3bitr4i eqriv $.
$}
$( Obsolete proof of ~ resiun2 as of 5-Apr-2016.  Distributive law for
       cross product over restriction.  (Contributed by Mario Carneiro,
       11-Nov-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	$d x F $.
	fresiundiOLD_0 $f set x $.
	fresiundiOLD_1 $f class A $.
	fresiundiOLD_2 $f class B $.
	fresiundiOLD_3 $f class F $.
	resiundiOLD $p |- ( F |` U_ x e. A B ) = U_ x e. A ( F |` B ) $= fresiundiOLD_3 fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 ciun cvv cxp cin fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_3 fresiundiOLD_2 cvv cxp cin ciun fresiundiOLD_3 fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 ciun cres fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_3 fresiundiOLD_2 cres ciun fresiundiOLD_3 fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 ciun cvv cxp cin fresiundiOLD_3 fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 cvv cxp ciun cin fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_3 fresiundiOLD_2 cvv cxp cin ciun fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 ciun cvv cxp fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 cvv cxp ciun fresiundiOLD_3 fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 cvv xpiundir ineq2i fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_3 fresiundiOLD_2 cvv cxp iunin2 eqtr4i fresiundiOLD_3 fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_2 ciun df-res fresiundiOLD_0 fresiundiOLD_1 fresiundiOLD_3 fresiundiOLD_2 cres fresiundiOLD_3 fresiundiOLD_2 cvv cxp cin fresiundiOLD_3 fresiundiOLD_2 cres fresiundiOLD_3 fresiundiOLD_2 cvv cxp cin wceq fresiundiOLD_0 sup_set_class fresiundiOLD_1 wcel fresiundiOLD_3 fresiundiOLD_2 df-res a1i iuneq2i 3eqtr4i $.
$}
$( Membership in a union of cross products when the second factor is
       constant.  (Contributed by Mario Carneiro, 29-Dec-2014.) $)
${
	$d x A $.
	$d x B $.
	fiunxpconst_0 $f set x $.
	fiunxpconst_1 $f class A $.
	fiunxpconst_2 $f class B $.
	iunxpconst $p |- U_ x e. A ( { x } X. B ) = ( A X. B ) $= fiunxpconst_0 fiunxpconst_1 fiunxpconst_0 sup_set_class csn ciun fiunxpconst_2 cxp fiunxpconst_0 fiunxpconst_1 fiunxpconst_0 sup_set_class csn fiunxpconst_2 cxp ciun fiunxpconst_1 fiunxpconst_2 cxp fiunxpconst_0 fiunxpconst_1 fiunxpconst_0 sup_set_class csn fiunxpconst_2 xpiundir fiunxpconst_0 fiunxpconst_1 fiunxpconst_0 sup_set_class csn ciun fiunxpconst_1 fiunxpconst_2 fiunxpconst_0 fiunxpconst_1 iunid xpeq1i eqtr3i $.
$}
$( The cross product of two unions.  (Contributed by NM, 12-Aug-2004.) $)
${
	fxpun_0 $f class A $.
	fxpun_1 $f class B $.
	fxpun_2 $f class C $.
	fxpun_3 $f class D $.
	xpun $p |- ( ( A u. B ) X. ( C u. D ) ) = ( ( ( A X. C ) u. ( A X. D ) ) u. ( ( B X. C ) u. ( B X. D ) ) ) $= fxpun_0 fxpun_1 cun fxpun_2 fxpun_3 cun cxp fxpun_0 fxpun_1 cun fxpun_2 cxp fxpun_0 fxpun_1 cun fxpun_3 cxp cun fxpun_0 fxpun_2 cxp fxpun_1 fxpun_2 cxp cun fxpun_0 fxpun_3 cxp fxpun_1 fxpun_3 cxp cun cun fxpun_0 fxpun_2 cxp fxpun_0 fxpun_3 cxp cun fxpun_1 fxpun_2 cxp fxpun_1 fxpun_3 cxp cun cun fxpun_0 fxpun_1 cun fxpun_2 fxpun_3 xpundi fxpun_0 fxpun_1 cun fxpun_2 cxp fxpun_0 fxpun_2 cxp fxpun_1 fxpun_2 cxp cun fxpun_0 fxpun_1 cun fxpun_3 cxp fxpun_0 fxpun_3 cxp fxpun_1 fxpun_3 cxp cun fxpun_0 fxpun_1 fxpun_2 xpundir fxpun_0 fxpun_1 fxpun_3 xpundir uneq12i fxpun_0 fxpun_2 cxp fxpun_1 fxpun_2 cxp fxpun_0 fxpun_3 cxp fxpun_1 fxpun_3 cxp un4 3eqtri $.
$}
$( Membership in universal class of ordered pairs.  (Contributed by NM,
       4-Jul-1994.) $)
${
	$d x y A $.
	felvv_0 $f set x $.
	felvv_1 $f set y $.
	felvv_2 $f class A $.
	elvv $p |- ( A e. ( _V X. _V ) <-> E. x E. y A = <. x , y >. ) $= felvv_2 cvv cvv cxp wcel felvv_2 felvv_0 sup_set_class felvv_1 sup_set_class cop wceq felvv_0 sup_set_class cvv wcel felvv_1 sup_set_class cvv wcel wa wa felvv_1 wex felvv_0 wex felvv_2 felvv_0 sup_set_class felvv_1 sup_set_class cop wceq felvv_1 wex felvv_0 wex felvv_0 felvv_1 felvv_2 cvv cvv elxp felvv_2 felvv_0 sup_set_class felvv_1 sup_set_class cop wceq felvv_2 felvv_0 sup_set_class felvv_1 sup_set_class cop wceq felvv_0 sup_set_class cvv wcel felvv_1 sup_set_class cvv wcel wa wa felvv_0 felvv_1 felvv_0 sup_set_class cvv wcel felvv_1 sup_set_class cvv wcel wa felvv_2 felvv_0 sup_set_class felvv_1 sup_set_class cop wceq felvv_0 sup_set_class cvv wcel felvv_1 sup_set_class cvv wcel felvv_0 vex felvv_1 vex pm3.2i biantru 2exbii bitr4i $.
$}
$( Membership in universal class of ordered triples.  (Contributed by NM,
       17-Dec-2008.) $)
${
	$d w x y z A $.
	ielvvv_0 $f set w $.
	felvvv_0 $f set x $.
	felvvv_1 $f set y $.
	felvvv_2 $f set z $.
	felvvv_3 $f class A $.
	elvvv $p |- ( A e. ( ( _V X. _V ) X. _V ) <-> E. x E. y E. z A = <. <. x , y >. , z >. ) $= felvvv_3 cvv cvv cxp cvv cxp wcel felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel felvvv_2 sup_set_class cvv wcel wa wa felvvv_2 wex ielvvv_0 wex felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq felvvv_2 wex felvvv_1 wex felvvv_0 wex ielvvv_0 felvvv_2 felvvv_3 cvv cvv cxp cvv elxp felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel felvvv_2 sup_set_class cvv wcel wa wa felvvv_2 wex ielvvv_0 wex ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_1 wex felvvv_0 wex felvvv_2 wex ielvvv_0 wex felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq felvvv_2 wex felvvv_1 wex felvvv_0 wex felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel felvvv_2 sup_set_class cvv wcel wa wa ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_1 wex felvvv_0 wex ielvvv_0 felvvv_2 felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel felvvv_2 sup_set_class cvv wcel wa wa felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel wa felvvv_2 sup_set_class cvv wcel wa ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_1 wex felvvv_0 wex felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel felvvv_2 sup_set_class cvv wcel anass felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq wa felvvv_1 wex felvvv_0 wex felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_1 wex felvvv_0 wex wa ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_1 wex felvvv_0 wex felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel wa felvvv_2 sup_set_class cvv wcel wa felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_0 felvvv_1 19.42vv ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq wa felvvv_0 felvvv_1 ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ancom 2exbii felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel wa felvvv_2 sup_set_class cvv wcel wa felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel wa felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_1 wex felvvv_0 wex wa felvvv_2 sup_set_class cvv wcel felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq ielvvv_0 sup_set_class cvv cvv cxp wcel wa felvvv_2 vex biantru ielvvv_0 sup_set_class cvv cvv cxp wcel ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_1 wex felvvv_0 wex felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq felvvv_0 felvvv_1 ielvvv_0 sup_set_class elvv anbi2i bitr3i 3bitr4ri bitr3i 2exbii ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_1 wex felvvv_0 wex felvvv_2 wex ielvvv_0 wex ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_2 wex ielvvv_0 wex felvvv_1 wex felvvv_0 wex felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq felvvv_2 wex felvvv_1 wex felvvv_0 wex ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_0 felvvv_1 ielvvv_0 felvvv_2 exrot4 ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_2 wex ielvvv_0 wex felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq felvvv_2 wex felvvv_0 felvvv_1 ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa felvvv_2 wex ielvvv_0 wex ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa ielvvv_0 wex felvvv_2 wex felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq felvvv_2 wex ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa ielvvv_0 felvvv_2 excom ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq wa ielvvv_0 wex felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq felvvv_2 felvvv_3 ielvvv_0 sup_set_class felvvv_2 sup_set_class cop wceq felvvv_3 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop wceq ielvvv_0 felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_0 sup_set_class felvvv_1 sup_set_class opex ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop wceq ielvvv_0 sup_set_class felvvv_2 sup_set_class cop felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class cop felvvv_3 ielvvv_0 sup_set_class felvvv_0 sup_set_class felvvv_1 sup_set_class cop felvvv_2 sup_set_class opeq1 eqeq2d ceqsexv exbii bitri 2exbii bitr3i bitri bitri $.
$}
$( An ordered pair contains its union.  (Contributed by NM,
       16-Sep-2006.) $)
${
	$d x y A $.
	ielvvuni_0 $f set x $.
	ielvvuni_1 $f set y $.
	felvvuni_0 $f class A $.
	elvvuni $p |- ( A e. ( _V X. _V ) -> U. A e. A ) $= felvvuni_0 cvv cvv cxp wcel felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop wceq ielvvuni_1 wex ielvvuni_0 wex felvvuni_0 cuni felvvuni_0 wcel ielvvuni_0 ielvvuni_1 felvvuni_0 elvv felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop wceq felvvuni_0 cuni felvvuni_0 wcel ielvvuni_0 ielvvuni_1 felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop wceq felvvuni_0 cuni felvvuni_0 wcel ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop cuni ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop wcel ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop cuni ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cpr ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class ielvvuni_0 vex ielvvuni_1 vex uniop ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class ielvvuni_0 vex ielvvuni_1 vex opi2 eqeltri felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop wceq felvvuni_0 cuni ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop cuni felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop unieq felvvuni_0 ielvvuni_0 sup_set_class ielvvuni_1 sup_set_class cop wceq id eleq12d mpbiri exlimivv sylbi $.
$}
$( Intersection of binary relation with cross product.  (Contributed by NM,
     3-Mar-2007.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	fbrinxp2_0 $f class A $.
	fbrinxp2_1 $f class B $.
	fbrinxp2_2 $f class C $.
	fbrinxp2_3 $f class D $.
	fbrinxp2_4 $f class R $.
	brinxp2 $p |- ( A ( R i^i ( C X. D ) ) B <-> ( A e. C /\ B e. D /\ A R B ) ) $= fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 fbrinxp2_2 fbrinxp2_3 cxp cin wbr fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr fbrinxp2_0 fbrinxp2_1 fbrinxp2_2 fbrinxp2_3 cxp wbr wa fbrinxp2_0 fbrinxp2_1 fbrinxp2_2 fbrinxp2_3 cxp wbr fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr wa fbrinxp2_0 fbrinxp2_2 wcel fbrinxp2_1 fbrinxp2_3 wcel fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr w3a fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 fbrinxp2_2 fbrinxp2_3 cxp brin fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr fbrinxp2_0 fbrinxp2_1 fbrinxp2_2 fbrinxp2_3 cxp wbr ancom fbrinxp2_0 fbrinxp2_1 fbrinxp2_2 fbrinxp2_3 cxp wbr fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr wa fbrinxp2_0 fbrinxp2_2 wcel fbrinxp2_1 fbrinxp2_3 wcel wa fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr wa fbrinxp2_0 fbrinxp2_2 wcel fbrinxp2_1 fbrinxp2_3 wcel fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr w3a fbrinxp2_0 fbrinxp2_1 fbrinxp2_2 fbrinxp2_3 cxp wbr fbrinxp2_0 fbrinxp2_2 wcel fbrinxp2_1 fbrinxp2_3 wcel wa fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr fbrinxp2_0 fbrinxp2_1 fbrinxp2_2 fbrinxp2_3 brxp anbi1i fbrinxp2_0 fbrinxp2_2 wcel fbrinxp2_1 fbrinxp2_3 wcel fbrinxp2_0 fbrinxp2_1 fbrinxp2_4 wbr df-3an bitr4i 3bitri $.
$}
$( Intersection of binary relation with cross product.  (Contributed by NM,
     9-Mar-1997.) $)
${
	fbrinxp_0 $f class A $.
	fbrinxp_1 $f class B $.
	fbrinxp_2 $f class C $.
	fbrinxp_3 $f class D $.
	fbrinxp_4 $f class R $.
	brinxp $p |- ( ( A e. C /\ B e. D ) -> ( A R B <-> A ( R i^i ( C X. D ) ) B ) ) $= fbrinxp_0 fbrinxp_1 fbrinxp_4 fbrinxp_2 fbrinxp_3 cxp cin wbr fbrinxp_0 fbrinxp_2 wcel fbrinxp_1 fbrinxp_3 wcel wa fbrinxp_0 fbrinxp_1 fbrinxp_4 wbr fbrinxp_0 fbrinxp_1 fbrinxp_4 fbrinxp_2 fbrinxp_3 cxp cin wbr fbrinxp_0 fbrinxp_2 wcel fbrinxp_1 fbrinxp_3 wcel fbrinxp_0 fbrinxp_1 fbrinxp_4 wbr w3a fbrinxp_0 fbrinxp_2 wcel fbrinxp_1 fbrinxp_3 wcel wa fbrinxp_0 fbrinxp_1 fbrinxp_4 wbr wa fbrinxp_0 fbrinxp_1 fbrinxp_2 fbrinxp_3 fbrinxp_4 brinxp2 fbrinxp_0 fbrinxp_2 wcel fbrinxp_1 fbrinxp_3 wcel fbrinxp_0 fbrinxp_1 fbrinxp_4 wbr df-3an bitri baibr $.
$}
$( Intersection of partial order with cross product of its field.
       (Contributed by Mario Carneiro, 10-Jul-2014.) $)
${
	$d x y z A $.
	$d x y z R $.
	ipoinxp_0 $f set x $.
	ipoinxp_1 $f set y $.
	ipoinxp_2 $f set z $.
	fpoinxp_0 $f class A $.
	fpoinxp_1 $f class R $.
	poinxp $p |- ( R Po A <-> ( R i^i ( A X. A ) ) Po A ) $= ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wi wa ipoinxp_2 fpoinxp_0 wral ipoinxp_1 fpoinxp_0 wral ipoinxp_0 fpoinxp_0 wral ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wi wa ipoinxp_2 fpoinxp_0 wral ipoinxp_1 fpoinxp_0 wral ipoinxp_0 fpoinxp_0 wral fpoinxp_0 fpoinxp_1 wpo fpoinxp_0 fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wpo ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wi wa ipoinxp_2 fpoinxp_0 wral ipoinxp_1 fpoinxp_0 wral ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wi wa ipoinxp_2 fpoinxp_0 wral ipoinxp_1 fpoinxp_0 wral ipoinxp_0 fpoinxp_0 ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wi wa ipoinxp_2 fpoinxp_0 wral ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wi wa ipoinxp_2 fpoinxp_0 wral ipoinxp_1 fpoinxp_0 ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wi wa ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wi wa ipoinxp_2 fpoinxp_0 ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_2 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr wn ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wn ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wi ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wi ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_2 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_2 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 wbr ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wb ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel ipoinxp_2 sup_set_class fpoinxp_0 wcel simpll ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel ipoinxp_2 sup_set_class fpoinxp_0 wcel simpll ipoinxp_0 sup_set_class ipoinxp_0 sup_set_class fpoinxp_0 fpoinxp_0 fpoinxp_1 brinxp syl2anc notbid ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_2 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr wa ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wa ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_2 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class fpoinxp_0 wcel wa ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 wbr ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wb ipoinxp_2 sup_set_class fpoinxp_0 wcel ipoinxp_0 sup_set_class ipoinxp_1 sup_set_class fpoinxp_0 fpoinxp_0 fpoinxp_1 brinxp adantr ipoinxp_1 sup_set_class fpoinxp_0 wcel ipoinxp_2 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wb ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_1 sup_set_class ipoinxp_2 sup_set_class fpoinxp_0 fpoinxp_0 fpoinxp_1 brinxp adantll anbi12d ipoinxp_0 sup_set_class fpoinxp_0 wcel ipoinxp_2 sup_set_class fpoinxp_0 wcel ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 wbr ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin wbr wb ipoinxp_1 sup_set_class fpoinxp_0 wcel ipoinxp_0 sup_set_class ipoinxp_2 sup_set_class fpoinxp_0 fpoinxp_0 fpoinxp_1 brinxp adantlr imbi12d anbi12d ralbidva ralbidva ralbiia ipoinxp_0 ipoinxp_1 ipoinxp_2 fpoinxp_0 fpoinxp_1 df-po ipoinxp_0 ipoinxp_1 ipoinxp_2 fpoinxp_0 fpoinxp_1 fpoinxp_0 fpoinxp_0 cxp cin df-po 3bitr4i $.
$}
$( Intersection of total order with cross product of its field.
       (Contributed by Mario Carneiro, 10-Jul-2014.) $)
${
	$d x y A $.
	$d x y R $.
	isoinxp_0 $f set x $.
	isoinxp_1 $f set y $.
	fsoinxp_0 $f class A $.
	fsoinxp_1 $f class R $.
	soinxp $p |- ( R Or A <-> ( R i^i ( A X. A ) ) Or A ) $= fsoinxp_0 fsoinxp_1 wpo isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 wbr w3o isoinxp_1 fsoinxp_0 wral isoinxp_0 fsoinxp_0 wral wa fsoinxp_0 fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wpo isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr w3o isoinxp_1 fsoinxp_0 wral isoinxp_0 fsoinxp_0 wral wa fsoinxp_0 fsoinxp_1 wor fsoinxp_0 fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wor fsoinxp_0 fsoinxp_1 wpo fsoinxp_0 fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wpo isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 wbr w3o isoinxp_1 fsoinxp_0 wral isoinxp_0 fsoinxp_0 wral isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr w3o isoinxp_1 fsoinxp_0 wral isoinxp_0 fsoinxp_0 wral fsoinxp_0 fsoinxp_1 poinxp isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 wbr w3o isoinxp_1 fsoinxp_0 wral isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr w3o isoinxp_1 fsoinxp_0 wral isoinxp_0 fsoinxp_0 isoinxp_0 sup_set_class fsoinxp_0 wcel isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 wbr w3o isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr w3o isoinxp_1 fsoinxp_0 isoinxp_0 sup_set_class fsoinxp_0 wcel isoinxp_1 sup_set_class fsoinxp_0 wcel wa isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 wbr isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr isoinxp_0 sup_set_class isoinxp_1 sup_set_class fsoinxp_0 fsoinxp_0 fsoinxp_1 brinxp isoinxp_0 sup_set_class fsoinxp_0 wcel isoinxp_1 sup_set_class fsoinxp_0 wcel wa isoinxp_0 sup_set_class isoinxp_1 sup_set_class wceq biidd isoinxp_1 sup_set_class fsoinxp_0 wcel isoinxp_0 sup_set_class fsoinxp_0 wcel isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 wbr isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin wbr wb isoinxp_1 sup_set_class isoinxp_0 sup_set_class fsoinxp_0 fsoinxp_0 fsoinxp_1 brinxp ancoms 3orbi123d ralbidva ralbiia anbi12i isoinxp_0 isoinxp_1 fsoinxp_0 fsoinxp_1 df-so isoinxp_0 isoinxp_1 fsoinxp_0 fsoinxp_1 fsoinxp_0 fsoinxp_0 cxp cin df-so 3bitr4i $.
$}
$( Intersection of well-founded relation with cross product of its field.
       (Contributed by Mario Carneiro, 10-Jul-2014.) $)
${
	$d x y z A $.
	$d x y z R $.
	ifrinxp_0 $f set x $.
	ifrinxp_1 $f set y $.
	ifrinxp_2 $f set z $.
	ffrinxp_0 $f class A $.
	ffrinxp_1 $f class R $.
	frinxp $p |- ( R Fr A <-> ( R i^i ( A X. A ) ) Fr A ) $= ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_2 sup_set_class c0 wne wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex wi ifrinxp_2 wal ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_2 sup_set_class c0 wne wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex wi ifrinxp_2 wal ffrinxp_0 ffrinxp_1 wfr ffrinxp_0 ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wfr ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_2 sup_set_class c0 wne wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex wi ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_2 sup_set_class c0 wne wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex wi ifrinxp_2 ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_2 sup_set_class c0 wne wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class wrex wb ifrinxp_2 sup_set_class c0 wne ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wn ifrinxp_1 ifrinxp_2 sup_set_class wral ifrinxp_0 ifrinxp_2 sup_set_class ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_0 sup_set_class ifrinxp_2 sup_set_class wcel wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr wn ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wn ifrinxp_1 ifrinxp_2 sup_set_class ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_0 sup_set_class ifrinxp_2 sup_set_class wcel wa ifrinxp_1 sup_set_class ifrinxp_2 sup_set_class wcel wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_0 sup_set_class ifrinxp_2 sup_set_class wcel ifrinxp_1 sup_set_class ifrinxp_2 sup_set_class wcel ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wb ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_0 sup_set_class ifrinxp_2 sup_set_class wcel ifrinxp_1 sup_set_class ifrinxp_2 sup_set_class wcel wa ifrinxp_0 sup_set_class ffrinxp_0 wcel ifrinxp_1 sup_set_class ffrinxp_0 wcel wa ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wb ifrinxp_2 sup_set_class ffrinxp_0 wss ifrinxp_0 sup_set_class ifrinxp_2 sup_set_class wcel ifrinxp_0 sup_set_class ffrinxp_0 wcel ifrinxp_1 sup_set_class ifrinxp_2 sup_set_class wcel ifrinxp_1 sup_set_class ffrinxp_0 wcel ifrinxp_2 sup_set_class ffrinxp_0 ifrinxp_0 sup_set_class ssel ifrinxp_2 sup_set_class ffrinxp_0 ifrinxp_1 sup_set_class ssel anim12d ifrinxp_1 sup_set_class ffrinxp_0 wcel ifrinxp_0 sup_set_class ffrinxp_0 wcel ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 wbr ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin wbr wb ifrinxp_1 sup_set_class ifrinxp_0 sup_set_class ffrinxp_0 ffrinxp_0 ffrinxp_1 brinxp ancoms syl6 impl notbid ralbidva rexbidva adantr pm5.74i albii ifrinxp_2 ifrinxp_0 ifrinxp_1 ffrinxp_0 ffrinxp_1 df-fr ifrinxp_2 ifrinxp_0 ifrinxp_1 ffrinxp_0 ffrinxp_1 ffrinxp_0 ffrinxp_0 cxp cin df-fr 3bitr4i $.
$}
$( Intersection of set-like relation with cross product of its field.
       (Contributed by Mario Carneiro, 22-Jun-2015.) $)
${
	$d x y A $.
	$d x y R $.
	iseinxp_0 $f set x $.
	iseinxp_1 $f set y $.
	fseinxp_0 $f class A $.
	fseinxp_1 $f class R $.
	seinxp $p |- ( R Se A <-> ( R i^i ( A X. A ) ) Se A ) $= iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 wbr iseinxp_1 fseinxp_0 crab cvv wcel iseinxp_0 fseinxp_0 wral iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 fseinxp_0 fseinxp_0 cxp cin wbr iseinxp_1 fseinxp_0 crab cvv wcel iseinxp_0 fseinxp_0 wral fseinxp_0 fseinxp_1 wse fseinxp_0 fseinxp_1 fseinxp_0 fseinxp_0 cxp cin wse iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 wbr iseinxp_1 fseinxp_0 crab cvv wcel iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 fseinxp_0 fseinxp_0 cxp cin wbr iseinxp_1 fseinxp_0 crab cvv wcel iseinxp_0 fseinxp_0 iseinxp_0 sup_set_class fseinxp_0 wcel iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 wbr iseinxp_1 fseinxp_0 crab iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 fseinxp_0 fseinxp_0 cxp cin wbr iseinxp_1 fseinxp_0 crab cvv iseinxp_0 sup_set_class fseinxp_0 wcel iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 wbr iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 fseinxp_0 fseinxp_0 cxp cin wbr iseinxp_1 fseinxp_0 iseinxp_1 sup_set_class fseinxp_0 wcel iseinxp_0 sup_set_class fseinxp_0 wcel iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 wbr iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_1 fseinxp_0 fseinxp_0 cxp cin wbr wb iseinxp_1 sup_set_class iseinxp_0 sup_set_class fseinxp_0 fseinxp_0 fseinxp_1 brinxp ancoms rabbidva eleq1d ralbiia iseinxp_0 iseinxp_1 fseinxp_0 fseinxp_1 df-se iseinxp_0 iseinxp_1 fseinxp_0 fseinxp_1 fseinxp_0 fseinxp_0 cxp cin df-se 3bitr4i $.
$}
$( Intersection of well-ordering with cross product of its field.
       (Contributed by NM, 9-Mar-1997.)  (Revised by Mario Carneiro,
       10-Jul-2014.) $)
${
	fweinxp_0 $f class A $.
	fweinxp_1 $f class R $.
	weinxp $p |- ( R We A <-> ( R i^i ( A X. A ) ) We A ) $= fweinxp_0 fweinxp_1 wfr fweinxp_0 fweinxp_1 wor wa fweinxp_0 fweinxp_1 fweinxp_0 fweinxp_0 cxp cin wfr fweinxp_0 fweinxp_1 fweinxp_0 fweinxp_0 cxp cin wor wa fweinxp_0 fweinxp_1 wwe fweinxp_0 fweinxp_1 fweinxp_0 fweinxp_0 cxp cin wwe fweinxp_0 fweinxp_1 wfr fweinxp_0 fweinxp_1 fweinxp_0 fweinxp_0 cxp cin wfr fweinxp_0 fweinxp_1 wor fweinxp_0 fweinxp_1 fweinxp_0 fweinxp_0 cxp cin wor fweinxp_0 fweinxp_1 frinxp fweinxp_0 fweinxp_1 soinxp anbi12i fweinxp_0 fweinxp_1 df-we fweinxp_0 fweinxp_1 fweinxp_0 fweinxp_0 cxp cin df-we 3bitr4i $.
$}
$( Partial ordering of a singleton.  (Contributed by NM, 27-Apr-2009.)
       (Revised by Mario Carneiro, 23-Apr-2015.) $)
${
	$d x y z A $.
	$d x y z R $.
	iposn_0 $f set x $.
	iposn_1 $f set y $.
	iposn_2 $f set z $.
	fposn_0 $f class A $.
	fposn_1 $f class R $.
	posn $p |- ( Rel R -> ( R Po { A } <-> -. A R A ) ) $= fposn_1 wrel fposn_0 cvv wcel fposn_0 csn fposn_1 wpo fposn_0 fposn_0 fposn_1 wbr wn wb fposn_0 csn fposn_1 wpo iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_2 fposn_0 csn wral iposn_1 fposn_0 csn wral iposn_0 fposn_0 csn wral fposn_1 wrel fposn_0 cvv wcel wa fposn_0 fposn_0 fposn_1 wbr wn iposn_0 iposn_1 iposn_2 fposn_0 csn fposn_1 df-po fposn_0 cvv wcel iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_2 fposn_0 csn wral iposn_1 fposn_0 csn wral iposn_0 fposn_0 csn wral fposn_0 fposn_0 fposn_1 wbr wn wb fposn_1 wrel fposn_0 cvv wcel iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_2 fposn_0 csn wral iposn_1 fposn_0 csn wral iposn_0 fposn_0 csn wral iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 fposn_0 csn wral fposn_0 fposn_0 fposn_1 wbr wn fposn_0 cvv wcel iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_2 fposn_0 csn wral iposn_1 fposn_0 csn wral iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 fposn_0 csn fposn_0 cvv wcel iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_2 fposn_0 csn wral iposn_1 fposn_0 csn wral iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi wa iposn_1 fposn_0 csn wral iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn fposn_0 cvv wcel iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_2 fposn_0 csn wral iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi wa iposn_1 fposn_0 csn iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi wa iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi wa iposn_2 fposn_0 cvv iposn_2 sup_set_class fposn_0 wceq iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr wi iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_2 sup_set_class fposn_0 wceq iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr wa iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class iposn_2 sup_set_class fposn_1 wbr iposn_0 sup_set_class fposn_0 fposn_1 wbr iposn_2 sup_set_class fposn_0 wceq iposn_1 sup_set_class iposn_2 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_2 sup_set_class fposn_0 iposn_1 sup_set_class fposn_1 breq2 anbi2d iposn_2 sup_set_class fposn_0 iposn_0 sup_set_class fposn_1 breq2 imbi12d anbi2d ralsng ralbidv iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi wa iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_1 fposn_0 cvv iposn_1 sup_set_class fposn_0 wceq iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi wa iposn_1 sup_set_class fposn_0 wceq iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class fposn_0 fposn_1 wbr wi iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr wa iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 wceq iposn_0 sup_set_class fposn_0 fposn_1 wbr iposn_0 sup_set_class iposn_1 sup_set_class fposn_1 wbr iposn_1 sup_set_class fposn_0 fposn_1 wbr simpl iposn_1 sup_set_class fposn_0 iposn_0 sup_set_class fposn_1 breq2 syl5ib biantrud bicomd ralsng bitrd ralbidv iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr wn fposn_0 fposn_0 fposn_1 wbr wn iposn_0 fposn_0 cvv iposn_0 sup_set_class fposn_0 wceq iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr fposn_0 fposn_0 fposn_1 wbr iposn_0 sup_set_class fposn_0 wceq iposn_0 sup_set_class iposn_0 sup_set_class fposn_1 wbr fposn_0 fposn_0 fposn_1 wbr wb iposn_0 sup_set_class fposn_0 iposn_0 sup_set_class fposn_0 fposn_1 breq12 anidms notbid ralsng bitrd adantl syl5bb fposn_1 wrel fposn_0 cvv wcel wn wa fposn_0 csn fposn_1 wpo fposn_0 fposn_0 fposn_1 wbr wn fposn_0 cvv wcel wn fposn_0 csn fposn_1 wpo fposn_1 wrel fposn_0 cvv wcel wn fposn_0 csn fposn_1 wpo c0 fposn_1 wpo fposn_1 po0 fposn_0 cvv wcel wn fposn_0 csn c0 wceq fposn_0 csn fposn_1 wpo c0 fposn_1 wpo wb fposn_0 snprc fposn_0 csn c0 fposn_1 poeq2 sylbi mpbiri adantl fposn_1 wrel fposn_0 fposn_0 fposn_1 wbr fposn_0 cvv wcel fposn_1 wrel fposn_0 fposn_0 fposn_1 wbr fposn_0 cvv wcel fposn_0 fposn_0 fposn_1 brrelex ex con3and 2thd pm2.61dan $.
$}
$( Strict ordering on a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.) $)
${
	$d x y A $.
	$d x y R $.
	isosn_0 $f set x $.
	isosn_1 $f set y $.
	fsosn_0 $f class A $.
	fsosn_1 $f class R $.
	sosn $p |- ( Rel R -> ( R Or { A } <-> -. A R A ) ) $= fsosn_0 csn fsosn_1 wor fsosn_0 csn fsosn_1 wpo fsosn_1 wrel fsosn_0 fsosn_0 fsosn_1 wbr wn fsosn_0 csn fsosn_1 wor fsosn_0 csn fsosn_1 wpo isosn_0 sup_set_class isosn_1 sup_set_class fsosn_1 wbr isosn_0 sup_set_class isosn_1 sup_set_class wceq isosn_1 sup_set_class isosn_0 sup_set_class fsosn_1 wbr w3o isosn_1 fsosn_0 csn wral isosn_0 fsosn_0 csn wral isosn_0 sup_set_class isosn_1 sup_set_class fsosn_1 wbr isosn_0 sup_set_class isosn_1 sup_set_class wceq isosn_1 sup_set_class isosn_0 sup_set_class fsosn_1 wbr w3o isosn_0 isosn_1 fsosn_0 csn isosn_0 sup_set_class fsosn_0 csn wcel isosn_1 sup_set_class fsosn_0 csn wcel wa isosn_0 sup_set_class isosn_1 sup_set_class wceq isosn_0 sup_set_class isosn_1 sup_set_class fsosn_1 wbr isosn_0 sup_set_class isosn_1 sup_set_class wceq isosn_1 sup_set_class isosn_0 sup_set_class fsosn_1 wbr w3o isosn_0 sup_set_class fsosn_0 csn wcel isosn_1 sup_set_class fsosn_0 csn wcel isosn_0 sup_set_class fsosn_0 isosn_1 sup_set_class isosn_0 sup_set_class fsosn_0 elsni isosn_1 sup_set_class fsosn_0 csn wcel isosn_1 sup_set_class fsosn_0 isosn_1 sup_set_class fsosn_0 elsni eqcomd sylan9eq isosn_0 sup_set_class isosn_1 sup_set_class wceq isosn_0 sup_set_class isosn_1 sup_set_class fsosn_1 wbr isosn_1 sup_set_class isosn_0 sup_set_class fsosn_1 wbr 3mix2 syl rgen2a isosn_0 isosn_1 fsosn_0 csn fsosn_1 df-so mpbiran2 fsosn_0 fsosn_1 posn syl5bb $.
$}
$( Founded relation on a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
${
	$d x y z A $.
	$d x y z R $.
	ifrsn_0 $f set x $.
	ifrsn_1 $f set y $.
	ifrsn_2 $f set z $.
	ffrsn_0 $f class A $.
	ffrsn_1 $f class R $.
	frsn $p |- ( Rel R -> ( R Fr { A } <-> -. A R A ) ) $= ffrsn_1 wrel ffrsn_0 cvv wcel ffrsn_0 csn ffrsn_1 wfr ffrsn_0 ffrsn_0 ffrsn_1 wbr wn wb ffrsn_1 wrel ffrsn_0 cvv wcel wa ffrsn_0 csn ffrsn_1 wfr ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 csn wrex ffrsn_0 ffrsn_0 ffrsn_1 wbr wn ffrsn_0 csn ffrsn_1 wfr ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne wa ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex wi ifrsn_0 wal ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 csn wrex ifrsn_0 ifrsn_1 ifrsn_2 ffrsn_0 csn ffrsn_1 df-fr ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne wa ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex wi ifrsn_0 wal ifrsn_0 sup_set_class ffrsn_0 csn wceq ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex wi ifrsn_0 wal ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 csn wrex ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne wa ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex wi ifrsn_0 sup_set_class ffrsn_0 csn wceq ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex wi ifrsn_0 ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne wa ifrsn_0 sup_set_class ffrsn_0 csn wceq ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne wa ifrsn_0 sup_set_class ffrsn_0 csn wceq ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne ifrsn_0 sup_set_class ffrsn_0 csn wceq ifrsn_0 sup_set_class c0 wne ifrsn_0 sup_set_class c0 wceq wn ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss wa ifrsn_0 sup_set_class ffrsn_0 csn wceq ifrsn_0 sup_set_class c0 df-ne ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss wa ifrsn_0 sup_set_class c0 wceq ifrsn_0 sup_set_class ffrsn_0 csn wceq ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wceq ifrsn_0 sup_set_class ffrsn_0 csn wceq wo ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wss simpr ifrsn_0 sup_set_class ffrsn_0 sssn sylib ord syl5bi impr ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wceq wa ifrsn_0 sup_set_class ffrsn_0 csn wss ifrsn_0 sup_set_class c0 wne ifrsn_0 sup_set_class ffrsn_0 csn wceq ifrsn_0 sup_set_class ffrsn_0 csn wss ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn eqimss adantl ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wceq wa ifrsn_0 sup_set_class ffrsn_0 csn c0 ffrsn_1 wrel ffrsn_0 cvv wcel wa ifrsn_0 sup_set_class ffrsn_0 csn wceq simpr ffrsn_0 cvv wcel ffrsn_0 csn c0 wne ffrsn_1 wrel ifrsn_0 sup_set_class ffrsn_0 csn wceq ffrsn_0 cvv snnzg ad2antlr eqnetrd jca impbida imbi1d albidv ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_1 ifrsn_0 sup_set_class wrex ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 csn wrex ifrsn_0 ffrsn_0 csn ffrsn_0 snex ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class wral ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ifrsn_0 sup_set_class ffrsn_0 csn ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ifrsn_0 sup_set_class ffrsn_0 csn raleq rexeqbi1dv ceqsalv syl6bb syl5bb ffrsn_0 cvv wcel ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 csn wrex ffrsn_0 ffrsn_0 ffrsn_1 wbr wn wb ffrsn_1 wrel ffrsn_0 cvv wcel ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 csn wrex ifrsn_2 sup_set_class ffrsn_0 ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ffrsn_0 ffrsn_0 ffrsn_1 wbr wn ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_2 sup_set_class ffrsn_0 ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn wral ifrsn_1 ffrsn_0 cvv ifrsn_1 sup_set_class ffrsn_0 wceq ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr wn ifrsn_2 sup_set_class ffrsn_0 ffrsn_1 wbr wn ifrsn_2 ffrsn_0 csn ifrsn_1 sup_set_class ffrsn_0 wceq ifrsn_2 sup_set_class ifrsn_1 sup_set_class ffrsn_1 wbr ifrsn_2 sup_set_class ffrsn_0 ffrsn_1 wbr ifrsn_1 sup_set_class ffrsn_0 ifrsn_2 sup_set_class ffrsn_1 breq2 notbid ralbidv rexsng ifrsn_2 sup_set_class ffrsn_0 ffrsn_1 wbr wn ffrsn_0 ffrsn_0 ffrsn_1 wbr wn ifrsn_2 ffrsn_0 cvv ifrsn_2 sup_set_class ffrsn_0 wceq ifrsn_2 sup_set_class ffrsn_0 ffrsn_1 wbr ffrsn_0 ffrsn_0 ffrsn_1 wbr ifrsn_2 sup_set_class ffrsn_0 ffrsn_0 ffrsn_1 breq1 notbid ralsng bitrd adantl bitrd ffrsn_1 wrel ffrsn_0 cvv wcel wn wa ffrsn_0 csn ffrsn_1 wfr ffrsn_0 ffrsn_0 ffrsn_1 wbr wn ffrsn_0 cvv wcel wn ffrsn_0 csn ffrsn_1 wfr ffrsn_1 wrel ffrsn_0 cvv wcel wn ffrsn_0 csn c0 wceq ffrsn_0 csn ffrsn_1 wfr ffrsn_0 snprc ffrsn_0 csn c0 wceq ffrsn_0 csn ffrsn_1 wfr c0 ffrsn_1 wfr ffrsn_1 fr0 ffrsn_0 csn c0 ffrsn_1 freq2 mpbiri sylbi adantl ffrsn_1 wrel ffrsn_0 ffrsn_0 ffrsn_1 wbr ffrsn_0 cvv wcel ffrsn_1 wrel ffrsn_0 ffrsn_0 ffrsn_1 wbr ffrsn_0 cvv wcel ffrsn_0 ffrsn_0 ffrsn_1 brrelex ex con3and 2thd pm2.61dan $.
$}
$( Well-ordering of a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.) $)
${
	fwesn_0 $f class A $.
	fwesn_1 $f class R $.
	wesn $p |- ( Rel R -> ( R We { A } <-> -. A R A ) ) $= fwesn_1 wrel fwesn_0 csn fwesn_1 wfr fwesn_0 csn fwesn_1 wor wa fwesn_0 fwesn_0 fwesn_1 wbr wn fwesn_0 fwesn_0 fwesn_1 wbr wn wa fwesn_0 csn fwesn_1 wwe fwesn_0 fwesn_0 fwesn_1 wbr wn fwesn_1 wrel fwesn_0 csn fwesn_1 wfr fwesn_0 fwesn_0 fwesn_1 wbr wn fwesn_0 csn fwesn_1 wor fwesn_0 fwesn_0 fwesn_1 wbr wn fwesn_0 fwesn_1 frsn fwesn_0 fwesn_1 sosn anbi12d fwesn_0 csn fwesn_1 df-we fwesn_0 fwesn_0 fwesn_1 wbr wn pm4.24 3bitr4g $.
$}
$( An abstraction relation is a subset of a related cross product.
       (Contributed by NM, 16-Jul-1995.) $)
${
	$d x y A $.
	$d x y B $.
	fopabssxp_0 $f wff ph $.
	fopabssxp_1 $f set x $.
	fopabssxp_2 $f set y $.
	fopabssxp_3 $f class A $.
	fopabssxp_4 $f class B $.
	opabssxp $p |- { <. x , y >. | ( ( x e. A /\ y e. B ) /\ ph ) } C_ ( A X. B ) $= fopabssxp_1 sup_set_class fopabssxp_3 wcel fopabssxp_2 sup_set_class fopabssxp_4 wcel wa fopabssxp_0 wa fopabssxp_1 fopabssxp_2 copab fopabssxp_1 sup_set_class fopabssxp_3 wcel fopabssxp_2 sup_set_class fopabssxp_4 wcel wa fopabssxp_1 fopabssxp_2 copab fopabssxp_3 fopabssxp_4 cxp fopabssxp_1 sup_set_class fopabssxp_3 wcel fopabssxp_2 sup_set_class fopabssxp_4 wcel wa fopabssxp_0 wa fopabssxp_1 sup_set_class fopabssxp_3 wcel fopabssxp_2 sup_set_class fopabssxp_4 wcel wa fopabssxp_1 fopabssxp_2 fopabssxp_1 sup_set_class fopabssxp_3 wcel fopabssxp_2 sup_set_class fopabssxp_4 wcel wa fopabssxp_0 simpl ssopab2i fopabssxp_1 fopabssxp_2 fopabssxp_3 fopabssxp_4 df-xp sseqtr4i $.
$}
$( The law of concretion for a binary relation.  See ~ brab2a for alternate
       proof.  TODO: should one of them be deleted?  (Contributed by Mario
       Carneiro, 28-Apr-2015.)  (Proof modification is discouraged.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	$d x y ps $.
	fbrab2ga_0 $f wff ph $.
	fbrab2ga_1 $f wff ps $.
	fbrab2ga_2 $f set x $.
	fbrab2ga_3 $f set y $.
	fbrab2ga_4 $f class A $.
	fbrab2ga_5 $f class B $.
	fbrab2ga_6 $f class C $.
	fbrab2ga_7 $f class D $.
	fbrab2ga_8 $f class R $.
	ebrab2ga_0 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
	ebrab2ga_1 $e |- R = { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } $.
	brab2ga $p |- ( A R B <-> ( ( A e. C /\ B e. D ) /\ ps ) ) $= fbrab2ga_4 fbrab2ga_5 fbrab2ga_8 wbr fbrab2ga_4 fbrab2ga_6 wcel fbrab2ga_5 fbrab2ga_7 wcel wa fbrab2ga_1 fbrab2ga_4 fbrab2ga_5 fbrab2ga_6 fbrab2ga_7 fbrab2ga_8 fbrab2ga_8 fbrab2ga_2 sup_set_class fbrab2ga_6 wcel fbrab2ga_3 sup_set_class fbrab2ga_7 wcel wa fbrab2ga_0 wa fbrab2ga_2 fbrab2ga_3 copab fbrab2ga_6 fbrab2ga_7 cxp ebrab2ga_1 fbrab2ga_0 fbrab2ga_2 fbrab2ga_3 fbrab2ga_6 fbrab2ga_7 opabssxp eqsstri brel fbrab2ga_4 fbrab2ga_5 fbrab2ga_8 wbr fbrab2ga_4 fbrab2ga_5 cop fbrab2ga_2 sup_set_class fbrab2ga_6 wcel fbrab2ga_3 sup_set_class fbrab2ga_7 wcel wa fbrab2ga_0 wa fbrab2ga_2 fbrab2ga_3 copab wcel fbrab2ga_4 fbrab2ga_6 wcel fbrab2ga_5 fbrab2ga_7 wcel wa fbrab2ga_1 fbrab2ga_4 fbrab2ga_5 fbrab2ga_8 wbr fbrab2ga_4 fbrab2ga_5 cop fbrab2ga_8 wcel fbrab2ga_4 fbrab2ga_5 cop fbrab2ga_2 sup_set_class fbrab2ga_6 wcel fbrab2ga_3 sup_set_class fbrab2ga_7 wcel wa fbrab2ga_0 wa fbrab2ga_2 fbrab2ga_3 copab wcel fbrab2ga_4 fbrab2ga_5 fbrab2ga_8 df-br fbrab2ga_8 fbrab2ga_2 sup_set_class fbrab2ga_6 wcel fbrab2ga_3 sup_set_class fbrab2ga_7 wcel wa fbrab2ga_0 wa fbrab2ga_2 fbrab2ga_3 copab fbrab2ga_4 fbrab2ga_5 cop ebrab2ga_1 eleq2i bitri fbrab2ga_0 fbrab2ga_1 fbrab2ga_2 fbrab2ga_3 fbrab2ga_4 fbrab2ga_5 fbrab2ga_6 fbrab2ga_7 ebrab2ga_0 opelopab2a syl5bb biadan2 $.
$}
$( Implicit substitution of class for ordered pair.  (Contributed by NM,
       5-Mar-1995.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y ps $.
	foptocl_0 $f wff ph $.
	foptocl_1 $f wff ps $.
	foptocl_2 $f set x $.
	foptocl_3 $f set y $.
	foptocl_4 $f class A $.
	foptocl_5 $f class B $.
	foptocl_6 $f class C $.
	foptocl_7 $f class D $.
	eoptocl_0 $e |- D = ( B X. C ) $.
	eoptocl_1 $e |- ( <. x , y >. = A -> ( ph <-> ps ) ) $.
	eoptocl_2 $e |- ( ( x e. B /\ y e. C ) -> ph ) $.
	optocl $p |- ( A e. D -> ps ) $= foptocl_1 foptocl_4 foptocl_5 foptocl_6 cxp foptocl_7 foptocl_4 foptocl_5 foptocl_6 cxp wcel foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_4 wceq foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_5 foptocl_6 cxp wcel wa foptocl_3 wex foptocl_2 wex foptocl_1 foptocl_2 foptocl_3 foptocl_4 foptocl_5 foptocl_6 elxp3 foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_4 wceq foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_5 foptocl_6 cxp wcel wa foptocl_1 foptocl_2 foptocl_3 foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_4 wceq foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_5 foptocl_6 cxp wcel foptocl_1 foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_5 foptocl_6 cxp wcel foptocl_0 foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_4 wceq foptocl_1 foptocl_2 sup_set_class foptocl_3 sup_set_class cop foptocl_5 foptocl_6 cxp wcel foptocl_2 sup_set_class foptocl_5 wcel foptocl_3 sup_set_class foptocl_6 wcel wa foptocl_0 foptocl_2 sup_set_class foptocl_3 sup_set_class foptocl_5 foptocl_6 opelxp eoptocl_2 sylbi eoptocl_1 syl5ib imp exlimivv sylbi eoptocl_0 eleq2s $.
$}
$( Implicit substitution of classes for ordered pairs.  (Contributed by NM,
       12-Mar-1995.) $)
${
	$d x y z w A $.
	$d z w B $.
	$d x y z w C $.
	$d x y z w D $.
	$d x y ps $.
	$d z w ch $.
	$d z w R $.
	f2optocl_0 $f wff ph $.
	f2optocl_1 $f wff ps $.
	f2optocl_2 $f wff ch $.
	f2optocl_3 $f set x $.
	f2optocl_4 $f set y $.
	f2optocl_5 $f set z $.
	f2optocl_6 $f set w $.
	f2optocl_7 $f class A $.
	f2optocl_8 $f class B $.
	f2optocl_9 $f class C $.
	f2optocl_10 $f class D $.
	f2optocl_11 $f class R $.
	e2optocl_0 $e |- R = ( C X. D ) $.
	e2optocl_1 $e |- ( <. x , y >. = A -> ( ph <-> ps ) ) $.
	e2optocl_2 $e |- ( <. z , w >. = B -> ( ps <-> ch ) ) $.
	e2optocl_3 $e |- ( ( ( x e. C /\ y e. D ) /\ ( z e. C /\ w e. D ) ) -> ph ) $.
	2optocl $p |- ( ( A e. R /\ B e. R ) -> ch ) $= f2optocl_8 f2optocl_11 wcel f2optocl_7 f2optocl_11 wcel f2optocl_2 f2optocl_7 f2optocl_11 wcel f2optocl_1 wi f2optocl_7 f2optocl_11 wcel f2optocl_2 wi f2optocl_5 f2optocl_6 f2optocl_8 f2optocl_9 f2optocl_10 f2optocl_11 e2optocl_0 f2optocl_5 sup_set_class f2optocl_6 sup_set_class cop f2optocl_8 wceq f2optocl_1 f2optocl_2 f2optocl_7 f2optocl_11 wcel e2optocl_2 imbi2d f2optocl_7 f2optocl_11 wcel f2optocl_5 sup_set_class f2optocl_9 wcel f2optocl_6 sup_set_class f2optocl_10 wcel wa f2optocl_1 f2optocl_5 sup_set_class f2optocl_9 wcel f2optocl_6 sup_set_class f2optocl_10 wcel wa f2optocl_0 wi f2optocl_5 sup_set_class f2optocl_9 wcel f2optocl_6 sup_set_class f2optocl_10 wcel wa f2optocl_1 wi f2optocl_3 f2optocl_4 f2optocl_7 f2optocl_9 f2optocl_10 f2optocl_11 e2optocl_0 f2optocl_3 sup_set_class f2optocl_4 sup_set_class cop f2optocl_7 wceq f2optocl_0 f2optocl_1 f2optocl_5 sup_set_class f2optocl_9 wcel f2optocl_6 sup_set_class f2optocl_10 wcel wa e2optocl_1 imbi2d f2optocl_3 sup_set_class f2optocl_9 wcel f2optocl_4 sup_set_class f2optocl_10 wcel wa f2optocl_5 sup_set_class f2optocl_9 wcel f2optocl_6 sup_set_class f2optocl_10 wcel wa f2optocl_0 e2optocl_3 ex optocl com12 optocl impcom $.
$}
$( Implicit substitution of classes for ordered pairs.  (Contributed by NM,
       12-Mar-1995.) $)
${
	$d x y z w v u A $.
	$d z w v u B $.
	$d v u C $.
	$d x y z w v u D $.
	$d x y z w v u F $.
	$d z w v u R $.
	$d x y ps $.
	$d z w ch $.
	$d v u th $.
	f3optocl_0 $f wff ph $.
	f3optocl_1 $f wff ps $.
	f3optocl_2 $f wff ch $.
	f3optocl_3 $f wff th $.
	f3optocl_4 $f set x $.
	f3optocl_5 $f set y $.
	f3optocl_6 $f set z $.
	f3optocl_7 $f set w $.
	f3optocl_8 $f set v $.
	f3optocl_9 $f set u $.
	f3optocl_10 $f class A $.
	f3optocl_11 $f class B $.
	f3optocl_12 $f class C $.
	f3optocl_13 $f class D $.
	f3optocl_14 $f class R $.
	f3optocl_15 $f class F $.
	e3optocl_0 $e |- R = ( D X. F ) $.
	e3optocl_1 $e |- ( <. x , y >. = A -> ( ph <-> ps ) ) $.
	e3optocl_2 $e |- ( <. z , w >. = B -> ( ps <-> ch ) ) $.
	e3optocl_3 $e |- ( <. v , u >. = C -> ( ch <-> th ) ) $.
	e3optocl_4 $e |- ( ( ( x e. D /\ y e. F ) /\ ( z e. D /\ w e. F ) /\ ( v e. D /\ u e. F ) ) -> ph ) $.
	3optocl $p |- ( ( A e. R /\ B e. R /\ C e. R ) -> th ) $= f3optocl_10 f3optocl_14 wcel f3optocl_11 f3optocl_14 wcel f3optocl_12 f3optocl_14 wcel f3optocl_3 f3optocl_12 f3optocl_14 wcel f3optocl_10 f3optocl_14 wcel f3optocl_11 f3optocl_14 wcel wa f3optocl_3 f3optocl_10 f3optocl_14 wcel f3optocl_11 f3optocl_14 wcel wa f3optocl_2 wi f3optocl_10 f3optocl_14 wcel f3optocl_11 f3optocl_14 wcel wa f3optocl_3 wi f3optocl_8 f3optocl_9 f3optocl_12 f3optocl_13 f3optocl_15 f3optocl_14 e3optocl_0 f3optocl_8 sup_set_class f3optocl_9 sup_set_class cop f3optocl_12 wceq f3optocl_2 f3optocl_3 f3optocl_10 f3optocl_14 wcel f3optocl_11 f3optocl_14 wcel wa e3optocl_3 imbi2d f3optocl_10 f3optocl_14 wcel f3optocl_11 f3optocl_14 wcel wa f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa f3optocl_2 f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa f3optocl_0 wi f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa f3optocl_1 wi f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa f3optocl_2 wi f3optocl_4 f3optocl_5 f3optocl_6 f3optocl_7 f3optocl_10 f3optocl_11 f3optocl_13 f3optocl_15 f3optocl_14 e3optocl_0 f3optocl_4 sup_set_class f3optocl_5 sup_set_class cop f3optocl_10 wceq f3optocl_0 f3optocl_1 f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa e3optocl_1 imbi2d f3optocl_6 sup_set_class f3optocl_7 sup_set_class cop f3optocl_11 wceq f3optocl_1 f3optocl_2 f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa e3optocl_2 imbi2d f3optocl_4 sup_set_class f3optocl_13 wcel f3optocl_5 sup_set_class f3optocl_15 wcel wa f3optocl_6 sup_set_class f3optocl_13 wcel f3optocl_7 sup_set_class f3optocl_15 wcel wa f3optocl_8 sup_set_class f3optocl_13 wcel f3optocl_9 sup_set_class f3optocl_15 wcel wa f3optocl_0 e3optocl_4 3expia 2optocl com12 optocl impcom 3impa $.
$}
$( Ordered pair membership in a relation.  Special case.  (Contributed by
       NM, 5-Aug-1995.) $)
${
	$d x y z w v u A $.
	$d x y z w v u B $.
	$d x y z w v u C $.
	$d x y z w v u D $.
	$d x y z w v u S $.
	$d x y ph $.
	$d z w v u ps $.
	fopbrop_0 $f wff ph $.
	fopbrop_1 $f wff ps $.
	fopbrop_2 $f set x $.
	fopbrop_3 $f set y $.
	fopbrop_4 $f set z $.
	fopbrop_5 $f set w $.
	fopbrop_6 $f set v $.
	fopbrop_7 $f set u $.
	fopbrop_8 $f class A $.
	fopbrop_9 $f class B $.
	fopbrop_10 $f class C $.
	fopbrop_11 $f class D $.
	fopbrop_12 $f class R $.
	fopbrop_13 $f class S $.
	eopbrop_0 $e |- ( ( ( z = A /\ w = B ) /\ ( v = C /\ u = D ) ) -> ( ph <-> ps ) ) $.
	eopbrop_1 $e |- R = { <. x , y >. | ( ( x e. ( S X. S ) /\ y e. ( S X. S ) ) /\ E. z E. w E. v E. u ( ( x = <. z , w >. /\ y = <. v , u >. ) /\ ph ) ) } $.
	opbrop $p |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> ( <. A , B >. R <. C , D >. <-> ps ) ) $= fopbrop_8 fopbrop_13 wcel fopbrop_9 fopbrop_13 wcel wa fopbrop_10 fopbrop_13 wcel fopbrop_11 fopbrop_13 wcel wa wa fopbrop_8 fopbrop_9 cop fopbrop_10 fopbrop_11 cop fopbrop_12 wbr fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_1 wa fopbrop_1 fopbrop_8 fopbrop_9 cop fopbrop_10 fopbrop_11 cop fopbrop_12 wbr fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex wa fopbrop_8 fopbrop_13 wcel fopbrop_9 fopbrop_13 wcel wa fopbrop_10 fopbrop_13 wcel fopbrop_11 fopbrop_13 wcel wa wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_1 wa fopbrop_2 sup_set_class fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_2 sup_set_class fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex wa fopbrop_2 fopbrop_3 fopbrop_8 fopbrop_9 cop fopbrop_10 fopbrop_11 cop fopbrop_12 fopbrop_8 fopbrop_9 opex fopbrop_10 fopbrop_11 opex fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop wceq fopbrop_2 sup_set_class fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_2 sup_set_class fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop wceq fopbrop_2 sup_set_class fopbrop_13 fopbrop_13 cxp wcel fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp eleq1 anbi1d fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop wceq fopbrop_2 sup_set_class fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_4 fopbrop_5 fopbrop_6 fopbrop_7 fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop wceq fopbrop_2 sup_set_class fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop wceq fopbrop_2 sup_set_class fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq fopbrop_2 sup_set_class fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop eqeq1 anbi1d anbi1d 4exbidv anbi12d fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop wceq fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop wceq fopbrop_3 sup_set_class fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp eleq1 anbi2d fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop wceq fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_4 fopbrop_5 fopbrop_6 fopbrop_7 fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop wceq fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop wceq fopbrop_3 sup_set_class fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_3 sup_set_class fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop eqeq1 anbi2d anbi1d 4exbidv anbi12d eopbrop_1 brab fopbrop_8 fopbrop_13 wcel fopbrop_9 fopbrop_13 wcel wa fopbrop_10 fopbrop_13 wcel fopbrop_11 fopbrop_13 wcel wa wa fopbrop_8 fopbrop_9 cop fopbrop_4 sup_set_class fopbrop_5 sup_set_class cop wceq fopbrop_10 fopbrop_11 cop fopbrop_6 sup_set_class fopbrop_7 sup_set_class cop wceq wa fopbrop_0 wa fopbrop_7 wex fopbrop_6 wex fopbrop_5 wex fopbrop_4 wex fopbrop_1 fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_0 fopbrop_1 fopbrop_4 fopbrop_5 fopbrop_6 fopbrop_7 fopbrop_8 fopbrop_9 fopbrop_10 fopbrop_11 fopbrop_13 fopbrop_13 eopbrop_0 copsex4g anbi2d syl5bb fopbrop_8 fopbrop_13 wcel fopbrop_9 fopbrop_13 wcel wa fopbrop_10 fopbrop_13 wcel fopbrop_11 fopbrop_13 wcel wa wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel wa fopbrop_1 fopbrop_8 fopbrop_13 wcel fopbrop_9 fopbrop_13 wcel wa fopbrop_8 fopbrop_9 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_10 fopbrop_13 wcel fopbrop_11 fopbrop_13 wcel wa fopbrop_10 fopbrop_11 cop fopbrop_13 fopbrop_13 cxp wcel fopbrop_8 fopbrop_9 fopbrop_13 fopbrop_13 opelxpi fopbrop_10 fopbrop_11 fopbrop_13 fopbrop_13 opelxpi anim12i biantrurd bitr4d $.
$}
$( The cross product with the empty set is empty.  Part of Theorem 3.13(ii)
       of [Monk1] p. 37.  (Contributed by NM, 4-Jul-1994.) $)
${
	$d x y z A $.
	ixp0r_0 $f set x $.
	ixp0r_1 $f set y $.
	ixp0r_2 $f set z $.
	fxp0r_0 $f class A $.
	xp0r $p |- ( (/) X. A ) = (/) $= ixp0r_2 c0 fxp0r_0 cxp c0 ixp0r_2 sup_set_class c0 fxp0r_0 cxp wcel ixp0r_2 sup_set_class ixp0r_0 sup_set_class ixp0r_1 sup_set_class cop wceq ixp0r_0 sup_set_class c0 wcel ixp0r_1 sup_set_class fxp0r_0 wcel wa wa ixp0r_1 wex ixp0r_0 wex ixp0r_2 sup_set_class c0 wcel ixp0r_0 ixp0r_1 ixp0r_2 sup_set_class c0 fxp0r_0 elxp ixp0r_2 sup_set_class ixp0r_0 sup_set_class ixp0r_1 sup_set_class cop wceq ixp0r_0 sup_set_class c0 wcel ixp0r_1 sup_set_class fxp0r_0 wcel wa wa ixp0r_1 wex ixp0r_0 wex ixp0r_2 sup_set_class c0 wcel ixp0r_2 sup_set_class ixp0r_0 sup_set_class ixp0r_1 sup_set_class cop wceq ixp0r_0 sup_set_class c0 wcel ixp0r_1 sup_set_class fxp0r_0 wcel wa wa ixp0r_1 wex ixp0r_0 ixp0r_2 sup_set_class ixp0r_0 sup_set_class ixp0r_1 sup_set_class cop wceq ixp0r_0 sup_set_class c0 wcel ixp0r_1 sup_set_class fxp0r_0 wcel wa wa ixp0r_1 ixp0r_2 sup_set_class ixp0r_0 sup_set_class ixp0r_1 sup_set_class cop wceq ixp0r_0 sup_set_class c0 wcel ixp0r_1 sup_set_class fxp0r_0 wcel wa wa ixp0r_0 sup_set_class c0 wcel ixp0r_0 sup_set_class noel ixp0r_2 sup_set_class ixp0r_0 sup_set_class ixp0r_1 sup_set_class cop wceq ixp0r_0 sup_set_class c0 wcel ixp0r_1 sup_set_class fxp0r_0 wcel simprl mto nex nex ixp0r_2 sup_set_class noel 2false bitri eqriv $.
$}
$( Ordinal numbers and ordered pairs are disjoint collections.  This
       theorem can be used if we want to extend a set of ordinal numbers or
       ordered pairs with disjoint elements.  See also ~ snsn0non .
       (Contributed by NM, 1-Jun-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	ionxpdisj_0 $f set x $.
	onxpdisj $p |- ( On i^i ( _V X. _V ) ) = (/) $= con0 cvv cvv cxp cin c0 wceq ionxpdisj_0 sup_set_class cvv cvv cxp wcel wn ionxpdisj_0 con0 ionxpdisj_0 con0 cvv cvv cxp disj ionxpdisj_0 sup_set_class con0 wcel ionxpdisj_0 sup_set_class c0 wceq c0 ionxpdisj_0 sup_set_class wcel wo ionxpdisj_0 sup_set_class cvv cvv cxp wcel wn ionxpdisj_0 sup_set_class on0eqel ionxpdisj_0 sup_set_class c0 wceq ionxpdisj_0 sup_set_class cvv cvv cxp wcel wn c0 ionxpdisj_0 sup_set_class wcel ionxpdisj_0 sup_set_class c0 wceq ionxpdisj_0 sup_set_class cvv cvv cxp wcel c0 cvv cvv cxp wcel cvv cvv 0nelxp ionxpdisj_0 sup_set_class c0 cvv cvv cxp eleq1 mtbiri ionxpdisj_0 sup_set_class cvv cvv cxp wcel c0 ionxpdisj_0 sup_set_class wcel cvv cvv ionxpdisj_0 sup_set_class 0nelelxp con2i jaoi syl mprgbir $.
$}
$( The class of ordinal numbers is not equal to the universe.  (Contributed
     by NM, 16-Jun-2007.)  (Proof shortened by Mario Carneiro, 10-Jan-2013.) $)
${
	onnev $p |- On =/= _V $= c0 csn csn con0 wcel wn con0 cvv wne snsn0non c0 csn csn con0 wcel con0 cvv con0 cvv wceq c0 csn csn cvv con0 c0 csn snex con0 cvv wceq id syl5eleqr necon3bi ax-mp $.
$}
$( Equality theorem for the relation predicate.  (Contributed by NM,
     1-Aug-1994.) $)
${
	freleq_0 $f class A $.
	freleq_1 $f class B $.
	releq $p |- ( A = B -> ( Rel A <-> Rel B ) ) $= freleq_0 freleq_1 wceq freleq_0 cvv cvv cxp wss freleq_1 cvv cvv cxp wss freleq_0 wrel freleq_1 wrel freleq_0 freleq_1 cvv cvv cxp sseq1 freleq_0 df-rel freleq_1 df-rel 3bitr4g $.
$}
$( Equality inference for the relation predicate.  (Contributed by NM,
       8-Dec-2006.) $)
${
	freleqi_0 $f class A $.
	freleqi_1 $f class B $.
	ereleqi_0 $e |- A = B $.
	releqi $p |- ( Rel A <-> Rel B ) $= freleqi_0 freleqi_1 wceq freleqi_0 wrel freleqi_1 wrel wb ereleqi_0 freleqi_0 freleqi_1 releq ax-mp $.
$}
$( Equality deduction for the relation predicate.  (Contributed by NM,
       8-Mar-2014.) $)
${
	freleqd_0 $f wff ph $.
	freleqd_1 $f class A $.
	freleqd_2 $f class B $.
	ereleqd_0 $e |- ( ph -> A = B ) $.
	releqd $p |- ( ph -> ( Rel A <-> Rel B ) ) $= freleqd_0 freleqd_1 freleqd_2 wceq freleqd_1 wrel freleqd_2 wrel wb ereleqd_0 freleqd_1 freleqd_2 releq syl $.
$}
$( Bound-variable hypothesis builder for a relation.  (Contributed by NM,
       31-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	fnfrel_0 $f set x $.
	fnfrel_1 $f class A $.
	enfrel_0 $e |- F/_ x A $.
	nfrel $p |- F/ x Rel A $= fnfrel_1 wrel fnfrel_1 cvv cvv cxp wss fnfrel_0 fnfrel_1 df-rel fnfrel_0 fnfrel_1 cvv cvv cxp enfrel_0 fnfrel_0 cvv cvv cxp nfcv nfss nfxfr $.
$}
$( Subclass theorem for relation predicate.  Theorem 2 of [Suppes] p. 58.
     (Contributed by NM, 15-Aug-1994.) $)
${
	frelss_0 $f class A $.
	frelss_1 $f class B $.
	relss $p |- ( A C_ B -> ( Rel B -> Rel A ) ) $= frelss_0 frelss_1 wss frelss_1 cvv cvv cxp wss frelss_0 cvv cvv cxp wss frelss_1 wrel frelss_0 wrel frelss_0 frelss_1 cvv cvv cxp sstr2 frelss_1 df-rel frelss_0 df-rel 3imtr4g $.
$}
$( A subclass relationship depends only on a relation's ordered pairs.
       Theorem 3.2(i) of [Monk1] p. 33.  (Contributed by NM, 2-Aug-1994.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	issrel_0 $f set z $.
	fssrel_0 $f set x $.
	fssrel_1 $f set y $.
	fssrel_2 $f class A $.
	fssrel_3 $f class B $.
	ssrel $p |- ( Rel A -> ( A C_ B <-> A. x A. y ( <. x , y >. e. A -> <. x , y >. e. B ) ) ) $= fssrel_2 wrel fssrel_2 fssrel_3 wss fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal fssrel_2 fssrel_3 wss fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_0 fssrel_1 fssrel_2 fssrel_3 fssrel_0 sup_set_class fssrel_1 sup_set_class cop ssel alrimivv fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal fssrel_2 wrel fssrel_2 fssrel_3 wss fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex wi issrel_0 wal issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi issrel_0 wal fssrel_2 wrel fssrel_2 fssrel_3 wss fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex wi issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi issrel_0 fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex issrel_0 sup_set_class fssrel_3 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi fssrel_1 wal fssrel_0 wal issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi wi fssrel_1 wal fssrel_0 wal issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi wi fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi wi fssrel_0 fssrel_1 issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel wi issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq issrel_0 sup_set_class fssrel_2 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_2 eleq1 issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop fssrel_3 eleq1 imbi12d biimprcd 2alimi issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_3 wcel wi fssrel_0 fssrel_1 19.23vv sylib com23 a2d alimdv fssrel_2 wrel fssrel_2 cvv cvv cxp wss issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class cvv cvv cxp wcel wi issrel_0 wal issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex wi issrel_0 wal fssrel_2 df-rel issrel_0 fssrel_2 cvv cvv cxp dfss2 issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class cvv cvv cxp wcel wi issrel_0 sup_set_class fssrel_2 wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex wi issrel_0 issrel_0 sup_set_class cvv cvv cxp wcel issrel_0 sup_set_class fssrel_0 sup_set_class fssrel_1 sup_set_class cop wceq fssrel_1 wex fssrel_0 wex issrel_0 sup_set_class fssrel_2 wcel fssrel_0 fssrel_1 issrel_0 sup_set_class elvv imbi2i albii 3bitri issrel_0 fssrel_2 fssrel_3 dfss2 3imtr4g com12 impbid2 $.
$}
$( Extensionality principle for relations.  Theorem 3.2(ii) of [Monk1]
       p. 33.  (Contributed by NM, 2-Aug-1994.) $)
${
	$d x y A $.
	$d x y B $.
	feqrel_0 $f set x $.
	feqrel_1 $f set y $.
	feqrel_2 $f class A $.
	feqrel_3 $f class B $.
	eqrel $p |- ( ( Rel A /\ Rel B ) -> ( A = B <-> A. x A. y ( <. x , y >. e. A <-> <. x , y >. e. B ) ) ) $= feqrel_2 wrel feqrel_3 wrel wa feqrel_2 feqrel_3 wss feqrel_3 feqrel_2 wss wa feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_2 wcel feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_3 wcel wi feqrel_1 wal feqrel_0 wal feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_3 wcel feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_2 wcel wi feqrel_1 wal feqrel_0 wal wa feqrel_2 feqrel_3 wceq feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_2 wcel feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_3 wcel wb feqrel_1 wal feqrel_0 wal feqrel_2 wrel feqrel_2 feqrel_3 wss feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_2 wcel feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_3 wcel wi feqrel_1 wal feqrel_0 wal feqrel_3 wrel feqrel_3 feqrel_2 wss feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_3 wcel feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_2 wcel wi feqrel_1 wal feqrel_0 wal feqrel_0 feqrel_1 feqrel_2 feqrel_3 ssrel feqrel_0 feqrel_1 feqrel_3 feqrel_2 ssrel bi2anan9 feqrel_2 feqrel_3 eqss feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_2 wcel feqrel_0 sup_set_class feqrel_1 sup_set_class cop feqrel_3 wcel feqrel_0 feqrel_1 2albiim 3bitr4g $.
$}
$( Inference from subclass principle for relations.  (Contributed by NM,
       31-Mar-1998.) $)
${
	$d x y A $.
	$d x y B $.
	frelssi_0 $f set x $.
	frelssi_1 $f set y $.
	frelssi_2 $f class A $.
	frelssi_3 $f class B $.
	erelssi_0 $e |- Rel A $.
	erelssi_1 $e |- ( <. x , y >. e. A -> <. x , y >. e. B ) $.
	relssi $p |- A C_ B $= frelssi_2 frelssi_3 wss frelssi_0 sup_set_class frelssi_1 sup_set_class cop frelssi_2 wcel frelssi_0 sup_set_class frelssi_1 sup_set_class cop frelssi_3 wcel wi frelssi_1 wal frelssi_0 frelssi_2 wrel frelssi_2 frelssi_3 wss frelssi_0 sup_set_class frelssi_1 sup_set_class cop frelssi_2 wcel frelssi_0 sup_set_class frelssi_1 sup_set_class cop frelssi_3 wcel wi frelssi_1 wal frelssi_0 wal wb erelssi_0 frelssi_0 frelssi_1 frelssi_2 frelssi_3 ssrel ax-mp frelssi_0 sup_set_class frelssi_1 sup_set_class cop frelssi_2 wcel frelssi_0 sup_set_class frelssi_1 sup_set_class cop frelssi_3 wcel wi frelssi_1 erelssi_1 ax-gen mpgbir $.
$}
$( Deduction from subclass principle for relations.  (Contributed by NM,
       11-Sep-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y ph $.
	frelssdv_0 $f wff ph $.
	frelssdv_1 $f set x $.
	frelssdv_2 $f set y $.
	frelssdv_3 $f class A $.
	frelssdv_4 $f class B $.
	erelssdv_0 $e |- ( ph -> Rel A ) $.
	erelssdv_1 $e |- ( ph -> ( <. x , y >. e. A -> <. x , y >. e. B ) ) $.
	relssdv $p |- ( ph -> A C_ B ) $= frelssdv_0 frelssdv_3 frelssdv_4 wss frelssdv_1 sup_set_class frelssdv_2 sup_set_class cop frelssdv_3 wcel frelssdv_1 sup_set_class frelssdv_2 sup_set_class cop frelssdv_4 wcel wi frelssdv_2 wal frelssdv_1 wal frelssdv_0 frelssdv_1 sup_set_class frelssdv_2 sup_set_class cop frelssdv_3 wcel frelssdv_1 sup_set_class frelssdv_2 sup_set_class cop frelssdv_4 wcel wi frelssdv_1 frelssdv_2 erelssdv_1 alrimivv frelssdv_0 frelssdv_3 wrel frelssdv_3 frelssdv_4 wss frelssdv_1 sup_set_class frelssdv_2 sup_set_class cop frelssdv_3 wcel frelssdv_1 sup_set_class frelssdv_2 sup_set_class cop frelssdv_4 wcel wi frelssdv_2 wal frelssdv_1 wal wb erelssdv_0 frelssdv_1 frelssdv_2 frelssdv_3 frelssdv_4 ssrel syl mpbird $.
$}
$( Inference from extensionality principle for relations.  (Contributed by
       FL, 15-Oct-2012.) $)
${
	$d x y A $.
	$d x y B $.
	feqrelriv_0 $f set x $.
	feqrelriv_1 $f set y $.
	feqrelriv_2 $f class A $.
	feqrelriv_3 $f class B $.
	eeqrelriv_0 $e |- ( <. x , y >. e. A <-> <. x , y >. e. B ) $.
	eqrelriv $p |- ( ( Rel A /\ Rel B ) -> A = B ) $= feqrelriv_2 wrel feqrelriv_3 wrel wa feqrelriv_2 feqrelriv_3 wceq feqrelriv_0 sup_set_class feqrelriv_1 sup_set_class cop feqrelriv_2 wcel feqrelriv_0 sup_set_class feqrelriv_1 sup_set_class cop feqrelriv_3 wcel wb feqrelriv_1 wal feqrelriv_0 wal feqrelriv_0 sup_set_class feqrelriv_1 sup_set_class cop feqrelriv_2 wcel feqrelriv_0 sup_set_class feqrelriv_1 sup_set_class cop feqrelriv_3 wcel wb feqrelriv_0 feqrelriv_1 eeqrelriv_0 gen2 feqrelriv_0 feqrelriv_1 feqrelriv_2 feqrelriv_3 eqrel mpbiri $.
$}
$( Inference from extensionality principle for relations.  (Contributed by
       NM, 17-Mar-1995.) $)
${
	$d x y A $.
	$d x y B $.
	feqrelriiv_0 $f set x $.
	feqrelriiv_1 $f set y $.
	feqrelriiv_2 $f class A $.
	feqrelriiv_3 $f class B $.
	eeqrelriiv_0 $e |- Rel A $.
	eeqrelriiv_1 $e |- Rel B $.
	eeqrelriiv_2 $e |- ( <. x , y >. e. A <-> <. x , y >. e. B ) $.
	eqrelriiv $p |- A = B $= feqrelriiv_2 wrel feqrelriiv_3 wrel feqrelriiv_2 feqrelriiv_3 wceq eeqrelriiv_0 eeqrelriiv_1 feqrelriiv_0 feqrelriiv_1 feqrelriiv_2 feqrelriiv_3 eeqrelriiv_2 eqrelriv mp2an $.
$}
$( Inference from extensionality principle for relations.  (Contributed by
       NM, 12-Dec-2006.) $)
${
	$d x y A $.
	$d x y B $.
	feqbrriv_0 $f set x $.
	feqbrriv_1 $f set y $.
	feqbrriv_2 $f class A $.
	feqbrriv_3 $f class B $.
	eeqbrriv_0 $e |- Rel A $.
	eeqbrriv_1 $e |- Rel B $.
	eeqbrriv_2 $e |- ( x A y <-> x B y ) $.
	eqbrriv $p |- A = B $= feqbrriv_0 feqbrriv_1 feqbrriv_2 feqbrriv_3 eeqbrriv_0 eeqbrriv_1 feqbrriv_0 sup_set_class feqbrriv_1 sup_set_class feqbrriv_2 wbr feqbrriv_0 sup_set_class feqbrriv_1 sup_set_class feqbrriv_3 wbr feqbrriv_0 sup_set_class feqbrriv_1 sup_set_class cop feqbrriv_2 wcel feqbrriv_0 sup_set_class feqbrriv_1 sup_set_class cop feqbrriv_3 wcel eeqbrriv_2 feqbrriv_0 sup_set_class feqbrriv_1 sup_set_class feqbrriv_2 df-br feqbrriv_0 sup_set_class feqbrriv_1 sup_set_class feqbrriv_3 df-br 3bitr3i eqrelriiv $.
$}
$( Deduce equality of relations from equivalence of membership.
       (Contributed by Rodolfo Medina, 10-Oct-2010.) $)
${
	$d x y A $.
	$d x y B $.
	$d ph x $.
	$d ph y $.
	feqrelrdv_0 $f wff ph $.
	feqrelrdv_1 $f set x $.
	feqrelrdv_2 $f set y $.
	feqrelrdv_3 $f class A $.
	feqrelrdv_4 $f class B $.
	eeqrelrdv_0 $e |- Rel A $.
	eeqrelrdv_1 $e |- Rel B $.
	eeqrelrdv_2 $e |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) ) $.
	eqrelrdv $p |- ( ph -> A = B ) $= feqrelrdv_0 feqrelrdv_1 sup_set_class feqrelrdv_2 sup_set_class cop feqrelrdv_3 wcel feqrelrdv_1 sup_set_class feqrelrdv_2 sup_set_class cop feqrelrdv_4 wcel wb feqrelrdv_2 wal feqrelrdv_1 wal feqrelrdv_3 feqrelrdv_4 wceq feqrelrdv_0 feqrelrdv_1 sup_set_class feqrelrdv_2 sup_set_class cop feqrelrdv_3 wcel feqrelrdv_1 sup_set_class feqrelrdv_2 sup_set_class cop feqrelrdv_4 wcel wb feqrelrdv_1 feqrelrdv_2 eeqrelrdv_2 alrimivv feqrelrdv_3 wrel feqrelrdv_4 wrel feqrelrdv_3 feqrelrdv_4 wceq feqrelrdv_1 sup_set_class feqrelrdv_2 sup_set_class cop feqrelrdv_3 wcel feqrelrdv_1 sup_set_class feqrelrdv_2 sup_set_class cop feqrelrdv_4 wcel wb feqrelrdv_2 wal feqrelrdv_1 wal wb eeqrelrdv_0 eeqrelrdv_1 feqrelrdv_1 feqrelrdv_2 feqrelrdv_3 feqrelrdv_4 eqrel mp2an sylibr $.
$}
$( Deduction from extensionality principle for relations.  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
${
	$d x y A $.
	$d x y B $.
	$d ph x $.
	$d ph y $.
	feqbrrdv_0 $f wff ph $.
	feqbrrdv_1 $f set x $.
	feqbrrdv_2 $f set y $.
	feqbrrdv_3 $f class A $.
	feqbrrdv_4 $f class B $.
	eeqbrrdv_0 $e |- ( ph -> Rel A ) $.
	eeqbrrdv_1 $e |- ( ph -> Rel B ) $.
	eeqbrrdv_2 $e |- ( ph -> ( x A y <-> x B y ) ) $.
	eqbrrdv $p |- ( ph -> A = B ) $= feqbrrdv_0 feqbrrdv_3 feqbrrdv_4 wceq feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_3 wcel feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_4 wcel wb feqbrrdv_2 wal feqbrrdv_1 wal feqbrrdv_0 feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_3 wcel feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_4 wcel wb feqbrrdv_1 feqbrrdv_2 feqbrrdv_0 feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class feqbrrdv_3 wbr feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class feqbrrdv_4 wbr feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_3 wcel feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_4 wcel eeqbrrdv_2 feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class feqbrrdv_3 df-br feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class feqbrrdv_4 df-br 3bitr3g alrimivv feqbrrdv_0 feqbrrdv_3 wrel feqbrrdv_4 wrel feqbrrdv_3 feqbrrdv_4 wceq feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_3 wcel feqbrrdv_1 sup_set_class feqbrrdv_2 sup_set_class cop feqbrrdv_4 wcel wb feqbrrdv_2 wal feqbrrdv_1 wal wb eeqbrrdv_0 eeqbrrdv_1 feqbrrdv_1 feqbrrdv_2 feqbrrdv_3 feqbrrdv_4 eqrel syl2anc mpbird $.
$}
$( Deduction from extensionality principle for relations.  (Contributed by
       Rodolfo Medina, 10-Oct-2010.) $)
${
	$d x y A $.
	$d x y B $.
	$d ph x $.
	$d ph y $.
	feqbrrdiv_0 $f wff ph $.
	feqbrrdiv_1 $f set x $.
	feqbrrdiv_2 $f set y $.
	feqbrrdiv_3 $f class A $.
	feqbrrdiv_4 $f class B $.
	eeqbrrdiv_0 $e |- Rel A $.
	eeqbrrdiv_1 $e |- Rel B $.
	eeqbrrdiv_2 $e |- ( ph -> ( x A y <-> x B y ) ) $.
	eqbrrdiv $p |- ( ph -> A = B ) $= feqbrrdiv_0 feqbrrdiv_1 feqbrrdiv_2 feqbrrdiv_3 feqbrrdiv_4 eeqbrrdiv_0 eeqbrrdiv_1 feqbrrdiv_0 feqbrrdiv_1 sup_set_class feqbrrdiv_2 sup_set_class feqbrrdiv_3 wbr feqbrrdiv_1 sup_set_class feqbrrdiv_2 sup_set_class feqbrrdiv_4 wbr feqbrrdiv_1 sup_set_class feqbrrdiv_2 sup_set_class cop feqbrrdiv_3 wcel feqbrrdiv_1 sup_set_class feqbrrdiv_2 sup_set_class cop feqbrrdiv_4 wcel eeqbrrdiv_2 feqbrrdiv_1 sup_set_class feqbrrdiv_2 sup_set_class feqbrrdiv_3 df-br feqbrrdiv_1 sup_set_class feqbrrdiv_2 sup_set_class feqbrrdiv_4 df-br 3bitr3g eqrelrdv $.
$}
$( A version of ~ eqrelrdv .  (Contributed by Rodolfo Medina,
       10-Oct-2010.) $)
${
	$d x y A $.
	$d x y B $.
	$d ph x $.
	$d ph y $.
	feqrelrdv2_0 $f wff ph $.
	feqrelrdv2_1 $f set x $.
	feqrelrdv2_2 $f set y $.
	feqrelrdv2_3 $f class A $.
	feqrelrdv2_4 $f class B $.
	eeqrelrdv2_0 $e |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) ) $.
	eqrelrdv2 $p |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B ) $= feqrelrdv2_3 wrel feqrelrdv2_4 wrel wa feqrelrdv2_0 wa feqrelrdv2_3 feqrelrdv2_4 wceq feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_3 wcel feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_4 wcel wb feqrelrdv2_2 wal feqrelrdv2_1 wal feqrelrdv2_0 feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_3 wcel feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_4 wcel wb feqrelrdv2_2 wal feqrelrdv2_1 wal feqrelrdv2_3 wrel feqrelrdv2_4 wrel wa feqrelrdv2_0 feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_3 wcel feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_4 wcel wb feqrelrdv2_1 feqrelrdv2_2 eeqrelrdv2_0 alrimivv adantl feqrelrdv2_3 wrel feqrelrdv2_4 wrel wa feqrelrdv2_3 feqrelrdv2_4 wceq feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_3 wcel feqrelrdv2_1 sup_set_class feqrelrdv2_2 sup_set_class cop feqrelrdv2_4 wcel wb feqrelrdv2_2 wal feqrelrdv2_1 wal wb feqrelrdv2_0 feqrelrdv2_1 feqrelrdv2_2 feqrelrdv2_3 feqrelrdv2_4 eqrel adantr mpbird $.
$}
$( A subclass relationship determined by ordered triples.  Use ~ relrelss
       to express the antecedent in terms of the relation predicate.
       (Contributed by NM, 17-Dec-2008.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	$d w x y z A $.
	$d w x y z B $.
	issrelrel_0 $f set w $.
	fssrelrel_0 $f set x $.
	fssrelrel_1 $f set y $.
	fssrelrel_2 $f set z $.
	fssrelrel_3 $f class A $.
	fssrelrel_4 $f class B $.
	ssrelrel $p |- ( A C_ ( ( _V X. _V ) X. _V ) -> ( A C_ B <-> A. x A. y A. z ( <. <. x , y >. , z >. e. A -> <. <. x , y >. , z >. e. B ) ) ) $= fssrelrel_3 cvv cvv cxp cvv cxp wss fssrelrel_3 fssrelrel_4 wss fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal fssrelrel_3 fssrelrel_4 wss fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_0 fssrelrel_1 fssrelrel_3 fssrelrel_4 wss fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 fssrelrel_3 fssrelrel_4 fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop ssel alrimiv alrimivv fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal fssrelrel_3 cvv cvv cxp cvv cxp wss fssrelrel_3 fssrelrel_4 wss fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class cvv cvv cxp cvv cxp wcel wi issrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi issrelrel_0 wal fssrelrel_3 cvv cvv cxp cvv cxp wss fssrelrel_3 fssrelrel_4 wss fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class cvv cvv cxp cvv cxp wcel wi issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi issrelrel_0 fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class cvv cvv cxp cvv cxp wcel issrelrel_0 sup_set_class fssrelrel_4 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class cvv cvv cxp cvv cxp wcel issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel issrelrel_0 sup_set_class cvv cvv cxp cvv cxp wcel issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq fssrelrel_2 wex fssrelrel_1 wex fssrelrel_0 wex fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi fssrelrel_0 fssrelrel_1 fssrelrel_2 issrelrel_0 sup_set_class elvvv fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq fssrelrel_2 wex issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi wi fssrelrel_1 wal fssrelrel_0 wal issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq fssrelrel_2 wex fssrelrel_1 wex fssrelrel_0 wex issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi wi fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq fssrelrel_2 wex issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi wi fssrelrel_0 fssrelrel_1 fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi fssrelrel_2 wal issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi wi fssrelrel_2 wal issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq fssrelrel_2 wex issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi wi fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi wi fssrelrel_2 issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel wi issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq issrelrel_0 sup_set_class fssrelrel_3 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 wcel issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_3 eleq1 issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop fssrelrel_4 eleq1 imbi12d biimprcd alimi issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi fssrelrel_2 19.23v sylib 2alimi issrelrel_0 sup_set_class fssrelrel_0 sup_set_class fssrelrel_1 sup_set_class cop fssrelrel_2 sup_set_class cop wceq fssrelrel_2 wex issrelrel_0 sup_set_class fssrelrel_3 wcel issrelrel_0 sup_set_class fssrelrel_4 wcel wi fssrelrel_0 fssrelrel_1 19.23vv sylib syl5bi com23 a2d alimdv issrelrel_0 fssrelrel_3 cvv cvv cxp cvv cxp dfss2 issrelrel_0 fssrelrel_3 fssrelrel_4 dfss2 3imtr4g com12 impbid2 $.
$}
$( Extensionality principle for ordered triples (used by 2-place operations
       ~ df-oprab ), analogous to ~ eqrel .  Use ~ relrelss to express the
       antecedent in terms of the relation predicate.  (Contributed by NM,
       17-Dec-2008.) $)
${
	$d x y z A $.
	$d x y z B $.
	feqrelrel_0 $f set x $.
	feqrelrel_1 $f set y $.
	feqrelrel_2 $f set z $.
	feqrelrel_3 $f class A $.
	feqrelrel_4 $f class B $.
	eqrelrel $p |- ( ( A u. B ) C_ ( ( _V X. _V ) X. _V ) -> ( A = B <-> A. x A. y A. z ( <. <. x , y >. , z >. e. A <-> <. <. x , y >. , z >. e. B ) ) ) $= feqrelrel_3 feqrelrel_4 cun cvv cvv cxp cvv cxp wss feqrelrel_3 cvv cvv cxp cvv cxp wss feqrelrel_4 cvv cvv cxp cvv cxp wss wa feqrelrel_3 feqrelrel_4 wceq feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wb feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal wb feqrelrel_3 feqrelrel_4 cvv cvv cxp cvv cxp unss feqrelrel_3 cvv cvv cxp cvv cxp wss feqrelrel_4 cvv cvv cxp cvv cxp wss wa feqrelrel_3 feqrelrel_4 wss feqrelrel_4 feqrelrel_3 wss wa feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal wa feqrelrel_3 feqrelrel_4 wceq feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wb feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal feqrelrel_3 cvv cvv cxp cvv cxp wss feqrelrel_3 feqrelrel_4 wss feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal feqrelrel_4 cvv cvv cxp cvv cxp wss feqrelrel_4 feqrelrel_3 wss feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal feqrelrel_0 feqrelrel_1 feqrelrel_2 feqrelrel_3 feqrelrel_4 ssrelrel feqrelrel_0 feqrelrel_1 feqrelrel_2 feqrelrel_4 feqrelrel_3 ssrelrel bi2anan9 feqrelrel_3 feqrelrel_4 eqss feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wb feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel wi feqrelrel_2 wal feqrelrel_1 wal wa feqrelrel_0 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 wal wa feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wb feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel wi feqrelrel_2 wal feqrelrel_1 wal wa feqrelrel_0 feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_1 feqrelrel_2 2albiim albii feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_4 wcel feqrelrel_0 sup_set_class feqrelrel_1 sup_set_class cop feqrelrel_2 sup_set_class cop feqrelrel_3 wcel wi feqrelrel_2 wal feqrelrel_1 wal feqrelrel_0 19.26 bitri 3bitr4g sylbir $.
$}
$( A member of a relation is an ordered pair.  (Contributed by NM,
       17-Sep-2006.) $)
${
	$d x y A $.
	felrel_0 $f set x $.
	felrel_1 $f set y $.
	felrel_2 $f class A $.
	felrel_3 $f class R $.
	elrel $p |- ( ( Rel R /\ A e. R ) -> E. x E. y A = <. x , y >. ) $= felrel_3 wrel felrel_2 felrel_3 wcel wa felrel_2 cvv cvv cxp wcel felrel_2 felrel_0 sup_set_class felrel_1 sup_set_class cop wceq felrel_1 wex felrel_0 wex felrel_3 wrel felrel_3 cvv cvv cxp felrel_2 felrel_3 wrel felrel_3 cvv cvv cxp wss felrel_3 df-rel biimpi sselda felrel_0 felrel_1 felrel_2 elvv sylib $.
$}
$( A singleton is a relation iff it is an ordered pair.  (Contributed by
       NM, 24-Sep-2013.) $)
${
	frelsn_0 $f class A $.
	erelsn_0 $e |- A e. _V $.
	relsn $p |- ( Rel { A } <-> A e. ( _V X. _V ) ) $= frelsn_0 csn wrel frelsn_0 csn cvv cvv cxp wss frelsn_0 cvv cvv cxp wcel frelsn_0 csn df-rel frelsn_0 cvv cvv cxp erelsn_0 snss bitr4i $.
$}
$( A singleton of an ordered pair is a relation.  (Contributed by NM,
       17-May-1998.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	frelsnop_0 $f class A $.
	frelsnop_1 $f class B $.
	erelsnop_0 $e |- A e. _V $.
	erelsnop_1 $e |- B e. _V $.
	relsnop $p |- Rel { <. A , B >. } $= frelsnop_0 frelsnop_1 cop csn wrel frelsnop_0 frelsnop_1 cop cvv cvv cxp wcel frelsnop_0 frelsnop_1 erelsnop_0 erelsnop_1 opelvv frelsnop_0 frelsnop_1 cop frelsnop_0 frelsnop_1 opex relsn mpbir $.
$}
$( Subset theorem for cross product.  Generalization of Theorem 101 of
       [Suppes] p. 52.  (Contributed by NM, 26-Aug-1995.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	ixpss12_0 $f set x $.
	ixpss12_1 $f set y $.
	fxpss12_0 $f class A $.
	fxpss12_1 $f class B $.
	fxpss12_2 $f class C $.
	fxpss12_3 $f class D $.
	xpss12 $p |- ( ( A C_ B /\ C C_ D ) -> ( A X. C ) C_ ( B X. D ) ) $= fxpss12_0 fxpss12_1 wss fxpss12_2 fxpss12_3 wss wa ixpss12_0 sup_set_class fxpss12_0 wcel ixpss12_1 sup_set_class fxpss12_2 wcel wa ixpss12_0 ixpss12_1 copab ixpss12_0 sup_set_class fxpss12_1 wcel ixpss12_1 sup_set_class fxpss12_3 wcel wa ixpss12_0 ixpss12_1 copab fxpss12_0 fxpss12_2 cxp fxpss12_1 fxpss12_3 cxp fxpss12_0 fxpss12_1 wss fxpss12_2 fxpss12_3 wss wa ixpss12_0 sup_set_class fxpss12_0 wcel ixpss12_1 sup_set_class fxpss12_2 wcel wa ixpss12_0 sup_set_class fxpss12_1 wcel ixpss12_1 sup_set_class fxpss12_3 wcel wa ixpss12_0 ixpss12_1 fxpss12_0 fxpss12_1 wss ixpss12_0 sup_set_class fxpss12_0 wcel ixpss12_0 sup_set_class fxpss12_1 wcel fxpss12_2 fxpss12_3 wss ixpss12_1 sup_set_class fxpss12_2 wcel ixpss12_1 sup_set_class fxpss12_3 wcel fxpss12_0 fxpss12_1 ixpss12_0 sup_set_class ssel fxpss12_2 fxpss12_3 ixpss12_1 sup_set_class ssel im2anan9 ssopab2dv ixpss12_0 ixpss12_1 fxpss12_0 fxpss12_2 df-xp ixpss12_0 ixpss12_1 fxpss12_1 fxpss12_3 df-xp 3sstr4g $.
$}
$( A cross product is included in the ordered pair universe.  Exercise 3 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 2-Aug-1994.) $)
${
	fxpss_0 $f class A $.
	fxpss_1 $f class B $.
	xpss $p |- ( A X. B ) C_ ( _V X. _V ) $= fxpss_0 cvv wss fxpss_1 cvv wss fxpss_0 fxpss_1 cxp cvv cvv cxp wss fxpss_0 ssv fxpss_1 ssv fxpss_0 cvv fxpss_1 cvv xpss12 mp2an $.
$}
$( A cross product is a relation.  Theorem 3.13(i) of [Monk1] p. 37.
     (Contributed by NM, 2-Aug-1994.) $)
${
	frelxp_0 $f class A $.
	frelxp_1 $f class B $.
	relxp $p |- Rel ( A X. B ) $= frelxp_0 frelxp_1 cxp wrel frelxp_0 frelxp_1 cxp cvv cvv cxp wss frelxp_0 frelxp_1 xpss frelxp_0 frelxp_1 cxp df-rel mpbir $.
$}
$( Subset relation for cross product.  (Contributed by Jeff Hankins,
     30-Aug-2009.) $)
${
	fxpss1_0 $f class A $.
	fxpss1_1 $f class B $.
	fxpss1_2 $f class C $.
	xpss1 $p |- ( A C_ B -> ( A X. C ) C_ ( B X. C ) ) $= fxpss1_0 fxpss1_1 wss fxpss1_2 fxpss1_2 wss fxpss1_0 fxpss1_2 cxp fxpss1_1 fxpss1_2 cxp wss fxpss1_2 ssid fxpss1_0 fxpss1_1 fxpss1_2 fxpss1_2 xpss12 mpan2 $.
$}
$( Subset relation for cross product.  (Contributed by Jeff Hankins,
     30-Aug-2009.) $)
${
	fxpss2_0 $f class A $.
	fxpss2_1 $f class B $.
	fxpss2_2 $f class C $.
	xpss2 $p |- ( A C_ B -> ( C X. A ) C_ ( C X. B ) ) $= fxpss2_2 fxpss2_2 wss fxpss2_0 fxpss2_1 wss fxpss2_2 fxpss2_0 cxp fxpss2_2 fxpss2_1 cxp wss fxpss2_2 ssid fxpss2_2 fxpss2_2 fxpss2_0 fxpss2_1 xpss12 mpan $.
$}
$( A cross product is included in the power of the power of the union of
       its arguments.  (Contributed by NM, 13-Sep-2006.) $)
${
	$d A x y z $.
	$d B x y z $.
	ixpsspw_0 $f set x $.
	ixpsspw_1 $f set y $.
	ixpsspw_2 $f set z $.
	fxpsspw_0 $f class A $.
	fxpsspw_1 $f class B $.
	xpsspw $p |- ( A X. B ) C_ ~P ~P ( A u. B ) $= ixpsspw_2 fxpsspw_0 fxpsspw_1 cxp fxpsspw_0 fxpsspw_1 cun cpw cpw ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cxp wcel ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw cpw wcel ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cxp wcel ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop wceq ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa wa ixpsspw_1 wex ixpsspw_0 wex ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_0 ixpsspw_1 ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 elxpi ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop wceq ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa wa ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_0 ixpsspw_1 ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop wceq ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop ixpsspw_0 sup_set_class csn ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr cpr fxpsspw_0 fxpsspw_1 cun cpw ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class ixpsspw_0 vex ixpsspw_1 vex dfop ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_2 ixpsspw_0 sup_set_class csn ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr cpr fxpsspw_0 fxpsspw_1 cun cpw ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class csn wceq ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr wceq wo ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun wss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class csn ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr cpr wcel ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw wcel ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class csn wceq ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun wss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr wceq ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun wss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class csn wceq ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_1 sup_set_class fxpsspw_1 wcel ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_0 sup_set_class csn fxpsspw_0 wss ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_0 sup_set_class fxpsspw_0 snssi ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 ssun3 syl adantr ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun sseq1 syl5ibrcom ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun wss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr wceq ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr fxpsspw_0 fxpsspw_1 cun wss ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr ixpsspw_0 sup_set_class csn ixpsspw_1 sup_set_class csn cun fxpsspw_0 fxpsspw_1 cun ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class df-pr ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_1 sup_set_class fxpsspw_1 wcel wa ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_1 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss wa ixpsspw_0 sup_set_class csn ixpsspw_1 sup_set_class csn cun fxpsspw_0 fxpsspw_1 cun wss ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_1 sup_set_class fxpsspw_1 wcel ixpsspw_1 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_0 sup_set_class fxpsspw_0 wcel ixpsspw_0 sup_set_class csn fxpsspw_0 wss ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_0 sup_set_class fxpsspw_0 snssi ixpsspw_0 sup_set_class csn fxpsspw_0 fxpsspw_1 ssun3 syl ixpsspw_1 sup_set_class fxpsspw_1 wcel ixpsspw_1 sup_set_class csn fxpsspw_1 wss ixpsspw_1 sup_set_class csn fxpsspw_0 fxpsspw_1 cun wss ixpsspw_1 sup_set_class fxpsspw_1 snssi ixpsspw_1 sup_set_class csn fxpsspw_1 fxpsspw_0 ssun4 syl anim12i ixpsspw_0 sup_set_class csn ixpsspw_1 sup_set_class csn fxpsspw_0 fxpsspw_1 cun unss sylib syl5eqss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr fxpsspw_0 fxpsspw_1 cun sseq1 syl5ibrcom jaod ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class csn ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cpr ixpsspw_2 vex elpr ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun ixpsspw_2 vex elpw 3imtr4g ssrdv syl5eqss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop wceq ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop fxpsspw_0 fxpsspw_1 cun cpw wss ixpsspw_2 sup_set_class ixpsspw_0 sup_set_class ixpsspw_1 sup_set_class cop fxpsspw_0 fxpsspw_1 cun cpw sseq1 biimpar sylan2 exlimivv syl ixpsspw_2 sup_set_class fxpsspw_0 fxpsspw_1 cun cpw ixpsspw_2 vex elpw sylibr ssriv $.
$}
$( A cross product is included in the power of the power of the union of
       its arguments.  (Contributed by NM, 13-Sep-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	$d x y A $.
	$d x y B $.
	ixpsspwOLD_0 $f set x $.
	ixpsspwOLD_1 $f set y $.
	fxpsspwOLD_0 $f class A $.
	fxpsspwOLD_1 $f class B $.
	xpsspwOLD $p |- ( A X. B ) C_ ~P ~P ( A u. B ) $= ixpsspwOLD_0 ixpsspwOLD_1 fxpsspwOLD_0 fxpsspwOLD_1 cxp fxpsspwOLD_0 fxpsspwOLD_1 cun cpw cpw fxpsspwOLD_0 fxpsspwOLD_1 relxp ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cop fxpsspwOLD_0 fxpsspwOLD_1 cxp wcel ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel wa ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cop fxpsspwOLD_0 fxpsspwOLD_1 cun cpw cpw wcel ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class fxpsspwOLD_0 fxpsspwOLD_1 opelxp ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel wa ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel wa ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cop fxpsspwOLD_0 fxpsspwOLD_1 cun cpw cpw wcel ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel wa ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 wss ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 snssi ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 ssun3 syl ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun ixpsspwOLD_0 sup_set_class snex elpw sylibr adantr ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel wa ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel wa ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_1 sup_set_class csn cun fxpsspwOLD_0 fxpsspwOLD_1 cun ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class df-pr ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel wa ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_1 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss wa ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_1 sup_set_class csn cun fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel ixpsspwOLD_1 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 wcel ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 wss ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_0 sup_set_class fxpsspwOLD_0 snssi ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 ssun3 syl ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 wcel ixpsspwOLD_1 sup_set_class csn fxpsspwOLD_1 wss ixpsspwOLD_1 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun wss ixpsspwOLD_1 sup_set_class fxpsspwOLD_1 snssi ixpsspwOLD_1 sup_set_class csn fxpsspwOLD_1 fxpsspwOLD_0 ssun4 syl anim12i ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_1 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun unss sylib syl5eqss ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun ixpsspwOLD_0 ixpsspwOLD_1 zfpair2 elpw sylibr jca ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw cpw wcel ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wss ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cop fxpsspwOLD_0 fxpsspwOLD_1 cun cpw cpw wcel ixpsspwOLD_0 sup_set_class csn fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw wcel wa ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr prex elpw ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cop ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw cpw ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class ixpsspwOLD_0 vex ixpsspwOLD_1 vex dfop eleq1i ixpsspwOLD_0 sup_set_class csn ixpsspwOLD_0 sup_set_class ixpsspwOLD_1 sup_set_class cpr fxpsspwOLD_0 fxpsspwOLD_1 cun cpw ixpsspwOLD_0 sup_set_class snex ixpsspwOLD_0 ixpsspwOLD_1 zfpair2 prss 3bitr4ri sylib sylbi relssi $.
$}
$( The double class union of a cross product is included in the union of its
     arguments.  (Contributed by NM, 16-Sep-2006.) $)
${
	funixpss_0 $f class A $.
	funixpss_1 $f class B $.
	unixpss $p |- U. U. ( A X. B ) C_ ( A u. B ) $= funixpss_0 funixpss_1 cxp cuni cuni funixpss_0 funixpss_1 cun cpw cuni funixpss_0 funixpss_1 cun funixpss_0 funixpss_1 cxp cuni funixpss_0 funixpss_1 cun cpw wss funixpss_0 funixpss_1 cxp cuni cuni funixpss_0 funixpss_1 cun cpw cuni wss funixpss_0 funixpss_1 cxp cuni funixpss_0 funixpss_1 cun cpw cpw cuni funixpss_0 funixpss_1 cun cpw funixpss_0 funixpss_1 cxp funixpss_0 funixpss_1 cun cpw cpw wss funixpss_0 funixpss_1 cxp cuni funixpss_0 funixpss_1 cun cpw cpw cuni wss funixpss_0 funixpss_1 xpsspw funixpss_0 funixpss_1 cxp funixpss_0 funixpss_1 cun cpw cpw uniss ax-mp funixpss_0 funixpss_1 cun cpw unipw sseqtri funixpss_0 funixpss_1 cxp cuni funixpss_0 funixpss_1 cun cpw uniss ax-mp funixpss_0 funixpss_1 cun unipw sseqtri $.
$}
$( The cross product of two sets is a set.  Proposition 6.2 of
     [TakeutiZaring] p. 23.  See also ~ xpexgALT .  (Contributed by NM,
     14-Aug-1994.) $)
${
	fxpexg_0 $f class A $.
	fxpexg_1 $f class B $.
	fxpexg_2 $f class V $.
	fxpexg_3 $f class W $.
	xpexg $p |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V ) $= fxpexg_0 fxpexg_2 wcel fxpexg_1 fxpexg_3 wcel wa fxpexg_0 fxpexg_1 cxp fxpexg_0 fxpexg_1 cun cpw cpw wss fxpexg_0 fxpexg_1 cun cpw cpw cvv wcel fxpexg_0 fxpexg_1 cxp cvv wcel fxpexg_0 fxpexg_1 xpsspw fxpexg_0 fxpexg_2 wcel fxpexg_1 fxpexg_3 wcel wa fxpexg_0 fxpexg_1 cun cvv wcel fxpexg_0 fxpexg_1 cun cpw cvv wcel fxpexg_0 fxpexg_1 cun cpw cpw cvv wcel fxpexg_0 fxpexg_1 fxpexg_2 fxpexg_3 unexg fxpexg_0 fxpexg_1 cun cvv pwexg fxpexg_0 fxpexg_1 cun cpw cvv pwexg 3syl fxpexg_0 fxpexg_1 cxp fxpexg_0 fxpexg_1 cun cpw cpw cvv ssexg sylancr $.
$}
$( The cross product of two sets is a set.  Proposition 6.2 of
       [TakeutiZaring] p. 23.  (Contributed by NM, 14-Aug-1994.) $)
${
	fxpex_0 $f class A $.
	fxpex_1 $f class B $.
	expex_0 $e |- A e. _V $.
	expex_1 $e |- B e. _V $.
	xpex $p |- ( A X. B ) e. _V $= fxpex_0 cvv wcel fxpex_1 cvv wcel fxpex_0 fxpex_1 cxp cvv wcel expex_0 expex_1 fxpex_0 fxpex_1 cvv cvv xpexg mp2an $.
$}
$( The union of two relations is a relation.  Compare Exercise 5 of
     [TakeutiZaring] p. 25.  (Contributed by NM, 12-Aug-1994.) $)
${
	frelun_0 $f class A $.
	frelun_1 $f class B $.
	relun $p |- ( Rel ( A u. B ) <-> ( Rel A /\ Rel B ) ) $= frelun_0 cvv cvv cxp wss frelun_1 cvv cvv cxp wss wa frelun_0 frelun_1 cun cvv cvv cxp wss frelun_0 wrel frelun_1 wrel wa frelun_0 frelun_1 cun wrel frelun_0 frelun_1 cvv cvv cxp unss frelun_0 wrel frelun_0 cvv cvv cxp wss frelun_1 wrel frelun_1 cvv cvv cxp wss frelun_0 df-rel frelun_1 df-rel anbi12i frelun_0 frelun_1 cun df-rel 3bitr4ri $.
$}
$( The intersection with a relation is a relation.  (Contributed by NM,
     16-Aug-1994.) $)
${
	frelin1_0 $f class A $.
	frelin1_1 $f class B $.
	relin1 $p |- ( Rel A -> Rel ( A i^i B ) ) $= frelin1_0 frelin1_1 cin frelin1_0 wss frelin1_0 wrel frelin1_0 frelin1_1 cin wrel wi frelin1_0 frelin1_1 inss1 frelin1_0 frelin1_1 cin frelin1_0 relss ax-mp $.
$}
$( The intersection with a relation is a relation.  (Contributed by NM,
     17-Jan-2006.) $)
${
	frelin2_0 $f class A $.
	frelin2_1 $f class B $.
	relin2 $p |- ( Rel B -> Rel ( A i^i B ) ) $= frelin2_0 frelin2_1 cin frelin2_1 wss frelin2_1 wrel frelin2_0 frelin2_1 cin wrel wi frelin2_0 frelin2_1 inss2 frelin2_0 frelin2_1 cin frelin2_1 relss ax-mp $.
$}
$( A difference cutting down a relation is a relation.  (Contributed by NM,
     31-Mar-1998.) $)
${
	freldif_0 $f class A $.
	freldif_1 $f class B $.
	reldif $p |- ( Rel A -> Rel ( A \ B ) ) $= freldif_0 freldif_1 cdif freldif_0 wss freldif_0 wrel freldif_0 freldif_1 cdif wrel wi freldif_0 freldif_1 difss freldif_0 freldif_1 cdif freldif_0 relss ax-mp $.
$}
$( An indexed union is a relation iff each member of its indexed family is
       a relation.  (Contributed by NM, 19-Dec-2008.) $)
${
	$d y A $.
	$d y B $.
	$d x y $.
	ireliun_0 $f set y $.
	freliun_0 $f set x $.
	freliun_1 $f class A $.
	freliun_2 $f class B $.
	reliun $p |- ( Rel U_ x e. A B <-> A. x e. A Rel B ) $= freliun_0 freliun_1 freliun_2 ciun wrel ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 cab wrel ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 cab cvv cvv cxp wss freliun_2 wrel freliun_0 freliun_1 wral freliun_0 freliun_1 freliun_2 ciun ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 cab freliun_0 ireliun_0 freliun_1 freliun_2 df-iun releqi ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 cab df-rel ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 cab cvv cvv cxp wss ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 sup_set_class cvv cvv cxp wcel wi ireliun_0 wal freliun_2 wrel freliun_0 freliun_1 wral ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 cvv cvv cxp abss freliun_2 wrel freliun_0 freliun_1 wral ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel wi ireliun_0 wal freliun_0 freliun_1 wral ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel wi freliun_0 freliun_1 wral ireliun_0 wal ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 sup_set_class cvv cvv cxp wcel wi ireliun_0 wal freliun_2 wrel ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel wi ireliun_0 wal freliun_0 freliun_1 freliun_2 wrel freliun_2 cvv cvv cxp wss ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel wi ireliun_0 wal freliun_2 df-rel ireliun_0 freliun_2 cvv cvv cxp dfss2 bitri ralbii ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel wi freliun_0 ireliun_0 freliun_1 ralcom4 ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel wi freliun_0 freliun_1 wral ireliun_0 sup_set_class freliun_2 wcel freliun_0 freliun_1 wrex ireliun_0 sup_set_class cvv cvv cxp wcel wi ireliun_0 ireliun_0 sup_set_class freliun_2 wcel ireliun_0 sup_set_class cvv cvv cxp wcel freliun_0 freliun_1 r19.23v albii 3bitri bitr4i 3bitri $.
$}
$( An indexed intersection is a relation if at least one of the member of the
     indexed family is a relation.  (Contributed by NM, 8-Mar-2014.) $)
${
	freliin_0 $f set x $.
	freliin_1 $f class A $.
	freliin_2 $f class B $.
	reliin $p |- ( E. x e. A Rel B -> Rel |^|_ x e. A B ) $= freliin_2 cvv cvv cxp wss freliin_0 freliin_1 wrex freliin_0 freliin_1 freliin_2 ciin cvv cvv cxp wss freliin_2 wrel freliin_0 freliin_1 wrex freliin_0 freliin_1 freliin_2 ciin wrel freliin_0 freliin_1 freliin_2 cvv cvv cxp iinss freliin_2 wrel freliin_2 cvv cvv cxp wss freliin_0 freliin_1 freliin_2 df-rel rexbii freliin_0 freliin_1 freliin_2 ciin df-rel 3imtr4i $.
$}
$( The union of a class is a relation iff any member is a relation.
       Exercise 6 of [TakeutiZaring] p. 25 and its converse.  (Contributed by
       NM, 13-Aug-2004.) $)
${
	$d x A $.
	freluni_0 $f set x $.
	freluni_1 $f class A $.
	reluni $p |- ( Rel U. A <-> A. x e. A Rel x ) $= freluni_1 cuni wrel freluni_0 freluni_1 freluni_0 sup_set_class ciun wrel freluni_0 sup_set_class wrel freluni_0 freluni_1 wral freluni_1 cuni freluni_0 freluni_1 freluni_0 sup_set_class ciun freluni_0 freluni_1 uniiun releqi freluni_0 freluni_1 freluni_0 sup_set_class reliun bitri $.
$}
$( The intersection of a class is a relation if at least one member is a
       relation.  (Contributed by NM, 8-Mar-2014.) $)
${
	$d x A $.
	frelint_0 $f set x $.
	frelint_1 $f class A $.
	relint $p |- ( E. x e. A Rel x -> Rel |^| A ) $= frelint_0 sup_set_class wrel frelint_0 frelint_1 wrex frelint_0 frelint_1 frelint_0 sup_set_class ciin wrel frelint_1 cint wrel frelint_0 frelint_1 frelint_0 sup_set_class reliin frelint_1 cint frelint_0 frelint_1 frelint_0 sup_set_class ciin frelint_0 frelint_1 intiin releqi sylibr $.
$}
$( The empty set is a relation.  (Contributed by NM, 26-Apr-1998.) $)
${
	rel0 $p |- Rel (/) $= c0 wrel c0 cvv cvv cxp wss cvv cvv cxp 0ss c0 df-rel mpbir $.
$}
$( A class of ordered pairs is a relation.  (Contributed by Mario Carneiro,
       21-Dec-2013.) $)
${
	$d ph z $.
	$d x z $.
	$d y z $.
	irelopabi_0 $f set z $.
	frelopabi_0 $f wff ph $.
	frelopabi_1 $f set x $.
	frelopabi_2 $f set y $.
	frelopabi_3 $f class A $.
	erelopabi_0 $e |- A = { <. x , y >. | ph } $.
	relopabi $p |- Rel A $= frelopabi_3 wrel frelopabi_3 cvv cvv cxp wss frelopabi_3 irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop wceq frelopabi_0 wa frelopabi_2 wex frelopabi_1 wex irelopabi_0 cab cvv cvv cxp frelopabi_3 frelopabi_0 frelopabi_1 frelopabi_2 copab irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop wceq frelopabi_0 wa frelopabi_2 wex frelopabi_1 wex irelopabi_0 cab erelopabi_0 frelopabi_0 frelopabi_1 frelopabi_2 irelopabi_0 df-opab eqtri irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop wceq frelopabi_0 wa frelopabi_2 wex frelopabi_1 wex irelopabi_0 cvv cvv cxp irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop wceq frelopabi_0 wa irelopabi_0 sup_set_class cvv cvv cxp wcel frelopabi_1 frelopabi_2 irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop wceq irelopabi_0 sup_set_class cvv cvv cxp wcel frelopabi_0 irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop wceq irelopabi_0 sup_set_class cvv cvv cxp wcel frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop cvv cvv cxp wcel frelopabi_1 sup_set_class frelopabi_2 sup_set_class frelopabi_1 vex frelopabi_2 vex opelvv irelopabi_0 sup_set_class frelopabi_1 sup_set_class frelopabi_2 sup_set_class cop cvv cvv cxp eleq1 mpbiri adantr exlimivv abssi eqsstri frelopabi_3 df-rel mpbir $.
$}
$( A class of ordered pairs is a relation.  (Contributed by NM, 8-Mar-1995.)
     (Unnecessary distinct variable restrictions were removed by Alan Sare,
     9-Jul-2013.)  (Proof shortened by Mario Carneiro, 21-Dec-2013.) $)
${
	frelopab_0 $f wff ph $.
	frelopab_1 $f set x $.
	frelopab_2 $f set y $.
	relopab $p |- Rel { <. x , y >. | ph } $= frelopab_0 frelopab_1 frelopab_2 frelopab_0 frelopab_1 frelopab_2 copab frelopab_0 frelopab_1 frelopab_2 copab eqid relopabi $.
$}
$( The identity relation is a relation.  Part of Exercise 4.12(p) of
       [Mendelson] p. 235.  (Contributed by NM, 26-Apr-1998.)  (Revised by
       Mario Carneiro, 21-Dec-2013.) $)
${
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	ireli_0 $f set x $.
	ireli_1 $f set y $.
	reli $p |- Rel _I $= ireli_0 sup_set_class ireli_1 sup_set_class wceq ireli_0 ireli_1 cid ireli_0 ireli_1 dfid3 relopabi $.
$}
$( The membership relation is a relation.  (Contributed by NM,
       26-Apr-1998.)  (Revised by Mario Carneiro, 21-Dec-2013.) $)
${
	$d x y $.
	$d x y $.
	$d x y $.
	$d x y $.
	irele_0 $f set x $.
	irele_1 $f set y $.
	rele $p |- Rel _E $= irele_0 sup_set_class irele_1 sup_set_class wcel irele_0 irele_1 cep irele_0 irele_1 df-eprel relopabi $.
$}
$( A relation expressed as an ordered pair abstraction.  (Contributed by
       NM, 11-Dec-2006.) $)
${
	$d w x y z A $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d z w $.
	$d z w $.
	iopabid2_0 $f set z $.
	iopabid2_1 $f set w $.
	fopabid2_0 $f set x $.
	fopabid2_1 $f set y $.
	fopabid2_2 $f class A $.
	opabid2 $p |- ( Rel A -> { <. x , y >. | <. x , y >. e. A } = A ) $= fopabid2_2 wrel fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab fopabid2_2 wceq iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab wcel iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_2 wcel wb iopabid2_1 wal iopabid2_0 wal iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab wcel iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_2 wcel wb iopabid2_0 iopabid2_1 fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel iopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 iopabid2_0 sup_set_class iopabid2_1 sup_set_class iopabid2_0 vex iopabid2_1 vex fopabid2_0 sup_set_class iopabid2_0 sup_set_class wceq fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop iopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 fopabid2_0 sup_set_class iopabid2_0 sup_set_class fopabid2_1 sup_set_class opeq1 eleq1d fopabid2_1 sup_set_class iopabid2_1 sup_set_class wceq iopabid2_0 sup_set_class fopabid2_1 sup_set_class cop iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_2 fopabid2_1 sup_set_class iopabid2_1 sup_set_class iopabid2_0 sup_set_class opeq2 eleq1d opelopab gen2 fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab wrel fopabid2_2 wrel fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab fopabid2_2 wceq iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab wcel iopabid2_0 sup_set_class iopabid2_1 sup_set_class cop fopabid2_2 wcel wb iopabid2_1 wal iopabid2_0 wal wb fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 relopab iopabid2_0 iopabid2_1 fopabid2_0 sup_set_class fopabid2_1 sup_set_class cop fopabid2_2 wcel fopabid2_0 fopabid2_1 copab fopabid2_2 eqrel mpan mpbiri $.
$}
$( Intersection of two ordered pair class abstractions.  (Contributed by
       NM, 30-Sep-2002.) $)
${
	$d w x y z $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d ph z w $.
	$d ps z w $.
	iinopab_0 $f set z $.
	iinopab_1 $f set w $.
	finopab_0 $f wff ph $.
	finopab_1 $f wff ps $.
	finopab_2 $f set x $.
	finopab_3 $f set y $.
	inopab $p |- ( { <. x , y >. | ph } i^i { <. x , y >. | ps } ) = { <. x , y >. | ( ph /\ ps ) } $= iinopab_0 iinopab_1 finopab_0 finopab_2 finopab_3 copab finopab_1 finopab_2 finopab_3 copab cin finopab_0 finopab_1 wa finopab_2 finopab_3 copab finopab_0 finopab_2 finopab_3 copab wrel finopab_0 finopab_2 finopab_3 copab finopab_1 finopab_2 finopab_3 copab cin wrel finopab_0 finopab_2 finopab_3 relopab finopab_0 finopab_2 finopab_3 copab finopab_1 finopab_2 finopab_3 copab relin1 ax-mp finopab_0 finopab_1 wa finopab_2 finopab_3 relopab iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_0 finopab_2 finopab_3 copab wcel iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_1 finopab_2 finopab_3 copab wcel wa finopab_0 finopab_1 wa finopab_2 iinopab_0 wsb finopab_3 iinopab_1 wsb iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_0 finopab_2 finopab_3 copab finopab_1 finopab_2 finopab_3 copab cin wcel iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_0 finopab_1 wa finopab_2 finopab_3 copab wcel finopab_0 finopab_2 iinopab_0 wsb finopab_1 finopab_2 iinopab_0 wsb wa finopab_3 iinopab_1 wsb finopab_0 finopab_2 iinopab_0 wsb finopab_3 iinopab_1 wsb finopab_1 finopab_2 iinopab_0 wsb finopab_3 iinopab_1 wsb wa finopab_0 finopab_1 wa finopab_2 iinopab_0 wsb finopab_3 iinopab_1 wsb iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_0 finopab_2 finopab_3 copab wcel iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_1 finopab_2 finopab_3 copab wcel wa finopab_0 finopab_2 iinopab_0 wsb finopab_1 finopab_2 iinopab_0 wsb finopab_3 iinopab_1 sban finopab_0 finopab_1 wa finopab_2 iinopab_0 wsb finopab_0 finopab_2 iinopab_0 wsb finopab_1 finopab_2 iinopab_0 wsb wa finopab_3 iinopab_1 finopab_0 finopab_1 finopab_2 iinopab_0 sban sbbii iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_0 finopab_2 finopab_3 copab wcel finopab_0 finopab_2 iinopab_0 wsb finopab_3 iinopab_1 wsb iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_1 finopab_2 finopab_3 copab wcel finopab_1 finopab_2 iinopab_0 wsb finopab_3 iinopab_1 wsb finopab_0 finopab_2 finopab_3 iinopab_0 iinopab_1 opelopabsbOLD finopab_1 finopab_2 finopab_3 iinopab_0 iinopab_1 opelopabsbOLD anbi12i 3bitr4ri iinopab_0 sup_set_class iinopab_1 sup_set_class cop finopab_0 finopab_2 finopab_3 copab finopab_1 finopab_2 finopab_3 copab elin finopab_0 finopab_1 wa finopab_2 finopab_3 iinopab_0 iinopab_1 opelopabsbOLD 3bitr4i eqrelriiv $.
$}
$( The difference of two ordered-pair abstractions.  (Contributed by Stefan
       O'Rear, 17-Jan-2015.) $)
${
	$d w x y z $.
	$d x y $.
	$d x y $.
	$d x y $.
	$d ph z w $.
	$d ps z w $.
	idifopab_0 $f set z $.
	idifopab_1 $f set w $.
	fdifopab_0 $f wff ph $.
	fdifopab_1 $f wff ps $.
	fdifopab_2 $f set x $.
	fdifopab_3 $f set y $.
	difopab $p |- ( { <. x , y >. | ph } \ { <. x , y >. | ps } ) = { <. x , y >. | ( ph /\ -. ps ) } $= idifopab_0 idifopab_1 fdifopab_0 fdifopab_2 fdifopab_3 copab fdifopab_1 fdifopab_2 fdifopab_3 copab cdif fdifopab_0 fdifopab_1 wn wa fdifopab_2 fdifopab_3 copab fdifopab_0 fdifopab_2 fdifopab_3 copab wrel fdifopab_0 fdifopab_2 fdifopab_3 copab fdifopab_1 fdifopab_2 fdifopab_3 copab cdif wrel fdifopab_0 fdifopab_2 fdifopab_3 relopab fdifopab_0 fdifopab_2 fdifopab_3 copab fdifopab_1 fdifopab_2 fdifopab_3 copab reldif ax-mp fdifopab_0 fdifopab_1 wn wa fdifopab_2 fdifopab_3 relopab idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_0 fdifopab_2 fdifopab_3 copab wcel idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_1 fdifopab_2 fdifopab_3 copab wcel wn wa fdifopab_0 fdifopab_1 wn wa fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_0 fdifopab_2 fdifopab_3 copab fdifopab_1 fdifopab_2 fdifopab_3 copab cdif wcel idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_0 fdifopab_1 wn wa fdifopab_2 fdifopab_3 copab wcel fdifopab_0 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc wa fdifopab_2 idifopab_0 sup_set_class wsbc fdifopab_0 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc wa fdifopab_0 fdifopab_1 wn wa fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_0 fdifopab_2 fdifopab_3 copab wcel idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_1 fdifopab_2 fdifopab_3 copab wcel wn wa fdifopab_0 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class sbcan fdifopab_0 fdifopab_1 wn wa fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_0 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc wa fdifopab_2 idifopab_0 sup_set_class fdifopab_0 fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class sbcan sbcbii idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_0 fdifopab_2 fdifopab_3 copab wcel fdifopab_0 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_1 fdifopab_2 fdifopab_3 copab wcel wn fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc fdifopab_0 fdifopab_2 fdifopab_3 idifopab_0 sup_set_class idifopab_1 sup_set_class opelopabsb fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc wn fdifopab_2 idifopab_0 sup_set_class wsbc fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc wn fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_1 fdifopab_2 fdifopab_3 copab wcel wn idifopab_0 sup_set_class cvv wcel fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc wn fdifopab_2 idifopab_0 sup_set_class wsbc fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc wn wb idifopab_0 vex fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class cvv sbcng ax-mp fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc wn fdifopab_2 idifopab_0 sup_set_class idifopab_1 sup_set_class cvv wcel fdifopab_1 wn fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc wn wb idifopab_1 vex fdifopab_1 fdifopab_3 idifopab_1 sup_set_class cvv sbcng ax-mp sbcbii idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_1 fdifopab_2 fdifopab_3 copab wcel fdifopab_1 fdifopab_3 idifopab_1 sup_set_class wsbc fdifopab_2 idifopab_0 sup_set_class wsbc fdifopab_1 fdifopab_2 fdifopab_3 idifopab_0 sup_set_class idifopab_1 sup_set_class opelopabsb notbii 3bitr4ri anbi12i 3bitr4ri idifopab_0 sup_set_class idifopab_1 sup_set_class cop fdifopab_0 fdifopab_2 fdifopab_3 copab fdifopab_1 fdifopab_2 fdifopab_3 copab eldif fdifopab_0 fdifopab_1 wn wa fdifopab_2 fdifopab_3 idifopab_0 sup_set_class idifopab_1 sup_set_class opelopabsb 3bitr4i eqrelriiv $.
$}
$( The intersection of two cross products.  Exercise 9 of [TakeutiZaring]
       p. 25.  (Contributed by NM, 3-Aug-1994.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	$d x y D $.
	iinxp_0 $f set x $.
	iinxp_1 $f set y $.
	finxp_0 $f class A $.
	finxp_1 $f class B $.
	finxp_2 $f class C $.
	finxp_3 $f class D $.
	inxp $p |- ( ( A X. B ) i^i ( C X. D ) ) = ( ( A i^i C ) X. ( B i^i D ) ) $= iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 iinxp_1 copab iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa iinxp_0 iinxp_1 copab cin iinxp_0 sup_set_class finxp_0 finxp_2 cin wcel iinxp_1 sup_set_class finxp_1 finxp_3 cin wcel wa iinxp_0 iinxp_1 copab finxp_0 finxp_1 cxp finxp_2 finxp_3 cxp cin finxp_0 finxp_2 cin finxp_1 finxp_3 cin cxp iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 iinxp_1 copab iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa iinxp_0 iinxp_1 copab cin iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa wa iinxp_0 iinxp_1 copab iinxp_0 sup_set_class finxp_0 finxp_2 cin wcel iinxp_1 sup_set_class finxp_1 finxp_3 cin wcel wa iinxp_0 iinxp_1 copab iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa iinxp_0 iinxp_1 inopab iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa wa iinxp_0 sup_set_class finxp_0 finxp_2 cin wcel iinxp_1 sup_set_class finxp_1 finxp_3 cin wcel wa iinxp_0 iinxp_1 iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa wa iinxp_0 sup_set_class finxp_0 wcel iinxp_0 sup_set_class finxp_2 wcel wa iinxp_1 sup_set_class finxp_1 wcel iinxp_1 sup_set_class finxp_3 wcel wa wa iinxp_0 sup_set_class finxp_0 finxp_2 cin wcel iinxp_1 sup_set_class finxp_1 finxp_3 cin wcel wa iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel an4 iinxp_0 sup_set_class finxp_0 finxp_2 cin wcel iinxp_0 sup_set_class finxp_0 wcel iinxp_0 sup_set_class finxp_2 wcel wa iinxp_1 sup_set_class finxp_1 finxp_3 cin wcel iinxp_1 sup_set_class finxp_1 wcel iinxp_1 sup_set_class finxp_3 wcel wa iinxp_0 sup_set_class finxp_0 finxp_2 elin iinxp_1 sup_set_class finxp_1 finxp_3 elin anbi12i bitr4i opabbii eqtri finxp_0 finxp_1 cxp iinxp_0 sup_set_class finxp_0 wcel iinxp_1 sup_set_class finxp_1 wcel wa iinxp_0 iinxp_1 copab finxp_2 finxp_3 cxp iinxp_0 sup_set_class finxp_2 wcel iinxp_1 sup_set_class finxp_3 wcel wa iinxp_0 iinxp_1 copab iinxp_0 iinxp_1 finxp_0 finxp_1 df-xp iinxp_0 iinxp_1 finxp_2 finxp_3 df-xp ineq12i iinxp_0 iinxp_1 finxp_0 finxp_2 cin finxp_1 finxp_3 cin df-xp 3eqtr4i $.
$}
$( Distributive law for cross product over intersection.  Theorem 102 of
       [Suppes] p. 52.  (Contributed by NM, 26-Sep-2004.) $)
${
	fxpindi_0 $f class A $.
	fxpindi_1 $f class B $.
	fxpindi_2 $f class C $.
	xpindi $p |- ( A X. ( B i^i C ) ) = ( ( A X. B ) i^i ( A X. C ) ) $= fxpindi_0 fxpindi_1 cxp fxpindi_0 fxpindi_2 cxp cin fxpindi_0 fxpindi_0 cin fxpindi_1 fxpindi_2 cin cxp fxpindi_0 fxpindi_1 fxpindi_2 cin cxp fxpindi_0 fxpindi_1 fxpindi_0 fxpindi_2 inxp fxpindi_0 fxpindi_0 cin fxpindi_0 fxpindi_1 fxpindi_2 cin fxpindi_0 inidm xpeq1i eqtr2i $.
$}
$( Distributive law for cross product over intersection.  Similar to
       Theorem 102 of [Suppes] p. 52.  (Contributed by NM, 26-Sep-2004.) $)
${
	fxpindir_0 $f class A $.
	fxpindir_1 $f class B $.
	fxpindir_2 $f class C $.
	xpindir $p |- ( ( A i^i B ) X. C ) = ( ( A X. C ) i^i ( B X. C ) ) $= fxpindir_0 fxpindir_2 cxp fxpindir_1 fxpindir_2 cxp cin fxpindir_0 fxpindir_1 cin fxpindir_2 fxpindir_2 cin cxp fxpindir_0 fxpindir_1 cin fxpindir_2 cxp fxpindir_0 fxpindir_2 fxpindir_1 fxpindir_2 inxp fxpindir_2 fxpindir_2 cin fxpindir_2 fxpindir_0 fxpindir_1 cin fxpindir_2 inidm xpeq2i eqtr2i $.
$}
$( Distributive law for cross product over indexed intersection.
       (Contributed by Mario Carneiro, 21-Mar-2015.) $)
${
	$d x y z A $.
	$d x y z C $.
	$d y z B $.
	ixpiindi_0 $f set y $.
	ixpiindi_1 $f set z $.
	fxpiindi_0 $f set x $.
	fxpiindi_1 $f class A $.
	fxpiindi_2 $f class B $.
	fxpiindi_3 $f class C $.
	xpiindi $p |- ( A =/= (/) -> ( C X. |^|_ x e. A B ) = |^|_ x e. A ( C X. B ) ) $= fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin cxp wrel fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin wrel wa fxpiindi_1 c0 wne fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin cxp fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin wceq fxpiindi_1 c0 wne fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin wrel fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin cxp wrel fxpiindi_1 c0 wne fxpiindi_3 fxpiindi_2 cxp wrel fxpiindi_0 fxpiindi_1 wrex fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin wrel fxpiindi_1 c0 wne fxpiindi_3 fxpiindi_2 cxp wrel fxpiindi_0 fxpiindi_1 wral fxpiindi_3 fxpiindi_2 cxp wrel fxpiindi_0 fxpiindi_1 wrex fxpiindi_3 fxpiindi_2 cxp wrel fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 relxp rgenw fxpiindi_3 fxpiindi_2 cxp wrel fxpiindi_0 fxpiindi_1 r19.2z mpan2 fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp reliin syl fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin relxp jctil fxpiindi_1 c0 wne ixpiindi_0 ixpiindi_1 fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin cxp fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin fxpiindi_1 c0 wne ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin wcel wa ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_3 fxpiindi_2 cxp wcel fxpiindi_0 fxpiindi_1 wral ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin cxp wcel ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin wcel fxpiindi_1 c0 wne ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel fxpiindi_0 fxpiindi_1 wral wa ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel wa fxpiindi_0 fxpiindi_1 wral ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin wcel wa ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_3 fxpiindi_2 cxp wcel fxpiindi_0 fxpiindi_1 wral fxpiindi_1 c0 wne ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel wa fxpiindi_0 fxpiindi_1 wral ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel fxpiindi_0 fxpiindi_1 wral wa ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel fxpiindi_0 fxpiindi_1 r19.28zv bicomd ixpiindi_1 sup_set_class fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel fxpiindi_0 fxpiindi_1 wral ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class cvv wcel ixpiindi_1 sup_set_class fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel fxpiindi_0 fxpiindi_1 wral wb ixpiindi_1 vex fxpiindi_0 ixpiindi_1 sup_set_class fxpiindi_1 fxpiindi_2 cvv eliin ax-mp anbi2i ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_3 fxpiindi_2 cxp wcel ixpiindi_0 sup_set_class fxpiindi_3 wcel ixpiindi_1 sup_set_class fxpiindi_2 wcel wa fxpiindi_0 fxpiindi_1 ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class fxpiindi_3 fxpiindi_2 opelxp ralbii 3bitr4g ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class fxpiindi_3 fxpiindi_0 fxpiindi_1 fxpiindi_2 ciin opelxp ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop cvv wcel ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_0 fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp ciin wcel ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_3 fxpiindi_2 cxp wcel fxpiindi_0 fxpiindi_1 wral wb ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class opex fxpiindi_0 ixpiindi_0 sup_set_class ixpiindi_1 sup_set_class cop fxpiindi_1 fxpiindi_3 fxpiindi_2 cxp cvv eliin ax-mp 3bitr4g eqrelrdv2 mpancom $.
$}
$( Distributive law for cross product over relativized indexed
       intersection.  (Contributed by Mario Carneiro, 21-Mar-2015.) $)
${
	$d x A $.
	$d x C $.
	fxpriindi_0 $f set x $.
	fxpriindi_1 $f class A $.
	fxpriindi_2 $f class B $.
	fxpriindi_3 $f class C $.
	fxpriindi_4 $f class D $.
	xpriindi $p |- ( C X. ( D i^i |^|_ x e. A B ) ) = ( ( C X. D ) i^i |^|_ x e. A ( C X. B ) ) $= fxpriindi_3 fxpriindi_4 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cin cxp fxpriindi_3 fxpriindi_4 cxp fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin cin wceq fxpriindi_1 c0 fxpriindi_1 c0 wceq fxpriindi_3 fxpriindi_4 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cin cxp fxpriindi_3 fxpriindi_4 cxp fxpriindi_3 fxpriindi_4 cxp fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin cin fxpriindi_1 c0 wceq fxpriindi_4 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cin fxpriindi_4 fxpriindi_3 fxpriindi_1 c0 wceq fxpriindi_4 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cin fxpriindi_4 cvv cin fxpriindi_4 fxpriindi_1 c0 wceq fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cvv fxpriindi_4 fxpriindi_1 c0 wceq fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin fxpriindi_0 c0 fxpriindi_2 ciin cvv fxpriindi_0 fxpriindi_1 c0 fxpriindi_2 iineq1 fxpriindi_0 fxpriindi_2 0iin syl6eq ineq2d fxpriindi_4 inv1 syl6eq xpeq2d fxpriindi_1 c0 wceq fxpriindi_3 fxpriindi_4 cxp fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin cin fxpriindi_3 fxpriindi_4 cxp cvv cin fxpriindi_3 fxpriindi_4 cxp fxpriindi_1 c0 wceq fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin cvv fxpriindi_3 fxpriindi_4 cxp fxpriindi_1 c0 wceq fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin fxpriindi_0 c0 fxpriindi_3 fxpriindi_2 cxp ciin cvv fxpriindi_0 fxpriindi_1 c0 fxpriindi_3 fxpriindi_2 cxp iineq1 fxpriindi_0 fxpriindi_3 fxpriindi_2 cxp 0iin syl6eq ineq2d fxpriindi_3 fxpriindi_4 cxp inv1 syl6eq eqtr4d fxpriindi_1 c0 wne fxpriindi_3 fxpriindi_4 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cin cxp fxpriindi_3 fxpriindi_4 cxp fxpriindi_3 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cxp cin fxpriindi_3 fxpriindi_4 cxp fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin cin fxpriindi_3 fxpriindi_4 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin xpindi fxpriindi_1 c0 wne fxpriindi_3 fxpriindi_0 fxpriindi_1 fxpriindi_2 ciin cxp fxpriindi_0 fxpriindi_1 fxpriindi_3 fxpriindi_2 cxp ciin fxpriindi_3 fxpriindi_4 cxp fxpriindi_0 fxpriindi_1 fxpriindi_2 fxpriindi_3 xpiindi ineq2d syl5eq pm2.61ine $.
$}
$( Membership in a union of cross products.  Analogue of ~ elxp for
       nonconstant ` B ( x ) ` .  (Contributed by Mario Carneiro,
       29-Dec-2014.) $)
${
	$d y A $.
	$d y B $.
	$d x y C $.
	$d x y $.
	feliunxp_0 $f set x $.
	feliunxp_1 $f set y $.
	feliunxp_2 $f class A $.
	feliunxp_3 $f class B $.
	feliunxp_4 $f class C $.
	eliunxp $p |- ( C e. U_ x e. A ( { x } X. B ) <-> E. x E. y ( C = <. x , y >. /\ ( x e. A /\ y e. B ) ) ) $= feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_0 wex feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel wa feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel wa feliunxp_0 wex feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_0 sup_set_class feliunxp_2 wcel feliunxp_1 sup_set_class feliunxp_3 wcel wa wa feliunxp_1 wex feliunxp_0 wex feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_0 wex feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wrel feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_0 wex feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wrel feliunxp_0 sup_set_class csn feliunxp_3 cxp wrel feliunxp_0 feliunxp_2 wral feliunxp_0 sup_set_class csn feliunxp_3 cxp wrel feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 relxp rgenw feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp reliun mpbir feliunxp_0 feliunxp_1 feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun elrel mpan pm4.71ri feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_0 feliunxp_0 feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp nfiu1 nfel2 19.41 feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel wa feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_0 sup_set_class feliunxp_2 wcel feliunxp_1 sup_set_class feliunxp_3 wcel wa wa feliunxp_1 wex feliunxp_0 feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_1 wex feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel wa feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel wa feliunxp_1 wex feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_0 sup_set_class feliunxp_2 wcel feliunxp_1 sup_set_class feliunxp_3 wcel wa wa feliunxp_1 wex feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_1 19.41v feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel wa feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_0 sup_set_class feliunxp_2 wcel feliunxp_1 sup_set_class feliunxp_3 wcel wa wa feliunxp_1 feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_0 sup_set_class feliunxp_2 wcel feliunxp_1 sup_set_class feliunxp_3 wcel wa feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop wceq feliunxp_4 feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun wcel feliunxp_0 sup_set_class feliunxp_2 wcel feliunxp_1 sup_set_class feliunxp_3 wcel wa feliunxp_4 feliunxp_0 sup_set_class feliunxp_1 sup_set_class cop feliunxp_0 feliunxp_2 feliunxp_0 sup_set_class csn feliunxp_3 cxp ciun eleq1 feliunxp_0 feliunxp_2 feliunxp_3 feliunxp_1 sup_set_class opeliunxp syl6bb pm5.32i exbii bitr3i exbii 3bitr2i $.
$}
$( Membership in a union of cross products.  (Contributed by Mario
       Carneiro, 14-Feb-2015.) $)
${
	$d x C $.
	$d x D $.
	$d x E $.
	$d x A $.
	fopeliunxp2_0 $f set x $.
	fopeliunxp2_1 $f class A $.
	fopeliunxp2_2 $f class B $.
	fopeliunxp2_3 $f class C $.
	fopeliunxp2_4 $f class D $.
	fopeliunxp2_5 $f class E $.
	eopeliunxp2_0 $e |- ( x = C -> B = E ) $.
	opeliunxp2 $p |- ( <. C , D >. e. U_ x e. A ( { x } X. B ) <-> ( C e. A /\ D e. E ) ) $= fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_3 cvv wcel fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_5 wcel wa fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_3 fopeliunxp2_4 fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wbr fopeliunxp2_3 cvv wcel fopeliunxp2_3 fopeliunxp2_4 fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun df-br fopeliunxp2_3 fopeliunxp2_4 fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wrel fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp wrel fopeliunxp2_0 fopeliunxp2_1 wral fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp wrel fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 relxp rgenw fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp reliun mpbir brrelexi sylbir fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_3 cvv wcel fopeliunxp2_4 fopeliunxp2_5 wcel fopeliunxp2_3 fopeliunxp2_1 elex adantr fopeliunxp2_0 sup_set_class fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_0 sup_set_class fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_2 wcel wa wb fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_5 wcel wa wb fopeliunxp2_0 fopeliunxp2_3 cvv fopeliunxp2_0 fopeliunxp2_3 nfcv fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_5 wcel wa fopeliunxp2_0 fopeliunxp2_0 fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp nfiu1 nfel2 fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_5 wcel wa fopeliunxp2_0 nfv nfbi fopeliunxp2_0 sup_set_class fopeliunxp2_3 wceq fopeliunxp2_0 sup_set_class fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun wcel fopeliunxp2_0 sup_set_class fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_2 wcel wa fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_5 wcel wa fopeliunxp2_0 sup_set_class fopeliunxp2_3 wceq fopeliunxp2_0 sup_set_class fopeliunxp2_4 cop fopeliunxp2_3 fopeliunxp2_4 cop fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_0 sup_set_class csn fopeliunxp2_2 cxp ciun fopeliunxp2_0 sup_set_class fopeliunxp2_3 fopeliunxp2_4 opeq1 eleq1d fopeliunxp2_0 sup_set_class fopeliunxp2_3 wceq fopeliunxp2_0 sup_set_class fopeliunxp2_1 wcel fopeliunxp2_3 fopeliunxp2_1 wcel fopeliunxp2_4 fopeliunxp2_2 wcel fopeliunxp2_4 fopeliunxp2_5 wcel fopeliunxp2_0 sup_set_class fopeliunxp2_3 fopeliunxp2_1 eleq1 fopeliunxp2_0 sup_set_class fopeliunxp2_3 wceq fopeliunxp2_2 fopeliunxp2_5 fopeliunxp2_4 eopeliunxp2_0 eleq2d anbi12d bibi12d fopeliunxp2_0 fopeliunxp2_1 fopeliunxp2_2 fopeliunxp2_4 opeliunxp vtoclgf pm5.21nii $.
$}
$( Write a double restricted quantification as one universal quantifier.
       In this version of ~ ralxp , ` B ( y ) ` is not assumed to be constant.
       (Contributed by Mario Carneiro, 29-Dec-2014.) $)
${
	$d x y z A $.
	$d x z B $.
	$d y z ph $.
	$d x ps $.
	fraliunxp_0 $f wff ph $.
	fraliunxp_1 $f wff ps $.
	fraliunxp_2 $f set x $.
	fraliunxp_3 $f set y $.
	fraliunxp_4 $f set z $.
	fraliunxp_5 $f class A $.
	fraliunxp_6 $f class B $.
	eraliunxp_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	raliunxp $p |- ( A. x e. U_ y e. A ( { y } X. B ) ph <-> A. y e. A A. z e. B ps ) $= fraliunxp_2 sup_set_class fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun wcel fraliunxp_0 wi fraliunxp_2 wal fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_1 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_0 fraliunxp_2 fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun wral fraliunxp_1 fraliunxp_4 fraliunxp_6 wral fraliunxp_3 fraliunxp_5 wral fraliunxp_2 sup_set_class fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun wcel fraliunxp_0 wi fraliunxp_2 wal fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_2 wal fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_1 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_2 sup_set_class fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun wcel fraliunxp_0 wi fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_2 fraliunxp_2 sup_set_class fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun wcel fraliunxp_0 wi fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_4 wex fraliunxp_3 wex fraliunxp_0 wi fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_2 sup_set_class fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun wcel fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_4 wex fraliunxp_3 wex fraliunxp_0 fraliunxp_3 fraliunxp_4 fraliunxp_5 fraliunxp_6 fraliunxp_2 sup_set_class eliunxp imbi1i fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 fraliunxp_3 fraliunxp_4 19.23vv bitr4i albii fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_2 wal fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_2 wal fraliunxp_4 wal fraliunxp_3 wal fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_1 wi fraliunxp_4 wal fraliunxp_3 wal fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_2 fraliunxp_3 fraliunxp_4 alrot3 fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_2 wal fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_1 wi fraliunxp_3 fraliunxp_4 fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_2 wal fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_0 wi wi fraliunxp_2 wal fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_1 wi fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa wa fraliunxp_0 wi fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_0 wi wi fraliunxp_2 fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_0 impexp albii fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_0 wi fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa fraliunxp_1 wi fraliunxp_2 fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class opex fraliunxp_2 sup_set_class fraliunxp_3 sup_set_class fraliunxp_4 sup_set_class cop wceq fraliunxp_0 fraliunxp_1 fraliunxp_3 sup_set_class fraliunxp_5 wcel fraliunxp_4 sup_set_class fraliunxp_6 wcel wa eraliunxp_0 imbi2d ceqsalv bitri 2albii bitri bitri fraliunxp_0 fraliunxp_2 fraliunxp_3 fraliunxp_5 fraliunxp_3 sup_set_class csn fraliunxp_6 cxp ciun df-ral fraliunxp_1 fraliunxp_3 fraliunxp_4 fraliunxp_5 fraliunxp_6 r2al 3bitr4i $.
$}
$( Write a double restricted quantification as one universal quantifier.
       In this version of ~ rexxp , ` B ( y ) ` is not assumed to be constant.
       (Contributed by Mario Carneiro, 14-Feb-2015.) $)
${
	$d x y z A $.
	$d x z B $.
	$d y z ph $.
	$d x ps $.
	frexiunxp_0 $f wff ph $.
	frexiunxp_1 $f wff ps $.
	frexiunxp_2 $f set x $.
	frexiunxp_3 $f set y $.
	frexiunxp_4 $f set z $.
	frexiunxp_5 $f class A $.
	frexiunxp_6 $f class B $.
	erexiunxp_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	rexiunxp $p |- ( E. x e. U_ y e. A ( { y } X. B ) ph <-> E. y e. A E. z e. B ps ) $= frexiunxp_0 wn frexiunxp_2 frexiunxp_3 frexiunxp_5 frexiunxp_3 sup_set_class csn frexiunxp_6 cxp ciun wral wn frexiunxp_1 frexiunxp_4 frexiunxp_6 wrex wn frexiunxp_3 frexiunxp_5 wral wn frexiunxp_0 frexiunxp_2 frexiunxp_3 frexiunxp_5 frexiunxp_3 sup_set_class csn frexiunxp_6 cxp ciun wrex frexiunxp_1 frexiunxp_4 frexiunxp_6 wrex frexiunxp_3 frexiunxp_5 wrex frexiunxp_0 wn frexiunxp_2 frexiunxp_3 frexiunxp_5 frexiunxp_3 sup_set_class csn frexiunxp_6 cxp ciun wral frexiunxp_1 frexiunxp_4 frexiunxp_6 wrex wn frexiunxp_3 frexiunxp_5 wral frexiunxp_0 wn frexiunxp_2 frexiunxp_3 frexiunxp_5 frexiunxp_3 sup_set_class csn frexiunxp_6 cxp ciun wral frexiunxp_1 wn frexiunxp_4 frexiunxp_6 wral frexiunxp_3 frexiunxp_5 wral frexiunxp_1 frexiunxp_4 frexiunxp_6 wrex wn frexiunxp_3 frexiunxp_5 wral frexiunxp_0 wn frexiunxp_1 wn frexiunxp_2 frexiunxp_3 frexiunxp_4 frexiunxp_5 frexiunxp_6 frexiunxp_2 sup_set_class frexiunxp_3 sup_set_class frexiunxp_4 sup_set_class cop wceq frexiunxp_0 frexiunxp_1 erexiunxp_0 notbid raliunxp frexiunxp_1 wn frexiunxp_4 frexiunxp_6 wral frexiunxp_1 frexiunxp_4 frexiunxp_6 wrex wn frexiunxp_3 frexiunxp_5 frexiunxp_1 frexiunxp_4 frexiunxp_6 ralnex ralbii bitri notbii frexiunxp_0 frexiunxp_2 frexiunxp_3 frexiunxp_5 frexiunxp_3 sup_set_class csn frexiunxp_6 cxp ciun dfrex2 frexiunxp_1 frexiunxp_4 frexiunxp_6 wrex frexiunxp_3 frexiunxp_5 dfrex2 3bitr4i $.
$}
$( Universal quantification restricted to a cross product is equivalent to
       a double restricted quantification.  The hypothesis specifies an
       implicit substitution.  (Contributed by NM, 7-Feb-2004.)  (Revised by
       Mario Carneiro, 29-Dec-2014.) $)
${
	$d x y z A $.
	$d x z B $.
	$d y z ph $.
	$d x ps $.
	$d y B $.
	fralxp_0 $f wff ph $.
	fralxp_1 $f wff ps $.
	fralxp_2 $f set x $.
	fralxp_3 $f set y $.
	fralxp_4 $f set z $.
	fralxp_5 $f class A $.
	fralxp_6 $f class B $.
	eralxp_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	ralxp $p |- ( A. x e. ( A X. B ) ph <-> A. y e. A A. z e. B ps ) $= fralxp_0 fralxp_2 fralxp_5 fralxp_6 cxp wral fralxp_0 fralxp_2 fralxp_3 fralxp_5 fralxp_3 sup_set_class csn fralxp_6 cxp ciun wral fralxp_1 fralxp_4 fralxp_6 wral fralxp_3 fralxp_5 wral fralxp_0 fralxp_2 fralxp_3 fralxp_5 fralxp_3 sup_set_class csn fralxp_6 cxp ciun fralxp_5 fralxp_6 cxp fralxp_3 fralxp_5 fralxp_6 iunxpconst raleqi fralxp_0 fralxp_1 fralxp_2 fralxp_3 fralxp_4 fralxp_5 fralxp_6 eralxp_0 raliunxp bitr3i $.
$}
$( Existential quantification restricted to a cross product is equivalent
       to a double restricted quantification.  (Contributed by NM,
       11-Nov-1995.)  (Revised by Mario Carneiro, 14-Feb-2015.) $)
${
	$d x y z A $.
	$d x z B $.
	$d y z ph $.
	$d x ps $.
	$d y B $.
	frexxp_0 $f wff ph $.
	frexxp_1 $f wff ps $.
	frexxp_2 $f set x $.
	frexxp_3 $f set y $.
	frexxp_4 $f set z $.
	frexxp_5 $f class A $.
	frexxp_6 $f class B $.
	erexxp_0 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	rexxp $p |- ( E. x e. ( A X. B ) ph <-> E. y e. A E. z e. B ps ) $= frexxp_0 frexxp_2 frexxp_5 frexxp_6 cxp wrex frexxp_0 frexxp_2 frexxp_3 frexxp_5 frexxp_3 sup_set_class csn frexxp_6 cxp ciun wrex frexxp_1 frexxp_4 frexxp_6 wrex frexxp_3 frexxp_5 wrex frexxp_0 frexxp_2 frexxp_3 frexxp_5 frexxp_3 sup_set_class csn frexxp_6 cxp ciun frexxp_5 frexxp_6 cxp frexxp_3 frexxp_5 frexxp_6 iunxpconst rexeqi frexxp_0 frexxp_1 frexxp_2 frexxp_3 frexxp_4 frexxp_5 frexxp_6 erexxp_0 rexiunxp bitr3i $.
$}
$( Disjoint union is a subset of a cross product.  (Contributed by Stefan
       O'Rear, 21-Nov-2014.) $)
${
	$d x A $.
	fdjussxp_0 $f set x $.
	fdjussxp_1 $f class A $.
	fdjussxp_2 $f class B $.
	djussxp $p |- U_ x e. A ( { x } X. B ) C_ ( A X. _V ) $= fdjussxp_0 fdjussxp_1 fdjussxp_0 sup_set_class csn fdjussxp_2 cxp ciun fdjussxp_1 cvv cxp wss fdjussxp_0 sup_set_class csn fdjussxp_2 cxp fdjussxp_1 cvv cxp wss fdjussxp_0 fdjussxp_1 fdjussxp_0 fdjussxp_1 fdjussxp_0 sup_set_class csn fdjussxp_2 cxp fdjussxp_1 cvv cxp iunss fdjussxp_0 sup_set_class fdjussxp_1 wcel fdjussxp_0 sup_set_class csn fdjussxp_1 wss fdjussxp_2 cvv wss fdjussxp_0 sup_set_class csn fdjussxp_2 cxp fdjussxp_1 cvv cxp wss fdjussxp_0 sup_set_class fdjussxp_1 snssi fdjussxp_2 ssv fdjussxp_0 sup_set_class csn fdjussxp_1 fdjussxp_2 cvv xpss12 sylancl mprgbir $.
$}
$( Version of ~ ralxp with bound-variable hypotheses.  (Contributed by NM,
       18-Aug-2006.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$d u v w x y A $.
	$d u v w x y z B $.
	$d u v w ph $.
	$d u v w ps $.
	iralxpf_0 $f set w $.
	iralxpf_1 $f set v $.
	iralxpf_2 $f set u $.
	fralxpf_0 $f wff ph $.
	fralxpf_1 $f wff ps $.
	fralxpf_2 $f set x $.
	fralxpf_3 $f set y $.
	fralxpf_4 $f set z $.
	fralxpf_5 $f class A $.
	fralxpf_6 $f class B $.
	eralxpf_0 $e |- F/ y ph $.
	eralxpf_1 $e |- F/ z ph $.
	eralxpf_2 $e |- F/ x ps $.
	eralxpf_3 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	ralxpf $p |- ( A. x e. ( A X. B ) ph <-> A. y e. A A. z e. B ps ) $= fralxpf_0 fralxpf_2 fralxpf_5 fralxpf_6 cxp wral fralxpf_0 fralxpf_2 iralxpf_0 wsb iralxpf_0 fralxpf_5 fralxpf_6 cxp wral fralxpf_1 fralxpf_4 fralxpf_6 wral fralxpf_3 fralxpf_5 wral fralxpf_0 fralxpf_2 iralxpf_0 fralxpf_5 fralxpf_6 cxp cbvralsv fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 fralxpf_6 wral iralxpf_2 fralxpf_5 wral fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb iralxpf_1 fralxpf_6 wral iralxpf_2 fralxpf_5 wral fralxpf_1 fralxpf_4 fralxpf_6 wral fralxpf_3 fralxpf_5 wral fralxpf_0 fralxpf_2 iralxpf_0 wsb iralxpf_0 fralxpf_5 fralxpf_6 cxp wral fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 fralxpf_6 wral fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb iralxpf_1 fralxpf_6 wral iralxpf_2 fralxpf_5 fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 fralxpf_6 cbvralsv ralbii fralxpf_1 fralxpf_4 fralxpf_6 wral fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 fralxpf_6 wral fralxpf_3 iralxpf_2 fralxpf_5 fralxpf_1 fralxpf_4 fralxpf_6 wral iralxpf_2 nfv fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_3 fralxpf_4 fralxpf_6 fralxpf_3 fralxpf_6 nfcv fralxpf_1 fralxpf_3 iralxpf_2 nfs1v nfral fralxpf_3 sup_set_class iralxpf_2 sup_set_class wceq fralxpf_1 fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 fralxpf_6 fralxpf_1 fralxpf_3 iralxpf_2 sbequ12 ralbidv cbvral fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb iralxpf_0 iralxpf_2 iralxpf_1 fralxpf_5 fralxpf_6 iralxpf_0 sup_set_class iralxpf_2 sup_set_class iralxpf_1 sup_set_class cop wceq iralxpf_0 sup_set_class fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop wceq fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop iralxpf_2 sup_set_class iralxpf_1 sup_set_class cop wceq wa fralxpf_4 wex fralxpf_3 wex fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb wb fralxpf_3 fralxpf_4 iralxpf_0 sup_set_class iralxpf_2 sup_set_class iralxpf_1 sup_set_class iralxpf_2 vex iralxpf_1 vex eqvinop iralxpf_0 sup_set_class fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop wceq fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop iralxpf_2 sup_set_class iralxpf_1 sup_set_class cop wceq wa fralxpf_4 wex fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb wb fralxpf_3 fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb fralxpf_3 fralxpf_0 fralxpf_2 iralxpf_0 fralxpf_3 eralxpf_0 nfsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 fralxpf_3 fralxpf_1 fralxpf_3 iralxpf_2 nfs1v nfsb nfbi iralxpf_0 sup_set_class fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop wceq fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop iralxpf_2 sup_set_class iralxpf_1 sup_set_class cop wceq wa fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb wb fralxpf_4 fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb fralxpf_4 fralxpf_0 fralxpf_2 iralxpf_0 fralxpf_4 eralxpf_1 nfsb fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 nfs1v nfbi iralxpf_0 sup_set_class fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop wceq fralxpf_0 fralxpf_2 iralxpf_0 wsb fralxpf_1 fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop iralxpf_2 sup_set_class iralxpf_1 sup_set_class cop wceq fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb fralxpf_0 fralxpf_1 fralxpf_2 iralxpf_0 fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop eralxpf_2 eralxpf_3 sbhypf fralxpf_3 sup_set_class fralxpf_4 sup_set_class cop iralxpf_2 sup_set_class iralxpf_1 sup_set_class cop wceq fralxpf_3 sup_set_class iralxpf_2 sup_set_class wceq fralxpf_4 sup_set_class iralxpf_1 sup_set_class wceq wa fralxpf_1 fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb wb fralxpf_3 sup_set_class fralxpf_4 sup_set_class iralxpf_2 sup_set_class iralxpf_1 sup_set_class fralxpf_3 vex fralxpf_4 vex opth fralxpf_3 sup_set_class iralxpf_2 sup_set_class wceq fralxpf_1 fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 sup_set_class iralxpf_1 sup_set_class wceq fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 wsb fralxpf_1 fralxpf_3 iralxpf_2 sbequ12 fralxpf_1 fralxpf_3 iralxpf_2 wsb fralxpf_4 iralxpf_1 sbequ12 sylan9bb sylbi sylan9bb exlimi exlimi sylbi ralxp 3bitr4ri bitri $.
$}
$( Version of ~ rexxp with bound-variable hypotheses.  (Contributed by NM,
       19-Dec-2008.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$d x y A $.
	$d x y z B $.
	frexxpf_0 $f wff ph $.
	frexxpf_1 $f wff ps $.
	frexxpf_2 $f set x $.
	frexxpf_3 $f set y $.
	frexxpf_4 $f set z $.
	frexxpf_5 $f class A $.
	frexxpf_6 $f class B $.
	erexxpf_0 $e |- F/ y ph $.
	erexxpf_1 $e |- F/ z ph $.
	erexxpf_2 $e |- F/ x ps $.
	erexxpf_3 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
	rexxpf $p |- ( E. x e. ( A X. B ) ph <-> E. y e. A E. z e. B ps ) $= frexxpf_0 wn frexxpf_2 frexxpf_5 frexxpf_6 cxp wral wn frexxpf_1 frexxpf_4 frexxpf_6 wrex wn frexxpf_3 frexxpf_5 wral wn frexxpf_0 frexxpf_2 frexxpf_5 frexxpf_6 cxp wrex frexxpf_1 frexxpf_4 frexxpf_6 wrex frexxpf_3 frexxpf_5 wrex frexxpf_0 wn frexxpf_2 frexxpf_5 frexxpf_6 cxp wral frexxpf_1 frexxpf_4 frexxpf_6 wrex wn frexxpf_3 frexxpf_5 wral frexxpf_0 wn frexxpf_2 frexxpf_5 frexxpf_6 cxp wral frexxpf_1 wn frexxpf_4 frexxpf_6 wral frexxpf_3 frexxpf_5 wral frexxpf_1 frexxpf_4 frexxpf_6 wrex wn frexxpf_3 frexxpf_5 wral frexxpf_0 wn frexxpf_1 wn frexxpf_2 frexxpf_3 frexxpf_4 frexxpf_5 frexxpf_6 frexxpf_0 frexxpf_3 erexxpf_0 nfn frexxpf_0 frexxpf_4 erexxpf_1 nfn frexxpf_1 frexxpf_2 erexxpf_2 nfn frexxpf_2 sup_set_class frexxpf_3 sup_set_class frexxpf_4 sup_set_class cop wceq frexxpf_0 frexxpf_1 erexxpf_3 notbid ralxpf frexxpf_1 wn frexxpf_4 frexxpf_6 wral frexxpf_1 frexxpf_4 frexxpf_6 wrex wn frexxpf_3 frexxpf_5 frexxpf_1 frexxpf_4 frexxpf_6 ralnex ralbii bitri notbii frexxpf_0 frexxpf_2 frexxpf_5 frexxpf_6 cxp dfrex2 frexxpf_1 frexxpf_4 frexxpf_6 wrex frexxpf_3 frexxpf_5 dfrex2 3bitr4i $.
$}
$( Indexed union on a cross product is equals a double indexed union.  The
       hypothesis specifies an implicit substitution.  (Contributed by NM,
       19-Dec-2008.) $)
${
	$d w x y A $.
	$d w x y z B $.
	$d w C $.
	$d w D $.
	iiunxpf_0 $f set w $.
	fiunxpf_0 $f set x $.
	fiunxpf_1 $f set y $.
	fiunxpf_2 $f set z $.
	fiunxpf_3 $f class A $.
	fiunxpf_4 $f class B $.
	fiunxpf_5 $f class C $.
	fiunxpf_6 $f class D $.
	eiunxpf_0 $e |- F/_ y C $.
	eiunxpf_1 $e |- F/_ z C $.
	eiunxpf_2 $e |- F/_ x D $.
	eiunxpf_3 $e |- ( x = <. y , z >. -> C = D ) $.
	iunxpf $p |- U_ x e. ( A X. B ) C = U_ y e. A U_ z e. B D $= iiunxpf_0 fiunxpf_0 fiunxpf_3 fiunxpf_4 cxp fiunxpf_5 ciun fiunxpf_1 fiunxpf_3 fiunxpf_2 fiunxpf_4 fiunxpf_6 ciun ciun iiunxpf_0 sup_set_class fiunxpf_5 wcel fiunxpf_0 fiunxpf_3 fiunxpf_4 cxp wrex iiunxpf_0 sup_set_class fiunxpf_6 wcel fiunxpf_2 fiunxpf_4 wrex fiunxpf_1 fiunxpf_3 wrex iiunxpf_0 sup_set_class fiunxpf_0 fiunxpf_3 fiunxpf_4 cxp fiunxpf_5 ciun wcel iiunxpf_0 sup_set_class fiunxpf_1 fiunxpf_3 fiunxpf_2 fiunxpf_4 fiunxpf_6 ciun ciun wcel iiunxpf_0 sup_set_class fiunxpf_5 wcel iiunxpf_0 sup_set_class fiunxpf_6 wcel fiunxpf_0 fiunxpf_1 fiunxpf_2 fiunxpf_3 fiunxpf_4 fiunxpf_1 iiunxpf_0 fiunxpf_5 eiunxpf_0 nfcri fiunxpf_2 iiunxpf_0 fiunxpf_5 eiunxpf_1 nfcri fiunxpf_0 iiunxpf_0 fiunxpf_6 eiunxpf_2 nfcri fiunxpf_0 sup_set_class fiunxpf_1 sup_set_class fiunxpf_2 sup_set_class cop wceq fiunxpf_5 fiunxpf_6 iiunxpf_0 sup_set_class eiunxpf_3 eleq2d rexxpf fiunxpf_0 iiunxpf_0 sup_set_class fiunxpf_3 fiunxpf_4 cxp fiunxpf_5 eliun iiunxpf_0 sup_set_class fiunxpf_1 fiunxpf_3 fiunxpf_2 fiunxpf_4 fiunxpf_6 ciun ciun wcel iiunxpf_0 sup_set_class fiunxpf_2 fiunxpf_4 fiunxpf_6 ciun wcel fiunxpf_1 fiunxpf_3 wrex iiunxpf_0 sup_set_class fiunxpf_6 wcel fiunxpf_2 fiunxpf_4 wrex fiunxpf_1 fiunxpf_3 wrex fiunxpf_1 iiunxpf_0 sup_set_class fiunxpf_3 fiunxpf_2 fiunxpf_4 fiunxpf_6 ciun eliun iiunxpf_0 sup_set_class fiunxpf_2 fiunxpf_4 fiunxpf_6 ciun wcel iiunxpf_0 sup_set_class fiunxpf_6 wcel fiunxpf_2 fiunxpf_4 wrex fiunxpf_1 fiunxpf_3 fiunxpf_2 iiunxpf_0 sup_set_class fiunxpf_4 fiunxpf_6 eliun rexbii bitri 3bitr4i eqriv $.
$}
$( Deduce equality of a relation and an ordered-pair class builder.
       Compare ~ abbi2dv .  (Contributed by NM, 24-Feb-2014.) $)
${
	$d x y A $.
	$d x y ph $.
	fopabbi2dv_0 $f wff ph $.
	fopabbi2dv_1 $f wff ps $.
	fopabbi2dv_2 $f set x $.
	fopabbi2dv_3 $f set y $.
	fopabbi2dv_4 $f class A $.
	eopabbi2dv_0 $e |- Rel A $.
	eopabbi2dv_1 $e |- ( ph -> ( <. x , y >. e. A <-> ps ) ) $.
	opabbi2dv $p |- ( ph -> A = { <. x , y >. | ps } ) $= fopabbi2dv_0 fopabbi2dv_4 fopabbi2dv_2 sup_set_class fopabbi2dv_3 sup_set_class cop fopabbi2dv_4 wcel fopabbi2dv_2 fopabbi2dv_3 copab fopabbi2dv_1 fopabbi2dv_2 fopabbi2dv_3 copab fopabbi2dv_4 wrel fopabbi2dv_2 sup_set_class fopabbi2dv_3 sup_set_class cop fopabbi2dv_4 wcel fopabbi2dv_2 fopabbi2dv_3 copab fopabbi2dv_4 wceq eopabbi2dv_0 fopabbi2dv_2 fopabbi2dv_3 fopabbi2dv_4 opabid2 ax-mp fopabbi2dv_0 fopabbi2dv_2 sup_set_class fopabbi2dv_3 sup_set_class cop fopabbi2dv_4 wcel fopabbi2dv_1 fopabbi2dv_2 fopabbi2dv_3 eopabbi2dv_1 opabbidv syl5eqr $.
$}
$( A necessary and sufficient condition for a Kuratowski ordered pair to be
       a relation.  (Contributed by NM, 3-Jun-2008.) $)
${
	$d v w x y z A $.
	$d v w x y z B $.
	irelop_0 $f set z $.
	irelop_1 $f set w $.
	irelop_2 $f set v $.
	frelop_0 $f set x $.
	frelop_1 $f set y $.
	frelop_2 $f class A $.
	frelop_3 $f class B $.
	erelop_0 $e |- A e. _V $.
	erelop_1 $e |- B e. _V $.
	relop $p |- ( Rel <. A , B >. <-> E. x E. y ( A = { x } /\ B = { x , y } ) ) $= frelop_2 frelop_3 cop wrel frelop_2 frelop_3 cop cvv cvv cxp wss frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_1 wex frelop_0 wex frelop_2 frelop_3 cop df-rel frelop_2 frelop_3 cop cvv cvv cxp wss frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_1 wex frelop_0 wex frelop_2 frelop_3 cop cvv cvv cxp wss irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal wa frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_1 wex frelop_0 wex frelop_2 frelop_3 cop cvv cvv cxp wss irelop_0 sup_set_class frelop_2 frelop_3 cop wcel irelop_0 sup_set_class cvv cvv cxp wcel wi irelop_0 wal irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal wa irelop_0 frelop_2 frelop_3 cop cvv cvv cxp dfss2 irelop_0 sup_set_class frelop_2 frelop_3 cop wcel irelop_0 sup_set_class cvv cvv cxp wcel wi irelop_0 wal irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi wa irelop_0 wal irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal wa irelop_0 sup_set_class frelop_2 frelop_3 cop wcel irelop_0 sup_set_class cvv cvv cxp wcel wi irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi wa irelop_0 irelop_0 sup_set_class frelop_2 frelop_3 cop wcel irelop_0 sup_set_class cvv cvv cxp wcel wi irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq wo irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi wa irelop_0 sup_set_class frelop_2 frelop_3 cop wcel irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq wo irelop_0 sup_set_class cvv cvv cxp wcel irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex irelop_0 sup_set_class frelop_2 frelop_3 irelop_0 vex erelop_0 erelop_1 elop frelop_0 frelop_1 irelop_0 sup_set_class elvv imbi12i irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq jaob bitri albii irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 19.26 bitri bitri irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal frelop_2 irelop_1 sup_set_class csn wceq irelop_1 wex frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_1 wex frelop_0 wex irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal frelop_2 csn frelop_2 csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 wex wi frelop_2 irelop_1 sup_set_class csn wceq irelop_1 wex irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi frelop_2 csn frelop_2 csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 wex wi irelop_0 frelop_2 csn frelop_2 snex irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_2 csn wceq frelop_2 csn frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 wex irelop_0 sup_set_class frelop_2 csn frelop_2 csn eqeq1 irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_0 frelop_1 irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_2 csn frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa irelop_0 sup_set_class frelop_2 csn frelop_0 sup_set_class frelop_1 sup_set_class cop eqeq1 frelop_2 csn frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_0 sup_set_class frelop_1 sup_set_class cop frelop_2 csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_2 csn frelop_0 sup_set_class frelop_1 sup_set_class cop eqcom frelop_0 sup_set_class frelop_1 sup_set_class frelop_2 frelop_0 vex frelop_1 vex erelop_0 opeqsn bitri syl6bb 2exbidv imbi12d spcv frelop_2 irelop_1 sup_set_class csn wceq irelop_1 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_0 wex frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 wex frelop_2 csn frelop_2 csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 wex wi frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq irelop_1 frelop_0 irelop_1 sup_set_class frelop_0 sup_set_class wceq irelop_1 sup_set_class csn frelop_0 sup_set_class csn frelop_2 irelop_1 sup_set_class frelop_0 sup_set_class sneq eqeq2d cbvexv frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_0 frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_1 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_1 sup_set_class frelop_0 sup_set_class wceq frelop_1 wex frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_1 wex frelop_1 frelop_0 a9ev frelop_1 sup_set_class frelop_0 sup_set_class wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_1 frelop_1 frelop_0 equcom exbii mpbi frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_1 19.41v mpbiran exbii frelop_2 csn frelop_2 csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_1 wex frelop_0 wex frelop_2 csn eqid a1bi 3bitr2ri sylib irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 wal frelop_2 frelop_3 cpr frelop_2 frelop_3 cpr wceq frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex frelop_2 frelop_3 cpr eqid irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi frelop_2 frelop_3 cpr frelop_2 frelop_3 cpr wceq frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex wi irelop_0 frelop_2 frelop_3 cpr frelop_2 frelop_3 prex irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq frelop_2 frelop_3 cpr frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex irelop_0 sup_set_class frelop_2 frelop_3 cpr frelop_2 frelop_3 cpr eqeq1 irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_0 frelop_1 irelop_0 sup_set_class frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop eqeq1 2exbidv imbi12d spcv mpi frelop_2 irelop_1 sup_set_class csn wceq irelop_1 wex frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_1 wex frelop_0 wex frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_1 wex frelop_0 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_1 wex frelop_0 wex wi irelop_1 frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_0 frelop_1 frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq wa wo frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop wceq frelop_0 sup_set_class frelop_1 sup_set_class cop frelop_2 frelop_3 cpr wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq wa wo frelop_2 frelop_3 cpr frelop_0 sup_set_class frelop_1 sup_set_class cop eqcom frelop_0 sup_set_class frelop_1 sup_set_class frelop_2 frelop_3 frelop_0 vex frelop_1 vex erelop_0 erelop_1 opeqpr bitri frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq wa frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa idd frelop_2 irelop_1 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_2 irelop_1 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa wi frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_2 irelop_1 sup_set_class csn wceq wa frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa wi frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_2 irelop_1 sup_set_class csn wceq wa frelop_0 sup_set_class frelop_1 sup_set_class cpr irelop_1 sup_set_class csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr irelop_1 sup_set_class csn eqtr2 frelop_0 sup_set_class frelop_1 sup_set_class cpr irelop_1 sup_set_class csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_1 sup_set_class irelop_1 sup_set_class wceq frelop_0 sup_set_class frelop_1 sup_set_class irelop_1 sup_set_class frelop_0 vex frelop_1 vex irelop_1 vex preqsn simplbi syl frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa wi wi frelop_2 irelop_1 sup_set_class csn wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa wi frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_3 frelop_0 sup_set_class csn wceq wa frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_0 sup_set_class frelop_1 sup_set_class cpr frelop_0 sup_set_class csn frelop_2 frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_0 sup_set_class cpr frelop_0 sup_set_class frelop_1 sup_set_class cpr frelop_0 sup_set_class dfsn2 frelop_0 sup_set_class frelop_1 sup_set_class frelop_0 sup_set_class preq2 syl5req eqeq2d frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_1 sup_set_class cpr frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class wceq frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_0 sup_set_class cpr frelop_0 sup_set_class frelop_1 sup_set_class cpr frelop_0 sup_set_class dfsn2 frelop_0 sup_set_class frelop_1 sup_set_class frelop_0 sup_set_class preq2 syl5eq eqeq2d anbi12d biimpd exp3a com12 adantr mpd expcom imp3a jaod syl5bi 2eximdv exlimiv imp syl2an sylbi frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_3 cop cvv cvv cxp wss frelop_0 frelop_1 frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 frelop_2 frelop_3 cop cvv cvv cxp frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq wo irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_2 wex irelop_1 wex irelop_0 sup_set_class frelop_2 frelop_3 cop wcel irelop_0 sup_set_class cvv cvv cxp wcel frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq wo irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_2 wex irelop_1 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_2 wex irelop_1 wex irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq frelop_2 frelop_0 sup_set_class csn wceq irelop_0 sup_set_class frelop_2 csn wceq irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_2 wex irelop_1 wex frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq frelop_2 frelop_0 sup_set_class csn wceq irelop_0 sup_set_class frelop_2 csn wceq wa irelop_0 sup_set_class frelop_0 sup_set_class frelop_0 sup_set_class cop wceq irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_2 wex irelop_1 wex frelop_2 frelop_0 sup_set_class csn wceq irelop_0 sup_set_class frelop_2 csn wceq wa irelop_0 sup_set_class frelop_2 csn frelop_0 sup_set_class frelop_0 sup_set_class cop frelop_2 frelop_0 sup_set_class csn wceq irelop_0 sup_set_class frelop_2 csn wceq simpr frelop_2 frelop_0 sup_set_class csn wceq frelop_0 sup_set_class frelop_0 sup_set_class cop frelop_2 csn wceq irelop_0 sup_set_class frelop_2 csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_0 sup_set_class frelop_0 sup_set_class wceq frelop_2 frelop_0 sup_set_class csn wceq wa frelop_0 sup_set_class frelop_0 sup_set_class cop frelop_2 csn wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_0 sup_set_class frelop_0 sup_set_class wceq frelop_0 equid jctl frelop_0 sup_set_class frelop_0 sup_set_class frelop_2 frelop_0 vex frelop_0 vex erelop_0 opeqsn sylibr adantr eqtr4d irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_0 sup_set_class cop wceq irelop_1 irelop_2 frelop_0 sup_set_class frelop_0 sup_set_class frelop_0 vex frelop_0 vex irelop_1 sup_set_class frelop_0 sup_set_class wceq irelop_2 sup_set_class frelop_0 sup_set_class wceq wa irelop_1 sup_set_class irelop_2 sup_set_class cop frelop_0 sup_set_class frelop_0 sup_set_class cop irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class frelop_0 sup_set_class frelop_0 sup_set_class opeq12 eqeq2d spc2ev syl adantlr frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq wa irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_2 wex irelop_1 wex frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq wa irelop_0 sup_set_class frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_1 sup_set_class cpr cpr frelop_0 sup_set_class frelop_1 sup_set_class cop frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa irelop_0 sup_set_class frelop_2 frelop_3 cpr wceq irelop_0 sup_set_class frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_1 sup_set_class cpr cpr wceq frelop_2 frelop_0 sup_set_class csn wceq frelop_3 frelop_0 sup_set_class frelop_1 sup_set_class cpr wceq wa frelop_2 frelop_3 cpr frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_1 sup_set_class cpr cpr irelop_0 sup_set_class frelop_2 frelop_3 frelop_0 sup_set_class csn frelop_0 sup_set_class frelop_1 sup_set_class cpr preq12 eqeq2d biimpa frelop_0 sup_set_class frelop_1 sup_set_class frelop_0 vex frelop_1 vex dfop syl6eqr irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class cop wceq irelop_0 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class cop wceq irelop_1 irelop_2 frelop_0 sup_set_class frelop_1 sup_set_class frelop_0 vex frelop_1 vex irelop_1 sup_set_class frelop_0 sup_set_class wceq irelop_2 sup_set_class frelop_1 sup_set_class wceq wa irelop_1 sup_set_class irelop_2 sup_set_class cop frelop_0 sup_set_class frelop_1 sup_set_class cop irelop_0 sup_set_class irelop_1 sup_set_class irelop_2 sup_set_class frelop_0 sup_set_class frelop_1 sup_set_class opeq12 eqeq2d spc2ev syl jaodan ex irelop_0 sup_set_class frelop_2 frelop_3 irelop_0 vex erelop_0 erelop_1 elop irelop_1 irelop_2 irelop_0 sup_set_class elvv 3imtr4g ssrdv exlimivv impbii bitri $.
$}
$( For sets, the identity relation is the same as equality.  (Contributed
       by NM, 30-Apr-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	iideqg_0 $f set x $.
	iideqg_1 $f set y $.
	fideqg_0 $f class A $.
	fideqg_1 $f class B $.
	fideqg_2 $f class V $.
	ideqg $p |- ( B e. V -> ( A _I B <-> A = B ) ) $= fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 cid wbr fideqg_0 fideqg_1 wceq fideqg_0 cvv wcel fideqg_1 fideqg_2 wcel wa fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 cid wbr wa fideqg_0 cvv wcel fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 cid wbr fideqg_0 cvv wcel fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 cid reli brrelexi adantl fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 cid wbr simpl jca fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 wceq wa fideqg_0 cvv wcel fideqg_1 fideqg_2 wcel fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 wceq wa fideqg_0 fideqg_2 wcel fideqg_0 cvv wcel fideqg_0 fideqg_1 wceq fideqg_0 fideqg_2 wcel fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 fideqg_2 eleq1 biimparc fideqg_0 fideqg_2 elex syl fideqg_1 fideqg_2 wcel fideqg_0 fideqg_1 wceq simpl jca iideqg_0 sup_set_class iideqg_1 sup_set_class wceq fideqg_0 iideqg_1 sup_set_class wceq fideqg_0 fideqg_1 wceq iideqg_0 iideqg_1 fideqg_0 fideqg_1 cvv fideqg_2 cid iideqg_0 sup_set_class fideqg_0 iideqg_1 sup_set_class eqeq1 iideqg_1 sup_set_class fideqg_1 fideqg_0 eqeq2 iideqg_0 iideqg_1 df-id brabg pm5.21nd $.
$}
$( For sets, the identity relation is the same as equality.  (Contributed
       by NM, 13-Aug-1995.) $)
${
	fideq_0 $f class A $.
	fideq_1 $f class B $.
	eideq_0 $e |- B e. _V $.
	ideq $p |- ( A _I B <-> A = B ) $= fideq_1 cvv wcel fideq_0 fideq_1 cid wbr fideq_0 fideq_1 wceq wb eideq_0 fideq_0 fideq_1 cvv ideqg ax-mp $.
$}
$( A set is identical to itself.  (Contributed by NM, 28-May-2008.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fididg_0 $f class A $.
	fididg_1 $f class V $.
	ididg $p |- ( A e. V -> A _I A ) $= fididg_0 fididg_1 wcel fididg_0 fididg_0 cid wbr fididg_0 fididg_0 wceq fididg_0 eqid fididg_0 fididg_0 fididg_1 ideqg mpbiri $.
$}
$( Two ways of expressing set existence.  (Contributed by NM, 16-Feb-2008.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) $)
${
	fissetid_0 $f class A $.
	issetid $p |- ( A e. _V <-> A _I A ) $= fissetid_0 cvv wcel fissetid_0 fissetid_0 cid wbr fissetid_0 cvv ididg fissetid_0 fissetid_0 cid reli brrelexi impbii $.
$}
$( Subclass theorem for composition.  (Contributed by FL, 30-Dec-2010.) $)
${
	$d A x y z $.
	$d B x y z $.
	$d C x y z $.
	icoss1_0 $f set x $.
	icoss1_1 $f set y $.
	icoss1_2 $f set z $.
	fcoss1_0 $f class A $.
	fcoss1_1 $f class B $.
	fcoss1_2 $f class C $.
	coss1 $p |- ( A C_ B -> ( A o. C ) C_ ( B o. C ) ) $= fcoss1_0 fcoss1_1 wss icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_0 wbr wa icoss1_1 wex icoss1_0 icoss1_2 copab icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_1 wbr wa icoss1_1 wex icoss1_0 icoss1_2 copab fcoss1_0 fcoss1_2 ccom fcoss1_1 fcoss1_2 ccom fcoss1_0 fcoss1_1 wss icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_0 wbr wa icoss1_1 wex icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_1 wbr wa icoss1_1 wex icoss1_0 icoss1_2 fcoss1_0 fcoss1_1 wss icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_0 wbr wa icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_1 wbr wa icoss1_1 fcoss1_0 fcoss1_1 wss icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_0 wbr icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_1 wbr icoss1_0 sup_set_class icoss1_1 sup_set_class fcoss1_2 wbr fcoss1_0 fcoss1_1 wss fcoss1_0 fcoss1_1 icoss1_1 sup_set_class icoss1_2 sup_set_class fcoss1_0 fcoss1_1 wss id ssbrd anim2d eximdv ssopab2dv icoss1_0 icoss1_2 icoss1_1 fcoss1_0 fcoss1_2 df-co icoss1_0 icoss1_2 icoss1_1 fcoss1_1 fcoss1_2 df-co 3sstr4g $.
$}
$( Subclass theorem for composition.  (Contributed by NM, 5-Apr-2013.) $)
${
	$d A x y z $.
	$d B x y z $.
	$d C x y z $.
	icoss2_0 $f set x $.
	icoss2_1 $f set y $.
	icoss2_2 $f set z $.
	fcoss2_0 $f class A $.
	fcoss2_1 $f class B $.
	fcoss2_2 $f class C $.
	coss2 $p |- ( A C_ B -> ( C o. A ) C_ ( C o. B ) ) $= fcoss2_0 fcoss2_1 wss icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_0 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr wa icoss2_1 wex icoss2_0 icoss2_2 copab icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_1 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr wa icoss2_1 wex icoss2_0 icoss2_2 copab fcoss2_2 fcoss2_0 ccom fcoss2_2 fcoss2_1 ccom fcoss2_0 fcoss2_1 wss icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_0 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr wa icoss2_1 wex icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_1 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr wa icoss2_1 wex icoss2_0 icoss2_2 fcoss2_0 fcoss2_1 wss icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_0 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr wa icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_1 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr wa icoss2_1 fcoss2_0 fcoss2_1 wss icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_0 wbr icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_1 wbr icoss2_1 sup_set_class icoss2_2 sup_set_class fcoss2_2 wbr fcoss2_0 fcoss2_1 wss fcoss2_0 fcoss2_1 icoss2_0 sup_set_class icoss2_1 sup_set_class fcoss2_0 fcoss2_1 wss id ssbrd anim1d eximdv ssopab2dv icoss2_0 icoss2_2 icoss2_1 fcoss2_2 fcoss2_0 df-co icoss2_0 icoss2_2 icoss2_1 fcoss2_2 fcoss2_1 df-co 3sstr4g $.
$}
$( Equality theorem for composition of two classes.  (Contributed by NM,
     3-Jan-1997.) $)
${
	fcoeq1_0 $f class A $.
	fcoeq1_1 $f class B $.
	fcoeq1_2 $f class C $.
	coeq1 $p |- ( A = B -> ( A o. C ) = ( B o. C ) ) $= fcoeq1_0 fcoeq1_1 wss fcoeq1_1 fcoeq1_0 wss wa fcoeq1_0 fcoeq1_2 ccom fcoeq1_1 fcoeq1_2 ccom wss fcoeq1_1 fcoeq1_2 ccom fcoeq1_0 fcoeq1_2 ccom wss wa fcoeq1_0 fcoeq1_1 wceq fcoeq1_0 fcoeq1_2 ccom fcoeq1_1 fcoeq1_2 ccom wceq fcoeq1_0 fcoeq1_1 wss fcoeq1_0 fcoeq1_2 ccom fcoeq1_1 fcoeq1_2 ccom wss fcoeq1_1 fcoeq1_0 wss fcoeq1_1 fcoeq1_2 ccom fcoeq1_0 fcoeq1_2 ccom wss fcoeq1_0 fcoeq1_1 fcoeq1_2 coss1 fcoeq1_1 fcoeq1_0 fcoeq1_2 coss1 anim12i fcoeq1_0 fcoeq1_1 eqss fcoeq1_0 fcoeq1_2 ccom fcoeq1_1 fcoeq1_2 ccom eqss 3imtr4i $.
$}
$( Equality theorem for composition of two classes.  (Contributed by NM,
     3-Jan-1997.) $)
${
	fcoeq2_0 $f class A $.
	fcoeq2_1 $f class B $.
	fcoeq2_2 $f class C $.
	coeq2 $p |- ( A = B -> ( C o. A ) = ( C o. B ) ) $= fcoeq2_0 fcoeq2_1 wss fcoeq2_1 fcoeq2_0 wss wa fcoeq2_2 fcoeq2_0 ccom fcoeq2_2 fcoeq2_1 ccom wss fcoeq2_2 fcoeq2_1 ccom fcoeq2_2 fcoeq2_0 ccom wss wa fcoeq2_0 fcoeq2_1 wceq fcoeq2_2 fcoeq2_0 ccom fcoeq2_2 fcoeq2_1 ccom wceq fcoeq2_0 fcoeq2_1 wss fcoeq2_2 fcoeq2_0 ccom fcoeq2_2 fcoeq2_1 ccom wss fcoeq2_1 fcoeq2_0 wss fcoeq2_2 fcoeq2_1 ccom fcoeq2_2 fcoeq2_0 ccom wss fcoeq2_0 fcoeq2_1 fcoeq2_2 coss2 fcoeq2_1 fcoeq2_0 fcoeq2_2 coss2 anim12i fcoeq2_0 fcoeq2_1 eqss fcoeq2_2 fcoeq2_0 ccom fcoeq2_2 fcoeq2_1 ccom eqss 3imtr4i $.
$}
$( Equality inference for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
${
	fcoeq1i_0 $f class A $.
	fcoeq1i_1 $f class B $.
	fcoeq1i_2 $f class C $.
	ecoeq1i_0 $e |- A = B $.
	coeq1i $p |- ( A o. C ) = ( B o. C ) $= fcoeq1i_0 fcoeq1i_1 wceq fcoeq1i_0 fcoeq1i_2 ccom fcoeq1i_1 fcoeq1i_2 ccom wceq ecoeq1i_0 fcoeq1i_0 fcoeq1i_1 fcoeq1i_2 coeq1 ax-mp $.
$}
$( Equality inference for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
${
	fcoeq2i_0 $f class A $.
	fcoeq2i_1 $f class B $.
	fcoeq2i_2 $f class C $.
	ecoeq2i_0 $e |- A = B $.
	coeq2i $p |- ( C o. A ) = ( C o. B ) $= fcoeq2i_0 fcoeq2i_1 wceq fcoeq2i_2 fcoeq2i_0 ccom fcoeq2i_2 fcoeq2i_1 ccom wceq ecoeq2i_0 fcoeq2i_0 fcoeq2i_1 fcoeq2i_2 coeq2 ax-mp $.
$}
$( Equality deduction for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
${
	fcoeq1d_0 $f wff ph $.
	fcoeq1d_1 $f class A $.
	fcoeq1d_2 $f class B $.
	fcoeq1d_3 $f class C $.
	ecoeq1d_0 $e |- ( ph -> A = B ) $.
	coeq1d $p |- ( ph -> ( A o. C ) = ( B o. C ) ) $= fcoeq1d_0 fcoeq1d_1 fcoeq1d_2 wceq fcoeq1d_1 fcoeq1d_3 ccom fcoeq1d_2 fcoeq1d_3 ccom wceq ecoeq1d_0 fcoeq1d_1 fcoeq1d_2 fcoeq1d_3 coeq1 syl $.
$}
$( Equality deduction for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
${
	fcoeq2d_0 $f wff ph $.
	fcoeq2d_1 $f class A $.
	fcoeq2d_2 $f class B $.
	fcoeq2d_3 $f class C $.
	ecoeq2d_0 $e |- ( ph -> A = B ) $.
	coeq2d $p |- ( ph -> ( C o. A ) = ( C o. B ) ) $= fcoeq2d_0 fcoeq2d_1 fcoeq2d_2 wceq fcoeq2d_3 fcoeq2d_1 ccom fcoeq2d_3 fcoeq2d_2 ccom wceq ecoeq2d_0 fcoeq2d_1 fcoeq2d_2 fcoeq2d_3 coeq2 syl $.
$}
$( Equality inference for composition of two classes.  (Contributed by FL,
       7-Jun-2012.) $)
${
	fcoeq12i_0 $f class A $.
	fcoeq12i_1 $f class B $.
	fcoeq12i_2 $f class C $.
	fcoeq12i_3 $f class D $.
	ecoeq12i_0 $e |- A = B $.
	ecoeq12i_1 $e |- C = D $.
	coeq12i $p |- ( A o. C ) = ( B o. D ) $= fcoeq12i_0 fcoeq12i_2 ccom fcoeq12i_1 fcoeq12i_2 ccom fcoeq12i_1 fcoeq12i_3 ccom fcoeq12i_0 fcoeq12i_1 fcoeq12i_2 ecoeq12i_0 coeq1i fcoeq12i_2 fcoeq12i_3 fcoeq12i_1 ecoeq12i_1 coeq2i eqtri $.
$}
$( Equality deduction for composition of two classes.  (Contributed by FL,
       7-Jun-2012.) $)
${
	fcoeq12d_0 $f wff ph $.
	fcoeq12d_1 $f class A $.
	fcoeq12d_2 $f class B $.
	fcoeq12d_3 $f class C $.
	fcoeq12d_4 $f class D $.
	ecoeq12d_0 $e |- ( ph -> A = B ) $.
	ecoeq12d_1 $e |- ( ph -> C = D ) $.
	coeq12d $p |- ( ph -> ( A o. C ) = ( B o. D ) ) $= fcoeq12d_0 fcoeq12d_1 fcoeq12d_3 ccom fcoeq12d_2 fcoeq12d_3 ccom fcoeq12d_2 fcoeq12d_4 ccom fcoeq12d_0 fcoeq12d_1 fcoeq12d_2 fcoeq12d_3 ecoeq12d_0 coeq1d fcoeq12d_0 fcoeq12d_3 fcoeq12d_4 fcoeq12d_2 ecoeq12d_1 coeq2d eqtrd $.
$}
$( Bound-variable hypothesis builder for function value.  (Contributed by
       NM, 1-Sep-1999.) $)
${
	$d w x y z $.
	$d y z w A $.
	$d y z w B $.
	infco_0 $f set y $.
	infco_1 $f set z $.
	infco_2 $f set w $.
	fnfco_0 $f set x $.
	fnfco_1 $f class A $.
	fnfco_2 $f class B $.
	enfco_0 $e |- F/_ x A $.
	enfco_1 $e |- F/_ x B $.
	nfco $p |- F/_ x ( A o. B ) $= fnfco_0 fnfco_1 fnfco_2 ccom infco_0 sup_set_class infco_2 sup_set_class fnfco_2 wbr infco_2 sup_set_class infco_1 sup_set_class fnfco_1 wbr wa infco_2 wex infco_0 infco_1 copab infco_0 infco_1 infco_2 fnfco_1 fnfco_2 df-co infco_0 sup_set_class infco_2 sup_set_class fnfco_2 wbr infco_2 sup_set_class infco_1 sup_set_class fnfco_1 wbr wa infco_2 wex infco_0 infco_1 fnfco_0 infco_0 sup_set_class infco_2 sup_set_class fnfco_2 wbr infco_2 sup_set_class infco_1 sup_set_class fnfco_1 wbr wa fnfco_0 infco_2 infco_0 sup_set_class infco_2 sup_set_class fnfco_2 wbr infco_2 sup_set_class infco_1 sup_set_class fnfco_1 wbr fnfco_0 fnfco_0 infco_0 sup_set_class infco_2 sup_set_class fnfco_2 fnfco_0 infco_0 sup_set_class nfcv enfco_1 fnfco_0 infco_2 sup_set_class nfcv nfbr fnfco_0 infco_2 sup_set_class infco_1 sup_set_class fnfco_1 fnfco_0 infco_2 sup_set_class nfcv enfco_0 fnfco_0 infco_1 sup_set_class nfcv nfbr nfan nfex nfopab nfcxfr $.
$}
$( Ordered pair membership in a composition.  (Contributed by NM,
       24-Feb-2015.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	$d x y z D $.
	ibrcog_0 $f set y $.
	ibrcog_1 $f set z $.
	fbrcog_0 $f set x $.
	fbrcog_1 $f class A $.
	fbrcog_2 $f class B $.
	fbrcog_3 $f class C $.
	fbrcog_4 $f class D $.
	fbrcog_5 $f class V $.
	fbrcog_6 $f class W $.
	brcog $p |- ( ( A e. V /\ B e. W ) -> ( A ( C o. D ) B <-> E. x ( A D x /\ x C B ) ) ) $= ibrcog_0 sup_set_class fbrcog_0 sup_set_class fbrcog_4 wbr fbrcog_0 sup_set_class ibrcog_1 sup_set_class fbrcog_3 wbr wa fbrcog_0 wex fbrcog_1 fbrcog_0 sup_set_class fbrcog_4 wbr fbrcog_0 sup_set_class fbrcog_2 fbrcog_3 wbr wa fbrcog_0 wex ibrcog_0 ibrcog_1 fbrcog_1 fbrcog_2 fbrcog_3 fbrcog_4 ccom fbrcog_5 fbrcog_6 ibrcog_0 sup_set_class fbrcog_1 wceq ibrcog_1 sup_set_class fbrcog_2 wceq wa ibrcog_0 sup_set_class fbrcog_0 sup_set_class fbrcog_4 wbr fbrcog_0 sup_set_class ibrcog_1 sup_set_class fbrcog_3 wbr wa fbrcog_1 fbrcog_0 sup_set_class fbrcog_4 wbr fbrcog_0 sup_set_class fbrcog_2 fbrcog_3 wbr wa fbrcog_0 ibrcog_0 sup_set_class fbrcog_1 wceq ibrcog_0 sup_set_class fbrcog_0 sup_set_class fbrcog_4 wbr fbrcog_1 fbrcog_0 sup_set_class fbrcog_4 wbr ibrcog_1 sup_set_class fbrcog_2 wceq fbrcog_0 sup_set_class ibrcog_1 sup_set_class fbrcog_3 wbr fbrcog_0 sup_set_class fbrcog_2 fbrcog_3 wbr ibrcog_0 sup_set_class fbrcog_1 fbrcog_0 sup_set_class fbrcog_4 breq1 ibrcog_1 sup_set_class fbrcog_2 fbrcog_0 sup_set_class fbrcog_3 breq2 bi2anan9 exbidv ibrcog_0 ibrcog_1 fbrcog_0 fbrcog_3 fbrcog_4 df-co brabga $.
$}
$( Ordered pair membership in a composition.  (Contributed by NM,
       27-Jan-1997.)  (Revised by Mario Carneiro, 24-Feb-2015.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	fopelco2g_0 $f set x $.
	fopelco2g_1 $f class A $.
	fopelco2g_2 $f class B $.
	fopelco2g_3 $f class C $.
	fopelco2g_4 $f class D $.
	fopelco2g_5 $f class V $.
	fopelco2g_6 $f class W $.
	opelco2g $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. ( C o. D ) <-> E. x ( <. A , x >. e. D /\ <. x , B >. e. C ) ) ) $= fopelco2g_1 fopelco2g_5 wcel fopelco2g_2 fopelco2g_6 wcel wa fopelco2g_1 fopelco2g_2 fopelco2g_3 fopelco2g_4 ccom wbr fopelco2g_1 fopelco2g_0 sup_set_class fopelco2g_4 wbr fopelco2g_0 sup_set_class fopelco2g_2 fopelco2g_3 wbr wa fopelco2g_0 wex fopelco2g_1 fopelco2g_2 cop fopelco2g_3 fopelco2g_4 ccom wcel fopelco2g_1 fopelco2g_0 sup_set_class cop fopelco2g_4 wcel fopelco2g_0 sup_set_class fopelco2g_2 cop fopelco2g_3 wcel wa fopelco2g_0 wex fopelco2g_0 fopelco2g_1 fopelco2g_2 fopelco2g_3 fopelco2g_4 fopelco2g_5 fopelco2g_6 brcog fopelco2g_1 fopelco2g_2 fopelco2g_3 fopelco2g_4 ccom df-br fopelco2g_1 fopelco2g_0 sup_set_class fopelco2g_4 wbr fopelco2g_0 sup_set_class fopelco2g_2 fopelco2g_3 wbr wa fopelco2g_1 fopelco2g_0 sup_set_class cop fopelco2g_4 wcel fopelco2g_0 sup_set_class fopelco2g_2 cop fopelco2g_3 wcel wa fopelco2g_0 fopelco2g_1 fopelco2g_0 sup_set_class fopelco2g_4 wbr fopelco2g_1 fopelco2g_0 sup_set_class cop fopelco2g_4 wcel fopelco2g_0 sup_set_class fopelco2g_2 fopelco2g_3 wbr fopelco2g_0 sup_set_class fopelco2g_2 cop fopelco2g_3 wcel fopelco2g_1 fopelco2g_0 sup_set_class fopelco2g_4 df-br fopelco2g_0 sup_set_class fopelco2g_2 fopelco2g_3 df-br anbi12i exbii 3bitr3g $.
$}
$( Binary relation on a composition.  (Contributed by NM, 21-Sep-2004.)
       (Revised by Mario Carneiro, 24-Feb-2015.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	fbrco_0 $f set x $.
	fbrco_1 $f class A $.
	fbrco_2 $f class B $.
	fbrco_3 $f class C $.
	fbrco_4 $f class D $.
	ebrco_0 $e |- A e. _V $.
	ebrco_1 $e |- B e. _V $.
	brco $p |- ( A ( C o. D ) B <-> E. x ( A D x /\ x C B ) ) $= fbrco_1 cvv wcel fbrco_2 cvv wcel fbrco_1 fbrco_2 fbrco_3 fbrco_4 ccom wbr fbrco_1 fbrco_0 sup_set_class fbrco_4 wbr fbrco_0 sup_set_class fbrco_2 fbrco_3 wbr wa fbrco_0 wex wb ebrco_0 ebrco_1 fbrco_0 fbrco_1 fbrco_2 fbrco_3 fbrco_4 cvv cvv brcog mp2an $.
$}
$( Ordered pair membership in a composition.  (Contributed by NM,
       27-Dec-1996.)  (Revised by Mario Carneiro, 24-Feb-2015.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	$d x D $.
	fopelco_0 $f set x $.
	fopelco_1 $f class A $.
	fopelco_2 $f class B $.
	fopelco_3 $f class C $.
	fopelco_4 $f class D $.
	eopelco_0 $e |- A e. _V $.
	eopelco_1 $e |- B e. _V $.
	opelco $p |- ( <. A , B >. e. ( C o. D ) <-> E. x ( A D x /\ x C B ) ) $= fopelco_1 fopelco_2 cop fopelco_3 fopelco_4 ccom wcel fopelco_1 fopelco_2 fopelco_3 fopelco_4 ccom wbr fopelco_1 fopelco_0 sup_set_class fopelco_4 wbr fopelco_0 sup_set_class fopelco_2 fopelco_3 wbr wa fopelco_0 wex fopelco_1 fopelco_2 fopelco_3 fopelco_4 ccom df-br fopelco_0 fopelco_1 fopelco_2 fopelco_3 fopelco_4 eopelco_0 eopelco_1 brco bitr3i $.
$}
$( Subset theorem for converse.  (Contributed by NM, 22-Mar-1998.) $)
${
	$d x y A $.
	$d x y B $.
	icnvss_0 $f set x $.
	icnvss_1 $f set y $.
	fcnvss_0 $f class A $.
	fcnvss_1 $f class B $.
	cnvss $p |- ( A C_ B -> `' A C_ `' B ) $= fcnvss_0 fcnvss_1 wss icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_0 wbr icnvss_0 icnvss_1 copab icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_1 wbr icnvss_0 icnvss_1 copab fcnvss_0 ccnv fcnvss_1 ccnv fcnvss_0 fcnvss_1 wss icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_0 wbr icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_1 wbr icnvss_0 icnvss_1 fcnvss_0 fcnvss_1 wss icnvss_1 sup_set_class icnvss_0 sup_set_class cop fcnvss_0 wcel icnvss_1 sup_set_class icnvss_0 sup_set_class cop fcnvss_1 wcel icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_0 wbr icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_1 wbr fcnvss_0 fcnvss_1 icnvss_1 sup_set_class icnvss_0 sup_set_class cop ssel icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_0 df-br icnvss_1 sup_set_class icnvss_0 sup_set_class fcnvss_1 df-br 3imtr4g ssopab2dv icnvss_0 icnvss_1 fcnvss_0 df-cnv icnvss_0 icnvss_1 fcnvss_1 df-cnv 3sstr4g $.
$}
$( Equality theorem for converse.  (Contributed by NM, 13-Aug-1995.) $)
${
	fcnveq_0 $f class A $.
	fcnveq_1 $f class B $.
	cnveq $p |- ( A = B -> `' A = `' B ) $= fcnveq_0 fcnveq_1 wss fcnveq_1 fcnveq_0 wss wa fcnveq_0 ccnv fcnveq_1 ccnv wss fcnveq_1 ccnv fcnveq_0 ccnv wss wa fcnveq_0 fcnveq_1 wceq fcnveq_0 ccnv fcnveq_1 ccnv wceq fcnveq_0 fcnveq_1 wss fcnveq_0 ccnv fcnveq_1 ccnv wss fcnveq_1 fcnveq_0 wss fcnveq_1 ccnv fcnveq_0 ccnv wss fcnveq_0 fcnveq_1 cnvss fcnveq_1 fcnveq_0 cnvss anim12i fcnveq_0 fcnveq_1 eqss fcnveq_0 ccnv fcnveq_1 ccnv eqss 3imtr4i $.
$}
$( Equality inference for converse.  (Contributed by NM, 23-Dec-2008.) $)
${
	fcnveqi_0 $f class A $.
	fcnveqi_1 $f class B $.
	ecnveqi_0 $e |- A = B $.
	cnveqi $p |- `' A = `' B $= fcnveqi_0 fcnveqi_1 wceq fcnveqi_0 ccnv fcnveqi_1 ccnv wceq ecnveqi_0 fcnveqi_0 fcnveqi_1 cnveq ax-mp $.
$}
$( Equality deduction for converse.  (Contributed by NM, 6-Dec-2013.) $)
${
	fcnveqd_0 $f wff ph $.
	fcnveqd_1 $f class A $.
	fcnveqd_2 $f class B $.
	ecnveqd_0 $e |- ( ph -> A = B ) $.
	cnveqd $p |- ( ph -> `' A = `' B ) $= fcnveqd_0 fcnveqd_1 fcnveqd_2 wceq fcnveqd_1 ccnv fcnveqd_2 ccnv wceq ecnveqd_0 fcnveqd_1 fcnveqd_2 cnveq syl $.
$}
$( Membership in a converse.  Equation 5 of [Suppes] p. 62.  (Contributed
       by NM, 24-Mar-1998.) $)
${
	$d x y A $.
	$d x y R $.
	felcnv_0 $f set x $.
	felcnv_1 $f set y $.
	felcnv_2 $f class A $.
	felcnv_3 $f class R $.
	elcnv $p |- ( A e. `' R <-> E. x E. y ( A = <. x , y >. /\ y R x ) ) $= felcnv_2 felcnv_3 ccnv wcel felcnv_2 felcnv_1 sup_set_class felcnv_0 sup_set_class felcnv_3 wbr felcnv_0 felcnv_1 copab wcel felcnv_2 felcnv_0 sup_set_class felcnv_1 sup_set_class cop wceq felcnv_1 sup_set_class felcnv_0 sup_set_class felcnv_3 wbr wa felcnv_1 wex felcnv_0 wex felcnv_3 ccnv felcnv_1 sup_set_class felcnv_0 sup_set_class felcnv_3 wbr felcnv_0 felcnv_1 copab felcnv_2 felcnv_0 felcnv_1 felcnv_3 df-cnv eleq2i felcnv_1 sup_set_class felcnv_0 sup_set_class felcnv_3 wbr felcnv_0 felcnv_1 felcnv_2 elopab bitri $.
$}
$( Membership in a converse.  Equation 5 of [Suppes] p. 62.  (Contributed
       by NM, 11-Aug-2004.) $)
${
	$d x y A $.
	$d x y R $.
	felcnv2_0 $f set x $.
	felcnv2_1 $f set y $.
	felcnv2_2 $f class A $.
	felcnv2_3 $f class R $.
	elcnv2 $p |- ( A e. `' R <-> E. x E. y ( A = <. x , y >. /\ <. y , x >. e. R ) ) $= felcnv2_2 felcnv2_3 ccnv wcel felcnv2_2 felcnv2_0 sup_set_class felcnv2_1 sup_set_class cop wceq felcnv2_1 sup_set_class felcnv2_0 sup_set_class felcnv2_3 wbr wa felcnv2_1 wex felcnv2_0 wex felcnv2_2 felcnv2_0 sup_set_class felcnv2_1 sup_set_class cop wceq felcnv2_1 sup_set_class felcnv2_0 sup_set_class cop felcnv2_3 wcel wa felcnv2_1 wex felcnv2_0 wex felcnv2_0 felcnv2_1 felcnv2_2 felcnv2_3 elcnv felcnv2_2 felcnv2_0 sup_set_class felcnv2_1 sup_set_class cop wceq felcnv2_1 sup_set_class felcnv2_0 sup_set_class felcnv2_3 wbr wa felcnv2_2 felcnv2_0 sup_set_class felcnv2_1 sup_set_class cop wceq felcnv2_1 sup_set_class felcnv2_0 sup_set_class cop felcnv2_3 wcel wa felcnv2_0 felcnv2_1 felcnv2_1 sup_set_class felcnv2_0 sup_set_class felcnv2_3 wbr felcnv2_1 sup_set_class felcnv2_0 sup_set_class cop felcnv2_3 wcel felcnv2_2 felcnv2_0 sup_set_class felcnv2_1 sup_set_class cop wceq felcnv2_1 sup_set_class felcnv2_0 sup_set_class felcnv2_3 df-br anbi2i 2exbii bitri $.
$}
$( Bound-variable hypothesis builder for converse.  (Contributed by NM,
       31-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$d y z A $.
	$d x y z $.
	infcnv_0 $f set y $.
	infcnv_1 $f set z $.
	fnfcnv_0 $f set x $.
	fnfcnv_1 $f class A $.
	enfcnv_0 $e |- F/_ x A $.
	nfcnv $p |- F/_ x `' A $= fnfcnv_0 fnfcnv_1 ccnv infcnv_1 sup_set_class infcnv_0 sup_set_class fnfcnv_1 wbr infcnv_0 infcnv_1 copab infcnv_0 infcnv_1 fnfcnv_1 df-cnv infcnv_1 sup_set_class infcnv_0 sup_set_class fnfcnv_1 wbr infcnv_0 infcnv_1 fnfcnv_0 fnfcnv_0 infcnv_1 sup_set_class infcnv_0 sup_set_class fnfcnv_1 fnfcnv_0 infcnv_1 sup_set_class nfcv enfcnv_0 fnfcnv_0 infcnv_0 sup_set_class nfcv nfbr nfopab nfcxfr $.
$}
$( Ordered-pair membership in converse.  (Contributed by NM, 13-May-1999.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	iopelcnvg_0 $f set x $.
	iopelcnvg_1 $f set y $.
	fopelcnvg_0 $f class A $.
	fopelcnvg_1 $f class B $.
	fopelcnvg_2 $f class C $.
	fopelcnvg_3 $f class D $.
	fopelcnvg_4 $f class R $.
	opelcnvg $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e. `' R <-> <. B , A >. e. R ) ) $= fopelcnvg_0 fopelcnvg_2 wcel fopelcnvg_1 fopelcnvg_3 wcel wa fopelcnvg_0 fopelcnvg_1 fopelcnvg_4 ccnv wbr fopelcnvg_1 fopelcnvg_0 fopelcnvg_4 wbr fopelcnvg_0 fopelcnvg_1 cop fopelcnvg_4 ccnv wcel fopelcnvg_1 fopelcnvg_0 cop fopelcnvg_4 wcel iopelcnvg_1 sup_set_class iopelcnvg_0 sup_set_class fopelcnvg_4 wbr iopelcnvg_1 sup_set_class fopelcnvg_0 fopelcnvg_4 wbr fopelcnvg_1 fopelcnvg_0 fopelcnvg_4 wbr iopelcnvg_0 iopelcnvg_1 fopelcnvg_0 fopelcnvg_1 fopelcnvg_2 fopelcnvg_3 fopelcnvg_4 ccnv iopelcnvg_0 sup_set_class fopelcnvg_0 iopelcnvg_1 sup_set_class fopelcnvg_4 breq2 iopelcnvg_1 sup_set_class fopelcnvg_1 fopelcnvg_0 fopelcnvg_4 breq1 iopelcnvg_0 iopelcnvg_1 fopelcnvg_4 df-cnv brabg fopelcnvg_0 fopelcnvg_1 fopelcnvg_4 ccnv df-br fopelcnvg_1 fopelcnvg_0 fopelcnvg_4 df-br 3bitr3g $.
$}
$( The converse of a binary relation swaps arguments.  Theorem 11 of [Suppes]
     p. 61.  (Contributed by NM, 10-Oct-2005.) $)
${
	fbrcnvg_0 $f class A $.
	fbrcnvg_1 $f class B $.
	fbrcnvg_2 $f class C $.
	fbrcnvg_3 $f class D $.
	fbrcnvg_4 $f class R $.
	brcnvg $p |- ( ( A e. C /\ B e. D ) -> ( A `' R B <-> B R A ) ) $= fbrcnvg_0 fbrcnvg_2 wcel fbrcnvg_1 fbrcnvg_3 wcel wa fbrcnvg_0 fbrcnvg_1 cop fbrcnvg_4 ccnv wcel fbrcnvg_1 fbrcnvg_0 cop fbrcnvg_4 wcel fbrcnvg_0 fbrcnvg_1 fbrcnvg_4 ccnv wbr fbrcnvg_1 fbrcnvg_0 fbrcnvg_4 wbr fbrcnvg_0 fbrcnvg_1 fbrcnvg_2 fbrcnvg_3 fbrcnvg_4 opelcnvg fbrcnvg_0 fbrcnvg_1 fbrcnvg_4 ccnv df-br fbrcnvg_1 fbrcnvg_0 fbrcnvg_4 df-br 3bitr4g $.
$}
$( Ordered-pair membership in converse.  (Contributed by NM,
       13-Aug-1995.) $)
${
	fopelcnv_0 $f class A $.
	fopelcnv_1 $f class B $.
	fopelcnv_2 $f class R $.
	eopelcnv_0 $e |- A e. _V $.
	eopelcnv_1 $e |- B e. _V $.
	opelcnv $p |- ( <. A , B >. e. `' R <-> <. B , A >. e. R ) $= fopelcnv_0 cvv wcel fopelcnv_1 cvv wcel fopelcnv_0 fopelcnv_1 cop fopelcnv_2 ccnv wcel fopelcnv_1 fopelcnv_0 cop fopelcnv_2 wcel wb eopelcnv_0 eopelcnv_1 fopelcnv_0 fopelcnv_1 cvv cvv fopelcnv_2 opelcnvg mp2an $.
$}
$( The converse of a binary relation swaps arguments.  Theorem 11 of
       [Suppes] p. 61.  (Contributed by NM, 13-Aug-1995.) $)
${
	fbrcnv_0 $f class A $.
	fbrcnv_1 $f class B $.
	fbrcnv_2 $f class R $.
	ebrcnv_0 $e |- A e. _V $.
	ebrcnv_1 $e |- B e. _V $.
	brcnv $p |- ( A `' R B <-> B R A ) $= fbrcnv_0 cvv wcel fbrcnv_1 cvv wcel fbrcnv_0 fbrcnv_1 fbrcnv_2 ccnv wbr fbrcnv_1 fbrcnv_0 fbrcnv_2 wbr wb ebrcnv_0 ebrcnv_1 fbrcnv_0 fbrcnv_1 cvv cvv fbrcnv_2 brcnvg mp2an $.
$}
$( Distributive law of converse over class composition.  Theorem 26 of
       [Suppes] p. 64.  (Contributed by NM, 19-Mar-1998.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	icnvco_0 $f set x $.
	icnvco_1 $f set y $.
	icnvco_2 $f set z $.
	fcnvco_0 $f class A $.
	fcnvco_1 $f class B $.
	cnvco $p |- `' ( A o. B ) = ( `' B o. `' A ) $= icnvco_0 sup_set_class icnvco_1 sup_set_class fcnvco_0 fcnvco_1 ccom wbr icnvco_1 icnvco_0 copab icnvco_1 sup_set_class icnvco_2 sup_set_class fcnvco_0 ccnv wbr icnvco_2 sup_set_class icnvco_0 sup_set_class fcnvco_1 ccnv wbr wa icnvco_2 wex icnvco_1 icnvco_0 copab fcnvco_0 fcnvco_1 ccom ccnv fcnvco_1 ccnv fcnvco_0 ccnv ccom icnvco_0 sup_set_class icnvco_1 sup_set_class fcnvco_0 fcnvco_1 ccom wbr icnvco_1 sup_set_class icnvco_2 sup_set_class fcnvco_0 ccnv wbr icnvco_2 sup_set_class icnvco_0 sup_set_class fcnvco_1 ccnv wbr wa icnvco_2 wex icnvco_1 icnvco_0 icnvco_0 sup_set_class icnvco_2 sup_set_class fcnvco_1 wbr icnvco_2 sup_set_class icnvco_1 sup_set_class fcnvco_0 wbr wa icnvco_2 wex icnvco_2 sup_set_class icnvco_1 sup_set_class fcnvco_0 wbr icnvco_0 sup_set_class icnvco_2 sup_set_class fcnvco_1 wbr wa icnvco_2 wex icnvco_0 sup_set_class icnvco_1 sup_set_class fcnvco_0 fcnvco_1 ccom wbr icnvco_1 sup_set_class icnvco_2 sup_set_class fcnvco_0 ccnv wbr icnvco_2 sup_set_class icnvco_0 sup_set_class fcnvco_1 ccnv wbr wa icnvco_2 wex icnvco_0 sup_set_class icnvco_2 sup_set_class fcnvco_1 wbr icnvco_2 sup_set_class icnvco_1 sup_set_class fcnvco_0 wbr icnvco_2 exancom icnvco_2 icnvco_0 sup_set_class icnvco_1 sup_set_class fcnvco_0 fcnvco_1 icnvco_0 vex icnvco_1 vex brco icnvco_1 sup_set_class icnvco_2 sup_set_class fcnvco_0 ccnv wbr icnvco_2 sup_set_class icnvco_0 sup_set_class fcnvco_1 ccnv wbr wa icnvco_2 sup_set_class icnvco_1 sup_set_class fcnvco_0 wbr icnvco_0 sup_set_class icnvco_2 sup_set_class fcnvco_1 wbr wa icnvco_2 icnvco_1 sup_set_class icnvco_2 sup_set_class fcnvco_0 ccnv wbr icnvco_2 sup_set_class icnvco_1 sup_set_class fcnvco_0 wbr icnvco_2 sup_set_class icnvco_0 sup_set_class fcnvco_1 ccnv wbr icnvco_0 sup_set_class icnvco_2 sup_set_class fcnvco_1 wbr icnvco_1 sup_set_class icnvco_2 sup_set_class fcnvco_0 icnvco_1 vex icnvco_2 vex brcnv icnvco_2 sup_set_class icnvco_0 sup_set_class fcnvco_1 icnvco_2 vex icnvco_0 vex brcnv anbi12i exbii 3bitr4i opabbii icnvco_1 icnvco_0 fcnvco_0 fcnvco_1 ccom df-cnv icnvco_1 icnvco_0 icnvco_2 fcnvco_1 ccnv fcnvco_0 ccnv df-co 3eqtr4i $.
$}
$( The converse of a class union is the (indexed) union of the converses of
       its members.  (Contributed by NM, 11-Aug-2004.) $)
${
	$d x y z w A $.
	icnvuni_0 $f set y $.
	icnvuni_1 $f set z $.
	icnvuni_2 $f set w $.
	fcnvuni_0 $f set x $.
	fcnvuni_1 $f class A $.
	cnvuni $p |- `' U. A = U_ x e. A `' x $= icnvuni_0 fcnvuni_1 cuni ccnv fcnvuni_0 fcnvuni_1 fcnvuni_0 sup_set_class ccnv ciun icnvuni_0 sup_set_class fcnvuni_1 cuni ccnv wcel icnvuni_0 sup_set_class fcnvuni_0 sup_set_class ccnv wcel fcnvuni_0 fcnvuni_1 wrex icnvuni_0 sup_set_class fcnvuni_0 fcnvuni_1 fcnvuni_0 sup_set_class ccnv ciun wcel icnvuni_0 sup_set_class fcnvuni_1 cuni ccnv wcel icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_1 cuni wcel wa icnvuni_2 wex icnvuni_1 wex icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa fcnvuni_0 fcnvuni_1 wrex icnvuni_2 wex icnvuni_1 wex icnvuni_0 sup_set_class fcnvuni_0 sup_set_class ccnv wcel fcnvuni_0 fcnvuni_1 wrex icnvuni_1 icnvuni_2 icnvuni_0 sup_set_class fcnvuni_1 cuni elcnv2 icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_1 cuni wcel wa icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa fcnvuni_0 fcnvuni_1 wrex icnvuni_1 icnvuni_2 icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_1 cuni wcel wa icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel fcnvuni_0 fcnvuni_1 wrex wa icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa fcnvuni_0 fcnvuni_1 wrex icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_1 cuni wcel icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel fcnvuni_0 fcnvuni_1 wrex icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq fcnvuni_0 icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_1 eluni2 anbi2i icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel fcnvuni_0 fcnvuni_1 r19.42v bitr4i 2exbii icnvuni_0 sup_set_class fcnvuni_0 sup_set_class ccnv wcel fcnvuni_0 fcnvuni_1 wrex icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa icnvuni_2 wex icnvuni_1 wex fcnvuni_0 fcnvuni_1 wrex icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa icnvuni_2 wex fcnvuni_0 fcnvuni_1 wrex icnvuni_1 wex icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa fcnvuni_0 fcnvuni_1 wrex icnvuni_2 wex icnvuni_1 wex icnvuni_0 sup_set_class fcnvuni_0 sup_set_class ccnv wcel icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa icnvuni_2 wex icnvuni_1 wex fcnvuni_0 fcnvuni_1 icnvuni_1 icnvuni_2 icnvuni_0 sup_set_class fcnvuni_0 sup_set_class elcnv2 rexbii icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa icnvuni_2 wex fcnvuni_0 icnvuni_1 fcnvuni_1 rexcom4 icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa icnvuni_2 wex fcnvuni_0 fcnvuni_1 wrex icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa fcnvuni_0 fcnvuni_1 wrex icnvuni_2 wex icnvuni_1 icnvuni_0 sup_set_class icnvuni_1 sup_set_class icnvuni_2 sup_set_class cop wceq icnvuni_2 sup_set_class icnvuni_1 sup_set_class cop fcnvuni_0 sup_set_class wcel wa fcnvuni_0 icnvuni_2 fcnvuni_1 rexcom4 exbii 3bitrri 3bitri fcnvuni_0 icnvuni_0 sup_set_class fcnvuni_1 fcnvuni_0 sup_set_class ccnv eliun bitr4i eqriv $.
$}
$( Alternate definition of domain.  Definition 6.5(1) of [TakeutiZaring]
       p. 24.  (Contributed by NM, 28-Dec-1996.) $)
${
	$d x y A $.
	fdfdm3_0 $f set x $.
	fdfdm3_1 $f set y $.
	fdfdm3_2 $f class A $.
	dfdm3 $p |- dom A = { x | E. y <. x , y >. e. A } $= fdfdm3_2 cdm fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class fdfdm3_2 wbr fdfdm3_1 wex fdfdm3_0 cab fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class cop fdfdm3_2 wcel fdfdm3_1 wex fdfdm3_0 cab fdfdm3_0 fdfdm3_1 fdfdm3_2 df-dm fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class fdfdm3_2 wbr fdfdm3_1 wex fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class cop fdfdm3_2 wcel fdfdm3_1 wex fdfdm3_0 fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class fdfdm3_2 wbr fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class cop fdfdm3_2 wcel fdfdm3_1 fdfdm3_0 sup_set_class fdfdm3_1 sup_set_class fdfdm3_2 df-br exbii abbii eqtri $.
$}
$( Alternate definition of range.  Definition 4 of [Suppes] p. 60.
       (Contributed by NM, 27-Dec-1996.) $)
${
	$d x y A $.
	fdfrn2_0 $f set x $.
	fdfrn2_1 $f set y $.
	fdfrn2_2 $f class A $.
	dfrn2 $p |- ran A = { y | E. x x A y } $= fdfrn2_2 crn fdfrn2_2 ccnv cdm fdfrn2_1 sup_set_class fdfrn2_0 sup_set_class fdfrn2_2 ccnv wbr fdfrn2_0 wex fdfrn2_1 cab fdfrn2_0 sup_set_class fdfrn2_1 sup_set_class fdfrn2_2 wbr fdfrn2_0 wex fdfrn2_1 cab fdfrn2_2 df-rn fdfrn2_1 fdfrn2_0 fdfrn2_2 ccnv df-dm fdfrn2_1 sup_set_class fdfrn2_0 sup_set_class fdfrn2_2 ccnv wbr fdfrn2_0 wex fdfrn2_0 sup_set_class fdfrn2_1 sup_set_class fdfrn2_2 wbr fdfrn2_0 wex fdfrn2_1 fdfrn2_1 sup_set_class fdfrn2_0 sup_set_class fdfrn2_2 ccnv wbr fdfrn2_0 sup_set_class fdfrn2_1 sup_set_class fdfrn2_2 wbr fdfrn2_0 fdfrn2_1 sup_set_class fdfrn2_0 sup_set_class fdfrn2_2 fdfrn2_1 vex fdfrn2_0 vex brcnv exbii abbii 3eqtri $.
$}
$( Alternate definition of range.  Definition 6.5(2) of [TakeutiZaring]
       p. 24.  (Contributed by NM, 28-Dec-1996.) $)
${
	$d x y A $.
	fdfrn3_0 $f set x $.
	fdfrn3_1 $f set y $.
	fdfrn3_2 $f class A $.
	dfrn3 $p |- ran A = { y | E. x <. x , y >. e. A } $= fdfrn3_2 crn fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class fdfrn3_2 wbr fdfrn3_0 wex fdfrn3_1 cab fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class cop fdfrn3_2 wcel fdfrn3_0 wex fdfrn3_1 cab fdfrn3_0 fdfrn3_1 fdfrn3_2 dfrn2 fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class fdfrn3_2 wbr fdfrn3_0 wex fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class cop fdfrn3_2 wcel fdfrn3_0 wex fdfrn3_1 fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class fdfrn3_2 wbr fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class cop fdfrn3_2 wcel fdfrn3_0 fdfrn3_0 sup_set_class fdfrn3_1 sup_set_class fdfrn3_2 df-br exbii abbii eqtri $.
$}
$( Membership in a range.  (Contributed by Scott Fenton, 2-Feb-2011.) $)
${
	$d A x y $.
	$d B x y $.
	ielrn2g_0 $f set y $.
	felrn2g_0 $f set x $.
	felrn2g_1 $f class A $.
	felrn2g_2 $f class B $.
	felrn2g_3 $f class V $.
	elrn2g $p |- ( A e. V -> ( A e. ran B <-> E. x <. x , A >. e. B ) ) $= felrn2g_0 sup_set_class ielrn2g_0 sup_set_class cop felrn2g_2 wcel felrn2g_0 wex felrn2g_0 sup_set_class felrn2g_1 cop felrn2g_2 wcel felrn2g_0 wex ielrn2g_0 felrn2g_1 felrn2g_2 crn felrn2g_3 ielrn2g_0 sup_set_class felrn2g_1 wceq felrn2g_0 sup_set_class ielrn2g_0 sup_set_class cop felrn2g_2 wcel felrn2g_0 sup_set_class felrn2g_1 cop felrn2g_2 wcel felrn2g_0 ielrn2g_0 sup_set_class felrn2g_1 wceq felrn2g_0 sup_set_class ielrn2g_0 sup_set_class cop felrn2g_0 sup_set_class felrn2g_1 cop felrn2g_2 ielrn2g_0 sup_set_class felrn2g_1 felrn2g_0 sup_set_class opeq2 eleq1d exbidv felrn2g_0 ielrn2g_0 felrn2g_2 dfrn3 elab2g $.
$}
$( Membership in a range.  (Contributed by Scott Fenton, 2-Feb-2011.) $)
${
	$d A x $.
	$d B x $.
	felrng_0 $f set x $.
	felrng_1 $f class A $.
	felrng_2 $f class B $.
	felrng_3 $f class V $.
	elrng $p |- ( A e. V -> ( A e. ran B <-> E. x x B A ) ) $= felrng_1 felrng_3 wcel felrng_1 felrng_2 crn wcel felrng_0 sup_set_class felrng_1 cop felrng_2 wcel felrng_0 wex felrng_0 sup_set_class felrng_1 felrng_2 wbr felrng_0 wex felrng_0 felrng_1 felrng_2 felrng_3 elrn2g felrng_0 sup_set_class felrng_1 felrng_2 wbr felrng_0 sup_set_class felrng_1 cop felrng_2 wcel felrng_0 felrng_0 sup_set_class felrng_1 felrng_2 df-br exbii syl6bbr $.
$}
$( Alternate definition of domain.  (Contributed by NM, 28-Dec-1996.) $)
${
	$d x y A $.
	idfdm4_0 $f set x $.
	idfdm4_1 $f set y $.
	fdfdm4_0 $f class A $.
	dfdm4 $p |- dom A = ran `' A $= idfdm4_1 sup_set_class idfdm4_0 sup_set_class fdfdm4_0 ccnv wbr idfdm4_1 wex idfdm4_0 cab idfdm4_0 sup_set_class idfdm4_1 sup_set_class fdfdm4_0 wbr idfdm4_1 wex idfdm4_0 cab fdfdm4_0 ccnv crn fdfdm4_0 cdm idfdm4_1 sup_set_class idfdm4_0 sup_set_class fdfdm4_0 ccnv wbr idfdm4_1 wex idfdm4_0 sup_set_class idfdm4_1 sup_set_class fdfdm4_0 wbr idfdm4_1 wex idfdm4_0 idfdm4_1 sup_set_class idfdm4_0 sup_set_class fdfdm4_0 ccnv wbr idfdm4_0 sup_set_class idfdm4_1 sup_set_class fdfdm4_0 wbr idfdm4_1 idfdm4_1 sup_set_class idfdm4_0 sup_set_class fdfdm4_0 idfdm4_1 vex idfdm4_0 vex brcnv exbii abbii idfdm4_1 idfdm4_0 fdfdm4_0 ccnv dfrn2 idfdm4_0 idfdm4_1 fdfdm4_0 df-dm 3eqtr4ri $.
$}
$( Definition of domain, using bound-variable hypotheses instead of
       distinct variable conditions.  (Contributed by NM, 8-Mar-1995.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$d x y w v $.
	$d w v A $.
	idfdmf_0 $f set w $.
	idfdmf_1 $f set v $.
	fdfdmf_0 $f set x $.
	fdfdmf_1 $f set y $.
	fdfdmf_2 $f class A $.
	edfdmf_0 $e |- F/_ x A $.
	edfdmf_1 $e |- F/_ y A $.
	dfdmf $p |- dom A = { x | E. y x A y } $= fdfdmf_2 cdm idfdmf_0 sup_set_class idfdmf_1 sup_set_class fdfdmf_2 wbr idfdmf_1 wex idfdmf_0 cab idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 wex idfdmf_0 cab fdfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 wex fdfdmf_0 cab idfdmf_0 idfdmf_1 fdfdmf_2 df-dm idfdmf_0 sup_set_class idfdmf_1 sup_set_class fdfdmf_2 wbr idfdmf_1 wex idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 wex idfdmf_0 idfdmf_0 sup_set_class idfdmf_1 sup_set_class fdfdmf_2 wbr idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr idfdmf_1 fdfdmf_1 fdfdmf_1 idfdmf_0 sup_set_class idfdmf_1 sup_set_class fdfdmf_2 fdfdmf_1 idfdmf_0 sup_set_class nfcv edfdmf_1 fdfdmf_1 idfdmf_1 sup_set_class nfcv nfbr idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr idfdmf_1 nfv idfdmf_1 sup_set_class fdfdmf_1 sup_set_class idfdmf_0 sup_set_class fdfdmf_2 breq2 cbvex abbii idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 wex fdfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 wex idfdmf_0 fdfdmf_0 idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_0 fdfdmf_1 fdfdmf_0 idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 fdfdmf_0 idfdmf_0 sup_set_class nfcv edfdmf_0 fdfdmf_0 fdfdmf_1 sup_set_class nfcv nfbr nfex fdfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 wex idfdmf_0 nfv idfdmf_0 sup_set_class fdfdmf_0 sup_set_class wceq idfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 wbr fdfdmf_1 idfdmf_0 sup_set_class fdfdmf_0 sup_set_class fdfdmf_1 sup_set_class fdfdmf_2 breq1 exbidv cbvab 3eqtri $.
$}
$( Domain membership.  Theorem 4 of [Suppes] p. 59.  (Contributed by Mario
       Carneiro, 9-Jul-2014.) $)
${
	$d x y A $.
	$d x y B $.
	ieldmg_0 $f set x $.
	feldmg_0 $f set y $.
	feldmg_1 $f class A $.
	feldmg_2 $f class B $.
	feldmg_3 $f class V $.
	eldmg $p |- ( A e. V -> ( A e. dom B <-> E. y A B y ) ) $= ieldmg_0 sup_set_class feldmg_0 sup_set_class feldmg_2 wbr feldmg_0 wex feldmg_1 feldmg_0 sup_set_class feldmg_2 wbr feldmg_0 wex ieldmg_0 feldmg_1 feldmg_2 cdm feldmg_3 ieldmg_0 sup_set_class feldmg_1 wceq ieldmg_0 sup_set_class feldmg_0 sup_set_class feldmg_2 wbr feldmg_1 feldmg_0 sup_set_class feldmg_2 wbr feldmg_0 ieldmg_0 sup_set_class feldmg_1 feldmg_0 sup_set_class feldmg_2 breq1 exbidv ieldmg_0 feldmg_0 feldmg_2 df-dm elab2g $.
$}
$( Domain membership.  Theorem 4 of [Suppes] p. 59.  (Contributed by NM,
       27-Jan-1997.)  (Revised by Mario Carneiro, 9-Jul-2014.) $)
${
	$d y A $.
	$d y B $.
	feldm2g_0 $f set y $.
	feldm2g_1 $f class A $.
	feldm2g_2 $f class B $.
	feldm2g_3 $f class V $.
	eldm2g $p |- ( A e. V -> ( A e. dom B <-> E. y <. A , y >. e. B ) ) $= feldm2g_1 feldm2g_3 wcel feldm2g_1 feldm2g_2 cdm wcel feldm2g_1 feldm2g_0 sup_set_class feldm2g_2 wbr feldm2g_0 wex feldm2g_1 feldm2g_0 sup_set_class cop feldm2g_2 wcel feldm2g_0 wex feldm2g_0 feldm2g_1 feldm2g_2 feldm2g_3 eldmg feldm2g_1 feldm2g_0 sup_set_class feldm2g_2 wbr feldm2g_1 feldm2g_0 sup_set_class cop feldm2g_2 wcel feldm2g_0 feldm2g_1 feldm2g_0 sup_set_class feldm2g_2 df-br exbii syl6bb $.
$}
$( Membership in a domain.  Theorem 4 of [Suppes] p. 59.  (Contributed by
       NM, 2-Apr-2004.) $)
${
	$d y A $.
	$d y B $.
	feldm_0 $f set y $.
	feldm_1 $f class A $.
	feldm_2 $f class B $.
	eeldm_0 $e |- A e. _V $.
	eldm $p |- ( A e. dom B <-> E. y A B y ) $= feldm_1 cvv wcel feldm_1 feldm_2 cdm wcel feldm_1 feldm_0 sup_set_class feldm_2 wbr feldm_0 wex wb eeldm_0 feldm_0 feldm_1 feldm_2 cvv eldmg ax-mp $.
$}
$( Membership in a domain.  Theorem 4 of [Suppes] p. 59.  (Contributed by
       NM, 1-Aug-1994.) $)
${
	$d y A $.
	$d y B $.
	feldm2_0 $f set y $.
	feldm2_1 $f class A $.
	feldm2_2 $f class B $.
	eeldm2_0 $e |- A e. _V $.
	eldm2 $p |- ( A e. dom B <-> E. y <. A , y >. e. B ) $= feldm2_1 cvv wcel feldm2_1 feldm2_2 cdm wcel feldm2_1 feldm2_0 sup_set_class cop feldm2_2 wcel feldm2_0 wex wb eeldm2_0 feldm2_0 feldm2_1 feldm2_2 cvv eldm2g ax-mp $.
$}
$( Subset theorem for domain.  (Contributed by NM, 11-Aug-1994.) $)
${
	$d x y A $.
	$d x y B $.
	idmss_0 $f set x $.
	idmss_1 $f set y $.
	fdmss_0 $f class A $.
	fdmss_1 $f class B $.
	dmss $p |- ( A C_ B -> dom A C_ dom B ) $= fdmss_0 fdmss_1 wss idmss_0 fdmss_0 cdm fdmss_1 cdm fdmss_0 fdmss_1 wss idmss_0 sup_set_class idmss_1 sup_set_class cop fdmss_0 wcel idmss_1 wex idmss_0 sup_set_class idmss_1 sup_set_class cop fdmss_1 wcel idmss_1 wex idmss_0 sup_set_class fdmss_0 cdm wcel idmss_0 sup_set_class fdmss_1 cdm wcel fdmss_0 fdmss_1 wss idmss_0 sup_set_class idmss_1 sup_set_class cop fdmss_0 wcel idmss_0 sup_set_class idmss_1 sup_set_class cop fdmss_1 wcel idmss_1 fdmss_0 fdmss_1 idmss_0 sup_set_class idmss_1 sup_set_class cop ssel eximdv idmss_1 idmss_0 sup_set_class fdmss_0 idmss_0 vex eldm2 idmss_1 idmss_0 sup_set_class fdmss_1 idmss_0 vex eldm2 3imtr4g ssrdv $.
$}
$( Equality theorem for domain.  (Contributed by NM, 11-Aug-1994.) $)
${
	fdmeq_0 $f class A $.
	fdmeq_1 $f class B $.
	dmeq $p |- ( A = B -> dom A = dom B ) $= fdmeq_0 fdmeq_1 wss fdmeq_1 fdmeq_0 wss wa fdmeq_0 cdm fdmeq_1 cdm wss fdmeq_1 cdm fdmeq_0 cdm wss wa fdmeq_0 fdmeq_1 wceq fdmeq_0 cdm fdmeq_1 cdm wceq fdmeq_0 fdmeq_1 wss fdmeq_0 cdm fdmeq_1 cdm wss fdmeq_1 fdmeq_0 wss fdmeq_1 cdm fdmeq_0 cdm wss fdmeq_0 fdmeq_1 dmss fdmeq_1 fdmeq_0 dmss anim12i fdmeq_0 fdmeq_1 eqss fdmeq_0 cdm fdmeq_1 cdm eqss 3imtr4i $.
$}
$( Equality inference for domain.  (Contributed by NM, 4-Mar-2004.) $)
${
	fdmeqi_0 $f class A $.
	fdmeqi_1 $f class B $.
	edmeqi_0 $e |- A = B $.
	dmeqi $p |- dom A = dom B $= fdmeqi_0 fdmeqi_1 wceq fdmeqi_0 cdm fdmeqi_1 cdm wceq edmeqi_0 fdmeqi_0 fdmeqi_1 dmeq ax-mp $.
$}
$( Equality deduction for domain.  (Contributed by NM, 4-Mar-2004.) $)
${
	fdmeqd_0 $f wff ph $.
	fdmeqd_1 $f class A $.
	fdmeqd_2 $f class B $.
	edmeqd_0 $e |- ( ph -> A = B ) $.
	dmeqd $p |- ( ph -> dom A = dom B ) $= fdmeqd_0 fdmeqd_1 fdmeqd_2 wceq fdmeqd_1 cdm fdmeqd_2 cdm wceq edmeqd_0 fdmeqd_1 fdmeqd_2 dmeq syl $.
$}
$( Membership of first of an ordered pair in a domain.  (Contributed by NM,
       30-Jul-1995.) $)
${
	$d y A $.
	$d y B $.
	$d y C $.
	iopeldm_0 $f set y $.
	fopeldm_0 $f class A $.
	fopeldm_1 $f class B $.
	fopeldm_2 $f class C $.
	eopeldm_0 $e |- A e. _V $.
	eopeldm_1 $e |- B e. _V $.
	opeldm $p |- ( <. A , B >. e. C -> A e. dom C ) $= fopeldm_0 fopeldm_1 cop fopeldm_2 wcel fopeldm_0 iopeldm_0 sup_set_class cop fopeldm_2 wcel iopeldm_0 wex fopeldm_0 fopeldm_2 cdm wcel fopeldm_0 iopeldm_0 sup_set_class cop fopeldm_2 wcel fopeldm_0 fopeldm_1 cop fopeldm_2 wcel iopeldm_0 fopeldm_1 eopeldm_1 iopeldm_0 sup_set_class fopeldm_1 wceq fopeldm_0 iopeldm_0 sup_set_class cop fopeldm_0 fopeldm_1 cop fopeldm_2 iopeldm_0 sup_set_class fopeldm_1 fopeldm_0 opeq2 eleq1d spcev iopeldm_0 fopeldm_0 fopeldm_2 eopeldm_0 eldm2 sylibr $.
$}
$( Membership of first of a binary relation in a domain.  (Contributed by
       NM, 30-Jul-1995.) $)
${
	fbreldm_0 $f class A $.
	fbreldm_1 $f class B $.
	fbreldm_2 $f class R $.
	ebreldm_0 $e |- A e. _V $.
	ebreldm_1 $e |- B e. _V $.
	breldm $p |- ( A R B -> A e. dom R ) $= fbreldm_0 fbreldm_1 fbreldm_2 wbr fbreldm_0 fbreldm_1 cop fbreldm_2 wcel fbreldm_0 fbreldm_2 cdm wcel fbreldm_0 fbreldm_1 fbreldm_2 df-br fbreldm_0 fbreldm_1 fbreldm_2 ebreldm_0 ebreldm_1 opeldm sylbi $.
$}
$( Membership of first of a binary relation in a domain.  (Contributed by
       NM, 21-Mar-2007.) $)
${
	$d x A $.
	$d x B $.
	$d x R $.
	ibreldmg_0 $f set x $.
	fbreldmg_0 $f class A $.
	fbreldmg_1 $f class B $.
	fbreldmg_2 $f class C $.
	fbreldmg_3 $f class D $.
	fbreldmg_4 $f class R $.
	breldmg $p |- ( ( A e. C /\ B e. D /\ A R B ) -> A e. dom R ) $= fbreldmg_0 fbreldmg_2 wcel fbreldmg_1 fbreldmg_3 wcel fbreldmg_0 fbreldmg_1 fbreldmg_4 wbr w3a fbreldmg_0 fbreldmg_4 cdm wcel fbreldmg_0 ibreldmg_0 sup_set_class fbreldmg_4 wbr ibreldmg_0 wex fbreldmg_1 fbreldmg_3 wcel fbreldmg_0 fbreldmg_1 fbreldmg_4 wbr fbreldmg_0 ibreldmg_0 sup_set_class fbreldmg_4 wbr ibreldmg_0 wex fbreldmg_0 fbreldmg_2 wcel fbreldmg_1 fbreldmg_3 wcel fbreldmg_0 fbreldmg_1 fbreldmg_4 wbr fbreldmg_0 ibreldmg_0 sup_set_class fbreldmg_4 wbr ibreldmg_0 wex fbreldmg_0 ibreldmg_0 sup_set_class fbreldmg_4 wbr fbreldmg_0 fbreldmg_1 fbreldmg_4 wbr ibreldmg_0 fbreldmg_1 fbreldmg_3 ibreldmg_0 sup_set_class fbreldmg_1 fbreldmg_0 fbreldmg_4 breq2 spcegv imp 3adant1 fbreldmg_0 fbreldmg_2 wcel fbreldmg_1 fbreldmg_3 wcel fbreldmg_0 fbreldmg_4 cdm wcel fbreldmg_0 ibreldmg_0 sup_set_class fbreldmg_4 wbr ibreldmg_0 wex wb fbreldmg_0 fbreldmg_1 fbreldmg_4 wbr ibreldmg_0 fbreldmg_0 fbreldmg_4 fbreldmg_2 eldmg 3ad2ant1 mpbird $.
$}
$( The domain of a union is the union of domains.  Exercise 56(a) of
       [Enderton] p. 65.  (Contributed by NM, 12-Aug-1994.)  (Proof shortened
       by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	idmun_0 $f set x $.
	idmun_1 $f set y $.
	fdmun_0 $f class A $.
	fdmun_1 $f class B $.
	dmun $p |- dom ( A u. B ) = ( dom A u. dom B ) $= idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 cab idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex idmun_1 cab cun idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 fdmun_1 cun wbr idmun_0 wex idmun_1 cab fdmun_0 cdm fdmun_1 cdm cun fdmun_0 fdmun_1 cun cdm idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 cab idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex idmun_1 cab cun idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex wo idmun_1 cab idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 fdmun_1 cun wbr idmun_0 wex idmun_1 cab idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex idmun_1 unab idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex wo idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 fdmun_1 cun wbr idmun_0 wex idmun_1 idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 fdmun_1 cun wbr idmun_0 wex idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr wo idmun_0 wex idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex wo idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 fdmun_1 cun wbr idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr wo idmun_0 idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 fdmun_1 brun exbii idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 19.43 bitr2i abbii eqtri fdmun_0 cdm idmun_1 sup_set_class idmun_0 sup_set_class fdmun_0 wbr idmun_0 wex idmun_1 cab fdmun_1 cdm idmun_1 sup_set_class idmun_0 sup_set_class fdmun_1 wbr idmun_0 wex idmun_1 cab idmun_1 idmun_0 fdmun_0 df-dm idmun_1 idmun_0 fdmun_1 df-dm uneq12i idmun_1 idmun_0 fdmun_0 fdmun_1 cun df-dm 3eqtr4ri $.
$}
$( The domain of an intersection belong to the intersection of domains.
       Theorem 6 of [Suppes] p. 60.  (Contributed by NM, 15-Sep-2004.) $)
${
	$d x y A $.
	$d x y B $.
	idmin_0 $f set x $.
	idmin_1 $f set y $.
	fdmin_0 $f class A $.
	fdmin_1 $f class B $.
	dmin $p |- dom ( A i^i B ) C_ ( dom A i^i dom B ) $= idmin_0 fdmin_0 fdmin_1 cin cdm fdmin_0 cdm fdmin_1 cdm cin idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel wa idmin_1 wex idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_1 wex idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel idmin_1 wex wa idmin_0 sup_set_class fdmin_0 fdmin_1 cin cdm wcel idmin_0 sup_set_class fdmin_0 cdm fdmin_1 cdm cin wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel idmin_1 19.40 idmin_0 sup_set_class fdmin_0 fdmin_1 cin cdm wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 fdmin_1 cin wcel idmin_1 wex idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel wa idmin_1 wex idmin_1 idmin_0 sup_set_class fdmin_0 fdmin_1 cin idmin_0 vex eldm2 idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 fdmin_1 cin wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel wa idmin_1 idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 fdmin_1 elin exbii bitri idmin_0 sup_set_class fdmin_0 cdm fdmin_1 cdm cin wcel idmin_0 sup_set_class fdmin_0 cdm wcel idmin_0 sup_set_class fdmin_1 cdm wcel wa idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_1 wex idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel idmin_1 wex wa idmin_0 sup_set_class fdmin_0 cdm fdmin_1 cdm elin idmin_0 sup_set_class fdmin_0 cdm wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_0 wcel idmin_1 wex idmin_0 sup_set_class fdmin_1 cdm wcel idmin_0 sup_set_class idmin_1 sup_set_class cop fdmin_1 wcel idmin_1 wex idmin_1 idmin_0 sup_set_class fdmin_0 idmin_0 vex eldm2 idmin_1 idmin_0 sup_set_class fdmin_1 idmin_0 vex eldm2 anbi12i bitri 3imtr4i ssriv $.
$}
$( The domain of an indexed union.  (Contributed by Mario Carneiro,
       26-Apr-2016.) $)
${
	$d x y z $.
	$d y z A $.
	$d y z B $.
	idmiun_0 $f set y $.
	idmiun_1 $f set z $.
	fdmiun_0 $f set x $.
	fdmiun_1 $f class A $.
	fdmiun_2 $f class B $.
	dmiun $p |- dom U_ x e. A B = U_ x e. A dom B $= idmiun_0 fdmiun_0 fdmiun_1 fdmiun_2 ciun cdm fdmiun_0 fdmiun_1 fdmiun_2 cdm ciun idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_0 fdmiun_1 fdmiun_2 ciun wcel idmiun_1 wex idmiun_0 sup_set_class fdmiun_2 cdm wcel fdmiun_0 fdmiun_1 wrex idmiun_0 sup_set_class fdmiun_0 fdmiun_1 fdmiun_2 ciun cdm wcel idmiun_0 sup_set_class fdmiun_0 fdmiun_1 fdmiun_2 cdm ciun wcel idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_2 wcel idmiun_1 wex fdmiun_0 fdmiun_1 wrex idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_2 wcel fdmiun_0 fdmiun_1 wrex idmiun_1 wex idmiun_0 sup_set_class fdmiun_2 cdm wcel fdmiun_0 fdmiun_1 wrex idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_0 fdmiun_1 fdmiun_2 ciun wcel idmiun_1 wex idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_2 wcel fdmiun_0 idmiun_1 fdmiun_1 rexcom4 idmiun_0 sup_set_class fdmiun_2 cdm wcel idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_2 wcel idmiun_1 wex fdmiun_0 fdmiun_1 idmiun_1 idmiun_0 sup_set_class fdmiun_2 idmiun_0 vex eldm2 rexbii idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_0 fdmiun_1 fdmiun_2 ciun wcel idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_2 wcel fdmiun_0 fdmiun_1 wrex idmiun_1 fdmiun_0 idmiun_0 sup_set_class idmiun_1 sup_set_class cop fdmiun_1 fdmiun_2 eliun exbii 3bitr4ri idmiun_1 idmiun_0 sup_set_class fdmiun_0 fdmiun_1 fdmiun_2 ciun idmiun_0 vex eldm2 fdmiun_0 idmiun_0 sup_set_class fdmiun_1 fdmiun_2 cdm eliun 3bitr4i eqriv $.
$}
$( The domain of a union.  Part of Exercise 8 of [Enderton] p. 41.
       (Contributed by NM, 3-Feb-2004.) $)
${
	$d x y z $.
	$d y z A $.
	$d y z $.
	$d x A $.
	idmuni_0 $f set y $.
	idmuni_1 $f set z $.
	fdmuni_0 $f set x $.
	fdmuni_1 $f class A $.
	dmuni $p |- dom U. A = U_ x e. A dom x $= idmuni_0 fdmuni_1 cuni cdm fdmuni_0 fdmuni_1 fdmuni_0 sup_set_class cdm ciun idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_1 cuni wcel idmuni_1 wex idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel fdmuni_0 fdmuni_1 wrex idmuni_0 sup_set_class fdmuni_1 cuni cdm wcel idmuni_0 sup_set_class fdmuni_0 fdmuni_1 fdmuni_0 sup_set_class cdm ciun wcel idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa fdmuni_0 wex idmuni_1 wex fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel wa fdmuni_0 wex idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_1 cuni wcel idmuni_1 wex idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel fdmuni_0 fdmuni_1 wrex idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa fdmuni_0 wex idmuni_1 wex idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa idmuni_1 wex fdmuni_0 wex fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel wa fdmuni_0 wex idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa idmuni_1 fdmuni_0 excom idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa idmuni_1 wex fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel wa fdmuni_0 idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel idmuni_1 wex fdmuni_0 sup_set_class fdmuni_1 wcel wa fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel idmuni_1 wex wa idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa idmuni_1 wex fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel wa idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel idmuni_1 wex fdmuni_0 sup_set_class fdmuni_1 wcel ancom idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_1 19.41v idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel idmuni_1 wex fdmuni_0 sup_set_class fdmuni_1 wcel idmuni_1 idmuni_0 sup_set_class fdmuni_0 sup_set_class idmuni_0 vex eldm2 anbi2i 3bitr4i exbii bitri idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_1 cuni wcel idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_0 sup_set_class wcel fdmuni_0 sup_set_class fdmuni_1 wcel wa fdmuni_0 wex idmuni_1 fdmuni_0 idmuni_0 sup_set_class idmuni_1 sup_set_class cop fdmuni_1 eluni exbii idmuni_0 sup_set_class fdmuni_0 sup_set_class cdm wcel fdmuni_0 fdmuni_1 df-rex 3bitr4i idmuni_1 idmuni_0 sup_set_class fdmuni_1 cuni idmuni_0 vex eldm2 fdmuni_0 idmuni_0 sup_set_class fdmuni_1 fdmuni_0 sup_set_class cdm eliun 3bitr4i eqriv $.
$}
$( The domain of a class of ordered pairs.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 4-Dec-2016.) $)
${
	$d x y $.
	fdmopab_0 $f wff ph $.
	fdmopab_1 $f set x $.
	fdmopab_2 $f set y $.
	dmopab $p |- dom { <. x , y >. | ph } = { x | E. y ph } $= fdmopab_0 fdmopab_1 fdmopab_2 copab cdm fdmopab_1 sup_set_class fdmopab_2 sup_set_class fdmopab_0 fdmopab_1 fdmopab_2 copab wbr fdmopab_2 wex fdmopab_1 cab fdmopab_0 fdmopab_2 wex fdmopab_1 cab fdmopab_1 fdmopab_2 fdmopab_0 fdmopab_1 fdmopab_2 copab fdmopab_0 fdmopab_1 fdmopab_2 nfopab1 fdmopab_0 fdmopab_1 fdmopab_2 nfopab2 dfdmf fdmopab_1 sup_set_class fdmopab_2 sup_set_class fdmopab_0 fdmopab_1 fdmopab_2 copab wbr fdmopab_2 wex fdmopab_0 fdmopab_2 wex fdmopab_1 fdmopab_1 sup_set_class fdmopab_2 sup_set_class fdmopab_0 fdmopab_1 fdmopab_2 copab wbr fdmopab_0 fdmopab_2 fdmopab_1 sup_set_class fdmopab_2 sup_set_class fdmopab_0 fdmopab_1 fdmopab_2 copab wbr fdmopab_1 sup_set_class fdmopab_2 sup_set_class cop fdmopab_0 fdmopab_1 fdmopab_2 copab wcel fdmopab_0 fdmopab_1 sup_set_class fdmopab_2 sup_set_class fdmopab_0 fdmopab_1 fdmopab_2 copab df-br fdmopab_0 fdmopab_1 fdmopab_2 opabid bitri exbii abbii eqtri $.
$}
$( Upper bound for the domain of a restricted class of ordered pairs.
       (Contributed by NM, 31-Jan-2004.) $)
${
	$d x y A $.
	fdmopabss_0 $f wff ph $.
	fdmopabss_1 $f set x $.
	fdmopabss_2 $f set y $.
	fdmopabss_3 $f class A $.
	dmopabss $p |- dom { <. x , y >. | ( x e. A /\ ph ) } C_ A $= fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 wa fdmopabss_1 fdmopabss_2 copab cdm fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 wa fdmopabss_2 wex fdmopabss_1 cab fdmopabss_3 fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 wa fdmopabss_1 fdmopabss_2 dmopab fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 wa fdmopabss_2 wex fdmopabss_1 cab fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 fdmopabss_2 wex wa fdmopabss_1 cab fdmopabss_3 fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 wa fdmopabss_2 wex fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 fdmopabss_2 wex wa fdmopabss_1 fdmopabss_1 sup_set_class fdmopabss_3 wcel fdmopabss_0 fdmopabss_2 19.42v abbii fdmopabss_0 fdmopabss_2 wex fdmopabss_1 fdmopabss_3 ssab2 eqsstri eqsstri $.
$}
$( The domain of a restricted class of ordered pairs.  (Contributed by NM,
       31-Jan-2004.) $)
${
	$d x y A $.
	fdmopab3_0 $f wff ph $.
	fdmopab3_1 $f set x $.
	fdmopab3_2 $f set y $.
	fdmopab3_3 $f class A $.
	dmopab3 $p |- ( A. x e. A E. y ph <-> dom { <. x , y >. | ( x e. A /\ ph ) } = A ) $= fdmopab3_0 fdmopab3_2 wex fdmopab3_1 fdmopab3_3 wral fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wi fdmopab3_1 wal fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa wb fdmopab3_1 wal fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_1 fdmopab3_2 copab cdm fdmopab3_3 wceq fdmopab3_0 fdmopab3_2 wex fdmopab3_1 fdmopab3_3 df-ral fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wi fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa wb fdmopab3_1 fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex pm4.71 albii fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_1 fdmopab3_2 copab cdm fdmopab3_3 wceq fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 cab fdmopab3_3 wceq fdmopab3_3 fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 cab wceq fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa wb fdmopab3_1 wal fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_1 fdmopab3_2 copab cdm fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 cab fdmopab3_3 fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_1 fdmopab3_2 copab cdm fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_2 wex fdmopab3_1 cab fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 cab fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_1 fdmopab3_2 dmopab fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 wa fdmopab3_2 wex fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 19.42v abbii eqtri eqeq1i fdmopab3_3 fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 cab eqcom fdmopab3_1 sup_set_class fdmopab3_3 wcel fdmopab3_0 fdmopab3_2 wex wa fdmopab3_1 fdmopab3_3 abeq2 3bitr2ri 3bitri $.
$}
$( The domain of the empty set is empty.  Part of Theorem 3.8(v) of [Monk1]
       p. 36.  (Contributed by NM, 4-Jul-1994.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	idm0_0 $f set x $.
	idm0_1 $f set y $.
	dm0 $p |- dom (/) = (/) $= c0 cdm c0 wceq idm0_0 sup_set_class c0 cdm wcel wn idm0_0 idm0_0 c0 cdm eq0 idm0_0 sup_set_class c0 cdm wcel idm0_0 sup_set_class idm0_1 sup_set_class cop c0 wcel idm0_1 wex idm0_0 sup_set_class idm0_1 sup_set_class cop c0 wcel idm0_1 idm0_0 sup_set_class idm0_1 sup_set_class cop noel nex idm0_1 idm0_0 sup_set_class c0 idm0_0 vex eldm2 mtbir mpgbir $.
$}
$( The domain of the identity relation is the universe.  (Contributed by
       NM, 30-Apr-1998.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	idmi_0 $f set x $.
	idmi_1 $f set y $.
	dmi $p |- dom _I = _V $= cid cdm cvv wceq idmi_0 sup_set_class cid cdm wcel idmi_0 idmi_0 cid cdm eqv idmi_0 sup_set_class cid cdm wcel idmi_0 sup_set_class idmi_1 sup_set_class cid wbr idmi_1 wex idmi_0 sup_set_class idmi_1 sup_set_class cid wbr idmi_1 wex idmi_1 sup_set_class idmi_0 sup_set_class wceq idmi_1 wex idmi_1 idmi_0 a9ev idmi_0 sup_set_class idmi_1 sup_set_class cid wbr idmi_1 sup_set_class idmi_0 sup_set_class wceq idmi_1 idmi_0 sup_set_class idmi_1 sup_set_class cid wbr idmi_0 sup_set_class idmi_1 sup_set_class wceq idmi_1 sup_set_class idmi_0 sup_set_class wceq idmi_0 sup_set_class idmi_1 sup_set_class idmi_1 vex ideq idmi_0 idmi_1 equcom bitri exbii mpbir idmi_1 idmi_0 sup_set_class cid idmi_0 vex eldm mpbir mpgbir $.
$}
$( The domain of the universe is the universe.  (Contributed by NM,
       8-Aug-2003.) $)
${
	dmv $p |- dom _V = _V $= cvv cdm cvv cvv cdm ssv cvv cid cdm cvv cdm dmi cid cvv wss cid cdm cvv cdm wss cid ssv cid cvv dmss ax-mp eqsstr3i eqssi $.
$}
$( An empty domain implies an empty range.  (Contributed by NM,
       21-May-1998.) $)
${
	$d x y A $.
	idm0rn0_0 $f set x $.
	idm0rn0_1 $f set y $.
	fdm0rn0_0 $f class A $.
	dm0rn0 $p |- ( dom A = (/) <-> ran A = (/) ) $= idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 cab c0 wceq idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 cab c0 wceq fdm0rn0_0 cdm c0 wceq fdm0rn0_0 crn c0 wceq idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 sup_set_class c0 wcel wb idm0rn0_0 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 sup_set_class c0 wcel wb idm0rn0_1 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 cab c0 wceq idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 cab c0 wceq idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex wn idm0rn0_0 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex wn idm0rn0_1 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 sup_set_class c0 wcel wb idm0rn0_0 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 sup_set_class c0 wcel wb idm0rn0_1 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex wn idm0rn0_0 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 wex wn idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex wn idm0rn0_1 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex wn idm0rn0_0 wal idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 wex idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 wex idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 alnex idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 idm0rn0_1 excom xchbinx idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 alnex bitr4i idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex wn idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 sup_set_class c0 wcel wb idm0rn0_0 idm0rn0_0 sup_set_class c0 wcel idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 sup_set_class noel nbn albii idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex wn idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 sup_set_class c0 wcel wb idm0rn0_1 idm0rn0_1 sup_set_class c0 wcel idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 sup_set_class noel nbn albii 3bitr3i idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 c0 abeq1 idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 c0 abeq1 3bitr4i fdm0rn0_0 cdm idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_1 wex idm0rn0_0 cab c0 idm0rn0_0 idm0rn0_1 fdm0rn0_0 df-dm eqeq1i fdm0rn0_0 crn idm0rn0_0 sup_set_class idm0rn0_1 sup_set_class fdm0rn0_0 wbr idm0rn0_0 wex idm0rn0_1 cab c0 idm0rn0_0 idm0rn0_1 fdm0rn0_0 dfrn2 eqeq1i 3bitr4i $.
$}
$( A relation is empty iff its domain is empty.  (Contributed by NM,
       15-Sep-2004.) $)
${
	$d x y A $.
	ireldm0_0 $f set x $.
	ireldm0_1 $f set y $.
	freldm0_0 $f class A $.
	reldm0 $p |- ( Rel A -> ( A = (/) <-> dom A = (/) ) ) $= freldm0_0 wrel freldm0_0 c0 wceq ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel wb ireldm0_1 wal ireldm0_0 wal freldm0_0 cdm c0 wceq freldm0_0 wrel c0 wrel freldm0_0 c0 wceq ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel wb ireldm0_1 wal ireldm0_0 wal wb rel0 ireldm0_0 ireldm0_1 freldm0_0 c0 eqrel mpan2 freldm0_0 cdm c0 wceq ireldm0_0 sup_set_class freldm0_0 cdm wcel wn ireldm0_0 wal ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel wb ireldm0_1 wal ireldm0_0 wal ireldm0_0 freldm0_0 cdm eq0 ireldm0_0 sup_set_class freldm0_0 cdm wcel wn ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel wb ireldm0_1 wal ireldm0_0 ireldm0_0 sup_set_class freldm0_0 cdm wcel wn ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel wn ireldm0_1 wal ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel wb ireldm0_1 wal ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel wn ireldm0_1 wal ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_1 wex ireldm0_0 sup_set_class freldm0_0 cdm wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_1 alnex ireldm0_1 ireldm0_0 sup_set_class freldm0_0 ireldm0_0 vex eldm2 xchbinxr ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel wn ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel wb ireldm0_1 ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop c0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop freldm0_0 wcel ireldm0_0 sup_set_class ireldm0_1 sup_set_class cop noel nbn albii bitr3i albii bitr2i syl6bb $.
$}
$( The domain of a cross product.  Part of Theorem 3.13(x) of [Monk1]
       p. 37.  (Contributed by NM, 28-Jul-1995.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	idmxp_0 $f set x $.
	idmxp_1 $f set y $.
	fdmxp_0 $f class A $.
	fdmxp_1 $f class B $.
	dmxp $p |- ( B =/= (/) -> dom ( A X. B ) = A ) $= fdmxp_1 c0 wne fdmxp_0 fdmxp_1 cxp cdm idmxp_1 sup_set_class fdmxp_0 wcel idmxp_0 sup_set_class fdmxp_1 wcel wa idmxp_1 idmxp_0 copab cdm fdmxp_0 fdmxp_0 fdmxp_1 cxp idmxp_1 sup_set_class fdmxp_0 wcel idmxp_0 sup_set_class fdmxp_1 wcel wa idmxp_1 idmxp_0 copab idmxp_1 idmxp_0 fdmxp_0 fdmxp_1 df-xp dmeqi fdmxp_1 c0 wne idmxp_0 sup_set_class fdmxp_1 wcel idmxp_0 wex idmxp_1 fdmxp_0 wral idmxp_1 sup_set_class fdmxp_0 wcel idmxp_0 sup_set_class fdmxp_1 wcel wa idmxp_1 idmxp_0 copab cdm fdmxp_0 wceq fdmxp_1 c0 wne idmxp_0 sup_set_class fdmxp_1 wcel idmxp_0 wex idmxp_1 fdmxp_0 fdmxp_1 c0 wne idmxp_0 sup_set_class fdmxp_1 wcel idmxp_0 wex idmxp_0 fdmxp_1 n0 biimpi ralrimivw idmxp_0 sup_set_class fdmxp_1 wcel idmxp_1 idmxp_0 fdmxp_0 dmopab3 sylib syl5eq $.
$}
$( The domain of a square cross product.  (Contributed by NM,
     28-Jul-1995.) $)
${
	fdmxpid_0 $f class A $.
	dmxpid $p |- dom ( A X. A ) = A $= fdmxpid_0 fdmxpid_0 cxp cdm fdmxpid_0 wceq fdmxpid_0 c0 fdmxpid_0 c0 wceq c0 cdm c0 fdmxpid_0 fdmxpid_0 cxp cdm fdmxpid_0 dm0 fdmxpid_0 c0 wceq fdmxpid_0 fdmxpid_0 cxp c0 fdmxpid_0 c0 wceq fdmxpid_0 fdmxpid_0 cxp c0 fdmxpid_0 cxp c0 fdmxpid_0 c0 fdmxpid_0 xpeq1 fdmxpid_0 xp0r syl6eq dmeqd fdmxpid_0 c0 wceq id 3eqtr4a fdmxpid_0 fdmxpid_0 dmxp pm2.61ine $.
$}
$( The domain of the intersection of two square cross products.  Unlike
     ~ dmin , equality holds.  (Contributed by NM, 29-Jan-2008.) $)
${
	fdmxpin_0 $f class A $.
	fdmxpin_1 $f class B $.
	dmxpin $p |- dom ( ( A X. A ) i^i ( B X. B ) ) = ( A i^i B ) $= fdmxpin_0 fdmxpin_0 cxp fdmxpin_1 fdmxpin_1 cxp cin cdm fdmxpin_0 fdmxpin_1 cin fdmxpin_0 fdmxpin_1 cin cxp cdm fdmxpin_0 fdmxpin_1 cin fdmxpin_0 fdmxpin_0 cxp fdmxpin_1 fdmxpin_1 cxp cin fdmxpin_0 fdmxpin_1 cin fdmxpin_0 fdmxpin_1 cin cxp fdmxpin_0 fdmxpin_0 fdmxpin_1 fdmxpin_1 inxp dmeqi fdmxpin_0 fdmxpin_1 cin dmxpid eqtri $.
$}
$( The cross product of a class with itself is one-to-one.  (Contributed by
     NM, 5-Nov-2006.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fxpid11_0 $f class A $.
	fxpid11_1 $f class B $.
	xpid11 $p |- ( ( A X. A ) = ( B X. B ) <-> A = B ) $= fxpid11_0 fxpid11_0 cxp fxpid11_1 fxpid11_1 cxp wceq fxpid11_0 fxpid11_1 wceq fxpid11_0 fxpid11_0 cxp fxpid11_1 fxpid11_1 cxp wceq fxpid11_0 fxpid11_0 cxp cdm fxpid11_1 fxpid11_1 cxp cdm fxpid11_0 fxpid11_1 fxpid11_0 fxpid11_0 cxp fxpid11_1 fxpid11_1 cxp dmeq fxpid11_0 dmxpid fxpid11_1 dmxpid 3eqtr3g fxpid11_0 fxpid11_1 wceq fxpid11_0 fxpid11_0 cxp fxpid11_1 fxpid11_1 cxp wceq fxpid11_0 fxpid11_1 fxpid11_0 fxpid11_1 xpeq12 anidms impbii $.
$}
$( The domain of the double converse of a class (which doesn't have to be a
     relation as in ~ dfrel2 ).  (Contributed by NM, 8-Apr-2007.) $)
${
	fdmcnvcnv_0 $f class A $.
	dmcnvcnv $p |- dom `' `' A = dom A $= fdmcnvcnv_0 cdm fdmcnvcnv_0 ccnv crn fdmcnvcnv_0 ccnv ccnv cdm fdmcnvcnv_0 dfdm4 fdmcnvcnv_0 ccnv df-rn eqtr2i $.
$}
$( The range of the double converse of a class.  (Contributed by NM,
     8-Apr-2007.) $)
${
	frncnvcnv_0 $f class A $.
	rncnvcnv $p |- ran `' `' A = ran A $= frncnvcnv_0 crn frncnvcnv_0 ccnv cdm frncnvcnv_0 ccnv ccnv crn frncnvcnv_0 df-rn frncnvcnv_0 ccnv dfdm4 eqtr2i $.
$}
$( The first member of an ordered pair in a relation belongs to the domain
       of the relation.  (Contributed by NM, 28-Jul-2004.) $)
${
	$d x y A $.
	$d x y B $.
	ielreldm_0 $f set x $.
	ielreldm_1 $f set y $.
	felreldm_0 $f class A $.
	felreldm_1 $f class B $.
	elreldm $p |- ( ( Rel A /\ B e. A ) -> |^| |^| B e. dom A ) $= felreldm_0 wrel felreldm_1 felreldm_0 wcel felreldm_1 cint cint felreldm_0 cdm wcel felreldm_1 felreldm_0 wcel felreldm_0 wrel felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq ielreldm_1 wex ielreldm_0 wex felreldm_1 cint cint felreldm_0 cdm wcel felreldm_0 wrel felreldm_1 felreldm_0 wcel felreldm_1 cvv cvv cxp wcel felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq ielreldm_1 wex ielreldm_0 wex felreldm_0 wrel felreldm_0 cvv cvv cxp wss felreldm_1 felreldm_0 wcel felreldm_1 cvv cvv cxp wcel wi felreldm_0 df-rel felreldm_0 cvv cvv cxp felreldm_1 ssel sylbi ielreldm_0 ielreldm_1 felreldm_1 elvv syl6ib felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq felreldm_1 felreldm_0 wcel felreldm_1 cint cint felreldm_0 cdm wcel wi ielreldm_0 ielreldm_1 felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq felreldm_1 felreldm_0 wcel ielreldm_0 sup_set_class felreldm_0 cdm wcel felreldm_1 cint cint felreldm_0 cdm wcel felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq felreldm_1 felreldm_0 wcel ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop felreldm_0 wcel ielreldm_0 sup_set_class felreldm_0 cdm wcel felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop felreldm_0 eleq1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class felreldm_0 ielreldm_0 vex ielreldm_1 vex opeldm syl6bi felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq felreldm_1 cint cint ielreldm_0 sup_set_class felreldm_0 cdm felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq felreldm_1 cint cint ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop cint cint ielreldm_0 sup_set_class felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop wceq felreldm_1 cint ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop cint felreldm_1 ielreldm_0 sup_set_class ielreldm_1 sup_set_class cop inteq inteqd ielreldm_0 sup_set_class ielreldm_1 sup_set_class ielreldm_0 vex ielreldm_1 vex op1stb syl6eq eleq1d sylibrd exlimivv syli imp $.
$}
$( Equality theorem for range.  (Contributed by NM, 29-Dec-1996.) $)
${
	frneq_0 $f class A $.
	frneq_1 $f class B $.
	rneq $p |- ( A = B -> ran A = ran B ) $= frneq_0 frneq_1 wceq frneq_0 ccnv cdm frneq_1 ccnv cdm frneq_0 crn frneq_1 crn frneq_0 frneq_1 wceq frneq_0 ccnv frneq_1 ccnv frneq_0 frneq_1 cnveq dmeqd frneq_0 df-rn frneq_1 df-rn 3eqtr4g $.
$}
$( Equality inference for range.  (Contributed by NM, 4-Mar-2004.) $)
${
	frneqi_0 $f class A $.
	frneqi_1 $f class B $.
	erneqi_0 $e |- A = B $.
	rneqi $p |- ran A = ran B $= frneqi_0 frneqi_1 wceq frneqi_0 crn frneqi_1 crn wceq erneqi_0 frneqi_0 frneqi_1 rneq ax-mp $.
$}
$( Equality deduction for range.  (Contributed by NM, 4-Mar-2004.) $)
${
	frneqd_0 $f wff ph $.
	frneqd_1 $f class A $.
	frneqd_2 $f class B $.
	erneqd_0 $e |- ( ph -> A = B ) $.
	rneqd $p |- ( ph -> ran A = ran B ) $= frneqd_0 frneqd_1 frneqd_2 wceq frneqd_1 crn frneqd_2 crn wceq erneqd_0 frneqd_1 frneqd_2 rneq syl $.
$}
$( Subset theorem for range.  (Contributed by NM, 22-Mar-1998.) $)
${
	frnss_0 $f class A $.
	frnss_1 $f class B $.
	rnss $p |- ( A C_ B -> ran A C_ ran B ) $= frnss_0 frnss_1 wss frnss_0 ccnv cdm frnss_1 ccnv cdm frnss_0 crn frnss_1 crn frnss_0 frnss_1 wss frnss_0 ccnv frnss_1 ccnv wss frnss_0 ccnv cdm frnss_1 ccnv cdm wss frnss_0 frnss_1 cnvss frnss_0 ccnv frnss_1 ccnv dmss syl frnss_0 df-rn frnss_1 df-rn 3sstr4g $.
$}
$( The second argument of a binary relation belongs to its range.
     (Contributed by NM, 29-Jun-2008.) $)
${
	fbrelrng_0 $f class A $.
	fbrelrng_1 $f class B $.
	fbrelrng_2 $f class C $.
	fbrelrng_3 $f class F $.
	fbrelrng_4 $f class G $.
	brelrng $p |- ( ( A e. F /\ B e. G /\ A C B ) -> B e. ran C ) $= fbrelrng_0 fbrelrng_3 wcel fbrelrng_1 fbrelrng_4 wcel fbrelrng_0 fbrelrng_1 fbrelrng_2 wbr w3a fbrelrng_1 fbrelrng_2 ccnv cdm fbrelrng_2 crn fbrelrng_0 fbrelrng_3 wcel fbrelrng_1 fbrelrng_4 wcel fbrelrng_0 fbrelrng_1 fbrelrng_2 wbr fbrelrng_1 fbrelrng_0 fbrelrng_2 ccnv wbr fbrelrng_1 fbrelrng_2 ccnv cdm wcel fbrelrng_0 fbrelrng_3 wcel fbrelrng_1 fbrelrng_4 wcel fbrelrng_1 fbrelrng_0 fbrelrng_2 ccnv wbr fbrelrng_0 fbrelrng_1 fbrelrng_2 wbr fbrelrng_1 fbrelrng_4 wcel fbrelrng_0 fbrelrng_3 wcel fbrelrng_1 fbrelrng_0 fbrelrng_2 ccnv wbr fbrelrng_0 fbrelrng_1 fbrelrng_2 wbr wb fbrelrng_1 fbrelrng_0 fbrelrng_4 fbrelrng_3 fbrelrng_2 brcnvg ancoms biimp3ar fbrelrng_1 fbrelrng_4 wcel fbrelrng_0 fbrelrng_3 wcel fbrelrng_1 fbrelrng_0 fbrelrng_2 ccnv wbr fbrelrng_1 fbrelrng_2 ccnv cdm wcel fbrelrng_1 fbrelrng_0 fbrelrng_4 fbrelrng_3 fbrelrng_2 ccnv breldmg 3com12 syld3an3 fbrelrng_2 df-rn syl6eleqr $.
$}
$( The second argument of a binary relation belongs to its range.
       (Contributed by NM, 13-Aug-2004.) $)
${
	fbrelrn_0 $f class A $.
	fbrelrn_1 $f class B $.
	fbrelrn_2 $f class C $.
	ebrelrn_0 $e |- A e. _V $.
	ebrelrn_1 $e |- B e. _V $.
	brelrn $p |- ( A C B -> B e. ran C ) $= fbrelrn_0 cvv wcel fbrelrn_1 cvv wcel fbrelrn_0 fbrelrn_1 fbrelrn_2 wbr fbrelrn_1 fbrelrn_2 crn wcel ebrelrn_0 ebrelrn_1 fbrelrn_0 fbrelrn_1 fbrelrn_2 cvv cvv brelrng mp3an12 $.
$}
$( Membership of second member of an ordered pair in a range.  (Contributed
       by NM, 23-Feb-1997.) $)
${
	fopelrn_0 $f class A $.
	fopelrn_1 $f class B $.
	fopelrn_2 $f class C $.
	eopelrn_0 $e |- A e. _V $.
	eopelrn_1 $e |- B e. _V $.
	opelrn $p |- ( <. A , B >. e. C -> B e. ran C ) $= fopelrn_0 fopelrn_1 cop fopelrn_2 wcel fopelrn_0 fopelrn_1 fopelrn_2 wbr fopelrn_1 fopelrn_2 crn wcel fopelrn_0 fopelrn_1 fopelrn_2 df-br fopelrn_0 fopelrn_1 fopelrn_2 eopelrn_0 eopelrn_1 brelrn sylbir $.
$}
$( The first argument of a binary relation belongs to its domain.
     (Contributed by NM, 2-Jul-2008.) $)
${
	freleldm_0 $f class A $.
	freleldm_1 $f class B $.
	freleldm_2 $f class R $.
	releldm $p |- ( ( Rel R /\ A R B ) -> A e. dom R ) $= freleldm_2 wrel freleldm_0 freleldm_1 freleldm_2 wbr wa freleldm_0 cvv wcel freleldm_1 cvv wcel freleldm_0 freleldm_1 freleldm_2 wbr freleldm_0 freleldm_2 cdm wcel freleldm_0 freleldm_1 freleldm_2 brrelex freleldm_0 freleldm_1 freleldm_2 brrelex2 freleldm_2 wrel freleldm_0 freleldm_1 freleldm_2 wbr simpr freleldm_0 freleldm_1 cvv cvv freleldm_2 breldmg syl3anc $.
$}
$( The second argument of a binary relation belongs to its range.
     (Contributed by NM, 2-Jul-2008.) $)
${
	frelelrn_0 $f class A $.
	frelelrn_1 $f class B $.
	frelelrn_2 $f class R $.
	relelrn $p |- ( ( Rel R /\ A R B ) -> B e. ran R ) $= frelelrn_2 wrel frelelrn_0 frelelrn_1 frelelrn_2 wbr wa frelelrn_0 cvv wcel frelelrn_1 cvv wcel frelelrn_0 frelelrn_1 frelelrn_2 wbr frelelrn_1 frelelrn_2 crn wcel frelelrn_0 frelelrn_1 frelelrn_2 brrelex frelelrn_0 frelelrn_1 frelelrn_2 brrelex2 frelelrn_2 wrel frelelrn_0 frelelrn_1 frelelrn_2 wbr simpr frelelrn_0 frelelrn_1 frelelrn_2 cvv cvv brelrng syl3anc $.
$}
$( Membership in a domain.  (Contributed by Mario Carneiro, 5-Nov-2015.) $)
${
	$d x A $.
	$d x R $.
	freleldmb_0 $f set x $.
	freleldmb_1 $f class A $.
	freleldmb_2 $f class R $.
	releldmb $p |- ( Rel R -> ( A e. dom R <-> E. x A R x ) ) $= freleldmb_2 wrel freleldmb_1 freleldmb_2 cdm wcel freleldmb_1 freleldmb_0 sup_set_class freleldmb_2 wbr freleldmb_0 wex freleldmb_1 freleldmb_2 cdm wcel freleldmb_1 freleldmb_0 sup_set_class freleldmb_2 wbr freleldmb_0 wex freleldmb_0 freleldmb_1 freleldmb_2 freleldmb_2 cdm eldmg ibi freleldmb_2 wrel freleldmb_1 freleldmb_0 sup_set_class freleldmb_2 wbr freleldmb_1 freleldmb_2 cdm wcel freleldmb_0 freleldmb_2 wrel freleldmb_1 freleldmb_0 sup_set_class freleldmb_2 wbr freleldmb_1 freleldmb_2 cdm wcel freleldmb_1 freleldmb_0 sup_set_class freleldmb_2 releldm ex exlimdv impbid2 $.
$}
$( Membership in a range.  (Contributed by Mario Carneiro, 5-Nov-2015.) $)
${
	$d x A $.
	$d x R $.
	frelelrnb_0 $f set x $.
	frelelrnb_1 $f class A $.
	frelelrnb_2 $f class R $.
	relelrnb $p |- ( Rel R -> ( A e. ran R <-> E. x x R A ) ) $= frelelrnb_2 wrel frelelrnb_1 frelelrnb_2 crn wcel frelelrnb_0 sup_set_class frelelrnb_1 frelelrnb_2 wbr frelelrnb_0 wex frelelrnb_1 frelelrnb_2 crn wcel frelelrnb_0 sup_set_class frelelrnb_1 frelelrnb_2 wbr frelelrnb_0 wex frelelrnb_0 frelelrnb_1 frelelrnb_2 frelelrnb_2 crn elrng ibi frelelrnb_2 wrel frelelrnb_0 sup_set_class frelelrnb_1 frelelrnb_2 wbr frelelrnb_1 frelelrnb_2 crn wcel frelelrnb_0 frelelrnb_2 wrel frelelrnb_0 sup_set_class frelelrnb_1 frelelrnb_2 wbr frelelrnb_1 frelelrnb_2 crn wcel frelelrnb_0 sup_set_class frelelrnb_1 frelelrnb_2 relelrn ex exlimdv impbid2 $.
$}
$( The first argument of a binary relation belongs to its domain.
       (Contributed by NM, 28-Apr-2015.) $)
${
	freleldmi_0 $f class A $.
	freleldmi_1 $f class B $.
	freleldmi_2 $f class R $.
	ereleldmi_0 $e |- Rel R $.
	releldmi $p |- ( A R B -> A e. dom R ) $= freleldmi_2 wrel freleldmi_0 freleldmi_1 freleldmi_2 wbr freleldmi_0 freleldmi_2 cdm wcel ereleldmi_0 freleldmi_0 freleldmi_1 freleldmi_2 releldm mpan $.
$}
$( The second argument of a binary relation belongs to its range.
       (Contributed by NM, 28-Apr-2015.) $)
${
	frelelrni_0 $f class A $.
	frelelrni_1 $f class B $.
	frelelrni_2 $f class R $.
	erelelrni_0 $e |- Rel R $.
	relelrni $p |- ( A R B -> B e. ran R ) $= frelelrni_2 wrel frelelrni_0 frelelrni_1 frelelrni_2 wbr frelelrni_1 frelelrni_2 crn wcel erelelrni_0 frelelrni_0 frelelrni_1 frelelrni_2 relelrn mpan $.
$}
$( Definition of range, using bound-variable hypotheses instead of distinct
       variable conditions.  (Contributed by NM, 14-Aug-1995.)  (Revised by
       Mario Carneiro, 15-Oct-2016.) $)
${
	$d x y w v $.
	$d w v A $.
	idfrnf_0 $f set w $.
	idfrnf_1 $f set v $.
	fdfrnf_0 $f set x $.
	fdfrnf_1 $f set y $.
	fdfrnf_2 $f class A $.
	edfrnf_0 $e |- F/_ x A $.
	edfrnf_1 $e |- F/_ y A $.
	dfrnf $p |- ran A = { y | E. x x A y } $= fdfrnf_2 crn idfrnf_1 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr idfrnf_1 wex idfrnf_0 cab fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr fdfrnf_0 wex idfrnf_0 cab fdfrnf_0 sup_set_class fdfrnf_1 sup_set_class fdfrnf_2 wbr fdfrnf_0 wex fdfrnf_1 cab idfrnf_1 idfrnf_0 fdfrnf_2 dfrn2 idfrnf_1 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr idfrnf_1 wex fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr fdfrnf_0 wex idfrnf_0 idfrnf_1 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr idfrnf_1 fdfrnf_0 fdfrnf_0 idfrnf_1 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 fdfrnf_0 idfrnf_1 sup_set_class nfcv edfrnf_0 fdfrnf_0 idfrnf_0 sup_set_class nfcv nfbr fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr idfrnf_1 nfv idfrnf_1 sup_set_class fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 breq1 cbvex abbii fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr fdfrnf_0 wex fdfrnf_0 sup_set_class fdfrnf_1 sup_set_class fdfrnf_2 wbr fdfrnf_0 wex idfrnf_0 fdfrnf_1 fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr fdfrnf_1 fdfrnf_0 fdfrnf_1 fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 fdfrnf_1 fdfrnf_0 sup_set_class nfcv edfrnf_1 fdfrnf_1 idfrnf_0 sup_set_class nfcv nfbr nfex fdfrnf_0 sup_set_class fdfrnf_1 sup_set_class fdfrnf_2 wbr fdfrnf_0 wex idfrnf_0 nfv idfrnf_0 sup_set_class fdfrnf_1 sup_set_class wceq fdfrnf_0 sup_set_class idfrnf_0 sup_set_class fdfrnf_2 wbr fdfrnf_0 sup_set_class fdfrnf_1 sup_set_class fdfrnf_2 wbr fdfrnf_0 idfrnf_0 sup_set_class fdfrnf_1 sup_set_class fdfrnf_0 sup_set_class fdfrnf_2 breq2 exbidv cbvab 3eqtri $.
$}
$( Membership in a range.  (Contributed by NM, 10-Jul-1994.) $)
${
	$d x y A $.
	$d x y B $.
	ielrn2_0 $f set y $.
	felrn2_0 $f set x $.
	felrn2_1 $f class A $.
	felrn2_2 $f class B $.
	eelrn2_0 $e |- A e. _V $.
	elrn2 $p |- ( A e. ran B <-> E. x <. x , A >. e. B ) $= felrn2_0 sup_set_class ielrn2_0 sup_set_class cop felrn2_2 wcel felrn2_0 wex felrn2_0 sup_set_class felrn2_1 cop felrn2_2 wcel felrn2_0 wex ielrn2_0 felrn2_1 felrn2_2 crn eelrn2_0 ielrn2_0 sup_set_class felrn2_1 wceq felrn2_0 sup_set_class ielrn2_0 sup_set_class cop felrn2_2 wcel felrn2_0 sup_set_class felrn2_1 cop felrn2_2 wcel felrn2_0 ielrn2_0 sup_set_class felrn2_1 wceq felrn2_0 sup_set_class ielrn2_0 sup_set_class cop felrn2_0 sup_set_class felrn2_1 cop felrn2_2 ielrn2_0 sup_set_class felrn2_1 felrn2_0 sup_set_class opeq2 eleq1d exbidv felrn2_0 ielrn2_0 felrn2_2 dfrn3 elab2 $.
$}
$( Membership in a range.  (Contributed by NM, 2-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	felrn_0 $f set x $.
	felrn_1 $f class A $.
	felrn_2 $f class B $.
	eelrn_0 $e |- A e. _V $.
	elrn $p |- ( A e. ran B <-> E. x x B A ) $= felrn_1 felrn_2 crn wcel felrn_0 sup_set_class felrn_1 cop felrn_2 wcel felrn_0 wex felrn_0 sup_set_class felrn_1 felrn_2 wbr felrn_0 wex felrn_0 felrn_1 felrn_2 eelrn_0 elrn2 felrn_0 sup_set_class felrn_1 felrn_2 wbr felrn_0 sup_set_class felrn_1 cop felrn_2 wcel felrn_0 felrn_0 sup_set_class felrn_1 felrn_2 df-br exbii bitr4i $.
$}
$( Bound-variable hypothesis builder for domain.  (Contributed by NM,
       30-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	$d x y z $.
	$d y z A $.
	infdm_0 $f set y $.
	infdm_1 $f set z $.
	fnfdm_0 $f set x $.
	fnfdm_1 $f class A $.
	enfdm_0 $e |- F/_ x A $.
	nfdm $p |- F/_ x dom A $= fnfdm_0 fnfdm_1 cdm infdm_0 sup_set_class infdm_1 sup_set_class fnfdm_1 wbr infdm_1 wex infdm_0 cab infdm_0 infdm_1 fnfdm_1 df-dm infdm_0 sup_set_class infdm_1 sup_set_class fnfdm_1 wbr infdm_1 wex fnfdm_0 infdm_0 infdm_0 sup_set_class infdm_1 sup_set_class fnfdm_1 wbr fnfdm_0 infdm_1 fnfdm_0 infdm_0 sup_set_class infdm_1 sup_set_class fnfdm_1 fnfdm_0 infdm_0 sup_set_class nfcv enfdm_0 fnfdm_0 infdm_1 sup_set_class nfcv nfbr nfex nfab nfcxfr $.
$}
$( Bound-variable hypothesis builder for range.  (Contributed by NM,
       1-Sep-1999.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
${
	fnfrn_0 $f set x $.
	fnfrn_1 $f class A $.
	enfrn_0 $e |- F/_ x A $.
	nfrn $p |- F/_ x ran A $= fnfrn_0 fnfrn_1 crn fnfrn_1 ccnv cdm fnfrn_1 df-rn fnfrn_0 fnfrn_1 ccnv fnfrn_0 fnfrn_1 enfrn_0 nfcnv nfdm nfcxfr $.
$}
$( Domain of an intersection.  (Contributed by FL, 15-Oct-2012.) $)
${
	fdmiin_0 $f set x $.
	fdmiin_1 $f class A $.
	fdmiin_2 $f class B $.
	dmiin $p |- dom |^|_ x e. A B C_ |^|_ x e. A dom B $= fdmiin_0 fdmiin_1 fdmiin_2 ciin cdm fdmiin_0 fdmiin_1 fdmiin_2 cdm ciin wss fdmiin_0 fdmiin_1 fdmiin_2 ciin cdm fdmiin_2 cdm wss fdmiin_0 fdmiin_1 fdmiin_0 fdmiin_1 fdmiin_2 cdm fdmiin_0 fdmiin_1 fdmiin_2 ciin cdm fdmiin_0 fdmiin_0 fdmiin_1 fdmiin_2 ciin fdmiin_0 fdmiin_1 fdmiin_2 nfii1 nfdm ssiinf fdmiin_0 sup_set_class fdmiin_1 wcel fdmiin_0 fdmiin_1 fdmiin_2 ciin fdmiin_2 wss fdmiin_0 fdmiin_1 fdmiin_2 ciin cdm fdmiin_2 cdm wss fdmiin_0 fdmiin_1 fdmiin_2 iinss2 fdmiin_0 fdmiin_1 fdmiin_2 ciin fdmiin_2 dmss syl mprgbir $.
$}
$( Distribute proper substitution through the range of a class.
       (Contributed by Alan Sare, 10-Nov-2012.) $)
${
	$d A w y $.
	$d B w y $.
	$d V w y $.
	$d x w y $.
	icsbrng_0 $f set y $.
	icsbrng_1 $f set w $.
	fcsbrng_0 $f set x $.
	fcsbrng_1 $f class A $.
	fcsbrng_2 $f class B $.
	fcsbrng_3 $f class V $.
	csbrng $p |- ( A e. V -> [_ A / x ]_ ran B = ran [_ A / x ]_ B ) $= fcsbrng_1 fcsbrng_3 wcel fcsbrng_0 fcsbrng_1 icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex icsbrng_0 cab csb icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_0 fcsbrng_1 fcsbrng_2 csb wcel icsbrng_1 wex icsbrng_0 cab fcsbrng_0 fcsbrng_1 fcsbrng_2 crn csb fcsbrng_0 fcsbrng_1 fcsbrng_2 csb crn fcsbrng_1 fcsbrng_3 wcel fcsbrng_0 fcsbrng_1 icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex icsbrng_0 cab csb icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex fcsbrng_0 fcsbrng_1 wsbc icsbrng_0 cab icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_0 fcsbrng_1 fcsbrng_2 csb wcel icsbrng_1 wex icsbrng_0 cab icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex fcsbrng_0 icsbrng_0 fcsbrng_1 fcsbrng_3 csbabg fcsbrng_1 fcsbrng_3 wcel icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex fcsbrng_0 fcsbrng_1 wsbc icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_0 fcsbrng_1 fcsbrng_2 csb wcel icsbrng_1 wex icsbrng_0 fcsbrng_1 fcsbrng_3 wcel icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex fcsbrng_0 fcsbrng_1 wsbc icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel fcsbrng_0 fcsbrng_1 wsbc icsbrng_1 wex icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_0 fcsbrng_1 fcsbrng_2 csb wcel icsbrng_1 wex icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 fcsbrng_0 fcsbrng_1 fcsbrng_3 sbcexg fcsbrng_1 fcsbrng_3 wcel icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel fcsbrng_0 fcsbrng_1 wsbc icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_0 fcsbrng_1 fcsbrng_2 csb wcel icsbrng_1 fcsbrng_0 fcsbrng_1 icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 fcsbrng_3 sbcel2g exbidv bitrd abbidv eqtrd fcsbrng_0 fcsbrng_1 fcsbrng_2 crn icsbrng_1 sup_set_class icsbrng_0 sup_set_class cop fcsbrng_2 wcel icsbrng_1 wex icsbrng_0 cab icsbrng_1 icsbrng_0 fcsbrng_2 dfrn3 csbeq2i icsbrng_1 icsbrng_0 fcsbrng_0 fcsbrng_1 fcsbrng_2 csb dfrn3 3eqtr4g $.
$}
$( The range of a class of ordered pairs.  (Contributed by NM,
       14-Aug-1995.)  (Revised by Mario Carneiro, 4-Dec-2016.) $)
${
	$d x y $.
	frnopab_0 $f wff ph $.
	frnopab_1 $f set x $.
	frnopab_2 $f set y $.
	rnopab $p |- ran { <. x , y >. | ph } = { y | E. x ph } $= frnopab_0 frnopab_1 frnopab_2 copab crn frnopab_1 sup_set_class frnopab_2 sup_set_class frnopab_0 frnopab_1 frnopab_2 copab wbr frnopab_1 wex frnopab_2 cab frnopab_0 frnopab_1 wex frnopab_2 cab frnopab_1 frnopab_2 frnopab_0 frnopab_1 frnopab_2 copab frnopab_0 frnopab_1 frnopab_2 nfopab1 frnopab_0 frnopab_1 frnopab_2 nfopab2 dfrnf frnopab_1 sup_set_class frnopab_2 sup_set_class frnopab_0 frnopab_1 frnopab_2 copab wbr frnopab_1 wex frnopab_0 frnopab_1 wex frnopab_2 frnopab_1 sup_set_class frnopab_2 sup_set_class frnopab_0 frnopab_1 frnopab_2 copab wbr frnopab_0 frnopab_1 frnopab_1 sup_set_class frnopab_2 sup_set_class frnopab_0 frnopab_1 frnopab_2 copab wbr frnopab_1 sup_set_class frnopab_2 sup_set_class cop frnopab_0 frnopab_1 frnopab_2 copab wcel frnopab_0 frnopab_1 sup_set_class frnopab_2 sup_set_class frnopab_0 frnopab_1 frnopab_2 copab df-br frnopab_0 frnopab_1 frnopab_2 opabid bitri exbii abbii eqtri $.
$}
$( The range of a function in maps-to notation.  (Contributed by Scott
       Fenton, 21-Mar-2011.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$d y A $.
	$d y B $.
	$d x y $.
	frnmpt_0 $f set x $.
	frnmpt_1 $f set y $.
	frnmpt_2 $f class A $.
	frnmpt_3 $f class B $.
	frnmpt_4 $f class F $.
	ernmpt_0 $e |- F = ( x e. A |-> B ) $.
	rnmpt $p |- ran F = { y | E. x e. A y = B } $= frnmpt_0 sup_set_class frnmpt_2 wcel frnmpt_1 sup_set_class frnmpt_3 wceq wa frnmpt_0 frnmpt_1 copab crn frnmpt_0 sup_set_class frnmpt_2 wcel frnmpt_1 sup_set_class frnmpt_3 wceq wa frnmpt_0 wex frnmpt_1 cab frnmpt_4 crn frnmpt_1 sup_set_class frnmpt_3 wceq frnmpt_0 frnmpt_2 wrex frnmpt_1 cab frnmpt_0 sup_set_class frnmpt_2 wcel frnmpt_1 sup_set_class frnmpt_3 wceq wa frnmpt_0 frnmpt_1 rnopab frnmpt_4 frnmpt_0 sup_set_class frnmpt_2 wcel frnmpt_1 sup_set_class frnmpt_3 wceq wa frnmpt_0 frnmpt_1 copab frnmpt_4 frnmpt_0 frnmpt_2 frnmpt_3 cmpt frnmpt_0 sup_set_class frnmpt_2 wcel frnmpt_1 sup_set_class frnmpt_3 wceq wa frnmpt_0 frnmpt_1 copab ernmpt_0 frnmpt_0 frnmpt_1 frnmpt_2 frnmpt_3 df-mpt eqtri rneqi frnmpt_1 sup_set_class frnmpt_3 wceq frnmpt_0 frnmpt_2 wrex frnmpt_0 sup_set_class frnmpt_2 wcel frnmpt_1 sup_set_class frnmpt_3 wceq wa frnmpt_0 wex frnmpt_1 frnmpt_1 sup_set_class frnmpt_3 wceq frnmpt_0 frnmpt_2 df-rex abbii 3eqtr4i $.
$}
$( The range of a function in maps-to notation.  (Contributed by Mario
       Carneiro, 20-Feb-2015.) $)
${
	$d y A $.
	$d y B $.
	$d x y C $.
	ielrnmpt_0 $f set y $.
	felrnmpt_0 $f set x $.
	felrnmpt_1 $f class A $.
	felrnmpt_2 $f class B $.
	felrnmpt_3 $f class C $.
	felrnmpt_4 $f class F $.
	felrnmpt_5 $f class V $.
	eelrnmpt_0 $e |- F = ( x e. A |-> B ) $.
	elrnmpt $p |- ( C e. V -> ( C e. ran F <-> E. x e. A C = B ) ) $= ielrnmpt_0 sup_set_class felrnmpt_2 wceq felrnmpt_0 felrnmpt_1 wrex felrnmpt_3 felrnmpt_2 wceq felrnmpt_0 felrnmpt_1 wrex ielrnmpt_0 felrnmpt_3 felrnmpt_4 crn felrnmpt_5 ielrnmpt_0 sup_set_class felrnmpt_3 wceq ielrnmpt_0 sup_set_class felrnmpt_2 wceq felrnmpt_3 felrnmpt_2 wceq felrnmpt_0 felrnmpt_1 ielrnmpt_0 sup_set_class felrnmpt_3 felrnmpt_2 eqeq1 rexbidv felrnmpt_0 ielrnmpt_0 felrnmpt_1 felrnmpt_2 felrnmpt_4 eelrnmpt_0 rnmpt elab2g $.
$}
$( Elementhood in an image set.  (Contributed by Mario Carneiro,
         12-Sep-2015.) $)
${
	$d x C $.
	$d x A $.
	$d x D $.
	felrnmpt1s_0 $f set x $.
	felrnmpt1s_1 $f class A $.
	felrnmpt1s_2 $f class B $.
	felrnmpt1s_3 $f class C $.
	felrnmpt1s_4 $f class D $.
	felrnmpt1s_5 $f class F $.
	felrnmpt1s_6 $f class V $.
	eelrnmpt1s_0 $e |- F = ( x e. A |-> B ) $.
	eelrnmpt1s_1 $e |- ( x = D -> B = C ) $.
	elrnmpt1s $p |- ( ( D e. A /\ C e. V ) -> C e. ran F ) $= felrnmpt1s_4 felrnmpt1s_1 wcel felrnmpt1s_3 felrnmpt1s_2 wceq felrnmpt1s_0 felrnmpt1s_1 wrex felrnmpt1s_3 felrnmpt1s_6 wcel felrnmpt1s_3 felrnmpt1s_5 crn wcel felrnmpt1s_4 felrnmpt1s_1 wcel felrnmpt1s_3 felrnmpt1s_3 wceq felrnmpt1s_3 felrnmpt1s_2 wceq felrnmpt1s_0 felrnmpt1s_1 wrex felrnmpt1s_3 eqid felrnmpt1s_3 felrnmpt1s_2 wceq felrnmpt1s_3 felrnmpt1s_3 wceq felrnmpt1s_0 felrnmpt1s_4 felrnmpt1s_1 felrnmpt1s_0 sup_set_class felrnmpt1s_4 wceq felrnmpt1s_2 felrnmpt1s_3 felrnmpt1s_3 eelrnmpt1s_1 eqeq2d rspcev mpan2 felrnmpt1s_3 felrnmpt1s_6 wcel felrnmpt1s_3 felrnmpt1s_5 crn wcel felrnmpt1s_3 felrnmpt1s_2 wceq felrnmpt1s_0 felrnmpt1s_1 wrex felrnmpt1s_0 felrnmpt1s_1 felrnmpt1s_2 felrnmpt1s_3 felrnmpt1s_5 felrnmpt1s_6 eelrnmpt1s_0 elrnmpt biimparc sylan $.
$}
$( Elementhood in an image set.  (Contributed by Mario Carneiro,
       31-Aug-2015.) $)
${
	$d y z A $.
	$d y z B $.
	$d x y z $.
	ielrnmpt1_0 $f set y $.
	ielrnmpt1_1 $f set z $.
	felrnmpt1_0 $f set x $.
	felrnmpt1_1 $f class A $.
	felrnmpt1_2 $f class B $.
	felrnmpt1_3 $f class F $.
	felrnmpt1_4 $f class V $.
	eelrnmpt1_0 $e |- F = ( x e. A |-> B ) $.
	elrnmpt1 $p |- ( ( x e. A /\ B e. V ) -> B e. ran F ) $= felrnmpt1_2 felrnmpt1_4 wcel felrnmpt1_0 sup_set_class felrnmpt1_1 wcel felrnmpt1_2 felrnmpt1_3 crn wcel felrnmpt1_0 sup_set_class felrnmpt1_1 wcel felrnmpt1_2 felrnmpt1_3 crn wcel felrnmpt1_2 felrnmpt1_4 wcel ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 wex ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa felrnmpt1_0 sup_set_class felrnmpt1_1 wcel ielrnmpt1_1 felrnmpt1_0 sup_set_class felrnmpt1_0 vex ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa felrnmpt1_0 sup_set_class felrnmpt1_1 wcel wb felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq felrnmpt1_0 sup_set_class felrnmpt1_1 wcel ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class felrnmpt1_1 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq id felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csbeq1a eleq12d felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csbeq1a biantrud bitr2d eqcoms spcev ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq felrnmpt1_0 felrnmpt1_1 wrex ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 wex ielrnmpt1_0 felrnmpt1_2 felrnmpt1_3 crn felrnmpt1_4 ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq felrnmpt1_0 felrnmpt1_1 wrex ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 wex ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 wex ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq felrnmpt1_0 felrnmpt1_1 wrex felrnmpt1_0 sup_set_class felrnmpt1_1 wcel ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq wa felrnmpt1_0 wex ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 wex ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq felrnmpt1_0 felrnmpt1_1 df-rex felrnmpt1_0 sup_set_class felrnmpt1_1 wcel ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq wa ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa felrnmpt1_0 ielrnmpt1_1 felrnmpt1_0 sup_set_class felrnmpt1_1 wcel ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq wa ielrnmpt1_1 nfv ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq felrnmpt1_0 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 nfcsb1v nfel2 felrnmpt1_0 ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 nfcsb1v nfeq2 nfan felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq felrnmpt1_0 sup_set_class felrnmpt1_1 wcel ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class felrnmpt1_1 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq id felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csbeq1a eleq12d felrnmpt1_0 sup_set_class ielrnmpt1_1 sup_set_class wceq felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csbeq1a eqeq2d anbi12d cbvex bitri ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq wa ielrnmpt1_1 ielrnmpt1_0 sup_set_class felrnmpt1_2 wceq ielrnmpt1_0 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb wceq ielrnmpt1_1 sup_set_class felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_1 csb wcel ielrnmpt1_0 sup_set_class felrnmpt1_2 felrnmpt1_0 ielrnmpt1_1 sup_set_class felrnmpt1_2 csb eqeq1 anbi2d exbidv syl5bb felrnmpt1_0 ielrnmpt1_0 felrnmpt1_1 felrnmpt1_2 felrnmpt1_3 eelrnmpt1_0 rnmpt elab2g syl5ibr impcom $.
$}
$( Membership in the range of a function.  (Contributed by NM,
       27-Aug-2007.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$d y A $.
	$d y B $.
	$d x y C $.
	ielrnmptg_0 $f set y $.
	felrnmptg_0 $f set x $.
	felrnmptg_1 $f class A $.
	felrnmptg_2 $f class B $.
	felrnmptg_3 $f class C $.
	felrnmptg_4 $f class F $.
	felrnmptg_5 $f class V $.
	eelrnmptg_0 $e |- F = ( x e. A |-> B ) $.
	elrnmptg $p |- ( A. x e. A B e. V -> ( C e. ran F <-> E. x e. A C = B ) ) $= felrnmptg_3 felrnmptg_4 crn wcel felrnmptg_3 ielrnmptg_0 sup_set_class felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex ielrnmptg_0 cab wcel felrnmptg_2 felrnmptg_5 wcel felrnmptg_0 felrnmptg_1 wral felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex felrnmptg_4 crn ielrnmptg_0 sup_set_class felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex ielrnmptg_0 cab felrnmptg_3 felrnmptg_0 ielrnmptg_0 felrnmptg_1 felrnmptg_2 felrnmptg_4 eelrnmptg_0 rnmpt eleq2i felrnmptg_2 felrnmptg_5 wcel felrnmptg_0 felrnmptg_1 wral felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex felrnmptg_3 cvv wcel wi felrnmptg_3 ielrnmptg_0 sup_set_class felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex ielrnmptg_0 cab wcel felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex wb felrnmptg_2 felrnmptg_5 wcel felrnmptg_0 felrnmptg_1 wral felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex felrnmptg_3 cvv wcel felrnmptg_2 felrnmptg_5 wcel felrnmptg_0 felrnmptg_1 wral felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex wa felrnmptg_2 felrnmptg_5 wcel felrnmptg_3 felrnmptg_2 wceq wa felrnmptg_0 felrnmptg_1 wrex felrnmptg_3 cvv wcel felrnmptg_2 felrnmptg_5 wcel felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 r19.29 felrnmptg_2 felrnmptg_5 wcel felrnmptg_3 felrnmptg_2 wceq wa felrnmptg_3 cvv wcel felrnmptg_0 felrnmptg_1 felrnmptg_2 felrnmptg_5 wcel felrnmptg_3 felrnmptg_2 wceq wa felrnmptg_3 felrnmptg_5 wcel felrnmptg_3 cvv wcel felrnmptg_3 felrnmptg_2 wceq felrnmptg_3 felrnmptg_5 wcel felrnmptg_2 felrnmptg_5 wcel felrnmptg_3 felrnmptg_2 felrnmptg_5 eleq1 biimparc felrnmptg_3 felrnmptg_5 elex syl rexlimivw syl ex ielrnmptg_0 sup_set_class felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 wrex ielrnmptg_0 felrnmptg_3 cvv ielrnmptg_0 sup_set_class felrnmptg_3 wceq ielrnmptg_0 sup_set_class felrnmptg_2 wceq felrnmptg_3 felrnmptg_2 wceq felrnmptg_0 felrnmptg_1 ielrnmptg_0 sup_set_class felrnmptg_3 felrnmptg_2 eqeq1 rexbidv elab3g syl syl5bb $.
$}
$( Membership in the range of a function.  (Contributed by NM,
       30-Aug-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
${
	$d x C $.
	felrnmpti_0 $f set x $.
	felrnmpti_1 $f class A $.
	felrnmpti_2 $f class B $.
	felrnmpti_3 $f class C $.
	felrnmpti_4 $f class F $.
	eelrnmpti_0 $e |- F = ( x e. A |-> B ) $.
	eelrnmpti_1 $e |- B e. _V $.
	elrnmpti $p |- ( C e. ran F <-> E. x e. A C = B ) $= felrnmpti_2 cvv wcel felrnmpti_0 felrnmpti_1 wral felrnmpti_3 felrnmpti_4 crn wcel felrnmpti_3 felrnmpti_2 wceq felrnmpti_0 felrnmpti_1 wrex wb felrnmpti_2 cvv wcel felrnmpti_0 felrnmpti_1 eelrnmpti_1 rgenw felrnmpti_0 felrnmpti_1 felrnmpti_2 felrnmpti_3 felrnmpti_4 cvv eelrnmpti_0 elrnmptg ax-mp $.
$}
$( Alternate definition of indexed union when ` B ` is a set.  (Contributed
       by Mario Carneiro, 31-Aug-2015.) $)
${
	$d y A $.
	$d y B $.
	$d x y $.
	idfiun3g_0 $f set y $.
	fdfiun3g_0 $f set x $.
	fdfiun3g_1 $f class A $.
	fdfiun3g_2 $f class B $.
	fdfiun3g_3 $f class C $.
	dfiun3g $p |- ( A. x e. A B e. C -> U_ x e. A B = U. ran ( x e. A |-> B ) ) $= fdfiun3g_2 fdfiun3g_3 wcel fdfiun3g_0 fdfiun3g_1 wral fdfiun3g_0 fdfiun3g_1 fdfiun3g_2 ciun idfiun3g_0 sup_set_class fdfiun3g_2 wceq fdfiun3g_0 fdfiun3g_1 wrex idfiun3g_0 cab cuni fdfiun3g_0 fdfiun3g_1 fdfiun3g_2 cmpt crn cuni fdfiun3g_0 idfiun3g_0 fdfiun3g_1 fdfiun3g_2 fdfiun3g_3 dfiun2g fdfiun3g_0 fdfiun3g_1 fdfiun3g_2 cmpt crn idfiun3g_0 sup_set_class fdfiun3g_2 wceq fdfiun3g_0 fdfiun3g_1 wrex idfiun3g_0 cab fdfiun3g_0 idfiun3g_0 fdfiun3g_1 fdfiun3g_2 fdfiun3g_0 fdfiun3g_1 fdfiun3g_2 cmpt fdfiun3g_0 fdfiun3g_1 fdfiun3g_2 cmpt eqid rnmpt unieqi syl6eqr $.
$}
$( Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Mario Carneiro, 31-Aug-2015.) $)
${
	$d y A $.
	$d y B $.
	$d x y $.
	idfiin3g_0 $f set y $.
	fdfiin3g_0 $f set x $.
	fdfiin3g_1 $f class A $.
	fdfiin3g_2 $f class B $.
	fdfiin3g_3 $f class C $.
	dfiin3g $p |- ( A. x e. A B e. C -> |^|_ x e. A B = |^| ran ( x e. A |-> B ) ) $= fdfiin3g_2 fdfiin3g_3 wcel fdfiin3g_0 fdfiin3g_1 wral fdfiin3g_0 fdfiin3g_1 fdfiin3g_2 ciin idfiin3g_0 sup_set_class fdfiin3g_2 wceq fdfiin3g_0 fdfiin3g_1 wrex idfiin3g_0 cab cint fdfiin3g_0 fdfiin3g_1 fdfiin3g_2 cmpt crn cint fdfiin3g_0 idfiin3g_0 fdfiin3g_1 fdfiin3g_2 fdfiin3g_3 dfiin2g fdfiin3g_0 fdfiin3g_1 fdfiin3g_2 cmpt crn idfiin3g_0 sup_set_class fdfiin3g_2 wceq fdfiin3g_0 fdfiin3g_1 wrex idfiin3g_0 cab fdfiin3g_0 idfiin3g_0 fdfiin3g_1 fdfiin3g_2 fdfiin3g_0 fdfiin3g_1 fdfiin3g_2 cmpt fdfiin3g_0 fdfiin3g_1 fdfiin3g_2 cmpt eqid rnmpt inteqi syl6eqr $.
$}
$( Alternate definition of indexed union when ` B ` is a set.  (Contributed
       by Mario Carneiro, 31-Aug-2015.) $)
${
	fdfiun3_0 $f set x $.
	fdfiun3_1 $f class A $.
	fdfiun3_2 $f class B $.
	edfiun3_0 $e |- B e. _V $.
	dfiun3 $p |- U_ x e. A B = U. ran ( x e. A |-> B ) $= fdfiun3_2 cvv wcel fdfiun3_0 fdfiun3_1 fdfiun3_2 ciun fdfiun3_0 fdfiun3_1 fdfiun3_2 cmpt crn cuni wceq fdfiun3_0 fdfiun3_1 fdfiun3_0 fdfiun3_1 fdfiun3_2 cvv dfiun3g fdfiun3_2 cvv wcel fdfiun3_0 sup_set_class fdfiun3_1 wcel edfiun3_0 a1i mprg $.
$}
$( Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Mario Carneiro, 31-Aug-2015.) $)
${
	fdfiin3_0 $f set x $.
	fdfiin3_1 $f class A $.
	fdfiin3_2 $f class B $.
	edfiin3_0 $e |- B e. _V $.
	dfiin3 $p |- |^|_ x e. A B = |^| ran ( x e. A |-> B ) $= fdfiin3_2 cvv wcel fdfiin3_0 fdfiin3_1 fdfiin3_2 ciin fdfiin3_0 fdfiin3_1 fdfiin3_2 cmpt crn cint wceq fdfiin3_0 fdfiin3_1 fdfiin3_0 fdfiin3_1 fdfiin3_2 cvv dfiin3g fdfiin3_2 cvv wcel fdfiin3_0 sup_set_class fdfiin3_1 wcel edfiin3_0 a1i mprg $.
$}
$( Express a relative indexed intersection as an intersection.
       (Contributed by Stefan O'Rear, 22-Feb-2015.) $)
$v k $.
$v I $.
${
	$d V k $.
	$d X k $.
	friinint_0 $f class S $.
	friinint_1 $f set k $.
	friinint_2 $f class I $.
	friinint_3 $f class V $.
	friinint_4 $f class X $.
	riinint $p |- ( ( X e. V /\ A. k e. I S C_ X ) -> ( X i^i |^|_ k e. I S ) = |^| ( { X } u. ran ( k e. I |-> S ) ) ) $= friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_1 friinint_2 wral wa friinint_4 friinint_1 friinint_2 friinint_0 ciin cin friinint_4 friinint_1 friinint_2 friinint_0 cmpt crn cint cin friinint_4 csn friinint_1 friinint_2 friinint_0 cmpt crn cun cint friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_1 friinint_2 wral wa friinint_1 friinint_2 friinint_0 ciin friinint_1 friinint_2 friinint_0 cmpt crn cint friinint_4 friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_1 friinint_2 wral wa friinint_0 cvv wcel friinint_1 friinint_2 wral friinint_1 friinint_2 friinint_0 ciin friinint_1 friinint_2 friinint_0 cmpt crn cint wceq friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_1 friinint_2 wral friinint_0 cvv wcel friinint_1 friinint_2 wral friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_0 cvv wcel friinint_1 friinint_2 friinint_0 friinint_4 wss friinint_4 friinint_3 wcel friinint_0 cvv wcel friinint_0 friinint_4 friinint_3 ssexg expcom ralimdv imp friinint_1 friinint_2 friinint_0 cvv dfiin3g syl ineq2d friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_1 friinint_2 wral wa friinint_4 csn friinint_1 friinint_2 friinint_0 cmpt crn cun cint friinint_4 csn cint friinint_1 friinint_2 friinint_0 cmpt crn cint cin friinint_4 friinint_1 friinint_2 friinint_0 cmpt crn cint cin friinint_4 csn friinint_1 friinint_2 friinint_0 cmpt crn intun friinint_4 friinint_3 wcel friinint_0 friinint_4 wss friinint_1 friinint_2 wral wa friinint_4 csn cint friinint_4 friinint_1 friinint_2 friinint_0 cmpt crn cint friinint_4 friinint_3 wcel friinint_4 csn cint friinint_4 wceq friinint_0 friinint_4 wss friinint_1 friinint_2 wral friinint_4 friinint_3 intsng adantr ineq1d syl5eq eqtr4d $.
$}
$( The range of the empty set is empty.  Part of Theorem 3.8(v) of [Monk1]
     p. 36.  (Contributed by NM, 4-Jul-1994.) $)
${
	rn0 $p |- ran (/) = (/) $= c0 cdm c0 wceq c0 crn c0 wceq dm0 c0 dm0rn0 mpbi $.
$}
$( A relation is empty iff its range is empty.  (Contributed by NM,
       15-Sep-2004.) $)
${
	frelrn0_0 $f class A $.
	relrn0 $p |- ( Rel A -> ( A = (/) <-> ran A = (/) ) ) $= frelrn0_0 wrel frelrn0_0 c0 wceq frelrn0_0 cdm c0 wceq frelrn0_0 crn c0 wceq frelrn0_0 reldm0 frelrn0_0 dm0rn0 syl6bb $.
$}
$( The domain and range of a class are included in its double union.
       (Contributed by NM, 13-May-2008.) $)
${
	$d x y A $.
	idmrnssfld_0 $f set x $.
	idmrnssfld_1 $f set y $.
	fdmrnssfld_0 $f class A $.
	dmrnssfld $p |- ( dom A u. ran A ) C_ U. U. A $= fdmrnssfld_0 cdm fdmrnssfld_0 crn fdmrnssfld_0 cuni cuni idmrnssfld_0 fdmrnssfld_0 cdm fdmrnssfld_0 cuni cuni idmrnssfld_0 sup_set_class fdmrnssfld_0 cdm wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_1 wex idmrnssfld_0 sup_set_class fdmrnssfld_0 cuni cuni wcel idmrnssfld_1 idmrnssfld_0 sup_set_class fdmrnssfld_0 idmrnssfld_0 vex eldm2 idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class fdmrnssfld_0 cuni cuni wcel idmrnssfld_1 idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr wcel idmrnssfld_0 sup_set_class fdmrnssfld_0 cuni cuni wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class idmrnssfld_0 vex prid1 idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni cuni idmrnssfld_0 sup_set_class idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni cuni wss idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop cuni fdmrnssfld_0 cuni idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class idmrnssfld_0 vex idmrnssfld_1 vex uniop idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class fdmrnssfld_0 idmrnssfld_0 vex idmrnssfld_1 vex uniopel syl5eqelr idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni elssuni syl sseld mpi exlimiv sylbi ssriv idmrnssfld_1 fdmrnssfld_0 crn fdmrnssfld_0 cuni cuni idmrnssfld_1 sup_set_class fdmrnssfld_0 crn wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 wex idmrnssfld_1 sup_set_class fdmrnssfld_0 cuni cuni wcel idmrnssfld_0 idmrnssfld_1 sup_set_class fdmrnssfld_0 idmrnssfld_1 vex elrn2 idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_1 sup_set_class fdmrnssfld_0 cuni cuni wcel idmrnssfld_0 idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_1 sup_set_class idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr wcel idmrnssfld_1 sup_set_class fdmrnssfld_0 cuni cuni wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class idmrnssfld_1 vex prid2 idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni cuni idmrnssfld_1 sup_set_class idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni cuni wss idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop fdmrnssfld_0 wcel idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cop cuni fdmrnssfld_0 cuni idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class idmrnssfld_0 vex idmrnssfld_1 vex uniop idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class fdmrnssfld_0 idmrnssfld_0 vex idmrnssfld_1 vex uniopel syl5eqelr idmrnssfld_0 sup_set_class idmrnssfld_1 sup_set_class cpr fdmrnssfld_0 cuni elssuni syl sseld mpi exlimiv sylbi ssriv unssi $.
$}
$( The domain of a set is a set.  Corollary 6.8(2) of [TakeutiZaring] p. 26.
     (Contributed by NM, 7-Apr-1995.) $)
${
	fdmexg_0 $f class A $.
	fdmexg_1 $f class V $.
	dmexg $p |- ( A e. V -> dom A e. _V ) $= fdmexg_0 fdmexg_1 wcel fdmexg_0 cuni cvv wcel fdmexg_0 cuni cuni cvv wcel fdmexg_0 cdm cvv wcel fdmexg_0 fdmexg_1 uniexg fdmexg_0 cuni cvv uniexg fdmexg_0 cdm fdmexg_0 cuni cuni wss fdmexg_0 cuni cuni cvv wcel fdmexg_0 cdm cvv wcel fdmexg_0 cdm fdmexg_0 cdm fdmexg_0 crn cun fdmexg_0 cuni cuni fdmexg_0 cdm fdmexg_0 crn ssun1 fdmexg_0 dmrnssfld sstri fdmexg_0 cdm fdmexg_0 cuni cuni cvv ssexg mpan 3syl $.
$}
$( The range of a set is a set.  Corollary 6.8(3) of [TakeutiZaring] p. 26.
     Similar to Lemma 3D of [Enderton] p. 41.  (Contributed by NM,
     31-Mar-1995.) $)
${
	frnexg_0 $f class A $.
	frnexg_1 $f class V $.
	rnexg $p |- ( A e. V -> ran A e. _V ) $= frnexg_0 frnexg_1 wcel frnexg_0 cuni cvv wcel frnexg_0 cuni cuni cvv wcel frnexg_0 crn cvv wcel frnexg_0 frnexg_1 uniexg frnexg_0 cuni cvv uniexg frnexg_0 crn frnexg_0 cuni cuni wss frnexg_0 cuni cuni cvv wcel frnexg_0 crn cvv wcel frnexg_0 crn frnexg_0 cdm frnexg_0 crn cun frnexg_0 cuni cuni frnexg_0 crn frnexg_0 cdm ssun2 frnexg_0 dmrnssfld sstri frnexg_0 crn frnexg_0 cuni cuni cvv ssexg mpan 3syl $.
$}
$( The domain of a set is a set.  Corollary 6.8(2) of [TakeutiZaring]
       p. 26.  (Contributed by NM, 7-Jul-2008.) $)
${
	fdmex_0 $f class A $.
	edmex_0 $e |- A e. _V $.
	dmex $p |- dom A e. _V $= fdmex_0 cvv wcel fdmex_0 cdm cvv wcel edmex_0 fdmex_0 cvv dmexg ax-mp $.
$}
$( The range of a set is a set.  Corollary 6.8(3) of [TakeutiZaring]
       p. 26.  Similar to Lemma 3D of [Enderton] p. 41.  (Contributed by NM,
       7-Jul-2008.) $)
${
	frnex_0 $f class A $.
	ernex_0 $e |- A e. _V $.
	rnex $p |- ran A e. _V $= frnex_0 cvv wcel frnex_0 crn cvv wcel ernex_0 frnex_0 cvv rnexg ax-mp $.
$}
$( The identity function is a proper class.  This means, for example, that we
     cannot use it as a member of the class of continuous functions unless it
     is restricted to a set, as in ~ idcn .  (Contributed by NM,
     1-Jan-2007.) $)
${
	iprc $p |- -. _I e. _V $= cid cvv wcel cid cdm cvv wcel cid cdm cvv wcel cvv cvv wcel vprc cid cdm cvv cvv dmi eleq1i mtbir cid cvv dmexg mto $.
$}
$( Domain of a composition.  Theorem 21 of [Suppes] p. 63.  (Contributed by
       NM, 19-Mar-1998.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	idmcoss_0 $f set x $.
	idmcoss_1 $f set y $.
	idmcoss_2 $f set z $.
	fdmcoss_0 $f class A $.
	fdmcoss_1 $f class B $.
	dmcoss $p |- dom ( A o. B ) C_ dom B $= idmcoss_0 fdmcoss_0 fdmcoss_1 ccom cdm fdmcoss_1 cdm idmcoss_0 sup_set_class idmcoss_1 sup_set_class cop fdmcoss_0 fdmcoss_1 ccom wcel idmcoss_1 wex idmcoss_0 sup_set_class idmcoss_1 sup_set_class fdmcoss_1 wbr idmcoss_1 wex idmcoss_0 sup_set_class fdmcoss_0 fdmcoss_1 ccom cdm wcel idmcoss_0 sup_set_class fdmcoss_1 cdm wcel idmcoss_0 sup_set_class idmcoss_1 sup_set_class cop fdmcoss_0 fdmcoss_1 ccom wcel idmcoss_0 sup_set_class idmcoss_1 sup_set_class fdmcoss_1 wbr idmcoss_1 wex idmcoss_1 idmcoss_0 sup_set_class idmcoss_1 sup_set_class fdmcoss_1 wbr idmcoss_1 nfe1 idmcoss_0 sup_set_class idmcoss_2 sup_set_class fdmcoss_1 wbr idmcoss_2 sup_set_class idmcoss_1 sup_set_class fdmcoss_0 wbr wa idmcoss_2 wex idmcoss_0 sup_set_class idmcoss_2 sup_set_class fdmcoss_1 wbr idmcoss_2 wex idmcoss_0 sup_set_class idmcoss_1 sup_set_class cop fdmcoss_0 fdmcoss_1 ccom wcel idmcoss_0 sup_set_class idmcoss_1 sup_set_class fdmcoss_1 wbr idmcoss_1 wex idmcoss_0 sup_set_class idmcoss_2 sup_set_class fdmcoss_1 wbr idmcoss_2 sup_set_class idmcoss_1 sup_set_class fdmcoss_0 wbr idmcoss_2 exsimpl idmcoss_2 idmcoss_0 sup_set_class idmcoss_1 sup_set_class fdmcoss_0 fdmcoss_1 idmcoss_0 vex idmcoss_1 vex opelco idmcoss_0 sup_set_class idmcoss_1 sup_set_class fdmcoss_1 wbr idmcoss_0 sup_set_class idmcoss_2 sup_set_class fdmcoss_1 wbr idmcoss_1 idmcoss_2 idmcoss_1 sup_set_class idmcoss_2 sup_set_class idmcoss_0 sup_set_class fdmcoss_1 breq2 cbvexv 3imtr4i exlimi idmcoss_1 idmcoss_0 sup_set_class fdmcoss_0 fdmcoss_1 ccom idmcoss_0 vex eldm2 idmcoss_1 idmcoss_0 sup_set_class fdmcoss_1 idmcoss_0 vex eldm 3imtr4i ssriv $.
$}
$( Range of a composition.  (Contributed by NM, 19-Mar-1998.) $)
${
	frncoss_0 $f class A $.
	frncoss_1 $f class B $.
	rncoss $p |- ran ( A o. B ) C_ ran A $= frncoss_1 ccnv frncoss_0 ccnv ccom cdm frncoss_0 ccnv cdm frncoss_0 frncoss_1 ccom crn frncoss_0 crn frncoss_1 ccnv frncoss_0 ccnv dmcoss frncoss_0 frncoss_1 ccom crn frncoss_0 frncoss_1 ccom ccnv cdm frncoss_1 ccnv frncoss_0 ccnv ccom cdm frncoss_0 frncoss_1 ccom df-rn frncoss_0 frncoss_1 ccom ccnv frncoss_1 ccnv frncoss_0 ccnv ccom frncoss_0 frncoss_1 cnvco dmeqi eqtri frncoss_0 df-rn 3sstr4i $.
$}
$( Domain of a composition.  (Contributed by NM, 28-May-1998.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	idmcosseq_0 $f set x $.
	idmcosseq_1 $f set y $.
	idmcosseq_2 $f set z $.
	fdmcosseq_0 $f class A $.
	fdmcosseq_1 $f class B $.
	dmcosseq $p |- ( ran B C_ dom A -> dom ( A o. B ) = dom B ) $= fdmcosseq_1 crn fdmcosseq_0 cdm wss fdmcosseq_0 fdmcosseq_1 ccom cdm fdmcosseq_1 cdm fdmcosseq_0 fdmcosseq_1 ccom cdm fdmcosseq_1 cdm wss fdmcosseq_1 crn fdmcosseq_0 cdm wss fdmcosseq_0 fdmcosseq_1 dmcoss a1i fdmcosseq_1 crn fdmcosseq_0 cdm wss idmcosseq_0 fdmcosseq_1 cdm fdmcosseq_0 fdmcosseq_1 ccom cdm fdmcosseq_1 crn fdmcosseq_0 cdm wss idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 wex idmcosseq_0 sup_set_class idmcosseq_2 sup_set_class cop fdmcosseq_0 fdmcosseq_1 ccom wcel idmcosseq_2 wex idmcosseq_0 sup_set_class fdmcosseq_1 cdm wcel idmcosseq_0 sup_set_class fdmcosseq_0 fdmcosseq_1 ccom cdm wcel fdmcosseq_1 crn fdmcosseq_0 cdm wss idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 wex idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_1 wex idmcosseq_2 wex idmcosseq_0 sup_set_class idmcosseq_2 sup_set_class cop fdmcosseq_0 fdmcosseq_1 ccom wcel idmcosseq_2 wex fdmcosseq_1 crn fdmcosseq_0 cdm wss idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 wex idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 wex idmcosseq_1 wex idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_1 wex idmcosseq_2 wex fdmcosseq_1 crn fdmcosseq_0 cdm wss idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 wex idmcosseq_1 fdmcosseq_1 crn fdmcosseq_0 cdm wss idmcosseq_1 sup_set_class fdmcosseq_1 crn wcel idmcosseq_1 sup_set_class fdmcosseq_0 cdm wcel wi idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 wex wi fdmcosseq_1 crn fdmcosseq_0 cdm idmcosseq_1 sup_set_class ssel idmcosseq_1 sup_set_class fdmcosseq_1 crn wcel idmcosseq_1 sup_set_class fdmcosseq_0 cdm wcel wi idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 wex idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr idmcosseq_2 wex wi idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 wex wi idmcosseq_1 sup_set_class fdmcosseq_1 crn wcel idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 wex idmcosseq_1 sup_set_class fdmcosseq_0 cdm wcel idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr idmcosseq_2 wex idmcosseq_0 idmcosseq_1 sup_set_class fdmcosseq_1 idmcosseq_1 vex elrn idmcosseq_2 idmcosseq_1 sup_set_class fdmcosseq_0 idmcosseq_1 vex eldm imbi12i idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 wex idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr idmcosseq_2 wex wi idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr idmcosseq_2 wex idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 wex idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 wex idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr idmcosseq_2 wex idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_0 19.8a imim1i idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr pm3.2 eximdv sylcom sylbi syl eximdv idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_2 idmcosseq_1 excom syl6ibr idmcosseq_0 sup_set_class idmcosseq_2 sup_set_class cop fdmcosseq_0 fdmcosseq_1 ccom wcel idmcosseq_0 sup_set_class idmcosseq_1 sup_set_class fdmcosseq_1 wbr idmcosseq_1 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 wbr wa idmcosseq_1 wex idmcosseq_2 idmcosseq_1 idmcosseq_0 sup_set_class idmcosseq_2 sup_set_class fdmcosseq_0 fdmcosseq_1 idmcosseq_0 vex idmcosseq_2 vex opelco exbii syl6ibr idmcosseq_1 idmcosseq_0 sup_set_class fdmcosseq_1 idmcosseq_0 vex eldm idmcosseq_2 idmcosseq_0 sup_set_class fdmcosseq_0 fdmcosseq_1 ccom idmcosseq_0 vex eldm2 3imtr4g ssrdv eqssd $.
$}
$( Domain of a composition.  (Contributed by NM, 19-Mar-1998.) $)
${
	fdmcoeq_0 $f class A $.
	fdmcoeq_1 $f class B $.
	dmcoeq $p |- ( dom A = ran B -> dom ( A o. B ) = dom B ) $= fdmcoeq_0 cdm fdmcoeq_1 crn wceq fdmcoeq_1 crn fdmcoeq_0 cdm wss fdmcoeq_0 fdmcoeq_1 ccom cdm fdmcoeq_1 cdm wceq fdmcoeq_1 crn fdmcoeq_0 cdm eqimss2 fdmcoeq_0 fdmcoeq_1 dmcosseq syl $.
$}
$( Range of a composition.  (Contributed by NM, 19-Mar-1998.) $)
${
	frncoeq_0 $f class A $.
	frncoeq_1 $f class B $.
	rncoeq $p |- ( dom A = ran B -> ran ( A o. B ) = ran A ) $= frncoeq_1 ccnv cdm frncoeq_0 ccnv crn wceq frncoeq_1 ccnv frncoeq_0 ccnv ccom cdm frncoeq_0 ccnv cdm wceq frncoeq_0 cdm frncoeq_1 crn wceq frncoeq_0 frncoeq_1 ccom crn frncoeq_0 crn wceq frncoeq_1 ccnv frncoeq_0 ccnv dmcoeq frncoeq_0 cdm frncoeq_1 crn wceq frncoeq_1 crn frncoeq_0 cdm wceq frncoeq_1 ccnv cdm frncoeq_0 ccnv crn wceq frncoeq_0 cdm frncoeq_1 crn eqcom frncoeq_1 crn frncoeq_1 ccnv cdm frncoeq_0 cdm frncoeq_0 ccnv crn frncoeq_1 df-rn frncoeq_0 dfdm4 eqeq12i bitri frncoeq_0 frncoeq_1 ccom crn frncoeq_1 ccnv frncoeq_0 ccnv ccom cdm frncoeq_0 crn frncoeq_0 ccnv cdm frncoeq_0 frncoeq_1 ccom crn frncoeq_0 frncoeq_1 ccom ccnv cdm frncoeq_1 ccnv frncoeq_0 ccnv ccom cdm frncoeq_0 frncoeq_1 ccom df-rn frncoeq_0 frncoeq_1 ccom ccnv frncoeq_1 ccnv frncoeq_0 ccnv ccom frncoeq_0 frncoeq_1 cnvco dmeqi eqtri frncoeq_0 df-rn eqeq12i 3imtr4i $.
$}
$( Equality theorem for restrictions.  (Contributed by NM, 7-Aug-1994.) $)
${
	freseq1_0 $f class A $.
	freseq1_1 $f class B $.
	freseq1_2 $f class C $.
	reseq1 $p |- ( A = B -> ( A |` C ) = ( B |` C ) ) $= freseq1_0 freseq1_1 wceq freseq1_0 freseq1_2 cvv cxp cin freseq1_1 freseq1_2 cvv cxp cin freseq1_0 freseq1_2 cres freseq1_1 freseq1_2 cres freseq1_0 freseq1_1 freseq1_2 cvv cxp ineq1 freseq1_0 freseq1_2 df-res freseq1_1 freseq1_2 df-res 3eqtr4g $.
$}
$( Equality theorem for restrictions.  (Contributed by NM, 8-Aug-1994.) $)
${
	freseq2_0 $f class A $.
	freseq2_1 $f class B $.
	freseq2_2 $f class C $.
	reseq2 $p |- ( A = B -> ( C |` A ) = ( C |` B ) ) $= freseq2_0 freseq2_1 wceq freseq2_2 freseq2_0 cvv cxp cin freseq2_2 freseq2_1 cvv cxp cin freseq2_2 freseq2_0 cres freseq2_2 freseq2_1 cres freseq2_0 freseq2_1 wceq freseq2_0 cvv cxp freseq2_1 cvv cxp freseq2_2 freseq2_0 freseq2_1 cvv xpeq1 ineq2d freseq2_2 freseq2_0 df-res freseq2_2 freseq2_1 df-res 3eqtr4g $.
$}
$( Equality inference for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
${
	freseq1i_0 $f class A $.
	freseq1i_1 $f class B $.
	freseq1i_2 $f class C $.
	ereseq1i_0 $e |- A = B $.
	reseq1i $p |- ( A |` C ) = ( B |` C ) $= freseq1i_0 freseq1i_1 wceq freseq1i_0 freseq1i_2 cres freseq1i_1 freseq1i_2 cres wceq ereseq1i_0 freseq1i_0 freseq1i_1 freseq1i_2 reseq1 ax-mp $.
$}
$( Equality inference for restrictions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
${
	freseq2i_0 $f class A $.
	freseq2i_1 $f class B $.
	freseq2i_2 $f class C $.
	ereseq2i_0 $e |- A = B $.
	reseq2i $p |- ( C |` A ) = ( C |` B ) $= freseq2i_0 freseq2i_1 wceq freseq2i_2 freseq2i_0 cres freseq2i_2 freseq2i_1 cres wceq ereseq2i_0 freseq2i_0 freseq2i_1 freseq2i_2 reseq2 ax-mp $.
$}
$( Equality inference for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
${
	freseq12i_0 $f class A $.
	freseq12i_1 $f class B $.
	freseq12i_2 $f class C $.
	freseq12i_3 $f class D $.
	ereseq12i_0 $e |- A = B $.
	ereseq12i_1 $e |- C = D $.
	reseq12i $p |- ( A |` C ) = ( B |` D ) $= freseq12i_0 freseq12i_2 cres freseq12i_1 freseq12i_2 cres freseq12i_1 freseq12i_3 cres freseq12i_0 freseq12i_1 freseq12i_2 ereseq12i_0 reseq1i freseq12i_2 freseq12i_3 freseq12i_1 ereseq12i_1 reseq2i eqtri $.
$}
$( Equality deduction for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
${
	freseq1d_0 $f wff ph $.
	freseq1d_1 $f class A $.
	freseq1d_2 $f class B $.
	freseq1d_3 $f class C $.
	ereseq1d_0 $e |- ( ph -> A = B ) $.
	reseq1d $p |- ( ph -> ( A |` C ) = ( B |` C ) ) $= freseq1d_0 freseq1d_1 freseq1d_2 wceq freseq1d_1 freseq1d_3 cres freseq1d_2 freseq1d_3 cres wceq ereseq1d_0 freseq1d_1 freseq1d_2 freseq1d_3 reseq1 syl $.
$}
$( Equality deduction for restrictions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
${
	freseq2d_0 $f wff ph $.
	freseq2d_1 $f class A $.
	freseq2d_2 $f class B $.
	freseq2d_3 $f class C $.
	ereseq2d_0 $e |- ( ph -> A = B ) $.
	reseq2d $p |- ( ph -> ( C |` A ) = ( C |` B ) ) $= freseq2d_0 freseq2d_1 freseq2d_2 wceq freseq2d_3 freseq2d_1 cres freseq2d_3 freseq2d_2 cres wceq ereseq2d_0 freseq2d_1 freseq2d_2 freseq2d_3 reseq2 syl $.
$}
$( Equality deduction for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
${
	freseq12d_0 $f wff ph $.
	freseq12d_1 $f class A $.
	freseq12d_2 $f class B $.
	freseq12d_3 $f class C $.
	freseq12d_4 $f class D $.
	ereseq12d_0 $e |- ( ph -> A = B ) $.
	ereseq12d_1 $e |- ( ph -> C = D ) $.
	reseq12d $p |- ( ph -> ( A |` C ) = ( B |` D ) ) $= freseq12d_0 freseq12d_1 freseq12d_3 cres freseq12d_2 freseq12d_3 cres freseq12d_2 freseq12d_4 cres freseq12d_0 freseq12d_1 freseq12d_2 freseq12d_3 ereseq12d_0 reseq1d freseq12d_0 freseq12d_3 freseq12d_4 freseq12d_2 ereseq12d_1 reseq2d eqtrd $.
$}
$( Bound-variable hypothesis builder for restriction.  (Contributed by NM,
       15-Sep-2003.)  (Revised by David Abernethy, 19-Jun-2012.) $)
${
	fnfres_0 $f set x $.
	fnfres_1 $f class A $.
	fnfres_2 $f class B $.
	enfres_0 $e |- F/_ x A $.
	enfres_1 $e |- F/_ x B $.
	nfres $p |- F/_ x ( A |` B ) $= fnfres_0 fnfres_1 fnfres_2 cres fnfres_1 fnfres_2 cvv cxp cin fnfres_1 fnfres_2 df-res fnfres_0 fnfres_1 fnfres_2 cvv cxp enfres_0 fnfres_0 fnfres_2 cvv enfres_1 fnfres_0 cvv nfcv nfxp nfin nfcxfr $.
$}
$( Distribute proper substitution through the restriction of a class.
     ~ csbresg is derived from the virtual deduction proof ~ csbresgVD .
     (Contributed by Alan Sare, 10-Nov-2012.) $)
${
	fcsbresg_0 $f set x $.
	fcsbresg_1 $f class A $.
	fcsbresg_2 $f class B $.
	fcsbresg_3 $f class C $.
	fcsbresg_4 $f class V $.
	csbresg $p |- ( A e. V -> [_ A / x ]_ ( B |` C ) = ( [_ A / x ]_ B |` [_ A / x ]_ C ) ) $= fcsbresg_1 fcsbresg_4 wcel fcsbresg_0 fcsbresg_1 fcsbresg_2 fcsbresg_3 cvv cxp cin csb fcsbresg_0 fcsbresg_1 fcsbresg_2 csb fcsbresg_0 fcsbresg_1 fcsbresg_3 csb cvv cxp cin fcsbresg_0 fcsbresg_1 fcsbresg_2 fcsbresg_3 cres csb fcsbresg_0 fcsbresg_1 fcsbresg_2 csb fcsbresg_0 fcsbresg_1 fcsbresg_3 csb cres fcsbresg_1 fcsbresg_4 wcel fcsbresg_0 fcsbresg_1 fcsbresg_2 fcsbresg_3 cvv cxp cin csb fcsbresg_0 fcsbresg_1 fcsbresg_2 csb fcsbresg_0 fcsbresg_1 fcsbresg_3 cvv cxp csb cin fcsbresg_0 fcsbresg_1 fcsbresg_2 csb fcsbresg_0 fcsbresg_1 fcsbresg_3 csb cvv cxp cin fcsbresg_0 fcsbresg_1 fcsbresg_4 fcsbresg_2 fcsbresg_3 cvv cxp csbing fcsbresg_1 fcsbresg_4 wcel fcsbresg_0 fcsbresg_1 fcsbresg_3 cvv cxp csb fcsbresg_0 fcsbresg_1 fcsbresg_3 csb cvv cxp fcsbresg_0 fcsbresg_1 fcsbresg_2 csb fcsbresg_1 fcsbresg_4 wcel fcsbresg_0 fcsbresg_1 fcsbresg_3 cvv cxp csb fcsbresg_0 fcsbresg_1 fcsbresg_3 csb fcsbresg_0 fcsbresg_1 cvv csb cxp fcsbresg_0 fcsbresg_1 fcsbresg_3 csb cvv cxp fcsbresg_0 fcsbresg_1 fcsbresg_3 cvv fcsbresg_4 csbxpg fcsbresg_1 fcsbresg_4 wcel fcsbresg_0 fcsbresg_1 cvv csb cvv fcsbresg_0 fcsbresg_1 fcsbresg_3 csb fcsbresg_0 fcsbresg_1 cvv fcsbresg_4 csbconstg xpeq2d eqtrd ineq2d eqtrd fcsbresg_0 fcsbresg_1 fcsbresg_2 fcsbresg_3 cres fcsbresg_2 fcsbresg_3 cvv cxp cin fcsbresg_2 fcsbresg_3 df-res csbeq2i fcsbresg_0 fcsbresg_1 fcsbresg_2 csb fcsbresg_0 fcsbresg_1 fcsbresg_3 csb df-res 3eqtr4g $.
$}
$( A restriction to the empty set is empty.  (Contributed by NM,
     12-Nov-1994.) $)
${
	fres0_0 $f class A $.
	res0 $p |- ( A |` (/) ) = (/) $= fres0_0 c0 cres fres0_0 c0 cvv cxp cin fres0_0 c0 cin c0 fres0_0 c0 df-res c0 cvv cxp c0 fres0_0 cvv xp0r ineq2i fres0_0 in0 3eqtri $.
$}
$( Ordered pair membership in a restriction.  Exercise 13 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 13-Nov-1995.) $)
${
	fopelres_0 $f class A $.
	fopelres_1 $f class B $.
	fopelres_2 $f class C $.
	fopelres_3 $f class D $.
	eopelres_0 $e |- B e. _V $.
	opelres $p |- ( <. A , B >. e. ( C |` D ) <-> ( <. A , B >. e. C /\ A e. D ) ) $= fopelres_0 fopelres_1 cop fopelres_2 fopelres_3 cres wcel fopelres_0 fopelres_1 cop fopelres_2 fopelres_3 cvv cxp cin wcel fopelres_0 fopelres_1 cop fopelres_2 wcel fopelres_0 fopelres_1 cop fopelres_3 cvv cxp wcel wa fopelres_0 fopelres_1 cop fopelres_2 wcel fopelres_0 fopelres_3 wcel wa fopelres_2 fopelres_3 cres fopelres_2 fopelres_3 cvv cxp cin fopelres_0 fopelres_1 cop fopelres_2 fopelres_3 df-res eleq2i fopelres_0 fopelres_1 cop fopelres_2 fopelres_3 cvv cxp elin fopelres_0 fopelres_1 cop fopelres_3 cvv cxp wcel fopelres_0 fopelres_3 wcel fopelres_0 fopelres_1 cop fopelres_2 wcel fopelres_0 fopelres_1 cop fopelres_3 cvv cxp wcel fopelres_0 fopelres_3 wcel fopelres_1 cvv wcel eopelres_0 fopelres_0 fopelres_1 fopelres_3 cvv opelxp mpbiran2 anbi2i 3bitri $.
$}
$( Binary relation on a restriction.  (Contributed by NM, 12-Dec-2006.) $)
${
	fbrres_0 $f class A $.
	fbrres_1 $f class B $.
	fbrres_2 $f class C $.
	fbrres_3 $f class D $.
	ebrres_0 $e |- B e. _V $.
	brres $p |- ( A ( C |` D ) B <-> ( A C B /\ A e. D ) ) $= fbrres_0 fbrres_1 cop fbrres_2 fbrres_3 cres wcel fbrres_0 fbrres_1 cop fbrres_2 wcel fbrres_0 fbrres_3 wcel wa fbrres_0 fbrres_1 fbrres_2 fbrres_3 cres wbr fbrres_0 fbrres_1 fbrres_2 wbr fbrres_0 fbrres_3 wcel wa fbrres_0 fbrres_1 fbrres_2 fbrres_3 ebrres_0 opelres fbrres_0 fbrres_1 fbrres_2 fbrres_3 cres df-br fbrres_0 fbrres_1 fbrres_2 wbr fbrres_0 fbrres_1 cop fbrres_2 wcel fbrres_0 fbrres_3 wcel fbrres_0 fbrres_1 fbrres_2 df-br anbi1i 3bitr4i $.
$}
$( Ordered pair membership in a restriction.  Exercise 13 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 14-Oct-2005.) $)
${
	$d y A $.
	$d y B $.
	$d y C $.
	$d y D $.
	iopelresg_0 $f set y $.
	fopelresg_0 $f class A $.
	fopelresg_1 $f class B $.
	fopelresg_2 $f class C $.
	fopelresg_3 $f class D $.
	fopelresg_4 $f class V $.
	opelresg $p |- ( B e. V -> ( <. A , B >. e. ( C |` D ) <-> ( <. A , B >. e. C /\ A e. D ) ) ) $= fopelresg_0 iopelresg_0 sup_set_class cop fopelresg_2 fopelresg_3 cres wcel fopelresg_0 iopelresg_0 sup_set_class cop fopelresg_2 wcel fopelresg_0 fopelresg_3 wcel wa fopelresg_0 fopelresg_1 cop fopelresg_2 fopelresg_3 cres wcel fopelresg_0 fopelresg_1 cop fopelresg_2 wcel fopelresg_0 fopelresg_3 wcel wa iopelresg_0 fopelresg_1 fopelresg_4 iopelresg_0 sup_set_class fopelresg_1 wceq fopelresg_0 iopelresg_0 sup_set_class cop fopelresg_0 fopelresg_1 cop fopelresg_2 fopelresg_3 cres iopelresg_0 sup_set_class fopelresg_1 fopelresg_0 opeq2 eleq1d iopelresg_0 sup_set_class fopelresg_1 wceq fopelresg_0 iopelresg_0 sup_set_class cop fopelresg_2 wcel fopelresg_0 fopelresg_1 cop fopelresg_2 wcel fopelresg_0 fopelresg_3 wcel iopelresg_0 sup_set_class fopelresg_1 wceq fopelresg_0 iopelresg_0 sup_set_class cop fopelresg_0 fopelresg_1 cop fopelresg_2 iopelresg_0 sup_set_class fopelresg_1 fopelresg_0 opeq2 eleq1d anbi1d fopelresg_0 iopelresg_0 sup_set_class fopelresg_2 fopelresg_3 iopelresg_0 vex opelres vtoclbg $.
$}
$( Binary relation on a restriction.  (Contributed by Mario Carneiro,
       4-Nov-2015.) $)
${
	fbrresg_0 $f class A $.
	fbrresg_1 $f class B $.
	fbrresg_2 $f class C $.
	fbrresg_3 $f class D $.
	fbrresg_4 $f class V $.
	brresg $p |- ( B e. V -> ( A ( C |` D ) B <-> ( A C B /\ A e. D ) ) ) $= fbrresg_1 fbrresg_4 wcel fbrresg_0 fbrresg_1 cop fbrresg_2 fbrresg_3 cres wcel fbrresg_0 fbrresg_1 cop fbrresg_2 wcel fbrresg_0 fbrresg_3 wcel wa fbrresg_0 fbrresg_1 fbrresg_2 fbrresg_3 cres wbr fbrresg_0 fbrresg_1 fbrresg_2 wbr fbrresg_0 fbrresg_3 wcel wa fbrresg_0 fbrresg_1 fbrresg_2 fbrresg_3 fbrresg_4 opelresg fbrresg_0 fbrresg_1 fbrresg_2 fbrresg_3 cres df-br fbrresg_0 fbrresg_1 fbrresg_2 wbr fbrresg_0 fbrresg_1 cop fbrresg_2 wcel fbrresg_0 fbrresg_3 wcel fbrresg_0 fbrresg_1 fbrresg_2 df-br anbi1i 3bitr4g $.
$}
$( Ordered pair membership in a restriction when the first member belongs
       to the restricting class.  (Contributed by NM, 30-Apr-2004.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fopres_0 $f class A $.
	fopres_1 $f class B $.
	fopres_2 $f class C $.
	fopres_3 $f class D $.
	eopres_0 $e |- B e. _V $.
	opres $p |- ( A e. D -> ( <. A , B >. e. ( C |` D ) <-> <. A , B >. e. C ) ) $= fopres_0 fopres_1 cop fopres_2 fopres_3 cres wcel fopres_0 fopres_1 cop fopres_2 wcel fopres_0 fopres_3 wcel fopres_0 fopres_1 fopres_2 fopres_3 eopres_0 opelres rbaib $.
$}
$( A restricted identity relation is equivalent to equality in its domain.
       (Contributed by NM, 30-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	iresieq_0 $f set x $.
	fresieq_0 $f class A $.
	fresieq_1 $f class B $.
	fresieq_2 $f class C $.
	resieq $p |- ( ( B e. A /\ C e. A ) -> ( B ( _I |` A ) C <-> B = C ) ) $= fresieq_2 fresieq_0 wcel fresieq_1 fresieq_0 wcel fresieq_1 fresieq_2 cid fresieq_0 cres wbr fresieq_1 fresieq_2 wceq wb fresieq_1 fresieq_0 wcel fresieq_1 iresieq_0 sup_set_class cid fresieq_0 cres wbr fresieq_1 iresieq_0 sup_set_class wceq wb wi fresieq_1 fresieq_0 wcel fresieq_1 fresieq_2 cid fresieq_0 cres wbr fresieq_1 fresieq_2 wceq wb wi iresieq_0 fresieq_2 fresieq_0 iresieq_0 sup_set_class fresieq_2 wceq fresieq_1 iresieq_0 sup_set_class cid fresieq_0 cres wbr fresieq_1 iresieq_0 sup_set_class wceq wb fresieq_1 fresieq_2 cid fresieq_0 cres wbr fresieq_1 fresieq_2 wceq wb fresieq_1 fresieq_0 wcel iresieq_0 sup_set_class fresieq_2 wceq fresieq_1 iresieq_0 sup_set_class cid fresieq_0 cres wbr fresieq_1 fresieq_2 cid fresieq_0 cres wbr fresieq_1 iresieq_0 sup_set_class wceq fresieq_1 fresieq_2 wceq iresieq_0 sup_set_class fresieq_2 fresieq_1 cid fresieq_0 cres breq2 iresieq_0 sup_set_class fresieq_2 fresieq_1 eqeq2 bibi12d imbi2d fresieq_1 fresieq_0 wcel fresieq_1 iresieq_0 sup_set_class cop cid fresieq_0 cres wcel fresieq_1 iresieq_0 sup_set_class cop cid wcel fresieq_1 iresieq_0 sup_set_class cid fresieq_0 cres wbr fresieq_1 iresieq_0 sup_set_class wceq fresieq_1 iresieq_0 sup_set_class cid fresieq_0 iresieq_0 vex opres fresieq_1 iresieq_0 sup_set_class cid fresieq_0 cres df-br fresieq_1 iresieq_0 sup_set_class wceq fresieq_1 iresieq_0 sup_set_class cid wbr fresieq_1 iresieq_0 sup_set_class cop cid wcel fresieq_1 iresieq_0 sup_set_class iresieq_0 vex ideq fresieq_1 iresieq_0 sup_set_class cid df-br bitr3i 3bitr4g vtoclg impcom $.
$}
$( ` <. A , A >. ` belongs to a restriction of the identity class iff ` A `
     belongs to the restricting class.  (Contributed by FL, 27-Oct-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fopelresiOLD_0 $f class A $.
	fopelresiOLD_1 $f class B $.
	fopelresiOLD_2 $f class V $.
	opelresiOLD $p |- ( A e. V -> ( A e. B <-> <. A , A >. e. ( _I |` B ) ) ) $= fopelresiOLD_0 fopelresiOLD_2 wcel fopelresiOLD_0 fopelresiOLD_1 wcel fopelresiOLD_0 fopelresiOLD_0 cop cid wcel fopelresiOLD_0 fopelresiOLD_1 wcel wa fopelresiOLD_0 fopelresiOLD_0 cop cid fopelresiOLD_1 cres wcel fopelresiOLD_0 fopelresiOLD_2 wcel fopelresiOLD_0 fopelresiOLD_0 cop cid wcel fopelresiOLD_0 fopelresiOLD_1 wcel fopelresiOLD_0 fopelresiOLD_2 wcel fopelresiOLD_0 fopelresiOLD_0 cid wbr fopelresiOLD_0 fopelresiOLD_0 cop cid wcel fopelresiOLD_0 fopelresiOLD_2 ididg fopelresiOLD_0 fopelresiOLD_0 cid df-br sylib biantrurd fopelresiOLD_0 fopelresiOLD_0 cid fopelresiOLD_1 fopelresiOLD_2 opelresg bitr4d $.
$}
$( ` <. A , A >. ` belongs to a restriction of the identity class iff ` A `
     belongs to the restricting class.  (Contributed by FL, 27-Oct-2008.)
     (Revised by NM, 30-Mar-2016.) $)
${
	fopelresi_0 $f class A $.
	fopelresi_1 $f class B $.
	fopelresi_2 $f class V $.
	opelresi $p |- ( A e. V -> ( <. A , A >. e. ( _I |` B ) <-> A e. B ) ) $= fopelresi_0 fopelresi_2 wcel fopelresi_0 fopelresi_0 cop cid fopelresi_1 cres wcel fopelresi_0 fopelresi_0 cop cid wcel fopelresi_0 fopelresi_1 wcel wa fopelresi_0 fopelresi_1 wcel fopelresi_0 fopelresi_0 cid fopelresi_1 fopelresi_2 opelresg fopelresi_0 fopelresi_2 wcel fopelresi_0 fopelresi_0 cop cid wcel fopelresi_0 fopelresi_1 wcel fopelresi_0 fopelresi_2 wcel fopelresi_0 fopelresi_0 cid wbr fopelresi_0 fopelresi_0 cop cid wcel fopelresi_0 fopelresi_2 ididg fopelresi_0 fopelresi_0 cid df-br sylib biantrurd bitr4d $.
$}
$( The restriction of a restriction.  (Contributed by NM, 27-Mar-2008.) $)
${
	fresres_0 $f class A $.
	fresres_1 $f class B $.
	fresres_2 $f class C $.
	resres $p |- ( ( A |` B ) |` C ) = ( A |` ( B i^i C ) ) $= fresres_0 fresres_1 cres fresres_2 cres fresres_0 fresres_1 cres fresres_2 cvv cxp cin fresres_0 fresres_1 cvv cxp cin fresres_2 cvv cxp cin fresres_0 fresres_1 fresres_2 cin cres fresres_0 fresres_1 cres fresres_2 df-res fresres_0 fresres_1 cres fresres_0 fresres_1 cvv cxp cin fresres_2 cvv cxp fresres_0 fresres_1 df-res ineq1i fresres_0 fresres_1 fresres_2 cin cvv cxp cin fresres_0 fresres_1 cvv cxp fresres_2 cvv cxp cin cin fresres_0 fresres_1 fresres_2 cin cres fresres_0 fresres_1 cvv cxp cin fresres_2 cvv cxp cin fresres_1 fresres_2 cin cvv cxp fresres_1 cvv cxp fresres_2 cvv cxp cin fresres_0 fresres_1 fresres_2 cvv xpindir ineq2i fresres_0 fresres_1 fresres_2 cin df-res fresres_0 fresres_1 cvv cxp fresres_2 cvv cxp inass 3eqtr4ri 3eqtri $.
$}
$( Distributive law for restriction over union.  Theorem 31 of [Suppes]
     p. 65.  (Contributed by NM, 30-Sep-2002.) $)
${
	fresundi_0 $f class A $.
	fresundi_1 $f class B $.
	fresundi_2 $f class C $.
	resundi $p |- ( A |` ( B u. C ) ) = ( ( A |` B ) u. ( A |` C ) ) $= fresundi_0 fresundi_1 fresundi_2 cun cvv cxp cin fresundi_0 fresundi_1 cvv cxp cin fresundi_0 fresundi_2 cvv cxp cin cun fresundi_0 fresundi_1 fresundi_2 cun cres fresundi_0 fresundi_1 cres fresundi_0 fresundi_2 cres cun fresundi_0 fresundi_1 fresundi_2 cun cvv cxp cin fresundi_0 fresundi_1 cvv cxp fresundi_2 cvv cxp cun cin fresundi_0 fresundi_1 cvv cxp cin fresundi_0 fresundi_2 cvv cxp cin cun fresundi_1 fresundi_2 cun cvv cxp fresundi_1 cvv cxp fresundi_2 cvv cxp cun fresundi_0 fresundi_1 fresundi_2 cvv xpundir ineq2i fresundi_0 fresundi_1 cvv cxp fresundi_2 cvv cxp indi eqtri fresundi_0 fresundi_1 fresundi_2 cun df-res fresundi_0 fresundi_1 cres fresundi_0 fresundi_1 cvv cxp cin fresundi_0 fresundi_2 cres fresundi_0 fresundi_2 cvv cxp cin fresundi_0 fresundi_1 df-res fresundi_0 fresundi_2 df-res uneq12i 3eqtr4i $.
$}
$( Distributive law for restriction over union.  (Contributed by NM,
     23-Sep-2004.) $)
${
	fresundir_0 $f class A $.
	fresundir_1 $f class B $.
	fresundir_2 $f class C $.
	resundir $p |- ( ( A u. B ) |` C ) = ( ( A |` C ) u. ( B |` C ) ) $= fresundir_0 fresundir_1 cun fresundir_2 cvv cxp cin fresundir_0 fresundir_2 cvv cxp cin fresundir_1 fresundir_2 cvv cxp cin cun fresundir_0 fresundir_1 cun fresundir_2 cres fresundir_0 fresundir_2 cres fresundir_1 fresundir_2 cres cun fresundir_0 fresundir_1 fresundir_2 cvv cxp indir fresundir_0 fresundir_1 cun fresundir_2 df-res fresundir_0 fresundir_2 cres fresundir_0 fresundir_2 cvv cxp cin fresundir_1 fresundir_2 cres fresundir_1 fresundir_2 cvv cxp cin fresundir_0 fresundir_2 df-res fresundir_1 fresundir_2 df-res uneq12i 3eqtr4i $.
$}
$( Class restriction distributes over intersection.  (Contributed by FL,
     6-Oct-2008.) $)
${
	fresindi_0 $f class A $.
	fresindi_1 $f class B $.
	fresindi_2 $f class C $.
	resindi $p |- ( A |` ( B i^i C ) ) = ( ( A |` B ) i^i ( A |` C ) ) $= fresindi_0 fresindi_1 fresindi_2 cin cvv cxp cin fresindi_0 fresindi_1 cvv cxp cin fresindi_0 fresindi_2 cvv cxp cin cin fresindi_0 fresindi_1 fresindi_2 cin cres fresindi_0 fresindi_1 cres fresindi_0 fresindi_2 cres cin fresindi_0 fresindi_1 fresindi_2 cin cvv cxp cin fresindi_0 fresindi_1 cvv cxp fresindi_2 cvv cxp cin cin fresindi_0 fresindi_1 cvv cxp cin fresindi_0 fresindi_2 cvv cxp cin cin fresindi_1 fresindi_2 cin cvv cxp fresindi_1 cvv cxp fresindi_2 cvv cxp cin fresindi_0 fresindi_1 fresindi_2 cvv xpindir ineq2i fresindi_0 fresindi_1 cvv cxp fresindi_2 cvv cxp inindi eqtri fresindi_0 fresindi_1 fresindi_2 cin df-res fresindi_0 fresindi_1 cres fresindi_0 fresindi_1 cvv cxp cin fresindi_0 fresindi_2 cres fresindi_0 fresindi_2 cvv cxp cin fresindi_0 fresindi_1 df-res fresindi_0 fresindi_2 df-res ineq12i 3eqtr4i $.
$}
$( Class restriction distributes over intersection.  (Contributed by NM,
     18-Dec-2008.) $)
${
	fresindir_0 $f class A $.
	fresindir_1 $f class B $.
	fresindir_2 $f class C $.
	resindir $p |- ( ( A i^i B ) |` C ) = ( ( A |` C ) i^i ( B |` C ) ) $= fresindir_0 fresindir_1 cin fresindir_2 cvv cxp cin fresindir_0 fresindir_2 cvv cxp cin fresindir_1 fresindir_2 cvv cxp cin cin fresindir_0 fresindir_1 cin fresindir_2 cres fresindir_0 fresindir_2 cres fresindir_1 fresindir_2 cres cin fresindir_0 fresindir_1 fresindir_2 cvv cxp inindir fresindir_0 fresindir_1 cin fresindir_2 df-res fresindir_0 fresindir_2 cres fresindir_0 fresindir_2 cvv cxp cin fresindir_1 fresindir_2 cres fresindir_1 fresindir_2 cvv cxp cin fresindir_0 fresindir_2 df-res fresindir_1 fresindir_2 df-res ineq12i 3eqtr4i $.
$}
$( Move intersection into class restriction.  (Contributed by NM,
     18-Dec-2008.) $)
${
	finres_0 $f class A $.
	finres_1 $f class B $.
	finres_2 $f class C $.
	inres $p |- ( A i^i ( B |` C ) ) = ( ( A i^i B ) |` C ) $= finres_0 finres_1 cin finres_2 cvv cxp cin finres_0 finres_1 finres_2 cvv cxp cin cin finres_0 finres_1 cin finres_2 cres finres_0 finres_1 finres_2 cres cin finres_0 finres_1 finres_2 cvv cxp inass finres_0 finres_1 cin finres_2 df-res finres_1 finres_2 cres finres_1 finres_2 cvv cxp cin finres_0 finres_1 finres_2 df-res ineq2i 3eqtr4ri $.
$}
$( Distribution of restriction over indexed union.  (Contributed by Mario
       Carneiro, 29-May-2015.) $)
${
	$d x C $.
	fresiun1_0 $f set x $.
	fresiun1_1 $f class A $.
	fresiun1_2 $f class B $.
	fresiun1_3 $f class C $.
	resiun1 $p |- ( U_ x e. A B |` C ) = U_ x e. A ( B |` C ) $= fresiun1_0 fresiun1_1 fresiun1_3 cvv cxp fresiun1_2 cin ciun fresiun1_3 cvv cxp fresiun1_0 fresiun1_1 fresiun1_2 ciun cin fresiun1_0 fresiun1_1 fresiun1_2 fresiun1_3 cres ciun fresiun1_0 fresiun1_1 fresiun1_2 ciun fresiun1_3 cres fresiun1_0 fresiun1_1 fresiun1_3 cvv cxp fresiun1_2 iunin2 fresiun1_0 fresiun1_1 fresiun1_2 fresiun1_3 cres fresiun1_3 cvv cxp fresiun1_2 cin fresiun1_2 fresiun1_3 cres fresiun1_3 cvv cxp fresiun1_2 cin wceq fresiun1_0 sup_set_class fresiun1_1 wcel fresiun1_2 fresiun1_3 cres fresiun1_2 fresiun1_3 cvv cxp cin fresiun1_3 cvv cxp fresiun1_2 cin fresiun1_2 fresiun1_3 df-res fresiun1_2 fresiun1_3 cvv cxp incom eqtri a1i iuneq2i fresiun1_0 fresiun1_1 fresiun1_2 ciun fresiun1_3 cres fresiun1_0 fresiun1_1 fresiun1_2 ciun fresiun1_3 cvv cxp cin fresiun1_3 cvv cxp fresiun1_0 fresiun1_1 fresiun1_2 ciun cin fresiun1_0 fresiun1_1 fresiun1_2 ciun fresiun1_3 df-res fresiun1_0 fresiun1_1 fresiun1_2 ciun fresiun1_3 cvv cxp incom eqtri 3eqtr4ri $.
$}
$( Distribution of restriction over indexed union.  (Contributed by Mario
       Carneiro, 29-May-2015.) $)
${
	$d x C $.
	fresiun2_0 $f set x $.
	fresiun2_1 $f class A $.
	fresiun2_2 $f class B $.
	fresiun2_3 $f class C $.
	resiun2 $p |- ( C |` U_ x e. A B ) = U_ x e. A ( C |` B ) $= fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 ciun cres fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 ciun cvv cxp cin fresiun2_0 fresiun2_1 fresiun2_3 fresiun2_2 cres ciun fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 ciun df-res fresiun2_0 fresiun2_1 fresiun2_3 fresiun2_2 cres ciun fresiun2_0 fresiun2_1 fresiun2_3 fresiun2_2 cvv cxp cin ciun fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 ciun cvv cxp cin fresiun2_0 fresiun2_1 fresiun2_3 fresiun2_2 cres fresiun2_3 fresiun2_2 cvv cxp cin fresiun2_3 fresiun2_2 cres fresiun2_3 fresiun2_2 cvv cxp cin wceq fresiun2_0 sup_set_class fresiun2_1 wcel fresiun2_3 fresiun2_2 df-res a1i iuneq2i fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 ciun cvv cxp cin fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 cvv cxp ciun cin fresiun2_0 fresiun2_1 fresiun2_3 fresiun2_2 cvv cxp cin ciun fresiun2_0 fresiun2_1 fresiun2_2 ciun cvv cxp fresiun2_0 fresiun2_1 fresiun2_2 cvv cxp ciun fresiun2_3 fresiun2_0 fresiun2_1 fresiun2_2 cvv xpiundir ineq2i fresiun2_0 fresiun2_1 fresiun2_3 fresiun2_2 cvv cxp iunin2 eqtr4i eqtr4i eqtr4i $.
$}
$( The domain of a restriction.  Exercise 14 of [TakeutiZaring] p. 25.
       (Contributed by NM, 1-Aug-1994.) $)
${
	$d x y A $.
	$d x y B $.
	idmres_0 $f set x $.
	idmres_1 $f set y $.
	fdmres_0 $f class A $.
	fdmres_1 $f class B $.
	dmres $p |- dom ( A |` B ) = ( B i^i dom A ) $= fdmres_0 cdm fdmres_1 cin fdmres_0 fdmres_1 cres cdm fdmres_1 fdmres_0 cdm cin idmres_0 fdmres_0 cdm fdmres_1 fdmres_0 fdmres_1 cres cdm idmres_0 sup_set_class fdmres_0 fdmres_1 cres cdm wcel idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 fdmres_1 cres wcel idmres_1 wex idmres_0 sup_set_class fdmres_0 cdm wcel idmres_0 sup_set_class fdmres_1 wcel wa idmres_1 idmres_0 sup_set_class fdmres_0 fdmres_1 cres idmres_0 vex eldm2 idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 wcel idmres_0 sup_set_class fdmres_1 wcel wa idmres_1 wex idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 wcel idmres_1 wex idmres_0 sup_set_class fdmres_1 wcel wa idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 fdmres_1 cres wcel idmres_1 wex idmres_0 sup_set_class fdmres_0 cdm wcel idmres_0 sup_set_class fdmres_1 wcel wa idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 wcel idmres_0 sup_set_class fdmres_1 wcel idmres_1 19.41v idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 fdmres_1 cres wcel idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 wcel idmres_0 sup_set_class fdmres_1 wcel wa idmres_1 idmres_0 sup_set_class idmres_1 sup_set_class fdmres_0 fdmres_1 idmres_1 vex opelres exbii idmres_0 sup_set_class fdmres_0 cdm wcel idmres_0 sup_set_class idmres_1 sup_set_class cop fdmres_0 wcel idmres_1 wex idmres_0 sup_set_class fdmres_1 wcel idmres_1 idmres_0 sup_set_class fdmres_0 idmres_0 vex eldm2 anbi1i 3bitr4i bitr2i ineqri fdmres_0 cdm fdmres_1 incom eqtr3i $.
$}
$( A domain restricted to a subclass equals the subclass.  (Contributed by
     NM, 2-Mar-1997.) $)
${
	fssdmres_0 $f class A $.
	fssdmres_1 $f class B $.
	ssdmres $p |- ( A C_ dom B <-> dom ( B |` A ) = A ) $= fssdmres_0 fssdmres_1 cdm wss fssdmres_0 fssdmres_1 cdm cin fssdmres_0 wceq fssdmres_1 fssdmres_0 cres cdm fssdmres_0 wceq fssdmres_0 fssdmres_1 cdm df-ss fssdmres_1 fssdmres_0 cres cdm fssdmres_0 fssdmres_1 cdm cin fssdmres_0 fssdmres_1 fssdmres_0 dmres eqeq1i bitr4i $.
$}
$( The domain of a restriction to a set exists.  (Contributed by NM,
     7-Apr-1995.) $)
${
	fdmresexg_0 $f class A $.
	fdmresexg_1 $f class B $.
	fdmresexg_2 $f class V $.
	dmresexg $p |- ( B e. V -> dom ( A |` B ) e. _V ) $= fdmresexg_1 fdmresexg_2 wcel fdmresexg_0 fdmresexg_1 cres cdm fdmresexg_1 fdmresexg_0 cdm cin cvv fdmresexg_0 fdmresexg_1 dmres fdmresexg_1 fdmresexg_0 cdm fdmresexg_2 inex1g syl5eqel $.
$}
$( A class includes its restriction.  Exercise 15 of [TakeutiZaring] p. 25.
     (Contributed by NM, 2-Aug-1994.) $)
${
	fresss_0 $f class A $.
	fresss_1 $f class B $.
	resss $p |- ( A |` B ) C_ A $= fresss_0 fresss_1 cres fresss_0 fresss_1 cvv cxp cin fresss_0 fresss_0 fresss_1 df-res fresss_0 fresss_1 cvv cxp inss1 eqsstri $.
$}
$( Commutative law for restriction.  (Contributed by NM, 27-Mar-1998.) $)
${
	frescom_0 $f class A $.
	frescom_1 $f class B $.
	frescom_2 $f class C $.
	rescom $p |- ( ( A |` B ) |` C ) = ( ( A |` C ) |` B ) $= frescom_0 frescom_1 frescom_2 cin cres frescom_0 frescom_2 frescom_1 cin cres frescom_0 frescom_1 cres frescom_2 cres frescom_0 frescom_2 cres frescom_1 cres frescom_1 frescom_2 cin frescom_2 frescom_1 cin frescom_0 frescom_1 frescom_2 incom reseq2i frescom_0 frescom_1 frescom_2 resres frescom_0 frescom_2 frescom_1 resres 3eqtr4i $.
$}
$( Subclass theorem for restriction.  (Contributed by NM, 16-Aug-1994.) $)
${
	fssres_0 $f class A $.
	fssres_1 $f class B $.
	fssres_2 $f class C $.
	ssres $p |- ( A C_ B -> ( A |` C ) C_ ( B |` C ) ) $= fssres_0 fssres_1 wss fssres_0 fssres_2 cvv cxp cin fssres_1 fssres_2 cvv cxp cin fssres_0 fssres_2 cres fssres_1 fssres_2 cres fssres_0 fssres_1 fssres_2 cvv cxp ssrin fssres_0 fssres_2 df-res fssres_1 fssres_2 df-res 3sstr4g $.
$}
$( Subclass theorem for restriction.  (Contributed by NM, 22-Mar-1998.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fssres2_0 $f class A $.
	fssres2_1 $f class B $.
	fssres2_2 $f class C $.
	ssres2 $p |- ( A C_ B -> ( C |` A ) C_ ( C |` B ) ) $= fssres2_0 fssres2_1 wss fssres2_2 fssres2_0 cvv cxp cin fssres2_2 fssres2_1 cvv cxp cin fssres2_2 fssres2_0 cres fssres2_2 fssres2_1 cres fssres2_0 fssres2_1 wss fssres2_0 cvv cxp fssres2_1 cvv cxp wss fssres2_2 fssres2_0 cvv cxp cin fssres2_2 fssres2_1 cvv cxp cin wss fssres2_0 fssres2_1 cvv xpss1 fssres2_0 cvv cxp fssres2_1 cvv cxp fssres2_2 sslin syl fssres2_2 fssres2_0 df-res fssres2_2 fssres2_1 df-res 3sstr4g $.
$}
$( A restriction is a relation.  Exercise 12 of [TakeutiZaring] p. 25.
     (Contributed by NM, 2-Aug-1994.)  (Proof shortened by Andrew Salmon,
     27-Aug-2011.) $)
${
	frelres_0 $f class A $.
	frelres_1 $f class B $.
	relres $p |- Rel ( A |` B ) $= frelres_0 frelres_1 cres frelres_1 cvv cxp wss frelres_1 cvv cxp wrel frelres_0 frelres_1 cres wrel frelres_0 frelres_1 cres frelres_0 frelres_1 cvv cxp cin frelres_1 cvv cxp frelres_0 frelres_1 df-res frelres_0 frelres_1 cvv cxp inss2 eqsstri frelres_1 cvv relxp frelres_0 frelres_1 cres frelres_1 cvv cxp relss mp2 $.
$}
$( Absorption law for restriction.  Exercise 17 of [TakeutiZaring] p. 25.
     (Contributed by NM, 9-Aug-1994.) $)
${
	fresabs1_0 $f class A $.
	fresabs1_1 $f class B $.
	fresabs1_2 $f class C $.
	resabs1 $p |- ( B C_ C -> ( ( A |` C ) |` B ) = ( A |` B ) ) $= fresabs1_1 fresabs1_2 wss fresabs1_0 fresabs1_2 cres fresabs1_1 cres fresabs1_0 fresabs1_2 fresabs1_1 cin cres fresabs1_0 fresabs1_1 cres fresabs1_0 fresabs1_2 fresabs1_1 resres fresabs1_1 fresabs1_2 wss fresabs1_2 fresabs1_1 cin fresabs1_1 wceq fresabs1_0 fresabs1_2 fresabs1_1 cin cres fresabs1_0 fresabs1_1 cres wceq fresabs1_1 fresabs1_2 sseqin2 fresabs1_2 fresabs1_1 cin fresabs1_1 fresabs1_0 reseq2 sylbi syl5eq $.
$}
$( Absorption law for restriction.  (Contributed by NM, 27-Mar-1998.) $)
${
	fresabs2_0 $f class A $.
	fresabs2_1 $f class B $.
	fresabs2_2 $f class C $.
	resabs2 $p |- ( B C_ C -> ( ( A |` B ) |` C ) = ( A |` B ) ) $= fresabs2_1 fresabs2_2 wss fresabs2_0 fresabs2_1 cres fresabs2_2 cres fresabs2_0 fresabs2_2 cres fresabs2_1 cres fresabs2_0 fresabs2_1 cres fresabs2_0 fresabs2_1 fresabs2_2 rescom fresabs2_0 fresabs2_1 fresabs2_2 resabs1 syl5eq $.
$}
$( Idempotent law for restriction.  (Contributed by NM, 27-Mar-1998.) $)
${
	fresidm_0 $f class A $.
	fresidm_1 $f class B $.
	residm $p |- ( ( A |` B ) |` B ) = ( A |` B ) $= fresidm_1 fresidm_1 wss fresidm_0 fresidm_1 cres fresidm_1 cres fresidm_0 fresidm_1 cres wceq fresidm_1 ssid fresidm_0 fresidm_1 fresidm_1 resabs2 ax-mp $.
$}
$( A restriction to an image.  (Contributed by NM, 29-Sep-2004.) $)
${
	fresima_0 $f class A $.
	fresima_1 $f class B $.
	resima $p |- ( ( A |` B ) " B ) = ( A " B ) $= fresima_0 fresima_1 cres fresima_1 cres crn fresima_0 fresima_1 cres crn fresima_0 fresima_1 cres fresima_1 cima fresima_0 fresima_1 cima fresima_0 fresima_1 cres fresima_1 cres fresima_0 fresima_1 cres fresima_0 fresima_1 residm rneqi fresima_0 fresima_1 cres fresima_1 df-ima fresima_0 fresima_1 df-ima 3eqtr4i $.
$}
$( Image under a restricted class.  (Contributed by FL, 31-Aug-2009.) $)
${
	fresima2_0 $f class A $.
	fresima2_1 $f class B $.
	fresima2_2 $f class C $.
	resima2 $p |- ( B C_ C -> ( ( A |` C ) " B ) = ( A " B ) ) $= fresima2_1 fresima2_2 wss fresima2_0 fresima2_2 cres fresima2_1 cima fresima2_0 fresima2_2 cres fresima2_1 cres crn fresima2_0 fresima2_1 cima fresima2_0 fresima2_2 cres fresima2_1 df-ima fresima2_1 fresima2_2 wss fresima2_0 fresima2_2 cres fresima2_1 cres crn fresima2_0 fresima2_2 fresima2_1 cin cres crn fresima2_0 fresima2_1 cima fresima2_0 fresima2_2 cres fresima2_1 cres fresima2_0 fresima2_2 fresima2_1 cin cres fresima2_0 fresima2_2 fresima2_1 resres rneqi fresima2_1 fresima2_2 wss fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_0 fresima2_2 fresima2_1 cin cres crn fresima2_0 fresima2_1 cima wceq fresima2_1 fresima2_2 df-ss fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_0 fresima2_2 fresima2_1 cin cres crn fresima2_0 fresima2_1 fresima2_2 cin cres crn fresima2_0 fresima2_1 cima fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_0 fresima2_2 fresima2_1 cin cres fresima2_0 fresima2_1 fresima2_2 cin cres fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_2 fresima2_1 cin fresima2_1 fresima2_2 cin fresima2_0 fresima2_2 fresima2_1 cin fresima2_1 fresima2_2 cin wceq fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_2 fresima2_1 incom a1i reseq2d rneqd fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_0 fresima2_1 fresima2_2 cin cres crn fresima2_0 fresima2_1 cres crn fresima2_0 fresima2_1 cima fresima2_1 fresima2_2 cin fresima2_1 wceq fresima2_0 fresima2_1 fresima2_2 cin cres fresima2_0 fresima2_1 cres fresima2_1 fresima2_2 cin fresima2_1 fresima2_0 reseq2 rneqd fresima2_0 fresima2_1 df-ima syl6eqr eqtrd sylbi syl5eq syl5eq $.
$}
$( Restriction of a constant function (or other cross product).  (Contributed
     by Stefan O'Rear, 24-Jan-2015.) $)
${
	fxpssres_0 $f class A $.
	fxpssres_1 $f class B $.
	fxpssres_2 $f class C $.
	xpssres $p |- ( C C_ A -> ( ( A X. B ) |` C ) = ( C X. B ) ) $= fxpssres_2 fxpssres_0 wss fxpssres_0 fxpssres_1 cxp fxpssres_2 cres fxpssres_2 fxpssres_0 cin fxpssres_1 cxp fxpssres_2 fxpssres_1 cxp fxpssres_0 fxpssres_1 cxp fxpssres_2 cres fxpssres_0 fxpssres_1 cxp fxpssres_2 cvv cxp cin fxpssres_0 fxpssres_2 cin fxpssres_1 cvv cin cxp fxpssres_2 fxpssres_0 cin fxpssres_1 cxp fxpssres_0 fxpssres_1 cxp fxpssres_2 df-res fxpssres_0 fxpssres_1 fxpssres_2 cvv inxp fxpssres_0 fxpssres_2 cin fxpssres_2 fxpssres_0 cin fxpssres_1 cvv cin fxpssres_1 fxpssres_0 fxpssres_2 incom fxpssres_1 inv1 xpeq12i 3eqtri fxpssres_2 fxpssres_0 wss fxpssres_2 fxpssres_0 cin fxpssres_2 fxpssres_1 fxpssres_2 fxpssres_0 wss fxpssres_2 fxpssres_0 cin fxpssres_2 wceq fxpssres_2 fxpssres_0 df-ss biimpi xpeq1d syl5eq $.
$}
$( Membership in a restriction.  (Contributed by Scott Fenton,
       17-Mar-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	felres_0 $f set x $.
	felres_1 $f set y $.
	felres_2 $f class A $.
	felres_3 $f class B $.
	felres_4 $f class C $.
	elres $p |- ( A e. ( B |` C ) <-> E. x e. C E. y ( A = <. x , y >. /\ <. x , y >. e. B ) ) $= felres_2 felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_1 wex felres_0 felres_4 wrex felres_2 felres_3 felres_4 cres wcel felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_1 wex felres_0 wex felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_1 wex felres_0 felres_4 wrex felres_2 felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_1 wex felres_0 wex felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_1 wex felres_0 wex felres_3 felres_4 cres wrel felres_2 felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_1 wex felres_0 wex felres_3 felres_4 relres felres_0 felres_1 felres_2 felres_3 felres_4 cres elrel mpan felres_2 felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_0 felres_1 felres_2 felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_2 felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_2 felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_2 felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres eleq1 biimpd felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel felres_0 sup_set_class felres_4 wcel wa felres_0 sup_set_class felres_1 sup_set_class felres_3 felres_4 felres_1 vex opelres biimpi ancomd syl6com ancld felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel an12 syl6ib 2eximdv mpd felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_1 wex felres_0 felres_4 wrex felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_0 felres_4 wrex felres_1 wex felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_0 wex felres_1 wex felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_1 wex felres_0 wex felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_0 felres_1 felres_4 rexcom4 felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_0 felres_4 wrex felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_0 wex felres_1 felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_0 felres_4 df-rex exbii felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa wa felres_1 felres_0 excom 3bitri sylibr felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_1 wex felres_2 felres_3 felres_4 cres wcel felres_0 felres_4 felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel wa felres_2 felres_3 felres_4 cres wcel felres_1 felres_0 sup_set_class felres_4 wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel felres_2 felres_3 felres_4 cres wcel felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_2 felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 wcel felres_0 sup_set_class felres_4 wcel felres_0 sup_set_class felres_1 sup_set_class felres_3 felres_4 felres_1 vex opelres simplbi2com felres_2 felres_0 sup_set_class felres_1 sup_set_class cop wceq felres_2 felres_3 felres_4 cres wcel felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres wcel felres_2 felres_0 sup_set_class felres_1 sup_set_class cop felres_3 felres_4 cres eleq1 biimprd syl9 imp3a exlimdv rexlimiv impbii $.
$}
$( Memebership in restriction to a singleton.  (Contributed by Scott
         Fenton, 17-Mar-2011.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ielsnres_0 $f set x $.
	felsnres_0 $f set y $.
	felsnres_1 $f class A $.
	felsnres_2 $f class B $.
	felsnres_3 $f class C $.
	eelsnres_0 $e |- C e. _V $.
	elsnres $p |- ( A e. ( B |` { C } ) <-> E. y ( A = <. C , y >. /\ <. C , y >. e. B ) ) $= felsnres_1 felsnres_2 felsnres_3 csn cres wcel felsnres_1 ielsnres_0 sup_set_class felsnres_0 sup_set_class cop wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_2 wcel wa felsnres_0 wex ielsnres_0 felsnres_3 csn wrex felsnres_1 ielsnres_0 sup_set_class felsnres_0 sup_set_class cop wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_2 wcel wa ielsnres_0 felsnres_3 csn wrex felsnres_0 wex felsnres_1 felsnres_3 felsnres_0 sup_set_class cop wceq felsnres_3 felsnres_0 sup_set_class cop felsnres_2 wcel wa felsnres_0 wex ielsnres_0 felsnres_0 felsnres_1 felsnres_2 felsnres_3 csn elres felsnres_1 ielsnres_0 sup_set_class felsnres_0 sup_set_class cop wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_2 wcel wa ielsnres_0 felsnres_0 felsnres_3 csn rexcom4 felsnres_1 ielsnres_0 sup_set_class felsnres_0 sup_set_class cop wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_2 wcel wa ielsnres_0 felsnres_3 csn wrex felsnres_1 felsnres_3 felsnres_0 sup_set_class cop wceq felsnres_3 felsnres_0 sup_set_class cop felsnres_2 wcel wa felsnres_0 felsnres_1 ielsnres_0 sup_set_class felsnres_0 sup_set_class cop wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_2 wcel wa felsnres_1 felsnres_3 felsnres_0 sup_set_class cop wceq felsnres_3 felsnres_0 sup_set_class cop felsnres_2 wcel wa ielsnres_0 felsnres_3 eelsnres_0 ielsnres_0 sup_set_class felsnres_3 wceq felsnres_1 ielsnres_0 sup_set_class felsnres_0 sup_set_class cop wceq felsnres_1 felsnres_3 felsnres_0 sup_set_class cop wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_2 wcel felsnres_3 felsnres_0 sup_set_class cop felsnres_2 wcel ielsnres_0 sup_set_class felsnres_3 wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_3 felsnres_0 sup_set_class cop felsnres_1 ielsnres_0 sup_set_class felsnres_3 felsnres_0 sup_set_class opeq1 eqeq2d ielsnres_0 sup_set_class felsnres_3 wceq ielsnres_0 sup_set_class felsnres_0 sup_set_class cop felsnres_3 felsnres_0 sup_set_class cop felsnres_2 ielsnres_0 sup_set_class felsnres_3 felsnres_0 sup_set_class opeq1 eleq1d anbi12d rexsn exbii 3bitri $.
$}
$( Simplification law for restriction.  (Contributed by NM,
       16-Aug-1994.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	irelssres_0 $f set x $.
	irelssres_1 $f set y $.
	frelssres_0 $f class A $.
	frelssres_1 $f class B $.
	relssres $p |- ( ( Rel A /\ dom A C_ B ) -> ( A |` B ) = A ) $= frelssres_0 wrel frelssres_0 cdm frelssres_1 wss wa frelssres_0 frelssres_1 cres frelssres_0 wss frelssres_0 frelssres_0 frelssres_1 cres wss wa frelssres_0 frelssres_1 cres frelssres_0 wceq frelssres_0 wrel frelssres_0 cdm frelssres_1 wss wa frelssres_0 frelssres_0 frelssres_1 cres wss frelssres_0 frelssres_1 cres frelssres_0 wss frelssres_0 wrel frelssres_0 cdm frelssres_1 wss wa irelssres_0 irelssres_1 frelssres_0 frelssres_0 frelssres_1 cres frelssres_0 wrel frelssres_0 cdm frelssres_1 wss simpl frelssres_0 cdm frelssres_1 wss irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 wcel irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 frelssres_1 cres wcel wi frelssres_0 wrel frelssres_0 cdm frelssres_1 wss irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 wcel irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 wcel irelssres_0 sup_set_class frelssres_1 wcel wa irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 frelssres_1 cres wcel frelssres_0 cdm frelssres_1 wss irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 wcel irelssres_0 sup_set_class frelssres_1 wcel irelssres_0 sup_set_class irelssres_1 sup_set_class cop frelssres_0 wcel irelssres_0 sup_set_class frelssres_0 cdm wcel frelssres_0 cdm frelssres_1 wss irelssres_0 sup_set_class frelssres_1 wcel irelssres_0 sup_set_class irelssres_1 sup_set_class frelssres_0 irelssres_0 vex irelssres_1 vex opeldm frelssres_0 cdm frelssres_1 irelssres_0 sup_set_class ssel syl5 ancld irelssres_0 sup_set_class irelssres_1 sup_set_class frelssres_0 frelssres_1 irelssres_1 vex opelres syl6ibr adantl relssdv frelssres_0 frelssres_1 resss jctil frelssres_0 frelssres_1 cres frelssres_0 eqss sylibr $.
$}
$( A relation restricted to its domain equals itself.  (Contributed by NM,
     12-Dec-2006.) $)
${
	fresdm_0 $f class A $.
	resdm $p |- ( Rel A -> ( A |` dom A ) = A ) $= fresdm_0 wrel fresdm_0 cdm fresdm_0 cdm wss fresdm_0 fresdm_0 cdm cres fresdm_0 wceq fresdm_0 cdm ssid fresdm_0 fresdm_0 cdm relssres mpan2 $.
$}
$( The restriction of a set is a set.  (Contributed by NM, 28-Mar-1998.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fresexg_0 $f class A $.
	fresexg_1 $f class B $.
	fresexg_2 $f class V $.
	resexg $p |- ( A e. V -> ( A |` B ) e. _V ) $= fresexg_0 fresexg_1 cres fresexg_0 wss fresexg_0 fresexg_2 wcel fresexg_0 fresexg_1 cres cvv wcel fresexg_0 fresexg_1 resss fresexg_0 fresexg_1 cres fresexg_0 fresexg_2 ssexg mpan $.
$}
$( The restriction of a set is a set.  (Contributed by Jeff Madsen,
       19-Jun-2011.) $)
${
	fresex_0 $f class A $.
	fresex_1 $f class B $.
	eresex_0 $e |- A e. _V $.
	resex $p |- ( A |` B ) e. _V $= fresex_0 cvv wcel fresex_0 fresex_1 cres cvv wcel eresex_0 fresex_0 fresex_1 cvv resexg ax-mp $.
$}
$( Restriction of a class abstraction of ordered pairs.  (Contributed by
       NM, 5-Nov-2002.) $)
${
	$d x y A $.
	fresopab_0 $f wff ph $.
	fresopab_1 $f set x $.
	fresopab_2 $f set y $.
	fresopab_3 $f class A $.
	resopab $p |- ( { <. x , y >. | ph } |` A ) = { <. x , y >. | ( x e. A /\ ph ) } $= fresopab_0 fresopab_1 fresopab_2 copab fresopab_3 cres fresopab_0 fresopab_1 fresopab_2 copab fresopab_3 cvv cxp cin fresopab_1 sup_set_class fresopab_3 wcel fresopab_0 wa fresopab_1 fresopab_2 copab fresopab_0 fresopab_1 fresopab_2 copab fresopab_3 df-res fresopab_0 fresopab_1 fresopab_2 copab fresopab_3 cvv cxp cin fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 fresopab_2 copab fresopab_0 fresopab_1 fresopab_2 copab cin fresopab_1 sup_set_class fresopab_3 wcel fresopab_0 wa fresopab_1 fresopab_2 copab fresopab_0 fresopab_1 fresopab_2 copab fresopab_3 cvv cxp cin fresopab_0 fresopab_1 fresopab_2 copab fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 fresopab_2 copab cin fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 fresopab_2 copab fresopab_0 fresopab_1 fresopab_2 copab cin fresopab_3 cvv cxp fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 fresopab_2 copab fresopab_0 fresopab_1 fresopab_2 copab fresopab_3 cvv cxp fresopab_1 sup_set_class fresopab_3 wcel fresopab_2 sup_set_class cvv wcel wa fresopab_1 fresopab_2 copab fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 fresopab_2 copab fresopab_1 fresopab_2 fresopab_3 cvv df-xp fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 sup_set_class fresopab_3 wcel fresopab_2 sup_set_class cvv wcel wa fresopab_1 fresopab_2 fresopab_2 sup_set_class cvv wcel fresopab_1 sup_set_class fresopab_3 wcel fresopab_2 vex biantru opabbii eqtr4i ineq2i fresopab_0 fresopab_1 fresopab_2 copab fresopab_1 sup_set_class fresopab_3 wcel fresopab_1 fresopab_2 copab incom eqtri fresopab_1 sup_set_class fresopab_3 wcel fresopab_0 fresopab_1 fresopab_2 inopab eqtri eqtri $.
$}
$( The existence of a restricted identity function, proved without using
       the Axiom of Replacement (unlike ~ resfunexg ).  (Contributed by NM,
       13-Jan-2007.) $)
${
	$d x y A $.
	iresiexg_0 $f set x $.
	iresiexg_1 $f set y $.
	fresiexg_0 $f class A $.
	fresiexg_1 $f class V $.
	resiexg $p |- ( A e. V -> ( _I |` A ) e. _V ) $= fresiexg_0 fresiexg_1 wcel cid fresiexg_0 cres fresiexg_0 fresiexg_0 cxp wss fresiexg_0 fresiexg_0 cxp cvv wcel cid fresiexg_0 cres cvv wcel iresiexg_0 iresiexg_1 cid fresiexg_0 cres fresiexg_0 fresiexg_0 cxp cid fresiexg_0 relres iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class fresiexg_0 wcel wa iresiexg_0 sup_set_class fresiexg_0 wcel iresiexg_1 sup_set_class fresiexg_0 wcel wa iresiexg_0 sup_set_class iresiexg_1 sup_set_class cop cid fresiexg_0 cres wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class cop fresiexg_0 fresiexg_0 cxp wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class fresiexg_0 wcel wa iresiexg_0 sup_set_class fresiexg_0 wcel iresiexg_1 sup_set_class fresiexg_0 wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class fresiexg_0 wcel simpr iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class fresiexg_0 wcel iresiexg_1 sup_set_class fresiexg_0 wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class fresiexg_0 eleq1 biimpa jca iresiexg_0 sup_set_class iresiexg_1 sup_set_class cop cid fresiexg_0 cres wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class cop cid wcel iresiexg_0 sup_set_class fresiexg_0 wcel wa iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class fresiexg_0 wcel wa iresiexg_0 sup_set_class iresiexg_1 sup_set_class cid fresiexg_0 iresiexg_1 vex opelres iresiexg_0 sup_set_class iresiexg_1 sup_set_class cop cid wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class fresiexg_0 wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class cop cid wcel iresiexg_0 sup_set_class iresiexg_1 sup_set_class cid wbr iresiexg_0 sup_set_class iresiexg_1 sup_set_class wceq iresiexg_0 sup_set_class iresiexg_1 sup_set_class cid df-br iresiexg_0 sup_set_class iresiexg_1 sup_set_class iresiexg_1 vex ideq bitr3i anbi1i bitri iresiexg_0 sup_set_class iresiexg_1 sup_set_class fresiexg_0 fresiexg_0 opelxp 3imtr4i relssi fresiexg_0 fresiexg_1 wcel fresiexg_0 fresiexg_0 cxp cvv wcel fresiexg_0 fresiexg_0 fresiexg_1 fresiexg_1 xpexg anidms cid fresiexg_0 cres fresiexg_0 fresiexg_0 cxp cvv ssexg sylancr $.
$}
$( A subclass of the identity function is the identity function restricted
       to its domain.  (Contributed by NM, 13-Dec-2003.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	iiss_0 $f set x $.
	iiss_1 $f set y $.
	fiss_0 $f class A $.
	iss $p |- ( A C_ _I <-> A = ( _I |` dom A ) ) $= fiss_0 cid wss fiss_0 cid fiss_0 cdm cres wceq fiss_0 cid wss fiss_0 cid fiss_0 cdm cres wceq iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid fiss_0 cdm cres wcel wb iiss_1 wal iiss_0 wal fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid fiss_0 cdm cres wcel wb iiss_0 iiss_1 fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class fiss_0 cdm wcel wa iiss_0 sup_set_class iiss_1 sup_set_class cop cid fiss_0 cdm cres wcel fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class fiss_0 cdm wcel wa fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class fiss_0 cdm wcel fiss_0 cid iiss_0 sup_set_class iiss_1 sup_set_class cop ssel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class fiss_0 cdm wcel wi fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class fiss_0 iiss_0 vex iiss_1 vex opeldm a1i jcad fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class fiss_0 cdm wcel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class iiss_1 sup_set_class wceq fiss_0 cid wss iiss_0 sup_set_class fiss_0 cdm wcel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel wi iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class iiss_1 sup_set_class cid wbr iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_1 sup_set_class cid df-br iiss_0 sup_set_class iiss_1 sup_set_class iiss_1 vex ideq bitr3i fiss_0 cid wss iiss_0 sup_set_class fiss_0 cdm wcel iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel wi iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class fiss_0 cdm wcel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel wi iiss_0 sup_set_class fiss_0 cdm wcel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_1 wex fiss_0 cid wss iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel iiss_1 iiss_0 sup_set_class fiss_0 iiss_0 vex eldm2 fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel iiss_1 fiss_0 cid wss iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel fiss_0 cid iiss_0 sup_set_class iiss_1 sup_set_class cop ssel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid wcel iiss_0 sup_set_class iiss_1 sup_set_class cid wbr iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_1 sup_set_class cid df-br iiss_0 sup_set_class iiss_1 sup_set_class iiss_1 vex ideq bitr3i iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_0 sup_set_class cop iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 iiss_0 sup_set_class iiss_1 sup_set_class iiss_0 sup_set_class opeq2 eleq1d biimprcd syl5bi sylcom exlimdv syl5bi iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_0 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class fiss_0 cdm wcel iiss_0 sup_set_class iiss_1 sup_set_class wceq iiss_0 sup_set_class iiss_0 sup_set_class cop iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 iiss_0 sup_set_class iiss_1 sup_set_class iiss_0 sup_set_class opeq2 eleq1d imbi2d syl5ibcom syl5bi imp3a impbid iiss_0 sup_set_class iiss_1 sup_set_class cid fiss_0 cdm iiss_1 vex opelres syl6bbr alrimivv fiss_0 cid wss fiss_0 wrel cid fiss_0 cdm cres wrel fiss_0 cid fiss_0 cdm cres wceq iiss_0 sup_set_class iiss_1 sup_set_class cop fiss_0 wcel iiss_0 sup_set_class iiss_1 sup_set_class cop cid fiss_0 cdm cres wcel wb iiss_1 wal iiss_0 wal wb fiss_0 cid wss cid wrel fiss_0 wrel reli fiss_0 cid relss mpi cid fiss_0 cdm relres iiss_0 iiss_1 fiss_0 cid fiss_0 cdm cres eqrel sylancl mpbird fiss_0 cid fiss_0 cdm cres wceq fiss_0 cid wss cid fiss_0 cdm cres cid wss cid fiss_0 cdm resss fiss_0 cid fiss_0 cdm cres cid sseq1 mpbiri impbii $.
$}
$( Restriction of a class abstraction of ordered pairs.  (Contributed by
       NM, 24-Aug-2007.) $)
${
	$d x y A $.
	$d x y B $.
	fresopab2_0 $f wff ph $.
	fresopab2_1 $f set x $.
	fresopab2_2 $f set y $.
	fresopab2_3 $f class A $.
	fresopab2_4 $f class B $.
	resopab2 $p |- ( A C_ B -> ( { <. x , y >. | ( x e. B /\ ph ) } |` A ) = { <. x , y >. | ( x e. A /\ ph ) } ) $= fresopab2_3 fresopab2_4 wss fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_0 wa fresopab2_1 fresopab2_2 copab fresopab2_3 cres fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_0 wa wa fresopab2_1 fresopab2_2 copab fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_0 wa fresopab2_1 fresopab2_2 copab fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_0 wa fresopab2_1 fresopab2_2 fresopab2_3 resopab fresopab2_3 fresopab2_4 wss fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_0 wa wa fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_0 wa fresopab2_1 fresopab2_2 fresopab2_3 fresopab2_4 wss fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_0 wa fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel wa fresopab2_0 wa fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_0 wa wa fresopab2_3 fresopab2_4 wss fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel wa fresopab2_0 fresopab2_3 fresopab2_4 wss fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_3 fresopab2_4 fresopab2_1 sup_set_class ssel pm4.71d anbi1d fresopab2_1 sup_set_class fresopab2_3 wcel fresopab2_1 sup_set_class fresopab2_4 wcel fresopab2_0 anass syl6rbb opabbidv syl5eq $.
$}
$( Restriction of the mapping operation.  (Contributed by Mario Carneiro,
       15-Jul-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d y C $.
	iresmpt_0 $f set y $.
	fresmpt_0 $f set x $.
	fresmpt_1 $f class A $.
	fresmpt_2 $f class B $.
	fresmpt_3 $f class C $.
	resmpt $p |- ( B C_ A -> ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C ) ) $= fresmpt_2 fresmpt_1 wss fresmpt_0 sup_set_class fresmpt_1 wcel iresmpt_0 sup_set_class fresmpt_3 wceq wa fresmpt_0 iresmpt_0 copab fresmpt_2 cres fresmpt_0 sup_set_class fresmpt_2 wcel iresmpt_0 sup_set_class fresmpt_3 wceq wa fresmpt_0 iresmpt_0 copab fresmpt_0 fresmpt_1 fresmpt_3 cmpt fresmpt_2 cres fresmpt_0 fresmpt_2 fresmpt_3 cmpt iresmpt_0 sup_set_class fresmpt_3 wceq fresmpt_0 iresmpt_0 fresmpt_2 fresmpt_1 resopab2 fresmpt_0 fresmpt_1 fresmpt_3 cmpt fresmpt_0 sup_set_class fresmpt_1 wcel iresmpt_0 sup_set_class fresmpt_3 wceq wa fresmpt_0 iresmpt_0 copab fresmpt_2 fresmpt_0 iresmpt_0 fresmpt_1 fresmpt_3 df-mpt reseq1i fresmpt_0 iresmpt_0 fresmpt_2 fresmpt_3 df-mpt 3eqtr4g $.
$}
$( Unconditional restriction of the mapping operation.  (Contributed by
       Stefan O'Rear, 24-Jan-2015.)  (Proof shortened by Mario Carneiro,
       22-Mar-2015.) $)
${
	$d x A $.
	$d x B $.
	fresmpt3_0 $f set x $.
	fresmpt3_1 $f class A $.
	fresmpt3_2 $f class B $.
	fresmpt3_3 $f class C $.
	resmpt3 $p |- ( ( x e. A |-> C ) |` B ) = ( x e. ( A i^i B ) |-> C ) $= fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_1 cres fresmpt3_2 cres fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_1 fresmpt3_2 cin cres fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_2 cres fresmpt3_0 fresmpt3_1 fresmpt3_2 cin fresmpt3_3 cmpt fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_1 fresmpt3_2 resres fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_1 cres fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_2 fresmpt3_1 fresmpt3_1 wss fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_1 cres fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt wceq fresmpt3_1 ssid fresmpt3_0 fresmpt3_1 fresmpt3_1 fresmpt3_3 resmpt ax-mp reseq1i fresmpt3_1 fresmpt3_2 cin fresmpt3_1 wss fresmpt3_0 fresmpt3_1 fresmpt3_3 cmpt fresmpt3_1 fresmpt3_2 cin cres fresmpt3_0 fresmpt3_1 fresmpt3_2 cin fresmpt3_3 cmpt wceq fresmpt3_1 fresmpt3_2 inss1 fresmpt3_0 fresmpt3_1 fresmpt3_1 fresmpt3_2 cin fresmpt3_3 resmpt ax-mp 3eqtr3i $.
$}
$( Alternate definition of the restriction operation.  (Contributed by
       Mario Carneiro, 5-Nov-2013.) $)
${
	$d w x y z A $.
	$d w x y z R $.
	idfres2_0 $f set z $.
	idfres2_1 $f set w $.
	fdfres2_0 $f set x $.
	fdfres2_1 $f set y $.
	fdfres2_2 $f class A $.
	fdfres2_3 $f class R $.
	dfres2 $p |- ( R |` A ) = { <. x , y >. | ( x e. A /\ x R y ) } $= idfres2_0 idfres2_1 fdfres2_3 fdfres2_2 cres fdfres2_0 sup_set_class fdfres2_2 wcel fdfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr wa fdfres2_0 fdfres2_1 copab fdfres2_3 fdfres2_2 relres fdfres2_0 sup_set_class fdfres2_2 wcel fdfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr wa fdfres2_0 fdfres2_1 relopab idfres2_0 sup_set_class idfres2_1 sup_set_class cop fdfres2_3 fdfres2_2 cres wcel idfres2_0 sup_set_class fdfres2_2 wcel idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 wbr wa idfres2_0 sup_set_class idfres2_1 sup_set_class cop fdfres2_0 sup_set_class fdfres2_2 wcel fdfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr wa fdfres2_0 fdfres2_1 copab wcel idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 fdfres2_2 cres wbr idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 wbr idfres2_0 sup_set_class fdfres2_2 wcel wa idfres2_0 sup_set_class idfres2_1 sup_set_class cop fdfres2_3 fdfres2_2 cres wcel idfres2_0 sup_set_class fdfres2_2 wcel idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 wbr wa idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 fdfres2_2 idfres2_1 vex brres idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 fdfres2_2 cres df-br idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 wbr idfres2_0 sup_set_class fdfres2_2 wcel ancom 3bitr3i fdfres2_0 sup_set_class fdfres2_2 wcel fdfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr wa idfres2_0 sup_set_class fdfres2_2 wcel idfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr wa idfres2_0 sup_set_class fdfres2_2 wcel idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 wbr wa fdfres2_0 fdfres2_1 idfres2_0 sup_set_class idfres2_1 sup_set_class idfres2_0 vex idfres2_1 vex fdfres2_0 sup_set_class idfres2_0 sup_set_class wceq fdfres2_0 sup_set_class fdfres2_2 wcel idfres2_0 sup_set_class fdfres2_2 wcel fdfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr idfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr fdfres2_0 sup_set_class idfres2_0 sup_set_class fdfres2_2 eleq1 fdfres2_0 sup_set_class idfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 breq1 anbi12d fdfres2_1 sup_set_class idfres2_1 sup_set_class wceq idfres2_0 sup_set_class fdfres2_1 sup_set_class fdfres2_3 wbr idfres2_0 sup_set_class idfres2_1 sup_set_class fdfres2_3 wbr idfres2_0 sup_set_class fdfres2_2 wcel fdfres2_1 sup_set_class idfres2_1 sup_set_class idfres2_0 sup_set_class fdfres2_3 breq2 anbi2d opelopab bitr4i eqrelriiv $.
$}
$( The restricted identity expressed with the class builder.  (Contributed
       by FL, 25-Apr-2012.) $)
${
	$d A x y $.
	fopabresid_0 $f set x $.
	fopabresid_1 $f set y $.
	fopabresid_2 $f class A $.
	opabresid $p |- { <. x , y >. | ( x e. A /\ y = x ) } = ( _I |` A ) $= fopabresid_1 sup_set_class fopabresid_0 sup_set_class wceq fopabresid_0 fopabresid_1 copab fopabresid_2 cres fopabresid_0 sup_set_class fopabresid_2 wcel fopabresid_1 sup_set_class fopabresid_0 sup_set_class wceq wa fopabresid_0 fopabresid_1 copab cid fopabresid_2 cres fopabresid_1 sup_set_class fopabresid_0 sup_set_class wceq fopabresid_0 fopabresid_1 fopabresid_2 resopab fopabresid_1 sup_set_class fopabresid_0 sup_set_class wceq fopabresid_0 fopabresid_1 copab cid fopabresid_2 fopabresid_1 sup_set_class fopabresid_0 sup_set_class wceq fopabresid_0 fopabresid_1 copab fopabresid_0 sup_set_class fopabresid_1 sup_set_class wceq fopabresid_0 fopabresid_1 copab cid fopabresid_1 sup_set_class fopabresid_0 sup_set_class wceq fopabresid_0 sup_set_class fopabresid_1 sup_set_class wceq fopabresid_0 fopabresid_1 fopabresid_1 fopabresid_0 equcom opabbii fopabresid_0 fopabresid_1 dfid3 eqtr4i reseq1i eqtr3i $.
$}
$( The restricted identity expressed with the "maps to" notation.
       (Contributed by FL, 25-Apr-2012.) $)
${
	$d A x y $.
	imptresid_0 $f set y $.
	fmptresid_0 $f set x $.
	fmptresid_1 $f class A $.
	mptresid $p |- ( x e. A |-> x ) = ( _I |` A ) $= fmptresid_0 fmptresid_1 fmptresid_0 sup_set_class cmpt fmptresid_0 sup_set_class fmptresid_1 wcel imptresid_0 sup_set_class fmptresid_0 sup_set_class wceq wa fmptresid_0 imptresid_0 copab cid fmptresid_1 cres fmptresid_0 imptresid_0 fmptresid_1 fmptresid_0 sup_set_class df-mpt fmptresid_0 imptresid_0 fmptresid_1 opabresid eqtri $.
$}
$( The domain of a restricted identity function.  (Contributed by NM,
     27-Aug-2004.) $)
${
	fdmresi_0 $f class A $.
	dmresi $p |- dom ( _I |` A ) = A $= fdmresi_0 cid cdm wss cid fdmresi_0 cres cdm fdmresi_0 wceq fdmresi_0 cvv cid cdm fdmresi_0 ssv dmi sseqtr4i fdmresi_0 cid ssdmres mpbi $.
$}
$( TODO - delete this and replace w/ dfres3 (in FL's mathbox) $)
$( Any relation restricted to the universe is itself.  (Contributed by NM,
     16-Mar-2004.) $)
${
	fresid_0 $f class A $.
	resid $p |- ( Rel A -> ( A |` _V ) = A ) $= fresid_0 wrel fresid_0 cdm cvv wss fresid_0 cvv cres fresid_0 wceq fresid_0 cdm ssv fresid_0 cvv relssres mpan2 $.
$}
$( Equality theorem for image.  (Contributed by NM, 14-Aug-1994.) $)
${
	fimaeq1_0 $f class A $.
	fimaeq1_1 $f class B $.
	fimaeq1_2 $f class C $.
	imaeq1 $p |- ( A = B -> ( A " C ) = ( B " C ) ) $= fimaeq1_0 fimaeq1_1 wceq fimaeq1_0 fimaeq1_2 cres crn fimaeq1_1 fimaeq1_2 cres crn fimaeq1_0 fimaeq1_2 cima fimaeq1_1 fimaeq1_2 cima fimaeq1_0 fimaeq1_1 wceq fimaeq1_0 fimaeq1_2 cres fimaeq1_1 fimaeq1_2 cres fimaeq1_0 fimaeq1_1 fimaeq1_2 reseq1 rneqd fimaeq1_0 fimaeq1_2 df-ima fimaeq1_1 fimaeq1_2 df-ima 3eqtr4g $.
$}
$( Equality theorem for image.  (Contributed by NM, 14-Aug-1994.) $)
${
	fimaeq2_0 $f class A $.
	fimaeq2_1 $f class B $.
	fimaeq2_2 $f class C $.
	imaeq2 $p |- ( A = B -> ( C " A ) = ( C " B ) ) $= fimaeq2_0 fimaeq2_1 wceq fimaeq2_2 fimaeq2_0 cres crn fimaeq2_2 fimaeq2_1 cres crn fimaeq2_2 fimaeq2_0 cima fimaeq2_2 fimaeq2_1 cima fimaeq2_0 fimaeq2_1 wceq fimaeq2_2 fimaeq2_0 cres fimaeq2_2 fimaeq2_1 cres fimaeq2_0 fimaeq2_1 fimaeq2_2 reseq2 rneqd fimaeq2_2 fimaeq2_0 df-ima fimaeq2_2 fimaeq2_1 df-ima 3eqtr4g $.
$}
$( Equality theorem for image.  (Contributed by NM, 21-Dec-2008.) $)
${
	fimaeq1i_0 $f class A $.
	fimaeq1i_1 $f class B $.
	fimaeq1i_2 $f class C $.
	eimaeq1i_0 $e |- A = B $.
	imaeq1i $p |- ( A " C ) = ( B " C ) $= fimaeq1i_0 fimaeq1i_1 wceq fimaeq1i_0 fimaeq1i_2 cima fimaeq1i_1 fimaeq1i_2 cima wceq eimaeq1i_0 fimaeq1i_0 fimaeq1i_1 fimaeq1i_2 imaeq1 ax-mp $.
$}
$( Equality theorem for image.  (Contributed by NM, 21-Dec-2008.) $)
${
	fimaeq2i_0 $f class A $.
	fimaeq2i_1 $f class B $.
	fimaeq2i_2 $f class C $.
	eimaeq2i_0 $e |- A = B $.
	imaeq2i $p |- ( C " A ) = ( C " B ) $= fimaeq2i_0 fimaeq2i_1 wceq fimaeq2i_2 fimaeq2i_0 cima fimaeq2i_2 fimaeq2i_1 cima wceq eimaeq2i_0 fimaeq2i_0 fimaeq2i_1 fimaeq2i_2 imaeq2 ax-mp $.
$}
$( Equality theorem for image.  (Contributed by FL, 15-Dec-2006.) $)
${
	fimaeq1d_0 $f wff ph $.
	fimaeq1d_1 $f class A $.
	fimaeq1d_2 $f class B $.
	fimaeq1d_3 $f class C $.
	eimaeq1d_0 $e |- ( ph -> A = B ) $.
	imaeq1d $p |- ( ph -> ( A " C ) = ( B " C ) ) $= fimaeq1d_0 fimaeq1d_1 fimaeq1d_2 wceq fimaeq1d_1 fimaeq1d_3 cima fimaeq1d_2 fimaeq1d_3 cima wceq eimaeq1d_0 fimaeq1d_1 fimaeq1d_2 fimaeq1d_3 imaeq1 syl $.
$}
$( Equality theorem for image.  (Contributed by FL, 15-Dec-2006.) $)
${
	fimaeq2d_0 $f wff ph $.
	fimaeq2d_1 $f class A $.
	fimaeq2d_2 $f class B $.
	fimaeq2d_3 $f class C $.
	eimaeq2d_0 $e |- ( ph -> A = B ) $.
	imaeq2d $p |- ( ph -> ( C " A ) = ( C " B ) ) $= fimaeq2d_0 fimaeq2d_1 fimaeq2d_2 wceq fimaeq2d_3 fimaeq2d_1 cima fimaeq2d_3 fimaeq2d_2 cima wceq eimaeq2d_0 fimaeq2d_1 fimaeq2d_2 fimaeq2d_3 imaeq2 syl $.
$}
$( Equality theorem for image.  (Contributed by Mario Carneiro,
       4-Dec-2016.) $)
${
	fimaeq12d_0 $f wff ph $.
	fimaeq12d_1 $f class A $.
	fimaeq12d_2 $f class B $.
	fimaeq12d_3 $f class C $.
	fimaeq12d_4 $f class D $.
	eimaeq12d_0 $e |- ( ph -> A = B ) $.
	eimaeq12d_1 $e |- ( ph -> C = D ) $.
	imaeq12d $p |- ( ph -> ( A " C ) = ( B " D ) ) $= fimaeq12d_0 fimaeq12d_1 fimaeq12d_3 cima fimaeq12d_2 fimaeq12d_3 cima fimaeq12d_2 fimaeq12d_4 cima fimaeq12d_0 fimaeq12d_1 fimaeq12d_2 fimaeq12d_3 eimaeq12d_0 imaeq1d fimaeq12d_0 fimaeq12d_3 fimaeq12d_4 fimaeq12d_2 eimaeq12d_1 imaeq2d eqtrd $.
$}
$( Alternate definition of image.  Compare definition (d) of [Enderton]
       p. 44.  (Contributed by NM, 19-Apr-2004.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	fdfima2_0 $f set x $.
	fdfima2_1 $f set y $.
	fdfima2_2 $f class A $.
	fdfima2_3 $f class B $.
	dfima2 $p |- ( A " B ) = { y | E. x e. B x A y } $= fdfima2_2 fdfima2_3 cima fdfima2_2 fdfima2_3 cres crn fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 fdfima2_3 cres wbr fdfima2_0 wex fdfima2_1 cab fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr fdfima2_0 fdfima2_3 wrex fdfima2_1 cab fdfima2_2 fdfima2_3 df-ima fdfima2_0 fdfima2_1 fdfima2_2 fdfima2_3 cres dfrn2 fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 fdfima2_3 cres wbr fdfima2_0 wex fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr fdfima2_0 fdfima2_3 wrex fdfima2_1 fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 fdfima2_3 cres wbr fdfima2_0 wex fdfima2_0 sup_set_class fdfima2_3 wcel fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr wa fdfima2_0 wex fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr fdfima2_0 fdfima2_3 wrex fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 fdfima2_3 cres wbr fdfima2_0 sup_set_class fdfima2_3 wcel fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr wa fdfima2_0 fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 fdfima2_3 cres wbr fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr fdfima2_0 sup_set_class fdfima2_3 wcel wa fdfima2_0 sup_set_class fdfima2_3 wcel fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr wa fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 fdfima2_3 fdfima2_1 vex brres fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr fdfima2_0 sup_set_class fdfima2_3 wcel ancom bitri exbii fdfima2_0 sup_set_class fdfima2_1 sup_set_class fdfima2_2 wbr fdfima2_0 fdfima2_3 df-rex bitr4i abbii 3eqtri $.
$}
$( Alternate definition of image.  Compare definition (d) of [Enderton]
       p. 44.  (Contributed by NM, 14-Aug-1994.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	fdfima3_0 $f set x $.
	fdfima3_1 $f set y $.
	fdfima3_2 $f class A $.
	fdfima3_3 $f class B $.
	dfima3 $p |- ( A " B ) = { y | E. x ( x e. B /\ <. x , y >. e. A ) } $= fdfima3_2 fdfima3_3 cima fdfima3_0 sup_set_class fdfima3_1 sup_set_class fdfima3_2 wbr fdfima3_0 fdfima3_3 wrex fdfima3_1 cab fdfima3_0 sup_set_class fdfima3_3 wcel fdfima3_0 sup_set_class fdfima3_1 sup_set_class cop fdfima3_2 wcel wa fdfima3_0 wex fdfima3_1 cab fdfima3_0 fdfima3_1 fdfima3_2 fdfima3_3 dfima2 fdfima3_0 sup_set_class fdfima3_1 sup_set_class fdfima3_2 wbr fdfima3_0 fdfima3_3 wrex fdfima3_0 sup_set_class fdfima3_3 wcel fdfima3_0 sup_set_class fdfima3_1 sup_set_class cop fdfima3_2 wcel wa fdfima3_0 wex fdfima3_1 fdfima3_0 sup_set_class fdfima3_1 sup_set_class fdfima3_2 wbr fdfima3_0 fdfima3_3 wrex fdfima3_0 sup_set_class fdfima3_1 sup_set_class cop fdfima3_2 wcel fdfima3_0 fdfima3_3 wrex fdfima3_0 sup_set_class fdfima3_3 wcel fdfima3_0 sup_set_class fdfima3_1 sup_set_class cop fdfima3_2 wcel wa fdfima3_0 wex fdfima3_0 sup_set_class fdfima3_1 sup_set_class fdfima3_2 wbr fdfima3_0 sup_set_class fdfima3_1 sup_set_class cop fdfima3_2 wcel fdfima3_0 fdfima3_3 fdfima3_0 sup_set_class fdfima3_1 sup_set_class fdfima3_2 df-br rexbii fdfima3_0 sup_set_class fdfima3_1 sup_set_class cop fdfima3_2 wcel fdfima3_0 fdfima3_3 df-rex bitri abbii eqtri $.
$}
$( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 20-Jan-2007.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ielimag_0 $f set y $.
	felimag_0 $f set x $.
	felimag_1 $f class A $.
	felimag_2 $f class B $.
	felimag_3 $f class C $.
	felimag_4 $f class V $.
	elimag $p |- ( A e. V -> ( A e. ( B " C ) <-> E. x e. C x B A ) ) $= felimag_0 sup_set_class ielimag_0 sup_set_class felimag_2 wbr felimag_0 felimag_3 wrex felimag_0 sup_set_class felimag_1 felimag_2 wbr felimag_0 felimag_3 wrex ielimag_0 felimag_1 felimag_2 felimag_3 cima felimag_4 ielimag_0 sup_set_class felimag_1 wceq felimag_0 sup_set_class ielimag_0 sup_set_class felimag_2 wbr felimag_0 sup_set_class felimag_1 felimag_2 wbr felimag_0 felimag_3 ielimag_0 sup_set_class felimag_1 felimag_0 sup_set_class felimag_2 breq2 rexbidv felimag_0 ielimag_0 felimag_2 felimag_3 dfima2 elab2g $.
$}
$( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 19-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	felima_0 $f set x $.
	felima_1 $f class A $.
	felima_2 $f class B $.
	felima_3 $f class C $.
	eelima_0 $e |- A e. _V $.
	elima $p |- ( A e. ( B " C ) <-> E. x e. C x B A ) $= felima_1 cvv wcel felima_1 felima_2 felima_3 cima wcel felima_0 sup_set_class felima_1 felima_2 wbr felima_0 felima_3 wrex wb eelima_0 felima_0 felima_1 felima_2 felima_3 cvv elimag ax-mp $.
$}
$( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 11-Aug-2004.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	felima2_0 $f set x $.
	felima2_1 $f class A $.
	felima2_2 $f class B $.
	felima2_3 $f class C $.
	eelima2_0 $e |- A e. _V $.
	elima2 $p |- ( A e. ( B " C ) <-> E. x ( x e. C /\ x B A ) ) $= felima2_1 felima2_2 felima2_3 cima wcel felima2_0 sup_set_class felima2_1 felima2_2 wbr felima2_0 felima2_3 wrex felima2_0 sup_set_class felima2_3 wcel felima2_0 sup_set_class felima2_1 felima2_2 wbr wa felima2_0 wex felima2_0 felima2_1 felima2_2 felima2_3 eelima2_0 elima felima2_0 sup_set_class felima2_1 felima2_2 wbr felima2_0 felima2_3 df-rex bitri $.
$}
$( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 14-Aug-1994.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	felima3_0 $f set x $.
	felima3_1 $f class A $.
	felima3_2 $f class B $.
	felima3_3 $f class C $.
	eelima3_0 $e |- A e. _V $.
	elima3 $p |- ( A e. ( B " C ) <-> E. x ( x e. C /\ <. x , A >. e. B ) ) $= felima3_1 felima3_2 felima3_3 cima wcel felima3_0 sup_set_class felima3_3 wcel felima3_0 sup_set_class felima3_1 felima3_2 wbr wa felima3_0 wex felima3_0 sup_set_class felima3_3 wcel felima3_0 sup_set_class felima3_1 cop felima3_2 wcel wa felima3_0 wex felima3_0 felima3_1 felima3_2 felima3_3 eelima3_0 elima2 felima3_0 sup_set_class felima3_3 wcel felima3_0 sup_set_class felima3_1 felima3_2 wbr wa felima3_0 sup_set_class felima3_3 wcel felima3_0 sup_set_class felima3_1 cop felima3_2 wcel wa felima3_0 felima3_0 sup_set_class felima3_1 felima3_2 wbr felima3_0 sup_set_class felima3_1 cop felima3_2 wcel felima3_0 sup_set_class felima3_3 wcel felima3_0 sup_set_class felima3_1 felima3_2 df-br anbi2i exbii bitri $.
$}
$( Bound-variable hypothesis builder for image.  (Contributed by NM,
       30-Dec-1996.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fnfima_0 $f set x $.
	fnfima_1 $f class A $.
	fnfima_2 $f class B $.
	enfima_0 $e |- F/_ x A $.
	enfima_1 $e |- F/_ x B $.
	nfima $p |- F/_ x ( A " B ) $= fnfima_0 fnfima_1 fnfima_2 cima fnfima_1 fnfima_2 cres crn fnfima_1 fnfima_2 df-ima fnfima_0 fnfima_1 fnfima_2 cres fnfima_0 fnfima_1 fnfima_2 enfima_0 enfima_1 nfres nfrn nfcxfr $.
$}
$( Deduction version of bound-variable hypothesis builder ~ nfima .
       (Contributed by FL, 15-Dec-2006.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
${
	$d x z $.
	$d B z $.
	$d A z $.
	infimad_0 $f set z $.
	fnfimad_0 $f wff ph $.
	fnfimad_1 $f set x $.
	fnfimad_2 $f class A $.
	fnfimad_3 $f class B $.
	enfimad_0 $e |- ( ph -> F/_ x A ) $.
	enfimad_1 $e |- ( ph -> F/_ x B ) $.
	nfimad $p |- ( ph -> F/_ x ( A " B ) ) $= fnfimad_0 fnfimad_1 infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 wal infimad_0 cab infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab cima wnfc fnfimad_1 fnfimad_2 fnfimad_3 cima wnfc fnfimad_1 infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 wal infimad_0 cab infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 infimad_0 nfaba1 infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 infimad_0 nfaba1 nfima fnfimad_0 fnfimad_1 fnfimad_2 wnfc fnfimad_1 fnfimad_3 wnfc fnfimad_1 infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 wal infimad_0 cab infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab cima wnfc fnfimad_1 fnfimad_2 fnfimad_3 cima wnfc wb enfimad_0 enfimad_1 fnfimad_1 fnfimad_2 wnfc fnfimad_1 fnfimad_3 wnfc wa fnfimad_1 infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 wal infimad_0 cab infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab cima fnfimad_2 fnfimad_3 cima fnfimad_1 fnfimad_2 wnfc fnfimad_1 fnfimad_3 wnfc fnfimad_1 fnfimad_1 fnfimad_2 nfnfc1 fnfimad_1 fnfimad_3 nfnfc1 nfan fnfimad_1 fnfimad_2 wnfc fnfimad_1 fnfimad_3 wnfc infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 wal infimad_0 cab infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab cima fnfimad_2 infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab cima fnfimad_2 fnfimad_3 cima fnfimad_1 fnfimad_2 wnfc infimad_0 sup_set_class fnfimad_2 wcel fnfimad_1 wal infimad_0 cab fnfimad_2 infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab fnfimad_1 infimad_0 fnfimad_2 abidnf imaeq1d fnfimad_1 fnfimad_3 wnfc infimad_0 sup_set_class fnfimad_3 wcel fnfimad_1 wal infimad_0 cab fnfimad_3 fnfimad_2 fnfimad_1 infimad_0 fnfimad_3 abidnf imaeq2d sylan9eq nfceqdf syl2anc mpbii $.
$}
$( Move class substitution in and out of the image of a function.
       (Contributed by FL, 15-Dec-2006.)  (Proof shortened by Mario Carneiro,
       4-Dec-2016.) $)
${
	$d A y $.
	$d B y $.
	$d C y $.
	$d x y $.
	$d F y $.
	icsbima12g_0 $f set y $.
	fcsbima12g_0 $f set x $.
	fcsbima12g_1 $f class A $.
	fcsbima12g_2 $f class B $.
	fcsbima12g_3 $f class C $.
	fcsbima12g_4 $f class F $.
	csbima12g $p |- ( A e. C -> [_ A / x ]_ ( F " B ) = ( [_ A / x ]_ F " [_ A / x ]_ B ) ) $= fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 fcsbima12g_2 cima csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csb cima wceq fcsbima12g_0 fcsbima12g_1 fcsbima12g_4 fcsbima12g_2 cima csb fcsbima12g_0 fcsbima12g_1 fcsbima12g_4 csb fcsbima12g_0 fcsbima12g_1 fcsbima12g_2 csb cima wceq icsbima12g_0 fcsbima12g_1 fcsbima12g_3 icsbima12g_0 sup_set_class fcsbima12g_1 wceq fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 fcsbima12g_2 cima csb fcsbima12g_0 fcsbima12g_1 fcsbima12g_4 fcsbima12g_2 cima csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csb cima fcsbima12g_0 fcsbima12g_1 fcsbima12g_4 csb fcsbima12g_0 fcsbima12g_1 fcsbima12g_2 csb cima fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_1 fcsbima12g_4 fcsbima12g_2 cima csbeq1 icsbima12g_0 sup_set_class fcsbima12g_1 wceq fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csb fcsbima12g_0 fcsbima12g_1 fcsbima12g_4 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csb fcsbima12g_0 fcsbima12g_1 fcsbima12g_2 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_1 fcsbima12g_4 csbeq1 fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_1 fcsbima12g_2 csbeq1 imaeq12d eqeq12d fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 fcsbima12g_2 cima fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csb cima icsbima12g_0 vex fcsbima12g_0 fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 nfcsb1v fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 nfcsb1v nfima fcsbima12g_0 sup_set_class icsbima12g_0 sup_set_class wceq fcsbima12g_4 fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csb fcsbima12g_2 fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csb fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_4 csbeq1a fcsbima12g_0 icsbima12g_0 sup_set_class fcsbima12g_2 csbeq1a imaeq12d csbief vtoclg $.
$}
$( Move class substitution in and out of the image of a function.  (This is
     ~ csbima12g with a shortened proof, shortened by Alan Sare, 10-Nov-2012.)
     The proof is derived from the virtual deduction proof ~ csbima12gALTVD .
     Although the proof is shorter, the total number of steps of all theorems
     used in the proof is probably longer.  (Contributed by NM, 10-Nov-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
${
	fcsbima12gALT_0 $f set x $.
	fcsbima12gALT_1 $f class A $.
	fcsbima12gALT_2 $f class B $.
	fcsbima12gALT_3 $f class C $.
	fcsbima12gALT_4 $f class F $.
	csbima12gALT $p |- ( A e. C -> [_ A / x ]_ ( F " B ) = ( [_ A / x ]_ F " [_ A / x ]_ B ) ) $= fcsbima12gALT_1 fcsbima12gALT_3 wcel fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cres crn csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_2 csb cres crn fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cima csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_2 csb cima fcsbima12gALT_1 fcsbima12gALT_3 wcel fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cres crn csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cres csb crn fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_2 csb cres crn fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cres fcsbima12gALT_3 csbrng fcsbima12gALT_1 fcsbima12gALT_3 wcel fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cres csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_2 csb cres fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 fcsbima12gALT_3 csbresg rneqd eqtrd fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 fcsbima12gALT_2 cima fcsbima12gALT_4 fcsbima12gALT_2 cres crn fcsbima12gALT_4 fcsbima12gALT_2 df-ima csbeq2i fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_4 csb fcsbima12gALT_0 fcsbima12gALT_1 fcsbima12gALT_2 csb df-ima 3eqtr4g $.
$}
$( The image of the domain of a class is the range of the class.
       (Contributed by NM, 14-Aug-1994.) $)
${
	$d x y A $.
	$d x y $.
	iimadmrn_0 $f set x $.
	iimadmrn_1 $f set y $.
	fimadmrn_0 $f class A $.
	imadmrn $p |- ( A " dom A ) = ran A $= iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel wa iimadmrn_0 wex iimadmrn_1 cab iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 wex iimadmrn_1 cab fimadmrn_0 fimadmrn_0 cdm cima fimadmrn_0 crn iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel wa iimadmrn_0 wex iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 wex iimadmrn_1 iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel wa iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel wa iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel wa iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class fimadmrn_0 iimadmrn_0 vex iimadmrn_1 vex opeldm pm4.71i iimadmrn_0 sup_set_class iimadmrn_1 sup_set_class cop fimadmrn_0 wcel iimadmrn_0 sup_set_class fimadmrn_0 cdm wcel ancom bitr2i exbii abbii iimadmrn_0 iimadmrn_1 fimadmrn_0 fimadmrn_0 cdm dfima3 iimadmrn_0 iimadmrn_1 fimadmrn_0 dfrn3 3eqtr4i $.
$}
$( The image of a class is a subset of its range.  Theorem 3.16(xi) of
       [Monk1] p. 39.  (Contributed by NM, 31-Mar-1995.) $)
${
	$d x y A $.
	$d x y B $.
	iimassrn_0 $f set x $.
	iimassrn_1 $f set y $.
	fimassrn_0 $f class A $.
	fimassrn_1 $f class B $.
	imassrn $p |- ( A " B ) C_ ran A $= iimassrn_0 sup_set_class fimassrn_1 wcel iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel wa iimassrn_0 wex iimassrn_1 cab iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel iimassrn_0 wex iimassrn_1 cab fimassrn_0 fimassrn_1 cima fimassrn_0 crn iimassrn_0 sup_set_class fimassrn_1 wcel iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel wa iimassrn_0 wex iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel iimassrn_0 wex iimassrn_1 iimassrn_0 sup_set_class fimassrn_1 wcel iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel wa iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel iimassrn_0 iimassrn_0 sup_set_class fimassrn_1 wcel iimassrn_0 sup_set_class iimassrn_1 sup_set_class cop fimassrn_0 wcel simpr eximi ss2abi iimassrn_0 iimassrn_1 fimassrn_0 fimassrn_1 dfima3 iimassrn_0 iimassrn_1 fimassrn_0 dfrn3 3sstr4i $.
$}
$( The image of a set is a set.  Theorem 3.17 of [Monk1] p. 39.  (Contributed
     by NM, 24-Jul-1995.) $)
${
	fimaexg_0 $f class A $.
	fimaexg_1 $f class B $.
	fimaexg_2 $f class V $.
	imaexg $p |- ( A e. V -> ( A " B ) e. _V ) $= fimaexg_0 fimaexg_2 wcel fimaexg_0 fimaexg_1 cima fimaexg_0 crn wss fimaexg_0 crn cvv wcel fimaexg_0 fimaexg_1 cima cvv wcel fimaexg_0 fimaexg_1 imassrn fimaexg_0 fimaexg_2 rnexg fimaexg_0 fimaexg_1 cima fimaexg_0 crn cvv ssexg sylancr $.
$}
$( Image under the identity relation.  Theorem 3.16(viii) of [Monk1]
       p. 38.  (Contributed by NM, 30-Apr-1998.) $)
${
	$d x y A $.
	iimai_0 $f set x $.
	iimai_1 $f set y $.
	fimai_0 $f class A $.
	imai $p |- ( _I " A ) = A $= cid fimai_0 cima iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel wa iimai_0 wex iimai_1 cab iimai_1 sup_set_class fimai_0 wcel iimai_1 cab fimai_0 iimai_0 iimai_1 cid fimai_0 dfima3 iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel wa iimai_0 wex iimai_1 sup_set_class fimai_0 wcel iimai_1 iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel wa iimai_0 wex iimai_0 sup_set_class iimai_1 sup_set_class wceq iimai_0 sup_set_class fimai_0 wcel wa iimai_0 wex iimai_1 sup_set_class fimai_0 wcel iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel wa iimai_0 sup_set_class iimai_1 sup_set_class wceq iimai_0 sup_set_class fimai_0 wcel wa iimai_0 iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel wa iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class wceq wa iimai_0 sup_set_class iimai_1 sup_set_class wceq iimai_0 sup_set_class fimai_0 wcel wa iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel iimai_0 sup_set_class iimai_1 sup_set_class wceq iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class cop cid wcel iimai_0 sup_set_class iimai_1 sup_set_class cid wbr iimai_0 sup_set_class iimai_1 sup_set_class wceq iimai_0 sup_set_class iimai_1 sup_set_class cid df-br iimai_0 sup_set_class iimai_1 sup_set_class iimai_1 vex ideq bitr3i anbi2i iimai_0 sup_set_class fimai_0 wcel iimai_0 sup_set_class iimai_1 sup_set_class wceq ancom bitri exbii iimai_0 sup_set_class fimai_0 wcel iimai_1 sup_set_class fimai_0 wcel iimai_0 iimai_1 sup_set_class iimai_1 vex iimai_0 sup_set_class iimai_1 sup_set_class fimai_0 eleq1 ceqsexv bitri abbii iimai_1 fimai_0 abid2 3eqtri $.
$}
$( The range of the restricted identity function.  (Contributed by NM,
     27-Aug-2004.) $)
${
	frnresi_0 $f class A $.
	rnresi $p |- ran ( _I |` A ) = A $= cid frnresi_0 cima cid frnresi_0 cres crn frnresi_0 cid frnresi_0 df-ima frnresi_0 imai eqtr3i $.
$}
$( The image of a restriction of the identity function.  (Contributed by FL,
     31-Dec-2006.) $)
${
	fresiima_0 $f class A $.
	fresiima_1 $f class B $.
	resiima $p |- ( B C_ A -> ( ( _I |` A ) " B ) = B ) $= fresiima_1 fresiima_0 wss cid fresiima_0 cres fresiima_1 cima cid fresiima_0 cres fresiima_1 cres crn cid fresiima_1 cres crn fresiima_1 cid fresiima_0 cres fresiima_1 cima cid fresiima_0 cres fresiima_1 cres crn wceq fresiima_1 fresiima_0 wss cid fresiima_0 cres fresiima_1 df-ima a1i fresiima_1 fresiima_0 wss cid fresiima_0 cres fresiima_1 cres cid fresiima_1 cres cid fresiima_1 fresiima_0 resabs1 rneqd cid fresiima_1 cres crn fresiima_1 wceq fresiima_1 fresiima_0 wss fresiima_1 rnresi a1i 3eqtrd $.
$}
$( Image of the empty set.  Theorem 3.16(ii) of [Monk1] p. 38.  (Contributed
     by NM, 20-May-1998.) $)
${
	fima0_0 $f class A $.
	ima0 $p |- ( A " (/) ) = (/) $= fima0_0 c0 cima fima0_0 c0 cres crn c0 crn c0 fima0_0 c0 df-ima fima0_0 c0 cres c0 fima0_0 res0 rneqi rn0 3eqtri $.
$}
$( Image under the empty relation.  (Contributed by FL, 11-Jan-2007.) $)
${
	f0ima_0 $f class A $.
	0ima $p |- ( (/) " A ) = (/) $= c0 f0ima_0 cima c0 c0 f0ima_0 cima c0 crn c0 c0 f0ima_0 imassrn rn0 sseqtri c0 f0ima_0 cima 0ss eqssi $.
$}
$( A class whose image under another is empty is disjoint with the other's
     domain.  (Contributed by FL, 24-Jan-2007.) $)
${
	fimadisj_0 $f class A $.
	fimadisj_1 $f class B $.
	imadisj $p |- ( ( A " B ) = (/) <-> ( dom A i^i B ) = (/) ) $= fimadisj_0 fimadisj_1 cima c0 wceq fimadisj_0 fimadisj_1 cres crn c0 wceq fimadisj_0 fimadisj_1 cres cdm c0 wceq fimadisj_0 cdm fimadisj_1 cin c0 wceq fimadisj_0 fimadisj_1 cima fimadisj_0 fimadisj_1 cres crn c0 fimadisj_0 fimadisj_1 df-ima eqeq1i fimadisj_0 fimadisj_1 cres dm0rn0 fimadisj_0 fimadisj_1 cres cdm fimadisj_0 cdm fimadisj_1 cin c0 fimadisj_0 fimadisj_1 cres cdm fimadisj_1 fimadisj_0 cdm cin fimadisj_0 cdm fimadisj_1 cin fimadisj_0 fimadisj_1 dmres fimadisj_1 fimadisj_0 cdm incom eqtri eqeq1i 3bitr2i $.
$}
$( A preimage under any class is included in the domain of the class.
     (Contributed by FL, 29-Jan-2007.) $)
${
	fcnvimass_0 $f class A $.
	fcnvimass_1 $f class B $.
	cnvimass $p |- ( `' A " B ) C_ dom A $= fcnvimass_0 ccnv fcnvimass_1 cima fcnvimass_0 ccnv crn fcnvimass_0 cdm fcnvimass_0 ccnv fcnvimass_1 imassrn fcnvimass_0 dfdm4 sseqtr4i $.
$}
$( The preimage of the range of a class is the domain of the class.
     (Contributed by Jeff Hankins, 15-Jul-2009.) $)
${
	fcnvimarndm_0 $f class A $.
	cnvimarndm $p |- ( `' A " ran A ) = dom A $= fcnvimarndm_0 ccnv fcnvimarndm_0 ccnv cdm cima fcnvimarndm_0 ccnv crn fcnvimarndm_0 ccnv fcnvimarndm_0 crn cima fcnvimarndm_0 cdm fcnvimarndm_0 ccnv imadmrn fcnvimarndm_0 crn fcnvimarndm_0 ccnv cdm fcnvimarndm_0 ccnv fcnvimarndm_0 df-rn imaeq2i fcnvimarndm_0 dfdm4 3eqtr4i $.
$}
$( The image of a singleton.  (Contributed by NM, 8-May-2005.) $)
${
	$d x y A $.
	$d x B $.
	$d x y R $.
	iimasng_0 $f set x $.
	fimasng_0 $f set y $.
	fimasng_1 $f class A $.
	fimasng_2 $f class B $.
	fimasng_3 $f class R $.
	imasng $p |- ( A e. B -> ( R " { A } ) = { y | A R y } ) $= fimasng_1 fimasng_2 wcel fimasng_1 cvv wcel fimasng_3 fimasng_1 csn cima fimasng_1 fimasng_0 sup_set_class fimasng_3 wbr fimasng_0 cab wceq fimasng_1 fimasng_2 elex fimasng_1 cvv wcel fimasng_3 fimasng_1 csn cima iimasng_0 sup_set_class fimasng_0 sup_set_class fimasng_3 wbr iimasng_0 fimasng_1 csn wrex fimasng_0 cab fimasng_1 fimasng_0 sup_set_class fimasng_3 wbr fimasng_0 cab iimasng_0 fimasng_0 fimasng_3 fimasng_1 csn dfima2 fimasng_1 cvv wcel iimasng_0 sup_set_class fimasng_0 sup_set_class fimasng_3 wbr iimasng_0 fimasng_1 csn wrex fimasng_1 fimasng_0 sup_set_class fimasng_3 wbr fimasng_0 iimasng_0 sup_set_class fimasng_0 sup_set_class fimasng_3 wbr fimasng_1 fimasng_0 sup_set_class fimasng_3 wbr iimasng_0 fimasng_1 cvv iimasng_0 sup_set_class fimasng_1 fimasng_0 sup_set_class fimasng_3 breq1 rexsng abbidv syl5eq syl $.
$}
$( The image of a singleton.  (Contributed by NM, 20-May-1998.) $)
${
	$d y A $.
	$d y R $.
	frelimasn_0 $f set y $.
	frelimasn_1 $f class A $.
	frelimasn_2 $f class R $.
	relimasn $p |- ( Rel R -> ( R " { A } ) = { y | A R y } ) $= frelimasn_2 wrel frelimasn_1 cvv wcel frelimasn_2 frelimasn_1 csn cima frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 cab wceq frelimasn_2 wrel frelimasn_1 cvv wcel wn frelimasn_2 frelimasn_1 csn cima frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 cab wceq frelimasn_2 wrel frelimasn_1 cvv wcel wn wa frelimasn_2 frelimasn_1 csn cima c0 frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 cab frelimasn_1 cvv wcel wn frelimasn_2 frelimasn_1 csn cima c0 wceq frelimasn_2 wrel frelimasn_1 cvv wcel wn frelimasn_2 frelimasn_1 csn cima frelimasn_2 c0 cima c0 frelimasn_1 cvv wcel wn frelimasn_1 csn c0 wceq frelimasn_2 frelimasn_1 csn cima frelimasn_2 c0 cima wceq frelimasn_1 snprc frelimasn_1 csn c0 frelimasn_2 imaeq2 sylbi frelimasn_2 ima0 syl6eq adantl frelimasn_2 wrel frelimasn_1 cvv wcel wn wa frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 wex wn frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 cab c0 wceq frelimasn_2 wrel frelimasn_1 cvv wcel wn wa frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 frelimasn_2 wrel frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_1 cvv wcel frelimasn_2 wrel frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_1 cvv wcel frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 brrelex ex con3and nexdv frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 wex frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 cab c0 frelimasn_1 frelimasn_0 sup_set_class frelimasn_2 wbr frelimasn_0 abn0 necon1bbii sylib eqtr4d ex frelimasn_0 frelimasn_1 cvv frelimasn_2 imasng pm2.61d2 $.
$}
$( Elementhood in the image of a singleton.  (Contributed by Mario
       Carneiro, 3-Nov-2015.) $)
${
	$d x A $.
	$d x B $.
	$d x R $.
	ielrelimasn_0 $f set x $.
	felrelimasn_0 $f class A $.
	felrelimasn_1 $f class B $.
	felrelimasn_2 $f class R $.
	elrelimasn $p |- ( Rel R -> ( B e. ( R " { A } ) <-> A R B ) ) $= felrelimasn_2 wrel felrelimasn_1 felrelimasn_2 felrelimasn_0 csn cima wcel felrelimasn_1 felrelimasn_0 ielrelimasn_0 sup_set_class felrelimasn_2 wbr ielrelimasn_0 cab wcel felrelimasn_0 felrelimasn_1 felrelimasn_2 wbr felrelimasn_2 wrel felrelimasn_2 felrelimasn_0 csn cima felrelimasn_0 ielrelimasn_0 sup_set_class felrelimasn_2 wbr ielrelimasn_0 cab felrelimasn_1 ielrelimasn_0 felrelimasn_0 felrelimasn_2 relimasn eleq2d felrelimasn_2 wrel felrelimasn_0 felrelimasn_1 felrelimasn_2 wbr felrelimasn_1 cvv wcel wi felrelimasn_1 felrelimasn_0 ielrelimasn_0 sup_set_class felrelimasn_2 wbr ielrelimasn_0 cab wcel felrelimasn_0 felrelimasn_1 felrelimasn_2 wbr wb felrelimasn_2 wrel felrelimasn_0 felrelimasn_1 felrelimasn_2 wbr felrelimasn_1 cvv wcel felrelimasn_0 felrelimasn_1 felrelimasn_2 brrelex2 ex felrelimasn_0 ielrelimasn_0 sup_set_class felrelimasn_2 wbr felrelimasn_0 felrelimasn_1 felrelimasn_2 wbr ielrelimasn_0 felrelimasn_1 cvv ielrelimasn_0 sup_set_class felrelimasn_1 felrelimasn_0 felrelimasn_2 breq2 elab3g syl bitrd $.
$}
$( Membership in an image of a singleton.  (Contributed by NM,
       15-Mar-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x A $.
	$d x B $.
	$d x C $.
	ielimasn_0 $f set x $.
	felimasn_0 $f class A $.
	felimasn_1 $f class B $.
	felimasn_2 $f class C $.
	eelimasn_0 $e |- B e. _V $.
	eelimasn_1 $e |- C e. _V $.
	elimasn $p |- ( C e. ( A " { B } ) <-> <. B , C >. e. A ) $= felimasn_2 felimasn_0 felimasn_1 csn cima wcel felimasn_1 felimasn_2 felimasn_0 wbr felimasn_1 felimasn_2 cop felimasn_0 wcel felimasn_1 ielimasn_0 sup_set_class felimasn_0 wbr felimasn_1 felimasn_2 felimasn_0 wbr ielimasn_0 felimasn_2 felimasn_0 felimasn_1 csn cima eelimasn_1 ielimasn_0 sup_set_class felimasn_2 felimasn_1 felimasn_0 breq2 felimasn_1 cvv wcel felimasn_0 felimasn_1 csn cima felimasn_1 ielimasn_0 sup_set_class felimasn_0 wbr ielimasn_0 cab wceq eelimasn_0 ielimasn_0 felimasn_1 cvv felimasn_0 imasng ax-mp elab2 felimasn_1 felimasn_2 felimasn_0 df-br bitri $.
$}
$( Membership in an image of a singleton.  (Contributed by Raph Levien,
       21-Oct-2006.) $)
${
	$d A y z $.
	$d B y z $.
	$d C y z $.
	ielimasng_0 $f set y $.
	ielimasng_1 $f set z $.
	felimasng_0 $f class A $.
	felimasng_1 $f class B $.
	felimasng_2 $f class C $.
	felimasng_3 $f class V $.
	felimasng_4 $f class W $.
	elimasng $p |- ( ( B e. V /\ C e. W ) -> ( C e. ( A " { B } ) <-> <. B , C >. e. A ) ) $= ielimasng_1 sup_set_class felimasng_0 ielimasng_0 sup_set_class csn cima wcel ielimasng_0 sup_set_class ielimasng_1 sup_set_class cop felimasng_0 wcel wb ielimasng_1 sup_set_class felimasng_0 felimasng_1 csn cima wcel felimasng_1 ielimasng_1 sup_set_class cop felimasng_0 wcel wb felimasng_2 felimasng_0 felimasng_1 csn cima wcel felimasng_1 felimasng_2 cop felimasng_0 wcel wb ielimasng_0 ielimasng_1 felimasng_1 felimasng_2 felimasng_3 felimasng_4 ielimasng_0 sup_set_class felimasng_1 wceq ielimasng_1 sup_set_class felimasng_0 ielimasng_0 sup_set_class csn cima wcel ielimasng_1 sup_set_class felimasng_0 felimasng_1 csn cima wcel ielimasng_0 sup_set_class ielimasng_1 sup_set_class cop felimasng_0 wcel felimasng_1 ielimasng_1 sup_set_class cop felimasng_0 wcel ielimasng_0 sup_set_class felimasng_1 wceq felimasng_0 ielimasng_0 sup_set_class csn cima felimasng_0 felimasng_1 csn cima ielimasng_1 sup_set_class ielimasng_0 sup_set_class felimasng_1 wceq ielimasng_0 sup_set_class csn felimasng_1 csn felimasng_0 ielimasng_0 sup_set_class felimasng_1 sneq imaeq2d eleq2d ielimasng_0 sup_set_class felimasng_1 wceq ielimasng_0 sup_set_class ielimasng_1 sup_set_class cop felimasng_1 ielimasng_1 sup_set_class cop felimasng_0 ielimasng_0 sup_set_class felimasng_1 ielimasng_1 sup_set_class opeq1 eleq1d bibi12d ielimasng_1 sup_set_class felimasng_2 wceq ielimasng_1 sup_set_class felimasng_0 felimasng_1 csn cima wcel felimasng_2 felimasng_0 felimasng_1 csn cima wcel felimasng_1 ielimasng_1 sup_set_class cop felimasng_0 wcel felimasng_1 felimasng_2 cop felimasng_0 wcel ielimasng_1 sup_set_class felimasng_2 felimasng_0 felimasng_1 csn cima eleq1 ielimasng_1 sup_set_class felimasng_2 wceq felimasng_1 ielimasng_1 sup_set_class cop felimasng_1 felimasng_2 cop felimasng_0 ielimasng_1 sup_set_class felimasng_2 felimasng_1 opeq2 eleq1d bibi12d felimasng_0 ielimasng_0 sup_set_class ielimasng_1 sup_set_class ielimasng_0 vex ielimasng_1 vex elimasn vtocl2g $.
$}
$( Membership in an image of a singleton.  (Contributed by NM,
     5-Aug-2010.) $)
${
	felimasni_0 $f class A $.
	felimasni_1 $f class B $.
	felimasni_2 $f class C $.
	elimasni $p |- ( C e. ( A " { B } ) -> B A C ) $= felimasni_1 cvv wcel felimasni_2 cvv wcel wa felimasni_2 felimasni_0 felimasni_1 csn cima wcel felimasni_1 felimasni_2 felimasni_0 wbr felimasni_2 felimasni_0 felimasni_1 csn cima wcel felimasni_1 cvv wcel felimasni_2 cvv wcel felimasni_1 cvv wcel felimasni_2 felimasni_0 felimasni_1 csn cima wcel felimasni_1 cvv wcel wn felimasni_2 felimasni_0 felimasni_1 csn cima wcel felimasni_2 c0 wcel felimasni_2 noel felimasni_1 cvv wcel wn felimasni_0 felimasni_1 csn cima c0 felimasni_2 felimasni_1 cvv wcel wn felimasni_0 felimasni_1 csn cima felimasni_0 c0 cima c0 felimasni_1 cvv wcel wn felimasni_1 csn c0 felimasni_0 felimasni_1 cvv wcel wn felimasni_1 csn c0 wceq felimasni_1 snprc biimpi imaeq2d felimasni_0 ima0 syl6eq eleq2d mtbiri con4i felimasni_2 felimasni_0 felimasni_1 csn cima elex jca felimasni_1 cvv wcel felimasni_2 cvv wcel wa felimasni_2 felimasni_0 felimasni_1 csn cima wcel felimasni_1 felimasni_2 felimasni_0 wbr felimasni_1 cvv wcel felimasni_2 cvv wcel wa felimasni_2 felimasni_0 felimasni_1 csn cima wcel felimasni_1 felimasni_2 cop felimasni_0 wcel felimasni_1 felimasni_2 felimasni_0 wbr felimasni_0 felimasni_1 felimasni_2 cvv cvv elimasng felimasni_1 felimasni_2 felimasni_0 df-br syl6bbr biimpd mpcom $.
$}
$( Two ways to express the class of unique-valued arguments of ` F ` ,
       which is the same as the domain of ` F ` whenever ` F ` is a function.
       The left-hand side of the equality is from Definition 10.2 of [Quine]
       p. 65.  Quine uses the notation "arg ` F ` " for this class (for which
       we have no separate notation).  Observe the resemblance to the
       alternative definition ~ dffv4 of function value, which is based on the
       idea in Quine's definition.  (Contributed by NM, 8-May-2005.) $)
${
	$d y F $.
	$d x y $.
	fargs_0 $f set x $.
	fargs_1 $f set y $.
	fargs_2 $f class F $.
	args $p |- { x | E. y ( F " { x } ) = { y } } = { x | E! y x F y } $= fargs_2 fargs_0 sup_set_class csn cima fargs_1 sup_set_class csn wceq fargs_1 wex fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 weu fargs_0 fargs_2 fargs_0 sup_set_class csn cima fargs_1 sup_set_class csn wceq fargs_1 wex fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 cab fargs_1 sup_set_class csn wceq fargs_1 wex fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 weu fargs_2 fargs_0 sup_set_class csn cima fargs_1 sup_set_class csn wceq fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 cab fargs_1 sup_set_class csn wceq fargs_1 fargs_2 fargs_0 sup_set_class csn cima fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 cab fargs_1 sup_set_class csn fargs_0 sup_set_class cvv wcel fargs_2 fargs_0 sup_set_class csn cima fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 cab wceq fargs_0 vex fargs_1 fargs_0 sup_set_class cvv fargs_2 imasng ax-mp eqeq1i exbii fargs_0 sup_set_class fargs_1 sup_set_class fargs_2 wbr fargs_1 euabsn bitr4i abbii $.
$}
$( Membership in an initial segment.  The idiom ` ( ``' A " { B } ) ` ,
       meaning ` { x | x A B } ` , is used to specify an initial segment in
       (for example) Definition 6.21 of [TakeutiZaring] p. 30.  (Contributed by
       NM, 28-Apr-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	feliniseg_0 $f class A $.
	feliniseg_1 $f class B $.
	feliniseg_2 $f class C $.
	feliniseg_3 $f class V $.
	eeliniseg_0 $e |- C e. _V $.
	eliniseg $p |- ( B e. V -> ( C e. ( `' A " { B } ) <-> C A B ) ) $= feliniseg_1 feliniseg_3 wcel feliniseg_2 cvv wcel feliniseg_2 feliniseg_0 ccnv feliniseg_1 csn cima wcel feliniseg_2 feliniseg_1 feliniseg_0 wbr wb eeliniseg_0 feliniseg_1 feliniseg_3 wcel feliniseg_2 cvv wcel wa feliniseg_2 feliniseg_0 ccnv feliniseg_1 csn cima wcel feliniseg_1 feliniseg_2 feliniseg_0 ccnv wbr feliniseg_2 feliniseg_1 feliniseg_0 wbr feliniseg_1 feliniseg_3 wcel feliniseg_2 cvv wcel wa feliniseg_2 feliniseg_0 ccnv feliniseg_1 csn cima wcel feliniseg_1 feliniseg_2 cop feliniseg_0 ccnv wcel feliniseg_1 feliniseg_2 feliniseg_0 ccnv wbr feliniseg_0 ccnv feliniseg_1 feliniseg_2 feliniseg_3 cvv elimasng feliniseg_1 feliniseg_2 feliniseg_0 ccnv df-br syl6bbr feliniseg_1 feliniseg_2 feliniseg_3 cvv feliniseg_0 brcnvg bitrd mpan2 $.
$}
$( Any set is equal to its preimage under the converse epsilon relation.
       (Contributed by Mario Carneiro, 9-Mar-2013.) $)
${
	$d A x $.
	iepini_0 $f set x $.
	fepini_0 $f class A $.
	eepini_0 $e |- A e. _V $.
	epini $p |- ( `' _E " { A } ) = A $= iepini_0 cep ccnv fepini_0 csn cima fepini_0 iepini_0 sup_set_class cep ccnv fepini_0 csn cima wcel iepini_0 sup_set_class fepini_0 cep wbr iepini_0 sup_set_class fepini_0 wcel fepini_0 cvv wcel iepini_0 sup_set_class cep ccnv fepini_0 csn cima wcel iepini_0 sup_set_class fepini_0 cep wbr wb eepini_0 cep fepini_0 iepini_0 sup_set_class cvv iepini_0 vex eliniseg ax-mp iepini_0 sup_set_class fepini_0 eepini_0 epelc bitri eqriv $.
$}
$( An idiom that signifies an initial segment of an ordering, used, for
       example, in Definition 6.21 of [TakeutiZaring] p. 30.  (Contributed by
       NM, 28-Apr-2004.) $)
${
	$d x A $.
	$d x B $.
	finiseg_0 $f set x $.
	finiseg_1 $f class A $.
	finiseg_2 $f class B $.
	finiseg_3 $f class V $.
	iniseg $p |- ( B e. V -> ( `' A " { B } ) = { x | x A B } ) $= finiseg_2 finiseg_3 wcel finiseg_2 cvv wcel finiseg_1 ccnv finiseg_2 csn cima finiseg_0 sup_set_class finiseg_2 finiseg_1 wbr finiseg_0 cab wceq finiseg_2 finiseg_3 elex finiseg_2 cvv wcel finiseg_0 sup_set_class finiseg_2 finiseg_1 wbr finiseg_0 finiseg_1 ccnv finiseg_2 csn cima finiseg_1 finiseg_2 finiseg_0 sup_set_class cvv finiseg_0 vex eliniseg abbi2dv syl $.
$}
$( Alternate definition of well-founded relation.  Definition 6.21 of
       [TakeutiZaring] p. 30.  (Contributed by NM, 23-Apr-2004.)  (Revised by
       Mario Carneiro, 23-Jun-2015.) $)
${
	$d x y z A $.
	$d x y z R $.
	idffr3_0 $f set z $.
	fdffr3_0 $f set x $.
	fdffr3_1 $f set y $.
	fdffr3_2 $f class A $.
	fdffr3_3 $f class R $.
	dffr3 $p |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) -> E. y e. x ( x i^i ( `' R " { y } ) ) = (/) ) ) $= fdffr3_2 fdffr3_3 wfr fdffr3_0 sup_set_class fdffr3_2 wss fdffr3_0 sup_set_class c0 wne wa idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class crab c0 wceq fdffr3_1 fdffr3_0 sup_set_class wrex wi fdffr3_0 wal fdffr3_0 sup_set_class fdffr3_2 wss fdffr3_0 sup_set_class c0 wne wa fdffr3_0 sup_set_class fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima cin c0 wceq fdffr3_1 fdffr3_0 sup_set_class wrex wi fdffr3_0 wal fdffr3_0 fdffr3_1 idffr3_0 fdffr3_2 fdffr3_3 dffr2 fdffr3_0 sup_set_class fdffr3_2 wss fdffr3_0 sup_set_class c0 wne wa fdffr3_0 sup_set_class fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima cin c0 wceq fdffr3_1 fdffr3_0 sup_set_class wrex wi fdffr3_0 sup_set_class fdffr3_2 wss fdffr3_0 sup_set_class c0 wne wa idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class crab c0 wceq fdffr3_1 fdffr3_0 sup_set_class wrex wi fdffr3_0 fdffr3_0 sup_set_class fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima cin c0 wceq fdffr3_1 fdffr3_0 sup_set_class wrex idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class crab c0 wceq fdffr3_1 fdffr3_0 sup_set_class wrex fdffr3_0 sup_set_class fdffr3_2 wss fdffr3_0 sup_set_class c0 wne wa fdffr3_0 sup_set_class fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima cin c0 wceq idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class crab c0 wceq fdffr3_1 fdffr3_0 sup_set_class fdffr3_0 sup_set_class fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima cin idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class crab c0 fdffr3_0 sup_set_class fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima cin fdffr3_0 sup_set_class idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 cab cin idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class crab fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 cab fdffr3_0 sup_set_class fdffr3_1 sup_set_class cvv wcel fdffr3_3 ccnv fdffr3_1 sup_set_class csn cima idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 cab wceq fdffr3_1 vex idffr3_0 fdffr3_3 fdffr3_1 sup_set_class cvv iniseg ax-mp ineq2i idffr3_0 sup_set_class fdffr3_1 sup_set_class fdffr3_3 wbr idffr3_0 fdffr3_0 sup_set_class dfrab3 eqtr4i eqeq1i rexbii imbi2i albii bitr4i $.
$}
$( Alternate definition of set-like relation.  (Contributed by Mario
       Carneiro, 23-Jun-2015.) $)
${
	$d x y A $.
	$d x y R $.
	idfse2_0 $f set y $.
	fdfse2_0 $f set x $.
	fdfse2_1 $f class A $.
	fdfse2_2 $f class R $.
	dfse2 $p |- ( R Se A <-> A. x e. A ( A i^i ( `' R " { x } ) ) e. _V ) $= fdfse2_1 fdfse2_2 wse idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 fdfse2_1 crab cvv wcel fdfse2_0 fdfse2_1 wral fdfse2_1 fdfse2_2 ccnv fdfse2_0 sup_set_class csn cima cin cvv wcel fdfse2_0 fdfse2_1 wral fdfse2_0 idfse2_0 fdfse2_1 fdfse2_2 df-se idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 fdfse2_1 crab cvv wcel fdfse2_1 fdfse2_2 ccnv fdfse2_0 sup_set_class csn cima cin cvv wcel fdfse2_0 fdfse2_1 idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 fdfse2_1 crab fdfse2_1 fdfse2_2 ccnv fdfse2_0 sup_set_class csn cima cin cvv idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 fdfse2_1 crab fdfse2_1 idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 cab cin fdfse2_1 fdfse2_2 ccnv fdfse2_0 sup_set_class csn cima cin idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 fdfse2_1 dfrab3 fdfse2_2 ccnv fdfse2_0 sup_set_class csn cima idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 cab fdfse2_1 fdfse2_0 sup_set_class cvv wcel fdfse2_2 ccnv fdfse2_0 sup_set_class csn cima idfse2_0 sup_set_class fdfse2_0 sup_set_class fdfse2_2 wbr idfse2_0 cab wceq fdfse2_0 vex idfse2_0 fdfse2_2 fdfse2_0 sup_set_class cvv iniseg ax-mp ineq2i eqtr4i eleq1i ralbii bitri $.
$}
$( Any set relation is set-like.  (Contributed by Mario Carneiro,
       22-Jun-2015.) $)
${
	$d x y A $.
	$d x y R $.
	$d x V $.
	iexse2_0 $f set x $.
	iexse2_1 $f set y $.
	fexse2_0 $f class A $.
	fexse2_1 $f class R $.
	fexse2_2 $f class V $.
	exse2 $p |- ( R e. V -> R Se A ) $= fexse2_1 fexse2_2 wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 crab cvv wcel iexse2_0 fexse2_0 wral fexse2_0 fexse2_1 wse fexse2_1 fexse2_2 wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 crab cvv wcel iexse2_0 fexse2_0 fexse2_1 fexse2_2 wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 crab fexse2_1 cdm wss fexse2_1 cdm cvv wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 crab cvv wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 crab iexse2_1 sup_set_class fexse2_0 wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr wa iexse2_1 cab fexse2_1 cdm iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 df-rab iexse2_1 sup_set_class fexse2_0 wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr wa iexse2_1 fexse2_1 cdm iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 sup_set_class fexse2_1 cdm wcel iexse2_1 sup_set_class fexse2_0 wcel iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 iexse2_1 vex iexse2_0 vex breldm adantl abssi eqsstri fexse2_1 fexse2_2 dmexg iexse2_1 sup_set_class iexse2_0 sup_set_class fexse2_1 wbr iexse2_1 fexse2_0 crab fexse2_1 cdm cvv ssexg sylancr ralrimivw iexse2_0 iexse2_1 fexse2_0 fexse2_1 df-se sylibr $.
$}
$( Subset theorem for image.  (Contributed by NM, 16-Mar-2004.) $)
${
	fimass1_0 $f class A $.
	fimass1_1 $f class B $.
	fimass1_2 $f class C $.
	imass1 $p |- ( A C_ B -> ( A " C ) C_ ( B " C ) ) $= fimass1_0 fimass1_1 wss fimass1_0 fimass1_2 cres crn fimass1_1 fimass1_2 cres crn fimass1_0 fimass1_2 cima fimass1_1 fimass1_2 cima fimass1_0 fimass1_1 wss fimass1_0 fimass1_2 cres fimass1_1 fimass1_2 cres wss fimass1_0 fimass1_2 cres crn fimass1_1 fimass1_2 cres crn wss fimass1_0 fimass1_1 fimass1_2 ssres fimass1_0 fimass1_2 cres fimass1_1 fimass1_2 cres rnss syl fimass1_0 fimass1_2 df-ima fimass1_1 fimass1_2 df-ima 3sstr4g $.
$}
$( Subset theorem for image.  Exercise 22(a) of [Enderton] p. 53.
     (Contributed by NM, 22-Mar-1998.) $)
${
	fimass2_0 $f class A $.
	fimass2_1 $f class B $.
	fimass2_2 $f class C $.
	imass2 $p |- ( A C_ B -> ( C " A ) C_ ( C " B ) ) $= fimass2_0 fimass2_1 wss fimass2_2 fimass2_0 cres crn fimass2_2 fimass2_1 cres crn fimass2_2 fimass2_0 cima fimass2_2 fimass2_1 cima fimass2_0 fimass2_1 wss fimass2_2 fimass2_0 cres fimass2_2 fimass2_1 cres wss fimass2_2 fimass2_0 cres crn fimass2_2 fimass2_1 cres crn wss fimass2_0 fimass2_1 fimass2_2 ssres2 fimass2_2 fimass2_0 cres fimass2_2 fimass2_1 cres rnss syl fimass2_2 fimass2_0 df-ima fimass2_2 fimass2_1 df-ima 3sstr4g $.
$}
$( The image of a singleton outside the domain is empty.  (Contributed by NM,
     22-May-1998.) $)
${
	fndmima_0 $f class A $.
	fndmima_1 $f class B $.
	ndmima $p |- ( -. A e. dom B -> ( B " { A } ) = (/) ) $= fndmima_0 fndmima_1 cdm wcel wn fndmima_1 fndmima_0 csn cima fndmima_1 fndmima_0 csn cres crn c0 fndmima_1 fndmima_0 csn df-ima fndmima_0 fndmima_1 cdm wcel wn fndmima_1 fndmima_0 csn cres cdm c0 wceq fndmima_1 fndmima_0 csn cres crn c0 wceq fndmima_0 fndmima_1 cdm wcel wn fndmima_1 fndmima_0 csn cres cdm fndmima_1 cdm fndmima_0 csn cin c0 fndmima_1 fndmima_0 csn cres cdm fndmima_0 csn fndmima_1 cdm cin fndmima_1 cdm fndmima_0 csn cin fndmima_1 fndmima_0 csn dmres fndmima_0 csn fndmima_1 cdm incom eqtri fndmima_1 cdm fndmima_0 csn cin c0 wceq fndmima_0 fndmima_1 cdm wcel wn fndmima_1 cdm fndmima_0 disjsn biimpri syl5eq fndmima_1 fndmima_0 csn cres dm0rn0 sylib syl5eq $.
$}
$( A converse is a relation.  Theorem 12 of [Suppes] p. 62.  (Contributed
       by NM, 29-Oct-1996.) $)
${
	$d x y A $.
	irelcnv_0 $f set x $.
	irelcnv_1 $f set y $.
	frelcnv_0 $f class A $.
	relcnv $p |- Rel `' A $= irelcnv_1 sup_set_class irelcnv_0 sup_set_class frelcnv_0 wbr irelcnv_0 irelcnv_1 frelcnv_0 ccnv irelcnv_0 irelcnv_1 frelcnv_0 df-cnv relopabi $.
$}
$( When ` R ` is a relation, the sethood assumptions on ~ brcnv can be
       omitted.  (Contributed by Mario Carneiro, 28-Apr-2015.) $)
${
	frelbrcnvg_0 $f class A $.
	frelbrcnvg_1 $f class B $.
	frelbrcnvg_2 $f class R $.
	relbrcnvg $p |- ( Rel R -> ( A `' R B <-> B R A ) ) $= frelbrcnvg_2 wrel frelbrcnvg_0 cvv wcel frelbrcnvg_1 cvv wcel wa frelbrcnvg_0 frelbrcnvg_1 frelbrcnvg_2 ccnv wbr frelbrcnvg_1 frelbrcnvg_0 frelbrcnvg_2 wbr frelbrcnvg_0 frelbrcnvg_1 frelbrcnvg_2 ccnv wbr frelbrcnvg_0 cvv wcel frelbrcnvg_1 cvv wcel wa wi frelbrcnvg_2 wrel frelbrcnvg_2 ccnv wrel frelbrcnvg_0 frelbrcnvg_1 frelbrcnvg_2 ccnv wbr frelbrcnvg_0 cvv wcel frelbrcnvg_1 cvv wcel wa frelbrcnvg_2 relcnv frelbrcnvg_0 frelbrcnvg_1 frelbrcnvg_2 ccnv brrelex12 mpan a1i frelbrcnvg_2 wrel frelbrcnvg_1 frelbrcnvg_0 frelbrcnvg_2 wbr frelbrcnvg_0 cvv wcel frelbrcnvg_1 cvv wcel wa frelbrcnvg_2 wrel frelbrcnvg_1 frelbrcnvg_0 frelbrcnvg_2 wbr wa frelbrcnvg_1 cvv wcel frelbrcnvg_0 cvv wcel frelbrcnvg_1 frelbrcnvg_0 frelbrcnvg_2 brrelex12 ancomd ex frelbrcnvg_0 cvv wcel frelbrcnvg_1 cvv wcel wa frelbrcnvg_0 frelbrcnvg_1 frelbrcnvg_2 ccnv wbr frelbrcnvg_1 frelbrcnvg_0 frelbrcnvg_2 wbr wb wi frelbrcnvg_2 wrel frelbrcnvg_0 frelbrcnvg_1 cvv cvv frelbrcnvg_2 brcnvg a1i pm5.21ndd $.
$}
$( Eliminate the class existence constraint in ~ eliniseg .  (Contributed
       by Mario Carneiro, 5-Dec-2014.)  (Revised by Mario Carneiro,
       17-Nov-2015.) $)
${
	feliniseg2_0 $f class A $.
	feliniseg2_1 $f class B $.
	feliniseg2_2 $f class C $.
	eliniseg2 $p |- ( Rel A -> ( C e. ( `' A " { B } ) <-> C A B ) ) $= feliniseg2_2 feliniseg2_0 ccnv feliniseg2_1 csn cima wcel feliniseg2_1 feliniseg2_2 feliniseg2_0 ccnv wbr feliniseg2_0 wrel feliniseg2_2 feliniseg2_1 feliniseg2_0 wbr feliniseg2_0 ccnv wrel feliniseg2_2 feliniseg2_0 ccnv feliniseg2_1 csn cima wcel feliniseg2_1 feliniseg2_2 feliniseg2_0 ccnv wbr wb feliniseg2_0 relcnv feliniseg2_1 feliniseg2_2 feliniseg2_0 ccnv elrelimasn ax-mp feliniseg2_1 feliniseg2_2 feliniseg2_0 relbrcnvg syl5bb $.
$}
$( When ` R ` is a relation, the sethood assumptions on ~ brcnv can be
       omitted.  (Contributed by Mario Carneiro, 28-Apr-2015.) $)
${
	frelbrcnv_0 $f class A $.
	frelbrcnv_1 $f class B $.
	frelbrcnv_2 $f class R $.
	erelbrcnv_0 $e |- Rel R $.
	relbrcnv $p |- ( A `' R B <-> B R A ) $= frelbrcnv_2 wrel frelbrcnv_0 frelbrcnv_1 frelbrcnv_2 ccnv wbr frelbrcnv_1 frelbrcnv_0 frelbrcnv_2 wbr wb erelbrcnv_0 frelbrcnv_0 frelbrcnv_1 frelbrcnv_2 relbrcnvg ax-mp $.
$}
$( Two ways of saying a relation is transitive.  Definition of transitivity
       in [Schechter] p. 51.  (Contributed by NM, 27-Dec-1996.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	$d x y $.
	$d x y z R $.
	fcotr_0 $f set x $.
	fcotr_1 $f set y $.
	fcotr_2 $f set z $.
	fcotr_3 $f class R $.
	cotr $p |- ( ( R o. R ) C_ R <-> A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) ) $= fcotr_3 fcotr_3 ccom fcotr_3 wss fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel wi fcotr_2 wal fcotr_0 wal fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_2 wal fcotr_1 wal fcotr_0 wal fcotr_3 fcotr_3 ccom wrel fcotr_3 fcotr_3 ccom fcotr_3 wss fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel wi fcotr_2 wal fcotr_0 wal wb fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_1 wex fcotr_0 fcotr_2 fcotr_3 fcotr_3 ccom fcotr_0 fcotr_2 fcotr_1 fcotr_3 fcotr_3 df-co relopabi fcotr_0 fcotr_2 fcotr_3 fcotr_3 ccom fcotr_3 ssrel ax-mp fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel wi fcotr_2 wal fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_2 wal fcotr_1 wal fcotr_0 fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel wi fcotr_2 wal fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_1 wal fcotr_2 wal fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_2 wal fcotr_1 wal fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel wi fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_1 wal fcotr_2 fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel wi fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_1 wex fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_1 wal fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 fcotr_3 ccom wcel fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_1 wex fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr fcotr_1 fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 fcotr_3 fcotr_0 vex fcotr_2 vex opelco fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr fcotr_0 sup_set_class fcotr_2 sup_set_class cop fcotr_3 wcel fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 df-br bicomi imbi12i fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr fcotr_1 19.23v bitr4i albii fcotr_0 sup_set_class fcotr_1 sup_set_class fcotr_3 wbr fcotr_1 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wa fcotr_0 sup_set_class fcotr_2 sup_set_class fcotr_3 wbr wi fcotr_2 fcotr_1 alcom bitri albii bitri $.
$}
$( Two ways to state a relation is reflexive.  Adapted from Tarski.
       (Contributed by FL, 15-Jan-2012.)  (Revised by NM, 30-Mar-2016.) $)
${
	$d x y z A $.
	$d x y z $.
	$d x y z R $.
	$d x y z $.
	iissref_0 $f set y $.
	iissref_1 $f set z $.
	fissref_0 $f set x $.
	fissref_1 $f class A $.
	fissref_2 $f class R $.
	issref $p |- ( ( _I |` A ) C_ R <-> A. x e. A x R x ) $= fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 wbr fissref_0 fissref_1 wral fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 wbr wi fissref_0 wal fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 wal cid fissref_1 cres fissref_2 wss fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 wbr fissref_0 fissref_1 df-ral fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 wbr wi fissref_0 fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 wbr fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_1 wcel wb fissref_0 vex fissref_0 sup_set_class fissref_1 cvv opelresi ax-mp fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 wbr fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel fissref_0 sup_set_class fissref_0 sup_set_class fissref_2 df-br bicomi imbi12i albii fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 wal cid fissref_1 cres fissref_2 wss fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 wal iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 wal cid fissref_1 cres fissref_2 wss fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 wal fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 cvv wral iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 wal fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 cvv wral fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 wal fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv ralidm fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 ralv bitri fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 cvv wral iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 cvv cvv cxp wral iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 wal fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 cvv wral fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv wral fissref_0 cvv wral iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 cvv cvv cxp wral fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv wral fissref_0 cvv fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv wral fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi wi fissref_0 wal fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv wral fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cvv df-ral fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv wral fissref_0 fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv wral wi fissref_0 vex fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv wral fissref_0 sup_set_class cvv wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi pm2.27 fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_1 cvv iissref_1 sup_set_class cvv wcel fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel iissref_1 sup_set_class cvv wcel fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop cid wcel fissref_0 sup_set_class fissref_1 wcel wa fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cid fissref_1 cvv opelresg fissref_0 sup_set_class iissref_1 sup_set_class cop cid wcel fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop cid wcel fissref_0 sup_set_class iissref_1 sup_set_class cid wbr fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class iissref_1 sup_set_class cid df-br fissref_0 sup_set_class iissref_1 sup_set_class cid wbr fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class iissref_1 sup_set_class iissref_1 vex ideq fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_1 wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi wi fissref_0 sup_set_class fissref_1 fissref_1 opelresi fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel pm2.27 fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel fissref_0 sup_set_class iissref_1 sup_set_class wceq fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 fissref_0 sup_set_class iissref_1 sup_set_class fissref_0 sup_set_class opeq2 eleq1d biimpcd syl6 syl6bir pm2.43i com3r sylbi sylbir imp syl6bi com3r ralrimiv syl6 ax-mp sps sylbi ralimi iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel wi iissref_0 fissref_0 iissref_1 cvv cvv iissref_0 sup_set_class fissref_0 sup_set_class iissref_1 sup_set_class cop wceq iissref_0 sup_set_class cid fissref_1 cres wcel fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 wcel iissref_0 sup_set_class fissref_0 sup_set_class iissref_1 sup_set_class cop cid fissref_1 cres eleq1 iissref_0 sup_set_class fissref_0 sup_set_class iissref_1 sup_set_class cop fissref_2 eleq1 imbi12d ralxp sylibr iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 cvv cvv cxp wral iissref_0 sup_set_class cvv cvv cxp wcel iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi wi iissref_0 wal iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 wal iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 cvv cvv cxp df-ral iissref_0 sup_set_class cvv cvv cxp wcel iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi wi iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi iissref_0 iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class cvv cvv cxp wcel iissref_0 sup_set_class cid fissref_1 cres wcel wa iissref_0 sup_set_class cvv cvv cxp wcel iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel wi wi iissref_0 sup_set_class fissref_2 wcel iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class cvv cvv cxp wcel cid fissref_1 cres cvv cvv cxp iissref_0 sup_set_class cid fissref_1 cres wrel cid fissref_1 cres cvv cvv cxp wss cid fissref_1 relres cid fissref_1 cres df-rel mpbi sseli ancri iissref_0 sup_set_class cvv cvv cxp wcel iissref_0 sup_set_class cid fissref_1 cres wcel iissref_0 sup_set_class fissref_2 wcel pm3.31 syl5 alimi sylbi syl sylbir iissref_0 cid fissref_1 cres fissref_2 dfss2 sylibr cid fissref_1 cres fissref_2 wss fissref_0 sup_set_class fissref_0 sup_set_class cop cid fissref_1 cres wcel fissref_0 sup_set_class fissref_0 sup_set_class cop fissref_2 wcel wi fissref_0 cid fissref_1 cres fissref_2 fissref_0 sup_set_class fissref_0 sup_set_class cop ssel alrimiv impbii 3bitr2ri $.
$}
$( Two ways of saying a relation is symmetric.  Similar to definition of
       symmetry in [Schechter] p. 51.  (Contributed by NM, 28-Dec-1996.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	$d x y $.
	$d x y R $.
	$d x y $.
	fcnvsym_0 $f set x $.
	fcnvsym_1 $f set y $.
	fcnvsym_2 $f class R $.
	cnvsym $p |- ( `' R C_ R <-> A. x A. y ( x R y -> y R x ) ) $= fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 wcel wi fcnvsym_0 wal fcnvsym_1 wal fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 wcel wi fcnvsym_1 wal fcnvsym_0 wal fcnvsym_2 ccnv fcnvsym_2 wss fcnvsym_0 sup_set_class fcnvsym_1 sup_set_class fcnvsym_2 wbr fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 wbr wi fcnvsym_1 wal fcnvsym_0 wal fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 wcel wi fcnvsym_1 fcnvsym_0 alcom fcnvsym_2 ccnv wrel fcnvsym_2 ccnv fcnvsym_2 wss fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 wcel wi fcnvsym_0 wal fcnvsym_1 wal wb fcnvsym_2 relcnv fcnvsym_1 fcnvsym_0 fcnvsym_2 ccnv fcnvsym_2 ssrel ax-mp fcnvsym_0 sup_set_class fcnvsym_1 sup_set_class fcnvsym_2 wbr fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 wbr wi fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 wcel wi fcnvsym_0 fcnvsym_1 fcnvsym_0 sup_set_class fcnvsym_1 sup_set_class fcnvsym_2 wbr fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 wbr fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 wcel fcnvsym_0 sup_set_class fcnvsym_1 sup_set_class fcnvsym_2 wbr fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 ccnv wbr fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class cop fcnvsym_2 ccnv wcel fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 fcnvsym_1 vex fcnvsym_0 vex brcnv fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 ccnv df-br bitr3i fcnvsym_1 sup_set_class fcnvsym_0 sup_set_class fcnvsym_2 df-br imbi12i 2albii 3bitr4i $.
$}
$( Two ways of saying a relation is antisymmetric.  Definition of
       antisymmetry in [Schechter] p. 51.  (Contributed by NM, 9-Sep-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	$d x y $.
	$d x y R $.
	$d x y $.
	fintasym_0 $f set x $.
	fintasym_1 $f set y $.
	fintasym_2 $f class R $.
	intasym $p |- ( ( R i^i `' R ) C_ _I <-> A. x A. y ( ( x R y /\ y R x ) -> x = y ) ) $= fintasym_2 fintasym_2 ccnv cin cid wss fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 fintasym_2 ccnv cin wcel fintasym_0 sup_set_class fintasym_1 sup_set_class cop cid wcel wi fintasym_1 wal fintasym_0 wal fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 wbr fintasym_1 sup_set_class fintasym_0 sup_set_class fintasym_2 wbr wa fintasym_0 sup_set_class fintasym_1 sup_set_class wceq wi fintasym_1 wal fintasym_0 wal fintasym_2 ccnv wrel fintasym_2 fintasym_2 ccnv cin wrel fintasym_2 fintasym_2 ccnv cin cid wss fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 fintasym_2 ccnv cin wcel fintasym_0 sup_set_class fintasym_1 sup_set_class cop cid wcel wi fintasym_1 wal fintasym_0 wal wb fintasym_2 relcnv fintasym_2 fintasym_2 ccnv relin2 fintasym_0 fintasym_1 fintasym_2 fintasym_2 ccnv cin cid ssrel mp2b fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 fintasym_2 ccnv cin wcel fintasym_0 sup_set_class fintasym_1 sup_set_class cop cid wcel wi fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 wbr fintasym_1 sup_set_class fintasym_0 sup_set_class fintasym_2 wbr wa fintasym_0 sup_set_class fintasym_1 sup_set_class wceq wi fintasym_0 fintasym_1 fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 fintasym_2 ccnv cin wcel fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 wbr fintasym_1 sup_set_class fintasym_0 sup_set_class fintasym_2 wbr wa fintasym_0 sup_set_class fintasym_1 sup_set_class cop cid wcel fintasym_0 sup_set_class fintasym_1 sup_set_class wceq fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 fintasym_2 ccnv cin wcel fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 wcel fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 ccnv wcel wa fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 wbr fintasym_1 sup_set_class fintasym_0 sup_set_class fintasym_2 wbr wa fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 fintasym_2 ccnv elin fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 wbr fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 wcel fintasym_1 sup_set_class fintasym_0 sup_set_class fintasym_2 wbr fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 ccnv wcel fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 df-br fintasym_1 sup_set_class fintasym_0 sup_set_class fintasym_2 wbr fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 ccnv wbr fintasym_0 sup_set_class fintasym_1 sup_set_class cop fintasym_2 ccnv wcel fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 fintasym_0 vex fintasym_1 vex brcnv fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_2 ccnv df-br bitr3i anbi12i bitr4i fintasym_0 sup_set_class fintasym_1 sup_set_class cop cid wcel fintasym_0 sup_set_class fintasym_1 sup_set_class cid wbr fintasym_0 sup_set_class fintasym_1 sup_set_class wceq fintasym_0 sup_set_class fintasym_1 sup_set_class cid df-br fintasym_0 sup_set_class fintasym_1 sup_set_class fintasym_1 vex ideq bitr3i imbi12i 2albii bitri $.
$}
$( Two ways of saying a relation is antisymmetric and reflexive.
       ` U. U. R ` is the field of a relation by ~ relfld .  (Contributed by
       NM, 6-May-2008.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	$d x y $.
	$d x y R $.
	$d x y $.
	fasymref_0 $f set x $.
	fasymref_1 $f set y $.
	fasymref_2 $f class R $.
	asymref $p |- ( ( R i^i `' R ) = ( _I |` U. U. R ) <-> A. x e. U. U. R A. y ( ( x R y /\ y R x ) <-> x = y ) ) $= fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel wb fasymref_1 wal fasymref_0 wal fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb fasymref_1 wal wi fasymref_0 wal fasymref_2 fasymref_2 ccnv cin cid fasymref_2 cuni cuni cres wceq fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb fasymref_1 wal fasymref_0 fasymref_2 cuni cuni wral fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel wb fasymref_1 wal fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb fasymref_1 wal wi fasymref_0 fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel wb fasymref_1 wal fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb wi fasymref_1 wal fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb fasymref_1 wal wi fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel wb fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb wi fasymref_1 fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wa wb fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa wa fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wa wb fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel wb fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb wi fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa wa fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wa fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_1 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 wcel fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_1 sup_set_class fasymref_2 cuni cuni wcel wa fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 df-br fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 fasymref_0 vex fasymref_1 vex opeluu sylbi simpld adantr pm4.71ri bibi1i fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wa fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 ccnv wcel wa fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv elin fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 wcel fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 ccnv wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 df-br fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 ccnv wbr fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 ccnv wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 fasymref_0 vex fasymref_1 vex brcnv fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 ccnv df-br bitr3i anbi12i bitr4i fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid wcel fasymref_0 sup_set_class fasymref_2 cuni cuni wcel wa fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wa fasymref_0 sup_set_class fasymref_1 sup_set_class cid fasymref_2 cuni cuni fasymref_1 vex opelres fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid wcel fasymref_0 sup_set_class fasymref_1 sup_set_class wceq fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cid wbr fasymref_0 sup_set_class fasymref_1 sup_set_class wceq fasymref_0 sup_set_class fasymref_1 sup_set_class cid df-br fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_1 vex ideq bitr3i anbi2ci bitri bibi12i fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq pm5.32 3bitr4i albii fasymref_0 sup_set_class fasymref_2 cuni cuni wcel fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb fasymref_1 19.21v bitri albii fasymref_2 fasymref_2 ccnv cin wrel cid fasymref_2 cuni cuni cres wrel fasymref_2 fasymref_2 ccnv cin cid fasymref_2 cuni cuni cres wceq fasymref_0 sup_set_class fasymref_1 sup_set_class cop fasymref_2 fasymref_2 ccnv cin wcel fasymref_0 sup_set_class fasymref_1 sup_set_class cop cid fasymref_2 cuni cuni cres wcel wb fasymref_1 wal fasymref_0 wal wb fasymref_2 ccnv wrel fasymref_2 fasymref_2 ccnv cin wrel fasymref_2 relcnv fasymref_2 fasymref_2 ccnv relin2 ax-mp cid fasymref_2 cuni cuni relres fasymref_0 fasymref_1 fasymref_2 fasymref_2 ccnv cin cid fasymref_2 cuni cuni cres eqrel mp2an fasymref_0 sup_set_class fasymref_1 sup_set_class fasymref_2 wbr fasymref_1 sup_set_class fasymref_0 sup_set_class fasymref_2 wbr wa fasymref_0 sup_set_class fasymref_1 sup_set_class wceq wb fasymref_1 wal fasymref_0 fasymref_2 cuni cuni df-ral 3bitr4i $.
$}
$( Two ways of saying a relation is antisymmetric and reflexive.
       (Contributed by NM, 6-May-2008.)  (Proof shortened by Mario Carneiro,
       4-Dec-2016.) $)
${
	$d x y $.
	$d x y $.
	$d x y R $.
	$d x y $.
	fasymref2_0 $f set x $.
	fasymref2_1 $f set y $.
	fasymref2_2 $f class R $.
	asymref2 $p |- ( ( R i^i `' R ) = ( _I |` U. U. R ) <-> ( A. x e. U. U. R x R x /\ A. x A. y ( ( x R y /\ y R x ) -> x = y ) ) ) $= fasymref2_2 fasymref2_2 ccnv cin cid fasymref2_2 cuni cuni cres wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wb fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal wa fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 wal wa fasymref2_0 fasymref2_1 fasymref2_2 asymref fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wb fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal wa fasymref2_0 fasymref2_2 cuni cuni fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_1 albiim ralbii fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal wa fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral wa fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 wal wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni r19.26 fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral ancom fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 fasymref2_2 cuni cuni fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_1 sup_set_class fasymref2_0 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 sup_set_class fasymref2_0 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa wi fasymref2_1 fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_1 sup_set_class fasymref2_0 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 fasymref2_1 equcom imbi1i albii fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_1 fasymref2_0 fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_1 nfv fasymref2_1 sup_set_class fasymref2_0 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 breq2 fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 breq1 anbi12d fasymref2_0 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr anidm syl6bb equsal bitri ralbii fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni wral fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal wi fasymref2_0 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_2 cuni cuni df-ral fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal wi fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal wi fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel wn fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel wn fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_0 sup_set_class fasymref2_1 sup_set_class cop fasymref2_2 wcel fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 df-br fasymref2_0 sup_set_class fasymref2_1 sup_set_class cop fasymref2_2 wcel fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_1 sup_set_class fasymref2_2 cuni cuni wcel fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 fasymref2_0 vex fasymref2_1 vex opeluu simpld sylbi adantr pm2.24d com12 alrimiv fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal id ja fasymref2_0 sup_set_class fasymref2_1 sup_set_class fasymref2_2 wbr fasymref2_1 sup_set_class fasymref2_0 sup_set_class fasymref2_2 wbr wa fasymref2_0 sup_set_class fasymref2_1 sup_set_class wceq wi fasymref2_1 wal fasymref2_0 sup_set_class fasymref2_2 cuni cuni wcel ax-1 impbii albii bitri anbi12i 3bitri 3bitri $.
$}
$( Two ways of saying a relation is irreflexive.  Definition of
       irreflexivity in [Schechter] p. 51.  (Contributed by NM, 9-Sep-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	$d x y $.
	$d x y R $.
	$d x y $.
	iintirr_0 $f set y $.
	fintirr_0 $f set x $.
	fintirr_1 $f class R $.
	intirr $p |- ( ( R i^i _I ) = (/) <-> A. x -. x R x ) $= fintirr_1 cid cin c0 wceq fintirr_0 sup_set_class iintirr_0 sup_set_class cop cid wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel wi iintirr_0 wal fintirr_0 wal iintirr_0 sup_set_class fintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr wn wi iintirr_0 wal fintirr_0 wal fintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_1 wbr wn fintirr_0 wal fintirr_1 cid cin c0 wceq cid fintirr_1 cin c0 wceq cid cvv fintirr_1 cdif wss fintirr_0 sup_set_class iintirr_0 sup_set_class cop cid wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel wi iintirr_0 wal fintirr_0 wal fintirr_1 cid cin cid fintirr_1 cin c0 fintirr_1 cid incom eqeq1i cid fintirr_1 disj2 cid wrel cid cvv fintirr_1 cdif wss fintirr_0 sup_set_class iintirr_0 sup_set_class cop cid wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel wi iintirr_0 wal fintirr_0 wal wb reli fintirr_0 iintirr_0 cid cvv fintirr_1 cdif ssrel ax-mp 3bitri iintirr_0 sup_set_class fintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr wn wi fintirr_0 sup_set_class iintirr_0 sup_set_class cop cid wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel wi fintirr_0 iintirr_0 iintirr_0 sup_set_class fintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class cop cid wcel fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr wn fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel iintirr_0 sup_set_class fintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class cid wbr fintirr_0 sup_set_class iintirr_0 sup_set_class cop cid wcel iintirr_0 sup_set_class fintirr_0 sup_set_class eqcom fintirr_0 sup_set_class iintirr_0 sup_set_class iintirr_0 vex ideq fintirr_0 sup_set_class iintirr_0 sup_set_class cid df-br 3bitr2i fintirr_0 sup_set_class iintirr_0 sup_set_class cop fintirr_1 wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr fintirr_0 sup_set_class iintirr_0 sup_set_class cop fintirr_1 wcel wn fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop fintirr_1 wcel wn wa fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 cdif wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv wcel fintirr_0 sup_set_class iintirr_0 sup_set_class cop fintirr_1 wcel wn fintirr_0 sup_set_class iintirr_0 sup_set_class opex biantrur fintirr_0 sup_set_class iintirr_0 sup_set_class cop cvv fintirr_1 eldif bitr4i fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 df-br xchnxbir imbi12i 2albii iintirr_0 sup_set_class fintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr wn wi iintirr_0 wal fintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_1 wbr wn fintirr_0 fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr wn fintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_1 wbr wn iintirr_0 fintirr_0 fintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_1 wbr wn iintirr_0 nfv iintirr_0 sup_set_class fintirr_0 sup_set_class wceq fintirr_0 sup_set_class iintirr_0 sup_set_class fintirr_1 wbr fintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_1 wbr iintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_0 sup_set_class fintirr_1 breq2 notbid equsal albii 3bitr2i $.
$}
$( Two ways of saying that two elements have an upper bound.  (Contributed
       by Mario Carneiro, 3-Nov-2015.) $)
${
	$d z A $.
	$d z B $.
	$d z R $.
	$d z V $.
	$d z W $.
	fbrcodir_0 $f set z $.
	fbrcodir_1 $f class A $.
	fbrcodir_2 $f class B $.
	fbrcodir_3 $f class R $.
	fbrcodir_4 $f class V $.
	fbrcodir_5 $f class W $.
	brcodir $p |- ( ( A e. V /\ B e. W ) -> ( A ( `' R o. R ) B <-> E. z ( A R z /\ B R z ) ) ) $= fbrcodir_1 fbrcodir_4 wcel fbrcodir_2 fbrcodir_5 wcel wa fbrcodir_1 fbrcodir_2 fbrcodir_3 ccnv fbrcodir_3 ccom wbr fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_0 sup_set_class fbrcodir_2 fbrcodir_3 ccnv wbr wa fbrcodir_0 wex fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_2 fbrcodir_0 sup_set_class fbrcodir_3 wbr wa fbrcodir_0 wex fbrcodir_0 fbrcodir_1 fbrcodir_2 fbrcodir_3 ccnv fbrcodir_3 fbrcodir_4 fbrcodir_5 brcog fbrcodir_1 fbrcodir_4 wcel fbrcodir_2 fbrcodir_5 wcel wa fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_0 sup_set_class fbrcodir_2 fbrcodir_3 ccnv wbr wa fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_2 fbrcodir_0 sup_set_class fbrcodir_3 wbr wa fbrcodir_0 fbrcodir_2 fbrcodir_5 wcel fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_0 sup_set_class fbrcodir_2 fbrcodir_3 ccnv wbr wa fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_2 fbrcodir_0 sup_set_class fbrcodir_3 wbr wa wb fbrcodir_1 fbrcodir_4 wcel fbrcodir_2 fbrcodir_5 wcel fbrcodir_0 sup_set_class fbrcodir_2 fbrcodir_3 ccnv wbr fbrcodir_2 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_1 fbrcodir_0 sup_set_class fbrcodir_3 wbr fbrcodir_0 sup_set_class cvv wcel fbrcodir_2 fbrcodir_5 wcel fbrcodir_0 sup_set_class fbrcodir_2 fbrcodir_3 ccnv wbr fbrcodir_2 fbrcodir_0 sup_set_class fbrcodir_3 wbr wb fbrcodir_0 vex fbrcodir_0 sup_set_class fbrcodir_2 cvv fbrcodir_5 fbrcodir_3 brcnvg mpan anbi2d adantl exbidv bitrd $.
$}
$( Two ways of saying a relation is directed.  (Contributed by Mario
       Carneiro, 22-Nov-2013.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z R $.
	$d x y z $.
	fcodir_0 $f set x $.
	fcodir_1 $f set y $.
	fcodir_2 $f set z $.
	fcodir_3 $f class A $.
	fcodir_4 $f class B $.
	fcodir_5 $f class R $.
	codir $p |- ( ( A X. B ) C_ ( `' R o. R ) <-> A. x e. A A. y e. B E. z ( x R z /\ y R z ) ) $= fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_3 fcodir_4 cxp wcel fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_5 ccnv fcodir_5 ccom wcel wi fcodir_1 wal fcodir_0 wal fcodir_0 sup_set_class fcodir_3 wcel fcodir_1 sup_set_class fcodir_4 wcel wa fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex wi fcodir_1 wal fcodir_0 wal fcodir_3 fcodir_4 cxp fcodir_5 ccnv fcodir_5 ccom wss fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex fcodir_1 fcodir_4 wral fcodir_0 fcodir_3 wral fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_3 fcodir_4 cxp wcel fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_5 ccnv fcodir_5 ccom wcel wi fcodir_0 sup_set_class fcodir_3 wcel fcodir_1 sup_set_class fcodir_4 wcel wa fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex wi fcodir_0 fcodir_1 fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_3 fcodir_4 cxp wcel fcodir_0 sup_set_class fcodir_3 wcel fcodir_1 sup_set_class fcodir_4 wcel wa fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_5 ccnv fcodir_5 ccom wcel fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex fcodir_0 sup_set_class fcodir_1 sup_set_class fcodir_3 fcodir_4 opelxp fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_5 ccnv fcodir_5 ccom wcel fcodir_0 sup_set_class fcodir_1 sup_set_class fcodir_5 ccnv fcodir_5 ccom wbr fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex fcodir_0 sup_set_class fcodir_1 sup_set_class fcodir_5 ccnv fcodir_5 ccom df-br fcodir_0 sup_set_class cvv wcel fcodir_1 sup_set_class cvv wcel fcodir_0 sup_set_class fcodir_1 sup_set_class fcodir_5 ccnv fcodir_5 ccom wbr fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex wb fcodir_0 vex fcodir_1 vex fcodir_2 fcodir_0 sup_set_class fcodir_1 sup_set_class fcodir_5 cvv cvv brcodir mp2an bitr3i imbi12i 2albii fcodir_3 fcodir_4 cxp wrel fcodir_3 fcodir_4 cxp fcodir_5 ccnv fcodir_5 ccom wss fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_3 fcodir_4 cxp wcel fcodir_0 sup_set_class fcodir_1 sup_set_class cop fcodir_5 ccnv fcodir_5 ccom wcel wi fcodir_1 wal fcodir_0 wal wb fcodir_3 fcodir_4 relxp fcodir_0 fcodir_1 fcodir_3 fcodir_4 cxp fcodir_5 ccnv fcodir_5 ccom ssrel ax-mp fcodir_0 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr fcodir_1 sup_set_class fcodir_2 sup_set_class fcodir_5 wbr wa fcodir_2 wex fcodir_0 fcodir_1 fcodir_3 fcodir_4 r2al 3bitr4i $.
$}
$( A quantifier-free way of expressing the total order predicate.
       (Contributed by Mario Carneiro, 22-Nov-2013.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	$d x y $.
	fqfto_0 $f set x $.
	fqfto_1 $f set y $.
	fqfto_2 $f class A $.
	fqfto_3 $f class B $.
	fqfto_4 $f class R $.
	qfto $p |- ( ( A X. B ) C_ ( R u. `' R ) <-> A. x e. A A. y e. B ( x R y \/ y R x ) ) $= fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_2 fqfto_3 cxp wcel fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_4 fqfto_4 ccnv cun wcel wi fqfto_1 wal fqfto_0 wal fqfto_0 sup_set_class fqfto_2 wcel fqfto_1 sup_set_class fqfto_3 wcel wa fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr wo wi fqfto_1 wal fqfto_0 wal fqfto_2 fqfto_3 cxp fqfto_4 fqfto_4 ccnv cun wss fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr wo fqfto_1 fqfto_3 wral fqfto_0 fqfto_2 wral fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_2 fqfto_3 cxp wcel fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_4 fqfto_4 ccnv cun wcel wi fqfto_0 sup_set_class fqfto_2 wcel fqfto_1 sup_set_class fqfto_3 wcel wa fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr wo wi fqfto_0 fqfto_1 fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_2 fqfto_3 cxp wcel fqfto_0 sup_set_class fqfto_2 wcel fqfto_1 sup_set_class fqfto_3 wcel wa fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_4 fqfto_4 ccnv cun wcel fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr wo fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_2 fqfto_3 opelxp fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 fqfto_4 ccnv cun wbr fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 ccnv wbr wo fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_4 fqfto_4 ccnv cun wcel fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr wo fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 fqfto_4 ccnv brun fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 fqfto_4 ccnv cun df-br fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 ccnv wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 fqfto_0 vex fqfto_1 vex brcnv orbi2i 3bitr3i imbi12i 2albii fqfto_2 fqfto_3 cxp wrel fqfto_2 fqfto_3 cxp fqfto_4 fqfto_4 ccnv cun wss fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_2 fqfto_3 cxp wcel fqfto_0 sup_set_class fqfto_1 sup_set_class cop fqfto_4 fqfto_4 ccnv cun wcel wi fqfto_1 wal fqfto_0 wal wb fqfto_2 fqfto_3 relxp fqfto_0 fqfto_1 fqfto_2 fqfto_3 cxp fqfto_4 fqfto_4 ccnv cun ssrel ax-mp fqfto_0 sup_set_class fqfto_1 sup_set_class fqfto_4 wbr fqfto_1 sup_set_class fqfto_0 sup_set_class fqfto_4 wbr wo fqfto_0 fqfto_1 fqfto_2 fqfto_3 r2al 3bitr4i $.
$}
$( A square cross product ` ( A X. A ) ` is a transitive relation.
       (Contributed by FL, 31-Jul-2009.) $)
${
	$d x y z A $.
	$d x y z $.
	$d x y z $.
	$d x y z $.
	ixpidtr_0 $f set x $.
	ixpidtr_1 $f set y $.
	ixpidtr_2 $f set z $.
	fxpidtr_0 $f class A $.
	xpidtr $p |- ( ( A X. A ) o. ( A X. A ) ) C_ ( A X. A ) $= fxpidtr_0 fxpidtr_0 cxp fxpidtr_0 fxpidtr_0 cxp ccom fxpidtr_0 fxpidtr_0 cxp wss ixpidtr_0 sup_set_class ixpidtr_1 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wa ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_2 wal ixpidtr_1 wal ixpidtr_0 wal ixpidtr_0 sup_set_class ixpidtr_1 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wa ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_2 wal ixpidtr_0 ixpidtr_1 ixpidtr_0 sup_set_class ixpidtr_1 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wa ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_2 ixpidtr_0 sup_set_class ixpidtr_1 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class ixpidtr_1 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class fxpidtr_0 wcel ixpidtr_1 sup_set_class fxpidtr_0 wcel wa ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_0 sup_set_class ixpidtr_1 sup_set_class fxpidtr_0 fxpidtr_0 brxp ixpidtr_0 sup_set_class fxpidtr_0 wcel ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_1 sup_set_class fxpidtr_0 wcel ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class fxpidtr_0 wcel ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_1 sup_set_class fxpidtr_0 wcel ixpidtr_2 sup_set_class fxpidtr_0 wcel wa ixpidtr_0 sup_set_class fxpidtr_0 wcel ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_1 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 brxp ixpidtr_2 sup_set_class fxpidtr_0 wcel ixpidtr_0 sup_set_class fxpidtr_0 wcel ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr wi ixpidtr_1 sup_set_class fxpidtr_0 wcel ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 cxp wbr ixpidtr_0 sup_set_class fxpidtr_0 wcel ixpidtr_2 sup_set_class fxpidtr_0 wcel ixpidtr_0 sup_set_class ixpidtr_2 sup_set_class fxpidtr_0 fxpidtr_0 brxp simplbi2com adantl sylbi com12 adantr sylbi imp ax-gen gen2 ixpidtr_0 ixpidtr_1 ixpidtr_2 fxpidtr_0 fxpidtr_0 cxp cotr mpbir $.
$}
$( The intersection of two transitive classes is transitive.  (Contributed
       by FL, 31-Jul-2009.) $)
${
	$d x y z $.
	$d x y z $.
	$d x y z R $.
	$d x y z S $.
	itrin2_0 $f set x $.
	itrin2_1 $f set y $.
	itrin2_2 $f set z $.
	ftrin2_0 $f class R $.
	ftrin2_1 $f class S $.
	trin2 $p |- ( ( ( R o. R ) C_ R /\ ( S o. S ) C_ S ) -> ( ( R i^i S ) o. ( R i^i S ) ) C_ ( R i^i S ) ) $= ftrin2_0 ftrin2_0 ccom ftrin2_0 wss ftrin2_1 ftrin2_1 ccom ftrin2_1 wss wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal ftrin2_0 ftrin2_1 cin ftrin2_0 ftrin2_1 cin ccom ftrin2_0 ftrin2_1 cin wss ftrin2_0 ftrin2_0 ccom ftrin2_0 wss ftrin2_1 ftrin2_1 ccom ftrin2_1 wss itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal ftrin2_0 ftrin2_0 ccom ftrin2_0 wss itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal ftrin2_1 ftrin2_1 ccom ftrin2_1 wss itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal wi itrin2_0 itrin2_1 itrin2_2 ftrin2_0 cotr ftrin2_1 ftrin2_1 ccom ftrin2_1 wss itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal ftrin2_1 ftrin2_1 ccom ftrin2_1 wss itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal wi itrin2_0 itrin2_1 itrin2_2 ftrin2_1 cotr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 wal itrin2_0 itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_2 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_2 wal itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 wal itrin2_1 itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wi itrin2_2 itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr wa itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa wi itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 cin wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 ftrin2_1 brin itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 brin itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi wa itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi simpr itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_1 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_1 wbr wi itrin2_0 sup_set_class itrin2_1 sup_set_class ftrin2_0 wbr itrin2_1 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wa itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 wbr wi simpl anim12d com12 an4s syl2anb com12 itrin2_0 sup_set_class itrin2_2 sup_set_class ftrin2_0 ftrin2_1 brin syl6ibr alanimi alanimi alanimi ex sylbi com12 sylbi imp itrin2_0 itrin2_1 itrin2_2 ftrin2_0 ftrin2_1 cin cotr sylibr $.
$}
$( A partial order relation is irreflexive.  (Contributed by Mario
       Carneiro, 2-Nov-2015.) $)
${
	$d x y A $.
	$d x y $.
	$d x y R $.
	$d x y $.
	ipoirr2_0 $f set x $.
	ipoirr2_1 $f set y $.
	fpoirr2_0 $f class A $.
	fpoirr2_1 $f class R $.
	poirr2 $p |- ( R Po A -> ( R i^i ( _I |` A ) ) = (/) ) $= fpoirr2_0 fpoirr2_1 wpo fpoirr2_1 cid fpoirr2_0 cres cin c0 wss fpoirr2_1 cid fpoirr2_0 cres cin c0 wceq fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 ipoirr2_1 fpoirr2_1 cid fpoirr2_0 cres cin c0 cid fpoirr2_0 cres wrel fpoirr2_1 cid fpoirr2_0 cres cin wrel fpoirr2_0 fpoirr2_1 wpo cid fpoirr2_0 relres fpoirr2_1 cid fpoirr2_0 cres relin2 mp1i ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cop fpoirr2_1 cid fpoirr2_0 cres cin wcel ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr wa fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cop c0 wcel ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cop fpoirr2_1 cid fpoirr2_0 cres cin wcel ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 cid fpoirr2_0 cres cin wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr wa ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 cid fpoirr2_0 cres cin df-br ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 cid fpoirr2_0 cres brin bitr3i fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr wa ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cop c0 wcel fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr wn wi ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr wa wn fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid wbr ipoirr2_0 sup_set_class fpoirr2_0 wcel wa fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr wn ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 ipoirr2_1 vex brres fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class fpoirr2_0 wcel ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr wn fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class fpoirr2_0 wcel ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr wn fpoirr2_0 fpoirr2_1 wpo ipoirr2_0 sup_set_class fpoirr2_0 wcel wa ipoirr2_0 sup_set_class ipoirr2_0 sup_set_class fpoirr2_1 wbr wn ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr wn fpoirr2_0 ipoirr2_0 sup_set_class fpoirr2_1 poirr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid wbr ipoirr2_0 sup_set_class ipoirr2_0 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class wceq ipoirr2_0 sup_set_class ipoirr2_0 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr wb ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class ipoirr2_1 vex ideq ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class ipoirr2_0 sup_set_class fpoirr2_1 breq2 sylbi notbid syl5ibcom expimpd ancomsd syl5bi con2d ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class fpoirr2_1 wbr ipoirr2_0 sup_set_class ipoirr2_1 sup_set_class cid fpoirr2_0 cres wbr imnan sylib pm2.21d syl5bi relssdv fpoirr2_1 cid fpoirr2_0 cres cin ss0 syl $.
$}
$( The relation induced by a transitive relation on a part of its field is
     transitive.  (Taking the intersection of a relation with a square cross
     product is a way to restrict it to a subset of its field.)  (Contributed
     by FL, 31-Jul-2009.) $)
${
	ftrinxp_0 $f class A $.
	ftrinxp_1 $f class R $.
	trinxp $p |- ( ( R o. R ) C_ R -> ( ( R i^i ( A X. A ) ) o. ( R i^i ( A X. A ) ) ) C_ ( R i^i ( A X. A ) ) ) $= ftrinxp_1 ftrinxp_1 ccom ftrinxp_1 wss ftrinxp_0 ftrinxp_0 cxp ftrinxp_0 ftrinxp_0 cxp ccom ftrinxp_0 ftrinxp_0 cxp wss ftrinxp_1 ftrinxp_0 ftrinxp_0 cxp cin ftrinxp_1 ftrinxp_0 ftrinxp_0 cxp cin ccom ftrinxp_1 ftrinxp_0 ftrinxp_0 cxp cin wss ftrinxp_0 xpidtr ftrinxp_1 ftrinxp_0 ftrinxp_0 cxp trin2 mpan2 $.
$}
$( A strict order relation is irreflexive.  (Contributed by NM,
       10-Feb-1996.)  (Revised by Mario Carneiro, 10-May-2013.) $)
${
	fsoirri_0 $f class A $.
	fsoirri_1 $f class R $.
	fsoirri_2 $f class S $.
	esoirri_0 $e |- R Or S $.
	esoirri_1 $e |- R C_ ( S X. S ) $.
	soirri $p |- -. A R A $= fsoirri_0 fsoirri_2 wcel fsoirri_0 fsoirri_2 wcel wa fsoirri_0 fsoirri_0 fsoirri_1 wbr wn fsoirri_0 fsoirri_2 wcel fsoirri_0 fsoirri_0 fsoirri_1 wbr wn fsoirri_0 fsoirri_2 wcel fsoirri_2 fsoirri_1 wor fsoirri_0 fsoirri_2 wcel fsoirri_0 fsoirri_0 fsoirri_1 wbr wn esoirri_0 fsoirri_2 fsoirri_0 fsoirri_1 sonr mpan adantl fsoirri_0 fsoirri_0 fsoirri_1 wbr fsoirri_0 fsoirri_2 wcel fsoirri_0 fsoirri_2 wcel wa fsoirri_0 fsoirri_0 fsoirri_2 fsoirri_2 fsoirri_1 esoirri_1 brel con3i pm2.61i $.
$}
$( A strict order relation is a transitive relation.  (Contributed by NM,
         10-Feb-1996.)  (Revised by Mario Carneiro, 10-May-2013.) $)
${
	fsotri_0 $f class A $.
	fsotri_1 $f class B $.
	fsotri_2 $f class C $.
	fsotri_3 $f class R $.
	fsotri_4 $f class S $.
	esotri_0 $e |- R Or S $.
	esotri_1 $e |- R C_ ( S X. S ) $.
	sotri $p |- ( ( A R B /\ B R C ) -> A R C ) $= fsotri_0 fsotri_4 wcel fsotri_1 fsotri_4 wcel fsotri_2 fsotri_4 wcel wa wa fsotri_0 fsotri_1 fsotri_3 wbr fsotri_1 fsotri_2 fsotri_3 wbr wa fsotri_0 fsotri_2 fsotri_3 wbr fsotri_0 fsotri_1 fsotri_3 wbr fsotri_0 fsotri_4 wcel fsotri_1 fsotri_2 fsotri_3 wbr fsotri_1 fsotri_4 wcel fsotri_2 fsotri_4 wcel wa fsotri_0 fsotri_1 fsotri_3 wbr fsotri_0 fsotri_4 wcel fsotri_1 fsotri_4 wcel fsotri_0 fsotri_1 fsotri_4 fsotri_4 fsotri_3 esotri_1 brel simpld fsotri_1 fsotri_2 fsotri_4 fsotri_4 fsotri_3 esotri_1 brel anim12i fsotri_0 fsotri_4 wcel fsotri_1 fsotri_4 wcel fsotri_2 fsotri_4 wcel fsotri_0 fsotri_1 fsotri_3 wbr fsotri_1 fsotri_2 fsotri_3 wbr wa fsotri_0 fsotri_2 fsotri_3 wbr wi fsotri_4 fsotri_3 wor fsotri_0 fsotri_4 wcel fsotri_1 fsotri_4 wcel fsotri_2 fsotri_4 wcel w3a fsotri_0 fsotri_1 fsotri_3 wbr fsotri_1 fsotri_2 fsotri_3 wbr wa fsotri_0 fsotri_2 fsotri_3 wbr wi esotri_0 fsotri_4 fsotri_0 fsotri_1 fsotri_2 fsotri_3 sotr mpan 3expb mpcom $.
$}
$( A strict order relation has no 2-cycle loops.  (Contributed by NM,
         10-Feb-1996.)  (Revised by Mario Carneiro, 10-May-2013.) $)
${
	fson2lpi_0 $f class A $.
	fson2lpi_1 $f class B $.
	fson2lpi_2 $f class R $.
	fson2lpi_3 $f class S $.
	eson2lpi_0 $e |- R Or S $.
	eson2lpi_1 $e |- R C_ ( S X. S ) $.
	son2lpi $p |- -. ( A R B /\ B R A ) $= fson2lpi_0 fson2lpi_1 fson2lpi_2 wbr fson2lpi_1 fson2lpi_0 fson2lpi_2 wbr wa fson2lpi_0 fson2lpi_0 fson2lpi_2 wbr fson2lpi_0 fson2lpi_2 fson2lpi_3 eson2lpi_0 eson2lpi_1 soirri fson2lpi_0 fson2lpi_1 fson2lpi_0 fson2lpi_2 fson2lpi_3 eson2lpi_0 eson2lpi_1 sotri mto $.
$}
$( A transitivity relation.  (Read ` A <_ B ` and ` B < C ` implies
         ` A < C ` .)  (Contributed by Mario Carneiro, 10-May-2013.) $)
${
	fsotri2_0 $f class A $.
	fsotri2_1 $f class B $.
	fsotri2_2 $f class C $.
	fsotri2_3 $f class R $.
	fsotri2_4 $f class S $.
	esotri2_0 $e |- R Or S $.
	esotri2_1 $e |- R C_ ( S X. S ) $.
	sotri2 $p |- ( ( A e. S /\ -. B R A /\ B R C ) -> A R C ) $= fsotri2_0 fsotri2_4 wcel fsotri2_1 fsotri2_0 fsotri2_3 wbr wn fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_2 fsotri2_3 wbr fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_4 wcel fsotri2_1 fsotri2_0 fsotri2_3 wbr wn fsotri2_0 fsotri2_2 fsotri2_3 wbr fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_1 fsotri2_4 wcel fsotri2_0 fsotri2_4 wcel fsotri2_1 fsotri2_0 fsotri2_3 wbr wn fsotri2_0 fsotri2_2 fsotri2_3 wbr wi fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_1 fsotri2_4 wcel fsotri2_2 fsotri2_4 wcel fsotri2_1 fsotri2_2 fsotri2_4 fsotri2_4 fsotri2_3 esotri2_1 brel simpld fsotri2_1 fsotri2_4 wcel fsotri2_0 fsotri2_4 wcel wa fsotri2_1 fsotri2_0 fsotri2_3 wbr wn fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_2 fsotri2_3 wbr fsotri2_1 fsotri2_4 wcel fsotri2_0 fsotri2_4 wcel wa fsotri2_1 fsotri2_0 fsotri2_3 wbr wn fsotri2_1 fsotri2_0 wceq fsotri2_0 fsotri2_1 fsotri2_3 wbr wo fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_2 fsotri2_3 wbr wi fsotri2_1 fsotri2_4 wcel fsotri2_0 fsotri2_4 wcel wa fsotri2_1 fsotri2_0 fsotri2_3 wbr fsotri2_1 fsotri2_0 wceq fsotri2_0 fsotri2_1 fsotri2_3 wbr wo fsotri2_4 fsotri2_3 wor fsotri2_1 fsotri2_4 wcel fsotri2_0 fsotri2_4 wcel wa fsotri2_1 fsotri2_0 fsotri2_3 wbr fsotri2_1 fsotri2_0 wceq fsotri2_0 fsotri2_1 fsotri2_3 wbr wo wn wb esotri2_0 fsotri2_4 fsotri2_1 fsotri2_0 fsotri2_3 sotric mpan con2bid fsotri2_1 fsotri2_0 wceq fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_2 fsotri2_3 wbr wi fsotri2_0 fsotri2_1 fsotri2_3 wbr fsotri2_1 fsotri2_0 wceq fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_2 fsotri2_3 wbr fsotri2_1 fsotri2_0 fsotri2_2 fsotri2_3 breq1 biimpd fsotri2_0 fsotri2_1 fsotri2_3 wbr fsotri2_1 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_2 fsotri2_3 wbr fsotri2_0 fsotri2_1 fsotri2_2 fsotri2_3 fsotri2_4 esotri2_0 esotri2_1 sotri ex jaoi syl6bir com3r mpand com3l 3imp $.
$}
$( A transitivity relation.  (Read ` A < B ` and ` B <_ C ` implies
         ` A < C ` .)  (Contributed by Mario Carneiro, 10-May-2013.) $)
${
	fsotri3_0 $f class A $.
	fsotri3_1 $f class B $.
	fsotri3_2 $f class C $.
	fsotri3_3 $f class R $.
	fsotri3_4 $f class S $.
	esotri3_0 $e |- R Or S $.
	esotri3_1 $e |- R C_ ( S X. S ) $.
	sotri3 $p |- ( ( C e. S /\ A R B /\ -. C R B ) -> A R C ) $= fsotri3_2 fsotri3_4 wcel fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_2 fsotri3_1 fsotri3_3 wbr wn fsotri3_0 fsotri3_2 fsotri3_3 wbr fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_2 fsotri3_4 wcel fsotri3_2 fsotri3_1 fsotri3_3 wbr wn fsotri3_0 fsotri3_2 fsotri3_3 wbr wi fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_2 fsotri3_4 wcel fsotri3_1 fsotri3_4 wcel fsotri3_2 fsotri3_1 fsotri3_3 wbr wn fsotri3_0 fsotri3_2 fsotri3_3 wbr wi fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_0 fsotri3_4 wcel fsotri3_1 fsotri3_4 wcel fsotri3_0 fsotri3_1 fsotri3_4 fsotri3_4 fsotri3_3 esotri3_1 brel simprd fsotri3_2 fsotri3_4 wcel fsotri3_1 fsotri3_4 wcel wa fsotri3_2 fsotri3_1 fsotri3_3 wbr wn fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_0 fsotri3_2 fsotri3_3 wbr fsotri3_2 fsotri3_4 wcel fsotri3_1 fsotri3_4 wcel wa fsotri3_2 fsotri3_1 fsotri3_3 wbr wn fsotri3_2 fsotri3_1 wceq fsotri3_1 fsotri3_2 fsotri3_3 wbr wo fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_0 fsotri3_2 fsotri3_3 wbr wi fsotri3_2 fsotri3_4 wcel fsotri3_1 fsotri3_4 wcel wa fsotri3_2 fsotri3_1 fsotri3_3 wbr fsotri3_2 fsotri3_1 wceq fsotri3_1 fsotri3_2 fsotri3_3 wbr wo fsotri3_4 fsotri3_3 wor fsotri3_2 fsotri3_4 wcel fsotri3_1 fsotri3_4 wcel wa fsotri3_2 fsotri3_1 fsotri3_3 wbr fsotri3_2 fsotri3_1 wceq fsotri3_1 fsotri3_2 fsotri3_3 wbr wo wn wb esotri3_0 fsotri3_4 fsotri3_2 fsotri3_1 fsotri3_3 sotric mpan con2bid fsotri3_2 fsotri3_1 wceq fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_0 fsotri3_2 fsotri3_3 wbr wi fsotri3_1 fsotri3_2 fsotri3_3 wbr fsotri3_2 fsotri3_1 wceq fsotri3_0 fsotri3_2 fsotri3_3 wbr fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_2 fsotri3_1 fsotri3_0 fsotri3_3 breq2 biimprd fsotri3_0 fsotri3_1 fsotri3_3 wbr fsotri3_1 fsotri3_2 fsotri3_3 wbr fsotri3_0 fsotri3_2 fsotri3_3 wbr fsotri3_0 fsotri3_1 fsotri3_2 fsotri3_3 fsotri3_4 esotri3_0 esotri3_1 sotri expcom jaoi syl6bir com3r mpan2d com12 3imp $.
$}
$( A strict order relation is irreflexive.  (Contributed by NM,
       10-Feb-1996.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
${
	fsoirriOLD_0 $f class A $.
	fsoirriOLD_1 $f class R $.
	fsoirriOLD_2 $f class S $.
	esoirriOLD_0 $e |- A e. _V $.
	esoirriOLD_1 $e |- R Or S $.
	esoirriOLD_2 $e |- R C_ ( S X. S ) $.
	soirriOLD $p |- -. A R A $= fsoirriOLD_0 fsoirriOLD_2 wcel fsoirriOLD_0 fsoirriOLD_2 wcel wa fsoirriOLD_0 fsoirriOLD_0 fsoirriOLD_1 wbr wn fsoirriOLD_0 fsoirriOLD_2 wcel fsoirriOLD_0 fsoirriOLD_0 fsoirriOLD_1 wbr wn fsoirriOLD_0 fsoirriOLD_2 wcel fsoirriOLD_2 fsoirriOLD_1 wor fsoirriOLD_0 fsoirriOLD_2 wcel fsoirriOLD_0 fsoirriOLD_0 fsoirriOLD_1 wbr wn esoirriOLD_1 fsoirriOLD_2 fsoirriOLD_0 fsoirriOLD_1 sonr mpan adantl fsoirriOLD_0 fsoirriOLD_0 fsoirriOLD_1 wbr fsoirriOLD_0 fsoirriOLD_2 wcel fsoirriOLD_0 fsoirriOLD_2 wcel wa fsoirriOLD_0 fsoirriOLD_0 fsoirriOLD_2 fsoirriOLD_2 fsoirriOLD_1 esoirriOLD_2 brel con3i pm2.61i $.
$}
$( A strict order relation is a transitive relation.  (Contributed by NM,
         10-Feb-1996.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
${
	fsotriOLD_0 $f class A $.
	fsotriOLD_1 $f class B $.
	fsotriOLD_2 $f class C $.
	fsotriOLD_3 $f class R $.
	fsotriOLD_4 $f class S $.
	esotriOLD_0 $e |- A e. _V $.
	esotriOLD_1 $e |- R Or S $.
	esotriOLD_2 $e |- R C_ ( S X. S ) $.
	esotriOLD_3 $e |- B e. _V $.
	esotriOLD_4 $e |- C e. _V $.
	sotriOLD $p |- ( ( A R B /\ B R C ) -> A R C ) $= fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a fsotriOLD_0 fsotriOLD_1 fsotriOLD_3 wbr fsotriOLD_1 fsotriOLD_2 fsotriOLD_3 wbr wa fsotriOLD_0 fsotriOLD_2 fsotriOLD_3 wbr fsotriOLD_0 fsotriOLD_1 fsotriOLD_3 wbr fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel wa fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel wa fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a fsotriOLD_1 fsotriOLD_2 fsotriOLD_3 wbr fsotriOLD_0 fsotriOLD_1 fsotriOLD_4 fsotriOLD_4 fsotriOLD_3 esotriOLD_2 brel fsotriOLD_1 fsotriOLD_2 fsotriOLD_4 fsotriOLD_4 fsotriOLD_3 esotriOLD_2 brel fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a wi fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a id 3exp a1dd imp43 syl2an fsotriOLD_4 fsotriOLD_3 wor fsotriOLD_0 fsotriOLD_4 wcel fsotriOLD_1 fsotriOLD_4 wcel fsotriOLD_2 fsotriOLD_4 wcel w3a fsotriOLD_0 fsotriOLD_1 fsotriOLD_3 wbr fsotriOLD_1 fsotriOLD_2 fsotriOLD_3 wbr wa fsotriOLD_0 fsotriOLD_2 fsotriOLD_3 wbr wi esotriOLD_1 fsotriOLD_4 fsotriOLD_0 fsotriOLD_1 fsotriOLD_2 fsotriOLD_3 sotr mpan mpcom $.
$}
$( A strict order relation has no 2-cycle loops.  (Contributed by NM,
         10-Feb-1996.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
${
	fson2lpiOLD_0 $f class A $.
	fson2lpiOLD_1 $f class B $.
	fson2lpiOLD_2 $f class R $.
	fson2lpiOLD_3 $f class S $.
	eson2lpiOLD_0 $e |- A e. _V $.
	eson2lpiOLD_1 $e |- R Or S $.
	eson2lpiOLD_2 $e |- R C_ ( S X. S ) $.
	eson2lpiOLD_3 $e |- B e. _V $.
	son2lpiOLD $p |- -. ( A R B /\ B R A ) $= fson2lpiOLD_0 fson2lpiOLD_1 fson2lpiOLD_2 wbr fson2lpiOLD_1 fson2lpiOLD_0 fson2lpiOLD_2 wbr wa fson2lpiOLD_0 fson2lpiOLD_0 fson2lpiOLD_2 wbr fson2lpiOLD_0 fson2lpiOLD_2 fson2lpiOLD_3 eson2lpiOLD_1 eson2lpiOLD_2 soirri fson2lpiOLD_0 fson2lpiOLD_1 fson2lpiOLD_0 fson2lpiOLD_2 fson2lpiOLD_3 eson2lpiOLD_1 eson2lpiOLD_2 sotri mto $.
$}
$( Express "less than or equals" for general strict orders.  (Contributed by
     Stefan O'Rear, 17-Jan-2015.) $)
${
	fpoleloe_0 $f class A $.
	fpoleloe_1 $f class B $.
	fpoleloe_2 $f class R $.
	fpoleloe_3 $f class V $.
	poleloe $p |- ( B e. V -> ( A ( R u. _I ) B <-> ( A R B \/ A = B ) ) ) $= fpoleloe_0 fpoleloe_1 fpoleloe_2 cid cun wbr fpoleloe_0 fpoleloe_1 fpoleloe_2 wbr fpoleloe_0 fpoleloe_1 cid wbr wo fpoleloe_1 fpoleloe_3 wcel fpoleloe_0 fpoleloe_1 fpoleloe_2 wbr fpoleloe_0 fpoleloe_1 wceq wo fpoleloe_0 fpoleloe_1 fpoleloe_2 cid brun fpoleloe_1 fpoleloe_3 wcel fpoleloe_0 fpoleloe_1 cid wbr fpoleloe_0 fpoleloe_1 wceq fpoleloe_0 fpoleloe_1 fpoleloe_2 wbr fpoleloe_0 fpoleloe_1 fpoleloe_3 ideqg orbi2d syl5bb $.
$}
$( Transitive law for general strict orders.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
${
	fpoltletr_0 $f class A $.
	fpoltletr_1 $f class B $.
	fpoltletr_2 $f class C $.
	fpoltletr_3 $f class R $.
	fpoltletr_4 $f class X $.
	poltletr $p |- ( ( R Po X /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A R B /\ B ( R u. _I ) C ) -> A R C ) ) $= fpoltletr_4 fpoltletr_3 wpo fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a wa fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 cid cun wbr wa fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 wceq wo wa fpoltletr_0 fpoltletr_2 fpoltletr_3 wbr fpoltletr_4 fpoltletr_3 wpo fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a wa fpoltletr_1 fpoltletr_2 fpoltletr_3 cid cun wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 wceq wo fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a fpoltletr_1 fpoltletr_2 fpoltletr_3 cid cun wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 wceq wo wb fpoltletr_4 fpoltletr_3 wpo fpoltletr_2 fpoltletr_4 wcel fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_2 fpoltletr_3 cid cun wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 wceq wo wb fpoltletr_1 fpoltletr_4 wcel fpoltletr_1 fpoltletr_2 fpoltletr_3 fpoltletr_4 poleloe 3ad2ant3 adantl anbi2d fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 wceq wo wa fpoltletr_4 fpoltletr_3 wpo fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a wa fpoltletr_0 fpoltletr_2 fpoltletr_3 wbr fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr fpoltletr_4 fpoltletr_3 wpo fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a wa fpoltletr_0 fpoltletr_2 fpoltletr_3 wbr wi fpoltletr_1 fpoltletr_2 wceq fpoltletr_4 fpoltletr_3 wpo fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a wa fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 fpoltletr_3 wbr wa fpoltletr_0 fpoltletr_2 fpoltletr_3 wbr fpoltletr_4 fpoltletr_0 fpoltletr_1 fpoltletr_2 fpoltletr_3 potr com12 fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 wceq wa fpoltletr_0 fpoltletr_2 fpoltletr_3 wbr fpoltletr_4 fpoltletr_3 wpo fpoltletr_0 fpoltletr_4 wcel fpoltletr_1 fpoltletr_4 wcel fpoltletr_2 fpoltletr_4 wcel w3a wa fpoltletr_1 fpoltletr_2 wceq fpoltletr_0 fpoltletr_1 fpoltletr_3 wbr fpoltletr_0 fpoltletr_2 fpoltletr_3 wbr fpoltletr_1 fpoltletr_2 fpoltletr_0 fpoltletr_3 breq2 biimpac a1d jaodan com12 sylbid $.
$}
$( Property of a minimum in a strict order.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
${
	fsomin1_0 $f class A $.
	fsomin1_1 $f class B $.
	fsomin1_2 $f class R $.
	fsomin1_3 $f class X $.
	somin1 $p |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) -> if ( A R B , A , B ) ( R u. _I ) A ) $= fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 cid cun wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 iftrue olcd adantl fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr wn wa fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo fsomin1_0 fsomin1_1 fsomin1_2 wbr wn fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 wceq fsomin1_1 fsomin1_0 fsomin1_2 wbr wo wn fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo wn fsomin1_3 fsomin1_0 fsomin1_1 fsomin1_2 sotric fsomin1_0 fsomin1_1 wceq fsomin1_1 fsomin1_0 fsomin1_2 wbr wo fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo fsomin1_0 fsomin1_1 wceq fsomin1_1 fsomin1_0 fsomin1_2 wbr wo fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 wceq wo fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo fsomin1_0 fsomin1_1 wceq fsomin1_1 fsomin1_0 fsomin1_2 wbr orcom fsomin1_0 fsomin1_1 wceq fsomin1_1 fsomin1_0 wceq fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 eqcom orbi2i bitri notbii syl6bb con2bid biimpar fsomin1_0 fsomin1_1 fsomin1_2 wbr wn fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo wb fsomin1_3 fsomin1_2 wor fsomin1_0 fsomin1_3 wcel fsomin1_1 fsomin1_3 wcel wa wa fsomin1_0 fsomin1_1 fsomin1_2 wbr wn fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_1 wceq fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 wceq wo wb fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 iffalse fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_1 wceq fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_1 fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq fsomin1_1 fsomin1_0 wceq fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_1 fsomin1_0 fsomin1_2 breq1 fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_1 fsomin1_0 eqeq1 orbi12d syl adantl mpbird pm2.61dan fsomin1_0 fsomin1_3 wcel fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 cid cun wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 wbr fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 wceq wo wb fsomin1_3 fsomin1_2 wor fsomin1_1 fsomin1_3 wcel fsomin1_0 fsomin1_1 fsomin1_2 wbr fsomin1_0 fsomin1_1 cif fsomin1_0 fsomin1_2 fsomin1_3 poleloe ad2antrl mpbird $.
$}
$( Commutativity of minimum in a total order.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
${
	fsomincom_0 $f class A $.
	fsomincom_1 $f class B $.
	fsomincom_2 $f class R $.
	fsomincom_3 $f class X $.
	somincom $p |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) -> if ( A R B , A , B ) = if ( B R A , B , A ) ) $= fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 cif fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif wceq fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 cif fsomincom_0 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 cif fsomincom_0 wceq fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 iftrue adantl fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wa fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif fsomincom_0 fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wa fsomincom_1 fsomincom_0 fsomincom_2 wbr wn fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif fsomincom_0 wceq fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_1 fsomincom_0 fsomincom_2 wbr wa wn wi fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wa fsomincom_1 fsomincom_0 fsomincom_2 wbr wn wi fsomincom_3 fsomincom_0 fsomincom_1 fsomincom_2 so2nr fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_1 fsomincom_0 fsomincom_2 wbr nan mpbi fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 iffalse syl eqcomd eqtrd fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wn wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 cif fsomincom_1 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif fsomincom_0 fsomincom_1 fsomincom_2 wbr wn fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 cif fsomincom_1 wceq fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 iffalse adantl fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wn fsomincom_1 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif wceq fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr wn fsomincom_0 fsomincom_1 wceq fsomincom_1 fsomincom_0 fsomincom_2 wbr wo fsomincom_1 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif wceq fsomincom_3 fsomincom_2 wor fsomincom_0 fsomincom_3 wcel fsomincom_1 fsomincom_3 wcel wa wa fsomincom_0 fsomincom_1 fsomincom_2 wbr fsomincom_0 fsomincom_1 wceq fsomincom_1 fsomincom_0 fsomincom_2 wbr wo fsomincom_3 fsomincom_0 fsomincom_1 fsomincom_2 sotric con2bid fsomincom_0 fsomincom_1 wceq fsomincom_1 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif wceq fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_0 fsomincom_1 wceq fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_1 cif fsomincom_1 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_0 fsomincom_1 fsomincom_1 ifeq2 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 ifid syl6req fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 cif fsomincom_1 fsomincom_1 fsomincom_0 fsomincom_2 wbr fsomincom_1 fsomincom_0 iftrue eqcomd jaoi syl6bir imp eqtrd pm2.61dan $.
$}
$( Property of a minimum in a strict order.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
${
	fsomin2_0 $f class A $.
	fsomin2_1 $f class B $.
	fsomin2_2 $f class R $.
	fsomin2_3 $f class X $.
	somin2 $p |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) -> if ( A R B , A , B ) ( R u. _I ) B ) $= fsomin2_3 fsomin2_2 wor fsomin2_0 fsomin2_3 wcel fsomin2_1 fsomin2_3 wcel wa wa fsomin2_0 fsomin2_1 fsomin2_2 wbr fsomin2_0 fsomin2_1 cif fsomin2_1 fsomin2_0 fsomin2_2 wbr fsomin2_1 fsomin2_0 cif fsomin2_1 fsomin2_2 cid cun fsomin2_0 fsomin2_1 fsomin2_2 fsomin2_3 somincom fsomin2_3 fsomin2_2 wor fsomin2_1 fsomin2_3 wcel fsomin2_0 fsomin2_3 wcel fsomin2_1 fsomin2_0 fsomin2_2 wbr fsomin2_1 fsomin2_0 cif fsomin2_1 fsomin2_2 cid cun wbr fsomin2_1 fsomin2_0 fsomin2_2 fsomin2_3 somin1 ancom2s eqbrtrd $.
$}
$( Being less than a minimum, for a general total order.  (Contributed by
     Stefan O'Rear, 17-Jan-2015.) $)
${
	fsoltmin_0 $f class A $.
	fsoltmin_1 $f class B $.
	fsoltmin_2 $f class C $.
	fsoltmin_3 $f class R $.
	fsoltmin_4 $f class X $.
	soltmin $p |- ( ( R Or X /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( A R if ( B R C , B , C ) <-> ( A R B /\ A R C ) ) ) $= fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_0 fsoltmin_1 fsoltmin_3 wbr fsoltmin_0 fsoltmin_2 fsoltmin_3 wbr wa fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_0 fsoltmin_1 fsoltmin_3 wbr fsoltmin_0 fsoltmin_2 fsoltmin_3 wbr wa fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_0 fsoltmin_1 fsoltmin_3 wbr fsoltmin_0 fsoltmin_2 fsoltmin_3 wbr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_4 fsoltmin_3 wpo fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel w3a fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_1 fsoltmin_3 cid cun wbr fsoltmin_0 fsoltmin_1 fsoltmin_3 wbr fsoltmin_4 fsoltmin_3 wor fsoltmin_4 fsoltmin_3 wpo fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_4 fsoltmin_3 sopo ad2antrr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr1 fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr2 fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr3 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_4 ifcl syl2anc fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr2 3jca fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simpr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_4 fsoltmin_3 wor fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_1 fsoltmin_3 cid cun wbr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simpll fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr2 fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr3 fsoltmin_1 fsoltmin_2 fsoltmin_3 fsoltmin_4 somin1 syl12anc fsoltmin_4 fsoltmin_3 wpo fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_1 fsoltmin_3 cid cun wbr wa fsoltmin_0 fsoltmin_1 fsoltmin_3 wbr fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_1 fsoltmin_3 fsoltmin_4 poltletr imp syl22anc fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_4 fsoltmin_3 wpo fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_2 fsoltmin_3 cid cun wbr fsoltmin_0 fsoltmin_2 fsoltmin_3 wbr fsoltmin_4 fsoltmin_3 wor fsoltmin_4 fsoltmin_3 wpo fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_4 fsoltmin_3 sopo ad2antrr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr1 fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr2 fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr3 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_4 ifcl syl2anc fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr3 3jca fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simpr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr wa fsoltmin_4 fsoltmin_3 wor fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_2 fsoltmin_3 cid cun wbr fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simpll fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr2 fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel fsoltmin_4 fsoltmin_3 wor fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr simplr3 fsoltmin_1 fsoltmin_2 fsoltmin_3 fsoltmin_4 somin2 syl12anc fsoltmin_4 fsoltmin_3 wpo fsoltmin_0 fsoltmin_4 wcel fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_4 wcel fsoltmin_2 fsoltmin_4 wcel w3a wa fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_2 fsoltmin_3 cid cun wbr wa fsoltmin_0 fsoltmin_2 fsoltmin_3 wbr fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_2 fsoltmin_3 fsoltmin_4 poltletr imp syl22anc jca ex fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_0 fsoltmin_1 fsoltmin_3 wbr fsoltmin_0 fsoltmin_2 fsoltmin_3 wbr fsoltmin_0 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 fsoltmin_1 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_0 fsoltmin_3 breq2 fsoltmin_2 fsoltmin_1 fsoltmin_2 fsoltmin_3 wbr fsoltmin_1 fsoltmin_2 cif fsoltmin_0 fsoltmin_3 breq2 ifboth impbid1 $.
$}
$( The converse of a class abstraction of ordered pairs.  (Contributed by
       NM, 11-Dec-2003.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z w $.
	$d z w ph $.
	icnvopab_0 $f set z $.
	icnvopab_1 $f set w $.
	fcnvopab_0 $f wff ph $.
	fcnvopab_1 $f set x $.
	fcnvopab_2 $f set y $.
	cnvopab $p |- `' { <. x , y >. | ph } = { <. y , x >. | ph } $= icnvopab_0 icnvopab_1 fcnvopab_0 fcnvopab_1 fcnvopab_2 copab ccnv fcnvopab_0 fcnvopab_2 fcnvopab_1 copab fcnvopab_0 fcnvopab_1 fcnvopab_2 copab relcnv fcnvopab_0 fcnvopab_2 fcnvopab_1 relopab icnvopab_1 sup_set_class icnvopab_0 sup_set_class cop fcnvopab_0 fcnvopab_1 fcnvopab_2 copab wcel fcnvopab_0 fcnvopab_2 icnvopab_0 wsb fcnvopab_1 icnvopab_1 wsb icnvopab_0 sup_set_class icnvopab_1 sup_set_class cop fcnvopab_0 fcnvopab_1 fcnvopab_2 copab ccnv wcel icnvopab_0 sup_set_class icnvopab_1 sup_set_class cop fcnvopab_0 fcnvopab_2 fcnvopab_1 copab wcel icnvopab_1 sup_set_class icnvopab_0 sup_set_class cop fcnvopab_0 fcnvopab_1 fcnvopab_2 copab wcel fcnvopab_0 fcnvopab_1 icnvopab_1 wsb fcnvopab_2 icnvopab_0 wsb fcnvopab_0 fcnvopab_2 icnvopab_0 wsb fcnvopab_1 icnvopab_1 wsb fcnvopab_0 fcnvopab_1 fcnvopab_2 icnvopab_1 icnvopab_0 opelopabsbOLD fcnvopab_0 fcnvopab_1 icnvopab_1 fcnvopab_2 icnvopab_0 sbcom2 bitri icnvopab_0 sup_set_class icnvopab_1 sup_set_class fcnvopab_0 fcnvopab_1 fcnvopab_2 copab icnvopab_0 vex icnvopab_1 vex opelcnv fcnvopab_0 fcnvopab_2 fcnvopab_1 icnvopab_0 icnvopab_1 opelopabsbOLD 3bitr4i eqrelriiv $.
$}
$( The converse of the empty set.  (Contributed by NM, 6-Apr-1998.) $)
${
	$d x y $.
	icnv0_0 $f set x $.
	icnv0_1 $f set y $.
	cnv0 $p |- `' (/) = (/) $= icnv0_0 icnv0_1 c0 ccnv c0 c0 relcnv rel0 icnv0_0 sup_set_class icnv0_1 sup_set_class cop c0 ccnv wcel icnv0_1 sup_set_class icnv0_0 sup_set_class cop c0 wcel icnv0_0 sup_set_class icnv0_1 sup_set_class cop c0 wcel icnv0_0 sup_set_class icnv0_1 sup_set_class c0 icnv0_0 vex icnv0_1 vex opelcnv icnv0_0 sup_set_class icnv0_1 sup_set_class cop c0 wcel icnv0_1 sup_set_class icnv0_0 sup_set_class cop c0 wcel icnv0_0 sup_set_class icnv0_1 sup_set_class cop noel icnv0_1 sup_set_class icnv0_0 sup_set_class cop noel 2false bitr4i eqrelriiv $.
$}
$( The converse of the identity relation.  Theorem 3.7(ii) of [Monk1]
       p. 36.  (Contributed by NM, 26-Apr-1998.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
${
	$d x y $.
	icnvi_0 $f set x $.
	icnvi_1 $f set y $.
	cnvi $p |- `' _I = _I $= icnvi_1 sup_set_class icnvi_0 sup_set_class cid wbr icnvi_0 icnvi_1 copab icnvi_0 sup_set_class icnvi_1 sup_set_class wceq icnvi_0 icnvi_1 copab cid ccnv cid icnvi_1 sup_set_class icnvi_0 sup_set_class cid wbr icnvi_0 sup_set_class icnvi_1 sup_set_class wceq icnvi_0 icnvi_1 icnvi_1 sup_set_class icnvi_0 sup_set_class cid wbr icnvi_1 sup_set_class icnvi_0 sup_set_class wceq icnvi_0 sup_set_class icnvi_1 sup_set_class wceq icnvi_1 sup_set_class icnvi_0 sup_set_class icnvi_0 vex ideq icnvi_1 icnvi_0 equcom bitri opabbii icnvi_0 icnvi_1 cid df-cnv icnvi_0 icnvi_1 df-id 3eqtr4i $.
$}
$( The converse of a union is the union of converses.  Theorem 16 of
       [Suppes] p. 62.  (Contributed by NM, 25-Mar-1998.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	icnvun_0 $f set x $.
	icnvun_1 $f set y $.
	fcnvun_0 $f class A $.
	fcnvun_1 $f class B $.
	cnvun $p |- `' ( A u. B ) = ( `' A u. `' B ) $= fcnvun_0 fcnvun_1 cun ccnv icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_0 icnvun_1 copab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr icnvun_0 icnvun_1 copab cun fcnvun_0 ccnv fcnvun_1 ccnv cun fcnvun_0 fcnvun_1 cun ccnv icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 fcnvun_1 cun wbr icnvun_0 icnvun_1 copab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_0 icnvun_1 copab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr icnvun_0 icnvun_1 copab cun icnvun_0 icnvun_1 fcnvun_0 fcnvun_1 cun df-cnv icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_0 icnvun_1 copab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr icnvun_0 icnvun_1 copab cun icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr wo icnvun_0 icnvun_1 copab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 fcnvun_1 cun wbr icnvun_0 icnvun_1 copab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr icnvun_0 icnvun_1 unopab icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 fcnvun_1 cun wbr icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr wo icnvun_0 icnvun_1 icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 fcnvun_1 brun opabbii eqtr4i eqtr4i fcnvun_0 ccnv icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_0 wbr icnvun_0 icnvun_1 copab fcnvun_1 ccnv icnvun_1 sup_set_class icnvun_0 sup_set_class fcnvun_1 wbr icnvun_0 icnvun_1 copab icnvun_0 icnvun_1 fcnvun_0 df-cnv icnvun_0 icnvun_1 fcnvun_1 df-cnv uneq12i eqtr4i $.
$}
$( Distributive law for converse over set difference.  (Contributed by
       Mario Carneiro, 26-Jun-2014.) $)
${
	$d x y A $.
	$d x y B $.
	icnvdif_0 $f set x $.
	icnvdif_1 $f set y $.
	fcnvdif_0 $f class A $.
	fcnvdif_1 $f class B $.
	cnvdif $p |- `' ( A \ B ) = ( `' A \ `' B ) $= icnvdif_0 icnvdif_1 fcnvdif_0 fcnvdif_1 cdif ccnv fcnvdif_0 ccnv fcnvdif_1 ccnv cdif fcnvdif_0 fcnvdif_1 cdif relcnv fcnvdif_0 ccnv fcnvdif_1 ccnv cdif fcnvdif_0 ccnv wss fcnvdif_0 ccnv wrel fcnvdif_0 ccnv fcnvdif_1 ccnv cdif wrel fcnvdif_0 ccnv fcnvdif_1 ccnv difss fcnvdif_0 relcnv fcnvdif_0 ccnv fcnvdif_1 ccnv cdif fcnvdif_0 ccnv relss mp2 icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_0 fcnvdif_1 cdif wcel icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_0 wcel icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_1 wcel wn wa icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_0 fcnvdif_1 cdif ccnv wcel icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_0 ccnv fcnvdif_1 ccnv cdif wcel icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_0 fcnvdif_1 eldif icnvdif_0 sup_set_class icnvdif_1 sup_set_class fcnvdif_0 fcnvdif_1 cdif icnvdif_0 vex icnvdif_1 vex opelcnv icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_0 ccnv fcnvdif_1 ccnv cdif wcel icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_0 ccnv wcel icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_1 ccnv wcel wn wa icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_0 wcel icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_1 wcel wn wa icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_0 ccnv fcnvdif_1 ccnv eldif icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_0 ccnv wcel icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_0 wcel icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_1 ccnv wcel wn icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_1 wcel wn icnvdif_0 sup_set_class icnvdif_1 sup_set_class fcnvdif_0 icnvdif_0 vex icnvdif_1 vex opelcnv icnvdif_0 sup_set_class icnvdif_1 sup_set_class cop fcnvdif_1 ccnv wcel icnvdif_1 sup_set_class icnvdif_0 sup_set_class cop fcnvdif_1 wcel icnvdif_0 sup_set_class icnvdif_1 sup_set_class fcnvdif_1 icnvdif_0 vex icnvdif_1 vex opelcnv notbii anbi12i bitri 3bitr4i eqrelriiv $.
$}
$( Distributive law for converse over intersection.  Theorem 15 of [Suppes]
       p. 62.  (Contributed by NM, 25-Mar-1998.)  (Revised by Mario Carneiro,
       26-Jun-2014.) $)
${
	fcnvin_0 $f class A $.
	fcnvin_1 $f class B $.
	cnvin $p |- `' ( A i^i B ) = ( `' A i^i `' B ) $= fcnvin_0 fcnvin_0 fcnvin_1 cdif cdif ccnv fcnvin_0 ccnv fcnvin_0 ccnv fcnvin_1 ccnv cdif cdif fcnvin_0 fcnvin_1 cin ccnv fcnvin_0 ccnv fcnvin_1 ccnv cin fcnvin_0 fcnvin_0 fcnvin_1 cdif cdif ccnv fcnvin_0 ccnv fcnvin_0 fcnvin_1 cdif ccnv cdif fcnvin_0 ccnv fcnvin_0 ccnv fcnvin_1 ccnv cdif cdif fcnvin_0 fcnvin_0 fcnvin_1 cdif cnvdif fcnvin_0 fcnvin_1 cdif ccnv fcnvin_0 ccnv fcnvin_1 ccnv cdif fcnvin_0 ccnv fcnvin_0 fcnvin_1 cnvdif difeq2i eqtri fcnvin_0 fcnvin_1 cin fcnvin_0 fcnvin_0 fcnvin_1 cdif cdif fcnvin_0 fcnvin_1 dfin4 cnveqi fcnvin_0 ccnv fcnvin_1 ccnv dfin4 3eqtr4i $.
$}
$( Distributive law for range over union.  Theorem 8 of [Suppes] p. 60.
     (Contributed by NM, 24-Mar-1998.) $)
${
	frnun_0 $f class A $.
	frnun_1 $f class B $.
	rnun $p |- ran ( A u. B ) = ( ran A u. ran B ) $= frnun_0 frnun_1 cun ccnv cdm frnun_0 ccnv cdm frnun_1 ccnv cdm cun frnun_0 frnun_1 cun crn frnun_0 crn frnun_1 crn cun frnun_0 frnun_1 cun ccnv cdm frnun_0 ccnv frnun_1 ccnv cun cdm frnun_0 ccnv cdm frnun_1 ccnv cdm cun frnun_0 frnun_1 cun ccnv frnun_0 ccnv frnun_1 ccnv cun frnun_0 frnun_1 cnvun dmeqi frnun_0 ccnv frnun_1 ccnv dmun eqtri frnun_0 frnun_1 cun df-rn frnun_0 crn frnun_0 ccnv cdm frnun_1 crn frnun_1 ccnv cdm frnun_0 df-rn frnun_1 df-rn uneq12i 3eqtr4i $.
$}
$( The range of an intersection belongs the intersection of ranges.  Theorem
     9 of [Suppes] p. 60.  (Contributed by NM, 15-Sep-2004.) $)
${
	frnin_0 $f class A $.
	frnin_1 $f class B $.
	rnin $p |- ran ( A i^i B ) C_ ( ran A i^i ran B ) $= frnin_0 frnin_1 cin ccnv cdm frnin_0 ccnv cdm frnin_1 ccnv cdm cin frnin_0 frnin_1 cin crn frnin_0 crn frnin_1 crn cin frnin_0 frnin_1 cin ccnv cdm frnin_0 ccnv frnin_1 ccnv cin cdm frnin_0 ccnv cdm frnin_1 ccnv cdm cin frnin_0 frnin_1 cin ccnv frnin_0 ccnv frnin_1 ccnv cin frnin_0 frnin_1 cnvin dmeqi frnin_0 ccnv frnin_1 ccnv dmin eqsstri frnin_0 frnin_1 cin df-rn frnin_0 crn frnin_0 ccnv cdm frnin_1 crn frnin_1 ccnv cdm frnin_0 df-rn frnin_1 df-rn ineq12i 3sstr4i $.
$}
$( The range of an indexed union.  (Contributed by Mario Carneiro,
       29-May-2015.) $)
${
	$d x y z $.
	$d y z A $.
	$d y z B $.
	irniun_0 $f set y $.
	irniun_1 $f set z $.
	frniun_0 $f set x $.
	frniun_1 $f class A $.
	frniun_2 $f class B $.
	rniun $p |- ran U_ x e. A B = U_ x e. A ran B $= irniun_1 frniun_0 frniun_1 frniun_2 ciun crn frniun_0 frniun_1 frniun_2 crn ciun irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_0 frniun_1 frniun_2 ciun wcel irniun_0 wex irniun_1 sup_set_class frniun_2 crn wcel frniun_0 frniun_1 wrex irniun_1 sup_set_class frniun_0 frniun_1 frniun_2 ciun crn wcel irniun_1 sup_set_class frniun_0 frniun_1 frniun_2 crn ciun wcel irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_2 wcel irniun_0 wex frniun_0 frniun_1 wrex irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_2 wcel frniun_0 frniun_1 wrex irniun_0 wex irniun_1 sup_set_class frniun_2 crn wcel frniun_0 frniun_1 wrex irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_0 frniun_1 frniun_2 ciun wcel irniun_0 wex irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_2 wcel frniun_0 irniun_0 frniun_1 rexcom4 irniun_1 sup_set_class frniun_2 crn wcel irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_2 wcel irniun_0 wex frniun_0 frniun_1 irniun_0 irniun_1 sup_set_class frniun_2 irniun_1 vex elrn2 rexbii irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_0 frniun_1 frniun_2 ciun wcel irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_2 wcel frniun_0 frniun_1 wrex irniun_0 frniun_0 irniun_0 sup_set_class irniun_1 sup_set_class cop frniun_1 frniun_2 eliun exbii 3bitr4ri irniun_0 irniun_1 sup_set_class frniun_0 frniun_1 frniun_2 ciun irniun_1 vex elrn2 frniun_0 irniun_1 sup_set_class frniun_1 frniun_2 crn eliun 3bitr4i eqriv $.
$}
$( The range of a union.  Part of Exercise 8 of [Enderton] p. 41.
       (Contributed by NM, 17-Mar-2004.)  (Revised by Mario Carneiro,
       29-May-2015.) $)
${
	$d x A $.
	frnuni_0 $f set x $.
	frnuni_1 $f class A $.
	rnuni $p |- ran U. A = U_ x e. A ran x $= frnuni_1 cuni crn frnuni_0 frnuni_1 frnuni_0 sup_set_class ciun crn frnuni_0 frnuni_1 frnuni_0 sup_set_class crn ciun frnuni_1 cuni frnuni_0 frnuni_1 frnuni_0 sup_set_class ciun frnuni_0 frnuni_1 uniiun rneqi frnuni_0 frnuni_1 frnuni_0 sup_set_class rniun eqtri $.
$}
$( Distributive law for image over union.  Theorem 35 of [Suppes] p. 65.
     (Contributed by NM, 30-Sep-2002.) $)
${
	fimaundi_0 $f class A $.
	fimaundi_1 $f class B $.
	fimaundi_2 $f class C $.
	imaundi $p |- ( A " ( B u. C ) ) = ( ( A " B ) u. ( A " C ) ) $= fimaundi_0 fimaundi_1 fimaundi_2 cun cres crn fimaundi_0 fimaundi_1 cres crn fimaundi_0 fimaundi_2 cres crn cun fimaundi_0 fimaundi_1 fimaundi_2 cun cima fimaundi_0 fimaundi_1 cima fimaundi_0 fimaundi_2 cima cun fimaundi_0 fimaundi_1 fimaundi_2 cun cres crn fimaundi_0 fimaundi_1 cres fimaundi_0 fimaundi_2 cres cun crn fimaundi_0 fimaundi_1 cres crn fimaundi_0 fimaundi_2 cres crn cun fimaundi_0 fimaundi_1 fimaundi_2 cun cres fimaundi_0 fimaundi_1 cres fimaundi_0 fimaundi_2 cres cun fimaundi_0 fimaundi_1 fimaundi_2 resundi rneqi fimaundi_0 fimaundi_1 cres fimaundi_0 fimaundi_2 cres rnun eqtri fimaundi_0 fimaundi_1 fimaundi_2 cun df-ima fimaundi_0 fimaundi_1 cima fimaundi_0 fimaundi_1 cres crn fimaundi_0 fimaundi_2 cima fimaundi_0 fimaundi_2 cres crn fimaundi_0 fimaundi_1 df-ima fimaundi_0 fimaundi_2 df-ima uneq12i 3eqtr4i $.
$}
$( The image of a union.  (Contributed by Jeff Hoffman, 17-Feb-2008.) $)
${
	fimaundir_0 $f class A $.
	fimaundir_1 $f class B $.
	fimaundir_2 $f class C $.
	imaundir $p |- ( ( A u. B ) " C ) = ( ( A " C ) u. ( B " C ) ) $= fimaundir_0 fimaundir_1 cun fimaundir_2 cima fimaundir_0 fimaundir_2 cres crn fimaundir_1 fimaundir_2 cres crn cun fimaundir_0 fimaundir_2 cima fimaundir_1 fimaundir_2 cima cun fimaundir_0 fimaundir_1 cun fimaundir_2 cima fimaundir_0 fimaundir_1 cun fimaundir_2 cres crn fimaundir_0 fimaundir_2 cres fimaundir_1 fimaundir_2 cres cun crn fimaundir_0 fimaundir_2 cres crn fimaundir_1 fimaundir_2 cres crn cun fimaundir_0 fimaundir_1 cun fimaundir_2 df-ima fimaundir_0 fimaundir_1 cun fimaundir_2 cres fimaundir_0 fimaundir_2 cres fimaundir_1 fimaundir_2 cres cun fimaundir_0 fimaundir_1 fimaundir_2 resundir rneqi fimaundir_0 fimaundir_2 cres fimaundir_1 fimaundir_2 cres rnun 3eqtri fimaundir_0 fimaundir_2 cima fimaundir_0 fimaundir_2 cres crn fimaundir_1 fimaundir_2 cima fimaundir_1 fimaundir_2 cres crn fimaundir_0 fimaundir_2 df-ima fimaundir_1 fimaundir_2 df-ima uneq12i eqtr4i $.
$}
$( An upper bound for intersection with a domain.  Theorem 40 of [Suppes]
       p. 66, who calls it "somewhat surprising."  (Contributed by NM,
       11-Aug-2004.) $)
${
	$d x y A $.
	$d x y $.
	$d x y R $.
	idminss_0 $f set x $.
	idminss_1 $f set y $.
	fdminss_0 $f class A $.
	fdminss_1 $f class R $.
	dminss $p |- ( dom R i^i A ) C_ ( `' R " ( R " A ) ) $= idminss_0 fdminss_1 cdm fdminss_0 cin fdminss_1 ccnv fdminss_1 fdminss_0 cima cima idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel wa idminss_1 wex idminss_1 sup_set_class fdminss_1 fdminss_0 cima wcel idminss_1 sup_set_class idminss_0 sup_set_class fdminss_1 ccnv wbr wa idminss_1 wex idminss_0 sup_set_class fdminss_1 cdm fdminss_0 cin wcel idminss_0 sup_set_class fdminss_1 ccnv fdminss_1 fdminss_0 cima cima wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel wa idminss_1 sup_set_class fdminss_1 fdminss_0 cima wcel idminss_1 sup_set_class idminss_0 sup_set_class fdminss_1 ccnv wbr wa idminss_1 idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel wa idminss_1 sup_set_class fdminss_1 fdminss_0 cima wcel idminss_1 sup_set_class idminss_0 sup_set_class fdminss_1 ccnv wbr idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel wa idminss_0 sup_set_class fdminss_0 wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr wa idminss_0 wex idminss_1 sup_set_class fdminss_1 fdminss_0 cima wcel idminss_0 sup_set_class fdminss_0 wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr wa idminss_0 wex idminss_0 sup_set_class fdminss_0 wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr wa idminss_0 19.8a ancoms idminss_0 idminss_1 sup_set_class fdminss_1 fdminss_0 idminss_1 vex elima2 sylibr idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel wa idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_1 sup_set_class idminss_0 sup_set_class fdminss_1 ccnv wbr idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel simpl idminss_1 sup_set_class idminss_0 sup_set_class fdminss_1 idminss_1 vex idminss_0 vex brcnv sylibr jca eximi idminss_0 sup_set_class fdminss_1 cdm wcel idminss_0 sup_set_class fdminss_0 wcel wa idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_1 wex idminss_0 sup_set_class fdminss_0 wcel wa idminss_0 sup_set_class fdminss_1 cdm fdminss_0 cin wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel wa idminss_1 wex idminss_0 sup_set_class fdminss_1 cdm wcel idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_1 wex idminss_0 sup_set_class fdminss_0 wcel idminss_1 idminss_0 sup_set_class fdminss_1 idminss_0 vex eldm anbi1i idminss_0 sup_set_class fdminss_1 cdm fdminss_0 elin idminss_0 sup_set_class idminss_1 sup_set_class fdminss_1 wbr idminss_0 sup_set_class fdminss_0 wcel idminss_1 19.41v 3bitr4i idminss_1 idminss_0 sup_set_class fdminss_1 ccnv fdminss_1 fdminss_0 cima idminss_0 vex elima2 3imtr4i ssriv $.
$}
$( An upper bound for intersection with an image.  Theorem 41 of [Suppes]
       p. 66.  (Contributed by NM, 11-Aug-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y R $.
	iimainss_0 $f set x $.
	iimainss_1 $f set y $.
	fimainss_0 $f class A $.
	fimainss_1 $f class B $.
	fimainss_2 $f class R $.
	imainss $p |- ( ( R " A ) i^i B ) C_ ( R " ( A i^i ( `' R " B ) ) ) $= iimainss_1 fimainss_2 fimainss_0 cima fimainss_1 cin fimainss_2 fimainss_0 fimainss_2 ccnv fimainss_1 cima cin cima iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_0 wex iimainss_0 sup_set_class fimainss_0 fimainss_2 ccnv fimainss_1 cima cin wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 wex iimainss_1 sup_set_class fimainss_2 fimainss_0 cima fimainss_1 cin wcel iimainss_1 sup_set_class fimainss_2 fimainss_0 fimainss_2 ccnv fimainss_1 cima cin cima wcel iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_0 sup_set_class fimainss_0 fimainss_2 ccnv fimainss_1 cima cin wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex wa iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 sup_set_class fimainss_0 fimainss_2 ccnv fimainss_1 cima cin wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_1 sup_set_class fimainss_1 wcel iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex wa iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_1 sup_set_class fimainss_1 wcel wa wa iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex wa iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 iimainss_1 vex iimainss_0 vex brcnv iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 19.8a sylan2br ancoms anim2i iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_1 sup_set_class fimainss_1 wcel simprl jca anassrs iimainss_0 sup_set_class fimainss_0 fimainss_2 ccnv fimainss_1 cima cin wcel iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex wa iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr iimainss_0 sup_set_class fimainss_0 fimainss_2 ccnv fimainss_1 cima cin wcel iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class fimainss_2 ccnv fimainss_1 cima wcel wa iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex wa iimainss_0 sup_set_class fimainss_0 fimainss_2 ccnv fimainss_1 cima elin iimainss_0 sup_set_class fimainss_2 ccnv fimainss_1 cima wcel iimainss_1 sup_set_class fimainss_1 wcel iimainss_1 sup_set_class iimainss_0 sup_set_class fimainss_2 ccnv wbr wa iimainss_1 wex iimainss_0 sup_set_class fimainss_0 wcel iimainss_1 iimainss_0 sup_set_class fimainss_2 ccnv fimainss_1 iimainss_0 vex elima2 anbi2i bitri anbi1i sylibr eximi iimainss_1 sup_set_class fimainss_2 fimainss_0 cima wcel iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 wex iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_1 sup_set_class fimainss_2 fimainss_0 cima fimainss_1 cin wcel iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_1 sup_set_class fimainss_1 wcel wa iimainss_0 wex iimainss_1 sup_set_class fimainss_2 fimainss_0 cima wcel iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_0 wex iimainss_1 sup_set_class fimainss_1 wcel iimainss_0 iimainss_1 sup_set_class fimainss_2 fimainss_0 iimainss_1 vex elima2 anbi1i iimainss_1 sup_set_class fimainss_2 fimainss_0 cima fimainss_1 elin iimainss_0 sup_set_class fimainss_0 wcel iimainss_0 sup_set_class iimainss_1 sup_set_class fimainss_2 wbr wa iimainss_1 sup_set_class fimainss_1 wcel iimainss_0 19.41v 3bitr4i iimainss_0 iimainss_1 sup_set_class fimainss_2 fimainss_0 fimainss_2 ccnv fimainss_1 cima cin iimainss_1 vex elima2 3imtr4i ssriv $.
$}
$( The converse of a cross product.  Exercise 11 of [Suppes] p. 67.
       (Contributed by NM, 14-Aug-1999.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
${
	$d x y A $.
	$d x y B $.
	icnvxp_0 $f set x $.
	icnvxp_1 $f set y $.
	fcnvxp_0 $f class A $.
	fcnvxp_1 $f class B $.
	cnvxp $p |- `' ( A X. B ) = ( B X. A ) $= icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel wa icnvxp_1 icnvxp_0 copab ccnv icnvxp_0 sup_set_class fcnvxp_1 wcel icnvxp_1 sup_set_class fcnvxp_0 wcel wa icnvxp_0 icnvxp_1 copab fcnvxp_0 fcnvxp_1 cxp ccnv fcnvxp_1 fcnvxp_0 cxp icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel wa icnvxp_1 icnvxp_0 copab ccnv icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel wa icnvxp_0 icnvxp_1 copab icnvxp_0 sup_set_class fcnvxp_1 wcel icnvxp_1 sup_set_class fcnvxp_0 wcel wa icnvxp_0 icnvxp_1 copab icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel wa icnvxp_1 icnvxp_0 cnvopab icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel wa icnvxp_0 sup_set_class fcnvxp_1 wcel icnvxp_1 sup_set_class fcnvxp_0 wcel wa icnvxp_0 icnvxp_1 icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel ancom opabbii eqtri fcnvxp_0 fcnvxp_1 cxp icnvxp_1 sup_set_class fcnvxp_0 wcel icnvxp_0 sup_set_class fcnvxp_1 wcel wa icnvxp_1 icnvxp_0 copab icnvxp_1 icnvxp_0 fcnvxp_0 fcnvxp_1 df-xp cnveqi icnvxp_0 icnvxp_1 fcnvxp_1 fcnvxp_0 df-xp 3eqtr4i $.
$}
$( The cross product with the empty set is empty.  Part of Theorem 3.13(ii)
     of [Monk1] p. 37.  (Contributed by NM, 12-Apr-2004.) $)
${
	fxp0_0 $f class A $.
	xp0 $p |- ( A X. (/) ) = (/) $= c0 fxp0_0 cxp ccnv c0 ccnv fxp0_0 c0 cxp c0 c0 fxp0_0 cxp c0 fxp0_0 xp0r cnveqi c0 fxp0_0 cnvxp cnv0 3eqtr3i $.
$}
$( The cross product of nonempty classes is nonempty.  (Variation of a
       theorem contributed by Raph Levien, 30-Jun-2006.)  (Contributed by NM,
       30-Jun-2006.) $)
${
	$d x y z A $.
	$d x y z B $.
	ixpnz_0 $f set x $.
	ixpnz_1 $f set y $.
	ixpnz_2 $f set z $.
	fxpnz_0 $f class A $.
	fxpnz_1 $f class B $.
	xpnz $p |- ( ( A =/= (/) /\ B =/= (/) ) <-> ( A X. B ) =/= (/) ) $= fxpnz_0 c0 wne fxpnz_1 c0 wne wa fxpnz_0 fxpnz_1 cxp c0 wne fxpnz_0 c0 wne fxpnz_1 c0 wne wa ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel wa ixpnz_1 wex ixpnz_0 wex fxpnz_0 fxpnz_1 cxp c0 wne fxpnz_0 c0 wne fxpnz_1 c0 wne wa ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_0 wex ixpnz_1 sup_set_class fxpnz_1 wcel ixpnz_1 wex wa ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel wa ixpnz_1 wex ixpnz_0 wex fxpnz_0 c0 wne ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_0 wex fxpnz_1 c0 wne ixpnz_1 sup_set_class fxpnz_1 wcel ixpnz_1 wex ixpnz_0 fxpnz_0 n0 ixpnz_1 fxpnz_1 n0 anbi12i ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel ixpnz_0 ixpnz_1 eeanv bitr4i ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel wa fxpnz_0 fxpnz_1 cxp c0 wne ixpnz_0 ixpnz_1 ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel wa ixpnz_2 sup_set_class fxpnz_0 fxpnz_1 cxp wcel ixpnz_2 wex fxpnz_0 fxpnz_1 cxp c0 wne ixpnz_2 sup_set_class fxpnz_0 fxpnz_1 cxp wcel ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel wa ixpnz_2 ixpnz_0 sup_set_class ixpnz_1 sup_set_class cop ixpnz_0 sup_set_class ixpnz_1 sup_set_class opex ixpnz_2 sup_set_class ixpnz_0 sup_set_class ixpnz_1 sup_set_class cop wceq ixpnz_2 sup_set_class fxpnz_0 fxpnz_1 cxp wcel ixpnz_0 sup_set_class ixpnz_1 sup_set_class cop fxpnz_0 fxpnz_1 cxp wcel ixpnz_0 sup_set_class fxpnz_0 wcel ixpnz_1 sup_set_class fxpnz_1 wcel wa ixpnz_2 sup_set_class ixpnz_0 sup_set_class ixpnz_1 sup_set_class cop fxpnz_0 fxpnz_1 cxp eleq1 ixpnz_0 sup_set_class ixpnz_1 sup_set_class fxpnz_0 fxpnz_1 opelxp syl6bb spcev ixpnz_2 fxpnz_0 fxpnz_1 cxp n0 sylibr exlimivv sylbi fxpnz_0 fxpnz_1 cxp c0 wne fxpnz_0 c0 wne fxpnz_1 c0 wne fxpnz_0 c0 fxpnz_0 fxpnz_1 cxp c0 fxpnz_0 c0 wceq fxpnz_0 fxpnz_1 cxp c0 fxpnz_1 cxp c0 fxpnz_0 c0 fxpnz_1 xpeq1 fxpnz_1 xp0r syl6eq necon3i fxpnz_1 c0 fxpnz_0 fxpnz_1 cxp c0 fxpnz_1 c0 wceq fxpnz_0 fxpnz_1 cxp fxpnz_0 c0 cxp c0 fxpnz_1 c0 fxpnz_0 xpeq2 fxpnz_0 xp0 syl6eq necon3i jca impbii $.
$}
$( At least one member of an empty cross product is empty.  (Contributed by
     NM, 27-Aug-2006.) $)
${
	fxpeq0_0 $f class A $.
	fxpeq0_1 $f class B $.
	xpeq0 $p |- ( ( A X. B ) = (/) <-> ( A = (/) \/ B = (/) ) ) $= fxpeq0_0 fxpeq0_1 cxp c0 wceq fxpeq0_0 c0 wne fxpeq0_1 c0 wne wa wn fxpeq0_0 c0 wne wn fxpeq0_1 c0 wne wn wo fxpeq0_0 c0 wceq fxpeq0_1 c0 wceq wo fxpeq0_0 c0 wne fxpeq0_1 c0 wne wa fxpeq0_0 fxpeq0_1 cxp c0 fxpeq0_0 fxpeq0_1 xpnz necon2bbii fxpeq0_0 c0 wne fxpeq0_1 c0 wne ianor fxpeq0_0 c0 wne wn fxpeq0_0 c0 wceq fxpeq0_1 c0 wne wn fxpeq0_1 c0 wceq fxpeq0_0 c0 nne fxpeq0_1 c0 nne orbi12i 3bitri $.
$}
$( Cross products with disjoint sets are disjoint.  (Contributed by NM,
     13-Sep-2004.) $)
${
	fxpdisj1_0 $f class A $.
	fxpdisj1_1 $f class B $.
	fxpdisj1_2 $f class C $.
	fxpdisj1_3 $f class D $.
	xpdisj1 $p |- ( ( A i^i B ) = (/) -> ( ( A X. C ) i^i ( B X. D ) ) = (/) ) $= fxpdisj1_0 fxpdisj1_1 cin c0 wceq fxpdisj1_0 fxpdisj1_2 cxp fxpdisj1_1 fxpdisj1_3 cxp cin fxpdisj1_0 fxpdisj1_1 cin fxpdisj1_2 fxpdisj1_3 cin cxp c0 fxpdisj1_0 fxpdisj1_2 fxpdisj1_1 fxpdisj1_3 inxp fxpdisj1_0 fxpdisj1_1 cin c0 wceq fxpdisj1_0 fxpdisj1_1 cin fxpdisj1_2 fxpdisj1_3 cin cxp c0 fxpdisj1_2 fxpdisj1_3 cin cxp c0 fxpdisj1_0 fxpdisj1_1 cin c0 fxpdisj1_2 fxpdisj1_3 cin xpeq1 fxpdisj1_2 fxpdisj1_3 cin xp0r syl6eq syl5eq $.
$}
$( Cross products with disjoint sets are disjoint.  (Contributed by NM,
     13-Sep-2004.) $)
${
	fxpdisj2_0 $f class A $.
	fxpdisj2_1 $f class B $.
	fxpdisj2_2 $f class C $.
	fxpdisj2_3 $f class D $.
	xpdisj2 $p |- ( ( A i^i B ) = (/) -> ( ( C X. A ) i^i ( D X. B ) ) = (/) ) $= fxpdisj2_0 fxpdisj2_1 cin c0 wceq fxpdisj2_2 fxpdisj2_0 cxp fxpdisj2_3 fxpdisj2_1 cxp cin fxpdisj2_2 fxpdisj2_3 cin fxpdisj2_0 fxpdisj2_1 cin cxp c0 fxpdisj2_2 fxpdisj2_0 fxpdisj2_3 fxpdisj2_1 inxp fxpdisj2_0 fxpdisj2_1 cin c0 wceq fxpdisj2_2 fxpdisj2_3 cin fxpdisj2_0 fxpdisj2_1 cin cxp fxpdisj2_2 fxpdisj2_3 cin c0 cxp c0 fxpdisj2_0 fxpdisj2_1 cin c0 fxpdisj2_2 fxpdisj2_3 cin xpeq2 fxpdisj2_2 fxpdisj2_3 cin xp0 syl6eq syl5eq $.
$}
$( Cross products with two different singletons are disjoint.  (Contributed
     by NM, 28-Jul-2004.) $)
${
	fxpsndisj_0 $f class A $.
	fxpsndisj_1 $f class B $.
	fxpsndisj_2 $f class C $.
	fxpsndisj_3 $f class D $.
	xpsndisj $p |- ( B =/= D -> ( ( A X. { B } ) i^i ( C X. { D } ) ) = (/) ) $= fxpsndisj_1 fxpsndisj_3 wne fxpsndisj_1 csn fxpsndisj_3 csn cin c0 wceq fxpsndisj_0 fxpsndisj_1 csn cxp fxpsndisj_2 fxpsndisj_3 csn cxp cin c0 wceq fxpsndisj_1 fxpsndisj_3 disjsn2 fxpsndisj_1 csn fxpsndisj_3 csn fxpsndisj_0 fxpsndisj_2 xpdisj2 syl $.
$}
$( Disjoint unions with disjoint index sets are disjoint.  (Contributed by
       Stefan O'Rear, 21-Nov-2014.) $)
${
	$d x A $.
	$d y B $.
	fdjudisj_0 $f set x $.
	fdjudisj_1 $f set y $.
	fdjudisj_2 $f class A $.
	fdjudisj_3 $f class B $.
	fdjudisj_4 $f class C $.
	fdjudisj_5 $f class D $.
	djudisj $p |- ( ( A i^i B ) = (/) -> ( U_ x e. A ( { x } X. C ) i^i U_ y e. B ( { y } X. D ) ) = (/) ) $= fdjudisj_2 fdjudisj_3 cin c0 wceq fdjudisj_0 fdjudisj_2 fdjudisj_0 sup_set_class csn fdjudisj_4 cxp ciun fdjudisj_2 cvv cxp wss fdjudisj_2 cvv cxp fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun cin c0 wceq fdjudisj_0 fdjudisj_2 fdjudisj_0 sup_set_class csn fdjudisj_4 cxp ciun fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun cin c0 wceq fdjudisj_0 fdjudisj_2 fdjudisj_4 djussxp fdjudisj_2 fdjudisj_3 cin c0 wceq fdjudisj_2 cvv cxp fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun cin fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun fdjudisj_2 cvv cxp cin c0 fdjudisj_2 cvv cxp fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun incom fdjudisj_2 fdjudisj_3 cin c0 wceq fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun fdjudisj_3 cvv cxp wss fdjudisj_3 cvv cxp fdjudisj_2 cvv cxp cin c0 wceq fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun fdjudisj_2 cvv cxp cin c0 wceq fdjudisj_1 fdjudisj_3 fdjudisj_5 djussxp fdjudisj_2 fdjudisj_3 cin c0 wceq fdjudisj_3 cvv cxp fdjudisj_2 cvv cxp cin fdjudisj_2 cvv cxp fdjudisj_3 cvv cxp cin c0 fdjudisj_3 cvv cxp fdjudisj_2 cvv cxp incom fdjudisj_2 fdjudisj_3 cvv cvv xpdisj1 syl5eq fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun fdjudisj_3 cvv cxp fdjudisj_2 cvv cxp ssdisj sylancr syl5eq fdjudisj_0 fdjudisj_2 fdjudisj_0 sup_set_class csn fdjudisj_4 cxp ciun fdjudisj_2 cvv cxp fdjudisj_1 fdjudisj_3 fdjudisj_1 sup_set_class csn fdjudisj_5 cxp ciun ssdisj sylancr $.
$}
$( A double restriction to disjoint classes is the empty set.  (Contributed
     by NM, 7-Oct-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	fresdisj_0 $f class A $.
	fresdisj_1 $f class B $.
	fresdisj_2 $f class C $.
	resdisj $p |- ( ( A i^i B ) = (/) -> ( ( C |` A ) |` B ) = (/) ) $= fresdisj_0 fresdisj_1 cin c0 wceq fresdisj_2 fresdisj_0 cres fresdisj_1 cres fresdisj_2 fresdisj_0 fresdisj_1 cin cres c0 fresdisj_2 fresdisj_0 fresdisj_1 resres fresdisj_0 fresdisj_1 cin c0 wceq fresdisj_2 fresdisj_0 fresdisj_1 cin cres fresdisj_2 c0 cres c0 fresdisj_0 fresdisj_1 cin c0 fresdisj_2 reseq2 fresdisj_2 res0 syl6eq syl5eq $.
$}
$( The range of a cross product.  Part of Theorem 3.13(x) of [Monk1] p. 37.
     (Contributed by NM, 12-Apr-2004.) $)
${
	frnxp_0 $f class A $.
	frnxp_1 $f class B $.
	rnxp $p |- ( A =/= (/) -> ran ( A X. B ) = B ) $= frnxp_0 c0 wne frnxp_0 frnxp_1 cxp crn frnxp_1 frnxp_0 cxp cdm frnxp_1 frnxp_0 frnxp_1 cxp crn frnxp_0 frnxp_1 cxp ccnv cdm frnxp_1 frnxp_0 cxp cdm frnxp_0 frnxp_1 cxp df-rn frnxp_0 frnxp_1 cxp ccnv frnxp_1 frnxp_0 cxp frnxp_0 frnxp_1 cnvxp dmeqi eqtri frnxp_1 frnxp_0 dmxp syl5eq $.
$}
$( The domain of a cross product is a subclass of the first factor.
     (Contributed by NM, 19-Mar-2007.) $)
${
	fdmxpss_0 $f class A $.
	fdmxpss_1 $f class B $.
	dmxpss $p |- dom ( A X. B ) C_ A $= fdmxpss_0 fdmxpss_1 cxp cdm fdmxpss_0 wss fdmxpss_1 c0 fdmxpss_1 c0 wceq fdmxpss_0 fdmxpss_1 cxp cdm fdmxpss_0 wss c0 fdmxpss_0 wss fdmxpss_0 0ss fdmxpss_1 c0 wceq fdmxpss_0 fdmxpss_1 cxp cdm c0 fdmxpss_0 fdmxpss_1 c0 wceq fdmxpss_0 fdmxpss_1 cxp cdm c0 cdm c0 fdmxpss_1 c0 wceq fdmxpss_0 fdmxpss_1 cxp c0 fdmxpss_1 c0 wceq fdmxpss_0 fdmxpss_1 cxp fdmxpss_0 c0 cxp c0 fdmxpss_1 c0 fdmxpss_0 xpeq2 fdmxpss_0 xp0 syl6eq dmeqd dm0 syl6eq sseq1d mpbiri fdmxpss_1 c0 wne fdmxpss_0 fdmxpss_1 cxp cdm fdmxpss_0 wceq fdmxpss_0 fdmxpss_1 cxp cdm fdmxpss_0 wss fdmxpss_0 fdmxpss_1 dmxp fdmxpss_0 fdmxpss_1 cxp cdm fdmxpss_0 eqimss syl pm2.61ine $.
$}
$( The range of a cross product is a subclass of the second factor.
     (Contributed by NM, 16-Jan-2006.)  (Proof shortened by Andrew Salmon,
     27-Aug-2011.) $)
${
	frnxpss_0 $f class A $.
	frnxpss_1 $f class B $.
	rnxpss $p |- ran ( A X. B ) C_ B $= frnxpss_0 frnxpss_1 cxp crn frnxpss_0 frnxpss_1 cxp ccnv cdm frnxpss_1 frnxpss_0 frnxpss_1 cxp df-rn frnxpss_0 frnxpss_1 cxp ccnv cdm frnxpss_1 frnxpss_0 cxp cdm frnxpss_1 frnxpss_0 frnxpss_1 cxp ccnv frnxpss_1 frnxpss_0 cxp frnxpss_0 frnxpss_1 cnvxp dmeqi frnxpss_1 frnxpss_0 dmxpss eqsstri eqsstri $.
$}
$( The range of a square cross product.  (Contributed by FL, 17-May-2010.) $)
${
	frnxpid_0 $f class A $.
	rnxpid $p |- ran ( A X. A ) = A $= frnxpid_0 frnxpid_0 cxp crn frnxpid_0 wceq frnxpid_0 c0 frnxpid_0 c0 wceq c0 crn c0 frnxpid_0 frnxpid_0 cxp crn frnxpid_0 rn0 frnxpid_0 c0 wceq frnxpid_0 frnxpid_0 cxp c0 frnxpid_0 c0 wceq frnxpid_0 frnxpid_0 cxp frnxpid_0 c0 cxp c0 frnxpid_0 c0 frnxpid_0 xpeq2 frnxpid_0 xp0 syl6eq rneqd frnxpid_0 c0 wceq id 3eqtr4a frnxpid_0 frnxpid_0 rnxp pm2.61ine $.
$}
$( A cross-product subclass relationship is equivalent to the relationship
     for it components.  (Contributed by NM, 17-Dec-2008.) $)
${
	fssxpb_0 $f class A $.
	fssxpb_1 $f class B $.
	fssxpb_2 $f class C $.
	fssxpb_3 $f class D $.
	ssxpb $p |- ( ( A X. B ) =/= (/) -> ( ( A X. B ) C_ ( C X. D ) <-> ( A C_ C /\ B C_ D ) ) ) $= fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss fssxpb_0 fssxpb_2 wss fssxpb_1 fssxpb_3 wss wa fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss fssxpb_0 fssxpb_2 wss fssxpb_1 fssxpb_3 wss wa fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss wa fssxpb_0 fssxpb_2 wss fssxpb_1 fssxpb_3 wss fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss wa fssxpb_0 fssxpb_2 fssxpb_3 cxp cdm fssxpb_2 fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss wa fssxpb_0 fssxpb_0 fssxpb_1 cxp cdm fssxpb_2 fssxpb_3 cxp cdm fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp cdm fssxpb_0 wceq fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 c0 wne fssxpb_1 c0 wne wa fssxpb_0 fssxpb_1 cxp cdm fssxpb_0 wceq fssxpb_0 fssxpb_1 xpnz fssxpb_1 c0 wne fssxpb_0 fssxpb_1 cxp cdm fssxpb_0 wceq fssxpb_0 c0 wne fssxpb_0 fssxpb_1 dmxp adantl sylbir adantr fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss fssxpb_0 fssxpb_1 cxp cdm fssxpb_2 fssxpb_3 cxp cdm wss fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp dmss adantl eqsstr3d fssxpb_2 fssxpb_3 dmxpss syl6ss fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss wa fssxpb_1 fssxpb_2 fssxpb_3 cxp crn fssxpb_3 fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss wa fssxpb_1 fssxpb_0 fssxpb_1 cxp crn fssxpb_2 fssxpb_3 cxp crn fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp crn fssxpb_1 wceq fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 c0 wne fssxpb_1 c0 wne wa fssxpb_0 fssxpb_1 cxp crn fssxpb_1 wceq fssxpb_0 fssxpb_1 xpnz fssxpb_0 c0 wne fssxpb_0 fssxpb_1 cxp crn fssxpb_1 wceq fssxpb_1 c0 wne fssxpb_0 fssxpb_1 rnxp adantr sylbir adantr fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp wss fssxpb_0 fssxpb_1 cxp crn fssxpb_2 fssxpb_3 cxp crn wss fssxpb_0 fssxpb_1 cxp c0 wne fssxpb_0 fssxpb_1 cxp fssxpb_2 fssxpb_3 cxp rnss adantl eqsstr3d fssxpb_2 fssxpb_3 rnxpss syl6ss jca ex fssxpb_0 fssxpb_2 fssxpb_1 fssxpb_3 xpss12 impbid1 $.
$}
$( The cross product of non-empty classes is one-to-one.  (Contributed by NM,
     31-May-2008.) $)
${
	fxp11_0 $f class A $.
	fxp11_1 $f class B $.
	fxp11_2 $f class C $.
	fxp11_3 $f class D $.
	xp11 $p |- ( ( A =/= (/) /\ B =/= (/) ) -> ( ( A X. B ) = ( C X. D ) <-> ( A = C /\ B = D ) ) ) $= fxp11_0 c0 wne fxp11_1 c0 wne wa fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_2 wceq fxp11_1 fxp11_3 wceq wa fxp11_0 c0 wne fxp11_1 c0 wne wa fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_2 wceq fxp11_1 fxp11_3 wceq wa wi fxp11_0 fxp11_1 xpnz fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_2 wceq fxp11_1 fxp11_3 wceq wa fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_1 cxp c0 wne fxp11_2 fxp11_3 cxp c0 wne wa fxp11_0 fxp11_2 wceq fxp11_1 fxp11_3 wceq wa fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_1 cxp c0 wne wa fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp c0 wne fxp11_2 fxp11_3 cxp c0 wne wa fxp11_0 fxp11_1 cxp c0 wne anidm fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp c0 wne fxp11_2 fxp11_3 cxp c0 wne fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp c0 neeq1 anbi2d syl5bbr fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp c0 wne fxp11_2 fxp11_3 cxp c0 wne wa fxp11_0 fxp11_2 wss fxp11_1 fxp11_3 wss wa fxp11_2 fxp11_0 wss fxp11_3 fxp11_1 wss wa wa fxp11_0 fxp11_2 wceq fxp11_1 fxp11_3 wceq wa fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_2 wss fxp11_1 fxp11_3 wss wa fxp11_2 fxp11_3 cxp c0 wne fxp11_2 fxp11_0 wss fxp11_3 fxp11_1 wss wa fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wss fxp11_0 fxp11_1 cxp c0 wne fxp11_0 fxp11_2 wss fxp11_1 fxp11_3 wss wa fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp eqimss fxp11_0 fxp11_1 fxp11_2 fxp11_3 ssxpb syl5ibcom fxp11_0 fxp11_1 cxp fxp11_2 fxp11_3 cxp wceq fxp11_2 fxp11_3 cxp fxp11_0 fxp11_1 cxp wss fxp11_2 fxp11_3 cxp c0 wne fxp11_2 fxp11_0 wss fxp11_3 fxp11_1 wss wa fxp11_2 fxp11_3 cxp fxp11_0 fxp11_1 cxp eqimss2 fxp11_2 fxp11_3 fxp11_0 fxp11_1 ssxpb syl5ibcom anim12d fxp11_0 fxp11_2 wss fxp11_1 fxp11_3 wss wa fxp11_2 fxp11_0 wss fxp11_3 fxp11_1 wss wa wa fxp11_0 fxp11_2 wss fxp11_2 fxp11_0 wss wa fxp11_1 fxp11_3 wss fxp11_3 fxp11_1 wss wa wa fxp11_0 fxp11_2 wceq fxp11_1 fxp11_3 wceq wa fxp11_0 fxp11_2 wss fxp11_1 fxp11_3 wss fxp11_2 fxp11_0 wss fxp11_3 fxp11_1 wss an4 fxp11_0 fxp11_2 wceq fxp11_0 fxp11_2 wss fxp11_2 fxp11_0 wss wa fxp11_1 fxp11_3 wceq fxp11_1 fxp11_3 wss fxp11_3 fxp11_1 wss wa fxp11_0 fxp11_2 eqss fxp11_1 fxp11_3 eqss anbi12i bitr4i syl6ib sylbid com12 sylbi fxp11_0 fxp11_2 fxp11_1 fxp11_3 xpeq12 impbid1 $.
$}
$( Cancellation law for cross-product.  (Contributed by NM, 30-Aug-2011.) $)
${
	fxpcan_0 $f class A $.
	fxpcan_1 $f class B $.
	fxpcan_2 $f class C $.
	xpcan $p |- ( C =/= (/) -> ( ( C X. A ) = ( C X. B ) <-> A = B ) ) $= fxpcan_2 c0 wne fxpcan_0 c0 wne fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_0 fxpcan_1 wceq wb fxpcan_2 c0 wne fxpcan_0 c0 wne wa fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_2 fxpcan_2 wceq fxpcan_0 fxpcan_1 wceq wa fxpcan_0 fxpcan_1 wceq fxpcan_2 fxpcan_0 fxpcan_2 fxpcan_1 xp11 fxpcan_2 fxpcan_2 wceq fxpcan_0 fxpcan_1 wceq fxpcan_2 eqid biantrur syl6bbr fxpcan_2 c0 wne fxpcan_0 c0 wne wn wa fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_0 fxpcan_1 wceq fxpcan_0 c0 wne wn fxpcan_2 c0 wne fxpcan_0 c0 wceq fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_0 fxpcan_1 wceq wi fxpcan_0 c0 nne fxpcan_2 c0 wne fxpcan_0 c0 wceq wa fxpcan_0 c0 wceq fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_1 c0 wceq fxpcan_0 fxpcan_1 wceq fxpcan_2 c0 wne fxpcan_0 c0 wceq simpr fxpcan_2 c0 wne fxpcan_0 c0 wceq wa fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_2 fxpcan_1 cxp c0 wceq fxpcan_1 c0 wceq fxpcan_0 c0 wceq fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq fxpcan_2 fxpcan_1 cxp c0 wceq wb fxpcan_2 c0 wne fxpcan_0 c0 wceq fxpcan_2 fxpcan_0 cxp fxpcan_2 fxpcan_1 cxp wceq c0 fxpcan_2 fxpcan_1 cxp wceq fxpcan_2 fxpcan_1 cxp c0 wceq fxpcan_0 c0 wceq fxpcan_2 fxpcan_0 cxp c0 fxpcan_2 fxpcan_1 cxp fxpcan_0 c0 wceq fxpcan_2 fxpcan_0 cxp fxpcan_2 c0 cxp c0 fxpcan_0 c0 fxpcan_2 xpeq2 fxpcan_2 xp0 syl6eq eqeq1d c0 fxpcan_2 fxpcan_1 cxp eqcom syl6bb adantl fxpcan_2 c0 wne fxpcan_2 fxpcan_1 cxp c0 wceq fxpcan_1 c0 wceq wi fxpcan_0 c0 wceq fxpcan_2 c0 wne fxpcan_2 c0 wceq wn fxpcan_2 fxpcan_1 cxp c0 wceq fxpcan_1 c0 wceq wi fxpcan_2 c0 df-ne fxpcan_2 fxpcan_1 cxp c0 wceq fxpcan_2 c0 wceq fxpcan_1 c0 wceq wo fxpcan_2 c0 wceq wn fxpcan_1 c0 wceq fxpcan_2 fxpcan_1 xpeq0 fxpcan_2 c0 wceq fxpcan_1 c0 wceq orel1 syl5bi sylbi adantr sylbid fxpcan_0 fxpcan_1 c0 eqtr3 ee12an sylan2b fxpcan_0 fxpcan_1 fxpcan_2 xpeq2 impbid1 pm2.61dan $.
$}
$( Cancellation law for cross-product.  (Contributed by NM, 30-Aug-2011.) $)
${
	fxpcan2_0 $f class A $.
	fxpcan2_1 $f class B $.
	fxpcan2_2 $f class C $.
	xpcan2 $p |- ( C =/= (/) -> ( ( A X. C ) = ( B X. C ) <-> A = B ) ) $= fxpcan2_0 c0 wne fxpcan2_2 c0 wne fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_0 fxpcan2_1 wceq wb fxpcan2_0 c0 wne fxpcan2_2 c0 wne wa fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_0 fxpcan2_1 wceq fxpcan2_2 fxpcan2_2 wceq wa fxpcan2_0 fxpcan2_1 wceq fxpcan2_0 fxpcan2_2 fxpcan2_1 fxpcan2_2 xp11 fxpcan2_2 fxpcan2_2 wceq fxpcan2_0 fxpcan2_1 wceq fxpcan2_2 eqid biantru syl6bbr fxpcan2_0 c0 wne wn fxpcan2_0 c0 wceq fxpcan2_2 c0 wne fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_0 fxpcan2_1 wceq wb fxpcan2_0 c0 nne fxpcan2_0 c0 wceq fxpcan2_2 c0 wne wa fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_0 fxpcan2_1 wceq fxpcan2_0 c0 wceq fxpcan2_2 c0 wne wa fxpcan2_0 c0 wceq fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_1 c0 wceq fxpcan2_0 fxpcan2_1 wceq fxpcan2_0 c0 wceq fxpcan2_2 c0 wne simpl fxpcan2_0 c0 wceq fxpcan2_2 c0 wne wa fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_1 fxpcan2_2 cxp c0 wceq fxpcan2_1 c0 wceq fxpcan2_0 c0 wceq fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_1 fxpcan2_2 cxp c0 wceq wb fxpcan2_2 c0 wne fxpcan2_0 c0 wceq fxpcan2_0 fxpcan2_2 cxp fxpcan2_1 fxpcan2_2 cxp wceq c0 fxpcan2_1 fxpcan2_2 cxp wceq fxpcan2_1 fxpcan2_2 cxp c0 wceq fxpcan2_0 c0 wceq fxpcan2_0 fxpcan2_2 cxp c0 fxpcan2_1 fxpcan2_2 cxp fxpcan2_0 c0 wceq fxpcan2_0 fxpcan2_2 cxp c0 fxpcan2_2 cxp c0 fxpcan2_0 c0 fxpcan2_2 xpeq1 fxpcan2_2 xp0r syl6eq eqeq1d c0 fxpcan2_1 fxpcan2_2 cxp eqcom syl6bb adantr fxpcan2_2 c0 wne fxpcan2_1 fxpcan2_2 cxp c0 wceq fxpcan2_1 c0 wceq wi fxpcan2_0 c0 wceq fxpcan2_2 c0 wne fxpcan2_2 c0 wceq wn fxpcan2_1 fxpcan2_2 cxp c0 wceq fxpcan2_1 c0 wceq wi fxpcan2_2 c0 df-ne fxpcan2_1 fxpcan2_2 cxp c0 wceq fxpcan2_1 c0 wceq fxpcan2_2 c0 wceq wo fxpcan2_2 c0 wceq wn fxpcan2_1 c0 wceq fxpcan2_1 fxpcan2_2 xpeq0 fxpcan2_2 c0 wceq fxpcan2_1 c0 wceq orel2 syl5bi sylbi adantl sylbid fxpcan2_0 fxpcan2_1 c0 eqtr3 ee12an fxpcan2_0 fxpcan2_1 fxpcan2_2 xpeq1 impbid1 sylanb pm2.61ian $.
$}
$( If a cross product is a set, one of its components must be a set.
     (Contributed by NM, 27-Aug-2006.) $)
${
	fxpexr_0 $f class A $.
	fxpexr_1 $f class B $.
	fxpexr_2 $f class C $.
	xpexr $p |- ( ( A X. B ) e. C -> ( A e. _V \/ B e. _V ) ) $= fxpexr_0 fxpexr_1 cxp fxpexr_2 wcel fxpexr_0 cvv wcel fxpexr_1 cvv wcel fxpexr_0 fxpexr_1 cxp fxpexr_2 wcel fxpexr_0 cvv wcel wn fxpexr_1 cvv wcel wi wi fxpexr_0 c0 fxpexr_0 c0 wceq fxpexr_0 cvv wcel wn fxpexr_1 cvv wcel wi fxpexr_0 fxpexr_1 cxp fxpexr_2 wcel fxpexr_0 c0 wceq fxpexr_0 cvv wcel fxpexr_1 cvv wcel fxpexr_0 c0 wceq fxpexr_0 cvv wcel c0 cvv wcel 0ex fxpexr_0 c0 cvv eleq1 mpbiri pm2.24d a1d fxpexr_0 c0 wne fxpexr_0 fxpexr_1 cxp fxpexr_2 wcel fxpexr_1 cvv wcel fxpexr_0 cvv wcel wn fxpexr_0 fxpexr_1 cxp fxpexr_2 wcel fxpexr_0 fxpexr_1 cxp crn cvv wcel fxpexr_0 c0 wne fxpexr_1 cvv wcel fxpexr_0 fxpexr_1 cxp fxpexr_2 rnexg fxpexr_0 c0 wne fxpexr_0 fxpexr_1 cxp crn fxpexr_1 cvv fxpexr_0 fxpexr_1 rnxp eleq1d syl5ib a1dd pm2.61ine orrd $.
$}
$( If a nonempty cross product is a set, so are both of its components.
     (Contributed by NM, 27-Aug-2006.) $)
${
	fxpexr2_0 $f class A $.
	fxpexr2_1 $f class B $.
	fxpexr2_2 $f class C $.
	xpexr2 $p |- ( ( ( A X. B ) e. C /\ ( A X. B ) =/= (/) ) -> ( A e. _V /\ B e. _V ) ) $= fxpexr2_0 fxpexr2_1 cxp c0 wne fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_0 c0 wne fxpexr2_1 c0 wne wa fxpexr2_0 cvv wcel fxpexr2_1 cvv wcel wa fxpexr2_0 fxpexr2_1 xpnz fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_1 c0 wne fxpexr2_0 c0 wne fxpexr2_0 cvv wcel fxpexr2_1 cvv wcel wa fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_1 c0 wne fxpexr2_0 cvv wcel fxpexr2_0 c0 wne fxpexr2_1 cvv wcel fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_1 c0 wne wa fxpexr2_0 fxpexr2_1 cxp cdm fxpexr2_0 cvv fxpexr2_1 c0 wne fxpexr2_0 fxpexr2_1 cxp cdm fxpexr2_0 wceq fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_0 fxpexr2_1 dmxp adantl fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_0 fxpexr2_1 cxp cdm cvv wcel fxpexr2_1 c0 wne fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 dmexg adantr eqeltrrd fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_0 c0 wne wa fxpexr2_0 fxpexr2_1 cxp crn fxpexr2_1 cvv fxpexr2_0 c0 wne fxpexr2_0 fxpexr2_1 cxp crn fxpexr2_1 wceq fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_0 fxpexr2_1 rnxp adantl fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 wcel fxpexr2_0 fxpexr2_1 cxp crn cvv wcel fxpexr2_0 c0 wne fxpexr2_0 fxpexr2_1 cxp fxpexr2_2 rnexg adantr eqeltrrd anim12dan ancom2s sylan2br $.
$}
$( Subset of the range of a restriction.  (Contributed by NM,
       16-Jan-2006.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	issrnres_0 $f set x $.
	issrnres_1 $f set y $.
	fssrnres_0 $f class A $.
	fssrnres_1 $f class B $.
	fssrnres_2 $f class C $.
	ssrnres $p |- ( B C_ ran ( C |` A ) <-> ran ( C i^i ( A X. B ) ) = B ) $= fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_1 wceq fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn wss fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_1 wceq fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_1 wss fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_0 fssrnres_1 cxp crn fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin fssrnres_0 fssrnres_1 cxp wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_0 fssrnres_1 cxp crn wss fssrnres_2 fssrnres_0 fssrnres_1 cxp inss2 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin fssrnres_0 fssrnres_1 cxp rnss ax-mp fssrnres_0 fssrnres_1 rnxpss sstri fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_1 eqss mpbiran fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn wss fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_2 fssrnres_0 cres crn wss fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin fssrnres_2 fssrnres_0 cres wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_2 fssrnres_0 cres crn wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin fssrnres_2 fssrnres_0 cvv cxp cin fssrnres_2 fssrnres_0 cres fssrnres_0 fssrnres_1 cxp fssrnres_0 cvv cxp wss fssrnres_2 fssrnres_0 fssrnres_1 cxp cin fssrnres_2 fssrnres_0 cvv cxp cin wss fssrnres_0 fssrnres_0 wss fssrnres_1 cvv wss fssrnres_0 fssrnres_1 cxp fssrnres_0 cvv cxp wss fssrnres_0 ssid fssrnres_1 ssv fssrnres_0 fssrnres_0 fssrnres_1 cvv xpss12 mp2an fssrnres_0 fssrnres_1 cxp fssrnres_0 cvv cxp fssrnres_2 sslin ax-mp fssrnres_2 fssrnres_0 df-res sseqtr4i fssrnres_2 fssrnres_0 fssrnres_1 cxp cin fssrnres_2 fssrnres_0 cres rnss ax-mp fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_2 fssrnres_0 cres crn sstr mpan2 fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss issrnres_1 fssrnres_1 fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss issrnres_1 sup_set_class fssrnres_1 wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_0 wex issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_1 sup_set_class fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn wcel fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss issrnres_1 sup_set_class fssrnres_1 wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_0 wex fssrnres_1 fssrnres_2 fssrnres_0 cres crn wss issrnres_1 sup_set_class fssrnres_1 wcel issrnres_1 sup_set_class fssrnres_2 fssrnres_0 cres crn wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_0 wex fssrnres_1 fssrnres_2 fssrnres_0 cres crn issrnres_1 sup_set_class ssel issrnres_0 issrnres_1 sup_set_class fssrnres_2 fssrnres_0 cres issrnres_1 vex elrn2 syl6ib ancrd issrnres_1 sup_set_class fssrnres_2 fssrnres_0 fssrnres_1 cxp cin crn wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 fssrnres_1 cxp cin wcel issrnres_0 wex issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 wex issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_0 wex issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 issrnres_1 sup_set_class fssrnres_2 fssrnres_0 fssrnres_1 cxp cin issrnres_1 vex elrn2 issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 fssrnres_1 cxp cin wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 fssrnres_1 cxp cin wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_0 fssrnres_1 cxp wcel wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class fssrnres_0 wcel issrnres_1 sup_set_class fssrnres_1 wcel wa wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 fssrnres_1 cxp elin issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_0 fssrnres_1 cxp wcel issrnres_0 sup_set_class fssrnres_0 wcel issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class issrnres_1 sup_set_class fssrnres_0 fssrnres_1 opelxp anbi2i issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class fssrnres_0 wcel wa issrnres_1 sup_set_class fssrnres_1 wcel wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class fssrnres_0 wcel issrnres_1 sup_set_class fssrnres_1 wcel wa wa issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class fssrnres_0 wcel wa issrnres_1 sup_set_class fssrnres_1 wcel issrnres_0 sup_set_class issrnres_1 sup_set_class fssrnres_2 fssrnres_0 issrnres_1 vex opelres anbi1i issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 wcel issrnres_0 sup_set_class fssrnres_0 wcel issrnres_1 sup_set_class fssrnres_1 wcel anass bitr2i 3bitri exbii issrnres_0 sup_set_class issrnres_1 sup_set_class cop fssrnres_2 fssrnres_0 cres wcel issrnres_1 sup_set_class fssrnres_1 wcel issrnres_0 19.41v 3bitri syl6ibr ssrdv impbii bitr2i $.
$}
$( Range of the intersection with a cross product.  (Contributed by NM,
       17-Jan-2006.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	$d y B $.
	$d x y C $.
	frninxp_0 $f set x $.
	frninxp_1 $f set y $.
	frninxp_2 $f class A $.
	frninxp_3 $f class B $.
	frninxp_4 $f class C $.
	rninxp $p |- ( ran ( C i^i ( A X. B ) ) = B <-> A. y e. B E. x e. A x C y ) $= frninxp_3 frninxp_4 frninxp_2 cres crn wss frninxp_1 sup_set_class frninxp_4 frninxp_2 cres crn wcel frninxp_1 frninxp_3 wral frninxp_4 frninxp_2 frninxp_3 cxp cin crn frninxp_3 wceq frninxp_0 sup_set_class frninxp_1 sup_set_class frninxp_4 wbr frninxp_0 frninxp_2 wrex frninxp_1 frninxp_3 wral frninxp_1 frninxp_3 frninxp_4 frninxp_2 cres crn dfss3 frninxp_2 frninxp_3 frninxp_4 ssrnres frninxp_1 sup_set_class frninxp_4 frninxp_2 cres crn wcel frninxp_0 sup_set_class frninxp_1 sup_set_class frninxp_4 wbr frninxp_0 frninxp_2 wrex frninxp_1 frninxp_3 frninxp_1 sup_set_class frninxp_4 frninxp_2 cres crn wcel frninxp_1 sup_set_class frninxp_4 frninxp_2 cima wcel frninxp_0 sup_set_class frninxp_1 sup_set_class frninxp_4 wbr frninxp_0 frninxp_2 wrex frninxp_4 frninxp_2 cima frninxp_4 frninxp_2 cres crn frninxp_1 sup_set_class frninxp_4 frninxp_2 df-ima eleq2i frninxp_0 frninxp_1 sup_set_class frninxp_4 frninxp_2 frninxp_1 vex elima bitr3i ralbii 3bitr3i $.
$}
$( Domain of the intersection with a cross product.  (Contributed by NM,
       17-Jan-2006.) $)
${
	$d x A $.
	$d x y B $.
	$d x y C $.
	fdminxp_0 $f set x $.
	fdminxp_1 $f set y $.
	fdminxp_2 $f class A $.
	fdminxp_3 $f class B $.
	fdminxp_4 $f class C $.
	dminxp $p |- ( dom ( C i^i ( A X. B ) ) = A <-> A. x e. A E. y e. B x C y ) $= fdminxp_4 fdminxp_2 fdminxp_3 cxp cin cdm fdminxp_2 wceq fdminxp_4 ccnv fdminxp_3 fdminxp_2 cxp cin crn fdminxp_2 wceq fdminxp_1 sup_set_class fdminxp_0 sup_set_class fdminxp_4 ccnv wbr fdminxp_1 fdminxp_3 wrex fdminxp_0 fdminxp_2 wral fdminxp_0 sup_set_class fdminxp_1 sup_set_class fdminxp_4 wbr fdminxp_1 fdminxp_3 wrex fdminxp_0 fdminxp_2 wral fdminxp_4 fdminxp_2 fdminxp_3 cxp cin cdm fdminxp_4 ccnv fdminxp_3 fdminxp_2 cxp cin crn fdminxp_2 fdminxp_4 fdminxp_2 fdminxp_3 cxp cin cdm fdminxp_4 fdminxp_2 fdminxp_3 cxp cin ccnv crn fdminxp_4 ccnv fdminxp_3 fdminxp_2 cxp cin crn fdminxp_4 fdminxp_2 fdminxp_3 cxp cin dfdm4 fdminxp_4 fdminxp_2 fdminxp_3 cxp cin ccnv fdminxp_4 ccnv fdminxp_3 fdminxp_2 cxp cin fdminxp_4 fdminxp_2 fdminxp_3 cxp cin ccnv fdminxp_4 ccnv fdminxp_2 fdminxp_3 cxp ccnv cin fdminxp_4 ccnv fdminxp_3 fdminxp_2 cxp cin fdminxp_4 fdminxp_2 fdminxp_3 cxp cnvin fdminxp_2 fdminxp_3 cxp ccnv fdminxp_3 fdminxp_2 cxp fdminxp_4 ccnv fdminxp_2 fdminxp_3 cnvxp ineq2i eqtri rneqi eqtri eqeq1i fdminxp_1 fdminxp_0 fdminxp_3 fdminxp_2 fdminxp_4 ccnv rninxp fdminxp_1 sup_set_class fdminxp_0 sup_set_class fdminxp_4 ccnv wbr fdminxp_1 fdminxp_3 wrex fdminxp_0 sup_set_class fdminxp_1 sup_set_class fdminxp_4 wbr fdminxp_1 fdminxp_3 wrex fdminxp_0 fdminxp_2 fdminxp_1 sup_set_class fdminxp_0 sup_set_class fdminxp_4 ccnv wbr fdminxp_0 sup_set_class fdminxp_1 sup_set_class fdminxp_4 wbr fdminxp_1 fdminxp_3 fdminxp_1 sup_set_class fdminxp_0 sup_set_class fdminxp_4 fdminxp_1 vex fdminxp_0 vex brcnv rexbii ralbii 3bitri $.
$}
$( Image of a relation restricted to a rectangular region.  (Contributed by
     Stefan O'Rear, 19-Feb-2015.) $)
${
	fimainrect_0 $f class A $.
	fimainrect_1 $f class B $.
	fimainrect_2 $f class G $.
	fimainrect_3 $f class Y $.
	imainrect $p |- ( ( G i^i ( A X. B ) ) " Y ) = ( ( G " ( Y i^i A ) ) i^i B ) $= fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cres crn fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin crn fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cima fimainrect_2 fimainrect_3 fimainrect_0 cin cima fimainrect_1 cin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cres fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 df-res rneqi fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 df-ima fimainrect_2 fimainrect_3 fimainrect_0 cin cima fimainrect_1 cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin crn fimainrect_1 cin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin crn fimainrect_2 fimainrect_3 fimainrect_0 cin cima fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin crn fimainrect_1 fimainrect_2 fimainrect_3 fimainrect_0 cin cima fimainrect_2 fimainrect_3 fimainrect_0 cin cres crn fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin crn fimainrect_2 fimainrect_3 fimainrect_0 cin df-ima fimainrect_2 fimainrect_3 fimainrect_0 cin cres fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin fimainrect_2 fimainrect_3 fimainrect_0 cin df-res rneqi eqtri ineq1i fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 cres cdm fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin ccnv cdm fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin crn fimainrect_1 cin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin crn fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 cres fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin ccnv fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin cvv fimainrect_1 cxp cin ccnv fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cvv fimainrect_1 cxp ccnv cin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin ccnv fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 cres fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin cvv fimainrect_1 cxp cnvin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin cvv fimainrect_1 cxp cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 fimainrect_1 cxp cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cvv fimainrect_1 cxp cin cin fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin cvv fimainrect_1 cxp cin fimainrect_0 fimainrect_1 cxp fimainrect_0 cvv cxp cvv fimainrect_1 cxp cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cvv fimainrect_1 cxp cin fimainrect_0 cvv cin cvv fimainrect_1 cin cxp fimainrect_0 fimainrect_1 cxp fimainrect_0 cvv cvv fimainrect_1 inxp fimainrect_0 cvv cin fimainrect_0 cvv fimainrect_1 cin fimainrect_1 fimainrect_0 inv1 cvv fimainrect_1 cin fimainrect_1 cvv cin fimainrect_1 cvv fimainrect_1 incom fimainrect_1 inv1 eqtri xpeq12i eqtr2i ineq2i fimainrect_2 fimainrect_0 fimainrect_1 cxp fimainrect_3 cvv cxp in32 fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin cvv fimainrect_1 cxp cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cin cvv fimainrect_1 cxp cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cvv fimainrect_1 cxp cin cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cin cvv fimainrect_1 cxp fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin fimainrect_2 fimainrect_3 cvv cxp fimainrect_0 cvv cxp cin cin fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cin fimainrect_3 fimainrect_0 cin cvv cxp fimainrect_3 cvv cxp fimainrect_0 cvv cxp cin fimainrect_2 fimainrect_3 fimainrect_0 cvv xpindir ineq2i fimainrect_2 fimainrect_3 cvv cxp fimainrect_0 cvv cxp inass eqtr4i ineq1i fimainrect_2 fimainrect_3 cvv cxp cin fimainrect_0 cvv cxp cvv fimainrect_1 cxp inass eqtri 3eqtr4i cnveqi fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 cres fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 cvv cxp cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cvv fimainrect_1 cxp ccnv cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 df-res cvv fimainrect_1 cxp ccnv fimainrect_1 cvv cxp fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cvv fimainrect_1 cnvxp ineq2i eqtr4i 3eqtr4ri dmeqi fimainrect_1 fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cdm cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cdm fimainrect_1 cin fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 cres cdm fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin crn fimainrect_1 cin fimainrect_1 fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cdm incom fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv fimainrect_1 dmres fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin crn fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin ccnv cdm fimainrect_1 fimainrect_2 fimainrect_3 fimainrect_0 cin cvv cxp cin df-rn ineq1i 3eqtr4ri fimainrect_2 fimainrect_0 fimainrect_1 cxp cin fimainrect_3 cvv cxp cin df-rn 3eqtr4ri eqtr4i 3eqtr4i $.
$}
$( The base set of a strict order is contained in the field of the
       relation, except possibly for one element (note that
       ` (/) Or { B } ` ).  (Contributed by Mario Carneiro, 27-Apr-2015.) $)
${
	$d x A $.
	$d x B $.
	$d x R $.
	isossfld_0 $f set x $.
	fsossfld_0 $f class A $.
	fsossfld_1 $f class B $.
	fsossfld_2 $f class R $.
	sossfld $p |- ( ( R Or A /\ B e. A ) -> ( A \ { B } ) C_ ( dom R u. ran R ) ) $= fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel wa isossfld_0 fsossfld_0 fsossfld_1 csn cdif fsossfld_2 cdm fsossfld_2 crn cun isossfld_0 sup_set_class fsossfld_0 fsossfld_1 csn cdif wcel isossfld_0 sup_set_class fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_1 wne wa fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_2 cdm fsossfld_2 crn cun wcel isossfld_0 sup_set_class fsossfld_0 fsossfld_1 eldifsn fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_1 wne isossfld_0 sup_set_class fsossfld_2 cdm fsossfld_2 crn cun wcel fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_1 wne isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr wo isossfld_0 sup_set_class fsossfld_2 cdm fsossfld_2 crn cun wcel fsossfld_0 fsossfld_2 wor isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr wo isossfld_0 sup_set_class fsossfld_1 wne wb fsossfld_0 fsossfld_2 wor isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 fsossfld_0 wcel wa wa isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr wo isossfld_0 sup_set_class fsossfld_1 fsossfld_0 isossfld_0 sup_set_class fsossfld_1 fsossfld_2 sotrieq necon2abid anass1rs fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr wo isossfld_0 sup_set_class fsossfld_2 cdm wcel isossfld_0 sup_set_class fsossfld_2 crn wcel wo isossfld_0 sup_set_class fsossfld_2 cdm fsossfld_2 crn cun wcel fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_0 wcel wa isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 cdm wcel fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 crn wcel fsossfld_0 fsossfld_2 wor isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 cdm wcel wi isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 cdm wcel wi fsossfld_0 fsossfld_2 wor isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_1 fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 cdm wcel isossfld_0 sup_set_class fsossfld_1 fsossfld_0 fsossfld_0 fsossfld_2 breldmg 3expia adantll an32s fsossfld_1 fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 crn wcel wi fsossfld_0 fsossfld_2 wor fsossfld_1 fsossfld_0 wcel isossfld_0 sup_set_class fsossfld_0 wcel fsossfld_1 isossfld_0 sup_set_class fsossfld_2 wbr isossfld_0 sup_set_class fsossfld_2 crn wcel fsossfld_1 isossfld_0 sup_set_class fsossfld_2 fsossfld_0 fsossfld_0 brelrng 3expia adantll orim12d isossfld_0 sup_set_class fsossfld_2 cdm fsossfld_2 crn elun syl6ibr sylbird expimpd syl5bi ssrdv $.
$}
$( The base set of a nonempty strict order is the same as the field of the
       relation.  (Contributed by Mario Carneiro, 15-May-2015.) $)
${
	$d x y A $.
	$d x y R $.
	isofld_0 $f set x $.
	isofld_1 $f set y $.
	fsofld_0 $f class A $.
	fsofld_1 $f class R $.
	sofld $p |- ( ( R Or A /\ R C_ ( A X. A ) /\ R =/= (/) ) -> A = ( dom R u. ran R ) ) $= fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 c0 wne w3a fsofld_0 fsofld_1 cdm fsofld_1 crn cun fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 c0 wne fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss fsofld_1 c0 fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss wn fsofld_1 c0 wceq fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss wn wa fsofld_1 c0 wss fsofld_1 c0 wceq fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss wn wa isofld_0 isofld_1 fsofld_1 c0 fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 wrel fsofld_0 fsofld_1 wor fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss wn fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_0 fsofld_0 cxp wrel fsofld_1 wrel fsofld_0 fsofld_0 relxp fsofld_1 fsofld_0 fsofld_0 cxp relss mpi ad2antlr fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss wn wa isofld_0 sup_set_class isofld_1 sup_set_class cop fsofld_1 wcel isofld_0 sup_set_class isofld_1 sup_set_class cop c0 wcel fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class cop fsofld_1 wcel fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss isofld_0 sup_set_class isofld_1 sup_set_class cop fsofld_1 wcel isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 df-br fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_0 fsofld_1 cdm fsofld_1 crn cun wss fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr wa fsofld_0 fsofld_0 isofld_0 sup_set_class csn cdif isofld_0 sup_set_class csn cun fsofld_1 cdm fsofld_1 crn cun fsofld_0 fsofld_0 isofld_0 sup_set_class csn cun fsofld_0 isofld_0 sup_set_class csn cdif isofld_0 sup_set_class csn cun fsofld_0 isofld_0 sup_set_class csn ssun1 fsofld_0 isofld_0 sup_set_class csn undif1 sseqtr4i fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr wa fsofld_0 isofld_0 sup_set_class csn cdif isofld_0 sup_set_class csn fsofld_1 cdm fsofld_1 crn cun fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr wa fsofld_0 fsofld_1 wor isofld_0 sup_set_class fsofld_0 wcel fsofld_0 isofld_0 sup_set_class csn cdif fsofld_1 cdm fsofld_1 crn cun wss fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr simpll fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr wa fsofld_1 cdm fsofld_0 isofld_0 sup_set_class fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 cdm fsofld_0 wss fsofld_0 fsofld_1 wor isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 cdm fsofld_0 fsofld_0 cxp cdm fsofld_0 fsofld_1 fsofld_0 fsofld_0 cxp dmss fsofld_0 dmxpid syl6sseq ad2antlr fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_1 wrel isofld_0 sup_set_class fsofld_1 cdm wcel fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 wrel fsofld_0 fsofld_1 wor isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_0 fsofld_0 cxp wrel fsofld_1 wrel fsofld_0 fsofld_0 relxp fsofld_1 fsofld_0 fsofld_0 cxp relss mpi ad2antlr isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 releldm sylancom sseldd fsofld_0 isofld_0 sup_set_class fsofld_1 sossfld syl2anc fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr wa isofld_0 sup_set_class fsofld_1 cdm fsofld_1 crn cun fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr wa fsofld_1 cdm fsofld_1 cdm fsofld_1 crn cun isofld_0 sup_set_class fsofld_1 cdm fsofld_1 crn ssun1 fsofld_0 fsofld_1 wor fsofld_1 fsofld_0 fsofld_0 cxp wss wa isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_1 wrel isofld_0 sup_set_class fsofld_1 cdm wcel fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 wrel fsofld_0 fsofld_1 wor isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 wbr fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_0 fsofld_0 cxp wrel fsofld_1 wrel fsofld_0 fsofld_0 relxp fsofld_1 fsofld_0 fsofld_0 cxp relss mpi ad2antlr isofld_0 sup_set_class isofld_1 sup_set_class fsofld_1 releldm sylancom sseldi snssd unssd syl5ss ex syl5bir con3and pm2.21d relssdv fsofld_1 ss0 syl ex necon1ad 3impia fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_0 fsofld_1 wor fsofld_1 cdm fsofld_1 crn cun fsofld_0 wss fsofld_1 c0 wne fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 cdm fsofld_1 crn fsofld_0 fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 cdm fsofld_0 fsofld_0 cxp cdm fsofld_0 fsofld_1 fsofld_0 fsofld_0 cxp dmss fsofld_0 dmxpid syl6sseq fsofld_1 fsofld_0 fsofld_0 cxp wss fsofld_1 crn fsofld_0 fsofld_0 cxp crn fsofld_0 fsofld_1 fsofld_0 fsofld_0 cxp rnss fsofld_0 rnxpid syl6sseq unssd 3ad2ant2 eqssd $.
$}
$( If the relation in a strict order is a set, then the base field is also
       a set.  (Contributed by Mario Carneiro, 27-Apr-2015.) $)
${
	$d x A $.
	$d x R $.
	$d x V $.
	isoex_0 $f set x $.
	fsoex_0 $f class A $.
	fsoex_1 $f class R $.
	fsoex_2 $f class V $.
	soex $p |- ( ( R Or A /\ R e. V ) -> A e. _V ) $= fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa fsoex_0 cvv wcel fsoex_0 c0 fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa fsoex_0 c0 wceq wa fsoex_0 c0 cvv fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa fsoex_0 c0 wceq simpr 0ex syl6eqel fsoex_0 c0 wne fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa isoex_0 sup_set_class fsoex_0 wcel isoex_0 wex fsoex_0 cvv wcel isoex_0 fsoex_0 n0 fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa isoex_0 sup_set_class fsoex_0 wcel isoex_0 wex fsoex_0 cvv wcel fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa isoex_0 sup_set_class fsoex_0 wcel fsoex_0 cvv wcel isoex_0 fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa isoex_0 sup_set_class fsoex_0 wcel fsoex_0 cvv wcel fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa isoex_0 sup_set_class fsoex_0 wcel wa fsoex_0 isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cun wss isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cun cvv wcel fsoex_0 cvv wcel fsoex_0 fsoex_1 wor fsoex_1 fsoex_2 wcel wa isoex_0 sup_set_class fsoex_0 wcel wa fsoex_0 isoex_0 sup_set_class csn cdif fsoex_1 cdm fsoex_1 crn cun wss fsoex_0 isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cun wss fsoex_0 fsoex_1 wor isoex_0 sup_set_class fsoex_0 wcel fsoex_0 isoex_0 sup_set_class csn cdif fsoex_1 cdm fsoex_1 crn cun wss fsoex_1 fsoex_2 wcel fsoex_0 isoex_0 sup_set_class fsoex_1 sossfld adantlr fsoex_0 isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun ssundif sylibr fsoex_1 fsoex_2 wcel isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cun cvv wcel fsoex_0 fsoex_1 wor isoex_0 sup_set_class fsoex_0 wcel fsoex_1 fsoex_2 wcel isoex_0 sup_set_class csn cvv wcel fsoex_1 cdm fsoex_1 crn cun cvv wcel isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cun cvv wcel isoex_0 sup_set_class snex fsoex_1 fsoex_2 wcel fsoex_1 cdm cvv wcel fsoex_1 crn cvv wcel fsoex_1 cdm fsoex_1 crn cun cvv wcel fsoex_1 fsoex_2 dmexg fsoex_1 fsoex_2 rnexg fsoex_1 cdm fsoex_1 crn cvv cvv unexg syl2anc isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cvv cvv unexg sylancr ad2antlr fsoex_0 isoex_0 sup_set_class csn fsoex_1 cdm fsoex_1 crn cun cun cvv ssexg syl2anc ex exlimdv imp sylan2b pm2.61dane $.
$}
$( The set of all ordered pairs in a class is the same as the double
       converse.  (Contributed by Mario Carneiro, 16-Aug-2015.) $)
${
	$d x y R $.
	fcnvcnv3_0 $f set x $.
	fcnvcnv3_1 $f set y $.
	fcnvcnv3_2 $f class R $.
	cnvcnv3 $p |- `' `' R = { <. x , y >. | x R y } $= fcnvcnv3_2 ccnv ccnv fcnvcnv3_1 sup_set_class fcnvcnv3_0 sup_set_class fcnvcnv3_2 ccnv wbr fcnvcnv3_0 fcnvcnv3_1 copab fcnvcnv3_0 sup_set_class fcnvcnv3_1 sup_set_class fcnvcnv3_2 wbr fcnvcnv3_0 fcnvcnv3_1 copab fcnvcnv3_0 fcnvcnv3_1 fcnvcnv3_2 ccnv df-cnv fcnvcnv3_1 sup_set_class fcnvcnv3_0 sup_set_class fcnvcnv3_2 ccnv wbr fcnvcnv3_0 sup_set_class fcnvcnv3_1 sup_set_class fcnvcnv3_2 wbr fcnvcnv3_0 fcnvcnv3_1 fcnvcnv3_1 sup_set_class fcnvcnv3_0 sup_set_class fcnvcnv3_2 fcnvcnv3_1 vex fcnvcnv3_0 vex brcnv opabbii eqtri $.
$}
$( Alternate definition of relation.  Exercise 2 of [TakeutiZaring] p. 25.
       (Contributed by NM, 29-Dec-1996.) $)
${
	$d x y R $.
	idfrel2_0 $f set x $.
	idfrel2_1 $f set y $.
	fdfrel2_0 $f class R $.
	dfrel2 $p |- ( Rel R <-> `' `' R = R ) $= fdfrel2_0 wrel fdfrel2_0 ccnv ccnv fdfrel2_0 wceq fdfrel2_0 ccnv ccnv wrel fdfrel2_0 wrel fdfrel2_0 ccnv ccnv fdfrel2_0 wceq fdfrel2_0 ccnv relcnv idfrel2_0 idfrel2_1 fdfrel2_0 ccnv ccnv fdfrel2_0 idfrel2_0 sup_set_class idfrel2_1 sup_set_class cop fdfrel2_0 ccnv ccnv wcel idfrel2_1 sup_set_class idfrel2_0 sup_set_class cop fdfrel2_0 ccnv wcel idfrel2_0 sup_set_class idfrel2_1 sup_set_class cop fdfrel2_0 wcel idfrel2_0 sup_set_class idfrel2_1 sup_set_class fdfrel2_0 ccnv idfrel2_0 vex idfrel2_1 vex opelcnv idfrel2_1 sup_set_class idfrel2_0 sup_set_class fdfrel2_0 idfrel2_1 vex idfrel2_0 vex opelcnv bitri eqrelriv mpan fdfrel2_0 ccnv ccnv fdfrel2_0 wceq fdfrel2_0 ccnv ccnv wrel fdfrel2_0 wrel fdfrel2_0 ccnv relcnv fdfrel2_0 ccnv ccnv fdfrel2_0 releq mpbii impbii $.
$}
$( A relation can be expressed as the set of ordered pairs in it.  An
       analogue of ~ dffn5 for relations.  (Contributed by Mario Carneiro,
       16-Aug-2015.) $)
${
	$d x y R $.
	fdfrel4v_0 $f set x $.
	fdfrel4v_1 $f set y $.
	fdfrel4v_2 $f class R $.
	dfrel4v $p |- ( Rel R <-> R = { <. x , y >. | x R y } ) $= fdfrel4v_2 wrel fdfrel4v_2 ccnv ccnv fdfrel4v_2 wceq fdfrel4v_2 fdfrel4v_2 ccnv ccnv wceq fdfrel4v_2 fdfrel4v_0 sup_set_class fdfrel4v_1 sup_set_class fdfrel4v_2 wbr fdfrel4v_0 fdfrel4v_1 copab wceq fdfrel4v_2 dfrel2 fdfrel4v_2 ccnv ccnv fdfrel4v_2 eqcom fdfrel4v_2 ccnv ccnv fdfrel4v_0 sup_set_class fdfrel4v_1 sup_set_class fdfrel4v_2 wbr fdfrel4v_0 fdfrel4v_1 copab fdfrel4v_2 fdfrel4v_0 fdfrel4v_1 fdfrel4v_2 cnvcnv3 eqeq2i 3bitri $.
$}
$( The double converse of a class strips out all elements that are not
     ordered pairs.  (Contributed by NM, 8-Dec-2003.) $)
${
	fcnvcnv_0 $f class A $.
	cnvcnv $p |- `' `' A = ( A i^i ( _V X. _V ) ) $= fcnvcnv_0 ccnv ccnv fcnvcnv_0 ccnv ccnv cvv cvv cxp ccnv ccnv cin fcnvcnv_0 ccnv cvv cvv cxp ccnv cin ccnv fcnvcnv_0 cvv cvv cxp cin fcnvcnv_0 ccnv ccnv cvv cvv cxp ccnv ccnv wss fcnvcnv_0 ccnv ccnv fcnvcnv_0 ccnv ccnv cvv cvv cxp ccnv ccnv cin wceq fcnvcnv_0 ccnv ccnv cvv cvv cxp cvv cvv cxp ccnv ccnv fcnvcnv_0 ccnv ccnv wrel fcnvcnv_0 ccnv ccnv cvv cvv cxp wss fcnvcnv_0 ccnv relcnv fcnvcnv_0 ccnv ccnv df-rel mpbi cvv cvv cxp wrel cvv cvv cxp ccnv ccnv cvv cvv cxp wceq cvv cvv relxp cvv cvv cxp dfrel2 mpbi sseqtr4i fcnvcnv_0 ccnv ccnv cvv cvv cxp ccnv ccnv dfss mpbi fcnvcnv_0 ccnv cvv cvv cxp ccnv cnvin fcnvcnv_0 cvv cvv cxp cin ccnv ccnv fcnvcnv_0 ccnv cvv cvv cxp ccnv cin ccnv fcnvcnv_0 cvv cvv cxp cin fcnvcnv_0 cvv cvv cxp cin ccnv fcnvcnv_0 ccnv cvv cvv cxp ccnv cin fcnvcnv_0 cvv cvv cxp cnvin cnveqi fcnvcnv_0 cvv cvv cxp cin wrel fcnvcnv_0 cvv cvv cxp cin ccnv ccnv fcnvcnv_0 cvv cvv cxp cin wceq fcnvcnv_0 cvv cvv cxp cin wrel fcnvcnv_0 cvv cvv cxp cin cvv cvv cxp wss fcnvcnv_0 cvv cvv cxp inss2 fcnvcnv_0 cvv cvv cxp cin df-rel mpbir fcnvcnv_0 cvv cvv cxp cin dfrel2 mpbi eqtr3i 3eqtr2i $.
$}
$( The double converse of a class equals its restriction to the universe.
     (Contributed by NM, 8-Oct-2007.) $)
${
	fcnvcnv2_0 $f class A $.
	cnvcnv2 $p |- `' `' A = ( A |` _V ) $= fcnvcnv2_0 ccnv ccnv fcnvcnv2_0 cvv cvv cxp cin fcnvcnv2_0 cvv cres fcnvcnv2_0 cnvcnv fcnvcnv2_0 cvv df-res eqtr4i $.
$}
$( The double converse of a class is a subclass.  Exercise 2 of
     [TakeutiZaring] p. 25.  (Contributed by NM, 23-Jul-2004.) $)
${
	fcnvcnvss_0 $f class A $.
	cnvcnvss $p |- `' `' A C_ A $= fcnvcnvss_0 ccnv ccnv fcnvcnvss_0 cvv cvv cxp cin fcnvcnvss_0 fcnvcnvss_0 cnvcnv fcnvcnvss_0 cvv cvv cxp inss1 eqsstri $.
$}
$( Equality theorem for converse.  (Contributed by FL, 19-Sep-2011.) $)
${
	fcnveqb_0 $f class A $.
	fcnveqb_1 $f class B $.
	cnveqb $p |- ( ( Rel A /\ Rel B ) -> ( A = B <-> `' A = `' B ) ) $= fcnveqb_0 wrel fcnveqb_1 wrel wa fcnveqb_0 fcnveqb_1 wceq fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 fcnveqb_1 cnveq fcnveqb_0 wrel fcnveqb_1 wrel fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 fcnveqb_1 wceq wi fcnveqb_0 wrel fcnveqb_0 ccnv ccnv fcnveqb_0 wceq fcnveqb_1 wrel fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 fcnveqb_1 wceq wi wi fcnveqb_0 dfrel2 fcnveqb_1 wrel fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 fcnveqb_1 wceq wi wi fcnveqb_0 fcnveqb_0 ccnv ccnv fcnveqb_1 wrel fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 fcnveqb_1 wceq wi fcnveqb_0 fcnveqb_0 ccnv ccnv wceq fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 ccnv ccnv fcnveqb_1 wceq wi fcnveqb_1 wrel fcnveqb_1 ccnv ccnv fcnveqb_1 wceq fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 ccnv ccnv fcnveqb_1 wceq wi fcnveqb_1 dfrel2 fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 ccnv ccnv fcnveqb_1 wceq wi fcnveqb_1 fcnveqb_1 ccnv ccnv fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 ccnv ccnv fcnveqb_1 wceq fcnveqb_1 fcnveqb_1 ccnv ccnv wceq fcnveqb_0 ccnv ccnv fcnveqb_1 ccnv ccnv wceq fcnveqb_0 ccnv fcnveqb_1 ccnv cnveq fcnveqb_1 fcnveqb_1 ccnv ccnv fcnveqb_0 ccnv ccnv eqeq2 syl5ibr eqcoms sylbi fcnveqb_0 fcnveqb_0 ccnv ccnv wceq fcnveqb_0 fcnveqb_1 wceq fcnveqb_0 ccnv ccnv fcnveqb_1 wceq fcnveqb_0 ccnv fcnveqb_1 ccnv wceq fcnveqb_0 fcnveqb_0 ccnv ccnv fcnveqb_1 eqeq1 imbi2d syl5ibr eqcoms sylbi imp impbid2 $.
$}
$( A relation empty iff its converse is empty.  (Contributed by FL,
     19-Sep-2011.) $)
${
	fcnveq0_0 $f class A $.
	cnveq0 $p |- ( Rel A -> ( A = (/) <-> `' A = (/) ) ) $= c0 ccnv c0 wceq fcnveq0_0 wrel fcnveq0_0 c0 wceq fcnveq0_0 ccnv c0 wceq wb wi cnv0 fcnveq0_0 wrel fcnveq0_0 c0 wceq fcnveq0_0 ccnv c0 wceq wb wi c0 c0 ccnv fcnveq0_0 wrel fcnveq0_0 c0 wceq fcnveq0_0 ccnv c0 wceq wb c0 c0 ccnv wceq fcnveq0_0 c0 wceq fcnveq0_0 ccnv c0 ccnv wceq wb fcnveq0_0 wrel c0 wrel fcnveq0_0 c0 wceq fcnveq0_0 ccnv c0 ccnv wceq wb rel0 fcnveq0_0 c0 cnveqb mpan2 c0 c0 ccnv wceq fcnveq0_0 ccnv c0 wceq fcnveq0_0 ccnv c0 ccnv wceq fcnveq0_0 c0 wceq c0 c0 ccnv fcnveq0_0 ccnv eqeq2 bibi2d syl5ibr eqcoms ax-mp $.
$}
$( [19-Sep-2011] $)
$( Alternate definition of relation.  (Contributed by NM, 14-May-2008.) $)
${
	fdfrel3_0 $f class R $.
	dfrel3 $p |- ( Rel R <-> ( R |` _V ) = R ) $= fdfrel3_0 wrel fdfrel3_0 ccnv ccnv fdfrel3_0 wceq fdfrel3_0 cvv cres fdfrel3_0 wceq fdfrel3_0 dfrel2 fdfrel3_0 ccnv ccnv fdfrel3_0 cvv cres fdfrel3_0 fdfrel3_0 cnvcnv2 eqeq1i bitri $.
$}
$( The domain of a universal restriction.  (Contributed by NM,
     14-May-2008.) $)
${
	fdmresv_0 $f class A $.
	dmresv $p |- dom ( A |` _V ) = dom A $= fdmresv_0 cvv cres cdm cvv fdmresv_0 cdm cin fdmresv_0 cdm cvv cin fdmresv_0 cdm fdmresv_0 cvv dmres cvv fdmresv_0 cdm incom fdmresv_0 cdm inv1 3eqtri $.
$}
$( The range of a universal restriction.  (Contributed by NM,
     14-May-2008.) $)
${
	frnresv_0 $f class A $.
	rnresv $p |- ran ( A |` _V ) = ran A $= frnresv_0 ccnv ccnv crn frnresv_0 cvv cres crn frnresv_0 crn frnresv_0 ccnv ccnv frnresv_0 cvv cres frnresv_0 cnvcnv2 rneqi frnresv_0 rncnvcnv eqtr3i $.
$}
$( Range defined in terms of image.  (Contributed by NM, 14-May-2008.) $)
${
	fdfrn4_0 $f class A $.
	dfrn4 $p |- ran A = ( A " _V ) $= fdfrn4_0 cvv cima fdfrn4_0 cvv cres crn fdfrn4_0 crn fdfrn4_0 cvv df-ima fdfrn4_0 rnresv eqtr2i $.
$}
$( The restriction of the double converse of a class.  (Contributed by NM,
     8-Apr-2007.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	frescnvcnv_0 $f class A $.
	frescnvcnv_1 $f class B $.
	rescnvcnv $p |- ( `' `' A |` B ) = ( A |` B ) $= frescnvcnv_0 ccnv ccnv frescnvcnv_1 cres frescnvcnv_0 cvv cres frescnvcnv_1 cres frescnvcnv_0 cvv frescnvcnv_1 cin cres frescnvcnv_0 frescnvcnv_1 cres frescnvcnv_0 ccnv ccnv frescnvcnv_0 cvv cres frescnvcnv_1 frescnvcnv_0 cnvcnv2 reseq1i frescnvcnv_0 cvv frescnvcnv_1 resres cvv frescnvcnv_1 cin frescnvcnv_1 frescnvcnv_0 frescnvcnv_1 cvv wss cvv frescnvcnv_1 cin frescnvcnv_1 wceq frescnvcnv_1 ssv frescnvcnv_1 cvv sseqin2 mpbi reseq2i 3eqtri $.
$}
$( The double converse of the restriction of a class.  (Contributed by NM,
     3-Jun-2007.) $)
${
	fcnvcnvres_0 $f class A $.
	fcnvcnvres_1 $f class B $.
	cnvcnvres $p |- `' `' ( A |` B ) = ( `' `' A |` B ) $= fcnvcnvres_0 fcnvcnvres_1 cres ccnv ccnv fcnvcnvres_0 fcnvcnvres_1 cres fcnvcnvres_0 ccnv ccnv fcnvcnvres_1 cres fcnvcnvres_0 fcnvcnvres_1 cres wrel fcnvcnvres_0 fcnvcnvres_1 cres ccnv ccnv fcnvcnvres_0 fcnvcnvres_1 cres wceq fcnvcnvres_0 fcnvcnvres_1 relres fcnvcnvres_0 fcnvcnvres_1 cres dfrel2 mpbi fcnvcnvres_0 fcnvcnvres_1 rescnvcnv eqtr4i $.
$}
$( The image of the double converse of a class.  (Contributed by NM,
     8-Apr-2007.) $)
${
	fimacnvcnv_0 $f class A $.
	fimacnvcnv_1 $f class B $.
	imacnvcnv $p |- ( `' `' A " B ) = ( A " B ) $= fimacnvcnv_0 ccnv ccnv fimacnvcnv_1 cres crn fimacnvcnv_0 fimacnvcnv_1 cres crn fimacnvcnv_0 ccnv ccnv fimacnvcnv_1 cima fimacnvcnv_0 fimacnvcnv_1 cima fimacnvcnv_0 ccnv ccnv fimacnvcnv_1 cres fimacnvcnv_0 fimacnvcnv_1 cres fimacnvcnv_0 fimacnvcnv_1 rescnvcnv rneqi fimacnvcnv_0 ccnv ccnv fimacnvcnv_1 df-ima fimacnvcnv_0 fimacnvcnv_1 df-ima 3eqtr4i $.
$}
$( The domain of a singleton is nonzero iff the singleton argument is an
       ordered pair.  (Contributed by NM, 14-Dec-2008.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y A $.
	idmsnn0_0 $f set x $.
	idmsnn0_1 $f set y $.
	fdmsnn0_0 $f class A $.
	dmsnn0 $p |- ( A e. ( _V X. _V ) <-> dom { A } =/= (/) ) $= fdmsnn0_0 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop wceq idmsnn0_1 wex idmsnn0_0 wex idmsnn0_0 sup_set_class fdmsnn0_0 csn cdm wcel idmsnn0_0 wex fdmsnn0_0 cvv cvv cxp wcel fdmsnn0_0 csn cdm c0 wne fdmsnn0_0 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop wceq idmsnn0_1 wex idmsnn0_0 sup_set_class fdmsnn0_0 csn cdm wcel idmsnn0_0 idmsnn0_0 sup_set_class fdmsnn0_0 csn cdm wcel idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class fdmsnn0_0 csn wbr idmsnn0_1 wex fdmsnn0_0 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop wceq idmsnn0_1 wex idmsnn0_1 idmsnn0_0 sup_set_class fdmsnn0_0 csn idmsnn0_0 vex eldm idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class fdmsnn0_0 csn wbr fdmsnn0_0 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop wceq idmsnn0_1 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class fdmsnn0_0 csn wbr idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop fdmsnn0_0 csn wcel idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop fdmsnn0_0 wceq fdmsnn0_0 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop wceq idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class fdmsnn0_0 csn df-br idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop fdmsnn0_0 idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class opex elsnc idmsnn0_0 sup_set_class idmsnn0_1 sup_set_class cop fdmsnn0_0 eqcom 3bitri exbii bitr2i exbii idmsnn0_0 idmsnn0_1 fdmsnn0_0 elvv idmsnn0_0 fdmsnn0_0 csn cdm n0 3bitr4i $.
$}
$( The range of a singleton is nonzero iff the singleton argument is an
     ordered pair.  (Contributed by NM, 14-Dec-2008.) $)
${
	frnsnn0_0 $f class A $.
	rnsnn0 $p |- ( A e. ( _V X. _V ) <-> ran { A } =/= (/) ) $= frnsnn0_0 cvv cvv cxp wcel frnsnn0_0 csn cdm c0 wne frnsnn0_0 csn crn c0 wne frnsnn0_0 dmsnn0 frnsnn0_0 csn cdm c0 frnsnn0_0 csn crn c0 frnsnn0_0 csn dm0rn0 necon3bii bitri $.
$}
$( The domain of the singleton of the empty set is empty.  (Contributed by
     NM, 30-Jan-2004.) $)
${
	dmsn0 $p |- dom { (/) } = (/) $= c0 csn cdm c0 wceq c0 cvv cvv cxp wcel wn cvv cvv 0nelxp c0 cvv cvv cxp wcel c0 csn cdm c0 c0 dmsnn0 necon2bbii mpbir $.
$}
$( The converse of the singleton of the empty set is empty.  (Contributed by
     Mario Carneiro, 30-Aug-2015.) $)
${
	cnvsn0 $p |- `' { (/) } = (/) $= c0 csn ccnv c0 wceq c0 csn ccnv crn c0 wceq c0 csn cdm c0 csn ccnv crn c0 c0 csn dfdm4 dmsn0 eqtr3i c0 csn ccnv wrel c0 csn ccnv c0 wceq c0 csn ccnv crn c0 wceq wb c0 csn relcnv c0 csn ccnv relrn0 ax-mp mpbir $.
$}
$( The domain of a singleton is empty if the singleton's argument contains
     the empty set.  (Contributed by NM, 15-Dec-2008.) $)
${
	fdmsn0el_0 $f class A $.
	dmsn0el $p |- ( (/) e. A -> dom { A } = (/) ) $= c0 fdmsn0el_0 wcel fdmsn0el_0 csn cdm c0 fdmsn0el_0 csn cdm c0 wne fdmsn0el_0 cvv cvv cxp wcel c0 fdmsn0el_0 wcel wn fdmsn0el_0 dmsnn0 cvv cvv fdmsn0el_0 0nelelxp sylbir necon4ai $.
$}
$( A singleton is a relation iff it has a nonempty domain.  (Contributed by
       NM, 25-Sep-2013.) $)
${
	frelsn2_0 $f class A $.
	erelsn2_0 $e |- A e. _V $.
	relsn2 $p |- ( Rel { A } <-> dom { A } =/= (/) ) $= frelsn2_0 csn wrel frelsn2_0 cvv cvv cxp wcel frelsn2_0 csn cdm c0 wne frelsn2_0 erelsn2_0 relsn frelsn2_0 dmsnn0 bitri $.
$}
$( The domain of a singleton of an ordered pair is the singleton of the
       first member.  (Contributed by Mario Carneiro, 26-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x V $.
	idmsnopg_0 $f set x $.
	idmsnopg_1 $f set y $.
	fdmsnopg_0 $f class A $.
	fdmsnopg_1 $f class B $.
	fdmsnopg_2 $f class V $.
	dmsnopg $p |- ( B e. V -> dom { <. A , B >. } = { A } ) $= fdmsnopg_1 fdmsnopg_2 wcel idmsnopg_0 fdmsnopg_0 fdmsnopg_1 cop csn cdm fdmsnopg_0 csn fdmsnopg_1 fdmsnopg_2 wcel idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_1 wex idmsnopg_0 sup_set_class fdmsnopg_0 wceq idmsnopg_0 sup_set_class fdmsnopg_0 fdmsnopg_1 cop csn cdm wcel idmsnopg_0 sup_set_class fdmsnopg_0 csn wcel fdmsnopg_1 fdmsnopg_2 wcel idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_1 wex idmsnopg_0 sup_set_class fdmsnopg_0 wceq idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_0 sup_set_class fdmsnopg_0 wceq idmsnopg_1 idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class fdmsnopg_0 fdmsnopg_1 idmsnopg_0 vex idmsnopg_1 vex opth1 exlimiv idmsnopg_0 sup_set_class fdmsnopg_0 wceq idmsnopg_0 sup_set_class fdmsnopg_1 cop fdmsnopg_0 fdmsnopg_1 cop wceq fdmsnopg_1 fdmsnopg_2 wcel idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_1 wex idmsnopg_0 sup_set_class fdmsnopg_0 fdmsnopg_1 opeq1 idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_0 sup_set_class fdmsnopg_1 cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_1 fdmsnopg_1 fdmsnopg_2 idmsnopg_1 sup_set_class fdmsnopg_1 wceq idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop idmsnopg_0 sup_set_class fdmsnopg_1 cop fdmsnopg_0 fdmsnopg_1 cop idmsnopg_1 sup_set_class fdmsnopg_1 idmsnopg_0 sup_set_class opeq2 eqeq1d spcegv syl5 impbid2 idmsnopg_0 sup_set_class fdmsnopg_0 fdmsnopg_1 cop csn cdm wcel idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop csn wcel idmsnopg_1 wex idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_1 wex idmsnopg_1 idmsnopg_0 sup_set_class fdmsnopg_0 fdmsnopg_1 cop csn idmsnopg_0 vex eldm2 idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop csn wcel idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop wceq idmsnopg_1 idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class cop fdmsnopg_0 fdmsnopg_1 cop idmsnopg_0 sup_set_class idmsnopg_1 sup_set_class opex elsnc exbii bitri idmsnopg_0 fdmsnopg_0 elsn 3bitr4g eqrdv $.
$}
$( The domain of a singleton of an ordered pair is a subset of the
       singleton of the first member (with no sethood assumptions on ` B ` ).
       (Contributed by Mario Carneiro, 30-Apr-2015.) $)
${
	fdmsnopss_0 $f class A $.
	fdmsnopss_1 $f class B $.
	dmsnopss $p |- dom { <. A , B >. } C_ { A } $= fdmsnopss_1 cvv wcel fdmsnopss_0 fdmsnopss_1 cop csn cdm fdmsnopss_0 csn wss fdmsnopss_1 cvv wcel fdmsnopss_0 fdmsnopss_1 cop csn cdm fdmsnopss_0 csn wceq fdmsnopss_0 fdmsnopss_1 cop csn cdm fdmsnopss_0 csn wss fdmsnopss_0 fdmsnopss_1 cvv dmsnopg fdmsnopss_0 fdmsnopss_1 cop csn cdm fdmsnopss_0 csn eqimss syl fdmsnopss_1 cvv wcel wn fdmsnopss_0 fdmsnopss_1 cop csn cdm c0 fdmsnopss_0 csn fdmsnopss_1 cvv wcel wn fdmsnopss_0 fdmsnopss_1 cop csn cdm c0 csn cdm c0 fdmsnopss_1 cvv wcel wn fdmsnopss_0 fdmsnopss_1 cop csn c0 csn fdmsnopss_1 cvv wcel wn fdmsnopss_0 fdmsnopss_1 cop c0 fdmsnopss_0 fdmsnopss_1 opprc2 sneqd dmeqd dmsn0 syl6eq c0 fdmsnopss_0 csn wss fdmsnopss_1 cvv wcel wn fdmsnopss_0 csn 0ss a1i eqsstrd pm2.61i $.
$}
$( The domain of an unordered pair of ordered pairs.  (Contributed by Mario
       Carneiro, 26-Apr-2015.) $)
${
	fdmpropg_0 $f class A $.
	fdmpropg_1 $f class B $.
	fdmpropg_2 $f class C $.
	fdmpropg_3 $f class D $.
	fdmpropg_4 $f class V $.
	fdmpropg_5 $f class W $.
	dmpropg $p |- ( ( B e. V /\ D e. W ) -> dom { <. A , B >. , <. C , D >. } = { A , C } ) $= fdmpropg_1 fdmpropg_4 wcel fdmpropg_3 fdmpropg_5 wcel wa fdmpropg_0 fdmpropg_1 cop csn cdm fdmpropg_2 fdmpropg_3 cop csn cdm cun fdmpropg_0 csn fdmpropg_2 csn cun fdmpropg_0 fdmpropg_1 cop fdmpropg_2 fdmpropg_3 cop cpr cdm fdmpropg_0 fdmpropg_2 cpr fdmpropg_1 fdmpropg_4 wcel fdmpropg_0 fdmpropg_1 cop csn cdm fdmpropg_0 csn wceq fdmpropg_2 fdmpropg_3 cop csn cdm fdmpropg_2 csn wceq fdmpropg_0 fdmpropg_1 cop csn cdm fdmpropg_2 fdmpropg_3 cop csn cdm cun fdmpropg_0 csn fdmpropg_2 csn cun wceq fdmpropg_3 fdmpropg_5 wcel fdmpropg_0 fdmpropg_1 fdmpropg_4 dmsnopg fdmpropg_2 fdmpropg_3 fdmpropg_5 dmsnopg fdmpropg_0 fdmpropg_1 cop csn cdm fdmpropg_0 csn fdmpropg_2 fdmpropg_3 cop csn cdm fdmpropg_2 csn uneq12 syl2an fdmpropg_0 fdmpropg_1 cop fdmpropg_2 fdmpropg_3 cop cpr cdm fdmpropg_0 fdmpropg_1 cop csn fdmpropg_2 fdmpropg_3 cop csn cun cdm fdmpropg_0 fdmpropg_1 cop csn cdm fdmpropg_2 fdmpropg_3 cop csn cdm cun fdmpropg_0 fdmpropg_1 cop fdmpropg_2 fdmpropg_3 cop cpr fdmpropg_0 fdmpropg_1 cop csn fdmpropg_2 fdmpropg_3 cop csn cun fdmpropg_0 fdmpropg_1 cop fdmpropg_2 fdmpropg_3 cop df-pr dmeqi fdmpropg_0 fdmpropg_1 cop csn fdmpropg_2 fdmpropg_3 cop csn dmun eqtri fdmpropg_0 fdmpropg_2 df-pr 3eqtr4g $.
$}
$( The domain of a singleton of an ordered pair is the singleton of the
       first member.  (Contributed by NM, 30-Jan-2004.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	fdmsnop_0 $f class A $.
	fdmsnop_1 $f class B $.
	edmsnop_0 $e |- B e. _V $.
	dmsnop $p |- dom { <. A , B >. } = { A } $= fdmsnop_1 cvv wcel fdmsnop_0 fdmsnop_1 cop csn cdm fdmsnop_0 csn wceq edmsnop_0 fdmsnop_0 fdmsnop_1 cvv dmsnopg ax-mp $.
$}
$( The domain of an unordered pair of ordered pairs.  (Contributed by NM,
       13-Sep-2011.) $)
${
	fdmprop_0 $f class A $.
	fdmprop_1 $f class B $.
	fdmprop_2 $f class C $.
	fdmprop_3 $f class D $.
	edmprop_0 $e |- B e. _V $.
	edmprop_1 $e |- D e. _V $.
	dmprop $p |- dom { <. A , B >. , <. C , D >. } = { A , C } $= fdmprop_1 cvv wcel fdmprop_3 cvv wcel fdmprop_0 fdmprop_1 cop fdmprop_2 fdmprop_3 cop cpr cdm fdmprop_0 fdmprop_2 cpr wceq edmprop_0 edmprop_1 fdmprop_0 fdmprop_1 fdmprop_2 fdmprop_3 cvv cvv dmpropg mp2an $.
$}
$( The domain of an unordered triple of ordered pairs.  (Contributed by NM,
       14-Sep-2011.) $)
${
	fdmtpop_0 $f class A $.
	fdmtpop_1 $f class B $.
	fdmtpop_2 $f class C $.
	fdmtpop_3 $f class D $.
	fdmtpop_4 $f class E $.
	fdmtpop_5 $f class F $.
	edmtpop_0 $e |- B e. _V $.
	edmtpop_1 $e |- D e. _V $.
	edmtpop_2 $e |- F e. _V $.
	dmtpop $p |- dom { <. A , B >. , <. C , D >. , <. E , F >. } = { A , C , E } $= fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop fdmtpop_4 fdmtpop_5 cop ctp cdm fdmtpop_0 fdmtpop_2 cpr fdmtpop_4 csn cun fdmtpop_0 fdmtpop_2 fdmtpop_4 ctp fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop fdmtpop_4 fdmtpop_5 cop ctp cdm fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop cpr fdmtpop_4 fdmtpop_5 cop csn cun cdm fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop cpr cdm fdmtpop_4 fdmtpop_5 cop csn cdm cun fdmtpop_0 fdmtpop_2 cpr fdmtpop_4 csn cun fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop fdmtpop_4 fdmtpop_5 cop ctp fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop cpr fdmtpop_4 fdmtpop_5 cop csn cun fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop fdmtpop_4 fdmtpop_5 cop df-tp dmeqi fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop cpr fdmtpop_4 fdmtpop_5 cop csn dmun fdmtpop_0 fdmtpop_1 cop fdmtpop_2 fdmtpop_3 cop cpr cdm fdmtpop_0 fdmtpop_2 cpr fdmtpop_4 fdmtpop_5 cop csn cdm fdmtpop_4 csn fdmtpop_0 fdmtpop_1 fdmtpop_2 fdmtpop_3 edmtpop_0 edmtpop_1 dmprop fdmtpop_4 fdmtpop_5 edmtpop_2 dmsnop uneq12i 3eqtri fdmtpop_0 fdmtpop_2 fdmtpop_4 df-tp eqtr4i $.
$}
$( Double converse of a singleton of an ordered pair.  (Unlike ~ cnvsn ,
       this does not need any sethood assumptions on ` A ` and ` B ` .)
       (Contributed by Mario Carneiro, 26-Apr-2015.) $)
${
	$d x y A $.
	$d x y B $.
	icnvcnvsn_0 $f set x $.
	icnvcnvsn_1 $f set y $.
	fcnvcnvsn_0 $f class A $.
	fcnvcnvsn_1 $f class B $.
	cnvcnvsn $p |- `' `' { <. A , B >. } = `' { <. B , A >. } $= icnvcnvsn_0 icnvcnvsn_1 fcnvcnvsn_0 fcnvcnvsn_1 cop csn ccnv ccnv fcnvcnvsn_1 fcnvcnvsn_0 cop csn ccnv fcnvcnvsn_0 fcnvcnvsn_1 cop csn ccnv relcnv fcnvcnvsn_1 fcnvcnvsn_0 cop csn relcnv icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop csn ccnv ccnv wcel icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop csn ccnv wcel icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop csn ccnv wcel icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class fcnvcnvsn_0 fcnvcnvsn_1 cop csn ccnv icnvcnvsn_0 vex icnvcnvsn_1 vex opelcnv icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop csn wcel icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop csn wcel icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop csn ccnv wcel icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop csn ccnv wcel icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop wceq icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop wceq icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop csn wcel icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop csn wcel icnvcnvsn_0 sup_set_class fcnvcnvsn_0 wceq icnvcnvsn_1 sup_set_class fcnvcnvsn_1 wceq wa icnvcnvsn_1 sup_set_class fcnvcnvsn_1 wceq icnvcnvsn_0 sup_set_class fcnvcnvsn_0 wceq wa icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop wceq icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop wceq icnvcnvsn_0 sup_set_class fcnvcnvsn_0 wceq icnvcnvsn_1 sup_set_class fcnvcnvsn_1 wceq ancom icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class fcnvcnvsn_0 fcnvcnvsn_1 icnvcnvsn_0 vex icnvcnvsn_1 vex opth icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class fcnvcnvsn_1 fcnvcnvsn_0 icnvcnvsn_1 vex icnvcnvsn_0 vex opth 3bitr4i icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class cop fcnvcnvsn_0 fcnvcnvsn_1 cop icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class opex elsnc icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class cop fcnvcnvsn_1 fcnvcnvsn_0 cop icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class opex elsnc 3bitr4i icnvcnvsn_1 sup_set_class icnvcnvsn_0 sup_set_class fcnvcnvsn_0 fcnvcnvsn_1 cop csn icnvcnvsn_1 vex icnvcnvsn_0 vex opelcnv icnvcnvsn_0 sup_set_class icnvcnvsn_1 sup_set_class fcnvcnvsn_1 fcnvcnvsn_0 cop csn icnvcnvsn_0 vex icnvcnvsn_1 vex opelcnv 3bitr4i bitri eqrelriiv $.
$}
$( The domain of the singleton of the singleton of a singleton.
       (Contributed by NM, 15-Sep-2004.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
${
	$d x A $.
	idmsnsnsn_0 $f set x $.
	fdmsnsnsn_0 $f class A $.
	dmsnsnsn $p |- dom { { { A } } } = { A } $= fdmsnsnsn_0 cvv wcel fdmsnsnsn_0 csn csn csn cdm fdmsnsnsn_0 csn wceq idmsnsnsn_0 sup_set_class idmsnsnsn_0 sup_set_class cop csn cdm idmsnsnsn_0 sup_set_class csn wceq fdmsnsnsn_0 csn csn csn cdm fdmsnsnsn_0 csn wceq idmsnsnsn_0 fdmsnsnsn_0 cvv idmsnsnsn_0 sup_set_class fdmsnsnsn_0 wceq idmsnsnsn_0 sup_set_class idmsnsnsn_0 sup_set_class cop csn cdm fdmsnsnsn_0 csn csn csn cdm idmsnsnsn_0 sup_set_class csn fdmsnsnsn_0 csn idmsnsnsn_0 sup_set_class fdmsnsnsn_0 wceq idmsnsnsn_0 sup_set_class idmsnsnsn_0 sup_set_class cop csn fdmsnsnsn_0 csn csn csn idmsnsnsn_0 sup_set_class fdmsnsnsn_0 wceq idmsnsnsn_0 sup_set_class idmsnsnsn_0 sup_set_class cop fdmsnsnsn_0 csn csn idmsnsnsn_0 sup_set_class fdmsnsnsn_0 wceq idmsnsnsn_0 sup_set_class idmsnsnsn_0 sup_set_class cop idmsnsnsn_0 sup_set_class csn csn fdmsnsnsn_0 csn csn idmsnsnsn_0 sup_set_class idmsnsnsn_0 vex opid idmsnsnsn_0 sup_set_class fdmsnsnsn_0 wceq idmsnsnsn_0 sup_set_class csn fdmsnsnsn_0 csn idmsnsnsn_0 sup_set_class fdmsnsnsn_0 sneq sneqd syl5eq sneqd dmeqd idmsnsnsn_0 sup_set_class fdmsnsnsn_0 sneq eqeq12d idmsnsnsn_0 sup_set_class idmsnsnsn_0 sup_set_class idmsnsnsn_0 vex dmsnop vtoclg fdmsnsnsn_0 cvv wcel wn c0 csn csn cdm c0 fdmsnsnsn_0 csn csn csn cdm fdmsnsnsn_0 csn c0 c0 csn wcel c0 csn csn cdm c0 wceq c0 0ex snid c0 csn dmsn0el ax-mp fdmsnsnsn_0 cvv wcel wn fdmsnsnsn_0 csn csn csn c0 csn csn fdmsnsnsn_0 cvv wcel wn fdmsnsnsn_0 csn csn c0 csn fdmsnsnsn_0 cvv wcel wn fdmsnsnsn_0 csn c0 fdmsnsnsn_0 cvv wcel wn fdmsnsnsn_0 csn c0 wceq fdmsnsnsn_0 snprc biimpi sneqd sneqd dmeqd fdmsnsnsn_0 cvv wcel wn fdmsnsnsn_0 csn c0 wceq fdmsnsnsn_0 snprc biimpi 3eqtr4a pm2.61i $.
$}
$( The range of a singleton of an ordered pair is the singleton of the second
     member.  (Contributed by NM, 24-Jul-2004.)  (Revised by Mario Carneiro,
     30-Apr-2015.) $)
${
	frnsnopg_0 $f class A $.
	frnsnopg_1 $f class B $.
	frnsnopg_2 $f class V $.
	rnsnopg $p |- ( A e. V -> ran { <. A , B >. } = { B } ) $= frnsnopg_0 frnsnopg_2 wcel frnsnopg_0 frnsnopg_1 cop csn crn frnsnopg_1 frnsnopg_0 cop csn cdm frnsnopg_1 csn frnsnopg_0 frnsnopg_1 cop csn crn frnsnopg_0 frnsnopg_1 cop csn ccnv cdm frnsnopg_1 frnsnopg_0 cop csn cdm frnsnopg_0 frnsnopg_1 cop csn df-rn frnsnopg_1 frnsnopg_0 cop csn cdm frnsnopg_1 frnsnopg_0 cop csn ccnv crn frnsnopg_1 frnsnopg_0 cop csn ccnv ccnv cdm frnsnopg_0 frnsnopg_1 cop csn ccnv cdm frnsnopg_1 frnsnopg_0 cop csn dfdm4 frnsnopg_1 frnsnopg_0 cop csn ccnv df-rn frnsnopg_1 frnsnopg_0 cop csn ccnv ccnv frnsnopg_0 frnsnopg_1 cop csn ccnv frnsnopg_1 frnsnopg_0 cnvcnvsn dmeqi 3eqtri eqtr4i frnsnopg_1 frnsnopg_0 frnsnopg_2 dmsnopg syl5eq $.
$}
$( The range of a singleton of an ordered pair is the singleton of the
       second member.  (Contributed by NM, 24-Jul-2004.)  (Revised by Mario
       Carneiro, 26-Apr-2015.) $)
${
	frnsnop_0 $f class A $.
	frnsnop_1 $f class B $.
	ernsnop_0 $e |- A e. _V $.
	rnsnop $p |- ran { <. A , B >. } = { B } $= frnsnop_0 cvv wcel frnsnop_0 frnsnop_1 cop csn crn frnsnop_1 csn wceq ernsnop_0 frnsnop_0 frnsnop_1 cvv rnsnopg ax-mp $.
$}
$( Extract the first member of an ordered pair.  (See ~ op2nda to extract
       the second member, ~ op1stb for an alternate version, and ~ op1st for
       the preferred version.)  (Contributed by Raph Levien, 4-Dec-2003.) $)
${
	fop1sta_0 $f class A $.
	fop1sta_1 $f class B $.
	eop1sta_0 $e |- A e. _V $.
	eop1sta_1 $e |- B e. _V $.
	op1sta $p |- U. dom { <. A , B >. } = A $= fop1sta_0 fop1sta_1 cop csn cdm cuni fop1sta_0 csn cuni fop1sta_0 fop1sta_0 fop1sta_1 cop csn cdm fop1sta_0 csn fop1sta_0 fop1sta_1 eop1sta_1 dmsnop unieqi fop1sta_0 eop1sta_0 unisn eqtri $.
$}
$( Converse of a singleton of an ordered pair.  (Contributed by NM,
       11-May-1998.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
${
	fcnvsn_0 $f class A $.
	fcnvsn_1 $f class B $.
	ecnvsn_0 $e |- A e. _V $.
	ecnvsn_1 $e |- B e. _V $.
	cnvsn $p |- `' { <. A , B >. } = { <. B , A >. } $= fcnvsn_1 fcnvsn_0 cop csn ccnv ccnv fcnvsn_0 fcnvsn_1 cop csn ccnv fcnvsn_1 fcnvsn_0 cop csn fcnvsn_1 fcnvsn_0 cnvcnvsn fcnvsn_1 fcnvsn_0 cop csn wrel fcnvsn_1 fcnvsn_0 cop csn ccnv ccnv fcnvsn_1 fcnvsn_0 cop csn wceq fcnvsn_1 fcnvsn_0 ecnvsn_1 ecnvsn_0 relsnop fcnvsn_1 fcnvsn_0 cop csn dfrel2 mpbi eqtr3i $.
$}
$( Extract the second member of an ordered pair.  Theorem 5.12(ii) of
       [Monk1] p. 52.  (See ~ op1stb to extract the first member, ~ op2nda for
       an alternate version, and ~ op2nd for the preferred version.)
       (Contributed by NM, 25-Nov-2003.) $)
${
	fop2ndb_0 $f class A $.
	fop2ndb_1 $f class B $.
	eop2ndb_0 $e |- A e. _V $.
	eop2ndb_1 $e |- B e. _V $.
	op2ndb $p |- |^| |^| |^| `' { <. A , B >. } = B $= fop2ndb_0 fop2ndb_1 cop csn ccnv cint cint cint fop2ndb_1 fop2ndb_0 cop cint cint fop2ndb_1 fop2ndb_0 fop2ndb_1 cop csn ccnv cint cint fop2ndb_1 fop2ndb_0 cop cint fop2ndb_0 fop2ndb_1 cop csn ccnv cint fop2ndb_1 fop2ndb_0 cop fop2ndb_0 fop2ndb_1 cop csn ccnv cint fop2ndb_1 fop2ndb_0 cop csn cint fop2ndb_1 fop2ndb_0 cop fop2ndb_0 fop2ndb_1 cop csn ccnv fop2ndb_1 fop2ndb_0 cop csn fop2ndb_0 fop2ndb_1 eop2ndb_0 eop2ndb_1 cnvsn inteqi fop2ndb_1 fop2ndb_0 cop fop2ndb_1 fop2ndb_0 opex intsn eqtri inteqi inteqi fop2ndb_1 fop2ndb_0 eop2ndb_1 eop2ndb_0 op1stb eqtri $.
$}
$( Extract the second member of an ordered pair.  (See ~ op1sta to extract
       the first member, ~ op2ndb for an alternate version, and ~ op2nd for the
       preferred version.)  (Contributed by NM, 17-Feb-2004.)  (Proof shortened
       by Andrew Salmon, 27-Aug-2011.) $)
${
	fop2nda_0 $f class A $.
	fop2nda_1 $f class B $.
	eop2nda_0 $e |- A e. _V $.
	eop2nda_1 $e |- B e. _V $.
	op2nda $p |- U. ran { <. A , B >. } = B $= fop2nda_0 fop2nda_1 cop csn crn cuni fop2nda_1 csn cuni fop2nda_1 fop2nda_0 fop2nda_1 cop csn crn fop2nda_1 csn fop2nda_0 fop2nda_1 eop2nda_0 rnsnop unieqi fop2nda_1 eop2nda_1 unisn eqtri $.
$}
$( Converse of a singleton of an ordered pair.  (Contributed by NM,
       23-Jan-2015.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y $.
	icnvsng_0 $f set x $.
	icnvsng_1 $f set y $.
	fcnvsng_0 $f class A $.
	fcnvsng_1 $f class B $.
	fcnvsng_2 $f class V $.
	fcnvsng_3 $f class W $.
	cnvsng $p |- ( ( A e. V /\ B e. W ) -> `' { <. A , B >. } = { <. B , A >. } ) $= icnvsng_0 sup_set_class icnvsng_1 sup_set_class cop csn ccnv icnvsng_1 sup_set_class icnvsng_0 sup_set_class cop csn wceq fcnvsng_0 icnvsng_1 sup_set_class cop csn ccnv icnvsng_1 sup_set_class fcnvsng_0 cop csn wceq fcnvsng_0 fcnvsng_1 cop csn ccnv fcnvsng_1 fcnvsng_0 cop csn wceq icnvsng_0 icnvsng_1 fcnvsng_0 fcnvsng_1 fcnvsng_2 fcnvsng_3 icnvsng_0 sup_set_class fcnvsng_0 wceq icnvsng_0 sup_set_class icnvsng_1 sup_set_class cop csn ccnv fcnvsng_0 icnvsng_1 sup_set_class cop csn ccnv icnvsng_1 sup_set_class icnvsng_0 sup_set_class cop csn icnvsng_1 sup_set_class fcnvsng_0 cop csn icnvsng_0 sup_set_class fcnvsng_0 wceq icnvsng_0 sup_set_class icnvsng_1 sup_set_class cop csn fcnvsng_0 icnvsng_1 sup_set_class cop csn icnvsng_0 sup_set_class fcnvsng_0 wceq icnvsng_0 sup_set_class icnvsng_1 sup_set_class cop fcnvsng_0 icnvsng_1 sup_set_class cop icnvsng_0 sup_set_class fcnvsng_0 icnvsng_1 sup_set_class opeq1 sneqd cnveqd icnvsng_0 sup_set_class fcnvsng_0 wceq icnvsng_1 sup_set_class icnvsng_0 sup_set_class cop icnvsng_1 sup_set_class fcnvsng_0 cop icnvsng_0 sup_set_class fcnvsng_0 icnvsng_1 sup_set_class opeq2 sneqd eqeq12d icnvsng_1 sup_set_class fcnvsng_1 wceq fcnvsng_0 icnvsng_1 sup_set_class cop csn ccnv fcnvsng_0 fcnvsng_1 cop csn ccnv icnvsng_1 sup_set_class fcnvsng_0 cop csn fcnvsng_1 fcnvsng_0 cop csn icnvsng_1 sup_set_class fcnvsng_1 wceq fcnvsng_0 icnvsng_1 sup_set_class cop csn fcnvsng_0 fcnvsng_1 cop csn icnvsng_1 sup_set_class fcnvsng_1 wceq fcnvsng_0 icnvsng_1 sup_set_class cop fcnvsng_0 fcnvsng_1 cop icnvsng_1 sup_set_class fcnvsng_1 fcnvsng_0 opeq2 sneqd cnveqd icnvsng_1 sup_set_class fcnvsng_1 wceq icnvsng_1 sup_set_class fcnvsng_0 cop fcnvsng_1 fcnvsng_0 cop icnvsng_1 sup_set_class fcnvsng_1 fcnvsng_0 opeq1 sneqd eqeq12d icnvsng_0 sup_set_class icnvsng_1 sup_set_class icnvsng_0 vex icnvsng_1 vex cnvsn vtocl2g $.
$}
$( Swap the members of an ordered pair.  (Contributed by NM, 14-Dec-2008.)
       (Revised by Mario Carneiro, 30-Aug-2015.) $)
${
	fopswap_0 $f class A $.
	fopswap_1 $f class B $.
	opswap $p |- U. `' { <. A , B >. } = <. B , A >. $= fopswap_0 cvv wcel fopswap_1 cvv wcel wa fopswap_0 fopswap_1 cop csn ccnv cuni fopswap_1 fopswap_0 cop wceq fopswap_0 cvv wcel fopswap_1 cvv wcel wa fopswap_0 fopswap_1 cop csn ccnv cuni fopswap_1 fopswap_0 cop csn cuni fopswap_1 fopswap_0 cop fopswap_0 cvv wcel fopswap_1 cvv wcel wa fopswap_0 fopswap_1 cop csn ccnv fopswap_1 fopswap_0 cop csn fopswap_0 fopswap_1 cvv cvv cnvsng unieqd fopswap_1 fopswap_0 cop fopswap_1 fopswap_0 opex unisn syl6eq fopswap_0 cvv wcel fopswap_1 cvv wcel wa wn c0 cuni c0 fopswap_0 fopswap_1 cop csn ccnv cuni fopswap_1 fopswap_0 cop uni0 fopswap_0 cvv wcel fopswap_1 cvv wcel wa wn fopswap_0 fopswap_1 cop csn ccnv c0 fopswap_0 cvv wcel fopswap_1 cvv wcel wa wn fopswap_0 fopswap_1 cop csn ccnv c0 csn ccnv c0 fopswap_0 cvv wcel fopswap_1 cvv wcel wa wn fopswap_0 fopswap_1 cop csn c0 csn fopswap_0 cvv wcel fopswap_1 cvv wcel wa wn fopswap_0 fopswap_1 cop c0 fopswap_0 fopswap_1 opprc sneqd cnveqd cnvsn0 syl6eq unieqd fopswap_0 cvv wcel fopswap_1 cvv wcel wa fopswap_1 cvv wcel fopswap_0 cvv wcel wa fopswap_1 fopswap_0 cop c0 wceq fopswap_0 cvv wcel fopswap_1 cvv wcel ancom fopswap_1 fopswap_0 opprc sylnbi 3eqtr4a pm2.61i $.
$}
$( Membership in a cross product.  This version requires no quantifiers or
       dummy variables.  See also ~ elxp5 , ~ elxp6 , and ~ elxp7 .
       (Contributed by NM, 17-Feb-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ielxp4_0 $f set x $.
	ielxp4_1 $f set y $.
	felxp4_0 $f class A $.
	felxp4_1 $f class B $.
	felxp4_2 $f class C $.
	elxp4 $p |- ( A e. ( B X. C ) <-> ( A = <. U. dom { A } , U. ran { A } >. /\ ( U. dom { A } e. B /\ U. ran { A } e. C ) ) ) $= felxp4_0 felxp4_1 felxp4_2 cxp wcel felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 wex ielxp4_0 wex ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa wa ielxp4_0 wex felxp4_0 felxp4_0 csn cdm cuni felxp4_0 csn crn cuni cop wceq felxp4_0 csn cdm cuni felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa ielxp4_0 ielxp4_1 felxp4_0 felxp4_1 felxp4_2 elxp felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 wex ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa wa ielxp4_0 felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 wex felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq wa ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa wa felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 wex ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa wa ielxp4_1 wex felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa wa ielxp4_1 felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq wa ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa wa felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq wa ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq felxp4_0 csn crn cuni ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop csn crn cuni ielxp4_1 sup_set_class felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq felxp4_0 csn crn ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop csn crn felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq felxp4_0 csn ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop csn felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop sneq rneqd unieqd ielxp4_0 sup_set_class ielxp4_1 sup_set_class ielxp4_0 vex ielxp4_1 vex op2nda syl6req pm4.71ri anbi1i ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa anass bitri exbii felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa wa felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa ielxp4_1 felxp4_0 csn crn cuni felxp4_0 csn crn felxp4_0 csn felxp4_0 snex rnex uniex ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq felxp4_0 ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_2 wcel wa ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq ielxp4_0 sup_set_class ielxp4_1 sup_set_class cop ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop felxp4_0 ielxp4_1 sup_set_class felxp4_0 csn crn cuni ielxp4_0 sup_set_class opeq2 eqeq2d ielxp4_1 sup_set_class felxp4_0 csn crn cuni wceq ielxp4_1 sup_set_class felxp4_2 wcel felxp4_0 csn crn cuni felxp4_2 wcel ielxp4_0 sup_set_class felxp4_1 wcel ielxp4_1 sup_set_class felxp4_0 csn crn cuni felxp4_2 eleq1 anbi2d anbi12d ceqsexv bitri felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq wa ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq felxp4_0 csn cdm cuni ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop csn cdm cuni ielxp4_0 sup_set_class felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq felxp4_0 csn cdm ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop csn cdm felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq felxp4_0 csn ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop csn felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop sneq dmeqd unieqd ielxp4_0 sup_set_class felxp4_0 csn crn cuni ielxp4_0 vex felxp4_0 csn crn felxp4_0 csn felxp4_0 snex rnex uniex op1sta syl6req pm4.71ri anbi1i ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa anass 3bitri exbii felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa felxp4_0 felxp4_0 csn cdm cuni felxp4_0 csn crn cuni cop wceq felxp4_0 csn cdm cuni felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa wa ielxp4_0 felxp4_0 csn cdm cuni felxp4_0 csn cdm felxp4_0 csn felxp4_0 snex dmex uniex ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop wceq felxp4_0 felxp4_0 csn cdm cuni felxp4_0 csn crn cuni cop wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa felxp4_0 csn cdm cuni felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel wa ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq ielxp4_0 sup_set_class felxp4_0 csn crn cuni cop felxp4_0 csn cdm cuni felxp4_0 csn crn cuni cop felxp4_0 ielxp4_0 sup_set_class felxp4_0 csn cdm cuni felxp4_0 csn crn cuni opeq1 eqeq2d ielxp4_0 sup_set_class felxp4_0 csn cdm cuni wceq ielxp4_0 sup_set_class felxp4_1 wcel felxp4_0 csn cdm cuni felxp4_1 wcel felxp4_0 csn crn cuni felxp4_2 wcel ielxp4_0 sup_set_class felxp4_0 csn cdm cuni felxp4_1 eleq1 anbi1d anbi12d ceqsexv 3bitri $.
$}
$( Membership in a cross product requiring no quantifiers or dummy
       variables.  Provides a slightly shorter version of ~ elxp4 when the
       double intersection does not create class existence problems (caused by
       ~ int0 ).  (Contributed by NM, 1-Aug-2004.) $)
${
	$d x y A $.
	$d x y B $.
	$d x y C $.
	ielxp5_0 $f set x $.
	ielxp5_1 $f set y $.
	felxp5_0 $f class A $.
	felxp5_1 $f class B $.
	felxp5_2 $f class C $.
	elxp5 $p |- ( A e. ( B X. C ) <-> ( A = <. |^| |^| A , U. ran { A } >. /\ ( |^| |^| A e. B /\ U. ran { A } e. C ) ) ) $= felxp5_0 felxp5_1 felxp5_2 cxp wcel felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 wex ielxp5_0 wex ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa wa ielxp5_0 wex felxp5_0 felxp5_0 cint cint felxp5_0 csn crn cuni cop wceq felxp5_0 cint cint felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_0 ielxp5_1 felxp5_0 felxp5_1 felxp5_2 elxp felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 wex ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa wa ielxp5_0 felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 wex felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq wa ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa wa felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 wex ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa wa ielxp5_1 wex felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa wa ielxp5_1 felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq wa ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa wa felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq wa ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq felxp5_0 csn crn cuni ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop csn crn cuni ielxp5_1 sup_set_class felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq felxp5_0 csn crn ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop csn crn felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq felxp5_0 csn ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop csn felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop sneq rneqd unieqd ielxp5_0 sup_set_class ielxp5_1 sup_set_class ielxp5_0 vex ielxp5_1 vex op2nda syl6req pm4.71ri anbi1i ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa anass bitri exbii felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa wa felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_1 felxp5_0 csn crn cuni felxp5_0 csn crn felxp5_0 csn felxp5_0 snex rnex uniex ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq felxp5_0 ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_2 wcel wa ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq ielxp5_0 sup_set_class ielxp5_1 sup_set_class cop ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop felxp5_0 ielxp5_1 sup_set_class felxp5_0 csn crn cuni ielxp5_0 sup_set_class opeq2 eqeq2d ielxp5_1 sup_set_class felxp5_0 csn crn cuni wceq ielxp5_1 sup_set_class felxp5_2 wcel felxp5_0 csn crn cuni felxp5_2 wcel ielxp5_0 sup_set_class felxp5_1 wcel ielxp5_1 sup_set_class felxp5_0 csn crn cuni felxp5_2 eleq1 anbi2d anbi12d ceqsexv bitri felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq wa ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq felxp5_0 cint cint ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop cint cint ielxp5_0 sup_set_class felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq felxp5_0 cint ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop cint felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop inteq inteqd ielxp5_0 sup_set_class felxp5_0 csn crn cuni ielxp5_0 vex felxp5_0 csn crn felxp5_0 csn felxp5_0 snex rnex uniex op1stb syl6req pm4.71ri anbi1i ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa anass 3bitri exbii ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa wa ielxp5_0 wex felxp5_0 cint cint cvv wcel felxp5_0 felxp5_0 cint cint felxp5_0 csn crn cuni cop wceq felxp5_0 cint cint felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa wa felxp5_0 cint cint cvv wcel ielxp5_0 ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 cint cint cvv wcel felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_0 sup_set_class felxp5_0 cint cint wceq ielxp5_0 sup_set_class cvv wcel felxp5_0 cint cint cvv wcel ielxp5_0 vex ielxp5_0 sup_set_class felxp5_0 cint cint cvv eleq1 mpbii adantr exlimiv felxp5_0 cint cint felxp5_1 wcel felxp5_0 cint cint cvv wcel felxp5_0 felxp5_0 cint cint felxp5_0 csn crn cuni cop wceq felxp5_0 csn crn cuni felxp5_2 wcel felxp5_0 cint cint felxp5_1 elex ad2antrl felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa felxp5_0 felxp5_0 cint cint felxp5_0 csn crn cuni cop wceq felxp5_0 cint cint felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa wa ielxp5_0 felxp5_0 cint cint cvv ielxp5_0 sup_set_class felxp5_0 cint cint wceq felxp5_0 ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop wceq felxp5_0 felxp5_0 cint cint felxp5_0 csn crn cuni cop wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa felxp5_0 cint cint felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel wa ielxp5_0 sup_set_class felxp5_0 cint cint wceq ielxp5_0 sup_set_class felxp5_0 csn crn cuni cop felxp5_0 cint cint felxp5_0 csn crn cuni cop felxp5_0 ielxp5_0 sup_set_class felxp5_0 cint cint felxp5_0 csn crn cuni opeq1 eqeq2d ielxp5_0 sup_set_class felxp5_0 cint cint wceq ielxp5_0 sup_set_class felxp5_1 wcel felxp5_0 cint cint felxp5_1 wcel felxp5_0 csn crn cuni felxp5_2 wcel ielxp5_0 sup_set_class felxp5_0 cint cint felxp5_1 eleq1 anbi1d anbi12d ceqsexgv pm5.21nii 3bitri $.
$}
$( An image under the converse of a restriction.  (Contributed by Jeff
       Hankins, 12-Jul-2009.) $)
${
	$d s t A $.
	$d s t B $.
	$d s t F $.
	icnvresima_0 $f set t $.
	icnvresima_1 $f set s $.
	fcnvresima_0 $f class A $.
	fcnvresima_1 $f class B $.
	fcnvresima_2 $f class F $.
	cnvresima $p |- ( `' ( F |` A ) " B ) = ( ( `' F " B ) i^i A ) $= icnvresima_0 fcnvresima_2 fcnvresima_0 cres ccnv fcnvresima_1 cima fcnvresima_2 ccnv fcnvresima_1 cima fcnvresima_0 cin icnvresima_0 sup_set_class fcnvresima_2 fcnvresima_0 cres ccnv fcnvresima_1 cima wcel icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel wa icnvresima_1 wex icnvresima_0 sup_set_class fcnvresima_2 ccnv fcnvresima_1 cima fcnvresima_0 cin wcel icnvresima_1 icnvresima_0 sup_set_class fcnvresima_2 fcnvresima_0 cres ccnv fcnvresima_1 icnvresima_0 vex elima3 icnvresima_0 sup_set_class fcnvresima_2 ccnv fcnvresima_1 cima wcel icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_1 wex icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_0 sup_set_class fcnvresima_2 ccnv fcnvresima_1 cima fcnvresima_0 cin wcel icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel wa icnvresima_1 wex icnvresima_0 sup_set_class fcnvresima_2 ccnv fcnvresima_1 cima wcel icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_1 wex icnvresima_0 sup_set_class fcnvresima_0 wcel icnvresima_1 icnvresima_0 sup_set_class fcnvresima_2 ccnv fcnvresima_1 icnvresima_0 vex elima3 anbi1i icnvresima_0 sup_set_class fcnvresima_2 ccnv fcnvresima_1 cima fcnvresima_0 elin icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel wa icnvresima_1 wex icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 wex icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_1 wex icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel wa icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel wa icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel icnvresima_0 sup_set_class fcnvresima_0 wcel wa wa icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 fcnvresima_0 cres ccnv wcel icnvresima_0 sup_set_class icnvresima_1 sup_set_class cop fcnvresima_2 fcnvresima_0 cres wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 sup_set_class icnvresima_0 sup_set_class fcnvresima_2 fcnvresima_0 cres icnvresima_1 vex icnvresima_0 vex opelcnv icnvresima_0 sup_set_class icnvresima_1 sup_set_class cop fcnvresima_2 fcnvresima_0 cres wcel icnvresima_0 sup_set_class icnvresima_1 sup_set_class cop fcnvresima_2 wcel icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel icnvresima_0 sup_set_class fcnvresima_0 wcel wa icnvresima_0 sup_set_class icnvresima_1 sup_set_class fcnvresima_2 fcnvresima_0 icnvresima_1 vex opelres icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel icnvresima_0 sup_set_class icnvresima_1 sup_set_class cop fcnvresima_2 wcel icnvresima_0 sup_set_class fcnvresima_0 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class fcnvresima_2 icnvresima_1 vex icnvresima_0 vex opelcnv anbi1i bitr4i bitri anbi2i icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel icnvresima_0 sup_set_class fcnvresima_0 wcel anass bitr4i exbii icnvresima_1 sup_set_class fcnvresima_1 wcel icnvresima_1 sup_set_class icnvresima_0 sup_set_class cop fcnvresima_2 ccnv wcel wa icnvresima_0 sup_set_class fcnvresima_0 wcel icnvresima_1 19.41v bitri 3bitr4ri bitri eqriv $.
$}
$( A class restricted to its domain equals its double converse.  (Contributed
     by NM, 8-Apr-2007.) $)
${
	fresdm2_0 $f class A $.
	resdm2 $p |- ( A |` dom A ) = `' `' A $= fresdm2_0 ccnv ccnv fresdm2_0 ccnv ccnv cdm cres fresdm2_0 fresdm2_0 ccnv ccnv cdm cres fresdm2_0 ccnv ccnv fresdm2_0 fresdm2_0 cdm cres fresdm2_0 fresdm2_0 ccnv ccnv cdm rescnvcnv fresdm2_0 ccnv ccnv wrel fresdm2_0 ccnv ccnv fresdm2_0 ccnv ccnv cdm cres fresdm2_0 ccnv ccnv wceq fresdm2_0 ccnv relcnv fresdm2_0 ccnv ccnv resdm ax-mp fresdm2_0 ccnv ccnv cdm fresdm2_0 cdm fresdm2_0 fresdm2_0 dmcnvcnv reseq2i 3eqtr3ri $.
$}
$( Restriction to the domain of a restriction.  (Contributed by NM,
     8-Apr-2007.) $)
${
	fresdmres_0 $f class A $.
	fresdmres_1 $f class B $.
	resdmres $p |- ( A |` dom ( A |` B ) ) = ( A |` B ) $= fresdmres_0 fresdmres_0 fresdmres_1 cres cdm cres fresdmres_0 ccnv ccnv fresdmres_1 cres fresdmres_0 fresdmres_1 cres fresdmres_0 fresdmres_1 cvv cxp fresdmres_0 cdm cvv cxp cin cin fresdmres_0 ccnv ccnv fresdmres_1 cvv cxp cin fresdmres_0 fresdmres_0 fresdmres_1 cres cdm cres fresdmres_0 ccnv ccnv fresdmres_1 cres fresdmres_0 fresdmres_1 cvv cxp fresdmres_0 cdm cvv cxp cin cin fresdmres_1 cvv cxp fresdmres_0 fresdmres_0 cdm cvv cxp cin cin fresdmres_1 cvv cxp fresdmres_0 ccnv ccnv cin fresdmres_0 ccnv ccnv fresdmres_1 cvv cxp cin fresdmres_0 fresdmres_1 cvv cxp fresdmres_0 cdm cvv cxp in12 fresdmres_0 fresdmres_0 cdm cvv cxp cin fresdmres_0 ccnv ccnv fresdmres_1 cvv cxp fresdmres_0 fresdmres_0 cdm cres fresdmres_0 fresdmres_0 cdm cvv cxp cin fresdmres_0 ccnv ccnv fresdmres_0 fresdmres_0 cdm df-res fresdmres_0 resdm2 eqtr3i ineq2i fresdmres_1 cvv cxp fresdmres_0 ccnv ccnv incom 3eqtri fresdmres_0 fresdmres_0 fresdmres_1 cres cdm cres fresdmres_0 fresdmres_0 fresdmres_1 cres cdm cvv cxp cin fresdmres_0 fresdmres_1 cvv cxp fresdmres_0 cdm cvv cxp cin cin fresdmres_0 fresdmres_0 fresdmres_1 cres cdm df-res fresdmres_0 fresdmres_1 cres cdm cvv cxp fresdmres_1 cvv cxp fresdmres_0 cdm cvv cxp cin fresdmres_0 fresdmres_0 fresdmres_1 cres cdm cvv cxp fresdmres_1 fresdmres_0 cdm cin cvv cxp fresdmres_1 cvv cxp fresdmres_0 cdm cvv cxp cin fresdmres_0 fresdmres_1 cres cdm fresdmres_1 fresdmres_0 cdm cin cvv fresdmres_0 fresdmres_1 dmres xpeq1i fresdmres_1 fresdmres_0 cdm cvv xpindir eqtri ineq2i eqtri fresdmres_0 ccnv ccnv fresdmres_1 df-res 3eqtr4i fresdmres_0 fresdmres_1 rescnvcnv eqtri $.
$}
$( The image of the domain of a restriction.  (Contributed by NM,
     8-Apr-2007.) $)
${
	fimadmres_0 $f class A $.
	fimadmres_1 $f class B $.
	imadmres $p |- ( A " dom ( A |` B ) ) = ( A " B ) $= fimadmres_0 fimadmres_0 fimadmres_1 cres cdm cres crn fimadmres_0 fimadmres_1 cres crn fimadmres_0 fimadmres_0 fimadmres_1 cres cdm cima fimadmres_0 fimadmres_1 cima fimadmres_0 fimadmres_0 fimadmres_1 cres cdm cres fimadmres_0 fimadmres_1 cres fimadmres_0 fimadmres_1 resdmres rneqi fimadmres_0 fimadmres_0 fimadmres_1 cres cdm df-ima fimadmres_0 fimadmres_1 df-ima 3eqtr4i $.
$}
$( The preimage of a function in maps-to notation.  (Contributed by Stefan
       O'Rear, 25-Jan-2015.) $)
${
	$d x y C $.
	$d y A $.
	$d y B $.
	$d y F $.
	imptpreima_0 $f set y $.
	fmptpreima_0 $f set x $.
	fmptpreima_1 $f class A $.
	fmptpreima_2 $f class B $.
	fmptpreima_3 $f class C $.
	fmptpreima_4 $f class F $.
	emptpreima_0 $e |- F = ( x e. A |-> B ) $.
	mptpreima $p |- ( `' F " C ) = { x e. A | B e. C } $= fmptpreima_4 ccnv fmptpreima_3 cima fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 cima fmptpreima_2 fmptpreima_3 wcel fmptpreima_0 fmptpreima_1 crab fmptpreima_4 ccnv fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 fmptpreima_4 ccnv fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa fmptpreima_0 imptpreima_0 copab ccnv fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_4 fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa fmptpreima_0 imptpreima_0 copab fmptpreima_4 fmptpreima_0 fmptpreima_1 fmptpreima_2 cmpt fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa fmptpreima_0 imptpreima_0 copab emptpreima_0 fmptpreima_0 imptpreima_0 fmptpreima_1 fmptpreima_2 df-mpt eqtri cnveqi fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa fmptpreima_0 imptpreima_0 cnvopab eqtri imaeq1i fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 cima fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 cres crn fmptpreima_2 fmptpreima_3 wcel fmptpreima_0 fmptpreima_1 crab fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 df-ima fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 cres crn imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 fmptpreima_0 copab crn fmptpreima_2 fmptpreima_3 wcel fmptpreima_0 fmptpreima_1 crab fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 copab fmptpreima_3 cres imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 fmptpreima_0 copab fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 fmptpreima_0 fmptpreima_3 resopab rneqi imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 wex fmptpreima_0 cab fmptpreima_0 sup_set_class fmptpreima_1 wcel fmptpreima_2 fmptpreima_3 wcel wa fmptpreima_0 cab imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 fmptpreima_0 copab crn fmptpreima_2 fmptpreima_3 wcel fmptpreima_0 fmptpreima_1 crab imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 wex fmptpreima_0 sup_set_class fmptpreima_1 wcel fmptpreima_2 fmptpreima_3 wcel wa fmptpreima_0 imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 wex fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa wa imptpreima_0 wex fmptpreima_0 sup_set_class fmptpreima_1 wcel fmptpreima_2 fmptpreima_3 wcel wa imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa wa imptpreima_0 imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa imptpreima_0 sup_set_class fmptpreima_3 wcel wa fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa wa imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa ancom fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel anass bitri exbii fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa wa imptpreima_0 wex fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa imptpreima_0 wex wa fmptpreima_0 sup_set_class fmptpreima_1 wcel fmptpreima_2 fmptpreima_3 wcel wa fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa imptpreima_0 19.42v imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa imptpreima_0 wex fmptpreima_2 fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel fmptpreima_2 fmptpreima_3 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq imptpreima_0 sup_set_class fmptpreima_3 wcel wa imptpreima_0 wex imptpreima_0 fmptpreima_2 fmptpreima_3 df-clel bicomi anbi2i bitri bitri abbii imptpreima_0 sup_set_class fmptpreima_3 wcel fmptpreima_0 sup_set_class fmptpreima_1 wcel imptpreima_0 sup_set_class fmptpreima_2 wceq wa wa imptpreima_0 fmptpreima_0 rnopab fmptpreima_2 fmptpreima_3 wcel fmptpreima_0 fmptpreima_1 df-rab 3eqtr4i eqtri eqtri eqtri $.
$}
$( Converse singleton image of a function defined by maps-to.  (Contributed
       by Stefan O'Rear, 25-Jan-2015.) $)
${
	$d x C $.
	$d x V $.
	fmptiniseg_0 $f set x $.
	fmptiniseg_1 $f class A $.
	fmptiniseg_2 $f class B $.
	fmptiniseg_3 $f class C $.
	fmptiniseg_4 $f class F $.
	fmptiniseg_5 $f class V $.
	emptiniseg_0 $e |- F = ( x e. A |-> B ) $.
	mptiniseg $p |- ( C e. V -> ( `' F " { C } ) = { x e. A | B = C } ) $= fmptiniseg_3 fmptiniseg_5 wcel fmptiniseg_4 ccnv fmptiniseg_3 csn cima fmptiniseg_2 fmptiniseg_3 csn wcel fmptiniseg_0 fmptiniseg_1 crab fmptiniseg_2 fmptiniseg_3 wceq fmptiniseg_0 fmptiniseg_1 crab fmptiniseg_0 fmptiniseg_1 fmptiniseg_2 fmptiniseg_3 csn fmptiniseg_4 emptiniseg_0 mptpreima fmptiniseg_3 fmptiniseg_5 wcel fmptiniseg_2 fmptiniseg_3 csn wcel fmptiniseg_2 fmptiniseg_3 wceq fmptiniseg_0 fmptiniseg_1 fmptiniseg_2 fmptiniseg_3 fmptiniseg_5 elsnc2g rabbidv syl5eq $.
$}
$( The domain of the mapping operation in general.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 22-Mar-2015.) $)
${
	fdmmpt_0 $f set x $.
	fdmmpt_1 $f class A $.
	fdmmpt_2 $f class B $.
	fdmmpt_3 $f class F $.
	edmmpt_0 $e |- F = ( x e. A |-> B ) $.
	dmmpt $p |- dom F = { x e. A | B e. _V } $= fdmmpt_3 cdm fdmmpt_3 ccnv crn fdmmpt_3 ccnv cvv cima fdmmpt_2 cvv wcel fdmmpt_0 fdmmpt_1 crab fdmmpt_3 dfdm4 fdmmpt_3 ccnv dfrn4 fdmmpt_0 fdmmpt_1 fdmmpt_2 cvv fdmmpt_3 edmmpt_0 mptpreima 3eqtri $.
$}
$( The domain of a mapping is a subset of its base class.  (Contributed by
       Scott Fenton, 17-Jun-2013.) $)
${
	$d x A $.
	fdmmptss_0 $f set x $.
	fdmmptss_1 $f class A $.
	fdmmptss_2 $f class B $.
	fdmmptss_3 $f class F $.
	edmmptss_0 $e |- F = ( x e. A |-> B ) $.
	dmmptss $p |- dom F C_ A $= fdmmptss_3 cdm fdmmptss_2 cvv wcel fdmmptss_0 fdmmptss_1 crab fdmmptss_1 fdmmptss_0 fdmmptss_1 fdmmptss_2 fdmmptss_3 edmmptss_0 dmmpt fdmmptss_2 cvv wcel fdmmptss_0 fdmmptss_1 ssrab2 eqsstri $.
$}
$( The domain of the mapping operation is the stated domain, if the
       function value is always a set.  (Contributed by Mario Carneiro,
       9-Feb-2013.)  (Revised by Mario Carneiro, 14-Sep-2013.) $)
${
	$d A x $.
	fdmmptg_0 $f set x $.
	fdmmptg_1 $f class A $.
	fdmmptg_2 $f class B $.
	fdmmptg_3 $f class V $.
	dmmptg $p |- ( A. x e. A B e. V -> dom ( x e. A |-> B ) = A ) $= fdmmptg_2 fdmmptg_3 wcel fdmmptg_0 fdmmptg_1 wral fdmmptg_1 fdmmptg_2 cvv wcel fdmmptg_0 fdmmptg_1 crab fdmmptg_0 fdmmptg_1 fdmmptg_2 cmpt cdm fdmmptg_2 fdmmptg_3 wcel fdmmptg_0 fdmmptg_1 wral fdmmptg_2 cvv wcel fdmmptg_0 fdmmptg_1 wral fdmmptg_1 fdmmptg_2 cvv wcel fdmmptg_0 fdmmptg_1 crab wceq fdmmptg_2 fdmmptg_3 wcel fdmmptg_2 cvv wcel fdmmptg_0 fdmmptg_1 fdmmptg_2 fdmmptg_3 elex ralimi fdmmptg_2 cvv wcel fdmmptg_0 fdmmptg_1 rabid2 sylibr fdmmptg_0 fdmmptg_1 fdmmptg_2 fdmmptg_0 fdmmptg_1 fdmmptg_2 cmpt fdmmptg_0 fdmmptg_1 fdmmptg_2 cmpt eqid dmmpt syl6reqr $.
$}
$( A composition is a relation.  Exercise 24 of [TakeutiZaring] p. 25.
       (Contributed by NM, 26-Jan-1997.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	irelco_0 $f set x $.
	irelco_1 $f set y $.
	irelco_2 $f set z $.
	frelco_0 $f class A $.
	frelco_1 $f class B $.
	relco $p |- Rel ( A o. B ) $= irelco_0 sup_set_class irelco_2 sup_set_class frelco_1 wbr irelco_2 sup_set_class irelco_1 sup_set_class frelco_0 wbr wa irelco_2 wex irelco_0 irelco_1 frelco_0 frelco_1 ccom irelco_0 irelco_1 irelco_2 frelco_0 frelco_1 df-co relopabi $.
$}
$( Alternate definition of a class composition, using only one bound
       variable.  (Contributed by NM, 19-Dec-2008.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	idfco2_0 $f set y $.
	idfco2_1 $f set z $.
	fdfco2_0 $f set x $.
	fdfco2_1 $f class A $.
	fdfco2_2 $f class B $.
	dfco2 $p |- ( A o. B ) = U_ x e. _V ( ( `' B " { x } ) X. ( A " { x } ) ) $= idfco2_0 idfco2_1 fdfco2_1 fdfco2_2 ccom fdfco2_0 cvv fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp ciun fdfco2_1 fdfco2_2 relco fdfco2_0 cvv fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp ciun wrel fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wrel fdfco2_0 cvv fdfco2_0 cvv fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp reliun fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wrel fdfco2_0 sup_set_class cvv wcel fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima relxp a1i mprgbir idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 fdfco2_2 ccom wcel idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel fdfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 wcel wa fdfco2_0 wex idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_0 cvv fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp ciun wcel idfco2_0 sup_set_class cvv wcel idfco2_1 sup_set_class cvv wcel idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 fdfco2_2 ccom wcel idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel fdfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 wcel wa fdfco2_0 wex wb idfco2_0 vex idfco2_1 vex fdfco2_0 idfco2_0 sup_set_class idfco2_1 sup_set_class fdfco2_1 fdfco2_2 cvv cvv opelco2g mp2an idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_0 cvv fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp ciun wcel idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wcel fdfco2_0 cvv wrex idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wcel fdfco2_0 wex idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel fdfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 wcel wa fdfco2_0 wex fdfco2_0 idfco2_0 sup_set_class idfco2_1 sup_set_class cop cvv fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp eliun idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wcel fdfco2_0 rexv idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wcel idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel fdfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 wcel wa fdfco2_0 idfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima cxp wcel idfco2_0 sup_set_class fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima wcel idfco2_1 sup_set_class fdfco2_1 fdfco2_0 sup_set_class csn cima wcel wa idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel fdfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 wcel wa idfco2_0 sup_set_class idfco2_1 sup_set_class fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima fdfco2_1 fdfco2_0 sup_set_class csn cima opelxp idfco2_0 sup_set_class fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima wcel idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel idfco2_1 sup_set_class fdfco2_1 fdfco2_0 sup_set_class csn cima wcel fdfco2_0 sup_set_class idfco2_1 sup_set_class cop fdfco2_1 wcel idfco2_0 sup_set_class fdfco2_2 ccnv fdfco2_0 sup_set_class csn cima wcel fdfco2_0 sup_set_class idfco2_0 sup_set_class cop fdfco2_2 ccnv wcel idfco2_0 sup_set_class fdfco2_0 sup_set_class cop fdfco2_2 wcel fdfco2_2 ccnv fdfco2_0 sup_set_class idfco2_0 sup_set_class fdfco2_0 vex idfco2_0 vex elimasn fdfco2_0 sup_set_class idfco2_0 sup_set_class fdfco2_2 fdfco2_0 vex idfco2_0 vex opelcnv bitri fdfco2_1 fdfco2_0 sup_set_class idfco2_1 sup_set_class fdfco2_0 vex idfco2_1 vex elimasn anbi12i bitri exbii 3bitrri bitri eqrelriiv $.
$}
$( Generalization of ~ dfco2 , where ` C ` can have any value between
       ` dom A i^i ran B ` and ` _V ` .  (Contributed by NM, 21-Dec-2008.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d w x y z A $.
	$d w x y z B $.
	$d w x y z C $.
	idfco2a_0 $f set y $.
	idfco2a_1 $f set z $.
	idfco2a_2 $f set w $.
	fdfco2a_0 $f set x $.
	fdfco2a_1 $f class A $.
	fdfco2a_2 $f class B $.
	fdfco2a_3 $f class C $.
	dfco2a $p |- ( ( dom A i^i ran B ) C_ C -> ( A o. B ) = U_ x e. C ( ( `' B " { x } ) X. ( A " { x } ) ) ) $= fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss fdfco2a_1 fdfco2a_2 ccom fdfco2a_0 cvv fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp ciun fdfco2a_0 fdfco2a_3 fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp ciun fdfco2a_0 fdfco2a_1 fdfco2a_2 dfco2 fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss idfco2a_0 fdfco2a_0 cvv fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp ciun fdfco2a_0 fdfco2a_3 fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp ciun fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 cvv wrex idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 fdfco2a_3 wrex idfco2a_0 sup_set_class fdfco2a_0 cvv fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp ciun wcel idfco2a_0 sup_set_class fdfco2a_0 fdfco2a_3 fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp ciun wcel fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 wex fdfco2a_0 sup_set_class fdfco2a_3 wcel idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel wa fdfco2a_0 wex idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 cvv wrex idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 fdfco2a_3 wrex fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 sup_set_class fdfco2a_3 wcel idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel wa fdfco2a_0 fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 sup_set_class fdfco2a_3 wcel idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 sup_set_class fdfco2a_1 cdm fdfco2a_2 crn cin wcel fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 wss fdfco2a_0 sup_set_class fdfco2a_3 wcel idfco2a_0 sup_set_class idfco2a_1 sup_set_class idfco2a_2 sup_set_class cop wceq idfco2a_1 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima wcel idfco2a_2 sup_set_class fdfco2a_1 fdfco2a_0 sup_set_class csn cima wcel wa wa idfco2a_2 wex idfco2a_1 wex fdfco2a_0 sup_set_class fdfco2a_1 cdm wcel fdfco2a_0 sup_set_class fdfco2a_2 crn wcel wa idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 sup_set_class fdfco2a_1 cdm fdfco2a_2 crn cin wcel idfco2a_0 sup_set_class idfco2a_1 sup_set_class idfco2a_2 sup_set_class cop wceq idfco2a_1 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima wcel idfco2a_2 sup_set_class fdfco2a_1 fdfco2a_0 sup_set_class csn cima wcel wa wa fdfco2a_0 sup_set_class fdfco2a_1 cdm wcel fdfco2a_0 sup_set_class fdfco2a_2 crn wcel wa idfco2a_1 idfco2a_2 idfco2a_1 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima wcel idfco2a_2 sup_set_class fdfco2a_1 fdfco2a_0 sup_set_class csn cima wcel wa fdfco2a_0 sup_set_class fdfco2a_1 cdm wcel fdfco2a_0 sup_set_class fdfco2a_2 crn wcel wa idfco2a_0 sup_set_class idfco2a_1 sup_set_class idfco2a_2 sup_set_class cop wceq idfco2a_1 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima wcel fdfco2a_0 sup_set_class fdfco2a_2 crn wcel idfco2a_2 sup_set_class fdfco2a_1 fdfco2a_0 sup_set_class csn cima wcel fdfco2a_0 sup_set_class fdfco2a_1 cdm wcel idfco2a_1 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima wcel idfco2a_1 sup_set_class fdfco2a_0 sup_set_class fdfco2a_2 wbr fdfco2a_0 sup_set_class fdfco2a_2 crn wcel fdfco2a_0 sup_set_class cvv wcel idfco2a_1 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima wcel idfco2a_1 sup_set_class fdfco2a_0 sup_set_class fdfco2a_2 wbr wb fdfco2a_0 vex fdfco2a_2 fdfco2a_0 sup_set_class idfco2a_1 sup_set_class cvv idfco2a_1 vex eliniseg ax-mp idfco2a_1 sup_set_class fdfco2a_0 sup_set_class fdfco2a_2 idfco2a_1 vex fdfco2a_0 vex brelrn sylbi idfco2a_2 sup_set_class fdfco2a_1 fdfco2a_0 sup_set_class csn cima wcel fdfco2a_0 sup_set_class idfco2a_2 sup_set_class cop fdfco2a_1 wcel fdfco2a_0 sup_set_class fdfco2a_1 cdm wcel fdfco2a_1 fdfco2a_0 sup_set_class idfco2a_2 sup_set_class fdfco2a_0 vex idfco2a_2 vex elimasn fdfco2a_0 sup_set_class idfco2a_2 sup_set_class fdfco2a_1 fdfco2a_0 vex idfco2a_2 vex opeldm sylbi anim12ci adantl exlimivv idfco2a_1 idfco2a_2 idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima elxp fdfco2a_0 sup_set_class fdfco2a_1 cdm fdfco2a_2 crn elin 3imtr4i fdfco2a_1 cdm fdfco2a_2 crn cin fdfco2a_3 fdfco2a_0 sup_set_class ssel syl5 pm4.71rd exbidv idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 rexv idfco2a_0 sup_set_class fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp wcel fdfco2a_0 fdfco2a_3 df-rex 3bitr4g fdfco2a_0 idfco2a_0 sup_set_class cvv fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp eliun fdfco2a_0 idfco2a_0 sup_set_class fdfco2a_3 fdfco2a_2 ccnv fdfco2a_0 sup_set_class csn cima fdfco2a_1 fdfco2a_0 sup_set_class csn cima cxp eliun 3bitr4g eqrdv syl5eq $.
$}
$( Class composition distributes over union.  (Contributed by NM,
       21-Dec-2008.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	icoundi_0 $f set x $.
	icoundi_1 $f set y $.
	icoundi_2 $f set z $.
	fcoundi_0 $f class A $.
	fcoundi_1 $f class B $.
	fcoundi_2 $f class C $.
	coundi $p |- ( A o. ( B u. C ) ) = ( ( A o. B ) u. ( A o. C ) ) $= icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab cun icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab fcoundi_0 fcoundi_1 ccom fcoundi_0 fcoundi_2 ccom cun fcoundi_0 fcoundi_1 fcoundi_2 cun ccom icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab cun icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex wo icoundi_0 icoundi_1 copab icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 unopab icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex wo icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa wo icoundi_2 wex icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex wo icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa wo icoundi_2 icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr wo icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa wo icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 cun wbr icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr wo icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 fcoundi_2 brun anbi1i icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr andir bitri exbii icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 19.43 bitr2i opabbii eqtri fcoundi_0 fcoundi_1 ccom icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_1 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab fcoundi_0 fcoundi_2 ccom icoundi_0 sup_set_class icoundi_2 sup_set_class fcoundi_2 wbr icoundi_2 sup_set_class icoundi_1 sup_set_class fcoundi_0 wbr wa icoundi_2 wex icoundi_0 icoundi_1 copab icoundi_0 icoundi_1 icoundi_2 fcoundi_0 fcoundi_1 df-co icoundi_0 icoundi_1 icoundi_2 fcoundi_0 fcoundi_2 df-co uneq12i icoundi_0 icoundi_1 icoundi_2 fcoundi_0 fcoundi_1 fcoundi_2 cun df-co 3eqtr4ri $.
$}
$( Class composition distributes over union.  (Contributed by NM,
       21-Dec-2008.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	icoundir_0 $f set x $.
	icoundir_1 $f set y $.
	icoundir_2 $f set z $.
	fcoundir_0 $f class A $.
	fcoundir_1 $f class B $.
	fcoundir_2 $f class C $.
	coundir $p |- ( ( A u. B ) o. C ) = ( ( A o. C ) u. ( B o. C ) ) $= icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab cun icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab fcoundir_0 fcoundir_2 ccom fcoundir_1 fcoundir_2 ccom cun fcoundir_0 fcoundir_1 cun fcoundir_2 ccom icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab cun icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex wo icoundir_0 icoundir_2 copab icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex icoundir_0 icoundir_2 unopab icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex wo icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr wa icoundir_1 wex icoundir_0 icoundir_2 icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr wa icoundir_1 wex icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa wo icoundir_1 wex icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex wo icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa wo icoundir_1 icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wo wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa wo icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 cun wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wo icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 fcoundir_1 brun anbi2i icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr andi bitri exbii icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 19.43 bitr2i opabbii eqtri fcoundir_0 fcoundir_2 ccom icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_0 wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab fcoundir_1 fcoundir_2 ccom icoundir_0 sup_set_class icoundir_1 sup_set_class fcoundir_2 wbr icoundir_1 sup_set_class icoundir_2 sup_set_class fcoundir_1 wbr wa icoundir_1 wex icoundir_0 icoundir_2 copab icoundir_0 icoundir_2 icoundir_1 fcoundir_0 fcoundir_2 df-co icoundir_0 icoundir_2 icoundir_1 fcoundir_1 fcoundir_2 df-co uneq12i icoundir_0 icoundir_2 icoundir_1 fcoundir_0 fcoundir_1 cun fcoundir_2 df-co 3eqtr4ri $.
$}
$( Restricted first member of a class composition.  (Contributed by NM,
       12-Oct-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	icores_0 $f set x $.
	icores_1 $f set y $.
	icores_2 $f set z $.
	fcores_0 $f class A $.
	fcores_1 $f class B $.
	fcores_2 $f class C $.
	cores $p |- ( ran B C_ C -> ( ( A |` C ) o. B ) = ( A o. B ) ) $= fcores_1 crn fcores_2 wss icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 cres wbr wa icores_1 wex icores_2 icores_0 copab icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 wbr wa icores_1 wex icores_2 icores_0 copab fcores_0 fcores_2 cres fcores_1 ccom fcores_0 fcores_1 ccom fcores_1 crn fcores_2 wss icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 cres wbr wa icores_1 wex icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 wbr wa icores_1 wex icores_2 icores_0 fcores_1 crn fcores_2 wss icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 cres wbr wa icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 wbr wa icores_1 fcores_1 crn fcores_2 wss icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 cres wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 wbr icores_2 sup_set_class icores_1 sup_set_class fcores_1 wbr icores_1 sup_set_class fcores_1 crn wcel fcores_1 crn fcores_2 wss icores_1 sup_set_class fcores_2 wcel icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 cres wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 wbr wb icores_2 sup_set_class icores_1 sup_set_class fcores_1 icores_2 vex icores_1 vex brelrn fcores_1 crn fcores_2 icores_1 sup_set_class ssel icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 cres wbr icores_1 sup_set_class icores_0 sup_set_class fcores_0 wbr icores_1 sup_set_class fcores_2 wcel icores_1 sup_set_class icores_0 sup_set_class fcores_0 fcores_2 icores_0 vex brres rbaib syl56 pm5.32d exbidv opabbidv icores_2 icores_0 icores_1 fcores_0 fcores_2 cres fcores_1 df-co icores_2 icores_0 icores_1 fcores_0 fcores_1 df-co 3eqtr4g $.
$}
$( Associative law for the restriction of a composition.  (Contributed by
       NM, 12-Dec-2006.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	iresco_0 $f set x $.
	iresco_1 $f set y $.
	iresco_2 $f set z $.
	fresco_0 $f class A $.
	fresco_1 $f class B $.
	fresco_2 $f class C $.
	resco $p |- ( ( A o. B ) |` C ) = ( A o. ( B |` C ) ) $= iresco_0 iresco_1 fresco_0 fresco_1 ccom fresco_2 cres fresco_0 fresco_1 fresco_2 cres ccom fresco_0 fresco_1 ccom fresco_2 relres fresco_0 fresco_1 fresco_2 cres relco iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 ccom wbr iresco_0 sup_set_class fresco_2 wcel wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 fresco_2 cres wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_2 wex iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 ccom fresco_2 cres wbr iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 fresco_2 cres ccom wbr iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 ccom wbr iresco_0 sup_set_class fresco_2 wcel wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_2 wex iresco_0 sup_set_class fresco_2 wcel wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_0 sup_set_class fresco_2 wcel wa iresco_2 wex iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 fresco_2 cres wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_2 wex iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 ccom wbr iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_2 wex iresco_0 sup_set_class fresco_2 wcel iresco_2 iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 iresco_0 vex iresco_1 vex brco anbi1i iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_0 sup_set_class fresco_2 wcel iresco_2 19.41v iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_0 sup_set_class fresco_2 wcel wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 fresco_2 cres wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_2 iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_0 sup_set_class fresco_2 wcel wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_0 sup_set_class fresco_2 wcel wa iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 fresco_2 cres wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr wa iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr iresco_0 sup_set_class fresco_2 wcel an32 iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 fresco_2 cres wbr iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 wbr iresco_0 sup_set_class fresco_2 wcel wa iresco_2 sup_set_class iresco_1 sup_set_class fresco_0 wbr iresco_0 sup_set_class iresco_2 sup_set_class fresco_1 fresco_2 iresco_2 vex brres anbi1i bitr4i exbii 3bitr2i iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 ccom fresco_2 iresco_1 vex brres iresco_2 iresco_0 sup_set_class iresco_1 sup_set_class fresco_0 fresco_1 fresco_2 cres iresco_0 vex iresco_1 vex brco 3bitr4i eqbrriv $.
$}
$( Image of the composition of two classes.  (Contributed by Jason
       Orendorff, 12-Dec-2006.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z C $.
	iimaco_0 $f set x $.
	iimaco_1 $f set y $.
	iimaco_2 $f set z $.
	fimaco_0 $f class A $.
	fimaco_1 $f class B $.
	fimaco_2 $f class C $.
	imaco $p |- ( ( A o. B ) " C ) = ( A " ( B " C ) ) $= iimaco_0 fimaco_0 fimaco_1 ccom fimaco_2 cima fimaco_0 fimaco_1 fimaco_2 cima cima iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr iimaco_1 fimaco_1 fimaco_2 cima wrex iimaco_1 sup_set_class fimaco_1 fimaco_2 cima wcel iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_0 sup_set_class fimaco_0 fimaco_1 fimaco_2 cima cima wcel iimaco_0 sup_set_class fimaco_0 fimaco_1 ccom fimaco_2 cima wcel iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr iimaco_1 fimaco_1 fimaco_2 cima df-rex iimaco_1 iimaco_0 sup_set_class fimaco_0 fimaco_1 fimaco_2 cima iimaco_0 vex elima iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_2 fimaco_2 wrex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_2 fimaco_2 wrex iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_0 sup_set_class fimaco_0 fimaco_1 ccom fimaco_2 cima wcel iimaco_1 sup_set_class fimaco_1 fimaco_2 cima wcel iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_2 fimaco_2 wrex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_2 fimaco_2 wrex iimaco_1 wex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_2 fimaco_2 wrex iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_2 iimaco_1 fimaco_2 rexcom4 iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_2 fimaco_2 wrex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_2 fimaco_2 wrex iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr iimaco_2 fimaco_2 r19.41v exbii bitri iimaco_0 sup_set_class fimaco_0 fimaco_1 ccom fimaco_2 cima wcel iimaco_2 sup_set_class iimaco_0 sup_set_class fimaco_0 fimaco_1 ccom wbr iimaco_2 fimaco_2 wrex iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_2 fimaco_2 wrex iimaco_2 iimaco_0 sup_set_class fimaco_0 fimaco_1 ccom fimaco_2 iimaco_0 vex elima iimaco_2 sup_set_class iimaco_0 sup_set_class fimaco_0 fimaco_1 ccom wbr iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 wex iimaco_2 fimaco_2 iimaco_1 iimaco_2 sup_set_class iimaco_0 sup_set_class fimaco_0 fimaco_1 iimaco_2 vex iimaco_0 vex brco rexbii bitri iimaco_1 sup_set_class fimaco_1 fimaco_2 cima wcel iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_2 fimaco_2 wrex iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr wa iimaco_1 iimaco_1 sup_set_class fimaco_1 fimaco_2 cima wcel iimaco_2 sup_set_class iimaco_1 sup_set_class fimaco_1 wbr iimaco_2 fimaco_2 wrex iimaco_1 sup_set_class iimaco_0 sup_set_class fimaco_0 wbr iimaco_2 iimaco_1 sup_set_class fimaco_1 fimaco_2 iimaco_1 vex elima anbi1i exbii 3bitr4i 3bitr4ri eqriv $.
$}
$( The range of the composition of two classes.  (Contributed by NM,
       12-Dec-2006.) $)
${
	$d x y z A $.
	$d x y z B $.
	$d x y z $.
	irnco_0 $f set x $.
	irnco_1 $f set y $.
	irnco_2 $f set z $.
	frnco_0 $f class A $.
	frnco_1 $f class B $.
	rnco $p |- ran ( A o. B ) = ran ( A |` ran B ) $= irnco_1 frnco_0 frnco_1 ccom crn frnco_0 frnco_1 crn cres crn irnco_0 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 ccom wbr irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 crn cres wbr irnco_2 wex irnco_1 sup_set_class frnco_0 frnco_1 ccom crn wcel irnco_1 sup_set_class frnco_0 frnco_1 crn cres crn wcel irnco_0 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 ccom wbr irnco_0 wex irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_2 wex irnco_0 wex irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_0 wex irnco_2 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 crn cres wbr irnco_2 wex irnco_0 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 ccom wbr irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_2 wex irnco_0 irnco_2 irnco_0 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 irnco_0 vex irnco_1 vex brco exbii irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_0 irnco_2 excom irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 crn cres wbr irnco_2 irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr irnco_2 sup_set_class frnco_1 crn wcel wa irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 crn cres wbr irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_0 wex wa irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr wa irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr irnco_2 sup_set_class frnco_1 crn wcel wa irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr ancom irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr irnco_0 19.41v irnco_2 sup_set_class frnco_1 crn wcel irnco_0 sup_set_class irnco_2 sup_set_class frnco_1 wbr irnco_0 wex irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 wbr irnco_0 irnco_2 sup_set_class frnco_1 irnco_2 vex elrn anbi2i 3bitr4i irnco_2 sup_set_class irnco_1 sup_set_class frnco_0 frnco_1 crn irnco_1 vex brres bitr4i exbii 3bitri irnco_0 irnco_1 sup_set_class frnco_0 frnco_1 ccom irnco_1 vex elrn irnco_2 irnco_1 sup_set_class frnco_0 frnco_1 crn cres irnco_1 vex elrn 3bitr4i eqriv $.
$}
$( The range of the composition of two classes.  (Contributed by NM,
     27-Mar-2008.) $)
${
	frnco2_0 $f class A $.
	frnco2_1 $f class B $.
	rnco2 $p |- ran ( A o. B ) = ( A " ran B ) $= frnco2_0 frnco2_1 ccom crn frnco2_0 frnco2_1 crn cres crn frnco2_0 frnco2_1 crn cima frnco2_0 frnco2_1 rnco frnco2_0 frnco2_1 crn df-ima eqtr4i $.
$}
$( The domain of a composition.  Exercise 27 of [Enderton] p. 53.
     (Contributed by NM, 4-Feb-2004.) $)
${
	fdmco_0 $f class A $.
	fdmco_1 $f class B $.
	dmco $p |- dom ( A o. B ) = ( `' B " dom A ) $= fdmco_0 fdmco_1 ccom cdm fdmco_0 fdmco_1 ccom ccnv crn fdmco_1 ccnv fdmco_0 ccnv ccom crn fdmco_1 ccnv fdmco_0 cdm cima fdmco_0 fdmco_1 ccom dfdm4 fdmco_0 fdmco_1 ccom ccnv fdmco_1 ccnv fdmco_0 ccnv ccom fdmco_0 fdmco_1 cnvco rneqi fdmco_1 ccnv fdmco_0 ccnv ccom crn fdmco_1 ccnv fdmco_0 ccnv crn cima fdmco_1 ccnv fdmco_0 cdm cima fdmco_1 ccnv fdmco_0 ccnv rnco2 fdmco_0 cdm fdmco_0 ccnv crn fdmco_1 ccnv fdmco_0 dfdm4 imaeq2i eqtr4i 3eqtri $.
$}
$( Composition with an indexed union.  (Contributed by NM, 21-Dec-2008.) $)
${
	$d w x y z A $.
	$d w y z B $.
	$d w y z C $.
	icoiun_0 $f set y $.
	icoiun_1 $f set z $.
	icoiun_2 $f set w $.
	fcoiun_0 $f set x $.
	fcoiun_1 $f class A $.
	fcoiun_2 $f class B $.
	fcoiun_3 $f class C $.
	coiun $p |- ( A o. U_ x e. C B ) = U_ x e. C ( A o. B ) $= icoiun_0 icoiun_1 fcoiun_1 fcoiun_0 fcoiun_3 fcoiun_2 ciun ccom fcoiun_0 fcoiun_3 fcoiun_1 fcoiun_2 ccom ciun fcoiun_1 fcoiun_0 fcoiun_3 fcoiun_2 ciun relco fcoiun_0 fcoiun_3 fcoiun_1 fcoiun_2 ccom ciun wrel fcoiun_1 fcoiun_2 ccom wrel fcoiun_0 fcoiun_3 fcoiun_0 fcoiun_3 fcoiun_1 fcoiun_2 ccom reliun fcoiun_1 fcoiun_2 ccom wrel fcoiun_0 sup_set_class fcoiun_3 wcel fcoiun_1 fcoiun_2 relco a1i mprgbir icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_2 wex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_2 wex fcoiun_0 fcoiun_3 wrex icoiun_0 sup_set_class icoiun_1 sup_set_class cop fcoiun_1 fcoiun_0 fcoiun_3 fcoiun_2 ciun ccom wcel icoiun_0 sup_set_class icoiun_1 sup_set_class cop fcoiun_0 fcoiun_3 fcoiun_1 fcoiun_2 ccom ciun wcel icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_2 wex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa fcoiun_0 fcoiun_3 wrex icoiun_2 wex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_2 wex fcoiun_0 fcoiun_3 wrex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa fcoiun_0 fcoiun_3 wrex icoiun_2 icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr fcoiun_0 fcoiun_3 wrex icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa fcoiun_0 fcoiun_3 wrex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun wbr icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr fcoiun_0 fcoiun_3 wrex icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr icoiun_0 sup_set_class icoiun_2 sup_set_class cop fcoiun_0 fcoiun_3 fcoiun_2 ciun wcel icoiun_0 sup_set_class icoiun_2 sup_set_class cop fcoiun_2 wcel fcoiun_0 fcoiun_3 wrex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun wbr icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr fcoiun_0 fcoiun_3 wrex fcoiun_0 icoiun_0 sup_set_class icoiun_2 sup_set_class cop fcoiun_3 fcoiun_2 eliun icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_0 fcoiun_3 fcoiun_2 ciun df-br icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_0 sup_set_class icoiun_2 sup_set_class cop fcoiun_2 wcel fcoiun_0 fcoiun_3 icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 df-br rexbii 3bitr4i anbi1i icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr fcoiun_0 fcoiun_3 r19.41v bitr4i exbii icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa fcoiun_0 icoiun_2 fcoiun_3 rexcom4 bitr4i icoiun_2 icoiun_0 sup_set_class icoiun_1 sup_set_class fcoiun_1 fcoiun_0 fcoiun_3 fcoiun_2 ciun icoiun_0 vex icoiun_1 vex opelco icoiun_0 sup_set_class icoiun_1 sup_set_class cop fcoiun_0 fcoiun_3 fcoiun_1 fcoiun_2 ccom ciun wcel icoiun_0 sup_set_class icoiun_1 sup_set_class cop fcoiun_1 fcoiun_2 ccom wcel fcoiun_0 fcoiun_3 wrex icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_2 wex fcoiun_0 fcoiun_3 wrex fcoiun_0 icoiun_0 sup_set_class icoiun_1 sup_set_class cop fcoiun_3 fcoiun_1 fcoiun_2 ccom eliun icoiun_0 sup_set_class icoiun_1 sup_set_class cop fcoiun_1 fcoiun_2 ccom wcel icoiun_0 sup_set_class icoiun_2 sup_set_class fcoiun_2 wbr icoiun_2 sup_set_class icoiun_1 sup_set_class fcoiun_1 wbr wa icoiun_2 wex fcoiun_0 fcoiun_3 icoiun_2 icoiun_0 sup_set_class icoiun_1 sup_set_class fcoiun_1 fcoiun_2 icoiun_0 vex icoiun_1 vex opelco rexbii bitri 3bitr4i eqrelriiv $.
$}
$( A composition is not affected by a double converse of its first argument.
     (Contributed by NM, 8-Oct-2007.) $)
${
	fcocnvcnv1_0 $f class A $.
	fcocnvcnv1_1 $f class B $.
	cocnvcnv1 $p |- ( `' `' A o. B ) = ( A o. B ) $= fcocnvcnv1_0 ccnv ccnv fcocnvcnv1_1 ccom fcocnvcnv1_0 cvv cres fcocnvcnv1_1 ccom fcocnvcnv1_0 fcocnvcnv1_1 ccom fcocnvcnv1_0 ccnv ccnv fcocnvcnv1_0 cvv cres fcocnvcnv1_1 fcocnvcnv1_0 cnvcnv2 coeq1i fcocnvcnv1_1 crn cvv wss fcocnvcnv1_0 cvv cres fcocnvcnv1_1 ccom fcocnvcnv1_0 fcocnvcnv1_1 ccom wceq fcocnvcnv1_1 crn ssv fcocnvcnv1_0 fcocnvcnv1_1 cvv cores ax-mp eqtri $.
$}
$( A composition is not affected by a double converse of its second
     argument.  (Contributed by NM, 8-Oct-2007.) $)
${
	fcocnvcnv2_0 $f class A $.
	fcocnvcnv2_1 $f class B $.
	cocnvcnv2 $p |- ( A o. `' `' B ) = ( A o. B ) $= fcocnvcnv2_0 fcocnvcnv2_1 ccnv ccnv ccom fcocnvcnv2_0 fcocnvcnv2_1 cvv cres ccom fcocnvcnv2_0 fcocnvcnv2_1 ccom cvv cres fcocnvcnv2_0 fcocnvcnv2_1 ccom fcocnvcnv2_1 ccnv ccnv fcocnvcnv2_1 cvv cres fcocnvcnv2_0 fcocnvcnv2_1 cnvcnv2 coeq2i fcocnvcnv2_0 fcocnvcnv2_1 cvv resco fcocnvcnv2_0 fcocnvcnv2_1 ccom wrel fcocnvcnv2_0 fcocnvcnv2_1 ccom cvv cres fcocnvcnv2_0 fcocnvcnv2_1 ccom wceq fcocnvcnv2_0 fcocnvcnv2_1 relco fcocnvcnv2_0 fcocnvcnv2_1 ccom dfrel3 mpbi 3eqtr2i $.
$}
$( Absorption of a reverse (preimage) restriction of the second member of a
     class composition.  (Contributed by NM, 11-Dec-2006.) $)
${
	fcores2_0 $f class A $.
	fcores2_1 $f class B $.
	fcores2_2 $f class C $.
	cores2 $p |- ( dom A C_ C -> ( A o. `' ( `' B |` C ) ) = ( A o. B ) ) $= fcores2_0 cdm fcores2_2 wss fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom ccnv ccnv fcores2_0 fcores2_1 ccom ccnv ccnv fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom fcores2_0 fcores2_1 ccom fcores2_0 cdm fcores2_2 wss fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom ccnv fcores2_0 fcores2_1 ccom ccnv fcores2_0 cdm fcores2_2 wss fcores2_1 ccnv fcores2_2 cres fcores2_0 ccnv ccom fcores2_1 ccnv fcores2_0 ccnv ccom fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom ccnv fcores2_0 fcores2_1 ccom ccnv fcores2_0 cdm fcores2_2 wss fcores2_0 ccnv crn fcores2_2 wss fcores2_1 ccnv fcores2_2 cres fcores2_0 ccnv ccom fcores2_1 ccnv fcores2_0 ccnv ccom wceq fcores2_0 cdm fcores2_0 ccnv crn fcores2_2 fcores2_0 dfdm4 sseq1i fcores2_1 ccnv fcores2_0 ccnv fcores2_2 cores sylbi fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom ccnv fcores2_1 ccnv fcores2_2 cres ccnv ccnv fcores2_0 ccnv ccom fcores2_1 ccnv fcores2_2 cres fcores2_0 ccnv ccom fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv cnvco fcores2_1 ccnv fcores2_2 cres fcores2_0 ccnv cocnvcnv1 eqtri fcores2_0 fcores2_1 cnvco 3eqtr4g cnveqd fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom wrel fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom ccnv ccnv fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom wceq fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv relco fcores2_0 fcores2_1 ccnv fcores2_2 cres ccnv ccom dfrel2 mpbi fcores2_0 fcores2_1 ccom wrel fcores2_0 fcores2_1 ccom ccnv ccnv fcores2_0 fcores2_1 ccom wceq fcores2_0 fcores2_1 relco fcores2_0 fcores2_1 ccom dfrel2 mpbi 3eqtr3g $.
$}
$( Composition with the empty set.  Theorem 20 of [Suppes] p. 63.
       (Contributed by NM, 24-Apr-2004.) $)
${
	$d x y z A $.
	ico02_0 $f set x $.
	ico02_1 $f set y $.
	ico02_2 $f set z $.
	fco02_0 $f class A $.
	co02 $p |- ( A o. (/) ) = (/) $= ico02_0 ico02_1 fco02_0 c0 ccom c0 fco02_0 c0 relco rel0 ico02_0 sup_set_class ico02_1 sup_set_class cop fco02_0 c0 ccom wcel ico02_0 sup_set_class ico02_1 sup_set_class cop c0 wcel ico02_0 sup_set_class ico02_1 sup_set_class cop fco02_0 c0 ccom wcel ico02_0 sup_set_class ico02_2 sup_set_class c0 wbr ico02_2 sup_set_class ico02_1 sup_set_class fco02_0 wbr wa ico02_2 wex ico02_0 sup_set_class ico02_2 sup_set_class c0 wbr ico02_2 sup_set_class ico02_1 sup_set_class fco02_0 wbr wa ico02_2 ico02_0 sup_set_class ico02_2 sup_set_class c0 wbr ico02_2 sup_set_class ico02_1 sup_set_class fco02_0 wbr ico02_0 sup_set_class ico02_2 sup_set_class c0 wbr ico02_0 sup_set_class ico02_2 sup_set_class cop c0 wcel ico02_0 sup_set_class ico02_2 sup_set_class cop noel ico02_0 sup_set_class ico02_2 sup_set_class c0 df-br mtbir intnanr nex ico02_2 ico02_0 sup_set_class ico02_1 sup_set_class fco02_0 c0 ico02_0 vex ico02_1 vex opelco mtbir ico02_0 sup_set_class ico02_1 sup_set_class cop noel 2false eqrelriiv $.
$}
$( Composition with the empty set.  (Contributed by NM, 24-Apr-2004.) $)
${
	fco01_0 $f class A $.
	co01 $p |- ( (/) o. A ) = (/) $= c0 ccnv ccnv c0 fco01_0 ccom ccnv ccnv c0 c0 fco01_0 ccom c0 ccnv c0 fco01_0 ccom ccnv c0 ccnv c0 c0 fco01_0 ccom ccnv cnv0 c0 fco01_0 ccom ccnv fco01_0 ccnv c0 ccnv ccom fco01_0 ccnv c0 ccom c0 c0 fco01_0 cnvco c0 ccnv c0 fco01_0 ccnv cnv0 coeq2i fco01_0 ccnv co02 3eqtri eqtr4i cnveqi c0 wrel c0 ccnv ccnv c0 wceq rel0 c0 dfrel2 mpbi c0 fco01_0 ccom wrel c0 fco01_0 ccom ccnv ccnv c0 fco01_0 ccom wceq c0 fco01_0 relco c0 fco01_0 ccom dfrel2 mpbi 3eqtr3ri $.
$}
$( Composition with the identity relation.  Part of Theorem 3.7(i) of
       [Monk1] p. 36.  (Contributed by NM, 22-Apr-2004.) $)
${
	$d x y z A $.
	icoi1_0 $f set x $.
	icoi1_1 $f set y $.
	icoi1_2 $f set z $.
	fcoi1_0 $f class A $.
	coi1 $p |- ( Rel A -> ( A o. _I ) = A ) $= fcoi1_0 cid ccom wrel fcoi1_0 wrel fcoi1_0 cid ccom fcoi1_0 wceq fcoi1_0 cid relco icoi1_0 icoi1_1 fcoi1_0 cid ccom fcoi1_0 icoi1_0 sup_set_class icoi1_1 sup_set_class cop fcoi1_0 cid ccom wcel icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr icoi1_0 sup_set_class icoi1_1 sup_set_class cop fcoi1_0 wcel icoi1_0 sup_set_class icoi1_1 sup_set_class cop fcoi1_0 cid ccom wcel icoi1_0 sup_set_class icoi1_2 sup_set_class cid wbr icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr wa icoi1_2 wex icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr icoi1_2 icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 cid icoi1_0 vex icoi1_1 vex opelco icoi1_0 sup_set_class icoi1_2 sup_set_class cid wbr icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr wa icoi1_2 wex icoi1_2 sup_set_class icoi1_0 sup_set_class wceq icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr wa icoi1_2 wex icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr icoi1_0 sup_set_class icoi1_2 sup_set_class cid wbr icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr wa icoi1_2 sup_set_class icoi1_0 sup_set_class wceq icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr wa icoi1_2 icoi1_0 sup_set_class icoi1_2 sup_set_class cid wbr icoi1_2 sup_set_class icoi1_0 sup_set_class wceq icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr icoi1_0 sup_set_class icoi1_2 sup_set_class cid wbr icoi1_0 sup_set_class icoi1_2 sup_set_class wceq icoi1_2 sup_set_class icoi1_0 sup_set_class wceq icoi1_0 sup_set_class icoi1_2 sup_set_class icoi1_2 vex ideq icoi1_0 icoi1_2 equcom bitri anbi1i exbii icoi1_2 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 wbr icoi1_2 icoi1_0 sup_set_class icoi1_0 vex icoi1_2 sup_set_class icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 breq1 ceqsexv bitri bitri icoi1_0 sup_set_class icoi1_1 sup_set_class fcoi1_0 df-br bitri eqrelriv mpan $.
$}
$( Composition with the identity relation.  Part of Theorem 3.7(i) of
       [Monk1] p. 36.  (Contributed by NM, 22-Apr-2004.) $)
${
	fcoi2_0 $f class A $.
	coi2 $p |- ( Rel A -> ( _I o. A ) = A ) $= fcoi2_0 wrel cid ccnv fcoi2_0 ccnv ccnv ccom fcoi2_0 ccnv ccnv cid fcoi2_0 ccom fcoi2_0 fcoi2_0 ccnv cid ccom ccnv cid ccnv fcoi2_0 ccnv ccnv ccom fcoi2_0 ccnv ccnv fcoi2_0 ccnv cid cnvco fcoi2_0 ccnv cid ccom fcoi2_0 ccnv fcoi2_0 ccnv wrel fcoi2_0 ccnv cid ccom fcoi2_0 ccnv wceq fcoi2_0 relcnv fcoi2_0 ccnv coi1 ax-mp cnveqi eqtr3i fcoi2_0 wrel fcoi2_0 ccnv ccnv fcoi2_0 wceq cid ccnv fcoi2_0 ccnv ccnv ccom cid fcoi2_0 ccom wceq fcoi2_0 dfrel2 fcoi2_0 ccnv ccnv fcoi2_0 wceq cid ccnv cid wceq cid ccnv fcoi2_0 ccnv ccnv ccom cid fcoi2_0 ccom wceq cnvi fcoi2_0 ccnv ccnv fcoi2_0 wceq cid ccnv cid wceq cid ccnv fcoi2_0 ccnv ccnv ccom cid ccnv fcoi2_0 ccom cid fcoi2_0 ccom fcoi2_0 ccnv ccnv fcoi2_0 cid ccnv coeq2 cid ccnv cid fcoi2_0 coeq1 sylan9eq mpan2 sylbi fcoi2_0 wrel fcoi2_0 ccnv ccnv fcoi2_0 wceq fcoi2_0 dfrel2 biimpi 3eqtr3a $.
$}
$( Composition with a restricted identity relation.  (Contributed by FL,
     19-Jun-2011.)  (Revised by Stefan O'Rear, 7-Mar-2015.) $)
${
	fcoires1_0 $f class A $.
	fcoires1_1 $f class B $.
	coires1 $p |- ( A o. ( _I |` B ) ) = ( A |` B ) $= fcoires1_0 ccnv ccnv fcoires1_1 cres fcoires1_0 cid fcoires1_1 cres ccom fcoires1_0 fcoires1_1 cres fcoires1_0 cid ccom fcoires1_1 cres fcoires1_0 ccnv ccnv fcoires1_1 cres fcoires1_0 cid fcoires1_1 cres ccom fcoires1_0 cid ccom fcoires1_0 ccnv ccnv fcoires1_1 fcoires1_0 ccnv ccnv cid ccom fcoires1_0 cid ccom fcoires1_0 ccnv ccnv fcoires1_0 cid cocnvcnv1 fcoires1_0 ccnv ccnv wrel fcoires1_0 ccnv ccnv cid ccom fcoires1_0 ccnv ccnv wceq fcoires1_0 ccnv relcnv fcoires1_0 ccnv ccnv coi1 ax-mp eqtr3i reseq1i fcoires1_0 cid fcoires1_1 resco eqtr3i fcoires1_0 fcoires1_1 rescnvcnv eqtr3i $.
$}
$( Associative law for class composition.  Theorem 27 of [Suppes] p. 64.
       Also Exercise 21 of [Enderton] p. 53.  Interestingly, this law holds for
       any classes whatsoever, not just functions or even relations.
       (Contributed by NM, 27-Jan-1997.) $)
${
	$d x y z w A $.
	$d x y z w B $.
	$d x y z w C $.
	icoass_0 $f set x $.
	icoass_1 $f set y $.
	icoass_2 $f set z $.
	icoass_3 $f set w $.
	fcoass_0 $f class A $.
	fcoass_1 $f class B $.
	fcoass_2 $f class C $.
	coass $p |- ( ( A o. B ) o. C ) = ( A o. ( B o. C ) ) $= icoass_0 icoass_1 fcoass_0 fcoass_1 ccom fcoass_2 ccom fcoass_0 fcoass_1 fcoass_2 ccom ccom fcoass_0 fcoass_1 ccom fcoass_2 relco fcoass_0 fcoass_1 fcoass_2 ccom relco icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa wa icoass_3 wex icoass_2 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_2 wex icoass_3 wex icoass_0 sup_set_class icoass_1 sup_set_class cop fcoass_0 fcoass_1 ccom fcoass_2 ccom wcel icoass_0 sup_set_class icoass_1 sup_set_class cop fcoass_0 fcoass_1 fcoass_2 ccom ccom wcel icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa wa icoass_3 wex icoass_2 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa wa icoass_2 wex icoass_3 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_2 wex icoass_3 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa wa icoass_2 icoass_3 excom icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa wa icoass_3 icoass_2 icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr anass 2exbii bitr4i icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_1 sup_set_class fcoass_0 fcoass_1 ccom wbr wa icoass_2 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 wex wa icoass_2 wex icoass_0 sup_set_class icoass_1 sup_set_class cop fcoass_0 fcoass_1 ccom fcoass_2 ccom wcel icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa wa icoass_3 wex icoass_2 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_1 sup_set_class fcoass_0 fcoass_1 ccom wbr wa icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 wex wa icoass_2 icoass_2 sup_set_class icoass_1 sup_set_class fcoass_0 fcoass_1 ccom wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_3 icoass_2 sup_set_class icoass_1 sup_set_class fcoass_0 fcoass_1 icoass_2 vex icoass_1 vex brco anbi2i exbii icoass_2 icoass_0 sup_set_class icoass_1 sup_set_class fcoass_0 fcoass_1 ccom fcoass_2 icoass_0 vex icoass_1 vex opelco icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_2 icoass_3 exdistr 3bitr4i icoass_0 sup_set_class icoass_3 sup_set_class fcoass_1 fcoass_2 ccom wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_2 wex icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 wex icoass_0 sup_set_class icoass_1 sup_set_class cop fcoass_0 fcoass_1 fcoass_2 ccom ccom wcel icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_2 wex icoass_3 wex icoass_0 sup_set_class icoass_3 sup_set_class fcoass_1 fcoass_2 ccom wbr icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_2 wex icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 icoass_0 sup_set_class icoass_3 sup_set_class fcoass_1 fcoass_2 ccom wbr icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_2 wex icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr icoass_2 icoass_0 sup_set_class icoass_3 sup_set_class fcoass_1 fcoass_2 icoass_0 vex icoass_3 vex brco anbi1i exbii icoass_3 icoass_0 sup_set_class icoass_1 sup_set_class fcoass_0 fcoass_1 fcoass_2 ccom icoass_0 vex icoass_1 vex opelco icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_2 wex icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_2 wex icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr wa icoass_3 icoass_0 sup_set_class icoass_2 sup_set_class fcoass_2 wbr icoass_2 sup_set_class icoass_3 sup_set_class fcoass_1 wbr wa icoass_3 sup_set_class icoass_1 sup_set_class fcoass_0 wbr icoass_2 19.41v exbii 3bitr4i 3bitr4i eqrelriiv $.
$}
$( A relation is transitive iff its converse is transitive.  (Contributed by
     FL, 19-Sep-2011.) $)
${
	frelcnvtr_0 $f class R $.
	relcnvtr $p |- ( Rel R -> ( ( R o. R ) C_ R <-> ( `' R o. `' R ) C_ `' R ) ) $= frelcnvtr_0 wrel frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom frelcnvtr_0 ccnv wss frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom frelcnvtr_0 frelcnvtr_0 ccom ccnv frelcnvtr_0 ccnv frelcnvtr_0 frelcnvtr_0 cnvco frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 cnvss syl5eqssr frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom frelcnvtr_0 ccnv wss frelcnvtr_0 wrel frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom ccnv frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom wceq frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom frelcnvtr_0 ccnv wss frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom ccnv frelcnvtr_0 ccnv ccnv wss frelcnvtr_0 wrel frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss wi frelcnvtr_0 ccnv frelcnvtr_0 ccnv cnvco frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom frelcnvtr_0 ccnv cnvss frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom ccnv frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom wceq frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom ccnv frelcnvtr_0 ccnv ccnv wss frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 ccnv ccnv wss frelcnvtr_0 wrel frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss wi frelcnvtr_0 ccnv frelcnvtr_0 ccnv ccom ccnv frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 ccnv ccnv sseq1 frelcnvtr_0 wrel frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 ccnv ccnv wss frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss frelcnvtr_0 wrel frelcnvtr_0 ccnv ccnv frelcnvtr_0 wceq frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 ccnv ccnv wss frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss wi frelcnvtr_0 dfrel2 frelcnvtr_0 ccnv ccnv frelcnvtr_0 wceq frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 ccnv ccnv wss frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 wss frelcnvtr_0 ccnv ccnv frelcnvtr_0 wceq frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 ccnv ccnv frelcnvtr_0 frelcnvtr_0 ccnv ccnv frelcnvtr_0 wceq frelcnvtr_0 ccnv ccnv frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 frelcnvtr_0 ccnv ccnv ccom frelcnvtr_0 frelcnvtr_0 ccom frelcnvtr_0 ccnv ccnv frelcnvtr_0 frelcnvtr_0 ccnv ccnv coeq1 frelcnvtr_0 ccnv ccnv frelcnvtr_0 frelcnvtr_0 coeq2 eqtrd frelcnvtr_0 ccnv ccnv frelcnvtr_0 wceq id sseq12d biimpd sylbi com12 syl6bi mpsyl com12 impbid2 $.
$}
$( A relation is included in the cross product of its domain and range.
       Exercise 4.12(t) of [Mendelson] p. 235.  (Contributed by NM,
       3-Aug-1994.) $)
${
	$d x y A $.
	irelssdmrn_0 $f set x $.
	irelssdmrn_1 $f set y $.
	frelssdmrn_0 $f class A $.
	relssdmrn $p |- ( Rel A -> A C_ ( dom A X. ran A ) ) $= frelssdmrn_0 wrel irelssdmrn_0 irelssdmrn_1 frelssdmrn_0 frelssdmrn_0 cdm frelssdmrn_0 crn cxp frelssdmrn_0 wrel id irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 cdm frelssdmrn_0 crn cxp wcel wi frelssdmrn_0 wrel irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_1 wex irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_0 wex irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 cdm frelssdmrn_0 crn cxp wcel irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_1 19.8a irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_0 19.8a irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 cdm frelssdmrn_0 crn cxp wcel irelssdmrn_0 sup_set_class frelssdmrn_0 cdm wcel irelssdmrn_1 sup_set_class frelssdmrn_0 crn wcel wa irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_1 wex irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_0 wex wa irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class frelssdmrn_0 cdm frelssdmrn_0 crn opelxp irelssdmrn_0 sup_set_class frelssdmrn_0 cdm wcel irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_1 wex irelssdmrn_1 sup_set_class frelssdmrn_0 crn wcel irelssdmrn_0 sup_set_class irelssdmrn_1 sup_set_class cop frelssdmrn_0 wcel irelssdmrn_0 wex irelssdmrn_1 irelssdmrn_0 sup_set_class frelssdmrn_0 irelssdmrn_0 vex eldm2 irelssdmrn_0 irelssdmrn_1 sup_set_class frelssdmrn_0 irelssdmrn_1 vex elrn2 anbi12i bitri sylanbrc a1i relssdv $.
$}
$( The converse is a subset of the cartesian product of range and domain.
     (Contributed by Mario Carneiro, 2-Jan-2017.) $)
${
	fcnvssrndm_0 $f class A $.
	cnvssrndm $p |- `' A C_ ( ran A X. dom A ) $= fcnvssrndm_0 ccnv fcnvssrndm_0 ccnv cdm fcnvssrndm_0 ccnv crn cxp fcnvssrndm_0 crn fcnvssrndm_0 cdm cxp fcnvssrndm_0 ccnv wrel fcnvssrndm_0 ccnv fcnvssrndm_0 ccnv cdm fcnvssrndm_0 ccnv crn cxp wss fcnvssrndm_0 relcnv fcnvssrndm_0 ccnv relssdmrn ax-mp fcnvssrndm_0 crn fcnvssrndm_0 ccnv cdm fcnvssrndm_0 cdm fcnvssrndm_0 ccnv crn fcnvssrndm_0 df-rn fcnvssrndm_0 dfdm4 xpeq12i sseqtr4i $.
$}
$( Composition as a subset of the cross product of factors.  (Contributed by
     Mario Carneiro, 12-Jan-2017.) $)
${
	fcossxp_0 $f class A $.
	fcossxp_1 $f class B $.
	cossxp $p |- ( A o. B ) C_ ( dom B X. ran A ) $= fcossxp_0 fcossxp_1 ccom fcossxp_0 fcossxp_1 ccom cdm fcossxp_0 fcossxp_1 ccom crn cxp fcossxp_1 cdm fcossxp_0 crn cxp fcossxp_0 fcossxp_1 ccom wrel fcossxp_0 fcossxp_1 ccom fcossxp_0 fcossxp_1 ccom cdm fcossxp_0 fcossxp_1 ccom crn cxp wss fcossxp_0 fcossxp_1 relco fcossxp_0 fcossxp_1 ccom relssdmrn ax-mp fcossxp_0 fcossxp_1 ccom cdm fcossxp_1 cdm wss fcossxp_0 fcossxp_1 ccom crn fcossxp_0 crn wss fcossxp_0 fcossxp_1 ccom cdm fcossxp_0 fcossxp_1 ccom crn cxp fcossxp_1 cdm fcossxp_0 crn cxp wss fcossxp_0 fcossxp_1 dmcoss fcossxp_0 fcossxp_1 rncoss fcossxp_0 fcossxp_1 ccom cdm fcossxp_1 cdm fcossxp_0 fcossxp_1 ccom crn fcossxp_0 crn xpss12 mp2an sstri $.
$}
$( Two ways to describe the structure of a two-place operation.  (Contributed
     by NM, 17-Dec-2008.) $)
${
	frelrelss_0 $f class A $.
	relrelss $p |- ( ( Rel A /\ Rel dom A ) <-> A C_ ( ( _V X. _V ) X. _V ) ) $= frelrelss_0 wrel frelrelss_0 cdm wrel wa frelrelss_0 wrel frelrelss_0 cdm cvv cvv cxp wss wa frelrelss_0 cvv cvv cxp cvv cxp wss frelrelss_0 cdm wrel frelrelss_0 cdm cvv cvv cxp wss frelrelss_0 wrel frelrelss_0 cdm df-rel anbi2i frelrelss_0 wrel frelrelss_0 cdm cvv cvv cxp wss wa frelrelss_0 cvv cvv cxp cvv cxp wss frelrelss_0 wrel frelrelss_0 cdm cvv cvv cxp wss frelrelss_0 frelrelss_0 cdm frelrelss_0 crn cxp cvv cvv cxp cvv cxp frelrelss_0 relssdmrn frelrelss_0 cdm cvv cvv cxp wss frelrelss_0 crn cvv wss frelrelss_0 cdm frelrelss_0 crn cxp cvv cvv cxp cvv cxp wss frelrelss_0 crn ssv frelrelss_0 cdm cvv cvv cxp frelrelss_0 crn cvv xpss12 mpan2 sylan9ss frelrelss_0 cvv cvv cxp cvv cxp wss frelrelss_0 wrel frelrelss_0 cdm cvv cvv cxp wss frelrelss_0 cvv cvv cxp cvv cxp wss frelrelss_0 cvv cvv cxp wss frelrelss_0 wrel frelrelss_0 cvv cvv cxp cvv cxp wss cvv cvv cxp cvv cxp cvv cvv cxp wss frelrelss_0 cvv cvv cxp wss cvv cvv cxp cvv xpss frelrelss_0 cvv cvv cxp cvv cxp cvv cvv cxp sstr mpan2 frelrelss_0 df-rel sylibr frelrelss_0 cvv cvv cxp cvv cxp wss frelrelss_0 cdm cvv cvv cxp cvv cxp cdm cvv cvv cxp frelrelss_0 cvv cvv cxp cvv cxp dmss cvv c0 wne cvv cvv cxp cvv cxp cdm cvv cvv cxp wceq vn0 cvv cvv cxp cvv dmxp ax-mp syl6sseq jca impbii bitri $.
$}
$( The membership relation for a relation is inherited by class union.
       (Contributed by NM, 17-Sep-2006.) $)
${
	$d x y A $.
	$d x y R $.
	iunielrel_0 $f set x $.
	iunielrel_1 $f set y $.
	funielrel_0 $f class A $.
	funielrel_1 $f class R $.
	unielrel $p |- ( ( Rel R /\ A e. R ) -> U. A e. U. R ) $= funielrel_1 wrel funielrel_0 funielrel_1 wcel wa funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop wceq iunielrel_1 wex iunielrel_0 wex funielrel_0 funielrel_1 wcel funielrel_0 cuni funielrel_1 cuni wcel iunielrel_0 iunielrel_1 funielrel_0 funielrel_1 elrel funielrel_1 wrel funielrel_0 funielrel_1 wcel simpr funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop wceq funielrel_0 funielrel_1 wcel funielrel_0 cuni funielrel_1 cuni wcel wi iunielrel_0 iunielrel_1 funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop wceq iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop funielrel_1 wcel iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop cuni funielrel_1 cuni wcel funielrel_0 funielrel_1 wcel funielrel_0 cuni funielrel_1 cuni wcel iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop funielrel_1 wcel iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop cuni funielrel_1 cuni wcel wi funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop wceq iunielrel_0 sup_set_class iunielrel_1 sup_set_class funielrel_1 iunielrel_0 vex iunielrel_1 vex uniopel a1i funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop funielrel_1 eleq1 funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop wceq funielrel_0 cuni iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop cuni funielrel_1 cuni funielrel_0 iunielrel_0 sup_set_class iunielrel_1 sup_set_class cop unieq eleq1d 3imtr4d exlimivv sylc $.
$}
$( The double union of a relation is its field.  (Contributed by NM,
     17-Sep-2006.) $)
${
	frelfld_0 $f class R $.
	relfld $p |- ( Rel R -> U. U. R = ( dom R u. ran R ) ) $= frelfld_0 wrel frelfld_0 cuni cuni frelfld_0 cdm frelfld_0 crn cun frelfld_0 wrel frelfld_0 cuni cuni frelfld_0 cdm frelfld_0 crn cxp cuni cuni frelfld_0 cdm frelfld_0 crn cun frelfld_0 wrel frelfld_0 frelfld_0 cdm frelfld_0 crn cxp wss frelfld_0 cuni frelfld_0 cdm frelfld_0 crn cxp cuni wss frelfld_0 cuni cuni frelfld_0 cdm frelfld_0 crn cxp cuni cuni wss frelfld_0 relssdmrn frelfld_0 frelfld_0 cdm frelfld_0 crn cxp uniss frelfld_0 cuni frelfld_0 cdm frelfld_0 crn cxp cuni uniss 3syl frelfld_0 cdm frelfld_0 crn unixpss syl6ss frelfld_0 cdm frelfld_0 crn cun frelfld_0 cuni cuni wss frelfld_0 wrel frelfld_0 dmrnssfld a1i eqssd $.
$}
$( Restriction of a relation to its field.  (Contributed by FL,
     15-Apr-2012.) $)
${
	frelresfld_0 $f class R $.
	relresfld $p |- ( Rel R -> ( R |` U. U. R ) = R ) $= frelresfld_0 wrel frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq frelresfld_0 wrel frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm frelresfld_0 crn cun cres wceq frelresfld_0 frelresfld_0 cdm frelresfld_0 crn cun cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 wrel frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq wi frelresfld_0 wrel frelresfld_0 cuni cuni frelresfld_0 cdm frelresfld_0 crn cun frelresfld_0 frelresfld_0 relfld reseq2d frelresfld_0 frelresfld_0 cdm frelresfld_0 crn resundi frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm frelresfld_0 crn cun cres wceq frelresfld_0 frelresfld_0 cdm frelresfld_0 crn cun cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq wa frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 wrel frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm frelresfld_0 crn cun cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun eqtr frelresfld_0 frelresfld_0 crn cres frelresfld_0 wss frelresfld_0 wrel frelresfld_0 frelresfld_0 cdm cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq wi frelresfld_0 frelresfld_0 crn resss frelresfld_0 resdm frelresfld_0 frelresfld_0 crn cres frelresfld_0 wss frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 wceq frelresfld_0 frelresfld_0 cdm cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq wi wi frelresfld_0 frelresfld_0 crn cres frelresfld_0 ssequn2 frelresfld_0 frelresfld_0 cdm cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cdm cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq wi frelresfld_0 frelresfld_0 cdm cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 cdm cres frelresfld_0 frelresfld_0 frelresfld_0 crn cres uneq1 eqeq2d frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun wceq frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 wceq frelresfld_0 frelresfld_0 cuni cuni cres frelresfld_0 frelresfld_0 frelresfld_0 crn cres cun frelresfld_0 eqtr ex syl6bi com3r sylbi mpsyl syl5com sylancl pm2.43i $.
$}
$( Composition with the identity relation restricted to a relation's field.
     (Contributed by FL, 2-May-2011.) $)
${
	frelcoi2_0 $f class R $.
	relcoi2 $p |- ( Rel R -> ( ( _I |` U. U. R ) o. R ) = R ) $= frelcoi2_0 wrel cid frelcoi2_0 cuni cuni cres frelcoi2_0 ccom cid frelcoi2_0 ccom frelcoi2_0 frelcoi2_0 crn frelcoi2_0 cuni cuni wss cid frelcoi2_0 cuni cuni cres frelcoi2_0 ccom cid frelcoi2_0 ccom wceq frelcoi2_0 wrel frelcoi2_0 cdm frelcoi2_0 crn cun frelcoi2_0 cuni cuni wss frelcoi2_0 crn frelcoi2_0 cuni cuni wss frelcoi2_0 dmrnssfld frelcoi2_0 cdm frelcoi2_0 crn cun frelcoi2_0 cuni cuni wss frelcoi2_0 cdm frelcoi2_0 cuni cuni wss frelcoi2_0 crn frelcoi2_0 cuni cuni wss wa frelcoi2_0 crn frelcoi2_0 cuni cuni wss frelcoi2_0 cdm frelcoi2_0 crn frelcoi2_0 cuni cuni unss frelcoi2_0 cdm frelcoi2_0 cuni cuni wss frelcoi2_0 crn frelcoi2_0 cuni cuni wss simpr sylbir ax-mp cid frelcoi2_0 frelcoi2_0 cuni cuni cores mp1i frelcoi2_0 coi2 eqtrd $.
$}
$( Composition with the identity relation restricted to a relation's field.
     (Contributed by FL, 8-May-2011.) $)
${
	frelcoi1_0 $f class R $.
	relcoi1 $p |- ( Rel R -> ( R o. ( _I |` U. U. R ) ) = R ) $= frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cuni cuni cres ccom frelcoi1_0 cid ccom frelcoi1_0 frelcoi1_0 cuni cuni frelcoi1_0 cdm frelcoi1_0 crn cun wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cuni cuni cres ccom frelcoi1_0 cid ccom wceq frelcoi1_0 relfld frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cuni cuni cres ccom frelcoi1_0 cid ccom wceq frelcoi1_0 cuni cuni frelcoi1_0 cdm frelcoi1_0 crn cun wceq frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid ccom wceq cid frelcoi1_0 cdm frelcoi1_0 crn cun cres cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun wceq frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun ccom wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid ccom wceq wi cid frelcoi1_0 cdm frelcoi1_0 crn resundi cid frelcoi1_0 cdm frelcoi1_0 crn cun cres cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun frelcoi1_0 coeq2 frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid ccom wceq frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun ccom frelcoi1_0 cid ccom wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun ccom frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom frelcoi1_0 cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres coundi frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq frelcoi1_0 cid frelcoi1_0 cdm resco frelcoi1_0 cid ccom frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 coi1 frelcoi1_0 cid ccom frelcoi1_0 wceq frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 frelcoi1_0 cdm cres wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid ccom frelcoi1_0 frelcoi1_0 cdm reseq1 frelcoi1_0 frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 frelcoi1_0 cdm cres wceq frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 resdm frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 frelcoi1_0 cdm cres wceq frelcoi1_0 frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 frelcoi1_0 cdm cres wceq frelcoi1_0 frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 frelcoi1_0 cdm cres wceq frelcoi1_0 frelcoi1_0 cdm cres frelcoi1_0 wceq wa frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 frelcoi1_0 cdm cres frelcoi1_0 eqtr frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom wceq frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid ccom frelcoi1_0 cdm cres wceq frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid ccom frelcoi1_0 cdm cres wceq frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 wceq wa frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid ccom frelcoi1_0 cdm cres frelcoi1_0 eqtr frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 cid frelcoi1_0 crn cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid frelcoi1_0 crn resco frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom uneq1 frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 cid frelcoi1_0 crn cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq frelcoi1_0 cid ccom frelcoi1_0 wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 cid frelcoi1_0 crn cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 coi1 frelcoi1_0 cid ccom frelcoi1_0 wceq frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 cid frelcoi1_0 crn cres ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi wi frelcoi1_0 cid ccom frelcoi1_0 frelcoi1_0 crn reseq1 frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 cid frelcoi1_0 crn cres ccom wceq frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi wi frelcoi1_0 cid frelcoi1_0 crn cres ccom frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 cid frelcoi1_0 crn cres ccom frelcoi1_0 cid ccom frelcoi1_0 crn cres wceq frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 cid frelcoi1_0 crn cres ccom frelcoi1_0 cid ccom frelcoi1_0 crn cres wceq frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres wceq wa frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi wi frelcoi1_0 cid frelcoi1_0 crn cres ccom frelcoi1_0 cid ccom frelcoi1_0 crn cres wceq frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres wceq wa frelcoi1_0 cid frelcoi1_0 crn cres ccom frelcoi1_0 frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom frelcoi1_0 cid ccom frelcoi1_0 crn cres frelcoi1_0 frelcoi1_0 crn cres eqtr uneq2d frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun wceq frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun wceq wa frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun wceq frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq wi frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun eqtr frelcoi1_0 wrel frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 cid ccom wceq frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun wceq frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun frelcoi1_0 cid ccom wceq frelcoi1_0 wrel frelcoi1_0 cid ccom frelcoi1_0 frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun frelcoi1_0 coi1 frelcoi1_0 frelcoi1_0 crn cres frelcoi1_0 wss frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun frelcoi1_0 wceq frelcoi1_0 frelcoi1_0 crn resss frelcoi1_0 frelcoi1_0 crn cres frelcoi1_0 ssequn2 mpbi syl6reqr frelcoi1_0 cid frelcoi1_0 cdm cres ccom frelcoi1_0 cid frelcoi1_0 crn cres ccom cun frelcoi1_0 frelcoi1_0 frelcoi1_0 crn cres cun frelcoi1_0 cid ccom eqeq1 syl5ibr syl ex com3l syl ex eqcoms com3l syl mpcom com3l mpsyl syl ex eqcoms com3l syl ex com3l mpcom syl5com mpcom mpi syl5eq frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid frelcoi1_0 cdm cres cid frelcoi1_0 crn cres cun ccom frelcoi1_0 cid ccom eqeq1 syl5ibr mp2b frelcoi1_0 cuni cuni frelcoi1_0 cdm frelcoi1_0 crn cun wceq frelcoi1_0 cid frelcoi1_0 cuni cuni cres ccom frelcoi1_0 cid frelcoi1_0 cdm frelcoi1_0 crn cun cres ccom frelcoi1_0 cid ccom frelcoi1_0 cuni cuni frelcoi1_0 cdm frelcoi1_0 crn cun wceq cid frelcoi1_0 cuni cuni cres cid frelcoi1_0 cdm frelcoi1_0 crn cun cres frelcoi1_0 frelcoi1_0 cuni cuni frelcoi1_0 cdm frelcoi1_0 crn cun cid reseq2 coeq2d eqeq1d syl5ibr mpcom frelcoi1_0 coi1 eqtrd $.
$}
$( The double union of the converse of a class is its field.  (Contributed by
     NM, 4-Jun-2008.) $)
${
	funidmrn_0 $f class A $.
	unidmrn $p |- U. U. `' A = ( dom A u. ran A ) $= funidmrn_0 ccnv cuni cuni funidmrn_0 ccnv crn funidmrn_0 ccnv cdm cun funidmrn_0 cdm funidmrn_0 crn cun funidmrn_0 ccnv cuni cuni funidmrn_0 ccnv cdm funidmrn_0 ccnv crn funidmrn_0 ccnv wrel funidmrn_0 ccnv cuni cuni funidmrn_0 ccnv cdm funidmrn_0 ccnv crn cun wceq funidmrn_0 relcnv funidmrn_0 ccnv relfld ax-mp equncomi funidmrn_0 cdm funidmrn_0 ccnv crn funidmrn_0 crn funidmrn_0 ccnv cdm funidmrn_0 dfdm4 funidmrn_0 df-rn uneq12i eqtr4i $.
$}
$( if ` R ` is a relation, its double union equals the double union of its
     converse.  (Contributed by FL, 5-Jan-2009.) $)
${
	frelcnvfld_0 $f class R $.
	relcnvfld $p |- ( Rel R -> U. U. R = U. U. `' R ) $= frelcnvfld_0 wrel frelcnvfld_0 cuni cuni frelcnvfld_0 cdm frelcnvfld_0 crn cun frelcnvfld_0 ccnv cuni cuni frelcnvfld_0 relfld frelcnvfld_0 unidmrn syl6eqr $.
$}
$( Alternate definition of domain ~ df-dm that doesn't require dummy
     variables.  (Contributed by NM, 2-Aug-2010.) $)
${
	fdfdm2_0 $f class A $.
	dfdm2 $p |- dom A = U. U. ( `' A o. A ) $= fdfdm2_0 ccnv fdfdm2_0 ccom cuni cuni fdfdm2_0 ccnv fdfdm2_0 ccom cdm fdfdm2_0 ccnv fdfdm2_0 ccom crn cun fdfdm2_0 cdm fdfdm2_0 cdm cun fdfdm2_0 cdm fdfdm2_0 ccnv fdfdm2_0 ccom ccnv cuni cuni fdfdm2_0 ccnv fdfdm2_0 ccom cuni cuni fdfdm2_0 ccnv fdfdm2_0 ccom cdm fdfdm2_0 ccnv fdfdm2_0 ccom crn cun fdfdm2_0 ccnv fdfdm2_0 ccom ccnv cuni fdfdm2_0 ccnv fdfdm2_0 ccom cuni fdfdm2_0 ccnv fdfdm2_0 ccom ccnv fdfdm2_0 ccnv fdfdm2_0 ccom fdfdm2_0 ccnv fdfdm2_0 ccom ccnv fdfdm2_0 ccnv fdfdm2_0 ccnv ccnv ccom fdfdm2_0 ccnv fdfdm2_0 ccom fdfdm2_0 ccnv fdfdm2_0 cnvco fdfdm2_0 ccnv fdfdm2_0 cocnvcnv2 eqtri unieqi unieqi fdfdm2_0 ccnv fdfdm2_0 ccom unidmrn eqtr3i fdfdm2_0 ccnv fdfdm2_0 ccom cdm fdfdm2_0 cdm fdfdm2_0 ccnv fdfdm2_0 ccom crn fdfdm2_0 cdm fdfdm2_0 ccnv cdm fdfdm2_0 crn wceq fdfdm2_0 ccnv fdfdm2_0 ccom cdm fdfdm2_0 cdm wceq fdfdm2_0 crn fdfdm2_0 ccnv cdm fdfdm2_0 df-rn eqcomi fdfdm2_0 ccnv fdfdm2_0 dmcoeq ax-mp fdfdm2_0 ccnv fdfdm2_0 ccom crn fdfdm2_0 ccnv crn fdfdm2_0 cdm fdfdm2_0 ccnv cdm fdfdm2_0 crn wceq fdfdm2_0 ccnv fdfdm2_0 ccom crn fdfdm2_0 ccnv crn wceq fdfdm2_0 crn fdfdm2_0 ccnv cdm fdfdm2_0 df-rn eqcomi fdfdm2_0 ccnv fdfdm2_0 rncoeq ax-mp fdfdm2_0 dfdm4 eqtr4i uneq12i fdfdm2_0 cdm unidm 3eqtrri $.
$}
$( The double class union of a non-empty cross product is the union of it
     members.  (Contributed by NM, 17-Sep-2006.) $)
${
	funixp_0 $f class A $.
	funixp_1 $f class B $.
	unixp $p |- ( ( A X. B ) =/= (/) -> U. U. ( A X. B ) = ( A u. B ) ) $= funixp_0 funixp_1 cxp c0 wne funixp_0 funixp_1 cxp cuni cuni funixp_0 funixp_1 cxp cdm funixp_0 funixp_1 cxp crn cun funixp_0 funixp_1 cun funixp_0 funixp_1 cxp wrel funixp_0 funixp_1 cxp cuni cuni funixp_0 funixp_1 cxp cdm funixp_0 funixp_1 cxp crn cun wceq funixp_0 funixp_1 relxp funixp_0 funixp_1 cxp relfld ax-mp funixp_0 funixp_1 cxp c0 wne funixp_1 c0 wne funixp_0 c0 wne funixp_0 funixp_1 cxp cdm funixp_0 funixp_1 cxp crn cun funixp_0 funixp_1 cun wceq funixp_1 c0 funixp_0 funixp_1 cxp c0 funixp_1 c0 wceq funixp_0 funixp_1 cxp funixp_0 c0 cxp c0 funixp_1 c0 funixp_0 xpeq2 funixp_0 xp0 syl6eq necon3i funixp_0 c0 funixp_0 funixp_1 cxp c0 funixp_0 c0 wceq funixp_0 funixp_1 cxp c0 funixp_1 cxp c0 funixp_0 c0 funixp_1 xpeq1 funixp_1 xp0r syl6eq necon3i funixp_1 c0 wne funixp_0 funixp_1 cxp cdm funixp_0 wceq funixp_0 funixp_1 cxp crn funixp_1 wceq funixp_0 funixp_1 cxp cdm funixp_0 funixp_1 cxp crn cun funixp_0 funixp_1 cun wceq funixp_0 c0 wne funixp_0 funixp_1 dmxp funixp_0 funixp_1 rnxp funixp_0 funixp_1 cxp cdm funixp_0 funixp_0 funixp_1 cxp crn funixp_1 uneq12 syl2an syl2anc syl5eq $.
$}
$( A cross product is empty iff its union is empty.  (Contributed by NM,
       20-Sep-2006.) $)
${
	$d x y z A $.
	$d x y z B $.
	iunixp0_0 $f set x $.
	iunixp0_1 $f set y $.
	iunixp0_2 $f set z $.
	funixp0_0 $f class A $.
	funixp0_1 $f class B $.
	unixp0 $p |- ( ( A X. B ) = (/) <-> U. ( A X. B ) = (/) ) $= funixp0_0 funixp0_1 cxp c0 wceq funixp0_0 funixp0_1 cxp cuni c0 wceq funixp0_0 funixp0_1 cxp c0 wceq funixp0_0 funixp0_1 cxp cuni c0 cuni c0 funixp0_0 funixp0_1 cxp c0 unieq uni0 syl6eq funixp0_0 funixp0_1 cxp c0 funixp0_0 funixp0_1 cxp cuni c0 funixp0_0 funixp0_1 cxp c0 wne iunixp0_2 sup_set_class funixp0_0 funixp0_1 cxp wcel iunixp0_2 wex funixp0_0 funixp0_1 cxp cuni c0 wne iunixp0_2 funixp0_0 funixp0_1 cxp n0 iunixp0_2 sup_set_class funixp0_0 funixp0_1 cxp wcel funixp0_0 funixp0_1 cxp cuni c0 wne iunixp0_2 iunixp0_2 sup_set_class funixp0_0 funixp0_1 cxp wcel iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop iunixp0_2 sup_set_class wceq iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp wcel wa iunixp0_1 wex iunixp0_0 wex funixp0_0 funixp0_1 cxp cuni c0 wne iunixp0_0 iunixp0_1 iunixp0_2 sup_set_class funixp0_0 funixp0_1 elxp3 iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop iunixp0_2 sup_set_class wceq iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp wcel wa funixp0_0 funixp0_1 cxp cuni c0 wne iunixp0_0 iunixp0_1 iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp wcel funixp0_0 funixp0_1 cxp cuni c0 wne iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop iunixp0_2 sup_set_class wceq iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp wcel iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp cuni wss iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop c0 wne funixp0_0 funixp0_1 cxp cuni c0 wne iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp elssuni iunixp0_0 sup_set_class iunixp0_1 sup_set_class iunixp0_0 vex iunixp0_1 vex opnzi iunixp0_0 sup_set_class iunixp0_1 sup_set_class cop funixp0_0 funixp0_1 cxp cuni ssn0 sylancl adantl exlimivv sylbi exlimiv sylbi necon4i impbii $.
$}
$( Field of a square cross product.  (Contributed by FL, 10-Oct-2009.) $)
${
	funixpid_0 $f class A $.
	unixpid $p |- U. U. ( A X. A ) = A $= funixpid_0 c0 wceq funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq funixpid_0 funixpid_0 cxp c0 wceq funixpid_0 c0 wceq funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq funixpid_0 c0 wceq funixpid_0 funixpid_0 cxp c0 funixpid_0 cxp c0 funixpid_0 c0 funixpid_0 xpeq1 funixpid_0 xp0r syl6eq funixpid_0 funixpid_0 cxp c0 wceq funixpid_0 funixpid_0 cxp cuni cuni c0 cuni cuni wceq c0 cuni cuni c0 wceq funixpid_0 c0 wceq funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq wi funixpid_0 funixpid_0 cxp c0 wceq funixpid_0 funixpid_0 cxp cuni c0 cuni funixpid_0 funixpid_0 cxp c0 unieq unieqd c0 cuni cuni c0 cuni c0 c0 cuni c0 uni0 unieqi uni0 eqtri funixpid_0 funixpid_0 cxp cuni cuni c0 cuni cuni wceq c0 cuni cuni c0 wceq wa funixpid_0 funixpid_0 cxp cuni cuni c0 wceq funixpid_0 c0 wceq funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq funixpid_0 funixpid_0 cxp cuni cuni c0 cuni cuni c0 eqtr funixpid_0 funixpid_0 cxp cuni cuni c0 wceq funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq wi c0 funixpid_0 funixpid_0 funixpid_0 cxp cuni cuni c0 wceq c0 funixpid_0 wceq funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq funixpid_0 funixpid_0 cxp cuni cuni c0 funixpid_0 eqtr expcom eqcoms syl5com sylancl mpcom funixpid_0 c0 wceq wn funixpid_0 c0 wne funixpid_0 c0 wne funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq funixpid_0 c0 df-ne funixpid_0 c0 df-ne funixpid_0 c0 wne funixpid_0 c0 wne wa funixpid_0 funixpid_0 cxp c0 wne funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 wceq funixpid_0 funixpid_0 xpnz funixpid_0 funixpid_0 cxp c0 wne funixpid_0 funixpid_0 cxp cuni cuni funixpid_0 funixpid_0 cun funixpid_0 funixpid_0 funixpid_0 unixp funixpid_0 unidm syl6eq sylbi sylancbr pm2.61i $.
$}
$( The converse of a set is a set.  Corollary 6.8(1) of [TakeutiZaring]
     p. 26.  (Contributed by NM, 17-Mar-1998.) $)
${
	fcnvexg_0 $f class A $.
	fcnvexg_1 $f class V $.
	cnvexg $p |- ( A e. V -> `' A e. _V ) $= fcnvexg_0 fcnvexg_1 wcel fcnvexg_0 ccnv fcnvexg_0 ccnv cdm fcnvexg_0 ccnv crn cxp wss fcnvexg_0 ccnv cdm fcnvexg_0 ccnv crn cxp cvv wcel fcnvexg_0 ccnv cvv wcel fcnvexg_0 ccnv wrel fcnvexg_0 ccnv fcnvexg_0 ccnv cdm fcnvexg_0 ccnv crn cxp wss fcnvexg_0 relcnv fcnvexg_0 ccnv relssdmrn ax-mp fcnvexg_0 fcnvexg_1 wcel fcnvexg_0 ccnv cdm cvv wcel fcnvexg_0 ccnv crn cvv wcel fcnvexg_0 ccnv cdm fcnvexg_0 ccnv crn cxp cvv wcel fcnvexg_0 fcnvexg_1 wcel fcnvexg_0 ccnv cdm fcnvexg_0 crn cvv fcnvexg_0 df-rn fcnvexg_0 fcnvexg_1 rnexg syl5eqelr fcnvexg_0 fcnvexg_1 wcel fcnvexg_0 ccnv crn fcnvexg_0 cdm cvv fcnvexg_0 dfdm4 fcnvexg_0 fcnvexg_1 dmexg syl5eqelr fcnvexg_0 ccnv cdm fcnvexg_0 ccnv crn cvv cvv xpexg syl2anc fcnvexg_0 ccnv fcnvexg_0 ccnv cdm fcnvexg_0 ccnv crn cxp cvv ssexg sylancr $.
$}
$( The converse of a set is a set.  Corollary 6.8(1) of [TakeutiZaring]
       p. 26.  (Contributed by NM, 19-Dec-2003.) $)
${
	fcnvex_0 $f class A $.
	ecnvex_0 $e |- A e. _V $.
	cnvex $p |- `' A e. _V $= fcnvex_0 cvv wcel fcnvex_0 ccnv cvv wcel ecnvex_0 fcnvex_0 cvv cnvexg ax-mp $.
$}
$( A relation is a set iff its converse is a set.  (Contributed by FL,
     3-Mar-2007.) $)
${
	frelcnvexb_0 $f class R $.
	relcnvexb $p |- ( Rel R -> ( R e. _V <-> `' R e. _V ) ) $= frelcnvexb_0 wrel frelcnvexb_0 cvv wcel frelcnvexb_0 ccnv cvv wcel frelcnvexb_0 cvv cnvexg frelcnvexb_0 wrel frelcnvexb_0 ccnv ccnv frelcnvexb_0 wceq frelcnvexb_0 ccnv cvv wcel frelcnvexb_0 cvv wcel wi frelcnvexb_0 dfrel2 frelcnvexb_0 ccnv cvv wcel frelcnvexb_0 ccnv ccnv cvv wcel frelcnvexb_0 ccnv ccnv frelcnvexb_0 wceq frelcnvexb_0 cvv wcel frelcnvexb_0 ccnv cvv cnvexg frelcnvexb_0 ccnv ccnv frelcnvexb_0 cvv eleq1 syl5ib sylbi impbid2 $.
$}
$( Restriction of a class to a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.) $)
${
	$d x y A $.
	$d x y B $.
	iressn_0 $f set x $.
	iressn_1 $f set y $.
	fressn_0 $f class A $.
	fressn_1 $f class B $.
	ressn $p |- ( A |` { B } ) = ( { B } X. ( A " { B } ) ) $= iressn_0 iressn_1 fressn_0 fressn_1 csn cres fressn_1 csn fressn_0 fressn_1 csn cima cxp fressn_0 fressn_1 csn relres fressn_1 csn fressn_0 fressn_1 csn cima relxp iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 wcel iressn_0 sup_set_class fressn_1 csn wcel wa iressn_0 sup_set_class fressn_1 csn wcel iressn_1 sup_set_class fressn_0 fressn_1 csn cima wcel wa iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 fressn_1 csn cres wcel iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_1 csn fressn_0 fressn_1 csn cima cxp wcel iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 wcel iressn_0 sup_set_class fressn_1 csn wcel wa iressn_0 sup_set_class fressn_1 csn wcel iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 wcel wa iressn_0 sup_set_class fressn_1 csn wcel iressn_1 sup_set_class fressn_0 fressn_1 csn cima wcel wa iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 wcel iressn_0 sup_set_class fressn_1 csn wcel ancom iressn_0 sup_set_class fressn_1 csn wcel iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 wcel iressn_1 sup_set_class fressn_0 fressn_1 csn cima wcel iressn_0 sup_set_class iressn_1 sup_set_class cop fressn_0 wcel iressn_1 sup_set_class fressn_0 iressn_0 sup_set_class csn cima wcel iressn_0 sup_set_class fressn_1 csn wcel iressn_1 sup_set_class fressn_0 fressn_1 csn cima wcel fressn_0 iressn_0 sup_set_class iressn_1 sup_set_class iressn_0 vex iressn_1 vex elimasn iressn_0 sup_set_class fressn_1 csn wcel fressn_0 iressn_0 sup_set_class csn cima fressn_0 fressn_1 csn cima iressn_1 sup_set_class iressn_0 sup_set_class fressn_1 csn wcel iressn_0 sup_set_class csn fressn_1 csn fressn_0 iressn_0 sup_set_class fressn_1 csn wcel iressn_0 sup_set_class fressn_1 iressn_0 sup_set_class fressn_1 elsni sneqd imaeq2d eleq2d syl5bbr pm5.32i bitri iressn_0 sup_set_class iressn_1 sup_set_class fressn_0 fressn_1 csn iressn_1 vex opelres iressn_0 sup_set_class iressn_1 sup_set_class fressn_1 csn fressn_0 fressn_1 csn cima opelxp 3bitr4i eqrelriiv $.
$}
$( The converse of an intersection is the intersection of the converse.
       (Contributed by FL, 15-Oct-2012.) $)
${
	$d A a b x $.
	$d B a b $.
	icnviin_0 $f set a $.
	icnviin_1 $f set b $.
	fcnviin_0 $f set x $.
	fcnviin_1 $f class A $.
	fcnviin_2 $f class B $.
	cnviin $p |- ( A =/= (/) -> `' |^|_ x e. A B = |^|_ x e. A `' B ) $= fcnviin_1 c0 wne fcnviin_0 fcnviin_1 fcnviin_2 ciin ccnv wrel fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin wrel fcnviin_0 fcnviin_1 fcnviin_2 ciin ccnv fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin wceq fcnviin_0 fcnviin_1 fcnviin_2 ciin relcnv fcnviin_1 c0 wne fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin cvv cvv cxp wss fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin wrel fcnviin_1 c0 wne fcnviin_2 ccnv cvv cvv cxp wss fcnviin_0 fcnviin_1 wrex fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin cvv cvv cxp wss fcnviin_2 ccnv cvv cvv cxp wss fcnviin_1 c0 wne fcnviin_2 ccnv cvv cvv cxp wss fcnviin_0 fcnviin_1 wrex wi fcnviin_0 fcnviin_1 fcnviin_1 c0 wne fcnviin_2 ccnv cvv cvv cxp wss fcnviin_0 fcnviin_1 wral fcnviin_2 ccnv cvv cvv cxp wss fcnviin_0 fcnviin_1 wrex fcnviin_2 ccnv cvv cvv cxp wss fcnviin_0 fcnviin_1 r19.2z expcom fcnviin_2 ccnv cvv cvv cxp wss fcnviin_0 sup_set_class fcnviin_1 wcel fcnviin_2 ccnv wrel fcnviin_2 ccnv cvv cvv cxp wss fcnviin_2 relcnv fcnviin_2 ccnv df-rel mpbi a1i mprg fcnviin_0 fcnviin_1 fcnviin_2 ccnv cvv cvv cxp iinss syl fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin df-rel sylibr icnviin_0 icnviin_1 fcnviin_0 fcnviin_1 fcnviin_2 ciin ccnv fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_0 fcnviin_1 fcnviin_2 ciin wcel icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_2 wcel fcnviin_0 fcnviin_1 wral icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_0 fcnviin_1 fcnviin_2 ciin ccnv wcel icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin wcel icnviin_1 sup_set_class icnviin_0 sup_set_class cop cvv wcel icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_0 fcnviin_1 fcnviin_2 ciin wcel icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_2 wcel fcnviin_0 fcnviin_1 wral wb icnviin_1 sup_set_class icnviin_0 sup_set_class opex fcnviin_0 icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_1 fcnviin_2 cvv eliin ax-mp icnviin_0 sup_set_class icnviin_1 sup_set_class fcnviin_0 fcnviin_1 fcnviin_2 ciin icnviin_0 vex icnviin_1 vex opelcnv icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin wcel icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_2 ccnv wcel fcnviin_0 fcnviin_1 wral icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_2 wcel fcnviin_0 fcnviin_1 wral icnviin_0 sup_set_class icnviin_1 sup_set_class cop cvv wcel icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_0 fcnviin_1 fcnviin_2 ccnv ciin wcel icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_2 ccnv wcel fcnviin_0 fcnviin_1 wral wb icnviin_0 sup_set_class icnviin_1 sup_set_class opex fcnviin_0 icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_1 fcnviin_2 ccnv cvv eliin ax-mp icnviin_0 sup_set_class icnviin_1 sup_set_class cop fcnviin_2 ccnv wcel icnviin_1 sup_set_class icnviin_0 sup_set_class cop fcnviin_2 wcel fcnviin_0 fcnviin_1 icnviin_0 sup_set_class icnviin_1 sup_set_class fcnviin_2 icnviin_0 vex icnviin_1 vex opelcnv ralbii bitri 3bitr4i eqrelriv sylancr $.
$}
$( The converse of a partial order relation is a partial order relation.
       (Contributed by NM, 15-Jun-2005.) $)
${
	$d x y z A $.
	$d x y z R $.
	icnvpo_0 $f set x $.
	icnvpo_1 $f set y $.
	icnvpo_2 $f set z $.
	fcnvpo_0 $f class A $.
	fcnvpo_1 $f class R $.
	cnvpo $p |- ( R Po A <-> `' R Po A ) $= icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_1 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_1 fcnvpo_0 wral icnvpo_2 fcnvpo_0 wral fcnvpo_0 fcnvpo_1 wpo fcnvpo_0 fcnvpo_1 ccnv wpo icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_1 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_2 fcnvpo_0 wral icnvpo_1 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_1 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_1 fcnvpo_0 wral icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_2 fcnvpo_0 wral icnvpo_1 fcnvpo_0 icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral wa icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral wa icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral wa icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 r19.26 icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 ralidm icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral wb fcnvpo_0 c0 fcnvpo_0 c0 wceq icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 rzal icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 rzal 2thd fcnvpo_0 c0 wne icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 r19.3rzv ralbidv pm2.61ine bitr2i anbi1i bitri icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 fcnvpo_0 icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 r19.26 ralbii icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 r19.26 3bitr4i icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 fcnvpo_0 icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral wa icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi icnvpo_2 fcnvpo_0 r19.26 icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 wral icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_2 icnvpo_0 fcnvpo_0 icnvpo_2 sup_set_class icnvpo_0 sup_set_class wceq icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr icnvpo_2 sup_set_class icnvpo_0 sup_set_class wceq icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 icnvpo_2 vex icnvpo_2 vex brcnv icnvpo_2 sup_set_class icnvpo_0 sup_set_class wceq icnvpo_2 sup_set_class icnvpo_0 sup_set_class icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 icnvpo_2 sup_set_class icnvpo_0 sup_set_class wceq id icnvpo_2 sup_set_class icnvpo_0 sup_set_class wceq id breq12d syl5bb notbid cbvralv icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi icnvpo_2 fcnvpo_0 icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 icnvpo_2 vex icnvpo_1 vex brcnv icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 icnvpo_1 vex icnvpo_0 vex brcnv anbi12ci icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 icnvpo_2 vex icnvpo_0 vex brcnv imbi12i ralbii anbi12i bitr2i ralbii icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 icnvpo_2 fcnvpo_0 fcnvpo_0 ralcom bitri bitri ralbii icnvpo_0 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 wbr wn icnvpo_0 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 wbr icnvpo_1 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wa icnvpo_0 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 wbr wi wa icnvpo_2 fcnvpo_0 wral icnvpo_0 icnvpo_1 fcnvpo_0 fcnvpo_0 ralcom icnvpo_2 sup_set_class icnvpo_2 sup_set_class fcnvpo_1 ccnv wbr wn icnvpo_2 sup_set_class icnvpo_1 sup_set_class fcnvpo_1 ccnv wbr icnvpo_1 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wa icnvpo_2 sup_set_class icnvpo_0 sup_set_class fcnvpo_1 ccnv wbr wi wa icnvpo_0 fcnvpo_0 wral icnvpo_2 icnvpo_1 fcnvpo_0 fcnvpo_0 ralcom 3bitr4i icnvpo_0 icnvpo_1 icnvpo_2 fcnvpo_0 fcnvpo_1 df-po icnvpo_2 icnvpo_1 icnvpo_0 fcnvpo_0 fcnvpo_1 ccnv df-po 3bitr4i $.
$}
$( The converse of a strict order relation is a strict order relation.
       (Contributed by NM, 15-Jun-2005.) $)
${
	$d x y A $.
	$d x y R $.
	icnvso_0 $f set x $.
	icnvso_1 $f set y $.
	fcnvso_0 $f class A $.
	fcnvso_1 $f class R $.
	cnvso $p |- ( R Or A <-> `' R Or A ) $= fcnvso_0 fcnvso_1 wpo icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr w3o icnvso_1 fcnvso_0 wral icnvso_0 fcnvso_0 wral wa fcnvso_0 fcnvso_1 ccnv wpo icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 ccnv wbr icnvso_1 sup_set_class icnvso_0 sup_set_class wceq icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 ccnv wbr w3o icnvso_0 fcnvso_0 wral icnvso_1 fcnvso_0 wral wa fcnvso_0 fcnvso_1 wor fcnvso_0 fcnvso_1 ccnv wor fcnvso_0 fcnvso_1 wpo fcnvso_0 fcnvso_1 ccnv wpo icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr w3o icnvso_1 fcnvso_0 wral icnvso_0 fcnvso_0 wral icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 ccnv wbr icnvso_1 sup_set_class icnvso_0 sup_set_class wceq icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 ccnv wbr w3o icnvso_0 fcnvso_0 wral icnvso_1 fcnvso_0 wral fcnvso_0 fcnvso_1 cnvpo icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr w3o icnvso_1 fcnvso_0 wral icnvso_0 fcnvso_0 wral icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr w3o icnvso_0 fcnvso_0 wral icnvso_1 fcnvso_0 wral icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 ccnv wbr icnvso_1 sup_set_class icnvso_0 sup_set_class wceq icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 ccnv wbr w3o icnvso_0 fcnvso_0 wral icnvso_1 fcnvso_0 wral icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr w3o icnvso_0 icnvso_1 fcnvso_0 fcnvso_0 ralcom icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 ccnv wbr icnvso_1 sup_set_class icnvso_0 sup_set_class wceq icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 ccnv wbr w3o icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr w3o icnvso_1 icnvso_0 fcnvso_0 fcnvso_0 icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 ccnv wbr icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 wbr icnvso_1 sup_set_class icnvso_0 sup_set_class wceq icnvso_0 sup_set_class icnvso_1 sup_set_class wceq icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 ccnv wbr icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 wbr icnvso_1 sup_set_class icnvso_0 sup_set_class fcnvso_1 icnvso_1 vex icnvso_0 vex brcnv icnvso_1 icnvso_0 equcom icnvso_0 sup_set_class icnvso_1 sup_set_class fcnvso_1 icnvso_0 vex icnvso_1 vex brcnv 3orbi123i 2ralbii bitr4i anbi12i icnvso_0 icnvso_1 fcnvso_0 fcnvso_1 df-so icnvso_1 icnvso_0 fcnvso_0 fcnvso_1 ccnv df-so 3bitr4i $.
$}
$( The composition of two sets is a set.  (Contributed by NM,
     19-Mar-1998.) $)
${
	fcoexg_0 $f class A $.
	fcoexg_1 $f class B $.
	fcoexg_2 $f class V $.
	fcoexg_3 $f class W $.
	coexg $p |- ( ( A e. V /\ B e. W ) -> ( A o. B ) e. _V ) $= fcoexg_0 fcoexg_2 wcel fcoexg_1 fcoexg_3 wcel wa fcoexg_0 fcoexg_1 ccom fcoexg_1 cdm fcoexg_0 crn cxp wss fcoexg_1 cdm fcoexg_0 crn cxp cvv wcel fcoexg_0 fcoexg_1 ccom cvv wcel fcoexg_0 fcoexg_1 ccom wrel fcoexg_0 fcoexg_1 ccom fcoexg_1 cdm fcoexg_0 crn cxp wss fcoexg_0 fcoexg_1 relco fcoexg_0 fcoexg_1 ccom wrel fcoexg_0 fcoexg_1 ccom fcoexg_0 fcoexg_1 ccom cdm fcoexg_0 fcoexg_1 ccom crn cxp fcoexg_1 cdm fcoexg_0 crn cxp fcoexg_0 fcoexg_1 ccom relssdmrn fcoexg_0 fcoexg_1 ccom cdm fcoexg_1 cdm wss fcoexg_0 fcoexg_1 ccom crn fcoexg_0 crn wss fcoexg_0 fcoexg_1 ccom cdm fcoexg_0 fcoexg_1 ccom crn cxp fcoexg_1 cdm fcoexg_0 crn cxp wss fcoexg_0 fcoexg_1 dmcoss fcoexg_0 fcoexg_1 rncoss fcoexg_0 fcoexg_1 ccom cdm fcoexg_1 cdm fcoexg_0 fcoexg_1 ccom crn fcoexg_0 crn xpss12 mp2an syl6ss ax-mp fcoexg_1 fcoexg_3 wcel fcoexg_1 cdm cvv wcel fcoexg_0 crn cvv wcel fcoexg_1 cdm fcoexg_0 crn cxp cvv wcel fcoexg_0 fcoexg_2 wcel fcoexg_1 fcoexg_3 dmexg fcoexg_0 fcoexg_2 rnexg fcoexg_1 cdm fcoexg_0 crn cvv cvv xpexg syl2anr fcoexg_0 fcoexg_1 ccom fcoexg_1 cdm fcoexg_0 crn cxp cvv ssexg sylancr $.
$}
$( The composition of two sets is a set.  (Contributed by NM,
       15-Dec-2003.) $)
${
	fcoex_0 $f class A $.
	fcoex_1 $f class B $.
	ecoex_0 $e |- A e. _V $.
	ecoex_1 $e |- B e. _V $.
	coex $p |- ( A o. B ) e. _V $= fcoex_0 cvv wcel fcoex_1 cvv wcel fcoex_0 fcoex_1 ccom cvv wcel ecoex_0 ecoex_1 fcoex_0 fcoex_1 cvv cvv coexg mp2an $.
$}

