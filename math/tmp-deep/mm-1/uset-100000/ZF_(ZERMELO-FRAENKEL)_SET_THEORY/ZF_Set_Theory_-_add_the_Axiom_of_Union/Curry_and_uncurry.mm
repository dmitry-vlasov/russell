$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Function_transposition.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Curry and uncurry

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$c curry  $.
$c uncurry  $.
$( Extend class notation to include the currying function. $)
${
	fccur_0 $f class A $.
	ccur $a class curry A $.
$}
$( Extend class notation to include the uncurrying function. $)
${
	fcunc_0 $f class A $.
	cunc $a class uncurry A $.
$}
$( Define the currying of ` F ` , which splits a function of two arguments
       into a function of the first argument, producing a function over the
       second argument.  (Contributed by Mario Carneiro, 7-Jan-2017.) $)
${
	$d x y z F $.
	fdf-cur_0 $f set x $.
	fdf-cur_1 $f set y $.
	fdf-cur_2 $f set z $.
	fdf-cur_3 $f class F $.
	df-cur $a |- curry F = ( x e. dom dom F |-> { <. y , z >. | <. x , y >. F z } ) $.
$}
$( Define the uncurrying of ` F ` , which takes a function producing
       functions, and transforms it into a two-argument function.  (Contributed
       by Mario Carneiro, 7-Jan-2017.) $)
${
	$d x y z F $.
	fdf-unc_0 $f set x $.
	fdf-unc_1 $f set y $.
	fdf-unc_2 $f set z $.
	fdf-unc_3 $f class F $.
	df-unc $a |- uncurry F = { <. <. x , y >. , z >. | y ( F ` x ) z } $.
$}

