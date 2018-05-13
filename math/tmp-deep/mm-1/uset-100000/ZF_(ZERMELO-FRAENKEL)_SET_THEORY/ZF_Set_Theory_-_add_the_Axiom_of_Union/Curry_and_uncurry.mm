$[ turnstile_special_source.mm $]

$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Function_transposition.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Curry and uncurry

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$c curry $.

$c uncurry $.

$(Extend class notation to include the currying function. $)

${
	$v A  $.
	f0_ccur $f class A $.
	a_ccur $a class curry A $.
$}

$(Extend class notation to include the uncurrying function. $)

${
	$v A  $.
	f0_cunc $f class A $.
	a_cunc $a class uncurry A $.
$}

$(Define the currying of ` F ` , which splits a function of two arguments
       into a function of the first argument, producing a function over the
       second argument.  (Contributed by Mario Carneiro, 7-Jan-2017.) $)

${
	$v x y z F  $.
	$d x y z F  $.
	f0_df-cur $f set x $.
	f1_df-cur $f set y $.
	f2_df-cur $f set z $.
	f3_df-cur $f class F $.
	a_df-cur $a |- curry F = ( x e. dom dom F |-> { <. y , z >. | <. x , y >. F z } ) $.
$}

$(Define the uncurrying of ` F ` , which takes a function producing
       functions, and transforms it into a two-argument function.  (Contributed
       by Mario Carneiro, 7-Jan-2017.) $)

${
	$v x y z F  $.
	$d x y z F  $.
	f0_df-unc $f set x $.
	f1_df-unc $f set y $.
	f2_df-unc $f set z $.
	f3_df-unc $f class F $.
	a_df-unc $a |- uncurry F = { <. <. x , y >. , z >. | y ( F ` x ) z } $.
$}


