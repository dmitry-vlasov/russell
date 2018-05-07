$[ turnstile_special_source.mm $]
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Existential_uniqueness.mm $]
$( =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with all distinct variables

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
$( Distinct variable version of ~ ax-7 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fax-7d_0 $f wff ph $.
	fax-7d_1 $f set x $.
	fax-7d_2 $f set y $.
	ax-7d $a |- ( A. x A. y ph -> A. y A. x ph ) $.
$}
$( Distinct variable version of ~ ax-8 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$v z $.
	$d x y z $.
	fax-8d_0 $f set x $.
	fax-8d_1 $f set y $.
	fax-8d_2 $f set z $.
	ax-8d $a |- ( x = y -> ( x = z -> y = z ) ) $.
$}
$( Distinct variable version of ~ ax9 , equal variables case.  (Contributed
       by Mario Carneiro, 14-Aug-2015.) $)
${
	$v x $.
	fax-9d1_0 $f set x $.
	ax-9d1 $a |- -. A. x -. x = x $.
$}
$( Distinct variable version of ~ ax9 , distinct variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fax-9d2_0 $f set x $.
	fax-9d2_1 $f set y $.
	ax-9d2 $a |- -. A. x -. x = y $.
$}
$( Distinct variable version of ~ ax10 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
${
	$v x $.
	$v y $.
	$d x y $.
	fax-10d_0 $f set x $.
	fax-10d_1 $f set y $.
	ax-10d $a |- ( A. x x = y -> A. y y = x ) $.
$}
$( Distinct variable version of ~ ax-11 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
${
	$v ph $.
	$v x $.
	$v y $.
	$d x y $.
	fax-11d_0 $f wff ph $.
	fax-11d_1 $f set x $.
	fax-11d_2 $f set y $.
	ax-11d $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
$}

