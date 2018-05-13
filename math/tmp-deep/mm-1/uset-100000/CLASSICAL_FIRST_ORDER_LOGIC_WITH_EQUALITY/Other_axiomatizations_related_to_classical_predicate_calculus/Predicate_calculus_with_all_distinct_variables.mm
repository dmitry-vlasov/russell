$[ turnstile_special_source.mm $]

$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Existential_uniqueness.mm $]

$(=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with all distinct variables

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(Distinct variable version of ~ ax-7 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_ax-7d $f wff ph $.
	f1_ax-7d $f set x $.
	f2_ax-7d $f set y $.
	a_ax-7d $a |- ( A. x A. y ph -> A. y A. x ph ) $.
$}

$(Distinct variable version of ~ ax-8 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)

${
	$v x y z  $.
	$d x y z  $.
	f0_ax-8d $f set x $.
	f1_ax-8d $f set y $.
	f2_ax-8d $f set z $.
	a_ax-8d $a |- ( x = y -> ( x = z -> y = z ) ) $.
$}

$(Distinct variable version of ~ ax9 , equal variables case.  (Contributed
       by Mario Carneiro, 14-Aug-2015.) $)

${
	$v x  $.
	$d x  $.
	f0_ax-9d1 $f set x $.
	a_ax-9d1 $a |- -. A. x -. x = x $.
$}

$(Distinct variable version of ~ ax9 , distinct variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)

${
	$v x y  $.
	$d x y  $.
	f0_ax-9d2 $f set x $.
	f1_ax-9d2 $f set y $.
	a_ax-9d2 $a |- -. A. x -. x = y $.
$}

$(Distinct variable version of ~ ax10 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)

${
	$v x y  $.
	$d x y  $.
	f0_ax-10d $f set x $.
	f1_ax-10d $f set y $.
	a_ax-10d $a |- ( A. x x = y -> A. y y = x ) $.
$}

$(Distinct variable version of ~ ax-11 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)

${
	$v ph x y  $.
	$d x y  $.
	f0_ax-11d $f wff ph $.
	f1_ax-11d $f set x $.
	f2_ax-11d $f set y $.
	a_ax-11d $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
$}


