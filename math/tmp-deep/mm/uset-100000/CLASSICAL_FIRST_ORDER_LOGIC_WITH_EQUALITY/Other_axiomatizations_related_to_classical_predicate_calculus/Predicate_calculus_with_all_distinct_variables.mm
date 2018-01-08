
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Existential_uniqueness.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Predicate calculus with all distinct variables

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( Distinct variable version of ~ ax-7 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-7d $a |- ( A. x A. y ph -> A. y A. x ph ) $.

    $( Distinct variable version of ~ ax-8 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-8d $a |- ( x = y -> ( x = z -> y = z ) ) $.

    $( Distinct variable version of ~ ax9 , equal variables case.  (Contributed
       by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d1 $a |- -. A. x -. x = x $.

    $( Distinct variable version of ~ ax9 , distinct variables case.
       (Contributed by Mario Carneiro, 14-Aug-2015.) $)
    ax-9d2 $a |- -. A. x -. x = y $.

    $( Distinct variable version of ~ ax10 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-10d $a |- ( A. x x = y -> A. y y = x ) $.

    $( Distinct variable version of ~ ax-11 .  (Contributed by Mario Carneiro,
       14-Aug-2015.) $)
    ax-11d $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.
  $}


