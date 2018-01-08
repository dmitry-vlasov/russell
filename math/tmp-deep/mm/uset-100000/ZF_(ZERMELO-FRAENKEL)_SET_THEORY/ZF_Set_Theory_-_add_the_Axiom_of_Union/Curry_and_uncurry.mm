
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Function_transposition.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Curry and uncurry

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c curry $.
  $c uncurry $.

  $( Extend class notation to include the currying function. $)
  ccur $a class curry A $.

  $( Extend class notation to include the uncurrying function. $)
  cunc $a class uncurry A $.

  ${
    $d x y z F $.
    $( Define the currying of ` F ` , which splits a function of two arguments
       into a function of the first argument, producing a function over the
       second argument.  (Contributed by Mario Carneiro, 7-Jan-2017.) $)
    df-cur $a |- curry F = ( x e. dom dom F |->
      { <. y , z >. | <. x , y >. F z } ) $.

    $( Define the uncurrying of ` F ` , which takes a function producing
       functions, and transforms it into a two-argument function.  (Contributed
       by Mario Carneiro, 7-Jan-2017.) $)
    df-unc $a |- uncurry F = { <. <. x , y >. , z >. | y ( F ` x ) z } $.
  $}


