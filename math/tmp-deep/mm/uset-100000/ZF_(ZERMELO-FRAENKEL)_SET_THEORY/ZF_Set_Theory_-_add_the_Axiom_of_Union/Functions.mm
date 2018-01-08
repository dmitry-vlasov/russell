
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Definite_description_binder_(inverted_iota).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                                 Functions

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c : $. $( Colon $)
  $c Fun $. $( Function predicate $)
  $c Fn $. $( Function connective $)
  $c --> $. $( Domain-codomain connective $)
  $c -1-1-> $. $( 'One-to-one' domain-codomain connective $)
  $c -onto-> $. $( 'Onto' domain-codomain connective $)
  $c -1-1-onto-> $. $( 'One-to-one' and 'onto' domain-codomain connective $)
  $c ` $. $( Left apostrophe (function value symbol) $)
  $c Isom $. $( Isomorphism $)

  $( Extend the definition of a wff to include the function predicate.  (Read:
     ` A ` is a function.) $)
  wfun $a wff Fun A $.

  $( Extend the definition of a wff to include the function predicate with a
     domain.  (Read: ` A ` is a function on ` B ` .) $)
  wfn $a wff A Fn B $.

  $( Extend the definition of a wff to include the function predicate with
     domain and codomain.  (Read: ` F ` maps ` A ` into ` B ` .) $)
  wf $a wff F : A --> B $.

  $( Extend the definition of a wff to include one-to-one functions.  (Read:
     ` F ` maps ` A ` one-to-one into ` B ` .)  The notation ("1-1" above the
     arrow) is from Definition 6.15(5) of [TakeutiZaring] p. 27. $)
  wf1 $a wff F : A -1-1-> B $.

  $( Extend the definition of a wff to include onto functions.  (Read: ` F `
     maps ` A ` onto ` B ` .)  The notation ("onto" below the arrow) is from
     Definition 6.15(4) of [TakeutiZaring] p. 27. $)
  wfo $a wff F : A -onto-> B $.

  $( Extend the definition of a wff to include one-to-one onto functions.
     (Read: ` F ` maps ` A ` one-to-one onto ` B ` .)  The notation ("1-1"
     above the arrow and "onto" below the arrow) is from Definition 6.15(6) of
     [TakeutiZaring] p. 27. $)
  wf1o $a wff F : A -1-1-onto-> B $.

  $( Extend the definition of a class to include the value of a function.
     (Read:  The value of ` F ` at ` A ` , or " ` F ` of ` A ` .") $)
  cfv $a class ( F ` A ) $.

  $( Extend the definition of a wff to include the isomorphism property.
     (Read: ` H ` is an ` R ` , ` S ` isomorphism of ` A ` onto ` B ` .) $)
  wiso $a wff H Isom R , S ( A , B ) $.

  ${
    $d x A $.  $d x F $.
    $( Define predicate that determines if some class ` A ` is a function.
       Definition 10.1 of [Quine] p. 65.  For example, the expression
       ` Fun cos ` is true once we define cosine ( ~ df-cos ).  This is not the
       same as defining a specific function's mapping, which is typically done
       using the format of ~ cmpt with the maps-to notation (see ~ df-mpt and
       ~ df-mpt2 ).  Contrast this predicate with the predicates to determine
       if some class is a function with a given domain ( ~ df-fn ), a function
       with a given domain and codomain ( ~ df-f ), a one-to-one function
       ( ~ df-f1 ), an onto function ( ~ df-fo ), or a one-to-one onto function
       ( ~ df-f1o ).  For alternate definitions, see ~ dffun2 , ~ dffun3 ,
       ~ dffun4 , ~ dffun5 , ~ dffun6 , ~ dffun7 , ~ dffun8 , and ~ dffun9 .
       (Contributed by NM, 1-Aug-1994.) $)
    df-fun $a |- ( Fun A <-> ( Rel A /\ ( A o. `' A ) C_ _I ) ) $.

    $( Define a function with domain.  Definition 6.15(1) of [TakeutiZaring]
       p. 27.  For alternate definitions, see ~ dffn2 , ~ dffn3 , ~ dffn4 , and
       ~ dffn5 .  (Contributed by NM, 1-Aug-1994.) $)
    df-fn $a |- ( A Fn B <-> ( Fun A /\ dom A = B ) ) $.

    $( Define a function (mapping) with domain and codomain.  Definition
       6.15(3) of [TakeutiZaring] p. 27.  For alternate definitions, see
       ~ dff2 , ~ dff3 , and ~ dff4 .  (Contributed by NM, 1-Aug-1994.) $)
    df-f $a |- ( F : A --> B <-> ( F Fn A /\ ran F C_ B ) ) $.

    $( Define a one-to-one function.  For equivalent definitions see ~ dff12
       and ~ dff13 .  Compare Definition 6.15(5) of [TakeutiZaring] p. 27.  We
       use their notation ("1-1" above the arrow).  (Contributed by NM,
       1-Aug-1994.) $)
    df-f1 $a |- ( F : A -1-1-> B <-> ( F : A --> B /\ Fun `' F ) ) $.

    $( Define an onto function.  Definition 6.15(4) of [TakeutiZaring] p. 27.
       We use their notation ("onto" under the arrow).  For alternate
       definitions, see ~ dffo2 , ~ dffo3 , ~ dffo4 , and ~ dffo5 .
       (Contributed by NM, 1-Aug-1994.) $)
    df-fo $a |- ( F : A -onto-> B <-> ( F Fn A /\ ran F = B ) ) $.

    $( Define a one-to-one onto function.  For equivalent definitions see
       ~ dff1o2 , ~ dff1o3 , ~ dff1o4 , and ~ dff1o5 .  Compare Definition
       6.15(6) of [TakeutiZaring] p. 27.  We use their notation ("1-1" above
       the arrow and "onto" below the arrow).  (Contributed by NM,
       1-Aug-1994.) $)
    df-f1o $a |- ( F : A -1-1-onto-> B <->
                ( F : A -1-1-> B /\ F : A -onto-> B ) ) $.

    $( Define the value of a function, ` ( F `` A ) ` , also known as function
       application.  For example, ` ( cos `` 0 ) = 1 ` (we prove this in ~ cos0
       after we define cosine in ~ df-cos ).  Typically, function ` F ` is
       defined using maps-to notation (see ~ df-mpt and ~ df-mpt2 ), but this
       is not required.  For example,
       ` F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ( F `` 3 ) = 9 ` ( ~ ex-fv ).
       Note that ~ df-ov will define two-argument functions using ordered pairs
       as ` ( A F B ) = ( F `` <. A , B >. ) ` .  This particular definition is
       quite convenient: it can be applied to any class and evaluates to the
       empty set when it is not meaningful (as shown by ~ ndmfv and ~ fvprc ).
       The left apostrophe notation originated with Peano and was adopted in
       Definition *30.01 of [WhiteheadRussell] p. 235, Definition 10.11 of
       [Quine] p. 68, and Definition 6.11 of [TakeutiZaring] p. 26.  It means
       the same thing as the more familiar ` F ( A ) ` notation for a
       function's value at ` A ` , i.e.  " ` F ` of ` A ` ," but without
       context-dependent notational ambiguity.  Alternate definitions are
       ~ dffv2 , ~ dffv3 , ~ fv2 , and ~ fv3 (the latter two previously
       required ` A ` to be a set.)  Restricted equivalents that require ` F `
       to be a function are shown in ~ funfv and ~ funfv2 .  For the familiar
       definition of function value in terms of ordered pair membership, see
       ~ funopfvb .  (Contributed by Scott Fenton, 6-Oct-2017.) $)
    df-fv $a |- ( F ` A ) = ( iota x A F x ) $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $( Define the isomorphism predicate.  We read this as " ` H ` is an ` R ` ,
       ` S ` isomorphism of ` A ` onto ` B ` ."  Normally, ` R ` and ` S ` are
       ordering relations on ` A ` and ` B ` respectively.  Definition 6.28 of
       [TakeutiZaring] p. 32, whose notation is the same as ours except that
       ` R ` and ` S ` are subscripts.  (Contributed by NM, 4-Mar-1997.) $)
    df-isom $a |- ( H Isom R , S ( A , B ) <-> ( H : A -1-1-onto-> B /\
                 A. x e. A A. y e. A ( x R y <-> ( H ` x ) S ( H ` y ) ) ) ) $.
  $}

  ${
    $d x y z A $.
    $( Alternate definition of a function.  (Contributed by NM,
       29-Dec-1996.) $)
    dffun2 $p |- ( Fun A <-> ( Rel A /\
                 A. x A. y A. z ( ( x A y /\ x A z ) -> y = z ) ) ) $=
      cA wfun cA wrel cA cA ccnv ccom cid wss wa cA wrel vx cv vy cv cA wbr vx
      cv vz cv cA wbr wa vy cv vz cv wceq wi vz wal vy wal vx wal wa cA df-fun
      cA cA ccnv ccom cid wss vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz
      cv wceq wi vz wal vy wal vx wal cA wrel cA cA ccnv ccom cid wss vy cv vx
      cv cA ccnv wbr vx cv vz cv cA wbr wa vx wex vy cv vz cv wceq wi vz wal vy
      wal vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq wi vz wal
      vx wal vy wal vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq
      wi vz wal vy wal vx wal cA cA ccnv ccom cid wss cA cA ccnv ccom vy cv vz
      cv wceq vy vz copab wss vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx
      wex vy vz copab vy cv vz cv wceq vy vz copab wss vy cv vx cv cA ccnv wbr
      vx cv vz cv cA wbr wa vx wex vy cv vz cv wceq wi vz wal vy wal cid vy cv
      vz cv wceq vy vz copab cA cA ccnv ccom vy vz df-id sseq2i cA cA ccnv ccom
      vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx wex vy vz copab vy cv vz
      cv wceq vy vz copab vy vz vx cA cA ccnv df-co sseq1i vy cv vx cv cA ccnv
      wbr vx cv vz cv cA wbr wa vx wex vy cv vz cv wceq vy vz ssopab2b 3bitri
      vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx wex vy cv vz cv wceq wi
      vz wal vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq wi vz
      wal vx wal vy vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx wex vy cv
      vz cv wceq wi vz wal vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv
      wceq wi vx wal vz wal vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz
      cv wceq wi vz wal vx wal vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx
      wex vy cv vz cv wceq wi vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz
      cv wceq wi vx wal vz vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx wex
      vy cv vz cv wceq wi vx cv vy cv cA wbr vx cv vz cv cA wbr wa vx wex vy cv
      vz cv wceq wi vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq
      wi vx wal vy cv vx cv cA ccnv wbr vx cv vz cv cA wbr wa vx wex vx cv vy
      cv cA wbr vx cv vz cv cA wbr wa vx wex vy cv vz cv wceq vy cv vx cv cA
      ccnv wbr vx cv vz cv cA wbr wa vx cv vy cv cA wbr vx cv vz cv cA wbr wa
      vx vy cv vx cv cA ccnv wbr vx cv vy cv cA wbr vx cv vz cv cA wbr vy cv vx
      cv cA vy vex vx vex brcnv anbi1i exbii imbi1i vx cv vy cv cA wbr vx cv vz
      cv cA wbr wa vy cv vz cv wceq vx 19.23v bitr4i albii vx cv vy cv cA wbr
      vx cv vz cv cA wbr wa vy cv vz cv wceq wi vz vx alcom bitri albii vx cv
      vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq wi vz wal vy vx alcom
      3bitri anbi2i bitri $.

    $( Alternate definition of function.  (Contributed by NM, 29-Dec-1996.) $)
    dffun3 $p |- ( Fun A <-> ( Rel A /\
                 A. x E. z A. y ( x A y -> y = z ) ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq
      wi vz wal vy wal vx wal wa cA wrel vx cv vy cv cA wbr vy cv vz cv wceq wi
      vy wal vz wex vx wal wa vx vy vz cA dffun2 vx cv vy cv cA wbr vx cv vz cv
      cA wbr wa vy cv vz cv wceq wi vz wal vy wal vx wal vx cv vy cv cA wbr vy
      cv vz cv wceq wi vy wal vz wex vx wal cA wrel vx cv vy cv cA wbr vx cv vz
      cv cA wbr wa vy cv vz cv wceq wi vz wal vy wal vx cv vy cv cA wbr vy cv
      vz cv wceq wi vy wal vz wex vx vx cv vy cv cA wbr vx cv vz cv cA wbr wa
      vy cv vz cv wceq wi vz wal vy wal vx cv vy cv cA wbr vy wmo vx cv vy cv
      cA wbr vy cv vz cv wceq wi vy wal vz wex vx cv vy cv cA wbr vx cv vz cv
      cA wbr vy vz vy cv vz cv vx cv cA breq2 mo4 vx cv vy cv cA wbr vy vz vx
      cv vy cv cA wbr vz nfv mo2 bitr3i albii anbi2i bitri $.

    $( Alternate definition of a function.  Definition 6.4(4) of
       [TakeutiZaring] p. 24.  (Contributed by NM, 29-Dec-1996.) $)
    dffun4 $p |- ( Fun A <-> ( Rel A /\
                 A. x A. y A. z ( ( <. x , y >. e. A /\ <. x , z >. e. A )
                 -> y = z ) ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq
      wi vz wal vy wal vx wal wa cA wrel vx cv vy cv cop cA wcel vx cv vz cv
      cop cA wcel wa vy cv vz cv wceq wi vz wal vy wal vx wal wa vx vy vz cA
      dffun2 vx cv vy cv cA wbr vx cv vz cv cA wbr wa vy cv vz cv wceq wi vz
      wal vy wal vx wal vx cv vy cv cop cA wcel vx cv vz cv cop cA wcel wa vy
      cv vz cv wceq wi vz wal vy wal vx wal cA wrel vx cv vy cv cA wbr vx cv vz
      cv cA wbr wa vy cv vz cv wceq wi vz wal vx cv vy cv cop cA wcel vx cv vz
      cv cop cA wcel wa vy cv vz cv wceq wi vz wal vx vy vx cv vy cv cA wbr vx
      cv vz cv cA wbr wa vy cv vz cv wceq wi vx cv vy cv cop cA wcel vx cv vz
      cv cop cA wcel wa vy cv vz cv wceq wi vz vx cv vy cv cA wbr vx cv vz cv
      cA wbr wa vx cv vy cv cop cA wcel vx cv vz cv cop cA wcel wa vy cv vz cv
      wceq vx cv vy cv cA wbr vx cv vy cv cop cA wcel vx cv vz cv cA wbr vx cv
      vz cv cop cA wcel vx cv vy cv cA df-br vx cv vz cv cA df-br anbi12i
      imbi1i albii 2albii anbi2i bitri $.

    $( Alternate definition of function.  (Contributed by NM, 29-Dec-1996.) $)
    dffun5 $p |- ( Fun A <-> ( Rel A /\
                 A. x E. z A. y ( <. x , y >. e. A -> y = z ) ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vy cv vz cv wceq wi vy wal vz wex vx
      wal wa cA wrel vx cv vy cv cop cA wcel vy cv vz cv wceq wi vy wal vz wex
      vx wal wa vx vy vz cA dffun3 vx cv vy cv cA wbr vy cv vz cv wceq wi vy
      wal vz wex vx wal vx cv vy cv cop cA wcel vy cv vz cv wceq wi vy wal vz
      wex vx wal cA wrel vx cv vy cv cA wbr vy cv vz cv wceq wi vy wal vz wex
      vx cv vy cv cop cA wcel vy cv vz cv wceq wi vy wal vz wex vx vx cv vy cv
      cA wbr vy cv vz cv wceq wi vy wal vx cv vy cv cop cA wcel vy cv vz cv
      wceq wi vy wal vz vx cv vy cv cA wbr vy cv vz cv wceq wi vx cv vy cv cop
      cA wcel vy cv vz cv wceq wi vy vx cv vy cv cA wbr vx cv vy cv cop cA wcel
      vy cv vz cv wceq vx cv vy cv cA df-br imbi1i albii exbii albii anbi2i
      bitri $.
  $}

  ${
    $d x y w v u $.  $d A w v u $.
    dffun6f.1 $e |- F/_ x A $.
    dffun6f.2 $e |- F/_ y A $.
    $( Definition of function, using bound-variable hypotheses instead of
       distinct variable conditions.  (Contributed by NM, 9-Mar-1995.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    dffun6f $p |- ( Fun A <-> ( Rel A /\ A. x E* y x A y ) ) $=
      cA wfun cA wrel vw cv vv cv cA wbr vv cv vu cv wceq wi vv wal vu wex vw
      wal wa cA wrel vx cv vy cv cA wbr vy wmo vx wal wa vw vv vu cA dffun3 vx
      cv vy cv cA wbr vy wmo vx wal vw cv vv cv cA wbr vv cv vu cv wceq wi vv
      wal vu wex vw wal cA wrel vw cv vv cv cA wbr vv wmo vw wal vw cv vy cv cA
      wbr vy wmo vw wal vw cv vv cv cA wbr vv cv vu cv wceq wi vv wal vu wex vw
      wal vx cv vy cv cA wbr vy wmo vx wal vw cv vv cv cA wbr vv wmo vw cv vy
      cv cA wbr vy wmo vw vw cv vv cv cA wbr vw cv vy cv cA wbr vv vy vy vw cv
      vv cv cA vy vw cv nfcv dffun6f.2 vy vv cv nfcv nfbr vw cv vy cv cA wbr vv
      nfv vv cv vy cv vw cv cA breq2 cbvmo albii vw cv vv cv cA wbr vv wmo vw
      cv vv cv cA wbr vv cv vu cv wceq wi vv wal vu wex vw vw cv vv cv cA wbr
      vv vu vw cv vv cv cA wbr vu nfv mo2 albii vw cv vy cv cA wbr vy wmo vx cv
      vy cv cA wbr vy wmo vw vx vw cv vy cv cA wbr vx vy vx vw cv vy cv cA vx
      vw cv nfcv dffun6f.1 vx vy cv nfcv nfbr nfmo vx cv vy cv cA wbr vy wmo vw
      nfv vw cv vx cv wceq vw cv vy cv cA wbr vx cv vy cv cA wbr vy vw cv vx cv
      vy cv cA breq1 mobidv cbval 3bitr3ri anbi2i bitr4i $.
  $}

  ${
    $d x y A $.  $d x y z F $.
    $( Alternate definition of a function using "at most one" notation.
       (Contributed by NM, 9-Mar-1995.) $)
    dffun6 $p |- ( Fun F <-> ( Rel F /\ A. x E* y x F y ) ) $=
      vx vy cF vx cF nfcv vy cF nfcv dffun6f $.

    $( A function has at most one value for each argument.  (Contributed by NM,
       24-May-1998.) $)
    funmo $p |- ( Fun F -> E* y A F y ) $=
      cF wfun cA vy cv cF wbr cA cvv wcel cA vy cv cF wbr wa wi vy wal cA cvv
      wcel cA vy cv cF wbr wa vy wmo cA vy cv cF wbr vy wmo cF wfun cA vy cv cF
      wbr cA cvv wcel cA vy cv cF wbr wa wi vy cF wfun cA vy cv cF wbr cA cvv
      wcel cF wfun cF wrel cA vy cv cF wbr cA cvv wcel wi cF wfun cF wrel vx cv
      vy cv cF wbr vy wmo vx wal vx vy cF dffun6 simplbi cF wrel cA vy cv cF
      wbr cA cvv wcel cA vy cv cF brrelex ex syl ancrd alrimiv cF wfun cA cvv
      wcel cA vy cv cF wbr vy wmo wi cA cvv wcel cA vy cv cF wbr wa vy wmo cA
      cvv wcel cF wfun cA vy cv cF wbr vy wmo cF wfun vx cv vy cv cF wbr vy wmo
      wi cF wfun cA vy cv cF wbr vy wmo wi vx cA cvv vx cv cA wceq vx cv vy cv
      cF wbr vy wmo cA vy cv cF wbr vy wmo cF wfun vx cv cA wceq vx cv vy cv cF
      wbr cA vy cv cF wbr vy vx cv cA vy cv cF breq1 mobidv imbi2d cF wfun vx
      cv vy cv cF wbr vy wmo vx cF wfun cF wrel vx cv vy cv cF wbr vy wmo vx
      wal vx vy cF dffun6 simprbi 19.21bi vtoclg com12 cA cvv wcel cA vy cv cF
      wbr vy moanimv sylibr cA vy cv cF wbr cA cvv wcel cA vy cv cF wbr wa vy
      moim sylc $.
  $}

  $( A function is a relation.  (Contributed by NM, 1-Aug-1994.) $)
  funrel $p |- ( Fun A -> Rel A ) $=
    cA wfun cA wrel cA cA ccnv ccom cid wss cA df-fun simplbi $.

  ${
    $d x y z A $.  $d x y z B $.
    $( Subclass theorem for function predicate.  (Contributed by NM,
       16-Aug-1994.)  (Proof shortened by Mario Carneiro, 24-Jun-2014.) $)
    funss $p |- ( A C_ B -> ( Fun B -> Fun A ) ) $=
      cA cB wss cB wrel cB cB ccnv ccom cid wss wa cA wrel cA cA ccnv ccom cid
      wss wa cB wfun cA wfun cA cB wss cB wrel cA wrel cB cB ccnv ccom cid wss
      cA cA ccnv ccom cid wss cA cB relss cA cB wss cA cA ccnv ccom cB cB ccnv
      ccom wss cB cB ccnv ccom cid wss cA cA ccnv ccom cid wss wi cA cB wss cA
      cA ccnv ccom cB cA ccnv ccom cB cB ccnv ccom cA cB cA ccnv coss1 cA cB
      wss cA ccnv cB ccnv wss cB cA ccnv ccom cB cB ccnv ccom wss cA cB cnvss
      cA ccnv cB ccnv cB coss2 syl sstrd cA cA ccnv ccom cB cB ccnv ccom cid
      sstr2 syl anim12d cB df-fun cA df-fun 3imtr4g $.
  $}

  $( Equality theorem for function predicate.  (Contributed by NM,
     16-Aug-1994.) $)
  funeq $p |- ( A = B -> ( Fun A <-> Fun B ) ) $=
    cA cB wceq cA wfun cB wfun cA cB wceq cB cA wss cA wfun cB wfun wi cB cA
    eqimss2 cB cA funss syl cA cB wceq cA cB wss cB wfun cA wfun wi cA cB
    eqimss cA cB funss syl impbid $.

  ${
    funeqi.1 $e |- A = B $.
    $( Equality inference for the function predicate.  (Contributed by Jonathan
       Ben-Naim, 3-Jun-2011.) $)
    funeqi $p |- ( Fun A <-> Fun B ) $=
      cA cB wceq cA wfun cB wfun wb funeqi.1 cA cB funeq ax-mp $.
  $}

  ${
    funeqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for the function predicate.  (Contributed by NM,
       23-Feb-2013.) $)
    funeqd $p |- ( ph -> ( Fun A <-> Fun B ) ) $=
      wph cA cB wceq cA wfun cB wfun wb funeqd.1 cA cB funeq syl $.
  $}

  ${
    nffun.1 $e |- F/_ x F $.
    $( Bound-variable hypothesis builder for a function.  (Contributed by NM,
       30-Jan-2004.) $)
    nffun $p |- F/ x Fun F $=
      cF wfun cF wrel cF cF ccnv ccom cid wss wa vx cF df-fun cF wrel cF cF
      ccnv ccom cid wss vx vx cF nffun.1 nfrel vx cF cF ccnv ccom cid vx cF cF
      ccnv nffun.1 vx cF nffun.1 nfcnv nfco vx cid nfcv nfss nfan nfxfr $.
  $}

  ${
    $d y A $.  $d y F $.
    $( There is exactly one value of a function.  (Contributed by NM,
       22-Apr-2004.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    funeu $p |- ( ( Fun F /\ A F B ) -> E! y A F y ) $=
      cF wfun cA cB cF wbr wa cA vy cv cF wbr vy wex cA vy cv cF wbr vy weu cF
      wfun cA cB cF wbr wa cA cF cdm wcel cA vy cv cF wbr vy wex cF wfun cF
      wrel cA cB cF wbr cA cF cdm wcel cF funrel cA cB cF releldm sylan cA cF
      cdm wcel cA vy cv cF wbr vy wex vy cA cF cF cdm eldmg ibi syl cF wfun cA
      cB cF wbr wa cA vy cv cF wbr vy wmo cA vy cv cF wbr vy wex cA vy cv cF
      wbr vy weu wi cF wfun cA vy cv cF wbr vy wmo cA cB cF wbr vy cA cF funmo
      adantr cA vy cv cF wbr vy df-mo sylib mpd $.

    $( There is exactly one value of a function.  (Contributed by NM,
       3-Aug-1994.) $)
    funeu2 $p |- ( ( Fun F /\ <. A , B >. e. F ) -> E! y <. A , y >. e. F ) $=
      cA cB cop cF wcel cF wfun cA cB cF wbr cA vy cv cop cF wcel vy weu cA cB
      cF df-br cF wfun cA cB cF wbr wa cA vy cv cF wbr vy weu cA vy cv cop cF
      wcel vy weu vy cA cB cF funeu cA vy cv cF wbr cA vy cv cop cF wcel vy cA
      vy cv cF df-br eubii sylib sylan2br $.
  $}

  ${
    $d x y A $.
    $( Alternate definition of a function.  One possibility for the definition
       of a function in [Enderton] p. 42.  (Enderton's definition is ambiguous
       because "there is only one" could mean either "there is at most one" or
       "there is exactly one."  However, ~ dffun8 shows that it doesn't matter
       which meaning we pick.)  (Contributed by NM, 4-Nov-2002.) $)
    dffun7 $p |- ( Fun A <-> ( Rel A /\ A. x e. dom A E* y x A y ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vy wmo vx wal wa cA wrel vx cv vy cv
      cA wbr vy wmo vx cA cdm wral wa vx vy cA dffun6 vx cv vy cv cA wbr vy wmo
      vx wal vx cv vy cv cA wbr vy wmo vx cA cdm wral cA wrel vx cv vy cv cA
      wbr vy wmo vx wal vx cv cA cdm wcel vx cv vy cv cA wbr vy wmo wi vx wal
      vx cv vy cv cA wbr vy wmo vx cA cdm wral vx cv vy cv cA wbr vy wmo vx cv
      cA cdm wcel vx cv vy cv cA wbr vy wmo wi vx vx cv vy cv cA wbr vy wmo vx
      cv vy cv cA wbr vy wex vx cv vy cv cA wbr vy wmo wi vx cv cA cdm wcel vx
      cv vy cv cA wbr vy wmo wi vx cv vy cv cA wbr vy moabs vx cv cA cdm wcel
      vx cv vy cv cA wbr vy wex vx cv vy cv cA wbr vy wmo vy vx cv cA vx vex
      eldm imbi1i bitr4i albii vx cv vy cv cA wbr vy wmo vx cA cdm df-ral
      bitr4i anbi2i bitri $.

    $( Alternate definition of a function.  One possibility for the definition
       of a function in [Enderton] p. 42.  Compare ~ dffun7 .  (Contributed by
       NM, 4-Nov-2002.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    dffun8 $p |- ( Fun A <-> ( Rel A /\ A. x e. dom A E! y x A y ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vy wmo vx cA cdm wral wa cA wrel vx cv
      vy cv cA wbr vy weu vx cA cdm wral wa vx vy cA dffun7 vx cv vy cv cA wbr
      vy wmo vx cA cdm wral vx cv vy cv cA wbr vy weu vx cA cdm wral cA wrel vx
      cv vy cv cA wbr vy wmo vx cv vy cv cA wbr vy weu vx cA cdm vx cv vy cv cA
      wbr vy wmo vx cv vy cv cA wbr vy wex vx cv vy cv cA wbr vy weu wi vx cv
      cA cdm wcel vx cv vy cv cA wbr vy weu vx cv vy cv cA wbr vy df-mo vx cv
      cA cdm wcel vx cv vy cv cA wbr vy wex vx cv vy cv cA wbr vy wex vx cv vy
      cv cA wbr vy weu wi vx cv vy cv cA wbr vy weu wb vy vx cv cA vx vex eldm
      vx cv vy cv cA wbr vy wex vx cv vy cv cA wbr vy weu pm5.5 sylbi syl5bb
      ralbiia anbi2i bitri $.

    $( Alternate definition of a function.  (Contributed by NM, 28-Mar-2007.)
       (Revised by NM, 16-Jun-2017.) $)
    dffun9 $p |- ( Fun A <->
                 ( Rel A /\ A. x e. dom A E* y e. ran A x A y ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vy wmo vx cA cdm wral wa cA wrel vx cv
      vy cv cA wbr vy cA crn wrmo vx cA cdm wral wa vx vy cA dffun7 vx cv vy cv
      cA wbr vy wmo vx cA cdm wral vx cv vy cv cA wbr vy cA crn wrmo vx cA cdm
      wral cA wrel vx cv vy cv cA wbr vy wmo vx cv vy cv cA wbr vy cA crn wrmo
      vx cA cdm vx cv vy cv cA wbr vy wmo vy cv cA crn wcel vx cv vy cv cA wbr
      wa vy wmo vx cv vy cv cA wbr vy cA crn wrmo vx cv vy cv cA wbr vy cv cA
      crn wcel vx cv vy cv cA wbr wa vy vx cv vy cv cA wbr vy cv cA crn wcel vx
      cv vy cv cA vx vex vy vex brelrn pm4.71ri mobii vx cv vy cv cA wbr vy cA
      crn df-rmo bitr4i ralbii anbi2i bitri $.
  $}

  $( An equivalence for the function predicate.  (Contributed by NM,
     13-Aug-2004.) $)
  funfn $p |- ( Fun A <-> A Fn dom A ) $=
    cA wfun cA wfun cA cdm cA cdm wceq wa cA cA cdm wfn cA cdm cA cdm wceq cA
    wfun cA cdm eqid biantru cA cA cdm df-fn bitr4i $.

  $( The identity relation is a function.  Part of Theorem 10.4 of [Quine]
     p. 65.  (Contributed by NM, 30-Apr-1998.) $)
  funi $p |- Fun _I $=
    cid wfun cid wrel cid cid ccnv ccom cid wss reli cid cid ccnv ccom cid cid
    cid ccnv ccom cid ccnv cid cid ccnv wrel cid cid ccnv ccom cid ccnv wceq
    cid relcnv cid ccnv coi2 ax-mp cnvi eqtri eqimssi cid df-fun mpbir2an $.

  $( The universe is not a function.  (Contributed by Raph Levien,
     27-Jan-2004.) $)
  nfunv $p |- -. Fun _V $=
    cvv wfun cvv wrel cvv wrel c0 cvv cvv cxp wcel cvv cvv 0nelxp cvv wrel c0
    cvv wcel c0 cvv cvv cxp wcel 0ex cvv wrel cvv cvv cvv cxp c0 cvv wrel cvv
    cvv cvv cxp wss cvv df-rel biimpi sseld mpi mto cvv funrel mto $.

  ${
    $d t u v w x y z A $.  $d t u v w x y z B $.
    $( A Kuratowski ordered pair is a function only if its components are
       equal.  (Contributed by NM, 5-Jun-2008.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    funopg $p |- ( ( A e. V /\ B e. W /\ Fun <. A , B >. ) -> A = B ) $=
      cA cV wcel cB cW wcel cA cB cop wfun cA cB wceq vu cv vt cv cop wfun vu
      cv vt cv wceq wi cA vt cv cop wfun cA vt cv wceq wi cA cB cop wfun cA cB
      wceq wi vu vt cA cB cV cW vu cv cA wceq vu cv vt cv cop wfun cA vt cv cop
      wfun vu cv vt cv wceq cA vt cv wceq vu cv cA wceq vu cv vt cv cop cA vt
      cv cop vu cv cA vt cv opeq1 funeqd vu cv cA vt cv eqeq1 imbi12d vt cv cB
      wceq cA vt cv cop wfun cA cB cop wfun cA vt cv wceq cA cB wceq vt cv cB
      wceq cA vt cv cop cA cB cop vt cv cB cA opeq2 funeqd vt cv cB cA eqeq2
      imbi12d vu cv vt cv cop wfun vu cv vx cv csn wceq vt cv vx cv vy cv cpr
      wceq wa vy wex vx wex vu cv vt cv wceq vu cv vt cv cop wfun vu cv vt cv
      cop wrel vu cv vx cv csn wceq vt cv vx cv vy cv cpr wceq wa vy wex vx wex
      vu cv vt cv cop funrel vx vy vu cv vt cv vu vex vt vex relop sylib vu cv
      vt cv cop wfun vu cv vx cv csn wceq vt cv vx cv vy cv cpr wceq wa vu cv
      vt cv wceq vx vy vu cv vt cv cop wfun vu cv vx cv csn wceq vt cv vx cv vy
      cv cpr wceq wa vx cv vy cv wceq vu cv vt cv wceq vu cv vx cv csn wceq vt
      cv vx cv vy cv cpr wceq wa vu cv vt cv cop vx cv vx cv cop vx cv vy cv
      cop cpr wceq vu cv vt cv cop wfun vx cv vy cv wceq vu cv vx cv csn wceq
      vt cv vx cv vy cv cpr wceq wa vu cv vt cv cop vx cv csn vx cv vy cv cpr
      cop wceq vu cv vt cv cop vx cv vx cv cop vx cv vy cv cop cpr wceq vu cv
      vt cv vx cv csn vx cv vy cv cpr vu vex vt vex opth vx cv csn vx cv vy cv
      cpr cop vx cv vx cv cop vx cv vy cv cop cpr vu cv vt cv cop vx cv vx cv
      cop vx cv csn vx cv vy cv cpr cpr cpr vx cv csn csn vx cv csn vx cv vy cv
      cpr cpr cpr vx cv vx cv cop vx cv vy cv cop cpr vx cv csn vx cv vy cv cpr
      cop vx cv vx cv cop vx cv csn csn vx cv csn vx cv vy cv cpr cpr vx cv vx
      vex opid preq1i vx cv vy cv cop vx cv csn vx cv vy cv cpr cpr vx cv vx cv
      cop vx cv vy cv vx vex vy vex dfop preq2i vx cv csn vx cv vy cv cpr vx cv
      snex vx vy zfpair2 dfop 3eqtr4ri eqeq2i bitr3i vu cv vt cv cop wfun vz cv
      vw cv cop vu cv vt cv cop wcel vz cv vv cv cop vu cv vt cv cop wcel wa vw
      cv vv cv wceq wi vv wal vw wal vz wal vu cv vt cv cop vx cv vx cv cop vx
      cv vy cv cop cpr wceq vx cv vx cv cop vu cv vt cv cop wcel vx cv vy cv
      cop vu cv vt cv cop wcel wa vx cv vy cv wceq vu cv vt cv cop wfun vu cv
      vt cv cop wrel vz cv vw cv cop vu cv vt cv cop wcel vz cv vv cv cop vu cv
      vt cv cop wcel wa vw cv vv cv wceq wi vv wal vw wal vz wal vz vw vv vu cv
      vt cv cop dffun4 simprbi vu cv vt cv cop vx cv vx cv cop vx cv vy cv cop
      cpr wceq vx cv vx cv cop vu cv vt cv cop wcel vx cv vy cv cop vu cv vt cv
      cop wcel vu cv vt cv cop vx cv vx cv cop vx cv vy cv cop cpr wceq vx cv
      vx cv cop vu cv vt cv cop wcel vx cv vx cv cop vx cv vx cv cop vx cv vy
      cv cop cpr wcel vx cv vx cv cop vx cv vy cv cop vx cv vx cv opex prid1 vu
      cv vt cv cop vx cv vx cv cop vx cv vy cv cop cpr vx cv vx cv cop eleq2
      mpbiri vu cv vt cv cop vx cv vx cv cop vx cv vy cv cop cpr wceq vx cv vy
      cv cop vu cv vt cv cop wcel vx cv vy cv cop vx cv vx cv cop vx cv vy cv
      cop cpr wcel vx cv vx cv cop vx cv vy cv cop vx cv vy cv opex prid2 vu cv
      vt cv cop vx cv vx cv cop vx cv vy cv cop cpr vx cv vy cv cop eleq2
      mpbiri jca vx cv cvv wcel vx cv cvv wcel vy cv cvv wcel vz cv vw cv cop
      vu cv vt cv cop wcel vz cv vv cv cop vu cv vt cv cop wcel wa vw cv vv cv
      wceq wi vv wal vw wal vz wal vx cv vx cv cop vu cv vt cv cop wcel vx cv
      vy cv cop vu cv vt cv cop wcel wa vx cv vy cv wceq wi wi vx vex vx vex vy
      vex vz cv vw cv cop vu cv vt cv cop wcel vz cv vv cv cop vu cv vt cv cop
      wcel wa vw cv vv cv wceq wi vx cv vx cv cop vu cv vt cv cop wcel vx cv vy
      cv cop vu cv vt cv cop wcel wa vx cv vy cv wceq wi vz vw vv vx cv vx cv
      vy cv cvv cvv cvv vz cv vx cv wceq vw cv vx cv wceq vv cv vy cv wceq w3a
      vz cv vw cv cop vu cv vt cv cop wcel vz cv vv cv cop vu cv vt cv cop wcel
      wa vx cv vx cv cop vu cv vt cv cop wcel vx cv vy cv cop vu cv vt cv cop
      wcel wa vw cv vv cv wceq vx cv vy cv wceq vz cv vx cv wceq vw cv vx cv
      wceq vv cv vy cv wceq w3a vz cv vw cv cop vu cv vt cv cop wcel vx cv vx
      cv cop vu cv vt cv cop wcel vz cv vv cv cop vu cv vt cv cop wcel vx cv vy
      cv cop vu cv vt cv cop wcel vz cv vx cv wceq vw cv vx cv wceq vv cv vy cv
      wceq w3a vz cv vw cv cop vx cv vx cv cop vu cv vt cv cop vz cv vx cv wceq
      vw cv vx cv wceq vz cv vw cv cop vx cv vx cv cop wceq vv cv vy cv wceq vz
      cv vw cv vx cv vx cv opeq12 3adant3 eleq1d vz cv vx cv wceq vw cv vx cv
      wceq vv cv vy cv wceq w3a vz cv vv cv cop vx cv vy cv cop vu cv vt cv cop
      vz cv vx cv wceq vv cv vy cv wceq vz cv vv cv cop vx cv vy cv cop wceq vw
      cv vx cv wceq vz cv vv cv vx cv vy cv opeq12 3adant2 eleq1d anbi12d vw cv
      vx cv wceq vv cv vy cv wceq vw cv vv cv wceq vx cv vy cv wceq wb vz cv vx
      cv wceq vw cv vx cv vv cv vy cv eqeq12 3adant1 imbi12d spc3gv mp3an
      syl2im syl5bi vu cv vx cv csn wceq vt cv vx cv vy cv cpr wceq vx cv vy cv
      wceq vu cv vt cv wceq wi vx cv vy cv wceq vt cv vx cv vy cv cpr wceq vu
      cv vx cv csn wceq vu cv vt cv wceq vx cv vy cv wceq vt cv vx cv vy cv cpr
      wceq vt cv vx cv csn wceq vu cv vx cv csn wceq vu cv vt cv wceq wi vx cv
      vy cv wceq vx cv vy cv cpr vx cv csn vt cv vx cv vy cv wceq vx cv csn vx
      cv vx cv cpr vx cv vy cv cpr vx cv dfsn2 vx cv vy cv vx cv preq2 syl5req
      eqeq2d vu cv vx cv csn wceq vt cv vx cv csn wceq vu cv vt cv wceq vu cv
      vt cv vx cv csn eqtr3 expcom syl6bi com13 imp sylcom exlimdvv mpd vtocl2g
      3impia $.
  $}


  ${
    $d x y z $.  $d z ph $.
    $( A class of ordered pairs is a function when there is at most one second
       member for each pair.  (Contributed by NM, 16-May-1995.) $)
    funopab $p |- ( Fun { <. x , y >. | ph } <-> A. x E* y ph ) $=
      wph vx vy copab wfun vx cv vy cv wph vx vy copab wbr vy wmo vx wal wph vy
      wmo vx wal wph vx vy copab wfun wph vx vy copab wrel vx cv vy cv wph vx
      vy copab wbr vy wmo vx wal wph vx vy relopab vx vy wph vx vy copab wph vx
      vy nfopab1 wph vx vy nfopab2 dffun6f mpbiran vx cv vy cv wph vx vy copab
      wbr vy wmo wph vy wmo vx vx cv vy cv wph vx vy copab wbr wph vy vx cv vy
      cv wph vx vy copab wbr vx cv vy cv cop wph vx vy copab wcel wph vx cv vy
      cv wph vx vy copab df-br wph vx vy opabid bitri mobii albii bitri $.
  $}

  ${
    $d x y $.  $d y A $.
    $( A class of ordered pairs of values is a function.  (Contributed by NM,
       14-Nov-1995.) $)
    funopabeq $p |- Fun { <. x , y >. | y = A } $=
      vy cv cA wceq vx vy copab wfun vy cv cA wceq vy wmo vx vy cv cA wceq vx
      vy funopab vy cA moeq mpgbir $.

    $( A class of ordered pairs of values in the form used by ~ df-mpt is a
       function.  (Contributed by NM, 17-Feb-2013.) $)
    funopab4 $p |- Fun { <. x , y >. | ( ph /\ y = A ) } $=
      wph vy cv cA wceq wa vx vy copab vy cv cA wceq vx vy copab wss vy cv cA
      wceq vx vy copab wfun wph vy cv cA wceq wa vx vy copab wfun wph vy cv cA
      wceq wa vy cv cA wceq vx vy wph vy cv cA wceq simpr ssopab2i vx vy cA
      funopabeq wph vy cv cA wceq wa vx vy copab vy cv cA wceq vx vy copab
      funss mp2 $.
  $}

  ${
    $d A y $.  $d B y $.  $d x y $.
    $( A function in maps-to notation is a function.  (Contributed by Mario
       Carneiro, 13-Jan-2013.) $)
    funmpt $p |- Fun ( x e. A |-> B ) $=
      vx cA cB cmpt wfun vx cv cA wcel vy cv cB wceq wa vx vy copab wfun vx cv
      cA wcel vx vy cB funopab4 vx cA cB cmpt vx cv cA wcel vy cv cB wceq wa vx
      vy copab vx vy cA cB df-mpt funeqi mpbir $.
  $}

  ${
    funmpt2.1 $e |- F = ( x e. A |-> B ) $.
    $( Functionality of a class given by a "maps to" notation.  (Contributed by
       FL, 17-Feb-2008.)  (Revised by Mario Carneiro, 31-May-2014.) $)
    funmpt2 $p |- Fun F $=
      cF wfun vx cA cB cmpt wfun vx cA cB funmpt cF vx cA cB cmpt funmpt2.1
      funeqi mpbir $.
  $}

  ${
    $d x y z F $.  $d x y z G $.
    $( The composition of two functions is a function.  Exercise 29 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 26-Jan-1997.)  (Proof
       shortened by Andrew Salmon, 17-Sep-2011.) $)
    funco $p |- ( ( Fun F /\ Fun G ) -> Fun ( F o. G ) ) $=
      cF wfun cG wfun wa vx cv vz cv cG wbr vz cv vy cv cF wbr wa vz wex vx vy
      copab wfun cF cG ccom wfun cF wfun cG wfun wa vx cv vz cv cG wbr vz cv vy
      cv cF wbr wa vz wex vy wmo vx wal vx cv vz cv cG wbr vz cv vy cv cF wbr
      wa vz wex vx vy copab wfun cF wfun cG wfun wa vx cv vz cv cG wbr vz cv vy
      cv cF wbr wa vz wex vy wmo vx cG wfun vx cv vz cv cG wbr vz wmo vz cv vy
      cv cF wbr vy wmo vz wal vx cv vz cv cG wbr vz cv vy cv cF wbr wa vz wex
      vy wmo cF wfun vz vx cv cG funmo cF wfun vz cv vy cv cF wbr vy wmo vz vy
      vz cv cF funmo alrimiv vx cv vz cv cG wbr vz cv vy cv cF wbr vz vy
      moexexv syl2anr alrimiv vx cv vz cv cG wbr vz cv vy cv cF wbr wa vz wex
      vx vy funopab sylibr cF cG ccom vx cv vz cv cG wbr vz cv vy cv cF wbr wa
      vz wex vx vy copab vx vy vz cF cG df-co funeqi sylibr $.
  $}

  $( A restriction of a function is a function.  Compare Exercise 18 of
     [TakeutiZaring] p. 25.  (Contributed by NM, 16-Aug-1994.) $)
  funres $p |- ( Fun F -> Fun ( F |` A ) ) $=
    cF cA cres cF wss cF wfun cF cA cres wfun wi cF cA resss cF cA cres cF
    funss ax-mp $.

  ${
    $d x y F $.  $d x y G $.  $d x y A $.
    $( The restriction of a function to the domain of a subclass equals the
       subclass.  (Contributed by NM, 15-Aug-1994.) $)
    funssres $p |- ( ( Fun F /\ G C_ F ) -> ( F |` dom G ) = G ) $=
      cF wfun cG cF wss wa cF cG cdm cres cG wceq vx cv vy cv cop cF cG cdm
      cres wcel vx cv vy cv cop cG wcel wb vy wal vx wal cF wfun cG cF wss wa
      vx cv vy cv cop cF cG cdm cres wcel vx cv vy cv cop cG wcel wb vx vy cF
      wfun cG cF wss wa vx cv vy cv cop cG wcel vx cv vy cv cop cF wcel vx cv
      cG cdm wcel wa vx cv vy cv cop cF cG cdm cres wcel cF wfun cG cF wss wa
      vx cv vy cv cop cG wcel vx cv vy cv cop cF wcel vx cv cG cdm wcel wa cG
      cF wss vx cv vy cv cop cG wcel vx cv vy cv cop cF wcel vx cv cG cdm wcel
      wa wi cF wfun cG cF wss vx cv vy cv cop cG wcel vx cv vy cv cop cF wcel
      vx cv cG cdm wcel cG cF vx cv vy cv cop ssel vx cv vy cv cop cG wcel vx
      cv cG cdm wcel wi cG cF wss vx cv vy cv cG vx vex vy vex opeldm a1i jcad
      adantl cF wfun cG cF wss wa vx cv vy cv cop cF wcel vx cv cG cdm wcel vx
      cv vy cv cop cG wcel cF wfun cG cF wss wa vx cv vy cv cop cF wcel vx cv
      cG cdm wcel vx cv vy cv cop cG wcel wi cF wfun cG cF wss wa vx cv vy cv
      cop cF wcel vx cv cG cdm wcel vx cv vy cv cop cF wcel vx cv vy cv cop cG
      wcel cF wfun cG cF wss vx cv vy cv cop cF wcel vx cv cG cdm wcel vx cv vy
      cv cop cF wcel vx cv vy cv cop cG wcel wi wi wi cF wfun vx cv vy cv cop
      cF wcel cG cF wss vx cv cG cdm wcel vx cv vy cv cop cF wcel vx cv vy cv
      cop cG wcel wi wi cF wfun vx cv vy cv cop cF wcel cG cF wss vx cv cG cdm
      wcel vx cv vy cv cop cF wcel vx cv vy cv cop cG wcel wi cF wfun vx cv vy
      cv cop cF wcel wa vx cv vy cv cop cF wcel vy weu vx cv vy cv cop cF wcel
      vx cv vy cv cop cG wcel wa vy wex vx cv vy cv cop cF wcel vx cv vy cv cop
      cG wcel wi cG cF wss vx cv cG cdm wcel wa vy vx cv vy cv cF funeu2 cG cF
      wss vx cv cG cdm wcel vx cv vy cv cop cF wcel vx cv vy cv cop cG wcel wa
      vy wex vx cv cG cdm wcel vx cv vy cv cop cG wcel vy wex cG cF wss vx cv
      vy cv cop cF wcel vx cv vy cv cop cG wcel wa vy wex vy vx cv cG vx vex
      eldm2 cG cF wss vx cv vy cv cop cG wcel vx cv vy cv cop cF wcel vx cv vy
      cv cop cG wcel wa vy cG cF wss vx cv vy cv cop cG wcel vx cv vy cv cop cF
      wcel cG cF vx cv vy cv cop ssel ancrd eximdv syl5bi imp vx cv vy cv cop
      cF wcel vx cv vy cv cop cG wcel vy eupick syl2an exp43 com23 imp com34
      pm2.43d imp3a impbid vx cv vy cv cF cG cdm vy vex opelres syl6rbbr
      alrimivv cF wfun cG cF wss wa cF cG cdm cres wrel cG wrel cF cG cdm cres
      cG wceq vx cv vy cv cop cF cG cdm cres wcel vx cv vy cv cop cG wcel wb vy
      wal vx wal wb cF cG cdm relres cF wfun cF wrel cG cF wss cG wrel cF
      funrel cG cF relss mpan9 vx vy cF cG cdm cres cG eqrel sylancr mpbird $.
  $}

  $( Equality of restrictions of a function and a subclass.  (Contributed by
     NM, 16-Aug-1994.) $)
  fun2ssres $p |- ( ( Fun F /\ G C_ F /\ A C_ dom G ) ->
                  ( F |` A ) = ( G |` A ) ) $=
    cF wfun cG cF wss cA cG cdm wss cF cA cres cG cA cres wceq cA cG cdm wss cF
    wfun cG cF wss wa cF cA cres cF cG cdm cres cA cres cG cA cres cA cG cdm
    wss cF cG cdm cres cA cres cF cA cres cF cA cG cdm resabs1 eqcomd cF wfun
    cG cF wss wa cF cG cdm cres cG cA cF cG funssres reseq1d sylan9eqr 3impa $.

  ${
    $d x y z F $.  $d x y z G $.
    $( The union of functions with disjoint domains is a function.  Theorem 4.6
       of [Monk1] p. 43.  (Contributed by NM, 12-Aug-1994.) $)
    funun $p |- ( ( ( Fun F /\ Fun G ) /\ ( dom F i^i dom G ) = (/) ) ->
                Fun ( F u. G ) ) $=
      cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cF cG cun wrel vx cv vy
      cv cop cF cG cun wcel vx cv vz cv cop cF cG cun wcel wa vy cv vz cv wceq
      wi vz wal vy wal vx wal cF cG cun wfun cF wfun cG wfun wa cF cG cun wrel
      cF cdm cG cdm cin c0 wceq cF wfun cG wfun wa cF wrel cG wrel wa cF cG cun
      wrel cF wfun cF wrel cG wfun cG wrel cF funrel cG funrel anim12i cF cG
      relun sylibr adantr cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa vx cv
      vy cv cop cF cG cun wcel vx cv vz cv cop cF cG cun wcel wa vy cv vz cv
      wceq wi vz wal vx vy cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa vx
      cv vy cv cop cF cG cun wcel vx cv vz cv cop cF cG cun wcel wa vy cv vz cv
      wceq wi vz cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa vx cv vy cv
      cop cF cG cun wcel vx cv vz cv cop cF cG cun wcel wa vx cv vy cv cop cF
      wcel vx cv vz cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv vz cv cop
      cG wcel wa wo vy cv vz cv wceq vx cv vy cv cop cF cG cun wcel vx cv vz cv
      cop cF cG cun wcel wa vx cv vy cv cop cF wcel vx cv vz cv cop cF wcel wa
      vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa wo vx cv vy cv cop cG
      wcel vx cv vz cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv vz cv cop
      cG wcel wa wo wo cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa vx cv vy
      cv cop cF wcel vx cv vz cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv
      vz cv cop cG wcel wa wo vx cv vy cv cop cF cG cun wcel vx cv vz cv cop cF
      cG cun wcel wa vx cv vy cv cop cF wcel vx cv vy cv cop cG wcel wo vx cv
      vz cv cop cF wcel vx cv vz cv cop cG wcel wo wa vx cv vy cv cop cF wcel
      vx cv vz cv cop cF wcel wa vx cv vy cv cop cF wcel vx cv vz cv cop cG
      wcel wa wo vx cv vy cv cop cG wcel vx cv vz cv cop cF wcel wa vx cv vy cv
      cop cG wcel vx cv vz cv cop cG wcel wa wo wo vx cv vy cv cop cF cG cun
      wcel vx cv vy cv cop cF wcel vx cv vy cv cop cG wcel wo vx cv vz cv cop
      cF cG cun wcel vx cv vz cv cop cF wcel vx cv vz cv cop cG wcel wo vx cv
      vy cv cop cF cG elun vx cv vz cv cop cF cG elun anbi12i vx cv vy cv cop
      cF wcel vx cv vy cv cop cG wcel vx cv vz cv cop cF wcel vx cv vz cv cop
      cG wcel anddi bitri cF cdm cG cdm cin c0 wceq vx cv vy cv cop cF wcel vx
      cv vz cv cop cF wcel wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel
      wa wo vx cv vy cv cop cG wcel vx cv vz cv cop cF wcel wa vx cv vy cv cop
      cG wcel vx cv vz cv cop cG wcel wa wo wo vx cv vy cv cop cF wcel vx cv vz
      cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa wo
      wi cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq vx cv vy cv cop cF wcel
      vx cv vz cv cop cF wcel wa vx cv vy cv cop cF wcel vx cv vz cv cop cG
      wcel wa wo vx cv vy cv cop cF wcel vx cv vz cv cop cF wcel wa vx cv vy cv
      cop cG wcel vx cv vz cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv vz
      cv cop cG wcel wa wo vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa
      cF cdm cG cdm cin c0 wceq vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel
      wa wn vx cv vy cv cop cF wcel vx cv vz cv cop cF wcel wa vx cv vy cv cop
      cF wcel vx cv vz cv cop cG wcel wa wo vx cv vy cv cop cF wcel vx cv vz cv
      cop cF wcel wa wi cF cdm cG cdm cin c0 wceq vx cv cF cdm wcel vx cv cG
      cdm wcel wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa cF cdm cG
      cdm cin c0 wceq vx cv cF cdm wcel vx cv cG cdm wcel wn wi vx cv cF cdm
      wcel vx cv cG cdm wcel wa wn cF cdm cG cdm cin c0 wceq vx cv cF cdm wcel
      vx cv cG cdm wcel wn wi vx cF cdm cG cdm cin c0 wceq vx cv cF cdm wcel vx
      cv cG cdm wcel wn wi vx wal vx cF cdm cG cdm disj1 biimpi 19.21bi vx cv
      cF cdm wcel vx cv cG cdm wcel imnan sylib vx cv vy cv cop cF wcel vx cv
      cF cdm wcel vx cv vz cv cop cG wcel vx cv cG cdm wcel vx cv vy cv cF vx
      vex vy vex opeldm vx cv vz cv cG vx vex vz vex opeldm anim12i nsyl vx cv
      vy cv cop cF wcel vx cv vz cv cop cG wcel wa vx cv vy cv cop cF wcel vx
      cv vz cv cop cF wcel wa orel2 syl cF cdm cG cdm cin c0 wceq vx cv vy cv
      cop cG wcel vx cv vz cv cop cF wcel wa wn vx cv vy cv cop cG wcel vx cv
      vz cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa
      wo vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa wi cF cdm cG cdm
      cin c0 wceq vx cv cG cdm wcel vx cv cF cdm wcel wa vx cv vy cv cop cG
      wcel vx cv vz cv cop cF wcel wa cF cdm cG cdm cin c0 wceq vx cv cG cdm
      wcel vx cv cF cdm wcel wn wi vx cv cG cdm wcel vx cv cF cdm wcel wa wn cF
      cdm cG cdm cin c0 wceq vx cv cF cdm wcel vx cv cG cdm wcel cF cdm cG cdm
      cin c0 wceq vx cv cF cdm wcel vx cv cG cdm wcel wn wi vx cF cdm cG cdm
      cin c0 wceq vx cv cF cdm wcel vx cv cG cdm wcel wn wi vx wal vx cF cdm cG
      cdm disj1 biimpi 19.21bi con2d vx cv cG cdm wcel vx cv cF cdm wcel imnan
      sylib vx cv vy cv cop cG wcel vx cv cG cdm wcel vx cv vz cv cop cF wcel
      vx cv cF cdm wcel vx cv vy cv cG vx vex vy vex opeldm vx cv vz cv cF vx
      vex vz vex opeldm anim12i nsyl vx cv vy cv cop cG wcel vx cv vz cv cop cF
      wcel wa vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa orel1 syl
      orim12d adantl syl5bi cF wfun cG wfun wa vx cv vy cv cop cF wcel vx cv vz
      cv cop cF wcel wa vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa wo
      vy cv vz cv wceq wi cF cdm cG cdm cin c0 wceq cF wfun vx cv vy cv cop cF
      wcel vx cv vz cv cop cF wcel wa vy cv vz cv wceq cG wfun vx cv vy cv cop
      cG wcel vx cv vz cv cop cG wcel wa cF wfun vx cv vy cv cop cF wcel vx cv
      vz cv cop cF wcel wa vy cv vz cv wceq wi vy vz cF wfun vx cv vy cv cop cF
      wcel vx cv vz cv cop cF wcel wa vy cv vz cv wceq wi vz wal vy wal vx cF
      wfun cF wrel vx cv vy cv cop cF wcel vx cv vz cv cop cF wcel wa vy cv vz
      cv wceq wi vz wal vy wal vx wal vx vy vz cF dffun4 simprbi 19.21bi
      19.21bbi cG wfun vx cv vy cv cop cG wcel vx cv vz cv cop cG wcel wa vy cv
      vz cv wceq wi vy vz cG wfun vx cv vy cv cop cG wcel vx cv vz cv cop cG
      wcel wa vy cv vz cv wceq wi vz wal vy wal vx cG wfun cG wrel vx cv vy cv
      cop cG wcel vx cv vz cv cop cG wcel wa vy cv vz cv wceq wi vz wal vy wal
      vx wal vx vy vz cG dffun4 simprbi 19.21bi 19.21bbi jaao adantr syld
      alrimiv alrimivv vx vy vz cF cG cun dffun4 sylanbrc $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The converse singleton of an ordered pair is a function.  This is
       equivalent to ~ funsn via ~ cnvsn , but stating it this way allows us to
       skip the sethood assumptions on ` A ` and ` B ` .  (Contributed by NM,
       30-Apr-2015.) $)
    funcnvsn $p |- Fun `' { <. A , B >. } $=
      cA cB cop csn ccnv wfun cA cB cop csn ccnv wrel vx cv vy cv cA cB cop csn
      ccnv wbr vy wmo vx wal cA cB cop csn relcnv vx cv vy cv cA cB cop csn
      ccnv wbr vy wmo vx vy cv cA wceq vy wmo vx cv vy cv cA cB cop csn ccnv
      wbr vy wmo vy cA moeq vx cv vy cv cA cB cop csn ccnv wbr vy cv cA wceq vy
      vx cv vy cv cA cB cop csn ccnv wbr vy cv vx cv cop cA cB cop csn wcel vy
      cv cA wceq vx cv vy cv cA cB cop csn ccnv wbr vy cv vx cv cA cB cop csn
      wbr vy cv vx cv cop cA cB cop csn wcel vx cv vy cv cA cB cop csn vx vex
      vy vex brcnv vy cv vx cv cA cB cop csn df-br bitri vy cv vx cv cop cA cB
      cop csn wcel vy cv vx cv cop cA cB cop wceq vy cv cA wceq vy cv vx cv cop
      cA cB cop elsni vy cv vx cv cA cB vy vex vx vex opth1 syl sylbi moimi
      ax-mp ax-gen vx vy cA cB cop csn ccnv dffun6 mpbir2an $.

    $( A singleton of an ordered pair is a function.  Theorem 10.5 of [Quine]
       p. 65.  (Contributed by NM, 28-Jun-2011.) $)
    funsng $p |- ( ( A e. V /\ B e. W ) -> Fun { <. A , B >. } ) $=
      cA cV wcel cB cW wcel wa cB cA cop csn ccnv wfun cA cB cop csn wfun cB cA
      funcnvsn cA cV wcel cB cW wcel wa cB cA cop csn ccnv cA cB cop csn cB cW
      wcel cA cV wcel cB cA cop csn ccnv cA cB cop csn wceq cB cA cW cV cnvsng
      ancoms funeqd mpbii $.

    $( Functionality and domain of the singleton of an ordered pair.
       (Contributed by Mario Carneiro, 30-Apr-2015.) $)
    fnsng $p |- ( ( A e. V /\ B e. W ) -> { <. A , B >. } Fn { A } ) $=
      cA cV wcel cB cW wcel wa cA cB cop csn wfun cA cB cop csn cdm cA csn wceq
      cA cB cop csn cA csn wfn cA cB cV cW funsng cB cW wcel cA cB cop csn cdm
      cA csn wceq cA cV wcel cA cB cW dmsnopg adantl cA cB cop csn cA csn df-fn
      sylanbrc $.

    funsn.1 $e |- A e. _V $.
    funsn.2 $e |- B e. _V $.
    $( A singleton of an ordered pair is a function.  Theorem 10.5 of [Quine]
       p. 65.  (Contributed by NM, 12-Aug-1994.) $)
    funsn $p |- Fun { <. A , B >. } $=
      cA cvv wcel cB cvv wcel cA cB cop csn wfun funsn.1 funsn.2 cA cB cvv cvv
      funsng mp2an $.
  $}

  $( A set of two pairs is a function if their first members are different.
     (Contributed by FL, 26-Jun-2011.) $)
  funprg $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) /\ A =/= B )
     -> Fun { <. A , C >. , <. B , D >. } ) $=
    cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel wa cA cB wne w3a cA cC cop
    csn cB cD cop csn cun wfun cA cC cop cB cD cop cpr wfun cA cV wcel cB cW
    wcel wa cC cX wcel cD cY wcel wa cA cB wne w3a cA cC cop csn wfun cB cD cop
    csn wfun cA cC cop csn cdm cB cD cop csn cdm cin c0 wceq cA cC cop csn cB
    cD cop csn cun wfun cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel wa cA cB
    wne w3a cA cV wcel cC cX wcel cA cC cop csn wfun cA cV wcel cB cW wcel cC
    cX wcel cD cY wcel wa cA cB wne simp1l cA cV wcel cB cW wcel wa cC cX wcel
    cD cY wcel cA cB wne simp2l cA cC cV cX funsng syl2anc cA cV wcel cB cW
    wcel wa cC cX wcel cD cY wcel wa cA cB wne w3a cB cW wcel cD cY wcel cB cD
    cop csn wfun cA cV wcel cB cW wcel cC cX wcel cD cY wcel wa cA cB wne
    simp1r cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel cA cB wne simp2r cB
    cD cW cY funsng syl2anc cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel wa
    cA cB wne w3a cA cC cop csn cdm cB cD cop csn cdm cin cA csn cB csn cin c0
    cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel wa cA cB wne w3a cA cC cop
    csn cdm cA csn cB cD cop csn cdm cB csn cA cV wcel cB cW wcel wa cC cX wcel
    cD cY wcel wa cA cB wne w3a cC cX wcel cA cC cop csn cdm cA csn wceq cA cV
    wcel cB cW wcel wa cC cX wcel cD cY wcel cA cB wne simp2l cA cC cX dmsnopg
    syl cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel wa cA cB wne w3a cD cY
    wcel cB cD cop csn cdm cB csn wceq cA cV wcel cB cW wcel wa cC cX wcel cD
    cY wcel cA cB wne simp2r cB cD cY dmsnopg syl ineq12d cA cB wne cA cV wcel
    cB cW wcel wa cA csn cB csn cin c0 wceq cC cX wcel cD cY wcel wa cA cB
    disjsn2 3ad2ant3 eqtrd cA cC cop csn cB cD cop csn funun syl21anc cA cC cop
    cB cD cop cpr cA cC cop csn cB cD cop csn cun cA cC cop cB cD cop df-pr
    funeqi sylibr $.

  ${
    funpr.1 $e |- A e. _V $.
    funpr.2 $e |- B e. _V $.
    funpr.3 $e |- C e. _V $.
    funpr.4 $e |- D e. _V $.
    $( A function with a domain of two elements.  (Contributed by Jeff Madsen,
       20-Jun-2010.) $)
    funpr $p |- ( A =/= B -> Fun { <. A , C >. , <. B , D >. } ) $=
      cA cvv wcel cB cvv wcel wa cC cvv wcel cD cvv wcel wa cA cB wne cA cC cop
      cB cD cop cpr wfun cA cvv wcel cB cvv wcel funpr.1 funpr.2 pm3.2i cC cvv
      wcel cD cvv wcel funpr.3 funpr.4 pm3.2i cA cB cC cD cvv cvv cvv cvv
      funprg mp3an12 $.
  $}

  ${
    funtp.1 $e |- A e. _V $.
    funtp.2 $e |- B e. _V $.
    funtp.3 $e |- C e. _V $.
    funtp.4 $e |- D e. _V $.
    funtp.5 $e |- E e. _V $.
    funtp.6 $e |- F e. _V $.
    $( A function with a domain of three elements.  (Contributed by NM,
       14-Sep-2011.) $)
    funtp $p |- ( ( A =/= B /\ A =/= C /\ B =/= C )
                    -> Fun { <. A , D >. , <. B , E >. , <. C , F >. } ) $=
      cA cB wne cA cC wne cB cC wne w3a cA cD cop cB cE cop cpr cC cF cop csn
      cun wfun cA cD cop cB cE cop cC cF cop ctp wfun cA cB wne cA cC wne cB cC
      wne cA cD cop cB cE cop cpr cC cF cop csn cun wfun cA cB wne cA cD cop cB
      cE cop cpr wfun cC cF cop csn wfun wa cA cD cop cB cE cop cpr cdm cC cF
      cop csn cdm cin c0 wceq cA cD cop cB cE cop cpr cC cF cop csn cun wfun cA
      cC wne cB cC wne wa cA cB wne cA cD cop cB cE cop cpr wfun cC cF cop csn
      wfun cA cB cD cE funtp.1 funtp.2 funtp.4 funtp.5 funpr cC cF funtp.3
      funtp.6 funsn jctir cA cC wne cB cC wne wa cA cD cop cB cE cop cpr cdm cC
      cF cop csn cdm cin cA csn cB csn cun cC csn cin c0 cA cD cop cB cE cop
      cpr cdm cA csn cB csn cun cC cF cop csn cdm cC csn cA cD cop cB cE cop
      cpr cdm cA cB cpr cA csn cB csn cun cA cD cB cE funtp.4 funtp.5 dmprop cA
      cB df-pr eqtri cC cF funtp.6 dmsnop ineq12i cA cC wne cB cC wne wa cA csn
      cC csn cin c0 wceq cB csn cC csn cin c0 wceq wa cA csn cB csn cun cC csn
      cin c0 wceq cA cC wne cA csn cC csn cin c0 wceq cB cC wne cB csn cC csn
      cin c0 wceq cA cC disjsn2 cB cC disjsn2 anim12i cA csn cB csn cC csn
      undisj1 sylib syl5eq cA cD cop cB cE cop cpr cC cF cop csn funun syl2an
      3impb cA cD cop cB cE cop cC cF cop ctp cA cD cop cB cE cop cpr cC cF cop
      csn cun cA cD cop cB cE cop cC cF cop df-tp funeqi sylibr $.
  $}

  ${
    fnsn.1 $e |- A e. _V $.
    fnsn.2 $e |- B e. _V $.
    $( Functionality and domain of the singleton of an ordered pair.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    fnsn $p |- { <. A , B >. } Fn { A } $=
      cA cvv wcel cB cvv wcel cA cB cop csn cA csn wfn fnsn.1 fnsn.2 cA cB cvv
      cvv fnsng mp2an $.
  $}

  ${
    $( Domain of a function with a domain of two different values.
       (Contributed by FL, 26-Jun-2011.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    fnprg $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) /\ A =/= B )
         -> { <. A , C >. , <. B , D >. } Fn { A , B } ) $=
      cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel wa cA cB wne w3a cA cC cop
      cB cD cop cpr wfun cA cC cop cB cD cop cpr cdm cA cB cpr wceq cA cC cop
      cB cD cop cpr cA cB cpr wfn cA cB cC cD cV cW cX cY funprg cC cX wcel cD
      cY wcel wa cA cV wcel cB cW wcel wa cA cC cop cB cD cop cpr cdm cA cB cpr
      wceq cA cB wne cA cC cB cD cX cY dmpropg 3ad2ant2 cA cC cop cB cD cop cpr
      cA cB cpr df-fn sylanbrc $.
  $}

  ${
    fntp.1 $e |- A e. _V $.
    fntp.2 $e |- B e. _V $.
    fntp.3 $e |- C e. _V $.
    fntp.4 $e |- D e. _V $.
    fntp.5 $e |- E e. _V $.
    fntp.6 $e |- F e. _V $.
    $( A function with a domain of three elements.  (Contributed by NM,
       14-Sep-2011.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    fntp $p |- ( ( A =/= B /\ A =/= C /\ B =/= C )
          -> { <. A , D >. , <. B , E >. , <. C , F >. } Fn { A , B , C } ) $=
      cA cB wne cA cC wne cB cC wne w3a cA cD cop cB cE cop cC cF cop ctp wfun
      cA cD cop cB cE cop cC cF cop ctp cdm cA cB cC ctp wceq cA cD cop cB cE
      cop cC cF cop ctp cA cB cC ctp wfn cA cB cC cD cE cF fntp.1 fntp.2 fntp.3
      fntp.4 fntp.5 fntp.6 funtp cA cD cop cB cE cop cC cF cop ctp cdm cA cB cC
      ctp wceq cA cB wne cA cC wne cB cC wne w3a cA cD cB cE cC cF fntp.4
      fntp.5 fntp.6 dmtpop a1i cA cD cop cB cE cop cC cF cop ctp cA cB cC ctp
      df-fn sylanbrc $.
  $}

  $( The empty set is a function.  Theorem 10.3 of [Quine] p. 65.  (Contributed
     by NM, 7-Apr-1998.) $)
  fun0 $p |- Fun (/) $=
    c0 c0 c0 cop csn wss c0 c0 cop csn wfun c0 wfun c0 c0 cop csn 0ss c0 c0 0ex
    0ex funsn c0 c0 c0 cop csn funss mp2 $.

  $( The double converse of a function is a function.  (Contributed by NM,
     21-Sep-2004.) $)
  funcnvcnv $p |- ( Fun A -> Fun `' `' A ) $=
    cA ccnv ccnv cA wss cA wfun cA ccnv ccnv wfun wi cA cnvcnvss cA ccnv ccnv
    cA funss ax-mp $.

  ${
    $d f g x y z w v A $.  $d x y B $.  $d x y R $.
    $( A simpler equivalence for single-rooted (see ~ funcnv ).  (Contributed
       by NM, 9-Aug-2004.) $)
    funcnv2 $p |- ( Fun `' A <-> A. y E* x x A y ) $=
      cA ccnv wfun vy cv vx cv cA ccnv wbr vx wmo vy wal vx cv vy cv cA wbr vx
      wmo vy wal cA ccnv wfun cA ccnv wrel vy cv vx cv cA ccnv wbr vx wmo vy
      wal cA relcnv vy vx cA ccnv dffun6 mpbiran vy cv vx cv cA ccnv wbr vx wmo
      vx cv vy cv cA wbr vx wmo vy vy cv vx cv cA ccnv wbr vx cv vy cv cA wbr
      vx vy cv vx cv cA vy vex vx vex brcnv mobii albii bitri $.

    $( The converse of a class is a function iff the class is single-rooted,
       which means that for any ` y ` in the range of ` A ` there is at most
       one ` x ` such that ` x A y ` .  Definition of single-rooted in
       [Enderton] p. 43.  See ~ funcnv2 for a simpler version.  (Contributed by
       NM, 13-Aug-2004.) $)
    funcnv $p |- ( Fun `' A <-> A. y e. ran A E* x x A y ) $=
      vx cv vy cv cA wbr vx wmo vy wal vy cv cA crn wcel vx cv vy cv cA wbr vx
      wmo wi vy wal cA ccnv wfun vx cv vy cv cA wbr vx wmo vy cA crn wral vx cv
      vy cv cA wbr vx wmo vy cv cA crn wcel vx cv vy cv cA wbr vx wmo wi vy vx
      cv vy cv cA wbr vx wmo vy cv cA crn wcel vx cv vy cv cA wbr wa vx wmo vy
      cv cA crn wcel vx cv vy cv cA wbr vx wmo wi vx cv vy cv cA wbr vy cv cA
      crn wcel vx cv vy cv cA wbr wa vx vx cv vy cv cA wbr vy cv cA crn wcel vx
      cv vy cv cA vx vex vy vex brelrn pm4.71ri mobii vy cv cA crn wcel vx cv
      vy cv cA wbr vx moanimv bitri albii vx vy cA funcnv2 vx cv vy cv cA wbr
      vx wmo vy cA crn df-ral 3bitr4i $.

    $( A condition showing a class is single-rooted.  (See ~ funcnv ).
       (Contributed by NM, 26-May-2006.) $)
    funcnv3 $p |- ( Fun `' A <-> A. y e. ran A E! x e. dom A x A y ) $=
      vx cv vy cv cA wbr vx wmo vy cA crn wral vx cv vy cv cA wbr vx wex vx cv
      vy cv cA wbr vx wmo wa vy cA crn wral cA ccnv wfun vx cv vy cv cA wbr vx
      cA cdm wreu vy cA crn wral vx cv vy cv cA wbr vx wmo vx cv vy cv cA wbr
      vx wex vx cv vy cv cA wbr vx wmo wa vy cA crn vy cv cA crn wcel vx cv vy
      cv cA wbr vx wex vx cv vy cv cA wbr vx wmo vy cv cA crn wcel vx cv vy cv
      cA wbr vx wex vx cv vy cv cA wbr vx wex vy cA crn vx vy cA dfrn2 abeq2i
      biimpi biantrurd ralbiia vx vy cA funcnv vx cv vy cv cA wbr vx cA cdm
      wreu vx cv vy cv cA wbr vx wex vx cv vy cv cA wbr vx wmo wa vy cA crn vx
      cv vy cv cA wbr vx cA cdm wreu vx cv cA cdm wcel vx cv vy cv cA wbr wa vx
      weu vx cv vy cv cA wbr vx weu vx cv vy cv cA wbr vx wex vx cv vy cv cA
      wbr vx wmo wa vx cv vy cv cA wbr vx cA cdm df-reu vx cv vy cv cA wbr vx
      cv cA cdm wcel vx cv vy cv cA wbr wa vx vx cv vy cv cA wbr vx cv cA cdm
      wcel vx cv vy cv cA vx vex vy vex breldm pm4.71ri eubii vx cv vy cv cA
      wbr vx eu5 3bitr2i ralbii 3bitr4i $.

    $( The double converse of a class is a function iff the class is
       single-valued.  Each side is equivalent to Definition 6.4(2) of
       [TakeutiZaring] p. 23, who use the notation "Un(A)" for single-valued.
       Note that ` A ` is not necessarily a function.  (Contributed by NM,
       13-Aug-2004.) $)
    fun2cnv $p |- ( Fun `' `' A <-> A. x E* y x A y ) $=
      cA ccnv ccnv wfun vy cv vx cv cA ccnv wbr vy wmo vx wal vx cv vy cv cA
      wbr vy wmo vx wal vy vx cA ccnv funcnv2 vy cv vx cv cA ccnv wbr vy wmo vx
      cv vy cv cA wbr vy wmo vx vy cv vx cv cA ccnv wbr vx cv vy cv cA wbr vy
      vy cv vx cv cA vy vex vx vex brcnv mobii albii bitri $.

    $( A single-valued relation is a function.  (See ~ fun2cnv for
       "single-valued.") Definition 6.4(4) of [TakeutiZaring] p. 24.
       (Contributed by NM, 17-Jan-2006.) $)
    svrelfun $p |- ( Fun A <-> ( Rel A /\ Fun `' `' A ) ) $=
      cA wfun cA wrel vx cv vy cv cA wbr vy wmo vx wal wa cA wrel cA ccnv ccnv
      wfun wa vx vy cA dffun6 cA ccnv ccnv wfun vx cv vy cv cA wbr vy wmo vx
      wal cA wrel vx vy cA fun2cnv anbi2i bitr4i $.

    $( Single-rootedness (see ~ funcnv ) of a class cut down by a cross
       product.  (Contributed by NM, 5-Mar-2007.) $)
    fncnv $p |- ( `' ( R i^i ( A X. B ) ) Fn B <->
                  A. y e. B E! x e. A x R y ) $=
      cR cA cB cxp cin ccnv cB wfn cR cA cB cxp cin ccnv wfun cR cA cB cxp cin
      ccnv cdm cB wceq wa cR cA cB cxp cin ccnv wfun cR cA cB cxp cin crn cB
      wceq wa vx cv vy cv cR wbr vx cA wreu vy cB wral cR cA cB cxp cin ccnv cB
      df-fn cR cA cB cxp cin crn cB wceq cR cA cB cxp cin ccnv cdm cB wceq cR
      cA cB cxp cin ccnv wfun cR cA cB cxp cin crn cR cA cB cxp cin ccnv cdm cB
      cR cA cB cxp cin df-rn eqeq1i anbi2i cR cA cB cxp cin crn cB wceq cR cA
      cB cxp cin ccnv wfun wa vx cv vy cv cR wbr vx cA wrex vx cv vy cv cR wbr
      vx cA wrmo wa vy cB wral cR cA cB cxp cin ccnv wfun cR cA cB cxp cin crn
      cB wceq wa vx cv vy cv cR wbr vx cA wreu vy cB wral cR cA cB cxp cin crn
      cB wceq vx cv vy cv cR wbr vx cA wrmo vy cB wral wa vx cv vy cv cR wbr vx
      cA wrex vy cB wral vx cv vy cv cR wbr vx cA wrmo vy cB wral wa cR cA cB
      cxp cin crn cB wceq cR cA cB cxp cin ccnv wfun wa vx cv vy cv cR wbr vx
      cA wrex vx cv vy cv cR wbr vx cA wrmo wa vy cB wral cR cA cB cxp cin crn
      cB wceq vx cv vy cv cR wbr vx cA wrex vy cB wral vx cv vy cv cR wbr vx cA
      wrmo vy cB wral vx vy cA cB cR rninxp anbi1i cR cA cB cxp cin crn cB wceq
      cR cA cB cxp cin ccnv wfun vx cv vy cv cR wbr vx cA wrmo vy cB wral cR cA
      cB cxp cin ccnv wfun vx cv vy cv cR cA cB cxp cin wbr vx wmo vy cR cA cB
      cxp cin crn wral cR cA cB cxp cin crn cB wceq vx cv vy cv cR wbr vx cA
      wrmo vy cB wral vx vy cR cA cB cxp cin funcnv cR cA cB cxp cin crn cB
      wceq vx cv vy cv cR cA cB cxp cin wbr vx wmo vy cR cA cB cxp cin crn wral
      vx cv vy cv cR cA cB cxp cin wbr vx wmo vy cB wral vx cv vy cv cR wbr vx
      cA wrmo vy cB wral vx cv vy cv cR cA cB cxp cin wbr vx wmo vy cR cA cB
      cxp cin crn cB raleq vx cv vy cv cR cA cB cxp cin wbr vx wmo vx cv vy cv
      cR wbr vx cA wrmo vy cB vy cv cB wcel vx cv vy cv cR wbr vx cA wrmo vy cv
      cB wcel vx cv vy cv cR wbr vx cA wrmo wi vx cv vy cv cR cA cB cxp cin wbr
      vx wmo vy cv cB wcel vx cv vy cv cR wbr vx cA wrmo biimt vy cv cB wcel vx
      cv cA wcel vx cv vy cv cR wbr wa wa vx wmo vy cv cB wcel vx cv cA wcel vx
      cv vy cv cR wbr wa vx wmo wi vx cv vy cv cR cA cB cxp cin wbr vx wmo vy
      cv cB wcel vx cv vy cv cR wbr vx cA wrmo wi vy cv cB wcel vx cv cA wcel
      vx cv vy cv cR wbr wa vx moanimv vx cv vy cv cR cA cB cxp cin wbr vy cv
      cB wcel vx cv cA wcel vx cv vy cv cR wbr wa wa vx vx cv vy cv cR cA cB
      cxp cin wbr vx cv cA wcel vy cv cB wcel vx cv vy cv cR wbr w3a vy cv cB
      wcel vx cv cA wcel vx cv vy cv cR wbr wa wa vx cv vy cv cA cB cR brinxp2
      vx cv cA wcel vy cv cB wcel vx cv vy cv cR wbr 3anan12 bitri mobii vx cv
      vy cv cR wbr vx cA wrmo vx cv cA wcel vx cv vy cv cR wbr wa vx wmo vy cv
      cB wcel vx cv vy cv cR wbr vx cA df-rmo imbi2i 3bitr4i syl6rbbr ralbiia
      syl6bb syl5bb pm5.32i vx cv vy cv cR wbr vx cA wrex vx cv vy cv cR wbr vx
      cA wrmo vy cB r19.26 3bitr4i cR cA cB cxp cin ccnv wfun cR cA cB cxp cin
      crn cB wceq ancom vx cv vy cv cR wbr vx cA wreu vx cv vy cv cR wbr vx cA
      wrex vx cv vy cv cR wbr vx cA wrmo wa vy cB vx cv vy cv cR wbr vx cA reu5
      ralbii 3bitr4i 3bitr2i $.

    $( Two ways of stating that ` A ` is one-to-one (but not necessarily a
       function).  Each side is equivalent to Definition 6.4(3) of
       [TakeutiZaring] p. 24, who use the notation "Un_2 (A)" for one-to-one
       (but not necessarily a function).  (Contributed by NM, 17-Jan-2006.) $)
    fun11 $p |- ( ( Fun `' `' A /\ Fun `' A ) <->
         A. x A. y A. z A. w ( ( x A y /\ z A w ) -> ( x = z <-> y = w ) ) ) $=
      vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi vy wal vw
      wal vz wal vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi
      vx wal vw wal vz wal wa vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz
      cv wceq vy cv vw cv wceq wb wi vy wal vx wal vw wal vz wal cA ccnv ccnv
      wfun cA ccnv wfun wa vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv
      wceq vy cv vw cv wceq wb wi vw wal vz wal vy wal vx wal vx cv vy cv cA
      wbr vz cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wb wi vy wal
      vx wal vw wal vz wal vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv
      wceq wi vy wal vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq
      wi vx wal wa vw wal vz wal vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv
      vw cv wceq wi vy wal vw wal vz wal vx cv vw cv cA wbr vz cv vw cv cA wbr
      wa vx cv vz cv wceq wi vx wal vw wal vz wal wa vx cv vy cv cA wbr vz cv
      vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wb wi vy wal vx wal vz
      cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi vy wal vx cv vw
      cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal wa vz vw vx cv
      vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wb
      wi vy wal vx wal vx cv vz cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr
      wa vy cv vw cv wceq wi wi vy cv vw cv wceq vx cv vy cv cA wbr vz cv vw cv
      cA wbr wa vx cv vz cv wceq wi wi wa vy wal vx wal vx cv vz cv wceq vx cv
      vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi wi vy wal vx wal
      vy cv vw cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv
      wceq wi wi vy wal vx wal wa vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy
      cv vw cv wceq wi vy wal vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz
      cv wceq wi vx wal wa vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv
      wceq vy cv vw cv wceq wb wi vx cv vz cv wceq vx cv vy cv cA wbr vz cv vw
      cv cA wbr wa vy cv vw cv wceq wi wi vy cv vw cv wceq vx cv vy cv cA wbr
      vz cv vw cv cA wbr wa vx cv vz cv wceq wi wi wa vx vy vx cv vy cv cA wbr
      vz cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wb wi vx cv vy cv
      cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wi vy cv
      vw cv wceq vx cv vz cv wceq wi wa wi vx cv vy cv cA wbr vz cv vw cv cA
      wbr wa vx cv vz cv wceq vy cv vw cv wceq wi wi vx cv vy cv cA wbr vz cv
      vw cv cA wbr wa vy cv vw cv wceq vx cv vz cv wceq wi wi wa vx cv vz cv
      wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi wi vy
      cv vw cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq
      wi wi wa vx cv vz cv wceq vy cv vw cv wceq wb vx cv vz cv wceq vy cv vw
      cv wceq wi vy cv vw cv wceq vx cv vz cv wceq wi wa vx cv vy cv cA wbr vz
      cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq dfbi2 imbi2i vx cv
      vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wi
      vy cv vw cv wceq vx cv vz cv wceq wi pm4.76 vx cv vy cv cA wbr vz cv vw
      cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wi wi vx cv vz cv wceq vx
      cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi wi vx cv vy cv
      cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq vx cv vz cv wceq wi wi vy
      cv vw cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq
      wi wi vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq vy cv vw
      cv wceq bi2.04 vx cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq
      vx cv vz cv wceq bi2.04 anbi12i 3bitr2i 2albii vx cv vz cv wceq vx cv vy
      cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi wi vy cv vw cv wceq
      vx cv vy cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi wi vx vy
      19.26-2 vx cv vz cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv
      vw cv wceq wi wi vy wal vx wal vz cv vy cv cA wbr vz cv vw cv cA wbr wa
      vy cv vw cv wceq wi vy wal vy cv vw cv wceq vx cv vy cv cA wbr vz cv vw
      cv cA wbr wa vx cv vz cv wceq wi wi vy wal vx wal vx cv vw cv cA wbr vz
      cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal vx cv vz cv wceq vx cv vy
      cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi wi vy wal vx wal vx
      cv vz cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq
      wi wi vx wal vy wal vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv
      wceq wi vy wal vx cv vz cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa
      vy cv vw cv wceq wi wi vx vy alcom vx cv vz cv wceq vx cv vy cv cA wbr vz
      cv vw cv cA wbr wa vy cv vw cv wceq wi wi vx wal vz cv vy cv cA wbr vz cv
      vw cv cA wbr wa vy cv vw cv wceq wi vy vx cv vy cv cA wbr vz cv vw cv cA
      wbr wa vy cv vw cv wceq wi vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv
      vw cv wceq wi vx vz vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv
      wceq wi vx nfv vx cv vz cv wceq vx cv vy cv cA wbr vz cv vw cv cA wbr wa
      vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq vx cv vz cv
      wceq vx cv vy cv cA wbr vz cv vy cv cA wbr vz cv vw cv cA wbr vx cv vz cv
      vy cv cA breq1 anbi1d imbi1d equsal albii bitri vy cv vw cv wceq vx cv vy
      cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi wi vy wal vx cv vw cv
      cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx vx cv vy cv cA wbr vz
      cv vw cv cA wbr wa vx cv vz cv wceq wi vx cv vw cv cA wbr vz cv vw cv cA
      wbr wa vx cv vz cv wceq wi vy vw vx cv vw cv cA wbr vz cv vw cv cA wbr wa
      vx cv vz cv wceq wi vy nfv vy cv vw cv wceq vx cv vy cv cA wbr vz cv vw
      cv cA wbr wa vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq vy
      cv vw cv wceq vx cv vy cv cA wbr vx cv vw cv cA wbr vz cv vw cv cA wbr vy
      cv vw cv vx cv cA breq2 anbi1d imbi1d equsal albii anbi12i 3bitri 2albii
      vz cv vy cv cA wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi vy wal vx cv
      vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal vz vw
      19.26-2 bitr2i cA ccnv ccnv wfun vz cv vy cv cA wbr vz cv vw cv cA wbr wa
      vy cv vw cv wceq wi vy wal vw wal vz wal cA ccnv wfun vx cv vw cv cA wbr
      vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal vw wal vz wal cA ccnv
      ccnv wfun vz cv vy cv cA wbr vy wmo vz wal vz cv vy cv cA wbr vz cv vw cv
      cA wbr wa vy cv vw cv wceq wi vw wal vy wal vz wal vz cv vy cv cA wbr vz
      cv vw cv cA wbr wa vy cv vw cv wceq wi vy wal vw wal vz wal vz vy cA
      fun2cnv vz cv vy cv cA wbr vy wmo vz cv vy cv cA wbr vz cv vw cv cA wbr
      wa vy cv vw cv wceq wi vw wal vy wal vz vz cv vy cv cA wbr vz cv vw cv cA
      wbr vy vw vy cv vw cv vz cv cA breq2 mo4 albii vz cv vy cv cA wbr vz cv
      vw cv cA wbr wa vy cv vw cv wceq wi vw wal vy wal vz cv vy cv cA wbr vz
      cv vw cv cA wbr wa vy cv vw cv wceq wi vy wal vw wal vz vz cv vy cv cA
      wbr vz cv vw cv cA wbr wa vy cv vw cv wceq wi vy vw alcom albii 3bitri cA
      ccnv wfun vx cv vw cv cA wbr vx wmo vw wal vx cv vw cv cA wbr vz cv vw cv
      cA wbr wa vx cv vz cv wceq wi vz wal vx wal vw wal vx cv vw cv cA wbr vz
      cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal vw wal vz wal vx vw cA
      funcnv2 vx cv vw cv cA wbr vx wmo vx cv vw cv cA wbr vz cv vw cv cA wbr
      wa vx cv vz cv wceq wi vz wal vx wal vw vx cv vw cv cA wbr vz cv vw cv cA
      wbr vx vz vx cv vz cv vw cv cA breq1 mo4 albii vx cv vw cv cA wbr vz cv
      vw cv cA wbr wa vx cv vz cv wceq wi vz wal vx wal vw wal vx cv vw cv cA
      wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal vz wal vw wal vx cv
      vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx wal vw wal vz
      wal vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vz wal
      vx wal vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq wi vx
      wal vz wal vw vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv wceq
      wi vx vz alcom albii vx cv vw cv cA wbr vz cv vw cv cA wbr wa vx cv vz cv
      wceq wi vx wal vw vz alcom bitri 3bitri anbi12i vx cv vy cv cA wbr vz cv
      vw cv cA wbr wa vx cv vz cv wceq vy cv vw cv wceq wb wi vx vy vz vw
      alrot4 3bitr4i $.

    $( The union of a chain (with respect to inclusion) of functions is a
       function.  (Contributed by NM, 10-Aug-2004.) $)
    fununi $p |- ( A. f e. A ( Fun f /\ A. g e. A ( f C_ g \/ g C_ f ) ) ->
                 Fun U. A ) $=
      vf cv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA wral cA
      cuni wrel vx cv vy cv cop cA cuni wcel vx cv vz cv cop cA cuni wcel wa vy
      cv vz cv wceq wi vz wal vy wal vx wal cA cuni wfun vf cv wfun vf cv vg cv
      wss vg cv vf cv wss wo vg cA wral wa vf cA wral vf cv wrel vf cA wral cA
      cuni wrel vf cv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf
      cv wrel vf cA vf cv wfun vf cv wrel vf cv vg cv wss vg cv vf cv wss wo vg
      cA wral vf cv funrel adantr ralimi vf cA reluni sylibr vf cv wfun vf cv
      vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA wral vf cv wfun vf cv vg
      cv wss vg cv vf cv wss wo wa vg cA wral vf cA wral vx cv vy cv cop cA
      cuni wcel vx cv vz cv cop cA cuni wcel wa vy cv vz cv wceq wi vz wal vy
      wal vx wal vf cv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf
      cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vg cA wral vf cA vf cv wfun
      vf cv vg cv wss vg cv vf cv wss wo vg cA r19.28av ralimi vf cv wfun vf cv
      vg cv wss vg cv vf cv wss wo wa vg cA wral vf cA wral vx cv vy cv cop cA
      cuni wcel vx cv vz cv cop cA cuni wcel wa vy cv vz cv wceq wi vz wal vx
      vy vf cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vg cA wral vf cA wral
      vx cv vy cv cop cA cuni wcel vx cv vz cv cop cA cuni wcel wa vy cv vz cv
      wceq wi vz vw cv wfun vv cv wfun wa vw cv vv cv wss vv cv vw cv wss wo wa
      vv cA wral vw cA wral vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv
      wcel wa vy cv vz cv wceq wi vv cA wral vw cA wral vf cv wfun vf cv vg cv
      wss vg cv vf cv wss wo wa vg cA wral vf cA wral vx cv vy cv cop cA cuni
      wcel vx cv vz cv cop cA cuni wcel wa vy cv vz cv wceq wi vw cv wfun vv cv
      wfun wa vw cv vv cv wss vv cv vw cv wss wo wa vv cA wral vx cv vy cv cop
      vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi vv cA wral
      vw cA vw cv wfun vv cv wfun wa vw cv vv cv wss vv cv vw cv wss wo wa vx
      cv vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi
      vv cA vw cv wfun vv cv wfun wa vw cv vv cv wss vv cv vw cv wss wo vx cv
      vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi vw
      cv wfun vv cv wfun wa vw cv vv cv wss vx cv vy cv cop vw cv wcel vx cv vz
      cv cop vv cv wcel wa vy cv vz cv wceq wi vv cv vw cv wss vv cv wfun vw cv
      vv cv wss vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv
      vz cv wceq wi wi vw cv wfun vw cv vv cv wss vx cv vy cv cop vw cv wcel vx
      cv vz cv cop vv cv wcel wa vx cv vy cv cop vv cv wcel vx cv vz cv cop vv
      cv wcel wa vv cv wfun vy cv vz cv wceq vw cv vv cv wss vx cv vy cv cop vw
      cv wcel vx cv vy cv cop vv cv wcel vx cv vz cv cop vv cv wcel vw cv vv cv
      vx cv vy cv cop ssel anim1d vv cv wfun vx cv vy cv cop vv cv wcel vx cv
      vz cv cop vv cv wcel wa vy cv vz cv wceq wi vz vv cv wfun vx cv vy cv cop
      vv cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi vz wal vx vy
      vv cv wfun vv cv wrel vx cv vy cv cop vv cv wcel vx cv vz cv cop vv cv
      wcel wa vy cv vz cv wceq wi vz wal vy wal vx wal vx vy vz vv cv dffun4
      simprbi 19.21bbi 19.21bi syl9r adantl vw cv wfun vv cv vw cv wss vx cv vy
      cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi wi vv
      cv wfun vv cv vw cv wss vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv
      wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv cop vw cv wcel wa vw cv
      wfun vy cv vz cv wceq vv cv vw cv wss vx cv vz cv cop vv cv wcel vx cv vz
      cv cop vw cv wcel vx cv vy cv cop vw cv wcel vv cv vw cv vx cv vz cv cop
      ssel anim2d vw cv wfun vx cv vy cv cop vw cv wcel vx cv vz cv cop vw cv
      wcel wa vy cv vz cv wceq wi vz vw cv wfun vx cv vy cv cop vw cv wcel vx
      cv vz cv cop vw cv wcel wa vy cv vz cv wceq wi vz wal vx vy vw cv wfun vw
      cv wrel vx cv vy cv cop vw cv wcel vx cv vz cv cop vw cv wcel wa vy cv vz
      cv wceq wi vz wal vy wal vx wal vx vy vz vw cv dffun4 simprbi 19.21bbi
      19.21bi syl9r adantr jaod imp ralimi ralimi vf cv wfun vf cv vg cv wss vg
      cv vf cv wss wo wa vg cA wral vf cA wral vf cv wfun vf cv vg cv wss vg cv
      vf cv wss wo wa vg cA wral vf cA wral wa vw cv wfun vw cv vv cv wss vv cv
      vw cv wss wo wa vv cA wral vw cA wral vv cv wfun vw cv vv cv wss vv cv vw
      cv wss wo wa vv cA wral vw cA wral wa vf cv wfun vf cv vg cv wss vg cv vf
      cv wss wo wa vg cA wral vf cA wral vw cv wfun vv cv wfun wa vw cv vv cv
      wss vv cv vw cv wss wo wa vv cA wral vw cA wral vf cv wfun vf cv vg cv
      wss vg cv vf cv wss wo wa vg cA wral vf cA wral vw cv wfun vw cv vv cv
      wss vv cv vw cv wss wo wa vv cA wral vw cA wral vf cv wfun vf cv vg cv
      wss vg cv vf cv wss wo wa vg cA wral vf cA wral vv cv wfun vw cv vv cv
      wss vv cv vw cv wss wo wa vv cA wral vw cA wral vf cv wfun vf cv vg cv
      wss vg cv vf cv wss wo wa vw cv wfun vw cv vv cv wss vv cv vw cv wss wo
      wa vw cv wfun vw cv vg cv wss vg cv vw cv wss wo wa vf vg vw vv cA cA vf
      cv vw cv wceq vf cv wfun vw cv wfun vf cv vg cv wss vg cv vf cv wss wo vw
      cv vg cv wss vg cv vw cv wss wo vf cv vw cv funeq vf cv vw cv wceq vf cv
      vg cv wss vw cv vg cv wss vg cv vf cv wss vg cv vw cv wss vf cv vw cv vg
      cv sseq1 vf cv vw cv vg cv sseq2 orbi12d anbi12d vg cv vv cv wceq vw cv
      vg cv wss vg cv vw cv wss wo vw cv vv cv wss vv cv vw cv wss wo vw cv
      wfun vg cv vv cv wceq vw cv vg cv wss vw cv vv cv wss vg cv vw cv wss vv
      cv vw cv wss vg cv vv cv vw cv sseq2 vg cv vv cv vw cv sseq1 orbi12d
      anbi2d cbvral2v vf cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vg cA
      wral vf cA wral vf cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vf cA
      wral vg cA wral vv cv wfun vw cv vv cv wss vv cv vw cv wss wo wa vv cA
      wral vw cA wral vf cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vf vg cA
      cA ralcom vf cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vv cv wfun vw
      cv vv cv wss vv cv vw cv wss wo wa vf cv wfun vw cv vf cv wss vf cv vw cv
      wss wo wa vg vf vw vv cA cA vg cv vw cv wceq vf cv vg cv wss vg cv vf cv
      wss wo vw cv vf cv wss vf cv vw cv wss wo vf cv wfun vf cv vg cv wss vg
      cv vf cv wss wo vg cv vf cv wss vf cv vg cv wss wo vg cv vw cv wceq vw cv
      vf cv wss vf cv vw cv wss wo vf cv vg cv wss vg cv vf cv wss orcom vg cv
      vw cv wceq vg cv vf cv wss vw cv vf cv wss vf cv vg cv wss vf cv vw cv
      wss vg cv vw cv vf cv sseq1 vg cv vw cv vf cv sseq2 orbi12d syl5bb anbi2d
      vf cv vv cv wceq vf cv wfun vv cv wfun vw cv vf cv wss vf cv vw cv wss wo
      vw cv vv cv wss vv cv vw cv wss wo vf cv vv cv funeq vf cv vv cv wceq vw
      cv vf cv wss vw cv vv cv wss vf cv vw cv wss vv cv vw cv wss vf cv vv cv
      vw cv sseq2 vf cv vv cv vw cv sseq1 orbi12d anbi12d cbvral2v bitri
      anbi12i vf cv wfun vf cv vg cv wss vg cv vf cv wss wo wa vg cA wral vf cA
      wral anidm vw cv wfun vv cv wfun wa vw cv vv cv wss vv cv vw cv wss wo wa
      vv cA wral vw cA wral vw cv wfun vw cv vv cv wss vv cv vw cv wss wo wa vv
      cv wfun vw cv vv cv wss vv cv vw cv wss wo wa wa vv cA wral vw cA wral vw
      cv wfun vw cv vv cv wss vv cv vw cv wss wo wa vv cA wral vw cA wral vv cv
      wfun vw cv vv cv wss vv cv vw cv wss wo wa vv cA wral vw cA wral wa vw cv
      wfun vv cv wfun wa vw cv vv cv wss vv cv vw cv wss wo wa vw cv wfun vw cv
      vv cv wss vv cv vw cv wss wo wa vv cv wfun vw cv vv cv wss vv cv vw cv
      wss wo wa wa vw vv cA cA vw cv wfun vv cv wfun vw cv vv cv wss vv cv vw
      cv wss wo anandir 2ralbii vw cv wfun vw cv vv cv wss vv cv vw cv wss wo
      wa vv cv wfun vw cv vv cv wss vv cv vw cv wss wo wa vw vv cA cA r19.26-2
      bitr2i 3bitr3i vx cv vy cv cop cA cuni wcel vx cv vz cv cop cA cuni wcel
      wa vy cv vz cv wceq wi vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw
      cv wcel vx cv vz cv cop vv cv wcel wa wa vv wex vw wex vy cv vz cv wceq
      wi vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv
      cop vv cv wcel wa wa vv wex vy cv vz cv wceq wi vw wal vx cv vy cv cop vw
      cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi vv cA wral vw
      cA wral vx cv vy cv cop cA cuni wcel vx cv vz cv cop cA cuni wcel wa vw
      cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv cop vv
      cv wcel wa wa vv wex vw wex vy cv vz cv wceq vx cv vy cv cop cA cuni wcel
      vx cv vz cv cop cA cuni wcel wa vx cv vy cv cop vw cv wcel vw cv cA wcel
      wa vw wex vx cv vz cv cop vv cv wcel vv cv cA wcel wa vv wex wa vx cv vy
      cv cop vw cv wcel vw cv cA wcel wa vx cv vz cv cop vv cv wcel vv cv cA
      wcel wa wa vv wex vw wex vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop
      vw cv wcel vx cv vz cv cop vv cv wcel wa wa vv wex vw wex vx cv vy cv cop
      cA cuni wcel vx cv vy cv cop vw cv wcel vw cv cA wcel wa vw wex vx cv vz
      cv cop cA cuni wcel vx cv vz cv cop vv cv wcel vv cv cA wcel wa vv wex vw
      vx cv vy cv cop cA eluni vv vx cv vz cv cop cA eluni anbi12i vx cv vy cv
      cop vw cv wcel vw cv cA wcel wa vx cv vz cv cop vv cv wcel vv cv cA wcel
      wa vw vv eeanv vx cv vy cv cop vw cv wcel vw cv cA wcel wa vx cv vz cv
      cop vv cv wcel vv cv cA wcel wa wa vw cv cA wcel vv cv cA wcel wa vx cv
      vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa wa vw vv vx cv vy cv
      cop vw cv wcel vw cv cA wcel wa vx cv vz cv cop vv cv wcel vv cv cA wcel
      wa wa vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vw cv cA
      wcel vv cv cA wcel wa wa vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop
      vw cv wcel vx cv vz cv cop vv cv wcel wa wa vx cv vy cv cop vw cv wcel vw
      cv cA wcel vx cv vz cv cop vv cv wcel vv cv cA wcel an4 vx cv vy cv cop
      vw cv wcel vx cv vz cv cop vv cv wcel wa vw cv cA wcel vv cv cA wcel wa
      ancom bitri 2exbii 3bitr2i imbi1i vw cv cA wcel vv cv cA wcel wa vx cv vy
      cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa wa vv wex vy cv vz cv
      wceq vw 19.23v vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa
      vy cv vz cv wceq wi vv cA wral vw cA wral vw cv cA wcel vv cv cA wcel wa
      vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq
      wi wi vv wal vw wal vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv
      wcel vx cv vz cv cop vv cv wcel wa wa vy cv vz cv wceq wi vv wal vw wal
      vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv cop
      vv cv wcel wa wa vv wex vy cv vz cv wceq wi vw wal vx cv vy cv cop vw cv
      wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi vw vv cA cA r2al
      vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv cop
      vv cv wcel wa wa vy cv vz cv wceq wi vw cv cA wcel vv cv cA wcel wa vx cv
      vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa vy cv vz cv wceq wi wi
      vw vv vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz
      cv cop vv cv wcel wa vy cv vz cv wceq impexp 2albii vw cv cA wcel vv cv
      cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv cop vv cv wcel wa wa vy
      cv vz cv wceq wi vv wal vw cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw
      cv wcel vx cv vz cv cop vv cv wcel wa wa vv wex vy cv vz cv wceq wi vw vw
      cv cA wcel vv cv cA wcel wa vx cv vy cv cop vw cv wcel vx cv vz cv cop vv
      cv wcel wa wa vy cv vz cv wceq vv 19.23v albii 3bitr2ri 3bitr2i 3imtr4i
      alrimiv alrimivv syl vx vy vz cA cuni dffun4 sylanbrc $.

    $( The union of a chain (with respect to inclusion) of single-rooted sets
       is single-rooted.  (See ~ funcnv for "single-rooted" definition.)
       (Contributed by NM, 11-Aug-2004.) $)
    funcnvuni $p |- ( A. f e. A ( Fun `' f /\ A. g e. A ( f C_ g \/ g C_ f ) )
                    -> Fun `' U. A ) $=
      vf cv ccnv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA
      wral vy cv vx cv ccnv wceq vx cA wrex vy cab cuni wfun cA cuni ccnv wfun
      vf cv ccnv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA
      wral vz cv wfun vz cv vw cv wss vw cv vz cv wss wo vw vy cv vx cv ccnv
      wceq vx cA wrex vy cab wral wa vz vy cv vx cv ccnv wceq vx cA wrex vy cab
      wral vy cv vx cv ccnv wceq vx cA wrex vy cab cuni wfun vf cv ccnv wfun vf
      cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA wral vz cv vx cv ccnv
      wceq vx cA wrex vz cv wfun vw cv vx cv ccnv wceq vx cA wrex vz cv vw cv
      wss vw cv vz cv wss wo wi vw wal wa wi vz wal vz cv wfun vz cv vw cv wss
      vw cv vz cv wss wo vw vy cv vx cv ccnv wceq vx cA wrex vy cab wral wa vz
      vy cv vx cv ccnv wceq vx cA wrex vy cab wral vf cv ccnv wfun vf cv vg cv
      wss vg cv vf cv wss wo vg cA wral wa vf cA wral vz cv vx cv ccnv wceq vx
      cA wrex vz cv wfun vw cv vx cv ccnv wceq vx cA wrex vz cv vw cv wss vw cv
      vz cv wss wo wi vw wal wa wi vz vz cv vx cv ccnv wceq vx cA wrex vz cv vv
      cv ccnv wceq vv cA wrex vf cv ccnv wfun vf cv vg cv wss vg cv vf cv wss
      wo vg cA wral wa vf cA wral vz cv wfun vw cv vx cv ccnv wceq vx cA wrex
      vz cv vw cv wss vw cv vz cv wss wo wi vw wal wa vz cv vx cv ccnv wceq vz
      cv vv cv ccnv wceq vx vv cA vx cv vv cv wceq vx cv ccnv vv cv ccnv vz cv
      vx cv vv cv cnveq eqeq2d cbvrexv vf cv ccnv wfun vf cv vg cv wss vg cv vf
      cv wss wo vg cA wral wa vf cA wral vz cv vv cv ccnv wceq vz cv wfun vw cv
      vx cv ccnv wceq vx cA wrex vz cv vw cv wss vw cv vz cv wss wo wi vw wal
      wa vv cA vv cv cA wcel vf cv ccnv wfun vf cv vg cv wss vg cv vf cv wss wo
      vg cA wral wa vf cA wral vv cv ccnv wfun vv cv vg cv wss vg cv vv cv wss
      wo vg cA wral wa vz cv vv cv ccnv wceq vz cv wfun vw cv vx cv ccnv wceq
      vx cA wrex vz cv vw cv wss vw cv vz cv wss wo wi vw wal wa wi vf cv ccnv
      wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vv cv ccnv wfun vv
      cv vg cv wss vg cv vv cv wss wo vg cA wral wa vf vv cv cA vf cv vv cv
      wceq vf cv ccnv wfun vv cv ccnv wfun vf cv vg cv wss vg cv vf cv wss wo
      vg cA wral vv cv vg cv wss vg cv vv cv wss wo vg cA wral vf cv vv cv wceq
      vf cv ccnv vv cv ccnv vf cv vv cv cnveq funeqd vf cv vv cv wceq vf cv vg
      cv wss vg cv vf cv wss wo vv cv vg cv wss vg cv vv cv wss wo vg cA vf cv
      vv cv wceq vf cv vg cv wss vv cv vg cv wss vg cv vf cv wss vg cv vv cv
      wss vf cv vv cv vg cv sseq1 vf cv vv cv vg cv sseq2 orbi12d ralbidv
      anbi12d rspcv vv cv ccnv wfun vz cv vv cv ccnv wceq vz cv wfun vv cv vg
      cv wss vg cv vv cv wss wo vg cA wral vw cv vx cv ccnv wceq vx cA wrex vz
      cv vw cv wss vw cv vz cv wss wo wi vw wal vz cv vv cv ccnv wceq vz cv
      wfun vv cv ccnv wfun vz cv vv cv ccnv funeq biimprcd vv cv vg cv wss vg
      cv vv cv wss wo vg cA wral vz cv vv cv ccnv wceq vw cv vx cv ccnv wceq vx
      cA wrex vz cv vw cv wss vw cv vz cv wss wo wi vw vv cv vg cv wss vg cv vv
      cv wss wo vg cA wral vw cv vx cv ccnv wceq vx cA wrex vz cv vv cv ccnv
      wceq vz cv vw cv wss vw cv vz cv wss wo vv cv vg cv wss vg cv vv cv wss
      wo vg cA wral vw cv vx cv ccnv wceq vz cv vv cv ccnv wceq vz cv vw cv wss
      vw cv vz cv wss wo wi vx cA vx cv cA wcel vv cv vg cv wss vg cv vv cv wss
      wo vg cA wral vv cv vx cv wss vx cv vv cv wss wo vw cv vx cv ccnv wceq vz
      cv vv cv ccnv wceq vz cv vw cv wss vw cv vz cv wss wo wi wi vv cv vg cv
      wss vg cv vv cv wss wo vv cv vx cv wss vx cv vv cv wss wo vg vx cv cA vg
      cv vx cv wceq vv cv vg cv wss vv cv vx cv wss vg cv vv cv wss vx cv vv cv
      wss vg cv vx cv vv cv sseq2 vg cv vx cv vv cv sseq1 orbi12d rspcv vv cv
      vx cv wss vx cv vv cv wss wo vw cv vx cv ccnv wceq vz cv vv cv ccnv wceq
      vz cv vw cv wss vw cv vz cv wss wo vv cv vx cv wss vx cv vv cv wss wo vz
      cv vw cv wss vw cv vz cv wss wo vw cv vx cv ccnv wceq vz cv vv cv ccnv
      wceq wa vv cv ccnv vx cv ccnv wss vx cv ccnv vv cv ccnv wss wo vv cv vx
      cv wss vv cv ccnv vx cv ccnv wss vx cv vv cv wss vx cv ccnv vv cv ccnv
      wss vv cv vx cv cnvss vx cv vv cv cnvss orim12i vw cv vx cv ccnv wceq vz
      cv vv cv ccnv wceq wa vz cv vw cv wss vv cv ccnv vx cv ccnv wss vw cv vz
      cv wss vx cv ccnv vv cv ccnv wss vz cv vv cv ccnv wceq vw cv vx cv ccnv
      wceq vz cv vw cv wss vv cv ccnv vx cv ccnv wss wb vz cv vv cv ccnv vw cv
      vx cv ccnv sseq12 ancoms vw cv vx cv ccnv vz cv vv cv ccnv sseq12 orbi12d
      syl5ibrcom exp3a syl6com rexlimdv com23 alrimdv anim12ii syl6com rexlimdv
      syl5bi alrimiv vz cv wfun vz cv vw cv wss vw cv vz cv wss wo vw vy cv vx
      cv ccnv wceq vx cA wrex vy cab wral wa vz vy cv vx cv ccnv wceq vx cA
      wrex vy cab wral vz cv vy cv vx cv ccnv wceq vx cA wrex vy cab wcel vz cv
      wfun vz cv vw cv wss vw cv vz cv wss wo vw vy cv vx cv ccnv wceq vx cA
      wrex vy cab wral wa wi vz wal vz cv vx cv ccnv wceq vx cA wrex vz cv wfun
      vw cv vx cv ccnv wceq vx cA wrex vz cv vw cv wss vw cv vz cv wss wo wi vw
      wal wa wi vz wal vz cv wfun vz cv vw cv wss vw cv vz cv wss wo vw vy cv
      vx cv ccnv wceq vx cA wrex vy cab wral wa vz vy cv vx cv ccnv wceq vx cA
      wrex vy cab df-ral vz cv vy cv vx cv ccnv wceq vx cA wrex vy cab wcel vz
      cv wfun vz cv vw cv wss vw cv vz cv wss wo vw vy cv vx cv ccnv wceq vx cA
      wrex vy cab wral wa wi vz cv vx cv ccnv wceq vx cA wrex vz cv wfun vw cv
      vx cv ccnv wceq vx cA wrex vz cv vw cv wss vw cv vz cv wss wo wi vw wal
      wa wi vz vz cv vy cv vx cv ccnv wceq vx cA wrex vy cab wcel vz cv vx cv
      ccnv wceq vx cA wrex vz cv wfun vz cv vw cv wss vw cv vz cv wss wo vw vy
      cv vx cv ccnv wceq vx cA wrex vy cab wral wa vz cv wfun vw cv vx cv ccnv
      wceq vx cA wrex vz cv vw cv wss vw cv vz cv wss wo wi vw wal wa vy cv vx
      cv ccnv wceq vx cA wrex vz cv vx cv ccnv wceq vx cA wrex vy vz cv vz vex
      vy cv vz cv wceq vy cv vx cv ccnv wceq vz cv vx cv ccnv wceq vx cA vy cv
      vz cv vx cv ccnv eqeq1 rexbidv elab vz cv vw cv wss vw cv vz cv wss wo vw
      vy cv vx cv ccnv wceq vx cA wrex vy cab wral vw cv vx cv ccnv wceq vx cA
      wrex vz cv vw cv wss vw cv vz cv wss wo wi vw wal vz cv wfun vy cv vx cv
      ccnv wceq vx cA wrex vw cv vx cv ccnv wceq vx cA wrex vz cv vw cv wss vw
      cv vz cv wss wo vw vy vy cv vw cv wceq vy cv vx cv ccnv wceq vw cv vx cv
      ccnv wceq vx cA vy cv vw cv vx cv ccnv eqeq1 rexbidv ralab anbi2i imbi12i
      albii bitr2i sylib vy cv vx cv ccnv wceq vx cA wrex vy cab vz vw fununi
      syl cA cuni ccnv vy cv vx cv ccnv wceq vx cA wrex vy cab cuni cA cuni
      ccnv vx cA vx cv ccnv ciun vy cv vx cv ccnv wceq vx cA wrex vy cab cuni
      vx cA cnvuni vx vy cA vx cv ccnv vx cv vx vex cnvex dfiun2 eqtri funeqi
      sylibr $.

    $( The union of a chain (with respect to inclusion) of one-to-one functions
       is a one-to-one function.  (Contributed by NM, 11-Aug-2004.) $)
    fun11uni $p |- ( A. f e. A ( ( Fun f /\ Fun `' f ) /\
                   A. g e. A ( f C_ g \/ g C_ f ) ) ->
                   ( Fun U. A /\ Fun `' U. A ) ) $=
      vf cv wfun vf cv ccnv wfun wa vf cv vg cv wss vg cv vf cv wss wo vg cA
      wral wa vf cA wral cA cuni wfun cA cuni ccnv wfun vf cv wfun vf cv ccnv
      wfun wa vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA wral vf cv
      wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA wral cA cuni
      wfun vf cv wfun vf cv ccnv wfun wa vf cv vg cv wss vg cv vf cv wss wo vg
      cA wral wa vf cv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf
      cA vf cv wfun vf cv ccnv wfun wa vf cv wfun vf cv vg cv wss vg cv vf cv
      wss wo vg cA wral vf cv wfun vf cv ccnv wfun simpl anim1i ralimi cA vf vg
      fununi syl vf cv wfun vf cv ccnv wfun wa vf cv vg cv wss vg cv vf cv wss
      wo vg cA wral wa vf cA wral vf cv ccnv wfun vf cv vg cv wss vg cv vf cv
      wss wo vg cA wral wa vf cA wral cA cuni ccnv wfun vf cv wfun vf cv ccnv
      wfun wa vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cv ccnv wfun
      vf cv vg cv wss vg cv vf cv wss wo vg cA wral wa vf cA vf cv wfun vf cv
      ccnv wfun wa vf cv ccnv wfun vf cv vg cv wss vg cv vf cv wss wo vg cA
      wral vf cv wfun vf cv ccnv wfun simpr anim1i ralimi cA vf vg funcnvuni
      syl jca $.
  $}

  ${
    $d x y F $.  $d x y G $.
    $( The intersection with a function is a function.  Exercise 14(a) of
       [Enderton] p. 53.  (Contributed by NM, 19-Mar-2004.)  (Proof shortened
       by Andrew Salmon, 17-Sep-2011.) $)
    funin $p |- ( Fun F -> Fun ( F i^i G ) ) $=
      cF cG cin cF wss cF wfun cF cG cin wfun wi cF cG inss1 cF cG cin cF funss
      ax-mp $.
  $}

  $( The restriction of a one-to-one function is one-to-one.  (Contributed by
     NM, 25-Mar-1998.) $)
  funres11 $p |- ( Fun `' F -> Fun `' ( F |` A ) ) $=
    cF cA cres cF wss cF cA cres ccnv cF ccnv wss cF ccnv wfun cF cA cres ccnv
    wfun wi cF cA resss cF cA cres cF cnvss cF cA cres ccnv cF ccnv funss mp2b
    $.

  $( The converse of a restricted function.  (Contributed by NM,
     27-Mar-1998.) $)
  funcnvres $p |- ( Fun `' F -> `' ( F |` A ) = ( `' F |` ( F " A ) ) ) $=
    cF ccnv wfun cF ccnv cF cA cima cres cF ccnv cF cA cres ccnv cdm cres cF cA
    cres ccnv cF cA cima cF cA cres ccnv cdm cF ccnv cF cA cima cF cA cres crn
    cF cA cres ccnv cdm cF cA df-ima cF cA cres df-rn eqtri reseq2i cF ccnv
    wfun cF cA cres ccnv cF ccnv wss cF ccnv cF cA cres ccnv cdm cres cF cA
    cres ccnv wceq cF cA cres cF wss cF cA cres ccnv cF ccnv wss cF cA resss cF
    cA cres cF cnvss ax-mp cF ccnv cF cA cres ccnv funssres mpan2 syl5req $.

  $( Converse of a restricted identity function.  (Contributed by FL,
     4-Mar-2007.) $)
  cnvresid $p |- `' ( _I |` A ) = ( _I |` A ) $=
    cid cid ccnv wceq cid ccnv wfun cid cA cres ccnv cid cA cres wceq cid ccnv
    cid cnvi eqcomi cid cid ccnv wceq cid wfun cid ccnv wfun funi cid cid ccnv
    funeq mpbii cid ccnv wfun cid cA cres ccnv cid ccnv cid cA cima cres cid cA
    cres cA cid funcnvres cid ccnv cid cid cA cima cA cnvi cA imai reseq12i
    syl6eq mp2b $.

  $( The converse of a restriction of the converse of a function equals the
     function restricted to the image of its converse.  (Contributed by NM,
     4-May-2005.) $)
  funcnvres2 $p |- ( Fun F -> `' ( `' F |` A ) = ( F |` ( `' F " A ) ) ) $=
    cF wfun cF ccnv cA cres ccnv cF ccnv ccnv cF ccnv cA cima cres cF cF ccnv
    cA cima cres cF wfun cF ccnv ccnv wfun cF ccnv cA cres ccnv cF ccnv ccnv cF
    ccnv cA cima cres wceq cF funcnvcnv cA cF ccnv funcnvres syl cF wfun cF
    ccnv ccnv cF cF ccnv cA cima cF wfun cF wrel cF ccnv ccnv cF wceq cF funrel
    cF dfrel2 sylib reseq1d eqtrd $.

  $( The image of the preimage of a function.  (Contributed by NM,
     25-May-2004.) $)
  funimacnv $p |- ( Fun F -> ( F " ( `' F " A ) ) = ( A i^i ran F ) ) $=
    cF wfun cF cF ccnv cA cima cima cF ccnv cA cres ccnv crn cA cF crn cin cF
    wfun cF ccnv cA cres ccnv crn cF cF ccnv cA cima cres crn cF cF ccnv cA
    cima cima cF wfun cF ccnv cA cres ccnv cF cF ccnv cA cima cres cA cF
    funcnvres2 rneqd cF cF ccnv cA cima df-ima syl6reqr cA cF crn cin cA cF
    ccnv cdm cin cF ccnv cA cres cdm cF ccnv cA cres ccnv crn cF crn cF ccnv
    cdm cA cF df-rn ineq2i cF ccnv cA dmres cF ccnv cA cres dfdm4 3eqtr2ri
    syl6eq $.

  $( A kind of contraposition law that infers a subclass of an image from a
     preimage subclass.  (Contributed by NM, 25-May-2004.) $)
  funimass1 $p |- ( ( Fun F /\ A C_ ran F ) ->
                 ( ( `' F " A ) C_ B -> A C_ ( F " B ) ) ) $=
    cF ccnv cA cima cB wss cF cF ccnv cA cima cima cF cB cima wss cF wfun cA cF
    crn wss wa cA cF cB cima wss cF ccnv cA cima cB cF imass2 cF wfun cA cF crn
    wss wa cF cF ccnv cA cima cima cA cF cB cima cF wfun cA cF crn wss cF cF
    ccnv cA cima cima cA cF crn cin cA cA cF funimacnv cA cF crn wss cA cA cF
    crn cin cA cF crn wss cA cA cF crn cin wceq cA cF crn dfss biimpi eqcomd
    sylan9eq sseq1d syl5ib $.

  $( A kind of contraposition law that infers an image subclass from a subclass
     of a preimage.  (Contributed by NM, 25-May-2004.) $)
  funimass2 $p |- ( ( Fun F /\ A C_ ( `' F " B ) ) -> ( F " A ) C_ B ) $=
    cA cF ccnv cB cima wss cF wfun cF cA cima cF cF ccnv cB cima cima wss cF cA
    cima cB wss cA cF ccnv cB cima cF imass2 cF wfun cF cA cima cF cF ccnv cB
    cima cima wss cF cA cima cB wss cF wfun cF cA cima cF cF ccnv cB cima cima
    wss cF cA cima cB cF crn cin wss cF cA cima cB wss cF wfun cF cF ccnv cB
    cima cima cB cF crn cin cF cA cima cB cF funimacnv sseq2d cF cA cima cB cF
    crn cin wss cB cF crn cin cB wss cF cA cima cB wss cB cF crn inss1 cF cA
    cima cB cF crn cin cB sstr2 mpi syl6bi imp sylan2 $.

  ${
    $d x y A $.  $d x y B $.  $d x y F $.
    $( The image of a difference is the difference of images.  (Contributed by
       NM, 24-May-1998.) $)
    imadif $p |- ( Fun `' F ->
                 ( F " ( A \ B ) ) = ( ( F " A ) \ ( F " B ) ) ) $=
      cF ccnv wfun vy cF cA cB cdif cima cF cA cima cF cB cima cdif cF ccnv
      wfun vx cv cA cB cdif wcel vx cv vy cv cF wbr wa vx wex vy cv cF cA cima
      wcel vy cv cF cB cima wcel wn wa vy cv cF cA cB cdif cima wcel vy cv cF
      cA cima cF cB cima cdif wcel cF ccnv wfun vx cv cA wcel vx cv cB wcel wn
      wa vx cv vy cv cF wbr wa vx wex vx cv cA wcel vx cv vy cv cF wbr wa vx
      wex vx cv cB wcel vx cv vy cv cF wbr wa vx wex wn wa vx cv cA cB cdif
      wcel vx cv vy cv cF wbr wa vx wex vy cv cF cA cima wcel vy cv cF cB cima
      wcel wn wa cF ccnv wfun vx cv cA wcel vx cv cB wcel wn wa vx cv vy cv cF
      wbr wa vx wex vx cv cA wcel vx cv vy cv cF wbr wa vx wex vx cv cB wcel vx
      cv vy cv cF wbr wa vx wex wn wa vx cv cA wcel vx cv cB wcel wn wa vx cv
      vy cv cF wbr wa vx wex vx cv cA wcel vx cv vy cv cF wbr wa vx wex vx cv
      cB wcel wn vx cv vy cv cF wbr wa vx wex wa cF ccnv wfun vx cv cA wcel vx
      cv vy cv cF wbr wa vx wex vx cv cB wcel vx cv vy cv cF wbr wa vx wex wn
      wa vx cv cA wcel vx cv cB wcel wn wa vx cv vy cv cF wbr wa vx wex vx cv
      cA wcel vx cv vy cv cF wbr wa vx cv cB wcel wn vx cv vy cv cF wbr wa wa
      vx wex vx cv cA wcel vx cv vy cv cF wbr wa vx wex vx cv cB wcel wn vx cv
      vy cv cF wbr wa vx wex wa vx cv cA wcel vx cv cB wcel wn wa vx cv vy cv
      cF wbr wa vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB wcel wn vx cv vy
      cv cF wbr wa wa vx vx cv cA wcel vx cv cB wcel wn vx cv vy cv cF wbr
      anandir exbii vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB wcel wn vx cv
      vy cv cF wbr wa vx 19.40 sylbi cF ccnv wfun vx cv cB wcel wn vx cv vy cv
      cF wbr wa vx wex vx cv cB wcel vx cv vy cv cF wbr wa vx wex wn vx cv cA
      wcel vx cv vy cv cF wbr wa vx wex cF ccnv wfun vx cv vy cv cF wbr vx cv
      cB wcel wn wa vx wex vx cv cB wcel vx cv vy cv cF wbr wa wn vx wal vx cv
      cB wcel wn vx cv vy cv cF wbr wa vx wex vx cv cB wcel vx cv vy cv cF wbr
      wa vx wex wn cF ccnv wfun vx cv vy cv cF wbr vx cv cB wcel wn wa vx wex
      vx cv cB wcel vx cv vy cv cF wbr wa wn vx wal cF ccnv wfun vx cv vy cv cF
      wbr vx cv cB wcel wn wa vx wex wa vx cv cB wcel vx cv vy cv cF wbr wa wn
      vx cF ccnv wfun vx cv vy cv cF wbr vx cv cB wcel wn wa vx wex vx cF ccnv
      wfun vx nfv vx cv vy cv cF wbr vx cv cB wcel wn wa vx nfe1 nfan cF ccnv
      wfun vx cv vy cv cF wbr vx cv cB wcel wn wa vx wex wa vx cv cB wcel vx cv
      vy cv cF wbr wn wi vx cv cB wcel vx cv vy cv cF wbr wa wn cF ccnv wfun vx
      cv vy cv cF wbr vx cv cB wcel wn wa vx wex wa vx cv vy cv cF wbr vx cv cB
      wcel cF ccnv wfun vx cv vy cv cF wbr vx wmo vx cv vy cv cF wbr vx cv cB
      wcel wn wa vx wex vx cv vy cv cF wbr vx cv cB wcel wn wi cF ccnv wfun vy
      cv vx cv cF ccnv wbr vx wmo vx cv vy cv cF wbr vx wmo vx vy cv cF ccnv
      funmo vy cv vx cv cF ccnv wbr vx cv vy cv cF wbr vx vy cv vx cv cF vy vex
      vx vex brcnv mobii sylib vx cv vy cv cF wbr vx cv cB wcel wn vx mopick
      sylan con2d vx cv cB wcel vx cv vy cv cF wbr imnan sylib alrimi ex vx cv
      vy cv cF wbr vx cv cB wcel wn vx exancom vx cv cB wcel vx cv vy cv cF wbr
      wa vx alnex 3imtr3g anim2d syl5 vx cv cA wcel vx cv vy cv cF wbr wa vx
      wex vx cv cB wcel vx cv vy cv cF wbr wa vx wex wn wa vx cv cA wcel vx cv
      vy cv cF wbr wa vx cv cB wcel vx cv vy cv cF wbr wa wn wa vx wex vx cv cA
      wcel vx cv cB wcel wn wa vx cv vy cv cF wbr wa vx wex vx cv cB wcel vx cv
      vy cv cF wbr wa vx wex wn vx cv cA wcel vx cv vy cv cF wbr wa vx wex vx
      cv cB wcel vx cv vy cv cF wbr wa wn vx wal vx cv cA wcel vx cv vy cv cF
      wbr wa vx cv cB wcel vx cv vy cv cF wbr wa wn wa vx wex vx cv cB wcel vx
      cv vy cv cF wbr wa vx alnex vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB
      wcel vx cv vy cv cF wbr wa wn vx 19.29r sylan2br vx cv cA wcel vx cv vy
      cv cF wbr wa vx cv cB wcel vx cv vy cv cF wbr wa wn wa vx cv cA wcel vx
      cv cB wcel wn wa vx cv vy cv cF wbr wa vx vx cv cA wcel vx cv vy cv cF
      wbr wa vx cv cB wcel wn vx cv vy cv cF wbr wn wo wa vx cv cA wcel vx cv
      vy cv cF wbr wa vx cv cB wcel wn wa vx cv cA wcel vx cv vy cv cF wbr wa
      vx cv vy cv cF wbr wn wa wo vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB
      wcel vx cv vy cv cF wbr wa wn wa vx cv cA wcel vx cv cB wcel wn wa vx cv
      vy cv cF wbr wa vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB wcel wn vx
      cv vy cv cF wbr wn andi vx cv cB wcel vx cv vy cv cF wbr wa wn vx cv cB
      wcel wn vx cv vy cv cF wbr wn wo vx cv cA wcel vx cv vy cv cF wbr wa vx
      cv cB wcel vx cv vy cv cF wbr ianor anbi2i vx cv cA wcel vx cv cB wcel wn
      wa vx cv vy cv cF wbr wa vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB
      wcel wn wa vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB wcel wn wa vx cv
      cA wcel vx cv vy cv cF wbr wa vx cv vy cv cF wbr wn wa wo vx cv cA wcel
      vx cv cB wcel wn vx cv vy cv cF wbr an32 vx cv cA wcel vx cv vy cv cF wbr
      wa vx cv vy cv cF wbr wn wa vx cv cA wcel vx cv vy cv cF wbr wa vx cv cB
      wcel wn wa vx cv cA wcel vx cv vy cv cF wbr wa vx cv vy cv cF wbr wn wa
      vx cv cA wcel vx cv vy cv cF wbr vx cv vy cv cF wbr wn wa wa vx cv vy cv
      cF wbr vx cv vy cv cF wbr wn wa vx cv cA wcel vx cv vy cv cF wbr pm3.24
      intnan vx cv cA wcel vx cv vy cv cF wbr vx cv vy cv cF wbr wn anass mtbir
      biorfi bitri 3bitr4i exbii sylib impbid1 vx cv cA cB cdif wcel vx cv vy
      cv cF wbr wa vx cv cA wcel vx cv cB wcel wn wa vx cv vy cv cF wbr wa vx
      vx cv cA cB cdif wcel vx cv cA wcel vx cv cB wcel wn wa vx cv vy cv cF
      wbr vx cv cA cB eldif anbi1i exbii vy cv cF cA cima wcel vx cv cA wcel vx
      cv vy cv cF wbr wa vx wex vy cv cF cB cima wcel wn vx cv cB wcel vx cv vy
      cv cF wbr wa vx wex wn vx vy cv cF cA vy vex elima2 vy cv cF cB cima wcel
      vx cv cB wcel vx cv vy cv cF wbr wa vx wex vx vy cv cF cB vy vex elima2
      notbii anbi12i 3bitr4g vx vy cv cF cA cB cdif vy vex elima2 vy cv cF cA
      cima cF cB cima eldif 3bitr4g eqrdv $.
  $}

  $( The image of an intersection is the intersection of images.  (Contributed
     by Paul Chapman, 11-Apr-2009.) $)
  imain $p |- ( Fun `' F ->
                ( F " ( A i^i B ) ) = ( ( F " A ) i^i ( F " B ) ) ) $=
    cF ccnv wfun cF cA cA cB cdif cdif cima cF cA cima cF cA cima cF cB cima
    cdif cdif cF cA cB cin cima cF cA cima cF cB cima cin cF ccnv wfun cF cA cA
    cB cdif cdif cima cF cA cima cF cA cB cdif cima cdif cF cA cima cF cA cima
    cF cB cima cdif cdif cA cA cB cdif cF imadif cF ccnv wfun cF cA cB cdif
    cima cF cA cima cF cB cima cdif cF cA cima cA cB cF imadif difeq2d eqtrd cA
    cB cin cA cA cB cdif cdif cF cA cB dfin4 imaeq2i cF cA cima cF cB cima
    dfin4 3eqtr4g $.

  ${
    $d w B $.  $d x y z w A $.
    $( Axiom of Replacement using abbreviations.  Axiom 39(vi) of [Quine]
       p. 284.  Compare Exercise 9 of [TakeutiZaring] p. 29.  (Contributed by
       NM, 10-Sep-2006.) $)
    funimaexg $p |- ( ( Fun A /\ B e. C ) -> ( A " B ) e. _V ) $=
      cB cC wcel cA wfun cA cB cima cvv wcel cA wfun cA vw cv cima cvv wcel wi
      cA wfun cA cB cima cvv wcel wi vw cB cC vw cv cB wceq cA vw cv cima cvv
      wcel cA cB cima cvv wcel cA wfun vw cv cB wceq cA vw cv cima cA cB cima
      cvv vw cv cB cA imaeq2 eleq1d imbi2d cA wfun vx cv vy cv cop cA wcel vy
      cv vz cv wceq wi vy wal vz wex vx wal cA vw cv cima cvv wcel cA wfun cA
      wrel vx cv vy cv cop cA wcel vy cv vz cv wceq wi vy wal vz wex vx wal vx
      vy vz cA dffun5 simprbi vx cv vy cv cop cA wcel vy cv vz cv wceq wi vy
      wal vz wex vx wal vy cv vz cv wcel vx cv vw cv wcel vx cv vy cv cop cA
      wcel wa vx wex wb vy wal vz wex cA vw cv cima cvv wcel vx cv vy cv cop cA
      wcel vx vy vz vw vx cv vy cv cop cA wcel vz nfv axrep4 cA vw cv cima cvv
      wcel vz cv cA vw cv cima wceq vz wex vy cv vz cv wcel vx cv vw cv wcel vx
      cv vy cv cop cA wcel wa vx wex wb vy wal vz wex vz cA vw cv cima isset vz
      cv cA vw cv cima wceq vy cv vz cv wcel vx cv vw cv wcel vx cv vy cv cop
      cA wcel wa vx wex wb vy wal vz vz cv cA vw cv cima wceq vz cv vx cv vw cv
      wcel vx cv vy cv cop cA wcel wa vx wex vy cab wceq vy cv vz cv wcel vx cv
      vw cv wcel vx cv vy cv cop cA wcel wa vx wex wb vy wal cA vw cv cima vx
      cv vw cv wcel vx cv vy cv cop cA wcel wa vx wex vy cab vz cv vx vy cA vw
      cv dfima3 eqeq2i vx cv vw cv wcel vx cv vy cv cop cA wcel wa vx wex vy vz
      cv abeq2 bitri exbii bitri sylibr syl vtoclg impcom $.
  $}

  ${
    zfrep5.1 $e |- B e. _V $.
    $( The image of a set under any function is also a set.  Equivalent of
       Axiom of Replacement ~ ax-rep .  Axiom 39(vi) of [Quine] p. 284.
       Compare Exercise 9 of [TakeutiZaring] p. 29.  (Contributed by NM,
       17-Nov-2002.) $)
    funimaex $p |- ( Fun A -> ( A " B ) e. _V ) $=
      cA wfun cB cvv wcel cA cB cima cvv wcel zfrep5.1 cA cB cvv funimaexg
      mpan2 $.
  $}

  ${
    $d x z A $.  $d b x y z $.  $d z ph $.
    $( Part of a study of the Axiom of Replacement used by the Isabelle
       prover.  The object PrimReplace is apparently the image of the function
       encoded by ` ph ( x , y ) ` i.e. the class
       ` ( { <. x , y >. | ph } " A ) ` .  If so, we can prove Isabelle's
       "Axiom of Replacement" conclusion without using the Axiom of
       Replacement, for which I (N. Megill) currently have no explanation.
       (Contributed by NM, 26-Oct-2006.)  (Proof shortened by Mario Carneiro,
       4-Dec-2016.) $)
    isarep1 $p |- ( b e. ( { <. x , y >. | ph } " A ) <->
                 E. x e. A [ b / y ] ph ) $=
      vb cv wph vx vy copab cA cima wcel vz cv vb cv wph vx vy copab wbr vz cA
      wrex wph vy vb wsb vx vz wsb vz cA wrex wph vy vb wsb vx cA wrex vz vb cv
      wph vx vy copab cA vb vex elima vz cv vb cv wph vx vy copab wbr wph vy vb
      wsb vx vz wsb vz cA vz cv vb cv wph vx vy copab wbr vz cv vb cv cop wph
      vx vy copab wcel wph vy vb cv wsbc vx vz cv wsbc wph vy vb wsb vx vz wsb
      vz cv vb cv wph vx vy copab df-br wph vx vy vz cv vb cv opelopabsb wph vy
      vb wsb vx vz wsb wph vy vb cv wsbc vx vz wsb wph vy vb cv wsbc vx vz cv
      wsbc wph vy vb wsb wph vy vb cv wsbc vx vz wph vy vb sbsbc sbbii wph vy
      vb cv wsbc vx vz sbsbc bitr2i 3bitri rexbii wph vy vb wsb vx vz wsb wph
      vy vb wsb vz vx cA wph vy vb wsb vx vz nfs1v wph vy vb wsb vz nfv wph vy
      vb wsb vz vx sbequ12r cbvrex 3bitri $.
  $}

  ${
    $d w x y A $.  $d b x y $.  $d y z $.  $d w ph $.  $d z ph $.
    isarep2.1 $e |- A e. _V $.
    isarep2.2 $e |- A. x e. A A. y A. z ( ( ph /\ [ z / y ] ph ) -> y = z ) $.
    $( Part of a study of the Axiom of Replacement used by the Isabelle
       prover.  In Isabelle, the sethood of PrimReplace is apparently
       postulated implicitly by its type signature " ` [ ` i, ` [ ` i, i ` ] `
       => o ` ] ` => i", which automatically asserts that it is a set without
       using any axioms.  To prove that it is a set in Metamath, we need the
       hypotheses of Isabelle's "Axiom of Replacement" as well as the Axiom of
       Replacement in the form ~ funimaex .  (Contributed by NM,
       26-Oct-2006.) $)
    isarep2 $p |- E. w w = ( { <. x , y >. | ph } " A ) $=
      vw wph vx vy copab cA cima wph vx vy copab cA cima vx cv cA wcel wph wa
      vx vy copab cA cima cvv wph vx vy copab cA cres cA cima wph vx vy copab
      cA cima vx cv cA wcel wph wa vx vy copab cA cima wph vx vy copab cA
      resima wph vx vy copab cA cres vx cv cA wcel wph wa vx vy copab cA wph vx
      vy cA resopab imaeq1i eqtr3i vx cv cA wcel wph wa vx vy copab wfun vx cv
      cA wcel wph wa vx vy copab cA cima cvv wcel vx cv cA wcel wph wa vx vy
      copab wfun vx cv cA wcel wph wa vy wmo vx vx cv cA wcel wph wa vx vy
      funopab vx cv cA wcel wph wa vy wmo vx cv cA wcel wph vy wmo wi vx cv cA
      wcel wph wph vy vz wsb wa vy cv vz cv wceq wi vz wal vy wal wph vy wmo
      wph wph vy vz wsb wa vy cv vz cv wceq wi vz wal vy wal vx cA isarep2.2
      rspec wph vy vz wph vz nfv mo3 sylibr vx cv cA wcel wph vy moanimv mpbir
      mpgbir vx cv cA wcel wph wa vx vy copab cA isarep2.1 funimaex ax-mp
      eqeltri isseti $.
  $}

  $( Equality theorem for function predicate with domain.  (Contributed by NM,
     1-Aug-1994.) $)
  fneq1 $p |- ( F = G -> ( F Fn A <-> G Fn A ) ) $=
    cF cG wceq cF wfun cF cdm cA wceq wa cG wfun cG cdm cA wceq wa cF cA wfn cG
    cA wfn cF cG wceq cF wfun cG wfun cF cdm cA wceq cG cdm cA wceq cF cG funeq
    cF cG wceq cF cdm cG cdm cA cF cG dmeq eqeq1d anbi12d cF cA df-fn cG cA
    df-fn 3bitr4g $.

  $( Equality theorem for function predicate with domain.  (Contributed by NM,
     1-Aug-1994.) $)
  fneq2 $p |- ( A = B -> ( F Fn A <-> F Fn B ) ) $=
    cA cB wceq cF wfun cF cdm cA wceq wa cF wfun cF cdm cB wceq wa cF cA wfn cF
    cB wfn cA cB wceq cF cdm cA wceq cF cdm cB wceq cF wfun cA cB cF cdm eqeq2
    anbi2d cF cA df-fn cF cB df-fn 3bitr4g $.

  ${
    fneq1d.1 $e |- ( ph -> F = G ) $.
    $( Equality deduction for function predicate with domain.  (Contributed by
       Paul Chapman, 22-Jun-2011.) $)
    fneq1d $p |- ( ph -> ( F Fn A <-> G Fn A ) ) $=
      wph cF cG wceq cF cA wfn cG cA wfn wb fneq1d.1 cA cF cG fneq1 syl $.
  $}

  ${
    fneq2d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for function predicate with domain.  (Contributed by
       Paul Chapman, 22-Jun-2011.) $)
    fneq2d $p |- ( ph -> ( F Fn A <-> F Fn B ) ) $=
      wph cA cB wceq cF cA wfn cF cB wfn wb fneq2d.1 cA cB cF fneq2 syl $.
  $}

  ${
    fneq12d.1 $e |- ( ph -> F = G ) $.
    fneq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for function predicate with domain.  (Contributed by
       NM, 26-Jun-2011.) $)
    fneq12d $p |- ( ph -> ( F Fn A <-> G Fn B ) ) $=
      wph cF cA wfn cG cA wfn cG cB wfn wph cA cF cG fneq12d.1 fneq1d wph cA cB
      cG fneq12d.2 fneq2d bitrd $.
  $}

  ${
    fneq1i.1 $e |- F = G $.
    $( Equality inference for function predicate with domain.  (Contributed by
       Paul Chapman, 22-Jun-2011.) $)
    fneq1i $p |- ( F Fn A <-> G Fn A ) $=
      cF cG wceq cF cA wfn cG cA wfn wb fneq1i.1 cA cF cG fneq1 ax-mp $.
  $}

  ${
    fneq2i.1 $e |- A = B $.
    $( Equality inference for function predicate with domain.  (Contributed by
       NM, 4-Sep-2011.) $)
    fneq2i $p |- ( F Fn A <-> F Fn B ) $=
      cA cB wceq cF cA wfn cF cB wfn wb fneq2i.1 cA cB cF fneq2 ax-mp $.
  $}

  ${
    nffn.1 $e |- F/_ x F $.
    nffn.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for a function with domain.
       (Contributed by NM, 30-Jan-2004.) $)
    nffn $p |- F/ x F Fn A $=
      cF cA wfn cF wfun cF cdm cA wceq wa vx cF cA df-fn cF wfun cF cdm cA wceq
      vx vx cF nffn.1 nffun vx cF cdm cA vx cF nffn.1 nfdm nffn.2 nfeq nfan
      nfxfr $.
  $}

  $( A function with domain is a function.  (Contributed by NM, 1-Aug-1994.) $)
  fnfun $p |- ( F Fn A -> Fun F ) $=
    cF cA wfn cF wfun cF cdm cA wceq cF cA df-fn simplbi $.

  $( A function with domain is a relation.  (Contributed by NM, 1-Aug-1994.) $)
  fnrel $p |- ( F Fn A -> Rel F ) $=
    cF cA wfn cF wfun cF wrel cA cF fnfun cF funrel syl $.

  $( The domain of a function.  (Contributed by NM, 2-Aug-1994.) $)
  fndm $p |- ( F Fn A -> dom F = A ) $=
    cF cA wfn cF wfun cF cdm cA wceq cF cA df-fn simprbi $.

  ${
    funfni.1 $e |- ( ( Fun F /\ B e. dom F ) -> ph ) $.
    $( Inference to convert a function and domain antecedent.  (Contributed by
       NM, 22-Apr-2004.) $)
    funfni $p |- ( ( F Fn A /\ B e. A ) -> ph ) $=
      cF cA wfn cB cA wcel wa cF wfun cB cF cdm wcel wph cF cA wfn cF wfun cB
      cA wcel cA cF fnfun adantr cF cA wfn cB cF cdm wcel cB cA wcel cF cA wfn
      cF cdm cA cB cA cF fndm eleq2d biimpar funfni.1 syl2anc $.
  $}

  $( A function has a unique domain.  (Contributed by NM, 11-Aug-1994.) $)
  fndmu $p |- ( ( F Fn A /\ F Fn B ) -> A = B ) $=
    cF cA wfn cF cB wfn cA cF cdm cB cA cF fndm cB cF fndm sylan9req $.

  $( The first argument of binary relation on a function belongs to the
     function's domain.  (Contributed by NM, 7-May-2004.) $)
  fnbr $p |- ( ( F Fn A /\ B F C ) -> B e. A ) $=
    cF cA wfn cB cC cF wbr cB cF cdm wcel cB cA wcel cF cA wfn cF wrel cB cC cF
    wbr cB cF cdm wcel cA cF fnrel cB cC cF releldm sylan cF cA wfn cB cF cdm
    wcel cB cA wcel cF cA wfn cF cdm cA cB cA cF fndm eleq2d biimpa syldan $.

  $( The first argument of an ordered pair in a function belongs to the
     function's domain.  (Contributed by NM, 8-Aug-1994.) $)
  fnop $p |- ( ( F Fn A /\ <. B , C >. e. F ) -> B e. A ) $=
    cB cC cop cF wcel cF cA wfn cB cC cF wbr cB cA wcel cB cC cF df-br cA cB cC
    cF fnbr sylan2br $.

  ${
    $d x y F $.  $d x y B $.  $d x A $.
    $( There is exactly one value of a function.  (Contributed by NM,
       22-Apr-2004.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    fneu $p |- ( ( F Fn A /\ B e. A ) -> E! y B F y ) $=
      cB vy cv cF wbr vy weu cA cB cF cF wfun cB cF cdm wcel wa cB vy cv cF wbr
      vy wmo cB vy cv cF wbr vy weu cF wfun cB vy cv cF wbr vy wmo cB cF cdm
      wcel vy cB cF funmo adantr cF wfun cB cF cdm wcel wa cB vy cv cF wbr vy
      wex cB vy cv cF wbr vy wmo cB vy cv cF wbr vy weu wb cB cF cdm wcel cB vy
      cv cF wbr vy wex cF wfun cB cF cdm wcel cB vy cv cF wbr vy wex vy cB cF
      cF cdm eldmg ibi adantl cB vy cv cF wbr vy exmoeu2 syl mpbid funfni $.

    $( There is exactly one value of a function.  (Contributed by NM,
       7-Nov-1995.) $)
    fneu2 $p |- ( ( F Fn A /\ B e. A ) -> E! y <. B , y >. e. F ) $=
      cF cA wfn cB cA wcel wa cB vy cv cF wbr vy weu cB vy cv cop cF wcel vy
      weu vy cA cB cF fneu cB vy cv cF wbr cB vy cv cop cF wcel vy cB vy cv cF
      df-br eubii sylib $.
  $}

  $( The union of two functions with disjoint domains.  (Contributed by NM,
     22-Sep-2004.) $)
  fnun $p |- ( ( ( F Fn A /\ G Fn B ) /\ ( A i^i B ) = (/) ) ->
             ( F u. G ) Fn ( A u. B ) ) $=
    cF cA wfn cG cB wfn wa cA cB cin c0 wceq cF cG cun cA cB cun wfn cF cA wfn
    cF wfun cF cdm cA wceq wa cG wfun cG cdm cB wceq wa cA cB cin c0 wceq cF cG
    cun cA cB cun wfn wi cG cB wfn cF cA df-fn cG cB df-fn cF wfun cG wfun cF
    cdm cA wceq cG cdm cB wceq cA cB cin c0 wceq cF cG cun cA cB cun wfn wi cF
    cdm cA wceq cG cdm cB wceq wa cF wfun cG wfun wa cA cB cin c0 wceq cF cG
    cun cA cB cun wfn wi cF cdm cA wceq cG cdm cB wceq wa cF wfun cG wfun wa cA
    cB cin c0 wceq cF cG cun cA cB cun wfn cF cdm cA wceq cG cdm cB wceq wa cF
    wfun cG wfun wa cA cB cin c0 wceq wa cF cG cun wfun cF cG cun cdm cA cB cun
    wceq wa cF cG cun cA cB cun wfn cF cdm cA wceq cG cdm cB wceq wa cF wfun cG
    wfun wa cA cB cin c0 wceq wa cF cG cun wfun cF cG cun cdm cA cB cun wceq cF
    cdm cA wceq cG cdm cB wceq wa cF wfun cG wfun wa cA cB cin c0 wceq wa cF
    wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cF cG cun wfun cF cdm cA wceq
    cG cdm cB wceq wa cF cdm cG cdm cin c0 wceq cA cB cin c0 wceq cF wfun cG
    wfun wa cF cdm cA wceq cG cdm cB wceq wa cF cdm cG cdm cin cA cB cin c0 cF
    cdm cA cG cdm cB ineq12 eqeq1d anbi2d cF cG funun syl6bir cF cdm cA wceq cG
    cdm cB wceq wa cF cG cun cdm cF cdm cG cdm cun cA cB cun cF cG dmun cF cdm
    cA cG cdm cB uneq12 syl5eq jctird cF cG cun cA cB cun df-fn syl6ibr exp3a
    impcom an4s syl2anb imp $.

  ${
    fnunop.x $e |- ( ph -> X e. _V ) $.
    fnunop.y $e |- ( ph -> Y e. _V ) $.
    fnunop.f $e |- ( ph -> F Fn D ) $.
    fnunop.g $e |- G = ( F u. { <. X , Y >. } ) $.
    fnunop.e $e |- E = ( D u. { X } ) $.
    fnunop.d $e |- ( ph -> -. X e. D ) $.
    $( Extension of a function with a new ordered pair.  (Contributed by NM,
       28-Sep-2013.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    fnunsn $p |- ( ph -> G Fn E ) $=
      wph cF cX cY cop csn cun cD cX csn cun wfn cG cE wfn wph cF cD wfn cX cY
      cop csn cX csn wfn cD cX csn cin c0 wceq cF cX cY cop csn cun cD cX csn
      cun wfn fnunop.f wph cX cvv wcel cY cvv wcel cX cY cop csn cX csn wfn
      fnunop.x fnunop.y cX cY cvv cvv fnsng syl2anc wph cX cD wcel wn cD cX csn
      cin c0 wceq fnunop.d cD cX disjsn sylibr cD cX csn cF cX cY cop csn fnun
      syl21anc cG cE wfn cF cX cY cop csn cun cE wfn cF cX cY cop csn cun cD cX
      csn cun wfn cE cG cF cX cY cop csn cun fnunop.g fneq1i cE cD cX csn cun
      cF cX cY cop csn cun fnunop.e fneq2i bitri sylibr $.
  $}

  $( Composition of two functions.  (Contributed by NM, 22-May-2006.) $)
  fnco $p |- ( ( F Fn A /\ G Fn B /\ ran G C_ A ) -> ( F o. G ) Fn B ) $=
    cF cA wfn cG cB wfn cG crn cA wss w3a cF cG ccom wfun cF cG ccom cdm cB
    wceq cF cG ccom cB wfn cF cA wfn cG cB wfn cF cG ccom wfun cG crn cA wss cF
    cA wfn cF wfun cG wfun cF cG ccom wfun cG cB wfn cA cF fnfun cB cG fnfun cF
    cG funco syl2an 3adant3 cF cA wfn cG cB wfn cG crn cA wss w3a cF cG ccom
    cdm cG cdm cB cF cA wfn cG crn cA wss cF cG ccom cdm cG cdm wceq cG cB wfn
    cF cA wfn cG crn cA wss wa cG crn cF cdm wss cF cG ccom cdm cG cdm wceq cF
    cA wfn cG crn cF cdm wss cG crn cA wss cF cA wfn cF cdm cA cG crn cA cF
    fndm sseq2d biimpar cF cG dmcosseq syl 3adant2 cG cB wfn cF cA wfn cG cdm
    cB wceq cG crn cA wss cB cG fndm 3ad2ant2 eqtrd cF cG ccom cB df-fn
    sylanbrc $.

  $( A function does not change when restricted to its domain.  (Contributed by
     NM, 5-Sep-2004.) $)
  fnresdm $p |- ( F Fn A -> ( F |` A ) = F ) $=
    cF cA wfn cF wrel cF cdm cA wss cF cA cres cF wceq cA cF fnrel cF cA wfn cF
    cdm cA wceq cF cdm cA wss cA cF fndm cF cdm cA eqimss syl cF cA relssres
    syl2anc $.

  $( A function restricted to a class disjoint with its domain is empty.
     (Contributed by NM, 23-Sep-2004.) $)
  fnresdisj $p |- ( F Fn A -> ( ( A i^i B ) = (/) <-> ( F |` B ) = (/) ) ) $=
    cF cB cres c0 wceq cF cB cres cdm c0 wceq cF cA wfn cA cB cin c0 wceq cF cB
    cres wrel cF cB cres c0 wceq cF cB cres cdm c0 wceq wb cF cB relres cF cB
    cres reldm0 ax-mp cF cA wfn cF cB cres cdm cA cB cin c0 cF cA wfn cF cB
    cres cdm cF cdm cB cin cA cB cin cF cB cres cdm cB cF cdm cin cF cdm cB cin
    cF cB dmres cB cF cdm incom eqtri cF cA wfn cF cdm cA cB cA cF fndm ineq1d
    syl5eq eqeq1d syl5rbb $.

  $( Membership in two functions restricted by each other's domain.
     (Contributed by NM, 8-Aug-1994.) $)
  2elresin $p |- ( ( F Fn A /\ G Fn B ) ->
                 ( ( <. x , y >. e. F /\ <. x , z >. e. G ) <->
                   ( <. x , y >. e. ( F |` ( A i^i B ) ) /\
                     <. x , z >. e. ( G |` ( A i^i B ) ) ) ) ) $=
    cF cA wfn cG cB wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa
    vx cv vy cv cop cF cA cB cin cres wcel vx cv vz cv cop cG cA cB cin cres
    wcel wa cF cA wfn cG cB wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG
    wcel wa vx cv vy cv cop cF cA cB cin cres wcel vx cv vz cv cop cG cA cB cin
    cres wcel wa cF cA wfn cG cB wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop
    cG wcel wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa vx cv vy cv
    cop cF cA cB cin cres wcel vx cv vz cv cop cG cA cB cin cres wcel wa wi cF
    cA wfn cG cB wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa wa
    vx cv cA cB cin wcel vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa vx
    cv vy cv cop cF cA cB cin cres wcel vx cv vz cv cop cG cA cB cin cres wcel
    wa wi cF cA wfn cG cB wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG
    wcel wa wa vx cv cA wcel vx cv cB wcel wa vx cv cA cB cin wcel cF cA wfn vx
    cv vy cv cop cF wcel cG cB wfn vx cv vz cv cop cG wcel vx cv cA wcel vx cv
    cB wcel wa cF cA wfn vx cv vy cv cop cF wcel wa vx cv cA wcel cG cB wfn vx
    cv vz cv cop cG wcel wa vx cv cB wcel cA vx cv vy cv cF fnop cB vx cv vz cv
    cG fnop anim12i an4s vx cv cA cB elin sylibr vx cv cA cB cin wcel vx cv vy
    cv cop cF cA cB cin cres wcel vx cv vz cv cop cG cA cB cin cres wcel wa vx
    cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa vx cv cA cB cin wcel vx cv
    vy cv cop cF cA cB cin cres wcel vx cv vy cv cop cF wcel vx cv vz cv cop cG
    cA cB cin cres wcel vx cv vz cv cop cG wcel vx cv vy cv cF cA cB cin vy vex
    opres vx cv vz cv cG cA cB cin vz vex opres anbi12d biimprd syl ex pm2.43d
    vx cv vy cv cop cF cA cB cin cres wcel vx cv vy cv cop cF wcel vx cv vz cv
    cop cG cA cB cin cres wcel vx cv vz cv cop cG wcel cF cA cB cin cres cF vx
    cv vy cv cop cF cA cB cin resss sseli cG cA cB cin cres cG vx cv vz cv cop
    cG cA cB cin resss sseli anim12i impbid1 $.

  $( Restriction of a function with a subclass of its domain.  (Contributed by
     NM, 10-Oct-2007.) $)
  fnssresb $p |- ( F Fn A -> ( ( F |` B ) Fn B <-> B C_ A ) ) $=
    cF cB cres cB wfn cF cB cres wfun cF cB cres cdm cB wceq wa cF cA wfn cB cA
    wss cF cB cres cB df-fn cF cA wfn cF cB cres cdm cB wceq cF cB cres wfun cF
    cB cres cdm cB wceq wa cB cA wss cF cA wfn cF cB cres wfun cF cB cres cdm
    cB wceq cF cA wfn cF wfun cF cB cres wfun cA cF fnfun cB cF funres syl
    biantrurd cF cB cres cdm cB wceq cB cF cdm wss cF cA wfn cB cA wss cB cF
    ssdmres cF cA wfn cF cdm cA cB cA cF fndm sseq2d syl5bbr bitr3d syl5bb $.

  $( Restriction of a function with a subclass of its domain.  (Contributed by
     NM, 2-Aug-1994.) $)
  fnssres $p |- ( ( F Fn A /\ B C_ A ) -> ( F |` B ) Fn B ) $=
    cF cA wfn cF cB cres cB wfn cB cA wss cA cB cF fnssresb biimpar $.

  $( Restriction of a function's domain with an intersection.  (Contributed by
     NM, 9-Aug-1994.) $)
  fnresin1 $p |- ( F Fn A -> ( F |` ( A i^i B ) ) Fn ( A i^i B ) ) $=
    cF cA wfn cA cB cin cA wss cF cA cB cin cres cA cB cin wfn cA cB inss1 cA
    cA cB cin cF fnssres mpan2 $.

  $( Restriction of a function's domain with an intersection.  (Contributed by
     NM, 9-Aug-1994.) $)
  fnresin2 $p |- ( F Fn A -> ( F |` ( B i^i A ) ) Fn ( B i^i A ) ) $=
    cF cA wfn cB cA cin cA wss cF cB cA cin cres cB cA cin wfn cB cA inss2 cA
    cB cA cin cF fnssres mpan2 $.

  ${
    $d x y A $.  $d x y F $.
    $( An equivalence for functionality of a restriction.  Compare ~ dffun8 .
       (Contributed by Mario Carneiro, 20-May-2015.) $)
    fnres $p |- ( ( F |` A ) Fn A <-> A. x e. A E! y x F y ) $=
      cF cA cres wfun cF cA cres cdm cA wceq wa vx cv vy cv cF wbr vy wex vx cv
      vy cv cF wbr vy wmo wa vx cA wral cF cA cres cA wfn vx cv vy cv cF wbr vy
      weu vx cA wral vx cv vy cv cF wbr vy wmo vx cA wral vx cv vy cv cF wbr vy
      wex vx cA wral wa vx cv vy cv cF wbr vy wex vx cA wral vx cv vy cv cF wbr
      vy wmo vx cA wral wa cF cA cres wfun cF cA cres cdm cA wceq wa vx cv vy
      cv cF wbr vy wex vx cv vy cv cF wbr vy wmo wa vx cA wral vx cv vy cv cF
      wbr vy wmo vx cA wral vx cv vy cv cF wbr vy wex vx cA wral ancom cF cA
      cres wfun vx cv vy cv cF wbr vy wmo vx cA wral cF cA cres cdm cA wceq vx
      cv vy cv cF wbr vy wex vx cA wral vx cv vy cv cF cA cres wbr vy wmo vx
      wal vx cv cA wcel vx cv vy cv cF wbr vy wmo wi vx wal cF cA cres wfun vx
      cv vy cv cF wbr vy wmo vx cA wral vx cv vy cv cF cA cres wbr vy wmo vx cv
      cA wcel vx cv vy cv cF wbr vy wmo wi vx vx cv vy cv cF cA cres wbr vy wmo
      vx cv cA wcel vx cv vy cv cF wbr wa vy wmo vx cv cA wcel vx cv vy cv cF
      wbr vy wmo wi vx cv vy cv cF cA cres wbr vx cv cA wcel vx cv vy cv cF wbr
      wa vy vx cv vy cv cF cA cres wbr vx cv vy cv cF wbr vx cv cA wcel wa vx
      cv cA wcel vx cv vy cv cF wbr wa vx cv vy cv cF cA vy vex brres vx cv vy
      cv cF wbr vx cv cA wcel ancom bitri mobii vx cv cA wcel vx cv vy cv cF
      wbr vy moanimv bitri albii cF cA cres wfun cF cA cres wrel vx cv vy cv cF
      cA cres wbr vy wmo vx wal cF cA relres vx vy cF cA cres dffun6 mpbiran vx
      cv vy cv cF wbr vy wmo vx cA df-ral 3bitr4i cF cA cres cdm cA wceq cA cF
      cA cres cdm wss vx cv vy cv cF wbr vy wex vx cA wral cF cA cres cdm cA
      wceq cF cA cres cdm cA wss cA cF cA cres cdm wss cF cA cres cdm cA cF cdm
      cin cA cF cA dmres cA cF cdm inss1 eqsstri cF cA cres cdm cA eqss mpbiran
      cA cF cA cres cdm wss vx cv cF cA cres cdm wcel vx cA wral vx cv vy cv cF
      wbr vy wex vx cA wral vx cA cF cA cres cdm dfss3 vx cv cF cA cres cdm
      wcel vx cv vy cv cF wbr vy wex vx cA vx cv cA wcel vx cv cF cA cres cdm
      wcel vx cv cF cdm wcel vx cv vy cv cF wbr vy wex vx cv cF cA cres cdm
      wcel vx cv cA wcel vx cv cF cdm wcel vx cv cA cF cdm cF cA cres cdm cF cA
      dmres elin2 baib vy vx cv cF vx vex eldm syl6bb ralbiia bitri bitri
      anbi12i vx cv vy cv cF wbr vy wex vx cv vy cv cF wbr vy wmo vx cA r19.26
      3bitr4i cF cA cres cA df-fn vx cv vy cv cF wbr vy weu vx cv vy cv cF wbr
      vy wex vx cv vy cv cF wbr vy wmo wa vx cA vx cv vy cv cF wbr vy eu5
      ralbii 3bitr4i $.
  $}

  $( Functionality and domain of restricted identity.  (Contributed by NM,
     27-Aug-2004.) $)
  fnresi $p |- ( _I |` A ) Fn A $=
    cid cA cres cA wfn cid cA cres wfun cid cA cres cdm cA wceq cid wfun cid cA
    cres wfun funi cA cid funres ax-mp cA dmresi cid cA cres cA df-fn mpbir2an
    $.

  $( The image of a function's domain is its range.  (Contributed by NM,
     4-Nov-2004.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
  fnima $p |- ( F Fn A -> ( F " A ) = ran F ) $=
    cF cA wfn cF cA cima cF cA cres crn cF crn cF cA df-ima cF cA wfn cF cA
    cres cF cA cF fnresdm rneqd syl5eq $.

  ${
    $d x y F $.
    $( A function with empty domain is empty.  (Contributed by NM,
       15-Apr-1998.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    fn0 $p |- ( F Fn (/) <-> F = (/) ) $=
      cF c0 wfn cF c0 wceq cF c0 wfn cF wrel cF cdm c0 wceq cF c0 wceq c0 cF
      fnrel c0 cF fndm cF wrel cF c0 wceq cF cdm c0 wceq cF reldm0 biimpar
      syl2anc cF c0 wceq cF c0 wfn c0 c0 wfn c0 c0 wfn c0 wfun c0 cdm c0 wceq
      fun0 dm0 c0 c0 df-fn mpbir2an c0 cF c0 fneq1 mpbiri impbii $.
  $}

  $( A class that is disjoint with the domain of a function has an empty image
     under the function.  (Contributed by FL, 24-Jan-2007.) $)
  fnimadisj $p |- ( ( F Fn A /\ ( A i^i C ) = (/) ) -> ( F " C ) = (/) ) $=
    cF cA wfn cA cC cin c0 wceq wa cF cdm cC cin c0 wceq cF cC cima c0 wceq cF
    cA wfn cF cdm cC cin c0 wceq cA cC cin c0 wceq cF cA wfn cF cdm cC cin cA
    cC cin c0 cF cA wfn cF cdm cA cC cA cF fndm ineq1d eqeq1d biimpar cF cC
    imadisj sylibr $.

  $( Images under a function never map nonempty sets to empty sets.
     _EDITORIAL_: usable in ~ fnwe2lem2 .  (Contributed by Stefan O'Rear,
     21-Jan-2015.) $)
  fnimaeq0 $p |- ( ( F Fn A /\ B C_ A ) ->
      ( ( F " B ) = (/) <-> B = (/) ) ) $=
    cF cB cima c0 wceq cF cdm cB cin c0 wceq cF cA wfn cB cA wss wa cB c0 wceq
    cF cB imadisj cF cA wfn cB cA wss wa cF cdm cB cin cB c0 cF cA wfn cB cA
    wss wa cF cdm cB cin cB cF cdm cin cB cF cdm cB incom cF cA wfn cB cA wss
    wa cB cF cdm wss cB cF cdm cin cB wceq cF cA wfn cB cF cdm wss cB cA wss cF
    cA wfn cF cdm cA cB cA cF fndm sseq2d biimpar cB cF cdm df-ss sylib syl5eq
    eqeq1d syl5bb $.

  ${
    $d y z A $.  $d y z B $.  $d x y z $.
    $( Alternate definition for the "maps to" notation ~ df-mpt .  (Contributed
       by Mario Carneiro, 30-Dec-2016.) $)
    dfmpt3 $p |- ( x e. A |-> B ) = U_ x e. A ( { x } X. { B } ) $=
      vx cA cB cmpt vx cv cA wcel vy cv cB wceq wa vx vy copab vx cA vx cv csn
      cB csn cxp ciun vx vy cA cB df-mpt vz vx cA vx cv csn cB csn cxp ciun vx
      cv cA wcel vy cv cB wceq wa vx vy copab vz cv vx cv vy cv cop wceq vx cv
      cA wcel vy cv cB csn wcel wa wa vy wex vx wex vz cv vx cv vy cv cop wceq
      vx cv cA wcel vy cv cB wceq wa wa vy wex vx wex vz cv vx cA vx cv csn cB
      csn cxp ciun wcel vz cv vx cv cA wcel vy cv cB wceq wa vx vy copab wcel
      vz cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB csn wcel wa wa vz cv vx
      cv vy cv cop wceq vx cv cA wcel vy cv cB wceq wa wa vx vy vx cv cA wcel
      vy cv cB csn wcel wa vx cv cA wcel vy cv cB wceq wa vz cv vx cv vy cv cop
      wceq vy cv cB csn wcel vy cv cB wceq vx cv cA wcel vy cB elsn anbi2i
      anbi2i 2exbii vx vy cA cB csn vz cv eliunxp vx cv cA wcel vy cv cB wceq
      wa vx vy vz cv elopab 3bitr4i eqriv eqtr4i $.
  $}

  ${
    $d x y z A $.  $d z F $.  $d x y z w $.
    fnopabg.1 $e |- F = { <. x , y >. | ( x e. A /\ ph ) } $.
    $( Functionality and domain of an ordered-pair class abstraction.
       (Contributed by NM, 30-Jan-2004.)  (Proof shortened by Mario Carneiro,
       4-Dec-2016.) $)
    fnopabg $p |- ( A. x e. A E! y ph <-> F Fn A ) $=
      wph vy wmo wph vy wex wa vx cA wral vx cv cA wcel wph wa vx vy copab cA
      wfn wph vy weu vx cA wral cF cA wfn wph vy wmo vx cA wral wph vy wex vx
      cA wral wa vx cv cA wcel wph wa vx vy copab wfun vx cv cA wcel wph wa vx
      vy copab cdm cA wceq wa wph vy wmo wph vy wex wa vx cA wral vx cv cA wcel
      wph wa vx vy copab cA wfn wph vy wmo vx cA wral vx cv cA wcel wph wa vx
      vy copab wfun wph vy wex vx cA wral vx cv cA wcel wph wa vx vy copab cdm
      cA wceq vx cv cA wcel wph wa vy wmo vx wal vx cv cA wcel wph vy wmo wi vx
      wal vx cv cA wcel wph wa vx vy copab wfun wph vy wmo vx cA wral vx cv cA
      wcel wph wa vy wmo vx cv cA wcel wph vy wmo wi vx vx cv cA wcel wph vy
      moanimv albii vx cv cA wcel wph wa vx vy funopab wph vy wmo vx cA df-ral
      3bitr4ri wph vx vy cA dmopab3 anbi12i wph vy wmo wph vy wex vx cA r19.26
      vx cv cA wcel wph wa vx vy copab cA df-fn 3bitr4i wph vy weu wph vy wmo
      wph vy wex wa vx cA wph vy weu wph vy wex wph vy wmo wa wph vy wmo wph vy
      wex wa wph vy eu5 wph vy wex wph vy wmo ancom bitri ralbii cA cF vx cv cA
      wcel wph wa vx vy copab fnopabg.1 fneq1i 3bitr4i $.
  $}

  ${
    $d x y A $.
    fnopab.1 $e |- ( x e. A -> E! y ph ) $.
    fnopab.2 $e |- F = { <. x , y >. | ( x e. A /\ ph ) } $.
    $( Functionality and domain of an ordered-pair class abstraction.
       (Contributed by NM, 5-Mar-1996.) $)
    fnopab $p |- F Fn A $=
      wph vy weu vx cA wral cF cA wfn wph vy weu vx cA fnopab.1 rgen wph vx vy
      cA cF fnopab.2 fnopabg mpbi $.
  $}

  ${
    $d x y A $.  $d y B $.
    mptfng.1 $e |- F = ( x e. A |-> B ) $.
    $( The maps-to notation defines a function with domain.  (Contributed by
       Scott Fenton, 21-Mar-2011.) $)
    mptfng $p |- ( A. x e. A B e. _V <-> F Fn A ) $=
      cB cvv wcel vx cA wral vy cv cB wceq vy weu vx cA wral cF cA wfn cB cvv
      wcel vy cv cB wceq vy weu vx cA vy cB eueq ralbii vy cv cB wceq vx vy cA
      cF cF vx cA cB cmpt vx cv cA wcel vy cv cB wceq wa vx vy copab mptfng.1
      vx vy cA cB df-mpt eqtri fnopabg bitri $.

    $( The maps-to notation defines a function with domain.  (Contributed by
       NM, 9-Apr-2013.) $)
    fnmpt $p |- ( A. x e. A B e. V -> F Fn A ) $=
      cB cV wcel vx cA wral cB cvv wcel vx cA wral cF cA wfn cB cV wcel cB cvv
      wcel vx cA cB cV elex ralimi vx cA cB cF mptfng.1 mptfng sylib $.
  $}

  $( A mapping operation with empty domain.  (Contributed by Mario Carneiro,
     28-Dec-2014.) $)
  mpt0 $p |- ( x e. (/) |-> A ) = (/) $=
    vx c0 cA cmpt c0 wfn vx c0 cA cmpt c0 wceq cA cvv wcel vx c0 wral vx c0 cA
    cmpt c0 wfn cA cvv wcel vx ral0 vx c0 cA vx c0 cA cmpt cvv vx c0 cA cmpt
    eqid fnmpt ax-mp vx c0 cA cmpt fn0 mpbi $.

  ${
    $d x y A $.  $d y B $.
    fnmpti.1 $e |- B e. _V $.
    fnmpti.2 $e |- F = ( x e. A |-> B ) $.
    $( Functionality and domain of an ordered-pair class abstraction.
       (Contributed by NM, 29-Jan-2004.)  (Revised by Mario Carneiro,
       31-Aug-2015.) $)
    fnmpti $p |- F Fn A $=
      cB cvv wcel vx cA wral cF cA wfn cB cvv wcel vx cA fnmpti.1 rgenw vx cA
      cB cF fnmpti.2 mptfng mpbi $.

    $( Domain of an ordered-pair class abstraction that specifies a function.
       (Contributed by NM, 6-Sep-2005.)  (Revised by Mario Carneiro,
       31-Aug-2015.) $)
    dmmpti $p |- dom F = A $=
      cF cA wfn cF cdm cA wceq vx cA cB cF fnmpti.1 fnmpti.2 fnmpti cA cF fndm
      ax-mp $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( Union of mappings which are mutually compatible.  (Contributed by Mario
       Carneiro, 31-Aug-2015.) $)
    mptun $p |- ( x e. ( A u. B ) |-> C ) =
        ( ( x e. A |-> C ) u. ( x e. B |-> C ) ) $=
      vx cA cB cun cC cmpt vx cv cA cB cun wcel vy cv cC wceq wa vx vy copab vx
      cA cC cmpt vx cB cC cmpt cun vx vy cA cB cun cC df-mpt vx cA cC cmpt vx
      cB cC cmpt cun vx cv cA wcel vy cv cC wceq wa vx vy copab vx cv cB wcel
      vy cv cC wceq wa vx vy copab cun vx cv cA cB cun wcel vy cv cC wceq wa vx
      vy copab vx cA cC cmpt vx cv cA wcel vy cv cC wceq wa vx vy copab vx cB
      cC cmpt vx cv cB wcel vy cv cC wceq wa vx vy copab vx vy cA cC df-mpt vx
      vy cB cC df-mpt uneq12i vx cv cA cB cun wcel vy cv cC wceq wa vx vy copab
      vx cv cA wcel vy cv cC wceq wa vx cv cB wcel vy cv cC wceq wa wo vx vy
      copab vx cv cA wcel vy cv cC wceq wa vx vy copab vx cv cB wcel vy cv cC
      wceq wa vx vy copab cun vx cv cA cB cun wcel vy cv cC wceq wa vx cv cA
      wcel vy cv cC wceq wa vx cv cB wcel vy cv cC wceq wa wo vx vy vx cv cA cB
      cun wcel vy cv cC wceq wa vx cv cA wcel vx cv cB wcel wo vy cv cC wceq wa
      vx cv cA wcel vy cv cC wceq wa vx cv cB wcel vy cv cC wceq wa wo vx cv cA
      cB cun wcel vx cv cA wcel vx cv cB wcel wo vy cv cC wceq vx cv cA cB elun
      anbi1i vx cv cA wcel vx cv cB wcel vy cv cC wceq andir bitri opabbii vx
      cv cA wcel vy cv cC wceq wa vx cv cB wcel vy cv cC wceq wa vx vy unopab
      eqtr4i eqtr4i eqtr4i $.
  $}

  $( Equality theorem for functions.  (Contributed by NM, 1-Aug-1994.) $)
  feq1 $p |- ( F = G -> ( F : A --> B <-> G : A --> B ) ) $=
    cF cG wceq cF cA wfn cF crn cB wss wa cG cA wfn cG crn cB wss wa cA cB cF
    wf cA cB cG wf cF cG wceq cF cA wfn cG cA wfn cF crn cB wss cG crn cB wss
    cA cF cG fneq1 cF cG wceq cF crn cG crn cB cF cG rneq sseq1d anbi12d cA cB
    cF df-f cA cB cG df-f 3bitr4g $.

  $( Equality theorem for functions.  (Contributed by NM, 1-Aug-1994.) $)
  feq2 $p |- ( A = B -> ( F : A --> C <-> F : B --> C ) ) $=
    cA cB wceq cF cA wfn cF crn cC wss wa cF cB wfn cF crn cC wss wa cA cC cF
    wf cB cC cF wf cA cB wceq cF cA wfn cF cB wfn cF crn cC wss cA cB cF fneq2
    anbi1d cA cC cF df-f cB cC cF df-f 3bitr4g $.

  $( Equality theorem for functions.  (Contributed by NM, 1-Aug-1994.) $)
  feq3 $p |- ( A = B -> ( F : C --> A <-> F : C --> B ) ) $=
    cA cB wceq cF cC wfn cF crn cA wss wa cF cC wfn cF crn cB wss wa cC cA cF
    wf cC cB cF wf cA cB wceq cF crn cA wss cF crn cB wss cF cC wfn cA cB cF
    crn sseq2 anbi2d cC cA cF df-f cC cB cF df-f 3bitr4g $.

  $( Equality theorem for functions.  (Contributed by FL, 14-Jul-2007.)  (Proof
     shortened by Andrew Salmon, 17-Sep-2011.) $)
  feq23 $p |- ( ( A = C /\ B = D ) -> ( F : A --> B <-> F : C --> D ) ) $=
    cA cC wceq cA cB cF wf cC cB cF wf cB cD wceq cC cD cF wf cA cC cB cF feq2
    cB cD cC cF feq3 sylan9bb $.

  ${
    feq1d.1 $e |- ( ph -> F = G ) $.
    $( Equality deduction for functions.  (Contributed by NM, 19-Feb-2008.) $)
    feq1d $p |- ( ph -> ( F : A --> B <-> G : A --> B ) ) $=
      wph cF cG wceq cA cB cF wf cA cB cG wf wb feq1d.1 cA cB cF cG feq1 syl $.
  $}

  ${
    feq2d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for functions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    feq2d $p |- ( ph -> ( F : A --> C <-> F : B --> C ) ) $=
      wph cA cB wceq cA cC cF wf cB cC cF wf wb feq2d.1 cA cB cC cF feq2 syl $.
  $}

  ${
    feq12d.1 $e |- ( ph -> F = G ) $.
    feq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for functions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    feq12d $p |- ( ph -> ( F : A --> C <-> G : B --> C ) ) $=
      wph cA cC cF wf cA cC cG wf cB cC cG wf wph cA cC cF cG feq12d.1 feq1d
      wph cA cB cC cG feq12d.2 feq2d bitrd $.

    feq123d.3 $e |- ( ph -> C = D ) $.
    $( Equality deduction for functions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    feq123d $p |- ( ph -> ( F : A --> C <-> G : B --> D ) ) $=
      wph cA cC cF wf cB cC cG wf cB cD cG wf wph cA cB cC cF cG feq12d.1
      feq12d.2 feq12d wph cC cD wceq cB cC cG wf cB cD cG wf wb feq123d.3 cC cD
      cB cG feq3 syl bitrd $.
  $}

  ${
    feq1i.1 $e |- F = G $.
    $( Equality inference for functions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    feq1i $p |- ( F : A --> B <-> G : A --> B ) $=
      cF cG wceq cA cB cF wf cA cB cG wf wb feq1i.1 cA cB cF cG feq1 ax-mp $.
  $}

  ${
    feq2i.1 $e |- A = B $.
    $( Equality inference for functions.  (Contributed by NM, 5-Sep-2011.) $)
    feq2i $p |- ( F : A --> C <-> F : B --> C ) $=
      cA cB wceq cA cC cF wf cB cC cF wf wb feq2i.1 cA cB cC cF feq2 ax-mp $.
  $}

  ${
    feq23i.1 $e |- A = C $.
    feq23i.2 $e |- B = D $.
    $( Equality inference for functions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    feq23i $p |- ( F : A --> B <-> F : C --> D ) $=
      cA cC wceq cB cD wceq cA cB cF wf cC cD cF wf wb feq23i.1 feq23i.2 cA cB
      cC cD cF feq23 mp2an $.
  $}

  ${
    feq23d.1 $e |- ( ph -> A = C ) $.
    feq23d.2 $e |- ( ph -> B = D ) $.
    $( Equality deduction for functions.  (Contributed by NM, 8-Jun-2013.) $)
    feq23d $p |- ( ph -> ( F : A --> B <-> F : C --> D ) ) $=
      wph cA cC cB cD cF cF wph cF eqidd feq23d.1 feq23d.2 feq123d $.
  $}

  ${
    $d y F $.  $d y A $.  $d y B $.  $d x y $.
    nff.1 $e |- F/_ x F $.
    nff.2 $e |- F/_ x A $.
    nff.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for a mapping.  (Contributed by NM,
       29-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nff $p |- F/ x F : A --> B $=
      cA cB cF wf cF cA wfn cF crn cB wss wa vx cA cB cF df-f cF cA wfn cF crn
      cB wss vx vx cA cF nff.1 nff.2 nffn vx cF crn cB vx cF nff.1 nfrn nff.3
      nfss nfan nfxfr $.
  $}

  ${
    elimf.1 $e |- G : A --> B $.
    $( Eliminate a mapping hypothesis for the weak deduction theorem ~ dedth ,
       when a special case ` G : A --> B ` is provable, in order to convert
       ` F : A --> B ` from a hypothesis to an antecedent.  (Contributed by NM,
       24-Aug-2006.) $)
    elimf $p |- if ( F : A --> B , F , G ) : A --> B $=
      cA cB cF wf cA cB cA cB cF wf cF cG cif wf cA cB cG wf cF cG cA cB cF cA
      cB cF wf cF cG cif feq1 cA cB cG cA cB cF wf cF cG cif feq1 elimf.1
      elimhyp $.
  $}

  $( A mapping is a function.  (Contributed by NM, 2-Aug-1994.) $)
  ffn $p |- ( F : A --> B -> F Fn A ) $=
    cA cB cF wf cF cA wfn cF crn cB wss cA cB cF df-f simplbi $.

  $( Any function is a mapping into ` _V ` .  (Contributed by NM,
     31-Oct-1995.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
  dffn2 $p |- ( F Fn A <-> F : A --> _V ) $=
    cF cA wfn cF cA wfn cF crn cvv wss wa cA cvv cF wf cF crn cvv wss cF cA wfn
    cF crn ssv biantru cA cvv cF df-f bitr4i $.

  $( A mapping is a function.  (Contributed by NM, 3-Aug-1994.) $)
  ffun $p |- ( F : A --> B -> Fun F ) $=
    cA cB cF wf cF cA wfn cF wfun cA cB cF ffn cA cF fnfun syl $.

  $( A mapping is a relation.  (Contributed by NM, 3-Aug-1994.) $)
  frel $p |- ( F : A --> B -> Rel F ) $=
    cA cB cF wf cF cA wfn cF wrel cA cB cF ffn cA cF fnrel syl $.

  $( The domain of a mapping.  (Contributed by NM, 2-Aug-1994.) $)
  fdm $p |- ( F : A --> B -> dom F = A ) $=
    cA cB cF wf cF cA wfn cF cdm cA wceq cA cB cF ffn cA cF fndm syl $.

  ${
    fdmi.1 $e |- F : A --> B $.
    $( The domain of a mapping.  (Contributed by NM, 28-Jul-2008.) $)
    fdmi $p |- dom F = A $=
      cA cB cF wf cF cdm cA wceq fdmi.1 cA cB cF fdm ax-mp $.
  $}

  $( The range of a mapping.  (Contributed by NM, 3-Aug-1994.) $)
  frn $p |- ( F : A --> B -> ran F C_ B ) $=
    cA cB cF wf cF cA wfn cF crn cB wss cA cB cF df-f simprbi $.

  $( A function maps to its range.  (Contributed by NM, 1-Sep-1999.) $)
  dffn3 $p |- ( F Fn A <-> F : A --> ran F ) $=
    cF cA wfn cF cA wfn cF crn cF crn wss wa cA cF crn cF wf cF crn cF crn wss
    cF cA wfn cF crn ssid biantru cA cF crn cF df-f bitr4i $.

  $( Expanding the codomain of a mapping.  (Contributed by NM, 10-May-1998.)
     (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
  fss $p |- ( ( F : A --> B /\ B C_ C ) -> F : A --> C ) $=
    cB cC wss cA cB cF wf cA cC cF wf cB cC wss cF cA wfn cF crn cB wss wa cF
    cA wfn cF crn cC wss wa cA cB cF wf cA cC cF wf cB cC wss cF crn cB wss cF
    crn cC wss cF cA wfn cF crn cB wss cB cC wss cF crn cC wss cF crn cB cC
    sstr2 com12 anim2d cA cB cF df-f cA cC cF df-f 3imtr4g impcom $.

  $( Composition of two mappings.  (Contributed by NM, 29-Aug-1999.)  (Proof
     shortened by Andrew Salmon, 17-Sep-2011.) $)
  fco $p |- ( ( F : B --> C /\ G : A --> B ) -> ( F o. G ) : A --> C ) $=
    cB cC cF wf cA cB cG wf wa cF cG ccom cA wfn cF cG ccom crn cC wss wa cA cC
    cF cG ccom wf cB cC cF wf cF cB wfn cF crn cC wss wa cG cA wfn cG crn cB
    wss wa cF cG ccom cA wfn cF cG ccom crn cC wss wa cA cB cG wf cB cC cF df-f
    cA cB cG df-f cF cB wfn cF crn cC wss wa cG cA wfn cG crn cB wss wa cF cG
    ccom cA wfn cF cG ccom crn cC wss wa cF cB wfn cF crn cC wss wa cG cA wfn
    cG crn cB wss wa cF cG ccom cA wfn cF cG ccom crn cC wss cF cB wfn cG cA
    wfn cG crn cB wss wa cF cG ccom cA wfn wi cF crn cC wss cF cB wfn cG cA wfn
    cG crn cB wss cF cG ccom cA wfn cB cA cF cG fnco 3expib adantr cF crn cC
    wss cF cG ccom crn cC wss cF cB wfn cF cG ccom crn cF crn wss cF crn cC wss
    cF cG ccom crn cC wss cF cG rncoss cF cG ccom crn cF crn cC sstr mpan
    adantl jctird imp syl2anb cA cC cF cG ccom df-f sylibr $.

  $( Functionality of a composition with weakened out of domain condition on
     the first argument.  (Contributed by Stefan O'Rear, 11-Mar-2015.) $)
  fco2 $p |- ( ( ( F |` B ) : B --> C /\ G : A --> B ) ->
      ( F o. G ) : A --> C ) $=
    cB cC cF cB cres wf cA cB cG wf wa cA cC cF cB cres cG ccom wf cA cC cF cG
    ccom wf cA cB cC cF cB cres cG fco cB cC cF cB cres wf cA cB cG wf wa cA cC
    cF cB cres cG ccom cF cG ccom cA cB cG wf cF cB cres cG ccom cF cG ccom
    wceq cB cC cF cB cres wf cA cB cG wf cG crn cB wss cF cB cres cG ccom cF cG
    ccom wceq cA cB cG frn cF cG cB cores syl adantl feq1d mpbid $.

  $( A mapping is a class of ordered pairs.  (Contributed by NM, 3-Aug-1994.)
     (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
  fssxp $p |- ( F : A --> B -> F C_ ( A X. B ) ) $=
    cA cB cF wf cF cF cdm cF crn cxp cA cB cxp cA cB cF wf cF wrel cF cF cdm cF
    crn cxp wss cA cB cF frel cF relssdmrn syl cA cB cF wf cF cdm cA wss cF crn
    cB wss cF cdm cF crn cxp cA cB cxp wss cA cB cF wf cF cdm cA wceq cF cdm cA
    wss cA cB cF fdm cF cdm cA eqimss syl cA cB cF frn cF cdm cA cF crn cB
    xpss12 syl2anc sstrd $.

  $( A function with bounded domain and range is a set.  This version of ~ fex
     is proven without the Axiom of Replacement.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)
  fex2 $p |- ( ( F : A --> B /\ A e. V /\ B e. W ) -> F e. _V ) $=
    cA cB cF wf cA cV wcel cB cW wcel w3a cF cA cB cxp wss cA cB cxp cvv wcel
    cF cvv wcel cA cB cF wf cA cV wcel cF cA cB cxp wss cB cW wcel cA cB cF
    fssxp 3ad2ant1 cA cV wcel cB cW wcel cA cB cxp cvv wcel cA cB cF wf cA cB
    cV cW xpexg 3adant1 cF cA cB cxp cvv ssexg syl2anc $.

  $( Two ways of specifying a partial function from ` A ` to ` B ` .
     (Contributed by NM, 13-Nov-2007.) $)
  funssxp $p |- ( ( Fun F /\ F C_ ( A X. B ) ) <->
             ( F : dom F --> B /\ dom F C_ A ) ) $=
    cF wfun cF cA cB cxp wss wa cF cdm cB cF wf cF cdm cA wss wa cF wfun cF cA
    cB cxp wss wa cF cdm cB cF wf cF cdm cA wss cF wfun cF cA cB cxp wss wa cF
    cF cdm wfn cF crn cB wss wa cF cdm cB cF wf cF wfun cF cF cdm wfn cF cA cB
    cxp wss cF crn cB wss cF wfun cF cF cdm wfn cF funfn biimpi cF cA cB cxp
    wss cF crn cA cB cxp crn cB cF cA cB cxp rnss cA cB rnxpss syl6ss anim12i
    cF cdm cB cF df-f sylibr cF cA cB cxp wss cF cdm cA wss cF wfun cF cA cB
    cxp wss cF cdm cA cB cxp cdm cA cF cA cB cxp dmss cA cB dmxpss syl6ss
    adantl jca cF cdm cB cF wf cF cdm cA wss wa cF wfun cF cA cB cxp wss cF cdm
    cB cF wf cF wfun cF cdm cA wss cF cdm cB cF ffun adantr cF cdm cB cF wf cF
    cdm cA wss cF cF cdm cB cxp cA cB cxp cF cdm cB cF fssxp cF cdm cA cB xpss1
    sylan9ss jca impbii $.

  $( A mapping is a partial function.  (Contributed by NM, 25-Nov-2007.) $)
  ffdm $p |- ( F : A --> B -> ( F : dom F --> B /\ dom F C_ A ) ) $=
    cA cB cF wf cF cdm cB cF wf cF cdm cA wss cA cB cF wf cF cdm cB cF wf cA cB
    cF wf cF cdm cA cB cF cA cB cF fdm feq2d ibir cA cB cF wf cF cdm cA wceq cF
    cdm cA wss cA cB cF fdm cF cdm cA eqimss syl jca $.

  $( The members of an ordered pair element of a mapping belong to the
     mapping's domain and codomain.  (Contributed by NM, 10-Dec-2003.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)
  opelf $p |- ( ( F : A --> B /\ <. C , D >. e. F ) ->
              ( C e. A /\ D e. B ) ) $=
    cA cB cF wf cC cD cop cF wcel cC cA wcel cD cB wcel wa cA cB cF wf cC cD
    cop cF wcel cC cD cop cA cB cxp wcel cC cA wcel cD cB wcel wa cA cB cF wf
    cF cA cB cxp cC cD cop cA cB cF fssxp sseld cC cD cA cB opelxp syl6ib imp
    $.

  $( The union of two functions with disjoint domains.  (Contributed by NM,
     22-Sep-2004.) $)
  fun $p |- ( ( ( F : A --> C /\ G : B --> D ) /\ ( A i^i B ) = (/) ) ->
             ( F u. G ) : ( A u. B ) --> ( C u. D ) ) $=
    cA cB cin c0 wceq cA cC cF wf cB cD cG wf wa cA cB cun cC cD cun cF cG cun
    wf cA cB cin c0 wceq cF cA wfn cG cB wfn wa cF crn cC wss cG crn cD wss wa
    wa cF cG cun cA cB cun wfn cF cG cun crn cC cD cun wss wa cA cC cF wf cB cD
    cG wf wa cA cB cun cC cD cun cF cG cun wf cA cB cin c0 wceq cF cA wfn cG cB
    wfn wa cF cG cun cA cB cun wfn cF crn cC wss cG crn cD wss wa cF cG cun crn
    cC cD cun wss cF cA wfn cG cB wfn wa cA cB cin c0 wceq cF cG cun cA cB cun
    wfn cA cB cF cG fnun expcom cF crn cC wss cG crn cD wss wa cF cG cun crn cC
    cD cun wss wi cA cB cin c0 wceq cF crn cC wss cG crn cD wss wa cF cG cun
    crn cF crn cG crn cun cC cD cun cF cG rnun cF crn cC cG crn cD unss12
    syl5eqss a1i anim12d cA cC cF wf cB cD cG wf wa cF cA wfn cF crn cC wss wa
    cG cB wfn cG crn cD wss wa wa cF cA wfn cG cB wfn wa cF crn cC wss cG crn
    cD wss wa wa cA cC cF wf cF cA wfn cF crn cC wss wa cB cD cG wf cG cB wfn
    cG crn cD wss wa cA cC cF df-f cB cD cG df-f anbi12i cF cA wfn cF crn cC
    wss cG cB wfn cG crn cD wss an4 bitri cA cB cun cC cD cun cF cG cun df-f
    3imtr4g impcom $.

  $( The union of two functions with disjoint domains.  (Contributed by Mario
     Carneiro, 12-Mar-2015.) $)
  fun2 $p |- ( ( ( F : A --> C /\ G : B --> C ) /\ ( A i^i B ) = (/) ) ->
             ( F u. G ) : ( A u. B ) --> C ) $=
    cA cC cF wf cB cC cG wf wa cA cB cin c0 wceq wa cA cB cun cC cC cun cF cG
    cun wf cA cB cun cC cF cG cun wf cA cB cC cC cF cG fun cC cC cun cC wceq cA
    cB cun cC cC cun cF cG cun wf cA cB cun cC cF cG cun wf wb cC unidm cC cC
    cun cC cA cB cun cF cG cun feq3 ax-mp sylib $.

  $( Composition of two functions.  (Contributed by NM, 22-May-2006.) $)
  fnfco $p |- ( ( F Fn A /\ G : B --> A ) -> ( F o. G ) Fn B ) $=
    cB cA cG wf cF cA wfn cG cB wfn cG crn cA wss wa cF cG ccom cB wfn cB cA cG
    df-f cF cA wfn cG cB wfn cG crn cA wss cF cG ccom cB wfn cA cB cF cG fnco
    3expb sylan2b $.

  $( Restriction of a function with a subclass of its domain.  (Contributed by
     NM, 23-Sep-2004.) $)
  fssres $p |- ( ( F : A --> B /\ C C_ A ) -> ( F |` C ) : C --> B ) $=
    cA cB cF wf cC cA wss wa cF cC cres cC wfn cF cC cres crn cB wss wa cC cB
    cF cC cres wf cA cB cF wf cF cA wfn cF crn cB wss wa cC cA wss cF cC cres
    cC wfn cF cC cres crn cB wss wa cA cB cF df-f cF cA wfn cC cA wss cF crn cB
    wss cF cC cres cC wfn cF cC cres crn cB wss wa cF cA wfn cC cA wss wa cF cC
    cres cC wfn cF crn cB wss cF cC cres crn cB wss cA cC cF fnssres cF cC cres
    crn cF crn wss cF crn cB wss cF cC cres crn cB wss cF cC cres cF wss cF cC
    cres crn cF crn wss cF cC resss cF cC cres cF rnss ax-mp cF cC cres crn cF
    crn cB sstr mpan anim12i an32s sylanb cC cB cF cC cres df-f sylibr $.

  $( Restriction of a restricted function with a subclass of its domain.
     (Contributed by NM, 21-Jul-2005.) $)
  fssres2 $p |- ( ( ( F |` A ) : A --> B /\ C C_ A ) ->
                ( F |` C ) : C --> B ) $=
    cA cB cF cA cres wf cC cA wss wa cC cB cF cA cres cC cres wf cC cB cF cC
    cres wf cA cB cC cF cA cres fssres cC cA wss cC cB cF cA cres cC cres wf cC
    cB cF cC cres wf wb cA cB cF cA cres wf cC cA wss cC cB cF cA cres cC cres
    cF cC cres cF cC cA resabs1 feq1d adantl mpbid $.

  $( An identity for the mapping relationship under restriction.  (Contributed
     by Scott Fenton, 4-Sep-2011.)  (Proof shortened by Mario Carneiro,
     26-May-2016.) $)
  fresin $p |- ( F : A --> B -> ( F |` X ) : ( A i^i X ) --> B ) $=
    cA cB cF wf cA cX cin cB cF cA cX cin cres wf cA cX cin cB cF cX cres wf cA
    cB cF wf cA cX cin cA wss cA cX cin cB cF cA cX cin cres wf cA cX inss1 cA
    cB cA cX cin cF fssres mpan2 cA cB cF wf cA cX cin cB cF cA cX cin cres cF
    cX cres cA cB cF wf cF cA cX cin cres cF cA cres cX cres cF cX cres cF cA
    cX resres cA cB cF wf cF cA cres cF cX cA cB cF wf cF cA wfn cF cA cres cF
    wceq cA cB cF ffn cA cF fnresdm syl reseq1d syl5eqr feq1d mpbid $.

  $( If two functions agree on their common domain, express their union as a
     union of three functions with pairwise disjoint domains.  (Contributed by
     Stefan O'Rear, 9-Oct-2014.) $)
  resasplit $p |- ( ( F Fn A /\ G Fn B /\
      ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( F u. G ) =
  ( ( F |` ( A i^i B ) ) u. ( ( F |` ( A \ B ) ) u. ( G |` ( B \ A ) ) ) ) ) $=
    cF cA wfn cG cB wfn cF cA cB cin cres cG cA cB cin cres wceq w3a cF cA cres
    cG cB cres cun cF cG cun cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif
    cres cun cun cF cA wfn cG cB wfn cF cA cres cG cB cres cun cF cG cun wceq
    cF cA cB cin cres cG cA cB cin cres wceq cF cA wfn cF cA cres cF wceq cG cB
    cres cG wceq cF cA cres cG cB cres cun cF cG cun wceq cG cB wfn cA cF
    fnresdm cB cG fnresdm cF cA cres cF cG cB cres cG uneq12 syl2an 3adant3 cF
    cA wfn cG cB wfn cF cA cB cin cres cG cA cB cin cres wceq w3a cF cA cres cG
    cB cres cun cF cA cB cin cres cF cA cB cin cres cun cF cA cB cdif cres cG
    cB cA cdif cres cun cun cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif
    cres cun cun cF cA wfn cG cB wfn cF cA cB cin cres cG cA cB cin cres wceq
    w3a cF cA cres cG cB cres cun cF cA cB cin cres cF cA cB cdif cres cun cF
    cA cB cin cres cG cB cA cdif cres cun cun cF cA cB cin cres cF cA cB cin
    cres cun cF cA cB cdif cres cG cB cA cdif cres cun cun cF cA wfn cG cB wfn
    cF cA cB cin cres cG cA cB cin cres wceq w3a cF cA cB cin cres cF cA cB
    cdif cres cun cF cA cB cin cres cG cB cA cdif cres cun cun cF cA cB cin
    cres cF cA cB cdif cres cun cG cA cB cin cres cG cB cA cdif cres cun cun cF
    cA cres cG cB cres cun cF cA wfn cG cB wfn cF cA cB cin cres cG cA cB cin
    cres wceq w3a cF cA cB cin cres cG cB cA cdif cres cun cG cA cB cin cres cG
    cB cA cdif cres cun cF cA cB cin cres cF cA cB cdif cres cun cF cA wfn cG
    cB wfn cF cA cB cin cres cG cA cB cin cres wceq w3a cF cA cB cin cres cG cA
    cB cin cres cG cB cA cdif cres cF cA wfn cG cB wfn cF cA cB cin cres cG cA
    cB cin cres wceq simp3 uneq1d uneq2d cF cA cres cF cA cB cin cres cF cA cB
    cdif cres cun cG cB cres cG cA cB cin cres cG cB cA cdif cres cun cF cA cB
    cin cA cB cdif cun cres cF cA cres cF cA cB cin cres cF cA cB cdif cres cun
    cA cB cin cA cB cdif cun cA cF cA cB inundif reseq2i cF cA cB cin cA cB
    cdif resundi eqtr3i cG cA cB cin cB cA cdif cun cres cG cB cres cG cA cB
    cin cres cG cB cA cdif cres cun cA cB cin cB cA cdif cun cB cG cA cB cin cB
    cA cdif cun cB cA cin cB cA cdif cun cB cA cB cin cB cA cin cB cA cdif cA
    cB incom uneq1i cB cA inundif eqtri reseq2i cG cA cB cin cB cA cdif resundi
    eqtr3i uneq12i syl6reqr cF cA cB cin cres cF cA cB cdif cres cF cA cB cin
    cres cG cB cA cdif cres un4 syl6eq cF cA cB cin cres cF cA cB cin cres cun
    cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif cres cun cF cA cB cin
    cres unidm uneq1i syl6eq eqtr3d $.

  $( The union of two functions which agree on their common domain is a
     function.  (Contributed by Stefan O'Rear, 9-Oct-2014.) $)
  fresaun $p |- ( ( F : A --> C /\ G : B --> C /\
      ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) ->
    ( F u. G ) : ( A u. B ) --> C ) $=
    cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cA cB
    cin cA cB cdif cB cA cdif cun cun cC cF cA cB cin cres cF cA cB cdif cres
    cG cB cA cdif cres cun cun wf cA cB cun cC cF cG cun wf cA cC cF wf cB cC
    cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cA cB cin cC cF cA cB
    cin cres wf cA cB cdif cB cA cdif cun cC cF cA cB cdif cres cG cB cA cdif
    cres cun wf cA cB cin cA cB cdif cB cA cdif cun cin c0 wceq cA cB cin cA cB
    cdif cB cA cdif cun cun cC cF cA cB cin cres cF cA cB cdif cres cG cB cA
    cdif cres cun cun wf cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin
    cres wceq w3a cA cC cF wf cA cB cin cA wss cA cB cin cC cF cA cB cin cres
    wf cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq simp1
    cA cB inss1 cA cC cA cB cin cF fssres sylancl cA cC cF wf cB cC cG wf cF cA
    cB cin cres cG cA cB cin cres wceq w3a cA cB cdif cC cF cA cB cdif cres wf
    cB cA cdif cC cG cB cA cdif cres wf cA cB cdif cB cA cdif cin c0 wceq cA cB
    cdif cB cA cdif cun cC cF cA cB cdif cres cG cB cA cdif cres cun wf cA cC
    cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cA cC cF wf
    cA cB cdif cA wss cA cB cdif cC cF cA cB cdif cres wf cA cC cF wf cB cC cG
    wf cF cA cB cin cres cG cA cB cin cres wceq simp1 cA cB difss cA cC cA cB
    cdif cF fssres sylancl cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB
    cin cres wceq w3a cB cC cG wf cB cA cdif cB wss cB cA cdif cC cG cB cA cdif
    cres wf cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq
    simp2 cB cA difss cB cC cB cA cdif cG fssres sylancl cA cB cdif cB cA cdif
    cin c0 wceq cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres
    wceq w3a cA cB cdif cB cA cdif cin cA cB cA cdif cin cB cB cA cdif cin cdif
    c0 cB cB cA cdif cin cdif c0 cA cB cB cA cdif indifdir cA cB cA cdif cin c0
    cB cB cA cdif cin cA cB disjdif difeq1i cB cB cA cdif cin 0dif 3eqtri a1i
    cA cB cdif cB cA cdif cC cF cA cB cdif cres cG cB cA cdif cres fun2
    syl21anc cA cB cin cA cB cdif cB cA cdif cun cin c0 wceq cA cC cF wf cB cC
    cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cA cB cin cA cB cdif cB
    cA cdif cun cin cA cB cin cA cB cdif cin cA cB cin cB cA cdif cin cun c0 c0
    cun c0 cA cB cin cA cB cdif cB cA cdif indi cA cB cin cA cB cdif cin c0 cA
    cB cin cB cA cdif cin c0 cA cB cin cA cB cdif cin cA cB cA cB cdif cin cin
    cA c0 cin c0 cA cB cA cB cdif inass cB cA cB cdif cin c0 cA cB cA disjdif
    ineq2i cA in0 3eqtri cA cB cin cB cA cdif cin cB cA cin cB cA cdif cin c0
    cA cB cin cB cA cin cB cA cdif cA cB incom ineq1i cB cA cin cB cA cdif cin
    cB cA cB cA cdif cin cin cB c0 cin c0 cB cA cB cA cdif inass cA cB cA cdif
    cin c0 cB cA cB disjdif ineq2i cB in0 3eqtri eqtri uneq12i c0 un0 3eqtri
    a1i cA cB cin cA cB cdif cB cA cdif cun cC cF cA cB cin cres cF cA cB cdif
    cres cG cB cA cdif cres cun fun2 syl21anc cA cC cF wf cB cC cG wf cF cA cB
    cin cres cG cA cB cin cres wceq w3a cA cB cun cC cF cG cun wf cA cB cun cC
    cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif cres cun cun wf cA cB
    cin cA cB cdif cB cA cdif cun cun cC cF cA cB cin cres cF cA cB cdif cres
    cG cB cA cdif cres cun cun wf cA cC cF wf cB cC cG wf cF cA cB cin cres cG
    cA cB cin cres wceq w3a cA cB cun cC cF cG cun cF cA cB cin cres cF cA cB
    cdif cres cG cB cA cdif cres cun cun cA cC cF wf cF cA wfn cB cC cG wf cG
    cB wfn cF cA cB cin cres cG cA cB cin cres wceq cF cA cB cin cres cG cA cB
    cin cres wceq cF cG cun cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif
    cres cun cun wceq cA cC cF ffn cB cC cG ffn cF cA cB cin cres cG cA cB cin
    cres wceq id cA cB cF cG resasplit syl3an feq1d cA cB cin cA cB cdif cB cA
    cdif cun cun cA cB cun cC cF cA cB cin cres cF cA cB cdif cres cG cB cA
    cdif cres cun cun cA cB cin cA cB cdif cB cA cdif cun cun cA cB cdif cA cB
    cin cB cA cdif cun cun cA cB cdif cB cun cA cB cun cA cB cin cA cB cdif cB
    cA cdif un12 cA cB cin cB cA cdif cun cB cA cB cdif cA cB cin cB cA cdif
    cun cB cA cin cB cA cdif cun cB cA cB cin cB cA cin cB cA cdif cA cB incom
    uneq1i cB cA inundif eqtri uneq2i cA cB undif1 3eqtri feq2i syl6rbbr mpbid
    $.

  $( From the union of two functions that agree on the domain overlap, either
     component can be recovered by restriction.  (Contributed by Stefan O'Rear,
     9-Oct-2014.) $)
  fresaunres2 $p |- ( ( F : A --> C /\ G : B --> C /\
      ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) ->
    ( ( F u. G ) |` B ) = G ) $=
    cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cF cG
    cun cB cres cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif cres cun cun
    cB cres cG cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq
    w3a cF cG cun cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif cres cun
    cun cB cA cC cF wf cF cA wfn cB cC cG wf cG cB wfn cF cA cB cin cres cG cA
    cB cin cres wceq cF cA cB cin cres cG cA cB cin cres wceq cF cG cun cF cA
    cB cin cres cF cA cB cdif cres cG cB cA cdif cres cun cun wceq cA cC cF ffn
    cB cC cG ffn cF cA cB cin cres cG cA cB cin cres wceq id cA cB cF cG
    resasplit syl3an reseq1d cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB
    cin cres wceq w3a cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif cres
    cun cun cB cres cF cA cB cin cres cB cres cF cA cB cdif cres cG cB cA cdif
    cres cun cB cres cun cG cF cA cB cin cres cF cA cB cdif cres cG cB cA cdif
    cres cun cB resundir cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin
    cres wceq w3a cF cA cB cin cres cB cres cF cA cB cdif cres cG cB cA cdif
    cres cun cB cres cun cF cA cB cin cres cF cA cB cdif cres cB cres cG cB cA
    cdif cres cB cres cun cun cG cF cA cB cin cres cB cres cF cA cB cin cres cF
    cA cB cdif cres cG cB cA cdif cres cun cB cres cF cA cB cdif cres cB cres
    cG cB cA cdif cres cB cres cun cA cB cin cB wss cF cA cB cin cres cB cres
    cF cA cB cin cres wceq cA cB inss2 cF cA cB cin cB resabs2 ax-mp cF cA cB
    cdif cres cG cB cA cdif cres cB resundir uneq12i cA cC cF wf cB cC cG wf cF
    cA cB cin cres cG cA cB cin cres wceq w3a cF cA cB cin cres cF cA cB cdif
    cres cB cres cG cB cA cdif cres cB cres cun cun cF cA cB cin cres c0 cG cB
    cA cdif cres cun cun cG cF cA cB cdif cres cB cres cG cB cA cdif cres cB
    cres cun c0 cG cB cA cdif cres cun cF cA cB cin cres cF cA cB cdif cres cB
    cres c0 cG cB cA cdif cres cB cres cG cB cA cdif cres cF cA cB cdif cres cB
    cres c0 wceq cF cA cB cdif cres cB cres cdm c0 wceq cF cA cB cdif cres cB
    cres cdm cB cF cA cB cdif cres cdm cin c0 cF cA cB cdif cres cB dmres cB cF
    cA cB cdif cres cdm cin cB cA cB cdif cF cdm cin cin c0 cF cA cB cdif cres
    cdm cA cB cdif cF cdm cin cB cF cA cB cdif dmres ineq2i cB cA cB cdif cin
    cF cdm cin c0 cF cdm cin cB cA cB cdif cF cdm cin cin c0 cB cA cB cdif cin
    c0 cF cdm cB cA disjdif ineq1i cB cA cB cdif cF cdm inass c0 cF cdm cin c0
    c0 cF cdm inss1 c0 cF cdm cin 0ss eqssi 3eqtr3i eqtri eqtri cF cA cB cdif
    cres cB cres wrel cF cA cB cdif cres cB cres c0 wceq cF cA cB cdif cres cB
    cres cdm c0 wceq wb cF cA cB cdif cres cB relres cF cA cB cdif cres cB cres
    reldm0 ax-mp mpbir cB cA cdif cB wss cG cB cA cdif cres cB cres cG cB cA
    cdif cres wceq cB cA difss cG cB cA cdif cB resabs2 ax-mp uneq12i uneq2i cA
    cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cF cA cB
    cin cres c0 cG cB cA cdif cres cun cun cG cA cB cin cres c0 cG cB cA cdif
    cres cun cun cG cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres
    wceq w3a cF cA cB cin cres cG cA cB cin cres c0 cG cB cA cdif cres cun cA
    cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq simp3 uneq1d
    cA cC cF wf cB cC cG wf cG cA cB cin cres c0 cG cB cA cdif cres cun cun cG
    wceq cF cA cB cin cres cG cA cB cin cres wceq cA cC cF wf cB cC cG wf wa cG
    cA cB cin cres c0 cG cB cA cdif cres cun cun cG cA cB cin cres cG cB cA
    cdif cres cun cG c0 cG cB cA cdif cres cun cG cB cA cdif cres cG cA cB cin
    cres c0 cG cB cA cdif cres cun cG cB cA cdif cres c0 cun cG cB cA cdif cres
    c0 cG cB cA cdif cres uncom cG cB cA cdif cres un0 eqtri uneq2i cA cC cF wf
    cB cC cG wf wa cG cA cB cin cres cG cB cA cdif cres cun cG cA cB cin cB cA
    cdif cun cres cG cG cA cB cin cB cA cdif resundi cA cC cF wf cB cC cG wf wa
    cG cA cB cin cB cA cdif cun cres cG cB cres cG cA cB cin cB cA cdif cun cB
    cG cA cB cin cB cA cdif cun cB cA cin cB cA cdif cun cB cA cB cin cB cA cin
    cB cA cdif cA cB incom uneq1i cB cA inundif eqtri reseq2i cB cC cG wf cG cB
    cres cG wceq cA cC cF wf cB cC cG wf cG cB wfn cG cB cres cG wceq cB cC cG
    ffn cB cG fnresdm syl adantl syl5eq syl5eqr syl5eq 3adant3 eqtrd syl5eq
    syl5eq syl5eq eqtrd $.

  $( From the union of two functions that agree on the domain overlap, either
     component can be recovered by restriction.  (Contributed by Mario
     Carneiro, 16-Feb-2015.) $)
  fresaunres1 $p |- ( ( F : A --> C /\ G : B --> C /\
      ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) ->
    ( ( F u. G ) |` A ) = F ) $=
    cA cC cF wf cB cC cG wf cF cA cB cin cres cG cA cB cin cres wceq w3a cF cG
    cun cA cres cG cF cun cA cres cF cF cG cun cG cF cun cA cF cG uncom reseq1i
    cF cA cB cin cres cG cA cB cin cres wceq cA cC cF wf cB cC cG wf cG cB cA
    cin cres cF cB cA cin cres wceq cG cF cun cA cres cF wceq cF cA cB cin cres
    cG cA cB cin cres wceq cF cB cA cin cres cG cB cA cin cres wceq cG cB cA
    cin cres cF cB cA cin cres wceq cF cA cB cin cres cF cB cA cin cres cG cA
    cB cin cres cG cB cA cin cres cA cB cin cB cA cin cF cA cB incom reseq2i cA
    cB cin cB cA cin cG cA cB incom reseq2i eqeq12i cF cB cA cin cres cG cB cA
    cin cres eqcom bitri cB cC cG wf cA cC cF wf cG cB cA cin cres cF cB cA cin
    cres wceq cG cF cun cA cres cF wceq cB cA cC cG cF fresaunres2 3com12
    syl3an3b syl5eq $.

  ${
    $d x y z A $.  $d x y z B $.  $d x y z F $.
    $( Composition of a mapping and restricted identity.  (Contributed by NM,
       13-Dec-2003.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    fcoi1 $p |- ( F : A --> B -> ( F o. ( _I |` A ) ) = F ) $=
      cA cB cF wf cF cA wfn cF cid cA cres ccom cF wceq cA cB cF ffn cF cA wfn
      cF wfun cF cdm cA wceq wa cF cid cA cres ccom cF wceq cF cA df-fn cF cdm
      cA wceq cF wfun cF cid cA cres ccom cF cid ccom cF cF cdm cA wceq cF cdm
      cA wss cF cid cA cres ccom cF cid ccom wceq cF cdm cA eqimss cF cdm cA
      wss cF cid cA cres ccom cF cid ccnv cA cres ccnv ccom cF cid ccom cid cA
      cres cid ccnv cA cres ccnv cF cid ccnv cA cres ccnv cid cA cres ccnv cid
      cA cres cid ccnv cA cres cid cA cres cid ccnv cid cA cnvi reseq1i cnveqi
      cA cnvresid eqtr2i coeq2i cF cid cA cores2 syl5eq syl cF wfun cF wrel cF
      cid ccom cF wceq cF funrel cF coi1 syl sylan9eqr sylbi syl $.

    $( Composition of restricted identity and a mapping.  (Contributed by NM,
       13-Dec-2003.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    fcoi2 $p |- ( F : A --> B -> ( ( _I |` B ) o. F ) = F ) $=
      cA cB cF wf cF cA wfn cF crn cB wss wa cid cB cres cF ccom cF wceq cA cB
      cF df-f cF crn cB wss cF cA wfn cid cB cres cF ccom cid cF ccom cF cid cF
      cB cores cF cA wfn cF wrel cid cF ccom cF wceq cA cF fnrel cF coi2 syl
      sylan9eqr sylbi $.
  $}

  ${
    $d y F $.  $d y A $.  $d y B $.  $d y C $.
    $( There is exactly one value of a function in its codomain.  (Contributed
       by NM, 10-Dec-2003.) $)
    feu $p |- ( ( F : A --> B /\ C e. A ) -> E! y e. B <. C , y >. e. F ) $=
      cA cB cF wf cC cA wcel wa vy cv cB wcel cC vy cv cop cF wcel wa vy weu cC
      vy cv cop cF wcel vy cB wreu cA cB cF wf cC cA wcel wa cC vy cv cop cF
      wcel vy weu vy cv cB wcel cC vy cv cop cF wcel wa vy weu cA cB cF wf cF
      cA wfn cC cA wcel cC vy cv cop cF wcel vy weu cA cB cF ffn vy cA cC cF
      fneu2 sylan cA cB cF wf cC vy cv cop cF wcel vy weu vy cv cB wcel cC vy
      cv cop cF wcel wa vy weu wb cC cA wcel cA cB cF wf cC vy cv cop cF wcel
      vy cv cB wcel cC vy cv cop cF wcel wa vy cA cB cF wf cC vy cv cop cF wcel
      vy cv cB wcel cA cB cF wf cC vy cv cop cF wcel vy cv cB wcel cA cB cF wf
      cC vy cv cop cF wcel wa cC cA wcel vy cv cB wcel cA cB cC vy cv cF opelf
      simprd ex pm4.71rd eubidv adantr mpbid cC vy cv cop cF wcel vy cB df-reu
      sylibr $.
  $}

  ${
    $d x y F $.  $d x y A $.  $d x y B $.
    $( The converse of a restriction of a function.  (Contributed by NM,
       26-Mar-1998.) $)
    fcnvres $p |- ( F : A --> B -> `' ( F |` A ) = ( `' F |` B ) ) $=
      cA cB cF wf vy vx cF cA cres ccnv cF ccnv cB cres cF cA cres relcnv cF
      ccnv cB relres cA cB cF wf vx cv vy cv cop cF wcel vy cv vx cv cop cF cA
      cres ccnv wcel vy cv vx cv cop cF ccnv cB cres wcel cA cB cF wf vx cv vy
      cv cop cF wcel vx cv vy cv cop cF wcel vx cv cA wcel wa vy cv vx cv cop
      cF cA cres ccnv wcel cA cB cF wf vx cv vy cv cop cF wcel vx cv cA wcel cA
      cB cF wf vx cv vy cv cop cF wcel vx cv cA wcel cA cB cF wf vx cv vy cv
      cop cF wcel wa vx cv cA wcel vy cv cB wcel cA cB vx cv vy cv cF opelf
      simpld ex pm4.71d vy cv vx cv cop cF cA cres ccnv wcel vx cv vy cv cop cF
      cA cres wcel vx cv vy cv cop cF wcel vx cv cA wcel wa vy cv vx cv cF cA
      cres vy vex vx vex opelcnv vx cv vy cv cF cA vy vex opelres bitri syl6bbr
      cA cB cF wf vx cv vy cv cop cF wcel vx cv vy cv cop cF wcel vy cv cB wcel
      wa vy cv vx cv cop cF ccnv cB cres wcel cA cB cF wf vx cv vy cv cop cF
      wcel vy cv cB wcel cA cB cF wf vx cv vy cv cop cF wcel vy cv cB wcel cA
      cB cF wf vx cv vy cv cop cF wcel wa vx cv cA wcel vy cv cB wcel cA cB vx
      cv vy cv cF opelf simprd ex pm4.71d vy cv vx cv cop cF ccnv cB cres wcel
      vy cv vx cv cop cF ccnv wcel vy cv cB wcel wa vx cv vy cv cop cF wcel vy
      cv cB wcel wa vy cv vx cv cF ccnv cB vx vex opelres vy cv vx cv cop cF
      ccnv wcel vx cv vy cv cop cF wcel vy cv cB wcel vy cv vx cv cF vy vex vx
      vex opelcnv anbi1i bitri syl6bbr bitr3d eqrelrdv $.
  $}

  $( The preimage of a class disjoint with a mapping's codomain is empty.
     (Contributed by FL, 24-Jan-2007.) $)
  fimacnvdisj $p |- ( ( F : A --> B /\ ( B i^i C ) = (/) ) ->
    ( `' F " C ) = (/) ) $=
    cA cB cF wf cB cC cin c0 wceq wa cF ccnv cdm cC cin c0 wceq cF ccnv cC cima
    c0 wceq cA cB cF wf cB cC cin c0 wceq cF ccnv cdm cB wss cF ccnv cdm cC cin
    c0 wceq cA cB cF wf cB cC cin c0 wceq wa cF ccnv cdm cF crn cB cF df-rn cA
    cB cF wf cF crn cB wss cB cC cin c0 wceq cA cB cF frn adantr syl5eqssr cF
    ccnv cdm cB cC ssdisj sylancom cF ccnv cC imadisj sylibr $.

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x F $.
    fint.1 $e |- B =/= (/) $.
    $( Function into an intersection.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
    fint $p |- ( F : A --> |^| B <-> A. x e. B F : A --> x ) $=
      cF cA wfn cF crn cB cint wss wa cF cA wfn cF crn vx cv wss wa vx cB wral
      cA cB cint cF wf cA vx cv cF wf vx cB wral cF cA wfn cF crn cB cint wss
      wa cF cA wfn cF crn vx cv wss vx cB wral wa cF cA wfn cF crn vx cv wss wa
      vx cB wral cF crn cB cint wss cF crn vx cv wss vx cB wral cF cA wfn vx cF
      crn cB ssint anbi2i cB c0 wne cF cA wfn cF crn vx cv wss wa vx cB wral cF
      cA wfn cF crn vx cv wss vx cB wral wa wb fint.1 cF cA wfn cF crn vx cv
      wss vx cB r19.28zv ax-mp bitr4i cA cB cint cF df-f cA vx cv cF wf cF cA
      wfn cF crn vx cv wss wa vx cB cA vx cv cF df-f ralbii 3bitr4i $.
  $}

  $( Mapping into an intersection.  (Contributed by NM, 14-Sep-1999.)  (Proof
     shortened by Andrew Salmon, 17-Sep-2011.) $)
  fin $p |- ( F : A --> ( B i^i C ) <-> ( F : A --> B /\ F : A --> C ) ) $=
    cF cA wfn cF crn cB cC cin wss wa cF cA wfn cF crn cB wss wa cF cA wfn cF
    crn cC wss wa wa cA cB cC cin cF wf cA cB cF wf cA cC cF wf wa cF cA wfn cF
    crn cB cC cin wss wa cF cA wfn cF crn cB wss cF crn cC wss wa wa cF cA wfn
    cF crn cB wss wa cF cA wfn cF crn cC wss wa wa cF crn cB wss cF crn cC wss
    wa cF crn cB cC cin wss cF cA wfn cF crn cB cC ssin anbi2i cF cA wfn cF crn
    cB wss cF crn cC wss anandi bitr3i cA cB cC cin cF df-f cA cB cF wf cF cA
    wfn cF crn cB wss wa cA cC cF wf cF cA wfn cF crn cC wss wa cA cB cF df-f
    cA cC cF df-f anbi12i 3bitr4i $.

  ${
    $d A x $.  $d B x $.
    fabexg.1 $e |- F = { x | ( x : A --> B /\ ph ) } $.
    $( Existence of a set of functions.  (Contributed by Paul Chapman,
       25-Feb-2008.) $)
    fabexg $p |- ( ( A e. C /\ B e. D ) -> F e. _V ) $=
      cA cC wcel cB cD wcel wa cA cB cxp cvv wcel cA cB cxp cpw cvv wcel cF cvv
      wcel cA cB cC cD xpexg cA cB cxp cvv pwexg cF cA cB cxp cpw wss cA cB cxp
      cpw cvv wcel cF cvv wcel cF vx cv cA cB cxp cpw wcel wph wa vx cab cA cB
      cxp cpw cF cA cB vx cv wf wph wa vx cab vx cv cA cB cxp cpw wcel wph wa
      vx cab fabexg.1 cA cB vx cv wf wph wa vx cv cA cB cxp cpw wcel wph wa vx
      cA cB vx cv wf vx cv cA cB cxp cpw wcel wph cA cB vx cv wf vx cv cA cB
      cxp wss vx cv cA cB cxp cpw wcel cA cB vx cv fssxp vx cv cA cB cxp vx vex
      elpw sylibr anim1i ss2abi eqsstri wph vx cA cB cxp cpw ssab2 sstri cF cA
      cB cxp cpw cvv ssexg mpan 3syl $.
  $}

  ${
    $d x A $.  $d x B $.
    fabex.1 $e |- A e. _V $.
    fabex.2 $e |- B e. _V $.
    fabex.3 $e |- F = { x | ( x : A --> B /\ ph ) } $.
    $( Existence of a set of functions.  (Contributed by NM, 3-Dec-2007.) $)
    fabex $p |- F e. _V $=
      cA cvv wcel cB cvv wcel cF cvv wcel fabex.1 fabex.2 wph vx cA cB cvv cvv
      cF fabex.3 fabexg mp2an $.
  $}

  $( If a mapping is a set, its domain is a set.  (Contributed by NM,
     27-Aug-2006.)  (Proof shortened by Andrew Salmon, 17-Sep-2011.) $)
  dmfex $p |- ( ( F e. C /\ F : A --> B ) -> A e. _V ) $=
    cA cB cF wf cF cC wcel cA cvv wcel cA cB cF wf cF cdm cA wceq cF cC wcel cA
    cvv wcel wi cA cB cF fdm cF cC wcel cF cdm cvv wcel cF cdm cA wceq cA cvv
    wcel cF cC dmexg cF cdm cA cvv eleq1 syl5ib syl impcom $.

  $( The empty function.  (Contributed by NM, 14-Aug-1999.) $)
  f0 $p |- (/) : (/) --> A $=
    c0 cA c0 wf c0 c0 wfn c0 crn cA wss c0 c0 wfn c0 c0 wceq c0 eqid c0 fn0
    mpbir c0 crn c0 cA rn0 cA 0ss eqsstri c0 cA c0 df-f mpbir2an $.

  $( A class is a function with empty codomain iff it and its domain are
     empty.  (Contributed by NM, 10-Dec-2003.) $)
  f00 $p |- ( F : A --> (/) <-> ( F = (/) /\ A = (/) ) ) $=
    cA c0 cF wf cF c0 wceq cA c0 wceq wa cA c0 cF wf cF c0 wceq cA c0 wceq cA
    c0 cF wf cF c0 wfn cF c0 wceq cA c0 cF wf cF wfun cF cdm c0 wceq cF c0 wfn
    cA c0 cF ffun cA c0 cF wf cF crn c0 wceq cF cdm c0 wceq cA c0 cF wf cF crn
    c0 wss cF crn c0 wceq cA c0 cF frn cF crn ss0 syl cF dm0rn0 sylibr cF c0
    df-fn sylanbrc cF fn0 sylib cA c0 cF wf cF cdm cA c0 cA c0 cF fdm cA c0 cF
    wf cF crn c0 wceq cF cdm c0 wceq cA c0 cF wf cF crn c0 wss cF crn c0 wceq
    cA c0 cF frn cF crn ss0 syl cF dm0rn0 sylibr eqtr3d jca cF c0 wceq cA c0
    wceq wa cA c0 cF wf c0 c0 c0 wf c0 f0 cF c0 wceq cA c0 cF wf cA c0 c0 wf cA
    c0 wceq c0 c0 c0 wf cA c0 cF c0 feq1 cA c0 c0 c0 feq2 sylan9bb mpbiri
    impbii $.

  ${
    $d x y A $.  $d x y B $.
    fconst.1 $e |- B e. _V $.
    $( A cross product with a singleton is a constant function.  (Contributed
       by NM, 14-Aug-1999.)  (Proof shortened by Andrew Salmon,
       17-Sep-2011.) $)
    fconst $p |- ( A X. { B } ) : A --> { B } $=
      cA cB csn cA cB csn cxp wf cA cB csn cxp cA wfn cA cB csn cxp crn cB csn
      wss vx cA cB cA cB csn cxp fconst.1 vx cA cB fconstmpt fnmpti cA cB csn
      rnxpss cA cB csn cA cB csn cxp df-f mpbir2an $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A cross product with a singleton is a constant function.  (Contributed
       by NM, 19-Oct-2004.) $)
    fconstg $p |- ( B e. V -> ( A X. { B } ) : A --> { B } ) $=
      cA vx cv csn cA vx cv csn cxp wf cA cB csn cA cB csn cxp wf vx cB cV vx
      cv cB wceq cA vx cv csn cxp cA cB csn cxp wceq vx cv csn cB csn wceq cA
      vx cv csn cA vx cv csn cxp wf cA cB csn cA cB csn cxp wf wb vx cv cB wceq
      vx cv csn cB csn cA vx cv cB sneq xpeq2d vx cv cB sneq cA vx cv csn cxp
      cA cB csn cxp wceq cA vx cv csn cA vx cv csn cxp wf cA vx cv csn cA cB
      csn cxp wf vx cv csn cB csn wceq cA cB csn cA cB csn cxp wf cA vx cv csn
      cA vx cv csn cxp cA cB csn cxp feq1 vx cv csn cB csn cA cA cB csn cxp
      feq3 sylan9bb syl2anc cA vx cv vx vex fconst vtoclg $.
  $}

  $( A cross product with a singleton is a constant function.  (Contributed by
     NM, 24-Jul-2014.) $)
  fnconstg $p |- ( B e. V -> ( A X. { B } ) Fn A ) $=
    cB cV wcel cA cB csn cA cB csn cxp wf cA cB csn cxp cA wfn cA cB cV fconstg
    cA cB csn cA cB csn cxp ffn syl $.

  $( Constant function with loose range.  (Contributed by Stefan O'Rear,
     1-Feb-2015.) $)
  fconst6g $p |- ( B e. C -> ( A X. { B } ) : A --> C ) $=
    cB cC wcel cA cB csn cA cB csn cxp wf cB csn cC wss cA cC cA cB csn cxp wf
    cA cB cC fconstg cB cC snssi cA cB csn cC cA cB csn cxp fss syl2anc $.

  ${
    fconst6.1 $e |- B e. C $.
    $( A constant function as a mapping.  (Contributed by Jeff Madsen,
       30-Nov-2009.)  (Revised by Mario Carneiro, 22-Apr-2015.) $)
    fconst6 $p |- ( A X. { B } ) : A --> C $=
      cB cC wcel cA cC cA cB csn cxp wf fconst6.1 cA cB cC fconst6g ax-mp $.
  $}

  $( Equality theorem for one-to-one functions.  (Contributed by NM,
     10-Feb-1997.) $)
  f1eq1 $p |- ( F = G -> ( F : A -1-1-> B <-> G : A -1-1-> B ) ) $=
    cF cG wceq cA cB cF wf cF ccnv wfun wa cA cB cG wf cG ccnv wfun wa cA cB cF
    wf1 cA cB cG wf1 cF cG wceq cA cB cF wf cA cB cG wf cF ccnv wfun cG ccnv
    wfun cA cB cF cG feq1 cF cG wceq cF ccnv cG ccnv cF cG cnveq funeqd anbi12d
    cA cB cF df-f1 cA cB cG df-f1 3bitr4g $.

  $( Equality theorem for one-to-one functions.  (Contributed by NM,
     10-Feb-1997.) $)
  f1eq2 $p |- ( A = B -> ( F : A -1-1-> C <-> F : B -1-1-> C ) ) $=
    cA cB wceq cA cC cF wf cF ccnv wfun wa cB cC cF wf cF ccnv wfun wa cA cC cF
    wf1 cB cC cF wf1 cA cB wceq cA cC cF wf cB cC cF wf cF ccnv wfun cA cB cC
    cF feq2 anbi1d cA cC cF df-f1 cB cC cF df-f1 3bitr4g $.

  $( Equality theorem for one-to-one functions.  (Contributed by NM,
     10-Feb-1997.) $)
  f1eq3 $p |- ( A = B -> ( F : C -1-1-> A <-> F : C -1-1-> B ) ) $=
    cA cB wceq cC cA cF wf cF ccnv wfun wa cC cB cF wf cF ccnv wfun wa cC cA cF
    wf1 cC cB cF wf1 cA cB wceq cC cA cF wf cC cB cF wf cF ccnv wfun cA cB cC
    cF feq3 anbi1d cC cA cF df-f1 cC cB cF df-f1 3bitr4g $.

  ${
    $d y F $.  $d y A $.  $d y B $.  $d x y $.
    nff1.1 $e |- F/_ x F $.
    nff1.2 $e |- F/_ x A $.
    nff1.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for a one-to-one function.
       (Contributed by NM, 16-May-2004.) $)
    nff1 $p |- F/ x F : A -1-1-> B $=
      cA cB cF wf1 cA cB cF wf cF ccnv wfun wa vx cA cB cF df-f1 cA cB cF wf cF
      ccnv wfun vx vx cA cB cF nff1.1 nff1.2 nff1.3 nff vx cF ccnv vx cF nff1.1
      nfcnv nffun nfan nfxfr $.
  $}

  ${
    $d x y F $.
    $( Alternate definition of a one-to-one function.  (Contributed by NM,
       31-Dec-1996.) $)
    dff12 $p |- ( F : A -1-1-> B <-> ( F : A --> B /\ A. y E* x x F y ) ) $=
      cA cB cF wf1 cA cB cF wf cF ccnv wfun wa cA cB cF wf vx cv vy cv cF wbr
      vx wmo vy wal wa cA cB cF df-f1 cF ccnv wfun vx cv vy cv cF wbr vx wmo vy
      wal cA cB cF wf vx vy cF funcnv2 anbi2i bitri $.
  $}

  $( A one-to-one mapping is a mapping.  (Contributed by NM, 31-Dec-1996.) $)
  f1f $p |- ( F : A -1-1-> B -> F : A --> B ) $=
    cA cB cF wf1 cA cB cF wf cF ccnv wfun cA cB cF df-f1 simplbi $.

  $( A one-to-one mapping is a function on its domain.  (Contributed by NM,
     8-Mar-2014.) $)
  f1fn $p |- ( F : A -1-1-> B -> F Fn A ) $=
    cA cB cF wf1 cA cB cF wf cF cA wfn cA cB cF f1f cA cB cF ffn syl $.

  $( A one-to-one mapping is a function.  (Contributed by NM, 8-Mar-2014.) $)
  f1fun $p |- ( F : A -1-1-> B -> Fun F ) $=
    cA cB cF wf1 cF cA wfn cF wfun cA cB cF f1fn cA cF fnfun syl $.

  $( A one-to-one onto mapping is a relation.  (Contributed by NM,
     8-Mar-2014.) $)
  f1rel $p |- ( F : A -1-1-> B -> Rel F ) $=
    cA cB cF wf1 cF cA wfn cF wrel cA cB cF f1fn cA cF fnrel syl $.

  $( The domain of a one-to-one mapping.  (Contributed by NM, 8-Mar-2014.) $)
  f1dm $p |- ( F : A -1-1-> B -> dom F = A ) $=
    cA cB cF wf1 cF cA wfn cF cdm cA wceq cA cB cF f1fn cA cF fndm syl $.

  $( A function that is one-to-one is also one-to-one on some superset of its
     range.  (Contributed by Mario Carneiro, 12-Jan-2013.) $)
  f1ss $p |- ( ( F : A -1-1-> B /\ B C_ C ) -> F : A -1-1-> C ) $=
    cA cB cF wf1 cB cC wss wa cA cC cF wf cF ccnv wfun cA cC cF wf1 cA cB cF
    wf1 cA cB cF wf cB cC wss cA cC cF wf cA cB cF f1f cA cB cC cF fss sylan cA
    cB cF wf1 cF ccnv wfun cB cC wss cA cB cF wf1 cA cB cF wf cF ccnv wfun cA
    cB cF df-f1 simprbi adantr cA cC cF df-f1 sylanbrc $.

  $( Combine a one-to-one function with a restriction on the domain.
     (Contributed by Stefan O'Rear, 20-Feb-2015.) $)
  f1ssr $p |- ( ( F : A -1-1-> B /\ ran F C_ C ) -> F : A -1-1-> C ) $=
    cA cB cF wf1 cF crn cC wss wa cA cC cF wf cF ccnv wfun cA cC cF wf1 cA cB
    cF wf1 cF crn cC wss wa cF cA wfn cF crn cC wss cA cC cF wf cA cB cF wf1 cF
    cA wfn cF crn cC wss cA cB cF f1fn adantr cA cB cF wf1 cF crn cC wss simpr
    cA cC cF df-f sylanbrc cA cB cF wf1 cF ccnv wfun cF crn cC wss cA cB cF wf1
    cA cB cF wf cF ccnv wfun cA cB cF df-f1 simprbi adantr cA cC cF df-f1
    sylanbrc $.

  $( A function that is one-to-one is also one-to-one on some aubset of its
     domain.  (Contributed by Mario Carneiro, 17-Jan-2015.) $)
  f1ssres $p |- ( ( F : A -1-1-> B /\ C C_ A ) -> ( F |` C ) : C -1-1-> B ) $=
    cA cB cF wf1 cC cA wss wa cC cB cF cC cres wf cF cC cres ccnv wfun cC cB cF
    cC cres wf1 cA cB cF wf1 cA cB cF wf cC cA wss cC cB cF cC cres wf cA cB cF
    f1f cA cB cC cF fssres sylan cA cB cF wf1 cF cC cres ccnv wfun cC cA wss cA
    cB cF wf1 cF ccnv wfun cF cC cres ccnv wfun cA cB cF wf1 cA cB cF wf cF
    ccnv wfun cA cB cF df-f1 simprbi cC cF funres11 syl adantr cC cB cF cC cres
    df-f1 sylanbrc $.

  $( Two ways to express that a set ` A ` (not necessarily a function) is
     one-to-one.  Each side is equivalent to Definition 6.4(3) of
     [TakeutiZaring] p. 24, who use the notation "Un_2 (A)" for one-to-one.  We
     do not introduce a separate notation since we rarely use it.  (Contributed
     by NM, 13-Aug-2004.) $)
  f1cnvcnv $p |- ( `' `' A : dom A -1-1-> _V
             <-> ( Fun `' A /\ Fun `' `' A ) ) $=
    cA cdm cvv cA ccnv ccnv wf1 cA cdm cvv cA ccnv ccnv wf cA ccnv ccnv ccnv
    wfun wa cA ccnv wfun cA ccnv ccnv wfun wa cA cdm cvv cA ccnv ccnv df-f1 cA
    cdm cvv cA ccnv ccnv wf cA ccnv ccnv wfun cA ccnv ccnv ccnv wfun cA ccnv
    wfun cA cdm cvv cA ccnv ccnv wf cA ccnv ccnv cA cdm wfn cA ccnv ccnv wfun
    cA cdm cA ccnv ccnv dffn2 cA ccnv ccnv cA cdm wfn cA ccnv ccnv wfun cA ccnv
    ccnv cdm cA cdm wceq cA dmcnvcnv cA ccnv ccnv cA cdm df-fn mpbiran2 bitr3i
    cA ccnv ccnv ccnv cA ccnv cA ccnv wrel cA ccnv ccnv ccnv cA ccnv wceq cA
    relcnv cA ccnv dfrel2 mpbi funeqi anbi12ci bitri $.

  $( Composition of one-to-one functions.  Exercise 30 of [TakeutiZaring]
     p. 25.  (Contributed by NM, 28-May-1998.) $)
  f1co $p |- ( ( F : B -1-1-> C /\ G : A -1-1-> B ) ->
              ( F o. G ) : A -1-1-> C ) $=
    cB cC cF wf1 cA cB cG wf1 wa cA cC cF cG ccom wf cF cG ccom ccnv wfun wa cA
    cC cF cG ccom wf1 cB cC cF wf1 cB cC cF wf cF ccnv wfun wa cA cB cG wf cG
    ccnv wfun wa cA cC cF cG ccom wf cF cG ccom ccnv wfun wa cA cB cG wf1 cB cC
    cF df-f1 cA cB cG df-f1 cB cC cF wf cA cB cG wf cF ccnv wfun cG ccnv wfun
    cA cC cF cG ccom wf cF cG ccom ccnv wfun wa cB cC cF wf cA cB cG wf wa cA
    cC cF cG ccom wf cF ccnv wfun cG ccnv wfun wa cF cG ccom ccnv wfun cA cB cC
    cF cG fco cG ccnv wfun cF ccnv wfun cF cG ccom ccnv wfun cG ccnv wfun cF
    ccnv wfun wa cG ccnv cF ccnv ccom wfun cF cG ccom ccnv wfun cG ccnv cF ccnv
    funco cF cG ccom ccnv cG ccnv cF ccnv ccom cF cG cnvco funeqi sylibr ancoms
    anim12i an4s syl2anb cA cC cF cG ccom df-f1 sylibr $.

  $( Equality theorem for onto functions.  (Contributed by NM, 1-Aug-1994.) $)
  foeq1 $p |- ( F = G -> ( F : A -onto-> B <-> G : A -onto-> B ) ) $=
    cF cG wceq cF cA wfn cF crn cB wceq wa cG cA wfn cG crn cB wceq wa cA cB cF
    wfo cA cB cG wfo cF cG wceq cF cA wfn cG cA wfn cF crn cB wceq cG crn cB
    wceq cA cF cG fneq1 cF cG wceq cF crn cG crn cB cF cG rneq eqeq1d anbi12d
    cA cB cF df-fo cA cB cG df-fo 3bitr4g $.

  $( Equality theorem for onto functions.  (Contributed by NM, 1-Aug-1994.) $)
  foeq2 $p |- ( A = B -> ( F : A -onto-> C <-> F : B -onto-> C ) ) $=
    cA cB wceq cF cA wfn cF crn cC wceq wa cF cB wfn cF crn cC wceq wa cA cC cF
    wfo cB cC cF wfo cA cB wceq cF cA wfn cF cB wfn cF crn cC wceq cA cB cF
    fneq2 anbi1d cA cC cF df-fo cB cC cF df-fo 3bitr4g $.

  $( Equality theorem for onto functions.  (Contributed by NM, 1-Aug-1994.) $)
  foeq3 $p |- ( A = B -> ( F : C -onto-> A <-> F : C -onto-> B ) ) $=
    cA cB wceq cF cC wfn cF crn cA wceq wa cF cC wfn cF crn cB wceq wa cC cA cF
    wfo cC cB cF wfo cA cB wceq cF crn cA wceq cF crn cB wceq cF cC wfn cA cB
    cF crn eqeq2 anbi2d cC cA cF df-fo cC cB cF df-fo 3bitr4g $.

  ${
    $d y F $.  $d y A $.  $d y B $.  $d x y $.
    nffo.1 $e |- F/_ x F $.
    nffo.2 $e |- F/_ x A $.
    nffo.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for an onto function.  (Contributed by
       NM, 16-May-2004.) $)
    nffo $p |- F/ x F : A -onto-> B $=
      cA cB cF wfo cF cA wfn cF crn cB wceq wa vx cA cB cF df-fo cF cA wfn cF
      crn cB wceq vx vx cA cF nffo.1 nffo.2 nffn vx cF crn cB vx cF nffo.1 nfrn
      nffo.3 nfeq nfan nfxfr $.
  $}

  $( An onto mapping is a mapping.  (Contributed by NM, 3-Aug-1994.) $)
  fof $p |- ( F : A -onto-> B -> F : A --> B ) $=
    cF cA wfn cF crn cB wceq wa cF cA wfn cF crn cB wss wa cA cB cF wfo cA cB
    cF wf cF crn cB wceq cF crn cB wss cF cA wfn cF crn cB eqimss anim2i cA cB
    cF df-fo cA cB cF df-f 3imtr4i $.

  $( An onto mapping is a function.  (Contributed by NM, 29-Mar-2008.) $)
  fofun $p |- ( F : A -onto-> B -> Fun F ) $=
    cA cB cF wfo cA cB cF wf cF wfun cA cB cF fof cA cB cF ffun syl $.

  $( An onto mapping is a function on its domain.  (Contributed by NM,
     16-Dec-2008.) $)
  fofn $p |- ( F : A -onto-> B -> F Fn A ) $=
    cA cB cF wfo cA cB cF wf cF cA wfn cA cB cF fof cA cB cF ffn syl $.

  $( The codomain of an onto function is its range.  (Contributed by NM,
     3-Aug-1994.) $)
  forn $p |- ( F : A -onto-> B -> ran F = B ) $=
    cA cB cF wfo cF cA wfn cF crn cB wceq cA cB cF df-fo simprbi $.

  $( Alternate definition of an onto function.  (Contributed by NM,
     22-Mar-2006.) $)
  dffo2 $p |- ( F : A -onto-> B <-> ( F : A --> B /\ ran F = B ) ) $=
    cA cB cF wfo cA cB cF wf cF crn cB wceq wa cA cB cF wfo cA cB cF wf cF crn
    cB wceq cA cB cF fof cA cB cF forn jca cA cB cF wf cF cA wfn cF crn cB wceq
    cA cB cF wfo cA cB cF ffn cA cB cF wfo cF cA wfn cF crn cB wceq wa cA cB cF
    df-fo biimpri sylan impbii $.

  $( The image of the domain of an onto function.  (Contributed by NM,
     29-Nov-2002.) $)
  foima $p |- ( F : A -onto-> B -> ( F " A ) = B ) $=
    cA cB cF wfo cF cF cdm cima cF crn cF cA cima cB cF imadmrn cA cB cF wfo cF
    cdm cA cF cA cB cF wfo cA cB cF wf cF cdm cA wceq cA cB cF fof cA cB cF fdm
    syl imaeq2d cA cB cF forn 3eqtr3a $.

  $( A function maps onto its range.  (Contributed by NM, 10-May-1998.) $)
  dffn4 $p |- ( F Fn A <-> F : A -onto-> ran F ) $=
    cF cA wfn cF cA wfn cF crn cF crn wceq wa cA cF crn cF wfo cF crn cF crn
    wceq cF cA wfn cF crn eqid biantru cA cF crn cF df-fo bitr4i $.

  $( A function maps its domain onto its range.  (Contributed by NM,
     23-Jul-2004.) $)
  funforn $p |- ( Fun A <-> A : dom A -onto-> ran A ) $=
    cA wfun cA cA cdm wfn cA cdm cA crn cA wfo cA funfn cA cdm cA dffn4 bitri
    $.

  $( An onto function has unique domain and range.  (Contributed by NM,
     5-Nov-2006.) $)
  fodmrnu $p |- ( ( F : A -onto-> B /\ F : C -onto-> D ) ->
                ( A = C /\ B = D ) ) $=
    cA cB cF wfo cC cD cF wfo wa cA cC wceq cB cD wceq cA cB cF wfo cF cA wfn
    cF cC wfn cA cC wceq cC cD cF wfo cA cB cF fofn cC cD cF fofn cA cC cF
    fndmu syl2an cA cB cF wfo cC cD cF wfo cB cF crn cD cA cB cF forn cC cD cF
    forn sylan9req jca $.

  $( Restriction of a function.  (Contributed by NM, 4-Mar-1997.) $)
  fores $p |- ( ( Fun F /\ A C_ dom F ) ->
              ( F |` A ) : A -onto-> ( F " A ) ) $=
    cF wfun cA cF cdm wss wa cF cA cres wfun cA cF cdm wss wa cA cF cA cima cF
    cA cres wfo cF wfun cF cA cres wfun cA cF cdm wss cA cF funres anim1i cF cA
    cres cA wfn cF cA cres wfun cF cA cres cdm cA wceq wa cA cF cA cima cF cA
    cres wfo cF cA cres wfun cA cF cdm wss wa cF cA cres cA df-fn cA cF cA cima
    cF cA cres wfo cF cA cres cA wfn cF cA cres crn cF cA cima wceq cF cA cima
    cF cA cres crn cF cA df-ima eqcomi cA cF cA cima cF cA cres df-fo mpbiran2
    cA cF cdm wss cF cA cres cdm cA wceq cF cA cres wfun cA cF ssdmres anbi2i
    3bitr4i sylibr $.

  $( Composition of onto functions.  (Contributed by NM, 22-Mar-2006.) $)
  foco $p |- ( ( F : B -onto-> C /\ G : A -onto-> B ) ->
             ( F o. G ) : A -onto-> C ) $=
    cB cC cF wfo cA cB cG wfo wa cA cC cF cG ccom wf cF cG ccom crn cC wceq wa
    cA cC cF cG ccom wfo cB cC cF wfo cB cC cF wf cF crn cC wceq wa cA cB cG wf
    cG crn cB wceq wa cA cC cF cG ccom wf cF cG ccom crn cC wceq wa cA cB cG
    wfo cB cC cF dffo2 cA cB cG dffo2 cB cC cF wf cF crn cC wceq wa cA cB cG wf
    cG crn cB wceq wa wa cA cC cF cG ccom wf cF cG ccom crn cC wceq cB cC cF wf
    cA cB cG wf cA cC cF cG ccom wf cF crn cC wceq cG crn cB wceq cA cB cC cF
    cG fco ad2ant2r cB cC cF wf cF crn cC wceq wa cG crn cB wceq cF cG ccom crn
    cC wceq cA cB cG wf cB cC cF wf cG crn cB wceq cF crn cC wceq cF cG ccom
    crn cC wceq cB cC cF wf cG crn cB wceq wa cF cdm cG crn wceq cF crn cC wceq
    cF cG ccom crn cC wceq cB cC cF wf cF cdm cB wceq cG crn cB wceq cF cdm cG
    crn wceq cB cC cF fdm cF cdm cG crn cB eqtr3 sylan cF cdm cG crn wceq cF cG
    ccom crn cC wceq cF crn cC wceq cF cdm cG crn wceq cF cG ccom crn cF crn cC
    cF cG rncoeq eqeq1d biimpar sylan an32s adantrl jca syl2anb cA cC cF cG
    ccom dffo2 sylibr $.

  $( A nonzero constant function is onto.  (Contributed by NM, 12-Jan-2007.) $)
  foconst $p |- ( ( F : A --> { B } /\ F =/= (/) ) -> F : A -onto-> { B } ) $=
    cA cB csn cF wf cF c0 wne wa cA cB csn cF wf cF crn cB csn wceq wa cA cB
    csn cF wfo cA cB csn cF wf cF c0 wne cF crn cB csn wceq cA cB csn cF wf cF
    c0 wne cF crn c0 wceq wn cF crn cB csn wceq cA cB csn cF wf cF wrel cF c0
    wne cF crn c0 wceq wn wb cA cB csn cF frel cF wrel cF crn c0 wceq cF c0 cF
    relrn0 necon3abid syl cA cB csn cF wf cF crn c0 wceq cF crn cB csn wceq cA
    cB csn cF wf cF crn cB csn wss cF crn c0 wceq cF crn cB csn wceq wo cA cB
    csn cF frn cF crn cB sssn sylib ord sylbid imdistani cA cB csn cF dffo2
    sylibr $.

  $( Equality theorem for one-to-one onto functions.  (Contributed by NM,
     10-Feb-1997.) $)
  f1oeq1 $p |- ( F = G -> ( F : A -1-1-onto-> B <-> G : A -1-1-onto-> B ) ) $=
    cF cG wceq cA cB cF wf1 cA cB cF wfo wa cA cB cG wf1 cA cB cG wfo wa cA cB
    cF wf1o cA cB cG wf1o cF cG wceq cA cB cF wf1 cA cB cG wf1 cA cB cF wfo cA
    cB cG wfo cA cB cF cG f1eq1 cA cB cF cG foeq1 anbi12d cA cB cF df-f1o cA cB
    cG df-f1o 3bitr4g $.

  $( Equality theorem for one-to-one onto functions.  (Contributed by NM,
     10-Feb-1997.) $)
  f1oeq2 $p |- ( A = B -> ( F : A -1-1-onto-> C <-> F : B -1-1-onto-> C ) ) $=
    cA cB wceq cA cC cF wf1 cA cC cF wfo wa cB cC cF wf1 cB cC cF wfo wa cA cC
    cF wf1o cB cC cF wf1o cA cB wceq cA cC cF wf1 cB cC cF wf1 cA cC cF wfo cB
    cC cF wfo cA cB cC cF f1eq2 cA cB cC cF foeq2 anbi12d cA cC cF df-f1o cB cC
    cF df-f1o 3bitr4g $.

  $( Equality theorem for one-to-one onto functions.  (Contributed by NM,
     10-Feb-1997.) $)
  f1oeq3 $p |- ( A = B -> ( F : C -1-1-onto-> A <-> F : C -1-1-onto-> B ) ) $=
    cA cB wceq cC cA cF wf1 cC cA cF wfo wa cC cB cF wf1 cC cB cF wfo wa cC cA
    cF wf1o cC cB cF wf1o cA cB wceq cC cA cF wf1 cC cB cF wf1 cC cA cF wfo cC
    cB cF wfo cA cB cC cF f1eq3 cA cB cC cF foeq3 anbi12d cC cA cF df-f1o cC cB
    cF df-f1o 3bitr4g $.

  $( Equality theorem for one-to-one onto functions.  (Contributed by FL,
     14-Jul-2012.) $)
  f1oeq23 $p |- ( ( A = B /\ C = D ) ->
   ( F : A -1-1-onto-> C <-> F : B -1-1-onto-> D ) ) $=
    cA cB wceq cA cC cF wf1o cB cC cF wf1o cC cD wceq cB cD cF wf1o cA cB cC cF
    f1oeq2 cC cD cB cF f1oeq3 sylan9bb $.

  ${
    f1eq123d.1 $e |- ( ph -> F = G ) $.
    f1eq123d.2 $e |- ( ph -> A = B ) $.
    f1eq123d.3 $e |- ( ph -> C = D ) $.
    $( Equality deduction for one-to-one functions.  (Contributed by Mario
       Carneiro, 27-Jan-2017.) $)
    f1eq123d $p |- ( ph -> ( F : A -1-1-> C <-> G : B -1-1-> D ) ) $=
      wph cA cC cF wf1 cA cC cG wf1 cB cC cG wf1 cB cD cG wf1 wph cF cG wceq cA
      cC cF wf1 cA cC cG wf1 wb f1eq123d.1 cA cC cF cG f1eq1 syl wph cA cB wceq
      cA cC cG wf1 cB cC cG wf1 wb f1eq123d.2 cA cB cC cG f1eq2 syl wph cC cD
      wceq cB cC cG wf1 cB cD cG wf1 wb f1eq123d.3 cC cD cB cG f1eq3 syl 3bitrd
      $.

    $( Equality deduction for onto functions.  (Contributed by Mario Carneiro,
       27-Jan-2017.) $)
    foeq123d $p |- ( ph -> ( F : A -onto-> C <-> G : B -onto-> D ) ) $=
      wph cA cC cF wfo cA cC cG wfo cB cC cG wfo cB cD cG wfo wph cF cG wceq cA
      cC cF wfo cA cC cG wfo wb f1eq123d.1 cA cC cF cG foeq1 syl wph cA cB wceq
      cA cC cG wfo cB cC cG wfo wb f1eq123d.2 cA cB cC cG foeq2 syl wph cC cD
      wceq cB cC cG wfo cB cD cG wfo wb f1eq123d.3 cC cD cB cG foeq3 syl 3bitrd
      $.

    $( Equality deduction for one-to-one onto functions.  (Contributed by Mario
       Carneiro, 27-Jan-2017.) $)
    f1oeq123d $p |- ( ph ->
      ( F : A -1-1-onto-> C <-> G : B -1-1-onto-> D ) ) $=
      wph cA cC cF wf1o cA cC cG wf1o cB cC cG wf1o cB cD cG wf1o wph cF cG
      wceq cA cC cF wf1o cA cC cG wf1o wb f1eq123d.1 cA cC cF cG f1oeq1 syl wph
      cA cB wceq cA cC cG wf1o cB cC cG wf1o wb f1eq123d.2 cA cB cC cG f1oeq2
      syl wph cC cD wceq cB cC cG wf1o cB cD cG wf1o wb f1eq123d.3 cC cD cB cG
      f1oeq3 syl 3bitrd $.
  $}

  ${
    $d y F $.  $d y A $.  $d y B $.  $d x y $.
    nff1o.1 $e |- F/_ x F $.
    nff1o.2 $e |- F/_ x A $.
    nff1o.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for a one-to-one onto function.
       (Contributed by NM, 16-May-2004.) $)
    nff1o $p |- F/ x F : A -1-1-onto-> B $=
      cA cB cF wf1o cA cB cF wf1 cA cB cF wfo wa vx cA cB cF df-f1o cA cB cF
      wf1 cA cB cF wfo vx vx cA cB cF nff1o.1 nff1o.2 nff1o.3 nff1 vx cA cB cF
      nff1o.1 nff1o.2 nff1o.3 nffo nfan nfxfr $.
  $}

  $( A one-to-one onto mapping is a one-to-one mapping.  (Contributed by NM,
     12-Dec-2003.) $)
  f1of1 $p |- ( F : A -1-1-onto-> B -> F : A -1-1-> B ) $=
    cA cB cF wf1o cA cB cF wf1 cA cB cF wfo cA cB cF df-f1o simplbi $.

  $( A one-to-one onto mapping is a mapping.  (Contributed by NM,
     12-Dec-2003.) $)
  f1of $p |- ( F : A -1-1-onto-> B -> F : A --> B ) $=
    cA cB cF wf1o cA cB cF wf1 cA cB cF wf cA cB cF f1of1 cA cB cF f1f syl $.

  $( A one-to-one onto mapping is function on its domain.  (Contributed by NM,
     12-Dec-2003.) $)
  f1ofn $p |- ( F : A -1-1-onto-> B -> F Fn A ) $=
    cA cB cF wf1o cA cB cF wf cF cA wfn cA cB cF f1of cA cB cF ffn syl $.

  $( A one-to-one onto mapping is a function.  (Contributed by NM,
     12-Dec-2003.) $)
  f1ofun $p |- ( F : A -1-1-onto-> B -> Fun F ) $=
    cA cB cF wf1o cF cA wfn cF wfun cA cB cF f1ofn cA cF fnfun syl $.

  $( A one-to-one onto mapping is a relation.  (Contributed by NM,
     13-Dec-2003.) $)
  f1orel $p |- ( F : A -1-1-onto-> B -> Rel F ) $=
    cA cB cF wf1o cF wfun cF wrel cA cB cF f1ofun cF funrel syl $.

  $( The domain of a one-to-one onto mapping.  (Contributed by NM,
     8-Mar-2014.) $)
  f1odm $p |- ( F : A -1-1-onto-> B -> dom F = A ) $=
    cA cB cF wf1o cF cA wfn cF cdm cA wceq cA cB cF f1ofn cA cF fndm syl $.

  $( Alternate definition of one-to-one onto function.  (Contributed by NM,
     10-Feb-1997.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
  dff1o2 $p |- ( F : A -1-1-onto-> B
        <-> ( F Fn A /\ Fun `' F /\ ran F = B ) ) $=
    cA cB cF wf1o cA cB cF wf1 cA cB cF wfo wa cF cA wfn cF ccnv wfun cF crn cB
    wceq w3a cA cB cF df-f1o cA cB cF wf1 cA cB cF wfo wa cA cB cF wf cF ccnv
    wfun wa cF cA wfn cF crn cB wceq wa wa cF cA wfn cF ccnv wfun cF crn cB
    wceq w3a cA cB cF wf1 cA cB cF wf cF ccnv wfun wa cA cB cF wfo cF cA wfn cF
    crn cB wceq wa cA cB cF df-f1 cA cB cF df-fo anbi12i cA cB cF wf cF ccnv
    wfun wa cF cA wfn cF crn cB wceq wa wa cA cB cF wf cF ccnv wfun cF cA wfn
    cF crn cB wceq wa wa wa cF cA wfn cF ccnv wfun cF crn cB wceq w3a cA cB cF
    wf cF ccnv wfun cF cA wfn cF crn cB wceq wa anass cF cA wfn cF ccnv wfun cF
    crn cB wceq w3a cA cB cF wf wa cF ccnv wfun cF cA wfn cF crn cB wceq wa wa
    cA cB cF wf wa cF cA wfn cF ccnv wfun cF crn cB wceq w3a cA cB cF wf cF
    ccnv wfun cF cA wfn cF crn cB wceq wa wa wa cF cA wfn cF ccnv wfun cF crn
    cB wceq w3a cF ccnv wfun cF cA wfn cF crn cB wceq wa wa cA cB cF wf cF cA
    wfn cF ccnv wfun cF crn cB wceq 3anan12 anbi1i cF cA wfn cF ccnv wfun cF
    crn cB wceq w3a cA cB cF wf cF cA wfn cF crn cB wceq cA cB cF wf cF ccnv
    wfun cF crn cB wceq cF cA wfn cF crn cB wss cA cB cF wf cF crn cB eqimss cA
    cB cF wf cF cA wfn cF crn cB wss wa cA cB cF df-f biimpri sylan2 3adant2
    pm4.71i cA cB cF wf cF ccnv wfun cF cA wfn cF crn cB wceq wa wa ancom
    3bitr4ri bitri bitri bitri $.

  $( Alternate definition of one-to-one onto function.  (Contributed by NM,
     25-Mar-1998.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
  dff1o3 $p |- ( F : A -1-1-onto-> B <-> ( F : A -onto-> B /\ Fun `' F ) ) $=
    cF cA wfn cF ccnv wfun cF crn cB wceq w3a cF cA wfn cF crn cB wceq wa cF
    ccnv wfun wa cA cB cF wf1o cA cB cF wfo cF ccnv wfun wa cF cA wfn cF ccnv
    wfun cF crn cB wceq 3anan32 cA cB cF dff1o2 cA cB cF wfo cF cA wfn cF crn
    cB wceq wa cF ccnv wfun cA cB cF df-fo anbi1i 3bitr4i $.

  $( A one-to-one onto function is an onto function.  (Contributed by NM,
     28-Apr-2004.) $)
  f1ofo $p |- ( F : A -1-1-onto-> B -> F : A -onto-> B ) $=
    cA cB cF wf1o cA cB cF wfo cF ccnv wfun cA cB cF dff1o3 simplbi $.

  $( Alternate definition of one-to-one onto function.  (Contributed by NM,
     25-Mar-1998.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
  dff1o4 $p |- ( F : A -1-1-onto-> B <-> ( F Fn A /\ `' F Fn B ) ) $=
    cA cB cF wf1o cF cA wfn cF ccnv wfun cF crn cB wceq w3a cF cA wfn cF ccnv
    wfun cF crn cB wceq wa wa cF cA wfn cF ccnv cB wfn wa cA cB cF dff1o2 cF cA
    wfn cF ccnv wfun cF crn cB wceq 3anass cF ccnv wfun cF crn cB wceq wa cF
    ccnv cB wfn cF cA wfn cF ccnv wfun cF crn cB wceq wa cF ccnv wfun cF ccnv
    cdm cB wceq wa cF ccnv cB wfn cF crn cB wceq cF ccnv cdm cB wceq cF ccnv
    wfun cF crn cF ccnv cdm cB cF df-rn eqeq1i anbi2i cF ccnv cB df-fn bitr4i
    anbi2i 3bitri $.

  $( Alternate definition of one-to-one onto function.  (Contributed by NM,
     10-Dec-2003.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
  dff1o5 $p |- ( F : A -1-1-onto-> B <-> ( F : A -1-1-> B /\ ran F = B ) ) $=
    cA cB cF wf1o cA cB cF wf1 cA cB cF wfo wa cA cB cF wf1 cF crn cB wceq wa
    cA cB cF df-f1o cA cB cF wf1 cA cB cF wfo cF crn cB wceq cA cB cF wf1 cF
    crn cB wceq cA cB cF wf cF crn cB wceq wa cA cB cF wfo cA cB cF wf1 cA cB
    cF wf cF crn cB wceq cA cB cF f1f biantrurd cA cB cF dffo2 syl6rbbr pm5.32i
    bitri $.

  $( A one-to-one function maps onto its range.  (Contributed by NM,
     13-Aug-2004.) $)
  f1orn $p |- ( F : A -1-1-onto-> ran F <-> ( F Fn A /\ Fun `' F ) ) $=
    cA cF crn cF wf1o cF cA wfn cF ccnv wfun cF crn cF crn wceq w3a cF cA wfn
    cF ccnv wfun wa cA cF crn cF dff1o2 cF cA wfn cF ccnv wfun cF crn cF crn
    wceq w3a cF cA wfn cF ccnv wfun wa cF crn cF crn wceq cF crn eqid cF cA wfn
    cF ccnv wfun cF crn cF crn wceq df-3an mpbiran2 bitri $.

  $( A one-to-one function maps one-to-one onto its range.  (Contributed by NM,
     4-Sep-2004.) $)
  f1f1orn $p |- ( F : A -1-1-> B -> F : A -1-1-onto-> ran F ) $=
    cA cB cF wf1 cF cA wfn cF ccnv wfun cA cF crn cF wf1o cA cB cF f1fn cA cB
    cF wf1 cA cB cF wf cF ccnv wfun cA cB cF df-f1 simprbi cA cF f1orn sylanbrc
    $.

  ${
    $d A f $.  $d B f $.
    f1oabexg.1 $e |- F = { f | ( f : A -1-1-onto-> B /\ ph ) } $.
    $( The class of all 1-1-onto functions mapping one set to another is a
       set.  (Contributed by Paul Chapman, 25-Feb-2008.) $)
    f1oabexg $p |- ( ( A e. C /\ B e. D ) -> F e. _V ) $=
      cA cC wcel cB cD wcel wa cF cA cB vf cv wf1o wph wa vf cab cvv f1oabexg.1
      cA cC wcel cB cD wcel wa cA cB vf cv wf1o wph wa vf cab cA cB vf cv wf
      wph wa vf cab wss cA cB vf cv wf wph wa vf cab cvv wcel cA cB vf cv wf1o
      wph wa vf cab cvv wcel cA cB vf cv wf1o wph wa cA cB vf cv wf wph wa vf
      cA cB vf cv wf1o cA cB vf cv wf wph cA cB vf cv f1of anim1i ss2abi wph vf
      cA cB cC cD cA cB vf cv wf wph wa vf cab cA cB vf cv wf wph wa vf cab
      eqid fabexg cA cB vf cv wf1o wph wa vf cab cA cB vf cv wf wph wa vf cab
      cvv ssexg sylancr syl5eqel $.
  $}

  $( The converse of a one-to-one onto function is also one-to-one onto.
     (Contributed by NM, 11-Feb-1997.)  (Proof shortened by Andrew Salmon,
     22-Oct-2011.) $)
  f1ocnv $p |- ( F : A -1-1-onto-> B -> `' F : B -1-1-onto-> A ) $=
    cF cA wfn cF ccnv cB wfn wa cF ccnv cB wfn cF ccnv ccnv cA wfn wa cA cB cF
    wf1o cB cA cF ccnv wf1o cF ccnv cB wfn cF cA wfn cF ccnv cB wfn cF ccnv
    ccnv cA wfn wa cF cA wfn cF ccnv ccnv cA wfn cF ccnv cB wfn cF wrel cF cA
    wfn cF ccnv ccnv cA wfn cA cF fnrel cF wrel cF ccnv ccnv cF wceq cF cA wfn
    cF ccnv ccnv cA wfn wi cF dfrel2 cF ccnv ccnv cF wceq cF ccnv ccnv cA wfn
    cF cA wfn cA cF ccnv ccnv cF fneq1 biimprd sylbi mpcom anim2i ancoms cA cB
    cF dff1o4 cB cA cF ccnv dff1o4 3imtr4i $.

  $( A relation is a one-to-one onto function iff its converse is a one-to-one
     onto function with domain and range interchanged.  (Contributed by NM,
     8-Dec-2003.) $)
  f1ocnvb $p |- ( Rel F ->
                ( F : A -1-1-onto-> B <-> `' F : B -1-1-onto-> A ) ) $=
    cF wrel cA cB cF wf1o cB cA cF ccnv wf1o cA cB cF f1ocnv cB cA cF ccnv wf1o
    cA cB cF ccnv ccnv wf1o cF wrel cA cB cF wf1o cB cA cF ccnv f1ocnv cF wrel
    cF ccnv ccnv cF wceq cA cB cF ccnv ccnv wf1o cA cB cF wf1o wb cF dfrel2 cA
    cB cF ccnv ccnv cF f1oeq1 sylbi syl5ib impbid2 $.

  $( The restriction of a one-to-one function maps one-to-one onto the image.
     (Contributed by NM, 25-Mar-1998.) $)
  f1ores $p |- ( ( F : A -1-1-> B /\ C C_ A ) -> ( F |` C ) : C -1-1-onto->
            ( F " C ) ) $=
    cA cB cF wf1 cC cA wss wa cC cF cC cres crn cF cC cres wf1o cC cF cC cima
    cF cC cres wf1o cA cB cF wf1 cC cA wss wa cC cB cF cC cres wf1 cC cF cC
    cres crn cF cC cres wf1o cA cB cC cF f1ssres cC cB cF cC cres f1f1orn syl
    cF cC cima cF cC cres crn wceq cC cF cC cima cF cC cres wf1o cC cF cC cres
    crn cF cC cres wf1o wb cF cC df-ima cF cC cima cF cC cres crn cC cF cC cres
    f1oeq3 ax-mp sylibr $.

  $( The converse of a one-to-one-onto restricted function.  (Contributed by
     Paul Chapman, 21-Apr-2008.) $)
  f1orescnv $p |- ( ( Fun `' F /\ ( F |` R ) : R -1-1-onto-> P ) ->
                    ( `' F |` P ) : P -1-1-onto-> R ) $=
    cF ccnv wfun cR cP cF cR cres wf1o wa cP cR cF cR cres ccnv wf1o cP cR cF
    ccnv cP cres wf1o cR cP cF cR cres wf1o cP cR cF cR cres ccnv wf1o cF ccnv
    wfun cR cP cF cR cres f1ocnv adantl cF ccnv wfun cR cP cF cR cres wf1o wa
    cF cR cres ccnv cF ccnv cP cres wceq cP cR cF cR cres ccnv wf1o cP cR cF
    ccnv cP cres wf1o wb cF ccnv wfun cR cP cF cR cres wf1o cF cR cres ccnv cF
    ccnv cF cR cima cres cF ccnv cP cres cR cF funcnvres cR cP cF cR cres wf1o
    cF cR cima cP cF ccnv cR cP cF cR cres wf1o cF cR cima cF cR cres crn cP cF
    cR df-ima cR cP cF cR cres wf1o cR cP cF cR cres wf1 cF cR cres crn cP wceq
    cR cP cF cR cres dff1o5 simprbi syl5eq reseq2d sylan9eq cP cR cF cR cres
    ccnv cF ccnv cP cres f1oeq1 syl mpbid $.

  $( Preimage of an image.  (Contributed by NM, 30-Sep-2004.) $)
  f1imacnv $p |- ( ( F : A -1-1-> B /\ C C_ A )
                 -> ( `' F " ( F " C ) ) = C ) $=
    cA cB cF wf1 cC cA wss wa cF ccnv cF cC cima cima cF ccnv cF cC cima cres
    cF cC cima cima cC cF ccnv cF cC cima resima cA cB cF wf1 cC cA wss wa cF
    cC cres ccnv cF cC cima cima cF ccnv cF cC cima cres cF cC cima cima cC cA
    cB cF wf1 cC cA wss wa cF cC cres ccnv cF ccnv cF cC cima cres cF cC cima
    cA cB cF wf1 cC cA wss wa cF ccnv wfun cF cC cres ccnv cF ccnv cF cC cima
    cres wceq cA cB cF wf1 cF ccnv wfun cC cA wss cA cB cF wf1 cA cB cF wf cF
    ccnv wfun cA cB cF df-f1 simprbi adantr cC cF funcnvres syl imaeq1d cA cB
    cF wf1 cC cA wss wa cF cC cima cC cF cC cres ccnv wf1o cF cC cres ccnv cF
    cC cima cima cC wceq cA cB cF wf1 cC cA wss wa cC cF cC cima cF cC cres
    wf1o cF cC cima cC cF cC cres ccnv wf1o cA cB cC cF f1ores cC cF cC cima cF
    cC cres f1ocnv syl cF cC cima cC cF cC cres ccnv wf1o cF cC cres ccnv cF cC
    cres ccnv cdm cima cF cC cres ccnv crn cF cC cres ccnv cF cC cima cima cC
    cF cC cres ccnv imadmrn cF cC cima cC cF cC cres ccnv wf1o cF cC cres ccnv
    cdm cF cC cima cF cC cres ccnv cF cC cima cC cF cC cres ccnv f1odm imaeq2d
    cF cC cima cC cF cC cres ccnv wf1o cF cC cima cC cF cC cres ccnv wfo cF cC
    cres ccnv crn cC wceq cF cC cima cC cF cC cres ccnv f1ofo cF cC cima cC cF
    cC cres ccnv forn syl 3eqtr3a syl eqtr3d syl5eqr $.

  $( A reverse version of ~ f1imacnv .  (Contributed by Jeffrey Hankins,
     16-Jul-2009.) $)
  foimacnv $p |- ( ( F : A -onto-> B /\ C C_ B )
                 -> ( F " ( `' F " C ) ) = C ) $=
    cA cB cF wfo cC cB wss wa cF cF ccnv cC cima cima cF cF ccnv cC cima cres
    cF ccnv cC cima cima cC cF cF ccnv cC cima resima cA cB cF wfo cC cB wss wa
    cF ccnv cC cres ccnv cF ccnv cC cima cima cF cF ccnv cC cima cres cF ccnv
    cC cima cima cC cA cB cF wfo cC cB wss wa cF ccnv cC cres ccnv cF cF ccnv
    cC cima cres cF ccnv cC cima cA cB cF wfo cC cB wss wa cF wfun cF ccnv cC
    cres ccnv cF cF ccnv cC cima cres wceq cA cB cF wfo cF wfun cC cB wss cA cB
    cF fofun adantr cC cF funcnvres2 syl imaeq1d cA cB cF wfo cC cB wss wa cF
    ccnv cC cima cC cF ccnv cC cres ccnv wfo cF ccnv cC cres ccnv cF ccnv cC
    cima cima cC wceq cA cB cF wfo cC cB wss wa cF ccnv cC cres ccnv cF ccnv cC
    cima wfn cF ccnv cC cres ccnv crn cC wceq cF ccnv cC cima cC cF ccnv cC
    cres ccnv wfo cA cB cF wfo cC cB wss wa cF ccnv cC cres ccnv wfun cF ccnv
    cC cres ccnv cdm cF ccnv cC cima wceq wa cF ccnv cC cres ccnv cF ccnv cC
    cima wfn cA cB cF wfo cC cB wss wa cF ccnv cC cres ccnv wfun cF ccnv cC
    cres ccnv cdm cF ccnv cC cima wceq cA cB cF wfo cF ccnv cC cres ccnv wfun
    cC cB wss cF ccnv cC cres ccnv cF wss cA cB cF wfo cF wfun cF ccnv cC cres
    ccnv wfun cF ccnv cC cres ccnv cF ccnv ccnv cF cF ccnv cC cres cF ccnv wss
    cF ccnv cC cres ccnv cF ccnv ccnv wss cF ccnv cC resss cF ccnv cC cres cF
    ccnv cnvss ax-mp cF cnvcnvss sstri cA cB cF fofun cF ccnv cC cres ccnv cF
    funss mpsyl adantr cF ccnv cC cima cF ccnv cC cres crn cF ccnv cC cres ccnv
    cdm cF ccnv cC df-ima cF ccnv cC cres df-rn eqtr2i jctir cF ccnv cC cres
    ccnv cF ccnv cC cima df-fn sylibr cA cB cF wfo cC cB wss wa cF ccnv cC cres
    ccnv crn cF ccnv cC cres cdm cC cF ccnv cC cres dfdm4 cA cB cF wfo cC cB
    wss wa cC cF ccnv cdm wss cF ccnv cC cres cdm cC wceq cA cB cF wfo cC cB
    wss wa cC cF crn cF ccnv cdm cA cB cF wfo cC cF crn wss cC cB wss cA cB cF
    wfo cF crn cB cC cA cB cF forn sseq2d biimpar cF df-rn syl6sseq cC cF ccnv
    ssdmres sylib syl5eqr cF ccnv cC cima cC cF ccnv cC cres ccnv df-fo
    sylanbrc cF ccnv cC cima cC cF ccnv cC cres ccnv foima syl eqtr3d syl5eqr
    $.

  $( The union of two onto functions with disjoint domains is an onto
     function.  (Contributed by Mario Carneiro, 22-Jun-2016.) $)
  foun $p |- ( ( ( F : A -onto-> B /\ G : C -onto-> D )
            /\ ( A i^i C ) = (/) )
           -> ( F u. G ) : ( A u. C ) -onto-> ( B u. D ) ) $=
    cA cB cF wfo cC cD cG wfo wa cA cC cin c0 wceq wa cF cG cun cA cC cun wfn
    cF cG cun crn cB cD cun wceq cA cC cun cB cD cun cF cG cun wfo cA cB cF wfo
    cC cD cG wfo wa cF cA wfn cG cC wfn wa cA cC cin c0 wceq cF cG cun cA cC
    cun wfn cA cB cF wfo cF cA wfn cC cD cG wfo cG cC wfn cA cB cF fofn cC cD
    cG fofn anim12i cA cC cF cG fnun sylan cA cB cF wfo cC cD cG wfo wa cA cC
    cin c0 wceq wa cF cG cun crn cF crn cG crn cun cB cD cun cF cG rnun cA cB
    cF wfo cC cD cG wfo wa cA cC cin c0 wceq wa cF crn cB cG crn cD cA cB cF
    wfo cF crn cB wceq cC cD cG wfo cA cC cin c0 wceq cA cB cF forn ad2antrr cC
    cD cG wfo cG crn cD wceq cA cB cF wfo cA cC cin c0 wceq cC cD cG forn
    ad2antlr uneq12d syl5eq cA cC cun cB cD cun cF cG cun df-fo sylanbrc $.

  $( The union of two one-to-one onto functions with disjoint domains and
     ranges.  (Contributed by NM, 26-Mar-1998.) $)
  f1oun $p |- ( ( ( F : A -1-1-onto-> B /\ G : C -1-1-onto-> D )
            /\ ( ( A i^i C ) = (/) /\ ( B i^i D ) = (/) ) )
           -> ( F u. G ) : ( A u. C ) -1-1-onto-> ( B u. D ) ) $=
    cA cB cF wf1o cC cD cG wf1o wa cA cC cin c0 wceq cB cD cin c0 wceq wa cA cC
    cun cB cD cun cF cG cun wf1o cA cB cF wf1o cC cD cG wf1o wa cA cC cin c0
    wceq cB cD cin c0 wceq wa cF cG cun cA cC cun wfn cF cG cun ccnv cB cD cun
    wfn wa cA cC cun cB cD cun cF cG cun wf1o cA cB cF wf1o cF cA wfn cF ccnv
    cB wfn wa cG cC wfn cG ccnv cD wfn wa cA cC cin c0 wceq cB cD cin c0 wceq
    wa cF cG cun cA cC cun wfn cF cG cun ccnv cB cD cun wfn wa wi cC cD cG wf1o
    cA cB cF dff1o4 cC cD cG dff1o4 cF cA wfn cG cC wfn cF ccnv cB wfn cG ccnv
    cD wfn cA cC cin c0 wceq cB cD cin c0 wceq wa cF cG cun cA cC cun wfn cF cG
    cun ccnv cB cD cun wfn wa wi cF cA wfn cG cC wfn wa cA cC cin c0 wceq cF cG
    cun cA cC cun wfn cF ccnv cB wfn cG ccnv cD wfn wa cB cD cin c0 wceq cF cG
    cun ccnv cB cD cun wfn cF cA wfn cG cC wfn wa cA cC cin c0 wceq cF cG cun
    cA cC cun wfn cA cC cF cG fnun ex cF ccnv cB wfn cG ccnv cD wfn wa cB cD
    cin c0 wceq cF cG cun ccnv cB cD cun wfn cF ccnv cB wfn cG ccnv cD wfn wa
    cB cD cin c0 wceq wa cF ccnv cG ccnv cun cB cD cun wfn cF cG cun ccnv cB cD
    cun wfn cB cD cF ccnv cG ccnv fnun cB cD cun cF cG cun ccnv cF ccnv cG ccnv
    cun cF cG cnvun fneq1i sylibr ex im2anan9 an4s syl2anb cA cC cun cB cD cun
    cF cG cun dff1o4 syl6ibr imp $.

  ${
    $d A u v x z $.  $d A u v y $.  $d B u v y $.  $d B u v z $.  $d C u v x $.
    $d D u v $.  $d S u v x $.
    fun11iun.1 $e |- ( x = y -> B = C ) $.
    fun11iun.2 $e |- B e. _V $.
    $( The union of a chain (with respect to inclusion) of one-to-one functions
       is a one-to-one function.  (Contributed by Mario Carneiro,
       20-May-2013.)  (Revised by Mario Carneiro, 24-Jun-2015.) $)
    fun11iun $p |- ( A. x e. A ( B : D -1-1-> S /\
                       A. y e. A ( B C_ C \/ C C_ B ) ) ->
                     U_ x e. A B : U_ x e. A D -1-1-> S ) $=
      cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral vx cA cD
      ciun cS vx cA cB ciun wf vx cA cB ciun ccnv wfun vx cA cD ciun cS vx cA
      cB ciun wf1 cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral
      vx cA cB ciun vx cA cD ciun wfn vx cA cB ciun crn cS wss vx cA cD ciun cS
      vx cA cB ciun wf cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA
      wral vx cA cB ciun wfun vx cA cB ciun cdm vx cA cD ciun wceq vx cA cB
      ciun vx cA cD ciun wfn cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa
      vx cA wral vz cv cB wceq vx cA wrex vz cab cuni wfun vx cA cB ciun wfun
      cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral vz cv cB
      wceq vx cA wrex vz cab cuni wfun vz cv cB wceq vx cA wrex vz cab cuni
      ccnv wfun cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral vu
      cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss wo vv vz cv cB
      wceq vx cA wrex vz cab wral wa vu vz cv cB wceq vx cA wrex vz cab wral vz
      cv cB wceq vx cA wrex vz cab cuni wfun vz cv cB wceq vx cA wrex vz cab
      cuni ccnv wfun wa cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA
      wral vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss wo vv
      vz cv cB wceq vx cA wrex vz cab wral wa vu vz cv cB wceq vx cA wrex vz
      cab vu cv vz cv cB wceq vx cA wrex vz cab wcel cD cS cB wf1 cB cC wss cC
      cB wss wo vy cA wral wa vx cA wral vu cv cB wceq vx cA wrex vu cv wfun vu
      cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA
      wrex vz cab wral wa vz cv cB wceq vx cA wrex vu cv cB wceq vx cA wrex vz
      vu cv vu vex vz cv vu cv wceq vz cv cB wceq vu cv cB wceq vx cA vz cv vu
      cv cB eqeq1 rexbidv elab cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral
      wa vx cA wral vu cv cB wceq vx cA wrex wa cD cS cB wf1 cB cC wss cC cB
      wss wo vy cA wral wa vu cv cB wceq wa vx cA wrex vu cv wfun vu cv ccnv
      wfun wa vu cv vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz
      cab wral wa cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv cB
      wceq vx cA r19.29 cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv
      cB wceq wa vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss
      wo vv vz cv cB wceq vx cA wrex vz cab wral wa vx cA vu cv wfun vu cv ccnv
      wfun wa vu cv vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz
      cab wral vx vu cv wfun vu cv ccnv wfun wa vx nfv vu cv vv cv wss vv cv vu
      cv wss wo vx vv vz cv cB wceq vx cA wrex vz cab vz cv cB wceq vx cA wrex
      vx vz vz cv cB wceq vx cA nfre1 nfab vu cv vv cv wss vv cv vu cv wss wo
      vx nfv nfral nfan cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv
      cB wceq wa vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss
      wo vv vz cv cB wceq vx cA wrex vz cab wral wa wi vx cv cA wcel cD cS cB
      wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv cB wceq wa vu cv wfun vu
      cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA
      wrex vz cab wral cD cS cB wf1 vu cv cB wceq vu cv wfun vu cv ccnv wfun wa
      cB cC wss cC cB wss wo vy cA wral cD cS cB wf1 vu cv cB wceq wa cD cS vu
      cv wf1 vu cv wfun vu cv ccnv wfun wa vu cv cB wceq cD cS vu cv wf1 cD cS
      cB wf1 cD cS vu cv cB f1eq1 biimparc cD cS vu cv wf1 cD cS vu cv wf vu cv
      ccnv wfun wa vu cv wfun vu cv ccnv wfun wa cD cS vu cv df-f1 cD cS vu cv
      wf vu cv wfun vu cv ccnv wfun cD cS vu cv ffun anim1i sylbi syl adantlr
      cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv cB wceq wa vu cv
      vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz cab vv cv vz
      cv cB wceq vx cA wrex vz cab wcel cD cS cB wf1 cB cC wss cC cB wss wo vy
      cA wral wa vu cv cB wceq wa vv cv cB wceq vx cA wrex vu cv vv cv wss vv
      cv vu cv wss wo vz cv cB wceq vx cA wrex vv cv cB wceq vx cA wrex vz vv
      cv vv vex vz cv vv cv wceq vz cv cB wceq vv cv cB wceq vx cA vz cv vv cv
      cB eqeq1 rexbidv elab vv cv cB wceq vx cA wrex cD cS cB wf1 cB cC wss cC
      cB wss wo vy cA wral wa vu cv cB wceq wa vv cv cC wceq vy cA wrex vu cv
      vv cv wss vv cv vu cv wss wo vv cv cB wceq vv cv cC wceq vx vy cA vx cv
      vy cv wceq cB cC vv cv fun11iun.1 eqeq2d cbvrexv cB cC wss cC cB wss wo
      vy cA wral vu cv cB wceq vv cv cC wceq vy cA wrex vu cv vv cv wss vv cv
      vu cv wss wo cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral vv cv cC wceq
      vy cA wrex vu cv cB wceq vu cv vv cv wss vv cv vu cv wss wo cB cC wss cC
      cB wss wo vy cA wral vv cv cC wceq vy cA wrex wa cB cC wss cC cB wss wo
      vv cv cC wceq wa vy cA wrex vu cv cB wceq vu cv vv cv wss vv cv vu cv wss
      wo cB cC wss cC cB wss wo vv cv cC wceq vy cA r19.29 cB cC wss cC cB wss
      wo vv cv cC wceq wa vy cA wrex vu cv cB wceq vu cv vv cv wss vv cv vu cv
      wss wo cB cC wss cC cB wss wo vv cv cC wceq wa vu cv cB wceq vu cv vv cv
      wss vv cv vu cv wss wo wi vy cA cB cC wss cC cB wss wo vv cv cC wceq vu
      cv cB wceq vu cv vv cv wss vv cv vu cv wss wo vv cv cC wceq vu cv cB wceq
      wa vu cv vv cv wss vv cv vu cv wss wo cB cC wss cC cB wss wo vv cv cC
      wceq vu cv cB wceq wa vu cv vv cv wss cB cC wss vv cv vu cv wss cC cB wss
      vu cv cB wceq vv cv cC wceq vu cv vv cv wss cB cC wss wb vu cv cB vv cv
      cC sseq12 ancoms vv cv cC vu cv cB sseq12 orbi12d biimprcd expdimp
      rexlimivw imp sylan an32s adantlll sylan2b sylan2b ralrimiva jca a1i
      rexlimi syl sylan2b ralrimiva vz cv cB wceq vx cA wrex vz cab vu vv
      fun11uni syl simpld vx cA cB ciun vz cv cB wceq vx cA wrex vz cab cuni vx
      vz cA cB fun11iun.2 dfiun2 funeqi sylibr cD cS cB wf1 cB cC wss cC cB wss
      wo vy cA wral wa vx cA wral vu vx cA cB ciun cdm vx cA cD ciun cD cS cB
      wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral vu cv vv cv cop cB
      wcel vv wex vx cA wrex vu cv cD wcel vx cA wrex vu cv vx cA cB ciun cdm
      wcel vu cv vx cA cD ciun wcel cD cS cB wf1 cB cC wss cC cB wss wo vy cA
      wral wa vx cA wral vu cv vv cv cop cB wcel vv wex vu cv cD wcel vx cA cD
      cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA nfra1 cD cS cB wf1
      cB cC wss cC cB wss wo vy cA wral wa vx cA wral vx cv cA wcel vu cv vv cv
      cop cB wcel vv wex vu cv cD wcel wb cD cS cB wf1 cB cC wss cC cB wss wo
      vy cA wral wa vx cA wral vx cv cA wcel cD cS cB wf1 cB cC wss cC cB wss
      wo vy cA wral wa vu cv vv cv cop cB wcel vv wex vu cv cD wcel wb cD cS cB
      wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA rsp cD cS cB wf1 vu cv vv
      cv cop cB wcel vv wex vu cv cD wcel wb cB cC wss cC cB wss wo vy cA wral
      vu cv vv cv cop cB wcel vv wex vu cv cB cdm wcel cD cS cB wf1 vu cv cD
      wcel vv vu cv cB vu vex eldm2 cD cS cB wf1 cB cdm cD vu cv cD cS cB f1dm
      eleq2d syl5bbr adantr syl6 imp rexbida vu cv vv cv cop vx cA cB ciun wcel
      vv wex vu cv vv cv cop cB wcel vx cA wrex vv wex vu cv vx cA cB ciun cdm
      wcel vu cv vv cv cop cB wcel vv wex vx cA wrex vu cv vv cv cop vx cA cB
      ciun wcel vu cv vv cv cop cB wcel vx cA wrex vv vx vu cv vv cv cop cA cB
      eliun exbii vv vu cv vx cA cB ciun vu vex eldm2 vu cv vv cv cop cB wcel
      vx vv cA rexcom4 3bitr4i vx vu cv cA cD eliun 3bitr4g eqrdv vx cA cB ciun
      vx cA cD ciun df-fn sylanbrc cD cS cB wf1 cB cC wss cC cB wss wo vy cA
      wral wa vx cA wral vx cA cB ciun crn vx cA cB crn ciun cS vx cA cB rniun
      cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral cB crn cS
      wss vx cA wral vx cA cB crn ciun cS wss cD cS cB wf1 cB cC wss cC cB wss
      wo vy cA wral wa cB crn cS wss vx cA cD cS cB wf1 cB crn cS wss cB cC wss
      cC cB wss wo vy cA wral cD cS cB wf1 cD cS cB wf cB crn cS wss cD cS cB
      f1f cD cS cB frn syl adantr ralimi vx cA cB crn cS iunss sylibr syl5eqss
      vx cA cD ciun cS vx cA cB ciun df-f sylanbrc cD cS cB wf1 cB cC wss cC cB
      wss wo vy cA wral wa vx cA wral vz cv cB wceq vx cA wrex vz cab cuni ccnv
      wfun vx cA cB ciun ccnv wfun cD cS cB wf1 cB cC wss cC cB wss wo vy cA
      wral wa vx cA wral vz cv cB wceq vx cA wrex vz cab cuni wfun vz cv cB
      wceq vx cA wrex vz cab cuni ccnv wfun cD cS cB wf1 cB cC wss cC cB wss wo
      vy cA wral wa vx cA wral vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv
      cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz cab wral wa vu vz cv cB
      wceq vx cA wrex vz cab wral vz cv cB wceq vx cA wrex vz cab cuni wfun vz
      cv cB wceq vx cA wrex vz cab cuni ccnv wfun wa cD cS cB wf1 cB cC wss cC
      cB wss wo vy cA wral wa vx cA wral vu cv wfun vu cv ccnv wfun wa vu cv vv
      cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz cab wral wa vu
      vz cv cB wceq vx cA wrex vz cab vu cv vz cv cB wceq vx cA wrex vz cab
      wcel cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vx cA wral vu cv
      cB wceq vx cA wrex vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu
      cv wss wo vv vz cv cB wceq vx cA wrex vz cab wral wa vz cv cB wceq vx cA
      wrex vu cv cB wceq vx cA wrex vz vu cv vu vex vz cv vu cv wceq vz cv cB
      wceq vu cv cB wceq vx cA vz cv vu cv cB eqeq1 rexbidv elab cD cS cB wf1
      cB cC wss cC cB wss wo vy cA wral wa vx cA wral vu cv cB wceq vx cA wrex
      wa cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv cB wceq wa vx
      cA wrex vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss wo
      vv vz cv cB wceq vx cA wrex vz cab wral wa cD cS cB wf1 cB cC wss cC cB
      wss wo vy cA wral wa vu cv cB wceq vx cA r19.29 cD cS cB wf1 cB cC wss cC
      cB wss wo vy cA wral wa vu cv cB wceq wa vu cv wfun vu cv ccnv wfun wa vu
      cv vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz cab wral
      wa vx cA vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv vu cv wss wo
      vv vz cv cB wceq vx cA wrex vz cab wral vx vu cv wfun vu cv ccnv wfun wa
      vx nfv vu cv vv cv wss vv cv vu cv wss wo vx vv vz cv cB wceq vx cA wrex
      vz cab vz cv cB wceq vx cA wrex vx vz vz cv cB wceq vx cA nfre1 nfab vu
      cv vv cv wss vv cv vu cv wss wo vx nfv nfral nfan cD cS cB wf1 cB cC wss
      cC cB wss wo vy cA wral wa vu cv cB wceq wa vu cv wfun vu cv ccnv wfun wa
      vu cv vv cv wss vv cv vu cv wss wo vv vz cv cB wceq vx cA wrex vz cab
      wral wa wi vx cv cA wcel cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral
      wa vu cv cB wceq wa vu cv wfun vu cv ccnv wfun wa vu cv vv cv wss vv cv
      vu cv wss wo vv vz cv cB wceq vx cA wrex vz cab wral cD cS cB wf1 vu cv
      cB wceq vu cv wfun vu cv ccnv wfun wa cB cC wss cC cB wss wo vy cA wral
      cD cS cB wf1 vu cv cB wceq wa cD cS vu cv wf1 vu cv wfun vu cv ccnv wfun
      wa vu cv cB wceq cD cS vu cv wf1 cD cS cB wf1 cD cS vu cv cB f1eq1
      biimparc cD cS vu cv wf1 cD cS vu cv wf vu cv ccnv wfun wa vu cv wfun vu
      cv ccnv wfun wa cD cS vu cv df-f1 cD cS vu cv wf vu cv wfun vu cv ccnv
      wfun cD cS vu cv ffun anim1i sylbi syl adantlr cD cS cB wf1 cB cC wss cC
      cB wss wo vy cA wral wa vu cv cB wceq wa vu cv vv cv wss vv cv vu cv wss
      wo vv vz cv cB wceq vx cA wrex vz cab vv cv vz cv cB wceq vx cA wrex vz
      cab wcel cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu cv cB wceq
      wa vv cv cB wceq vx cA wrex vu cv vv cv wss vv cv vu cv wss wo vz cv cB
      wceq vx cA wrex vv cv cB wceq vx cA wrex vz vv cv vv vex vz cv vv cv wceq
      vz cv cB wceq vv cv cB wceq vx cA vz cv vv cv cB eqeq1 rexbidv elab vv cv
      cB wceq vx cA wrex cD cS cB wf1 cB cC wss cC cB wss wo vy cA wral wa vu
      cv cB wceq wa vv cv cC wceq vy cA wrex vu cv vv cv wss vv cv vu cv wss wo
      vv cv cB wceq vv cv cC wceq vx vy cA vx cv vy cv wceq cB cC vv cv
      fun11iun.1 eqeq2d cbvrexv cB cC wss cC cB wss wo vy cA wral vu cv cB wceq
      vv cv cC wceq vy cA wrex vu cv vv cv wss vv cv vu cv wss wo cD cS cB wf1
      cB cC wss cC cB wss wo vy cA wral vv cv cC wceq vy cA wrex vu cv cB wceq
      vu cv vv cv wss vv cv vu cv wss wo cB cC wss cC cB wss wo vy cA wral vv
      cv cC wceq vy cA wrex wa cB cC wss cC cB wss wo vv cv cC wceq wa vy cA
      wrex vu cv cB wceq vu cv vv cv wss vv cv vu cv wss wo cB cC wss cC cB wss
      wo vv cv cC wceq vy cA r19.29 cB cC wss cC cB wss wo vv cv cC wceq wa vy
      cA wrex vu cv cB wceq vu cv vv cv wss vv cv vu cv wss wo cB cC wss cC cB
      wss wo vv cv cC wceq wa vu cv cB wceq vu cv vv cv wss vv cv vu cv wss wo
      wi vy cA cB cC wss cC cB wss wo vv cv cC wceq vu cv cB wceq vu cv vv cv
      wss vv cv vu cv wss wo vv cv cC wceq vu cv cB wceq wa vu cv vv cv wss vv
      cv vu cv wss wo cB cC wss cC cB wss wo vv cv cC wceq vu cv cB wceq wa vu
      cv vv cv wss cB cC wss vv cv vu cv wss cC cB wss vu cv cB wceq vv cv cC
      wceq vu cv vv cv wss cB cC wss wb vu cv cB vv cv cC sseq12 ancoms vv cv
      cC vu cv cB sseq12 orbi12d biimprcd expdimp rexlimivw imp sylan an32s
      adantlll sylan2b sylan2b ralrimiva jca a1i rexlimi syl sylan2b ralrimiva
      vz cv cB wceq vx cA wrex vz cab vu vv fun11uni syl simprd vx cA cB ciun
      ccnv vz cv cB wceq vx cA wrex vz cab cuni ccnv vx cA cB ciun vz cv cB
      wceq vx cA wrex vz cab cuni vx vz cA cB fun11iun.2 dfiun2 cnveqi funeqi
      sylibr vx cA cD ciun cS vx cA cB ciun df-f1 sylanbrc $.
  $}

  $( The restriction of a one-to-one onto function to a difference maps onto
     the difference of the images.  (Contributed by Paul Chapman,
     11-Apr-2009.) $)
  resdif $p |- ( ( Fun `' F /\ ( F |` A ) : A -onto-> C /\
                               ( F |` B ) : B -onto-> D ) ->
                 ( F |` ( A \ B ) ) : ( A \ B ) -1-1-onto-> ( C \ D ) ) $=
    cF ccnv wfun cA cC cF cA cres wfo cB cD cF cB cres wfo w3a cA cB cdif cF cA
    cB cdif cima cF cA cB cdif cres wf1o cA cB cdif cC cD cdif cF cA cB cdif
    cres wf1o cF ccnv wfun cA cC cF cA cres wfo cA cB cdif cF cA cB cdif cima
    cF cA cB cdif cres wf1o cB cD cF cB cres wfo cA cC cF cA cres wfo cA cB
    cdif cF cA cB cdif cima cF cA cB cdif cres wfo cF cA cB cdif cres ccnv wfun
    cA cB cdif cF cA cB cdif cima cF cA cB cdif cres wf1o cF ccnv wfun cA cC cF
    cA cres wfo cA cB cdif cF cA cres cA cB cdif cima cF cA cres cA cB cdif
    cres wfo cA cB cdif cF cA cB cdif cima cF cA cB cdif cres wfo cA cC cF cA
    cres wfo cF cA cres wfun cA cB cdif cF cA cres cdm wss cA cB cdif cF cA
    cres cA cB cdif cima cF cA cres cA cB cdif cres wfo cA cC cF cA cres fofun
    cA cC cF cA cres wfo cA cA cB cdif cF cA cres cdm cA cB difss cA cC cF cA
    cres wfo cA cC cF cA cres wf cF cA cres cdm cA wceq cA cC cF cA cres fof cA
    cC cF cA cres fdm syl syl5sseqr cA cB cdif cF cA cres fores syl2anc cA cB
    cdif cF cA cres cA cB cdif cima cF cA cres cA cB cdif cres wfo cA cB cdif
    cF cA cres cA cB cdif cima cF cA cB cdif cres wfo cA cB cdif cF cA cB cdif
    cima cF cA cB cdif cres wfo cF cA cres cA cB cdif cres cF cA cB cdif cres
    wceq cA cB cdif cF cA cres cA cB cdif cima cF cA cres cA cB cdif cres wfo
    cA cB cdif cF cA cres cA cB cdif cima cF cA cB cdif cres wfo wb cF cA cres
    cA cB cdif cres cF cA cA cB cdif cin cres cF cA cB cdif cres cF cA cA cB
    cdif resres cA cA cB cdif cin cA cB cdif cF cA cB indif reseq2i eqtri cA cB
    cdif cF cA cres cA cB cdif cima cF cA cres cA cB cdif cres cF cA cB cdif
    cres foeq1 ax-mp cF cA cres cA cB cdif cima cF cA cB cdif cima wceq cA cB
    cdif cF cA cres cA cB cdif cima cF cA cB cdif cres wfo cA cB cdif cF cA cB
    cdif cima cF cA cB cdif cres wfo wb cF cA cres cA cB cdif cres crn cF cA cB
    cdif cres crn cF cA cres cA cB cdif cima cF cA cB cdif cima cF cA cres cA
    cB cdif cres cF cA cB cdif cres cF cA cres cA cB cdif cres cF cA cA cB cdif
    cin cres cF cA cB cdif cres cF cA cA cB cdif resres cA cA cB cdif cin cA cB
    cdif cF cA cB indif reseq2i eqtri rneqi cF cA cres cA cB cdif df-ima cF cA
    cB cdif df-ima 3eqtr4i cF cA cres cA cB cdif cima cF cA cB cdif cima cA cB
    cdif cF cA cB cdif cres foeq3 ax-mp bitri sylib cA cB cdif cF funres11 cA
    cB cdif cF cA cB cdif cima cF cA cB cdif cres wf1o cA cB cdif cF cA cB cdif
    cima cF cA cB cdif cres wfo cF cA cB cdif cres ccnv wfun wa cA cB cdif cF
    cA cB cdif cima cF cA cB cdif cres dff1o3 biimpri syl2anr 3adant3 cF ccnv
    wfun cA cC cF cA cres wfo cB cD cF cB cres wfo w3a cF cA cB cdif cima cC cD
    cdif wceq cA cB cdif cF cA cB cdif cima cF cA cB cdif cres wf1o cA cB cdif
    cC cD cdif cF cA cB cdif cres wf1o wb cF ccnv wfun cA cC cF cA cres wfo cB
    cD cF cB cres wfo cF cA cB cdif cima cC cD cdif wceq cA cC cF cA cres wfo
    cB cD cF cB cres wfo wa cF ccnv wfun cF cA cima cC wceq cF cB cima cD wceq
    wa cF cA cB cdif cima cC cD cdif wceq cA cC cF cA cres wfo cF cA cima cC
    wceq cB cD cF cB cres wfo cF cB cima cD wceq cA cC cF cA cres wfo cF cA
    cima cF cA cres crn cC cF cA df-ima cA cC cF cA cres forn syl5eq cB cD cF
    cB cres wfo cF cB cima cF cB cres crn cD cF cB df-ima cB cD cF cB cres forn
    syl5eq anim12i cF ccnv wfun cF cA cima cC wceq cF cB cima cD wceq wa cF cA
    cB cdif cima cF cA cima cF cB cima cdif cC cD cdif cA cB cF imadif cF cA
    cima cC cF cB cima cD difeq12 sylan9eq sylan2 3impb cF cA cB cdif cima cC
    cD cdif cA cB cdif cF cA cB cdif cres f1oeq3 syl mpbid $.

  $( The restriction of a one-to-one onto function to an intersection maps onto
     the intersection of the images.  (Contributed by Paul Chapman,
     11-Apr-2009.) $)
  resin $p |- ( ( Fun `' F /\ ( F |` A ) : A -onto-> C /\
                               ( F |` B ) : B -onto-> D ) ->
      ( F |` ( A i^i B ) ) : ( A i^i B ) -1-1-onto-> ( C i^i D ) ) $=
    cF ccnv wfun cA cC cF cA cres wfo cB cD cF cB cres wfo w3a cA cA cB cdif
    cdif cC cC cD cdif cdif cF cA cA cB cdif cdif cres wf1o cA cB cin cC cD cin
    cF cA cB cin cres wf1o cF ccnv wfun cA cC cF cA cres wfo cB cD cF cB cres
    wfo cA cB cdif cC cD cdif cF cA cB cdif cres wfo cA cA cB cdif cdif cC cC
    cD cdif cdif cF cA cA cB cdif cdif cres wf1o cF ccnv wfun cA cC cF cA cres
    wfo cB cD cF cB cres wfo w3a cA cB cdif cC cD cdif cF cA cB cdif cres wf1o
    cA cB cdif cC cD cdif cF cA cB cdif cres wfo cA cB cC cD cF resdif cA cB
    cdif cC cD cdif cF cA cB cdif cres f1ofo syl cA cA cB cdif cC cC cD cdif cF
    resdif syld3an3 cA cB cin cC cD cin cF cA cB cin cres wf1o cA cB cin cC cC
    cD cdif cdif cF cA cB cin cres wf1o cA cA cB cdif cdif cC cC cD cdif cdif
    cF cA cB cin cres wf1o cA cA cB cdif cdif cC cC cD cdif cdif cF cA cA cB
    cdif cdif cres wf1o cC cD cin cC cC cD cdif cdif wceq cA cB cin cC cD cin
    cF cA cB cin cres wf1o cA cB cin cC cC cD cdif cdif cF cA cB cin cres wf1o
    wb cC cD dfin4 cC cD cin cC cC cD cdif cdif cA cB cin cF cA cB cin cres
    f1oeq3 ax-mp cA cB cin cA cA cB cdif cdif wceq cA cB cin cC cC cD cdif cdif
    cF cA cB cin cres wf1o cA cA cB cdif cdif cC cC cD cdif cdif cF cA cB cin
    cres wf1o wb cA cB dfin4 cA cB cin cA cA cB cdif cdif cC cC cD cdif cdif cF
    cA cB cin cres f1oeq2 ax-mp cF cA cB cin cres cF cA cA cB cdif cdif cres
    wceq cA cA cB cdif cdif cC cC cD cdif cdif cF cA cB cin cres wf1o cA cA cB
    cdif cdif cC cC cD cdif cdif cF cA cA cB cdif cdif cres wf1o wb cA cB cin
    cA cA cB cdif cdif cF cA cB dfin4 reseq2i cA cA cB cdif cdif cC cC cD cdif
    cdif cF cA cB cin cres cF cA cA cB cdif cdif cres f1oeq1 ax-mp 3bitrri
    sylib $.

  $( Composition of one-to-one onto functions.  (Contributed by NM,
     19-Mar-1998.) $)
  f1oco $p |- ( ( F : B -1-1-onto-> C /\ G : A -1-1-onto-> B ) ->
              ( F o. G ) : A -1-1-onto-> C ) $=
    cB cC cF wf1o cA cB cG wf1o wa cA cC cF cG ccom wf1 cA cC cF cG ccom wfo wa
    cA cC cF cG ccom wf1o cB cC cF wf1o cB cC cF wf1 cB cC cF wfo wa cA cB cG
    wf1 cA cB cG wfo wa cA cC cF cG ccom wf1 cA cC cF cG ccom wfo wa cA cB cG
    wf1o cB cC cF df-f1o cA cB cG df-f1o cB cC cF wf1 cA cB cG wf1 cB cC cF wfo
    cA cB cG wfo cA cC cF cG ccom wf1 cA cC cF cG ccom wfo wa cB cC cF wf1 cA
    cB cG wf1 wa cA cC cF cG ccom wf1 cB cC cF wfo cA cB cG wfo wa cA cC cF cG
    ccom wfo cA cB cC cF cG f1co cA cB cC cF cG foco anim12i an4s syl2anb cA cC
    cF cG ccom df-f1o sylibr $.

  $( The converse of an injective function is bijective.  (Contributed by FL,
     11-Nov-2011.) $)
  f1cnv $p |- ( F : A -1-1-> B -> `' F : ran F -1-1-onto-> A ) $=
    cA cB cF wf1 cA cF crn cF wf1o cF crn cA cF ccnv wf1o cA cB cF f1f1orn cA
    cF crn cF f1ocnv syl $.

  $( Composition with the converse.  (Contributed by Jeff Madsen,
     2-Sep-2009.) $)
  funcocnv2 $p |- ( Fun F -> ( F o. `' F ) = ( _I |` ran F ) ) $=
    cF wfun cF cF ccnv ccom cid wss cF cF ccnv ccom cid cF crn cres wceq cF
    wfun cF wrel cF cF ccnv ccom cid wss cF df-fun simprbi cF cF ccnv ccom cid
    wss cF cF ccnv ccom cid cF cF ccnv ccom cdm cres wceq cF wfun cF cF ccnv
    ccom cid cF crn cres wceq cF cF ccnv ccom iss cF wfun cid cF cF ccnv ccom
    cdm cres cid cF crn cres cF cF ccnv ccom cF wfun cF cF ccnv ccom cdm cF crn
    cid cF cF ccnv ccom cdm cF crn wceq cF wfun cF cF ccnv ccom cdm cF ccnv cdm
    cF crn cF cdm cF ccnv crn wceq cF cF ccnv ccom cdm cF ccnv cdm wceq cF
    dfdm4 cF cF ccnv dmcoeq ax-mp cF df-rn eqtr4i a1i reseq2d eqeq2d syl5bb
    mpbid $.

  $( The composition of an onto function and its converse.  (Contributed by
     Stefan O'Rear, 12-Feb-2015.) $)
  fococnv2 $p |- ( F : A -onto-> B -> ( F o. `' F ) = ( _I |` B ) ) $=
    cA cB cF wfo cF cF ccnv ccom cid cF crn cres cid cB cres cA cB cF wfo cF
    wfun cF cF ccnv ccom cid cF crn cres wceq cA cB cF fofun cF funcocnv2 syl
    cA cB cF wfo cF crn cB cid cA cB cF forn reseq2d eqtrd $.

  $( The composition of a one-to-one onto function and its converse equals the
     identity relation restricted to the function's range.  (Contributed by NM,
     13-Dec-2003.)  (Proof shortened by Stefan O'Rear, 12-Feb-2015.) $)
  f1ococnv2 $p |- ( F : A -1-1-onto-> B -> ( F o. `' F ) = ( _I |` B ) ) $=
    cA cB cF wf1o cA cB cF wfo cF cF ccnv ccom cid cB cres wceq cA cB cF f1ofo
    cA cB cF fococnv2 syl $.

  $( Composition of an injective function with its converse.  (Contributed by
     FL, 11-Nov-2011.) $)
  f1cocnv2 $p |- ( F : A -1-1-> B -> ( F o. `' F ) = ( _I |` ran F ) ) $=
    cA cB cF wf1 cF wfun cF cF ccnv ccom cid cF crn cres wceq cA cB cF f1fun cF
    funcocnv2 syl $.

  $( The composition of a one-to-one onto function's converse and itself equals
     the identity relation restricted to the function's domain.  (Contributed
     by NM, 13-Dec-2003.) $)
  f1ococnv1 $p |- ( F : A -1-1-onto-> B -> ( `' F o. F ) = ( _I |` A ) ) $=
    cA cB cF wf1o cF ccnv cF ccnv ccnv ccom cF ccnv cF ccom cid cA cres cA cB
    cF wf1o cF ccnv ccnv cF cF ccnv cA cB cF wf1o cF wrel cF ccnv ccnv cF wceq
    cA cB cF f1orel cF dfrel2 sylib coeq2d cA cB cF wf1o cB cA cF ccnv wf1o cF
    ccnv cF ccnv ccnv ccom cid cA cres wceq cA cB cF f1ocnv cB cA cF ccnv
    f1ococnv2 syl eqtr3d $.

  $( Composition of an injective function with its converse.  (Contributed by
     FL, 11-Nov-2011.) $)
  f1cocnv1 $p |- ( F : A -1-1-> B -> ( `' F o. F ) = ( _I |` A ) ) $=
    cA cB cF wf1 cA cF crn cF wf1o cF ccnv cF ccom cid cA cres wceq cA cB cF
    f1f1orn cA cF crn cF f1ococnv1 syl $.

  $( Re-express a constraint on a composition as a constraint on the
     composand.  (Contributed by Stefan O'Rear, 7-Mar-2015.) $)
  funcoeqres $p |- ( ( Fun G /\ ( F o. G ) = H ) ->
      ( F |` ran G ) = ( H o. `' G ) ) $=
    cG wfun cF cG ccom cH wceq cF cG crn cres cF cG ccom cG ccnv ccom cH cG
    ccnv ccom cG wfun cF cG cG ccnv ccom ccom cF cid cG crn cres ccom cF cG
    ccom cG ccnv ccom cF cG crn cres cG wfun cG cG ccnv ccom cid cG crn cres cF
    cG funcocnv2 coeq2d cF cG ccom cG ccnv ccom cF cG cG ccnv ccom ccom cF cG
    cG ccnv coass eqcomi cF cG crn coires1 3eqtr3g cF cG ccom cH cG ccnv coeq1
    sylan9req $.

  ${
    $d x F $.  $d x A $.  $d x B $.
    f11o.1 $e |- F e. _V $.
    $( Relationship between a mapping and an onto mapping.  Figure 38 of
       [Enderton] p. 145.  (Contributed by NM, 10-May-1998.) $)
    ffoss $p |- ( F : A --> B <-> E. x ( F : A -onto-> x /\ x C_ B ) ) $=
      cA cB cF wf cA vx cv cF wfo vx cv cB wss wa vx wex cA cB cF wf cA cF crn
      cF wfo cF crn cB wss wa cA vx cv cF wfo vx cv cB wss wa vx wex cA cB cF
      wf cF cA wfn cF crn cB wss wa cA cF crn cF wfo cF crn cB wss wa cA cB cF
      df-f cF cA wfn cA cF crn cF wfo cF crn cB wss cA cF dffn4 anbi1i bitri cA
      vx cv cF wfo vx cv cB wss wa cA cF crn cF wfo cF crn cB wss wa vx cF crn
      cF f11o.1 rnex vx cv cF crn wceq cA vx cv cF wfo cA cF crn cF wfo vx cv
      cB wss cF crn cB wss vx cv cF crn cA cF foeq3 vx cv cF crn cB sseq1
      anbi12d spcev sylbi cA vx cv cF wfo vx cv cB wss wa cA cB cF wf vx cA vx
      cv cF wfo cA vx cv cF wf vx cv cB wss cA cB cF wf cA vx cv cF fof cA vx
      cv cB cF fss sylan exlimiv impbii $.

    $( Relationship between one-to-one and one-to-one onto function.
       (Contributed by NM, 4-Apr-1998.) $)
    f11o $p |- ( F : A -1-1-> B <-> E. x ( F : A -1-1-onto-> x /\ x C_ B ) ) $=
      cA cB cF wf cF ccnv wfun wa cA vx cv cF wfo vx cv cB wss wa vx wex cF
      ccnv wfun wa cA cB cF wf1 cA vx cv cF wf1o vx cv cB wss wa vx wex cA cB
      cF wf cA vx cv cF wfo vx cv cB wss wa vx wex cF ccnv wfun vx cA cB cF
      f11o.1 ffoss anbi1i cA cB cF df-f1 cA vx cv cF wf1o vx cv cB wss wa vx
      wex cA vx cv cF wfo vx cv cB wss wa cF ccnv wfun wa vx wex cA vx cv cF
      wfo vx cv cB wss wa vx wex cF ccnv wfun wa cA vx cv cF wf1o vx cv cB wss
      wa cA vx cv cF wfo vx cv cB wss wa cF ccnv wfun wa vx cA vx cv cF wf1o vx
      cv cB wss wa cA vx cv cF wfo cF ccnv wfun wa vx cv cB wss wa cA vx cv cF
      wfo vx cv cB wss wa cF ccnv wfun wa cA vx cv cF wf1o cA vx cv cF wfo cF
      ccnv wfun wa vx cv cB wss cA vx cv cF dff1o3 anbi1i cA vx cv cF wfo cF
      ccnv wfun vx cv cB wss an32 bitri exbii cA vx cv cF wfo vx cv cB wss wa
      cF ccnv wfun vx 19.41v bitri 3bitr4i $.
  $}

  $( The empty set maps one-to-one into any class.  (Contributed by NM,
     7-Apr-1998.) $)
  f10 $p |- (/) : (/) -1-1-> A $=
    c0 cA c0 wf1 c0 cA c0 wf c0 ccnv wfun cA f0 c0 ccnv wfun c0 wfun fun0 c0
    ccnv c0 cnv0 funeqi mpbir c0 cA c0 df-f1 mpbir2an $.

  $( One-to-one onto mapping of the empty set.  (Contributed by NM,
     15-Apr-1998.) $)
  f1o00 $p |- ( F : (/) -1-1-onto-> A <-> ( F = (/) /\ A = (/) ) ) $=
    c0 cA cF wf1o cF c0 wfn cF ccnv cA wfn wa cF c0 wceq cA c0 wceq wa c0 cA cF
    dff1o4 cF c0 wfn cF ccnv cA wfn wa cF c0 wceq cA c0 wceq wa cF c0 wfn cF
    ccnv cA wfn wa cF c0 wceq cA c0 wceq cF c0 wfn cF c0 wceq cF ccnv cA wfn cF
    c0 wfn cF c0 wceq cF fn0 biimpi adantr cF c0 wfn cF ccnv cA wfn wa c0 c0
    cdm cA dm0 cF c0 wfn cF ccnv cA wfn wa c0 cA wfn c0 cdm cA wceq cF c0 wfn
    cF ccnv cA wfn c0 cA wfn cF c0 wfn cA cF ccnv c0 cF c0 wfn cF c0 wceq cF
    ccnv c0 wceq cF fn0 cF c0 wceq cF ccnv c0 ccnv c0 cF c0 cnveq cnv0 syl6eq
    sylbi fneq1d biimpa cA c0 fndm syl syl5reqr jca cF c0 wceq cA c0 wceq wa cF
    c0 wfn cF ccnv cA wfn cF c0 wceq cF c0 wfn cA c0 wceq cF c0 wfn cF c0 wceq
    cF fn0 biimpri adantr cF c0 wceq cA c0 wceq wa cF ccnv cA wfn c0 c0 wfn c0
    c0 wfn c0 c0 wceq c0 eqid c0 fn0 mpbir cF c0 wceq cF ccnv cA wfn c0 cA wfn
    cA c0 wceq c0 c0 wfn cF c0 wceq cA cF ccnv c0 cF c0 wceq cF ccnv c0 ccnv c0
    cF c0 cnveq cnv0 syl6eq fneq1d cA c0 c0 fneq2 sylan9bb mpbiri jca impbii
    bitri $.

  $( Onto mapping of the empty set.  (Contributed by NM, 22-Mar-2006.) $)
  fo00 $p |- ( F : (/) -onto-> A <-> ( F = (/) /\ A = (/) ) ) $=
    c0 cA cF wfo c0 cA cF wf1o cF c0 wceq cA c0 wceq wa c0 cA cF wfo c0 cA cF
    wf1o c0 cA cF wfo c0 cA cF wf1 c0 cA cF wfo wa c0 cA cF wf1o c0 cA cF wfo
    c0 cA cF wf1 c0 cA cF wfo cF c0 wfn c0 cA cF wf1 c0 cA cF fofn cF c0 wfn cF
    c0 wceq c0 cA cF wf1 cF fn0 cF c0 wceq c0 cA cF wf1 c0 cA c0 wf1 cA f10 c0
    cA cF c0 f1eq1 mpbiri sylbi syl ancri c0 cA cF df-f1o sylibr c0 cA cF f1ofo
    impbii cA cF f1o00 bitri $.

  $( One-to-one onto mapping of the empty set.  (Contributed by NM,
     10-Sep-2004.) $)
  f1o0 $p |- (/) : (/) -1-1-onto-> (/) $=
    c0 c0 c0 wf1o c0 c0 wceq c0 c0 wceq c0 eqid c0 eqid c0 c0 f1o00 mpbir2an $.

  $( A restriction of the identity relation is a one-to-one onto function.
     (Contributed by NM, 30-Apr-1998.)  (Proof shortened by Andrew Salmon,
     22-Oct-2011.) $)
  f1oi $p |- ( _I |` A ) : A -1-1-onto-> A $=
    cA cA cid cA cres wf1o cid cA cres cA wfn cid cA cres ccnv cA wfn cA fnresi
    cid cA cres ccnv cA wfn cid cA cres cA wfn cA fnresi cA cid cA cres ccnv
    cid cA cres cA cnvresid fneq1i mpbir cA cA cid cA cres dff1o4 mpbir2an $.

  $( The identity relation is a one-to-one onto function on the universe.
     (Contributed by NM, 16-May-2004.) $)
  f1ovi $p |- _I : _V -1-1-onto-> _V $=
    cvv cvv cid cvv cres wf1o cvv cvv cid wf1o cvv f1oi cid cvv cres cid wceq
    cvv cvv cid cvv cres wf1o cvv cvv cid wf1o wb cid wrel cid cvv cres cid
    wceq reli cid dfrel3 mpbi cvv cvv cid cvv cres cid f1oeq1 ax-mp mpbi $.

  ${
    f1osn.1 $e |- A e. _V $.
    f1osn.2 $e |- B e. _V $.
    $( A singleton of an ordered pair is one-to-one onto function.
       (Contributed by NM, 18-May-1998.)  (Proof shortened by Andrew Salmon,
       22-Oct-2011.) $)
    f1osn $p |- { <. A , B >. } : { A } -1-1-onto-> { B } $=
      cA csn cB csn cA cB cop csn wf1o cA cB cop csn cA csn wfn cA cB cop csn
      ccnv cB csn wfn cA cB f1osn.1 f1osn.2 fnsn cA cB cop csn ccnv cB csn wfn
      cB cA cop csn cB csn wfn cB cA f1osn.2 f1osn.1 fnsn cB csn cA cB cop csn
      ccnv cB cA cop csn cA cB f1osn.1 f1osn.2 cnvsn fneq1i mpbir cA csn cB csn
      cA cB cop csn dff1o4 mpbir2an $.
  $}

  ${
    $d A a b $.  $d B b $.
    $( A singleton of an ordered pair is one-to-one onto function.
       (Contributed by Mario Carneiro, 12-Jan-2013.) $)
    f1osng $p |- ( ( A e. V /\ B e. W ) ->
                   { <. A , B >. } : { A } -1-1-onto-> { B } ) $=
      va cv csn vb cv csn va cv vb cv cop csn wf1o cA csn vb cv csn cA vb cv
      cop csn wf1o cA csn cB csn cA cB cop csn wf1o va vb cA cB cV cW va cv cA
      wceq va cv csn vb cv csn va cv vb cv cop csn wf1o cA csn vb cv csn va cv
      vb cv cop csn wf1o cA csn vb cv csn cA vb cv cop csn wf1o va cv cA wceq
      va cv csn cA csn wceq va cv csn vb cv csn va cv vb cv cop csn wf1o cA csn
      vb cv csn va cv vb cv cop csn wf1o wb va cv cA sneq va cv csn cA csn vb
      cv csn va cv vb cv cop csn f1oeq2 syl va cv cA wceq va cv vb cv cop csn
      cA vb cv cop csn wceq cA csn vb cv csn va cv vb cv cop csn wf1o cA csn vb
      cv csn cA vb cv cop csn wf1o wb va cv cA wceq va cv vb cv cop cA vb cv
      cop va cv cA vb cv opeq1 sneqd cA csn vb cv csn va cv vb cv cop csn cA vb
      cv cop csn f1oeq1 syl bitrd vb cv cB wceq cA csn vb cv csn cA vb cv cop
      csn wf1o cA csn cB csn cA vb cv cop csn wf1o cA csn cB csn cA cB cop csn
      wf1o vb cv cB wceq vb cv csn cB csn wceq cA csn vb cv csn cA vb cv cop
      csn wf1o cA csn cB csn cA vb cv cop csn wf1o wb vb cv cB sneq vb cv csn
      cB csn cA csn cA vb cv cop csn f1oeq3 syl vb cv cB wceq cA vb cv cop csn
      cA cB cop csn wceq cA csn cB csn cA vb cv cop csn wf1o cA csn cB csn cA
      cB cop csn wf1o wb vb cv cB wceq cA vb cv cop cA cB cop vb cv cB cA opeq2
      sneqd cA csn cB csn cA vb cv cop csn cA cB cop csn f1oeq1 syl bitrd va cv
      vb cv va vex vb vex f1osn vtocl2g $.
  $}

  ${
    $d A a b $.  $d B b $.
    $( A two-element swap is a bijection on a pair.  (Contributed by Mario
       Carneiro, 23-Jan-2015.) $)
    f1oprswap $p |- ( ( A e. V /\ B e. W ) ->
      { <. A , B >. , <. B , A >. } : { A , B } -1-1-onto-> { A , B } ) $=
      cA cV wcel cB cW wcel wa cA cB cpr cA cB cpr cA cB cop cB cA cop cpr wf1o
      cA cB cA cV wcel cB cW wcel wa cA cB wceq wa cA csn cA csn cA cA cop csn
      wf1o cA cB cpr cA cB cpr cA cB cop cB cA cop cpr wf1o cA cV wcel cA csn
      cA csn cA cA cop csn wf1o cB cW wcel cA cB wceq cA cV wcel cA csn cA csn
      cA cA cop csn wf1o cA cA cV cV f1osng anidms ad2antrr cA cB wceq cA csn
      cA csn cA cA cop csn wf1o cA cB cpr cA cB cpr cA cB cop cB cA cop cpr
      wf1o wb cA cV wcel cB cW wcel wa cA cB wceq cA csn cA csn cA cA cop csn
      wf1o cA csn cA csn cA cB cop cB cA cop cpr wf1o cA cB cpr cA cB cpr cA cB
      cop cB cA cop cpr wf1o cA cB wceq cA cA cop csn cA cB cop cB cA cop cpr
      wceq cA csn cA csn cA cA cop csn wf1o cA csn cA csn cA cB cop cB cA cop
      cpr wf1o wb cA cB wceq cA cA cop csn cA cA cop cA cA cop cpr cA cB cop cB
      cA cop cpr cA cA cop dfsn2 cA cB wceq cA cA cop cA cB cop cA cA cop cB cA
      cop cA cB cA opeq2 cA cB cA opeq1 preq12d syl5eq cA csn cA csn cA cA cop
      csn cA cB cop cB cA cop cpr f1oeq1 syl cA cB wceq cA csn cA cB cpr wceq
      cA csn cA csn cA cB cop cB cA cop cpr wf1o cA cB cpr cA cB cpr cA cB cop
      cB cA cop cpr wf1o wb cA cB wceq cA csn cA cA cpr cA cB cpr cA dfsn2 cA
      cB cA preq2 syl5eq cA csn cA cB cpr wceq cA csn cA csn cA cB cop cB cA
      cop cpr wf1o cA cB cpr cA csn cA cB cop cB cA cop cpr wf1o cA cB cpr cA
      cB cpr cA cB cop cB cA cop cpr wf1o cA csn cA cB cpr cA csn cA cB cop cB
      cA cop cpr f1oeq2 cA csn cA cB cpr cA cB cpr cA cB cop cB cA cop cpr
      f1oeq3 bitrd syl bitrd adantl mpbid cA cV wcel cB cW wcel wa cA cB wne wa
      cA cB cop cB cA cop cpr cA cB cpr wfn cA cB cop cB cA cop cpr ccnv cA cB
      cpr wfn cA cB cpr cA cB cpr cA cB cop cB cA cop cpr wf1o cA cV wcel cB cW
      wcel wa cA cB wne wa cA cV wcel cB cW wcel cB cW wcel cA cV wcel cA cB
      wne cA cB cop cB cA cop cpr cA cB cpr wfn cA cV wcel cB cW wcel cA cB wne
      simpll cA cV wcel cB cW wcel cA cB wne simplr cA cV wcel cB cW wcel cA cB
      wne simplr cA cV wcel cB cW wcel cA cB wne simpll cA cV wcel cB cW wcel
      wa cA cB wne simpr cA cB cB cA cV cW cW cV fnprg syl221anc cA cV wcel cB
      cW wcel wa cA cB wne wa cA cB cop cB cA cop cpr ccnv cA cB cpr wfn cA cB
      cop cB cA cop cpr cA cB cpr wfn cA cV wcel cB cW wcel wa cA cB wne wa cA
      cV wcel cB cW wcel cB cW wcel cA cV wcel cA cB wne cA cB cop cB cA cop
      cpr cA cB cpr wfn cA cV wcel cB cW wcel cA cB wne simpll cA cV wcel cB cW
      wcel cA cB wne simplr cA cV wcel cB cW wcel cA cB wne simplr cA cV wcel
      cB cW wcel cA cB wne simpll cA cV wcel cB cW wcel wa cA cB wne simpr cA
      cB cB cA cV cW cW cV fnprg syl221anc cA cV wcel cB cW wcel wa cA cB wne
      wa cA cB cpr cA cB cop cB cA cop cpr ccnv cA cB cop cB cA cop cpr cA cV
      wcel cB cW wcel wa cA cB wne wa cA cB cop csn ccnv cB cA cop csn ccnv cun
      cA cB cop csn cB cA cop csn cun cA cB cop cB cA cop cpr ccnv cA cB cop cB
      cA cop cpr cA cV wcel cB cW wcel wa cA cB cop csn ccnv cB cA cop csn ccnv
      cun cA cB cop csn cB cA cop csn cun wceq cA cB wne cA cV wcel cB cW wcel
      wa cA cB cop csn ccnv cB cA cop csn ccnv cun cB cA cop csn cA cB cop csn
      cun cA cB cop csn cB cA cop csn cun cA cV wcel cB cW wcel wa cA cB cop
      csn ccnv cB cA cop csn cB cA cop csn ccnv cA cB cop csn cA cB cV cW
      cnvsng cB cW wcel cA cV wcel cB cA cop csn ccnv cA cB cop csn wceq cB cA
      cW cV cnvsng ancoms uneq12d cB cA cop csn cA cB cop csn uncom syl6eq
      adantr cA cB cop cB cA cop cpr ccnv cA cB cop csn cB cA cop csn cun ccnv
      cA cB cop csn ccnv cB cA cop csn ccnv cun cA cB cop cB cA cop cpr cA cB
      cop csn cB cA cop csn cun cA cB cop cB cA cop df-pr cnveqi cA cB cop csn
      cB cA cop csn cnvun eqtri cA cB cop cB cA cop df-pr 3eqtr4g fneq1d mpbird
      cA cB cpr cA cB cpr cA cB cop cB cA cop cpr dff1o4 sylanbrc pm2.61dane $.
  $}

  ${
    $d x F $.  $d x A $.
    $( Function value when ` F ` is not a function.  Theorem 6.12(2) of
       [TakeutiZaring] p. 27.  (Contributed by NM, 30-Apr-2004.)  (Proof
       shortened by Mario Carneiro, 31-Aug-2015.) $)
    tz6.12-2 $p |- ( -. E! x A F x -> ( F ` A ) = (/) ) $=
      cA vx cv cF wbr vx weu wn cA cF cfv cA vx cv cF wbr vx cio c0 vx cA cF
      df-fv cA vx cv cF wbr vx iotanul syl5eq $.

    $( The value of a function at a unique point.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)
    fveu $p |- ( E! x A F x -> ( F ` A ) = U. { x | A F x } ) $=
      cA vx cv cF wbr vx weu cA cF cfv cA vx cv cF wbr vx cio cA vx cv cF wbr
      vx cab cuni vx cA cF df-fv cA vx cv cF wbr vx iotauni syl5eq $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( If ` A ` is a proper class, then there is no unique binary relationship
       with ` A ` as the first element.  (Contributed by Scott Fenton,
       7-Oct-2017.) $)
    brprcneu $p |- ( -. A e. _V -> -. E! x A F x ) $=
      cA cvv wcel wn cA vx cv cF wbr vx wex cA vx cv cF wbr vx wmo wn wi cA vx
      cv cF wbr vx weu wn cA cvv wcel wn cA vx cv cF wbr vx wex cA vx cv cF wbr
      cA vy cv cF wbr wa vx vy weq wn wa vy wex vx wex cA vx cv cF wbr vx wmo
      wn cA cvv wcel wn cA vx cv cF wbr cA vx cv cF wbr cA vy cv cF wbr wa vx
      vy weq wn wa vy wex vx cA cvv wcel wn cA vx cv cop cF wcel cA vx cv cop
      cF wcel cA vy cv cop cF wcel wa vx vy weq wn wa vy wex cA vx cv cF wbr cA
      vx cv cF wbr cA vy cv cF wbr wa vx vy weq wn wa vy wex cA cvv wcel wn cA
      vx cv cop cF wcel cA vx cv cop cF wcel cA vy cv cop cF wcel wa vx vy weq
      wn wa vy wex wi c0 cF wcel c0 cF wcel vx vy weq wn wa vy wex wi c0 cF
      wcel c0 cF wcel vx vy weq wn vy wex wa c0 cF wcel vx vy weq wn wa vy wex
      c0 cF wcel vx vy weq wn vy wex vx vy weq wn vy wex vy vx weq vy wal wn vy
      vx dtru vx vy weq wn vy wex vx vy weq vy wal vy vx weq vy wal vx vy weq
      vy exnal vx vy weq vy vx weq vy vx vy equcom albii xchbinx mpbir jctr c0
      cF wcel vx vy weq wn vy 19.42v sylibr cA cvv wcel wn cA vx cv cop cF wcel
      c0 cF wcel cA vx cv cop cF wcel cA vy cv cop cF wcel wa vx vy weq wn wa
      vy wex c0 cF wcel vx vy weq wn wa vy wex cA cvv wcel wn cA vx cv cop c0
      cF cA vx cv opprc1 eleq1d cA cvv wcel wn cA vx cv cop cF wcel cA vy cv
      cop cF wcel wa vx vy weq wn wa c0 cF wcel vx vy weq wn wa vy cA cvv wcel
      wn cA vx cv cop cF wcel cA vy cv cop cF wcel wa c0 cF wcel vx vy weq wn
      cA cvv wcel wn cA vx cv cop cF wcel cA vy cv cop cF wcel wa c0 cF wcel c0
      cF wcel wa c0 cF wcel cA cvv wcel wn cA vx cv cop cF wcel c0 cF wcel cA
      vy cv cop cF wcel c0 cF wcel cA cvv wcel wn cA vx cv cop c0 cF cA vx cv
      opprc1 eleq1d cA cvv wcel wn cA vy cv cop c0 cF cA vy cv opprc1 eleq1d
      anbi12d c0 cF wcel anidm syl6bb anbi1d exbidv imbi12d mpbiri cA vx cv cF
      df-br cA vx cv cF wbr cA vy cv cF wbr wa vx vy weq wn wa cA vx cv cop cF
      wcel cA vy cv cop cF wcel wa vx vy weq wn wa vy cA vx cv cF wbr cA vy cv
      cF wbr wa cA vx cv cop cF wcel cA vy cv cop cF wcel wa vx vy weq wn cA vx
      cv cF wbr cA vx cv cop cF wcel cA vy cv cF wbr cA vy cv cop cF wcel cA vx
      cv cF df-br cA vy cv cF df-br anbi12i anbi1i exbii 3imtr4g eximdv cA vx
      cv cF wbr vx wmo wn cA vx cv cF wbr cA vy cv cF wbr wa vx vy weq wi vy
      wal vx wal wn cA vx cv cF wbr cA vy cv cF wbr wa vx vy weq wn wa vy wex
      vx wex cA vx cv cF wbr vx wmo cA vx cv cF wbr cA vy cv cF wbr wa vx vy
      weq wi vy wal vx wal cA vx cv cF wbr cA vy cv cF wbr vx vy vx cv vy cv cA
      cF breq2 mo4 notbii cA vx cv cF wbr cA vy cv cF wbr wa vx vy weq wn wa vy
      wex vx wex cA vx cv cF wbr cA vy cv cF wbr wa vx vy weq wi vy wal wn vx
      wex cA vx cv cF wbr cA vy cv cF wbr wa vx vy weq wi vy wal vx wal wn cA
      vx cv cF wbr cA vy cv cF wbr wa vx vy weq wn wa vy wex cA vx cv cF wbr cA
      vy cv cF wbr wa vx vy weq wi vy wal wn vx cA vx cv cF wbr cA vy cv cF wbr
      wa vx vy weq vy exanali exbii cA vx cv cF wbr cA vy cv cF wbr wa vx vy
      weq wi vy wal vx exnal bitri bitr4i syl6ibr cA vx cv cF wbr vx weu wn cA
      vx cv cF wbr vx wex cA vx cv cF wbr vx wmo wa wn cA vx cv cF wbr vx wex
      cA vx cv cF wbr vx wmo wn wi cA vx cv cF wbr vx weu cA vx cv cF wbr vx
      wex cA vx cv cF wbr vx wmo wa cA vx cv cF wbr vx eu5 notbii cA vx cv cF
      wbr vx wex cA vx cv cF wbr vx wmo imnan bitr4i sylibr $.
  $}


  ${
    $d x y A $.  $d x y F $.
    $( A function's value at a proper class is the empty set.  (Contributed by
       NM, 20-May-1998.) $)
    fvprc $p |- ( -. A e. _V -> ( F ` A ) = (/) ) $=
      cA cvv wcel wn cA vx cv cF wbr vx weu wn cA cF cfv c0 wceq vx cA cF
      brprcneu vx cA cF tz6.12-2 syl $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( Alternate definition of function value.  Definition 10.11 of [Quine]
       p. 68.  (Contributed by NM, 30-Apr-2004.)  (Proof shortened by Andrew
       Salmon, 17-Sep-2011.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    fv2 $p |- ( F ` A ) = U. { x | A. y ( A F y <-> y = x ) } $=
      cA cF cfv cA vy cv cF wbr vy cio cA vy cv cF wbr vy vx weq wb vy wal vx
      cab cuni vy cA cF df-fv cA vy cv cF wbr vy vx dfiota2 eqtri $.
  $}

  ${
    $d F x y $.  $d A x y $.
    $( A definition of function value in terms of iota.  (Contributed by Scott
       Fenton, 19-Feb-2013.) $)
    dffv3 $p |- ( F ` A ) = ( iota x x e. ( F " { A } ) ) $=
      cA cvv wcel cA cF cfv vx cv cF cA csn cima wcel vx cio wceq cA cvv wcel
      vx cv cF cA csn cima wcel vx cio cA vx cv cF wbr vx cio cA cF cfv cA cvv
      wcel vx cv cF cA csn cima wcel cA vx cv cF wbr vx cA cvv wcel vx cv cvv
      wcel vx cv cF cA csn cima wcel cA vx cv cF wbr wb vx vex cA cvv wcel vx
      cv cvv wcel wa vx cv cF cA csn cima wcel cA vx cv cop cF wcel cA vx cv cF
      wbr cF cA vx cv cvv cvv elimasng cA vx cv cF df-br syl6bbr mpan2 iotabidv
      vx cA cF df-fv syl6reqr cA cvv wcel wn cA cF cfv c0 vx cv cF cA csn cima
      wcel vx cio cA cF fvprc cA cvv wcel wn vx cv cF cA csn cima wcel vx cio
      vx cv c0 wcel vx cio c0 cA cvv wcel wn vx cv cF cA csn cima wcel vx cv c0
      wcel vx cA cvv wcel wn cF cA csn cima c0 vx cv cA cvv wcel wn cF cA csn
      cima cF c0 cima c0 cA cvv wcel wn cA csn c0 cF cA cvv wcel wn cA csn c0
      wceq cA snprc biimpi imaeq2d cF ima0 syl6eq eleq2d iotabidv vx cv c0 wcel
      vx weu wn vx cv c0 wcel vx cio c0 wceq vx cv c0 wcel vx weu vx cv c0 wcel
      vx wex vx cv c0 wcel vx vx cv noel nex vx cv c0 wcel vx euex mto vx cv c0
      wcel vx iotanul ax-mp syl6eq eqtr4d pm2.61i $.
  $}


  ${
    $d x y A $.  $d x y F $.
    $( The previous definition of function value, from before the ` iota `
       operator was introduced.  Although based on the idea embodied by
       Definition 10.2 of [Quine] p. 65 (see ~ args ), this definition
       apparently does not appear in the literature.  (Contributed by NM,
       1-Aug-1994.) $)
    dffv4 $p |- ( F ` A ) = U. { x | ( F " { A } ) = { x } } $=
      cA cF cfv vy cv cF cA csn cima wcel vy cio vy cv cF cA csn cima wcel vy
      cab vx cv csn wceq vx cab cuni cF cA csn cima vx cv csn wceq vx cab cuni
      vy cA cF dffv3 vy cv cF cA csn cima wcel vy vx df-iota vy cv cF cA csn
      cima wcel vy cab vx cv csn wceq vx cab cF cA csn cima vx cv csn wceq vx
      cab vy cv cF cA csn cima wcel vy cab vx cv csn wceq cF cA csn cima vx cv
      csn wceq vx vy cv cF cA csn cima wcel vy cab cF cA csn cima vx cv csn vy
      cF cA csn cima abid2 eqeq1i abbii unieqi 3eqtri $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x y F $.
    $( Membership in a function value.  (Contributed by NM, 30-Apr-2004.) $)
    elfv $p |- ( A e. ( F ` B ) <->
               E. x ( A e. x /\ A. y ( B F y <-> y = x ) ) ) $=
      cA cB cF cfv wcel cA cB vy cv cF wbr vy cv vx cv wceq wb vy wal vx cab
      cuni wcel cA vx cv wcel cB vy cv cF wbr vy cv vx cv wceq wb vy wal wa vx
      wex cB cF cfv cB vy cv cF wbr vy cv vx cv wceq wb vy wal vx cab cuni cA
      vx vy cB cF fv2 eleq2i cB vy cv cF wbr vy cv vx cv wceq wb vy wal vx cA
      eluniab bitri $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.  $d x G $.
    $( Equality theorem for function value.  (Contributed by NM,
       29-Dec-1996.) $)
    fveq1 $p |- ( F = G -> ( F ` A ) = ( G ` A ) ) $=
      cF cG wceq cA vx cv cF wbr vx cio cA vx cv cG wbr vx cio cA cF cfv cA cG
      cfv cF cG wceq cA vx cv cF wbr cA vx cv cG wbr vx cA vx cv cF cG breq
      iotabidv vx cA cF df-fv vx cA cG df-fv 3eqtr4g $.

    $( Equality theorem for function value.  (Contributed by NM,
       29-Dec-1996.) $)
    fveq2 $p |- ( A = B -> ( F ` A ) = ( F ` B ) ) $=
      cA cB wceq cA vx cv cF wbr vx cio cB vx cv cF wbr vx cio cA cF cfv cB cF
      cfv cA cB wceq cA vx cv cF wbr cB vx cv cF wbr vx cA cB vx cv cF breq1
      iotabidv vx cA cF df-fv vx cB cF df-fv 3eqtr4g $.
  $}

  ${
    fveq1i.1 $e |- F = G $.
    $( Equality inference for function value.  (Contributed by NM,
       2-Sep-2003.) $)
    fveq1i $p |- ( F ` A ) = ( G ` A ) $=
      cF cG wceq cA cF cfv cA cG cfv wceq fveq1i.1 cA cF cG fveq1 ax-mp $.
  $}

  ${
    fveq1d.1 $e |- ( ph -> F = G ) $.
    $( Equality deduction for function value.  (Contributed by NM,
       2-Sep-2003.) $)
    fveq1d $p |- ( ph -> ( F ` A ) = ( G ` A ) ) $=
      wph cF cG wceq cA cF cfv cA cG cfv wceq fveq1d.1 cA cF cG fveq1 syl $.
  $}

  ${
    fveq2i.1 $e |- A = B $.
    $( Equality inference for function value.  (Contributed by NM,
       28-Jul-1999.) $)
    fveq2i $p |- ( F ` A ) = ( F ` B ) $=
      cA cB wceq cA cF cfv cB cF cfv wceq fveq2i.1 cA cB cF fveq2 ax-mp $.
  $}

  ${
    fveq2d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for function value.  (Contributed by NM,
       29-May-1999.) $)
    fveq2d $p |- ( ph -> ( F ` A ) = ( F ` B ) ) $=
      wph cA cB wceq cA cF cfv cB cF cfv wceq fveq2d.1 cA cB cF fveq2 syl $.
  $}

  ${
    fveq12i.1 $e |- F = G $.
    fveq12i.2 $e |- A = B $.
    $( Equality deduction for function value.  (Contributed by FL,
       27-Jun-2014.) $)
    fveq12i $p |- ( F ` A ) = ( G ` B ) $=
      cA cF cfv cA cG cfv cB cG cfv cA cF cG fveq12i.1 fveq1i cA cB cG
      fveq12i.2 fveq2i eqtri $.
  $}

  ${
    fveq12d.1 $e |- ( ph -> F = G ) $.
    fveq12d.2 $e |- ( ph -> A = B ) $.
    $( Equality deduction for function value.  (Contributed by FL,
       22-Dec-2008.) $)
    fveq12d $p |- ( ph -> ( F ` A ) = ( G ` B ) ) $=
      wph cA cF cfv cA cG cfv cB cG cfv wph cA cF cG fveq12d.1 fveq1d wph cA cB
      cG fveq12d.2 fveq2d eqtrd $.
  $}

  ${
    $d y z F $.  $d y z A $.  $d x y z $.
    nffv.1 $e |- F/_ x F $.
    nffv.2 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for function value.  (Contributed by
       NM, 14-Nov-1995.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nffv $p |- F/_ x ( F ` A ) $=
      vx cA cF cfv cA vy cv cF wbr vy cio vy cA cF df-fv cA vy cv cF wbr vx vy
      vx cA vy cv cF nffv.2 nffv.1 vx vy cv nfcv nfbr nfiota nfcxfr $.
  $}

  ${
    $d x C $.
    $( Bound-variable hypothesis builder for mapping, special case.
       (Contributed by Mario Carneiro, 25-Dec-2016.) $)
    nffvmpt1 $p |- F/_ x ( ( x e. A |-> B ) ` C ) $=
      vx cC vx cA cB cmpt vx cA cB nfmpt1 vx cC nfcv nffv $.
  $}

  ${
    $d y z A $.  $d y z F $.  $d y ph $.  $d x y z $.
    nffvd.2 $e |- ( ph -> F/_ x F ) $.
    nffvd.3 $e |- ( ph -> F/_ x A ) $.
    $( Deduction version of bound-variable hypothesis builder ~ nffv .
       (Contributed by NM, 10-Nov-2005.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
    nffvd $p |- ( ph -> F/_ x ( F ` A ) ) $=
      wph vx vz cv cA wcel vx wal vz cab vz cv cF wcel vx wal vz cab cfv wnfc
      vx cA cF cfv wnfc vx vz cv cA wcel vx wal vz cab vz cv cF wcel vx wal vz
      cab vz cv cF wcel vx vz nfaba1 vz cv cA wcel vx vz nfaba1 nffv wph vx cF
      wnfc vx cA wnfc vx vz cv cA wcel vx wal vz cab vz cv cF wcel vx wal vz
      cab cfv wnfc vx cA cF cfv wnfc wb nffvd.2 nffvd.3 vx cF wnfc vx cA wnfc
      wa vx vz cv cA wcel vx wal vz cab vz cv cF wcel vx wal vz cab cfv cA cF
      cfv vx cF wnfc vx cA wnfc vx vx cF nfnfc1 vx cA nfnfc1 nfan vx cF wnfc vx
      cA wnfc wa vz cv cA wcel vx wal vz cab cA vz cv cF wcel vx wal vz cab cF
      vx cF wnfc vz cv cF wcel vx wal vz cab cF wceq vx cA wnfc vx vz cF abidnf
      adantr vx cA wnfc vz cv cA wcel vx wal vz cab cA wceq vx cF wnfc vx vz cA
      abidnf adantl fveq12d nfceqdf syl2anc mpbii $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z C $.  $d y z F $.  $d x y z $.
    $( Move class substitution in and out of a function value.  (Contributed by
       NM, 11-Nov-2005.) $)
    csbfv12g $p |- ( A e. C ->
                 [_ A / x ]_ ( F ` B ) = ( [_ A / x ]_ F ` [_ A / x ]_ B ) ) $=
      cA cC wcel vx cA cB vy cv cF wbr vy cio csb vx cA cB csb vy cv vx cA cF
      csb wbr vy cio vx cA cB cF cfv csb vx cA cB csb vx cA cF csb cfv cA cC
      wcel vx cA cB vy cv cF wbr vy cio csb cB vy cv cF wbr vx cA wsbc vy cio
      vx cA cB csb vy cv vx cA cF csb wbr vy cio cB vy cv cF wbr vx vy cA cC
      csbiotag cA cC wcel cB vy cv cF wbr vx cA wsbc vx cA cB csb vy cv vx cA
      cF csb wbr vy cA cC wcel cB vy cv cF wbr vx cA wsbc vx cA cB csb vx cA vy
      cv csb vx cA cF csb wbr vx cA cB csb vy cv vx cA cF csb wbr vx cA cB vy
      cv cC cF sbcbrg cA cC wcel vx cA vy cv csb vy cv vx cA cB csb vx cA cF
      csb vx cA vy cv cC csbconstg breq2d bitrd iotabidv eqtrd vx cA cB cF cfv
      cB vy cv cF wbr vy cio vy cB cF df-fv csbeq2i vy vx cA cB csb vx cA cF
      csb df-fv 3eqtr4g $.
  $}

  ${
    $d A y $.  $d F y $.  $d B y $.  $d C y $.  $d x y $.
    $( Move class substitution in and out of a function value.(This is
       ~ csbfv12g with a shortened proof, shortened by Alan Sare,
       10-Nov-2012.)  The proof is derived from the virtual deduction proof
       ~ csbfv12gALTVD .  Although the proof is shorter, the total number of
       steps of all theorems used in the proof is probably longer.
       (Contributed by NM, 10-Nov-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    csbfv12gALT $p |- ( A e. C -> [_ A / x ]_ ( F ` B ) =
                ( [_ A / x ]_ F ` [_ A / x ]_ B ) ) $=
      cA cC wcel vx cA cF cB csn cima vy cv csn wceq vy cab cuni csb vx cA cF
      csb vx cA cB csb csn cima vy cv csn wceq vy cab cuni vx cA cB cF cfv csb
      vx cA cB csb vx cA cF csb cfv cA cC wcel vx cA cF cB csn cima vy cv csn
      wceq vy cab cuni csb vx cA cF cB csn cima vy cv csn wceq vy cab csb cuni
      vx cA cF csb vx cA cB csb csn cima vy cv csn wceq vy cab cuni vx cA cF cB
      csn cima vy cv csn wceq vy cab cC csbunig cA cC wcel vx cA cF cB csn cima
      vy cv csn wceq vy cab csb vx cA cF csb vx cA cB csb csn cima vy cv csn
      wceq vy cab cA cC wcel vx cA cF cB csn cima vy cv csn wceq vy cab csb cF
      cB csn cima vy cv csn wceq vx cA wsbc vy cab vx cA cF csb vx cA cB csb
      csn cima vy cv csn wceq vy cab cF cB csn cima vy cv csn wceq vx vy cA cC
      csbabg cA cC wcel cF cB csn cima vy cv csn wceq vx cA wsbc vx cA cF csb
      vx cA cB csb csn cima vy cv csn wceq vy cA cC wcel cF cB csn cima vy cv
      csn wceq vx cA wsbc vx cA cF cB csn cima csb vx cA vy cv csn csb wceq vx
      cA cF csb vx cA cB csb csn cima vy cv csn wceq vx cA cF cB csn cima vy cv
      csn cC sbceqg cA cC wcel vx cA cF cB csn cima csb vx cA cF csb vx cA cB
      csb csn cima vx cA vy cv csn csb vy cv csn cA cC wcel vx cA cF cB csn
      cima csb vx cA cF csb vx cA cB csn csb cima vx cA cF csb vx cA cB csb csn
      cima vx cA cB csn cC cF csbima12g cA cC wcel vx cA cB csn csb vx cA cB
      csb csn vx cA cF csb vx cA cB cC csbsng imaeq2d eqtrd vx cA vy cv csn cC
      csbconstg eqeq12d bitrd abbidv eqtrd unieqd eqtrd vx cA cB cF cfv cF cB
      csn cima vy cv csn wceq vy cab cuni vy cB cF dffv4 csbeq2i vy vx cA cB
      csb vx cA cF csb dffv4 3eqtr4g $.
  $}

  ${
    $d y A $.  $d y C $.  $d x y F $.
    $( Move class substitution in and out of a function value.  (Contributed by
       NM, 10-Nov-2005.) $)
    csbfv2g $p |- ( A e. C -> [_ A / x ]_ ( F ` B ) =
                  ( F ` [_ A / x ]_ B ) ) $=
      cA cC wcel vx cA cB cF cfv csb vx cA cB csb vx cA cF csb cfv vx cA cB csb
      cF cfv vx cA cB cC cF csbfv12g cA cC wcel vx cA cB csb vx cA cF csb cF vx
      cA cF cC csbconstg fveq1d eqtrd $.

    $( Substitution for a function value.  (Contributed by NM, 1-Jan-2006.) $)
    csbfvg $p |- ( A e. C -> [_ A / x ]_ ( F ` x ) = ( F ` A ) ) $=
      cA cC wcel vx cA vx cv cF cfv csb vx cA vx cv csb cF cfv cA cF cfv vx cA
      vx cv cC cF csbfv2g cA cC wcel vx cA vx cv csb cA cF vx cA cC csbvarg
      fveq2d eqtrd $.
  $}

  ${
    $d x A $.  $d x F $.
    $( The value of a class exists.  Corollary 6.13 of [TakeutiZaring] p. 27.
       (Contributed by NM, 30-Dec-1996.) $)
    fvex $p |- ( F ` A ) e. _V $=
      cA cF cfv cA vx cv cF wbr vx cio cvv vx cA cF df-fv cA vx cv cF wbr vx
      iotaex eqeltri $.
  $}

  $( Move a conditional outside of a function.  (Contributed by Jeff Madsen,
     2-Sep-2009.) $)
  fvif $p |- ( F ` if ( ph , A , B ) ) = if ( ph , ( F ` A ) , ( F ` B ) ) $=
    wph cA cB wph cA cB cif cF cfv cA cF cfv cB cF cfv wph cA cB cif cA cF
    fveq2 wph cA cB cif cB cF fveq2 ifsb $.

  ${
    $d x y z F $.  $d x y z A $.
    $( Alternate definition of the value of a function.  Definition 6.11 of
       [TakeutiZaring] p. 26.  (Contributed by NM, 30-Apr-2004.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
    fv3 $p |- ( F ` A ) = { x | ( E. y ( x e. y /\ A F y ) /\
              E! y A F y ) } $=
      vx cv vy cv wcel cA vy cv cF wbr wa vy wex cA vy cv cF wbr vy weu wa vx
      cA cF cfv vx cv cA cF cfv wcel vx cv vz cv wcel cA vy cv cF wbr vy cv vz
      cv wceq wb vy wal wa vz wex vx cv vy cv wcel cA vy cv cF wbr wa vy wex cA
      vy cv cF wbr vy weu wa vz vy vx cv cA cF elfv vx cv vz cv wcel cA vy cv
      cF wbr vy cv vz cv wceq wb vy wal wa vz wex vx cv vy cv wcel cA vy cv cF
      wbr wa vy wex cA vy cv cF wbr vy weu wa vx cv vz cv wcel cA vy cv cF wbr
      vy cv vz cv wceq wb vy wal wa vz wex vx cv vy cv wcel cA vy cv cF wbr wa
      vy wex cA vy cv cF wbr vy weu vx cv vz cv wcel cA vy cv cF wbr vy cv vz
      cv wceq wb vy wal wa vz wex vx cv vz cv wcel cA vz cv cF wbr wa vz wex vx
      cv vy cv wcel cA vy cv cF wbr wa vy wex vx cv vz cv wcel cA vy cv cF wbr
      vy cv vz cv wceq wb vy wal wa vx cv vz cv wcel cA vz cv cF wbr wa vz cA
      vy cv cF wbr vy cv vz cv wceq wb vy wal cA vz cv cF wbr vx cv vz cv wcel
      cA vy cv cF wbr vy cv vz cv wceq wb vy wal vy cv vz cv wceq cA vy cv cF
      wbr wi vy wal cA vz cv cF wbr cA vy cv cF wbr vy cv vz cv wceq wb vy cv
      vz cv wceq cA vy cv cF wbr wi vy cA vy cv cF wbr vy cv vz cv wceq bi2
      alimi cA vy cv cF wbr cA vz cv cF wbr vy vz cv vz vex vy cv vz cv cA cF
      breq2 ceqsalv sylib anim2i eximi vx cv vz cv wcel cA vz cv cF wbr wa vx
      cv vy cv wcel cA vy cv cF wbr wa vz vy vz cv vy cv wceq vx cv vz cv wcel
      vx cv vy cv wcel cA vz cv cF wbr cA vy cv cF wbr vz vy vx elequ2 vz cv vy
      cv cA cF breq2 anbi12d cbvexv sylib vx cv vz cv wcel cA vy cv cF wbr vy
      cv vz cv wceq wb vy wal wa vz wex cA vy cv cF wbr vy cv vz cv wceq wb vy
      wal vz wex cA vy cv cF wbr vy weu vx cv vz cv wcel cA vy cv cF wbr vy cv
      vz cv wceq wb vy wal wa vz wex vx cv vz cv wcel vz wex cA vy cv cF wbr vy
      cv vz cv wceq wb vy wal vz wex vx cv vz cv wcel cA vy cv cF wbr vy cv vz
      cv wceq wb vy wal vz 19.40 simprd cA vy cv cF wbr vy vz df-eu sylibr jca
      vx cv vy cv wcel cA vy cv cF wbr wa vy wex cA vy cv cF wbr vy weu vx cv
      vz cv wcel cA vy cv cF wbr vy cv vz cv wceq wb vy wal wa vz wex vx cv vy
      cv wcel cA vy cv cF wbr wa cA vy cv cF wbr vy weu vx cv vz cv wcel cA vy
      cv cF wbr vy cv vz cv wceq wb vy wal wa vz wex wi vy cA vy cv cF wbr vy
      weu vx cv vz cv wcel cA vy cv cF wbr vy cv vz cv wceq wb vy wal wa vz wex
      vy cA vy cv cF wbr vy nfeu1 vx cv vz cv wcel cA vy cv cF wbr vy cv vz cv
      wceq wb vy wal wa vy vz vx cv vz cv wcel cA vy cv cF wbr vy cv vz cv wceq
      wb vy wal vy vx cv vz cv wcel vy nfv cA vy cv cF wbr vy cv vz cv wceq wb
      vy nfa1 nfan nfex nfim cA vy cv cF wbr vy weu cA vy cv cF wbr vy cv vz cv
      wceq wb vy wal vz wex vx cv vy cv wcel cA vy cv cF wbr wa vx cv vz cv
      wcel cA vy cv cF wbr vy cv vz cv wceq wb vy wal wa vz wex cA vy cv cF wbr
      vy vz df-eu vx cv vy cv wcel cA vy cv cF wbr wa cA vy cv cF wbr vy cv vz
      cv wceq wb vy wal vx cv vz cv wcel cA vy cv cF wbr vy cv vz cv wceq wb vy
      wal wa vz cA vy cv cF wbr vy cv vz cv wceq wb vy wal vx cv vy cv wcel cA
      vy cv cF wbr wa vx cv vz cv wcel cA vy cv cF wbr vy cv vz cv wceq wb vy
      wal wa cA vy cv cF wbr vy cv vz cv wceq wb vy wal vx cv vy cv wcel cA vy
      cv cF wbr wa vx cv vz cv wcel cA vy cv cF wbr vy cv vz cv wceq wb vx cv
      vy cv wcel cA vy cv cF wbr wa vx cv vz cv wcel wi vy cA vy cv cF wbr vy
      cv vz cv wceq wb vx cv vy cv wcel cA vy cv cF wbr vx cv vz cv wcel cA vy
      cv cF wbr vy cv vz cv wceq wb cA vy cv cF wbr vx cv vy cv wcel vx cv vz
      cv wcel cA vy cv cF wbr vy cv vz cv wceq wb cA vy cv cF wbr vy cv vz cv
      wceq vx cv vy cv wcel vx cv vz cv wcel wi cA vy cv cF wbr vy cv vz cv
      wceq bi1 vy vz vx ax-14 syl6 com23 imp3a sps anc2ri com12 eximdv syl5bi
      exlimi imp impbii bitri abbi2i $.
  $}

  ${
    $d x F $.  $d x A $.  $d x B $.
    $( The value of a restricted function.  (Contributed by NM, 2-Aug-1994.) $)
    fvres $p |- ( A e. B -> ( ( F |` B ) ` A ) = ( F ` A ) ) $=
      cA cB wcel cA vx cv cF cB cres wbr vx cio cA vx cv cF wbr vx cio cA cF cB
      cres cfv cA cF cfv cA cB wcel cA vx cv cF cB cres wbr cA vx cv cF wbr vx
      cA vx cv cF cB cres wbr cA vx cv cF wbr cA cB wcel cA vx cv cF cB vx vex
      brres rbaib iotabidv vx cA cF cB cres df-fv vx cA cF df-fv 3eqtr4g $.
  $}

  $( The value of a member of the domain of a subclass of a function.
     (Contributed by NM, 15-Aug-1994.) $)
  funssfv $p |- ( ( Fun F /\ G C_ F /\ A e. dom G ) ->
                ( F ` A ) = ( G ` A ) ) $=
    cF wfun cG cF wss cA cG cdm wcel cA cF cfv cA cG cfv wceq cA cG cdm wcel cF
    wfun cG cF wss wa cA cF cfv cA cF cG cdm cres cfv cA cG cfv cA cG cdm wcel
    cA cF cG cdm cres cfv cA cF cfv cA cG cdm cF fvres eqcomd cF wfun cG cF wss
    wa cA cF cG cdm cres cG cF cG funssres fveq1d sylan9eqr 3impa $.

  ${
    $d y z F $.  $d y z A $.
    $( Function value.  Theorem 6.12(1) of [TakeutiZaring] p. 27.  (Contributed
       by NM, 30-Apr-2004.) $)
    tz6.12-1 $p |- ( ( A F y /\ E! y A F y ) -> ( F ` A ) = y ) $=
      cA vy cv cF wbr cA vy cv cF wbr vy weu wa cA cF cfv cA vy cv cF wbr vy
      cio vy cv vy cA cF df-fv cA vy cv cF wbr vy weu cA vy cv cF wbr cA vy cv
      cF wbr vy cio vy cv wceq cA vy cv cF wbr vy weu cA vy cv cF wbr cA vy cv
      cF wbr vy cio vy cv wceq cA vy cv cF wbr vy iota1 biimpd impcom syl5eq $.

    $( Function value.  Theorem 6.12(1) of [TakeutiZaring] p. 27.  (Contributed
       by NM, 10-Jul-1994.) $)
    tz6.12 $p |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F ) ->
                 ( F ` A ) = y ) $=
      cA vy cv cop cF wcel cA vy cv cF wbr cA vy cv cF wbr vy weu cA cF cfv vy
      cv wceq cA vy cv cop cF wcel vy weu cA vy cv cF df-br cA vy cv cF wbr cA
      vy cv cop cF wcel vy cA vy cv cF df-br eubii vy cA cF tz6.12-1 syl2anbr
      $.
  $}

  ${
    $d A y z w $.  $d z w v F $.
    tz6.12f.1 $e |- F/_ y F $.
    $( Function value, using bound-variable hypotheses instead of distinct
       variable conditions.  (Contributed by NM, 30-Aug-1999.) $)
    tz6.12f $p |- ( ( <. A , y >. e. F /\ E! y <. A , y >. e. F ) ->
                 ( F ` A ) = y ) $=
      cA vz cv cop cF wcel cA vz cv cop cF wcel vz weu wa cA cF cfv vz cv wceq
      wi cA vy cv cop cF wcel cA vy cv cop cF wcel vy weu wa cA cF cfv vy cv
      wceq wi vz vy vz cv vy cv wceq cA vz cv cop cF wcel cA vz cv cop cF wcel
      vz weu wa cA vy cv cop cF wcel cA vy cv cop cF wcel vy weu wa cA cF cfv
      vz cv wceq cA cF cfv vy cv wceq vz cv vy cv wceq cA vz cv cop cF wcel cA
      vy cv cop cF wcel cA vz cv cop cF wcel vz weu cA vy cv cop cF wcel vy weu
      vz cv vy cv wceq cA vz cv cop cA vy cv cop cF vz cv vy cv cA opeq2 eleq1d
      cA vz cv cop cF wcel vz weu cA vy cv cop cF wcel vy weu wb vz cv vy cv
      wceq cA vz cv cop cF wcel cA vy cv cop cF wcel vz vy vy cA vz cv cop cF
      tz6.12f.1 nfel2 cA vy cv cop cF wcel vz nfv vz cv vy cv wceq cA vz cv cop
      cA vy cv cop cF vz cv vy cv cA opeq2 eleq1d cbveu a1i anbi12d vz cv vy cv
      cA cF cfv eqeq2 imbi12d vz cA cF tz6.12 chvarv $.
  $}

  ${
    $d y F $.  $d y A $.
    $( Corollary of Theorem 6.12(1) of [TakeutiZaring] p. 27.  (Contributed by
       NM, 30-Apr-2004.) $)
    tz6.12c $p |- ( E! y A F y -> ( ( F ` A ) = y <-> A F y ) ) $=
      cA vy cv cF wbr vy weu cA cF cfv vy cv wceq cA vy cv cF wbr cA vy cv cF
      wbr vy weu cA cA cF cfv cF wbr cA cF cfv vy cv wceq cA vy cv cF wbr cA vy
      cv cF wbr vy wex cA vy cv cF wbr vy weu cA cA cF cfv cF wbr cA vy cv cF
      wbr vy euex cA vy cv cF wbr cA vy cv cF wbr vy weu cA cA cF cfv cF wbr wi
      vy cA vy cv cF wbr vy weu cA cA cF cfv cF wbr vy cA vy cv cF wbr vy nfeu1
      cA cA cF cfv cF wbr vy nfv nfim cA vy cv cF wbr vy weu cA vy cv cF wbr cA
      cA cF cfv cF wbr cA vy cv cF wbr cA vy cv cF wbr vy weu cA cF cfv vy cv
      wceq cA cA cF cfv cF wbr cA vy cv cF wbr cA vy cv cF wbr vy weu cA cF cfv
      vy cv wceq vy cA cF tz6.12-1 expcom cA cF cfv vy cv wceq cA cA cF cfv cF
      wbr cA vy cv cF wbr cA cF cfv vy cv cA cF breq2 biimprd syli com12 exlimi
      mpcom cA cF cfv vy cv cA cF breq2 syl5ibcom cA vy cv cF wbr cA vy cv cF
      wbr vy weu cA cF cfv vy cv wceq vy cA cF tz6.12-1 expcom impbid $.
  $}

  ${
    $d x y F $.  $d x y A $.  $d y B $.
    $( Corollary of Theorem 6.12(2) of [TakeutiZaring] p. 27.  (Contributed by
       Mario Carneiro, 17-Nov-2014.) $)
    tz6.12i $p |- ( B =/= (/) -> ( ( F ` A ) = B -> A F B ) ) $=
      cA cF cfv cB wceq cB c0 wne cA cB cF wbr cA cF cfv cB wceq cA cF cfv c0
      wne cA cA cF cfv cF wbr cB c0 wne cA cB cF wbr cA cF cfv c0 wne cA cA cF
      cfv cF wbr wi cA cF cfv cB wceq cA cF cfv c0 wne cA cA cF cfv cF wbr wi
      vy cA cF cfv cA cF fvex vy cv cA cF cfv wceq vy cv c0 wne cA vy cv cF wbr
      cA cF cfv c0 wne cA cA cF cfv cF wbr vy cv c0 wne cA vy cv cF wbr wi cA
      cF cfv vy cv cA cF cfv vy cv wceq vy cv c0 wne cA cF cfv c0 wne cA vy cv
      cF wbr cA cF cfv vy cv c0 neeq1 cA cF cfv c0 wne cA cF cfv vy cv wceq cA
      vy cv cF wbr cA cF cfv c0 wne cA vy cv cF wbr vy weu cA cF cfv vy cv wceq
      cA vy cv cF wbr wb cA vy cv cF wbr vy weu cA cF cfv c0 vy cA cF tz6.12-2
      necon1ai vy cA cF tz6.12c syl biimpcd sylbird eqcoms vy cv cA cF cfv c0
      neeq1 vy cv cA cF cfv cA cF breq2 3imtr3d vtocle a1i cA cF cfv cB c0
      neeq1 cA cF cfv cB cA cF breq2 3imtr3d com12 $.
  $}

  $( Two possibilities for the behavior of a function value.  (Contributed by
     Stefan O'Rear, 2-Nov-2014.)  (Proof shortened by Mario Carneiro,
     31-Aug-2015.) $)
  fvbr0 $p |- ( X F ( F ` X ) \/ ( F ` X ) = (/) ) $=
    cX cX cF cfv cF wbr cX cF cfv c0 wceq cX cX cF cfv cF wbr cX cF cfv c0 cX
    cF cfv c0 wne cX cF cfv cX cF cfv wceq cX cX cF cfv cF wbr cX cF cfv eqid
    cX cX cF cfv cF tz6.12i mpi necon1bi orri $.

  $( A function value is a member of the range plus null.  (Contributed by
     Scott Fenton, 8-Jun-2011.)  (Revised by Stefan O'Rear, 3-Jan-2015.) $)
  fvrn0 $p |- ( F ` X ) e. ( ran F u. { (/) } ) $=
    cX cF cfv c0 wceq cX cF cfv cF crn c0 csn cun wcel cX cF cfv c0 wceq cX cF
    cfv c0 cF crn c0 csn cun cX cF cfv c0 wceq id c0 csn cF crn c0 csn cun c0
    c0 csn cF crn ssun2 c0 0ex snid sselii syl6eqel cX cF cfv c0 wceq wn cF crn
    cF crn c0 csn cun cX cF cfv cF crn c0 csn ssun1 cX cF cfv c0 wceq wn cX cvv
    wcel cX cF cfv cvv wcel cX cX cF cfv cF wbr cX cF cfv cF crn wcel cX cvv
    wcel cX cF cfv c0 wceq cX cF fvprc con1i cX cF cfv cvv wcel cX cF cfv c0
    wceq wn cX cF fvex a1i cX cX cF cfv cF wbr cX cF cfv c0 wceq cX cX cF cfv
    cF wbr cX cF cfv c0 wceq cF cX fvbr0 ori con1i cX cX cF cfv cF cvv cvv
    brelrng syl3anc sseldi pm2.61i $.

  $( The result of a function value is always a subset of the union of the
     range, even if it is invalid and thus empty.  (Contributed by Stefan
     O'Rear, 2-Nov-2014.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
  fvssunirn $p |- ( F ` X ) C_ U. ran F $=
    cX cF cfv cF crn c0 csn cun cuni cF crn cuni cX cF cfv cF crn c0 csn cun
    wcel cX cF cfv cF crn c0 csn cun cuni wss cF cX fvrn0 cX cF cfv cF crn c0
    csn cun elssuni ax-mp cF crn c0 csn cun cuni cF crn cuni c0 csn cuni cun cF
    crn cuni c0 cun cF crn cuni cF crn c0 csn uniun c0 csn cuni c0 cF crn cuni
    c0 0ex unisn uneq2i cF crn cuni un0 3eqtri sseqtri $.

  ${
    $d x y A $.  $d x y F $.
    $( The value of a class outside its domain is the empty set.  (Contributed
       by NM, 24-Aug-1995.) $)
    ndmfv $p |- ( -. A e. dom F -> ( F ` A ) = (/) ) $=
      cA cvv wcel cA cF cdm wcel wn cA cF cfv c0 wceq wi cA cvv wcel cA cF cdm
      wcel wn cA vx cv cF wbr vx weu wn cA cF cfv c0 wceq cA cvv wcel cA vx cv
      cF wbr vx weu cA cF cdm wcel cA vx cv cF wbr vx weu cA cF cdm wcel cA cvv
      wcel cA vx cv cF wbr vx wex cA vx cv cF wbr vx euex vx cA cF cvv eldmg
      syl5ibr con3d vx cA cF tz6.12-2 syl6 cA cvv wcel wn cA cF cfv c0 wceq cA
      cF cdm wcel wn cA cF fvprc a1d pm2.61i $.
  $}

  ${
    ndmfvrcl.1 $e |- dom F = S $.
    ndmfvrcl.2 $e |- -. (/) e. S $.
    $( Reverse closure law for function with the empty set not in its domain.
       (Contributed by NM, 26-Apr-1996.) $)
    ndmfvrcl $p |- ( ( F ` A ) e. S -> A e. S ) $=
      cA cF cfv cS wcel cA cF cdm cS cA cF cdm wcel cA cF cfv cS wcel cA cF cdm
      wcel wn cA cF cfv cS wcel c0 cS wcel ndmfvrcl.2 cA cF cdm wcel wn cA cF
      cfv c0 cS cA cF ndmfv eleq1d mtbiri con4i ndmfvrcl.1 syl6eleq $.
  $}

  $( If a function value has a member, the argument belongs to the domain.
     (Contributed by NM, 12-Feb-2007.) $)
  elfvdm $p |- ( A e. ( F ` B ) -> B e. dom F ) $=
    cA cB cF cfv wcel cB cF cfv c0 wne cB cF cdm wcel cB cF cfv cA ne0i cB cF
    cdm wcel cB cF cfv c0 cB cF ndmfv necon1ai syl $.

  $( If a function value has a member, the argument is a set.  (Contributed by
     Mario Carneiro, 6-Nov-2015.) $)
  elfvex $p |- ( A e. ( F ` B ) -> B e. _V ) $=
    cA cB cF cfv wcel cB cF cdm wcel cB cvv wcel cA cB cF elfvdm cB cF cdm elex
    syl $.

  ${
    elfvexd.1 $e |- ( ph -> A e. ( B ` C ) ) $.
    $( If a function value is nonempty, its argument is a set.  Deduction form
       of ~ elfvex .  (Contributed by David Moews, 1-May-2017.) $)
    elfvexd $p |- ( ph -> C e. _V ) $=
      wph cA cC cB cfv wcel cC cvv wcel elfvexd.1 cA cC cB elfvex syl $.
  $}

  $( The value of a non-member of a restriction is the empty set.  (Contributed
     by NM, 13-Nov-1995.) $)
  nfvres $p |- ( -. A e. B -> ( ( F |` B ) ` A ) = (/) ) $=
    cA cB wcel wn cA cF cB cres cdm wcel wn cA cF cB cres cfv c0 wceq cA cF cB
    cres cdm wcel cA cB wcel cF cB cres cdm cB cA cF cB cres cdm cB cF cdm cin
    cB cF cB dmres cB cF cdm inss1 eqsstri sseli con3i cA cF cB cres ndmfv syl
    $.

  ${
    $d x y A $.  $d x y F $.
    $( If the restriction of a class to a singleton is not a function, its
       value is the empty set.  (Contributed by NM, 8-Aug-2010.)  (Proof
       shortened by Andrew Salmon, 22-Oct-2011.) $)
    nfunsn $p |- ( -. Fun ( F |` { A } ) -> ( F ` A ) = (/) ) $=
      cA cF cfv c0 wceq cF cA csn cres wfun cA cF cfv c0 wceq wn cF cA csn cres
      wrel vx cv vy cv cF cA csn cres wbr vy wmo vx wal wa cF cA csn cres wfun
      cA cF cfv c0 wceq wn vx cv vy cv cF cA csn cres wbr vy wmo vx wal cF cA
      csn cres wrel cA cF cfv c0 wceq wn vx cv vy cv cF cA csn cres wbr vy wmo
      vx cA vy cv cF wbr vy weu vx cv vy cv cF cA csn cres wbr vy wmo cA cF cfv
      c0 wceq cA vy cv cF wbr vy weu cA vy cv cF wbr vy wmo vx cv vy cv cF cA
      csn cres wbr vy wmo cA vy cv cF wbr vy eumo vx cv vy cv cF cA csn cres
      wbr cA vy cv cF wbr vy vx cv vy cv cF cA csn cres wbr vx cv vy cv cF wbr
      vx cv cA csn wcel wa cA vy cv cF wbr vx cv vy cv cF cA csn vy vex brres
      vx cv cA csn wcel vx cv vy cv cF wbr cA vy cv cF wbr vx cv cA csn wcel vx
      cv cA wceq vx cv vy cv cF wbr cA vy cv cF wbr wb vx cA elsn vx cv cA vy
      cv cF breq1 sylbi biimpac sylbi moimi syl vy cA cF tz6.12-2 nsyl4 alrimiv
      cF cA csn relres jctil vx vy cF cA csn cres dffun6 sylibr con1i $.
  $}

  $( Function value of the empty set.  (Contributed by Stefan O'Rear,
     26-Nov-2014.) $)
  fv01 $p |- ( (/) ` A ) = (/) $=
    cA c0 cdm wcel wn cA c0 cfv c0 wceq cA c0 cdm wcel cA c0 wcel cA noel c0
    cdm c0 cA dm0 eleq2i mtbir cA c0 ndmfv ax-mp $.

  $( Equal values imply equal values in a restriction.  (Contributed by NM,
     13-Nov-1995.) $)
  fveqres $p |- ( ( F ` A ) = ( G ` A ) ->
                ( ( F |` B ) ` A ) = ( ( G |` B ) ` A ) ) $=
    cA cB wcel cA cF cfv cA cG cfv wceq cA cF cB cres cfv cA cG cB cres cfv
    wceq wi cA cB wcel cA cF cB cres cfv cA cG cB cres cfv wceq cA cF cfv cA cG
    cfv wceq cA cB wcel cA cF cB cres cfv cA cF cfv cA cG cB cres cfv cA cG cfv
    cA cB cF fvres cA cB cG fvres eqeq12d biimprd cA cB wcel wn cA cF cB cres
    cfv cA cG cB cres cfv wceq cA cF cfv cA cG cfv wceq cA cB wcel wn cA cF cB
    cres cfv c0 cA cG cB cres cfv cA cB cF nfvres cA cB cG nfvres eqtr4d a1d
    pm2.61i $.

  ${
    $d x y A $.  $d x y F $.  $d x y B $.
    $( The second argument of a binary relation on a function is the function's
       value.  (Contributed by NM, 30-Apr-2004.)  (Revised by Mario Carneiro,
       28-Apr-2015.) $)
    funbrfv $p |- ( Fun F -> ( A F B -> ( F ` A ) = B ) ) $=
      cF wfun cA cB cF wbr cA cF cfv cB wceq cB cvv wcel cF wfun cA cB cF wbr
      wa cA cF cfv cB wceq cF wfun cF wrel cA cB cF wbr cB cvv wcel cF funrel
      cA cB cF brrelex2 sylan cF wfun cA vy cv cF wbr wa cA cF cfv vy cv wceq
      wi cF wfun cA cB cF wbr wa cA cF cfv cB wceq wi vy cB cvv vy cv cB wceq
      cF wfun cA vy cv cF wbr wa cF wfun cA cB cF wbr wa cA cF cfv vy cv wceq
      cA cF cfv cB wceq vy cv cB wceq cA vy cv cF wbr cA cB cF wbr cF wfun vy
      cv cB cA cF breq2 anbi2d vy cv cB cA cF cfv eqeq2 imbi12d cF wfun cA vy
      cv cF wbr cA cF cfv vy cv wceq cF wfun cA vy cv cF wbr wa cA vy cv cF wbr
      cA vy cv cF wbr vy weu cA cF cfv vy cv wceq vy cA vy cv cF funeu vy cA cF
      tz6.12-1 sylan2 anabss7 vtoclg mpcom ex $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d x y B $.
    $( The second element in an ordered pair member of a function is the
       function's value.  (Contributed by NM, 19-Jul-1996.) $)
    funopfv $p |- ( Fun F -> ( <. A , B >. e. F -> ( F ` A ) = B ) ) $=
      cA cB cop cF wcel cA cB cF wbr cF wfun cA cF cfv cB wceq cA cB cF df-br
      cA cB cF funbrfv syl5bir $.
  $}

  ${
    $d x y F $.  $d x A $.  $d x y B $.  $d x C $.
    $( Equivalence of function value and binary relation.  (Contributed by NM,
       19-Apr-2004.)  (Revised by Mario Carneiro, 28-Apr-2015.) $)
    fnbrfvb $p |- ( ( F Fn A /\ B e. A ) ->
                   ( ( F ` B ) = C <-> B F C ) ) $=
      cF cA wfn cB cA wcel wa cB cF cfv cC wceq cB cC cF wbr cF cA wfn cB cA
      wcel wa cB cB cF cfv cF wbr cB cF cfv cC wceq cB cC cF wbr cF cA wfn cB
      cA wcel wa cB cF cfv cB cF cfv wceq cB cB cF cfv cF wbr cB cF cfv eqid cF
      cA wfn cB cA wcel wa cB cF cfv vx cv wceq cB vx cv cF wbr wb wi cF cA wfn
      cB cA wcel wa cB cF cfv cB cF cfv wceq cB cB cF cfv cF wbr wb wi vx cB cF
      cfv cB cF fvex vx cv cB cF cfv wceq cB cF cfv vx cv wceq cB vx cv cF wbr
      wb cB cF cfv cB cF cfv wceq cB cB cF cfv cF wbr wb cF cA wfn cB cA wcel
      wa vx cv cB cF cfv wceq cB cF cfv vx cv wceq cB cF cfv cB cF cfv wceq cB
      vx cv cF wbr cB cB cF cfv cF wbr vx cv cB cF cfv cB cF cfv eqeq2 vx cv cB
      cF cfv cB cF breq2 bibi12d imbi2d cF cA wfn cB cA wcel wa cB vx cv cF wbr
      vx weu cB cF cfv vx cv wceq cB vx cv cF wbr wb vx cA cB cF fneu vx cB cF
      tz6.12c syl vtocl mpbii cB cF cfv cC cB cF breq2 syl5ibcom cF cA wfn cB
      cC cF wbr cB cF cfv cC wceq wi cB cA wcel cF cA wfn cF wfun cB cC cF wbr
      cB cF cfv cC wceq wi cA cF fnfun cB cC cF funbrfv syl adantr impbid $.

    $( Equivalence of function value and ordered pair membership.  (Contributed
       by NM, 7-Nov-1995.) $)
    fnopfvb $p |- ( ( F Fn A /\ B e. A ) ->
                   ( ( F ` B ) = C <-> <. B , C >. e. F ) ) $=
      cF cA wfn cB cA wcel wa cB cF cfv cC wceq cB cC cF wbr cB cC cop cF wcel
      cA cB cC cF fnbrfvb cB cC cF df-br syl6bb $.
  $}

  ${
    $( Equivalence of function value and binary relation.  (Contributed by NM,
       26-Mar-2006.) $)
    funbrfvb $p |- ( ( Fun F /\ A e. dom F ) ->
                   ( ( F ` A ) = B <-> A F B ) ) $=
      cF wfun cF cF cdm wfn cA cF cdm wcel cA cF cfv cB wceq cA cB cF wbr wb cF
      funfn cF cdm cA cB cF fnbrfvb sylanb $.

    $( Equivalence of function value and ordered pair membership.  Theorem
       4.3(ii) of [Monk1] p. 42.  (Contributed by NM, 26-Jan-1997.) $)
    funopfvb $p |- ( ( Fun F /\ A e. dom F ) ->
                   ( ( F ` A ) = B <-> <. A , B >. e. F ) ) $=
      cF wfun cF cF cdm wfn cA cF cdm wcel cA cF cfv cB wceq cA cB cop cF wcel
      wb cF funfn cF cdm cA cB cF fnopfvb sylanb $.
  $}

  ${
    $d x y z w A $.  $d x y B $.  $d x y z w F $.  $d x y C $.
    $( Function value in terms of a binary relation.  (Contributed by Mario
       Carneiro, 19-Mar-2014.) $)
    funbrfv2b $p |- ( Fun F ->
                       ( A F B <-> ( A e. dom F /\ ( F ` A ) = B ) ) ) $=
      cF wfun cA cB cF wbr cA cF cdm wcel cA cB cF wbr wa cA cF cdm wcel cA cF
      cfv cB wceq wa cF wfun cA cB cF wbr cA cF cdm wcel cF wfun cF wrel cA cB
      cF wbr cA cF cdm wcel wi cF funrel cF wrel cA cB cF wbr cA cF cdm wcel cA
      cB cF releldm ex syl pm4.71rd cF wfun cA cF cdm wcel cA cF cfv cB wceq cA
      cB cF wbr cA cB cF funbrfvb pm5.32da bitr4d $.

    $( Representation of a function in terms of its values.  (Contributed by
       FL, 14-Sep-2013.)  (Proof shortened by Mario Carneiro, 31-Aug-2015.) $)
    dffn5 $p |- ( F Fn A <-> F = ( x e. A |-> ( F ` x ) ) ) $=
      cF cA wfn cF vx cA vx cv cF cfv cmpt wceq cF cA wfn cF vx cv cA wcel vy
      cv vx cv cF cfv wceq wa vx vy copab vx cA vx cv cF cfv cmpt cF cA wfn cF
      vx cv vy cv cF wbr vx vy copab vx cv cA wcel vy cv vx cv cF cfv wceq wa
      vx vy copab cF cA wfn cF wrel cF vx cv vy cv cF wbr vx vy copab wceq cA
      cF fnrel vx vy cF dfrel4v sylib cF cA wfn vx cv vy cv cF wbr vx cv cA
      wcel vy cv vx cv cF cfv wceq wa vx vy cF cA wfn vx cv vy cv cF wbr vx cv
      cA wcel vx cv vy cv cF wbr wa vx cv cA wcel vy cv vx cv cF cfv wceq wa cF
      cA wfn vx cv vy cv cF wbr vx cv cA wcel cF cA wfn vx cv vy cv cF wbr vx
      cv cA wcel cA vx cv vy cv cF fnbr ex pm4.71rd cF cA wfn vx cv cA wcel vy
      cv vx cv cF cfv wceq vx cv vy cv cF wbr vy cv vx cv cF cfv wceq vx cv cF
      cfv vy cv wceq cF cA wfn vx cv cA wcel wa vx cv vy cv cF wbr vy cv vx cv
      cF cfv eqcom cA vx cv vy cv cF fnbrfvb syl5bb pm5.32da bitr4d opabbidv
      eqtrd vx vy cA vx cv cF cfv df-mpt syl6eqr cF vx cA vx cv cF cfv cmpt
      wceq cF cA wfn vx cA vx cv cF cfv cmpt cA wfn vx cA vx cv cF cfv vx cA vx
      cv cF cfv cmpt vx cv cF fvex vx cA vx cv cF cfv cmpt eqid fnmpti cA cF vx
      cA vx cv cF cfv cmpt fneq1 mpbiri impbii $.

    $( The range of a function expressed as a collection of the function's
       values.  (Contributed by NM, 20-Oct-2005.)  (Proof shortened by Mario
       Carneiro, 31-Aug-2015.) $)
    fnrnfv $p |- ( F Fn A -> ran F = { y | E. x e. A y = ( F ` x ) } ) $=
      cF cA wfn cF crn vx cA vx cv cF cfv cmpt crn vy cv vx cv cF cfv wceq vx
      cA wrex vy cab cF cA wfn cF vx cA vx cv cF cfv cmpt wceq cF crn vx cA vx
      cv cF cfv cmpt crn wceq vx cA cF dffn5 cF vx cA vx cv cF cfv cmpt rneq
      sylbi vx vy cA vx cv cF cfv vx cA vx cv cF cfv cmpt vx cA vx cv cF cfv
      cmpt eqid rnmpt syl6eq $.

    $( A member of a function's range is a value of the function.  (Contributed
       by NM, 31-Oct-1995.) $)
    fvelrnb $p |- ( F Fn A -> ( B e. ran F <-> E. x e. A ( F ` x ) = B ) ) $=
      cF cA wfn cB cF crn wcel cB vy cv vx cv cF cfv wceq vx cA wrex vy cab
      wcel vx cv cF cfv cB wceq vx cA wrex cF cA wfn cF crn vy cv vx cv cF cfv
      wceq vx cA wrex vy cab cB vx vy cA cF fnrnfv eleq2d vy cv vx cv cF cfv
      wceq vx cA wrex vx cv cF cfv cB wceq vx cA wrex vy cB vx cv cF cfv cB
      wceq cB cvv wcel vx cA vx cv cF cfv cB wceq vx cv cF cfv cvv wcel cB cvv
      wcel vx cv cF fvex vx cv cF cfv cB cvv eleq1 mpbii rexlimivw vy cv cB
      wceq vy cv vx cv cF cfv wceq vx cv cF cfv cB wceq vx cA vy cv cB wceq vy
      cv vx cv cF cfv wceq cB vx cv cF cfv wceq vx cv cF cfv cB wceq vy cv cB
      vx cv cF cfv eqeq1 cB vx cv cF cfv eqcom syl6bb rexbidv elab3 syl6bb $.

    $( Alternate definition of the image of a function.  (Contributed by Raph
       Levien, 20-Nov-2006.) $)
    dfimafn $p |- ( ( Fun F /\ A C_ dom F ) ->
                  ( F " A ) = { y | E. x e. A ( F ` x ) = y } ) $=
      cF wfun cA cF cdm wss wa vx cv cF cfv vy cv wceq vx cA wrex vy cab vx cv
      vy cv cF wbr vx cA wrex vy cab cF cA cima cF wfun cA cF cdm wss wa vx cv
      cF cfv vy cv wceq vx cA wrex vx cv vy cv cF wbr vx cA wrex vy cF wfun cA
      cF cdm wss wa vx cv cF cfv vy cv wceq vx cv vy cv cF wbr vx cA cF wfun cA
      cF cdm wss vx cv cA wcel vx cv cF cfv vy cv wceq vx cv vy cv cF wbr wb cA
      cF cdm wss vx cv cA wcel vx cv cF cdm wcel cF wfun vx cv cF cfv vy cv
      wceq vx cv vy cv cF wbr wb cA cF cdm vx cv ssel cF wfun vx cv cF cdm wcel
      vx cv cF cfv vy cv wceq vx cv vy cv cF wbr wb vx cv vy cv cF funbrfvb ex
      syl9r imp31 rexbidva abbidv vx vy cF cA dfima2 syl6reqr $.

    $( Alternate definition of the image of a function as an indexed union of
       singletons of function values.  (Contributed by Raph Levien,
       20-Nov-2006.) $)
    dfimafn2 $p |- ( ( Fun F /\ A C_ dom F ) ->
                   ( F " A ) = U_ x e. A { ( F ` x ) } ) $=
      cF wfun cA cF cdm wss wa cF cA cima vx cA vx cv cF cfv vy cv wceq vy cab
      ciun vx cA vx cv cF cfv csn ciun cF wfun cA cF cdm wss wa cF cA cima vx
      cv cF cfv vy cv wceq vx cA wrex vy cab vx cA vx cv cF cfv vy cv wceq vy
      cab ciun vx vy cA cF dfimafn vx cv cF cfv vy cv wceq vx vy cA iunab
      syl6eqr vx cA vx cv cF cfv csn vx cv cF cfv vy cv wceq vy cab vx cv cF
      cfv csn vx cv cF cfv vy cv wceq vy cab wceq vx cv cA wcel vx cv cF cfv
      csn vy cv vx cv cF cfv wceq vy cab vx cv cF cfv vy cv wceq vy cab vy vx
      cv cF cfv df-sn vy cv vx cv cF cfv wceq vx cv cF cfv vy cv wceq vy vy cv
      vx cv cF cfv eqcom abbii eqtri a1i iuneq2i syl6eqr $.

    $( Membership relation for the values of a function whose image is a
       subclass.  (Contributed by Raph Levien, 20-Nov-2006.) $)
    funimass4 $p |- ( ( Fun F /\ A C_ dom F ) ->
                    ( ( F " A ) C_ B <-> A. x e. A ( F ` x ) e. B ) ) $=
      cA cF cdm wss cF wfun cF cA cima cB wss vx cv cF cfv cB wcel vx cA wral
      wb cF cA cima cB wss vy cv cF cA cima wcel vy cv cB wcel wi vy wal cA cF
      cdm wss cF wfun wa vx cv cF cfv cB wcel vx cA wral vy cF cA cima cB dfss2
      cA cF cdm wss cF wfun wa vy cv cF cA cima wcel vy cv cB wcel wi vy wal vy
      cv vx cv cF cfv wceq vy cv cB wcel wi vx cA wral vy wal vx cv cF cfv cB
      wcel vx cA wral cA cF cdm wss cF wfun wa vy cv cF cA cima wcel vy cv cB
      wcel wi vy cv vx cv cF cfv wceq vy cv cB wcel wi vx cA wral vy cA cF cdm
      wss cF wfun wa vy cv cF cA cima wcel vy cv cB wcel wi vy cv vx cv cF cfv
      wceq vx cA wrex vy cv cB wcel wi vy cv vx cv cF cfv wceq vy cv cB wcel wi
      vx cA wral cA cF cdm wss cF wfun wa vy cv cF cA cima wcel vy cv vx cv cF
      cfv wceq vx cA wrex vy cv cB wcel cA cF cdm wss cF wfun wa vy cv vx cv cF
      cfv wceq vx cA wrex vx cv vy cv cF wbr vx cA wrex vy cv cF cA cima wcel
      cA cF cdm wss cF wfun wa vy cv vx cv cF cfv wceq vx cv vy cv cF wbr vx cA
      vy cv vx cv cF cfv wceq vx cv cF cfv vy cv wceq cA cF cdm wss cF wfun wa
      vx cv cA wcel wa vx cv vy cv cF wbr vy cv vx cv cF cfv eqcom cA cF cdm
      wss cF wfun vx cv cA wcel vx cv cF cfv vy cv wceq vx cv vy cv cF wbr wb
      cA cF cdm wss vx cv cA wcel vx cv cF cdm wcel cF wfun vx cv cF cfv vy cv
      wceq vx cv vy cv cF wbr wb cA cF cdm vx cv ssel cF wfun vx cv cF cdm wcel
      vx cv cF cfv vy cv wceq vx cv vy cv cF wbr wb vx cv vy cv cF funbrfvb ex
      syl9 imp31 syl5bb rexbidva vx vy cv cF cA vy vex elima syl6rbbr imbi1d vy
      cv vx cv cF cfv wceq vy cv cB wcel vx cA r19.23v syl6bbr albidv vy cv vx
      cv cF cfv wceq vy cv cB wcel wi vx cA wral vy wal vy cv vx cv cF cfv wceq
      vy cv cB wcel wi vy wal vx cA wral vx cv cF cfv cB wcel vx cA wral vy cv
      vx cv cF cfv wceq vy cv cB wcel wi vx vy cA ralcom4 vy cv vx cv cF cfv
      wceq vy cv cB wcel wi vy wal vx cv cF cfv cB wcel vx cA vy cv cB wcel vx
      cv cF cfv cB wcel vy vx cv cF cfv vx cv cF fvex vy cv vx cv cF cfv cB
      eleq1 ceqsalv ralbii bitr3i syl6bb syl5bb ancoms $.

    $( Function value in an image.  Part of Theorem 4.4(iii) of [Monk1] p. 42.
       (Contributed by NM, 29-Apr-2004.)  (Proof shortened by Andrew Salmon,
       22-Oct-2011.) $)
    fvelima $p |- ( ( Fun F /\ A e. ( F " B ) ) ->
                  E. x e. B ( F ` x ) = A ) $=
      cF wfun cA cF cB cima wcel vx cv cF cfv cA wceq vx cB wrex cA cF cB cima
      wcel vx cv cA cF wbr vx cB wrex cF wfun vx cv cF cfv cA wceq vx cB wrex
      cA cF cB cima wcel vx cv cA cF wbr vx cB wrex vx cA cF cB cF cB cima
      elimag ibi cF wfun vx cv cA cF wbr vx cv cF cfv cA wceq vx cB vx cv cA cF
      funbrfv reximdv syl5 imp $.
  $}

  ${
    $d x y A $.  $d x C $.  $d x y F $.
    feqmptd.1 $e |- ( ph -> F : A --> B ) $.
    $( Deduction form of ~ dffn5 .  (Contributed by Mario Carneiro,
       8-Jan-2015.) $)
    feqmptd $p |- ( ph -> F = ( x e. A |-> ( F ` x ) ) ) $=
      wph cF cA wfn cF vx cA vx cv cF cfv cmpt wceq wph cA cB cF wf cF cA wfn
      feqmptd.1 cA cB cF ffn syl vx cA cF dffn5 sylib $.

    feqresmpt.2 $e |- ( ph -> C C_ A ) $.
    $( Express a restricted function as a mapping.  (Contributed by Mario
       Carneiro, 18-May-2016.) $)
    feqresmpt $p |- ( ph -> ( F |` C ) = ( x e. C |-> ( F ` x ) ) ) $=
      wph cF cC cres vx cC vx cv cF cC cres cfv cmpt vx cC vx cv cF cfv cmpt
      wph vx cC cB cF cC cres wph cA cB cF wf cC cA wss cC cB cF cC cres wf
      feqmptd.1 feqresmpt.2 cA cB cC cF fssres syl2anc feqmptd vx cC vx cv cF
      cC cres cfv vx cv cF cfv vx cv cC cF fvres mpteq2ia syl6eq $.
  $}

  ${
    $d x z $.  $d x z A $.  $d z F $.
    dffn5f.1 $e |- F/_ x F $.
    $( Representation of a function in terms of its values.  (Contributed by
       Mario Carneiro, 3-Jul-2015.) $)
    dffn5f $p |- ( F Fn A <-> F = ( x e. A |-> ( F ` x ) ) ) $=
      cF cA wfn cF vz cA vz cv cF cfv cmpt wceq cF vx cA vx cv cF cfv cmpt wceq
      vz cA cF dffn5 vz cA vz cv cF cfv cmpt vx cA vx cv cF cfv cmpt cF vz vx
      cA vz cv cF cfv vx cv cF cfv vx vz cv cF dffn5f.1 vx vz cv nfcv nffv vz
      vx cv cF cfv nfcv vz cv vx cv cF fveq2 cbvmpt eqeq2i bitri $.
  $}

  ${
    $d y A $.  $d x y B $.  $d x y C $.  $d x y F $.
    $( Function value in an image.  (Contributed by NM, 20-Jan-2007.)  (Proof
       shortened by Andrew Salmon, 22-Oct-2011.)  (Revised by David Abernethy,
       17-Dec-2011.) $)
    fvelimab $p |- ( ( F Fn A /\ B C_ A ) -> ( C e. ( F " B ) <->
                  E. x e. B ( F ` x ) = C ) ) $=
      cF cA wfn cB cA wss wa cC cF cB cima wcel vx cv cF cfv cC wceq vx cB wrex
      cF cA wfn cB cA wss wa cC cvv wcel wa cC cF cB cima wcel cC cvv wcel cF
      cA wfn cB cA wss wa cC cF cB cima elex anim2i vx cv cF cfv cC wceq vx cB
      wrex cC cvv wcel cF cA wfn cB cA wss wa vx cv cF cfv cC wceq cC cvv wcel
      vx cB vx cv cF cfv cC wceq vx cv cF cfv cvv wcel cC cvv wcel vx cv cF
      fvex vx cv cF cfv cC cvv eleq1 mpbii rexlimivw anim2i cC cvv wcel cF cA
      wfn cB cA wss wa cC cF cB cima wcel vx cv cF cfv cC wceq vx cB wrex wb cF
      cA wfn cB cA wss wa vy cv cF cB cima wcel vx cv cF cfv vy cv wceq vx cB
      wrex wb wi cF cA wfn cB cA wss wa cC cF cB cima wcel vx cv cF cfv cC wceq
      vx cB wrex wb wi vy cC cvv vy cv cC wceq vy cv cF cB cima wcel vx cv cF
      cfv vy cv wceq vx cB wrex wb cC cF cB cima wcel vx cv cF cfv cC wceq vx
      cB wrex wb cF cA wfn cB cA wss wa vy cv cC wceq vy cv cF cB cima wcel cC
      cF cB cima wcel vx cv cF cfv vy cv wceq vx cB wrex vx cv cF cfv cC wceq
      vx cB wrex vy cv cC cF cB cima eleq1 vy cv cC wceq vx cv cF cfv vy cv
      wceq vx cv cF cfv cC wceq vx cB vy cv cC vx cv cF cfv eqeq2 rexbidv
      bibi12d imbi2d cF cA wfn cB cA wss wa vx cv cF cfv vy cv wceq vx cB wrex
      vy cF cB cima cF cA wfn cB cA wss wa cF wfun cB cF cdm wss cF cB cima vx
      cv cF cfv vy cv wceq vx cB wrex vy cab wceq cF cA wfn cF wfun cB cA wss
      cA cF fnfun adantr cF cA wfn cB cF cdm wss cB cA wss cF cA wfn cF cdm cA
      cB cA cF fndm sseq2d biimpar vx vy cB cF dfimafn syl2anc abeq2d vtoclg
      impcom pm5.21nd $.
  $}

  $( The value of the identity function.  (Contributed by NM, 1-May-2004.)
     (Revised by Mario Carneiro, 28-Apr-2015.) $)
  fvi $p |- ( A e. V -> ( _I ` A ) = A ) $=
    cid wfun cA cV wcel cA cA cid wbr cA cid cfv cA wceq funi cA cV ididg cA cA
    cid funbrfv mpsyl $.

  ${
    $d x y A $.  $d y B $.  $d x y F $.
    $( The value of the identity function is a subset of the argument.
       (Contributed by Mario Carneiro, 27-Feb-2016.) $)
    fviss $p |- ( _I ` A ) C_ A $=
      vx cA cid cfv cA vx cv cA cid cfv wcel vx cv cA cid cfv cA vx cv cA cid
      cfv wcel id vx cv cA cid cfv wcel cA cvv wcel cA cid cfv cA wceq vx cv cA
      cid elfvex cA cvv fvi syl eleqtrd ssriv $.

    $( The indexed intersection of a function's values is the intersection of
       its range.  (Contributed by NM, 20-Oct-2005.) $)
    fniinfv $p |- ( F Fn A -> |^|_ x e. A ( F ` x ) = |^| ran F ) $=
      cF cA wfn cF crn cint vy cv vx cv cF cfv wceq vx cA wrex vy cab cint vx
      cA vx cv cF cfv ciin cF cA wfn cF crn vy cv vx cv cF cfv wceq vx cA wrex
      vy cab vx vy cA cF fnrnfv inteqd vx vy cA vx cv cF cfv vx cv cF fvex
      dfiin2 syl6reqr $.

    $( Singleton of function value.  (Contributed by NM, 22-May-1998.) $)
    fnsnfv $p |- ( ( F Fn A /\ B e. A ) -> { ( F ` B ) } = ( F " { B } ) ) $=
      cF cA wfn cB cA wcel wa vy cv cB cF cfv wceq vy cab cB vy cv cF wbr vy
      cab cB cF cfv csn cF cB csn cima cF cA wfn cB cA wcel wa vy cv cB cF cfv
      wceq cB vy cv cF wbr vy vy cv cB cF cfv wceq cB cF cfv vy cv wceq cF cA
      wfn cB cA wcel wa cB vy cv cF wbr vy cv cB cF cfv eqcom cA cB vy cv cF
      fnbrfvb syl5bb abbidv cB cF cfv csn vy cv cB cF cfv wceq vy cab wceq cF
      cA wfn cB cA wcel wa vy cB cF cfv df-sn a1i cF cA wfn cF cB csn cima cB
      vy cv cF wbr vy cab wceq cB cA wcel cF cA wfn cF wrel cF cB csn cima cB
      vy cv cF wbr vy cab wceq cA cF fnrel vy cB cF relimasn syl adantr 3eqtr4d
      $.
  $}

  $( The image of a pair under a funtion.  (Contributed by Jeff Madsen,
     6-Jan-2011.) $)
  fnimapr $p |- ( ( F Fn A /\ B e. A /\ C e. A ) ->
                          ( F " { B , C } ) = { ( F ` B ) , ( F ` C ) } ) $=
    cF cA wfn cB cA wcel cC cA wcel w3a cF cB csn cima cF cC csn cima cun cB cF
    cfv csn cC cF cfv csn cun cF cB cC cpr cima cB cF cfv cC cF cfv cpr cF cA
    wfn cB cA wcel cC cA wcel w3a cB cF cfv csn cC cF cfv csn cun cF cB csn
    cima cF cC csn cima cun cF cA wfn cB cA wcel cC cA wcel w3a cB cF cfv csn
    cF cB csn cima cC cF cfv csn cF cC csn cima cF cA wfn cB cA wcel cB cF cfv
    csn cF cB csn cima wceq cC cA wcel cA cB cF fnsnfv 3adant3 cF cA wfn cC cA
    wcel cC cF cfv csn cF cC csn cima wceq cB cA wcel cA cC cF fnsnfv 3adant2
    uneq12d eqcomd cF cB cC cpr cima cF cB csn cC csn cun cima cF cB csn cima
    cF cC csn cima cun cB cC cpr cB csn cC csn cun cF cB cC df-pr imaeq2i cF cB
    csn cC csn imaundi eqtri cB cF cfv cC cF cfv df-pr 3eqtr4g $.

  ${
    $d w x y z A $.  $d w x y z B $.  $d w x y z F $.
    ssimaex.1 $e |- A e. _V $.
    $( The existence of a subimage.  (Contributed by NM, 8-Apr-2007.) $)
    ssimaex $p |- ( ( Fun F /\ B C_ ( F " A ) ) ->
                 E. x ( x C_ A /\ B = ( F " x ) ) ) $=
      cB cF cA cima wss cF wfun cB cF cA cF cdm cin cima wss vx cv cA wss cB cF
      vx cv cima wceq wa vx wex cF cA cF cdm cin cima cF cA cima cB cF cF cA
      cres cdm cima cF cA cF cdm cin cima cF cA cima cF cA cres cdm cA cF cdm
      cin cF cF cA dmres imaeq2i cF cA imadmres eqtr3i sseq2i cF wfun cB cF cA
      cF cdm cin cima wss wa vx cv cA cF cdm cin wss cB cF vx cv cima wceq wa
      vx wex vx cv cA wss cB cF vx cv cima wceq wa vx wex cF wfun cB cF cA cF
      cdm cin cima wss wa vy cv cF cfv cB wcel vy cA cF cdm cin crab cA cF cdm
      cin wss cB cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima wceq vx cv
      cA cF cdm cin wss cB cF vx cv cima wceq wa vx wex vy cv cF cfv cB wcel vy
      cA cF cdm cin ssrab2 cF wfun cB cF cA cF cdm cin cima wss wa vz cB cF vy
      cv cF cfv cB wcel vy cA cF cdm cin crab cima cF wfun cB cF cA cF cdm cin
      cima wss wa vz cv cB wcel vz cv cF vy cv cF cfv cB wcel vy cA cF cdm cin
      crab cima wcel cF wfun cB cF cA cF cdm cin cima wss wa vz cv cB wcel vz
      cv cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima wcel cF wfun cB cF
      cA cF cdm cin cima wss wa vz cv cB wcel wa vz cv cF cA cF cdm cin cima
      wcel vz cv cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima wcel cB cF
      cA cF cdm cin cima wss vz cv cB wcel vz cv cF cA cF cdm cin cima wcel cF
      wfun cB cF cA cF cdm cin cima vz cv ssel2 adantll cF wfun vz cv cB wcel
      vz cv cF cA cF cdm cin cima wcel vz cv cF vy cv cF cfv cB wcel vy cA cF
      cdm cin crab cima wcel wi cB cF cA cF cdm cin cima wss cF wfun vz cv cB
      wcel wa vz cv cF cA cF cdm cin cima wcel vw cv cF cfv vz cv wceq vw cA cF
      cdm cin wrex vz cv cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima
      wcel cF wfun vz cv cF cA cF cdm cin cima wcel vw cv cF cfv vz cv wceq vw
      cA cF cdm cin wrex wi vz cv cB wcel cF wfun vz cv cF cA cF cdm cin cima
      wcel vw cv cF cfv vz cv wceq vw cA cF cdm cin wrex vw vz cv cA cF cdm cin
      cF fvelima ex adantr cF wfun vz cv cB wcel wa vw cv cF cfv vz cv wceq vw
      cA cF cdm cin wrex vw cv cF cfv vz cv wceq vw vy cv cF cfv cB wcel vy cA
      cF cdm cin crab wrex vz cv cF vy cv cF cfv cB wcel vy cA cF cdm cin crab
      cima wcel vz cv cB wcel vw cv cF cfv vz cv wceq vw cA cF cdm cin wrex vw
      cv cF cfv vz cv wceq vw vy cv cF cfv cB wcel vy cA cF cdm cin crab wrex
      wi cF wfun vz cv cB wcel vw cv cF cfv vz cv wceq vw cv cF cfv vz cv wceq
      vw cA cF cdm cin vy cv cF cfv cB wcel vy cA cF cdm cin crab vz cv cB wcel
      vw cv cA cF cdm cin wcel vw cv cF cfv vz cv wceq wa vw cv vy cv cF cfv cB
      wcel vy cA cF cdm cin crab wcel vw cv cF cfv vz cv wceq vz cv cB wcel vw
      cv cA cF cdm cin wcel vw cv cF cfv vz cv wceq wa vw cv cA cF cdm cin wcel
      vw cv cF cfv cB wcel wa vw cv vy cv cF cfv cB wcel vy cA cF cdm cin crab
      wcel vz cv cB wcel vw cv cF cfv vz cv wceq vw cv cF cfv cB wcel vw cv cA
      cF cdm cin wcel vz cv cB vw cv cF cfv eleq1a anim2d vy cv cF cfv cB wcel
      vw cv cF cfv cB wcel vy vw cv cA cF cdm cin vy cv vw cv wceq vy cv cF cfv
      vw cv cF cfv cB vy cv vw cv cF fveq2 eleq1d elrab syl6ibr vw cv cA cF cdm
      cin wcel vw cv cF cfv vz cv wceq wa vw cv cF cfv vz cv wceq wi vz cv cB
      wcel vw cv cA cF cdm cin wcel vw cv cF cfv vz cv wceq simpr a1i jcad
      reximdv2 adantl cF wfun vz cv cF vy cv cF cfv cB wcel vy cA cF cdm cin
      crab cima wcel vw cv cF cfv vz cv wceq vw vy cv cF cfv cB wcel vy cA cF
      cdm cin crab wrex wb vz cv cB wcel cF wfun cF cF cdm wfn vz cv cF vy cv
      cF cfv cB wcel vy cA cF cdm cin crab cima wcel vw cv cF cfv vz cv wceq vw
      vy cv cF cfv cB wcel vy cA cF cdm cin crab wrex wb cF funfn cF cF cdm wfn
      vy cv cF cfv cB wcel vy cA cF cdm cin crab cF cdm wss vz cv cF vy cv cF
      cfv cB wcel vy cA cF cdm cin crab cima wcel vw cv cF cfv vz cv wceq vw vy
      cv cF cfv cB wcel vy cA cF cdm cin crab wrex wb vy cv cF cfv cB wcel vy
      cA cF cdm cin crab cA cF cdm cin cF cdm vy cv cF cfv cB wcel vy cA cF cdm
      cin ssrab2 cA cF cdm inss2 sstri vw cF cdm vy cv cF cfv cB wcel vy cA cF
      cdm cin crab vz cv cF fvelimab mpan2 sylbi adantr sylibrd syld adantlr
      mpd ex cF wfun vz cv cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima
      wcel vz cv cB wcel wi cB cF cA cF cdm cin cima wss cF wfun vz cv cF vy cv
      cF cfv cB wcel vy cA cF cdm cin crab cima wcel vw cv cF cfv vz cv wceq vw
      vy cv cF cfv cB wcel vy cA cF cdm cin crab wrex vz cv cB wcel cF wfun vz
      cv cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima wcel vw cv cF cfv
      vz cv wceq vw vy cv cF cfv cB wcel vy cA cF cdm cin crab wrex vw vz cv vy
      cv cF cfv cB wcel vy cA cF cdm cin crab cF fvelima ex vw cv cF cfv vz cv
      wceq vz cv cB wcel vw vy cv cF cfv cB wcel vy cA cF cdm cin crab vw cv vy
      cv cF cfv cB wcel vy cA cF cdm cin crab wcel vw cv cA cF cdm cin wcel vw
      cv cF cfv cB wcel wa vw cv cF cfv vz cv wceq vz cv cB wcel wi vy cv cF
      cfv cB wcel vw cv cF cfv cB wcel vy vw cv cA cF cdm cin vy cv vw cv wceq
      vy cv cF cfv vw cv cF cfv cB vy cv vw cv cF fveq2 eleq1d elrab vw cv cF
      cfv cB wcel vw cv cF cfv vz cv wceq vz cv cB wcel wi vw cv cA cF cdm cin
      wcel vw cv cF cfv vz cv wceq vw cv cF cfv cB wcel vz cv cB wcel vw cv cF
      cfv vz cv cB eleq1 biimpcd adantl sylbi rexlimiv syl6 adantr impbid eqrdv
      vx cv cA cF cdm cin wss cB cF vx cv cima wceq wa vy cv cF cfv cB wcel vy
      cA cF cdm cin crab cA cF cdm cin wss cB cF vy cv cF cfv cB wcel vy cA cF
      cdm cin crab cima wceq wa vx vy cv cF cfv cB wcel vy cA cF cdm cin crab
      vy cv cF cfv cB wcel vy cA cF cdm cin cA cF cdm ssimaex.1 inex1 rabex vx
      cv vy cv cF cfv cB wcel vy cA cF cdm cin crab wceq vx cv cA cF cdm cin
      wss vy cv cF cfv cB wcel vy cA cF cdm cin crab cA cF cdm cin wss cB cF vx
      cv cima wceq cB cF vy cv cF cfv cB wcel vy cA cF cdm cin crab cima wceq
      vx cv vy cv cF cfv cB wcel vy cA cF cdm cin crab cA cF cdm cin sseq1 vx
      cv vy cv cF cfv cB wcel vy cA cF cdm cin crab wceq cF vx cv cima cF vy cv
      cF cfv cB wcel vy cA cF cdm cin crab cima cB vx cv vy cv cF cfv cB wcel
      vy cA cF cdm cin crab cF imaeq2 eqeq2d anbi12d spcev sylancr vx cv cA cF
      cdm cin wss cB cF vx cv cima wceq wa vx cv cA wss cB cF vx cv cima wceq
      wa vx vx cv cA cF cdm cin wss vx cv cA wss cB cF vx cv cima wceq vx cv cA
      cF cdm cin wss cA cF cdm cin cA wss vx cv cA wss cA cF cdm inss1 vx cv cA
      cF cdm cin cA sstr mpan2 anim1i eximi syl sylan2br $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.
    $( The existence of a subimage.  (Contributed by FL, 15-Apr-2007.) $)
    ssimaexg $p |- ( ( A e. C /\ Fun F /\ B C_ ( F " A ) ) ->
                 E. x ( x C_ A /\ B = ( F " x ) ) ) $=
      cA cC wcel cF wfun cB cF cA cima wss vx cv cA wss cB cF vx cv cima wceq
      wa vx wex cF wfun cB cF vy cv cima wss wa vx cv vy cv wss cB cF vx cv
      cima wceq wa vx wex wi cF wfun cB cF cA cima wss wa vx cv cA wss cB cF vx
      cv cima wceq wa vx wex wi vy cA cC vy cv cA wceq cF wfun cB cF vy cv cima
      wss wa cF wfun cB cF cA cima wss wa vx cv vy cv wss cB cF vx cv cima wceq
      wa vx wex vx cv cA wss cB cF vx cv cima wceq wa vx wex vy cv cA wceq cB
      cF vy cv cima wss cB cF cA cima wss cF wfun vy cv cA wceq cF vy cv cima
      cF cA cima cB vy cv cA cF imaeq2 sseq2d anbi2d vy cv cA wceq vx cv vy cv
      wss cB cF vx cv cima wceq wa vx cv cA wss cB cF vx cv cima wceq wa vx vy
      cv cA wceq vx cv vy cv wss vx cv cA wss cB cF vx cv cima wceq vy cv cA vx
      cv sseq2 anbi1d exbidv imbi12d vx vy cv cB cF vy vex ssimaex vtoclg
      3impib $.
  $}

  $( A simplified expression for the value of a function when we know it's a
     function.  (Contributed by NM, 22-May-1998.) $)
  funfv $p |- ( Fun F -> ( F ` A ) = U. ( F " { A } ) ) $=
    cF wfun cA cF cdm wcel cA cF cfv cF cA csn cima cuni wceq cF wfun cA cF cdm
    wcel cA cF cfv cF cA csn cima cuni wceq cF wfun cA cF cdm wcel wa cA cF cfv
    cA cF cfv csn cuni cF cA csn cima cuni cA cF cfv cA cF fvex unisn cF wfun
    cA cF cdm wcel wa cA cF cfv csn cF cA csn cima cF wfun cF cF cdm wfn cA cF
    cdm wcel cA cF cfv csn cF cA csn cima wceq cF cF cdm wfn cF wfun cF cdm cF
    cdm wceq cF cdm eqid cF cF cdm df-fn mpbiran2 cF cdm cA cF fnsnfv sylanbr
    unieqd syl5eqr ex cA cF cdm wcel wn cA cF cfv c0 cF cA csn cima cuni cA cF
    ndmfv cA cF cdm wcel wn cF cA csn cima cuni c0 cuni c0 cA cF cdm wcel wn cF
    cA csn cima c0 cA cF ndmima unieqd uni0 syl6eq eqtr4d pm2.61d1 $.

  ${
    $d y A $.  $d y F $.
    $( The value of a function.  Definition of function value in [Enderton]
       p. 43.  (Contributed by NM, 22-May-1998.) $)
    funfv2 $p |- ( Fun F -> ( F ` A ) = U. { y | A F y } ) $=
      cF wfun cA cF cfv cF cA csn cima cuni cA vy cv cF wbr vy cab cuni cA cF
      funfv cF wfun cF cA csn cima cA vy cv cF wbr vy cab cF wfun cF wrel cF cA
      csn cima cA vy cv cF wbr vy cab wceq cF funrel vy cA cF relimasn syl
      unieqd eqtrd $.
  $}

  ${
    $d w z A $.  $d w z F $.  $d w y z $.
    funfv2f.1 $e |- F/_ y A $.
    funfv2f.2 $e |- F/_ y F $.
    $( The value of a function.  Version of ~ funfv2 using a bound-variable
       hypotheses instead of distinct variable conditions.  (Contributed by NM,
       19-Feb-2006.) $)
    funfv2f $p |- ( Fun F -> ( F ` A ) = U. { y | A F y } ) $=
      cF wfun cA cF cfv cA vw cv cF wbr vw cab cuni cA vy cv cF wbr vy cab cuni
      vw cA cF funfv2 cA vw cv cF wbr vw cab cA vy cv cF wbr vy cab cA vw cv cF
      wbr cA vy cv cF wbr vw vy vy cA vw cv cF funfv2f.1 funfv2f.2 vy vw cv
      nfcv nfbr cA vy cv cF wbr vw nfv vw cv vy cv cA cF breq2 cbvab unieqi
      syl6eq $.
  $}

  $( Value of the union of two functions when the domains are separate.
     (Contributed by FL, 7-Nov-2011.) $)
  fvun $p |- ( ( ( Fun F /\ Fun G ) /\ ( dom F i^i dom G ) = (/) ) ->
                ( ( F u. G ) ` A ) = ( ( F ` A ) u. ( G ` A ) ) ) $=
    cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cA cF cG cun cfv cF cG cun
    cA csn cima cuni cF cA csn cima cG cA csn cima cun cuni cA cF cfv cA cG cfv
    cun cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cF cG cun wfun cA cF cG
    cun cfv cF cG cun cA csn cima cuni wceq cF cG funun cA cF cG cun funfv syl
    cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cF cG cun cA csn cima cF cA
    csn cima cG cA csn cima cun cF cG cun cA csn cima cF cA csn cima cG cA csn
    cima cun wceq cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cF cG cA csn
    imaundir a1i unieqd cF wfun cG wfun wa cF cdm cG cdm cin c0 wceq wa cF cA
    csn cima cG cA csn cima cun cuni cF cA csn cima cuni cG cA csn cima cuni
    cun cA cF cfv cA cG cfv cun cF cA csn cima cG cA csn cima uniun cF wfun cG
    wfun wa cF cdm cG cdm cin c0 wceq wa cF cA csn cima cuni cA cF cfv wceq cG
    cA csn cima cuni cA cG cfv wceq wa cF cA csn cima cuni cG cA csn cima cuni
    cun cA cF cfv cA cG cfv cun wceq cF wfun cG wfun wa cF cA csn cima cuni cA
    cF cfv wceq cG cA csn cima cuni cA cG cfv wceq wa cF cdm cG cdm cin c0 wceq
    cF wfun cF cA csn cima cuni cA cF cfv wceq cG wfun cG cA csn cima cuni cA
    cG cfv wceq cF wfun cA cF cfv cF cA csn cima cuni cA cF funfv eqcomd cG
    wfun cA cG cfv cG cA csn cima cuni cA cG funfv eqcomd anim12i adantr cF cA
    csn cima cuni cA cF cfv cG cA csn cima cuni cA cG cfv uneq12 syl syl5eq
    3eqtrd $.

  ${
    $d A x $.  $d B x $.  $d X x $.
    $( The value of a union when the argument is in the first domain.
       (Contributed by Scott Fenton, 29-Jun-2013.) $)
    fvun1 $p |- ( ( F Fn A /\ G Fn B /\ ( ( A i^i B ) = (/) /\ X e. A ) ) ->
    ( ( F u. G ) ` X ) = ( F ` X ) ) $=
      cF cA wfn cG cB wfn cA cB cin c0 wceq cX cA wcel wa w3a cX cF cG cun cfv
      cX cF cfv cX cG cfv cun cX cF cfv cF cA wfn cG cB wfn cA cB cin c0 wceq
      cX cA wcel wa w3a cF wfun cG wfun cF cdm cG cdm cin c0 wceq cX cF cG cun
      cfv cX cF cfv cX cG cfv cun wceq cF cA wfn cG cB wfn cF wfun cA cB cin c0
      wceq cX cA wcel wa cA cF fnfun 3ad2ant1 cG cB wfn cF cA wfn cG wfun cA cB
      cin c0 wceq cX cA wcel wa cB cG fnfun 3ad2ant2 cF cA wfn cG cB wfn cA cB
      cin c0 wceq cX cA wcel wa cF cdm cG cdm cin c0 wceq cF cA wfn cG cB wfn
      wa cA cB cin c0 wceq cF cdm cG cdm cin c0 wceq cX cA wcel cF cA wfn cG cB
      wfn wa cF cdm cG cdm cin c0 wceq cA cB cin c0 wceq cF cA wfn cG cB wfn wa
      cF cdm cG cdm cin cA cB cin c0 cF cA wfn cG cB wfn cF cdm cA cG cdm cB cA
      cF fndm cB cG fndm ineqan12d eqeq1d biimprd adantrd 3impia cX cF cG fvun
      syl21anc cF cA wfn cG cB wfn cA cB cin c0 wceq cX cA wcel wa w3a cX cF
      cfv cX cG cfv cun cX cF cfv c0 cun cX cF cfv cF cA wfn cG cB wfn cA cB
      cin c0 wceq cX cA wcel wa w3a cX cG cfv c0 cX cF cfv cF cA wfn cG cB wfn
      cA cB cin c0 wceq cX cA wcel wa w3a cX cG cdm wcel wn cX cG cfv c0 wceq
      cG cB wfn cA cB cin c0 wceq cX cA wcel wa cX cG cdm wcel wn cF cA wfn cG
      cB wfn cA cB cin c0 wceq cX cA wcel wa wa cX cG cdm wcel cX cB wcel cA cB
      cin c0 wceq cX cA wcel wa cX cB wcel wn cG cB wfn cA cB cX disjel adantl
      cG cB wfn cX cG cdm wcel cX cB wcel wb cA cB cin c0 wceq cX cA wcel wa cG
      cB wfn cG cdm cB cX cB cG fndm eleq2d adantr mtbird 3adant1 cX cG ndmfv
      syl uneq2d cX cF cfv un0 syl6eq eqtrd $.
  $}

  $( The value of a union when the argument is in the second domain.
     (Contributed by Scott Fenton, 29-Jun-2013.) $)
  fvun2 $p |- ( ( F Fn A /\ G Fn B /\ ( ( A i^i B ) = (/) /\ X e. B ) ) ->
    ( ( F u. G ) ` X ) = ( G ` X ) ) $=
    cF cA wfn cG cB wfn cA cB cin c0 wceq cX cB wcel wa w3a cX cF cG cun cfv cX
    cG cF cun cfv cX cG cfv cX cF cG cun cG cF cun cF cG uncom fveq1i cG cB wfn
    cF cA wfn cA cB cin c0 wceq cX cB wcel wa cX cG cF cun cfv cX cG cfv wceq
    cA cB cin c0 wceq cX cB wcel wa cG cB wfn cF cA wfn cB cA cin c0 wceq cX cB
    wcel wa cX cG cF cun cfv cX cG cfv wceq cA cB cin c0 wceq cB cA cin c0 wceq
    cX cB wcel cA cB cin cB cA cin c0 cA cB incom eqeq1i anbi1i cB cA cG cF cX
    fvun1 syl3an3b 3com12 syl5eq $.

  ${
    $d x y z A $.  $d x y z F $.
    $( Alternate definition of function value ~ df-fv that doesn't require
       dummy variables.  (Contributed by NM, 4-Aug-2010.) $)
    dffv2 $p |- ( F ` A ) = U. ( ( F " { A } )
            \ U. U. ( ( ( F |` { A } ) o. `' ( F |` { A } ) ) \ _I ) ) $=
      cF cA csn cres wfun cA cF cfv cF cA csn cima cF cA csn cres cF cA csn
      cres ccnv ccom cid cdif cuni cuni cdif cuni wceq cF cA csn cres wfun cA
      cF cfv cA cF cA csn cres cfv cF cA csn cima cF cA csn cres cF cA csn cres
      ccnv ccom cid cdif cuni cuni cdif cuni cA cvv wcel cA cF cA csn cres cfv
      cA cF cfv wceq cA cvv wcel cA cA csn wcel cA cF cA csn cres cfv cA cF cfv
      wceq cA snidb cA cA csn cF fvres sylbi cA cvv wcel wn cA cF cA csn cres
      cfv c0 cA cF cfv cA cF cA csn cres fvprc cA cF fvprc eqtr4d pm2.61i cF cA
      csn cres wfun cA cF cA csn cres cfv cF cA csn cres cA csn cima cuni cF cA
      csn cima cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni cuni cdif
      cuni cA cF cA csn cres funfv cF cA csn cres wfun cF cA csn cres cA csn
      cima cF cA csn cima cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni
      cuni cdif cF cA csn cres wfun cF cA csn cima cF cA csn cres cF cA csn
      cres ccnv ccom cid cdif cuni cuni cdif cF cA csn cima c0 cdif cF cA csn
      cres cA csn cima cF cA csn cres wfun cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni c0 cF cA csn cima cF cA csn cres wfun cF cA csn
      cres cF cA csn cres ccnv ccom cid cdif cuni cuni c0 cuni c0 cF cA csn
      cres wfun cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni c0 cF cA
      csn cres wfun cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni c0
      cuni c0 cF cA csn cres wfun cF cA csn cres cF cA csn cres ccnv ccom cid
      cdif c0 cF cA csn cres wfun cF cA csn cres cF cA csn cres ccnv ccom cid
      wss cF cA csn cres cF cA csn cres ccnv ccom cid cdif c0 wceq cF cA csn
      cres wfun cF cA csn cres wrel cF cA csn cres cF cA csn cres ccnv ccom cid
      wss cF cA csn cres df-fun simprbi cF cA csn cres cF cA csn cres ccnv ccom
      cid ssdif0 sylib unieqd uni0 syl6eq unieqd uni0 syl6eq difeq2d cF cA csn
      cres cA csn cima cF cA csn cima cF cA csn cima c0 cdif cF cA csn resima
      cF cA csn cima dif0 eqtr4i syl6reqr unieqd eqtrd syl5eqr cF cA csn cres
      wfun wn cA cF cfv c0 cF cA csn cima cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni cdif cuni cA cF nfunsn cF cA csn cres wfun wn cF
      cA csn cima cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni cuni
      cdif cuni c0 cuni c0 cF cA csn cres wfun wn cF cA csn cima cF cA csn cres
      cF cA csn cres ccnv ccom cid cdif cuni cuni cdif c0 cF cA csn cres wfun
      wn cA cF cA csn cres cdm wcel cF cA csn cima cF cA csn cres cF cA csn
      cres ccnv ccom cid cdif cuni cuni cdif c0 wceq cF cA csn cres wfun wn cA
      cF cA csn cres cdm wcel cF cA csn cima cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni cdif c0 wceq cF cA csn cres wfun wn cA cF cA csn
      cres cdm wcel wa cF cA csn cima cF cA csn cres cF cA csn cres ccnv ccom
      cid cdif cuni cuni wss cF cA csn cima cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni cdif c0 wceq cF cA csn cres wfun wn cA cF cA csn
      cres cdm wcel wa vy cF cA csn cima cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni cF cA csn cres wfun wn cA cF cA csn cres cdm wcel
      wa cA vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex vy cv cF cA
      csn cima wcel vy cv cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni
      cuni wcel wi cF cA csn cres wfun wn vx cv vz cv cF cA csn cres wbr vz cv
      vy cv wceq wn wa vz wex vx wex cA cF cA csn cres cdm wcel cA vz cv cF cA
      csn cres wbr vz cv vy cv wceq wn wa vz wex cF cA csn cres wfun wn vx cv
      vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex vy wal vx wex vx
      cv vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex vx wex vx cv vz
      cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex vy wal vx wex cF cA
      csn cres wfun cF cA csn cres wfun vx cv vz cv cF cA csn cres wbr vz cv vy
      cv wceq wi vz wal vy wex vx wal vx cv vz cv cF cA csn cres wbr vz cv vy
      cv wceq wn wa vz wex vy wal wn vx wal vx cv vz cv cF cA csn cres wbr vz
      cv vy cv wceq wn wa vz wex vy wal vx wex wn cF cA csn cres wfun cF cA csn
      cres wrel vx cv vz cv cF cA csn cres wbr vz cv vy cv wceq wi vz wal vy
      wex vx wal cF cA csn relres vx vz vy cF cA csn cres dffun3 mpbiran vx cv
      vz cv cF cA csn cres wbr vz cv vy cv wceq wi vz wal vy wex vx cv vz cv cF
      cA csn cres wbr vz cv vy cv wceq wn wa vz wex vy wal wn vx vx cv vz cv cF
      cA csn cres wbr vz cv vy cv wceq wi vz wal vy wex vx cv vz cv cF cA csn
      cres wbr vz cv vy cv wceq wn wa vz wex wn vy wex vx cv vz cv cF cA csn
      cres wbr vz cv vy cv wceq wn wa vz wex vy wal wn vx cv vz cv cF cA csn
      cres wbr vz cv vy cv wceq wi vz wal vx cv vz cv cF cA csn cres wbr vz cv
      vy cv wceq wn wa vz wex wn vy vx cv vz cv cF cA csn cres wbr vz cv vy cv
      wceq wi vz wal vx cv vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa wn
      vz wal vx cv vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex wn vx
      cv vz cv cF cA csn cres wbr vz cv vy cv wceq wi vx cv vz cv cF cA csn
      cres wbr vz cv vy cv wceq wn wa wn vz vx cv vz cv cF cA csn cres wbr vz
      cv vy cv wceq iman albii vx cv vz cv cF cA csn cres wbr vz cv vy cv wceq
      wn wa vz alnex bitri exbii vx cv vz cv cF cA csn cres wbr vz cv vy cv
      wceq wn wa vz wex vy exnal bitri albii vx cv vz cv cF cA csn cres wbr vz
      cv vy cv wceq wn wa vz wex vy wal vx alnex 3bitrri con1bii vx cv vz cv cF
      cA csn cres wbr vz cv vy cv wceq wn wa vz wex vy wal vx cv vz cv cF cA
      csn cres wbr vz cv vy cv wceq wn wa vz wex vx vx cv vz cv cF cA csn cres
      wbr vz cv vy cv wceq wn wa vz wex vy sp eximi sylbi cA cF cA csn cres cdm
      wcel vx cv vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex cA vz
      cv cF cA csn cres wbr vz cv vy cv wceq wn wa vz wex vx cA cF cA csn cres
      cdm wcel vx cv vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa cA vz cv
      cF cA csn cres wbr vz cv vy cv wceq wn wa vz cA cF cA csn cres cdm wcel
      vx cv vz cv cF cA csn cres wbr cA vz cv cF cA csn cres wbr vz cv vy cv
      wceq wn cA cF cA csn cres cdm wcel vx cv vz cv cF cA csn cres wbr cA vz
      cv cF cA csn cres wbr cA cF cA csn cres cdm wcel vx cv vz cv cF cA csn
      cres wbr vx cv vz cv cF cA csn cres wbr cA vz cv cF cA csn cres wbr wi cA
      cF cA csn cres cdm wcel vx cv vz cv cF cA csn cres wbr wa vx cv vz cv cF
      cA csn cres wbr cA vz cv cF cA csn cres wbr cA cF cA csn cres cdm wcel vx
      cv vz cv cF cA csn cres wbr wa vx cv cA vz cv cF cA csn cres cA cF cA csn
      cres cdm wcel cF cA csn cres cdm cA csn wceq vx cv cF cA csn cres cdm
      wcel vx cv cA wceq vx cv vz cv cF cA csn cres wbr cA cF cA csn cres cdm
      wcel cA csn cF cA csn cres cdm wss cF cA csn cres cdm cA csn wceq cA cF
      cA csn cres cdm snssi cA csn cF cA csn cres cdm wss cF cA csn cres cdm cF
      cA csn cres cA csn cres cdm cA csn cF cA csn cres cA csn cres cF cA csn
      cres cF cA csn residm dmeqi cA csn cF cA csn cres cdm wss cF cA csn cres
      cA csn cres cdm cA csn wceq cA csn cF cA csn cres ssdmres biimpi syl5eqr
      syl vx cv vz cv cF cA csn cres vx vex vz vex breldm cF cA csn cres cdm cA
      csn wceq vx cv cF cA csn cres cdm wcel vx cv cA wceq cF cA csn cres cdm
      cA csn wceq vx cv cF cA csn cres cdm wcel vx cv cA csn wcel vx cv cA wceq
      cF cA csn cres cdm cA csn vx cv eleq2 vx cA elsn syl6bb biimpa syl2an
      breq1d biimpd ex pm2.43d anim1d eximdv exlimdv mpan9 cA vz cv cF cA csn
      cres wbr vz cv vy cv wceq wn wa vy cv cF cA csn cima wcel vy cv cF cA csn
      cres cF cA csn cres ccnv ccom cid cdif cuni cuni wcel wi vz vy cv cF cA
      csn cima wcel cA vy cv cF cA csn cres wbr cA vz cv cF cA csn cres wbr vz
      cv vy cv wceq wn wa vy cv cF cA csn cres cF cA csn cres ccnv ccom cid
      cdif cuni cuni wcel vy cv cF cA csn cima wcel vy cv cF cA csn cres cA csn
      cima wcel cA vy cv cF cA csn cres wbr cF cA csn cres cA csn cima cF cA
      csn cima vy cv cF cA csn resima eleq2i cF cA csn cres cA vy cv elimasni
      sylbir cA vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa cA vy cv cF cA
      csn cres wbr vy cv cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni
      cuni wcel cA vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa cA vy cv cF
      cA csn cres wbr wa vy cv cF cA csn cres cF cA csn cres ccnv ccom cid cdif
      cuni cuni wcel vz cv cF cA csn cres cF cA csn cres ccnv ccom cid cdif
      cuni cuni wcel cA vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa cA vy
      cv cF cA csn cres wbr wa vy cv vz cv cpr cF cA csn cres cF cA csn cres
      ccnv ccom cid cdif cuni cuni wss vy cv cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni wcel vz cv cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni wcel wa cA vz cv cF cA csn cres wbr vz cv vy cv
      wceq wn wa cA vy cv cF cA csn cres wbr wa vy cv vz cv cpr vy cv vz cv cop
      cuni cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni cuni vy cv vz
      cv vy vex vz vex uniop cA vz cv cF cA csn cres wbr vz cv vy cv wceq wn wa
      cA vy cv cF cA csn cres wbr wa vy cv vz cv cop cF cA csn cres cF cA csn
      cres ccnv ccom cid cdif cuni wss vy cv vz cv cop cuni cF cA csn cres cF
      cA csn cres ccnv ccom cid cdif cuni cuni wss cA vz cv cF cA csn cres wbr
      vz cv vy cv wceq wn wa cA vy cv cF cA csn cres wbr wa vy cv vz cv cop vy
      cv vz cv cop csn cuni cF cA csn cres cF cA csn cres ccnv ccom cid cdif
      cuni vy cv vz cv cop vy cv vz cv opex unisn cA vz cv cF cA csn cres wbr
      vz cv vy cv wceq wn wa cA vy cv cF cA csn cres wbr wa vy cv vz cv cop cF
      cA csn cres cF cA csn cres ccnv ccom cid cdif wcel vy cv vz cv cop csn cF
      cA csn cres cF cA csn cres ccnv ccom cid cdif wss vy cv vz cv cop csn
      cuni cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni wss cA vz cv
      cF cA csn cres wbr vz cv vy cv wceq wn wa cA vy cv cF cA csn cres wbr wa
      vy cv vx cv cF cA csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx
      cvv wrex vz cv vy cv wceq wn wa vy cv vz cv cop cF cA csn cres cF cA csn
      cres ccnv ccom cid cdif wcel cA vz cv cF cA csn cres wbr cA vy cv cF cA
      csn cres wbr vz cv vy cv wceq wn vy cv vx cv cF cA csn cres ccnv wbr vx
      cv vz cv cF cA csn cres wbr wa vx cvv wrex vz cv vy cv wceq wn wa cA vz
      cv cF cA csn cres wbr cA vy cv cF cA csn cres wbr wa vy cv vx cv cF cA
      csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx cvv wrex vz cv vy
      cv wceq wn cA vz cv cF cA csn cres wbr cA vy cv cF cA csn cres wbr vy cv
      cA cF cA csn cres ccnv wbr vy cv vx cv cF cA csn cres ccnv wbr vx cv vz
      cv cF cA csn cres wbr wa vx cvv wrex cA vz cv cF cA csn cres wbr vy cv cA
      cF cA csn cres ccnv wbr cA vy cv cF cA csn cres wbr cA vz cv cF cA csn
      cres wbr vy cv cvv wcel cA cvv wcel vy cv cA cF cA csn cres ccnv wbr cA
      vy cv cF cA csn cres wbr wb vy vex cA vz cv cF cA csn cres cF cA csn
      relres brrelexi vy cv cA cvv cvv cF cA csn cres brcnvg sylancr biimpar vy
      cv cA cF cA csn cres ccnv wbr cA vz cv cF cA csn cres wbr vy cv vx cv cF
      cA csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx cvv wrex cA cvv
      wcel vy cv cA cF cA csn cres ccnv wbr cA vz cv cF cA csn cres wbr wa vy
      cv vx cv cF cA csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx cvv
      wrex cA vz cv cF cA csn cres wbr cA cvv wcel vy cv cA cF cA csn cres ccnv
      wbr cA vz cv cF cA csn cres cF cA csn relres brrelexi adantl vy cv vx cv
      cF cA csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vy cv cA cF cA
      csn cres ccnv wbr cA vz cv cF cA csn cres wbr wa vx cA cvv vx cv cA wceq
      vy cv vx cv cF cA csn cres ccnv wbr vy cv cA cF cA csn cres ccnv wbr vx
      cv vz cv cF cA csn cres wbr cA vz cv cF cA csn cres wbr vx cv cA vy cv cF
      cA csn cres ccnv breq2 vx cv cA vz cv cF cA csn cres breq1 anbi12d rspcev
      mpancom ancoms syldan anim1i an32s vy cv vz cv cop cF cA csn cres cF cA
      csn cres ccnv ccom cid cdif wcel vy cv vz cv cop cF cA csn cres cF cA csn
      cres ccnv ccom wcel vy cv vz cv cop cid wcel wn wa vy cv vx cv cF cA csn
      cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx cvv wrex vz cv vy cv
      wceq wn wa vy cv vz cv cop cF cA csn cres cF cA csn cres ccnv ccom cid
      eldif vy cv vz cv cop cF cA csn cres cF cA csn cres ccnv ccom wcel vy cv
      vx cv cF cA csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx cvv
      wrex vy cv vz cv cop cid wcel wn vz cv vy cv wceq wn vy cv vx cv cF cA
      csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx cvv wrex vy cv vx
      cv cF cA csn cres ccnv wbr vx cv vz cv cF cA csn cres wbr wa vx wex vy cv
      vz cv cF cA csn cres cF cA csn cres ccnv ccom wbr vy cv vz cv cop cF cA
      csn cres cF cA csn cres ccnv ccom wcel vy cv vx cv cF cA csn cres ccnv
      wbr vx cv vz cv cF cA csn cres wbr wa vx rexv vx vy cv vz cv cF cA csn
      cres cF cA csn cres ccnv vy vex vz vex brco vy cv vz cv cF cA csn cres cF
      cA csn cres ccnv ccom df-br 3bitr2ri vy cv vz cv cop cid wcel vz cv vy cv
      wceq vy cv vz cv cid wbr vy cv vz cv wceq vy cv vz cv cop cid wcel vz cv
      vy cv wceq vy cv vz cv vz vex ideq vy cv vz cv cid df-br vy vz equcom
      3bitr3i notbii anbi12i bitr2i sylib vy cv vz cv cop cF cA csn cres cF cA
      csn cres ccnv ccom cid cdif snssi vy cv vz cv cop csn cF cA csn cres cF
      cA csn cres ccnv ccom cid cdif uniss 3syl syl5eqssr vy cv vz cv cop cF cA
      csn cres cF cA csn cres ccnv ccom cid cdif cuni uniss syl syl5eqssr vy cv
      vz cv cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni cuni vy vex
      vz vex prss sylibr simpld ex syl5 exlimiv syl ssrdv cF cA csn cima cF cA
      csn cres cF cA csn cres ccnv ccom cid cdif cuni cuni ssdif0 sylib ex cA
      cF cA csn cres cdm wcel wn cF cA csn cima cF cA csn cres cF cA csn cres
      ccnv ccom cid cdif cuni cuni cdif c0 cF cA csn cres cF cA csn cres ccnv
      ccom cid cdif cuni cuni cdif c0 cA cF cA csn cres cdm wcel wn cF cA csn
      cima c0 cF cA csn cres cF cA csn cres ccnv ccom cid cdif cuni cuni cA cF
      cA csn cres cdm wcel wn cF cA csn cima cF cA csn cres cA csn cima c0 cF
      cA csn resima cA cF cA csn cres ndmima syl5eqr difeq1d cF cA csn cres cF
      cA csn cres ccnv ccom cid cdif cuni cuni 0dif syl6eq pm2.61d1 unieqd uni0
      syl6eq eqtr4d pm2.61i $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d x y G $.  $d x X $.
    $( Domains of a function composition.  (Contributed by NM, 27-Jan-1997.) $)
    dmfco $p |- ( ( Fun G /\ A e. dom G ) ->
               ( A e. dom ( F o. G ) <-> ( G ` A ) e. dom F ) ) $=
      cG wfun cA cG cdm wcel wa cA cF cG ccom cdm wcel cA vx cv cop cG wcel vx
      cv vy cv cop cF wcel wa vx wex vy wex cA cG cfv cF cdm wcel cA cG cdm
      wcel cA cF cG ccom cdm wcel cA vx cv cop cG wcel vx cv vy cv cop cF wcel
      wa vx wex vy wex wb cG wfun cA cG cdm wcel cA cF cG ccom cdm wcel cA vy
      cv cop cF cG ccom wcel vy wex cA vx cv cop cG wcel vx cv vy cv cop cF
      wcel wa vx wex vy wex vy cA cF cG ccom cG cdm eldm2g cA cG cdm wcel cA vy
      cv cop cF cG ccom wcel cA vx cv cop cG wcel vx cv vy cv cop cF wcel wa vx
      wex vy cA cG cdm wcel vy cv cvv wcel cA vy cv cop cF cG ccom wcel cA vx
      cv cop cG wcel vx cv vy cv cop cF wcel wa vx wex wb vy vex vx cA vy cv cF
      cG cG cdm cvv opelco2g mpan2 exbidv bitrd adantl cA cG cfv cF cdm wcel cA
      cG cfv vy cv cop cF wcel vy wex cG wfun cA cG cdm wcel wa cA vx cv cop cG
      wcel vx cv vy cv cop cF wcel wa vx wex vy wex vy cA cG cfv cF cA cG fvex
      eldm2 cG wfun cA cG cdm wcel wa cA cG cfv vy cv cop cF wcel cA vx cv cop
      cG wcel vx cv vy cv cop cF wcel wa vx wex vy cA cG cfv vy cv cop cF wcel
      vx cv cA cG cfv wceq vx cv vy cv cop cF wcel wa vx wex cG wfun cA cG cdm
      wcel wa cA vx cv cop cG wcel vx cv vy cv cop cF wcel wa vx wex vx cv vy
      cv cop cF wcel cA cG cfv vy cv cop cF wcel vx cA cG cfv cA cG fvex vx cv
      cA cG cfv wceq vx cv vy cv cop cA cG cfv vy cv cop cF vx cv cA cG cfv vy
      cv opeq1 eleq1d ceqsexv cG wfun cA cG cdm wcel wa vx cv cA cG cfv wceq vx
      cv vy cv cop cF wcel wa cA vx cv cop cG wcel vx cv vy cv cop cF wcel wa
      vx cG wfun cA cG cdm wcel wa vx cv cA cG cfv wceq cA vx cv cop cG wcel vx
      cv vy cv cop cF wcel vx cv cA cG cfv wceq cA cG cfv vx cv wceq cG wfun cA
      cG cdm wcel wa cA vx cv cop cG wcel vx cv cA cG cfv eqcom cA vx cv cG
      funopfvb syl5bb anbi1d exbidv syl5bbr exbidv syl5bb bitr4d $.

    $( Value of a function composition.  Similar to second part of Theorem 3H
       of [Enderton] p. 47.  (Contributed by NM, 9-Oct-2004.)  (Proof shortened
       by Andrew Salmon, 22-Oct-2011.)  (Revised by Stefan O'Rear,
       16-Oct-2014.) $)
    fvco2 $p |- ( ( G Fn A /\ X e. A ) -> ( ( F o. G ) ` X ) =
          ( F ` ( G ` X ) ) ) $=
      cG cA wfn cX cA wcel wa vx cv cF cG ccom cX csn cima wcel vx cio vx cv cF
      cX cG cfv csn cima wcel vx cio cX cF cG ccom cfv cX cG cfv cF cfv cG cA
      wfn cX cA wcel wa vx cv cF cG ccom cX csn cima wcel vx cv cF cX cG cfv
      csn cima wcel vx cG cA wfn cX cA wcel wa cF cG ccom cX csn cima cF cX cG
      cfv csn cima vx cv cG cA wfn cX cA wcel wa cF cX cG cfv csn cima cF cG cX
      csn cima cima cF cG ccom cX csn cima cG cA wfn cX cA wcel wa cX cG cfv
      csn cG cX csn cima cF cA cX cG fnsnfv imaeq2d cF cG cX csn imaco syl6reqr
      eleq2d iotabidv vx cX cF cG ccom dffv3 vx cX cG cfv cF dffv3 3eqtr4g $.
  $}

  $( Value of a function composition.  Similar to Exercise 5 of [TakeutiZaring]
     p. 28.  (Contributed by NM, 22-Apr-2006.)  (Proof shortened by Mario
     Carneiro, 26-Dec-2014.) $)
  fvco $p |- ( ( Fun G /\ A e. dom G ) ->
               ( ( F o. G ) ` A ) = ( F ` ( G ` A ) ) ) $=
    cG wfun cG cG cdm wfn cA cG cdm wcel cA cF cG ccom cfv cA cG cfv cF cfv
    wceq cG funfn cG cdm cF cG cA fvco2 sylanb $.

  $( Value of a function composition.  (Contributed by NM, 3-Jan-2004.)
     (Revised by Mario Carneiro, 26-Dec-2014.) $)
  fvco3 $p |- ( ( G : A --> B /\ C e. A ) ->
             ( ( F o. G ) ` C ) = ( F ` ( G ` C ) ) ) $=
    cA cB cG wf cG cA wfn cC cA wcel cC cF cG ccom cfv cC cG cfv cF cfv wceq cA
    cB cG ffn cA cF cG cC fvco2 sylan $.

  ${
    fvco4i.a $e |- (/) = ( F ` (/) ) $.
    fvco4i.b $e |- Fun G $.
    $( Conditions for a composition to be expandable without conditions on the
       argument.  (Contributed by Stefan O'Rear, 31-Mar-2015.) $)
    fvco4i $p |- ( ( F o. G ) ` X ) = ( F ` ( G ` X ) ) $=
      cX cG cdm wcel cX cF cG ccom cfv cX cG cfv cF cfv wceq cG cG cdm wfn cX
      cG cdm wcel cX cF cG ccom cfv cX cG cfv cF cfv wceq cG wfun cG cG cdm wfn
      fvco4i.b cG funfn mpbi cG cdm cF cG cX fvco2 mpan cX cG cdm wcel wn c0 c0
      cF cfv cX cF cG ccom cfv cX cG cfv cF cfv fvco4i.a cX cG cdm wcel wn cX
      cF cG ccom cdm wcel wn cX cF cG ccom cfv c0 wceq cX cF cG ccom cdm wcel
      cX cG cdm wcel cF cG ccom cdm cG cdm cX cF cG dmcoss sseli con3i cX cF cG
      ccom ndmfv syl cX cG cdm wcel wn cX cG cfv c0 cF cX cG ndmfv fveq2d
      3eqtr4a pm2.61i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y ch $.
    fvopab3g.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    fvopab3g.3 $e |- ( y = B -> ( ps <-> ch ) ) $.
    fvopab3g.4 $e |- ( x e. C -> E! y ph ) $.
    fvopab3g.5 $e |- F = { <. x , y >. | ( x e. C /\ ph ) } $.
    $( Value of a function given by ordered-pair class abstraction.
       (Contributed by NM, 6-Mar-1996.)  (Revised by Mario Carneiro,
       28-Apr-2015.) $)
    fvopab3g $p |- ( ( A e. C /\ B e. D ) -> ( ( F ` A ) = B <-> ch ) ) $=
      cA cC wcel cB cD wcel wa cA cB cop vx cv cC wcel wph wa vx vy copab wcel
      cA cC wcel wch wa cA cF cfv cB wceq wch vx cv cC wcel wph wa cA cC wcel
      wps wa cA cC wcel wch wa vx vy cA cB cC cD vx cv cA wceq vx cv cC wcel cA
      cC wcel wph wps vx cv cA cC eleq1 fvopab3g.2 anbi12d vy cv cB wceq wps
      wch cA cC wcel fvopab3g.3 anbi2d opelopabg cA cC wcel cA cF cfv cB wceq
      cA cB cop vx cv cC wcel wph wa vx vy copab wcel wb cB cD wcel cA cC wcel
      cA cF cfv cB wceq cA cB cop cF wcel cA cB cop vx cv cC wcel wph wa vx vy
      copab wcel cF cC wfn cA cC wcel cA cF cfv cB wceq cA cB cop cF wcel wb
      wph vx vy cC cF fvopab3g.4 fvopab3g.5 fnopab cC cA cB cF fnopfvb mpan cF
      vx cv cC wcel wph wa vx vy copab cA cB cop fvopab3g.5 eleq2i syl6bb
      adantr cA cC wcel wch cA cC wcel wch wa wb cB cD wcel cA cC wcel wch ibar
      adantr 3bitr4d $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y ch $.
    fvopab3ig.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    fvopab3ig.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    fvopab3ig.3 $e |- ( x e. C -> E* y ph ) $.
    fvopab3ig.4 $e |- F = { <. x , y >. | ( x e. C /\ ph ) } $.
    $( Value of a function given by ordered-pair class abstraction.
       (Contributed by NM, 23-Oct-1999.) $)
    fvopab3ig $p |- ( ( A e. C /\ B e. D ) -> ( ch -> ( F ` A ) = B ) ) $=
      cA cC wcel cB cD wcel wa wch cA cB cop vx cv cC wcel wph wa vx vy copab
      wcel cA cF cfv cB wceq cA cC wcel cB cD wcel wch cA cB cop vx cv cC wcel
      wph wa vx vy copab wcel wi cB cD wcel cA cC wcel wch cA cB cop vx cv cC
      wcel wph wa vx vy copab wcel wi cA cC wcel cB cD wcel cA cC wcel wch cA
      cB cop vx cv cC wcel wph wa vx vy copab wcel cA cC wcel cB cD wcel wa cA
      cB cop vx cv cC wcel wph wa vx vy copab wcel cA cC wcel wch wa vx cv cC
      wcel wph wa cA cC wcel wps wa cA cC wcel wch wa vx vy cA cB cC cD vx cv
      cA wceq vx cv cC wcel cA cC wcel wph wps vx cv cA cC eleq1 fvopab3ig.1
      anbi12d vy cv cB wceq wps wch cA cC wcel fvopab3ig.2 anbi2d opelopabg
      biimpar exp43 pm2.43a imp cA cB cop vx cv cC wcel wph wa vx vy copab wcel
      cA cF cfv cA vx cv cC wcel wph wa vx vy copab cfv cB cA cF vx cv cC wcel
      wph wa vx vy copab fvopab3ig.4 fveq1i vx cv cC wcel wph wa vx vy copab
      wfun cA cB cop vx cv cC wcel wph wa vx vy copab wcel cA vx cv cC wcel wph
      wa vx vy copab cfv cB wceq wi vx cv cC wcel wph wa vx vy copab wfun vx cv
      cC wcel wph wa vy wmo vx vx cv cC wcel wph wa vx vy funopab vx cv cC wcel
      wph wa vy wmo vx cv cC wcel wph vy wmo wi fvopab3ig.3 vx cv cC wcel wph
      vy moanimv mpbir mpgbir cA cB vx cv cC wcel wph wa vx vy copab funopfv
      ax-mp syl5eq syl6 $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x C y $.  $d x D y $.
    fvmptg.1 $e |- ( x = A -> B = C ) $.
    fvmptg.2 $e |- F = ( x e. D |-> B ) $.
    $( Value of a function given in maps-to notation.  (Contributed by NM,
       2-Oct-2007.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    fvmptg $p |- ( ( A e. D /\ C e. R ) -> ( F ` A ) = C ) $=
      cA cD wcel cC cR wcel wa cC cC wceq cA cF cfv cC wceq cC eqid vy cv cB
      wceq vy cv cC wceq cC cC wceq vx vy cA cC cD cR cF vx cv cA wceq cB cC vy
      cv fvmptg.1 eqeq2d vy cv cC cC eqeq1 vy cv cB wceq vy wmo vx cv cD wcel
      vy cB moeq a1i cF vx cD cB cmpt vx cv cD wcel vy cv cB wceq wa vx vy
      copab fvmptg.2 vx vy cD cB df-mpt eqtri fvopab3ig mpi $.

    $( Value of a function given in maps-to notation.  (Contributed by Mario
       Carneiro, 23-Apr-2014.) $)
    fvmpti $p |- ( A e. D -> ( F ` A ) = ( _I ` C ) ) $=
      cA cD wcel cC cvv wcel cA cF cfv cC cid cfv wceq cA cD wcel cC cvv wcel
      wa cA cF cfv cC cC cid cfv vx cA cB cC cD cvv cF fvmptg.1 fvmptg.2 fvmptg
      cC cvv wcel cC cid cfv cC wceq cA cD wcel cC cvv fvi adantl eqtr4d cA cD
      wcel cC cvv wcel wn wa cA cF cfv c0 cC cid cfv cA cD wcel cC cvv wcel wn
      cA cF cfv c0 wceq cA cD wcel cC cvv wcel wn cA cF cdm wcel wn cA cF cfv
      c0 wceq cA cD wcel cA cF cdm wcel cC cvv wcel cA cF cdm wcel cA cD wcel
      cC cvv wcel cB cvv wcel cC cvv wcel vx cA cD cF cdm vx cv cA wceq cB cC
      cvv fvmptg.1 eleq1d vx cD cB cF fvmptg.2 dmmpt elrab2 baib notbid cA cF
      ndmfv syl6bir imp cC cvv wcel wn cC cid cfv c0 wceq cA cD wcel cC cid
      fvprc adantl eqtr4d pm2.61dan $.

    ${
      fvmpt.3 $e |- C e. _V $.
      $( Value of a function given in maps-to notation.  (Contributed by NM,
         17-Aug-2011.) $)
      fvmpt $p |- ( A e. D -> ( F ` A ) = C ) $=
        cA cD wcel cC cvv wcel cA cF cfv cC wceq fvmpt.3 vx cA cB cC cD cvv cF
        fvmptg.1 fvmptg.2 fvmptg mpan2 $.
    $}
  $}

  ${
    $d y A $.  $d y z B $.  $d x y z C $.
    fvmpts.1 $e |- F = ( x e. C |-> B ) $.
    $( Value of a function given in maps-to notation, using explicit class
       substitution.  (Contributed by Scott Fenton, 17-Jul-2013.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
    fvmpts $p |- ( ( A e. C /\ [_ A / x ]_ B e. V ) ->
        ( F ` A ) = [_ A / x ]_ B ) $=
      vy cA vx vy cv cB csb vx cA cB csb cC cV cF vx vy cv cA cB csbeq1 cF vx
      cC cB cmpt vy cC vx vy cv cB csb cmpt fvmpts.1 vx vy cC cB vx vy cv cB
      csb vy cB nfcv vx vy cv cB nfcsb1v vx vy cv cB csbeq1a cbvmpt eqtri
      fvmptg $.
  $}

  ${
    $d x A $.  $d x C $.  $d x D $.  $d x V $.
    fvmpt3.a $e |- ( x = A -> B = C ) $.
    fvmpt3.b $e |- F = ( x e. D |-> B ) $.
    ${
      fvmpt3.c $e |- ( x e. D -> B e. V ) $.
      $( Value of a function given in maps-to notation, with a slightly
         different sethood condition.  (Contributed by Stefan O'Rear,
         30-Jan-2015.) $)
      fvmpt3 $p |- ( A e. D -> ( F ` A ) = C ) $=
        cA cD wcel cC cV wcel cA cF cfv cC wceq cB cV wcel cC cV wcel vx cA cD
        vx cv cA wceq cB cC cV fvmpt3.a eleq1d fvmpt3.c vtoclga vx cA cB cC cD
        cV cF fvmpt3.a fvmpt3.b fvmptg mpdan $.
    $}

    fvmpt3i.c $e |- B e. _V $.
    $( Value of a function given in maps-to notation, with a slightly different
       sethood condition.  (Contributed by Mario Carneiro, 11-Sep-2015.) $)
    fvmpt3i $p |- ( A e. D -> ( F ` A ) = C ) $=
      vx cA cB cC cD cF cvv fvmpt3.a fvmpt3.b cB cvv wcel vx cv cD wcel
      fvmpt3i.c a1i fvmpt3 $.
  $}

  ${
    $d x A $.  $d x C $.  $d x D $.  $d x ph $.
    fvmptd.1 $e |- ( ph -> F = ( x e. D |-> B ) ) $.
    fvmptd.2 $e |- ( ( ph /\ x = A ) -> B = C ) $.
    fvmptd.3 $e |- ( ph -> A e. D ) $.
    fvmptd.4 $e |- ( ph -> C e. V ) $.
    $( Deduction version of ~ fvmpt .  (Contributed by Scott Fenton,
       18-Feb-2013.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    fvmptd $p |- ( ph -> ( F ` A ) = C ) $=
      wph cA cF cfv cA vx cD cB cmpt cfv vx cA cB csb cC wph cA cF vx cD cB
      cmpt fvmptd.1 fveq1d wph cA cD wcel vx cA cB csb cV wcel cA vx cD cB cmpt
      cfv vx cA cB csb wceq fvmptd.3 wph vx cA cB csb cC cV wph vx cA cB cC cD
      fvmptd.3 fvmptd.2 csbied fvmptd.4 eqeltrd vx cA cB cD vx cD cB cmpt cV vx
      cD cB cmpt eqid fvmpts syl2anc wph vx cA cB cC cD fvmptd.3 fvmptd.2
      csbied 3eqtrd $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d y D $.  $d y z F $.
    fvmpt2.1 $e |- F = ( x e. A |-> B ) $.
    $( Value of a function given by the "maps to" notation.  (Contributed by
       Mario Carneiro, 23-Apr-2014.) $)
    fvmpt2i $p |- ( x e. A -> ( F ` x ) = ( _I ` B ) ) $=
      vy vx cv vx vy cv cB csb cB cA cF vy cv vx cv wceq vx vy cv cB csb vx vx
      cv cB csb cB vx vy cv vx cv cB csbeq1 vx cB csbid syl6eq cF vx cA cB cmpt
      vy cA vx vy cv cB csb cmpt fvmpt2.1 vx vy cA cB vx vy cv cB csb vy cB
      nfcv vx vy cv cB nfcsb1v vx vy cv cB csbeq1a cbvmpt eqtri fvmpti $.

    $( Value of a function given by the "maps to" notation.  (Contributed by
       FL, 21-Jun-2010.) $)
    fvmpt2 $p |- ( ( x e. A /\ B e. C ) -> ( F ` x ) = B ) $=
      vx cv cA wcel cB cC wcel vx cv cF cfv cB cid cfv cB vx cA cB cF fvmpt2.1
      fvmpt2i cB cC fvi sylan9eq $.

    $d x y z C $.
    $( If all the values of the mapping are subsets of a class ` C ` , then so
       is any evaluation of the mapping, even if ` D ` is not in the base set
       ` A ` .  (Contributed by Mario Carneiro, 13-Feb-2015.) $)
    fvmptss $p |- ( A. x e. A B C_ C -> ( F ` D ) C_ C ) $=
      cB cC wss vx cA wral cD cF cdm wcel cD cF cfv cC wss cD cF cdm wcel cB cC
      wss vx cA wral cD cA wcel cD cF cfv cC wss cF cdm cA cD vx cA cB cF
      fvmpt2.1 dmmptss sseli cD cA wcel cB cC wss vx cA wral cD cF cfv cC wss
      cB cC wss vx cA wral vy cv cF cfv cC wss wi cB cC wss vx cA wral cD cF
      cfv cC wss wi vy cD cA vy cv cD wceq vy cv cF cfv cC wss cD cF cfv cC wss
      cB cC wss vx cA wral vy cv cD wceq vy cv cF cfv cD cF cfv cC vy cv cD cF
      fveq2 sseq1d imbi2d cB cC wss vx cA wral vx cv cF cfv cC wss wi cB cC wss
      vx cA wral vy cv cF cfv cC wss wi vx vy cv cA vx vy cv nfcv cB cC wss vx
      cA wral vy cv cF cfv cC wss vx cB cC wss vx cA nfra1 vx vy cv cF cfv cC
      vx vy cv cF vx cF vx cA cB cmpt fvmpt2.1 vx cA cB nfmpt1 nfcxfr vx vy cv
      nfcv nffv vx cC nfcv nfss nfim vx cv vy cv wceq vx cv cF cfv cC wss vy cv
      cF cfv cC wss cB cC wss vx cA wral vx cv vy cv wceq vx cv cF cfv vy cv cF
      cfv cC vx cv vy cv cF fveq2 sseq1d imbi2d vx cv cA wcel cB cC wss vx cA
      wral vx cv cF cfv cC wss vx cv cA wcel cB cC wss vx cA wral wa vx cv cF
      cfv cB cC vx cv cF cdm wcel vx cv cF cfv cB wss vx cv cF cdm wcel vx cv
      cA wcel cB cvv wcel wa vx cv cF cfv cB wss cB cvv wcel vx cF cdm cA vx cA
      cB cF fvmpt2.1 dmmpt rabeq2i vx cv cA wcel cB cvv wcel wa vx cv cF cfv cB
      wceq vx cv cF cfv cB wss vx cA cB cvv cF fvmpt2.1 fvmpt2 vx cv cF cfv cB
      eqimss syl sylbi vx cv cF cdm wcel wn vx cv cF cfv c0 cB vx cv cF ndmfv
      c0 cB wss vx cv cF cdm wcel wn cB 0ss a1i eqsstrd pm2.61i cB cC wss vx cA
      wral vx cv cA wcel cB cC wss cB cC wss vx cA rsp impcom syl5ss ex
      vtoclgaf vtoclga impcom sylan2 cB cC wss vx cA wral cD cF cdm wcel wn wa
      cD cF cfv c0 cC cD cF cdm wcel wn cD cF cfv c0 wceq cB cC wss vx cA wral
      cD cF ndmfv adantl c0 cC wss cB cC wss vx cA wral cD cF cdm wcel wn wa cC
      0ss a1i eqsstrd pm2.61dan $.
  $}

  ${
    $d x z $.  $d x y A $.  $d y z B $.  $d y C $.
    fvmptex.1 $e |- F = ( x e. A |-> B ) $.
    fvmptex.2 $e |- G = ( x e. A |-> ( _I ` B ) ) $.
    $( Express a function ` F ` whose value ` B ` may not always be a set in
       terms of another function ` G ` for which sethood is guaranteed.  (Note
       that ` ( _I `` B ) ` is just shorthand for
       ` if ( B e. _V , B , (/) ) ` , and it is always a set by ~ fvex .)  Note
       also that these functions are not the same; wherever ` B ( C ) ` is not
       a set, ` C ` is not in the domain of ` F ` (so it evaluates to the empty
       set), but ` C ` is in the domain of ` G ` , and ` G ( C ) ` is defined
       to be the empty set.  (Contributed by Mario Carneiro, 14-Jul-2013.)
       (Revised by Mario Carneiro, 23-Apr-2014.) $)
    fvmptex $p |- ( F ` C ) = ( G ` C ) $=
      cC cA wcel cC cF cfv cC cG cfv wceq cC cA wcel cC cF cfv vx cC cB csb cid
      cfv cC cG cfv vy cC vx vy cv cB csb vx cC cB csb cA cF vx vy cv cC cB
      csbeq1 cF vx cA cB cmpt vy cA vx vy cv cB csb cmpt fvmptex.1 vx vy cA cB
      vx vy cv cB csb vy cB nfcv vx vy cv cB nfcsb1v vx vy cv cB csbeq1a cbvmpt
      eqtri fvmpti vy cC vx vy cv cB csb cid cfv vx cC cB csb cid cfv cA cG vy
      cv cC wceq vx vy cv cB csb vx cC cB csb cid vx vy cv cC cB csbeq1 fveq2d
      cG vx cA cB cid cfv cmpt vy cA vx vy cv cB csb cid cfv cmpt fvmptex.2 vx
      vy cA cB cid cfv vx vy cv cB csb cid cfv vy cB cid cfv nfcv vx vx vy cv
      cB csb cid vx cid nfcv vx vy cv cB nfcsb1v nffv vx cv vy cv wceq cB vx vy
      cv cB csb cid vx vy cv cB csbeq1a fveq2d cbvmpt eqtri vx cC cB csb cid
      fvex fvmpt eqtr4d cC cA wcel wn cC cF cfv c0 cC cG cfv cC cA wcel wn cC
      cF cdm wcel wn cC cF cfv c0 wceq cC cF cdm wcel cC cA wcel cF cdm cA cC
      vx cA cB cF fvmptex.1 dmmptss sseli con3i cC cF ndmfv syl cC cA wcel cC
      cG cdm wcel cC cG cfv c0 wceq cG cdm cA cC vx cA cB cid cfv cG cB cid
      fvex fvmptex.2 dmmpti eleq2i cC cG ndmfv sylnbir eqtr4d pm2.61i $.
  $}

  ${
    $d x A $.  $d x D $.  $d x ph $.
    fvmptdf.1 $e |- ( ph -> A e. D ) $.
    fvmptdf.2 $e |- ( ( ph /\ x = A ) -> B e. V ) $.
    fvmptdf.3 $e |- ( ( ph /\ x = A ) -> ( ( F ` A ) = B -> ps ) ) $.
    ${
      fvmptdf.4 $e |- F/_ x F $.
      fvmptdf.5 $e |- F/ x ps $.
      $( Alternate deduction version of ~ fvmpt , suitable for iteration.
         (Contributed by Mario Carneiro, 7-Jan-2017.) $)
      fvmptdf $p |- ( ph -> ( F = ( x e. D |-> B ) -> ps ) ) $=
        wph vx cv cA wceq vx wex cF vx cD cB cmpt wceq wps wi wph cA cvv wcel
        vx cv cA wceq vx wex wph cA cD wcel cA cvv wcel fvmptdf.1 cA cD elex
        syl vx cA isset sylib wph vx cv cA wceq cF vx cD cB cmpt wceq wps wi vx
        wph vx nfv cF vx cD cB cmpt wceq wps vx vx cF vx cD cB cmpt fvmptdf.4
        vx cD cB nfmpt1 nfeq fvmptdf.5 nfim wph vx cv cA wceq cF vx cD cB cmpt
        wceq wps wi cF vx cD cB cmpt wceq cA cF cfv cA vx cD cB cmpt cfv wceq
        wph vx cv cA wceq wa wps cA cF vx cD cB cmpt fveq1 wph vx cv cA wceq wa
        cA cF cfv cA vx cD cB cmpt cfv wceq cA cF cfv cB wceq wps wph vx cv cA
        wceq wa cA vx cD cB cmpt cfv cB cA cF cfv wph vx cv cA wceq wa vx cv vx
        cD cB cmpt cfv cA vx cD cB cmpt cfv cB wph vx cv cA wceq wa vx cv cA vx
        cD cB cmpt wph vx cv cA wceq simpr fveq2d wph vx cv cA wceq wa vx cv cD
        wcel cB cV wcel vx cv vx cD cB cmpt cfv cB wceq wph vx cv cA wceq wa vx
        cv cA cD wph vx cv cA wceq simpr wph cA cD wcel vx cv cA wceq fvmptdf.1
        adantr eqeltrd fvmptdf.2 vx cD cB cV vx cD cB cmpt vx cD cB cmpt eqid
        fvmpt2 syl2anc eqtr3d eqeq2d fvmptdf.3 sylbid syl5 ex exlimd mpd $.
    $}

    $d x F $.  $d x ps $.
    $( Alternate deduction version of ~ fvmpt , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) $)
    fvmptdv $p |- ( ph -> ( F = ( x e. D |-> B ) -> ps ) ) $=
      wph wps vx cA cB cD cF cV fvmptdf.1 fvmptdf.2 fvmptdf.3 vx cF nfcv wps vx
      nfv fvmptdf $.
  $}

  ${
    $d x A $.  $d x C $.  $d x D $.  $d x ph $.
    fvmptdv2.1 $e |- ( ph -> A e. D ) $.
    fvmptdv2.2 $e |- ( ( ph /\ x = A ) -> B e. V ) $.
    fvmptdv2.3 $e |- ( ( ph /\ x = A ) -> B = C ) $.
    $( Alternate deduction version of ~ fvmpt , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) $)
    fvmptdv2 $p |- ( ph -> ( F = ( x e. D |-> B ) -> ( F ` A ) = C ) ) $=
      wph cA cF cfv cC wceq cF vx cD cB cmpt wceq cA vx cD cB cmpt cfv cC wceq
      wph vx cA cB cC cD vx cD cB cmpt cvv wph vx cD cB cmpt eqidd fvmptdv2.3
      fvmptdv2.1 wph vx cv cA wceq vx wex cC cvv wcel wph cA cvv wcel vx cv cA
      wceq vx wex wph cA cD wcel cA cvv wcel fvmptdv2.1 cA cD elex syl vx cA
      isset sylib wph vx cv cA wceq cC cvv wcel vx wph vx cv cA wceq cC cvv
      wcel wph vx cv cA wceq wa cB cC cvv fvmptdv2.3 wph vx cv cA wceq wa cB cV
      wcel cB cvv wcel fvmptdv2.2 cB cV elex syl eqeltrrd ex exlimdv mpd fvmptd
      cF vx cD cB cmpt wceq cA cF cfv cA vx cD cB cmpt cfv cC cA cF vx cD cB
      cmpt fveq1 eqeq1d syl5ibrcom $.
  $}

  ${
    $d x y A $.  $d y B $.  $d y C $.
    $( Bidirectional equality theorem for a mapping abstraction.  Equivalent to
       ~ eqfnfv .  (Contributed by Mario Carneiro, 14-Nov-2014.) $)
    mpteqb $p |- ( A. x e. A B e. V ->
      ( ( x e. A |-> B ) = ( x e. A |-> C ) <->
        A. x e. A B = C ) ) $=
      cB cV wcel vx cA wral cB cvv wcel vx cA wral vx cA cB cmpt vx cA cC cmpt
      wceq cB cC wceq vx cA wral wb cB cV wcel cB cvv wcel vx cA cB cV elex
      ralimi cB cvv wcel vx cA wral vx cA cB cmpt vx cA cC cmpt wceq cB cC wceq
      vx cA wral vx cA cB cmpt vx cA cC cmpt wceq cB cvv wcel vx cA wral cB cC
      wceq vx cA wral vx cA cB cmpt vx cA cC cmpt wceq cB cvv wcel vx cA wral
      cC cvv wcel vx cA wral cB cC wceq vx cA wral vx cA cB cmpt vx cA cC cmpt
      wceq cB cvv wcel vx cA wral cC cvv wcel vx cA wral vx cA cB cmpt vx cA cC
      cmpt wceq vx cA cB cmpt cA wfn vx cA cC cmpt cA wfn cB cvv wcel vx cA
      wral cC cvv wcel vx cA wral cA vx cA cB cmpt vx cA cC cmpt fneq1 vx cA cB
      vx cA cB cmpt vx cA cB cmpt eqid mptfng vx cA cC vx cA cC cmpt vx cA cC
      cmpt eqid mptfng 3bitr4g biimpd vx cA cB cmpt vx cA cC cmpt wceq cB cvv
      wcel vx cA wral cC cvv wcel vx cA wral cB cC wceq vx cA wral cB cvv wcel
      vx cA wral cC cvv wcel vx cA wral wa cB cvv wcel cC cvv wcel wa vx cA
      wral vx cA cB cmpt vx cA cC cmpt wceq cB cC wceq vx cA wral cB cvv wcel
      cC cvv wcel vx cA r19.26 vx cA cB cmpt vx cA cC cmpt wceq cB cvv wcel cC
      cvv wcel wa cB cC wceq wi vx cA wral cB cvv wcel cC cvv wcel wa vx cA
      wral cB cC wceq vx cA wral wi vx cA cB cmpt vx cA cC cmpt wceq cB cvv
      wcel cC cvv wcel wa cB cC wceq wi vx cA vx vx cA cB cmpt vx cA cC cmpt vx
      cA cB nfmpt1 vx cA cC nfmpt1 nfeq vx cA cB cmpt vx cA cC cmpt wceq vx cv
      cA wcel cB cvv wcel cC cvv wcel wa cB cC wceq vx cA cB cmpt vx cA cC cmpt
      wceq vx cv cA wcel wa cB cvv wcel cC cvv wcel wa wa vx cv vx cA cB cmpt
      cfv vx cv vx cA cC cmpt cfv cB cC vx cA cB cmpt vx cA cC cmpt wceq vx cv
      cA wcel wa cB cvv wcel cC cvv wcel wa wa vx cv vx cA cB cmpt vx cA cC
      cmpt vx cA cB cmpt vx cA cC cmpt wceq vx cv cA wcel cB cvv wcel cC cvv
      wcel wa simpll fveq1d vx cv cA wcel cB cvv wcel vx cv vx cA cB cmpt cfv
      cB wceq vx cA cB cmpt vx cA cC cmpt wceq cC cvv wcel vx cA cB cvv vx cA
      cB cmpt vx cA cB cmpt eqid fvmpt2 ad2ant2lr vx cv cA wcel cC cvv wcel vx
      cv vx cA cC cmpt cfv cC wceq vx cA cB cmpt vx cA cC cmpt wceq cB cvv wcel
      vx cA cC cvv vx cA cC cmpt vx cA cC cmpt eqid fvmpt2 ad2ant2l 3eqtr3d
      exp31 ralrimi cB cvv wcel cC cvv wcel wa cB cC wceq vx cA ralim syl
      syl5bir exp3a mpdd com12 cA cA wceq cB cC wceq vx cA wral vx cA cB cmpt
      vx cA cC cmpt wceq cA eqid vx cA cB cA cC mpteq12 mpan impbid1 syl $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y D $.
    $( Closed theorem form of ~ fvmpt .  (Contributed by Scott Fenton,
       21-Feb-2013.)  (Revised by Mario Carneiro, 11-Sep-2015.) $)
    fvmptt $p |- ( ( A. x ( x = A -> B = C ) /\
      F = ( x e. D |-> B ) /\ ( A e. D /\ C e. V ) ) -> ( F ` A ) = C ) $=
      vx cv cA wceq cB cC wceq wi vx wal cF vx cD cB cmpt wceq cA cD wcel cC cV
      wcel wa w3a cA cF cfv cA vx cD cB cmpt cfv cC vx cv cA wceq cB cC wceq wi
      vx wal cF vx cD cB cmpt wceq cA cD wcel cC cV wcel wa w3a cA cF vx cD cB
      cmpt vx cv cA wceq cB cC wceq wi vx wal cF vx cD cB cmpt wceq cA cD wcel
      cC cV wcel wa simp2 fveq1d vx cv cA wceq cB cC wceq wi vx wal cA cD wcel
      cC cV wcel wa cA vx cD cB cmpt cfv cC wceq cF vx cD cB cmpt wceq vx cv cA
      wceq cB cC wceq wi vx wal cA cD wcel cC cV wcel cA vx cD cB cmpt cfv cC
      wceq cA cD wcel vx cv cA wceq vx cD wrex vx cv cA wceq cB cC wceq wi vx
      wal cC cV wcel cA vx cD cB cmpt cfv cC wceq wi vx cA cD risset cC cV wcel
      cC cvv wcel vx cv cA wceq cB cC wceq wi vx wal vx cv cA wceq vx cD wrex
      cA vx cD cB cmpt cfv cC wceq cC cV elex vx cv cA wceq cB cC wceq wi vx
      wal vx cv cA wceq cC cvv wcel cA vx cD cB cmpt cfv cC wceq wi vx cD vx cv
      cA wceq cB cC wceq wi vx nfa1 cC cvv wcel cA vx cD cB cmpt cfv cC wceq vx
      cC cvv wcel vx nfv vx cA vx cD cB cmpt cfv cC vx cA vx cD cB cmpt vx cD
      cB nfmpt1 vx cA nfcv nffv nfeq1 nfim vx cv cA wceq cB cC wceq wi vx cv cD
      wcel vx cv cA wceq cC cvv wcel cA vx cD cB cmpt cfv cC wceq wi wi wi vx
      vx cv cA wceq cB cC wceq wi vx cv cA wceq vx cv cD wcel cC cvv wcel cA vx
      cD cB cmpt cfv cC wceq wi vx cv cA wceq cB cC wceq vx cv cD wcel cC cvv
      wcel cA vx cD cB cmpt cfv cC wceq wi wi vx cv cA wceq cB cC wceq vx cv cD
      wcel cC cvv wcel cA vx cD cB cmpt cfv cC wceq vx cv cA wceq cB cC wceq wa
      vx cv cD wcel cC cvv wcel wa wa vx cv vx cD cB cmpt cfv cB cA vx cD cB
      cmpt cfv cC vx cv cA wceq cB cC wceq wa vx cv cD wcel cC cvv wcel wa wa
      vx cv cD wcel cB cvv wcel vx cv vx cD cB cmpt cfv cB wceq vx cv cA wceq
      cB cC wceq wa vx cv cD wcel cC cvv wcel simprl vx cv cA wceq cB cC wceq
      wa vx cv cD wcel cC cvv wcel wa wa cB cC cvv vx cv cA wceq cB cC wceq vx
      cv cD wcel cC cvv wcel wa simplr vx cv cA wceq cB cC wceq wa vx cv cD
      wcel cC cvv wcel simprr eqeltrd vx cD cB cvv vx cD cB cmpt vx cD cB cmpt
      eqid fvmpt2 syl2anc vx cv cA wceq cB cC wceq wa vx cv cD wcel cC cvv wcel
      wa wa vx cv cA vx cD cB cmpt vx cv cA wceq cB cC wceq vx cv cD wcel cC
      cvv wcel wa simpll fveq2d vx cv cA wceq cB cC wceq vx cv cD wcel cC cvv
      wcel wa simplr 3eqtr3d exp43 a2i com23 sps rexlimd syl7 syl5bi imp32
      3adant2 eqtrd $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d x y D $.  $d y F $.
    fvmptf.1 $e |- F/_ x A $.
    fvmptf.2 $e |- F/_ x C $.
    fvmptf.3 $e |- ( x = A -> B = C ) $.
    fvmptf.4 $e |- F = ( x e. D |-> B ) $.
    $( Value of a function given by an ordered-pair class abstraction.  This
       version of ~ fvmptg uses bound-variable hypotheses instead of distinct
       variable conditions.  (Contributed by NM, 8-Nov-2005.)  (Revised by
       Mario Carneiro, 15-Oct-2016.) $)
    fvmptf $p |- ( ( A e. D /\ C e. V ) -> ( F ` A ) = C ) $=
      cA cD wcel cC cV wcel cA cF cfv cC wceq cC cV wcel cC cvv wcel cA cD wcel
      cA cF cfv cC wceq cC cV elex cB cvv wcel vx cv cF cfv cB wceq wi cC cvv
      wcel cA cF cfv cC wceq wi vx cA cD fvmptf.1 cC cvv wcel cA cF cfv cC wceq
      vx vx cC cvv fvmptf.2 nfel1 vx cA cF cfv cC vx cA cF vx cF vx cD cB cmpt
      fvmptf.4 vx cD cB nfmpt1 nfcxfr fvmptf.1 nffv fvmptf.2 nfeq nfim vx cv cA
      wceq cB cvv wcel cC cvv wcel vx cv cF cfv cB wceq cA cF cfv cC wceq vx cv
      cA wceq cB cC cvv fvmptf.3 eleq1d vx cv cA wceq vx cv cF cfv cA cF cfv cB
      cC vx cv cA cF fveq2 fvmptf.3 eqeq12d imbi12d vx cv cD wcel cB cvv wcel
      vx cv cF cfv cB wceq vx cD cB cvv cF fvmptf.4 fvmpt2 ex vtoclgaf syl5 imp
      $.

    $( The value of a function given by an ordered-pair class abstraction is
       the empty set when the class it would otherwise map to is a proper
       class.  This version of ~ fvmptn uses bound-variable hypotheses instead
       of distinct variable conditions.  (Contributed by NM, 21-Oct-2003.)
       (Revised by Mario Carneiro, 11-Sep-2015.) $)
    fvmptnf $p |- ( -. C e. _V -> ( F ` A ) = (/) ) $=
      cC cvv wcel wn cA cF cdm wcel cA cF cfv c0 wceq cA cF cdm wcel cA cD wcel
      cC cvv wcel wn cA cF cfv c0 wceq cF cdm cD cA vx cD cB cF fvmptf.4
      dmmptss sseli cA cD wcel cC cvv wcel wn cA cF cfv c0 wceq cA cD wcel cC
      cvv wcel wn cA cF cfv cC cid cfv c0 cA cD wcel cA cF cfv cA vx cD cB cid
      cfv cmpt cfv cC cid cfv vx cD cB cA cF vx cD cB cid cfv cmpt fvmptf.4 vx
      cD cB cid cfv cmpt eqid fvmptex cA cD wcel cC cid cfv cvv wcel cA vx cD
      cB cid cfv cmpt cfv cC cid cfv wceq cC cid fvex vx cA cB cid cfv cC cid
      cfv cD vx cD cB cid cfv cmpt cvv fvmptf.1 vx cC cid vx cid nfcv fvmptf.2
      nffv vx cv cA wceq cB cC cid fvmptf.3 fveq2d vx cD cB cid cfv cmpt eqid
      fvmptf mpan2 syl5eq cC cid fvprc sylan9eq expcom syl5 cA cF ndmfv
      pm2.61d1 $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y D $.  $d y F $.
    fvmptn.1 $e |- ( x = D -> B = C ) $.
    fvmptn.2 $e |- F = ( x e. A |-> B ) $.
    $( This somewhat non-intuitive theorem tells us the value of its function
       is the empty set when the class ` C ` it would otherwise map to is a
       proper class.  This is a technical lemma that can help eliminate
       redundant sethood antecedents otherwise required by ~ fvmptg .
       (Contributed by NM, 21-Oct-2003.)  (Revised by Mario Carneiro,
       9-Sep-2013.) $)
    fvmptn $p |- ( -. C e. _V -> ( F ` D ) = (/) ) $=
      vx cD cB cC cA cF vx cD nfcv vx cC nfcv fvmptn.1 fvmptn.2 fvmptnf $.

    $( A mapping always evaluates to a subset of the substituted expression in
       the mapping, even if this is a proper class, or we are out of the
       domain.  (Contributed by Mario Carneiro, 13-Feb-2015.) $)
    fvmptss2 $p |- ( F ` D ) C_ C $=
      cD cF cdm wcel cD cF cfv cC wss cD cF cdm wcel cD cA wcel cC cvv wcel wa
      cD cF cfv cC wss cB cvv wcel cC cvv wcel vx cD cA cF cdm vx cv cD wceq cB
      cC cvv fvmptn.1 eleq1d vx cA cB cF fvmptn.2 dmmpt elrab2 cD cA wcel cC
      cvv wcel wa cD cF cfv cC wceq cD cF cfv cC wss vx cD cB cC cA cvv cF
      fvmptn.1 fvmptn.2 fvmptg cD cF cfv cC eqimss syl sylbi cD cF cdm wcel wn
      cD cF cfv c0 cC cD cF ndmfv c0 cC wss cD cF cdm wcel wn cC 0ss a1i
      eqsstrd pm2.61i $.
  $}

  ${
    $d x y A $.
    fvopab4ndm.1 $e |- F = { <. x , y >. | ( x e. A /\ ph ) } $.
    $( Value of a function given by an ordered-pair class abstraction, outside
       of its domain.  (Contributed by NM, 28-Mar-2008.) $)
    fvopab4ndm $p |- ( -. B e. A -> ( F ` B ) = (/) ) $=
      cB cA wcel wn cB cF cdm wcel wn cB cF cfv c0 wceq cB cF cdm wcel cB cA
      wcel cF cdm cA cB cF cdm vx cv cA wcel wph wa vx vy copab cdm cA cF vx cv
      cA wcel wph wa vx vy copab fvopab4ndm.1 dmeqi wph vx vy cA dmopabss
      eqsstri sseli con3i cB cF ndmfv syl $.
  $}

  ${
    $d A x y $.  $d ps x y $.  $d B y $.  $d C x y $.
    fvopab6.1 $e |- F = { <. x , y >. | ( ph /\ y = B ) } $.
    fvopab6.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    fvopab6.3 $e |- ( x = A -> B = C ) $.
    $( Value of a function given by ordered-pair class abstraction.
       (Contributed by Jeff Madsen, 2-Sep-2009.)  (Revised by Mario Carneiro,
       11-Sep-2015.) $)
    fvopab6 $p |- ( ( A e. D /\ C e. R /\ ps ) -> ( F ` A ) = C ) $=
      cA cD wcel cC cR wcel wps cA cF cfv cC wceq cA cD wcel cA cvv wcel cC cR
      wcel wps cA cF cfv cC wceq wi cA cD elex wph vy cv cB wceq wa wps vy cv
      cC wceq wa wps vx vy cA cC cvv cR cF vx cv cA wceq wph wps vy cv cB wceq
      vy cv cC wceq fvopab6.2 vx cv cA wceq cB cC vy cv fvopab6.3 eqeq2d
      anbi12d vy cv cC wceq wps wps vy cv cC wceq wa vy cv cC wceq wps iba
      bicomd wph vy cv cB wceq wa vy wmo vx cv cvv wcel vy cv cB wceq wph vy vy
      cB moeq moani a1i cF wph vy cv cB wceq wa vx vy copab vx cv cvv wcel wph
      vy cv cB wceq wa wa vx vy copab fvopab6.1 wph vy cv cB wceq wa vx cv cvv
      wcel wph vy cv cB wceq wa wa vx vy vx cv cvv wcel wph vy cv cB wceq wa vx
      vex biantrur opabbii eqtri fvopab3ig sylan 3impia $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y F $.  $d x y G $.  $d x ph $.
    $( Equality of functions is determined by their values.  Special case of
       Exercise 4 of [TakeutiZaring] p. 28 (with domain equality omitted).
       (Contributed by NM, 3-Aug-1994.)  (Proof shortened by Andrew Salmon,
       22-Oct-2011.)  (Proof shortened by Mario Carneiro, 31-Aug-2015.) $)
    eqfnfv $p |- ( ( F Fn A /\ G Fn A ) -> ( F = G <->
                 A. x e. A ( F ` x ) = ( G ` x ) ) ) $=
      cF cA wfn cG cA wfn wa cF cG wceq vx cA vx cv cF cfv cmpt vx cA vx cv cG
      cfv cmpt wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral cF cA wfn cF vx
      cA vx cv cF cfv cmpt wceq cG vx cA vx cv cG cfv cmpt wceq cF cG wceq vx
      cA vx cv cF cfv cmpt vx cA vx cv cG cfv cmpt wceq wb cG cA wfn vx cA cF
      dffn5 vx cA cG dffn5 cF vx cA vx cv cF cfv cmpt cG vx cA vx cv cG cfv
      cmpt eqeq12 syl2anb vx cv cF cfv cvv wcel vx cA wral vx cA vx cv cF cfv
      cmpt vx cA vx cv cG cfv cmpt wceq vx cv cF cfv vx cv cG cfv wceq vx cA
      wral wb vx cv cF cfv cvv wcel vx cA vx cv cF fvex rgenw vx cA vx cv cF
      cfv vx cv cG cfv cvv mpteqb ax-mp syl6bb $.

    $( Equality of functions is determined by their values.  Exercise 4 of
       [TakeutiZaring] p. 28.  (Contributed by NM, 3-Aug-1994.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
    eqfnfv2 $p |- ( ( F Fn A /\ G Fn B ) -> ( F = G <->
                 ( A = B /\ A. x e. A ( F ` x ) = ( G ` x ) ) ) ) $=
      cF cA wfn cG cB wfn wa cF cG wceq cA cB wceq cF cG wceq wa cA cB wceq vx
      cv cF cfv vx cv cG cfv wceq vx cA wral wa cF cA wfn cG cB wfn wa cF cG
      wceq cA cB wceq cF cG wceq cF cdm cG cdm wceq cF cA wfn cG cB wfn wa cA
      cB wceq cF cG dmeq cF cA wfn cG cB wfn cF cdm cA cG cdm cB cA cF fndm cB
      cG fndm eqeqan12d syl5ib pm4.71rd cF cA wfn cG cB wfn wa cA cB wceq cF cG
      wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral cF cA wfn cG cB wfn cA cB
      wceq cF cG wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral wb cG cB wfn cA
      cB wceq wa cF cA wfn cG cA wfn cF cG wceq vx cv cF cfv vx cv cG cfv wceq
      vx cA wral wb cA cB wceq cG cA wfn cG cB wfn cA cB cG fneq2 biimparc vx
      cA cF cG eqfnfv sylan2 anassrs pm5.32da bitrd $.

    $d x B $.
    $( Derive equality of functions from equality of their values.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    eqfnfv3 $p |- ( ( F Fn A /\ G Fn B ) -> ( F = G <-> ( B C_ A /\ A. x e. A
                                  ( x e. B /\ ( F ` x ) = ( G ` x ) ) ) ) ) $=
      cF cA wfn cG cB wfn wa cF cG wceq cA cB wceq vx cv cF cfv vx cv cG cfv
      wceq vx cA wral wa cB cA wss vx cv cB wcel vx cv cF cfv vx cv cG cfv wceq
      wa vx cA wral wa vx cA cB cF cG eqfnfv2 cA cB wceq vx cv cF cfv vx cv cG
      cfv wceq vx cA wral wa cB cA wss cA cB wss wa vx cv cF cfv vx cv cG cfv
      wceq vx cA wral wa cB cA wss vx cv cB wcel vx cv cF cfv vx cv cG cfv wceq
      wa vx cA wral wa cA cB wceq cB cA wss cA cB wss wa vx cv cF cfv vx cv cG
      cfv wceq vx cA wral cA cB wceq cA cB wss cB cA wss wa cB cA wss cA cB wss
      wa cA cB eqss cA cB wss cB cA wss ancom bitri anbi1i cB cA wss cA cB wss
      wa vx cv cF cfv vx cv cG cfv wceq vx cA wral wa cB cA wss cA cB wss vx cv
      cF cfv vx cv cG cfv wceq vx cA wral wa wa cB cA wss vx cv cB wcel vx cv
      cF cfv vx cv cG cfv wceq wa vx cA wral wa cB cA wss cA cB wss vx cv cF
      cfv vx cv cG cfv wceq vx cA wral anass cA cB wss vx cv cF cfv vx cv cG
      cfv wceq vx cA wral wa vx cv cB wcel vx cv cF cfv vx cv cG cfv wceq wa vx
      cA wral cB cA wss cA cB wss vx cv cF cfv vx cv cG cfv wceq vx cA wral wa
      vx cv cB wcel vx cA wral vx cv cF cfv vx cv cG cfv wceq vx cA wral wa vx
      cv cB wcel vx cv cF cfv vx cv cG cfv wceq wa vx cA wral cA cB wss vx cv
      cB wcel vx cA wral vx cv cF cfv vx cv cG cfv wceq vx cA wral vx cA cB
      dfss3 anbi1i vx cv cB wcel vx cv cF cfv vx cv cG cfv wceq vx cA r19.26
      bitr4i anbi2i bitri bitri syl6bb $.

    eqfnfvd.1 $e |- ( ph -> F Fn A ) $.
    eqfnfvd.2 $e |- ( ph -> G Fn A ) $.
    eqfnfvd.3 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = ( G ` x ) ) $.
    $( Deduction for equality of functions.  (Contributed by Mario Carneiro,
       24-Jul-2014.) $)
    eqfnfvd $p |- ( ph -> F = G ) $=
      wph cF cG wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral wph vx cv cF cfv
      vx cv cG cfv wceq vx cA eqfnfvd.3 ralrimiva wph cF cA wfn cG cA wfn cF cG
      wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral wb eqfnfvd.1 eqfnfvd.2 vx
      cA cF cG eqfnfv syl2anc mpbird $.
  $}

  ${
    $d x z A $.  $d y z F $.  $d y z G $.  $d x y $.
    eqfnfv2f.1 $e |- F/_ x F $.
    eqfnfv2f.2 $e |- F/_ x G $.
    $( Equality of functions is determined by their values.  Special case of
       Exercise 4 of [TakeutiZaring] p. 28 (with domain equality omitted).
       This version of ~ eqfnfv uses bound-variable hypotheses instead of
       distinct variable conditions.  (Contributed by NM, 29-Jan-2004.) $)
    eqfnfv2f $p |- ( ( F Fn A /\ G Fn A ) -> ( F = G <->
                 A. x e. A ( F ` x ) = ( G ` x ) ) ) $=
      cF cA wfn cG cA wfn wa cF cG wceq vz cv cF cfv vz cv cG cfv wceq vz cA
      wral vx cv cF cfv vx cv cG cfv wceq vx cA wral vz cA cF cG eqfnfv vz cv
      cF cfv vz cv cG cfv wceq vx cv cF cfv vx cv cG cfv wceq vz vx cA vx vz cv
      cF cfv vz cv cG cfv vx vz cv cF eqfnfv2f.1 vx vz cv nfcv nffv vx vz cv cG
      eqfnfv2f.2 vx vz cv nfcv nffv nfeq vx cv cF cfv vx cv cG cfv wceq vz nfv
      vz cv vx cv wceq vz cv cF cfv vx cv cF cfv vz cv cG cfv vx cv cG cfv vz
      cv vx cv cF fveq2 vz cv vx cv cG fveq2 eqeq12d cbvral syl6bb $.
  $}

  ${
    $d F x $.  $d G x $.
    $( Equality of functions is determined by their values.  (Contributed by
       Scott Fenton, 19-Jun-2011.) $)
    eqfunfv $p |- ( ( Fun F /\ Fun G ) -> ( F = G <->
                    ( dom F = dom G /\
                      A. x e. dom F ( F ` x ) = ( G ` x ) ) ) ) $=
      cF wfun cF cF cdm wfn cG cG cdm wfn cF cG wceq cF cdm cG cdm wceq vx cv
      cF cfv vx cv cG cfv wceq vx cF cdm wral wa wb cG wfun cF funfn cG funfn
      vx cF cdm cG cdm cF cG eqfnfv2 syl2anb $.
  $}

  ${
    $d x B $.  $d x F $.  $d x G $.
    $( Equality of restricted functions is determined by their values.
       (Contributed by NM, 3-Aug-1994.) $)
    fvreseq $p |- ( ( ( F Fn A /\ G Fn A ) /\ B C_ A ) ->
         ( ( F |` B ) = ( G |` B ) <-> A. x e. B ( F ` x ) = ( G ` x ) ) ) $=
      cF cA wfn cG cA wfn wa cB cA wss wa cF cB cres cB wfn cG cB cres cB wfn
      wa cF cB cres cG cB cres wceq vx cv cF cfv vx cv cG cfv wceq vx cB wral
      wb cF cA wfn cG cA wfn cB cA wss cF cB cres cB wfn cG cB cres cB wfn wa
      cF cA wfn cB cA wss wa cF cB cres cB wfn cG cA wfn cB cA wss wa cG cB
      cres cB wfn cA cB cF fnssres cA cB cG fnssres anim12i anandirs cF cB cres
      cB wfn cG cB cres cB wfn wa cF cB cres cG cB cres wceq vx cv cF cB cres
      cfv vx cv cG cB cres cfv wceq vx cB wral vx cv cF cfv vx cv cG cfv wceq
      vx cB wral vx cB cF cB cres cG cB cres eqfnfv vx cv cF cB cres cfv vx cv
      cG cB cres cfv wceq vx cv cF cfv vx cv cG cfv wceq vx cB vx cv cB wcel vx
      cv cF cB cres cfv vx cv cF cfv vx cv cG cB cres cfv vx cv cG cfv vx cv cB
      cF fvres vx cv cB cG fvres eqeq12d ralbiia syl6bb syl $.
  $}

  ${
    $d F x y $.  $d G x y $.  $d A x y $.
    $( Two ways to express the locus of differences between two functions.
       (Contributed by Stefan O'Rear, 17-Jan-2015.) $)
    fndmdif $p |- ( ( F Fn A /\ G Fn A ) -> dom ( F \ G ) =
          { x e. A | ( F ` x ) =/= ( G ` x ) } ) $=
      cF cA wfn cG cA wfn wa cA cF cG cdif cdm cin cF cG cdif cdm vx cv cF cfv
      vx cv cG cfv wne vx cA crab cF cA wfn cG cA wfn wa cF cG cdif cdm cA wss
      cA cF cG cdif cdm cin cF cG cdif cdm wceq cF cA wfn cG cA wfn wa cF cdm
      cF cG cdif cdm cA cF cG cdif cF wss cF cG cdif cdm cF cdm wss cF cG difss
      cF cG cdif cF dmss ax-mp cF cA wfn cF cdm cA wceq cG cA wfn cA cF fndm
      adantr syl5sseq cF cG cdif cdm cA dfss1 sylib cF cA wfn cG cA wfn wa vx
      cv cF cfv vx cv cG cfv wne vx cA cF cG cdif cdm vx cv cF cG cdif cdm wcel
      vx cv vy cv cF cG cdif wbr vy wex cF cA wfn cG cA wfn wa vx cv cA wcel wa
      vx cv cF cfv vx cv cG cfv wne vy vx cv cF cG cdif vx vex eldm cF cA wfn
      cG cA wfn wa vx cv cA wcel wa vx cv cF cfv vx cv cG cfv wne vy cv vx cv
      cF cfv wceq vx cv vy cv cG wbr wn wa vy wex vx cv vy cv cF cG cdif wbr vy
      wex cF cA wfn cG cA wfn wa vx cv cA wcel wa vx cv cF cfv vx cv cG cfv wne
      vx cv vx cv cF cfv cG wbr wn vy cv vx cv cF cfv wceq vx cv vy cv cG wbr
      wn wa vy wex cF cA wfn cG cA wfn wa vx cv cA wcel wa vx cv vx cv cF cfv
      cG wbr vx cv cF cfv vx cv cG cfv cG cA wfn vx cv cA wcel vx cv cF cfv vx
      cv cG cfv wceq vx cv vx cv cF cfv cG wbr wb cF cA wfn vx cv cF cfv vx cv
      cG cfv wceq vx cv cG cfv vx cv cF cfv wceq cG cA wfn vx cv cA wcel wa vx
      cv vx cv cF cfv cG wbr vx cv cF cfv vx cv cG cfv eqcom cA vx cv vx cv cF
      cfv cG fnbrfvb syl5bb adantll necon3abid vx cv vy cv cG wbr wn vx cv vx
      cv cF cfv cG wbr wn vy vx cv cF cfv vx cv cF fvex vy cv vx cv cF cfv wceq
      vx cv vy cv cG wbr vx cv vx cv cF cfv cG wbr vy cv vx cv cF cfv vx cv cG
      breq2 notbid ceqsexv syl6bbr cF cA wfn cG cA wfn wa vx cv cA wcel wa vy
      cv vx cv cF cfv wceq vx cv vy cv cG wbr wn wa vx cv vy cv cF cG cdif wbr
      vy cF cA wfn cG cA wfn wa vx cv cA wcel wa vy cv vx cv cF cfv wceq vx cv
      vy cv cG wbr wn wa vx cv vy cv cF wbr vx cv vy cv cG wbr wn wa vx cv vy
      cv cF cG cdif wbr cF cA wfn cG cA wfn wa vx cv cA wcel wa vy cv vx cv cF
      cfv wceq vx cv vy cv cF wbr vx cv vy cv cG wbr wn cF cA wfn vx cv cA wcel
      vy cv vx cv cF cfv wceq vx cv vy cv cF wbr wb cG cA wfn vy cv vx cv cF
      cfv wceq vx cv cF cfv vy cv wceq cF cA wfn vx cv cA wcel wa vx cv vy cv
      cF wbr vy cv vx cv cF cfv eqcom cA vx cv vy cv cF fnbrfvb syl5bb adantlr
      anbi1d vx cv vy cv cF cG brdif syl6bbr exbidv bitr2d syl5bb rabbi2dva
      eqtr3d $.

    $( The difference set between two functions is commutative.  (Contributed
       by Stefan O'Rear, 17-Jan-2015.) $)
    fndmdifcom $p |- ( ( F Fn A /\ G Fn A ) ->
        dom ( F \ G ) = dom ( G \ F ) ) $=
      cF cA wfn cG cA wfn wa vx cv cF cfv vx cv cG cfv wne vx cA crab vx cv cG
      cfv vx cv cF cfv wne vx cA crab cF cG cdif cdm cG cF cdif cdm vx cv cF
      cfv vx cv cG cfv wne vx cv cG cfv vx cv cF cfv wne vx cA vx cv cF cfv vx
      cv cG cfv wne vx cv cG cfv vx cv cF cfv wne wb vx cv cA wcel vx cv cF cfv
      vx cv cG cfv necom a1i rabbiia vx cA cF cG fndmdif cG cA wfn cF cA wfn cG
      cF cdif cdm vx cv cG cfv vx cv cF cfv wne vx cA crab wceq vx cA cG cF
      fndmdif ancoms 3eqtr4a $.

    $( The difference set of two functions is empty if and only if the
       functions are equal.  (Contributed by Stefan O'Rear, 17-Jan-2015.) $)
    fndmdifeq0 $p |- ( ( F Fn A /\ G Fn A ) ->
        ( dom ( F \ G ) = (/) <-> F = G ) ) $=
      cF cA wfn cG cA wfn wa cF cG cdif cdm c0 wceq vx cv cF cfv vx cv cG cfv
      wne vx cA crab c0 wceq cF cG wceq cF cA wfn cG cA wfn wa cF cG cdif cdm
      vx cv cF cfv vx cv cG cfv wne vx cA crab c0 vx cA cF cG fndmdif eqeq1d cF
      cA wfn cG cA wfn wa cF cG wceq vx cv cF cfv vx cv cG cfv wceq vx cA wral
      vx cv cF cfv vx cv cG cfv wne vx cA crab c0 wceq vx cA cF cG eqfnfv vx cv
      cF cfv vx cv cG cfv wne vx cA crab c0 wceq vx cv cF cfv vx cv cG cfv wne
      wn vx cA wral vx cv cF cfv vx cv cG cfv wceq vx cA wral vx cv cF cfv vx
      cv cG cfv wne vx cA rabeq0 vx cv cF cfv vx cv cG cfv wne wn vx cv cF cfv
      vx cv cG cfv wceq vx cA vx cv cF cfv vx cv cG cfv nne ralbii bitri
      syl6rbbr bitrd $.

    $( Two ways to express the locus of equality between two functions.
       (Contributed by Stefan O'Rear, 17-Jan-2015.) $)
    fndmin $p |- ( ( F Fn A /\ G Fn A ) -> dom ( F i^i G ) =
          { x e. A | ( F ` x ) = ( G ` x ) } ) $=
      cF cA wfn cG cA wfn wa cF cG cin cdm vx cv cA wcel vy cv vx cv cF cfv
      wceq wa vx cv cA wcel vy cv vx cv cG cfv wceq wa wa vx vy copab cdm vx cv
      cF cfv vx cv cG cfv wceq vx cA crab cF cA wfn cG cA wfn wa cF cG cin vx
      cv cA wcel vy cv vx cv cF cfv wceq wa vx cv cA wcel vy cv vx cv cG cfv
      wceq wa wa vx vy copab cF cA wfn cG cA wfn wa cF cG cin vx cv cA wcel vy
      cv vx cv cF cfv wceq wa vx vy copab vx cv cA wcel vy cv vx cv cG cfv wceq
      wa vx vy copab cin vx cv cA wcel vy cv vx cv cF cfv wceq wa vx cv cA wcel
      vy cv vx cv cG cfv wceq wa wa vx vy copab cF cA wfn cG cA wfn cF vx cv cA
      wcel vy cv vx cv cF cfv wceq wa vx vy copab cG vx cv cA wcel vy cv vx cv
      cG cfv wceq wa vx vy copab cF cA wfn cF vx cA vx cv cF cfv cmpt vx cv cA
      wcel vy cv vx cv cF cfv wceq wa vx vy copab cF cA wfn cF vx cA vx cv cF
      cfv cmpt wceq vx cA cF dffn5 biimpi vx vy cA vx cv cF cfv df-mpt syl6eq
      cG cA wfn cG vx cA vx cv cG cfv cmpt vx cv cA wcel vy cv vx cv cG cfv
      wceq wa vx vy copab cG cA wfn cG vx cA vx cv cG cfv cmpt wceq vx cA cG
      dffn5 biimpi vx vy cA vx cv cG cfv df-mpt syl6eq ineqan12d vx cv cA wcel
      vy cv vx cv cF cfv wceq wa vx cv cA wcel vy cv vx cv cG cfv wceq wa vx vy
      inopab syl6eq dmeqd vx cv cA wcel vy cv vx cv cF cfv wceq wa vx cv cA
      wcel vy cv vx cv cG cfv wceq wa wa vy wex vx cab vx cv cA wcel vx cv cF
      cfv vx cv cG cfv wceq wa vx cab vx cv cA wcel vy cv vx cv cF cfv wceq wa
      vx cv cA wcel vy cv vx cv cG cfv wceq wa wa vx vy copab cdm vx cv cF cfv
      vx cv cG cfv wceq vx cA crab vx cv cA wcel vy cv vx cv cF cfv wceq wa vx
      cv cA wcel vy cv vx cv cG cfv wceq wa wa vy wex vx cv cA wcel vx cv cF
      cfv vx cv cG cfv wceq wa vx vx cv cA wcel vy cv vx cv cF cfv wceq vy cv
      vx cv cG cfv wceq wa wa vy wex vx cv cA wcel vy cv vx cv cF cfv wceq vy
      cv vx cv cG cfv wceq wa vy wex wa vx cv cA wcel vy cv vx cv cF cfv wceq
      wa vx cv cA wcel vy cv vx cv cG cfv wceq wa wa vy wex vx cv cA wcel vx cv
      cF cfv vx cv cG cfv wceq wa vx cv cA wcel vy cv vx cv cF cfv wceq vy cv
      vx cv cG cfv wceq wa vy 19.42v vx cv cA wcel vy cv vx cv cF cfv wceq vy
      cv vx cv cG cfv wceq wa wa vx cv cA wcel vy cv vx cv cF cfv wceq wa vx cv
      cA wcel vy cv vx cv cG cfv wceq wa wa vy vx cv cA wcel vy cv vx cv cF cfv
      wceq vy cv vx cv cG cfv wceq anandi exbii vy cv vx cv cF cfv wceq vy cv
      vx cv cG cfv wceq wa vy wex vx cv cF cfv vx cv cG cfv wceq vx cv cA wcel
      vy cv vx cv cG cfv wceq vx cv cF cfv vx cv cG cfv wceq vy vx cv cF cfv vx
      cv cF fvex vy cv vx cv cF cfv vx cv cG cfv eqeq1 ceqsexv anbi2i 3bitr3i
      abbii vx cv cA wcel vy cv vx cv cF cfv wceq wa vx cv cA wcel vy cv vx cv
      cG cfv wceq wa wa vx vy dmopab vx cv cF cfv vx cv cG cfv wceq vx cA
      df-rab 3eqtr4i syl6eq $.
  $}

  ${
    $d F x $.  $d G x $.  $d A x $.
    $( Two functions are equal iff their equalizer is the whole domain.
       (Contributed by Stefan O'Rear, 7-Mar-2015.) $)
    fneqeql $p |- ( ( F Fn A /\ G Fn A ) ->
        ( F = G <-> dom ( F i^i G ) = A ) ) $=
      cF cA wfn cG cA wfn wa cF cG wceq vx cv cF cfv vx cv cG cfv wceq vx cA
      crab cA wceq cF cG cin cdm cA wceq cF cA wfn cG cA wfn wa cF cG wceq vx
      cv cF cfv vx cv cG cfv wceq vx cA wral vx cv cF cfv vx cv cG cfv wceq vx
      cA crab cA wceq vx cA cF cG eqfnfv vx cv cF cfv vx cv cG cfv wceq vx cA
      crab cA wceq cA vx cv cF cfv vx cv cG cfv wceq vx cA crab wceq vx cv cF
      cfv vx cv cG cfv wceq vx cA wral vx cv cF cfv vx cv cG cfv wceq vx cA
      crab cA eqcom vx cv cF cfv vx cv cG cfv wceq vx cA rabid2 bitri syl6bbr
      cF cA wfn cG cA wfn wa cF cG cin cdm vx cv cF cfv vx cv cG cfv wceq vx cA
      crab cA vx cA cF cG fndmin eqeq1d bitr4d $.

    $( Two functions are equal iff their equalizer contains the whole domain.
       (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
    fneqeql2 $p |- ( ( F Fn A /\ G Fn A ) ->
        ( F = G <-> A C_ dom ( F i^i G ) ) ) $=
      cF cA wfn cG cA wfn wa cF cG wceq cF cG cin cdm cA wceq cA cF cG cin cdm
      wss cA cF cG fneqeql cF cA wfn cG cA wfn wa cA cF cG cin cdm wss cF cG
      cin cdm cA wss cA cF cG cin cdm wss wa cF cG cin cdm cA wceq cF cA wfn cG
      cA wfn wa cF cG cin cdm cA wss cA cF cG cin cdm wss cF cA wfn cG cA wfn
      wa cF cdm cF cG cin cdm cA cF cG cin cF wss cF cG cin cdm cF cdm wss cF
      cG inss1 cF cG cin cF dmss ax-mp cF cA wfn cF cdm cA wceq cG cA wfn cA cF
      fndm adantr syl5sseq biantrurd cF cG cin cdm cA eqss syl6rbbr bitrd $.

    $( Two functions are equal on a subset iff their equalizer contains that
       subset.  (Contributed by Stefan O'Rear, 7-Mar-2015.) $)
    fnreseql $p |- ( ( F Fn A /\ G Fn A /\ X C_ A ) ->
        ( ( F |` X ) = ( G |` X ) <-> X C_ dom ( F i^i G ) ) ) $=
      cF cA wfn cG cA wfn cX cA wss w3a cF cX cres cG cX cres wceq cF cX cres
      cG cX cres cin cdm cX wceq cX cF cG cin cdm wss cF cA wfn cG cA wfn cX cA
      wss w3a cF cX cres cX wfn cG cX cres cX wfn cF cX cres cG cX cres wceq cF
      cX cres cG cX cres cin cdm cX wceq wb cF cA wfn cX cA wss cF cX cres cX
      wfn cG cA wfn cA cX cF fnssres 3adant2 cG cA wfn cX cA wss cG cX cres cX
      wfn cF cA wfn cA cX cG fnssres 3adant1 cX cF cX cres cG cX cres fneqeql
      syl2anc cF cX cres cG cX cres cin cdm cX wceq cX cF cG cin cdm cin cX
      wceq cX cF cG cin cdm wss cF cX cres cG cX cres cin cdm cX cF cG cin cdm
      cin cX cF cG cin cX cres cdm cF cX cres cG cX cres cin cdm cX cF cG cin
      cdm cin cF cG cin cX cres cF cX cres cG cX cres cin cF cG cX resindir
      dmeqi cF cG cin cX dmres eqtr3i eqeq1i cX cF cG cin cdm df-ss bitr4i
      syl6bb $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( The range of a choice function (a function that chooses an element from
       each member of its domain) is included in the union of its domain.
       (Contributed by NM, 31-Aug-1999.) $)
    chfnrn $p |- ( ( F Fn A /\ A. x e. A ( F ` x ) e. x ) -> ran F C_ U. A ) $=
      cF cA wfn vx cv cF cfv vx cv wcel vx cA wral wa vy cF crn cA cuni cF cA
      wfn vx cv cF cfv vx cv wcel vx cA wral wa vy cv cF crn wcel vy cv vx cv
      wcel vx cA wrex vy cv cA cuni wcel cF cA wfn vy cv cF crn wcel vx cv cF
      cfv vy cv wceq vx cA wrex vx cv cF cfv vx cv wcel vx cA wral vy cv vx cv
      wcel vx cA wrex cF cA wfn vy cv cF crn wcel vx cv cF cfv vy cv wceq vx cA
      wrex vx cA vy cv cF fvelrnb biimpd vx cv cF cfv vx cv wcel vx cA wral vx
      cv cF cfv vy cv wceq vy cv vx cv wcel wi vx cA wral vx cv cF cfv vy cv
      wceq vx cA wrex vy cv vx cv wcel vx cA wrex wi vx cv cF cfv vx cv wcel vx
      cv cF cfv vy cv wceq vy cv vx cv wcel wi vx cA vx cv cF cfv vy cv wceq vx
      cv cF cfv vx cv wcel vy cv vx cv wcel vx cv cF cfv vy cv vx cv eleq1
      biimpcd ralimi vx cv cF cfv vy cv wceq vy cv vx cv wcel vx cA rexim syl
      sylan9 vx vy cv cA eluni2 syl6ibr ssrdv $.
  $}

  ${
    $d x F $.  $d x A $.
    $( Ordered pair with function value.  Part of Theorem 4.3(i) of [Monk1]
       p. 41.  (Contributed by NM, 14-Oct-1996.) $)
    funfvop $p |- ( ( Fun F /\ A e. dom F ) -> <. A , ( F ` A ) >. e. F ) $=
      cF wfun cA cF cdm wcel wa cA cF cfv cA cF cfv wceq cA cA cF cfv cop cF
      wcel cA cF cfv eqid cA cA cF cfv cF funopfvb mpbii $.
  $}

  $( Two ways to say that ` A ` is in the domain of ` F ` .  (Contributed by
     Mario Carneiro, 1-May-2014.) $)
  funfvbrb $p |- ( Fun F -> ( A e. dom F <-> A F ( F ` A ) ) ) $=
    cF wfun cA cF cdm wcel cA cA cF cfv cF wbr cF wfun cA cF cdm wcel wa cA cA
    cF cfv cop cF wcel cA cA cF cfv cF wbr cA cF funfvop cA cA cF cfv cF df-br
    sylibr cF wfun cF wrel cA cA cF cfv cF wbr cA cF cdm wcel cF funrel cA cA
    cF cfv cF releldm sylan impbida $.

  $( A member of a preimage is a function value argument.  (Contributed by NM,
     4-May-2007.) $)
  fvimacnvi $p |- ( ( Fun F /\ A e. ( `' F " B ) ) -> ( F ` A ) e. B ) $=
    cF wfun cA cF ccnv cB cima wcel wa cA cF cfv cB wcel cF cA csn cima cB wss
    cA cF ccnv cB cima wcel cF wfun cA csn cF ccnv cB cima wss cF cA csn cima
    cB wss cA cF ccnv cB cima snssi cA csn cB cF funimass2 sylan2 cA cF cfv cB
    wcel cA cF cfv csn cB wss cF wfun cA cF ccnv cB cima wcel wa cF cA csn cima
    cB wss cA cF cfv cB cA cF fvex snss cF wfun cA cF ccnv cB cima wcel wa cA
    cF cfv csn cF cA csn cima cB cA cF ccnv cB cima wcel cF wfun cA cF cdm wcel
    cA cF cfv csn cF cA csn cima wceq cF ccnv cB cima cF cdm cA cF cB cnvimass
    sseli cF wfun cF cF cdm wfn cA cF cdm wcel cA cF cfv csn cF cA csn cima
    wceq cF funfn cF cdm cA cF fnsnfv sylanb sylan2 sseq1d syl5bb mpbird $.

  $( The argument of a function value belongs to the preimage of any class
     containing the function value.  Raph Levien remarks:  "This proof is
     unsatisfying, because it seems to me that ~ funimass2 could probably be
     strengthened to a biconditional."  (Contributed by Raph Levien,
     20-Nov-2006.) $)
  fvimacnv $p |- ( ( Fun F /\ A e. dom F ) ->
                 ( ( F ` A ) e. B <-> A e. ( `' F " B ) ) ) $=
    cF wfun cA cF cdm wcel wa cA cF cfv cB wcel cA cF ccnv cB cima wcel cF wfun
    cA cF cdm wcel wa cA cF ccnv cA cF cfv csn cima wcel cA cF cfv cB wcel cA
    cF ccnv cB cima wcel cF wfun cA cF cdm wcel wa cA cF ccnv cA cF cfv csn
    cima wcel cA cF cfv cA cop cF ccnv wcel cF wfun cA cF cdm wcel wa cA cF cfv
    cA cop cF ccnv wcel cA cA cF cfv cop cF wcel cA cF funfvop cA cF cdm wcel
    cA cF cfv cA cop cF ccnv wcel cA cA cF cfv cop cF wcel wb cF wfun cA cF cfv
    cvv wcel cA cF cdm wcel cA cF cfv cA cop cF ccnv wcel cA cA cF cfv cop cF
    wcel wb cA cF fvex cA cF cfv cA cvv cF cdm cF opelcnvg mpan adantl mpbird
    cA cF cdm wcel cA cF ccnv cA cF cfv csn cima wcel cA cF cfv cA cop cF ccnv
    wcel wb cF wfun cA cF cfv cvv wcel cA cF cdm wcel cA cF ccnv cA cF cfv csn
    cima wcel cA cF cfv cA cop cF ccnv wcel wb cA cF fvex cF ccnv cA cF cfv cA
    cvv cF cdm elimasng mpan adantl mpbird cA cF cfv cB wcel cF ccnv cA cF cfv
    csn cima cF ccnv cB cima cA cA cF cfv cB wcel cA cF cfv csn cB wss cF ccnv
    cA cF cfv csn cima cF ccnv cB cima wss cA cF cfv cB cA cF fvex snss cA cF
    cfv csn cB cF ccnv imass2 sylbi sseld syl5com cF wfun cA cF ccnv cB cima
    wcel cA cF cfv cB wcel wi cA cF cdm wcel cF wfun cA cF ccnv cB cima wcel cA
    cF cfv cB wcel cA cB cF fvimacnvi ex adantr impbid $.

  ${
    $d F x $.  $d A x $.  $d B x $.
    $( A kind of contraposition law that infers an image subclass from a
       subclass of a preimage.  Raph Levien remarks:  "Likely this could be
       proved directly, and ~ fvimacnv would be the special case of ` A ` being
       a singleton, but it works this way round too."  (Contributed by Raph
       Levien, 20-Nov-2006.) $)
    funimass3 $p |- ( ( Fun F /\ A C_ dom F ) ->
                    ( ( F " A ) C_ B <-> A C_ ( `' F " B ) ) ) $=
      cF wfun cA cF cdm wss wa cF cA cima cB wss vx cv cF ccnv cB cima wcel vx
      cA wral cA cF ccnv cB cima wss cF wfun cA cF cdm wss wa cF cA cima cB wss
      vx cv cF cfv cB wcel vx cA wral vx cv cF ccnv cB cima wcel vx cA wral vx
      cA cB cF funimass4 cF wfun cA cF cdm wss wa vx cv cF cfv cB wcel vx cv cF
      ccnv cB cima wcel vx cA cF wfun cA cF cdm wss vx cv cA wcel vx cv cF cfv
      cB wcel vx cv cF ccnv cB cima wcel wb cA cF cdm wss vx cv cA wcel vx cv
      cF cdm wcel cF wfun vx cv cF cfv cB wcel vx cv cF ccnv cB cima wcel wb cA
      cF cdm vx cv ssel cF wfun vx cv cF cdm wcel vx cv cF cfv cB wcel vx cv cF
      ccnv cB cima wcel wb vx cv cB cF fvimacnv ex syl9r imp31 ralbidva bitrd
      vx cA cF ccnv cB cima dfss3 syl6bbr $.

    $( A subclass of a preimage in terms of function values.  (Contributed by
       NM, 15-May-2007.) $)
    funimass5 $p |- ( ( Fun F /\ A C_ dom F ) ->
                    ( A C_ ( `' F " B ) <-> A. x e. A ( F ` x ) e. B ) ) $=
      cF wfun cA cF cdm wss wa cF cA cima cB wss cA cF ccnv cB cima wss vx cv
      cF cfv cB wcel vx cA wral cA cB cF funimass3 vx cA cB cF funimass4 bitr3d
      $.

    $( Two ways of specifying that a function is constant on a subdomain.
       (Contributed by NM, 8-Mar-2007.) $)
    funconstss $p |- ( ( Fun F /\ A C_ dom F ) ->
                     ( A. x e. A ( F ` x ) = B <-> A C_ ( `' F " { B } ) ) ) $=
      cF wfun cA cF cdm wss wa vx cv cF cfv cB wceq vx cA wral cF cA cima cB
      csn wss cA cF ccnv cB csn cima wss cF wfun cA cF cdm wss wa cF cA cima cB
      csn wss vx cv cF cfv cB csn wcel vx cA wral vx cv cF cfv cB wceq vx cA
      wral vx cA cB csn cF funimass4 vx cv cF cfv cB csn wcel vx cv cF cfv cB
      wceq vx cA vx cv cF cfv cB vx cv cF fvex elsnc ralbii syl6rbb cA cB csn
      cF funimass3 bitrd $.
  $}


  $( Another proof of ~ fvimacnv , based on ~ funimass3 .  If ~ funimass3 is
     ever proved directly, as opposed to using ~ funimacnv pointwise, then the
     proof of ~ funimacnv should be replaced with this one.  (Contributed by
     Raph Levien, 20-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  fvimacnvALT $p |- ( ( Fun F /\ A e. dom F ) ->
                    ( ( F ` A ) e. B <-> A e. ( `' F " B ) ) ) $=
    cF wfun cA cF cdm wcel wa cF cA csn cima cB wss cA csn cF ccnv cB cima wss
    cA cF cfv cB wcel cA cF ccnv cB cima wcel cA cF cdm wcel cF wfun cA csn cF
    cdm wss cF cA csn cima cB wss cA csn cF ccnv cB cima wss wb cA cF cdm snssi
    cA csn cB cF funimass3 sylan2 cA cF cfv cB wcel cA cF cfv csn cB wss cF
    wfun cA cF cdm wcel wa cF cA csn cima cB wss cA cF cfv cB cA cF fvex snss
    cF wfun cA cF cdm wcel wa cA cF cfv csn cF cA csn cima cB cF wfun cF cF cdm
    wfn cA cF cdm wcel cA cF cfv csn cF cA csn cima wceq cF wfun cF cdm cF cdm
    wceq cF cF cdm wfn cF cdm eqid cF cF cdm wfn cF wfun cF cdm cF cdm wceq wa
    cF cF cdm df-fn biimpri mpan2 cF cdm cA cF fnsnfv sylan sseq1d syl5bb cA cF
    cdm wcel cA cF ccnv cB cima wcel cA csn cF ccnv cB cima wss wb cF wfun cA
    cF ccnv cB cima cF cdm snssg adantl 3bitr4d $.

  $( Membership in the preimage of a set under a function.  (Contributed by
     Jeff Madsen, 2-Sep-2009.) $)
  elpreima $p |- ( F Fn A -> ( B e. ( `' F " C )
                              <-> ( B e. A /\ ( F ` B ) e. C ) ) ) $=
    cF cA wfn cB cF ccnv cC cima wcel cB cA wcel cB cF cfv cC wcel wa cF cA wfn
    cB cF ccnv cC cima wcel cB cA wcel cB cF cfv cC wcel cB cF ccnv cC cima
    wcel cB cF cdm wcel cF cA wfn cB cA wcel cF ccnv cC cima cF cdm cB cF cC
    cnvimass sseli cF cA wfn cF cdm cA cB cA cF fndm eleq2d syl5ib cF cA wfn cB
    cF ccnv cC cima wcel cB cF cfv cC wcel cF cA wfn cF wfun cB cF ccnv cC cima
    wcel cB cF cfv cC wcel cA cF fnfun cB cC cF fvimacnvi sylan ex jcad cF cA
    wfn cB cA wcel cB cF cfv cC wcel cB cF ccnv cC cima wcel cF cA wfn cB cA
    wcel wa cB cF cfv cC wcel cB cF ccnv cC cima wcel cB cF cfv cC wcel cB cF
    ccnv cC cima wcel wb cA cB cF cB cC cF fvimacnv funfni biimpd expimpd
    impbid $.

  ${
    $d x B $.  $d x C $.  $d x F $.  $d x V $.
    $( Membership in the preimage of a singleton, under a function.
       (Contributed by Mario Carneiro, 12-May-2014.)  (Proof shortened by Mario
       Carneiro, 28-Apr-2015.) $)
    fniniseg $p |- ( F Fn A -> ( C e. ( `' F " { B } ) <->
                     ( C e. A /\ ( F ` C ) = B ) ) ) $=
      cF cA wfn cC cF ccnv cB csn cima wcel cC cA wcel cC cF cfv cB csn wcel wa
      cC cA wcel cC cF cfv cB wceq wa cA cC cB csn cF elpreima cC cF cfv cB csn
      wcel cC cF cfv cB wceq cC cA wcel cC cF cfv cB cC cF fvex elsnc anbi2i
      syl6bb $.
  $}

  ${
    $d x A $.  $d x F $.  $d x B $.
    $( Inverse images under functions expressed as abstractions.  (Contributed
       by Stefan O'Rear, 1-Feb-2015.) $)
    fncnvima2 $p |- ( F Fn A -> ( `' F " B ) = { x e. A | ( F ` x ) e. B } ) $=
      cF cA wfn cF ccnv cB cima vx cv cA wcel vx cv cF cfv cB wcel wa vx cab vx
      cv cF cfv cB wcel vx cA crab cF cA wfn vx cv cA wcel vx cv cF cfv cB wcel
      wa vx cF ccnv cB cima cA vx cv cB cF elpreima abbi2dv vx cv cF cfv cB
      wcel vx cA df-rab syl6eqr $.

    $( Inverse point images under functions expressed as abstractions.
       (Contributed by Stefan O'Rear, 1-Feb-2015.) $)
    fniniseg2 $p |- ( F Fn A -> ( `' F " { B } ) =
          { x e. A | ( F ` x ) = B } ) $=
      cF cA wfn cF ccnv cB csn cima vx cv cF cfv cB csn wcel vx cA crab vx cv
      cF cfv cB wceq vx cA crab vx cA cB csn cF fncnvima2 vx cv cF cfv cB csn
      wcel vx cv cF cfv cB wceq vx cA vx cv cF cfv cB csn wcel vx cv cF cfv cB
      wceq wb vx cv cA wcel vx cv cF cfv cB vx cv cF fvex elsnc a1i rabbiia
      syl6eq $.

    $( Support sets of functions expressed as abstractions.  (Contributed by
       Stefan O'Rear, 1-Feb-2015.) $)
    fnniniseg2 $p |- ( F Fn A -> ( `' F " ( _V \ { B } ) ) =
          { x e. A | ( F ` x ) =/= B } ) $=
      cF cA wfn cF ccnv cvv cB csn cdif cima vx cv cF cfv cvv cB csn cdif wcel
      vx cA crab vx cv cF cfv cB wne vx cA crab vx cA cvv cB csn cdif cF
      fncnvima2 vx cv cF cfv cvv cB csn cdif wcel vx cv cF cfv cB wne vx cA vx
      cv cF cfv cvv cB csn cdif wcel vx cv cF cfv cB wne wb vx cv cA wcel vx cv
      cF cfv cvv cB csn cdif wcel vx cv cF cfv cvv wcel vx cv cF cfv cB wne vx
      cv cF fvex vx cv cF cfv cvv cB eldifsn mpbiran a1i rabbiia syl6eq $.
  $}

  ${
    $d F x $.  $d A x $.
    $( Existential quantification restricted to a support.  (Contributed by
       Stefan O'Rear, 23-Mar-2015.) $)
    rexsupp $p |- ( F Fn A -> ( E. x e. ( `' F " ( _V \ { Z } ) ) ph <->
          E. x e. A ( ( F ` x ) =/= Z /\ ph ) ) ) $=
      cF cA wfn wph vx cv cF cfv cZ wne wph wa vx cF ccnv cvv cZ csn cdif cima
      cA cF cA wfn vx cv cF ccnv cvv cZ csn cdif cima wcel wph wa vx cv cA wcel
      vx cv cF cfv cZ wne wa wph wa vx cv cA wcel vx cv cF cfv cZ wne wph wa wa
      cF cA wfn vx cv cF ccnv cvv cZ csn cdif cima wcel vx cv cA wcel vx cv cF
      cfv cZ wne wa wph cF cA wfn vx cv cF ccnv cvv cZ csn cdif cima wcel vx cv
      cA wcel vx cv cF cfv cvv cZ csn cdif wcel wa vx cv cA wcel vx cv cF cfv
      cZ wne wa cA vx cv cvv cZ csn cdif cF elpreima vx cv cF cfv cvv cZ csn
      cdif wcel vx cv cF cfv cZ wne vx cv cA wcel vx cv cF cfv cvv cZ csn cdif
      wcel vx cv cF cfv cvv wcel vx cv cF cfv cZ wne vx cv cF fvex vx cv cF cfv
      cvv cZ eldifsn mpbiran anbi2i syl6bb anbi1d vx cv cA wcel vx cv cF cfv cZ
      wne wph anass syl6bb rexbidv2 $.
  $}

  ${
    $d x F $.  $d x A $.  $d x B $.
    $( Preimage of a union.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    unpreima $p |- ( Fun F -> ( `' F " ( A u. B ) )
                                  = ( ( `' F " A ) u. ( `' F " B ) ) ) $=
      cF wfun cF cF cdm wfn cF ccnv cA cB cun cima cF ccnv cA cima cF ccnv cB
      cima cun wceq cF funfn cF cF cdm wfn vx cF ccnv cA cB cun cima cF ccnv cA
      cima cF ccnv cB cima cun cF cF cdm wfn vx cv cF ccnv cA cB cun cima wcel
      vx cv cF cdm wcel vx cv cF cfv cA cB cun wcel wa vx cv cF ccnv cA cima cF
      ccnv cB cima cun wcel cF cdm vx cv cA cB cun cF elpreima cF cF cdm wfn vx
      cv cF ccnv cA cima cF ccnv cB cima cun wcel vx cv cF cdm wcel vx cv cF
      cfv cA wcel wa vx cv cF cdm wcel vx cv cF cfv cB wcel wa wo vx cv cF cdm
      wcel vx cv cF cfv cA cB cun wcel wa vx cv cF ccnv cA cima cF ccnv cB cima
      cun wcel vx cv cF ccnv cA cima wcel vx cv cF ccnv cB cima wcel wo cF cF
      cdm wfn vx cv cF cdm wcel vx cv cF cfv cA wcel wa vx cv cF cdm wcel vx cv
      cF cfv cB wcel wa wo vx cv cF ccnv cA cima cF ccnv cB cima elun cF cF cdm
      wfn vx cv cF ccnv cA cima wcel vx cv cF cdm wcel vx cv cF cfv cA wcel wa
      vx cv cF ccnv cB cima wcel vx cv cF cdm wcel vx cv cF cfv cB wcel wa cF
      cdm vx cv cA cF elpreima cF cdm vx cv cB cF elpreima orbi12d syl5bb vx cv
      cF cdm wcel vx cv cF cfv cA cB cun wcel wa vx cv cF cdm wcel vx cv cF cfv
      cA wcel vx cv cF cfv cB wcel wo wa vx cv cF cdm wcel vx cv cF cfv cA wcel
      wa vx cv cF cdm wcel vx cv cF cfv cB wcel wa wo vx cv cF cfv cA cB cun
      wcel vx cv cF cfv cA wcel vx cv cF cfv cB wcel wo vx cv cF cdm wcel vx cv
      cF cfv cA cB elun anbi2i vx cv cF cdm wcel vx cv cF cfv cA wcel vx cv cF
      cfv cB wcel andi bitri syl6rbbr bitrd eqrdv sylbi $.

    $( Preimage of an intersection.  (Contributed by Jeff Madsen, 2-Sep-2009.)
       (Proof shortened by Mario Carneiro, 14-Jun-2016.) $)
    inpreima $p |- ( Fun F -> ( `' F " ( A i^i B ) )
                                  = ( ( `' F " A ) i^i ( `' F " B ) ) ) $=
      cF wfun cF ccnv ccnv wfun cF ccnv cA cB cin cima cF ccnv cA cima cF ccnv
      cB cima cin wceq cF funcnvcnv cA cB cF ccnv imain syl $.

    $( Preimage of a difference.  (Contributed by Mario Carneiro,
       14-Jun-2016.) $)
    difpreima $p |- ( Fun F -> ( `' F " ( A \ B ) )
                                  = ( ( `' F " A ) \ ( `' F " B ) ) ) $=
      cF wfun cF ccnv ccnv wfun cF ccnv cA cB cdif cima cF ccnv cA cima cF ccnv
      cB cima cdif wceq cF funcnvcnv cA cB cF ccnv imadif syl $.

    $( The preimage of a restricted function.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    respreima $p |- ( Fun F -> ( `' ( F |` B ) " A )
                                    = ( ( `' F " A ) i^i B ) ) $=
      cF wfun vx cF cB cres ccnv cA cima cF ccnv cA cima cB cin cF wfun cF cF
      cdm wfn vx cv cF cB cres ccnv cA cima wcel vx cv cF ccnv cA cima cB cin
      wcel wb cF funfn cF cF cdm wfn vx cv cB cF cdm cin wcel vx cv cF cB cres
      cfv cA wcel wa vx cv cF cdm wcel vx cv cF cfv cA wcel wa vx cv cB wcel wa
      vx cv cF cB cres ccnv cA cima wcel vx cv cF ccnv cA cima cB cin wcel cF
      cF cdm wfn vx cv cB cF cdm cin wcel vx cv cF cB cres cfv cA wcel wa vx cv
      cF cdm wcel vx cv cB wcel wa vx cv cF cfv cA wcel wa vx cv cF cdm wcel vx
      cv cF cfv cA wcel wa vx cv cB wcel wa vx cv cB cF cdm cin wcel vx cv cF
      cB cres cfv cA wcel wa vx cv cF cdm wcel vx cv cB wcel wa vx cv cF cfv cA
      wcel wa wb cF cF cdm wfn vx cv cB cF cdm cin wcel vx cv cF cB cres cfv cA
      wcel wa vx cv cF cdm wcel vx cv cB wcel wa vx cv cF cB cres cfv cA wcel
      wa vx cv cF cdm wcel vx cv cB wcel wa vx cv cF cfv cA wcel wa vx cv cB cF
      cdm cin wcel vx cv cF cdm wcel vx cv cB wcel wa vx cv cF cB cres cfv cA
      wcel vx cv cB cF cdm cin wcel vx cv cB wcel vx cv cF cdm wcel wa vx cv cF
      cdm wcel vx cv cB wcel wa vx cv cB cF cdm elin vx cv cB wcel vx cv cF cdm
      wcel ancom bitri anbi1i vx cv cF cdm wcel vx cv cB wcel wa vx cv cF cB
      cres cfv cA wcel vx cv cF cfv cA wcel vx cv cB wcel vx cv cF cB cres cfv
      cA wcel vx cv cF cfv cA wcel wb vx cv cF cdm wcel vx cv cB wcel vx cv cF
      cB cres cfv vx cv cF cfv cA vx cv cB cF fvres eleq1d adantl pm5.32i bitri
      a1i vx cv cF cdm wcel vx cv cB wcel vx cv cF cfv cA wcel an32 syl6bb cF
      cF cdm wfn cF cB cres cB cF cdm cin wfn vx cv cF cB cres ccnv cA cima
      wcel vx cv cB cF cdm cin wcel vx cv cF cB cres cfv cA wcel wa wb cF cF
      cdm wfn cF cB cres wfun cF cB cres cdm cB cF cdm cin wceq wa cF cB cres
      cB cF cdm cin wfn cF cF cdm wfn cF cB cres wfun cF cB cres cdm cB cF cdm
      cin wceq cF cF cdm wfn cF wfun cF cB cres wfun cF cdm cF fnfun cB cF
      funres syl cF cB dmres jctir cF cB cres cB cF cdm cin df-fn sylibr cB cF
      cdm cin vx cv cA cF cB cres elpreima syl vx cv cF ccnv cA cima cB cin
      wcel vx cv cF ccnv cA cima wcel vx cv cB wcel wa cF cF cdm wfn vx cv cF
      cdm wcel vx cv cF cfv cA wcel wa vx cv cB wcel wa vx cv cF ccnv cA cima
      cB elin cF cF cdm wfn vx cv cF ccnv cA cima wcel vx cv cF cdm wcel vx cv
      cF cfv cA wcel wa vx cv cB wcel cF cdm vx cv cA cF elpreima anbi1d syl5bb
      3bitr4d sylbi eqrdv $.
  $}

  ${
    $d A x y $.  $d B y $.  $d F x y $.
    $( Preimage of an intersection.  (Contributed by FL, 16-Apr-2012.) $)
    iinpreima $p |- ( ( Fun F /\ A =/= (/) )
        -> ( `' F " |^|_ x e. A B ) = |^|_ x e. A ( `' F " B ) ) $=
      cF wfun cA c0 wne wa vy cF ccnv vx cA cB ciin cima vx cA cF ccnv cB cima
      ciin cF wfun cA c0 wne wa vy cv cF ccnv vx cA cB ciin cima wcel vy cv vx
      cA cF ccnv cB cima ciin wcel cF wfun cA c0 wne wa vy cv cF ccnv vx cA cB
      ciin cima wcel wa vy cv cF ccnv cB cima wcel vx cA wral vy cv vx cA cF
      ccnv cB cima ciin wcel cF wfun cA c0 wne wa vy cv cF ccnv vx cA cB ciin
      cima wcel wa cF wfun vy cv cF cdm wcel vy cv cF cfv cB wcel vx cA wral vy
      cv cF ccnv cB cima wcel vx cA wral cF wfun cA c0 wne vy cv cF ccnv vx cA
      cB ciin cima wcel simpll vy cv cF ccnv vx cA cB ciin cima wcel vy cv cF
      cdm wcel cF wfun cA c0 wne wa cF ccnv vx cA cB ciin cima cF cdm vy cv cF
      vx cA cB ciin cnvimass sseli adantl cF wfun cA c0 wne wa vy cv cF ccnv vx
      cA cB ciin cima wcel wa vy cv cF cfv cvv wcel vy cv cF cfv vx cA cB ciin
      wcel vy cv cF cfv cB wcel vx cA wral vy cv cF fvex cF wfun vy cv cF ccnv
      vx cA cB ciin cima wcel vy cv cF cfv vx cA cB ciin wcel cA c0 wne vy cv
      vx cA cB ciin cF fvimacnvi adantlr vy cv cF cfv cvv wcel vy cv cF cfv vx
      cA cB ciin wcel vy cv cF cfv cB wcel vx cA wral vx vy cv cF cfv cA cB cvv
      eliin biimpa sylancr cF wfun vy cv cF cdm wcel wa vy cv cF cfv cB wcel vx
      cA wral vy cv cF ccnv cB cima wcel vx cA wral cF wfun vy cv cF cdm wcel
      wa vy cv cF cfv cB wcel vy cv cF ccnv cB cima wcel vx cA vy cv cB cF
      fvimacnv ralbidv biimpa syl21anc vy cv cvv wcel vy cv vx cA cF ccnv cB
      cima ciin wcel vy cv cF ccnv cB cima wcel vx cA wral wb vy vex vx vy cv
      cA cF ccnv cB cima cvv eliin ax-mp sylibr cF wfun cA c0 wne wa vy cv vx
      cA cF ccnv cB cima ciin wcel wa vy cv cF cfv vx cA cB ciin wcel vy cv cF
      ccnv vx cA cB ciin cima wcel cF wfun cA c0 wne wa vy cv vx cA cF ccnv cB
      cima ciin wcel wa vy cv cF cfv cB wcel vx cA wral vy cv cF cfv vx cA cB
      ciin wcel cF wfun cA c0 wne wa vy cv vx cA cF ccnv cB cima ciin wcel wa
      cF wfun vy cv cF ccnv cB cima wcel vx cA wral vy cv cF cfv cB wcel vx cA
      wral cF wfun cA c0 wne vy cv vx cA cF ccnv cB cima ciin wcel simpll vy cv
      vx cA cF ccnv cB cima ciin wcel vy cv cF ccnv cB cima wcel vx cA wral cF
      wfun cA c0 wne wa vy cv cvv wcel vy cv vx cA cF ccnv cB cima ciin wcel vy
      cv cF ccnv cB cima wcel vx cA wral wi vy vex vy cv cvv wcel vy cv vx cA
      cF ccnv cB cima ciin wcel vy cv cF ccnv cB cima wcel vx cA wral vx vy cv
      cA cF ccnv cB cima cvv eliin biimpd ax-mp adantl cF wfun vy cv cF ccnv cB
      cima wcel vy cv cF cfv cB wcel vx cA cF wfun vy cv cF ccnv cB cima wcel
      vy cv cF cfv cB wcel vy cv cB cF fvimacnvi ex ralimdv sylc vy cv cF cfv
      cvv wcel vy cv cF cfv vx cA cB ciin wcel vy cv cF cfv cB wcel vx cA wral
      wb vy cv cF fvex vx vy cv cF cfv cA cB cvv eliin ax-mp sylibr cF wfun cA
      c0 wne wa vy cv vx cA cF ccnv cB cima ciin wcel wa cF wfun vy cv cF cdm
      wcel vy cv cF cfv vx cA cB ciin wcel vy cv cF ccnv vx cA cB ciin cima
      wcel wb cF wfun cA c0 wne vy cv vx cA cF ccnv cB cima ciin wcel simpll cF
      wfun cA c0 wne wa vy cv vx cA cF ccnv cB cima ciin wcel vy cv cF cdm wcel
      cA c0 wne vy cv vx cA cF ccnv cB cima ciin wcel vy cv cF cdm wcel wi cF
      wfun vy cv vx cA cF ccnv cB cima ciin wcel vy cv cF ccnv cB cima wcel vx
      cA wral cA c0 wne vy cv cF cdm wcel vy cv cvv wcel vy cv vx cA cF ccnv cB
      cima ciin wcel vy cv cF ccnv cB cima wcel vx cA wral wb vy vex vx vy cv
      cA cF ccnv cB cima cvv eliin ax-mp cA c0 wne vy cv cF ccnv cB cima wcel
      vx cA wral vy cv cF ccnv cB cima wcel vx cA wrex vy cv cF cdm wcel cA c0
      wne vy cv cF ccnv cB cima wcel vx cA wral vy cv cF ccnv cB cima wcel vx
      cA wrex wi vy cv cF ccnv cB cima wcel vx cA r19.2zb biimpi vy cv cF ccnv
      cB cima wcel vy cv cF cdm wcel vx cA cF ccnv cB cima cF cdm vy cv cF cB
      cnvimass sseli rexlimivw syl6 syl5bi adantl imp vy cv vx cA cB ciin cF
      fvimacnv syl2anc mpbid impbida eqrdv $.

    $( Preimage of an intersection.  (Contributed by FL, 28-Apr-2012.) $)
    intpreima $p |- ( ( Fun F /\ A =/= (/) )
        -> ( `' F " |^| A ) = |^|_ x e. A ( `' F " x ) ) $=
      cF wfun cA c0 wne wa cF ccnv cA cint cima cF ccnv vx cA vx cv ciin cima
      vx cA cF ccnv vx cv cima ciin cA cint vx cA vx cv ciin cF ccnv vx cA
      intiin imaeq2i vx cA vx cv cF iinpreima syl5eq $.
  $}

  $( The preimage of the codomain of a mapping is the mapping's domain.
     (Contributed by FL, 25-Jan-2007.) $)
  fimacnv $p |- ( F : A --> B -> ( `' F " B ) = A ) $=
    cA cB cF wf cF ccnv cB cima cA cA cB cF wf cF ccnv cB cima cF ccnv crn cA
    cF ccnv cB imassrn cA cB cF wf cF ccnv crn cF cdm cA cF dfdm4 cA cB cF wf
    cF cdm cA cA cA cB cF fdm cA cA wss cA cB cF wf cA ssid a1i eqsstrd
    syl5eqssr syl5ss cA cB cF wf cF cA cima cB wss cA cF ccnv cB cima wss cA cB
    cF wf cF cA cima cF crn cB cF cA imassrn cA cB cF frn syl5ss cA cB cF wf cF
    wfun cA cF cdm wss cF cA cima cB wss cA cF ccnv cB cima wss wb cA cB cF
    ffun cA cB cF wf cA cA cF cdm cA ssid cA cB cF fdm syl5sseqr cA cB cF
    funimass3 syl2anc mpbid eqssd $.

  ${
    $d k F $.  $d k ph $.  $d k W $.  $d k Z $.
    suppss.f $e |- ( ph -> F : A --> B ) $.
    suppss.n $e |- ( ( ph /\ k e. ( A \ W ) ) -> ( F ` k ) = Z ) $.
    $( Show that the support of a function is contained in a set.  (Contributed
       by Mario Carneiro, 19-Dec-2014.) $)
    suppss $p |- ( ph -> ( `' F " ( _V \ { Z } ) ) C_ W ) $=
      wph vk cF ccnv cvv cZ csn cdif cima cW wph vk cv cF ccnv cvv cZ csn cdif
      cima wcel vk cv cA wcel vk cv cF cfv cvv cZ csn cdif wcel wa vk cv cW
      wcel wph cA cB cF wf cF cA wfn vk cv cF ccnv cvv cZ csn cdif cima wcel vk
      cv cA wcel vk cv cF cfv cvv cZ csn cdif wcel wa wb suppss.f cA cB cF ffn
      cA vk cv cvv cZ csn cdif cF elpreima 3syl wph vk cv cA wcel vk cv cF cfv
      cvv cZ csn cdif wcel vk cv cW wcel vk cv cF cfv cvv cZ csn cdif wcel vk
      cv cF cfv cZ wne wph vk cv cA wcel wa vk cv cW wcel vk cv cF cfv cvv cZ
      csn cdif wcel vk cv cF cfv cvv wcel vk cv cF cfv cZ wne vk cv cF fvex vk
      cv cF cfv cvv cZ eldifsn mpbiran wph vk cv cA wcel wa vk cv cW wcel vk cv
      cF cfv cZ wph vk cv cA wcel vk cv cW wcel wn vk cv cF cfv cZ wceq vk cv
      cA wcel vk cv cW wcel wn wa wph vk cv cA cW cdif wcel vk cv cF cfv cZ
      wceq vk cv cA cW eldif suppss.n sylan2br expr necon1ad syl5bi expimpd
      sylbid ssrdv $.
  $}

  ${
    suppssr.f $e |- ( ph -> F : A --> B ) $.
    suppssr.n $e |- ( ph -> ( `' F " ( _V \ { Z } ) ) C_ W ) $.
    $( A function is zero outside its support.  (Contributed by Mario Carneiro,
       19-Dec-2014.) $)
    suppssr $p |- ( ( ph /\ X e. ( A \ W ) ) -> ( F ` X ) = Z ) $=
      cX cA cW cdif wcel wph cX cA wcel cX cW wcel wn wa cX cF cfv cZ wceq cX
      cA cW eldif wph cX cA wcel cX cW wcel wn cX cF cfv cZ wceq wph cX cA wcel
      wa cX cW wcel cX cF cfv cZ cX cF cfv cZ wne cX cF cfv cvv cZ csn cdif
      wcel wph cX cA wcel wa cX cW wcel cX cF cfv cvv cZ csn cdif wcel cX cF
      cfv cvv wcel cX cF cfv cZ wne cX cF fvex cX cF cfv cvv cZ eldifsn mpbiran
      wph cX cA wcel cX cF cfv cvv cZ csn cdif wcel cX cW wcel wph cX cA wcel
      cX cF cfv cvv cZ csn cdif wcel wa cX cF ccnv cvv cZ csn cdif cima wcel cX
      cW wcel wph cA cB cF wf cF cA wfn cX cF ccnv cvv cZ csn cdif cima wcel cX
      cA wcel cX cF cfv cvv cZ csn cdif wcel wa wb suppssr.f cA cB cF ffn cA cX
      cvv cZ csn cdif cF elpreima 3syl wph cF ccnv cvv cZ csn cdif cima cW cX
      suppssr.n sseld sylbird expdimp syl5bir necon1bd impr sylan2b $.
  $}

  $( Ordered pair with function value.  Part of Theorem 4.3(i) of [Monk1]
     p. 41.  (Contributed by NM, 30-Sep-2004.) $)
  fnopfv $p |- ( ( F Fn A /\ B e. A ) -> <. B , ( F ` B ) >. e. F ) $=
    cB cB cF cfv cop cF wcel cA cB cF cB cF funfvop funfni $.

  ${
    $d x y F $.  $d x A $.
    $( A function's value belongs to its range.  (Contributed by NM,
       14-Oct-1996.) $)
    fvelrn $p |- ( ( Fun F /\ A e. dom F ) -> ( F ` A ) e. ran F ) $=
      cF wfun cA cF cdm wcel cA cF cfv cF crn wcel cF wfun vx cv cF cdm wcel wa
      vx cv cF cfv cF crn wcel wi cF wfun cA cF cdm wcel wa cA cF cfv cF crn
      wcel wi vx cA cF cdm vx cv cA wceq cF wfun vx cv cF cdm wcel wa cF wfun
      cA cF cdm wcel wa vx cv cF cfv cF crn wcel cA cF cfv cF crn wcel vx cv cA
      wceq vx cv cF cdm wcel cA cF cdm wcel cF wfun vx cv cA cF cdm eleq1
      anbi2d vx cv cA wceq vx cv cF cfv cA cF cfv cF crn vx cv cA cF fveq2
      eleq1d imbi12d cF wfun vx cv cF cdm wcel wa vy cv vx cv cF cfv cop cF
      wcel vy wex vx cv cF cfv cF crn wcel cF wfun vx cv cF cdm wcel wa vx cv
      vx cv cF cfv cop cF wcel vy cv vx cv cF cfv cop cF wcel vy wex vx cv cF
      funfvop vy cv vx cv cF cfv cop cF wcel vx cv vx cv cF cfv cop cF wcel vy
      vx cv vx vex vy cv vx cv wceq vy cv vx cv cF cfv cop vx cv vx cv cF cfv
      cop cF vy cv vx cv vx cv cF cfv opeq1 eleq1d spcev syl vy vx cv cF cfv cF
      vx cv cF fvex elrn2 sylibr vtoclg anabsi7 $.
  $}

  $( A function's value belongs to its range.  (Contributed by NM,
     15-Oct-1996.) $)
  fnfvelrn $p |- ( ( F Fn A /\ B e. A ) -> ( F ` B ) e. ran F ) $=
    cB cF cfv cF crn wcel cA cB cF cB cF fvelrn funfni $.

  $( A function's value belongs to its codomain.  (Contributed by NM,
     12-Aug-1999.) $)
  ffvelrn $p |- ( ( F : A --> B /\ C e. A ) -> ( F ` C ) e. B ) $=
    cA cB cF wf cC cA wcel wa cC cF cfv cF crn wcel cC cF cfv cB wcel cA cB cF
    wf cF cA wfn cC cA wcel cC cF cfv cF crn wcel cA cB cF ffn cA cC cF
    fnfvelrn sylan cA cB cF wf cC cF cfv cF crn wcel cC cF cfv cB wcel wi cC cA
    wcel cA cB cF wf cF crn cB cC cF cfv cA cB cF frn sseld adantr mpd $.

  ${
    ffvrni.1 $e |- F : A --> B $.
    $( A function's value belongs to its codomain.  (Contributed by NM,
       6-Apr-2005.) $)
    ffvelrni $p |- ( C e. A -> ( F ` C ) e. B ) $=
      cA cB cF wf cC cA wcel cC cF cfv cB wcel ffvrni.1 cA cB cC cF ffvelrn
      mpan $.
  $}

  ${
    ffvelrnd.1 $e |- ( ph -> F : A --> B ) $.
    $( A function's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) $)
    ffvelrnda $p |- ( ( ph /\ C e. A ) -> ( F ` C ) e. B ) $=
      wph cA cB cF wf cC cA wcel cC cF cfv cB wcel ffvelrnd.1 cA cB cC cF
      ffvelrn sylan $.

    ffvelrnd.2 $e |- ( ph -> C e. A ) $.
    $( A function's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) $)
    ffvelrnd $p |- ( ph -> ( F ` C ) e. B ) $=
      wph cC cA wcel cC cF cfv cB wcel ffvelrnd.2 wph cA cB cC cF ffvelrnd.1
      ffvelrnda mpdan $.
  $}

  ${
    $d x y A $.  $d x y F $.  $d x ps $.  $d y ph $.
    rexrn.1 $e |- ( x = ( F ` y ) -> ( ph <-> ps ) ) $.
    $( Restricted existential quantification over the range of a function.
       (Contributed by Mario Carneiro, 24-Dec-2013.)  (Revised by Mario
       Carneiro, 20-Aug-2014.) $)
    rexrn $p |- ( F Fn A -> ( E. x e. ran F ph <-> E. y e. A ps ) ) $=
      cF cA wfn wph wps vx vy vy cv cF cfv cF crn cA cvv vy cv cF cfv cvv wcel
      cF cA wfn vy cv cA wcel wa vy cv cF fvex a1i cF cA wfn vx cv cF crn wcel
      vy cv cF cfv vx cv wceq vy cA wrex vx cv vy cv cF cfv wceq vy cA wrex vy
      cA vx cv cF fvelrnb vy cv cF cfv vx cv wceq vx cv vy cv cF cfv wceq vy cA
      vy cv cF cfv vx cv eqcom rexbii syl6bb vx cv vy cv cF cfv wceq wph wps wb
      cF cA wfn rexrn.1 adantl rexxfr2d $.

    $( Restricted universal quantification over the range of a function.
       (Contributed by Mario Carneiro, 24-Dec-2013.)  (Revised by Mario
       Carneiro, 20-Aug-2014.) $)
    ralrn $p |- ( F Fn A -> ( A. x e. ran F ph <-> A. y e. A ps ) ) $=
      cF cA wfn wph wps vx vy vy cv cF cfv cF crn cA cvv vy cv cF cfv cvv wcel
      cF cA wfn vy cv cA wcel wa vy cv cF fvex a1i cF cA wfn vx cv cF crn wcel
      vy cv cF cfv vx cv wceq vy cA wrex vx cv vy cv cF cfv wceq vy cA wrex vy
      cA vx cv cF fvelrnb vy cv cF cfv vx cv wceq vx cv vy cv cF cfv wceq vy cA
      vy cv cF cfv vx cv eqcom rexbii syl6bb vx cv vy cv cF cfv wceq wph wps wb
      cF cA wfn rexrn.1 adantl ralxfr2d $.
  $}

  ${
    $d w x z A $.  $d y B $.  $d y ch $.  $d w y z F $.  $d w x z ps $.
    ralrnmpt.1 $e |- F = ( x e. A |-> B ) $.
    ralrnmpt.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 20-Aug-2015.) $)
    ralrnmpt $p |- ( A. x e. A B e. V ->
      ( A. y e. ran F ps <-> A. x e. A ch ) ) $=
      cB cV wcel vx cA wral wps vy cF crn wral wps vy vx cv cF cfv wsbc vx cA
      wral wch vx cA wral cB cV wcel vx cA wral wps vy vw cv wsbc vw cF crn
      wral wps vy vz cv cF cfv wsbc vz cA wral wps vy cF crn wral wps vy vx cv
      cF cfv wsbc vx cA wral cB cV wcel vx cA wral cF cA wfn wps vy vw cv wsbc
      vw cF crn wral wps vy vz cv cF cfv wsbc vz cA wral wb vx cA cB cF cV
      ralrnmpt.1 fnmpt wps vy vw cv wsbc wps vy vz cv cF cfv wsbc vw vz cA cF
      wps vy vw cv vz cv cF cfv dfsbcq ralrn syl wps vy cF crn wral wps vy vw
      cv wsbc vw cF crn wral wps wps vy vw cv wsbc vy vw cF crn wps vw nfv wps
      vy vw cv nfsbc1v wps vy vw cv sbceq1a cbvral bicomi wps vy vz cv cF cfv
      wsbc wps vy vx cv cF cfv wsbc vz vx cA wps vx vy vz cv cF cfv vx vz cv cF
      vx cF vx cA cB cmpt ralrnmpt.1 vx cA cB nfmpt1 nfcxfr vx vz cv nfcv nffv
      wps vx nfv nfsbc wps vy vx cv cF cfv wsbc vz nfv vz vx weq vz cv cF cfv
      vx cv cF cfv wceq wps vy vz cv cF cfv wsbc wps vy vx cv cF cfv wsbc wb vz
      cv vx cv cF fveq2 wps vy vz cv cF cfv vx cv cF cfv dfsbcq syl cbvral
      3bitr3g cB cV wcel vx cA wral wps vy vx cv cF cfv wsbc wch wb vx cA wral
      wps vy vx cv cF cfv wsbc vx cA wral wch vx cA wral wb cB cV wcel wps vy
      vx cv cF cfv wsbc wch wb vx cA vx cv cA wcel cB cV wcel wa wps vy vx cv
      cF cfv wsbc wps vy cB wsbc wch vx cv cA wcel cB cV wcel wa vx cv cF cfv
      cB wceq wps vy vx cv cF cfv wsbc wps vy cB wsbc wb vx cA cB cV cF
      ralrnmpt.1 fvmpt2 wps vy vx cv cF cfv cB dfsbcq syl cB cV wcel wps vy cB
      wsbc wch wb vx cv cA wcel wps wch vy cB cV ralrnmpt.2 sbcieg adantl bitrd
      ralimiaa wps vy vx cv cF cfv wsbc wch vx cA ralbi syl bitrd $.

    $( A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 20-Aug-2015.) $)
    rexrnmpt $p |- ( A. x e. A B e. V ->
      ( E. y e. ran F ps <-> E. x e. A ch ) ) $=
      cB cV wcel vx cA wral wps wn vy cF crn wral wn wch wn vx cA wral wn wps
      vy cF crn wrex wch vx cA wrex cB cV wcel vx cA wral wps wn vy cF crn wral
      wch wn vx cA wral wps wn wch wn vx vy cA cB cF cV ralrnmpt.1 vy cv cB
      wceq wps wch ralrnmpt.2 notbid ralrnmpt notbid wps vy cF crn dfrex2 wch
      vx cA dfrex2 3bitr4g $.
  $}

  ${
    $d x y A $.  $d x y C $.  $d x y D $.  $d y B $.
    f0cl.1 $e |- F : A --> B $.
    f0cl.2 $e |- (/) e. B $.
    $( Unconditional closure of a function when the range includes the empty
       set.  (Contributed by Mario Carneiro, 12-Sep-2013.) $)
    f0cli $p |- ( F ` C ) e. B $=
      cC cA wcel cC cF cfv cB wcel cA cB cC cF f0cl.1 ffvelrni cC cA wcel cC cF
      cdm wcel cC cF cfv cB wcel cF cdm cA cC cA cB cF f0cl.1 fdmi eleq2i cC cF
      cdm wcel wn cC cF cfv c0 cB cC cF ndmfv f0cl.2 syl6eqel sylnbir pm2.61i
      $.
  $}

  $( Alternate definition of a mapping.  (Contributed by NM, 14-Nov-2007.) $)
  dff2 $p |- ( F : A --> B <-> ( F Fn A /\ F C_ ( A X. B ) ) ) $=
    cA cB cF wf cF cA wfn cF cA cB cxp wss wa cA cB cF wf cF cA wfn cF cA cB
    cxp wss cA cB cF ffn cA cB cF fssxp jca cF cA wfn cF cA cB cxp wss wa cF cA
    wfn cF crn cB wss wa cA cB cF wf cF cA cB cxp wss cF crn cB wss cF cA wfn
    cF cA cB cxp wss cF crn cA cB cxp crn cB cF cA cB cxp rnss cA cB rnxpss
    syl6ss anim2i cA cB cF df-f sylibr impbii $.

  ${
    $d f g x y z A $.  $d f g x y z B $.  $d x y z F $.
    $( Alternate definition of a mapping.  (Contributed by NM, 20-Mar-2007.) $)
    dff3 $p |- ( F : A --> B <->
              ( F C_ ( A X. B ) /\ A. x e. A E! y x F y ) ) $=
      cA cB cF wf cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral wa cA
      cB cF wf cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral cA cB cF
      fssxp cA cB cF wf vx cv vy cv cF wbr vy weu vx cA cA cB cF wf vx cv cA
      wcel wa vx cv vy cv cF wbr vy wex vx cv vy cv cF wbr vy wmo vx cv vy cv
      cF wbr vy weu cA cB cF wf vx cv cA wcel wa vx cv vx cv cF cfv cF wbr vx
      cv vy cv cF wbr vy wex cA cB cF wf vx cv cA wcel wa vx cv vx cv cF cfv
      cop cF wcel vx cv vx cv cF cfv cF wbr cA cB cF wf vx cv cA wcel wa cF
      wfun vx cv cF cdm wcel vx cv vx cv cF cfv cop cF wcel cA cB cF wf cF wfun
      vx cv cA wcel cA cB cF ffun adantr cA cB cF wf vx cv cF cdm wcel vx cv cA
      wcel cA cB cF wf cF cdm cA vx cv cA cB cF fdm eleq2d biimpar vx cv cF
      funfvop syl2anc vx cv vx cv cF cfv cF df-br sylibr vx cv vy cv cF wbr vx
      cv vx cv cF cfv cF wbr vy vx cv cF cfv vx cv cF fvex vy cv vx cv cF cfv
      vx cv cF breq2 spcev syl cA cB cF wf vx cv vy cv cF wbr vy wmo vx cv cA
      wcel cA cB cF wf cF wfun vx cv vy cv cF wbr vy wmo cA cB cF ffun vy vx cv
      cF funmo syl adantr vx cv vy cv cF wbr vy eu5 sylanbrc ralrimiva jca cF
      cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral wa cF cA wfn cF crn cB
      wss cA cB cF wf cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral wa
      cF wfun cF cdm cA wceq cF cA wfn cF cA cB cxp wss vx cv vy cv cF wbr vy
      weu vx cA wral wa cF wrel vx cv vy cv cF wbr vy wmo vx wal cF wfun cF cA
      cB cxp wss cF wrel vx cv vy cv cF wbr vy weu vx cA wral cF cA cB cxp wss
      cF cvv cvv cxp wss cF wrel cF cA cB cxp wss cA cB cxp cvv cvv cxp wss cF
      cvv cvv cxp wss cA cB xpss cF cA cB cxp cvv cvv cxp sstr mpan2 cF df-rel
      sylibr adantr cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral vx cv
      vy cv cF wbr vy wmo vx wal vx cv vy cv cF wbr vy weu vx cA wral vx cv cA
      wcel vx cv vy cv cF wbr vy weu wi vx wal cF cA cB cxp wss vx cv vy cv cF
      wbr vy wmo vx wal vx cv vy cv cF wbr vy weu vx cA df-ral cF cA cB cxp wss
      vx cv cA wcel vx cv vy cv cF wbr vy weu wi vx cv vy cv cF wbr vy wmo vx
      cF cA cB cxp wss vx cv cA wcel vx cv vy cv cF wbr vy weu wi vx cv vy cv
      cF wbr vy wmo cF cA cB cxp wss vx cv cA wcel vx cv vy cv cF wbr vy weu wi
      wa vx cv cA wcel vx cv vy cv cF wbr vy wmo vx cv cA wcel vx cv vy cv cF
      wbr vy weu wi vx cv cA wcel vx cv vy cv cF wbr vy wmo wi cF cA cB cxp wss
      vx cv vy cv cF wbr vy weu vx cv vy cv cF wbr vy wmo vx cv cA wcel vx cv
      vy cv cF wbr vy eumo imim2i adantl cF cA cB cxp wss vx cv cA wcel wn vx
      cv vy cv cF wbr vy wmo wi vx cv cA wcel vx cv vy cv cF wbr vy weu wi cF
      cA cB cxp wss vx cv cA wcel wn vx cv vy cv cF wbr vy wex wn vx cv vy cv
      cF wbr vy wmo cF cA cB cxp wss vx cv vy cv cF wbr vy wex vx cv cA wcel cF
      cA cB cxp wss vx cv vy cv cF wbr vx cv cA wcel vy cF cA cB cxp wss vx cv
      vy cv cF wbr vx cv vy cv cop cA cB cxp wcel vx cv cA wcel vx cv vy cv cF
      wbr vx cv vy cv cop cF wcel cF cA cB cxp wss vx cv vy cv cop cA cB cxp
      wcel vx cv vy cv cF df-br cF cA cB cxp vx cv vy cv cop ssel syl5bi vx cv
      vy cv cA cB opelxp1 syl6 exlimdv con3d vx cv vy cv cF wbr vy wex vx cv vy
      cv cF wbr vy wmo vx cv vy cv cF wbr vy exmo ori syl6 adantr pm2.61d ex
      alimdv syl5bi imp vx vy cF dffun6 sylanbrc cF cA cB cxp wss vx cv vy cv
      cF wbr vy weu vx cA wral wa cF cdm cA wss cA cF cdm wss wa cF cdm cA wceq
      cF cA cB cxp wss cF cdm cA wss vx cv vy cv cF wbr vy weu vx cA wral cA cF
      cdm wss cF cA cB cxp wss cF cdm cA cB cxp cdm cA cF cA cB cxp dmss cA cB
      dmxpss syl6ss vx cv vy cv cF wbr vy weu vx cA wral vz cA cF cdm vx cv vy
      cv cF wbr vy weu vx cA wral vz cv cA wcel vz cv vy cv cF wbr vy weu vz cv
      cF cdm wcel vx cv vy cv cF wbr vy weu vz cv vy cv cF wbr vy weu vx vz cv
      cA vx cv vz cv wceq vx cv vy cv cF wbr vz cv vy cv cF wbr vy vx cv vz cv
      vy cv cF breq1 eubidv rspccv vz cv vy cv cF wbr vy weu vz cv vy cv cF wbr
      vy wex vz cv cF cdm wcel vz cv vy cv cF wbr vy euex vy vz cv cF vz vex
      eldm sylibr syl6 ssrdv anim12i cF cdm cA eqss sylibr cF cA df-fn sylanbrc
      cF cA cB cxp wss cF crn cB wss vx cv vy cv cF wbr vy weu vx cA wral cF cA
      cB cxp wss cF crn cA cB cxp crn cB cF cA cB cxp rnss cA cB rnxpss syl6ss
      adantr cA cB cF df-f sylanbrc impbii $.

    $( Alternate definition of a mapping.  (Contributed by NM, 20-Mar-2007.) $)
    dff4 $p |- ( F : A --> B <->
              ( F C_ ( A X. B ) /\ A. x e. A E! y e. B x F y ) ) $=
      cA cB cF wf cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral wa cF
      cA cB cxp wss vx cv vy cv cF wbr vy cB wreu vx cA wral wa vx vy cA cB cF
      dff3 cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx cA wral vx cv vy cv cF
      wbr vy cB wreu vx cA wral cF cA cB cxp wss vx cv vy cv cF wbr vy weu vx
      cv vy cv cF wbr vy cB wreu vx cA cF cA cB cxp wss vx cv vy cv cF wbr vy
      weu vy cv cB wcel vx cv vy cv cF wbr wa vy weu vx cv vy cv cF wbr vy cB
      wreu cF cA cB cxp wss vx cv vy cv cF wbr vy cv cB wcel vx cv vy cv cF wbr
      wa vy cF cA cB cxp wss vx cv vy cv cF wbr vy cv cB wcel vx cv vy cv cF
      wbr vx cv vy cv cop cF wcel cF cA cB cxp wss vy cv cB wcel vx cv vy cv cF
      df-br cF cA cB cxp wss vx cv vy cv cop cF wcel vx cv vy cv cop cA cB cxp
      wcel vy cv cB wcel cF cA cB cxp vx cv vy cv cop ssel vx cv vy cv cA cB
      opelxp2 syl6 syl5bi pm4.71rd eubidv vx cv vy cv cF wbr vy cB df-reu
      syl6bbr ralbidv pm5.32i bitri $.

    $( An onto mapping expressed in terms of function values.  (Contributed by
       NM, 29-Oct-2006.) $)
    dffo3 $p |- ( F : A -onto-> B <-> ( F : A --> B /\
                  A. y e. B E. x e. A y = ( F ` x ) ) ) $=
      cA cB cF wfo cA cB cF wf cF crn cB wceq wa cA cB cF wf vy cv vx cv cF cfv
      wceq vx cA wrex vy cB wral wa cA cB cF dffo2 cA cB cF wf cF crn cB wceq
      vy cv vx cv cF cfv wceq vx cA wrex vy cB wral cA cB cF wf cF crn cB wceq
      vy cv vx cv cF cfv wceq vx cA wrex vy cab cB wceq vy cv vx cv cF cfv wceq
      vx cA wrex vy cB wral cA cB cF wf cF cA wfn cF crn cB wceq vy cv vx cv cF
      cfv wceq vx cA wrex vy cab cB wceq wb cA cB cF ffn cF cA wfn cF crn vy cv
      vx cv cF cfv wceq vx cA wrex vy cab cB vx vy cA cF fnrnfv eqeq1d syl cA
      cB cF wf vy cv vx cv cF cfv wceq vx cA wrex vy cv cB wcel wb vy wal vy cv
      cB wcel vy cv vx cv cF cfv wceq vx cA wrex wi vy wal vy cv vx cv cF cfv
      wceq vx cA wrex vy cab cB wceq vy cv vx cv cF cfv wceq vx cA wrex vy cB
      wral cA cB cF wf vy cv vx cv cF cfv wceq vx cA wrex vy cv cB wcel wb vy
      cv cB wcel vy cv vx cv cF cfv wceq vx cA wrex wi vy cA cB cF wf vy cv cB
      wcel vy cv vx cv cF cfv wceq vx cA wrex wi vy cv vx cv cF cfv wceq vx cA
      wrex vy cv cB wcel wi vy cv cB wcel vy cv vx cv cF cfv wceq vx cA wrex wi
      wa vy cv vx cv cF cfv wceq vx cA wrex vy cv cB wcel wb cA cB cF wf vy cv
      vx cv cF cfv wceq vx cA wrex vy cv cB wcel wi vy cv cB wcel vy cv vx cv
      cF cfv wceq vx cA wrex wi cA cB cF wf vy cv vx cv cF cfv wceq vy cv cB
      wcel vx cA cA cB cF wf vx cv cA wcel vy cv vx cv cF cfv wceq vy cv cB
      wcel cA cB cF wf vx cv cA wcel wa vy cv vx cv cF cfv wceq wa vy cv vx cv
      cF cfv cB cA cB cF wf vx cv cA wcel wa vy cv vx cv cF cfv wceq simpr cA
      cB cF wf vx cv cA wcel wa vx cv cF cfv cB wcel vy cv vx cv cF cfv wceq cA
      cB vx cv cF ffvelrn adantr eqeltrd exp31 rexlimdv biantrurd vy cv vx cv
      cF cfv wceq vx cA wrex vy cv cB wcel dfbi2 syl6rbbr albidv vy cv vx cv cF
      cfv wceq vx cA wrex vy cB abeq1 vy cv vx cv cF cfv wceq vx cA wrex vy cB
      df-ral 3bitr4g bitrd pm5.32i bitri $.

    $( Alternate definition of an onto mapping.  (Contributed by NM,
       20-Mar-2007.) $)
    dffo4 $p |- ( F : A -onto-> B <->
                ( F : A --> B /\ A. y e. B E. x e. A x F y ) ) $=
      cA cB cF wfo cA cB cF wf vx cv vy cv cF wbr vx cA wrex vy cB wral wa cA
      cB cF wfo cA cB cF wf cF crn cB wceq wa cA cB cF wf vx cv vy cv cF wbr vx
      cA wrex vy cB wral wa cA cB cF dffo2 cA cB cF wf cF crn cB wceq wa cA cB
      cF wf vx cv vy cv cF wbr vx cA wrex vy cB wral cA cB cF wf cF crn cB wceq
      simpl cA cB cF wf cF crn cB wceq wa vx cv vy cv cF wbr vx cA wrex vy cB
      cA cB cF wf cF crn cB wceq wa vy cv cB wcel wa vx cv vy cv cF wbr vx wex
      vx cv vy cv cF wbr vx cA wrex cF crn cB wceq vy cv cB wcel vx cv vy cv cF
      wbr vx wex cA cB cF wf cF crn cB wceq vx cv vy cv cF wbr vx wex vy cv cB
      wcel vx cv vy cv cF wbr vx wex vy cv cF crn wcel cF crn cB wceq vy cv cB
      wcel vx vy cv cF vy vex elrn cF crn cB vy cv eleq2 syl5bbr biimpar
      adantll cA cB cF wf vx cv vy cv cF wbr vx wex vx cv vy cv cF wbr vx cA
      wrex wi cF crn cB wceq vy cv cB wcel cA cB cF wf vx cv vy cv cF wbr vx
      wex vx cv cA wcel vx cv vy cv cF wbr wa vx wex vx cv vy cv cF wbr vx cA
      wrex cA cB cF wf vx cv vy cv cF wbr vx cv cA wcel vx cv vy cv cF wbr wa
      vx cA cB cF wf vx cv vy cv cF wbr vx cv cA wcel cA cB cF wf cF cA wfn vx
      cv vy cv cF wbr vx cv cA wcel wi cA cB cF ffn cF cA wfn vx cv vy cv cF
      wbr vx cv cA wcel cA vx cv vy cv cF fnbr ex syl ancrd eximdv vx cv vy cv
      cF wbr vx cA df-rex syl6ibr ad2antrr mpd ralrimiva jca sylbi cA cB cF wf
      vx cv vy cv cF wbr vx cA wrex vy cB wral wa cA cB cF wf vy cv vx cv cF
      cfv wceq vx cA wrex vy cB wral wa cA cB cF wfo cA cB cF wf vx cv vy cv cF
      wbr vx cA wrex vy cB wral vy cv vx cv cF cfv wceq vx cA wrex vy cB wral
      cA cB cF wf vx cv vy cv cF wbr vx cA wrex vy cv vx cv cF cfv wceq vx cA
      wrex vy cB cA cB cF wf vx cv vy cv cF wbr vy cv vx cv cF cfv wceq vx cA
      cA cB cF wf cF cA wfn vx cv cA wcel vx cv vy cv cF wbr vy cv vx cv cF cfv
      wceq wi cA cB cF ffn cF cA wfn vx cv cA wcel wa vx cv vy cv cF wbr vx cv
      cF cfv vy cv wceq vy cv vx cv cF cfv wceq cF cA wfn vx cv cA wcel wa vx
      cv cF cfv vy cv wceq vx cv vy cv cF wbr cA vx cv vy cv cF fnbrfvb biimprd
      vx cv cF cfv vy cv eqcom syl6ib sylan reximdva ralimdv imdistani vx vy cA
      cB cF dffo3 sylibr impbii $.

    $( Alternate definition of an onto mapping.  (Contributed by NM,
       20-Mar-2007.) $)
    dffo5 $p |- ( F : A -onto-> B <->
                ( F : A --> B /\ A. y e. B E. x x F y ) ) $=
      cA cB cF wfo cA cB cF wf vx cv vy cv cF wbr vx cA wrex vy cB wral wa cA
      cB cF wf vx cv vy cv cF wbr vx wex vy cB wral wa vx vy cA cB cF dffo4 cA
      cB cF wf vx cv vy cv cF wbr vx cA wrex vy cB wral wa cA cB cF wf vx cv vy
      cv cF wbr vx wex vy cB wral wa vx cv vy cv cF wbr vx cA wrex vy cB wral
      vx cv vy cv cF wbr vx wex vy cB wral cA cB cF wf vx cv vy cv cF wbr vx cA
      wrex vx cv vy cv cF wbr vx wex vy cB vx cv vy cv cF wbr vx cA rexex
      ralimi anim2i cA cB cF wf vx cv vy cv cF wbr vx wex vy cB wral vx cv vy
      cv cF wbr vx cA wrex vy cB wral cA cB cF wf vx cv vy cv cF wbr vx wex vx
      cv vy cv cF wbr vx cA wrex vy cB cA cB cF wf vx cv vy cv cF wbr vx wex vx
      cv cA wcel vx cv vy cv cF wbr wa vx wex vx cv vy cv cF wbr vx cA wrex cA
      cB cF wf vx cv vy cv cF wbr vx cv cA wcel vx cv vy cv cF wbr wa vx cA cB
      cF wf vx cv vy cv cF wbr vx cv cA wcel cA cB cF wf cF cA wfn vx cv vy cv
      cF wbr vx cv cA wcel wi cA cB cF ffn cF cA wfn vx cv vy cv cF wbr vx cv
      cA wcel cA vx cv vy cv cF fnbr ex syl ancrd eximdv vx cv vy cv cF wbr vx
      cA df-rex syl6ibr ralimdv imdistani impbii bitri $.

    $( A relation equivalent to the existence of an onto mapping.  The
       right-hand ` f ` is not necessarily a function.  (Contributed by NM,
       20-Mar-2007.) $)
    exfo $p |- ( E. f f : A -onto-> B <->
           E. f ( A. x e. A E! y e. B x f y /\ A. x e. B E. y e. A y f x ) ) $=
      cA cB vf cv wfo vf wex vx cv vy cv vf cv wbr vy cB wreu vx cA wral vy cv
      vx cv vf cv wbr vy cA wrex vx cB wral wa vf wex cA cB vf cv wfo vx cv vy
      cv vf cv wbr vy cB wreu vx cA wral vy cv vx cv vf cv wbr vy cA wrex vx cB
      wral wa vf cA cB vf cv wfo cA cB vf cv wf vy cv vx cv vf cv wbr vy cA
      wrex vx cB wral wa vx cv vy cv vf cv wbr vy cB wreu vx cA wral vy cv vx
      cv vf cv wbr vy cA wrex vx cB wral wa vy vx cA cB vf cv dffo4 cA cB vf cv
      wf vx cv vy cv vf cv wbr vy cB wreu vx cA wral vy cv vx cv vf cv wbr vy
      cA wrex vx cB wral cA cB vf cv wf vf cv cA cB cxp wss vx cv vy cv vf cv
      wbr vy cB wreu vx cA wral vx vy cA cB vf cv dff4 simprbi anim1i sylbi
      eximi vx cv vy cv vf cv wbr vy cB wreu vx cA wral vy cv vx cv vf cv wbr
      vy cA wrex vx cB wral wa vf wex cA cB vg cv wfo vg wex cA cB vf cv wfo vf
      wex vx cv vy cv vf cv wbr vy cB wreu vx cA wral vy cv vx cv vf cv wbr vy
      cA wrex vx cB wral wa cA cB vg cv wfo vg wex vf vx cv vy cv vf cv wbr vy
      cB wreu vx cA wral vy cv vx cv vf cv wbr vy cA wrex vx cB wral wa cA cB
      vf cv cA cB cxp cin wfo cA cB vg cv wfo vg wex vx cv vy cv vf cv wbr vy
      cB wreu vx cA wral vy cv vx cv vf cv wbr vy cA wrex vx cB wral wa cA cB
      vf cv cA cB cxp cin wf vf cv cA cB cxp cin crn cB wceq wa cA cB vf cv cA
      cB cxp cin wfo vx cv vy cv vf cv wbr vy cB wreu vx cA wral cA cB vf cv cA
      cB cxp cin wf vy cv vx cv vf cv wbr vy cA wrex vx cB wral vf cv cA cB cxp
      cin crn cB wceq vx cv vy cv vf cv wbr vy cB wreu vx cA wral vf cv cA cB
      cxp cin cA cB cxp wss vx cv vy cv vf cv cA cB cxp cin wbr vy cB wreu vx
      cA wral wa cA cB vf cv cA cB cxp cin wf vx cv vy cv vf cv wbr vy cB wreu
      vx cA wral vx cv vy cv vf cv cA cB cxp cin wbr vy cB wreu vx cA wral vf
      cv cA cB cxp cin cA cB cxp wss vx cv vy cv vf cv wbr vy cB wreu vx cv vy
      cv vf cv cA cB cxp cin wbr vy cB wreu vx cA vx cv cA wcel vx cv vy cv vf
      cv wbr vy cB wreu vx cv vy cv vf cv cA cB cxp cin wbr vy cB wreu vx cv cA
      wcel vx cv vy cv vf cv wbr vx cv vy cv vf cv cA cB cxp cin wbr vy cB vx
      cv vy cv cA cB vf cv brinxp reubidva biimpd ralimia vf cv cA cB cxp inss2
      jctil vx vy cA cB vf cv cA cB cxp cin dff4 sylibr vf cv cA cB cxp cin crn
      cB wceq vy cv vx cv vf cv wbr vy cA wrex vx cB wral vy vx cA cB vf cv
      rninxp biimpri anim12i cA cB vf cv cA cB cxp cin dffo2 sylibr cA cB vg cv
      wfo cA cB vf cv cA cB cxp cin wfo vg vf cv cA cB cxp cin vf cv cA cB cxp
      vf vex inex1 cA cB vg cv vf cv cA cB cxp cin foeq1 spcev syl exlimiv cA
      cB vg cv wfo cA cB vf cv wfo vg vf cA cB vg cv vf cv foeq1 cbvexv sylib
      impbii $.
  $}

  ${
    $d F x y $.  $d A x y $.  $d B x y $.  $d C x y $.
    $( Property of a surjective function.  (Contributed by Jeff Madsen,
       4-Jan-2011.) $)
    foelrn $p |- ( ( F : A -onto-> B /\ C e. B )
                                  -> E. x e. A C = ( F ` x ) ) $=
      cA cB cF wfo vy cv vx cv cF cfv wceq vx cA wrex vy cB wral cC cB wcel cC
      vx cv cF cfv wceq vx cA wrex cA cB cF wfo cA cB cF wf vy cv vx cv cF cfv
      wceq vx cA wrex vy cB wral vx vy cA cB cF dffo3 simprbi vy cv vx cv cF
      cfv wceq vx cA wrex cC vx cv cF cfv wceq vx cA wrex vy cC cB vy cv cC
      wceq vy cv vx cv cF cfv wceq cC vx cv cF cfv wceq vx cA vy cv cC vx cv cF
      cfv eqeq1 rexbidv rspccva sylan $.
  $}

  ${
    $d F x y z $.  $d G x y z $.  $d A y z $.  $d B x y z $.  $d C x y z $.
    $( If a composition of two functions is surjective, then the function on
       the left is surjective.  (Contributed by Jeff Madsen, 16-Jun-2011.) $)
    foco2 $p |- ( ( F : B --> C /\ G : A --> B /\
                        ( F o. G ) : A -onto-> C ) -> F : B -onto-> C ) $=
      cB cC cF wf cA cB cG wf cA cC cF cG ccom wfo w3a cB cC cF wf vy cv vx cv
      cF cfv wceq vx cB wrex vy cC wral cB cC cF wfo cB cC cF wf cA cB cG wf cA
      cC cF cG ccom wfo simp1 cB cC cF wf cA cB cG wf cA cC cF cG ccom wfo vy
      cv vx cv cF cfv wceq vx cB wrex vy cC wral cB cC cF wf cA cB cG wf wa cA
      cC cF cG ccom wfo wa vy cv vx cv cF cfv wceq vx cB wrex vy cC cB cC cF wf
      cA cB cG wf wa cA cC cF cG ccom wfo vy cv cC wcel vy cv vx cv cF cfv wceq
      vx cB wrex cA cC cF cG ccom wfo vy cv cC wcel wa vy cv vz cv cF cG ccom
      cfv wceq vz cA wrex cB cC cF wf cA cB cG wf wa vy cv vx cv cF cfv wceq vx
      cB wrex vz cA cC vy cv cF cG ccom foelrn cB cC cF wf cA cB cG wf wa vy cv
      vz cv cF cG ccom cfv wceq vy cv vx cv cF cfv wceq vx cB wrex vz cA cB cC
      cF wf cA cB cG wf wa vz cv cA wcel wa vy cv vx cv cF cfv wceq vx cB wrex
      vy cv vz cv cF cG ccom cfv wceq vz cv cF cG ccom cfv vx cv cF cfv wceq vx
      cB wrex cB cC cF wf cA cB cG wf wa vz cv cA wcel wa vz cv cG cfv cB wcel
      vz cv cF cG ccom cfv vz cv cG cfv cF cfv wceq vz cv cF cG ccom cfv vx cv
      cF cfv wceq vx cB wrex cA cB cG wf vz cv cA wcel vz cv cG cfv cB wcel cB
      cC cF wf cA cB vz cv cG ffvelrn adantll cA cB cG wf vz cv cA wcel vz cv
      cF cG ccom cfv vz cv cG cfv cF cfv wceq cB cC cF wf cA cB vz cv cF cG
      fvco3 adantll vz cv cF cG ccom cfv vx cv cF cfv wceq vz cv cF cG ccom cfv
      vz cv cG cfv cF cfv wceq vx vz cv cG cfv cB vx cv vz cv cG cfv wceq vx cv
      cF cfv vz cv cG cfv cF cfv vz cv cF cG ccom cfv vx cv vz cv cG cfv cF
      fveq2 eqeq2d rspcev syl2anc vy cv vz cv cF cG ccom cfv wceq vy cv vx cv
      cF cfv wceq vz cv cF cG ccom cfv vx cv cF cfv wceq vx cB vy cv vz cv cF
      cG ccom cfv vx cv cF cfv eqeq1 rexbidv syl5ibrcom rexlimdva syl5 impl
      ralrimiva 3impa vx vy cB cC cF dffo3 sylanbrc $.
  $}

  ${
    $d w x y z A $.  $d x y z B $.  $d y z C $.  $d w y z F $.
    fmpt.1 $e |- F = ( x e. A |-> C ) $.
    $( Functionality of the mapping operation.  (Contributed by Mario Carneiro,
       26-Jul-2013.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    fmpt $p |- ( A. x e. A C e. B <-> F : A --> B ) $=
      cC cB wcel vx cA wral cA cB cF wf cC cB wcel vx cA wral cF cA wfn cF crn
      cB wss cA cB cF wf vx cA cC cF cB fmpt.1 fnmpt cC cB wcel vx cA wral cF
      crn vy cv cC wceq vx cA wrex vy cab cB vx vy cA cC cF fmpt.1 rnmpt cC cB
      wcel vx cA wral vy cv cC wceq vx cA wrex vy cB cC cB wcel vx cA wral vy
      cv cC wceq vx cA wrex vy cv cB wcel cC cB wcel vx cA wral vy cv cC wceq
      vx cA wrex wa cC cB wcel vy cv cC wceq wa vx cA wrex vy cv cB wcel cC cB
      wcel vy cv cC wceq vx cA r19.29 cC cB wcel vy cv cC wceq wa vy cv cB wcel
      vx cA vy cv cC wceq vy cv cB wcel cC cB wcel vy cv cC cB eleq1 biimparc
      rexlimivw syl ex abssdv syl5eqss cA cB cF df-f sylanbrc cA cB cF wf cA cC
      cB wcel vx cA crab wceq cC cB wcel vx cA wral cA cB cF wf cC cB wcel vx
      cA crab cF ccnv cB cima cA vx cA cC cB cF fmpt.1 mptpreima cA cB cF
      fimacnv syl5reqr cC cB wcel vx cA rabid2 sylib impbii $.

    $( Express bijection for a mapping operation.  (Contributed by Mario
       Carneiro, 30-May-2015.)  (Revised by Mario Carneiro, 4-Dec-2016.) $)
    f1ompt $p |- ( F : A -1-1-onto-> B <->
        ( A. x e. A C e. B /\ A. y e. B E! x e. A y = C ) ) $=
      cA cB cF wf cA cB cF wf1o wa cA cB cF wf vy cv cC wceq vx cA wreu vy cB
      wral wa cA cB cF wf1o cC cB wcel vx cA wral vy cv cC wceq vx cA wreu vy
      cB wral wa cA cB cF wf cA cB cF wf1o vy cv cC wceq vx cA wreu vy cB wral
      cA cB cF wf cA cB cF wf1o cF ccnv cB wfn vy cv cC wceq vx cA wreu vy cB
      wral cA cB cF wf cF cA wfn cA cB cF wf1o cF ccnv cB wfn wb cA cB cF ffn
      cA cB cF wf1o cF cA wfn cF ccnv cB wfn cA cB cF dff1o4 baib syl vy cv cC
      wceq vx cA wreu vy cB wral cF ccnv cB cres cB wfn cA cB cF wf cF ccnv cB
      wfn cF ccnv cB cres cB wfn vy cv vz cv cF ccnv wbr vz weu vy cB wral vy
      cv cC wceq vx cA wreu vy cB wral vy vz cB cF ccnv fnres vy cv vz cv cF
      ccnv wbr vz weu vy cv cC wceq vx cA wreu vy cB vz cv vy cv cF wbr vz weu
      vx cv cA wcel vy cv cC wceq wa vx weu vy cv vz cv cF ccnv wbr vz weu vy
      cv cC wceq vx cA wreu vz cv vy cv cF wbr vx cv cA wcel vy cv cC wceq wa
      vz vx vx vz cv vy cv cF vx vz cv nfcv vx cF vx cA cC cmpt fmpt.1 vx cA cC
      nfmpt1 nfcxfr vx vy cv nfcv nfbr vx cv cA wcel vy cv cC wceq wa vz nfv vz
      cv vx cv wceq vz cv vy cv cF wbr vx cv vy cv cF wbr vx cv cA wcel vy cv
      cC wceq wa vz cv vx cv vy cv cF breq1 vx cv vy cv cF wbr vx cv vy cv vx
      cv cA wcel vy cv cC wceq wa vx vy copab wbr vx cv cA wcel vy cv cC wceq
      wa vx cv vy cv cF vx cv cA wcel vy cv cC wceq wa vx vy copab cF vx cA cC
      cmpt vx cv cA wcel vy cv cC wceq wa vx vy copab fmpt.1 vx vy cA cC df-mpt
      eqtri breqi vx cv vy cv vx cv cA wcel vy cv cC wceq wa vx vy copab wbr vx
      cv vy cv cop vx cv cA wcel vy cv cC wceq wa vx vy copab wcel vx cv cA
      wcel vy cv cC wceq wa vx cv vy cv vx cv cA wcel vy cv cC wceq wa vx vy
      copab df-br vx cv cA wcel vy cv cC wceq wa vx vy opabid bitri bitri
      syl6bb cbveu vy cv vz cv cF ccnv wbr vz cv vy cv cF wbr vz vy cv vz cv cF
      vy vex vz vex brcnv eubii vy cv cC wceq vx cA df-reu 3bitr4i ralbii bitri
      cA cB cF wf cB cF ccnv cB cres cF ccnv cA cB cF wf cF ccnv wrel cF ccnv
      cdm cB wss cF ccnv cB cres cF ccnv wceq cF relcnv cA cB cF wf cF ccnv cdm
      cF crn cB cF df-rn cA cB cF frn syl5eqssr cF ccnv cB relssres sylancr
      fneq1d syl5bbr bitr4d pm5.32i cA cB cF wf1o cA cB cF wf cA cB cF f1of
      pm4.71ri cC cB wcel vx cA wral cA cB cF wf vy cv cC wceq vx cA wreu vy cB
      wral vx cA cB cC cF fmpt.1 fmpt anbi1i 3bitr4i $.

    fmpti.2 $e |- ( x e. A -> C e. B ) $.
    $( Functionality of the mapping operation.  (Contributed by NM,
       19-Mar-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
    fmpti $p |- F : A --> B $=
      cC cB wcel vx cA wral cA cB cF wf cC cB wcel vx cA fmpti.2 rgen vx cA cB
      cC cF fmpt.1 fmpt mpbi $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x ph $.
    fmptd.1 $e |- ( ( ph /\ x e. A ) -> B e. C ) $.
    fmptd.2 $e |- F = ( x e. A |-> B ) $.
    $( Domain and codomain of the mapping operation; deduction form.
       (Contributed by Mario Carneiro, 13-Jan-2013.) $)
    fmptd $p |- ( ph -> F : A --> C ) $=
      wph cB cC wcel vx cA wral cA cC cF wf wph cB cC wcel vx cA fmptd.1
      ralrimiva vx cA cC cB cF fmptd.2 fmpt sylib $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.
    $( A function maps to a class to which all values belong.  (Contributed by
       NM, 3-Dec-2003.) $)
    ffnfv $p |- ( F : A --> B <-> ( F Fn A /\ A. x e. A ( F ` x ) e. B ) ) $=
      cA cB cF wf cF cA wfn vx cv cF cfv cB wcel vx cA wral wa cA cB cF wf cF
      cA wfn vx cv cF cfv cB wcel vx cA wral cA cB cF ffn cA cB cF wf vx cv cF
      cfv cB wcel vx cA cA cB vx cv cF ffvelrn ralrimiva jca cF cA wfn vx cv cF
      cfv cB wcel vx cA wral wa cF cA wfn cF crn cB wss cA cB cF wf cF cA wfn
      vx cv cF cfv cB wcel vx cA wral simpl cF cA wfn vx cv cF cfv cB wcel vx
      cA wral wa vy cF crn cB cF cA wfn vy cv cF crn wcel vx cv cF cfv vy cv
      wceq vx cA wrex vx cv cF cfv cB wcel vx cA wral vy cv cB wcel cF cA wfn
      vy cv cF crn wcel vx cv cF cfv vy cv wceq vx cA wrex vx cA vy cv cF
      fvelrnb biimpd vx cv cF cfv cB wcel vx cA wral vx cv cF cfv vy cv wceq vy
      cv cB wcel vx cA vx cv cF cfv cB wcel vx cA nfra1 vy cv cB wcel vx nfv vx
      cv cF cfv cB wcel vx cA wral vx cv cA wcel vx cv cF cfv cB wcel vx cv cF
      cfv vy cv wceq vy cv cB wcel wi vx cv cF cfv cB wcel vx cA rsp vx cv cF
      cfv vy cv wceq vx cv cF cfv cB wcel vy cv cB wcel vx cv cF cfv vy cv cB
      eleq1 biimpcd syl6 rexlimd sylan9 ssrdv cA cB cF df-f sylanbrc impbii $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z F $.  $d x y z $.
    ffnfvf.1 $e |- F/_ x A $.
    ffnfvf.2 $e |- F/_ x B $.
    ffnfvf.3 $e |- F/_ x F $.
    $( A function maps to a class to which all values belong.  This version of
       ~ ffnfv uses bound-variable hypotheses instead of distinct variable
       conditions.  (Contributed by NM, 28-Sep-2006.) $)
    ffnfvf $p |- ( F : A --> B <-> ( F Fn A /\ A. x e. A ( F ` x ) e. B ) ) $=
      cA cB cF wf cF cA wfn vz cv cF cfv cB wcel vz cA wral wa cF cA wfn vx cv
      cF cfv cB wcel vx cA wral wa vz cA cB cF ffnfv vz cv cF cfv cB wcel vz cA
      wral vx cv cF cfv cB wcel vx cA wral cF cA wfn vz cv cF cfv cB wcel vx cv
      cF cfv cB wcel vz vx cA vz cA nfcv ffnfvf.1 vx vz cv cF cfv cB vx vz cv
      cF ffnfvf.3 vx vz cv nfcv nffv ffnfvf.2 nfel vx cv cF cfv cB wcel vz nfv
      vz cv vx cv wceq vz cv cF cfv vx cv cF cfv cB vz cv vx cv cF fveq2 eleq1d
      cbvralf anbi2i bitri $.
  $}

  ${
    $d x y A $.  $d x B $.  $d x y F $.
    $( An upper bound for range determined by function values.  (Contributed by
       NM, 8-Oct-2004.) $)
    fnfvrnss $p |- ( ( F Fn A /\ A. x e. A ( F ` x ) e. B ) -> ran F C_ B ) $=
      cF cA wfn vx cv cF cfv cB wcel vx cA wral wa cA cB cF wf cF crn cB wss vx
      cA cB cF ffnfv cA cB cF frn sylbir $.
  $}

  ${
    $d x A $.  $d y A $.  $d y C $.  $d y F $.  $d x ph $.  $d y ph $.
    fmpt2d.2 $e |- ( ( ph /\ x e. A ) -> B e. V ) $.
    fmpt2d.1 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
    fmpt2d.3 $e |- ( ( ph /\ y e. A ) -> ( F ` y ) e. C ) $.
    $( Domain and codomain of the mapping operation; deduction form.
       (Contributed by NM, 27-Dec-2014.) $)
    fmpt2d $p |- ( ph -> F : A --> C ) $=
      wph cF cA wfn vy cv cF cfv cC wcel vy cA wral cA cC cF wf wph cF cA wfn
      vx cA cB cmpt cA wfn wph cB cV wcel vx cA wral vx cA cB cmpt cA wfn wph
      cB cV wcel vx cA fmpt2d.2 ralrimiva vx cA cB vx cA cB cmpt cV vx cA cB
      cmpt eqid fnmpt syl wph cA cF vx cA cB cmpt fmpt2d.1 fneq1d mpbird wph vy
      cv cF cfv cC wcel vy cA fmpt2d.3 ralrimiva vy cA cC cF ffnfv sylanbrc $.
  $}

  ${
    $d x y A $.  $d y C $.  $d y F $.  $d x y ph $.
    fmpt2dOLD.1 $e |- ( ph -> ( x e. A -> B e. V ) ) $.
    fmpt2dOLD.2 $e |- F = ( x e. A |-> B ) $.
    fmpt2dOLD.3 $e |- ( ph -> ( y e. A -> ( F ` y ) e. C ) ) $.
    $( Domain and codomain of the mapping operation; deduction form.
       (Contributed by NM, 9-Apr-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    fmpt2dOLD $p |- ( ph -> F : A --> C ) $=
      wph vx vy cA cB cC cF cV wph vx cv cA wcel cB cV wcel fmpt2dOLD.1 imp cF
      vx cA cB cmpt wceq wph fmpt2dOLD.2 a1i wph vy cv cA wcel vy cv cF cfv cC
      wcel fmpt2dOLD.3 imp fmpt2d $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.
    $( A necessary and sufficient condition for a restricted function.
       (Contributed by Mario Carneiro, 14-Nov-2013.) $)
    ffvresb $p |- ( Fun F -> ( ( F |` A ) : A --> B <->
        A. x e. A ( x e. dom F /\ ( F ` x ) e. B ) ) ) $=
      cF wfun cA cB cF cA cres wf vx cv cF cdm wcel vx cv cF cfv cB wcel wa vx
      cA wral cA cB cF cA cres wf vx cv cF cdm wcel vx cv cF cfv cB wcel wa vx
      cA cA cB cF cA cres wf vx cv cA wcel wa vx cv cF cdm wcel vx cv cF cfv cB
      wcel cA cB cF cA cres wf cA cF cdm vx cv cA cB cF cA cres wf cA cF cA
      cres cdm cF cdm cA cB cF cA cres fdm cF cA cres cdm cF cdm wss cA cB cF
      cA cres wf cF cA cres cdm cA cF cdm cin cF cdm cF cA dmres cA cF cdm
      inss2 eqsstri a1i eqsstr3d sselda cA cB cF cA cres wf vx cv cA wcel wa vx
      cv cF cA cres cfv vx cv cF cfv cB vx cv cA wcel vx cv cF cA cres cfv vx
      cv cF cfv wceq cA cB cF cA cres wf vx cv cA cF fvres adantl cA cB vx cv
      cF cA cres ffvelrn eqeltrrd jca ralrimiva cF wfun vx cv cF cdm wcel vx cv
      cF cfv cB wcel wa vx cA wral cA cB cF cA cres wf cF wfun vx cv cF cdm
      wcel vx cv cF cfv cB wcel wa vx cA wral wa cF cA cres cA wfn cF cA cres
      crn cB wss cA cB cF cA cres wf vx cv cF cdm wcel vx cv cF cfv cB wcel wa
      vx cA wral cF wfun cA cF cdm wss cF cA cres cA wfn vx cv cF cdm wcel vx
      cv cF cfv cB wcel wa vx cA wral vx cv cF cdm wcel vx cA wral cA cF cdm
      wss vx cv cF cdm wcel vx cv cF cfv cB wcel wa vx cv cF cdm wcel vx cA vx
      cv cF cdm wcel vx cv cF cfv cB wcel simpl ralimi vx cA cF cdm dfss3
      sylibr cF wfun cF cF cdm wfn cA cF cdm wss cF cA cres cA wfn cF funfn cF
      cdm cA cF fnssres sylanb sylan2 cF wfun vx cv cF cdm wcel vx cv cF cfv cB
      wcel wa vx cA wral wa cF cA cres cA wfn vx cv cF cA cres cfv cB wcel vx
      cA wral cF cA cres crn cB wss vx cv cF cdm wcel vx cv cF cfv cB wcel wa
      vx cA wral cF wfun cA cF cdm wss cF cA cres cA wfn vx cv cF cdm wcel vx
      cv cF cfv cB wcel wa vx cA wral vx cv cF cdm wcel vx cA wral cA cF cdm
      wss vx cv cF cdm wcel vx cv cF cfv cB wcel wa vx cv cF cdm wcel vx cA vx
      cv cF cdm wcel vx cv cF cfv cB wcel simpl ralimi vx cA cF cdm dfss3
      sylibr cF wfun cF cF cdm wfn cA cF cdm wss cF cA cres cA wfn cF funfn cF
      cdm cA cF fnssres sylanb sylan2 vx cv cF cdm wcel vx cv cF cfv cB wcel wa
      vx cA wral vx cv cF cA cres cfv cB wcel vx cA wral cF wfun vx cv cF cdm
      wcel vx cv cF cfv cB wcel wa vx cv cF cA cres cfv cB wcel vx cA vx cv cF
      cdm wcel vx cv cF cfv cB wcel wa vx cv cF cA cres cfv cB wcel vx cv cA
      wcel vx cv cF cfv cB wcel vx cv cF cdm wcel vx cv cF cfv cB wcel simpr vx
      cv cA wcel vx cv cF cA cres cfv vx cv cF cfv cB vx cv cA cF fvres eleq1d
      syl5ibr ralimia adantl vx cA cB cF cA cres fnfvrnss syl2anc cA cB cF cA
      cres df-f sylanbrc ex impbid2 $.
  $}

  ${
    $d u v w x z A $.  $d u x y B $.  $d u w z F $.  $d u w z G $.  $d u y R $.
    $d u w x z ph $.  $d u x S $.  $d u v w y z T $.
    fmptco.1 $e |- ( ( ph /\ x e. A ) -> R e. B ) $.
    fmptco.2 $e |- ( ph -> F = ( x e. A |-> R ) ) $.
    fmptco.3 $e |- ( ph -> G = ( y e. B |-> S ) ) $.
    fmptco.4 $e |- ( y = R -> S = T ) $.
    $( Composition of two functions expressed as ordered-pair class
       abstractions.  If ` F ` has the equation ` ( x + 2 ) ` and ` G ` the
       equation ` ( 3 * z ) ` then ` ( G o. F ) ` has the equation
       ` ( 3 * ( x + 2 ) ) ` .  (Contributed by FL, 21-Jun-2012.)  (Revised by
       Mario Carneiro, 24-Jul-2014.) $)
    fmptco $p |- ( ph -> ( G o. F ) = ( x e. A |-> T ) ) $=
      wph vz vw cG cF ccom vx cA cT cmpt cG cF relco vx cA cT cmpt wfun vx cA
      cT cmpt wrel vx cA cT funmpt vx cA cT cmpt funrel ax-mp wph vz cv vu cv
      cF wbr vu cv vw cv cG wbr wa vu wex vz cv cA wcel vw cv vx vz cv cT csb
      wceq wa vz cv vw cv cop cG cF ccom wcel vz cv vw cv cop vx cA cT cmpt
      wcel wph vz cv vu cv cF wbr vu cv vw cv cG wbr wa vu wex vu cv vz cv cF
      cfv wceq vz cv vu cv cF wbr vu cv vw cv cG wbr wa wa vu wex vz cv cA wcel
      vw cv vx vz cv cT csb wceq wa wph vz cv vu cv cF wbr vu cv vw cv cG wbr
      wa vu cv vz cv cF cfv wceq vz cv vu cv cF wbr vu cv vw cv cG wbr wa wa vu
      wph vz cv vu cv cF wbr vu cv vw cv cG wbr wa vu cv vz cv cF cfv wceq wph
      vz cv vu cv cF wbr vu cv vw cv cG wbr vu cv vz cv cF cfv wceq wph vz cv
      vu cv cF wbr wa vu cv vz cv cF cfv wceq vu cv vw cv cG wbr wph vz cv vu
      cv cF wbr wa vz cv cF cfv vu cv wph cF wfun vz cv vu cv cF wbr vz cv cF
      cfv vu cv wceq wph cA cB cF wf cF wfun wph cA cB cF wf cA cB vx cA cR
      cmpt wf wph vx cA cR cB vx cA cR cmpt fmptco.1 vx cA cR cmpt eqid fmptd
      wph cA cB cF vx cA cR cmpt fmptco.2 feq1d mpbird cA cB cF ffun syl cF
      wfun vz cv vu cv cF wbr vz cv cF cfv vu cv wceq vz cv vu cv cF funbrfv
      imp sylan eqcomd a1d expimpd pm4.71rd exbidv vu cv vz cv cF cfv wceq vz
      cv vu cv cF wbr vu cv vw cv cG wbr wa wa vu wex vz cv vz cv cF cfv cF wbr
      vz cv cF cfv vw cv cG wbr wa wph vz cv cA wcel vw cv vx vz cv cT csb wceq
      wa vz cv vu cv cF wbr vu cv vw cv cG wbr wa vz cv vz cv cF cfv cF wbr vz
      cv cF cfv vw cv cG wbr wa vu vz cv cF cfv vz cv cF fvex vu cv vz cv cF
      cfv wceq vz cv vu cv cF wbr vz cv vz cv cF cfv cF wbr vu cv vw cv cG wbr
      vz cv cF cfv vw cv cG wbr vu cv vz cv cF cfv vz cv cF breq2 vu cv vz cv
      cF cfv vw cv cG breq1 anbi12d ceqsexv wph vz cv vz cv cF cfv cF wbr vz cv
      cF cfv vw cv cG wbr wa vz cv cA wcel vz cv vx cA cR cmpt cfv vw cv vy cB
      cS cmpt wbr wa vz cv cA wcel vw cv vx vz cv cT csb wceq wa wph vz cv vz
      cv cF cfv cF wbr vz cv cA wcel vz cv cF cfv vw cv cG wbr vz cv vx cA cR
      cmpt cfv vw cv vy cB cS cmpt wbr wph vz cv cF cdm wcel vz cv vz cv cF cfv
      cF wbr vz cv cA wcel wph cF wfun vz cv cF cdm wcel vz cv vz cv cF cfv cF
      wbr wb wph cA cB cF wf cF wfun wph cA cB cF wf cA cB vx cA cR cmpt wf wph
      vx cA cR cB vx cA cR cmpt fmptco.1 vx cA cR cmpt eqid fmptd wph cA cB cF
      vx cA cR cmpt fmptco.2 feq1d mpbird cA cB cF ffun syl vz cv cF funfvbrb
      syl wph cF cdm cA vz cv wph cA cB cF wf cF cdm cA wceq wph cA cB cF wf cA
      cB vx cA cR cmpt wf wph vx cA cR cB vx cA cR cmpt fmptco.1 vx cA cR cmpt
      eqid fmptd wph cA cB cF vx cA cR cmpt fmptco.2 feq1d mpbird cA cB cF fdm
      syl eleq2d bitr3d wph vz cv cF cfv vz cv vx cA cR cmpt cfv vw cv vw cv cG
      vy cB cS cmpt wph vz cv cF vx cA cR cmpt fmptco.2 fveq1d fmptco.3 wph vw
      cv eqidd breq123d anbi12d wph vz cv cA wcel vz cv vx cA cR cmpt cfv vw cv
      vy cB cS cmpt wbr vw cv vx vz cv cT csb wceq vz cv cA wcel wph vz cv vx
      cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv vx vz cv cT csb wceq wb wph
      vx cv vx cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv cT wceq wb wi wph
      vz cv vx cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv vx vz cv cT csb
      wceq wb wi vx vz cv cA vx vz cv nfcv wph vz cv vx cA cR cmpt cfv vw cv vy
      cB cS cmpt wbr vw cv vx vz cv cT csb wceq wb vx wph vx nfv vz cv vx cA cR
      cmpt cfv vw cv vy cB cS cmpt wbr vw cv vx vz cv cT csb wceq vx vx vz cv
      vx cA cR cmpt cfv vw cv vy cB cS cmpt vx vz cv vx cA cR cmpt vx cA cR
      nfmpt1 vx vz cv nfcv nffv vx vy cB cS cmpt nfcv vx vw cv nfcv nfbr vx vw
      cv vx vz cv cT csb vx vz cv cT nfcsb1v nfeq2 nfbi nfim vx cv vz cv wceq
      vx cv vx cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv cT wceq wb vz cv vx
      cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv vx vz cv cT csb wceq wb wph
      vx cv vz cv wceq vx cv vx cA cR cmpt cfv vw cv vy cB cS cmpt wbr vz cv vx
      cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv cT wceq vw cv vx vz cv cT
      csb wceq vx cv vz cv wceq vx cv vx cA cR cmpt cfv vz cv vx cA cR cmpt cfv
      vw cv vy cB cS cmpt vx cv vz cv vx cA cR cmpt fveq2 breq1d vx cv vz cv
      wceq cT vx vz cv cT csb vw cv vx vz cv cT csbeq1a eqeq2d bibi12d imbi2d
      wph vx cv cA wcel vx cv vx cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv
      cT wceq wb wph vx cv cA wcel wa cR vw cv vy cB cS cmpt wbr cR cB wcel vw
      cv cT wceq wa vx cv vx cA cR cmpt cfv vw cv vy cB cS cmpt wbr vw cv cT
      wceq wph vx cv cA wcel wa cR cB wcel vw cv cvv wcel cR vw cv vy cB cS
      cmpt wbr cR cB wcel vw cv cT wceq wa wb fmptco.1 vw vex vy cv cB wcel vu
      cv cS wceq wa cR cB wcel vw cv cT wceq wa vy vu cR vw cv vy cB cS cmpt cB
      cvv vy cv cR wceq vu cv vw cv wceq wa vy cv cB wcel cR cB wcel vu cv cS
      wceq vw cv cT wceq vy cv cR wceq vu cv vw cv wceq wa vy cv cR cB vy cv cR
      wceq vu cv vw cv wceq simpl eleq1d vy cv cR wceq vu cv vw cv wceq wa vu
      cv vw cv cS cT vy cv cR wceq vu cv vw cv wceq simpr vy cv cR wceq cS cT
      wceq vu cv vw cv wceq fmptco.4 adantr eqeq12d anbi12d vy vu cB cS df-mpt
      brabga sylancl wph vx cv cA wcel wa vx cv vx cA cR cmpt cfv cR vw cv vy
      cB cS cmpt wph vx cv cA wcel wa vx cv cA wcel cR cB wcel vx cv vx cA cR
      cmpt cfv cR wceq wph vx cv cA wcel simpr fmptco.1 vx cA cR cB vx cA cR
      cmpt vx cA cR cmpt eqid fvmpt2 syl2anc breq1d wph vx cv cA wcel wa cR cB
      wcel vw cv cT wceq fmptco.1 biantrurd 3bitr4d expcom vtoclgaf impcom
      pm5.32da bitrd syl5bb bitrd vu vz cv vw cv cG cF vz vex vw vex opelco vz
      cv vw cv cop vx cA cT cmpt wcel vz cv vw cv cop vx cv cA wcel vv cv cT
      wceq wa vx vv copab wcel vz cv cA wcel vw cv vx vz cv cT csb wceq wa vx
      cA cT cmpt vx cv cA wcel vv cv cT wceq wa vx vv copab vz cv vw cv cop vx
      vv cA cT df-mpt eleq2i vx cv cA wcel vv cv cT wceq wa vz cv cA wcel vv cv
      vx vz cv cT csb wceq wa vz cv cA wcel vw cv vx vz cv cT csb wceq wa vx vv
      vz cv vw cv vz cv cA wcel vv cv vx vz cv cT csb wceq vx vz cv cA wcel vx
      nfv vx vv cv vx vz cv cT csb vx vz cv cT nfcsb1v nfeq2 nfan vz cv cA wcel
      vw cv vx vz cv cT csb wceq wa vv nfv vz vex vw vex vx cv vz cv wceq vx cv
      cA wcel vz cv cA wcel vv cv cT wceq vv cv vx vz cv cT csb wceq vx cv vz
      cv cA eleq1 vx cv vz cv wceq cT vx vz cv cT csb vv cv vx vz cv cT csbeq1a
      eqeq2d anbi12d vv cv vw cv wceq vv cv vx vz cv cT csb wceq vw cv vx vz cv
      cT csb wceq vz cv cA wcel vv cv vw cv vx vz cv cT csb eqeq1 anbi2d
      opelopabf bitri 3bitr4g eqrelrdv $.
  $}

  ${
    $d w x y z B $.  $d w y z R $.  $d w x z S $.  $d x z A $.  $d y z T $.
    $d z ph $.
    fmptcof.1 $e |- ( ph -> A. x e. A R e. B ) $.
    fmptcof.2 $e |- ( ph -> F = ( x e. A |-> R ) ) $.
    fmptcof.3 $e |- ( ph -> G = ( y e. B |-> S ) ) $.
    ${
      fmptcof.4 $e |- ( y = R -> S = T ) $.
      $( Version of ~ fmptco where ` ph ` needn't be distinct from ` x ` .
         (Contributed by NM, 27-Dec-2014.) $)
      fmptcof $p |- ( ph -> ( G o. F ) = ( x e. A |-> T ) ) $=
        wph cG cF ccom vx cA vy cR cS csb cmpt vx cA cT cmpt wph cG cF ccom vz
        cA vy vx vz cv cR csb cS csb cmpt vx cA vy cR cS csb cmpt wph vz vw cA
        cB vx vz cv cR csb vy vw cv cS csb vy vx vz cv cR csb cS csb cF cG wph
        cR cB wcel vx cA wral vz cv cA wcel vx vz cv cR csb cB wcel fmptcof.1
        cR cB wcel vx vz cv cR csb cB wcel vx vz cv cA vx vx vz cv cR csb cB vx
        vz cv cR nfcsb1v nfel1 vx cv vz cv wceq cR vx vz cv cR csb cB vx vz cv
        cR csbeq1a eleq1d rspc mpan9 wph cF vx cA cR cmpt vz cA vx vz cv cR csb
        cmpt fmptcof.2 vx vz cA cR vx vz cv cR csb vz cR nfcv vx vz cv cR
        nfcsb1v vx vz cv cR csbeq1a cbvmpt syl6eq wph cG vy cB cS cmpt vw cB vy
        vw cv cS csb cmpt fmptcof.3 vy vw cB cS vy vw cv cS csb vw cS nfcv vy
        vw cv cS nfcsb1v vy vw cv cS csbeq1a cbvmpt syl6eq vy vw cv vx vz cv cR
        csb cS csbeq1 fmptco vx vz cA vy cR cS csb vy vx vz cv cR csb cS csb vz
        vy cR cS csb nfcv vx vy vx vz cv cR csb cS vx vz cv cR nfcsb1v vx cS
        nfcv nfcsb vx cv vz cv wceq vy cR vx vz cv cR csb cS vx vz cv cR
        csbeq1a csbeq1d cbvmpt syl6eqr wph cR cB wcel vx cA wral vx cA vy cR cS
        csb cmpt vx cA cT cmpt wceq fmptcof.1 cR cB wcel vx cA wral cA cA wceq
        vy cR cS csb cT wceq vx cA wral vx cA vy cR cS csb cmpt vx cA cT cmpt
        wceq cA eqid cR cB wcel vy cR cS csb cT wceq vx cA vy cR cS cT cB cR cB
        wcel vy cT nfcvd fmptcof.4 csbiegf ralimi vx cA vy cR cS csb cA cT
        mpteq12 sylancr syl eqtrd $.
    $}

    $( Composition of two functions expressed as mapping abstractions.
       (Contributed by NM, 22-May-2006.)  (Revised by Mario Carneiro,
       31-Aug-2015.) $)
    fmptcos $p |- ( ph -> ( G o. F ) = ( x e. A |-> [_ R / y ]_ S ) ) $=
      wph vx vz cA cB cR vy vz cv cS csb vy cR cS csb cF cG fmptcof.1 fmptcof.2
      wph cG vy cB cS cmpt vz cB vy vz cv cS csb cmpt fmptcof.3 vy vz cB cS vy
      vz cv cS csb vz cS nfcv vy vz cv cS nfcsb1v vy vz cv cS csbeq1a cbvmpt
      syl6eq vy vz cv cR cS csbeq1 fmptcof $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x C $.  $d x y D $.  $d x E $.
    $( Express composition of two functions as a maps-to applying both in
       sequence.  (Contributed by Stefan O'Rear, 5-Oct-2014.)  (Proof shortened
       by Mario Carneiro, 27-Dec-2014.) $)
    fcompt $p |- ( ( A : D --> E /\ B : C --> D ) -> ( A o. B ) = ( x e. C |->
        ( A ` ( B ` x ) ) ) ) $=
      cD cE cA wf cC cD cB wf wa vx vy cC cD vx cv cB cfv vy cv cA cfv vx cv cB
      cfv cA cfv cB cA cC cD cB wf vx cv cC wcel vx cv cB cfv cD wcel cD cE cA
      wf cC cD vx cv cB ffvelrn adantll cD cE cA wf cC cD cB wf wa cB cC wfn cB
      vx cC vx cv cB cfv cmpt wceq cC cD cB wf cB cC wfn cD cE cA wf cC cD cB
      ffn adantl vx cC cB dffn5 sylib cD cE cA wf cC cD cB wf wa cA cD wfn cA
      vy cD vy cv cA cfv cmpt wceq cD cE cA wf cA cD wfn cC cD cB wf cD cE cA
      ffn adantr vy cD cA dffn5 sylib vy cv vx cv cB cfv cA fveq2 fmptco $.
  $}

  ${
    $d F x y $.  $d I x $.  $d X x y $.  $d Y x y $.
    $( Composition with a constant function.  (Contributed by Stefan O'Rear,
       11-Mar-2015.) $)
    fcoconst $p |- ( ( F Fn X /\ Y e. X ) ->
        ( F o. ( I X. { Y } ) ) = ( I X. { ( F ` Y ) } ) ) $=
      cF cX wfn cY cX wcel wa cF cI cY csn cxp ccom vx cI cY cF cfv cmpt cI cY
      cF cfv csn cxp cF cX wfn cY cX wcel wa vx vy cI cX cY vy cv cF cfv cY cF
      cfv cI cY csn cxp cF cF cX wfn cY cX wcel vx cv cI wcel simplr cI cY csn
      cxp vx cI cY cmpt wceq cF cX wfn cY cX wcel wa vx cI cY fconstmpt a1i cF
      cX wfn cY cX wcel wa vy cX cvv cF cF cX wfn cY cX wcel wa cF cX wfn cX
      cvv cF wf cF cX wfn cY cX wcel simpl cX cF dffn2 sylib feqmptd vy cv cY
      cF fveq2 fmptco vx cI cY cF cfv fconstmpt syl6eqr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.
    fsn.1 $e |- A e. _V $.
    fsn.2 $e |- B e. _V $.
    $( A function maps a singleton to a singleton iff it is the singleton of an
       ordered pair.  (Contributed by NM, 10-Dec-2003.) $)
    fsn $p |- ( F : { A } --> { B } <-> F = { <. A , B >. } ) $=
      cA csn cB csn cF wf cF cA cB cop csn wceq cA csn cB csn cF wf cF cA cB
      cop csn wceq vx cv vy cv cop cF wcel vx cv vy cv cop cA cB cop csn wcel
      wb vy wal vx wal cA csn cB csn cF wf vx cv vy cv cop cF wcel vx cv vy cv
      cop cA cB cop csn wcel wb vx vy cA csn cB csn cF wf vx cv vy cv cop cF
      wcel vx cv cA wceq vy cv cB wceq wa vx cv vy cv cop cA cB cop csn wcel cA
      csn cB csn cF wf vx cv vy cv cop cF wcel vx cv cA wceq vy cv cB wceq wa
      cA csn cB csn cF wf vx cv vy cv cop cF wcel vx cv cA wceq vy cv cB wceq
      wa cA csn cB csn cF wf vx cv vy cv cop cF wcel wa vx cv cA csn wcel vy cv
      cB csn wcel wa vx cv cA wceq vy cv cB wceq wa cA csn cB csn vx cv vy cv
      cF opelf vx cv cA csn wcel vx cv cA wceq vy cv cB csn wcel vy cv cB wceq
      vx cA elsn vy cB elsn anbi12i sylib ex cA csn cB csn cF wf vx cv vy cv
      cop cF wcel vx cv cA wceq vy cv cB wceq wa cA cB cop cF wcel cA csn cB
      csn cF wf cA vy cv cop cF wcel vy cB csn wreu cA cB cop cF wcel cA csn cB
      csn cF wf cA cA csn wcel cA vy cv cop cF wcel vy cB csn wreu cA fsn.1
      snid vy cA csn cB csn cA cF feu mpan2 cA cB cop cF wcel vy cv cB wceq wa
      vy weu vy cv cB csn wcel cA vy cv cop cF wcel wa vy weu cA cB cop cF wcel
      cA vy cv cop cF wcel vy cB csn wreu cA cB cop cF wcel vy cv cB wceq wa vy
      cv cB csn wcel cA vy cv cop cF wcel wa vy vy cv cB csn wcel cA vy cv cop
      cF wcel wa vy cv cB wceq cA vy cv cop cF wcel wa cA cB cop cF wcel vy cv
      cB wceq wa vy cv cB csn wcel vy cv cB wceq cA vy cv cop cF wcel vy cB
      elsn anbi1i vy cv cB wceq cA vy cv cop cF wcel wa vy cv cB wceq cA cB cop
      cF wcel wa cA cB cop cF wcel vy cv cB wceq wa vy cv cB wceq cA vy cv cop
      cF wcel cA cB cop cF wcel vy cv cB wceq cA vy cv cop cA cB cop cF vy cv
      cB cA opeq2 eleq1d pm5.32i cA cB cop cF wcel vy cv cB wceq ancom bitr4i
      bitr2i eubii cA cB cop cF wcel cA cB cop cF wcel vy cv cB wceq vy weu wa
      cA cB cop cF wcel vy cv cB wceq wa vy weu vy cv cB wceq vy weu cA cB cop
      cF wcel vy cB fsn.2 eueq1 biantru cA cB cop cF wcel vy cv cB wceq vy
      euanv bitr4i cA vy cv cop cF wcel vy cB csn df-reu 3bitr4i sylibr vx cv
      cA wceq vy cv cB wceq wa vx cv vy cv cop cA cB cop cF vx cv vy cv cA cB
      opeq12 eleq1d syl5ibrcom impbid vx cv vy cv cop cA cB cop csn wcel vx cv
      vy cv cop cA cB cop wceq vx cv cA wceq vy cv cB wceq wa vx cv vy cv cop
      cA cB cop vx cv vy cv opex elsnc vx cv vy cv cA cB fsn.1 fsn.2 opth2
      bitr2i syl6bb alrimivv cA csn cB csn cF wf cF wrel cA cB cop csn wrel cF
      cA cB cop csn wceq vx cv vy cv cop cF wcel vx cv vy cv cop cA cB cop csn
      wcel wb vy wal vx wal wb cA csn cB csn cF frel cA cB fsn.1 fsn.2 relsnop
      vx vy cF cA cB cop csn eqrel sylancl mpbird cF cA cB cop csn wceq cA csn
      cB csn cF wf1o cA csn cB csn cF wf cF cA cB cop csn wceq cA csn cB csn cF
      wf1o cA csn cB csn cA cB cop csn wf1o cA cB fsn.1 fsn.2 f1osn cA csn cB
      csn cF cA cB cop csn f1oeq1 mpbiri cA csn cB csn cF f1of syl impbii $.
  $}

  ${
    $d A a b $.  $d B b $.  $d F a b $.
    $( A function maps a singleton to a singleton iff it is the singleton of an
       ordered pair.  (Contributed by NM, 26-Oct-2012.) $)
    fsng $p |- ( ( A e. C /\ B e. D ) ->
                 ( F : { A } --> { B } <-> F = { <. A , B >. } ) ) $=
      va cv csn vb cv csn cF wf cF va cv vb cv cop csn wceq wb cA csn vb cv csn
      cF wf cF cA vb cv cop csn wceq wb cA csn cB csn cF wf cF cA cB cop csn
      wceq wb va vb cA cB cC cD va cv cA wceq va cv csn vb cv csn cF wf cA csn
      vb cv csn cF wf cF va cv vb cv cop csn wceq cF cA vb cv cop csn wceq va
      cv cA wceq va cv csn cA csn vb cv csn cF va cv cA sneq feq2d va cv cA
      wceq va cv vb cv cop csn cA vb cv cop csn cF va cv cA wceq va cv vb cv
      cop cA vb cv cop va cv cA vb cv opeq1 sneqd eqeq2d bibi12d vb cv cB wceq
      cA csn vb cv csn cF wf cA csn cB csn cF wf cF cA vb cv cop csn wceq cF cA
      cB cop csn wceq vb cv cB wceq vb cv csn cB csn wceq cA csn vb cv csn cF
      wf cA csn cB csn cF wf wb vb cv cB sneq vb cv csn cB csn cA csn cF feq3
      syl vb cv cB wceq cA vb cv cop csn cA cB cop csn cF vb cv cB wceq cA vb
      cv cop cA cB cop vb cv cB cA opeq2 sneqd eqeq2d bibi12d va cv vb cv cF va
      vex vb vex fsn vtocl2g $.
  $}

  ${
    fsn2.1 $e |- A e. _V $.
    $( A function that maps a singleton to a class is the singleton of an
       ordered pair.  (Contributed by NM, 19-May-2004.) $)
    fsn2 $p |- ( F : { A } --> B <->
               ( ( F ` A ) e. B /\ F = { <. A , ( F ` A ) >. } ) ) $=
      cA csn cB cF wf cA cF cfv cB wcel cA csn cA cF cfv csn cF wf wa cA cF cfv
      cB wcel cF cA cA cF cfv cop csn wceq wa cA csn cB cF wf cA cF cfv cB wcel
      cA csn cA cF cfv csn cF wf wa cA csn cB cF wf cA cF cfv cB wcel cA csn cA
      cF cfv csn cF wf cA csn cB cF wf cA cA csn wcel cA cF cfv cB wcel cA
      fsn2.1 snid cA csn cB cA cF ffvelrn mpan2 cA csn cB cF wf cF cA csn wfn
      cA csn cA cF cfv csn cF wf cA csn cB cF ffn cF cA csn wfn cA csn cF crn
      cF wf cA csn cA cF cfv csn cF wf cF cA csn wfn cA csn cF crn cF wf cA csn
      cF dffn3 biimpi cF cA csn wfn cF crn cA cF cfv csn wceq cA csn cF crn cF
      wf cA csn cA cF cfv csn cF wf wb cF cA csn wfn cF crn cF cA csn cima cA
      cF cfv csn cF cA csn wfn cF crn cF cF cdm cima cF cA csn cima cF imadmrn
      cF cA csn wfn cF cdm cA csn cF cA csn cF fndm imaeq2d syl5eqr cF cA csn
      wfn cA cA csn wcel cA cF cfv csn cF cA csn cima wceq cA fsn2.1 snid cA
      csn cA cF fnsnfv mpan2 eqtr4d cF crn cA cF cfv csn cA csn cF feq3 syl
      mpbid syl jca cA cF cfv cB wcel cA cF cfv csn cB wss cA csn cA cF cfv csn
      cF wf cA csn cB cF wf cA cF cfv cB snssi cA csn cA cF cfv csn cF wf cA cF
      cfv csn cB wss cA csn cB cF wf cA csn cA cF cfv csn cB cF fss ancoms
      sylan impbii cA csn cA cF cfv csn cF wf cF cA cA cF cfv cop csn wceq cA
      cF cfv cB wcel cA cA cF cfv cF fsn2.1 cA cF fvex fsn anbi2i bitri $.
  $}

  $( The cross product of two singletons.  (Contributed by Mario Carneiro,
     30-Apr-2015.) $)
  xpsng $p |- ( ( A e. V /\ B e. W ) ->
    ( { A } X. { B } ) = { <. A , B >. } ) $=
    cA cV wcel cB cW wcel wa cA csn cB csn cA csn cB csn cxp wf cA csn cB csn
    cxp cA cB cop csn wceq cB cW wcel cA csn cB csn cA csn cB csn cxp wf cA cV
    wcel cA csn cB cW fconstg adantl cA cB cV cW cA csn cB csn cxp fsng mpbid
    $.

  ${
    xpsn.1 $e |- A e. _V $.
    xpsn.2 $e |- B e. _V $.
    $( The cross product of two singletons.  (Contributed by NM,
       4-Nov-2006.) $)
    xpsn $p |- ( { A } X. { B } ) = { <. A , B >. } $=
      cA cvv wcel cB cvv wcel cA csn cB csn cxp cA cB cop csn wceq xpsn.1
      xpsn.2 cA cB cvv cvv xpsng mp2an $.
  $}

  ${
    dfmpt.1 $e |- B e. _V $.
    $( Alternate definition for the "maps to" notation ~ df-mpt (although it
       requires that ` B ` be a set).  (Contributed by NM, 24-Aug-2010.)
       (Revised by Mario Carneiro, 30-Dec-2016.) $)
    dfmpt $p |- ( x e. A |-> B ) = U_ x e. A { <. x , B >. } $=
      vx cA cB cmpt vx cA vx cv csn cB csn cxp ciun vx cA vx cv cB cop csn ciun
      vx cA cB dfmpt3 vx cA vx cv csn cB csn cxp vx cv cB cop csn vx cv csn cB
      csn cxp vx cv cB cop csn wceq vx cv cA wcel vx cv cB vx vex dfmpt.1 xpsn
      a1i iuneq2i eqtri $.

    $d x y $.  $d y A $.  $d y B $.
    $( A function expressed as the range of another function.  (Contributed by
       Mario Carneiro, 22-Jun-2013.)  (Proof shortened by Mario Carneiro,
       31-Aug-2015.) $)
    fnasrn $p |- ( x e. A |-> B ) = ran ( x e. A |-> <. x , B >. ) $=
      vx cA cB cmpt vx cA vx cv cB cop csn ciun vx cA vx cv cB cop cmpt crn vx
      cA cB dfmpt.1 dfmpt vx cA vx cv cB cop cmpt crn vy cv vx cv cB cop csn
      wcel vx cA wrex vy cab vx cA vx cv cB cop csn ciun vx cA vx cv cB cop
      cmpt crn vy cv vx cv cB cop wceq vx cA wrex vy cab vy cv vx cv cB cop csn
      wcel vx cA wrex vy cab vx vy cA vx cv cB cop vx cA vx cv cB cop cmpt vx
      cA vx cv cB cop cmpt eqid rnmpt vy cv vx cv cB cop csn wcel vx cA wrex vy
      cv vx cv cB cop wceq vx cA wrex vy vy cv vx cv cB cop csn wcel vy cv vx
      cv cB cop wceq vx cA vy vx cv cB cop elsn rexbii abbii eqtr4i vx vy cA vx
      cv cB cop csn df-iun eqtr4i eqtr4i $.
  $}

  $( If ` A ` is not in ` C ` , then the restriction of a singleton of
     ` <. A , B >. ` to ` C ` is null.  (Contributed by Scott Fenton,
     15-Apr-2011.) $)
  ressnop0 $p |- ( -. A e. C -> ( { <. A , B >. } |` C ) = (/) ) $=
    cA cC wcel wn cA cB cop cC cvv cxp wcel wn cA cB cop csn cC cres c0 wceq cA
    cB cop cC cvv cxp wcel cA cC wcel cA cB cC cvv opelxp1 con3i cA cB cop cC
    cvv cxp wcel wn cA cB cop csn cC cres cC cvv cxp cA cB cop csn cin c0 cA cB
    cop csn cC cres cA cB cop csn cC cvv cxp cin cC cvv cxp cA cB cop csn cin
    cA cB cop csn cC df-res cA cB cop csn cC cvv cxp incom eqtri cC cvv cxp cA
    cB cop csn cin c0 wceq cA cB cop cC cvv cxp wcel wn cC cvv cxp cA cB cop
    disjsn biimpri syl5eq syl $.

  ${
    fpr.1 $e |- A e. _V $.
    fpr.2 $e |- B e. _V $.
    fpr.3 $e |- C e. _V $.
    fpr.4 $e |- D e. _V $.
    $( A function with a domain of two elements.  (Contributed by Jeff Madsen,
       20-Jun-2010.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
    fpr $p |- ( A =/= B
                -> { <. A , C >. , <. B , D >. } : { A , B } --> { C , D } ) $=
      cA cB wne cA cC cop cB cD cop cpr cA cB cpr wfn cA cC cop cB cD cop cpr
      crn cC cD cpr wss wa cA cB cpr cC cD cpr cA cC cop cB cD cop cpr wf cA cB
      wne cA cC cop cB cD cop cpr cA cB cpr wfn cA cC cop cB cD cop cpr crn cC
      cD cpr wss cA cB wne cA cC cop cB cD cop cpr wfun cA cC cop cB cD cop cpr
      cdm cA cB cpr wceq wa cA cC cop cB cD cop cpr cA cB cpr wfn cA cB wne cA
      cC cop cB cD cop cpr wfun cA cC cop cB cD cop cpr cdm cA cB cpr wceq cA
      cB cC cD fpr.1 fpr.2 fpr.3 fpr.4 funpr cA cC cB cD fpr.3 fpr.4 dmprop
      jctir cA cC cop cB cD cop cpr cA cB cpr df-fn sylibr cA cC cop cB cD cop
      cpr crn cC cD cpr cA cC cop cB cD cop cpr crn cA cC cop csn cB cD cop csn
      cun crn cA cC cop csn crn cB cD cop csn crn cun cC cD cpr cA cC cop cB cD
      cop cpr cA cC cop csn cB cD cop csn cun cA cC cop cB cD cop df-pr rneqi
      cA cC cop csn cB cD cop csn rnun cA cC cop csn crn cB cD cop csn crn cun
      cC csn cD csn cun cC cD cpr cA cC cop csn crn cC csn cB cD cop csn crn cD
      csn cA cC fpr.1 rnsnop cB cD fpr.2 rnsnop uneq12i cC cD df-pr eqtr4i
      3eqtri eqimssi jctir cA cB cpr cC cD cpr cA cC cop cB cD cop cpr df-f
      sylibr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x F $.
    $( A function restricted to a singleton.  (Contributed by NM,
       9-Oct-2004.) $)
    fnressn $p |- ( ( F Fn A /\ B e. A ) ->
                  ( F |` { B } ) = { <. B , ( F ` B ) >. } ) $=
      cB cA wcel cF cA wfn cF cB csn cres cB cB cF cfv cop csn wceq cF cA wfn
      cF vx cv csn cres vx cv vx cv cF cfv cop csn wceq wi cF cA wfn cF cB csn
      cres cB cB cF cfv cop csn wceq wi vx cB cA vx cv cB wceq cF vx cv csn
      cres vx cv vx cv cF cfv cop csn wceq cF cB csn cres cB cB cF cfv cop csn
      wceq cF cA wfn vx cv cB wceq cF vx cv csn cres cF cB csn cres vx cv vx cv
      cF cfv cop csn cB cB cF cfv cop csn vx cv cB wceq vx cv csn cB csn cF vx
      cv cB sneq reseq2d vx cv cB wceq vx cv vx cv cF cfv cop cB cB cF cfv cop
      vx cv cB wceq vx cv cF cfv cB cF cfv wceq vx cv vx cv cF cfv cop cB cB cF
      cfv cop wceq vx cv cB cF fveq2 vx cv vx cv cF cfv cB cB cF cfv opeq12
      mpdan sneqd eqeq12d imbi2d cF cA wfn vx cv cA wcel cF vx cv csn cres vx
      cv vx cv cF cfv cop csn wceq cF cA wfn vx cv cA wcel wa cF vx cv csn cres
      vx cv csn wfn cF vx cv csn cres vx cv vx cv cF cfv cop csn wceq vx cv cA
      wcel cF cA wfn vx cv csn cA wss cF vx cv csn cres vx cv csn wfn vx cv cA
      vx vex snss cA vx cv csn cF fnssres sylan2b cF vx cv csn cres vx cv csn
      wfn vx cv csn cvv cF vx cv csn cres wf vx cv cF vx cv csn cres cfv cvv
      wcel cF vx cv csn cres vx cv vx cv cF vx cv csn cres cfv cop csn wceq wa
      cF vx cv csn cres vx cv vx cv cF cfv cop csn wceq vx cv csn cF vx cv csn
      cres dffn2 vx cv cvv cF vx cv csn cres vx vex fsn2 vx cv cF vx cv csn
      cres cfv cvv wcel cF vx cv csn cres vx cv vx cv cF vx cv csn cres cfv cop
      csn wceq wa cF vx cv csn cres vx cv vx cv cF vx cv csn cres cfv cop csn
      wceq cF vx cv csn cres vx cv vx cv cF cfv cop csn wceq vx cv cF vx cv csn
      cres cfv cvv wcel cF vx cv csn cres vx cv vx cv cF vx cv csn cres cfv cop
      csn wceq vx cv cF vx cv csn cres fvex biantrur vx cv vx cv cF vx cv csn
      cres cfv cop csn vx cv vx cv cF cfv cop csn cF vx cv csn cres vx cv vx cv
      cF vx cv csn cres cfv cop vx cv vx cv cF cfv cop vx cv cF vx cv csn cres
      cfv vx cv cF cfv vx cv vx cv vx cv csn wcel vx cv cF vx cv csn cres cfv
      vx cv cF cfv wceq vx cv vx vex snid vx cv vx cv csn cF fvres ax-mp opeq2i
      sneqi eqeq2i bitr3i 3bitri sylib expcom vtoclga impcom $.

    $( A function restricted to a singleton.  (Contributed by Mario Carneiro,
       16-Nov-2014.) $)
    funressn $p |- ( Fun F -> ( F |` { B } ) C_ { <. B , ( F ` B ) >. } ) $=
      cF wfun cB cF cdm wcel cF cB csn cres cB cB cF cfv cop csn wss cF wfun cB
      cF cdm wcel wa cF cB csn cres cB cB cF cfv cop csn wceq cF cB csn cres cB
      cB cF cfv cop csn wss cF wfun cF cF cdm wfn cB cF cdm wcel cF cB csn cres
      cB cB cF cfv cop csn wceq cF funfn cF cdm cB cF fnressn sylanb cF cB csn
      cres cB cB cF cfv cop csn eqimss syl cF wfun cB cF cdm wcel wn wa cF cB
      csn cres c0 cB cB cF cfv cop csn cF wfun cB cF cdm wcel wn cF cB csn cres
      c0 wceq cB cF cdm wcel wn cF cdm cB csn cin c0 wceq cF wfun cF cB csn
      cres c0 wceq cF cdm cB disjsn cF wfun cF cF cdm wfn cF cdm cB csn cin c0
      wceq cF cB csn cres c0 wceq wb cF funfn cF cdm cB csn cF fnresdisj sylbi
      syl5bbr biimpa c0 cB cB cF cfv cop csn wss cF wfun cB cF cdm wcel wn wa
      cB cB cF cfv cop csn 0ss a1i eqsstrd pm2.61dan $.

    $( The value of a function restricted to a singleton.  (Contributed by NM,
       9-Oct-2004.) $)
    fressnfv $p |- ( ( F Fn A /\ B e. A ) ->
                 ( ( F |` { B } ) : { B } --> C <-> ( F ` B ) e. C ) ) $=
      cB cA wcel cF cA wfn cB csn cC cF cB csn cres wf cB cF cfv cC wcel wb cF
      cA wfn vx cv csn cC cF vx cv csn cres wf vx cv cF cfv cC wcel wb wi cF cA
      wfn cB csn cC cF cB csn cres wf cB cF cfv cC wcel wb wi vx cB cA vx cv cB
      wceq vx cv csn cC cF vx cv csn cres wf vx cv cF cfv cC wcel wb cB csn cC
      cF cB csn cres wf cB cF cfv cC wcel wb cF cA wfn vx cv cB wceq vx cv csn
      cC cF vx cv csn cres wf cB csn cC cF cB csn cres wf vx cv cF cfv cC wcel
      cB cF cfv cC wcel vx cv cB wceq vx cv csn cB csn wceq vx cv csn cC cF vx
      cv csn cres wf cB csn cC cF cB csn cres wf wb vx cv cB sneq vx cv csn cB
      csn wceq vx cv csn cC cF vx cv csn cres wf vx cv csn cC cF cB csn cres wf
      cB csn cC cF cB csn cres wf vx cv csn cB csn wceq vx cv csn cC cF vx cv
      csn cres cF cB csn cres vx cv csn cB csn cF reseq2 feq1d vx cv csn cB csn
      cC cF cB csn cres feq2 bitrd syl vx cv cB wceq vx cv cF cfv cB cF cfv cC
      vx cv cB cF fveq2 eleq1d bibi12d imbi2d cF cA wfn vx cv cA wcel vx cv csn
      cC cF vx cv csn cres wf vx cv cF cfv cC wcel wb cF cA wfn vx cv cA wcel
      wa cF vx cv csn cres vx cv vx cv cF cfv cop csn wceq vx cv csn cC cF vx
      cv csn cres wf vx cv cF cfv cC wcel wb cA vx cv cF fnressn cF vx cv csn
      cres vx cv vx cv cF cfv cop csn wceq cF vx cv csn cres vx cv vx cv cF vx
      cv csn cres cfv cop csn wceq vx cv csn cC cF vx cv csn cres wf vx cv cF
      cfv cC wcel wb vx cv vx cv cF vx cv csn cres cfv cop csn vx cv vx cv cF
      cfv cop csn cF vx cv csn cres vx cv vx cv cF vx cv csn cres cfv cop vx cv
      vx cv cF cfv cop vx cv cF vx cv csn cres cfv vx cv cF cfv vx cv vx cv vx
      cv csn wcel vx cv cF vx cv csn cres cfv vx cv cF cfv wceq vx cv vx vex
      snid vx cv vx cv csn cF fvres ax-mp opeq2i sneqi eqeq2i vx cv csn cC cF
      vx cv csn cres wf vx cv cF vx cv csn cres cfv cC wcel cF vx cv csn cres
      vx cv vx cv cF vx cv csn cres cfv cop csn wceq wa cF vx cv csn cres vx cv
      vx cv cF vx cv csn cres cfv cop csn wceq vx cv cF cfv cC wcel vx cv cC cF
      vx cv csn cres vx vex fsn2 vx cv cF cfv cC wcel vx cv cF vx cv csn cres
      cfv cC wcel cF vx cv csn cres vx cv vx cv cF vx cv csn cres cfv cop csn
      wceq vx cv cF vx cv csn cres cfv cC wcel cF vx cv csn cres vx cv vx cv cF
      vx cv csn cres cfv cop csn wceq wa vx cv cF vx cv csn cres cfv vx cv cF
      cfv cC vx cv vx cv csn wcel vx cv cF vx cv csn cres cfv vx cv cF cfv wceq
      vx cv vx vex snid vx cv vx cv csn cF fvres ax-mp eleq1i cF vx cv csn cres
      vx cv vx cv cF vx cv csn cres cfv cop csn wceq vx cv cF vx cv csn cres
      cfv cC wcel iba syl5rbbr syl5bb sylbir syl expcom vtoclga impcom $.
  $}

  $( The value of a constant function.  (Contributed by NM, 30-May-1999.) $)
  fvconst $p |- ( ( F : A --> { B } /\ C e. A ) -> ( F ` C ) = B ) $=
    cA cB csn cF wf cC cA wcel wa cC cF cfv cB csn wcel cC cF cfv cB wceq cA cB
    csn cC cF ffvelrn cC cF cfv cB elsni syl $.

  ${
    $d x A $.  $d x B $.
    $( Express a singleton function in maps-to notation.  (Contributed by NM,
       6-Jun-2006.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.)  (Revised
       by Stefan O'Rear, 28-Feb-2015.) $)
    fmptsn $p |- ( ( A e. V /\ B e. W ) ->
        { <. A , B >. } = ( x e. { A } |-> B ) ) $=
      cA cV wcel cB cW wcel wa vx cA csn cB cmpt cA csn cB csn cxp cA cB cop
      csn vx cA csn cB fconstmpt cA cB cV cW xpsng syl5reqr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x R $.  $d x S $.
    fmptap.0a $e |- A e. _V $.
    fmptap.0b $e |- B e. _V $.
    fmptap.1 $e |- ( R u. { A } ) = S $.
    fmptap.2 $e |- ( x = A -> C = B ) $.
    $( Append an additional value to a function.  (Contributed by NM,
       6-Jun-2006.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    fmptap $p |- ( ( x e. R |-> C ) u. { <. A , B >. } ) = ( x e. S |-> C ) $=
      vx cR cC cmpt cA cB cop csn cun vx cR cC cmpt vx cA csn cC cmpt cun vx cR
      cA csn cun cC cmpt vx cS cC cmpt cA cB cop csn vx cA csn cC cmpt vx cR cC
      cmpt cA cB cop csn vx cA csn cB cmpt vx cA csn cC cmpt cA cvv wcel cB cvv
      wcel cA cB cop csn vx cA csn cB cmpt wceq fmptap.0a fmptap.0b vx cA cB
      cvv cvv fmptsn mp2an vx cA csn cC cB vx cv cA csn wcel vx cv cA wceq cC
      cB wceq vx cv cA elsni fmptap.2 syl mpteq2ia eqtr4i uneq2i vx cR cA csn
      cC mptun cR cA csn cun cS wceq vx cR cA csn cun cC cmpt vx cS cC cmpt
      wceq fmptap.1 vx cR cA csn cun cS cC mpteq1 ax-mp 3eqtr2i $.
  $}

  $( The value of a restricted identity function.  (Contributed by NM,
     19-May-2004.) $)
  fvresi $p |- ( B e. A -> ( ( _I |` A ) ` B ) = B ) $=
    cB cA wcel cB cid cA cres cfv cB cid cfv cB cB cA cid fvres cB cA fvi eqtrd
    $.

  $( Remove an ordered pair not participating in a function value.
     (Contributed by NM, 1-Oct-2013.)  (Revised by Mario Carneiro,
     28-May-2014.) $)
  fvunsn $p |- ( B =/= D
       -> ( ( A u. { <. B , C >. } ) ` D ) = ( A ` D ) ) $=
    cB cD wne cD cA cB cC cop csn cun cD csn cres cfv cD cA cD csn cres cfv cD
    cA cB cC cop csn cun cfv cD cA cfv cB cD wne cD cA cB cC cop csn cun cD csn
    cres cA cD csn cres cB cD wne cA cB cC cop csn cun cD csn cres cA cD csn
    cres cB cC cop csn cD csn cres cun cA cD csn cres cA cB cC cop csn cD csn
    resundir cB cD wne cA cD csn cres cB cC cop csn cD csn cres cun cA cD csn
    cres c0 cun cA cD csn cres cB cD wne cB cC cop csn cD csn cres c0 cA cD csn
    cres cB cD wne cB cD csn wcel wn cB cC cop csn cD csn cres c0 wceq cB cD
    csn wcel cB cD cB cD elsni necon3ai cB cC cD csn ressnop0 syl uneq2d cA cD
    csn cres un0 syl6eq syl5eq fveq1d cD cvv wcel cD cA cB cC cop csn cun cD
    csn cres cfv cD cA cB cC cop csn cun cfv wceq cD cvv wcel cD cD csn wcel cD
    cA cB cC cop csn cun cD csn cres cfv cD cA cB cC cop csn cun cfv wceq cD
    cvv snidg cD cD csn cA cB cC cop csn cun fvres syl cD cvv wcel wn cD cA cB
    cC cop csn cun cD csn cres cfv c0 cD cA cB cC cop csn cun cfv cD cA cB cC
    cop csn cun cD csn cres fvprc cD cA cB cC cop csn cun fvprc eqtr4d pm2.61i
    cD cvv wcel cD cA cD csn cres cfv cD cA cfv wceq cD cvv wcel cD cD csn wcel
    cD cA cD csn cres cfv cD cA cfv wceq cD cvv snidg cD cD csn cA fvres syl cD
    cvv wcel wn cD cA cD csn cres cfv c0 cD cA cfv cD cA cD csn cres fvprc cD
    cA fvprc eqtr4d pm2.61i 3eqtr3g $.

  ${
    fvsn.1 $e |- A e. _V $.
    fvsn.2 $e |- B e. _V $.
    $( The value of a singleton of an ordered pair is the second member.
       (Contributed by NM, 12-Aug-1994.) $)
    fvsn $p |- ( { <. A , B >. } ` A ) = B $=
      cA cB cop csn wfun cA cB cop cA cB cop csn wcel cA cA cB cop csn cfv cB
      wceq cA cB fvsn.1 fvsn.2 funsn cA cB cop cA cB opex snid cA cB cA cB cop
      csn funopfv mp2 $.
  $}

  ${
    $d A a b $.  $d B b $.
    $( The value of a singleton of an ordered pair is the second member.
       (Contributed by NM, 26-Oct-2012.) $)
    fvsng $p |- ( ( A e. V /\ B e. W ) -> ( { <. A , B >. } ` A ) = B ) $=
      va cv va cv vb cv cop csn cfv vb cv wceq cA cA vb cv cop csn cfv vb cv
      wceq cA cA cB cop csn cfv cB wceq va vb cA cB cV cW va cv cA wceq va cv
      va cv vb cv cop csn cfv cA cA vb cv cop csn cfv vb cv va cv cA wceq va cv
      cA va cv vb cv cop csn cA vb cv cop csn va cv cA wceq va cv vb cv cop cA
      vb cv cop va cv cA vb cv opeq1 sneqd va cv cA wceq id fveq12d eqeq1d vb
      cv cB wceq cA cA vb cv cop csn cfv cA cA cB cop csn cfv vb cv cB vb cv cB
      wceq cA cA vb cv cop csn cA cB cop csn vb cv cB wceq cA vb cv cop cA cB
      cop vb cv cB cA opeq2 sneqd fveq1d vb cv cB wceq id eqeq12d va cv vb cv
      va vex vb vex fvsn vtocl2g $.
  $}

  ${
    fvsnun.1 $e |- A e. _V $.
    fvsnun.2 $e |- B e. _V $.
    fvsnun.3 $e |- G = ( { <. A , B >. } u. ( F |` ( C \ { A } ) ) ) $.
    $( The value of a function with one of its ordered pairs replaced, at the
       replaced ordered pair.  See also ~ fvsnun2 .  (Contributed by NM,
       23-Sep-2007.) $)
    fvsnun1 $p |- ( G ` A ) = B $=
      cA cG cA csn cres cfv cA cA cB cop csn cA csn cres cfv cA cG cfv cB cA cG
      cA csn cres cA cB cop csn cA csn cres cG cA csn cres cA cB cop csn cF cC
      cA csn cdif cres cun cA csn cres cA cB cop csn cA csn cres cG cA cB cop
      csn cF cC cA csn cdif cres cun cA csn fvsnun.3 reseq1i cA cB cop csn cF
      cC cA csn cdif cres cun cA csn cres cA cB cop csn cA csn cres cF cC cA
      csn cdif cres cA csn cres cun cA cB cop csn cA csn cres cA cB cop csn cF
      cC cA csn cdif cres cA csn resundir cA cB cop csn cA csn cres cF cC cA
      csn cdif cres cA csn cres cun cA cB cop csn cA csn cres c0 cun cA cB cop
      csn cA csn cres cF cC cA csn cdif cres cA csn cres c0 cA cB cop csn cA
      csn cres cC cA csn cdif cA csn cin c0 wceq cF cC cA csn cdif cres cA csn
      cres c0 wceq cC cA csn cdif cA csn cin cA csn cC cA csn cdif cin c0 cC cA
      csn cdif cA csn incom cA csn cC disjdif eqtri cC cA csn cdif cA csn cF
      resdisj ax-mp uneq2i cA cB cop csn cA csn cres un0 eqtri eqtri eqtri
      fveq1i cA cA csn wcel cA cG cA csn cres cfv cA cG cfv wceq cA fvsnun.1
      snid cA cA csn cG fvres ax-mp cA cA cB cop csn cA csn cres cfv cA cA cB
      cop csn cfv cB cA cA csn wcel cA cA cB cop csn cA csn cres cfv cA cA cB
      cop csn cfv wceq cA fvsnun.1 snid cA cA csn cA cB cop csn fvres ax-mp cA
      cB fvsnun.1 fvsnun.2 fvsn eqtri 3eqtr3i $.

    $( The value of a function with one of its ordered pairs replaced, at
       arguments other than the replaced one.  See also ~ fvsnun1 .
       (Contributed by NM, 23-Sep-2007.) $)
    fvsnun2 $p |- ( D e. ( C \ { A } ) -> ( G ` D ) = ( F ` D ) ) $=
      cD cC cA csn cdif wcel cD cG cC cA csn cdif cres cfv cD cF cC cA csn cdif
      cres cfv cD cG cfv cD cF cfv cD cG cC cA csn cdif cres cF cC cA csn cdif
      cres cG cC cA csn cdif cres cA cB cop csn cF cC cA csn cdif cres cun cC
      cA csn cdif cres cA cB cop csn cC cA csn cdif cres cF cC cA csn cdif cres
      cC cA csn cdif cres cun cF cC cA csn cdif cres cG cA cB cop csn cF cC cA
      csn cdif cres cun cC cA csn cdif fvsnun.3 reseq1i cA cB cop csn cF cC cA
      csn cdif cres cC cA csn cdif resundir cA cB cop csn cC cA csn cdif cres
      cF cC cA csn cdif cres cC cA csn cdif cres cun c0 cF cC cA csn cdif cres
      cun cF cC cA csn cdif cres c0 cun cF cC cA csn cdif cres cA cB cop csn cC
      cA csn cdif cres c0 cF cC cA csn cdif cres cC cA csn cdif cres cF cC cA
      csn cdif cres cA csn cC cA csn cdif cin c0 wceq cA cB cop csn cC cA csn
      cdif cres c0 wceq cA csn cC disjdif cA cB cop csn cA csn wfn cA csn cC cA
      csn cdif cin c0 wceq cA cB cop csn cC cA csn cdif cres c0 wceq wb cA cB
      fvsnun.1 fvsnun.2 fnsn cA csn cC cA csn cdif cA cB cop csn fnresdisj
      ax-mp mpbi cF cC cA csn cdif residm uneq12i c0 cF cC cA csn cdif cres
      uncom cF cC cA csn cdif cres un0 3eqtri 3eqtri fveq1i cD cC cA csn cdif
      cG fvres cD cC cA csn cdif cF fvres 3eqtr3a $.
  $}

  $( Split a function into a single point and all the rest.  (Contributed by
     Stefan O'Rear, 27-Feb-2015.) $)
  fnsnsplit $p |- ( ( F Fn A /\ X e. A ) ->
      F = ( ( F |` ( A \ { X } ) ) u. { <. X , ( F ` X ) >. } ) ) $=
    cF cA wfn cX cA wcel wa cF cA cres cF cF cA cX csn cdif cres cX cX cF cfv
    cop csn cun cF cA wfn cF cA cres cF wceq cX cA wcel cA cF fnresdm adantr cF
    cA wfn cX cA wcel wa cF cA cX csn cdif cX csn cun cres cF cA cX csn cdif
    cres cF cX csn cres cun cF cA cres cF cA cX csn cdif cres cX cX cF cfv cop
    csn cun cF cA cX csn cdif cX csn resundi cF cA wfn cX cA wcel wa cA cX csn
    cdif cX csn cun cA cF cX cA wcel cA cX csn cdif cX csn cun cA wceq cF cA
    wfn cA cX difsnid adantl reseq2d cF cA wfn cX cA wcel wa cF cX csn cres cX
    cX cF cfv cop csn cF cA cX csn cdif cres cA cX cF fnressn uneq2d 3eqtr3a
    eqtr3d $.

  $( Adjoining a point to a function gives a function.  (Contributed by Stefan
     O'Rear, 28-Feb-2015.) $)
  fsnunf $p |- ( ( F : S --> T /\ ( X e. V /\ -. X e. S ) /\ Y e. T ) ->
      ( F u. { <. X , Y >. } ) : ( S u. { X } ) --> T ) $=
    cS cT cF wf cX cV wcel cX cS wcel wn wa cY cT wcel w3a cS cX csn cun cT cY
    csn cun cF cX cY cop csn cun wf cS cX csn cun cT cF cX cY cop csn cun wf cS
    cT cF wf cX cV wcel cX cS wcel wn wa cY cT wcel w3a cS cT cF wf cX csn cY
    csn cX cY cop csn wf cS cX csn cin c0 wceq cS cX csn cun cT cY csn cun cF
    cX cY cop csn cun wf cS cT cF wf cX cV wcel cX cS wcel wn wa cY cT wcel
    simp1 cS cT cF wf cX cV wcel cX cS wcel wn wa cY cT wcel w3a cX csn cY csn
    cX cY cop csn wf1o cX csn cY csn cX cY cop csn wf cS cT cF wf cX cV wcel cX
    cS wcel wn wa cY cT wcel w3a cX cV wcel cY cT wcel cX csn cY csn cX cY cop
    csn wf1o cS cT cF wf cX cV wcel cX cS wcel wn cY cT wcel simp2l cS cT cF wf
    cX cV wcel cX cS wcel wn wa cY cT wcel simp3 cX cY cV cT f1osng syl2anc cX
    csn cY csn cX cY cop csn f1of syl cS cT cF wf cX cV wcel cX cS wcel wn wa
    cY cT wcel w3a cX cS wcel wn cS cX csn cin c0 wceq cS cT cF wf cX cV wcel
    cX cS wcel wn cY cT wcel simp2r cS cX disjsn sylibr cS cX csn cT cY csn cF
    cX cY cop csn fun syl21anc cS cT cF wf cX cV wcel cX cS wcel wn wa cY cT
    wcel w3a cT cY csn cun cT wceq cS cX csn cun cT cY csn cun cF cX cY cop csn
    cun wf cS cX csn cun cT cF cX cY cop csn cun wf wb cS cT cF wf cX cV wcel
    cX cS wcel wn wa cY cT wcel w3a cY csn cT wss cT cY csn cun cT wceq cY cT
    wcel cS cT cF wf cY csn cT wss cX cV wcel cX cS wcel wn wa cY cT snssi
    3ad2ant3 cY csn cT ssequn2 sylib cT cY csn cun cT cS cX csn cun cF cX cY
    cop csn cun feq3 syl mpbid $.

  $( Adjoining a point to a punctured function gives a function.  (Contributed
     by Stefan O'Rear, 28-Feb-2015.) $)
  fsnunf2 $p |- ( ( F : ( S \ { X } ) --> T /\ X e. S /\ Y e. T ) ->
      ( F u. { <. X , Y >. } ) : S --> T ) $=
    cS cX csn cdif cT cF wf cX cS wcel cY cT wcel w3a cS cX csn cdif cX csn cun
    cT cF cX cY cop csn cun wf cS cT cF cX cY cop csn cun wf cS cX csn cdif cT
    cF wf cX cS wcel cY cT wcel w3a cS cX csn cdif cT cF wf cX cS wcel cX cS cX
    csn cdif wcel wn cY cT wcel cS cX csn cdif cX csn cun cT cF cX cY cop csn
    cun wf cS cX csn cdif cT cF wf cX cS wcel cY cT wcel simp1 cS cX csn cdif
    cT cF wf cX cS wcel cY cT wcel simp2 cX cS wcel cS cX csn cdif cT cF wf cX
    cS cX csn cdif wcel wn cY cT wcel cX cS wcel cX cX csn wcel cX cS cX csn
    cdif wcel wn cX cS snidg cX cX csn cS elndif syl 3ad2ant2 cS cX csn cdif cT
    cF wf cX cS wcel cY cT wcel simp3 cS cX csn cdif cT cF cS cX cY fsnunf
    syl121anc cS cX csn cdif cT cF wf cX cS wcel cY cT wcel w3a cS cX csn cdif
    cX csn cun cS cT cF cX cY cop csn cun cX cS wcel cS cX csn cdif cT cF wf cS
    cX csn cdif cX csn cun cS wceq cY cT wcel cS cX difsnid 3ad2ant2 feq2d
    mpbid $.

  $( Recover the added point from a point-added function.  (Contributed by
     Stefan O'Rear, 28-Feb-2015.)  (Revised by NM, 18-May-2017.) $)
  fsnunfv $p |- ( ( X e. V /\ Y e. W /\ -. X e. dom F ) ->
      ( ( F u. { <. X , Y >. } ) ` X ) = Y ) $=
    cX cV wcel cY cW wcel cX cF cdm wcel wn w3a cX cF cX cY cop csn cun cX csn
    cres cfv cX cX cY cop csn cfv cX cF cX cY cop csn cun cfv cY cX cV wcel cY
    cW wcel cX cF cdm wcel wn w3a cX cF cX cY cop csn cun cX csn cres cX cY cop
    csn cX cV wcel cY cW wcel cX cF cdm wcel wn w3a cF cX csn cres cX cY cop
    csn cX csn cres cun c0 cX cY cop csn cun cF cX cY cop csn cun cX csn cres
    cX cY cop csn cX cV wcel cY cW wcel cX cF cdm wcel wn w3a cF cX csn cres c0
    cX cY cop csn cX csn cres cX cY cop csn cX cV wcel cY cW wcel cX cF cdm
    wcel wn w3a cF cX csn cres cdm c0 wceq cF cX csn cres c0 wceq cX cF cdm
    wcel wn cX cV wcel cF cX csn cres cdm c0 wceq cY cW wcel cX cF cdm wcel wn
    cF cX csn cres cdm cF cdm cX csn cin c0 cF cX csn cres cdm cX csn cF cdm
    cin cF cdm cX csn cin cF cX csn dmres cX csn cF cdm incom eqtri cF cdm cX
    csn cin c0 wceq cX cF cdm wcel wn cF cdm cX disjsn biimpri syl5eq 3ad2ant3
    cF cX csn cres wrel cF cX csn cres c0 wceq cF cX csn cres cdm c0 wceq wb cF
    cX csn relres cF cX csn cres reldm0 ax-mp sylibr cX cV wcel cY cW wcel cX
    cF cdm wcel wn w3a cX cY cop csn cX csn wfn cX cY cop csn cX csn cres cX cY
    cop csn wceq cX cV wcel cY cW wcel cX cY cop csn cX csn wfn cX cF cdm wcel
    wn cX cY cV cW fnsng 3adant3 cX csn cX cY cop csn fnresdm syl uneq12d cF cX
    cY cop csn cX csn resundir c0 cX cY cop csn cun cX cY cop csn c0 cun cX cY
    cop csn c0 cX cY cop csn uncom cX cY cop csn un0 eqtr2i 3eqtr4g fveq1d cX
    cV wcel cY cW wcel cX cF cdm wcel wn w3a cX cX csn wcel cX cF cX cY cop csn
    cun cX csn cres cfv cX cF cX cY cop csn cun cfv wceq cX cV wcel cY cW wcel
    cX cX csn wcel cX cF cdm wcel wn cX cV snidg 3ad2ant1 cX cX csn cF cX cY
    cop csn cun fvres syl cX cV wcel cY cW wcel cX cX cY cop csn cfv cY wceq cX
    cF cdm wcel wn cX cY cV cW fvsng 3adant3 3eqtr3d $.

  $( Recover the original function from a point-added function.  (Contributed
     by Stefan O'Rear, 28-Feb-2015.) $)
  fsnunres $p |- ( ( F Fn S /\ -. X e. S ) ->
      ( ( F u. { <. X , Y >. } ) |` S ) = F ) $=
    cF cS wfn cX cS wcel wn wa cF cS cres cX cY cop csn cS cres cun cF c0 cun
    cF cX cY cop csn cun cS cres cF cF cS wfn cX cS wcel wn wa cF cS cres cF cX
    cY cop csn cS cres c0 cF cS wfn cF cS cres cF wceq cX cS wcel wn cS cF
    fnresdm adantr cX cS wcel wn cX cY cop csn cS cres c0 wceq cF cS wfn cX cY
    cS ressnop0 adantl uneq12d cF cX cY cop csn cS resundir cF c0 cun cF cF un0
    eqcomi 3eqtr4g $.

  ${
    fvpr1.1 $e |- A e. _V $.
    fvpr1.2 $e |- C e. _V $.
    $( The value of a function with a domain of two elements.  (Contributed by
       Jeff Madsen, 20-Jun-2010.) $)
    fvpr1 $p |- ( A =/= B -> ( { <. A , C >. , <. B , D >. } ` A ) = C ) $=
      cA cB wne cA cA cC cop cB cD cop cpr cfv cA cA cC cop csn cfv cC cA cB
      wne cA cA cC cop cB cD cop cpr cfv cA cA cC cop csn cB cD cop csn cun cfv
      cA cA cC cop csn cfv cA cA cC cop cB cD cop cpr cA cC cop csn cB cD cop
      csn cun cA cC cop cB cD cop df-pr fveq1i cA cB wne cB cA wne cA cA cC cop
      csn cB cD cop csn cun cfv cA cA cC cop csn cfv wceq cA cB necom cA cC cop
      csn cB cD cA fvunsn sylbi syl5eq cA cC fvpr1.1 fvpr1.2 fvsn syl6eq $.
  $}

  ${
    fvpr2.1 $e |- B e. _V $.
    fvpr2.2 $e |- D e. _V $.
    $( The value of a function with a domain of two elements.  (Contributed by
       Jeff Madsen, 20-Jun-2010.) $)
    fvpr2 $p |- ( A =/= B -> ( { <. A , C >. , <. B , D >. } ` B ) = D ) $=
      cA cB wne cB cA cC cop cB cD cop cpr cfv cB cB cD cop cA cC cop cpr cfv
      cD cB cA cC cop cB cD cop cpr cB cD cop cA cC cop cpr cA cC cop cB cD cop
      prcom fveq1i cA cB wne cB cA wne cB cB cD cop cA cC cop cpr cfv cD wceq
      cA cB necom cB cA cD cC fvpr2.1 fvpr2.2 fvpr1 sylbi syl5eq $.
  $}

  ${
    fvtp1.1 $e |- A e. _V $.
    fvtp1.4 $e |- D e. _V $.
    $( The first value of a function with a domain of three elements.
       (Contributed by NM, 14-Sep-2011.) $)
    fvtp1 $p |- ( ( A =/= B /\ A =/= C )
             -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` A ) = D ) $=
      cA cB wne cA cC wne wa cA cA cD cop cB cE cop cC cF cop ctp cfv cA cA cD
      cop cB cE cop cpr cC cF cop csn cun cfv cD cA cA cD cop cB cE cop cC cF
      cop ctp cA cD cop cB cE cop cpr cC cF cop csn cun cA cD cop cB cE cop cC
      cF cop df-tp fveq1i cA cC wne cA cB wne cA cA cD cop cB cE cop cpr cC cF
      cop csn cun cfv cA cA cD cop cB cE cop cpr cfv cD cA cC wne cC cA wne cA
      cA cD cop cB cE cop cpr cC cF cop csn cun cfv cA cA cD cop cB cE cop cpr
      cfv wceq cA cC necom cA cD cop cB cE cop cpr cC cF cA fvunsn sylbi cA cB
      cD cE fvtp1.1 fvtp1.4 fvpr1 sylan9eqr syl5eq $.
  $}

  ${
    fvtp2.1 $e |- B e. _V $.
    fvtp2.4 $e |- E e. _V $.
    $( The second value of a function with a domain of three elements.
       (Contributed by NM, 14-Sep-2011.) $)
    fvtp2 $p |- ( ( A =/= B /\ B =/= C )
             -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` B ) = E ) $=
      cA cB wne cB cC wne wa cB cA cD cop cB cE cop cC cF cop ctp cfv cB cB cE
      cop cC cF cop cA cD cop ctp cfv cE cB cA cD cop cB cE cop cC cF cop ctp
      cB cE cop cC cF cop cA cD cop ctp cA cD cop cB cE cop cC cF cop tprot
      fveq1i cA cB wne cB cA wne cB cC wne cB cB cE cop cC cF cop cA cD cop ctp
      cfv cE wceq cA cB necom cB cC wne cB cA wne cB cB cE cop cC cF cop cA cD
      cop ctp cfv cE wceq cB cC cA cE cF cD fvtp2.1 fvtp2.4 fvtp1 ancoms sylanb
      syl5eq $.
  $}

  ${
    fvtp3.1 $e |- C e. _V $.
    fvtp3.4 $e |- F e. _V $.
    $( The third value of a function with a domain of three elements.
       (Contributed by NM, 14-Sep-2011.) $)
    fvtp3 $p |- ( ( A =/= C /\ B =/= C )
             -> ( { <. A , D >. , <. B , E >. , <. C , F >. } ` C ) = F ) $=
      cA cC wne cB cC wne wa cC cA cD cop cB cE cop cC cF cop ctp cfv cC cB cE
      cop cC cF cop cA cD cop ctp cfv cF cC cA cD cop cB cE cop cC cF cop ctp
      cB cE cop cC cF cop cA cD cop ctp cA cD cop cB cE cop cC cF cop tprot
      fveq1i cB cC wne cA cC wne cC cB cE cop cC cF cop cA cD cop ctp cfv cF
      wceq cA cC wne cB cC wne cC cA wne cC cB cE cop cC cF cop cA cD cop ctp
      cfv cF wceq cA cC necom cB cC cA cE cF cD fvtp3.1 fvtp3.4 fvtp2 sylan2b
      ancoms syl5eq $.
  $}

  $( The value of a constant function.  (Contributed by NM, 20-Aug-2005.) $)
  fvconst2g $p |- ( ( B e. D /\ C e. A ) -> ( ( A X. { B } ) ` C ) = B ) $=
    cB cD wcel cA cB csn cA cB csn cxp wf cC cA wcel cC cA cB csn cxp cfv cB
    wceq cA cB cD fconstg cA cB cC cA cB csn cxp fvconst sylan $.

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x F $.
    $( A constant function expressed as a cross product.  (Contributed by NM,
       27-Nov-2007.) $)
    fconst2g $p |- ( B e. C -> ( F : A --> { B } <-> F = ( A X. { B } ) ) ) $=
      cB cC wcel cA cB csn cF wf cF cA cB csn cxp wceq cA cB csn cF wf cB cC
      wcel cF cA cB csn cxp wceq cA cB csn cF wf cB cC wcel wa cF cA cB csn cxp
      wceq vx cv cF cfv vx cv cA cB csn cxp cfv wceq vx cA wral cA cB csn cF wf
      cB cC wcel wa vx cv cF cfv vx cv cA cB csn cxp cfv wceq vx cA cA cB csn
      cF wf cB cC wcel wa vx cv cA wcel wa vx cv cF cfv cB vx cv cA cB csn cxp
      cfv cA cB csn cF wf vx cv cA wcel vx cv cF cfv cB wceq cB cC wcel cA cB
      vx cv cF fvconst adantlr cB cC wcel vx cv cA wcel vx cv cA cB csn cxp cfv
      cB wceq cA cB csn cF wf cA cB vx cv cC fvconst2g adantll eqtr4d ralrimiva
      cA cB csn cF wf cF cA wfn cA cB csn cxp cA wfn cF cA cB csn cxp wceq vx
      cv cF cfv vx cv cA cB csn cxp cfv wceq vx cA wral wb cB cC wcel cA cB csn
      cF ffn cA cB cC fnconstg vx cA cF cA cB csn cxp eqfnfv syl2an mpbird
      expcom cB cC wcel cA cB csn cF wf cF cA cB csn cxp wceq cA cB csn cA cB
      csn cxp wf cA cB cC fconstg cA cB csn cF cA cB csn cxp feq1 syl5ibrcom
      impbid $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.
    fvconst2.1 $e |- B e. _V $.
    $( The value of a constant function.  (Contributed by NM, 16-Apr-2005.) $)
    fvconst2 $p |- ( C e. A -> ( ( A X. { B } ) ` C ) = B ) $=
      cB cvv wcel cC cA wcel cC cA cB csn cxp cfv cB wceq fvconst2.1 cA cB cC
      cvv fvconst2g mpan $.

    $( A constant function expressed as a cross product.  (Contributed by NM,
       20-Aug-1999.) $)
    fconst2 $p |- ( F : A --> { B } <-> F = ( A X. { B } ) ) $=
      cB cvv wcel cA cB csn cF wf cF cA cB csn cxp wceq wb fvconst2.1 cA cB cvv
      cF fconst2g ax-mp $.
  $}

  $( Two ways to express that a function is constant.  (Contributed by NM,
     27-Nov-2007.) $)
  fconst5 $p |- ( ( F Fn A /\ A =/= (/) ) -> ( F = ( A X. { B } ) <->
                 ran F = { B } ) ) $=
    cF cA wfn cA c0 wne wa cF cA cB csn cxp wceq cF crn cB csn wceq cA c0 wne
    cF cA cB csn cxp wceq cF crn cB csn wceq wi cF cA wfn cF cA cB csn cxp wceq
    cF crn cA cB csn cxp crn wceq cA c0 wne cF crn cB csn wceq cF cA cB csn cxp
    rneq cA c0 wne cA cB csn cxp crn cB csn cF crn cA cB csn rnxp eqeq2d syl5ib
    adantl cB cvv wcel cF cA wfn cA c0 wne wa cF crn cB csn wceq cF cA cB csn
    cxp wceq wi wi cB cvv wcel cF cA wfn cF crn cB csn wceq cF cA cB csn cxp
    wceq wi cA c0 wne cB cvv wcel cF cA wfn cF crn cB csn wceq cF cA cB csn cxp
    wceq cF cA wfn cF crn cB csn wceq wa cA cB csn cF wf cB cvv wcel cF cA cB
    csn cxp wceq cF cA wfn cF crn cB csn wceq wa cA cB csn cF wfo cA cB csn cF
    wf cA cB csn cF df-fo cA cB csn cF fof sylbir cA cB cvv cF fconst2g syl5ib
    exp3a adantrd cB cvv wcel wn cF cA wfn cF crn cB csn wceq cF cA cB csn cxp
    wceq wi cA c0 wne cF cA wfn cF wrel cB cvv wcel wn cF crn cB csn wceq cF cA
    cB csn cxp wceq wi cA cF fnrel cB cvv wcel wn cB csn c0 wceq cF wrel cF crn
    cB csn wceq cF cA cB csn cxp wceq wi wi cB snprc cB csn c0 wceq cF wrel cF
    crn cB csn wceq cF cA cB csn cxp wceq wi cB csn c0 wceq cF wrel wa cF crn
    c0 wceq cF c0 wceq cF crn cB csn wceq cF cA cB csn cxp wceq cF wrel cF crn
    c0 wceq cF c0 wceq wi cB csn c0 wceq cF wrel cF c0 wceq cF crn c0 wceq cF
    relrn0 biimprd adantl cB csn c0 wceq cF crn cB csn wceq cF crn c0 wceq wb
    cF wrel cB csn c0 cF crn eqeq2 adantr cB csn c0 wceq cF cA cB csn cxp wceq
    cF c0 wceq wb cF wrel cB csn c0 wceq cA cB csn cxp c0 cF cB csn c0 wceq cA
    cB csn cxp cA c0 cxp c0 cB csn c0 cA xpeq2 cA xp0 syl6eq eqeq2d adantr
    3imtr4d ex sylbi syl5 adantrd pm2.61i impbid $.

  ${
    $d F a $.  $d V a $.  $d A a $.  $d B a $.  $d Z a $.
    $( Two ways to express restriction of a support set.  (Contributed by
       Stefan O'Rear, 5-Feb-2015.) $)
    fnsuppres $p |- ( ( F Fn ( A u. B ) /\ ( A i^i B ) = (/) /\ Z e. V ) ->
        ( ( `' F " ( _V \ { Z } ) ) C_ A <-> ( F |` B ) = ( B X. { Z } ) ) ) $=
      cF cA cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cF cfv cZ wne va
      cA cB cun crab cA wss va cv cF cB cres cfv va cv cB cZ csn cxp cfv wceq
      va cB wral cF ccnv cvv cZ csn cdif cima cA wss cF cB cres cB cZ csn cxp
      wceq va cv cF cfv cZ wne va cA cB cun crab cA wss va cv cF cfv cZ wne va
      cB crab cA wss cF cA cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cF
      cB cres cfv va cv cB cZ csn cxp cfv wceq va cB wral va cv cF cfv cZ wne
      va cA crab cA wss va cv cF cfv cZ wne va cB crab cA wss wa va cv cF cfv
      cZ wne va cA crab va cv cF cfv cZ wne va cB crab cun cA wss va cv cF cfv
      cZ wne va cB crab cA wss va cv cF cfv cZ wne va cA cB cun crab cA wss va
      cv cF cfv cZ wne va cA crab va cv cF cfv cZ wne va cB crab cA unss va cv
      cF cfv cZ wne va cA crab cA wss va cv cF cfv cZ wne va cB crab cA wss va
      cv cF cfv cZ wne va cA ssrab2 biantrur va cv cF cfv cZ wne va cA cB cun
      crab va cv cF cfv cZ wne va cA crab va cv cF cfv cZ wne va cB crab cun cA
      va cv cF cfv cZ wne va cA cB rabun2 sseq1i 3bitr4ri va cv cF cfv cZ wne
      va cB crab cA wss va cv cF cfv cZ wne va cv cA wcel wi va cB wral cF cA
      cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cF cB cres cfv va cv cB
      cZ csn cxp cfv wceq va cB wral va cv cF cfv cZ wne va cB cA rabss cF cA
      cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cF cfv cZ wne va cv cA
      wcel wi va cv cF cB cres cfv va cv cB cZ csn cxp cfv wceq va cB cF cA cB
      cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cB wcel wa va cv cF cB
      cres cfv va cv cB cZ csn cxp cfv wceq va cv cF cfv cZ wceq va cv cF cfv
      cZ wne wn va cv cF cfv cZ wne va cv cA wcel wi cF cA cB cun wfn cA cB cin
      c0 wceq cZ cV wcel w3a va cv cB wcel wa va cv cF cB cres cfv va cv cF cfv
      va cv cB cZ csn cxp cfv cZ va cv cB wcel va cv cF cB cres cfv va cv cF
      cfv wceq cF cA cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cB cF
      fvres adantl cZ cV wcel cF cA cB cun wfn va cv cB wcel va cv cB cZ csn
      cxp cfv cZ wceq cA cB cin c0 wceq cB cZ va cv cV fvconst2g 3ad2antl3
      eqeq12d va cv cF cfv cZ wne wn va cv cF cfv cZ wceq wb cF cA cB cun wfn
      cA cB cin c0 wceq cZ cV wcel w3a va cv cB wcel wa va cv cF cfv cZ nne a1i
      cF cA cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cB wcel wa va cv
      cA wcel wn va cv cF cfv cZ wne wn va cv cF cfv cZ wne va cv cA wcel wi wb
      va cv cB wcel va cv cB wcel cA cB cin c0 wceq va cv cA wcel wn cF cA cB
      cun wfn cA cB cin c0 wceq cZ cV wcel w3a va cv cB wcel id cF cA cB cun
      wfn cA cB cin c0 wceq cZ cV wcel simp2 va cv cB cA minel syl2anr va cv cA
      wcel va cv cF cfv cZ wne mtt syl 3bitr2rd ralbidva syl5bb syl5bb cF cA cB
      cun wfn cA cB cin c0 wceq cZ cV wcel w3a cF ccnv cvv cZ csn cdif cima va
      cv cF cfv cZ wne va cA cB cun crab cA cF cA cB cun wfn cA cB cin c0 wceq
      cF ccnv cvv cZ csn cdif cima va cv cF cfv cZ wne va cA cB cun crab wceq
      cZ cV wcel va cA cB cun cZ cF fnniniseg2 3ad2ant1 sseq1d cF cA cB cun wfn
      cA cB cin c0 wceq cZ cV wcel w3a cF cB cres cB wfn cB cZ csn cxp cB wfn
      cF cB cres cB cZ csn cxp wceq va cv cF cB cres cfv va cv cB cZ csn cxp
      cfv wceq va cB wral wb cF cA cB cun wfn cA cB cin c0 wceq cZ cV wcel w3a
      cF cA cB cun wfn cB cA cB cun wss cF cB cres cB wfn cF cA cB cun wfn cA
      cB cin c0 wceq cZ cV wcel simp1 cB cA cB cun wss cF cA cB cun wfn cA cB
      cin c0 wceq cZ cV wcel w3a cB cA ssun2 a1i cA cB cun cB cF fnssres
      syl2anc cZ cV wcel cF cA cB cun wfn cB cZ csn cxp cB wfn cA cB cin c0
      wceq cB cZ cV fnconstg 3ad2ant3 va cB cF cB cres cB cZ csn cxp eqfnfv
      syl2anc 3bitr4d $.

    $( The support of a function is empty iff it is identically zero.
       (Contributed by Stefan O'Rear, 22-Mar-2015.) $)
    fnsuppeq0 $p |- ( ( F Fn A /\ Z e. V ) ->
        ( ( `' F " ( _V \ { Z } ) ) = (/) <-> F = ( A X. { Z } ) ) ) $=
      cF cA wfn cZ cV wcel wa cF ccnv cvv cZ csn cdif cima c0 wceq cF cA cres
      cA cZ csn cxp wceq cF cA cZ csn cxp wceq cF ccnv cvv cZ csn cdif cima c0
      wceq cF ccnv cvv cZ csn cdif cima c0 wss cF cA wfn cZ cV wcel wa cF cA
      cres cA cZ csn cxp wceq cF ccnv cvv cZ csn cdif cima ss0b cF cA wfn cZ cV
      wcel wa cF c0 cA cun wfn c0 cA cin c0 wceq cZ cV wcel cF ccnv cvv cZ csn
      cdif cima c0 wss cF cA cres cA cZ csn cxp wceq wb cF cA wfn cF c0 cA cun
      wfn cZ cV wcel cF cA wfn cF c0 cA cun wfn cA c0 cA cun cF cA c0 cun cA c0
      cA cun cA un0 cA c0 uncom eqtr3i fneq2i biimpi adantr c0 cA cin c0 wceq
      cF cA wfn cZ cV wcel wa c0 cA cin cA c0 cin c0 c0 cA incom cA in0 eqtri
      a1i cF cA wfn cZ cV wcel simpr c0 cA cF cV cZ fnsuppres syl3anc syl5bbr
      cF cA wfn cZ cV wcel wa cF cA cres cF cA cZ csn cxp cF cA wfn cF cA cres
      cF wceq cZ cV wcel cA cF fnresdm adantr eqeq1d bitrd $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z F $.
    $( A constant function expressed in terms of its functionality, domain, and
       value.  See also ~ fconst2 .  (Contributed by NM, 27-Aug-2004.) $)
    fconstfv $p |- ( F : A --> { B } <->
                   ( F Fn A /\ A. x e. A ( F ` x ) = B ) ) $=
      cA cB csn cF wf cF cA wfn vx cv cF cfv cB wceq vx cA wral wa cA cB csn cF
      wf cF cA wfn vx cv cF cfv cB wceq vx cA wral cA cB csn cF ffn cA cB csn
      cF wf vx cv cF cfv cB wceq vx cA cA cB vx cv cF fvconst ralrimiva jca cF
      cA wfn vx cv cF cfv cB wceq vx cA wral wa cA cB csn cF wf wi cA c0 cA c0
      wceq cF cA wfn cA cB csn cF wf vx cv cF cfv cB wceq vx cA wral cA c0 wceq
      cF cA wfn c0 cB csn cF wf cA cB csn cF wf cA c0 wceq cF cA wfn cF c0 wceq
      c0 cB csn cF wf cA c0 wceq cF cA wfn cF c0 wfn cF c0 wceq cA c0 cF fneq2
      cF fn0 syl6bb cF c0 wceq c0 cB csn cF wf c0 cB csn c0 wf cB csn f0 c0 cB
      csn cF c0 feq1 mpbiri syl6bi cA c0 cB csn cF feq2 sylibrd adantrd cA c0
      wne cF cA wfn vx cv cF cfv cB wceq vx cA wral wa cF cA wfn cF crn cB csn
      wceq wa cA cB csn cF wf cA c0 wne cF cA wfn vx cv cF cfv cB wceq vx cA
      wral cF crn cB csn wceq cA c0 wne cF cA wfn vx cv cF cfv cB wceq vx cA
      wral cF crn cB csn wceq cA c0 wne vx cv cF cfv cB wceq vx cA wral cF cA
      wfn cF crn cB csn wceq cA c0 wne vx cv cF cfv cB wceq vx cA wral wa cF cA
      wfn wa vy cF crn cB csn cA c0 wne vx cv cF cfv cB wceq vx cA wral wa cF
      cA wfn wa vy cv cF crn wcel cB vy cv wceq vy cv cB csn wcel cF cA wfn vy
      cv cF crn wcel vz cv cF cfv vy cv wceq vz cA wrex cA c0 wne vx cv cF cfv
      cB wceq vx cA wral wa cB vy cv wceq vz cA vy cv cF fvelrnb vx cv cF cfv
      cB wceq vx cA wral vz cv cF cfv vy cv wceq vz cA wrex cB vy cv wceq vz cA
      wrex cA c0 wne cB vy cv wceq vx cv cF cfv cB wceq vx cA wral vz cv cF cfv
      vy cv wceq cB vy cv wceq vz cA vx cv cF cfv cB wceq vx cA wral vz cv cA
      wcel wa vz cv cF cfv cB vy cv vx cv cF cfv cB wceq vz cv cF cfv cB wceq
      vx vz cv cA vx cv vz cv wceq vx cv cF cfv vz cv cF cfv cB vx cv vz cv cF
      fveq2 eqeq1d rspccva eqeq1d rexbidva cA c0 wne cB vy cv wceq cB vy cv
      wceq vz cA wrex cB vy cv wceq vz cA r19.9rzv bicomd sylan9bbr sylan9bbr
      vy cv cB csn wcel vy cv cB wceq cB vy cv wceq vy cB elsn vy cv cB eqcom
      bitr2i syl6bb eqrdv an32s exp31 imdistand cF cA wfn cF crn cB csn wceq wa
      cA cB csn cF wfo cA cB csn cF wf cA cB csn cF df-fo cA cB csn cF fof
      sylbir syl6 pm2.61ine impbii $.

    $( Two ways to express a constant function.  (Contributed by NM,
       15-Mar-2007.) $)
    fconst3 $p |- ( F : A --> { B } <->
                  ( F Fn A /\ A C_ ( `' F " { B } ) ) ) $=
      cA cB csn cF wf cF cA wfn vx cv cF cfv cB wceq vx cA wral wa cF cA wfn cA
      cF ccnv cB csn cima wss wa vx cA cB cF fconstfv cF cA wfn vx cv cF cfv cB
      wceq vx cA wral cA cF ccnv cB csn cima wss cF cA wfn cF wfun cA cF cdm
      wss vx cv cF cfv cB wceq vx cA wral cA cF ccnv cB csn cima wss wb cA cF
      fnfun cF cA wfn cF cdm cA wceq cA cF cdm wss cA cF fndm cA cF cdm eqimss2
      syl vx cA cB cF funconstss syl2anc pm5.32i bitri $.
  $}

  $( Two ways to express a constant function.  (Contributed by NM,
     8-Mar-2007.) $)
  fconst4 $p |- ( F : A --> { B } <->
                ( F Fn A /\ ( `' F " { B } ) = A ) ) $=
    cA cB csn cF wf cF cA wfn cA cF ccnv cB csn cima wss wa cF cA wfn cF ccnv
    cB csn cima cA wceq wa cA cB cF fconst3 cF cA wfn cA cF ccnv cB csn cima
    wss cF ccnv cB csn cima cA wceq cF cA wfn cA cF ccnv cB csn cima wss cF
    ccnv cB csn cima cA wss cA cF ccnv cB csn cima wss wa cF ccnv cB csn cima
    cA wceq cF cA wfn cF ccnv cB csn cima cA wss cA cF ccnv cB csn cima wss cF
    cA wfn cF cdm cF ccnv cB csn cima cA cF cB csn cnvimass cA cF fndm syl5sseq
    biantrurd cF ccnv cB csn cima cA eqss syl6bbr pm5.32i bitri $.

  ${
    $d x y A $.  $d x y B $.
    $( The restriction of a function to a set exists.  Compare Proposition 6.17
       of [TakeutiZaring] p. 28.  (Contributed by NM, 7-Apr-1995.)  (Revised by
       Mario Carneiro, 22-Jun-2013.) $)
    resfunexg $p |- ( ( Fun A /\ B e. C ) -> ( A |` B ) e. _V ) $=
      cA wfun cB cC wcel wa cA cB cres vx cA cB cres cdm vx cv vx cv cA cB cres
      cfv cop cmpt cA cB cres cdm cima cvv cA wfun cB cC wcel wa cA cB cres vx
      cA cB cres cdm vx cv vx cv cA cB cres cfv cop cmpt crn vx cA cB cres cdm
      vx cv vx cv cA cB cres cfv cop cmpt cA cB cres cdm cima cA wfun cB cC
      wcel wa cA cB cres vx cA cB cres cdm vx cv cA cB cres cfv cmpt vx cA cB
      cres cdm vx cv vx cv cA cB cres cfv cop cmpt crn cA wfun cB cC wcel wa cA
      cB cres cA cB cres cdm wfn cA cB cres vx cA cB cres cdm vx cv cA cB cres
      cfv cmpt wceq cA wfun cB cC wcel wa cA cB cres wfun cA cB cres cA cB cres
      cdm wfn cA wfun cA cB cres wfun cB cC wcel cB cA funres adantr cA cB cres
      funfn sylib vx cA cB cres cdm cA cB cres dffn5 sylib vx cA cB cres cdm vx
      cv cA cB cres cfv vx cv cA cB cres fvex fnasrn syl6eq vx cA cB cres cdm
      vx cv vx cv cA cB cres cfv cop cmpt vx cA cB cres cdm vx cv vx cv cA cB
      cres cfv cop cmpt cdm cima vx cA cB cres cdm vx cv vx cv cA cB cres cfv
      cop cmpt cA cB cres cdm cima vx cA cB cres cdm vx cv vx cv cA cB cres cfv
      cop cmpt crn vx cA cB cres cdm vx cv vx cv cA cB cres cfv cop cmpt cdm cA
      cB cres cdm vx cA cB cres cdm vx cv vx cv cA cB cres cfv cop cmpt vx cA
      cB cres cdm vx cv vx cv cA cB cres cfv cop vx cA cB cres cdm vx cv vx cv
      cA cB cres cfv cop cmpt vx cv vx cv cA cB cres cfv opex vx cA cB cres cdm
      vx cv vx cv cA cB cres cfv cop cmpt eqid dmmpti imaeq2i vx cA cB cres cdm
      vx cv vx cv cA cB cres cfv cop cmpt imadmrn eqtr3i syl6eqr cA wfun cB cC
      wcel wa vx cA cB cres cdm vx cv vx cv cA cB cres cfv cop cmpt wfun cA cB
      cres cdm cvv wcel vx cA cB cres cdm vx cv vx cv cA cB cres cfv cop cmpt
      cA cB cres cdm cima cvv wcel vx cA cB cres cdm vx cv vx cv cA cB cres cfv
      cop funmpt cB cC wcel cA cB cres cdm cvv wcel cA wfun cA cB cC dmresexg
      adantl vx cA cB cres cdm vx cv vx cv cA cB cres cfv cop cmpt cA cB cres
      cdm cvv funimaexg sylancr eqeltrd $.
  $}

  $( The restriction of a function to a set exists.  Compare Proposition 6.17
     of [TakeutiZaring] p. 28.  This version has a shorter proof than
     ~ resfunexg but requires ~ ax-pow .  (Contributed by NM, 7-Apr-1995.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  resfunexgALT $p |- ( ( Fun A /\ B e. C ) -> ( A |` B ) e. _V ) $=
    cA wfun cB cC wcel wa cA cB cres cdm cvv wcel cA cB cres crn cvv wcel wa cA
    cB cres cdm cA cB cres crn cxp cvv wcel cA cB cres cvv wcel cA wfun cB cC
    wcel wa cA cB cres cdm cvv wcel cA cB cres crn cvv wcel cB cC wcel cA cB
    cres cdm cvv wcel cA wfun cA cB cC dmresexg adantl cA wfun cB cC wcel wa cA
    cB cres crn cA cB cima cvv cA cB df-ima cA cB cC funimaexg syl5eqelr jca cA
    cB cres cdm cA cB cres crn cvv cvv xpexg cA cB cres cA cB cres cdm cA cB
    cres crn cxp wss cA cB cres cdm cA cB cres crn cxp cvv wcel cA cB cres cvv
    wcel cA cB cres wrel cA cB cres cA cB cres cdm cA cB cres crn cxp wss cA cB
    relres cA cB cres relssdmrn ax-mp cA cB cres cA cB cres cdm cA cB cres crn
    cxp cvv ssexg mpan 3syl $.

  $( Existence of a composition when the first member is a function.
     (Contributed by NM, 8-Oct-2007.) $)
  cofunexg $p |- ( ( Fun A /\ B e. C ) -> ( A o. B ) e. _V ) $=
    cA wfun cB cC wcel wa cA cB ccom cA cB ccom cdm cA cB ccom crn cxp wss cA
    cB ccom cdm cA cB ccom crn cxp cvv wcel cA cB ccom cvv wcel cA cB ccom wrel
    cA cB ccom cA cB ccom cdm cA cB ccom crn cxp wss cA cB relco cA cB ccom
    relssdmrn ax-mp cA wfun cB cC wcel wa cA cB ccom cdm cvv wcel cA cB ccom
    crn cvv wcel cA cB ccom cdm cA cB ccom crn cxp cvv wcel cB cC wcel cA cB
    ccom cdm cvv wcel cA wfun cB cC wcel cA cB ccom cdm cB cdm wss cB cdm cvv
    wcel cA cB ccom cdm cvv wcel cA cB dmcoss cB cC dmexg cA cB ccom cdm cB cdm
    cvv ssexg sylancr adantl cA wfun cB cC wcel wa cA cB ccom crn cA cB crn
    cres crn cvv cA cB rnco cA wfun cB cC wcel wa cA cB crn cres cvv wcel cA cB
    crn cres crn cvv wcel cB cC wcel cA wfun cB crn cvv wcel cA cB crn cres cvv
    wcel cB cC rnexg cA cB crn cvv resfunexg sylan2 cA cB crn cres cvv rnexg
    syl syl5eqel cA cB ccom cdm cA cB ccom crn cvv cvv xpexg syl2anc cA cB ccom
    cA cB ccom cdm cA cB ccom crn cxp cvv ssexg sylancr $.

  $( Existence of a composition when the second member is one-to-one.
     (Contributed by NM, 8-Oct-2007.) $)
  cofunex2g $p |- ( ( A e. V /\ Fun `' B ) -> ( A o. B ) e. _V ) $=
    cB ccnv wfun cA cV wcel cA cB ccom cvv wcel cB ccnv wfun cA cV wcel wa cB
    ccnv cA ccnv ccom cvv wcel cA cB ccom cvv wcel cA cV wcel cB ccnv wfun cA
    ccnv cvv wcel cB ccnv cA ccnv ccom cvv wcel cA cV cnvexg cB ccnv cA ccnv
    cvv cofunexg sylan2 cB ccnv cA ccnv ccom cvv wcel cA cB ccom cB ccnv cA
    ccnv ccom ccnv cvv cB ccnv cA ccnv ccom ccnv cA ccnv ccnv cB ccnv ccnv ccom
    cA ccnv ccnv cB ccom cA cB ccom cB ccnv cA ccnv cnvco cA ccnv ccnv cB
    cocnvcnv2 cA cB cocnvcnv1 3eqtrri cB ccnv cA ccnv ccom cvv cnvexg syl5eqel
    syl ancoms $.

  $( If the domain of a function is a set, the function is a set.  Theorem
     6.16(1) of [TakeutiZaring] p. 28.  This theorem is derived using the Axiom
     of Replacement in the form of ~ resfunexg .  See ~ fnexALT for alternate
     proof.  (Contributed by NM, 14-Aug-1994.)  (Proof shortened by Andrew
     Salmon, 17-Sep-2011.) $)
  fnex $p |- ( ( F Fn A /\ A e. B ) -> F e. _V ) $=
    cF cA wfn cA cB wcel wa cF wrel cF cF cdm cres cvv wcel cF cvv wcel cF cA
    wfn cF wrel cA cB wcel cA cF fnrel adantr cF cA wfn cF wfun cF cdm cA wceq
    wa cA cB wcel cF cF cdm cres cvv wcel cF cA df-fn cF wfun cF cdm cA wceq cA
    cB wcel cF cF cdm cres cvv wcel cF cdm cA wceq cA cB wcel wa cF wfun cF cdm
    cB wcel cF cF cdm cres cvv wcel cA cB wcel cF cdm cA wceq cF cdm cB wcel cA
    cB cF cdm eleq1a impcom cF cF cdm cB resfunexg sylan2 anassrs sylanb cF
    wrel cF cF cdm cres cvv wcel cF cvv wcel cF wrel cF cF cdm cres cF cvv cF
    resdm eleq1d biimpa syl2anc $.

  $( If the domain of a function is a set, the function is a set.  Theorem
     6.16(1) of [TakeutiZaring] p. 28.  This theorem is derived using the Axiom
     of Replacement in the form of ~ funimaexg .  This version of ~ fnex uses
     ~ ax-pow , whereas ~ fnex does not.  (Contributed by NM, 14-Aug-1994.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  fnexALT $p |- ( ( F Fn A /\ A e. B ) -> F e. _V ) $=
    cF cA wfn cA cB wcel wa cF cF cdm cF crn cxp wss cF cdm cF crn cxp cvv wcel
    cF cvv wcel cF cA wfn cF cF cdm cF crn cxp wss cA cB wcel cF cA wfn cF wrel
    cF cF cdm cF crn cxp wss cA cF fnrel cF relssdmrn syl adantr cF cA wfn cA
    cB wcel wa cF cdm cB wcel cF crn cvv wcel cF cdm cF crn cxp cvv wcel cF cA
    wfn cF cdm cB wcel cA cB wcel cF cA wfn cF cdm cA cB cA cF fndm eleq1d
    biimpar cF cA wfn cA cB wcel cF cA cima cvv wcel cF crn cvv wcel cF cA wfn
    cF wfun cA cB wcel cF cA cima cvv wcel cA cF fnfun cF cA cB funimaexg sylan
    cF cA wfn cF crn cvv wcel cF cA cima cvv wcel cF cA wfn cF crn cF cA cima
    cvv cF cA wfn cF crn cF cF cdm cima cF cA cima cF imadmrn cF cA wfn cF cdm
    cA cF cA cF fndm imaeq2d syl5eqr eleq1d biimpar syldan cF cdm cF crn cB cvv
    xpexg syl2anc cF cF cdm cF crn cxp cvv ssexg syl2anc $.

  $( If the domain of a function exists, so the function.  Part of Theorem
     4.15(v) of [Monk1] p. 46.  This theorem is derived using the Axiom of
     Replacement in the form of ~ fnex .  (Note:  Any resemblance between
     F.U.N.E.X. and "Have You Any Eggs" is purely a coincidence originated by
     Swedish chefs.)  (Contributed by NM, 11-Nov-1995.) $)
  funex $p |- ( ( Fun F /\ dom F e. B ) -> F e. _V ) $=
    cF wfun cF cF cdm wfn cF cdm cB wcel cF cvv wcel cF funfn cF cdm cB cF fnex
    sylanb $.

  ${
    $d x y A $.
    opabex.1 $e |- A e. _V $.
    opabex.2 $e |- ( x e. A -> E* y ph ) $.
    $( Existence of a function expressed as class of ordered pairs.
       (Contributed by NM, 21-Jul-1996.) $)
    opabex $p |- { <. x , y >. | ( x e. A /\ ph ) } e. _V $=
      vx cv cA wcel wph wa vx vy copab wfun vx cv cA wcel wph wa vx vy copab
      cdm cvv wcel vx cv cA wcel wph wa vx vy copab cvv wcel vx cv cA wcel wph
      wa vx vy copab wfun vx cv cA wcel wph wa vy wmo vx vx cv cA wcel wph wa
      vx vy funopab vx cv cA wcel wph wa vy wmo vx cv cA wcel wph vy wmo wi
      opabex.2 vx cv cA wcel wph vy moanimv mpbir mpgbir vx cv cA wcel wph wa
      vx vy copab cdm cA opabex.1 wph vx vy cA dmopabss ssexi cvv vx cv cA wcel
      wph wa vx vy copab funex mp2an $.
  $}

  ${
    $d x y A $.  $d y B $.
    $( If the domain of a function given by maps-to notation is a set, the
       function is a set.  (Contributed by FL, 6-Jun-2011.)  (Revised by Mario
       Carneiro, 31-Aug-2015.) $)
    mptexg $p |- ( A e. V -> ( x e. A |-> B ) e. _V ) $=
      cA cV wcel vx cA cB cmpt wfun vx cA cB cmpt cdm cvv wcel vx cA cB cmpt
      cvv wcel vx cA cB funmpt vx cA cB cmpt cdm cA wss cA cV wcel vx cA cB
      cmpt cdm cvv wcel vx cA cB vx cA cB cmpt vx cA cB cmpt eqid dmmptss vx cA
      cB cmpt cdm cA cV ssexg mpan cvv vx cA cB cmpt funex sylancr $.
  $}

  ${
    $d x y A $.
    mptex.1 $e |- A e. _V $.
    $( If the domain of a function given by maps-to notation is a set, the
       function is a set.  (Contributed by NM, 22-Apr-2005.)  (Revised by Mario
       Carneiro, 20-Dec-2013.) $)
    mptex $p |- ( x e. A |-> B ) e. _V $=
      cA cvv wcel vx cA cB cmpt cvv wcel mptex.1 vx cA cB cvv mptexg ax-mp $.
  $}

  $( If the domain of a function exists, so does its range.  Part of Theorem
     4.15(v) of [Monk1] p. 46.  This theorem is derived using the Axiom of
     Replacement in the form of ~ funex .  (Contributed by NM, 11-Nov-1995.) $)
  funrnex $p |- ( dom F e. B -> ( Fun F -> ran F e. _V ) ) $=
    cF wfun cF cdm cB wcel cF cvv wcel cF crn cvv wcel cF wfun cF cdm cB wcel
    cF cvv wcel cB cF funex ex cF cvv rnexg syl6com $.

  ${
    $d ph w v $.  $d x y z w v $.
    $( A version of the Axiom of Replacement.  Normally ` ph ` would have free
       variables ` x ` and ` y ` .  Axiom 6 of [Kunen] p. 12.  The Separation
       Scheme ~ ax-sep cannot be derived from this version and must be stated
       as a separate axiom in an axiom system (such as Kunen's) that uses this
       version in place of our ~ ax-rep .  (Contributed by NM, 10-Oct-2003.) $)
    zfrep6 $p |- ( A. x e. z E! y ph -> E. w A. x e. z E. y e. w ph ) $=
      wph vy weu vx vz cv wral vx cv vz cv wcel wph wa vx vy copab crn cvv wcel
      wph vy vx cv vz cv wcel wph wa vx vy copab crn wrex vx vz cv wral wph vy
      vw cv wrex vx vz cv wral vw wex wph vy weu vx vz cv wral vx cv vz cv wcel
      wph wa vx vy copab cdm cvv wcel vx cv vz cv wcel wph wa vx vy copab wfun
      vx cv vz cv wcel wph wa vx vy copab crn cvv wcel wph vy weu vx vz cv wral
      vx cv vz cv wcel wph wa vx vy copab cdm vz cv cvv wph vy weu vx vz cv
      wral vz cv wph vy wex vx vz cv crab vx cv vz cv wcel wph wa vx vy copab
      cdm wph vy weu vx vz cv wral wph vy wex vx vz cv wral vz cv wph vy wex vx
      vz cv crab wceq wph vy weu wph vy wex vx vz cv wph vy euex ralimi wph vy
      wex vx vz cv rabid2 sylibr vx cv vz cv wcel wph wa vy wex vx cab vx cv vz
      cv wcel wph vy wex wa vx cab vx cv vz cv wcel wph wa vx vy copab cdm wph
      vy wex vx vz cv crab vx cv vz cv wcel wph wa vy wex vx cv vz cv wcel wph
      vy wex wa vx vx cv vz cv wcel wph vy 19.42v abbii vx cv vz cv wcel wph wa
      vx vy dmopab wph vy wex vx vz cv df-rab 3eqtr4i syl6reqr vz vex syl6eqel
      vx cv vz cv wcel wph vy weu wi vx wal vx cv vz cv wcel wph wa vy wmo vx
      wal wph vy weu vx vz cv wral vx cv vz cv wcel wph wa vx vy copab wfun vx
      cv vz cv wcel wph vy weu wi vx cv vz cv wcel wph wa vy wmo vx vx cv vz cv
      wcel wph vy weu wi vx cv vz cv wcel wph vy wmo wi vx cv vz cv wcel wph wa
      vy wmo wph vy weu wph vy wmo vx cv vz cv wcel wph vy eumo imim2i vx cv vz
      cv wcel wph vy moanimv sylibr alimi wph vy weu vx vz cv df-ral vx cv vz
      cv wcel wph wa vx vy funopab 3imtr4i cvv vx cv vz cv wcel wph wa vx vy
      copab funrnex sylc wph vy weu vx vz cv wral wph vy vx cv vz cv wcel wph
      wa vx vy copab crn wrex vx vz cv wph vy weu vx vz cv nfra1 wph vy weu vx
      vz cv wral vx cv vz cv wcel vx cv vx cv vz cv wcel wph wa vx vy copab cdm
      wcel wph vy vx cv vz cv wcel wph wa vx vy copab crn wrex wph vy weu vx vz
      cv wral vx cv vz cv wcel wph wa vx vy copab cdm vz cv vx cv wph vy weu vx
      vz cv wral vz cv wph vy wex vx vz cv crab vx cv vz cv wcel wph wa vx vy
      copab cdm wph vy weu vx vz cv wral wph vy wex vx vz cv wral vz cv wph vy
      wex vx vz cv crab wceq wph vy weu wph vy wex vx vz cv wph vy euex ralimi
      wph vy wex vx vz cv rabid2 sylibr vx cv vz cv wcel wph wa vy wex vx cab
      vx cv vz cv wcel wph vy wex wa vx cab vx cv vz cv wcel wph wa vx vy copab
      cdm wph vy wex vx vz cv crab vx cv vz cv wcel wph wa vy wex vx cv vz cv
      wcel wph vy wex wa vx vx cv vz cv wcel wph vy 19.42v abbii vx cv vz cv
      wcel wph wa vx vy dmopab wph vy wex vx vz cv df-rab 3eqtr4i syl6reqr
      eleq2d vx cv vz cv wcel wph wa vy wex vy cv vx cv vz cv wcel wph wa vx vy
      copab crn wcel wph wa vy wex vx cv vx cv vz cv wcel wph wa vx vy copab
      cdm wcel wph vy vx cv vz cv wcel wph wa vx vy copab crn wrex vx cv vz cv
      wcel wph wa vy cv vx cv vz cv wcel wph wa vx vy copab crn wcel wph wa vy
      vx cv vz cv wcel wph vy cv vx cv vz cv wcel wph wa vx vy copab crn wcel
      vx cv vz cv wcel wph vy cv vx cv vz cv wcel wph wa vx vy copab crn wcel
      vx cv vz cv wcel wph wa vx cv vy cv cop vx cv vz cv wcel wph wa vx vy
      copab wcel vy cv vx cv vz cv wcel wph wa vx vy copab crn wcel vx cv vz cv
      wcel wph wa vx vy opabid vx cv vy cv vx cv vz cv wcel wph wa vx vy copab
      vx vex vy vex opelrn sylbir ex impac eximi vx cv vz cv wcel wph wa vy wex
      vx vx cv vz cv wcel wph wa vx vy copab cdm vx cv vz cv wcel wph wa vx vy
      dmopab abeq2i wph vy vx cv vz cv wcel wph wa vx vy copab crn df-rex
      3imtr4i syl6bir ralrimi wph vy vw cv wrex vx vz cv wral wph vy vx cv vz
      cv wcel wph wa vx vy copab crn wrex vx vz cv wral vw vx cv vz cv wcel wph
      wa vx vy copab crn cvv vw cv vx cv vz cv wcel wph wa vx vy copab crn wceq
      wph vy vw cv wrex wph vy vx cv vz cv wcel wph wa vx vy copab crn wrex vx
      vz cv vx vw cv vx cv vz cv wcel wph wa vx vy copab crn vx vx cv vz cv
      wcel wph wa vx vy copab vx cv vz cv wcel wph wa vx vy nfopab1 nfrn nfeq2
      wph vy vw cv vx cv vz cv wcel wph wa vx vy copab crn vy vw cv nfcv vy vx
      cv vz cv wcel wph wa vx vy copab vx cv vz cv wcel wph wa vx vy nfopab2
      nfrn rexeqf ralbid spcegv sylc $.
  $}

  $( If the domain of a mapping is a set, the function is a set.  (Contributed
     by NM, 3-Oct-1999.) $)
  fex $p |- ( ( F : A --> B /\ A e. C ) -> F e. _V ) $=
    cA cB cF wf cF cA wfn cA cC wcel cF cvv wcel cA cB cF ffn cA cC cF fnex
    sylan $.

  $( If the domain of an onto function exists, so does its codomain.
     (Contributed by NM, 23-Jul-2004.) $)
  fornex $p |- ( A e. C -> ( F : A -onto-> B -> B e. _V ) ) $=
    cA cB cF wfo cA cC wcel cB cvv wcel cA cB cF wfo cF cdm cC wcel cF crn cvv
    wcel cA cC wcel cB cvv wcel cA cB cF wfo cF wfun cF cdm cC wcel cF crn cvv
    wcel cA cB cF fofun cC cF funrnex syl5com cA cB cF wfo cF cdm cA cC cA cB
    cF wfo cA cB cF wf cF cdm cA wceq cA cB cF fof cA cB cF fdm syl eleq1d cA
    cB cF wfo cF crn cB cvv cA cB cF forn eleq1d 3imtr3d com12 $.

  $( If the codomain of a one-to-one function exists, so does its domain.  This
     theorem is equivalent to the Axiom of Replacement ~ ax-rep .  (Contributed
     by NM, 4-Sep-2004.) $)
  f1dmex $p |- ( ( F : A -1-1-> B /\ B e. C ) -> A e. _V ) $=
    cA cB cF wf1 cB cC wcel cA cvv wcel cA cB cF wf1 cB cC wcel cF crn cvv wcel
    cA cvv wcel cA cB cF wf1 cB cC wcel cF crn cvv wcel cA cB cF wf1 cF crn cB
    wss cB cC wcel cF crn cvv wcel cA cB cF wf1 cA cB cF wf cF crn cB wss cA cB
    cF f1f cA cB cF frn syl cF crn cB cC ssexg sylan ex cA cB cF wf1 cF crn cA
    cF ccnv wfo cF crn cvv wcel cA cvv wcel cA cB cF wf1 cF crn cA cF ccnv wf1o
    cF crn cA cF ccnv wfo cA cB cF f1cnv cF crn cA cF ccnv f1ofo syl cF crn cA
    cvv cF ccnv fornex syl5com syld imp $.

  ${
    $d f x y z A $.  $d f y z B $.
    eufnfv.1 $e |- A e. _V $.
    eufnfv.2 $e |- B e. _V $.
    $( A function is uniquely determined by its values.  (Contributed by NM,
       31-Aug-2011.) $)
    eufnfv $p |- E! f ( f Fn A /\ A. x e. A ( f ` x ) = B ) $=
      vf cv cA wfn vx cv vf cv cfv cB wceq vx cA wral wa vf weu vf cv cA wfn vx
      cv vf cv cfv cB wceq vx cA wral wa vf cv vz cv wceq wb vf wal vz wex vf
      cv cA wfn vx cv vf cv cfv cB wceq vx cA wral wa vf cv vx cA cB cmpt wceq
      wb vf cv cA wfn vx cv vf cv cfv cB wceq vx cA wral wa vf cv vz cv wceq wb
      vf wal vz wex vf vf cv cA wfn vx cv vf cv cfv cB wceq vx cA wral wa vf cv
      vz cv wceq wb vf wal vf cv cA wfn vx cv vf cv cfv cB wceq vx cA wral wa
      vf cv vx cA cB cmpt wceq wb vf wal vz vx cA cB cmpt vx cA cB eufnfv.1
      mptex vz cv vx cA cB cmpt wceq vf cv cA wfn vx cv vf cv cfv cB wceq vx cA
      wral wa vf cv vz cv wceq wb vf cv cA wfn vx cv vf cv cfv cB wceq vx cA
      wral wa vf cv vx cA cB cmpt wceq wb vf vz cv vx cA cB cmpt wceq vf cv vz
      cv wceq vf cv vx cA cB cmpt wceq vf cv cA wfn vx cv vf cv cfv cB wceq vx
      cA wral wa vz cv vx cA cB cmpt vf cv eqeq2 bibi2d albidv spcev vf cv vx
      cA cB cmpt wceq vf cv cA wfn vf cv vx cA cB cmpt wceq wa vf cv cA wfn vx
      cv vf cv cfv cB wceq vx cA wral wa vf cv vx cA cB cmpt wceq vf cv cA wfn
      vf cv vx cA cB cmpt wceq vf cv cA wfn vx cA cB cmpt cA wfn vx cA cB vx cA
      cB cmpt eufnfv.2 vx cA cB cmpt eqid fnmpti cA vf cv vx cA cB cmpt fneq1
      mpbiri pm4.71ri vf cv cA wfn vf cv vx cA cB cmpt wceq vx cv vf cv cfv cB
      wceq vx cA wral vf cv cA wfn vf cv vx cA cB cmpt wceq vx cA vx cv vf cv
      cfv cmpt vx cA cB cmpt wceq vx cv vf cv cfv cB wceq vx cA wral vf cv cA
      wfn vf cv vx cA vx cv vf cv cfv cmpt wceq vf cv vx cA cB cmpt wceq vx cA
      vx cv vf cv cfv cmpt vx cA cB cmpt wceq wb vx cA vf cv dffn5 vf cv vx cA
      vx cv vf cv cfv cmpt vx cA cB cmpt eqeq1 sylbi vx cv vf cv cfv cvv wcel
      vx cA wral vx cA vx cv vf cv cfv cmpt vx cA cB cmpt wceq vx cv vf cv cfv
      cB wceq vx cA wral wb vx cv vf cv cfv cvv wcel vx cA vx cv vf cv fvex
      rgenw vx cA vx cv vf cv cfv cB cvv mpteqb ax-mp syl6bb pm5.32i bitr2i mpg
      vf cv cA wfn vx cv vf cv cfv cB wceq vx cA wral wa vf vz df-eu mpbir $.
  $}

  $( A function's value in a preimage belongs to the image.  (Contributed by
     NM, 23-Sep-2003.) $)
  funfvima $p |- ( ( Fun F /\ B e. dom F ) -> ( B e. A ->
                 ( F ` B ) e. ( F " A ) ) ) $=
    cF wfun cB cF cdm wcel wa cB cA wcel cB cF cfv cF cA cima wcel cB cA wcel
    cF wfun cB cF cdm wcel cB cA wcel cB cF cfv cF cA cima wcel wi cF wfun cB
    cA wcel cB cF cdm wcel cB cA wcel cB cF cfv cF cA cima wcel wi wi cF wfun
    cB cA wcel cB cF cdm wcel cB cA wcel cB cF cfv cF cA cima wcel wi cB cA
    wcel cB cF cdm wcel wa cB cF cA cres cdm wcel cF wfun cB cA wcel cB cF cfv
    cF cA cima wcel wi cB cA cF cdm cF cA cres cdm cF cA dmres elin2 cF wfun cB
    cF cA cres cdm wcel cB cA wcel cB cF cfv cF cA cima wcel wi cF wfun cB cF
    cA cres cdm wcel wa cB cF cfv cF cA cima wcel cB cA wcel cB cF cA cres cfv
    cF cA cres crn wcel cF wfun cF cA cres wfun cB cF cA cres cdm wcel cB cF cA
    cres cfv cF cA cres crn wcel cA cF funres cB cF cA cres fvelrn sylan cB cA
    wcel cB cF cA cres cfv cF cA cres crn wcel cB cF cfv cF cA cres crn wcel cB
    cF cfv cF cA cima wcel cB cA wcel cB cF cA cres cfv cB cF cfv cF cA cres
    crn cB cA cF fvres eleq1d cF cA cima cF cA cres crn cB cF cfv cF cA df-ima
    eleq2i syl6rbbr syl5ibrcom ex syl5bir exp3a com12 imp3a pm2.43b $.

  $( A function's value in an included preimage belongs to the image.
     (Contributed by NM, 3-Feb-1997.) $)
  funfvima2 $p |- ( ( Fun F /\ A C_ dom F ) -> ( B e. A ->
                  ( F ` B ) e. ( F " A ) ) ) $=
    cF wfun cA cF cdm wss cB cA wcel cB cF cfv cF cA cima wcel wi cA cF cdm wss
    cB cA wcel cB cF cdm wcel wi cF wfun cB cA wcel cB cF cfv cF cA cima wcel
    wi cA cF cdm cB ssel cF wfun cB cA wcel cB cF cdm wcel cB cF cfv cF cA cima
    wcel cF wfun cB cF cdm wcel cB cA wcel cB cF cfv cF cA cima wcel cF wfun cB
    cF cdm wcel cB cA wcel cB cF cfv cF cA cima wcel wi cA cB cF funfvima ex
    com23 a2d syl5 imp $.

  ${
    $d x A $.  $d x F $.  $d x G $.
    $( A class including a function contains the function's value in the image
       of the singleton of the argument.  (Contributed by NM, 23-Mar-2004.) $)
    funfvima3 $p |- ( ( Fun F /\ F C_ G ) -> ( A e. dom F ->
                    ( F ` A ) e. ( G " { A } ) ) ) $=
      cF cG wss cF wfun cA cF cdm wcel cA cF cfv cG cA csn cima wcel wi cF cG
      wss cF wfun cA cF cdm wcel cA cF cfv cG cA csn cima wcel cF cG wss cF
      wfun cA cF cdm wcel wa wa cA cF cfv cG cA csn cima wcel cA cA cF cfv cop
      cG wcel cF cG wss cF wfun cA cF cdm wcel wa cA cA cF cfv cop cG wcel cF
      wfun cA cF cdm wcel wa cA cA cF cfv cop cF wcel cF cG wss cA cA cF cfv
      cop cG wcel cA cF funfvop cF cG cA cA cF cfv cop ssel syl5 imp cA cF cdm
      wcel cA cF cfv cG cA csn cima wcel cA cA cF cfv cop cG wcel wb cF cG wss
      cF wfun cA cF cfv cG vx cv csn cima wcel vx cv cA cF cfv cop cG wcel cA
      cF cfv cG cA csn cima wcel cA cA cF cfv cop cG wcel vx cA cF cdm vx cv cA
      wceq cG vx cv csn cima cG cA csn cima cA cF cfv vx cv cA wceq vx cv csn
      cA csn cG vx cv cA sneq imaeq2d eleq2d vx cv cA wceq vx cv cA cF cfv cop
      cA cA cF cfv cop cG vx cv cA cA cF cfv opeq1 eleq1d cG vx cv cA cF cfv vx
      vex cA cF fvex elimasn vtoclbg ad2antll mpbird exp32 impcom $.
  $}

  $( The function value of an operand in a set is contained in the image of
     that set, using the ` Fn ` abbreviation.  (Contributed by Stefan O'Rear,
     10-Mar-2015.) $)
  fnfvima $p |- ( ( F Fn A /\ S C_ A /\ X e. S ) -> ( F ` X ) e. ( F " S ) ) $=
    cF cA wfn cS cA wss cX cS wcel w3a cF wfun cS cF cdm wss wa cX cS wcel cX
    cF cfv cF cS cima wcel cF cA wfn cS cA wss cX cS wcel w3a cF wfun cS cF cdm
    wss cF cA wfn cS cA wss cF wfun cX cS wcel cA cF fnfun 3ad2ant1 cF cA wfn
    cS cA wss cX cS wcel w3a cS cA cF cdm cF cA wfn cS cA wss cX cS wcel simp2
    cF cA wfn cS cA wss cF cdm cA wceq cX cS wcel cA cF fndm 3ad2ant1 sseqtr4d
    jca cF cA wfn cS cA wss cX cS wcel simp3 cS cX cF funfvima2 sylc $.

  ${
    $d ph y $.  $d ps x $.  $d F x y $.  $d B x y $.  $d A x y $.
    rexima.x $e |- ( x = ( F ` y ) -> ( ph <-> ps ) ) $.
    $( Existential quantification under an image in terms of the base set.
       (Contributed by Stefan O'Rear, 21-Jan-2015.) $)
    rexima $p |- ( ( F Fn A /\ B C_ A ) ->
        ( E. x e. ( F " B ) ph <-> E. y e. B ps ) ) $=
      cF cA wfn cB cA wss wa wph wps vx vy vy cv cF cfv cF cB cima cB cvv vy cv
      cF cfv cvv wcel cF cA wfn cB cA wss wa vy cv cB wcel wa vy cv cF fvex a1i
      cF cA wfn cB cA wss wa vx cv cF cB cima wcel vy cv cF cfv vx cv wceq vy
      cB wrex vx cv vy cv cF cfv wceq vy cB wrex vy cA cB vx cv cF fvelimab vy
      cv cF cfv vx cv wceq vx cv vy cv cF cfv wceq vy cB vy cv cF cfv vx cv
      eqcom rexbii syl6bb vx cv vy cv cF cfv wceq wph wps wb cF cA wfn cB cA
      wss wa rexima.x adantl rexxfr2d $.

    $( Universal quantification under an image in terms of the base set.
       (Contributed by Stefan O'Rear, 21-Jan-2015.) $)
    ralima $p |- ( ( F Fn A /\ B C_ A ) ->
        ( A. x e. ( F " B ) ph <-> A. y e. B ps ) ) $=
      cF cA wfn cB cA wss wa wph wps vx vy vy cv cF cfv cF cB cima cB cvv vy cv
      cF cfv cvv wcel cF cA wfn cB cA wss wa vy cv cB wcel wa vy cv cF fvex a1i
      cF cA wfn cB cA wss wa vx cv cF cB cima wcel vy cv cF cfv vx cv wceq vy
      cB wrex vx cv vy cv cF cfv wceq vy cB wrex vy cA cB vx cv cF fvelimab vy
      cv cF cfv vx cv wceq vx cv vy cv cF cfv wceq vy cB vy cv cF cfv vx cv
      eqcom rexbii syl6bb vx cv vy cv cF cfv wceq wph wps wb cF cA wfn cB cA
      wss wa rexima.x adantl ralxfr2d $.
  $}

  ${
    $d A u x y $.  $d R u x y $.
    $( TODO:  This is the same as ~ issref (which has a much longer proof).
       Should we replace ~ issref with this one? - NM 9-May-2016.

       Two ways to state a relation is reflexive.  (Adapted from Tarski.)
       (Contributed by FL, 15-Jan-2012.)  (Proof shortened by Mario Carneiro,
       3-Nov-2015.)  (Proof modification is discouraged.) $)
    idref $p |- ( ( _I |` A ) C_ R <-> A. x e. A x R x ) $=
      vx cv vx cv cop cR wcel vx cA wral vx cA vx cv vx cv cop cmpt crn cR wss
      vx cv vx cv cR wbr vx cA wral cid cA cres cR wss vx cv vx cv cop cR wcel
      vx cA wral cA cR vx cA vx cv vx cv cop cmpt wf vx cA vx cv vx cv cop cmpt
      crn cR wss vx cA cR vx cv vx cv cop vx cA vx cv vx cv cop cmpt vx cA vx
      cv vx cv cop cmpt eqid fmpt cA cR vx cA vx cv vx cv cop cmpt wf vx cA vx
      cv vx cv cop cmpt cA wfn vx cA vx cv vx cv cop cmpt crn cR wss vx cA vx
      cv vx cv cop vx cA vx cv vx cv cop cmpt vx cv vx cv opex vx cA vx cv vx
      cv cop cmpt eqid fnmpti cA cR vx cA vx cv vx cv cop cmpt df-f mpbiran
      bitri vx cv vx cv cR wbr vx cv vx cv cop cR wcel vx cA vx cv vx cv cR
      df-br ralbii cid cA cres vx cA vx cv vx cv cop cmpt crn cR vx cA vx cv
      cmpt cid cA cres vx cA vx cv vx cv cop cmpt crn vx cA mptresid vx cA vx
      cv vx vex fnasrn eqtr3i sseq1i 3bitr4ri $.
  $}

  ${
    $d x y F $.
    $( Upper bound for the class of values of a class.  (Contributed by NM,
       9-Nov-1995.) $)
    fvclss $p |- { y | E. x y = ( F ` x ) } C_ ( ran F u. { (/) } ) $=
      vy cv vx cv cF cfv wceq vx wex vy cab vy cv cF crn wcel vy cv c0 csn wcel
      wo vy cab cF crn c0 csn cun vy cv vx cv cF cfv wceq vx wex vy cv cF crn
      wcel vy cv c0 csn wcel wo vy vy cv vx cv cF cfv wceq vx wex vy cv cF crn
      wcel vy cv c0 csn wcel vy cv vx cv cF cfv wceq vx wex vy cv cF crn wcel
      wn vy cv c0 wceq vy cv c0 csn wcel vy cv vx cv cF cfv wceq vx wex vy cv
      cF crn wcel vy cv c0 vy cv c0 wne vy cv vx cv cF cfv wceq vx wex vy cv cF
      crn wcel vy cv c0 wne vy cv vx cv cF cfv wceq vx wex vx cv vy cv cF wbr
      vx wex vy cv cF crn wcel vy cv c0 wne vy cv vx cv cF cfv wceq vx cv vy cv
      cF wbr vx vy cv vx cv cF cfv wceq vx cv cF cfv vy cv wceq vy cv c0 wne vx
      cv vy cv cF wbr vy cv vx cv cF cfv eqcom vx cv vy cv cF tz6.12i syl5bi
      eximdv vx vy cv cF vy vex elrn syl6ibr com12 necon1bd vy c0 elsn syl6ibr
      orrd ss2abi vy cF crn c0 csn df-un sseqtr4i $.
  $}

  ${
    $d x y F $.
    fvclex.1 $e |- F e. _V $.
    $( Existence of the class of values of a set.  (Contributed by NM,
       9-Nov-1995.) $)
    fvclex $p |- { y | E. x y = ( F ` x ) } e. _V $=
      vy cv vx cv cF cfv wceq vx wex vy cab cF crn c0 csn cun cF crn c0 csn cF
      fvclex.1 rnex p0ex unex vx vy cF fvclss ssexi $.
  $}

  ${
    $d x y z A $.  $d x y z F $.
    fvresex.1 $e |- A e. _V $.
    $( Existence of the class of values of a restricted class.  (Contributed by
       NM, 14-Nov-1995.)  (Revised by Mario Carneiro, 11-Sep-2015.) $)
    fvresex $p |- { y | E. x y = ( ( F |` A ) ` x ) } e. _V $=
      vy cv vx cv vz cA vz cv cF cfv cmpt cfv wceq vx wex vy cab vy cv vx cv cF
      cA cres cfv wceq vx wex vy cab cvv vy cv vx cv vz cA vz cv cF cfv cmpt
      cfv wceq vx wex vy cv vx cv cF cA cres cfv wceq vx wex vy vy cv vx cv vz
      cA vz cv cF cfv cmpt cfv wceq vy cv vx cv cF cA cres cfv wceq vx vx cv vz
      cA vz cv cF cfv cmpt cfv vx cv cF cA cres cfv vy cv vx cv vz cvv vz cv cF
      cfv cmpt cA cres cfv vx cv vz cA vz cv cF cfv cmpt cfv vx cv cF cA cres
      cfv vx cv vz cvv vz cv cF cfv cmpt cA cres vz cA vz cv cF cfv cmpt cA cvv
      wss vz cvv vz cv cF cfv cmpt cA cres vz cA vz cv cF cfv cmpt wceq cA ssv
      vz cvv cA vz cv cF cfv resmpt ax-mp fveq1i vx cv vz cvv vz cv cF cfv cmpt
      cfv vx cv cF cfv wceq vx cv vz cvv vz cv cF cfv cmpt cA cres cfv vx cv cF
      cA cres cfv wceq vx cv cvv wcel vx cv vz cvv vz cv cF cfv cmpt cfv vx cv
      cF cfv wceq vx vex vz vx cv vz cv cF cfv vx cv cF cfv cvv vz cvv vz cv cF
      cfv cmpt vz cv vx cv cF fveq2 vz cvv vz cv cF cfv cmpt eqid vx cv cF fvex
      fvmpt ax-mp vx cv cA vz cvv vz cv cF cfv cmpt cF fveqres ax-mp eqtr3i
      eqeq2i exbii abbii vx vy vz cA vz cv cF cfv cmpt vz cA vz cv cF cfv
      fvresex.1 mptex fvclex eqeltrri $.
  $}

  ${
    $d x y z w A $.  $d y z w B $.
    abrexex.1 $e |- A e. _V $.
    $( Existence of a class abstraction of existentially restricted sets. ` x `
       is normally a free-variable parameter in the class expression
       substituted for ` B ` , which can be thought of as ` B ( x ) ` .  This
       simple-looking theorem is actually quite powerful and appears to involve
       the Axiom of Replacement in an intrinsic way, as can be seen by tracing
       back through the path ~ mptexg , ~ funex , ~ fnex , ~ resfunexg , and
       ~ funimaexg .  See also ~ abrexex2 .  (Contributed by NM, 16-Oct-2003.)
       (Proof shortened by Mario Carneiro, 31-Aug-2015.) $)
    abrexex $p |- { y | E. x e. A y = B } e. _V $=
      vx cA cB cmpt crn vy cv cB wceq vx cA wrex vy cab cvv vx vy cA cB vx cA
      cB cmpt vx cA cB cmpt eqid rnmpt vx cA cB cmpt vx cA cB abrexex.1 mptex
      rnex eqeltrri $.
  $}

  ${
    $d x y z A $.  $d y z B $.
    $( Existence of a class abstraction of existentially restricted sets. ` x `
       is normally a free-variable parameter in ` B ` .  The antecedent assures
       us that ` A ` is a set.  (Contributed by NM, 3-Nov-2003.) $)
    abrexexg $p |- ( A e. V -> { y | E. x e. A y = B } e. _V ) $=
      cA cV wcel vy cv cB wceq vx cA wrex vy cab vx cA cB cmpt crn cvv vx vy cA
      cB vx cA cB cmpt vx cA cB cmpt eqid rnmpt cA cV wcel vx cA cB cmpt cvv
      wcel vx cA cB cmpt crn cvv wcel vx cA cB cV mptexg vx cA cB cmpt cvv
      rnexg syl syl5eqelr $.
  $}

  ${
    $d w y z B $.  $d w x y z A $.
    elabrex.1 $e |- B e. _V $.
    $( Elementhood in an image set.  (Contributed by Mario Carneiro,
       14-Jan-2014.) $)
    elabrex $p |- ( x e. A -> B e. { y | E. x e. A y = B } ) $=
      vx cv cA wcel cB vy cv vx vz cv cB csb wceq vz cA wrex vy cab vy cv cB
      wceq vx cA wrex vy cab vx cv cA wcel cB vx vz cv cB csb wceq vz cA wrex
      cB vy cv vx vz cv cB csb wceq vz cA wrex vy cab wcel vx cv cA wcel wtru
      cB vx vz cv cB csb wceq vz cA wrex tru cB vx vz cv cB csb wceq wtru vz vx
      cv cA vz cv vx cv wceq cB vx vz cv cB csb wceq wtru cB vx vz cv cB csb
      wceq vx cv vz cv vx vz cv cB csbeq1a eqcoms vz cv vx cv wceq a1tru 2thd
      rspcev mpan2 vy cv vx vz cv cB csb wceq vz cA wrex cB vx vz cv cB csb
      wceq vz cA wrex vy cB elabrex.1 vy cv cB wceq vy cv vx vz cv cB csb wceq
      cB vx vz cv cB csb wceq vz cA vy cv cB vx vz cv cB csb eqeq1 rexbidv elab
      sylibr vy cv cB wceq vx cA wrex vy cv vx vz cv cB csb wceq vz cA wrex vy
      vy cv cB wceq vy cv vx vz cv cB csb wceq vx vz cA vy cv cB wceq vz nfv vx
      vy cv vx vz cv cB csb vx vz cv cB nfcsb1v nfeq2 vx cv vz cv wceq cB vx vz
      cv cB csb vy cv vx vz cv cB csbeq1a eqeq2d cbvrex abbii syl6eleqr $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d C w $.  $d D y $.  $d w x y $.  $d w z y $.
    abrexco.1 $e |- B e. _V $.
    abrexco.2 $e |- ( y = B -> C = D ) $.
    $( Composition of two image maps ` C ( y ) ` and ` B ( w ) ` .
       (Contributed by NM, 27-May-2013.) $)
    abrexco $p |- { x | E. y e. { z | E. w e. A z = B } x = C } =
        { x | E. w e. A x = D } $=
      vx cv cC wceq vy vz cv cB wceq vw cA wrex vz cab wrex vx cv cD wceq vw cA
      wrex vx vx cv cC wceq vy vz cv cB wceq vw cA wrex vz cab wrex vy cv cB
      wceq vx cv cC wceq wa vy wex vw cA wrex vx cv cD wceq vw cA wrex vx cv cC
      wceq vy vz cv cB wceq vw cA wrex vz cab wrex vy cv cB wceq vx cv cC wceq
      wa vw cA wrex vy wex vy cv cB wceq vx cv cC wceq wa vy wex vw cA wrex vx
      cv cC wceq vy vz cv cB wceq vw cA wrex vz cab wrex vy cv vz cv cB wceq vw
      cA wrex vz cab wcel vx cv cC wceq wa vy wex vy cv cB wceq vx cv cC wceq
      wa vw cA wrex vy wex vx cv cC wceq vy vz cv cB wceq vw cA wrex vz cab
      df-rex vy cv vz cv cB wceq vw cA wrex vz cab wcel vx cv cC wceq wa vy cv
      cB wceq vx cv cC wceq wa vw cA wrex vy vy cv vz cv cB wceq vw cA wrex vz
      cab wcel vx cv cC wceq wa vy cv cB wceq vw cA wrex vx cv cC wceq wa vy cv
      cB wceq vx cv cC wceq wa vw cA wrex vy cv vz cv cB wceq vw cA wrex vz cab
      wcel vy cv cB wceq vw cA wrex vx cv cC wceq vz cv cB wceq vw cA wrex vy
      cv cB wceq vw cA wrex vz vy cv vy vex vz cv vy cv wceq vz cv cB wceq vy
      cv cB wceq vw cA vz cv vy cv cB eqeq1 rexbidv elab anbi1i vy cv cB wceq
      vx cv cC wceq vw cA r19.41v bitr4i exbii bitri vy cv cB wceq vx cv cC
      wceq wa vw vy cA rexcom4 bitr4i vy cv cB wceq vx cv cC wceq wa vy wex vx
      cv cD wceq vw cA vx cv cC wceq vx cv cD wceq vy cB abrexco.1 vy cv cB
      wceq cC cD vx cv abrexco.2 eqeq2d ceqsexv rexbii bitri abbii $.
  $}

  ${
    $d x y A $.  $d y B $.
    $( The existence of an indexed union. ` x ` is normally a free-variable
       parameter in ` B ` .  (Contributed by NM, 23-Mar-2006.) $)
    iunexg $p |- ( ( A e. V /\ A. x e. A B e. W ) -> U_ x e. A B e. _V ) $=
      cA cV wcel cB cW wcel vx cA wral wa vx cA cB ciun vy cv cB wceq vx cA
      wrex vy cab cuni cvv cB cW wcel vx cA wral vx cA cB ciun vy cv cB wceq vx
      cA wrex vy cab cuni wceq cA cV wcel vx vy cA cB cW dfiun2g adantl cA cV
      wcel vy cv cB wceq vx cA wrex vy cab cuni cvv wcel cB cW wcel vx cA wral
      cA cV wcel vy cv cB wceq vx cA wrex vy cab cvv wcel vy cv cB wceq vx cA
      wrex vy cab cuni cvv wcel vx vy cA cB cV abrexexg vy cv cB wceq vx cA
      wrex vy cab cvv uniexg syl adantr eqeltrd $.
  $}

  ${
    $d A x y z $.  $d V x y z $.  $d W x y z $.  $d ph z $.
    $( Existence of an existentially restricted class abstraction.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    abrexex2g $p |- ( ( A e. V /\ A. x e. A { y | ph } e. W )
                                  -> { y | E. x e. A ph } e. _V ) $=
      cA cV wcel wph vy cab cW wcel vx cA wral wa wph vx cA wrex vy cab vz cv
      wph vy cab wcel vx cA wrex vz cab cvv wph vx cA wrex vy cab wph vy vz wsb
      vx cA wrex vz cab vz cv wph vy cab wcel vx cA wrex vz cab wph vx cA wrex
      wph vy vz wsb vx cA wrex vy vz wph vx cA wrex vz nfv wph vy vz wsb vy vx
      cA vy cA nfcv wph vy vz nfs1v nfrex vy cv vz cv wceq wph wph vy vz wsb vx
      cA wph vy vz sbequ12 rexbidv cbvab vz cv wph vy cab wcel vx cA wrex wph
      vy vz wsb vx cA wrex vz vz cv wph vy cab wcel wph vy vz wsb vx cA wph vz
      vy df-clab rexbii abbii eqtr4i cA cV wcel wph vy cab cW wcel vx cA wral
      wa vz cv wph vy cab wcel vx cA wrex vz cab vx cA wph vy cab ciun cvv vx
      vz cA wph vy cab df-iun vx cA wph vy cab cV cW iunexg syl5eqelr syl5eqel
      $.
  $}

  ${
    $d A x y v w z $.  $d ph v w z $.
    opabex3.1 $e |- A e. _V $.
    opabex3.2 $e |- ( x e. A -> { y | ph } e. _V ) $.
    $( Existence of an ordered pair abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    opabex3 $p |- { <. x , y >. | ( x e. A /\ ph ) } e. _V $=
      vx cA vx cv csn wph vy cab cxp ciun vx cv cA wcel wph wa vx vy copab cvv
      vz vx cA vx cv csn wph vy cab cxp ciun vx cv cA wcel wph wa vx vy copab
      vx cv cA wcel vz cv vx cv csn wph vy cab cxp wcel wa vx wex vz cv vx cv
      vy cv cop wceq vx cv cA wcel wph wa wa vy wex vx wex vz cv vx cA vx cv
      csn wph vy cab cxp ciun wcel vz cv vx cv cA wcel wph wa vx vy copab wcel
      vx cv cA wcel vz cv vx cv csn wph vy cab cxp wcel wa vz cv vx cv vy cv
      cop wceq vx cv cA wcel wph wa wa vy wex vx vx cv cA wcel vz cv vx cv vy
      cv cop wceq wph wa wa vy wex vx cv cA wcel vz cv vx cv vy cv cop wceq wph
      wa vy wex wa vz cv vx cv vy cv cop wceq vx cv cA wcel wph wa wa vy wex vx
      cv cA wcel vz cv vx cv csn wph vy cab cxp wcel wa vx cv cA wcel vz cv vx
      cv vy cv cop wceq wph wa vy 19.42v vz cv vx cv vy cv cop wceq vx cv cA
      wcel wph wa wa vx cv cA wcel vz cv vx cv vy cv cop wceq wph wa wa vy vz
      cv vx cv vy cv cop wceq vx cv cA wcel wph an12 exbii vz cv vx cv csn wph
      vy cab cxp wcel vz cv vx cv vy cv cop wceq wph wa vy wex vx cv cA wcel vz
      cv vx cv csn wph vy cab cxp wcel vz cv vv cv vw cv cop wceq vv cv vx cv
      csn wcel vw cv wph vy cab wcel wa wa vw wex vv wex vz cv vx cv vw cv cop
      wceq vw cv wph vy cab wcel wa vw wex vz cv vx cv vy cv cop wceq wph wa vy
      wex vv vw vz cv vx cv csn wph vy cab elxp vz cv vv cv vw cv cop wceq vv
      cv vx cv csn wcel vw cv wph vy cab wcel wa wa vw wex vv wex vz cv vv cv
      vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy cab wcel wa wa vv wex vw
      wex vz cv vx cv vw cv cop wceq vw cv wph vy cab wcel wa vw wex vz cv vv
      cv vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy cab wcel wa wa vv vw
      excom vz cv vv cv vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy cab
      wcel wa wa vv wex vz cv vx cv vw cv cop wceq vw cv wph vy cab wcel wa vw
      vz cv vv cv vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy cab wcel wa
      wa vv wex vv cv vx cv wceq vz cv vv cv vw cv cop wceq vw cv wph vy cab
      wcel wa wa vv wex vz cv vx cv vw cv cop wceq vw cv wph vy cab wcel wa vz
      cv vv cv vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy cab wcel wa wa
      vv cv vx cv wceq vz cv vv cv vw cv cop wceq vw cv wph vy cab wcel wa wa
      vv vz cv vv cv vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy cab wcel
      wa wa vv cv vx cv csn wcel vz cv vv cv vw cv cop wceq vw cv wph vy cab
      wcel wa wa vv cv vx cv wceq vz cv vv cv vw cv cop wceq vw cv wph vy cab
      wcel wa wa vz cv vv cv vw cv cop wceq vv cv vx cv csn wcel vw cv wph vy
      cab wcel an12 vv cv vx cv csn wcel vv cv vx cv wceq vz cv vv cv vw cv cop
      wceq vw cv wph vy cab wcel wa vv vx cv elsn anbi1i bitri exbii vz cv vv
      cv vw cv cop wceq vw cv wph vy cab wcel wa vz cv vx cv vw cv cop wceq vw
      cv wph vy cab wcel wa vv vx cv vx vex vv cv vx cv wceq vz cv vv cv vw cv
      cop wceq vz cv vx cv vw cv cop wceq vw cv wph vy cab wcel vv cv vx cv
      wceq vv cv vw cv cop vx cv vw cv cop vz cv vv cv vx cv vw cv opeq1 eqeq2d
      anbi1d ceqsexv bitri exbii bitri vz cv vx cv vw cv cop wceq vw cv wph vy
      cab wcel wa vz cv vx cv vy cv cop wceq wph wa vw vy vz cv vx cv vw cv cop
      wceq vw cv wph vy cab wcel vy vz cv vx cv vw cv cop wceq vy nfv wph vy vw
      nfsab1 nfan vz cv vx cv vy cv cop wceq wph wa vw nfv vw cv vy cv wceq vz
      cv vx cv vw cv cop wceq vz cv vx cv vy cv cop wceq vw cv wph vy cab wcel
      wph vw cv vy cv wceq vx cv vw cv cop vx cv vy cv cop vz cv vw cv vy cv vx
      cv opeq2 eqeq2d vw cv vy cv wceq wph wph vy vw wsb vw cv wph vy cab wcel
      wph wph vy vw wsb wb vy cv vw cv wph vy vw sbequ12 eqcoms wph vw vy
      df-clab syl6rbbr anbi12d cbvex 3bitri anbi2i 3bitr4ri exbii vz cv vx cA
      vx cv csn wph vy cab cxp ciun wcel vz cv vx cv csn wph vy cab cxp wcel vx
      cA wrex vx cv cA wcel vz cv vx cv csn wph vy cab cxp wcel wa vx wex vx vz
      cv cA vx cv csn wph vy cab cxp eliun vz cv vx cv csn wph vy cab cxp wcel
      vx cA df-rex bitri vx cv cA wcel wph wa vx vy vz cv elopab 3bitr4i eqriv
      cA cvv wcel vx cv csn wph vy cab cxp cvv wcel vx cA wral vx cA vx cv csn
      wph vy cab cxp ciun cvv wcel opabex3.1 vx cv csn wph vy cab cxp cvv wcel
      vx cA vx cv cA wcel vx cv csn cvv wcel wph vy cab cvv wcel vx cv csn wph
      vy cab cxp cvv wcel vx cv snex opabex3.2 vx cv csn wph vy cab cvv cvv
      xpexg sylancr rgen vx cA vx cv csn wph vy cab cxp cvv cvv iunexg mp2an
      eqeltrri $.
  $}

  ${
    $d x A $.
    iunex.1 $e |- A e. _V $.
    iunex.2 $e |- B e. _V $.
    $( The existence of an indexed union. ` x ` is normally a free-variable
       parameter in the class expression substituted for ` B ` , which can be
       read informally as ` B ( x ) ` .  (Contributed by NM, 13-Oct-2003.) $)
    iunex $p |- U_ x e. A B e. _V $=
      cA cvv wcel cB cvv wcel vx cA wral vx cA cB ciun cvv wcel iunex.1 cB cvv
      wcel vx cA iunex.2 rgenw vx cA cB cvv cvv iunexg mp2an $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d y z C $.
    $( The image of an indexed union is the indexed union of the images.
       (Contributed by Mario Carneiro, 18-Jun-2014.) $)
    imaiun $p |- ( A " U_ x e. B C ) = U_ x e. B ( A " C ) $=
      vy cA vx cB cC ciun cima vx cB cA cC cima ciun vz cv vx cB cC ciun wcel
      vz cv vy cv cop cA wcel wa vz wex vy cv cA cC cima wcel vx cB wrex vy cv
      cA vx cB cC ciun cima wcel vy cv vx cB cA cC cima ciun wcel vz cv cC wcel
      vz cv vy cv cop cA wcel wa vz wex vx cB wrex vz cv cC wcel vz cv vy cv
      cop cA wcel wa vx cB wrex vz wex vy cv cA cC cima wcel vx cB wrex vz cv
      vx cB cC ciun wcel vz cv vy cv cop cA wcel wa vz wex vz cv cC wcel vz cv
      vy cv cop cA wcel wa vx vz cB rexcom4 vy cv cA cC cima wcel vz cv cC wcel
      vz cv vy cv cop cA wcel wa vz wex vx cB vz vy cv cA cC vy vex elima3
      rexbii vz cv vx cB cC ciun wcel vz cv vy cv cop cA wcel wa vz cv cC wcel
      vz cv vy cv cop cA wcel wa vx cB wrex vz vz cv vx cB cC ciun wcel vz cv
      vy cv cop cA wcel wa vz cv cC wcel vx cB wrex vz cv vy cv cop cA wcel wa
      vz cv cC wcel vz cv vy cv cop cA wcel wa vx cB wrex vz cv vx cB cC ciun
      wcel vz cv cC wcel vx cB wrex vz cv vy cv cop cA wcel vx vz cv cB cC
      eliun anbi1i vz cv cC wcel vz cv vy cv cop cA wcel vx cB r19.41v bitr4i
      exbii 3bitr4ri vz vy cv cA vx cB cC ciun vy vex elima3 vx vy cv cB cA cC
      cima eliun 3bitr4i eqriv $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( The image of a union is the indexed union of the images.  Theorem 3K(a)
       of [Enderton] p. 50.  (Contributed by NM, 9-Aug-2004.)  (Proof shortened
       by Mario Carneiro, 18-Jun-2014.) $)
    imauni $p |- ( A " U. B ) = U_ x e. B ( A " x ) $=
      cA cB cuni cima cA vx cB vx cv ciun cima vx cB cA vx cv cima ciun cB cuni
      vx cB vx cv ciun cA vx cB uniiun imaeq2i vx cA cB vx cv imaiun eqtri $.
  $}

  ${
    $d w x y z A $.  $d w x y z F $.
    $( The indexed union of a function's values is the union of its range.
       Compare Definition 5.4 of [Monk1] p. 50.  (Contributed by NM,
       27-Sep-2004.) $)
    fniunfv $p |- ( F Fn A -> U_ x e. A ( F ` x ) = U. ran F ) $=
      cF cA wfn cF crn cuni vy cv vx cv cF cfv wceq vx cA wrex vy cab cuni vx
      cA vx cv cF cfv ciun cF cA wfn cF crn vy cv vx cv cF cfv wceq vx cA wrex
      vy cab vx vy cA cF fnrnfv unieqd vx vy cA vx cv cF cfv vx cv cF fvex
      dfiun2 syl6reqr $.

    $( The indexed union of a function's values is the union of its image under
       the index class.

       Note:  This theorem depends on the fact that our function value is the
       empty set outside of its domain.  If the antecedent is changed to
       ` F Fn A ` , the theorem can be proved without this dependency.
       (Contributed by NM, 26-Mar-2006.)  (Proof shortened by Mario Carneiro,
       31-Aug-2015.) $)
    funiunfv $p |- ( Fun F -> U_ x e. A ( F ` x ) = U. ( F " A ) ) $=
      cF wfun vx cF cA cres cdm vx cv cF cA cres cfv ciun cF cA cres crn cuni
      vx cA vx cv cF cfv ciun cF cA cima cuni cF wfun cF cA cres cF cA cres cdm
      wfn vx cF cA cres cdm vx cv cF cA cres cfv ciun cF cA cres crn cuni wceq
      cF wfun cF cA cres wfun cF cA cres cF cA cres cdm wfn cA cF funres cF cA
      cres funfn sylib vx cF cA cres cdm cF cA cres fniunfv syl vx cF cA cres
      cdm cA cF cA cres cdm cdif cun vx cv cF cA cres cfv ciun vx cA vx cv cF
      cA cres cfv ciun vx cF cA cres cdm vx cv cF cA cres cfv ciun vx cA vx cv
      cF cfv ciun cF cA cres cdm cA cF cA cres cdm cdif cun cA wceq vx cF cA
      cres cdm cA cF cA cres cdm cdif cun vx cv cF cA cres cfv ciun vx cA vx cv
      cF cA cres cfv ciun wceq cF cA cres cdm cA cF cA cres cdm cdif cun cF cA
      cres cdm cA cun cA cF cA cres cdm cA undif2 cF cA cres cdm cA wss cF cA
      cres cdm cA cun cA wceq cF cA cres cdm cA cF cdm cin cA cF cA dmres cA cF
      cdm inss1 eqsstri cF cA cres cdm cA ssequn1 mpbi eqtri vx cF cA cres cdm
      cA cF cA cres cdm cdif cun cA vx cv cF cA cres cfv iuneq1 ax-mp vx cF cA
      cres cdm cA cF cA cres cdm cdif cun vx cv cF cA cres cfv ciun vx cF cA
      cres cdm vx cv cF cA cres cfv ciun vx cA cF cA cres cdm cdif vx cv cF cA
      cres cfv ciun cun vx cF cA cres cdm vx cv cF cA cres cfv ciun vx cF cA
      cres cdm cA cF cA cres cdm cdif vx cv cF cA cres cfv iunxun vx cF cA cres
      cdm vx cv cF cA cres cfv ciun vx cA cF cA cres cdm cdif vx cv cF cA cres
      cfv ciun cun vx cF cA cres cdm vx cv cF cA cres cfv ciun c0 cun vx cF cA
      cres cdm vx cv cF cA cres cfv ciun vx cA cF cA cres cdm cdif vx cv cF cA
      cres cfv ciun c0 vx cF cA cres cdm vx cv cF cA cres cfv ciun vx cA cF cA
      cres cdm cdif vx cv cF cA cres cfv ciun vx cA cF cA cres cdm cdif c0 ciun
      c0 vx cA cF cA cres cdm cdif vx cv cF cA cres cfv c0 vx cv cA cF cA cres
      cdm cdif wcel vx cv cF cA cres cdm wcel wn vx cv cF cA cres cfv c0 wceq
      vx cv cA cF cA cres cdm eldifn vx cv cF cA cres ndmfv syl iuneq2i vx cA
      cF cA cres cdm cdif iun0 eqtri uneq2i vx cF cA cres cdm vx cv cF cA cres
      cfv ciun un0 eqtri eqtri vx cA vx cv cF cA cres cfv vx cv cF cfv vx cv cA
      cF fvres iuneq2i 3eqtr3ri cF cA cima cF cA cres crn cF cA df-ima unieqi
      3eqtr4g $.
  $}

  ${
    $d x z A $.  $d y z F $.  $d x y $.
    funiunfvf.1 $e |- F/_ x F $.
    $( The indexed union of a function's values is the union of its image under
       the index class.  This version of ~ funiunfv uses a bound-variable
       hypothesis in place of a distinct variable condition.  (Contributed by
       NM, 26-Mar-2006.)  (Revised by David Abernethy, 15-Apr-2013.) $)
    funiunfvf $p |- ( Fun F -> U_ x e. A ( F ` x ) = U. ( F " A ) ) $=
      cF wfun vx cA vx cv cF cfv ciun vz cA vz cv cF cfv ciun cF cA cima cuni
      vz vx cA vz cv cF cfv vx cv cF cfv vx vz cv cF funiunfvf.1 vx vz cv nfcv
      nffv vz vx cv cF cfv nfcv vz cv vx cv cF fveq2 cbviun vz cA cF funiunfv
      syl5eqr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x F $.
    $( Membership in the union of an image of a function.  (Contributed by NM,
       28-Sep-2006.) $)
    eluniima $p |- ( Fun F ->
                   ( B e. U. ( F " A ) <-> E. x e. A B e. ( F ` x ) ) ) $=
      cB vx cv cF cfv wcel vx cA wrex cB vx cA vx cv cF cfv ciun wcel cF wfun
      cB cF cA cima cuni wcel vx cB cA vx cv cF cfv eliun cF wfun vx cA vx cv
      cF cfv ciun cF cA cima cuni cB vx cA cF funiunfv eleq2d syl5rbbr $.

    $( Membership in the union of the range of a function.  See ~ elunirnALT
       for alternate proof.  (Contributed by NM, 24-Sep-2006.) $)
    elunirn $p |- ( Fun F ->
                     ( A e. U. ran F <-> E. x e. dom F A e. ( F ` x ) ) ) $=
      cA cF crn cuni wcel cA cF cF cdm cima cuni wcel cF wfun cA vx cv cF cfv
      wcel vx cF cdm wrex cF cF cdm cima cuni cF crn cuni cA cF cF cdm cima cF
      crn cF imadmrn unieqi eleq2i vx cF cdm cA cF eluniima syl5bbr $.
  $}

  ${
    $d x A $.  $d x I $.  $d x F $.
    $( Membership in a union of some function-defined family of sets.
       (Contributed by Stefan O'Rear, 30-Jan-2015.) $)
    fnunirn $p |- ( F Fn I -> ( A e. U. ran F <->
        E. x e. I A e. ( F ` x ) ) ) $=
      cF cI wfn cA cF crn cuni wcel cA vx cv cF cfv wcel vx cF cdm wrex cA vx
      cv cF cfv wcel vx cI wrex cF cI wfn cF wfun cA cF crn cuni wcel cA vx cv
      cF cfv wcel vx cF cdm wrex wb cI cF fnfun vx cA cF elunirn syl cF cI wfn
      cA vx cv cF cfv wcel vx cF cdm cI cI cF fndm rexeqdv bitrd $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( Membership in the union of the range of a function, proved directly.
       Unlike ~ elunirn , it doesn't appeal to ~ ndmfv (via ~ funiunfv ).
       (Contributed by NM, 24-Sep-2006.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    elunirnALT $p |- ( Fun F -> ( A e. U. ran F <->
                E. x e. dom F A e. ( F ` x ) ) ) $=
      cA cF crn cuni wcel cA vy cv wcel vy cv cF crn wcel wa vy wex cF wfun cA
      vx cv cF cfv wcel vx cF cdm wrex vy cA cF crn eluni cF wfun cA vy cv wcel
      vy cv cF crn wcel wa vy wex cA vx cv cF cfv wcel vx cF cdm wrex cF wfun
      cA vy cv wcel vy cv cF crn wcel wa cA vx cv cF cfv wcel vx cF cdm wrex vy
      cF wfun cA vy cv wcel vy cv cF crn wcel wa cA vy cv wcel vx cv cF cfv vy
      cv wceq wa vx cF cdm wrex cA vx cv cF cfv wcel vx cF cdm wrex cF wfun cA
      vy cv wcel vy cv cF crn wcel wa cA vy cv wcel vx cv cF cfv vy cv wceq vx
      cF cdm wrex wa cA vy cv wcel vx cv cF cfv vy cv wceq wa vx cF cdm wrex cF
      wfun vy cv cF crn wcel vx cv cF cfv vy cv wceq vx cF cdm wrex cA vy cv
      wcel cF wfun cF cF cdm wfn vy cv cF crn wcel vx cv cF cfv vy cv wceq vx
      cF cdm wrex wb cF funfn vx cF cdm vy cv cF fvelrnb sylbi anbi2d cA vy cv
      wcel vx cv cF cfv vy cv wceq vx cF cdm r19.42v syl6bbr cA vy cv wcel vx
      cv cF cfv vy cv wceq wa cA vx cv cF cfv wcel vx cF cdm vx cv cF cfv vy cv
      wceq cA vx cv cF cfv wcel cA vy cv wcel vx cv cF cfv vy cv cA eleq2
      biimparc reximi syl6bi exlimdv cF wfun cA vx cv cF cfv wcel cA vy cv wcel
      vy cv cF crn wcel wa vy wex vx cF cdm cF wfun vx cv cF cdm wcel wa cA vx
      cv cF cfv wcel cA vx cv cF cfv wcel vx cv cF cfv cF crn wcel wa cA vy cv
      wcel vy cv cF crn wcel wa vy wex cF wfun vx cv cF cdm wcel wa cA vx cv cF
      cfv wcel vx cv cF cfv cF crn wcel cF wfun vx cv cF cdm wcel wa vx cv cF
      cfv cF crn wcel cA vx cv cF cfv wcel vx cv cF fvelrn a1d ancld cA vy cv
      wcel vy cv cF crn wcel wa cA vx cv cF cfv wcel vx cv cF cfv cF crn wcel
      wa vy vx cv cF cfv vx cv cF fvex vy cv vx cv cF cfv wceq cA vy cv wcel cA
      vx cv cF cfv wcel vy cv cF crn wcel vx cv cF cfv cF crn wcel vy cv vx cv
      cF cfv cA eleq2 vy cv vx cv cF cfv cF crn eleq1 anbi12d spcev syl6
      rexlimdva impbid syl5bb $.
  $}

  ${
    $d x y z A $.  $d z ph $.
    abrexex2.1 $e |- A e. _V $.
    abrexex2.2 $e |- { y | ph } e. _V $.
    $( Existence of an existentially restricted class abstraction. ` ph ` is
       normally has free-variable parameters ` x ` and ` y ` .  See also
       ~ abrexex .  (Contributed by NM, 12-Sep-2004.) $)
    abrexex2 $p |- { y | E. x e. A ph } e. _V $=
      wph vx cA wrex vy cab vz cv wph vy cab wcel vx cA wrex vz cab cvv wph vx
      cA wrex vy cab wph vy vz wsb vx cA wrex vz cab vz cv wph vy cab wcel vx
      cA wrex vz cab wph vx cA wrex wph vy vz wsb vx cA wrex vy vz wph vx cA
      wrex vz nfv wph vy vz wsb vy vx cA vy cA nfcv wph vy vz nfs1v nfrex vy cv
      vz cv wceq wph wph vy vz wsb vx cA wph vy vz sbequ12 rexbidv cbvab vz cv
      wph vy cab wcel vx cA wrex wph vy vz wsb vx cA wrex vz vz cv wph vy cab
      wcel wph vy vz wsb vx cA wph vz vy df-clab rexbii abbii eqtr4i vx cA wph
      vy cab ciun vz cv wph vy cab wcel vx cA wrex vz cab cvv vx vz cA wph vy
      cab df-iun vx cA wph vy cab abrexex2.1 abrexex2.2 iunex eqeltrri eqeltri
      $.

    $( Existence of a class abstraction with an existentially quantified
       expression.  Both ` x ` and ` y ` can be free in ` ph ` .  (Contributed
       by NM, 29-Jul-2006.) $)
    abexssex $p |- { y | E. x ( x C_ A /\ ph ) } e. _V $=
      wph vx cA cpw wrex vy cab vx cv cA wss wph wa vx wex vy cab cvv wph vx cA
      cpw wrex vx cv cA wss wph wa vx wex vy wph vx cA cpw wrex vx cv cA cpw
      wcel wph wa vx wex vx cv cA wss wph wa vx wex wph vx cA cpw df-rex vx cv
      cA cpw wcel wph wa vx cv cA wss wph wa vx vx cv cA cpw wcel vx cv cA wss
      wph vx cv cA abrexex2.1 elpw2 anbi1i exbii bitri abbii wph vx vy cA cpw
      cA abrexex2.1 pwex abrexex2.2 abrexex2 eqeltrri $.
  $}

  ${
    $d x y A $.
    abexex.1 $e |- A e. _V $.
    abexex.2 $e |- ( ph -> x e. A ) $.
    abexex.3 $e |- { y | ph } e. _V $.
    $( A condition where a class builder continues to exist after its wff is
       existentially quantified.  (Contributed by NM, 4-Mar-2007.) $)
    abexex $p |- { y | E. x ph } e. _V $=
      wph vx cA wrex vy cab wph vx wex vy cab cvv wph vx cA wrex wph vx wex vy
      wph vx cA wrex vx cv cA wcel wph wa vx wex wph vx wex wph vx cA df-rex
      wph vx cv cA wcel wph wa vx wph vx cv cA wcel abexex.2 pm4.71ri exbii
      bitr4i abbii wph vx vy cA abexex.1 abexex.3 abrexex2 eqeltrri $.
  $}

  ${
    $d x y z A $.  $d z B $.  $d x y z F $.
    $( A one-to-one function in terms of function values.  Compare Theorem
       4.8(iv) of [Monk1] p. 43.  (Contributed by NM, 29-Oct-1996.) $)
    dff13 $p |- ( F : A -1-1-> B <-> ( F : A --> B /\
             A. x e. A A. y e. A ( ( F ` x ) = ( F ` y ) -> x = y ) ) ) $=
      cA cB cF wf1 cA cB cF wf vx cv vz cv cF wbr vx wmo vz wal wa cA cB cF wf
      vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral
      wa vx vz cA cB cF dff12 cA cB cF wf vx cv vz cv cF wbr vx wmo vz wal vx
      cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA
      cB cF wf cF cA wfn vx cv vz cv cF wbr vx wmo vz wal vx cv cF cfv vy cv cF
      cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral wb cA cB cF ffn cF cA
      wfn vx cv vz cv cF wbr vy cv vz cv cF wbr wa vx cv vy cv wceq wi vz wal
      vy wal vx wal vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv
      wceq vx cv vy cv wceq wi wi vy wal vx wal vx cv vz cv cF wbr vx wmo vz
      wal vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA
      wral cF cA wfn vx cv vz cv cF wbr vy cv vz cv cF wbr wa vx cv vy cv wceq
      wi vz wal vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq
      vx cv vy cv wceq wi wi vx vy cF cA wfn vx cv vz cv cF wbr vy cv vz cv cF
      wbr wa vx cv vy cv wceq wi vz wal vx cv cA wcel vy cv cA wcel wa vz cv vx
      cv cF cfv wceq vz cv vy cv cF cfv wceq wa vx cv vy cv wceq wi wi vz wal
      vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv
      wceq wi wi cF cA wfn vx cv vz cv cF wbr vy cv vz cv cF wbr wa vx cv vy cv
      wceq wi vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz cv vy
      cv cF cfv wceq wa vx cv vy cv wceq wi wi vz cF cA wfn vx cv vz cv cF wbr
      vy cv vz cv cF wbr wa vx cv vy cv wceq wi vx cv cA wcel vy cv cA wcel wa
      vz cv vx cv cF cfv wceq vz cv vy cv cF cfv wceq wa wa vx cv vy cv wceq wi
      vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz cv vy cv cF cfv
      wceq wa vx cv vy cv wceq wi wi cF cA wfn vx cv vz cv cF wbr vy cv vz cv
      cF wbr wa vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz cv vy
      cv cF cfv wceq wa wa vx cv vy cv wceq cF cA wfn vx cv vz cv cF wbr vy cv
      vz cv cF wbr wa vx cv cA wcel vy cv cA wcel wa vx cv vz cv cF wbr vy cv
      vz cv cF wbr wa wa vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq
      vz cv vy cv cF cfv wceq wa wa cF cA wfn vx cv vz cv cF wbr vy cv vz cv cF
      wbr wa vx cv cA wcel vy cv cA wcel wa cF cA wfn vx cv vz cv cF wbr vx cv
      cA wcel vy cv vz cv cF wbr vy cv cA wcel vx cv vz cv cF wbr vx cv cF cdm
      wcel cF cA wfn vx cv cA wcel vx cv vz cv cF vx vex vz vex breldm cF cA
      wfn cF cdm cA vx cv cA cF fndm eleq2d syl5ib vy cv vz cv cF wbr vy cv cF
      cdm wcel cF cA wfn vy cv cA wcel vy cv vz cv cF vy vex vz vex breldm cF
      cA wfn cF cdm cA vy cv cA cF fndm eleq2d syl5ib anim12d pm4.71rd cF cA
      wfn vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz cv vy cv cF
      cfv wceq wa vx cv vz cv cF wbr vy cv vz cv cF wbr wa cF cA wfn vx cv cA
      wcel vy cv cA wcel vz cv vx cv cF cfv wceq vz cv vy cv cF cfv wceq wa vx
      cv vz cv cF wbr vy cv vz cv cF wbr wa wb cF cA wfn vx cv cA wcel wa vz cv
      vx cv cF cfv wceq vx cv vz cv cF wbr cF cA wfn vy cv cA wcel wa vz cv vy
      cv cF cfv wceq vy cv vz cv cF wbr vz cv vx cv cF cfv wceq vx cv cF cfv vz
      cv wceq cF cA wfn vx cv cA wcel wa vx cv vz cv cF wbr vz cv vx cv cF cfv
      eqcom cA vx cv vz cv cF fnbrfvb syl5bb vz cv vy cv cF cfv wceq vy cv cF
      cfv vz cv wceq cF cA wfn vy cv cA wcel wa vy cv vz cv cF wbr vz cv vy cv
      cF cfv eqcom cA vy cv vz cv cF fnbrfvb syl5bb bi2anan9 anandis pm5.32da
      bitr4d imbi1d vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz
      cv vy cv cF cfv wceq wa vx cv vy cv wceq impexp syl6bb albidv vx cv cA
      wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz cv vy cv cF cfv wceq wa
      vx cv vy cv wceq wi wi vz wal vx cv cA wcel vy cv cA wcel wa vz cv vx cv
      cF cfv wceq vz cv vy cv cF cfv wceq wa vx cv vy cv wceq wi vz wal wi vx
      cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv
      wceq wi wi vx cv cA wcel vy cv cA wcel wa vz cv vx cv cF cfv wceq vz cv
      vy cv cF cfv wceq wa vx cv vy cv wceq wi vz 19.21v vz cv vx cv cF cfv
      wceq vz cv vy cv cF cfv wceq wa vx cv vy cv wceq wi vz wal vx cv cF cfv
      vy cv cF cfv wceq vx cv vy cv wceq wi vx cv cA wcel vy cv cA wcel wa vz
      cv vx cv cF cfv wceq vz cv vy cv cF cfv wceq wa vx cv vy cv wceq wi vz
      wal vz cv vx cv cF cfv wceq vz cv vy cv cF cfv wceq wa vz wex vx cv vy cv
      wceq wi vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vz cv vx cv cF
      cfv wceq vz cv vy cv cF cfv wceq wa vx cv vy cv wceq vz 19.23v vx cv cF
      cfv vy cv cF cfv wceq vz cv vx cv cF cfv wceq vz cv vy cv cF cfv wceq wa
      vz wex vx cv vy cv wceq vz vx cv cF cfv vy cv cF cfv vx cv cF fvex eqvinc
      imbi1i bitr4i imbi2i bitri syl6bb 2albidv vx cv vz cv cF wbr vx wmo vz
      wal vx cv vz cv cF wbr vy cv vz cv cF wbr wa vx cv vy cv wceq wi vy wal
      vx wal vz wal vx cv vz cv cF wbr vy cv vz cv cF wbr wa vx cv vy cv wceq
      wi vz wal vy wal vx wal vx cv vz cv cF wbr vx wmo vx cv vz cv cF wbr vy
      cv vz cv cF wbr wa vx cv vy cv wceq wi vy wal vx wal vz vx cv vz cv cF
      wbr vy cv vz cv cF wbr vx vy vx cv vy cv vz cv cF breq1 mo4 albii vx cv
      vz cv cF wbr vy cv vz cv cF wbr wa vx cv vy cv wceq wi vz vx vy alrot3
      bitri vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vx vy cA cA r2al
      3bitr4g syl pm5.32i bitri $.
  $}

  ${
    $d x y w v A $.  $d w v B $.  $d z w v F $.  $d x y z $.
    dff13f.1 $e |- F/_ x F $.
    dff13f.2 $e |- F/_ y F $.
    $( A one-to-one function in terms of function values.  Compare Theorem
       4.8(iv) of [Monk1] p. 43.  (Contributed by NM, 31-Jul-2003.) $)
    dff13f $p |- ( F : A -1-1-> B <-> ( F : A --> B /\
             A. x e. A A. y e. A ( ( F ` x ) = ( F ` y ) -> x = y ) ) ) $=
      cA cB cF wf1 cA cB cF wf vw cv cF cfv vv cv cF cfv wceq vw cv vv cv wceq
      wi vv cA wral vw cA wral wa cA cB cF wf vx cv cF cfv vy cv cF cfv wceq vx
      cv vy cv wceq wi vy cA wral vx cA wral wa vw vv cA cB cF dff13 vw cv cF
      cfv vv cv cF cfv wceq vw cv vv cv wceq wi vv cA wral vw cA wral vx cv cF
      cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA cB cF
      wf vw cv cF cfv vv cv cF cfv wceq vw cv vv cv wceq wi vv cA wral vw cA
      wral vw cv cF cfv vy cv cF cfv wceq vw cv vy cv wceq wi vy cA wral vw cA
      wral vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA
      wral vw cv cF cfv vv cv cF cfv wceq vw cv vv cv wceq wi vv cA wral vw cv
      cF cfv vy cv cF cfv wceq vw cv vy cv wceq wi vy cA wral vw cA vw cv cF
      cfv vv cv cF cfv wceq vw cv vv cv wceq wi vw cv cF cfv vy cv cF cfv wceq
      vw cv vy cv wceq wi vv vy cA vw cv cF cfv vv cv cF cfv wceq vw cv vv cv
      wceq vy vy vw cv cF cfv vv cv cF cfv vy vw cv cF dff13f.2 vy vw cv nfcv
      nffv vy vv cv cF dff13f.2 vy vv cv nfcv nffv nfeq vw cv vv cv wceq vy nfv
      nfim vw cv cF cfv vy cv cF cfv wceq vw cv vy cv wceq wi vv nfv vv cv vy
      cv wceq vw cv cF cfv vv cv cF cfv wceq vw cv cF cfv vy cv cF cfv wceq vw
      cv vv cv wceq vw cv vy cv wceq vv cv vy cv wceq vv cv cF cfv vy cv cF cfv
      vw cv cF cfv vv cv vy cv cF fveq2 eqeq2d vv cv vy cv vw cv eqeq2 imbi12d
      cbvral ralbii vw cv cF cfv vy cv cF cfv wceq vw cv vy cv wceq wi vy cA
      wral vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vw vx
      cA vw cv cF cfv vy cv cF cfv wceq vw cv vy cv wceq wi vx vy cA vx cA nfcv
      vw cv cF cfv vy cv cF cfv wceq vw cv vy cv wceq vx vx vw cv cF cfv vy cv
      cF cfv vx vw cv cF dff13f.1 vx vw cv nfcv nffv vx vy cv cF dff13f.1 vx vy
      cv nfcv nffv nfeq vw cv vy cv wceq vx nfv nfim nfral vx cv cF cfv vy cv
      cF cfv wceq vx cv vy cv wceq wi vy cA wral vw nfv vw cv vx cv wceq vw cv
      cF cfv vy cv cF cfv wceq vw cv vy cv wceq wi vx cv cF cfv vy cv cF cfv
      wceq vx cv vy cv wceq wi vy cA vw cv vx cv wceq vw cv cF cfv vy cv cF cfv
      wceq vx cv cF cfv vy cv cF cfv wceq vw cv vy cv wceq vx cv vy cv wceq vw
      cv vx cv wceq vw cv cF cfv vx cv cF cfv vy cv cF cfv vw cv vx cv cF fveq2
      eqeq1d vw cv vx cv vy cv eqeq1 imbi12d ralbidv cbvral bitri anbi2i bitri
      $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x D $.  $d y F $.
    f1mpt.1 $e |- F = ( x e. A |-> C ) $.
    f1mpt.2 $e |- ( x = y -> C = D ) $.
    $( Express injection for a mapping operation.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    f1mpt $p |- ( F : A -1-1-> B <->
      ( A. x e. A C e. B /\ A. x e. A A. y e. A ( C = D -> x = y ) ) ) $=
      cA cB cF wf1 cA cB cF wf vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq
      wi vy cA wral vx cA wral wa cC cB wcel vx cA wral cC cD wceq vx cv vy cv
      wceq wi vy cA wral vx cA wral wa vx vy cA cB cF vx cF vx cA cC cmpt
      f1mpt.1 vx cA cC nfmpt1 nfcxfr vy cF nfcv dff13f cA cB cF wf vx cv cF cfv
      vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral wa cC cB wcel
      vx cA wral vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral
      vx cA wral wa cC cB wcel vx cA wral cC cD wceq vx cv vy cv wceq wi vy cA
      wral vx cA wral wa cC cB wcel vx cA wral cA cB cF wf vx cv cF cfv vy cv
      cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral vx cA cB cC cF
      f1mpt.1 fmpt anbi1i cC cB wcel vx cA wral vx cv cF cfv vy cv cF cfv wceq
      vx cv vy cv wceq wi vy cA wral vx cA wral cC cD wceq vx cv vy cv wceq wi
      vy cA wral vx cA wral cC cB wcel vx cA wral vx cv cF cfv vy cv cF cfv
      wceq vx cv vy cv wceq wi vy cA wral vx cA wral cC cD wceq vx cv vy cv
      wceq wi vy cA wral vx cA wral wb cC cB wcel vx cA wral cC cB wcel vx cA
      wral cD cB wcel vy cA wral vx cv cF cfv vy cv cF cfv wceq vx cv vy cv
      wceq wi vy cA wral vx cA wral cC cD wceq vx cv vy cv wceq wi vy cA wral
      vx cA wral wb cC cB wcel cD cB wcel vx vy cA vx cv vy cv wceq cC cD cB
      f1mpt.2 eleq1d cbvralv cC cB wcel vx cA wral cD cB wcel vy cA wral wa cC
      cB wcel cD cB wcel wa vy cA wral vx cA wral vx cv cF cfv vy cv cF cfv
      wceq vx cv vy cv wceq wi vy cA wral vx cA wral cC cD wceq vx cv vy cv
      wceq wi vy cA wral vx cA wral wb cC cB wcel cD cB wcel vx vy cA raaanv cC
      cB wcel cD cB wcel wa vy cA wral vx cA wral vx cv cF cfv vy cv cF cfv
      wceq vx cv vy cv wceq wi vy cA wral cC cD wceq vx cv vy cv wceq wi vy cA
      wral wb vx cA wral vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy
      cA wral vx cA wral cC cD wceq vx cv vy cv wceq wi vy cA wral vx cA wral
      wb cC cB wcel cD cB wcel wa vy cA wral vx cv cF cfv vy cv cF cfv wceq vx
      cv vy cv wceq wi vy cA wral cC cD wceq vx cv vy cv wceq wi vy cA wral wb
      vx cA vx cv cA wcel cC cB wcel cD cB wcel wa vy cA wral vx cv cF cfv vy
      cv cF cfv wceq vx cv vy cv wceq wi cC cD wceq vx cv vy cv wceq wi wb vy
      cA wral vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral cC
      cD wceq vx cv vy cv wceq wi vy cA wral wb vx cv cA wcel cC cB wcel cD cB
      wcel wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi cC cD wceq vx
      cv vy cv wceq wi wb vy cA vx cv cA wcel vy cv cA wcel wa cC cB wcel cD cB
      wcel wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi cC cD wceq vx
      cv vy cv wceq wi wb vx cv cA wcel vy cv cA wcel wa cC cB wcel cD cB wcel
      wa wa vx cv cF cfv vy cv cF cfv wceq cC cD wceq vx cv vy cv wceq vx cv cA
      wcel cC cB wcel vy cv cA wcel cD cB wcel vx cv cF cfv vy cv cF cfv wceq
      cC cD wceq wb vx cv cA wcel cC cB wcel wa vy cv cA wcel cD cB wcel wa vx
      cv cF cfv cC vy cv cF cfv cD vx cA cC cB cF f1mpt.1 fvmpt2 vx vy cv cC cD
      cA cB cF f1mpt.2 f1mpt.1 fvmptg eqeqan12d an4s imbi1d ex ralimdva vx cv
      cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi cC cD wceq vx cv vy cv wceq
      wi vy cA ralbi syl6 ralimia vx cv cF cfv vy cv cF cfv wceq vx cv vy cv
      wceq wi vy cA wral cC cD wceq vx cv vy cv wceq wi vy cA wral vx cA ralbi
      syl sylbir sylan2b anidms pm5.32i bitr3i bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y F $.
    $( Equality of function values for a one-to-one function.  (Contributed by
       NM, 11-Feb-1997.) $)
    f1fveq $p |- ( ( F : A -1-1-> B /\ ( C e. A /\ D e. A ) ) ->
                 ( ( F ` C ) = ( F ` D ) <-> C = D ) ) $=
      cA cB cF wf1 cC cA wcel cD cA wcel wa wa cC cF cfv cD cF cfv wceq cC cD
      wceq cC cA wcel cD cA wcel wa cA cB cF wf1 cC cF cfv cD cF cfv wceq cC cD
      wceq wi cA cB cF wf1 vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi
      wi cA cB cF wf1 cC cF cfv vy cv cF cfv wceq cC vy cv wceq wi wi cA cB cF
      wf1 cC cF cfv cD cF cfv wceq cC cD wceq wi wi vx vy cC cD cA cA vx cv cC
      wceq vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi cC cF cfv vy cv
      cF cfv wceq cC vy cv wceq wi cA cB cF wf1 vx cv cC wceq vx cv cF cfv vy
      cv cF cfv wceq cC cF cfv vy cv cF cfv wceq vx cv vy cv wceq cC vy cv wceq
      vx cv cC wceq vx cv cF cfv cC cF cfv vy cv cF cfv vx cv cC cF fveq2
      eqeq1d vx cv cC vy cv eqeq1 imbi12d imbi2d vy cv cD wceq cC cF cfv vy cv
      cF cfv wceq cC vy cv wceq wi cC cF cfv cD cF cfv wceq cC cD wceq wi cA cB
      cF wf1 vy cv cD wceq cC cF cfv vy cv cF cfv wceq cC cF cfv cD cF cfv wceq
      cC vy cv wceq cC cD wceq vy cv cD wceq vy cv cF cfv cD cF cfv cC cF cfv
      vy cv cD cF fveq2 eqeq2d vy cv cD cC eqeq2 imbi12d imbi2d cA cB cF wf1 vx
      cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv
      wceq wi cA cB cF wf1 vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi
      vy cA wral vx cA wral vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv
      cF cfv wceq vx cv vy cv wceq wi wi cA cB cF wf1 cA cB cF wf vx cv cF cfv
      vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral vx vy cA cB
      cF dff13 simprbi vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vx vy
      cA cA rsp2 syl com12 vtocl2ga impcom cC cD cF fveq2 impbid1 $.
  $}

  ${
    $d F z $.  $d A z $.  $d Y z $.  $d X z $.  $d B z $.
    $( Membership in the image of a 1-1 map.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    f1elima $p |- ( ( F : A -1-1-> B /\ X e. A /\ Y C_ A )
                                -> ( ( F ` X ) e. ( F " Y ) <-> X e. Y ) ) $=
      cA cB cF wf1 cX cA wcel cY cA wss w3a cX cF cfv cF cY cima wcel vz cv cF
      cfv cX cF cfv wceq vz cY wrex cX cY wcel cA cB cF wf1 cY cA wss cX cF cfv
      cF cY cima wcel vz cv cF cfv cX cF cfv wceq vz cY wrex wb cX cA wcel cA
      cB cF wf1 cF cA wfn cY cA wss cX cF cfv cF cY cima wcel vz cv cF cfv cX
      cF cfv wceq vz cY wrex wb cA cB cF f1fn vz cA cY cX cF cfv cF fvelimab
      sylan 3adant2 cA cB cF wf1 cX cA wcel cY cA wss w3a vz cv cF cfv cX cF
      cfv wceq vz cY wrex cX cY wcel cA cB cF wf1 cX cA wcel cY cA wss vz cv cF
      cfv cX cF cfv wceq vz cY wrex cX cY wcel wi cA cB cF wf1 cX cA wcel wa cY
      cA wss wa vz cv cF cfv cX cF cfv wceq cX cY wcel vz cY cA cB cF wf1 cX cA
      wcel wa cY cA wss vz cv cY wcel vz cv cF cfv cX cF cfv wceq cX cY wcel wi
      cY cA wss vz cv cY wcel wa cA cB cF wf1 cX cA wcel wa vz cv cA wcel vz cv
      cY wcel wa vz cv cF cfv cX cF cfv wceq cX cY wcel wi cY cA wss vz cv cY
      wcel vz cv cA wcel cY cA vz cv ssel impac cA cB cF wf1 cX cA wcel wa vz
      cv cA wcel vz cv cY wcel vz cv cF cfv cX cF cfv wceq cX cY wcel wi cA cB
      cF wf1 cX cA wcel wa vz cv cA wcel wa vz cv cF cfv cX cF cfv wceq vz cv
      cX wceq vz cv cY wcel cX cY wcel cA cB cF wf1 cX cA wcel vz cv cA wcel vz
      cv cF cfv cX cF cfv wceq vz cv cX wceq wi cA cB cF wf1 cX cA wcel vz cv
      cA wcel wa wa vz cv cF cfv cX cF cfv wceq vz cv cX wceq cA cB cF wf1 vz
      cv cA wcel cX cA wcel vz cv cF cfv cX cF cfv wceq vz cv cX wceq wb cA cB
      vz cv cX cF f1fveq ancom2s biimpd anassrs vz cv cX wceq vz cv cY wcel cX
      cY wcel vz cv cX cY eleq1 biimpcd sylan9 anasss sylan2 anassrs rexlimdva
      3impa cX cY wcel cX cF cfv cX cF cfv wceq vz cv cF cfv cX cF cfv wceq vz
      cY wrex cX cF cfv eqid vz cv cF cfv cX cF cfv wceq cX cF cfv cX cF cfv
      wceq vz cX cY vz cv cX wceq vz cv cF cfv cX cF cfv cX cF cfv vz cv cX cF
      fveq2 eqeq1d rspcev mpan2 impbid1 bitrd $.
  $}

  ${
    $d F a b $.  $d A a b $.  $d B a b $.  $d C a b $.  $d D a b $.
    $( Taking images under a one-to-one function preserves subsets.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
    f1imass $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C_ ( F " D ) <-> C C_ D ) ) $=
      cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss cC cD
      wss cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss cC
      cD wss cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss
      wa va cC cD cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima
      wss wa va cv cC wcel va cv cD wcel cA cB cF wf1 cC cA wss cD cA wss wa wa
      cF cC cima cF cD cima wss wa va cv cC wcel va cv cA wcel va cv cC wcel va
      cv cD wcel wi cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD
      cima wss wa cC cA va cv cA cB cF wf1 cC cA wss cD cA wss cF cC cima cF cD
      cima wss simplrl sseld cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima
      cF cD cima wss wa va cv cA wcel va cv cC wcel va cv cD wcel wi cA cB cF
      wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss wa va cv cA wcel
      wa va cv cF cfv cF cC cima wcel va cv cF cfv cF cD cima wcel va cv cC
      wcel va cv cD wcel cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF
      cD cima wss wa va cv cA wcel wa cF cC cima cF cD cima va cv cF cfv cA cB
      cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss va cv cA wcel
      simplr sseld cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima
      wss wa va cv cA wcel wa cA cB cF wf1 va cv cA wcel cC cA wss va cv cF cfv
      cF cC cima wcel va cv cC wcel wb cA cB cF wf1 cC cA wss cD cA wss wa cF
      cC cima cF cD cima wss va cv cA wcel simplll cA cB cF wf1 cC cA wss cD cA
      wss wa wa cF cC cima cF cD cima wss wa va cv cA wcel simpr cA cB cF wf1
      cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss va cv cA wcel cC cA
      wss cC cA wss cD cA wss cA cB cF wf1 cF cC cima cF cD cima wss va cv cA
      wcel simp1rl 3expa cA cB cF va cv cC f1elima syl3anc cA cB cF wf1 cC cA
      wss cD cA wss wa wa cF cC cima cF cD cima wss wa va cv cA wcel wa cA cB
      cF wf1 va cv cA wcel cD cA wss va cv cF cfv cF cD cima wcel va cv cD wcel
      wb cA cB cF wf1 cC cA wss cD cA wss wa cF cC cima cF cD cima wss va cv cA
      wcel simplll cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima
      wss wa va cv cA wcel simpr cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC
      cima cF cD cima wss va cv cA wcel cD cA wss cC cA wss cD cA wss cA cB cF
      wf1 cF cC cima cF cD cima wss va cv cA wcel simp1rr 3expa cA cB cF va cv
      cD f1elima syl3anc 3imtr3d ex syld pm2.43d ssrdv ex cC cD cF imass2
      impbid1 $.

    $( Taking images under a one-to-one function preserves equality.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
    f1imaeq $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) = ( F " D ) <-> C = D ) ) $=
      cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss cF cD
      cima cF cC cima wss wa cC cD wss cD cC wss wa cF cC cima cF cD cima wceq
      cC cD wceq cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima
      wss cC cD wss cF cD cima cF cC cima wss cD cC wss cA cB cC cD cF f1imass
      cA cB cF wf1 cD cA wss cC cA wss cF cD cima cF cC cima wss cD cC wss wb
      cA cB cD cC cF f1imass ancom2s anbi12d cF cC cima cF cD cima eqss cC cD
      eqss 3bitr4g $.

    $( Taking images under a one-to-one function preserves proper subsets.
       (Contributed by Stefan O'Rear, 30-Oct-2014.) $)
    f1imapss $p |- ( ( F : A -1-1-> B /\ ( C C_ A /\ D C_ A ) ) ->
      ( ( F " C ) C. ( F " D ) <-> C C. D ) ) $=
      cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD cima wss cF cC
      cima cF cD cima wceq wn wa cC cD wss cC cD wceq wn wa cF cC cima cF cD
      cima wpss cC cD wpss cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF
      cD cima wss cC cD wss cF cC cima cF cD cima wceq wn cC cD wceq wn cA cB
      cC cD cF f1imass cA cB cF wf1 cC cA wss cD cA wss wa wa cF cC cima cF cD
      cima wceq cC cD wceq cA cB cC cD cF f1imaeq notbid anbi12d cF cC cima cF
      cD cima dfpss2 cC cD dfpss2 3bitr4g $.
  $}

  ${
    $d x y A $.  $d x y F $.
    $( A one-to-one onto function in terms of function values.  (Contributed by
       NM, 29-Mar-2008.) $)
    dff1o6 $p |- ( F : A -1-1-onto-> B <-> ( F Fn A /\ ran F = B /\
             A. x e. A A. y e. A ( ( F ` x ) = ( F ` y ) -> x = y ) ) ) $=
      cA cB cF wf1o cA cB cF wf1 cA cB cF wfo wa cA cB cF wf vx cv cF cfv vy cv
      cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral wa cF cA wfn cF crn
      cB wceq wa wa cF cA wfn cF crn cB wceq vx cv cF cfv vy cv cF cfv wceq vx
      cv vy cv wceq wi vy cA wral vx cA wral w3a cA cB cF df-f1o cA cB cF wf1
      cA cB cF wf vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral
      vx cA wral wa cA cB cF wfo cF cA wfn cF crn cB wceq wa vx vy cA cB cF
      dff13 cA cB cF df-fo anbi12i cF cA wfn cF crn cB wceq vx cv cF cfv vy cv
      cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral w3a cF cA wfn cF
      crn cB wceq wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA
      wral vx cA wral wa cA cB cF wf cF cA wfn cF crn cB wceq wa wa vx cv cF
      cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral wa cA cB
      cF wf vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA
      wral wa cF cA wfn cF crn cB wceq wa wa cF cA wfn cF crn cB wceq vx cv cF
      cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral df-3an cF
      cA wfn cF crn cB wceq wa cA cB cF wf cF cA wfn cF crn cB wceq wa wa vx cv
      cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cF cA
      wfn cF crn cB wceq wa cA cB cF wf cF cA wfn cF crn cB wceq wa cF cA wfn
      cF crn cB wss wa cA cB cF wf cF crn cB wceq cF crn cB wss cF cA wfn cF
      crn cB eqimss anim2i cA cB cF df-f sylibr pm4.71ri anbi1i cA cB cF wf cF
      cA wfn cF crn cB wceq wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq
      wi vy cA wral vx cA wral an32 3bitrri 3bitri $.
  $}

  $( The converse value of the value of a one-to-one onto function.
     (Contributed by NM, 20-May-2004.) $)
  f1ocnvfv1 $p |- ( ( F : A -1-1-onto-> B /\ C e. A ) ->
                 ( `' F ` ( F ` C ) ) = C ) $=
    cA cB cF wf1o cC cA wcel wa cC cF ccnv cF ccom cfv cC cid cA cres cfv cC cF
    cfv cF ccnv cfv cC cA cB cF wf1o cC cF ccnv cF ccom cfv cC cid cA cres cfv
    wceq cC cA wcel cA cB cF wf1o cC cF ccnv cF ccom cid cA cres cA cB cF
    f1ococnv1 fveq1d adantr cA cB cF wf1o cA cB cF wf cC cA wcel cC cF ccnv cF
    ccom cfv cC cF cfv cF ccnv cfv wceq cA cB cF f1of cA cB cC cF ccnv cF fvco3
    sylan cC cA wcel cC cid cA cres cfv cC wceq cA cB cF wf1o cA cC fvresi
    adantl 3eqtr3d $.

  $( The value of the converse value of a one-to-one onto function.
     (Contributed by NM, 20-May-2004.) $)
  f1ocnvfv2 $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) ->
                 ( F ` ( `' F ` C ) ) = C ) $=
    cA cB cF wf1o cC cB wcel wa cC cF cF ccnv ccom cfv cC cid cB cres cfv cC cF
    ccnv cfv cF cfv cC cA cB cF wf1o cC cF cF ccnv ccom cfv cC cid cB cres cfv
    wceq cC cB wcel cA cB cF wf1o cC cF cF ccnv ccom cid cB cres cA cB cF
    f1ococnv2 fveq1d adantr cA cB cF wf1o cB cA cF ccnv wf cC cB wcel cC cF cF
    ccnv ccom cfv cC cF ccnv cfv cF cfv wceq cA cB cF wf1o cB cA cF ccnv wf1o
    cB cA cF ccnv wf cA cB cF f1ocnv cB cA cF ccnv f1of syl cB cA cC cF cF ccnv
    fvco3 sylan cC cB wcel cC cid cB cres cfv cC wceq cA cB cF wf1o cB cC
    fvresi adantl 3eqtr3d $.

  $( Relationship between the value of a one-to-one onto function and the value
     of its converse.  (Contributed by Raph Levien, 10-Apr-2004.) $)
  f1ocnvfv $p |- ( ( F : A -1-1-onto-> B /\ C e. A ) ->
                  ( ( F ` C ) = D -> ( `' F ` D ) = C ) ) $=
    cC cF cfv cD wceq cD cF ccnv cfv cC cF cfv cF ccnv cfv wceq cA cB cF wf1o
    cC cA wcel wa cD cF ccnv cfv cC wceq cD cF ccnv cfv cC cF cfv cF ccnv cfv
    wceq cD cC cF cfv cD cC cF cfv cF ccnv fveq2 eqcoms cA cB cF wf1o cC cA
    wcel wa cC cF cfv cF ccnv cfv cC cD cF ccnv cfv cA cB cC cF f1ocnvfv1
    eqeq2d syl5ib $.

  $( Relationship between the value of a one-to-one onto function and the value
     of its converse.  (Contributed by NM, 20-May-2004.) $)
  f1ocnvfvb $p |- ( ( F : A -1-1-onto-> B /\ C e. A /\ D e. B ) ->
                  ( ( F ` C ) = D <-> ( `' F ` D ) = C ) ) $=
    cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cF cfv cD wceq cD cF ccnv cfv cC
    wceq cA cB cF wf1o cC cA wcel cC cF cfv cD wceq cD cF ccnv cfv cC wceq wi
    cD cB wcel cA cB cC cD cF f1ocnvfv 3adant3 cA cB cF wf1o cD cB wcel cD cF
    ccnv cfv cC wceq cC cF cfv cD wceq wi cC cA wcel cD cF ccnv cfv cC wceq cC
    cF cfv cD cF ccnv cfv cF cfv wceq cA cB cF wf1o cD cB wcel wa cC cF cfv cD
    wceq cC cF cfv cD cF ccnv cfv cF cfv wceq cC cD cF ccnv cfv cC cD cF ccnv
    cfv cF fveq2 eqcoms cA cB cF wf1o cD cB wcel wa cD cF ccnv cfv cF cfv cD cC
    cF cfv cA cB cD cF f1ocnvfv2 eqeq2d syl5ib 3adant2 impbid $.

  $( The value of the converse of a one-to-one onto function belongs to its
     domain.  (Contributed by NM, 26-May-2006.) $)
  f1ocnvdm $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) ->
                    ( `' F ` C ) e. A ) $=
    cA cB cF wf1o cB cA cF ccnv wf cC cB wcel cC cF ccnv cfv cA wcel cA cB cF
    wf1o cB cA cF ccnv wf1o cB cA cF ccnv wf cA cB cF f1ocnv cB cA cF ccnv f1of
    syl cB cA cC cF ccnv ffvelrn sylan $.

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d R x y $.
    $( An application is injective if a retraction exists.  Proposition 8 of
       [BourbakiEns] p.  E.II.18.  (Contributed by FL, 11-Nov-2011.)  (Revised
       by Mario Carneiro, 27-Dec-2014.) $)
    fcof1 $p |- ( ( F : A --> B /\ ( R o. F ) = ( _I |` A ) )
         -> F : A -1-1-> B ) $=
      cA cB cF wf cR cF ccom cid cA cres wceq wa cA cB cF wf vx cv cF cfv vy cv
      cF cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA cB cF wf1 cA cB
      cF wf cR cF ccom cid cA cres wceq simpl cA cB cF wf cR cF ccom cid cA
      cres wceq wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq wi vx vy cA
      cA cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel
      wa vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq cA cB cF wf cR cF ccom
      cid cA cres wceq wa vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF
      cfv wceq wa wa vx cv cid cA cres cfv vy cv cid cA cres cfv vx cv vy cv cA
      cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel wa vx
      cv cF cfv vy cv cF cfv wceq wa wa vx cv cR cF ccom cfv vy cv cR cF ccom
      cfv vx cv cid cA cres cfv vy cv cid cA cres cfv cA cB cF wf cR cF ccom
      cid cA cres wceq wa vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF
      cfv wceq wa wa vx cv cF cfv cR cfv vy cv cF cfv cR cfv vx cv cR cF ccom
      cfv vy cv cR cF ccom cfv cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv
      cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa wa vx cv cF
      cfv vy cv cF cfv cR cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA
      wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq simprr fveq2d cA cB
      cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel wa vx cv
      cF cfv vy cv cF cfv wceq wa wa cA cB cF wf vx cv cA wcel vx cv cR cF ccom
      cfv vx cv cF cfv cR cfv wceq cA cB cF wf cR cF ccom cid cA cres wceq vx
      cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa simpll cA
      cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel vx cv
      cF cfv vy cv cF cfv wceq simprll cA cB vx cv cR cF fvco3 syl2anc cA cB cF
      wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel wa vx cv cF
      cfv vy cv cF cfv wceq wa wa cA cB cF wf vy cv cA wcel vy cv cR cF ccom
      cfv vy cv cF cfv cR cfv wceq cA cB cF wf cR cF ccom cid cA cres wceq vx
      cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa simpll cA
      cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel vx cv
      cF cfv vy cv cF cfv wceq simprlr cA cB vy cv cR cF fvco3 syl2anc 3eqtr4d
      cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv cA wcel wa
      vx cv cF cfv vy cv cF cfv wceq wa wa vx cv cR cF ccom cid cA cres cA cB
      cF wf cR cF ccom cid cA cres wceq vx cv cA wcel vy cv cA wcel wa vx cv cF
      cfv vy cv cF cfv wceq wa simplr fveq1d cA cB cF wf cR cF ccom cid cA cres
      wceq wa vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa
      wa vy cv cR cF ccom cid cA cres cA cB cF wf cR cF ccom cid cA cres wceq
      vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa simplr
      fveq1d 3eqtr3d cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel
      vy cv cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa wa vx cv cA wcel vx cv
      cid cA cres cfv vx cv wceq cA cB cF wf cR cF ccom cid cA cres wceq wa vx
      cv cA wcel vy cv cA wcel vx cv cF cfv vy cv cF cfv wceq simprll cA vx cv
      fvresi syl cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv cA wcel vy cv
      cA wcel wa vx cv cF cfv vy cv cF cfv wceq wa wa vy cv cA wcel vy cv cid
      cA cres cfv vy cv wceq cA cB cF wf cR cF ccom cid cA cres wceq wa vx cv
      cA wcel vy cv cA wcel vx cv cF cfv vy cv cF cfv wceq simprlr cA vy cv
      fvresi syl 3eqtr3d expr ralrimivva vx vy cA cB cF dff13 sylanbrc $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d S x y $.
    $( An application is surjective if a section exists.  Proposition 8 of
       [BourbakiEns] p.  E.II.18.  (Contributed by FL, 17-Nov-2011.)  (Proof
       shortened by Mario Carneiro, 27-Dec-2014.) $)
    fcofo $p |- ( ( F : A --> B /\ S : B --> A /\ ( F o. S ) = ( _I |` B ) )
         -> F : A -onto-> B ) $=
      cA cB cF wf cB cA cS wf cF cS ccom cid cB cres wceq w3a cA cB cF wf vy cv
      vx cv cF cfv wceq vx cA wrex vy cB wral cA cB cF wfo cA cB cF wf cB cA cS
      wf cF cS ccom cid cB cres wceq simp1 cA cB cF wf cB cA cS wf cF cS ccom
      cid cB cres wceq w3a vy cv vx cv cF cfv wceq vx cA wrex vy cB cA cB cF wf
      cB cA cS wf cF cS ccom cid cB cres wceq w3a vy cv cB wcel wa vy cv cS cfv
      cA wcel vy cv vy cv cS cfv cF cfv wceq vy cv vx cv cF cfv wceq vx cA wrex
      cB cA cS wf cA cB cF wf vy cv cB wcel vy cv cS cfv cA wcel cF cS ccom cid
      cB cres wceq cB cA vy cv cS ffvelrn 3ad2antl2 cA cB cF wf cB cA cS wf cF
      cS ccom cid cB cres wceq w3a vy cv cB wcel wa vy cv cF cS ccom cfv vy cv
      cid cB cres cfv vy cv cS cfv cF cfv vy cv cA cB cF wf cB cA cS wf cF cS
      ccom cid cB cres wceq w3a vy cv cB wcel wa vy cv cF cS ccom cid cB cres
      cA cB cF wf cB cA cS wf cF cS ccom cid cB cres wceq vy cv cB wcel simpl3
      fveq1d cB cA cS wf cA cB cF wf vy cv cB wcel vy cv cF cS ccom cfv vy cv
      cS cfv cF cfv wceq cF cS ccom cid cB cres wceq cB cA vy cv cF cS fvco3
      3ad2antl2 vy cv cB wcel vy cv cid cB cres cfv vy cv wceq cA cB cF wf cB
      cA cS wf cF cS ccom cid cB cres wceq w3a cB vy cv fvresi adantl 3eqtr3rd
      vy cv vx cv cF cfv wceq vy cv vy cv cS cfv cF cfv wceq vx vy cv cS cfv cA
      vx cv vy cv cS cfv wceq vx cv cF cfv vy cv cS cfv cF cfv vy cv vx cv vy
      cv cS cfv cF fveq2 eqeq2d rspcev syl2anc ralrimiva vx vy cA cB cF dffo3
      sylanbrc $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y F $.  $d y ph $.  $d x ps $.
    cbvfo.1 $e |- ( ( F ` x ) = y -> ( ph <-> ps ) ) $.
    $( Change bound variable between domain and range of function.
       (Contributed by NM, 23-Feb-1997.)  (Proof shortened by Mario Carneiro,
       21-Mar-2015.) $)
    cbvfo $p |- ( F : A -onto-> B -> ( A. x e. A ph <-> A. y e. B ps ) ) $=
      cA cB cF wfo wps vy cF crn wral wph vx cA wral wps vy cB wral cA cB cF
      wfo cF cA wfn wps vy cF crn wral wph vx cA wral wb cA cB cF fofn wps wph
      vy vx cA cF wps wph wb vx cv cF cfv vy cv vx cv cF cfv vy cv wceq wph wps
      cbvfo.1 bicomd eqcoms ralrn syl cA cB cF wfo wps vy cF crn cB cA cB cF
      forn raleqdv bitr3d $.

    $( Change bound variable between domain and range of function.
       (Contributed by NM, 23-Feb-1997.) $)
    cbvexfo $p |- ( F : A -onto-> B -> ( E. x e. A ph <-> E. y e. B ps ) ) $=
      cA cB cF wfo wph wn vx cA wral wn wps wn vy cB wral wn wph vx cA wrex wps
      vy cB wrex cA cB cF wfo wph wn vx cA wral wps wn vy cB wral wph wn wps wn
      vx vy cA cB cF vx cv cF cfv vy cv wceq wph wps cbvfo.1 notbid cbvfo
      notbid wph vx cA dfrex2 wps vy cB dfrex2 3bitr4g $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d F x $.  $d H x $.  $d K x $.
    $( An injection is left-cancelable.  (Contributed by FL, 2-Aug-2009.)
       (Revised by Mario Carneiro, 21-Mar-2015.) $)
    cocan1 $p |- ( ( F : B -1-1-> C /\ H : A --> B /\ K : A --> B ) ->
      ( ( F o. H ) = ( F o. K ) <-> H = K ) ) $=
      cB cC cF wf1 cA cB cH wf cA cB cK wf w3a vx cv cF cH ccom cfv vx cv cF cK
      ccom cfv wceq vx cA wral vx cv cH cfv vx cv cK cfv wceq vx cA wral cF cH
      ccom cF cK ccom wceq cH cK wceq cB cC cF wf1 cA cB cH wf cA cB cK wf w3a
      vx cv cF cH ccom cfv vx cv cF cK ccom cfv wceq vx cv cH cfv vx cv cK cfv
      wceq vx cA cB cC cF wf1 cA cB cH wf cA cB cK wf w3a vx cv cA wcel wa vx
      cv cF cH ccom cfv vx cv cF cK ccom cfv wceq vx cv cH cfv cF cfv vx cv cK
      cfv cF cfv wceq vx cv cH cfv vx cv cK cfv wceq cB cC cF wf1 cA cB cH wf
      cA cB cK wf w3a vx cv cA wcel wa vx cv cF cH ccom cfv vx cv cH cfv cF cfv
      vx cv cF cK ccom cfv vx cv cK cfv cF cfv cA cB cH wf cB cC cF wf1 vx cv
      cA wcel vx cv cF cH ccom cfv vx cv cH cfv cF cfv wceq cA cB cK wf cA cB
      vx cv cF cH fvco3 3ad2antl2 cA cB cK wf cB cC cF wf1 vx cv cA wcel vx cv
      cF cK ccom cfv vx cv cK cfv cF cfv wceq cA cB cH wf cA cB vx cv cF cK
      fvco3 3ad2antl3 eqeq12d cB cC cF wf1 cA cB cH wf cA cB cK wf w3a vx cv cA
      wcel wa cB cC cF wf1 vx cv cH cfv cB wcel vx cv cK cfv cB wcel vx cv cH
      cfv cF cfv vx cv cK cfv cF cfv wceq vx cv cH cfv vx cv cK cfv wceq wb cB
      cC cF wf1 cA cB cH wf cA cB cK wf vx cv cA wcel simpl1 cA cB cH wf cB cC
      cF wf1 vx cv cA wcel vx cv cH cfv cB wcel cA cB cK wf cA cB vx cv cH
      ffvelrn 3ad2antl2 cA cB cK wf cB cC cF wf1 vx cv cA wcel vx cv cK cfv cB
      wcel cA cB cH wf cA cB vx cv cK ffvelrn 3ad2antl3 cB cC vx cv cH cfv vx
      cv cK cfv cF f1fveq syl12anc bitrd ralbidva cB cC cF wf1 cA cB cH wf cA
      cB cK wf w3a cF cH ccom cA wfn cF cK ccom cA wfn cF cH ccom cF cK ccom
      wceq vx cv cF cH ccom cfv vx cv cF cK ccom cfv wceq vx cA wral wb cB cC
      cF wf1 cA cB cH wf cA cB cK wf w3a cF cB wfn cA cB cH wf cF cH ccom cA
      wfn cB cC cF wf1 cA cB cH wf cA cB cK wf w3a cB cC cF wf cF cB wfn cB cC
      cF wf1 cA cB cH wf cB cC cF wf cA cB cK wf cB cC cF f1f 3ad2ant1 cB cC cF
      ffn syl cB cC cF wf1 cA cB cH wf cA cB cK wf simp2 cB cA cF cH fnfco
      syl2anc cB cC cF wf1 cA cB cH wf cA cB cK wf w3a cF cB wfn cA cB cK wf cF
      cK ccom cA wfn cB cC cF wf1 cA cB cH wf cA cB cK wf w3a cB cC cF wf cF cB
      wfn cB cC cF wf1 cA cB cH wf cB cC cF wf cA cB cK wf cB cC cF f1f
      3ad2ant1 cB cC cF ffn syl cB cC cF wf1 cA cB cH wf cA cB cK wf simp3 cB
      cA cF cK fnfco syl2anc vx cA cF cH ccom cF cK ccom eqfnfv syl2anc cB cC
      cF wf1 cA cB cH wf cA cB cK wf w3a cH cA wfn cK cA wfn cH cK wceq vx cv
      cH cfv vx cv cK cfv wceq vx cA wral wb cB cC cF wf1 cA cB cH wf cA cB cK
      wf w3a cA cB cH wf cH cA wfn cB cC cF wf1 cA cB cH wf cA cB cK wf simp2
      cA cB cH ffn syl cB cC cF wf1 cA cB cH wf cA cB cK wf w3a cA cB cK wf cK
      cA wfn cB cC cF wf1 cA cB cH wf cA cB cK wf simp3 cA cB cK ffn syl vx cA
      cH cK eqfnfv syl2anc 3bitr4d $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y F $.  $d x y H $.  $d x y K $.
    $( A surjection is right-cancelable.  (Contributed by FL, 21-Nov-2011.)
       (Proof shortened by Mario Carneiro, 21-Mar-2015.) $)
    cocan2 $p |- ( ( F : A -onto-> B /\ H Fn B /\ K Fn B ) ->
      ( ( H o. F ) = ( K o. F ) <-> H = K ) ) $=
      cA cB cF wfo cH cB wfn cK cB wfn w3a vy cv cH cF ccom cfv vy cv cK cF
      ccom cfv wceq vy cA wral vx cv cH cfv vx cv cK cfv wceq vx cB wral cH cF
      ccom cK cF ccom wceq cH cK wceq cA cB cF wfo cH cB wfn cK cB wfn w3a vy
      cv cH cF ccom cfv vy cv cK cF ccom cfv wceq vy cA wral vy cv cF cfv cH
      cfv vy cv cF cfv cK cfv wceq vy cA wral vx cv cH cfv vx cv cK cfv wceq vx
      cB wral cA cB cF wfo cH cB wfn cK cB wfn w3a vy cv cH cF ccom cfv vy cv
      cK cF ccom cfv wceq vy cv cF cfv cH cfv vy cv cF cfv cK cfv wceq vy cA cA
      cB cF wfo cH cB wfn cK cB wfn w3a vy cv cA wcel wa vy cv cH cF ccom cfv
      vy cv cF cfv cH cfv vy cv cK cF ccom cfv vy cv cF cfv cK cfv cA cB cF wfo
      cH cB wfn cK cB wfn w3a cA cB cF wf vy cv cA wcel vy cv cH cF ccom cfv vy
      cv cF cfv cH cfv wceq cA cB cF wfo cH cB wfn cA cB cF wf cK cB wfn cA cB
      cF fof 3ad2ant1 cA cB vy cv cH cF fvco3 sylan cA cB cF wfo cH cB wfn cK
      cB wfn w3a cA cB cF wf vy cv cA wcel vy cv cK cF ccom cfv vy cv cF cfv cK
      cfv wceq cA cB cF wfo cH cB wfn cA cB cF wf cK cB wfn cA cB cF fof
      3ad2ant1 cA cB vy cv cK cF fvco3 sylan eqeq12d ralbidva cA cB cF wfo cH
      cB wfn vy cv cF cfv cH cfv vy cv cF cfv cK cfv wceq vy cA wral vx cv cH
      cfv vx cv cK cfv wceq vx cB wral wb cK cB wfn vy cv cF cfv cH cfv vy cv
      cF cfv cK cfv wceq vx cv cH cfv vx cv cK cfv wceq vy vx cA cB cF vy cv cF
      cfv vx cv wceq vy cv cF cfv cH cfv vx cv cH cfv vy cv cF cfv cK cfv vx cv
      cK cfv vy cv cF cfv vx cv cH fveq2 vy cv cF cfv vx cv cK fveq2 eqeq12d
      cbvfo 3ad2ant1 bitrd cA cB cF wfo cH cB wfn cK cB wfn w3a cH cF ccom cA
      wfn cK cF ccom cA wfn cH cF ccom cK cF ccom wceq vy cv cH cF ccom cfv vy
      cv cK cF ccom cfv wceq vy cA wral wb cA cB cF wfo cH cB wfn cK cB wfn w3a
      cH cB wfn cA cB cF wf cH cF ccom cA wfn cA cB cF wfo cH cB wfn cK cB wfn
      simp2 cA cB cF wfo cH cB wfn cA cB cF wf cK cB wfn cA cB cF fof 3ad2ant1
      cB cA cH cF fnfco syl2anc cA cB cF wfo cH cB wfn cK cB wfn w3a cK cB wfn
      cA cB cF wf cK cF ccom cA wfn cA cB cF wfo cH cB wfn cK cB wfn simp3 cA
      cB cF wfo cH cB wfn cA cB cF wf cK cB wfn cA cB cF fof 3ad2ant1 cB cA cK
      cF fnfco syl2anc vy cA cH cF ccom cK cF ccom eqfnfv syl2anc cA cB cF wfo
      cH cB wfn cK cB wfn w3a cH cB wfn cK cB wfn cH cK wceq vx cv cH cfv vx cv
      cK cfv wceq vx cB wral wb cA cB cF wfo cH cB wfn cK cB wfn simp2 cA cB cF
      wfo cH cB wfn cK cB wfn simp3 vx cB cH cK eqfnfv syl2anc 3bitr4d $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d S x y $.
    $( Show that two functions are inverse to each other by computing their
       compositions.  (Contributed by Mario Carneiro, 21-Mar-2015.) $)
    fcof1o $p |- ( ( ( F : A --> B /\ G : B --> A ) /\
      ( ( F o. G ) = ( _I |` B ) /\ ( G o. F ) = ( _I |` A ) ) ) ->
      ( F : A -1-1-onto-> B /\ `' F = G ) ) $=
      cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq cG cF ccom cid cA
      cres wceq wa wa cA cB cF wf1o cF ccnv cG wceq cA cB cF wf cB cA cG wf wa
      cF cG ccom cid cB cres wceq cG cF ccom cid cA cres wceq wa wa cA cB cF
      wf1 cA cB cF wfo cA cB cF wf1o cA cB cF wf cG cF ccom cid cA cres wceq cA
      cB cF wf1 cB cA cG wf cF cG ccom cid cB cres wceq cA cB cG cF fcof1
      ad2ant2rl cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq cA cB cF
      wfo cG cF ccom cid cA cres wceq cA cB cF wf cB cA cG wf cF cG ccom cid cB
      cres wceq cA cB cF wfo cA cB cG cF fcofo 3expa adantrr cA cB cF df-f1o
      sylanbrc cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq cG cF
      ccom cid cA cres wceq wa wa cF ccnv cF cG ccom ccom cF ccnv cid cB cres
      ccom cG cF ccnv cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq cG
      cF ccom cid cA cres wceq wa wa cF cG ccom cid cB cres cF ccnv cA cB cF wf
      cB cA cG wf wa cF cG ccom cid cB cres wceq cG cF ccom cid cA cres wceq
      simprl coeq2d cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq cG
      cF ccom cid cA cres wceq wa wa cF ccnv cF cG ccom ccom cF ccnv cF ccom cG
      ccom cG cF ccnv cF cG coass cA cB cF wf cB cA cG wf wa cF cG ccom cid cB
      cres wceq cG cF ccom cid cA cres wceq wa wa cF ccnv cF ccom cG ccom cid
      cA cres cG ccom cG cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq
      cG cF ccom cid cA cres wceq wa wa cF ccnv cF ccom cid cA cres cG cA cB cF
      wf cB cA cG wf wa cF cG ccom cid cB cres wceq cG cF ccom cid cA cres wceq
      wa wa cA cB cF wf1o cF ccnv cF ccom cid cA cres wceq cA cB cF wf cB cA cG
      wf wa cF cG ccom cid cB cres wceq cG cF ccom cid cA cres wceq wa wa cA cB
      cF wf1 cA cB cF wfo cA cB cF wf1o cA cB cF wf cG cF ccom cid cA cres wceq
      cA cB cF wf1 cB cA cG wf cF cG ccom cid cB cres wceq cA cB cG cF fcof1
      ad2ant2rl cA cB cF wf cB cA cG wf wa cF cG ccom cid cB cres wceq cA cB cF
      wfo cG cF ccom cid cA cres wceq cA cB cF wf cB cA cG wf cF cG ccom cid cB
      cres wceq cA cB cF wfo cA cB cG cF fcofo 3expa adantrr cA cB cF df-f1o
      sylanbrc cA cB cF f1ococnv1 syl coeq1d cB cA cG wf cid cA cres cG ccom cG
      wceq cA cB cF wf cF cG ccom cid cB cres wceq cG cF ccom cid cA cres wceq
      wa cB cA cG fcoi2 ad2antlr eqtrd syl5eqr cA cB cF wf cB cA cG wf wa cF cG
      ccom cid cB cres wceq cG cF ccom cid cA cres wceq wa wa cB cA cF ccnv wf
      cF ccnv cid cB cres ccom cF ccnv wceq cA cB cF wf cB cA cG wf wa cF cG
      ccom cid cB cres wceq cG cF ccom cid cA cres wceq wa wa cA cB cF wf1o cB
      cA cF ccnv wf1o cB cA cF ccnv wf cA cB cF wf cB cA cG wf wa cF cG ccom
      cid cB cres wceq cG cF ccom cid cA cres wceq wa wa cA cB cF wf1 cA cB cF
      wfo cA cB cF wf1o cA cB cF wf cG cF ccom cid cA cres wceq cA cB cF wf1 cB
      cA cG wf cF cG ccom cid cB cres wceq cA cB cG cF fcof1 ad2ant2rl cA cB cF
      wf cB cA cG wf wa cF cG ccom cid cB cres wceq cA cB cF wfo cG cF ccom cid
      cA cres wceq cA cB cF wf cB cA cG wf cF cG ccom cid cB cres wceq cA cB cF
      wfo cA cB cG cF fcofo 3expa adantrr cA cB cF df-f1o sylanbrc cA cB cF
      f1ocnv cB cA cF ccnv f1of 3syl cB cA cF ccnv fcoi1 syl 3eqtr3rd jca $.
  $}

  ${
    $d F x y $.  $d G x y $.  $d A x y $.  $d B x y $.
    $( Condition for function equality in terms of vanishing of the composition
       with the converse. _EDITORIAL_:  Is there a relation-algebraic proof of
       this?  (Contributed by Stefan O'Rear, 12-Feb-2015.) $)
    foeqcnvco $p |- ( ( F : A -onto-> B /\ G : A -onto-> B ) ->
        ( F = G <-> ( F o. `' G ) = ( _I |` B ) ) ) $=
      cA cB cF wfo cA cB cG wfo wa cF cG wceq cF cG ccnv ccom cid cB cres wceq
      cA cB cF wfo cF cG wceq cF cG ccnv ccom cid cB cres wceq wi cA cB cG wfo
      cA cB cF wfo cF cF ccnv ccom cid cB cres wceq cF cG wceq cF cG ccnv ccom
      cid cB cres wceq cA cB cF fococnv2 cF cG wceq cF cF ccnv ccom cF cG ccnv
      ccom cid cB cres cF cG wceq cF ccnv cG ccnv cF cF cG cnveq coeq2d eqeq1d
      syl5ibcom adantr cA cB cF wfo cA cB cG wfo wa cF cG ccnv ccom cid cB cres
      wceq cF cG wceq cA cB cF wfo cA cB cG wfo wa cF cG ccnv ccom cid cB cres
      wceq wa vx cA cF cG cA cB cF wfo cF cA wfn cA cB cG wfo cF cG ccnv ccom
      cid cB cres wceq cA cB cF fofn ad2antrr cA cB cG wfo cG cA wfn cA cB cF
      wfo cF cG ccnv ccom cid cB cres wceq cA cB cG fofn ad2antlr cA cB cF wfo
      cA cB cG wfo wa cF cG ccnv ccom cid cB cres wceq wa vx cv cA wcel wa vx
      cv cG cfv vx cv cF cfv cA cB cF wfo cA cB cG wfo wa cF cG ccnv ccom cid
      cB cres wceq wa vx cv cA wcel wa vx cv cG cfv vx cv cF cfv cid cB cres
      wbr vx cv cG cfv vx cv cF cfv wceq cA cB cF wfo cA cB cG wfo wa cF cG
      ccnv ccom cid cB cres wceq wa vx cv cA wcel wa vx cv cG cfv vx cv cF cfv
      cF cG ccnv ccom wbr vx cv cG cfv vx cv cF cfv cid cB cres wbr cA cB cF
      wfo cA cB cG wfo wa vx cv cA wcel vx cv cG cfv vx cv cF cfv cF cG ccnv
      ccom wbr cF cG ccnv ccom cid cB cres wceq cA cB cF wfo cA cB cG wfo wa vx
      cv cA wcel wa vx cv cG cfv vy cv cG ccnv wbr vy cv vx cv cF cfv cF wbr wa
      vy wex vx cv cG cfv vx cv cF cfv cF cG ccnv ccom wbr cA cB cF wfo cA cB
      cG wfo wa vx cv cA wcel wa vx cv cG cfv vx cv cG ccnv wbr vx cv vx cv cF
      cfv cF wbr vx cv cG cfv vy cv cG ccnv wbr vy cv vx cv cF cfv cF wbr wa vy
      wex cA cB cF wfo cA cB cG wfo wa vx cv cA wcel wa vx cv vx cv cG cfv cop
      cG wcel vx cv cG cfv vx cv cG ccnv wbr cA cB cF wfo cA cB cG wfo wa cG cA
      wfn vx cv cA wcel vx cv vx cv cG cfv cop cG wcel cA cB cG wfo cG cA wfn
      cA cB cF wfo cA cB cG fofn adantl cA vx cv cG fnopfv sylan vx cv cG cfv
      vx cv cG ccnv wbr vx cv vx cv cG cfv cG wbr vx cv vx cv cG cfv cop cG
      wcel vx cv cG cfv vx cv cG vx cv cG fvex vx vex brcnv vx cv vx cv cG cfv
      cG df-br bitri sylibr cA cB cF wfo cA cB cG wfo wa vx cv cA wcel wa vx cv
      vx cv cF cfv cop cF wcel vx cv vx cv cF cfv cF wbr cA cB cF wfo cA cB cG
      wfo wa cF cA wfn vx cv cA wcel vx cv vx cv cF cfv cop cF wcel cA cB cF
      wfo cF cA wfn cA cB cG wfo cA cB cF fofn adantr cA vx cv cF fnopfv sylan
      vx cv vx cv cF cfv cF df-br sylibr vx cv cG cfv vy cv cG ccnv wbr vy cv
      vx cv cF cfv cF wbr wa vx cv cG cfv vx cv cG ccnv wbr vx cv vx cv cF cfv
      cF wbr wa vy vx cv vx vex vy vx weq vx cv cG cfv vy cv cG ccnv wbr vx cv
      cG cfv vx cv cG ccnv wbr vy cv vx cv cF cfv cF wbr vx cv vx cv cF cfv cF
      wbr vy cv vx cv vx cv cG cfv cG ccnv breq2 vy cv vx cv vx cv cF cfv cF
      breq1 anbi12d spcev syl2anc vy vx cv cG cfv vx cv cF cfv cF cG ccnv vx cv
      cG fvex vx cv cF fvex brco sylibr adantlr cF cG ccnv ccom cid cB cres
      wceq vx cv cG cfv vx cv cF cfv cF cG ccnv ccom wbr vx cv cG cfv vx cv cF
      cfv cid cB cres wbr wb cA cB cF wfo cA cB cG wfo wa vx cv cA wcel vx cv
      cG cfv vx cv cF cfv cF cG ccnv ccom cid cB cres breq ad2antlr mpbid cA cB
      cF wfo cA cB cG wfo wa vx cv cA wcel vx cv cG cfv vx cv cF cfv cid cB
      cres wbr vx cv cG cfv vx cv cF cfv wceq wb cF cG ccnv ccom cid cB cres
      wceq cA cB cF wfo cA cB cG wfo wa vx cv cA wcel wa vx cv cG cfv cB wcel
      vx cv cF cfv cB wcel vx cv cG cfv vx cv cF cfv cid cB cres wbr vx cv cG
      cfv vx cv cF cfv wceq wb cA cB cF wfo cA cB cG wfo wa cA cB cG wf vx cv
      cA wcel vx cv cG cfv cB wcel cA cB cG wfo cA cB cG wf cA cB cF wfo cA cB
      cG fof adantl cA cB vx cv cG ffvelrn sylan cA cB cF wfo cA cB cG wfo wa
      cA cB cF wf vx cv cA wcel vx cv cF cfv cB wcel cA cB cF wfo cA cB cF wf
      cA cB cG wfo cA cB cF fof adantr cA cB vx cv cF ffvelrn sylan cB vx cv cG
      cfv vx cv cF cfv resieq syl2anc adantlr mpbid eqcomd eqfnfvd ex impbid $.

    $( Condition for function equality in terms of vanishing of the composition
       with the inverse.  (Contributed by Stefan O'Rear, 12-Feb-2015.) $)
    f1eqcocnv $p |- ( ( F : A -1-1-> B /\ G : A -1-1-> B ) ->
        ( F = G <-> ( `' F o. G ) = ( _I |` A ) ) ) $=
      cA cB cF wf1 cA cB cG wf1 wa cF cG wceq cF ccnv cG ccom cid cA cres wceq
      cA cB cF wf1 cF cG wceq cF ccnv cG ccom cid cA cres wceq wi cA cB cG wf1
      cA cB cF wf1 cF ccnv cF ccom cid cA cres wceq cF cG wceq cF ccnv cG ccom
      cid cA cres wceq cA cB cF f1cocnv1 cF cG wceq cF ccnv cF ccom cF ccnv cG
      ccom cid cA cres cF cG cF ccnv coeq2 eqeq1d syl5ibcom adantr cA cB cF wf1
      cA cB cG wf1 wa cF ccnv cG ccom cid cA cres wceq cF cG wceq cA cB cF wf1
      cA cB cG wf1 wa cF ccnv cG ccom cid cA cres wceq wa cG cF cA cB cF wf1 cA
      cB cG wf1 wa cF ccnv cG ccom cid cA cres wceq wa vx cA cG cF cA cB cF wf1
      cA cB cG wf1 wa cG cA wfn cF ccnv cG ccom cid cA cres wceq cA cB cG wf1
      cG cA wfn cA cB cF wf1 cA cB cG f1fn adantl adantr cA cB cF wf1 cA cB cG
      wf1 wa cF cA wfn cF ccnv cG ccom cid cA cres wceq cA cB cF wf1 cF cA wfn
      cA cB cG wf1 cA cB cF f1fn adantr adantr cA cB cF wf1 cA cB cG wf1 wa cF
      ccnv cG ccom cid cA cres wceq wa vx cv cA wcel wa vx cv vx cv cF ccnv cG
      ccom wbr vx cv cG cfv vx cv cF cfv wceq cA cB cF wf1 cA cB cG wf1 wa cF
      ccnv cG ccom cid cA cres wceq wa vx cv cA wcel wa vx cv vx cv cF ccnv cG
      ccom wbr vx cv vx cv cid cA cres wbr vx cv cA wcel vx cv vx cv cid cA
      cres wbr cA cB cF wf1 cA cB cG wf1 wa cF ccnv cG ccom cid cA cres wceq wa
      vx cv cA wcel vx cv vx cv cid cA cres wbr vx cv cA wcel vx cv cA wcel wa
      vx cv vx cv cid cA cres wbr vx cv vx cv wceq vx cv eqid cA vx cv vx cv
      resieq mpbiri anidms adantl cF ccnv cG ccom cid cA cres wceq vx cv vx cv
      cF ccnv cG ccom wbr vx cv vx cv cid cA cres wbr wb cA cB cF wf1 cA cB cG
      wf1 wa vx cv cA wcel vx cv vx cv cF ccnv cG ccom cid cA cres breq
      ad2antlr mpbird cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel vx cv vx cv cF
      ccnv cG ccom wbr vx cv cG cfv vx cv cF cfv wceq wi cF ccnv cG ccom cid cA
      cres wceq cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vx cv vy cv cG
      wbr vy cv vx cv cF ccnv wbr wa vy wex vy cv vx cv cG cfv wceq vy cv vx cv
      cF cfv wceq wa vy wex vx cv vx cv cF ccnv cG ccom wbr vx cv cG cfv vx cv
      cF cfv wceq cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vx cv vy cv cG
      wbr vy cv vx cv cF ccnv wbr wa vy cv vx cv cG cfv wceq vy cv vx cv cF cfv
      wceq wa vy cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vx cv vy cv cG
      wbr vy cv vx cv cG cfv wceq vy cv vx cv cF ccnv wbr vy cv vx cv cF cfv
      wceq cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vx cv vy cv cG wbr vy
      cv vx cv cG cfv wceq cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vx cv
      vy cv cop cG wcel vx cv cG cfv vy cv wceq vx cv vy cv cG wbr vy cv vx cv
      cG cfv wceq cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vx cv cG cfv vy
      cv wceq vx cv vy cv cop cG wcel cA cB cF wf1 cA cB cG wf1 wa vx cv cA
      wcel wa cG wfun vx cv cG cdm wcel vx cv cG cfv vy cv wceq vx cv vy cv cop
      cG wcel wb cA cB cF wf1 cA cB cG wf1 wa cG wfun vx cv cA wcel cA cB cF
      wf1 cA cB cG wf1 wa cG cA wfn cG wfun cA cB cG wf1 cG cA wfn cA cB cF wf1
      cA cB cG f1fn adantl cA cG fnfun syl adantr cA cB cF wf1 cA cB cG wf1 wa
      vx cv cG cdm wcel vx cv cA wcel cA cB cF wf1 cA cB cG wf1 wa cG cdm cA vx
      cv cA cB cF wf1 cA cB cG wf1 wa cG cA wfn cG cdm cA wceq cA cB cG wf1 cG
      cA wfn cA cB cF wf1 cA cB cG f1fn adantl cA cG fndm syl eleq2d biimpar vx
      cv vy cv cG funopfvb syl2anc bicomd vx cv vy cv cG df-br vy cv vx cv cG
      cfv eqcom 3bitr4g biimpd cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa vy
      cv vx cv cF ccnv wbr vy cv vx cv cF cfv wceq cA cB cF wf1 cA cB cG wf1 wa
      vx cv cA wcel wa vx cv vy cv cF wbr vx cv cF cfv vy cv wceq vy cv vx cv
      cF ccnv wbr vy cv vx cv cF cfv wceq cA cB cF wf1 cA cB cG wf1 wa vx cv cA
      wcel wa vx cv cF cfv vy cv wceq vx cv vy cv cop cF wcel vx cv vy cv cF
      wbr cA cB cF wf1 cA cB cG wf1 wa vx cv cA wcel wa cF wfun vx cv cF cdm
      wcel vx cv cF cfv vy cv wceq vx cv vy cv cop cF wcel wb cA cB cF wf1 cA
      cB cG wf1 wa cF wfun vx cv cA wcel cA cB cF wf1 cA cB cG wf1 wa cF cA wfn
      cF wfun cA cB cF wf1 cF cA wfn cA cB cG wf1 cA cB cF f1fn adantr cA cF
      fnfun syl adantr cA cB cF wf1 cA cB cG wf1 wa vx cv cF cdm wcel vx cv cA
      wcel cA cB cF wf1 cA cB cG wf1 wa cF cdm cA vx cv cA cB cF wf1 cA cB cG
      wf1 wa cF cA wfn cF cdm cA wceq cA cB cF wf1 cF cA wfn cA cB cG wf1 cA cB
      cF f1fn adantr cA cF fndm syl eleq2d biimpar vx cv vy cv cF funopfvb
      syl2anc vx cv vy cv cF df-br syl6rbbr vy cv vx cv cF vy vex vx vex brcnv
      vy cv vx cv cF cfv eqcom 3bitr4g biimpd anim12d eximdv vy vx cv vx cv cF
      ccnv cG vx vex vx vex brco vy vx cv cG cfv vx cv cF cfv vx cv cG fvex
      eqvinc 3imtr4g adantlr mpd eqfnfvd eqcomd ex impbid $.
  $}

  ${
    fveqf1o.1 $e |- G = ( F o. ( ( _I |` ( A \ { C , ( `' F ` D ) } ) ) u.
      { <. C , ( `' F ` D ) >. , <. ( `' F ` D ) , C >. } ) ) $.
    $( Given a bijection ` F ` , produce another bijection ` G ` which
       additionally maps two specified points.  (Contributed by Mario Carneiro,
       30-May-2015.) $)
    fveqf1o $p |- ( ( F : A -1-1-onto-> B /\ C e. A /\ D e. B ) ->
      ( G : A -1-1-onto-> B /\ ( G ` C ) = D ) ) $=
      cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cG wf1o cC cG cfv cD wceq
      cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cF cid cA cC cD cF ccnv cfv
      cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun ccom
      wf1o cA cB cG wf1o cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cF wf1o
      cA cA cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF
      ccnv cfv cC cop cpr cun wf1o cA cB cF cid cA cC cD cF ccnv cfv cpr cdif
      cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun ccom wf1o cA cB
      cF wf1o cC cA wcel cD cB wcel simp1 cA cB cF wf1o cC cA wcel cD cB wcel
      w3a cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC
      cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop
      cpr cun wf1o cA cA cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv
      cfv cop cD cF ccnv cfv cC cop cpr cun wf1o cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA cC cD
      cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC cD cF ccnv cfv
      cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf1o cA
      cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC cD cF
      ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr
      cun wf1o cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr
      cdif cA cC cD cF ccnv cfv cpr cdif cid cA cC cD cF ccnv cfv cpr cdif cres
      wf1o cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cop cD
      cF ccnv cfv cC cop cpr wf1o cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv
      cfv cpr cin c0 wceq cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr
      cin c0 wceq cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA cC
      cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC cD cF ccnv
      cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun
      wf1o cA cC cD cF ccnv cfv cpr cdif cA cC cD cF ccnv cfv cpr cdif cid cA
      cC cD cF ccnv cfv cpr cdif cres wf1o cA cB cF wf1o cC cA wcel cD cB wcel
      w3a cA cC cD cF ccnv cfv cpr cdif f1oi a1i cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cC cA wcel cD cF ccnv cfv cA wcel cC cD cF ccnv cfv cpr cC cD cF
      ccnv cfv cpr cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr wf1o cA cB
      cF wf1o cC cA wcel cD cB wcel simp2 cA cB cF wf1o cC cA wcel cD cB wcel
      w3a cB cA cF ccnv wf cD cB wcel cD cF ccnv cfv cA wcel cA cB cF wf1o cC
      cA wcel cD cB wcel w3a cA cB cF wf1o cB cA cF ccnv wf1o cB cA cF ccnv wf
      cA cB cF wf1o cC cA wcel cD cB wcel simp1 cA cB cF f1ocnv cB cA cF ccnv
      f1of 3syl cA cB cF wf1o cC cA wcel cD cB wcel simp3 cB cA cD cF ccnv
      ffvelrn syl2anc cC cD cF ccnv cfv cA cA f1oprswap syl2anc cA cC cD cF
      ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cin c0 wceq cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr
      cin cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv cpr cdif cin c0 cA cC cD
      cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr incom cC cD cF ccnv cfv cpr cA
      disjdif eqtri a1i cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cin
      c0 wceq cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr
      cdif cC cD cF ccnv cfv cpr cin cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv
      cpr cdif cin c0 cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr incom
      cC cD cF ccnv cfv cpr cA disjdif eqtri a1i cA cC cD cF ccnv cfv cpr cdif
      cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr
      cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr f1oun syl22anc cA cB cF wf1o cC cA wcel cD cB wcel w3a cA
      cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA wceq cA cC cD cF
      ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA cC cD cF ccnv cfv cpr cdif
      cC cD cF ccnv cfv cpr cun cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF
      ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf1o cA cA cC cD cF ccnv cfv
      cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC cD cF ccnv cfv cpr cdif cres
      cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf1o wb cA cB cF wf1o
      cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cun cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv cpr cdif cun cA cA cC
      cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr uncom cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cC cD cF ccnv cfv cpr cA wss cC cD cF ccnv cfv cpr cA
      cC cD cF ccnv cfv cpr cdif cun cA wceq cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cC cA wcel cD cF ccnv cfv cA wcel cC cD cF ccnv cfv cpr cA wss
      cA cB cF wf1o cC cA wcel cD cB wcel simp2 cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cB cA cF ccnv wf cD cB wcel cD cF ccnv cfv cA wcel cA cB cF wf1o
      cC cA wcel cD cB wcel w3a cA cB cF wf1o cB cA cF ccnv wf1o cB cA cF ccnv
      wf cA cB cF wf1o cC cA wcel cD cB wcel simp1 cA cB cF f1ocnv cB cA cF
      ccnv f1of 3syl cA cB cF wf1o cC cA wcel cD cB wcel simp3 cB cA cD cF ccnv
      ffvelrn syl2anc cC cD cF ccnv cfv cA prssi syl2anc cC cD cF ccnv cfv cpr
      cA undif sylib syl5eq cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr
      cun cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC
      cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop
      cpr cun f1oeq2 syl mpbid cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC cD
      cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA wceq cA cA cC cD cF
      ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC cD cF ccnv cfv cpr
      cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf1o cA cA
      cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr cun wf1o wb cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC
      cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cC cD cF ccnv cfv cpr
      cA cC cD cF ccnv cfv cpr cdif cun cA cA cC cD cF ccnv cfv cpr cdif cC cD
      cF ccnv cfv cpr uncom cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cD cF
      ccnv cfv cpr cA wss cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv cpr cdif
      cun cA wceq cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cA wcel cD cF ccnv
      cfv cA wcel cC cD cF ccnv cfv cpr cA wss cA cB cF wf1o cC cA wcel cD cB
      wcel simp2 cA cB cF wf1o cC cA wcel cD cB wcel w3a cB cA cF ccnv wf cD cB
      wcel cD cF ccnv cfv cA wcel cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB
      cF wf1o cB cA cF ccnv wf1o cB cA cF ccnv wf cA cB cF wf1o cC cA wcel cD
      cB wcel simp1 cA cB cF f1ocnv cB cA cF ccnv f1of 3syl cA cB cF wf1o cC cA
      wcel cD cB wcel simp3 cB cA cD cF ccnv ffvelrn syl2anc cC cD cF ccnv cfv
      cA prssi syl2anc cC cD cF ccnv cfv cpr cA undif sylib syl5eq cA cC cD cF
      ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA cA cid cA cC cD cF ccnv
      cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun
      f1oeq3 syl mpbid cA cA cB cF cid cA cC cD cF ccnv cfv cpr cdif cres cC cD
      cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun f1oco syl2anc cG cF cid cA
      cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC
      cop cpr cun ccom wceq cA cB cG wf1o cA cB cF cid cA cC cD cF ccnv cfv cpr
      cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun ccom wf1o
      wb fveqf1o.1 cA cB cG cF cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF
      ccnv cfv cop cD cF ccnv cfv cC cop cpr cun ccom f1oeq1 ax-mp sylibr cA cB
      cF wf1o cC cA wcel cD cB wcel w3a cC cG cfv cC cid cA cC cD cF ccnv cfv
      cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun cfv cF
      cfv cD cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cG cfv cC cF cid cA cC
      cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop
      cpr cun ccom cfv cC cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv
      cfv cop cD cF ccnv cfv cC cop cpr cun cfv cF cfv cC cG cF cid cA cC cD cF
      ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr
      cun ccom fveqf1o.1 fveq1i cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cA
      cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr cun wf cC cA wcel cC cF cid cA cC cD cF ccnv cfv cpr cdif
      cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun ccom cfv cC cid
      cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv
      cC cop cpr cun cfv cF cfv wceq cA cB cF wf1o cC cA wcel cD cB wcel w3a cA
      cA cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF
      ccnv cfv cC cop cpr cun wf1o cA cA cid cA cC cD cF ccnv cfv cpr cdif cres
      cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf cA cB cF wf1o cC
      cA wcel cD cB wcel w3a cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cun cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD
      cF ccnv cfv cC cop cpr cun wf1o cA cA cid cA cC cD cF ccnv cfv cpr cdif
      cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf1o cA cB cF
      wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF
      ccnv cfv cpr cun cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun
      cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr cun wf1o cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv
      cfv cpr cun cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop
      cD cF ccnv cfv cC cop cpr cun wf1o cA cB cF wf1o cC cA wcel cD cB wcel
      w3a cA cC cD cF ccnv cfv cpr cdif cA cC cD cF ccnv cfv cpr cdif cid cA cC
      cD cF ccnv cfv cpr cdif cres wf1o cC cD cF ccnv cfv cpr cC cD cF ccnv cfv
      cpr cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr wf1o cA cC cD cF ccnv
      cfv cpr cdif cC cD cF ccnv cfv cpr cin c0 wceq cA cC cD cF ccnv cfv cpr
      cdif cC cD cF ccnv cfv cpr cin c0 wceq cA cC cD cF ccnv cfv cpr cdif cC
      cD cF ccnv cfv cpr cun cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cun cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD
      cF ccnv cfv cC cop cpr cun wf1o cA cC cD cF ccnv cfv cpr cdif cA cC cD cF
      ccnv cfv cpr cdif cid cA cC cD cF ccnv cfv cpr cdif cres wf1o cA cB cF
      wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif f1oi a1i cA
      cB cF wf1o cC cA wcel cD cB wcel w3a cC cA wcel cD cF ccnv cfv cA wcel cC
      cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr wf1o cA cB cF wf1o cC cA wcel cD cB wcel simp2 cA cB cF
      wf1o cC cA wcel cD cB wcel w3a cB cA cF ccnv wf cD cB wcel cD cF ccnv cfv
      cA wcel cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cF wf1o cB cA cF
      ccnv wf1o cB cA cF ccnv wf cA cB cF wf1o cC cA wcel cD cB wcel simp1 cA
      cB cF f1ocnv cB cA cF ccnv f1of 3syl cA cB cF wf1o cC cA wcel cD cB wcel
      simp3 cB cA cD cF ccnv ffvelrn syl2anc cC cD cF ccnv cfv cA cA f1oprswap
      syl2anc cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cin c0 wceq
      cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC
      cD cF ccnv cfv cpr cin cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv cpr
      cdif cin c0 cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr incom cC
      cD cF ccnv cfv cpr cA disjdif eqtri a1i cA cC cD cF ccnv cfv cpr cdif cC
      cD cF ccnv cfv cpr cin c0 wceq cA cB cF wf1o cC cA wcel cD cB wcel w3a cA
      cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cin cC cD cF ccnv cfv
      cpr cA cC cD cF ccnv cfv cpr cdif cin c0 cA cC cD cF ccnv cfv cpr cdif cC
      cD cF ccnv cfv cpr incom cC cD cF ccnv cfv cpr cA disjdif eqtri a1i cA cC
      cD cF ccnv cfv cpr cdif cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cC cD cF ccnv cfv cpr cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF
      ccnv cfv cop cD cF ccnv cfv cC cop cpr f1oun syl22anc cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr
      cun cA wceq cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cA cC
      cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC cD cF ccnv
      cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun
      wf1o cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cun cid cA cC
      cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop
      cpr cun wf1o wb cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv
      cfv cpr cdif cC cD cF ccnv cfv cpr cun cC cD cF ccnv cfv cpr cA cC cD cF
      ccnv cfv cpr cdif cun cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr uncom cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cD cF ccnv cfv cpr
      cA wss cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv cpr cdif cun cA wceq cA
      cB cF wf1o cC cA wcel cD cB wcel w3a cC cA wcel cD cF ccnv cfv cA wcel cC
      cD cF ccnv cfv cpr cA wss cA cB cF wf1o cC cA wcel cD cB wcel simp2 cA cB
      cF wf1o cC cA wcel cD cB wcel w3a cB cA cF ccnv wf cD cB wcel cD cF ccnv
      cfv cA wcel cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cF wf1o cB cA
      cF ccnv wf1o cB cA cF ccnv wf cA cB cF wf1o cC cA wcel cD cB wcel simp1
      cA cB cF f1ocnv cB cA cF ccnv f1of 3syl cA cB cF wf1o cC cA wcel cD cB
      wcel simp3 cB cA cD cF ccnv ffvelrn syl2anc cC cD cF ccnv cfv cA prssi
      syl2anc cC cD cF ccnv cfv cpr cA undif sylib syl5eq cA cC cD cF ccnv cfv
      cpr cdif cC cD cF ccnv cfv cpr cun cA cA cC cD cF ccnv cfv cpr cdif cC cD
      cF ccnv cfv cpr cun cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv
      cfv cop cD cF ccnv cfv cC cop cpr cun f1oeq2 syl mpbid cA cB cF wf1o cC
      cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cun cA wceq cA cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr
      cun cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF
      ccnv cfv cC cop cpr cun wf1o cA cA cid cA cC cD cF ccnv cfv cpr cdif cres
      cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun wf1o wb cA cB cF wf1o
      cC cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cun cC cD cF ccnv cfv cpr cA cC cD cF ccnv cfv cpr cdif cun cA cA cC
      cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr uncom cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cC cD cF ccnv cfv cpr cA wss cC cD cF ccnv cfv cpr cA
      cC cD cF ccnv cfv cpr cdif cun cA wceq cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cC cA wcel cD cF ccnv cfv cA wcel cC cD cF ccnv cfv cpr cA wss
      cA cB cF wf1o cC cA wcel cD cB wcel simp2 cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cB cA cF ccnv wf cD cB wcel cD cF ccnv cfv cA wcel cA cB cF wf1o
      cC cA wcel cD cB wcel w3a cA cB cF wf1o cB cA cF ccnv wf1o cB cA cF ccnv
      wf cA cB cF wf1o cC cA wcel cD cB wcel simp1 cA cB cF f1ocnv cB cA cF
      ccnv f1of 3syl cA cB cF wf1o cC cA wcel cD cB wcel simp3 cB cA cD cF ccnv
      ffvelrn syl2anc cC cD cF ccnv cfv cA prssi syl2anc cC cD cF ccnv cfv cpr
      cA undif sylib syl5eq cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr
      cun cA cA cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD
      cF ccnv cfv cC cop cpr cun f1oeq3 syl mpbid cA cA cid cA cC cD cF ccnv
      cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun
      f1of syl cA cB cF wf1o cC cA wcel cD cB wcel simp2 cA cA cC cF cid cA cC
      cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop
      cpr cun fvco3 syl2anc syl5eq cA cB cF wf1o cC cA wcel cD cB wcel w3a cC
      cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr cun cfv cF cfv cD cF ccnv cfv cF cfv cD cA cB cF wf1o cC
      cA wcel cD cB wcel w3a cC cid cA cC cD cF ccnv cfv cpr cdif cres cC cD cF
      ccnv cfv cop cD cF ccnv cfv cC cop cpr cun cfv cD cF ccnv cfv cF cA cB cF
      wf1o cC cA wcel cD cB wcel w3a cC cid cA cC cD cF ccnv cfv cpr cdif cres
      cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun cfv cC cC cD cF ccnv
      cfv cop cD cF ccnv cfv cC cop cpr cfv cD cF ccnv cfv cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cid cA cC cD cF ccnv cfv cpr cdif cres cA cC cD cF
      ccnv cfv cpr cdif wfn cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cC
      cD cF ccnv cfv cpr wfn cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cin c0 wceq cC cC cD cF ccnv cfv cpr wcel cC cid cA cC cD cF ccnv cfv
      cpr cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cun cfv cC
      cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cfv wceq cid cA cC cD cF
      ccnv cfv cpr cdif cres cA cC cD cF ccnv cfv cpr cdif wfn cA cB cF wf1o cC
      cA wcel cD cB wcel w3a cA cC cD cF ccnv cfv cpr cdif fnresi a1i cA cB cF
      wf1o cC cA wcel cD cB wcel w3a cC cD cF ccnv cfv cpr cC cD cF ccnv cfv
      cpr cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr wf1o cC cD cF ccnv
      cfv cop cD cF ccnv cfv cC cop cpr cC cD cF ccnv cfv cpr wfn cA cB cF wf1o
      cC cA wcel cD cB wcel w3a cC cA wcel cD cF ccnv cfv cA wcel cC cD cF ccnv
      cfv cpr cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop
      cpr wf1o cA cB cF wf1o cC cA wcel cD cB wcel simp2 cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cB cA cF ccnv wf cD cB wcel cD cF ccnv cfv cA wcel cA
      cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cF wf1o cB cA cF ccnv wf1o cB
      cA cF ccnv wf cA cB cF wf1o cC cA wcel cD cB wcel simp1 cA cB cF f1ocnv
      cB cA cF ccnv f1of 3syl cA cB cF wf1o cC cA wcel cD cB wcel simp3 cB cA
      cD cF ccnv ffvelrn syl2anc cC cD cF ccnv cfv cA cA f1oprswap syl2anc cC
      cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr f1ofn syl cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr cin c0 wceq cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cC cD cF ccnv
      cfv cpr cdif cC cD cF ccnv cfv cpr cin cC cD cF ccnv cfv cpr cA cC cD cF
      ccnv cfv cpr cdif cin c0 cA cC cD cF ccnv cfv cpr cdif cC cD cF ccnv cfv
      cpr incom cC cD cF ccnv cfv cpr cA disjdif eqtri a1i cA cB cF wf1o cC cA
      wcel cD cB wcel w3a cC cA wcel cC cC cD cF ccnv cfv cpr wcel cA cB cF
      wf1o cC cA wcel cD cB wcel simp2 cC cD cF ccnv cfv cA prid1g syl cA cC cD
      cF ccnv cfv cpr cdif cC cD cF ccnv cfv cpr cid cA cC cD cF ccnv cfv cpr
      cdif cres cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr cC fvun2
      syl112anc cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cD cF ccnv cfv cop
      cD cF ccnv cfv cC cop cpr wfun cC cD cF ccnv cfv cop cC cD cF ccnv cfv
      cop cD cF ccnv cfv cC cop cpr wcel cC cC cD cF ccnv cfv cop cD cF ccnv
      cfv cC cop cpr cfv cD cF ccnv cfv wceq cA cB cF wf1o cC cA wcel cD cB
      wcel w3a cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr cC cD cF ccnv cfv
      cop cD cF ccnv cfv cC cop cpr wf1o cC cD cF ccnv cfv cop cD cF ccnv cfv
      cC cop cpr wfun cA cB cF wf1o cC cA wcel cD cB wcel w3a cC cA wcel cD cF
      ccnv cfv cA wcel cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr cC cD cF
      ccnv cfv cop cD cF ccnv cfv cC cop cpr wf1o cA cB cF wf1o cC cA wcel cD
      cB wcel simp2 cA cB cF wf1o cC cA wcel cD cB wcel w3a cB cA cF ccnv wf cD
      cB wcel cD cF ccnv cfv cA wcel cA cB cF wf1o cC cA wcel cD cB wcel w3a cA
      cB cF wf1o cB cA cF ccnv wf1o cB cA cF ccnv wf cA cB cF wf1o cC cA wcel
      cD cB wcel simp1 cA cB cF f1ocnv cB cA cF ccnv f1of 3syl cA cB cF wf1o cC
      cA wcel cD cB wcel simp3 cB cA cD cF ccnv ffvelrn syl2anc cC cD cF ccnv
      cfv cA cA f1oprswap syl2anc cC cD cF ccnv cfv cpr cC cD cF ccnv cfv cpr
      cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr f1ofun syl cC cD cF ccnv
      cfv cop cD cF ccnv cfv cC cop cC cD cF ccnv cfv opex prid1 cC cD cF ccnv
      cfv cC cD cF ccnv cfv cop cD cF ccnv cfv cC cop cpr funopfv ee10 eqtrd
      fveq2d cA cB cF wf1o cC cA wcel cD cB wcel w3a cA cB cF wf1o cD cB wcel
      cD cF ccnv cfv cF cfv cD wceq cA cB cF wf1o cC cA wcel cD cB wcel simp1
      cA cB cF wf1o cC cA wcel cD cB wcel simp3 cA cB cD cF f1ocnvfv2 syl2anc
      eqtrd eqtrd jca $.
  $}

  ${
    $d u v y z A $.  $d u v y z B $.  $d u v x z C $.  $d x y z R $.  $d x Y $.
    $d u v x z D $.  $d u v y z F $.  $d u v x y z ph $.  $d u v x y z X $.
    $d x y z S $.
    flift.1 $e |- F = ran ( x e. X |-> <. A , B >. ) $.
    flift.2 $e |- ( ( ph /\ x e. X ) -> A e. R ) $.
    flift.3 $e |- ( ( ph /\ x e. X ) -> B e. S ) $.
    $( ` F ` , a function lift, is a subset of ` R X. S ` .  (Contributed by
       Mario Carneiro, 23-Dec-2016.) $)
    fliftrel $p |- ( ph -> F C_ ( R X. S ) ) $=
      wph cF vx cX cA cB cop cmpt crn cR cS cxp flift.1 wph cX cR cS cxp vx cX
      cA cB cop cmpt wf vx cX cA cB cop cmpt crn cR cS cxp wss wph vx cX cA cB
      cop cR cS cxp vx cX cA cB cop cmpt wph vx cv cX wcel wa cA cR wcel cB cS
      wcel cA cB cop cR cS cxp wcel flift.2 flift.3 cA cB cR cS opelxpi syl2anc
      vx cX cA cB cop cmpt eqid fmptd cX cR cS cxp vx cX cA cB cop cmpt frn syl
      syl5eqss $.

    $( Elementhood in the relation ` F ` .  (Contributed by Mario Carneiro,
       23-Dec-2016.) $)
    fliftel $p |- ( ph -> ( C F D <-> E. x e. X ( C = A /\ D = B ) ) ) $=
      cC cD cF wbr cC cD cop cA cB cop wceq vx cX wrex wph cC cA wceq cD cB
      wceq wa vx cX wrex cC cD cF wbr cC cD cop cF wcel cC cD cop vx cX cA cB
      cop cmpt crn wcel cC cD cop cA cB cop wceq vx cX wrex cC cD cF df-br cF
      vx cX cA cB cop cmpt crn cC cD cop flift.1 eleq2i vx cX cA cB cop cC cD
      cop vx cX cA cB cop cmpt vx cX cA cB cop cmpt eqid cA cB opex elrnmpti
      3bitri wph cC cD cop cA cB cop wceq cC cA wceq cD cB wceq wa vx cX wph vx
      cv cX wcel wa cA cR wcel cB cS wcel cC cD cop cA cB cop wceq cC cA wceq
      cD cB wceq wa wb flift.2 flift.3 cC cD cA cB cR cS opthg2 syl2anc
      rexbidva syl5bb $.

    $( Elementhood in the relation ` F ` .  (Contributed by Mario Carneiro,
       23-Dec-2016.) $)
    fliftel1 $p |- ( ( ph /\ x e. X ) -> A F B ) $=
      wph vx cv cX wcel wa cA cB cop cF wcel cA cB cF wbr wph vx cv cX wcel wa
      cA cB cop vx cX cA cB cop cmpt crn cF vx cv cX wcel cA cB cop vx cX cA cB
      cop cmpt crn wcel wph vx cv cX wcel cA cB cop cvv wcel cA cB cop vx cX cA
      cB cop cmpt crn wcel cA cB opex vx cX cA cB cop vx cX cA cB cop cmpt cvv
      vx cX cA cB cop cmpt eqid elrnmpt1 mpan2 adantl flift.1 syl6eleqr cA cB
      cF df-br sylibr $.

    $( Converse of the relation ` F ` .  (Contributed by Mario Carneiro,
       23-Dec-2016.) $)
    fliftcnv $p |- ( ph -> `' F = ran ( x e. X |-> <. B , A >. ) ) $=
      cF ccnv wrel vx cX cB cA cop cmpt crn wrel wa wph cF ccnv vx cX cB cA cop
      cmpt crn wceq wph vx cX cB cA cop cmpt crn wrel cF ccnv wrel wph vx cX cB
      cA cop cmpt crn cS cR cxp wss cS cR cxp wrel vx cX cB cA cop cmpt crn
      wrel wph vx cB cA cS cR vx cX cB cA cop cmpt crn cX vx cX cB cA cop cmpt
      crn eqid flift.3 flift.2 fliftrel cS cR relxp vx cX cB cA cop cmpt crn cS
      cR cxp relss ee10 cF relcnv jctil wph vy vz cF ccnv vx cX cB cA cop cmpt
      crn wph vy cv vz cv cF ccnv wbr vy cv vz cv vx cX cB cA cop cmpt crn wbr
      vy cv vz cv cop cF ccnv wcel vy cv vz cv cop vx cX cB cA cop cmpt crn
      wcel wph vy cv vz cv cF ccnv wbr vy cv cB wceq vz cv cA wceq wa vx cX
      wrex vy cv vz cv vx cX cB cA cop cmpt crn wbr wph vz cv vy cv cF wbr vz
      cv cA wceq vy cv cB wceq wa vx cX wrex vy cv vz cv cF ccnv wbr vy cv cB
      wceq vz cv cA wceq wa vx cX wrex wph vx cA cB vz cv vy cv cR cS cF cX
      flift.1 flift.2 flift.3 fliftel vy cv vz cv cF vy vex vz vex brcnv vy cv
      cB wceq vz cv cA wceq wa vz cv cA wceq vy cv cB wceq wa vx cX vy cv cB
      wceq vz cv cA wceq ancom rexbii 3bitr4g wph vx cB cA vy cv vz cv cS cR vx
      cX cB cA cop cmpt crn cX vx cX cB cA cop cmpt crn eqid flift.3 flift.2
      fliftel bitr4d vy cv vz cv cF ccnv df-br vy cv vz cv vx cX cB cA cop cmpt
      crn df-br 3bitr3g eqrelrdv2 mpancom $.

    ${
      fliftfun.4 $e |- ( x = y -> A = C ) $.
      fliftfun.5 $e |- ( x = y -> B = D ) $.
      $( The function ` F ` is the unique function defined by ` F `` A = B ` ,
         provided that the well-definedness condition holds.  (Contributed by
         Mario Carneiro, 23-Dec-2016.) $)
      fliftfun $p |- ( ph -> ( Fun F <->
        A. x e. X A. y e. X ( A = C -> B = D ) ) ) $=
        wph cF wfun cA cC wceq cB cD wceq wi vy cX wral vx cX wral wph cF wfun
        cA cC wceq cB cD wceq wi vy cX wral vx cX wph vx nfv vx cF vx cF vx cX
        cA cB cop cmpt crn flift.1 vx vx cX cA cB cop cmpt vx cX cA cB cop
        nfmpt1 nfrn nfcxfr nffun wph cF wfun vx cv cX wcel cA cC wceq cB cD
        wceq wi vy cX wral wph cF wfun wa vx cv cX wcel wa cA cC wceq cB cD
        wceq wi vy cX wph cF wfun wa vx cv cX wcel vy cv cX wcel cA cC wceq cB
        cD wceq wi cA cC wceq cA cF cfv cC cF cfv wceq wph cF wfun wa vx cv cX
        wcel vy cv cX wcel wa wa cB cD wceq cA cC cF fveq2 wph cF wfun wa vx cv
        cX wcel vy cv cX wcel wa wa cA cF cfv cB cC cF cfv cD wph cF wfun wa vx
        cv cX wcel vy cv cX wcel wa wa cF wfun cA cB cF wbr cA cF cfv cB wceq
        wph cF wfun vx cv cX wcel vy cv cX wcel wa simplr wph vx cv cX wcel cA
        cB cF wbr cF wfun vy cv cX wcel wph vx cA cB cR cS cF cX flift.1
        flift.2 flift.3 fliftel1 ad2ant2r cA cB cF funbrfv sylc wph cF wfun wa
        vx cv cX wcel vy cv cX wcel wa wa cF wfun cC cD cF wbr cC cF cfv cD
        wceq wph cF wfun vx cv cX wcel vy cv cX wcel wa simplr wph cF wfun wa
        vx cv cX wcel vy cv cX wcel wa wa cC cD cF wbr cC cA wceq cD cB wceq wa
        vx cX wrex wph cF wfun wa vx cv cX wcel vy cv cX wcel wa wa vy cv cX
        wcel cC cC wceq cD cD wceq cC cA wceq cD cB wceq wa vx cX wrex wph cF
        wfun wa vx cv cX wcel vy cv cX wcel simprr wph cF wfun wa vx cv cX wcel
        vy cv cX wcel wa wa cC eqidd wph cF wfun wa vx cv cX wcel vy cv cX wcel
        wa wa cD eqidd cC cA wceq cD cB wceq wa cC cC wceq cD cD wceq wa vx vy
        cv cX vx cv vy cv wceq cC cA wceq cC cC wceq cD cB wceq cD cD wceq vx
        cv vy cv wceq cA cC cC fliftfun.4 eqeq2d vx cv vy cv wceq cB cD cD
        fliftfun.5 eqeq2d anbi12d rspcev syl12anc wph cC cD cF wbr cC cA wceq
        cD cB wceq wa vx cX wrex wb cF wfun vx cv cX wcel vy cv cX wcel wa wph
        vx cA cB cC cD cR cS cF cX flift.1 flift.2 flift.3 fliftel ad2antrr
        mpbird cC cD cF funbrfv sylc eqeq12d syl5ib anassrs ralrimiva exp31
        ralrimd wph cA cC wceq cB cD wceq wi vy cX wral vx cX wral vz cv vu cv
        cF wbr vz cv vv cv cF wbr wa vu cv vv cv wceq wi vv wal vu wal vz wal
        cF wfun wph cA cC wceq cB cD wceq wi vy cX wral vx cX wral vz cv vu cv
        cF wbr vz cv vv cv cF wbr wa vu cv vv cv wceq wi vv wal vu wal vz wph
        cA cC wceq cB cD wceq wi vy cX wral vx cX wral vz cv vu cv cF wbr vz cv
        vv cv cF wbr wa vu cv vv cv wceq wi vv wal vu wph cA cC wceq cB cD wceq
        wi vy cX wral vx cX wral vz cv vu cv cF wbr vz cv vv cv cF wbr wa vu cv
        vv cv wceq wi vv wph vz cv vu cv cF wbr vz cv vv cv cF wbr wa vz cv cA
        wceq vu cv cB wceq wa vx cX wrex vz cv cC wceq vv cv cD wceq wa vy cX
        wrex wa cA cC wceq cB cD wceq wi vy cX wral vx cX wral vu cv vv cv wceq
        wph vz cv vu cv cF wbr vz cv vv cv cF wbr wa vz cv cA wceq vu cv cB
        wceq wa vx cX wrex vz cv cC wceq vv cv cD wceq wa vy cX wrex wa wph vz
        cv vu cv cF wbr vz cv cA wceq vu cv cB wceq wa vx cX wrex vz cv vv cv
        cF wbr vz cv cC wceq vv cv cD wceq wa vy cX wrex wph vx cA cB vz cv vu
        cv cR cS cF cX flift.1 flift.2 flift.3 fliftel wph vz cv vv cv cF wbr
        vz cv cA wceq vv cv cB wceq wa vx cX wrex vz cv cC wceq vv cv cD wceq
        wa vy cX wrex wph vx cA cB vz cv vv cv cR cS cF cX flift.1 flift.2
        flift.3 fliftel vz cv cA wceq vv cv cB wceq wa vz cv cC wceq vv cv cD
        wceq wa vx vy cX vx cv vy cv wceq vz cv cA wceq vz cv cC wceq vv cv cB
        wceq vv cv cD wceq vx cv vy cv wceq cA cC vz cv fliftfun.4 eqeq2d vx cv
        vy cv wceq cB cD vv cv fliftfun.5 eqeq2d anbi12d cbvrexv syl6bb anbi12d
        biimpd vz cv cA wceq vu cv cB wceq wa vx cX wrex vz cv cC wceq vv cv cD
        wceq wa vy cX wrex wa vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv
        cv cD wceq wa wa vy cX wrex vx cX wrex cA cC wceq cB cD wceq wi vy cX
        wral vx cX wral vu cv vv cv wceq vz cv cA wceq vu cv cB wceq wa vz cv
        cC wceq vv cv cD wceq wa vx vy cX cX reeanv cA cC wceq cB cD wceq wi vy
        cX wral vx cX wral vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv
        cD wceq wa wa vy cX wrex vx cX wrex vu cv vv cv wceq cA cC wceq cB cD
        wceq wi vy cX wral vx cX wral vz cv cA wceq vu cv cB wceq wa vz cv cC
        wceq vv cv cD wceq wa wa vy cX wrex vx cX wrex wa cA cC wceq cB cD wceq
        wi vy cX wral vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv cD
        wceq wa wa vy cX wrex wa vx cX wrex vu cv vv cv wceq cA cC wceq cB cD
        wceq wi vy cX wral vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv
        cD wceq wa wa vy cX wrex vx cX r19.29 cA cC wceq cB cD wceq wi vy cX
        wral vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv cD wceq wa wa
        vy cX wrex wa vu cv vv cv wceq vx cX cA cC wceq cB cD wceq wi vy cX
        wral vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv cD wceq wa wa
        vy cX wrex wa cA cC wceq cB cD wceq wi vz cv cA wceq vu cv cB wceq wa
        vz cv cC wceq vv cv cD wceq wa wa wa vy cX wrex vu cv vv cv wceq cA cC
        wceq cB cD wceq wi vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv
        cD wceq wa wa vy cX r19.29 cA cC wceq cB cD wceq wi vz cv cA wceq vu cv
        cB wceq wa vz cv cC wceq vv cv cD wceq wa wa wa vu cv vv cv wceq vy cX
        cA cC wceq cB cD wceq wi vz cv cA wceq vu cv cB wceq wa vz cv cC wceq
        vv cv cD wceq wa wa wa cB cD vu cv vv cv cA cC wceq cB cD wceq wi vz cv
        cA wceq vu cv cB wceq wa vz cv cC wceq vv cv cD wceq wa wa cB cD wceq
        vz cv cA wceq vu cv cB wceq wa vz cv cC wceq vv cv cD wceq wa wa cA cC
        wceq cB cD wceq vz cv cA wceq vz cv cC wceq cA cC wceq vu cv cB wceq vv
        cv cD wceq vz cv cA cC eqtr2 ad2ant2r imim1i imp cA cC wceq cB cD wceq
        wi vz cv cA wceq vu cv cB wceq vz cv cC wceq vv cv cD wceq wa simprlr
        cA cC wceq cB cD wceq wi vz cv cA wceq vu cv cB wceq wa vz cv cC wceq
        vv cv cD wceq simprrr 3eqtr4d rexlimivw syl rexlimivw syl ex syl5bir
        syl9 alrimdv alrimdv alrimdv wph cF wrel cF wfun vz cv vu cv cF wbr vz
        cv vv cv cF wbr wa vu cv vv cv wceq wi vv wal vu wal vz wal wb wph cF
        cR cS cxp wss cR cS cxp wrel cF wrel wph vx cA cB cR cS cF cX flift.1
        flift.2 flift.3 fliftrel cR cS relxp cF cR cS cxp relss ee10 cF wfun cF
        wrel vz cv vu cv cF wbr vz cv vv cv cF wbr wa vu cv vv cv wceq wi vv
        wal vu wal vz wal vz vu vv cF dffun2 baib syl sylibrd impbid $.

      fliftfund.6 $e |- ( ( ph /\ ( x e. X /\ y e. X /\ A = C ) ) -> B = D ) $.
      $( The function ` F ` is the unique function defined by ` F `` A = B ` ,
         provided that the well-definedness condition holds.  (Contributed by
         Mario Carneiro, 23-Dec-2016.) $)
      fliftfund $p |- ( ph -> Fun F ) $=
        wph cF wfun cA cC wceq cB cD wceq wi vy cX wral vx cX wral wph cA cC
        wceq cB cD wceq wi vx vy cX cX wph vx cv cX wcel vy cv cX wcel cA cC
        wceq cB cD wceq wi wph vx cv cX wcel vy cv cX wcel cA cC wceq cB cD
        wceq fliftfund.6 3exp2 imp32 ralrimivva wph vx vy cA cB cC cD cR cS cF
        cX flift.1 flift.2 flift.3 fliftfun.4 fliftfun.5 fliftfun mpbird $.
    $}

    $( The function ` F ` is the unique function defined by ` F `` A = B ` ,
       provided that the well-definedness condition holds.  (Contributed by
       Mario Carneiro, 23-Dec-2016.) $)
    fliftfuns $p |- ( ph -> ( Fun F <-> A. y e. X A. z e. X
      ( [_ y / x ]_ A = [_ z / x ]_ A -> [_ y / x ]_ B = [_ z / x ]_ B ) ) ) $=
      wph vy vz vx vy cv cA csb vx vy cv cB csb vx vz cv cA csb vx vz cv cB csb
      cR cS cF cX cF vx cX cA cB cop cmpt crn vy cX vx vy cv cA csb vx vy cv cB
      csb cop cmpt crn flift.1 vx cX cA cB cop cmpt vy cX vx vy cv cA csb vx vy
      cv cB csb cop cmpt vx vy cX cA cB cop vx vy cv cA csb vx vy cv cB csb cop
      vy cA cB cop nfcv vx vx vy cv cA csb vx vy cv cB csb vx vy cv cA nfcsb1v
      vx vy cv cB nfcsb1v nfop vx cv vy cv wceq cA vx vy cv cA csb cB vx vy cv
      cB csb vx vy cv cA csbeq1a vx vy cv cB csbeq1a opeq12d cbvmpt rneqi eqtri
      wph cA cR wcel vx cX wral vy cv cX wcel vx vy cv cA csb cR wcel wph cA cR
      wcel vx cX flift.2 ralrimiva cA cR wcel vx vy cv cA csb cR wcel vx vy cv
      cX vx vx vy cv cA csb cR vx vy cv cA nfcsb1v nfel1 vx cv vy cv wceq cA vx
      vy cv cA csb cR vx vy cv cA csbeq1a eleq1d rspc mpan9 wph cB cS wcel vx
      cX wral vy cv cX wcel vx vy cv cB csb cS wcel wph cB cS wcel vx cX
      flift.3 ralrimiva cB cS wcel vx vy cv cB csb cS wcel vx vy cv cX vx vx vy
      cv cB csb cS vx vy cv cB nfcsb1v nfel1 vx cv vy cv wceq cB vx vy cv cB
      csb cS vx vy cv cB csbeq1a eleq1d rspc mpan9 vx vy cv vz cv cA csbeq1 vx
      vy cv vz cv cB csbeq1 fliftfun $.

    $( The domain and range of the function ` F ` .  (Contributed by Mario
       Carneiro, 23-Dec-2016.) $)
    fliftf $p |- ( ph -> ( Fun F <-> F : ran ( x e. X |-> A ) --> S ) ) $=
      wph cF wfun vx cX cA cmpt crn cS cF wf wph cF wfun vx cX cA cmpt crn cS
      cF wf wph cF wfun wa cF vx cX cA cmpt crn wfn cF crn cS wss vx cX cA cmpt
      crn cS cF wf wph cF wfun wa cF wfun cF cdm vx cX cA cmpt crn wceq cF vx
      cX cA cmpt crn wfn wph cF wfun simpr wph cF wfun wa vy cv vz cv cF wbr vz
      wex vy cab vy cv cA wceq vx cX wrex vy cab cF cdm vx cX cA cmpt crn wph
      cF wfun wa vy cv vz cv cF wbr vz wex vy cv cA wceq vx cX wrex vy wph cF
      wfun wa vy cv vz cv cF wbr vz wex vy cv cA wceq vz cv cB wceq wa vx cX
      wrex vz wex vy cv cA wceq vx cX wrex wph vy cv vz cv cF wbr vz wex vy cv
      cA wceq vz cv cB wceq wa vx cX wrex vz wex wb cF wfun wph vy cv vz cv cF
      wbr vy cv cA wceq vz cv cB wceq wa vx cX wrex vz wph vx cA cB vy cv vz cv
      cR cS cF cX flift.1 flift.2 flift.3 fliftel exbidv adantr vy cv cA wceq
      vz cv cB wceq wa vx cX wrex vz wex vy cv cA wceq vz cv cB wceq wa vz wex
      vx cX wrex wph cF wfun wa vy cv cA wceq vx cX wrex vy cv cA wceq vz cv cB
      wceq wa vx vz cX rexcom4 wph vy cv cA wceq vz cv cB wceq wa vz wex vx cX
      wrex vy cv cA wceq vx cX wrex wb cF wfun wph vy cv cA wceq vz cv cB wceq
      wa vz wex vy cv cA wceq vx cX wph vx cv cX wcel wa vy cv cA wceq vy cv cA
      wceq vz cv cB wceq vz wex wa vy cv cA wceq vz cv cB wceq wa vz wex wph vx
      cv cX wcel wa vz cv cB wceq vz wex vy cv cA wceq wph vx cv cX wcel wa cB
      cS wcel vz cv cB wceq vz wex flift.3 vz cB cS elisset syl biantrud vy cv
      cA wceq vz cv cB wceq vz 19.42v syl6rbbr rexbidva adantr syl5bbr bitrd
      abbidv vy vz cF df-dm vx vy cX cA vx cX cA cmpt vx cX cA cmpt eqid rnmpt
      3eqtr4g cF vx cX cA cmpt crn df-fn sylanbrc wph cF wfun wa cF crn cR cS
      cxp crn cS wph cF wfun wa cF cR cS cxp wss cF crn cR cS cxp crn wss wph
      cF cR cS cxp wss cF wfun wph vx cA cB cR cS cF cX flift.1 flift.2 flift.3
      fliftrel adantr cF cR cS cxp rnss syl cR cS rnxpss syl6ss vx cX cA cmpt
      crn cS cF df-f sylanbrc ex vx cX cA cmpt crn cS cF ffun impbid1 $.

    fliftval.4 $e |- ( x = Y -> A = C ) $.
    fliftval.5 $e |- ( x = Y -> B = D ) $.
    fliftval.6 $e |- ( ph -> Fun F ) $.
    $( The value of the function ` F ` .  (Contributed by Mario Carneiro,
       23-Dec-2016.) $)
    fliftval $p |- ( ( ph /\ Y e. X ) -> ( F ` C ) = D ) $=
      wph cY cX wcel wa cF wfun cC cD cF wbr cC cF cfv cD wceq wph cF wfun cY
      cX wcel fliftval.6 adantr wph cY cX wcel wa cC cD cF wbr cC cA wceq cD cB
      wceq wa vx cX wrex wph cY cX wcel wa cY cX wcel cC cC wceq cD cD wceq wa
      cC cA wceq cD cB wceq wa vx cX wrex wph cY cX wcel simpr wph cD cD wceq
      cY cX wcel cC cC wceq wph cD eqidd cY cX wcel cC eqidd anim12ci cC cA
      wceq cD cB wceq wa cC cC wceq cD cD wceq wa vx cY cX vx cv cY wceq cC cA
      wceq cC cC wceq cD cB wceq cD cD wceq vx cv cY wceq cA cC cC fliftval.4
      eqeq2d vx cv cY wceq cB cD cD fliftval.5 eqeq2d anbi12d rspcev syl2anc
      wph cC cD cF wbr cC cA wceq cD cB wceq wa vx cX wrex wb cY cX wcel wph vx
      cA cB cC cD cR cS cF cX flift.1 flift.2 flift.3 fliftel adantr mpbird cC
      cD cF funbrfv sylc $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y H $.  $d x y G $.
    $d x y R $.  $d x y S $.  $d x y T $.
    $( Equality theorem for isomorphisms.  (Contributed by NM, 17-May-2004.) $)
    isoeq1 $p |- ( H = G ->
          ( H Isom R , S ( A , B ) <-> G Isom R , S ( A , B ) ) ) $=
      cH cG wceq cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wb vy cA wral vx cA wral wa cA cB cG wf1o vx cv vy cv cR wbr vx cv cG
      cfv vy cv cG cfv cS wbr wb vy cA wral vx cA wral wa cA cB cR cS cH wiso
      cA cB cR cS cG wiso cH cG wceq cA cB cH wf1o cA cB cG wf1o vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral vx cv vy cv
      cR wbr vx cv cG cfv vy cv cG cfv cS wbr wb vy cA wral vx cA wral cA cB cH
      cG f1oeq1 cH cG wceq vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wb vx cv vy cv cR wbr vx cv cG cfv vy cv cG cfv cS wbr wb vx vy cA cA cH
      cG wceq vx cv cH cfv vy cv cH cfv cS wbr vx cv cG cfv vy cv cG cfv cS wbr
      vx cv vy cv cR wbr cH cG wceq vx cv cH cfv vx cv cG cfv vy cv cH cfv vy
      cv cG cfv cS vx cv cH cG fveq1 vy cv cH cG fveq1 breq12d bibi2d 2ralbidv
      anbi12d vx vy cA cB cR cS cH df-isom vx vy cA cB cR cS cG df-isom 3bitr4g
      $.

    $( Equality theorem for isomorphisms.  (Contributed by NM, 17-May-2004.) $)
    isoeq2 $p |- ( R = T ->
          ( H Isom R , S ( A , B ) <-> H Isom T , S ( A , B ) ) ) $=
      cR cT wceq cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wb vy cA wral vx cA wral wa cA cB cH wf1o vx cv vy cv cT wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral wa cA cB cR cS cH wiso
      cA cB cT cS cH wiso cR cT wceq vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wb vy cA wral vx cA wral vx cv vy cv cT wbr vx cv cH cfv vy cv
      cH cfv cS wbr wb vy cA wral vx cA wral cA cB cH wf1o cR cT wceq vx cv vy
      cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vx cv vy cv cT wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vx vy cA cA cR cT wceq vx cv vy cv cR wbr vx
      cv vy cv cT wbr vx cv cH cfv vy cv cH cfv cS wbr vx cv vy cv cR cT breq
      bibi1d 2ralbidv anbi2d vx vy cA cB cR cS cH df-isom vx vy cA cB cT cS cH
      df-isom 3bitr4g $.

    $( Equality theorem for isomorphisms.  (Contributed by NM, 17-May-2004.) $)
    isoeq3 $p |- ( S = T ->
          ( H Isom R , S ( A , B ) <-> H Isom R , T ( A , B ) ) ) $=
      cS cT wceq cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wb vy cA wral vx cA wral wa cA cB cH wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cT wbr wb vy cA wral vx cA wral wa cA cB cR cS cH wiso
      cA cB cR cT cH wiso cS cT wceq vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wb vy cA wral vx cA wral vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cT wbr wb vy cA wral vx cA wral cA cB cH wf1o cS cT wceq vx cv vy
      cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cT wbr wb vx vy cA cA cS cT wceq vx cv cH cfv vy cv cH
      cfv cS wbr vx cv cH cfv vy cv cH cfv cT wbr vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS cT breq bibi2d 2ralbidv anbi2d vx vy cA cB cR cS cH
      df-isom vx vy cA cB cR cT cH df-isom 3bitr4g $.

    $( Equality theorem for isomorphisms.  (Contributed by NM, 17-May-2004.) $)
    isoeq4 $p |- ( A = C ->
          ( H Isom R , S ( A , B ) <-> H Isom R , S ( C , B ) ) ) $=
      cA cC wceq cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wb vy cA wral vx cA wral wa cC cB cH wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cC wral vx cC wral wa cA cB cR cS cH wiso
      cC cB cR cS cH wiso cA cC wceq cA cB cH wf1o cC cB cH wf1o vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral vx cv vy cv
      cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cC wral vx cC wral cA cC cB
      cH f1oeq2 vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA
      wral vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cC wral vx
      cA cC vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA cC
      raleq raleqbi1dv anbi12d vx vy cA cB cR cS cH df-isom vx vy cC cB cR cS
      cH df-isom 3bitr4g $.

    $( Equality theorem for isomorphisms.  (Contributed by NM, 17-May-2004.) $)
    isoeq5 $p |- ( B = C ->
          ( H Isom R , S ( A , B ) <-> H Isom R , S ( A , C ) ) ) $=
      cB cC wceq cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wb vy cA wral vx cA wral wa cA cC cH wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral wa cA cB cR cS cH wiso
      cA cC cR cS cH wiso cB cC wceq cA cB cH wf1o cA cC cH wf1o vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral cB cC cA cH
      f1oeq3 anbi1d vx vy cA cB cR cS cH df-isom vx vy cA cC cR cS cH df-isom
      3bitr4g $.
  $}

  ${
    $d y z w H $.  $d y z w R $.  $d y z w S $.  $d y z w A $.  $d y z w B $.
    $d x y z w $.
    nfiso.1 $e |- F/_ x H $.
    nfiso.2 $e |- F/_ x R $.
    nfiso.3 $e |- F/_ x S $.
    nfiso.4 $e |- F/_ x A $.
    nfiso.5 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for an isomorphism.  (Contributed by
       NM, 17-May-2004.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
    nfiso $p |- F/ x H Isom R , S ( A , B ) $=
      cA cB cR cS cH wiso cA cB cH wf1o vy cv vz cv cR wbr vy cv cH cfv vz cv
      cH cfv cS wbr wb vz cA wral vy cA wral wa vx vy vz cA cB cR cS cH df-isom
      cA cB cH wf1o vy cv vz cv cR wbr vy cv cH cfv vz cv cH cfv cS wbr wb vz
      cA wral vy cA wral vx vx cA cB cH nfiso.1 nfiso.4 nfiso.5 nff1o vy cv vz
      cv cR wbr vy cv cH cfv vz cv cH cfv cS wbr wb vz cA wral vx vy cA nfiso.4
      vy cv vz cv cR wbr vy cv cH cfv vz cv cH cfv cS wbr wb vx vz cA nfiso.4
      vy cv vz cv cR wbr vy cv cH cfv vz cv cH cfv cS wbr vx vx vy cv vz cv cR
      vx vy cv nfcv nfiso.2 vx vz cv nfcv nfbr vx vy cv cH cfv vz cv cH cfv cS
      vx vy cv cH nfiso.1 vx vy cv nfcv nffv nfiso.3 vx vz cv cH nfiso.1 vx vz
      cv nfcv nffv nfbr nfbi nfral nfral nfan nfxfr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $( An isomorphism is a one-to-one onto function.  (Contributed by NM,
       27-Apr-2004.) $)
    isof1o $p |- ( H Isom R , S ( A , B ) -> H : A -1-1-onto-> B ) $=
      cA cB cR cS cH wiso cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr wb vy cA wral vx cA wral vx vy cA cB cR cS cH df-isom
      simplbi $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $d x y C $.  $d x y D $.
    $( An isomorphism connects binary relations via its function values.
       (Contributed by NM, 27-Apr-2004.) $)
    isorel $p |- ( ( H Isom R , S ( A , B ) /\ ( C e. A /\ D e. A ) ) ->
                 ( C R D <-> ( H ` C ) S ( H ` D ) ) ) $=
      cA cB cR cS cH wiso vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wb vy cA wral vx cA wral cC cA wcel cD cA wcel wa cC cD cR wbr cC cH cfv
      cD cH cfv cS wbr wb cA cB cR cS cH wiso cA cB cH wf1o vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral vx vy cA cB cR
      cS cH df-isom simprbi vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wb cC cD cR wbr cC cH cfv cD cH cfv cS wbr wb cC vy cv cR wbr cC cH cfv
      vy cv cH cfv cS wbr wb vx vy cC cD cA cA vx cv cC wceq vx cv vy cv cR wbr
      cC vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr cC cH cfv vy cv cH cfv
      cS wbr vx cv cC vy cv cR breq1 vx cv cC wceq vx cv cH cfv cC cH cfv vy cv
      cH cfv cS vx cv cC cH fveq2 breq1d bibi12d vy cv cD wceq cC vy cv cR wbr
      cC cD cR wbr cC cH cfv vy cv cH cfv cS wbr cC cH cfv cD cH cfv cS wbr vy
      cv cD cC cR breq2 vy cv cD wceq vy cv cH cfv cD cH cfv cC cH cfv cS vy cv
      cD cH fveq2 breq2d bibi12d rspc2v mpan9 $.
  $}

  ${
    $d w x y z A $.  $d w z B $.  $d w z C $.  $d w x y z F $.  $d w x y z R $.
    $d w x y z S $.
    $( Express the condition of isomorphism on two strict orders for a
       function's restriction.  (Contributed by Mario Carneiro,
       22-Jan-2015.) $)
    soisores $p |- ( ( ( R Or B /\ S Or C ) /\ ( F : B --> C /\ A C_ B ) ) ->
      ( ( F |` A ) Isom R , S ( A , ( F " A ) ) <->
        A. x e. A A. y e. A ( x R y -> ( F ` x ) S ( F ` y ) ) ) ) $=
      cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa wa cA cF cA cima cR cS cF
      cA cres wiso vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral cA cF cA cima cR cS cF cA cres wiso vx cv vy cv cR wbr vx
      cv cF cfv vy cv cF cfv cS wbr wi vx vy cA cA cA cF cA cima cR cS cF cA
      cres wiso vx cv cA wcel vy cv cA wcel wa wa vx cv vy cv cR wbr vx cv cF
      cfv vy cv cF cfv cS wbr cA cF cA cima cR cS cF cA cres wiso vx cv cA wcel
      vy cv cA wcel wa wa vx cv vy cv cR wbr vx cv cF cA cres cfv vy cv cF cA
      cres cfv cS wbr vx cv cF cfv vy cv cF cfv cS wbr cA cF cA cima vx cv vy
      cv cR cS cF cA cres isorel vx cv cA wcel vy cv cA wcel wa vx cv cF cA
      cres cfv vy cv cF cA cres cfv cS wbr vx cv cF cfv vy cv cF cfv cS wbr wb
      cA cF cA cima cR cS cF cA cres wiso vx cv cA wcel vy cv cA wcel vx cv cF
      cA cres cfv vx cv cF cfv vy cv cF cA cres cfv vy cv cF cfv cS vx cv cA cF
      fvres vy cv cA cF fvres breqan12d adantl bitrd biimpd ralrimivva cB cR
      wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv
      vy cv cF cfv cS wbr wi vy cA wral vx cA wral cA cF cA cima cR cS cF cA
      cres wiso cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a cA cF
      cA cima cF cA cres wf1o vz cv vw cv cR wbr vz cv cF cA cres cfv vw cv cF
      cA cres cfv cS wbr wb vw cA wral vz cA wral cA cF cA cima cR cS cF cA
      cres wiso cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a cF cA
      cres cA wfn cF cA cres crn cF cA cima wceq vz cv cF cA cres cfv vw cv cF
      cA cres cfv wceq vz cv vw cv wceq wi vw cA wral vz cA wral cA cF cA cima
      cF cA cres wf1o cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa cF cA
      cres cA wfn vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa wa cF cB
      wfn cA cB wss cF cA cres cA wfn cB cC cF wf cF cB wfn cB cR wor cC cS wor
      wa cA cB wss cB cC cF ffn ad2antrl cB cR wor cC cS wor wa cB cC cF wf cA
      cB wss simprr cB cA cF fnssres syl2anc 3adant3 cF cA cres crn cF cA cima
      wceq cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a cF cA cima
      cF cA cres crn cF cA df-ima eqcomi a1i cB cR wor cC cS wor wa cB cC cF wf
      cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral w3a vz cv cF cA cres cfv vw cv cF cA cres cfv wceq vz cv
      vw cv wceq wi vz vw cA cA cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa
      vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA
      wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv cF cA cres cfv vw cv cF
      cA cres cfv wceq vz cv cF cfv vw cv cF cfv wceq vz cv vw cv wceq vz cv cA
      wcel vw cv cA wcel wa vz cv cF cA cres cfv vw cv cF cA cres cfv wceq vz
      cv cF cfv vw cv cF cfv wceq wb cB cR wor cC cS wor wa cB cC cF wf cA cB
      wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral
      vx cA wral w3a vz cv cA wcel vw cv cA wcel vz cv cF cA cres cfv vz cv cF
      cfv vw cv cF cA cres cfv vw cv cF cfv vz cv cA cF fvres vw cv cA cF fvres
      eqeqan12d adantl cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy
      cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a
      vz cv cA wcel vw cv cA wcel wa wa vz cv cF cfv vw cv cF cfv cS wbr vw cv
      cF cfv vz cv cF cfv cS wbr wo wn vz cv vw cv cR wbr vw cv vz cv cR wbr wo
      wn vz cv cF cfv vw cv cF cfv wceq vz cv vw cv wceq cB cR wor cC cS wor wa
      cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS
      wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv
      vw cv cR wbr vw cv vz cv cR wbr wo vz cv cF cfv vw cv cF cfv cS wbr vw cv
      cF cfv vz cv cF cfv cS wbr wo cB cR wor cC cS wor wa cB cC cF wf cA cB
      wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral
      vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv vw cv cR wbr vz cv
      cF cfv vw cv cF cfv cS wbr vw cv vz cv cR wbr vw cv cF cfv vz cv cF cfv
      cS wbr cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA
      wcel vw cv cA wcel wa wa vz cv cA wcel vw cv cA wcel vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv vw cv cR
      wbr vz cv cF cfv vw cv cF cfv cS wbr wi cB cR wor cC cS wor wa cB cC cF
      wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy
      cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel simprl cB cR wor cC cS
      wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      simprr cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel
      vw cv cA wcel wa simpl3 vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS
      wbr wi vz cv vw cv cR wbr vz cv cF cfv vw cv cF cfv cS wbr wi vz cv vy cv
      cR wbr vz cv cF cfv vy cv cF cfv cS wbr wi vx vy vz cv vw cv cA cA vx cv
      vz cv wceq vx cv vy cv cR wbr vz cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr vz cv cF cfv vy cv cF cfv cS wbr vx cv vz cv vy cv cR breq1 vx
      cv vz cv wceq vx cv cF cfv vz cv cF cfv vy cv cF cfv cS vx cv vz cv cF
      fveq2 breq1d imbi12d vy cv vw cv wceq vz cv vy cv cR wbr vz cv vw cv cR
      wbr vz cv cF cfv vy cv cF cfv cS wbr vz cv cF cfv vw cv cF cfv cS wbr vy
      cv vw cv vz cv cR breq2 vy cv vw cv wceq vy cv cF cfv vw cv cF cfv vz cv
      cF cfv cS vy cv vw cv cF fveq2 breq2d imbi12d rspc2va syl21anc cB cR wor
      cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy
      cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      wa wa vw cv cA wcel vz cv cA wcel vx cv vy cv cR wbr vx cv cF cfv vy cv
      cF cfv cS wbr wi vy cA wral vx cA wral vw cv vz cv cR wbr vw cv cF cfv vz
      cv cF cfv cS wbr wi cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv
      vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      w3a vz cv cA wcel vw cv cA wcel simprr cB cR wor cC cS wor wa cB cC cF wf
      cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral w3a vz cv cA wcel vw cv cA wcel simprl cB cR wor cC cS
      wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl3
      vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vw cv vz cv cR wbr
      vw cv cF cfv vz cv cF cfv cS wbr wi vw cv vy cv cR wbr vw cv cF cfv vy cv
      cF cfv cS wbr wi vx vy vw cv vz cv cA cA vx cv vw cv wceq vx cv vy cv cR
      wbr vw cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr vw cv cF cfv vy
      cv cF cfv cS wbr vx cv vw cv vy cv cR breq1 vx cv vw cv wceq vx cv cF cfv
      vw cv cF cfv vy cv cF cfv cS vx cv vw cv cF fveq2 breq1d imbi12d vy cv vz
      cv wceq vw cv vy cv cR wbr vw cv vz cv cR wbr vw cv cF cfv vy cv cF cfv
      cS wbr vw cv cF cfv vz cv cF cfv cS wbr vy cv vz cv vw cv cR breq2 vy cv
      vz cv wceq vy cv cF cfv vz cv cF cfv vw cv cF cfv cS vy cv vz cv cF fveq2
      breq2d imbi12d rspc2va syl21anc orim12d con3d cB cR wor cC cS wor wa cB
      cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr
      wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa cC cS wor
      vz cv cF cfv cC wcel vw cv cF cfv cC wcel vz cv cF cfv vw cv cF cfv wceq
      vz cv cF cfv vw cv cF cfv cS wbr vw cv cF cfv vz cv cF cfv cS wbr wo wn
      wb cB cR wor cC cS wor cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv
      cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv
      cA wcel wa simpl1r cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv
      vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      w3a vz cv cA wcel vw cv cA wcel wa wa cB cC cF wf vz cv cB wcel vz cv cF
      cfv cC wcel cB cC cF wf cA cB wss cB cR wor cC cS wor wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA
      wcel vw cv cA wcel wa simpl2l cB cR wor cC cS wor wa cB cC cF wf cA cB
      wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral
      vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa cA cB vz cv cB cC cF wf
      cA cB wss cB cR wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa
      simpl2r cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv
      cA wcel vw cv cA wcel simprl sseldd cB cC vz cv cF ffvelrn syl2anc cB cR
      wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv
      vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA
      wcel wa wa cB cC cF wf vw cv cB wcel vw cv cF cfv cC wcel cB cC cF wf cA
      cB wss cB cR wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa
      simpl2l cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv
      cA wcel vw cv cA wcel wa wa cA cB vw cv cB cC cF wf cA cB wss cB cR wor
      cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2r cB cR wor cC cS
      wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      simprr sseldd cB cC vw cv cF ffvelrn syl2anc cC vz cv cF cfv vw cv cF cfv
      cS sotrieq syl12anc cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv
      vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      w3a vz cv cA wcel vw cv cA wcel wa wa cB cR wor vz cv cB wcel vw cv cB
      wcel vz cv vw cv wceq vz cv vw cv cR wbr vw cv vz cv cR wbr wo wn wb cB
      cR wor cC cS wor cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv
      vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel
      wa simpl1l cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv
      cA wcel vw cv cA wcel wa wa cA cB vz cv cB cC cF wf cA cB wss cB cR wor
      cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2r cB cR wor cC cS
      wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      simprl sseldd cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv
      cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz
      cv cA wcel vw cv cA wcel wa wa cA cB vw cv cB cC cF wf cA cB wss cB cR
      wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi
      vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2r cB cR wor cC
      cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv
      cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      simprr sseldd cB vz cv vw cv cR sotrieq syl12anc 3imtr4d sylbid
      ralrimivva vz vw cA cF cA cima cF cA cres dff1o6 syl3anbrc cB cR wor cC
      cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv
      cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv vw cv cR wbr vz cv cF cA
      cres cfv vw cv cF cA cres cfv cS wbr wb vz vw cA cA cB cR wor cC cS wor
      wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv
      cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa vz
      cv vw cv cR wbr vz cv cF cfv vw cv cF cfv cS wbr vz cv cF cA cres cfv vw
      cv cF cA cres cfv cS wbr cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa
      vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA
      wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv vw cv cR wbr vz cv cF
      cfv vw cv cF cfv cS wbr cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa
      vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA
      wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv cA wcel vw cv cA wcel vx
      cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      vz cv vw cv cR wbr vz cv cF cfv vw cv cF cfv cS wbr wi cB cR wor cC cS
      wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      simprl cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA
      wcel vw cv cA wcel simprr cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa
      vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA
      wral vz cv cA wcel vw cv cA wcel wa simpl3 vx cv vy cv cR wbr vx cv cF
      cfv vy cv cF cfv cS wbr wi vz cv vw cv cR wbr vz cv cF cfv vw cv cF cfv
      cS wbr wi vz cv vy cv cR wbr vz cv cF cfv vy cv cF cfv cS wbr wi vx vy vz
      cv vw cv cA cA vx cv vz cv wceq vx cv vy cv cR wbr vz cv vy cv cR wbr vx
      cv cF cfv vy cv cF cfv cS wbr vz cv cF cfv vy cv cF cfv cS wbr vx cv vz
      cv vy cv cR breq1 vx cv vz cv wceq vx cv cF cfv vz cv cF cfv vy cv cF cfv
      cS vx cv vz cv cF fveq2 breq1d imbi12d vy cv vw cv wceq vz cv vy cv cR
      wbr vz cv vw cv cR wbr vz cv cF cfv vy cv cF cfv cS wbr vz cv cF cfv vw
      cv cF cfv cS wbr vy cv vw cv vz cv cR breq2 vy cv vw cv wceq vy cv cF cfv
      vw cv cF cfv vz cv cF cfv cS vy cv vw cv cF fveq2 breq2d imbi12d rspc2va
      syl21anc cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv
      cA wcel vw cv cA wcel wa wa vz cv cF cfv vw cv cF cfv wceq vw cv cF cfv
      vz cv cF cfv cS wbr wo wn vz cv vw cv wceq vw cv vz cv cR wbr wo wn vz cv
      cF cfv vw cv cF cfv cS wbr vz cv vw cv cR wbr cB cR wor cC cS wor wa cB
      cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr
      wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv vw
      cv wceq vw cv vz cv cR wbr wo vz cv cF cfv vw cv cF cfv wceq vw cv cF cfv
      vz cv cF cfv cS wbr wo cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx
      cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      w3a vz cv cA wcel vw cv cA wcel wa wa vz cv vw cv wceq vz cv cF cfv vw cv
      cF cfv wceq vw cv vz cv cR wbr vw cv cF cfv vz cv cF cfv cS wbr vz cv vw
      cv wceq vz cv cF cfv vw cv cF cfv wceq wi cB cR wor cC cS wor wa cB cC cF
      wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy
      cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa vz cv vw cv cF
      fveq2 a1i cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv
      cA wcel vw cv cA wcel wa wa vw cv cA wcel vz cv cA wcel vx cv vy cv cR
      wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vw cv vz cv
      cR wbr vw cv cF cfv vz cv cF cfv cS wbr wi cB cR wor cC cS wor wa cB cC
      cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi
      vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel simprr cB cR wor cC
      cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv
      cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      simprl cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel
      vw cv cA wcel wa simpl3 vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS
      wbr wi vw cv vz cv cR wbr vw cv cF cfv vz cv cF cfv cS wbr wi vw cv vy cv
      cR wbr vw cv cF cfv vy cv cF cfv cS wbr wi vx vy vw cv vz cv cA cA vx cv
      vw cv wceq vx cv vy cv cR wbr vw cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr vw cv cF cfv vy cv cF cfv cS wbr vx cv vw cv vy cv cR breq1 vx
      cv vw cv wceq vx cv cF cfv vw cv cF cfv vy cv cF cfv cS vx cv vw cv cF
      fveq2 breq1d imbi12d vy cv vz cv wceq vw cv vy cv cR wbr vw cv vz cv cR
      wbr vw cv cF cfv vy cv cF cfv cS wbr vw cv cF cfv vz cv cF cfv cS wbr vy
      cv vz cv vw cv cR breq2 vy cv vz cv wceq vy cv cF cfv vz cv cF cfv vw cv
      cF cfv cS vy cv vz cv cF fveq2 breq2d imbi12d rspc2va syl21anc orim12d
      con3d cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA
      wcel vw cv cA wcel wa wa cC cS wor vz cv cF cfv cC wcel vw cv cF cfv cC
      wcel vz cv cF cfv vw cv cF cfv cS wbr vz cv cF cfv vw cv cF cfv wceq vw
      cv cF cfv vz cv cF cfv cS wbr wo wn wb cB cR wor cC cS wor cB cC cF wf cA
      cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl1r cB cR wor cC cS
      wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF
      cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel wa wa
      cB cC cF wf vz cv cB wcel vz cv cF cfv cC wcel cB cC cF wf cA cB wss cB
      cR wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr
      wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2l cB cR wor
      cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy
      cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA wcel
      wa wa cA cB vz cv cB cC cF wf cA cB wss cB cR wor cC cS wor wa vx cv vy
      cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv
      cA wcel vw cv cA wcel wa simpl2r cB cR wor cC cS wor wa cB cC cF wf cA cB
      wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral
      vx cA wral w3a vz cv cA wcel vw cv cA wcel simprl sseldd cB cC vz cv cF
      ffvelrn syl2anc cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy
      cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a
      vz cv cA wcel vw cv cA wcel wa wa cB cC cF wf vw cv cB wcel vw cv cF cfv
      cC wcel cB cC cF wf cA cB wss cB cR wor cC cS wor wa vx cv vy cv cR wbr
      vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel
      vw cv cA wcel wa simpl2l cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa
      vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA
      wral w3a vz cv cA wcel vw cv cA wcel wa wa cA cB vw cv cB cC cF wf cA cB
      wss cB cR wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv
      cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2r cB
      cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF
      cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv
      cA wcel simprr sseldd cB cC vw cv cF ffvelrn syl2anc cC vz cv cF cfv vw
      cv cF cfv cS sotric syl12anc cB cR wor cC cS wor wa cB cC cF wf cA cB wss
      wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx
      cA wral w3a vz cv cA wcel vw cv cA wcel wa wa cB cR wor vz cv cB wcel vw
      cv cB wcel vz cv vw cv cR wbr vz cv vw cv wceq vw cv vz cv cR wbr wo wn
      wb cB cR wor cC cS wor cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv
      cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv
      cA wcel wa simpl1l cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv
      vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      w3a vz cv cA wcel vw cv cA wcel wa wa cA cB vz cv cB cC cF wf cA cB wss
      cB cR wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS
      wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2r cB cR
      wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv
      vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA
      wcel simprl sseldd cB cR wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv
      vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA wral vx cA wral
      w3a vz cv cA wcel vw cv cA wcel wa wa cA cB vw cv cB cC cF wf cA cB wss
      cB cR wor cC cS wor wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS
      wbr wi vy cA wral vx cA wral vz cv cA wcel vw cv cA wcel wa simpl2r cB cR
      wor cC cS wor wa cB cC cF wf cA cB wss wa vx cv vy cv cR wbr vx cv cF cfv
      vy cv cF cfv cS wbr wi vy cA wral vx cA wral w3a vz cv cA wcel vw cv cA
      wcel simprr sseldd cB vz cv vw cv cR sotric syl12anc 3imtr4d impbid vz cv
      cA wcel vw cv cA wcel wa vz cv cF cA cres cfv vw cv cF cA cres cfv cS wbr
      vz cv cF cfv vw cv cF cfv cS wbr wb cB cR wor cC cS wor wa cB cC cF wf cA
      cB wss wa vx cv vy cv cR wbr vx cv cF cfv vy cv cF cfv cS wbr wi vy cA
      wral vx cA wral w3a vz cv cA wcel vw cv cA wcel vz cv cF cA cres cfv vz
      cv cF cfv vw cv cF cA cres cfv vw cv cF cfv cS vz cv cA cF fvres vw cv cA
      cF fvres breqan12d adantl bitr4d ralrimivva vz vw cA cF cA cima cR cS cF
      cA cres df-isom sylanbrc 3expia impbid2 $.
  $}

  ${
    $d R x y a b $.  $d S x y a b $.  $d H x y a b $.  $d A x y a b $.
    $d B x y a b $.
    $( Infer isomorphism from one direction of an order proof for isomorphisms
       between strict orders.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    soisoi $p |- ( ( ( R Or A /\ S Po B ) /\ ( H : A -onto-> B /\
          A. x e. A A. y e. A ( x R y -> ( H ` x ) S ( H ` y ) ) ) ) ->
        H Isom R , S ( A , B ) ) $=
      cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr wi vy cA wral vx cA wral wa wa cA cB cH wf1o va cv vb cv cR
      wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA wral va cA wral cA cB cR cS
      cH wiso cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa cA cB cH wf1 cA cB
      cH wfo cA cB cH wf1o cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa cA cB
      cH wf va cv cH cfv vb cv cH cfv wceq va vb weq wi vb cA wral va cA wral
      cA cB cH wf1 cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa cA cB cH wfo cA
      cB cH wf cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral simprl cA cB cH fof syl
      cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cH cfv vb cv cH cfv
      wceq va vb weq wi va vb cA cA cA cR wor cB cS wpo wa cA cB cH wfo vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa
      wa va cv cA wcel vb cv cA wcel wa wa va vb weq va cv cH cfv vb cv cH cfv
      wceq cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA
      wcel wa wa va vb weq wn va cv vb cv cR wbr vb cv va cv cR wbr wo va cv cH
      cfv vb cv cH cfv wceq wn cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv
      cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa cA
      cR wor va cv cA wcel vb cv cA wcel wa va cv vb cv cR wbr vb cv va cv cR
      wbr wo va vb weq wn wb cA cR wor cB cS wpo cA cB cH wfo vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa simpll
      cA cR wor va cv cA wcel vb cv cA wcel wa wa va vb weq va cv vb cv cR wbr
      vb cv va cv cR wbr wo cA va cv vb cv cR sotrieq con2bid sylan cA cR wor
      cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa va
      cv vb cv cR wbr va cv cH cfv vb cv cH cfv wceq wn vb cv va cv cR wbr cA
      cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa
      wa va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr va cv cH cfv vb cv
      cH cfv wceq wn cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx
      cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa vx cv vy cv
      cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral va cv cA
      wcel vb cv cA wcel wa va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr
      wi cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy
      cv cH cfv cS wbr wi vy cA wral vx cA wral simprr va cv cA wcel vb cv cA
      wcel wa vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral
      vx cA wral va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wi vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi va cv vb cv cR wbr va cv
      cH cfv vb cv cH cfv cS wbr wi va cv vy cv cR wbr va cv cH cfv vy cv cH
      cfv cS wbr wi vx vy va cv vb cv cA cA vx va weq vx cv vy cv cR wbr va cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr va cv cH cfv vy cv cH cfv
      cS wbr vx cv va cv vy cv cR breq1 vx va weq vx cv cH cfv va cv cH cfv vy
      cv cH cfv cS vx cv va cv cH fveq2 breq1d imbi12d vy vb weq va cv vy cv cR
      wbr va cv vb cv cR wbr va cv cH cfv vy cv cH cfv cS wbr va cv cH cfv vb
      cv cH cfv cS wbr vy cv vb cv va cv cR breq2 vy vb weq vy cv cH cfv vb cv
      cH cfv va cv cH cfv cS vy cv vb cv cH fveq2 breq2d imbi12d rspc2va ancoms
      sylan cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA
      wcel wa wa va cv cH cfv vb cv cH cfv wceq va cv cH cfv vb cv cH cfv cS
      wbr cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA
      wcel wa wa cB cS wpo vb cv cH cfv cB wcel va cv cH cfv vb cv cH cfv wceq
      va cv cH cfv vb cv cH cfv cS wbr wn wi cA cR wor cB cS wpo cA cB cH wfo
      vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA
      wral wa va cv cA wcel vb cv cA wcel wa simpllr cA cR wor cB cS wpo wa cA
      cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA
      wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wf vb cv
      cA wcel vb cv cH cfv cB wcel cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy
      cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa
      va cv cA wcel vb cv cA wcel wa wa cA cB cH wfo cA cB cH wf cA cR wor cB
      cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa simplrl cA cB
      cH fof syl cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel
      vb cv cA wcel simprr cA cB vb cv cH ffvelrn syl2anc cB cS wpo vb cv cH
      cfv cB wcel wa va cv cH cfv vb cv cH cfv cS wbr wn va cv cH cfv vb cv cH
      cfv wceq vb cv cH cfv vb cv cH cfv cS wbr wn cB vb cv cH cfv cS poirr va
      cv cH cfv vb cv cH cfv wceq va cv cH cfv vb cv cH cfv cS wbr vb cv cH cfv
      vb cv cH cfv cS wbr va cv cH cfv vb cv cH cfv vb cv cH cfv cS breq1
      notbid syl5ibrcom syl2anc con2d syld cA cR wor cB cS wpo wa cA cB cH wfo
      vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA
      wral wa wa va cv cA wcel vb cv cA wcel wa wa vb cv va cv cR wbr vb cv cH
      cfv va cv cH cfv cS wbr va cv cH cfv vb cv cH cfv wceq wn cA cR wor cB cS
      wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wi vy cA wral vx cA wral wa wa vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa vb cv
      va cv cR wbr vb cv cH cfv va cv cH cfv cS wbr wi cA cR wor cB cS wpo wa
      cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA
      wral vx cA wral simprr vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral vb cv cA wcel va cv cA wcel vb cv va cv cR
      wbr vb cv cH cfv va cv cH cfv cS wbr wi vb cv cA wcel va cv cA wcel wa vx
      cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral
      vb cv va cv cR wbr vb cv cH cfv va cv cH cfv cS wbr wi vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr wi vb cv va cv cR wbr vb cv cH cfv va cv
      cH cfv cS wbr wi vb cv vy cv cR wbr vb cv cH cfv vy cv cH cfv cS wbr wi
      vx vy vb cv va cv cA cA vx vb weq vx cv vy cv cR wbr vb cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr vb cv cH cfv vy cv cH cfv cS wbr vx cv
      vb cv vy cv cR breq1 vx vb weq vx cv cH cfv vb cv cH cfv vy cv cH cfv cS
      vx cv vb cv cH fveq2 breq1d imbi12d vy va weq vb cv vy cv cR wbr vb cv va
      cv cR wbr vb cv cH cfv vy cv cH cfv cS wbr vb cv cH cfv va cv cH cfv cS
      wbr vy cv va cv vb cv cR breq2 vy va weq vy cv cH cfv va cv cH cfv vb cv
      cH cfv cS vy cv va cv cH fveq2 breq2d imbi12d rspc2va ancoms ancom2s
      sylan cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA
      wcel wa wa va cv cH cfv vb cv cH cfv wceq vb cv cH cfv va cv cH cfv cS
      wbr cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA
      wcel wa wa cB cS wpo vb cv cH cfv cB wcel va cv cH cfv vb cv cH cfv wceq
      vb cv cH cfv va cv cH cfv cS wbr wn wi cA cR wor cB cS wpo cA cB cH wfo
      vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA
      wral wa va cv cA wcel vb cv cA wcel wa simpllr cA cR wor cB cS wpo wa cA
      cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA
      wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wf vb cv
      cA wcel vb cv cH cfv cB wcel cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy
      cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa
      va cv cA wcel vb cv cA wcel wa wa cA cB cH wfo cA cB cH wf cA cR wor cB
      cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa simplrl cA cB
      cH fof syl cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel
      vb cv cA wcel simprr cA cB vb cv cH ffvelrn syl2anc cB cS wpo vb cv cH
      cfv cB wcel wa vb cv cH cfv va cv cH cfv cS wbr wn va cv cH cfv vb cv cH
      cfv wceq vb cv cH cfv vb cv cH cfv cS wbr wn cB vb cv cH cfv cS poirr va
      cv cH cfv vb cv cH cfv wceq vb cv cH cfv va cv cH cfv cS wbr vb cv cH cfv
      vb cv cH cfv cS wbr va cv cH cfv vb cv cH cfv vb cv cH cfv cS breq2
      notbid syl5ibrcom syl2anc con2d syld jaod sylbird con4d ralrimivva va vb
      cA cB cH dff13 sylanbrc cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv
      cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral simprl
      cA cB cH df-f1o sylanbrc cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv
      cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va
      cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb va vb cA cA cA cR wor
      cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa va
      cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr cA cR wor cB cS wpo wa
      cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA
      wral vx cA wral wa wa vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa va cv vb cv cR
      wbr va cv cH cfv vb cv cH cfv cS wbr wi cA cR wor cB cS wpo wa cA cB cH
      wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx
      cA wral simprr va cv cA wcel vb cv cA wcel wa vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral va cv vb cv cR wbr va cv
      cH cfv vb cv cH cfv cS wbr wi vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wi va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wi va
      cv vy cv cR wbr va cv cH cfv vy cv cH cfv cS wbr wi vx vy va cv vb cv cA
      cA vx va weq vx cv vy cv cR wbr va cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr va cv cH cfv vy cv cH cfv cS wbr vx cv va cv vy cv cR breq1 vx
      va weq vx cv cH cfv va cv cH cfv vy cv cH cfv cS vx cv va cv cH fveq2
      breq1d imbi12d vy vb weq va cv vy cv cR wbr va cv vb cv cR wbr va cv cH
      cfv vy cv cH cfv cS wbr va cv cH cfv vb cv cH cfv cS wbr vy cv vb cv va
      cv cR breq2 vy vb weq vy cv cH cfv vb cv cH cfv va cv cH cfv cS vy cv vb
      cv cH fveq2 breq2d imbi12d rspc2va ancoms sylan cA cR wor cB cS wpo wa cA
      cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA
      wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa va cv vb cv cR
      wbr wn va vb weq vb cv va cv cR wbr wo va cv cH cfv vb cv cH cfv cS wbr
      wn cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy
      cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa cA cR wor va cv cA wcel
      vb cv cA wcel wa va vb weq vb cv va cv cR wbr wo va cv vb cv cR wbr wn wb
      cA cR wor cB cS wpo cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wi vy cA wral vx cA wral wa simpll cA cR wor va cv cA wcel vb
      cv cA wcel wa wa va cv vb cv cR wbr va vb weq vb cv va cv cR wbr wo cA va
      cv vb cv cR sotric con2bid sylan cA cR wor cB cS wpo wa cA cB cH wfo vx
      cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral
      wa wa va cv cA wcel vb cv cA wcel wa wa va vb weq va cv cH cfv vb cv cH
      cfv cS wbr wn vb cv va cv cR wbr cA cR wor cB cS wpo wa cA cB cH wfo vx
      cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral
      wa wa va cv cA wcel vb cv cA wcel wa wa cB cS wpo vb cv cH cfv cB wcel va
      vb weq va cv cH cfv vb cv cH cfv cS wbr wn wi cA cR wor cB cS wpo cA cB
      cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral
      vx cA wral wa va cv cA wcel vb cv cA wcel wa simpllr cA cR wor cB cS wpo
      wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy
      cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wf vb
      cv cA wcel vb cv cH cfv cB wcel cA cR wor cB cS wpo wa cA cB cH wfo vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa
      wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wfo cA cB cH wf cA cR wor
      cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa simplrl cA cB
      cH fof syl cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel
      vb cv cA wcel simprr cA cB vb cv cH ffvelrn syl2anc cB cS wpo vb cv cH
      cfv cB wcel wa va cv cH cfv vb cv cH cfv cS wbr wn va vb weq vb cv cH cfv
      vb cv cH cfv cS wbr wn cB vb cv cH cfv cS poirr va vb weq va cv cH cfv vb
      cv cH cfv cS wbr vb cv cH cfv vb cv cH cfv cS wbr va vb weq va cv cH cfv
      vb cv cH cfv vb cv cH cfv cS va cv vb cv cH fveq2 breq1d notbid
      syl5ibrcom syl2anc cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA
      wcel vb cv cA wcel wa wa vb cv va cv cR wbr vb cv cH cfv va cv cH cfv cS
      wbr va cv cH cfv vb cv cH cfv cS wbr wn cA cR wor cB cS wpo wa cA cB cH
      wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx
      cA wral wa wa vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy
      cA wral vx cA wral va cv cA wcel vb cv cA wcel wa vb cv va cv cR wbr vb
      cv cH cfv va cv cH cfv cS wbr wi cA cR wor cB cS wpo wa cA cB cH wfo vx
      cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral
      simprr vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral
      vx cA wral vb cv cA wcel va cv cA wcel vb cv va cv cR wbr vb cv cH cfv va
      cv cH cfv cS wbr wi vb cv cA wcel va cv cA wcel wa vx cv vy cv cR wbr vx
      cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral vb cv va cv cR wbr
      vb cv cH cfv va cv cH cfv cS wbr wi vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr wi vb cv va cv cR wbr vb cv cH cfv va cv cH cfv cS wbr wi
      vb cv vy cv cR wbr vb cv cH cfv vy cv cH cfv cS wbr wi vx vy vb cv va cv
      cA cA vx vb weq vx cv vy cv cR wbr vb cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr vb cv cH cfv vy cv cH cfv cS wbr vx cv vb cv vy cv cR breq1
      vx vb weq vx cv cH cfv vb cv cH cfv vy cv cH cfv cS vx cv vb cv cH fveq2
      breq1d imbi12d vy va weq vb cv vy cv cR wbr vb cv va cv cR wbr vb cv cH
      cfv vy cv cH cfv cS wbr vb cv cH cfv va cv cH cfv cS wbr vy cv va cv vb
      cv cR breq2 vy va weq vy cv cH cfv va cv cH cfv vb cv cH cfv cS vy cv va
      cv cH fveq2 breq2d imbi12d rspc2va ancoms ancom2s sylan cA cR wor cB cS
      wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wi vy cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa cB cS
      wpo vb cv cH cfv cB wcel va cv cH cfv cB wcel vb cv cH cfv va cv cH cfv
      cS wbr va cv cH cfv vb cv cH cfv cS wbr wn wi cA cR wor cB cS wpo cA cB
      cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral
      vx cA wral wa va cv cA wcel vb cv cA wcel wa simpllr cA cR wor cB cS wpo
      wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy
      cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wf vb
      cv cA wcel vb cv cH cfv cB wcel cA cR wor cB cS wpo wa cA cB cH wfo vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa
      wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wfo cA cB cH wf cA cR wor
      cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa simplrl cA cB
      cH fof syl cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel
      vb cv cA wcel simprr cA cB vb cv cH ffvelrn syl2anc cA cR wor cB cS wpo
      wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy
      cA wral vx cA wral wa wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wf va
      cv cA wcel va cv cH cfv cB wcel cA cR wor cB cS wpo wa cA cB cH wfo vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa
      wa va cv cA wcel vb cv cA wcel wa wa cA cB cH wfo cA cB cH wf cA cR wor
      cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wi vy cA wral vx cA wral va cv cA wcel vb cv cA wcel wa simplrl cA cB
      cH fof syl cA cR wor cB cS wpo wa cA cB cH wfo vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wi vy cA wral vx cA wral wa wa va cv cA wcel
      vb cv cA wcel simprl cA cB va cv cH ffvelrn syl2anc cB cS wpo vb cv cH
      cfv cB wcel va cv cH cfv cB wcel wa wa vb cv cH cfv va cv cH cfv cS wbr
      va cv cH cfv vb cv cH cfv cS wbr wa wn vb cv cH cfv va cv cH cfv cS wbr
      va cv cH cfv vb cv cH cfv cS wbr wn wi cB vb cv cH cfv va cv cH cfv cS
      po2nr vb cv cH cfv va cv cH cfv cS wbr va cv cH cfv vb cv cH cfv cS wbr
      imnan sylibr syl12anc syld jaod sylbird impcon4bid ralrimivva va vb cA cB
      cR cS cH df-isom sylanbrc $.
  $}

  ${
    $d x y A $.  $d x y R $.
    $( Identity law for isomorphism.  Proposition 6.30(1) of [TakeutiZaring]
       p. 33.  (Contributed by NM, 27-Apr-2004.) $)
    isoid $p |- ( _I |` A ) Isom R , R ( A , A ) $=
      cA cA cR cR cid cA cres wiso cA cA cid cA cres wf1o vx cv vy cv cR wbr vx
      cv cid cA cres cfv vy cv cid cA cres cfv cR wbr wb vy cA wral vx cA wral
      cA f1oi vx cv vy cv cR wbr vx cv cid cA cres cfv vy cv cid cA cres cfv cR
      wbr wb vx vy cA vx cv cA wcel vy cv cA wcel wa vx cv cid cA cres cfv vy
      cv cid cA cres cfv cR wbr vx cv vy cv cR wbr vx cv cA wcel vy cv cA wcel
      vx cv cid cA cres cfv vx cv vy cv cid cA cres cfv vy cv cR cA vx cv
      fvresi cA vy cv fvresi breqan12d bicomd rgen2a vx vy cA cA cR cR cid cA
      cres df-isom mpbir2an $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d x y C $.  $d x y D $.  $d w x y z H $.
    $d w x y z R $.  $d w x y z S $.
    $( Converse law for isomorphism.  Proposition 6.30(2) of [TakeutiZaring]
       p. 33.  (Contributed by NM, 27-Apr-2004.) $)
    isocnv $p |- ( H Isom R , S ( A , B ) -> `' H Isom S , R ( B , A ) ) $=
      cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy
      cA wral vx cA wral wa cB cA cH ccnv wf1o vz cv vw cv cS wbr vz cv cH ccnv
      cfv vw cv cH ccnv cfv cR wbr wb vw cB wral vz cB wral wa cA cB cR cS cH
      wiso cB cA cS cR cH ccnv wiso cA cB cH wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral wa cB cA cH ccnv wf1o vz
      cv vw cv cS wbr vz cv cH ccnv cfv vw cv cH ccnv cfv cR wbr wb vw cB wral
      vz cB wral cA cB cH wf1o cB cA cH ccnv wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral cA cB cH f1ocnv adantr
      cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy
      cA wral vx cA wral wa vz cv vw cv cS wbr vz cv cH ccnv cfv vw cv cH ccnv
      cfv cR wbr wb vz vw cB cB cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wb vy cA wral vx cA wral wa vz cv cB wcel vw cv cB
      wcel wa wa vz cv cH ccnv cfv cH cfv vw cv cH ccnv cfv cH cfv cS wbr vz cv
      vw cv cS wbr vz cv cH ccnv cfv vw cv cH ccnv cfv cR wbr cA cB cH wf1o vz
      cv cB wcel vw cv cB wcel wa vz cv cH ccnv cfv cH cfv vw cv cH ccnv cfv cH
      cfv cS wbr vz cv vw cv cS wbr wb vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wb vy cA wral vx cA wral cA cB cH wf1o vz cv cB wcel vw cv cB
      wcel wa wa vz cv cH ccnv cfv cH cfv vz cv vw cv cH ccnv cfv cH cfv vw cv
      cS cA cB cH wf1o vz cv cB wcel vz cv cH ccnv cfv cH cfv vz cv wceq vw cv
      cB wcel cA cB vz cv cH f1ocnvfv2 adantrr cA cB cH wf1o vw cv cB wcel vw
      cv cH ccnv cfv cH cfv vw cv wceq vz cv cB wcel cA cB vw cv cH f1ocnvfv2
      adantrl breq12d adantlr cA cB cH wf1o cB cA cH ccnv wf vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral vz cv cB wcel
      vw cv cB wcel wa vz cv cH ccnv cfv cH cfv vw cv cH ccnv cfv cH cfv cS wbr
      vz cv cH ccnv cfv vw cv cH ccnv cfv cR wbr wb cA cB cH wf1o cB cA cH ccnv
      wf1o cB cA cH ccnv wf cA cB cH f1ocnv cB cA cH ccnv f1of syl cB cA cH
      ccnv wf vz cv cB wcel vw cv cB wcel wa vx cv vy cv cR wbr vx cv cH cfv vy
      cv cH cfv cS wbr wb vy cA wral vx cA wral vz cv cH ccnv cfv cH cfv vw cv
      cH ccnv cfv cH cfv cS wbr vz cv cH ccnv cfv vw cv cH ccnv cfv cR wbr wb
      cB cA cH ccnv wf vz cv cB wcel vw cv cB wcel wa wa vz cv cH ccnv cfv cA
      wcel vw cv cH ccnv cfv cA wcel wa vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr wb vy cA wral vx cA wral vz cv cH ccnv cfv cH cfv vw cv cH
      ccnv cfv cH cfv cS wbr vz cv cH ccnv cfv vw cv cH ccnv cfv cR wbr wb cB
      cA cH ccnv wf vz cv cB wcel vz cv cH ccnv cfv cA wcel vw cv cB wcel vw cv
      cH ccnv cfv cA wcel cB cA vz cv cH ccnv ffvelrn cB cA vw cv cH ccnv
      ffvelrn anim12dan vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb
      vz cv cH ccnv cfv cH cfv vw cv cH ccnv cfv cH cfv cS wbr vz cv cH ccnv
      cfv vw cv cH ccnv cfv cR wbr wb vz cv cH ccnv cfv cH cfv vy cv cH cfv cS
      wbr vz cv cH ccnv cfv vy cv cR wbr wb vx vy vz cv cH ccnv cfv vw cv cH
      ccnv cfv cA cA vx cv vz cv cH ccnv cfv wceq vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vz cv cH ccnv cfv vy cv cR wbr vz cv cH ccnv
      cfv cH cfv vy cv cH cfv cS wbr wb vz cv cH ccnv cfv cH cfv vy cv cH cfv
      cS wbr vz cv cH ccnv cfv vy cv cR wbr wb vx cv vz cv cH ccnv cfv wceq vx
      cv vy cv cR wbr vz cv cH ccnv cfv vy cv cR wbr vx cv cH cfv vy cv cH cfv
      cS wbr vz cv cH ccnv cfv cH cfv vy cv cH cfv cS wbr vx cv vz cv cH ccnv
      cfv vy cv cR breq1 vx cv vz cv cH ccnv cfv wceq vx cv cH cfv vz cv cH
      ccnv cfv cH cfv vy cv cH cfv cS vx cv vz cv cH ccnv cfv cH fveq2 breq1d
      bibi12d vz cv cH ccnv cfv vy cv cR wbr vz cv cH ccnv cfv cH cfv vy cv cH
      cfv cS wbr bicom syl6bb vy cv vw cv cH ccnv cfv wceq vz cv cH ccnv cfv cH
      cfv vy cv cH cfv cS wbr vz cv cH ccnv cfv cH cfv vw cv cH ccnv cfv cH cfv
      cS wbr vz cv cH ccnv cfv vy cv cR wbr vz cv cH ccnv cfv vw cv cH ccnv cfv
      cR wbr vy cv vw cv cH ccnv cfv wceq vy cv cH cfv vw cv cH ccnv cfv cH cfv
      vz cv cH ccnv cfv cH cfv cS vy cv vw cv cH ccnv cfv cH fveq2 breq2d vy cv
      vw cv cH ccnv cfv vz cv cH ccnv cfv cR breq2 bibi12d rspc2va sylan an32s
      sylanl1 bitr3d ralrimivva jca vx vy cA cB cR cS cH df-isom vz vw cB cA cS
      cR cH ccnv df-isom 3imtr4i $.

    $( Converse law for isomorphism.  (Contributed by Mario Carneiro,
       30-Jan-2014.) $)
    isocnv2 $p |- ( H Isom R , S ( A , B ) <->
                    H Isom `' R , `' S ( A , B ) ) $=
      cA cB cH wf1o vy cv vx cv cR wbr vy cv cH cfv vx cv cH cfv cS wbr wb vx
      cA wral vy cA wral wa cA cB cH wf1o vx cv vy cv cR ccnv wbr vx cv cH cfv
      vy cv cH cfv cS ccnv wbr wb vy cA wral vx cA wral wa cA cB cR cS cH wiso
      cA cB cR ccnv cS ccnv cH wiso vy cv vx cv cR wbr vy cv cH cfv vx cv cH
      cfv cS wbr wb vx cA wral vy cA wral vx cv vy cv cR ccnv wbr vx cv cH cfv
      vy cv cH cfv cS ccnv wbr wb vy cA wral vx cA wral cA cB cH wf1o vy cv vx
      cv cR wbr vy cv cH cfv vx cv cH cfv cS wbr wb vx cA wral vy cA wral vy cv
      vx cv cR wbr vy cv cH cfv vx cv cH cfv cS wbr wb vy cA wral vx cA wral vx
      cv vy cv cR ccnv wbr vx cv cH cfv vy cv cH cfv cS ccnv wbr wb vy cA wral
      vx cA wral vy cv vx cv cR wbr vy cv cH cfv vx cv cH cfv cS wbr wb vy vx
      cA cA ralcom vx cv vy cv cR ccnv wbr vx cv cH cfv vy cv cH cfv cS ccnv
      wbr wb vy cv vx cv cR wbr vy cv cH cfv vx cv cH cfv cS wbr wb vx vy cA cA
      vx cv vy cv cR ccnv wbr vy cv vx cv cR wbr vx cv cH cfv vy cv cH cfv cS
      ccnv wbr vy cv cH cfv vx cv cH cfv cS wbr vx cv vy cv cR vx vex vy vex
      brcnv vx cv cH cfv vy cv cH cfv cS vx cv cH fvex vy cv cH fvex brcnv
      bibi12i 2ralbii bitr4i anbi2i vy vx cA cB cR cS cH df-isom vx vy cA cB cR
      ccnv cS ccnv cH df-isom 3bitr4i $.

    isocnv3.1 $e |- C = ( ( A X. A ) \ R ) $.
    isocnv3.2 $e |- D = ( ( B X. B ) \ S ) $.
    $( Complementation law for isomorphism.  (Contributed by Mario Carneiro,
       9-Sep-2015.) $)
    isocnv3 $p |- ( H Isom R , S ( A , B ) <-> H Isom C , D ( A , B ) ) $=
      cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy
      cA wral vx cA wral wa cA cB cH wf1o vx cv vy cv cC wbr vx cv cH cfv vy cv
      cH cfv cD wbr wb vy cA wral vx cA wral wa cA cB cR cS cH wiso cA cB cC cD
      cH wiso cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wb vy cA wral vx cA wral vx cv vy cv cC wbr vx cv cH cfv vy cv cH cfv cD
      wbr wb vy cA wral vx cA wral cA cB cH wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vx cv vy cv cC wbr vx cv cH cfv vy cv cH cfv
      cD wbr wb vx vy cA cA cA cB cH wf1o vx cv cA wcel vy cv cA wcel wa wa vx
      cv vy cv cC wbr vx cv cH cfv vy cv cH cfv cD wbr wb vx cv vy cv cR wbr wn
      vx cv cH cfv vy cv cH cfv cS wbr wn wb vx cv vy cv cR wbr vx cv cH cfv vy
      cv cH cfv cS wbr wb cA cB cH wf1o vx cv cA wcel vy cv cA wcel wa wa vx cv
      vy cv cC wbr vx cv vy cv cR wbr wn vx cv cH cfv vy cv cH cfv cD wbr vx cv
      cH cfv vy cv cH cfv cS wbr wn vx cv cA wcel vy cv cA wcel wa vx cv vy cv
      cC wbr vx cv vy cv cR wbr wn wb cA cB cH wf1o vx cv cA wcel vy cv cA wcel
      wa vx cv vy cv cA cA cxp wbr vx cv vy cv cC wbr vx cv vy cv cR wbr wn wb
      vx cv vy cv cA cA brxp vx cv vy cv cC wbr vx cv vy cv cA cA cxp wbr vx cv
      vy cv cR wbr wn vx cv vy cv cC wbr vx cv vy cv cA cA cxp cR cdif wbr vx
      cv vy cv cA cA cxp wbr vx cv vy cv cR wbr wn wa vx cv vy cv cC cA cA cxp
      cR cdif isocnv3.1 breqi vx cv vy cv cA cA cxp cR brdif bitri baib sylbir
      adantl cA cB cH wf1o vx cv cA wcel vy cv cA wcel wa wa vx cv cH cfv vy cv
      cH cfv cB cB cxp wbr vx cv cH cfv vy cv cH cfv cD wbr vx cv cH cfv vy cv
      cH cfv cS wbr wn wb cA cB cH wf1o cA cB cH wf vx cv cA wcel vy cv cA wcel
      wa vx cv cH cfv vy cv cH cfv cB cB cxp wbr cA cB cH f1of cA cB cH wf vx
      cv cA wcel vy cv cA wcel wa wa vx cv cH cfv cB wcel vy cv cH cfv cB wcel
      wa vx cv cH cfv vy cv cH cfv cB cB cxp wbr cA cB cH wf vx cv cA wcel vx
      cv cH cfv cB wcel vy cv cA wcel vy cv cH cfv cB wcel cA cB vx cv cH
      ffvelrn cA cB vy cv cH ffvelrn anim12dan vx cv cH cfv vy cv cH cfv cB cB
      brxp sylibr sylan vx cv cH cfv vy cv cH cfv cD wbr vx cv cH cfv vy cv cH
      cfv cB cB cxp wbr vx cv cH cfv vy cv cH cfv cS wbr wn vx cv cH cfv vy cv
      cH cfv cD wbr vx cv cH cfv vy cv cH cfv cB cB cxp cS cdif wbr vx cv cH
      cfv vy cv cH cfv cB cB cxp wbr vx cv cH cfv vy cv cH cfv cS wbr wn wa vx
      cv cH cfv vy cv cH cfv cD cB cB cxp cS cdif isocnv3.2 breqi vx cv cH cfv
      vy cv cH cfv cB cB cxp cS brdif bitri baib syl bibi12d vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr notbi syl6rbbr 2ralbidva pm5.32i vx vy
      cA cB cR cS cH df-isom vx vy cA cB cC cD cH df-isom 3bitr4i $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d H x y $.  $d R x y $.  $d S x y $.
    $( An isomorphism from one well-order to another can be restricted on
       either well-order.  (Contributed by Mario Carneiro, 15-Jan-2013.) $)
    isores2 $p |- ( H Isom R , S ( A , B ) <->
                      H Isom R , ( S i^i ( B X. B ) ) ( A , B ) ) $=
      cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy
      cA wral vx cA wral wa cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS cB cB cxp cin wbr wb vy cA wral vx cA wral wa cA cB cR cS cH
      wiso cA cB cR cS cB cB cxp cin cH wiso cA cB cH wf1o vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS cB cB cxp cin wbr wb vy cA wral vx cA
      wral cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb
      vy cA wral vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS cB cB cxp cin
      wbr wb vy cA wral vx cA cA cB cH wf1o vx cv cA wcel wa vx cv vy cv cR wbr
      vx cv cH cfv vy cv cH cfv cS wbr wb vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS cB cB cxp cin wbr wb vy cA cA cB cH wf1o vx cv cA wcel wa vy cv
      cA wcel wa vx cv cH cfv vy cv cH cfv cS wbr vx cv cH cfv vy cv cH cfv cS
      cB cB cxp cin wbr vx cv vy cv cR wbr cA cB cH wf1o vx cv cA wcel vy cv cA
      wcel vx cv cH cfv vy cv cH cfv cS wbr vx cv cH cfv vy cv cH cfv cS cB cB
      cxp cin wbr wb cA cB cH wf1o cA cB cH wf vx cv cA wcel vy cv cA wcel wa
      vx cv cH cfv vy cv cH cfv cS wbr vx cv cH cfv vy cv cH cfv cS cB cB cxp
      cin wbr wb cA cB cH f1of cA cB cH wf vx cv cA wcel vy cv cA wcel wa wa vx
      cv cH cfv cB wcel vy cv cH cfv cB wcel vx cv cH cfv vy cv cH cfv cS wbr
      vx cv cH cfv vy cv cH cfv cS cB cB cxp cin wbr wb cA cB cH wf vx cv cA
      wcel vx cv cH cfv cB wcel vy cv cA wcel cA cB vx cv cH ffvelrn adantrr cA
      cB cH wf vy cv cA wcel vy cv cH cfv cB wcel vx cv cA wcel cA cB vy cv cH
      ffvelrn adantrl vx cv cH cfv vy cv cH cfv cB cB cS brinxp syl2anc sylan
      anassrs bibi2d ralbidva ralbidva pm5.32i vx vy cA cB cR cS cH df-isom vx
      vy cA cB cR cS cB cB cxp cin cH df-isom 3bitr4i $.
  $}

  ${
    $( An isomorphism from one well-order to another can be restricted on
       either well-order.  (Contributed by Mario Carneiro, 15-Jan-2013.) $)
    isores1 $p |- ( H Isom R , S ( A , B ) <->
                      H Isom ( R i^i ( A X. A ) ) , S ( A , B ) ) $=
      cA cB cR cS cH wiso cA cB cR cA cA cxp cin cS cH wiso cA cB cR cS cH wiso
      cA cB cR cA cA cxp cin cS cH ccnv ccnv wiso cA cB cR cA cA cxp cin cS cH
      wiso cA cB cR cS cH wiso cB cA cS cR cA cA cxp cin cH ccnv wiso cA cB cR
      cA cA cxp cin cS cH ccnv ccnv wiso cA cB cR cS cH wiso cB cA cS cR cH
      ccnv wiso cB cA cS cR cA cA cxp cin cH ccnv wiso cA cB cR cS cH isocnv cB
      cA cS cR cH ccnv isores2 sylib cB cA cS cR cA cA cxp cin cH ccnv isocnv
      syl cA cB cR cS cH wiso cA cB cH wf1o cH wrel cA cB cR cA cA cxp cin cS
      cH ccnv ccnv wiso cA cB cR cA cA cxp cin cS cH wiso wb cA cB cR cS cH
      isof1o cA cB cH f1orel cH wrel cH ccnv ccnv cH wceq cA cB cR cA cA cxp
      cin cS cH ccnv ccnv wiso cA cB cR cA cA cxp cin cS cH wiso wb cH dfrel2
      cA cB cR cA cA cxp cin cS cH cH ccnv ccnv isoeq1 sylbi 3syl mpbid cA cB
      cR cA cA cxp cin cS cH wiso cA cB cR cS cH ccnv ccnv wiso cA cB cR cS cH
      wiso cA cB cR cA cA cxp cin cS cH wiso cB cA cS cR cH ccnv wiso cA cB cR
      cS cH ccnv ccnv wiso cA cB cR cA cA cxp cin cS cH wiso cB cA cS cR cA cA
      cxp cin cH ccnv wiso cB cA cS cR cH ccnv wiso cA cB cR cA cA cxp cin cS
      cH isocnv cB cA cS cR cH ccnv isores2 sylibr cB cA cS cR cH ccnv isocnv
      syl cA cB cR cA cA cxp cin cS cH wiso cA cB cH wf1o cH wrel cA cB cR cS
      cH ccnv ccnv wiso cA cB cR cS cH wiso wb cA cB cR cA cA cxp cin cS cH
      isof1o cA cB cH f1orel cH wrel cH ccnv ccnv cH wceq cA cB cR cS cH ccnv
      ccnv wiso cA cB cR cS cH wiso wb cH dfrel2 cA cB cR cS cH cH ccnv ccnv
      isoeq1 sylbi 3syl mpbid impbii $.
  $}

  ${
    $d H a b c $.  $d R a b c $.  $d S a b c $.  $d K a b c $.  $d A a b c $.
    $d B a b c $.  $d X a b c $.
    $( Induced isomorphism on a subset.  (Contributed by Stefan O'Rear,
       5-Nov-2014.) $)
    isores3 $p |- ( ( H Isom R , S ( A , B ) /\ K C_ A /\ X = ( H " K ) ) ->
        ( H |` K ) Isom R , S ( K , X ) ) $=
      cA cB cR cS cH wiso cK cA wss cX cH cK cima wceq cK cX cR cS cH cK cres
      wiso cA cB cR cS cH wiso cK cA wss wa cK cX cR cS cH cK cres wiso cX cH
      cK cima wceq cK cH cK cima cR cS cH cK cres wiso cK cA wss cA cB cR cS cH
      wiso cK cH cK cima cR cS cH cK cres wiso cK cA wss cA cB cH wf1o va cv vb
      cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA wral va cA wral wa cK
      cH cK cima cH cK cres wf1o va cv vb cv cR wbr va cv cH cK cres cfv vb cv
      cH cK cres cfv cS wbr wb vb cK wral va cK wral wa cA cB cR cS cH wiso cK
      cH cK cima cR cS cH cK cres wiso cK cA wss cA cB cH wf1o cK cH cK cima cH
      cK cres wf1o va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA
      wral va cA wral va cv vb cv cR wbr va cv cH cK cres cfv vb cv cH cK cres
      cfv cS wbr wb vb cK wral va cK wral cA cB cH wf1o cA cB cH wf1 cK cA wss
      cK cH cK cima cH cK cres wf1o cA cB cH f1of1 cA cB cH wf1 cK cA wss cK cH
      cK cima cH cK cres wf1o cA cB cK cH f1ores expcom syl5 cK cA wss va cv vb
      cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA wral va cA wral va cv
      vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA wral va cK wral va
      cv vb cv cR wbr va cv cH cK cres cfv vb cv cH cK cres cfv cS wbr wb vb cK
      wral va cK wral va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb
      cA wral va cK cA ssralv cK cA wss va cv vb cv cR wbr va cv cH cfv vb cv
      cH cfv cS wbr wb vb cA wral va cv vb cv cR wbr va cv cH cK cres cfv vb cv
      cH cK cres cfv cS wbr wb vb cK wral va cK cK cA wss va cv cK wcel wa va
      cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA wral va cv vb
      cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cK wral va cv vb cv cR
      wbr va cv cH cK cres cfv vb cv cH cK cres cfv cS wbr wb vb cK wral cK cA
      wss va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cA wral va
      cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cK wral wi va cv
      cK wcel va cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb vb cK cA
      ssralv adantr cK cA wss va cv cK wcel wa va cv vb cv cR wbr va cv cH cfv
      vb cv cH cfv cS wbr wb va cv vb cv cR wbr va cv cH cK cres cfv vb cv cH
      cK cres cfv cS wbr wb vb cK cK cA wss va cv cK wcel wa vb cv cK wcel wa
      va cv vb cv cR wbr va cv cH cK cres cfv vb cv cH cK cres cfv cS wbr wb va
      cv vb cv cR wbr va cv cH cfv vb cv cH cfv cS wbr wb cK cA wss va cv cK
      wcel wa vb cv cK wcel wa va cv cH cK cres cfv vb cv cH cK cres cfv cS wbr
      va cv cH cfv vb cv cH cfv cS wbr va cv vb cv cR wbr va cv cK wcel vb cv
      cK wcel va cv cH cK cres cfv vb cv cH cK cres cfv cS wbr va cv cH cfv vb
      cv cH cfv cS wbr wb cK cA wss va cv cK wcel vb cv cK wcel va cv cH cK
      cres cfv va cv cH cfv vb cv cH cK cres cfv vb cv cH cfv cS va cv cK cH
      fvres vb cv cK cH fvres breqan12d adantll bibi2d biimprd ralimdva syld
      ralimdva syld anim12d va vb cA cB cR cS cH df-isom va vb cK cH cK cima cR
      cS cH cK cres df-isom 3imtr4g impcom cK cX cH cK cima cR cS cH cK cres
      isoeq5 syl5ibrcom 3impia $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d x y z w R $.
    $d x y z w S $.  $d x y z w T $.  $d x y z w G $.  $d x y z w H $.
    $( Composition (transitive) law for isomorphism.  Proposition 6.30(3) of
       [TakeutiZaring] p. 33.  (Contributed by NM, 27-Apr-2004.)  (Proof
       shortened by Mario Carneiro, 5-Dec-2016.) $)
    isotr $p |- ( ( H Isom R , S ( A , B ) /\ G Isom S , T ( B , C ) ) ->
               ( G o. H ) Isom R , T ( A , C ) ) $=
      cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy
      cA wral vx cA wral wa cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv
      cG cfv cT wbr wb vw cB wral vz cB wral wa wa cA cC cG cH ccom wf1o vx cv
      vy cv cR wbr vx cv cG cH ccom cfv vy cv cG cH ccom cfv cT wbr wb vy cA
      wral vx cA wral wa cA cB cR cS cH wiso cB cC cS cT cG wiso wa cA cC cR cT
      cG cH ccom wiso cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wb vy cA wral vx cA wral wa cB cC cG wf1o vz cv vw cv cS wbr
      vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa wa cA cC cG
      cH ccom wf1o vx cv vy cv cR wbr vx cv cG cH ccom cfv vy cv cG cH ccom cfv
      cT wbr wb vy cA wral vx cA wral cB cC cG wf1o vz cv vw cv cS wbr vz cv cG
      cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa cB cC cG wf1o cA cB
      cH wf1o cA cC cG cH ccom wf1o cA cB cH wf1o vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral wa cB cC cG wf1o vz cv
      vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral
      simpl cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr
      wb vy cA wral vx cA wral simpl cA cB cC cG cH f1oco syl2anr cA cB cH wf1o
      vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA
      wral wa cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr
      wb vw cB wral vz cB wral wa vx cv vy cv cR wbr vx cv cG cH ccom cfv vy cv
      cG cH ccom cfv cT wbr wb vy cA wral vx cA wral cA cB cH wf1o cB cC cG
      wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz
      cB wral wa vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA
      wral vx cA wral vx cv vy cv cR wbr vx cv cG cH ccom cfv vy cv cG cH ccom
      cfv cT wbr wb vy cA wral vx cA wral cA cB cH wf1o cB cC cG wf1o vz cv vw
      cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa wa
      vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA
      wral vx cv vy cv cR wbr vx cv cG cH ccom cfv vy cv cG cH ccom cfv cT wbr
      wb vy cA wral vx cA wral cA cB cH wf1o cB cC cG wf1o vz cv vw cv cS wbr
      vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa wa vx cv vy
      cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vx cv vy cv cR wbr vx cv cG
      cH ccom cfv vy cv cG cH ccom cfv cT wbr wb vx vy cA cA cA cB cH wf1o cB
      cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB
      wral vz cB wral wa wa vx cv cA wcel vy cv cA wcel wa wa vx cv cH cfv vy
      cv cH cfv cS wbr vx cv cG cH ccom cfv vy cv cG cH ccom cfv cT wbr vx cv
      vy cv cR wbr cA cB cH wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv
      vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA
      wcel wa wa vx cv cH cfv vy cv cH cfv cS wbr vx cv cH cfv cG cfv vy cv cH
      cfv cG cfv cT wbr vx cv cG cH ccom cfv vy cv cG cH ccom cfv cT wbr cA cB
      cH wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr
      wb vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA wcel wa wa vx cv cH
      cfv cB wcel vy cv cH cfv cB wcel vz cv vw cv cS wbr vz cv cG cfv vw cv cG
      cfv cT wbr wb vw cB wral vz cB wral vx cv cH cfv vy cv cH cfv cS wbr vx
      cv cH cfv cG cfv vy cv cH cfv cG cfv cT wbr wb cA cB cH wf1o cB cC cG
      wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz
      cB wral wa wa vx cv cA wcel vy cv cA wcel wa wa cA cB cH wf vx cv cA wcel
      vx cv cH cfv cB wcel cA cB cH wf1o cA cB cH wf cB cC cG wf1o vz cv vw cv
      cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa vx cv
      cA wcel vy cv cA wcel wa cA cB cH f1of ad2antrr cA cB cH wf1o cB cC cG
      wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz
      cB wral wa wa vx cv cA wcel vy cv cA wcel simprl cA cB vx cv cH ffvelrn
      syl2anc cA cB cH wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv
      cG cfv cT wbr wb vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA wcel
      wa wa cA cB cH wf vy cv cA wcel vy cv cH cfv cB wcel cA cB cH wf1o cA cB
      cH wf cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr
      wb vw cB wral vz cB wral wa vx cv cA wcel vy cv cA wcel wa cA cB cH f1of
      ad2antrr cA cB cH wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw
      cv cG cfv cT wbr wb vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA
      wcel simprr cA cB vy cv cH ffvelrn syl2anc cA cB cH wf1o cB cC cG wf1o vz
      cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB wral
      vx cv cA wcel vy cv cA wcel wa simplrr vz cv vw cv cS wbr vz cv cG cfv vw
      cv cG cfv cT wbr wb vx cv cH cfv vy cv cH cfv cS wbr vx cv cH cfv cG cfv
      vy cv cH cfv cG cfv cT wbr wb vx cv cH cfv vw cv cS wbr vx cv cH cfv cG
      cfv vw cv cG cfv cT wbr wb vz vw vx cv cH cfv vy cv cH cfv cB cB vz cv vx
      cv cH cfv wceq vz cv vw cv cS wbr vx cv cH cfv vw cv cS wbr vz cv cG cfv
      vw cv cG cfv cT wbr vx cv cH cfv cG cfv vw cv cG cfv cT wbr vz cv vx cv
      cH cfv vw cv cS breq1 vz cv vx cv cH cfv wceq vz cv cG cfv vx cv cH cfv
      cG cfv vw cv cG cfv cT vz cv vx cv cH cfv cG fveq2 breq1d bibi12d vw cv
      vy cv cH cfv wceq vx cv cH cfv vw cv cS wbr vx cv cH cfv vy cv cH cfv cS
      wbr vx cv cH cfv cG cfv vw cv cG cfv cT wbr vx cv cH cfv cG cfv vy cv cH
      cfv cG cfv cT wbr vw cv vy cv cH cfv vx cv cH cfv cS breq2 vw cv vy cv cH
      cfv wceq vw cv cG cfv vy cv cH cfv cG cfv vx cv cH cfv cG cfv cT vw cv vy
      cv cH cfv cG fveq2 breq2d bibi12d rspc2va syl21anc cA cB cH wf1o cB cC cG
      wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz
      cB wral wa wa vx cv cA wcel vy cv cA wcel wa wa vx cv cG cH ccom cfv vx
      cv cH cfv cG cfv vy cv cG cH ccom cfv vy cv cH cfv cG cfv cT cA cB cH
      wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb
      vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA wcel wa wa cA cB cH wf
      vx cv cA wcel vx cv cG cH ccom cfv vx cv cH cfv cG cfv wceq cA cB cH wf1o
      cA cB cH wf cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT
      wbr wb vw cB wral vz cB wral wa vx cv cA wcel vy cv cA wcel wa cA cB cH
      f1of ad2antrr cA cB cH wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv
      vw cv cG cfv cT wbr wb vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA
      wcel simprl cA cB vx cv cG cH fvco3 syl2anc cA cB cH wf1o cB cC cG wf1o
      vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB wral vz cB
      wral wa wa vx cv cA wcel vy cv cA wcel wa wa cA cB cH wf vy cv cA wcel vy
      cv cG cH ccom cfv vy cv cH cfv cG cfv wceq cA cB cH wf1o cA cB cH wf cB
      cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb vw cB
      wral vz cB wral wa vx cv cA wcel vy cv cA wcel wa cA cB cH f1of ad2antrr
      cA cB cH wf1o cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv
      cT wbr wb vw cB wral vz cB wral wa wa vx cv cA wcel vy cv cA wcel simprr
      cA cB vy cv cG cH fvco3 syl2anc breq12d bitr4d bibi2d 2ralbidva biimpd
      impancom imp jca cA cB cR cS cH wiso cA cB cH wf1o vx cv vy cv cR wbr vx
      cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral wa cB cC cS cT cG
      wiso cB cC cG wf1o vz cv vw cv cS wbr vz cv cG cfv vw cv cG cfv cT wbr wb
      vw cB wral vz cB wral wa vx vy cA cB cR cS cH df-isom vz vw cB cC cS cT
      cG df-isom anbi12i vx vy cA cC cR cT cG cH ccom df-isom 3imtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $d x y C $.  $d x y D $.
    $( Isomorphisms preserve minimal elements.  Note that ` ( ``' R " { D } ) `
       is Takeuti and Zaring's idiom for the initial segment
       ` { x | x R D } ` .  Proposition 6.31(1) of [TakeutiZaring] p. 33.
       (Contributed by NM, 19-Apr-2004.) $)
    isomin $p |- ( ( H Isom R , S ( A , B ) /\ ( C C_ A /\ D e. A ) ) ->
               ( ( C i^i ( `' R " { D } ) ) = (/) <->
               ( ( H " C ) i^i ( `' S " { ( H ` D ) } ) ) = (/) ) ) $=
      cA cB cR cS cH wiso cC cA wss cD cA wcel wa wa cC cR ccnv cD csn cima cin
      c0 wceq cH cC cima cS ccnv cD cH cfv csn cima cin c0 wceq cA cB cR cS cH
      wiso cC cA wss cD cA wcel wa wa cH cC cima cS ccnv cD cH cfv csn cima cin
      c0 wceq cC cR ccnv cD csn cima cin c0 wceq cH cC cima cS ccnv cD cH cfv
      csn cima cin c0 wceq wn vy cv cH cC cima cS ccnv cD cH cfv csn cima cin
      wcel vy wex cA cB cR cS cH wiso cC cA wss cD cA wcel wa wa cC cR ccnv cD
      csn cima cin c0 wceq wn vy cH cC cima cS ccnv cD cH cfv csn cima cin neq0
      cA cB cR cS cH wiso cC cA wss cD cA wcel wa wa vy cv cH cC cima cS ccnv
      cD cH cfv csn cima cin wcel cC cR ccnv cD csn cima cin c0 wceq wn vy cA
      cB cR cS cH wiso cC cA wss cD cA wcel wa wa vy cv cH cC cima cS ccnv cD
      cH cfv csn cima cin wcel vx cv cR ccnv cD csn cima wcel vx cC wrex cC cR
      ccnv cD csn cima cin c0 wceq wn cA cB cR cS cH wiso cC cA wss cD cA wcel
      wa wa vy cv cH cC cima cS ccnv cD cH cfv csn cima cin wcel vx cv cH cfv
      vy cv wceq vy cv cD cH cfv cS wbr wa vx cC wrex vx cv cR ccnv cD csn cima
      wcel vx cC wrex cA cB cR cS cH wiso cC cA wss vy cv cH cC cima cS ccnv cD
      cH cfv csn cima cin wcel vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr
      wa vx cC wrex wb cD cA wcel cA cB cR cS cH wiso cC cA wss wa vy cv cH cC
      cima wcel vy cv cS ccnv cD cH cfv csn cima wcel wa vx cv cH cfv vy cv
      wceq vx cC wrex vy cv cD cH cfv cS wbr wa vy cv cH cC cima cS ccnv cD cH
      cfv csn cima cin wcel vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa
      vx cC wrex cA cB cR cS cH wiso cC cA wss wa vy cv cH cC cima wcel vx cv
      cH cfv vy cv wceq vx cC wrex vy cv cS ccnv cD cH cfv csn cima wcel vy cv
      cD cH cfv cS wbr cA cB cR cS cH wiso cC cA wss wa vx cv cH cfv vy cv wceq
      vx cC wrex vx cv vy cv cH wbr vx cC wrex vy cv cH cC cima wcel cA cB cR
      cS cH wiso cC cA wss wa vx cv cH cfv vy cv wceq vx cv vy cv cH wbr vx cC
      cA cB cR cS cH wiso cC cA wss vx cv cC wcel vx cv cH cfv vy cv wceq vx cv
      vy cv cH wbr wb cC cA wss vx cv cC wcel vx cv cA wcel cA cB cR cS cH wiso
      vx cv cH cfv vy cv wceq vx cv vy cv cH wbr wb cC cA vx cv ssel cA cB cR
      cS cH wiso cA cB cH wf1o cH cA wfn vx cv cA wcel vx cv cH cfv vy cv wceq
      vx cv vy cv cH wbr wb wi cA cB cR cS cH isof1o cA cB cH f1ofn cH cA wfn
      vx cv cA wcel vx cv cH cfv vy cv wceq vx cv vy cv cH wbr wb cA vx cv vy
      cv cH fnbrfvb ex 3syl syl9r imp31 rexbidva vx vy cv cH cC vy vex elima
      syl6rbbr cD cH cfv cvv wcel vy cv cS ccnv cD cH cfv csn cima wcel vy cv
      cD cH cfv cS wbr wb cA cB cR cS cH wiso cC cA wss wa cD cH fvex cS cD cH
      cfv vy cv cvv vy vex eliniseg mp1i anbi12d vy cv cH cC cima cS ccnv cD cH
      cfv csn cima elin vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr vx cC
      r19.41v 3bitr4g adantrr cA cB cR cS cH wiso cC cA wss cD cA wcel wa wa vx
      cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx cv cR ccnv cD csn cima
      wcel vx cC cA cB cR cS cH wiso cC cA wss cD cA wcel vx cv cC wcel vx cv
      cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx cv cR ccnv cD csn cima
      wcel wi wi cA cB cR cS cH wiso cC cA wss vx cv cC wcel cD cA wcel vx cv
      cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx cv cR ccnv cD csn cima
      wcel wi cC cA wss vx cv cC wcel vx cv cA wcel cA cB cR cS cH wiso cD cA
      wcel vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx cv cR ccnv cD
      csn cima wcel wi wi cC cA vx cv ssel cA cB cR cS cH wiso vx cv cA wcel cD
      cA wcel vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx cv cR ccnv
      cD csn cima wcel wi vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx
      cv cR ccnv cD csn cima wcel cA cB cR cS cH wiso vx cv cA wcel cD cA wcel
      wa wa vx cv cH cfv cD cH cfv cS wbr vx cv cH cfv vy cv wceq vx cv cH cfv
      cD cH cfv cS wbr vy cv cD cH cfv cS wbr vx cv cH cfv vy cv cD cH cfv cS
      breq1 biimpar cA cB cR cS cH wiso vx cv cA wcel cD cA wcel wa wa vx cv cR
      ccnv cD csn cima wcel vx cv cD cR wbr vx cv cH cfv cD cH cfv cS wbr cD cA
      wcel vx cv cR ccnv cD csn cima wcel vx cv cD cR wbr wb cA cB cR cS cH
      wiso vx cv cA wcel cR cD vx cv cA vx vex eliniseg ad2antll cA cB vx cv cD
      cR cS cH isorel bitrd syl5ibr exp32 syl9r com34 imp32 reximdvai sylbid vx
      cv cC cR ccnv cD csn cima cin wcel vx wex vx cv cC wcel vx cv cR ccnv cD
      csn cima wcel wa vx wex cC cR ccnv cD csn cima cin c0 wceq wn vx cv cR
      ccnv cD csn cima wcel vx cC wrex vx cv cC cR ccnv cD csn cima cin wcel vx
      cv cC wcel vx cv cR ccnv cD csn cima wcel wa vx vx cv cC cR ccnv cD csn
      cima elin exbii vx cC cR ccnv cD csn cima cin neq0 vx cv cR ccnv cD csn
      cima wcel vx cC df-rex 3bitr4i syl6ibr exlimdv syl5bi con4d cC cR ccnv cD
      csn cima cin c0 wceq wn vx cv cC cR ccnv cD csn cima cin wcel vx wex cA
      cB cR cS cH wiso cC cA wss cD cA wcel wa wa cH cC cima cS ccnv cD cH cfv
      csn cima cin c0 wceq wn vx cC cR ccnv cD csn cima cin neq0 cA cB cR cS cH
      wiso cC cA wss cD cA wcel wa wa vx cv cC cR ccnv cD csn cima cin wcel cH
      cC cima cS ccnv cD cH cfv csn cima cin c0 wceq wn vx cA cB cR cS cH wiso
      cC cA wss cD cA wcel wa wa vx cv cC cR ccnv cD csn cima cin wcel vx cv cH
      cfv cH cC cima cS ccnv cD cH cfv csn cima cin wcel cH cC cima cS ccnv cD
      cH cfv csn cima cin c0 wceq wn cA cB cR cS cH wiso cC cA wss cD cA wcel
      wa wa vx cv cC wcel vx cv cR ccnv cD csn cima wcel wa vx cv cH cfv cH cC
      cima wcel vx cv cH cfv cS ccnv cD cH cfv csn cima wcel wa vx cv cC cR
      ccnv cD csn cima cin wcel vx cv cH cfv cH cC cima cS ccnv cD cH cfv csn
      cima cin wcel cA cB cR cS cH wiso cC cA wss cD cA wcel wa wa vx cv cC
      wcel vx cv cR ccnv cD csn cima wcel wa vx cv cH cfv cH cC cima wcel vx cv
      cH cfv cS ccnv cD cH cfv csn cima wcel cA cB cR cS cH wiso cC cA wss cD
      cA wcel wa wa vx cv cC wcel vx cv cH cfv cH cC cima wcel vx cv cR ccnv cD
      csn cima wcel cA cB cR cS cH wiso cH cA wfn cC cA wss cD cA wcel wa vx cv
      cC wcel vx cv cH cfv cH cC cima wcel wi cA cB cR cS cH wiso cA cB cH wf1o
      cH cA wfn cA cB cR cS cH isof1o cA cB cH f1ofn syl cH cA wfn cC cA wss vx
      cv cC wcel vx cv cH cfv cH cC cima wcel wi cD cA wcel cH cA wfn cC cA wss
      vx cv cC wcel vx cv cH cfv cH cC cima wcel cA cC cH vx cv fnfvima 3expia
      adantrr sylan adantrd cA cB cR cS cH wiso cC cA wss cD cA wcel wa wa vx
      cv cC wcel vx cv cR ccnv cD csn cima wcel vx cv cH cfv cS ccnv cD cH cfv
      csn cima wcel cA cB cR cS cH wiso cC cA wss cD cA wcel vx cv cC wcel vx
      cv cR ccnv cD csn cima wcel vx cv cH cfv cS ccnv cD cH cfv csn cima wcel
      wi wi cA cB cR cS cH wiso cC cA wss vx cv cC wcel cD cA wcel vx cv cR
      ccnv cD csn cima wcel vx cv cH cfv cS ccnv cD cH cfv csn cima wcel wi cC
      cA wss vx cv cC wcel vx cv cA wcel cA cB cR cS cH wiso cD cA wcel vx cv
      cR ccnv cD csn cima wcel vx cv cH cfv cS ccnv cD cH cfv csn cima wcel wi
      wi cC cA vx cv ssel cA cB cR cS cH wiso vx cv cA wcel cD cA wcel vx cv cR
      ccnv cD csn cima wcel vx cv cH cfv cS ccnv cD cH cfv csn cima wcel wi cA
      cB cR cS cH wiso vx cv cA wcel cD cA wcel wa wa vx cv cR ccnv cD csn cima
      wcel vx cv cD cR wbr vx cv cH cfv cS ccnv cD cH cfv csn cima wcel cD cA
      wcel vx cv cR ccnv cD csn cima wcel vx cv cD cR wbr wb cA cB cR cS cH
      wiso vx cv cA wcel cR cD vx cv cA vx vex eliniseg ad2antll cA cB cR cS cH
      wiso vx cv cA wcel cD cA wcel wa wa vx cv cD cR wbr vx cv cH cfv cD cH
      cfv cS wbr vx cv cH cfv cS ccnv cD cH cfv csn cima wcel cA cB cR cS cH
      wiso vx cv cA wcel cD cA wcel wa wa vx cv cD cR wbr vx cv cH cfv cD cH
      cfv cS wbr cA cB vx cv cD cR cS cH isorel biimpd cD cH cfv cvv wcel vx cv
      cH cfv cS ccnv cD cH cfv csn cima wcel vx cv cH cfv cD cH cfv cS wbr wb
      cD cH fvex cS cD cH cfv vx cv cH cfv cvv vx cv cH fvex eliniseg ax-mp
      syl6ibr sylbid exp32 syl9r com34 imp32 imp3a jcad vx cv cC cR ccnv cD csn
      cima elin vx cv cH cfv cH cC cima cS ccnv cD cH cfv csn cima elin 3imtr4g
      cH cC cima cS ccnv cD cH cfv csn cima cin vx cv cH cfv n0i syl6 exlimdv
      syl5bi impcon4bid $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.  $d x y S $.  $d x y H $.
    $d x y D $.
    $( Isomorphisms preserve initial segments.  Proposition 6.31(2) of
       [TakeutiZaring] p. 33.  (Contributed by NM, 20-Apr-2004.) $)
    isoini $p |- ( ( H Isom R , S ( A , B ) /\ D e. A ) ->
               ( H " ( A i^i ( `' R " { D } ) ) ) =
               ( B i^i ( `' S " { ( H ` D ) } ) ) ) $=
      cA cB cR cS cH wiso cD cA wcel wa cB cS ccnv cD cH cfv csn cima cin vx cv
      vy cv cH wbr vx cA cR ccnv cD csn cima cin wrex vy cab cH cA cR ccnv cD
      csn cima cin cima cA cB cR cS cH wiso cD cA wcel wa vx cv vy cv cH wbr vx
      cA cR ccnv cD csn cima cin wrex vy cB cS ccnv cD cH cfv csn cima cin vy
      cv cB cS ccnv cD cH cfv csn cima cin wcel vy cv cB wcel vy cv cS ccnv cD
      cH cfv csn cima wcel wa cA cB cR cS cH wiso cD cA wcel wa vx cv vy cv cH
      wbr vx cA cR ccnv cD csn cima cin wrex vy cv cB cS ccnv cD cH cfv csn
      cima elin cA cB cR cS cH wiso cD cA wcel wa vy cv cB wcel vy cv cS ccnv
      cD cH cfv csn cima wcel wa vx cv cH cfv vy cv wceq vx cA wrex vy cv cD cH
      cfv cS wbr wa vx cv vy cv cH wbr vx cA cR ccnv cD csn cima cin wrex cA cB
      cR cS cH wiso vy cv cB wcel vy cv cS ccnv cD cH cfv csn cima wcel wa vx
      cv cH cfv vy cv wceq vx cA wrex vy cv cD cH cfv cS wbr wa wb cD cA wcel
      cA cB cR cS cH wiso vy cv cB wcel vx cv cH cfv vy cv wceq vx cA wrex vy
      cv cS ccnv cD cH cfv csn cima wcel vy cv cD cH cfv cS wbr cA cB cR cS cH
      wiso vy cv cH crn wcel vy cv cB wcel vx cv cH cfv vy cv wceq vx cA wrex
      cA cB cR cS cH wiso cA cB cH wf1o cA cB cH wfo vy cv cH crn wcel vy cv cB
      wcel wb cA cB cR cS cH isof1o cA cB cH f1ofo cA cB cH wfo cH crn cB vy cv
      cA cB cH forn eleq2d 3syl cA cB cR cS cH wiso cA cB cH wf1o cH cA wfn vy
      cv cH crn wcel vx cv cH cfv vy cv wceq vx cA wrex wb cA cB cR cS cH
      isof1o cA cB cH f1ofn vx cA vy cv cH fvelrnb 3syl bitr3d cD cH cfv cvv
      wcel vy cv cS ccnv cD cH cfv csn cima wcel vy cv cD cH cfv cS wbr wb cA
      cB cR cS cH wiso cD cH fvex cS cD cH cfv vy cv cvv vy vex eliniseg mp1i
      anbi12d adantr cA cB cR cS cH wiso cD cA wcel wa vx cv vy cv cH wbr vx cA
      cR ccnv cD csn cima cin wrex vx cv cH cfv vy cv wceq vy cv cD cH cfv cS
      wbr wa vx cA wrex vx cv cH cfv vy cv wceq vx cA wrex vy cv cD cH cfv cS
      wbr wa cA cB cR cS cH wiso cD cA wcel wa vx cv vy cv cH wbr vx cv cH cfv
      vy cv wceq vy cv cD cH cfv cS wbr wa vx cA cR ccnv cD csn cima cin cA cA
      cB cR cS cH wiso cD cA wcel wa vx cv cA cR ccnv cD csn cima cin wcel vx
      cv vy cv cH wbr wa vx cv cA wcel vx cv cD cR wbr vx cv vy cv cH wbr wa wa
      vx cv cA wcel vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa wa cD cA
      wcel vx cv cA cR ccnv cD csn cima cin wcel vx cv vy cv cH wbr wa vx cv cA
      wcel vx cv cD cR wbr vx cv vy cv cH wbr wa wa wb cA cB cR cS cH wiso cD
      cA wcel vx cv cA cR ccnv cD csn cima cin wcel vx cv vy cv cH wbr wa vx cv
      cA wcel vx cv cD cR wbr wa vx cv vy cv cH wbr wa vx cv cA wcel vx cv cD
      cR wbr vx cv vy cv cH wbr wa wa cD cA wcel vx cv cA cR ccnv cD csn cima
      cin wcel vx cv cA wcel vx cv cD cR wbr wa vx cv vy cv cH wbr vx cv cA cR
      ccnv cD csn cima cin wcel vx cv cA wcel vx cv cR ccnv cD csn cima wcel wa
      cD cA wcel vx cv cA wcel vx cv cD cR wbr wa vx cv cA cR ccnv cD csn cima
      elin cD cA wcel vx cv cR ccnv cD csn cima wcel vx cv cD cR wbr vx cv cA
      wcel cR cD vx cv cA vx vex eliniseg anbi2d syl5bb anbi1d vx cv cA wcel vx
      cv cD cR wbr vx cv vy cv cH wbr anass syl6bb adantl cA cB cR cS cH wiso
      cD cA wcel wa vx cv cA wcel vx cv cD cR wbr vx cv vy cv cH wbr wa vx cv
      cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa cA cB cR cS cH wiso cD cA
      wcel vx cv cA wcel vx cv cD cR wbr vx cv vy cv cH wbr wa vx cv cH cfv vy
      cv wceq vy cv cD cH cfv cS wbr wa wb wi cA cB cR cS cH wiso vx cv cA wcel
      cD cA wcel vx cv cD cR wbr vx cv vy cv cH wbr wa vx cv cH cfv vy cv wceq
      vy cv cD cH cfv cS wbr wa wb cA cB cR cS cH wiso vx cv cA wcel cD cA wcel
      vx cv cD cR wbr vx cv vy cv cH wbr wa vx cv cH cfv vy cv wceq vy cv cD cH
      cfv cS wbr wa wb cA cB cR cS cH wiso vx cv cA wcel cD cA wcel wa wa vx cv
      cD cR wbr vx cv vy cv cH wbr wa vx cv cH cfv cD cH cfv cS wbr vx cv cH
      cfv vy cv wceq wa vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa cA cB
      cR cS cH wiso vx cv cA wcel cD cA wcel wa wa vx cv cD cR wbr vx cv cH cfv
      cD cH cfv cS wbr vx cv vy cv cH wbr vx cv cH cfv vy cv wceq cA cB vx cv
      cD cR cS cH isorel cA cB cR cS cH wiso vx cv cA wcel vx cv vy cv cH wbr
      vx cv cH cfv vy cv wceq wb cD cA wcel cA cB cR cS cH wiso cH cA wfn vx cv
      cA wcel vx cv vy cv cH wbr vx cv cH cfv vy cv wceq wb cA cB cR cS cH wiso
      cA cB cH wf1o cH cA wfn cA cB cR cS cH isof1o cA cB cH f1ofn syl cH cA
      wfn vx cv cA wcel wa vx cv cH cfv vy cv wceq vx cv vy cv cH wbr cA vx cv
      vy cv cH fnbrfvb bicomd sylan adantrr anbi12d vx cv cH cfv cD cH cfv cS
      wbr vx cv cH cfv vy cv wceq wa vx cv cH cfv vy cv wceq vx cv cH cfv cD cH
      cfv cS wbr wa vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr wa vx cv cH
      cfv cD cH cfv cS wbr vx cv cH cfv vy cv wceq ancom vx cv cH cfv vy cv
      wceq vx cv cH cfv cD cH cfv cS wbr vy cv cD cH cfv cS wbr vx cv cH cfv vy
      cv cD cH cfv cS breq1 pm5.32i bitri syl6bb exp32 com23 imp pm5.32d bitrd
      rexbidv2 vx cv cH cfv vy cv wceq vy cv cD cH cfv cS wbr vx cA r19.41v
      syl6bb bitr4d syl5bb abbi2dv vx vy cH cA cR ccnv cD csn cima cin dfima2
      syl6reqr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y H $.
    $d x y R $.  $d x y S $.
    isoini2.1 $e |- C = ( A i^i ( `' R " { X } ) ) $.
    isoini2.2 $e |- D = ( B i^i ( `' S " { ( H ` X ) } ) ) $.
    $( Isomorphisms are isomorphisms on their initial segments.  (Contributed
       by Mario Carneiro, 29-Mar-2014.) $)
    isoini2 $p |- ( ( H Isom R , S ( A , B ) /\ X e. A ) ->
                    ( H |` C ) Isom R , S ( C , D ) ) $=
      cA cB cR cS cH wiso cX cA wcel wa cC cD cH cC cres wf1o vx cv vy cv cR
      wbr vx cv cH cC cres cfv vy cv cH cC cres cfv cS wbr wb vy cC wral vx cC
      wral cC cD cR cS cH cC cres wiso cA cB cR cS cH wiso cX cA wcel wa cC cH
      cC cima cH cC cres wf1o cC cD cH cC cres wf1o cA cB cR cS cH wiso cX cA
      wcel wa cA cB cH wf1 cC cA wss cC cH cC cima cH cC cres wf1o cA cB cR cS
      cH wiso cA cB cH wf1 cX cA wcel cA cB cR cS cH wiso cA cB cH wf1o cA cB
      cH wf1 cA cB cR cS cH isof1o cA cB cH f1of1 syl adantr cC cA cR ccnv cX
      csn cima cin cA isoini2.1 cA cR ccnv cX csn cima inss1 eqsstri cA cB cC
      cH f1ores sylancl cA cB cR cS cH wiso cX cA wcel wa cH cC cima cD wceq cC
      cH cC cima cH cC cres wf1o cC cD cH cC cres wf1o wb cA cB cR cS cH wiso
      cX cA wcel wa cH cA cR ccnv cX csn cima cin cima cB cS ccnv cX cH cfv csn
      cima cin cH cC cima cD cA cB cX cR cS cH isoini cC cA cR ccnv cX csn cima
      cin cH isoini2.1 imaeq2i isoini2.2 3eqtr4g cH cC cima cD cC cH cC cres
      f1oeq3 syl mpbid cA cB cR cS cH wiso cX cA wcel wa vx cv vy cv cR wbr vx
      cv cH cfv vy cv cH cfv cS wbr wb vy cC wral vx cC wral vx cv vy cv cR wbr
      vx cv cH cC cres cfv vy cv cH cC cres cfv cS wbr wb vy cC wral vx cC wral
      cC cA wss cA cB cR cS cH wiso cX cA wcel wa vx cv vy cv cR wbr vx cv cH
      cfv vy cv cH cfv cS wbr wb vy cC wral vx cA wral vx cv vy cv cR wbr vx cv
      cH cfv vy cv cH cfv cS wbr wb vy cC wral vx cC wral cC cA cR ccnv cX csn
      cima cin cA isoini2.1 cA cR ccnv cX csn cima inss1 eqsstri cC cA wss cA
      cB cR cS cH wiso cX cA wcel wa vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wb vy cA wral vx cA wral vx cv vy cv cR wbr vx cv cH cfv vy cv
      cH cfv cS wbr wb vy cC wral vx cA wral cC cA cR ccnv cX csn cima cin cA
      isoini2.1 cA cR ccnv cX csn cima inss1 eqsstri cA cB cR cS cH wiso vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cA wral vx cA wral cX
      cA wcel cA cB cR cS cH wiso cA cB cH wf1o vx cv vy cv cR wbr vx cv cH cfv
      vy cv cH cfv cS wbr wb vy cA wral vx cA wral vx vy cA cB cR cS cH df-isom
      simprbi adantr cC cA wss vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS
      wbr wb vy cA wral vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb
      vy cC wral vx cA vx cv vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb
      vy cC cA ssralv ralimdv mpsyl vx cv vy cv cR wbr vx cv cH cfv vy cv cH
      cfv cS wbr wb vy cC wral vx cC cA ssralv mpsyl vx cv vy cv cR wbr vx cv
      cH cC cres cfv vy cv cH cC cres cfv cS wbr wb vy cC wral vx cv vy cv cR
      wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cC wral vx cC vx cv cC wcel vx
      cv vy cv cR wbr vx cv cH cC cres cfv vy cv cH cC cres cfv cS wbr wb vx cv
      vy cv cR wbr vx cv cH cfv vy cv cH cfv cS wbr wb vy cC vx cv cC wcel vy
      cv cC wcel wa vx cv cH cC cres cfv vy cv cH cC cres cfv cS wbr vx cv cH
      cfv vy cv cH cfv cS wbr vx cv vy cv cR wbr vx cv cC wcel vy cv cC wcel vx
      cv cH cC cres cfv vx cv cH cfv vy cv cH cC cres cfv vy cv cH cfv cS vx cv
      cC cH fvres vy cv cC cH fvres breqan12d bibi2d ralbidva ralbiia sylibr vx
      vy cC cD cR cS cH cC cres df-isom sylanbrc $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w x y z H $.  $d w x y z ph $.
    $d w x y z R $.  $d w x y z S $.
    isofrlem.1 $e |- ( ph -> H Isom R , S ( A , B ) ) $.
    isofrlem.2 $e |- ( ph -> ( H " x ) e. _V ) $.
    $( Lemma for ~ isofr .  (Contributed by NM, 29-Apr-2004.)  (Revised by
       Mario Carneiro, 18-Nov-2014.) $)
    isofrlem $p |- ( ph -> ( S Fr B -> R Fr A ) ) $=
      wph cB cS wfr vx cv cA wss vx cv c0 wne wa vx cv cR ccnv vy cv csn cima
      cin c0 wceq vy vx cv wrex wi vx wal cA cR wfr wph cB cS wfr vx cv cA wss
      vx cv c0 wne wa vx cv cR ccnv vy cv csn cima cin c0 wceq vy vx cv wrex wi
      vx wph cB cS wfr vx cv cA wss vx cv c0 wne wa cH vx cv cima cS ccnv vw cv
      csn cima cin c0 wceq vw cH vx cv cima wrex wi vx cv cA wss vx cv c0 wne
      wa vx cv cR ccnv vy cv csn cima cin c0 wceq vy vx cv wrex wi wph vx cv cA
      wss vx cv c0 wne wa cH vx cv cima cB wss cH vx cv cima c0 wne wa cB cS
      wfr cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq vw cH vx cv cima
      wrex wph cA cB cH wf1o vx cv cA wss vx cv c0 wne wa cH vx cv cima cB wss
      cH vx cv cima c0 wne wa wi wph cA cB cR cS cH wiso cA cB cH wf1o
      isofrlem.1 cA cB cR cS cH isof1o syl cA cB cH wf1o vx cv cA wss vx cv c0
      wne wa cH vx cv cima c0 wne cH vx cv cima cB wss cA cB cH wf1o cH cA wfn
      vx cv cA wss vx cv c0 wne wa cH vx cv cima c0 wne wi cA cB cH f1ofn cH cA
      wfn vx cv cA wss vx cv c0 wne cH vx cv cima c0 wne vx cv c0 wne vy cv vx
      cv wcel vy wex cH cA wfn vx cv cA wss wa cH vx cv cima c0 wne vy vx cv n0
      cH cA wfn vx cv cA wss wa vy cv vx cv wcel cH vx cv cima c0 wne vy cH cA
      wfn vx cv cA wss vy cv vx cv wcel cH vx cv cima c0 wne cH cA wfn vx cv cA
      wss vy cv vx cv wcel w3a vy cv cH cfv cH vx cv cima wcel cH vx cv cima c0
      wne cA vx cv cH vy cv fnfvima cH vx cv cima vy cv cH cfv ne0i syl 3expia
      exlimdv syl5bi expimpd syl cA cB cH wf1o cA cB cH wfo cH vx cv cima cB
      wss cA cB cH f1ofo cA cB cH wfo cH crn cH vx cv cima cB cH vx cv imassrn
      cA cB cH forn syl5sseq syl jctild syl cB cS wfr vz cv cB wss vz cv c0 wne
      wa vz cv cS ccnv vw cv csn cima cin c0 wceq vw vz cv wrex wi vz wal wph
      cH vx cv cima cB wss cH vx cv cima c0 wne wa cH vx cv cima cS ccnv vw cv
      csn cima cin c0 wceq vw cH vx cv cima wrex wi vz vw cB cS dffr3 wph cH vx
      cv cima cvv wcel vz cv cB wss vz cv c0 wne wa vz cv cS ccnv vw cv csn
      cima cin c0 wceq vw vz cv wrex wi vz wal cH vx cv cima cB wss cH vx cv
      cima c0 wne wa cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq vw cH vx
      cv cima wrex wi wi isofrlem.2 vz cv cB wss vz cv c0 wne wa vz cv cS ccnv
      vw cv csn cima cin c0 wceq vw vz cv wrex wi cH vx cv cima cB wss cH vx cv
      cima c0 wne wa cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq vw cH vx
      cv cima wrex wi vz cH vx cv cima cvv vz cv cH vx cv cima wceq vz cv cB
      wss vz cv c0 wne wa cH vx cv cima cB wss cH vx cv cima c0 wne wa vz cv cS
      ccnv vw cv csn cima cin c0 wceq vw vz cv wrex cH vx cv cima cS ccnv vw cv
      csn cima cin c0 wceq vw cH vx cv cima wrex vz cv cH vx cv cima wceq vz cv
      cB wss cH vx cv cima cB wss vz cv c0 wne cH vx cv cima c0 wne vz cv cH vx
      cv cima cB sseq1 vz cv cH vx cv cima c0 neeq1 anbi12d vz cv cS ccnv vw cv
      csn cima cin c0 wceq cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq vw
      vz cv cH vx cv cima vz cv cH vx cv cima wceq vz cv cS ccnv vw cv csn cima
      cin cH vx cv cima cS ccnv vw cv csn cima cin c0 vz cv cH vx cv cima cS
      ccnv vw cv csn cima ineq1 eqeq1d rexeqbi1dv imbi12d spcgv syl syl5bi
      syl5d wph vx cv cA wss vx cv c0 wne wa cH vx cv cima cS ccnv vw cv csn
      cima cin c0 wceq vw cH vx cv cima wrex vx cv cR ccnv vy cv csn cima cin
      c0 wceq vy vx cv wrex wph vx cv cA wss cH vx cv cima cS ccnv vw cv csn
      cima cin c0 wceq vw cH vx cv cima wrex vx cv cR ccnv vy cv csn cima cin
      c0 wceq vy vx cv wrex wi vx cv c0 wne wph vx cv cA wss cH vx cv cima cS
      ccnv vw cv csn cima cin c0 wceq vw cH vx cv cima wrex vx cv cR ccnv vy cv
      csn cima cin c0 wceq vy vx cv wrex wi wph vx cv cA wss wa cH vx cv cima
      cS ccnv vw cv csn cima cin c0 wceq vx cv cR ccnv vy cv csn cima cin c0
      wceq vy vx cv wrex vw cH vx cv cima wph vx cv cA wss wa vw cv cH vx cv
      cima wcel cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq vx cv cR ccnv
      vy cv csn cima cin c0 wceq vy vx cv wrex wph vx cv cA wss wa vw cv cH vx
      cv cima wcel cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq wa wa vy cv
      cH cfv vw cv wceq vy vx cv wrex vx cv cR ccnv vy cv csn cima cin c0 wceq
      vy vx cv wrex wph vx cv cA wss wa cH wfun vw cv cH vx cv cima wcel vy cv
      cH cfv vw cv wceq vy vx cv wrex vw cv cH vx cv cima wcel cH vx cv cima cS
      ccnv vw cv csn cima cin c0 wceq wa wph vx cv cA wss wa cA cB cH wf1o cH
      wfun wph cA cB cH wf1o vx cv cA wss wph cA cB cR cS cH wiso cA cB cH wf1o
      isofrlem.1 cA cB cR cS cH isof1o syl adantr cA cB cH f1ofun syl vw cv cH
      vx cv cima wcel cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq simpl vy
      vw cv vx cv cH fvelima syl2an wph vx cv cA wss wa vw cv cH vx cv cima
      wcel cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq wa wa vy cv cH cfv
      vw cv wceq vx cv cR ccnv vy cv csn cima cin c0 wceq vy vx cv wph vx cv cA
      wss wa vw cv cH vx cv cima wcel cH vx cv cima cS ccnv vw cv csn cima cin
      c0 wceq wa vy cv vx cv wcel vy cv cH cfv vw cv wceq vx cv cR ccnv vy cv
      csn cima cin c0 wceq wi wi vy cv vx cv wcel vy cv cH cfv vw cv wceq wph
      vx cv cA wss wa vw cv cH vx cv cima wcel cH vx cv cima cS ccnv vw cv csn
      cima cin c0 wceq wa vx cv cR ccnv vy cv csn cima cin c0 wceq wph vx cv cA
      wss wa vy cv vx cv wcel vy cv cH cfv vw cv wceq vw cv cH vx cv cima wcel
      cH vx cv cima cS ccnv vw cv csn cima cin c0 wceq wa vx cv cR ccnv vy cv
      csn cima cin c0 wceq wi wph vx cv cA wss vy cv vx cv wcel vy cv cH cfv vw
      cv wceq vw cv cH vx cv cima wcel cH vx cv cima cS ccnv vw cv csn cima cin
      c0 wceq wa vx cv cR ccnv vy cv csn cima cin c0 wceq wi wi wi wph vx cv cA
      wss vy cv vx cv wcel vy cv cH cfv vw cv wceq vw cv cH vx cv cima wcel cH
      vx cv cima cS ccnv vw cv csn cima cin c0 wceq wa vx cv cR ccnv vy cv csn
      cima cin c0 wceq wi vw cv cH vx cv cima wcel cH vx cv cima cS ccnv vw cv
      csn cima cin c0 wceq wa vx cv cR ccnv vy cv csn cima cin c0 wceq wph vx
      cv cA wss vy cv vx cv wcel wa wa vy cv cH cfv vw cv wceq wa cH vx cv cima
      cS ccnv vw cv csn cima cin c0 wceq vw cv cH vx cv cima wcel cH vx cv cima
      cS ccnv vw cv csn cima cin c0 wceq simpr wph vx cv cA wss vy cv vx cv
      wcel wa wa vx cv cR ccnv vy cv csn cima cin c0 wceq cH vx cv cima cS ccnv
      vy cv cH cfv csn cima cin c0 wceq vy cv cH cfv vw cv wceq cH vx cv cima
      cS ccnv vw cv csn cima cin c0 wceq wph cA cB cR cS cH wiso vx cv cA wss
      vy cv cA wcel wa vx cv cR ccnv vy cv csn cima cin c0 wceq cH vx cv cima
      cS ccnv vy cv cH cfv csn cima cin c0 wceq wb vx cv cA wss vy cv vx cv
      wcel wa isofrlem.1 vx cv cA wss vy cv vx cv wcel vy cv cA wcel vx cv cA
      vy cv ssel imdistani cA cB vx cv vy cv cR cS cH isomin syl2an vy cv cH
      cfv vw cv wceq cH vx cv cima cS ccnv vy cv cH cfv csn cima cin cH vx cv
      cima cS ccnv vw cv csn cima cin c0 vy cv cH cfv vw cv wceq cS ccnv vy cv
      cH cfv csn cima cS ccnv vw cv csn cima cH vx cv cima vy cv cH cfv vw cv
      wceq vy cv cH cfv csn vw cv csn cS ccnv vy cv cH cfv vw cv sneq imaeq2d
      ineq2d eqeq1d sylan9bb syl5ibr exp42 imp com3l com4t imp reximdvai mpd
      exp32 rexlimdv ex adantrd a2d syld alrimdv vx vy cA cR dffr3 syl6ibr $.

    $( Lemma for ~ isose .  (Contributed by Mario Carneiro, 23-Jun-2015.) $)
    isoselem $p |- ( ph -> ( R Se A -> S Se B ) ) $=
      wph cA cR wse cB cS ccnv vy cv csn cima cin cvv wcel vy cB wral cB cS wse
      wph cA cR wse cB cS ccnv vz cv cH cfv csn cima cin cvv wcel vz cA wral cB
      cS ccnv vy cv csn cima cin cvv wcel vy cB wral wph cA cR wse cB cS ccnv
      vz cv cH cfv csn cima cin cvv wcel vz cA wph vz cv cA wcel wa cA cR wse
      cA cR ccnv vz cv csn cima cin cvv wcel cB cS ccnv vz cv cH cfv csn cima
      cin cvv wcel vz cv cA wcel cA cR wse cA cR ccnv vz cv csn cima cin cvv
      wcel wi wph cA cR wse vz cv cA wcel cA cR ccnv vz cv csn cima cin cvv
      wcel cA cR wse cA cR ccnv vz cv csn cima cin cvv wcel vz cA cA cR wse cA
      cR ccnv vz cv csn cima cin cvv wcel vz cA wral vz cA cR dfse2 biimpi
      r19.21bi expcom adantl wph vz cv cA wcel wa cA cR ccnv vz cv csn cima cin
      cvv wcel cH cA cR ccnv vz cv csn cima cin cima cvv wcel cB cS ccnv vz cv
      cH cfv csn cima cin cvv wcel wph cA cR ccnv vz cv csn cima cin cvv wcel
      cH cA cR ccnv vz cv csn cima cin cima cvv wcel wi vz cv cA wcel cA cR
      ccnv vz cv csn cima cin cvv wcel wph cH cA cR ccnv vz cv csn cima cin
      cima cvv wcel wph cH vx cv cima cvv wcel wi wph cH cA cR ccnv vz cv csn
      cima cin cima cvv wcel wi vx cA cR ccnv vz cv csn cima cin cvv vx cv cA
      cR ccnv vz cv csn cima cin wceq cH vx cv cima cvv wcel cH cA cR ccnv vz
      cv csn cima cin cima cvv wcel wph vx cv cA cR ccnv vz cv csn cima cin
      wceq cH vx cv cima cH cA cR ccnv vz cv csn cima cin cima cvv vx cv cA cR
      ccnv vz cv csn cima cin cH imaeq2 eleq1d imbi2d isofrlem.2 vtoclg com12
      adantr wph vz cv cA wcel wa cH cA cR ccnv vz cv csn cima cin cima cB cS
      ccnv vz cv cH cfv csn cima cin cvv wph cA cB cR cS cH wiso vz cv cA wcel
      cH cA cR ccnv vz cv csn cima cin cima cB cS ccnv vz cv cH cfv csn cima
      cin wceq isofrlem.1 cA cB vz cv cR cS cH isoini sylan eleq1d sylibd syld
      ralrimdva wph cB cS ccnv vy cv csn cima cin cvv wcel vy cH crn wral cB cS
      ccnv vz cv cH cfv csn cima cin cvv wcel vz cA wral cB cS ccnv vy cv csn
      cima cin cvv wcel vy cB wral wph cA cB cH wf1o cH cA wfn cB cS ccnv vy cv
      csn cima cin cvv wcel vy cH crn wral cB cS ccnv vz cv cH cfv csn cima cin
      cvv wcel vz cA wral wb wph cA cB cR cS cH wiso cA cB cH wf1o isofrlem.1
      cA cB cR cS cH isof1o syl cA cB cH f1ofn cB cS ccnv vy cv csn cima cin
      cvv wcel cB cS ccnv vz cv cH cfv csn cima cin cvv wcel vy vz cA cH vy cv
      vz cv cH cfv wceq cB cS ccnv vy cv csn cima cin cB cS ccnv vz cv cH cfv
      csn cima cin cvv vy cv vz cv cH cfv wceq cS ccnv vy cv csn cima cS ccnv
      vz cv cH cfv csn cima cB vy cv vz cv cH cfv wceq vy cv csn vz cv cH cfv
      csn cS ccnv vy cv vz cv cH cfv sneq imaeq2d ineq2d eleq1d ralrn 3syl wph
      cB cS ccnv vy cv csn cima cin cvv wcel vy cH crn cB wph cA cB cH wf1o cA
      cB cH wfo cH crn cB wceq wph cA cB cR cS cH wiso cA cB cH wf1o isofrlem.1
      cA cB cR cS cH isof1o syl cA cB cH f1ofo cA cB cH forn 3syl raleqdv
      bitr3d sylibd vy cB cS dfse2 syl6ibr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x H $.  $d x R $.  $d x S $.  $d x V $.
    $( An isomorphism preserves well-foundedness.  Proposition 6.32(1) of
       [TakeutiZaring] p. 33.  (Contributed by NM, 30-Apr-2004.)  (Revised by
       Mario Carneiro, 18-Nov-2014.) $)
    isofr $p |- ( H Isom R , S ( A , B ) -> ( R Fr A <-> S Fr B ) ) $=
      cA cB cR cS cH wiso cA cR wfr cB cS wfr cA cB cR cS cH wiso cB cA cS cR
      cH ccnv wiso cA cR wfr cB cS wfr wi cA cB cR cS cH isocnv cB cA cS cR cH
      ccnv wiso vx cB cA cS cR cH ccnv cB cA cS cR cH ccnv wiso id cB cA cS cR
      cH ccnv wiso cB cA cH ccnv wf1o cH ccnv wfun cH ccnv vx cv cima cvv wcel
      cB cA cS cR cH ccnv isof1o cB cA cH ccnv f1ofun cH ccnv vx cv vx vex
      funimaex 3syl isofrlem syl cA cB cR cS cH wiso vx cA cB cR cS cH cA cB cR
      cS cH wiso id cA cB cR cS cH wiso cA cB cH wf1o cH wfun cH vx cv cima cvv
      wcel cA cB cR cS cH isof1o cA cB cH f1ofun cH vx cv vx vex funimaex 3syl
      isofrlem impbid $.

    $( An isomorphism preserves set-like relations.  (Contributed by Mario
       Carneiro, 23-Jun-2015.) $)
    isose $p |- ( H Isom R , S ( A , B ) -> ( R Se A <-> S Se B ) ) $=
      cA cB cR cS cH wiso cA cR wse cB cS wse cA cB cR cS cH wiso vx cA cB cR
      cS cH cA cB cR cS cH wiso id cA cB cR cS cH wiso cA cB cH wf1o cH wfun cH
      vx cv cima cvv wcel cA cB cR cS cH isof1o cA cB cH f1ofun cH vx cv vx vex
      funimaex 3syl isoselem cA cB cR cS cH wiso vx cB cA cS cR cH ccnv cA cB
      cR cS cH isocnv cA cB cR cS cH wiso cB cA cS cR cH ccnv wiso cH ccnv vx
      cv cima cvv wcel cA cB cR cS cH isocnv cB cA cS cR cH ccnv wiso cB cA cH
      ccnv wf1o cH ccnv wfun cH ccnv vx cv cima cvv wcel cB cA cS cR cH ccnv
      isof1o cB cA cH ccnv f1ofun cH ccnv vx cv vx vex funimaex 3syl syl
      isoselem impbid $.

    $( A weak form of ~ isofr that does not need Replacement.  (Contributed by
       Mario Carneiro, 18-Nov-2014.) $)
    isofr2 $p |- ( ( H Isom R , S ( A , B ) /\ B e. V ) ->
                   ( S Fr B -> R Fr A ) ) $=
      cA cB cR cS cH wiso cB cV wcel wa vx cA cB cR cS cH cA cB cR cS cH wiso
      cB cV wcel simpl cA cB cR cS cH wiso cH vx cv cima cB wss cB cV wcel cH
      vx cv cima cvv wcel cA cB cR cS cH wiso cH vx cv cima cH crn cB cH vx cv
      imassrn cA cB cR cS cH wiso cA cB cH wf1o cA cB cH wf cH crn cB wss cA cB
      cR cS cH isof1o cA cB cH f1of cA cB cH frn 3syl syl5ss cH vx cv cima cB
      cV ssexg sylan isofrlem $.
  $}

  ${
    $d H a b c d e f $.  $d R a b c d e f $.  $d S a b c d e f $.
    $d A a b c d e f $.  $d B a b c d e f $.
    $( Lemma for ~ isopo .  (Contributed by Stefan O'Rear, 16-Nov-2014.) $)
    isopolem $p |- ( H Isom R , S ( A , B ) -> ( S Po B -> R Po A ) ) $=
      cA cB cR cS cH wiso va cv va cv cS wbr wn va cv vb cv cS wbr vb cv vc cv
      cS wbr wa va cv vc cv cS wbr wi wa vc cB wral vb cB wral va cB wral vd cv
      vd cv cR wbr wn vd cv ve cv cR wbr ve cv vf cv cR wbr wa vd cv vf cv cR
      wbr wi wa vf cA wral ve cA wral vd cA wral cB cS wpo cA cR wpo cA cB cR
      cS cH wiso va cv va cv cS wbr wn va cv vb cv cS wbr vb cv vc cv cS wbr wa
      va cv vc cv cS wbr wi wa vc cB wral vb cB wral va cB wral vd cv vd cv cR
      wbr wn vd cv ve cv cR wbr ve cv vf cv cR wbr wa vd cv vf cv cR wbr wi wa
      vf cA wral ve cA wral vd cA wral cA cB cR cS cH wiso va cv va cv cS wbr
      wn va cv vb cv cS wbr vb cv vc cv cS wbr wa va cv vc cv cS wbr wi wa vc
      cB wral vb cB wral va cB wral wa vd cv vd cv cR wbr wn vd cv ve cv cR wbr
      ve cv vf cv cR wbr wa vd cv vf cv cR wbr wi wa vd ve vf cA cA cA cA cB cR
      cS cH wiso va cv va cv cS wbr wn va cv vb cv cS wbr vb cv vc cv cS wbr wa
      va cv vc cv cS wbr wi wa vc cB wral vb cB wral va cB wral vd cv cA wcel
      ve cv cA wcel vf cv cA wcel w3a vd cv vd cv cR wbr wn vd cv ve cv cR wbr
      ve cv vf cv cR wbr wa vd cv vf cv cR wbr wi wa cA cB cR cS cH wiso vd cv
      cA wcel ve cv cA wcel vf cv cA wcel w3a va cv va cv cS wbr wn va cv vb cv
      cS wbr vb cv vc cv cS wbr wa va cv vc cv cS wbr wi wa vc cB wral vb cB
      wral va cB wral vd cv vd cv cR wbr wn vd cv ve cv cR wbr ve cv vf cv cR
      wbr wa vd cv vf cv cR wbr wi wa cA cB cR cS cH wiso vd cv cA wcel ve cv
      cA wcel vf cv cA wcel w3a va cv va cv cS wbr wn va cv vb cv cS wbr vb cv
      vc cv cS wbr wa va cv vc cv cS wbr wi wa vc cB wral vb cB wral va cB wral
      vd cv vd cv cR wbr wn vd cv ve cv cR wbr ve cv vf cv cR wbr wa vd cv vf
      cv cR wbr wi wa wi cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf cv
      cA wcel w3a wa va cv va cv cS wbr wn va cv vb cv cS wbr vb cv vc cv cS
      wbr wa va cv vc cv cS wbr wi wa vc cB wral vb cB wral va cB wral vd cv cH
      cfv vd cv cH cfv cS wbr wn vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv
      vf cv cH cfv cS wbr wa vd cv cH cfv vf cv cH cfv cS wbr wi wa vd cv vd cv
      cR wbr wn vd cv ve cv cR wbr ve cv vf cv cR wbr wa vd cv vf cv cR wbr wi
      wa cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a wa
      vd cv cH cfv cB wcel ve cv cH cfv cB wcel vf cv cH cfv cB wcel w3a va cv
      va cv cS wbr wn va cv vb cv cS wbr vb cv vc cv cS wbr wa va cv vc cv cS
      wbr wi wa vc cB wral vb cB wral va cB wral vd cv cH cfv vd cv cH cfv cS
      wbr wn vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv vf cv cH cfv cS wbr
      wa vd cv cH cfv vf cv cH cfv cS wbr wi wa wi cA cB cR cS cH wiso vd cv cA
      wcel ve cv cA wcel vf cv cA wcel w3a vd cv cH cfv cB wcel ve cv cH cfv cB
      wcel vf cv cH cfv cB wcel w3a cA cB cR cS cH wiso cA cB cH wf1o cA cB cH
      wf vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a vd cv cH cfv cB wcel ve
      cv cH cfv cB wcel vf cv cH cfv cB wcel w3a wi cA cB cR cS cH isof1o cA cB
      cH f1of cA cB cH wf vd cv cA wcel vd cv cH cfv cB wcel ve cv cA wcel ve
      cv cH cfv cB wcel vf cv cA wcel vf cv cH cfv cB wcel cA cB cH wf vd cv cA
      wcel vd cv cH cfv cB wcel cA cB vd cv cH ffvelrn ex cA cB cH wf ve cv cA
      wcel ve cv cH cfv cB wcel cA cB ve cv cH ffvelrn ex cA cB cH wf vf cv cA
      wcel vf cv cH cfv cB wcel cA cB vf cv cH ffvelrn ex 3anim123d 3syl imp va
      cv va cv cS wbr wn va cv vb cv cS wbr vb cv vc cv cS wbr wa va cv vc cv
      cS wbr wi wa vd cv cH cfv vd cv cH cfv cS wbr wn vd cv cH cfv ve cv cH
      cfv cS wbr ve cv cH cfv vf cv cH cfv cS wbr wa vd cv cH cfv vf cv cH cfv
      cS wbr wi wa vd cv cH cfv vd cv cH cfv cS wbr wn vd cv cH cfv vb cv cS
      wbr vb cv vc cv cS wbr wa vd cv cH cfv vc cv cS wbr wi wa vd cv cH cfv vd
      cv cH cfv cS wbr wn vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv vc cv
      cS wbr wa vd cv cH cfv vc cv cS wbr wi wa va vb vc vd cv cH cfv ve cv cH
      cfv vf cv cH cfv cB cB cB va cv vd cv cH cfv wceq va cv va cv cS wbr wn
      vd cv cH cfv vd cv cH cfv cS wbr wn va cv vb cv cS wbr vb cv vc cv cS wbr
      wa va cv vc cv cS wbr wi vd cv cH cfv vb cv cS wbr vb cv vc cv cS wbr wa
      vd cv cH cfv vc cv cS wbr wi va cv vd cv cH cfv wceq va cv va cv cS wbr
      vd cv cH cfv vd cv cH cfv cS wbr va cv vd cv cH cfv wceq va cv va cv cS
      wbr vd cv cH cfv vd cv cH cfv cS wbr wb va cv vd cv cH cfv va cv vd cv cH
      cfv cS breq12 anidms notbid va cv vd cv cH cfv wceq va cv vb cv cS wbr vb
      cv vc cv cS wbr wa vd cv cH cfv vb cv cS wbr vb cv vc cv cS wbr wa va cv
      vc cv cS wbr vd cv cH cfv vc cv cS wbr va cv vd cv cH cfv wceq va cv vb
      cv cS wbr vd cv cH cfv vb cv cS wbr vb cv vc cv cS wbr va cv vd cv cH cfv
      vb cv cS breq1 anbi1d va cv vd cv cH cfv vc cv cS breq1 imbi12d anbi12d
      vb cv ve cv cH cfv wceq vd cv cH cfv vb cv cS wbr vb cv vc cv cS wbr wa
      vd cv cH cfv vc cv cS wbr wi vd cv cH cfv ve cv cH cfv cS wbr ve cv cH
      cfv vc cv cS wbr wa vd cv cH cfv vc cv cS wbr wi vd cv cH cfv vd cv cH
      cfv cS wbr wn vb cv ve cv cH cfv wceq vd cv cH cfv vb cv cS wbr vb cv vc
      cv cS wbr wa vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv vc cv cS wbr
      wa vd cv cH cfv vc cv cS wbr vb cv ve cv cH cfv wceq vd cv cH cfv vb cv
      cS wbr vd cv cH cfv ve cv cH cfv cS wbr vb cv vc cv cS wbr ve cv cH cfv
      vc cv cS wbr vb cv ve cv cH cfv vd cv cH cfv cS breq2 vb cv ve cv cH cfv
      vc cv cS breq1 anbi12d imbi1d anbi2d vc cv vf cv cH cfv wceq vd cv cH cfv
      ve cv cH cfv cS wbr ve cv cH cfv vc cv cS wbr wa vd cv cH cfv vc cv cS
      wbr wi vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv vf cv cH cfv cS wbr
      wa vd cv cH cfv vf cv cH cfv cS wbr wi vd cv cH cfv vd cv cH cfv cS wbr
      wn vc cv vf cv cH cfv wceq vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv
      vc cv cS wbr wa vd cv cH cfv ve cv cH cfv cS wbr ve cv cH cfv vf cv cH
      cfv cS wbr wa vd cv cH cfv vc cv cS wbr vd cv cH cfv vf cv cH cfv cS wbr
      vc cv vf cv cH cfv wceq ve cv cH cfv vc cv cS wbr ve cv cH cfv vf cv cH
      cfv cS wbr vd cv cH cfv ve cv cH cfv cS wbr vc cv vf cv cH cfv ve cv cH
      cfv cS breq2 anbi2d vc cv vf cv cH cfv vd cv cH cfv cS breq2 imbi12d
      anbi2d rspc3v syl cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf cv
      cA wcel w3a wa vd cv vd cv cR wbr wn vd cv cH cfv vd cv cH cfv cS wbr wn
      vd cv ve cv cR wbr ve cv vf cv cR wbr wa vd cv vf cv cR wbr wi vd cv cH
      cfv ve cv cH cfv cS wbr ve cv cH cfv vf cv cH cfv cS wbr wa vd cv cH cfv
      vf cv cH cfv cS wbr wi cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf
      cv cA wcel w3a wa vd cv vd cv cR wbr vd cv cH cfv vd cv cH cfv cS wbr cA
      cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a wa cA cB
      cR cS cH wiso vd cv cA wcel vd cv cA wcel vd cv vd cv cR wbr vd cv cH cfv
      vd cv cH cfv cS wbr wb cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf
      cv cA wcel w3a simpl cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf
      cv cA wcel simpr1 cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf cv
      cA wcel simpr1 cA cB vd cv vd cv cR cS cH isorel syl12anc notbid cA cB cR
      cS cH wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a wa vd cv ve cv
      cR wbr ve cv vf cv cR wbr wa vd cv cH cfv ve cv cH cfv cS wbr ve cv cH
      cfv vf cv cH cfv cS wbr wa vd cv vf cv cR wbr vd cv cH cfv vf cv cH cfv
      cS wbr cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a
      wa vd cv ve cv cR wbr vd cv cH cfv ve cv cH cfv cS wbr ve cv vf cv cR wbr
      ve cv cH cfv vf cv cH cfv cS wbr cA cB cR cS cH wiso vd cv cA wcel ve cv
      cA wcel vf cv cA wcel w3a wa cA cB cR cS cH wiso vd cv cA wcel ve cv cA
      wcel vd cv ve cv cR wbr vd cv cH cfv ve cv cH cfv cS wbr wb cA cB cR cS
      cH wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a simpl cA cB cR cS
      cH wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel simpr1 cA cB cR cS cH
      wiso vd cv cA wcel ve cv cA wcel vf cv cA wcel simpr2 cA cB vd cv ve cv
      cR cS cH isorel syl12anc cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel
      vf cv cA wcel w3a wa cA cB cR cS cH wiso ve cv cA wcel vf cv cA wcel ve
      cv vf cv cR wbr ve cv cH cfv vf cv cH cfv cS wbr wb cA cB cR cS cH wiso
      vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a simpl cA cB cR cS cH wiso
      vd cv cA wcel ve cv cA wcel vf cv cA wcel simpr2 cA cB cR cS cH wiso vd
      cv cA wcel ve cv cA wcel vf cv cA wcel simpr3 cA cB ve cv vf cv cR cS cH
      isorel syl12anc anbi12d cA cB cR cS cH wiso vd cv cA wcel ve cv cA wcel
      vf cv cA wcel w3a wa cA cB cR cS cH wiso vd cv cA wcel vf cv cA wcel vd
      cv vf cv cR wbr vd cv cH cfv vf cv cH cfv cS wbr wb cA cB cR cS cH wiso
      vd cv cA wcel ve cv cA wcel vf cv cA wcel w3a simpl cA cB cR cS cH wiso
      vd cv cA wcel ve cv cA wcel vf cv cA wcel simpr1 cA cB cR cS cH wiso vd
      cv cA wcel ve cv cA wcel vf cv cA wcel simpr3 cA cB vd cv vf cv cR cS cH
      isorel syl12anc imbi12d anbi12d sylibrd ex com23 imp31 ralrimivvva ex va
      vb vc cB cS df-po vd ve vf cA cR df-po 3imtr4g $.

    $( An isomorphism preserves partial ordering.  (Contributed by Stefan
       O'Rear, 16-Nov-2014.) $)
    isopo $p |- ( H Isom R , S ( A , B ) -> ( R Po A <-> S Po B ) ) $=
      cA cB cR cS cH wiso cA cR wpo cB cS wpo cA cB cR cS cH wiso cB cA cS cR
      cH ccnv wiso cA cR wpo cB cS wpo wi cA cB cR cS cH isocnv cB cA cS cR cH
      ccnv isopolem syl cA cB cR cS cH isopolem impbid $.

    $( Lemma for ~ isoso .  (Contributed by Stefan O'Rear, 16-Nov-2014.) $)
    isosolem $p |- ( H Isom R , S ( A , B ) -> ( S Or B -> R Or A ) ) $=
      cA cB cR cS cH wiso cB cS wpo va cv vb cv cS wbr va vb weq vb cv va cv cS
      wbr w3o vb cB wral va cB wral wa cA cR wpo vc cv vd cv cR wbr vc vd weq
      vd cv vc cv cR wbr w3o vd cA wral vc cA wral wa cB cS wor cA cR wor cA cB
      cR cS cH wiso cB cS wpo cA cR wpo va cv vb cv cS wbr va vb weq vb cv va
      cv cS wbr w3o vb cB wral va cB wral vc cv vd cv cR wbr vc vd weq vd cv vc
      cv cR wbr w3o vd cA wral vc cA wral cA cB cR cS cH isopolem cA cB cR cS
      cH wiso va cv vb cv cS wbr va vb weq vb cv va cv cS wbr w3o vb cB wral va
      cB wral vc cv vd cv cR wbr vc vd weq vd cv vc cv cR wbr w3o vc vd cA cA
      cA cB cR cS cH wiso vc cv cA wcel vd cv cA wcel wa wa va cv vb cv cS wbr
      va vb weq vb cv va cv cS wbr w3o vb cB wral va cB wral vc cv cH cfv vd cv
      cH cfv cS wbr vc cv cH cfv vd cv cH cfv wceq vd cv cH cfv vc cv cH cfv cS
      wbr w3o vc cv vd cv cR wbr vc vd weq vd cv vc cv cR wbr w3o cA cB cR cS
      cH wiso vc cv cA wcel vd cv cA wcel wa wa vc cv cH cfv cB wcel vd cv cH
      cfv cB wcel wa va cv vb cv cS wbr va vb weq vb cv va cv cS wbr w3o vb cB
      wral va cB wral vc cv cH cfv vd cv cH cfv cS wbr vc cv cH cfv vd cv cH
      cfv wceq vd cv cH cfv vc cv cH cfv cS wbr w3o wi cA cB cR cS cH wiso vc
      cv cA wcel vd cv cA wcel wa vc cv cH cfv cB wcel vd cv cH cfv cB wcel wa
      cA cB cR cS cH wiso cA cB cH wf1o cA cB cH wf vc cv cA wcel vd cv cA wcel
      wa vc cv cH cfv cB wcel vd cv cH cfv cB wcel wa wi cA cB cR cS cH isof1o
      cA cB cH f1of cA cB cH wf vc cv cA wcel vc cv cH cfv cB wcel vd cv cA
      wcel vd cv cH cfv cB wcel cA cB cH wf vc cv cA wcel vc cv cH cfv cB wcel
      cA cB vc cv cH ffvelrn ex cA cB cH wf vd cv cA wcel vd cv cH cfv cB wcel
      cA cB vd cv cH ffvelrn ex anim12d 3syl imp va cv vb cv cS wbr va vb weq
      vb cv va cv cS wbr w3o vc cv cH cfv vd cv cH cfv cS wbr vc cv cH cfv vd
      cv cH cfv wceq vd cv cH cfv vc cv cH cfv cS wbr w3o vc cv cH cfv vb cv cS
      wbr vc cv cH cfv vb cv wceq vb cv vc cv cH cfv cS wbr w3o va vb vc cv cH
      cfv vd cv cH cfv cB cB va cv vc cv cH cfv wceq va cv vb cv cS wbr vc cv
      cH cfv vb cv cS wbr va vb weq vc cv cH cfv vb cv wceq vb cv va cv cS wbr
      vb cv vc cv cH cfv cS wbr va cv vc cv cH cfv vb cv cS breq1 va cv vc cv
      cH cfv vb cv eqeq1 va cv vc cv cH cfv vb cv cS breq2 3orbi123d vb cv vd
      cv cH cfv wceq vc cv cH cfv vb cv cS wbr vc cv cH cfv vd cv cH cfv cS wbr
      vc cv cH cfv vb cv wceq vc cv cH cfv vd cv cH cfv wceq vb cv vc cv cH cfv
      cS wbr vd cv cH cfv vc cv cH cfv cS wbr vb cv vd cv cH cfv vc cv cH cfv
      cS breq2 vb cv vd cv cH cfv vc cv cH cfv eqeq2 vb cv vd cv cH cfv vc cv
      cH cfv cS breq1 3orbi123d rspc2v syl cA cB cR cS cH wiso vc cv cA wcel vd
      cv cA wcel wa wa vc cv vd cv cR wbr vc cv cH cfv vd cv cH cfv cS wbr vc
      vd weq vc cv cH cfv vd cv cH cfv wceq vd cv vc cv cR wbr vd cv cH cfv vc
      cv cH cfv cS wbr cA cB vc cv vd cv cR cS cH isorel cA cB cR cS cH wiso vc
      cv cA wcel vd cv cA wcel wa wa vc cv cH cfv vd cv cH cfv wceq vc vd weq
      cA cB cR cS cH wiso cA cB cH wf1 vc cv cA wcel vd cv cA wcel wa vc cv cH
      cfv vd cv cH cfv wceq vc vd weq wb cA cB cR cS cH wiso cA cB cH wf1o cA
      cB cH wf1 cA cB cR cS cH isof1o cA cB cH f1of1 syl cA cB vc cv vd cv cH
      f1fveq sylan bicomd cA cB cR cS cH wiso vd cv cA wcel vc cv cA wcel vd cv
      vc cv cR wbr vd cv cH cfv vc cv cH cfv cS wbr wb cA cB vd cv vc cv cR cS
      cH isorel ancom2s 3orbi123d sylibrd ralrimdvva anim12d va vb cB cS df-so
      vc vd cA cR df-so 3imtr4g $.

    $( An isomorphism preserves strict ordering.  (Contributed by Stefan
       O'Rear, 16-Nov-2014.) $)
    isoso $p |- ( H Isom R , S ( A , B ) -> ( R Or A <-> S Or B ) ) $=
      cA cB cR cS cH wiso cA cR wor cB cS wor cA cB cR cS cH wiso cB cA cS cR
      cH ccnv wiso cA cR wor cB cS wor wi cA cB cR cS cH isocnv cB cA cS cR cH
      ccnv isosolem syl cA cB cR cS cH isosolem impbid $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y R $.  $d x y z w S $.
    $d x y z w H $.
    $( An isomorphism preserves well-ordering.  Proposition 6.32(3) of
       [TakeutiZaring] p. 33.  (Contributed by NM, 30-Apr-2004.)  (Revised by
       Mario Carneiro, 18-Nov-2014.) $)
    isowe $p |- ( H Isom R , S ( A , B ) -> ( R We A <-> S We B ) ) $=
      cA cB cR cS cH wiso cA cR wfr cA cR wor wa cB cS wfr cB cS wor wa cA cR
      wwe cB cS wwe cA cB cR cS cH wiso cA cR wfr cB cS wfr cA cR wor cB cS wor
      cA cB cR cS cH isofr cA cB cR cS cH isoso anbi12d cA cR df-we cB cS df-we
      3bitr4g $.

    $( A weak form of ~ isowe that does not need Replacement.  (Contributed by
       Mario Carneiro, 18-Nov-2014.) $)
    isowe2 $p |- ( ( H Isom R , S ( A , B ) /\ A. x ( H " x ) e. _V ) ->
                   ( S We B -> R We A ) ) $=
      cA cB cR cS cH wiso cH vx cv cima cvv wcel vx wal wa cB cS wfr cB cS wor
      wa cA cR wfr cA cR wor wa cB cS wwe cA cR wwe cA cB cR cS cH wiso cH vx
      cv cima cvv wcel vx wal wa cB cS wfr cA cR wfr cB cS wor cA cR wor cA cB
      cR cS cH wiso cH vx cv cima cvv wcel vx wal wa vy cA cB cR cS cH cA cB cR
      cS cH wiso cH vx cv cima cvv wcel vx wal simpl cH vx cv cima cvv wcel vx
      wal cH vy cv cima cvv wcel cA cB cR cS cH wiso cH vx cv cima cvv wcel cH
      vy cv cima cvv wcel vx vy vx cv vy cv wceq cH vx cv cima cH vy cv cima
      cvv vx cv vy cv cH imaeq2 eleq1d spv adantl isofrlem cA cB cR cS cH wiso
      cB cS wor cA cR wor wi cH vx cv cima cvv wcel vx wal cA cB cR cS cH
      isosolem adantr anim12d cB cS df-we cA cR df-we 3imtr4g $.
  $}

  ${
    $d x y z w v u A $.  $d x y v u B $.  $d x y z w v u H $.
    $d x y z w v u R $.  $d v u S $.
    $( Any one-to-one onto function determines an isomorphism with an induced
       relation ` S ` .  Proposition 6.33 of [TakeutiZaring] p. 34.
       (Contributed by NM, 30-Apr-2004.) $)
    f1oiso $p |- ( ( H : A -1-1-onto-> B /\ S = { <. z , w >. |
     E. x e. A E. y e. A ( ( z = ( H ` x ) /\ w = ( H ` y ) ) /\ x R y ) } ) ->
                  H Isom R , S ( A , B ) ) $=
      cA cB cH wf1o cS vz cv vx cv cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv
      vy cv cR wbr wa vy cA wrex vx cA wrex vz vw copab wceq wa cA cB cH wf1o
      vv cv vu cv cR wbr vv cv cH cfv vu cv cH cfv cS wbr wb vu cA wral vv cA
      wral cA cB cR cS cH wiso cA cB cH wf1o cS vz cv vx cv cH cfv wceq vw cv
      vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz vw
      copab wceq simpl cA cB cH wf1o cA cB cH wf1 cS vz cv vx cv cH cfv wceq vw
      cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz vw
      copab wceq vv cv vu cv cR wbr vv cv cH cfv vu cv cH cfv cS wbr wb vu cA
      wral vv cA wral cA cB cH f1of1 cA cB cH wf1 cS vz cv vx cv cH cfv wceq vw
      cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz vw
      copab wceq wa vv cv vu cv cR wbr vv cv cH cfv vu cv cH cfv cS wbr wb vv
      vu cA cA vv cv cH cfv vu cv cH cfv cS wbr vv cv cH cfv vu cv cH cfv cop
      cS wcel cA cB cH wf1 cS vz cv vx cv cH cfv wceq vw cv vy cv cH cfv wceq
      wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz vw copab wceq wa vv cv
      cA wcel vu cv cA wcel wa wa vv cv vu cv cR wbr vv cv cH cfv vu cv cH cfv
      cS df-br cA cB cH wf1 vv cv cA wcel vu cv cA wcel wa cS vz cv vx cv cH
      cfv wceq vw cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx
      cA wrex vz vw copab wceq vv cv cH cfv vu cv cH cfv cop cS wcel vv cv vu
      cv cR wbr wb cS vz cv vx cv cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv
      vy cv cR wbr wa vy cA wrex vx cA wrex vz vw copab wceq vv cv cH cfv vu cv
      cH cfv cop cS wcel vv cv cH cfv vu cv cH cfv cop vz cv vx cv cH cfv wceq
      vw cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz
      vw copab wcel cA cB cH wf1 vv cv cA wcel vu cv cA wcel wa wa vv cv vu cv
      cR wbr cS vz cv vx cv cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv vy cv
      cR wbr wa vy cA wrex vx cA wrex vz vw copab vv cv cH cfv vu cv cH cfv cop
      eleq2 vv cv cH cfv vu cv cH cfv cop vz cv vx cv cH cfv wceq vw cv vy cv
      cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz vw copab
      wcel vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv wceq wa vx
      cv vy cv cR wbr wa vy cA wrex vx cA wrex cA cB cH wf1 vv cv cA wcel vu cv
      cA wcel wa wa vv cv vu cv cR wbr vz cv vx cv cH cfv wceq vw cv vy cv cH
      cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vv cv cH cfv vx
      cv cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA
      wrex vx cA wrex vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv
      wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vz vw vv cv cH cfv vu
      cv cH cfv vv cv cH fvex vu cv cH fvex vz cv vv cv cH cfv wceq vz cv vx cv
      cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vv cv cH cfv
      vx cv cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vx vy
      cA cA vz cv vv cv cH cfv wceq vz cv vx cv cH cfv wceq vw cv vy cv cH cfv
      wceq wa vv cv cH cfv vx cv cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv
      vy cv cR wbr vz cv vv cv cH cfv wceq vz cv vx cv cH cfv wceq vv cv cH cfv
      vx cv cH cfv wceq vw cv vy cv cH cfv wceq vz cv vv cv cH cfv vx cv cH cfv
      eqeq1 anbi1d anbi1d 2rexbidv vw cv vu cv cH cfv wceq vv cv cH cfv vx cv
      cH cfv wceq vw cv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vv cv cH cfv
      vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa
      vx vy cA cA vw cv vu cv cH cfv wceq vv cv cH cfv vx cv cH cfv wceq vw cv
      vy cv cH cfv wceq wa vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH
      cfv wceq wa vx cv vy cv cR wbr vw cv vu cv cH cfv wceq vw cv vy cv cH cfv
      wceq vu cv cH cfv vy cv cH cfv wceq vv cv cH cfv vx cv cH cfv wceq vw cv
      vu cv cH cfv vy cv cH cfv eqeq1 anbi2d anbi1d 2rexbidv opelopab cA cB cH
      wf1 vv cv cA wcel vu cv cA wcel vv cv cH cfv vx cv cH cfv wceq vu cv cH
      cfv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vv
      cv vu cv cR wbr wb cA cB cH wf1 vv cv cA wcel wa vv cv cH cfv vx cv cH
      cfv wceq vu cv cH cfv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA
      wrex vx cA wrex vu cv cH cfv vy cv cH cfv wceq vv cv vy cv cR wbr wa vy
      cA wrex cA cB cH wf1 vu cv cA wcel wa vv cv vu cv cR wbr cA cB cH wf1 vv
      cv cA wcel wa vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv
      wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cA wrex vx cv vv cv wceq vu
      cv cH cfv vy cv cH cfv wceq vx cv vy cv cR wbr wa vy cA wrex wa vx cA
      wrex vu cv cH cfv vy cv cH cfv wceq vv cv vy cv cR wbr wa vy cA wrex cA
      cB cH wf1 vv cv cA wcel wa vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy
      cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cv vv cv wceq vu cv
      cH cfv vy cv cH cfv wceq vx cv vy cv cR wbr wa vy cA wrex wa vx cA cA cB
      cH wf1 vv cv cA wcel wa vx cv cA wcel wa vv cv cH cfv vx cv cH cfv wceq
      vu cv cH cfv vy cv cH cfv wceq wa vx cv vy cv cR wbr wa vy cA wrex vx cv
      vv cv wceq vu cv cH cfv vy cv cH cfv wceq vx cv vy cv cR wbr wa wa vy cA
      wrex vx cv vv cv wceq vu cv cH cfv vy cv cH cfv wceq vx cv vy cv cR wbr
      wa vy cA wrex wa cA cB cH wf1 vv cv cA wcel wa vx cv cA wcel wa vv cv cH
      cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv wceq wa vx cv vy cv cR
      wbr wa vx cv vv cv wceq vu cv cH cfv vy cv cH cfv wceq vx cv vy cv cR wbr
      wa wa vy cA vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv wceq
      wa vx cv vy cv cR wbr wa vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy
      cv cH cfv wceq vx cv vy cv cR wbr wa wa cA cB cH wf1 vv cv cA wcel wa vx
      cv cA wcel wa vx cv vv cv wceq vu cv cH cfv vy cv cH cfv wceq vx cv vy cv
      cR wbr wa wa vv cv cH cfv vx cv cH cfv wceq vu cv cH cfv vy cv cH cfv
      wceq vx cv vy cv cR wbr anass cA cB cH wf1 vv cv cA wcel wa vx cv cA wcel
      wa vv cv cH cfv vx cv cH cfv wceq vx cv vv cv wceq vu cv cH cfv vy cv cH
      cfv wceq vx cv vy cv cR wbr wa cA cB cH wf1 vv cv cA wcel vx cv cA wcel
      vv cv cH cfv vx cv cH cfv wceq vx cv vv cv wceq wb cA cB cH wf1 vv cv cA
      wcel vx cv cA wcel wa wa vv cv cH cfv vx cv cH cfv wceq vv cv vx cv wceq
      vx cv vv cv wceq cA cB vv cv vx cv cH f1fveq vv cv vx cv eqcom syl6bb
      anassrs anbi1d syl5bb rexbidv vx cv vv cv wceq vu cv cH cfv vy cv cH cfv
      wceq vx cv vy cv cR wbr wa vy cA r19.42v syl6bb rexbidva vv cv cA wcel vx
      cv vv cv wceq vu cv cH cfv vy cv cH cfv wceq vx cv vy cv cR wbr wa vy cA
      wrex wa vx cA wrex vu cv cH cfv vy cv cH cfv wceq vv cv vy cv cR wbr wa
      vy cA wrex wb cA cB cH wf1 vu cv cH cfv vy cv cH cfv wceq vx cv vy cv cR
      wbr wa vy cA wrex vu cv cH cfv vy cv cH cfv wceq vv cv vy cv cR wbr wa vy
      cA wrex vx vv cv cA vx cv vv cv wceq vu cv cH cfv vy cv cH cfv wceq vx cv
      vy cv cR wbr wa vu cv cH cfv vy cv cH cfv wceq vv cv vy cv cR wbr wa vy
      cA vx cv vv cv wceq vx cv vy cv cR wbr vv cv vy cv cR wbr vu cv cH cfv vy
      cv cH cfv wceq vx cv vv cv vy cv cR breq1 anbi2d rexbidv ceqsrexv adantl
      bitrd cA cB cH wf1 vu cv cA wcel wa vu cv cH cfv vy cv cH cfv wceq vv cv
      vy cv cR wbr wa vy cA wrex vy cv vu cv wceq vv cv vy cv cR wbr wa vy cA
      wrex vv cv vu cv cR wbr cA cB cH wf1 vu cv cA wcel wa vu cv cH cfv vy cv
      cH cfv wceq vv cv vy cv cR wbr wa vy cv vu cv wceq vv cv vy cv cR wbr wa
      vy cA cA cB cH wf1 vu cv cA wcel wa vy cv cA wcel wa vu cv cH cfv vy cv
      cH cfv wceq vy cv vu cv wceq vv cv vy cv cR wbr cA cB cH wf1 vu cv cA
      wcel vy cv cA wcel vu cv cH cfv vy cv cH cfv wceq vy cv vu cv wceq wb cA
      cB cH wf1 vu cv cA wcel vy cv cA wcel wa wa vu cv cH cfv vy cv cH cfv
      wceq vu cv vy cv wceq vy cv vu cv wceq cA cB vu cv vy cv cH f1fveq vu cv
      vy cv eqcom syl6bb anassrs anbi1d rexbidva vu cv cA wcel vy cv vu cv wceq
      vv cv vy cv cR wbr wa vy cA wrex vv cv vu cv cR wbr wb cA cB cH wf1 vv cv
      vy cv cR wbr vv cv vu cv cR wbr vy vu cv cA vy cv vu cv vv cv cR breq2
      ceqsrexv adantl bitrd sylan9bb anandis syl5bb sylan9bbr an32s syl5rbb
      ralrimivva sylan vv vu cA cB cR cS cH df-isom sylanbrc $.
  $}

  ${
    $d A w x y z $.  $d B w x y z $.  $d H w x y z $.  $d R w x y z $.
    f1oiso2.1 $e |- S = { <. x , y >. |
      ( ( x e. B /\ y e. B ) /\ ( `' H ` x ) R ( `' H ` y ) ) } $.
    $( Any one-to-one onto function determines an isomorphism with an induced
       relation ` S ` .  (Contributed by Mario Carneiro, 9-Mar-2013.) $)
    f1oiso2 $p |- ( H : A -1-1-onto-> B -> H Isom R , S ( A , B ) ) $=
      cA cB cH wf1o cS vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv
      vw cv cR wbr wa vw cA wrex vz cA wrex vx vy copab wceq cA cB cR cS cH
      wiso cA cB cH wf1o cS vx cv cB wcel vy cv cB wcel wa vx cv cH ccnv cfv vy
      cv cH ccnv cfv cR wbr wa vx vy copab vx cv vz cv cH cfv wceq vy cv vw cv
      cH cfv wceq wa vz cv vw cv cR wbr wa vw cA wrex vz cA wrex vx vy copab
      f1oiso2.1 cA cB cH wf1o vx cv cB wcel vy cv cB wcel wa vx cv cH ccnv cfv
      vy cv cH ccnv cfv cR wbr wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv
      wceq wa vz cv vw cv cR wbr wa vw cA wrex vz cA wrex vx vy cA cB cH wf1o
      vx cv cB wcel vy cv cB wcel wa vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr
      wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr
      wa vw cA wrex vz cA wrex cA cB cH wf1o vx cv cB wcel vy cv cB wcel wa vx
      cv cH ccnv cfv vy cv cH ccnv cfv cR wbr vx cv vz cv cH cfv wceq vy cv vw
      cv cH cfv wceq wa vz cv vw cv cR wbr wa vw cA wrex vz cA wrex cA cB cH
      wf1o vx cv cB wcel vy cv cB wcel wa vx cv cH ccnv cfv vy cv cH ccnv cfv
      cR wbr w3a vx cv cH ccnv cfv cA wcel vx cv vx cv cH ccnv cfv cH cfv wceq
      vy cv vw cv cH cfv wceq wa vx cv cH ccnv cfv vw cv cR wbr wa vw cA wrex
      vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa
      vw cA wrex vz cA wrex cA cB cH wf1o vx cv cB wcel vy cv cB wcel wa vx cv
      cH ccnv cfv cA wcel vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr cA cB cH
      wf1o vx cv cB wcel vx cv cH ccnv cfv cA wcel vy cv cB wcel cA cB vx cv cH
      f1ocnvdm adantrr 3adant3 cA cB cH wf1o vx cv cB wcel vy cv cB wcel wa vx
      cv cH ccnv cfv vy cv cH ccnv cfv cR wbr w3a vy cv cH ccnv cfv cA wcel vx
      cv vx cv cH ccnv cfv cH cfv wceq vy cv vy cv cH ccnv cfv cH cfv wceq wa
      vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr vx cv vx cv cH ccnv cfv cH cfv
      wceq vy cv vw cv cH cfv wceq wa vx cv cH ccnv cfv vw cv cR wbr wa vw cA
      wrex cA cB cH wf1o vx cv cB wcel vy cv cB wcel wa vy cv cH ccnv cfv cA
      wcel vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr cA cB cH wf1o vy cv cB
      wcel vy cv cH ccnv cfv cA wcel vx cv cB wcel cA cB vy cv cH f1ocnvdm
      adantrl 3adant3 cA cB cH wf1o vx cv cB wcel vy cv cB wcel wa vx cv vx cv
      cH ccnv cfv cH cfv wceq vy cv vy cv cH ccnv cfv cH cfv wceq wa vx cv cH
      ccnv cfv vy cv cH ccnv cfv cR wbr cA cB cH wf1o vx cv cB wcel vx cv vx cv
      cH ccnv cfv cH cfv wceq vy cv cB wcel vy cv vy cv cH ccnv cfv cH cfv wceq
      cA cB cH wf1o vx cv cB wcel wa vx cv cH ccnv cfv cH cfv vx cv cA cB vx cv
      cH f1ocnvfv2 eqcomd cA cB cH wf1o vy cv cB wcel wa vy cv cH ccnv cfv cH
      cfv vy cv cA cB vy cv cH f1ocnvfv2 eqcomd anim12dan 3adant3 cA cB cH wf1o
      vx cv cB wcel vy cv cB wcel wa vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr
      simp3 vx cv vx cv cH ccnv cfv cH cfv wceq vy cv vw cv cH cfv wceq wa vx
      cv cH ccnv cfv vw cv cR wbr wa vx cv vx cv cH ccnv cfv cH cfv wceq vy cv
      vy cv cH ccnv cfv cH cfv wceq wa vx cv cH ccnv cfv vy cv cH ccnv cfv cR
      wbr wa vw vy cv cH ccnv cfv cA vw cv vy cv cH ccnv cfv wceq vx cv vx cv
      cH ccnv cfv cH cfv wceq vy cv vw cv cH cfv wceq wa vx cv vx cv cH ccnv
      cfv cH cfv wceq vy cv vy cv cH ccnv cfv cH cfv wceq wa vx cv cH ccnv cfv
      vw cv cR wbr vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr vw cv vy cv cH
      ccnv cfv wceq vy cv vw cv cH cfv wceq vy cv vy cv cH ccnv cfv cH cfv wceq
      vx cv vx cv cH ccnv cfv cH cfv wceq vw cv vy cv cH ccnv cfv wceq vw cv cH
      cfv vy cv cH ccnv cfv cH cfv vy cv vw cv vy cv cH ccnv cfv cH fveq2
      eqeq2d anbi2d vw cv vy cv cH ccnv cfv vx cv cH ccnv cfv cR breq2 anbi12d
      rspcev syl12anc vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv
      vw cv cR wbr wa vw cA wrex vx cv vx cv cH ccnv cfv cH cfv wceq vy cv vw
      cv cH cfv wceq wa vx cv cH ccnv cfv vw cv cR wbr wa vw cA wrex vz vx cv
      cH ccnv cfv cA vz cv vx cv cH ccnv cfv wceq vx cv vz cv cH cfv wceq vy cv
      vw cv cH cfv wceq wa vz cv vw cv cR wbr wa vx cv vx cv cH ccnv cfv cH cfv
      wceq vy cv vw cv cH cfv wceq wa vx cv cH ccnv cfv vw cv cR wbr wa vw cA
      vz cv vx cv cH ccnv cfv wceq vx cv vz cv cH cfv wceq vy cv vw cv cH cfv
      wceq wa vx cv vx cv cH ccnv cfv cH cfv wceq vy cv vw cv cH cfv wceq wa vz
      cv vw cv cR wbr vx cv cH ccnv cfv vw cv cR wbr vz cv vx cv cH ccnv cfv
      wceq vx cv vz cv cH cfv wceq vx cv vx cv cH ccnv cfv cH cfv wceq vy cv vw
      cv cH cfv wceq vz cv vx cv cH ccnv cfv wceq vz cv cH cfv vx cv cH ccnv
      cfv cH cfv vx cv vz cv vx cv cH ccnv cfv cH fveq2 eqeq2d anbi1d vz cv vx
      cv cH ccnv cfv vw cv cR breq1 anbi12d rexbidv rspcev syl2anc 3expib cA cB
      cH wf1o vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR
      wbr wa vx cv cB wcel vy cv cB wcel wa vx cv cH ccnv cfv vy cv cH ccnv cfv
      cR wbr wa vz vw cA cA cA cB cH wf1o vz cv cA wcel vw cv cA wcel wa vx cv
      vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa vx cv
      cB wcel vy cv cB wcel wa vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr wa cA
      cB cH wf1o vz cv cA wcel vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv
      vw cv cH cfv wceq wa vz cv vw cv cR wbr wa w3a vx cv cB wcel vy cv cB
      wcel vx cv cH ccnv cfv vy cv cH ccnv cfv cR wbr cA cB cH wf1o vz cv cA
      wcel vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa
      vz cv vw cv cR wbr wa w3a vx cv vz cv cH cfv cB vx cv vz cv cH cfv wceq
      vy cv vw cv cH cfv wceq vz cv vw cv cR wbr cA cB cH wf1o vz cv cA wcel vw
      cv cA wcel wa simp3ll cA cB cH wf1o vz cv cA wcel vw cv cA wcel wa vx cv
      vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa w3a cA
      cB cH wf1o vz cv cA wcel vz cv cH cfv cB wcel cA cB cH wf1o vz cv cA wcel
      vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv
      vw cv cR wbr wa simp1 cA cB cH wf1o vz cv cA wcel vw cv cA wcel vx cv vz
      cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa simp2l cA
      cB cH wf1o cA cB cH wf vz cv cA wcel vz cv cH cfv cB wcel cA cB cH f1of
      cA cB vz cv cH ffvelrn sylan syl2anc eqeltrd cA cB cH wf1o vz cv cA wcel
      vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv
      vw cv cR wbr wa w3a vy cv vw cv cH cfv cB vx cv vz cv cH cfv wceq vy cv
      vw cv cH cfv wceq vz cv vw cv cR wbr cA cB cH wf1o vz cv cA wcel vw cv cA
      wcel wa simp3lr cA cB cH wf1o vz cv cA wcel vw cv cA wcel wa vx cv vz cv
      cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa w3a cA cB cH
      wf1o vw cv cA wcel vw cv cH cfv cB wcel cA cB cH wf1o vz cv cA wcel vw cv
      cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv
      cR wbr wa simp1 cA cB cH wf1o vz cv cA wcel vw cv cA wcel vx cv vz cv cH
      cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa simp2r cA cB cH
      wf1o cA cB cH wf vw cv cA wcel vw cv cH cfv cB wcel cA cB cH f1of cA cB
      vw cv cH ffvelrn sylan syl2anc eqeltrd cA cB cH wf1o vz cv cA wcel vw cv
      cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv
      cR wbr wa w3a vz cv vw cv vx cv cH ccnv cfv vy cv cH ccnv cfv cR cA cB cH
      wf1o vz cv cA wcel vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv
      cH cfv wceq wa vz cv vw cv cR wbr simp3r cA cB cH wf1o vz cv cA wcel vw
      cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw
      cv cR wbr wa w3a vz cv cH cfv vx cv wceq vx cv cH ccnv cfv vz cv wceq cA
      cB cH wf1o vz cv cA wcel vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv
      vw cv cH cfv wceq wa vz cv vw cv cR wbr wa w3a vx cv vz cv cH cfv vx cv
      vz cv cH cfv wceq vy cv vw cv cH cfv wceq vz cv vw cv cR wbr cA cB cH
      wf1o vz cv cA wcel vw cv cA wcel wa simp3ll eqcomd cA cB cH wf1o vz cv cA
      wcel vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa
      vz cv vw cv cR wbr wa w3a cA cB cH wf1o vz cv cA wcel vz cv cH cfv vx cv
      wceq vx cv cH ccnv cfv vz cv wceq wi cA cB cH wf1o vz cv cA wcel vw cv cA
      wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR
      wbr wa simp1 cA cB cH wf1o vz cv cA wcel vw cv cA wcel vx cv vz cv cH cfv
      wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa simp2l cA cB vz cv
      vx cv cH f1ocnvfv syl2anc mpd cA cB cH wf1o vz cv cA wcel vw cv cA wcel
      wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr
      wa w3a vw cv cH cfv vy cv wceq vy cv cH ccnv cfv vw cv wceq cA cB cH wf1o
      vz cv cA wcel vw cv cA wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv
      wceq wa vz cv vw cv cR wbr wa w3a vy cv vw cv cH cfv vx cv vz cv cH cfv
      wceq vy cv vw cv cH cfv wceq vz cv vw cv cR wbr cA cB cH wf1o vz cv cA
      wcel vw cv cA wcel wa simp3lr eqcomd cA cB cH wf1o vz cv cA wcel vw cv cA
      wcel wa vx cv vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR
      wbr wa w3a cA cB cH wf1o vw cv cA wcel vw cv cH cfv vy cv wceq vy cv cH
      ccnv cfv vw cv wceq wi cA cB cH wf1o vz cv cA wcel vw cv cA wcel wa vx cv
      vz cv cH cfv wceq vy cv vw cv cH cfv wceq wa vz cv vw cv cR wbr wa simp1
      cA cB cH wf1o vz cv cA wcel vw cv cA wcel vx cv vz cv cH cfv wceq vy cv
      vw cv cH cfv wceq wa vz cv vw cv cR wbr wa simp2r cA cB vw cv vy cv cH
      f1ocnvfv syl2anc mpd 3brtr4d jca31 3exp rexlimdvv impbid opabbidv syl5eq
      vz vw vx vy cA cB cR cS cH f1oiso mpdan $.
  $}

  ${
    $d z w R $.  $d x y z w S $.  $d z w A $.  $d z w B $.  $d x y z w F $.
    f1owe.1 $e |- R = { <. x , y >. | ( F ` x ) S ( F ` y ) } $.
    $( Well-ordering of isomorphic relations.  (Contributed by NM,
       4-Mar-1997.) $)
    f1owe $p |- ( F : A -1-1-onto-> B -> ( S We B -> R We A ) ) $=
      cA cB cF wf1o cA cR wwe cB cS wwe cA cB cF wf1o vz cv vw cv cR wbr vz cv
      cF cfv vw cv cF cfv cS wbr wb vw cA wral vz cA wral cA cR wwe cB cS wwe
      wb vz cv vw cv cR wbr vz cv cF cfv vw cv cF cfv cS wbr wb vz vw cA vx cv
      cF cfv vy cv cF cfv cS wbr vz cv cF cfv vy cv cF cfv cS wbr vz cv cF cfv
      vw cv cF cfv cS wbr vx vy vz cv vw cv cA cA cR vx cv vz cv wceq vx cv cF
      cfv vz cv cF cfv vy cv cF cfv cS vx cv vz cv cF fveq2 breq1d vy cv vw cv
      wceq vy cv cF cfv vw cv cF cfv vz cv cF cfv cS vy cv vw cv cF fveq2
      breq2d f1owe.1 brabg rgen2a cA cB cF wf1o vz cv vw cv cR wbr vz cv cF cfv
      vw cv cF cfv cS wbr wb vw cA wral vz cA wral wa cA cB cR cS cF wiso cA cR
      wwe cB cS wwe wb vz vw cA cB cR cS cF df-isom cA cB cR cS cF isowe sylbir
      mpan2 biimprd $.
  $}

  ${
    $d z w v u f R $.  $d x y z w v u f S $.  $d z w v u f A $.
    $d z w v u f B $.  $d x y z w v u f F $.
    f1oweALT.1 $e |- R = { <. x , y >. | ( F ` x ) S ( F ` y ) } $.
    $( Well-ordering of isomorphic relations.  (This version is proved directly
       instead of with the isomorphism predicate.)  (Contributed by NM,
       4-Mar-1997.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    f1oweALT $p |- ( F : A -1-1-onto-> B -> ( S We B -> R We A ) ) $=
      cA cB cF wf1o cB cS wfr vu cv vf cv cS wbr vu cv vf cv wceq vf cv vu cv
      cS wbr w3o vf cB wral vu cB wral wa cA cR wfr vw cv vv cv cR wbr vw cv vv
      cv wceq vv cv vw cv cR wbr w3o vv cA wral vw cA wral wa cB cS wwe cA cR
      wwe cA cB cF wf1o cB cS wfr cA cR wfr vu cv vf cv cS wbr vu cv vf cv wceq
      vf cv vu cv cS wbr w3o vf cB wral vu cB wral vw cv vv cv cR wbr vw cv vv
      cv wceq vv cv vw cv cR wbr w3o vv cA wral vw cA wral cA cB cF wf1o cA cB
      cF wfo cB cS wfr cA cR wfr wi cA cB cF f1ofo cA cB cF wfo cF cA wfn cF
      crn cB wceq wa cB cS wfr cA cR wfr wi cA cB cF df-fo cF crn cB wceq cB cS
      wfr cF crn cS wfr cF cA wfn cA cR wfr cF crn cB wceq cF crn cS wfr cB cS
      wfr cF crn cB cS freq2 biimprd cF cA wfn cF wfun cF cdm cA wceq wa cF crn
      cS wfr cA cR wfr wi cF cA df-fn cF wfun cF crn cS wfr cF cdm cR wfr cF
      cdm cA wceq cA cR wfr cF wfun cF crn cS wfr vz cv cF cdm wss vz cv c0 wne
      wa vv cv vw cv cR wbr wn vv vz cv wral vw vz cv wrex wi vz wal cF cdm cR
      wfr cF wfun cF crn cS wfr vz cv cF cdm wss vz cv c0 wne wa vv cv vw cv cR
      wbr wn vv vz cv wral vw vz cv wrex wi vz cF wfun cF crn cS wfr vz cv cF
      cdm wss vz cv c0 wne vv cv vw cv cR wbr wn vv vz cv wral vw vz cv wrex cF
      wfun vz cv cF cdm wss cF crn cS wfr vz cv c0 wne vv cv vw cv cR wbr wn vv
      vz cv wral vw vz cv wrex wi cF wfun vz cv cF cdm wss vz cv c0 wne cF crn
      cS wfr vv cv vw cv cR wbr wn vv vz cv wral vw vz cv wrex cF wfun vz cv cF
      cdm wss vz cv c0 wne cF crn cS wfr vv cv vw cv cR wbr wn vv vz cv wral vw
      vz cv wrex cF wfun vz cv cF cdm wss wa vz cv c0 wne cF crn cS wfr wa vf
      cv vu cv cS wbr wn vf cF vz cv cima wral vu cF vz cv cima wrex vv cv vw
      cv cR wbr wn vv vz cv wral vw vz cv wrex cF wfun vz cv cF cdm wss wa vz
      cv c0 wne cF crn cS wfr vf cv vu cv cS wbr wn vf cF vz cv cima wral vu cF
      vz cv cima wrex cF wfun vz cv cF cdm wss vz cv c0 wne cF crn cS wfr vf cv
      vu cv cS wbr wn vf cF vz cv cima wral vu cF vz cv cima wrex wi wi cF wfun
      cF wfun vz cv cF cdm wss wa vz cv c0 wne cF crn cS wfr vf cv vu cv cS wbr
      wn vf cF vz cv cima wral vu cF vz cv cima wrex wi cF wfun cF crn cS wfr
      cF wfun vz cv cF cdm wss wa vz cv c0 wne wa vf cv vu cv cS wbr wn vf cF
      vz cv cima wral vu cF vz cv cima wrex cF crn cS wfr vw cv cF crn wss vw
      cv c0 wne wa vf cv vu cv cS wbr wn vf vw cv wral vu vw cv wrex wi vw wal
      cF wfun cF wfun vz cv cF cdm wss wa vz cv c0 wne wa vf cv vu cv cS wbr wn
      vf cF vz cv cima wral vu cF vz cv cima wrex wi vw vu vf cF crn cS df-fr
      cF wfun cF vz cv cima cvv wcel vw cv cF crn wss vw cv c0 wne wa vf cv vu
      cv cS wbr wn vf vw cv wral vu vw cv wrex wi vw wal cF wfun vz cv cF cdm
      wss wa vz cv c0 wne wa vf cv vu cv cS wbr wn vf cF vz cv cima wral vu cF
      vz cv cima wrex wi wi cF vz cv vz vex funimaex cF wfun vz cv cF cdm wss
      wa vz cv c0 wne wa cF vz cv cima cF crn wss cF vz cv cima c0 wne wa cF vz
      cv cima cvv wcel vw cv cF crn wss vw cv c0 wne wa vf cv vu cv cS wbr wn
      vf vw cv wral vu vw cv wrex wi vw wal vf cv vu cv cS wbr wn vf cF vz cv
      cima wral vu cF vz cv cima wrex cF wfun vz cv cF cdm wss wa vz cv c0 wne
      wa cF vz cv cima c0 wne cF vz cv cima cF crn wss cF wfun vz cv cF cdm wss
      wa vz cv c0 wne cF vz cv cima c0 wne vz cv c0 wne vw cv vz cv wcel vw wex
      cF wfun vz cv cF cdm wss wa cF vz cv cima c0 wne vw vz cv n0 cF wfun vz
      cv cF cdm wss wa vw cv vz cv wcel cF vz cv cima c0 wne vw cF wfun vz cv
      cF cdm wss wa vw cv vz cv wcel vw cv cF cfv cF vz cv cima wcel cF vz cv
      cima c0 wne vz cv vw cv cF funfvima2 cF vz cv cima vw cv cF cfv ne0i syl6
      exlimdv syl5bi imp cF vz cv imassrn jctil vw cv cF crn wss vw cv c0 wne
      wa vf cv vu cv cS wbr wn vf vw cv wral vu vw cv wrex wi cF vz cv cima cF
      crn wss cF vz cv cima c0 wne wa vf cv vu cv cS wbr wn vf cF vz cv cima
      wral vu cF vz cv cima wrex wi vw cF vz cv cima cvv vw cv cF vz cv cima
      wceq vw cv cF crn wss vw cv c0 wne wa cF vz cv cima cF crn wss cF vz cv
      cima c0 wne wa vf cv vu cv cS wbr wn vf vw cv wral vu vw cv wrex vf cv vu
      cv cS wbr wn vf cF vz cv cima wral vu cF vz cv cima wrex vw cv cF vz cv
      cima wceq vw cv cF crn wss cF vz cv cima cF crn wss vw cv c0 wne cF vz cv
      cima c0 wne vw cv cF vz cv cima cF crn sseq1 vw cv cF vz cv cima c0 neeq1
      anbi12d vf cv vu cv cS wbr wn vf vw cv wral vf cv vu cv cS wbr wn vf cF
      vz cv cima wral vu vw cv cF vz cv cima vf cv vu cv cS wbr wn vf vw cv cF
      vz cv cima raleq rexeqbi1dv imbi12d spcgv syl7 syl syl5bi com23 exp3a
      anabsi5 imp3a cF wfun vz cv cF cdm wss wa vz cv cF vz cv cima cF vz cv
      cres wfo vv cv vw cv cR wbr wn vv vz cv wral vw vz cv wrex vf cv vu cv cS
      wbr wn vf cF vz cv cima wral vu cF vz cv cima wrex wb vz cv cF fores vv
      cv vw cv cR wbr wn vv vz cv wral vw vz cv wrex vv cv cF vz cv cres cfv vw
      cv cF vz cv cres cfv cS wbr wn vv vz cv wral vw vz cv wrex vz cv cF vz cv
      cima cF vz cv cres wfo vf cv vu cv cS wbr wn vf cF vz cv cima wral vu cF
      vz cv cima wrex vv cv vw cv cR wbr wn vv vz cv wral vv cv cF vz cv cres
      cfv vw cv cF vz cv cres cfv cS wbr wn vv vz cv wral vw vz cv vw cv vz cv
      wcel vv cv vw cv cR wbr wn vv cv cF vz cv cres cfv vw cv cF vz cv cres
      cfv cS wbr wn vv vz cv vw cv vz cv wcel vv cv vz cv wcel wa vv cv vw cv
      cR wbr vv cv cF vz cv cres cfv vw cv cF vz cv cres cfv cS wbr vw cv vz cv
      wcel vv cv vz cv wcel wa vv cv cF vz cv cres cfv vw cv cF vz cv cres cfv
      cS wbr vv cv cF cfv vw cv cF cfv cS wbr vv cv vw cv cR wbr vv cv vz cv
      wcel vw cv vz cv wcel vv cv cF vz cv cres cfv vv cv cF cfv vw cv cF vz cv
      cres cfv vw cv cF cfv cS vv cv vz cv cF fvres vw cv vz cv cF fvres
      breqan12rd vx cv cF cfv vy cv cF cfv cS wbr vv cv cF cfv vy cv cF cfv cS
      wbr vv cv cF cfv vw cv cF cfv cS wbr vx vy vv cv vw cv cR vv vex vw vex
      vx cv vv cv wceq vx cv cF cfv vv cv cF cfv vy cv cF cfv cS vx cv vv cv cF
      fveq2 breq1d vy cv vw cv wceq vy cv cF cfv vw cv cF cfv vv cv cF cfv cS
      vy cv vw cv cF fveq2 breq2d f1oweALT.1 brab syl6rbbr notbid ralbidva
      rexbiia vz cv cF vz cv cima cF vz cv cres wfo vv cv cF vz cv cres cfv vw
      cv cF vz cv cres cfv cS wbr wn vv vz cv wral vw vz cv wrex vf cv vw cv cF
      vz cv cres cfv cS wbr wn vf cF vz cv cima wral vw vz cv wrex vf cv vu cv
      cS wbr wn vf cF vz cv cima wral vu cF vz cv cima wrex vz cv cF vz cv cima
      cF vz cv cres wfo vv cv cF vz cv cres cfv vw cv cF vz cv cres cfv cS wbr
      wn vv vz cv wral vf cv vw cv cF vz cv cres cfv cS wbr wn vf cF vz cv cima
      wral vw vz cv vv cv cF vz cv cres cfv vw cv cF vz cv cres cfv cS wbr wn
      vf cv vw cv cF vz cv cres cfv cS wbr wn vv vf vz cv cF vz cv cima cF vz
      cv cres vv cv cF vz cv cres cfv vf cv wceq vv cv cF vz cv cres cfv vw cv
      cF vz cv cres cfv cS wbr vf cv vw cv cF vz cv cres cfv cS wbr vv cv cF vz
      cv cres cfv vf cv vw cv cF vz cv cres cfv cS breq1 notbid cbvfo rexbidv
      vf cv vw cv cF vz cv cres cfv cS wbr wn vf cF vz cv cima wral vf cv vu cv
      cS wbr wn vf cF vz cv cima wral vw vu vz cv cF vz cv cima cF vz cv cres
      vw cv cF vz cv cres cfv vu cv wceq vf cv vw cv cF vz cv cres cfv cS wbr
      wn vf cv vu cv cS wbr wn vf cF vz cv cima vw cv cF vz cv cres cfv vu cv
      wceq vf cv vw cv cF vz cv cres cfv cS wbr vf cv vu cv cS wbr vw cv cF vz
      cv cres cfv vu cv vf cv cS breq2 notbid ralbidv cbvexfo bitrd syl5bb syl
      sylibrd exp4b com34 com23 imp4a alrimdv vz vw vv cF cdm cR df-fr syl6ibr
      cF cdm cA wceq cF cdm cR wfr cA cR wfr cF cdm cA cR freq2 biimpd sylan9
      sylbi sylan9r sylbi syl cA cB cF wf1o vw cv vv cv cR wbr vw cv vv cv wceq
      vv cv vw cv cR wbr w3o vv cA wral vw cA wral vu cv vf cv cS wbr vu cv vf
      cv wceq vf cv vu cv cS wbr w3o vf cB wral vu cB wral cA cB cF wf1o cA cB
      cF wf1 cA cB cF wfo wa vw cv vv cv cR wbr vw cv vv cv wceq vv cv vw cv cR
      wbr w3o vv cA wral vw cA wral vu cv vf cv cS wbr vu cv vf cv wceq vf cv
      vu cv cS wbr w3o vf cB wral vu cB wral wb cA cB cF df-f1o cA cB cF wf1 vw
      cv vv cv cR wbr vw cv vv cv wceq vv cv vw cv cR wbr w3o vv cA wral vw cA
      wral vw cv cF cfv vv cv cF cfv cS wbr vw cv cF cfv vv cv cF cfv wceq vv
      cv cF cfv vw cv cF cfv cS wbr w3o vv cA wral vw cA wral cA cB cF wfo vu
      cv vf cv cS wbr vu cv vf cv wceq vf cv vu cv cS wbr w3o vf cB wral vu cB
      wral cA cB cF wf1 vw cv vv cv cR wbr vw cv vv cv wceq vv cv vw cv cR wbr
      w3o vw cv cF cfv vv cv cF cfv cS wbr vw cv cF cfv vv cv cF cfv wceq vv cv
      cF cfv vw cv cF cfv cS wbr w3o vw vv cA cA cA cB cF wf1 vw cv cA wcel vv
      cv cA wcel wa wa vw cv vv cv cR wbr vw cv cF cfv vv cv cF cfv cS wbr vw
      cv vv cv wceq vw cv cF cfv vv cv cF cfv wceq vv cv vw cv cR wbr vv cv cF
      cfv vw cv cF cfv cS wbr vw cv vv cv cR wbr vw cv cF cfv vv cv cF cfv cS
      wbr wb cA cB cF wf1 vw cv cA wcel vv cv cA wcel wa wa vx cv cF cfv vy cv
      cF cfv cS wbr vw cv cF cfv vy cv cF cfv cS wbr vw cv cF cfv vv cv cF cfv
      cS wbr vx vy vw cv vv cv cR vw vex vv vex vx cv vw cv wceq vx cv cF cfv
      vw cv cF cfv vy cv cF cfv cS vx cv vw cv cF fveq2 breq1d vy cv vv cv wceq
      vy cv cF cfv vv cv cF cfv vw cv cF cfv cS vy cv vv cv cF fveq2 breq2d
      f1oweALT.1 brab a1i cA cB cF wf1 vw cv cA wcel vv cv cA wcel wa wa vw cv
      cF cfv vv cv cF cfv wceq vw cv vv cv wceq cA cB vw cv vv cv cF f1fveq
      bicomd vv cv vw cv cR wbr vv cv cF cfv vw cv cF cfv cS wbr wb cA cB cF
      wf1 vw cv cA wcel vv cv cA wcel wa wa vx cv cF cfv vy cv cF cfv cS wbr vv
      cv cF cfv vy cv cF cfv cS wbr vv cv cF cfv vw cv cF cfv cS wbr vx vy vv
      cv vw cv cR vv vex vw vex vx cv vv cv wceq vx cv cF cfv vv cv cF cfv vy
      cv cF cfv cS vx cv vv cv cF fveq2 breq1d vy cv vw cv wceq vy cv cF cfv vw
      cv cF cfv vv cv cF cfv cS vy cv vw cv cF fveq2 breq2d f1oweALT.1 brab a1i
      3orbi123d 2ralbidva cA cB cF wfo vw cv cF cfv vv cv cF cfv cS wbr vw cv
      cF cfv vv cv cF cfv wceq vv cv cF cfv vw cv cF cfv cS wbr w3o vv cA wral
      vw cA wral vu cv vv cv cF cfv cS wbr vu cv vv cv cF cfv wceq vv cv cF cfv
      vu cv cS wbr w3o vv cA wral vu cB wral vu cv vf cv cS wbr vu cv vf cv
      wceq vf cv vu cv cS wbr w3o vf cB wral vu cB wral vw cv cF cfv vv cv cF
      cfv cS wbr vw cv cF cfv vv cv cF cfv wceq vv cv cF cfv vw cv cF cfv cS
      wbr w3o vv cA wral vu cv vv cv cF cfv cS wbr vu cv vv cv cF cfv wceq vv
      cv cF cfv vu cv cS wbr w3o vv cA wral vw vu cA cB cF vw cv cF cfv vu cv
      wceq vw cv cF cfv vv cv cF cfv cS wbr vw cv cF cfv vv cv cF cfv wceq vv
      cv cF cfv vw cv cF cfv cS wbr w3o vu cv vv cv cF cfv cS wbr vu cv vv cv
      cF cfv wceq vv cv cF cfv vu cv cS wbr w3o vv cA vw cv cF cfv vu cv wceq
      vw cv cF cfv vv cv cF cfv cS wbr vu cv vv cv cF cfv cS wbr vw cv cF cfv
      vv cv cF cfv wceq vu cv vv cv cF cfv wceq vv cv cF cfv vw cv cF cfv cS
      wbr vv cv cF cfv vu cv cS wbr vw cv cF cfv vu cv vv cv cF cfv cS breq1 vw
      cv cF cfv vu cv vv cv cF cfv eqeq1 vw cv cF cfv vu cv vv cv cF cfv cS
      breq2 3orbi123d ralbidv cbvfo cA cB cF wfo vu cv vv cv cF cfv cS wbr vu
      cv vv cv cF cfv wceq vv cv cF cfv vu cv cS wbr w3o vv cA wral vu cv vf cv
      cS wbr vu cv vf cv wceq vf cv vu cv cS wbr w3o vf cB wral vu cB vu cv vv
      cv cF cfv cS wbr vu cv vv cv cF cfv wceq vv cv cF cfv vu cv cS wbr w3o vu
      cv vf cv cS wbr vu cv vf cv wceq vf cv vu cv cS wbr w3o vv vf cA cB cF vv
      cv cF cfv vf cv wceq vu cv vv cv cF cfv cS wbr vu cv vf cv cS wbr vu cv
      vv cv cF cfv wceq vu cv vf cv wceq vv cv cF cfv vu cv cS wbr vf cv vu cv
      cS wbr vv cv cF cfv vf cv vu cv cS breq2 vv cv cF cfv vf cv vu cv eqeq2
      vv cv cF cfv vf cv vu cv cS breq1 3orbi123d cbvfo ralbidv bitrd sylan9bb
      sylbi biimprd anim12d vu vf cB cS dfwe2 vw vv cA cR dfwe2 3imtr4g $.
  $}

  ${
    $d A a b c $.  $d R b c $.  $d F a b c $.
    $( A set-like well-ordering has no nontrivial automorphisms.  (Contributed
       by Stefan O'Rear, 16-Nov-2014.)  (Revised by Mario Carneiro,
       25-Jun-2015.) $)
    weniso $p |- ( ( R We A /\ R Se A /\ F Isom R , R ( A , A ) ) ->
        F = ( _I |` A ) ) $=
      cA cR wwe cA cR wse cA cA cR cR cF wiso w3a cF cid cA cres wceq va cv cF
      cfv va cv cid cA cres cfv wceq va cA wral cA cR wwe cA cR wse cA cA cR cR
      cF wiso w3a va cv cF cfv va cv wceq va cA wral va cv cF cfv va cv cid cA
      cres cfv wceq va cA wral cA cR wwe cA cR wse cA cA cR cR cF wiso w3a va
      cv cF cfv va cv wceq va cA wral va cv cF cfv va cv wceq va cA wral wn va
      cv cF cfv va cv wceq wn va cA crab c0 wne cA cR wwe cA cR wse cA cA cR cR
      cF wiso w3a va cv cF cfv va cv wceq va cA wral va cv cF cfv va cv wceq wn
      va cA crab c0 wne va cv cF cfv va cv wceq wn va cA wrex va cv cF cfv va
      cv wceq va cA wral wn va cv cF cfv va cv wceq wn va cA rabn0 va cv cF cfv
      va cv wceq va cA rexnal bitri cA cR wwe cA cR wse cA cA cR cR cF wiso w3a
      va cv cF cfv va cv wceq wn va cA crab c0 wne vc cv vb cv cR wbr wn vc va
      cv cF cfv va cv wceq wn va cA crab wral vb va cv cF cfv va cv wceq wn va
      cA crab wrex va cv cF cfv va cv wceq va cA wral cA cR wwe cA cR wse cA cA
      cR cR cF wiso w3a va cv cF cfv va cv wceq wn va cA crab c0 wne vc cv vb
      cv cR wbr wn vc va cv cF cfv va cv wceq wn va cA crab wral vb va cv cF
      cfv va cv wceq wn va cA crab wrex cA cR wwe cA cR wse cA cA cR cR cF wiso
      w3a va cv cF cfv va cv wceq wn va cA crab c0 wne wa vc cv vb cv cR wbr wn
      vc va cv cF cfv va cv wceq wn va cA crab wral vb va cv cF cfv va cv wceq
      wn va cA crab wreu vc cv vb cv cR wbr wn vc va cv cF cfv va cv wceq wn va
      cA crab wral vb va cv cF cfv va cv wceq wn va cA crab wrex cA cR wwe cA
      cR wse cA cA cR cR cF wiso w3a va cv cF cfv va cv wceq wn va cA crab c0
      wne wa cA cR wwe cA cR wse va cv cF cfv va cv wceq wn va cA crab cA wss
      va cv cF cfv va cv wceq wn va cA crab c0 wne vc cv vb cv cR wbr wn vc va
      cv cF cfv va cv wceq wn va cA crab wral vb va cv cF cfv va cv wceq wn va
      cA crab wreu cA cR wwe cA cR wse cA cA cR cR cF wiso va cv cF cfv va cv
      wceq wn va cA crab c0 wne simpl1 cA cR wwe cA cR wse cA cA cR cR cF wiso
      va cv cF cfv va cv wceq wn va cA crab c0 wne simpl2 va cv cF cfv va cv
      wceq wn va cA crab cA wss cA cR wwe cA cR wse cA cA cR cR cF wiso w3a va
      cv cF cfv va cv wceq wn va cA crab c0 wne wa va cv cF cfv va cv wceq wn
      va cA ssrab2 a1i cA cR wwe cA cR wse cA cA cR cR cF wiso w3a va cv cF cfv
      va cv wceq wn va cA crab c0 wne simpr vb vc cA va cv cF cfv va cv wceq wn
      va cA crab cR wereu2 syl22anc vc cv vb cv cR wbr wn vc va cv cF cfv va cv
      wceq wn va cA crab wral vb va cv cF cfv va cv wceq wn va cA crab reurex
      syl ex cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vc cv vb cv cR wbr wn
      vc va cv cF cfv va cv wceq wn va cA crab wral va cv cF cfv va cv wceq va
      cA wral vb va cv cF cfv va cv wceq wn va cA crab vb cv va cv cF cfv va cv
      wceq wn va cA crab wcel vb cv cA wcel vb cv cF cfv vb cv wceq wn wa cA cR
      wwe cA cR wse cA cA cR cR cF wiso w3a vc cv vb cv cR wbr wn vc va cv cF
      cfv va cv wceq wn va cA crab wral va cv cF cfv va cv wceq va cA wral wi
      va cv cF cfv va cv wceq wn vb cv cF cfv vb cv wceq wn va vb cv cA va cv
      vb cv wceq va cv cF cfv va cv wceq vb cv cF cfv vb cv wceq va cv vb cv
      wceq va cv cF cfv vb cv cF cfv va cv vb cv va cv vb cv cF fveq2 va cv vb
      cv wceq id eqeq12d notbid elrab cA cR wwe cA cR wse cA cA cR cR cF wiso
      w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa vc cv vb cv cR wbr wn vc
      va cv cF cfv va cv wceq wn va cA crab wral va cv cF cfv va cv wceq va cA
      wral wi vc cv vb cv cR wbr wn vc va cv cF cfv va cv wceq wn va cA crab
      wral vc cv vb cv cR wbr vc cv cF cfv vc cv wceq wi vc cA wral cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa va cv cF cfv va cv wceq va cA wral vc cv vb cv cR wbr wn vc va
      cv cF cfv va cv wceq wn va cA crab wral vc cv cF cfv vc cv wceq wn vc cv
      vb cv cR wbr wn wi vc cA wral vc cv vb cv cR wbr vc cv cF cfv vc cv wceq
      wi vc cA wral va cv cF cfv va cv wceq wn vc cv cF cfv vc cv wceq wn vc cv
      vb cv cR wbr wn vc va cA va cv vc cv wceq va cv cF cfv va cv wceq vc cv
      cF cfv vc cv wceq va cv vc cv wceq va cv cF cfv vc cv cF cfv va cv vc cv
      va cv vc cv cF fveq2 va cv vc cv wceq id eqeq12d notbid ralrab vc cv cF
      cfv vc cv wceq wn vc cv vb cv cR wbr wn wi vc cv vb cv cR wbr vc cv cF
      cfv vc cv wceq wi vc cA vc cv vb cv cR wbr vc cv cF cfv vc cv wceq wi vc
      cv cF cfv vc cv wceq wn vc cv vb cv cR wbr wn wi vc cv vb cv cR wbr vc cv
      cF cfv vc cv wceq con34b bicomi ralbii bitri cA cR wwe cA cR wse cA cA cR
      cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF
      cfv vb cv cR wbr vc cv vb cv cR wbr vc cv cF cfv vc cv wceq wi vc cA wral
      va cv cF cfv va cv wceq va cA wral wi vb cv vb cv cF cfv cR wbr cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa vb cv cF cfv vb cv cR wbr wa vc cv vb cv cR wbr vc cv cF cfv vc
      cv wceq wi vc cA wral vb cv cF cfv cF cfv vb cv cF cfv wceq va cv cF cfv
      va cv wceq va cA wral cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv
      cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF cfv vb cv cR wbr vc cv
      vb cv cR wbr vc cv cF cfv vc cv wceq wi vc cA wral vb cv cF cfv cF cfv vb
      cv cF cfv wceq wi cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn wa wa vc cv vb cv cR wbr vc cv cF cfv vc
      cv wceq wi vc cA wral vb cv cF cfv vb cv cR wbr vb cv cF cfv cF cfv vb cv
      cF cfv wceq cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb
      cv cF cfv vb cv wceq wn wa wa vb cv cF cfv cA wcel vc cv vb cv cR wbr vc
      cv cF cfv vc cv wceq wi vc cA wral vb cv cF cfv vb cv cR wbr vb cv cF cfv
      cF cfv vb cv cF cfv wceq wi wi cA cR wwe cA cR wse cA cA cR cR cF wiso
      w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF wf vb cv cA
      wcel vb cv cF cfv cA wcel cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb
      cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF wf1o cA cA cF wf cA
      cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv
      wceq wn wa wa cA cA cR cR cF wiso cA cA cF wf1o cA cR wwe cA cR wse cA cA
      cR cR cF wiso vb cv cA wcel vb cv cF cfv vb cv wceq wn wa simpl3 cA cA cR
      cR cF isof1o syl cA cA cF f1of syl cA cR wwe cA cR wse cA cA cR cR cF
      wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA cA vb cv cF
      ffvelrn syl2anc vc cv vb cv cR wbr vc cv cF cfv vc cv wceq wi vb cv cF
      cfv vb cv cR wbr vb cv cF cfv cF cfv vb cv cF cfv wceq wi vc vb cv cF cfv
      cA vc cv vb cv cF cfv wceq vc cv vb cv cR wbr vb cv cF cfv vb cv cR wbr
      vc cv cF cfv vc cv wceq vb cv cF cfv cF cfv vb cv cF cfv wceq vc cv vb cv
      cF cfv vb cv cR breq1 vc cv vb cv cF cfv wceq vc cv cF cfv vb cv cF cfv
      cF cfv vc cv vb cv cF cfv vc cv vb cv cF cfv cF fveq2 vc cv vb cv cF cfv
      wceq id eqeq12d imbi12d rspcv syl com23 imp cA cR wwe cA cR wse cA cA cR
      cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF
      cfv cF cfv vb cv cF cfv wceq va cv cF cfv va cv wceq va cA wral wi vb cv
      cF cfv vb cv cR wbr cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF cfv cF cfv vb cv cF cfv
      wceq vb cv cF cfv vb cv wceq va cv cF cfv va cv wceq va cA wral cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa cA cA cF wf1 vb cv cF cfv cA wcel vb cv cA wcel vb cv cF cfv cF
      cfv vb cv cF cfv wceq vb cv cF cfv vb cv wceq wb cA cR wwe cA cR wse cA
      cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA
      cF wf1o cA cA cF wf1 cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF wf1o
      cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv vb cv
      wceq wn wa simpl3 cA cA cR cR cF isof1o syl cA cA cF f1of1 syl cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa cA cA cF wf vb cv cA wcel vb cv cF cfv cA wcel cA cR wwe cA cR
      wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa
      wa cA cA cF wf1o cA cA cF wf cA cR wwe cA cR wse cA cA cR cR cF wiso w3a
      vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA
      cF wf1o cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF
      cfv vb cv wceq wn wa simpl3 cA cA cR cR cF isof1o syl cA cA cF f1of syl
      cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb
      cv wceq wn simprl cA cA vb cv cF ffvelrn syl2anc cA cR wwe cA cR wse cA
      cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA
      cA vb cv cF cfv vb cv cF f1fveq syl12anc vb cv cF cfv vb cv wceq wn vb cv
      cF cfv vb cv wceq va cv cF cfv va cv wceq va cA wral wi cA cR wwe cA cR
      wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq va cv
      cF cfv va cv wceq va cA wral pm2.21 ad2antll sylbid adantr syld cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa vb cv vb cv cF cfv cR wbr wa vc cv vb cv cR wbr vc cv cF cfv vc
      cv wceq wi vc cA wral vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv wceq va
      cv cF cfv va cv wceq va cA wral cA cR wwe cA cR wse cA cA cR cR cF wiso
      w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv vb cv cF cfv cR
      wbr wa vb cv cF ccnv cfv cA wcel vb cv cF ccnv cfv vb cv cR wbr vc cv vb
      cv cR wbr vc cv cF cfv vc cv wceq wi vc cA wral vb cv cF ccnv cfv cF cfv
      vb cv cF ccnv cfv wceq wi cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb
      cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF ccnv cfv cA wcel vb
      cv vb cv cF cfv cR wbr cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv
      cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF ccnv wf vb cv cA wcel
      vb cv cF ccnv cfv cA wcel cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb
      cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF wf1o cA cA cF ccnv
      wf1o cA cA cF ccnv wf cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv
      cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF
      wf1o cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv
      vb cv wceq wn wa simpl3 cA cA cR cR cF isof1o syl cA cA cF f1ocnv cA cA
      cF ccnv f1of 3syl cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn simprl cA cA vb cv cF ccnv ffvelrn
      syl2anc adantr cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel
      vb cv cF cfv vb cv wceq wn wa wa vb cv vb cv cF cfv cR wbr vb cv cF ccnv
      cfv vb cv cR wbr cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF ccnv cfv vb cv cR wbr vb
      cv cF ccnv cfv cF cfv vb cv cF cfv cR wbr vb cv vb cv cF cfv cR wbr cA cR
      wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv
      wceq wn wa wa cA cA cR cR cF wiso vb cv cF ccnv cfv cA wcel vb cv cA wcel
      vb cv cF ccnv cfv vb cv cR wbr vb cv cF ccnv cfv cF cfv vb cv cF cfv cR
      wbr wb cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv
      vb cv wceq wn wa simpl3 cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv
      cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF ccnv wf vb cv cA wcel
      vb cv cF ccnv cfv cA wcel cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb
      cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF wf1o cA cA cF ccnv
      wf1o cA cA cF ccnv wf cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv
      cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF
      wf1o cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv
      vb cv wceq wn wa simpl3 cA cA cR cR cF isof1o syl cA cA cF f1ocnv cA cA
      cF ccnv f1of 3syl cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn simprl cA cA vb cv cF ccnv ffvelrn
      syl2anc cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv
      cF cfv vb cv wceq wn simprl cA cA vb cv cF ccnv cfv vb cv cR cR cF isorel
      syl12anc cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv
      cF cfv vb cv wceq wn wa wa vb cv cF ccnv cfv cF cfv vb cv vb cv cF cfv cR
      cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb
      cv wceq wn wa wa cA cA cF wf1o vb cv cA wcel vb cv cF ccnv cfv cF cfv vb
      cv wceq cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv
      cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF wf1o cA cR wwe cA
      cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv vb cv wceq wn wa
      simpl3 cA cA cR cR cF isof1o syl cA cR wwe cA cR wse cA cA cR cR cF wiso
      w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA cA vb cv cF
      f1ocnvfv2 syl2anc breq1d bitr2d biimpa vb cv cF ccnv cfv cA wcel vc cv vb
      cv cR wbr vc cv cF cfv vc cv wceq wi vc cA wral vb cv cF ccnv cfv vb cv
      cR wbr vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv wceq vc cv vb cv cR wbr
      vc cv cF cfv vc cv wceq wi vb cv cF ccnv cfv vb cv cR wbr vb cv cF ccnv
      cfv cF cfv vb cv cF ccnv cfv wceq wi vc vb cv cF ccnv cfv cA vc cv vb cv
      cF ccnv cfv wceq vc cv vb cv cR wbr vb cv cF ccnv cfv vb cv cR wbr vc cv
      cF cfv vc cv wceq vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv wceq vc cv
      vb cv cF ccnv cfv vb cv cR breq1 vc cv vb cv cF ccnv cfv wceq vc cv cF
      cfv vb cv cF ccnv cfv cF cfv vc cv vb cv cF ccnv cfv vc cv vb cv cF ccnv
      cfv cF fveq2 vc cv vb cv cF ccnv cfv wceq id eqeq12d imbi12d rspcv com23
      sylc cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF
      cfv vb cv wceq wn wa wa vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv wceq
      va cv cF cfv va cv wceq va cA wral wi vb cv vb cv cF cfv cR wbr cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv wceq va cv cF cfv va
      cv wceq va cA wral cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF ccnv cfv cF cfv vb cv cF
      ccnv cfv wceq wa vb cv cF cfv vb cv wceq wn vb cv cF cfv vb cv wceq va cv
      cF cfv va cv wceq va cA wral cA cR wwe cA cR wse cA cA cR cR cF wiso w3a
      vb cv cA wcel vb cv cF cfv vb cv wceq wn vb cv cF ccnv cfv cF cfv vb cv
      cF ccnv cfv wceq simplrr cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb
      cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF ccnv cfv cF cfv vb
      cv cF ccnv cfv wceq wa vb cv cF ccnv cfv cF cfv cF cfv vb cv cF ccnv cfv
      cF cfv vb cv cF cfv vb cv vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv wceq
      vb cv cF ccnv cfv cF cfv cF cfv vb cv cF ccnv cfv cF cfv wceq cA cR wwe
      cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa wa vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv cF fveq2 adantl cA cR
      wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv
      wceq wn wa wa vb cv cF ccnv cfv cF cfv cF cfv vb cv cF cfv wceq vb cv cF
      ccnv cfv cF cfv vb cv cF ccnv cfv wceq cA cR wwe cA cR wse cA cA cR cR cF
      wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF ccnv cfv
      cF cfv vb cv cF cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel
      vb cv cF cfv vb cv wceq wn wa wa cA cA cF wf1o vb cv cA wcel vb cv cF
      ccnv cfv cF cfv vb cv wceq cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb
      cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF
      wf1o cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv
      vb cv wceq wn wa simpl3 cA cA cR cR cF isof1o syl cA cR wwe cA cR wse cA
      cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA
      cA vb cv cF f1ocnvfv2 syl2anc fveq2d adantr cA cR wwe cA cR wse cA cA cR
      cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF
      ccnv cfv cF cfv vb cv wceq vb cv cF ccnv cfv cF cfv vb cv cF ccnv cfv
      wceq cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF
      cfv vb cv wceq wn wa wa cA cA cF wf1o vb cv cA wcel vb cv cF ccnv cfv cF
      cfv vb cv wceq cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel
      vb cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF wf1o cA cR
      wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv vb cv wceq
      wn wa simpl3 cA cA cR cR cF isof1o syl cA cR wwe cA cR wse cA cA cR cR cF
      wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA cA vb cv cF
      f1ocnvfv2 syl2anc adantr 3eqtr3d vb cv cF cfv vb cv wceq va cv cF cfv va
      cv wceq va cA wral pm2.21 sylc ex adantr syld cA cR wwe cA cR wse cA cA
      cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF
      cfv vb cv cR wbr vb cv vb cv cF cfv cR wbr wo vb cv cF cfv vb cv wceq wn
      cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb
      cv wceq wn simprr cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA
      wcel vb cv cF cfv vb cv wceq wn wa wa vb cv cF cfv vb cv wceq vb cv cF
      cfv vb cv cR wbr vb cv vb cv cF cfv cR wbr wo cA cR wwe cA cR wse cA cA
      cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cR
      wor vb cv cF cfv cA wcel vb cv cA wcel vb cv cF cfv vb cv wceq vb cv cF
      cfv vb cv cR wbr vb cv vb cv cF cfv cR wbr wo wn wb cA cR wwe cA cR wse
      cA cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA
      cR wwe cA cR wor cA cR wwe cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb
      cv cF cfv vb cv wceq wn wa simpl1 cA cR weso syl cA cR wwe cA cR wse cA
      cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA
      cF wf vb cv cA wcel vb cv cF cfv cA wcel cA cR wwe cA cR wse cA cA cR cR
      cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn wa wa cA cA cF wf1o
      cA cA cF wf cA cR wwe cA cR wse cA cA cR cR cF wiso w3a vb cv cA wcel vb
      cv cF cfv vb cv wceq wn wa wa cA cA cR cR cF wiso cA cA cF wf1o cA cR wwe
      cA cR wse cA cA cR cR cF wiso vb cv cA wcel vb cv cF cfv vb cv wceq wn wa
      simpl3 cA cA cR cR cF isof1o syl cA cA cF f1of syl cA cR wwe cA cR wse cA
      cA cR cR cF wiso w3a vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA
      cA vb cv cF ffvelrn syl2anc cA cR wwe cA cR wse cA cA cR cR cF wiso w3a
      vb cv cA wcel vb cv cF cfv vb cv wceq wn simprl cA vb cv cF cfv vb cv cR
      sotrieq syl12anc con2bid mpbird mpjaodan syl5bi ex syl5bi rexlimdv syld
      syl5bir pm2.18d va cv cF cfv va cv wceq va cv cF cfv va cv cid cA cres
      cfv wceq va cA va cv cA wcel va cv cF cfv va cv cid cA cres cfv wceq va
      cv cF cfv va cv wceq va cv cA wcel va cv cid cA cres cfv va cv va cv cF
      cfv cA va cv fvresi eqeq2d biimprd ralimia syl cA cR wwe cA cR wse cA cA
      cR cR cF wiso w3a cF cA wfn cid cA cres cA wfn cF cid cA cres wceq va cv
      cF cfv va cv cid cA cres cfv wceq va cA wral wb cA cR wwe cA cR wse cA cA
      cR cR cF wiso w3a cA cA cF wf1o cF cA wfn cA cA cR cR cF wiso cA cR wwe
      cA cA cF wf1o cA cR wse cA cA cR cR cF isof1o 3ad2ant3 cA cA cF f1ofn syl
      cid cA cres cA wfn cA cR wwe cA cR wse cA cA cR cR cF wiso w3a cA fnresi
      a1i va cA cF cid cA cres eqfnfv syl2anc mpbird $.

    $( Thus, there is at most one isomorphism between any two set-like
       well-ordered classes.  Class version of ~ wemoiso .  (Contributed by
       Mario Carneiro, 25-Jun-2015.) $)
    weisoeq $p |- ( ( ( R We A /\ R Se A ) /\
      ( F Isom R , S ( A , B ) /\ G Isom R , S ( A , B ) ) ) -> F = G ) $=
      cA cR wwe cA cR wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso wa wa cF
      cG wceq cF ccnv cG ccom cid cA cres wceq cA cB cR cS cF wiso cA cB cR cS
      cG wiso wa cA cR wwe cA cR wse wa cA cA cR cR cF ccnv cG ccom wiso cF
      ccnv cG ccom cid cA cres wceq cA cB cR cS cG wiso cA cB cR cS cG wiso cB
      cA cS cR cF ccnv wiso cA cA cR cR cF ccnv cG ccom wiso cA cB cR cS cF
      wiso cA cB cR cS cG wiso id cA cB cR cS cF isocnv cA cB cA cR cS cR cF
      ccnv cG isotr syl2anr cA cR wwe cA cR wse cA cA cR cR cF ccnv cG ccom
      wiso cF ccnv cG ccom cid cA cres wceq cA cR cF ccnv cG ccom weniso 3expa
      sylan2 cA cR wwe cA cR wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso wa
      wa cA cB cF wf1 cA cB cG wf1 cF cG wceq cF ccnv cG ccom cid cA cres wceq
      wb cA cR wwe cA cR wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso wa wa
      cA cB cR cS cF wiso cA cB cF wf1o cA cB cF wf1 cA cR wwe cA cR wse wa cA
      cB cR cS cF wiso cA cB cR cS cG wiso simprl cA cB cR cS cF isof1o cA cB
      cF f1of1 3syl cA cR wwe cA cR wse wa cA cB cR cS cF wiso cA cB cR cS cG
      wiso wa wa cA cB cR cS cG wiso cA cB cG wf1o cA cB cG wf1 cA cR wwe cA cR
      wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso simprr cA cB cR cS cG
      isof1o cA cB cG f1of1 3syl cA cB cF cG f1eqcocnv syl2anc mpbird $.

    $( Thus, there is at most one isomorphism between any two set-like
       well-ordered classes.  Class version of ~ wemoiso2 .  (Contributed by
       Mario Carneiro, 25-Jun-2015.) $)
    weisoeq2 $p |- ( ( ( S We B /\ S Se B ) /\
      ( F Isom R , S ( A , B ) /\ G Isom R , S ( A , B ) ) ) -> F = G ) $=
      cB cS wwe cB cS wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso wa wa cF
      cG wceq cF ccnv cG ccnv wceq cA cB cR cS cF wiso cA cB cR cS cG wiso wa
      cB cS wwe cB cS wse wa cB cA cS cR cF ccnv wiso cB cA cS cR cG ccnv wiso
      wa cF ccnv cG ccnv wceq cA cB cR cS cF wiso cB cA cS cR cF ccnv wiso cA
      cB cR cS cG wiso cB cA cS cR cG ccnv wiso cA cB cR cS cF isocnv cA cB cR
      cS cG isocnv anim12i cB cA cS cR cF ccnv cG ccnv weisoeq sylan2 cB cS wwe
      cB cS wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso wa wa cF wrel cG
      wrel cF cG wceq cF ccnv cG ccnv wceq wb cB cS wwe cB cS wse wa cA cB cR
      cS cF wiso cA cB cR cS cG wiso wa wa cA cB cR cS cF wiso cA cB cF wf1o cF
      wrel cB cS wwe cB cS wse wa cA cB cR cS cF wiso cA cB cR cS cG wiso
      simprl cA cB cR cS cF isof1o cA cB cF f1orel 3syl cB cS wwe cB cS wse wa
      cA cB cR cS cF wiso cA cB cR cS cG wiso wa wa cA cB cR cS cG wiso cA cB
      cG wf1o cG wrel cB cS wwe cB cS wse wa cA cB cR cS cF wiso cA cB cR cS cG
      wiso simprr cA cB cR cS cG isof1o cA cB cG f1orel 3syl cF cG cnveqb
      syl2anc mpbird $.
  $}

  ${
    $d R f g $.  $d A f g $.  $d S f g $.  $d B f g $.
    $( Thus, there is at most one isomorphism between any two well-ordered
       sets.  TODO:  Shorten ~ finnisoeu .  (Contributed by Stefan O'Rear,
       12-Feb-2015.)  (Revised by Mario Carneiro, 25-Jun-2015.) $)
    wemoiso $p |- ( R We A -> E* f f Isom R , S ( A , B ) ) $=
      cA cR wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso wa vf cv vg cv
      wceq wi vg wal vf wal cA cB cR cS vf cv wiso vf wmo cA cR wwe cA cB cR cS
      vf cv wiso cA cB cR cS vg cv wiso wa vf cv vg cv wceq wi vf vg cA cR wwe
      cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso wa vf cv vg cv wceq cA cR
      wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso wa cA cR wwe cA cR wse
      wa vf cv vg cv wceq cA cR wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv
      wiso wa wa cA cR wwe cA cR wse cA cR wwe cA cB cR cS vf cv wiso cA cB cR
      cS vg cv wiso wa simpl cA cR wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv
      wiso wa wa cA cvv wcel cA cR wse cA cB cR cS vf cv wiso cA cvv wcel cA cR
      wwe cA cB cR cS vg cv wiso cA cB cR cS vf cv wiso vf cv cvv wcel cA cB vf
      cv wf cA cvv wcel vf vex cA cB cR cS vf cv wiso cA cB vf cv wf1o cA cB vf
      cv wf cA cB cR cS vf cv isof1o cA cB vf cv f1of syl cA cB cvv vf cv dmfex
      sylancr ad2antrl cA cR cvv exse syl jca cA cB cR cS vf cv vg cv weisoeq
      sylancom ex alrimivv cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso vf vg
      cA cB cR cS vg cv vf cv isoeq1 mo4 sylibr $.

    $( Thus, there is at most one isomorphism between any two well-ordered
       sets.  (Contributed by Stefan O'Rear, 12-Feb-2015.)  (Revised by Mario
       Carneiro, 25-Jun-2015.) $)
    wemoiso2 $p |- ( S We B -> E* f f Isom R , S ( A , B ) ) $=
      cB cS wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso wa vf cv vg cv
      wceq wi vg wal vf wal cA cB cR cS vf cv wiso vf wmo cB cS wwe cA cB cR cS
      vf cv wiso cA cB cR cS vg cv wiso wa vf cv vg cv wceq wi vf vg cB cS wwe
      cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso wa vf cv vg cv wceq cB cS
      wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv wiso wa cB cS wwe cB cS wse
      wa vf cv vg cv wceq cB cS wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv
      wiso wa wa cB cS wwe cB cS wse cB cS wwe cA cB cR cS vf cv wiso cA cB cR
      cS vg cv wiso wa simpl cB cS wwe cA cB cR cS vf cv wiso cA cB cR cS vg cv
      wiso wa wa cB cvv wcel cB cS wse cA cB cR cS vf cv wiso cB cvv wcel cB cS
      wwe cA cB cR cS vg cv wiso cA cB cR cS vf cv wiso cB vf cv crn cvv cA cB
      cR cS vf cv wiso cA cB vf cv wf1o cA cB vf cv wfo vf cv crn cB wceq cA cB
      cR cS vf cv isof1o cA cB vf cv f1ofo cA cB vf cv forn 3syl vf cv vf vex
      rnex syl6eqelr ad2antrl cB cS cvv exse syl jca cA cB cR cS vf cv vg cv
      weisoeq2 sylancom ex alrimivv cA cB cR cS vf cv wiso cA cB cR cS vg cv
      wiso vf vg cA cB cR cS vg cv vf cv isoeq1 mo4 sylibr $.
  $}

  ${
    $d w x y z A $.  $d w x y z F $.  $d w V $.  $d w x y X $.
    knatar.1 $e |- X = |^| { z e. ~P A | ( F ` z ) C_ z } $.
    $( The Knaster-Tarski theorem says that every monotone function over a
       complete lattice has a (least) fixpoint.  Here we specialize this
       theorem to the case when the lattice is the powerset lattice ` ~P A ` .
       (Contributed by Mario Carneiro, 11-Jun-2015.) $)
    knatar $p |- ( ( A e. V /\ ( F ` A ) C_ A /\
        A. x e. ~P A A. y e. ~P x ( F ` y ) C_ ( F ` x ) ) ->
      ( X C_ A /\ ( F ` X ) = X ) ) $=
      cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw
      wral vx cA cpw wral w3a cX cA wss cX cF cfv cX wceq cA cV wcel cA cF cfv
      cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a
      cX vz cv cF cfv vz cv wss vz cA cpw crab cint cA knatar.1 cA cV wcel cA
      cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw
      wral w3a cA cA cpw wcel cA cF cfv cA wss vz cv cF cfv vz cv wss vz cA cpw
      crab cint cA wss cA cV wcel cA cF cfv cA wss cA cA cpw wcel vy cv cF cfv
      vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral cA cV pwidg 3ad2ant1 cA
      cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral
      vx cA cpw wral simp2 vz cv cF cfv vz cv wss cA cF cfv cA wss vz cA cA cpw
      vz cv cA wceq vz cv cF cfv cA cF cfv vz cv cA vz cv cA cF fveq2 vz cv cA
      wceq id sseq12d intminss syl2anc syl5eqss cA cV wcel cA cF cfv cA wss vy
      cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a cX cF cfv
      cX cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw
      wral vx cA cpw wral w3a cX cF cfv vw cv cF cfv vw cv wss vw cA cpw crab
      cint cX cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx
      cv cpw wral vx cA cpw wral w3a vw cv cF cfv vw cv wss cX cF cfv vw cv wss
      wi vw cA cpw wral cX cF cfv vw cv cF cfv vw cv wss vw cA cpw crab cint
      wss cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral w3a vw cv cF cfv vw cv wss cX cF cfv vw cv wss wi
      vw cA cpw cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx
      cv cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss
      cX cF cfv vw cv wss cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv
      wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv
      vw cv wss wa wa cX cF cfv vw cv cF cfv vw cv cA cV wcel cA cF cfv cA wss
      vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a vw cv
      cA cpw wcel vw cv cF cfv vw cv wss wa wa cX vw cv cpw wcel vy cv cF cfv
      vw cv cF cfv wss vy vw cv cpw wral cX cF cfv vw cv cF cfv wss cA cV wcel
      cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA
      cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss wa wa cX vw cv wss
      cX vw cv cpw wcel cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv
      wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv
      vw cv wss wa wa cX vz cv cF cfv vz cv wss vz cA cpw crab cint vw cv
      knatar.1 vw cv cA cpw wcel vw cv cF cfv vw cv wss wa vz cv cF cfv vz cv
      wss vz cA cpw crab cint vw cv wss cA cV wcel cA cF cfv cA wss vy cv cF
      cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a vz cv cF cfv vz
      cv wss vw cv cF cfv vw cv wss vz vw cv cA cpw vz cv vw cv wceq vz cv cF
      cfv vw cv cF cfv vz cv vw cv vz cv vw cv cF fveq2 vz cv vw cv wceq id
      sseq12d intminss adantl syl5eqss cX vw cv vw vex elpw2 sylibr cA cV wcel
      cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA
      cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss wa wa vw cv cA cpw
      wcel vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral vy cv
      cF cfv vw cv cF cfv wss vy vw cv cpw wral cA cV wcel cA cF cfv cA wss vy
      cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA
      cpw wcel vw cv cF cfv vw cv wss simprl cA cV wcel cA cF cfv cA wss vy cv
      cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral vw cv cA cpw
      wcel vw cv cF cfv vw cv wss wa simpl3 vy cv cF cfv vx cv cF cfv wss vy vx
      cv cpw wral vy cv cF cfv vw cv cF cfv wss vy vw cv cpw wral vx vw cv cA
      cpw vx cv vw cv wceq vy cv cF cfv vx cv cF cfv wss vy cv cF cfv vw cv cF
      cfv wss vy vx cv cpw vw cv cpw vx cv vw cv pweq vx cv vw cv wceq vx cv cF
      cfv vw cv cF cfv vy cv cF cfv vx cv vw cv cF fveq2 sseq2d raleqbidv rspcv
      sylc vy cv cF cfv vw cv cF cfv wss cX cF cfv vw cv cF cfv wss vy cX vw cv
      cpw vy cv cX wceq vy cv cF cfv cX cF cfv vw cv cF cfv vy cv cX cF fveq2
      sseq1d rspcv sylc cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv
      wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv
      vw cv wss simprr sstrd expr ralrimiva vw cv cF cfv vw cv wss vw cX cF cfv
      cA cpw ssintrab sylibr cX vz cv cF cfv vz cv wss vz cA cpw crab cint vw
      cv cF cfv vw cv wss vw cA cpw crab cint knatar.1 vz cv cF cfv vz cv wss
      vz cA cpw crab vw cv cF cfv vw cv wss vw cA cpw crab vz cv cF cfv vz cv
      wss vw cv cF cfv vw cv wss vz vw cA cpw vz cv vw cv wceq vz cv cF cfv vw
      cv cF cfv vz cv vw cv vz cv vw cv cF fveq2 vz cv vw cv wceq id sseq12d
      cbvrabv inteqi eqtri syl6sseqr cA cV wcel cA cF cfv cA wss vy cv cF cfv
      vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a cX vw cv cF cfv vw
      cv wss vw cA cpw crab cint cX cF cfv cX vz cv cF cfv vz cv wss vz cA cpw
      crab cint vw cv cF cfv vw cv wss vw cA cpw crab cint knatar.1 vz cv cF
      cfv vz cv wss vz cA cpw crab vw cv cF cfv vw cv wss vw cA cpw crab vz cv
      cF cfv vz cv wss vw cv cF cfv vw cv wss vz vw cA cpw vz cv vw cv wceq vz
      cv cF cfv vw cv cF cfv vz cv vw cv vz cv vw cv cF fveq2 vz cv vw cv wceq
      id sseq12d cbvrabv inteqi eqtri cA cV wcel cA cF cfv cA wss vy cv cF cfv
      vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a cX cF cfv cA cpw
      wcel cX cF cfv cF cfv cX cF cfv wss vw cv cF cfv vw cv wss vw cA cpw crab
      cint cX cF cfv wss cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv
      wss vy vx cv cpw wral vx cA cpw wral w3a cX cF cfv cA wss cX cF cfv cA
      cpw wcel cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx
      cv cpw wral vx cA cpw wral w3a cX cF cfv cA cF cfv cA cA cV wcel cA cF
      cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral
      w3a cX cA cpw wcel vy cv cF cfv cA cF cfv wss vy cA cpw wral cX cF cfv cA
      cF cfv wss cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy
      vx cv cpw wral vx cA cpw wral w3a cX cA cpw wcel cX cA wss cA cV wcel cA
      cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw
      wral w3a cX vz cv cF cfv vz cv wss vz cA cpw crab cint cA knatar.1 cA cV
      wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx
      cA cpw wral w3a cA cA cpw wcel cA cF cfv cA wss vz cv cF cfv vz cv wss vz
      cA cpw crab cint cA wss cA cV wcel cA cF cfv cA wss cA cA cpw wcel vy cv
      cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral cA cV pwidg
      3ad2ant1 cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx
      cv cpw wral vx cA cpw wral simp2 vz cv cF cfv vz cv wss cA cF cfv cA wss
      vz cA cA cpw vz cv cA wceq vz cv cF cfv cA cF cfv vz cv cA vz cv cA cF
      fveq2 vz cv cA wceq id sseq12d intminss syl2anc syl5eqss cA cV wcel cA cF
      cfv cA wss cX cA cpw wcel cX cA wss wb vy cv cF cfv vx cv cF cfv wss vy
      vx cv cpw wral vx cA cpw wral cX cA cV elpw2g 3ad2ant1 mpbird cA cV wcel
      cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA
      cpw wral w3a cA cA cpw wcel vy cv cF cfv vx cv cF cfv wss vy vx cv cpw
      wral vx cA cpw wral vy cv cF cfv cA cF cfv wss vy cA cpw wral cA cV wcel
      cA cF cfv cA wss cA cA cpw wcel vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral cA cV pwidg 3ad2ant1 cA cV wcel cA cF cfv cA wss
      vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral simp3 vy
      cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vy cv cF cfv cA cF cfv wss
      vy cA cpw wral vx cA cA cpw vx cv cA wceq vy cv cF cfv vx cv cF cfv wss
      vy cv cF cfv cA cF cfv wss vy vx cv cpw cA cpw vx cv cA pweq vx cv cA
      wceq vx cv cF cfv cA cF cfv vy cv cF cfv vx cv cA cF fveq2 sseq2d
      raleqbidv rspcv sylc vy cv cF cfv cA cF cfv wss cX cF cfv cA cF cfv wss
      vy cX cA cpw vy cv cX wceq vy cv cF cfv cX cF cfv cA cF cfv vy cv cX cF
      fveq2 sseq1d rspcv sylc cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF
      cfv wss vy vx cv cpw wral vx cA cpw wral simp2 sstrd cX cF cfv cA cX cF
      fvex elpw sylibr cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv
      wss vy vx cv cpw wral vx cA cpw wral w3a cX cF cfv cX cpw wcel vy cv cF
      cfv cX cF cfv wss vy cX cpw wral cX cF cfv cF cfv cX cF cfv wss cA cV
      wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx
      cA cpw wral w3a cX cF cfv cX wss cX cF cfv cX cpw wcel cA cV wcel cA cF
      cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral
      w3a cX cF cfv vw cv cF cfv vw cv wss vw cA cpw crab cint cX cA cV wcel cA
      cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw
      wral w3a vw cv cF cfv vw cv wss cX cF cfv vw cv wss wi vw cA cpw wral cX
      cF cfv vw cv cF cfv vw cv wss vw cA cpw crab cint wss cA cV wcel cA cF
      cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral
      w3a vw cv cF cfv vw cv wss cX cF cfv vw cv wss wi vw cA cpw cA cV wcel cA
      cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw
      wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss cX cF cfv vw cv wss cA
      cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral
      vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss wa wa cX cF
      cfv vw cv cF cfv vw cv cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF
      cfv wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF
      cfv vw cv wss wa wa cX vw cv cpw wcel vy cv cF cfv vw cv cF cfv wss vy vw
      cv cpw wral cX cF cfv vw cv cF cfv wss cA cV wcel cA cF cfv cA wss vy cv
      cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA cpw
      wcel vw cv cF cfv vw cv wss wa wa cX vw cv wss cX vw cv cpw wcel cA cV
      wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx
      cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss wa wa cX vz cv
      cF cfv vz cv wss vz cA cpw crab cint vw cv knatar.1 vw cv cA cpw wcel vw
      cv cF cfv vw cv wss wa vz cv cF cfv vz cv wss vz cA cpw crab cint vw cv
      wss cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral w3a vz cv cF cfv vz cv wss vw cv cF cfv vw cv wss
      vz vw cv cA cpw vz cv vw cv wceq vz cv cF cfv vw cv cF cfv vz cv vw cv vz
      cv vw cv cF fveq2 vz cv vw cv wceq id sseq12d intminss adantl syl5eqss cX
      vw cv vw vex elpw2 sylibr cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv
      cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv
      cF cfv vw cv wss wa wa vw cv cA cpw wcel vy cv cF cfv vx cv cF cfv wss vy
      vx cv cpw wral vx cA cpw wral vy cv cF cfv vw cv cF cfv wss vy vw cv cpw
      wral cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss
      simprl cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral vw cv cA cpw wcel vw cv cF cfv vw cv wss wa
      simpl3 vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vy cv cF cfv vw cv
      cF cfv wss vy vw cv cpw wral vx vw cv cA cpw vx cv vw cv wceq vy cv cF
      cfv vx cv cF cfv wss vy cv cF cfv vw cv cF cfv wss vy vx cv cpw vw cv cpw
      vx cv vw cv pweq vx cv vw cv wceq vx cv cF cfv vw cv cF cfv vy cv cF cfv
      vx cv vw cv cF fveq2 sseq2d raleqbidv rspcv sylc vy cv cF cfv vw cv cF
      cfv wss cX cF cfv vw cv cF cfv wss vy cX vw cv cpw vy cv cX wceq vy cv cF
      cfv cX cF cfv vw cv cF cfv vy cv cX cF fveq2 sseq1d rspcv sylc cA cV wcel
      cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA
      cpw wral w3a vw cv cA cpw wcel vw cv cF cfv vw cv wss simprr sstrd expr
      ralrimiva vw cv cF cfv vw cv wss vw cX cF cfv cA cpw ssintrab sylibr cX
      vz cv cF cfv vz cv wss vz cA cpw crab cint vw cv cF cfv vw cv wss vw cA
      cpw crab cint knatar.1 vz cv cF cfv vz cv wss vz cA cpw crab vw cv cF cfv
      vw cv wss vw cA cpw crab vz cv cF cfv vz cv wss vw cv cF cfv vw cv wss vz
      vw cA cpw vz cv vw cv wceq vz cv cF cfv vw cv cF cfv vz cv vw cv vz cv vw
      cv cF fveq2 vz cv vw cv wceq id sseq12d cbvrabv inteqi eqtri syl6sseqr cX
      cF cfv cX cX cF fvex elpw sylibr cA cV wcel cA cF cfv cA wss vy cv cF cfv
      vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a cX cA cpw wcel vy
      cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw wral vy cv cF cfv
      cX cF cfv wss vy cX cpw wral cA cV wcel cA cF cfv cA wss vy cv cF cfv vx
      cv cF cfv wss vy vx cv cpw wral vx cA cpw wral w3a cX cA cpw wcel cX cA
      wss cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral w3a cX vz cv cF cfv vz cv wss vz cA cpw crab cint
      cA knatar.1 cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy
      vx cv cpw wral vx cA cpw wral w3a cA cA cpw wcel cA cF cfv cA wss vz cv
      cF cfv vz cv wss vz cA cpw crab cint cA wss cA cV wcel cA cF cfv cA wss
      cA cA cpw wcel vy cv cF cfv vx cv cF cfv wss vy vx cv cpw wral vx cA cpw
      wral cA cV pwidg 3ad2ant1 cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv
      cF cfv wss vy vx cv cpw wral vx cA cpw wral simp2 vz cv cF cfv vz cv wss
      cA cF cfv cA wss vz cA cA cpw vz cv cA wceq vz cv cF cfv cA cF cfv vz cv
      cA vz cv cA cF fveq2 vz cv cA wceq id sseq12d intminss syl2anc syl5eqss
      cA cV wcel cA cF cfv cA wss cX cA cpw wcel cX cA wss wb vy cv cF cfv vx
      cv cF cfv wss vy vx cv cpw wral vx cA cpw wral cX cA cV elpw2g 3ad2ant1
      mpbird cA cV wcel cA cF cfv cA wss vy cv cF cfv vx cv cF cfv wss vy vx cv
      cpw wral vx cA cpw wral simp3 vy cv cF cfv vx cv cF cfv wss vy vx cv cpw
      wral vy cv cF cfv cX cF cfv wss vy cX cpw wral vx cX cA cpw vx cv cX wceq
      vy cv cF cfv vx cv cF cfv wss vy cv cF cfv cX cF cfv wss vy vx cv cpw cX
      cpw vx cv cX pweq vx cv cX wceq vx cv cF cfv cX cF cfv vy cv cF cfv vx cv
      cX cF fveq2 sseq2d raleqbidv rspcv sylc vy cv cF cfv cX cF cfv wss cX cF
      cfv cF cfv cX cF cfv wss vy cX cF cfv cX cpw vy cv cX cF cfv wceq vy cv
      cF cfv cX cF cfv cF cfv cX cF cfv vy cv cX cF cfv cF fveq2 sseq1d rspcv
      sylc vw cv cF cfv vw cv wss cX cF cfv cF cfv cX cF cfv wss vw cX cF cfv
      cA cpw vw cv cX cF cfv wceq vw cv cF cfv cX cF cfv cF cfv vw cv cX cF cfv
      vw cv cX cF cfv cF fveq2 vw cv cX cF cfv wceq id sseq12d intminss syl2anc
      syl5eqss eqssd jca $.
  $}



