
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Binary_relations.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Ordered-pair class abstractions (class builders)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c |-> $.  $( Maps-to symbol $)

  $( Extend class notation to include ordered-pair class abstraction (class
     builder). $)
  copab $a class { <. x , y >. | ph } $.

  $( Extend the definition of a class to include maps-to notation for defining
     a function via a rule. $)
  cmpt $a class ( x e. A |-> B ) $.

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Define the class abstraction of a collection of ordered pairs.
       Definition 3.3 of [Monk1] p. 34.  Usually ` x ` and ` y ` are distinct,
       although the definition doesn't strictly require it (see ~ dfid2 for a
       case where they are not distinct).  The brace notation is called "class
       abstraction" by Quine; it is also (more commonly) called a "class
       builder" in the literature.  An alternate definition using no
       existential quantifiers is shown by ~ dfopab2 .  For example,
` R = { <. x , y >. | ( x e. CC /\ y e. CC /\ ( x + 1 ) = y ) } -> 3 R 4 `
       ( ~ ex-opab ).  (Contributed by NM, 4-Jul-1994.) $)
    df-opab $a |- { <. x , y >. | ph } =
                  { z | E. x E. y ( z = <. x , y >. /\ ph ) } $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    $( Define maps-to notation for defining a function via a rule.  Read as
       "the function defined by the map from ` x ` (in ` A ` ) to
       ` B ( x ) ` ."  The class expression ` B ` is the value of the function
       at ` x ` and normally contains the variable ` x ` .  An example is the
       square function for complex numbers, ` ( x e. CC |-> ( x ^ 2 ) ) ` .
       Similar to the definition of mapping in [ChoquetDD] p. 2.  (Contributed
       by NM, 17-Feb-2008.) $)
    df-mpt $a |- ( x e. A |-> B ) =
                    { <. x , y >. | ( x e. A /\ y = B ) } $.
  $}

  ${
    $d x z R $.  $d y z R $.
    $( The collection of ordered pairs in a class is a subclass of it.
       (Contributed by NM, 27-Dec-1996.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    opabss $p |- { <. x , y >. | x R y } C_ R $=
      vx cv vy cv cR wbr vx vy copab vz cv vx cv vy cv cop wceq vx cv vy cv cR
      wbr wa vy wex vx wex vz cab cR vx cv vy cv cR wbr vx vy vz df-opab vz cv
      vx cv vy cv cop wceq vx cv vy cv cR wbr wa vy wex vx wex vz cR vz cv vx
      cv vy cv cop wceq vx cv vy cv cR wbr wa vz cv cR wcel vx vy vx cv vy cv
      cR wbr vz cv vx cv vy cv cop wceq vx cv vy cv cop cR wcel vz cv cR wcel
      vx cv vy cv cR df-br vz cv vx cv vy cv cop wceq vz cv cR wcel vx cv vy cv
      cop cR wcel vz cv vx cv vy cv cop cR eleq1 biimpar sylan2b exlimivv abssi
      eqsstri $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.  $d z ps $.  $d z ch $.
    opabbid.1 $e |- F/ x ph $.
    opabbid.2 $e |- F/ y ph $.
    opabbid.3 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal ordered-pair class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.)  (Proof shortened by Andrew
       Salmon, 9-Jul-2011.) $)
    opabbid $p |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } ) $=
      wph vz cv vx cv vy cv cop wceq wps wa vy wex vx wex vz cab vz cv vx cv vy
      cv cop wceq wch wa vy wex vx wex vz cab wps vx vy copab wch vx vy copab
      wph vz cv vx cv vy cv cop wceq wps wa vy wex vx wex vz cv vx cv vy cv cop
      wceq wch wa vy wex vx wex vz wph vz cv vx cv vy cv cop wceq wps wa vy wex
      vz cv vx cv vy cv cop wceq wch wa vy wex vx opabbid.1 wph vz cv vx cv vy
      cv cop wceq wps wa vz cv vx cv vy cv cop wceq wch wa vy opabbid.2 wph wps
      wch vz cv vx cv vy cv cop wceq opabbid.3 anbi2d exbid exbid abbidv wps vx
      vy vz df-opab wch vx vy vz df-opab 3eqtr4g $.
  $}

  ${
    $d x ph $.  $d y z ph $.  $d z ps $.  $d z ch $.
    opabbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal ordered-pair class abstractions (deduction
       rule).  (Contributed by NM, 15-May-1995.) $)
    opabbidv $p |- ( ph -> { <. x , y >. | ps } = { <. x , y >. | ch } ) $=
      wph wps wch vx vy wph vx nfv wph vy nfv opabbidv.1 opabbid $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.  $d z ps $.
    opabbii.1 $e |- ( ph <-> ps ) $.
    $( Equivalent wff's yield equal class abstractions.  (Contributed by NM,
       15-May-1995.) $)
    opabbii $p |- { <. x , y >. | ph } = { <. x , y >. | ps } $=
      vz cv vz cv wceq wph vx vy copab wps vx vy copab wceq vz cv eqid vz cv vz
      cv wceq wph wps vx vy wph wps wb vz cv vz cv wceq opabbii.1 a1i opabbidv
      ax-mp $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d ph w $.
    nfopab.1 $e |- F/ z ph $.
    $( Bound-variable hypothesis builder for class abstraction.  (Contributed
       by NM, 1-Sep-1999.)  (Unnecessary distinct variable restrictions were
       removed by Andrew Salmon, 11-Jul-2011.) $)
    nfopab $p |- F/_ z { <. x , y >. | ph } $=
      vz wph vx vy copab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cab
      wph vx vy vw df-opab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vz
      vw vw cv vx cv vy cv cop wceq wph wa vy wex vz vx vw cv vx cv vy cv cop
      wceq wph wa vz vy vw cv vx cv vy cv cop wceq wph vz vw cv vx cv vy cv cop
      wceq vz nfv nfopab.1 nfan nfex nfex nfab nfcxfr $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( The first abstraction variable in an ordered-pair class abstraction
       (class builder) is effectively not free.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
    nfopab1 $p |- F/_ x { <. x , y >. | ph } $=
      vx wph vx vy copab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cab
      wph vx vy vz df-opab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vx
      vz vz cv vx cv vy cv cop wceq wph wa vy wex vx nfe1 nfab nfcxfr $.

    $( The second abstraction variable in an ordered-pair class abstraction
       (class builder) is effectively not free.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
    nfopab2 $p |- F/_ y { <. x , y >. | ph } $=
      vy wph vx vy copab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cab
      wph vx vy vz df-opab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vy
      vz vz cv vx cv vy cv cop wceq wph wa vy wex vy vx vz cv vx cv vy cv cop
      wceq wph wa vy nfe1 nfex nfab nfcxfr $.
  $}

  ${
    $d x y z w v $.  $d v ph $.  $d v ps $.
    cbvopab.1 $e |- F/ z ph $.
    cbvopab.2 $e |- F/ w ph $.
    cbvopab.3 $e |- F/ x ps $.
    cbvopab.4 $e |- F/ y ps $.
    cbvopab.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables in an ordered-pair class
       abstraction, using implicit substitution.  (Contributed by NM,
       14-Sep-2003.) $)
    cbvopab $p |- { <. x , y >. | ph } = { <. z , w >. | ps } $=
      vv cv vx cv vy cv cop wceq wph wa vy wex vx wex vv cab vv cv vz cv vw cv
      cop wceq wps wa vw wex vz wex vv cab wph vx vy copab wps vz vw copab vv
      cv vx cv vy cv cop wceq wph wa vy wex vx wex vv cv vz cv vw cv cop wceq
      wps wa vw wex vz wex vv vv cv vx cv vy cv cop wceq wph wa vv cv vz cv vw
      cv cop wceq wps wa vx vy vz vw vv cv vx cv vy cv cop wceq wph vz vv cv vx
      cv vy cv cop wceq vz nfv cbvopab.1 nfan vv cv vx cv vy cv cop wceq wph vw
      vv cv vx cv vy cv cop wceq vw nfv cbvopab.2 nfan vv cv vz cv vw cv cop
      wceq wps vx vv cv vz cv vw cv cop wceq vx nfv cbvopab.3 nfan vv cv vz cv
      vw cv cop wceq wps vy vv cv vz cv vw cv cop wceq vy nfv cbvopab.4 nfan vx
      cv vz cv wceq vy cv vw cv wceq wa vv cv vx cv vy cv cop wceq vv cv vz cv
      vw cv cop wceq wph wps vx cv vz cv wceq vy cv vw cv wceq wa vx cv vy cv
      cop vz cv vw cv cop vv cv vx cv vy cv vz cv vw cv opeq12 eqeq2d cbvopab.5
      anbi12d cbvex2 abbii wph vx vy vv df-opab wps vz vw vv df-opab 3eqtr4i $.
  $}

  ${
    $d x y z w $.  $d z w v ph $.  $d x y v ps $.
    cbvopabv.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables in an ordered-pair class
       abstraction, using implicit substitution.  (Contributed by NM,
       15-Oct-1996.) $)
    cbvopabv $p |- { <. x , y >. | ph } = { <. z , w >. | ps } $=
      wph wps vx vy vz vw wph vz nfv wph vw nfv wps vx nfv wps vy nfv
      cbvopabv.1 cbvopab $.
  $}

  ${
    $d v w x y $.  $d v w y z $.  $d v w ph $.  $d v w ps $.
    cbvopab1.1 $e |- F/ z ph $.
    cbvopab1.2 $e |- F/ x ps $.
    cbvopab1.3 $e |- ( x = z -> ( ph <-> ps ) ) $.
    $( Change first bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 6-Oct-2004.)  (Revised by
       Mario Carneiro, 14-Oct-2016.) $)
    cbvopab1 $p |- { <. x , y >. | ph } = { <. z , y >. | ps } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cab vw cv vz cv vy cv
      cop wceq wps wa vy wex vz wex vw cab wph vx vy copab wps vz vy copab vw
      cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cv vz cv vy cv cop wceq
      wps wa vy wex vz wex vw vw cv vx cv vy cv cop wceq wph wa vy wex vx wex
      vw cv vv cv vy cv cop wceq wph vx vv wsb wa vy wex vv wex vw cv vz cv vy
      cv cop wceq wps wa vy wex vz wex vw cv vx cv vy cv cop wceq wph wa vy wex
      vw cv vv cv vy cv cop wceq wph vx vv wsb wa vy wex vx vv vw cv vx cv vy
      cv cop wceq wph wa vy wex vv nfv vw cv vv cv vy cv cop wceq wph vx vv wsb
      wa vx vy vw cv vv cv vy cv cop wceq wph vx vv wsb vx vw cv vv cv vy cv
      cop wceq vx nfv wph vx vv nfs1v nfan nfex vx cv vv cv wceq vw cv vx cv vy
      cv cop wceq wph wa vw cv vv cv vy cv cop wceq wph vx vv wsb wa vy vx cv
      vv cv wceq vw cv vx cv vy cv cop wceq vw cv vv cv vy cv cop wceq wph wph
      vx vv wsb vx cv vv cv wceq vx cv vy cv cop vv cv vy cv cop vw cv vx cv vv
      cv vy cv opeq1 eqeq2d wph vx vv sbequ12 anbi12d exbidv cbvex vw cv vv cv
      vy cv cop wceq wph vx vv wsb wa vy wex vw cv vz cv vy cv cop wceq wps wa
      vy wex vv vz vw cv vv cv vy cv cop wceq wph vx vv wsb wa vz vy vw cv vv
      cv vy cv cop wceq wph vx vv wsb vz vw cv vv cv vy cv cop wceq vz nfv wph
      vx vv vz cbvopab1.1 nfsb nfan nfex vw cv vz cv vy cv cop wceq wps wa vy
      wex vv nfv vv cv vz cv wceq vw cv vv cv vy cv cop wceq wph vx vv wsb wa
      vw cv vz cv vy cv cop wceq wps wa vy vv cv vz cv wceq vw cv vv cv vy cv
      cop wceq vw cv vz cv vy cv cop wceq wph vx vv wsb wps vv cv vz cv wceq vv
      cv vy cv cop vz cv vy cv cop vw cv vv cv vz cv vy cv opeq1 eqeq2d vv cv
      vz cv wceq wph vx vv wsb wph vx vz wsb wps wph vv vz vx sbequ wph wps vx
      vz cbvopab1.2 cbvopab1.3 sbie syl6bb anbi12d exbidv cbvex bitri abbii wph
      vx vy vw df-opab wps vz vy vw df-opab 3eqtr4i $.
  $}

  ${
    $d w x y z $.  $d w ph $.  $d w ps $.
    cbvopab2.1 $e |- F/ z ph $.
    cbvopab2.2 $e |- F/ y ps $.
    cbvopab2.3 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Change second bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 22-Aug-2013.) $)
    cbvopab2 $p |- { <. x , y >. | ph } = { <. x , z >. | ps } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cab vw cv vx cv vz cv
      cop wceq wps wa vz wex vx wex vw cab wph vx vy copab wps vx vz copab vw
      cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cv vx cv vz cv cop wceq
      wps wa vz wex vx wex vw vw cv vx cv vy cv cop wceq wph wa vy wex vw cv vx
      cv vz cv cop wceq wps wa vz wex vx vw cv vx cv vy cv cop wceq wph wa vw
      cv vx cv vz cv cop wceq wps wa vy vz vw cv vx cv vy cv cop wceq wph vz vw
      cv vx cv vy cv cop wceq vz nfv cbvopab2.1 nfan vw cv vx cv vz cv cop wceq
      wps vy vw cv vx cv vz cv cop wceq vy nfv cbvopab2.2 nfan vy cv vz cv wceq
      vw cv vx cv vy cv cop wceq vw cv vx cv vz cv cop wceq wph wps vy cv vz cv
      wceq vx cv vy cv cop vx cv vz cv cop vw cv vy cv vz cv vx cv opeq2 eqeq2d
      cbvopab2.3 anbi12d cbvex exbii abbii wph vx vy vw df-opab wps vx vz vw
      df-opab 3eqtr4i $.
  $}

  ${
    $d x y z w $.  $d z w ph $.
    $( Change first bound variable in an ordered-pair class abstraction, using
       explicit substitution.  (Contributed by NM, 31-Jul-2003.) $)
    cbvopab1s $p |- { <. x , y >. | ph } = { <. z , y >. | [ z / x ] ph } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cab vw cv vz cv vy cv
      cop wceq wph vx vz wsb wa vy wex vz wex vw cab wph vx vy copab wph vx vz
      wsb vz vy copab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cv vz
      cv vy cv cop wceq wph vx vz wsb wa vy wex vz wex vw vw cv vx cv vy cv cop
      wceq wph wa vy wex vw cv vz cv vy cv cop wceq wph vx vz wsb wa vy wex vx
      vz vw cv vx cv vy cv cop wceq wph wa vy wex vz nfv vw cv vz cv vy cv cop
      wceq wph vx vz wsb wa vx vy vw cv vz cv vy cv cop wceq wph vx vz wsb vx
      vw cv vz cv vy cv cop wceq vx nfv wph vx vz nfs1v nfan nfex vx cv vz cv
      wceq vw cv vx cv vy cv cop wceq wph wa vw cv vz cv vy cv cop wceq wph vx
      vz wsb wa vy vx cv vz cv wceq vw cv vx cv vy cv cop wceq vw cv vz cv vy
      cv cop wceq wph wph vx vz wsb vx cv vz cv wceq vx cv vy cv cop vz cv vy
      cv cop vw cv vx cv vz cv vy cv opeq1 eqeq2d wph vx vz sbequ12 anbi12d
      exbidv cbvex abbii wph vx vy vw df-opab wph vx vz wsb vz vy vw df-opab
      3eqtr4i $.
  $}

  ${
    $d x y $.  $d y z $.  $d z ph $.  $d x ps $.
    cbvopab1v.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    $( Rule used to change the first bound variable in an ordered pair
       abstraction, using implicit substitution.  (Contributed by NM,
       31-Jul-2003.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)
    cbvopab1v $p |- { <. x , y >. | ph } = { <. z , y >. | ps } $=
      wph wps vx vy vz wph vz nfv wps vx nfv cbvopab1v.1 cbvopab1 $.
  $}

  ${
    $d x y z w $.  $d z w ph $.  $d y w ps $.
    cbvopab2v.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    $( Rule used to change the second bound variable in an ordered pair
       abstraction, using implicit substitution.  (Contributed by NM,
       2-Sep-1999.) $)
    cbvopab2v $p |- { <. x , y >. | ph } = { <. x , z >. | ps } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cab vw cv vx cv vz cv
      cop wceq wps wa vz wex vx wex vw cab wph vx vy copab wps vx vz copab vw
      cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cv vx cv vz cv cop wceq
      wps wa vz wex vx wex vw vw cv vx cv vy cv cop wceq wph wa vy wex vw cv vx
      cv vz cv cop wceq wps wa vz wex vx vw cv vx cv vy cv cop wceq wph wa vw
      cv vx cv vz cv cop wceq wps wa vy vz vy cv vz cv wceq vw cv vx cv vy cv
      cop wceq vw cv vx cv vz cv cop wceq wph wps vy cv vz cv wceq vx cv vy cv
      cop vx cv vz cv cop vw cv vy cv vz cv vx cv opeq2 eqeq2d cbvopab2v.1
      anbi12d cbvexv exbii abbii wph vx vy vw df-opab wps vx vz vw df-opab
      3eqtr4i $.
  $}

  ${
    $d w y z A $.  $d w ph $.  $d w x y z $.
    $( Move substitution into a class abstraction.  (Contributed by NM,
       6-Aug-2007.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
    csbopabg $p |- ( A e. V -> [_ A / x ]_ { <. y , z >. | ph } =
               { <. y , z >. | [. A / x ]. ph } ) $=
      vx vw cv wph vy vz copab csb wph vx vw wsb vy vz copab wceq vx cA wph vy
      vz copab csb wph vx cA wsbc vy vz copab wceq vw cA cV vw cv cA wceq vx vw
      cv wph vy vz copab csb vx cA wph vy vz copab csb wph vx vw wsb vy vz
      copab wph vx cA wsbc vy vz copab vx vw cv cA wph vy vz copab csbeq1 vw cv
      cA wceq wph vx vw wsb wph vx cA wsbc vy vz wph vx vw cA dfsbcq2 opabbidv
      eqeq12d vx vw cv wph vy vz copab wph vx vw wsb vy vz copab vw vex wph vx
      vw wsb vy vz vx wph vx vw nfs1v nfopab vx cv vw cv wceq wph wph vx vw wsb
      vy vz wph vx vw sbequ12 opabbidv csbief vtoclg $.
  $}

  ${
    $d x z $.  $d y z $.  $d ph z $.  $d ps z $.
    $( Union of two ordered pair class abstractions.  (Contributed by NM,
       30-Sep-2002.) $)
    unopab $p |- ( { <. x , y >. | ph } u. { <. x , y >. | ps } ) =
               { <. x , y >. | ( ph \/ ps ) } $=
      vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cab vz cv vx cv vy cv
      cop wceq wps wa vy wex vx wex vz cab cun vz cv vx cv vy cv cop wceq wph
      wps wo wa vy wex vx wex vz cab wph vx vy copab wps vx vy copab cun wph
      wps wo vx vy copab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cab
      vz cv vx cv vy cv cop wceq wps wa vy wex vx wex vz cab cun vz cv vx cv vy
      cv cop wceq wph wa vy wex vx wex vz cv vx cv vy cv cop wceq wps wa vy wex
      vx wex wo vz cab vz cv vx cv vy cv cop wceq wph wps wo wa vy wex vx wex
      vz cab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cv vx cv vy cv
      cop wceq wps wa vy wex vx wex vz unab vz cv vx cv vy cv cop wceq wph wa
      vy wex vx wex vz cv vx cv vy cv cop wceq wps wa vy wex vx wex wo vz cv vx
      cv vy cv cop wceq wph wps wo wa vy wex vx wex vz vz cv vx cv vy cv cop
      wceq wph wa vy wex vx wex vz cv vx cv vy cv cop wceq wps wa vy wex vx wex
      wo vz cv vx cv vy cv cop wceq wph wa vy wex vz cv vx cv vy cv cop wceq
      wps wa vy wex wo vx wex vz cv vx cv vy cv cop wceq wph wps wo wa vy wex
      vx wex vz cv vx cv vy cv cop wceq wph wa vy wex vz cv vx cv vy cv cop
      wceq wps wa vy wex vx 19.43 vz cv vx cv vy cv cop wceq wph wa vy wex vz
      cv vx cv vy cv cop wceq wps wa vy wex wo vz cv vx cv vy cv cop wceq wph
      wps wo wa vy wex vx vz cv vx cv vy cv cop wceq wph wps wo wa vy wex vz cv
      vx cv vy cv cop wceq wph wa vz cv vx cv vy cv cop wceq wps wa wo vy wex
      vz cv vx cv vy cv cop wceq wph wa vy wex vz cv vx cv vy cv cop wceq wps
      wa vy wex wo vz cv vx cv vy cv cop wceq wph wps wo wa vz cv vx cv vy cv
      cop wceq wph wa vz cv vx cv vy cv cop wceq wps wa wo vy vz cv vx cv vy cv
      cop wceq wph wps andi exbii vz cv vx cv vy cv cop wceq wph wa vz cv vx cv
      vy cv cop wceq wps wa vy 19.43 bitr2i exbii bitr3i abbii eqtri wph vx vy
      copab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cab wps vx vy
      copab vz cv vx cv vy cv cop wceq wps wa vy wex vx wex vz cab wph vx vy vz
      df-opab wps vx vy vz df-opab uneq12i wph wps wo vx vy vz df-opab 3eqtr4i
      $.
  $}

  ${
    $d x y ph $.  $d y A $.  $d y B $.  $d y C $.  $d y D $.
    $( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
    mpteq12f $p |- ( ( A. x A = C /\ A. x e. A B = D ) ->
                    ( x e. A |-> B ) = ( x e. C |-> D ) ) $=
      cA cC wceq vx wal cB cD wceq vx cA wral wa vx cv cA wcel vy cv cB wceq wa
      vx vy copab vx cv cC wcel vy cv cD wceq wa vx vy copab vx cA cB cmpt vx
      cC cD cmpt cA cC wceq vx wal cB cD wceq vx cA wral wa vx cv cA wcel vy cv
      cB wceq wa vx cv cC wcel vy cv cD wceq wa vx vy cA cC wceq vx wal cB cD
      wceq vx cA wral vx cA cC wceq vx nfa1 cB cD wceq vx cA nfra1 nfan cA cC
      wceq vx wal cB cD wceq vx cA wral wa vy nfv cB cD wceq vx cA wral vx cv
      cA wcel vy cv cB wceq wa vx cv cA wcel vy cv cD wceq wa cA cC wceq vx wal
      vx cv cC wcel vy cv cD wceq wa cB cD wceq vx cA wral vx cv cA wcel vy cv
      cB wceq vy cv cD wceq cB cD wceq vx cA wral vx cv cA wcel wa cB cD vy cv
      cB cD wceq vx cA wral vx cv cA wcel cB cD wceq cB cD wceq vx cA rsp imp
      eqeq2d pm5.32da cA cC wceq vx wal vx cv cA wcel vx cv cC wcel vy cv cD
      wceq cA cC wceq vx wal cA cC vx cv cA cC wceq vx sp eleq2d anbi1d
      sylan9bbr opabbid vx vy cA cB df-mpt vx vy cC cD df-mpt 3eqtr4g $.

    mpteq12dv.1 $e |- ( ph -> A = C ) $.
    ${
      mpteq12dva.2 $e |- ( ( ph /\ x e. A ) -> B = D ) $.
      $( An equality inference for the maps to notation.  (Contributed by Mario
         Carneiro, 26-Jan-2017.) $)
      mpteq12dva $p |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $=
        wph cA cC wceq vx wal cB cD wceq vx cA wral vx cA cB cmpt vx cC cD cmpt
        wceq wph cA cC wceq vx mpteq12dv.1 alrimiv wph cB cD wceq vx cA
        mpteq12dva.2 ralrimiva vx cA cB cC cD mpteq12f syl2anc $.
    $}

    mpteq12dv.2 $e |- ( ph -> B = D ) $.
    $( An equality inference for the maps to notation.  (Contributed by NM,
       24-Aug-2011.)  (Revised by Mario Carneiro, 16-Dec-2013.) $)
    mpteq12dv $p |- ( ph -> ( x e. A |-> B ) = ( x e. C |-> D ) ) $=
      wph vx cA cB cC cD mpteq12dv.1 wph cB cD wceq vx cv cA wcel mpteq12dv.2
      adantr mpteq12dva $.
  $}

  ${
    $d x A $.  $d x C $.
    $( An equality theorem for the maps to notation.  (Contributed by NM,
       16-Dec-2013.) $)
    mpteq12 $p |- ( ( A = C /\ A. x e. A B = D ) ->
                    ( x e. A |-> B ) = ( x e. C |-> D ) ) $=
      cA cC wceq cA cC wceq vx wal cB cD wceq vx cA wral vx cA cB cmpt vx cC cD
      cmpt wceq cA cC wceq vx ax-17 vx cA cB cC cD mpteq12f sylan $.
  $}

  ${
    $d x A $.  $d x B $.
    $( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
    mpteq1 $p |- ( A = B -> ( x e. A |-> C ) = ( x e. B |-> C ) ) $=
      cA cB wceq cC cC wceq vx cA wral vx cA cC cmpt vx cB cC cmpt wceq cC cC
      wceq vx cA vx cv cA wcel cC eqidd rgen vx cA cC cB cC mpteq12 mpan2 $.

    mpteq1d.1 $e |- ( ph -> A = B ) $.
    $( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 11-Jun-2016.) $)
    mpteq1d $p |- ( ph -> ( x e. A |-> C ) = ( x e. B |-> C ) ) $=
      wph cA cB wceq vx cA cC cmpt vx cB cC cmpt wceq mpteq1d.1 vx cA cB cC
      mpteq1 syl $.
  $}

  ${
    mpteq2ia.1 $e |- ( x e. A -> B = C ) $.
    $( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
    mpteq2ia $p |- ( x e. A |-> B ) = ( x e. A |-> C ) $=
      cA cA wceq vx wal cB cC wceq vx cA wral vx cA cB cmpt vx cA cC cmpt wceq
      cA cA wceq vx cA eqid ax-gen cB cC wceq vx cA mpteq2ia.1 rgen vx cA cB cA
      cC mpteq12f mp2an $.
  $}

  ${
    mpteq2i.1 $e |- B = C $.
    $( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
    mpteq2i $p |- ( x e. A |-> B ) = ( x e. A |-> C ) $=
      vx cA cB cC cB cC wceq vx cv cA wcel mpteq2i.1 a1i mpteq2ia $.
  $}

  ${
    mpteq12i.1 $e |- A = C $.
    mpteq12i.2 $e |- B = D $.
    $( An equality inference for the maps to notation.  (Contributed by Scott
       Fenton, 27-Oct-2010.)  (Revised by Mario Carneiro, 16-Dec-2013.) $)
    mpteq12i $p |- ( x e. A |-> B ) = ( x e. C |-> D ) $=
      vx cA cB cmpt vx cC cD cmpt wceq wtru vx cA cB cC cD cA cC wceq wtru
      mpteq12i.1 a1i cB cD wceq wtru mpteq12i.2 a1i mpteq12dv trud $.
  $}

  ${
    mpteq2da.1 $e |- F/ x ph $.
    mpteq2da.2 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
    $( Slightly more general equality inference for the maps to notation.
       (Contributed by FL, 14-Sep-2013.)  (Revised by Mario Carneiro,
       16-Dec-2013.) $)
    mpteq2da $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $=
      wph cA cA wceq vx wal cB cC wceq vx cA wral vx cA cB cmpt vx cA cC cmpt
      wceq cA cA wceq vx cA eqid ax-gen wph cB cC wceq vx cA mpteq2da.1 wph vx
      cv cA wcel cB cC wceq mpteq2da.2 ex ralrimi vx cA cB cA cC mpteq12f
      sylancr $.
  $}

  ${
    $d x ph $.
    mpteq2dva.1 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
    $( Slightly more general equality inference for the maps to notation.
       (Contributed by Scott Fenton, 25-Apr-2012.) $)
    mpteq2dva $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $=
      wph vx cA cB cC wph vx nfv mpteq2dva.1 mpteq2da $.
  $}

  ${
    $d x ph $.
    mpteq2dv.1 $e |- ( ph -> B = C ) $.
    $( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 23-Aug-2014.) $)
    mpteq2dv $p |- ( ph -> ( x e. A |-> B ) = ( x e. A |-> C ) ) $=
      wph vx cA cB cC wph cB cC wceq vx cv cA wcel mpteq2dv.1 adantr mpteq2dva
      $.
  $}

  ${
    $d z A $.  $d z B $.  $d x y z $.
    nfmpt.1 $e |- F/_ x A $.
    nfmpt.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by NM, 20-Feb-2013.) $)
    nfmpt $p |- F/_ x ( y e. A |-> B ) $=
      vx vy cA cB cmpt vy cv cA wcel vz cv cB wceq wa vy vz copab vy vz cA cB
      df-mpt vy cv cA wcel vz cv cB wceq wa vy vz vx vy cv cA wcel vz cv cB
      wceq vx vx vy cA nfmpt.1 nfcri vx vz cv cB nfmpt.2 nfeq2 nfan nfopab
      nfcxfr $.
  $}

  ${
    $d A z $.  $d B z $.  $d x y $.  $d x z $.
    $( Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by FL, 17-Feb-2008.) $)
    nfmpt1 $p |- F/_ x ( x e. A |-> B ) $=
      vx vx cA cB cmpt vx cv cA wcel vz cv cB wceq wa vx vz copab vx vz cA cB
      df-mpt vx cv cA wcel vz cv cB wceq wa vx vz nfopab1 nfcxfr $.
  $}

  ${
    $d w z x A $.  $d w z y A $.  $d w z B $.  $d w z C $.
    cbvmpt.1 $e |- F/_ y B $.
    cbvmpt.2 $e |- F/_ x C $.
    cbvmpt.3 $e |- ( x = y -> B = C ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable conditions.  (Contributed by NM, 11-Sep-2011.) $)
    cbvmpt $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $=
      vx cv cA wcel vz cv cB wceq wa vx vz copab vy cv cA wcel vz cv cC wceq wa
      vy vz copab vx cA cB cmpt vy cA cC cmpt vx cv cA wcel vz cv cB wceq wa vx
      vz copab vw cv cA wcel vz cv cB wceq vx vw wsb wa vw vz copab vy cv cA
      wcel vz cv cC wceq wa vy vz copab vx cv cA wcel vz cv cB wceq wa vw cv cA
      wcel vz cv cB wceq vx vw wsb wa vx vz vw vx cv cA wcel vz cv cB wceq wa
      vw nfv vw cv cA wcel vz cv cB wceq vx vw wsb vx vw cv cA wcel vx nfv vz
      cv cB wceq vx vw nfs1v nfan vx cv vw cv wceq vx cv cA wcel vw cv cA wcel
      vz cv cB wceq vz cv cB wceq vx vw wsb vx cv vw cv cA eleq1 vz cv cB wceq
      vx vw sbequ12 anbi12d cbvopab1 vw cv cA wcel vz cv cB wceq vx vw wsb wa
      vy cv cA wcel vz cv cC wceq wa vw vz vy vw cv cA wcel vz cv cB wceq vx vw
      wsb vy vw cv cA wcel vy nfv vz cv cB wceq vx vw vy vy vz cv cB cbvmpt.1
      nfeq2 nfsb nfan vy cv cA wcel vz cv cC wceq wa vw nfv vw cv vy cv wceq vw
      cv cA wcel vy cv cA wcel vz cv cB wceq vx vw wsb vz cv cC wceq vw cv vy
      cv cA eleq1 vw cv vy cv wceq vz cv cB wceq vx vw wsb vz cv cB wceq vx vy
      wsb vz cv cC wceq vz cv cB wceq vw vy vx sbequ vz cv cB wceq vz cv cC
      wceq vx vy vx vz cv cC cbvmpt.2 nfeq2 vx cv vy cv wceq cB cC vz cv
      cbvmpt.3 eqeq2d sbie syl6bb anbi12d cbvopab1 eqtri vx vz cA cB df-mpt vy
      vz cA cC df-mpt 3eqtr4i $.
  $}

  ${
    $d A x $.  $d A y $.  $d B y $.  $d C x $.
    cbvmptv.1 $e |- ( x = y -> B = C ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  (Contributed by Mario Carneiro, 19-Feb-2013.) $)
    cbvmptv $p |- ( x e. A |-> B ) = ( y e. A |-> C ) $=
      vx vy cA cB cC vy cB nfcv vx cC nfcv cbvmptv.1 cbvmpt $.
  $}

  ${
    $d x y $.  $d y B $.
    $( Function with universal domain in maps-to notation.  (Contributed by NM,
       16-Aug-2013.) $)
    mptv $p |- ( x e. _V |-> B ) = { <. x , y >. | y = B } $=
      vx cvv cB cmpt vx cv cvv wcel vy cv cB wceq wa vx vy copab vy cv cB wceq
      vx vy copab vx vy cvv cB df-mpt vy cv cB wceq vx cv cvv wcel vy cv cB
      wceq wa vx vy vx cv cvv wcel vy cv cB wceq vx vex biantrur opabbii eqtr4i
      $.
  $}


