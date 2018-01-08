
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Partial_and_complete_ordering.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Founded and well-ordering relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new constant symbols. $)
  $c Fr $. $( Well-founded predicate symbol (read: 'well-founded'). $)
  $c Se $. $( Set-like predicate symbol (read: 'set-like'). $)
  $c We $. $( Well-ordering predicate symbol (read: 'well-orders') $)

  $( Extend wff notation to include the well-founded predicate.  Read:  ' ` R `
     is a well-founded relation on ` A ` .' $)
  wfr $a wff R Fr A $.

  $( Extend wff notation to include the set-like predicate.  Read:  ' ` R ` is
     set-like on ` A ` .' $)
  wse $a wff R Se A $.

  $( Extend wff notation to include the well-ordering predicate.
     Read:  ' ` R ` well-orders ` A ` .' $)
  wwe $a wff R We A $.

  ${
    $d x y z R $.  $d x y z A $.
    $( Define the well-founded relation predicate.  Definition 6.24(1) of
       [TakeutiZaring] p. 30.  For alternate definitions, see ~ dffr2 and
       ~ dffr3 .  (Contributed by NM, 3-Apr-1994.) $)
    df-fr $a |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) ->
                E. y e. x A. z e. x -. z R y ) ) $.

    $( Define the set-like predicate.  (Contributed by Mario Carneiro,
       19-Nov-2014.) $)
    df-se $a |- ( R Se A <-> A. x e. A { y e. A | y R x } e. _V ) $.
  $}

  $( Define the well-ordering predicate.  For an alternate definition, see
     ~ dfwe2 .  (Contributed by NM, 3-Apr-1994.) $)
  df-we $a |- ( R We A <-> ( R Fr A /\ R Or A ) ) $.

  ${
    $d x y z A $.  $d x y z B $.  $d x y z R $.  $d x y V $.
    $( Property of well-founded relation (one direction of definition).
       (Contributed by NM, 18-Mar-1997.) $)
    fri $p |- ( ( ( B e. C /\ R Fr A ) /\ ( B C_ A /\ B =/= (/) ) ) ->
                E. x e. B A. y e. B -. y R x ) $=
      cB cC wcel cA cR wfr cB cA wss cB c0 wne wa vy cv vx cv cR wbr wn vy cB
      wral vx cB wrex cA cR wfr vz cv cA wss vz cv c0 wne wa vy cv vx cv cR wbr
      wn vy vz cv wral vx vz cv wrex wi vz wal cB cC wcel cB cA wss cB c0 wne
      wa vy cv vx cv cR wbr wn vy cB wral vx cB wrex wi vz vx vy cA cR df-fr vz
      cv cA wss vz cv c0 wne wa vy cv vx cv cR wbr wn vy vz cv wral vx vz cv
      wrex wi cB cA wss cB c0 wne wa vy cv vx cv cR wbr wn vy cB wral vx cB
      wrex wi vz cB cC vz cv cB wceq vz cv cA wss vz cv c0 wne wa cB cA wss cB
      c0 wne wa vy cv vx cv cR wbr wn vy vz cv wral vx vz cv wrex vy cv vx cv
      cR wbr wn vy cB wral vx cB wrex vz cv cB wceq vz cv cA wss cB cA wss vz
      cv c0 wne cB c0 wne vz cv cB cA sseq1 vz cv cB c0 neeq1 anbi12d vy cv vx
      cv cR wbr wn vy vz cv wral vy cv vx cv cR wbr wn vy cB wral vx vz cv cB
      vy cv vx cv cR wbr wn vy vz cv cB raleq rexeqbi1dv imbi12d spcgv syl5bi
      imp31 $.

    $( The ` R ` -preimage of an element of the base set in a set-like relation
       is a set.  (Contributed by Mario Carneiro, 19-Nov-2014.) $)
    seex $p |- ( ( R Se A /\ B e. A ) -> { x e. A | x R B } e. _V ) $=
      cA cR wse vx cv vy cv cR wbr vx cA crab cvv wcel vy cA wral cB cA wcel vx
      cv cB cR wbr vx cA crab cvv wcel vy vx cA cR df-se vx cv vy cv cR wbr vx
      cA crab cvv wcel vx cv cB cR wbr vx cA crab cvv wcel vy cB cA vy cv cB
      wceq vx cv vy cv cR wbr vx cA crab vx cv cB cR wbr vx cA crab cvv vy cv
      cB wceq vx cv vy cv cR wbr vx cv cB cR wbr vx cA vy cv cB vx cv cR breq2
      rabbidv eleq1d rspccva sylanb $.

    $( Any relation on a set is set-like on it.  (Contributed by Mario
       Carneiro, 22-Jun-2015.) $)
    exse $p |- ( A e. V -> R Se A ) $=
      cA cV wcel vy cv vx cv cR wbr vy cA crab cvv wcel vx cA wral cA cR wse cA
      cV wcel vy cv vx cv cR wbr vy cA crab cvv wcel vx cA vy cv vx cv cR wbr
      vy cA cV rabexg ralrimivw vx vy cA cR df-se sylibr $.
  $}

  ${
    $d x y z A $.  $d x y z R $.
    $( Alternate definition of well-founded relation.  Similar to Definition
       6.21 of [TakeutiZaring] p. 30.  (Contributed by NM, 17-Feb-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.)  (Proof shortened by
       Mario Carneiro, 23-Jun-2015.) $)
    dffr2 $p |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) ->
                E. y e. x { z e. x | z R y } = (/) ) ) $=
      cA cR wfr vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv
      wral vy vx cv wrex wi vx wal vx cv cA wss vx cv c0 wne wa vz cv vy cv cR
      wbr vz vx cv crab c0 wceq vy vx cv wrex wi vx wal vx vy vz cA cR df-fr vx
      cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx
      cv wrex wi vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv
      wral vy vx cv wrex wi vx vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx
      cv wrex vz cv vy cv cR wbr wn vz vx cv wral vy vx cv wrex vx cv cA wss vx
      cv c0 wne wa vz cv vy cv cR wbr vz vx cv crab c0 wceq vz cv vy cv cR wbr
      wn vz vx cv wral vy vx cv vz cv vy cv cR wbr vz vx cv rabeq0 rexbii
      imbi2i albii bitr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.
    frc.1 $e |- B e. _V $.
    $( Property of well-founded relation (one direction of definition using
       class variables).  (Contributed by NM, 17-Feb-2004.)  (Revised by Mario
       Carneiro, 19-Nov-2014.) $)
    frc $p |- ( ( R Fr A /\ B C_ A /\ B =/= (/) ) ->
                E. x e. B { y e. B | y R x } = (/) ) $=
      cA cR wfr cB cA wss cB c0 wne w3a vy cv vx cv cR wbr wn vy cB wral vx cB
      wrex vy cv vx cv cR wbr vy cB crab c0 wceq vx cB wrex cA cR wfr cB cA wss
      cB c0 wne vy cv vx cv cR wbr wn vy cB wral vx cB wrex cB cvv wcel cA cR
      wfr cB cA wss cB c0 wne wa vy cv vx cv cR wbr wn vy cB wral vx cB wrex
      frc.1 vx vy cA cB cvv cR fri mpanl1 3impb vy cv vx cv cR wbr vy cB crab
      c0 wceq vy cv vx cv cR wbr wn vy cB wral vx cB vy cv vx cv cR wbr vy cB
      rabeq0 rexbii sylibr $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z R $.  $d x y S $.
    $( Subset theorem for the well-founded predicate.  Exercise 1 of
       [TakeutiZaring] p. 31.  (Contributed by NM, 3-Apr-1994.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)
    frss $p |- ( A C_ B -> ( R Fr B -> R Fr A ) ) $=
      cA cB wss vx cv cB wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv
      wral vy vx cv wrex wi vx wal vx cv cA wss vx cv c0 wne wa vz cv vy cv cR
      wbr wn vz vx cv wral vy vx cv wrex wi vx wal cB cR wfr cA cR wfr cA cB
      wss vx cv cB wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv wral vy
      vx cv wrex wi vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv
      wral vy vx cv wrex wi vx cA cB wss vx cv cA wss vx cv c0 wne wa vx cv cB
      wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv wral vy vx cv wrex cA
      cB wss vx cv cA wss vx cv cB wss vx cv c0 wne vx cv cA wss cA cB wss vx
      cv cB wss vx cv cA cB sstr2 com12 anim1d imim1d alimdv vx vy vz cB cR
      df-fr vx vy vz cA cR df-fr 3imtr4g $.

    $( Subset theorem for the set-like predicate.  (Contributed by Mario
       Carneiro, 24-Jun-2015.) $)
    sess1 $p |- ( R C_ S -> ( S Se A -> R Se A ) ) $=
      cR cS wss vy cv vx cv cS wbr vy cA crab cvv wcel vx cA wral vy cv vx cv
      cR wbr vy cA crab cvv wcel vx cA wral cA cS wse cA cR wse cR cS wss vy cv
      vx cv cS wbr vy cA crab cvv wcel vy cv vx cv cR wbr vy cA crab cvv wcel
      vx cA cR cS wss vy cv vx cv cR wbr vy cA crab vy cv vx cv cS wbr vy cA
      crab wss vy cv vx cv cS wbr vy cA crab cvv wcel vy cv vx cv cR wbr vy cA
      crab cvv wcel wi cR cS wss vy cv vx cv cR wbr vy cv vx cv cS wbr vy cA cR
      cS wss vy cv cA wcel wa cR cS vy cv vx cv cR cS wss vy cv cA wcel simpl
      ssbrd ss2rabdv vy cv vx cv cR wbr vy cA crab vy cv vx cv cS wbr vy cA
      crab wss vy cv vx cv cS wbr vy cA crab cvv wcel vy cv vx cv cR wbr vy cA
      crab cvv wcel vy cv vx cv cR wbr vy cA crab vy cv vx cv cS wbr vy cA crab
      cvv ssexg ex syl ralimdv vx vy cA cS df-se vx vy cA cR df-se 3imtr4g $.

    $( Subset theorem for the set-like predicate.  (Contributed by Mario
       Carneiro, 24-Jun-2015.) $)
    sess2 $p |- ( A C_ B -> ( R Se B -> R Se A ) ) $=
      cA cB wss vy cv vx cv cR wbr vy cB crab cvv wcel vx cB wral vy cv vx cv
      cR wbr vy cA crab cvv wcel vx cA wral cB cR wse cA cR wse cA cB wss vy cv
      vx cv cR wbr vy cB crab cvv wcel vx cB wral vy cv vx cv cR wbr vy cB crab
      cvv wcel vx cA wral vy cv vx cv cR wbr vy cA crab cvv wcel vx cA wral vy
      cv vx cv cR wbr vy cB crab cvv wcel vx cA cB ssralv cA cB wss vy cv vx cv
      cR wbr vy cB crab cvv wcel vy cv vx cv cR wbr vy cA crab cvv wcel vx cA
      cA cB wss vy cv vx cv cR wbr vy cA crab vy cv vx cv cR wbr vy cB crab wss
      vy cv vx cv cR wbr vy cB crab cvv wcel vy cv vx cv cR wbr vy cA crab cvv
      wcel wi vy cv vx cv cR wbr vy cA cB rabss2 vy cv vx cv cR wbr vy cA crab
      vy cv vx cv cR wbr vy cB crab wss vy cv vx cv cR wbr vy cB crab cvv wcel
      vy cv vx cv cR wbr vy cA crab cvv wcel vy cv vx cv cR wbr vy cA crab vy
      cv vx cv cR wbr vy cB crab cvv ssexg ex syl ralimdv syld vx vy cB cR
      df-se vx vy cA cR df-se 3imtr4g $.
  $}

  ${
    $d x y z R $.  $d x y z S $.  $d x y z A $.
    $( Equality theorem for the well-founded predicate.  (Contributed by NM,
       9-Mar-1997.) $)
    freq1 $p |- ( R = S -> ( R Fr A <-> S Fr A ) ) $=
      cR cS wceq vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv
      wral vy vx cv wrex wi vx wal vx cv cA wss vx cv c0 wne wa vz cv vy cv cS
      wbr wn vz vx cv wral vy vx cv wrex wi vx wal cA cR wfr cA cS wfr cR cS
      wceq vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv wral vy
      vx cv wrex wi vx cv cA wss vx cv c0 wne wa vz cv vy cv cS wbr wn vz vx cv
      wral vy vx cv wrex wi vx cR cS wceq vz cv vy cv cR wbr wn vz vx cv wral
      vy vx cv wrex vz cv vy cv cS wbr wn vz vx cv wral vy vx cv wrex vx cv cA
      wss vx cv c0 wne wa cR cS wceq vz cv vy cv cR wbr wn vz cv vy cv cS wbr
      wn vy vz vx cv vx cv cR cS wceq vz cv vy cv cR wbr vz cv vy cv cS wbr vz
      cv vy cv cR cS breq notbid rexralbidv imbi2d albidv vx vy vz cA cR df-fr
      vx vy vz cA cS df-fr 3bitr4g $.
  $}

  $( Equality theorem for the well-founded predicate.  (Contributed by NM,
     3-Apr-1994.) $)
  freq2 $p |- ( A = B -> ( R Fr A <-> R Fr B ) ) $=
    cA cB wceq cA cR wfr cB cR wfr cA cB wceq cB cA wss cA cR wfr cB cR wfr wi
    cB cA eqimss2 cB cA cR frss syl cA cB wceq cA cB wss cB cR wfr cA cR wfr wi
    cA cB eqimss cA cB cR frss syl impbid $.

  $( Equality theorem for the set-like predicate.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)
  seeq1 $p |- ( R = S -> ( R Se A <-> S Se A ) ) $=
    cR cS wceq cA cR wse cA cS wse cR cS wceq cS cR wss cA cR wse cA cS wse wi
    cS cR eqimss2 cA cS cR sess1 syl cR cS wceq cR cS wss cA cS wse cA cR wse
    wi cR cS eqimss cA cR cS sess1 syl impbid $.

  $( Equality theorem for the set-like predicate.  (Contributed by Mario
     Carneiro, 24-Jun-2015.) $)
  seeq2 $p |- ( A = B -> ( R Se A <-> R Se B ) ) $=
    cA cB wceq cA cR wse cB cR wse cA cB wceq cB cA wss cA cR wse cB cR wse wi
    cB cA eqimss2 cB cA cR sess2 syl cA cB wceq cA cB wss cB cR wse cA cR wse
    wi cA cB eqimss cA cB cR sess2 syl impbid $.

  ${
    $d y R a b c $.  $d y A a b c $.  $d x y a b c $.
    nffr.r $e |- F/_ x R $.
    nffr.a $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for well-founded relations.
       (Contributed by Stefan O'Rear, 20-Jan-2015.)  (Revised by Mario
       Carneiro, 14-Oct-2016.) $)
    nffr $p |- F/ x R Fr A $=
      cA cR wfr va cv cA wss va cv c0 wne wa vc cv vb cv cR wbr wn vc va cv
      wral vb va cv wrex wi va wal vx va vb vc cA cR df-fr va cv cA wss va cv
      c0 wne wa vc cv vb cv cR wbr wn vc va cv wral vb va cv wrex wi vx va va
      cv cA wss va cv c0 wne wa vc cv vb cv cR wbr wn vc va cv wral vb va cv
      wrex vx va cv cA wss va cv c0 wne vx vx va cv cA vx va cv nfcv nffr.a
      nfss va cv c0 wne vx nfv nfan vc cv vb cv cR wbr wn vc va cv wral vx vb
      va cv vx va cv nfcv vc cv vb cv cR wbr wn vx vc va cv vx va cv nfcv vc cv
      vb cv cR wbr vx vx vc cv vb cv cR vx vc cv nfcv nffr.r vx vb cv nfcv nfbr
      nfn nfral nfrex nfim nfal nfxfr $.

    $( Bound-variable hypothesis builder for set-like relations.  (Contributed
       by Mario Carneiro, 24-Jun-2015.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
    nfse $p |- F/ x R Se A $=
      cA cR wse va cv vb cv cR wbr va cA crab cvv wcel vb cA wral vx vb va cA
      cR df-se va cv vb cv cR wbr va cA crab cvv wcel vx vb cA nffr.a vx va cv
      vb cv cR wbr va cA crab cvv va cv vb cv cR wbr vx va cA vx va cv vb cv cR
      vx va cv nfcv nffr.r vx vb cv nfcv nfbr nffr.a nfrab nfel1 nfral nfxfr $.

    $( Bound-variable hypothesis builder for well-orderings.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
    nfwe $p |- F/ x R We A $=
      cA cR wwe cA cR wfr cA cR wor wa vx cA cR df-we cA cR wfr cA cR wor vx vx
      cA cR nffr.r nffr.a nffr vx cA cR nffr.r nffr.a nfso nfan nfxfr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.
    $( A well-founded relation is irreflexive.  Special case of Proposition
       6.23 of [TakeutiZaring] p. 30.  (Contributed by NM, 2-Jan-1994.)
       (Revised by Mario Carneiro, 22-Jun-2015.) $)
    frirr $p |- ( ( R Fr A /\ B e. A ) -> -. B R B ) $=
      cA cR wfr cB cA wcel wa vx cv vy cv cR wbr vx cB csn crab c0 wceq vy cB
      csn wrex cB cB cR wbr wn cA cR wfr cB cA wcel wa cA cR wfr cB csn cA wss
      cB csn c0 wne vx cv vy cv cR wbr vx cB csn crab c0 wceq vy cB csn wrex cA
      cR wfr cB cA wcel simpl cA cR wfr cB cA wcel wa cB cA cA cR wfr cB cA
      wcel simpr snssd cB cA wcel cB csn c0 wne cA cR wfr cB cA snnzg adantl vy
      vx cA cB csn cR cB snex frc syl3anc cB cA wcel vx cv vy cv cR wbr vx cB
      csn crab c0 wceq vy cB csn wrex cB cB cR wbr wn wb cA cR wfr cB cA wcel
      vx cv vy cv cR wbr vx cB csn crab c0 wceq vy cB csn wrex vx cv cB cR wbr
      wn vx cB csn wral cB cB cR wbr wn vx cv vy cv cR wbr vx cB csn crab c0
      wceq vx cv cB cR wbr wn vx cB csn wral vy cB cA vx cv vy cv cR wbr vx cB
      csn crab c0 wceq vx cv vy cv cR wbr wn vx cB csn wral vy cv cB wceq vx cv
      cB cR wbr wn vx cB csn wral vx cv vy cv cR wbr vx cB csn rabeq0 vy cv cB
      wceq vx cv vy cv cR wbr wn vx cv cB cR wbr wn vx cB csn vy cv cB wceq vx
      cv vy cv cR wbr vx cv cB cR wbr vy cv cB vx cv cR breq2 notbid ralbidv
      syl5bb rexsng vx cv cB cR wbr wn cB cB cR wbr wn vx cB cA vx cv cB wceq
      vx cv cB cR wbr cB cB cR wbr vx cv cB cB cR breq1 notbid ralsng bitrd
      adantl mpbid $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y R $.
    $( A well-founded relation has no 2-cycle loops.  Special case of
       Proposition 6.23 of [TakeutiZaring] p. 30.  (Contributed by NM,
       30-May-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)
    fr2nr $p |- ( ( R Fr A /\ ( B e. A /\ C e. A ) ) ->
                -. ( B R C /\ C R B ) ) $=
      cA cR wfr cB cA wcel cC cA wcel wa wa cB cC cR wbr wn cC cB cR wbr wn wo
      cB cC cR wbr cC cB cR wbr wa wn cA cR wfr cB cA wcel cC cA wcel wa wa cC
      cB cR wbr wn cB cC cR wbr wn cA cR wfr cB cA wcel cC cA wcel wa wa vx cv
      cB cR wbr wn vx cB cC cpr wral vx cv cC cR wbr wn vx cB cC cpr wral wo cC
      cB cR wbr wn cB cC cR wbr wn wo cA cR wfr cB cA wcel cC cA wcel wa wa vx
      cv vy cv cR wbr wn vx cB cC cpr wral vy cB cC cpr wrex vx cv cB cR wbr wn
      vx cB cC cpr wral vx cv cC cR wbr wn vx cB cC cpr wral wo cA cR wfr cB cA
      wcel cC cA wcel wa wa cB cC cpr cvv wcel cA cR wfr cB cC cpr cA wss cB cC
      cpr c0 wne vx cv vy cv cR wbr wn vx cB cC cpr wral vy cB cC cpr wrex cB
      cC cpr cvv wcel cA cR wfr cB cA wcel cC cA wcel wa wa cB cC prex a1i cA
      cR wfr cB cA wcel cC cA wcel wa simpl cB cA wcel cC cA wcel wa cB cC cpr
      cA wss cA cR wfr cB cC cA prssi adantl cB cA wcel cB cC cpr c0 wne cA cR
      wfr cC cA wcel cB cC cA prnzg ad2antrl vy vx cA cB cC cpr cvv cR fri
      syl22anc cB cA wcel cC cA wcel wa vx cv vy cv cR wbr wn vx cB cC cpr wral
      vy cB cC cpr wrex vx cv cB cR wbr wn vx cB cC cpr wral vx cv cC cR wbr wn
      vx cB cC cpr wral wo wb cA cR wfr vx cv vy cv cR wbr wn vx cB cC cpr wral
      vx cv cB cR wbr wn vx cB cC cpr wral vx cv cC cR wbr wn vx cB cC cpr wral
      vy cB cC cA cA vy cv cB wceq vx cv vy cv cR wbr wn vx cv cB cR wbr wn vx
      cB cC cpr vy cv cB wceq vx cv vy cv cR wbr vx cv cB cR wbr vy cv cB vx cv
      cR breq2 notbid ralbidv vy cv cC wceq vx cv vy cv cR wbr wn vx cv cC cR
      wbr wn vx cB cC cpr vy cv cC wceq vx cv vy cv cR wbr vx cv cC cR wbr vy
      cv cC vx cv cR breq2 notbid ralbidv rexprg adantl mpbid cA cR wfr cB cA
      wcel cC cA wcel wa wa vx cv cB cR wbr wn vx cB cC cpr wral cC cB cR wbr
      wn vx cv cC cR wbr wn vx cB cC cpr wral cB cC cR wbr wn cA cR wfr cB cA
      wcel cC cA wcel wa wa cC cB cC cpr wcel vx cv cB cR wbr wn vx cB cC cpr
      wral cC cB cR wbr wn wi cC cA wcel cC cB cC cpr wcel cA cR wfr cB cA wcel
      cB cC cA prid2g ad2antll vx cv cB cR wbr wn cC cB cR wbr wn vx cC cB cC
      cpr vx cv cC wceq vx cv cB cR wbr cC cB cR wbr vx cv cC cB cR breq1
      notbid rspcv syl cA cR wfr cB cA wcel cC cA wcel wa wa cB cB cC cpr wcel
      vx cv cC cR wbr wn vx cB cC cpr wral cB cC cR wbr wn wi cB cA wcel cB cB
      cC cpr wcel cA cR wfr cC cA wcel cB cC cA prid1g ad2antrl vx cv cC cR wbr
      wn cB cC cR wbr wn vx cB cB cC cpr vx cv cB wceq vx cv cC cR wbr cB cC cR
      wbr vx cv cB cC cR breq1 notbid rspcv syl orim12d mpd orcomd cB cC cR wbr
      cC cB cR wbr ianor sylibr $.
  $}

  ${
    $d x y z R $.
    $( Any relation is well-founded on the empty set.  (Contributed by NM,
       17-Sep-1993.) $)
    fr0 $p |- R Fr (/) $=
      c0 cR wfr vx cv c0 wss vx cv c0 wne wa vz cv vy cv cR wbr vz vx cv crab
      c0 wceq vy vx cv wrex wi vx vx vy vz c0 cR dffr2 vx cv c0 wss vx cv c0
      wne vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx cv wrex vx cv c0 wss
      vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx cv wrex vx cv c0 vx cv c0
      wss vx cv c0 wceq vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx cv wrex
      wn vx cv ss0 a1d necon1ad imp mpgbir $.
  $}

  ${
    $d A x y z $.  $d R x y z $.  $d ph y z $.  $d ps x z $.
    frminex.1 $e |- A e. _V $.
    frminex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( If an element of a well-founded set satisfies a property ` ph ` , then
       there is a minimal element that satisfies ` ph ` .  (Contributed by Jeff
       Madsen, 18-Jun-2010.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)
    frminex $p |- ( R Fr A -> ( E. x e. A ph ->
                      E. x e. A ( ph /\ A. y e. A ( ps -> -. y R x ) ) ) ) $=
      wph vx cA wrex wph vx cA crab c0 wne cA cR wfr wph wps vy cv vx cv cR wbr
      wn wi vy cA wral wa vx cA wrex wph vx cA rabn0 cA cR wfr wph vx cA crab
      c0 wne wph wps vy cv vx cv cR wbr wn wi vy cA wral wa vx cA wrex wph vx
      cA crab cvv wcel wph vx cA crab cA wss cA cR wfr wph vx cA crab c0 wne wa
      wph wps vy cv vx cv cR wbr wn wi vy cA wral wa vx cA wrex wph vx cA
      frminex.1 rabex wph vx cA ssrab2 wph vx cA crab cvv wcel cA cR wfr wph vx
      cA crab cA wss wph vx cA crab c0 wne wph wps vy cv vx cv cR wbr wn wi vy
      cA wral wa vx cA wrex wph vx cA crab cvv wcel cA cR wfr wa wph vx cA crab
      cA wss wph vx cA crab c0 wne wa wa vy cv vz cv cR wbr wn vy wph vx cA
      crab wral vz wph vx cA crab wrex wph wps vy cv vx cv cR wbr wn wi vy cA
      wral wa vx cA wrex vz vy cA wph vx cA crab cvv cR fri vy cv vz cv cR wbr
      wn vy wph vx cA crab wral vz wph vx cA crab wrex wps vy cv vz cv cR wbr
      wn wi vy cA wral vz wph vx cA crab wrex wph wps vy cv vx cv cR wbr wn wi
      vy cA wral wa vx cA wrex vy cv vz cv cR wbr wn vy wph vx cA crab wral wps
      vy cv vz cv cR wbr wn wi vy cA wral vz wph vx cA crab wph wps vy cv vz cv
      cR wbr wn vy vx cA frminex.2 ralrab rexbii wph wps vy cv vz cv cR wbr wn
      wi vy cA wral wps vy cv vx cv cR wbr wn wi vy cA wral vz vx cA vz cv vx
      cv wceq wps vy cv vz cv cR wbr wn wi wps vy cv vx cv cR wbr wn wi vy cA
      vz cv vx cv wceq vy cv vz cv cR wbr wn vy cv vx cv cR wbr wn wps vz cv vx
      cv wceq vy cv vz cv cR wbr vy cv vx cv cR wbr vz cv vx cv vy cv cR breq2
      notbid imbi2d ralbidv rexrab2 bitri sylib an4s mpanl12 ex syl5bir $.
  $}

  ${
    $d x A $.
    $( Irreflexivity of the epsilon relation: a class founded by epsilon is not
       a member of itself.  (Contributed by NM, 18-Apr-1994.)  (Revised by
       Mario Carneiro, 22-Jun-2015.) $)
    efrirr $p |- ( _E Fr A -> -. A e. A ) $=
      cA cep wfr cA cA wcel cA cep wfr cA cA wcel cA cA wcel wn cA cep wfr cA
      cA wcel wa cA cA cep wbr cA cA wcel cA cA cep frirr cA cA wcel cA cA cep
      wbr cA cA wcel wb cA cep wfr cA cA cA epelg adantl mtbid ex pm2.01d $.
  $}

  $( A set founded by epsilon contains no 2-cycle loops.  (Contributed by NM,
     19-Apr-1994.) $)
  efrn2lp $p |- ( ( _E Fr A /\ ( B e. A /\ C e. A ) ) ->
                -. ( B e. C /\ C e. B ) ) $=
    cA cep wfr cB cA wcel cC cA wcel wa wa cB cC cep wbr cC cB cep wbr wa cB cC
    wcel cC cB wcel wa cA cB cC cep fr2nr cB cA wcel cC cA wcel wa cB cC cep
    wbr cC cB cep wbr wa cB cC wcel cC cB wcel wa wb cA cep wfr cC cA wcel cB
    cC cep wbr cB cC wcel cB cA wcel cC cB cep wbr cC cB wcel cB cC cA epelg cC
    cB cA epelg bi2anan9r adantl mtbid $.

  ${
    $d x y A $.
    $( The epsilon relation is set-like on any class.  (This is the origin of
       the term "set-like": a set-like relation "acts like" the epsilon
       relation of sets and their elements.)  (Contributed by Mario Carneiro,
       22-Jun-2015.) $)
    epse $p |- _E Se A $=
      cA cep wse vy cv vx cv cep wbr vy cA crab cvv wcel vx cA wral vy cv vx cv
      cep wbr vy cA crab cvv wcel vx cA vy cv vx cv cep wbr vy cA crab vy cv vx
      cv cep wbr vy cab vx cv vy cv vx cv cep wbr vy cab cvv vy cv vx cv cep
      wbr vy vx cv vy cv vx cv cep wbr vy cv vx cv wcel vy vx epel bicomi
      abbi2i vx vex eqeltrri vy cv vx cv cep wbr vy cA crab vy cv vx cv cep wbr
      vy cab cA cin vy cv vx cv cep wbr vy cab vy cv vx cv cep wbr vy cA dfrab2
      vy cv vx cv cep wbr vy cab cA inss1 eqsstri ssexi rgenw vx vy cA cep
      df-se mpbir $.
  $}

  $( Similar to Theorem 7.2 of [TakeutiZaring] p. 35, of except that the Axiom
     of Regularity is not required due to antecedent ` _E Fr A ` .
     (Contributed by NM, 4-May-1994.) $)
  tz7.2 $p |- ( ( Tr A /\ _E Fr A /\ B e. A ) -> ( B C_ A /\ B =/= A ) ) $=
    cA wtr cA cep wfr cB cA wcel cB cA wss cB cA wne wa cA wtr cB cA wcel cB cA
    wss cA cep wfr cB cA wne cA cB trss cA cep wfr cB cA wcel cB cA cA cep wfr
    cB cA wcel wn cB cA wceq cA cA wcel wn cA efrirr cB cA wceq cB cA wcel cA
    cA wcel cB cA cA eleq1 notbid syl5ibrcom necon2ad anim12ii 3impia $.

  ${
    $d x y z A $.
    $( An alternate way of saying that the epsilon relation is well-founded.
       (Contributed by NM, 17-Feb-2004.)  (Revised by Mario Carneiro,
       23-Jun-2015.) $)
    dfepfr $p |- ( _E Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) ->
                  E. y e. x ( x i^i y ) = (/) ) ) $=
      cA cep wfr vx cv cA wss vx cv c0 wne wa vz cv vy cv cep wbr vz vx cv crab
      c0 wceq vy vx cv wrex wi vx wal vx cv cA wss vx cv c0 wne wa vx cv vy cv
      cin c0 wceq vy vx cv wrex wi vx wal vx vy vz cA cep dffr2 vx cv cA wss vx
      cv c0 wne wa vz cv vy cv cep wbr vz vx cv crab c0 wceq vy vx cv wrex wi
      vx cv cA wss vx cv c0 wne wa vx cv vy cv cin c0 wceq vy vx cv wrex wi vx
      vz cv vy cv cep wbr vz vx cv crab c0 wceq vy vx cv wrex vx cv vy cv cin
      c0 wceq vy vx cv wrex vx cv cA wss vx cv c0 wne wa vz cv vy cv cep wbr vz
      vx cv crab c0 wceq vx cv vy cv cin c0 wceq vy vx cv vz cv vy cv cep wbr
      vz vx cv crab vx cv vy cv cin c0 vz cv vy cv cep wbr vz vx cv crab vz cv
      vy cv wcel vz vx cv crab vx cv vy cv cin vz cv vy cv cep wbr vz cv vy cv
      wcel vz vx cv vz cv vy cv cep wbr vz cv vy cv wcel wb vz cv vx cv wcel vz
      vy epel a1i rabbiia vz vx cv vy cv dfin5 eqtr4i eqeq1i rexbii imbi2i
      albii bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.
    epfrc.1 $e |- B e. _V $.
    $( A subset of an epsilon-founded class has a minimal element.
       (Contributed by NM, 17-Feb-2004.)  (Revised by David Abernethy,
       22-Feb-2011.) $)
    epfrc $p |- ( ( _E Fr A /\ B C_ A /\ B =/= (/) ) ->
                  E. x e. B ( B i^i x ) = (/) ) $=
      cA cep wfr cB cA wss cB c0 wne w3a vy cv vx cv cep wbr vy cB crab c0 wceq
      vx cB wrex cB vx cv cin c0 wceq vx cB wrex vx vy cA cB cep epfrc.1 frc cB
      vx cv cin c0 wceq vy cv vx cv cep wbr vy cB crab c0 wceq vx cB cB vx cv
      cin vy cv vx cv cep wbr vy cB crab c0 cB vx cv cin vy cv vx cv wcel vy cB
      crab vy cv vx cv cep wbr vy cB crab vy cB vx cv dfin5 vy cv vx cv cep wbr
      vy cv vx cv wcel vy cB vy cv vx cv cep wbr vy cv vx cv wcel wb vy cv cB
      wcel vy vx epel a1i rabbiia eqtr4i eqeq1i rexbii sylibr $.
  $}

  $( Subset theorem for the well-ordering predicate.  Exercise 4 of
     [TakeutiZaring] p. 31.  (Contributed by NM, 19-Apr-1994.) $)
  wess $p |- ( A C_ B -> ( R We B -> R We A ) ) $=
    cA cB wss cB cR wfr cB cR wor wa cA cR wfr cA cR wor wa cB cR wwe cA cR wwe
    cA cB wss cB cR wfr cA cR wfr cB cR wor cA cR wor cA cB cR frss cA cB cR
    soss anim12d cB cR df-we cA cR df-we 3imtr4g $.

  $( Equality theorem for the well-ordering predicate.  (Contributed by NM,
     9-Mar-1997.) $)
  weeq1 $p |- ( R = S -> ( R We A <-> S We A ) ) $=
    cR cS wceq cA cR wfr cA cR wor wa cA cS wfr cA cS wor wa cA cR wwe cA cS
    wwe cR cS wceq cA cR wfr cA cS wfr cA cR wor cA cS wor cA cR cS freq1 cA cR
    cS soeq1 anbi12d cA cR df-we cA cS df-we 3bitr4g $.

  $( Equality theorem for the well-ordering predicate.  (Contributed by NM,
     3-Apr-1994.) $)
  weeq2 $p |- ( A = B -> ( R We A <-> R We B ) ) $=
    cA cB wceq cA cR wfr cA cR wor wa cB cR wfr cB cR wor wa cA cR wwe cB cR
    wwe cA cB wceq cA cR wfr cB cR wfr cA cR wor cB cR wor cA cB cR freq2 cA cB
    cR soeq2 anbi12d cA cR df-we cB cR df-we 3bitr4g $.

  $( A well-ordering is well-founded.  (Contributed by NM, 22-Apr-1994.) $)
  wefr $p |- ( R We A -> R Fr A ) $=
    cA cR wwe cA cR wfr cA cR wor cA cR df-we simplbi $.

  $( A well-ordering is a strict ordering.  (Contributed by NM,
     16-Mar-1997.) $)
  weso $p |- ( R We A -> R Or A ) $=
    cA cR wwe cA cR wfr cA cR wor cA cR df-we simprbi $.

  $( The elements of an epsilon well-ordering are comparable.  (Contributed by
     NM, 17-May-1994.) $)
  wecmpep $p |- ( ( _E We A /\ ( x e. A /\ y e. A ) ) ->
                 ( x e. y \/ x = y \/ y e. x ) ) $=
    cA cep wwe cA cep wor vx cv cA wcel vy cv cA wcel wa vx cv vy cv wcel vx cv
    vy cv wceq vy cv vx cv wcel w3o cA cep weso cA cep wor vx cv cA wcel vy cv
    cA wcel wa wa vx cv vy cv cep wbr vx cv vy cv wceq vy cv vx cv cep wbr w3o
    vx cv vy cv wcel vx cv vy cv wceq vy cv vx cv wcel w3o cA vx cv vy cv cep
    solin vx cv vy cv cep wbr vx cv vy cv wcel vx cv vy cv wceq vx cv vy cv
    wceq vy cv vx cv cep wbr vy cv vx cv wcel vx vy epel vx cv vy cv wceq biid
    vy vx epel 3orbi123i sylib sylan $.

  $( An epsilon well-ordering is a transitive relation.  (Contributed by NM,
     22-Apr-1994.) $)
  wetrep $p |- ( ( _E We A /\ ( x e. A /\ y e. A /\ z e. A ) ) ->
             ( ( x e. y /\ y e. z ) -> x e. z ) ) $=
    cA cep wwe vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a wa vx cv vy cv cep
    wbr vy cv vz cv cep wbr wa vx cv vz cv cep wbr vx cv vy cv wcel vy cv vz cv
    wcel wa vx cv vz cv wcel cA cep wwe cA cep wor vx cv cA wcel vy cv cA wcel
    vz cv cA wcel w3a vx cv vy cv cep wbr vy cv vz cv cep wbr wa vx cv vz cv
    cep wbr wi cA cep weso cA vx cv vy cv vz cv cep sotr sylan vx cv vy cv cep
    wbr vx cv vy cv wcel vy cv vz cv cep wbr vy cv vz cv wcel vx vy epel vy vz
    epel anbi12i vx vz epel 3imtr3g $.

  ${
    $d x y z R $.  $d y z A $.  $d x y z B $.
    $( A non-empty (possibly proper) subclass of a class well-ordered by ` _E `
       has a minimal element.  Special case of Proposition 6.26 of
       [TakeutiZaring] p. 31.  (Contributed by NM, 17-Feb-2004.) $)
    wefrc $p |- ( ( _E We A /\ B C_ A /\ B =/= (/) ) ->
               E. x e. B ( B i^i x ) = (/) ) $=
      cA cep wwe cB cA wss cB c0 wne cB vx cv cin c0 wceq vx cB wrex cB cA wss
      cA cep wwe cB cep wwe cB c0 wne cB vx cv cin c0 wceq vx cB wrex wi cB cA
      cep wess cB c0 wne vy cv cB wcel vy wex cB cep wwe cB vx cv cin c0 wceq
      vx cB wrex vy cB n0 cB cep wwe vy cv cB wcel cB vx cv cin c0 wceq vx cB
      wrex vy cB cep wwe vy cv cB wcel cB vx cv cin c0 wceq vx cB wrex cB cep
      wwe vy cv cB wcel wa cB vx cv cin c0 wceq vx cB wrex cB vy cv cin c0 vy
      cv cB wcel cB vy cv cin c0 wceq cB vx cv cin c0 wceq vx cB wrex wi cB cep
      wwe vy cv cB wcel cB vy cv cin c0 wceq cB vx cv cin c0 wceq vx cB wrex cB
      vx cv cin c0 wceq cB vy cv cin c0 wceq vx vy cv cB vx cv vy cv wceq cB vx
      cv cin cB vy cv cin c0 vx cv vy cv cB ineq2 eqeq1d rspcev ex adantl cB
      cep wwe vy cv cB wcel wa cB vy cv cin c0 wne vx cv vy cv wcel cB vy cv
      cin vx cv cin c0 wceq wa vx cB wrex cB vx cv cin c0 wceq vx cB wrex cB
      cep wwe cB vy cv cin c0 wne vx cv vy cv wcel cB vy cv cin vx cv cin c0
      wceq wa vx cB wrex wi vy cv cB wcel cB cep wwe cB vy cv cin c0 wne cB vy
      cv cin vx cv cin c0 wceq vx cB vy cv cin wrex vx cv vy cv wcel cB vy cv
      cin vx cv cin c0 wceq wa vx cB wrex cB cep wwe cB vy cv cin cB wss cB vy
      cv cin c0 wne cB vy cv cin vx cv cin c0 wceq vx cB vy cv cin wrex wi cB
      vy cv inss1 cB cep wwe cB vy cv cin cB wss cB vy cv cin c0 wne cB vy cv
      cin vx cv cin c0 wceq vx cB vy cv cin wrex cB cep wwe cB cep wfr cB vy cv
      cin cB wss cB vy cv cin c0 wne cB vy cv cin vx cv cin c0 wceq vx cB vy cv
      cin wrex cB cep wefr vx cB cB vy cv cin vy cv cB vy vex inex2 epfrc
      syl3an1 3exp mpi cB vy cv cin vx cv cin c0 wceq vx cv vy cv wcel cB vy cv
      cin vx cv cin c0 wceq wa vx cB vy cv cin cB vx cv cB vy cv cin wcel cB vy
      cv cin vx cv cin c0 wceq wa vx cv cB wcel vx cv vy cv wcel wa cB vy cv
      cin vx cv cin c0 wceq wa vx cv cB wcel vx cv vy cv wcel cB vy cv cin vx
      cv cin c0 wceq wa wa vx cv cB vy cv cin wcel vx cv cB wcel vx cv vy cv
      wcel wa cB vy cv cin vx cv cin c0 wceq vx cv cB vy cv elin anbi1i vx cv
      cB wcel vx cv vy cv wcel cB vy cv cin vx cv cin c0 wceq anass bitri
      rexbii2 syl6ib adantr cB cep wwe vy cv cB wcel wa vx cv vy cv wcel cB vy
      cv cin vx cv cin c0 wceq wa cB vx cv cin c0 wceq vx cB cB cep wwe vy cv
      cB wcel wa vx cv cB wcel vx cv vy cv wcel cB vy cv cin vx cv cin c0 wceq
      cB vx cv cin c0 wceq cB cep wwe vy cv cB wcel wa vx cv cB wcel vx cv vy
      cv wcel cB vy cv cin vx cv cin c0 wceq cB vx cv cin c0 wceq wi cB cep wwe
      vy cv cB wcel wa vx cv cB wcel vx cv vy cv wcel wa cB vx cv cin vy cv wss
      cB vy cv cin vx cv cin c0 wceq cB vx cv cin c0 wceq wi cB cep wwe vy cv
      cB wcel wa vx cv cB wcel vx cv vy cv wcel wa vz cv vy cv wcel vz cB vx cv
      cin wral cB vx cv cin vy cv wss cB cep wwe vy cv cB wcel wa vx cv cB wcel
      vx cv vy cv wcel wa vz cv vy cv wcel vz cB vx cv cin cB cep wwe vy cv cB
      wcel wa vz cv cB vx cv cin wcel vx cv cB wcel vx cv vy cv wcel wa vz cv
      vy cv wcel cB cep wwe vy cv cB wcel wa vz cv cB vx cv cin wcel vx cv cB
      wcel vx cv vy cv wcel vz cv vy cv wcel vz cv cB vx cv cin wcel vz cv cB
      wcel vz cv vx cv wcel wa cB cep wwe vy cv cB wcel wa vx cv cB wcel vx cv
      vy cv wcel vz cv vy cv wcel wi wi vz cv cB vx cv elin cB cep wwe vy cv cB
      wcel wa vz cv cB wcel vz cv vx cv wcel vx cv cB wcel vx cv vy cv wcel vz
      cv vy cv wcel wi wi cB cep wwe vy cv cB wcel wa vz cv cB wcel vx cv cB
      wcel vz cv vx cv wcel vx cv vy cv wcel vz cv vy cv wcel wi cB cep wwe vy
      cv cB wcel vz cv cB wcel vx cv cB wcel vz cv vx cv wcel vx cv vy cv wcel
      vz cv vy cv wcel wi wi wi wi cB cep wwe vy cv cB wcel vz cv cB wcel vx cv
      cB wcel vz cv vx cv wcel vx cv vy cv wcel vz cv vy cv wcel wi wi vy cv cB
      wcel vz cv cB wcel wa vx cv cB wcel wa cB cep wwe vz cv cB wcel vx cv cB
      wcel vy cv cB wcel w3a vz cv vx cv wcel vx cv vy cv wcel vz cv vy cv wcel
      wi wi vy cv cB wcel vz cv cB wcel wa vx cv cB wcel wa vy cv cB wcel vz cv
      cB wcel vx cv cB wcel w3a vz cv cB wcel vx cv cB wcel vy cv cB wcel w3a
      vy cv cB wcel vz cv cB wcel vx cv cB wcel df-3an vy cv cB wcel vz cv cB
      wcel vx cv cB wcel 3anrot bitr3i cB cep wwe vz cv cB wcel vx cv cB wcel
      vy cv cB wcel w3a wa vz cv vx cv wcel vx cv vy cv wcel vz cv vy cv wcel
      vz vx vy cB wetrep exp3a sylan2b exp44 imp com34 imp3a syl5bi imp4a com23
      ralrimdv vz cB vx cv cin vy cv dfss3 syl6ibr cB vx cv cin vy cv wss cB vx
      cv cin c0 wceq cB vy cv cin vx cv cin c0 wceq cB vx cv cin vy cv wss cB
      vx cv cin cB vy cv cin vx cv cin c0 cB vx cv cin vy cv wss cB vx cv cin
      cB vy cv cin vx cv cin wceq cB vx cv cin vy cv wss cB vx cv cin cB vx cv
      cin vy cv cin wceq cB vx cv cin cB vy cv cin vx cv cin wceq cB vx cv cin
      vy cv dfss cB vx cv cin vy cv cin cB vy cv cin vx cv cin cB vx cv cin cB
      vx cv vy cv in32 eqeq2i bitri biimpi eqeq1d biimprd syl6 exp3a imp4a
      reximdvai syld pm2.61dne ex exlimdv syl5bi syl6com 3imp $.
  $}

  $( Any relation is a well-ordering of the empty set.  (Contributed by NM,
     16-Mar-1997.) $)
  we0 $p |- R We (/) $=
    c0 cR wwe c0 cR wfr c0 cR wor cR fr0 cR so0 c0 cR df-we mpbir2an $.

  ${
    $d x y z A $.  $d w x y z B $.  $d w x y z R $.
    $( A subset of a well-ordered set has a unique minimal element.
       (Contributed by NM, 18-Mar-1997.)  (Revised by Mario Carneiro,
       28-Apr-2015.) $)
    wereu $p |- ( ( R We A /\ ( B e. V /\ B C_ A /\ B =/= (/) ) ) ->
                E! x e. B A. y e. B -. y R x ) $=
      cA cR wwe cB cV wcel cB cA wss cB c0 wne w3a wa vy cv vx cv cR wbr wn vy
      cB wral vx cB wrex vy cv vx cv cR wbr wn vy cB wral vx cB wrmo vy cv vx
      cv cR wbr wn vy cB wral vx cB wreu cA cR wwe cA cR wfr cB cV wcel cB cA
      wss cB c0 wne w3a vy cv vx cv cR wbr wn vy cB wral vx cB wrex cA cR wefr
      cA cR wfr cB cV wcel cB cA wss cB c0 wne vy cv vx cv cR wbr wn vy cB wral
      vx cB wrex cB cV wcel cA cR wfr cB cA wss cB c0 wne vy cv vx cv cR wbr wn
      vy cB wral vx cB wrex wi wi cB cV wcel cA cR wfr wa cB cA wss cB c0 wne
      vy cv vx cv cR wbr wn vy cB wral vx cB wrex vx vy cA cB cV cR fri exp32
      expcom 3imp2 sylan cA cR wwe cB cV wcel cB cA wss cB c0 wne w3a wa cB cR
      wor vy cv vx cv cR wbr wn vy cB wral vx cB wrmo cA cR wwe cB cV wcel cB
      cA wss cB c0 wne w3a wa cB cA wss cA cR wor cB cR wor cA cR wwe cB cV
      wcel cB cA wss cB c0 wne simpr2 cA cR wwe cA cR wor cB cV wcel cB cA wss
      cB c0 wne w3a cA cR weso adantr cB cA cR soss sylc vx vy cB cR somo syl
      vy cv vx cv cR wbr wn vy cB wral vx cB reu5 sylanbrc $.

    $( All nonempty (possibly proper) subclasses of ` A ` , which has a
       well-founded relation ` R ` , have ` R `-minimal elements.  Proposition
       6.26 of [TakeutiZaring] p. 31.  (Contributed by Scott Fenton,
       29-Jan-2011.)  (Revised by Mario Carneiro, 24-Jun-2015.) $)
    wereu2 $p |- ( ( ( R We A /\ R Se A ) /\ ( B C_ A /\ B =/= (/) ) ) ->
                E! x e. B A. y e. B -. y R x ) $=
      cA cR wwe cA cR wse wa cB cA wss cB c0 wne wa wa vy cv vx cv cR wbr wn vy
      cB wral vx cB wrex vy cv vx cv cR wbr wn vy cB wral vx cB wrmo vy cv vx
      cv cR wbr wn vy cB wral vx cB wreu cA cR wwe cA cR wse wa cB cA wss cB c0
      wne vy cv vx cv cR wbr wn vy cB wral vx cB wrex cB c0 wne vz cv cB wcel
      vz wex cA cR wwe cA cR wse wa cB cA wss wa vy cv vx cv cR wbr wn vy cB
      wral vx cB wrex vz cB n0 cA cR wwe cA cR wse wa cB cA wss wa vz cv cB
      wcel vy cv vx cv cR wbr wn vy cB wral vx cB wrex vz cA cR wwe cA cR wse
      wa cB cA wss vz cv cB wcel vy cv vx cv cR wbr wn vy cB wral vx cB wrex cA
      cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vy cv vx cv cR wbr wn
      vy cB wral vx cB wrex vw cv vz cv cR wbr vw cB crab c0 vw cv vz cv cR wbr
      vw cB crab c0 wceq vw cv vz cv cR wbr wn vw cB wral cA cR wwe cA cR wse
      wa cB cA wss vz cv cB wcel wa wa vy cv vx cv cR wbr wn vy cB wral vx cB
      wrex vw cv vz cv cR wbr vw cB rabeq0 vz cv cB wcel vw cv vz cv cR wbr wn
      vw cB wral vy cv vx cv cR wbr wn vy cB wral vx cB wrex wi cA cR wwe cA cR
      wse wa cB cA wss vz cv cB wcel vw cv vz cv cR wbr wn vw cB wral vy cv vx
      cv cR wbr wn vy cB wral vx cB wrex vy cv vx cv cR wbr wn vy cB wral vw cv
      vz cv cR wbr wn vw cB wral vx vz cv cB vy cv vx cv cR wbr wn vy cB wral
      vw cv vx cv cR wbr wn vw cB wral vx vz weq vw cv vz cv cR wbr wn vw cB
      wral vy cv vx cv cR wbr wn vw cv vx cv cR wbr wn vy vw cB vy vw weq vy cv
      vx cv cR wbr vw cv vx cv cR wbr vy cv vw cv vx cv cR breq1 notbid cbvralv
      vx vz weq vw cv vx cv cR wbr wn vw cv vz cv cR wbr wn vw cB vx vz weq vw
      cv vx cv cR wbr vw cv vz cv cR wbr vx cv vz cv vw cv cR breq2 notbid
      ralbidv syl5bb rspcev ex ad2antll syl5bi cA cR wwe cA cR wse wa cB cA wss
      vz cv cB wcel wa wa vw cv vz cv cR wbr vw cB crab c0 wne vy cv vx cv cR
      wbr wn vy vw cv vz cv cR wbr vw cB crab wral vx vw cv vz cv cR wbr vw cB
      crab wrex vy cv vx cv cR wbr wn vy cB wral vx cB wrex cA cR wwe cA cR wse
      wa cB cA wss vz cv cB wcel wa wa vw cv vz cv cR wbr vw cB crab cvv wcel
      cA cR wfr vw cv vz cv cR wbr vw cB crab cA wss vw cv vz cv cR wbr vw cB
      crab c0 wne vy cv vx cv cR wbr wn vy vw cv vz cv cR wbr vw cB crab wral
      vx vw cv vz cv cR wbr vw cB crab wrex wi cA cR wwe cA cR wse wa cB cA wss
      vz cv cB wcel wa wa cB cR wse vz cv cB wcel vw cv vz cv cR wbr vw cB crab
      cvv wcel cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa cB cA wss
      cA cR wse cB cR wse cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel simprl
      cA cR wwe cA cR wse cB cA wss vz cv cB wcel wa simplr cB cA cR sess2 sylc
      cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel simprr vw cB vz cv cR seex
      syl2anc cA cR wwe cA cR wfr cA cR wse cB cA wss vz cv cB wcel wa cA cR
      wefr ad2antrr cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vw cv
      vz cv cR wbr vw cB crab cB cA vw cv vz cv cR wbr vw cB ssrab2 cA cR wwe
      cA cR wse wa cB cA wss vz cv cB wcel simprl syl5ss vw cv vz cv cR wbr vw
      cB crab cvv wcel cA cR wfr wa vw cv vz cv cR wbr vw cB crab cA wss vw cv
      vz cv cR wbr vw cB crab c0 wne vy cv vx cv cR wbr wn vy vw cv vz cv cR
      wbr vw cB crab wral vx vw cv vz cv cR wbr vw cB crab wrex vx vy cA vw cv
      vz cv cR wbr vw cB crab cvv cR fri expr syl21anc vy cv vx cv cR wbr wn vy
      vw cv vz cv cR wbr vw cB crab wral vx vw cv vz cv cR wbr vw cB crab wrex
      vx cv vz cv cR wbr vy cv vx cv cR wbr wn vy vw cv vz cv cR wbr vw cB crab
      wral wa vx cB wrex cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa
      vy cv vx cv cR wbr wn vy cB wral vx cB wrex vw cv vz cv cR wbr vx cv vz
      cv cR wbr vy cv vx cv cR wbr wn vy vw cv vz cv cR wbr vw cB crab wral vx
      vw cB vw cv vx cv vz cv cR breq1 rexrab cA cR wwe cA cR wse wa cB cA wss
      vz cv cB wcel wa wa vx cv vz cv cR wbr vy cv vx cv cR wbr wn vy vw cv vz
      cv cR wbr vw cB crab wral wa vy cv vx cv cR wbr wn vy cB wral vx cB cA cR
      wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vx cv cB wcel wa vx cv vz
      cv cR wbr vy cv vx cv cR wbr wn vy vw cv vz cv cR wbr vw cB crab wral vy
      cv vx cv cR wbr wn vy cB wral vy cv vx cv cR wbr wn vy vw cv vz cv cR wbr
      vw cB crab wral vy cv vz cv cR wbr vy cv vx cv cR wbr wn wi vy cB wral cA
      cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vx cv cB wcel wa vx cv
      vz cv cR wbr wa vy cv vx cv cR wbr wn vy cB wral vw cv vz cv cR wbr vy cv
      vz cv cR wbr vy cv vx cv cR wbr wn vy vw cB vw cv vy cv vz cv cR breq1
      ralrab cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vx cv cB wcel
      wa vx cv vz cv cR wbr wa vy cv vz cv cR wbr vy cv vx cv cR wbr wn wi vy
      cv vx cv cR wbr wn vy cB cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel
      wa wa vx cv cB wcel wa vx cv vz cv cR wbr wa vy cv cB wcel wa vy cv vz cv
      cR wbr vy cv vx cv cR wbr wn vy cv vx cv cR wbr wn cA cR wwe cA cR wse wa
      cB cA wss vz cv cB wcel wa wa vx cv cB wcel wa vx cv vz cv cR wbr wa vy
      cv cB wcel wa vy cv vx cv cR wbr vy cv vz cv cR wbr cA cR wwe cA cR wse
      wa cB cA wss vz cv cB wcel wa wa vx cv cB wcel wa vy cv cB wcel vx cv vz
      cv cR wbr vy cv vx cv cR wbr vy cv vz cv cR wbr wi cA cR wwe cA cR wse wa
      cB cA wss vz cv cB wcel wa wa vx cv cB wcel wa vy cv cB wcel wa vx cv vz
      cv cR wbr vy cv vx cv cR wbr vy cv vz cv cR wbr cA cR wwe cA cR wse wa cB
      cA wss vz cv cB wcel wa wa vx cv cB wcel wa vy cv cB wcel wa vy cv vx cv
      cR wbr vx cv vz cv cR wbr vy cv vz cv cR wbr cA cR wwe cA cR wse wa cB cA
      wss vz cv cB wcel wa wa vx cv cB wcel wa vy cv cB wcel wa cB cR wor vy cv
      cB wcel vx cv cB wcel vz cv cB wcel vy cv vx cv cR wbr vx cv vz cv cR wbr
      wa vy cv vz cv cR wbr wi cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel
      wa wa cB cR wor vx cv cB wcel vy cv cB wcel cA cR wwe cA cR wse wa cB cA
      wss vz cv cB wcel wa wa cB cA wss cA cR wor cB cR wor cA cR wwe cA cR wse
      wa cB cA wss vz cv cB wcel simprl cA cR wwe cA cR wor cA cR wse cB cA wss
      vz cv cB wcel wa cA cR weso ad2antrr cB cA cR soss sylc ad2antrr cA cR
      wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vx cv cB wcel wa vy cv cB
      wcel simpr cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel wa wa vx cv cB
      wcel vy cv cB wcel simplr cA cR wwe cA cR wse wa cB cA wss vz cv cB wcel
      wa wa vz cv cB wcel vx cv cB wcel vy cv cB wcel cA cR wwe cA cR wse wa cB
      cA wss vz cv cB wcel simprr ad2antrr cB vy cv vx cv vz cv cR sotr
      syl13anc ancomsd expdimp an32s con3d cA cR wwe cA cR wse wa cB cA wss vz
      cv cB wcel wa wa vx cv cB wcel wa vx cv vz cv cR wbr wa vy cv cB wcel wa
      vy cv vx cv cR wbr wn idd jad ralimdva syl5bi expimpd reximdva syl5bi
      syld pm2.61dne expr exlimdv syl5bi impr cA cR wwe cA cR wse wa cB cA wss
      cB c0 wne wa wa cB cR wor vy cv vx cv cR wbr wn vy cB wral vx cB wrmo cA
      cR wwe cA cR wse wa cB cA wss cB c0 wne wa wa cB cA wss cA cR wor cB cR
      wor cA cR wwe cA cR wse wa cB cA wss cB c0 wne simprl cA cR wwe cA cR wor
      cA cR wse cB cA wss cB c0 wne wa cA cR weso ad2antrr cB cA cR soss sylc
      vx vy cB cR somo syl vy cv vx cv cR wbr wn vy cB wral vx cB reu5 sylanbrc
      $.
  $}


