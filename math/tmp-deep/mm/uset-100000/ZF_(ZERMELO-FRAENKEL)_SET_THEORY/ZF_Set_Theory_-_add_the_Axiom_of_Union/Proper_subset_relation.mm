
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Curry_and_uncurry.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper subset relation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [C.] $.

  $( Extend class notation to include the reified proper subset relation. $)
  crpss $a class [C.] $.

  ${
    $d x y A $.  $d x y B $.
    $( Define a relation which corresponds to proper subsethood ~ df-pss on
       sets.  This allows us to use proper subsethood with general concepts
       that require relations, such as strict ordering, see ~ sorpss .
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    df-rpss $a |- [C.] = { <. x , y >. | x C. y } $.

    $( The proper subset relation is a relation.  (Contributed by Stefan
       O'Rear, 2-Nov-2014.) $)
    relrpss $p |- Rel [C.] $=
      vx cv vy cv wpss vx vy crpss vx vy df-rpss relopabi $.

    $( The proper subset relation on sets is the same as class proper
       subsethood.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    brrpssg $p |- ( B e. V -> ( A [C.] B <-> A C. B ) ) $=
      cB cV wcel cA cB crpss wbr cA cB wpss cB cvv wcel cA cvv wcel wa cB cV
      wcel cB cvv wcel cA cB crpss wbr cA cvv wcel cB cV elex cA cB crpss
      relrpss brrelexi anim12i cB cV wcel cA cB wpss wa cB cvv wcel cA cvv wcel
      cB cV wcel cB cvv wcel cA cB wpss cB cV elex adantr cA cB wpss cA cB wss
      cB cvv wcel cA cvv wcel cB cV wcel cA cB pssss cB cV elex cA cB cvv ssexg
      syl2anr jca cA cvv wcel cB cvv wcel cA cB crpss wbr cA cB wpss wb vx cv
      vy cv wpss cA vy cv wpss cA cB wpss vx vy cA cB cvv cvv crpss vx cv cA vy
      cv psseq1 vy cv cB cA psseq2 vx vy df-rpss brabg ancoms pm5.21nd $.
  $}

  ${
    brrpss.a $e |- B e. _V $.
    $( The proper subset relation on sets is the same as class proper
       subsethood.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    brrpss $p |- ( A [C.] B <-> A C. B ) $=
      cB cvv wcel cA cB crpss wbr cA cB wpss wb brrpss.a cA cB cvv brrpssg
      ax-mp $.
  $}

  ${
    $d x y z A $.
    $( Every class is partially ordered by proper subsets.  (Contributed by
       Stefan O'Rear, 2-Nov-2014.) $)
    porpss $p |- [C.] Po A $=
      cA crpss wpo vx cv vx cv crpss wbr wn vx cv vy cv crpss wbr vy cv vz cv
      crpss wbr wa vx cv vz cv crpss wbr wi wa vz cA wral vy cA wral vx cA wral
      vx cv vx cv crpss wbr wn vx cv vy cv crpss wbr vy cv vz cv crpss wbr wa
      vx cv vz cv crpss wbr wi wa vz cA wral vx vy cA cA vx cv vx cv crpss wbr
      wn vx cv vy cv crpss wbr vy cv vz cv crpss wbr wa vx cv vz cv crpss wbr
      wi wa vz cA vx cv vx cv crpss wbr wn vx cv vy cv crpss wbr vy cv vz cv
      crpss wbr wa vx cv vz cv crpss wbr wi wa vx cv vx cv wpss wn vx cv vy cv
      wpss vy cv vz cv wpss wa vx cv vz cv wpss wi vx cv pssirr vx cv vy cv vz
      cv psstr vx cv vx cv crpss wbr wn vx cv vx cv wpss wn vx cv vy cv crpss
      wbr vy cv vz cv crpss wbr wa vx cv vz cv crpss wbr wi vx cv vy cv wpss vy
      cv vz cv wpss wa vx cv vz cv wpss wi vx cv vx cv crpss wbr vx cv vx cv
      wpss vx cv vx cv vx vex brrpss notbii vx cv vy cv crpss wbr vy cv vz cv
      crpss wbr wa vx cv vy cv wpss vy cv vz cv wpss wa vx cv vz cv crpss wbr
      vx cv vz cv wpss vx cv vy cv crpss wbr vx cv vy cv wpss vy cv vz cv crpss
      wbr vy cv vz cv wpss vx cv vy cv vy vex brrpss vy cv vz cv vz vex brrpss
      anbi12i vx cv vz cv vz vex brrpss imbi12i anbi12i mpbir2an rgenw rgen2w
      vx vy vz cA crpss df-po mpbir $.

    $( Express strict ordering under proper subsets, i.e. the notion of a chain
       of sets.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    sorpss $p |- ( [C.] Or A <-> A. x e. A A. y e. A ( x C_ y \/ y C_ x ) ) $=
      vx cv vy cv crpss wbr vx vy weq vy cv vx cv crpss wbr w3o vy cA wral vx
      cA wral cA crpss wpo vx cv vy cv crpss wbr vx vy weq vy cv vx cv crpss
      wbr w3o vy cA wral vx cA wral wa vx cv vy cv wss vy cv vx cv wss wo vy cA
      wral vx cA wral cA crpss wor cA crpss wpo vx cv vy cv crpss wbr vx vy weq
      vy cv vx cv crpss wbr w3o vy cA wral vx cA wral cA porpss biantrur vx cv
      vy cv wss vy cv vx cv wss wo vx cv vy cv crpss wbr vx vy weq vy cv vx cv
      crpss wbr w3o vx vy cA cA vx cv vy cv wss vy cv vx cv wss wo vx cv vy cv
      wpss vx vy weq vy cv vx cv wpss w3o vx cv vy cv crpss wbr vx vy weq vy cv
      vx cv crpss wbr w3o vx cv vy cv sspsstri vx cv vy cv crpss wbr vx cv vy
      cv wpss vx vy weq vx vy weq vy cv vx cv crpss wbr vy cv vx cv wpss vx cv
      vy cv vy vex brrpss vx vy weq biid vy cv vx cv vx vex brrpss 3orbi123i
      bitr4i 2ralbii vx vy cA crpss df-so 3bitr4ri $.
  $}

  $( Property of a chain of sets.  (Contributed by Stefan O'Rear,
     2-Nov-2014.) $)
  sorpssi $p |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) ->
      ( B C_ C \/ C C_ B ) ) $=
    cA crpss wor cB cA wcel cC cA wcel wa wa cB cC wpss cB cC wceq cC cB wpss
    w3o cB cC wss cC cB wss wo cA crpss wor cB cA wcel cC cA wcel wa wa cB cC
    crpss wbr cB cC wceq cC cB crpss wbr w3o cB cC wpss cB cC wceq cC cB wpss
    w3o cA cB cC crpss solin cA crpss wor cB cA wcel cC cA wcel wa wa cB cC
    crpss wbr cB cC wpss cB cC wceq cB cC wceq cC cB crpss wbr cC cB wpss cA
    crpss wor cB cA wcel cC cA wcel wa wa cC cvv wcel cB cC crpss wbr cB cC
    wpss wb cC cA wcel cC cvv wcel cA crpss wor cB cA wcel cC cA elex ad2antll
    cB cC cvv brrpssg syl cA crpss wor cB cA wcel cC cA wcel wa wa cB cC wceq
    biidd cA crpss wor cB cA wcel cC cA wcel wa wa cB cvv wcel cC cB crpss wbr
    cC cB wpss wb cB cA wcel cB cvv wcel cA crpss wor cC cA wcel cB cA elex
    ad2antrl cC cB cvv brrpssg syl 3orbi123d mpbid cB cC sspsstri sylibr $.

  $( A chain of sets is closed under binary union.  (Contributed by Mario
     Carneiro, 16-May-2015.) $)
  sorpssun $p |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) ->
      ( B u. C ) e. A ) $=
    cA crpss wor cB cA wcel cC cA wcel wa wa cB cC wss cB cC cun cA wcel cC cB
    wss cA crpss wor cB cA wcel cC cA wcel wa wa cB cC cun cA wcel cB cC wss cC
    cA wcel cA crpss wor cB cA wcel cC cA wcel simprr cB cC wss cB cC cun cC
    wceq cB cC cun cA wcel cC cA wcel wb cB cC ssequn1 cB cC cun cC cA eleq1
    sylbi syl5ibrcom cA crpss wor cB cA wcel cC cA wcel wa wa cB cC cun cA wcel
    cC cB wss cB cA wcel cA crpss wor cB cA wcel cC cA wcel simprl cC cB wss cB
    cC cun cB wceq cB cC cun cA wcel cB cA wcel wb cC cB ssequn2 cB cC cun cB
    cA eleq1 sylbi syl5ibrcom cA cB cC sorpssi mpjaod $.

  $( A chain of sets is closed under binary intersection.  (Contributed by
     Mario Carneiro, 16-May-2015.) $)
  sorpssin $p |- ( ( [C.] Or A /\ ( B e. A /\ C e. A ) ) ->
      ( B i^i C ) e. A ) $=
    cA crpss wor cB cA wcel cC cA wcel wa wa cB cC wss cB cC cin cA wcel cC cB
    wss cA crpss wor cB cA wcel cC cA wcel wa wa cB cC cin cA wcel cB cC wss cB
    cA wcel cA crpss wor cB cA wcel cC cA wcel simprl cB cC wss cB cC cin cB
    wceq cB cC cin cA wcel cB cA wcel wb cB cC df-ss cB cC cin cB cA eleq1
    sylbi syl5ibrcom cA crpss wor cB cA wcel cC cA wcel wa wa cB cC cin cA wcel
    cC cB wss cC cA wcel cA crpss wor cB cA wcel cC cA wcel simprr cC cB wss cB
    cC cin cC wceq cB cC cin cA wcel cC cA wcel wb cC cB dfss1 cB cC cin cC cA
    eleq1 sylbi syl5ibrcom cA cB cC sorpssi mpjaod $.

  ${
    $d Y z w u v $.
    $( In a chain of sets, a maximal element is the union of the chain.
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    sorpssuni $p |- ( [C.] Or Y -> ( E. u e. Y A. v e. Y -. u C. v <->
        U. Y e. Y ) ) $=
      cY crpss wor vu cv vv cv wpss wn vv cY wral vu cY wrex cY cuni cY wcel cY
      crpss wor vu cv vv cv wpss wn vv cY wral cY cuni cY wcel vu cY cY crpss
      wor vu cv cY wcel vu cv vv cv wpss wn vv cY wral w3a cY cuni vu cv cY cY
      crpss wor vu cv cY wcel vu cv vv cv wpss wn vv cY wral w3a cY cuni vu cv
      cY crpss wor vu cv cY wcel vu cv vv cv wpss wn vv cY wral w3a vv cv vu cv
      wss vv cY wral cY cuni vu cv wss cY crpss wor vu cv cY wcel vu cv vv cv
      wpss wn vv cY wral vv cv vu cv wss vv cY wral cY crpss wor vu cv cY wcel
      wa vu cv vv cv wpss wn vv cv vu cv wss vv cY cY crpss wor vu cv cY wcel
      wa vv cv cY wcel wa vu cv vv cv wss vv cv vu cv wss wo vu cv vv cv wpss
      wn vv cv vu cv wss wi cY crpss wor vu cv cY wcel vv cv cY wcel vu cv vv
      cv wss vv cv vu cv wss wo cY vu cv vv cv sorpssi anassrs vu cv vv cv wss
      vu cv vv cv wpss wn vv cv vu cv wss wi vv cv vu cv wss vu cv vv cv wss vu
      cv vv cv wpss vu vv weq wo vu cv vv cv wpss wn vv cv vu cv wss wi vu cv
      vv cv sspss vu cv vv cv wpss wn vu cv vv cv wpss vu vv weq wo vu vv weq
      vv cv vu cv wss vu cv vv cv wpss vu vv weq orel1 vv cv vu cv eqimss2
      syl6com sylbi vv cv vu cv wss vu cv vv cv wpss wn ax-1 jaoi syl ralimdva
      3impia vv cY vu cv unissb sylibr vu cv cY wcel cY crpss wor vu cv cY cuni
      wss vu cv vv cv wpss wn vv cY wral vu cv cY elssuni 3ad2ant2 eqssd cY
      crpss wor vu cv cY wcel vu cv vv cv wpss wn vv cY wral simp2 eqeltrd
      rexlimdv3a cY cuni cY wcel cY cuni vv cv wpss wn vv cY wral vu cv vv cv
      wpss wn vv cY wral vu cY wrex cY cuni vv cv wpss wn vv cY vv cv cY wcel
      vv cv cY cuni wss cY cuni vv cv wpss wn vv cv cY elssuni vv cv cY cuni
      ssnpss syl rgen vu cv vv cv wpss wn vv cY wral cY cuni vv cv wpss wn vv
      cY wral vu cY cuni cY vu cv cY cuni wceq vu cv vv cv wpss wn cY cuni vv
      cv wpss wn vv cY vu cv cY cuni wceq vu cv vv cv wpss cY cuni vv cv wpss
      vu cv cY cuni vv cv psseq1 notbid ralbidv rspcev mpan2 impbid1 $.

    $( In a chain of sets, a minimal element is the intersection of the chain.
       (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    sorpssint $p |- ( [C.] Or Y -> ( E. u e. Y A. v e. Y -. v C. u <->
        |^| Y e. Y ) ) $=
      cY crpss wor vv cv vu cv wpss wn vv cY wral vu cY wrex cY cint cY wcel cY
      crpss wor vv cv vu cv wpss wn vv cY wral cY cint cY wcel vu cY cY crpss
      wor vu cv cY wcel vv cv vu cv wpss wn vv cY wral w3a cY cint vu cv cY cY
      crpss wor vu cv cY wcel vv cv vu cv wpss wn vv cY wral w3a cY cint vu cv
      vu cv cY wcel cY crpss wor cY cint vu cv wss vv cv vu cv wpss wn vv cY
      wral vu cv cY intss1 3ad2ant2 cY crpss wor vu cv cY wcel vv cv vu cv wpss
      wn vv cY wral w3a vu cv vv cv wss vv cY wral vu cv cY cint wss cY crpss
      wor vu cv cY wcel vv cv vu cv wpss wn vv cY wral vu cv vv cv wss vv cY
      wral cY crpss wor vu cv cY wcel wa vv cv vu cv wpss wn vu cv vv cv wss vv
      cY cY crpss wor vu cv cY wcel wa vv cv cY wcel wa vu cv vv cv wss vv cv
      vu cv wss wo vv cv vu cv wpss wn vu cv vv cv wss wi cY crpss wor vu cv cY
      wcel vv cv cY wcel vu cv vv cv wss vv cv vu cv wss wo cY vu cv vv cv
      sorpssi anassrs vu cv vv cv wss vv cv vu cv wpss wn vu cv vv cv wss wi vv
      cv vu cv wss vu cv vv cv wss vv cv vu cv wpss wn ax-1 vv cv vu cv wss vv
      cv vu cv wpss vv vu weq wo vv cv vu cv wpss wn vu cv vv cv wss wi vv cv
      vu cv sspss vv cv vu cv wpss wn vv cv vu cv wpss vv vu weq wo vv vu weq
      vu cv vv cv wss vv cv vu cv wpss vv vu weq orel1 vu cv vv cv eqimss2
      syl6com sylbi jaoi syl ralimdva 3impia vv vu cv cY ssint sylibr eqssd cY
      crpss wor vu cv cY wcel vv cv vu cv wpss wn vv cY wral simp2 eqeltrd
      rexlimdv3a cY cint cY wcel vv cv cY cint wpss wn vv cY wral vv cv vu cv
      wpss wn vv cY wral vu cY wrex vv cv cY cint wpss wn vv cY vv cv cY wcel
      cY cint vv cv wss vv cv cY cint wpss wn vv cv cY intss1 cY cint vv cv
      ssnpss syl rgen vv cv vu cv wpss wn vv cY wral vv cv cY cint wpss wn vv
      cY wral vu cY cint cY vu cv cY cint wceq vv cv vu cv wpss wn vv cv cY
      cint wpss wn vv cY vu cv cY cint wceq vv cv vu cv wpss vv cv cY cint wpss
      vu cv cY cint vv cv psseq2 notbid ralbidv rspcev mpan2 impbid1 $.
  $}

  ${
    $d Y z w b c $.  $d Y x y $.  $d Y d $.  $d d A b c $.  $d A x y b c $.
    $d Y u $.  $d A u $.  $d d u x y $.
    $( The componentwise complement of a chain of sets is also a chain of
       sets.  (Contributed by Stefan O'Rear, 2-Nov-2014.) $)
    sorpsscmpl $p |- ( [C.] Or Y -> [C.] Or { u e. ~P A | ( A \ u ) e. Y } ) $=
      cY crpss wor vx cv vy cv wss vy cv vx cv wss wo vy cA vu cv cdif cY wcel
      vu cA cpw crab wral vx cA vu cv cdif cY wcel vu cA cpw crab wral cA vu cv
      cdif cY wcel vu cA cpw crab crpss wor cY crpss wor vx cv vy cv wss vy cv
      vx cv wss wo vx vy cA vu cv cdif cY wcel vu cA cpw crab cA vu cv cdif cY
      wcel vu cA cpw crab vx cv cA vu cv cdif cY wcel vu cA cpw crab wcel vy cv
      cA vu cv cdif cY wcel vu cA cpw crab wcel wa vx cv cA cpw wcel vy cv cA
      cpw wcel wa cA vx cv cdif cY wcel cA vy cv cdif cY wcel wa wa cY crpss
      wor vx cv vy cv wss vy cv vx cv wss wo vx cv cA vu cv cdif cY wcel vu cA
      cpw crab wcel vx cv cA cpw wcel cA vx cv cdif cY wcel wa vy cv cA cpw
      wcel cA vy cv cdif cY wcel wa vx cv cA cpw wcel vy cv cA cpw wcel wa cA
      vx cv cdif cY wcel cA vy cv cdif cY wcel wa wa vy cv cA vu cv cdif cY
      wcel vu cA cpw crab wcel cA vu cv cdif cY wcel cA vx cv cdif cY wcel vu
      vx cv cA cpw vu vx weq cA vu cv cdif cA vx cv cdif cY vu cv vx cv cA
      difeq2 eleq1d elrab cA vu cv cdif cY wcel cA vy cv cdif cY wcel vu vy cv
      cA cpw vu vy weq cA vu cv cdif cA vy cv cdif cY vu cv vy cv cA difeq2
      eleq1d elrab vx cv cA cpw wcel cA vx cv cdif cY wcel wa vy cv cA cpw wcel
      cA vy cv cdif cY wcel wa wa vx cv cA cpw wcel vy cv cA cpw wcel wa cA vx
      cv cdif cY wcel cA vy cv cdif cY wcel wa wa vx cv cA cpw wcel cA vx cv
      cdif cY wcel vy cv cA cpw wcel cA vy cv cdif cY wcel an4 biimpi syl2anb
      cY crpss wor vx cv cA cpw wcel vy cv cA cpw wcel wa cA vx cv cdif cY wcel
      cA vy cv cdif cY wcel wa vx cv vy cv wss vy cv vx cv wss wo cA vx cv cdif
      cY wcel cA vy cv cdif cY wcel wa cY crpss wor vx cv cA cpw wcel vy cv cA
      cpw wcel wa vx cv vy cv wss vy cv vx cv wss wo cA vx cv cdif cY wcel cA
      vy cv cdif cY wcel wa cY crpss wor cA vx cv cdif cA vy cv cdif wss cA vy
      cv cdif cA vx cv cdif wss wo vx cv cA cpw wcel vy cv cA cpw wcel wa vx cv
      vy cv wss vy cv vx cv wss wo wi cY crpss wor cA vx cv cdif cY wcel cA vy
      cv cdif cY wcel wa cA vx cv cdif cA vy cv cdif wss cA vy cv cdif cA vx cv
      cdif wss wo cY cA vx cv cdif cA vy cv cdif sorpssi expcom cA vy cv cdif
      cA vx cv cdif wss cA vx cv cdif cA vy cv cdif wss vx cv cA cpw wcel vy cv
      cA cpw wcel wa vx cv vy cv wss vy cv vx cv wss wo wi vx cv cA cpw wcel vy
      cv cA cpw wcel wa cA vy cv cdif cA vx cv cdif wss cA vx cv cdif cA vy cv
      cdif wss wo vx cv vy cv wss vy cv vx cv wss wo vx cv cA cpw wcel cA cA vx
      cv cdif cdif vx cv wceq cA cA vy cv cdif cdif vy cv wceq cA vy cv cdif cA
      vx cv cdif wss cA vx cv cdif cA vy cv cdif wss wo vx cv vy cv wss vy cv
      vx cv wss wo wi vy cv cA cpw wcel vx cv cA cpw wcel vx cv cA wss cA cA vx
      cv cdif cdif vx cv wceq vx cv cA vx vex elpw vx cv cA dfss4 bitri vy cv
      cA cpw wcel vy cv cA wss cA cA vy cv cdif cdif vy cv wceq vy cv cA vy vex
      elpw vy cv cA dfss4 bitri cA cA vx cv cdif cdif vx cv wceq cA cA vy cv
      cdif cdif vy cv wceq wa cA vy cv cdif cA vx cv cdif wss vx cv vy cv wss
      cA vx cv cdif cA vy cv cdif wss vy cv vx cv wss cA vy cv cdif cA vx cv
      cdif wss cA cA vx cv cdif cdif cA cA vy cv cdif cdif wss cA cA vx cv cdif
      cdif vx cv wceq cA cA vy cv cdif cdif vy cv wceq wa vx cv vy cv wss cA vy
      cv cdif cA vx cv cdif cA sscon cA cA vx cv cdif cdif vx cv cA cA vy cv
      cdif cdif vy cv sseq12 syl5ib cA vx cv cdif cA vy cv cdif wss cA cA vy cv
      cdif cdif cA cA vx cv cdif cdif wss cA cA vx cv cdif cdif vx cv wceq cA
      cA vy cv cdif cdif vy cv wceq wa vy cv vx cv wss cA vx cv cdif cA vy cv
      cdif cA sscon cA cA vy cv cdif cdif vy cv wceq cA cA vx cv cdif cdif vx
      cv wceq cA cA vy cv cdif cdif cA cA vx cv cdif cdif wss vy cv vx cv wss
      wb cA cA vy cv cdif cdif vy cv cA cA vx cv cdif cdif vx cv sseq12 ancoms
      syl5ib orim12d syl2anb com12 orcoms syl6 com3l imp3a syl5 ralrimivv vx vy
      cA vu cv cdif cY wcel vu cA cpw crab sorpss sylibr $.
  $}



