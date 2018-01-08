
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Proper_subset_relation.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                            Iota properties

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w x y z A $.  $d w z F $.  $d x ps $.
    fvopab5.1 $e |- F = { <. x , y >. | ph } $.
    fvopab5.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( The value of a function that is expressed as an ordered pair
       abstraction.  (Contributed by NM, 19-Feb-2006.)  (Revised by Mario
       Carneiro, 11-Sep-2015.) $)
    fvopab5 $p |- ( A e. V -> ( F ` A ) = ( iota y ps ) ) $=
      cA cV wcel cA cvv wcel cA cF cfv wps vy cio wceq cA cV elex cA cvv wcel
      cA cF cfv cA vy cv cF wbr vy cio wps vy cio cA cF cfv cA vz cv cF wbr vz
      cio cA vy cv cF wbr vy cio vz cA cF df-fv cA vz cv cF wbr cA vy cv cF wbr
      vz vy vz cv vy cv cA cF breq2 vy cA vz cv cF vy cA nfcv vy cF wph vx vy
      copab fvopab5.1 wph vx vy nfopab2 nfcxfr vy vz cv nfcv nfbr cA vy cv cF
      wbr vz nfv cbviota eqtri cA cvv wcel cA vy cv cF wbr wps vy vx cv vy cv
      cF wbr wph wb cA vy cv cF wbr wps wb vx cA cvv vx cA nfcv cA vy cv cF wbr
      wps vx vx cA vy cv cF vx cA nfcv vx cF wph vx vy copab fvopab5.1 wph vx
      vy nfopab1 nfcxfr vx vy cv nfcv nfbr wps vx nfv nfbi vx cv cA wceq vx cv
      vy cv cF wbr cA vy cv cF wbr wph wps vx cv cA vy cv cF breq1 fvopab5.2
      bibi12d vx cv vy cv cF wbr vx cv vy cv cop cF wcel vx cv vy cv cop wph vx
      vy copab wcel wph vx cv vy cv cF df-br cF wph vx vy copab vx cv vy cv cop
      fvopab5.1 eleq2i wph vx vy opabid 3bitri vtoclgf iotabidv syl5eq syl $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w x y z C $.  $d y ch $.  $d w z ph $.
    $d w x y z D $.  $d x ps $.
    opiota.1 $e |- I =
      ( iota z E. x e. A E. y e. B ( z = <. x , y >. /\ ph ) ) $.
    opiota.2 $e |- X = ( 1st ` I ) $.
    opiota.3 $e |- Y = ( 2nd ` I ) $.
    opiota.4 $e |- ( x = C -> ( ph <-> ps ) ) $.
    opiota.5 $e |- ( y = D -> ( ps <-> ch ) ) $.
    $( The property of a uniquely specified ordered pair.  (Contributed by
       Mario Carneiro, 21-May-2015.) $)
    opiota $p |- ( E! z E. x e. A E. y e. B ( z = <. x , y >. /\ ph ) ->
      ( ( C e. A /\ D e. B /\ ch ) <-> ( C = X /\ D = Y ) ) ) $=
      vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz weu cC cA wcel
      cD cB wcel wa wch wa cC cD cop cI c1st cfv cI c2nd cfv cop wceq cC cA
      wcel cD cB wcel wch w3a cC cX wceq cD cY wceq wa vz cv vx cv vy cv cop
      wceq wph wa vy cB wrex vx cA wrex vz weu cC cA wcel cD cB wcel wa wch wa
      cC cA wcel cD cB wcel wa cC cD cop cI wceq wa cC cD cop cI wceq cC cD cop
      cI c1st cfv cI c2nd cfv cop wceq vz cv vx cv vy cv cop wceq wph wa vy cB
      wrex vx cA wrex vz weu cC cA wcel cD cB wcel wa wch cC cD cop cI wceq cC
      cA wcel cD cB wcel wa wch vx cv cC wceq vy cv cD wceq wa wph wa vy cB
      wrex vx cA wrex vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex
      vz weu cC cD cop cI wceq cC cA wcel cD cB wcel wa vx cv cC wceq vy cv cD
      wceq wa wph wa vy cB wrex vx cA wrex wch wph wps wch vx vy cC cD cA cB
      opiota.4 opiota.5 ceqsrex2v bicomd vz cv vx cv vy cv cop wceq wph wa vy
      cB wrex vx cA wrex vz weu vx cv cC wceq vy cv cD wceq wa wph wa vy cB
      wrex vx cA wrex vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex
      vz cio cC cD cop wceq cC cD cop cI wceq vz cv vx cv vy cv cop wceq wph wa
      vy cB wrex vx cA wrex vz weu vz cv vx cv vy cv cop wceq wph wa vy cB wrex
      vx cA wrex vx cv cC wceq vy cv cD wceq wa wph wa vy cB wrex vx cA wrex vz
      cC cD cop cvv cC cD cop cvv wcel vz cv vx cv vy cv cop wceq wph wa vy cB
      wrex vx cA wrex vz weu cC cD opex a1i vz cv vx cv vy cv cop wceq wph wa
      vy cB wrex vx cA wrex vz weu id vz cv cC cD cop wceq vz cv vx cv vy cv
      cop wceq wph wa vy cB wrex vx cA wrex vx cv cC wceq vy cv cD wceq wa wph
      wa vy cB wrex vx cA wrex wb vz cv vx cv vy cv cop wceq wph wa vy cB wrex
      vx cA wrex vz weu vz cv cC cD cop wceq vz cv vx cv vy cv cop wceq wph wa
      vx cv cC wceq vy cv cD wceq wa wph wa vx vy cA cB vz cv cC cD cop wceq vz
      cv vx cv vy cv cop wceq vx cv cC wceq vy cv cD wceq wa wph vz cv cC cD
      cop wceq vz cv vx cv vy cv cop wceq cC cD cop vx cv vy cv cop wceq vx cv
      cC wceq vy cv cD wceq wa vz cv cC cD cop vx cv vy cv cop eqeq1 cC cD cop
      vx cv vy cv cop wceq vx cv vy cv cop cC cD cop wceq vx cv cC wceq vy cv
      cD wceq wa cC cD cop vx cv vy cv cop eqcom vx cv vy cv cC cD vx vex vy
      vex opth bitri syl6bb anbi1d 2rexbidv adantl vz cv vx cv vy cv cop wceq
      wph wa vy cB wrex vx cA wrex vz nfeu1 vz cv vx cv vy cv cop wceq wph wa
      vy cB wrex vx cA wrex vz weu vx cv cC wceq vy cv cD wceq wa wph wa vy cB
      wrex vx cA wrex vz nfvd vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx
      cA wrex vz weu vz cC cD cop nfcvd iota2df cC cD cop cI wceq cI cC cD cop
      wceq vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz cio cC cD
      cop wceq cC cD cop cI eqcom cI vz cv vx cv vy cv cop wceq wph wa vy cB
      wrex vx cA wrex vz cio cC cD cop opiota.1 eqeq1i bitri syl6bbr sylan9bbr
      pm5.32da vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz weu
      cC cD cop cI wceq cC cA wcel cD cB wcel wa vz cv vx cv vy cv cop wceq wph
      wa vy cB wrex vx cA wrex vz weu cC cA wcel cD cB wcel wa cC cD cop cI
      wceq cI cA cB cxp wcel vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA
      wrex vz weu cI vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz
      cio cA cB cxp opiota.1 vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA
      wrex vz weu vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz
      cab cA cB cxp vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz
      cio vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz cA cB cxp
      vz cv vx cv vy cv cop wceq wph wa vz cv cA cB cxp wcel vx vy cA cB vx cv
      cA wcel vy cv cB wcel wa vz cv cA cB cxp wcel vz cv vx cv vy cv cop wceq
      wph wa vx cv vy cv cop cA cB cxp wcel vx cv vy cv cA cB opelxpi vz cv vx
      cv vy cv cop wceq wph wa vz cv vx cv vy cv cop cA cB cxp vz cv vx cv vy
      cv cop wceq wph simpl eleq1d syl5ibrcom rexlimivv abssi vz cv vx cv vy cv
      cop wceq wph wa vy cB wrex vx cA wrex vz iotacl sseldi syl5eqel cC cA
      wcel cD cB wcel wa cC cD cop cA cB cxp wcel cC cD cop cI wceq cI cA cB
      cxp wcel cC cD cA cB opelxp cC cD cop cI cA cB cxp eleq1 syl5bbr
      syl5ibrcom pm4.71rd vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA
      wrex vz weu cI cI c1st cfv cI c2nd cfv cop cC cD cop vz cv vx cv vy cv
      cop wceq wph wa vy cB wrex vx cA wrex vz weu cI cA cB cxp wcel cI cI c1st
      cfv cI c2nd cfv cop wceq vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx
      cA wrex vz weu cI vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex
      vz cio cA cB cxp opiota.1 vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx
      cA wrex vz weu vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz
      cab cA cB cxp vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz
      cio vz cv vx cv vy cv cop wceq wph wa vy cB wrex vx cA wrex vz cA cB cxp
      vz cv vx cv vy cv cop wceq wph wa vz cv cA cB cxp wcel vx vy cA cB vx cv
      cA wcel vy cv cB wcel wa vz cv cA cB cxp wcel vz cv vx cv vy cv cop wceq
      wph wa vx cv vy cv cop cA cB cxp wcel vx cv vy cv cA cB opelxpi vz cv vx
      cv vy cv cop wceq wph wa vz cv vx cv vy cv cop cA cB cxp vz cv vx cv vy
      cv cop wceq wph simpl eleq1d syl5ibrcom rexlimivv abssi vz cv vx cv vy cv
      cop wceq wph wa vy cB wrex vx cA wrex vz iotacl sseldi syl5eqel cI cA cB
      1st2nd2 syl eqeq2d 3bitr2d cC cA wcel cD cB wcel wch df-3an cC cX wceq cD
      cY wceq wa cC cI c1st cfv wceq cD cI c2nd cfv wceq wa cC cD cop cI c1st
      cfv cI c2nd cfv cop wceq cC cX wceq cC cI c1st cfv wceq cD cY wceq cD cI
      c2nd cfv wceq cX cI c1st cfv cC opiota.2 eqeq2i cY cI c2nd cfv cD
      opiota.3 eqeq2i anbi12i cC cD cI c1st cfv cI c2nd cfv cI c1st fvex cI
      c2nd fvex opth2 bitr4i 3bitr4g $.
  $}

  ${
    $d x y z B $.  $d x y z F $.  $d z ph $.  $d x z ps $.
    opabiota.1 $e |- F = { <. x , y >. | { y | ph } = { y } } $.
    $( Define a function whose value is "the unique ` y ` such that
       ` ph ( x , y ) ` ".  (Contributed by NM, 19-May-2015.) $)
    opabiotafun $p |- Fun F $=
      cF wfun wph vy cab vy cv csn wceq vx vy copab wfun wph vy cab vy cv csn
      wceq vx vy copab wfun wph vy cab vy cv csn wceq vy wmo vx wph vy cab vy
      cv csn wceq vx vy funopab wph vy cab vy cv csn wceq vy wmo wph vy cab vz
      cv csn wceq vz wmo wph vy cab vz cv csn wceq vz cv wph vy cab cuni wceq
      wi wph vy cab vz cv csn wceq vz wmo vz wph vy cab vz cv csn wceq vz wph
      vy cab cuni mo2icl wph vy cab vz cv csn wceq wph vy cab cuni vz cv csn
      cuni vz cv wph vy cab vz cv csn unieq vz cv vz vex unisn syl6req mpg wph
      vy cab vy cv csn wceq wph vy cab vz cv csn wceq vy vz wph vy cab vy cv
      csn wceq vz nfv vy wph vy cab vz cv csn wph vy nfab1 nfeq1 vy cv vz cv
      wceq vy cv csn vz cv csn wph vy cab vy cv vz cv sneq eqeq2d cbvmo mpbir
      mpgbir cF wph vy cab vy cv csn wceq vx vy copab opabiota.1 funeqi mpbir
      $.

    $( Define a function whose value is "the unique ` y ` such that
       ` ph ( x , y ) ` ".  (Contributed by NM, 16-Nov-2013.) $)
    opabiotadm $p |- dom F = { x | E! y ph } $=
      wph vy cab vy cv csn wceq vx vy copab cdm wph vy cab vy cv csn wceq vy
      wex vx cab cF cdm wph vy weu vx cab wph vy cab vy cv csn wceq vx vy
      dmopab cF wph vy cab vy cv csn wceq vx vy copab opabiota.1 dmeqi wph vy
      weu wph vy cab vy cv csn wceq vy wex vx wph vy euabsn abbii 3eqtr4i $.

    opabiota.2 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( Define a function whose value is "the unique ` y ` such that
       ` ph ( x , y ) ` ".  (Contributed by NM, 16-Nov-2013.) $)
    opabiota $p |- ( B e. dom F -> ( F ` B ) = ( iota y ps ) ) $=
      vx cv cF cfv wph vy cio wceq cB cF cfv wps vy cio wceq vx cB cF cdm vx cv
      cB wceq vx cv cF cfv cB cF cfv wph vy cio wps vy cio vx cv cB cF fveq2 vx
      cv cB wceq wph wps vy opabiota.2 iotabidv eqeq12d vx cv cF cdm wcel vx cv
      vy cv cF wbr vy wex vx cv cF cfv wph vy cio wceq vy vx cv cF vx vex eldm
      vx cv vy cv cF wbr vx cv cF cfv wph vy cio wceq vy vy vx cv cF cfv wph vy
      cio vy vx cv cF vy cF wph vy cab vy cv csn wceq vx vy copab opabiota.1
      wph vy cab vy cv csn wceq vx vy nfopab2 nfcxfr vy vx cv nfcv nffv wph vy
      nfiota1 nfeq vx cv vy cv cF wbr vx cv cF cfv vy cv wph vy cio cF wfun vx
      cv vy cv cF wbr vx cv cF cfv vy cv wceq wi wph vx vy cF opabiota.1
      opabiotafun vx cv vy cv cF funbrfv ax-mp vx cv vy cv cF wbr wph wph vy
      cio vy cv wceq vx cv vy cv cF wbr wph vy cab vy cv csn wceq wph vx cv vy
      cv cF wbr vx cv vy cv cop cF wcel vx cv vy cv cop wph vy cab vy cv csn
      wceq vx vy copab wcel wph vy cab vy cv csn wceq vx cv vy cv cF df-br cF
      wph vy cab vy cv csn wceq vx vy copab vx cv vy cv cop opabiota.1 eleq2i
      wph vy cab vy cv csn wceq vx vy opabid 3bitri wph vy cab vy cv csn wceq
      vy cv wph vy cab wcel wph wph vy cab vy cv csn wceq vy cv vy cv csn wph
      vy cab vy cv vy vex snid wph vy cab vy cv csn wceq id syl5eleqr wph vy
      abid sylib sylbi vx cv vy cv cF wbr wph vy weu wph wph vy cio vy cv wceq
      wb vx cv vy cv cF wbr vx cv cF cdm wcel wph vy weu vx cv vy cv cF vx vex
      vy vex breldm wph vy weu vx cF cdm wph vx vy cF opabiota.1 opabiotadm
      abeq2i sylib wph vy iota1 syl mpbid eqtr4d exlimi sylbi vtoclga $.
  $}



