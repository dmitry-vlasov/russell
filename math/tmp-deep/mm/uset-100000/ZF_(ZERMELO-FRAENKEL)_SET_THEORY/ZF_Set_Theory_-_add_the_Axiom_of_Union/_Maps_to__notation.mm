
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Operations.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        "Maps to" notation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d A x y z $.  $d B x y z $.  $d C z $.
    elmpt2cl.f $e |- F = ( x e. A , y e. B |-> C ) $.
    $( If a two-parameter class is not empty, constrain the implicit pair.
       (Contributed by Stefan O'Rear, 7-Mar-2015.) $)
    elmpt2cl $p |- ( X e. ( S F T ) -> ( S e. A /\ T e. B ) ) $=
      cX cS cT cF co wcel cS cT cop cA cB cxp wcel cS cA wcel cT cB wcel wa cX
      cS cT cF co wcel cF cdm cA cB cxp cS cT cop cF cdm vx cv cA wcel vy cv cB
      wcel wa vz cv cC wceq wa vx vy vz coprab cdm cA cB cxp cF vx cv cA wcel
      vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab cF vx vy cA cB cC cmpt2
      vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab
      elmpt2cl.f vx vy vz cA cB cC df-mpt2 eqtri dmeqi vz cv cC wceq vx vy vz
      cA cB dmoprabss eqsstri cS cT cop cF cdm wcel cX cS cT cop cF cfv cS cT
      cF co cX cS cT cop cF elfvdm cS cT cF df-ov eleq2s sseldi cS cT cA cB
      opelxp sylib $.

    $( If a two-parameter class is not empty, the first argument is in its
       nominal domain.  (Contributed by FL, 15-Oct-2012.)  (Revised by Stefan
       O'Rear, 7-Mar-2015.) $)
    elmpt2cl1 $p |- ( X e. ( S F T ) -> S e. A ) $=
      cX cS cT cF co wcel cS cA wcel cT cB wcel vx vy cA cB cC cS cT cF cX
      elmpt2cl.f elmpt2cl simpld $.

    $( If a two-parameter class is not empty, the second argument is in its
       nominal domain.  (Contributed by FL, 15-Oct-2012.)  (Revised by Stefan
       O'Rear, 7-Mar-2015.) $)
    elmpt2cl2 $p |- ( X e. ( S F T ) -> T e. B ) $=
      cX cS cT cF co wcel cS cA wcel cT cB wcel vx vy cA cB cC cS cT cF cX
      elmpt2cl.f elmpt2cl simprd $.
  $}

  ${
    $d A a b $.  $d B a b $.  $d E a b $.  $d F a b $.  $d X a b $.
    $d Y a b $.  $d V a b $.
    elovmpt2.d $e |- D = ( a e. A , b e. B |-> C ) $.
    elovmpt2.c $e |- C e. _V $.
    elovmpt2.e $e |- ( ( a = X /\ b = Y ) -> C = E ) $.
    $( Utility lemma for two-parameter classes.

       _EDITORIAL_: can simplify ~ isghm , ~ islmhm .  (Contributed by Stefan
       O'Rear, 21-Jan-2015.) $)
    elovmpt2 $p |- ( F e. ( X D Y ) <-> ( X e. A /\ Y e. B /\ F e. E ) ) $=
      cF cX cY cD co wcel cX cA wcel cY cB wcel wa cF cE wcel wa cX cA wcel cY
      cB wcel cF cE wcel w3a cF cX cY cD co wcel cX cA wcel cY cB wcel wa cF cE
      wcel va vb cA cB cC cX cY cD cF elovmpt2.d elmpt2cl cX cA wcel cY cB wcel
      wa cX cY cD co cE cF cX cA wcel cY cB wcel cE cvv wcel cX cY cD co cE
      wceq cX cA wcel cY cB wcel wa cC cvv wcel vb wal va wal cE cvv wcel cC
      cvv wcel va vb elovmpt2.c gen2 cC cvv wcel cE cvv wcel va vb cX cY cA cB
      va cv cX wceq vb cv cY wceq wa cC cE cvv elovmpt2.e eleq1d spc2gv mpi va
      vb cX cY cA cB cC cE cD cvv elovmpt2.e elovmpt2.d ovmpt2ga mpd3an3 eleq2d
      biadan2 cX cA wcel cY cB wcel cF cE wcel df-3an bitr4i $.
  $}

  ${
    $d x w A $.  $d w B $.  $d w F $.
    relmptopab.1 $e |- F = ( x e. A |-> { <. y , z >. | ph } ) $.
    $( Any function to sets of ordered pairs produces a relation on function
       value unconditionally.  (Contributed by Mario Carneiro, 7-Aug-2014.)
       (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)
    relmptopab $p |- Rel ( F ` B ) $=
      cB cF cfv wrel cB cF cfv cvv cvv cxp wss wph vy vz copab cvv cvv cxp wss
      cB cF cfv cvv cvv cxp wss vx cA vx cA wph vy vz copab cvv cvv cxp cB cF
      relmptopab.1 fvmptss wph vy vz copab cvv cvv cxp wss vx cv cA wcel wph vy
      vz copab wrel wph vy vz copab cvv cvv cxp wss wph vy vz relopab wph vy vz
      copab df-rel mpbi a1i mprg cB cF cfv df-rel mpbir $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x D $.  $d x y ph $.
    f1od.1 $e |- F = ( x e. A |-> C ) $.
    ${
      f1od.2 $e |- ( ( ph /\ x e. A ) -> C e. W ) $.
      f1od.3 $e |- ( ( ph /\ y e. B ) -> D e. X ) $.
      f1od.4 $e |- ( ph -> ( ( x e. A /\ y = C ) <-> ( y e. B /\ x = D ) ) ) $.
      $( Describe an implicit one-to-one onto function.  (Contributed by Mario
         Carneiro, 30-Apr-2015.) $)
      f1ocnvd $p |- ( ph ->
        ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $=
        wph cA cB cF wf1o cF ccnv vy cB cD cmpt wceq wph cF cA wfn cF ccnv cB
        wfn cA cB cF wf1o wph cC cW wcel vx cA wral cF cA wfn wph cC cW wcel vx
        cA f1od.2 ralrimiva vx cA cC cF cW f1od.1 fnmpt syl wph cF ccnv cB wfn
        vy cB cD cmpt cB wfn wph cD cX wcel vy cB wral vy cB cD cmpt cB wfn wph
        cD cX wcel vy cB f1od.3 ralrimiva vy cB cD vy cB cD cmpt cX vy cB cD
        cmpt eqid fnmpt syl wph cB cF ccnv vy cB cD cmpt wph vx cv cA wcel vy
        cv cC wceq wa vy vx copab vy cv cB wcel vx cv cD wceq wa vy vx copab cF
        ccnv vy cB cD cmpt wph vx cv cA wcel vy cv cC wceq wa vy cv cB wcel vx
        cv cD wceq wa vy vx f1od.4 opabbidv cF ccnv vx cv cA wcel vy cv cC wceq
        wa vx vy copab ccnv vx cv cA wcel vy cv cC wceq wa vy vx copab cF vx cv
        cA wcel vy cv cC wceq wa vx vy copab cF vx cA cC cmpt vx cv cA wcel vy
        cv cC wceq wa vx vy copab f1od.1 vx vy cA cC df-mpt eqtri cnveqi vx cv
        cA wcel vy cv cC wceq wa vx vy cnvopab eqtri vy vx cB cD df-mpt 3eqtr4g
        fneq1d mpbird cA cB cF dff1o4 sylanbrc wph vx cv cA wcel vy cv cC wceq
        wa vy vx copab vy cv cB wcel vx cv cD wceq wa vy vx copab cF ccnv vy cB
        cD cmpt wph vx cv cA wcel vy cv cC wceq wa vy cv cB wcel vx cv cD wceq
        wa vy vx f1od.4 opabbidv cF ccnv vx cv cA wcel vy cv cC wceq wa vx vy
        copab ccnv vx cv cA wcel vy cv cC wceq wa vy vx copab cF vx cv cA wcel
        vy cv cC wceq wa vx vy copab cF vx cA cC cmpt vx cv cA wcel vy cv cC
        wceq wa vx vy copab f1od.1 vx vy cA cC df-mpt eqtri cnveqi vx cv cA
        wcel vy cv cC wceq wa vx vy cnvopab eqtri vy vx cB cD df-mpt 3eqtr4g
        jca $.

      $( Describe an implicit one-to-one onto function.  (Contributed by Mario
         Carneiro, 12-May-2014.) $)
      f1od $p |- ( ph -> F : A -1-1-onto-> B ) $=
        wph cA cB cF wf1o cF ccnv vy cB cD cmpt wceq wph vx vy cA cB cC cD cF
        cW cX f1od.1 f1od.2 f1od.3 f1od.4 f1ocnvd simpld $.
    $}

    f1o2d.2 $e |- ( ( ph /\ x e. A ) -> C e. B ) $.
    f1o2d.3 $e |- ( ( ph /\ y e. B ) -> D e. A ) $.
    f1o2d.4 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) ->
                    ( x = D <-> y = C ) ) $.
    $( Describe an implicit one-to-one onto function.  (Contributed by Mario
       Carneiro, 30-Apr-2015.) $)
    f1ocnv2d $p |- ( ph ->
      ( F : A -1-1-onto-> B /\ `' F = ( y e. B |-> D ) ) ) $=
      wph vx vy cA cB cC cD cF cB cA f1od.1 f1o2d.2 f1o2d.3 wph vx cv cA wcel
      vy cv cC wceq wa vy cv cB wcel vx cv cD wceq wa wph vx cv cA wcel vy cv
      cC wceq wa wa vy cv cB wcel vx cv cD wceq wph vx cv cA wcel vy cv cC wceq
      vy cv cB wcel wph vx cv cA wcel wa cC cB wcel vy cv cC wceq vy cv cB wcel
      wi f1o2d.2 cC cB vy cv eleq1a syl impr wph vx cv cA wcel vy cv cC wceq vy
      cv cB wcel vx cv cD wceq wi wph vx cv cA wcel vy cv cB wcel vy cv cC wceq
      vx cv cD wceq wph vx cv cA wcel vy cv cB wcel vy cv cC wceq vx cv cD wceq
      wph vx cv cA wcel vy cv cB wcel wa wa vx cv cD wceq vy cv cC wceq f1o2d.4
      biimpar exp42 com34 imp32 jcai wph vy cv cB wcel vx cv cD wceq wa wa vx
      cv cA wcel vy cv cC wceq wph vy cv cB wcel vx cv cD wceq vx cv cA wcel
      wph vy cv cB wcel wa cD cA wcel vx cv cD wceq vx cv cA wcel wi f1o2d.3 cD
      cA vx cv eleq1a syl impr wph vy cv cB wcel vx cv cD wceq vx cv cA wcel vy
      cv cC wceq wi wph vy cv cB wcel vx cv cA wcel vx cv cD wceq vy cv cC wceq
      wph vx cv cA wcel vy cv cB wcel vx cv cD wceq vy cv cC wceq wi wph vx cv
      cA wcel vy cv cB wcel vx cv cD wceq vy cv cC wceq wph vx cv cA wcel vy cv
      cB wcel wa wa vx cv cD wceq vy cv cC wceq f1o2d.4 biimpa exp42 com23
      com34 imp32 jcai impbida f1ocnvd $.

    $( Describe an implicit one-to-one onto function.  (Contributed by Mario
       Carneiro, 12-May-2014.) $)
    f1o2d $p |- ( ph -> F : A -1-1-onto-> B ) $=
      wph cA cB cF wf1o cF ccnv vy cB cD cmpt wceq wph vx vy cA cB cC cD cF
      f1od.1 f1o2d.2 f1o2d.3 f1o2d.4 f1ocnv2d simpld $.
  $}

  ${
    $d A w x y z $.  $d B w x y z $.  $d V w y z $.
    $( The cross product of two sets is a set.  Proposition 6.2 of
       [TakeutiZaring] p. 23.  This version is proven using Replacement; see
       ~ xpexg for a version that uses the Power Set axiom instead.
       (Contributed by Mario Carneiro, 20-May-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    xpexgALT $p |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V ) $=
      cA cV wcel cB cW wcel wa cA cB cxp vy cB cA vy cv csn cxp ciun cvv cA vy
      cB vy cv csn ciun cxp cA cB cxp vy cB cA vy cv csn cxp ciun vy cB vy cv
      csn ciun cB cA vy cB iunid xpeq2i vy cB vy cv csn cA xpiundi eqtr3i cB cW
      wcel cB cW wcel cA vy cv csn cxp cvv wcel vy cB wral vy cB cA vy cv csn
      cxp ciun cvv wcel cA cV wcel cB cW wcel id cA cV wcel cA vy cv csn cxp
      cvv wcel vy cB cA cV wcel cA vy cv csn cxp vx cA vy cv cmpt cvv vx cA vy
      cv fconstmpt vx cA vy cv cV mptexg syl5eqel ralrimivw vy cB cA vy cv csn
      cxp cW cvv iunexg syl2anr syl5eqel $.
  $}

  ${
    $d a b A $.  $d a b B $.  $d a b F $.  $d a b ph $.
    f1opw2.1 $e |- ( ph -> F : A -1-1-onto-> B ) $.
    f1opw2.2 $e |- ( ph -> ( `' F " a ) e. _V ) $.
    f1opw2.3 $e |- ( ph -> ( F " b ) e. _V ) $.
    $( A one-to-one mapping induces a one-to-one mapping on power sets.  This
       version of ~ f1opw avoids the Axiom of Replacement.  (Contributed by
       Mario Carneiro, 26-Jun-2015.) $)
    f1opw2 $p |- ( ph ->
        ( b e. ~P A |-> ( F " b ) ) : ~P A -1-1-onto-> ~P B ) $=
      wph vb va cA cpw cB cpw cF vb cv cima cF ccnv va cv cima vb cA cpw cF vb
      cv cima cmpt vb cA cpw cF vb cv cima cmpt eqid wph cF vb cv cima cB cpw
      wcel vb cv cA cpw wcel wph cF vb cv cima cB cpw wcel cF vb cv cima cB wss
      wph cF crn cF vb cv cima cB cF vb cv imassrn wph cA cB cF wfo cF crn cB
      wceq wph cA cB cF wf1o cA cB cF wfo f1opw2.1 cA cB cF f1ofo syl cA cB cF
      forn syl syl5sseq wph cF vb cv cima cvv wcel cF vb cv cima cB cpw wcel cF
      vb cv cima cB wss wb f1opw2.3 cF vb cv cima cB cvv elpwg syl mpbird
      adantr wph cF ccnv va cv cima cA cpw wcel va cv cB cpw wcel wph cF ccnv
      va cv cima cA cpw wcel cF ccnv va cv cima cA wss wph cF ccnv crn cF ccnv
      va cv cima cA cF ccnv va cv imassrn wph cF ccnv crn cF cdm cA cF dfdm4
      wph cA cB cF wf1o cF cdm cA wceq f1opw2.1 cA cB cF f1odm syl syl5eqr
      syl5sseq wph cF ccnv va cv cima cvv wcel cF ccnv va cv cima cA cpw wcel
      cF ccnv va cv cima cA wss wb f1opw2.2 cF ccnv va cv cima cA cvv elpwg syl
      mpbird adantr wph vb cv cA cpw wcel va cv cB cpw wcel wa wa vb cv cF ccnv
      va cv cima wceq va cv cF vb cv cima wceq wph vb cv cA cpw wcel va cv cB
      cpw wcel wa wa va cv cF vb cv cima wceq vb cv cF ccnv va cv cima wceq va
      cv cF cF ccnv va cv cima cima wceq wph vb cv cA cpw wcel va cv cB cpw
      wcel wa wa cF cF ccnv va cv cima cima va cv wph cA cB cF wfo va cv cB wss
      cF cF ccnv va cv cima cima va cv wceq vb cv cA cpw wcel va cv cB cpw wcel
      wa wph cA cB cF wf1o cA cB cF wfo f1opw2.1 cA cB cF f1ofo syl va cv cB
      cpw wcel va cv cB wss vb cv cA cpw wcel va cv cB elpwi adantl cA cB va cv
      cF foimacnv syl2an eqcomd vb cv cF ccnv va cv cima wceq cF vb cv cima cF
      cF ccnv va cv cima cima va cv vb cv cF ccnv va cv cima cF imaeq2 eqeq2d
      syl5ibrcom wph vb cv cA cpw wcel va cv cB cpw wcel wa wa vb cv cF ccnv va
      cv cima wceq va cv cF vb cv cima wceq vb cv cF ccnv cF vb cv cima cima
      wceq wph vb cv cA cpw wcel va cv cB cpw wcel wa wa cF ccnv cF vb cv cima
      cima vb cv wph cA cB cF wf1 vb cv cA wss cF ccnv cF vb cv cima cima vb cv
      wceq vb cv cA cpw wcel va cv cB cpw wcel wa wph cA cB cF wf1o cA cB cF
      wf1 f1opw2.1 cA cB cF f1of1 syl vb cv cA cpw wcel vb cv cA wss va cv cB
      cpw wcel vb cv cA elpwi adantr cA cB vb cv cF f1imacnv syl2an eqcomd va
      cv cF vb cv cima wceq cF ccnv va cv cima cF ccnv cF vb cv cima cima vb cv
      va cv cF vb cv cima cF ccnv imaeq2 eqeq2d syl5ibrcom impbid f1o2d $.
  $}

  ${
    $d a b A $.  $d a b B $.  $d a b F $.
    $( A one-to-one mapping induces a one-to-one mapping on power sets.
       (Contributed by Stefan O'Rear, 18-Nov-2014.)  (Revised by Mario
       Carneiro, 26-Jun-2015.) $)
    f1opw $p |- ( F : A -1-1-onto-> B -> ( b e. ~P A |-> ( F " b ) ) :
          ~P A -1-1-onto-> ~P B ) $=
      cA cB cF wf1o cA cB cF va vb cA cB cF wf1o id cA cB cF wf1o cF ccnv wfun
      cF ccnv va cv cima cvv wcel cA cB cF wf1o cA cB cF wfo cF ccnv wfun cA cB
      cF dff1o3 simprbi cF ccnv va cv va vex funimaex syl cA cB cF wf1o cF wfun
      cF vb cv cima cvv wcel cA cB cF f1ofun cF vb cv vb vex funimaex syl
      f1opw2 $.
  $}

  ${
    $d k x y A $.  $d x y B $.  $d k x ph $.  $d k x y W $.  $d k x y Z $.
    suppss2.n $e |- ( ( ph /\ k e. ( A \ W ) ) -> B = Z ) $.
    $( Show that the support of a function is contained in a set.  (Contributed
       by Mario Carneiro, 19-Dec-2014.)  (Revised by Mario Carneiro,
       22-Mar-2015.) $)
    suppss2 $p |- ( ph -> ( `' ( k e. A |-> B ) " ( _V \ { Z } ) ) C_ W ) $=
      wph vk cA cB cmpt ccnv cvv cZ csn cdif cima cB cvv cZ csn cdif wcel vk cA
      crab cW vk cA cB cvv cZ csn cdif vk cA cB cmpt vk cA cB cmpt eqid
      mptpreima wph cB cvv cZ csn cdif wcel vk cA cW wph vk cv cA wcel cB cvv
      cZ csn cdif wcel vk cv cW wcel cB cvv cZ csn cdif wcel cB cZ wne wph vk
      cv cA wcel wa vk cv cW wcel cB cvv cZ eldifsni wph vk cv cA wcel wa vk cv
      cW wcel cB cZ wph vk cv cA wcel vk cv cW wcel wn cB cZ wceq vk cv cA wcel
      vk cv cW wcel wn wa wph vk cv cA cW cdif wcel cB cZ wceq vk cv cA cW
      eldif suppss2.n sylan2br expr necon1ad syl5 3impia rabssdv syl5eqss $.
  $}

  ${
    $d ph x $.  $d Y x $.  $d Z x $.
    suppssfv.a $e |- ( ph -> ( `' ( x e. D |-> A ) " ( _V \ { Y } ) ) C_ L ) $.
    suppssfv.f $e |- ( ph -> ( F ` Y ) = Z ) $.
    suppssfv.v $e |- ( ( ph /\ x e. D ) -> A e. V ) $.
    $( Formula building theorem for support restriction, on a function which
       preserves zero.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
    suppssfv $p |- ( ph -> ( `' ( x e. D |-> ( F ` A ) ) "
            ( _V \ { Z } ) ) C_ L ) $=
      wph vx cD cA cF cfv cmpt ccnv cvv cZ csn cdif cima vx cD cA cmpt ccnv cvv
      cY csn cdif cima cL wph cA cF cfv cvv cZ csn cdif wcel vx cD crab cA cvv
      cY csn cdif wcel vx cD crab vx cD cA cF cfv cmpt ccnv cvv cZ csn cdif
      cima vx cD cA cmpt ccnv cvv cY csn cdif cima wph cA cF cfv cvv cZ csn
      cdif wcel cA cvv cY csn cdif wcel vx cD cA cF cfv cvv cZ csn cdif wcel cA
      cF cfv cZ wne wph vx cv cD wcel wa cA cvv cY csn cdif wcel cA cF cfv cvv
      cZ eldifsni wph vx cv cD wcel wa cA cF cfv cZ wne cA cvv cY csn cdif wcel
      wph vx cv cD wcel wa cA cF cfv cZ wne wa cA cvv wcel cA cY wne cA cvv cY
      csn cdif wcel wph vx cv cD wcel wa cA cvv wcel cA cF cfv cZ wne wph vx cv
      cD wcel wa cA cV wcel cA cvv wcel suppssfv.v cA cV elex syl adantr wph vx
      cv cD wcel wa cA cF cfv cZ wne cA cY wne wph cA cF cfv cZ wne cA cY wne
      wi vx cv cD wcel wph cA cY cA cF cfv cZ wph cA cF cfv cZ wceq cA cY wceq
      cY cF cfv cZ wceq suppssfv.f cA cY wceq cA cF cfv cY cF cfv cZ cA cY cF
      fveq2 eqeq1d syl5ibrcom necon3d adantr imp cA cvv cY eldifsn sylanbrc ex
      syl5 ss2rabdv vx cD cA cF cfv cvv cZ csn cdif vx cD cA cF cfv cmpt vx cD
      cA cF cfv cmpt eqid mptpreima vx cD cA cvv cY csn cdif vx cD cA cmpt vx
      cD cA cmpt eqid mptpreima 3sstr4g suppssfv.a sstrd $.
  $}

  ${
    $d ph v $.  $d ph x $.  $d B v $.  $d O v $.  $d R v $.  $d Y v $.
    $d Y x $.  $d Z v $.  $d Z x $.
    suppssov1.s $e |- ( ph ->
        ( `' ( x e. D |-> A ) " ( _V \ { Y } ) ) C_ L ) $.
    suppssov1.o $e |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z ) $.
    suppssov1.a $e |- ( ( ph /\ x e. D ) -> A e. V ) $.
    suppssov1.b $e |- ( ( ph /\ x e. D ) -> B e. R ) $.
    $( Formula building theorem for support restrictions: operator with left
       annihilator.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
    suppssov1 $p |- ( ph -> ( `' ( x e. D |-> ( A O B ) ) "
            ( _V \ { Z } ) ) C_ L ) $=
      wph vx cD cA cB cO co cmpt ccnv cvv cZ csn cdif cima vx cD cA cmpt ccnv
      cvv cY csn cdif cima cL wph cA cB cO co cvv cZ csn cdif wcel vx cD crab
      cA cvv cY csn cdif wcel vx cD crab vx cD cA cB cO co cmpt ccnv cvv cZ csn
      cdif cima vx cD cA cmpt ccnv cvv cY csn cdif cima wph cA cB cO co cvv cZ
      csn cdif wcel cA cvv cY csn cdif wcel vx cD wph vx cv cD wcel wa cA cB cO
      co cvv cZ csn cdif wcel cA cvv cY csn cdif wcel wph vx cv cD wcel wa cA
      cB cO co cvv cZ csn cdif wcel wa cA cvv wcel cA cY wne cA cvv cY csn cdif
      wcel wph vx cv cD wcel wa cA cvv wcel cA cB cO co cvv cZ csn cdif wcel
      wph vx cv cD wcel wa cA cV wcel cA cvv wcel suppssov1.a cA cV elex syl
      adantr wph vx cv cD wcel wa cA cB cO co cvv cZ csn cdif wcel cA cY wne cA
      cB cO co cvv cZ csn cdif wcel cA cB cO co cZ wne wph vx cv cD wcel wa cA
      cY wne cA cB cO co cvv cZ eldifsni wph vx cv cD wcel wa cA cY cA cB cO co
      cZ wph vx cv cD wcel wa cA cB cO co cZ wceq cA cY wceq cY cB cO co cZ
      wceq wph vx cv cD wcel wa cB cR wcel cY vv cv cO co cZ wceq vv cR wral cY
      cB cO co cZ wceq suppssov1.b wph cY vv cv cO co cZ wceq vv cR wral vx cv
      cD wcel wph cY vv cv cO co cZ wceq vv cR suppssov1.o ralrimiva adantr cY
      vv cv cO co cZ wceq cY cB cO co cZ wceq vv cB cR vv cv cB wceq cY vv cv
      cO co cY cB cO co cZ vv cv cB cY cO oveq2 eqeq1d rspcva syl2anc cA cY
      wceq cA cB cO co cY cB cO co cZ cA cY cB cO oveq1 eqeq1d syl5ibrcom
      necon3d syl5 imp cA cvv cY eldifsn sylanbrc ex ss2rabdv vx cD cA cB cO co
      cvv cZ csn cdif vx cD cA cB cO co cmpt vx cD cA cB cO co cmpt eqid
      mptpreima vx cD cA cvv cY csn cdif vx cD cA cmpt vx cD cA cmpt eqid
      mptpreima 3sstr4g suppssov1.s sstrd $.
  $}


