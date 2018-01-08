
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/First_and_second_members_of_an_ordered_pair.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Function transposition

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c tpos $. $( Function transposition $)

  $( The transposition of a function. $)
  ctpos $a class tpos F $.

  ${
    $d F x $.
    $( Define the transposition of a function, which is a function
       ` G = tpos F ` satisfying ` G ( x , y ) = F ( y , x ) ` .  (Contributed
       by Mario Carneiro, 10-Sep-2015.) $)
    df-tpos $a |- tpos F = ( F o.
        ( x e. ( `' dom F u. { (/) } ) |-> U. `' { x } ) ) $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d w x y z F $.  $d x G $.
    $( Subset theorem for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    tposss $p |- ( F C_ G -> tpos F C_ tpos G ) $=
      cF cG wss cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cG
      vx cG cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cF ctpos cG ctpos
      cF cG wss cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cG
      vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cG vx cG cdm ccnv
      c0 csn cun vx cv csn ccnv cuni cmpt ccom cF cG vx cF cdm ccnv c0 csn cun
      vx cv csn ccnv cuni cmpt coss1 cF cG wss vx cF cdm ccnv c0 csn cun vx cv
      csn ccnv cuni cmpt vx cG cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wss
      cG vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cG vx cG cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom wss cF cG wss vx cG cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt cF cdm ccnv c0 csn cun cres vx
      cG cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wss vx cF cdm ccnv c0 csn
      cun vx cv csn ccnv cuni cmpt vx cG cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt wss vx cG cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cF cdm
      ccnv c0 csn cun resss cF cG wss vx cG cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt cF cdm ccnv c0 csn cun cres vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni cmpt vx cG cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cF cG
      wss cF cdm ccnv cG cdm ccnv wss cF cdm ccnv c0 csn cun cG cdm ccnv c0 csn
      cun wss vx cG cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cF cdm ccnv c0
      csn cun cres vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wceq cF
      cG wss cF cdm cG cdm wss cF cdm ccnv cG cdm ccnv wss cF cG dmss cF cdm cG
      cdm cnvss syl cF cdm ccnv cG cdm ccnv c0 csn unss1 vx cG cdm ccnv c0 csn
      cun cF cdm ccnv c0 csn cun vx cv csn ccnv cuni resmpt 3syl sseq1d mpbii
      vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt vx cG cdm ccnv c0 csn
      cun vx cv csn ccnv cuni cmpt cG coss2 syl sstrd vx cF df-tpos vx cG
      df-tpos 3sstr4g $.

    $( Equality theorem for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    tposeq $p |- ( F = G -> tpos F = tpos G ) $=
      cF cG wceq cF ctpos cG ctpos cF cG wceq cF cG wss cF ctpos cG ctpos wss
      cF cG eqimss cF cG tposss syl cF cG wceq cG cF wss cG ctpos cF ctpos wss
      cG cF eqimss2 cG cF tposss syl eqssd $.

    ${
      tposeqd.1 $e |- ( ph -> F = G ) $.
      $( Equality theorem for transposition.  (Contributed by Mario Carneiro,
         7-Jan-2017.) $)
      tposeqd $p |- ( ph -> tpos F = tpos G ) $=
        wph cF cG wceq cF ctpos cG ctpos wceq tposeqd.1 cF cG tposeq syl $.
    $}

    $( The transposition is a subset of a cross product.  (Contributed by Mario
       Carneiro, 12-Jan-2017.) $)
    tposssxp $p |- tpos F C_ ( ( `' dom F u. { (/) } ) X. ran F ) $=
      cF ctpos vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cdm cF crn
      cxp cF cdm ccnv c0 csn cun cF crn cxp cF ctpos cF vx cF cdm ccnv c0 csn
      cun vx cv csn ccnv cuni cmpt ccom vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni cmpt cdm cF crn cxp vx cF df-tpos cF vx cF cdm ccnv c0 csn cun
      vx cv csn ccnv cuni cmpt cossxp eqsstri vx cF cdm ccnv c0 csn cun vx cv
      csn ccnv cuni cmpt cdm cF cdm ccnv c0 csn cun wss vx cF cdm ccnv c0 csn
      cun vx cv csn ccnv cuni cmpt cdm cF crn cxp cF cdm ccnv c0 csn cun cF crn
      cxp wss vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni vx cF cdm ccnv c0
      csn cun vx cv csn ccnv cuni cmpt vx cF cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt eqid dmmptss vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt
      cdm cF cdm ccnv c0 csn cun cF crn xpss1 ax-mp sstri $.

    $( The transposition is a relation.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    reltpos $p |- Rel tpos F $=
      cF ctpos cF cdm ccnv c0 csn cun cF crn cxp wss cF cdm ccnv c0 csn cun cF
      crn cxp wrel cF ctpos wrel cF tposssxp cF cdm ccnv c0 csn cun cF crn
      relxp cF ctpos cF cdm ccnv c0 csn cun cF crn cxp relss mp2 $.

    $( Value of the transposition at a pair ` <. A , B >. ` .  (Contributed by
       Mario Carneiro, 10-Sep-2015.) $)
    brtpos2 $p |- ( B e. V -> ( A tpos F B <->
      ( A e. ( `' dom F u. { (/) } ) /\ U. `' { A } F B ) ) ) $=
      cB cV wcel cA cvv wcel cA cB cF ctpos wbr cA cF cdm ccnv c0 csn cun wcel
      cA csn ccnv cuni cB cF wbr wa cA cB cF ctpos wbr cA cvv wcel wi cB cV
      wcel cA cB cF ctpos cF reltpos brrelexi a1i cA cF cdm ccnv c0 csn cun
      wcel cA csn ccnv cuni cB cF wbr wa cA cvv wcel wi cB cV wcel cA cF cdm
      ccnv c0 csn cun wcel cA cvv wcel cA csn ccnv cuni cB cF wbr cA cF cdm
      ccnv c0 csn cun elex adantr a1i cA cvv wcel cB cV wcel cA cB cF ctpos wbr
      cA cF cdm ccnv c0 csn cun wcel cA csn ccnv cuni cB cF wbr wa wb cA cvv
      wcel cB cV wcel wa cA cB cF ctpos wbr cA vy cv vx cF cdm ccnv c0 csn cun
      vx cv csn ccnv cuni cmpt wbr vy cv cB cF wbr wa vy wex cA cF cdm ccnv c0
      csn cun wcel cA csn ccnv cuni cB cF wbr wa cA cB cF ctpos wbr cA cB cF vx
      cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom wbr cA cvv wcel cB
      cV wcel wa cA vy cv vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt
      wbr vy cv cB cF wbr wa vy wex cA cB cF ctpos cF vx cF cdm ccnv c0 csn cun
      vx cv csn ccnv cuni cmpt ccom vx cF df-tpos breqi vy cA cB cF vx cF cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt cvv cV brcog syl5bb cA vy cv vx
      cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wbr vy cv cB cF wbr wa vy
      wex vy cv cA csn ccnv cuni wceq cA cF cdm ccnv c0 csn cun wcel vy cv cB
      cF wbr wa wa vy wex cA cF cdm ccnv c0 csn cun wcel cA csn ccnv cuni cB cF
      wbr wa cA vy cv vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wbr vy
      cv cB cF wbr wa vy cv cA csn ccnv cuni wceq cA cF cdm ccnv c0 csn cun
      wcel vy cv cB cF wbr wa wa vy cA vy cv vx cF cdm ccnv c0 csn cun vx cv
      csn ccnv cuni cmpt wbr vy cv cB cF wbr wa vy cv cA csn ccnv cuni wceq cA
      cF cdm ccnv c0 csn cun wcel wa vy cv cB cF wbr wa vy cv cA csn ccnv cuni
      wceq cA cF cdm ccnv c0 csn cun wcel vy cv cB cF wbr wa wa cA vy cv vx cF
      cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wbr vy cv cA csn ccnv cuni
      wceq cA cF cdm ccnv c0 csn cun wcel wa vy cv cB cF wbr cA vy cv vx cF cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt wbr cA cF cdm ccnv c0 csn cun
      wcel vy cv cA csn ccnv cuni wceq wa vy cv cA csn ccnv cuni wceq cA cF cdm
      ccnv c0 csn cun wcel wa cA vy cv vx cF cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt wbr cA vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cdm
      wcel cA vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cfv vy cv wceq
      wa cA cF cdm ccnv c0 csn cun wcel vy cv cA csn ccnv cuni wceq wa vx cF
      cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt wfun cA vy cv vx cF cdm ccnv
      c0 csn cun vx cv csn ccnv cuni cmpt wbr cA vx cF cdm ccnv c0 csn cun vx
      cv csn ccnv cuni cmpt cdm wcel cA vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni cmpt cfv vy cv wceq wa wb vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni funmpt cA vy cv vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni
      cmpt funbrfv2b ax-mp cA vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni
      cmpt cdm wcel cA vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cfv
      vy cv wceq wa cA cF cdm ccnv c0 csn cun wcel vy cv cA vx cF cdm ccnv c0
      csn cun vx cv csn ccnv cuni cmpt cfv wceq wa cA cF cdm ccnv c0 csn cun
      wcel vy cv cA csn ccnv cuni wceq wa cA vx cF cdm ccnv c0 csn cun vx cv
      csn ccnv cuni cmpt cdm wcel cA cF cdm ccnv c0 csn cun wcel cA vx cF cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt cfv vy cv wceq vy cv cA vx cF
      cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cfv wceq vx cF cdm ccnv c0
      csn cun vx cv csn ccnv cuni cmpt cdm cF cdm ccnv c0 csn cun cA vx cF cdm
      ccnv c0 csn cun vx cv csn ccnv cuni vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni cmpt vx cv csn ccnv vx cv csn vx cv snex cnvex uniex vx cF cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt eqid dmmpti eleq2i cA vx cF cdm
      ccnv c0 csn cun vx cv csn ccnv cuni cmpt cfv vy cv eqcom anbi12i cA cF
      cdm ccnv c0 csn cun wcel vy cv cA vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni cmpt cfv wceq vy cv cA csn ccnv cuni wceq cA cF cdm ccnv c0 csn
      cun wcel cA vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cfv cA csn
      ccnv cuni vy cv vx cA vx cv csn ccnv cuni cA csn ccnv cuni cF cdm ccnv c0
      csn cun vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt vx cv cA wceq
      vx cv csn ccnv cA csn ccnv vx cv cA wceq vx cv csn cA csn vx cv cA sneq
      cnveqd unieqd vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt eqid cA
      csn ccnv cA csn cA snex cnvex uniex fvmpt eqeq2d pm5.32i bitri bitri cA
      cF cdm ccnv c0 csn cun wcel vy cv cA csn ccnv cuni wceq ancom bitri
      anbi1i vy cv cA csn ccnv cuni wceq cA cF cdm ccnv c0 csn cun wcel vy cv
      cB cF wbr anass bitri exbii cA cF cdm ccnv c0 csn cun wcel vy cv cB cF
      wbr wa cA cF cdm ccnv c0 csn cun wcel cA csn ccnv cuni cB cF wbr wa vy cA
      csn ccnv cuni cA csn ccnv cA csn cA snex cnvex uniex vy cv cA csn ccnv
      cuni wceq vy cv cB cF wbr cA csn ccnv cuni cB cF wbr cA cF cdm ccnv c0
      csn cun wcel vy cv cA csn ccnv cuni cB cF breq1 anbi2d ceqsexv bitri
      syl6bb expcom pm5.21ndd $.

    $( The behavior of ` tpos ` when the left argument is the empty set (which
       is not an ordered pair but is the "default" value of an ordered pair
       when the arguments are proper classes).  This allows us to eliminate
       sethood hypotheses on ` A , B ` in ~ brtpos .  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
    brtpos0 $p |- ( A e. V -> ( (/) tpos F A <-> (/) F A ) ) $=
      cA cV wcel c0 cA cF ctpos wbr c0 cF cdm ccnv c0 csn cun wcel c0 csn ccnv
      cuni cA cF wbr wa c0 cA cF wbr c0 cA cF cV brtpos2 c0 cF cdm ccnv c0 csn
      cun wcel c0 csn ccnv cuni cA cF wbr wa c0 csn ccnv cuni cA cF wbr c0 cA
      cF wbr c0 cF cdm ccnv c0 csn cun wcel c0 csn ccnv cuni cA cF wbr c0 csn
      cF cdm ccnv c0 csn cun c0 c0 csn cF cdm ccnv ssun2 c0 0ex snid sselii
      biantrur c0 csn ccnv cuni c0 cA cF c0 csn ccnv cuni c0 cuni c0 c0 csn
      ccnv c0 cnvsn0 unieqi uni0 eqtri breq1i bitr3i syl6bb $.

    $( Necessary and sufficient condition for ` dom tpos F ` to be a relation.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
    reldmtpos $p |- ( Rel dom tpos F <-> -. (/) e. dom F ) $=
      cF ctpos cdm wrel c0 cF cdm wcel wn c0 cF cdm wcel cF ctpos cdm wrel c0
      cF cdm wcel c0 vy cv cF wbr vy wex cF ctpos cdm wrel wn vy c0 cF 0ex eldm
      c0 vy cv cF wbr cF ctpos cdm wrel wn vy c0 vy cv cF wbr c0 vy cv cF ctpos
      wbr cF ctpos cdm wrel wn vy cv cvv wcel c0 vy cv cF ctpos wbr c0 vy cv cF
      wbr wb vy vex vy cv cF cvv brtpos0 ax-mp cF ctpos cdm wrel c0 cF ctpos
      cdm wcel c0 vy cv cF ctpos wbr cF ctpos cdm wrel c0 cF ctpos cdm wcel c0
      cvv cvv cxp wcel cvv cvv 0nelxp cF ctpos cdm wrel cF ctpos cdm cvv cvv
      cxp wss c0 cF ctpos cdm wcel c0 cvv cvv cxp wcel wi cF ctpos cdm df-rel
      cF ctpos cdm cvv cvv cxp c0 ssel sylbi mtoi c0 vy cv cF ctpos 0ex vy vex
      breldm nsyl3 sylbir exlimiv sylbi con2i c0 cF cdm wcel wn cF ctpos cdm
      cvv cvv cxp wss cF ctpos cdm wrel c0 cF cdm wcel wn vx cF ctpos cdm cvv
      cvv cxp vx cv cF ctpos cdm wcel vx cv vy cv cF ctpos wbr vy wex c0 cF cdm
      wcel wn vx cv cvv cvv cxp wcel vy vx cv cF ctpos vx vex eldm c0 cF cdm
      wcel wn vx cv vy cv cF ctpos wbr vx cv cvv cvv cxp wcel vy c0 cF cdm wcel
      wn vx cv vy cv cF ctpos wbr vx cv cvv cvv cxp wcel c0 cF cdm wcel wn vx
      cv vy cv cF ctpos wbr wa vx cv cF cdm ccnv wcel vx cv cvv cvv cxp wcel vx
      cv c0 csn wcel vx cv cF cdm ccnv wcel vx cv cvv cvv cxp wcel wi c0 cF cdm
      wcel wn vx cv vy cv cF ctpos wbr wa cF cdm ccnv cvv cvv cxp vx cv cF cdm
      ccnv wrel cF cdm ccnv cvv cvv cxp wss cF cdm relcnv cF cdm ccnv df-rel
      mpbi sseli a1i vx cv vy cv cF ctpos wbr c0 cF cdm wcel wn vx cv c0 csn
      wcel vx cv cvv cvv cxp wcel wi vx cv c0 csn wcel vx cv vy cv cF ctpos wbr
      c0 cF cdm wcel wn vx cv cvv cvv cxp wcel vx cv c0 csn wcel vx cv vy cv cF
      ctpos wbr c0 vy cv cF ctpos wbr c0 cF cdm wcel wn vx cv cvv cvv cxp wcel
      wi vx cv c0 csn wcel vx cv c0 vy cv cF ctpos vx cv c0 elsni breq1d c0 vy
      cv cF ctpos wbr c0 vy cv cF wbr c0 cF cdm wcel wn vx cv cvv cvv cxp wcel
      wi vy cv cvv wcel c0 vy cv cF ctpos wbr c0 vy cv cF wbr wb vy vex vy cv
      cF cvv brtpos0 ax-mp c0 vy cv cF wbr c0 cF cdm wcel vx cv cvv cvv cxp
      wcel c0 vy cv cF 0ex vy vex breldm pm2.24d sylbi syl6bi com3l impcom vx
      cv vy cv cF ctpos wbr vx cv cF cdm ccnv wcel vx cv c0 csn wcel wo c0 cF
      cdm wcel wn vx cv vy cv cF ctpos wbr vx cv cF cdm ccnv c0 csn cun wcel vx
      cv cF cdm ccnv wcel vx cv c0 csn wcel wo vx cv vy cv cF ctpos wbr vx cv
      cF cdm ccnv c0 csn cun wcel vx cv csn ccnv cuni vy cv cF wbr vy cv cvv
      wcel vx cv vy cv cF ctpos wbr vx cv cF cdm ccnv c0 csn cun wcel vx cv csn
      ccnv cuni vy cv cF wbr wa wb vy vex vx cv vy cv cF cvv brtpos2 ax-mp
      simplbi vx cv cF cdm ccnv c0 csn elun sylib adantl mpjaod ex exlimdv
      syl5bi ssrdv cF ctpos cdm df-rel sylibr impbii $.

    $( The transposition swaps arguments of a three-parameter relation.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
    brtpos $p |- ( C e. V -> ( <. A , B >. tpos F C <-> <. B , A >. F C ) ) $=
      cC cV wcel cA cvv wcel cB cvv wcel wa cA cB cop cC cF ctpos wbr cB cA cop
      cC cF wbr wb cC cV wcel cA cvv wcel cB cvv wcel wa cA cB cop cC cF ctpos
      wbr cB cA cop cC cF wbr wb cC cV wcel cA cvv wcel cB cvv wcel wa wa cA cB
      cop cC cF ctpos wbr cA cB cop cF cdm ccnv c0 csn cun wcel cA cB cop csn
      ccnv cuni cC cF wbr wa cB cA cop cC cF wbr cC cV wcel cA cB cop cC cF
      ctpos wbr cA cB cop cF cdm ccnv c0 csn cun wcel cA cB cop csn ccnv cuni
      cC cF wbr wa wb cA cvv wcel cB cvv wcel wa cA cB cop cC cF cV brtpos2
      adantr cC cV wcel cA cvv wcel cB cvv wcel wa wa cB cA cop cC cF wbr cA cB
      cop cF cdm ccnv c0 csn cun wcel cB cA cop cC cF wbr wa cA cB cop cF cdm
      ccnv c0 csn cun wcel cA cB cop csn ccnv cuni cC cF wbr wa cC cV wcel cA
      cvv wcel cB cvv wcel wa wa cB cA cop cC cF wbr cA cB cop cF cdm ccnv c0
      csn cun wcel cC cV wcel cA cvv wcel cB cvv wcel wa wa cB cA cop cC cF wbr
      cA cB cop cF cdm ccnv wcel cA cB cop cF cdm ccnv c0 csn cun wcel cC cV
      wcel cA cvv wcel cB cvv wcel wa wa cB cA cop cC cF wbr cB cA cop cF cdm
      wcel cA cB cop cF cdm ccnv wcel cC cV wcel cB cA cop cC cF wbr cB cA cop
      cF cdm wcel wi cA cvv wcel cB cvv wcel wa cB cA cop cvv wcel cC cV wcel
      cB cA cop cC cF wbr cB cA cop cF cdm wcel wi cB cA opex cB cA cop cvv
      wcel cC cV wcel cB cA cop cC cF wbr cB cA cop cF cdm wcel cB cA cop cC
      cvv cV cF breldmg 3expia mpan adantr cA cvv wcel cB cvv wcel wa cA cB cop
      cF cdm ccnv wcel cB cA cop cF cdm wcel wb cC cV wcel cA cB cvv cvv cF cdm
      opelcnvg adantl sylibrd cA cB cop cF cdm ccnv c0 csn elun1 syl6 pm4.71rd
      cA cB cop csn ccnv cuni cC cF wbr cB cA cop cC cF wbr cA cB cop cF cdm
      ccnv c0 csn cun wcel cA cB cop csn ccnv cuni cB cA cop cC cF cA cB opswap
      breq1i anbi2i syl6bbr bitr4d ex cC cV wcel cA cB cop cC cF ctpos wbr cB
      cA cop cC cF wbr wb cA cvv wcel cB cvv wcel wa wn c0 cC cF ctpos wbr c0
      cC cF wbr wb cC cF cV brtpos0 cA cvv wcel cB cvv wcel wa wn cA cB cop cC
      cF ctpos wbr c0 cC cF ctpos wbr cB cA cop cC cF wbr c0 cC cF wbr cA cvv
      wcel cB cvv wcel wa wn cA cB cop c0 cC cF ctpos cA cB opprc breq1d cA cvv
      wcel cB cvv wcel wa cB cvv wcel cA cvv wcel wa cB cA cop cC cF wbr c0 cC
      cF wbr wb cA cvv wcel cB cvv wcel ancom cB cvv wcel cA cvv wcel wa wn cB
      cA cop c0 cC cF cB cA opprc breq1d sylnbi bibi12d syl5ibrcom pm2.61d $.

    $( The transposition swaps the first two elements in a collection of
       ordered triples.  (Contributed by Mario Carneiro, 1-Dec-2014.) $)
    ottpos $p |- ( C e. V ->
      ( <. A , B , C >. e. tpos F <-> <. B , A , C >. e. F ) ) $=
      cC cV wcel cA cB cop cC cop cF ctpos wcel cB cA cop cC cop cF wcel cA cB
      cC cotp cF ctpos wcel cB cA cC cotp cF wcel cC cV wcel cA cB cop cC cF
      ctpos wbr cB cA cop cC cF wbr cA cB cop cC cop cF ctpos wcel cB cA cop cC
      cop cF wcel cA cB cC cF cV brtpos cA cB cop cC cF ctpos df-br cB cA cop
      cC cF df-br 3bitr3g cA cB cC cotp cA cB cop cC cop cF ctpos cA cB cC
      df-ot eleq1i cB cA cC cotp cB cA cop cC cop cF cB cA cC df-ot eleq1i
      3bitr4g $.

    $( The transposition swaps arguments of a three-parameter relation.
       (Contributed by Mario Carneiro, 3-Nov-2015.) $)
    relbrtpos $p |- ( Rel F ->
      ( <. A , B >. tpos F C <-> <. B , A >. F C ) ) $=
      cF wrel cA cB cop cC cF ctpos wbr cB cA cop cC cF wbr cC cvv wcel cF wrel
      cF ctpos wrel cA cB cop cC cF ctpos wbr cC cvv wcel cF ctpos wrel cF wrel
      cF reltpos a1i cA cB cop cC cF ctpos brrelex2 sylan cB cA cop cC cF
      brrelex2 cA cB cC cF cvv brtpos pm5.21nd $.

    $( The domain of ` tpos F ` when ` dom F ` is a relation.  (Contributed by
       Mario Carneiro, 10-Sep-2015.) $)
    dmtpos $p |- ( Rel dom F -> dom tpos F = `' dom F ) $=
      cF ctpos cdm wrel cF cdm ccnv wrel wa cF cdm wrel cF ctpos cdm cF cdm
      ccnv wceq cF cdm wrel cF ctpos cdm wrel cF cdm ccnv wrel cF cdm cvv cvv
      cxp wss c0 cF cdm wcel wn cF cdm wrel cF ctpos cdm wrel cF cdm cvv cvv
      cxp wss c0 cF cdm wcel c0 cvv cvv cxp wcel cvv cvv 0nelxp cF cdm cvv cvv
      cxp c0 ssel mtoi cF cdm df-rel cF reldmtpos 3imtr4i cF cdm relcnv jctir
      cF cdm wrel vx vy cF ctpos cdm cF cdm ccnv cF cdm wrel vx cv vy cv cop vz
      cv cF ctpos wbr vz wex vy cv vx cv cop vz cv cF wbr vz wex vx cv vy cv
      cop cF ctpos cdm wcel vx cv vy cv cop cF cdm ccnv wcel cF cdm wrel vx cv
      vy cv cop vz cv cF ctpos wbr vy cv vx cv cop vz cv cF wbr vz vz cv cvv
      wcel vx cv vy cv cop vz cv cF ctpos wbr vy cv vx cv cop vz cv cF wbr wb
      cF cdm wrel vz vex vx cv vy cv vz cv cF cvv brtpos mp1i exbidv vz vx cv
      vy cv cop cF ctpos vx cv vy cv opex eldm vx cv vy cv cop cF cdm ccnv wcel
      vy cv vx cv cop cF cdm wcel vy cv vx cv cop vz cv cF wbr vz wex vx cv vy
      cv cF cdm vx vex vy vex opelcnv vz vy cv vx cv cop cF vy cv vx cv opex
      eldm bitri 3bitr4g eqrelrdv2 mpancom $.

    $( The range of ` tpos F ` when ` dom F ` is a relation.  (Contributed by
       Mario Carneiro, 10-Sep-2015.) $)
    rntpos $p |- ( Rel dom F -> ran tpos F = ran F ) $=
      cF cdm wrel vz cF ctpos crn cF crn cF cdm wrel vz cv cF ctpos crn wcel vz
      cv cF crn wcel vz cv cF ctpos crn wcel vw cv vz cv cF ctpos wbr vw wex cF
      cdm wrel vz cv cF crn wcel vw vz cv cF ctpos vz vex elrn cF cdm wrel vw
      cv vz cv cF ctpos wbr vz cv cF crn wcel vw vw cv vz cv cF ctpos wbr cF
      cdm wrel vw cv vx cv vy cv cop wceq vy wex vx wex vz cv cF crn wcel cF
      cdm wrel vw cv vz cv cF ctpos wbr vw cv cF cdm ccnv wcel vw cv vx cv vy
      cv cop wceq vy wex vx wex vw cv vz cv cF ctpos wbr vw cv cF ctpos cdm
      wcel cF cdm wrel vw cv cF cdm ccnv wcel vw cv vz cv cF ctpos vw vex vz
      vex breldm cF cdm wrel cF ctpos cdm cF cdm ccnv vw cv cF dmtpos eleq2d
      syl5ib cF cdm ccnv wrel vw cv cF cdm ccnv wcel vw cv vx cv vy cv cop wceq
      vy wex vx wex cF cdm relcnv vx vy vw cv cF cdm ccnv elrel mpan syl6 vw cv
      vx cv vy cv cop wceq vw cv vz cv cF ctpos wbr vz cv cF crn wcel wi vx vy
      vw cv vx cv vy cv cop wceq vw cv vz cv cF ctpos wbr vy cv vx cv cop vz cv
      cF wbr vz cv cF crn wcel vw cv vx cv vy cv cop wceq vw cv vz cv cF ctpos
      wbr vx cv vy cv cop vz cv cF ctpos wbr vy cv vx cv cop vz cv cF wbr vw cv
      vx cv vy cv cop vz cv cF ctpos breq1 vz cv cvv wcel vx cv vy cv cop vz cv
      cF ctpos wbr vy cv vx cv cop vz cv cF wbr wb vz vex vx cv vy cv vz cv cF
      cvv brtpos ax-mp syl6bb vy cv vx cv cop vz cv cF vy cv vx cv opex vz vex
      brelrn syl6bi exlimivv syli exlimdv syl5bi vz cv cF crn wcel vw cv vz cv
      cF wbr vw wex cF cdm wrel vz cv cF ctpos crn wcel vw vz cv cF vz vex elrn
      cF cdm wrel vw cv vz cv cF wbr vz cv cF ctpos crn wcel vw vw cv vz cv cF
      wbr cF cdm wrel vw cv vy cv vx cv cop wceq vx wex vy wex vz cv cF ctpos
      crn wcel vw cv vz cv cF wbr vw cv cF cdm wcel cF cdm wrel vw cv vy cv vx
      cv cop wceq vx wex vy wex vw cv vz cv cF vw vex vz vex breldm cF cdm wrel
      vw cv cF cdm wcel vw cv vy cv vx cv cop wceq vx wex vy wex vy vx vw cv cF
      cdm elrel ex syl5 vw cv vy cv vx cv cop wceq vw cv vz cv cF wbr vz cv cF
      ctpos crn wcel wi vy vx vw cv vy cv vx cv cop wceq vw cv vz cv cF wbr vx
      cv vy cv cop vz cv cF ctpos wbr vz cv cF ctpos crn wcel vw cv vy cv vx cv
      cop wceq vw cv vz cv cF wbr vy cv vx cv cop vz cv cF wbr vx cv vy cv cop
      vz cv cF ctpos wbr vw cv vy cv vx cv cop vz cv cF breq1 vz cv cvv wcel vx
      cv vy cv cop vz cv cF ctpos wbr vy cv vx cv cop vz cv cF wbr wb vz vex vx
      cv vy cv vz cv cF cvv brtpos ax-mp syl6bbr vx cv vy cv cop vz cv cF ctpos
      vx cv vy cv opex vz vex brelrn syl6bi exlimivv syli exlimdv syl5bi impbid
      eqrdv $.

    $( The transposition of a set is a set.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    tposexg $p |- ( F e. V -> tpos F e. _V ) $=
      cF cV wcel cF ctpos cF cdm ccnv c0 csn cun cF crn cxp wss cF cdm ccnv c0
      csn cun cF crn cxp cvv wcel cF ctpos cvv wcel cF tposssxp cF cV wcel cF
      cdm ccnv c0 csn cun cvv wcel cF crn cvv wcel cF cdm ccnv c0 csn cun cF
      crn cxp cvv wcel cF cV wcel cF cdm ccnv cvv wcel c0 csn cvv wcel cF cdm
      ccnv c0 csn cun cvv wcel cF cV wcel cF cdm cvv wcel cF cdm ccnv cvv wcel
      cF cV dmexg cF cdm cvv cnvexg syl c0 snex cF cdm ccnv c0 csn cvv cvv
      unexg sylancl cF cV rnexg cF cdm ccnv c0 csn cun cF crn cvv cvv xpexg
      syl2anc cF ctpos cF cdm ccnv c0 csn cun cF crn cxp cvv ssexg sylancr $.

    $( The transposition swaps the arguments in a two-argument function.  When
       ` F ` is a matrix, which is to say a function from
       ` ( 1 ... m ) X. ( 1 ... n ) ` to ` RR ` or some ring, ` tpos F ` is the
       transposition of ` F ` , which is where the name comes from.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
    ovtpos $p |- ( A tpos F B ) = ( B F A ) $=
      cA cB cop cF ctpos cfv cB cA cop cF cfv cA cB cF ctpos co cB cA cF co cA
      cB cop vy cv cF ctpos wbr vy cio cB cA cop vy cv cF wbr vy cio cA cB cop
      cF ctpos cfv cB cA cop cF cfv cA cB cop vy cv cF ctpos wbr cB cA cop vy
      cv cF wbr vy vy cv cvv wcel cA cB cop vy cv cF ctpos wbr cB cA cop vy cv
      cF wbr wb vy vex cA cB vy cv cF cvv brtpos ax-mp iotabii vy cA cB cop cF
      ctpos df-fv vy cB cA cop cF df-fv 3eqtr4i cA cB cF ctpos df-ov cB cA cF
      df-ov 3eqtr4i $.

    $( The transposition of a function is a function.  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
    tposfun $p |- ( Fun F -> Fun tpos F ) $=
      cF wfun cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom wfun
      cF ctpos wfun cF wfun vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt
      wfun cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom wfun vx
      cF cdm ccnv c0 csn cun vx cv csn ccnv cuni funmpt cF vx cF cdm ccnv c0
      csn cun vx cv csn ccnv cuni cmpt funco mpan2 cF ctpos cF vx cF cdm ccnv
      c0 csn cun vx cv csn ccnv cuni cmpt ccom vx cF df-tpos funeqi sylibr $.

    $( Alternate definition of ` tpos ` when ` F ` has relational domain.
       (Contributed by Mario Carneiro, 10-Sep-2015.) $)
    dftpos2 $p |- ( Rel dom F -> tpos F =
        ( F o. ( x e. `' dom F |-> U. `' { x } ) ) ) $=
      cF cdm wrel cF ctpos cF ctpos cdm cres cF ctpos cF cdm ccnv cres cF ctpos
      cF vx cF cdm ccnv vx cv csn ccnv cuni cmpt ccom cF cdm wrel cF ctpos cdm
      cF cdm ccnv cF ctpos cF dmtpos reseq2d cF ctpos wrel cF ctpos cF ctpos
      cdm cres cF ctpos wceq cF reltpos cF ctpos resdm ax-mp cF ctpos cF cdm
      ccnv cres cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cF
      cdm ccnv cres cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt cF
      cdm ccnv cres ccom cF vx cF cdm ccnv vx cv csn ccnv cuni cmpt ccom cF
      ctpos cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cF cdm
      ccnv vx cF df-tpos reseq1i cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt cF cdm ccnv resco vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni
      cmpt cF cdm ccnv cres vx cF cdm ccnv vx cv csn ccnv cuni cmpt cF cF cdm
      ccnv cF cdm ccnv c0 csn cun wss vx cF cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt cF cdm ccnv cres vx cF cdm ccnv vx cv csn ccnv cuni cmpt wceq
      cF cdm ccnv c0 csn ssun1 vx cF cdm ccnv c0 csn cun cF cdm ccnv vx cv csn
      ccnv cuni resmpt ax-mp coeq2i 3eqtri 3eqtr3g $.

    $( Alternate definition of ` tpos ` when ` F ` has relational domain.
       Compare ~ df-cnv .  (Contributed by Mario Carneiro, 10-Sep-2015.) $)
    dftpos3 $p |- ( Rel dom F -> tpos F =
      { <. <. x , y >. , z >. | <. y , x >. F z } ) $=
      cF cdm wrel cF ctpos vw cv vx cv vy cv cop vz cv cop wceq vy cv vx cv cop
      vz cv cF wbr wa vz wex vy wex vx wex vw cab vy cv vx cv cop vz cv cF wbr
      vx vy vz coprab cF cdm wrel vw cv vx cv vy cv cop vz cv cop wceq vy cv vx
      cv cop vz cv cF wbr wa vz wex vy wex vx wex vw cF ctpos cF cdm wrel vw cv
      cF ctpos wcel vw cv vx cv vy cv cop vz cv cop wceq vz wex vy wex vx wex
      vw cv cF ctpos wcel wa vw cv vx cv vy cv cop vz cv cop wceq vy cv vx cv
      cop vz cv cF wbr wa vz wex vy wex vx wex cF cdm wrel vw cv cF ctpos wcel
      vw cv vx cv vy cv cop vz cv cop wceq vz wex vy wex vx wex cF cdm wrel vw
      cv cF ctpos wcel vw cv cvv cvv cxp cvv cxp wcel vw cv vx cv vy cv cop vz
      cv cop wceq vz wex vy wex vx wex cF cdm wrel cF ctpos cvv cvv cxp cvv cxp
      vw cv cF cdm wrel cF ctpos wrel cF ctpos cdm wrel wa cF ctpos cvv cvv cxp
      cvv cxp wss cF cdm wrel cF ctpos cdm wrel cF ctpos wrel cF cdm wrel cF
      ctpos cdm wrel cF cdm ccnv wrel cF cdm relcnv cF cdm wrel cF ctpos cdm cF
      cdm ccnv cF dmtpos releqd mpbiri cF reltpos jctil cF ctpos relrelss sylib
      sseld vx vy vz vw cv elvvv syl6ib pm4.71rd vw cv vx cv vy cv cop vz cv
      cop wceq vz wex vy wex vx wex vw cv cF ctpos wcel wa vw cv vx cv vy cv
      cop vz cv cop wceq vw cv cF ctpos wcel wa vz wex vy wex vx wex vw cv vx
      cv vy cv cop vz cv cop wceq vy cv vx cv cop vz cv cF wbr wa vz wex vy wex
      vx wex vw cv vx cv vy cv cop vz cv cop wceq vw cv cF ctpos wcel vx vy vz
      19.41vvv vw cv vx cv vy cv cop vz cv cop wceq vw cv cF ctpos wcel wa vw
      cv vx cv vy cv cop vz cv cop wceq vy cv vx cv cop vz cv cF wbr wa vx vy
      vz vw cv vx cv vy cv cop vz cv cop wceq vw cv cF ctpos wcel vy cv vx cv
      cop vz cv cF wbr vw cv vx cv vy cv cop vz cv cop wceq vw cv cF ctpos wcel
      vx cv vy cv cop vz cv cop cF ctpos wcel vy cv vx cv cop vz cv cF wbr vw
      cv vx cv vy cv cop vz cv cop cF ctpos eleq1 vx cv vy cv cop vz cv cop cF
      ctpos wcel vx cv vy cv cop vz cv cF ctpos wbr vy cv vx cv cop vz cv cF
      wbr vx cv vy cv cop vz cv cF ctpos df-br vz cv cvv wcel vx cv vy cv cop
      vz cv cF ctpos wbr vy cv vx cv cop vz cv cF wbr wb vz vex vx cv vy cv vz
      cv cF cvv brtpos ax-mp bitr3i syl6bb pm5.32i 3exbii bitr3i syl6bb abbi2dv
      vy cv vx cv cop vz cv cF wbr vx vy vz vw df-oprab syl6eqr $.

    $( Alternate definition of ` tpos ` .  (Contributed by Mario Carneiro,
       4-Oct-2015.) $)
    dftpos4 $p |- tpos F =
        ( F o. ( x e. ( ( _V X. _V ) u. { (/) } ) |-> U. `' { x } ) ) $=
      cF ctpos cF vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt ccom cF
      ctpos cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt ccom cF vx
      cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt ccom vx cF df-tpos vx cF
      cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt vx cvv cvv cxp c0 csn cun vx
      cv csn ccnv cuni cmpt wss cF vx cF cdm ccnv c0 csn cun vx cv csn ccnv
      cuni cmpt ccom cF vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt ccom
      wss vx cF cdm ccnv c0 csn cun vx cv csn ccnv cuni cmpt vx cvv cvv cxp c0
      csn cun vx cv csn ccnv cuni cmpt cF cdm ccnv c0 csn cun cres vx cvv cvv
      cxp c0 csn cun vx cv csn ccnv cuni cmpt cF cdm ccnv cvv cvv cxp wss cF
      cdm ccnv c0 csn cun cvv cvv cxp c0 csn cun wss vx cvv cvv cxp c0 csn cun
      vx cv csn ccnv cuni cmpt cF cdm ccnv c0 csn cun cres vx cF cdm ccnv c0
      csn cun vx cv csn ccnv cuni cmpt wceq cF cdm ccnv wrel cF cdm ccnv cvv
      cvv cxp wss cF cdm relcnv cF cdm ccnv df-rel mpbi cF cdm ccnv cvv cvv cxp
      c0 csn unss1 vx cvv cvv cxp c0 csn cun cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni resmpt mp2b vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt
      cF cdm ccnv c0 csn cun resss eqsstr3i vx cF cdm ccnv c0 csn cun vx cv csn
      ccnv cuni cmpt vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt cF
      coss2 ax-mp eqsstri vy vz cF vx cvv cvv cxp c0 csn cun vx cv csn ccnv
      cuni cmpt ccom cF ctpos cF vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni
      cmpt relco vy cv vz cv cop cF vx cvv cvv cxp c0 csn cun vx cv csn ccnv
      cuni cmpt ccom wcel vy cv vw cv vx cvv cvv cxp c0 csn cun vx cv csn ccnv
      cuni cmpt wbr vw cv vz cv cF wbr wa vw wex vy cv vz cv cop cF ctpos wcel
      vw vy cv vz cv cF vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt vy
      vex vz vex opelco vy cv vw cv vx cvv cvv cxp c0 csn cun vx cv csn ccnv
      cuni cmpt wbr vw cv vz cv cF wbr wa vy cv vz cv cop cF ctpos wcel vw vy
      cv vw cv vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt wbr vw cv vz
      cv cF wbr wa vy cv vz cv cF ctpos wbr vy cv vz cv cop cF ctpos wcel vy cv
      vw cv vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt wbr vw cv vz cv
      cF wbr wa vy cv cF cdm ccnv c0 csn cun wcel vy cv csn ccnv cuni vz cv cF
      wbr wa vy cv vz cv cF ctpos wbr vy cv vw cv vx cvv cvv cxp c0 csn cun vx
      cv csn ccnv cuni cmpt wbr vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv
      csn ccnv cuni wceq wa vw cv vz cv cF wbr vy cv cF cdm ccnv c0 csn cun
      wcel vy cv csn ccnv cuni vz cv cF wbr wa vx cv cvv cvv cxp c0 csn cun
      wcel vz cv vx cv csn ccnv cuni wceq wa vy cv cvv cvv cxp c0 csn cun wcel
      vz cv vy cv csn ccnv cuni wceq wa vy cv cvv cvv cxp c0 csn cun wcel vw cv
      vy cv csn ccnv cuni wceq wa vx vz vy cv vw cv vx cvv cvv cxp c0 csn cun
      vx cv csn ccnv cuni cmpt vy vex vw vex vx cv vy cv wceq vx cv cvv cvv cxp
      c0 csn cun wcel vy cv cvv cvv cxp c0 csn cun wcel vz cv vx cv csn ccnv
      cuni wceq vz cv vy cv csn ccnv cuni wceq vx cv vy cv cvv cvv cxp c0 csn
      cun eleq1 vx cv vy cv wceq vx cv csn ccnv cuni vy cv csn ccnv cuni vz cv
      vx cv vy cv wceq vx cv csn ccnv vy cv csn ccnv vx cv vy cv wceq vx cv csn
      vy cv csn vx cv vy cv sneq cnveqd unieqd eqeq2d anbi12d vz cv vw cv wceq
      vz cv vy cv csn ccnv cuni wceq vw cv vy cv csn ccnv cuni wceq vy cv cvv
      cvv cxp c0 csn cun wcel vz cv vw cv vy cv csn ccnv cuni eqeq1 anbi2d vx
      vz cvv cvv cxp c0 csn cun vx cv csn ccnv cuni df-mpt brab vy cv cvv cvv
      cxp c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq wa vw cv vz cv cF wbr
      wa vy cv cF cdm ccnv c0 csn cun wcel vy cv csn ccnv cuni vz cv cF wbr vy
      cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq wa vw cv vz
      cv cF wbr wa vy cv cvv cvv cxp wcel vy cv cF cdm ccnv c0 csn cun wcel vy
      cv c0 csn wcel vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv
      cuni wceq wa vw cv vz cv cF wbr wa vy cv csn ccnv cuni cF cdm wcel vy cv
      cvv cvv cxp wcel vy cv cF cdm ccnv c0 csn cun wcel wi vy cv cvv cvv cxp
      c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq wa vw cv vz cv cF wbr wa
      vw cv vy cv csn ccnv cuni cF cdm vy cv cvv cvv cxp c0 csn cun wcel vw cv
      vy cv csn ccnv cuni wceq vw cv vz cv cF wbr simplr vw cv vz cv cF wbr vw
      cv cF cdm wcel vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv
      cuni wceq wa vw cv vz cv cF vw vex vz vex breldm adantl eqeltrrd vy cv
      csn ccnv cuni cF cdm wcel vy cv cvv cvv cxp wcel vy cv cF cdm ccnv wcel
      vy cv cF cdm ccnv c0 csn cun wcel vy cv cvv cvv cxp wcel vy cv csn ccnv
      cuni cF cdm wcel vy cv cF cdm ccnv wcel vy cv cvv cvv cxp wcel vy cv vz
      cv vw cv cop wceq vw wex vz wex vy cv csn ccnv cuni cF cdm wcel vy cv cF
      cdm ccnv wcel wb vz vw vy cv elvv vy cv vz cv vw cv cop wceq vy cv csn
      ccnv cuni cF cdm wcel vy cv cF cdm ccnv wcel wb vz vw vy cv vz cv vw cv
      cop wceq vy cv csn ccnv cuni cF cdm wcel vy cv cF cdm ccnv wcel wb vz cv
      vw cv cop csn ccnv cuni cF cdm wcel vz cv vw cv cop cF cdm ccnv wcel wb
      vz cv vw cv cop csn ccnv cuni cF cdm wcel vw cv vz cv cop cF cdm wcel vz
      cv vw cv cop cF cdm ccnv wcel vz cv vw cv cop csn ccnv cuni vw cv vz cv
      cop cF cdm vz cv vw cv opswap eleq1i vz cv vw cv cF cdm vz vex vw vex
      opelcnv bitr4i vy cv vz cv vw cv cop wceq vy cv csn ccnv cuni cF cdm wcel
      vz cv vw cv cop csn ccnv cuni cF cdm wcel vy cv cF cdm ccnv wcel vz cv vw
      cv cop cF cdm ccnv wcel vy cv vz cv vw cv cop wceq vy cv csn ccnv cuni vz
      cv vw cv cop csn ccnv cuni cF cdm vy cv vz cv vw cv cop wceq vy cv csn
      ccnv vz cv vw cv cop csn ccnv vy cv vz cv vw cv cop wceq vy cv csn vz cv
      vw cv cop csn vy cv vz cv vw cv cop sneq cnveqd unieqd eleq1d vy cv vz cv
      vw cv cop cF cdm ccnv eleq1 bibi12d mpbiri exlimivv sylbi biimpcd vy cv
      cF cdm ccnv c0 csn elun1 syl6 syl vy cv c0 csn wcel vy cv cF cdm ccnv c0
      csn cun wcel wi vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv
      cuni wceq wa vw cv vz cv cF wbr wa vy cv c0 csn cF cdm ccnv elun2 a1i vy
      cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq wa vw cv vz
      cv cF wbr wa vy cv cvv cvv cxp c0 csn cun wcel vy cv cvv cvv cxp wcel vy
      cv c0 csn wcel wo vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv
      cuni wceq vw cv vz cv cF wbr simpll vy cv cvv cvv cxp c0 csn elun sylib
      mpjaod vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq
      wa vw cv vz cv cF wbr wa vw cv vy cv csn ccnv cuni vz cv cF vy cv cvv cvv
      cxp c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq vw cv vz cv cF wbr
      simplr vy cv cvv cvv cxp c0 csn cun wcel vw cv vy cv csn ccnv cuni wceq
      wa vw cv vz cv cF wbr simpr eqbrtrrd jca sylanb vz cv cvv wcel vy cv vz
      cv cF ctpos wbr vy cv cF cdm ccnv c0 csn cun wcel vy cv csn ccnv cuni vz
      cv cF wbr wa wb vz vex vy cv vz cv cF cvv brtpos2 ax-mp sylibr vy cv vz
      cv cF ctpos df-br sylib exlimiv sylbi relssi eqssi $.

    $( Value of the double transposition for a general class ` F ` .
       (Contributed by Mario Carneiro, 16-Sep-2015.) $)
    tpostpos $p |- tpos tpos F =
        ( F i^i ( ( ( _V X. _V ) u. { (/) } ) X. _V ) ) $=
      vw vz cF ctpos ctpos cF cvv cvv cxp c0 csn cun cvv cxp cin cF ctpos
      reltpos cF cvv cvv cxp c0 csn cun cvv cxp cin cvv cvv cxp c0 csn cun cvv
      cxp wss cvv cvv cxp c0 csn cun cvv cxp wrel cF cvv cvv cxp c0 csn cun cvv
      cxp cin wrel cF cvv cvv cxp c0 csn cun cvv cxp inss2 cvv cvv cxp c0 csn
      cun cvv relxp cF cvv cvv cxp c0 csn cun cvv cxp cin cvv cvv cxp c0 csn
      cun cvv cxp relss mp2 vw cv cF ctpos cdm ccnv c0 csn cun wcel vw cv csn
      ccnv cuni vz cv cF ctpos wbr wa vw cv vz cv cF wbr vw cv vz cv cvv cvv
      cxp c0 csn cun cvv cxp wbr wa vw cv vz cv cF ctpos ctpos wbr vw cv vz cv
      cF cvv cvv cxp c0 csn cun cvv cxp cin wbr vw cv cF ctpos cdm ccnv wcel vw
      cv c0 csn wcel wo vw cv csn ccnv cuni vz cv cF ctpos wbr wa vw cv vz cv
      cF wbr vw cv cvv cvv cxp wcel vw cv c0 csn wcel wo wa vw cv cF ctpos cdm
      ccnv c0 csn cun wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vw cv vz
      cv cF wbr vw cv vz cv cvv cvv cxp c0 csn cun cvv cxp wbr wa vw cv cF
      ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vw cv c0
      csn wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa wo vw cv vz cv cF wbr
      vw cv cvv cvv cxp wcel wa vw cv vz cv cF wbr vw cv c0 csn wcel wa wo vw
      cv cF ctpos cdm ccnv wcel vw cv c0 csn wcel wo vw cv csn ccnv cuni vz cv
      cF ctpos wbr wa vw cv vz cv cF wbr vw cv cvv cvv cxp wcel vw cv c0 csn
      wcel wo wa vw cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF
      ctpos wbr wa vw cv vz cv cF wbr vw cv cvv cvv cxp wcel wa vw cv c0 csn
      wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vw cv vz cv cF wbr vw cv
      c0 csn wcel wa vw cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF
      ctpos wbr wa vw cv cvv cvv cxp wcel vw cv vz cv cF wbr vw cv cvv cvv cxp
      wcel wa vw cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF ctpos
      wbr wa cF ctpos cdm ccnv cvv cvv cxp vw cv cF ctpos cdm ccnv wrel cF
      ctpos cdm ccnv cvv cvv cxp wss cF ctpos cdm relcnv cF ctpos cdm ccnv
      df-rel mpbi vw cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF
      ctpos wbr simpl sseldi vw cv vz cv cF wbr vw cv cvv cvv cxp wcel simpr vw
      cv cvv cvv cxp wcel vw cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz
      cv cF ctpos wbr wa vw cv vz cv cF wbr vw cv vz cv cF wbr vw cv cvv cvv
      cxp wcel wa vw cv cvv cvv cxp wcel vw cv vx cv vy cv cop wceq vy wex vx
      wex vw cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF ctpos wbr
      wa vw cv vz cv cF wbr wb vx vy vw cv elvv vw cv vx cv vy cv cop wceq vw
      cv cF ctpos cdm ccnv wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vw cv
      vz cv cF wbr wb vx vy vw cv vx cv vy cv cop wceq vw cv cF ctpos cdm ccnv
      wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vx cv vy cv cop vz cv cF
      wbr vw cv vz cv cF wbr vw cv vx cv vy cv cop wceq vw cv cF ctpos cdm ccnv
      wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vy cv vx cv cop cF ctpos
      cdm wcel vy cv vx cv cop vz cv cF ctpos wbr wa vx cv vy cv cop vz cv cF
      wbr vw cv vx cv vy cv cop wceq vw cv cF ctpos cdm ccnv wcel vy cv vx cv
      cop cF ctpos cdm wcel vw cv csn ccnv cuni vz cv cF ctpos wbr vy cv vx cv
      cop vz cv cF ctpos wbr vw cv vx cv vy cv cop wceq vw cv cF ctpos cdm ccnv
      wcel vx cv vy cv cop cF ctpos cdm ccnv wcel vy cv vx cv cop cF ctpos cdm
      wcel vw cv vx cv vy cv cop cF ctpos cdm ccnv eleq1 vx cv vy cv cF ctpos
      cdm vx vex vy vex opelcnv syl6bb vw cv vx cv vy cv cop wceq vw cv csn
      ccnv cuni vy cv vx cv cop vz cv cF ctpos vw cv vx cv vy cv cop wceq vw cv
      csn ccnv cuni vx cv vy cv cop csn ccnv cuni vy cv vx cv cop vw cv vx cv
      vy cv cop wceq vw cv csn ccnv vx cv vy cv cop csn ccnv vw cv vx cv vy cv
      cop wceq vw cv csn vx cv vy cv cop csn vw cv vx cv vy cv cop sneq cnveqd
      unieqd vx cv vy cv opswap syl6eq breq1d anbi12d vy cv vx cv cop cF ctpos
      cdm wcel vy cv vx cv cop vz cv cF ctpos wbr wa vy cv vx cv cop vz cv cF
      ctpos wbr vx cv vy cv cop vz cv cF wbr vy cv vx cv cop vz cv cF ctpos wbr
      vy cv vx cv cop cF ctpos cdm wcel vy cv vx cv cop vz cv cF ctpos vy cv vx
      cv opex vz vex breldm pm4.71ri vz cv cvv wcel vy cv vx cv cop vz cv cF
      ctpos wbr vx cv vy cv cop vz cv cF wbr wb vz vex vy cv vx cv vz cv cF cvv
      brtpos ax-mp bitr3i syl6bb vw cv vx cv vy cv cop vz cv cF breq1 bitr4d
      exlimivv sylbi vw cv cvv cvv cxp wcel vw cv vz cv cF wbr iba bitrd
      pm5.21nii vw cv c0 csn wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa vw
      cv c0 csn wcel vw cv vz cv cF wbr wa vw cv vz cv cF wbr vw cv c0 csn wcel
      wa vw cv c0 csn wcel vw cv csn ccnv cuni vz cv cF ctpos wbr vw cv vz cv
      cF wbr vw cv c0 csn wcel vw cv csn ccnv cuni vz cv cF ctpos wbr c0 vz cv
      cF wbr vw cv vz cv cF wbr vw cv c0 csn wcel vw cv csn ccnv cuni vz cv cF
      ctpos wbr c0 vz cv cF ctpos wbr c0 vz cv cF wbr vw cv c0 csn wcel vw cv
      csn ccnv cuni c0 vz cv cF ctpos vw cv c0 csn wcel vw cv csn ccnv cuni c0
      cuni c0 vw cv c0 csn wcel vw cv csn ccnv c0 vw cv c0 csn wcel vw cv csn
      ccnv c0 csn ccnv c0 vw cv c0 csn wcel vw cv csn c0 csn vw cv c0 csn wcel
      vw cv c0 vw cv c0 elsni sneqd cnveqd cnvsn0 syl6eq unieqd uni0 syl6eq
      breq1d vz cv cvv wcel c0 vz cv cF ctpos wbr c0 vz cv cF wbr wb vz vex vz
      cv cF cvv brtpos0 ax-mp syl6bb vw cv c0 csn wcel vw cv c0 vz cv cF vw cv
      c0 elsni breq1d bitr4d pm5.32i vw cv c0 csn wcel vw cv vz cv cF wbr ancom
      bitri orbi12i vw cv cF ctpos cdm ccnv wcel vw cv c0 csn wcel vw cv csn
      ccnv cuni vz cv cF ctpos wbr andir vw cv vz cv cF wbr vw cv cvv cvv cxp
      wcel vw cv c0 csn wcel andi 3bitr4i vw cv cF ctpos cdm ccnv c0 csn cun
      wcel vw cv cF ctpos cdm ccnv wcel vw cv c0 csn wcel wo vw cv csn ccnv
      cuni vz cv cF ctpos wbr vw cv cF ctpos cdm ccnv c0 csn elun anbi1i vw cv
      vz cv cvv cvv cxp c0 csn cun cvv cxp wbr vw cv cvv cvv cxp wcel vw cv c0
      csn wcel wo vw cv vz cv cF wbr vw cv vz cv cvv cvv cxp c0 csn cun cvv cxp
      wbr vw cv cvv cvv cxp c0 csn cun wcel vw cv cvv cvv cxp wcel vw cv c0 csn
      wcel wo vw cv vz cv cvv cvv cxp c0 csn cun cvv cxp wbr vw cv cvv cvv cxp
      c0 csn cun wcel vz cv cvv wcel vz vex vw cv vz cv cvv cvv cxp c0 csn cun
      cvv brxp mpbiran2 vw cv cvv cvv cxp c0 csn elun bitri anbi2i 3bitr4i vz
      cv cvv wcel vw cv vz cv cF ctpos ctpos wbr vw cv cF ctpos cdm ccnv c0 csn
      cun wcel vw cv csn ccnv cuni vz cv cF ctpos wbr wa wb vz vex vw cv vz cv
      cF ctpos cvv brtpos2 ax-mp vw cv vz cv cF cvv cvv cxp c0 csn cun cvv cxp
      brin 3bitr4i eqbrriv $.

    $( Value of the double transposition for a relation on triples.
       (Contributed by Mario Carneiro, 16-Sep-2015.) $)
    tpostpos2 $p |- ( ( Rel F /\ Rel dom F ) -> tpos tpos F = F ) $=
      cF wrel cF cdm wrel wa cF ctpos ctpos cF cvv cvv cxp c0 csn cun cvv cxp
      cin cF cF tpostpos cF wrel cF cdm wrel wa cF cvv cvv cxp c0 csn cun cvv
      cxp wss cF cvv cvv cxp c0 csn cun cvv cxp cin cF wceq cF wrel cF cdm wrel
      wa cF cvv cvv cxp cvv cxp wss cF cvv cvv cxp c0 csn cun cvv cxp wss cF
      relrelss cF cvv cvv cxp cvv cxp wss cvv cvv cxp cvv cxp cvv cvv cxp c0
      csn cun cvv cxp wss cF cvv cvv cxp c0 csn cun cvv cxp wss cvv cvv cxp cvv
      cvv cxp c0 csn cun wss cvv cvv cxp cvv cxp cvv cvv cxp c0 csn cun cvv cxp
      wss cvv cvv cxp c0 csn ssun1 cvv cvv cxp cvv cvv cxp c0 csn cun cvv xpss1
      ax-mp cF cvv cvv cxp cvv cxp cvv cvv cxp c0 csn cun cvv cxp sstr mpan2
      sylbi cF cvv cvv cxp c0 csn cun cvv cxp df-ss sylib syl5eq $.

    $( The domain of a transposition.  (Contributed by NM, 10-Sep-2015.) $)
    tposfn2 $p |- ( Rel A -> ( F Fn A -> tpos F Fn `' A ) ) $=
      cA wrel cF wfun cF cdm cA wceq wa cF ctpos wfun cF ctpos cdm cA ccnv wceq
      wa cF cA wfn cF ctpos cA ccnv wfn cA wrel cF wfun cF ctpos wfun cF cdm cA
      wceq cF ctpos cdm cA ccnv wceq cF wfun cF ctpos wfun wi cA wrel cF
      tposfun a1i cF cdm cA wceq cA wrel cF ctpos cdm cA ccnv wceq cF cdm cA
      wceq cF cdm wrel cF ctpos cdm cF cdm ccnv wceq cA wrel cF ctpos cdm cA
      ccnv wceq cF cdm wrel cF ctpos cdm cF cdm ccnv wceq wi cF cdm cA wceq cF
      dmtpos a1i cF cdm cA releq cF cdm cA wceq cF cdm ccnv cA ccnv cF ctpos
      cdm cF cdm cA cnveq eqeq2d 3imtr3d com12 anim12d cF cA df-fn cF ctpos cA
      ccnv df-fn 3imtr4g $.

    $( Condition for a surjective transposition.  (Contributed by NM,
       10-Sep-2015.) $)
    tposfo2 $p |- ( Rel A ->
        ( F : A -onto-> B -> tpos F : `' A -onto-> B ) ) $=
      cA wrel cF cA wfn cF crn cB wceq wa cF ctpos cA ccnv wfn cF ctpos crn cB
      wceq wa cA cB cF wfo cA ccnv cB cF ctpos wfo cA wrel cF cA wfn cF crn cB
      wceq wa cF ctpos cA ccnv wfn cF ctpos crn cB wceq cA wrel cF cA wfn cF
      ctpos cA ccnv wfn cF crn cB wceq cA cF tposfn2 adantrd cA wrel cF cA wfn
      cF crn cB wceq cF ctpos crn cB wceq cA wrel cF cA wfn wa cF ctpos crn cB
      wceq cF crn cB wceq cA wrel cF cA wfn wa cF ctpos crn cF crn cB cA wrel
      cF cA wfn wa cF cdm wrel cF ctpos crn cF crn wceq cF cA wfn cF cdm wrel
      cA wrel cF cA wfn cF cdm cA cA cF fndm releqd biimparc cF rntpos syl
      eqeq1d biimprd expimpd jcad cA cB cF df-fo cA ccnv cB cF ctpos df-fo
      3imtr4g $.

    $( The domain and range of a transposition.  (Contributed by NM,
       10-Sep-2015.) $)
    tposf2 $p |- ( Rel A -> ( F : A --> B -> tpos F : `' A --> B ) ) $=
      cA wrel cA cB cF wf cA ccnv cB cF ctpos wf cA wrel cA cB cF wf wa cA ccnv
      cF crn cF ctpos wf cF crn cB wss cA ccnv cB cF ctpos wf cA wrel cA cB cF
      wf wa cA ccnv cF crn cF ctpos wfo cA ccnv cF crn cF ctpos wf cA wrel cA
      cB cF wf cA ccnv cF crn cF ctpos wfo cA cB cF wf cA cF crn cF wfo cA wrel
      cA ccnv cF crn cF ctpos wfo cA cB cF wf cF cA wfn cA cF crn cF wfo cA cB
      cF ffn cA cF dffn4 sylib cA cF crn cF tposfo2 syl5 imp cA ccnv cF crn cF
      ctpos fof syl cA cB cF wf cF crn cB wss cA wrel cA cB cF frn adantl cA
      ccnv cF crn cB cF ctpos fss syl2anc ex $.

    $( Condition for an injective transposition.  (Contributed by NM,
       10-Sep-2015.) $)
    tposf12 $p |- ( Rel A -> ( F : A -1-1-> B -> tpos F : `' A -1-1-> B ) ) $=
      cA wrel cA cB cF wf1 cA ccnv cB cF ctpos wf1 cA wrel cA cB cF wf1 wa cA
      ccnv cB cF ctpos wf1 cA ccnv cB cF vx cF cdm ccnv vx cv csn ccnv cuni
      cmpt ccom wf1 cA wrel cA cB cF wf1 wa cA cB cF wf1 cA ccnv cA vx cF cdm
      ccnv vx cv csn ccnv cuni cmpt wf1 cA ccnv cB cF vx cF cdm ccnv vx cv csn
      ccnv cuni cmpt ccom wf1 cA wrel cA cB cF wf1 simpr cA wrel cA cB cF wf1
      wa cA ccnv cA vx cF cdm ccnv vx cv csn ccnv cuni cmpt wf1 cA ccnv cA vx
      cA ccnv vx cv csn ccnv cuni cmpt wf1 cA wrel cA cB cF wf1 wa cA ccnv cA
      ccnv ccnv vx cA ccnv vx cv csn ccnv cuni cmpt wf1 cA ccnv cA vx cA ccnv
      vx cv csn ccnv cuni cmpt wf1 cA ccnv wrel cA ccnv cA ccnv ccnv vx cA ccnv
      vx cv csn ccnv cuni cmpt wf1o cA ccnv cA ccnv ccnv vx cA ccnv vx cv csn
      ccnv cuni cmpt wf1 cA relcnv vx cA ccnv cnvf1o cA ccnv cA ccnv ccnv vx cA
      ccnv vx cv csn ccnv cuni cmpt f1of1 mp2b cA wrel cA cB cF wf1 wa cA ccnv
      ccnv cA wceq cA ccnv cA ccnv ccnv vx cA ccnv vx cv csn ccnv cuni cmpt wf1
      cA ccnv cA vx cA ccnv vx cv csn ccnv cuni cmpt wf1 wb cA wrel cA cB cF
      wf1 wa cA wrel cA ccnv ccnv cA wceq cA wrel cA cB cF wf1 simpl cA dfrel2
      sylib cA ccnv ccnv cA cA ccnv vx cA ccnv vx cv csn ccnv cuni cmpt f1eq3
      syl mpbii cA wrel cA cB cF wf1 wa cF cdm ccnv cA ccnv wceq vx cF cdm ccnv
      vx cv csn ccnv cuni cmpt vx cA ccnv vx cv csn ccnv cuni cmpt wceq cA ccnv
      cA vx cF cdm ccnv vx cv csn ccnv cuni cmpt wf1 cA ccnv cA vx cA ccnv vx
      cv csn ccnv cuni cmpt wf1 wb cA wrel cA cB cF wf1 wa cF cdm cA cA wrel cA
      cB cF wf1 wa cA cB cF wf1 cF cdm cA wceq cA wrel cA cB cF wf1 simpr cA cB
      cF f1dm syl cnveqd vx cF cdm ccnv cA ccnv vx cv csn ccnv cuni mpteq1 cA
      ccnv cA vx cF cdm ccnv vx cv csn ccnv cuni cmpt vx cA ccnv vx cv csn ccnv
      cuni cmpt f1eq1 3syl mpbird cA ccnv cA cB cF vx cF cdm ccnv vx cv csn
      ccnv cuni cmpt f1co syl2anc cA wrel cA cB cF wf1 wa cF cdm wrel cF ctpos
      cF vx cF cdm ccnv vx cv csn ccnv cuni cmpt ccom wceq cA ccnv cB cF ctpos
      wf1 cA ccnv cB cF vx cF cdm ccnv vx cv csn ccnv cuni cmpt ccom wf1 wb cA
      cB cF wf1 cF cdm wrel cA wrel cA cB cF wf1 cF cdm cA cA cB cF f1dm releqd
      biimparc vx cF dftpos2 cA ccnv cB cF ctpos cF vx cF cdm ccnv vx cv csn
      ccnv cuni cmpt ccom f1eq1 3syl mpbird ex $.

    $( Condition of a bijective transposition.  (Contributed by NM,
       10-Sep-2015.) $)
    tposf1o2 $p |- ( Rel A ->
      ( F : A -1-1-onto-> B -> tpos F : `' A -1-1-onto-> B ) ) $=
      cA wrel cA cB cF wf1 cA cB cF wfo wa cA ccnv cB cF ctpos wf1 cA ccnv cB
      cF ctpos wfo wa cA cB cF wf1o cA ccnv cB cF ctpos wf1o cA wrel cA cB cF
      wf1 cA ccnv cB cF ctpos wf1 cA cB cF wfo cA ccnv cB cF ctpos wfo cA cB cF
      tposf12 cA cB cF tposfo2 anim12d cA cB cF df-f1o cA ccnv cB cF ctpos
      df-f1o 3imtr4g $.

    $( The domain and range of a transposition.  (Contributed by NM,
       10-Sep-2015.) $)
    tposfo $p |- ( F : ( A X. B ) -onto-> C ->
              tpos F : ( B X. A ) -onto-> C ) $=
      cA cB cxp cC cF wfo cA cB cxp ccnv cC cF ctpos wfo cB cA cxp cC cF ctpos
      wfo cA cB cxp wrel cA cB cxp cC cF wfo cA cB cxp ccnv cC cF ctpos wfo wi
      cA cB relxp cA cB cxp cC cF tposfo2 ax-mp cA cB cxp ccnv cB cA cxp wceq
      cA cB cxp ccnv cC cF ctpos wfo cB cA cxp cC cF ctpos wfo wb cA cB cnvxp
      cA cB cxp ccnv cB cA cxp cC cF ctpos foeq2 ax-mp sylib $.

    $( The domain and range of a transposition.  (Contributed by NM,
       10-Sep-2015.) $)
    tposf $p |- ( F : ( A X. B ) --> C -> tpos F : ( B X. A ) --> C ) $=
      cA cB cxp cC cF wf cA cB cxp ccnv cC cF ctpos wf cB cA cxp cC cF ctpos wf
      cA cB cxp wrel cA cB cxp cC cF wf cA cB cxp ccnv cC cF ctpos wf wi cA cB
      relxp cA cB cxp cC cF tposf2 ax-mp cA cB cxp ccnv cB cA cxp cC cF ctpos
      cA cB cnvxp feq2i sylib $.

    $( Functionality of a transposition.  (Contributed by Mario Carneiro,
       4-Oct-2015.) $)
    tposfn $p |- ( F Fn ( A X. B ) -> tpos F Fn ( B X. A ) ) $=
      cA cB cxp cvv cF wf cB cA cxp cvv cF ctpos wf cF cA cB cxp wfn cF ctpos
      cB cA cxp wfn cA cB cvv cF tposf cA cB cxp cF dffn2 cB cA cxp cF ctpos
      dffn2 3imtr4i $.

    $( Transposition of the empty set.  (Contributed by NM, 10-Sep-2015.) $)
    tpos0 $p |- tpos (/) = (/) $=
      c0 ctpos c0 wfn c0 ctpos c0 wceq c0 ctpos c0 ccnv wfn c0 ctpos c0 wfn c0
      wrel c0 c0 wfn c0 ctpos c0 ccnv wfn rel0 c0 c0 wfn c0 c0 wceq c0 eqid c0
      fn0 mpbir c0 c0 tposfn2 mp2 c0 ccnv c0 c0 ctpos cnv0 fneq2i mpbi c0 ctpos
      fn0 mpbi $.

    $( Transposition of a composition.  (Contributed by Mario Carneiro,
       4-Oct-2015.) $)
    tposco $p |- tpos ( F o. G ) = ( F o. tpos G ) $=
      cF cG ccom vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt ccom cF cG
      vx cvv cvv cxp c0 csn cun vx cv csn ccnv cuni cmpt ccom ccom cF cG ccom
      ctpos cF cG ctpos ccom cF cG vx cvv cvv cxp c0 csn cun vx cv csn ccnv
      cuni cmpt coass vx cF cG ccom dftpos4 cG ctpos cG vx cvv cvv cxp c0 csn
      cun vx cv csn ccnv cuni cmpt ccom cF vx cG dftpos4 coeq2i 3eqtr4i $.

    $( Two ways to say a function is symmetric.  (Contributed by Mario
       Carneiro, 4-Oct-2015.) $)
    tpossym $p |- ( F Fn ( A X. A ) ->
      ( tpos F = F <-> A. x e. A A. y e. A ( x F y ) = ( y F x ) ) ) $=
      cF cA cA cxp wfn cF ctpos cF wceq vx cv vy cv cF ctpos co vx cv vy cv cF
      co wceq vy cA wral vx cA wral vx cv vy cv cF co vy cv vx cv cF co wceq vy
      cA wral vx cA wral cF ctpos cA cA cxp wfn cF cA cA cxp wfn cF ctpos cF
      wceq vx cv vy cv cF ctpos co vx cv vy cv cF co wceq vy cA wral vx cA wral
      wb cA cA cF tposfn vx vy cA cA cF ctpos cF eqfnov2 mpancom vx cv vy cv cF
      ctpos co vx cv vy cv cF co wceq vx cv vy cv cF co vy cv vx cv cF co wceq
      vx vy cA cA vx cv vy cv cF ctpos co vx cv vy cv cF co wceq vx cv vy cv cF
      co vx cv vy cv cF ctpos co wceq vx cv vy cv cF co vy cv vx cv cF co wceq
      vx cv vy cv cF ctpos co vx cv vy cv cF co eqcom vx cv vy cv cF ctpos co
      vy cv vx cv cF co vx cv vy cv cF co vx cv vy cv cF ovtpos eqeq2i bitri
      2ralbii syl6bb $.

  $}

  ${
    tposeqi.1 $e |- F = G $.
    $( Equality theorem for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    tposeqi $p |- tpos F = tpos G $=
      cF cG wceq cF ctpos cG ctpos wceq tposeqi.1 cF cG tposeq ax-mp $.
  $}

  ${
    tposex.1 $e |- F e. _V $.
    $( A transposition is a set.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    tposex $p |- tpos F e. _V $=
      cF cvv wcel cF ctpos cvv wcel tposex.1 cF cvv tposexg ax-mp $.
  $}

  ${
    $d x y $.  $d y F $.
    nftpos.1 $e |- F/_ x F $.
    $( Hypothesis builder for transposition.  (Contributed by Mario Carneiro,
       10-Sep-2015.) $)
    nftpos $p |- F/_ x tpos F $=
      vx cF ctpos cF vy cvv cvv cxp c0 csn cun vy cv csn ccnv cuni cmpt ccom vy
      cF dftpos4 vx cF vy cvv cvv cxp c0 csn cun vy cv csn ccnv cuni cmpt
      nftpos.1 vx vy cvv cvv cxp c0 csn cun vy cv csn ccnv cuni cmpt nfcv nfco
      nfcxfr $.
  $}

  ${
    $d a b c w x y z $.  $d a b c w ph $.
    tposoprab.1 $e |- F = { <. <. x , y >. , z >. | ph } $.
    $( Transposition of a class of ordered triples.  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
    tposoprab $p |- tpos F = { <. <. y , x >. , z >. | ph } $=
      cF ctpos wph vx vy vz coprab ctpos vb cv va cv cop vc cv wph vx vy vz
      coprab wbr va vb vc coprab wph vy vx vz coprab cF wph vx vy vz coprab
      tposoprab.1 tposeqi wph vx vy vz coprab cdm wrel wph vx vy vz coprab
      ctpos vb cv va cv cop vc cv wph vx vy vz coprab wbr va vb vc coprab wceq
      wph vx vy vz reldmoprab va vb vc wph vx vy vz coprab dftpos3 ax-mp vb cv
      va cv cop vc cv wph vx vy vz coprab wbr va vb vc coprab vx cv vy cv cop
      vc cv wph vx vy vz coprab wbr vy vx vc coprab wph vy vx vz coprab vb cv
      va cv cop vc cv wph vx vy vz coprab wbr vx cv vy cv cop vc cv wph vx vy
      vz coprab wbr va vb vc vy vx vy vb cv va cv cop vc cv wph vx vy vz coprab
      vy vb cv va cv cop nfcv wph vx vy vz nfoprab2 vy vc cv nfcv nfbr vx vb cv
      va cv cop vc cv wph vx vy vz coprab vx vb cv va cv cop nfcv wph vx vy vz
      nfoprab1 vx vc cv nfcv nfbr vx cv vy cv cop vc cv wph vx vy vz coprab wbr
      va nfv vx cv vy cv cop vc cv wph vx vy vz coprab wbr vb nfv va cv vy cv
      wceq vb cv vx cv wceq wa vb cv va cv cop vx cv vy cv cop vc cv wph vx vy
      vz coprab vb cv vx cv wceq va cv vy cv wceq vb cv va cv cop vx cv vy cv
      cop wceq vb cv va cv vx cv vy cv opeq12 ancoms breq1d cbvoprab12 vx cv vy
      cv cop vc cv wph vx vy vz coprab wbr wph vy vx vc vz vz vx cv vy cv cop
      vc cv wph vx vy vz coprab vz vx cv vy cv cop nfcv wph vx vy vz nfoprab3
      vz vc cv nfcv nfbr wph vc nfv vc cv vz cv wceq vx cv vy cv cop vc cv wph
      vx vy vz coprab wbr vx cv vy cv cop vz cv wph vx vy vz coprab wbr wph vc
      cv vz cv vx cv vy cv cop wph vx vy vz coprab breq2 vx cv vy cv cop vz cv
      wph vx vy vz coprab wbr vx cv vy cv cop vz cv cop wph vx vy vz coprab
      wcel wph vx cv vy cv cop vz cv wph vx vy vz coprab df-br wph vx vy vz
      oprabid bitri syl6bb cbvoprab3 eqtri 3eqtri $.
  $}

  ${
    $d x y z $.  $d z A $.  $d z B $.  $d z C $.
    tposmpt2.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( Transposition of a two-argument mapping.  (Contributed by Mario
       Carneiro, 10-Sep-2015.) $)
    tposmpt2 $p |- tpos F = ( y e. B , x e. A |-> C ) $=
      cF ctpos vy cv cB wcel vx cv cA wcel wa vz cv cC wceq wa vy vx vz coprab
      vy vx cB cA cC cmpt2 vy cv cB wcel vx cv cA wcel wa vz cv cC wceq wa vx
      vy vz cF cF vx vy cA cB cC cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cC
      wceq wa vx vy vz coprab vy cv cB wcel vx cv cA wcel wa vz cv cC wceq wa
      vx vy vz coprab tposmpt2.1 vx vy vz cA cB cC df-mpt2 vx cv cA wcel vy cv
      cB wcel wa vz cv cC wceq wa vy cv cB wcel vx cv cA wcel wa vz cv cC wceq
      wa vx vy vz vx cv cA wcel vy cv cB wcel wa vy cv cB wcel vx cv cA wcel wa
      vz cv cC wceq vx cv cA wcel vy cv cB wcel ancom anbi1i oprabbii 3eqtri
      tposoprab vy vx vz cB cA cC df-mpt2 eqtr4i $.
  $}


