
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Indexed_union_and_intersection.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Disjointness

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Disj_ $.

  $( Extend wff notation to include the statement that a family of classes
     ` B ( x ) ` , for ` x e. A ` , is a disjoint family. $)
  wdisj $a wff Disj_ x e. A B $.

  ${
    $d x y $.  $d y A $.  $d y B $.
    $( A collection of classes ` B ( x ) ` is disjoint when for each element
       ` y ` , it is in ` B ( x ) ` for at most one ` x ` .  (Contributed by
       Mario Carneiro, 14-Nov-2016.)  (Revised by NM, 16-Jun-2017.) $)
    df-disj $a |- ( Disj_ x e. A B <-> A. y E* x e. A y e. B ) $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    $( Alternate definition for disjoint classes.  (Contributed by NM,
       17-Jun-2017.) $)
    dfdisj2 $p |- ( Disj_ x e. A B <-> A. y E* x ( x e. A /\ y e. B ) ) $=
      vx cA cB wdisj vy cv cB wcel vx cA wrmo vy wal vx cv cA wcel vy cv cB
      wcel wa vx wmo vy wal vx vy cA cB df-disj vy cv cB wcel vx cA wrmo vx cv
      cA wcel vy cv cB wcel wa vx wmo vy vy cv cB wcel vx cA df-rmo albii bitri
      $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( If each element of a collection is contained in a disjoint collection,
       the original collection is also disjoint.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjss2 $p |- ( A. x e. A B C_ C ->
      ( Disj_ x e. A C -> Disj_ x e. A B ) ) $=
      cB cC wss vx cA wral vy cv cC wcel vx cA wrmo vy wal vy cv cB wcel vx cA
      wrmo vy wal vx cA cC wdisj vx cA cB wdisj cB cC wss vx cA wral vy cv cC
      wcel vx cA wrmo vy cv cB wcel vx cA wrmo vy cB cC wss vx cA wral vy cv cB
      wcel vy cv cC wcel wi vx cA wral vy cv cC wcel vx cA wrmo vy cv cB wcel
      vx cA wrmo wi cB cC wss vy cv cB wcel vy cv cC wcel wi vx cA cB cC vy cv
      ssel ralimi vy cv cB wcel vy cv cC wcel vx cA rmoim syl alimdv vx vy cA
      cC df-disj vx vy cA cB df-disj 3imtr4g $.
  $}

  $( Equality theorem for disjoint collection.  (Contributed by Mario Carneiro,
     14-Nov-2016.) $)
  disjeq2 $p |- ( A. x e. A B = C ->
    ( Disj_ x e. A B <-> Disj_ x e. A C ) ) $=
    cB cC wceq vx cA wral vx cA cB wdisj vx cA cC wdisj cB cC wceq vx cA wral
    cC cB wss vx cA wral vx cA cB wdisj vx cA cC wdisj wi cB cC wceq cC cB wss
    vx cA cC cB eqimss2 ralimi vx cA cC cB disjss2 syl cB cC wceq vx cA wral cB
    cC wss vx cA wral vx cA cC wdisj vx cA cB wdisj wi cB cC wceq cB cC wss vx
    cA cB cC eqimss ralimi vx cA cB cC disjss2 syl impbid $.

  ${
    $d x ph $.
    disjeq2dv.1 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
    $( Equality deduction for disjoint collection.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjeq2dv $p |- ( ph -> ( Disj_ x e. A B <-> Disj_ x e. A C ) ) $=
      wph cB cC wceq vx cA wral vx cA cB wdisj vx cA cC wdisj wb wph cB cC wceq
      vx cA disjeq2dv.1 ralrimiva vx cA cB cC disjeq2 syl $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.
    $( A subset of a disjoint collection is disjoint.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjss1 $p |- ( A C_ B -> ( Disj_ x e. B C -> Disj_ x e. A C ) ) $=
      cA cB wss vx cv cB wcel vy cv cC wcel wa vx wmo vy wal vx cv cA wcel vy
      cv cC wcel wa vx wmo vy wal vx cB cC wdisj vx cA cC wdisj cA cB wss vx cv
      cB wcel vy cv cC wcel wa vx wmo vx cv cA wcel vy cv cC wcel wa vx wmo vy
      cA cB wss vx cv cA wcel vy cv cC wcel wa vx cv cB wcel vy cv cC wcel wa
      wi vx wal vx cv cB wcel vy cv cC wcel wa vx wmo vx cv cA wcel vy cv cC
      wcel wa vx wmo wi cA cB wss vx cv cA wcel vy cv cC wcel wa vx cv cB wcel
      vy cv cC wcel wa wi vx cA cB wss vx cv cA wcel vx cv cB wcel vy cv cC
      wcel cA cB vx cv ssel anim1d alrimiv vx cv cA wcel vy cv cC wcel wa vx cv
      cB wcel vy cv cC wcel wa vx moim syl alimdv vx vy cB cC dfdisj2 vx vy cA
      cC dfdisj2 3imtr4g $.

    $( Equality theorem for disjoint collection.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjeq1 $p |- ( A = B -> ( Disj_ x e. A C <-> Disj_ x e. B C ) ) $=
      cA cB wceq vx cA cC wdisj vx cB cC wdisj cA cB wceq cB cA wss vx cA cC
      wdisj vx cB cC wdisj wi cB cA eqimss2 vx cB cA cC disjss1 syl cA cB wceq
      cA cB wss vx cB cC wdisj vx cA cC wdisj wi cA cB eqimss vx cA cB cC
      disjss1 syl impbid $.

    disjeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for disjoint collection.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjeq1d $p |- ( ph -> ( Disj_ x e. A C <-> Disj_ x e. B C ) ) $=
      wph cA cB wceq vx cA cC wdisj vx cB cC wdisj wb disjeq1d.1 vx cA cB cC
      disjeq1 syl $.

    $d x ph $.
    disjeq12d.1 $e |- ( ph -> C = D ) $.
    $( Equality theorem for disjoint collection.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    disjeq12d $p |- ( ph -> ( Disj_ x e. A C <-> Disj_ x e. B D ) ) $=
      wph vx cA cC wdisj vx cB cC wdisj vx cB cD wdisj wph vx cA cB cC
      disjeq1d.1 disjeq1d wph vx cB cC cD wph cC cD wceq vx cv cB wcel
      disjeq12d.1 adantr disjeq2dv bitrd $.
  $}

  ${
    $d x y z A $.  $d z B $.  $d z C $.
    cbvdisj.1 $e |- F/_ y B $.
    cbvdisj.2 $e |- F/_ x C $.
    cbvdisj.3 $e |- ( x = y -> B = C ) $.
    $( Change bound variables in a disjoint collection.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    cbvdisj $p |- ( Disj_ x e. A B <-> Disj_ y e. A C ) $=
      vz cv cB wcel vx cA wrmo vz wal vz cv cC wcel vy cA wrmo vz wal vx cA cB
      wdisj vy cA cC wdisj vz cv cB wcel vx cA wrmo vz cv cC wcel vy cA wrmo vz
      vz cv cB wcel vz cv cC wcel vx vy cA vy vz cB cbvdisj.1 nfcri vx vz cC
      cbvdisj.2 nfcri vx vy weq cB cC vz cv cbvdisj.3 eleq2d cbvrmo albii vx vz
      cA cB df-disj vy vz cA cC df-disj 3bitr4i $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x C $.
    cbvdisjv.1 $e |- ( x = y -> B = C ) $.
    $( Change bound variables in a disjoint collection.  (Contributed by Mario
       Carneiro, 11-Dec-2016.) $)
    cbvdisjv $p |- ( Disj_ x e. A B <-> Disj_ y e. A C ) $=
      vx vy cA cB cC vy cB nfcv vx cC nfcv cbvdisjv.1 cbvdisj $.
  $}

  ${
    $d z A $.  $d z B $.  $d x z $.  $d y z $.
    nfdisj.1 $e |- F/_ y A $.
    nfdisj.2 $e |- F/_ y B $.
    $( Bound-variable hypothesis builder for disjoint collection.  (Contributed
       by Mario Carneiro, 14-Nov-2016.) $)
    nfdisj $p |- F/ y Disj_ x e. A B $=
      vx cA cB wdisj vx cv cA wcel vz cv cB wcel wa vx wmo vz wal vy vx cA cB
      wdisj vz cv cB wcel vx cA wrmo vz wal vx cv cA wcel vz cv cB wcel wa vx
      wmo vz wal vx vz cA cB df-disj vz cv cB wcel vx cA wrmo vx cv cA wcel vz
      cv cB wcel wa vx wmo vz vz cv cB wcel vx cA df-rmo albii bitri vx cv cA
      wcel vz cv cB wcel wa vx wmo vy vz vx cv cA wcel vz cv cB wcel wa vx wmo
      vy wnf wtru vx cv cA wcel vz cv cB wcel wa vy vx vx nftru vy vx weq vy
      wal wn vx cv cA wcel vz cv cB wcel wa vy wnf wtru vy vx weq vy wal wn vx
      cv cA wcel vz cv cB wcel vy vy vx weq vy wal wn vy vx cv cA vy vx nfcvf
      vy cA wnfc vy vx weq vy wal wn nfdisj.1 a1i nfeld vz cv cB wcel vy wnf vy
      vx weq vy wal wn vy vz cB nfdisj.2 nfcri a1i nfand adantl nfmod2 trud
      nfal nfxfr $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( Bound-variable hypothesis builder for disjoint collection.  (Contributed
       by Mario Carneiro, 14-Nov-2016.) $)
    nfdisj1 $p |- F/ x Disj_ x e. A B $=
      vx cA cB wdisj vy cv cB wcel vx cA wrmo vy wal vx vx vy cA cB df-disj vy
      cv cB wcel vx cA wrmo vx vy vy cv cB wcel vx cA nfrmo1 nfal nfxfr $.
  $}

  ${
    $d i j x A $.  $d j x B $.  $d i x C $.
    disjmo.1 $e |- ( i = j -> B = C ) $.
    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Mario Carneiro, 26-Mar-2015.)  (Revised by
       Mario Carneiro, 14-Nov-2016.) $)
    disjor $p |- ( Disj_ i e. A B <->
      A. i e. A A. j e. A ( i = j \/ ( B i^i C ) = (/) ) ) $=
      vi cA cB wdisj vx cv cB wcel vi cA wrmo vx wal vi vj weq cB cC cin c0
      wceq wo vj cA wral vi cA wral vi vx cA cB df-disj vx cv cB wcel vx cv cC
      wcel wa vi vj weq wi vj cA wral vx wal vi cA wral vx cv cB wcel vx cv cC
      wcel wa vi vj weq wi vj cA wral vi cA wral vx wal vi vj weq cB cC cin c0
      wceq wo vj cA wral vi cA wral vx cv cB wcel vi cA wrmo vx wal vx cv cB
      wcel vx cv cC wcel wa vi vj weq wi vj cA wral vi vx cA ralcom4 vi vj weq
      cB cC cin c0 wceq wo vj cA wral vx cv cB wcel vx cv cC wcel wa vi vj weq
      wi vj cA wral vx wal vi cA vi vj weq cB cC cin c0 wceq wo vj cA wral vx
      cv cB wcel vx cv cC wcel wa vi vj weq wi vx wal vj cA wral vx cv cB wcel
      vx cv cC wcel wa vi vj weq wi vj cA wral vx wal vi vj weq cB cC cin c0
      wceq wo vx cv cB wcel vx cv cC wcel wa vi vj weq wi vx wal vj cA vi vj
      weq cB cC cin c0 wceq wo cB cC cin c0 wceq vi vj weq wo cB cC cin c0 wceq
      wn vi vj weq wi vx cv cB wcel vx cv cC wcel wa vi vj weq wi vx wal vi vj
      weq cB cC cin c0 wceq orcom cB cC cin c0 wceq vi vj weq df-or cB cC cin
      c0 wceq wn vi vj weq wi vx cv cB wcel vx cv cC wcel wa vx wex vi vj weq
      wi vx cv cB wcel vx cv cC wcel wa vi vj weq wi vx wal cB cC cin c0 wceq
      wn vx cv cB wcel vx cv cC wcel wa vx wex vi vj weq cB cC cin c0 wceq wn
      vx cv cB cC cin wcel vx wex vx cv cB wcel vx cv cC wcel wa vx wex vx cB
      cC cin neq0 vx cv cB cC cin wcel vx cv cB wcel vx cv cC wcel wa vx vx cv
      cB cC elin exbii bitri imbi1i vx cv cB wcel vx cv cC wcel wa vi vj weq vx
      19.23v bitr4i 3bitri ralbii vx cv cB wcel vx cv cC wcel wa vi vj weq wi
      vj vx cA ralcom4 bitri ralbii vx cv cB wcel vi cA wrmo vx cv cB wcel vx
      cv cC wcel wa vi vj weq wi vj cA wral vi cA wral vx vx cv cB wcel vx cv
      cC wcel vi vj cA vi vj weq cB cC vx cv disjmo.1 eleq2d rmo4 albii 3bitr4i
      bitr4i $.

    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Mario Carneiro, 26-Mar-2015.)
       (New usage is discouraged.) $)
    disjmoOLD $p |- ( A. x E* i ( i e. A /\ x e. B ) <->
      A. i e. A A. j e. A ( i = j \/ ( B i^i C ) = (/) ) ) $=
      vi cv cA wcel vx cv cB wcel wa vi wmo vx wal vi cA cB wdisj vi cv vj cv
      wceq cB cC cin c0 wceq wo vj cA wral vi cA wral vi vx cA cB dfdisj2 cA cB
      cC vi vj disjmo.1 disjor bitr3i $.
  $}

  ${
    $d i j x A $.  $d i j B $.
    $( Two ways to say that a collection ` B ( i ) ` for ` i e. A ` is
       disjoint.  (Contributed by Mario Carneiro, 14-Nov-2016.) $)
    disjors $p |- ( Disj_ x e. A B <-> A. i e. A A. j e. A
      ( i = j \/ ( [_ i / x ]_ B i^i [_ j / x ]_ B ) = (/) ) ) $=
      vx cA cB wdisj vi cA vx vi cv cB csb wdisj vi cv vj cv wceq vx vi cv cB
      csb vx vj cv cB csb cin c0 wceq wo vj cA wral vi cA wral vx vi cA cB vx
      vi cv cB csb vi cB nfcv vx vi cv cB nfcsb1v vx vi cv cB csbeq1a cbvdisj
      cA vx vi cv cB csb vx vj cv cB csb vi vj vx vi cv vj cv cB csbeq1 disjor
      bitri $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z C $.  $d x z D $.  $d x y z X $.
    $d x z Y $.
    disji.1 $e |- ( x = X -> B = C ) $.
    disji.2 $e |- ( x = Y -> B = D ) $.
    $( Property of a disjoint collection: if ` B ( X ) = C ` and
       ` B ( Y ) = D ` , and ` X =/= Y ` , then ` C ` and ` D ` are disjoint.
       (Contributed by Mario Carneiro, 14-Nov-2016.) $)
    disji2 $p |- ( ( Disj_ x e. A B /\ ( X e. A /\ Y e. A ) /\
      X =/= Y ) -> ( C i^i D ) = (/) ) $=
      vx cA cB wdisj cX cA wcel cY cA wcel wa cX cY wne cC cD cin c0 wceq cX cY
      wne cX cY wceq wn vx cA cB wdisj cX cA wcel cY cA wcel wa wa cC cD cin c0
      wceq cX cY df-ne vx cA cB wdisj cX cA wcel cY cA wcel wa wa cX cY wceq cC
      cD cin c0 wceq cX cA wcel cY cA wcel wa vx cA cB wdisj cX cY wceq cC cD
      cin c0 wceq wo vx cA cB wdisj vy cv vz cv wceq vx vy cv cB csb vx vz cv
      cB csb cin c0 wceq wo vz cA wral vy cA wral cX cA wcel cY cA wcel wa cX
      cY wceq cC cD cin c0 wceq wo vx cA cB vy vz disjors vy cv vz cv wceq vx
      vy cv cB csb vx vz cv cB csb cin c0 wceq wo cX cY wceq cC cD cin c0 wceq
      wo cX vz cv wceq cC vx vz cv cB csb cin c0 wceq wo vy vz cX cY cA cA vy
      cv cX wceq vy cv vz cv wceq cX vz cv wceq vx vy cv cB csb vx vz cv cB csb
      cin c0 wceq cC vx vz cv cB csb cin c0 wceq vy cv cX vz cv eqeq1 vy cv cX
      wceq vx vy cv cB csb vx vz cv cB csb cin cC vx vz cv cB csb cin c0 vy cv
      cX wceq vx vy cv cB csb cC vx vz cv cB csb vx vy cX cB cC vx cX nfcv vx
      cC nfcv disji.1 csbhypf ineq1d eqeq1d orbi12d vz cv cY wceq cX vz cv wceq
      cX cY wceq cC vx vz cv cB csb cin c0 wceq cC cD cin c0 wceq vz cv cY cX
      eqeq2 vz cv cY wceq cC vx vz cv cB csb cin cC cD cin c0 vz cv cY wceq vx
      vz cv cB csb cD cC vx vz cY cB cD vx cY nfcv vx cD nfcv disji.2 csbhypf
      ineq2d eqeq1d orbi12d rspc2v syl5bi impcom ord syl5bi 3impia $.

    $( Property of a disjoint collection: if ` B ( X ) = C ` and
       ` B ( Y ) = D ` have a common element ` Z ` , then ` X = Y ` .
       (Contributed by Mario Carneiro, 14-Nov-2016.) $)
    disji $p |- ( ( Disj_ x e. A B /\ ( X e. A /\ Y e. A ) /\
      ( Z e. C /\ Z e. D ) ) -> X = Y ) $=
      cZ cC wcel cZ cD wcel wa vx cA cB wdisj cX cA wcel cY cA wcel wa cC cD
      cin c0 wne cX cY wceq cZ cC cD inelcm vx cA cB wdisj cX cA wcel cY cA
      wcel wa cC cD cin c0 wne cX cY wceq vx cA cB wdisj cX cA wcel cY cA wcel
      wa wa cX cY cC cD cin c0 vx cA cB wdisj cX cA wcel cY cA wcel wa cX cY
      wne cC cD cin c0 wceq vx cA cB cC cD cX cY disji.1 disji.2 disji2 3expia
      necon1d 3impia syl3an3 $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d x C $.
    $( If there is a function ` C ( y ) ` such that ` C ( y ) = x ` for all
       ` y e. B ( x ) ` , then the sets ` B ( x ) ` for distinct ` x e. A ` are
       disjoint.  (Contributed by Mario Carneiro, 10-Dec-2016.) $)
    invdisj $p |- ( A. x e. A A. y e. B C = x -> Disj_ x e. A B ) $=
      cC vx cv wceq vy cB wral vx cA wral vx cv cA wcel vy cv cB wcel wa vx wmo
      vy wal vx cA cB wdisj cC vx cv wceq vy cB wral vx cA wral vx cv cA wcel
      vy cv cB wcel wa vx wmo vy cC vx cv wceq vx vy cA cB nfra2 cC vx cv wceq
      vy cB wral vx cA wral vx cv cA wcel vy cv cB wcel wa vx cv cC wceq wi vx
      wal vx cv cA wcel vy cv cB wcel wa vx wmo cC vx cv wceq vy cB wral vx cA
      wral vx cv cA wcel cC vx cv wceq vy cB wral wi vx wal vx cv cA wcel vy cv
      cB wcel wa vx cv cC wceq wi vx wal cC vx cv wceq vy cB wral vx cA df-ral
      vx cv cA wcel cC vx cv wceq vy cB wral wi vx cv cA wcel vy cv cB wcel wa
      vx cv cC wceq wi vx vx cv cA wcel cC vx cv wceq vy cB wral wi vx cv cA
      wcel vy cv cB wcel vx cv cC wceq cC vx cv wceq vy cB wral vy cv cB wcel
      vx cv cC wceq wi vx cv cA wcel cC vx cv wceq vy cB wral vy cv cB wcel cC
      vx cv wceq vx cv cC wceq cC vx cv wceq vy cB rsp cC vx cv eqcom syl6ib
      imim2i imp3a alimi sylbi vx cv cA wcel vy cv cB wcel wa vx cC mo2icl syl
      alrimi vx cA cB wdisj vy cv cB wcel vx cA wrmo vy wal vx cv cA wcel vy cv
      cB wcel wa vx wmo vy wal vx vy cA cB df-disj vy cv cB wcel vx cA wrmo vx
      cv cA wcel vy cv cB wcel wa vx wmo vy vy cv cB wcel vx cA df-rmo albii
      bitri sylibr $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z C $.  $d x y z D $.
    $( A disjoint collection yields disjoint indexed unions for disjoint index
       sets.  (Contributed by Mario Carneiro, 26-Mar-2015.)  (Revised by Mario
       Carneiro, 14-Nov-2016.) $)
    disjiun $p |- ( ( Disj_ x e. A B /\
      ( C C_ A /\ D C_ A /\ ( C i^i D ) = (/) ) ) ->
        ( U_ x e. C B i^i U_ x e. D B ) = (/) ) $=
      vx cA cB wdisj cC cA wss cD cA wss cC cD cin c0 wceq w3a wa vy cv vx cC
      cB ciun vx cD cB ciun cin wcel wn vy wal vx cC cB ciun vx cD cB ciun cin
      c0 wceq cC cA wss cD cA wss cC cD cin c0 wceq w3a vx cA cB wdisj vy cv vx
      cC cB ciun vx cD cB ciun cin wcel wn vy wal vx cA cB wdisj vy cv cB wcel
      vx cA wrmo vy wal cC cA wss cD cA wss cC cD cin c0 wceq w3a vy cv vx cC
      cB ciun vx cD cB ciun cin wcel wn vy wal vx vy cA cB df-disj cC cA wss cD
      cA wss cC cD cin c0 wceq w3a vy cv cB wcel vx cA wrmo vy cv vx cC cB ciun
      vx cD cB ciun cin wcel wn vy cC cA wss cD cA wss cC cD cin c0 wceq vy cv
      cB wcel vx cA wrmo vy cv vx cC cB ciun vx cD cB ciun cin wcel wn wi cC cA
      wss cD cA wss wa vy cv cB wcel vx cA wrmo cC cD cin c0 wceq vy cv vx cC
      cB ciun vx cD cB ciun cin wcel wn cC cA wss cD cA wss wa vy cv cB wcel vx
      cA wrmo wa vy cv vx cC cB ciun vx cD cB ciun cin wcel cC cD cin c0 vy cv
      vx cC cB ciun vx cD cB ciun cin wcel vy cv cB wcel vx cC wrex vy cv cB
      wcel vx cD wrex wa cC cA wss cD cA wss wa vy cv cB wcel vx cA wrmo wa cC
      cD cin c0 wne vy cv vx cC cB ciun vx cD cB ciun cin wcel vy cv vx cC cB
      ciun wcel vy cv vx cD cB ciun wcel wa vy cv cB wcel vx cC wrex vy cv cB
      wcel vx cD wrex wa vy cv vx cC cB ciun vx cD cB ciun elin vy cv vx cC cB
      ciun wcel vy cv cB wcel vx cC wrex vy cv vx cD cB ciun wcel vy cv cB wcel
      vx cD wrex vx vy cv cC cB eliun vx vy cv cD cB eliun anbi12i bitri vy cv
      cB wcel vx cA wrmo cC cA wss cD cA wss wa vy cv cB wcel vx cC wrex vy cv
      cB wcel vx cD wrex wa cC cD cin c0 wne wi vy cv cB wcel vx cA wrmo vy cv
      cB wcel vx vz weq wi vx cA wral vz wex cC cA wss cD cA wss wa vy cv cB
      wcel vx cC wrex vy cv cB wcel vx cD wrex wa cC cD cin c0 wne wi wi vy cv
      cB wcel vx vz cA vy cv cB wcel vz nfv rmo2 vy cv cB wcel vx vz weq wi vx
      cA wral vz wex cC cA wss cD cA wss wa vy cv cB wcel vx cC wrex vy cv cB
      wcel vx cD wrex wa cC cD cin c0 wne cC cA wss cD cA wss wa vy cv cB wcel
      vx cC wrex vy cv cB wcel vx cD wrex wa wa cC cA wss vy cv cB wcel vx cC
      wrex wa cD cA wss vy cv cB wcel vx cD wrex wa wa vy cv cB wcel vx vz weq
      wi vx cA wral vz wex cC cD cin c0 wne cC cA wss cD cA wss vy cv cB wcel
      vx cC wrex vy cv cB wcel vx cD wrex an4 vy cv cB wcel vx vz weq wi vx cA
      wral cC cA wss vy cv cB wcel vx cC wrex wa cD cA wss vy cv cB wcel vx cD
      wrex wa wa cC cD cin c0 wne wi vz vy cv cB wcel vx vz weq wi vx cA wral
      cC cA wss vy cv cB wcel vx cC wrex wa cD cA wss vy cv cB wcel vx cD wrex
      wa wa vz cv cC wcel vz cv cD wcel wa cC cD cin c0 wne vy cv cB wcel vx vz
      weq wi vx cA wral cC cA wss vy cv cB wcel vx cC wrex wa vz cv cC wcel cD
      cA wss vy cv cB wcel vx cD wrex wa vz cv cD wcel vy cv cB wcel vx vz weq
      wi vx cA wral cC cA wss vy cv cB wcel vx cC wrex vz cv cC wcel vy cv cB
      wcel vx vz weq wi vx cA wral cC cA wss wa vy cv cB wcel vx vz weq wi vx
      cC wral vy cv cB wcel vx cC wrex vz cv cC wcel wi cC cA wss vy cv cB wcel
      vx vz weq wi vx cA wral vy cv cB wcel vx vz weq wi vx cC wral vy cv cB
      wcel vx vz weq wi vx cC cA ssralv impcom vy cv cB wcel vx vz weq wi vx cC
      wral vy cv cB wcel vx cC wrex vz cv cC wcel vy cv cB wcel vx vz weq wi vx
      cC wral vy cv cB wcel vx cC wrex wa vy cv cB wcel vx vz weq wi vy cv cB
      wcel wa vx cC wrex vz cv cC wcel vy cv cB wcel vx vz weq wi vy cv cB wcel
      vx cC r19.29 vy cv cB wcel vx vz weq wi vy cv cB wcel wa vz cv cC wcel vx
      cC vy cv cB wcel vx vz weq wi vy cv cB wcel wa vx cv cC wcel vz cv cC
      wcel vy cv cB wcel vx vz weq wi vy cv cB wcel wa vx cv vz cv cC vy cv cB
      wcel vx vz weq wi vy cv cB wcel vx vz weq vy cv cB wcel vx vz weq wi id
      imp eleq1d biimpcd rexlimiv syl ex syl expimpd vy cv cB wcel vx vz weq wi
      vx cA wral cD cA wss vy cv cB wcel vx cD wrex vz cv cD wcel vy cv cB wcel
      vx vz weq wi vx cA wral cD cA wss wa vy cv cB wcel vx vz weq wi vx cD
      wral vy cv cB wcel vx cD wrex vz cv cD wcel wi cD cA wss vy cv cB wcel vx
      vz weq wi vx cA wral vy cv cB wcel vx vz weq wi vx cD wral vy cv cB wcel
      vx vz weq wi vx cD cA ssralv impcom vy cv cB wcel vx vz weq wi vx cD wral
      vy cv cB wcel vx cD wrex vz cv cD wcel vy cv cB wcel vx vz weq wi vx cD
      wral vy cv cB wcel vx cD wrex wa vy cv cB wcel vx vz weq wi vy cv cB wcel
      wa vx cD wrex vz cv cD wcel vy cv cB wcel vx vz weq wi vy cv cB wcel vx
      cD r19.29 vy cv cB wcel vx vz weq wi vy cv cB wcel wa vz cv cD wcel vx cD
      vy cv cB wcel vx vz weq wi vy cv cB wcel wa vx cv cD wcel vz cv cD wcel
      vy cv cB wcel vx vz weq wi vy cv cB wcel wa vx cv vz cv cD vy cv cB wcel
      vx vz weq wi vy cv cB wcel vx vz weq vy cv cB wcel vx vz weq wi id imp
      eleq1d biimpcd rexlimiv syl ex syl expimpd anim12d vz cv cC cD inelcm
      syl6 exlimiv syl5bi exp3a sylbi impcom syl5bi necon2bd impancom 3impa
      alimdv syl5bi impcom vy vx cC cB ciun vx cD cB ciun cin eq0 sylibr $.

    $( A disjoint collection yields disjoint indexed unions for disjoint index
       sets.  (Contributed by Mario Carneiro, 26-Mar-2015.)
       (New usage is discouraged.) $)
    disjiunOLD $p |- ( ( A. y E* x ( x e. A /\ y e. B ) /\
      ( C C_ A /\ D C_ A /\ ( C i^i D ) = (/) ) ) ->
        ( U_ x e. C B i^i U_ x e. D B ) = (/) ) $=
      vx cv cA wcel vy cv cB wcel wa vx wmo vy wal vx cA cB wdisj cC cA wss cD
      cA wss cC cD cin c0 wceq w3a vx cC cB ciun vx cD cB ciun cin c0 wceq vx
      vy cA cB dfdisj2 vx cA cB cC cD disjiun sylanbr $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Any collection of singletons is disjoint.  (Contributed by Mario
       Carneiro, 14-Nov-2016.) $)
    sndisj $p |- Disj_ x e. A { x } $=
      vx cA vx cv csn wdisj vx cv cA wcel vy cv vx cv csn wcel wa vx wmo vy vx
      vy cA vx cv csn dfdisj2 vx cv vy cv wceq vx wmo vx cv cA wcel vy cv vx cv
      csn wcel wa vx wmo vx vy cv moeq vx cv cA wcel vy cv vx cv csn wcel wa vx
      cv vy cv wceq vx vx cv cA wcel vy cv vx cv csn wcel wa vy cv vx cv vx cv
      cA wcel vy cv vx cv csn wcel wa vy cv vx cv csn wcel vy cv vx cv wceq vx
      cv cA wcel vy cv vx cv csn wcel simpr vy vx cv elsn sylib eqcomd moimi
      ax-mp mpgbir $.
  $}

  $( Any collection of empty sets is disjoint.  (Contributed by Mario Carneiro,
     14-Nov-2016.) $)
  0disj $p |- Disj_ x e. A (/) $=
    c0 vx cv csn wss vx cA wral vx cA vx cv csn wdisj vx cA c0 wdisj c0 vx cv
    csn wss vx cA vx cv csn 0ss rgenw vx cA sndisj vx cA c0 vx cv csn disjss2
    mp2 $.

  ${
    $d x y A $.  $d y B $.
    $( A singleton collection is disjoint.  (Contributed by Mario Carneiro,
       14-Nov-2016.) $)
    disjxsn $p |- Disj_ x e. { A } B $=
      vx cA csn cB wdisj vx cv cA csn wcel vy cv cB wcel wa vx wmo vy vx vy cA
      csn cB dfdisj2 vx cv cA wceq vx wmo vx cv cA csn wcel vy cv cB wcel wa vx
      wmo vx cA moeq vx cv cA csn wcel vy cv cB wcel wa vx cv cA wceq vx vx cv
      cA csn wcel vx cv cA wceq vy cv cB wcel vx cv cA elsni adantr moimi ax-mp
      mpgbir $.

    $( An empty collection is disjoint.  (Contributed by Mario Carneiro,
       14-Nov-2016.) $)
    disjx0 $p |- Disj_ x e. (/) B $=
      c0 c0 csn wss vx c0 csn cB wdisj vx c0 cB wdisj c0 csn 0ss vx c0 cB
      disjxsn vx c0 c0 csn cB disjss1 mp2 $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d y z C $.  $d x y z D $.  $d x y z E $.
    disjprg.1 $e |- ( x = A -> C = D ) $.
    disjprg.2 $e |- ( x = B -> C = E ) $.
    $( A pair collection is disjoint iff the two sets in the family have empty
       intersection.  (Contributed by Mario Carneiro, 14-Nov-2016.) $)
    disjprg $p |- ( ( A e. V /\ B e. V /\ A =/= B ) ->
      ( Disj_ x e. { A , B } C <-> ( D i^i E ) = (/) ) ) $=
      cA cV wcel cB cV wcel cA cB wne w3a vy cv vz cv wceq vx vy cv cC csb vx
      vz cv cC csb cin c0 wceq wo vz cA cB cpr wral vy cA cB cpr wral cD cE cin
      c0 wceq cD cE cin c0 wceq wa vx cA cB cpr cC wdisj cD cE cin c0 wceq cA
      cV wcel cB cV wcel cA cB wne w3a vy cv vz cv wceq vx vy cv cC csb vx vz
      cv cC csb cin c0 wceq wo vz cA cB cpr wral vy cA cB cpr wral cA vz cv
      wceq cD vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral cB vz cv wceq cE
      vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral wa cD cE cin c0 wceq cD
      cE cin c0 wceq wa cA cV wcel cB cV wcel vy cv vz cv wceq vx vy cv cC csb
      vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral vy cA cB cpr wral cA vz
      cv wceq cD vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral cB vz cv wceq
      cE vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral wa wb cA cB wne vy cv
      vz cv wceq vx vy cv cC csb vx vz cv cC csb cin c0 wceq wo vz cA cB cpr
      wral cA vz cv wceq cD vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral cB
      vz cv wceq cE vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral vy cA cB
      cV cV vy cv cA wceq vy cv vz cv wceq vx vy cv cC csb vx vz cv cC csb cin
      c0 wceq wo cA vz cv wceq cD vx vz cv cC csb cin c0 wceq wo vz cA cB cpr
      vy cv cA wceq vy cv vz cv wceq cA vz cv wceq vx vy cv cC csb vx vz cv cC
      csb cin c0 wceq cD vx vz cv cC csb cin c0 wceq vy cv cA vz cv eqeq1 vy cv
      cA wceq vx vy cv cC csb vx vz cv cC csb cin cD vx vz cv cC csb cin c0 vy
      cv cA wceq vx vy cv cC csb cD vx vz cv cC csb vx vy cA cC cD vx cA nfcv
      vx cD nfcv disjprg.1 csbhypf ineq1d eqeq1d orbi12d ralbidv vy cv cB wceq
      vy cv vz cv wceq vx vy cv cC csb vx vz cv cC csb cin c0 wceq wo cB vz cv
      wceq cE vx vz cv cC csb cin c0 wceq wo vz cA cB cpr vy cv cB wceq vy cv
      vz cv wceq cB vz cv wceq vx vy cv cC csb vx vz cv cC csb cin c0 wceq cE
      vx vz cv cC csb cin c0 wceq vy cv cB vz cv eqeq1 vy cv cB wceq vx vy cv
      cC csb vx vz cv cC csb cin cE vx vz cv cC csb cin c0 vy cv cB wceq vx vy
      cv cC csb cE vx vz cv cC csb vx vy cB cC cE vx cB nfcv vx cE nfcv
      disjprg.2 csbhypf ineq1d eqeq1d orbi12d ralbidv ralprg 3adant3 cA cV wcel
      cB cV wcel cA cB wne w3a cA vz cv wceq cD vx vz cv cC csb cin c0 wceq wo
      vz cA cB cpr wral cD cE cin c0 wceq cB vz cv wceq cE vx vz cv cC csb cin
      c0 wceq wo vz cA cB cpr wral cD cE cin c0 wceq cA cV wcel cB cV wcel cA
      cB wne w3a cA vz cv wceq cD vx vz cv cC csb cin c0 wceq wo vz cA cB cpr
      wral wtru cA cB wceq cD cE cin c0 wceq wo wa cD cE cin c0 wceq cA cV wcel
      cB cV wcel cA vz cv wceq cD vx vz cv cC csb cin c0 wceq wo vz cA cB cpr
      wral wtru cA cB wceq cD cE cin c0 wceq wo wa wb cA cB wne cA vz cv wceq
      cD vx vz cv cC csb cin c0 wceq wo wtru cA cB wceq cD cE cin c0 wceq wo vz
      cA cB cV cV vz cv cA wceq cA vz cv wceq cD vx vz cv cC csb cin c0 wceq wo
      wtru vz cv cA wceq cA vz cv wceq cD vx vz cv cC csb cin c0 wceq vz cv cA
      wceq vz cv cA vz cv cA wceq id eqcomd orcd vz cv cA wceq a1tru 2thd vz cv
      cB wceq cA vz cv wceq cA cB wceq cD vx vz cv cC csb cin c0 wceq cD cE cin
      c0 wceq vz cv cB cA eqeq2 vz cv cB wceq cD vx vz cv cC csb cin cD cE cin
      c0 vz cv cB wceq vx vz cv cC csb cE cD vx vz cB cC cE vx cB nfcv vx cE
      nfcv disjprg.2 csbhypf ineq2d eqeq1d orbi12d ralprg 3adant3 cA cV wcel cB
      cV wcel cA cB wne w3a cD cE cin c0 wceq cA cB wceq cD cE cin c0 wceq wo
      wtru cA cB wceq cD cE cin c0 wceq wo wa cA cV wcel cB cV wcel cA cB wne
      w3a cA cB wceq wn cD cE cin c0 wceq cA cB wceq cD cE cin c0 wceq wo wb cA
      cV wcel cB cV wcel cA cB wne w3a cA cB cA cV wcel cB cV wcel cA cB wne
      simp3 neneqd cA cB wceq cD cE cin c0 wceq biorf syl wtru cA cB wceq cD cE
      cin c0 wceq wo tru biantrur syl6bb bitr4d cA cV wcel cB cV wcel cA cB wne
      w3a cB vz cv wceq cE vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral cA
      cB wceq cD cE cin c0 wceq wo wtru wa cD cE cin c0 wceq cA cV wcel cB cV
      wcel cB vz cv wceq cE vx vz cv cC csb cin c0 wceq wo vz cA cB cpr wral cA
      cB wceq cD cE cin c0 wceq wo wtru wa wb cA cB wne cB vz cv wceq cE vx vz
      cv cC csb cin c0 wceq wo cA cB wceq cD cE cin c0 wceq wo wtru vz cA cB cV
      cV vz cv cA wceq cB vz cv wceq cA cB wceq cE vx vz cv cC csb cin c0 wceq
      cD cE cin c0 wceq vz cv cA wceq cB vz cv wceq cB cA wceq cA cB wceq vz cv
      cA cB eqeq2 cB cA eqcom syl6bb vz cv cA wceq cE vx vz cv cC csb cin cD cE
      cin c0 vz cv cA wceq cE vx vz cv cC csb cin cE cD cin cD cE cin vz cv cA
      wceq vx vz cv cC csb cD cE vx vz cA cC cD vx cA nfcv vx cD nfcv disjprg.1
      csbhypf ineq2d cE cD incom syl6eq eqeq1d orbi12d vz cv cB wceq cB vz cv
      wceq cE vx vz cv cC csb cin c0 wceq wo wtru vz cv cB wceq cB vz cv wceq
      cE vx vz cv cC csb cin c0 wceq vz cv cB wceq vz cv cB vz cv cB wceq id
      eqcomd orcd vz cv cB wceq a1tru 2thd ralprg 3adant3 cA cV wcel cB cV wcel
      cA cB wne w3a cD cE cin c0 wceq cA cB wceq cD cE cin c0 wceq wo cA cB
      wceq cD cE cin c0 wceq wo wtru wa cA cV wcel cB cV wcel cA cB wne w3a cA
      cB wceq wn cD cE cin c0 wceq cA cB wceq cD cE cin c0 wceq wo wb cA cV
      wcel cB cV wcel cA cB wne w3a cA cB cA cV wcel cB cV wcel cA cB wne simp3
      neneqd cA cB wceq cD cE cin c0 wceq biorf syl wtru cA cB wceq cD cE cin
      c0 wceq wo tru biantru syl6bb bitr4d anbi12d bitrd vx cA cB cpr cC vy vz
      disjors cD cE cin c0 wceq pm4.24 3bitr4g $.
  $}

  ${
    $d r s u v x y z A $.  $d r s u v x z B $.  $d r s u v y z C $.
    $( An indexed union of a disjoint collection of disjoint collections is
       disjoint if each component is disjoint, and the disjoint unions in the
       collection are also disjoint.  Note that ` B ( y ) ` and ` C ( x ) ` may
       have the displayed free variables.  (Contributed by Mario Carneiro,
       14-Nov-2016.) $)
    disjxiun $p |- ( Disj_ y e. A B -> ( Disj_ x e. U_ y e. A B C <->
      ( A. y e. A Disj_ x e. B C /\ Disj_ y e. A U_ x e. B C ) ) ) $=
      vy cA cB wdisj vx vy cA cB ciun cC wdisj vx cB cC wdisj vy cA wral vy cA
      vx cB cC ciun wdisj wa vy cA cB wdisj vx vy cA cB ciun cC wdisj vx cB cC
      wdisj vy cA wral vy cA vx cB cC ciun wdisj vx vy cA cB ciun cC wdisj vx
      cB cC wdisj vy cA wral wi vy cA cB wdisj vx vy cA cB ciun cC wdisj vx cB
      cC wdisj vy cA vx vy vy cA cB ciun cC vy cA cB nfiu1 vy cC nfcv nfdisj vy
      cv cA wcel vx vy cA cB ciun cC wdisj vx cB cC wdisj vy cv cA wcel cB vy
      cA cB ciun wss vx vy cA cB ciun cC wdisj vx cB cC wdisj wi vy cA cB
      ssiun2 vx cB vy cA cB ciun cC disjss1 syl com12 ralrimi a1i vy cA cB
      wdisj vx vy cA cB ciun cC wdisj vy cA vx cB cC ciun wdisj vy cA cB wdisj
      vx vy cA cB ciun cC wdisj wa vu cA vx vy vu cv cB csb cC ciun wdisj vy cA
      vx cB cC ciun wdisj vy cA cB wdisj vx vy cA cB ciun cC wdisj wa vu cv vv
      cv wceq vx vy vu cv cB csb cC ciun vx vy vv cv cB csb cC ciun cin c0 wceq
      wo vv cA wral vu cA wral vu cA vx vy vu cv cB csb cC ciun wdisj vy cA cB
      wdisj vx vy cA cB ciun cC wdisj wa vu cv vv cv wceq vx vy vu cv cB csb cC
      ciun vx vy vv cv cB csb cC ciun cin c0 wceq wo vu vv cA cA vy cA cB wdisj
      vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA wcel wa wa vu cv vv
      cv wceq vx vy vu cv cB csb cC ciun vx vy vv cv cB csb cC ciun cin c0 wceq
      vy cA cB wdisj vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA wcel
      wa vu cv vv cv wceq wn vx vy vu cv cB csb cC ciun vx vy vv cv cB csb cC
      ciun cin c0 wceq vy cA cB wdisj vx vy cA cB ciun cC wdisj wa vu cv cA
      wcel vv cv cA wcel wa vu cv vv cv wceq wn wa wa vx vy cA cB ciun cC wdisj
      vy vu cv cB csb vy cA cB ciun wss vy vv cv cB csb vy cA cB ciun wss vy vu
      cv cB csb vy vv cv cB csb cin c0 wceq vx vy vu cv cB csb cC ciun vx vy vv
      cv cB csb cC ciun cin c0 wceq vy cA cB wdisj vx vy cA cB ciun cC wdisj vu
      cv cA wcel vv cv cA wcel wa vu cv vv cv wceq wn wa simplr vy cA cB wdisj
      vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA wcel wa vu cv vv cv
      wceq wn wa wa vu cv cA wcel vy vu cv cB csb vy cA cB ciun wss vy cA cB
      wdisj vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA wcel vu cv vv
      cv wceq wn simprll vu cv cA wcel vy vu cv cB csb vu cA vy vu cv cB csb
      ciun vy cA cB ciun vu cA vy vu cv cB csb ssiun2 vy vu cA cB vy vu cv cB
      csb vu cB nfcv vy vu cv cB nfcsb1v vy vu cv cB csbeq1a cbviun syl6sseqr
      syl vy cA cB wdisj vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA
      wcel wa vu cv vv cv wceq wn wa wa vv cv cA wcel vy vv cv cB csb vy cA cB
      ciun wss vy cA cB wdisj vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv
      cA wcel vu cv vv cv wceq wn simprlr vy vu cv cB csb vy cA cB ciun wss vy
      vv cv cB csb vy cA cB ciun wss vu vv cv cA vu cv vv cv wceq vy vu cv cB
      csb vy vv cv cB csb vy cA cB ciun vy vu cv vv cv cB csbeq1 sseq1d vu cv
      cA wcel vy vu cv cB csb vu cA vy vu cv cB csb ciun vy cA cB ciun vu cA vy
      vu cv cB csb ssiun2 vy vu cA cB vy vu cv cB csb vu cB nfcv vy vu cv cB
      nfcsb1v vy vu cv cB csbeq1a cbviun syl6sseqr vtoclga syl vy cA cB wdisj
      vx vy cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA wcel wa vu cv vv cv
      wceq wn vy vu cv cB csb vy vv cv cB csb cin c0 wceq vy cA cB wdisj vx vy
      cA cB ciun cC wdisj wa vu cv cA wcel vv cv cA wcel wa wa vu cv vv cv wceq
      vy vu cv cB csb vy vv cv cB csb cin c0 wceq vy cA cB wdisj vx vy cA cB
      ciun cC wdisj wa vu cv cA wcel vv cv cA wcel wa vu cv vv cv wceq vy vu cv
      cB csb vy vv cv cB csb cin c0 wceq wo vy cA cB wdisj vx vy cA cB ciun cC
      wdisj wa vu cv vv cv wceq vy vu cv cB csb vy vv cv cB csb cin c0 wceq wo
      vv cA wral vu cA wral vu cv cA wcel vv cv cA wcel wa vu cv vv cv wceq vy
      vu cv cB csb vy vv cv cB csb cin c0 wceq wo wi vy cA cB wdisj vx vy cA cB
      ciun cC wdisj wa vu cA vy vu cv cB csb wdisj vu cv vv cv wceq vy vu cv cB
      csb vy vv cv cB csb cin c0 wceq wo vv cA wral vu cA wral vy cA cB wdisj
      vx vy cA cB ciun cC wdisj wa vy cA cB wdisj vu cA vy vu cv cB csb wdisj
      vy cA cB wdisj vx vy cA cB ciun cC wdisj simpl vy vu cA cB vy vu cv cB
      csb vu cB nfcv vy vu cv cB nfcsb1v vy vu cv cB csbeq1a cbvdisj sylib cA
      vy vu cv cB csb vy vv cv cB csb vu vv vy vu cv vv cv cB csbeq1 disjor
      sylib vu cv vv cv wceq vy vu cv cB csb vy vv cv cB csb cin c0 wceq wo vu
      vv cA cA rsp2 syl imp ord impr vx vy cA cB ciun cC vy vu cv cB csb vy vv
      cv cB csb disjiun syl13anc expr orrd ralrimivva cA vx vy vu cv cB csb cC
      ciun vx vy vv cv cB csb cC ciun vu vv vu cv vv cv wceq vx vy vu cv cB csb
      vy vv cv cB csb cC vy vu cv vv cv cB csbeq1 iuneq1d disjor sylibr vy vu
      cA vx cB cC ciun vx vy vu cv cB csb cC ciun vu vx cB cC ciun nfcv vx vy
      vy vu cv cB csb cC vy vu cv cB nfcsb1v vy cC nfcv nfiun vy cv vu cv wceq
      vx cB vy vu cv cB csb cC vy vu cv cB csbeq1a iuneq1d cbvdisj sylibr ex
      jcad vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj
      wa vx vy cA cB ciun cC wdisj vy cA cB wdisj vx cB cC wdisj vy cA wral vy
      cA vx cB cC ciun wdisj wa wa vr cv vs cv wceq vx vr cv cC csb vx vs cv cC
      csb cin c0 wceq wo vs vy cA cB ciun wral vr vy cA cB ciun wral vx vy cA
      cB ciun cC wdisj vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC
      ciun wdisj wa wa vr cv vs cv wceq vx vr cv cC csb vx vs cv cC csb cin c0
      wceq wo vr vs vy cA cB ciun vy cA cB ciun vr cv vy cA cB ciun wcel vs cv
      vy cA cB ciun wcel wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb
      wcel wa vv cA wrex vu cA wrex vy cA cB wdisj vx cB cC wdisj vy cA wral vy
      cA vx cB cC ciun wdisj wa wa vr cv vs cv wceq vx vr cv cC csb vx vs cv cC
      csb cin c0 wceq wo vr cv vy cA cB ciun wcel vs cv vy cA cB ciun wcel wa
      vr cv vy vu cv cB csb wcel vu cA wrex vs cv vy vv cv cB csb wcel vv cA
      wrex wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vv cA
      wrex vu cA wrex vr cv vy cA cB ciun wcel vr cv vy vu cv cB csb wcel vu cA
      wrex vs cv vy cA cB ciun wcel vs cv vy vv cv cB csb wcel vv cA wrex vr cv
      vy cA cB ciun wcel vr cv vu cA vy vu cv cB csb ciun wcel vr cv vy vu cv
      cB csb wcel vu cA wrex vy cA cB ciun vu cA vy vu cv cB csb ciun vr cv vy
      vu cA cB vy vu cv cB csb vu cB nfcv vy vu cv cB nfcsb1v vy vu cv cB
      csbeq1a cbviun eleq2i vu vr cv cA vy vu cv cB csb eliun bitri vs cv vy cA
      cB ciun wcel vs cv vv cA vy vv cv cB csb ciun wcel vs cv vy vv cv cB csb
      wcel vv cA wrex vy cA cB ciun vv cA vy vv cv cB csb ciun vs cv vy vv cA
      cB vy vv cv cB csb vv cB nfcv vy vv cv cB nfcsb1v vy vv cv cB csbeq1a
      cbviun eleq2i vv vs cv cA vy vv cv cB csb eliun bitri anbi12i vr cv vy vu
      cv cB csb wcel vs cv vy vv cv cB csb wcel vu vv cA cA reeanv bitr4i vy cA
      cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vr cv
      vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq vx vr
      cv cC csb vx vs cv cC csb cin c0 wceq wo vu vv cA cA vy cA cB wdisj vx cB
      cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv
      cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr
      cv vs cv wceq vx vr cv cC csb vx vs cv cC csb cin c0 wceq wo vy cA cB
      wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA
      wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb
      wcel wa wa vr cv vs cv wceq vx vr cv cC csb vx vs cv cC csb cin c0 wceq
      vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa
      vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv
      cv cB csb wcel wa vr cv vs cv wceq wn vx vr cv cC csb vx vs cv cC csb cin
      c0 wceq vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun
      wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel
      vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vx vr cv cC csb
      vx vs cv cC csb cin c0 wceq vu cv vv cv vy cA cB wdisj vx cB cC wdisj vy
      cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa
      vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq
      wn wa wa vu cv vv cv wceq wa vr cv vs cv wceq wn vx vr cv cC csb vx vs cv
      cC csb cin c0 wceq vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB
      cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB
      csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn vu cv vv cv
      wceq simplrr vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun
      wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel
      vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv wceq
      wa vr cv vs cv wceq vx vr cv cC csb vx vs cv cC csb cin c0 wceq vy cA cB
      wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA
      wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb
      wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv wceq wa vr cv vs cv wceq vx
      vr cv cC csb vx vs cv cC csb cin c0 wceq wo vs vy vu cv cB csb wral vr vy
      vu cv cB csb wral vr cv vy vu cv cB csb wcel vs cv vy vu cv cB csb wcel
      wa vr cv vs cv wceq vx vr cv cC csb vx vs cv cC csb cin c0 wceq wo vy cA
      cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv
      cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB
      csb wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv wceq wa vx vy vu cv cB
      csb cC wdisj vr cv vs cv wceq vx vr cv cC csb vx vs cv cC csb cin c0 wceq
      wo vs vy vu cv cB csb wral vr vy vu cv cB csb wral vy cA cB wdisj vx cB
      cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv
      cA wcel wa wa vx vy vu cv cB csb cC wdisj vr cv vy vu cv cB csb wcel vs
      cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa vu cv vv cv wceq vy cA
      cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv
      cA wcel vv cv cA wcel wa wa vu cv cA wcel vx cB cC wdisj vy cA wral vx vy
      vu cv cB csb cC wdisj vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx
      cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel simprl vy cA cB wdisj
      vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj vu cv cA wcel vv cv
      cA wcel wa simplrl vx cB cC wdisj vx vy vu cv cB csb cC wdisj vy vu cv cA
      vx vy vy vu cv cB csb cC vy vu cv cB nfcsb1v vy cC nfcv nfdisj vy cv vu
      cv wceq vx cB vy vu cv cB csb cC vy vu cv cB csbeq1a disjeq1d rspc sylc
      ad2antrr vx vy vu cv cB csb cC vr vs disjors sylib vy cA cB wdisj vx cB
      cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv
      cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr
      cv vs cv wceq wn wa wa vu cv vv cv wceq wa vr cv vy vu cv cB csb wcel vs
      cv vy vu cv cB csb wcel vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx
      cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv
      cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vu cv
      vv cv wceq wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel vy cA
      cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv
      cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB
      csb wcel wa vr cv vs cv wceq wn vu cv vv cv wceq simplrl simpld vy cA cB
      wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA
      wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb
      wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv wceq wa vs cv vy vv cv cB
      csb vy vu cv cB csb vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB
      cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB
      csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vu cv vv
      cv wceq wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel vy cA cB
      wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA
      wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb
      wcel wa vr cv vs cv wceq wn vu cv vv cv wceq simplrl simprd vu cv vv cv
      wceq vy vu cv cB csb vy vv cv cB csb wceq vy cA cB wdisj vx cB cC wdisj
      vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa
      wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv
      wceq wn wa wa vy vu cv vv cv cB csbeq1 adantl eleqtrrd jca vr cv vs cv
      wceq vx vr cv cC csb vx vs cv cC csb cin c0 wceq wo vr vs vy vu cv cB csb
      vy vu cv cB csb rsp2 sylc ord mpd vy cA cB wdisj vx cB cC wdisj vy cA
      wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr
      cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn
      wa wa vu cv vv cv wne wa vx vr cv cC csb vx vs cv cC csb cin vx vy vu cv
      cB csb cC ciun vx vy vv cv cB csb cC ciun cin wss vx vy vu cv cB csb cC
      ciun vx vy vv cv cB csb cC ciun cin c0 wceq vx vr cv cC csb vx vs cv cC
      csb cin c0 wceq vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC
      ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb
      wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv
      wne wa vx vr cv cC csb vx vy vu cv cB csb cC ciun wss vx vs cv cC csb vx
      vy vv cv cB csb cC ciun wss vx vr cv cC csb vx vs cv cC csb cin vx vy vu
      cv cB csb cC ciun vx vy vv cv cB csb cC ciun cin wss vy cA cB wdisj vx cB
      cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv
      cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr
      cv vs cv wceq wn wa wa vu cv vv cv wne wa vr cv vy vu cv cB csb wcel vx
      vr cv cC csb vx vy vu cv cB csb cC ciun wss vy cA cB wdisj vx cB cC wdisj
      vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa
      wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv
      wceq wn wa wa vu cv vv cv wne wa vr cv vy vu cv cB csb wcel vs cv vy vv
      cv cB csb wcel vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC
      ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb
      wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn vu cv vv cv wne
      simplrl simpld vr cv vy vu cv cB csb wcel vx vr cv cC csb vr vy vu cv cB
      csb vx vr cv cC csb ciun vx vy vu cv cB csb cC ciun vr vy vu cv cB csb vx
      vr cv cC csb ssiun2 vx vr vy vu cv cB csb cC vx vr cv cC csb vr cC nfcv
      vx vr cv cC nfcsb1v vx vr cv cC csbeq1a cbviun syl6sseqr syl vy cA cB
      wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA
      wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb
      wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv wne wa vs cv vy vv cv cB
      csb wcel vx vs cv cC csb vx vy vv cv cB csb cC ciun wss vy cA cB wdisj vx
      cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv
      cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa
      vr cv vs cv wceq wn wa wa vu cv vv cv wne wa vr cv vy vu cv cB csb wcel
      vs cv vy vv cv cB csb wcel vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA
      vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu
      cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn vu cv vv
      cv wne simplrl simprd vs cv vy vv cv cB csb wcel vx vs cv cC csb vs vy vv
      cv cB csb vx vs cv cC csb ciun vx vy vv cv cB csb cC ciun vs vy vv cv cB
      csb vx vs cv cC csb ssiun2 vx vs vy vv cv cB csb cC vx vs cv cC csb vs cC
      nfcv vx vs cv cC nfcsb1v vx vs cv cC csbeq1a cbviun syl6sseqr syl vx vr
      cv cC csb vx vy vu cv cB csb cC ciun vx vs cv cC csb vx vy vv cv cB csb
      cC ciun ss2in syl2anc vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx
      cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv
      cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vu cv
      vv cv wne wa vz cA vx vy vz cv cB csb cC ciun wdisj vu cv cA wcel vv cv
      cA wcel vu cv vv cv wne vx vy vu cv cB csb cC ciun vx vy vv cv cB csb cC
      ciun cin c0 wceq vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC
      ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb
      wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv
      wne wa vy cA vx cB cC ciun wdisj vz cA vx vy vz cv cB csb cC ciun wdisj
      vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa
      vu cv cA wcel vv cv cA wcel wa wa vy cA vx cB cC ciun wdisj vr cv vy vu
      cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq wn wa vu cv
      vv cv wne vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun
      wdisj vu cv cA wcel vv cv cA wcel wa simplrr ad2antrr vy vz cA vx cB cC
      ciun vx vy vz cv cB csb cC ciun vz vx cB cC ciun nfcv vx vy vy vz cv cB
      csb cC vy vz cv cB nfcsb1v vy cC nfcv nfiun vy cv vz cv wceq vx cB vy vz
      cv cB csb cC vy vz cv cB csbeq1a iuneq1d cbvdisj sylib vy cA cB wdisj vx
      cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv
      cv cA wcel wa wa vu cv cA wcel vr cv vy vu cv cB csb wcel vs cv vy vv cv
      cB csb wcel wa vr cv vs cv wceq wn wa vu cv vv cv wne vy cA cB wdisj vx
      cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv cA wcel vv
      cv cA wcel simprl ad2antrr vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA
      vx cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel wa wa vv cv cA wcel
      vr cv vy vu cv cB csb wcel vs cv vy vv cv cB csb wcel wa vr cv vs cv wceq
      wn wa vu cv vv cv wne vy cA cB wdisj vx cB cC wdisj vy cA wral vy cA vx
      cB cC ciun wdisj wa wa vu cv cA wcel vv cv cA wcel simprr ad2antrr vy cA
      cB wdisj vx cB cC wdisj vy cA wral vy cA vx cB cC ciun wdisj wa wa vu cv
      cA wcel vv cv cA wcel wa wa vr cv vy vu cv cB csb wcel vs cv vy vv cv cB
      csb wcel wa vr cv vs cv wceq wn wa wa vu cv vv cv wne simpr vz cA vx vy
      vz cv cB csb cC ciun vx vy vu cv cB csb cC ciun vx vy vv cv cB csb cC
      ciun vu cv vv cv vz cv vu cv wceq vx vy vz cv cB csb vy vu cv cB csb cC
      vy vz cv vu cv cB csbeq1 iuneq1d vz cv vv cv wceq vx vy vz cv cB csb vy
      vv cv cB csb cC vy vz cv vv cv cB csbeq1 iuneq1d disji2 syl121anc vx vr
      cv cC csb vx vs cv cC csb cin vx vy vu cv cB csb cC ciun vx vy vv cv cB
      csb cC ciun cin sseq0 syl2anc pm2.61dane expr orrd ex rexlimdvva syl5bi
      ralrimivv vx vy cA cB ciun cC vr vs disjors sylibr ex impbid $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w y z C $.  $d w x z D $.
    disjxun.1 $e |- ( x = y -> C = D ) $.
    $( The union of two disjoint collections.  (Contributed by Mario Carneiro,
       14-Nov-2016.) $)
    disjxun $p |- ( ( A i^i B ) = (/) -> ( Disj_ x e. ( A u. B ) C <->
      ( Disj_ x e. A C /\ Disj_ x e. B C /\
        A. x e. A A. y e. B ( C i^i D ) = (/) ) ) ) $=
      cA cB cin c0 wceq vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0
      wceq wo vw cA cB cun wral vz cA wral vz cv vw cv wceq vx vz cv cC csb vx
      vw cv cC csb cin c0 wceq wo vw cA cB cun wral vz cB wral wa vx cA cC
      wdisj cC cD cin c0 wceq vy cB wral vx cA wral wa vx cB cC wdisj cC cD cin
      c0 wceq vy cB wral vx cA wral wa wa vx cA cB cun cC wdisj vx cA cC wdisj
      vx cB cC wdisj cC cD cin c0 wceq vy cB wral vx cA wral w3a cA cB cin c0
      wceq vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw
      cA cB cun wral vz cA wral vx cA cC wdisj cC cD cin c0 wceq vy cB wral vx
      cA wral wa vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq
      wo vw cA cB cun wral vz cB wral vx cB cC wdisj cC cD cin c0 wceq vy cB
      wral vx cA wral wa cA cB cin c0 wceq vx cv vy cv wceq cC cD cin c0 wceq
      wo vy cA wral vx cA wral vx cv vy cv wceq cC cD cin c0 wceq wo vy cB wral
      vx cA wral wa vx cv vy cv wceq cC cD cin c0 wceq wo vy cA wral vx cA wral
      cC cD cin c0 wceq vy cB wral vx cA wral wa vz cv vw cv wceq vx vz cv cC
      csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral vz cA wral vx cA cC
      wdisj cC cD cin c0 wceq vy cB wral vx cA wral wa cA cB cin c0 wceq vx cv
      vy cv wceq cC cD cin c0 wceq wo vy cB wral vx cA wral cC cD cin c0 wceq
      vy cB wral vx cA wral vx cv vy cv wceq cC cD cin c0 wceq wo vy cA wral vx
      cA wral cA cB cin c0 wceq vx cv vy cv wceq cC cD cin c0 wceq wo cC cD cin
      c0 wceq vx vy cA cB cA cB cin c0 wceq vx cv cA wcel vy cv cB wcel wa wa
      cC cD cin c0 wceq vx cv vy cv wceq cC cD cin c0 wceq wo cA cB cin c0 wceq
      vx cv cA wcel vy cv cB wcel wa wa vx cv vy cv wceq wn cC cD cin c0 wceq
      vx cv vy cv wceq cC cD cin c0 wceq wo wb cA cB cin c0 wceq vx cv cA wcel
      vy cv cB wcel vx cv vy cv wceq wn cA cB cin c0 wceq vx cv cA wcel wa vx
      cv vy cv wceq vy cv cB wcel cA cB cin c0 wceq vx cv cA wcel wa vx cv cB
      wcel wn vx cv vy cv wceq vy cv cB wcel wn cA cB vx cv disjel vx cv vy cv
      wceq vx cv cB wcel vy cv cB wcel vx cv vy cv cB eleq1 notbid syl5ibcom
      con2d impr vx cv vy cv wceq cC cD cin c0 wceq biorf syl bicomd 2ralbidva
      anbi2d vx cv vy cv wceq cC cD cin c0 wceq wo vy cA cB cun wral vx cA wral
      vx cv vy cv wceq cC cD cin c0 wceq wo vy cA wral vx cv vy cv wceq cC cD
      cin c0 wceq wo vy cB wral wa vx cA wral vz cv vw cv wceq vx vz cv cC csb
      vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral vz cA wral vx cv vy cv
      wceq cC cD cin c0 wceq wo vy cA wral vx cA wral vx cv vy cv wceq cC cD
      cin c0 wceq wo vy cB wral vx cA wral wa vx cv vy cv wceq cC cD cin c0
      wceq wo vy cA cB cun wral vx cv vy cv wceq cC cD cin c0 wceq wo vy cA
      wral vx cv vy cv wceq cC cD cin c0 wceq wo vy cB wral wa vx cA vx cv vy
      cv wceq cC cD cin c0 wceq wo vy cA cB ralunb ralbii vx cv vy cv wceq cC
      cD cin c0 wceq wo vy cA cB cun wral vz cv vw cv wceq vx vz cv cC csb vx
      vw cv cC csb cin c0 wceq wo vw cA cB cun wral vx vz cA vx cv vy cv wceq
      cC cD cin c0 wceq wo vy cA cB cun wral vz nfv vz cv vw cv wceq vx vz cv
      cC csb vx vw cv cC csb cin c0 wceq wo vx vw cA cB cun vx cA cB cun nfcv
      vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq vx vz cv vw
      cv wceq vx nfv vx vx vz cv cC csb vx vw cv cC csb cin c0 vx vx vz cv cC
      csb vx vw cv cC csb vx vz cv cC nfcsb1v vx vw cv cC nfcsb1v nfin nfeq1
      nfor nfral vx cv vy cv wceq cC cD cin c0 wceq wo vy cA cB cun wral vx cv
      vw cv wceq cC vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral vx cv vz
      cv wceq vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo
      vw cA cB cun wral vx cv vw cv wceq cC vx vw cv cC csb cin c0 wceq wo vx
      cv vy cv wceq cC cD cin c0 wceq wo vw vy cA cB cun vw cv vy cv wceq vx cv
      vw cv wceq vx cv vy cv wceq cC vx vw cv cC csb cin c0 wceq cC cD cin c0
      wceq vw cv vy cv vx cv eqeq2 vw cv vy cv wceq cC vx vw cv cC csb cin cC
      cD cin c0 vw cv vy cv wceq vx vw cv cC csb cD cC vx vw vy cv cC cD vx vy
      cv nfcv vx cD nfcv disjxun.1 csbhypf ineq2d eqeq1d orbi12d cbvralv vx cv
      vz cv wceq vx cv vw cv wceq cC vx vw cv cC csb cin c0 wceq wo vz cv vw cv
      wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun vx cv vz
      cv wceq vx cv vw cv wceq vz cv vw cv wceq cC vx vw cv cC csb cin c0 wceq
      vx vz cv cC csb vx vw cv cC csb cin c0 wceq vx cv vz cv vw cv eqeq1 vx cv
      vz cv wceq cC vx vw cv cC csb cin vx vz cv cC csb vx vw cv cC csb cin c0
      vx cv vz cv wceq cC vx vz cv cC csb vx vw cv cC csb vx vz cv cC csbeq1a
      ineq1d eqeq1d orbi12d ralbidv syl5bbr cbvral vx cv vy cv wceq cC cD cin
      c0 wceq wo vy cA wral vx cv vy cv wceq cC cD cin c0 wceq wo vy cB wral vx
      cA r19.26 3bitr3i vx cA cC wdisj vx cv vy cv wceq cC cD cin c0 wceq wo vy
      cA wral vx cA wral cC cD cin c0 wceq vy cB wral vx cA wral cA cC cD vx vy
      disjxun.1 disjor anbi1i 3bitr4g cA cB cin c0 wceq vz cv vw cv wceq vx vz
      cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA wral vz cB wral vz cv vw
      cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cB wral vz cB
      wral wa cC cD cin c0 wceq vy cB wral vx cA wral vz cv vw cv wceq vx vz cv
      cC csb vx vw cv cC csb cin c0 wceq wo vw cB wral vz cB wral wa vz cv vw
      cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral
      vz cB wral vx cB cC wdisj cC cD cin c0 wceq vy cB wral vx cA wral wa cA
      cB cin c0 wceq vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0
      wceq wo vw cA wral vz cB wral cC cD cin c0 wceq vy cB wral vx cA wral vz
      cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cB wral
      vz cB wral vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq
      wo vw cA wral vz cB wral vx cv vy cv wceq cC cD cin c0 wceq wo vy cB wral
      vx cA wral cA cB cin c0 wceq cC cD cin c0 wceq vy cB wral vx cA wral vz
      cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA wral
      vz cB wral vx cv vy cv wceq cC cD cin c0 wceq wo vx cA wral vy cB wral vx
      cv vy cv wceq cC cD cin c0 wceq wo vy cB wral vx cA wral vz cv vw cv wceq
      vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA wral vx cv vy cv
      wceq cC cD cin c0 wceq wo vx cA wral vz vy cB vz cv vw cv wceq vx vz cv
      cC csb vx vw cv cC csb cin c0 wceq wo vw cA wral vz cv vx cv wceq vx vz
      cv cC csb cC cin c0 wceq wo vx cA wral vz cv vy cv wceq vx cv vy cv wceq
      cC cD cin c0 wceq wo vx cA wral vz cv vx cv wceq vx vz cv cC csb cC cin
      c0 wceq wo vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq
      wo vx vw cA vz cv vx cv wceq vx vz cv cC csb cC cin c0 wceq wo vw nfv vz
      cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq vx vz cv vw cv
      wceq vx nfv vx vx vz cv cC csb vx vw cv cC csb cin c0 vx vx vz cv cC csb
      vx vw cv cC csb vx vz cv cC nfcsb1v vx vw cv cC nfcsb1v nfin nfeq1 nfor
      vx cv vw cv wceq vz cv vx cv wceq vz cv vw cv wceq vx vz cv cC csb cC cin
      c0 wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq vx cv vw cv vz cv
      eqeq2 vx cv vw cv wceq vx vz cv cC csb cC cin vx vz cv cC csb vx vw cv cC
      csb cin c0 vx cv vw cv wceq cC vx vw cv cC csb vx vz cv cC csb vx vw cv
      cC csbeq1a ineq2d eqeq1d orbi12d cbvral vz cv vy cv wceq vz cv vx cv wceq
      vx vz cv cC csb cC cin c0 wceq wo vx cv vy cv wceq cC cD cin c0 wceq wo
      vx cA vz cv vy cv wceq vz cv vx cv wceq vx cv vy cv wceq vx vz cv cC csb
      cC cin c0 wceq cC cD cin c0 wceq vz cv vy cv wceq vz cv vx cv wceq vy cv
      vx cv wceq vx cv vy cv wceq vz cv vy cv vx cv eqeq1 vy cv vx cv eqcom
      syl6bb vz cv vy cv wceq vx vz cv cC csb cC cin cC cD cin c0 vz cv vy cv
      wceq vx vz cv cC csb cC cin cD cC cin cC cD cin vz cv vy cv wceq vx vz cv
      cC csb cD cC vx vz vy cv cC cD vx vy cv nfcv vx cD nfcv disjxun.1 csbhypf
      ineq1d cD cC incom syl6eq eqeq1d orbi12d ralbidv syl5bbr cbvralv vx cv vy
      cv wceq cC cD cin c0 wceq wo vy vx cB cA ralcom bitri cA cB cin c0 wceq
      vx cv vy cv wceq cC cD cin c0 wceq wo cC cD cin c0 wceq vx vy cA cB cA cB
      cin c0 wceq vx cv cA wcel vy cv cB wcel wa wa cC cD cin c0 wceq vx cv vy
      cv wceq cC cD cin c0 wceq wo cA cB cin c0 wceq vx cv cA wcel vy cv cB
      wcel wa wa vx cv vy cv wceq wn cC cD cin c0 wceq vx cv vy cv wceq cC cD
      cin c0 wceq wo wb cA cB cin c0 wceq vx cv cA wcel vy cv cB wcel vx cv vy
      cv wceq wn cA cB cin c0 wceq vx cv cA wcel wa vx cv vy cv wceq vy cv cB
      wcel cA cB cin c0 wceq vx cv cA wcel wa vx cv cB wcel wn vx cv vy cv wceq
      vy cv cB wcel wn cA cB vx cv disjel vx cv vy cv wceq vx cv cB wcel vy cv
      cB wcel vx cv vy cv cB eleq1 notbid syl5ibcom con2d impr vx cv vy cv wceq
      cC cD cin c0 wceq biorf syl bicomd 2ralbidva syl5bb anbi1d vz cv vw cv
      wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral vz
      cB wral vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo
      vw cA wral vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq
      wo vw cB wral wa vz cB wral vz cv vw cv wceq vx vz cv cC csb vx vw cv cC
      csb cin c0 wceq wo vw cA wral vz cB wral vz cv vw cv wceq vx vz cv cC csb
      vx vw cv cC csb cin c0 wceq wo vw cB wral vz cB wral wa vz cv vw cv wceq
      vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral vz cv vw
      cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA wral vz cv
      vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cB wral wa
      vz cB vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw
      cA cB ralunb ralbii vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin
      c0 wceq wo vw cA wral vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb
      cin c0 wceq wo vw cB wral vz cB r19.26 bitri vx cB cC wdisj vz cv vw cv
      wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cB wral vz cB wral
      cC cD cin c0 wceq vy cB wral vx cA wral vx cB cC vz vw disjors anbi2ci
      3bitr4g anbi12d vx cA cB cun cC wdisj vz cv vw cv wceq vx vz cv cC csb vx
      vw cv cC csb cin c0 wceq wo vw cA cB cun wral vz cA cB cun wral vz cv vw
      cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral
      vz cA wral vz cv vw cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq
      wo vw cA cB cun wral vz cB wral wa vx cA cB cun cC vz vw disjors vz cv vw
      cv wceq vx vz cv cC csb vx vw cv cC csb cin c0 wceq wo vw cA cB cun wral
      vz cA cB ralunb bitri vx cA cC wdisj vx cB cC wdisj cC cD cin c0 wceq vy
      cB wral vx cA wral w3a vx cA cC wdisj vx cB cC wdisj wa cC cD cin c0 wceq
      vy cB wral vx cA wral wa vx cA cC wdisj cC cD cin c0 wceq vy cB wral vx
      cA wral wa vx cB cC wdisj cC cD cin c0 wceq vy cB wral vx cA wral wa wa
      vx cA cC wdisj vx cB cC wdisj cC cD cin c0 wceq vy cB wral vx cA wral
      df-3an vx cA cC wdisj vx cB cC wdisj cC cD cin c0 wceq vy cB wral vx cA
      wral anandir bitri 3bitr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.
    $( Expand a disjoint collection with any number of empty sets.
       (Contributed by Mario Carneiro, 15-Nov-2016.) $)
    disjss3 $p |- ( ( A C_ B /\ A. x e. ( B \ A ) C = (/) ) ->
      ( Disj_ x e. A C <-> Disj_ x e. B C ) ) $=
      cA cB wss cC c0 wceq vx cB cA cdif wral wa vx cA cC wdisj vx cB cC wdisj
      cA cB wss cC c0 wceq vx cB cA cdif wral wa vx cv cA wcel vy cv cC wcel wa
      vx wmo vy wal vx cv cB wcel vy cv cC wcel wa vx wmo vy wal vx cA cC wdisj
      vx cB cC wdisj cA cB wss cC c0 wceq vx cB cA cdif wral wa vx cv cA wcel
      vy cv cC wcel wa vx wmo vx cv cB wcel vy cv cC wcel wa vx wmo vy cA cB
      wss cC c0 wceq vx cB cA cdif wral wa vx cv cB wcel vy cv cC wcel wa vx cv
      cA wcel vy cv cC wcel wa wi vx wal vx cv cA wcel vy cv cC wcel wa vx wmo
      vx cv cB wcel vy cv cC wcel wa vx wmo wi cA cB wss cC c0 wceq vx cB cA
      cdif wral vx cv cB wcel vy cv cC wcel wa vx cv cA wcel vy cv cC wcel wa
      wi vx wal cC c0 wceq vx cB cA cdif wral vx cv cB cA cdif wcel cC c0 wceq
      wi vx wal cA cB wss vx cv cB wcel vy cv cC wcel wa vx cv cA wcel vy cv cC
      wcel wa wi vx wal cC c0 wceq vx cB cA cdif df-ral cA cB wss vx cv cB cA
      cdif wcel cC c0 wceq wi vx cv cB wcel vy cv cC wcel wa vx cv cA wcel vy
      cv cC wcel wa wi vx cA cB wss vx cv cB cA cdif wcel cC c0 wceq wi vx cv
      cB wcel vy cv cC wcel wa vx cv cA wcel vy cv cC wcel wa cA cB wss vx cv
      cB cA cdif wcel cC c0 wceq wi vx cv cB wcel vy cv cC wcel wa w3a vx cv cA
      wcel vy cv cC wcel cA cB wss vx cv cB cA cdif wcel cC c0 wceq wi vx cv cB
      wcel vy cv cC wcel wa w3a vx cv cA wcel cC c0 wceq cA cB wss vx cv cB cA
      cdif wcel cC c0 wceq wi vx cv cB wcel vy cv cC wcel wa w3a vy cv cC wcel
      cC c0 wceq wn cA cB wss vx cv cB cA cdif wcel cC c0 wceq wi vx cv cB wcel
      vy cv cC wcel simp3r cC vy cv n0i syl cA cB wss vx cv cB cA cdif wcel cC
      c0 wceq wi vx cv cB wcel vy cv cC wcel wa w3a vx cv cB wcel vx cv cA wcel
      wn cC c0 wceq cA cB wss vx cv cB cA cdif wcel cC c0 wceq wi vx cv cB wcel
      vy cv cC wcel simp3l vx cv cB wcel vx cv cA wcel wn wa vx cv cB cA cdif
      wcel cA cB wss vx cv cB cA cdif wcel cC c0 wceq wi vx cv cB wcel vy cv cC
      wcel wa w3a cC c0 wceq vx cv cB cA eldif cA cB wss vx cv cB cA cdif wcel
      cC c0 wceq wi vx cv cB wcel vy cv cC wcel wa simp2 syl5bir mpand mt3d cA
      cB wss vx cv cB cA cdif wcel cC c0 wceq wi vx cv cB wcel vy cv cC wcel
      simp3r jca 3exp alimdv syl5bi imp vx cv cB wcel vy cv cC wcel wa vx cv cA
      wcel vy cv cC wcel wa vx moim syl alimdv vx vy cA cC dfdisj2 vx vy cB cC
      dfdisj2 3imtr4g cA cB wss vx cB cC wdisj vx cA cC wdisj wi cC c0 wceq vx
      cB cA cdif wral vx cA cB cC disjss1 adantr impbid $.
  $}


