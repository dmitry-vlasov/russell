
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/_Maps_to__notation.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                             Function operation

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c oF $.
  $c oR $.

  $( Extend class notation to include mapping of an operation to a function
     operation. $)
  cof $a class oF R $.

  $( Extend class notation to include mapping of a binary relation to a
     function relation. $)
  cofr $a class oR R $.

  ${
    $d f g x R $.
    $( Define the function operation map.  The definition is designed so that
       if ` R ` is a binary operation, then ` oF R ` is the analogous operation
       on functions which corresponds to applying ` R ` pointwise to the values
       of the functions.  (Contributed by Mario Carneiro, 20-Jul-2014.) $)
    df-of $a |- oF R = ( f e. _V , g e. _V |->
     ( x e. ( dom f i^i dom g ) |-> ( ( f ` x ) R ( g ` x ) ) ) ) $.

    $( Define the function relation map.  The definition is designed so that if
       ` R ` is a binary relation, then ` oF R ` is the analogous relation on
       functions which is true when each element of the left function relates
       to the corresponding element of the right function.  (Contributed by
       Mario Carneiro, 28-Jul-2014.) $)
    df-ofr $a |- oR R = { <. f , g >. |
      A. x e. ( dom f i^i dom g ) ( f ` x ) R ( g ` x ) } $.
  $}

  ${
    $d f g x y R $.  $d f g x y S $.
    $( Equality theorem for function operation.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
    ofeq $p |- ( R = S -> oF R = oF S ) $=
      cR cS wceq vf vg cvv cvv vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv
      vg cv cfv cR co cmpt cmpt2 vf vg cvv cvv vx vf cv cdm vg cv cdm cin vx cv
      vf cv cfv vx cv vg cv cfv cS co cmpt cmpt2 cR cof cS cof cR cS wceq vf vg
      cvv cvv vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cR co
      cmpt vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cS co
      cmpt cR cS wceq vf cv cvv wcel vg cv cvv wcel w3a vx vf cv cdm vg cv cdm
      cin vx cv vf cv cfv vx cv vg cv cfv cR co vx cv vf cv cfv vx cv vg cv cfv
      cS co cR cS wceq vf cv cvv wcel vg cv cvv wcel w3a cR cS vx cv vf cv cfv
      vx cv vg cv cfv cR cS wceq vf cv cvv wcel vg cv cvv wcel simp1 oveqd
      mpteq2dv mpt2eq3dva vx cR vf vg df-of vx cS vf vg df-of 3eqtr4g $.

    $( Equality theorem for function relation.  (Contributed by Mario Carneiro,
       28-Jul-2014.) $)
    ofreq $p |- ( R = S -> oR R = oR S ) $=
      cR cS wceq vx cv vf cv cfv vx cv vg cv cfv cR wbr vx vf cv cdm vg cv cdm
      cin wral vf vg copab vx cv vf cv cfv vx cv vg cv cfv cS wbr vx vf cv cdm
      vg cv cdm cin wral vf vg copab cR cofr cS cofr cR cS wceq vx cv vf cv cfv
      vx cv vg cv cfv cR wbr vx vf cv cdm vg cv cdm cin wral vx cv vf cv cfv vx
      cv vg cv cfv cS wbr vx vf cv cdm vg cv cdm cin wral vf vg cR cS wceq vx
      cv vf cv cfv vx cv vg cv cfv cR wbr vx cv vf cv cfv vx cv vg cv cfv cS
      wbr vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cR cS breq
      ralbidv opabbidv vx cR vf vg df-ofr vx cS vf vg df-ofr 3eqtr4g $.

    $( A function operation restricted to a set is a set.  (Contributed by NM,
       28-Jul-2014.) $)
    ofexg $p |- ( A e. V -> ( oF R |` A ) e. _V ) $=
      cR cof wfun cA cV wcel cR cof cA cres cvv wcel vf vg cvv cvv vx vf cv cdm
      vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cR co cmpt cR cof vx cR vf
      vg df-of mpt2fun cR cof cA cV resfunexg mpan $.

    nfof.1 $e |- F/_ x R $.
    $( Hypothesis builder for function operation.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
    nfof $p |- F/_ x oF R $=
      vx cR cof vf vg cvv cvv vy vf cv cdm vg cv cdm cin vy cv vf cv cfv vy cv
      vg cv cfv cR co cmpt cmpt2 vy cR vf vg df-of vf vg vx cvv cvv vy vf cv
      cdm vg cv cdm cin vy cv vf cv cfv vy cv vg cv cfv cR co cmpt vx cvv nfcv
      vx cvv nfcv vx vy vf cv cdm vg cv cdm cin vy cv vf cv cfv vy cv vg cv cfv
      cR co vx vf cv cdm vg cv cdm cin nfcv vx vy cv vf cv cfv vy cv vg cv cfv
      cR vx vy cv vf cv cfv nfcv nfof.1 vx vy cv vg cv cfv nfcv nfov nfmpt
      nfmpt2 nfcxfr $.

    $( Hypothesis builder for function relation.  (Contributed by Mario
       Carneiro, 28-Jul-2014.) $)
    nfofr $p |- F/_ x oR R $=
      vx cR cofr vy cv vf cv cfv vy cv vg cv cfv cR wbr vy vf cv cdm vg cv cdm
      cin wral vf vg copab vy cR vf vg df-ofr vy cv vf cv cfv vy cv vg cv cfv
      cR wbr vy vf cv cdm vg cv cdm cin wral vf vg vx vy cv vf cv cfv vy cv vg
      cv cfv cR wbr vx vy vf cv cdm vg cv cdm cin vx vf cv cdm vg cv cdm cin
      nfcv vx vy cv vf cv cfv vy cv vg cv cfv cR vx vy cv vf cv cfv nfcv nfof.1
      vx vy cv vg cv cfv nfcv nfbr nfral nfopab nfcxfr $.
  $}

  ${
    $d x A $.  $d f g x F $.  $d f g x G $.  $d x ph $.  $d x S $.  $d x X $.
    $d f g x R $.
    offval.1 $e |- ( ph -> F Fn A ) $.
    offval.2 $e |- ( ph -> G Fn B ) $.
    offval.3 $e |- ( ph -> A e. V ) $.
    offval.4 $e |- ( ph -> B e. W ) $.
    offval.5 $e |- ( A i^i B ) = S $.
    ${
      offval.6 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = C ) $.
      offval.7 $e |- ( ( ph /\ x e. B ) -> ( G ` x ) = D ) $.
      $( Value of an operation applied to two functions.  (Contributed by Mario
         Carneiro, 20-Jul-2014.) $)
      offval $p |- ( ph -> ( F oF R G ) = ( x e. S |-> ( C R D ) ) ) $=
        wph cF cG cR cof co vx cF cdm cG cdm cin vx cv cF cfv vx cv cG cfv cR
        co cmpt vx cS vx cv cF cfv vx cv cG cfv cR co cmpt vx cS cC cD cR co
        cmpt wph cF cvv wcel cG cvv wcel vx cF cdm cG cdm cin vx cv cF cfv vx
        cv cG cfv cR co cmpt cvv wcel cF cG cR cof co vx cF cdm cG cdm cin vx
        cv cF cfv vx cv cG cfv cR co cmpt wceq wph cF cA wfn cA cV wcel cF cvv
        wcel offval.1 offval.3 cA cV cF fnex syl2anc wph cG cB wfn cB cW wcel
        cG cvv wcel offval.2 offval.4 cB cW cG fnex syl2anc wph vx cF cdm cG
        cdm cin vx cv cF cfv vx cv cG cfv cR co cmpt vx cS vx cv cF cfv vx cv
        cG cfv cR co cmpt cvv wph cF cdm cG cdm cin cS wceq vx cF cdm cG cdm
        cin vx cv cF cfv vx cv cG cfv cR co cmpt vx cS vx cv cF cfv vx cv cG
        cfv cR co cmpt wceq wph cF cdm cG cdm cin cA cB cin cS wph cF cdm cA cG
        cdm cB wph cF cA wfn cF cdm cA wceq offval.1 cA cF fndm syl wph cG cB
        wfn cG cdm cB wceq offval.2 cB cG fndm syl ineq12d offval.5 syl6eq vx
        cF cdm cG cdm cin cS vx cv cF cfv vx cv cG cfv cR co mpteq1 syl wph cA
        cV wcel cS cvv wcel vx cS vx cv cF cfv vx cv cG cfv cR co cmpt cvv wcel
        offval.3 cA cV wcel cS cA cB cin cvv offval.5 cA cB cV inex1g syl5eqelr
        vx cS vx cv cF cfv vx cv cG cfv cR co cvv mptexg 3syl eqeltrd vf vg cF
        cG cvv cvv vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv
        cR co cmpt vx cF cdm cG cdm cin vx cv cF cfv vx cv cG cfv cR co cmpt cR
        cof cvv vf cv cF wceq vg cv cG wceq wa vx vf cv cdm vg cv cdm cin vx cv
        vf cv cfv vx cv vg cv cfv cR co cF cdm cG cdm cin vx cv cF cfv vx cv cG
        cfv cR co vf cv cF wceq vg cv cG wceq vf cv cdm cF cdm vg cv cdm cG cdm
        vf cv cF dmeq vg cv cG dmeq ineqan12d vf cv cF wceq vg cv cG wceq vx cv
        vf cv cfv vx cv cF cfv vx cv vg cv cfv vx cv cG cfv cR vx cv vf cv cF
        fveq1 vx cv vg cv cG fveq1 oveqan12d mpteq12dv vx cR vf vg df-of
        ovmpt2ga syl3anc wph cF cdm cG cdm cin cS wceq vx cF cdm cG cdm cin vx
        cv cF cfv vx cv cG cfv cR co cmpt vx cS vx cv cF cfv vx cv cG cfv cR co
        cmpt wceq wph cF cdm cG cdm cin cA cB cin cS wph cF cdm cA cG cdm cB
        wph cF cA wfn cF cdm cA wceq offval.1 cA cF fndm syl wph cG cB wfn cG
        cdm cB wceq offval.2 cB cG fndm syl ineq12d offval.5 syl6eq vx cF cdm
        cG cdm cin cS vx cv cF cfv vx cv cG cfv cR co mpteq1 syl wph vx cS vx
        cv cF cfv vx cv cG cfv cR co cC cD cR co vx cv cS wcel wph vx cv cA
        wcel vx cv cB wcel wa vx cv cF cfv vx cv cG cfv cR co cC cD cR co wceq
        vx cv cS wcel vx cv cA cB cin wcel vx cv cA wcel vx cv cB wcel wa cA cB
        cin cS vx cv offval.5 eleq2i vx cv cA cB elin bitr3i wph vx cv cA wcel
        vx cv cB wcel wa wa vx cv cF cfv cC vx cv cG cfv cD cR wph vx cv cA
        wcel vx cv cF cfv cC wceq vx cv cB wcel offval.6 adantrr wph vx cv cB
        wcel vx cv cG cfv cD wceq vx cv cA wcel offval.7 adantrl oveq12d
        sylan2b mpteq2dva 3eqtrd $.

      $( Value of a relation applied to two functions.  (Contributed by Mario
         Carneiro, 28-Jul-2014.) $)
      ofrfval $p |- ( ph -> ( F oR R G <-> A. x e. S C R D ) ) $=
        wph cF cG cR cofr wbr vx cv cF cfv vx cv cG cfv cR wbr vx cF cdm cG cdm
        cin wral vx cv cF cfv vx cv cG cfv cR wbr vx cS wral cC cD cR wbr vx cS
        wral wph cF cvv wcel cG cvv wcel cF cG cR cofr wbr vx cv cF cfv vx cv
        cG cfv cR wbr vx cF cdm cG cdm cin wral wb wph cF cA wfn cA cV wcel cF
        cvv wcel offval.1 offval.3 cA cV cF fnex syl2anc wph cG cB wfn cB cW
        wcel cG cvv wcel offval.2 offval.4 cB cW cG fnex syl2anc vx cv vf cv
        cfv vx cv vg cv cfv cR wbr vx vf cv cdm vg cv cdm cin wral vx cv cF cfv
        vx cv cG cfv cR wbr vx cF cdm cG cdm cin wral vf vg cF cG cR cofr cvv
        cvv vf cv cF wceq vg cv cG wceq wa vx cv vf cv cfv vx cv vg cv cfv cR
        wbr vx cv cF cfv vx cv cG cfv cR wbr vx vf cv cdm vg cv cdm cin cF cdm
        cG cdm cin vf cv cF wceq vg cv cG wceq vf cv cdm cF cdm vg cv cdm cG
        cdm vf cv cF dmeq vg cv cG dmeq ineqan12d vf cv cF wceq vg cv cG wceq
        vx cv vf cv cfv vx cv cF cfv vx cv vg cv cfv vx cv cG cfv cR vx cv vf
        cv cF fveq1 vx cv vg cv cG fveq1 breqan12d raleqbidv vx cR vf vg df-ofr
        brabga syl2anc wph vx cv cF cfv vx cv cG cfv cR wbr vx cF cdm cG cdm
        cin cS wph cF cdm cG cdm cin cA cB cin cS wph cF cdm cA cG cdm cB wph
        cF cA wfn cF cdm cA wceq offval.1 cA cF fndm syl wph cG cB wfn cG cdm
        cB wceq offval.2 cB cG fndm syl ineq12d offval.5 syl6eq raleqdv wph vx
        cv cF cfv vx cv cG cfv cR wbr cC cD cR wbr vx cS wph vx cv cS wcel wa
        vx cv cF cfv cC vx cv cG cfv cD cR vx cv cS wcel wph vx cv cA wcel vx
        cv cF cfv cC wceq cS cA vx cv cS cA cB cin cA offval.5 cA cB inss1
        eqsstr3i sseli offval.6 sylan2 vx cv cS wcel wph vx cv cB wcel vx cv cG
        cfv cD wceq cS cB vx cv cS cA cB cin cB offval.5 cA cB inss2 eqsstr3i
        sseli offval.7 sylan2 breq12d ralbidva 3bitrd $.
    $}

    ${
      ofval.6 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
      ofval.7 $e |- ( ( ph /\ X e. B ) -> ( G ` X ) = D ) $.
      $( Evaluate a function operation at a point.  (Contributed by Mario
         Carneiro, 20-Jul-2014.) $)
      ofval $p |- ( ( ph /\ X e. S ) -> ( ( F oF R G ) ` X ) = ( C R D ) ) $=
        wph cX cS wcel wa cX cF cG cR cof co cfv cX vx cS vx cv cF cfv vx cv cG
        cfv cR co cmpt cfv cX cF cfv cX cG cfv cR co cC cD cR co wph cX cF cG
        cR cof co cfv cX vx cS vx cv cF cfv vx cv cG cfv cR co cmpt cfv wceq cX
        cS wcel wph cX cF cG cR cof co vx cS vx cv cF cfv vx cv cG cfv cR co
        cmpt wph vx cA cB vx cv cF cfv vx cv cG cfv cR cS cF cG cV cW offval.1
        offval.2 offval.3 offval.4 offval.5 wph vx cv cA wcel wa vx cv cF cfv
        eqidd wph vx cv cB wcel wa vx cv cG cfv eqidd offval fveq1d adantr cX
        cS wcel cX vx cS vx cv cF cfv vx cv cG cfv cR co cmpt cfv cX cF cfv cX
        cG cfv cR co wceq wph vx cX vx cv cF cfv vx cv cG cfv cR co cX cF cfv
        cX cG cfv cR co cS vx cS vx cv cF cfv vx cv cG cfv cR co cmpt vx cv cX
        wceq vx cv cF cfv cX cF cfv vx cv cG cfv cX cG cfv cR vx cv cX cF fveq2
        vx cv cX cG fveq2 oveq12d vx cS vx cv cF cfv vx cv cG cfv cR co cmpt
        eqid cX cF cfv cX cG cfv cR ovex fvmpt adantl wph cX cS wcel wa cX cF
        cfv cC cX cG cfv cD cR cX cS wcel wph cX cA wcel cX cF cfv cC wceq cS
        cA cX cS cA cB cin cA offval.5 cA cB inss1 eqsstr3i sseli ofval.6
        sylan2 cX cS wcel wph cX cB wcel cX cG cfv cD wceq cS cB cX cS cA cB
        cin cB offval.5 cA cB inss2 eqsstr3i sseli ofval.7 sylan2 oveq12d
        3eqtrd $.

      $( Exhibit a function relation at a point.  (Contributed by Mario
         Carneiro, 28-Jul-2014.) $)
      ofrval $p |- ( ( ph /\ F oR R G /\ X e. S ) -> C R D ) $=
        wph cF cG cR cofr wbr cX cS wcel w3a cX cF cfv cX cG cfv cC cD cR wph
        cF cG cR cofr wbr cX cS wcel cX cF cfv cX cG cfv cR wbr wph cF cG cR
        cofr wbr wa vx cv cF cfv vx cv cG cfv cR wbr vx cS wral cX cS wcel cX
        cF cfv cX cG cfv cR wbr wi wph cF cG cR cofr wbr vx cv cF cfv vx cv cG
        cfv cR wbr vx cS wral wph vx cA cB vx cv cF cfv vx cv cG cfv cR cS cF
        cG cV cW offval.1 offval.2 offval.3 offval.4 offval.5 wph vx cv cA wcel
        wa vx cv cF cfv eqidd wph vx cv cB wcel wa vx cv cG cfv eqidd ofrfval
        biimpa vx cv cF cfv vx cv cG cfv cR wbr cX cF cfv cX cG cfv cR wbr vx
        cX cS vx cv cX wceq vx cv cF cfv cX cF cfv vx cv cG cfv cX cG cfv cR vx
        cv cX cF fveq2 vx cv cX cG fveq2 breq12d rspccv syl 3impia wph cF cG cR
        cofr wbr cX cS wcel w3a wph cX cA wcel cX cF cfv cC wceq wph cF cG cR
        cofr wbr cX cS wcel simp1 wph cF cG cR cofr wbr cX cS wcel w3a cS cA cX
        cS cA cB cin cA offval.5 cA cB inss1 eqsstr3i wph cF cG cR cofr wbr cX
        cS wcel simp3 sseldi ofval.6 syl2anc wph cF cG cR cofr wbr cX cS wcel
        w3a wph cX cB wcel cX cG cfv cD wceq wph cF cG cR cofr wbr cX cS wcel
        simp1 wph cF cG cR cofr wbr cX cS wcel w3a cS cB cX cS cA cB cin cB
        offval.5 cA cB inss2 eqsstr3i wph cF cG cR cofr wbr cX cS wcel simp3
        sseldi ofval.7 syl2anc 3brtr3d $.
    $}

    $( The function operation produces a function.  (Contributed by Mario
       Carneiro, 22-Jul-2014.) $)
    offn $p |- ( ph -> ( F oF R G ) Fn S ) $=
      wph cF cG cR cof co cS wfn vx cS vx cv cF cfv vx cv cG cfv cR co cmpt cS
      wfn vx cS vx cv cF cfv vx cv cG cfv cR co vx cS vx cv cF cfv vx cv cG cfv
      cR co cmpt vx cv cF cfv vx cv cG cfv cR ovex vx cS vx cv cF cfv vx cv cG
      cfv cR co cmpt eqid fnmpti wph cS cF cG cR cof co vx cS vx cv cF cfv vx
      cv cG cfv cR co cmpt wph vx cA cB vx cv cF cfv vx cv cG cfv cR cS cF cG
      cV cW offval.1 offval.2 offval.3 offval.4 offval.5 wph vx cv cA wcel wa
      vx cv cF cfv eqidd wph vx cv cB wcel wa vx cv cG cfv eqidd offval fneq1d
      mpbiri $.
  $}

  $( Function value of a pointwise composition.  (Contributed by Stefan O'Rear,
     5-Oct-2014.)  (Proof shortened by Mario Carneiro, 5-Jun-2015.) $)
  fnfvof $p |- ( ( ( F Fn A /\ G Fn A ) /\ ( A e. V /\ X e. A ) ) ->
      ( ( F oF R G ) ` X ) = ( ( F ` X ) R ( G ` X ) ) ) $=
    cF cA wfn cG cA wfn wa cA cV wcel cX cA wcel cX cF cG cR cof co cfv cX cF
    cfv cX cG cfv cR co wceq cF cA wfn cG cA wfn wa cA cV wcel wa cA cA cX cF
    cfv cX cG cfv cR cA cF cG cV cV cX cF cA wfn cG cA wfn cA cV wcel simpll cF
    cA wfn cG cA wfn cA cV wcel simplr cF cA wfn cG cA wfn wa cA cV wcel simpr
    cF cA wfn cG cA wfn wa cA cV wcel simpr cA inidm cF cA wfn cG cA wfn wa cA
    cV wcel wa cX cA wcel wa cX cF cfv eqidd cF cA wfn cG cA wfn wa cA cV wcel
    wa cX cA wcel wa cX cG cfv eqidd ofval anasss $.

  ${
    $d F x a b $.  $d G x a b $.  $d V x $.  $d W x $.  $d R x a b $.
    $d D x $.
    $( General value of ` ( F oF R G ) ` with no assumptions on functionality
       of ` F ` and ` G ` .  (Contributed by Stefan O'Rear, 24-Jan-2015.) $)
    offval3 $p |- ( ( F e. V /\ G e. W ) -> ( F oF R G ) =
        ( x e. ( dom F i^i dom G ) |-> ( ( F ` x ) R ( G ` x ) ) ) ) $=
      cF cV wcel cG cW wcel wa cF cvv wcel cG cvv wcel vx cF cdm cG cdm cin vx
      cv cF cfv vx cv cG cfv cR co cmpt cvv wcel cF cG cR cof co vx cF cdm cG
      cdm cin vx cv cF cfv vx cv cG cfv cR co cmpt wceq cF cV wcel cF cvv wcel
      cG cW wcel cF cV elex adantr cG cW wcel cG cvv wcel cF cV wcel cG cW elex
      adantl cF cV wcel vx cF cdm cG cdm cin vx cv cF cfv vx cv cG cfv cR co
      cmpt cvv wcel cG cW wcel cF cV wcel cF cdm cvv wcel cF cdm cG cdm cin cvv
      wcel vx cF cdm cG cdm cin vx cv cF cfv vx cv cG cfv cR co cmpt cvv wcel
      cF cV dmexg cF cdm cG cdm cvv inex1g vx cF cdm cG cdm cin vx cv cF cfv vx
      cv cG cfv cR co cvv mptexg 3syl adantr va vb cF cG cvv cvv vx va cv cdm
      vb cv cdm cin vx cv va cv cfv vx cv vb cv cfv cR co cmpt vx cF cdm cG cdm
      cin vx cv cF cfv vx cv cG cfv cR co cmpt cR cof cvv va cv cF wceq vb cv
      cG wceq wa vx va cv cdm vb cv cdm cin vx cv va cv cfv vx cv vb cv cfv cR
      co cF cdm cG cdm cin vx cv cF cfv vx cv cG cfv cR co va cv cF wceq vb cv
      cG wceq va cv cdm cF cdm vb cv cdm cG cdm va cv cF dmeq vb cv cG dmeq
      ineqan12d va cv cF wceq vb cv cG wceq vx cv va cv cfv vx cv cF cfv vx cv
      vb cv cfv vx cv cG cfv cR vx cv va cv cF fveq1 vx cv vb cv cG fveq1
      oveqan12d mpteq12dv vx cR va vb df-of ovmpt2ga syl3anc $.

    $( Pointwise combination commutes with restriction.  (Contributed by Stefan
       O'Rear, 24-Jan-2015.) $)
    offres $p |- ( ( F e. V /\ G e. W ) -> ( ( F oF R G ) |` D ) =
        ( ( F |` D ) oF R ( G |` D ) ) ) $=
      cF cV wcel cG cW wcel wa vx cF cdm cG cdm cin vx cv cF cfv vx cv cG cfv
      cR co cmpt cD cres vx cF cD cres cdm cG cD cres cdm cin vx cv cF cD cres
      cfv vx cv cG cD cres cfv cR co cmpt cF cG cR cof co cD cres cF cD cres cG
      cD cres cR cof co vx cF cdm cG cdm cin cD cin vx cv cF cD cres cfv vx cv
      cG cD cres cfv cR co cmpt vx cF cdm cG cdm cin cD cin vx cv cF cfv vx cv
      cG cfv cR co cmpt vx cF cD cres cdm cG cD cres cdm cin vx cv cF cD cres
      cfv vx cv cG cD cres cfv cR co cmpt vx cF cdm cG cdm cin vx cv cF cfv vx
      cv cG cfv cR co cmpt cD cres vx cF cdm cG cdm cin cD cin vx cv cF cD cres
      cfv vx cv cG cD cres cfv cR co vx cv cF cfv vx cv cG cfv cR co vx cv cF
      cdm cG cdm cin cD cin wcel vx cv cD wcel vx cv cF cD cres cfv vx cv cG cD
      cres cfv cR co vx cv cF cfv vx cv cG cfv cR co wceq cF cdm cG cdm cin cD
      cin cD vx cv cF cdm cG cdm cin cD inss2 sseli vx cv cD wcel vx cv cF cD
      cres cfv vx cv cF cfv vx cv cG cD cres cfv vx cv cG cfv cR vx cv cD cF
      fvres vx cv cD cG fvres oveq12d syl mpteq2ia vx cF cD cres cdm cG cD cres
      cdm cin vx cv cF cD cres cfv vx cv cG cD cres cfv cR co cF cdm cG cdm cin
      cD cin vx cv cF cD cres cfv vx cv cG cD cres cfv cR co cD cF cdm cG cdm
      cin cin cD cF cdm cin cD cG cdm cin cin cF cdm cG cdm cin cD cin cF cD
      cres cdm cG cD cres cdm cin cD cF cdm cG cdm inindi cF cdm cG cdm cin cD
      incom cF cD cres cdm cD cF cdm cin cG cD cres cdm cD cG cdm cin cF cD
      dmres cG cD dmres ineq12i 3eqtr4ri vx cv cF cD cres cfv vx cv cG cD cres
      cfv cR co eqid mpteq12i vx cF cdm cG cdm cin cD vx cv cF cfv vx cv cG cfv
      cR co resmpt3 3eqtr4ri cF cV wcel cG cW wcel wa cF cG cR cof co vx cF cdm
      cG cdm cin vx cv cF cfv vx cv cG cfv cR co cmpt cD vx cR cF cG cV cW
      offval3 reseq1d cF cV wcel cF cD cres cvv wcel cG cD cres cvv wcel cF cD
      cres cG cD cres cR cof co vx cF cD cres cdm cG cD cres cdm cin vx cv cF
      cD cres cfv vx cv cG cD cres cfv cR co cmpt wceq cG cW wcel cF cD cV
      resexg cG cD cW resexg vx cR cF cD cres cG cD cres cvv cvv offval3 syl2an
      3eqtr4a $.
  $}

  ${
    $d z A $.  $d z C $.  $d y z G $.  $d x y z ph $.  $d x y S $.  $d x y T $.
    $d x y z F $.  $d x y z R $.  $d x y z U $.
    off.1 $e |- ( ( ph /\ ( x e. S /\ y e. T ) ) -> ( x R y ) e. U ) $.
    off.2 $e |- ( ph -> F : A --> S ) $.
    off.3 $e |- ( ph -> G : B --> T ) $.
    off.4 $e |- ( ph -> A e. V ) $.
    off.5 $e |- ( ph -> B e. W ) $.
    off.6 $e |- ( A i^i B ) = C $.
    $( The function operation produces a function.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
    off $p |- ( ph -> ( F oF R G ) : C --> U ) $=
      wph cC cU cF cG cR cof co wf cC cU vz cC vz cv cF cfv vz cv cG cfv cR co
      cmpt wf wph vz cC vz cv cF cfv vz cv cG cfv cR co cU vz cC vz cv cF cfv
      vz cv cG cfv cR co cmpt wph vz cv cC wcel wa vz cv cF cfv cS wcel vz cv
      cG cfv cT wcel vx cv vy cv cR co cU wcel vy cT wral vx cS wral vz cv cF
      cfv vz cv cG cfv cR co cU wcel wph cA cS cF wf vz cv cA wcel vz cv cF cfv
      cS wcel vz cv cC wcel off.2 cC cA vz cv cC cA cB cin cA off.6 cA cB inss1
      eqsstr3i sseli cA cS vz cv cF ffvelrn syl2an wph cB cT cG wf vz cv cB
      wcel vz cv cG cfv cT wcel vz cv cC wcel off.3 cC cB vz cv cC cA cB cin cB
      off.6 cA cB inss2 eqsstr3i sseli cB cT vz cv cG ffvelrn syl2an wph vx cv
      vy cv cR co cU wcel vy cT wral vx cS wral vz cv cC wcel wph vx cv vy cv
      cR co cU wcel vx vy cS cT off.1 ralrimivva adantr vx cv vy cv cR co cU
      wcel vz cv cF cfv vz cv cG cfv cR co cU wcel vz cv cF cfv vy cv cR co cU
      wcel vx vy vz cv cF cfv vz cv cG cfv cS cT vx cv vz cv cF cfv wceq vx cv
      vy cv cR co vz cv cF cfv vy cv cR co cU vx cv vz cv cF cfv vy cv cR oveq1
      eleq1d vy cv vz cv cG cfv wceq vz cv cF cfv vy cv cR co vz cv cF cfv vz
      cv cG cfv cR co cU vy cv vz cv cG cfv vz cv cF cfv cR oveq2 eleq1d
      rspc2va syl21anc vz cC vz cv cF cfv vz cv cG cfv cR co cmpt eqid fmptd
      wph cC cU cF cG cR cof co vz cC vz cv cF cfv vz cv cG cfv cR co cmpt wph
      vz cA cB vz cv cF cfv vz cv cG cfv cR cC cF cG cV cW wph cA cS cF wf cF
      cA wfn off.2 cA cS cF ffn syl wph cB cT cG wf cG cB wfn off.3 cB cT cG
      ffn syl off.4 off.5 off.6 wph vz cv cA wcel wa vz cv cF cfv eqidd wph vz
      cv cB wcel wa vz cv cG cfv eqidd offval feq1d mpbird $.
  $}

  ${
    $d x A $.  $d x C $.  $d x F $.  $d x G $.  $d x ph $.  $d x R $.
    ofres.1 $e |- ( ph -> F Fn A ) $.
    ofres.2 $e |- ( ph -> G Fn B ) $.
    ofres.3 $e |- ( ph -> A e. V ) $.
    ofres.4 $e |- ( ph -> B e. W ) $.
    ofres.5 $e |- ( A i^i B ) = C $.
    $( Restrict the operands of a function operation to the same domain as that
       of the operation itself.  (Contributed by Mario Carneiro,
       15-Sep-2014.) $)
    ofres $p |- ( ph -> ( F oF R G ) = ( ( F |` C ) oF R ( G |` C ) ) ) $=
      wph cF cG cR cof co vx cC vx cv cF cfv vx cv cG cfv cR co cmpt cF cC cres
      cG cC cres cR cof co wph vx cA cB vx cv cF cfv vx cv cG cfv cR cC cF cG
      cV cW ofres.1 ofres.2 ofres.3 ofres.4 ofres.5 wph vx cv cA wcel wa vx cv
      cF cfv eqidd wph vx cv cB wcel wa vx cv cG cfv eqidd offval wph vx cC cC
      vx cv cF cfv vx cv cG cfv cR cC cF cC cres cG cC cres cvv cvv wph cF cA
      wfn cC cA wss cF cC cres cC wfn ofres.1 cC cA cB cin cA ofres.5 cA cB
      inss1 eqsstr3i cA cC cF fnssres sylancl wph cG cB wfn cC cB wss cG cC
      cres cC wfn ofres.2 cC cA cB cin cB ofres.5 cA cB inss2 eqsstr3i cB cC cG
      fnssres sylancl wph cC cA wss cA cV wcel cC cvv wcel cC cA cB cin cA
      ofres.5 cA cB inss1 eqsstr3i ofres.3 cC cA cV ssexg sylancr wph cC cA wss
      cA cV wcel cC cvv wcel cC cA cB cin cA ofres.5 cA cB inss1 eqsstr3i
      ofres.3 cC cA cV ssexg sylancr cC inidm vx cv cC wcel vx cv cF cC cres
      cfv vx cv cF cfv wceq wph vx cv cC cF fvres adantl vx cv cC wcel vx cv cG
      cC cres cfv vx cv cG cfv wceq wph vx cv cC cG fvres adantl offval eqtr4d
      $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d y z C $.  $d y F $.  $d y G $.  $d x y ph $.
    $d x y z R $.
    offval2.1 $e |- ( ph -> A e. V ) $.
    offval2.2 $e |- ( ( ph /\ x e. A ) -> B e. W ) $.
    offval2.3 $e |- ( ( ph /\ x e. A ) -> C e. X ) $.
    offval2.4 $e |- ( ph -> F = ( x e. A |-> B ) ) $.
    offval2.5 $e |- ( ph -> G = ( x e. A |-> C ) ) $.
    $( The function operation expressed as a mapping.  (Contributed by Mario
       Carneiro, 20-Jul-2014.) $)
    offval2 $p |- ( ph -> ( F oF R G ) = ( x e. A |-> ( B R C ) ) ) $=
      wph cF cG cR cof co vy cA vy cv vx cA cB cmpt cfv vy cv vx cA cC cmpt cfv
      cR co cmpt vx cA cB cC cR co cmpt wph vy cA cA vy cv vx cA cB cmpt cfv vy
      cv vx cA cC cmpt cfv cR cA cF cG cV cV wph cF cA wfn vx cA cB cmpt cA wfn
      wph cB cW wcel vx cA wral vx cA cB cmpt cA wfn wph cB cW wcel vx cA
      offval2.2 ralrimiva vx cA cB vx cA cB cmpt cW vx cA cB cmpt eqid fnmpt
      syl wph cA cF vx cA cB cmpt offval2.4 fneq1d mpbird wph cG cA wfn vx cA
      cC cmpt cA wfn wph cC cX wcel vx cA wral vx cA cC cmpt cA wfn wph cC cX
      wcel vx cA offval2.3 ralrimiva vx cA cC vx cA cC cmpt cX vx cA cC cmpt
      eqid fnmpt syl wph cA cG vx cA cC cmpt offval2.5 fneq1d mpbird offval2.1
      offval2.1 cA inidm wph vy cv cA wcel wa vy cv cF vx cA cB cmpt wph cF vx
      cA cB cmpt wceq vy cv cA wcel offval2.4 adantr fveq1d wph vy cv cA wcel
      wa vy cv cG vx cA cC cmpt wph cG vx cA cC cmpt wceq vy cv cA wcel
      offval2.5 adantr fveq1d offval wph vy cA vy cv vx cA cB cmpt cfv vy cv vx
      cA cC cmpt cfv cR co cmpt vx cA vx cv vx cA cB cmpt cfv vx cv vx cA cC
      cmpt cfv cR co cmpt vx cA cB cC cR co cmpt vy vx cA vy cv vx cA cB cmpt
      cfv vy cv vx cA cC cmpt cfv cR co vx cv vx cA cB cmpt cfv vx cv vx cA cC
      cmpt cfv cR co vx vy cv vx cA cB cmpt cfv vy cv vx cA cC cmpt cfv cR vx
      vy cv vx cA cB cmpt vx cA cB nfmpt1 vx vy cv nfcv nffv vx cR nfcv vx vy
      cv vx cA cC cmpt vx cA cC nfmpt1 vx vy cv nfcv nffv nfov vy vx cv vx cA
      cB cmpt cfv vx cv vx cA cC cmpt cfv cR co nfcv vy cv vx cv wceq vy cv vx
      cA cB cmpt cfv vx cv vx cA cB cmpt cfv vy cv vx cA cC cmpt cfv vx cv vx
      cA cC cmpt cfv cR vy cv vx cv vx cA cB cmpt fveq2 vy cv vx cv vx cA cC
      cmpt fveq2 oveq12d cbvmpt wph vx cA vx cv vx cA cB cmpt cfv vx cv vx cA
      cC cmpt cfv cR co cB cC cR co wph vx cv cA wcel wa vx cv vx cA cB cmpt
      cfv cB vx cv vx cA cC cmpt cfv cC cR wph vx cv cA wcel wa vx cv cA wcel
      cB cW wcel vx cv vx cA cB cmpt cfv cB wceq wph vx cv cA wcel simpr
      offval2.2 vx cA cB cW vx cA cB cmpt vx cA cB cmpt eqid fvmpt2 syl2anc wph
      vx cv cA wcel wa vx cv cA wcel cC cX wcel vx cv vx cA cC cmpt cfv cC wceq
      wph vx cv cA wcel simpr offval2.3 vx cA cC cX vx cA cC cmpt vx cA cC cmpt
      eqid fvmpt2 syl2anc oveq12d mpteq2dva syl5eq eqtrd $.

    $( The function relation acting on maps.  (Contributed by Mario Carneiro,
       20-Jul-2014.) $)
    ofrfval2 $p |- ( ph -> ( F oR R G <-> A. x e. A B R C ) ) $=
      wph cF cG cR cofr wbr vy cv vx cA cB cmpt cfv vy cv vx cA cC cmpt cfv cR
      wbr vy cA wral cB cC cR wbr vx cA wral wph vy cA cA vy cv vx cA cB cmpt
      cfv vy cv vx cA cC cmpt cfv cR cA cF cG cV cV wph cF cA wfn vx cA cB cmpt
      cA wfn wph cB cW wcel vx cA wral vx cA cB cmpt cA wfn wph cB cW wcel vx
      cA offval2.2 ralrimiva vx cA cB vx cA cB cmpt cW vx cA cB cmpt eqid fnmpt
      syl wph cA cF vx cA cB cmpt offval2.4 fneq1d mpbird wph cG cA wfn vx cA
      cC cmpt cA wfn wph cC cX wcel vx cA wral vx cA cC cmpt cA wfn wph cC cX
      wcel vx cA offval2.3 ralrimiva vx cA cC vx cA cC cmpt cX vx cA cC cmpt
      eqid fnmpt syl wph cA cG vx cA cC cmpt offval2.5 fneq1d mpbird offval2.1
      offval2.1 cA inidm wph vy cv cA wcel wa vy cv cF vx cA cB cmpt wph cF vx
      cA cB cmpt wceq vy cv cA wcel offval2.4 adantr fveq1d wph vy cv cA wcel
      wa vy cv cG vx cA cC cmpt wph cG vx cA cC cmpt wceq vy cv cA wcel
      offval2.5 adantr fveq1d ofrfval vy cv vx cA cB cmpt cfv vy cv vx cA cC
      cmpt cfv cR wbr vy cA wral vx cv vx cA cB cmpt cfv vx cv vx cA cC cmpt
      cfv cR wbr vx cA wral wph cB cC cR wbr vx cA wral vy cv vx cA cB cmpt cfv
      vy cv vx cA cC cmpt cfv cR wbr vx cv vx cA cB cmpt cfv vx cv vx cA cC
      cmpt cfv cR wbr vy vx cA vx vy cv vx cA cB cmpt cfv vy cv vx cA cC cmpt
      cfv cR vx vy cv vx cA cB cmpt vx cA cB nfmpt1 vx vy cv nfcv nffv vx cR
      nfcv vx vy cv vx cA cC cmpt vx cA cC nfmpt1 vx vy cv nfcv nffv nfbr vx cv
      vx cA cB cmpt cfv vx cv vx cA cC cmpt cfv cR wbr vy nfv vy cv vx cv wceq
      vy cv vx cA cB cmpt cfv vx cv vx cA cB cmpt cfv vy cv vx cA cC cmpt cfv
      vx cv vx cA cC cmpt cfv cR vy cv vx cv vx cA cB cmpt fveq2 vy cv vx cv vx
      cA cC cmpt fveq2 breq12d cbvral wph vx cv vx cA cB cmpt cfv vx cv vx cA
      cC cmpt cfv cR wbr cB cC cR wbr vx cA wph vx cv cA wcel wa vx cv vx cA cB
      cmpt cfv cB vx cv vx cA cC cmpt cfv cC cR wph vx cv cA wcel wa vx cv cA
      wcel cB cW wcel vx cv vx cA cB cmpt cfv cB wceq wph vx cv cA wcel simpr
      offval2.2 vx cA cB cW vx cA cB cmpt vx cA cB cmpt eqid fvmpt2 syl2anc wph
      vx cv cA wcel wa vx cv cA wcel cC cX wcel vx cv vx cA cC cmpt cfv cC wceq
      wph vx cv cA wcel simpr offval2.3 vx cA cC cX vx cA cC cmpt vx cA cC cmpt
      eqid fvmpt2 syl2anc breq12d ralbidva syl5bb bitrd $.
  $}

  ${
    $d y A $.  $d x y C $.  $d x y F $.  $d x y G $.  $d x y H $.  $d x y ph $.
    $d x D $.  $d x y R $.
    ofco.1 $e |- ( ph -> F Fn A ) $.
    ofco.2 $e |- ( ph -> G Fn B ) $.
    ofco.3 $e |- ( ph -> H : D --> C ) $.
    ofco.4 $e |- ( ph -> A e. V ) $.
    ofco.5 $e |- ( ph -> B e. W ) $.
    ofco.6 $e |- ( ph -> D e. X ) $.
    ofco.7 $e |- ( A i^i B ) = C $.
    $( The composition of a function operation with another function.
       (Contributed by Mario Carneiro, 19-Dec-2014.) $)
    ofco $p |- ( ph ->
      ( ( F oF R G ) o. H ) = ( ( F o. H ) oF R ( G o. H ) ) ) $=
      wph cF cG cR cof co cH ccom vx cD vx cv cH cfv cF cfv vx cv cH cfv cG cfv
      cR co cmpt cF cH ccom cG cH ccom cR cof co wph vx vy cD cC vx cv cH cfv
      vy cv cF cfv vy cv cG cfv cR co vx cv cH cfv cF cfv vx cv cH cfv cG cfv
      cR co cH cF cG cR cof co wph cD cC cH wf vx cv cD wcel vx cv cH cfv cC
      wcel ofco.3 cD cC vx cv cH ffvelrn sylan wph vx cD cC cH ofco.3 feqmptd
      wph vy cA cB vy cv cF cfv vy cv cG cfv cR cC cF cG cV cW ofco.1 ofco.2
      ofco.4 ofco.5 ofco.7 wph vy cv cA wcel wa vy cv cF cfv eqidd wph vy cv cB
      wcel wa vy cv cG cfv eqidd offval vy cv vx cv cH cfv wceq vy cv cF cfv vx
      cv cH cfv cF cfv vy cv cG cfv vx cv cH cfv cG cfv cR vy cv vx cv cH cfv
      cF fveq2 vy cv vx cv cH cfv cG fveq2 oveq12d fmptco wph vx cD cD vx cv cH
      cfv cF cfv vx cv cH cfv cG cfv cR cD cF cH ccom cG cH ccom cX cX wph cF
      cA wfn cD cA cH wf cF cH ccom cD wfn ofco.1 wph cD cC cH wf cC cA wss cD
      cA cH wf ofco.3 cC cA cB cin cA ofco.7 cA cB inss1 eqsstr3i cD cC cA cH
      fss sylancl cA cD cF cH fnfco syl2anc wph cG cB wfn cD cB cH wf cG cH
      ccom cD wfn ofco.2 wph cD cC cH wf cC cB wss cD cB cH wf ofco.3 cC cA cB
      cin cB ofco.7 cA cB inss2 eqsstr3i cD cC cB cH fss sylancl cB cD cG cH
      fnfco syl2anc ofco.6 ofco.6 cD inidm wph cH cD wfn vx cv cD wcel vx cv cF
      cH ccom cfv vx cv cH cfv cF cfv wceq wph cD cC cH wf cH cD wfn ofco.3 cD
      cC cH ffn syl cD cF cH vx cv fvco2 sylan wph cH cD wfn vx cv cD wcel vx
      cv cG cH ccom cfv vx cv cH cfv cG cfv wceq wph cD cC cH wf cH cD wfn
      ofco.3 cD cC cH ffn syl cD cG cH vx cv fvco2 sylan offval eqtr4d $.
  $}

  ${
    $d x A $.  $d x F $.  $d x G $.  $d x H $.  $d x ph $.  $d x R $.
    offveq.1 $e |- ( ph -> A e. V ) $.
    offveq.2 $e |- ( ph -> F Fn A ) $.
    offveq.3 $e |- ( ph -> G Fn A ) $.
    offveq.4 $e |- ( ph -> H Fn A ) $.
    offveq.5 $e |- ( ( ph /\ x e. A ) -> ( F ` x ) = B ) $.
    offveq.6 $e |- ( ( ph /\ x e. A ) -> ( G ` x ) = C ) $.
    ${
      offveq.7 $e |- ( ( ph /\ x e. A ) -> ( B R C ) = ( H ` x ) ) $.
      $( Convert an identity of the operation to the analogous identity on the
         function operation.  (Contributed by Mario Carneiro, 24-Jul-2014.) $)
      offveq $p |- ( ph -> ( F oF R G ) = H ) $=
        wph vx cA cF cG cR cof co cH wph cA cA cR cA cF cG cV cV offveq.2
        offveq.3 offveq.1 offveq.1 cA inidm offn offveq.4 wph vx cv cA wcel wa
        vx cv cF cG cR cof co cfv cB cC cR co vx cv cH cfv wph cA cA cB cC cR
        cA cF cG cV cV vx cv offveq.2 offveq.3 offveq.1 offveq.1 cA inidm
        offveq.5 offveq.6 ofval offveq.7 eqtrd eqfnfvd $.
    $}

    $d y A $.  $d y z B $.  $d y z C $.  $d x y z F $.  $d y z G $.  $d y H $.
    $d y R $.  $d y ph $.
    $( Equivalent expressions for equality with a function operation.
       (Contributed by NM, 9-Oct-2014.)  (Proof shortened by Mario Carneiro,
       5-Dec-2016.) $)
    offveqb $p |- ( ph
          -> ( H = ( F oF R G ) <-> A. x e. A ( H ` x ) = ( B R C ) ) ) $=
      wph cH cF cG cR cof co wceq vx cA vx cv cH cfv cmpt vx cA cB cC cR co
      cmpt wceq vx cv cH cfv cB cC cR co wceq vx cA wral wph cH vx cA vx cv cH
      cfv cmpt cF cG cR cof co vx cA cB cC cR co cmpt wph cH cA wfn cH vx cA vx
      cv cH cfv cmpt wceq offveq.4 vx cA cH dffn5 sylib wph vx cA cA cB cC cR
      cA cF cG cV cV offveq.2 offveq.3 offveq.1 offveq.1 cA inidm offveq.5
      offveq.6 offval eqeq12d wph vx cv cH cfv cvv wcel vx cA wral vx cA vx cv
      cH cfv cmpt vx cA cB cC cR co cmpt wceq vx cv cH cfv cB cC cR co wceq vx
      cA wral wb wph vx cv cH cfv cvv wcel vx cA vx cv cH cfv cvv wcel wph vx
      cv cH fvex a1i ralrimivw vx cA vx cv cH cfv cB cC cR co cvv mpteqb syl
      bitrd $.
  $}

  ${
    ofc1.1 $e |- ( ph -> A e. V ) $.
    ofc1.2 $e |- ( ph -> B e. W ) $.
    ofc1.3 $e |- ( ph -> F Fn A ) $.
    ofc1.4 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
    $( Left operation by a constant.  (Contributed by Mario Carneiro,
       24-Jul-2014.) $)
    ofc1 $p |- ( ( ph /\ X e. A ) ->
      ( ( ( A X. { B } ) oF R F ) ` X ) = ( B R C ) ) $=
      wph cA cA cB cC cR cA cA cB csn cxp cF cV cV cX wph cB cW wcel cA cB csn
      cxp cA wfn ofc1.2 cA cB cW fnconstg syl ofc1.3 ofc1.1 ofc1.1 cA inidm wph
      cB cW wcel cX cA wcel cX cA cB csn cxp cfv cB wceq ofc1.2 cA cB cX cW
      fvconst2g sylan ofc1.4 ofval $.
  $}

  ${
    ofc2.1 $e |- ( ph -> A e. V ) $.
    ofc2.2 $e |- ( ph -> B e. W ) $.
    ofc2.3 $e |- ( ph -> F Fn A ) $.
    ofc2.4 $e |- ( ( ph /\ X e. A ) -> ( F ` X ) = C ) $.
    $( Right operation by a constant.  (Contributed by NM, 7-Oct-2014.) $)
    ofc2 $p |- ( ( ph /\ X e. A ) ->
      ( ( F oF R ( A X. { B } ) ) ` X ) = ( C R B ) ) $=
      wph cA cA cC cB cR cA cF cA cB csn cxp cV cV cX ofc2.3 wph cB cW wcel cA
      cB csn cxp cA wfn ofc2.2 cA cB cW fnconstg syl ofc2.1 ofc2.1 cA inidm
      ofc2.4 wph cB cW wcel cX cA wcel cX cA cB csn cxp cfv cB wceq ofc2.2 cA
      cB cX cW fvconst2g sylan ofval $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x ph $.  $d x R $.  $d x W $.
    $d x X $.
    ofc12.1 $e |- ( ph -> A e. V ) $.
    ofc12.2 $e |- ( ph -> B e. W ) $.
    ofc12.3 $e |- ( ph -> C e. X ) $.
    $( Function operation on two constant functions.  (Contributed by Mario
       Carneiro, 28-Jul-2014.) $)
    ofc12 $p |- ( ph ->
      ( ( A X. { B } ) oF R ( A X. { C } ) ) = ( A X. { ( B R C ) } ) ) $=
      wph cA cB csn cxp cA cC csn cxp cR cof co vx cA cB cC cR co cmpt cA cB cC
      cR co csn cxp wph vx cA cB cC cR cA cB csn cxp cA cC csn cxp cV cW cX
      ofc12.1 wph cB cW wcel vx cv cA wcel ofc12.2 adantr wph cC cX wcel vx cv
      cA wcel ofc12.3 adantr cA cB csn cxp vx cA cB cmpt wceq wph vx cA cB
      fconstmpt a1i cA cC csn cxp vx cA cC cmpt wceq wph vx cA cC fconstmpt a1i
      offval2 vx cA cB cC cR co fconstmpt syl6eqr $.
  $}

  ${
    $d w x B $.  $d w x C $.  $d w x y z F $.  $d w x y z G $.  $d w x y z H $.
    $d w x y z O $.  $d w x y z P $.  $d w x y z ph $.  $d w x y z R $.
    $d w A $.  $d w x y z S $.  $d w x y z T $.  $d w x y z U $.
    caofref.1 $e |- ( ph -> A e. V ) $.
    caofref.2 $e |- ( ph -> F : A --> S ) $.
    ${
      caofref.3 $e |- ( ( ph /\ x e. S ) -> x R x ) $.
      $( Transfer a reflexive law to the function relation.  (Contributed by
         Mario Carneiro, 28-Jul-2014.) $)
      caofref $p |- ( ph -> F oR R F ) $=
        wph cF cF cR cofr wbr vw cv cF cfv vw cv cF cfv cR wbr vw cA wral wph
        vw cv cF cfv vw cv cF cfv cR wbr vw cA wph vw cv cA wcel wa vw cv cF
        cfv cS wcel vx cv vx cv cR wbr vx cS wral vw cv cF cfv vw cv cF cfv cR
        wbr wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA cS
        vw cv cF ffvelrn sylan wph vx cv vx cv cR wbr vx cS wral vw cv cA wcel
        wph vx cv vx cv cR wbr vx cS caofref.3 ralrimiva adantr vx cv vx cv cR
        wbr vw cv cF cfv vw cv cF cfv cR wbr vx vw cv cF cfv cS vx cv vw cv cF
        cfv wceq vx cv vw cv cF cfv vx cv vw cv cF cfv cR vx cv vw cv cF cfv
        wceq id vx cv vw cv cF cfv wceq id breq12d rspcv sylc ralrimiva wph vw
        cA cA vw cv cF cfv vw cv cF cfv cR cA cF cF cV cV wph cA cS cF wf cF cA
        wfn caofref.2 cA cS cF ffn syl wph cA cS cF wf cF cA wfn caofref.2 cA
        cS cF ffn syl caofref.1 caofref.1 cA inidm wph vw cv cA wcel wa vw cv
        cF cfv eqidd wph vw cv cA wcel wa vw cv cF cfv eqidd ofrfval mpbird $.
    $}

    ${
      $d v A $.  $d v F $.  $d x v N $.  $d v S $.  $d v ph $.  $d v w $.
      caofinv.3 $e |- ( ph -> B e. W ) $.
      caofinv.4 $e |- ( ph -> N : S --> S ) $.
      caofinv.5 $e |- ( ph -> G = ( v e. A |-> ( N ` ( F ` v ) ) ) ) $.
      ${
        caofinvl.6 $e |- ( ( ph /\ x e. S ) -> ( ( N ` x ) R x ) = B ) $.
        $( Transfer a left inverse law to the function operation.  (Contributed
           by NM, 22-Oct-2014.) $)
        caofinvl $p |- ( ph -> ( G oF R F ) = ( A X. { B } ) ) $=
          wph cG cF cR cof co vw cA cB cmpt cA cB csn cxp wph cG cF cR cof co
          vw cA vw cv cG cfv vw cv cF cfv cR co cmpt vw cA cB cmpt wph vw cA vw
          cv cG cfv vw cv cF cfv cR cG cF cV cS cS caofref.1 wph cA cS cG wf vw
          cv cA wcel vw cv cG cfv cS wcel wph cA cS cG wf cA cS vv cA vv cv cF
          cfv cN cfv cmpt wf wph vv cA vv cv cF cfv cN cfv cS vv cA vv cv cF
          cfv cN cfv cmpt wph vv cv cA wcel wa cS cS cN wf vv cv cF cfv cS wcel
          vv cv cF cfv cN cfv cS wcel wph cS cS cN wf vv cv cA wcel caofinv.4
          adantr wph cA cS cF wf vv cv cA wcel vv cv cF cfv cS wcel caofref.2
          cA cS vv cv cF ffvelrn sylan cS cS vv cv cF cfv cN ffvelrn syl2anc vv
          cA vv cv cF cfv cN cfv cmpt eqid fmptd wph cA cS cG vv cA vv cv cF
          cfv cN cfv cmpt caofinv.5 feq1d mpbird cA cS vw cv cG ffvelrn sylan
          wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw
          cv cF ffvelrn sylan wph cG cA wfn cG vw cA vw cv cG cfv cmpt wceq wph
          cG cA wfn vv cA vv cv cF cfv cN cfv cmpt cA wfn vv cA vv cv cF cfv cN
          cfv vv cA vv cv cF cfv cN cfv cmpt vv cv cF cfv cN fvex vv cA vv cv
          cF cfv cN cfv cmpt eqid fnmpti wph cA cG vv cA vv cv cF cfv cN cfv
          cmpt caofinv.5 fneq1d mpbiri vw cA cG dffn5 sylib wph vw cA cS cF
          caofref.2 feqmptd offval2 wph vw cA vw cv cG cfv vw cv cF cfv cR co
          cB wph vw cv cA wcel wa vw cv cG cfv vw cv cF cfv cR co vw cv cF cfv
          cN cfv vw cv cF cfv cR co cB wph vw cv cA wcel wa vw cv cG cfv vw cv
          cF cfv cN cfv vw cv cF cfv cR wph vw cv cA wcel vw cv cG cfv vw cv vv
          cA vv cv cF cfv cN cfv cmpt cfv vw cv cF cfv cN cfv wph vw cv cG vv
          cA vv cv cF cfv cN cfv cmpt caofinv.5 fveq1d vv vw cv vv cv cF cfv cN
          cfv vw cv cF cfv cN cfv cA vv cA vv cv cF cfv cN cfv cmpt vv cv vw cv
          wceq vv cv cF cfv vw cv cF cfv cN vv cv vw cv cF fveq2 fveq2d vv cA
          vv cv cF cfv cN cfv cmpt eqid vw cv cF cfv cN fvex fvmpt sylan9eq
          oveq1d wph vw cv cA wcel wa vw cv cF cfv cS wcel vx cv cN cfv vx cv
          cR co cB wceq vx cS wral vw cv cF cfv cN cfv vw cv cF cfv cR co cB
          wceq wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA
          cS vw cv cF ffvelrn sylan wph vx cv cN cfv vx cv cR co cB wceq vx cS
          wral vw cv cA wcel wph vx cv cN cfv vx cv cR co cB wceq vx cS
          caofinvl.6 ralrimiva adantr vx cv cN cfv vx cv cR co cB wceq vw cv cF
          cfv cN cfv vw cv cF cfv cR co cB wceq vx vw cv cF cfv cS vx cv vw cv
          cF cfv wceq vx cv cN cfv vx cv cR co vw cv cF cfv cN cfv vw cv cF cfv
          cR co cB vx cv vw cv cF cfv wceq vx cv cN cfv vw cv cF cfv cN cfv vx
          cv vw cv cF cfv cR vx cv vw cv cF cfv cN fveq2 vx cv vw cv cF cfv
          wceq id oveq12d eqeq1d rspcva syl2anc eqtrd mpteq2dva eqtrd vw cA cB
          fconstmpt syl6eqr $.
      $}
    $}

    ${
      caofid0.3 $e |- ( ph -> B e. W ) $.
      ${
        caofid0l.5 $e |- ( ( ph /\ x e. S ) -> ( B R x ) = x ) $.
        $( Transfer a left identity law to the function operation.
           (Contributed by NM, 21-Oct-2014.) $)
        caofid0l $p |- ( ph -> ( ( A X. { B } ) oF R F ) = F ) $=
          wph vw cA cB vw cv cF cfv cR cA cB csn cxp cF cF cV caofref.1 wph cB
          cW wcel cA cB csn cxp cA wfn caofid0.3 cA cB cW fnconstg syl wph cA
          cS cF wf cF cA wfn caofref.2 cA cS cF ffn syl wph cA cS cF wf cF cA
          wfn caofref.2 cA cS cF ffn syl wph cB cW wcel vw cv cA wcel vw cv cA
          cB csn cxp cfv cB wceq caofid0.3 cA cB vw cv cW fvconst2g sylan wph
          vw cv cA wcel wa vw cv cF cfv eqidd wph vw cv cA wcel vw cv cF cfv cS
          wcel cB vw cv cF cfv cR co vw cv cF cfv wceq wph cA cS cF wf vw cv cA
          wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn sylan wph
          cB vx cv cR co vx cv wceq vx cS wral vw cv cF cfv cS wcel cB vw cv cF
          cfv cR co vw cv cF cfv wceq wph cB vx cv cR co vx cv wceq vx cS
          caofid0l.5 ralrimiva cB vx cv cR co vx cv wceq cB vw cv cF cfv cR co
          vw cv cF cfv wceq vx vw cv cF cfv cS vx cv vw cv cF cfv wceq cB vx cv
          cR co cB vw cv cF cfv cR co vx cv vw cv cF cfv vx cv vw cv cF cfv cB
          cR oveq2 vx cv vw cv cF cfv wceq id eqeq12d rspccva sylan syldan
          offveq $.
      $}

      ${
        caofid0r.5 $e |- ( ( ph /\ x e. S ) -> ( x R B ) = x ) $.
        $( Transfer a right identity law to the function operation.
           (Contributed by NM, 21-Oct-2014.) $)
        caofid0r $p |- ( ph -> ( F oF R ( A X. { B } ) ) = F ) $=
          wph vw cA vw cv cF cfv cB cR cF cA cB csn cxp cF cV caofref.1 wph cA
          cS cF wf cF cA wfn caofref.2 cA cS cF ffn syl wph cB cW wcel cA cB
          csn cxp cA wfn caofid0.3 cA cB cW fnconstg syl wph cA cS cF wf cF cA
          wfn caofref.2 cA cS cF ffn syl wph vw cv cA wcel wa vw cv cF cfv
          eqidd wph cB cW wcel vw cv cA wcel vw cv cA cB csn cxp cfv cB wceq
          caofid0.3 cA cB vw cv cW fvconst2g sylan wph vw cv cA wcel vw cv cF
          cfv cS wcel vw cv cF cfv cB cR co vw cv cF cfv wceq wph cA cS cF wf
          vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn
          sylan wph vx cv cB cR co vx cv wceq vx cS wral vw cv cF cfv cS wcel
          vw cv cF cfv cB cR co vw cv cF cfv wceq wph vx cv cB cR co vx cv wceq
          vx cS caofid0r.5 ralrimiva vx cv cB cR co vx cv wceq vw cv cF cfv cB
          cR co vw cv cF cfv wceq vx vw cv cF cfv cS vx cv vw cv cF cfv wceq vx
          cv cB cR co vw cv cF cfv cB cR co vx cv vw cv cF cfv vx cv vw cv cF
          cfv cB cR oveq1 vx cv vw cv cF cfv wceq id eqeq12d rspccva sylan
          syldan offveq $.
      $}

      caofid1.4 $e |- ( ph -> C e. X ) $.
      ${
        caofid1.5 $e |- ( ( ph /\ x e. S ) -> ( x R B ) = C ) $.
        $( Transfer a right absorption law to the function operation.
           (Contributed by Mario Carneiro, 28-Jul-2014.) $)
        caofid1 $p |- ( ph -> ( F oF R ( A X. { B } ) ) = ( A X. { C } ) ) $=
          wph vw cA vw cv cF cfv cB cR cF cA cB csn cxp cA cC csn cxp cV
          caofref.1 wph cA cS cF wf cF cA wfn caofref.2 cA cS cF ffn syl wph cB
          cW wcel cA cB csn cxp cA wfn caofid0.3 cA cB cW fnconstg syl wph cC
          cX wcel cA cC csn cxp cA wfn caofid1.4 cA cC cX fnconstg syl wph vw
          cv cA wcel wa vw cv cF cfv eqidd wph cB cW wcel vw cv cA wcel vw cv
          cA cB csn cxp cfv cB wceq caofid0.3 cA cB vw cv cW fvconst2g sylan
          wph vw cv cA wcel wa vw cv cF cfv cB cR co cC vw cv cA cC csn cxp cfv
          wph vw cv cA wcel vw cv cF cfv cS wcel vw cv cF cfv cB cR co cC wceq
          wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw
          cv cF ffvelrn sylan wph vx cv cB cR co cC wceq vx cS wral vw cv cF
          cfv cS wcel vw cv cF cfv cB cR co cC wceq wph vx cv cB cR co cC wceq
          vx cS caofid1.5 ralrimiva vx cv cB cR co cC wceq vw cv cF cfv cB cR
          co cC wceq vx vw cv cF cfv cS vx cv vw cv cF cfv wceq vx cv cB cR co
          vw cv cF cfv cB cR co cC vx cv vw cv cF cfv cB cR oveq1 eqeq1d
          rspccva sylan syldan wph cC cX wcel vw cv cA wcel vw cv cA cC csn cxp
          cfv cC wceq caofid1.4 cA cC vw cv cX fvconst2g sylan eqtr4d offveq $.
      $}

      caofid2.5 $e |- ( ( ph /\ x e. S ) -> ( B R x ) = C ) $.
      $( Transfer a right absorption law to the function operation.
         (Contributed by Mario Carneiro, 28-Jul-2014.) $)
      caofid2 $p |- ( ph -> ( ( A X. { B } ) oF R F ) = ( A X. { C } ) ) $=
        wph vw cA cB vw cv cF cfv cR cA cB csn cxp cF cA cC csn cxp cV
        caofref.1 wph cB cW wcel cA cB csn cxp cA wfn caofid0.3 cA cB cW
        fnconstg syl wph cA cS cF wf cF cA wfn caofref.2 cA cS cF ffn syl wph
        cC cX wcel cA cC csn cxp cA wfn caofid1.4 cA cC cX fnconstg syl wph cB
        cW wcel vw cv cA wcel vw cv cA cB csn cxp cfv cB wceq caofid0.3 cA cB
        vw cv cW fvconst2g sylan wph vw cv cA wcel wa vw cv cF cfv eqidd wph vw
        cv cA wcel wa cB vw cv cF cfv cR co cC vw cv cA cC csn cxp cfv wph vw
        cv cA wcel vw cv cF cfv cS wcel cB vw cv cF cfv cR co cC wceq wph cA cS
        cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF
        ffvelrn sylan wph cB vx cv cR co cC wceq vx cS wral vw cv cF cfv cS
        wcel cB vw cv cF cfv cR co cC wceq wph cB vx cv cR co cC wceq vx cS
        caofid2.5 ralrimiva cB vx cv cR co cC wceq cB vw cv cF cfv cR co cC
        wceq vx vw cv cF cfv cS vx cv vw cv cF cfv wceq cB vx cv cR co cB vw cv
        cF cfv cR co cC vx cv vw cv cF cfv cB cR oveq2 eqeq1d rspccva sylan
        syldan wph cC cX wcel vw cv cA wcel vw cv cA cC csn cxp cfv cC wceq
        caofid1.4 cA cC vw cv cX fvconst2g sylan eqtr4d offveq $.
    $}

    caofcom.3 $e |- ( ph -> G : A --> S ) $.
    ${
      caofcom.4 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                        ( x R y ) = ( y R x ) ) $.
      $( Transfer a commutative law to the function operation.  (Contributed by
         Mario Carneiro, 26-Jul-2014.) $)
      caofcom $p |- ( ph -> ( F oF R G ) = ( G oF R F ) ) $=
        wph vw cA vw cv cF cfv vw cv cG cfv cR co cmpt vw cA vw cv cG cfv vw cv
        cF cfv cR co cmpt cF cG cR cof co cG cF cR cof co wph vw cA vw cv cF
        cfv vw cv cG cfv cR co vw cv cG cfv vw cv cF cfv cR co wph vw cv cA
        wcel vw cv cF cfv cS wcel vw cv cG cfv cS wcel wa vw cv cF cfv vw cv cG
        cfv cR co vw cv cG cfv vw cv cF cfv cR co wceq wph vw cv cA wcel wa vw
        cv cF cfv cS wcel vw cv cG cfv cS wcel wph cA cS cF wf vw cv cA wcel vw
        cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn sylan wph cA cS cG
        wf vw cv cA wcel vw cv cG cfv cS wcel caofcom.3 cA cS vw cv cG ffvelrn
        sylan jca wph vx vy vw cv cF cfv vw cv cG cfv cS cR caofcom.4 caovcomg
        syldan mpteq2dva wph vw cA vw cv cF cfv vw cv cG cfv cR cF cG cV cS cS
        caofref.1 wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2
        cA cS vw cv cF ffvelrn sylan wph cA cS cG wf vw cv cA wcel vw cv cG cfv
        cS wcel caofcom.3 cA cS vw cv cG ffvelrn sylan wph vw cA cS cF
        caofref.2 feqmptd wph vw cA cS cG caofcom.3 feqmptd offval2 wph vw cA
        vw cv cG cfv vw cv cF cfv cR cG cF cV cS cS caofref.1 wph cA cS cG wf
        vw cv cA wcel vw cv cG cfv cS wcel caofcom.3 cA cS vw cv cG ffvelrn
        sylan wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS wcel caofref.2 cA
        cS vw cv cF ffvelrn sylan wph vw cA cS cG caofcom.3 feqmptd wph vw cA
        cS cF caofref.2 feqmptd offval2 3eqtr4d $.
    $}

    ${
      caofrss.4 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                        ( x R y -> x T y ) ) $.
      $( Transfer a relation subset law to the function relation.  (Contributed
         by Mario Carneiro, 28-Jul-2014.) $)
      caofrss $p |- ( ph -> ( F oR R G -> F oR T G ) ) $=
        wph vw cv cF cfv vw cv cG cfv cR wbr vw cA wral vw cv cF cfv vw cv cG
        cfv cT wbr vw cA wral cF cG cR cofr wbr cF cG cT cofr wbr wph vw cv cF
        cfv vw cv cG cfv cR wbr vw cv cF cfv vw cv cG cfv cT wbr vw cA wph vw
        cv cA wcel wa vw cv cF cfv cS wcel vw cv cG cfv cS wcel vx cv vy cv cR
        wbr vx cv vy cv cT wbr wi vy cS wral vx cS wral vw cv cF cfv vw cv cG
        cfv cR wbr vw cv cF cfv vw cv cG cfv cT wbr wi wph cA cS cF wf vw cv cA
        wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn sylan wph cA
        cS cG wf vw cv cA wcel vw cv cG cfv cS wcel caofcom.3 cA cS vw cv cG
        ffvelrn sylan wph vx cv vy cv cR wbr vx cv vy cv cT wbr wi vy cS wral
        vx cS wral vw cv cA wcel wph vx cv vy cv cR wbr vx cv vy cv cT wbr wi
        vx vy cS cS caofrss.4 ralrimivva adantr vx cv vy cv cR wbr vx cv vy cv
        cT wbr wi vw cv cF cfv vw cv cG cfv cR wbr vw cv cF cfv vw cv cG cfv cT
        wbr wi vw cv cF cfv vy cv cR wbr vw cv cF cfv vy cv cT wbr wi vx vy vw
        cv cF cfv vw cv cG cfv cS cS vx cv vw cv cF cfv wceq vx cv vy cv cR wbr
        vw cv cF cfv vy cv cR wbr vx cv vy cv cT wbr vw cv cF cfv vy cv cT wbr
        vx cv vw cv cF cfv vy cv cR breq1 vx cv vw cv cF cfv vy cv cT breq1
        imbi12d vy cv vw cv cG cfv wceq vw cv cF cfv vy cv cR wbr vw cv cF cfv
        vw cv cG cfv cR wbr vw cv cF cfv vy cv cT wbr vw cv cF cfv vw cv cG cfv
        cT wbr vy cv vw cv cG cfv vw cv cF cfv cR breq2 vy cv vw cv cG cfv vw
        cv cF cfv cT breq2 imbi12d rspc2va syl21anc ralimdva wph vw cA cA vw cv
        cF cfv vw cv cG cfv cR cA cF cG cV cV wph cA cS cF wf cF cA wfn
        caofref.2 cA cS cF ffn syl wph cA cS cG wf cG cA wfn caofcom.3 cA cS cG
        ffn syl caofref.1 caofref.1 cA inidm wph vw cv cA wcel wa vw cv cF cfv
        eqidd wph vw cv cA wcel wa vw cv cG cfv eqidd ofrfval wph vw cA cA vw
        cv cF cfv vw cv cG cfv cT cA cF cG cV cV wph cA cS cF wf cF cA wfn
        caofref.2 cA cS cF ffn syl wph cA cS cG wf cG cA wfn caofcom.3 cA cS cG
        ffn syl caofref.1 caofref.1 cA inidm wph vw cv cA wcel wa vw cv cF cfv
        eqidd wph vw cv cA wcel wa vw cv cG cfv eqidd ofrfval 3imtr4d $.
    $}

    caofass.4 $e |- ( ph -> H : A --> S ) $.
    ${
      caofass.5 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
                        ( ( x R y ) T z ) = ( x O ( y P z ) ) ) $.
      $( Transfer an associative law to the function operation.  (Contributed
         by Mario Carneiro, 26-Jul-2014.) $)
      caofass $p |- ( ph ->
        ( ( F oF R G ) oF T H ) = ( F oF O ( G oF P H ) ) ) $=
        wph vw cA vw cv cF cfv vw cv cG cfv cR co vw cv cH cfv cT co cmpt vw cA
        vw cv cF cfv vw cv cG cfv vw cv cH cfv cP co cO co cmpt cF cG cR cof co
        cH cT cof co cF cG cH cP cof co cO cof co wph vw cA vw cv cF cfv vw cv
        cG cfv cR co vw cv cH cfv cT co vw cv cF cfv vw cv cG cfv vw cv cH cfv
        cP co cO co wph vw cv cA wcel wa vx cv vy cv cR co vz cv cT co vx cv vy
        cv vz cv cP co cO co wceq vz cS wral vy cS wral vx cS wral vw cv cF cfv
        vw cv cG cfv cR co vw cv cH cfv cT co vw cv cF cfv vw cv cG cfv vw cv
        cH cfv cP co cO co wceq wph vx cv vy cv cR co vz cv cT co vx cv vy cv
        vz cv cP co cO co wceq vz cS wral vy cS wral vx cS wral vw cv cA wcel
        wph vx cv vy cv cR co vz cv cT co vx cv vy cv vz cv cP co cO co wceq vx
        vy vz cS cS cS caofass.5 ralrimivvva adantr wph vw cv cA wcel wa vw cv
        cF cfv cS wcel vw cv cG cfv cS wcel vw cv cH cfv cS wcel vx cv vy cv cR
        co vz cv cT co vx cv vy cv vz cv cP co cO co wceq vz cS wral vy cS wral
        vx cS wral vw cv cF cfv vw cv cG cfv cR co vw cv cH cfv cT co vw cv cF
        cfv vw cv cG cfv vw cv cH cfv cP co cO co wceq wi wph cA cS cF wf vw cv
        cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn sylan wph
        cA cS cG wf vw cv cA wcel vw cv cG cfv cS wcel caofcom.3 cA cS vw cv cG
        ffvelrn sylan wph cA cS cH wf vw cv cA wcel vw cv cH cfv cS wcel
        caofass.4 cA cS vw cv cH ffvelrn sylan vx cv vy cv cR co vz cv cT co vx
        cv vy cv vz cv cP co cO co wceq vw cv cF cfv vw cv cG cfv cR co vw cv
        cH cfv cT co vw cv cF cfv vw cv cG cfv vw cv cH cfv cP co cO co wceq vw
        cv cF cfv vy cv cR co vz cv cT co vw cv cF cfv vy cv vz cv cP co cO co
        wceq vw cv cF cfv vw cv cG cfv cR co vz cv cT co vw cv cF cfv vw cv cG
        cfv vz cv cP co cO co wceq vx vy vz vw cv cF cfv vw cv cG cfv vw cv cH
        cfv cS cS cS vx cv vw cv cF cfv wceq vx cv vy cv cR co vz cv cT co vw
        cv cF cfv vy cv cR co vz cv cT co vx cv vy cv vz cv cP co cO co vw cv
        cF cfv vy cv vz cv cP co cO co vx cv vw cv cF cfv wceq vx cv vy cv cR
        co vw cv cF cfv vy cv cR co vz cv cT vx cv vw cv cF cfv vy cv cR oveq1
        oveq1d vx cv vw cv cF cfv vy cv vz cv cP co cO oveq1 eqeq12d vy cv vw
        cv cG cfv wceq vw cv cF cfv vy cv cR co vz cv cT co vw cv cF cfv vw cv
        cG cfv cR co vz cv cT co vw cv cF cfv vy cv vz cv cP co cO co vw cv cF
        cfv vw cv cG cfv vz cv cP co cO co vy cv vw cv cG cfv wceq vw cv cF cfv
        vy cv cR co vw cv cF cfv vw cv cG cfv cR co vz cv cT vy cv vw cv cG cfv
        vw cv cF cfv cR oveq2 oveq1d vy cv vw cv cG cfv wceq vy cv vz cv cP co
        vw cv cG cfv vz cv cP co vw cv cF cfv cO vy cv vw cv cG cfv vz cv cP
        oveq1 oveq2d eqeq12d vz cv vw cv cH cfv wceq vw cv cF cfv vw cv cG cfv
        cR co vz cv cT co vw cv cF cfv vw cv cG cfv cR co vw cv cH cfv cT co vw
        cv cF cfv vw cv cG cfv vz cv cP co cO co vw cv cF cfv vw cv cG cfv vw
        cv cH cfv cP co cO co vz cv vw cv cH cfv vw cv cF cfv vw cv cG cfv cR
        co cT oveq2 vz cv vw cv cH cfv wceq vw cv cG cfv vz cv cP co vw cv cG
        cfv vw cv cH cfv cP co vw cv cF cfv cO vz cv vw cv cH cfv vw cv cG cfv
        cP oveq2 oveq2d eqeq12d rspc3v syl3anc mpd mpteq2dva wph vw cA vw cv cF
        cfv vw cv cG cfv cR co vw cv cH cfv cT cF cG cR cof co cH cV cvv cS
        caofref.1 vw cv cF cfv vw cv cG cfv cR co cvv wcel wph vw cv cA wcel wa
        vw cv cF cfv vw cv cG cfv cR ovex a1i wph cA cS cH wf vw cv cA wcel vw
        cv cH cfv cS wcel caofass.4 cA cS vw cv cH ffvelrn sylan wph vw cA vw
        cv cF cfv vw cv cG cfv cR cF cG cV cS cS caofref.1 wph cA cS cF wf vw
        cv cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn sylan
        wph cA cS cG wf vw cv cA wcel vw cv cG cfv cS wcel caofcom.3 cA cS vw
        cv cG ffvelrn sylan wph vw cA cS cF caofref.2 feqmptd wph vw cA cS cG
        caofcom.3 feqmptd offval2 wph vw cA cS cH caofass.4 feqmptd offval2 wph
        vw cA vw cv cF cfv vw cv cG cfv vw cv cH cfv cP co cO cF cG cH cP cof
        co cV cS cvv caofref.1 wph cA cS cF wf vw cv cA wcel vw cv cF cfv cS
        wcel caofref.2 cA cS vw cv cF ffvelrn sylan vw cv cG cfv vw cv cH cfv
        cP co cvv wcel wph vw cv cA wcel wa vw cv cG cfv vw cv cH cfv cP ovex
        a1i wph vw cA cS cF caofref.2 feqmptd wph vw cA vw cv cG cfv vw cv cH
        cfv cP cG cH cV cS cS caofref.1 wph cA cS cG wf vw cv cA wcel vw cv cG
        cfv cS wcel caofcom.3 cA cS vw cv cG ffvelrn sylan wph cA cS cH wf vw
        cv cA wcel vw cv cH cfv cS wcel caofass.4 cA cS vw cv cH ffvelrn sylan
        wph vw cA cS cG caofcom.3 feqmptd wph vw cA cS cH caofass.4 feqmptd
        offval2 offval2 3eqtr4d $.
    $}

    ${
      caoftrn.5 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
                        ( ( x R y /\ y T z ) -> x U z ) ) $.
      $( Transfer a transitivity law to the function relation.  (Contributed by
         Mario Carneiro, 28-Jul-2014.) $)
      caoftrn $p |- ( ph -> ( ( F oR R G /\ G oR T H ) -> F oR U H ) ) $=
        wph vw cv cF cfv vw cv cG cfv cR wbr vw cv cG cfv vw cv cH cfv cT wbr
        wa vw cA wral vw cv cF cfv vw cv cH cfv cU wbr vw cA wral cF cG cR cofr
        wbr cG cH cT cofr wbr wa cF cH cU cofr wbr wph vw cv cF cfv vw cv cG
        cfv cR wbr vw cv cG cfv vw cv cH cfv cT wbr wa vw cv cF cfv vw cv cH
        cfv cU wbr vw cA wph vw cv cA wcel wa vx cv vy cv cR wbr vy cv vz cv cT
        wbr wa vx cv vz cv cU wbr wi vz cS wral vy cS wral vx cS wral vw cv cF
        cfv vw cv cG cfv cR wbr vw cv cG cfv vw cv cH cfv cT wbr wa vw cv cF
        cfv vw cv cH cfv cU wbr wi wph vx cv vy cv cR wbr vy cv vz cv cT wbr wa
        vx cv vz cv cU wbr wi vz cS wral vy cS wral vx cS wral vw cv cA wcel
        wph vx cv vy cv cR wbr vy cv vz cv cT wbr wa vx cv vz cv cU wbr wi vx
        vy vz cS cS cS caoftrn.5 ralrimivvva adantr wph vw cv cA wcel wa vw cv
        cF cfv cS wcel vw cv cG cfv cS wcel vw cv cH cfv cS wcel vx cv vy cv cR
        wbr vy cv vz cv cT wbr wa vx cv vz cv cU wbr wi vz cS wral vy cS wral
        vx cS wral vw cv cF cfv vw cv cG cfv cR wbr vw cv cG cfv vw cv cH cfv
        cT wbr wa vw cv cF cfv vw cv cH cfv cU wbr wi wi wph cA cS cF wf vw cv
        cA wcel vw cv cF cfv cS wcel caofref.2 cA cS vw cv cF ffvelrn sylan wph
        cA cS cG wf vw cv cA wcel vw cv cG cfv cS wcel caofcom.3 cA cS vw cv cG
        ffvelrn sylan wph cA cS cH wf vw cv cA wcel vw cv cH cfv cS wcel
        caofass.4 cA cS vw cv cH ffvelrn sylan vx cv vy cv cR wbr vy cv vz cv
        cT wbr wa vx cv vz cv cU wbr wi vw cv cF cfv vw cv cG cfv cR wbr vw cv
        cG cfv vw cv cH cfv cT wbr wa vw cv cF cfv vw cv cH cfv cU wbr wi vw cv
        cF cfv vy cv cR wbr vy cv vz cv cT wbr wa vw cv cF cfv vz cv cU wbr wi
        vw cv cF cfv vw cv cG cfv cR wbr vw cv cG cfv vz cv cT wbr wa vw cv cF
        cfv vz cv cU wbr wi vx vy vz vw cv cF cfv vw cv cG cfv vw cv cH cfv cS
        cS cS vx cv vw cv cF cfv wceq vx cv vy cv cR wbr vy cv vz cv cT wbr wa
        vw cv cF cfv vy cv cR wbr vy cv vz cv cT wbr wa vx cv vz cv cU wbr vw
        cv cF cfv vz cv cU wbr vx cv vw cv cF cfv wceq vx cv vy cv cR wbr vw cv
        cF cfv vy cv cR wbr vy cv vz cv cT wbr vx cv vw cv cF cfv vy cv cR
        breq1 anbi1d vx cv vw cv cF cfv vz cv cU breq1 imbi12d vy cv vw cv cG
        cfv wceq vw cv cF cfv vy cv cR wbr vy cv vz cv cT wbr wa vw cv cF cfv
        vw cv cG cfv cR wbr vw cv cG cfv vz cv cT wbr wa vw cv cF cfv vz cv cU
        wbr vy cv vw cv cG cfv wceq vw cv cF cfv vy cv cR wbr vw cv cF cfv vw
        cv cG cfv cR wbr vy cv vz cv cT wbr vw cv cG cfv vz cv cT wbr vy cv vw
        cv cG cfv vw cv cF cfv cR breq2 vy cv vw cv cG cfv vz cv cT breq1
        anbi12d imbi1d vz cv vw cv cH cfv wceq vw cv cF cfv vw cv cG cfv cR wbr
        vw cv cG cfv vz cv cT wbr wa vw cv cF cfv vw cv cG cfv cR wbr vw cv cG
        cfv vw cv cH cfv cT wbr wa vw cv cF cfv vz cv cU wbr vw cv cF cfv vw cv
        cH cfv cU wbr vz cv vw cv cH cfv wceq vw cv cG cfv vz cv cT wbr vw cv
        cG cfv vw cv cH cfv cT wbr vw cv cF cfv vw cv cG cfv cR wbr vz cv vw cv
        cH cfv vw cv cG cfv cT breq2 anbi2d vz cv vw cv cH cfv vw cv cF cfv cU
        breq2 imbi12d rspc3v syl3anc mpd ralimdva wph cF cG cR cofr wbr cG cH
        cT cofr wbr wa vw cv cF cfv vw cv cG cfv cR wbr vw cA wral vw cv cG cfv
        vw cv cH cfv cT wbr vw cA wral wa vw cv cF cfv vw cv cG cfv cR wbr vw
        cv cG cfv vw cv cH cfv cT wbr wa vw cA wral wph cF cG cR cofr wbr vw cv
        cF cfv vw cv cG cfv cR wbr vw cA wral cG cH cT cofr wbr vw cv cG cfv vw
        cv cH cfv cT wbr vw cA wral wph vw cA cA vw cv cF cfv vw cv cG cfv cR
        cA cF cG cV cV wph cA cS cF wf cF cA wfn caofref.2 cA cS cF ffn syl wph
        cA cS cG wf cG cA wfn caofcom.3 cA cS cG ffn syl caofref.1 caofref.1 cA
        inidm wph vw cv cA wcel wa vw cv cF cfv eqidd wph vw cv cA wcel wa vw
        cv cG cfv eqidd ofrfval wph vw cA cA vw cv cG cfv vw cv cH cfv cT cA cG
        cH cV cV wph cA cS cG wf cG cA wfn caofcom.3 cA cS cG ffn syl wph cA cS
        cH wf cH cA wfn caofass.4 cA cS cH ffn syl caofref.1 caofref.1 cA inidm
        wph vw cv cA wcel wa vw cv cG cfv eqidd wph vw cv cA wcel wa vw cv cH
        cfv eqidd ofrfval anbi12d vw cv cF cfv vw cv cG cfv cR wbr vw cv cG cfv
        vw cv cH cfv cT wbr vw cA r19.26 syl6bbr wph vw cA cA vw cv cF cfv vw
        cv cH cfv cU cA cF cH cV cV wph cA cS cF wf cF cA wfn caofref.2 cA cS
        cF ffn syl wph cA cS cH wf cH cA wfn caofass.4 cA cS cH ffn syl
        caofref.1 caofref.1 cA inidm wph vw cv cA wcel wa vw cv cF cfv eqidd
        wph vw cv cA wcel wa vw cv cH cfv eqidd ofrfval 3imtr4d $.
    $}
  $}

  ${
    $d w x y z A $.  $d w x y z F $.  $d w x y z G $.  $d w x y z ph $.
    $d w x y z H $.  $d w x y z K $.  $d w x y z O $.  $d w x y z R $.
    $d w x y z S $.  $d w x y z T $.
    caofdi.1 $e |- ( ph -> A e. V ) $.
    caofdi.2 $e |- ( ph -> F : A --> K ) $.
    caofdi.3 $e |- ( ph -> G : A --> S ) $.
    caofdi.4 $e |- ( ph -> H : A --> S ) $.
    ${
      caofdi.5 $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) ->
                          ( x T ( y R z ) ) = ( ( x T y ) O ( x T z ) ) ) $.
      $( Transfer a distributive law to the function operation.  (Contributed
         by Mario Carneiro, 26-Jul-2014.) $)
      caofdi $p |- ( ph ->
        ( F oF T ( G oF R H ) ) = ( ( F oF T G ) oF O ( F oF T H ) ) ) $=
        wph vw cA vw cv cF cfv vw cv cG cfv vw cv cH cfv cR co cT co cmpt vw cA
        vw cv cF cfv vw cv cG cfv cT co vw cv cF cfv vw cv cH cfv cT co cO co
        cmpt cF cG cH cR cof co cT cof co cF cG cT cof co cF cH cT cof co cO
        cof co wph vw cA vw cv cF cfv vw cv cG cfv vw cv cH cfv cR co cT co vw
        cv cF cfv vw cv cG cfv cT co vw cv cF cfv vw cv cH cfv cT co cO co wph
        vw cv cA wcel wa vx vy vz vw cv cF cfv vw cv cG cfv vw cv cH cfv cS cR
        cT cO cK wph vx cv cK wcel vy cv cS wcel vz cv cS wcel w3a vx cv vy cv
        vz cv cR co cT co vx cv vy cv cT co vx cv vz cv cT co cO co wceq vw cv
        cA wcel caofdi.5 adantlr wph cA cK cF wf vw cv cA wcel vw cv cF cfv cK
        wcel caofdi.2 cA cK vw cv cF ffvelrn sylan wph cA cS cG wf vw cv cA
        wcel vw cv cG cfv cS wcel caofdi.3 cA cS vw cv cG ffvelrn sylan wph cA
        cS cH wf vw cv cA wcel vw cv cH cfv cS wcel caofdi.4 cA cS vw cv cH
        ffvelrn sylan caovdid mpteq2dva wph vw cA vw cv cF cfv vw cv cG cfv vw
        cv cH cfv cR co cT cF cG cH cR cof co cV cK cvv caofdi.1 wph cA cK cF
        wf vw cv cA wcel vw cv cF cfv cK wcel caofdi.2 cA cK vw cv cF ffvelrn
        sylan vw cv cG cfv vw cv cH cfv cR co cvv wcel wph vw cv cA wcel wa vw
        cv cG cfv vw cv cH cfv cR ovex a1i wph vw cA cK cF caofdi.2 feqmptd wph
        vw cA vw cv cG cfv vw cv cH cfv cR cG cH cV cS cS caofdi.1 wph cA cS cG
        wf vw cv cA wcel vw cv cG cfv cS wcel caofdi.3 cA cS vw cv cG ffvelrn
        sylan wph cA cS cH wf vw cv cA wcel vw cv cH cfv cS wcel caofdi.4 cA cS
        vw cv cH ffvelrn sylan wph vw cA cS cG caofdi.3 feqmptd wph vw cA cS cH
        caofdi.4 feqmptd offval2 offval2 wph vw cA vw cv cF cfv vw cv cG cfv cT
        co vw cv cF cfv vw cv cH cfv cT co cO cF cG cT cof co cF cH cT cof co
        cV cvv cvv caofdi.1 vw cv cF cfv vw cv cG cfv cT co cvv wcel wph vw cv
        cA wcel wa vw cv cF cfv vw cv cG cfv cT ovex a1i vw cv cF cfv vw cv cH
        cfv cT co cvv wcel wph vw cv cA wcel wa vw cv cF cfv vw cv cH cfv cT
        ovex a1i wph vw cA vw cv cF cfv vw cv cG cfv cT cF cG cV cK cS caofdi.1
        wph cA cK cF wf vw cv cA wcel vw cv cF cfv cK wcel caofdi.2 cA cK vw cv
        cF ffvelrn sylan wph cA cS cG wf vw cv cA wcel vw cv cG cfv cS wcel
        caofdi.3 cA cS vw cv cG ffvelrn sylan wph vw cA cK cF caofdi.2 feqmptd
        wph vw cA cS cG caofdi.3 feqmptd offval2 wph vw cA vw cv cF cfv vw cv
        cH cfv cT cF cH cV cK cS caofdi.1 wph cA cK cF wf vw cv cA wcel vw cv
        cF cfv cK wcel caofdi.2 cA cK vw cv cF ffvelrn sylan wph cA cS cH wf vw
        cv cA wcel vw cv cH cfv cS wcel caofdi.4 cA cS vw cv cH ffvelrn sylan
        wph vw cA cK cF caofdi.2 feqmptd wph vw cA cS cH caofdi.4 feqmptd
        offval2 offval2 3eqtr4d $.
    $}

    ${
      caofdir.5 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) ->
                          ( ( x R y ) T z ) = ( ( x T z ) O ( y T z ) ) ) $.
      $( Transfer a reverse distributive law to the function operation.
         (Contributed by NM, 19-Oct-2014.) $)
      caofdir $p |- ( ph ->
        ( ( G oF R H ) oF T F ) = ( ( G oF T F ) oF O ( H oF T F ) ) ) $=
        wph vw cA vw cv cG cfv vw cv cH cfv cR co vw cv cF cfv cT co cmpt vw cA
        vw cv cG cfv vw cv cF cfv cT co vw cv cH cfv vw cv cF cfv cT co cO co
        cmpt cG cH cR cof co cF cT cof co cG cF cT cof co cH cF cT cof co cO
        cof co wph vw cA vw cv cG cfv vw cv cH cfv cR co vw cv cF cfv cT co vw
        cv cG cfv vw cv cF cfv cT co vw cv cH cfv vw cv cF cfv cT co cO co wph
        vw cv cA wcel wa vx vy vz vw cv cG cfv vw cv cH cfv vw cv cF cfv cS cR
        cT cO cK wph vx cv cS wcel vy cv cS wcel vz cv cK wcel w3a vx cv vy cv
        cR co vz cv cT co vx cv vz cv cT co vy cv vz cv cT co cO co wceq vw cv
        cA wcel caofdir.5 adantlr wph cA cS cG wf vw cv cA wcel vw cv cG cfv cS
        wcel caofdi.3 cA cS vw cv cG ffvelrn sylan wph cA cS cH wf vw cv cA
        wcel vw cv cH cfv cS wcel caofdi.4 cA cS vw cv cH ffvelrn sylan wph cA
        cK cF wf vw cv cA wcel vw cv cF cfv cK wcel caofdi.2 cA cK vw cv cF
        ffvelrn sylan caovdird mpteq2dva wph vw cA vw cv cG cfv vw cv cH cfv cR
        co vw cv cF cfv cT cG cH cR cof co cF cV cvv cK caofdi.1 vw cv cG cfv
        vw cv cH cfv cR co cvv wcel wph vw cv cA wcel wa vw cv cG cfv vw cv cH
        cfv cR ovex a1i wph cA cK cF wf vw cv cA wcel vw cv cF cfv cK wcel
        caofdi.2 cA cK vw cv cF ffvelrn sylan wph vw cA vw cv cG cfv vw cv cH
        cfv cR cG cH cV cS cS caofdi.1 wph cA cS cG wf vw cv cA wcel vw cv cG
        cfv cS wcel caofdi.3 cA cS vw cv cG ffvelrn sylan wph cA cS cH wf vw cv
        cA wcel vw cv cH cfv cS wcel caofdi.4 cA cS vw cv cH ffvelrn sylan wph
        vw cA cS cG caofdi.3 feqmptd wph vw cA cS cH caofdi.4 feqmptd offval2
        wph vw cA cK cF caofdi.2 feqmptd offval2 wph vw cA vw cv cG cfv vw cv
        cF cfv cT co vw cv cH cfv vw cv cF cfv cT co cO cG cF cT cof co cH cF
        cT cof co cV cvv cvv caofdi.1 vw cv cG cfv vw cv cF cfv cT co cvv wcel
        wph vw cv cA wcel wa vw cv cG cfv vw cv cF cfv cT ovex a1i vw cv cH cfv
        vw cv cF cfv cT co cvv wcel wph vw cv cA wcel wa vw cv cH cfv vw cv cF
        cfv cT ovex a1i wph vw cA vw cv cG cfv vw cv cF cfv cT cG cF cV cS cK
        caofdi.1 wph cA cS cG wf vw cv cA wcel vw cv cG cfv cS wcel caofdi.3 cA
        cS vw cv cG ffvelrn sylan wph cA cK cF wf vw cv cA wcel vw cv cF cfv cK
        wcel caofdi.2 cA cK vw cv cF ffvelrn sylan wph vw cA cS cG caofdi.3
        feqmptd wph vw cA cK cF caofdi.2 feqmptd offval2 wph vw cA vw cv cH cfv
        vw cv cF cfv cT cH cF cV cS cK caofdi.1 wph cA cS cH wf vw cv cA wcel
        vw cv cH cfv cS wcel caofdi.4 cA cS vw cv cH ffvelrn sylan wph cA cK cF
        wf vw cv cA wcel vw cv cF cfv cK wcel caofdi.2 cA cK vw cv cF ffvelrn
        sylan wph vw cA cS cH caofdi.4 feqmptd wph vw cA cK cF caofdi.2 feqmptd
        offval2 offval2 3eqtr4d $.
    $}
  $}

  ${
    $d ph x y z $.  $d A x y z $.  $d B y z $.  $d I z $.  $d M x y z $.
    $d S x y $.
    caonncan.i $e |- ( ph -> I e. V ) $.
    caonncan.a $e |- ( ph -> A : I --> S ) $.
    caonncan.b $e |- ( ph -> B : I --> S ) $.
    caonncan.z $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
        ( x M ( x M y ) ) = y ) $.
    $( Transfer ~ nncan -shaped laws to vectors of numbers.  (Contributed by
       Stefan O'Rear, 27-Mar-2015.) $)
    caonncan $p |- ( ph -> ( A oF M ( A oF M B ) ) = B ) $=
      wph vz cI vz cv cA cfv vz cv cA cfv vz cv cB cfv cM co cM co cmpt vz cI
      vz cv cB cfv cmpt cA cA cB cM cof co cM cof co cB wph vz cI vz cv cA cfv
      vz cv cA cfv vz cv cB cfv cM co cM co vz cv cB cfv wph vz cv cI wcel wa
      vz cv cA cfv cS wcel vz cv cB cfv cS wcel vx cv vx cv vy cv cM co cM co
      vy cv wceq vy cS wral vx cS wral vz cv cA cfv vz cv cA cfv vz cv cB cfv
      cM co cM co vz cv cB cfv wceq wph cI cS cA wf vz cv cI wcel vz cv cA cfv
      cS wcel caonncan.a cI cS vz cv cA ffvelrn sylan wph cI cS cB wf vz cv cI
      wcel vz cv cB cfv cS wcel caonncan.b cI cS vz cv cB ffvelrn sylan wph vx
      cv vx cv vy cv cM co cM co vy cv wceq vy cS wral vx cS wral vz cv cI wcel
      wph vx cv vx cv vy cv cM co cM co vy cv wceq vx vy cS cS caonncan.z
      ralrimivva adantr vx cv vx cv vy cv cM co cM co vy cv wceq vz cv cA cfv
      vz cv cA cfv vz cv cB cfv cM co cM co vz cv cB cfv wceq vz cv cA cfv vz
      cv cA cfv vy cv cM co cM co vy cv wceq vx vy vz cv cA cfv vz cv cB cfv cS
      cS vx cv vz cv cA cfv wceq vx cv vx cv vy cv cM co cM co vz cv cA cfv vz
      cv cA cfv vy cv cM co cM co vy cv vx cv vz cv cA cfv wceq vx cv vz cv cA
      cfv vx cv vy cv cM co vz cv cA cfv vy cv cM co cM vx cv vz cv cA cfv wceq
      id vx cv vz cv cA cfv vy cv cM oveq1 oveq12d eqeq1d vy cv vz cv cB cfv
      wceq vz cv cA cfv vz cv cA cfv vy cv cM co cM co vz cv cA cfv vz cv cA
      cfv vz cv cB cfv cM co cM co vy cv vz cv cB cfv vy cv vz cv cB cfv wceq
      vz cv cA cfv vy cv cM co vz cv cA cfv vz cv cB cfv cM co vz cv cA cfv cM
      vy cv vz cv cB cfv vz cv cA cfv cM oveq2 oveq2d vy cv vz cv cB cfv wceq
      id eqeq12d rspc2va syl21anc mpteq2dva wph vz cI vz cv cA cfv vz cv cA cfv
      vz cv cB cfv cM co cM cA cA cB cM cof co cV cvv cvv caonncan.i vz cv cA
      cfv cvv wcel wph vz cv cI wcel wa vz cv cA fvex a1i vz cv cA cfv vz cv cB
      cfv cM co cvv wcel wph vz cv cI wcel wa vz cv cA cfv vz cv cB cfv cM ovex
      a1i wph vz cI cS cA caonncan.a feqmptd wph vz cI vz cv cA cfv vz cv cB
      cfv cM cA cB cV cvv cvv caonncan.i vz cv cA cfv cvv wcel wph vz cv cI
      wcel wa vz cv cA fvex a1i vz cv cB cfv cvv wcel wph vz cv cI wcel wa vz
      cv cB fvex a1i wph vz cI cS cA caonncan.a feqmptd wph vz cI cS cB
      caonncan.b feqmptd offval2 offval2 wph vz cI cS cB caonncan.b feqmptd
      3eqtr4d $.
  $}

  ${
    $d f g A $.  $d f g B $.  $d f g x R $.
    $( Equivalent expressions for a restriction of the function operation map.
       Unlike ` oF R ` which is a proper class, ` ( oF R | `` ( A X. B ) ) `
       can be a set by ~ ofmresex , allowing it to be used as a function or
       structure argument.  By ~ ofmresval , the restricted operation map
       values are the same as the original values, allowing theorems for
       ` oF R ` to be reused.  (Contributed by NM, 20-Oct-2014.) $)
    ofmres $p |- ( oF R |` ( A X. B ) ) =
         ( f e. A , g e. B |-> ( f oF R g ) ) $=
      vf vg cvv cvv vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv
      cR co cmpt cmpt2 cA cB cxp cres vf vg cA cB vx vf cv cdm vg cv cdm cin vx
      cv vf cv cfv vx cv vg cv cfv cR co cmpt cmpt2 cR cof cA cB cxp cres vf vg
      cA cB vf cv vg cv cR cof co cmpt2 cA cvv wss cB cvv wss vf vg cvv cvv vx
      vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cR co cmpt cmpt2
      cA cB cxp cres vf vg cA cB vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx
      cv vg cv cfv cR co cmpt cmpt2 wceq cA ssv cB ssv vf vg cvv cvv cA cB vx
      vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cR co cmpt
      resmpt2 mp2an cR cof vf vg cvv cvv vx vf cv cdm vg cv cdm cin vx cv vf cv
      cfv vx cv vg cv cfv cR co cmpt cmpt2 cA cB cxp vx cR vf vg df-of reseq1i
      vf vg cA cB vf cv vg cv cR cof co cA cB vx vf cv cdm vg cv cdm cin vx cv
      vf cv cfv vx cv vg cv cfv cR co cmpt cA eqid cB eqid vf cv cvv wcel vg cv
      cvv wcel vx vf cv cdm vg cv cdm cin vx cv vf cv cfv vx cv vg cv cfv cR co
      cmpt cvv wcel vf cv vg cv cR cof co vx vf cv cdm vg cv cdm cin vx cv vf
      cv cfv vx cv vg cv cfv cR co cmpt wceq vf vex vg vex vx vf cv cdm vg cv
      cdm cin vx cv vf cv cfv vx cv vg cv cfv cR co vf cv cdm vg cv cdm vf cv
      vf vex dmex inex1 mptex vf vg cvv cvv vx vf cv cdm vg cv cdm cin vx cv vf
      cv cfv vx cv vg cv cfv cR co cmpt cR cof cvv vx cR vf vg df-of ovmpt4g
      mp3an mpt2eq123i 3eqtr4i $.

    ofmresval.f $e |- ( ph -> F e. A ) $.
    ofmresval.g $e |- ( ph -> G e. B ) $.
    $( Value of a restriction of the function operation map.  (Contributed by
       NM, 20-Oct-2014.) $)
    ofmresval $p |- ( ph -> ( F ( oF R |` ( A X. B ) ) G ) = ( F oF R G ) ) $=
      wph cF cA wcel cG cB wcel cF cG cR cof cA cB cxp cres co cF cG cR cof co
      wceq ofmresval.f ofmresval.g cF cG cA cB cR cof ovres syl2anc $.
  $}

  ${
    $d f g A $.  $d f g B $.  $d f g R $.
    ofmresex.a $e |- ( ph -> A e. V ) $.
    ofmresex.b $e |- ( ph -> B e. W ) $.
    $( Existence of a restriction of the function operation map.  (Contributed
       by NM, 20-Oct-2014.) $)
    ofmresex $p |- ( ph -> ( oF R |` ( A X. B ) ) e. _V ) $=
      wph cA cB cxp cvv wcel cR cof cA cB cxp cres cvv wcel wph cA cV wcel cB
      cW wcel cA cB cxp cvv wcel ofmresex.a ofmresex.b cA cB cV cW xpexg
      syl2anc cA cB cxp cR cvv ofexg syl $.
  $}

  ${
    $d ph v x $.  $d A x $.  $d B v x $.  $d D x $.  $d O v x $.  $d R v $.
    $d Y v x $.  $d Z v x $.
    suppssof1.s $e |- ( ph -> ( `' A " ( _V \ { Y } ) ) C_ L ) $.
    suppssof1.o $e |- ( ( ph /\ v e. R ) -> ( Y O v ) = Z ) $.
    suppssof1.a $e |- ( ph -> A : D --> V ) $.
    suppssof1.b $e |- ( ph -> B : D --> R ) $.
    suppssof1.d $e |- ( ph -> D e. W ) $.
    $( Formula building theorem for support restrictions: vector operation with
       left annihilator.  (Contributed by Stefan O'Rear, 9-Mar-2015.) $)
    suppssof1 $p |- ( ph -> ( `' ( A oF O B ) " ( _V \ { Z } ) ) C_ L ) $=
      wph cA cB cO cof co ccnv cvv cZ csn cdif cima vx cD vx cv cA cfv vx cv cB
      cfv cO co cmpt ccnv cvv cZ csn cdif cima cL wph cA cB cO cof co ccnv vx
      cD vx cv cA cfv vx cv cB cfv cO co cmpt ccnv cvv cZ csn cdif wph cA cB cO
      cof co vx cD vx cv cA cfv vx cv cB cfv cO co cmpt wph vx cD cD vx cv cA
      cfv vx cv cB cfv cO cD cA cB cW cW wph cD cV cA wf cA cD wfn suppssof1.a
      cD cV cA ffn syl wph cD cR cB wf cB cD wfn suppssof1.b cD cR cB ffn syl
      suppssof1.d suppssof1.d cD inidm wph vx cv cD wcel wa vx cv cA cfv eqidd
      wph vx cv cD wcel wa vx cv cB cfv eqidd offval cnveqd imaeq1d wph vx vv
      vx cv cA cfv vx cv cB cfv cD cR cL cO cvv cY cZ wph vx cD vx cv cA cfv
      cmpt ccnv cvv cY csn cdif cima cA ccnv cvv cY csn cdif cima cL wph cA
      ccnv vx cD vx cv cA cfv cmpt ccnv cvv cY csn cdif wph cA vx cD vx cv cA
      cfv cmpt wph vx cD cV cA suppssof1.a feqmptd cnveqd imaeq1d suppssof1.s
      eqsstr3d suppssof1.o vx cv cA cfv cvv wcel wph vx cv cD wcel wa vx cv cA
      fvex a1i wph cD cR cB wf vx cv cD wcel vx cv cB cfv cR wcel suppssof1.b
      cD cR vx cv cB ffvelrn sylan suppssov1 eqsstrd $.
  $}


