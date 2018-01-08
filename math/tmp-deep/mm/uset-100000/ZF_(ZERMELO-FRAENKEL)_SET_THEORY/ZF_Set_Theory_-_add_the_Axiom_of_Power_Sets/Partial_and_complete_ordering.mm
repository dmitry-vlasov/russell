
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Epsilon_and_identity_relations.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Partial and complete ordering

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

$(
We have not yet defined relations ( ~ df-rel ), but here we introduce a
few related notions we will use to develop ordinals.  The class variable
` R ` is no different from other class variables, but it reminds us that
normally it represents what we will later call a "relation."
$)

  $( Declare new constant symbols. $)
  $c Po $.  $( Partial ordering predicate symbol (read: 'partial ordering'). $)
  $c Or $.  $( Strict complete ordering predicate symbol (read: 'orders'). $)

  $( Extend wff notation to include the strict partial ordering predicate.
     Read:  ' ` R ` is a partial order on ` A ` .' $)
  wpo $a wff R Po A $.

  $( Extend wff notation to include the strict complete ordering predicate.
     Read:  ' ` R ` orders ` A ` .' $)
  wor $a wff R Or A $.

  ${
    $d x y z R $.  $d x y z A $.
    $( Define the strict partial order predicate.  Definition of [Enderton]
       p. 168.  The expression ` R Po A ` means ` R ` is a partial order on
       ` A ` .  For example, ` < Po RR ` is true, while ` <_ Po RR ` is false
       ( ~ ex-po ).  (Contributed by NM, 16-Mar-1997.) $)
    df-po $a |- ( R Po A <-> A. x e. A A. y e. A A. z e. A
                ( -. x R x /\ ( ( x R y /\ y R z ) -> x R z ) ) ) $.

    $( Define the strict complete (linear) order predicate.  The expression
       ` R Or A ` is true if relationship ` R ` orders ` A ` .  For example,
       ` < Or RR ` is true ( ~ ltso ).  Equivalent to Definition 6.19(1) of
       [TakeutiZaring] p. 29.  (Contributed by NM, 21-Jan-1996.) $)
    df-so $a |- ( R Or A <-> ( R Po A /\ A. x e. A A. y e. A
                ( x R y \/ x = y \/ y R x ) ) ) $.
  $}

  ${
    $d x y z R $.  $d x y z A $.  $d x y z B $.
    $( Subset theorem for the partial ordering predicate.  (Contributed by NM,
       27-Mar-1997.)  (Proof shortened by Mario Carneiro, 18-Nov-2016.) $)
    poss $p |- ( A C_ B -> ( R Po B -> R Po A ) ) $=
      cA cB wss vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa
      vx cv vz cv cR wbr wi wa vz cB wral vy cB wral vx cB wral vx cv vx cv cR
      wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa
      vz cA wral vy cA wral vx cA wral cB cR wpo cA cR wpo cA cB wss vx cv vx
      cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi wa vz cB wral vy cB wral vx cB wral vx cv vx cv cR wbr wn vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cB wral vy cB
      wral vx cA wral vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi wa vz cA wral vy cA wral vx cA wral vx cv vx
      cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi wa vz cB wral vy cB wral vx cA cB ssralv cA cB wss vx cv vx cv cR wbr
      wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz
      cB wral vy cB wral vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv
      cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vy cA wral vx cA cA cB wss
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa vz cB wral vy cB wral vx cv vx cv cR wbr wn vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cB wral vy cA
      wral vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv
      vz cv cR wbr wi wa vz cA wral vy cA wral vx cv vx cv cR wbr wn vx cv vy
      cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cB wral vy cA
      cB ssralv cA cB wss vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv
      cR wbr wa vx cv vz cv cR wbr wi wa vz cB wral vx cv vx cv cR wbr wn vx cv
      vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vy
      cA vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv
      vz cv cR wbr wi wa vz cA cB ssralv ralimdv syld ralimdv syld vx vy vz cB
      cR df-po vx vy vz cA cR df-po 3imtr4g $.
  $}

  ${
    $d x y z R $.  $d x y z S $.  $d x y z A $.
    $( Equality theorem for partial ordering predicate.  (Contributed by NM,
       27-Mar-1997.) $)
    poeq1 $p |- ( R = S -> ( R Po A <-> S Po A ) ) $=
      cR cS wceq vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa
      vx cv vz cv cR wbr wi wa vz cA wral vy cA wral vx cA wral vx cv vx cv cS
      wbr wn vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi wa
      vz cA wral vy cA wral vx cA wral cA cR wpo cA cS wpo cR cS wceq vx cv vx
      cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi wa vz cA wral vx cv vx cv cS wbr wn vx cv vy cv cS wbr vy cv vz cv cS
      wbr wa vx cv vz cv cS wbr wi wa vz cA wral vx vy cA cA cR cS wceq vx cv
      vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi wa vx cv vx cv cS wbr wn vx cv vy cv cS wbr vy cv vz cv cS wbr wa
      vx cv vz cv cS wbr wi wa vz cA cR cS wceq vx cv vx cv cR wbr wn vx cv vx
      cv cS wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi cR cS
      wceq vx cv vx cv cR wbr vx cv vx cv cS wbr vx cv vx cv cR cS breq notbid
      cR cS wceq vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vy cv cS wbr vy
      cv vz cv cS wbr wa vx cv vz cv cR wbr vx cv vz cv cS wbr cR cS wceq vx cv
      vy cv cR wbr vx cv vy cv cS wbr vy cv vz cv cR wbr vy cv vz cv cS wbr vx
      cv vy cv cR cS breq vy cv vz cv cR cS breq anbi12d vx cv vz cv cR cS breq
      imbi12d anbi12d ralbidv 2ralbidv vx vy vz cA cR df-po vx vy vz cA cS
      df-po 3bitr4g $.
  $}

  $( Equality theorem for partial ordering predicate.  (Contributed by NM,
     27-Mar-1997.) $)
  poeq2 $p |- ( A = B -> ( R Po A <-> R Po B ) ) $=
    cA cB wceq cA cR wpo cB cR wpo cA cB wceq cB cA wss cA cR wpo cB cR wpo wi
    cB cA eqimss2 cB cA cR poss syl cA cB wceq cA cB wss cB cR wpo cA cR wpo wi
    cA cB eqimss cA cB cR poss syl impbid $.

  ${
    $d R a b c $.  $d A a b c $.  $d x a b c $.
    nfpo.r $e |- F/_ x R $.
    nfpo.a $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for partial orders.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) $)
    nfpo $p |- F/ x R Po A $=
      cA cR wpo va cv va cv cR wbr wn va cv vb cv cR wbr vb cv vc cv cR wbr wa
      va cv vc cv cR wbr wi wa vc cA wral vb cA wral va cA wral vx va vb vc cA
      cR df-po va cv va cv cR wbr wn va cv vb cv cR wbr vb cv vc cv cR wbr wa
      va cv vc cv cR wbr wi wa vc cA wral vb cA wral vx va cA nfpo.a va cv va
      cv cR wbr wn va cv vb cv cR wbr vb cv vc cv cR wbr wa va cv vc cv cR wbr
      wi wa vc cA wral vx vb cA nfpo.a va cv va cv cR wbr wn va cv vb cv cR wbr
      vb cv vc cv cR wbr wa va cv vc cv cR wbr wi wa vx vc cA nfpo.a va cv va
      cv cR wbr wn va cv vb cv cR wbr vb cv vc cv cR wbr wa va cv vc cv cR wbr
      wi vx va cv va cv cR wbr vx vx va cv va cv cR vx va cv nfcv nfpo.r vx va
      cv nfcv nfbr nfn va cv vb cv cR wbr vb cv vc cv cR wbr wa va cv vc cv cR
      wbr vx va cv vb cv cR wbr vb cv vc cv cR wbr vx vx va cv vb cv cR vx va
      cv nfcv nfpo.r vx vb cv nfcv nfbr vx vb cv vc cv cR vx vb cv nfcv nfpo.r
      vx vc cv nfcv nfbr nfan vx va cv vc cv cR vx va cv nfcv nfpo.r vx vc cv
      nfcv nfbr nfim nfan nfral nfral nfral nfxfr $.

    $( Bound-variable hypothesis builder for total orders.  (Contributed by
       Stefan O'Rear, 20-Jan-2015.) $)
    nfso $p |- F/ x R Or A $=
      cA cR wor cA cR wpo va cv vb cv cR wbr va cv vb cv wceq vb cv va cv cR
      wbr w3o vb cA wral va cA wral wa vx va vb cA cR df-so cA cR wpo va cv vb
      cv cR wbr va cv vb cv wceq vb cv va cv cR wbr w3o vb cA wral va cA wral
      vx vx cA cR nfpo.r nfpo.a nfpo va cv vb cv cR wbr va cv vb cv wceq vb cv
      va cv cR wbr w3o vb cA wral vx va cA nfpo.a va cv vb cv cR wbr va cv vb
      cv wceq vb cv va cv cR wbr w3o vx vb cA nfpo.a va cv vb cv cR wbr va cv
      vb cv wceq vb cv va cv cR wbr vx vx va cv vb cv cR vx va cv nfcv nfpo.r
      vx vb cv nfcv nfbr va cv vb cv wceq vx nfv vx vb cv va cv cR vx vb cv
      nfcv nfpo.r vx va cv nfcv nfbr nf3or nfral nfral nfan nfxfr $.
  $}

  ${
    $d x y z R $.  $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.
    $( Properties of partial order relation in class notation.  (Contributed by
       NM, 27-Mar-1997.) $)
    pocl $p |- ( R Po A -> ( ( B e. A /\ C e. A /\ D e. A ) ->
               ( -. B R B /\ ( ( B R C /\ C R D ) -> B R D ) ) ) ) $=
      cB cA wcel cC cA wcel cD cA wcel w3a cA cR wpo cB cB cR wbr wn cB cC cR
      wbr cC cD cR wbr wa cB cD cR wbr wi wa cA cR wpo vx cv vx cv cR wbr wn vx
      cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa wi cA cR
      wpo cB cB cR wbr wn cB vy cv cR wbr vy cv vz cv cR wbr wa cB vz cv cR wbr
      wi wa wi cA cR wpo cB cB cR wbr wn cB cC cR wbr cC vz cv cR wbr wa cB vz
      cv cR wbr wi wa wi cA cR wpo cB cB cR wbr wn cB cC cR wbr cC cD cR wbr wa
      cB cD cR wbr wi wa wi vx vy vz cB cC cD cA cA cA vx cv cB wceq vx cv vx
      cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi wa cB cB cR wbr wn cB vy cv cR wbr vy cv vz cv cR wbr wa cB vz cv cR
      wbr wi wa cA cR wpo vx cv cB wceq vx cv vx cv cR wbr wn cB cB cR wbr wn
      vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi cB vy cv
      cR wbr vy cv vz cv cR wbr wa cB vz cv cR wbr wi vx cv cB wceq vx cv vx cv
      cR wbr cB cB cR wbr vx cv cB wceq vx cv cB vx cv cB cR vx cv cB wceq id
      vx cv cB wceq id breq12d notbid vx cv cB wceq vx cv vy cv cR wbr vy cv vz
      cv cR wbr wa cB vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr cB
      vz cv cR wbr vx cv cB wceq vx cv vy cv cR wbr cB vy cv cR wbr vy cv vz cv
      cR wbr vx cv cB vy cv cR breq1 anbi1d vx cv cB vz cv cR breq1 imbi12d
      anbi12d imbi2d vy cv cC wceq cB cB cR wbr wn cB vy cv cR wbr vy cv vz cv
      cR wbr wa cB vz cv cR wbr wi wa cB cB cR wbr wn cB cC cR wbr cC vz cv cR
      wbr wa cB vz cv cR wbr wi wa cA cR wpo vy cv cC wceq cB vy cv cR wbr vy
      cv vz cv cR wbr wa cB vz cv cR wbr wi cB cC cR wbr cC vz cv cR wbr wa cB
      vz cv cR wbr wi cB cB cR wbr wn vy cv cC wceq cB vy cv cR wbr vy cv vz cv
      cR wbr wa cB cC cR wbr cC vz cv cR wbr wa cB vz cv cR wbr vy cv cC wceq
      cB vy cv cR wbr cB cC cR wbr vy cv vz cv cR wbr cC vz cv cR wbr vy cv cC
      cB cR breq2 vy cv cC vz cv cR breq1 anbi12d imbi1d anbi2d imbi2d vz cv cD
      wceq cB cB cR wbr wn cB cC cR wbr cC vz cv cR wbr wa cB vz cv cR wbr wi
      wa cB cB cR wbr wn cB cC cR wbr cC cD cR wbr wa cB cD cR wbr wi wa cA cR
      wpo vz cv cD wceq cB cC cR wbr cC vz cv cR wbr wa cB vz cv cR wbr wi cB
      cC cR wbr cC cD cR wbr wa cB cD cR wbr wi cB cB cR wbr wn vz cv cD wceq
      cB cC cR wbr cC vz cv cR wbr wa cB cC cR wbr cC cD cR wbr wa cB vz cv cR
      wbr cB cD cR wbr vz cv cD wceq cC vz cv cR wbr cC cD cR wbr cB cC cR wbr
      vz cv cD cC cR breq2 anbi2d vz cv cD cB cR breq2 imbi12d anbi2d imbi2d cA
      cR wpo vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a vx cv vx cv cR wbr
      wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa cA
      cR wpo vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a vx cv vx cv cR wbr
      wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa wi
      vz cA cR wpo vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a vx cv vx cv cR
      wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa
      wi vz wal vx vy cA cR wpo vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa wi vz wal vy wal vx wal cA cR wpo vx cv vx cv cR wbr wn
      vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA
      wral vy cA wral vx cA wral vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa wi vz wal vy wal vx wal vx vy vz cA cR df-po vx cv vx cv
      cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi
      wa vx vy vz cA cA cA r3al bitri biimpi 19.21bbi 19.21bi com12 vtocl3ga
      com12 $.
  $}

  ${
    $d x y z A $.  $d x y z R $.  $d x y z ph $.
    ispod.1 $e |- ( ( ph /\ x e. A ) -> -. x R x ) $.
    ispod.2 $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) ->
                    ( ( x R y /\ y R z ) -> x R z ) ) $.
    $( Sufficient conditions for a partial order.  (Contributed by NM,
       9-Jul-2014.) $)
    ispod $p |- ( ph -> R Po A ) $=
      wph vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv
      vz cv cR wbr wi wa vz cA wral vy cA wral vx cA wral cA cR wpo wph vx cv
      vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi wa vx vy vz cA cA cA wph vx cv cA wcel vy cv cA wcel vz cv cA wcel
      w3a wa vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx
      cv vz cv cR wbr wi wph vy cv cA wcel vx cv cA wcel vx cv vx cv cR wbr wn
      vz cv cA wcel ispod.1 3ad2antr1 ispod.2 jca ralrimivvva vx vy vz cA cR
      df-po sylibr $.
  $}

  ${
    $d x y z A $.  $d x y z ph $.  $d x y z R $.  $d x y z X $.  $d y z Y $.
    $d z Z $.
    swopolem.1 $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) ->
                    ( x R y -> ( x R z \/ z R y ) ) ) $.
    $( Perform the substitutions into the strict weak ordering law.
       (Contributed by Mario Carneiro, 31-Dec-2014.) $)
    swopolem $p |- ( ( ph /\ ( X e. A /\ Y e. A /\ Z e. A ) ) ->
                    ( X R Y -> ( X R Z \/ Z R Y ) ) ) $=
      wph vx cv vy cv cR wbr vx cv vz cv cR wbr vz cv vy cv cR wbr wo wi vz cA
      wral vy cA wral vx cA wral cX cA wcel cY cA wcel cZ cA wcel w3a cX cY cR
      wbr cX cZ cR wbr cZ cY cR wbr wo wi wph vx cv vy cv cR wbr vx cv vz cv cR
      wbr vz cv vy cv cR wbr wo wi vx vy vz cA cA cA swopolem.1 ralrimivvva vx
      cv vy cv cR wbr vx cv vz cv cR wbr vz cv vy cv cR wbr wo wi cX cY cR wbr
      cX cZ cR wbr cZ cY cR wbr wo wi cX vy cv cR wbr cX vz cv cR wbr vz cv vy
      cv cR wbr wo wi cX cY cR wbr cX vz cv cR wbr vz cv cY cR wbr wo wi vx vy
      vz cX cY cZ cA cA cA vx cv cX wceq vx cv vy cv cR wbr cX vy cv cR wbr vx
      cv vz cv cR wbr vz cv vy cv cR wbr wo cX vz cv cR wbr vz cv vy cv cR wbr
      wo vx cv cX vy cv cR breq1 vx cv cX wceq vx cv vz cv cR wbr cX vz cv cR
      wbr vz cv vy cv cR wbr vx cv cX vz cv cR breq1 orbi1d imbi12d vy cv cY
      wceq cX vy cv cR wbr cX cY cR wbr cX vz cv cR wbr vz cv vy cv cR wbr wo
      cX vz cv cR wbr vz cv cY cR wbr wo vy cv cY cX cR breq2 vy cv cY wceq vz
      cv vy cv cR wbr vz cv cY cR wbr cX vz cv cR wbr vy cv cY vz cv cR breq2
      orbi2d imbi12d vz cv cZ wceq cX vz cv cR wbr vz cv cY cR wbr wo cX cZ cR
      wbr cZ cY cR wbr wo cX cY cR wbr vz cv cZ wceq cX vz cv cR wbr cX cZ cR
      wbr vz cv cY cR wbr cZ cY cR wbr vz cv cZ cX cR breq2 vz cv cZ cY cR
      breq1 orbi12d imbi2d rspc3v mpan9 $.
  $}

  ${
    $d x y z A $.  $d x y z R $.  $d x y z ph $.
    swopo.1 $e |- ( ( ph /\ ( y e. A /\ z e. A ) ) ->
                    ( y R z -> -. z R y ) ) $.
    swopo.2 $e |- ( ( ph /\ ( x e. A /\ y e. A /\ z e. A ) ) ->
                    ( x R y -> ( x R z \/ z R y ) ) ) $.
    $( A strict weak order is a partial order.  (Contributed by Mario Carneiro,
       9-Jul-2014.) $)
    swopo $p |- ( ph -> R Po A ) $=
      wph vx vy vz cA cR wph vx cv cA wcel wa vx cv vx cv cR wbr vx cv cA wcel
      vx cv cA wcel vx cv cA wcel wa vy cv vz cv cR wbr vz cv vy cv cR wbr wn
      wi vz cA wral vy cA wral vx cv vx cv cR wbr vx cv vx cv cR wbr wn wi wph
      vx cv cA wcel vx cv cA wcel vx cv cA wcel id ancli wph vy cv vz cv cR wbr
      vz cv vy cv cR wbr wn wi vy vz cA cA swopo.1 ralrimivva vy cv vz cv cR
      wbr vz cv vy cv cR wbr wn wi vx cv vx cv cR wbr vx cv vx cv cR wbr wn wi
      vx cv vz cv cR wbr vz cv vx cv cR wbr wn wi vy vz vx cv vx cv cA cA vy cv
      vx cv wceq vy cv vz cv cR wbr vx cv vz cv cR wbr vz cv vy cv cR wbr wn vz
      cv vx cv cR wbr wn vy cv vx cv vz cv cR breq1 vy cv vx cv wceq vz cv vy
      cv cR wbr vz cv vx cv cR wbr vy cv vx cv vz cv cR breq2 notbid imbi12d vz
      cv vx cv wceq vx cv vz cv cR wbr vx cv vx cv cR wbr vz cv vx cv cR wbr wn
      vx cv vx cv cR wbr wn vz cv vx cv vx cv cR breq2 vz cv vx cv wceq vz cv
      vx cv cR wbr vx cv vx cv cR wbr vz cv vx cv vx cv cR breq1 notbid imbi12d
      rspc2va syl2anr pm2.01d wph vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a
      wa vy cv vz cv cR wbr vz cv vy cv cR wbr wn vx cv vy cv cR wbr vx cv vz
      cv cR wbr wph vy cv cA wcel vz cv cA wcel vy cv vz cv cR wbr vz cv vy cv
      cR wbr wn wi vx cv cA wcel swopo.1 3adantr1 wph vx cv cA wcel vy cv cA
      wcel vz cv cA wcel w3a wa vx cv vy cv cR wbr vz cv vy cv cR wbr wn vx cv
      vz cv cR wbr wph vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a wa vx cv
      vy cv cR wbr wa vz cv vy cv cR wbr vx cv vz cv cR wbr wph vx cv cA wcel
      vy cv cA wcel vz cv cA wcel w3a wa vx cv vy cv cR wbr wa vx cv vz cv cR
      wbr vz cv vy cv cR wbr wph vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a
      wa vx cv vy cv cR wbr vx cv vz cv cR wbr vz cv vy cv cR wbr wo swopo.2
      imp orcomd ord expimpd sylan2d ispod $.
  $}

  $( A partial order relation is irreflexive.  (Contributed by NM,
     27-Mar-1997.) $)
  poirr $p |- ( ( R Po A /\ B e. A ) -> -. B R B ) $=
    cB cA wcel cA cR wpo cB cA wcel cB cA wcel cB cA wcel w3a cB cB cR wbr wn
    cB cA wcel cB cA wcel cB cA wcel w3a cB cA wcel cB cA wcel wa cB cA wcel wa
    cB cA wcel cB cA wcel wa cB cA wcel cB cA wcel cB cA wcel cB cA wcel df-3an
    cB cA wcel cB cA wcel anabs1 cB cA wcel anidm 3bitrri cA cR wpo cB cA wcel
    cB cA wcel cB cA wcel w3a wa cB cB cR wbr wn cB cB cR wbr cB cB cR wbr wa
    cB cB cR wbr wi cA cR wpo cB cA wcel cB cA wcel cB cA wcel w3a cB cB cR wbr
    wn cB cB cR wbr cB cB cR wbr wa cB cB cR wbr wi wa cA cB cB cB cR pocl imp
    simpld sylan2b $.

  $( A partial order relation is a transitive relation.  (Contributed by NM,
     27-Mar-1997.) $)
  potr $p |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
             ( ( B R C /\ C R D ) -> B R D ) ) $=
    cA cR wpo cB cA wcel cC cA wcel cD cA wcel w3a wa cB cB cR wbr wn cB cC cR
    wbr cC cD cR wbr wa cB cD cR wbr wi cA cR wpo cB cA wcel cC cA wcel cD cA
    wcel w3a cB cB cR wbr wn cB cC cR wbr cC cD cR wbr wa cB cD cR wbr wi wa cA
    cB cC cD cR pocl imp simprd $.

  $( A partial order relation has no 2-cycle loops.  (Contributed by NM,
     27-Mar-1997.) $)
  po2nr $p |- ( ( R Po A /\ ( B e. A /\ C e. A ) ) ->
              -. ( B R C /\ C R B ) ) $=
    cA cR wpo cB cA wcel cC cA wcel wa wa cB cC cR wbr cC cB cR wbr wa cB cB cR
    wbr cA cR wpo cB cA wcel cB cB cR wbr wn cC cA wcel cA cB cR poirr adantrr
    cA cR wpo cB cA wcel cC cA wcel cB cC cR wbr cC cB cR wbr wa cB cB cR wbr
    wi cA cR wpo cB cA wcel cC cA wcel cB cC cR wbr cC cB cR wbr wa cB cB cR
    wbr wi wi cA cR wpo cB cA wcel cC cA wcel cB cA wcel cB cC cR wbr cC cB cR
    wbr wa cB cB cR wbr wi cA cR wpo cB cA wcel cC cA wcel cB cA wcel cB cC cR
    wbr cC cB cR wbr wa cB cB cR wbr wi cA cB cC cB cR potr 3exp2 com34 pm2.43d
    imp32 mtod $.

  $( A partial order relation has no 3-cycle loops.  (Contributed by NM,
     27-Mar-1997.) $)
  po3nr $p |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
             -. ( B R C /\ C R D /\ D R B ) ) $=
    cA cR wpo cB cA wcel cC cA wcel cD cA wcel w3a wa cB cC cR wbr cC cD cR wbr
    cD cB cR wbr w3a cB cD cR wbr cD cB cR wbr wa cA cR wpo cB cA wcel cD cA
    wcel cB cD cR wbr cD cB cR wbr wa wn cC cA wcel cA cB cD cR po2nr 3adantr2
    cB cC cR wbr cC cD cR wbr cD cB cR wbr w3a cB cC cR wbr cC cD cR wbr wa cD
    cB cR wbr wa cA cR wpo cB cA wcel cC cA wcel cD cA wcel w3a wa cB cD cR wbr
    cD cB cR wbr wa cB cC cR wbr cC cD cR wbr cD cB cR wbr df-3an cA cR wpo cB
    cA wcel cC cA wcel cD cA wcel w3a wa cB cC cR wbr cC cD cR wbr wa cB cD cR
    wbr cD cB cR wbr cA cB cC cD cR potr anim1d syl5bi mtod $.

  ${
    $d x y z R $.
    $( Any relation is a partial ordering of the empty set.  (Contributed by
       NM, 28-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    po0 $p |- R Po (/) $=
      c0 cR wpo vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa
      vx cv vz cv cR wbr wi wa vz c0 wral vy c0 wral vx c0 wral vx cv vx cv cR
      wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa
      vz c0 wral vy c0 wral vx ral0 vx vy vz c0 cR df-po mpbir $.
  $}

  ${
    $d R v w x y z $.  $d S v w z $.  $d X v w y z $.  $d Y x z $.
    $d A v w x z $.  $d B v w x z $.
    pofun.1 $e |- S = { <. x , y >. | X R Y } $.
    pofun.2 $e |- ( x = y -> X = Y ) $.
    $( A function preserves a partial order relation.  (Contributed by Jeff
       Madsen, 18-Jun-2011.) $)
    pofun $p |- ( ( R Po B /\ A. x e. A X e. B ) -> S Po A ) $=
      cB cR wpo cX cB wcel vx cA wral wa vv vw vz cA cS cB cR wpo cX cB wcel vx
      cA wral vv cv cA wcel vv cv vv cv cS wbr wn cX cB wcel vx cA wral vv cv
      cA wcel wa cB cR wpo vx vv cv cX csb cB wcel vv cv vv cv cS wbr wn vv cv
      cA wcel cX cB wcel vx cA wral vx vv cv cX csb cB wcel cX cB wcel vx vv cv
      cX csb cB wcel vx vv cv cA vx vx vv cv cX csb cB vx vv cv cX nfcsb1v
      nfel1 vx cv vv cv wceq cX vx vv cv cX csb cB vx vv cv cX csbeq1a eleq1d
      rspc impcom cB cR wpo vx vv cv cX csb cB wcel wa vx vv cv cX csb vx vv cv
      cX csb cR wbr vv cv vv cv cS wbr cB vx vv cv cX csb cR poirr vv cv vv cv
      cS wbr vv cv vv cv cop cS wcel vv cv vv cv cop cX cY cR wbr vx vy copab
      wcel vx vv cv cX csb vx vv cv cX csb cR wbr vv cv vv cv cS df-br cS cX cY
      cR wbr vx vy copab vv cv vv cv cop pofun.1 eleq2i cX cY cR wbr vx vv cv
      cX csb cY cR wbr vx vv cv cX csb vx vv cv cX csb cR wbr vx vy vv cv vv cv
      vx vx vv cv cX csb cY cR vx vv cv cX nfcsb1v vx cR nfcv vx cY nfcv nfbr
      vx vv cv cX csb vx vv cv cX csb cR wbr vy nfv vv vex vv vex vx cv vv cv
      wceq cX vx vv cv cX csb cY cR vx vv cv cX csbeq1a breq1d vy cv vv cv wceq
      cY vx vv cv cX csb vx vv cv cX csb cR vy cv vv cv wceq cY vx vy cv cX csb
      vx vv cv cX csb vx vy cv cX cY vy vex vx cY nfcv pofun.2 csbief vx vy cv
      vv cv cX csbeq1 syl5eqr breq2d opelopabf 3bitri sylnibr sylan2 anassrs cB
      cR wpo cX cB wcel vx cA wral wa vv cv cA wcel vw cv cA wcel vz cv cA wcel
      w3a vx vv cv cX csb cB wcel vx vw cv cX csb cB wcel vx vz cv cX csb cB
      wcel w3a vv cv vw cv cS wbr vw cv vz cv cS wbr wa vv cv vz cv cS wbr wi
      cX cB wcel vx cA wral vv cv cA wcel vw cv cA wcel vz cv cA wcel w3a vx vv
      cv cX csb cB wcel vx vw cv cX csb cB wcel vx vz cv cX csb cB wcel w3a cB
      cR wpo cX cB wcel vx cA wral vv cv cA wcel vw cv cA wcel vz cv cA wcel
      w3a vx vv cv cX csb cB wcel vx vw cv cX csb cB wcel vx vz cv cX csb cB
      wcel w3a cX cB wcel vx cA wral vv cv cA wcel vx vv cv cX csb cB wcel vw
      cv cA wcel vx vw cv cX csb cB wcel vz cv cA wcel vx vz cv cX csb cB wcel
      vv cv cA wcel cX cB wcel vx cA wral vx vv cv cX csb cB wcel cX cB wcel vx
      vv cv cX csb cB wcel vx vv cv cA vx vx vv cv cX csb cB vx vv cv cX
      nfcsb1v nfel1 vx cv vv cv wceq cX vx vv cv cX csb cB vx vv cv cX csbeq1a
      eleq1d rspc com12 vw cv cA wcel cX cB wcel vx cA wral vx vw cv cX csb cB
      wcel cX cB wcel vx vw cv cX csb cB wcel vx vw cv cA vx vx vw cv cX csb cB
      vx vw cv cX nfcsb1v nfel1 vx cv vw cv wceq cX vx vw cv cX csb cB vx vw cv
      cX csbeq1a eleq1d rspc com12 vz cv cA wcel cX cB wcel vx cA wral vx vz cv
      cX csb cB wcel cX cB wcel vx vz cv cX csb cB wcel vx vz cv cA vx vx vz cv
      cX csb cB vx vz cv cX nfcsb1v nfel1 vx cv vz cv wceq cX vx vz cv cX csb
      cB vx vz cv cX csbeq1a eleq1d rspc com12 3anim123d imp adantll cB cR wpo
      vx vv cv cX csb cB wcel vx vw cv cX csb cB wcel vx vz cv cX csb cB wcel
      w3a vv cv vw cv cS wbr vw cv vz cv cS wbr wa vv cv vz cv cS wbr wi cX cB
      wcel vx cA wral cB cR wpo vx vv cv cX csb cB wcel vx vw cv cX csb cB wcel
      vx vz cv cX csb cB wcel w3a wa vx vv cv cX csb vx vw cv cX csb cR wbr vx
      vw cv cX csb vx vz cv cX csb cR wbr wa vx vv cv cX csb vx vz cv cX csb cR
      wbr vv cv vw cv cS wbr vw cv vz cv cS wbr wa vv cv vz cv cS wbr cB vx vv
      cv cX csb vx vw cv cX csb vx vz cv cX csb cR potr vv cv vw cv cS wbr vx
      vv cv cX csb vx vw cv cX csb cR wbr vw cv vz cv cS wbr vx vw cv cX csb vx
      vz cv cX csb cR wbr vv cv vw cv cS wbr vv cv vw cv cop cS wcel vv cv vw
      cv cop cX cY cR wbr vx vy copab wcel vx vv cv cX csb vx vw cv cX csb cR
      wbr vv cv vw cv cS df-br cS cX cY cR wbr vx vy copab vv cv vw cv cop
      pofun.1 eleq2i cX cY cR wbr vx vv cv cX csb cY cR wbr vx vv cv cX csb vx
      vw cv cX csb cR wbr vx vy vv cv vw cv vx vx vv cv cX csb cY cR vx vv cv
      cX nfcsb1v vx cR nfcv vx cY nfcv nfbr vx vv cv cX csb vx vw cv cX csb cR
      wbr vy nfv vv vex vw vex vx cv vv cv wceq cX vx vv cv cX csb cY cR vx vv
      cv cX csbeq1a breq1d vy cv vw cv wceq cY vx vw cv cX csb vx vv cv cX csb
      cR vy cv vw cv wceq cY vx vy cv cX csb vx vw cv cX csb vx vy cv cX cY vy
      vex vx cY nfcv pofun.2 csbief vx vy cv vw cv cX csbeq1 syl5eqr breq2d
      opelopabf 3bitri vw cv vz cv cS wbr vw cv vz cv cop cS wcel vw cv vz cv
      cop cX cY cR wbr vx vy copab wcel vx vw cv cX csb vx vz cv cX csb cR wbr
      vw cv vz cv cS df-br cS cX cY cR wbr vx vy copab vw cv vz cv cop pofun.1
      eleq2i cX cY cR wbr vx vw cv cX csb cY cR wbr vx vw cv cX csb vx vz cv cX
      csb cR wbr vx vy vw cv vz cv vx vx vw cv cX csb cY cR vx vw cv cX nfcsb1v
      vx cR nfcv vx cY nfcv nfbr vx vw cv cX csb vx vz cv cX csb cR wbr vy nfv
      vw vex vz vex vx cv vw cv wceq cX vx vw cv cX csb cY cR vx vw cv cX
      csbeq1a breq1d vy cv vz cv wceq cY vx vz cv cX csb vx vw cv cX csb cR vy
      cv vz cv wceq cY vx vy cv cX csb vx vz cv cX csb vx vy cv cX cY vy vex vx
      cY nfcv pofun.2 csbief vx vy cv vz cv cX csbeq1 syl5eqr breq2d opelopabf
      3bitri anbi12i vv cv vz cv cS wbr vv cv vz cv cop cS wcel vv cv vz cv cop
      cX cY cR wbr vx vy copab wcel vx vv cv cX csb vx vz cv cX csb cR wbr vv
      cv vz cv cS df-br cS cX cY cR wbr vx vy copab vv cv vz cv cop pofun.1
      eleq2i cX cY cR wbr vx vv cv cX csb cY cR wbr vx vv cv cX csb vx vz cv cX
      csb cR wbr vx vy vv cv vz cv vx vx vv cv cX csb cY cR vx vv cv cX nfcsb1v
      vx cR nfcv vx cY nfcv nfbr vx vv cv cX csb vx vz cv cX csb cR wbr vy nfv
      vv vex vz vex vx cv vv cv wceq cX vx vv cv cX csb cY cR vx vv cv cX
      csbeq1a breq1d vy cv vz cv wceq cY vx vz cv cX csb vx vv cv cX csb cR vy
      cv vz cv wceq cY vx vy cv cX csb vx vz cv cX csb vx vy cv cX cY vy vex vx
      cY nfcv pofun.2 csbief vx vy cv vz cv cX csbeq1 syl5eqr breq2d opelopabf
      3bitri 3imtr4g adantlr syldan ispod $.
  $}

  ${
    $d x y R $.  $d x y A $.
    $( A strict linear order is a strict partial order.  (Contributed by NM,
       28-Mar-1997.) $)
    sopo $p |- ( R Or A -> R Po A ) $=
      cA cR wor cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR
      wbr w3o vy cA wral vx cA wral vx vy cA cR df-so simplbi $.
  $}

  ${
    $d x y R $.  $d x y A $.  $d x y B $.
    $( Subset theorem for the strict ordering predicate.  (Contributed by NM,
       16-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    soss $p |- ( A C_ B -> ( R Or B -> R Or A ) ) $=
      cA cB wss cB cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR
      wbr w3o vy cB wral vx cB wral wa cA cR wpo vx cv vy cv cR wbr vx cv vy cv
      wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral wa cB cR wor cA cR wor
      cA cB wss cB cR wpo cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv
      vx cv cR wbr w3o vy cB wral vx cB wral vx cv vy cv cR wbr vx cv vy cv
      wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral cA cB cR poss cA cB wss
      vx cv cB wcel vy cv cB wcel wa vx cv vy cv cR wbr vx cv vy cv wceq vy cv
      vx cv cR wbr w3o wi vy wal vx wal vx cv cA wcel vy cv cA wcel wa vx cv vy
      cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o wi vy wal vx wal vx cv
      vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cB wral vx cB
      wral vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA
      wral vx cA wral cA cB wss vx cv cB wcel vy cv cB wcel wa vx cv vy cv cR
      wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o wi vx cv cA wcel vy cv cA
      wcel wa vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o wi vx
      vy cA cB wss vx cv cA wcel vy cv cA wcel wa vx cv cB wcel vy cv cB wcel
      wa vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o cA cB wss
      vx cv cA wcel vx cv cB wcel vy cv cA wcel vy cv cB wcel cA cB vx cv ssel
      cA cB vy cv ssel anim12d imim1d 2alimdv vx cv vy cv cR wbr vx cv vy cv
      wceq vy cv vx cv cR wbr w3o vx vy cB cB r2al vx cv vy cv cR wbr vx cv vy
      cv wceq vy cv vx cv cR wbr w3o vx vy cA cA r2al 3imtr4g anim12d vx vy cB
      cR df-so vx vy cA cR df-so 3imtr4g $.
  $}

  ${
    $d x y R $.  $d x y S $.  $d x y A $.
    $( Equality theorem for the strict ordering predicate.  (Contributed by NM,
       16-Mar-1997.) $)
    soeq1 $p |- ( R = S -> ( R Or A <-> S Or A ) ) $=
      cR cS wceq cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR
      wbr w3o vy cA wral vx cA wral wa cA cS wpo vx cv vy cv cS wbr vx cv vy cv
      wceq vy cv vx cv cS wbr w3o vy cA wral vx cA wral wa cA cR wor cA cS wor
      cR cS wceq cA cR wpo cA cS wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv
      vx cv cR wbr w3o vy cA wral vx cA wral vx cv vy cv cS wbr vx cv vy cv
      wceq vy cv vx cv cS wbr w3o vy cA wral vx cA wral cA cR cS poeq1 cR cS
      wceq vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vx cv vy
      cv cS wbr vx cv vy cv wceq vy cv vx cv cS wbr w3o vx vy cA cA cR cS wceq
      vx cv vy cv cR wbr vx cv vy cv cS wbr vx cv vy cv wceq vx cv vy cv wceq
      vy cv vx cv cR wbr vy cv vx cv cS wbr vx cv vy cv cR cS breq cR cS wceq
      vx cv vy cv wceq biidd vy cv vx cv cR cS breq 3orbi123d 2ralbidv anbi12d
      vx vy cA cR df-so vx vy cA cS df-so 3bitr4g $.
  $}

  $( Equality theorem for the strict ordering predicate.  (Contributed by NM,
     16-Mar-1997.) $)
  soeq2 $p |- ( A = B -> ( R Or A <-> R Or B ) ) $=
    cA cB wceq cB cR wor cA cR wor cA cB wss cB cA wss wa cB cR wor cA cR wor
    wi cA cR wor cB cR wor wi wa cA cB wceq cB cR wor cA cR wor wb cA cB wss cB
    cR wor cA cR wor wi cB cA wss cA cR wor cB cR wor wi cA cB cR soss cB cA cR
    soss anim12i cA cB eqss cB cR wor cA cR wor dfbi2 3imtr4i bicomd $.

  $( A strict order relation is irreflexive.  (Contributed by NM,
     24-Nov-1995.) $)
  sonr $p |- ( ( R Or A /\ B e. A ) -> -. B R B ) $=
    cA cR wor cA cR wpo cB cA wcel cB cB cR wbr wn cA cR sopo cA cB cR poirr
    sylan $.

  $( A strict order relation is a transitive relation.  (Contributed by NM,
     21-Jan-1996.) $)
  sotr $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
             ( ( B R C /\ C R D ) -> B R D ) ) $=
    cA cR wor cA cR wpo cB cA wcel cC cA wcel cD cA wcel w3a cB cC cR wbr cC cD
    cR wbr wa cB cD cR wbr wi cA cR sopo cA cB cC cD cR potr sylan $.

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y R $.
    $( A strict order relation is linear (satisfies trichotomy).  (Contributed
       by NM, 21-Jan-1996.) $)
    solin $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) ->
              ( B R C \/ B = C \/ C R B ) ) $=
      cB cA wcel cC cA wcel wa cA cR wor cB cC cR wbr cB cC wceq cC cB cR wbr
      w3o cA cR wor vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o
      wi cA cR wor cB vy cv cR wbr cB vy cv wceq vy cv cB cR wbr w3o wi cA cR
      wor cB cC cR wbr cB cC wceq cC cB cR wbr w3o wi vx vy cB cC cA cA vx cv
      cB wceq vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o cB vy
      cv cR wbr cB vy cv wceq vy cv cB cR wbr w3o cA cR wor vx cv cB wceq vx cv
      vy cv cR wbr cB vy cv cR wbr vx cv vy cv wceq cB vy cv wceq vy cv vx cv
      cR wbr vy cv cB cR wbr vx cv cB vy cv cR breq1 vx cv cB vy cv eqeq1 vx cv
      cB vy cv cR breq2 3orbi123d imbi2d vy cv cC wceq cB vy cv cR wbr cB vy cv
      wceq vy cv cB cR wbr w3o cB cC cR wbr cB cC wceq cC cB cR wbr w3o cA cR
      wor vy cv cC wceq cB vy cv cR wbr cB cC cR wbr cB vy cv wceq cB cC wceq
      vy cv cB cR wbr cC cB cR wbr vy cv cC cB cR breq2 vy cv cC cB eqeq2 vy cv
      cC cB cR breq1 3orbi123d imbi2d cA cR wor vx cv cA wcel vy cv cA wcel wa
      vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o cA cR wor cA
      cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA
      wral vx cA wral wa vx cv cA wcel vy cv cA wcel wa vx cv vy cv cR wbr vx
      cv vy cv wceq vy cv vx cv cR wbr w3o wi vx vy cA cR df-so vx cv vy cv cR
      wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral vx cv
      cA wcel vy cv cA wcel wa vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv
      cR wbr w3o wi cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv
      cR wbr w3o vx vy cA cA rsp2 adantl sylbi com12 vtocl2ga impcom $.
  $}

  $( A strict order relation has no 2-cycle loops.  (Contributed by NM,
     21-Jan-1996.) $)
  so2nr $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) ->
              -. ( B R C /\ C R B ) ) $=
    cA cR wor cA cR wpo cB cA wcel cC cA wcel wa cB cC cR wbr cC cB cR wbr wa
    wn cA cR sopo cA cB cC cR po2nr sylan $.

  $( A strict order relation has no 3-cycle loops.  (Contributed by NM,
     21-Jan-1996.) $)
  so3nr $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
             -. ( B R C /\ C R D /\ D R B ) ) $=
    cA cR wor cA cR wpo cB cA wcel cC cA wcel cD cA wcel w3a cB cC cR wbr cC cD
    cR wbr cD cB cR wbr w3a wn cA cR sopo cA cB cC cD cR po3nr sylan $.

  $( A strict order relation satisfies strict trichotomy.  (Contributed by NM,
     19-Feb-1996.) $)
  sotric $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) ->
              ( B R C <-> -. ( B = C \/ C R B ) ) ) $=
    cA cR wor cB cA wcel cC cA wcel wa wa cB cC wceq cC cB cR wbr wo cB cC cR
    wbr cA cR wor cB cA wcel cC cA wcel wa wa cB cC wceq cC cB cR wbr wo cB cC
    cR wbr wn cA cR wor cB cA wcel cC cA wcel wa wa cB cC wceq cB cC cR wbr wn
    cC cB cR wbr cA cR wor cB cA wcel cB cC wceq cB cC cR wbr wn wi cC cA wcel
    cA cR wor cB cA wcel wa cB cB cR wbr wn cB cC wceq cB cC cR wbr wn cA cB cR
    sonr cB cC wceq cB cB cR wbr cB cC cR wbr cB cC cB cR breq2 notbid
    syl5ibcom adantrr cA cR wor cB cA wcel cC cA wcel wa wa cB cC cR wbr cC cB
    cR wbr cA cR wor cB cA wcel cC cA wcel wa wa cB cC cR wbr cC cB cR wbr wa
    wn cB cC cR wbr cC cB cR wbr wn wi cA cB cC cR so2nr cB cC cR wbr cC cB cR
    wbr imnan sylibr con2d jaod cA cR wor cB cA wcel cC cA wcel wa wa cB cC cR
    wbr cB cC wceq cC cB cR wbr w3o cB cC cR wbr wn cB cC wceq cC cB cR wbr wo
    wi cA cB cC cR solin cB cC cR wbr cB cC wceq cC cB cR wbr w3o cB cC cR wbr
    cB cC wceq cC cB cR wbr wo wo cB cC cR wbr wn cB cC wceq cC cB cR wbr wo wi
    cB cC cR wbr cB cC wceq cC cB cR wbr 3orass cB cC cR wbr cB cC wceq cC cB
    cR wbr wo df-or bitri sylib impbid con2bid $.

  $( Trichotomy law for strict order relation.  (Contributed by NM,
     9-Apr-1996.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
  sotrieq $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) ->
              ( B = C <-> -. ( B R C \/ C R B ) ) ) $=
    cA cR wor cB cA wcel cC cA wcel wa wa cB cC cR wbr cC cB cR wbr wo cB cC
    wceq cA cR wor cB cA wcel cC cA wcel wa wa cB cC cR wbr cC cB cR wbr wo cB
    cC wceq wn cA cR wor cB cA wcel cC cA wcel wa wa cB cC wceq cB cC cR wbr cC
    cB cR wbr wo cA cR wor cB cA wcel cC cA wcel wa wa cB cB cR wbr cB cB cR
    wbr wo wn cB cC wceq cB cC cR wbr cC cB cR wbr wo wn cA cR wor cB cA wcel
    cC cA wcel wa wa cB cB cR wbr cB cB cR wbr cB cB cR wbr wo cA cR wor cB cA
    wcel cB cB cR wbr wn cC cA wcel cA cB cR sonr adantrr cB cB cR wbr pm1.2
    nsyl cB cC wceq cB cB cR wbr cB cB cR wbr wo cB cC cR wbr cC cB cR wbr wo
    cB cC wceq cB cB cR wbr cB cC cR wbr cB cB cR wbr cC cB cR wbr cB cC cB cR
    breq2 cB cC cB cR breq1 orbi12d notbid syl5ibcom con2d cA cR wor cB cA wcel
    cC cA wcel wa wa cB cC cR wbr cB cC wceq cC cB cR wbr w3o cB cC wceq wn cB
    cC cR wbr cC cB cR wbr wo wi cA cB cC cR solin cB cC cR wbr cB cC wceq cC
    cB cR wbr w3o cB cC cR wbr cB cC wceq cC cB cR wbr wo wo cB cC wceq cB cC
    cR wbr cC cB cR wbr wo wo cB cC wceq wn cB cC cR wbr cC cB cR wbr wo wi cB
    cC cR wbr cB cC wceq cC cB cR wbr 3orass cB cC cR wbr cB cC wceq cC cB cR
    wbr or12 cB cC wceq cB cC cR wbr cC cB cR wbr wo df-or 3bitri sylib impbid
    con2bid $.

  $( Trichotomy law for strict order relation.  (Contributed by NM,
     5-May-1999.) $)
  sotrieq2 $p |- ( ( R Or A /\ ( B e. A /\ C e. A ) ) ->
              ( B = C <-> ( -. B R C /\ -. C R B ) ) ) $=
    cA cR wor cB cA wcel cC cA wcel wa wa cB cC wceq cB cC cR wbr cC cB cR wbr
    wo wn cB cC cR wbr wn cC cB cR wbr wn wa cA cB cC cR sotrieq cB cC cR wbr
    cC cB cR wbr ioran syl6bb $.

  $( A transitivity relation.  (Read ` B <_ C ` and ` C < D ` implies
     ` B < D ` .)  (Contributed by Mario Carneiro, 10-May-2013.) $)
  sotr2 $p |- ( ( R Or A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
                ( ( -. C R B /\ C R D ) -> B R D ) ) $=
    cA cR wor cB cA wcel cC cA wcel cD cA wcel w3a wa cC cB cR wbr wn cC cD cR
    wbr cB cD cR wbr cA cR wor cB cA wcel cC cA wcel cD cA wcel w3a wa cC cB cR
    wbr wn cC cB wceq cB cC cR wbr wo cC cD cR wbr cB cD cR wbr wi cA cR wor cB
    cA wcel cC cA wcel cD cA wcel w3a wa cC cB cR wbr cC cB wceq cB cC cR wbr
    wo cA cR wor cB cA wcel cC cA wcel cC cB cR wbr cC cB wceq cB cC cR wbr wo
    wn wb cD cA wcel cA cR wor cC cA wcel cB cA wcel cC cB cR wbr cC cB wceq cB
    cC cR wbr wo wn wb cA cC cB cR sotric ancom2s 3adantr3 con2bid cA cR wor cB
    cA wcel cC cA wcel cD cA wcel w3a wa cC cB wceq cC cD cR wbr cB cD cR wbr
    wi cB cC cR wbr cC cB wceq cC cD cR wbr cB cD cR wbr wi wi cA cR wor cB cA
    wcel cC cA wcel cD cA wcel w3a wa cC cB wceq cC cD cR wbr cB cD cR wbr cC
    cB cD cR breq1 biimpd a1i cA cR wor cB cA wcel cC cA wcel cD cA wcel w3a wa
    cB cC cR wbr cC cD cR wbr cB cD cR wbr cA cB cC cD cR sotr exp3a jaod
    sylbird imp3a $.

  ${
    $d x y R $.  $d x y A $.  $d x y ph $.
    issod.1 $e |- ( ph -> R Po A ) $.
    issod.2 $e |- ( ( ph /\ ( x e. A /\ y e. A ) ) ->
                    ( x R y \/ x = y \/ y R x ) ) $.
    $( An irreflexive, transitive, linear relation is a strict ordering.
       (Contributed by NM, 21-Jan-1996.)  (Revised by Mario Carneiro,
       9-Jul-2014.) $)
    issod $p |- ( ph -> R Or A ) $=
      wph cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o
      vy cA wral vx cA wral cA cR wor issod.1 wph vx cv vy cv cR wbr vx cv vy
      cv wceq vy cv vx cv cR wbr w3o vx vy cA cA issod.2 ralrimivva vx vy cA cR
      df-so sylanbrc $.
  $}

  ${
    $d x y z R $.  $d x y z A $.
    issoi.1 $e |- ( x e. A -> -. x R x ) $.
    issoi.2 $e |- ( ( x e. A /\ y e. A /\ z e. A ) ->
                  ( ( x R y /\ y R z ) -> x R z ) ) $.
    issoi.3 $e |- ( ( x e. A /\ y e. A ) -> ( x R y \/ x = y \/ y R x ) ) $.
    $( An irreflexive, transitive, linear relation is a strict ordering.
       (Contributed by NM, 21-Jan-1996.)  (Revised by Mario Carneiro,
       9-Jul-2014.) $)
    issoi $p |- R Or A $=
      cA cR wor wtru vx vy cA cR wtru vx vy vz cA cR vx cv cA wcel vx cv vx cv
      cR wbr wn wtru issoi.1 adantl vx cv cA wcel vy cv cA wcel vz cv cA wcel
      w3a vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wtru
      issoi.2 adantl ispod vx cv cA wcel vy cv cA wcel wa vx cv vy cv cR wbr vx
      cv vy cv wceq vy cv vx cv cR wbr w3o wtru issoi.3 adantl issod trud $.
  $}

  ${
    $d x y z R $.  $d x y z A $.
    isso2i.1 $e |- ( ( x e. A /\ y e. A ) ->
                     ( x R y <-> -. ( x = y \/ y R x ) ) ) $.
    isso2i.2 $e |- ( ( x e. A /\ y e. A /\ z e. A ) ->
                     ( ( x R y /\ y R z ) -> x R z ) ) $.
    $( Deduce strict ordering from its properties.  (Contributed by NM,
       29-Jan-1996.)  (Revised by Mario Carneiro, 9-Jul-2014.) $)
    isso2i $p |- R Or A $=
      vx vy vz cA cR vx cv cA wcel vx cv vx cv cR wbr wn vx cv cA wcel vx cv cA
      wcel wa vx cv vx cv wceq vx cv vx cv cR wbr wo vx cv vx cv cR wbr wn vx
      cv vx cv wceq vx cv vx cv cR wbr vx cv eqid orci vx cv cA wcel vy cv cA
      wcel wa vx cv vy cv wceq vy cv vx cv cR wbr wo vx cv vy cv cR wbr wn wb
      wi vx cv cA wcel vx cv cA wcel wa vx cv vx cv wceq vx cv vx cv cR wbr wo
      vx cv vx cv cR wbr wn wb wi vy vx vy cv vx cv wceq vx cv cA wcel vy cv cA
      wcel wa vx cv cA wcel vx cv cA wcel wa vx cv vy cv wceq vy cv vx cv cR
      wbr wo vx cv vy cv cR wbr wn wb vx cv vx cv wceq vx cv vx cv cR wbr wo vx
      cv vx cv cR wbr wn wb vy cv vx cv wceq vy cv cA wcel vx cv cA wcel vx cv
      cA wcel vy cv vx cv cA eleq1 anbi2d vy cv vx cv wceq vx cv vy cv wceq vy
      cv vx cv cR wbr wo vx cv vx cv wceq vx cv vx cv cR wbr wo vx cv vy cv cR
      wbr wn vx cv vx cv cR wbr wn vy cv vx cv wceq vx cv vy cv wceq vx cv vx
      cv wceq vy cv vx cv cR wbr vx cv vx cv cR wbr vy cv vx cv vx cv eqeq2 vy
      cv vx cv vx cv cR breq1 orbi12d vy cv vx cv wceq vx cv vy cv cR wbr vx cv
      vx cv cR wbr vy cv vx cv vx cv cR breq2 notbid bibi12d imbi12d vx cv cA
      wcel vy cv cA wcel wa vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR
      wbr wo isso2i.1 con2bid chvarv mpbii anidms isso2i.2 vx cv cA wcel vy cv
      cA wcel wa vx cv vy cv cR wbr wn vx cv vy cv wceq vy cv vx cv cR wbr wo
      wi vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vx cv cA
      wcel vy cv cA wcel wa vx cv vy cv wceq vy cv vx cv cR wbr wo vx cv vy cv
      cR wbr wn vx cv cA wcel vy cv cA wcel wa vx cv vy cv cR wbr vx cv vy cv
      wceq vy cv vx cv cR wbr wo isso2i.1 con2bid biimprd vx cv vy cv cR wbr vx
      cv vy cv wceq vy cv vx cv cR wbr w3o vx cv vy cv cR wbr vx cv vy cv wceq
      vy cv vx cv cR wbr wo wo vx cv vy cv cR wbr wn vx cv vy cv wceq vy cv vx
      cv cR wbr wo wi vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr
      3orass vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr wo df-or
      bitri sylibr issoi $.
  $}

  ${
    $d x y R $.
    $( Any relation is a strict ordering of the empty set.  (Contributed by NM,
       16-Mar-1997.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    so0 $p |- R Or (/) $=
      c0 cR wor c0 cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR
      wbr w3o vy c0 wral vx c0 wral cR po0 vx cv vy cv cR wbr vx cv vy cv wceq
      vy cv vx cv cR wbr w3o vy c0 wral vx ral0 vx vy c0 cR df-so mpbir2an $.
  $}

  ${
    $d x y z A $.  $d x y z R $.
    $( A totally ordered set has at most one minimal element.  (Contributed by
       Mario Carneiro, 24-Jun-2015.)  (Revised by NM, 16-Jun-2017.) $)
    somo $p |- ( R Or A -> E* x e. A A. y e. A -. y R x ) $=
      cA cR wor vy cv vx cv cR wbr wn vy cA wral vy cv vz cv cR wbr wn vy cA
      wral wa vx vz weq wi vz cA wral vx cA wral vy cv vx cv cR wbr wn vy cA
      wral vx cA wrmo cA cR wor vy cv vx cv cR wbr wn vy cA wral vy cv vz cv cR
      wbr wn vy cA wral wa vx vz weq wi vx vz cA cA cA cR wor vx cv cA wcel vz
      cv cA wcel wa vy cv vx cv cR wbr wn vy cA wral vy cv vz cv cR wbr wn vy
      cA wral wa vx vz weq wi cA cR wor vx cv cA wcel vz cv cA wcel wa vx cv cA
      wcel vz cv cA wcel wa vy cv vx cv cR wbr wn vy cA wral vy cv vz cv cR wbr
      wn vy cA wral wa vx vz weq vx cv cA wcel vz cv cA wcel wa vy cv vx cv cR
      wbr wn vy cA wral vy cv vz cv cR wbr wn vy cA wral wa wa vx cv vz cv cR
      wbr wn vz cv vx cv cR wbr wn wa cA cR wor vx cv cA wcel vz cv cA wcel wa
      wa vx vz weq vx cv cA wcel vz cv cA wcel wa vy cv vx cv cR wbr wn vy cA
      wral vy cv vz cv cR wbr wn vy cA wral wa vx cv vz cv cR wbr wn vz cv vx
      cv cR wbr wn wa vx cv cA wcel vz cv cA wcel wa vy cv vz cv cR wbr wn vy
      cA wral vy cv vx cv cR wbr wn vy cA wral vx cv vz cv cR wbr wn vz cv vx
      cv cR wbr wn wa vx cv cA wcel vy cv vz cv cR wbr wn vy cA wral vx cv vz
      cv cR wbr wn vz cv cA wcel vy cv vx cv cR wbr wn vy cA wral vz cv vx cv
      cR wbr wn vy cv vz cv cR wbr wn vx cv vz cv cR wbr wn vy vx cv cA vy vx
      weq vy cv vz cv cR wbr vx cv vz cv cR wbr vy cv vx cv vz cv cR breq1
      notbid rspcv vy cv vx cv cR wbr wn vz cv vx cv cR wbr wn vy vz cv cA vy
      vz weq vy cv vx cv cR wbr vz cv vx cv cR wbr vy cv vz cv vx cv cR breq1
      notbid rspcv im2anan9 ancomsd imp vx cv vz cv cR wbr wn vz cv vx cv cR
      wbr wn wa vx cv vz cv cR wbr vz cv vx cv cR wbr wo wn cA cR wor vx cv cA
      wcel vz cv cA wcel wa wa vx vz weq vx cv vz cv cR wbr vz cv vx cv cR wbr
      ioran cA cR wor vx cv cA wcel vz cv cA wcel wa wa vx cv vz cv cR wbr vz
      cv vx cv cR wbr wo vx vz weq cA cR wor vx cv cA wcel vz cv cA wcel wa wa
      vx cv vz cv cR wbr vx vz weq vz cv vx cv cR wbr w3o vx cv vz cv cR wbr vz
      cv vx cv cR wbr wo vx vz weq wo cA vx cv vz cv cR solin vx cv vz cv cR
      wbr vx vz weq vz cv vx cv cR wbr w3o vx cv vz cv cR wbr vx vz weq wo vz
      cv vx cv cR wbr wo vx cv vz cv cR wbr vz cv vx cv cR wbr wo vx vz weq wo
      vx cv vz cv cR wbr vx vz weq vz cv vx cv cR wbr df-3or vx cv vz cv cR wbr
      vx vz weq vz cv vx cv cR wbr or32 bitri sylib ord syl5bir syl5 exp4b
      pm2.43d ralrimivv vy cv vx cv cR wbr wn vy cA wral vy cv vz cv cR wbr wn
      vy cA wral vx vz cA vx vz weq vy cv vx cv cR wbr wn vy cv vz cv cR wbr wn
      vy cA vx vz weq vy cv vx cv cR wbr vy cv vz cv cR wbr vx cv vz cv vy cv
      cR breq2 notbid ralbidv rmo4 sylibr $.
  $}


