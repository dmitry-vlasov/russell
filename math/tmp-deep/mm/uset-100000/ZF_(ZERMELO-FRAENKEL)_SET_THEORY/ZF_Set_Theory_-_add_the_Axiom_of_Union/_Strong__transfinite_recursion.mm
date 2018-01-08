
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Functions_on_ordinals__strictly_monotone_ordinal_functions.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
    "Strong" transfinite recursion

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c recs $.

  $( Notation for a function defined by strong transfinite recursion. $)
  crecs $a class recs ( F ) $.

  ${
    $d F f x y $.
    $( Define a function ` recs ( F ) ` on ` On ` , the class of ordinal
       numbers, by transfinite recursion given a rule ` F ` which sets the next
       value given all values so far.  See ~ df-rdg for more details on why
       this definition is desirable.  Unlike ~ df-rdg which restricts the
       update rule to use only the previous value, this version allows the
       update rule to use _all_ previous values, which is why it is described
       as "strong", although it is actually more primitive.  See ~ recsfnon and
       ~ recsval for the primary contract of this definition.

       _EDITORIAL_: there are several existing versions of this construction
       without the definition, notably in ~ ordtype , ~ zorn2 , and
       ~ dfac8alem .  (Contributed by Stefan O'Rear, 18-Jan-2015.)
       (New usage is discouraged.) $)
    df-recs $a |- recs ( F ) = U. { f | E. x e. On ( f Fn x /\
        A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) } $.
  $}

  ${
    $d F a b c y $.  $d G a b c y $.  $d x y a b c $.
    $( Equality theorem for ` recs ` .  (Contributed by Stefan O'Rear,
       18-Jan-2015.) $)
    recseq $p |- ( F = G -> recs ( F ) = recs ( G ) ) $=
      cF cG wceq va cv vb cv wfn vc cv va cv cfv va cv vc cv cres cF cfv wceq
      vc vb cv wral wa vb con0 wrex va cab cuni va cv vb cv wfn vc cv va cv cfv
      va cv vc cv cres cG cfv wceq vc vb cv wral wa vb con0 wrex va cab cuni cF
      crecs cG crecs cF cG wceq va cv vb cv wfn vc cv va cv cfv va cv vc cv
      cres cF cfv wceq vc vb cv wral wa vb con0 wrex va cab va cv vb cv wfn vc
      cv va cv cfv va cv vc cv cres cG cfv wceq vc vb cv wral wa vb con0 wrex
      va cab cF cG wceq va cv vb cv wfn vc cv va cv cfv va cv vc cv cres cF cfv
      wceq vc vb cv wral wa vb con0 wrex va cv vb cv wfn vc cv va cv cfv va cv
      vc cv cres cG cfv wceq vc vb cv wral wa vb con0 wrex va cF cG wceq va cv
      vb cv wfn vc cv va cv cfv va cv vc cv cres cF cfv wceq vc vb cv wral wa
      va cv vb cv wfn vc cv va cv cfv va cv vc cv cres cG cfv wceq vc vb cv
      wral wa vb con0 cF cG wceq vc cv va cv cfv va cv vc cv cres cF cfv wceq
      vc vb cv wral vc cv va cv cfv va cv vc cv cres cG cfv wceq vc vb cv wral
      va cv vb cv wfn cF cG wceq vc cv va cv cfv va cv vc cv cres cF cfv wceq
      vc cv va cv cfv va cv vc cv cres cG cfv wceq vc vb cv cF cG wceq va cv vc
      cv cres cF cfv va cv vc cv cres cG cfv vc cv va cv cfv va cv vc cv cres
      cF cG fveq1 eqeq2d ralbidv anbi2d rexbidv abbidv unieqd vb vc va cF
      df-recs vb vc va cG df-recs 3eqtr4g $.

    nfrecs.f $e |- F/_ x F $.
    $( Bound-variable hypothesis builder for ` recs ` .  (Contributed by Stefan
       O'Rear, 18-Jan-2015.) $)
    nfrecs $p |- F/_ x recs ( F ) $=
      vx cF crecs va cv vb cv wfn vc cv va cv cfv va cv vc cv cres cF cfv wceq
      vc vb cv wral wa vb con0 wrex va cab cuni vb vc va cF df-recs vx va cv vb
      cv wfn vc cv va cv cfv va cv vc cv cres cF cfv wceq vc vb cv wral wa vb
      con0 wrex va cab va cv vb cv wfn vc cv va cv cfv va cv vc cv cres cF cfv
      wceq vc vb cv wral wa vb con0 wrex vx va va cv vb cv wfn vc cv va cv cfv
      va cv vc cv cres cF cfv wceq vc vb cv wral wa vx vb con0 vx con0 nfcv va
      cv vb cv wfn vc cv va cv cfv va cv vc cv cres cF cfv wceq vc vb cv wral
      vx va cv vb cv wfn vx nfv vc cv va cv cfv va cv vc cv cres cF cfv wceq vx
      vc vb cv vx vb cv nfcv vx vc cv va cv cfv va cv vc cv cres cF cfv vx va
      cv vc cv cres cF nfrecs.f vx va cv vc cv cres nfcv nffv nfeq2 nfral nfan
      nfrex nfab nfuni nfcxfr $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d x y z w F $.  $d x y z w G $.
    $( A technical lemma for transfinite recursion.  Compare Lemma 1 of
       [TakeutiZaring] p. 47.  (Contributed by NM, 23-Mar-1995.)  (Revised by
       David Abernethy, 19-Jun-2012.) $)
    tfrlem1 $p |- ( A e. On -> ( ( F Fn A /\ G Fn A ) ->
                  ( A. x e. A ( ( F ` x ) = ( B ` ( F |` x ) ) /\
                                        ( G ` x ) = ( B ` ( G |` x ) ) ) ->
                  A. x e. A ( F ` x ) = ( G ` x ) ) ) ) $=
      cA con0 wcel cF cA wfn cG cA wfn wa cA cA wss vx cv cF cfv cF vx cv cres
      cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx cA wral vx cv cF
      cfv vx cv cG cfv wceq vx cA wral wi cA ssid cF cA wfn cG cA wfn wa vy cv
      cA wss vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv wral
      wi wi wi cF cA wfn cG cA wfn wa cA cA wss vx cv cF cfv cF vx cv cres cB
      cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx cA wral vx cv cF
      cfv vx cv cG cfv wceq vx cA wral wi wi wi vy cA con0 vy cv cA wceq vy cv
      cA wss vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv wral
      wi wi cA cA wss vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx
      cv cres cB cfv wceq wa vx cA wral vx cv cF cfv vx cv cG cfv wceq vx cA
      wral wi wi cF cA wfn cG cA wfn wa vy cv cA wceq vy cv cA wss cA cA wss vx
      cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv
      wceq wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv wral wi vx
      cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv
      wceq wa vx cA wral vx cv cF cfv vx cv cG cfv wceq vx cA wral wi vy cv cA
      cA sseq1 vy cv cA wceq vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG
      cfv cG vx cv cres cB cfv wceq wa vx vy cv wral vx cv cF cfv cF vx cv cres
      cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx cA wral vx cv cF
      cfv vx cv cG cfv wceq vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx cA
      wral vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB
      cfv wceq wa vx vy cv cA raleq vx cv cF cfv vx cv cG cfv wceq vx vy cv cA
      raleq imbi12d imbi12d imbi2d vy cv con0 wcel cF cA wfn cG cA wfn wa vy cv
      cA wss vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv wral
      cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv
      wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv wral wa vx cv cF
      cfv vx cv cG cfv wceq vx vy cv wral wi cF cA wfn cG cA wfn wa vz cv cA
      wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx vz cv wral wa vx cv cF cfv vx cv cG cfv wceq vx vz cv
      wral wi vy vz vy cv vz cv wceq cF cA wfn cG cA wfn wa vy cv cA wss wa vx
      cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv
      wceq wa vx vy cv wral wa cF cA wfn cG cA wfn wa vz cv cA wss wa vx cv cF
      cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa
      vx vz cv wral wa vx cv cF cfv vx cv cG cfv wceq vx vy cv wral vx cv cF
      cfv vx cv cG cfv wceq vx vz cv wral vy cv vz cv wceq cF cA wfn cG cA wfn
      wa vy cv cA wss wa cF cA wfn cG cA wfn wa vz cv cA wss wa vx cv cF cfv cF
      vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv
      wral vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB
      cfv wceq wa vx vz cv wral vy cv vz cv wceq vy cv cA wss vz cv cA wss cF
      cA wfn cG cA wfn wa vy cv vz cv cA sseq1 anbi2d vx cv cF cfv cF vx cv
      cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv vz cv
      raleq anbi12d vx cv cF cfv vx cv cG cfv wceq vx vy cv vz cv raleq imbi12d
      cF cA wfn cG cA wfn wa vz cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv
      wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vz cv wral wa vx cv cF
      cfv vx cv cG cfv wceq vx vz cv wral wi vz vy cv wral cF cA wfn cG cA wfn
      wa vz cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG
      vx cv cres cB cfv wceq wa vx vz cv wral wa vz vy cv wral vx cv cF cfv vx
      cv cG cfv wceq vx vz cv wral vz vy cv wral wi vy cv con0 wcel cF cA wfn
      cG cA wfn wa vy cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv
      cG cfv cG vx cv cres cB cfv wceq wa vx vy cv wral wa cF cA wfn cG cA wfn
      wa vy cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG
      vx cv cres cB cfv wceq wa vx vy cv wral wa vx cv cF cfv vx cv cG cfv wceq
      vx vy cv wral wi wi cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv cF cfv
      cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy
      cv wral wa vx cv cF cfv vx cv cG cfv wceq vx vy cv wral wi cF cA wfn cG
      cA wfn wa vz cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG
      cfv cG vx cv cres cB cfv wceq wa vx vz cv wral wa vx cv cF cfv vx cv cG
      cfv wceq vx vz cv wral vz vy cv ralim vy cv con0 wcel cF cA wfn cG cA wfn
      wa vy cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG
      vx cv cres cB cfv wceq wa vx vy cv wral wa cF cA wfn cG cA wfn wa vz cv
      cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv
      cres cB cfv wceq wa vx vz cv wral wa vz vy cv wral vx cv cF cfv vx cv cG
      cfv wceq vx vz cv wral vz vy cv wral cF cA wfn cG cA wfn wa vy cv cA wss
      wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB
      cfv wceq wa vx vy cv wral wa vx cv cF cfv vx cv cG cfv wceq vx vy cv wral
      wi vy cv con0 wcel cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv cF cfv cF
      vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv
      wral wa cF cA wfn cG cA wfn wa vz cv cA wss wa vx cv cF cfv cF vx cv cres
      cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vz cv wral wa vz
      vy cv vy cv con0 wcel vz cv vy cv wcel cF cA wfn cG cA wfn wa vy cv cA
      wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx vy cv wral wa cF cA wfn cG cA wfn wa vz cv cA wss wa vx
      cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv
      wceq wa vx vz cv wral wa vy cv con0 wcel vz cv vy cv wcel vz cv vy cv wss
      cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv
      wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv wral wa cF cA wfn
      cG cA wfn wa vz cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv
      cG cfv cG vx cv cres cB cfv wceq wa vx vz cv wral wa wi vy cv vz cv
      onelss vz cv vy cv wss cF cA wfn cG cA wfn wa vy cv cA wss wa cF cA wfn
      cG cA wfn wa vz cv cA wss wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv
      cG cfv cG vx cv cres cB cfv wceq wa vx vy cv wral vx cv cF cfv cF vx cv
      cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vz cv wral
      vz cv vy cv wss vy cv cA wss vz cv cA wss cF cA wfn cG cA wfn wa vz cv vy
      cv cA sstr2 anim2d vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG
      vx cv cres cB cfv wceq wa vx vz cv vy cv ssralv anim12d syl6 com23
      ralrimdv vy cv con0 wcel vx cv cF cfv vx cv cG cfv wceq vx vz cv wral vz
      vy cv wral cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv cF cfv cF vx cv
      cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv wral
      vx cv cF cfv vx cv cG cfv wceq vx vy cv wral vy cv con0 wcel cF cA wfn cG
      cA wfn wa vy cv cA wss wa vx cv cF cfv vx cv cG cfv wceq vx vz cv wral vz
      vy cv wral vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv
      cres cB cfv wceq wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv
      wral wi vy cv con0 wcel cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv cF
      cfv vx cv cG cfv wceq vx vz cv wral vz vy cv wral vx cv cF cfv cF vx cv
      cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx vy cv wral
      vx cv cF cfv vx cv cG cfv wceq vx vy cv wral wi wi vx cv cF cfv vx cv cG
      cfv wceq vx vz cv wral vz vy cv wral vw cv cF cfv vw cv cG cfv wceq vw vx
      cv wral vx vy cv wral vy cv con0 wcel cF cA wfn cG cA wfn wa vy cv cA wss
      wa wa vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv wral
      wi vx cv cF cfv vx cv cG cfv wceq vx vz cv wral vw cv cF cfv vw cv cG cfv
      wceq vw vx cv wral vz vx vy cv vx cv cF cfv vx cv cG cfv wceq vx vz cv
      nfra1 vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vz nfv vx cv cF cfv vx
      cv cG cfv wceq vx vz cv wral vw cv cF cfv vw cv cG cfv wceq vw vz cv wral
      vz cv vx cv wceq vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vx cv cF
      cfv vx cv cG cfv wceq vw cv cF cfv vw cv cG cfv wceq vx vw vz cv vx cv vw
      cv wceq vx cv cF cfv vw cv cF cfv vx cv cG cfv vw cv cG cfv vx cv vw cv
      cF fveq2 vx cv vw cv cG fveq2 eqeq12d cbvralv vw cv cF cfv vw cv cG cfv
      wceq vw vz cv vx cv raleq syl5bb cbvral vy cv con0 wcel cF cA wfn cG cA
      wfn wa vy cv cA wss wa wa vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vx
      vy cv wral vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv
      cres cB cfv wceq wa vx cv cF cfv vx cv cG cfv wceq wi vx vy cv wral vx cv
      cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq
      wa vx vy cv wral vx cv cF cfv vx cv cG cfv wceq vx vy cv wral wi vy cv
      con0 wcel cF cA wfn cG cA wfn wa vy cv cA wss wa wa vw cv cF cfv vw cv cG
      cfv wceq vw vx cv wral vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG
      cfv cG vx cv cres cB cfv wceq wa vx cv cF cfv vx cv cG cfv wceq wi vx vy
      cv vy cv con0 wcel cF cA wfn cG cA wfn wa vy cv cA wss wa vx cv vy cv
      wcel vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vx cv cF cfv cF vx cv
      cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx cv cF cfv
      vx cv cG cfv wceq wi wi vy cv con0 wcel vx cv vy cv wcel cF cA wfn cG cA
      wfn wa vy cv cA wss wa vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vx cv
      cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq
      wa vx cv cF cfv vx cv cG cfv wceq wi wi vy cv con0 wcel vx cv vy cv wcel
      cF cA wfn cG cA wfn wa vy cv cA wss vw cv cF cfv vw cv cG cfv wceq vw vx
      cv wral vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres
      cB cfv wceq wa vx cv cF cfv vx cv cG cfv wceq wi wi vy cv con0 wcel vx cv
      vy cv wcel vx cv vy cv wss cF cA wfn cG cA wfn wa vy cv cA wss vw cv cF
      cfv vw cv cG cfv wceq vw vx cv wral vx cv cF cfv cF vx cv cres cB cfv
      wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa vx cv cF cfv vx cv cG cfv
      wceq wi wi wi wi vy cv vx cv onelss vx cv vy cv wss vy cv cA wss vx cv cA
      wss cF cA wfn cG cA wfn wa vw cv cF cfv vw cv cG cfv wceq vw vx cv wral
      vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv
      wceq wa vx cv cF cfv vx cv cG cfv wceq wi wi vx cv vy cv cA sstr2 vx cv
      cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq
      wa cF cA wfn cG cA wfn wa vx cv cA wss vw cv cF cfv vw cv cG cfv wceq vw
      vx cv wral vx cv cF cfv vx cv cG cfv wceq vx cv cF cfv cF vx cv cres cB
      cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa cF cA wfn cG cA wfn wa
      vx cv cA wss vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vx cv cF cfv vx
      cv cG cfv wceq cF cA wfn cG cA wfn wa vx cv cA wss wa vw cv cF cfv vw cv
      cG cfv wceq vw vx cv wral wa vx cv cF cfv vx cv cG cfv wceq vx cv cF cfv
      cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv wceq wa cF vx
      cv cres cB cfv cG vx cv cres cB cfv wceq cF cA wfn cG cA wfn wa vx cv cA
      wss wa vw cv cF cfv vw cv cG cfv wceq vw vx cv wral wa cF vx cv cres cG
      vx cv cres cB cF cA wfn cG cA wfn wa vx cv cA wss wa cF vx cv cres cG vx
      cv cres wceq vw cv cF cfv vw cv cG cfv wceq vw vx cv wral vw cA vx cv cF
      cG fvreseq biimpar fveq2d vx cv cF cfv cF vx cv cres cB cfv vx cv cG cfv
      cG vx cv cres cB cfv eqeq12 syl5ibr exp4c com4l syl9 syl6 imp4a com23
      imp31 ralimdva vx cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx
      cv cres cB cfv wceq wa vx cv cF cfv vx cv cG cfv wceq vx vy cv ralim syl6
      syl5bi ex com23 imp4a imim12d cF cA wfn cG cA wfn wa vy cv cA wss wa vx
      cv cF cfv cF vx cv cres cB cfv wceq vx cv cG cfv cG vx cv cres cB cfv
      wceq wa vx vy cv wral wa vx cv cF cfv vx cv cG cfv wceq vx vy cv wral
      pm2.43 syl56 tfis2 exp4c vtoclga mpii $.
  $}

  ${
    $d w A $.  $d w F $.  $d w G $.  $d w x $.
    $( Lemma for transfinite recursion.  This provides some messy details
       needed to link ~ tfrlem1 into the main proof.  (Contributed by NM,
       23-Mar-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    tfrlem2 $p |- ( ( F Fn A /\ G Fn A ) ->
       ( ( <. x , y >. e. F /\ <. x , z >. e. G ) ->
       ( A e. On -> ( A. w ( A e. On -> ( w e. A ->
          ( ( F ` w ) = ( B ` ( F |` w ) ) /\
            ( G ` w ) = ( B ` ( G |` w ) ) ) ) ) ->
       y = z ) ) ) ) $=
      cF cA wfn cG cA wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa
      cA con0 wcel cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv
      wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa wi wi vw wal vy cv vz cv
      wceq cA con0 wcel cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres
      cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa wi wi vw wal wa cF
      cA wfn cG cA wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa wa
      cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv
      cG cfv cG vw cv cres cB cfv wceq wa wi vw wal wa vy cv vz cv wceq cA con0
      wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG
      vw cv cres cB cfv wceq wa wi wa vw wal cA con0 wcel cA con0 wcel vw cv cA
      wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB
      cfv wceq wa wi wi wa vw wal cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw
      cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa wi vw wal
      wa cA con0 wcel cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB
      cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa wi wi vw wal wa cA
      con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG
      cfv cG vw cv cres cB cfv wceq wa wi wa cA con0 wcel cA con0 wcel vw cv cA
      wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB
      cfv wceq wa wi wi wa vw cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv
      cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa wi abai albii
      cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv
      cG cfv cG vw cv cres cB cfv wceq wa wi vw 19.28v cA con0 wcel cA con0
      wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG
      vw cv cres cB cfv wceq wa wi wi vw 19.28v 3bitr3ri cF cA wfn cG cA wfn wa
      vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa wa cA con0 wcel vw cv
      cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG vw cv cres
      cB cfv wceq wa wi vw wal wa wa vx cv cF cfv vx cv cG cfv wceq vy cv vz cv
      wceq cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw
      cv cG cfv cG vw cv cres cB cfv wceq wa wi vw wal wa cF cA wfn cG cA wfn
      wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa wa cA con0 wcel vw
      cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv
      wceq wa vw cA wral wa vx cv cF cfv vx cv cG cfv wceq vw cv cF cfv cF vw
      cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA wral
      vw cv cA wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG cfv cG vw
      cv cres cB cfv wceq wa wi vw wal cA con0 wcel vw cv cF cfv cF vw cv cres
      cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA df-ral anbi2i
      cF cA wfn cG cA wfn wa vx cv vy cv cop cF wcel cA con0 wcel vw cv cF cfv
      cF vw cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA
      wral wa vx cv cF cfv vx cv cG cfv wceq vx cv vz cv cop cG wcel cF cA wfn
      cG cA wfn wa vx cv vy cv cop cF wcel wa cA con0 wcel vw cv cF cfv cF vw
      cv cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA wral
      wa vx cv cF cfv vx cv cG cfv wceq cF cA wfn cG cA wfn wa vx cv vy cv cop
      cF wcel wa vx cv cA wcel cA con0 wcel vw cv cF cfv cF vw cv cres cB cfv
      wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA wral wa vw cv cF cfv
      vw cv cG cfv wceq vw cA wral vx cv cF cfv vx cv cG cfv wceq cF cA wfn vx
      cv vy cv cop cF wcel vx cv cA wcel cG cA wfn cA vx cv vy cv cF fnop
      adantlr cF cA wfn cG cA wfn wa cA con0 wcel vw cv cF cfv cF vw cv cres cB
      cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA wral wa vw cv cF
      cfv vw cv cG cfv wceq vw cA wral wi vx cv vy cv cop cF wcel cF cA wfn cG
      cA wfn wa cA con0 wcel vw cv cF cfv cF vw cv cres cB cfv wceq vw cv cG
      cfv cG vw cv cres cB cfv wceq wa vw cA wral vw cv cF cfv vw cv cG cfv
      wceq vw cA wral cA con0 wcel cF cA wfn cG cA wfn wa vw cv cF cfv cF vw cv
      cres cB cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa vw cA wral vw
      cv cF cfv vw cv cG cfv wceq vw cA wral wi vw cA cB cF cG tfrlem1 com12
      imp3a adantr vw cv cF cfv vw cv cG cfv wceq vx cv cF cfv vx cv cG cfv
      wceq vw vx cv cA vw cv vx cv wceq vw cv cF cfv vx cv cF cfv vw cv cG cfv
      vx cv cG cfv vw cv vx cv cF fveq2 vw cv vx cv cG fveq2 eqeq12d rspcv
      sylsyld imp adantlrr sylan2br cF cA wfn cG cA wfn wa vx cv vy cv cop cF
      wcel vx cv vz cv cop cG wcel wa wa vx cv cF cfv vx cv cG cfv wceq vy cv
      vz cv wceq wb cA con0 wcel vw cv cA wcel vw cv cF cfv cF vw cv cres cB
      cfv wceq vw cv cG cfv cG vw cv cres cB cfv wceq wa wi vw wal wa cF cA wfn
      cG cA wfn wa vx cv vy cv cop cF wcel vx cv vz cv cop cG wcel wa wa vx cv
      cF cfv vy cv wceq vx cv cG cfv vz cv wceq wa vx cv cF cfv vx cv cG cfv
      wceq vy cv vz cv wceq wb cF cA wfn cG cA wfn wa cF wfun cG wfun wa vx cv
      vy cv cop cF wcel vx cv vz cv cop cG wcel wa vx cv cF cfv vy cv wceq vx
      cv cG cfv vz cv wceq wa cF cA wfn cF wfun cG cA wfn cG wfun cA cF fnfun
      cA cG fnfun anim12i cF wfun vx cv vy cv cop cF wcel cG wfun vx cv vz cv
      cop cG wcel vx cv cF cfv vy cv wceq vx cv cG cfv vz cv wceq wa cF wfun vx
      cv vy cv cop cF wcel wa vx cv cF cfv vy cv wceq cG wfun vx cv vz cv cop
      cG wcel wa vx cv cG cfv vz cv wceq cF wfun vx cv vy cv cop cF wcel vx cv
      cF cfv vy cv wceq vx cv vy cv cF funopfv imp cG wfun vx cv vz cv cop cG
      wcel vx cv cG cfv vz cv wceq vx cv vz cv cG funopfv imp anim12i an4s
      sylan vx cv cF cfv vy cv vx cv cG cfv vz cv eqeq12 syl adantr mpbid
      sylan2b exp43 $.
  $}

  ${
    $d x y f g $.  $d x y z $.  $d g z $.  $d f g F $.  $d x z F $.
    tfrlem3.1 $e |- A = { f | E. x e. On ( f Fn x /\
                A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) } $.
    $( Lemma for transfinite recursion.  Let ` A ` be the class of "acceptable"
       functions.  The final thing we're interested in is the union of all
       these acceptable functions.  This lemma just changes some bound
       variables in ` A ` for later use.  (Contributed by NM, 9-Apr-1995.) $)
    tfrlem3 $p |- A = { g | E. z e. On ( g Fn z /\
                A. y e. z ( g ` y ) = ( F ` ( g |` y ) ) ) } $=
      cA vf cv vx cv wfn vy cv vf cv cfv vf cv vy cv cres cF cfv wceq vy vx cv
      wral wa vx con0 wrex vf cab vg cv vz cv wfn vy cv vg cv cfv vg cv vy cv
      cres cF cfv wceq vy vz cv wral wa vz con0 wrex vg cab tfrlem3.1 vg cv vz
      cv wfn vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vz cv wral wa vz
      con0 wrex vg vf cv vx cv wfn vy cv vf cv cfv vf cv vy cv cres cF cfv wceq
      vy vx cv wral wa vx con0 wrex vf cab vg cv vf cv vx cv wfn vy cv vf cv
      cfv vf cv vy cv cres cF cfv wceq vy vx cv wral wa vx con0 wrex vf cab
      wcel vg cv vx cv wfn vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vx
      cv wral wa vx con0 wrex vg cv vz cv wfn vy cv vg cv cfv vg cv vy cv cres
      cF cfv wceq vy vz cv wral wa vz con0 wrex vf cv vx cv wfn vy cv vf cv cfv
      vf cv vy cv cres cF cfv wceq vy vx cv wral wa vx con0 wrex vg cv vx cv
      wfn vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vx cv wral wa vx con0
      wrex vf vg cv vg vex vf cv vg cv wceq vf cv vx cv wfn vy cv vf cv cfv vf
      cv vy cv cres cF cfv wceq vy vx cv wral wa vg cv vx cv wfn vy cv vg cv
      cfv vg cv vy cv cres cF cfv wceq vy vx cv wral wa vx con0 vf cv vg cv
      wceq vf cv vx cv wfn vg cv vx cv wfn vy cv vf cv cfv vf cv vy cv cres cF
      cfv wceq vy vx cv wral vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vx
      cv wral vx cv vf cv vg cv fneq1 vf cv vg cv wceq vy cv vf cv cfv vf cv vy
      cv cres cF cfv wceq vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vx cv
      vf cv vg cv wceq vy cv vf cv cfv vy cv vg cv cfv vf cv vy cv cres cF cfv
      vg cv vy cv cres cF cfv vy cv vf cv vg cv fveq1 vf cv vg cv wceq vf cv vy
      cv cres vg cv vy cv cres cF vf cv vg cv vy cv reseq1 fveq2d eqeq12d
      ralbidv anbi12d rexbidv elab vg cv vx cv wfn vy cv vg cv cfv vg cv vy cv
      cres cF cfv wceq vy vx cv wral wa vg cv vz cv wfn vy cv vg cv cfv vg cv
      vy cv cres cF cfv wceq vy vz cv wral wa vx vz con0 vx cv vz cv wceq vg cv
      vx cv wfn vg cv vz cv wfn vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy
      vx cv wral vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vz cv wral vx
      cv vz cv vg cv fneq2 vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vx
      cv vz cv raleq anbi12d cbvrexv bitri abbi2i eqtri $.
  $}

  ${
    $d x y f g $.  $d f g F $.
    tfrlem3a.1 $e |- A = { f | E. x e. On ( f Fn x /\
                A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) } $.
    $( Lemma for transfinite recursion.  Let ` A ` be the class of "acceptable"
       functions.  The final thing we're interested in is the union of all
       these acceptable functions.  This lemma just changes some bound
       variables in ` A ` for later use.  (Contributed by NM, 22-Jul-2012.) $)
    tfrlem3a $p |- A = { g | E. x e. On ( g Fn x /\
                A. y e. x ( g ` y ) = ( F ` ( g |` y ) ) ) } $=
      cA vf cv vx cv wfn vy cv vf cv cfv vf cv vy cv cres cF cfv wceq vy vx cv
      wral wa vx con0 wrex vf cab vg cv vx cv wfn vy cv vg cv cfv vg cv vy cv
      cres cF cfv wceq vy vx cv wral wa vx con0 wrex vg cab tfrlem3a.1 vf cv vx
      cv wfn vy cv vf cv cfv vf cv vy cv cres cF cfv wceq vy vx cv wral wa vx
      con0 wrex vg cv vx cv wfn vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy
      vx cv wral wa vx con0 wrex vf vg vf cv vg cv wceq vf cv vx cv wfn vy cv
      vf cv cfv vf cv vy cv cres cF cfv wceq vy vx cv wral wa vg cv vx cv wfn
      vy cv vg cv cfv vg cv vy cv cres cF cfv wceq vy vx cv wral wa vx con0 vf
      cv vg cv wceq vf cv vx cv wfn vg cv vx cv wfn vy cv vf cv cfv vf cv vy cv
      cres cF cfv wceq vy vx cv wral vy cv vg cv cfv vg cv vy cv cres cF cfv
      wceq vy vx cv wral vx cv vf cv vg cv fneq1 vf cv vg cv wceq vy cv vf cv
      cfv vf cv vy cv cres cF cfv wceq vy cv vg cv cfv vg cv vy cv cres cF cfv
      wceq vy vx cv vf cv vg cv wceq vy cv vf cv cfv vy cv vg cv cfv vf cv vy
      cv cres cF cfv vg cv vy cv cres cF cfv vy cv vf cv vg cv fveq1 vf cv vg
      cv wceq vf cv vy cv cres vg cv vy cv cres cF vf cv vg cv vy cv reseq1
      fveq2d eqeq12d ralbidv anbi12d rexbidv cbvabv eqtri $.
  $}

