
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Power_class_of_union_and_intersection.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Epsilon and identity relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new constant symbols. $)
  $c _E $. $( Letter E (for epsilon relation) $)
  $c _I $.  $( Letter I (for identity relation) $)

  $( Extend class notation to include the epsilon relation. $)
  cep $a class _E $.

  $( Extend the definition of a class to include identity relation. $)
  cid $a class _I $.

  ${
    $d x y $.
    $( Define the epsilon relation.  Similar to Definition 6.22 of
       [TakeutiZaring] p. 30.  The epsilon relation and set membership are the
       same, that is, ` ( A _E B <-> A e. B ) ` when ` B ` is a set by
       ~ epelg .  Thus, ` 5 _E { 1 , 5 } ` ( ~ ex-eprel ).  (Contributed by NM,
       13-Aug-1995.) $)
    df-eprel $a |- _E = { <. x , y >. | x e. y } $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( The epsilon relation and membership are the same.  General version of
       ~ epel .  (Contributed by Scott Fenton, 27-Mar-2011.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
    epelg $p |- ( B e. V -> ( A _E B <-> A e. B ) ) $=
      cB cV wcel cA cvv wcel cA cB cep wbr cA cB wcel cA cB cep wbr cA cvv wcel
      wi cB cV wcel cA cB cep wbr cA cB cop cep wcel cA cvv wcel cA cB cep
      df-br cA cvv wcel cA cB cop vx cv vy cv wcel vx vy copab cep cA cB cop vx
      cv vy cv wcel vx vy copab wcel cA cB cop vx cv vy cv cop wceq vx cv vy cv
      wcel wa vy wex vx wex cA cvv wcel vx cv vy cv wcel vx vy cA cB cop elopab
      cA cB cop vx cv vy cv cop wceq vx cv vy cv wcel wa cA cvv wcel vx vy cA
      cB cop vx cv vy cv cop wceq cA cvv wcel vx cv vy cv wcel cA cB cop vx cv
      vy cv cop wceq cA cvv wcel cB cvv wcel cA cB cop vx cv vy cv cop wceq cA
      cvv wcel cB cvv wcel wa vx cv cvv wcel vy cv cvv wcel wa vx cv cvv wcel
      vy cv cvv wcel vx vex vy vex pm3.2i cA cB vx cv vy cv opeqex mpbiri
      simpld adantr exlimivv sylbi vx vy df-eprel eleq2s sylbi a1i cA cB wcel
      cA cvv wcel wi cB cV wcel cA cB elex a1i cA cvv wcel cB cV wcel cA cB cep
      wbr cA cB wcel wb vx cv vy cv wcel cA cB wcel vx vy cA cB cep cvv cV vx
      cv cA vy cv cB eleq12 vx vy df-eprel brabga expcom pm5.21ndd $.
  $}

  ${
    epelc.1 $e |- B e. _V $.
    $( The epsilon relationship and the membership relation are the same.
       (Contributed by Scott Fenton, 11-Apr-2012.) $)
    epelc $p |- ( A _E B <-> A e. B ) $=
      cB cvv wcel cA cB cep wbr cA cB wcel wb epelc.1 cA cB cvv epelg ax-mp $.
  $}

  $( The epsilon relation and the membership relation are the same.
     (Contributed by NM, 13-Aug-1995.) $)
  epel $p |- ( x _E y <-> x e. y ) $=
    vx cv vy cv vy vex epelc $.

  ${
    $d x y $.
    $( Define the identity relation.  Definition 9.15 of [Quine] p. 64.  For
       example, ` 5 _I 5 ` and ` -. 4 _I 5 ` ( ~ ex-id ).  (Contributed by NM,
       13-Aug-1995.) $)
    df-id $a |- _I = { <. x , y >. | x = y } $.
  $}

  ${
    $d w z x $.  $d w z y $.
    $( A stronger version of ~ df-id that doesn't require ` x ` and ` y ` to be
       distinct.  Ordinarily, we wouldn't use this as a definition, since
       non-distinct dummy variables would make soundness verification more
       difficult (as the proof here shows).  The proof can be instructive in
       showing how distinct variable requirements may be eliminated, a task
       that is not necessarily obvious.  (Contributed by NM, 5-Feb-2008.)
       (Revised by Mario Carneiro, 18-Nov-2016.) $)
    dfid3 $p |- _I = { <. x , y >. | x = y } $=
      cid vx cv vz cv wceq vx vz copab vx cv vy cv wceq vx vy copab vx vz df-id
      vw cv vx cv vz cv cop wceq vx cv vz cv wceq wa vz wex vx wex vw cab vw cv
      vx cv vy cv cop wceq vx cv vy cv wceq wa vy wex vx wex vw cab vx cv vz cv
      wceq vx vz copab vx cv vy cv wceq vx vy copab vw cv vx cv vz cv cop wceq
      vx cv vz cv wceq wa vz wex vx wex vw cv vx cv vy cv cop wceq vx cv vy cv
      wceq wa vy wex vx wex vw vx cv vy cv wceq vx wal vw cv vx cv vz cv cop
      wceq vx cv vz cv wceq wa vz wex vx wex vw cv vx cv vy cv cop wceq vx cv
      vy cv wceq wa vy wex vx wex wb vw cv vx cv vz cv cop wceq vx cv vz cv
      wceq wa vz wex vx wex vw cv vx cv vx cv cop wceq vx cv vx cv wceq wa vx
      wex vx wex vx cv vy cv wceq vx wal vw cv vx cv vy cv cop wceq vx cv vy cv
      wceq wa vy wex vx wex vw cv vx cv vz cv cop wceq vx cv vz cv wceq wa vz
      wex vx wex vw cv vx cv vx cv cop wceq vx cv vx cv wceq wa vx wex vw cv vx
      cv vx cv cop wceq vx cv vx cv wceq wa vx wex vx wex vw cv vx cv vz cv cop
      wceq vx cv vz cv wceq wa vz wex vw cv vx cv vx cv cop wceq vx cv vx cv
      wceq wa vx vw cv vx cv vz cv cop wceq vx cv vz cv wceq wa vz wex vz cv vx
      cv wceq vw cv vx cv vz cv cop wceq wa vz wex vw cv vx cv vx cv cop wceq
      vw cv vx cv vx cv cop wceq vx cv vx cv wceq wa vw cv vx cv vz cv cop wceq
      vx cv vz cv wceq wa vz cv vx cv wceq vw cv vx cv vz cv cop wceq wa vz vw
      cv vx cv vz cv cop wceq vx cv vz cv wceq wa vx cv vz cv wceq vw cv vx cv
      vz cv cop wceq wa vz cv vx cv wceq vw cv vx cv vz cv cop wceq wa vw cv vx
      cv vz cv cop wceq vx cv vz cv wceq ancom vx cv vz cv wceq vz cv vx cv
      wceq vw cv vx cv vz cv cop wceq vx vz equcom anbi1i bitri exbii vw cv vx
      cv vz cv cop wceq vw cv vx cv vx cv cop wceq vz vx cv vx vex vz cv vx cv
      wceq vx cv vz cv cop vx cv vx cv cop vw cv vz cv vx cv vx cv opeq2 eqeq2d
      ceqsexv vx cv vx cv wceq vw cv vx cv vx cv cop wceq vx equid biantru
      3bitri exbii vw cv vx cv vx cv cop wceq vx cv vx cv wceq wa vx wex vx vw
      cv vx cv vx cv cop wceq vx cv vx cv wceq wa vx nfe1 19.9 bitr4i vw cv vx
      cv vx cv cop wceq vx cv vx cv wceq wa vx wex vw cv vx cv vy cv cop wceq
      vx cv vy cv wceq wa vy wex vx vy vx vw cv vx cv vx cv cop wceq vx cv vx
      cv wceq wa vw cv vx cv vy cv cop wceq vx cv vy cv wceq wa vx vy vx cv vy
      cv wceq vw cv vx cv vx cv cop wceq vx cv vx cv wceq wa vw cv vx cv vy cv
      cop wceq vx cv vy cv wceq wa wb vx vx cv vy cv wceq vw cv vx cv vx cv cop
      wceq vw cv vx cv vy cv cop wceq vx cv vx cv wceq vx cv vy cv wceq vx cv
      vy cv wceq vx cv vx cv cop vx cv vy cv cop vw cv vx cv vy cv vx cv opeq2
      eqeq2d vx vy vx equequ2 anbi12d sps drex1 drex2 syl5bb vx cv vy cv wceq
      vx wal wn vw cv vx cv vz cv cop wceq vx cv vz cv wceq wa vz wex vw cv vx
      cv vy cv cop wceq vx cv vy cv wceq wa vy wex vx vx vy vx nfnae vx cv vy
      cv wceq vx wal wn vw cv vx cv vz cv cop wceq vx cv vz cv wceq wa vw cv vx
      cv vy cv cop wceq vx cv vy cv wceq wa vz vy vx vy vy nfnae vx cv vy cv
      wceq vx wal wn vw cv vx cv vz cv cop wceq vx cv vz cv wceq vy vx cv vy cv
      wceq vx wal wn vy vw cv vx cv vz cv cop vx cv vy cv wceq vx wal wn vy vw
      cv nfcvd vx cv vy cv wceq vx wal wn vy vx cv vz cv vx vy nfcvf2 vx cv vy
      cv wceq vx wal wn vy vz cv nfcvd nfopd nfeqd vx cv vy cv wceq vx wal wn
      vy vx cv vz cv vx vy nfcvf2 vx cv vy cv wceq vx wal wn vy vz cv nfcvd
      nfeqd nfand vz cv vy cv wceq vw cv vx cv vz cv cop wceq vx cv vz cv wceq
      wa vw cv vx cv vy cv cop wceq vx cv vy cv wceq wa wb wi vx cv vy cv wceq
      vx wal wn vz cv vy cv wceq vw cv vx cv vz cv cop wceq vw cv vx cv vy cv
      cop wceq vx cv vz cv wceq vx cv vy cv wceq vz cv vy cv wceq vx cv vz cv
      cop vx cv vy cv cop vw cv vz cv vy cv vx cv opeq2 eqeq2d vz vy vx equequ2
      anbi12d a1i cbvexd exbid pm2.61i abbii vx cv vz cv wceq vx vz vw df-opab
      vx cv vy cv wceq vx vy vw df-opab 3eqtr4i eqtri $.
  $}

  $( Alternate definition of the identity relation.  (Contributed by NM,
     15-Mar-2007.) $)
  dfid2 $p |- _I = { <. x , x >. | x = x } $=
    vx vx dfid3 $.


