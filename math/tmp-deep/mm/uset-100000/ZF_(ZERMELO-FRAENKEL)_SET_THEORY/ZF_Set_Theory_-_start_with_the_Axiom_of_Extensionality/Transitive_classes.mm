
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Ordered-pair_class_abstractions_(class_builders).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Transitive classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare a new symbol. $)
  $c Tr $. $( Transitive predicate (read:  "the following class is
              transitive") $)

  $( Extend wff notation to include transitive classes.  Notation from
     [TakeutiZaring] p. 35. $)
  wtr $a wff Tr A $.

  $( Define the transitive class predicate.  Not to be confused with a
     transitive relation (see ~ cotr ).  Definition of [Enderton] p. 71
     extended to arbitrary classes.  For alternate definitions, see ~ dftr2
     (which is suggestive of the word "transitive"), ~ dftr3 , ~ dftr4 ,
     ~ dftr5 , and (when ` A ` is a set) ~ unisuc .  The term "complete" is
     used instead of "transitive" in Definition 3 of [Suppes] p. 130.
     (Contributed by NM, 29-Aug-1993.) $)
  df-tr $a |- ( Tr A <-> U. A C_ A ) $.

  ${
    $d x y A $.
    $( An alternate way of defining a transitive class.  Exercise 7 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 24-Apr-1994.) $)
    dftr2 $p |- ( Tr A <-> A. x A. y ( ( x e. y /\ y e. A ) -> x e. A ) ) $=
      cA cuni cA wss vx cv cA cuni wcel vx cv cA wcel wi vx wal cA wtr vx cv vy
      cv wcel vy cv cA wcel wa vx cv cA wcel wi vy wal vx wal vx cA cuni cA
      dfss2 cA df-tr vx cv vy cv wcel vy cv cA wcel wa vx cv cA wcel wi vy wal
      vx cv cA cuni wcel vx cv cA wcel wi vx vx cv vy cv wcel vy cv cA wcel wa
      vx cv cA wcel wi vy wal vx cv vy cv wcel vy cv cA wcel wa vy wex vx cv cA
      wcel wi vx cv cA cuni wcel vx cv cA wcel wi vx cv vy cv wcel vy cv cA
      wcel wa vx cv cA wcel vy 19.23v vx cv cA cuni wcel vx cv vy cv wcel vy cv
      cA wcel wa vy wex vx cv cA wcel vy vx cv cA eluni imbi1i bitr4i albii
      3bitr4i $.

    $( An alternate way of defining a transitive class.  (Contributed by NM,
       20-Mar-2004.) $)
    dftr5 $p |- ( Tr A <-> A. x e. A A. y e. x y e. A ) $=
      cA wtr vy cv vx cv wcel vx cv cA wcel wa vy cv cA wcel wi vx wal vy wal
      vy cv cA wcel vy vx cv wral vx cA wral vy vx cA dftr2 vy cv vx cv wcel vx
      cv cA wcel wa vy cv cA wcel wi vx wal vy wal vy cv vx cv wcel vx cv cA
      wcel wa vy cv cA wcel wi vy wal vx wal vy cv cA wcel vy vx cv wral vx cA
      wral vy cv vx cv wcel vx cv cA wcel wa vy cv cA wcel wi vy vx alcom vy cv
      vx cv wcel vx cv cA wcel wa vy cv cA wcel wi vy wal vx wal vx cv cA wcel
      vy cv cA wcel vy vx cv wral wi vx wal vy cv cA wcel vy vx cv wral vx cA
      wral vy cv vx cv wcel vx cv cA wcel wa vy cv cA wcel wi vy wal vx cv cA
      wcel vy cv cA wcel vy vx cv wral wi vx vy cv vx cv wcel vx cv cA wcel wa
      vy cv cA wcel wi vy wal vx cv cA wcel vy cv cA wcel wi vy vx cv wral vx
      cv cA wcel vy cv cA wcel vy vx cv wral wi vy cv vx cv wcel vx cv cA wcel
      wa vy cv cA wcel wi vy wal vy cv vx cv wcel vx cv cA wcel vy cv cA wcel
      wi wi vy wal vx cv cA wcel vy cv cA wcel wi vy vx cv wral vy cv vx cv
      wcel vx cv cA wcel wa vy cv cA wcel wi vy cv vx cv wcel vx cv cA wcel vy
      cv cA wcel wi wi vy vy cv vx cv wcel vx cv cA wcel vy cv cA wcel impexp
      albii vx cv cA wcel vy cv cA wcel wi vy vx cv df-ral bitr4i vx cv cA wcel
      vy cv cA wcel vy vx cv r19.21v bitri albii vy cv cA wcel vy vx cv wral vx
      cA df-ral bitr4i bitri bitri $.

    $( An alternate way of defining a transitive class.  Definition 7.1 of
       [TakeutiZaring] p. 35.  (Contributed by NM, 29-Aug-1993.) $)
    dftr3 $p |- ( Tr A <-> A. x e. A x C_ A ) $=
      cA wtr vy cv cA wcel vy vx cv wral vx cA wral vx cv cA wss vx cA wral vx
      vy cA dftr5 vx cv cA wss vy cv cA wcel vy vx cv wral vx cA vy vx cv cA
      dfss3 ralbii bitr4i $.
  $}

  $( An alternate way of defining a transitive class.  Definition of [Enderton]
     p. 71.  (Contributed by NM, 29-Aug-1993.) $)
  dftr4 $p |- ( Tr A <-> A C_ ~P A ) $=
    cA wtr cA cuni cA wss cA cA cpw wss cA df-tr cA cA sspwuni bitr4i $.

  $( Equality theorem for the transitive class predicate.  (Contributed by NM,
     17-Sep-1993.) $)
  treq $p |- ( A = B -> ( Tr A <-> Tr B ) ) $=
    cA cB wceq cA cuni cA wss cB cuni cB wss cA wtr cB wtr cA cB wceq cA cuni
    cA wss cB cuni cA wss cB cuni cB wss cA cB wceq cA cuni cB cuni cA cA cB
    unieq sseq1d cA cB cB cuni sseq2 bitrd cA df-tr cB df-tr 3bitr4g $.

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( In a transitive class, the membership relation is transitive.
       (Contributed by NM, 19-Apr-1994.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    trel $p |- ( Tr A -> ( ( B e. C /\ C e. A ) -> B e. A ) ) $=
      cA wtr vy cv vx cv wcel vx cv cA wcel wa vy cv cA wcel wi vx wal vy wal
      cB cC wcel cC cA wcel wa cB cA wcel wi vy vx cA dftr2 vy cv vx cv wcel vx
      cv cA wcel wa vy cv cA wcel wi vx wal vy wal cB cC wcel cC cA wcel wa cB
      cA wcel vy cv vx cv wcel vx cv cA wcel wa vy cv cA wcel wi cB cC wcel cC
      cA wcel wa cB cA wcel wi vy vx cB cC cC cA vy cv cB wceq vx cv cC wceq wa
      vy cv vx cv wcel vx cv cA wcel wa cB cC wcel cC cA wcel wa vy cv cA wcel
      cB cA wcel vy cv cB wceq vx cv cC wceq wa vy cv vx cv wcel cB cC wcel vx
      cv cA wcel cC cA wcel vy cv cB vx cv cC eleq12 vx cv cC wceq vx cv cA
      wcel cC cA wcel wb vy cv cB wceq vx cv cC cA eleq1 adantl anbi12d vy cv
      cB wceq vy cv cA wcel cB cA wcel wb vx cv cC wceq vy cv cB cA eleq1
      adantr imbi12d spc2gv pm2.43b sylbi $.
  $}

  $( In a transitive class, the membership relation is transitive.
     (Contributed by NM, 19-Apr-1994.) $)
  trel3 $p |- ( Tr A -> ( ( B e. C /\ C e. D /\ D e. A ) -> B e. A ) ) $=
    cA wtr cB cC wcel cC cD wcel cD cA wcel w3a cB cC wcel cC cA wcel wa cB cA
    wcel cB cC wcel cC cD wcel cD cA wcel w3a cB cC wcel cC cD wcel cD cA wcel
    wa wa cA wtr cB cC wcel cC cA wcel wa cB cC wcel cC cD wcel cD cA wcel
    3anass cA wtr cC cD wcel cD cA wcel wa cC cA wcel cB cC wcel cA cC cD trel
    anim2d syl5bi cA cB cC trel syld $.

  ${
    $d x A $.  $d x B $.
    $( An element of a transitive class is a subset of the class.  (Contributed
       by NM, 7-Aug-1994.) $)
    trss $p |- ( Tr A -> ( B e. A -> B C_ A ) ) $=
      cA wtr cB cA wcel cB cA wss cA wtr vx cv cA wcel vx cv cA wss wi wi cA
      wtr cB cA wcel cB cA wss wi wi vx cB cA vx cv cB wceq vx cv cA wcel vx cv
      cA wss wi cB cA wcel cB cA wss wi cA wtr vx cv cB wceq vx cv cA wcel cB
      cA wcel vx cv cA wss cB cA wss vx cv cB cA eleq1 vx cv cB cA sseq1
      imbi12d imbi2d cA wtr vx cv cA wss vx cA wral vx cv cA wcel vx cv cA wss
      wi vx cA dftr3 vx cv cA wss vx cA rsp sylbi vtoclg pm2.43b $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The intersection of transitive classes is transitive.  (Contributed by
       NM, 9-May-1994.) $)
    trin $p |- ( ( Tr A /\ Tr B ) -> Tr ( A i^i B ) ) $=
      cA wtr cB wtr wa vx cv cA cB cin wss vx cA cB cin wral cA cB cin wtr cA
      wtr cB wtr wa vx cv cA cB cin wss vx cA cB cin cA wtr cB wtr wa vx cv cA
      cB cin wcel vx cv cA wss vx cv cB wss wa vx cv cA cB cin wss vx cv cA cB
      cin wcel vx cv cA wcel vx cv cB wcel wa cA wtr cB wtr wa vx cv cA wss vx
      cv cB wss wa vx cv cA cB elin cA wtr vx cv cA wcel vx cv cA wss cB wtr vx
      cv cB wcel vx cv cB wss cA vx cv trss cB vx cv trss im2anan9 syl5bi vx cv
      cA cB ssin syl6ib ralrimiv vx cA cB cin dftr3 sylibr $.
  $}

  $( The empty set is transitive.  (Contributed by NM, 16-Sep-1993.) $)
  tr0 $p |- Tr (/) $=
    c0 wtr c0 c0 cpw wss c0 cpw 0ss c0 dftr4 mpbir $.

  $( The universe is transitive.  (Contributed by NM, 14-Sep-2003.) $)
  trv $p |- Tr _V $=
    cvv wtr cvv cuni cvv wss cvv cuni ssv cvv df-tr mpbir $.

  ${
    $d x y z A $.  $d y z B $.
    $( The indexed union of a class of transitive sets is transitive.
       (Contributed by Mario Carneiro, 16-Nov-2014.) $)
    triun $p |- ( A. x e. A Tr B -> Tr U_ x e. A B ) $=
      cB wtr vx cA wral vy cv vx cA cB ciun wss vy vx cA cB ciun wral vx cA cB
      ciun wtr cB wtr vx cA wral vy cv vx cA cB ciun wss vy vx cA cB ciun vy cv
      vx cA cB ciun wcel cB wtr vx cA wral vy cv cB wcel vx cA wrex vy cv vx cA
      cB ciun wss vx vy cv cA cB eliun cB wtr vx cA wral vy cv cB wcel vx cA
      wrex wa cB wtr vy cv cB wcel wa vx cA wrex vy cv vx cA cB ciun wss cB wtr
      vy cv cB wcel vx cA r19.29 cB wtr vy cv cB wcel wa vy cv vx cA cB ciun
      wss vx cA vx vy cv vx cA cB ciun vx vy cv nfcv vx cA cB nfiu1 nfss cB wtr
      vy cv cB wcel wa vy cv cB wss vx cv cA wcel vy cv vx cA cB ciun wss cB
      wtr vy cv cB wcel vy cv cB wss cB vy cv trss imp vx cv cA wcel cB vx cA
      cB ciun wss vy cv cB wss vy cv vx cA cB ciun wss vx cA cB ssiun2 vy cv cB
      vx cA cB ciun sstr2 syl5com syl5 rexlimi syl sylan2b ralrimiva vy vx cA
      cB ciun dftr3 sylibr $.

    $( The union of a class of transitive sets is transitive.  Exercise 5(a) of
       [Enderton] p. 73.  (Contributed by Scott Fenton, 21-Feb-2011.)  (Proof
       shortened by Mario Carneiro, 26-Apr-2014.) $)
    truni $p |- ( A. x e. A Tr x -> Tr U. A ) $=
      vx cv wtr vx cA wral vx cA vx cv ciun wtr cA cuni wtr vx cA vx cv triun
      cA cuni vx cA vx cv ciun wceq cA cuni wtr vx cA vx cv ciun wtr wb vx cA
      uniiun cA cuni vx cA vx cv ciun treq ax-mp sylibr $.

    $( The intersection of a class of transitive sets is transitive.  Exercise
       5(b) of [Enderton] p. 73.  (Contributed by Scott Fenton,
       25-Feb-2011.) $)
    trint $p |- ( A. x e. A Tr x -> Tr |^| A ) $=
      vx cv wtr vx cA wral vy vx wel vx cA wral vy cv vx cv wss vx cA wral wi
      vy wal cA cint wtr vx cv wtr vx cA wral vy vx wel vy cv vx cv wss wi vx
      cA wral vy wal vy vx wel vx cA wral vy cv vx cv wss vx cA wral wi vy wal
      vx cv wtr vx cA wral vy cv vx cv wss vy vx cv wral vx cA wral vy vx wel
      vy cv vx cv wss wi vx cA wral vy wal vx cv wtr vx cA wral vy cv vx cv wss
      vy vx cv wral vx cA wral vx cv wtr vy cv vx cv wss vy vx cv wral vx cA vy
      vx cv dftr3 ralbii biimpi vy cv vx cv wss vy vx cv wral vx cA wral vy vx
      wel vy cv vx cv wss wi vy wal vx cA wral vy vx wel vy cv vx cv wss wi vx
      cA wral vy wal vy cv vx cv wss vy vx cv wral vy vx wel vy cv vx cv wss wi
      vy wal vx cA vy cv vx cv wss vy vx cv df-ral ralbii vy vx wel vy cv vx cv
      wss wi vx vy cA ralcom4 bitri sylib vy vx wel vy cv vx cv wss wi vx cA
      wral vy vx wel vx cA wral vy cv vx cv wss vx cA wral wi vy vy vx wel vy
      cv vx cv wss vx cA ralim alimi syl cA cint wtr vy cv cA cint wss vy cA
      cint wral vy vx wel vx cA wral vy cv vx cv wss vx cA wral wi vy wal vy cA
      cint dftr3 vy cv cA cint wss vy cA cint wral vy cv cA cint wcel vy cv cA
      cint wss wi vy wal vy vx wel vx cA wral vy cv vx cv wss vx cA wral wi vy
      wal vy cv cA cint wss vy cA cint df-ral vy cv cA cint wcel vy cv cA cint
      wss wi vy vx wel vx cA wral vy cv vx cv wss vx cA wral wi vy vy cv cA
      cint wcel vy vx wel vx cA wral vy cv cA cint wss vy cv vx cv wss vx cA
      wral vx vy cv cA vy vex elint2 vx vy cv cA ssint imbi12i albii bitri
      bitri sylibr $.

    $( If ` A ` is transitive and non-null, then ` |^| A ` is a subset of
       ` A ` .  (Contributed by Scott Fenton, 3-Mar-2011.) $)
    trintss $p |- ( ( A =/= (/) /\ Tr A ) -> |^| A C_ A ) $=
      cA c0 wne cA wtr wa vy cA cint cA vy cv cA cint wcel vy vx wel vx cA wral
      cA c0 wne cA wtr wa vy cv cA wcel vx vy cv cA vy vex elint2 cA c0 wne vy
      vx wel vx cA wral vy vx wel vx cA wrex cA wtr vy cv cA wcel cA c0 wne vy
      vx wel vx cA wral vy vx wel vx cA wrex vy vx wel vx cA r19.2z ex cA wtr
      vy vx wel vy cv cA wcel vx cA cA wtr vy vx wel vx cv cA wcel vy cv cA
      wcel cA vy cv vx cv trel exp3acom23 rexlimdv sylan9 syl5bi ssrdv $.

    $( Any non-empty transitive class includes its intersection.  Exercise 2 in
       [TakeutiZaring] p. 44.  (Contributed by Andrew Salmon, 14-Nov-2011.) $)
    trint0 $p |- ( ( Tr A /\ A =/= (/) ) -> |^| A C_ A ) $=
      cA c0 wne cA wtr cA cint cA wss cA c0 wne vx cv cA wcel vx wex cA wtr cA
      cint cA wss wi vx cA n0 vx cv cA wcel cA wtr cA cint cA wss wi vx vx cv
      cA wcel cA cint vx cv wss cA wtr vx cv cA wss cA cint cA wss vx cv cA
      intss1 cA wtr vx cv cA wcel vx cv cA wss cA vx cv trss com12 cA cint vx
      cv cA sstr2 sylsyld exlimiv sylbi impcom $.
  $}


