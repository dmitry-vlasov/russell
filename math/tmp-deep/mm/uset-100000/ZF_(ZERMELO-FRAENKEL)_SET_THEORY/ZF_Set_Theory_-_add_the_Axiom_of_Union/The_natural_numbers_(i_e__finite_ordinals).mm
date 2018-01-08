
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Transfinite_induction.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The natural numbers (i.e. finite ordinals)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbol. $)
  $c om $. $( Greek letter omega $)

  $( Extend class notation to include the class of natural numbers. $)
  com $a class om $.

  ${
    $d x y $.
    $( Define the class of natural numbers, which are all ordinal numbers that
       are less than every limit ordinal, i.e. all finite ordinals.  Our
       definition is a variant of the Definition of N of [BellMachover]
       p. 471.  See ~ dfom2 for an alternate definition.  Later, when we assume
       the Axiom of Infinity, we show ` om ` is a set in ~ omex , and ` om `
       can then be defined per ~ dfom3 (the smallest inductive set) and
       ~ dfom4 .

       _Note_: the natural numbers ` om ` are a subset of the ordinal numbers
       ~ df-on .  They are completely different from the natural numbers ` NN `
       ( ~ df-nn ) that are a subset of the complex numbers defined much later
       in our development, although the two sets have analogous properties and
       operations defined on them.  (Contributed by NM, 15-May-1994.) $)
    df-om $a |- om = { x e. On | A. y ( Lim y -> x e. y ) } $.
  $}

  ${
    $d x z $.  $d y z $.
    $( An alternate definition of the set of natural numbers ` om ` .
       Definition 7.28 of [TakeutiZaring] p. 42, who use the symbol K_I for the
       inner class builder of non-limit ordinal numbers (see ~ nlimon ).
       (Contributed by NM, 1-Nov-2004.) $)
    dfom2 $p |- om = { x e. On | suc x C_ { y e. On | -. Lim y } } $=
      com vz cv wlim vx cv vz cv wcel wi vz wal vx con0 crab vx cv csuc vy cv
      wlim wn vy con0 crab wss vx con0 crab vx vz df-om vz cv wlim vx cv vz cv
      wcel wi vz wal vx cv csuc vy cv wlim wn vy con0 crab wss vx con0 vx cv
      con0 wcel vz cv wlim vx cv vz cv wcel wi vz wal vz cv vx cv csuc wcel vz
      cv vy cv wlim wn vy con0 crab wcel wi vz wal vx cv csuc vy cv wlim wn vy
      con0 crab wss vx cv con0 wcel vz cv wlim vx cv vz cv wcel wi vz cv vx cv
      csuc wcel vz cv vy cv wlim wn vy con0 crab wcel wi vz vx cv con0 wcel vz
      cv wlim vx cv vz cv wcel wi vz cv con0 wcel vz cv vx cv csuc wcel vz cv
      vy cv wlim wn vy con0 crab wcel wi wi vz cv vx cv csuc wcel vz cv vy cv
      wlim wn vy con0 crab wcel wi vx cv con0 wcel vz cv con0 wcel vz cv vx cv
      csuc wcel vz cv vy cv wlim wn vy con0 crab wcel wi wi vz cv con0 wcel vx
      cv vz cv wcel wn vz cv con0 wcel vz cv wlim wn wa wi wi vz cv wlim vx cv
      vz cv wcel wi vx cv con0 wcel vz cv con0 wcel vz cv vx cv csuc wcel vz cv
      vy cv wlim wn vy con0 crab wcel wi vx cv vz cv wcel wn vz cv con0 wcel vz
      cv wlim wn wa wi vx cv con0 wcel vz cv con0 wcel wa vz cv vx cv csuc wcel
      vx cv vz cv wcel wn vz cv vy cv wlim wn vy con0 crab wcel vz cv con0 wcel
      vz cv wlim wn wa vz cv con0 wcel vx cv con0 wcel vz cv vx cv csuc wcel vx
      cv vz cv wcel wn wb vz cv con0 wcel vx cv con0 wcel wa vz cv vx cv wss vz
      cv vx cv csuc wcel vx cv vz cv wcel wn vz cv vx cv onsssuc vz cv vx cv
      ontri1 bitr3d ancoms vz cv vy cv wlim wn vy con0 crab wcel vz cv con0
      wcel vz cv wlim wn wa wb vx cv con0 wcel vz cv con0 wcel wa vy cv wlim wn
      vz cv wlim wn vy vz cv con0 vy cv vz cv wceq vy cv wlim vz cv wlim vy cv
      vz cv limeq notbid elrab a1i imbi12d pm5.74da vz cv wlim vx cv vz cv wcel
      wi vz cv con0 wcel vz cv wlim wa vx cv vz cv wcel wi vz cv con0 wcel vz
      cv wlim vx cv vz cv wcel wi wi vz cv con0 wcel vx cv vz cv wcel wn vz cv
      con0 wcel vz cv wlim wn wa wi wi vz cv wlim vz cv con0 wcel vz cv wlim wa
      vx cv vz cv wcel vz cv wlim vz cv con0 wcel vz cv cvv wcel vz cv wlim vz
      cv con0 wcel vz vex vz cv cvv limelon mpan pm4.71ri imbi1i vz cv con0
      wcel vz cv wlim vx cv vz cv wcel impexp vz cv con0 wcel vz cv wlim vx cv
      vz cv wcel wi vx cv vz cv wcel wn vz cv con0 wcel vz cv wlim wn wa wi vz
      cv wlim vx cv vz cv wcel wi vx cv vz cv wcel wn vz cv wlim wn wi vz cv
      con0 wcel vx cv vz cv wcel wn vz cv con0 wcel vz cv wlim wn wa wi vz cv
      wlim vx cv vz cv wcel con34b vz cv con0 wcel vz cv wlim wn vz cv con0
      wcel vz cv wlim wn wa vx cv vz cv wcel wn vz cv con0 wcel vz cv wlim wn
      ibar imbi2d syl5bb pm5.74i 3bitri syl6rbbr vz cv con0 wcel vz cv vx cv
      csuc wcel vz cv vy cv wlim wn vy con0 crab wcel wi wi vz cv con0 wcel vz
      cv vx cv csuc wcel wa vz cv vy cv wlim wn vy con0 crab wcel wi vx cv con0
      wcel vz cv vx cv csuc wcel vz cv vy cv wlim wn vy con0 crab wcel wi vz cv
      con0 wcel vz cv vx cv csuc wcel vz cv vy cv wlim wn vy con0 crab wcel
      impexp vx cv con0 wcel vz cv con0 wcel vz cv vx cv csuc wcel wa vz cv vx
      cv csuc wcel vz cv vy cv wlim wn vy con0 crab wcel vx cv con0 wcel vz cv
      con0 wcel vz cv vx cv csuc wcel wa vz cv vx cv csuc wcel vz cv con0 wcel
      vz cv vx cv csuc wcel simpr vx cv con0 wcel vz cv vx cv csuc wcel vz cv
      con0 wcel vx cv con0 wcel vx cv csuc con0 wcel vz cv vx cv csuc wcel vz
      cv con0 wcel wi vx cv suceloni vx cv csuc con0 wcel vz cv vx cv csuc wcel
      vz cv con0 wcel vx cv csuc vz cv onelon ex syl ancrd impbid2 imbi1d
      syl5bbr bitrd albidv vz vx cv csuc vy cv wlim wn vy con0 crab dfss2
      syl6bbr rabbiia eqtri $.
  $}

  ${
    $d A x y $.
    $( Membership in omega.  The left conjunct can be eliminated if we assume
       the Axiom of Infinity; see ~ elom3 .  (Contributed by NM,
       15-May-1994.) $)
    elom $p |- ( A e. om <-> ( A e. On /\ A. x ( Lim x -> A e. x ) ) ) $=
      vx cv wlim vy cv vx cv wcel wi vx wal vx cv wlim cA vx cv wcel wi vx wal
      vy cA con0 com vy cv cA wceq vx cv wlim vy cv vx cv wcel wi vx cv wlim cA
      vx cv wcel wi vx vy cv cA wceq vy cv vx cv wcel cA vx cv wcel vx cv wlim
      vy cv cA vx cv eleq1 imbi2d albidv vy vx df-om elrab2 $.
  $}

  ${
    $d x y $.
    $( Omega is a subset of ` On ` .  (Contributed by NM, 13-Jun-1994.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    omsson $p |- om C_ On $=
      com vx cv csuc vy cv wlim wn vy con0 crab wss vx con0 crab con0 vx vy
      dfom2 vx cv csuc vy cv wlim wn vy con0 crab wss vx con0 ssrab2 eqsstri $.
  $}

  ${
    $d x y A $.
    $( The class of natural numbers is a subclass of any (infinite) limit
       ordinal.  Exercise 1 of [TakeutiZaring] p. 44.  Remarkably, our proof
       does not require the Axiom of Infinity.  (Contributed by NM,
       30-Oct-2003.) $)
    limomss $p |- ( Lim A -> om C_ A ) $=
      cA word cA wlim com cA wss cA limord cA word cA con0 wcel cA con0 wceq wo
      cA wlim com cA wss wi cA ordeleqon cA con0 wcel cA wlim com cA wss wi cA
      con0 wceq cA con0 wcel cA wlim com cA wss cA con0 wcel cA wlim wa vx com
      cA cA con0 wcel cA wlim vx cv com wcel vx cv cA wcel wi cA con0 wcel vx
      cv com wcel cA wlim vx cv cA wcel vx cv com wcel vy cv wlim vx cv vy cv
      wcel wi vy wal cA con0 wcel cA wlim vx cv cA wcel wi vx cv com wcel vx cv
      con0 wcel vy cv wlim vx cv vy cv wcel wi vy wal vy vx cv elom simprbi vy
      cv wlim vx cv vy cv wcel wi cA wlim vx cv cA wcel wi vy cA con0 vy cv cA
      wceq vy cv wlim cA wlim vx cv vy cv wcel vx cv cA wcel vy cv cA limeq vy
      cv cA vx cv eleq2 imbi12d spcgv syl5 com23 imp ssrdv ex cA con0 wceq com
      cA wss cA wlim cA con0 wceq com cA wss com con0 wss omsson cA con0 com
      sseq2 mpbiri a1d jaoi sylbi mpcom $.
  $}

  $( A natural number is an ordinal number.  (Contributed by NM,
     27-Jun-1994.) $)
  nnon $p |- ( A e. om -> A e. On ) $=
    com con0 cA omsson sseli $.

  ${
    nnoni.1 $e |- A e. om $.
    $( A natural number is an ordinal number.  (Contributed by NM,
       27-Jun-1994.) $)
    nnoni $p |- A e. On $=
      cA com wcel cA con0 wcel nnoni.1 cA nnon ax-mp $.
  $}

  $( A natural number is ordinal.  (Contributed by NM, 17-Oct-1995.) $)
  nnord $p |- ( A e. om -> Ord A ) $=
    cA com wcel cA con0 wcel cA word cA nnon cA eloni syl $.

  ${
    $d x y z $.
    $( Omega is ordinal.  Theorem 7.32 of [TakeutiZaring] p. 43.  (Contributed
       by NM, 18-Oct-1995.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    ordom $p |- Ord om $=
      com wtr com con0 wss con0 word com word com wtr vy cv vx cv wcel vx cv
      com wcel wa vy cv com wcel wi vx wal vy vy vx com dftr2 vy cv vx cv wcel
      vx cv com wcel wa vy cv com wcel wi vx vy cv vx cv wcel vx cv com wcel vy
      cv com wcel vy cv vx cv wcel vx cv con0 wcel vz cv wlim vx cv vz cv wcel
      wi vz wal wa vy cv con0 wcel vz cv wlim vy cv vz cv wcel wi vz wal wa vx
      cv com wcel vy cv com wcel vy cv vx cv wcel vx cv con0 wcel vy cv con0
      wcel vz cv wlim vx cv vz cv wcel wi vz wal vz cv wlim vy cv vz cv wcel wi
      vz wal vx cv con0 wcel vy cv vx cv wcel vy cv con0 wcel vx cv vy cv
      onelon expcom vy cv vx cv wcel vz cv wlim vx cv vz cv wcel wi vz cv wlim
      vy cv vz cv wcel wi vz vy cv vx cv wcel vz cv wlim vx cv vz cv wcel vy cv
      vz cv wcel vz cv wlim vy cv vx cv wcel vx cv vz cv wcel vy cv vz cv wcel
      wi vz cv wlim vy cv vx cv wcel vx cv vz cv wcel vy cv vz cv wcel vz cv
      wlim vz cv word vz cv wtr vy cv vx cv wcel vx cv vz cv wcel wa vy cv vz
      cv wcel wi vz cv limord vz cv ordtr vz cv vy cv vx cv trel 3syl exp3a
      com12 a2d alimdv anim12d vz vx cv elom vz vy cv elom 3imtr4g imp ax-gen
      mpgbir omsson ordon com con0 trssord mp3an $.
  $}

  $( A member of a natural number is a natural number.  (Contributed by NM,
     21-Jun-1998.) $)
  elnn $p |- ( ( A e. B /\ B e. om ) -> A e. om ) $=
    com word com wtr cA cB wcel cB com wcel wa cA com wcel wi ordom com ordtr
    com cA cB trel mp2b $.

  $( The class of natural numbers ` om ` is either an ordinal number (if we
     accept the Axiom of Infinity) or the proper class of all ordinal numbers
     (if we deny the Axiom of Infinity).  Remark in [TakeutiZaring] p. 43.
     (Contributed by NM, 10-May-1998.) $)
  omon $p |- ( om e. On \/ om = On ) $=
    com word com con0 wcel com con0 wceq wo ordom com ordeleqon mpbi $.

  ${
    $( Omega is an ordinal number.  (Contributed by Mario Carneiro,
       30-Jan-2013.) $)
    omelon2 $p |- ( om e. _V -> om e. On ) $=
      com con0 wcel com cvv wcel com con0 wcel wn com con0 wceq com cvv wcel wn
      com con0 wcel com con0 wceq omon ori com con0 wceq com cvv wcel con0 cvv
      wcel onprc com con0 cvv eleq1 mtbiri syl con4i $.
  $}

  ${
    $d x y A $.
    $( A natural number is not a limit ordinal.  (Contributed by NM,
       18-Oct-1995.) $)
    nnlim $p |- ( A e. om -> -. Lim A ) $=
      cA com wcel cA wlim cA cA wcel cA com wcel cA word cA cA wcel wn cA nnord
      cA ordirr syl cA com wcel vx cv wlim cA vx cv wcel wi vx wal cA wlim cA
      cA wcel wi cA com wcel cA con0 wcel vx cv wlim cA vx cv wcel wi vx wal vx
      cA elom simprbi vx cv wlim cA vx cv wcel wi cA wlim cA cA wcel wi vx cA
      com vx cv cA wceq vx cv wlim cA wlim cA vx cv wcel cA cA wcel vx cv cA
      limeq vx cv cA cA eleq2 imbi12d spcgv mpd mtod $.

    $( The class of natural numbers is a subclass of the class of non-limit
       ordinal numbers.  Exercise 4 of [TakeutiZaring] p. 42.  (Contributed by
       NM, 2-Nov-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    omssnlim $p |- om C_ { x e. On | -. Lim x } $=
      com vx cv wlim wn vx con0 crab wss com con0 wss vx cv wlim wn vx com wral
      omsson vx cv wlim wn vx com vx cv nnlim rgen vx cv wlim wn vx con0 com
      ssrab mpbir2an $.
  $}

  $( Omega is a limit ordinal.  Theorem 2.8 of [BellMachover] p. 473.  Our
     proof, however, does not require the Axiom of Infinity.  (Contributed by
     NM, 26-Mar-1995.)  (Proof shortened by Mario Carneiro, 2-Sep-2015.) $)
  limom $p |- Lim om $=
    com word com wlim ordom com word com con0 wcel com con0 wceq wo com wlim
    com ordeleqon com con0 wcel com wlim com con0 wceq com con0 wcel vx cv wlim
    com vx cv wcel wi vx wal com wlim com con0 wcel com com wcel vx cv wlim com
    vx cv wcel wi vx wal com word com com wcel wn ordom com ordirr ax-mp com
    com wcel com con0 wcel vx cv wlim com vx cv wcel wi vx wal vx com elom baib
    mtbii com wlim wn vx cv wlim com vx cv wcel wi vx vx cv wlim com wlim wn
    com vx cv wcel vx cv wlim com vx cv wcel com wlim vx cv wlim com vx cv wcel
    wn com vx cv wceq com wlim vx cv wlim com vx cv wcel com vx cv wceq vx cv
    wlim com vx cv wss com vx cv wcel com vx cv wceq wo vx cv limomss vx cv
    wlim com word vx cv word com vx cv wss com vx cv wcel com vx cv wceq wo wb
    ordom vx cv limord com vx cv ordsseleq sylancr mpbid ord com vx cv wceq com
    wlim vx cv wlim com vx cv limeq biimprcd syld con1d com12 alrimiv nsyl2 com
    con0 wceq com wlim con0 wlim limon com con0 limeq mpbiri jaoi sylbi ax-mp
    $.

  $( A class belongs to omega iff its successor does.  (Contributed by NM,
     3-Dec-1995.) $)
  peano2b $p |- ( A e. om <-> suc A e. om ) $=
    com wlim cA com wcel cA csuc com wcel wb limom com cA limsuc ax-mp $.

  ${
    $d x y A $.
    $( A nonzero natural number is a successor.  (Contributed by NM,
       18-Feb-2004.) $)
    nnsuc $p |- ( ( A e. om /\ A =/= (/) ) -> E. x e. om A = suc x ) $=
      cA com wcel cA c0 wne wa cA vx cv csuc wceq vx con0 wrex cA vx cv csuc
      wceq vx com wrex cA com wcel cA c0 wne wa cA vx cv csuc wceq vx con0 wrex
      cA wlim cA com wcel cA wlim wn cA c0 wne cA nnlim adantr cA com wcel cA
      word cA c0 wne cA vx cv csuc wceq vx con0 wrex wn cA wlim wi cA nnord cA
      word cA c0 wne wa cA vx cv csuc wceq vx con0 wrex wn cA cA cuni wceq cA
      wlim cA word cA cA cuni wceq cA vx cv csuc wceq vx con0 wrex wn wb cA c0
      wne vx cA orduninsuc adantr cA word cA c0 wne cA cA cuni wceq cA wlim cA
      wlim cA word cA c0 wne cA cA cuni wceq w3a cA df-lim biimpri 3expia
      sylbird sylan mt3d cA com wcel cA vx cv csuc wceq vx con0 wrex cA vx cv
      csuc wceq vx com wrex wi cA c0 wne cA com wcel cA vx cv csuc wceq cA vx
      cv csuc wceq vx con0 com cA com wcel cA vx cv csuc wceq vx cv com wcel cA
      vx cv csuc wceq wa vx cv con0 wcel cA com wcel cA vx cv csuc wceq vx cv
      com wcel cA com wcel cA vx cv csuc wceq vx cv csuc com wcel vx cv com
      wcel cA vx cv csuc wceq cA com wcel vx cv csuc com wcel cA vx cv csuc com
      eleq1 biimpcd vx cv peano2b syl6ibr ancrd adantld reximdv2 adantr mpd $.
  $}

  ${
    $d x A $.
    $( An ordinal subclass of non-limit ordinals is a class of natural
       numbers.  Exercise 7 of [TakeutiZaring] p. 42.  (Contributed by NM,
       2-Nov-2004.) $)
    ssnlim $p |- ( ( Ord A /\ A C_ { x e. On | -. Lim x } ) -> A C_ om ) $=
      cA word cA vx cv wlim wn vx con0 crab wss wa cA com wss com cA wcel wn cA
      vx cv wlim wn vx con0 crab wss com cA wcel wn cA word cA vx cv wlim wn vx
      con0 crab wss com cA wcel com wlim limom cA vx cv wlim wn vx con0 crab
      wss com cA wcel com vx cv wlim wn vx con0 crab wcel com wlim wn cA vx cv
      wlim wn vx con0 crab com ssel com vx cv wlim wn vx con0 crab wcel com
      con0 wcel com wlim wn vx cv wlim wn com wlim wn vx com con0 vx cv com
      wceq vx cv wlim com wlim vx cv com limeq notbid elrab simprbi syl6 mt2i
      adantl cA word cA com wss com cA wcel wn wb cA vx cv wlim wn vx con0 crab
      wss cA word com word cA com wss com cA wcel wn wb ordom cA com ordtri1
      mpan2 adantr mpbird $.
  $}


