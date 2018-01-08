
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Introduce_the_Axiom_of_Union.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Ordinals (continued)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y $.
    $( The class of all ordinal numbers is ordinal.  Proposition 7.12 of
       [TakeutiZaring] p. 38, but without using the Axiom of Regularity.
       (Contributed by NM, 17-May-1994.) $)
    ordon $p |- Ord On $=
      con0 word con0 wtr con0 cep wwe tron con0 cep wwe con0 cep wfr vx cv vy
      cv cep wbr vx cv vy cv wceq vy cv vx cv cep wbr w3o vy con0 wral vx con0
      wral onfr vx cv vy cv cep wbr vx cv vy cv wceq vy cv vx cv cep wbr w3o vx
      vy con0 vx cv con0 wcel vx cv word vy cv word vx cv vy cv cep wbr vx cv
      vy cv wceq vy cv vx cv cep wbr w3o vy cv con0 wcel vx cv eloni vy cv
      eloni vx cv word vy cv word wa vx cv vy cv wcel vx cv vy cv wceq vy cv vx
      cv wcel w3o vx cv vy cv cep wbr vx cv vy cv wceq vy cv vx cv cep wbr w3o
      vx cv vy cv ordtri3or vx cv vy cv cep wbr vx cv vy cv wcel vx cv vy cv
      wceq vx cv vy cv wceq vy cv vx cv cep wbr vy cv vx cv wcel vx vy epel vx
      cv vy cv wceq biid vy vx epel 3orbi123i sylibr syl2an rgen2a vx vy con0
      cep dfwe2 mpbir2an con0 df-ord mpbir2an $.
  $}

  $( The epsilon relation well-orders the class of ordinal numbers.
     Proposition 4.8(g) of [Mendelson] p. 244.  (Contributed by NM,
     1-Nov-2003.) $)
  epweon $p |- _E We On $=
    con0 word con0 cep wwe ordon con0 ordwe ax-mp $.

  $( No set contains all ordinal numbers.  Proposition 7.13 of [TakeutiZaring]
     p. 38, but without using the Axiom of Regularity.  This is also known as
     the Burali-Forti paradox (remark in [Enderton] p. 194).  In 1897, Cesare
     Burali-Forti noticed that since the "set" of all ordinal numbers is an
     ordinal class ( ~ ordon ), it must be both an element of the set of all
     ordinal numbers yet greater than every such element.  ZF set theory
     resolves this paradox by not allowing the class of all ordinal numbers to
     be a set (so instead it is a proper class).  Here we prove the denial of
     its existence.  (Contributed by NM, 18-May-1994.) $)
  onprc $p |- -. On e. _V $=
    con0 cvv wcel con0 con0 wcel con0 word con0 con0 wcel wn ordon con0 ordirr
    ax-mp con0 cvv wcel con0 con0 wcel con0 word ordon con0 cvv elong mpbiri
    mto $.

  ${
    $d x y A $.
    $( The union of a class of ordinal numbers is ordinal.  Proposition 7.19 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 30-May-1994.)  (Proof
       shortened by Andrew Salmon, 12-Aug-2011.) $)
    ssorduni $p |- ( A C_ On -> Ord U. A ) $=
      cA con0 wss cA cuni wtr cA cuni con0 wss cA cuni word cA con0 wss vx cv
      cA cuni wss vx cA cuni wral cA cuni wtr cA con0 wss vx cv cA cuni wss vx
      cA cuni vx cv cA cuni wcel vx cv vy cv wcel vy cA wrex cA con0 wss vx cv
      cA cuni wss vy vx cv cA eluni2 cA con0 wss vx cv vy cv wcel vx cv cA cuni
      wss vy cA cA con0 wss vy cv cA wcel vx cv vy cv wcel vx cv vy cv wss vy
      cv cA wcel wa vx cv cA cuni wss cA con0 wss vy cv cA wcel vx cv vy cv
      wcel vx cv vy cv wss wi wi vy cv cA wcel vx cv vy cv wcel vx cv vy cv wss
      vy cv cA wcel wa wi wi cA con0 wss vy cv cA wcel vy cv con0 wcel vx cv vy
      cv wcel vx cv vy cv wss wi cA con0 vy cv ssel vy cv vx cv onelss syl6 vy
      cv cA wcel vx cv vy cv wcel vx cv vy cv wss anc2r syl vx cv vy cv cA
      ssuni syl8 rexlimdv syl5bi ralrimiv vx cA cuni dftr3 sylibr cA con0 wss
      vx cA cuni con0 vx cv cA cuni wcel vx cv vy cv wcel vy cA wrex cA con0
      wss vx cv con0 wcel vy vx cv cA eluni2 cA con0 wss vx cv vy cv wcel vx cv
      con0 wcel vy cA cA con0 wss vy cv cA wcel vy cv con0 wcel vx cv vy cv
      wcel vx cv con0 wcel wi cA con0 vy cv ssel vy cv con0 wcel vx cv vy cv
      wcel vx cv con0 wcel vy cv vx cv onelon ex syl6 rexlimdv syl5bi ssrdv cA
      cuni wtr cA cuni con0 wss con0 word cA cuni word ordon cA cuni wtr cA
      cuni con0 wss con0 word cA cuni word cA cuni con0 trssord 3exp mpii sylc
      $.
  $}

  $( The union of a set of ordinal numbers is an ordinal number.  Theorem 9 of
     [Suppes] p. 132.  (Contributed by NM, 1-Nov-2003.) $)
  ssonuni $p |- ( A e. V -> ( A C_ On -> U. A e. On ) ) $=
    cA con0 wss cA cuni con0 wcel cA cV wcel cA cuni word cA ssorduni cA cV
    wcel cA cuni cvv wcel cA cuni con0 wcel cA cuni word wb cA cV uniexg cA
    cuni cvv elong syl syl5ibr $.

  ${
    ssonuni.1 $e |- A e. _V $.
    $( The union of a set of ordinal numbers is an ordinal number.  Corollary
       7N(d) of [Enderton] p. 193.  (Contributed by NM, 20-Sep-2003.) $)
    ssonunii $p |- ( A C_ On -> U. A e. On ) $=
      cA cvv wcel cA con0 wss cA cuni con0 wcel wi ssonuni.1 cA cvv ssonuni
      ax-mp $.
  $}

  $( A way to express the ordinal property of a class in terms of the class of
     ordinal numbers.  Corollary 7.14 of [TakeutiZaring] p. 38 and its
     converse.  (Contributed by NM, 1-Jun-2003.) $)
  ordeleqon $p |- ( Ord A <-> ( A e. On \/ A = On ) ) $=
    cA word cA con0 wcel cA con0 wceq wo cA word cA con0 wcel cA con0 wceq wo
    con0 cA wcel con0 cA wcel con0 cvv wcel onprc con0 cA elex mto cA word cA
    con0 wcel cA con0 wceq wo con0 cA wcel cA word cA con0 wcel cA con0 wceq
    con0 cA wcel w3o cA con0 wcel cA con0 wceq wo con0 cA wcel wo cA word con0
    word cA con0 wcel cA con0 wceq con0 cA wcel w3o ordon cA con0 ordtri3or
    mpan2 cA con0 wcel cA con0 wceq con0 cA wcel df-3or sylib ord mt3i cA con0
    wcel cA word cA con0 wceq cA eloni cA con0 wceq cA word con0 word ordon cA
    con0 ordeq mpbiri jaoi impbii $.

  $( Any ordinal class is a subclass of the class of ordinal numbers.
     Corollary 7.15 of [TakeutiZaring] p. 38.  (Contributed by NM,
     18-May-1994.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)
  ordsson $p |- ( Ord A -> A C_ On ) $=
    cA word con0 word cA con0 wss ordon cA word con0 word wa cA con0 wss cA
    con0 wcel cA con0 wceq wo cA word cA con0 wcel cA con0 wceq wo con0 word cA
    word cA con0 wcel cA con0 wceq wo cA ordeleqon biimpi adantr cA con0
    ordsseleq mpbird mpan2 $.

  $( An ordinal number is a subset of the class of ordinal numbers.
     (Contributed by NM, 5-Jun-1994.) $)
  onss $p |- ( A e. On -> A C_ On ) $=
    cA con0 wcel cA word cA con0 wss cA eloni cA ordsson syl $.

  $( Two ways of saying a class of ordinals is unbounded.  (Contributed by
     Mario Carneiro, 8-Jun-2013.) $)
  ssonprc $p |- ( A C_ On -> ( A e/ _V <-> U. A = On ) ) $=
    cA cvv wnel cA cvv wcel wn cA con0 wss cA cuni con0 wceq cA cvv df-nel cA
    con0 wss cA cvv wcel wn cA cuni con0 wceq cA con0 wss cA cuni con0 wceq cA
    cvv wcel cA con0 wss cA cuni con0 wceq wn cA cuni con0 wcel cA cvv wcel cA
    con0 wss cA cuni con0 wceq cA cuni con0 wcel cA con0 wss cA cuni con0 wcel
    cA cuni con0 wceq cA con0 wss cA cuni word cA cuni con0 wcel cA cuni con0
    wceq wo cA ssorduni cA cuni ordeleqon sylib orcomd ord cA cuni con0 wcel cA
    cuni cvv wcel cA cvv wcel cA cuni con0 elex cA uniexb sylibr syl6 con1d cA
    cuni con0 wceq cA cvv wcel con0 cvv wcel onprc cA cvv wcel cA cuni cvv wcel
    cA cuni con0 wceq con0 cvv wcel cA cvv uniexg cA cuni con0 cvv eleq1 syl5ib
    mtoi impbid1 syl5bb $.

  $( The union of an ordinal number is an ordinal number.  (Contributed by NM,
     29-Sep-2006.) $)
  onuni $p |- ( A e. On -> U. A e. On ) $=
    cA con0 wcel cA con0 wss cA cuni con0 wcel cA onss cA con0 ssonuni mpd $.

  $( The union of an ordinal class is ordinal.  (Contributed by NM,
     12-Sep-2003.) $)
  orduni $p |- ( Ord A -> Ord U. A ) $=
    cA word cA con0 wss cA cuni word cA ordsson cA ssorduni syl $.

  ${
    $d x y z A $.
    $( The intersection (infimum) of a non-empty class of ordinal numbers
       belongs to the class.  Compare Exercise 4 of [TakeutiZaring] p. 45.
       (Contributed by NM, 31-Jan-1997.) $)
    onint $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. A ) $=
      cA con0 wss cA c0 wne cA cint cA wcel cA con0 wss cA c0 wne wa cA vx cv
      cin c0 wceq vx cA wrex cA con0 wss cA cint cA wcel con0 word cA con0 wss
      cA c0 wne cA vx cv cin c0 wceq vx cA wrex ordon vx con0 cA tz7.5 mp3an1
      cA con0 wss cA vx cv cin c0 wceq cA cint cA wcel vx cA cA con0 wss vx cv
      cA wcel cA vx cv cin c0 wceq cA cint cA wcel wi cA con0 wss vx cv cA wcel
      cA vx cv cin c0 wceq vx cv cA wcel cA cint cA wcel cA con0 wss vx cv cA
      wcel cA vx cv cin c0 wceq vx cv cA wcel cA cint cA wcel wi cA con0 wss vx
      cv cA wcel cA vx cv cin c0 wceq wa wa vx cv cA wcel cA cint cA wcel cA
      con0 wss vx cv cA wcel cA vx cv cin c0 wceq wa wa vx cv cA cint cA cA
      con0 wss vx cv cA wcel cA vx cv cin c0 wceq wa wa vx cv cA cint cA con0
      wss vx cv cA wcel cA vx cv cin c0 wceq wa wa vy vx cv cA cint cA con0 wss
      vx cv cA wcel cA vx cv cin c0 wceq vy cv vx cv wcel vy cv cA cint wcel wi
      vy cv vx cv wcel cA con0 wss vx cv cA wcel cA vx cv cin c0 wceq vy cv cA
      cint wcel vy cv vx cv wcel cA con0 wss vx cv cA wcel cA vx cv cin c0 wceq
      vy cv cA cint wcel wi cA con0 wss vx cv cA wcel wa vy cv vx cv wcel cA
      con0 wss vx cv con0 wcel wa cA vx cv cin c0 wceq vy cv cA cint wcel wi cA
      con0 wss vx cv cA wcel vx cv con0 wcel cA con0 vx cv ssel imdistani vy cv
      vx cv wcel cA con0 wss vx cv con0 wcel wa wa vz cv vx cv wcel wn vz cA
      wral vy cv vz cv wcel vz cA wral cA vx cv cin c0 wceq vy cv cA cint wcel
      vy cv vx cv wcel cA con0 wss vx cv con0 wcel wa wa vz cv vx cv wcel wn vy
      cv vz cv wcel vz cA vy cv vx cv wcel cA con0 wss vx cv con0 wcel wa vz cv
      cA wcel vz cv vx cv wcel wn vy cv vz cv wcel wi cA con0 wss vx cv con0
      wcel wa vz cv cA wcel vz cv vx cv wcel wn vy cv vx cv wcel vy cv vz cv
      wcel cA con0 wss vz cv cA wcel vz cv con0 wcel vx cv con0 wcel vz cv vx
      cv wcel wn vy cv vx cv wcel vy cv vz cv wcel wi wi cA con0 vz cv ssel vx
      cv con0 wcel vz cv con0 wcel vz cv vx cv wcel wn vy cv vx cv wcel vy cv
      vz cv wcel wi wi vx cv con0 wcel vz cv con0 wcel wa vz cv vx cv wcel wn
      vx cv vz cv wss vy cv vx cv wcel vy cv vz cv wcel wi vx cv vz cv ontri1
      vx cv vz cv vy cv ssel syl6bir ex sylan9 com4r imp31 ralimdva vz cA vx cv
      disj vz vy cv cA vy vex elint2 3imtr4g sylan2 exp32 com4l imp32 ssrdv vx
      cv cA wcel cA cint vx cv wss cA con0 wss cA vx cv cin c0 wceq vx cv cA
      intss1 ad2antrl eqssd eleq1d biimpd exp32 com34 pm2.43d rexlimdv syl5
      anabsi5 $.
  $}

  $( The intersection of a class of ordinal numbers is zero iff the class
     contains zero.  (Contributed by NM, 24-Apr-2004.) $)
  onint0 $p |- ( A C_ On -> ( |^| A = (/) <-> (/) e. A ) ) $=
    cA con0 wss cA cint c0 wceq c0 cA wcel cA con0 wss cA cint c0 wceq c0 cA
    wcel cA con0 wss cA cint c0 wceq wa cA cint cA wcel c0 cA wcel cA cint c0
    wceq cA con0 wss cA c0 wne cA cint cA wcel cA cint c0 wceq cA cint cvv wcel
    cA c0 wne cA cint c0 wceq cA cint cvv wcel c0 cvv wcel 0ex cA cint c0 cvv
    eleq1 mpbiri cA intex sylibr cA onint sylan2 cA cint c0 wceq cA cint cA
    wcel c0 cA wcel wb cA con0 wss cA cint c0 cA eleq1 adantl mpbid ex cA
    int0el impbid1 $.

  ${
    $d x y A $.
    $( A non-empty class of ordinal numbers has the smallest member.  Exercise
       9 of [TakeutiZaring] p. 40.  (Contributed by NM, 3-Oct-2003.) $)
    onssmin $p |- ( ( A C_ On /\ A =/= (/) ) -> E. x e. A A. y e. A x C_ y ) $=
      cA con0 wss cA c0 wne wa cA cint cA wcel cA cint vy cv wss vy cA wral vx
      cv vy cv wss vy cA wral vx cA wrex cA onint cA cint vy cv wss vy cA vy cv
      cA intss1 rgen vx cv vy cv wss vy cA wral cA cint vy cv wss vy cA wral vx
      cA cint cA vx cv cA cint wceq vx cv vy cv wss cA cint vy cv wss vy cA vx
      cv cA cint vy cv sseq1 ralbidv rspcev sylancl $.
  $}

  ${
    $d x y $.
    $( If a property is true for some ordinal number, it is true for a minimal
       ordinal number.  This version uses explicit substitution.  Theorem
       Schema 62 of [Suppes] p. 228.  (Contributed by NM, 29-Sep-2003.) $)
    onminesb $p |- ( E. x e. On ph -> [. |^| { x e. On | ph } / x ]. ph ) $=
      wph vx con0 wrex wph vx con0 crab cint wph vx con0 crab wcel wph vx wph
      vx con0 crab cint wsbc wph vx con0 wrex wph vx con0 crab c0 wne wph vx
      con0 crab cint wph vx con0 crab wcel wph vx con0 rabn0 wph vx con0 crab
      con0 wss wph vx con0 crab c0 wne wph vx con0 crab cint wph vx con0 crab
      wcel wph vx con0 ssrab2 wph vx con0 crab onint mpan sylbir wph vx con0
      crab cint wph vx con0 crab wcel wph vx con0 crab cint con0 wcel wph vx
      wph vx con0 crab cint wsbc wph vx wph vx con0 crab cint con0 vx con0 nfcv
      elrabsf simprbi syl $.

    $d y ph $.
    onminsb.1 $e |- F/ x ps $.
    onminsb.2 $e |- ( x = |^| { x e. On | ph } -> ( ph <-> ps ) ) $.
    $( If a property is true for some ordinal number, it is true for a minimal
       ordinal number.  This version uses implicit substitution.  Theorem
       Schema 62 of [Suppes] p. 228.  (Contributed by NM, 3-Oct-2003.) $)
    onminsb $p |- ( E. x e. On ph -> ps ) $=
      wph vx con0 wrex wph vx con0 crab cint wph vx con0 crab wcel wps wph vx
      con0 wrex wph vx con0 crab c0 wne wph vx con0 crab cint wph vx con0 crab
      wcel wph vx con0 rabn0 wph vx con0 crab con0 wss wph vx con0 crab c0 wne
      wph vx con0 crab cint wph vx con0 crab wcel wph vx con0 ssrab2 wph vx
      con0 crab onint mpan sylbir wph vx con0 crab cint wph vx con0 crab wcel
      wph vx con0 crab cint con0 wcel wps wph wps vx wph vx con0 crab cint con0
      vx wph vx con0 crab wph vx con0 nfrab1 nfint vx con0 nfcv onminsb.1
      onminsb.2 elrabf simprbi syl $.
  $}

  $( The intersection of a non-empty collection of ordinal numbers is an
     ordinal number.  Compare Exercise 6 of [TakeutiZaring] p. 44.
     (Contributed by NM, 29-Jan-1997.) $)
  oninton $p |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. On ) $=
    cA con0 wss cA c0 wne cA cint con0 wcel cA con0 wss cA c0 wne cA cint cA
    wcel cA cint con0 wcel cA con0 wss cA c0 wne cA cint cA wcel cA onint ex cA
    con0 cA cint ssel syld imp $.

  $( The intersection of a class of ordinal numbers exists iff it is an ordinal
     number.  (Contributed by NM, 6-Nov-2003.) $)
  onintrab $p |- ( |^| { x e. On | ph } e. _V <->
                 |^| { x e. On | ph } e. On ) $=
    wph vx con0 crab cint cvv wcel wph vx con0 crab cint con0 wcel wph vx con0
    crab cint cvv wcel wph vx con0 crab c0 wne wph vx con0 crab cint con0 wcel
    wph vx con0 crab intex wph vx con0 crab con0 wss wph vx con0 crab c0 wne
    wph vx con0 crab cint con0 wcel wph vx con0 ssrab2 wph vx con0 crab oninton
    mpan sylbir wph vx con0 crab cint con0 elex impbii $.

  $( An existence condition equivalent to an intersection's being an ordinal
     number.  (Contributed by NM, 6-Nov-2003.) $)
  onintrab2 $p |- ( E. x e. On ph <-> |^| { x e. On | ph } e. On ) $=
    wph vx con0 wrex wph vx con0 crab cint cvv wcel wph vx con0 crab cint con0
    wcel wph vx con0 intexrab wph vx onintrab bitri $.

  $( No member of a set of ordinal numbers belongs to its minimum.
     (Contributed by NM, 2-Feb-1997.) $)
  onnmin $p |- ( ( A C_ On /\ B e. A ) -> -. B e. |^| A ) $=
    cA con0 wss cB cA wcel wa cA cint cB wss cB cA cint wcel wn cB cA wcel cA
    cint cB wss cA con0 wss cB cA intss1 adantl cA con0 wss cB cA wcel wa cA
    cint con0 wcel cB con0 wcel cA cint cB wss cB cA cint wcel wn wb cB cA wcel
    cA con0 wss cA c0 wne cA cint con0 wcel cA cB ne0i cA oninton sylan2 cA
    con0 cB ssel2 cA cint cB ontri1 syl2anc mpbid $.

  ${
    $d x A $.  $d x ps $.
    onnminsb.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( An ordinal number smaller than the minimum of a set of ordinal numbers
       does not have the property determining that set. ` ps ` is the wff
       resulting from the substitution of ` A ` for ` x ` in wff ` ph ` .
       (Contributed by NM, 9-Nov-2003.) $)
    onnminsb $p |- ( A e. On -> ( A e. |^| { x e. On | ph } -> -. ps ) ) $=
      cA con0 wcel wps cA wph vx con0 crab cint wcel cA con0 wcel wps cA wph vx
      con0 crab cint wcel wn cA con0 wcel wps wa cA wph vx con0 crab wcel cA
      wph vx con0 crab cint wcel wn wph wps vx cA con0 onnminsb.1 elrab wph vx
      con0 crab con0 wss cA wph vx con0 crab wcel cA wph vx con0 crab cint wcel
      wn wph vx con0 ssrab2 wph vx con0 crab cA onnmin mpan sylbir ex con2d $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A way to show that an ordinal number equals the minimum of a non-empty
       collection of ordinal numbers: it must be in the collection, and it must
       not be larger than any member of the collection.  (Contributed by NM,
       14-Nov-2003.) $)
    oneqmin $p |- ( ( B C_ On /\ B =/= (/) ) -> ( A = |^| B <->
                  ( A e. B /\ A. x e. A -. x e. B ) ) ) $=
      cB con0 wss cB c0 wne wa cA cB cint wceq cA cB wcel vx cv cB wcel wn vx
      cA wral wa cB con0 wss cB c0 wne wa cA cB cint wceq cA cB wcel vx cv cB
      wcel wn vx cA wral cB con0 wss cB c0 wne wa cA cB wcel cA cB cint wceq cB
      cint cB wcel cB onint cA cB cint cB eleq1 syl5ibrcom cB con0 wss cA cB
      cint wceq vx cv cB wcel wn vx cA wral wi cB c0 wne cB con0 wss cA cB cint
      wceq vx cv cB wcel wn vx cA cA cB cint wceq vx cv cA wcel vx cv cB cint
      wcel cB con0 wss vx cv cB wcel wn cA cB cint wceq vx cv cA wcel vx cv cB
      cint wcel cA cB cint vx cv eleq2 biimpd cB con0 wss vx cv cB wcel vx cv
      cB cint wcel cB con0 wss vx cv cB wcel vx cv cB cint wcel wn cB vx cv
      onnmin ex con2d syl9r ralrimdv adantr jcad cB con0 wss cA cB wcel vx cv
      cB wcel wn vx cA wral wa cA cB cint wceq wi cB c0 wne vx cA cB oneqmini
      adantr impbid $.
  $}

  ${
    $d x y A $.
    bm2.5ii.1 $e |- A e. _V $.
    $( Problem 2.5(ii) of [BellMachover] p. 471.  (Contributed by NM,
       20-Sep-2003.) $)
    bm2.5ii $p |- ( A C_ On -> U. A = |^| { x e. On | A. y e. A y C_ x } ) $=
      cA con0 wss cA cuni con0 wcel cA cuni vy cv vx cv wss vy cA wral vx con0
      crab cint wceq cA bm2.5ii.1 ssonunii cA cuni con0 wcel vy cv vx cv wss vy
      cA wral vx con0 crab cint cA cuni vx cv wss vx con0 crab cint cA cuni cA
      cuni vx cv wss vx con0 crab vy cv vx cv wss vy cA wral vx con0 crab cA
      cuni vx cv wss vy cv vx cv wss vy cA wral vx con0 cA cuni vx cv wss vy cv
      vx cv wss vy cA wral wb vx cv con0 wcel vy cA vx cv unissb a1i rabbiia
      inteqi vx cA cuni con0 intmin syl5reqr syl $.
  $}

  ${
    $d x y z $.  $d y z ph $.  $d x z ps $.
    onminex.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( If a wff is true for an ordinal number, there is the smallest ordinal
       number for which it is true.  (Contributed by NM, 2-Feb-1997.)  (Proof
       shortened by Mario Carneiro, 20-Nov-2016.) $)
    onminex $p |- ( E. x e. On ph -> E. x e. On ( ph /\ A. y e. x -. ps ) ) $=
      wph vx con0 wrex wph vx vz wsb wps wn vy vz cv wral wa vz con0 wrex wph
      wps wn vy vx cv wral wa vx con0 wrex wph vx con0 wrex wph vx con0 crab
      cint con0 wcel wph vx wph vx con0 crab cint wsbc wps wn vy wph vx con0
      crab cint wral wph vx vz wsb wps wn vy vz cv wral wa vz con0 wrex wph vx
      con0 wrex wph vx con0 crab con0 wss wph vx con0 crab c0 wne wph vx con0
      crab cint con0 wcel wph vx con0 ssrab2 wph vx con0 crab c0 wne wph vx
      con0 wrex wph vx con0 rabn0 biimpri wph vx con0 crab oninton sylancr wph
      vx onminesb wph vx con0 wrex wps wn vy wph vx con0 crab cint vy cv wph vx
      con0 crab cint wcel wph vx con0 wrex vy cv con0 wcel wps wn wph vx con0
      wrex wph vx con0 crab cint con0 vy cv wph vx con0 wrex wph vx con0 crab
      cint con0 wcel wph vx con0 crab cint con0 wss wph vx con0 wrex wph vx
      con0 crab con0 wss wph vx con0 crab c0 wne wph vx con0 crab cint con0
      wcel wph vx con0 ssrab2 wph vx con0 crab c0 wne wph vx con0 wrex wph vx
      con0 rabn0 biimpri wph vx con0 crab oninton sylancr wph vx con0 crab cint
      onss syl sseld wph wps vx vy cv onminex.1 onnminsb syli ralrimiv wph vx
      vz wsb wps wn vy vz cv wral wa wph vx wph vx con0 crab cint wsbc wps wn
      vy wph vx con0 crab cint wral wa vz wph vx con0 crab cint con0 vz cv wph
      vx con0 crab cint wceq wph vx vz wsb wph vx wph vx con0 crab cint wsbc
      wps wn vy vz cv wral wps wn vy wph vx con0 crab cint wral wph vx vz wph
      vx con0 crab cint dfsbcq2 wps wn vy vz cv wph vx con0 crab cint raleq
      anbi12d rspcev syl12anc wph wps wn vy vx cv wral wa wph vx vz wsb wps wn
      vy vz cv wral wa vx vz con0 wph wps wn vy vx cv wral wa vz nfv wph vx vz
      wsb wps wn vy vz cv wral vx wph vx vz nfs1v wps wn vy vz cv wral vx nfv
      nfan vx vz weq wph wph vx vz wsb wps wn vy vx cv wral wps wn vy vz cv
      wral wph vx vz sbequ12 wps wn vy vx cv vz cv raleq anbi12d cbvrex sylibr
      $.
  $}

  $( The class of all ordinal numbers is its own successor.  (Contributed by
     NM, 12-Sep-2003.) $)
  sucon $p |- suc On = On $=
    con0 cvv wcel wn con0 csuc con0 wceq onprc con0 sucprc ax-mp $.

  $( A successor exists iff its class argument exists.  (Contributed by NM,
     22-Jun-1998.) $)
  sucexb $p |- ( A e. _V <-> suc A e. _V ) $=
    cA cvv wcel cA csn cvv wcel wa cA cA csn cun cvv wcel cA cvv wcel cA csuc
    cvv wcel cA cA csn unexb cA csn cvv wcel cA cvv wcel cA snex biantru cA
    csuc cA cA csn cun cvv cA df-suc eleq1i 3bitr4i $.

  $( The successor of a set is a set (generalization).  (Contributed by NM,
     5-Jun-1994.) $)
  sucexg $p |- ( A e. V -> suc A e. _V ) $=
    cA cV wcel cA cvv wcel cA csuc cvv wcel cA cV elex cA sucexb sylib $.

  ${
    sucex.1 $e |- A e. _V $.
    $( The successor of a set is a set.  (Contributed by NM, 30-Aug-1993.) $)
    sucex $p |- suc A e. _V $=
      cA cvv wcel cA csuc cvv wcel sucex.1 cA cvv sucexg ax-mp $.
  $}

  ${
    $d x A $.
    $( The minimum of a class of ordinal numbers is less than the minimum of
       that class with its minimum removed.  (Contributed by NM,
       20-Nov-2003.) $)
    onmindif2 $p |- ( ( A C_ On /\ A =/= (/) ) ->
                   |^| A e. |^| ( A \ { |^| A } ) ) $=
      cA con0 wss cA c0 wne wa cA cint cA cA cint csn cdif cint wcel cA cint vx
      cv wcel vx cA cA cint csn cdif wral cA con0 wss cA c0 wne wa cA cint vx
      cv wcel vx cA cA cint csn cdif vx cv cA cA cint csn cdif wcel vx cv cA
      wcel vx cv cA cint wne wa cA con0 wss cA c0 wne wa cA cint vx cv wcel vx
      cv cA cA cint eldifsn cA con0 wss cA c0 wne wa vx cv cA wcel vx cv cA
      cint wne cA cint vx cv wcel cA con0 wss cA c0 wne wa vx cv cA wcel wa cA
      cint vx cv wcel vx cv cA cint cA con0 wss cA c0 wne wa vx cv cA wcel wa
      cA cint vx cv wcel wn cA cint vx cv wceq vx cv cA cint wceq cA con0 wss
      cA c0 wne wa vx cv cA wcel wa cA cint vx cv wcel cA cint vx cv wceq cA
      con0 wss cA c0 wne wa vx cv cA wcel wa vx cv cA cint wcel wn cA cint vx
      cv wcel cA cint vx cv wceq wo cA con0 wss vx cv cA wcel vx cv cA cint
      wcel wn cA c0 wne cA vx cv onnmin adantlr cA con0 wss cA c0 wne wa vx cv
      cA wcel wa cA cint con0 wcel vx cv con0 wcel vx cv cA cint wcel wn cA
      cint vx cv wcel cA cint vx cv wceq wo wb cA con0 wss cA c0 wne wa cA cint
      con0 wcel vx cv cA wcel cA oninton adantr cA con0 wss vx cv cA wcel vx cv
      con0 wcel cA c0 wne cA con0 vx cv ssel2 adantlr cA cint con0 wcel vx cv
      con0 wcel wa cA cint vx cv wss vx cv cA cint wcel wn cA cint vx cv wcel
      cA cint vx cv wceq wo cA cint vx cv ontri1 cA cint vx cv onsseleq bitr3d
      syl2anc mpbid ord cA cint vx cv eqcom syl6ib necon1ad expimpd syl5bi
      ralrimiv cA c0 wne cA cint cA cA cint csn cdif cint wcel cA cint vx cv
      wcel vx cA cA cint csn cdif wral wb cA con0 wss cA c0 wne cA cint cvv
      wcel cA cint cA cA cint csn cdif cint wcel cA cint vx cv wcel vx cA cA
      cint csn cdif wral wb cA intex vx cA cint cA cA cint csn cdif cvv elintg
      sylbi adantl mpbird $.
  $}

  ${
    $d x A $.
    $( The successor of an ordinal number is an ordinal number.  Proposition
       7.24 of [TakeutiZaring] p. 41.  (Contributed by NM, 6-Jun-1994.) $)
    suceloni $p |- ( A e. On -> suc A e. On ) $=
      cA con0 wcel cA csuc con0 wcel cA csuc word cA con0 wcel cA csuc wtr cA
      csuc con0 wss cA csuc word cA con0 wcel vx cv cA csuc wss vx cA csuc wral
      cA csuc wtr cA con0 wcel vx cv cA csuc wss vx cA csuc cA con0 wcel vx cv
      cA csuc wcel vx cv cA wss cA cA csuc wss vx cv cA csuc wss cA con0 wcel
      vx cv cA wcel vx cv cA csn wcel wo vx cv cA wss vx cv cA wss wo vx cv cA
      csuc wcel vx cv cA wss cA con0 wcel vx cv cA wcel vx cv cA wss vx cv cA
      csn wcel vx cv cA wss cA vx cv onelss vx cv cA csn wcel vx cv cA wss wi
      cA con0 wcel vx cv cA csn wcel vx cv cA wceq vx cv cA wss vx cA elsn vx
      cv cA eqimss sylbi a1i orim12d vx cv cA csuc wcel vx cv cA cA csn cun
      wcel vx cv cA wcel vx cv cA csn wcel wo cA csuc cA cA csn cun vx cv cA
      df-suc eleq2i vx cv cA cA csn elun bitr2i vx cv cA wss oridm 3imtr3g cA
      sssucid vx cv cA cA csuc sstr2 syl6mpi ralrimiv vx cA csuc dftr3 sylibr
      cA con0 wcel cA csuc cA cA csn cun con0 cA df-suc cA con0 wcel cA cA csn
      con0 cA onss cA con0 snssi unssd syl5eqss cA csuc wtr cA csuc con0 wss
      con0 word cA csuc word ordon cA csuc wtr cA csuc con0 wss con0 word cA
      csuc word cA csuc con0 trssord 3exp mpii sylc cA con0 wcel cA csuc cvv
      wcel cA csuc con0 wcel cA csuc word wb cA con0 sucexg cA csuc cvv elong
      syl mpbird $.
  $}

  $( The successor of an ordinal class is ordinal.  (Contributed by NM,
     3-Apr-1995.) $)
  ordsuc $p |- ( Ord A <-> Ord suc A ) $=
    cA cvv wcel cA word cA csuc word wb cA cvv wcel cA word cA csuc word cA cvv
    wcel cA word cA con0 wcel cA csuc word cA cvv elong cA con0 wcel cA csuc
    con0 wcel cA csuc word cA suceloni cA csuc eloni syl syl6bir cA cvv wcel cA
    cA csuc wcel cA csuc word cA word cA cvv sucidg cA csuc word cA cA csuc
    wcel cA word cA csuc cA ordelord ex syl5com impbid cA cvv wcel wn cA cA
    csuc wceq cA word cA csuc word wb cA cvv wcel wn cA csuc cA cA sucprc
    eqcomd cA cA csuc ordeq syl pm2.61i $.

  ${
    $d x A $.
    $( The collection of ordinals in the power class of an ordinal is its
       successor.  (Contributed by NM, 30-Jan-2005.) $)
    ordpwsuc $p |- ( Ord A -> ( ~P A i^i On ) = suc A ) $=
      cA word vx cA cpw con0 cin cA csuc vx cv cA cpw con0 cin wcel vx cv con0
      wcel vx cv cA wss wa cA word vx cv cA csuc wcel vx cv cA cpw con0 cin
      wcel vx cv cA cpw wcel vx cv con0 wcel wa vx cv con0 wcel vx cv cA wss wa
      vx cv cA cpw con0 elin vx cv cA cpw wcel vx cv cA wss vx cv con0 wcel vx
      cv cA vx vex elpw anbi2ci bitri cA word vx cv con0 wcel vx cv cA wss wa
      vx cv con0 wcel vx cv cA csuc wcel wa vx cv cA csuc wcel cA word vx cv
      con0 wcel vx cv cA wss vx cv cA csuc wcel vx cv con0 wcel cA word vx cv
      cA wss vx cv cA csuc wcel wb vx cv cA ordsssuc expcom pm5.32d cA word vx
      cv con0 wcel vx cv cA csuc wcel wa vx cv cA csuc wcel vx cv con0 wcel vx
      cv cA csuc wcel simpr cA word vx cv cA csuc wcel vx cv con0 wcel cA word
      cA csuc word vx cv cA csuc wcel vx cv con0 wcel wi cA ordsuc cA csuc word
      vx cv cA csuc wcel vx cv con0 wcel cA csuc vx cv ordelon ex sylbi ancrd
      impbid2 bitrd syl5bb eqrdv $.

    $( The collection of ordinal numbers in the power set of an ordinal number
       is its successor.  (Contributed by NM, 19-Oct-2004.) $)
    onpwsuc $p |- ( A e. On -> ( ~P A i^i On ) = suc A ) $=
      cA con0 wcel cA word cA cpw con0 cin cA csuc wceq cA eloni cA ordpwsuc
      syl $.
  $}

  $( The successor of an ordinal number is an ordinal number.  (Contributed by
     NM, 9-Sep-2003.) $)
  sucelon $p |- ( A e. On <-> suc A e. On ) $=
    cA word cA cvv wcel wa cA csuc word cA csuc cvv wcel wa cA con0 wcel cA
    csuc con0 wcel cA word cA csuc word cA cvv wcel cA csuc cvv wcel cA ordsuc
    cA sucexb anbi12i cA elon2 cA csuc elon2 3bitr4i $.

  $( The successor of an element of an ordinal class is a subset of it.
     (Contributed by NM, 21-Jun-1998.) $)
  ordsucss $p |- ( Ord B -> ( A e. B -> suc A C_ B ) ) $=
    cB word cA cB wcel cA csuc cB wss cA cB wcel cB word cA cB wcel cA csuc cB
    wss wi cB word cA cB wcel cB word cA cB wcel cA csuc cB wss wi cB word cA
    cB wcel wa cA word cB word cA cB wcel cA csuc cB wss wi cB cA ordelord cA
    word cB word wa cA cB wcel cB cA csuc wcel wn cA csuc cB wss cA word cA cB
    wcel cB cA csuc wcel wn wi cB word cA word cA cB wcel cB cA csuc wcel wa wn
    cA cB wcel cB cA csuc wcel wn wi cA cB ordnbtwn cA cB wcel cB cA csuc wcel
    imnan sylibr adantr cA word cA csuc word cB word cA csuc cB wss cB cA csuc
    wcel wn wb cA ordsuc cA csuc cB ordtri1 sylanb sylibrd sylan exp31 pm2.43b
    pm2.43b $.

  $( An ordinal number is a proper subset of its successor.  (Contributed by
     Stefan O'Rear, 18-Nov-2014.) $)
  onpsssuc $p |- ( A e. On -> A C. suc A ) $=
    cA con0 wcel cA cA csuc wcel cA cA csuc wpss cA con0 sucidg cA con0 wcel cA
    word cA csuc word cA cA csuc wcel cA cA csuc wpss wb cA eloni cA con0 wcel
    cA word cA csuc word cA eloni cA ordsuc sylib cA cA csuc ordelpss syl2anc
    mpbid $.

  $( A set belongs to an ordinal iff its successor is a subset of the ordinal.
     Exercise 8 of [TakeutiZaring] p. 42 and its converse.  (Contributed by NM,
     29-Nov-2003.) $)
  ordelsuc $p |- ( ( A e. C /\ Ord B ) -> ( A e. B <-> suc A C_ B ) ) $=
    cA cC wcel cB word wa cA cB wcel cA csuc cB wss cB word cA cB wcel cA csuc
    cB wss wi cA cC wcel cA cB ordsucss adantl cA cC wcel cA csuc cB wss cA cB
    wcel wi cB word cA cB cC sucssel adantr impbid $.

  ${
    $d x A $.
    $( The successor of an ordinal number is the smallest larger ordinal
       number.  (Contributed by NM, 28-Nov-2003.) $)
    onsucmin $p |- ( A e. On -> suc A = |^| { x e. On | A e. x } ) $=
      cA con0 wcel cA vx cv wcel vx con0 crab cint cA csuc vx cv wss vx con0
      crab cint cA csuc cA con0 wcel cA vx cv wcel vx con0 crab cA csuc vx cv
      wss vx con0 crab cA con0 wcel cA vx cv wcel cA csuc vx cv wss vx con0 vx
      cv con0 wcel cA con0 wcel vx cv word cA vx cv wcel cA csuc vx cv wss wb
      vx cv eloni cA vx cv con0 ordelsuc sylan2 rabbidva inteqd cA con0 wcel cA
      csuc con0 wcel cA csuc vx cv wss vx con0 crab cint cA csuc wceq cA
      sucelon vx cA csuc con0 intmin sylbi eqtr2d $.
  $}

  $( Membership is inherited by successors.  Generalization of Exercise 9 of
     [TakeutiZaring] p. 42.  (Contributed by NM, 22-Jun-1998.)  (Proof
     shortened by Andrew Salmon, 12-Aug-2011.) $)
  ordsucelsuc $p |- ( Ord B -> ( A e. B <-> suc A e. suc B ) ) $=
    cB word cA cB wcel cA csuc cB csuc wcel cB word cA word wa cB word cA cB
    wcel wa cB word cA word cB word cA cB wcel simpl cB cA ordelord jca cB word
    cA csuc cB csuc wcel wa cB word cA word cB word cA csuc cB csuc wcel simpl
    cB word cB csuc word cA csuc cB csuc wcel cA word cB ordsuc cB csuc word cA
    csuc cB csuc wcel wa cA csuc word cA word cB csuc cA csuc ordelord cA
    ordsuc sylibr sylanb jca cA cvv wcel cB word cA word wa cA cB wcel cA csuc
    cB csuc wcel wb wi cA cvv wcel cB word cA word wa cA cB wcel cA csuc cB
    csuc wcel wb cA cvv wcel cB word cA word wa wa cA csuc cB wss cA csuc cB
    wcel cA csuc cB wceq wo cA cB wcel cA csuc cB csuc wcel cB word cA word wa
    cA csuc cB wss cA csuc cB wcel cA csuc cB wceq wo wb cA cvv wcel cA word cB
    word cA csuc cB wss cA csuc cB wcel cA csuc cB wceq wo wb cA word cA csuc
    word cB word cA csuc cB wss cA csuc cB wcel cA csuc cB wceq wo wb cA ordsuc
    cA csuc cB ordsseleq sylanb ancoms adantl cA cvv wcel cB word cA word wa wa
    cA cB wcel cA csuc cB wss cB word cA cB wcel cA csuc cB wss wi cA cvv wcel
    cA word cA cB ordsucss ad2antrl cA cvv wcel cA csuc cB wss cA cB wcel wi cB
    word cA word wa cA cB cvv sucssel adantr impbid cA cvv wcel cA csuc cB csuc
    wcel cA csuc cB wcel cA csuc cB wceq wo wb cB word cA word wa cA cvv wcel
    cA csuc cvv wcel cA csuc cB csuc wcel cA csuc cB wcel cA csuc cB wceq wo wb
    cA sucexb cA csuc cB cvv elsucg sylbi adantr 3bitr4d ex cA cvv wcel wn cA
    cB wcel cA csuc cB csuc wcel wb cB word cA word wa cA cB wcel cA cvv wcel
    cA csuc cB csuc wcel cA cB elex cA csuc cB csuc wcel cA csuc cvv wcel cA
    cvv wcel cA csuc cB csuc elex cA sucexb sylibr pm5.21ni a1d pm2.61i
    pm5.21nd $.

  $( The subclass relationship between two ordinal classes is inherited by
     their successors.  (Contributed by NM, 4-Oct-2003.) $)
  ordsucsssuc $p |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> suc A C_ suc B ) ) $=
    cA word cB word wa cB cA wcel wn cB csuc cA csuc wcel wn cA cB wss cA csuc
    cB csuc wss cA word cB cA wcel wn cB csuc cA csuc wcel wn wb cB word cA
    word cB cA wcel cB csuc cA csuc wcel cB cA ordsucelsuc notbid adantr cA cB
    ordtri1 cA word cA csuc word cB csuc word cA csuc cB csuc wss cB csuc cA
    csuc wcel wn wb cB word cA ordsuc cB ordsuc cA csuc cB csuc ordtri1 syl2anb
    3bitr4d $.

  $( Given an element ` A ` of the union of an ordinal ` B ` , ` suc A ` is an
     element of ` B ` itself.  (Contributed by Scott Fenton, 28-Mar-2012.)
     (Proof shortened by Mario Carneiro, 29-May-2015.) $)
  ordsucuniel $p |- ( Ord B -> ( A e. U. B <-> suc A e. B ) ) $=
    cB word cA word cA cB cuni wcel cA csuc cB wcel cB word cB cuni word cA cB
    cuni wcel cA word wi cB orduni cB cuni word cA cB cuni wcel cA word cB cuni
    cA ordelord ex syl cB word cA csuc cB wcel cA word cB word cA csuc cB wcel
    wa cA csuc word cA word cB cA csuc ordelord cA ordsuc sylibr ex cB word cA
    word cA cB cuni wcel cA csuc cB wcel wb cB word cA word wa cA cB cuni wcel
    cA csuc cB wcel cB word cA word wa cB cuni cA wss cB cA csuc wss cA cB cuni
    wcel wn cA csuc cB wcel wn cB word cB con0 wss cA word cB cuni cA wss cB cA
    csuc wss wb cB ordsson cB cA ordunisssuc sylan cB word cB cuni word cA word
    cB cuni cA wss cA cB cuni wcel wn wb cB orduni cB cuni cA ordtri1 sylan cA
    word cB word cA csuc word cB cA csuc wss cA csuc cB wcel wn wb cA ordsuc cB
    cA csuc ordtri1 sylan2b 3bitr3d con4bid ex pm5.21ndd $.

  ${
    $d x A $.  $d x B $.
    $( The successor of the maximum (i.e. union) of two ordinals is the maximum
       of their successors.  (Contributed by NM, 28-Nov-2003.) $)
    ordsucun $p |- ( ( Ord A /\ Ord B ) ->
               suc ( A u. B ) = ( suc A u. suc B ) ) $=
      cA word cB word wa vx cA cB cun csuc cA csuc cB csuc cun cA word cB word
      wa vx cv con0 wcel vx cv cA cB cun csuc wcel vx cv cA csuc cB csuc cun
      wcel cA word cB word wa cA cB cun word vx cv cA cB cun csuc wcel vx cv
      con0 wcel wi cA cB ordun cA cB cun word cA cB cun csuc word vx cv cA cB
      cun csuc wcel vx cv con0 wcel wi cA cB cun ordsuc cA cB cun csuc word vx
      cv cA cB cun csuc wcel vx cv con0 wcel cA cB cun csuc vx cv ordelon ex
      sylbi syl cA word cA csuc word cB csuc word vx cv cA csuc cB csuc cun
      wcel vx cv con0 wcel wi cB word cA ordsuc cB ordsuc cA csuc word cB csuc
      word wa cA csuc cB csuc cun word vx cv cA csuc cB csuc cun wcel vx cv
      con0 wcel wi cA csuc cB csuc ordun cA csuc cB csuc cun word vx cv cA csuc
      cB csuc cun wcel vx cv con0 wcel cA csuc cB csuc cun vx cv ordelon ex syl
      syl2anb vx cv con0 wcel cA word cB word wa vx cv cA cB cun csuc wcel vx
      cv cA csuc cB csuc cun wcel wb vx cv con0 wcel cA word cB word wa wa vx
      cv cA cB cun csuc wcel vx cv cA csuc wcel vx cv cB csuc wcel wo vx cv cA
      csuc cB csuc cun wcel vx cv con0 wcel cA word cB word wa wa vx cv cA cB
      cun wss vx cv cA wss vx cv cB wss wo vx cv cA cB cun csuc wcel vx cv cA
      csuc wcel vx cv cB csuc wcel wo cA word cB word wa vx cv cA cB cun wss vx
      cv cA wss vx cv cB wss wo wb vx cv con0 wcel vx cv cA cB ordssun adantl
      cA word cB word wa vx cv con0 wcel cA cB cun word vx cv cA cB cun wss vx
      cv cA cB cun csuc wcel wb cA cB ordun vx cv cA cB cun ordsssuc sylan2 vx
      cv con0 wcel cA word cB word wa wa vx cv cA wss vx cv cA csuc wcel vx cv
      cB wss vx cv cB csuc wcel vx cv con0 wcel cA word vx cv cA wss vx cv cA
      csuc wcel wb cB word vx cv cA ordsssuc adantrr vx cv con0 wcel cB word vx
      cv cB wss vx cv cB csuc wcel wb cA word vx cv cB ordsssuc adantrl orbi12d
      3bitr3d vx cv cA csuc cB csuc elun syl6bbr expcom pm5.21ndd eqrdv $.
  $}

  $( The maximum of two ordinals is equal to one of them.  (Contributed by
     Mario Carneiro, 25-Jun-2015.) $)
  ordunpr $p |- ( ( B e. On /\ C e. On ) -> ( B u. C ) e. { B , C } ) $=
    cB con0 wcel cC con0 wcel wa cB cC cun cB cC cpr wcel cB cC cun cB wceq cB
    cC cun cC wceq wo cB con0 wcel cC con0 wcel wa cC cB wss cB cC wss wo cB cC
    cun cB wceq cB cC cun cC wceq wo cB con0 wcel cC con0 wcel wa cB cC wss cC
    cB wss cB con0 wcel cB word cC word cB cC wss cC cB wss wo cC con0 wcel cB
    eloni cC eloni cB cC ordtri2or2 syl2an orcomd cC cB wss cB cC cun cB wceq
    cB cC wss cB cC cun cC wceq cC cB ssequn2 cB cC ssequn1 orbi12i sylib cB
    con0 wcel cC con0 wcel wa cB cC cun cvv wcel cB cC cun cB cC cpr wcel cB cC
    cun cB wceq cB cC cun cC wceq wo wb cB cC con0 con0 unexg cB cC cun cB cC
    cvv elprg syl mpbird $.

  $( The maximum of two ordinals belongs to a third if each of them do.
     (Contributed by NM, 18-Sep-2006.)  (Revised by Mario Carneiro,
     25-Jun-2015.) $)
  ordunel $p |- ( ( Ord A /\ B e. A /\ C e. A ) -> ( B u. C ) e. A ) $=
    cA word cB cA wcel cC cA wcel w3a cB cC cpr cA cB cC cun cB cA wcel cC cA
    wcel cB cC cpr cA wss cA word cB cC cA prssi 3adant1 cA word cB cA wcel cC
    cA wcel w3a cB con0 wcel cC con0 wcel cB cC cun cB cC cpr wcel cA word cB
    cA wcel cB con0 wcel cC cA wcel cA cB ordelon 3adant3 cA word cC cA wcel cC
    con0 wcel cB cA wcel cA cC ordelon 3adant2 cB cC ordunpr syl2anc sseldd $.

  $( A class of ordinal numbers is a subclass of the successor of its union.
     Similar to Proposition 7.26 of [TakeutiZaring] p. 41.  (Contributed by NM,
     19-Sep-2003.) $)
  onsucuni $p |- ( A C_ On -> A C_ suc U. A ) $=
    cA con0 wss cA cuni word cA cA cuni csuc wss cA ssorduni cA con0 wss cA
    cuni word wa cA cuni cA cuni wss cA cA cuni csuc wss cA cuni ssid cA cA
    cuni ordunisssuc mpbii mpdan $.

  $( An ordinal class is a subclass of the successor of its union.
     (Contributed by NM, 12-Sep-2003.) $)
  ordsucuni $p |- ( Ord A -> A C_ suc U. A ) $=
    cA word cA con0 wss cA cA cuni csuc wss cA ordsson cA onsucuni syl $.

  $( An ordinal class is either its union or the successor of its union.  If we
     adopt the view that zero is a limit ordinal, this means every ordinal
     class is either a limit or a successor.  (Contributed by NM,
     13-Sep-2003.) $)
  orduniorsuc $p |- ( Ord A -> ( A = U. A \/ A = suc U. A ) ) $=
    cA word cA cA cuni wceq cA cA cuni csuc wceq cA word cA cuni cA wne cA cA
    cuni csuc wss cA cuni csuc cA wss wa cA cA cuni wceq wn cA cA cuni csuc
    wceq cA word cA cuni cA wne cA cuni csuc cA wss cA cA cuni csuc wss cA word
    cA cuni cA wne cA cuni cA wcel cA cuni csuc cA wss cA word cA cuni cA wss
    cA cuni cA wne cA cuni cA wcel cA orduniss cA word cA cuni cA wcel cA cuni
    cA wss cA cuni cA wne wa cA cuni word cA word cA cuni cA wcel cA cuni cA
    wss cA cuni cA wne wa wb cA orduni cA cuni cA ordelssne mpancom biimprd
    mpand cA cuni cA ordsucss syld cA ordsucuni jctild cA cA cuni wceq wn cA cA
    cuni wne cA cuni cA wne cA cA cuni df-ne cA cA cuni necom bitr3i cA cA cuni
    csuc eqss 3imtr4g orrd $.

  ${
    $d x y A $.
    $( The class of all ordinal numbers is its own union.  Exercise 11 of
       [TakeutiZaring] p. 40.  (Contributed by NM, 12-Nov-2003.) $)
    unon $p |- U. On = On $=
      vx con0 cuni con0 vx cv con0 cuni wcel vx cv con0 wcel vx cv con0 cuni
      wcel vx cv vy cv wcel vy con0 wrex vx cv con0 wcel vy vx cv con0 eluni2
      vx cv vy cv wcel vx cv con0 wcel vy con0 vy cv vx cv onelon rexlimiva
      sylbi vx cv con0 wcel vx cv vx cv csuc wcel vx cv csuc con0 wcel vx cv
      con0 cuni wcel vx cv vx vex sucid vx cv suceloni vx cv vx cv csuc con0
      elunii sylancr impbii eqriv $.

    $( An ordinal class is equal to the union of its successor.  (Contributed
       by NM, 10-Dec-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    ordunisuc $p |- ( Ord A -> U. suc A = A ) $=
      cA word cA con0 wcel cA con0 wceq wo cA csuc cuni cA wceq cA ordeleqon cA
      con0 wcel cA csuc cuni cA wceq cA con0 wceq vx cv csuc cuni vx cv wceq cA
      csuc cuni cA wceq vx cA con0 vx cv cA wceq vx cv csuc cuni cA csuc cuni
      vx cv cA vx cv cA wceq vx cv csuc cA csuc vx cv cA suceq unieqd vx cv cA
      wceq id eqeq12d vx cv con0 wcel vx cv wtr vx cv csuc cuni vx cv wceq vx
      cv con0 wcel vx cv word vx cv wtr vx cv eloni vx cv ordtr syl vx cv vx
      vex unisuc sylib vtoclga cA con0 wceq con0 csuc cuni con0 cA csuc cuni cA
      con0 csuc cuni con0 cuni con0 con0 csuc con0 sucon unieqi unon eqtri cA
      con0 wceq cA csuc con0 csuc cA con0 suceq unieqd cA con0 wceq id 3eqtr4a
      jaoi sylbi $.

    $( The union of the ordinal subsets of an ordinal number is that number.
       (Contributed by NM, 30-Jan-2005.) $)
    orduniss2 $p |- ( Ord A -> U. { x e. On | x C_ A } = A ) $=
      cA word vx cv cA wss vx con0 crab cuni cA csuc cuni cA cA word vx cv cA
      wss vx con0 crab cA csuc cA word vx cv cA wss vx con0 crab cA cpw con0
      cin cA csuc vx cv cA wss vx con0 crab vx cv con0 wcel vx cv cA wss wa vx
      cab cA cpw con0 cin vx cv cA wss vx con0 df-rab vx cv con0 wcel vx cab vx
      cv cA wss vx cab cin vx cv cA wss vx cab vx cv con0 wcel vx cab cin vx cv
      con0 wcel vx cv cA wss wa vx cab cA cpw con0 cin vx cv con0 wcel vx cab
      vx cv cA wss vx cab incom vx cv con0 wcel vx cv cA wss vx inab vx cv cA
      wss vx cab cA cpw vx cv con0 wcel vx cab con0 cA cpw vx cv cA wss vx cab
      vx cA df-pw eqcomi vx con0 abid2 ineq12i 3eqtr3i eqtri cA ordpwsuc syl5eq
      unieqd cA ordunisuc eqtrd $.
  $}

  $( A successor ordinal is the successor of its union.  (Contributed by NM,
     10-Dec-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  onsucuni2 $p |- ( ( A e. On /\ A = suc B ) -> suc U. A = A ) $=
    cA con0 wcel cA cB csuc wceq wa cA cuni csuc cA csuc cuni cA cA con0 wcel
    cA cB csuc wceq cA cuni csuc cA csuc cuni wceq cA con0 wcel cA cB csuc wceq
    wa cA cuni csuc cA csuc cuni wceq cA cB csuc wceq cB csuc cuni csuc cB csuc
    csuc cuni wceq cA con0 wcel cA cB csuc wceq wa cB csuc con0 wcel cB csuc
    word cB csuc cuni csuc cB csuc csuc cuni wceq cA cB csuc wceq cA con0 wcel
    cB csuc con0 wcel cA cB csuc con0 eleq1 biimpac cB csuc eloni cB csuc word
    cB csuc cuni csuc cB csuc cB csuc csuc cuni cB csuc word cB csuc cuni cB
    wceq cB csuc cuni csuc cB csuc wceq cB csuc word cB word cB csuc cuni cB
    wceq cB ordsuc cB ordunisuc sylbir cB csuc cuni cB suceq syl cB csuc
    ordunisuc eqtr4d 3syl cA cB csuc wceq cA cuni csuc cB csuc cuni csuc cA
    csuc cuni cB csuc csuc cuni cA cB csuc wceq cA cuni cB csuc cuni wceq cA
    cuni csuc cB csuc cuni csuc wceq cA cB csuc unieq cA cuni cB csuc cuni
    suceq syl cA cB csuc wceq cA csuc cB csuc csuc cA cB csuc suceq unieqd
    eqeq12d syl5ibr anabsi7 cA con0 wcel cA csuc cuni cA wceq cA cB csuc wceq
    cA con0 wcel cA word cA csuc cuni cA wceq cA eloni cA ordunisuc syl adantr
    eqtrd $.

  $( The successor of an ordinal class contains the empty set.  (Contributed by
     NM, 4-Apr-1995.) $)
  0elsuc $p |- ( Ord A -> (/) e. suc A ) $=
    cA word cA csuc word c0 cA csuc wcel cA ordsuc cA csuc word c0 cA csuc wcel
    cA csuc c0 wne cA nsuceq0 cA csuc ord0eln0 mpbiri sylbi $.

  $( The class of ordinal numbers is a limit ordinal.  (Contributed by NM,
     24-Mar-1995.) $)
  limon $p |- Lim On $=
    con0 wlim con0 word con0 c0 wne con0 con0 cuni wceq ordon onn0 con0 cuni
    con0 unon eqcomi con0 df-lim mpbir3an $.

  ${
    onssi.1 $e |- A e. On $.
    $( An ordinal number is a subset of ` On ` .  (Contributed by NM,
       11-Aug-1994.) $)
    onssi $p |- A C_ On $=
      cA con0 wcel cA con0 wss onssi.1 cA onss ax-mp $.

    $( The successor of an ordinal number is an ordinal number.  Corollary
       7N(c) of [Enderton] p. 193.  (Contributed by NM, 12-Jun-1994.) $)
    onsuci $p |- suc A e. On $=
      cA con0 wcel cA csuc con0 wcel onssi.1 cA suceloni ax-mp $.

    $( An ordinal number is either its own union (if zero or a limit ordinal)
       or the successor of its union.  (Contributed by NM, 13-Jun-1994.) $)
    onuniorsuci $p |- ( A = U. A \/ A = suc U. A ) $=
      cA word cA cA cuni wceq cA cA cuni csuc wceq wo cA onssi.1 onordi cA
      orduniorsuc ax-mp $.

    ${
      $d x A $.
      $( A limit ordinal is not a successor ordinal.  (Contributed by NM,
         18-Feb-2004.) $)
      onuninsuci $p |- ( A = U. A <-> -. E. x e. On A = suc x ) $=
        cA vx cv csuc wceq vx con0 wrex cA cA cuni wceq cA vx cv csuc wceq vx
        con0 wrex cA cA cuni wceq wn cA vx cv csuc wceq cA cA cuni wceq wn vx
        con0 cA vx cv csuc wceq cA cA cuni wceq cA vx cv csuc wceq cA cA cuni
        wceq wa cA cA wcel cA onssi.1 onirri cA vx cv csuc wceq cA cA cuni wceq
        wa cA vx cv cA cA cA cuni wceq cA vx cv csuc wceq cA cA cuni vx cv cA
        cA cuni wceq id cA vx cv csuc wceq cA cuni vx cv cuni vx cv cun vx cv
        cA vx cv csuc wceq cA cuni vx cv vx cv csn cun cuni vx cv cuni vx cv
        cun cA vx cv csuc wceq cA vx cv vx cv csn cun wceq cA cuni vx cv vx cv
        csn cun cuni wceq vx cv csuc vx cv vx cv csn cun cA vx cv df-suc eqeq2i
        cA vx cv vx cv csn cun unieq sylbi vx cv vx cv csn cun cuni vx cv cuni
        vx cv csn cuni cun vx cv cuni vx cv cun vx cv vx cv csn uniun vx cv csn
        cuni vx cv vx cv cuni vx cv vx vex unisn uneq2i eqtri syl6eq cA vx cv
        csuc wceq vx cv cuni vx cv wss vx cv cuni vx cv cun vx cv wceq cA vx cv
        csuc wceq vx cv con0 wcel vx cv cuni vx cv wss cA vx cv csuc wceq con0
        wtr vx cv csuc con0 wcel vx cv con0 wcel tron cA vx cv csuc wceq cA
        con0 wcel vx cv csuc con0 wcel onssi.1 cA vx cv csuc con0 eleq1 mpbii
        con0 vx cv trsuc sylancr vx cv con0 wcel vx cv wtr vx cv cuni vx cv wss
        vx cv con0 wcel vx cv word vx cv wtr vx cv eloni vx cv ordtr syl vx cv
        df-tr sylib syl vx cv cuni vx cv ssequn1 sylib eqtrd sylan9eqr cA vx cv
        csuc wceq vx cv cA wcel cA cA cuni wceq cA vx cv csuc wceq vx cv cA
        wcel vx cv vx cv csuc wcel vx cv vx vex sucid cA vx cv csuc vx cv eleq2
        mpbiri adantr eqeltrd mto imnani rexlimivw cA cA cuni wceq wn cA cuni
        con0 wcel cA cA cuni csuc wceq cA vx cv csuc wceq vx con0 wrex cA con0
        wcel cA cuni con0 wcel onssi.1 cA onuni ax-mp cA cA cuni wceq cA cA
        cuni csuc wceq cA onssi.1 onuniorsuci ori cA vx cv csuc wceq cA cA cuni
        csuc wceq vx cA cuni con0 vx cv cA cuni wceq vx cv csuc cA cuni csuc cA
        vx cv cA cuni suceq eqeq2d rspcev sylancr impbii con2bii $.
    $}

    ${
      onsucssi.2 $e |- B e. On $.
      $( A set belongs to an ordinal number iff its successor is a subset of
         the ordinal number.  Exercise 8 of [TakeutiZaring] p. 42 and its
         converse.  (Contributed by NM, 16-Sep-1995.) $)
      onsucssi $p |- ( A e. B <-> suc A C_ B ) $=
        cA con0 wcel cB word cA cB wcel cA csuc cB wss wb onssi.1 cB onsucssi.2
        onordi cA cB con0 ordelsuc mp2an $.
    $}
  $}

  $( A successor is not a limit ordinal.  (Contributed by NM, 25-Mar-1995.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  nlimsucg $p |- ( A e. V -> -. Lim suc A ) $=
    cA csuc wlim cA cV wcel cA csuc wlim cA word cA csuc cA csuc cuni wceq cA
    cV wcel wn cA csuc wlim cA csuc word cA word cA csuc limord cA ordsuc
    sylibr cA csuc limuni cA word cA csuc cA csuc cuni wceq cA csuc cA wceq cA
    cV wcel wn cA word cA csuc cuni cA cA csuc cA ordunisuc eqeq2d cA word cA
    csuc cA wceq cA cA csuc wcel wn cA cV wcel wn cA word cA cA csuc wcel wn cA
    csuc cA wceq cA cA wcel wn cA ordirr cA csuc cA wceq cA cA csuc wcel cA cA
    wcel cA csuc cA cA eleq2 notbid syl5ibrcom cA cV wcel cA cA csuc wcel cA cV
    sucidg con3i syl6 sylbid sylc con2i $.

  ${
    $d x A $.
    $( An ordinal equal to its union is not a successor.  (Contributed by NM,
       18-Feb-2004.) $)
    orduninsuc $p |- ( Ord A -> ( A = U. A <-> -. E. x e. On A = suc x ) ) $=
      cA word cA con0 wcel cA con0 wceq wo cA cA cuni wceq cA vx cv csuc wceq
      vx con0 wrex wn wb cA ordeleqon cA con0 wcel cA cA cuni wceq cA vx cv
      csuc wceq vx con0 wrex wn wb cA con0 wceq cA con0 wcel cA cA cuni wceq cA
      vx cv csuc wceq vx con0 wrex wn wb cA con0 wcel cA c0 cif cA con0 wcel cA
      c0 cif cuni wceq cA con0 wcel cA c0 cif vx cv csuc wceq vx con0 wrex wn
      wb cA c0 cA cA con0 wcel cA c0 cif wceq cA cA cuni wceq cA con0 wcel cA
      c0 cif cA con0 wcel cA c0 cif cuni wceq cA vx cv csuc wceq vx con0 wrex
      wn cA con0 wcel cA c0 cif vx cv csuc wceq vx con0 wrex wn cA cA con0 wcel
      cA c0 cif wceq cA cA con0 wcel cA c0 cif cA cuni cA con0 wcel cA c0 cif
      cuni cA cA con0 wcel cA c0 cif wceq id cA cA con0 wcel cA c0 cif unieq
      eqeq12d cA cA con0 wcel cA c0 cif wceq cA vx cv csuc wceq vx con0 wrex cA
      con0 wcel cA c0 cif vx cv csuc wceq vx con0 wrex cA cA con0 wcel cA c0
      cif wceq cA vx cv csuc wceq cA con0 wcel cA c0 cif vx cv csuc wceq vx
      con0 cA cA con0 wcel cA c0 cif vx cv csuc eqeq1 rexbidv notbid bibi12d vx
      cA con0 wcel cA c0 cif cA c0 con0 0elon elimel onuninsuci dedth cA con0
      wceq cA cA cuni wceq cA vx cv csuc wceq vx con0 wrex wn wb con0 con0 cuni
      wceq con0 vx cv csuc wceq vx con0 wrex wn wb con0 con0 cuni wceq con0 vx
      cv csuc wceq vx con0 wrex wn con0 cuni con0 unon eqcomi con0 vx cv csuc
      wceq vx con0 con0 vx cv csuc wceq wn vx cv con0 wcel con0 vx cv csuc wceq
      con0 cvv wcel onprc con0 vx cv csuc wceq con0 cvv wcel vx cv csuc cvv
      wcel vx cv vx vex sucex con0 vx cv csuc cvv eleq1 mpbiri mto a1i nrex 2th
      cA con0 wceq cA cA cuni wceq con0 con0 cuni wceq cA vx cv csuc wceq vx
      con0 wrex wn con0 vx cv csuc wceq vx con0 wrex wn cA con0 wceq cA con0 cA
      cuni con0 cuni cA con0 wceq id cA con0 unieq eqeq12d cA con0 wceq cA vx
      cv csuc wceq vx con0 wrex con0 vx cv csuc wceq vx con0 wrex cA con0 wceq
      cA vx cv csuc wceq con0 vx cv csuc wceq vx con0 cA con0 vx cv csuc eqeq1
      rexbidv notbid bibi12d mpbiri jaoi sylbi $.

    $( An ordinal equal to its union contains the successor of each of its
       members.  (Contributed by NM, 1-Feb-2005.) $)
    ordunisuc2 $p |- ( Ord A -> ( A = U. A <-> A. x e. A suc x e. A ) ) $=
      cA word cA cA cuni wceq cA vx cv csuc wceq vx con0 wrex wn vx cv csuc cA
      wcel vx cA wral vx cA orduninsuc cA vx cv csuc wceq vx con0 wrex wn cA vx
      cv csuc wceq wn vx con0 wral cA word vx cv csuc cA wcel vx cA wral cA vx
      cv csuc wceq vx con0 ralnex cA word cA vx cv csuc wceq wn vx cv csuc cA
      wcel vx con0 cA cA word vx cv con0 wcel cA vx cv csuc wceq wn wi vx cv
      con0 wcel vx cv cA wcel vx cv csuc cA wcel wi wi vx cv cA wcel vx cv csuc
      cA wcel wi cA word vx cv con0 wcel cA vx cv csuc wceq wn vx cv cA wcel vx
      cv csuc cA wcel wi cA word vx cv con0 wcel wa cA vx cv csuc wcel vx cv
      csuc cA wcel wo cA vx cv csuc wceq wn vx cv cA wcel vx cv csuc cA wcel wi
      cA word vx cv con0 wcel wa cA vx cv csuc wceq cA vx cv csuc wcel vx cv
      csuc cA wcel wo vx cv con0 wcel cA word vx cv csuc word cA vx cv csuc
      wceq cA vx cv csuc wcel vx cv csuc cA wcel wo wn wb vx cv con0 wcel vx cv
      csuc con0 wcel vx cv csuc word vx cv suceloni vx cv csuc eloni syl cA vx
      cv csuc ordtri3 sylan2 con2bid cA word vx cv con0 wcel wa cA vx cv csuc
      wcel vx cv csuc cA wcel wo vx cv cA wcel vx cv csuc cA wcel wi cA word vx
      cv con0 wcel wa cA vx cv csuc wcel vx cv cA wcel vx cv csuc cA wcel wi vx
      cv csuc cA wcel vx cv con0 wcel cA vx cv csuc wcel vx cv cA wcel vx cv
      csuc cA wcel wi wi cA word vx cv con0 wcel cA vx cv csuc wcel vx cv cA
      wcel wn vx cv cA wcel vx cv csuc cA wcel wi vx cv con0 wcel vx cv cA wcel
      cA vx cv csuc wcel vx cv con0 wcel vx cv cA wcel cA vx cv csuc wcel wa wn
      vx cv cA wcel cA vx cv csuc wcel wn wi vx cv cA onnbtwn vx cv cA wcel cA
      vx cv csuc wcel imnan sylibr con2d vx cv cA wcel vx cv csuc cA wcel
      pm2.21 syl6 adantl vx cv csuc cA wcel vx cv cA wcel vx cv csuc cA wcel wi
      wi cA word vx cv con0 wcel wa vx cv csuc cA wcel vx cv cA wcel ax-1 a1i
      jaod cA word vx cv con0 wcel wa vx cv cA wcel vx cv csuc cA wcel wi cA vx
      cv csuc wcel vx cv csuc cA wcel wo cA word vx cv con0 wcel wa vx cv cA
      wcel vx cv csuc cA wcel wi wa cA vx cv wss vx cv cA wcel wo cA vx cv csuc
      wcel vx cv csuc cA wcel wo cA word vx cv con0 wcel wa cA vx cv wss vx cv
      cA wcel wo vx cv cA wcel vx cv csuc cA wcel wi cA word vx cv con0 wcel wa
      vx cv cA wcel cA vx cv wss vx cv con0 wcel cA word vx cv cA wcel cA vx cv
      wss wo vx cv con0 wcel vx cv word cA word vx cv cA wcel cA vx cv wss wo
      vx cv eloni vx cv cA ordtri2or sylan ancoms orcomd adantr cA word vx cv
      con0 wcel wa vx cv cA wcel vx cv csuc cA wcel wi wa cA vx cv wss cA vx cv
      csuc wcel vx cv cA wcel vx cv csuc cA wcel cA word vx cv con0 wcel wa cA
      vx cv wss cA vx cv csuc wcel wi vx cv cA wcel vx cv csuc cA wcel wi cA
      word vx cv con0 wcel wa cA vx cv wss cA vx cv csuc wcel cA vx cv
      ordsssuc2 biimpd adantr cA word vx cv con0 wcel wa vx cv cA wcel vx cv
      csuc cA wcel wi simpr orim12d mpd ex impbid bitr3d pm5.74da vx cv con0
      wcel vx cv cA wcel vx cv csuc cA wcel wi wi vx cv con0 wcel vx cv cA wcel
      wa vx cv csuc cA wcel wi cA word vx cv cA wcel vx cv csuc cA wcel wi vx
      cv con0 wcel vx cv cA wcel vx cv csuc cA wcel impexp cA word vx cv con0
      wcel vx cv cA wcel wa vx cv cA wcel vx cv csuc cA wcel cA word vx cv con0
      wcel vx cv cA wcel wa vx cv cA wcel vx cv con0 wcel vx cv cA wcel simpr
      cA word vx cv cA wcel vx cv con0 wcel cA word vx cv cA wcel vx cv con0
      wcel cA vx cv ordelon ex ancrd impbid2 imbi1d syl5bbr bitrd ralbidv2
      syl5bbr bitrd $.

    $( An ordinal is zero, a successor ordinal, or a limit ordinal.
       (Contributed by NM, 1-Oct-2003.) $)
    ordzsl $p |- ( Ord A <->
                  ( A = (/) \/ E. x e. On A = suc x \/ Lim A ) ) $=
      cA word cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA wlim w3o cA word cA
      vx cv csuc wceq vx con0 wrex cA c0 wceq cA wlim wo wo cA c0 wceq cA vx cv
      csuc wceq vx con0 wrex cA wlim w3o cA word cA vx cv csuc wceq vx con0
      wrex cA c0 wceq cA wlim wo cA word cA vx cv csuc wceq vx con0 wrex wn cA
      cA cuni wceq cA c0 wceq cA wlim wo cA word cA cA cuni wceq cA vx cv csuc
      wceq vx con0 wrex wn vx cA orduninsuc biimprd cA unizlim sylibd orrd cA
      c0 wceq cA vx cv csuc wceq vx con0 wrex cA wlim w3o cA c0 wceq cA vx cv
      csuc wceq vx con0 wrex cA wlim wo wo cA vx cv csuc wceq vx con0 wrex cA
      c0 wceq cA wlim wo wo cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA wlim
      3orass cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA wlim or12 bitri
      sylibr cA c0 wceq cA word cA vx cv csuc wceq vx con0 wrex cA wlim cA c0
      wceq cA word c0 word ord0 cA c0 ordeq mpbiri cA vx cv csuc wceq cA word
      vx con0 cA vx cv csuc wceq vx cv con0 wcel cA con0 wcel cA word vx cv
      con0 wcel cA con0 wcel cA vx cv csuc wceq vx cv csuc con0 wcel vx cv
      suceloni cA vx cv csuc con0 eleq1 syl5ibr cA eloni syl6com rexlimiv cA
      limord 3jaoi impbii $.

    $( An ordinal number is zero, a successor ordinal, or a limit ordinal
       number.  (Contributed by NM, 1-Oct-2003.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    onzsl $p |- ( A e. On <->
               ( A = (/) \/ E. x e. On A = suc x \/ ( A e. _V /\ Lim A ) ) ) $=
      cA con0 wcel cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA cvv wcel cA
      wlim wa w3o cA con0 wcel cA cvv wcel cA word cA c0 wceq cA vx cv csuc
      wceq vx con0 wrex cA cvv wcel cA wlim wa w3o cA con0 elex cA eloni cA
      word cA cvv wcel cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA wlim w3o
      cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA cvv wcel cA wlim wa w3o vx
      cA ordzsl cA cvv wcel cA c0 wceq cA c0 wceq cA vx cv csuc wceq vx con0
      wrex cA cvv wcel cA wlim wa w3o cA vx cv csuc wceq vx con0 wrex cA wlim
      cA c0 wceq cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA cvv wcel cA wlim
      wa w3o cA cvv wcel cA c0 wceq cA vx cv csuc wceq vx con0 wrex cA cvv wcel
      cA wlim wa 3mix1 adantl cA vx cv csuc wceq vx con0 wrex cA c0 wceq cA vx
      cv csuc wceq vx con0 wrex cA cvv wcel cA wlim wa w3o cA cvv wcel cA vx cv
      csuc wceq vx con0 wrex cA c0 wceq cA cvv wcel cA wlim wa 3mix2 adantl cA
      cvv wcel cA wlim wa cA c0 wceq cA vx cv csuc wceq vx con0 wrex 3mix3
      3jaodan sylan2b syl2anc cA c0 wceq cA con0 wcel cA vx cv csuc wceq vx
      con0 wrex cA cvv wcel cA wlim wa cA c0 wceq cA con0 wcel c0 con0 wcel
      0elon cA c0 con0 eleq1 mpbiri cA vx cv csuc wceq cA con0 wcel vx con0 vx
      cv con0 wcel cA con0 wcel cA vx cv csuc wceq vx cv csuc con0 wcel vx cv
      suceloni cA vx cv csuc con0 eleq1 syl5ibrcom rexlimiv cA cvv limelon
      3jaoi impbii $.

    $( An alternate definition of a limit ordinal, which is any ordinal that is
       neither zero nor a successor.  (Contributed by NM, 1-Nov-2004.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    dflim3 $p |- ( Lim A <->
                 ( Ord A /\ -. ( A = (/) \/ E. x e. On A = suc x ) ) ) $=
      cA wlim cA word cA c0 wne cA cA cuni wceq w3a cA word cA c0 wne cA cA
      cuni wceq wa wa cA word cA c0 wceq cA vx cv csuc wceq vx con0 wrex wo wn
      wa cA df-lim cA word cA c0 wne cA cA cuni wceq 3anass cA word cA c0 wne
      cA cA cuni wceq wa cA c0 wceq cA vx cv csuc wceq vx con0 wrex wo wn cA
      word cA c0 wne cA cA cuni wceq wa cA c0 wceq wn cA vx cv csuc wceq vx
      con0 wrex wn wa cA c0 wceq cA vx cv csuc wceq vx con0 wrex wo wn cA word
      cA c0 wne cA c0 wceq wn cA cA cuni wceq cA vx cv csuc wceq vx con0 wrex
      wn cA c0 wne cA c0 wceq wn wb cA word cA c0 df-ne a1i vx cA orduninsuc
      anbi12d cA c0 wceq cA vx cv csuc wceq vx con0 wrex ioran syl6bbr pm5.32i
      3bitri $.

    $( An alternate definition of a limit ordinal.  (Contributed by NM,
       1-Feb-2005.) $)
    dflim4 $p |- ( Lim A <->
                 ( Ord A /\ (/) e. A /\ A. x e. A suc x e. A ) ) $=
      cA wlim cA word c0 cA wcel cA cA cuni wceq w3a cA word c0 cA wcel vx cv
      csuc cA wcel vx cA wral w3a cA dflim2 cA word c0 cA wcel cA cA cuni wceq
      wa wa cA word c0 cA wcel vx cv csuc cA wcel vx cA wral wa wa cA word c0
      cA wcel cA cA cuni wceq w3a cA word c0 cA wcel vx cv csuc cA wcel vx cA
      wral w3a cA word c0 cA wcel cA cA cuni wceq wa c0 cA wcel vx cv csuc cA
      wcel vx cA wral wa cA word cA cA cuni wceq vx cv csuc cA wcel vx cA wral
      c0 cA wcel vx cA ordunisuc2 anbi2d pm5.32i cA word c0 cA wcel cA cA cuni
      wceq 3anass cA word c0 cA wcel vx cv csuc cA wcel vx cA wral 3anass
      3bitr4i bitri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The successor of a member of a limit ordinal is also a member.
       (Contributed by NM, 3-Sep-2003.) $)
    limsuc $p |- ( Lim A -> ( B e. A <-> suc B e. A ) ) $=
      cA wlim cB cA wcel cB csuc cA wcel cA wlim cA word c0 cA wcel vx cv csuc
      cA wcel vx cA wral w3a cB cA wcel cB csuc cA wcel wi vx cA dflim4 vx cv
      csuc cA wcel vx cA wral cA word cB cA wcel cB csuc cA wcel wi c0 cA wcel
      vx cv csuc cA wcel cB csuc cA wcel vx cB cA vx cv cB wceq vx cv csuc cB
      csuc cA vx cv cB suceq eleq1d rspccv 3ad2ant3 sylbi cA wlim cA word cA
      wtr cB csuc cA wcel cB cA wcel wi cA limord cA ordtr cA wtr cB csuc cA
      wcel cB cA wcel cA cB trsuc ex 3syl impbid $.

    $( A class includes a limit ordinal iff the successor of the class includes
       it.  (Contributed by NM, 30-Oct-2003.) $)
    limsssuc $p |- ( Lim A -> ( A C_ B <-> A C_ suc B ) ) $=
      cA wlim cA cB wss cA cB csuc wss cA cB wss cB cB csuc wss cA cB csuc wss
      cB sssucid cA cB cB csuc sstr2 mpi cA wlim cA cB csuc wss cA cB wss cA
      wlim cA cB csuc wss wa vx cA cB cA wlim cA cB csuc wss wa vx cv cA wcel
      vx cv cB wcel cA wlim cA cB csuc wss wa vx cv cA wcel wa vx cv cB wceq wn
      vx cv cB wcel cA wlim cA cB csuc wss vx cv cA wcel vx cv cB wceq wn cA
      wlim vx cv cA wcel cA cB csuc wss vx cv cB wceq wn cA wlim vx cv cA wcel
      cA cB csuc wss vx cv cB wceq wn wi cA wlim vx cv cA wcel wa vx cv cB wceq
      cA cB csuc wss vx cv cA wcel vx cv cB wceq cB cA wcel cA wlim cA cB csuc
      wss wn vx cv cB wceq vx cv cA wcel cB cA wcel vx cv cB cA eleq1 biimpcd
      cA wlim cB cA wcel cA cB csuc wss wn cA wlim cB cA wcel wa cB csuc cA
      wcel cA cB csuc wss wn cA wlim cB cA wcel cB csuc cA wcel cA cB limsuc
      biimpa cA wlim cB cA wcel wa cA cB csuc wss cB csuc cA wcel cA wlim cB cA
      wcel wa cA word cB csuc word cA cB csuc wss cB csuc cA wcel wn wb cA wlim
      cA word cB cA wcel cA limord adantr cA wlim cB cA wcel wa cB word cB csuc
      word cA wlim cA word cB cA wcel cB word cA limord cA cB ordelord sylan cB
      ordsuc sylib cA cB csuc ordtri1 syl2anc con2bid mpbid ex sylan9r con2d ex
      com23 imp31 cA cB csuc wss vx cv cA wcel vx cv cB wceq wn vx cv cB wcel
      wi cA wlim cA cB csuc wss vx cv cA wcel wa vx cv cB wcel vx cv cB wceq cA
      cB csuc wss vx cv cA wcel wa vx cv cB wcel vx cv cB wceq cA cB csuc wss
      vx cv cA wcel wa vx cv cB csuc wcel vx cv cB wcel vx cv cB wceq wo cA cB
      csuc vx cv ssel2 vx cv cB vx vex elsuc sylib ord con1d adantll mpd ex
      ssrdv ex impbid2 $.
  $}

  ${
    $d x y $.
    $( Two ways to express the class of non-limit ordinal numbers.  Part of
       Definition 7.27 of [TakeutiZaring] p. 42, who use the symbol K_I for
       this class.  (Contributed by NM, 1-Nov-2004.) $)
    nlimon $p |- { x e. On | ( x = (/) \/ E. y e. On x = suc y ) } =
                   { x e. On | -. Lim x } $=
      vx cv c0 wceq vx cv vy cv csuc wceq vy con0 wrex wo vx cv wlim wn vx con0
      vx cv con0 wcel vx cv word vx cv c0 wceq vx cv vy cv csuc wceq vy con0
      wrex wo vx cv wlim wn wb vx cv eloni vx cv word vx cv wlim vx cv c0 wceq
      vx cv vy cv csuc wceq vy con0 wrex wo vx cv wlim vx cv word vx cv c0 wceq
      vx cv vy cv csuc wceq vy con0 wrex wo wn vy vx cv dflim3 baib con2bid syl
      rabbiia $.
  $}

  ${
    $d x y z A $.
    $( The union of a nonempty class of limit ordinals is a limit ordinal.
       (Contributed by NM, 1-Feb-2005.) $)
    limuni3 $p |- ( ( A =/= (/) /\ A. x e. A Lim x ) -> Lim U. A ) $=
      cA c0 wne vx cv wlim vx cA wral wa cA cuni word c0 cA cuni wcel vy cv
      csuc cA cuni wcel vy cA cuni wral cA cuni wlim vx cv wlim vx cA wral cA
      cuni word cA c0 wne vx cv wlim vx cA wral cA con0 wss cA cuni word vx cv
      wlim vx cA wral vz cA con0 vz cv cA wcel vx cv wlim vx cA wral vz cv wlim
      vz cv con0 wcel vx cv wlim vz cv wlim vx vz cv cA vx cv vz cv limeq rspcv
      vz cv cvv wcel vz cv wlim vz cv con0 wcel vz vex vz cv cvv limelon mpan
      syl6com ssrdv cA ssorduni syl adantl cA c0 wne vx cv wlim vx cA wral c0
      cA cuni wcel cA c0 wne vz cv cA wcel vz wex vx cv wlim vx cA wral c0 cA
      cuni wcel wi vz cA n0 vz cv cA wcel vx cv wlim vx cA wral c0 cA cuni wcel
      wi vz vz cv cA wcel vx cv wlim vx cA wral vz cv wlim c0 cA cuni wcel vx
      cv wlim vz cv wlim vx vz cv cA vx cv vz cv limeq rspcv vz cv wlim c0 vz
      cv wcel vz cv cA wcel c0 cA cuni wcel vz cv 0ellim c0 vz cv wcel vz cv cA
      wcel c0 cA cuni wcel c0 vz cv cA elunii expcom syl5 syld exlimiv sylbi
      imp vx cv wlim vx cA wral vy cv csuc cA cuni wcel vy cA cuni wral cA c0
      wne vx cv wlim vx cA wral vy cv csuc cA cuni wcel vy cA cuni vy cv cA
      cuni wcel vy cv vz cv wcel vz cA wrex vx cv wlim vx cA wral vy cv csuc cA
      cuni wcel vz vy cv cA eluni2 vx cv wlim vx cA wral vy cv vz cv wcel vy cv
      csuc cA cuni wcel vz cA vx cv wlim vx cA wral vz cv cA wcel vz cv wlim vy
      cv vz cv wcel vy cv csuc cA cuni wcel wi vx cv wlim vz cv wlim vx vz cv
      cA vx cv vz cv limeq rspccv vz cv wlim vy cv vz cv wcel vz cv cA wcel vy
      cv csuc cA cuni wcel vz cv wlim vy cv vz cv wcel vz cv cA wcel vy cv csuc
      cA cuni wcel vz cv wlim vy cv vz cv wcel vz cv cA wcel wa vy cv csuc vz
      cv wcel vz cv cA wcel wa vy cv csuc cA cuni wcel vz cv wlim vy cv vz cv
      wcel vy cv csuc vz cv wcel vz cv cA wcel vz cv vy cv limsuc anbi1d vy cv
      csuc vz cv cA elunii syl6bi exp3a com3r sylcom rexlimdv syl5bi ralrimiv
      adantl vy cA cuni dflim4 syl3anbrc $.
  $}



