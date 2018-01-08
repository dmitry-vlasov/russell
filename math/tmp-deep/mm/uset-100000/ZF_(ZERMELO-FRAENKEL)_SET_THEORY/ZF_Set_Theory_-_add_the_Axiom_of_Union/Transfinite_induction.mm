
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Ordinals_(continued).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Transfinite induction

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( The Principle of Transfinite Induction.  Theorem 7.17 of [TakeutiZaring]
       p. 39.  This principle states that if ` A ` is a class of ordinal
       numbers with the property that every ordinal number included in ` A `
       also belongs to ` A ` , then every ordinal number is in ` A ` .

       See theorem ~ tfindes or ~ tfinds for the version involving basis and
       induction hypotheses.  (Contributed by NM, 18-Feb-2004.) $)
    tfi $p |- ( ( A C_ On /\ A. x e. On ( x C_ A -> x e. A ) ) -> A = On ) $=
      cA con0 wss vx cv cA wss vx cv cA wcel wi vx con0 wral wa cA con0 wss
      con0 cA wss wa cA con0 wceq vx cv cA wss vx cv cA wcel wi vx con0 wral
      con0 cA wss cA con0 wss vx cv cA wss vx cv cA wcel wi vx con0 wral con0
      cA cdif vx cv cin c0 wceq vx con0 cA cdif wrex con0 cA wss vx cv cA wss
      vx cv cA wcel wi vx con0 wral con0 cA cdif vx cv cin c0 wceq wn vx con0
      cA cdif wral con0 cA cdif vx cv cin c0 wceq vx con0 cA cdif wrex wn vx cv
      cA wss vx cv cA wcel wi con0 cA cdif vx cv cin c0 wceq wn vx con0 con0 cA
      cdif vx cv con0 wcel vx cv cA wss vx cv cA wcel wi wi vx cv con0 cA cdif
      wcel con0 cA cdif vx cv cin c0 wceq wn vx cv con0 wcel vx cv cA wss vx cv
      cA wcel wi wi vx cv con0 cA cdif wcel wa con0 cA cdif vx cv cin c0 wceq
      vx cv cA wcel vx cv con0 cA cdif wcel vx cv cA wcel wn vx cv con0 wcel vx
      cv cA wss vx cv cA wcel wi wi vx cv con0 cA eldifn adantl vx cv con0 wcel
      vx cv cA wss vx cv cA wcel wi wi vx cv con0 cA cdif wcel con0 cA cdif vx
      cv cin c0 wceq vx cv cA wcel wi vx cv con0 cA cdif wcel vx cv con0 wcel
      vx cv con0 wcel vx cv cA wss vx cv cA wcel wi wi con0 cA cdif vx cv cin
      c0 wceq vx cv cA wcel wi vx cv con0 cA eldifi vx cv con0 wcel vx cv cA
      wss vx cv cA wcel wi con0 cA cdif vx cv cin c0 wceq vx cv cA wcel wi vx
      cv con0 wcel con0 cA cdif vx cv cin c0 wceq vx cv cA wss vx cv cA wcel vx
      cv con0 wcel vx cv con0 wss con0 cA cdif vx cv cin c0 wceq vx cv cA wss
      vx cv onss con0 cA vx cv difin0ss syl5com imim1d a2i syl5 imp mtod ex
      ralimi2 con0 cA cdif vx cv cin c0 wceq vx con0 cA cdif ralnex sylib con0
      cA wss wn con0 cA cdif c0 wne con0 cA cdif vx cv cin c0 wceq vx con0 cA
      cdif wrex con0 cA wss con0 cA cdif c0 con0 cA ssdif0 necon3bbii con0 word
      con0 cA cdif con0 wss con0 cA cdif c0 wne con0 cA cdif vx cv cin c0 wceq
      vx con0 cA cdif wrex ordon con0 cA difss vx con0 con0 cA cdif tz7.5
      mp3an12 sylbi nsyl2 anim2i cA con0 eqss sylibr $.
  $}

  ${
    $d w y z ph $.  $d w x y z $.
    tfis.1 $e |- ( x e. On -> ( A. y e. x [ y / x ] ph -> ph ) ) $.
    $( Transfinite Induction Schema.  If all ordinal numbers less than a given
       number ` x ` have a property (induction hypothesis), then all ordinal
       numbers have the property (conclusion).  Exercise 25 of [Enderton]
       p. 200.  (Contributed by NM, 1-Aug-1994.)  (Revised by Mario Carneiro,
       20-Nov-2016.) $)
    tfis $p |- ( x e. On -> ph ) $=
      vx cv con0 wcel vx cv con0 wcel wph wph vx con0 con0 wph vx con0 crab
      con0 wph vx con0 crab con0 wss vz cv wph vx con0 crab wss vz cv wph vx
      con0 crab wcel wi vz con0 wral wph vx con0 crab con0 wceq wph vx con0
      ssrab2 vz cv wph vx con0 crab wss vz cv wph vx con0 crab wcel wi vz con0
      vy cv wph vx con0 crab wcel vy vx cv wral vx cv con0 wcel wph wa wi vz cv
      wph vx con0 crab wss vz cv wph vx con0 crab wcel wi vx vz cv con0 vx vz
      cv nfcv vz cv wph vx con0 crab wss vz cv wph vx con0 crab wcel vx vx vz
      cv wph vx con0 crab vx vz cv nfcv wph vx con0 nfrab1 nfss vx vz wph vx
      con0 crab wph vx con0 nfrab1 nfcri nfim vx cv vz cv wceq vy cv wph vx
      con0 crab wcel vy vx cv wral vz cv wph vx con0 crab wss vx cv con0 wcel
      wph wa vz cv wph vx con0 crab wcel vy cv wph vx con0 crab wcel vy vx cv
      wral vx cv wph vx con0 crab wss vx cv vz cv wceq vz cv wph vx con0 crab
      wss vy vx cv wph vx con0 crab dfss3 vx cv vz cv wph vx con0 crab sseq1
      syl5bbr vx cv con0 wcel wph wa vx cv wph vx con0 crab wcel vx cv vz cv
      wceq vz cv wph vx con0 crab wcel wph vx con0 rabid vx cv vz cv wph vx
      con0 crab eleq1 syl5bbr imbi12d vx cv con0 wcel vy cv wph vx con0 crab
      wcel vy vx cv wral wph vy cv wph vx con0 crab wcel vy vx cv wral wph vx
      vy wsb vy vx cv wral vx cv con0 wcel wph vy cv wph vx con0 crab wcel wph
      vx vy wsb vy vx cv vy cv wph vx con0 crab wcel vy cv con0 wcel wph vx vy
      wsb wph vx vw wsb wph vx vy wsb vw vy cv con0 wph vx con0 crab wph vw vy
      vx sbequ wph wph vx vw wsb vx vw con0 vx con0 nfcv vw con0 nfcv wph vw
      nfv wph vx vw nfs1v wph vx vw sbequ12 cbvrab elrab2 simprbi ralimi tfis.1
      syl5 anc2li vtoclgaf rgen vz wph vx con0 crab tfi mp2an eqcomi rabeq2i
      simprbi $.
  $}

  ${
    $d y ph $.  $d x y $.
    tfis2f.1 $e |- F/ x ps $.
    tfis2f.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    tfis2f.3 $e |- ( x e. On -> ( A. y e. x ps -> ph ) ) $.
    $( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by NM, 18-Aug-1994.) $)
    tfis2f $p |- ( x e. On -> ph ) $=
      wph vx vy wph vx vy wsb vy vx cv wral wps vy vx cv wral vx cv con0 wcel
      wph wph vx vy wsb wps vy vx cv wph wps vx vy tfis2f.1 tfis2f.2 sbie
      ralbii tfis2f.3 syl5bi tfis $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x y $.
    tfis2.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    tfis2.2 $e |- ( x e. On -> ( A. y e. x ps -> ph ) ) $.
    $( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by NM, 18-Aug-1994.) $)
    tfis2 $p |- ( x e. On -> ph ) $=
      wph wps vx vy wps vx nfv tfis2.1 tfis2.2 tfis2f $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x ch $.  $d x A $.  $d x y $.
    tfis3.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    tfis3.2 $e |- ( x = A -> ( ph <-> ch ) ) $.
    tfis3.3 $e |- ( x e. On -> ( A. y e. x ps -> ph ) ) $.
    $( Transfinite Induction Schema, using implicit substitution.  (Contributed
       by NM, 4-Nov-2003.) $)
    tfis3 $p |- ( A e. On -> ch ) $=
      wph wch vx cA con0 tfis3.2 wph wps vx vy tfis3.1 tfis3.3 tfis2 vtoclga $.
  $}

  ${
    $d x v w y z T $.  $d v w y z R $.  $d x v w z S $.  $d x v w z ch $.
    $d x v w y z ph $.  $d w y z ps $.  $d x A $.  $d x th $.
    tfisi.a $e |- ( ph -> A e. V ) $.
    tfisi.b $e |- ( ph -> T e. On ) $.
    tfisi.c $e |- ( ( ph /\ ( R e. On /\ R C_ T ) /\
          A. y ( S e. R -> ch ) ) -> ps ) $.
    tfisi.d $e |- ( x = y -> ( ps <-> ch ) ) $.
    tfisi.e $e |- ( x = A -> ( ps <-> th ) ) $.
    tfisi.f $e |- ( x = y -> R = S ) $.
    tfisi.g $e |- ( x = A -> R = T ) $.
    $( A transfinite induction scheme in "implicit" form where the induction is
       done on an object derived from the object of interest.  (Contributed by
       Stefan O'Rear, 24-Aug-2015.) $)
    tfisi $p |- ( ph -> th ) $=
      wph cT cT wss wth cT ssid wph cT cT wss wth wi wph wph cT cT wss wth wph
      cT cT wceq wph cT cT wss wa wth wi cT eqid wph cA cV wcel cR cT wceq wph
      cT cT wss wa wps wi wi vx wal cT cT wceq wph cT cT wss wa wth wi wi
      tfisi.a wph cT con0 wcel cR cT wceq wph cT cT wss wa wps wi wi vx wal
      tfisi.b cR vz cv wceq wph vz cv cT wss wa wps wi wi vx wal cS vw cv wceq
      wph vw cv cT wss wa wch wi wi vy wal cR cT wceq wph cT cT wss wa wps wi
      wi vx wal vz vw cT vz cv vw cv wceq cR vz cv wceq wph vz cv cT wss wa wps
      wi wi vx wal cR vw cv wceq wph vw cv cT wss wa wps wi wi vx wal cS vw cv
      wceq wph vw cv cT wss wa wch wi wi vy wal vz cv vw cv wceq cR vz cv wceq
      wph vz cv cT wss wa wps wi wi cR vw cv wceq wph vw cv cT wss wa wps wi wi
      vx vz cv vw cv wceq cR vz cv wceq cR vw cv wceq wph vz cv cT wss wa wps
      wi wph vw cv cT wss wa wps wi vz cv vw cv cR eqeq2 vz cv vw cv wceq wph
      vz cv cT wss wa wph vw cv cT wss wa wps vz cv vw cv wceq vz cv cT wss vw
      cv cT wss wph vz cv vw cv cT sseq1 anbi2d imbi1d imbi12d albidv cR vw cv
      wceq wph vw cv cT wss wa wps wi wi cS vw cv wceq wph vw cv cT wss wa wch
      wi wi vx vy vx cv vy cv wceq cR vw cv wceq cS vw cv wceq wph vw cv cT wss
      wa wps wi wph vw cv cT wss wa wch wi vx cv vy cv wceq cR cS vw cv tfisi.f
      eqeq1d vx cv vy cv wceq wps wch wph vw cv cT wss wa tfisi.d imbi2d
      imbi12d cbvalv syl6bb vz cv cT wceq cR vz cv wceq wph vz cv cT wss wa wps
      wi wi cR cT wceq wph cT cT wss wa wps wi wi vx vz cv cT wceq cR vz cv
      wceq cR cT wceq wph vz cv cT wss wa wps wi wph cT cT wss wa wps wi vz cv
      cT cR eqeq2 vz cv cT wceq wph vz cv cT wss wa wph cT cT wss wa wps vz cv
      cT wceq vz cv cT wss cT cT wss wph vz cv cT cT sseq1 anbi2d imbi1d
      imbi12d albidv vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi
      wi vy wal vw vz cv wral cR vz cv wceq wph vz cv cT wss wa wps wi wi vx
      wal vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw
      vz cv wral wa cR vz cv wceq wph vz cv cT wss wa wps wi wi vx vz cv con0
      wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa
      cR vz cv wceq wph vz cv cT wss wa wps vz cv con0 wcel cS vw cv wceq wph
      vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv
      cT wss wa w3a wph cR con0 wcel cR cT wss cS cR wcel wch wi vy wal wps vz
      cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv
      wral wa cR vz cv wceq wph vz cv cT wss simp3l vz cv con0 wcel cS vw cv
      wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq
      wph vz cv cT wss wa w3a cR vz cv con0 vz cv con0 wcel cS vw cv wceq wph
      vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv
      cT wss wa simp2 vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi
      wi vy wal vw vz cv wral cR vz cv wceq wph vz cv cT wss wa simp1l eqeltrd
      vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz
      cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a cR vz cv cT vz cv con0
      wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa
      cR vz cv wceq wph vz cv cT wss wa simp2 vz cv con0 wcel cS vw cv wceq wph
      vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv
      cT wss simp3r eqsstrd vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa
      wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a
      vx vv cv cR csb cR wcel wps vx vv wsb wi vv wal cS cR wcel wch wi vy wal
      vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz
      cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv cv cR csb cR wcel
      wps vx vv wsb wi vv vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch
      wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv
      cv cR csb cR wcel wps vx vv wsb vz cv con0 wcel cS vw cv wceq wph vw cv
      cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv cT
      wss wa w3a vx vv cv cR csb cR wcel wa wph vx vv cv cR csb cT wss wps vx
      vv wsb wph vz cv cT wss vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa
      wch wi wi vy wal vw vz cv wral wa cR vz cv wceq vx vv cv cR csb cR wcel
      simpl3l vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy
      wal vw vz cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv cv cR
      csb cR wcel wa vx vv cv cR csb vz cv cT vz cv con0 wcel cS vw cv wceq wph
      vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv
      cT wss wa w3a vx vv cv cR csb cR wcel wa vz cv con0 wcel vx vv cv cR csb
      vz cv wcel vx vv cv cR csb vz cv wss vz cv con0 wcel cS vw cv wceq wph vw
      cv cT wss wa wch wi wi vy wal vw vz cv wral cR vz cv wceq wph vz cv cT
      wss wa vx vv cv cR csb cR wcel simpl1l vz cv con0 wcel cS vw cv wceq wph
      vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv
      cT wss wa w3a vx vv cv cR csb cR wcel wa vx vv cv cR csb cR vz cv vz cv
      con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv
      wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv cv cR csb cR wcel
      simpr vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal
      vw vz cv wral wa cR vz cv wceq wph vz cv cT wss wa vx vv cv cR csb cR
      wcel simpl2 eleqtrd vz cv vx vv cv cR csb onelss sylc wph vz cv cT wss vz
      cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv
      wral wa cR vz cv wceq vx vv cv cR csb cR wcel simpl3r sstrd vz cv con0
      wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa
      cR vz cv wceq wph vz cv cT wss wa w3a vx vv cv cR csb cR wcel wa cS vx vv
      cv cR csb wceq wph vx vv cv cR csb cT wss wa wch wi wi vy wal vx vv cv cR
      csb vx vv cv cR csb wceq wph vx vv cv cR csb cT wss wa wps vx vv wsb wi
      vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz
      cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv cv cR csb cR wcel
      wa vx vv cv cR csb vz cv wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi
      vy wal vw vz cv wral cS vx vv cv cR csb wceq wph vx vv cv cR csb cT wss
      wa wch wi wi vy wal vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch
      wi wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv
      cv cR csb cR wcel wa vx vv cv cR csb cR vz cv vz cv con0 wcel cS vw cv
      wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv wceq
      wph vz cv cT wss wa w3a vx vv cv cR csb cR wcel simpr vz cv con0 wcel cS
      vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv wral wa cR vz cv
      wceq wph vz cv cT wss wa vx vv cv cR csb cR wcel simpl2 eleqtrd vz cv
      con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi wi vy wal vw vz cv
      wral cR vz cv wceq wph vz cv cT wss wa vx vv cv cR csb cR wcel simpl1r cS
      vw cv wceq wph vw cv cT wss wa wch wi wi vy wal cS vx vv cv cR csb wceq
      wph vx vv cv cR csb cT wss wa wch wi wi vy wal vw vx vv cv cR csb vz cv
      vw cv vx vv cv cR csb wceq cS vw cv wceq wph vw cv cT wss wa wch wi wi cS
      vx vv cv cR csb wceq wph vx vv cv cR csb cT wss wa wch wi wi vy vw cv vx
      vv cv cR csb wceq cS vw cv wceq cS vx vv cv cR csb wceq wph vw cv cT wss
      wa wch wi wph vx vv cv cR csb cT wss wa wch wi vw cv vx vv cv cR csb cS
      eqeq2 vw cv vx vv cv cR csb wceq wph vw cv cT wss wa wph vx vv cv cR csb
      cT wss wa wch vw cv vx vv cv cR csb wceq vw cv cT wss vx vv cv cR csb cT
      wss wph vw cv vx vv cv cR csb cT sseq1 anbi2d imbi1d imbi12d albidv
      rspcva syl2anc vz cv con0 wcel cS vw cv wceq wph vw cv cT wss wa wch wi
      wi vy wal vw vz cv wral wa cR vz cv wceq wph vz cv cT wss wa w3a vx vv cv
      cR csb cR wcel wa vx vv cv cR csb eqidd cS vx vv cv cR csb wceq wph vx vv
      cv cR csb cT wss wa wch wi wi vx vv cv cR csb vx vv cv cR csb wceq wph vx
      vv cv cR csb cT wss wa wps vx vv wsb wi wi vy vv vy cv vv cv wceq cS vx
      vv cv cR csb wceq vx vv cv cR csb vx vv cv cR csb wceq wph vx vv cv cR
      csb cT wss wa wch wi wph vx vv cv cR csb cT wss wa wps vx vv wsb wi vy cv
      vv cv wceq cS vx vv cv cR csb vx vv cv cR csb cS vx vv cv cR csb wceq vv
      cv vy cv vv cv vy cv wceq vx vv cv cR csb cS vx vv vy cv cR cS vx vy cv
      nfcv vx cS nfcv tfisi.f csbhypf eqcomd eqcoms eqeq1d vy cv vv cv wceq wch
      wps vx vv wsb wph vx vv cv cR csb cT wss wa wch wps vx vv wsb wb vv cv vy
      cv vv cv vy cv wceq wps vx vv wsb wch vv cv vy cv wceq wps vx vv wsb wps
      vx vy wsb wch wps vv vy vx sbequ wps wch vx vy wch vx nfv tfisi.d sbie
      syl6bb bicomd eqcoms imbi2d imbi12d spv sylc mp2and ex alrimiv vx vv cv
      cR csb cR wcel wps vx vv wsb wi cS cR wcel wch wi vv vy vv cv vy cv wceq
      vx vv cv cR csb cR wcel cS cR wcel wps vx vv wsb wch vv cv vy cv wceq vx
      vv cv cR csb cS cR vx vv vy cv cR cS vx vy cv nfcv vx cS nfcv tfisi.f
      csbhypf eleq1d vv cv vy cv wceq wps vx vv wsb wps vx vy wsb wch wps vv vy
      vx sbequ wps wch vx vy wch vx nfv tfisi.d sbie syl6bb imbi12d cbvalv
      sylib tfisi.c syl121anc 3exp alrimiv ex tfis3 syl cR cT wceq wph cT cT
      wss wa wps wi wi cT cT wceq wph cT cT wss wa wth wi wi vx cA cV vx cv cA
      wceq cR cT wceq cT cT wceq wph cT cT wss wa wps wi wph cT cT wss wa wth
      wi vx cv cA wceq cR cT cT tfisi.g eqeq1d vx cv cA wceq wps wth wph cT cT
      wss wa tfisi.e imbi2d imbi12d spcgv sylc mpi exp3a pm2.43i mpi $.
  $}

  ${
    $d x y z $.  $d x A $.  $d x z ch $.  $d x ta $.  $d y z ph $.
    $( Substitutions. $)
    tfinds.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    tfinds.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    tfinds.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    tfinds.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    tfinds.5 $e |- ps $.
    $( Induction hypothesis for successors. $)
    tfinds.6 $e |- ( y e. On -> ( ch -> th ) ) $.
    $( Induction hypothesis for limit ordinals. $)
    tfinds.7 $e |- ( Lim x -> ( A. y e. x ch -> ph ) ) $.
    $( Principle of Transfinite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last three are the basis, the induction hypothesis for
       successors, and the induction hypothesis for limit ordinals.  Theorem
       Schema 4 of [Suppes] p. 197.  (Contributed by NM, 16-Apr-1995.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    tfinds $p |- ( A e. On -> ta ) $=
      wph wch wta vx vy cA tfinds.2 tfinds.4 vx cv con0 wcel vx cv wlim wch vy
      vx cv wral wph wi vx cv wlim wn vx cv word vx cv c0 wceq vx cv vy cv csuc
      wceq vy con0 wrex wo wn wa wn vx cv con0 wcel wch vy vx cv wral wph wi vx
      cv wlim vx cv word vx cv c0 wceq vx cv vy cv csuc wceq vy con0 wrex wo wn
      wa vy vx cv dflim3 notbii vx cv word vx cv c0 wceq vx cv vy cv csuc wceq
      vy con0 wrex wo wn wa wn vx cv word vx cv c0 wceq vx cv vy cv csuc wceq
      vy con0 wrex wo wi vx cv con0 wcel wch vy vx cv wral wph wi vx cv word vx
      cv c0 wceq vx cv vy cv csuc wceq vy con0 wrex wo iman vx cv con0 wcel vx
      cv word vx cv c0 wceq vx cv vy cv csuc wceq vy con0 wrex wo wi vx cv c0
      wceq vx cv vy cv csuc wceq vy con0 wrex wo wch vy vx cv wral wph wi vx cv
      con0 wcel vx cv word vx cv word vx cv c0 wceq vx cv vy cv csuc wceq vy
      con0 wrex wo wi vx cv c0 wceq vx cv vy cv csuc wceq vy con0 wrex wo wi vx
      cv eloni vx cv word vx cv c0 wceq vx cv vy cv csuc wceq vy con0 wrex wo
      pm2.27 syl vx cv c0 wceq wch vy vx cv wral wph wi vx cv vy cv csuc wceq
      vy con0 wrex vx cv c0 wceq wph wch vy vx cv wral vx cv c0 wceq wph wps
      tfinds.5 tfinds.1 mpbiri a1d vx cv vy cv csuc wceq wch vy vx cv wral wph
      wi vy con0 wch vy vx cv wral wph vy wch vy vx cv nfra1 wph vy nfv nfim vy
      cv con0 wcel vx cv vy cv csuc wceq wch vy vx cv wral wth wph vy cv con0
      wcel wch vy vx cv wral wth wi vx cv vy cv csuc wceq wph vx vy cv csuc
      wral wth wi wph vx vy cv csuc wral wch vy cv con0 wcel wth vy cv vy cv
      csuc wcel wph vx vy cv csuc wral wch wi vy cv vy vex sucid wph wch vx vy
      cv vy cv csuc tfinds.2 rspcv ax-mp tfinds.6 syl5 vx cv vy cv csuc wceq
      wch vy vx cv wral wph vx vy cv csuc wral wth vx cv vy cv csuc wceq wph vx
      vz wsb vz vx cv wral wph vx vz wsb vz vy cv csuc wral wch vy vx cv wral
      wph vx vy cv csuc wral wph vx vz wsb vz vx cv vy cv csuc raleq wch wph vx
      vz wsb vy vz vx cv wch wph vx vy wsb vy cv vz cv wceq wph vx vz wsb wph
      wch vx vy wch vx nfv tfinds.2 sbie wph vy vz vx sbequ syl5bbr cbvralv wph
      vx vz vy cv csuc cbvralsv 3bitr4g imbi1d syl5ibrcom vx cv vy cv csuc wceq
      wth wph wi wi vy cv con0 wcel vx cv vy cv csuc wceq wph wth tfinds.3
      biimprd a1i syldd rexlimi jaoi syl6 syl5bir syl5bi tfinds.7 pm2.61d2
      tfis3 $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x ch $.  $d x th $.  $d x ta $.  $d y ph $.
    $( Substitutions. $)
    tfindsg.1 $e |- ( x = B -> ( ph <-> ps ) ) $.
    tfindsg.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    tfindsg.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    tfindsg.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    tfindsg.5 $e |- ( B e. On -> ps ) $.
    $( Induction hypothesis for successor ordinals. $)
    tfindsg.6 $e |- ( ( ( y e. On /\ B e. On ) /\ B C_ y ) -> ( ch -> th ) ) $.
    $( Induction hypothesis for limit ordinals. $)
    tfindsg.7 $e |- ( ( ( Lim x /\ B e. On ) /\ B C_ x ) ->
                   ( A. y e. x ( B C_ y -> ch ) -> ph ) ) $.
    $( Transfinite Induction (inference schema), using implicit substitutions.
       The first four hypotheses establish the substitutions we need.  The last
       three are the basis, the induction hypothesis for successors, and the
       induction hypothesis for limit ordinals.  The basis of this version is
       an arbitrary ordinal ` B ` instead of zero.  Remark in [TakeutiZaring]
       p. 57.  (Contributed by NM, 5-Mar-2004.) $)
    tfindsg $p |- ( ( ( A e. On /\ B e. On ) /\ B C_ A ) -> ta ) $=
      cA con0 wcel cB con0 wcel cB cA wss wta cB con0 wcel cB vx cv wss wph wi
      wi cB con0 wcel cB c0 wss wps wi wi cB con0 wcel cB vy cv wss wch wi wi
      cB con0 wcel cB vy cv csuc wss wth wi wi cB con0 wcel cB cA wss wta wi wi
      vx vy cA vx cv c0 wceq cB vx cv wss wph wi cB c0 wss wps wi cB con0 wcel
      cB c0 wceq vx cv c0 wceq cB vx cv wss wph wi cB c0 wss wps wi wb cB c0
      wceq vx cv c0 wceq wa cB vx cv wss cB c0 wss wph wps vx cv c0 wceq cB vx
      cv wss cB c0 wss wb cB c0 wceq vx cv c0 cB sseq2 adantl cB c0 wceq vx cv
      c0 wceq wph wps wb cB c0 wceq vx cv c0 wceq vx cv cB wceq wph wps wb cB
      c0 vx cv eqeq2 tfindsg.1 syl6bir imp imbi12d vx cv c0 wceq cB vx cv wss
      wph wi cB c0 wss wph wi cB c0 wceq wn cB c0 wss wps wi vx cv c0 wceq cB
      vx cv wss cB c0 wss wph vx cv c0 cB sseq2 imbi1d cB c0 wceq wn cB c0 wss
      wph wps cB c0 wceq wn cB c0 wss wph wps wb cB c0 wss cB c0 wceq cB ss0
      con3i pm2.21d pm5.74d sylan9bbr pm2.61ian imbi2d vx cv vy cv wceq cB vx
      cv wss wph wi cB vy cv wss wch wi cB con0 wcel vx cv vy cv wceq cB vx cv
      wss cB vy cv wss wph wch vx cv vy cv cB sseq2 tfindsg.2 imbi12d imbi2d vx
      cv vy cv csuc wceq cB vx cv wss wph wi cB vy cv csuc wss wth wi cB con0
      wcel vx cv vy cv csuc wceq cB vx cv wss cB vy cv csuc wss wph wth vx cv
      vy cv csuc cB sseq2 tfindsg.3 imbi12d imbi2d vx cv cA wceq cB vx cv wss
      wph wi cB cA wss wta wi cB con0 wcel vx cv cA wceq cB vx cv wss cB cA wss
      wph wta vx cv cA cB sseq2 tfindsg.4 imbi12d imbi2d cB con0 wcel wps cB c0
      wss tfindsg.5 a1d vy cv con0 wcel cB con0 wcel cB vy cv wss wch wi cB vy
      cv csuc wss wth wi vy cv con0 wcel cB con0 wcel cB vy cv wss wch wi cB vy
      cv csuc wss wth wi wi vy cv con0 wcel cB con0 wcel wa cB vy cv csuc wss
      cB vy cv csuc wceq wi cB vy cv wss wch wi cB vy cv csuc wss wth wi wi cB
      con0 wcel cB vy cv csuc wss cB vy cv csuc wceq wi cB vy cv wss wch wi cB
      vy cv csuc wss wth wi wi wi vy cv con0 wcel cB vy cv csuc wss cB vy cv
      csuc wceq wi cB vy cv wss wch wi cB vy cv csuc wss cB con0 wcel wth cB vy
      cv csuc wss cB vy cv csuc wceq wi cB vy cv csuc wss cB con0 wcel wth wi
      wi cB vy cv wss wch wi cB vy cv csuc wceq cB con0 wcel wth wi cB vy cv
      csuc wss cB con0 wcel wth wi vy cv csuc cB vy cv csuc cB wceq vx cv vy cv
      csuc wceq vx cv cB wceq wa vx wex cB con0 wcel wth wi vx vy cv csuc cB vy
      cv vy vex sucex eqvinc vx cv vy cv csuc wceq vx cv cB wceq wa cB con0
      wcel wth wi vx vx cv cB wceq cB con0 wcel wph vx cv vy cv csuc wceq wth
      cB con0 wcel wph vx cv cB wceq wps tfindsg.5 tfindsg.1 syl5ibr vx cv vy
      cv csuc wceq wph wth tfindsg.3 biimpd sylan9r exlimiv sylbi eqcoms imim2i
      a1d com4r adantl cB vy cv csuc wss cB vy cv csuc wceq wi wn cB vy cv csuc
      wss cB vy cv csuc wne wa vy cv con0 wcel cB con0 wcel wa cB vy cv wss wch
      wi cB vy cv csuc wss wth wi wi cB vy cv csuc wss cB vy cv csuc wne wa cB
      vy cv csuc wss cB vy cv csuc wceq wn wa cB vy cv csuc wss cB vy cv csuc
      wceq wi wn cB vy cv csuc wne cB vy cv csuc wceq wn cB vy cv csuc wss cB
      vy cv csuc df-ne anbi2i cB vy cv csuc wss cB vy cv csuc wceq annim bitri
      vy cv con0 wcel cB con0 wcel wa cB vy cv csuc wss cB vy cv csuc wne wa cB
      vy cv wss cB vy cv wss wch wi cB vy cv csuc wss wth wi wi cB con0 wcel vy
      cv con0 wcel cB vy cv wss cB vy cv csuc wss cB vy cv csuc wne wa wb cB
      con0 wcel vy cv con0 wcel wa cB vy cv wss cB vy cv csuc wcel cB vy cv
      csuc wss cB vy cv csuc wne wa cB vy cv onsssuc vy cv con0 wcel cB con0
      wcel vy cv csuc con0 wcel cB vy cv csuc wcel cB vy cv csuc wss cB vy cv
      csuc wne wa wb vy cv suceloni cB vy cv csuc onelpss sylan2 bitrd ancoms
      vy cv con0 wcel cB con0 wcel wa cB vy cv wss wch wi cB vy cv wss cB vy cv
      csuc wss wth wi vy cv con0 wcel cB con0 wcel wa cB vy cv wss wch cB vy cv
      csuc wss wth wi vy cv con0 wcel cB con0 wcel wa cB vy cv wss wch wth cB
      vy cv csuc wss wth wi vy cv con0 wcel cB con0 wcel wa cB vy cv wss wch
      wth wi tfindsg.6 ex wth cB vy cv csuc wss ax-1 syl8 a2d com23 sylbird
      syl5bir pm2.61d ex a2d cB con0 wcel cB vx cv wss vx cv wlim cB con0 wcel
      cB vy cv wss wch wi wi vy vx cv wral wph vx cv wlim cB con0 wcel cB vx cv
      wss cB con0 wcel cB vy cv wss wch wi wi vy vx cv wral wph wi vx cv wlim
      cB con0 wcel cB vx cv wss cB con0 wcel cB vy cv wss wch wi wi vy vx cv
      wral wph wi vx cv wlim cB con0 wcel wa cB vx cv wss wa cB con0 wcel cB vy
      cv wss wch wi wi vy vx cv wral cB vy cv wss wch wi vy vx cv wral wph cB
      con0 wcel cB con0 wcel cB vy cv wss wch wi wi vy vx cv wral cB vy cv wss
      wch wi vy vx cv wral wi vx cv wlim cB vx cv wss cB con0 wcel cB con0 wcel
      cB vy cv wss wch wi wi cB vy cv wss wch wi vy vx cv cB con0 wcel cB vy cv
      wss wch wi pm2.27 ralimdv ad2antlr tfindsg.7 syld exp31 com3l com4t
      tfinds imp31 $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x ch $.  $d x th $.  $d x ta $.  $d y ph $.
    $( Substitutions. $)
    tfindsg2.1 $e |- ( x = suc B -> ( ph <-> ps ) ) $.
    tfindsg2.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    tfindsg2.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    tfindsg2.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    tfindsg2.5 $e |- ( B e. On -> ps ) $.
    $( Induction hypothesis for successor ordinals. $)
    tfindsg2.6 $e |- ( ( y e. On /\ B e. y ) -> ( ch -> th ) ) $.
    $( Induction hypothesis for limit ordinals. $)
    tfindsg2.7 $e |- ( ( Lim x /\ B e. x ) ->
                   ( A. y e. x ( B e. y -> ch ) -> ph ) ) $.
    $( Transfinite Induction (inference schema), using implicit substitutions.
       The first four hypotheses establish the substitutions we need.  The last
       three are the basis, the induction hypothesis for successors, and the
       induction hypothesis for limit ordinals.  The basis of this version is
       an arbitrary ordinal ` suc B ` instead of zero.  (Unnecessary distinct
       variable restrictions were removed by David Abernethy, 19-Jun-2012.)
       (Contributed by NM, 5-Jan-2005.) $)
    tfindsg2 $p |- ( ( A e. On /\ B e. A ) -> ta ) $=
      cA con0 wcel cB cA wcel wa cB csuc con0 wcel cB csuc cA wss wta cA con0
      wcel cB cA wcel wa cB con0 wcel cB csuc con0 wcel cA cB onelon cB sucelon
      sylib cA con0 wcel cB cA wcel cB csuc cA wss cA con0 wcel cA word cB cA
      wcel cB csuc cA wss wi cA eloni cB cA ordsucss syl imp cA con0 wcel cB
      csuc con0 wcel cB csuc cA wss wa wta wi cB cA wcel cA con0 wcel cB csuc
      con0 wcel cB csuc cA wss wta wph wps wch wth wta vx vy cA cB csuc
      tfindsg2.1 tfindsg2.2 tfindsg2.3 tfindsg2.4 cB csuc con0 wcel cB con0
      wcel wps cB sucelon tfindsg2.5 sylbir vy cv con0 wcel cB csuc con0 wcel
      wa cB csuc vy cv wss wch wth wi cB csuc con0 wcel vy cv con0 wcel cB con0
      wcel cB csuc vy cv wss wch wth wi wi cB sucelon vy cv con0 wcel cB con0
      wcel wa cB csuc vy cv wss cB vy cv wcel wch wth wi cB con0 wcel vy cv
      con0 wcel cB vy cv wcel cB csuc vy cv wss wb vy cv con0 wcel cB con0 wcel
      vy cv word cB vy cv wcel cB csuc vy cv wss wb vy cv eloni cB vy cv con0
      ordelsuc sylan2 ancoms vy cv con0 wcel cB vy cv wcel wch wth wi wi cB
      con0 wcel vy cv con0 wcel cB vy cv wcel wch wth wi tfindsg2.6 ex adantr
      sylbird sylan2br imp vx cv wlim cB csuc con0 wcel wa cB csuc vx cv wss cB
      csuc vy cv wss wch wi vy vx cv wral wph wi cB csuc con0 wcel vx cv wlim
      cB con0 wcel cB csuc vx cv wss cB csuc vy cv wss wch wi vy vx cv wral wph
      wi wi cB sucelon vx cv wlim cB con0 wcel wa cB vx cv wcel cB vy cv wcel
      wch wi vy vx cv wral wph wi wi cB csuc vx cv wss cB csuc vy cv wss wch wi
      vy vx cv wral wph wi wi vx cv wlim cB vx cv wcel cB vy cv wcel wch wi vy
      vx cv wral wph wi wi cB con0 wcel vx cv wlim cB vx cv wcel cB vy cv wcel
      wch wi vy vx cv wral wph wi tfindsg2.7 ex adantr cB con0 wcel vx cv wlim
      cB vx cv wcel cB vy cv wcel wch wi vy vx cv wral wph wi wi cB csuc vx cv
      wss cB csuc vy cv wss wch wi vy vx cv wral wph wi wi wb vx cv wlim cB
      con0 wcel vx cv con0 wcel cB vx cv wcel cB vy cv wcel wch wi vy vx cv
      wral wph wi wi cB csuc vx cv wss cB csuc vy cv wss wch wi vy vx cv wral
      wph wi wi wb vx cv cvv wcel vx cv wlim vx cv con0 wcel vx vex vx cv cvv
      limelon mpan cB con0 wcel vx cv con0 wcel wa cB vx cv wcel cB csuc vx cv
      wss cB vy cv wcel wch wi vy vx cv wral wph wi cB csuc vy cv wss wch wi vy
      vx cv wral wph wi vx cv con0 wcel cB con0 wcel vx cv word cB vx cv wcel
      cB csuc vx cv wss wb vx cv eloni cB vx cv con0 ordelsuc sylan2 cB con0
      wcel vx cv con0 wcel wa cB vy cv wcel wch wi vy vx cv wral cB csuc vy cv
      wss wch wi vy vx cv wral wph cB con0 wcel vx cv con0 wcel wa cB vy cv
      wcel wch wi cB csuc vy cv wss wch wi vy vx cv cB con0 wcel vx cv con0
      wcel wa vy cv vx cv wcel wa cB vy cv wcel cB csuc vy cv wss wch cB con0
      wcel vx cv con0 wcel vy cv vx cv wcel cB vy cv wcel cB csuc vy cv wss wb
      vx cv con0 wcel vy cv vx cv wcel wa cB con0 wcel vy cv word cB vy cv wcel
      cB csuc vy cv wss wb vx cv con0 wcel vy cv vx cv wcel wa vy cv con0 wcel
      vy cv word vx cv vy cv onelon vy cv eloni syl cB vy cv con0 ordelsuc
      sylan2 anassrs imbi1d ralbidva imbi1d imbi12d sylan2 ancoms mpbid
      sylan2br imp tfindsg expl adantr mp2and $.
  $}

  ${
    $d x y z $.  $d y z ph $.
    tfindes.1 $e |- [. (/) / x ]. ph $.
    tfindes.2 $e |- ( x e. On -> ( ph -> [. suc x / x ]. ph ) ) $.
    tfindes.3 $e |- ( Lim y -> ( A. x e. y ph -> [. y / x ]. ph ) ) $.
    $( Transfinite Induction with explicit substitution.  The first hypothesis
       is the basis, the second is the induction hypothesis for successors, and
       the third is the induction hypothesis for limit ordinals.  Theorem
       Schema 4 of [Suppes] p. 197.  (Contributed by NM, 5-Mar-2004.) $)
    tfindes $p |- ( x e. On -> ph ) $=
      wph vx vy cv wsbc wph vx c0 wsbc wph vx vz cv wsbc wph vx vz cv csuc wsbc
      wph vy vz vx cv wph vx vy cv c0 dfsbcq wph vx vy cv vz cv dfsbcq wph vx
      vy cv vz cv csuc dfsbcq wph vx vy cv sbceq2a tfindes.1 vx cv con0 wcel
      wph wph vx vx cv csuc wsbc wi wi vz cv con0 wcel wph vx vz cv wsbc wph vx
      vz cv csuc wsbc wi wi vx vz vz cv con0 wcel wph vx vz cv wsbc wph vx vz
      cv csuc wsbc wi vx vz cv con0 wcel vx nfv wph vx vz cv wsbc wph vx vz cv
      csuc wsbc vx wph vx vz cv nfsbc1v wph vx vz cv csuc nfsbc1v nfim nfim vx
      vz weq vx cv con0 wcel vz cv con0 wcel wph wph vx vx cv csuc wsbc wi wph
      vx vz cv wsbc wph vx vz cv csuc wsbc wi vx cv vz cv con0 eleq1 vx vz weq
      wph wph vx vz cv wsbc wph vx vx cv csuc wsbc wph vx vz cv csuc wsbc wph
      vx vz cv sbceq1a vx vz weq vx cv csuc vz cv csuc wceq wph vx vx cv csuc
      wsbc wph vx vz cv csuc wsbc wb vx cv vz cv suceq wph vx vx cv csuc vz cv
      csuc dfsbcq syl imbi12d imbi12d tfindes.2 chvar wph vx vz cv wsbc vz vy
      cv wral wph vx vy cv wral vy cv wlim wph vx vy cv wsbc wph vx vy cv wral
      wph vx vz wsb vz vy cv wral wph vx vz cv wsbc vz vy cv wral wph vx vz vy
      cv cbvralsv wph vx vz wsb wph vx vz cv wsbc vz vy cv wph vx vz sbsbc
      ralbii bitri tfindes.3 syl5bir tfinds $.
  $}

  ${
    $d x y ta $.  $d x ps $.  $d x ch $.  $d x th $.  $d y ph $.
    $( Substitutions. $)
    tfinds2.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    tfinds2.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    tfinds2.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    $( Basis. $)
    tfinds2.4 $e |- ( ta -> ps ) $.
    $( Induction hypothesis for successors. $)
    tfinds2.5 $e |- ( y e. On -> ( ta -> ( ch -> th ) ) ) $.
    $( Induction hypothesis for limit ordinals. $)
    tfinds2.6 $e |- ( Lim x -> ( ta -> ( A. y e. x ch -> ph ) ) ) $.
    $( Transfinite Induction (inference schema), using implicit substitutions.
       The first three hypotheses establish the substitutions we need.  The
       last three are the basis and the induction hypotheses (for successor and
       limit ordinals respectively).  Theorem Schema 4 of [Suppes] p. 197.  The
       wff ` ta ` is an auxiliary antecedent to help shorten proofs using this
       theorem.  (Contributed by NM, 4-Sep-2004.) $)
    tfinds2 $p |- ( x e. On -> ( ta -> ph ) ) $=
      wta wph wi vx vy wta wph wi vx c0 wsbc wta wps wi tfinds2.4 wta wph wi
      wta wps wi vx c0 0ex vx cv c0 wceq wph wps wta tfinds2.1 imbi2d sbcie
      mpbir vx cv con0 wcel wta wch wi vy vx cv wsbc wta wth wi vy vx cv wsbc
      wta wph wi wta wph wi vx vx cv csuc wsbc vy cv con0 wcel vy vx cv wsbc
      wta wch wi wta wth wi wi vy vx cv wsbc vx cv con0 wcel wta wch wi vy vx
      cv wsbc wta wth wi vy vx cv wsbc wi vy cv con0 wcel wta wch wi wta wth wi
      wi wi vy vx cv wsbc vy cv con0 wcel vy vx cv wsbc wta wch wi wta wth wi
      wi vy vx cv wsbc wi vx cv cvv wcel vy cv con0 wcel wta wch wi wta wth wi
      wi wi vy vx cv wsbc vx vex vy cv con0 wcel wta wch wi wta wth wi wi wi vy
      vx cv cvv vy cv con0 wcel wta wch wth tfinds2.5 a2d sbcth ax-mp vx cv cvv
      wcel vy cv con0 wcel wta wch wi wta wth wi wi wi vy vx cv wsbc vy cv con0
      wcel vy vx cv wsbc wta wch wi wta wth wi wi vy vx cv wsbc wi wb vx vex vy
      cv con0 wcel wta wch wi wta wth wi wi vy vx cv cvv sbcimg ax-mp mpbi vx
      cv cvv wcel vy cv con0 wcel vy vx cv wsbc vx cv con0 wcel wb vx vex vy vx
      cv con0 cvv sbcel1gv ax-mp vx cv cvv wcel wta wch wi wta wth wi wi vy vx
      cv wsbc wta wch wi vy vx cv wsbc wta wth wi vy vx cv wsbc wi wb vx vex
      wta wch wi wta wth wi vy vx cv cvv sbcimg ax-mp 3imtr3i wta wch wi wta
      wph wi vy vx cv vx vex vy vx weq wch wph wta wch wph wb vx vy vx vy weq
      wph wch tfinds2.2 bicomd equcoms imbi2d sbcie wta wth wi vy vx cv wsbc
      wta wph wi vx vy cv csuc wsbc vy vx cv wsbc wta wph wi vx vx cv csuc wsbc
      wta wph wi vx vy cv csuc wsbc wta wth wi vy vx cv wta wph wi wta wth wi
      vx vy cv csuc vy cv vy vex sucex vx cv vy cv csuc wceq wph wth wta
      tfinds2.3 imbi2d sbcie sbcbii wta wph wi vx vy vx cv csuc vy cv csuc vx
      cv vy cv suceq sbcco2 bitr3i 3imtr3g wta wph wi vx vy cv wral wta wch wi
      vy vx cv wral vx vy cv wsbc vy cv wlim wta wph wi vx vy cv wsbc wta wch
      wi vy vx cv wral vx vy cv wsbc wta wch wi vy vx cv wral vx vy wsb wta wph
      wi vx vy cv wral wta wch wi vy vx cv wral vx vy sbsbc wta wch wi wta wph
      wi vy vx vy vx weq wch wph wta wch wph wb vx vy vx vy weq wph wch
      tfinds2.2 bicomd equcoms imbi2d sbralie bitr3i vx cv wlim vx vy cv wsbc
      wta wch wi vy vx cv wral wta wph wi wi vx vy cv wsbc vy cv wlim wta wch
      wi vy vx cv wral vx vy cv wsbc wta wph wi vx vy cv wsbc wi vx cv wlim wta
      wch wi vy vx cv wral wta wph wi wi wi vx vy cv wsbc vx cv wlim vx vy cv
      wsbc wta wch wi vy vx cv wral wta wph wi wi vx vy cv wsbc wi vy cv cvv
      wcel vx cv wlim wta wch wi vy vx cv wral wta wph wi wi wi vx vy cv wsbc
      vy vex vx cv wlim wta wch wi vy vx cv wral wta wph wi wi wi vx vy cv cvv
      wta wch wi vy vx cv wral wta wch vy vx cv wral wi vx cv wlim wta wph wi
      wta wch vy vx cv r19.21v vx cv wlim wta wch vy vx cv wral wph tfinds2.6
      a2d syl5bi sbcth ax-mp vy cv cvv wcel vx cv wlim wta wch wi vy vx cv wral
      wta wph wi wi wi vx vy cv wsbc vx cv wlim vx vy cv wsbc wta wch wi vy vx
      cv wral wta wph wi wi vx vy cv wsbc wi wb vy vex vx cv wlim wta wch wi vy
      vx cv wral wta wph wi wi vx vy cv cvv sbcimg ax-mp mpbi vx cv wlim vy cv
      wlim vx vy cv vy vex vx cv vy cv limeq sbcie vy cv cvv wcel wta wch wi vy
      vx cv wral wta wph wi wi vx vy cv wsbc wta wch wi vy vx cv wral vx vy cv
      wsbc wta wph wi vx vy cv wsbc wi wb vy vex wta wch wi vy vx cv wral wta
      wph wi vx vy cv cvv sbcimg ax-mp 3imtr3i syl5bir tfindes $.
  $}

  ${
    $d x A $.  $d y ph $.  $d x ch $.  $d x ta $.  $d x y et $.
    $( Substitutions. $)
    tfinds3.1 $e |- ( x = (/) -> ( ph <-> ps ) ) $.
    tfinds3.2 $e |- ( x = y -> ( ph <-> ch ) ) $.
    tfinds3.3 $e |- ( x = suc y -> ( ph <-> th ) ) $.
    tfinds3.4 $e |- ( x = A -> ( ph <-> ta ) ) $.
    $( Basis. $)
    tfinds3.5 $e |- ( et -> ps ) $.
    $( Induction hypothesis for successors. $)
    tfinds3.6 $e |- ( y e. On -> ( et -> ( ch -> th ) ) ) $.
    $( Induction hypothesis for limit ordinals. $)
    tfinds3.7 $e |- ( Lim x -> ( et -> ( A. y e. x ch -> ph ) ) ) $.
    $( Principle of Transfinite Induction (inference schema), using implicit
       substitutions.  The first four hypotheses establish the substitutions we
       need.  The last three are the basis, the induction hypothesis for
       successors, and the induction hypothesis for limit ordinals.
       (Contributed by NM, 6-Jan-2005.)  (Revised by David Abernethy,
       21-Jun-2011.) $)
    tfinds3 $p |- ( A e. On -> ( et -> ta ) ) $=
      wet wph wi wet wps wi wet wch wi wet wth wi wet wta wi vx vy cA vx cv c0
      wceq wph wps wet tfinds3.1 imbi2d vx cv vy cv wceq wph wch wet tfinds3.2
      imbi2d vx cv vy cv csuc wceq wph wth wet tfinds3.3 imbi2d vx cv cA wceq
      wph wta wet tfinds3.4 imbi2d tfinds3.5 vy cv con0 wcel wet wch wth
      tfinds3.6 a2d wet wch wi vy vx cv wral wet wch vy vx cv wral wi vx cv
      wlim wet wph wi wet wch vy vx cv r19.21v vx cv wlim wet wch vy vx cv wral
      wph tfinds3.7 a2d syl5bi tfinds $.
  $}


