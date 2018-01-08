
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Undefined_values_and_restricted_iota_(description_binder).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Functions on ordinals; strictly monotone ordinal functions

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( The indexed union of a set of ordinal numbers ` B ( x ) ` is an ordinal
       number.  (Contributed by NM, 13-Oct-2003.)  (Revised by Mario Carneiro,
       5-Dec-2016.) $)
    iunon $p |- ( ( A e. V /\ A. x e. A B e. On ) -> U_ x e. A B e. On ) $=
      cA cV wcel cB con0 wcel vx cA wral wa vx cA cB ciun vx cA cB cmpt crn
      cuni con0 cB con0 wcel vx cA wral vx cA cB ciun vx cA cB cmpt crn cuni
      wceq cA cV wcel vx cA cB con0 dfiun3g adantl cA cV wcel vx cA cB cmpt crn
      cvv wcel vx cA cB cmpt crn con0 wss vx cA cB cmpt crn cuni con0 wcel cB
      con0 wcel vx cA wral cA cV wcel vx cA cB cmpt cvv wcel vx cA cB cmpt crn
      cvv wcel vx cA cB cV mptexg vx cA cB cmpt cvv rnexg syl cB con0 wcel vx
      cA wral cA con0 vx cA cB cmpt wf vx cA cB cmpt crn con0 wss vx cA con0 cB
      vx cA cB cmpt vx cA cB cmpt eqid fmpt cA con0 vx cA cB cmpt frn sylbi vx
      cA cB cmpt crn cvv wcel vx cA cB cmpt crn con0 wss vx cA cB cmpt crn cuni
      con0 wcel vx cA cB cmpt crn cvv ssonuni imp syl2an eqeltrd $.

    iunonOLD.1 $e |- A e. _V $.
    iunonOLD.2 $e |- B e. _V $.
    $( The indexed union of a set of ordinal numbers ` B ( x ) ` is an ordinal
       number.  (Contributed by NM, 13-Oct-2003.)  (Revised by Mario Carneiro,
       5-Dec-2016.) $)
    iunonOLD $p |- ( A. x e. A B e. On -> U_ x e. A B e. On ) $=
      cA cvv wcel cB con0 wcel vx cA wral vx cA cB ciun con0 wcel iunonOLD.1 vx
      cA cB cvv iunon mpan $.
  $}

  ${
    $d x y z A $.  $d y z B $.
    $( The nonempty indexed intersection of a class of ordinal numbers
       ` B ( x ) ` is an ordinal number.  (Contributed by NM, 13-Oct-2003.)
       (Proof shortened by Mario Carneiro, 5-Dec-2016.) $)
    iinon $p |- ( ( A. x e. A B e. On /\ A =/= (/) ) ->
                |^|_ x e. A B e. On ) $=
      cB con0 wcel vx cA wral cA c0 wne wa vx cA cB ciin vx cA cB cmpt crn cint
      con0 cB con0 wcel vx cA wral vx cA cB ciin vx cA cB cmpt crn cint wceq cA
      c0 wne vx cA cB con0 dfiin3g adantr cB con0 wcel vx cA wral cA c0 wne wa
      vx cA cB cmpt crn con0 wss vx cA cB cmpt crn c0 wne vx cA cB cmpt crn
      cint con0 wcel cB con0 wcel vx cA wral vx cA cB cmpt crn con0 wss cA c0
      wne cB con0 wcel vx cA wral cA con0 vx cA cB cmpt wf vx cA cB cmpt crn
      con0 wss vx cA con0 cB vx cA cB cmpt vx cA cB cmpt eqid fmpt cA con0 vx
      cA cB cmpt frn sylbi adantr cB con0 wcel vx cA wral vx cA cB cmpt crn c0
      wne cA c0 wne cB con0 wcel vx cA wral vx cA cB cmpt crn c0 cA c0 vx cA cB
      cmpt crn c0 wceq vx cA cB cmpt cdm c0 wceq cB con0 wcel vx cA wral cA c0
      wceq vx cA cB cmpt dm0rn0 cB con0 wcel vx cA wral vx cA cB cmpt cdm cA c0
      vx cA cB con0 dmmptg eqeq1d syl5bbr necon3bid biimpar vx cA cB cmpt crn
      oninton syl2anc eqeltrd $.
  $}

  ${
    $d x y S $.  $d x y F $.  $d x T $.
    onfununi.1 $e |- ( Lim y -> ( F ` y ) = U_ x e. y ( F ` x ) ) $.
    onfununi.2 $e |- ( ( x e. On /\ y e. On /\ x C_ y )
                  -> ( F ` x ) C_ ( F ` y ) ) $.
    $( A property of functions on ordinal numbers.  Generalization of Theorem
       Schema 8E of [Enderton] p. 218.  (Contributed by Eric Schmidt,
       26-May-2009.) $)
    onfununi $p |- ( ( S e. T /\ S C_ On /\ S =/= (/) )
                -> ( F ` U. S ) = U_ x e. S ( F ` x ) ) $=
      cS cT wcel cS con0 wss cS c0 wne w3a cS cuni cF cfv vx cS vx cv cF cfv
      ciun cS cT wcel cS con0 wss cS c0 wne w3a cS cuni cS wcel cS cuni cF cfv
      vx cS vx cv cF cfv ciun wss cS cT wcel cS con0 wss cS c0 wne w3a cS cuni
      cS wcel wn cS cuni cF cfv vx cS vx cv cF cfv ciun wss cS cT wcel cS con0
      wss cS c0 wne w3a cS cuni cS wcel wn wa cS cuni cF cfv vx cS cuni vx cv
      cF cfv ciun vx cS vx cv cF cfv ciun cS cT wcel cS con0 wss cS c0 wne w3a
      cS cuni cS wcel wn wa cS cuni wlim cS cuni cF cfv vx cS cuni vx cv cF cfv
      ciun wceq cS con0 wss cS c0 wne cS cuni cS wcel wn cS cuni wlim cS cT
      wcel cS con0 wss cS cuni cS wcel wn cS c0 wne cS cuni wlim cS con0 wss cS
      cuni cS wcel wn wa cS c0 wne wa cS cuni word cS cuni c0 wne cS cuni cS
      cuni cuni wceq cS cuni wlim cS con0 wss cS cuni word cS cuni cS wcel wn
      cS c0 wne cS ssorduni ad2antrr cS con0 wss cS cuni cS wcel wn wa cS cS
      cuni wss cS c0 wne cS cuni c0 wne cS con0 wss cS cuni cS wcel wn wa vx cS
      cS cuni cS con0 wss cS cuni cS wcel wn vx cv cS wcel vx cv cS cuni wcel
      wi cS con0 wss vx cv cS wcel cS cuni cS wcel wn vx cv cS cuni wcel cS
      con0 wss vx cv cS wcel cS cuni cS wcel wn vx cv cS cuni wcel wi cS con0
      wss vx cv cS wcel vx cv cS wcel cS cuni cS wcel wn vx cv cS cuni wcel vx
      cv cS wcel cS cuni cS wcel wn wa vx cv cS cuni wceq wn cS con0 wss vx cv
      cS wcel wa vx cv cS cuni wcel vx cv cS cuni cS nelneq cS con0 wss vx cv
      cS wcel wa vx cv cS cuni wcel vx cv cS cuni wceq cS con0 wss vx cv cS
      wcel wa vx cv cS cuni wcel vx cv cS cuni wceq cS con0 wss vx cv cS wcel
      wa vx cv cS cuni wss vx cv cS cuni wcel vx cv cS cuni wceq wo vx cv cS
      wcel vx cv cS cuni wss cS con0 wss vx cv cS elssuni adantl cS con0 wss vx
      cv cS wcel vx cv cS cuni wss vx cv cS cuni wcel vx cv cS cuni wceq wo wb
      cS con0 wss vx cv cS wcel wa vx cv word cS cuni word vx cv cS cuni wss vx
      cv cS cuni wcel vx cv cS cuni wceq wo wb cS con0 wss cS con0 wss vx cv cS
      wcel vx cv word cS con0 wss vx cv cS wcel vx cv con0 wcel vx cv word cS
      con0 vx cv ssel vx cv eloni syl6 imp cS ssorduni vx cv cS cuni ordsseleq
      syl2an anabss1 mpbid ord con1d syl5 exp4b pm2.43d com23 imp ssrdv cS cS
      cuni ssn0 sylan cS con0 wss cS cuni cS wcel wn wa cS cuni cS cuni cuni
      wceq cS c0 wne cS con0 wss cS cuni cS wcel wn wa cS cuni cS cuni cuni cS
      con0 wss cS cuni cS wcel wn wa cS cS cuni wss cS cuni cS cuni cuni wss cS
      con0 wss cS cuni cS wcel wn wa vx cS cS cuni cS con0 wss cS cuni cS wcel
      wn vx cv cS wcel vx cv cS cuni wcel wi cS con0 wss vx cv cS wcel cS cuni
      cS wcel wn vx cv cS cuni wcel cS con0 wss vx cv cS wcel cS cuni cS wcel
      wn vx cv cS cuni wcel wi cS con0 wss vx cv cS wcel vx cv cS wcel cS cuni
      cS wcel wn vx cv cS cuni wcel vx cv cS wcel cS cuni cS wcel wn wa vx cv
      cS cuni wceq wn cS con0 wss vx cv cS wcel wa vx cv cS cuni wcel vx cv cS
      cuni cS nelneq cS con0 wss vx cv cS wcel wa vx cv cS cuni wcel vx cv cS
      cuni wceq cS con0 wss vx cv cS wcel wa vx cv cS cuni wcel vx cv cS cuni
      wceq cS con0 wss vx cv cS wcel wa vx cv cS cuni wss vx cv cS cuni wcel vx
      cv cS cuni wceq wo vx cv cS wcel vx cv cS cuni wss cS con0 wss vx cv cS
      elssuni adantl cS con0 wss vx cv cS wcel vx cv cS cuni wss vx cv cS cuni
      wcel vx cv cS cuni wceq wo wb cS con0 wss vx cv cS wcel wa vx cv word cS
      cuni word vx cv cS cuni wss vx cv cS cuni wcel vx cv cS cuni wceq wo wb
      cS con0 wss cS con0 wss vx cv cS wcel vx cv word cS con0 wss vx cv cS
      wcel vx cv con0 wcel vx cv word cS con0 vx cv ssel vx cv eloni syl6 imp
      cS ssorduni vx cv cS cuni ordsseleq syl2an anabss1 mpbid ord con1d syl5
      exp4b pm2.43d com23 imp ssrdv cS cS cuni uniss syl cS con0 wss cS cuni
      cuni cS cuni wss cS cuni cS wcel wn cS con0 wss cS cuni word cS cuni cuni
      cS cuni wss cS ssorduni cS cuni orduniss syl adantr eqssd adantr cS cuni
      df-lim syl3anbrc an32s 3adantl1 cS cT wcel cS con0 wss cS c0 wne w3a cS
      cuni wlim cS cuni cF cfv vx cS cuni vx cv cF cfv ciun wceq wi cS cuni cS
      wcel wn cS cT wcel cS con0 wss cS cuni wlim cS cuni cF cfv vx cS cuni vx
      cv cF cfv ciun wceq wi cS c0 wne cS cT wcel cS con0 wss cS cuni wlim cS
      cuni cF cfv vx cS cuni vx cv cF cfv ciun wceq wi cS cT wcel cS con0 wss
      cS cuni con0 wcel cS cuni wlim cS cuni cF cfv vx cS cuni vx cv cF cfv
      ciun wceq wi cS cT ssonuni vy cv wlim vy cv cF cfv vx vy cv vx cv cF cfv
      ciun wceq wi cS cuni wlim cS cuni cF cfv vx cS cuni vx cv cF cfv ciun
      wceq wi vy cS cuni con0 vy cv cS cuni wceq vy cv wlim cS cuni wlim vy cv
      cF cfv vx vy cv vx cv cF cfv ciun wceq cS cuni cF cfv vx cS cuni vx cv cF
      cfv ciun wceq vy cv cS cuni limeq vy cv cS cuni wceq vy cv cF cfv cS cuni
      cF cfv vx vy cv vx cv cF cfv ciun vx cS cuni vx cv cF cfv ciun vy cv cS
      cuni cF fveq2 vx vy cv cS cuni vx cv cF cfv iuneq1 eqeq12d imbi12d
      onfununi.1 vtoclg syl6 imp 3adant3 adantr mpd cS cT wcel cS con0 wss cS
      c0 wne w3a vx cS cuni vx cv cF cfv ciun vx cS vx cv cF cfv ciun wss cS
      cuni cS wcel wn cS con0 wss cS cT wcel vx cS cuni vx cv cF cfv ciun vx cS
      vx cv cF cfv ciun wss cS c0 wne cS con0 wss vx cS cuni vx cv cF cfv ciun
      vy cS vy cv cF cfv ciun vx cS vx cv cF cfv ciun cS con0 wss vx cv cF cfv
      vy cS vy cv cF cfv ciun wss vx cS cuni wral vx cS cuni vx cv cF cfv ciun
      vy cS vy cv cF cfv ciun wss cS con0 wss vx cv cF cfv vy cS vy cv cF cfv
      ciun wss vx cS cuni cS con0 wss vx cv cS cuni wcel vx cv cF cfv vy cv cF
      cfv wss vy cS wrex vx cv cF cfv vy cS vy cv cF cfv ciun wss vx cv cS cuni
      wcel vx cv vy cv wcel vy cS wrex cS con0 wss vx cv cF cfv vy cv cF cfv
      wss vy cS wrex vy vx cv cS eluni2 cS con0 wss vx cv vy cv wcel vx cv cF
      cfv vy cv cF cfv wss vy cS cS con0 wss vy cv cS wcel vx cv vy cv wcel vx
      cv cF cfv vy cv cF cfv wss cS con0 wss vy cv cS wcel vx cv vy cv wcel wa
      vx cv con0 wcel vy cv con0 wcel vx cv vy cv wss w3a vx cv cF cfv vy cv cF
      cfv wss cS con0 wss vy cv cS wcel vx cv vy cv wcel wa vx cv con0 wcel vy
      cv con0 wcel vx cv vy cv wss cS con0 wss vy cv cS wcel vx cv vy cv wcel
      wa vy cv con0 wcel vx cv vy cv wcel wa vx cv con0 wcel cS con0 wss vy cv
      cS wcel vy cv con0 wcel vx cv vy cv wcel cS con0 vy cv ssel anim1d vy cv
      vx cv onelon syl6 cS con0 wss vy cv cS wcel vy cv con0 wcel vx cv vy cv
      wcel cS con0 vy cv ssel adantrd cS con0 wss vy cv cS wcel vy cv word vx
      cv vy cv wcel vx cv vy cv wss cS con0 wss vy cv cS wcel vy cv con0 wcel
      vy cv word cS con0 vy cv ssel vy cv eloni syl6 vy cv word vx cv vy cv
      wcel wa vx cv vy cv wss wi cS con0 wss vy cv vx cv ordelss a1i syland
      3jcad onfununi.2 syl6 exp3a reximdvai syl5bi vy cS vy cv cF cfv vx cv cF
      cfv ssiun syl6 ralrimiv vx cS cuni vx cv cF cfv vy cS vy cv cF cfv ciun
      iunss sylibr vy vx cS vy cv cF cfv vx cv cF cfv vy cv vx cv cF fveq2
      cbviunv syl6sseq 3ad2ant2 adantr eqsstrd ex vx cS vx cv cF cfv cS cuni cS
      cuni cF cfv vx cv cS cuni cF fveq2 ssiun2s pm2.61d2 cS cT wcel cS con0
      wss cS c0 wne w3a vx cv cF cfv cS cuni cF cfv wss vx cS wral vx cS vx cv
      cF cfv ciun cS cuni cF cfv wss cS cT wcel cS con0 wss cS c0 wne w3a vx cv
      cF cfv cS cuni cF cfv wss vx cS cS cT wcel cS con0 wss cS c0 wne w3a cS
      cuni con0 wcel vx cv cS wcel vx cv con0 wcel vx cv cS cuni wss wa vx cv
      cF cfv cS cuni cF cfv wss cS cT wcel cS con0 wss cS cuni con0 wcel cS c0
      wne cS cT wcel cS con0 wss cS cuni con0 wcel cS cT ssonuni imp 3adant3 cS
      cT wcel cS con0 wss cS c0 wne w3a vx cv cS wcel vx cv con0 wcel vx cv cS
      cuni wss cS con0 wss cS cT wcel vx cv cS wcel vx cv con0 wcel wi cS c0
      wne cS con0 vx cv ssel 3ad2ant2 vx cv cS wcel vx cv cS cuni wss wi cS cT
      wcel cS con0 wss cS c0 wne w3a vx cv cS elssuni a1i jcad vx cv con0 wcel
      vx cv vy cv wss wa vx cv cF cfv vy cv cF cfv wss wi vx cv con0 wcel vx cv
      cS cuni wss wa vx cv cF cfv cS cuni cF cfv wss wi vy cS cuni con0 vy cv
      cS cuni wceq vx cv con0 wcel vx cv vy cv wss wa vx cv con0 wcel vx cv cS
      cuni wss wa vx cv cF cfv vy cv cF cfv wss vx cv cF cfv cS cuni cF cfv wss
      vy cv cS cuni wceq vx cv vy cv wss vx cv cS cuni wss vx cv con0 wcel vy
      cv cS cuni vx cv sseq2 anbi2d vy cv cS cuni wceq vy cv cF cfv cS cuni cF
      cfv vx cv cF cfv vy cv cS cuni cF fveq2 sseq2d imbi12d vy cv con0 wcel vx
      cv con0 wcel vx cv vy cv wss vx cv cF cfv vy cv cF cfv wss vx cv con0
      wcel vy cv con0 wcel vx cv vy cv wss vx cv cF cfv vy cv cF cfv wss
      onfununi.2 3com12 3expib vtoclga sylsyld ralrimiv vx cS vx cv cF cfv cS
      cuni cF cfv iunss sylibr eqssd $.
  $}

  ${
    $d w x y z A $.  $d w x y z F $.  $d w x y z K $.  $d w x y L $.
    $d w x y z S $.  $d w T $.
    onovuni.1 $e |- ( Lim y -> ( A F y ) = U_ x e. y ( A F x ) ) $.
    onovuni.2 $e |- ( ( x e. On /\ y e. On /\ x C_ y )
                  -> ( A F x ) C_ ( A F y ) ) $.
    ${
      $d x T $.
      $( A variant of ~ onfununi for operations.  (Contributed by Eric Schmidt,
         26-May-2009.)  (Revised by Mario Carneiro, 11-Sep-2015.) $)
      onovuni $p |- ( ( S e. T /\ S C_ On /\ S =/= (/) )
                     -> ( A F U. S ) = U_ x e. S ( A F x ) ) $=
        cS cT wcel cS con0 wss cS c0 wne w3a cS cuni vz cvv cA vz cv cF co cmpt
        cfv vx cS vx cv vz cvv cA vz cv cF co cmpt cfv ciun cA cS cuni cF co vx
        cS cA vx cv cF co ciun vx vy cS cT vz cvv cA vz cv cF co cmpt vy cv
        wlim cA vy cv cF co vx vy cv cA vx cv cF co ciun vy cv vz cvv cA vz cv
        cF co cmpt cfv vx vy cv vx cv vz cvv cA vz cv cF co cmpt cfv ciun
        onovuni.1 vy cv cvv wcel vy cv vz cvv cA vz cv cF co cmpt cfv cA vy cv
        cF co wceq vy vex vz vy cv cA vz cv cF co cA vy cv cF co cvv vz cvv cA
        vz cv cF co cmpt vz cv vy cv cA cF oveq2 vz cvv cA vz cv cF co cmpt
        eqid cA vy cv cF ovex fvmpt ax-mp vx vy cv vx cv vz cvv cA vz cv cF co
        cmpt cfv cA vx cv cF co vx cv vz cvv cA vz cv cF co cmpt cfv cA vx cv
        cF co wceq vx cv vy cv wcel vx cv cvv wcel vx cv vz cvv cA vz cv cF co
        cmpt cfv cA vx cv cF co wceq vx vex vz vx cv cA vz cv cF co cA vx cv cF
        co cvv vz cvv cA vz cv cF co cmpt vz cv vx cv cA cF oveq2 vz cvv cA vz
        cv cF co cmpt eqid cA vx cv cF ovex fvmpt ax-mp a1i iuneq2i 3eqtr4g vx
        cv con0 wcel vy cv con0 wcel vx cv vy cv wss w3a cA vx cv cF co cA vy
        cv cF co vx cv vz cvv cA vz cv cF co cmpt cfv vy cv vz cvv cA vz cv cF
        co cmpt cfv onovuni.2 vx cv cvv wcel vx cv vz cvv cA vz cv cF co cmpt
        cfv cA vx cv cF co wceq vx vex vz vx cv cA vz cv cF co cA vx cv cF co
        cvv vz cvv cA vz cv cF co cmpt vz cv vx cv cA cF oveq2 vz cvv cA vz cv
        cF co cmpt eqid cA vx cv cF ovex fvmpt ax-mp vy cv cvv wcel vy cv vz
        cvv cA vz cv cF co cmpt cfv cA vy cv cF co wceq vy vex vz vy cv cA vz
        cv cF co cA vy cv cF co cvv vz cvv cA vz cv cF co cmpt vz cv vy cv cA
        cF oveq2 vz cvv cA vz cv cF co cmpt eqid cA vy cv cF ovex fvmpt ax-mp
        3sstr4g onfununi cS cT wcel cS con0 wss cS cuni vz cvv cA vz cv cF co
        cmpt cfv cA cS cuni cF co wceq cS c0 wne cS cT wcel cS cuni cvv wcel cS
        cuni vz cvv cA vz cv cF co cmpt cfv cA cS cuni cF co wceq cS cT uniexg
        vz cS cuni cA vz cv cF co cA cS cuni cF co cvv vz cvv cA vz cv cF co
        cmpt vz cv cS cuni cA cF oveq2 vz cvv cA vz cv cF co cmpt eqid cA cS
        cuni cF ovex fvmpt syl 3ad2ant1 vx cS vx cv vz cvv cA vz cv cF co cmpt
        cfv ciun vx cS cA vx cv cF co ciun wceq cS cT wcel cS con0 wss cS c0
        wne w3a vx cS vx cv vz cvv cA vz cv cF co cmpt cfv cA vx cv cF co vx cv
        vz cvv cA vz cv cF co cmpt cfv cA vx cv cF co wceq vx cv cS wcel vx cv
        cvv wcel vx cv vz cvv cA vz cv cF co cmpt cfv cA vx cv cF co wceq vx
        vex vz vx cv cA vz cv cF co cA vx cv cF co cvv vz cvv cA vz cv cF co
        cmpt vz cv vx cv cA cF oveq2 vz cvv cA vz cv cF co cmpt eqid cA vx cv
        cF ovex fvmpt ax-mp a1i iuneq2i a1i 3eqtr3d $.
    $}

    $( A variant of ~ onovuni with indexed unions.  (Contributed by Eric
       Schmidt, 26-May-2009.)  (Proof shortened by Mario Carneiro,
       5-Dec-2016.) $)
    onoviun $p |- ( ( K e. T /\ A. z e. K L e. On /\ K =/= (/) )
                -> ( A F U_ z e. K L ) = U_ z e. K ( A F L ) ) $=
      cK cT wcel cL con0 wcel vz cK wral cK c0 wne w3a cA vz cK cL ciun cF co
      cA vz cK cL cmpt crn cuni cF co vx vz cK cL cmpt crn cA vx cv cF co ciun
      vz cK cA cL cF co ciun cK cT wcel cL con0 wcel vz cK wral cK c0 wne w3a
      vz cK cL ciun vz cK cL cmpt crn cuni cA cF cL con0 wcel vz cK wral cK cT
      wcel vz cK cL ciun vz cK cL cmpt crn cuni wceq cK c0 wne vz cK cL con0
      dfiun3g 3ad2ant2 oveq2d cK cT wcel cL con0 wcel vz cK wral cK c0 wne w3a
      vz cK cL cmpt crn cvv wcel vz cK cL cmpt crn con0 wss vz cK cL cmpt crn
      c0 wne cA vz cK cL cmpt crn cuni cF co vx vz cK cL cmpt crn cA vx cv cF
      co ciun wceq cK cT wcel cL con0 wcel vz cK wral cK c0 wne w3a cK cT wcel
      vz cK cL cmpt cvv wcel vz cK cL cmpt crn cvv wcel cK cT wcel cL con0 wcel
      vz cK wral cK c0 wne simp1 vz cK cL cT mptexg vz cK cL cmpt cvv rnexg
      3syl cK cT wcel cL con0 wcel vz cK wral cK c0 wne w3a cK con0 vz cK cL
      cmpt wf vz cK cL cmpt crn con0 wss cK cT wcel cL con0 wcel vz cK wral cK
      c0 wne w3a cL con0 wcel vz cK wral cK con0 vz cK cL cmpt wf cK cT wcel cL
      con0 wcel vz cK wral cK c0 wne simp2 vz cK con0 cL vz cK cL cmpt vz cK cL
      cmpt eqid fmpt sylib cK con0 vz cK cL cmpt frn syl cK cT wcel cL con0
      wcel vz cK wral cK c0 wne w3a vz cK cL cmpt cdm c0 wne vz cK cL cmpt crn
      c0 wne cK cT wcel cL con0 wcel vz cK wral cK c0 wne w3a vz cK cL cmpt cdm
      cK c0 cL con0 wcel vz cK wral cK cT wcel vz cK cL cmpt cdm cK wceq cK c0
      wne vz cK cL con0 dmmptg 3ad2ant2 cK cT wcel cL con0 wcel vz cK wral cK
      c0 wne simp3 eqnetrd vz cK cL cmpt cdm c0 vz cK cL cmpt crn c0 vz cK cL
      cmpt dm0rn0 necon3bii sylib vx vy cA vz cK cL cmpt crn cvv cF onovuni.1
      onovuni.2 onovuni syl3anc cK cT wcel cL con0 wcel vz cK wral cK c0 wne
      w3a vw vx vz cK cL cmpt crn cA vx cv cF co ciun vz cK cA cL cF co ciun cK
      cT wcel cL con0 wcel vz cK wral cK c0 wne w3a vw cv cA vx cv cF co wcel
      vx vz cK cL cmpt crn wrex vw cv cA cL cF co wcel vz cK wrex vw cv vx vz
      cK cL cmpt crn cA vx cv cF co ciun wcel vw cv vz cK cA cL cF co ciun wcel
      cL con0 wcel vz cK wral cK cT wcel vw cv cA vx cv cF co wcel vx vz cK cL
      cmpt crn wrex vw cv cA cL cF co wcel vz cK wrex wb cK c0 wne vw cv cA vx
      cv cF co wcel vw cv cA cL cF co wcel vz vx cK cL vz cK cL cmpt con0 vz cK
      cL cmpt eqid vx cv cL wceq cA vx cv cF co cA cL cF co vw cv vx cv cL cA
      cF oveq2 eleq2d rexrnmpt 3ad2ant2 vx vw cv vz cK cL cmpt crn cA vx cv cF
      co eliun vz vw cv cK cA cL cF co eliun 3bitr4g eqrdv 3eqtrd $.
  $}

  ${
    $d w x y z F $.
    $( There are no length ` om ` decreasing sequences in the ordinals.  See
       also ~ noinfep for a stronger version assuming Regularity.  (Contributed
       by Mario Carneiro, 19-May-2015.) $)
    onnseq $p |- ( ( F ` (/) ) e. On ->
      E. x e. om -. ( F ` suc x ) e. ( F ` x ) ) $=
      c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wn vx
      cv csuc cF cfv vx cv cF cfv wcel wn vx com wrex c0 cF cfv con0 wcel vx cv
      csuc cF cfv vx cv cF cfv wcel vx com wral vy com vy cv cF cfv cmpt crn vw
      cv cF cfv cin c0 wceq vw com wrex c0 cF cfv con0 wcel vx cv csuc cF cfv
      vx cv cF cfv wcel vx com wral wa vy com vy cv cF cfv cmpt crn vz cv cin
      c0 wceq vz vy com vy cv cF cfv cmpt crn wrex vy com vy cv cF cfv cmpt crn
      vw cv cF cfv cin c0 wceq vw com wrex c0 cF cfv con0 wcel vx cv csuc cF
      cfv vx cv cF cfv wcel vx com wral wa con0 cep wwe vy com vy cv cF cfv
      cmpt crn con0 wss vy com vy cv cF cfv cmpt crn c0 wne vy com vy cv cF cfv
      cmpt crn vz cv cin c0 wceq vz vy com vy cv cF cfv cmpt crn wrex con0 cep
      wwe c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral
      wa epweon a1i c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx
      com wral wa com con0 vy com vy cv cF cfv cmpt wf vy com vy cv cF cfv cmpt
      crn con0 wss c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx
      com wral wa vy cv cF cfv con0 wcel vy com wral com con0 vy com vy cv cF
      cfv cmpt wf c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx
      com wral wa vy cv cF cfv con0 wcel vy com vy cv com wcel c0 cF cfv con0
      wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wa vy cv cF cfv con0
      wcel vy cv cF cfv con0 wcel c0 cF cfv con0 wcel vz cv cF cfv con0 wcel vz
      cv csuc cF cfv con0 wcel c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF
      cfv wcel vx com wral wa vy vz vy cv c0 wceq vy cv cF cfv c0 cF cfv con0
      vy cv c0 cF fveq2 eleq1d vy cv vz cv wceq vy cv cF cfv vz cv cF cfv con0
      vy cv vz cv cF fveq2 eleq1d vy cv vz cv csuc wceq vy cv cF cfv vz cv csuc
      cF cfv con0 vy cv vz cv csuc cF fveq2 eleq1d c0 cF cfv con0 wcel vx cv
      csuc cF cfv vx cv cF cfv wcel vx com wral simpl vz cv com wcel vx cv csuc
      cF cfv vx cv cF cfv wcel vx com wral vz cv cF cfv con0 wcel vz cv csuc cF
      cfv con0 wcel wi c0 cF cfv con0 wcel vz cv com wcel vx cv csuc cF cfv vx
      cv cF cfv wcel vx com wral vz cv csuc cF cfv vz cv cF cfv wcel vz cv cF
      cfv con0 wcel vz cv csuc cF cfv con0 wcel wi vx cv csuc cF cfv vx cv cF
      cfv wcel vz cv csuc cF cfv vz cv cF cfv wcel vx vz cv com vx cv vz cv
      wceq vx cv csuc cF cfv vz cv csuc cF cfv vx cv cF cfv vz cv cF cfv vx cv
      vz cv wceq vx cv csuc vz cv csuc cF vx cv vz cv suceq fveq2d vx cv vz cv
      cF fveq2 eleq12d rspcv vz cv cF cfv con0 wcel vz cv csuc cF cfv vz cv cF
      cfv wcel vz cv csuc cF cfv con0 wcel vz cv cF cfv vz cv csuc cF cfv
      onelon expcom syl6 adantld finds2 com12 ralrimiv vy com con0 vy cv cF cfv
      vy com vy cv cF cfv cmpt vy com vy cv cF cfv cmpt eqid fmpt sylib com
      con0 vy com vy cv cF cfv cmpt frn syl c0 cF cfv con0 wcel vx cv csuc cF
      cfv vx cv cF cfv wcel vx com wral wa vy com vy cv cF cfv cmpt cdm c0 wne
      vy com vy cv cF cfv cmpt crn c0 wne c0 cF cfv con0 wcel vx cv csuc cF cfv
      vx cv cF cfv wcel vx com wral wa c0 vy com vy cv cF cfv cmpt cdm wcel vy
      com vy cv cF cfv cmpt cdm c0 wne c0 cF cfv con0 wcel vx cv csuc cF cfv vx
      cv cF cfv wcel vx com wral wa c0 com vy com vy cv cF cfv cmpt cdm peano1
      c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wa
      com con0 vy com vy cv cF cfv cmpt wf vy com vy cv cF cfv cmpt cdm com
      wceq c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral
      wa vy cv cF cfv con0 wcel vy com wral com con0 vy com vy cv cF cfv cmpt
      wf c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wa
      vy cv cF cfv con0 wcel vy com vy cv com wcel c0 cF cfv con0 wcel vx cv
      csuc cF cfv vx cv cF cfv wcel vx com wral wa vy cv cF cfv con0 wcel vy cv
      cF cfv con0 wcel c0 cF cfv con0 wcel vz cv cF cfv con0 wcel vz cv csuc cF
      cfv con0 wcel c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx
      com wral wa vy vz vy cv c0 wceq vy cv cF cfv c0 cF cfv con0 vy cv c0 cF
      fveq2 eleq1d vy cv vz cv wceq vy cv cF cfv vz cv cF cfv con0 vy cv vz cv
      cF fveq2 eleq1d vy cv vz cv csuc wceq vy cv cF cfv vz cv csuc cF cfv con0
      vy cv vz cv csuc cF fveq2 eleq1d c0 cF cfv con0 wcel vx cv csuc cF cfv vx
      cv cF cfv wcel vx com wral simpl vz cv com wcel vx cv csuc cF cfv vx cv
      cF cfv wcel vx com wral vz cv cF cfv con0 wcel vz cv csuc cF cfv con0
      wcel wi c0 cF cfv con0 wcel vz cv com wcel vx cv csuc cF cfv vx cv cF cfv
      wcel vx com wral vz cv csuc cF cfv vz cv cF cfv wcel vz cv cF cfv con0
      wcel vz cv csuc cF cfv con0 wcel wi vx cv csuc cF cfv vx cv cF cfv wcel
      vz cv csuc cF cfv vz cv cF cfv wcel vx vz cv com vx cv vz cv wceq vx cv
      csuc cF cfv vz cv csuc cF cfv vx cv cF cfv vz cv cF cfv vx cv vz cv wceq
      vx cv csuc vz cv csuc cF vx cv vz cv suceq fveq2d vx cv vz cv cF fveq2
      eleq12d rspcv vz cv cF cfv con0 wcel vz cv csuc cF cfv vz cv cF cfv wcel
      vz cv csuc cF cfv con0 wcel vz cv cF cfv vz cv csuc cF cfv onelon expcom
      syl6 adantld finds2 com12 ralrimiv vy com con0 vy cv cF cfv vy com vy cv
      cF cfv cmpt vy com vy cv cF cfv cmpt eqid fmpt sylib com con0 vy com vy
      cv cF cfv cmpt fdm syl syl5eleqr vy com vy cv cF cfv cmpt cdm c0 ne0i syl
      vy com vy cv cF cfv cmpt cdm c0 vy com vy cv cF cfv cmpt crn c0 vy com vy
      cv cF cfv cmpt dm0rn0 necon3bii sylib vz con0 vy com vy cv cF cfv cmpt
      crn wefrc syl3anc vw cv cF cfv cvv wcel vw com wral vy com vy cv cF cfv
      cmpt crn vz cv cin c0 wceq vz vy com vy cv cF cfv cmpt crn wrex vy com vy
      cv cF cfv cmpt crn vw cv cF cfv cin c0 wceq vw com wrex wb vw cv cF cfv
      cvv wcel vw com vw cv cF fvex rgenw vy com vy cv cF cfv cmpt crn vz cv
      cin c0 wceq vy com vy cv cF cfv cmpt crn vw cv cF cfv cin c0 wceq vw vz
      com vw cv cF cfv vy com vy cv cF cfv cmpt cvv vy vw com vy cv cF cfv vw
      cv cF cfv vy cv vw cv cF fveq2 cbvmptv vz cv vw cv cF cfv wceq vy com vy
      cv cF cfv cmpt crn vz cv cin vy com vy cv cF cfv cmpt crn vw cv cF cfv
      cin c0 vz cv vw cv cF cfv vy com vy cv cF cfv cmpt crn ineq2 eqeq1d
      rexrnmpt ax-mp sylib c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv
      wcel vx com wral wa vy com vy cv cF cfv cmpt crn vw cv cF cfv cin c0 wceq
      vw com c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com
      wral wa vw cv com wcel wa vy com vy cv cF cfv cmpt crn vw cv cF cfv cin
      c0 c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wa
      vw cv com wcel wa vw cv csuc cF cfv vy com vy cv cF cfv cmpt crn wcel vw
      cv csuc cF cfv vw cv cF cfv wcel vy com vy cv cF cfv cmpt crn vw cv cF
      cfv cin c0 wne c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx
      com wral wa vw cv com wcel wa vw cv csuc cF cfv vy cv cF cfv wceq vy com
      wrex vw cv csuc cF cfv vy com vy cv cF cfv cmpt crn wcel c0 cF cfv con0
      wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wa vw cv com wcel wa
      vw cv csuc com wcel vw cv csuc cF cfv vw cv csuc cF cfv wceq vw cv csuc
      cF cfv vy cv cF cfv wceq vy com wrex vw cv com wcel vw cv csuc com wcel
      c0 cF cfv con0 wcel vx cv csuc cF cfv vx cv cF cfv wcel vx com wral wa vw
      cv peano2 adantl vw cv csuc cF cfv eqid vw cv csuc cF cfv vy cv cF cfv
      wceq vw cv csuc cF cfv vw cv csuc cF cfv wceq vy vw cv csuc com vy cv vw
      cv csuc wceq vy cv cF cfv vw cv csuc cF cfv vw cv csuc cF cfv vy cv vw cv
      csuc cF fveq2 eqeq2d rspcev sylancl vw cv csuc cF cfv cvv wcel vw cv csuc
      cF cfv vy com vy cv cF cfv cmpt crn wcel vw cv csuc cF cfv vy cv cF cfv
      wceq vy com wrex wb vw cv csuc cF fvex vy com vy cv cF cfv vw cv csuc cF
      cfv vy com vy cv cF cfv cmpt cvv vy com vy cv cF cfv cmpt eqid elrnmpt
      ax-mp sylibr vx cv csuc cF cfv vx cv cF cfv wcel vx com wral vw cv com
      wcel vw cv csuc cF cfv vw cv cF cfv wcel c0 cF cfv con0 wcel vx cv csuc
      cF cfv vx cv cF cfv wcel vw cv csuc cF cfv vw cv cF cfv wcel vx vw cv com
      vx cv vw cv wceq vx cv csuc cF cfv vw cv csuc cF cfv vx cv cF cfv vw cv
      cF cfv vx cv vw cv wceq vx cv csuc vw cv csuc cF vx cv vw cv suceq fveq2d
      vx cv vw cv cF fveq2 eleq12d rspccva adantll vw cv csuc cF cfv vy com vy
      cv cF cfv cmpt crn vw cv cF cfv inelcm syl2anc neneqd nrexdv pm2.65da vx
      cv csuc cF cfv vx cv cF cfv wcel vx com rexnal sylibr $.
  $}

  $c Smo $.

  $( Introduce the strictly monotone ordinal function.  A strictly monotone
     function is one that is constantly increasing across the ordinals. $)
  wsmo $a wff Smo A $.

  ${
    $d x y A $.
    $( Definition of a strictly monotone ordinal function.  Definition 7.46 in
       [TakeutiZaring] p. 50.  (Contributed by Andrew Salmon, 15-Nov-2011.) $)
    df-smo $a |- ( Smo A <-> ( A : dom A --> On /\ Ord dom A /\ A. x e. dom A
       A. y e. dom A ( x e. y -> ( A ` x ) e. ( A ` y ) ) ) ) $.
  $}

  ${
    $d F x y $.
    $( Alternate definition of a strictly monotone ordinal function.
       (Contributed by Mario Carneiro, 4-Mar-2013.) $)
    dfsmo2 $p |- ( Smo F <-> ( F : dom F --> On /\ Ord dom F /\ A. x e. dom F
       A. y e. x ( F ` y ) e. ( F ` x ) ) ) $=
      cF wsmo cF cdm con0 cF wf cF cdm word vy vx wel vy cv cF cfv vx cv cF cfv
      wcel wi vx cF cdm wral vy cF cdm wral w3a cF cdm con0 cF wf cF cdm word
      vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral w3a vy vx cF
      df-smo cF cdm con0 cF wf cF cdm word vy vx wel vy cv cF cfv vx cv cF cfv
      wcel wi vx cF cdm wral vy cF cdm wral wa wa cF cdm con0 cF wf cF cdm word
      vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral wa wa cF cdm
      con0 cF wf cF cdm word vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vx cF
      cdm wral vy cF cdm wral w3a cF cdm con0 cF wf cF cdm word vy cv cF cfv vx
      cv cF cfv wcel vy vx cv wral vx cF cdm wral w3a cF cdm word vy vx wel vy
      cv cF cfv vx cv cF cfv wcel wi vx cF cdm wral vy cF cdm wral wa cF cdm
      word vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral wa cF
      cdm con0 cF wf cF cdm word vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vx
      cF cdm wral vy cF cdm wral vy cv cF cfv vx cv cF cfv wcel vy vx cv wral
      vx cF cdm wral vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vx cF cdm wral
      vy cF cdm wral vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vy cF cdm wral
      vx cF cdm wral cF cdm word vy cv cF cfv vx cv cF cfv wcel vy vx cv wral
      vx cF cdm wral vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vy vx cF cdm
      cF cdm ralcom cF cdm word vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vy
      cF cdm wral vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm cF cdm
      word vx cv cF cdm wcel wa vy vx wel vy cv cF cfv vx cv cF cfv wcel wi vy
      cv cF cfv vx cv cF cfv wcel vy cF cdm vx cv vy cv cF cdm wcel vy vx wel
      vy cv cF cfv vx cv cF cfv wcel wi wi vy cv cF cdm wcel vy vx wel wa vy cv
      cF cfv vx cv cF cfv wcel wi cF cdm word vx cv cF cdm wcel wa vy vx wel vy
      cv cF cfv vx cv cF cfv wcel wi vy cv cF cdm wcel vy vx wel vy cv cF cfv
      vx cv cF cfv wcel impexp cF cdm word vx cv cF cdm wcel wa vy cv cF cdm
      wcel vy vx wel wa vy vx wel vy cv cF cfv vx cv cF cfv wcel cF cdm word vx
      cv cF cdm wcel wa vy cv cF cdm wcel vy vx wel wa vy vx wel vy cv cF cdm
      wcel vy vx wel simpr cF cdm word vx cv cF cdm wcel vy vx wel vy cv cF cdm
      wcel vy vx wel wa cF cdm word vx cv cF cdm wcel vy vx wel w3a vy cv cF
      cdm wcel vy vx wel cF cdm word vy vx wel vx cv cF cdm wcel vy cv cF cdm
      wcel cF cdm word vy vx wel vx cv cF cdm wcel vy cv cF cdm wcel vy cv vx
      cv cF cdm ordtr1 3impib 3com23 cF cdm word vx cv cF cdm wcel vy vx wel
      simp3 jca 3expia impbid2 imbi1d syl5bbr ralbidv2 ralbidva syl5bb pm5.32i
      anbi2i cF cdm con0 cF wf cF cdm word vy vx wel vy cv cF cfv vx cv cF cfv
      wcel wi vx cF cdm wral vy cF cdm wral 3anass cF cdm con0 cF wf cF cdm
      word vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral 3anass
      3bitr4i bitri $.
  $}

  ${
    $d x y A $.
    issmo.1 $e |- A : B --> On $.
    issmo.2 $e |- Ord B $.
    issmo.3 $e |- ( ( x e. B /\ y e. B ) -> ( x e. y -> ( A ` x ) e. ( A ` y
       ) ) ) $.
    issmo.4 $e |- dom A = B $.
    $( Conditions for which ` A ` is a strictly monotone ordinal function.
       (Contributed by Andrew Salmon, 15-Nov-2011.) $)
    issmo $p |- Smo A $=
      cA wsmo cA cdm con0 cA wf cA cdm word vx cv vy cv wcel vx cv cA cfv vy cv
      cA cfv wcel wi vy cA cdm wral vx cA cdm wral cA cdm con0 cA wf cB con0 cA
      wf issmo.1 cA cdm cB con0 cA issmo.4 feq2i mpbir cA cdm word cB word
      issmo.2 cA cdm cB wceq cA cdm word cB word wb issmo.4 cA cdm cB ordeq
      ax-mp mpbir vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vx vy cA
      cdm vx cv cA cdm wcel vx cv cB wcel vy cv cB wcel vx cv vy cv wcel vx cv
      cA cfv vy cv cA cfv wcel wi vy cv cA cdm wcel cA cdm cB vx cv issmo.4
      eleq2i cA cdm cB vy cv issmo.4 eleq2i issmo.3 syl2anb rgen2a vx vy cA
      df-smo mpbir3an $.
  $}

  ${
    $d A x $.  $d F x y $.
    $( Alternative definition of a strictly monotone ordinal function.
       (Contributed by Mario Carneiro, 12-Mar-2013.) $)
    issmo2 $p |- ( F : A --> B -> ( ( B C_ On /\ Ord A /\
       A. x e. A A. y e. x ( F ` y ) e. ( F ` x ) ) -> Smo F ) ) $=
      cA cB cF wf cB con0 wss cA word vy cv cF cfv vx cv cF cfv wcel vy vx cv
      wral vx cA wral w3a cF cdm con0 cF wf cF cdm word vy cv cF cfv vx cv cF
      cfv wcel vy vx cv wral vx cF cdm wral w3a cF wsmo cA cB cF wf cB con0 wss
      cF cdm con0 cF wf cA word cF cdm word vy cv cF cfv vx cv cF cfv wcel vy
      vx cv wral vx cA wral vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF
      cdm wral cA cB cF wf cB con0 wss cA con0 cF wf cF cdm con0 cF wf cA cB cF
      wf cB con0 wss cA con0 cF wf cA cB con0 cF fss ex cA cB cF wf cF cdm cA
      con0 cF cA cB cF fdm feq2d sylibrd cA cB cF wf cF cdm word cA word cA cB
      cF wf cF cdm cA wceq cF cdm word cA word wb cA cB cF fdm cF cdm cA ordeq
      syl biimprd cA cB cF wf vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx
      cF cdm wral vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cA wral cA cB
      cF wf vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm cA cA cB cF
      fdm raleqdv biimprd 3anim123d vx vy cF dfsmo2 syl6ibr $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Equality theorem for strictly monotone functions.  (Contributed by
       Andrew Salmon, 16-Nov-2011.) $)
    smoeq $p |- ( A = B -> ( Smo A <-> Smo B ) ) $=
      cA cB wceq cA cdm con0 cA wf cA cdm word vx cv vy cv wcel vx cv cA cfv vy
      cv cA cfv wcel wi vy cA cdm wral vx cA cdm wral w3a cB cdm con0 cB wf cB
      cdm word vx cv vy cv wcel vx cv cB cfv vy cv cB cfv wcel wi vy cB cdm
      wral vx cB cdm wral w3a cA wsmo cB wsmo cA cB wceq cA cdm con0 cA wf cB
      cdm con0 cB wf cA cdm word cB cdm word vx cv vy cv wcel vx cv cA cfv vy
      cv cA cfv wcel wi vy cA cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cB
      cfv vy cv cB cfv wcel wi vy cB cdm wral vx cB cdm wral cA cB wceq cA cdm
      cB cdm con0 cA cB cA cB wceq id cA cB dmeq feq12d cA cB wceq cA cdm cB
      cdm wceq cA cdm word cB cdm word wb cA cB dmeq cA cdm cB cdm ordeq syl cA
      cB wceq vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cdm wral
      vx cA cdm wral vx cv vy cv wcel vx cv cB cfv vy cv cB cfv wcel wi vy cA
      cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cB cfv vy cv cB cfv wcel
      wi vy cB cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cB cfv vy cv cB
      cfv wcel wi vy cB cdm wral vx cB cdm wral cA cB wceq vx cv vy cv wcel vx
      cv cA cfv vy cv cA cfv wcel wi vx cv vy cv wcel vx cv cB cfv vy cv cB cfv
      wcel wi vx vy cA cdm cA cdm cA cB wceq vx cv cA cfv vy cv cA cfv wcel vx
      cv cB cfv vy cv cB cfv wcel vx cv vy cv wcel cA cB wceq vx cv cA cfv vx
      cv cB cfv vy cv cA cfv vy cv cB cfv vx cv cA cB fveq1 vy cv cA cB fveq1
      eleq12d imbi2d 2ralbidv cA cB wceq vx cv vy cv wcel vx cv cB cfv vy cv cB
      cfv wcel wi vy cA cdm wral vx cv vy cv wcel vx cv cB cfv vy cv cB cfv
      wcel wi vy cB cdm wral vx cA cdm cA cB wceq vx cv vy cv wcel vx cv cB cfv
      vy cv cB cfv wcel wi vy cA cdm cB cdm cA cB dmeq raleqdv ralbidv cA cB
      wceq vx cv vy cv wcel vx cv cB cfv vy cv cB cfv wcel wi vy cB cdm wral vx
      cA cdm cB cdm cA cB dmeq raleqdv 3bitrd 3anbi123d vx vy cA df-smo vx vy
      cB df-smo 3bitr4g $.

    $( The domain of a strictly monotone function is an ordinal.  (Contributed
       by Andrew Salmon, 16-Nov-2011.) $)
    smodm $p |- ( Smo A -> Ord dom A ) $=
      cA wsmo cA cdm con0 cA wf cA cdm word vx cv vy cv wcel vx cv cA cfv vy cv
      cA cfv wcel wi vy cA cdm wral vx cA cdm wral vx vy cA df-smo simp2bi $.

    $( A strictly monotone function restricted to an ordinal remains strictly
       monotone.  (Contributed by Andrew Salmon, 16-Nov-2011.)  (Proof
       shortened by Mario Carneiro, 5-Dec-2016.) $)
    smores $p |- ( ( Smo A /\ B e. dom A ) -> Smo ( A |` B ) ) $=
      cB cA cdm wcel cA wsmo cA cB cres wsmo cB cA cdm wcel cA cdm con0 cA wf
      cA cdm word vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cdm
      wral vx cA cdm wral w3a cA cB cres cdm con0 cA cB cres wf cA cB cres cdm
      word vx cv vy cv wcel vx cv cA cB cres cfv vy cv cA cB cres cfv wcel wi
      vy cA cB cres cdm wral vx cA cB cres cdm wral w3a cA wsmo cA cB cres wsmo
      cB cA cdm wcel cA cdm con0 cA wf cA cB cres cdm con0 cA cB cres wf cA cdm
      word cA cB cres cdm word vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel
      wi vy cA cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cA cB cres cfv vy
      cv cA cB cres cfv wcel wi vy cA cB cres cdm wral vx cA cB cres cdm wral
      cA cdm con0 cA wf cA cB cres cdm con0 cA cB cres wf wi cB cA cdm wcel cA
      cA cdm wfn cA crn con0 wss wa cA cB cres cA cB cres cdm wfn cA cB cres
      crn con0 wss wa cA cdm con0 cA wf cA cB cres cdm con0 cA cB cres wf cA cA
      cdm wfn cA cB cres cA cB cres cdm wfn cA crn con0 wss cA cB cres crn con0
      wss cA wfun cA cB cres wfun cA cA cdm wfn cA cB cres cA cB cres cdm wfn
      cB cA funres cA funfn cA cB cres funfn 3imtr3i cA cB cres crn cA crn wss
      cA crn con0 wss cA cB cres crn con0 wss cA cB cres cA wss cA cB cres crn
      cA crn wss cA cB resss cA cB cres cA rnss ax-mp cA cB cres crn cA crn
      con0 sstr mpan anim12i cA cdm con0 cA df-f cA cB cres cdm con0 cA cB cres
      df-f 3imtr4i a1i cB cA cdm wcel cA cdm word cB cA cdm cin word cA cB cres
      cdm word cA cdm word cB cA cdm wcel cB word cB cA cdm cin word cA cdm
      word cB cA cdm wcel cB word cA cdm cB ordelord expcom cB word cA cdm word
      cB cA cdm cin word cB cA cdm ordin ex syli cA cB cres cdm cB cA cdm cin
      wceq cA cB cres cdm word cB cA cdm cin word wb cA cB dmres cA cB cres cdm
      cB cA cdm cin ordeq ax-mp syl6ibr vx cv vy cv wcel vx cv cA cfv vy cv cA
      cfv wcel wi vy cA cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cA cB
      cres cfv vy cv cA cB cres cfv wcel wi vy cA cB cres cdm wral vx cA cB
      cres cdm wral wi cB cA cdm wcel vx cv vy cv wcel vx cv cA cfv vy cv cA
      cfv wcel wi vy cA cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cA cfv
      vy cv cA cfv wcel wi vy cA cB cres cdm wral vx cA cB cres cdm wral vx cv
      vy cv wcel vx cv cA cB cres cfv vy cv cA cB cres cfv wcel wi vy cA cB
      cres cdm wral vx cA cB cres cdm wral vx cv vy cv wcel vx cv cA cfv vy cv
      cA cfv wcel wi vy cA cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cA
      cfv vy cv cA cfv wcel wi vy cA cdm wral vx cA cB cres cdm wral vx cv vy
      cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cB cres cdm wral vx cA cB
      cres cdm wral cA cB cres cdm cA cdm wss vx cv vy cv wcel vx cv cA cfv vy
      cv cA cfv wcel wi vy cA cdm wral vx cA cdm wral vx cv vy cv wcel vx cv cA
      cfv vy cv cA cfv wcel wi vy cA cdm wral vx cA cB cres cdm wral wi cA cB
      cres cA wss cA cB cres cdm cA cdm wss cA cB resss cA cB cres cA dmss
      ax-mp vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cdm wral
      vx cA cB cres cdm cA cdm ssralv ax-mp vx cv vy cv wcel vx cv cA cfv vy cv
      cA cfv wcel wi vy cA cdm wral vx cv vy cv wcel vx cv cA cfv vy cv cA cfv
      wcel wi vy cA cB cres cdm wral vx cA cB cres cdm cA cB cres cdm cA cdm
      wss vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cdm wral vx
      cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cB cres cdm wral wi
      cA cB cres cA wss cA cB cres cdm cA cdm wss cA cB resss cA cB cres cA
      dmss ax-mp vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi vy cA cB
      cres cdm cA cdm ssralv ax-mp ralimi syl vx cv vy cv wcel vx cv cA cB cres
      cfv vy cv cA cB cres cfv wcel wi vy cA cB cres cdm wral vx cv vy cv wcel
      vx cv cA cfv vy cv cA cfv wcel wi vy cA cB cres cdm wral vx cA cB cres
      cdm vx cv cA cB cres cdm wcel vx cv vy cv wcel vx cv cA cB cres cfv vy cv
      cA cB cres cfv wcel wi vx cv vy cv wcel vx cv cA cfv vy cv cA cfv wcel wi
      vy cA cB cres cdm vx cv cA cB cres cdm wcel vy cv cA cB cres cdm wcel wa
      vx cv cA cB cres cfv vy cv cA cB cres cfv wcel vx cv cA cfv vy cv cA cfv
      wcel vx cv vy cv wcel vx cv cA cB cres cdm wcel vy cv cA cB cres cdm wcel
      wa vx cv cA cB cres cfv vx cv cA cfv vy cv cA cB cres cfv vy cv cA cfv vx
      cv cA cB cres cdm wcel vy cv cA cB cres cdm wcel wa vx cv cB wcel vx cv
      cA cB cres cfv vx cv cA cfv wceq vx cv cA cB cres cdm wcel vy cv cA cB
      cres cdm wcel wa cA cB cres cdm cB vx cv cA cB cres cdm cB cA cdm cin cB
      cA cB dmres cB cA cdm inss1 eqsstri vx cv cA cB cres cdm wcel vy cv cA cB
      cres cdm wcel simpl sseldi vx cv cB cA fvres syl vx cv cA cB cres cdm
      wcel vy cv cA cB cres cdm wcel wa vy cv cB wcel vy cv cA cB cres cfv vy
      cv cA cfv wceq vx cv cA cB cres cdm wcel vy cv cA cB cres cdm wcel wa cA
      cB cres cdm cB vy cv cA cB cres cdm cB cA cdm cin cB cA cB dmres cB cA
      cdm inss1 eqsstri vx cv cA cB cres cdm wcel vy cv cA cB cres cdm wcel
      simpr sseldi vy cv cB cA fvres syl eleq12d imbi2d ralbidva ralbiia sylibr
      a1i 3anim123d vx vy cA df-smo vx vy cA cB cres df-smo 3imtr4g impcom $.

    $( A strictly monotone function restricted to an ordinal remains strictly
       monotone.  (Contributed by Andrew Salmon, 19-Nov-2011.) $)
    smores3 $p |- ( ( Smo ( A |` B ) /\ C e. ( dom A i^i B ) /\ Ord B ) -> Smo
       ( A |` C ) ) $=
      cA cB cres wsmo cC cA cdm cB cin wcel cB word w3a cA cB cres cC cres wsmo
      cA cC cres wsmo cA cB cres wsmo cC cA cdm cB cin wcel cA cB cres cC cres
      wsmo cB word cC cA cdm cB cin wcel cA cB cres wsmo cC cA cB cres cdm wcel
      cA cB cres cC cres wsmo cA cB cres cdm cA cdm cB cin cC cA cB cres cdm cB
      cA cdm cin cA cdm cB cin cA cB dmres cB cA cdm incom eqtri eleq2i cA cB
      cres cC smores sylan2br 3adant3 cA cB cres wsmo cC cA cdm cB cin wcel cB
      word w3a cC cB wss cA cB cres cC cres cA cC cres wceq cA cB cres cC cres
      wsmo cA cC cres wsmo wb cC cA cdm cB cin wcel cB word cC cB wss cA cB
      cres wsmo cC cA cdm cB cin wcel cC cB wcel cB word cC cB wss cA cdm cB
      cin cB cC cA cdm cB inss2 sseli cB word cC cB wcel cC cB wss cB cC
      ordelss ancoms sylan 3adant1 cA cC cB resabs1 cA cB cres cC cres cA cC
      cres smoeq 3syl mpbid $.
  $}

  ${
    $d A x y $.  $d F x y $.
    $( A strictly monotone ordinal function restricted to an ordinal is still
       monotone.  (Contributed by Mario Carneiro, 15-Mar-2013.) $)
    smores2 $p |- ( ( Smo F /\ Ord A ) -> Smo ( F |` A ) ) $=
      cF wsmo cA word wa cF cA cres cdm con0 cF cA cres wf cF cA cres cdm word
      vy cv cF cA cres cfv vx cv cF cA cres cfv wcel vy vx cv wral vx cF cA
      cres cdm wral cF cA cres wsmo cF wsmo cF cA cres cdm con0 cF cA cres wf
      cA word cF wsmo cF cA cres cF cA cres cdm wfn cF cA cres crn con0 wss cF
      cA cres cdm con0 cF cA cres wf cF wsmo cF wfun cF cA cres cF cA cres cdm
      wfn cF wsmo cF cdm con0 cF wf cF wfun cF wsmo cF cdm con0 cF wf cF cdm
      word vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral vx vy cF
      dfsmo2 simp1bi cF cdm con0 cF ffun syl cF wfun cF cA cres wfun cF cA cres
      cF cA cres cdm wfn cA cF funres cF cA cres funfn sylib syl cF wsmo cF cA
      cres crn cF crn con0 cF cA cres crn cF cA cima cF crn cF cA df-ima cF cA
      imassrn eqsstr3i cF wsmo cF cdm con0 cF wf cF crn con0 wss cF wsmo cF cdm
      con0 cF wf cF cdm word vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF
      cdm wral vx vy cF dfsmo2 simp1bi cF cdm con0 cF frn syl syl5ss cF cA cres
      cdm con0 cF cA cres df-f sylanbrc adantr cF wsmo cF cdm word cA word cF
      cA cres cdm word cF smodm cA word cF cdm word cF cA cres cdm word cA word
      cF cdm word wa cA cF cdm cin word cF cA cres cdm word cA cF cdm ordin cF
      cA cres cdm cA cF cdm cin wceq cF cA cres cdm word cA cF cdm cin word wb
      cF cA dmres cF cA cres cdm cA cF cdm cin ordeq ax-mp sylibr ancoms sylan
      cF wsmo cA word wa vy cv cF cA cres cfv vx cv cF cA cres cfv wcel vy vx
      cv wral vx cF cA cres cdm wral vy cv cF cfv vx cv cF cfv wcel vy vx cv
      wral vx cF cA cres cdm wral cF wsmo vy cv cF cfv vx cv cF cfv wcel vy vx
      cv wral vx cF cA cres cdm wral cA word cF cA cres cdm cF cdm wss cF wsmo
      vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral vy cv cF cfv
      vx cv cF cfv wcel vy vx cv wral vx cF cA cres cdm wral cF cA cres cF wss
      cF cA cres cdm cF cdm wss cF cA resss cF cA cres cF dmss ax-mp cF wsmo cF
      cdm con0 cF wf cF cdm word vy cv cF cfv vx cv cF cfv wcel vy vx cv wral
      vx cF cdm wral vx vy cF dfsmo2 simp3bi vy cv cF cfv vx cv cF cfv wcel vy
      vx cv wral vx cF cA cres cdm cF cdm ssralv mpsyl adantr cF wsmo cA word
      wa vy cv cF cA cres cfv vx cv cF cA cres cfv wcel vy vx cv wral vy cv cF
      cfv vx cv cF cfv wcel vy vx cv wral vx cF cA cres cdm cF wsmo cA word wa
      vx cv cF cA cres cdm wcel wa vy cv cF cA cres cfv vx cv cF cA cres cfv
      wcel vy cv cF cfv vx cv cF cfv wcel vy vx cv cF wsmo cA word wa vx cv cF
      cA cres cdm wcel wa vy vx wel wa vy cv cF cA cres cfv vy cv cF cfv vx cv
      cF cA cres cfv vx cv cF cfv cF wsmo cA word wa vx cv cF cA cres cdm wcel
      wa vy vx wel wa vy cv cA wcel vy cv cF cA cres cfv vy cv cF cfv wceq cF
      wsmo cA word wa vx cv cF cA cres cdm wcel vy vx wel vy cv cA wcel cF wsmo
      cA word wa vy vx wel vx cv cF cA cres cdm wcel vy cv cA wcel cF wsmo cA
      word wa vy vx wel vx cv cF cA cres cdm wcel wa vy cv cF cA cres cdm wcel
      vy cv cA wcel cF wsmo cA word wa cF cA cres cdm word vy vx wel vx cv cF
      cA cres cdm wcel wa vy cv cF cA cres cdm wcel wi cF wsmo cF cdm word cA
      word cF cA cres cdm word cF smodm cA word cF cdm word cF cA cres cdm word
      cA word cF cdm word wa cA cF cdm cin word cF cA cres cdm word cA cF cdm
      ordin cF cA cres cdm cA cF cdm cin wceq cF cA cres cdm word cA cF cdm cin
      word wb cF cA dmres cF cA cres cdm cA cF cdm cin ordeq ax-mp sylibr
      ancoms sylan vy cv vx cv cF cA cres cdm ordtr1 syl cF cA cres cdm cA vy
      cv cF cA cres cdm cA cF cdm cin cA cF cA dmres cA cF cdm inss1 eqsstri
      sseli syl6 exp3acom23 imp31 vy cv cA cF fvres syl vx cv cF cA cres cdm
      wcel vx cv cF cA cres cfv vx cv cF cfv wceq cF wsmo cA word wa vy vx wel
      vx cv cF cA cres cdm wcel vx cv cA wcel vx cv cF cA cres cfv vx cv cF cfv
      wceq cF cA cres cdm cA vx cv cF cA cres cdm cA cF cdm cin cA cF cA dmres
      cA cF cdm inss1 eqsstri sseli vx cv cA cF fvres syl ad2antlr eleq12d
      ralbidva ralbidva mpbird vx vy cF cA cres dfsmo2 syl3anbrc $.
  $}

  $( The domain of a strictly monotone ordinal function is an ordinal.
     (Contributed by Mario Carneiro, 12-Mar-2013.) $)
  smodm2 $p |- ( ( F Fn A /\ Smo F ) -> Ord A ) $=
    cF wsmo cF cA wfn cF cdm word cA word cF smodm cF cA wfn cF cdm word cA
    word cF cA wfn cF cdm cA wceq cF cdm word cA word wb cA cF fndm cF cdm cA
    ordeq syl biimpa sylan2 $.

  ${
    $d F x y $.
    $( The function values of a strictly monotone ordinal function are
       ordinals.  (Contributed by Mario Carneiro, 12-Mar-2013.) $)
    smofvon2 $p |- ( Smo F -> ( F ` B ) e. On ) $=
      cB cF cdm wcel cF wsmo cB cF cfv con0 wcel wi cF wsmo cF cdm con0 cF wf
      cB cF cdm wcel cB cF cfv con0 wcel cF wsmo cF cdm con0 cF wf cF cdm word
      vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cF cdm wral vx vy cF
      dfsmo2 simp1bi cF cdm con0 cF wf cB cF cdm wcel cB cF cfv con0 wcel cF
      cdm con0 cB cF ffvelrn expcom syl5 cB cF cdm wcel wn cB cF cfv con0 wcel
      cF wsmo cB cF cdm wcel wn cB cF cfv c0 con0 cB cF ndmfv 0elon syl6eqel
      a1d pm2.61i $.
  $}

  ${
    $d x y A $.
    iordsmo.1 $e |- Ord A $.
    $( The identity relation restricted to the ordinals is a strictly monotone
       function.  (Contributed by Andrew Salmon, 16-Nov-2011.) $)
    iordsmo $p |- Smo ( _I |` A ) $=
      vx vy cid cA cres cA cA con0 cid cA cres wf cid cA cres cA wfn cid cA
      cres crn con0 wss cA fnresi cid cA cres crn cA con0 cA rnresi cA word cA
      con0 wss iordsmo.1 cA ordsson ax-mp eqsstri cA con0 cid cA cres df-f
      mpbir2an iordsmo.1 vx cv cA wcel vy cv cA wcel wa vx cv cid cA cres cfv
      vy cv cid cA cres cfv wcel vx cv vy cv wcel vx cv cA wcel vy cv cA wcel
      wa vx cv cid cA cres cfv vx cv vy cv cid cA cres cfv vy cv vx cv cA wcel
      vx cv cid cA cres cfv vx cv wceq vy cv cA wcel cA vx cv fvresi adantr vy
      cv cA wcel vy cv cid cA cres cfv vy cv wceq vx cv cA wcel cA vy cv fvresi
      adantl eleq12d biimprd cA dmresi issmo $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y F $.
    $( The null set is a strictly monotone ordinal function.  (Contributed by
       Andrew Salmon, 20-Nov-2011.) $)
    smo0 $p |- Smo (/) $=
      cid c0 cres wsmo c0 wsmo c0 ord0 iordsmo cid c0 cres c0 wceq cid c0 cres
      wsmo c0 wsmo wb cid res0 cid c0 cres c0 smoeq ax-mp mpbi $.

    $( If ` B ` is a strictly monotone ordinal function, and ` A ` is in the
       domain of ` B ` , then the value of the function at ` A ` is an
       ordinal.  (Contributed by Andrew Salmon, 20-Nov-2011.) $)
    smofvon $p |- ( ( Smo B /\ A e. dom B ) -> ( B ` A ) e. On ) $=
      cB wsmo cB cdm con0 cB wf cA cB cdm wcel cA cB cfv con0 wcel cB wsmo cB
      cdm con0 cB wf cB cdm word vx cv vy cv wcel vx cv cB cfv vy cv cB cfv
      wcel wi vy cB cdm wral vx cB cdm wral vx vy cB df-smo simp1bi cB cdm con0
      cA cB ffvelrn sylan $.

    $( If ` x ` is less than ` y ` then a strictly monotone function's value
       will be strictly less at ` x ` than at ` y ` .  (Contributed by Andrew
       Salmon, 22-Nov-2011.) $)
    smoel $p |- ( ( Smo B /\ A e. dom B /\ C e. A ) -> ( B ` C ) e. ( B ` A )
       ) $=
      cB wsmo cA cB cdm wcel cC cA wcel cC cB cfv cA cB cfv wcel cB wsmo cA cB
      cdm wcel wa cC cA wcel cC cB cfv cA cB cfv wcel cB wsmo cA cB cdm wcel wa
      cC cA wcel cC cB cdm wcel cC cA wcel cC cB cfv cA cB cfv wcel wi cB wsmo
      cB cdm word cA cB cdm wcel cC cA wcel cC cB cdm wcel wi cB smodm cB cdm
      word cA cB cdm wcel cC cA wcel cC cB cdm wcel cB cdm word cC cA wcel cA
      cB cdm wcel cC cB cdm wcel cC cA cB cdm ordtr1 ancomsd expdimp sylan cB
      wsmo cA cB cdm wcel cC cB cdm wcel cC cA wcel cC cB cfv cA cB cfv wcel wi
      cB wsmo cB cdm con0 cB wf cB cdm word vx cv vy cv wcel vx cv cB cfv vy cv
      cB cfv wcel wi vy cB cdm wral vx cB cdm wral w3a cA cB cdm wcel cC cB cdm
      wcel wa cC cA wcel cC cB cfv cA cB cfv wcel wi wi vx vy cB df-smo vx cv
      vy cv wcel vx cv cB cfv vy cv cB cfv wcel wi vy cB cdm wral vx cB cdm
      wral cB cdm con0 cB wf cA cB cdm wcel cC cB cdm wcel wa cC cA wcel cC cB
      cfv cA cB cfv wcel wi wi cB cdm word cA cB cdm wcel cC cB cdm wcel wa vx
      cv vy cv wcel vx cv cB cfv vy cv cB cfv wcel wi vy cB cdm wral vx cB cdm
      wral cC cA wcel cC cB cfv cA cB cfv wcel wi cC cB cdm wcel cA cB cdm wcel
      vx cv vy cv wcel vx cv cB cfv vy cv cB cfv wcel wi vy cB cdm wral vx cB
      cdm wral cC cA wcel cC cB cfv cA cB cfv wcel wi wi vx cv vy cv wcel vx cv
      cB cfv vy cv cB cfv wcel wi cC cA wcel cC cB cfv cA cB cfv wcel wi cC vy
      cv wcel cC cB cfv vy cv cB cfv wcel wi vx vy cC cA cB cdm cB cdm vx cv cC
      wceq vx cv vy cv wcel cC vy cv wcel vx cv cB cfv vy cv cB cfv wcel cC cB
      cfv vy cv cB cfv wcel vx cv cC vy cv eleq1 vx cv cC wceq vx cv cB cfv cC
      cB cfv vy cv cB cfv vx cv cC cB fveq2 eleq1d imbi12d vy cv cA wceq cC vy
      cv wcel cC cA wcel cC cB cfv vy cv cB cfv wcel cC cB cfv cA cB cfv wcel
      vy cv cA cC eleq2 vy cv cA wceq vy cv cB cfv cA cB cfv cC cB cfv vy cv cA
      cB fveq2 eleq2d imbi12d rspc2v ancoms com12 3ad2ant3 sylbi expdimp syld
      pm2.43d 3impia $.

    $( The value of a strictly monotone ordinal function contains its indexed
       union.  (Contributed by Andrew Salmon, 22-Nov-2011.) $)
    smoiun $p |- ( ( Smo B /\ A e. dom B ) -> U_ x e. A ( B ` x )
       C_ ( B ` A ) ) $=
      cB wsmo cA cB cdm wcel wa vy vx cA vx cv cB cfv ciun cA cB cfv vy cv vx
      cA vx cv cB cfv ciun wcel vy cv vx cv cB cfv wcel vx cA wrex cB wsmo cA
      cB cdm wcel wa vy cv cA cB cfv wcel vx vy cv cA vx cv cB cfv eliun cB
      wsmo cA cB cdm wcel wa vy cv vx cv cB cfv wcel vy cv cA cB cfv wcel vx cA
      cB wsmo cA cB cdm wcel wa cA cB cfv con0 wcel vx cv cA wcel vx cv cB cfv
      cA cB cfv wcel vy cv vx cv cB cfv wcel vy cv cA cB cfv wcel wi cA cB
      smofvon cB wsmo cA cB cdm wcel vx cv cA wcel vx cv cB cfv cA cB cfv wcel
      cA cB vx cv smoel 3expia cA cB cfv con0 wcel vy cv vx cv cB cfv wcel vx
      cv cB cfv cA cB cfv wcel vy cv cA cB cfv wcel vy cv vx cv cB cfv cA cB
      cfv ontr1 exp3acom23 sylsyld rexlimdv syl5bi ssrdv $.

    $( If ` F ` is an isomorphism from an ordinal ` A ` onto ` B ` , which is a
       subset of the ordinals, then ` F ` is a strictly monotonic function.
       Exercise 3 in [TakeutiZaring] p. 50.  (Contributed by Andrew Salmon,
       24-Nov-2011.) $)
    smoiso $p |- ( ( F Isom _E , _E ( A , B ) /\ Ord A /\ B C_ On )
        -> Smo F ) $=
      cA cB cep cep cF wiso cA word cB con0 wss w3a cF cdm con0 cF wf cF cdm
      word vx cv vy cv wcel vx cv cF cfv vy cv cF cfv wcel wi vy cF cdm wral vx
      cF cdm wral cF wsmo cA cB cep cep cF wiso cA cB cF wf cA word cB con0 wss
      cF cdm con0 cF wf cA cB cep cep cF wiso cA cB cF wf1o cA cB cF wf cA cB
      cep cep cF isof1o cA cB cF f1of syl cA cB cF wf cB con0 wss cF cdm con0
      cF wf cA word cA cB cF wf cF cdm cB cF wf cB con0 wss cF cdm con0 cF wf
      cA cB cF wf cF cdm cB cF wf cF cdm cA wss cA cB cF ffdm simpld cF cdm cB
      con0 cF fss sylan 3adant2 syl3an1 cA cB cep cep cF wiso cA word cF cdm
      word cB con0 wss cA cB cep cep cF wiso cA word cF cdm word cA cB cep cep
      cF wiso cA cF cdm wceq cA word cF cdm word wb cA cB cep cep cF wiso cA cB
      cF wf1o cA cB cF wf cA cF cdm wceq cA cB cep cep cF isof1o cA cB cF f1of
      cA cB cF wf cF cdm cA cA cB cF fdm eqcomd 3syl cA cF cdm ordeq syl biimpa
      3adant3 cA cB cep cep cF wiso cA word vx cv vy cv wcel vx cv cF cfv vy cv
      cF cfv wcel wi vy cF cdm wral vx cF cdm wral cB con0 wss cA cB cep cep cF
      wiso vx cv vy cv wcel vx cv cF cfv vy cv cF cfv wcel wi vx vy cF cdm cF
      cdm cA cB cep cep cF wiso vx cv cF cdm wcel vy cv cF cdm wcel wa vx cv cA
      wcel vy cv cA wcel wa vx cv vy cv wcel vx cv cF cfv vy cv cF cfv wcel wi
      cA cB cep cep cF wiso cA cB cF wf1o cA cB cF wf vx cv cF cdm wcel vy cv
      cF cdm wcel wa vx cv cA wcel vy cv cA wcel wa wb cA cB cep cep cF isof1o
      cA cB cF f1of cA cB cF wf vx cv cF cdm wcel vx cv cA wcel vy cv cF cdm
      wcel vy cv cA wcel cA cB cF wf cF cdm cA vx cv cA cB cF fdm eleq2d cA cB
      cF wf cF cdm cA vy cv cA cB cF fdm eleq2d anbi12d 3syl cA cB cep cep cF
      wiso vx cv cA wcel vy cv cA wcel wa vx cv vy cv wcel vx cv cF cfv vy cv
      cF cfv wcel wi cA cB cep cep cF wiso vx cv cA wcel vy cv cA wcel wa wa vx
      cv vy cv wcel vx cv cF cfv vy cv cF cfv wcel cA cB cep cep cF wiso vx cv
      cA wcel vy cv cA wcel wa wa vx cv vy cv cep wbr vx cv cF cfv vy cv cF cfv
      cep wbr vx cv vy cv wcel vx cv cF cfv vy cv cF cfv wcel cA cB vx cv vy cv
      cep cep cF isorel vx vy epel vx cv cF cfv vy cv cF cfv vy cv cF fvex
      epelc 3bitr3g biimpd ex sylbid ralrimivv 3ad2ant1 vx vy cF df-smo
      syl3anbrc $.
  $}

  ${
    $d A w x z $.  $d B w z $.  $d F w x y z $.
    $( A strictly monotone ordinal function preserves the epsilon relation.
       (Contributed by Mario Carneiro, 12-Mar-2013.) $)
    smoel2 $p |- ( ( ( F Fn A /\ Smo F ) /\ ( B e. A /\ C e. B ) )
      -> ( F ` C ) e. ( F ` B ) ) $=
      cF cA wfn cF wsmo wa cB cA wcel cC cB wcel wa cC cF cfv cB cF cfv wcel cF
      cA wfn cB cA wcel cC cB wcel wa cB cF cdm wcel cC cB wcel wa cF wsmo cC
      cF cfv cB cF cfv wcel cF cA wfn cB cF cdm wcel cC cB wcel wa cB cA wcel
      cC cB wcel wa cF cA wfn cB cF cdm wcel cB cA wcel cC cB wcel cF cA wfn cF
      cdm cA cB cA cF fndm eleq2d anbi1d biimprd cF wsmo cB cF cdm wcel cC cB
      wcel cC cF cfv cB cF cfv wcel cB cF cC smoel 3expib sylan9 imp $.
  $}

  ${
    $d A w x y z $.  $d F w x y z $.
    $( A strictly monotone ordinal function is one-to-one.  (Contributed by
       Mario Carneiro, 28-Feb-2013.) $)
    smo11 $p |- ( ( F : A --> B /\ Smo F ) -> F : A -1-1-> B ) $=
      cA cB cF wf cF wsmo wa cA cB cF wf vz cv cF cfv vw cv cF cfv wceq vz vw
      weq wi vw cA wral vz cA wral cA cB cF wf1 cA cB cF wf cF wsmo simpl cA cB
      cF wf cF cA wfn cF wsmo vz cv cF cfv vw cv cF cfv wceq vz vw weq wi vw cA
      wral vz cA wral cA cB cF ffn cF cA wfn cF wsmo wa vz cv cF cfv vw cv cF
      cfv wceq vz vw weq wi vz vw cA cA cF cA wfn cF wsmo wa vz cv cA wcel vw
      cv cA wcel wa vz cv word vw cv word wa vz cv cF cfv vw cv cF cfv wceq vz
      vw weq wi cF cA wfn cF wsmo wa vz cv cA wcel vz cv word vw cv cA wcel vw
      cv word cF cA wfn cF wsmo wa cA word vz cv cA wcel vz cv word wi cA cF
      smodm2 cA word vz cv cA wcel vz cv word cA vz cv ordelord ex syl cF cA
      wfn cF wsmo wa cA word vw cv cA wcel vw cv word wi cA cF smodm2 cA word
      vw cv cA wcel vw cv word cA vw cv ordelord ex syl anim12d cF cA wfn cF
      wsmo wa vz cv cA wcel vw cv cA wcel wa vz cv word vw cv word wa vz cv cF
      cfv vw cv cF cfv wceq vz vw weq wi wi vz cv word vw cv word wa vz vw wel
      vz vw weq vw vz wel w3o cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel
      wa wa vz cv cF cfv vw cv cF cfv wceq vz vw weq wi vz cv vw cv ordtri3or
      cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vz vw wel vz cv cF
      cfv vw cv cF cfv wceq vz vw weq wi vz vw weq vw vz wel cF cA wfn cF wsmo
      wa vz cv cA wcel vw cv cA wcel wa wa vz vw wel vz cv cF cfv vw cv cF cfv
      wceq vz vw weq cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vz
      vw wel vz cv cF cfv vw cv cF cfv wceq w3a vz vw weq cF cA wfn cF wsmo wa
      vz cv cA wcel vw cv cA wcel wa wa vz vw wel vz cv cF cfv vw cv cF cfv
      wceq w3a vw cv cF cfv vw cv cF cfv wcel cF cA wfn cF wsmo wa vz cv cA
      wcel vw cv cA wcel wa wa vz vw wel vz cv cF cfv vw cv cF cfv wceq w3a vw
      cv cA wcel vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vz vw
      wel vz cv cF cfv vw cv cF cfv wceq vw cv cF cfv vw cv cF cfv wcel vz cv
      cA wcel vw cv cA wcel cF cA wfn cF wsmo wa vz vw wel vz cv cF cfv vw cv
      cF cfv wceq simp1rr cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa
      wa vz vw wel vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vz
      cv cF cfv vw cv cF cfv wceq cF cA wfn cF wsmo wa vy cv cF cfv vx cv cF
      cfv wcel vy vx cv wral vx cA wral vz cv cA wcel vw cv cA wcel wa cF cA
      wfn cF wsmo wa vy cv cF cfv vx cv cF cfv wcel vx vy cA vx cv cA vx cv vy
      cv cF smoel2 ralrimivva adantr 3ad2ant1 cF cA wfn cF wsmo wa vz cv cA
      wcel vw cv cA wcel wa wa vz vw wel vz cv cF cfv vw cv cF cfv wceq simp2
      cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vz vw wel vz cv cF
      cfv vw cv cF cfv wceq simp3 vw cv cA wcel vy cv cF cfv vx cv cF cfv wcel
      vy vx cv wral vx cA wral vz vw wel w3a vz cv cF cfv vw cv cF cfv wcel vz
      cv cF cfv vw cv cF cfv wceq vw cv cF cfv vw cv cF cfv wcel vw cv cA wcel
      vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vz vw wel vz cv
      cF cfv vw cv cF cfv wcel vw cv cA wcel vy cv cF cfv vx cv cF cfv wcel vy
      vx cv wral vx cA wral vy cv cF cfv vw cv cF cfv wcel vy vw cv wral vz vw
      wel vz cv cF cfv vw cv cF cfv wcel wi vy cv cF cfv vx cv cF cfv wcel vy
      vx cv wral vy cv cF cfv vw cv cF cfv wcel vy vw cv wral vx vw cv cA vy cv
      cF cfv vx cv cF cfv wcel vy cv cF cfv vw cv cF cfv wcel vy vx cv vw cv vx
      vw weq vx cv cF cfv vw cv cF cfv vy cv cF cfv vx cv vw cv cF fveq2 eleq2d
      raleqbi1dv rspcv vy cv cF cfv vw cv cF cfv wcel vz cv cF cfv vw cv cF cfv
      wcel vy vz cv vw cv vy vz weq vy cv cF cfv vz cv cF cfv vw cv cF cfv vy
      cv vz cv cF fveq2 eleq1d rspccv syl6 3imp vz cv cF cfv vw cv cF cfv wceq
      vz cv cF cfv vw cv cF cfv wcel vw cv cF cfv vw cv cF cfv wcel vz cv cF
      cfv vw cv cF cfv vw cv cF cfv eleq1 biimpac sylan syl31anc cF cA wfn cF
      wsmo wa vz cv cA wcel vw cv cA wcel wa wa vz vw wel vw cv cF cfv vw cv cF
      cfv wcel wn vz cv cF cfv vw cv cF cfv wceq cF wsmo vw cv cF cfv vw cv cF
      cfv wcel wn cF cA wfn vz cv cA wcel vw cv cA wcel wa cF wsmo vw cv cF cfv
      con0 wcel vw cv cF cfv word vw cv cF cfv vw cv cF cfv wcel wn vw cv cF
      smofvon2 vw cv cF cfv eloni vw cv cF cfv ordirr 3syl ad2antlr 3ad2ant1
      pm2.65i pm2.21i 3exp vz vw weq vz cv cF cfv vw cv cF cfv wceq vz vw weq
      wi wi cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vz vw weq vz
      cv cF cfv vw cv cF cfv wceq ax-1 a1i cF cA wfn cF wsmo wa vz cv cA wcel
      vw cv cA wcel wa wa vw vz wel vz cv cF cfv vw cv cF cfv wceq vz vw weq cF
      cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vw vz wel vz cv cF
      cfv vw cv cF cfv wceq w3a vz vw weq cF cA wfn cF wsmo wa vz cv cA wcel vw
      cv cA wcel wa wa vw vz wel vz cv cF cfv vw cv cF cfv wceq w3a vw cv cF
      cfv vw cv cF cfv wcel cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa
      wa vw vz wel vz cv cF cfv vw cv cF cfv wceq w3a vz cv cA wcel vy cv cF
      cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vw vz wel vz cv cF cfv vw
      cv cF cfv wceq vw cv cF cfv vw cv cF cfv wcel vz cv cA wcel vw cv cA wcel
      cF cA wfn cF wsmo wa vw vz wel vz cv cF cfv vw cv cF cfv wceq simp1rl cF
      cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vw vz wel vy cv cF
      cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vz cv cF cfv vw cv cF cfv
      wceq cF cA wfn cF wsmo wa vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx
      cA wral vz cv cA wcel vw cv cA wcel wa cF cA wfn cF wsmo wa vy cv cF cfv
      vx cv cF cfv wcel vx vy cA vx cv cA vx cv vy cv cF smoel2 ralrimivva
      adantr 3ad2ant1 cF cA wfn cF wsmo wa vz cv cA wcel vw cv cA wcel wa wa vw
      vz wel vz cv cF cfv vw cv cF cfv wceq simp2 cF cA wfn cF wsmo wa vz cv cA
      wcel vw cv cA wcel wa wa vw vz wel vz cv cF cfv vw cv cF cfv wceq simp3
      vz cv cA wcel vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vw
      vz wel w3a vw cv cF cfv vz cv cF cfv wcel vz cv cF cfv vw cv cF cfv wceq
      vw cv cF cfv vw cv cF cfv wcel vz cv cA wcel vy cv cF cfv vx cv cF cfv
      wcel vy vx cv wral vx cA wral vw vz wel vw cv cF cfv vz cv cF cfv wcel vz
      cv cA wcel vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vx cA wral vy cv
      cF cfv vz cv cF cfv wcel vy vz cv wral vw vz wel vw cv cF cfv vz cv cF
      cfv wcel wi vy cv cF cfv vx cv cF cfv wcel vy vx cv wral vy cv cF cfv vz
      cv cF cfv wcel vy vz cv wral vx vz cv cA vy cv cF cfv vx cv cF cfv wcel
      vy cv cF cfv vz cv cF cfv wcel vy vx cv vz cv vx vz weq vx cv cF cfv vz
      cv cF cfv vy cv cF cfv vx cv vz cv cF fveq2 eleq2d raleqbi1dv rspcv vy cv
      cF cfv vz cv cF cfv wcel vw cv cF cfv vz cv cF cfv wcel vy vw cv vz cv vy
      vw weq vy cv cF cfv vw cv cF cfv vz cv cF cfv vy cv vw cv cF fveq2 eleq1d
      rspccv syl6 3imp vz cv cF cfv vw cv cF cfv wceq vw cv cF cfv vz cv cF cfv
      wcel vw cv cF cfv vw cv cF cfv wcel vz cv cF cfv vw cv cF cfv vw cv cF
      cfv eleq2 biimpac sylan syl31anc cF cA wfn cF wsmo wa vz cv cA wcel vw cv
      cA wcel wa wa vw vz wel vw cv cF cfv vw cv cF cfv wcel wn vz cv cF cfv vw
      cv cF cfv wceq cF wsmo vw cv cF cfv vw cv cF cfv wcel wn cF cA wfn vz cv
      cA wcel vw cv cA wcel wa cF wsmo vw cv cF cfv con0 wcel vw cv cF cfv word
      vw cv cF cfv vw cv cF cfv wcel wn vw cv cF smofvon2 vw cv cF cfv eloni vw
      cv cF cfv ordirr 3syl ad2antlr 3ad2ant1 pm2.65i pm2.21i 3exp 3jaod syl5
      ex mpdd ralrimivv sylan vz vw cA cB cF dff13 sylanbrc $.
  $}

  ${
    $( A strictly monotone ordinal function preserves strict ordering.
       (Contributed by Mario Carneiro, 4-Mar-2013.) $)
    smoord $p |- ( ( ( F Fn A /\ Smo F ) /\ ( C e. A /\ D e. A ) ) ->
      ( C e. D <-> ( F ` C ) e. ( F ` D ) ) ) $=
      cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa wa cC word cD word cC cD
      wcel cC cF cfv cD cF cfv wcel wb cF cA wfn cF wsmo wa cC cA wcel cD cA
      wcel wa wa cA word cC cA wcel cC word cF cA wfn cF wsmo wa cA word cC cA
      wcel cD cA wcel wa cA cF smodm2 adantr cF cA wfn cF wsmo wa cC cA wcel cD
      cA wcel simprl cA cC ordelord syl2anc cF cA wfn cF wsmo wa cC cA wcel cD
      cA wcel wa wa cA word cD cA wcel cD word cF cA wfn cF wsmo wa cA word cC
      cA wcel cD cA wcel wa cA cF smodm2 adantr cF cA wfn cF wsmo wa cC cA wcel
      cD cA wcel simprr cA cD ordelord syl2anc cC word cD word wa cC cD wcel cC
      cD wceq cD cC wcel w3o cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa wa
      cC cD wcel cC cF cfv cD cF cfv wcel wb cC cD ordtri3or cF cA wfn cF wsmo
      wa cC cA wcel cD cA wcel wa wa cC cD wcel cC cD wcel cC cF cfv cD cF cfv
      wcel wb cC cD wceq cD cC wcel cF cA wfn cF wsmo wa cC cA wcel cD cA wcel
      wa cC cD wcel cC cD wcel cC cF cfv cD cF cfv wcel wb cF cA wfn cF wsmo wa
      cC cA wcel cD cA wcel wa cC cD wcel w3a cC cD wcel cC cF cfv cD cF cfv
      wcel cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wcel simp3 cF cA
      wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wcel cC cF cfv cD cF cfv
      wcel cF cA wfn cF wsmo wa cD cA wcel cC cD wcel cC cF cfv cD cF cfv wcel
      wi cC cA wcel cF cA wfn cF wsmo wa cD cA wcel cC cD wcel cC cF cfv cD cF
      cfv wcel cA cD cC cF smoel2 expr adantrl 3impia 2thd 3expia cF cA wfn cF
      wsmo wa cC cA wcel cD cA wcel wa cC cD wceq cC cD wcel cC cF cfv cD cF
      cfv wcel wb cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq w3a
      cC cD wcel cC cF cfv cD cF cfv wcel cF cA wfn cF wsmo wa cC cA wcel cD cA
      wcel wa cC cD wceq w3a cC cC wcel cC cD wcel cF cA wfn cF wsmo wa cC cA
      wcel cD cA wcel wa cC cC wcel wn cC cD wceq cF cA wfn cF wsmo wa cC cA
      wcel cD cA wcel wa wa cC word cC cC wcel wn cF cA wfn cF wsmo wa cC cA
      wcel cD cA wcel wa wa cA word cC cA wcel cC word cF cA wfn cF wsmo wa cA
      word cC cA wcel cD cA wcel wa cA cF smodm2 adantr cF cA wfn cF wsmo wa cC
      cA wcel cD cA wcel simprl cA cC ordelord syl2anc cC ordirr syl 3adant3 cF
      cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq w3a cC cD cC cF cA
      wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq simp3 eleq2d mtbid cF
      cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq w3a cC cF cfv cC cF
      cfv wcel cC cF cfv cD cF cfv wcel cF cA wfn cF wsmo wa cC cA wcel cD cA
      wcel wa cC cF cfv cC cF cfv wcel wn cC cD wceq cF cA wfn cF wsmo wa cC cA
      wcel cD cA wcel wa wa cC cF cfv con0 wcel cC cF cfv word cC cF cfv cC cF
      cfv wcel wn cF wsmo cC cF cfv con0 wcel cF cA wfn cC cA wcel cD cA wcel
      wa cC cF smofvon2 ad2antlr cC cF cfv eloni cC cF cfv ordirr 3syl 3adant3
      cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq w3a cC cF cfv cD
      cF cfv cC cF cfv cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq
      w3a cC cD cF cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cD wceq
      simp3 fveq2d eleq2d mtbid 2falsed 3expia cF cA wfn cF wsmo wa cC cA wcel
      cD cA wcel wa cD cC wcel cC cD wcel cC cF cfv cD cF cfv wcel wb cF cA wfn
      cF wsmo wa cC cA wcel cD cA wcel wa cD cC wcel w3a cC cD wcel cC cF cfv
      cD cF cfv wcel cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cD cC wcel
      w3a cC cD wcel cD cC wcel cC cD wcel wa cF cA wfn cF wsmo wa cC cA wcel
      cD cA wcel wa cD cC wcel w3a cD word cD cC wcel cC cD wcel wa wn cF cA
      wfn cF wsmo wa cC cA wcel cD cA wcel wa cD word cD cC wcel cF cA wfn cF
      wsmo wa cC cA wcel cD cA wcel wa wa cA word cD cA wcel cD word cF cA wfn
      cF wsmo wa cA word cC cA wcel cD cA wcel wa cA cF smodm2 adantr cF cA wfn
      cF wsmo wa cC cA wcel cD cA wcel simprr cA cD ordelord syl2anc 3adant3 cD
      cC ordn2lp syl cD cC wcel cF cA wfn cF wsmo wa cC cD wcel cD cC wcel cC
      cD wcel wa wi cC cA wcel cD cA wcel wa cD cC wcel cC cD wcel pm3.2
      3ad2ant3 mtod cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cD cC wcel
      w3a cC cF cfv cD cF cfv wcel cC cF cfv cD cF cfv wcel cD cF cfv cC cF cfv
      wcel wa cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cD cC wcel w3a cC
      cF cfv word cC cF cfv cD cF cfv wcel cD cF cfv cC cF cfv wcel wa wn cF cA
      wfn cF wsmo wa cC cA wcel cD cA wcel wa cC cF cfv word cD cC wcel cF cA
      wfn cF wsmo wa cC cA wcel cD cA wcel wa wa cC cF cfv con0 wcel cC cF cfv
      word cF wsmo cC cF cfv con0 wcel cF cA wfn cC cA wcel cD cA wcel wa cC cF
      smofvon2 ad2antlr cC cF cfv eloni syl 3adant3 cC cF cfv cD cF cfv ordn2lp
      syl cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa cD cC wcel w3a cD cF
      cfv cC cF cfv wcel cC cF cfv cD cF cfv wcel cC cF cfv cD cF cfv wcel cD
      cF cfv cC cF cfv wcel wa wi cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa
      cD cC wcel cD cF cfv cC cF cfv wcel cF cA wfn cF wsmo wa cC cA wcel cD cC
      wcel cD cF cfv cC cF cfv wcel cD cA wcel cA cC cD cF smoel2 adantrlr
      3impb cD cF cfv cC cF cfv wcel cC cF cfv cD cF cfv wcel pm3.21 syl mtod
      2falsed 3expia 3jaod syl5 mp2and $.
  $}

  ${
    $( A strictly monotone ordinal function preserves weak ordering.
       (Contributed by Mario Carneiro, 4-Mar-2013.) $)
    smoword $p |- ( ( ( F Fn A /\ Smo F ) /\ ( C e. A /\ D e. A ) ) ->
      ( C C_ D <-> ( F ` C ) C_ ( F ` D ) ) ) $=
      cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa wa cD cC wcel wn cD cF cfv
      cC cF cfv wcel wn cC cD wss cC cF cfv cD cF cfv wss cF cA wfn cF wsmo wa
      cD cA wcel cC cA wcel cD cC wcel wn cD cF cfv cC cF cfv wcel wn wb cF cA
      wfn cF wsmo wa cD cA wcel cC cA wcel wa wa cD cC wcel cD cF cfv cC cF cfv
      wcel cA cD cC cF smoord notbid ancom2s cF cA wfn cF wsmo wa cC cA wcel cD
      cA wcel wa wa cC word cD word cC cD wss cD cC wcel wn wb cF cA wfn cF
      wsmo wa cC cA wcel cD cA wcel wa wa cA word cC cA wcel cC word cF cA wfn
      cF wsmo wa cA word cC cA wcel cD cA wcel wa cA cF smodm2 adantr cF cA wfn
      cF wsmo wa cC cA wcel cD cA wcel simprl cA cC ordelord syl2anc cF cA wfn
      cF wsmo wa cC cA wcel cD cA wcel wa wa cA word cD cA wcel cD word cF cA
      wfn cF wsmo wa cA word cC cA wcel cD cA wcel wa cA cF smodm2 adantr cF cA
      wfn cF wsmo wa cC cA wcel cD cA wcel simprr cA cD ordelord syl2anc cC cD
      ordtri1 syl2anc cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa wa cC cF
      cfv word cD cF cfv word cC cF cfv cD cF cfv wss cD cF cfv cC cF cfv wcel
      wn wb cF cA wfn cF wsmo wa cC cA wcel cD cA wcel wa wa cF wsmo cC cF cfv
      con0 wcel cC cF cfv word cF cA wfn cF wsmo cC cA wcel cD cA wcel wa
      simplr cC cF smofvon2 cC cF cfv eloni 3syl cF cA wfn cF wsmo wa cC cA
      wcel cD cA wcel wa wa cF wsmo cD cF cfv con0 wcel cD cF cfv word cF cA
      wfn cF wsmo cC cA wcel cD cA wcel wa simplr cD cF smofvon2 cD cF cfv
      eloni 3syl cC cF cfv cD cF cfv ordtri1 syl2anc 3bitr4d $.
  $}

  ${
    $d A y x $.  $d C x $.  $d F y x $.
    $( A strictly monotone ordinal function is greater than or equal to its
       argument.  Exercise 1 in [TakeutiZaring] p. 50.  (Contributed by Andrew
       Salmon, 23-Nov-2011.)  (Revised by Mario Carneiro, 28-Feb-2013.) $)
    smogt $p |- ( ( F Fn A /\ Smo F /\ C e. A ) -> C C_ ( F ` C ) ) $=
      cF cA wfn cF wsmo cC cA wcel cC cC cF cfv wss cC cA wcel cF cA wfn cF
      wsmo wa cC cC cF cfv wss cF cA wfn cF wsmo wa vx cv vx cv cF cfv wss wi
      cF cA wfn cF wsmo wa cC cC cF cfv wss wi vx cC cA vx cv cC wceq vx cv vx
      cv cF cfv wss cC cC cF cfv wss cF cA wfn cF wsmo wa vx cv cC wceq vx cv
      cC vx cv cF cfv cC cF cfv vx cv cC wceq id vx cv cC cF fveq2 sseq12d
      imbi2d cF cA wfn cF wsmo wa vx cv cA wcel vx cv vx cv cF cfv wss cF cA
      wfn cF wsmo vx cv cA wcel vx cv vx cv cF cfv wss vx cv con0 wcel cF cA
      wfn cF wsmo vx cv cA wcel w3a vx cv vx cv cF cfv wss cF cA wfn cF wsmo vx
      cv cA wcel w3a vx cv word vx cv con0 wcel cF cA wfn cF wsmo vx cv cA wcel
      w3a cA word vx cv cA wcel vx cv word cF cA wfn cF wsmo cA word vx cv cA
      wcel cA cF smodm2 3adant3 cF cA wfn cF wsmo vx cv cA wcel simp3 cA vx cv
      ordelord syl2anc vx cv vx vex elon sylibr cF cA wfn cF wsmo vx cv cA wcel
      w3a vx cv vx cv cF cfv wss wi cF cA wfn cF wsmo vy cv cA wcel w3a vy cv
      vy cv cF cfv wss wi vx vy vx vy weq cF cA wfn cF wsmo vx cv cA wcel w3a
      cF cA wfn cF wsmo vy cv cA wcel w3a vx cv vx cv cF cfv wss vy cv vy cv cF
      cfv wss vx vy weq vx cv cA wcel vy cv cA wcel cF cA wfn cF wsmo vx cv vy
      cv cA eleq1 3anbi3d vx vy weq vx cv vy cv vx cv cF cfv vy cv cF cfv vx vy
      weq id vx cv vy cv cF fveq2 sseq12d imbi12d cF cA wfn cF wsmo vy cv cA
      wcel w3a vy cv vy cv cF cfv wss wi vy vx cv wral cF cA wfn cF wsmo vx cv
      cA wcel w3a vx cv vx cv cF cfv wss wi wi vx cv con0 wcel cF cA wfn cF
      wsmo vx cv cA wcel w3a cF cA wfn cF wsmo vy cv cA wcel w3a vy cv vy cv cF
      cfv wss wi vy vx cv wral vx cv vx cv cF cfv wss cF cA wfn cF wsmo vx cv
      cA wcel w3a cF cA wfn cF wsmo vy cv cA wcel w3a vy cv vy cv cF cfv wss wi
      vy vx cv wral vy cv vy cv cF cfv wss vy vx cv wral vx cv vx cv cF cfv wss
      cF cA wfn cF wsmo vx cv cA wcel w3a cF cA wfn cF wsmo vy cv cA wcel w3a
      vy cv vy cv cF cfv wss wi vy cv vy cv cF cfv wss vy vx cv cF cA wfn cF
      wsmo vx cv cA wcel w3a vy vx wel wa cF cA wfn cF wsmo vy cv cA wcel cF cA
      wfn cF wsmo vy cv cA wcel w3a vy cv vy cv cF cfv wss wi vy cv vy cv cF
      cfv wss wi cF cA wfn cF wsmo vx cv cA wcel vy vx wel simpl1 cF cA wfn cF
      wsmo vx cv cA wcel vy vx wel simpl2 cF cA wfn cF wsmo vx cv cA wcel w3a
      vy vx wel vy cv cA wcel cF cA wfn cF wsmo vx cv cA wcel w3a cA word vx cv
      cA wcel vy vx wel vy cv cA wcel wi cF cA wfn cF wsmo cA word vx cv cA
      wcel cA cF smodm2 3adant3 cF cA wfn cF wsmo vx cv cA wcel simp3 cA word
      vy vx wel vx cv cA wcel vy cv cA wcel vy cv vx cv cA ordtr1 exp3acom23
      sylc imp cF cA wfn cF wsmo vy cv cA wcel w3a vy cv vy cv cF cfv wss
      pm2.27 syl3anc ralimdva cF cA wfn cF wsmo vx cv cA wcel w3a vy cv vy cv
      cF cfv wss vy vx cv wral vy cv vx cv cF cfv wcel vy vx cv wral vx cv vx
      cv cF cfv wss cF cA wfn cF wsmo vx cv cA wcel w3a vy cv vy cv cF cfv wss
      vy cv vx cv cF cfv wcel vy vx cv cF cA wfn cF wsmo vx cv cA wcel w3a vy
      vx wel vy cv vy cv cF cfv wss vy cv vx cv cF cfv wcel wi cF cA wfn cF
      wsmo vx cv cA wcel vy vx wel vy cv vy cv cF cfv wss vy cv vx cv cF cfv
      wcel wi wi cF cA wfn cF wsmo wa vx cv cA wcel vy vx wel vy cv vy cv cF
      cfv wss vy cv vx cv cF cfv wcel cF cA wfn cF wsmo vx cv cA wcel vy vx wel
      vy cv vy cv cF cfv wss w3a vy cv vx cv cF cfv wcel cF cA wfn cF wsmo vx
      cv cA wcel vy vx wel vy cv vy cv cF cfv wss w3a w3a vy cv word vx cv cF
      cfv word vy cv vy cv cF cfv wss vy cv cF cfv vx cv cF cfv wcel vy cv vx
      cv cF cfv wcel cF cA wfn cF wsmo vx cv cA wcel vy vx wel vy cv vy cv cF
      cfv wss w3a w3a vx cv word vy vx wel vy cv word cF cA wfn cF wsmo vx cv
      cA wcel vy vx wel vy cv vy cv cF cfv wss w3a w3a cA word vx cv cA wcel vx
      cv word cF cA wfn cF wsmo cA word vx cv cA wcel vy vx wel vy cv vy cv cF
      cfv wss w3a cA cF smodm2 3adant3 cF cA wfn cF wsmo vx cv cA wcel vy vx
      wel vy cv vy cv cF cfv wss simp31 cA vx cv ordelord syl2anc cF cA wfn cF
      wsmo vx cv cA wcel vy vx wel vy cv vy cv cF cfv wss simp32 vx cv vy cv
      ordelord syl2anc cF cA wfn cF wsmo vx cv cA wcel vy vx wel vy cv vy cv cF
      cfv wss w3a w3a vx cv cF cfv con0 wcel vx cv cF cfv word cF wsmo cF cA
      wfn vx cv cF cfv con0 wcel vx cv cA wcel vy vx wel vy cv vy cv cF cfv wss
      w3a vx cv cF smofvon2 3ad2ant2 vx cv cF cfv eloni syl cF cA wfn cF wsmo
      vx cv cA wcel vy vx wel vy cv vy cv cF cfv wss simp33 cF cA wfn cF wsmo
      vx cv cA wcel vy vx wel vy cv vy cv cF cfv wss w3a vy cv cF cfv vx cv cF
      cfv wcel cF cA wfn cF wsmo wa vx cv cA wcel vy vx wel vy cv cF cfv vx cv
      cF cfv wcel vy cv vy cv cF cfv wss cA vx cv vy cv cF smoel2 3adantr3
      3impa vy cv word vx cv cF cfv word wa vy cv vy cv cF cfv wss vy cv cF cfv
      vx cv cF cfv wcel wa vy cv vx cv cF cfv wcel vy cv vy cv cF cfv vx cv cF
      cfv ordtr2 imp syl22anc 3expia 3expd 3impia imp ralimdva vy vx cv vx cv
      cF cfv dfss3 syl6ibr syld com12 a1i tfis2 mpcom 3expia com12 vtoclga
      com12 3impia $.
  $}

  ${
    $d A x $.  $d B x $.  $d F x $.
    $( The range of a strictly monotone ordinal function dominates the domain.
       (Contributed by Mario Carneiro, 13-Mar-2013.) $)
    smorndom $p |- ( ( F : A --> B /\ Smo F /\ Ord B ) -> A C_ B ) $=
      cA cB cF wf cF wsmo cB word w3a vx cA cB cA cB cF wf cF wsmo cB word w3a
      vx cv cA wcel vx cv cB wcel cA cB cF wf cF wsmo cB word w3a vx cv cA wcel
      wa vx cv word cB word vx cv vx cv cF cfv wss vx cv cF cfv cB wcel vx cv
      cB wcel cA cB cF wf cF wsmo cB word w3a vx cv cA wcel cA word vx cv word
      cA cB cF wf cF wsmo cB word w3a vx cv cA wcel wa cF cA wfn cF wsmo cA
      word cA cB cF wf cF wsmo cB word w3a vx cv cA wcel wa cA cB cF wf cF cA
      wfn cA cB cF wf cF wsmo cB word vx cv cA wcel simpl1 cA cB cF ffn syl cA
      cB cF wf cF wsmo cB word vx cv cA wcel simpl2 cA cF smodm2 syl2anc cA vx
      cv ordelord sylancom cA cB cF wf cF wsmo cB word vx cv cA wcel simpl3 cA
      cB cF wf cF wsmo cB word w3a vx cv cA wcel wa cF cA wfn cF wsmo vx cv cA
      wcel vx cv vx cv cF cfv wss cA cB cF wf cF wsmo cB word w3a vx cv cA wcel
      wa cA cB cF wf cF cA wfn cA cB cF wf cF wsmo cB word vx cv cA wcel simpl1
      cA cB cF ffn syl cA cB cF wf cF wsmo cB word vx cv cA wcel simpl2 cA cB
      cF wf cF wsmo cB word w3a vx cv cA wcel simpr cA vx cv cF smogt syl3anc
      cA cB cF wf cF wsmo vx cv cA wcel vx cv cF cfv cB wcel cB word cA cB vx
      cv cF ffvelrn 3ad2antl1 vx cv word cB word wa vx cv vx cv cF cfv wss vx
      cv cF cfv cB wcel wa vx cv cB wcel vx cv vx cv cF cfv cB ordtr2 imp
      syl22anc ex ssrdv $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.
    $( The strictly monotone ordinal functions are also epsilon isomorphisms of
       subclasses of ` On ` .  (Contributed by Mario Carneiro, 20-Mar-2013.) $)
    smoiso2 $p |- ( ( Ord A /\ B C_ On ) ->
      ( ( F : A -onto-> B /\ Smo F ) <-> F Isom _E , _E ( A , B ) ) ) $=
      cA word cB con0 wss wa cA cB cF wfo cF wsmo wa cA cB cep cep cF wiso cA
      word cB con0 wss wa cA cB cF wfo cF wsmo wa cA cB cep cep cF wiso cA word
      cB con0 wss wa cA cB cF wfo cF wsmo wa wa cA cB cF wf1o vx cv vy cv cep
      wbr vx cv cF cfv vy cv cF cfv cep wbr wb vy cA wral vx cA wral cA cB cep
      cep cF wiso cA cB cF wfo cF wsmo wa cA cB cF wf1o cA word cB con0 wss wa
      cA cB cF wfo cF wsmo wa cA cB cF wf1 cA cB cF wfo cA cB cF wf1o cA cB cF
      wfo cA cB cF wf cF wsmo cA cB cF wf1 cA cB cF fof cA cB cF smo11 sylan cA
      cB cF wfo cF wsmo simpl cA cB cF df-f1o sylanbrc adantl cA cB cF wfo cF
      wsmo wa vx cv vy cv cep wbr vx cv cF cfv vy cv cF cfv cep wbr wb vy cA
      wral vx cA wral cA word cB con0 wss wa cA cB cF wfo cF cA wfn cF wsmo vx
      cv vy cv cep wbr vx cv cF cfv vy cv cF cfv cep wbr wb vy cA wral vx cA
      wral cA cB cF fofn cF cA wfn cF wsmo wa vx cv vy cv cep wbr vx cv cF cfv
      vy cv cF cfv cep wbr wb vx vy cA cA cF cA wfn cF wsmo wa vx cv cA wcel vy
      cv cA wcel wa wa vx cv vy cv wcel vx cv cF cfv vy cv cF cfv wcel vx cv vy
      cv cep wbr vx cv cF cfv vy cv cF cfv cep wbr cA vx cv vy cv cF smoord vx
      vy epel vx cv cF cfv vy cv cF cfv vy cv cF fvex epelc 3bitr4g ralrimivva
      sylan adantl vx vy cA cB cep cep cF df-isom sylanbrc ex cA cB cep cep cF
      wiso cA word cB con0 wss wa cA cB cF wfo cF wsmo wa cA cB cep cep cF wiso
      cA word cB con0 wss cA cB cF wfo cF wsmo wa cA cB cep cep cF wiso cA word
      cB con0 wss w3a cA cB cF wfo cF wsmo cA cB cep cep cF wiso cA word cA cB
      cF wfo cB con0 wss cA cB cep cep cF wiso cA cB cF wf1o cA cB cF wfo cA cB
      cep cep cF isof1o cA cB cF f1ofo syl 3ad2ant1 cA cB cF smoiso jca 3expib
      com12 impbid $.
  $}


