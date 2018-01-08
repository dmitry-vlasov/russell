
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Function_operation.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        First and second members of an ordered pair

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c 1st $. $( First member of an ordered pair $)
  $c 2nd $. $( Second member of an ordered pair $)

  $( Extend the definition of a class to include the first member an ordered
     pair function. $)
  c1st $a class 1st $.

  $( Extend the definition of a class to include the second member an ordered
     pair function. $)
  c2nd $a class 2nd $.

  $( Define a function that extracts the first member, or abscissa, of an
     ordered pair.  Theorem ~ op1st proves that it does this.  For example,
     ` ( 1st `` <. 3 , 4 >. ) = 3 ` .  Equivalent to Definition 5.13 (i) of
     [Monk1] p. 52 (compare ~ op1sta and ~ op1stb ).  The notation is the same
     as Monk's.  (Contributed by NM, 9-Oct-2004.) $)
  df-1st $a |- 1st = ( x e. _V |-> U. dom { x } ) $.

  $( Define a function that extracts the second member, or ordinate, of an
     ordered pair.  Theorem ~ op2nd proves that it does this.  For example,
     ` ( 2nd `` <. 3 , 4 >. ) = 4 ` .  Equivalent to Definition 5.13 (ii) of
     [Monk1] p. 52 (compare ~ op2nda and ~ op2ndb ).  The notation is the same
     as Monk's.  (Contributed by NM, 9-Oct-2004.) $)
  df-2nd $a |- 2nd = ( x e. _V |-> U. ran { x } ) $.

  ${
    $d x y A $.  $d x y B $.
    $( The value of the function that extracts the first member of an ordered
       pair.  (Contributed by NM, 9-Oct-2004.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)
    1stval $p |- ( 1st ` A ) = U. dom { A } $=
      cA cvv wcel cA c1st cfv cA csn cdm cuni wceq vx cA vx cv csn cdm cuni cA
      csn cdm cuni cvv c1st vx cv cA wceq vx cv csn cdm cA csn cdm vx cv cA
      wceq vx cv csn cA csn vx cv cA sneq dmeqd unieqd vx df-1st cA csn cdm cA
      csn cA snex dmex uniex fvmpt cA cvv wcel wn cA c1st cfv c0 cA csn cdm
      cuni cA c1st fvprc cA cvv wcel wn cA csn cdm cuni c0 cuni c0 cA cvv wcel
      wn cA csn cdm c0 cA cvv wcel wn cA csn cdm c0 cdm c0 cA cvv wcel wn cA
      csn c0 cA cvv wcel wn cA csn c0 wceq cA snprc biimpi dmeqd dm0 syl6eq
      unieqd uni0 syl6eq eqtr4d pm2.61i $.

    $( The value of the function that extracts the second member of an ordered
       pair.  (Contributed by NM, 9-Oct-2004.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)
    2ndval $p |- ( 2nd ` A ) = U. ran { A } $=
      cA cvv wcel cA c2nd cfv cA csn crn cuni wceq vx cA vx cv csn crn cuni cA
      csn crn cuni cvv c2nd vx cv cA wceq vx cv csn crn cA csn crn vx cv cA
      wceq vx cv csn cA csn vx cv cA sneq rneqd unieqd vx df-2nd cA csn crn cA
      csn cA snex rnex uniex fvmpt cA cvv wcel wn cA c2nd cfv c0 cA csn crn
      cuni cA c2nd fvprc cA cvv wcel wn cA csn crn cuni c0 cuni c0 cA cvv wcel
      wn cA csn crn c0 cA cvv wcel wn cA csn crn c0 crn c0 cA cvv wcel wn cA
      csn c0 cA cvv wcel wn cA csn c0 wceq cA snprc biimpi rneqd rn0 syl6eq
      unieqd uni0 syl6eq eqtr4d pm2.61i $.
  $}

  $( The value of the first-member function at the empty set.  (Contributed by
     NM, 23-Apr-2007.) $)
  1st0 $p |- ( 1st ` (/) ) = (/) $=
    c0 c1st cfv c0 csn cdm cuni c0 cuni c0 c0 1stval c0 csn cdm c0 dmsn0 unieqi
    uni0 3eqtri $.

  $( The value of the second-member function at the empty set.  (Contributed by
     NM, 23-Apr-2007.) $)
  2nd0 $p |- ( 2nd ` (/) ) = (/) $=
    c0 c2nd cfv c0 csn crn cuni c0 cuni c0 c0 2ndval c0 csn crn c0 c0 csn cdm
    c0 wceq c0 csn crn c0 wceq dmsn0 c0 csn dm0rn0 mpbi unieqi uni0 3eqtri $.

  ${
    op1st.1 $e |- A e. _V $.
    op1st.2 $e |- B e. _V $.
    $( Extract the first member of an ordered pair.  (Contributed by NM,
       5-Oct-2004.) $)
    op1st $p |- ( 1st ` <. A , B >. ) = A $=
      cA cB cop c1st cfv cA cB cop csn cdm cuni cA cA cB cop 1stval cA cB
      op1st.1 op1st.2 op1sta eqtri $.

    $( Extract the second member of an ordered pair.  (Contributed by NM,
       5-Oct-2004.) $)
    op2nd $p |- ( 2nd ` <. A , B >. ) = B $=
      cA cB cop c2nd cfv cA cB cop csn crn cuni cB cA cB cop 2ndval cA cB
      op1st.1 op1st.2 op2nda eqtri $.

    $( Extract the first member of an ordered pair.  (Contributed by Mario
       Carneiro, 31-Aug-2015.) $)
    op1std $p |- ( C = <. A , B >. -> ( 1st ` C ) = A ) $=
      cC cA cB cop wceq cC c1st cfv cA cB cop c1st cfv cA cC cA cB cop c1st
      fveq2 cA cB op1st.1 op1st.2 op1st syl6eq $.

    $( Extract the second member of an ordered pair.  (Contributed by Mario
       Carneiro, 31-Aug-2015.) $)
    op2ndd $p |- ( C = <. A , B >. -> ( 2nd ` C ) = B ) $=
      cC cA cB cop wceq cC c2nd cfv cA cB cop c2nd cfv cB cC cA cB cop c2nd
      fveq2 cA cB op1st.1 op1st.2 op2nd syl6eq $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Extract the first member of an ordered pair.  (Contributed by NM,
       19-Jul-2005.) $)
    op1stg $p |- ( ( A e. V /\ B e. W ) -> ( 1st ` <. A , B >. ) = A ) $=
      vx cv vy cv cop c1st cfv vx cv wceq cA vy cv cop c1st cfv cA wceq cA cB
      cop c1st cfv cA wceq vx vy cA cB cV cW vx cv cA wceq vx cv vy cv cop c1st
      cfv cA vy cv cop c1st cfv vx cv cA vx cv cA wceq vx cv vy cv cop cA vy cv
      cop c1st vx cv cA vy cv opeq1 fveq2d vx cv cA wceq id eqeq12d vy cv cB
      wceq cA vy cv cop c1st cfv cA cB cop c1st cfv cA vy cv cB wceq cA vy cv
      cop cA cB cop c1st vy cv cB cA opeq2 fveq2d eqeq1d vx cv vy cv vx vex vy
      vex op1st vtocl2g $.

    $( Extract the second member of an ordered pair.  (Contributed by NM,
       19-Jul-2005.) $)
    op2ndg $p |- ( ( A e. V /\ B e. W ) -> ( 2nd ` <. A , B >. ) = B ) $=
      vx cv vy cv cop c2nd cfv vy cv wceq cA vy cv cop c2nd cfv vy cv wceq cA
      cB cop c2nd cfv cB wceq vx vy cA cB cV cW vx cv cA wceq vx cv vy cv cop
      c2nd cfv cA vy cv cop c2nd cfv vy cv vx cv cA wceq vx cv vy cv cop cA vy
      cv cop c2nd vx cv cA vy cv opeq1 fveq2d eqeq1d vy cv cB wceq cA vy cv cop
      c2nd cfv cA cB cop c2nd cfv vy cv cB vy cv cB wceq cA vy cv cop cA cB cop
      c2nd vy cv cB cA opeq2 fveq2d vy cv cB wceq id eqeq12d vx cv vy cv vx vex
      vy vex op2nd vtocl2g $.

    $( Extract the first member of an ordered triple.  (Due to infrequent
       usage, it isn't worthwhile at this point to define special extractors
       for triples, so we reuse the ordered pair extractors for ~ ot1stg ,
       ~ ot2ndg , ~ ot3rdg .)  (Contributed by NM, 3-Apr-2015.)  (Revised by
       Mario Carneiro, 2-May-2015.) $)
    ot1stg $p |- ( ( A e. V /\ B e. W /\ C e. X )
         -> ( 1st ` ( 1st ` <. A , B , C >. ) ) = A ) $=
      cA cV wcel cB cW wcel cC cX wcel cA cB cC cotp c1st cfv c1st cfv cA wceq
      cC cX wcel cA cV wcel cB cW wcel wa cA cB cC cotp c1st cfv c1st cfv cA cB
      cop c1st cfv cA cC cX wcel cA cB cC cotp c1st cfv cA cB cop c1st cC cX
      wcel cA cB cC cotp c1st cfv cA cB cop cC cop c1st cfv cA cB cop cA cB cC
      cotp cA cB cop cC cop c1st cA cB cC df-ot fveq2i cA cB cop cvv wcel cC cX
      wcel cA cB cop cC cop c1st cfv cA cB cop wceq cA cB opex cA cB cop cC cvv
      cX op1stg mpan syl5eq fveq2d cA cB cV cW op1stg sylan9eqr 3impa $.

    $( Extract the second member of an ordered triple.  (See ~ ot1stg
       comment.)  (Contributed by NM, 3-Apr-2015.)  (Revised by Mario Carneiro,
       2-May-2015.) $)
    ot2ndg $p |- ( ( A e. V /\ B e. W /\ C e. X )
         -> ( 2nd ` ( 1st ` <. A , B , C >. ) ) = B ) $=
      cA cV wcel cB cW wcel cC cX wcel cA cB cC cotp c1st cfv c2nd cfv cB wceq
      cC cX wcel cA cV wcel cB cW wcel wa cA cB cC cotp c1st cfv c2nd cfv cA cB
      cop c2nd cfv cB cC cX wcel cA cB cC cotp c1st cfv cA cB cop c2nd cC cX
      wcel cA cB cC cotp c1st cfv cA cB cop cC cop c1st cfv cA cB cop cA cB cC
      cotp cA cB cop cC cop c1st cA cB cC df-ot fveq2i cA cB cop cvv wcel cC cX
      wcel cA cB cop cC cop c1st cfv cA cB cop wceq cA cB opex cA cB cop cC cvv
      cX op1stg mpan syl5eq fveq2d cA cB cV cW op2ndg sylan9eqr 3impa $.

    $( Extract the third member of an ordered triple.  (See ~ ot1stg comment.)
       (Contributed by NM, 3-Apr-2015.) $)
    ot3rdg $p |- ( C e. V -> ( 2nd ` <. A , B , C >. ) = C ) $=
      cC cV wcel cA cB cC cotp c2nd cfv cA cB cop cC cop c2nd cfv cC cA cB cC
      cotp cA cB cop cC cop c2nd cA cB cC df-ot fveq2i cA cB cop cvv wcel cC cV
      wcel cA cB cop cC cop c2nd cfv cC wceq cA cB opex cA cB cop cC cvv cV
      op2ndg mpan syl5eq $.

    $( Alternate value of the function that extracts the first member of an
       ordered pair.  Definition 5.13 (i) of [Monk1] p. 52.  (Contributed by
       NM, 18-Aug-2006.) $)
    1stval2 $p |- ( A e. ( _V X. _V ) -> ( 1st ` A ) = |^| |^| A ) $=
      cA cvv cvv cxp wcel cA vx cv vy cv cop wceq vy wex vx wex cA c1st cfv cA
      cint cint wceq vx vy cA elvv cA vx cv vy cv cop wceq cA c1st cfv cA cint
      cint wceq vx vy cA vx cv vy cv cop wceq vx cv vy cv cop c1st cfv vx cv vy
      cv cop cint cint cA c1st cfv cA cint cint vx cv vy cv cop c1st cfv vx cv
      vx cv vy cv cop cint cint vx cv vy cv vx vex vy vex op1st vx cv vy cv vx
      vex vy vex op1stb eqtr4i cA vx cv vy cv cop c1st fveq2 cA vx cv vy cv cop
      wceq cA cint vx cv vy cv cop cint cA vx cv vy cv cop inteq inteqd 3eqtr4a
      exlimivv sylbi $.

    $( Alternate value of the function that extracts the second member of an
       ordered pair.  Definition 5.13 (ii) of [Monk1] p. 52.  (Contributed by
       NM, 18-Aug-2006.) $)
    2ndval2 $p |- ( A e. ( _V X. _V )
               -> ( 2nd ` A ) = |^| |^| |^| `' { A } ) $=
      cA cvv cvv cxp wcel cA vx cv vy cv cop wceq vy wex vx wex cA c2nd cfv cA
      csn ccnv cint cint cint wceq vx vy cA elvv cA vx cv vy cv cop wceq cA
      c2nd cfv cA csn ccnv cint cint cint wceq vx vy cA vx cv vy cv cop wceq vx
      cv vy cv cop c2nd cfv vx cv vy cv cop csn ccnv cint cint cint cA c2nd cfv
      cA csn ccnv cint cint cint vx cv vy cv cop c2nd cfv vy cv vx cv vy cv cop
      csn ccnv cint cint cint vx cv vy cv vx vex vy vex op2nd vx cv vy cv vx
      vex vy vex op2ndb eqtr4i cA vx cv vy cv cop c2nd fveq2 cA vx cv vy cv cop
      wceq cA csn ccnv cint cint vx cv vy cv cop csn ccnv cint cint cA vx cv vy
      cv cop wceq cA csn ccnv cint vx cv vy cv cop csn ccnv cint cA vx cv vy cv
      cop wceq cA csn ccnv vx cv vy cv cop csn ccnv cA vx cv vy cv cop wceq cA
      csn vx cv vy cv cop csn cA vx cv vy cv cop sneq cnveqd inteqd inteqd
      inteqd 3eqtr4a exlimivv sylbi $.
  $}

  ${
    $d x y z w v A $.  $d x y z B $.  $d x y z w v u $.
    $( The ` 1st ` function maps the universe onto the universe.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
    fo1st $p |- 1st : _V -onto-> _V $=
      cvv cvv c1st wfo c1st cvv wfn c1st crn cvv wceq vx cvv vx cv csn cdm cuni
      c1st vx cv csn cdm vx cv csn vx cv snex dmex uniex vx df-1st fnmpti c1st
      crn vy cv vx cv csn cdm cuni wceq vx cvv wrex vy cab cvv vx vy cvv vx cv
      csn cdm cuni c1st vx df-1st rnmpt vy cv vx cv csn cdm cuni wceq vx cvv
      wrex vy cvv vy cv cvv wcel vy cv vx cv csn cdm cuni wceq vx cvv wrex vy
      vex vy cv vy cv cop cvv wcel vy cv vy cv vy cv cop csn cdm cuni wceq vy
      cv vx cv csn cdm cuni wceq vx cvv wrex vy cv vy cv opex vy cv vy cv cop
      csn cdm cuni vy cv vy cv vy cv vy vex vy vex op1sta eqcomi vy cv vx cv
      csn cdm cuni wceq vy cv vy cv vy cv cop csn cdm cuni wceq vx vy cv vy cv
      cop cvv vx cv vy cv vy cv cop wceq vx cv csn cdm cuni vy cv vy cv cop csn
      cdm cuni vy cv vx cv vy cv vy cv cop wceq vx cv csn cdm vy cv vy cv cop
      csn cdm vx cv vy cv vy cv cop wceq vx cv csn vy cv vy cv cop csn vx cv vy
      cv vy cv cop sneq dmeqd unieqd eqeq2d rspcev mp2an 2th abbi2i eqtr4i cvv
      cvv c1st df-fo mpbir2an $.

    $d x y z w v A $.  $d x y z B $.  $d x y z w v u $.
    $( The ` 2nd ` function maps the universe onto the universe.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
    fo2nd $p |- 2nd : _V -onto-> _V $=
      cvv cvv c2nd wfo c2nd cvv wfn c2nd crn cvv wceq vx cvv vx cv csn crn cuni
      c2nd vx cv csn crn vx cv csn vx cv snex rnex uniex vx df-2nd fnmpti c2nd
      crn vy cv vx cv csn crn cuni wceq vx cvv wrex vy cab cvv vx vy cvv vx cv
      csn crn cuni c2nd vx df-2nd rnmpt vy cv vx cv csn crn cuni wceq vx cvv
      wrex vy cvv vy cv cvv wcel vy cv vx cv csn crn cuni wceq vx cvv wrex vy
      vex vy cv vy cv cop cvv wcel vy cv vy cv vy cv cop csn crn cuni wceq vy
      cv vx cv csn crn cuni wceq vx cvv wrex vy cv vy cv opex vy cv vy cv cop
      csn crn cuni vy cv vy cv vy cv vy vex vy vex op2nda eqcomi vy cv vx cv
      csn crn cuni wceq vy cv vy cv vy cv cop csn crn cuni wceq vx vy cv vy cv
      cop cvv vx cv vy cv vy cv cop wceq vx cv csn crn cuni vy cv vy cv cop csn
      crn cuni vy cv vx cv vy cv vy cv cop wceq vx cv csn crn vy cv vy cv cop
      csn crn vx cv vy cv vy cv cop wceq vx cv csn vy cv vy cv cop csn vx cv vy
      cv vy cv cop sneq rneqd unieqd eqeq2d rspcev mp2an 2th abbi2i eqtr4i cvv
      cvv c2nd df-fo mpbir2an $.

    $( Mapping of a restriction of the ` 1st ` (first member of an ordered
       pair) function.  (Contributed by NM, 11-Oct-2004.)  (Revised by Mario
       Carneiro, 8-Sep-2013.) $)
    f1stres $p |- ( 1st |` ( A X. B ) ) : ( A X. B ) --> A $=
      vx cv csn cdm cuni cA wcel vx cA cB cxp wral cA cB cxp cA c1st cA cB cxp
      cres wf vx cv csn cdm cuni cA wcel vx cA cB cxp wral vy cv vz cv cop csn
      cdm cuni cA wcel vz cB wral vy cA wral vy cv vz cv cop csn cdm cuni cA
      wcel vy vz cA cB vy cv cA wcel vy cv vz cv cop csn cdm cuni cA wcel vz cv
      cB wcel vy cv vz cv cop csn cdm cuni cA wcel vy cv cA wcel vy cv vz cv
      cop csn cdm cuni vy cv cA vy cv vz cv vy vex vz vex op1sta eleq1i biimpri
      adantr rgen2 vx cv csn cdm cuni cA wcel vy cv vz cv cop csn cdm cuni cA
      wcel vx vy vz cA cB vx cv vy cv vz cv cop wceq vx cv csn cdm cuni vy cv
      vz cv cop csn cdm cuni cA vx cv vy cv vz cv cop wceq vx cv csn cdm vy cv
      vz cv cop csn cdm vx cv vy cv vz cv cop wceq vx cv csn vy cv vz cv cop
      csn vx cv vy cv vz cv cop sneq dmeqd unieqd eleq1d ralxp mpbir vx cA cB
      cxp cA vx cv csn cdm cuni c1st cA cB cxp cres c1st cA cB cxp cres vx cvv
      vx cv csn cdm cuni cmpt cA cB cxp cres vx cA cB cxp vx cv csn cdm cuni
      cmpt c1st vx cvv vx cv csn cdm cuni cmpt cA cB cxp vx df-1st reseq1i cA
      cB cxp cvv wss vx cvv vx cv csn cdm cuni cmpt cA cB cxp cres vx cA cB cxp
      vx cv csn cdm cuni cmpt wceq cA cB cxp ssv vx cvv cA cB cxp vx cv csn cdm
      cuni resmpt ax-mp eqtri fmpt mpbi $.

    $( Mapping of a restriction of the ` 2nd ` (second member of an ordered
       pair) function.  (Contributed by NM, 7-Aug-2006.)  (Revised by Mario
       Carneiro, 8-Sep-2013.) $)
    f2ndres $p |- ( 2nd |` ( A X. B ) ) : ( A X. B ) --> B $=
      vx cv csn crn cuni cB wcel vx cA cB cxp wral cA cB cxp cB c2nd cA cB cxp
      cres wf vx cv csn crn cuni cB wcel vx cA cB cxp wral vy cv vz cv cop csn
      crn cuni cB wcel vz cB wral vy cA wral vy cv vz cv cop csn crn cuni cB
      wcel vy vz cA cB vz cv cB wcel vy cv vz cv cop csn crn cuni cB wcel vy cv
      cA wcel vy cv vz cv cop csn crn cuni cB wcel vz cv cB wcel vy cv vz cv
      cop csn crn cuni vz cv cB vy cv vz cv vy vex vz vex op2nda eleq1i biimpri
      adantl rgen2 vx cv csn crn cuni cB wcel vy cv vz cv cop csn crn cuni cB
      wcel vx vy vz cA cB vx cv vy cv vz cv cop wceq vx cv csn crn cuni vy cv
      vz cv cop csn crn cuni cB vx cv vy cv vz cv cop wceq vx cv csn crn vy cv
      vz cv cop csn crn vx cv vy cv vz cv cop wceq vx cv csn vy cv vz cv cop
      csn vx cv vy cv vz cv cop sneq rneqd unieqd eleq1d ralxp mpbir vx cA cB
      cxp cB vx cv csn crn cuni c2nd cA cB cxp cres c2nd cA cB cxp cres vx cvv
      vx cv csn crn cuni cmpt cA cB cxp cres vx cA cB cxp vx cv csn crn cuni
      cmpt c2nd vx cvv vx cv csn crn cuni cmpt cA cB cxp vx df-2nd reseq1i cA
      cB cxp cvv wss vx cvv vx cv csn crn cuni cmpt cA cB cxp cres vx cA cB cxp
      vx cv csn crn cuni cmpt wceq cA cB cxp ssv vx cvv cA cB cxp vx cv csn crn
      cuni resmpt ax-mp eqtri fmpt mpbi $.

    $( Onto mapping of a restriction of the ` 1st ` (first member of an ordered
       pair) function.  (Contributed by NM, 14-Dec-2008.) $)
    fo1stres $p |- ( B =/= (/) ->
                 ( 1st |` ( A X. B ) ) : ( A X. B ) -onto-> A ) $=
      cB c0 wne cA cB cxp cA c1st cA cB cxp cres wf c1st cA cB cxp cres crn cA
      wceq wa cA cB cxp cA c1st cA cB cxp cres wfo cB c0 wne c1st cA cB cxp
      cres crn cA wceq cA cB cxp cA c1st cA cB cxp cres wf cB c0 wne c1st cA cB
      cxp cres crn cA wss cA c1st cA cB cxp cres crn wss wa c1st cA cB cxp cres
      crn cA wceq cB c0 wne cA c1st cA cB cxp cres crn wss c1st cA cB cxp cres
      crn cA wss cB c0 wne vx cA c1st cA cB cxp cres crn cB c0 wne vy cv cB
      wcel vy wex vx cv cA wcel vx cv c1st cA cB cxp cres crn wcel wi vy cB n0
      vy cv cB wcel vx cv cA wcel vx cv c1st cA cB cxp cres crn wcel wi vy vx
      cv cA wcel vy cv cB wcel vx cv c1st cA cB cxp cres crn wcel vx cv cA wcel
      vy cv cB wcel wa vx cv vy cv cop cA cB cxp wcel vx cv c1st cA cB cxp cres
      crn wcel vx cv vy cv cA cB opelxp vx cv vy cv cop cA cB cxp wcel vx cv vx
      cv vy cv cop c1st cA cB cxp cres cfv c1st cA cB cxp cres crn vx cv vy cv
      cop cA cB cxp wcel vx cv vy cv cop c1st cA cB cxp cres cfv vx cv vy cv
      cop c1st cfv vx cv vx cv vy cv cop cA cB cxp c1st fvres vx cv vy cv vx
      vex vy vex op1st syl6req c1st cA cB cxp cres cA cB cxp wfn vx cv vy cv
      cop cA cB cxp wcel vx cv vy cv cop c1st cA cB cxp cres cfv c1st cA cB cxp
      cres crn wcel cA cB cxp cA c1st cA cB cxp cres wf c1st cA cB cxp cres cA
      cB cxp wfn cA cB f1stres cA cB cxp cA c1st cA cB cxp cres ffn ax-mp cA cB
      cxp vx cv vy cv cop c1st cA cB cxp cres fnfvelrn mpan eqeltrd sylbir
      expcom exlimiv sylbi ssrdv cA cB cxp cA c1st cA cB cxp cres wf c1st cA cB
      cxp cres crn cA wss cA cB f1stres cA cB cxp cA c1st cA cB cxp cres frn
      ax-mp jctil c1st cA cB cxp cres crn cA eqss sylibr cA cB f1stres jctil cA
      cB cxp cA c1st cA cB cxp cres dffo2 sylibr $.

    $( Onto mapping of a restriction of the ` 2nd ` (second member of an
       ordered pair) function.  (Contributed by NM, 14-Dec-2008.) $)
    fo2ndres $p |- ( A =/= (/) ->
                 ( 2nd |` ( A X. B ) ) : ( A X. B ) -onto-> B ) $=
      cA c0 wne cA cB cxp cB c2nd cA cB cxp cres wf c2nd cA cB cxp cres crn cB
      wceq wa cA cB cxp cB c2nd cA cB cxp cres wfo cA c0 wne c2nd cA cB cxp
      cres crn cB wceq cA cB cxp cB c2nd cA cB cxp cres wf cA c0 wne c2nd cA cB
      cxp cres crn cB wss cB c2nd cA cB cxp cres crn wss wa c2nd cA cB cxp cres
      crn cB wceq cA c0 wne cB c2nd cA cB cxp cres crn wss c2nd cA cB cxp cres
      crn cB wss cA c0 wne vy cB c2nd cA cB cxp cres crn cA c0 wne vx cv cA
      wcel vx wex vy cv cB wcel vy cv c2nd cA cB cxp cres crn wcel wi vx cA n0
      vx cv cA wcel vy cv cB wcel vy cv c2nd cA cB cxp cres crn wcel wi vx vx
      cv cA wcel vy cv cB wcel vy cv c2nd cA cB cxp cres crn wcel vx cv cA wcel
      vy cv cB wcel wa vx cv vy cv cop cA cB cxp wcel vy cv c2nd cA cB cxp cres
      crn wcel vx cv vy cv cA cB opelxp vx cv vy cv cop cA cB cxp wcel vy cv vx
      cv vy cv cop c2nd cA cB cxp cres cfv c2nd cA cB cxp cres crn vx cv vy cv
      cop cA cB cxp wcel vx cv vy cv cop c2nd cA cB cxp cres cfv vx cv vy cv
      cop c2nd cfv vy cv vx cv vy cv cop cA cB cxp c2nd fvres vx cv vy cv vx
      vex vy vex op2nd syl6req c2nd cA cB cxp cres cA cB cxp wfn vx cv vy cv
      cop cA cB cxp wcel vx cv vy cv cop c2nd cA cB cxp cres cfv c2nd cA cB cxp
      cres crn wcel cA cB cxp cB c2nd cA cB cxp cres wf c2nd cA cB cxp cres cA
      cB cxp wfn cA cB f2ndres cA cB cxp cB c2nd cA cB cxp cres ffn ax-mp cA cB
      cxp vx cv vy cv cop c2nd cA cB cxp cres fnfvelrn mpan eqeltrd sylbir ex
      exlimiv sylbi ssrdv cA cB cxp cB c2nd cA cB cxp cres wf c2nd cA cB cxp
      cres crn cB wss cA cB f2ndres cA cB cxp cB c2nd cA cB cxp cres frn ax-mp
      jctil c2nd cA cB cxp cres crn cB eqss sylibr cA cB f2ndres jctil cA cB
      cxp cB c2nd cA cB cxp cres dffo2 sylibr $.
  $}

  ${
    $d x y z w v $.  $d v w A $.
    $( Value of an alternate definition of the ` 1st ` function.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)
    1st2val $p |- ( { <. <. x , y >. , z >. | z = x } ` A ) = ( 1st ` A ) $=
      cA cvv cvv cxp wcel cA vz cv vx cv wceq vx vy vz coprab cfv cA c1st cfv
      wceq cA cvv cvv cxp wcel cA vw cv vv cv cop wceq vv wex vw wex cA vz cv
      vx cv wceq vx vy vz coprab cfv cA c1st cfv wceq vw vv cA elvv cA vw cv vv
      cv cop wceq cA vz cv vx cv wceq vx vy vz coprab cfv cA c1st cfv wceq vw
      vv cA vw cv vv cv cop wceq cA vz cv vx cv wceq vx vy vz coprab cfv vw cv
      cA c1st cfv cA vw cv vv cv cop wceq cA vz cv vx cv wceq vx vy vz coprab
      cfv vw cv vv cv cop vz cv vx cv wceq vx vy vz coprab cfv vw cv cA vw cv
      vv cv cop vz cv vx cv wceq vx vy vz coprab fveq2 vw cv vv cv vz cv vx cv
      wceq vx vy vz coprab co vw cv vv cv cop vz cv vx cv wceq vx vy vz coprab
      cfv vw cv vw cv vv cv vz cv vx cv wceq vx vy vz coprab df-ov vw cv cvv
      wcel vv cv cvv wcel vw cv vv cv vz cv vx cv wceq vx vy vz coprab co vw cv
      wceq vw vex vv vex vx vy vw cv vv cv cvv cvv vx cv vw cv vz cv vx cv wceq
      vx vy vz coprab vx cv vw cv wceq vy cv vv cv wceq simpl vx vy cvv cvv vx
      cv cmpt2 vz cv vx cv wceq vx vy vz coprab vx vy vz vx cv mpt2v eqcomi vw
      vex ovmpt2a mp2an eqtr3i syl6eq vw cv vv cv cA vw vex vv vex op1std
      eqtr4d exlimivv sylbi cA cvv cvv cxp wcel wn cA vz cv vx cv wceq vx vy vz
      coprab cfv cA csn cdm cuni cA c1st cfv cA cvv cvv cxp wcel wn cA vz cv vx
      cv wceq vx vy vz coprab cfv c0 cA csn cdm cuni cA cvv cvv cxp wcel cA vz
      cv vx cv wceq vx vy vz coprab cdm wcel cA vz cv vx cv wceq vx vy vz
      coprab cfv c0 wceq vz cv vx cv wceq vx vy vz coprab cdm cvv cvv cxp cA vx
      cv cvv wcel vy cv cvv wcel wa vx vy copab vz cv vx cv wceq vz wex vx vy
      copab cvv cvv cxp vz cv vx cv wceq vx vy vz coprab cdm vx cv cvv wcel vy
      cv cvv wcel wa vz cv vx cv wceq vz wex vx vy vx cv cvv wcel vy cv cvv
      wcel wa vz cv vx cv wceq vz wex vx cv cvv wcel vy cv cvv wcel vx vex vy
      vex pm3.2i vz vx a9ev 2th opabbii vx vy cvv cvv df-xp vz cv vx cv wceq vx
      vy vz dmoprab 3eqtr4ri eleq2i cA vz cv vx cv wceq vx vy vz coprab ndmfv
      sylnbir cA cvv cvv cxp wcel wn cA csn cdm cuni c0 cuni c0 cA cvv cvv cxp
      wcel wn cA csn cdm c0 cA cvv cvv cxp wcel cA csn cdm c0 cA cvv cvv cxp
      wcel cA csn cdm c0 wne cA dmsnn0 biimpri necon1bi unieqd uni0 syl6eq
      eqtr4d cA 1stval syl6eqr pm2.61i $.

    $( Value of an alternate definition of the ` 2nd ` function.  (Contributed
       by NM, 10-Aug-2006.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)
    2nd2val $p |- ( { <. <. x , y >. , z >. | z = y } ` A ) = ( 2nd ` A ) $=
      cA cvv cvv cxp wcel cA vz cv vy cv wceq vx vy vz coprab cfv cA c2nd cfv
      wceq cA cvv cvv cxp wcel cA vw cv vv cv cop wceq vv wex vw wex cA vz cv
      vy cv wceq vx vy vz coprab cfv cA c2nd cfv wceq vw vv cA elvv cA vw cv vv
      cv cop wceq cA vz cv vy cv wceq vx vy vz coprab cfv cA c2nd cfv wceq vw
      vv cA vw cv vv cv cop wceq cA vz cv vy cv wceq vx vy vz coprab cfv vv cv
      cA c2nd cfv cA vw cv vv cv cop wceq cA vz cv vy cv wceq vx vy vz coprab
      cfv vw cv vv cv cop vz cv vy cv wceq vx vy vz coprab cfv vv cv cA vw cv
      vv cv cop vz cv vy cv wceq vx vy vz coprab fveq2 vw cv vv cv vz cv vy cv
      wceq vx vy vz coprab co vw cv vv cv cop vz cv vy cv wceq vx vy vz coprab
      cfv vv cv vw cv vv cv vz cv vy cv wceq vx vy vz coprab df-ov vw cv cvv
      wcel vv cv cvv wcel vw cv vv cv vz cv vy cv wceq vx vy vz coprab co vv cv
      wceq vw vex vv vex vx vy vw cv vv cv cvv cvv vy cv vv cv vz cv vy cv wceq
      vx vy vz coprab vx cv vw cv wceq vy cv vv cv wceq simpr vx vy cvv cvv vy
      cv cmpt2 vz cv vy cv wceq vx vy vz coprab vx vy vz vy cv mpt2v eqcomi vv
      vex ovmpt2a mp2an eqtr3i syl6eq vw cv vv cv cA vw vex vv vex op2ndd
      eqtr4d exlimivv sylbi cA cvv cvv cxp wcel wn cA vz cv vy cv wceq vx vy vz
      coprab cfv cA csn crn cuni cA c2nd cfv cA cvv cvv cxp wcel wn cA vz cv vy
      cv wceq vx vy vz coprab cfv c0 cA csn crn cuni cA cvv cvv cxp wcel cA vz
      cv vy cv wceq vx vy vz coprab cdm wcel cA vz cv vy cv wceq vx vy vz
      coprab cfv c0 wceq vz cv vy cv wceq vx vy vz coprab cdm cvv cvv cxp cA vx
      cv cvv wcel vy cv cvv wcel wa vx vy copab vz cv vy cv wceq vz wex vx vy
      copab cvv cvv cxp vz cv vy cv wceq vx vy vz coprab cdm vx cv cvv wcel vy
      cv cvv wcel wa vz cv vy cv wceq vz wex vx vy vx cv cvv wcel vy cv cvv
      wcel wa vz cv vy cv wceq vz wex vx cv cvv wcel vy cv cvv wcel vx vex vy
      vex pm3.2i vz vy a9ev 2th opabbii vx vy cvv cvv df-xp vz cv vy cv wceq vx
      vy vz dmoprab 3eqtr4ri eleq2i cA vz cv vy cv wceq vx vy vz coprab ndmfv
      sylnbir cA cvv cvv cxp wcel wn cA csn crn cuni c0 cuni c0 cA cvv cvv cxp
      wcel wn cA csn crn c0 cA cvv cvv cxp wcel cA csn crn c0 cA cvv cvv cxp
      wcel cA csn crn c0 wne cA rnsnn0 biimpri necon1bi unieqd uni0 syl6eq
      eqtr4d cA 2ndval syl6eqr pm2.61i $.
  $}

  $( Composition of the first member function with another function.
     (Contributed by NM, 12-Oct-2007.) $)
  1stcof $p |- ( F : A --> ( B X. C ) -> ( 1st o. F ) : A --> B ) $=
    cA cB cC cxp cF wf c1st cF ccom cA wfn c1st cF ccom crn cB wss cA cB c1st
    cF ccom wf cA cB cC cxp cF wf c1st cvv wfn cA cvv cF wf c1st cF ccom cA wfn
    cvv cvv c1st wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp cA cB cC cxp cF
    wf cF cA wfn cA cvv cF wf cA cB cC cxp cF ffn cA cF dffn2 sylib cvv cA c1st
    cF fnfco sylancr cA cB cC cxp cF wf c1st cF ccom crn c1st cF crn cres crn
    cB c1st cF rnco cA cB cC cxp cF wf c1st cF crn cres crn c1st cB cC cxp cres
    crn cB cA cB cC cxp cF wf cF crn cB cC cxp wss c1st cF crn cres c1st cB cC
    cxp cres wss c1st cF crn cres crn c1st cB cC cxp cres crn wss cA cB cC cxp
    cF frn cF crn cB cC cxp c1st ssres2 c1st cF crn cres c1st cB cC cxp cres
    rnss 3syl cB cC cxp cB c1st cB cC cxp cres wf c1st cB cC cxp cres crn cB
    wss cB cC f1stres cB cC cxp cB c1st cB cC cxp cres frn ax-mp syl6ss
    syl5eqss cA cB c1st cF ccom df-f sylanbrc $.

  $( Composition of the first member function with another function.
     (Contributed by FL, 15-Oct-2012.) $)
  2ndcof $p |- ( F : A --> ( B X. C ) -> ( 2nd o. F ) : A --> C ) $=
    cA cB cC cxp cF wf c2nd cF ccom cA wfn c2nd cF ccom crn cC wss cA cC c2nd
    cF ccom wf cA cB cC cxp cF wf c2nd cvv wfn cA cvv cF wf c2nd cF ccom cA wfn
    cvv cvv c2nd wfo c2nd cvv wfn fo2nd cvv cvv c2nd fofn ax-mp cA cB cC cxp cF
    wf cF cA wfn cA cvv cF wf cA cB cC cxp cF ffn cA cF dffn2 sylib cvv cA c2nd
    cF fnfco sylancr cA cB cC cxp cF wf c2nd cF ccom crn c2nd cF crn cres crn
    cC c2nd cF rnco cA cB cC cxp cF wf c2nd cF crn cres crn c2nd cB cC cxp cres
    crn cC cA cB cC cxp cF wf cF crn cB cC cxp wss c2nd cF crn cres c2nd cB cC
    cxp cres wss c2nd cF crn cres crn c2nd cB cC cxp cres crn wss cA cB cC cxp
    cF frn cF crn cB cC cxp c2nd ssres2 c2nd cF crn cres c2nd cB cC cxp cres
    rnss 3syl cB cC cxp cC c2nd cB cC cxp cres wf c2nd cB cC cxp cres crn cC
    wss cB cC f2ndres cB cC cxp cC c2nd cB cC cxp cres frn ax-mp syl6ss
    syl5eqss cA cC c2nd cF ccom df-f sylanbrc $.

  ${
    $d A b c $.  $d B b c $.  $d C b c $.
    $( Location of the first element of a Cartesian product.  (Contributed by
       Jeff Madsen, 2-Sep-2009.) $)
    xp1st $p |- ( A e. ( B X. C ) -> ( 1st ` A ) e. B ) $=
      cA cB cC cxp wcel cA vb cv vc cv cop wceq vb cv cB wcel vc cv cC wcel wa
      wa vc wex vb wex cA c1st cfv cB wcel vb vc cA cB cC elxp cA vb cv vc cv
      cop wceq vb cv cB wcel vc cv cC wcel wa wa cA c1st cfv cB wcel vb vc cA
      vb cv vc cv cop wceq vb cv cB wcel cA c1st cfv cB wcel vc cv cC wcel cA
      vb cv vc cv cop wceq cA c1st cfv cB wcel vb cv cB wcel cA vb cv vc cv cop
      wceq cA c1st cfv vb cv cB vb cv vc cv cA vb vex vc vex op1std eleq1d
      biimpar adantrr exlimivv sylbi $.
  $}

  ${
    $d A b c $.  $d B b c $.  $d C b c $.
    $( Location of the second element of a Cartesian product.  (Contributed by
       Jeff Madsen, 2-Sep-2009.) $)
    xp2nd $p |- ( A e. ( B X. C ) -> ( 2nd ` A ) e. C ) $=
      cA cB cC cxp wcel cA vb cv vc cv cop wceq vb cv cB wcel vc cv cC wcel wa
      wa vc wex vb wex cA c2nd cfv cC wcel vb vc cA cB cC elxp cA vb cv vc cv
      cop wceq vb cv cB wcel vc cv cC wcel wa wa cA c2nd cfv cC wcel vb vc cA
      vb cv vc cv cop wceq vc cv cC wcel cA c2nd cfv cC wcel vb cv cB wcel cA
      vb cv vc cv cop wceq cA c2nd cfv cC wcel vc cv cC wcel cA vb cv vc cv cop
      wceq cA c2nd cfv vc cv cC vb cv vc cv cA vb vex vc vex op2ndd eleq1d
      biimpar adantrl exlimivv sylbi $.
  $}

  $( Membership in a cross product.  This version requires no quantifiers or
     dummy variables.  See also ~ elxp4 .  (Contributed by NM, 9-Oct-2004.) $)
  elxp6 $p |- ( A e. ( B X. C ) <-> ( A = <. ( 1st ` A ) , ( 2nd ` A ) >.
               /\ ( ( 1st ` A ) e. B /\ ( 2nd ` A ) e. C ) ) ) $=
    cA cB cC cxp wcel cA cA csn cdm cuni cA csn crn cuni cop wceq cA csn cdm
    cuni cB wcel cA csn crn cuni cC wcel wa wa cA cA c1st cfv cA c2nd cfv cop
    wceq cA c1st cfv cB wcel cA c2nd cfv cC wcel wa wa cA cB cC elxp4 cA cA
    c1st cfv cA c2nd cfv cop wceq cA cA csn cdm cuni cA csn crn cuni cop wceq
    cA c1st cfv cB wcel cA c2nd cfv cC wcel wa cA csn cdm cuni cB wcel cA csn
    crn cuni cC wcel wa cA c1st cfv cA c2nd cfv cop cA csn cdm cuni cA csn crn
    cuni cop cA cA c1st cfv cA csn cdm cuni cA c2nd cfv cA csn crn cuni cA
    1stval cA 2ndval opeq12i eqeq2i cA c1st cfv cB wcel cA csn cdm cuni cB wcel
    cA c2nd cfv cC wcel cA csn crn cuni cC wcel cA c1st cfv cA csn cdm cuni cB
    cA 1stval eleq1i cA c2nd cfv cA csn crn cuni cC cA 2ndval eleq1i anbi12i
    anbi12i bitr4i $.

  $( Membership in a cross product.  This version requires no quantifiers or
     dummy variables.  See also ~ elxp4 .  (Contributed by NM, 19-Aug-2006.) $)
  elxp7 $p |- ( A e. ( B X. C ) <-> ( A e. ( _V X. _V )
               /\ ( ( 1st ` A ) e. B /\ ( 2nd ` A ) e. C ) ) ) $=
    cA cB cC cxp wcel cA cA c1st cfv cA c2nd cfv cop wceq cA c1st cfv cB wcel
    cA c2nd cfv cC wcel wa wa cA cvv cvv cxp wcel cA c1st cfv cB wcel cA c2nd
    cfv cC wcel wa wa cA cB cC elxp6 cA cvv cvv cxp wcel cA cA c1st cfv cA c2nd
    cfv cop wceq cA c1st cfv cB wcel cA c2nd cfv cC wcel wa cA cvv cvv cxp wcel
    cA cA c1st cfv cA c2nd cfv cop wceq cA c1st cfv cvv wcel cA c2nd cfv cvv
    wcel wa cA c1st cfv cvv wcel cA c2nd cfv cvv wcel cA c1st fvex cA c2nd fvex
    pm3.2i cA cvv cvv elxp6 mpbiran2 anbi1i bitr4i $.

  ${
    $d A x y $.  $d B x y $.  $d C x y $.  $d D x y $.
    $( Difference of Cartesian products, expressed in terms of a union of
       Cartesian products of differences.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by Mario Carneiro, 26-Jun-2014.) $)
    difxp $p |- ( ( C X. D ) \ ( A X. B ) ) =
                ( ( ( C \ A ) X. D ) u. ( C X. ( D \ B ) ) ) $=
      vx vy cC cD cxp cA cB cxp cdif cC cA cdif cD cxp cC cD cB cdif cxp cun cC
      cD cxp cA cB cxp cdif cC cD cxp wss cC cD cxp wrel cC cD cxp cA cB cxp
      cdif wrel cC cD cxp cA cB cxp difss cC cD relxp cC cD cxp cA cB cxp cdif
      cC cD cxp relss mp2 cC cA cdif cD cxp cC cD cB cdif cxp cun wrel cC cA
      cdif cD cxp wrel cC cD cB cdif cxp wrel cC cA cdif cD relxp cC cD cB cdif
      relxp cC cA cdif cD cxp cC cD cB cdif cxp relun mpbir2an vx cv vy cv cop
      cC cD cxp wcel vx cv vy cv cop cA cB cxp wcel wn wa vx cv vy cv cop cC cA
      cdif cD cxp wcel vx cv vy cv cop cC cD cB cdif cxp wcel wo vx cv vy cv
      cop cC cD cxp cA cB cxp cdif wcel vx cv vy cv cop cC cA cdif cD cxp cC cD
      cB cdif cxp cun wcel vx cv cC wcel vy cv cD wcel wa vx cv cA wcel vy cv
      cB wcel wa wn wa vx cv cC wcel vy cv cD wcel wa vx cv cA wcel wn wa vx cv
      cC wcel vy cv cD wcel wa vy cv cB wcel wn wa wo vx cv vy cv cop cC cD cxp
      wcel vx cv vy cv cop cA cB cxp wcel wn wa vx cv vy cv cop cC cA cdif cD
      cxp wcel vx cv vy cv cop cC cD cB cdif cxp wcel wo vx cv cC wcel vy cv cD
      wcel wa vx cv cA wcel vy cv cB wcel wa wn wa vx cv cC wcel vy cv cD wcel
      wa vx cv cA wcel wn vy cv cB wcel wn wo wa vx cv cC wcel vy cv cD wcel wa
      vx cv cA wcel wn wa vx cv cC wcel vy cv cD wcel wa vy cv cB wcel wn wa wo
      vx cv cA wcel vy cv cB wcel wa wn vx cv cA wcel wn vy cv cB wcel wn wo vx
      cv cC wcel vy cv cD wcel wa vx cv cA wcel vy cv cB wcel ianor anbi2i vx
      cv cC wcel vy cv cD wcel wa vx cv cA wcel wn vy cv cB wcel wn andi bitri
      vx cv vy cv cop cC cD cxp wcel vx cv cC wcel vy cv cD wcel wa vx cv vy cv
      cop cA cB cxp wcel wn vx cv cA wcel vy cv cB wcel wa wn vx cv vy cv cC cD
      opelxp vx cv vy cv cop cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa vx
      cv vy cv cA cB opelxp notbii anbi12i vx cv vy cv cop cC cA cdif cD cxp
      wcel vx cv cC wcel vy cv cD wcel wa vx cv cA wcel wn wa vx cv vy cv cop
      cC cD cB cdif cxp wcel vx cv cC wcel vy cv cD wcel wa vy cv cB wcel wn wa
      vx cv vy cv cop cC cA cdif cD cxp wcel vx cv cC cA cdif wcel vy cv cD
      wcel wa vx cv cC wcel vy cv cD wcel wa vx cv cA wcel wn wa vx cv vy cv cC
      cA cdif cD opelxp vx cv cC cA cdif wcel vy cv cD wcel wa vx cv cC wcel vx
      cv cA wcel wn wa vy cv cD wcel wa vx cv cC wcel vy cv cD wcel wa vx cv cA
      wcel wn wa vx cv cC cA cdif wcel vx cv cC wcel vx cv cA wcel wn wa vy cv
      cD wcel vx cv cC cA eldif anbi1i vx cv cC wcel vx cv cA wcel wn vy cv cD
      wcel an32 bitri bitri vx cv cC wcel vy cv cD cB cdif wcel wa vx cv cC
      wcel vy cv cD wcel vy cv cB wcel wn wa wa vx cv vy cv cop cC cD cB cdif
      cxp wcel vx cv cC wcel vy cv cD wcel wa vy cv cB wcel wn wa vy cv cD cB
      cdif wcel vy cv cD wcel vy cv cB wcel wn wa vx cv cC wcel vy cv cD cB
      eldif anbi2i vx cv vy cv cC cD cB cdif opelxp vx cv cC wcel vy cv cD wcel
      vy cv cB wcel wn anass 3bitr4i orbi12i 3bitr4i vx cv vy cv cop cC cD cxp
      cA cB cxp eldif vx cv vy cv cop cC cA cdif cD cxp cC cD cB cdif cxp elun
      3bitr4i eqrelriiv $.
  $}

  $( Difference law for cross product.  (Contributed by Scott Fenton,
     18-Feb-2013.)  (Revised by Mario Carneiro, 26-Jun-2014.) $)
  difxp1 $p |- ( ( A \ B ) X. C ) = ( ( A X. C ) \ ( B X. C ) ) $=
    cA cC cxp cB cC cxp cdif cA cB cdif cC cxp cA cC cC cdif cxp cun cA cB cdif
    cC cxp c0 cun cA cB cdif cC cxp cB cC cA cC difxp cA cC cC cdif cxp c0 cA
    cB cdif cC cxp cA cC cC cdif cxp cA c0 cxp c0 cC cC cdif c0 cA cC difid
    xpeq2i cA xp0 eqtri uneq2i cA cB cdif cC cxp un0 3eqtrri $.

  $( Difference law for cross product.  (Contributed by Scott Fenton,
     18-Feb-2013.)  (Revised by Mario Carneiro, 26-Jun-2014.) $)
  difxp2 $p |- ( A X. ( B \ C ) ) = ( ( A X. B ) \ ( A X. C ) ) $=
    cA cB cxp cA cC cxp cdif cA cA cdif cB cxp cA cB cC cdif cxp cun c0 cA cB
    cC cdif cxp cun cA cB cC cdif cxp cA cC cA cB difxp cA cA cdif cB cxp c0 cA
    cB cC cdif cxp cA cA cdif cB cxp c0 cB cxp c0 cA cA cdif c0 cB cA difid
    xpeq1i cB xp0r eqtri uneq1i c0 cA cB cC cdif cxp cun cA cB cC cdif cxp c0
    cun cA cB cC cdif cxp c0 cA cB cC cdif cxp uncom cA cB cC cdif cxp un0
    eqtri 3eqtrri $.

  $( Equality with an ordered pair.  (Contributed by NM, 15-Dec-2008.)
     (Revised by Mario Carneiro, 23-Feb-2014.) $)
  eqopi $p |- ( ( A e. ( V X. W ) /\ ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) )
              -> A = <. B , C >. ) $=
    cA cV cW cxp wcel cA cvv cvv cxp wcel cA c1st cfv cB wceq cA c2nd cfv cC
    wceq wa cA cB cC cop wceq cV cW cxp cvv cvv cxp cA cV cW xpss sseli cA cvv
    cvv cxp wcel cA c1st cfv cB wceq cA c2nd cfv cC wceq wa cA cA c1st cfv cA
    c2nd cfv cop cB cC cop cA cvv cvv cxp wcel cA cA c1st cfv cA c2nd cfv cop
    wceq cA c1st cfv cvv wcel cA c2nd cfv cvv wcel wa cA cvv cvv elxp6 simplbi
    cA c1st cfv cA c2nd cfv cB cC opeq12 sylan9eq sylan $.

  ${
    $d x A $.  $d x B $.
    $( Representation of cross product based on ordered pair component
       functions.  (Contributed by NM, 16-Sep-2006.) $)
    xp2 $p |- ( A X. B ) = { x e. ( _V X. _V ) | ( ( 1st ` x ) e. A /\
              ( 2nd ` x ) e. B ) } $=
      cA cB cxp vx cv cvv cvv cxp wcel vx cv c1st cfv cA wcel vx cv c2nd cfv cB
      wcel wa wa vx cab vx cv c1st cfv cA wcel vx cv c2nd cfv cB wcel wa vx cvv
      cvv cxp crab vx cv cvv cvv cxp wcel vx cv c1st cfv cA wcel vx cv c2nd cfv
      cB wcel wa wa vx cA cB cxp vx cv cA cB elxp7 abbi2i vx cv c1st cfv cA
      wcel vx cv c2nd cfv cB wcel wa vx cvv cvv cxp df-rab eqtr4i $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( The membership relation for a cross product is inherited by union.
       (Contributed by NM, 16-Sep-2006.) $)
    unielxp $p |- ( A e. ( B X. C ) -> U. A e. U. ( B X. C ) ) $=
      cA cB cC cxp wcel cA cvv cvv cxp wcel cA c1st cfv cB wcel cA c2nd cfv cC
      wcel wa wa cA cuni cB cC cxp cuni wcel cA cB cC elxp7 cA cuni cA wcel cA
      cvv cvv cxp wcel cA c1st cfv cB wcel cA c2nd cfv cC wcel wa wa cA cuni cB
      cC cxp cuni wcel cA cvv cvv cxp wcel cA cuni cA wcel cA c1st cfv cB wcel
      cA c2nd cfv cC wcel wa cA elvvuni adantr cA cuni cA wcel cA cvv cvv cxp
      wcel cA c1st cfv cB wcel cA c2nd cfv cC wcel wa wa wa cA cuni vx cv cvv
      cvv cxp wcel vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa wa vx cab
      cuni cB cC cxp cuni cA cuni cA wcel cA cvv cvv cxp wcel cA c1st cfv cB
      wcel cA c2nd cfv cC wcel wa wa wa cA cuni vx cv wcel vx cv cvv cvv cxp
      wcel vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa wa wa vx wex cA
      cuni vx cv cvv cvv cxp wcel vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel
      wa wa vx cab cuni wcel cA cvv cvv cxp wcel cA cuni cA wcel cA cvv cvv cxp
      wcel cA c1st cfv cB wcel cA c2nd cfv cC wcel wa wa wa cA cuni vx cv wcel
      vx cv cvv cvv cxp wcel vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa
      wa wa vx wex cA cuni cA wcel cA cvv cvv cxp wcel cA c1st cfv cB wcel cA
      c2nd cfv cC wcel wa simprl cA cuni vx cv wcel vx cv cvv cvv cxp wcel vx
      cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa wa wa cA cuni cA wcel cA
      cvv cvv cxp wcel cA c1st cfv cB wcel cA c2nd cfv cC wcel wa wa wa vx cA
      cvv cvv cxp vx cv cA wceq cA cuni vx cv wcel cA cuni cA wcel vx cv cvv
      cvv cxp wcel vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa wa cA cvv
      cvv cxp wcel cA c1st cfv cB wcel cA c2nd cfv cC wcel wa wa vx cv cA cA
      cuni eleq2 vx cv cA wceq vx cv cvv cvv cxp wcel cA cvv cvv cxp wcel vx cv
      c1st cfv cB wcel vx cv c2nd cfv cC wcel wa cA c1st cfv cB wcel cA c2nd
      cfv cC wcel wa vx cv cA cvv cvv cxp eleq1 vx cv cA wceq vx cv c1st cfv cB
      wcel cA c1st cfv cB wcel vx cv c2nd cfv cC wcel cA c2nd cfv cC wcel vx cv
      cA wceq vx cv c1st cfv cA c1st cfv cB vx cv cA c1st fveq2 eleq1d vx cv cA
      wceq vx cv c2nd cfv cA c2nd cfv cC vx cv cA c2nd fveq2 eleq1d anbi12d
      anbi12d anbi12d spcegv mpcom vx cv cvv cvv cxp wcel vx cv c1st cfv cB
      wcel vx cv c2nd cfv cC wcel wa wa vx cA cuni eluniab sylibr cB cC cxp vx
      cv cvv cvv cxp wcel vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa wa
      vx cab cB cC cxp vx cv c1st cfv cB wcel vx cv c2nd cfv cC wcel wa vx cvv
      cvv cxp crab vx cv cvv cvv cxp wcel vx cv c1st cfv cB wcel vx cv c2nd cfv
      cC wcel wa wa vx cab vx cB cC xp2 vx cv c1st cfv cB wcel vx cv c2nd cfv
      cC wcel wa vx cvv cvv cxp df-rab eqtri unieqi syl6eleqr mpancom sylbi $.
  $}

  $( Reconstruction of a member of a cross product in terms of its ordered pair
     components.  (Contributed by NM, 20-Oct-2013.) $)
  1st2nd2 $p |- ( A e. ( B X. C ) -> A = <. ( 1st ` A ) , ( 2nd ` A ) >. ) $=
    cA cB cC cxp wcel cA cA c1st cfv cA c2nd cfv cop wceq cA c1st cfv cB wcel
    cA c2nd cfv cC wcel wa cA cB cC elxp6 simplbi $.

  $( Reconstruction of an ordered pair in terms of its components.
     (Contributed by NM, 25-Feb-2014.) $)
  1st2ndb $p |- ( A e. ( _V X. _V )
      <-> A = <. ( 1st ` A ) , ( 2nd ` A ) >. ) $=
    cA cvv cvv cxp wcel cA cA c1st cfv cA c2nd cfv cop wceq cA cvv cvv 1st2nd2
    cA cA c1st cfv cA c2nd cfv cop wceq cA cA c1st cfv cA c2nd cfv cop cvv cvv
    cxp cA cA c1st cfv cA c2nd cfv cop wceq id cA c1st cfv cA c2nd cfv cA c1st
    fvex cA c2nd fvex opelvv syl6eqel impbii $.

  $( An ordered pair theorem for members of cross products.  (Contributed by
     NM, 20-Jun-2007.) $)
  xpopth $p |- ( ( A e. ( C X. D ) /\ B e. ( R X. S ) ) ->
       ( ( ( 1st ` A ) = ( 1st ` B ) /\
     ( 2nd ` A ) = ( 2nd ` B ) ) <-> A = B ) ) $=
    cA cC cD cxp wcel cB cR cS cxp wcel wa cA cB wceq cA c1st cfv cA c2nd cfv
    cop cB c1st cfv cB c2nd cfv cop wceq cA c1st cfv cB c1st cfv wceq cA c2nd
    cfv cB c2nd cfv wceq wa cA cC cD cxp wcel cB cR cS cxp wcel cA cA c1st cfv
    cA c2nd cfv cop cB cB c1st cfv cB c2nd cfv cop cA cC cD 1st2nd2 cB cR cS
    1st2nd2 eqeqan12d cA c1st cfv cA c2nd cfv cB c1st cfv cB c2nd cfv cA c1st
    fvex cA c2nd fvex opth syl6rbb $.

  $( Two ways to express equality with an ordered pair.  (Contributed by NM,
     3-Sep-2007.)  (Proof shortened by Mario Carneiro, 26-Apr-2015.) $)
  eqop $p |- ( A e. ( V X. W ) -> ( A = <. B , C >.
            <-> ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) ) $=
    cA cV cW cxp wcel cA cB cC cop wceq cA c1st cfv cA c2nd cfv cop cB cC cop
    wceq cA c1st cfv cB wceq cA c2nd cfv cC wceq wa cA cV cW cxp wcel cA cA
    c1st cfv cA c2nd cfv cop cB cC cop cA cV cW 1st2nd2 eqeq1d cA c1st cfv cA
    c2nd cfv cB cC cA c1st fvex cA c2nd fvex opth syl6bb $.

  ${
    eqop2.1 $e |- B e. _V $.
    eqop2.2 $e |- C e. _V $.
    $( Two ways to express equality with an ordered pair.  (Contributed by NM,
       25-Feb-2014.) $)
    eqop2 $p |- ( A = <. B , C >.
       <-> ( A e. ( _V X. _V ) /\ ( ( 1st ` A ) = B /\ ( 2nd ` A ) = C ) ) ) $=
      cA cB cC cop wceq cA cvv cvv cxp wcel cA c1st cfv cB wceq cA c2nd cfv cC
      wceq wa cA cB cC cop wceq cA cvv cvv cxp wcel cB cC cop cvv cvv cxp wcel
      cB cC eqop2.1 eqop2.2 opelvv cA cB cC cop cvv cvv cxp eleq1 mpbiri cA cB
      cC cvv cvv eqop biadan2 $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Two ways of expressing that an element is the first member of an ordered
       pair.  (Contributed by NM, 22-Sep-2013.)  (Revised by Mario Carneiro,
       23-Feb-2014.) $)
    op1steq $p |- ( A e. ( V X. W )
         -> ( ( 1st ` A ) = B <-> E. x A = <. B , x >. ) ) $=
      cA cV cW cxp wcel cA cvv cvv cxp wcel cA c1st cfv cB wceq cA cB vx cv cop
      wceq vx wex wb cV cW cxp cvv cvv cxp cA cV cW xpss sseli cA cvv cvv cxp
      wcel cA c1st cfv cB wceq cA cB vx cv cop wceq vx wex cA cvv cvv cxp wcel
      cA c1st cfv cB wceq cA cB vx cv cop wceq vx wex cA cvv cvv cxp wcel cA
      c1st cfv cB wceq wa cA cB cA c2nd cfv cop wceq cA cB vx cv cop wceq vx
      wex cA cvv cvv cxp wcel cA c1st cfv cB wceq cA c2nd cfv cA c2nd cfv wceq
      cA cB cA c2nd cfv cop wceq cA c2nd cfv eqid cA cB cA c2nd cfv cvv cvv
      eqopi mpanr2 cA cB vx cv cop wceq cA cB cA c2nd cfv cop wceq vx cA c2nd
      cfv cA c2nd fvex vx cv cA c2nd cfv wceq cB vx cv cop cB cA c2nd cfv cop
      cA vx cv cA c2nd cfv cB opeq2 eqeq2d spcev syl ex cA cvv cvv cxp wcel cA
      cB vx cv cop wceq cA c1st cfv cB wceq vx cA cvv cvv cxp wcel cA cB vx cv
      cop wceq cA c1st cfv cB wceq cA c2nd cfv vx cv wceq wa cA c1st cfv cB
      wceq cA cB vx cv cvv cvv eqop cA c1st cfv cB wceq cA c2nd cfv vx cv wceq
      simpl syl6bi exlimdv impbid syl $.
  $}

  $( Swap the members of an ordered pair.  (Contributed by NM, 31-Dec-2014.) $)
  2nd1st $p |- ( A e. ( B X. C ) ->
    U. `' { A } = <. ( 2nd ` A ) , ( 1st ` A ) >. ) $=
    cA cB cC cxp wcel cA csn ccnv cuni cA c1st cfv cA c2nd cfv cop csn ccnv
    cuni cA c2nd cfv cA c1st cfv cop cA cB cC cxp wcel cA csn ccnv cA c1st cfv
    cA c2nd cfv cop csn ccnv cA cB cC cxp wcel cA csn cA c1st cfv cA c2nd cfv
    cop csn cA cB cC cxp wcel cA cA c1st cfv cA c2nd cfv cop cA cB cC 1st2nd2
    sneqd cnveqd unieqd cA c1st cfv cA c2nd cfv opswap syl6eq $.

  $( Reconstruction of a member of a relation in terms of its ordered pair
     components.  (Contributed by NM, 29-Aug-2006.) $)
  1st2nd $p |- ( ( Rel B /\ A e. B ) ->
               A = <. ( 1st ` A ) , ( 2nd ` A ) >. ) $=
    cB wrel cA cB wcel wa cA cvv cvv cxp wcel cA cA c1st cfv cA c2nd cfv cop
    wceq cB wrel cB cvv cvv cxp wss cA cB wcel cA cvv cvv cxp wcel cB df-rel cB
    cvv cvv cxp cA ssel2 sylanb cA cvv cvv 1st2nd2 syl $.

  $( The first ordered pair component of a member of a relation belongs to the
     domain of the relation.  (Contributed by NM, 17-Sep-2006.) $)
  1stdm $p |- ( ( Rel R /\ A e. R ) -> ( 1st ` A ) e. dom R ) $=
    cR wrel cA cR wcel wa cA c1st cfv cA cint cint cR cdm cR wrel cA cR wcel wa
    cA cvv cvv cxp wcel cA c1st cfv cA cint cint wceq cR wrel cR cvv cvv cxp cA
    cR wrel cR cvv cvv cxp wss cR df-rel biimpi sselda cA 1stval2 syl cR cA
    elreldm eqeltrd $.

  $( The second ordered pair component of a member of a relation belongs to the
     range of the relation.  (Contributed by NM, 17-Sep-2006.) $)
  2ndrn $p |- ( ( Rel R /\ A e. R ) -> ( 2nd ` A ) e. ran R ) $=
    cR wrel cA cR wcel wa cA c1st cfv cA c2nd cfv cop cR wcel cA c2nd cfv cR
    crn wcel cR wrel cA cR wcel wa cA cA c1st cfv cA c2nd cfv cop cR cA cR
    1st2nd cR wrel cA cR wcel simpr eqeltrrd cA c1st cfv cA c2nd cfv cR cA c1st
    fvex cA c2nd fvex opelrn syl $.

  $( Express an element of a relation as a relationship between first and
     second components.  (Contributed by Mario Carneiro, 22-Jun-2016.) $)
  1st2ndbr $p |- ( ( Rel B /\ A e. B ) -> ( 1st ` A ) B ( 2nd ` A ) ) $=
    cB wrel cA cB wcel wa cA c1st cfv cA c2nd cfv cop cB wcel cA c1st cfv cA
    c2nd cfv cB wbr cB wrel cA cB wcel wa cA cA c1st cfv cA c2nd cfv cop cB cA
    cB 1st2nd cB wrel cA cB wcel simpr eqeltrrd cA c1st cfv cA c2nd cfv cB
    df-br sylibr $.

  ${
    $d x y A $.  $d x y B $.
    $( Two ways of expressing membership in the domain of a relation.
       (Contributed by NM, 22-Sep-2013.) $)
    releldm2 $p |- ( Rel A
         -> ( B e. dom A <-> E. x e. A ( 1st ` x ) = B ) ) $=
      cA wrel cB cA cdm wcel vx cv c1st cfv cB wceq vx cA wrex cA wrel cB cvv
      wcel wa cB cA cdm wcel cB cvv wcel cA wrel cB cA cdm elex anim2i vx cv
      c1st cfv cB wceq vx cA wrex cB cvv wcel cA wrel vx cv c1st cfv cB wceq cB
      cvv wcel vx cA vx cv c1st cfv cB wceq cB vx cv c1st cfv cvv vx cv c1st
      cfv cB wceq id vx cv c1st fvex syl6eqelr rexlimivw anim2i cA wrel cB cvv
      wcel wa cB cA cdm wcel cB vy cv cop cA wcel vy wex vx cv c1st cfv cB wceq
      vx cA wrex cB cvv wcel cB cA cdm wcel cB vy cv cop cA wcel vy wex wb cA
      wrel vy cB cA cvv eldm2g adantl cA wrel cB cvv wcel wa vx cv c1st cfv cB
      wceq vx cA wrex vx cv cB vy cv cop wceq vy wex vx cA wrex cB vy cv cop cA
      wcel vy wex cA wrel vx cv c1st cfv cB wceq vx cA wrex vx cv cB vy cv cop
      wceq vy wex vx cA wrex wb cB cvv wcel cA wrel vx cv c1st cfv cB wceq vx
      cv cB vy cv cop wceq vy wex vx cA cA wrel vx cv cA wcel wa vx cv cvv cvv
      cxp wcel vx cv c1st cfv cB wceq vx cv cB vy cv cop wceq vy wex wb cA wrel
      vx cv cA wcel vx cv cvv cvv cxp wcel cA wrel cA cvv cvv cxp wss vx cv cA
      wcel vx cv cvv cvv cxp wcel wi cA df-rel cA cvv cvv cxp vx cv ssel sylbi
      imp vy vx cv cB cvv cvv op1steq syl rexbidva adantr vx cv cB vy cv cop
      wceq vy wex vx cA wrex vx cv cB vy cv cop wceq vx cA wrex vy wex cB vy cv
      cop cA wcel vy wex vx cv cB vy cv cop wceq vx vy cA rexcom4 cB vy cv cop
      cA wcel vx cv cB vy cv cop wceq vx cA wrex vy vx cB vy cv cop cA risset
      exbii bitr4i syl6bb bitr4d pm5.21nd $.
  $}

  ${
    $d x y z A $.
    $( An expression for the domain of a relation.  (Contributed by NM,
       22-Sep-2013.) $)
    reldm $p |- ( Rel A -> dom A = ran ( x e. A |-> ( 1st ` x ) ) ) $=
      cA wrel vy cA cdm vx cA vx cv c1st cfv cmpt crn cA wrel vy cv cA cdm wcel
      vz cv c1st cfv vy cv wceq vz cA wrex vy cv vx cA vx cv c1st cfv cmpt crn
      wcel vz cA vy cv releldm2 vy cv vx cA vx cv c1st cfv cmpt crn wcel vz cv
      vx cA vx cv c1st cfv cmpt cfv vy cv wceq vz cA wrex cA wrel vz cv c1st
      cfv vy cv wceq vz cA wrex vx cA vx cv c1st cfv cmpt cA wfn vy cv vx cA vx
      cv c1st cfv cmpt crn wcel vz cv vx cA vx cv c1st cfv cmpt cfv vy cv wceq
      vz cA wrex wb vx cA vx cv c1st cfv vx cA vx cv c1st cfv cmpt vx cv c1st
      fvex vx cA vx cv c1st cfv cmpt eqid fnmpti vz cA vy cv vx cA vx cv c1st
      cfv cmpt fvelrnb ax-mp vz cv vx cA vx cv c1st cfv cmpt cfv vy cv wceq vz
      cA wrex vz cv c1st cfv vy cv wceq vz cA wrex wb cA wrel vz cv vx cA vx cv
      c1st cfv cmpt cfv vy cv wceq vz cv c1st cfv vy cv wceq vz cA vz cv cA
      wcel vz cv vx cA vx cv c1st cfv cmpt cfv vz cv c1st cfv vy cv vx vz cv vx
      cv c1st cfv vz cv c1st cfv cA vx cA vx cv c1st cfv cmpt vx cv vz cv c1st
      fveq2 vx cA vx cv c1st cfv cmpt eqid vz cv c1st fvex fvmpt eqeq1d rexbiia
      a1i syl5rbb bitrd eqrdv $.
  $}

  $( Equality theorem for substitution of a class for an ordered pair (analog
     of ~ sbceq1a that avoids the existential quantifiers of ~ copsexg ).
     (Contributed by NM, 19-Aug-2006.)  (Revised by Mario Carneiro,
     31-Aug-2015.) $)
  sbcopeq1a $p |- ( A = <. x , y >. ->
      ( [. ( 1st ` A ) / x ]. [. ( 2nd ` A ) / y ]. ph <-> ph ) ) $=
    cA vx cv vy cv cop wceq wph wph vy cA c2nd cfv wsbc wph vy cA c2nd cfv wsbc
    vx cA c1st cfv wsbc cA vx cv vy cv cop wceq vy cv cA c2nd cfv wceq wph wph
    vy cA c2nd cfv wsbc wb cA vx cv vy cv cop wceq cA c2nd cfv vy cv vx cv vy
    cv cA vx vex vy vex op2ndd eqcomd wph vy cA c2nd cfv sbceq1a syl cA vx cv
    vy cv cop wceq vx cv cA c1st cfv wceq wph vy cA c2nd cfv wsbc wph vy cA
    c2nd cfv wsbc vx cA c1st cfv wsbc wb cA vx cv vy cv cop wceq cA c1st cfv vx
    cv vx cv vy cv cA vx vex vy vex op1std eqcomd wph vy cA c2nd cfv wsbc vx cA
    c1st cfv sbceq1a syl bitr2d $.

  $( Equality theorem for substitution of a class ` A ` for an ordered pair
     ` <. x , y >. ` in ` B ` (analog of ~ csbeq1a ).  (Contributed by NM,
     19-Aug-2006.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
  csbopeq1a $p |- ( A = <. x , y >. ->
      [_ ( 1st ` A ) / x ]_ [_ ( 2nd ` A ) / y ]_ B = B ) $=
    cA vx cv vy cv cop wceq cB vy cA c2nd cfv cB csb vx cA c1st cfv vy cA c2nd
    cfv cB csb csb cA vx cv vy cv cop wceq vy cv cA c2nd cfv wceq cB vy cA c2nd
    cfv cB csb wceq cA vx cv vy cv cop wceq cA c2nd cfv vy cv vx cv vy cv cA vx
    vex vy vex op2ndd eqcomd vy cA c2nd cfv cB csbeq1a syl cA vx cv vy cv cop
    wceq vx cv cA c1st cfv wceq vy cA c2nd cfv cB csb vx cA c1st cfv vy cA c2nd
    cfv cB csb csb wceq cA vx cv vy cv cop wceq cA c1st cfv vx cv vx cv vy cv
    cA vx vex vy vex op1std eqcomd vx cA c1st cfv vy cA c2nd cfv cB csb csbeq1a
    syl eqtr2d $.

  ${
    $d z ph $.  $d x y z $.
    $( A way to define an ordered-pair class abstraction without using
       existential quantifiers.  (Contributed by NM, 18-Aug-2006.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
    dfopab2 $p |- { <. x , y >. | ph } = { z e. ( _V X. _V ) |
                  [. ( 1st ` z ) / x ]. [. ( 2nd ` z ) / y ]. ph } $=
      vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cab vz cv cvv cvv cxp
      wcel wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc wa vz cab wph vx
      vy copab wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc vz cvv cvv cxp
      crab vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cv cvv cvv cxp
      wcel wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc wa vz vz cv vx cv
      vy cv cop wceq vy wex wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc
      wa vx wex vz cv vx cv vy cv cop wceq vy wex vx wex wph vy vz cv c2nd cfv
      wsbc vx vz cv c1st cfv wsbc wa vz cv vx cv vy cv cop wceq wph wa vy wex
      vx wex vz cv cvv cvv cxp wcel wph vy vz cv c2nd cfv wsbc vx vz cv c1st
      cfv wsbc wa vz cv vx cv vy cv cop wceq vy wex wph vy vz cv c2nd cfv wsbc
      vx vz cv c1st cfv wsbc vx wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv
      nfsbc1v 19.41 vz cv vx cv vy cv cop wceq wph wa vy wex vz cv vx cv vy cv
      cop wceq vy wex wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc wa vx
      vz cv vx cv vy cv cop wceq wph wa vy wex vz cv vx cv vy cv cop wceq wph
      vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc wa vy wex vz cv vx cv vy cv
      cop wceq vy wex wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc wa vz
      cv vx cv vy cv cop wceq wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc
      wa vz cv vx cv vy cv cop wceq wph wa vy vz cv vx cv vy cv cop wceq wph vy
      vz cv c2nd cfv wsbc vx vz cv c1st cfv wsbc wph wph vx vy vz cv sbcopeq1a
      pm5.32i exbii vz cv vx cv vy cv cop wceq wph vy vz cv c2nd cfv wsbc vx vz
      cv c1st cfv wsbc vy wph vy vz cv c2nd cfv wsbc vy vx vz cv c1st cfv vy vz
      cv c1st cfv nfcv wph vy vz cv c2nd cfv nfsbc1v nfsbc 19.41 bitr3i exbii
      vz cv cvv cvv cxp wcel vz cv vx cv vy cv cop wceq vy wex vx wex wph vy vz
      cv c2nd cfv wsbc vx vz cv c1st cfv wsbc vx vy vz cv elvv anbi1i 3bitr4i
      abbii wph vx vy vz df-opab wph vy vz cv c2nd cfv wsbc vx vz cv c1st cfv
      wsbc vz cvv cvv cxp df-rab 3eqtr4i $.
  $}

  ${
    $d w ph $.  $d x y z w $.
    $( A way to define an operation class abstraction without using existential
       quantifiers.  (Contributed by NM, 18-Aug-2006.)  (Revised by Mario
       Carneiro, 31-Aug-2015.) $)
    dfoprab3s $p |- { <. <. x , y >. , z >. | ph } = { <. w , z >. |
       ( w e. ( _V X. _V )
           /\ [. ( 1st ` w ) / x ]. [. ( 2nd ` w ) / y ]. ph ) } $=
      wph vx vy vz coprab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw vz
      copab vw cv cvv cvv cxp wcel wph vy vw cv c2nd cfv wsbc vx vw cv c1st cfv
      wsbc wa vw vz copab wph vx vy vz vw dfoprab2 vw cv vx cv vy cv cop wceq
      wph wa vy wex vx wex vw cv cvv cvv cxp wcel wph vy vw cv c2nd cfv wsbc vx
      vw cv c1st cfv wsbc wa vw vz vw cv vx cv vy cv cop wceq vy wex wph vy vw
      cv c2nd cfv wsbc vx vw cv c1st cfv wsbc wa vx wex vw cv vx cv vy cv cop
      wceq vy wex vx wex wph vy vw cv c2nd cfv wsbc vx vw cv c1st cfv wsbc wa
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cv cvv cvv cxp wcel
      wph vy vw cv c2nd cfv wsbc vx vw cv c1st cfv wsbc wa vw cv vx cv vy cv
      cop wceq vy wex wph vy vw cv c2nd cfv wsbc vx vw cv c1st cfv wsbc vx wph
      vy vw cv c2nd cfv wsbc vx vw cv c1st cfv nfsbc1v 19.41 vw cv vx cv vy cv
      cop wceq wph wa vy wex vw cv vx cv vy cv cop wceq vy wex wph vy vw cv
      c2nd cfv wsbc vx vw cv c1st cfv wsbc wa vx vw cv vx cv vy cv cop wceq wph
      wa vy wex vw cv vx cv vy cv cop wceq wph vy vw cv c2nd cfv wsbc vx vw cv
      c1st cfv wsbc wa vy wex vw cv vx cv vy cv cop wceq vy wex wph vy vw cv
      c2nd cfv wsbc vx vw cv c1st cfv wsbc wa vw cv vx cv vy cv cop wceq wph vy
      vw cv c2nd cfv wsbc vx vw cv c1st cfv wsbc wa vw cv vx cv vy cv cop wceq
      wph wa vy vw cv vx cv vy cv cop wceq wph vy vw cv c2nd cfv wsbc vx vw cv
      c1st cfv wsbc wph wph vx vy vw cv sbcopeq1a pm5.32i exbii vw cv vx cv vy
      cv cop wceq wph vy vw cv c2nd cfv wsbc vx vw cv c1st cfv wsbc vy wph vy
      vw cv c2nd cfv wsbc vy vx vw cv c1st cfv vy vw cv c1st cfv nfcv wph vy vw
      cv c2nd cfv nfsbc1v nfsbc 19.41 bitr3i exbii vw cv cvv cvv cxp wcel vw cv
      vx cv vy cv cop wceq vy wex vx wex wph vy vw cv c2nd cfv wsbc vx vw cv
      c1st cfv wsbc vx vy vw cv elvv anbi1i 3bitr4i opabbii eqtri $.
  $}

  ${
    $d x y ph $.  $d w ps $.  $d x y z w $.
    dfoprab3.1 $e |- ( w = <. x , y >. -> ( ph <-> ps ) ) $.
    $( Operation class abstraction expressed without existential quantifiers.
       (Contributed by NM, 16-Dec-2008.) $)
    dfoprab3 $p |- { <. w , z >. | ( w e. ( _V X. _V ) /\ ph ) } =
       { <. <. x , y >. , z >. | ps } $=
      wps vx vy vz coprab vw cv cvv cvv cxp wcel wps vy vw cv c2nd cfv wsbc vx
      vw cv c1st cfv wsbc wa vw vz copab vw cv cvv cvv cxp wcel wph wa vw vz
      copab wps vx vy vz vw dfoprab3s vw cv cvv cvv cxp wcel wps vy vw cv c2nd
      cfv wsbc vx vw cv c1st cfv wsbc wa vw cv cvv cvv cxp wcel wph wa vw vz vw
      cv cvv cvv cxp wcel wps vy vw cv c2nd cfv wsbc vx vw cv c1st cfv wsbc wph
      vw cv cvv cvv cxp wcel wps wph vx vy vw cv c1st cfv vw cv c2nd cfv vw cv
      c1st fvex vw cv c2nd fvex vw cv cvv cvv cxp wcel vx cv vw cv c1st cfv
      wceq vy cv vw cv c2nd cfv wceq wa wps wph wb vw cv cvv cvv cxp wcel vx cv
      vw cv c1st cfv wceq vy cv vw cv c2nd cfv wceq wa wa wph wps vw cv cvv cvv
      cxp wcel vx cv vw cv c1st cfv wceq vy cv vw cv c2nd cfv wceq wa wa vw cv
      vx cv vy cv cop wceq wph wps wb vx cv vw cv c1st cfv wceq vy cv vw cv
      c2nd cfv wceq wa vw cv cvv cvv cxp wcel vw cv c1st cfv vx cv wceq vw cv
      c2nd cfv vy cv wceq wa vw cv vx cv vy cv cop wceq vx cv vw cv c1st cfv
      wceq vw cv c1st cfv vx cv wceq vy cv vw cv c2nd cfv wceq vw cv c2nd cfv
      vy cv wceq vx cv vw cv c1st cfv eqcom vy cv vw cv c2nd cfv eqcom anbi12i
      vw cv vx cv vy cv cvv cvv eqopi sylan2b dfoprab3.1 syl bicomd ex sbc2iedv
      pm5.32i opabbii eqtr2i $.
  $}

  ${
    $d w x y A $.  $d w x y B $.  $d x y ph $.  $d w ps $.  $d w x y z $.
    dfoprab4.1 $e |- ( w = <. x , y >. -> ( ph <-> ps ) ) $.
    $( Operation class abstraction expressed without existential quantifiers.
       (Contributed by NM, 3-Sep-2007.)  (Revised by Mario Carneiro,
       31-Aug-2015.) $)
    dfoprab4 $p |- { <. w , z >. | ( w e. ( A X. B ) /\ ph ) } =
      { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } $=
      vw cv cA cB cxp wcel wph wa vw vz copab vw cv cvv cvv cxp wcel vw cv cA
      cB cxp wcel wph wa wa vw vz copab vx cv cA wcel vy cv cB wcel wa wps wa
      vx vy vz coprab vw cv cA cB cxp wcel wph wa vw cv cvv cvv cxp wcel vw cv
      cA cB cxp wcel wph wa wa vw vz vw cv cA cB cxp wcel wph wa vw cv cvv cvv
      cxp wcel vw cv cA cB cxp wcel vw cv cvv cvv cxp wcel wph cA cB cxp cvv
      cvv cxp vw cv cA cB xpss sseli adantr pm4.71ri opabbii vw cv cA cB cxp
      wcel wph wa vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz vw vw cv vx cv
      vy cv cop wceq vw cv cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa wph
      wps vw cv vx cv vy cv cop wceq vw cv cA cB cxp wcel vx cv vy cv cop cA cB
      cxp wcel vx cv cA wcel vy cv cB wcel wa vw cv vx cv vy cv cop cA cB cxp
      eleq1 vx cv vy cv cA cB opelxp syl6bb dfoprab4.1 anbi12d dfoprab3 eqtri
      $.
  $}

  ${
    $d t u w x y z $.  $d t u w x y A $.  $d t u w x y B $.  $d t u w ps $.
    $d t u ph $.
    dfoprab4f.x $e |- F/ x ph $.
    dfoprab4f.y $e |- F/ y ph $.
    dfoprab4f.1 $e |- ( w = <. x , y >. -> ( ph <-> ps ) ) $.
    $( Operation class abstraction expressed without existential quantifiers.
       (Unnecessary distinct variable restrictions were removed by David
       Abernethy, 19-Jun-2012.)  (Contributed by NM, 20-Dec-2008.)  (Revised by
       Mario Carneiro, 31-Aug-2015.) $)
    dfoprab4f $p |- { <. w , z >. | ( w e. ( A X. B ) /\ ph ) } =
      { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ps ) } $=
      vw cv cA cB cxp wcel wph wa vw vz copab vt cv cA wcel vu cv cB wcel wa
      wps vy vu wsb vx vt wsb wa vt vu vz coprab vx cv cA wcel vy cv cB wcel wa
      wps wa vx vy vz coprab wph wps vy vu wsb vx vt wsb vt vu vz vw cA cB vw
      cv vx cv vu cv cop wceq wph wps vy vu wsb wb wi vw cv vt cv vu cv cop
      wceq wph wps vy vu wsb vx vt wsb wb wi vx vt vw cv vt cv vu cv cop wceq
      wph wps vy vu wsb vx vt wsb wb vx vw cv vt cv vu cv cop wceq vx nfv wph
      wps vy vu wsb vx vt wsb vx dfoprab4f.x wps vy vu wsb vx vt nfs1v nfbi
      nfim vx cv vt cv wceq vw cv vx cv vu cv cop wceq vw cv vt cv vu cv cop
      wceq wph wps vy vu wsb wb wph wps vy vu wsb vx vt wsb wb vx cv vt cv wceq
      vx cv vu cv cop vt cv vu cv cop vw cv vx cv vt cv vu cv opeq1 eqeq2d vx
      cv vt cv wceq wps vy vu wsb wps vy vu wsb vx vt wsb wph wps vy vu wsb vx
      vt sbequ12 bibi2d imbi12d vw cv vx cv vy cv cop wceq wph wps wb wi vw cv
      vx cv vu cv cop wceq wph wps vy vu wsb wb wi vy vu vw cv vx cv vu cv cop
      wceq wph wps vy vu wsb wb vy vw cv vx cv vu cv cop wceq vy nfv wph wps vy
      vu wsb vy dfoprab4f.y wps vy vu nfs1v nfbi nfim vy cv vu cv wceq vw cv vx
      cv vy cv cop wceq vw cv vx cv vu cv cop wceq wph wps wb wph wps vy vu wsb
      wb vy cv vu cv wceq vx cv vy cv cop vx cv vu cv cop vw cv vy cv vu cv vx
      cv opeq2 eqeq2d vy cv vu cv wceq wps wps vy vu wsb wph wps vy vu sbequ12
      bibi2d imbi12d dfoprab4f.1 chvar chvar dfoprab4 vx cv cA wcel vy cv cB
      wcel wa wps wa vt cv cA wcel vu cv cB wcel wa wps vy vu wsb vx vt wsb wa
      vx vy vz vt vu vx cv cA wcel vy cv cB wcel wa wps wa vt nfv vx cv cA wcel
      vy cv cB wcel wa wps wa vu nfv vt cv cA wcel vu cv cB wcel wa wps vy vu
      wsb vx vt wsb vx vt cv cA wcel vu cv cB wcel wa vx nfv wps vy vu wsb vx
      vt nfs1v nfan vt cv cA wcel vu cv cB wcel wa wps vy vu wsb vx vt wsb vy
      vt cv cA wcel vu cv cB wcel wa vy nfv wps vy vu wsb vx vt vy wps vy vu
      nfs1v nfsb nfan vx cv vt cv wceq vy cv vu cv wceq wa vx cv cA wcel vy cv
      cB wcel wa vt cv cA wcel vu cv cB wcel wa wps wps vy vu wsb vx vt wsb vx
      cv vt cv wceq vx cv cA wcel vt cv cA wcel vy cv vu cv wceq vy cv cB wcel
      vu cv cB wcel vx cv vt cv cA eleq1 vy cv vu cv cB eleq1 bi2anan9 vy cv vu
      cv wceq wps wps vy vu wsb vx cv vt cv wceq wps vy vu wsb vx vt wsb wps vy
      vu sbequ12 wps vy vu wsb vx vt sbequ12 sylan9bbr anbi12d cbvoprab12
      eqtr4i $.
  $}

  ${
    $d x y z u A $.  $d x y z u B $.  $d x y z u C $.
    $( Define the cross product of three classes.  Compare ~ df-xp .
       (Contributed by FL, 6-Nov-2013.)  (Proof shortened by Mario Carneiro,
       3-Nov-2015.) $)
    dfxp3 $p |- ( ( A X. B ) X. C ) =
      { <. <. x , y >. , z >. | ( x e. A /\ y e. B /\ z e. C ) } $=
      vu cv cA cB cxp wcel vz cv cC wcel wa vu vz copab vx cv cA wcel vy cv cB
      wcel wa vz cv cC wcel wa vx vy vz coprab cA cB cxp cC cxp vx cv cA wcel
      vy cv cB wcel vz cv cC wcel w3a vx vy vz coprab vz cv cC wcel vz cv cC
      wcel vx vy vz vu cA cB vu cv vx cv vy cv cop wceq vz cv cC wcel biidd
      dfoprab4 vu vz cA cB cxp cC df-xp vx cv cA wcel vy cv cB wcel vz cv cC
      wcel w3a vx cv cA wcel vy cv cB wcel wa vz cv cC wcel wa vx vy vz vx cv
      cA wcel vy cv cB wcel vz cv cC wcel df-3an oprabbii 3eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y ph $.
    copsex2ga.1 $e |- ( A = <. x , y >. -> ( ph <-> ps ) ) $.
    $( Implicit substitution inference for ordered pairs.  Compare
       ~ copsex2ga .  (Contributed by NM, 12-Mar-2014.) $)
    copsex2gb $p |- ( E. x E. y ( A = <. x , y >. /\ ps )
         <-> ( A e. ( _V X. _V ) /\ ph ) ) $=
      cA cvv cvv cxp wcel wph wa cA vx cv vy cv cop wceq vy wex vx wex wph wa
      cA vx cv vy cv cop wceq wph wa vy wex vx wex cA vx cv vy cv cop wceq wps
      wa vy wex vx wex cA cvv cvv cxp wcel cA vx cv vy cv cop wceq vy wex vx
      wex wph vx vy cA elvv anbi1i cA vx cv vy cv cop wceq wph vx vy 19.41vv cA
      vx cv vy cv cop wceq wph wa cA vx cv vy cv cop wceq wps wa vx vy cA vx cv
      vy cv cop wceq wph wps copsex2ga.1 pm5.32i 2exbii 3bitr2ri $.

    $( Implicit substitution inference for ordered pairs.  Compare
       ~ copsex2g .  (Contributed by NM, 26-Feb-2014.)  (Proof shortened by
       Mario Carneiro, 31-Aug-2015.) $)
    copsex2ga $p |- ( A e. ( V X. W )
        -> ( ph <-> E. x E. y ( A = <. x , y >. /\ ps ) ) ) $=
      cA cV cW cxp wcel cA cvv cvv cxp wcel wph cA vx cv vy cv cop wceq wps wa
      vy wex vx wex wb cV cW cxp cvv cvv cxp cA cV cW xpss sseli cA vx cv vy cv
      cop wceq wps wa vy wex vx wex cA cvv cvv cxp wcel wph wph wps vx vy cA
      copsex2ga.1 copsex2gb baibr syl $.

    $( Membership in an ordered pair class builder.  (Contributed by NM,
       25-Feb-2014.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    elopaba $p |- ( A e. { <. x , y >. | ps } <->
            ( A e. ( _V X. _V ) /\ ph ) ) $=
      cA wps vx vy copab wcel cA vx cv vy cv cop wceq wps wa vy wex vx wex cA
      cvv cvv cxp wcel wph wa wps vx vy cA elopab wph wps vx vy cA copsex2ga.1
      copsex2gb bitri $.
  $}

  ${
    $d y z ph $.  $d x ps $.  $d x y z $.
    exopxfr.1 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
    $( Transfer ordered-pair existence from/to single variable existence.
       (Contributed by NM, 26-Feb-2014.)  (Proof shortened by Mario Carneiro,
       31-Aug-2015.) $)
    exopxfr $p |- ( E. x e. ( _V X. _V ) ph <-> E. y E. z ps ) $=
      wph vx cvv cvv cxp wrex wps vz cvv wrex vy cvv wrex wps vz cvv wrex vy
      wex wps vz wex vy wex wph wps vx vy vz cvv cvv exopxfr.1 rexxp wps vz cvv
      wrex vy rexv wps vz cvv wrex wps vz wex vy wps vz rexv exbii 3bitri $.
  $}

  ${
    $d x y z A $.  $d y z ph $.  $d x ps $.
    exopxfr2.1 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
    $( Transfer ordered-pair existence from/to single variable existence.
       (Contributed by NM, 26-Feb-2014.) $)
    exopxfr2 $p |- ( Rel A -> ( E. x e. A ph
              <-> E. y E. z ( <. y , z >. e. A /\ ps ) ) ) $=
      cA wrel wph vx cA wrex vx cv cA wcel wph wa vx cvv cvv cxp wrex vy cv vz
      cv cop cA wcel wps wa vz wex vy wex cA wrel wph vx cv cA wcel wph wa vx
      cA cvv cvv cxp cA wrel vx cv cA wcel wph wa vx cv cvv cvv cxp wcel cA
      wrel vx cv cA wcel vx cv cvv cvv cxp wcel wph cA wrel cA cvv cvv cxp vx
      cv cA wrel cA cvv cvv cxp wss cA df-rel biimpi sseld adantrd pm4.71rd
      rexbidv2 vx cv cA wcel wph wa vy cv vz cv cop cA wcel wps wa vx vy vz vx
      cv vy cv vz cv cop wceq vx cv cA wcel vy cv vz cv cop cA wcel wph wps vx
      cv vy cv vz cv cop cA eleq1 exopxfr2.1 anbi12d exopxfr syl6bb $.
  $}

  ${
    $d x y A $.  $d x y ch $.
    elopabi.1 $e |- ( x = ( 1st ` A ) -> ( ph <-> ps ) ) $.
    elopabi.2 $e |- ( y = ( 2nd ` A ) -> ( ps <-> ch ) ) $.
    $( A consequence of membership in an ordered-pair class abstraction, using
       ordered pair extractors.  (Contributed by NM, 29-Aug-2006.) $)
    elopabi $p |- ( A e. { <. x , y >. | ph } -> ch ) $=
      cA wph vx vy copab wcel cA c1st cfv cA c2nd cfv cop wph vx vy copab wcel
      wch cA wph vx vy copab wcel cA cA c1st cfv cA c2nd cfv cop wph vx vy
      copab wph vx vy copab wrel cA wph vx vy copab wcel cA cA c1st cfv cA c2nd
      cfv cop wceq wph vx vy relopab cA wph vx vy copab 1st2nd mpan cA wph vx
      vy copab wcel id eqeltrrd wph wps wch vx vy cA c1st cfv cA c2nd cfv cA
      c1st fvex cA c2nd fvex elopabi.1 elopabi.2 opelopab sylib $.
  $}

  ${
    $d w x y z A $.  $d w ph $.  $d x y z th $.
    eloprabi.1 $e |- ( x = ( 1st ` ( 1st ` A ) ) -> ( ph <-> ps ) ) $.
    eloprabi.2 $e |- ( y = ( 2nd ` ( 1st ` A ) ) -> ( ps <-> ch ) ) $.
    eloprabi.3 $e |- ( z = ( 2nd ` A ) -> ( ch <-> th ) ) $.
    $( A consequence of membership in an operation class abstraction, using
       ordered pair extractors.  (Contributed by NM, 6-Nov-2006.)  (Revised by
       David Abernethy, 19-Jun-2012.) $)
    eloprabi $p |- ( A e. { <. <. x , y >. , z >. | ph } -> th ) $=
      cA wph vx vy vz coprab wcel cA vx cv vy cv cop vz cv cop wceq wph wa vz
      wex vy wex vx wex wth cA wph vx vy vz coprab wcel cA vx cv vy cv cop vz
      cv cop wceq wph wa vz wex vy wex vx wex vw cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vx wex cA vx cv vy cv cop vz cv cop wceq wph wa
      vz wex vy wex vx wex vw cA wph vx vy vz coprab wph vx vy vz coprab vw cv
      cA wceq vw cv vx cv vy cv cop vz cv cop wceq wph wa cA vx cv vy cv cop vz
      cv cop wceq wph wa vx vy vz vw cv cA wceq vw cv vx cv vy cv cop vz cv cop
      wceq cA vx cv vy cv cop vz cv cop wceq wph vw cv cA vx cv vy cv cop vz cv
      cop eqeq1 anbi1d 3exbidv wph vx vy vz vw df-oprab elab2g ibi cA vx cv vy
      cv cop vz cv cop wceq wph wa vz wex vy wex wth vx cA vx cv vy cv cop vz
      cv cop wceq wph wa vz wex wth vy cA vx cv vy cv cop vz cv cop wceq wph wa
      wth vz cA vx cv vy cv cop vz cv cop wceq wph wth cA vx cv vy cv cop vz cv
      cop wceq wph wps wch wth cA vx cv vy cv cop vz cv cop wceq vx cv cA c1st
      cfv c1st cfv wceq wph wps wb cA vx cv vy cv cop vz cv cop wceq cA c1st
      cfv c1st cfv vx cv vy cv cop c1st cfv vx cv cA vx cv vy cv cop vz cv cop
      wceq cA c1st cfv vx cv vy cv cop c1st vx cv vy cv cop vz cv cA vx cv vy
      cv opex vz vex op1std fveq2d vx cv vy cv vx vex vy vex op1st syl6req
      eloprabi.1 syl cA vx cv vy cv cop vz cv cop wceq vy cv cA c1st cfv c2nd
      cfv wceq wps wch wb cA vx cv vy cv cop vz cv cop wceq cA c1st cfv c2nd
      cfv vx cv vy cv cop c2nd cfv vy cv cA vx cv vy cv cop vz cv cop wceq cA
      c1st cfv vx cv vy cv cop c2nd vx cv vy cv cop vz cv cA vx cv vy cv opex
      vz vex op1std fveq2d vx cv vy cv vx vex vy vex op2nd syl6req eloprabi.2
      syl cA vx cv vy cv cop vz cv cop wceq vz cv cA c2nd cfv wceq wch wth wb
      cA vx cv vy cv cop vz cv cop wceq cA c2nd cfv vz cv vx cv vy cv cop vz cv
      cA vx cv vy cv opex vz vex op2ndd eqcomd eloprabi.3 syl 3bitrd biimpa
      exlimiv exlimiv exlimiv syl $.
  $}

  ${
    $d u v x y z A $.  $d t u v y z B $.  $d t u v z C $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 24-Dec-2016.) $)
    mpt2mptsx $p |- ( x e. A , y e. B |-> C ) = ( z e. U_ x e. A ( { x } X. B )
        |-> [_ ( 1st ` z ) / x ]_ [_ ( 2nd ` z ) / y ]_ C ) $=
      vz vu cA vu cv csn vx vu cv cB csb cxp ciun vx vz cv c1st cfv vy vz cv
      c2nd cfv cC csb csb cmpt vu vv cA vx vu cv cB csb vx vu cv vy vv cv cC
      csb csb cmpt2 vz vx cA vx cv csn cB cxp ciun vx vz cv c1st cfv vy vz cv
      c2nd cfv cC csb csb cmpt vx vy cA cB cC cmpt2 vu vv vz cA vx vu cv cB csb
      vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb vx vu cv vy vv cv cC csb
      csb vz cv vu cv vv cv cop wceq vx vz cv c1st cfv vy vz cv c2nd cfv cC csb
      csb vx vu cv vy vz cv c2nd cfv cC csb csb vx vu cv vy vv cv cC csb csb vz
      cv vu cv vv cv cop wceq vx vz cv c1st cfv vu cv vy vz cv c2nd cfv cC csb
      vu cv vv cv vz cv vu vex vv vex op1std csbeq1d vz cv vu cv vv cv cop wceq
      vx vu cv vy vz cv c2nd cfv cC csb vy vv cv cC csb vz cv vu cv vv cv cop
      wceq vy vz cv c2nd cfv vv cv cC vu cv vv cv vz cv vu vex vv vex op2ndd
      csbeq1d csbeq2dv eqtrd mpt2mptx vx cA vx cv csn cB cxp ciun vu cA vu cv
      csn vx vu cv cB csb cxp ciun wceq vz vx cA vx cv csn cB cxp ciun vx vz cv
      c1st cfv vy vz cv c2nd cfv cC csb csb cmpt vz vu cA vu cv csn vx vu cv cB
      csb cxp ciun vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb cmpt wceq vx
      vu cA vx cv csn cB cxp vu cv csn vx vu cv cB csb cxp vu vx cv csn cB cxp
      nfcv vx vu cv csn vx vu cv cB csb vx vu cv csn nfcv vx vu cv cB nfcsb1v
      nfxp vx cv vu cv wceq vx cv csn vu cv csn cB vx vu cv cB csb vx cv vu cv
      sneq vx vu cv cB csbeq1a xpeq12d cbviun vz vx cA vx cv csn cB cxp ciun vu
      cA vu cv csn vx vu cv cB csb cxp ciun vx vz cv c1st cfv vy vz cv c2nd cfv
      cC csb csb mpteq1 ax-mp vx vy vu vv cA cB cC vx vu cv cB csb vx vu cv vy
      vv cv cC csb csb vu cB nfcv vx vu cv cB nfcsb1v vu cC nfcv vv cC nfcv vx
      vu cv vy vv cv cC csb nfcsb1v vy vx vu cv vy vv cv cC csb vy vu cv nfcv
      vy vv cv cC nfcsb1v nfcsb vx vu cv cB csbeq1a vy cv vv cv wceq vx cv vu
      cv wceq cC vy vv cv cC csb vx vu cv vy vv cv cC csb csb vy vv cv cC
      csbeq1a vx vu cv vy vv cv cC csb csbeq1a sylan9eqr cbvmpt2x 3eqtr4ri $.

    $d x B $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 24-Sep-2015.) $)
    mpt2mpts $p |- ( x e. A , y e. B |-> C ) =
      ( z e. ( A X. B ) |-> [_ ( 1st ` z ) / x ]_ [_ ( 2nd ` z ) / y ]_ C ) $=
      vx vy cA cB cC cmpt2 vz vx cA vx cv csn cB cxp ciun vx vz cv c1st cfv vy
      vz cv c2nd cfv cC csb csb cmpt vz cA cB cxp vx vz cv c1st cfv vy vz cv
      c2nd cfv cC csb csb cmpt vx vy vz cA cB cC mpt2mptsx vx cA vx cv csn cB
      cxp ciun cA cB cxp wceq vz vx cA vx cv csn cB cxp ciun vx vz cv c1st cfv
      vy vz cv c2nd cfv cC csb csb cmpt vz cA cB cxp vx vz cv c1st cfv vy vz cv
      c2nd cfv cC csb csb cmpt wceq vx cA cB iunxpconst vz vx cA vx cv csn cB
      cxp ciun cA cB cxp vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb mpteq1
      ax-mp eqtri $.
  $}

  ${
    $d t u v w x y z A $.  $d t u v w y z B $.  $d t u v w z C $.
    $d v w x y z D $.
    fmpt2x.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( The domain of a mapping is a subset of its base class.  (Contributed by
       Mario Carneiro, 9-Feb-2015.) $)
    dmmpt2ssx $p |- dom F C_ U_ x e. A ( { x } X. B ) $=
      cF cdm vu cA vu cv csn vx vu cv cB csb cxp ciun vx cA vx cv csn cB cxp
      ciun vt vu cA vu cv csn vx vu cv cB csb cxp ciun vx vt cv c1st cfv vy vt
      cv c2nd cfv cC csb csb cF vx vy cA cB cC cmpt2 vu vv cA vx vu cv cB csb
      vx vu cv vy vv cv cC csb csb cmpt2 cF vt vu cA vu cv csn vx vu cv cB csb
      cxp ciun vx vt cv c1st cfv vy vt cv c2nd cfv cC csb csb cmpt vx vy vu vv
      cA cB cC vx vu cv cB csb vx vu cv vy vv cv cC csb csb vu cB nfcv vx vu cv
      cB nfcsb1v vu cC nfcv vv cC nfcv vx vu cv vy vv cv cC csb nfcsb1v vy vx
      vu cv vy vv cv cC csb vy vu cv nfcv vy vv cv cC nfcsb1v nfcsb vx vu cv cB
      csbeq1a vy cv vv cv wceq vx cv vu cv wceq cC vy vv cv cC csb vx vu cv vy
      vv cv cC csb csb vy vv cv cC csbeq1a vx vu cv vy vv cv cC csb csbeq1a
      sylan9eqr cbvmpt2x fmpt2x.1 vu vv vt cA vx vu cv cB csb vx vt cv c1st cfv
      vy vt cv c2nd cfv cC csb csb vx vu cv vy vv cv cC csb csb vt cv vu cv vv
      cv cop wceq vx vt cv c1st cfv vy vt cv c2nd cfv cC csb csb vx vu cv vy vt
      cv c2nd cfv cC csb csb vx vu cv vy vv cv cC csb csb vt cv vu cv vv cv cop
      wceq vx vt cv c1st cfv vu cv vy vt cv c2nd cfv cC csb vu cv vv cv vt cv
      vu vex vv vex op1std csbeq1d vt cv vu cv vv cv cop wceq vx vu cv vy vt cv
      c2nd cfv cC csb vy vv cv cC csb vt cv vu cv vv cv cop wceq vy vt cv c2nd
      cfv vv cv cC vu cv vv cv vt cv vu vex vv vex op2ndd csbeq1d csbeq2dv
      eqtrd mpt2mptx 3eqtr4i dmmptss vx vu cA vx cv csn cB cxp vu cv csn vx vu
      cv cB csb cxp vu vx cv csn cB cxp nfcv vx vu cv csn vx vu cv cB csb vx vu
      cv csn nfcv vx vu cv cB nfcsb1v nfxp vx cv vu cv wceq vx cv csn vu cv csn
      cB vx vu cv cB csb vx cv vu cv sneq vx vu cv cB csbeq1a xpeq12d cbviun
      sseqtr4i $.

    $( Functionality, domain and codomain of a class given by the "maps to"
       notation, where ` B ( x ) ` is not constant but depends on ` x ` .
       (Contributed by NM, 29-Dec-2014.) $)
    fmpt2x $p |- ( A. x e. A A. y e. B C e. D <->
      F : U_ x e. A ( { x } X. B ) --> D ) $=
      vx vz cv vy vw cv cC csb csb cD wcel vw vx vz cv cB csb wral vz cA wral
      vz cA vz cv csn vx vz cv cB csb cxp ciun cD cF wf cC cD wcel vy cB wral
      vx cA wral vx cA vx cv csn cB cxp ciun cD cF wf vx vz cv vy vw cv cC csb
      csb cD wcel vw vx vz cv cB csb wral vz cA wral vx vv cv c1st cfv vy vv cv
      c2nd cfv cC csb csb cD wcel vv vz cA vz cv csn vx vz cv cB csb cxp ciun
      wral vz cA vz cv csn vx vz cv cB csb cxp ciun cD cF wf vx vv cv c1st cfv
      vy vv cv c2nd cfv cC csb csb cD wcel vx vz cv vy vw cv cC csb csb cD wcel
      vv vz vw cA vx vz cv cB csb vv cv vz cv vw cv cop wceq vx vv cv c1st cfv
      vy vv cv c2nd cfv cC csb csb vx vz cv vy vw cv cC csb csb cD vv cv vz cv
      vw cv cop wceq vx vv cv c1st cfv vy vv cv c2nd cfv cC csb csb vx vz cv vy
      vv cv c2nd cfv cC csb csb vx vz cv vy vw cv cC csb csb vv cv vz cv vw cv
      cop wceq vx vv cv c1st cfv vz cv vy vv cv c2nd cfv cC csb vz cv vw cv vv
      cv vz vex vw vex op1std csbeq1d vv cv vz cv vw cv cop wceq vx vz cv vy vv
      cv c2nd cfv cC csb vy vw cv cC csb vv cv vz cv vw cv cop wceq vy vv cv
      c2nd cfv vw cv cC vz cv vw cv vv cv vz vex vw vex op2ndd csbeq1d csbeq2dv
      eqtrd eleq1d raliunxp vv vz cA vz cv csn vx vz cv cB csb cxp ciun cD vx
      vv cv c1st cfv vy vv cv c2nd cfv cC csb csb cF vx vy cA cB cC cmpt2 vz vw
      cA vx vz cv cB csb vx vz cv vy vw cv cC csb csb cmpt2 cF vv vz cA vz cv
      csn vx vz cv cB csb cxp ciun vx vv cv c1st cfv vy vv cv c2nd cfv cC csb
      csb cmpt vx cv cA wcel vy cv cB wcel wa vv cv cC wceq wa vx vy vv coprab
      vz cv cA wcel vw cv vx vz cv cB csb wcel wa vv cv vx vz cv vy vw cv cC
      csb csb wceq wa vz vw vv coprab vx vy cA cB cC cmpt2 vz vw cA vx vz cv cB
      csb vx vz cv vy vw cv cC csb csb cmpt2 vx cv cA wcel vy cv cB wcel wa vv
      cv cC wceq wa vz cv cA wcel vw cv vx vz cv cB csb wcel wa vv cv vx vz cv
      vy vw cv cC csb csb wceq wa vx vy vv vz vw vx cv cA wcel vy cv cB wcel wa
      vv cv cC wceq wa vz nfv vx cv cA wcel vy cv cB wcel wa vv cv cC wceq wa
      vw nfv vz cv cA wcel vw cv vx vz cv cB csb wcel wa vv cv vx vz cv vy vw
      cv cC csb csb wceq vx vz cv cA wcel vw cv vx vz cv cB csb wcel vx vz cv
      cA wcel vx nfv vx vw cv vx vz cv cB csb vx vz cv cB nfcsb1v nfel2 nfan vx
      vv cv vx vz cv vy vw cv cC csb csb vx vz cv vy vw cv cC csb nfcsb1v nfeq2
      nfan vz cv cA wcel vw cv vx vz cv cB csb wcel wa vv cv vx vz cv vy vw cv
      cC csb csb wceq vy vz cv cA wcel vw cv vx vz cv cB csb wcel wa vy nfv vy
      vv cv vx vz cv vy vw cv cC csb csb vy vx vz cv vy vw cv cC csb vy vz cv
      nfcv vy vw cv cC nfcsb1v nfcsb nfeq2 nfan vx cv vz cv wceq vy cv vw cv
      wceq wa vx cv cA wcel vy cv cB wcel wa vz cv cA wcel vw cv vx vz cv cB
      csb wcel wa vv cv cC wceq vv cv vx vz cv vy vw cv cC csb csb wceq vx cv
      vz cv wceq vy cv vw cv wceq wa vx cv cA wcel vz cv cA wcel vy cv cB wcel
      vw cv vx vz cv cB csb wcel vx cv vz cv wceq vx cv cA wcel vz cv cA wcel
      wb vy cv vw cv wceq vx cv vz cv cA eleq1 adantr vy cv vw cv wceq vy cv cB
      wcel vw cv cB wcel vx cv vz cv wceq vw cv vx vz cv cB csb wcel vy cv vw
      cv cB eleq1 vx cv vz cv wceq cB vx vz cv cB csb vw cv vx vz cv cB csbeq1a
      eleq2d sylan9bbr anbi12d vx cv vz cv wceq vy cv vw cv wceq wa cC vx vz cv
      vy vw cv cC csb csb vv cv vy cv vw cv wceq vx cv vz cv wceq cC vy vw cv
      cC csb vx vz cv vy vw cv cC csb csb vy vw cv cC csbeq1a vx vz cv vy vw cv
      cC csb csbeq1a sylan9eqr eqeq2d anbi12d cbvoprab12 vx vy vv cA cB cC
      df-mpt2 vz vw vv cA vx vz cv cB csb vx vz cv vy vw cv cC csb csb df-mpt2
      3eqtr4i fmpt2x.1 vz vw vv cA vx vz cv cB csb vx vv cv c1st cfv vy vv cv
      c2nd cfv cC csb csb vx vz cv vy vw cv cC csb csb vv cv vz cv vw cv cop
      wceq vx vv cv c1st cfv vy vv cv c2nd cfv cC csb csb vx vz cv vy vv cv
      c2nd cfv cC csb csb vx vz cv vy vw cv cC csb csb vv cv vz cv vw cv cop
      wceq vx vv cv c1st cfv vz cv vy vv cv c2nd cfv cC csb vz cv vw cv vv cv
      vz vex vw vex op1std csbeq1d vv cv vz cv vw cv cop wceq vx vz cv vy vv cv
      c2nd cfv cC csb vy vw cv cC csb vv cv vz cv vw cv cop wceq vy vv cv c2nd
      cfv vw cv cC vz cv vw cv vv cv vz vex vw vex op2ndd csbeq1d csbeq2dv
      eqtrd mpt2mptx 3eqtr4i fmpt bitr3i cC cD wcel vy cB wral vx vz cv vy vw
      cv cC csb csb cD wcel vw vx vz cv cB csb wral vx vz cA cC cD wcel vy cB
      wral vz nfv vx vz cv vy vw cv cC csb csb cD wcel vx vw vx vz cv cB csb vx
      vz cv cB nfcsb1v vx vx vz cv vy vw cv cC csb csb cD vx vz cv vy vw cv cC
      csb nfcsb1v nfel1 nfral cC cD wcel vy cB wral vy vw cv cC csb cD wcel vw
      cB wral vx cv vz cv wceq vx vz cv vy vw cv cC csb csb cD wcel vw vx vz cv
      cB csb wral cC cD wcel vy vw cv cC csb cD wcel vy vw cB cC cD wcel vw nfv
      vy vy vw cv cC csb cD vy vw cv cC nfcsb1v nfel1 vy cv vw cv wceq cC vy vw
      cv cC csb cD vy vw cv cC csbeq1a eleq1d cbvral vx cv vz cv wceq vy vw cv
      cC csb cD wcel vx vz cv vy vw cv cC csb csb cD wcel vw cB vx vz cv cB csb
      vx vz cv cB csbeq1a vx cv vz cv wceq vy vw cv cC csb vx vz cv vy vw cv cC
      csb csb cD vx vz cv vy vw cv cC csb csbeq1a eleq1d raleqbidv syl5bb
      cbvral vx cA vx cv csn cB cxp ciun vz cA vz cv csn vx vz cv cB csb cxp
      ciun cD cF vx vz cA vx cv csn cB cxp vz cv csn vx vz cv cB csb cxp vz vx
      cv csn cB cxp nfcv vx vz cv csn vx vz cv cB csb vx vz cv csn nfcv vx vz
      cv cB nfcsb1v nfxp vx cv vz cv wceq vx cv csn vz cv csn cB vx vz cv cB
      csb vx cv vz cv sneq vx vz cv cB csbeq1a xpeq12d cbviun feq2i 3bitr4i $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C z $.  $d D x y z $.
    fmpt2.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( Functionality, domain and range of a class given by the "maps to"
       notation.  (Contributed by FL, 17-May-2010.) $)
    fmpt2 $p |- ( A. x e. A A. y e. B C e. D <-> F : ( A X. B ) --> D ) $=
      cC cD wcel vy cB wral vx cA wral vx cA vx cv csn cB cxp ciun cD cF wf cA
      cB cxp cD cF wf vx vy cA cB cC cD cF fmpt2.1 fmpt2x vx cA vx cv csn cB
      cxp ciun cA cB cxp cD cF vx cA cB iunxpconst feq2i bitri $.

    $( Functionality and domain of a class given by the "maps to" notation.
       (Contributed by FL, 17-May-2010.) $)
    fnmpt2 $p |- ( A. x e. A A. y e. B C e. V -> F Fn ( A X. B ) ) $=
      cC cV wcel vy cB wral vx cA wral cC cvv wcel vy cB wral vx cA wral cF cA
      cB cxp wfn cC cV wcel vy cB wral cC cvv wcel vy cB wral vx cA cC cV wcel
      cC cvv wcel vy cB cC cV elex ralimi ralimi cC cvv wcel vy cB wral vx cA
      wral cA cB cxp cvv cF wf cF cA cB cxp wfn vx vy cA cB cC cvv cF fmpt2.1
      fmpt2 cA cB cxp cF dffn2 bitr4i sylib $.

    fnmpt2i.2 $e |- C e. _V $.
    $( Functionality and domain of a class given by the "maps to" notation.
       (Contributed by FL, 17-May-2010.) $)
    fnmpt2i $p |- F Fn ( A X. B ) $=
      cC cvv wcel vy cB wral vx cA wral cF cA cB cxp wfn cC cvv wcel vx vy cA
      cB fnmpt2i.2 rgen2w vx vy cA cB cC cF cvv fmpt2.1 fnmpt2 ax-mp $.

    $( Domain of a class given by the "maps to" notation.  (Contributed by FL,
       17-May-2010.) $)
    dmmpt2 $p |- dom F = ( A X. B ) $=
      cF cA cB cxp wfn cF cdm cA cB cxp wceq vx vy cA cB cC cF fmpt2.1
      fnmpt2i.2 fnmpt2i cA cB cxp cF fndm ax-mp $.
  $}

  ${
    $d A x y z $.  $d B y z $.  $d C z $.
    mpt2exg.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( Existence of an operation class abstraction (version for dependent
       domains).  (Contributed by Mario Carneiro, 30-Dec-2016.) $)
    mpt2exxg $p |- ( ( A e. R /\ A. x e. A B e. S ) -> F e. _V ) $=
      cA cR wcel cB cS wcel vx cA wral wa cF wfun cF cdm cvv wcel cF cvv wcel
      vx vy cA cB cC cF mpt2exg.1 mpt2fun cA cR wcel cB cS wcel vx cA wral wa
      cF cdm vx cA vx cv csn cB cxp ciun wss vx cA vx cv csn cB cxp ciun cvv
      wcel cF cdm cvv wcel vx vy cA cB cC cF mpt2exg.1 dmmpt2ssx cB cS wcel vx
      cA wral cA cR wcel vx cv csn cB cxp cvv wcel vx cA wral vx cA vx cv csn
      cB cxp ciun cvv wcel cB cS wcel vx cv csn cB cxp cvv wcel vx cA vx cv csn
      cvv wcel cB cS wcel vx cv csn cB cxp cvv wcel vx cv snex vx cv csn cB cvv
      cS xpexg mpan ralimi vx cA vx cv csn cB cxp cR cvv iunexg sylan2 cF cdm
      vx cA vx cv csn cB cxp ciun cvv ssexg sylancr cvv cF funex sylancr $.

    $d x B $.
    $( Existence of an operation class abstraction (special case).
       (Contributed by FL, 17-May-2010.)  (Revised by Mario Carneiro,
       1-Sep-2015.) $)
    mpt2exg $p |- ( ( A e. R /\ B e. S ) -> F e. _V ) $=
      cB cS wcel cA cR wcel cB cvv wcel vx cA wral cF cvv wcel cB cS wcel cB
      cvv wcel cB cvv wcel vx cA wral cB cS elex cB cvv wcel cB cvv wcel vx cA
      cB cvv elex ralrimivw syl vx vy cA cB cC cR cvv cF mpt2exg.1 mpt2exxg
      sylan2 $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d z C $.
    $( If the domain of a function given by maps-to notation is a set, the
       function is a set.  (Contributed by NM, 12-Sep-2011.) $)
    mpt2exga $p |- ( ( A e. V /\ B e. W )
                       -> ( x e. A , y e. B |-> C ) e. _V ) $=
      vx vy cA cB cC cV cW vx vy cA cB cC cmpt2 vx vy cA cB cC cmpt2 eqid
      mpt2exg $.
  $}

  ${
    $d x y A $.  $d y B $.
    mpt2ex.1 $e |- A e. _V $.
    mpt2ex.2 $e |- B e. _V $.
    $( If the domain of a function given by maps-to notation is a set, the
       function is a set.  (Contributed by Mario Carneiro, 20-Dec-2013.) $)
    mpt2ex $p |- ( x e. A , y e. B |-> C ) e. _V $=
      cA cvv wcel cB cvv wcel vx cA wral vx vy cA cB cC cmpt2 cvv wcel mpt2ex.1
      cB cvv wcel vx cA mpt2ex.2 rgenw vx vy cA cB cC cvv cvv vx vy cA cB cC
      cmpt2 vx vy cA cB cC cmpt2 eqid mpt2exxg mp2an $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w z B $.  $d w z C $.
    $( A mapping operation with empty domain.  (Contributed by Stefan O'Rear,
       29-Jan-2015.)  (Revised by Mario Carneiro, 15-May-2015.) $)
    mpt20 $p |- ( x e. (/) , y e. B |-> C ) = (/) $=
      vx vy c0 cB cC cmpt2 vx cv c0 wcel vy cv cB wcel wa vz cv cC wceq wa vx
      vy vz coprab vw cv vx cv vy cv cop vz cv cop wceq vx cv c0 wcel vy cv cB
      wcel wa vz cv cC wceq wa wa vz wex vy wex vx wex vw cab c0 vx vy vz c0 cB
      cC df-mpt2 vx cv c0 wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz vw
      df-oprab vw cv vx cv vy cv cop vz cv cop wceq vx cv c0 wcel vy cv cB wcel
      wa vz cv cC wceq wa wa vz wex vy wex vx wex vw vw cv vx cv vy cv cop vz
      cv cop wceq vx cv c0 wcel vy cv cB wcel wa vz cv cC wceq wa wa vz wex vy
      wex vx vw cv vx cv vy cv cop vz cv cop wceq vx cv c0 wcel vy cv cB wcel
      wa vz cv cC wceq wa wa vz wex vy vw cv vx cv vy cv cop vz cv cop wceq vx
      cv c0 wcel vy cv cB wcel wa vz cv cC wceq wa wa vz vw cv vx cv vy cv cop
      vz cv cop wceq vx cv c0 wcel vy cv cB wcel wa vz cv cC wceq wa wa vx cv
      c0 wcel vx cv noel vw cv vx cv vy cv cop vz cv cop wceq vx cv c0 wcel vy
      cv cB wcel vz cv cC wceq simprll mto nex nex nex abf 3eqtri $.
  $}

  ${
    $d u v x y z A $.  $d u v y z B $.  $d u v z C $.  $d u v x y z X $.
    ovmptss.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( If all the values of the mapping are subsets of a class ` X ` , then so
       is any evaluation of the mapping.  (Contributed by Mario Carneiro,
       24-Dec-2016.) $)
    ovmptss $p |- ( A. x e. A A. y e. B C C_ X -> ( E F G ) C_ X ) $=
      vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb cX wss vz vx cA vx cv csn
      cB cxp ciun wral cE cG cop cF cfv cX wss cC cX wss vy cB wral vx cA wral
      cE cG cF co cX wss vz vx cA vx cv csn cB cxp ciun vx vz cv c1st cfv vy vz
      cv c2nd cfv cC csb csb cX cE cG cop cF cF vx vy cA cB cC cmpt2 vz vx cA
      vx cv csn cB cxp ciun vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb cmpt
      ovmptss.1 vx vy vz cA cB cC mpt2mptsx eqtri fvmptss vx vz cv c1st cfv vy
      vz cv c2nd cfv cC csb csb cX wss vz vu cA vu cv csn vx vu cv cB csb cxp
      ciun wral vx vu cv vy vv cv cC csb csb cX wss vv vx vu cv cB csb wral vu
      cA wral vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb cX wss vz vx cA vx
      cv csn cB cxp ciun wral cC cX wss vy cB wral vx cA wral vx vz cv c1st cfv
      vy vz cv c2nd cfv cC csb csb cX wss vx vu cv vy vv cv cC csb csb cX wss
      vz vu vv cA vx vu cv cB csb vz cv vu cv vv cv cop wceq vx vz cv c1st cfv
      vy vz cv c2nd cfv cC csb csb vx vu cv vy vv cv cC csb csb cX vz cv vu cv
      vv cv cop wceq vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb vx vu cv vy
      vz cv c2nd cfv cC csb csb vx vu cv vy vv cv cC csb csb vz cv vu cv vv cv
      cop wceq vx vz cv c1st cfv vu cv vy vz cv c2nd cfv cC csb vu cv vv cv vz
      cv vu vex vv vex op1std csbeq1d vz cv vu cv vv cv cop wceq vx vu cv vy vz
      cv c2nd cfv cC csb vy vv cv cC csb vz cv vu cv vv cv cop wceq vy vz cv
      c2nd cfv vv cv cC vu cv vv cv vz cv vu vex vv vex op2ndd csbeq1d csbeq2dv
      eqtrd sseq1d raliunxp vx vz cv c1st cfv vy vz cv c2nd cfv cC csb csb cX
      wss vz vx cA vx cv csn cB cxp ciun vu cA vu cv csn vx vu cv cB csb cxp
      ciun vx vu cA vx cv csn cB cxp vu cv csn vx vu cv cB csb cxp vu vx cv csn
      cB cxp nfcv vx vu cv csn vx vu cv cB csb vx vu cv csn nfcv vx vu cv cB
      nfcsb1v nfxp vx cv vu cv wceq vx cv csn vu cv csn cB vx vu cv cB csb vx
      cv vu cv sneq vx vu cv cB csbeq1a xpeq12d cbviun raleqi cC cX wss vy cB
      wral vx vu cv vy vv cv cC csb csb cX wss vv vx vu cv cB csb wral vx vu cA
      cC cX wss vy cB wral vu nfv vx vu cv vy vv cv cC csb csb cX wss vx vv vx
      vu cv cB csb vx vu cv cB nfcsb1v vx vx vu cv vy vv cv cC csb csb cX vx vu
      cv vy vv cv cC csb nfcsb1v vx cX nfcv nfss nfral cC cX wss vy cB wral vy
      vv cv cC csb cX wss vv cB wral vx cv vu cv wceq vx vu cv vy vv cv cC csb
      csb cX wss vv vx vu cv cB csb wral cC cX wss vy vv cv cC csb cX wss vy vv
      cB cC cX wss vv nfv vy vy vv cv cC csb cX vy vv cv cC nfcsb1v vy cX nfcv
      nfss vy cv vv cv wceq cC vy vv cv cC csb cX vy vv cv cC csbeq1a sseq1d
      cbvral vx cv vu cv wceq vy vv cv cC csb cX wss vx vu cv vy vv cv cC csb
      csb cX wss vv cB vx vu cv cB csb vx vu cv cB csbeq1a vx cv vu cv wceq vy
      vv cv cC csb vx vu cv vy vv cv cC csb csb cX vx vu cv vy vv cv cC csb
      csbeq1a sseq1d raleqbidv syl5bb cbvral 3bitr4ri cE cG cF co cE cG cop cF
      cfv cX cE cG cF df-ov sseq1i 3imtr4i $.
  $}

  ${
    $d t u v w x y z $.  $d t u v y B $.  $d t C $.  $d t D $.  $d t u v ph $.
    $d t u v x y A $.
    relmpt2opab.1 $e |- F = ( x e. A , y e. B |-> { <. z , w >. | ph } ) $.
    $( Any function to sets of ordered pairs produces a relation on function
       value unconditionally.  (Contributed by Mario Carneiro, 9-Feb-2015.) $)
    relmpt2opab $p |- Rel ( C F D ) $=
      cC cD cF co wrel cC cD cF co cvv cvv cxp wss wph vz vw copab cvv cvv cxp
      wss vy cB wral vx cA wral cC cD cF co cvv cvv cxp wss wph vz vw copab cvv
      cvv cxp wss vy cB wral vx cA wph vz vw copab cvv cvv cxp wss vy cB wph vz
      vw copab wrel wph vz vw copab cvv cvv cxp wss wph vz vw relopab wph vz vw
      copab df-rel mpbi rgenw rgenw vx vy cA cB wph vz vw copab cC cF cD cvv
      cvv cxp relmpt2opab.1 ovmptss ax-mp cC cD cF co df-rel mpbir $.
  $}

  ${
    $d t u v w x y B $.  $d t u w x y z C $.  $d x y ph $.  $d t u v w x y S $.
    $d u v w x y A $.  $d t u v w z R $.  $d t z T $.
    fmpt2co.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> R e. C ) $.
    fmpt2co.2 $e |- ( ph -> F = ( x e. A , y e. B |-> R ) ) $.
    fmpt2co.3 $e |- ( ph -> G = ( z e. C |-> S ) ) $.
    fmpt2co.4 $e |- ( z = R -> S = T ) $.
    $( Composition of two functions.  Variation of ~ fmptco when the second
       function has two arguments.  (Contributed by Mario Carneiro,
       8-Feb-2015.) $)
    fmpt2co $p |- ( ph -> ( G o. F ) = ( x e. A , y e. B |-> T ) ) $=
      wph cG cF ccom vw cA cB cxp vz vy vw cv c2nd cfv vx vw cv c1st cfv cR csb
      csb cS csb cmpt vx vy cA cB cT cmpt2 wph vw vz cA cB cxp cC vy vw cv c2nd
      cfv vx vw cv c1st cfv cR csb csb cS cF cG wph cA cB cxp cC vx vy cA cB cR
      cmpt2 wf vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb cC wcel vw cA cB
      cxp wral wph cR cC wcel vy cB wral vx cA wral cA cB cxp cC vx vy cA cB cR
      cmpt2 wf wph cR cC wcel vx vy cA cB fmpt2co.1 ralrimivva vx vy cA cB cR
      cC vx vy cA cB cR cmpt2 vx vy cA cB cR cmpt2 eqid fmpt2 sylib vw cA cB
      cxp cC vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb vx vy cA cB cR
      cmpt2 vx vy cA cB cR cmpt2 vu vv cA cB vy vv cv vx vu cv cR csb csb cmpt2
      vw cA cB cxp vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb cmpt vx vy vu
      vv cA cB cR vy vv cv vx vu cv cR csb csb vu cR nfcv vv cR nfcv vx vy vv
      cv vx vu cv cR csb vx vv cv nfcv vx vu cv cR nfcsb1v nfcsb vy vv cv vx vu
      cv cR csb nfcsb1v vx cv vu cv wceq vy cv vv cv wceq cR vx vu cv cR csb vy
      vv cv vx vu cv cR csb csb vx vu cv cR csbeq1a vy vv cv vx vu cv cR csb
      csbeq1a sylan9eq cbvmpt2 vu vv vw cA cB vy vw cv c2nd cfv vx vw cv c1st
      cfv cR csb csb vy vv cv vx vu cv cR csb csb vw cv vu cv vv cv cop wceq vy
      vw cv c2nd cfv vx vw cv c1st cfv cR csb csb vy vv cv vx vw cv c1st cfv cR
      csb csb vy vv cv vx vu cv cR csb csb vw cv vu cv vv cv cop wceq vy vw cv
      c2nd cfv vv cv vx vw cv c1st cfv cR csb vu cv vv cv vw cv vu vex vv vex
      op2ndd csbeq1d vw cv vu cv vv cv cop wceq vy vv cv vx vw cv c1st cfv cR
      csb vx vu cv cR csb vw cv vu cv vv cv cop wceq vx vw cv c1st cfv vu cv cR
      vu cv vv cv vw cv vu vex vv vex op1std csbeq1d csbeq2dv eqtrd mpt2mpt
      eqtr4i fmpt sylibr wph cF vx vy cA cB cR cmpt2 vw cA cB cxp vy vw cv c2nd
      cfv vx vw cv c1st cfv cR csb csb cmpt fmpt2co.2 vx vy cA cB cR cmpt2 vu
      vv cA cB vy vv cv vx vu cv cR csb csb cmpt2 vw cA cB cxp vy vw cv c2nd
      cfv vx vw cv c1st cfv cR csb csb cmpt vx vy vu vv cA cB cR vy vv cv vx vu
      cv cR csb csb vu cR nfcv vv cR nfcv vx vy vv cv vx vu cv cR csb vx vv cv
      nfcv vx vu cv cR nfcsb1v nfcsb vy vv cv vx vu cv cR csb nfcsb1v vx cv vu
      cv wceq vy cv vv cv wceq cR vx vu cv cR csb vy vv cv vx vu cv cR csb csb
      vx vu cv cR csbeq1a vy vv cv vx vu cv cR csb csbeq1a sylan9eq cbvmpt2 vu
      vv vw cA cB vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb vy vv cv vx vu
      cv cR csb csb vw cv vu cv vv cv cop wceq vy vw cv c2nd cfv vx vw cv c1st
      cfv cR csb csb vy vv cv vx vw cv c1st cfv cR csb csb vy vv cv vx vu cv cR
      csb csb vw cv vu cv vv cv cop wceq vy vw cv c2nd cfv vv cv vx vw cv c1st
      cfv cR csb vu cv vv cv vw cv vu vex vv vex op2ndd csbeq1d vw cv vu cv vv
      cv cop wceq vy vv cv vx vw cv c1st cfv cR csb vx vu cv cR csb vw cv vu cv
      vv cv cop wceq vx vw cv c1st cfv vu cv cR vu cv vv cv vw cv vu vex vv vex
      op1std csbeq1d csbeq2dv eqtrd mpt2mpt eqtr4i syl6eq fmpt2co.3 fmptcos wph
      vw cA cB cxp vz vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb cS csb
      cmpt vx vy cA cB vz cR cS csb cmpt2 vx vy cA cB cT cmpt2 vw cA cB cxp vz
      vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb cS csb cmpt vu vv cA cB vz
      vy vv cv vx vu cv cR csb csb cS csb cmpt2 vx vy cA cB vz cR cS csb cmpt2
      vu vv vw cA cB vz vy vw cv c2nd cfv vx vw cv c1st cfv cR csb csb cS csb
      vz vy vv cv vx vu cv cR csb csb cS csb vw cv vu cv vv cv cop wceq vz vy
      vw cv c2nd cfv vx vw cv c1st cfv cR csb csb vy vv cv vx vu cv cR csb csb
      cS vw cv vu cv vv cv cop wceq vy vw cv c2nd cfv vx vw cv c1st cfv cR csb
      csb vy vv cv vx vw cv c1st cfv cR csb csb vy vv cv vx vu cv cR csb csb vw
      cv vu cv vv cv cop wceq vy vw cv c2nd cfv vv cv vx vw cv c1st cfv cR csb
      vu cv vv cv vw cv vu vex vv vex op2ndd csbeq1d vw cv vu cv vv cv cop wceq
      vy vv cv vx vw cv c1st cfv cR csb vx vu cv cR csb vw cv vu cv vv cv cop
      wceq vx vw cv c1st cfv vu cv cR vu cv vv cv vw cv vu vex vv vex op1std
      csbeq1d csbeq2dv eqtrd csbeq1d mpt2mpt vx vy vu vv cA cB vz cR cS csb vz
      vy vv cv vx vu cv cR csb csb cS csb vu vz cR cS csb nfcv vv vz cR cS csb
      nfcv vx vz vy vv cv vx vu cv cR csb csb cS vx vy vv cv vx vu cv cR csb vx
      vv cv nfcv vx vu cv cR nfcsb1v nfcsb vx cS nfcv nfcsb vy vz vy vv cv vx
      vu cv cR csb csb cS vy vv cv vx vu cv cR csb nfcsb1v vy cS nfcv nfcsb vx
      cv vu cv wceq vy cv vv cv wceq wa vz cR vy vv cv vx vu cv cR csb csb cS
      vx cv vu cv wceq vy cv vv cv wceq cR vx vu cv cR csb vy vv cv vx vu cv cR
      csb csb vx vu cv cR csbeq1a vy vv cv vx vu cv cR csb csbeq1a sylan9eq
      csbeq1d cbvmpt2 eqtr4i wph vx vy cA cB vz cR cS csb cT wph vx cv cA wcel
      vy cv cB wcel w3a cR cC wcel vz cR cS csb cT wceq wph vx cv cA wcel vy cv
      cB wcel cR cC wcel fmpt2co.1 3impb vz cR cS cT cC cR cC wcel vz cT nfcvd
      fmpt2co.4 csbiegf syl mpt2eq3dva syl5eq eqtrd $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d x y z D $.  $d w x y z H $.
    $d w z C $.
    oprabco.1 $e |- ( ( x e. A /\ y e. B ) -> C e. D ) $.
    oprabco.2 $e |- F = ( x e. A , y e. B |-> C ) $.
    oprabco.3 $e |- G = ( x e. A , y e. B |-> ( H ` C ) ) $.
    $( Composition of a function with an operator abstraction.  (Contributed by
       Jeff Madsen, 2-Sep-2009.)  (Proof shortened by Mario Carneiro,
       26-Sep-2015.) $)
    oprabco $p |- ( H Fn D -> G = ( H o. F ) ) $=
      cH cD wfn cH cF ccom vx vy cA cB cC cH cfv cmpt2 cG cH cD wfn vx vy vz cA
      cB cD cC vz cv cH cfv cC cH cfv cF cH vx cv cA wcel vy cv cB wcel wa cC
      cD wcel cH cD wfn oprabco.1 adantl cF vx vy cA cB cC cmpt2 wceq cH cD wfn
      oprabco.2 a1i cH cD wfn cH vz cD vz cv cH cfv cmpt wceq vz cD cH dffn5
      biimpi vz cv cC cH fveq2 fmpt2co oprabco.3 syl6reqr $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w z C $.  $d w z D $.  $d w x y z M $.
    $d x y z R $.  $d x y z S $.
    oprab2co.1 $e |- ( ( x e. A /\ y e. B ) -> C e. R ) $.
    oprab2co.2 $e |- ( ( x e. A /\ y e. B ) -> D e. S ) $.
    oprab2co.3 $e |- F = ( x e. A , y e. B |-> <. C , D >. ) $.
    oprab2co.4 $e |- G = ( x e. A , y e. B |-> ( C M D ) ) $.
    $( Composition of operator abstractions.  (Contributed by Jeff Madsen,
       2-Sep-2009.)  (Revised by David Abernethy, 23-Apr-2013.) $)
    oprab2co $p |- ( M Fn ( R X. S ) -> G = ( M o. F ) ) $=
      vx vy cA cB cC cD cop cR cS cxp cF cG cM vx cv cA wcel vy cv cB wcel wa
      cC cR wcel cD cS wcel cC cD cop cR cS cxp wcel oprab2co.1 oprab2co.2 cC
      cD cR cS opelxpi syl2anc oprab2co.3 cG vx vy cA cB cC cD cM co cmpt2 vx
      vy cA cB cC cD cop cM cfv cmpt2 oprab2co.4 vx vy cA cB cC cD cM co cC cD
      cop cM cfv cC cD cM co cC cD cop cM cfv wceq vx cv cA wcel vy cv cB wcel
      wa cC cD cM df-ov a1i mpt2eq3ia eqtri oprabco $.
  $}

  ${
    $d w x y z $.
    $( An alternate possible definition of the ` 1st ` function.  (Contributed
       by NM, 14-Oct-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    df1st2 $p |- { <. <. x , y >. , z >. | z = x } = ( 1st |` ( _V X. _V ) ) $=
      c1st cvv cvv cxp cres vz cv vw cv c1st cfv wceq vw vz copab cvv cvv cxp
      cres vw cv cvv cvv cxp wcel vz cv vw cv c1st cfv wceq wa vw vz copab vz
      cv vx cv wceq vx vy vz coprab c1st vz cv vw cv c1st cfv wceq vw vz copab
      cvv cvv cxp c1st vw cvv vw cv c1st cfv cmpt vz cv vw cv c1st cfv wceq vw
      vz copab c1st cvv wfn c1st vw cvv vw cv c1st cfv cmpt wceq cvv cvv c1st
      wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp vw cvv c1st dffn5 mpbi vw
      vz vw cv c1st cfv mptv eqtri reseq1i vz cv vw cv c1st cfv wceq vw vz cvv
      cvv cxp resopab vz cv vw cv c1st cfv wceq vz cv vx cv wceq vx vy vz vw vw
      cv vx cv vy cv cop wceq vw cv c1st cfv vx cv vz cv vx cv vy cv vw cv vx
      vex vy vex op1std eqeq2d dfoprab3 3eqtrri $.

    $( An alternate possible definition of the ` 2nd ` function.  (Contributed
       by NM, 10-Aug-2006.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    df2nd2 $p |- { <. <. x , y >. , z >. | z = y } = ( 2nd |` ( _V X. _V ) ) $=
      c2nd cvv cvv cxp cres vz cv vw cv c2nd cfv wceq vw vz copab cvv cvv cxp
      cres vw cv cvv cvv cxp wcel vz cv vw cv c2nd cfv wceq wa vw vz copab vz
      cv vy cv wceq vx vy vz coprab c2nd vz cv vw cv c2nd cfv wceq vw vz copab
      cvv cvv cxp c2nd vw cvv vw cv c2nd cfv cmpt vz cv vw cv c2nd cfv wceq vw
      vz copab c2nd cvv wfn c2nd vw cvv vw cv c2nd cfv cmpt wceq cvv cvv c2nd
      wfo c2nd cvv wfn fo2nd cvv cvv c2nd fofn ax-mp vw cvv c2nd dffn5 mpbi vw
      vz vw cv c2nd cfv mptv eqtri reseq1i vz cv vw cv c2nd cfv wceq vw vz cvv
      cvv cxp resopab vz cv vw cv c2nd cfv wceq vz cv vy cv wceq vx vy vz vw vw
      cv vx cv vy cv cop wceq vw cv c2nd cfv vy cv vz cv vx cv vy cv vw cv vx
      vex vy vex op2ndd eqeq2d dfoprab3 3eqtrri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y V $.
    $( The mapping of a restriction of the ` 1st ` function to a constant
       function.  (Contributed by NM, 14-Dec-2008.) $)
    1stconst $p |- ( B e. V ->
             ( 1st |` ( A X. { B } ) ) : ( A X. { B } ) -1-1-onto-> A ) $=
      cB cV wcel cA cB csn cxp cA c1st cA cB csn cxp cres wfo c1st cA cB csn
      cxp cres ccnv wfun cA cB csn cxp cA c1st cA cB csn cxp cres wf1o cB cV
      wcel cB csn c0 wne cA cB csn cxp cA c1st cA cB csn cxp cres wfo cB cV
      snnzg cA cB csn fo1stres syl cB cV wcel vx cv vy cv c1st cA cB csn cxp
      cres wbr vx wmo vy wal c1st cA cB csn cxp cres ccnv wfun cB cV wcel vx cv
      vy cv c1st cA cB csn cxp cres wbr vx wmo vy cB cV wcel vx cv vy cv c1st
      cA cB csn cxp cres wbr vx wmo vy cv cA wcel vx cv vy cv cB cop wceq wa vx
      wmo vx cv vy cv cB cop wceq vy cv cA wcel vx vx vy cv cB cop moeq moani
      cB cV wcel vx cv vy cv c1st cA cB csn cxp cres wbr vy cv cA wcel vx cv vy
      cv cB cop wceq wa vx vx cv vy cv c1st cA cB csn cxp cres wbr vx cv vy cv
      c1st wbr vx cv cA cB csn cxp wcel wa cB cV wcel vy cv cA wcel vx cv vy cv
      cB cop wceq wa vx cv vy cv c1st cA cB csn cxp vy vex brres vx cv vy cv
      c1st wbr vx cv cA cB csn cxp wcel wa vx cv c1st cfv vy cv wceq vx cv cA
      cB csn cxp wcel wa cB cV wcel vy cv cA wcel vx cv vy cv cB cop wceq wa vx
      cv c1st cfv vy cv wceq vx cv vy cv c1st wbr vx cv cA cB csn cxp wcel c1st
      cvv wfn vx cv cvv wcel vx cv c1st cfv vy cv wceq vx cv vy cv c1st wbr wb
      cvv cvv c1st wfo c1st cvv wfn fo1st cvv cvv c1st fofn ax-mp vx vex cvv vx
      cv vy cv c1st fnbrfvb mp2an anbi1i cB cV wcel vx cv c1st cfv vy cv wceq
      vx cv cA cB csn cxp wcel wa vy cv cA wcel vx cv vy cv cB cop wceq wa vx
      cv c1st cfv vy cv wceq vx cv cA cB csn cxp wcel wa vy cv cA wcel vx cv vy
      cv cB cop wceq wa cB cV wcel vx cv cA cB csn cxp wcel vx cv c1st cfv vy
      cv wceq vx cv cvv cvv cxp wcel vx cv c1st cfv cA wcel vx cv c2nd cfv cB
      csn wcel wa wa vy cv cA wcel vx cv vy cv cB cop wceq wa vx cv cA cB csn
      elxp7 vx cv c1st cfv vy cv wceq vx cv cvv cvv cxp wcel vx cv c1st cfv cA
      wcel vx cv c2nd cfv cB csn wcel wa wa wa vy cv cA wcel vx cv vy cv cB cop
      wceq vx cv c1st cfv vy cv wceq vx cv c1st cfv cA wcel vx cv c2nd cfv cB
      csn wcel wa vy cv cA wcel vx cv cvv cvv cxp wcel vx cv c1st cfv vy cv
      wceq vx cv c1st cfv cA wcel vy cv cA wcel vx cv c2nd cfv cB csn wcel vx
      cv c1st cfv vy cv wceq vx cv c1st cfv cA wcel vy cv cA wcel vx cv c1st
      cfv vy cv cA eleq1 biimpa adantrr adantrl vx cv c1st cfv vy cv wceq vx cv
      cvv cvv cxp wcel vx cv c2nd cfv cB csn wcel vx cv vy cv cB cop wceq vx cv
      c1st cfv cA wcel vx cv c2nd cfv cB csn wcel vx cv c1st cfv vy cv wceq vx
      cv cvv cvv cxp wcel vx cv c2nd cfv cB wceq vx cv vy cv cB cop wceq vx cv
      c2nd cfv cB elsni vx cv cvv cvv cxp wcel vx cv c1st cfv vy cv wceq vx cv
      c2nd cfv cB wceq vx cv vy cv cB cop wceq vx cv vy cv cB cvv cvv eqopi
      an12s sylanr2 adantrrl jca sylan2b adantl cB cV wcel vy cv cA wcel vx cv
      vy cv cB cop wceq wa wa vx cv c1st cfv vy cv wceq vx cv cA cB csn cxp
      wcel cB cV wcel vy cv cA wcel vx cv vy cv cB cop wceq wa wa vx cv c1st
      cfv vy cv cB cop c1st cfv vy cv cB cV wcel vy cv cA wcel vx cv vy cv cB
      cop wceq wa wa vx cv vy cv cB cop c1st cB cV wcel vy cv cA wcel vx cv vy
      cv cB cop wceq simprr fveq2d cB cV wcel vy cv cA wcel vx cv vy cv cB cop
      wceq wa wa vy cv cA wcel cB cV wcel vy cv cB cop c1st cfv vy cv wceq cB
      cV wcel vy cv cA wcel vx cv vy cv cB cop wceq simprl cB cV wcel vy cv cA
      wcel vx cv vy cv cB cop wceq wa simpl vy cv cB cA cV op1stg syl2anc eqtrd
      cB cV wcel vy cv cA wcel vx cv vy cv cB cop wceq wa wa vx cv vy cv cB cop
      cA cB csn cxp cB cV wcel vy cv cA wcel vx cv vy cv cB cop wceq simprr cB
      cV wcel vy cv cA wcel vx cv vy cv cB cop wceq wa wa vy cv cA wcel cB cB
      csn wcel vy cv cB cop cA cB csn cxp wcel cB cV wcel vy cv cA wcel vx cv
      vy cv cB cop wceq simprl cB cV wcel cB cB csn wcel vy cv cA wcel vx cv vy
      cv cB cop wceq wa cB cV snidg adantr vy cv cB cA cB csn opelxpi syl2anc
      eqeltrd jca impbida syl5bbr syl5bb mobidv mpbiri alrimiv vx vy c1st cA cB
      csn cxp cres funcnv2 sylibr cA cB csn cxp cA c1st cA cB csn cxp cres
      dff1o3 sylanbrc $.

    $( The mapping of a restriction of the ` 2nd ` function to a converse
       constant function.  (Contributed by NM, 27-Mar-2008.) $)
    2ndconst $p |- ( A e. V ->
             ( 2nd |` ( { A } X. B ) ) : ( { A } X. B ) -1-1-onto-> B ) $=
      cA cV wcel cA csn cB cxp cB c2nd cA csn cB cxp cres wfo c2nd cA csn cB
      cxp cres ccnv wfun cA csn cB cxp cB c2nd cA csn cB cxp cres wf1o cA cV
      wcel cA csn c0 wne cA csn cB cxp cB c2nd cA csn cB cxp cres wfo cA cV
      snnzg cA csn cB fo2ndres syl cA cV wcel vx cv vy cv c2nd cA csn cB cxp
      cres wbr vx wmo vy wal c2nd cA csn cB cxp cres ccnv wfun cA cV wcel vx cv
      vy cv c2nd cA csn cB cxp cres wbr vx wmo vy cA cV wcel vx cv vy cv c2nd
      cA csn cB cxp cres wbr vx wmo vy cv cB wcel vx cv cA vy cv cop wceq wa vx
      wmo vx cv cA vy cv cop wceq vy cv cB wcel vx vx cA vy cv cop moeq moani
      cA cV wcel vx cv vy cv c2nd cA csn cB cxp cres wbr vy cv cB wcel vx cv cA
      vy cv cop wceq wa vx vx cv vy cv c2nd cA csn cB cxp cres wbr vx cv vy cv
      c2nd wbr vx cv cA csn cB cxp wcel wa cA cV wcel vy cv cB wcel vx cv cA vy
      cv cop wceq wa vx cv vy cv c2nd cA csn cB cxp vy vex brres vx cv vy cv
      c2nd wbr vx cv cA csn cB cxp wcel wa vx cv c2nd cfv vy cv wceq vx cv cA
      csn cB cxp wcel wa cA cV wcel vy cv cB wcel vx cv cA vy cv cop wceq wa vx
      cv c2nd cfv vy cv wceq vx cv vy cv c2nd wbr vx cv cA csn cB cxp wcel c2nd
      cvv wfn vx cv cvv wcel vx cv c2nd cfv vy cv wceq vx cv vy cv c2nd wbr wb
      cvv cvv c2nd wfo c2nd cvv wfn fo2nd cvv cvv c2nd fofn ax-mp vx vex cvv vx
      cv vy cv c2nd fnbrfvb mp2an anbi1i cA cV wcel vx cv c2nd cfv vy cv wceq
      vx cv cA csn cB cxp wcel wa vy cv cB wcel vx cv cA vy cv cop wceq wa vx
      cv c2nd cfv vy cv wceq vx cv cA csn cB cxp wcel wa vy cv cB wcel vx cv cA
      vy cv cop wceq wa cA cV wcel vx cv cA csn cB cxp wcel vx cv c2nd cfv vy
      cv wceq vx cv cvv cvv cxp wcel vx cv c1st cfv cA csn wcel vx cv c2nd cfv
      cB wcel wa wa vy cv cB wcel vx cv cA vy cv cop wceq wa vx cv cA csn cB
      elxp7 vx cv c2nd cfv vy cv wceq vx cv cvv cvv cxp wcel vx cv c1st cfv cA
      csn wcel vx cv c2nd cfv cB wcel wa wa wa vy cv cB wcel vx cv cA vy cv cop
      wceq vx cv c2nd cfv vy cv wceq vx cv c1st cfv cA csn wcel vx cv c2nd cfv
      cB wcel wa vy cv cB wcel vx cv cvv cvv cxp wcel vx cv c2nd cfv vy cv wceq
      vx cv c2nd cfv cB wcel vy cv cB wcel vx cv c1st cfv cA csn wcel vx cv
      c2nd cfv vy cv wceq vx cv c2nd cfv cB wcel vy cv cB wcel vx cv c2nd cfv
      vy cv cB eleq1 biimpa adantrl adantrl vx cv c2nd cfv vy cv wceq vx cv cvv
      cvv cxp wcel vx cv c1st cfv cA csn wcel vx cv cA vy cv cop wceq vx cv
      c2nd cfv cB wcel vx cv c1st cfv cA csn wcel vx cv c2nd cfv vy cv wceq vx
      cv cvv cvv cxp wcel vx cv c1st cfv cA wceq vx cv cA vy cv cop wceq vx cv
      c1st cfv cA elsni vx cv cvv cvv cxp wcel vx cv c2nd cfv vy cv wceq vx cv
      c1st cfv cA wceq vx cv cA vy cv cop wceq vx cv cvv cvv cxp wcel vx cv
      c1st cfv cA wceq vx cv c2nd cfv vy cv wceq vx cv cA vy cv cop wceq vx cv
      cA vy cv cvv cvv eqopi ancom2s an12s sylanr2 adantrrr jca sylan2b adantl
      cA cV wcel vy cv cB wcel vx cv cA vy cv cop wceq wa wa vx cv c2nd cfv vy
      cv wceq vx cv cA csn cB cxp wcel cA cV wcel vx cv cA vy cv cop wceq vx cv
      c2nd cfv vy cv wceq vy cv cB wcel vx cv cA vy cv cop wceq cA cV wcel vx
      cv c2nd cfv cA vy cv cop c2nd cfv vy cv vx cv cA vy cv cop c2nd fveq2 cA
      cV wcel vy cv cvv wcel cA vy cv cop c2nd cfv vy cv wceq vy vex cA vy cv
      cV cvv op2ndg mpan2 sylan9eqr adantrl cA cV wcel vy cv cB wcel vx cv cA
      vy cv cop wceq wa wa vx cv cA vy cv cop cA csn cB cxp cA cV wcel vy cv cB
      wcel vx cv cA vy cv cop wceq simprr cA cV wcel vy cv cB wcel vx cv cA vy
      cv cop wceq wa wa cA cA csn wcel vy cv cB wcel cA vy cv cop cA csn cB cxp
      wcel cA cV wcel cA cA csn wcel vy cv cB wcel vx cv cA vy cv cop wceq wa
      cA cV snidg adantr cA cV wcel vy cv cB wcel vx cv cA vy cv cop wceq
      simprl cA vy cv cA csn cB opelxpi syl2anc eqeltrd jca impbida syl5bbr
      syl5bb mobidv mpbiri alrimiv vx vy c2nd cA csn cB cxp cres funcnv2 sylibr
      cA csn cB cxp cB c2nd cA csn cB cxp cres dff1o3 sylanbrc $.
  $}

  ${
    $d v w x y A $.  $d v w x y B $.  $d v w C $.
    dfmpt2.1 $e |- C e. _V $.
    $( Alternate definition for the "maps to" notation ~ df-mpt2 (although it
       requires that ` C ` be a set).  (Contributed by NM, 19-Dec-2008.)
       (Revised by Mario Carneiro, 31-Aug-2015.) $)
    dfmpt2 $p |- ( x e. A , y e. B |-> C )
                = U_ x e. A U_ y e. B { <. <. x , y >. , C >. } $=
      vx vy cA cB cC cmpt2 vw cA cB cxp vx vw cv c1st cfv vy vw cv c2nd cfv cC
      csb csb cmpt vw cA cB cxp vw cv vx vw cv c1st cfv vy vw cv c2nd cfv cC
      csb csb cop csn ciun vx cA vy cB vx cv vy cv cop cC cop csn ciun ciun vx
      vy vw cA cB cC mpt2mpts vw cA cB cxp vx vw cv c1st cfv vy vw cv c2nd cfv
      cC csb csb vx vw cv c1st cfv vy vw cv c2nd cfv cC csb vw cv c1st fvex vy
      vw cv c2nd cfv cC vw cv c2nd fvex dfmpt2.1 csbex csbex dfmpt vw vx vy cA
      cB vw cv vx vw cv c1st cfv vy vw cv c2nd cfv cC csb csb cop csn vx cv vy
      cv cop cC cop csn vx vw cv vx vw cv c1st cfv vy vw cv c2nd cfv cC csb csb
      cop vx vw cv vx vw cv c1st cfv vy vw cv c2nd cfv cC csb csb vx vw cv nfcv
      vx vw cv c1st cfv vy vw cv c2nd cfv cC csb nfcsb1v nfop nfsn vy vw cv vx
      vw cv c1st cfv vy vw cv c2nd cfv cC csb csb cop vy vw cv vx vw cv c1st
      cfv vy vw cv c2nd cfv cC csb csb vy vw cv nfcv vy vx vw cv c1st cfv vy vw
      cv c2nd cfv cC csb vy vw cv c1st cfv nfcv vy vw cv c2nd cfv cC nfcsb1v
      nfcsb nfop nfsn vw vx cv vy cv cop cC cop csn nfcv vw cv vx cv vy cv cop
      wceq vw cv vx vw cv c1st cfv vy vw cv c2nd cfv cC csb csb cop vx cv vy cv
      cop cC cop vw cv vx cv vy cv cop wceq vw cv vx cv vy cv cop vx vw cv c1st
      cfv vy vw cv c2nd cfv cC csb csb cC vw cv vx cv vy cv cop wceq id vx vy
      vw cv cC csbopeq1a opeq12d sneqd iunxpf 3eqtri $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x F $.  $d x G $.
    curry1.1 $e |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) ) $.
    $( Composition with ` ``' ( 2nd |`` ( { C } X. _V ) ) ` turns any binary
       operation ` F ` with a constant first operand into a function ` G ` of
       the second operand only.  This transformation is called "currying."
       (Contributed by NM, 28-Mar-2008.)  (Revised by Mario Carneiro,
       26-Dec-2014.) $)
    curry1 $p |- ( ( F Fn ( A X. B ) /\ C e. A ) ->
                 G = ( x e. B |-> ( C F x ) ) ) $=
      cF cA cB cxp wfn cC cA wcel wa cG vx cB vx cv cG cfv cmpt vx cB cC vx cv
      cF co cmpt cF cA cB cxp wfn cC cA wcel wa cG cB wfn cG vx cB vx cv cG cfv
      cmpt wceq cF cA cB cxp wfn cC cA wcel wa cF c2nd cC csn cvv cxp cres ccnv
      ccom wfun cF c2nd cC csn cvv cxp cres ccnv ccom cdm cB wceq cG cB wfn cF
      cA cB cxp wfn cF wfun c2nd cC csn cvv cxp cres ccnv wfun cF c2nd cC csn
      cvv cxp cres ccnv ccom wfun cC cA wcel cA cB cxp cF fnfun cC cA wcel cC
      csn cvv cxp cvv c2nd cC csn cvv cxp cres wf1o c2nd cC csn cvv cxp cres
      ccnv wfun cC cvv cA 2ndconst cC csn cvv cxp cvv c2nd cC csn cvv cxp cres
      wf1o cC csn cvv cxp cvv c2nd cC csn cvv cxp cres wfo c2nd cC csn cvv cxp
      cres ccnv wfun cC csn cvv cxp cvv c2nd cC csn cvv cxp cres dff1o3 simprbi
      syl cF c2nd cC csn cvv cxp cres ccnv funco syl2an cF cA cB cxp wfn cC cA
      wcel wa cF c2nd cC csn cvv cxp cres ccnv ccom cdm c2nd cC csn cvv cxp
      cres ccnv ccnv cF cdm cima cB cF c2nd cC csn cvv cxp cres ccnv dmco cF cA
      cB cxp wfn cC cA wcel wa c2nd cC csn cvv cxp cres ccnv ccnv cF cdm cima
      c2nd cC csn cvv cxp cres ccnv ccnv cA cB cxp cima cB cF cA cB cxp wfn cC
      cA wcel wa cF cdm cA cB cxp c2nd cC csn cvv cxp cres ccnv ccnv cF cA cB
      cxp wfn cF cdm cA cB cxp wceq cC cA wcel cA cB cxp cF fndm adantr imaeq2d
      cC cA wcel c2nd cC csn cvv cxp cres ccnv ccnv cA cB cxp cima cB wceq cF
      cA cB cxp wfn cC cA wcel c2nd cC csn cvv cxp cres ccnv ccnv cA cB cxp
      cima c2nd cC csn cvv cxp cA cB cxp cin cres crn cB c2nd cC csn cvv cxp
      cres ccnv ccnv cA cB cxp cima c2nd cC csn cvv cxp cres cA cB cxp cima
      c2nd cC csn cvv cxp cres cA cB cxp cres crn c2nd cC csn cvv cxp cA cB cxp
      cin cres crn c2nd cC csn cvv cxp cres cA cB cxp imacnvcnv c2nd cC csn cvv
      cxp cres cA cB cxp df-ima c2nd cC csn cvv cxp cres cA cB cxp cres c2nd cC
      csn cvv cxp cA cB cxp cin cres c2nd cC csn cvv cxp cA cB cxp resres rneqi
      3eqtri cC cA wcel c2nd cC csn cvv cxp cA cB cxp cin cres crn c2nd cC csn
      cB cxp cres crn cB cC cA wcel c2nd cC csn cvv cxp cA cB cxp cin cres c2nd
      cC csn cB cxp cres cC cA wcel cC csn cvv cxp cA cB cxp cin cC csn cB cxp
      c2nd cC cA wcel cC csn cvv cxp cA cB cxp cin cC csn cA cin cB cxp cC csn
      cB cxp cC csn cvv cxp cA cB cxp cin cC csn cA cin cvv cB cin cxp cC csn
      cA cin cB cxp cC csn cvv cA cB inxp cvv cB cin cB cC csn cA cin cvv cB
      cin cB cvv cin cB cvv cB incom cB inv1 eqtri xpeq2i eqtri cC cA wcel cC
      csn cA cin cC csn cB cC cA wcel cC csn cA wss cC csn cA cin cC csn wceq
      cC cA snssi cC csn cA df-ss sylib xpeq1d syl5eq reseq2d rneqd cC cA wcel
      cC csn cB cxp cB c2nd cC csn cB cxp cres wf1o cC csn cB cxp cB c2nd cC
      csn cB cxp cres wfo c2nd cC csn cB cxp cres crn cB wceq cC cB cA 2ndconst
      cC csn cB cxp cB c2nd cC csn cB cxp cres f1ofo cC csn cB cxp cB c2nd cC
      csn cB cxp cres forn 3syl eqtrd syl5eq adantl eqtrd syl5eq cG cB wfn cF
      c2nd cC csn cvv cxp cres ccnv ccom cB wfn cF c2nd cC csn cvv cxp cres
      ccnv ccom wfun cF c2nd cC csn cvv cxp cres ccnv ccom cdm cB wceq wa cB cG
      cF c2nd cC csn cvv cxp cres ccnv ccom curry1.1 fneq1i cF c2nd cC csn cvv
      cxp cres ccnv ccom cB df-fn bitri sylanbrc vx cB cG dffn5 sylib cF cA cB
      cxp wfn cC cA wcel wa vx cB vx cv cG cfv cC vx cv cF co cF cA cB cxp wfn
      cC cA wcel wa vx cv cB wcel wa vx cv cG cfv vx cv c2nd cC csn cvv cxp
      cres ccnv cfv cF cfv cC vx cv cF co cF cA cB cxp wfn cC cA wcel wa vx cv
      cB wcel wa vx cv cG cfv vx cv cF c2nd cC csn cvv cxp cres ccnv ccom cfv
      vx cv c2nd cC csn cvv cxp cres ccnv cfv cF cfv vx cv cG cF c2nd cC csn
      cvv cxp cres ccnv ccom curry1.1 fveq1i cC cA wcel vx cv cF c2nd cC csn
      cvv cxp cres ccnv ccom cfv vx cv c2nd cC csn cvv cxp cres ccnv cfv cF cfv
      wceq cF cA cB cxp wfn vx cv cB wcel cC cA wcel c2nd cC csn cvv cxp cres
      ccnv cvv wfn vx cv cF c2nd cC csn cvv cxp cres ccnv ccom cfv vx cv c2nd
      cC csn cvv cxp cres ccnv cfv cF cfv wceq cC cA wcel c2nd cC csn cvv cxp
      cres cC csn cvv cxp wfn c2nd cC csn cvv cxp cres ccnv cvv wfn cC cA wcel
      cC csn cvv cxp cvv c2nd cC csn cvv cxp cres wf1o c2nd cC csn cvv cxp cres
      cC csn cvv cxp wfn c2nd cC csn cvv cxp cres ccnv cvv wfn wa cC cvv cA
      2ndconst cC csn cvv cxp cvv c2nd cC csn cvv cxp cres dff1o4 sylib simprd
      c2nd cC csn cvv cxp cres ccnv cvv wfn vx cv cvv wcel vx cv cF c2nd cC csn
      cvv cxp cres ccnv ccom cfv vx cv c2nd cC csn cvv cxp cres ccnv cfv cF cfv
      wceq vx vex cvv cF c2nd cC csn cvv cxp cres ccnv vx cv fvco2 mpan2 syl
      ad2antlr syl5eq cF cA cB cxp wfn cC cA wcel wa vx cv cB wcel wa vx cv
      c2nd cC csn cvv cxp cres ccnv cfv cF cfv cC vx cv cop cF cfv cC vx cv cF
      co cC cA wcel vx cv cB wcel vx cv c2nd cC csn cvv cxp cres ccnv cfv cF
      cfv cC vx cv cop cF cfv wceq cF cA cB cxp wfn cC cA wcel vx cv cB wcel wa
      vx cv c2nd cC csn cvv cxp cres ccnv cfv cC vx cv cop cF cC cA wcel vx cv
      cB wcel wa cC csn cvv cxp cvv c2nd cC csn cvv cxp cres wf1o cC vx cv cop
      cC csn cvv cxp wcel wa cC vx cv cop c2nd cC csn cvv cxp cres cfv vx cv
      wceq vx cv c2nd cC csn cvv cxp cres ccnv cfv cC vx cv cop wceq cC cA wcel
      vx cv cB wcel wa cC csn cvv cxp cvv c2nd cC csn cvv cxp cres wf1o cC vx
      cv cop cC csn cvv cxp wcel cC cA wcel cC csn cvv cxp cvv c2nd cC csn cvv
      cxp cres wf1o vx cv cB wcel cC cvv cA 2ndconst adantr cC cA wcel cC vx cv
      cop cC csn cvv cxp wcel vx cv cB wcel cC cA wcel cC cC csn wcel vx cv cvv
      wcel wa cC vx cv cop cC csn cvv cxp wcel cC cA wcel cC cC csn wcel vx cv
      cvv wcel cC cA snidg vx vex jctir cC vx cv cC csn cvv opelxp sylibr
      adantr jca cC cA wcel cC vx cv cop c2nd cC csn cvv cxp cres cfv vx cv
      wceq vx cv cB wcel cC cA wcel cC vx cv cop c2nd cC csn cvv cxp cres cfv
      cC vx cv cop c2nd cfv vx cv cC cA wcel cC vx cv cop cC csn cvv cxp wcel
      cC vx cv cop c2nd cC csn cvv cxp cres cfv cC vx cv cop c2nd cfv wceq cC
      cA wcel cC cC csn wcel vx cv cvv wcel wa cC vx cv cop cC csn cvv cxp wcel
      cC cA wcel cC cC csn wcel vx cv cvv wcel cC cA snidg vx vex jctir cC vx
      cv cC csn cvv opelxp sylibr cC vx cv cop cC csn cvv cxp c2nd fvres syl cC
      cA wcel vx cv cvv wcel cC vx cv cop c2nd cfv vx cv wceq vx vex cC vx cv
      cA cvv op2ndg mpan2 eqtrd adantr cC csn cvv cxp cvv cC vx cv cop vx cv
      c2nd cC csn cvv cxp cres f1ocnvfv sylc fveq2d adantll cC vx cv cF df-ov
      syl6eqr eqtrd mpteq2dva eqtrd $.

    $( The value of a curried function with a constant first argument.
       (Contributed by NM, 28-Mar-2008.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    curry1val $p |- ( ( F Fn ( A X. B ) /\ C e. A ) ->
        ( G ` D ) = ( C F D ) ) $=
      cF cA cB cxp wfn cC cA wcel wa cD cG cfv cD vx cB cC vx cv cF co cmpt cfv
      cC cD cF co cF cA cB cxp wfn cC cA wcel wa cD cG vx cB cC vx cv cF co
      cmpt vx cA cB cC cF cG curry1.1 curry1 fveq1d cF cA cB cxp wfn cC cA wcel
      wa cD cB wcel cD vx cB cC vx cv cF co cmpt cfv cC cD cF co wceq cF cA cB
      cxp wfn cC cA wcel wa cD cB wcel wn cD vx cB cC vx cv cF co cmpt cfv cC
      cD cF co wceq cF cA cB cxp wfn cC cA wcel wa cD cB wcel wn wa cD vx cB cC
      vx cv cF co cmpt cfv c0 cC cD cF co cD cB wcel wn cD vx cB cC vx cv cF co
      cmpt cfv c0 wceq cF cA cB cxp wfn cC cA wcel wa cD cB wcel wn cD vx cB cC
      vx cv cF co cmpt cdm wcel wn cD vx cB cC vx cv cF co cmpt cfv c0 wceq cD
      vx cB cC vx cv cF co cmpt cdm wcel cD cB wcel vx cB cC vx cv cF co cmpt
      cdm cB cD vx cB cC vx cv cF co vx cB cC vx cv cF co cmpt vx cB cC vx cv
      cF co cmpt eqid dmmptss sseli con3i cD vx cB cC vx cv cF co cmpt ndmfv
      syl adantl cF cA cB cxp wfn cC cA wcel wa cF cdm cA cB cxp wceq cC cA
      wcel cD cB wcel wa wn cC cD cF co c0 wceq cD cB wcel wn cF cA cB cxp wfn
      cF cdm cA cB cxp wceq cC cA wcel cA cB cxp cF fndm adantr cC cA wcel cD
      cB wcel wa cD cB wcel cC cA wcel cD cB wcel simpr con3i cC cD cA cB cF
      ndmovg syl2an eqtr4d ex vx cD cC vx cv cF co cC cD cF co cB vx cB cC vx
      cv cF co cmpt vx cv cD cC cF oveq2 vx cB cC vx cv cF co cmpt eqid cC cD
      cF ovex fvmpt pm2.61d2 eqtrd $.

    $( Functionality of a curried function with a constant first argument.
       (Contributed by NM, 29-Mar-2008.) $)
    curry1f $p |- ( ( F : ( A X. B ) --> D /\ C e. A ) ->
                 G : B --> D ) $=
      cA cB cxp cD cF wf cC cA wcel wa cB cD cG wf cB cD vx cB cC vx cv cF co
      cmpt wf cA cB cxp cD cF wf cC cA wcel wa vx cB cC vx cv cF co cD vx cB cC
      vx cv cF co cmpt cA cB cxp cD cF wf cC cA wcel vx cv cB wcel cC vx cv cF
      co cD wcel cC vx cv cD cA cB cF fovrn 3expa vx cB cC vx cv cF co cmpt
      eqid fmptd cA cB cxp cD cF wf cC cA wcel wa cB cD cG vx cB cC vx cv cF co
      cmpt cA cB cxp cD cF wf cF cA cB cxp wfn cC cA wcel cG vx cB cC vx cv cF
      co cmpt wceq cA cB cxp cD cF ffn vx cA cB cC cF cG curry1.1 curry1 sylan
      feq1d mpbird $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x F $.  $d x G $.
    curry2.1 $e |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) ) $.
    $( Composition with ` ``' ( 1st |`` ( _V X. { C } ) ) ` turns any binary
       operation ` F ` with a constant second operand into a function ` G ` of
       the first operand only.  This transformation is called "currying."  (If
       this becomes frequently used, we can introduce a new notation for the
       hypothesis.)  (Contributed by NM, 16-Dec-2008.) $)
    curry2 $p |- ( ( F Fn ( A X. B ) /\ C e. B ) ->
                 G = ( x e. A |-> ( x F C ) ) ) $=
      cF cA cB cxp wfn cC cB wcel wa cG vx cA vx cv cG cfv cmpt vx cA vx cv cC
      cF co cmpt cF cA cB cxp wfn cC cB wcel wa cG cA wfn cG vx cA vx cv cG cfv
      cmpt wceq cF cA cB cxp wfn cC cB wcel wa cF c1st cvv cC csn cxp cres ccnv
      ccom wfun cF c1st cvv cC csn cxp cres ccnv ccom cdm cA wceq cG cA wfn cF
      cA cB cxp wfn cF wfun c1st cvv cC csn cxp cres ccnv wfun cF c1st cvv cC
      csn cxp cres ccnv ccom wfun cC cB wcel cA cB cxp cF fnfun cC cB wcel cvv
      cC csn cxp cvv c1st cvv cC csn cxp cres wf1o c1st cvv cC csn cxp cres
      ccnv wfun cvv cC cB 1stconst cvv cC csn cxp cvv c1st cvv cC csn cxp cres
      wf1o cvv cC csn cxp cvv c1st cvv cC csn cxp cres wfo c1st cvv cC csn cxp
      cres ccnv wfun cvv cC csn cxp cvv c1st cvv cC csn cxp cres dff1o3 simprbi
      syl cF c1st cvv cC csn cxp cres ccnv funco syl2an cF cA cB cxp wfn cC cB
      wcel wa cF c1st cvv cC csn cxp cres ccnv ccom cdm c1st cvv cC csn cxp
      cres ccnv ccnv cF cdm cima cA cF c1st cvv cC csn cxp cres ccnv dmco cF cA
      cB cxp wfn cC cB wcel wa c1st cvv cC csn cxp cres ccnv ccnv cF cdm cima
      c1st cvv cC csn cxp cres ccnv ccnv cA cB cxp cima cA cF cA cB cxp wfn cC
      cB wcel wa cF cdm cA cB cxp c1st cvv cC csn cxp cres ccnv ccnv cF cA cB
      cxp wfn cF cdm cA cB cxp wceq cC cB wcel cA cB cxp cF fndm adantr imaeq2d
      cC cB wcel c1st cvv cC csn cxp cres ccnv ccnv cA cB cxp cima cA wceq cF
      cA cB cxp wfn cC cB wcel c1st cvv cC csn cxp cres ccnv ccnv cA cB cxp
      cima c1st cvv cC csn cxp cA cB cxp cin cres crn cA c1st cvv cC csn cxp
      cres ccnv ccnv cA cB cxp cima c1st cvv cC csn cxp cres cA cB cxp cima
      c1st cvv cC csn cxp cres cA cB cxp cres crn c1st cvv cC csn cxp cA cB cxp
      cin cres crn c1st cvv cC csn cxp cres cA cB cxp imacnvcnv c1st cvv cC csn
      cxp cres cA cB cxp df-ima c1st cvv cC csn cxp cres cA cB cxp cres c1st
      cvv cC csn cxp cA cB cxp cin cres c1st cvv cC csn cxp cA cB cxp resres
      rneqi 3eqtri cC cB wcel c1st cvv cC csn cxp cA cB cxp cin cres crn c1st
      cA cC csn cxp cres crn cA cC cB wcel c1st cvv cC csn cxp cA cB cxp cin
      cres c1st cA cC csn cxp cres cC cB wcel cvv cC csn cxp cA cB cxp cin cA
      cC csn cxp c1st cC cB wcel cvv cC csn cxp cA cB cxp cin cA cC csn cB cin
      cxp cA cC csn cxp cvv cC csn cxp cA cB cxp cin cvv cA cin cC csn cB cin
      cxp cA cC csn cB cin cxp cvv cC csn cA cB inxp cvv cA cin cA cC csn cB
      cin cvv cA cin cA cvv cin cA cvv cA incom cA inv1 eqtri xpeq1i eqtri cC
      cB wcel cC csn cB cin cC csn cA cC cB wcel cC csn cB wss cC csn cB cin cC
      csn wceq cC cB snssi cC csn cB df-ss sylib xpeq2d syl5eq reseq2d rneqd cC
      cB wcel cA cC csn cxp cA c1st cA cC csn cxp cres wf1o cA cC csn cxp cA
      c1st cA cC csn cxp cres wfo c1st cA cC csn cxp cres crn cA wceq cA cC cB
      1stconst cA cC csn cxp cA c1st cA cC csn cxp cres f1ofo cA cC csn cxp cA
      c1st cA cC csn cxp cres forn 3syl eqtrd syl5eq adantl eqtrd syl5eq cG cA
      wfn cF c1st cvv cC csn cxp cres ccnv ccom cA wfn cF c1st cvv cC csn cxp
      cres ccnv ccom wfun cF c1st cvv cC csn cxp cres ccnv ccom cdm cA wceq wa
      cA cG cF c1st cvv cC csn cxp cres ccnv ccom curry2.1 fneq1i cF c1st cvv
      cC csn cxp cres ccnv ccom cA df-fn bitri sylanbrc vx cA cG dffn5 sylib cF
      cA cB cxp wfn cC cB wcel wa vx cA vx cv cG cfv vx cv cC cF co cF cA cB
      cxp wfn cC cB wcel wa vx cv cA wcel wa vx cv cG cfv vx cv c1st cvv cC csn
      cxp cres ccnv cfv cF cfv vx cv cC cF co cF cA cB cxp wfn cC cB wcel wa vx
      cv cA wcel wa vx cv cG cfv vx cv cF c1st cvv cC csn cxp cres ccnv ccom
      cfv vx cv c1st cvv cC csn cxp cres ccnv cfv cF cfv vx cv cG cF c1st cvv
      cC csn cxp cres ccnv ccom curry2.1 fveq1i cC cB wcel vx cv cF c1st cvv cC
      csn cxp cres ccnv ccom cfv vx cv c1st cvv cC csn cxp cres ccnv cfv cF cfv
      wceq cF cA cB cxp wfn vx cv cA wcel cC cB wcel c1st cvv cC csn cxp cres
      ccnv cvv wfn vx cv cvv wcel vx cv cF c1st cvv cC csn cxp cres ccnv ccom
      cfv vx cv c1st cvv cC csn cxp cres ccnv cfv cF cfv wceq cC cB wcel c1st
      cvv cC csn cxp cres cvv cC csn cxp wfn c1st cvv cC csn cxp cres ccnv cvv
      wfn cC cB wcel cvv cC csn cxp cvv c1st cvv cC csn cxp cres wf1o c1st cvv
      cC csn cxp cres cvv cC csn cxp wfn c1st cvv cC csn cxp cres ccnv cvv wfn
      wa cvv cC cB 1stconst cvv cC csn cxp cvv c1st cvv cC csn cxp cres dff1o4
      sylib simprd vx vex cvv cF c1st cvv cC csn cxp cres ccnv vx cv fvco2
      sylancl ad2antlr syl5eq cF cA cB cxp wfn cC cB wcel wa vx cv cA wcel wa
      vx cv c1st cvv cC csn cxp cres ccnv cfv cF cfv vx cv cC cop cF cfv vx cv
      cC cF co cC cB wcel vx cv cA wcel vx cv c1st cvv cC csn cxp cres ccnv cfv
      cF cfv vx cv cC cop cF cfv wceq cF cA cB cxp wfn cC cB wcel vx cv cA wcel
      wa vx cv c1st cvv cC csn cxp cres ccnv cfv vx cv cC cop cF cC cB wcel vx
      cv cA wcel wa cvv cC csn cxp cvv c1st cvv cC csn cxp cres wf1o vx cv cC
      cop cvv cC csn cxp wcel wa vx cv cC cop c1st cvv cC csn cxp cres cfv vx
      cv wceq vx cv c1st cvv cC csn cxp cres ccnv cfv vx cv cC cop wceq cC cB
      wcel vx cv cA wcel wa cvv cC csn cxp cvv c1st cvv cC csn cxp cres wf1o vx
      cv cC cop cvv cC csn cxp wcel cC cB wcel cvv cC csn cxp cvv c1st cvv cC
      csn cxp cres wf1o vx cv cA wcel cvv cC cB 1stconst adantr cC cB wcel vx
      cv cA wcel wa vx cv cvv wcel cC cC csn wcel vx cv cC cop cvv cC csn cxp
      wcel vx cv cvv wcel cC cB wcel vx cv cA wcel wa vx vex a1i cC cB wcel cC
      cC csn wcel vx cv cA wcel cC cB snidg adantr vx cv cC cvv cC csn opelxp
      sylanbrc jca cC cB wcel vx cv cA wcel wa vx cv cC cop c1st cvv cC csn cxp
      cres cfv vx cv cC cop c1st cfv vx cv cC cB wcel vx cv cC cop c1st cvv cC
      csn cxp cres cfv vx cv cC cop c1st cfv wceq vx cv cA wcel cC cB wcel vx
      cv cC cop cvv cC csn cxp wcel vx cv cC cop c1st cvv cC csn cxp cres cfv
      vx cv cC cop c1st cfv wceq cC cB wcel vx cv cvv wcel cC cC csn wcel vx cv
      cC cop cvv cC csn cxp wcel vx cv cvv wcel cC cB wcel vx vex a1i cC cB
      snidg vx cv cC cvv cC csn opelxp sylanbrc vx cv cC cop cvv cC csn cxp
      c1st fvres syl adantr vx cv cA wcel cC cB wcel vx cv cC cop c1st cfv vx
      cv wceq vx cv cC cA cB op1stg ancoms eqtrd cvv cC csn cxp cvv vx cv cC
      cop vx cv c1st cvv cC csn cxp cres f1ocnvfv sylc fveq2d adantll vx cv cC
      cF df-ov syl6eqr eqtrd mpteq2dva eqtrd $.

    $( Functionality of a curried function with a constant second argument.
       (Contributed by NM, 16-Dec-2008.) $)
    curry2f $p |- ( ( F : ( A X. B ) --> D /\ C e. B ) ->
                 G : A --> D ) $=
      cA cB cxp cD cF wf cC cB wcel wa cA cD cG wf cA cD vx cA vx cv cC cF co
      cmpt wf cA cB cxp cD cF wf cC cB wcel wa vx cA vx cv cC cF co cD vx cA vx
      cv cC cF co cmpt cA cB cxp cD cF wf cC cB wcel vx cv cA wcel vx cv cC cF
      co cD wcel cA cB cxp cD cF wf vx cv cA wcel cC cB wcel vx cv cC cF co cD
      wcel vx cv cC cD cA cB cF fovrn 3com23 3expa vx cA vx cv cC cF co cmpt
      eqid fmptd cA cB cxp cD cF wf cC cB wcel wa cA cD cG vx cA vx cv cC cF co
      cmpt cA cB cxp cD cF wf cF cA cB cxp wfn cC cB wcel cG vx cA vx cv cC cF
      co cmpt wceq cA cB cxp cD cF ffn vx cA cB cC cF cG curry2.1 curry2 sylan
      feq1d mpbird $.

    $( The value of a curried function with a constant second argument.
       (Contributed by NM, 16-Dec-2008.) $)
    curry2val $p |- ( ( F Fn ( A X. B ) /\ C e. B ) ->
        ( G ` D ) = ( D F C ) ) $=
      cF cA cB cxp wfn cC cB wcel wa cD cG cfv cD vx cA vx cv cC cF co cmpt cfv
      cD cC cF co cF cA cB cxp wfn cC cB wcel wa cD cG vx cA vx cv cC cF co
      cmpt vx cA cB cC cF cG curry2.1 curry2 fveq1d cF cA cB cxp wfn cC cB wcel
      wa cD cA wcel cD vx cA vx cv cC cF co cmpt cfv cD cC cF co wceq cF cA cB
      cxp wfn cD cA wcel wn cD vx cA vx cv cC cF co cmpt cfv cD cC cF co wceq
      wi cC cB wcel cF cA cB cxp wfn cD cA wcel wn cD vx cA vx cv cC cF co cmpt
      cfv cD cC cF co wceq cF cA cB cxp wfn cD cA wcel wn wa cD vx cA vx cv cC
      cF co cmpt cfv c0 cD cC cF co cD cA wcel wn cD vx cA vx cv cC cF co cmpt
      cfv c0 wceq cF cA cB cxp wfn cD cA wcel wn cD vx cA vx cv cC cF co cmpt
      cdm wcel wn cD vx cA vx cv cC cF co cmpt cfv c0 wceq cD vx cA vx cv cC cF
      co cmpt cdm wcel cD cA wcel vx cA vx cv cC cF co cmpt cdm cA cD vx cA vx
      cv cC cF co vx cA vx cv cC cF co cmpt vx cA vx cv cC cF co cmpt eqid
      dmmptss sseli con3i cD vx cA vx cv cC cF co cmpt ndmfv syl adantl cF cA
      cB cxp wfn cF cdm cA cB cxp wceq cD cA wcel cC cB wcel wa wn cD cC cF co
      c0 wceq cD cA wcel wn cA cB cxp cF fndm cD cA wcel cC cB wcel wa cD cA
      wcel cD cA wcel cC cB wcel simpl con3i cD cC cA cB cF ndmovg syl2an
      eqtr4d ex adantr vx cD vx cv cC cF co cD cC cF co cA vx cA vx cv cC cF co
      cmpt vx cv cD cC cF oveq1 vx cA vx cv cC cF co cmpt eqid cD cC cF ovex
      fvmpt pm2.61d2 eqtrd $.
  $}

  $( Lemma for ~ cnvf1o .  (Contributed by Mario Carneiro, 27-Apr-2014.) $)
  cnvf1olem $p |- ( ( Rel A /\ ( B e. A /\ C = U. `' { B } ) ) ->
                    ( C e. `' A /\ B = U. `' { C } ) ) $=
    cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cC cA ccnv wcel cB cC csn
    ccnv cuni wceq cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cC cB c2nd
    cfv cB c1st cfv cop cA ccnv cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa
    wa cC cB c1st cfv cB c2nd cfv cop csn ccnv cuni cB c2nd cfv cB c1st cfv cop
    cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cC cB csn ccnv cuni cB
    c1st cfv cB c2nd cfv cop csn ccnv cuni cA wrel cB cA wcel cC cB csn ccnv
    cuni wceq simprr cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cB csn
    ccnv cB c1st cfv cB c2nd cfv cop csn ccnv cA wrel cB cA wcel cC cB csn ccnv
    cuni wceq wa wa cB csn cB c1st cfv cB c2nd cfv cop csn cA wrel cB cA wcel
    cC cB csn ccnv cuni wceq wa wa cB cB c1st cfv cB c2nd cfv cop cA wrel cB cA
    wcel cB cB c1st cfv cB c2nd cfv cop wceq cC cB csn ccnv cuni wceq cB cA
    1st2nd adantrr sneqd cnveqd unieqd eqtrd cB c1st cfv cB c2nd cfv opswap
    syl6eq cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cB c1st cfv cB
    c2nd cfv cop cA wcel cB c2nd cfv cB c1st cfv cop cA ccnv wcel cA wrel cB cA
    wcel cC cB csn ccnv cuni wceq wa wa cB cB c1st cfv cB c2nd cfv cop cA cA
    wrel cB cA wcel cB cB c1st cfv cB c2nd cfv cop wceq cC cB csn ccnv cuni
    wceq cB cA 1st2nd adantrr cA wrel cB cA wcel cC cB csn ccnv cuni wceq
    simprl eqeltrrd cB c2nd cfv cB c1st cfv cA cB c2nd fvex cB c1st fvex
    opelcnv sylibr eqeltrd cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cB
    c1st cfv cB c2nd cfv cop cB c2nd cfv cB c1st cfv cop csn ccnv cuni cB cC
    csn ccnv cuni cB c2nd cfv cB c1st cfv cop csn ccnv cuni cB c1st cfv cB c2nd
    cfv cop cB c2nd cfv cB c1st cfv opswap eqcomi cA wrel cB cA wcel cB cB c1st
    cfv cB c2nd cfv cop wceq cC cB csn ccnv cuni wceq cB cA 1st2nd adantrr cA
    wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cC csn ccnv cB c2nd cfv cB
    c1st cfv cop csn ccnv cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cC
    csn cB c2nd cfv cB c1st cfv cop csn cA wrel cB cA wcel cC cB csn ccnv cuni
    wceq wa wa cC cB c2nd cfv cB c1st cfv cop cA wrel cB cA wcel cC cB csn ccnv
    cuni wceq wa wa cC cB c1st cfv cB c2nd cfv cop csn ccnv cuni cB c2nd cfv cB
    c1st cfv cop cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa wa cC cB csn
    ccnv cuni cB c1st cfv cB c2nd cfv cop csn ccnv cuni cA wrel cB cA wcel cC
    cB csn ccnv cuni wceq simprr cA wrel cB cA wcel cC cB csn ccnv cuni wceq wa
    wa cB csn ccnv cB c1st cfv cB c2nd cfv cop csn ccnv cA wrel cB cA wcel cC
    cB csn ccnv cuni wceq wa wa cB csn cB c1st cfv cB c2nd cfv cop csn cA wrel
    cB cA wcel cC cB csn ccnv cuni wceq wa wa cB cB c1st cfv cB c2nd cfv cop cA
    wrel cB cA wcel cB cB c1st cfv cB c2nd cfv cop wceq cC cB csn ccnv cuni
    wceq cB cA 1st2nd adantrr sneqd cnveqd unieqd eqtrd cB c1st cfv cB c2nd cfv
    opswap syl6eq sneqd cnveqd unieqd 3eqtr4a jca $.

  ${
    $d x y A $.
    $( Describe a function that maps the elements of a set to its converse
       bijectively.  (Contributed by Mario Carneiro, 27-Apr-2014.) $)
    cnvf1o $p |- ( Rel A ->
                   ( x e. A |-> U. `' { x } ) : A -1-1-onto-> `' A ) $=
      cA wrel vx vy cA cA ccnv vx cv csn ccnv cuni vy cv csn ccnv cuni vx cA vx
      cv csn ccnv cuni cmpt cvv cvv vx cA vx cv csn ccnv cuni cmpt eqid vx cv
      csn ccnv cuni cvv wcel cA wrel vx cv cA wcel wa vx cv csn ccnv vx cv csn
      vx cv snex cnvex uniex a1i vy cv csn ccnv cuni cvv wcel cA wrel vy cv cA
      ccnv wcel wa vy cv csn ccnv vy cv csn vy cv snex cnvex uniex a1i cA wrel
      vx cv cA wcel vy cv vx cv csn ccnv cuni wceq wa vy cv cA ccnv wcel vx cv
      vy cv csn ccnv cuni wceq wa cA vx cv vy cv cnvf1olem cA wrel vy cv cA
      ccnv wcel vx cv vy cv csn ccnv cuni wceq wa wa vx cv cA ccnv ccnv wcel vy
      cv vx cv csn ccnv cuni wceq wa vx cv cA wcel vy cv vx cv csn ccnv cuni
      wceq wa cA wrel vy cv cA ccnv wcel vx cv vy cv csn ccnv cuni wceq wa wa
      cA ccnv wrel vy cv cA ccnv wcel vx cv vy cv csn ccnv cuni wceq wa vx cv
      cA ccnv ccnv wcel vy cv vx cv csn ccnv cuni wceq wa cA relcnv cA wrel vy
      cv cA ccnv wcel vx cv vy cv csn ccnv cuni wceq wa simpr cA ccnv vy cv vx
      cv cnvf1olem sylancr cA wrel vx cv cA ccnv ccnv wcel vy cv vx cv csn ccnv
      cuni wceq wa vx cv cA wcel vy cv vx cv csn ccnv cuni wceq wa wb vy cv cA
      ccnv wcel vx cv vy cv csn ccnv cuni wceq wa cA wrel vx cv cA ccnv ccnv
      wcel vx cv cA wcel vy cv vx cv csn ccnv cuni wceq cA wrel cA ccnv ccnv cA
      wceq vx cv cA ccnv ccnv wcel vx cv cA wcel wb cA dfrel2 cA ccnv ccnv cA
      vx cv eleq2 sylbi anbi1d adantr mpbid impbida f1od $.
  $}

  ${
    $d x A $.  $d y B $.  $d v w x y z F $.  $d v w x y z G $.
    $d s t u v w x y z $.
    $( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
    fparlem1 $p |- ( `' ( 1st |` ( _V X. _V ) ) " { x } ) = ( { x } X. _V ) $=
      vy c1st cvv cvv cxp cres ccnv vx cv csn cima vx cv csn cvv cxp vy cv cvv
      cvv cxp wcel vy cv c1st cvv cvv cxp cres cfv vx cv wceq wa vy cv cvv cvv
      cxp wcel vy cv c1st cfv vx cv csn wcel vy cv c2nd cfv cvv wcel wa wa vy
      cv c1st cvv cvv cxp cres ccnv vx cv csn cima wcel vy cv vx cv csn cvv cxp
      wcel vy cv cvv cvv cxp wcel vy cv c1st cvv cvv cxp cres cfv vx cv wceq vy
      cv c1st cfv vx cv csn wcel vy cv c2nd cfv cvv wcel wa vy cv cvv cvv cxp
      wcel vy cv c1st cvv cvv cxp cres cfv vx cv wceq vy cv c1st cfv vx cv wceq
      vy cv c1st cfv vx cv csn wcel vy cv c2nd cfv cvv wcel wa vy cv cvv cvv
      cxp wcel vy cv c1st cvv cvv cxp cres cfv vy cv c1st cfv vx cv vy cv cvv
      cvv cxp c1st fvres eqeq1d vy cv c1st cfv vx cv wceq vy cv c1st cfv vx cv
      csn wcel vy cv c1st cfv vx cv csn wcel vy cv c2nd cfv cvv wcel wa vy cv
      c1st cfv vx cv vx vex elsnc2 vy cv c2nd cfv cvv wcel vy cv c1st cfv vx cv
      csn wcel vy cv c2nd fvex biantru bitr3i syl6bb pm5.32i cvv cvv cxp cvv
      c1st cvv cvv cxp cres wf c1st cvv cvv cxp cres cvv cvv cxp wfn vy cv c1st
      cvv cvv cxp cres ccnv vx cv csn cima wcel vy cv cvv cvv cxp wcel vy cv
      c1st cvv cvv cxp cres cfv vx cv wceq wa wb cvv cvv f1stres cvv cvv cxp
      cvv c1st cvv cvv cxp cres ffn cvv cvv cxp vx cv vy cv c1st cvv cvv cxp
      cres fniniseg mp2b vy cv vx cv csn cvv elxp7 3bitr4i eqriv $.

    $( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
    fparlem2 $p |- ( `' ( 2nd |` ( _V X. _V ) ) " { y } ) = ( _V X. { y } ) $=
      vx c2nd cvv cvv cxp cres ccnv vy cv csn cima cvv vy cv csn cxp vx cv cvv
      cvv cxp wcel vx cv c2nd cvv cvv cxp cres cfv vy cv wceq wa vx cv cvv cvv
      cxp wcel vx cv c1st cfv cvv wcel vx cv c2nd cfv vy cv csn wcel wa wa vx
      cv c2nd cvv cvv cxp cres ccnv vy cv csn cima wcel vx cv cvv vy cv csn cxp
      wcel vx cv cvv cvv cxp wcel vx cv c2nd cvv cvv cxp cres cfv vy cv wceq vx
      cv c1st cfv cvv wcel vx cv c2nd cfv vy cv csn wcel wa vx cv cvv cvv cxp
      wcel vx cv c2nd cvv cvv cxp cres cfv vy cv wceq vx cv c2nd cfv vy cv wceq
      vx cv c1st cfv cvv wcel vx cv c2nd cfv vy cv csn wcel wa vx cv cvv cvv
      cxp wcel vx cv c2nd cvv cvv cxp cres cfv vx cv c2nd cfv vy cv vx cv cvv
      cvv cxp c2nd fvres eqeq1d vx cv c2nd cfv vy cv wceq vx cv c2nd cfv vy cv
      csn wcel vx cv c1st cfv cvv wcel vx cv c2nd cfv vy cv csn wcel wa vx cv
      c2nd cfv vy cv vy vex elsnc2 vx cv c1st cfv cvv wcel vx cv c2nd cfv vy cv
      csn wcel vx cv c1st fvex biantrur bitr3i syl6bb pm5.32i cvv cvv cxp cvv
      c2nd cvv cvv cxp cres wf c2nd cvv cvv cxp cres cvv cvv cxp wfn vx cv c2nd
      cvv cvv cxp cres ccnv vy cv csn cima wcel vx cv cvv cvv cxp wcel vx cv
      c2nd cvv cvv cxp cres cfv vy cv wceq wa wb cvv cvv f2ndres cvv cvv cxp
      cvv c2nd cvv cvv cxp cres ffn cvv cvv cxp vy cv vx cv c2nd cvv cvv cxp
      cres fniniseg mp2b vx cv cvv vy cv csn elxp7 3bitr4i eqriv $.

    $( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
    fparlem3 $p |- ( F Fn A
          -> ( `' ( 1st |` ( _V X. _V ) ) o. ( F o. ( 1st |` ( _V X. _V ) ) ) )
            = U_ x e. A ( ( { x } X. _V ) X. ( { ( F ` x ) } X. _V ) ) ) $=
      cF cA wfn c1st cvv cvv cxp cres ccnv vx cA c1st cvv cvv cxp cres ccnv vx
      cv csn cima cF vx cv csn cima cxp ciun ccom vx cA c1st cvv cvv cxp cres
      ccnv c1st cvv cvv cxp cres ccnv vx cv csn cima cF vx cv csn cima cxp ccom
      ciun c1st cvv cvv cxp cres ccnv cF c1st cvv cvv cxp cres ccom ccom vx cA
      vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp ciun vx c1st cvv cvv cxp
      cres ccnv c1st cvv cvv cxp cres ccnv vx cv csn cima cF vx cv csn cima cxp
      cA coiun cF cA wfn cF c1st cvv cvv cxp cres ccom vx cA c1st cvv cvv cxp
      cres ccnv vx cv csn cima cF vx cv csn cima cxp ciun c1st cvv cvv cxp cres
      ccnv cF cA wfn cF cdm c1st cvv cvv cxp cres crn cin cA wss cF c1st cvv
      cvv cxp cres ccom vx cA c1st cvv cvv cxp cres ccnv vx cv csn cima cF vx
      cv csn cima cxp ciun wceq cF cA wfn cF cdm cF cdm c1st cvv cvv cxp cres
      crn cin cA cF cdm c1st cvv cvv cxp cres crn inss1 cA cF fndm syl5sseq vx
      cF c1st cvv cvv cxp cres cA dfco2a syl coeq2d cF cA wfn vx cA vx cv csn
      cvv cxp vx cv cF cfv csn cvv cxp cxp c1st cvv cvv cxp cres ccnv c1st cvv
      cvv cxp cres ccnv vx cv csn cima cF vx cv csn cima cxp ccom cF cA wfn vx
      cv cA wcel wa vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp c1st cvv cvv
      cxp cres ccnv vx cv cF cfv csn vx cv csn cvv cxp cxp ccnv ccom c1st cvv
      cvv cxp cres ccnv c1st cvv cvv cxp cres ccnv vx cv csn cima cF vx cv csn
      cima cxp ccom vx cv cF cfv csn vx cv csn cvv cxp cxp c1st cvv cvv cxp
      cres ccom ccnv vx cv cF cfv csn cvv cxp vx cv csn cvv cxp cxp ccnv c1st
      cvv cvv cxp cres ccnv vx cv cF cfv csn vx cv csn cvv cxp cxp ccnv ccom vx
      cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp vx cv cF cfv csn vx cv csn
      cvv cxp cxp c1st cvv cvv cxp cres ccom vx cv cF cfv csn cvv cxp vx cv csn
      cvv cxp cxp vx cv cF cfv csn vx cv csn cvv cxp cxp c1st cvv cvv cxp cres
      ccom vy vx cv cF cfv csn c1st cvv cvv cxp cres ccnv vy cv csn cima vx cv
      cF cfv csn vx cv csn cvv cxp cxp vy cv csn cima cxp ciun vx cv cF cfv csn
      cvv cxp vx cv csn cvv cxp cxp vx cv cF cfv csn vx cv csn cvv cxp cxp cdm
      c1st cvv cvv cxp cres crn cin vx cv cF cfv csn wss vx cv cF cfv csn vx cv
      csn cvv cxp cxp c1st cvv cvv cxp cres ccom vy vx cv cF cfv csn c1st cvv
      cvv cxp cres ccnv vy cv csn cima vx cv cF cfv csn vx cv csn cvv cxp cxp
      vy cv csn cima cxp ciun wceq vx cv cF cfv csn vx cv csn cvv cxp cxp cdm
      c1st cvv cvv cxp cres crn cin vx cv cF cfv csn vx cv csn cvv cxp cxp cdm
      vx cv cF cfv csn vx cv cF cfv csn vx cv csn cvv cxp cxp cdm c1st cvv cvv
      cxp cres crn inss1 vx cv cF cfv csn vx cv csn cvv cxp dmxpss sstri vy vx
      cv cF cfv csn vx cv csn cvv cxp cxp c1st cvv cvv cxp cres vx cv cF cfv
      csn dfco2a ax-mp vy vx cv cF cfv c1st cvv cvv cxp cres ccnv vy cv csn
      cima vx cv cF cfv csn vx cv csn cvv cxp cxp vy cv csn cima cxp vx cv cF
      cfv csn cvv cxp vx cv csn cvv cxp cxp vx cv cF fvex vy cv vx cv cF cfv
      wceq c1st cvv cvv cxp cres ccnv vy cv csn cima vx cv cF cfv csn cvv cxp
      vx cv cF cfv csn vx cv csn cvv cxp cxp vy cv csn cima vx cv csn cvv cxp
      vy cv vx cv cF cfv wceq c1st cvv cvv cxp cres ccnv vy cv csn cima vy cv
      csn cvv cxp vx cv cF cfv csn cvv cxp vy fparlem1 vy cv vx cv cF cfv wceq
      vy cv csn vx cv cF cfv csn cvv vy cv vx cv cF cfv sneq xpeq1d syl5eq vy
      cv vx cv cF cfv wceq vx cv cF cfv csn vx cv csn cvv cxp cxp vy cv csn
      cima vx cv cF cfv csn vx cv csn cvv cxp cxp vx cv cF cfv csn cima vx cv
      csn cvv cxp vy cv vx cv cF cfv wceq vy cv csn vx cv cF cfv csn vx cv cF
      cfv csn vx cv csn cvv cxp cxp vy cv vx cv cF cfv sneq imaeq2d vx cv cF
      cfv csn vx cv csn cvv cxp cxp vx cv cF cfv csn cima vx cv cF cfv csn vx
      cv csn cvv cxp cxp vx cv cF cfv csn cres crn vx cv csn cvv cxp vx cv cF
      cfv csn vx cv csn cvv cxp cxp vx cv cF cfv csn df-ima vx cv cF cfv csn vx
      cv csn cvv cxp cxp vx cv cF cfv csn cres crn vx cv cF cfv csn vx cv csn
      cvv cxp cxp crn vx cv csn cvv cxp vx cv cF cfv csn vx cv csn cvv cxp cxp
      vx cv cF cfv csn cres vx cv cF cfv csn vx cv csn cvv cxp cxp vx cv cF cfv
      csn vx cv cF cfv csn wss vx cv cF cfv csn vx cv csn cvv cxp cxp vx cv cF
      cfv csn cres vx cv cF cfv csn vx cv csn cvv cxp cxp wceq vx cv cF cfv csn
      ssid vx cv cF cfv csn vx cv csn cvv cxp vx cv cF cfv csn xpssres ax-mp
      rneqi vx cv cF cfv csn c0 wne vx cv cF cfv csn vx cv csn cvv cxp cxp crn
      vx cv csn cvv cxp wceq vx cv cF cfv vx cv cF fvex snnz vx cv cF cfv csn
      vx cv csn cvv cxp rnxp ax-mp eqtri eqtri syl6eq xpeq12d iunxsn eqtri
      cnveqi vx cv cF cfv csn vx cv csn cvv cxp cxp c1st cvv cvv cxp cres cnvco
      vx cv cF cfv csn cvv cxp vx cv csn cvv cxp cnvxp 3eqtr3i cF cA wfn vx cv
      cA wcel wa vx cv cF cfv csn vx cv csn cvv cxp cxp ccnv c1st cvv cvv cxp
      cres ccnv vx cv csn cima cF vx cv csn cima cxp c1st cvv cvv cxp cres ccnv
      cF cA wfn vx cv cA wcel wa vx cv cF cfv csn vx cv csn cvv cxp cxp ccnv cF
      vx cv csn cima c1st cvv cvv cxp cres ccnv vx cv csn cima cxp ccnv c1st
      cvv cvv cxp cres ccnv vx cv csn cima cF vx cv csn cima cxp cF cA wfn vx
      cv cA wcel wa vx cv cF cfv csn vx cv csn cvv cxp cxp cF vx cv csn cima
      c1st cvv cvv cxp cres ccnv vx cv csn cima cxp cF cA wfn vx cv cA wcel wa
      vx cv cF cfv csn vx cv csn cvv cxp cxp vx cv cF cfv csn c1st cvv cvv cxp
      cres ccnv vx cv csn cima cxp cF vx cv csn cima c1st cvv cvv cxp cres ccnv
      vx cv csn cima cxp c1st cvv cvv cxp cres ccnv vx cv csn cima vx cv csn
      cvv cxp vx cv cF cfv csn vx fparlem1 xpeq2i cF cA wfn vx cv cA wcel wa vx
      cv cF cfv csn cF vx cv csn cima c1st cvv cvv cxp cres ccnv vx cv csn cima
      cA vx cv cF fnsnfv xpeq1d syl5eqr cnveqd cF vx cv csn cima c1st cvv cvv
      cxp cres ccnv vx cv csn cima cnvxp syl6eq coeq2d syl5eqr iuneq2dv 3eqtr4a
      $.

    $( Lemma for ~ fpar .  (Contributed by NM, 22-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
    fparlem4 $p |- ( G Fn B
          -> ( `' ( 2nd |` ( _V X. _V ) ) o. ( G o. ( 2nd |` ( _V X. _V ) ) ) )
            = U_ y e. B ( ( _V X. { y } ) X. ( _V X. { ( G ` y ) } ) ) ) $=
      cG cB wfn c2nd cvv cvv cxp cres ccnv vy cB c2nd cvv cvv cxp cres ccnv vy
      cv csn cima cG vy cv csn cima cxp ciun ccom vy cB c2nd cvv cvv cxp cres
      ccnv c2nd cvv cvv cxp cres ccnv vy cv csn cima cG vy cv csn cima cxp ccom
      ciun c2nd cvv cvv cxp cres ccnv cG c2nd cvv cvv cxp cres ccom ccom vy cB
      cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp ciun vy c2nd cvv cvv cxp
      cres ccnv c2nd cvv cvv cxp cres ccnv vy cv csn cima cG vy cv csn cima cxp
      cB coiun cG cB wfn cG c2nd cvv cvv cxp cres ccom vy cB c2nd cvv cvv cxp
      cres ccnv vy cv csn cima cG vy cv csn cima cxp ciun c2nd cvv cvv cxp cres
      ccnv cG cB wfn cG cdm c2nd cvv cvv cxp cres crn cin cB wss cG c2nd cvv
      cvv cxp cres ccom vy cB c2nd cvv cvv cxp cres ccnv vy cv csn cima cG vy
      cv csn cima cxp ciun wceq cG cB wfn cG cdm cG cdm c2nd cvv cvv cxp cres
      crn cin cB cG cdm c2nd cvv cvv cxp cres crn inss1 cB cG fndm syl5sseq vy
      cG c2nd cvv cvv cxp cres cB dfco2a syl coeq2d cG cB wfn vy cB cvv vy cv
      csn cxp cvv vy cv cG cfv csn cxp cxp c2nd cvv cvv cxp cres ccnv c2nd cvv
      cvv cxp cres ccnv vy cv csn cima cG vy cv csn cima cxp ccom cG cB wfn vy
      cv cB wcel wa cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp c2nd cvv cvv
      cxp cres ccnv vy cv cG cfv csn cvv vy cv csn cxp cxp ccnv ccom c2nd cvv
      cvv cxp cres ccnv c2nd cvv cvv cxp cres ccnv vy cv csn cima cG vy cv csn
      cima cxp ccom vy cv cG cfv csn cvv vy cv csn cxp cxp c2nd cvv cvv cxp
      cres ccom ccnv cvv vy cv cG cfv csn cxp cvv vy cv csn cxp cxp ccnv c2nd
      cvv cvv cxp cres ccnv vy cv cG cfv csn cvv vy cv csn cxp cxp ccnv ccom
      cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp vy cv cG cfv csn cvv vy cv
      csn cxp cxp c2nd cvv cvv cxp cres ccom cvv vy cv cG cfv csn cxp cvv vy cv
      csn cxp cxp vy cv cG cfv csn cvv vy cv csn cxp cxp c2nd cvv cvv cxp cres
      ccom vx vy cv cG cfv csn c2nd cvv cvv cxp cres ccnv vx cv csn cima vy cv
      cG cfv csn cvv vy cv csn cxp cxp vx cv csn cima cxp ciun cvv vy cv cG cfv
      csn cxp cvv vy cv csn cxp cxp vy cv cG cfv csn cvv vy cv csn cxp cxp cdm
      c2nd cvv cvv cxp cres crn cin vy cv cG cfv csn wss vy cv cG cfv csn cvv
      vy cv csn cxp cxp c2nd cvv cvv cxp cres ccom vx vy cv cG cfv csn c2nd cvv
      cvv cxp cres ccnv vx cv csn cima vy cv cG cfv csn cvv vy cv csn cxp cxp
      vx cv csn cima cxp ciun wceq vy cv cG cfv csn cvv vy cv csn cxp cxp cdm
      c2nd cvv cvv cxp cres crn cin vy cv cG cfv csn cvv vy cv csn cxp cxp cdm
      vy cv cG cfv csn vy cv cG cfv csn cvv vy cv csn cxp cxp cdm c2nd cvv cvv
      cxp cres crn inss1 vy cv cG cfv csn cvv vy cv csn cxp dmxpss sstri vx vy
      cv cG cfv csn cvv vy cv csn cxp cxp c2nd cvv cvv cxp cres vy cv cG cfv
      csn dfco2a ax-mp vx vy cv cG cfv c2nd cvv cvv cxp cres ccnv vx cv csn
      cima vy cv cG cfv csn cvv vy cv csn cxp cxp vx cv csn cima cxp cvv vy cv
      cG cfv csn cxp cvv vy cv csn cxp cxp vy cv cG fvex vx cv vy cv cG cfv
      wceq c2nd cvv cvv cxp cres ccnv vx cv csn cima cvv vy cv cG cfv csn cxp
      vy cv cG cfv csn cvv vy cv csn cxp cxp vx cv csn cima cvv vy cv csn cxp
      vx cv vy cv cG cfv wceq c2nd cvv cvv cxp cres ccnv vx cv csn cima cvv vx
      cv csn cxp cvv vy cv cG cfv csn cxp vx fparlem2 vx cv vy cv cG cfv wceq
      vx cv csn vy cv cG cfv csn cvv vx cv vy cv cG cfv sneq xpeq2d syl5eq vx
      cv vy cv cG cfv wceq vy cv cG cfv csn cvv vy cv csn cxp cxp vx cv csn
      cima vy cv cG cfv csn cvv vy cv csn cxp cxp vy cv cG cfv csn cima cvv vy
      cv csn cxp vx cv vy cv cG cfv wceq vx cv csn vy cv cG cfv csn vy cv cG
      cfv csn cvv vy cv csn cxp cxp vx cv vy cv cG cfv sneq imaeq2d vy cv cG
      cfv csn cvv vy cv csn cxp cxp vy cv cG cfv csn cima vy cv cG cfv csn cvv
      vy cv csn cxp cxp vy cv cG cfv csn cres crn cvv vy cv csn cxp vy cv cG
      cfv csn cvv vy cv csn cxp cxp vy cv cG cfv csn df-ima vy cv cG cfv csn
      cvv vy cv csn cxp cxp vy cv cG cfv csn cres crn vy cv cG cfv csn cvv vy
      cv csn cxp cxp crn cvv vy cv csn cxp vy cv cG cfv csn cvv vy cv csn cxp
      cxp vy cv cG cfv csn cres vy cv cG cfv csn cvv vy cv csn cxp cxp vy cv cG
      cfv csn vy cv cG cfv csn wss vy cv cG cfv csn cvv vy cv csn cxp cxp vy cv
      cG cfv csn cres vy cv cG cfv csn cvv vy cv csn cxp cxp wceq vy cv cG cfv
      csn ssid vy cv cG cfv csn cvv vy cv csn cxp vy cv cG cfv csn xpssres
      ax-mp rneqi vy cv cG cfv csn c0 wne vy cv cG cfv csn cvv vy cv csn cxp
      cxp crn cvv vy cv csn cxp wceq vy cv cG cfv vy cv cG fvex snnz vy cv cG
      cfv csn cvv vy cv csn cxp rnxp ax-mp eqtri eqtri syl6eq xpeq12d iunxsn
      eqtri cnveqi vy cv cG cfv csn cvv vy cv csn cxp cxp c2nd cvv cvv cxp cres
      cnvco cvv vy cv cG cfv csn cxp cvv vy cv csn cxp cnvxp 3eqtr3i cG cB wfn
      vy cv cB wcel wa vy cv cG cfv csn cvv vy cv csn cxp cxp ccnv c2nd cvv cvv
      cxp cres ccnv vy cv csn cima cG vy cv csn cima cxp c2nd cvv cvv cxp cres
      ccnv cG cB wfn vy cv cB wcel wa vy cv cG cfv csn cvv vy cv csn cxp cxp
      ccnv cG vy cv csn cima c2nd cvv cvv cxp cres ccnv vy cv csn cima cxp ccnv
      c2nd cvv cvv cxp cres ccnv vy cv csn cima cG vy cv csn cima cxp cG cB wfn
      vy cv cB wcel wa vy cv cG cfv csn cvv vy cv csn cxp cxp cG vy cv csn cima
      c2nd cvv cvv cxp cres ccnv vy cv csn cima cxp cG cB wfn vy cv cB wcel wa
      vy cv cG cfv csn cvv vy cv csn cxp cxp vy cv cG cfv csn c2nd cvv cvv cxp
      cres ccnv vy cv csn cima cxp cG vy cv csn cima c2nd cvv cvv cxp cres ccnv
      vy cv csn cima cxp c2nd cvv cvv cxp cres ccnv vy cv csn cima cvv vy cv
      csn cxp vy cv cG cfv csn vy fparlem2 xpeq2i cG cB wfn vy cv cB wcel wa vy
      cv cG cfv csn cG vy cv csn cima c2nd cvv cvv cxp cres ccnv vy cv csn cima
      cB vy cv cG fnsnfv xpeq1d syl5eqr cnveqd cG vy cv csn cima c2nd cvv cvv
      cxp cres ccnv vy cv csn cima cnvxp syl6eq coeq2d syl5eqr iuneq2dv 3eqtr4a
      $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z F $.  $d x y z G $.
    fpar.1 $e |- H = ( ( `' ( 1st |` ( _V X. _V ) )
                        o. ( F o. ( 1st |` ( _V X. _V ) ) ) )
                i^i ( `' ( 2nd |` ( _V X. _V ) )
                       o. ( G o. ( 2nd |` ( _V X. _V ) ) ) ) ) $.
    $( Merge two functions in parallel.  Use as the second argument of a
       composition with a (2-place) operation to build compound operations such
       as ` z = ( ( sqr `` x ) + ( abs `` y ) ) ` .  (Contributed by NM,
       17-Sep-2007.)  (Proof shortened by Mario Carneiro, 28-Apr-2015.) $)
    fpar $p |- ( ( F Fn A /\ G Fn B )
       -> H = ( x e. A , y e. B |-> <. ( F ` x ) , ( G ` y ) >. ) ) $=
      cF cA wfn cG cB wfn wa c1st cvv cvv cxp cres ccnv cF c1st cvv cvv cxp
      cres ccom ccom c2nd cvv cvv cxp cres ccnv cG c2nd cvv cvv cxp cres ccom
      ccom cin vx cA vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp ciun vy cB
      cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp ciun cin cH vx vy cA cB vx
      cv cF cfv vy cv cG cfv cop cmpt2 cF cA wfn cG cB wfn c1st cvv cvv cxp
      cres ccnv cF c1st cvv cvv cxp cres ccom ccom vx cA vx cv csn cvv cxp vx
      cv cF cfv csn cvv cxp cxp ciun c2nd cvv cvv cxp cres ccnv cG c2nd cvv cvv
      cxp cres ccom ccom vy cB cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp
      ciun vx cA cF fparlem3 vy cB cG fparlem4 ineqan12d fpar.1 vx vy cA cB vx
      cv cF cfv vy cv cG cfv cop cmpt2 vx cA vy cB vx cv vy cv cop vx cv cF cfv
      vy cv cG cfv cop cop csn ciun ciun vx cA vy cB vx cv csn cvv cxp vx cv cF
      cfv csn cvv cxp cxp cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp cin
      ciun ciun vx cA vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp ciun vy cB
      cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp ciun cin vx vy cA cB vx cv
      cF cfv vy cv cG cfv cop vx cv cF cfv vy cv cG cfv opex dfmpt2 vx cA vy cB
      vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp cvv vy cv csn cxp cvv vy
      cv cG cfv csn cxp cxp cin ciun vy cB vx cv vy cv cop vx cv cF cfv vy cv
      cG cfv cop cop csn ciun vy cB vx cv csn cvv cxp vx cv cF cfv csn cvv cxp
      cxp cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp cin ciun vy cB vx cv
      vy cv cop vx cv cF cfv vy cv cG cfv cop cop csn ciun wceq vx cv cA wcel
      vy cB vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp cvv vy cv csn cxp
      cvv vy cv cG cfv csn cxp cxp cin vx cv vy cv cop vx cv cF cfv vy cv cG
      cfv cop cop csn vx cv csn cvv cxp vx cv cF cfv csn cvv cxp cxp cvv vy cv
      csn cxp cvv vy cv cG cfv csn cxp cxp cin vx cv vy cv cop vx cv cF cfv vy
      cv cG cfv cop cop csn wceq vy cv cB wcel vx cv csn cvv cxp vx cv cF cfv
      csn cvv cxp cxp cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp cin vx cv
      csn cvv cxp cvv vy cv csn cxp cin vx cv cF cfv csn cvv cxp cvv vy cv cG
      cfv csn cxp cin cxp vx cv vy cv cop csn vx cv cF cfv vy cv cG cfv cop csn
      cxp vx cv vy cv cop vx cv cF cfv vy cv cG cfv cop cop csn vx cv csn cvv
      cxp vx cv cF cfv csn cvv cxp cvv vy cv csn cxp cvv vy cv cG cfv csn cxp
      inxp vx cv csn cvv cxp cvv vy cv csn cxp cin vx cv vy cv cop csn vx cv cF
      cfv csn cvv cxp cvv vy cv cG cfv csn cxp cin vx cv cF cfv vy cv cG cfv
      cop csn vx cv csn cvv cxp cvv vy cv csn cxp cin vx cv csn cvv cin cvv vy
      cv csn cin cxp vx cv csn vy cv csn cxp vx cv vy cv cop csn vx cv csn cvv
      cvv vy cv csn inxp vx cv csn cvv cin vx cv csn cvv vy cv csn cin vy cv
      csn vx cv csn inv1 cvv vy cv csn cin vy cv csn cvv cin vy cv csn cvv vy
      cv csn incom vy cv csn inv1 eqtri xpeq12i vx cv vy cv vx vex vy vex xpsn
      3eqtri vx cv cF cfv csn cvv cxp cvv vy cv cG cfv csn cxp cin vx cv cF cfv
      csn cvv cin cvv vy cv cG cfv csn cin cxp vx cv cF cfv csn vy cv cG cfv
      csn cxp vx cv cF cfv vy cv cG cfv cop csn vx cv cF cfv csn cvv cvv vy cv
      cG cfv csn inxp vx cv cF cfv csn cvv cin vx cv cF cfv csn cvv vy cv cG
      cfv csn cin vy cv cG cfv csn vx cv cF cfv csn inv1 cvv vy cv cG cfv csn
      cin vy cv cG cfv csn cvv cin vy cv cG cfv csn cvv vy cv cG cfv csn incom
      vy cv cG cfv csn inv1 eqtri xpeq12i vx cv cF cfv vy cv cG cfv vx cv cF
      fvex vy cv cG fvex xpsn 3eqtri xpeq12i vx cv vy cv cop vx cv cF cfv vy cv
      cG cfv cop vx cv vy cv opex vx cv cF cfv vy cv cG cfv opex xpsn 3eqtri
      a1i iuneq2i a1i iuneq2i vx vy cA cB vx cv csn cvv cxp vx cv cF cfv csn
      cvv cxp cxp cvv vy cv csn cxp cvv vy cv cG cfv csn cxp cxp 2iunin 3eqtr2i
      3eqtr4g $.
  $}

  ${
    $d w x y z $.
    $( A function that can be used to feed a common value to both operands of
       an operation.  Use as the second argument of a composition with the
       function of ~ fpar in order to build compound functions such as
       ` y = ( ( sqr `` x ) + ( abs `` x ) ) ` .  (Contributed by NM,
       17-Sep-2007.) $)
    fsplit $p |- `' ( 1st |` _I ) = ( x e. _V |-> <. x , x >. ) $=
      vx cv vy cv c1st cid cres ccnv wbr vx vy copab vy cv vx cv vx cv cop wceq
      vx vy copab c1st cid cres ccnv vx cvv vx cv vx cv cop cmpt vx cv vy cv
      c1st cid cres ccnv wbr vy cv vx cv vx cv cop wceq vx vy vx cv vy cv c1st
      cid cres ccnv wbr vy cv vx cv c1st cid cres wbr vy cv vx cv vx cv cop
      wceq vx cv vy cv c1st cid cres vx vex vy vex brcnv vy cv vx cv c1st cid
      cres wbr vy cv vx cv c1st wbr vy cv cid wcel wa vy cv vx cv vx cv cop
      wceq vy cv vx cv c1st cid vx vex brres vy cv vx cv c1st wbr vy cv cid
      wcel wa vz cv vx cv wceq vy cv vz cv vz cv cop wceq wa vz wex vy cv vx cv
      vx cv cop wceq vy cv c1st cfv vx cv wceq vy cv vz cv vz cv cop wceq wa vz
      wex vy cv c1st cfv vx cv wceq vy cv vz cv vz cv cop wceq vz wex wa vz cv
      vx cv wceq vy cv vz cv vz cv cop wceq wa vz wex vy cv vx cv c1st wbr vy
      cv cid wcel wa vy cv c1st cfv vx cv wceq vy cv vz cv vz cv cop wceq vz
      19.42v vy cv c1st cfv vx cv wceq vy cv vz cv vz cv cop wceq wa vz cv vx
      cv wceq vy cv vz cv vz cv cop wceq wa vz vy cv vz cv vz cv cop wceq vy cv
      c1st cfv vx cv wceq vz cv vx cv wceq vy cv vz cv vz cv cop wceq vy cv
      c1st cfv vz cv vx cv vz cv vz cv vy cv vz vex vz vex op1std eqeq1d
      pm5.32ri exbii vy cv c1st cfv vx cv wceq vy cv vx cv c1st wbr vy cv vz cv
      vz cv cop wceq vz wex vy cv cid wcel c1st cvv wfn vy cv cvv wcel vy cv
      c1st cfv vx cv wceq vy cv vx cv c1st wbr wb cvv cvv c1st wfo c1st cvv wfn
      fo1st cvv cvv c1st fofn ax-mp vy vex cvv vy cv vx cv c1st fnbrfvb mp2an
      vy cv cid wcel vy cv vz cv vz cv wceq vz vz copab wcel vy cv vz cv vz cv
      cop wceq vz wex cid vz cv vz cv wceq vz vz copab vy cv vz dfid2 eleq2i vy
      cv vz cv vz cv cop wceq vz cv vz cv wceq wa vz wex vz wex vy cv vz cv vz
      cv cop wceq vz cv vz cv wceq wa vz wex vy cv vz cv vz cv wceq vz vz copab
      wcel vy cv vz cv vz cv cop wceq vz wex vy cv vz cv vz cv cop wceq vz cv
      vz cv wceq wa vz wex vz vy cv vz cv vz cv cop wceq vz cv vz cv wceq wa vz
      nfe1 19.9 vz cv vz cv wceq vz vz vy cv elopab vy cv vz cv vz cv cop wceq
      vy cv vz cv vz cv cop wceq vz cv vz cv wceq wa vz vz cv vz cv wceq vy cv
      vz cv vz cv cop wceq vz equid biantru exbii 3bitr4i bitr2i anbi12i
      3bitr3ri vy cv vz cv vz cv cop wceq vy cv vx cv vx cv cop wceq vz vx cv
      vx vex vz cv vx cv wceq vz cv vz cv cop vx cv vx cv cop vy cv vz cv vx cv
      wceq vz cv vx cv vz cv vx cv vz cv vx cv wceq id vz cv vx cv wceq id
      opeq12d eqeq2d ceqsexv bitri bitri bitri opabbii c1st cid cres ccnv wrel
      c1st cid cres ccnv vx cv vy cv c1st cid cres ccnv wbr vx vy copab wceq
      c1st cid cres relcnv vx vy c1st cid cres ccnv dfrel4v mpbi vx vy vx cv vx
      cv cop mptv 3eqtr4i $.
  $}

  ${
    algrflem.1 $e |- B e. _V $.
    algrflem.2 $e |- C e. _V $.
    $( Lemma for ~ algrf and related theorems.  (Contributed by Mario Carneiro,
       28-May-2014.)  (Revised by Mario Carneiro, 30-Apr-2015.) $)
    algrflem $p |- ( B ( F o. 1st ) C ) = ( F ` B ) $=
      cB cC cF c1st ccom co cB cC cop cF c1st ccom cfv cB cC cop c1st cfv cF
      cfv cB cF cfv cB cC cF c1st ccom df-ov cvv cvv c1st wf cB cC cop cvv wcel
      cB cC cop cF c1st ccom cfv cB cC cop c1st cfv cF cfv wceq cvv cvv c1st
      wfo cvv cvv c1st wf fo1st cvv cvv c1st fof ax-mp cB cC opex cvv cvv cB cC
      cop cF c1st fvco3 mp2an cB cC cop c1st cfv cB cF cB cC algrflem.1
      algrflem.2 op1st fveq2i 3eqtri $.
  $}

  ${
    $d A a b c s v w x y z $.  $d B a b d s v w x y z $.
    $d R a b c s v w x y $.  $d S a b d s t u v w x y $.  $d T a b s w z $.
    frxp.1 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
      /\ ( ( 1st ` x ) R ( 1st ` y ) \/
           ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two well-founded classes.  (Contributed by
       Scott Fenton, 17-Mar-2011.)  (Revised by Mario Carneiro, 7-Mar-2013.)
       (Proof shortened by Wolf Lammen, 4-Oct-2014.) $)
    frxp $p |- ( ( R Fr A /\ S Fr B ) -> T Fr ( A X. B ) ) $=
      cA cR wfr cB cS wfr wa vs cv cA cB cxp wss vs cv c0 wne wa vw cv vz cv cT
      wbr wn vw vs cv wral vz vs cv wrex wi vs wal cA cB cxp cT wfr cA cR wfr
      cB cS wfr wa vs cv cA cB cxp wss vs cv c0 wne wa vw cv vz cv cT wbr wn vw
      vs cv wral vz vs cv wrex wi vs cA cR wfr cB cS wfr wa vs cv cA cB cxp wss
      vs cv c0 wne wa vc cv va cv cR wbr wn vc vs cv cdm wral va vs cv cdm wrex
      vw cv vz cv cT wbr wn vw vs cv wral vz vs cv wrex cA cR wfr vs cv cA cB
      cxp wss vs cv c0 wne wa vc cv va cv cR wbr wn vc vs cv cdm wral va vs cv
      cdm wrex wi cB cS wfr vs cv cA cB cxp wss vs cv c0 wne wa vs cv cdm cA
      wss vs cv cdm c0 wne wa cA cR wfr vc cv va cv cR wbr wn vc vs cv cdm wral
      va vs cv cdm wrex vs cv cA cB cxp wss vs cv c0 wne wa vs cv cdm cA wss vs
      cv cdm c0 wne vs cv cA cB cxp wss vs cv c0 wne cB c0 wne vs cv cdm cA wss
      vs cv cA cB cxp wss vs cv c0 wne wa cA cB cxp c0 wne cB c0 wne vs cv cA
      cB cxp ssn0 cA cB cxp c0 wne cA c0 wne cB c0 wne cA c0 wne cB c0 wne wa
      cA cB cxp c0 wne cA cB xpnz biimpri simprd syl cB c0 wne vs cv cA cB cxp
      wss vs cv cdm cA wss cB c0 wne cA cB cxp cdm cA wceq vs cv cA cB cxp wss
      vs cv cdm cA wss wi cA cB dmxp vs cv cA cB cxp wss vs cv cdm cA cB cxp
      cdm wss cA cB cxp cdm cA wceq vs cv cdm cA wss vs cv cA cB cxp dmss cA cB
      cxp cdm cA vs cv cdm sseq2 syl5ib syl impcom syldan vs cv cA cB cxp wss
      vs cv c0 wne vs cv cdm c0 wne vs cv cA cB cxp wss vs cv c0 vs cv cdm c0
      vs cv cA cB cxp wss vs cv wrel vs cv c0 wceq vs cv cdm c0 wceq wb vs cv
      cA cB cxp wss cA cB cxp wrel vs cv wrel cA cB relxp vs cv cA cB cxp relss
      mpi vs cv reldm0 syl necon3bid biimpa jca cA cR wfr vv cv cA wss vv cv c0
      wne wa vc cv va cv cR wbr wn vc vv cv wral va vv cv wrex wi vv wal vs cv
      cdm cA wss vs cv cdm c0 wne wa vc cv va cv cR wbr wn vc vs cv cdm wral va
      vs cv cdm wrex wi vv va vc cA cR df-fr vv cv cA wss vv cv c0 wne wa vc cv
      va cv cR wbr wn vc vv cv wral va vv cv wrex wi vs cv cdm cA wss vs cv cdm
      c0 wne wa vc cv va cv cR wbr wn vc vs cv cdm wral va vs cv cdm wrex wi vv
      vs cv cdm vs cv vs vex dmex vv cv vs cv cdm wceq vv cv cA wss vv cv c0
      wne wa vs cv cdm cA wss vs cv cdm c0 wne wa vc cv va cv cR wbr wn vc vv
      cv wral va vv cv wrex vc cv va cv cR wbr wn vc vs cv cdm wral va vs cv
      cdm wrex vv cv vs cv cdm wceq vv cv cA wss vs cv cdm cA wss vv cv c0 wne
      vs cv cdm c0 wne vv cv vs cv cdm cA sseq1 vv cv vs cv cdm c0 neeq1
      anbi12d vc cv va cv cR wbr wn vc vv cv wral vc cv va cv cR wbr wn vc vs
      cv cdm wral va vv cv vs cv cdm vc cv va cv cR wbr wn vc vv cv vs cv cdm
      raleq rexeqbi1dv imbi12d spcv sylbi syl5 adantr cB cS wfr vs cv cA cB cxp
      wss vs cv c0 wne wa vc cv va cv cR wbr wn vc vs cv cdm wral va vs cv cdm
      wrex vw cv vz cv cT wbr wn vw vs cv wral vz vs cv wrex wi wi cA cR wfr cB
      cS wfr vs cv cA cB cxp wss vs cv c0 wne vc cv va cv cR wbr wn vc vs cv
      cdm wral va vs cv cdm wrex vw cv vz cv cT wbr wn vw vs cv wral vz vs cv
      wrex wi cB cS wfr vs cv cA cB cxp wss vs cv c0 wne w3a vc cv va cv cR wbr
      wn vc vs cv cdm wral vw cv vz cv cT wbr wn vw vs cv wral vz vs cv wrex va
      vs cv cdm cB cS wfr vs cv cA cB cxp wss vs cv c0 wne w3a va cv vs cv cdm
      wcel vc cv va cv cR wbr wn vc vs cv cdm wral vw cv vz cv cT wbr wn vw vs
      cv wral vz vs cv wrex cB cS wfr vs cv cA cB cxp wss vs cv c0 wne w3a va
      cv vs cv cdm wcel vc cv va cv cR wbr wn vc vs cv cdm wral wa vw cv va cv
      vb cv cop cT wbr wn vw vs cv wral vb vs cv va cv csn cima wrex vw cv vz
      cv cT wbr wn vw vs cv wral vz vs cv wrex cB cS wfr vs cv cA cB cxp wss va
      cv vs cv cdm wcel vc cv va cv cR wbr wn vc vs cv cdm wral wa vw cv va cv
      vb cv cop cT wbr wn vw vs cv wral vb vs cv va cv csn cima wrex wi vs cv
      c0 wne cB cS wfr vs cv cA cB cxp wss wa va cv vs cv cdm wcel vc cv va cv
      cR wbr wn vc vs cv cdm wral vw cv va cv vb cv cop cT wbr wn vw vs cv wral
      vb vs cv va cv csn cima wrex cB cS wfr vs cv cA cB cxp wss va cv vs cv
      cdm wcel vc cv va cv cR wbr wn vc vs cv cdm wral vw cv va cv vb cv cop cT
      wbr wn vw vs cv wral vb vs cv va cv csn cima wrex wi cB cS wfr vs cv cA
      cB cxp wss va cv vs cv cdm wcel wa vd cv vb cv cS wbr wn vd vs cv va cv
      csn cima wral vb vs cv va cv csn cima wrex vc cv va cv cR wbr wn vc vs cv
      cdm wral vw cv va cv vb cv cop cT wbr wn vw vs cv wral vb vs cv va cv csn
      cima wrex wi vs cv cA cB cxp wss cB cS wfr vs cv va cv csn cima cB wss vs
      cv va cv csn cima c0 wne vd cv vb cv cS wbr wn vd vs cv va cv csn cima
      wral vb vs cv va cv csn cima wrex va cv vs cv cdm wcel vs cv cA cB cxp
      wss vs cv va cv csn cima vs cv crn cB vs cv va cv csn imassrn vs cv cA cB
      cxp wss vs cv crn cB wss wi cA c0 cA c0 wceq vs cv cA cB cxp wss vs cv c0
      wceq vs cv crn cB wss cA c0 wceq cA cB cxp c0 wceq vs cv cA cB cxp wss vs
      cv c0 wceq wi cA c0 wceq cB c0 wceq cA cB cxp c0 wceq cA cB cxp c0 wceq
      cA c0 wceq cB c0 wceq wo cA cB xpeq0 biimpri orcs cA cB cxp c0 wceq vs cv
      cA cB cxp wss vs cv c0 wss vs cv c0 wceq cA cB cxp c0 vs cv sseq2 vs cv
      ss0 syl6bi syl vs cv c0 wceq vs cv crn c0 crn cB vs cv c0 rneq c0 crn cB
      wss vs cv c0 wceq c0 crn c0 cB rn0 cB 0ss eqsstri a1i eqsstrd syl6 cA c0
      wne cA cB cxp crn cB wceq vs cv cA cB cxp wss vs cv crn cB wss wi cA cB
      rnxp vs cv cA cB cxp wss vs cv crn cA cB cxp crn wss cA cB cxp crn cB
      wceq vs cv crn cB wss vs cv cA cB cxp rnss cA cB cxp crn cB vs cv crn
      sseq2 syl5ib syl pm2.61ine syl5ss va cv vs cv cdm wcel va cv vb cv vs cv
      wbr vb wex vs cv va cv csn cima c0 wne vb va cv vs cv va vex eldm va cv
      vb cv vs cv wbr vs cv va cv csn cima c0 wne vb va cv vb cv vs cv wbr vb
      cv vs cv va cv csn cima wcel vs cv va cv csn cima c0 wne vb cv vs cv va
      cv csn cima wcel va cv vb cv cop vs cv wcel va cv vb cv vs cv wbr vs cv
      va cv vb cv va vex vb vex elimasn va cv vb cv vs cv df-br bitr4i vs cv va
      cv csn cima vb cv ne0i sylbir exlimiv sylbi cB cS wfr vv cv cB wss vv cv
      c0 wne wa vd cv vb cv cS wbr wn vd vv cv wral vb vv cv wrex wi vv wal vs
      cv va cv csn cima cB wss vs cv va cv csn cima c0 wne wa vd cv vb cv cS
      wbr wn vd vs cv va cv csn cima wral vb vs cv va cv csn cima wrex wi vv vb
      vd cB cS df-fr vv cv cB wss vv cv c0 wne wa vd cv vb cv cS wbr wn vd vv
      cv wral vb vv cv wrex wi vs cv va cv csn cima cB wss vs cv va cv csn cima
      c0 wne wa vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vb vs cv va
      cv csn cima wrex wi vv vs cv va cv csn cima vs cv cvv wcel vs cv va cv
      csn cima cvv wcel vs vex vs cv va cv csn cvv imaexg ax-mp vv cv vs cv va
      cv csn cima wceq vv cv cB wss vv cv c0 wne wa vs cv va cv csn cima cB wss
      vs cv va cv csn cima c0 wne wa vd cv vb cv cS wbr wn vd vv cv wral vb vv
      cv wrex vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vb vs cv va cv
      csn cima wrex vv cv vs cv va cv csn cima wceq vv cv cB wss vs cv va cv
      csn cima cB wss vv cv c0 wne vs cv va cv csn cima c0 wne vv cv vs cv va
      cv csn cima cB sseq1 vv cv vs cv va cv csn cima c0 neeq1 anbi12d vd cv vb
      cv cS wbr wn vd vv cv wral vd cv vb cv cS wbr wn vd vs cv va cv csn cima
      wral vb vv cv vs cv va cv csn cima vd cv vb cv cS wbr wn vd vv cv vs cv
      va cv csn cima raleq rexeqbi1dv imbi12d spcv sylbi syl2ani vs cv cA cB
      cxp wss vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vb vs cv va cv
      csn cima wrex vc cv va cv cR wbr wn vc vs cv cdm wral vw cv va cv vb cv
      cop cT wbr wn vw vs cv wral vb vs cv va cv csn cima wrex wi wi va cv vs
      cv cdm wcel vs cv cA cB cxp wss vc cv va cv cR wbr wn vc vs cv cdm wral
      vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vb vs cv va cv csn
      cima wrex vw cv va cv vb cv cop cT wbr wn vw vs cv wral vb vs cv va cv
      csn cima wrex vs cv cA cB cxp wss vc cv va cv cR wbr wn vc vs cv cdm wral
      vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vb vs cv va cv csn
      cima wrex vw cv va cv vb cv cop cT wbr wn vw vs cv wral vb vs cv va cv
      csn cima wrex wi vs cv cA cB cxp wss vc cv va cv cR wbr wn vc vs cv cdm
      wral wa vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vw cv va cv vb
      cv cop cT wbr wn vw vs cv wral vb vs cv va cv csn cima vs cv cA cB cxp
      wss vc cv va cv cR wbr wn vc vs cv cdm wral wa vd cv vb cv cS wbr wn vd
      vs cv va cv csn cima wral vw cv cA cB cxp wcel va cv vb cv cop cA cB cxp
      wcel wa wn vw cv c1st cfv va cv cR wbr wn vw cv c1st cfv va cv wceq vw cv
      c2nd cfv vb cv cS wbr wn wi wa wo vw vs cv wral vw cv va cv vb cv cop cT
      wbr wn vw vs cv wral vs cv cA cB cxp wss vc cv va cv cR wbr wn vc vs cv
      cdm wral wa vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vw cv c1st
      cfv va cv cR wbr wn vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr
      wn wi wa vw vs cv wral vw cv cA cB cxp wcel va cv vb cv cop cA cB cxp
      wcel wa wn vw cv c1st cfv va cv cR wbr wn vw cv c1st cfv va cv wceq vw cv
      c2nd cfv vb cv cS wbr wn wi wa wo vw vs cv wral vs cv cA cB cxp wss vs cv
      wrel vc cv va cv cR wbr wn vc vs cv cdm wral vd cv vb cv cS wbr wn vd vs
      cv va cv csn cima wral vw cv c1st cfv va cv cR wbr wn vw cv c1st cfv va
      cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa vw vs cv wral wi vs cv cA cB
      cxp wss cA cB cxp wrel vs cv wrel cA cB relxp vs cv cA cB cxp relss mpi
      vs cv wrel vc cv va cv cR wbr wn vc vs cv cdm wral wa vd cv vb cv cS wbr
      wn vd vs cv va cv csn cima wral vw cv c1st cfv va cv cR wbr wn vw cv c1st
      cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa vw vs cv wral vs cv
      wrel vc cv va cv cR wbr wn vc vs cv cdm wral wa vd cv vb cv cS wbr wn vd
      vs cv va cv csn cima wral wa vw cv c1st cfv va cv cR wbr wn vw cv c1st
      cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa vw vs cv vs cv wrel
      vc cv va cv cR wbr wn vc vs cv cdm wral wa vd cv vb cv cS wbr wn vd vs cv
      va cv csn cima wral wa vw cv vs cv wcel vw cv c1st cfv va cv cR wbr wn vw
      cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi vs cv wrel vc cv
      va cv cR wbr wn vc vs cv cdm wral wa vw cv vs cv wcel vw cv c1st cfv va
      cv cR wbr wn wi vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vc cv
      va cv cR wbr wn vc vs cv cdm wral vs cv wrel vw cv vs cv wcel vw cv c1st
      cfv va cv cR wbr wn wi vc cv va cv cR wbr wn vc vs cv cdm wral vs cv wrel
      vw cv vs cv wcel vw cv c1st cfv va cv cR wbr wn vs cv wrel vw cv vs cv
      wcel wa vw cv c1st cfv vs cv cdm wcel vc cv va cv cR wbr wn vc vs cv cdm
      wral vw cv c1st cfv va cv cR wbr wn vw cv vs cv 1stdm vc cv va cv cR wbr
      wn vw cv c1st cfv va cv cR wbr wn vc vw cv c1st cfv vs cv cdm vc cv vw cv
      c1st cfv wceq vc cv va cv cR wbr vw cv c1st cfv va cv cR wbr vc cv vw cv
      c1st cfv va cv cR breq1 notbid rspccv syl5 exp3a impcom adantr vs cv wrel
      vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vw cv vs cv wcel vw cv
      c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wi vc cv va cv cR
      wbr wn vc vs cv cdm wral vs cv wrel vd cv vb cv cS wbr wn vd vs cv va cv
      csn cima wral wa vw cv vs cv wcel vw cv vt cv vu cv cop wceq vu wex vt
      wex vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi vs cv
      wrel vw cv vs cv wcel vw cv vt cv vu cv cop wceq vu wex vt wex wi vd cv
      vb cv cS wbr wn vd vs cv va cv csn cima wral vs cv wrel vw cv vs cv wcel
      vw cv vt cv vu cv cop wceq vu wex vt wex vt vu vw cv vs cv elrel ex
      adantr vw cv vt cv vu cv cop wceq vu wex vt wex vs cv wrel vd cv vb cv cS
      wbr wn vd vs cv va cv csn cima wral wa vw cv vs cv wcel vw cv c1st cfv va
      cv wceq vw cv c2nd cfv vb cv cS wbr wn wi vw cv vt cv vu cv cop wceq vs
      cv wrel vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral wa vw cv vs cv
      wcel vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wi wi vt
      vu vs cv wrel vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral wa vw cv
      vs cv wcel vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wi
      vw cv vt cv vu cv cop wceq vt cv vu cv cop vs cv wcel vt cv va cv wceq vu
      cv vb cv cS wbr wn wi wi vt cv va cv wceq vs cv wrel vd cv vb cv cS wbr
      wn vd vs cv va cv csn cima wral wa vt cv vu cv cop vs cv wcel vu cv vb cv
      cS wbr wn vs cv wrel vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral
      wa vt cv vu cv cop vs cv wcel vu cv vb cv cS wbr wn wi vt cv va cv wceq
      va cv vu cv cop vs cv wcel vu cv vb cv cS wbr wn wi vd cv vb cv cS wbr wn
      vd vs cv va cv csn cima wral va cv vu cv cop vs cv wcel vu cv vb cv cS
      wbr wn wi vs cv wrel va cv vu cv cop vs cv wcel vu cv vs cv va cv csn
      cima wcel vd cv vb cv cS wbr wn vd vs cv va cv csn cima wral vu cv vb cv
      cS wbr wn vs cv va cv vu cv va vex vu vex elimasn vd cv vb cv cS wbr wn
      vu cv vb cv cS wbr wn vd vu cv vs cv va cv csn cima vd cv vu cv wceq vd
      cv vb cv cS wbr vu cv vb cv cS wbr vd cv vu cv vb cv cS breq1 notbid
      rspccv syl5bir adantl vt cv va cv wceq vt cv vu cv cop vs cv wcel va cv
      vu cv cop vs cv wcel vu cv vb cv cS wbr wn vt cv va cv wceq vt cv vu cv
      cop va cv vu cv cop vs cv vt cv va cv vu cv opeq1 eleq1d imbi1d syl5ibr
      com3l vw cv vt cv vu cv cop wceq vw cv vs cv wcel vt cv vu cv cop vs cv
      wcel vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi vt cv va
      cv wceq vu cv vb cv cS wbr wn wi vw cv vt cv vu cv cop vs cv eleq1 vw cv
      vt cv vu cv cop wceq vw cv c1st cfv va cv wceq vt cv va cv wceq vw cv
      c2nd cfv vb cv cS wbr wn vu cv vb cv cS wbr wn vw cv vt cv vu cv cop wceq
      vw cv c1st cfv vt cv va cv vt cv vu cv vw cv vt vex vu vex op1std eqeq1d
      vw cv vt cv vu cv cop wceq vw cv c2nd cfv vb cv cS wbr vu cv vb cv cS wbr
      vw cv vt cv vu cv cop wceq vw cv c2nd cfv vu cv vb cv cS vt cv vu cv vw
      cv vt vex vu vex op2ndd breq1d notbid imbi12d imbi12d syl5ibr exlimivv
      com3l mpdd adantlr jcad ralrimiv ex sylan vw cv c1st cfv va cv cR wbr wn
      vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa vw cv cA
      cB cxp wcel va cv vb cv cop cA cB cxp wcel wa wn vw cv c1st cfv va cv cR
      wbr wn vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa wo
      vw vs cv vw cv c1st cfv va cv cR wbr wn vw cv c1st cfv va cv wceq vw cv
      c2nd cfv vb cv cS wbr wn wi wa vw cv cA cB cxp wcel va cv vb cv cop cA cB
      cxp wcel wa wn olc ralimi syl6 vw cv va cv vb cv cop cT wbr wn vw cv cA
      cB cxp wcel va cv vb cv cop cA cB cxp wcel wa wn vw cv c1st cfv va cv cR
      wbr wn vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa wo
      vw vs cv vw cv va cv vb cv cop cT wbr wn vw cv cA cB cxp wcel va cv vb cv
      cop cA cB cxp wcel wa wn vw cv c1st cfv va cv cR wbr vw cv c1st cfv va cv
      wceq vw cv c2nd cfv vb cv cS wbr wa wo wn wo vw cv cA cB cxp wcel va cv
      vb cv cop cA cB cxp wcel wa wn vw cv c1st cfv va cv cR wbr wn vw cv c1st
      cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi wa wo vw cv cA cB cxp
      wcel va cv vb cv cop cA cB cxp wcel wa vw cv c1st cfv va cv cR wbr vw cv
      c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wa wo wa vw cv cA cB cxp
      wcel va cv vb cv cop cA cB cxp wcel wa wn vw cv c1st cfv va cv cR wbr vw
      cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wa wo wn wo vw cv va
      cv vb cv cop cT wbr vw cv cA cB cxp wcel va cv vb cv cop cA cB cxp wcel
      wa vw cv c1st cfv va cv cR wbr vw cv c1st cfv va cv wceq vw cv c2nd cfv
      vb cv cS wbr wa wo ianor vx cv cA cB cxp wcel vy cv cA cB cxp wcel wa vx
      cv c1st cfv vy cv c1st cfv cR wbr vx cv c1st cfv vy cv c1st cfv wceq vx
      cv c2nd cfv vy cv c2nd cfv cS wbr wa wo wa vw cv cA cB cxp wcel vy cv cA
      cB cxp wcel wa vw cv c1st cfv vy cv c1st cfv cR wbr vw cv c1st cfv vy cv
      c1st cfv wceq vw cv c2nd cfv vy cv c2nd cfv cS wbr wa wo wa vw cv cA cB
      cxp wcel va cv vb cv cop cA cB cxp wcel wa vw cv c1st cfv va cv cR wbr vw
      cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wa wo wa vx vy vw cv
      va cv vb cv cop cT vw vex va cv vb cv opex vx cv vw cv wceq vx cv cA cB
      cxp wcel vy cv cA cB cxp wcel wa vw cv cA cB cxp wcel vy cv cA cB cxp
      wcel wa vx cv c1st cfv vy cv c1st cfv cR wbr vx cv c1st cfv vy cv c1st
      cfv wceq vx cv c2nd cfv vy cv c2nd cfv cS wbr wa wo vw cv c1st cfv vy cv
      c1st cfv cR wbr vw cv c1st cfv vy cv c1st cfv wceq vw cv c2nd cfv vy cv
      c2nd cfv cS wbr wa wo vx cv vw cv wceq vx cv cA cB cxp wcel vw cv cA cB
      cxp wcel vy cv cA cB cxp wcel vx cv vw cv cA cB cxp eleq1 anbi1d vx cv vw
      cv wceq vx cv c1st cfv vy cv c1st cfv cR wbr vw cv c1st cfv vy cv c1st
      cfv cR wbr vx cv c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv vy cv c2nd
      cfv cS wbr wa vw cv c1st cfv vy cv c1st cfv wceq vw cv c2nd cfv vy cv
      c2nd cfv cS wbr wa vx cv vw cv wceq vx cv c1st cfv vw cv c1st cfv vy cv
      c1st cfv cR vx cv vw cv c1st fveq2 breq1d vx cv vw cv wceq vx cv c1st cfv
      vy cv c1st cfv wceq vw cv c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv vy
      cv c2nd cfv cS wbr vw cv c2nd cfv vy cv c2nd cfv cS wbr vx cv vw cv wceq
      vx cv c1st cfv vw cv c1st cfv vy cv c1st cfv vx cv vw cv c1st fveq2
      eqeq1d vx cv vw cv wceq vx cv c2nd cfv vw cv c2nd cfv vy cv c2nd cfv cS
      vx cv vw cv c2nd fveq2 breq1d anbi12d orbi12d anbi12d vy cv va cv vb cv
      cop wceq vw cv cA cB cxp wcel vy cv cA cB cxp wcel wa vw cv cA cB cxp
      wcel va cv vb cv cop cA cB cxp wcel wa vw cv c1st cfv vy cv c1st cfv cR
      wbr vw cv c1st cfv vy cv c1st cfv wceq vw cv c2nd cfv vy cv c2nd cfv cS
      wbr wa wo vw cv c1st cfv va cv cR wbr vw cv c1st cfv va cv wceq vw cv
      c2nd cfv vb cv cS wbr wa wo vy cv va cv vb cv cop wceq vy cv cA cB cxp
      wcel va cv vb cv cop cA cB cxp wcel vw cv cA cB cxp wcel vy cv va cv vb
      cv cop cA cB cxp eleq1 anbi2d vy cv va cv vb cv cop wceq vw cv c1st cfv
      vy cv c1st cfv cR wbr vw cv c1st cfv va cv cR wbr vw cv c1st cfv vy cv
      c1st cfv wceq vw cv c2nd cfv vy cv c2nd cfv cS wbr wa vw cv c1st cfv va
      cv wceq vw cv c2nd cfv vb cv cS wbr wa vy cv va cv vb cv cop wceq vy cv
      c1st cfv va cv vw cv c1st cfv cR va cv vb cv vy cv va vex vb vex op1std
      breq2d vy cv va cv vb cv cop wceq vw cv c1st cfv vy cv c1st cfv wceq vw
      cv c1st cfv va cv wceq vw cv c2nd cfv vy cv c2nd cfv cS wbr vw cv c2nd
      cfv vb cv cS wbr vy cv va cv vb cv cop wceq vy cv c1st cfv va cv vw cv
      c1st cfv va cv vb cv vy cv va vex vb vex op1std eqeq2d vy cv va cv vb cv
      cop wceq vy cv c2nd cfv vb cv vw cv c2nd cfv cS va cv vb cv vy cv va vex
      vb vex op2ndd breq2d anbi12d orbi12d anbi12d frxp.1 brab xchnxbir vw cv
      c1st cfv va cv cR wbr vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS
      wbr wa wo wn vw cv c1st cfv va cv cR wbr wn vw cv c1st cfv va cv wceq vw
      cv c2nd cfv vb cv cS wbr wn wi wa vw cv cA cB cxp wcel va cv vb cv cop cA
      cB cxp wcel wa wn vw cv c1st cfv va cv cR wbr vw cv c1st cfv va cv wceq
      vw cv c2nd cfv vb cv cS wbr wa wo wn vw cv c1st cfv va cv cR wbr wn vw cv
      c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wa wn wa vw cv c1st cfv
      va cv cR wbr wn vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn
      wi wa vw cv c1st cfv va cv cR wbr vw cv c1st cfv va cv wceq vw cv c2nd
      cfv vb cv cS wbr wa ioran vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv
      cS wbr wa wn vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi
      vw cv c1st cfv va cv cR wbr wn vw cv c1st cfv va cv wceq vw cv c2nd cfv
      vb cv cS wbr wa wn vw cv c1st cfv va cv wceq wn vw cv c2nd cfv vb cv cS
      wbr wn wo vw cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr wn wi vw
      cv c1st cfv va cv wceq vw cv c2nd cfv vb cv cS wbr ianor vw cv c1st cfv
      va cv wceq vw cv c2nd cfv vb cv cS wbr pm4.62 bitr4i anbi2i bitri orbi2i
      bitri ralbii syl6ibr reximdv ex com23 adantr sylcom impl expimpd 3adant3
      vs cv va cv csn cres vs cv wss vw cv va cv vb cv cop cT wbr wn vw vs cv
      wral vb vs cv va cv csn cima wrex vw cv vz cv cT wbr wn vw vs cv wral vz
      vs cv va cv csn cres wrex vw cv vz cv cT wbr wn vw vs cv wral vz vs cv
      wrex vs cv va cv csn resss vw cv va cv vb cv cop cT wbr wn vw vs cv wral
      vb vs cv va cv csn cima wrex vz cv va cv vb cv cop wceq va cv vb cv cop
      vs cv wcel vw cv vz cv cT wbr wn vw vs cv wral wa wa vb wex vz wex vw cv
      vz cv cT wbr wn vw vs cv wral vz vs cv va cv csn cres wrex vw cv va cv vb
      cv cop cT wbr wn vw vs cv wral vb vs cv va cv csn cima wrex vz cv va cv
      vb cv cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw vs cv
      wral wa wa vz wex vb wex vz cv va cv vb cv cop wceq va cv vb cv cop vs cv
      wcel vw cv vz cv cT wbr wn vw vs cv wral wa wa vb wex vz wex vw cv va cv
      vb cv cop cT wbr wn vw vs cv wral vb vs cv va cv csn cima wrex vb cv vs
      cv va cv csn cima wcel vw cv va cv vb cv cop cT wbr wn vw vs cv wral wa
      vb wex vz cv va cv vb cv cop wceq va cv vb cv cop vs cv wcel vw cv vz cv
      cT wbr wn vw vs cv wral wa wa vz wex vb wex vw cv va cv vb cv cop cT wbr
      wn vw vs cv wral vb vs cv va cv csn cima df-rex vb cv vs cv va cv csn
      cima wcel vw cv va cv vb cv cop cT wbr wn vw vs cv wral wa vz cv va cv vb
      cv cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw vs cv
      wral wa wa vz wex vb vb cv vs cv va cv csn cima wcel va cv vb cv cop vs
      cv wcel vw cv va cv vb cv cop cT wbr wn vw vs cv wral vz cv va cv vb cv
      cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw vs cv wral
      wa wa vz wex vs cv va cv vb cv va vex vb vex elimasn va cv vb cv cop va
      cv vb cv cop wceq va cv vb cv cop vs cv wcel vw cv va cv vb cv cop cT wbr
      wn vw vs cv wral wa vz cv va cv vb cv cop wceq va cv vb cv cop vs cv wcel
      vw cv vz cv cT wbr wn vw vs cv wral wa wa vz wex va cv vb cv cop eqid vz
      cv va cv vb cv cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn
      vw vs cv wral wa wa va cv vb cv cop va cv vb cv cop wceq va cv vb cv cop
      vs cv wcel vw cv va cv vb cv cop cT wbr wn vw vs cv wral wa wa vz va cv
      vb cv cop va cv vb cv opex vz cv va cv vb cv cop wceq vz cv va cv vb cv
      cop wceq va cv vb cv cop va cv vb cv cop wceq va cv vb cv cop vs cv wcel
      vw cv vz cv cT wbr wn vw vs cv wral wa va cv vb cv cop vs cv wcel vw cv
      va cv vb cv cop cT wbr wn vw vs cv wral wa vz cv va cv vb cv cop va cv vb
      cv cop eqeq1 vz cv va cv vb cv cop wceq vw cv vz cv cT wbr wn vw vs cv
      wral vw cv va cv vb cv cop cT wbr wn vw vs cv wral va cv vb cv cop vs cv
      wcel vz cv va cv vb cv cop wceq vw cv vz cv cT wbr wn vw cv va cv vb cv
      cop cT wbr wn vw vs cv vz cv va cv vb cv cop wceq vw cv vz cv cT wbr vw
      cv va cv vb cv cop cT wbr vz cv va cv vb cv cop vw cv cT breq2 notbid
      ralbidv anbi2d anbi12d spcev mpan sylanb eximi sylbi vz cv va cv vb cv
      cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw vs cv wral
      wa wa vb vz excom sylib vw cv vz cv cT wbr wn vw vs cv wral vz vs cv va
      cv csn cres wrex vz cv vs cv va cv csn cres wcel vw cv vz cv cT wbr wn vw
      vs cv wral wa vz wex vz cv va cv vb cv cop wceq va cv vb cv cop vs cv
      wcel vw cv vz cv cT wbr wn vw vs cv wral wa wa vb wex vz wex vw cv vz cv
      cT wbr wn vw vs cv wral vz vs cv va cv csn cres df-rex vz cv vs cv va cv
      csn cres wcel vw cv vz cv cT wbr wn vw vs cv wral wa vz cv va cv vb cv
      cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw vs cv wral
      wa wa vb wex vz vz cv vs cv va cv csn cres wcel vw cv vz cv cT wbr wn vw
      vs cv wral wa vz cv va cv vb cv cop wceq va cv vb cv cop vs cv wcel wa vb
      wex vw cv vz cv cT wbr wn vw vs cv wral wa vz cv va cv vb cv cop wceq va
      cv vb cv cop vs cv wcel wa vw cv vz cv cT wbr wn vw vs cv wral wa vb wex
      vz cv va cv vb cv cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr
      wn vw vs cv wral wa wa vb wex vz cv vs cv va cv csn cres wcel vz cv va cv
      vb cv cop wceq va cv vb cv cop vs cv wcel wa vb wex vw cv vz cv cT wbr wn
      vw vs cv wral vb vz cv vs cv va cv va vex elsnres anbi1i vz cv va cv vb
      cv cop wceq va cv vb cv cop vs cv wcel wa vw cv vz cv cT wbr wn vw vs cv
      wral vb 19.41v vz cv va cv vb cv cop wceq va cv vb cv cop vs cv wcel wa
      vw cv vz cv cT wbr wn vw vs cv wral wa vz cv va cv vb cv cop wceq va cv
      vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw vs cv wral wa wa vb vz cv
      va cv vb cv cop wceq va cv vb cv cop vs cv wcel vw cv vz cv cT wbr wn vw
      vs cv wral anass exbii 3bitr2i exbii bitri sylibr vw cv vz cv cT wbr wn
      vw vs cv wral vz vs cv va cv csn cres vs cv ssrexv mpsyl syl6 exp3a
      rexlimdv 3expib adantl mpdd alrimiv vs vz vw cA cB cxp cT df-fr sylibr $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.  $d a x y $.
    $d b x y $.  $d c x y $.  $d d x y $.
    xporderlem.1 $e |- T = { <. x , y >. | ( ( x e. ( A X. B )
     /\ y e. ( A X. B ) )
     /\ ( ( 1st ` x ) R ( 1st ` y )
       \/ ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( Lemma for lexicographical ordering theorems.  (Contributed by Scott
       Fenton, 16-Mar-2011.) $)
    xporderlem $p |- ( <. a , b >. T <. c , d >. <->
                        ( ( ( a e. A /\ c e. A ) /\ ( b e. B /\ d e. B ) ) /\
                          ( a R c \/ ( a = c /\ b S d ) ) ) ) $=
      va cv vb cv cop vc cv vd cv cop cT wbr va cv vb cv cop vc cv vd cv cop
      cop vx cv cA cB cxp wcel vy cv cA cB cxp wcel wa vx cv c1st cfv vy cv
      c1st cfv cR wbr vx cv c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv vy cv
      c2nd cfv cS wbr wa wo wa vx vy copab wcel va cv cA wcel vb cv cB wcel wa
      vc cv cA wcel vd cv cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb
      cv vd cv cS wbr wa wo wa va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd
      cv cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr
      wa wo wa va cv vb cv cop vc cv vd cv cop cT wbr va cv vb cv cop vc cv vd
      cv cop cop cT wcel va cv vb cv cop vc cv vd cv cop cop vx cv cA cB cxp
      wcel vy cv cA cB cxp wcel wa vx cv c1st cfv vy cv c1st cfv cR wbr vx cv
      c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv vy cv c2nd cfv cS wbr wa wo
      wa vx vy copab wcel va cv vb cv cop vc cv vd cv cop cT df-br cT vx cv cA
      cB cxp wcel vy cv cA cB cxp wcel wa vx cv c1st cfv vy cv c1st cfv cR wbr
      vx cv c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv vy cv c2nd cfv cS wbr
      wa wo wa vx vy copab va cv vb cv cop vc cv vd cv cop cop xporderlem.1
      eleq2i bitri vx cv cA cB cxp wcel vy cv cA cB cxp wcel wa vx cv c1st cfv
      vy cv c1st cfv cR wbr vx cv c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv
      vy cv c2nd cfv cS wbr wa wo wa va cv cA wcel vb cv cB wcel wa vy cv cA cB
      cxp wcel wa va cv vy cv c1st cfv cR wbr va cv vy cv c1st cfv wceq vb cv
      vy cv c2nd cfv cS wbr wa wo wa va cv cA wcel vb cv cB wcel wa vc cv cA
      wcel vd cv cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv
      cS wbr wa wo wa vx vy va cv vb cv cop vc cv vd cv cop va cv vb cv opex vc
      cv vd cv opex vx cv va cv vb cv cop wceq vx cv cA cB cxp wcel vy cv cA cB
      cxp wcel wa va cv cA wcel vb cv cB wcel wa vy cv cA cB cxp wcel wa vx cv
      c1st cfv vy cv c1st cfv cR wbr vx cv c1st cfv vy cv c1st cfv wceq vx cv
      c2nd cfv vy cv c2nd cfv cS wbr wa wo va cv vy cv c1st cfv cR wbr va cv vy
      cv c1st cfv wceq vb cv vy cv c2nd cfv cS wbr wa wo vx cv va cv vb cv cop
      wceq vx cv cA cB cxp wcel va cv cA wcel vb cv cB wcel wa vy cv cA cB cxp
      wcel vx cv va cv vb cv cop wceq vx cv cA cB cxp wcel va cv vb cv cop cA
      cB cxp wcel va cv cA wcel vb cv cB wcel wa vx cv va cv vb cv cop cA cB
      cxp eleq1 va cv vb cv cA cB opelxp syl6bb anbi1d vx cv va cv vb cv cop
      wceq vx cv c1st cfv vy cv c1st cfv cR wbr va cv vy cv c1st cfv cR wbr vx
      cv c1st cfv vy cv c1st cfv wceq vx cv c2nd cfv vy cv c2nd cfv cS wbr wa
      va cv vy cv c1st cfv wceq vb cv vy cv c2nd cfv cS wbr wa vx cv va cv vb
      cv cop wceq vx cv c1st cfv va cv vy cv c1st cfv cR va cv vb cv vx cv va
      vex vb vex op1std breq1d vx cv va cv vb cv cop wceq vx cv c1st cfv vy cv
      c1st cfv wceq va cv vy cv c1st cfv wceq vx cv c2nd cfv vy cv c2nd cfv cS
      wbr vb cv vy cv c2nd cfv cS wbr vx cv va cv vb cv cop wceq vx cv c1st cfv
      va cv vy cv c1st cfv va cv vb cv vx cv va vex vb vex op1std eqeq1d vx cv
      va cv vb cv cop wceq vx cv c2nd cfv vb cv vy cv c2nd cfv cS va cv vb cv
      vx cv va vex vb vex op2ndd breq1d anbi12d orbi12d anbi12d vy cv vc cv vd
      cv cop wceq va cv cA wcel vb cv cB wcel wa vy cv cA cB cxp wcel wa va cv
      cA wcel vb cv cB wcel wa vc cv cA wcel vd cv cB wcel wa wa va cv vy cv
      c1st cfv cR wbr va cv vy cv c1st cfv wceq vb cv vy cv c2nd cfv cS wbr wa
      wo va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo vy cv vc
      cv vd cv cop wceq vy cv cA cB cxp wcel vc cv cA wcel vd cv cB wcel wa va
      cv cA wcel vb cv cB wcel wa vy cv vc cv vd cv cop wceq vy cv cA cB cxp
      wcel vc cv vd cv cop cA cB cxp wcel vc cv cA wcel vd cv cB wcel wa vy cv
      vc cv vd cv cop cA cB cxp eleq1 vc cv vd cv cA cB opelxp syl6bb anbi2d vy
      cv vc cv vd cv cop wceq va cv vy cv c1st cfv cR wbr va cv vc cv cR wbr va
      cv vy cv c1st cfv wceq vb cv vy cv c2nd cfv cS wbr wa va cv vc cv wceq vb
      cv vd cv cS wbr wa vy cv vc cv vd cv cop wceq vy cv c1st cfv vc cv va cv
      cR vc cv vd cv vy cv vc vex vd vex op1std breq2d vy cv vc cv vd cv cop
      wceq va cv vy cv c1st cfv wceq va cv vc cv wceq vb cv vy cv c2nd cfv cS
      wbr vb cv vd cv cS wbr vy cv vc cv vd cv cop wceq vy cv c1st cfv vc cv va
      cv vc cv vd cv vy cv vc vex vd vex op1std eqeq2d vy cv vc cv vd cv cop
      wceq vy cv c2nd cfv vd cv vb cv cS vc cv vd cv vy cv vc vex vd vex op2ndd
      breq2d anbi12d orbi12d anbi12d opelopab va cv cA wcel vb cv cB wcel wa vc
      cv cA wcel vd cv cB wcel wa wa va cv cA wcel vc cv cA wcel wa vb cv cB
      wcel vd cv cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv
      cS wbr wa wo va cv cA wcel vb cv cB wcel vc cv cA wcel vd cv cB wcel an4
      anbi1i 3bitri $.
  $}

  ${
    $d A a b c d e f t u v x y $.  $d B a b c d e f t u v x y $.
    $d R a b c d e f t u v x y $.  $d S a b c d e f t u v x y $.
    $d T a b c d e f t u v $.
    poxp.1 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
      /\ ( ( 1st ` x ) R ( 1st ` y ) \/
           ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two posets.  (Contributed by Scott Fenton,
       16-Mar-2011.)  (Revised by Mario Carneiro, 7-Mar-2013.) $)
    poxp $p |- ( ( R Po A /\ S Po B ) -> T Po ( A X. B ) ) $=
      cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv
      cv cT wbr wa vt cv vv cv cT wbr wi wa vv cA cB cxp wral vu cA cB cxp wral
      vt cA cB cxp wral cA cB cxp cT wpo cA cR wpo cB cS wpo wa vt cv vt cv cT
      wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa
      vv cA cB cxp wral vt vu cA cB cxp cA cB cxp cA cR wpo cB cS wpo wa vt cv
      cA cB cxp wcel vu cv cA cB cxp wcel wa wa vt cv vt cv cT wbr wn vt cv vu
      cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa vv cA cB cxp cA
      cR wpo cB cS wpo wa vt cv cA cB cxp wcel vu cv cA cB cxp wcel wa vv cv cA
      cB cxp wcel vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr
      wa vt cv vv cv cT wbr wi wa wi vt cv cA cB cxp wcel vu cv cA cB cxp wcel
      wa vv cv cA cB cxp wcel cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt
      cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa vt cv cA
      cB cxp wcel vu cv cA cB cxp wcel vv cv cA cB cxp wcel cA cR wpo cB cS wpo
      wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv
      vv cv cT wbr wi wa wi vt cv cA cB cxp wcel vt cv va cv vb cv cop wceq va
      cv cA wcel vb cv cB wcel wa wa vb wex va wex vu cv cA cB cxp wcel vu cv
      vc cv vd cv cop wceq vc cv cA wcel vd cv cB wcel wa wa vd wex vc wex vv
      cv cA cB cxp wcel vv cv ve cv vf cv cop wceq ve cv cA wcel vf cv cB wcel
      wa wa vf wex ve wex cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu
      cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi va vb vt cv
      cA cB elxp vc vd vu cv cA cB elxp ve vf vv cv cA cB elxp vt cv va cv vb
      cv cop wceq va cv cA wcel vb cv cB wcel wa wa vb wex va wex vu cv vc cv
      vd cv cop wceq vc cv cA wcel vd cv cB wcel wa wa vd wex vc wex vv cv ve
      cv vf cv cop wceq ve cv cA wcel vf cv cB wcel wa wa vf wex ve wex cA cR
      wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT
      wbr wa vt cv vv cv cT wbr wi wa wi vt cv va cv vb cv cop wceq va cv cA
      wcel vb cv cB wcel wa wa vu cv vc cv vd cv cop wceq vc cv cA wcel vd cv
      cB wcel wa wa vd wex vc wex vv cv ve cv vf cv cop wceq ve cv cA wcel vf
      cv cB wcel wa wa vf wex ve wex cA cR wpo cB cS wpo wa vt cv vt cv cT wbr
      wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi
      wi wi va vb vv cv ve cv vf cv cop wceq ve cv cA wcel vf cv cB wcel wa wa
      vf wex ve wex vt cv va cv vb cv cop wceq va cv cA wcel vb cv cB wcel wa
      wa vu cv vc cv vd cv cop wceq vc cv cA wcel vd cv cB wcel wa wa vd wex vc
      wex cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv
      vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi vv cv ve cv vf cv cop wceq ve
      cv cA wcel vf cv cB wcel wa wa vt cv va cv vb cv cop wceq va cv cA wcel
      vb cv cB wcel wa wa vu cv vc cv vd cv cop wceq vc cv cA wcel vd cv cB
      wcel wa wa vd wex vc wex cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt
      cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi wi wi
      ve vf vu cv vc cv vd cv cop wceq vc cv cA wcel vd cv cB wcel wa wa vd wex
      vc wex vv cv ve cv vf cv cop wceq ve cv cA wcel vf cv cB wcel wa wa vt cv
      va cv vb cv cop wceq va cv cA wcel vb cv cB wcel wa wa cA cR wpo cB cS
      wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt
      cv vv cv cT wbr wi wa wi vu cv vc cv vd cv cop wceq vc cv cA wcel vd cv
      cB wcel wa wa vv cv ve cv vf cv cop wceq ve cv cA wcel vf cv cB wcel wa
      wa vt cv va cv vb cv cop wceq va cv cA wcel vb cv cB wcel wa wa cA cR wpo
      cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr
      wa vt cv vv cv cT wbr wi wa wi wi wi vc vd vt cv va cv vb cv cop wceq va
      cv cA wcel vb cv cB wcel wa wa vu cv vc cv vd cv cop wceq vc cv cA wcel
      vd cv cB wcel wa wa vv cv ve cv vf cv cop wceq ve cv cA wcel vf cv cB
      wcel wa wa cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT
      wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi vt cv va cv vb cv
      cop wceq va cv cA wcel vb cv cB wcel wa wa vu cv vc cv vd cv cop wceq vc
      cv cA wcel vd cv cB wcel wa wa vv cv ve cv vf cv cop wceq ve cv cA wcel
      vf cv cB wcel wa wa cA cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu
      cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi vt cv va cv
      vb cv cop wceq va cv cA wcel vb cv cB wcel wa wa vu cv vc cv vd cv cop
      wceq vc cv cA wcel vd cv cB wcel wa wa vv cv ve cv vf cv cop wceq ve cv
      cA wcel vf cv cB wcel wa wa w3a vt cv va cv vb cv cop wceq vu cv vc cv vd
      cv cop wceq vv cv ve cv vf cv cop wceq w3a va cv cA wcel vb cv cB wcel wa
      vc cv cA wcel vd cv cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a wa cA
      cR wpo cB cS wpo wa vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv
      cT wbr wa vt cv vv cv cT wbr wi wa wi vt cv va cv vb cv cop wceq va cv cA
      wcel vb cv cB wcel wa vu cv vc cv vd cv cop wceq vc cv cA wcel vd cv cB
      wcel wa vv cv ve cv vf cv cop wceq ve cv cA wcel vf cv cB wcel wa 3an6 vt
      cv va cv vb cv cop wceq vu cv vc cv vd cv cop wceq vv cv ve cv vf cv cop
      wceq w3a va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd cv cB wcel wa ve
      cv cA wcel vf cv cB wcel wa w3a cA cR wpo cB cS wpo wa vt cv vt cv cT wbr
      wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa wi
      vt cv va cv vb cv cop wceq vu cv vc cv vd cv cop wceq vv cv ve cv vf cv
      cop wceq w3a cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB wcel wa vc cv
      cA wcel vd cv cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a vt cv vt cv
      cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi
      wa cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd
      cv cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a wa vt cv vt cv cT wbr wn
      vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv cv cT wbr wi wa vt cv
      va cv vb cv cop wceq vu cv vc cv vd cv cop wceq vv cv ve cv vf cv cop
      wceq w3a va cv cA wcel va cv cA wcel wa vb cv cB wcel vb cv cB wcel wa wa
      va cv va cv cR wbr va va weq vb cv vb cv cS wbr wa wo wa wn va cv cA wcel
      vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va
      vc weq vb cv vd cv cS wbr wa wo wa vc cv cA wcel ve cv cA wcel wa vd cv
      cB wcel vf cv cB wcel wa wa vc cv ve cv cR wbr vc ve weq vd cv vf cv cS
      wbr wa wo wa wa va cv cA wcel ve cv cA wcel wa vb cv cB wcel vf cv cB
      wcel wa wa va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wa wi wa
      cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd cv
      cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a wa va cv cA wcel va cv cA
      wcel wa vb cv cB wcel vb cv cB wcel wa wa va cv va cv cR wbr va va weq vb
      cv vb cv cS wbr wa wo wa wn va cv cA wcel vc cv cA wcel wa vb cv cB wcel
      vd cv cB wcel wa wa va cv vc cv cR wbr va vc weq vb cv vd cv cS wbr wa wo
      wa vc cv cA wcel ve cv cA wcel wa vd cv cB wcel vf cv cB wcel wa wa vc cv
      ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo wa wa va cv cA wcel ve cv
      cA wcel wa vb cv cB wcel vf cv cB wcel wa wa va cv ve cv cR wbr va ve weq
      vb cv vf cv cS wbr wa wo wa wi cA cR wpo cB cS wpo wa vc cv cA wcel vd cv
      cB wcel wa va cv cA wcel vb cv cB wcel wa va cv cA wcel va cv cA wcel wa
      vb cv cB wcel vb cv cB wcel wa wa va cv va cv cR wbr va va weq vb cv vb
      cv cS wbr wa wo wa wn ve cv cA wcel vf cv cB wcel wa cA cR wpo cB cS wpo
      wa va cv cA wcel vb cv cB wcel wa wa va cv va cv cR wbr va va weq vb cv
      vb cv cS wbr wa wo va cv cA wcel va cv cA wcel wa vb cv cB wcel vb cv cB
      wcel wa wa cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB wcel wa va cv va
      cv cR wbr va va weq vb cv vb cv cS wbr wa wo wn cA cR wpo cB cS wpo wa va
      cv cA wcel vb cv cB wcel wa va cv va cv cR wbr wn va va weq vb cv vb cv
      cS wbr wa wn wa va cv va cv cR wbr va va weq vb cv vb cv cS wbr wa wo wn
      cA cR wpo va cv cA wcel va cv va cv cR wbr wn cB cS wpo vb cv cB wcel va
      va weq vb cv vb cv cS wbr wa wn cA cR wpo va cv cA wcel va cv va cv cR
      wbr wn cA va cv cR poirr ex cB cS wpo vb cv cB wcel va va weq vb cv vb cv
      cS wbr wa wn cB cS wpo vb cv cB wcel wa vb cv vb cv cS wbr va va weq cB
      vb cv cS poirr intnand ex im2anan9 va cv va cv cR wbr va va weq vb cv vb
      cv cS wbr wa ioran syl6ibr imp intnand 3ad2antr1 va cv cA wcel vc cv cA
      wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va vc weq vb
      cv vd cv cS wbr wa wo wa vc cv cA wcel ve cv cA wcel wa vd cv cB wcel vf
      cv cB wcel wa wa vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo wa
      wa va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa vc cv
      cA wcel ve cv cA wcel wa vd cv cB wcel vf cv cB wcel wa wa wa va cv vc cv
      cR wbr va vc weq vb cv vd cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq vd
      cv vf cv cS wbr wa wo wa wa cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB
      wcel wa vc cv cA wcel vd cv cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a
      wa va cv cA wcel ve cv cA wcel wa vb cv cB wcel vf cv cB wcel wa wa va cv
      ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wa va cv cA wcel vc cv cA
      wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va vc weq vb
      cv vd cv cS wbr wa wo vc cv cA wcel ve cv cA wcel wa vd cv cB wcel vf cv
      cB wcel wa wa vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo an4
      cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd cv
      cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a wa va cv vc cv cR wbr va vc
      weq vb cv vd cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq vd cv vf cv cS
      wbr wa wo wa va cv cA wcel ve cv cA wcel wa vb cv cB wcel vf cv cB wcel
      wa wa va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wa va cv cA
      wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa vc cv cA wcel ve
      cv cA wcel wa vd cv cB wcel vf cv cB wcel wa wa wa cA cR wpo cB cS wpo wa
      va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd cv cB wcel wa ve cv cA
      wcel vf cv cB wcel wa w3a wa va cv vc cv cR wbr va vc weq vb cv vd cv cS
      wbr wa wo vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo wa va cv
      ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo va cv cA wcel ve cv cA
      wcel wa vb cv cB wcel vf cv cB wcel wa wa va cv cA wcel vb cv cB wcel wa
      vc cv cA wcel vd cv cB wcel wa ve cv cA wcel vf cv cB wcel wa w3a cA cR
      wpo cB cS wpo wa va cv cA wcel vc cv cA wcel ve cv cA wcel w3a vb cv cB
      wcel vd cv cB wcel vf cv cB wcel w3a wa va cv vc cv cR wbr va vc weq vb
      cv vd cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa
      wo wa va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wi va cv cA
      wcel vb cv cB wcel vc cv cA wcel vd cv cB wcel ve cv cA wcel vf cv cB
      wcel 3an6 cA cR wpo va cv cA wcel vc cv cA wcel ve cv cA wcel w3a cB cS
      wpo vb cv cB wcel vd cv cB wcel vf cv cB wcel w3a va cv vc cv cR wbr va
      vc weq vb cv vd cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq vd cv vf cv
      cS wbr wa wo wa va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wi
      cA cR wpo va cv cA wcel vc cv cA wcel ve cv cA wcel w3a wa cB cS wpo vb
      cv cB wcel vd cv cB wcel vf cv cB wcel w3a wa wa va cv vc cv cR wbr va vc
      weq vb cv vd cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq vd cv vf cv cS
      wbr wa wo va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo cA cR wpo
      va cv cA wcel vc cv cA wcel ve cv cA wcel w3a wa va cv vc cv cR wbr vc cv
      ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo va cv ve cv cR wbr va ve
      weq vb cv vf cv cS wbr wa wo wi cB cS wpo vb cv cB wcel vd cv cB wcel vf
      cv cB wcel w3a wa va vc weq vb cv vd cv cS wbr wa cA cR wpo va cv cA wcel
      vc cv cA wcel ve cv cA wcel w3a wa va cv vc cv cR wbr vc cv ve cv cR wbr
      vc ve weq vd cv vf cv cS wbr wa wo va cv ve cv cR wbr va ve weq vb cv vf
      cv cS wbr wa wo wi cA cR wpo va cv cA wcel vc cv cA wcel ve cv cA wcel
      w3a wa va cv vc cv cR wbr wa vc cv ve cv cR wbr va cv ve cv cR wbr va ve
      weq vb cv vf cv cS wbr wa wo vc ve weq vd cv vf cv cS wbr wa cA cR wpo va
      cv cA wcel vc cv cA wcel ve cv cA wcel w3a wa va cv vc cv cR wbr vc cv ve
      cv cR wbr va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo cA cR wpo
      va cv cA wcel vc cv cA wcel ve cv cA wcel w3a va cv vc cv cR wbr vc cv ve
      cv cR wbr wa va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo cA cR
      wpo va cv cA wcel vc cv cA wcel ve cv cA wcel w3a va cv vc cv cR wbr vc
      cv ve cv cR wbr wa w3a va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa
      cA cR wpo va cv cA wcel vc cv cA wcel ve cv cA wcel w3a va cv vc cv cR
      wbr vc cv ve cv cR wbr wa va cv ve cv cR wbr cA va cv vc cv ve cv cR potr
      3impia orcd 3expia expdimp va cv vc cv cR wbr vc ve weq vd cv vf cv cS
      wbr wa va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wi cA cR wpo
      va cv cA wcel vc cv cA wcel ve cv cA wcel w3a wa va cv vc cv cR wbr vc ve
      weq va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo vd cv vf cv cS
      wbr vc ve weq va cv vc cv cR wbr va cv ve cv cR wbr va ve weq vb cv vf cv
      cS wbr wa wo vc ve weq va cv vc cv cR wbr wa va cv ve cv cR wbr va ve weq
      vb cv vf cv cS wbr wa vc ve weq va cv vc cv cR wbr va cv ve cv cR wbr vc
      cv ve cv va cv cR breq2 biimpa orcd expcom adantrd adantl jaod ex cB cS
      wpo vb cv cB wcel vd cv cB wcel vf cv cB wcel w3a wa va vc weq vb cv vd
      cv cS wbr vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo va cv ve
      cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wi va vc weq cB cS wpo vb cv
      cB wcel vd cv cB wcel vf cv cB wcel w3a wa vb cv vd cv cS wbr vc cv ve cv
      cR wbr vc ve weq vd cv vf cv cS wbr wa wo va cv ve cv cR wbr va ve weq vb
      cv vf cv cS wbr wa wo wi wi va vc weq cB cS wpo vb cv cB wcel vd cv cB
      wcel vf cv cB wcel w3a wa vb cv vd cv cS wbr vc cv ve cv cR wbr vc ve weq
      vd cv vf cv cS wbr wa wo va cv ve cv cR wbr va ve weq vb cv vf cv cS wbr
      wa wo wi cB cS wpo vb cv cB wcel vd cv cB wcel vf cv cB wcel w3a wa vb cv
      vd cv cS wbr wa vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo va
      cv ve cv cR wbr va ve weq vb cv vf cv cS wbr wa wo wi va vc weq vc cv ve
      cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq
      vb cv vf cv cS wbr wa wo wi cB cS wpo vb cv cB wcel vd cv cB wcel vf cv
      cB wcel w3a wa vb cv vd cv cS wbr wa vc ve weq vd cv vf cv cS wbr wa vc
      ve weq vb cv vf cv cS wbr wa vc cv ve cv cR wbr cB cS wpo vb cv cB wcel
      vd cv cB wcel vf cv cB wcel w3a wa vb cv vd cv cS wbr wa vd cv vf cv cS
      wbr vb cv vf cv cS wbr vc ve weq cB cS wpo vb cv cB wcel vd cv cB wcel vf
      cv cB wcel w3a wa vb cv vd cv cS wbr vd cv vf cv cS wbr vb cv vf cv cS
      wbr cB vb cv vd cv vf cv cS potr expdimp anim2d orim2d va vc weq va cv ve
      cv cR wbr va ve weq vb cv vf cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq
      vb cv vf cv cS wbr wa wo vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr
      wa wo va vc weq va cv ve cv cR wbr vc cv ve cv cR wbr va ve weq vb cv vf
      cv cS wbr wa vc ve weq vb cv vf cv cS wbr wa va cv vc cv ve cv cR breq1
      va vc weq va ve weq vc ve weq vb cv vf cv cS wbr va vc ve equequ1 anbi1d
      orbi12d imbi2d syl5ibr exp3a com12 imp3a jaao imp3a an4s sylan2b va cv cA
      wcel vb cv cB wcel wa vc cv cA wcel vd cv cB wcel wa ve cv cA wcel vf cv
      cB wcel wa w3a va cv cA wcel ve cv cA wcel wa vb cv cB wcel vf cv cB wcel
      wa wa cA cR wpo cB cS wpo wa va cv cA wcel vb cv cB wcel wa ve cv cA wcel
      vf cv cB wcel wa va cv cA wcel ve cv cA wcel wa vb cv cB wcel vf cv cB
      wcel wa wa vc cv cA wcel vd cv cB wcel wa va cv cA wcel vb cv cB wcel wa
      ve cv cA wcel vf cv cB wcel wa wa va cv cA wcel ve cv cA wcel wa vb cv cB
      wcel vf cv cB wcel wa wa va cv cA wcel vb cv cB wcel ve cv cA wcel vf cv
      cB wcel an4 biimpi 3adant2 adantl jctild adantld syl5bi jca vt cv va cv
      vb cv cop wceq vu cv vc cv vd cv cop wceq vv cv ve cv vf cv cop wceq w3a
      vt cv vt cv cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt cv vv
      cv cT wbr wi wa va cv vb cv cop va cv vb cv cop cT wbr wn va cv vb cv cop
      vc cv vd cv cop cT wbr vc cv vd cv cop ve cv vf cv cop cT wbr wa va cv vb
      cv cop ve cv vf cv cop cT wbr wi wa va cv cA wcel va cv cA wcel wa vb cv
      cB wcel vb cv cB wcel wa wa va cv va cv cR wbr va va weq vb cv vb cv cS
      wbr wa wo wa wn va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv cB
      wcel wa wa va cv vc cv cR wbr va vc weq vb cv vd cv cS wbr wa wo wa vc cv
      cA wcel ve cv cA wcel wa vd cv cB wcel vf cv cB wcel wa wa vc cv ve cv cR
      wbr vc ve weq vd cv vf cv cS wbr wa wo wa wa va cv cA wcel ve cv cA wcel
      wa vb cv cB wcel vf cv cB wcel wa wa va cv ve cv cR wbr va ve weq vb cv
      vf cv cS wbr wa wo wa wi wa vt cv va cv vb cv cop wceq vu cv vc cv vd cv
      cop wceq vv cv ve cv vf cv cop wceq w3a vt cv vt cv cT wbr wn va cv vb cv
      cop va cv vb cv cop cT wbr wn vt cv vu cv cT wbr vu cv vv cv cT wbr wa vt
      cv vv cv cT wbr wi va cv vb cv cop vc cv vd cv cop cT wbr vc cv vd cv cop
      ve cv vf cv cop cT wbr wa va cv vb cv cop ve cv vf cv cop cT wbr wi vt cv
      va cv vb cv cop wceq vu cv vc cv vd cv cop wceq vt cv vt cv cT wbr wn va
      cv vb cv cop va cv vb cv cop cT wbr wn wb vv cv ve cv vf cv cop wceq vt
      cv va cv vb cv cop wceq vt cv vt cv cT wbr va cv vb cv cop va cv vb cv
      cop cT wbr vt cv va cv vb cv cop wceq vt cv vt cv cT wbr va cv vb cv cop
      va cv vb cv cop cT wbr wb vt cv va cv vb cv cop vt cv va cv vb cv cop cT
      breq12 anidms notbid 3ad2ant1 vt cv va cv vb cv cop wceq vu cv vc cv vd
      cv cop wceq vv cv ve cv vf cv cop wceq w3a vt cv vu cv cT wbr vu cv vv cv
      cT wbr wa va cv vb cv cop vc cv vd cv cop cT wbr vc cv vd cv cop ve cv vf
      cv cop cT wbr wa vt cv vv cv cT wbr va cv vb cv cop ve cv vf cv cop cT
      wbr vt cv va cv vb cv cop wceq vu cv vc cv vd cv cop wceq vv cv ve cv vf
      cv cop wceq w3a vt cv vu cv cT wbr va cv vb cv cop vc cv vd cv cop cT wbr
      vu cv vv cv cT wbr vc cv vd cv cop ve cv vf cv cop cT wbr vt cv va cv vb
      cv cop wceq vu cv vc cv vd cv cop wceq vt cv vu cv cT wbr va cv vb cv cop
      vc cv vd cv cop cT wbr wb vv cv ve cv vf cv cop wceq vt cv va cv vb cv
      cop vu cv vc cv vd cv cop cT breq12 3adant3 vu cv vc cv vd cv cop wceq vv
      cv ve cv vf cv cop wceq vu cv vv cv cT wbr vc cv vd cv cop ve cv vf cv
      cop cT wbr wb vt cv va cv vb cv cop wceq vu cv vc cv vd cv cop vv cv ve
      cv vf cv cop cT breq12 3adant1 anbi12d vt cv va cv vb cv cop wceq vv cv
      ve cv vf cv cop wceq vt cv vv cv cT wbr va cv vb cv cop ve cv vf cv cop
      cT wbr wb vu cv vc cv vd cv cop wceq vt cv va cv vb cv cop vv cv ve cv vf
      cv cop cT breq12 3adant2 imbi12d anbi12d va cv vb cv cop va cv vb cv cop
      cT wbr wn va cv cA wcel va cv cA wcel wa vb cv cB wcel vb cv cB wcel wa
      wa va cv va cv cR wbr va va weq vb cv vb cv cS wbr wa wo wa wn va cv vb
      cv cop vc cv vd cv cop cT wbr vc cv vd cv cop ve cv vf cv cop cT wbr wa
      va cv vb cv cop ve cv vf cv cop cT wbr wi va cv cA wcel vc cv cA wcel wa
      vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va vc weq vb cv vd
      cv cS wbr wa wo wa vc cv cA wcel ve cv cA wcel wa vd cv cB wcel vf cv cB
      wcel wa wa vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo wa wa va
      cv cA wcel ve cv cA wcel wa vb cv cB wcel vf cv cB wcel wa wa va cv ve cv
      cR wbr va ve weq vb cv vf cv cS wbr wa wo wa wi va cv vb cv cop va cv vb
      cv cop cT wbr va cv cA wcel va cv cA wcel wa vb cv cB wcel vb cv cB wcel
      wa wa va cv va cv cR wbr va va weq vb cv vb cv cS wbr wa wo wa vx vy cA
      cB cR cS cT va vb va vb poxp.1 xporderlem notbii va cv vb cv cop vc cv vd
      cv cop cT wbr vc cv vd cv cop ve cv vf cv cop cT wbr wa va cv cA wcel vc
      cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va vc
      weq vb cv vd cv cS wbr wa wo wa vc cv cA wcel ve cv cA wcel wa vd cv cB
      wcel vf cv cB wcel wa wa vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr
      wa wo wa wa va cv vb cv cop ve cv vf cv cop cT wbr va cv cA wcel ve cv cA
      wcel wa vb cv cB wcel vf cv cB wcel wa wa va cv ve cv cR wbr va ve weq vb
      cv vf cv cS wbr wa wo wa va cv vb cv cop vc cv vd cv cop cT wbr va cv cA
      wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR
      wbr va vc weq vb cv vd cv cS wbr wa wo wa vc cv vd cv cop ve cv vf cv cop
      cT wbr vc cv cA wcel ve cv cA wcel wa vd cv cB wcel vf cv cB wcel wa wa
      vc cv ve cv cR wbr vc ve weq vd cv vf cv cS wbr wa wo wa vx vy cA cB cR
      cS cT va vb vc vd poxp.1 xporderlem vx vy cA cB cR cS cT vc vd ve vf
      poxp.1 xporderlem anbi12i vx vy cA cB cR cS cT va vb ve vf poxp.1
      xporderlem imbi12i anbi12i syl6bb syl5ibr exp3acom23 imp sylbi 3exp com3l
      exlimivv com3l exlimivv com3l exlimivv 3imp syl3anb 3expia com3r imp
      ralrimiv ralrimivva vt vu vv cA cB cxp cT df-po sylibr $.
  $}

  ${
    $d A a b c d t u x y $.  $d B a b c d t u x y $.  $d R a b c d t u x y $.
    $d S a b c d t u x y $.  $d T a b c d t u $.
    soxp.1 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
      /\ ( ( 1st ` x ) R ( 1st ` y ) \/
           ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two strictly ordered classes.
       (Contributed by Scott Fenton, 17-Mar-2011.)  (Revised by Mario Carneiro,
       7-Mar-2013.) $)
    soxp $p |- ( ( R Or A /\ S Or B ) -> T Or ( A X. B ) ) $=
      cA cR wor cB cS wor wa cA cB cxp cT wpo vt cv vu cv cT wbr vt cv vu cv
      wceq vu cv vt cv cT wbr w3o vu cA cB cxp wral vt cA cB cxp wral cA cB cxp
      cT wor cA cR wor cA cR wpo cB cS wpo cA cB cxp cT wpo cB cS wor cA cR
      sopo cB cS sopo vx vy cA cB cR cS cT soxp.1 poxp syl2an cA cR wor cB cS
      wor wa vt cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o vt vu
      cA cB cxp cA cB cxp vt cv cA cB cxp wcel vu cv cA cB cxp wcel wa cA cR
      wor cB cS wor wa vt cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr
      w3o vt cv cA cB cxp wcel vt cv va cv vb cv cop wceq va cv cA wcel vb cv
      cB wcel wa wa vb wex va wex vu cv vc cv vd cv cop wceq vc cv cA wcel vd
      cv cB wcel wa wa vd wex vc wex cA cR wor cB cS wor wa vt cv vu cv cT wbr
      vt cv vu cv wceq vu cv vt cv cT wbr w3o wi vu cv cA cB cxp wcel va vb vt
      cv cA cB elxp vc vd vu cv cA cB elxp vt cv va cv vb cv cop wceq va cv cA
      wcel vb cv cB wcel wa wa vb wex va wex vu cv vc cv vd cv cop wceq vc cv
      cA wcel vd cv cB wcel wa wa vd wex vc wex cA cR wor cB cS wor wa vt cv vu
      cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o wi vt cv va cv vb cv
      cop wceq va cv cA wcel vb cv cB wcel wa wa vu cv vc cv vd cv cop wceq vc
      cv cA wcel vd cv cB wcel wa wa vd wex vc wex cA cR wor cB cS wor wa vt cv
      vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o wi wi va vb vu cv vc
      cv vd cv cop wceq vc cv cA wcel vd cv cB wcel wa wa vd wex vc wex vt cv
      va cv vb cv cop wceq va cv cA wcel vb cv cB wcel wa wa cA cR wor cB cS
      wor wa vt cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o wi vu
      cv vc cv vd cv cop wceq vc cv cA wcel vd cv cB wcel wa wa vt cv va cv vb
      cv cop wceq va cv cA wcel vb cv cB wcel wa wa cA cR wor cB cS wor wa vt
      cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o wi wi vc vd vt cv
      va cv vb cv cop wceq va cv cA wcel vb cv cB wcel wa wa vu cv vc cv vd cv
      cop wceq vc cv cA wcel vd cv cB wcel wa wa cA cR wor cB cS wor wa vt cv
      vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o wi vt cv va cv vb cv
      cop wceq vu cv vc cv vd cv cop wceq va cv cA wcel vb cv cB wcel wa vc cv
      cA wcel vd cv cB wcel wa cA cR wor cB cS wor wa vt cv vu cv cT wbr vt cv
      vu cv wceq vu cv vt cv cT wbr w3o wi vt cv va cv vb cv cop wceq vu cv vc
      cv vd cv cop wceq wa va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd cv
      cB wcel wa wa cA cR wor cB cS wor wa vt cv vu cv cT wbr vt cv vu cv wceq
      vu cv vt cv cT wbr w3o wi va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd
      cv cB wcel wa wa cA cR wor cB cS wor wa vt cv va cv vb cv cop wceq vu cv
      vc cv vd cv cop wceq wa vt cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv
      cT wbr w3o va cv cA wcel vb cv cB wcel wa vc cv cA wcel vd cv cB wcel wa
      wa cA cR wor cB cS wor wa va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd
      cv cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr
      wa wo wa va cv vc cv wceq vb cv vd cv wceq wa vc cv cA wcel va cv cA wcel
      wa vd cv cB wcel vb cv cB wcel wa wa vc cv va cv cR wbr vc cv va cv wceq
      vd cv vb cv cS wbr wa wo wa w3o vt cv va cv vb cv cop wceq vu cv vc cv vd
      cv cop wceq wa vt cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o
      wi va cv cA wcel vc cv cA wcel vb cv cB wcel vd cv cB wcel cA cR wor cB
      cS wor wa va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa
      wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo wa va cv
      vc cv wceq vb cv vd cv wceq wa vc cv cA wcel va cv cA wcel wa vd cv cB
      wcel vb cv cB wcel wa wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv
      cS wbr wa wo wa w3o wi cA cR wor cB cS wor wa va cv cA wcel vc cv cA wcel
      wa vb cv cB wcel vd cv cB wcel wa wa va cv cA wcel vc cv cA wcel wa vb cv
      cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd
      cv cS wbr wa wo wa va cv vc cv wceq vb cv vd cv wceq wa vc cv cA wcel va
      cv cA wcel wa vd cv cB wcel vb cv cB wcel wa wa vc cv va cv cR wbr vc cv
      va cv wceq vd cv vb cv cS wbr wa wo wa w3o cA cR wor va cv cA wcel vc cv
      cA wcel wa cB cS wor vb cv cB wcel vd cv cB wcel wa va cv cA wcel vc cv
      cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va cv vc
      cv wceq vb cv vd cv cS wbr wa wo wa va cv vc cv wceq vb cv vd cv wceq wa
      vc cv cA wcel va cv cA wcel wa vd cv cB wcel vb cv cB wcel wa wa vc cv va
      cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wa w3o cA cR wor va
      cv cA wcel vc cv cA wcel wa wa cB cS wor vb cv cB wcel vd cv cB wcel wa
      wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo va cv
      vc cv wceq vb cv vd cv wceq wa vc cv va cv cR wbr vc cv va cv wceq vd cv
      vb cv cS wbr wa wo w3o va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv
      cB wcel wa wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa
      wo wa va cv vc cv wceq vb cv vd cv wceq wa vc cv cA wcel va cv cA wcel wa
      vd cv cB wcel vb cv cB wcel wa wa vc cv va cv cR wbr vc cv va cv wceq vd
      cv vb cv cS wbr wa wo wa w3o cA cR wor va cv cA wcel vc cv cA wcel wa wa
      cB cS wor vb cv cB wcel vd cv cB wcel wa wa wa va cv vc cv cR wbr va cv
      vc cv wceq vb cv vd cv cS wbr wa wo va cv vc cv wceq vb cv vd cv wceq wa
      wo wn vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wi va
      cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo va cv vc cv
      wceq vb cv vd cv wceq wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv
      cS wbr wa wo w3o va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr
      wa wo va cv vc cv wceq vb cv vd cv wceq wa wo wn va cv vc cv cR wbr wn va
      cv vc cv wceq wn vb cv vd cv cS wbr wn wo wa va cv vc cv wceq wn vb cv vd
      cv wceq wn wo wa cA cR wor va cv cA wcel vc cv cA wcel wa wa cB cS wor vb
      cv cB wcel vd cv cB wcel wa wa wa vc cv va cv cR wbr vc cv va cv wceq vd
      cv vb cv cS wbr wa wo va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS
      wbr wa wo va cv vc cv wceq vb cv vd cv wceq wa wo wn va cv vc cv cR wbr
      va cv vc cv wceq vb cv vd cv cS wbr wa wo wn va cv vc cv wceq vb cv vd cv
      wceq wa wn wa va cv vc cv cR wbr wn va cv vc cv wceq wn vb cv vd cv cS
      wbr wn wo wa va cv vc cv wceq wn vb cv vd cv wceq wn wo wa va cv vc cv cR
      wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo va cv vc cv wceq vb cv vd
      cv wceq wa ioran va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr
      wa wo wn va cv vc cv cR wbr wn va cv vc cv wceq wn vb cv vd cv cS wbr wn
      wo wa va cv vc cv wceq vb cv vd cv wceq wa wn va cv vc cv wceq wn vb cv
      vd cv wceq wn wo va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr
      wa wo wn va cv vc cv cR wbr wn va cv vc cv wceq vb cv vd cv cS wbr wa wn
      wa va cv vc cv cR wbr wn va cv vc cv wceq wn vb cv vd cv cS wbr wn wo wa
      va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa ioran va cv vc
      cv wceq vb cv vd cv cS wbr wa wn va cv vc cv wceq wn vb cv vd cv cS wbr
      wn wo va cv vc cv cR wbr wn va cv vc cv wceq vb cv vd cv cS wbr ianor
      anbi2i bitri va cv vc cv wceq vb cv vd cv wceq ianor anbi12i bitri cA cR
      wor va cv cA wcel vc cv cA wcel wa wa cB cS wor vb cv cB wcel vd cv cB
      wcel wa wa wa va cv vc cv cR wbr wn va cv vc cv wceq wn vb cv vd cv cS
      wbr wn wo wa va cv vc cv wceq wn vb cv vd cv wceq wn wo vc cv va cv cR
      wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo cA cR wor va cv cA wcel vc
      cv cA wcel wa wa cB cS wor vb cv cB wcel vd cv cB wcel wa wa wa va cv vc
      cv cR wbr wn va cv vc cv wceq wn vb cv vd cv cS wbr wn wo wa va cv vc cv
      wceq vc cv va cv cR wbr wo va cv vc cv wceq wn vb cv vd cv wceq vd cv vb
      cv cS wbr wo wo wa va cv vc cv wceq wn vb cv vd cv wceq wn wo vc cv va cv
      cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wi cA cR wor va cv cA
      wcel vc cv cA wcel wa wa va cv vc cv cR wbr wn va cv vc cv wceq vc cv va
      cv cR wbr wo cB cS wor vb cv cB wcel vd cv cB wcel wa wa va cv vc cv wceq
      wn vb cv vd cv cS wbr wn wo va cv vc cv wceq wn vb cv vd cv wceq vd cv vb
      cv cS wbr wo wo cA cR wor va cv cA wcel vc cv cA wcel wa wa va cv vc cv
      cR wbr va cv vc cv wceq vc cv va cv cR wbr w3o va cv vc cv cR wbr wn va
      cv vc cv wceq vc cv va cv cR wbr wo wi cA va cv vc cv cR solin va cv vc
      cv cR wbr va cv vc cv wceq vc cv va cv cR wbr w3o va cv vc cv cR wbr va
      cv vc cv wceq vc cv va cv cR wbr wo wo va cv vc cv cR wbr wn va cv vc cv
      wceq vc cv va cv cR wbr wo wi va cv vc cv cR wbr va cv vc cv wceq vc cv
      va cv cR wbr 3orass va cv vc cv cR wbr va cv vc cv wceq vc cv va cv cR
      wbr wo df-or bitri sylib cB cS wor vb cv cB wcel vd cv cB wcel wa wa vb
      cv vd cv cS wbr wn vb cv vd cv wceq vd cv vb cv cS wbr wo va cv vc cv
      wceq wn cB cS wor vb cv cB wcel vd cv cB wcel wa wa vb cv vd cv cS wbr vb
      cv vd cv wceq vd cv vb cv cS wbr w3o vb cv vd cv cS wbr wn vb cv vd cv
      wceq vd cv vb cv cS wbr wo wi cB vb cv vd cv cS solin vb cv vd cv cS wbr
      vb cv vd cv wceq vd cv vb cv cS wbr w3o vb cv vd cv cS wbr vb cv vd cv
      wceq vd cv vb cv cS wbr wo wo vb cv vd cv cS wbr wn vb cv vd cv wceq vd
      cv vb cv cS wbr wo wi vb cv vd cv cS wbr vb cv vd cv wceq vd cv vb cv cS
      wbr 3orass vb cv vd cv cS wbr vb cv vd cv wceq vd cv vb cv cS wbr wo
      df-or bitri sylib orim2d im2anan9 va cv vc cv wceq vc cv va cv cR wbr wo
      va cv vc cv wceq wn vb cv vd cv wceq vd cv vb cv cS wbr wo wo wa va cv vc
      cv wceq wn vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo
      vb cv vd cv wceq wn va cv vc cv wceq vc cv va cv cR wbr wo va cv vc cv
      wceq wn vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wi
      va cv vc cv wceq wn vb cv vd cv wceq vd cv vb cv cS wbr wo wo va cv vc cv
      wceq vc cv va cv cR wbr wo va cv vc cv wceq wn vc cv va cv cR wbr vc cv
      va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo va cv vc cv wceq
      vc cv va cv cR wbr pm2.53 vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv
      cS wbr wa orc syl6 adantr vb cv vd cv wceq wn va cv vc cv wceq vc cv va
      cv cR wbr wo va cv vc cv wceq wn vb cv vd cv wceq vd cv vb cv cS wbr wo
      wo wa va cv vc cv wceq vc cv va cv cR wbr wo va cv vc cv wceq wn vd cv vb
      cv cS wbr wo wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa
      wo vb cv vd cv wceq wn va cv vc cv wceq wn vb cv vd cv wceq vd cv vb cv
      cS wbr wo wo va cv vc cv wceq wn vd cv vb cv cS wbr wo va cv vc cv wceq
      vc cv va cv cR wbr wo vb cv vd cv wceq wn vb cv vd cv wceq vd cv vb cv cS
      wbr wo vd cv vb cv cS wbr va cv vc cv wceq wn vb cv vd cv wceq vd cv vb
      cv cS wbr orel1 orim2d anim2d va cv vc cv wceq vc cv va cv cR wbr wo va
      cv vc cv wceq wn vd cv vb cv cS wbr wo vc cv va cv cR wbr vc cv va cv
      wceq vd cv vb cv cS wbr wa wo va cv vc cv wceq va cv vc cv wceq wn vd cv
      vb cv cS wbr wo vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa
      wo wi vc cv va cv cR wbr va cv vc cv wceq va cv vc cv wceq wn vd cv vb cv
      cS wbr wo vd cv vb cv cS wbr vc cv va cv cR wbr vc cv va cv wceq vd cv vb
      cv cS wbr wa wo va cv vc cv wceq wn vd cv vb cv cS wbr wo va cv vc cv
      wceq vd cv vb cv cS wbr va cv vc cv wceq vd cv vb cv cS wbr wi va cv vc
      cv wceq wn vd cv vb cv cS wbr wo va cv vc cv wceq vd cv vb cv cS wbr imor
      biimpri com12 va cv vc cv wceq vd cv vb cv cS wbr vc cv va cv cR wbr vc
      cv va cv wceq vd cv vb cv cS wbr wa wo va cv vc cv wceq vd cv vb cv cS
      wbr wa vc cv va cv wceq vd cv vb cv cS wbr wa vc cv va cv cR wbr va cv vc
      cv wceq vc cv va cv wceq vd cv vb cv cS wbr va vc equcomi anim1i olcd ex
      syld vc cv va cv cR wbr vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv
      cS wbr wa wo va cv vc cv wceq wn vd cv vb cv cS wbr wo vc cv va cv cR wbr
      vc cv va cv wceq vd cv vb cv cS wbr wa orc a1d jaoi imp syl6com jaod syl6
      imp3a syl5bi va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo
      va cv vc cv wceq vb cv vd cv wceq wa vc cv va cv cR wbr vc cv va cv wceq
      vd cv vb cv cS wbr wa wo w3o va cv vc cv cR wbr va cv vc cv wceq vb cv vd
      cv cS wbr wa wo va cv vc cv wceq vb cv vd cv wceq wa wo vc cv va cv cR
      wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wo va cv vc cv cR wbr va cv
      vc cv wceq vb cv vd cv cS wbr wa wo va cv vc cv wceq vb cv vd cv wceq wa
      wo wn vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wi va
      cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo va cv vc cv
      wceq vb cv vd cv wceq wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv
      cS wbr wa wo df-3or va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS
      wbr wa wo va cv vc cv wceq vb cv vd cv wceq wa wo vc cv va cv cR wbr vc
      cv va cv wceq vd cv vb cv cS wbr wa wo df-or bitri sylibr cA cR wor va cv
      cA wcel vc cv cA wcel wa wa cB cS wor vb cv cB wcel vd cv cB wcel wa wa
      wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo va cv cA
      wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR
      wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo wa va cv vc cv wceq vb cv
      vd cv wceq wa va cv vc cv wceq vb cv vd cv wceq wa vc cv va cv cR wbr vc
      cv va cv wceq vd cv vb cv cS wbr wa wo vc cv cA wcel va cv cA wcel wa vd
      cv cB wcel vb cv cB wcel wa wa vc cv va cv cR wbr vc cv va cv wceq vd cv
      vb cv cS wbr wa wo wa va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv
      cB wcel wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo
      va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc
      cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo wa wi cA cR wor cB cS
      wor va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va
      cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo pm3.2 ad2ant2l
      cA cR wor va cv cA wcel vc cv cA wcel wa wa cB cS wor vb cv cB wcel vd cv
      cB wcel wa wa wa va cv vc cv wceq vb cv vd cv wceq wa idd cA cR wor va cv
      cA wcel vc cv cA wcel wa wa vc cv cA wcel va cv cA wcel wa vd cv cB wcel
      vb cv cB wcel wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr
      wa wo vc cv cA wcel va cv cA wcel wa vd cv cB wcel vb cv cB wcel wa wa vc
      cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wa wi cB cS wor
      vb cv cB wcel vd cv cB wcel wa wa cA cR wor va cv cA wcel vc cv cA wcel
      wa wa va cv cA wcel vc cv cA wcel cA cR wor va cv cA wcel vc cv cA wcel
      wa simpr ancomd cB cS wor vb cv cB wcel vd cv cB wcel wa wa vb cv cB wcel
      vd cv cB wcel cB cS wor vb cv cB wcel vd cv cB wcel wa simpr ancomd vc cv
      cA wcel va cv cA wcel wa vd cv cB wcel vb cv cB wcel wa wa vc cv va cv cR
      wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo pm3.2 syl2an 3orim123d mpd
      an4s expcom an4s vt cv va cv vb cv cop wceq vu cv vc cv vd cv cop wceq wa
      vt cv vu cv cT wbr vt cv vu cv wceq vu cv vt cv cT wbr w3o va cv cA wcel
      vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR wbr va
      cv vc cv wceq vb cv vd cv cS wbr wa wo wa va cv vc cv wceq vb cv vd cv
      wceq wa vc cv cA wcel va cv cA wcel wa vd cv cB wcel vb cv cB wcel wa wa
      vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wa w3o vt cv
      va cv vb cv cop wceq vu cv vc cv vd cv cop wceq wa vt cv vu cv cT wbr vt
      cv vu cv wceq vu cv vt cv cT wbr w3o va cv vb cv cop vc cv vd cv cop cT
      wbr va cv vb cv cop vc cv vd cv cop wceq vc cv vd cv cop va cv vb cv cop
      cT wbr w3o va cv cA wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa
      wa va cv vc cv cR wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo wa va cv
      vc cv wceq vb cv vd cv wceq wa vc cv cA wcel va cv cA wcel wa vd cv cB
      wcel vb cv cB wcel wa wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv
      cS wbr wa wo wa w3o vt cv va cv vb cv cop wceq vu cv vc cv vd cv cop wceq
      wa vt cv vu cv cT wbr va cv vb cv cop vc cv vd cv cop cT wbr vt cv vu cv
      wceq va cv vb cv cop vc cv vd cv cop wceq vu cv vt cv cT wbr vc cv vd cv
      cop va cv vb cv cop cT wbr vt cv va cv vb cv cop vu cv vc cv vd cv cop cT
      breq12 vt cv va cv vb cv cop vu cv vc cv vd cv cop eqeq12 vu cv vc cv vd
      cv cop wceq vt cv va cv vb cv cop wceq vu cv vt cv cT wbr vc cv vd cv cop
      va cv vb cv cop cT wbr wb vu cv vc cv vd cv cop vt cv va cv vb cv cop cT
      breq12 ancoms 3orbi123d va cv vb cv cop vc cv vd cv cop cT wbr va cv cA
      wcel vc cv cA wcel wa vb cv cB wcel vd cv cB wcel wa wa va cv vc cv cR
      wbr va cv vc cv wceq vb cv vd cv cS wbr wa wo wa va cv vb cv cop vc cv vd
      cv cop wceq va cv vc cv wceq vb cv vd cv wceq wa vc cv vd cv cop va cv vb
      cv cop cT wbr vc cv cA wcel va cv cA wcel wa vd cv cB wcel vb cv cB wcel
      wa wa vc cv va cv cR wbr vc cv va cv wceq vd cv vb cv cS wbr wa wo wa vx
      vy cA cB cR cS cT va vb vc vd soxp.1 xporderlem va cv vb cv vc cv vd cv
      va vex vb vex opth vx vy cA cB cR cS cT vc vd va vb soxp.1 xporderlem
      3orbi123i syl6bb biimprcd syl6 com3r imp an4s expcom exlimivv com12
      exlimivv imp syl2anb com12 ralrimivv vt vu cA cB cxp cT df-so sylanbrc $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d R x y $.  $d S x y $.
    wexp.1 $e |- T = { <. x , y >. | ( ( x e. ( A X. B ) /\ y e. ( A X. B ) )
      /\ ( ( 1st ` x ) R ( 1st ` y ) \/
           ( ( 1st ` x ) = ( 1st ` y ) /\ ( 2nd ` x ) S ( 2nd ` y ) ) ) ) } $.
    $( A lexicographical ordering of two well-ordered classes.  (Contributed by
       Scott Fenton, 17-Mar-2011.)  (Revised by Mario Carneiro, 7-Mar-2013.) $)
    wexp $p |- ( ( R We A /\ S We B ) -> T We ( A X. B ) ) $=
      cA cR wwe cB cS wwe wa cA cB cxp cT wfr cA cB cxp cT wor cA cB cxp cT wwe
      cA cR wwe cA cR wfr cB cS wfr cA cB cxp cT wfr cB cS wwe cA cR wefr cB cS
      wefr vx vy cA cB cR cS cT wexp.1 frxp syl2an cA cR wwe cA cR wor cB cS
      wor cA cB cxp cT wor cB cS wwe cA cR weso cB cS weso vx vy cA cB cR cS cT
      wexp.1 soxp syl2an cA cB cxp cT df-we sylanbrc $.
  $}

  ${
    $d s u v w x y z A $.  $d u v w x y z B $.  $d s w x y G $.  $d w x z ph $.
    $d u v w x y z F $.  $d s w x y Q $.  $d u v w x y R $.  $d u v w x y S $.
    $d s w T $.
    fnwe.1 $e |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\
      ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) } $.
    fnwe.2 $e |- ( ph -> F : A --> B ) $.
    fnwe.3 $e |- ( ph -> R We B ) $.
    fnwe.4 $e |- ( ph -> S We A ) $.
    fnwe.5 $e |- ( ph -> ( F " w ) e. _V ) $.
    ${
      fnwelem.6 $e |- Q = { <. u , v >. |
        ( ( u e. ( B X. A ) /\ v e. ( B X. A ) ) /\
          ( ( 1st ` u ) R ( 1st ` v ) \/
            ( ( 1st ` u ) = ( 1st ` v ) /\ ( 2nd ` u ) S ( 2nd ` v ) ) ) ) } $.
      fnwelem.7 $e |- G = ( z e. A |-> <. ( F ` z ) , z >. ) $.
      $( Lemma for ~ fnwe .  (Contributed by Mario Carneiro, 10-Mar-2013.)
         (Revised by Mario Carneiro, 18-Nov-2014.) $)
      fnwelem $p |- ( ph -> T We A ) $=
        wph cG crn cQ wwe cA cT wwe wph cG crn cB cA cxp wss cB cA cxp cQ wwe
        cG crn cQ wwe wph cA cB cF wf cA cB cA cxp cG wf cG crn cB cA cxp wss
        fnwe.2 cA cB cF wf vz cA vz cv cF cfv vz cv cop cB cA cxp cG cA cB cF
        wf vz cv cA wcel wa vz cv cF cfv cB wcel vz cv cA wcel vz cv cF cfv vz
        cv cop cB cA cxp wcel cA cB vz cv cF ffvelrn cA cB cF wf vz cv cA wcel
        simpr vz cv cF cfv vz cv cB cA opelxp sylanbrc fnwelem.7 fmptd cA cB cA
        cxp cG frn 3syl wph cB cR wwe cA cS wwe cB cA cxp cQ wwe fnwe.3 fnwe.4
        vu vv cB cA cR cS cQ fnwelem.6 wexp syl2anc cG crn cB cA cxp cQ wess
        sylc wph cA cG crn cT cQ cG ccnv ccnv wiso cG ccnv ccnv vw cv cima cvv
        wcel vw wal cG crn cQ wwe cA cT wwe wi wph cG crn cA cQ cT cG ccnv wiso
        cA cG crn cT cQ cG ccnv ccnv wiso wph cA cB cF wf cG crn cA cG ccnv
        wf1o cG crn cA cQ cT cG ccnv wiso fnwe.2 wph cA cB cA cxp cG wf1 cA cG
        crn cG wf1o cG crn cA cG ccnv wf1o wph cA cB cF wf cA cB cA cxp cG wf1
        fnwe.2 cA cB cF wf cA cB cA cxp cG wf vx cv cG cfv vy cv cG cfv wceq vx
        cv vy cv wceq wi vy cA wral vx cA wral cA cB cA cxp cG wf1 cA cB cF wf
        vz cA vz cv cF cfv vz cv cop cB cA cxp cG cA cB cF wf vz cv cA wcel wa
        vz cv cF cfv cB wcel vz cv cA wcel vz cv cF cfv vz cv cop cB cA cxp
        wcel cA cB vz cv cF ffvelrn cA cB cF wf vz cv cA wcel simpr vz cv cF
        cfv vz cv cB cA opelxp sylanbrc fnwelem.7 fmptd vx cv cG cfv vy cv cG
        cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA cB cF wf vx cv cG
        cfv vy cv cG cfv wceq vx cv vy cv wceq wi vx vy cA vx cv cA wcel vy cv
        cA wcel wa vx cv cG cfv vy cv cG cfv wceq vx cv cF cfv vx cv cop vy cv
        cF cfv vy cv cop wceq vx cv vy cv wceq vx cv cA wcel vy cv cA wcel vx
        cv cG cfv vx cv cF cfv vx cv cop vy cv cG cfv vy cv cF cfv vy cv cop vz
        vx cv vz cv cF cfv vz cv cop vx cv cF cfv vx cv cop cA cG vz cv vx cv
        wceq vz cv cF cfv vx cv cF cfv vz cv vx cv vz cv vx cv cF fveq2 vz cv
        vx cv wceq id opeq12d fnwelem.7 vx cv cF cfv vx cv opex fvmpt vz vy cv
        vz cv cF cfv vz cv cop vy cv cF cfv vy cv cop cA cG vz cv vy cv wceq vz
        cv cF cfv vy cv cF cfv vz cv vy cv vz cv vy cv cF fveq2 vz cv vy cv
        wceq id opeq12d fnwelem.7 vy cv cF cfv vy cv opex fvmpt eqeqan12d vx cv
        cF cfv vx cv cop vy cv cF cfv vy cv cop wceq vx cv cF cfv vy cv cF cfv
        wceq vx cv vy cv wceq vx cv cF cfv vx cv vy cv cF cfv vy cv vx cv cF
        fvex vx vex opth simprbi syl6bi rgen2a a1i vx vy cA cB cA cxp cG dff13
        sylanbrc syl cA cB cA cxp cG f1f1orn cA cG crn cG f1ocnv 3syl cG crn cA
        cG ccnv wf1o cG crn cA cQ cT cG ccnv wiso cA cB cF wf cG crn cA cQ vx
        cv cA wcel vy cv cA wcel wa vx cv cG ccnv ccnv cfv vy cv cG ccnv ccnv
        cfv cQ wbr wa vx vy copab cG ccnv wiso vx vy cG crn cA cQ vx cv cA wcel
        vy cv cA wcel wa vx cv cG ccnv ccnv cfv vy cv cG ccnv ccnv cfv cQ wbr
        wa vx vy copab cG ccnv vx cv cA wcel vy cv cA wcel wa vx cv cG ccnv
        ccnv cfv vy cv cG ccnv ccnv cfv cQ wbr wa vx vy copab eqid f1oiso2 cA
        cB cF wf cT vx cv cA wcel vy cv cA wcel wa vx cv cG ccnv ccnv cfv vy cv
        cG ccnv ccnv cfv cQ wbr wa vx vy copab wceq cG crn cA cQ cT cG ccnv
        wiso cG crn cA cQ vx cv cA wcel vy cv cA wcel wa vx cv cG ccnv ccnv cfv
        vy cv cG ccnv ccnv cfv cQ wbr wa vx vy copab cG ccnv wiso wb cA cB cF
        wf cT vx cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv cR wbr
        vx cv cF cfv vy cv cF cfv wceq vx cv vy cv cS wbr wa wo wa vx vy copab
        vx cv cA wcel vy cv cA wcel wa vx cv cG ccnv ccnv cfv vy cv cG ccnv
        ccnv cfv cQ wbr wa vx vy copab fnwe.1 cA cB cF wf vx cv cA wcel vy cv
        cA wcel wa vx cv cF cfv vy cv cF cfv cR wbr vx cv cF cfv vy cv cF cfv
        wceq vx cv vy cv cS wbr wa wo wa vx cv cA wcel vy cv cA wcel wa vx cv
        cG ccnv ccnv cfv vy cv cG ccnv ccnv cfv cQ wbr wa vx vy cA cB cF wf vx
        cv cA wcel vy cv cA wcel wa vx cv cF cfv vy cv cF cfv cR wbr vx cv cF
        cfv vy cv cF cfv wceq vx cv vy cv cS wbr wa wo vx cv cG ccnv ccnv cfv
        vy cv cG ccnv ccnv cfv cQ wbr cA cB cF wf vx cv cA wcel vy cv cA wcel
        wa wa vx cv cG ccnv ccnv cfv vy cv cG ccnv ccnv cfv cQ wbr vx cv cG cfv
        vy cv cG cfv cQ wbr vx cv cF cfv vx cv cop vy cv cF cfv vy cv cop cQ
        wbr vx cv cF cfv vy cv cF cfv cR wbr vx cv cF cfv vy cv cF cfv wceq vx
        cv vy cv cS wbr wa wo cA cB cF wf vx cv cG ccnv ccnv cfv vy cv cG ccnv
        ccnv cfv cQ wbr vx cv cG cfv vy cv cG cfv cQ wbr wb vx cv cA wcel vy cv
        cA wcel wa cA cB cF wf cA cB cA cxp cG wf vx cv cG ccnv ccnv cfv vy cv
        cG ccnv ccnv cfv cQ wbr vx cv cG cfv vy cv cG cfv cQ wbr wb cA cB cF wf
        vz cA vz cv cF cfv vz cv cop cB cA cxp cG cA cB cF wf vz cv cA wcel wa
        vz cv cF cfv cB wcel vz cv cA wcel vz cv cF cfv vz cv cop cB cA cxp
        wcel cA cB vz cv cF ffvelrn cA cB cF wf vz cv cA wcel simpr vz cv cF
        cfv vz cv cB cA opelxp sylanbrc fnwelem.7 fmptd cA cB cA cxp cG wf vx
        cv cG ccnv ccnv cfv vx cv cG cfv vy cv cG ccnv ccnv cfv vy cv cG cfv cQ
        cA cB cA cxp cG wf vx cv cG ccnv ccnv cG cA cB cA cxp cG wf cG wrel cG
        ccnv ccnv cG wceq cA cB cA cxp cG frel cG dfrel2 sylib fveq1d cA cB cA
        cxp cG wf vy cv cG ccnv ccnv cG cA cB cA cxp cG wf cG wrel cG ccnv ccnv
        cG wceq cA cB cA cxp cG frel cG dfrel2 sylib fveq1d breq12d syl adantr
        vx cv cA wcel vy cv cA wcel wa vx cv cG cfv vy cv cG cfv cQ wbr vx cv
        cF cfv vx cv cop vy cv cF cfv vy cv cop cQ wbr wb cA cB cF wf vx cv cA
        wcel vy cv cA wcel vx cv cG cfv vx cv cF cfv vx cv cop vy cv cG cfv vy
        cv cF cfv vy cv cop cQ vz vx cv vz cv cF cfv vz cv cop vx cv cF cfv vx
        cv cop cA cG vz cv vx cv wceq vz cv cF cfv vx cv cF cfv vz cv vx cv vz
        cv vx cv cF fveq2 vz cv vx cv wceq id opeq12d fnwelem.7 vx cv cF cfv vx
        cv opex fvmpt vz vy cv vz cv cF cfv vz cv cop vy cv cF cfv vy cv cop cA
        cG vz cv vy cv wceq vz cv cF cfv vy cv cF cfv vz cv vy cv vz cv vy cv
        cF fveq2 vz cv vy cv wceq id opeq12d fnwelem.7 vy cv cF cfv vy cv opex
        fvmpt breqan12d adantl cA cB cF wf vx cv cA wcel vy cv cA wcel wa wa vx
        cv cF cfv vy cv cF cfv cR wbr vx cv cF cfv vy cv cF cfv wceq vx cv vy
        cv cS wbr wa wo vx cv cF cfv cB wcel vx cv cA wcel wa vy cv cF cfv cB
        wcel vy cv cA wcel wa wa vx cv cF cfv vy cv cF cfv cR wbr vx cv cF cfv
        vy cv cF cfv wceq vx cv vy cv cS wbr wa wo wa vx cv cF cfv vx cv cop vy
        cv cF cfv vy cv cop cQ wbr cA cB cF wf vx cv cA wcel vy cv cA wcel wa
        wa vx cv cF cfv cB wcel vx cv cA wcel wa vy cv cF cfv cB wcel vy cv cA
        wcel wa wa vx cv cF cfv vy cv cF cfv cR wbr vx cv cF cfv vy cv cF cfv
        wceq vx cv vy cv cS wbr wa wo cA cB cF wf vx cv cA wcel vx cv cF cfv cB
        wcel vx cv cA wcel wa vy cv cA wcel vy cv cF cfv cB wcel vy cv cA wcel
        wa cA cB cF wf vx cv cA wcel wa vx cv cF cfv cB wcel vx cv cA wcel cA
        cB vx cv cF ffvelrn cA cB cF wf vx cv cA wcel simpr jca cA cB cF wf vy
        cv cA wcel wa vy cv cF cfv cB wcel vy cv cA wcel cA cB vy cv cF ffvelrn
        cA cB cF wf vy cv cA wcel simpr jca anim12dan biantrurd vu cv cB cA cxp
        wcel vv cv cB cA cxp wcel wa vu cv c1st cfv vv cv c1st cfv cR wbr vu cv
        c1st cfv vv cv c1st cfv wceq vu cv c2nd cfv vv cv c2nd cfv cS wbr wa wo
        wa vx cv cF cfv cB wcel vx cv cA wcel wa vv cv cB cA cxp wcel wa vx cv
        cF cfv vv cv c1st cfv cR wbr vx cv cF cfv vv cv c1st cfv wceq vx cv vv
        cv c2nd cfv cS wbr wa wo wa vx cv cF cfv cB wcel vx cv cA wcel wa vy cv
        cF cfv cB wcel vy cv cA wcel wa wa vx cv cF cfv vy cv cF cfv cR wbr vx
        cv cF cfv vy cv cF cfv wceq vx cv vy cv cS wbr wa wo wa vu vv vx cv cF
        cfv vx cv cop vy cv cF cfv vy cv cop cQ vx cv cF cfv vx cv opex vy cv
        cF cfv vy cv opex vu cv vx cv cF cfv vx cv cop wceq vu cv cB cA cxp
        wcel vv cv cB cA cxp wcel wa vx cv cF cfv cB wcel vx cv cA wcel wa vv
        cv cB cA cxp wcel wa vu cv c1st cfv vv cv c1st cfv cR wbr vu cv c1st
        cfv vv cv c1st cfv wceq vu cv c2nd cfv vv cv c2nd cfv cS wbr wa wo vx
        cv cF cfv vv cv c1st cfv cR wbr vx cv cF cfv vv cv c1st cfv wceq vx cv
        vv cv c2nd cfv cS wbr wa wo vu cv vx cv cF cfv vx cv cop wceq vu cv cB
        cA cxp wcel vx cv cF cfv cB wcel vx cv cA wcel wa vv cv cB cA cxp wcel
        vu cv vx cv cF cfv vx cv cop wceq vu cv cB cA cxp wcel vx cv cF cfv vx
        cv cop cB cA cxp wcel vx cv cF cfv cB wcel vx cv cA wcel wa vu cv vx cv
        cF cfv vx cv cop cB cA cxp eleq1 vx cv cF cfv vx cv cB cA opelxp syl6bb
        anbi1d vu cv vx cv cF cfv vx cv cop wceq vu cv c1st cfv vv cv c1st cfv
        cR wbr vx cv cF cfv vv cv c1st cfv cR wbr vu cv c1st cfv vv cv c1st cfv
        wceq vu cv c2nd cfv vv cv c2nd cfv cS wbr wa vx cv cF cfv vv cv c1st
        cfv wceq vx cv vv cv c2nd cfv cS wbr wa vu cv vx cv cF cfv vx cv cop
        wceq vu cv c1st cfv vx cv cF cfv vv cv c1st cfv cR vx cv cF cfv vx cv
        vu cv vx cv cF fvex vx vex op1std breq1d vu cv vx cv cF cfv vx cv cop
        wceq vu cv c1st cfv vv cv c1st cfv wceq vx cv cF cfv vv cv c1st cfv
        wceq vu cv c2nd cfv vv cv c2nd cfv cS wbr vx cv vv cv c2nd cfv cS wbr
        vu cv vx cv cF cfv vx cv cop wceq vu cv c1st cfv vx cv cF cfv vv cv
        c1st cfv vx cv cF cfv vx cv vu cv vx cv cF fvex vx vex op1std eqeq1d vu
        cv vx cv cF cfv vx cv cop wceq vu cv c2nd cfv vx cv vv cv c2nd cfv cS
        vx cv cF cfv vx cv vu cv vx cv cF fvex vx vex op2ndd breq1d anbi12d
        orbi12d anbi12d vv cv vy cv cF cfv vy cv cop wceq vx cv cF cfv cB wcel
        vx cv cA wcel wa vv cv cB cA cxp wcel wa vx cv cF cfv cB wcel vx cv cA
        wcel wa vy cv cF cfv cB wcel vy cv cA wcel wa wa vx cv cF cfv vv cv
        c1st cfv cR wbr vx cv cF cfv vv cv c1st cfv wceq vx cv vv cv c2nd cfv
        cS wbr wa wo vx cv cF cfv vy cv cF cfv cR wbr vx cv cF cfv vy cv cF cfv
        wceq vx cv vy cv cS wbr wa wo vv cv vy cv cF cfv vy cv cop wceq vv cv
        cB cA cxp wcel vy cv cF cfv cB wcel vy cv cA wcel wa vx cv cF cfv cB
        wcel vx cv cA wcel wa vv cv vy cv cF cfv vy cv cop wceq vv cv cB cA cxp
        wcel vy cv cF cfv vy cv cop cB cA cxp wcel vy cv cF cfv cB wcel vy cv
        cA wcel wa vv cv vy cv cF cfv vy cv cop cB cA cxp eleq1 vy cv cF cfv vy
        cv cB cA opelxp syl6bb anbi2d vv cv vy cv cF cfv vy cv cop wceq vx cv
        cF cfv vv cv c1st cfv cR wbr vx cv cF cfv vy cv cF cfv cR wbr vx cv cF
        cfv vv cv c1st cfv wceq vx cv vv cv c2nd cfv cS wbr wa vx cv cF cfv vy
        cv cF cfv wceq vx cv vy cv cS wbr wa vv cv vy cv cF cfv vy cv cop wceq
        vv cv c1st cfv vy cv cF cfv vx cv cF cfv cR vy cv cF cfv vy cv vv cv vy
        cv cF fvex vy vex op1std breq2d vv cv vy cv cF cfv vy cv cop wceq vx cv
        cF cfv vv cv c1st cfv wceq vx cv cF cfv vy cv cF cfv wceq vx cv vv cv
        c2nd cfv cS wbr vx cv vy cv cS wbr vv cv vy cv cF cfv vy cv cop wceq vv
        cv c1st cfv vy cv cF cfv vx cv cF cfv vy cv cF cfv vy cv vv cv vy cv cF
        fvex vy vex op1std eqeq2d vv cv vy cv cF cfv vy cv cop wceq vv cv c2nd
        cfv vy cv vx cv cS vy cv cF cfv vy cv vv cv vy cv cF fvex vy vex op2ndd
        breq2d anbi12d orbi12d anbi12d fnwelem.6 brab syl6rbbr 3bitrrd pm5.32da
        opabbidv syl5eq cG crn cA cQ cT vx cv cA wcel vy cv cA wcel wa vx cv cG
        ccnv ccnv cfv vy cv cG ccnv ccnv cfv cQ wbr wa vx vy copab cG ccnv
        isoeq3 syl syl5ibr sylc cG crn cA cQ cT cG ccnv isocnv syl wph cG ccnv
        ccnv vw cv cima cvv wcel vw wph cG ccnv ccnv vw cv cima cG vw cv cima
        cvv cG vw cv imacnvcnv wph cG vw cv cima cF vw cv cima vw cv cxp wss cF
        vw cv cima vw cv cxp cvv wcel cG vw cv cima cvv wcel wph cG vw cv cima
        cG cG vw cv cres cdm cima cF vw cv cima vw cv cxp cG vw cv imadmres wph
        cG cG vw cv cres cdm cima cF vw cv cima vw cv cxp wss vx cv cG cfv cF
        vw cv cima vw cv cxp wcel vx cG vw cv cres cdm wral wph vx cv cG cfv cF
        vw cv cima vw cv cxp wcel vx cG vw cv cres cdm vx cv cG vw cv cres cdm
        wcel wph vx cv vw cv wcel vx cv cG cdm wcel wa vx cv cG cfv cF vw cv
        cima vw cv cxp wcel vx cv vw cv cG cdm cG vw cv cres cdm cG vw cv dmres
        elin2 wph vx cv vw cv wcel vx cv cG cdm wcel wa wa vx cv cG cfv vx cv
        cF cfv vx cv cop cF vw cv cima vw cv cxp wph vx cv vw cv wcel vx cv cG
        cdm wcel wa wa vx cv cA wcel vx cv cG cfv vx cv cF cfv vx cv cop wceq
        wph vx cv vw cv wcel vx cv cG cdm wcel wa wa vx cv cG cdm cA wph vx cv
        vw cv wcel vx cv cG cdm wcel simprr wph cG cdm cA wceq vx cv vw cv wcel
        vx cv cG cdm wcel wa wph cA cB cF wf cA cB cA cxp cG wf1 cG cdm cA wceq
        fnwe.2 cA cB cF wf cA cB cA cxp cG wf vx cv cG cfv vy cv cG cfv wceq vx
        cv vy cv wceq wi vy cA wral vx cA wral cA cB cA cxp cG wf1 cA cB cF wf
        vz cA vz cv cF cfv vz cv cop cB cA cxp cG cA cB cF wf vz cv cA wcel wa
        vz cv cF cfv cB wcel vz cv cA wcel vz cv cF cfv vz cv cop cB cA cxp
        wcel cA cB vz cv cF ffvelrn cA cB cF wf vz cv cA wcel simpr vz cv cF
        cfv vz cv cB cA opelxp sylanbrc fnwelem.7 fmptd vx cv cG cfv vy cv cG
        cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA cB cF wf vx cv cG
        cfv vy cv cG cfv wceq vx cv vy cv wceq wi vx vy cA vx cv cA wcel vy cv
        cA wcel wa vx cv cG cfv vy cv cG cfv wceq vx cv cF cfv vx cv cop vy cv
        cF cfv vy cv cop wceq vx cv vy cv wceq vx cv cA wcel vy cv cA wcel vx
        cv cG cfv vx cv cF cfv vx cv cop vy cv cG cfv vy cv cF cfv vy cv cop vz
        vx cv vz cv cF cfv vz cv cop vx cv cF cfv vx cv cop cA cG vz cv vx cv
        wceq vz cv cF cfv vx cv cF cfv vz cv vx cv vz cv vx cv cF fveq2 vz cv
        vx cv wceq id opeq12d fnwelem.7 vx cv cF cfv vx cv opex fvmpt vz vy cv
        vz cv cF cfv vz cv cop vy cv cF cfv vy cv cop cA cG vz cv vy cv wceq vz
        cv cF cfv vy cv cF cfv vz cv vy cv vz cv vy cv cF fveq2 vz cv vy cv
        wceq id opeq12d fnwelem.7 vy cv cF cfv vy cv opex fvmpt eqeqan12d vx cv
        cF cfv vx cv cop vy cv cF cfv vy cv cop wceq vx cv cF cfv vy cv cF cfv
        wceq vx cv vy cv wceq vx cv cF cfv vx cv vy cv cF cfv vy cv vx cv cF
        fvex vx vex opth simprbi syl6bi rgen2a a1i vx vy cA cB cA cxp cG dff13
        sylanbrc cA cB cA cxp cG f1dm 3syl adantr eleqtrd vz vx cv vz cv cF cfv
        vz cv cop vx cv cF cfv vx cv cop cA cG vz cv vx cv wceq vz cv cF cfv vx
        cv cF cfv vz cv vx cv vz cv vx cv cF fveq2 vz cv vx cv wceq id opeq12d
        fnwelem.7 vx cv cF cfv vx cv opex fvmpt syl wph vx cv vw cv wcel vx cv
        cG cdm wcel wa wa vx cv cF cfv cF vw cv cima wcel vx cv vw cv wcel vx
        cv cF cfv vx cv cop cF vw cv cima vw cv cxp wcel wph vx cv vw cv wcel
        vx cv cG cdm wcel wa wa vx cv cF cfv cF cF vw cv cres cdm cima cF vw cv
        cima wph vx cv vw cv wcel vx cv cG cdm wcel wa wa cF cA wfn cF vw cv
        cres cdm cA wss vx cv cF vw cv cres cdm wcel vx cv cF cfv cF cF vw cv
        cres cdm cima wcel wph cF cA wfn vx cv vw cv wcel vx cv cG cdm wcel wa
        wph cA cB cF wf cF cA wfn fnwe.2 cA cB cF ffn syl adantr wph vx cv vw
        cv wcel vx cv cG cdm wcel wa wa cF vw cv cres cdm vw cv cF cdm cin cA
        cF vw cv dmres wph vx cv vw cv wcel vx cv cG cdm wcel wa wa cF cdm vw
        cv cF cdm cin cA vw cv cF cdm inss2 wph vx cv vw cv wcel vx cv cG cdm
        wcel wa wa cF cA wfn cF cdm cA wceq wph cF cA wfn vx cv vw cv wcel vx
        cv cG cdm wcel wa wph cA cB cF wf cF cA wfn fnwe.2 cA cB cF ffn syl
        adantr cA cF fndm syl syl5sseq syl5eqss wph vx cv vw cv wcel vx cv cG
        cdm wcel wa wa vx cv vw cv wcel vx cv cF cdm wcel vx cv cF vw cv cres
        cdm wcel wph vx cv vw cv wcel vx cv cG cdm wcel simprl wph vx cv vw cv
        wcel vx cv cG cdm wcel wa wa vx cv cA cF cdm wph vx cv vw cv wcel vx cv
        cG cdm wcel wa wa vx cv cG cdm cA wph vx cv vw cv wcel vx cv cG cdm
        wcel simprr wph cG cdm cA wceq vx cv vw cv wcel vx cv cG cdm wcel wa
        wph cA cB cF wf cA cB cA cxp cG wf1 cG cdm cA wceq fnwe.2 cA cB cF wf
        cA cB cA cxp cG wf vx cv cG cfv vy cv cG cfv wceq vx cv vy cv wceq wi
        vy cA wral vx cA wral cA cB cA cxp cG wf1 cA cB cF wf vz cA vz cv cF
        cfv vz cv cop cB cA cxp cG cA cB cF wf vz cv cA wcel wa vz cv cF cfv cB
        wcel vz cv cA wcel vz cv cF cfv vz cv cop cB cA cxp wcel cA cB vz cv cF
        ffvelrn cA cB cF wf vz cv cA wcel simpr vz cv cF cfv vz cv cB cA opelxp
        sylanbrc fnwelem.7 fmptd vx cv cG cfv vy cv cG cfv wceq vx cv vy cv
        wceq wi vy cA wral vx cA wral cA cB cF wf vx cv cG cfv vy cv cG cfv
        wceq vx cv vy cv wceq wi vx vy cA vx cv cA wcel vy cv cA wcel wa vx cv
        cG cfv vy cv cG cfv wceq vx cv cF cfv vx cv cop vy cv cF cfv vy cv cop
        wceq vx cv vy cv wceq vx cv cA wcel vy cv cA wcel vx cv cG cfv vx cv cF
        cfv vx cv cop vy cv cG cfv vy cv cF cfv vy cv cop vz vx cv vz cv cF cfv
        vz cv cop vx cv cF cfv vx cv cop cA cG vz cv vx cv wceq vz cv cF cfv vx
        cv cF cfv vz cv vx cv vz cv vx cv cF fveq2 vz cv vx cv wceq id opeq12d
        fnwelem.7 vx cv cF cfv vx cv opex fvmpt vz vy cv vz cv cF cfv vz cv cop
        vy cv cF cfv vy cv cop cA cG vz cv vy cv wceq vz cv cF cfv vy cv cF cfv
        vz cv vy cv vz cv vy cv cF fveq2 vz cv vy cv wceq id opeq12d fnwelem.7
        vy cv cF cfv vy cv opex fvmpt eqeqan12d vx cv cF cfv vx cv cop vy cv cF
        cfv vy cv cop wceq vx cv cF cfv vy cv cF cfv wceq vx cv vy cv wceq vx
        cv cF cfv vx cv vy cv cF cfv vy cv vx cv cF fvex vx vex opth simprbi
        syl6bi rgen2a a1i vx vy cA cB cA cxp cG dff13 sylanbrc cA cB cA cxp cG
        f1dm 3syl adantr eleqtrd wph vx cv vw cv wcel vx cv cG cdm wcel wa wa
        cF cA wfn cF cdm cA wceq wph cF cA wfn vx cv vw cv wcel vx cv cG cdm
        wcel wa wph cA cB cF wf cF cA wfn fnwe.2 cA cB cF ffn syl adantr cA cF
        fndm syl eleqtrrd vx cv vw cv cF cdm cF vw cv cres cdm cF vw cv dmres
        elin2 sylanbrc cA cF vw cv cres cdm cF vx cv fnfvima syl3anc cF vw cv
        imadmres syl6eleq wph vx cv vw cv wcel vx cv cG cdm wcel simprl vx cv
        cF cfv vx cv cF vw cv cima vw cv opelxpi syl2anc eqeltrd sylan2b
        ralrimiva wph cG wfun cG vw cv cres cdm cG cdm wss cG cG vw cv cres cdm
        cima cF vw cv cima vw cv cxp wss vx cv cG cfv cF vw cv cima vw cv cxp
        wcel vx cG vw cv cres cdm wral wb wph cA cB cF wf cA cB cA cxp cG wf1
        cG wfun fnwe.2 cA cB cF wf cA cB cA cxp cG wf vx cv cG cfv vy cv cG cfv
        wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA cB cA cxp cG wf1 cA
        cB cF wf vz cA vz cv cF cfv vz cv cop cB cA cxp cG cA cB cF wf vz cv cA
        wcel wa vz cv cF cfv cB wcel vz cv cA wcel vz cv cF cfv vz cv cop cB cA
        cxp wcel cA cB vz cv cF ffvelrn cA cB cF wf vz cv cA wcel simpr vz cv
        cF cfv vz cv cB cA opelxp sylanbrc fnwelem.7 fmptd vx cv cG cfv vy cv
        cG cfv wceq vx cv vy cv wceq wi vy cA wral vx cA wral cA cB cF wf vx cv
        cG cfv vy cv cG cfv wceq vx cv vy cv wceq wi vx vy cA vx cv cA wcel vy
        cv cA wcel wa vx cv cG cfv vy cv cG cfv wceq vx cv cF cfv vx cv cop vy
        cv cF cfv vy cv cop wceq vx cv vy cv wceq vx cv cA wcel vy cv cA wcel
        vx cv cG cfv vx cv cF cfv vx cv cop vy cv cG cfv vy cv cF cfv vy cv cop
        vz vx cv vz cv cF cfv vz cv cop vx cv cF cfv vx cv cop cA cG vz cv vx
        cv wceq vz cv cF cfv vx cv cF cfv vz cv vx cv vz cv vx cv cF fveq2 vz
        cv vx cv wceq id opeq12d fnwelem.7 vx cv cF cfv vx cv opex fvmpt vz vy
        cv vz cv cF cfv vz cv cop vy cv cF cfv vy cv cop cA cG vz cv vy cv wceq
        vz cv cF cfv vy cv cF cfv vz cv vy cv vz cv vy cv cF fveq2 vz cv vy cv
        wceq id opeq12d fnwelem.7 vy cv cF cfv vy cv opex fvmpt eqeqan12d vx cv
        cF cfv vx cv cop vy cv cF cfv vy cv cop wceq vx cv cF cfv vy cv cF cfv
        wceq vx cv vy cv wceq vx cv cF cfv vx cv vy cv cF cfv vy cv vx cv cF
        fvex vx vex opth simprbi syl6bi rgen2a a1i vx vy cA cB cA cxp cG dff13
        sylanbrc cA cB cA cxp cG f1fun 3syl cG vw cv cres cG wss cG vw cv cres
        cdm cG cdm wss cG vw cv resss cG vw cv cres cG dmss ax-mp vx cG vw cv
        cres cdm cF vw cv cima vw cv cxp cG funimass4 sylancl mpbird syl5eqssr
        wph cF vw cv cima cvv wcel vw cv cvv wcel cF vw cv cima vw cv cxp cvv
        wcel fnwe.5 vw vex cF vw cv cima vw cv cvv cvv xpexg sylancl cG vw cv
        cima cF vw cv cima vw cv cxp cvv ssexg syl2anc syl5eqel alrimiv vw cA
        cG crn cT cQ cG ccnv ccnv isowe2 syl2anc mpd $.
    $}

    $( A variant on lexicographic order, which sorts first by some function of
       the base set, and then by a "backup" well-ordering when the function
       value is equal on both elements.  (Contributed by Mario Carneiro,
       10-Mar-2013.)  (Revised by Mario Carneiro, 18-Nov-2014.) $)
    fnwe $p |- ( ph -> T We A ) $=
      wph vx vy vz vw vv vu cA cB vu cv cB cA cxp wcel vv cv cB cA cxp wcel wa
      vu cv c1st cfv vv cv c1st cfv cR wbr vu cv c1st cfv vv cv c1st cfv wceq
      vu cv c2nd cfv vv cv c2nd cfv cS wbr wa wo wa vu vv copab cR cS cT cF vz
      cA vz cv cF cfv vz cv cop cmpt fnwe.1 fnwe.2 fnwe.3 fnwe.4 fnwe.5 vu cv
      cB cA cxp wcel vv cv cB cA cxp wcel wa vu cv c1st cfv vv cv c1st cfv cR
      wbr vu cv c1st cfv vv cv c1st cfv wceq vu cv c2nd cfv vv cv c2nd cfv cS
      wbr wa wo wa vu vv copab eqid vz cA vz cv cF cfv vz cv cop cmpt eqid
      fnwelem $.
  $}

  ${
    $d x y z A $.  $d u w B $.  $d u w x y F $.  $d w z ph $.  $d u w x y R $.
    $d u z $.  $d x y S $.  $d w z T $.
    fnse.1 $e |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\
      ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) } $.
    fnse.2 $e |- ( ph -> F : A --> B ) $.
    fnse.3 $e |- ( ph -> R Se B ) $.
    fnse.4 $e |- ( ph -> ( `' F " w ) e. _V ) $.
    $( Condition for the well-order in ~ fnwe to be set-like.  (Contributed by
       Mario Carneiro, 25-Jun-2015.) $)
    fnse $p |- ( ph -> T Se A ) $=
      wph cA cT ccnv vz cv csn cima cin cvv wcel vz cA wral cA cT wse wph cA cT
      ccnv vz cv csn cima cin cvv wcel vz cA wph vz cv cA wcel wa cA cT ccnv vz
      cv csn cima cin cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv
      csn cun cima wss cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF
      cfv csn cun cima cvv wcel cA cT ccnv vz cv csn cima cin cvv wcel wph cA
      cT ccnv vz cv csn cima cin cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab
      vz cv cF cfv csn cun cima wss vz cv cA wcel wph cA cT ccnv vz cv csn cima
      cin cT ccnv vz cv csn cima cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab
      vz cv cF cfv csn cun cima cA cT ccnv vz cv csn cima inss2 wph vw cT ccnv
      vz cv csn cima cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv
      csn cun cima vw cv cT ccnv vz cv csn cima wcel vw cv vz cv cT wbr wph vw
      cv cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cima
      wcel vz cv cvv wcel vw cv cT ccnv vz cv csn cima wcel vw cv vz cv cT wbr
      wb vz vex cT vz cv vw cv cvv vw vex eliniseg ax-mp vw cv vz cv cT wbr vw
      cv cA wcel vz cv cA wcel wa vw cv cF cfv vz cv cF cfv cR wbr vw cv cF cfv
      vz cv cF cfv wceq vw cv vz cv cS wbr wa wo wa wph vw cv cF ccnv vu cv vz
      cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cima wcel vx cv cF cfv
      vy cv cF cfv cR wbr vx cv cF cfv vy cv cF cfv wceq vx cv vy cv cS wbr wa
      wo vw cv cF cfv vz cv cF cfv cR wbr vw cv cF cfv vz cv cF cfv wceq vw cv
      vz cv cS wbr wa wo vx vy vw cv vz cv cA cA cT vx cv vw cv wceq vy cv vz
      cv wceq wa vx cv cF cfv vy cv cF cfv cR wbr vw cv cF cfv vz cv cF cfv cR
      wbr vx cv cF cfv vy cv cF cfv wceq vx cv vy cv cS wbr wa vw cv cF cfv vz
      cv cF cfv wceq vw cv vz cv cS wbr wa vx cv vw cv wceq vy cv vz cv wceq vx
      cv cF cfv vw cv cF cfv vy cv cF cfv vz cv cF cfv cR vx cv vw cv cF fveq2
      vy cv vz cv cF fveq2 breqan12d vx cv vw cv wceq vy cv vz cv wceq wa vx cv
      cF cfv vy cv cF cfv wceq vw cv cF cfv vz cv cF cfv wceq vx cv vy cv cS
      wbr vw cv vz cv cS wbr vx cv vw cv wceq vy cv vz cv wceq vx cv cF cfv vw
      cv cF cfv vy cv cF cfv vz cv cF cfv vx cv vw cv cF fveq2 vy cv vz cv cF
      fveq2 eqeqan12d vx cv vw cv vy cv vz cv cS breq12 anbi12d orbi12d fnse.1
      brab2ga wph vw cv cA wcel vz cv cA wcel wa vw cv cF cfv vz cv cF cfv cR
      wbr vw cv cF cfv vz cv cF cfv wceq vw cv vz cv cS wbr wa wo vw cv cF ccnv
      vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cima wcel wph
      vw cv cA wcel vz cv cA wcel wa wa vw cv cF cfv vz cv cF cfv cR wbr vw cv
      cF cfv vz cv cF cfv wceq vw cv vz cv cS wbr wa wo vw cv cA wcel vw cv cF
      cfv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun wcel wa vw
      cv cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cima
      wcel wph vw cv cA wcel vz cv cA wcel wa wa vw cv cF cfv vz cv cF cfv cR
      wbr vw cv cF cfv vz cv cF cfv wceq vw cv vz cv cS wbr wa wo vw cv cF cfv
      vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun wcel vw cv cA
      wcel wph vw cv cA wcel vz cv cA wcel wa wa vw cv cF cfv vz cv cF cfv cR
      wbr vw cv cF cfv vz cv cF cfv wceq vw cv vz cv cS wbr wa wo vw cv cF cfv
      vu cv vz cv cF cfv cR wbr vu cB crab wcel vw cv cF cfv vz cv cF cfv csn
      wcel wo vw cv cF cfv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv
      csn cun wcel wph vw cv cA wcel vz cv cA wcel wa wa vw cv cF cfv vz cv cF
      cfv cR wbr vw cv cF cfv vu cv vz cv cF cfv cR wbr vu cB crab wcel vw cv
      cF cfv vz cv cF cfv wceq vw cv vz cv cS wbr wa vw cv cF cfv vz cv cF cfv
      csn wcel wph vw cv cA wcel vz cv cA wcel wa wa vw cv cF cfv vu cv vz cv
      cF cfv cR wbr vu cB crab wcel vw cv cF cfv vz cv cF cfv cR wbr wph vw cv
      cA wcel vz cv cA wcel wa wa vw cv cF cfv cB wcel vw cv cF cfv vu cv vz cv
      cF cfv cR wbr vu cB crab wcel vw cv cF cfv vz cv cF cfv cR wbr wb wph vw
      cv cA wcel vw cv cF cfv cB wcel vz cv cA wcel wph cA cB cF wf vw cv cA
      wcel vw cv cF cfv cB wcel fnse.2 cA cB vw cv cF ffvelrn sylan adantrr vu
      cv vz cv cF cfv cR wbr vw cv cF cfv vz cv cF cfv cR wbr vu vw cv cF cfv
      cB vu cv vw cv cF cfv vz cv cF cfv cR breq1 elrab3 syl biimprd vw cv cF
      cfv vz cv cF cfv wceq vw cv vz cv cS wbr wa vw cv cF cfv vz cv cF cfv csn
      wcel wi wph vw cv cA wcel vz cv cA wcel wa wa vw cv cF cfv vz cv cF cfv
      wceq vw cv vz cv cS wbr wa vw cv cF cfv vz cv cF cfv wceq vw cv cF cfv vz
      cv cF cfv csn wcel vw cv cF cfv vz cv cF cfv wceq vw cv vz cv cS wbr
      simpl vw cv cF cfv vz cv cF cfv vw cv cF fvex elsnc sylibr a1i orim12d vw
      cv cF cfv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn elun
      syl6ibr wph vw cv cA wcel vz cv cA wcel simprl jctild wph vw cv cA wcel
      vz cv cA wcel wa wa cF cA wfn vw cv cF ccnv vu cv vz cv cF cfv cR wbr vu
      cB crab vz cv cF cfv csn cun cima wcel vw cv cA wcel vw cv cF cfv vu cv
      vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun wcel wa wb wph cF cA
      wfn vw cv cA wcel vz cv cA wcel wa wph cA cB cF wf cF cA wfn fnse.2 cA cB
      cF ffn syl adantr cA vw cv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF
      cfv csn cun cF elpreima syl sylibrd expimpd syl5bi syl5bi ssrdv syl5ss
      adantr wph vz cv cA wcel vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF
      cfv csn cun cvv wcel cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv
      cF cfv csn cun cima cvv wcel wph vz cv cA wcel wa vu cv vz cv cF cfv cR
      wbr vu cB crab cvv wcel vz cv cF cfv csn cvv wcel vu cv vz cv cF cfv cR
      wbr vu cB crab vz cv cF cfv csn cun cvv wcel wph vz cv cA wcel vz cv cF
      cfv cB wcel vu cv vz cv cF cfv cR wbr vu cB crab cvv wcel wph cA cB cF wf
      vz cv cA wcel vz cv cF cfv cB wcel fnse.2 cA cB vz cv cF ffvelrn sylan
      wph cB cR wse vz cv cF cfv cB wcel vu cv vz cv cF cfv cR wbr vu cB crab
      cvv wcel fnse.3 vu cB vz cv cF cfv cR seex sylan syldan vz cv cF cfv snex
      vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cvv cvv unexg
      sylancl vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cvv
      wcel wph cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn
      cun cima cvv wcel wph cF ccnv vw cv cima cvv wcel wi wph cF ccnv vu cv vz
      cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cima cvv wcel wi vw vu
      cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun cvv vw cv vu cv vz
      cv cF cfv cR wbr vu cB crab vz cv cF cfv csn cun wceq cF ccnv vw cv cima
      cvv wcel cF ccnv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF cfv csn
      cun cima cvv wcel wph vw cv vu cv vz cv cF cfv cR wbr vu cB crab vz cv cF
      cfv csn cun wceq cF ccnv vw cv cima cF ccnv vu cv vz cv cF cfv cR wbr vu
      cB crab vz cv cF cfv csn cun cima cvv vw cv vu cv vz cv cF cfv cR wbr vu
      cB crab vz cv cF cfv csn cun cF ccnv imaeq2 eleq1d imbi2d fnse.4 vtoclg
      impcom syldan cA cT ccnv vz cv csn cima cin cF ccnv vu cv vz cv cF cfv cR
      wbr vu cB crab vz cv cF cfv csn cun cima cvv ssexg syl2anc ralrimiva vz
      cA cT dfse2 sylibr $.
  $}



