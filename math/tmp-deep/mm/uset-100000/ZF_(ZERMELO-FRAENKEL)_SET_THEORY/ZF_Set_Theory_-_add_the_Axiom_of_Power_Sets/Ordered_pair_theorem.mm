
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Derive_the_Axiom_of_Pairing.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Ordered pair theorem

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $( An ordered pair is nonempty iff the arguments are sets.  (Contributed by
       NM, 24-Jan-2004.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    opnz $p |- ( <. A , B >. =/= (/) <-> ( A e. _V /\ B e. _V ) ) $=
      cA cB cop c0 wne cA cvv wcel cB cvv wcel wa cA cvv wcel cB cvv wcel wa cA
      cB cop c0 cA cB opprc necon1ai cA cvv wcel cB cvv wcel wa cA cB cop cA
      csn cA cB cpr cpr c0 cA cB cvv cvv dfopg cA csn cA cB cpr cpr c0 wne cA
      cvv wcel cB cvv wcel wa cA csn cA cB cpr cA snex prnz a1i eqnetrd impbii
      $.
  $}

  ${
    opth1.1 $e |- A e. _V $.
    opth1.2 $e |- B e. _V $.
    $( An ordered pair is nonempty if the arguments are sets.  (Contributed by
       Mario Carneiro, 26-Apr-2015.) $)
    opnzi $p |- <. A , B >. =/= (/) $=
      cA cB cop c0 wne cA cvv wcel cB cvv wcel opth1.1 opth1.2 cA cB opnz
      mpbir2an $.

    $( Equality of the first members of equal ordered pairs.  (Contributed by
       NM, 28-May-2008.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    opth1 $p |- ( <. A , B >. = <. C , D >. -> A = C ) $=
      cA cB cop cC cD cop wceq cA csn cC csn wceq cA cC wceq cA csn cC cD cpr
      wceq cA csn cC csn wceq cA cC wceq wi cA cB cop cC cD cop wceq cA cC
      opth1.1 sneqr a1i cA cB cop cC cD cop wceq cA csn cC cD cpr wceq cC cA
      csn wcel cA cC wceq cA cB cop cC cD cop wceq cC cA csn wcel cA csn cC cD
      cpr wceq cC cC cD cpr wcel cA cB cop cC cD cop wceq cC cvv wcel cC cC cD
      cpr wcel cA cB cop cC cD cop wceq cC cvv wcel cD cvv wcel cA cB cop cC cD
      cop wceq cA csn cC cD cop wcel cC cvv wcel cD cvv wcel wa cA cB cop cC cD
      cop wceq cA csn cA cB cop cC cD cop cA cB opth1.1 opth1.2 opi1 cA cB cop
      cC cD cop wceq id syl5eleq cC cD cA csn oprcl syl simpld cC cD cvv prid1g
      syl cA csn cC cD cpr cC eleq2 syl5ibrcom cC cA csn wcel cC cA cC cA elsni
      eqcomd syl6 cA cB cop cC cD cop wceq cA csn cC csn cC cD cpr cpr wcel cA
      csn cC csn wceq cA csn cC cD cpr wceq wo cA cB cop cC cD cop wceq cA csn
      cC cD cop cC csn cC cD cpr cpr cA cB cop cC cD cop wceq cA csn cA cB cop
      cC cD cop cA cB opth1.1 opth1.2 opi1 cA cB cop cC cD cop wceq id syl5eleq
      cA cB cop cC cD cop wceq cA csn cC cD cop wcel cC cvv wcel cD cvv wcel wa
      cC cD cop cC csn cC cD cpr cpr wceq cA cB cop cC cD cop wceq cA csn cA cB
      cop cC cD cop cA cB opth1.1 opth1.2 opi1 cA cB cop cC cD cop wceq id
      syl5eleq cC cD cA csn oprcl cC cD cvv cvv dfopg 3syl eleqtrd cA csn cC
      csn cC cD cpr elpri syl mpjaod $.

    $d x B $.  $d x C $.  $d x D $.
    $( The ordered pair theorem.  If two ordered pairs are equal, their first
       elements are equal and their second elements are equal.  Exercise 6 of
       [TakeutiZaring] p. 16.  Note that ` C ` and ` D ` are not required to be
       sets due our specific ordered pair definition.  (Contributed by NM,
       28-May-1995.) $)
    opth $p |- ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) $=
      cA cB cop cC cD cop wceq cA cC wceq cB cD wceq wa cA cB cop cC cD cop
      wceq cA cC wceq cB cD wceq cA cB cC cD opth1.1 opth1.2 opth1 cA cB cop cC
      cD cop wceq cD cvv wcel cC cB cpr cC cD cpr wceq cB cD wceq cA cB cop cC
      cD cop wceq cC cvv wcel cD cvv wcel cA cB cop cC cD cop wceq cA csn cC cD
      cop wcel cC cvv wcel cD cvv wcel wa cA cB cop cC cD cop wceq cA csn cA cB
      cop cC cD cop cA cB opth1.1 opth1.2 opi1 cA cB cop cC cD cop wceq id
      syl5eleq cC cD cA csn oprcl syl simprd cA cB cop cC cD cop wceq cC csn cC
      cB cpr cpr cC csn cC cD cpr cpr wceq cC cB cpr cC cD cpr wceq cA cB cop
      cC cD cop wceq cC cD cop cC csn cC cB cpr cpr cC csn cC cD cpr cpr cA cB
      cop cC cD cop wceq cC cB cop cC cD cop cC csn cC cB cpr cpr cA cB cop cC
      cD cop wceq cA cB cop cC cB cop cC cD cop cA cB cop cC cD cop wceq cA cC
      cB cA cB cC cD opth1.1 opth1.2 opth1 opeq1d cA cB cop cC cD cop wceq id
      eqtr3d cA cB cop cC cD cop wceq cC cvv wcel cB cvv wcel cC cB cop cC csn
      cC cB cpr cpr wceq cA cB cop cC cD cop wceq cC cvv wcel cD cvv wcel cA cB
      cop cC cD cop wceq cA csn cC cD cop wcel cC cvv wcel cD cvv wcel wa cA cB
      cop cC cD cop wceq cA csn cA cB cop cC cD cop cA cB opth1.1 opth1.2 opi1
      cA cB cop cC cD cop wceq id syl5eleq cC cD cA csn oprcl syl simpld
      opth1.2 cC cB cvv cvv dfopg sylancl eqtr3d cA cB cop cC cD cop wceq cC
      cvv wcel cD cvv wcel wa cC cD cop cC csn cC cD cpr cpr wceq cA cB cop cC
      cD cop wceq cA csn cC cD cop wcel cC cvv wcel cD cvv wcel wa cA cB cop cC
      cD cop wceq cA csn cA cB cop cC cD cop cA cB opth1.1 opth1.2 opi1 cA cB
      cop cC cD cop wceq id syl5eleq cC cD cA csn oprcl syl cC cD cvv cvv dfopg
      syl eqtr3d cC cB cpr cC cD cpr cC csn cC cB prex cC cD prex preqr2 syl cC
      cB cpr cC vx cv cpr wceq cB vx cv wceq wi cC cB cpr cC cD cpr wceq cB cD
      wceq wi vx cD cvv vx cv cD wceq cC cB cpr cC vx cv cpr wceq cC cB cpr cC
      cD cpr wceq cB vx cv wceq cB cD wceq vx cv cD wceq cC vx cv cpr cC cD cpr
      cC cB cpr vx cv cD cC preq2 eqeq2d vx cv cD cB eqeq2 imbi12d cB vx cv cC
      opth1.2 vx vex preqr2 vtoclg sylc jca cA cB cC cD opeq12 impbii $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y D $.
    $( Ordered pair theorem. ` C ` and ` D ` are not required to be sets under
       our specific ordered pair definition.  (Contributed by NM,
       14-Oct-2005.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    opthg $p |- ( ( A e. V /\ B e. W ) ->
                 ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) ) $=
      vx cv vy cv cop cC cD cop wceq vx cv cC wceq vy cv cD wceq wa wb cA vy cv
      cop cC cD cop wceq cA cC wceq vy cv cD wceq wa wb cA cB cop cC cD cop
      wceq cA cC wceq cB cD wceq wa wb vx vy cA cB cV cW vx cv cA wceq vx cv vy
      cv cop cC cD cop wceq cA vy cv cop cC cD cop wceq vx cv cC wceq vy cv cD
      wceq wa cA cC wceq vy cv cD wceq wa vx cv cA wceq vx cv vy cv cop cA vy
      cv cop cC cD cop vx cv cA vy cv opeq1 eqeq1d vx cv cA wceq vx cv cC wceq
      cA cC wceq vy cv cD wceq vx cv cA cC eqeq1 anbi1d bibi12d vy cv cB wceq
      cA vy cv cop cC cD cop wceq cA cB cop cC cD cop wceq cA cC wceq vy cv cD
      wceq wa cA cC wceq cB cD wceq wa vy cv cB wceq cA vy cv cop cA cB cop cC
      cD cop vy cv cB cA opeq2 eqeq1d vy cv cB wceq vy cv cD wceq cB cD wceq cA
      cC wceq vy cv cB cD eqeq1 anbi2d bibi12d vx cv vy cv cC cD vx vex vy vex
      opth vtocl2g $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y D $.  $d x y X $.
    $( Ordered pair theorem.  (Contributed by NM, 14-Oct-2005.)  (Revised by
       Mario Carneiro, 26-Apr-2015.) $)
    opthg2 $p |- ( ( C e. V /\ D e. W ) ->
                 ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) ) $=
      cC cV wcel cD cW wcel wa cC cD cop cA cB cop wceq cC cA wceq cD cB wceq
      wa cA cB cop cC cD cop wceq cA cC wceq cB cD wceq wa cC cD cA cB cV cW
      opthg cA cB cop cC cD cop eqcom cA cC wceq cC cA wceq cB cD wceq cD cB
      wceq cA cC eqcom cB cD eqcom anbi12i 3bitr4g $.
  $}

  ${
    opth2.1 $e |- C e. _V $.
    opth2.2 $e |- D e. _V $.
    $( Ordered pair theorem.  (Contributed by NM, 21-Sep-2014.) $)
    opth2 $p |- ( <. A , B >. = <. C , D >. <-> ( A = C /\ B = D ) ) $=
      cC cvv wcel cD cvv wcel cA cB cop cC cD cop wceq cA cC wceq cB cD wceq wa
      wb opth2.1 opth2.2 cA cB cC cD cvv cvv opthg2 mp2an $.
  $}

  ${
    otth.1 $e |- A e. _V $.
    otth.2 $e |- B e. _V $.
    otth.3 $e |- R e. _V $.
    $( Ordered triple theorem, with triple express with ordered pairs.
       (Contributed by NM, 1-May-1995.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    otth2 $p |- ( <. <. A , B >. , R >. = <. <. C , D >. , S >. <->
                ( A = C /\ B = D /\ R = S ) ) $=
      cA cB cop cC cD cop wceq cR cS wceq wa cA cC wceq cB cD wceq wa cR cS
      wceq wa cA cB cop cR cop cC cD cop cS cop wceq cA cC wceq cB cD wceq cR
      cS wceq w3a cA cB cop cC cD cop wceq cA cC wceq cB cD wceq wa cR cS wceq
      cA cB cC cD otth.1 otth.2 opth anbi1i cA cB cop cR cC cD cop cS cA cB
      opex otth.3 opth cA cC wceq cB cD wceq cR cS wceq df-3an 3bitr4i $.

    $( Ordered triple theorem.  (Contributed by NM, 25-Sep-2014.)  (Revised by
       Mario Carneiro, 26-Apr-2015.) $)
    otth $p |- ( <. A , B , R >. = <. C , D , S >. <->
      ( A = C /\ B = D /\ R = S ) ) $=
      cA cB cR cotp cC cD cS cotp wceq cA cB cop cR cop cC cD cop cS cop wceq
      cA cC wceq cB cD wceq cR cS wceq w3a cA cB cR cotp cA cB cop cR cop cC cD
      cS cotp cC cD cop cS cop cA cB cR df-ot cC cD cS df-ot eqeq12i cA cB cC
      cD cR cS otth.1 otth.2 otth.3 otth2 bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    eqvinop.1 $e |- B e. _V $.
    eqvinop.2 $e |- C e. _V $.
    $( A variable introduction law for ordered pairs.  Analog of Lemma 15 of
       [Monk2] p. 109.  (Contributed by NM, 28-May-1995.) $)
    eqvinop $p |- ( A = <. B , C >. <-> E. x E. y ( A = <. x , y >. /\
                  <. x , y >. = <. B , C >. ) ) $=
      cA vx cv vy cv cop wceq vx cv vy cv cop cB cC cop wceq wa vy wex vx wex
      vx cv cB wceq cA vx cv cC cop wceq wa vx wex cA cB cC cop wceq cA vx cv
      vy cv cop wceq vx cv vy cv cop cB cC cop wceq wa vy wex vx cv cB wceq cA
      vx cv cC cop wceq wa vx cA vx cv vy cv cop wceq vx cv vy cv cop cB cC cop
      wceq wa vy wex vx cv cB wceq vy cv cC wceq cA vx cv vy cv cop wceq wa wa
      vy wex vx cv cB wceq vy cv cC wceq cA vx cv vy cv cop wceq wa vy wex wa
      vx cv cB wceq cA vx cv cC cop wceq wa cA vx cv vy cv cop wceq vx cv vy cv
      cop cB cC cop wceq wa vx cv cB wceq vy cv cC wceq cA vx cv vy cv cop wceq
      wa wa vy cA vx cv vy cv cop wceq vx cv vy cv cop cB cC cop wceq wa cA vx
      cv vy cv cop wceq vx cv cB wceq vy cv cC wceq wa wa vx cv cB wceq vy cv
      cC wceq wa cA vx cv vy cv cop wceq wa vx cv cB wceq vy cv cC wceq cA vx
      cv vy cv cop wceq wa wa vx cv vy cv cop cB cC cop wceq vx cv cB wceq vy
      cv cC wceq wa cA vx cv vy cv cop wceq vx cv vy cv cB cC eqvinop.1
      eqvinop.2 opth2 anbi2i cA vx cv vy cv cop wceq vx cv cB wceq vy cv cC
      wceq wa ancom vx cv cB wceq vy cv cC wceq cA vx cv vy cv cop wceq anass
      3bitri exbii vx cv cB wceq vy cv cC wceq cA vx cv vy cv cop wceq wa vy
      19.42v vy cv cC wceq cA vx cv vy cv cop wceq wa vy wex cA vx cv cC cop
      wceq vx cv cB wceq cA vx cv vy cv cop wceq cA vx cv cC cop wceq vy cC
      eqvinop.2 vy cv cC wceq vx cv vy cv cop vx cv cC cop cA vy cv cC vx cv
      opeq2 eqeq2d ceqsexv anbi2i 3bitri exbii cA vx cv cC cop wceq cA cB cC
      cop wceq vx cB eqvinop.1 vx cv cB wceq vx cv cC cop cB cC cop cA vx cv cB
      cC opeq1 eqeq2d ceqsexv bitr2i $.
  $}

  ${
    $d x z w A $.  $d y z w A $.  $d z w ph $.
    $( Substitution of class ` A ` for ordered pair ` <. x , y >. ` .
       (Contributed by NM, 27-Dec-1996.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
    copsexg $p |- ( A = <. x , y >. ->
                  ( ph <-> E. x E. y ( A = <. x , y >. /\ ph ) ) ) $=
      cA vx cv vy cv cop wceq wph cA vx cv vy cv cop wceq wph wa vy wex vx wex
      wb cA vx cv vy cv cop wceq cA vz cv vw cv cop wceq vz cv vw cv cop vx cv
      vy cv cop wceq wa vw wex vz wex cA vx cv vy cv cop wceq wph cA vx cv vy
      cv cop wceq wph wa vy wex vx wex wb wi vz vw cA vx cv vy cv vx vex vy vex
      eqvinop cA vz cv vw cv cop wceq vz cv vw cv cop vx cv vy cv cop wceq wa
      cA vx cv vy cv cop wceq wph cA vx cv vy cv cop wceq wph wa vy wex vx wex
      wb wi vz vw cA vz cv vw cv cop wceq cA vx cv vy cv cop wceq wph cA vx cv
      vy cv cop wceq wph wa vy wex vx wex wb wi vz cv vw cv cop vx cv vy cv cop
      wceq cA vz cv vw cv cop wceq cA vx cv vy cv cop wceq wph cA vx cv vy cv
      cop wceq wph wa vy wex vx wex wb wi vz cv vw cv cop vx cv vy cv cop wceq
      wph vz cv vw cv cop vx cv vy cv cop wceq wph wa vy wex vx wex wb wi vz cv
      vw cv cop vx cv vy cv cop wceq wph vz cv vw cv cop vx cv vy cv cop wceq
      wph wa vy wex vx wex vz cv vw cv cop vx cv vy cv cop wceq wph vz cv vw cv
      cop vx cv vy cv cop wceq wph wa vy wex vx wex vz cv vw cv cop vx cv vy cv
      cop wceq wph wa vz cv vw cv cop vx cv vy cv cop wceq wph wa vy wex vx wex
      vy vz cv vw cv cop vx cv vy cv cop wceq wph wa vy wex vx 19.8a 19.23bi ex
      vz cv vw cv cop vx cv vy cv cop wceq vz cv vx cv wceq vw cv vy cv wceq wa
      vz cv vw cv cop vx cv vy cv cop wceq wph wa vy wex vx wex wph wi vz cv vw
      cv vx cv vy cv vz vex vw vex opth vz cv vw cv cop vx cv vy cv cop wceq
      wph wa vy wex vx wex vz cv vx cv wceq vw cv vy cv wceq wa wph wa vy wex
      vx wex vz cv vx cv wceq vw cv vy cv wceq wa wph vz cv vw cv cop vx cv vy
      cv cop wceq wph wa vz cv vx cv wceq vw cv vy cv wceq wa wph wa vx vy vz
      cv vw cv cop vx cv vy cv cop wceq vz cv vx cv wceq vw cv vy cv wceq wa
      wph vz cv vw cv vx cv vy cv vz vex vw vex opth anbi1i 2exbii vz cv vx cv
      wceq vw cv vy cv wceq wa wph wa vy wex vx wex vz cv vx cv wceq vw cv vy
      cv wceq wph wa vy wex wa vx wex vz cv vx cv wceq vw cv vy cv wceq wa wph
      vz cv vx cv wceq vw cv vy cv wceq wa wph wa vy wex vz cv vx cv wceq vw cv
      vy cv wceq wph wa vy wex wa vx wex vx vz cv vx cv wceq vw cv vy cv wceq
      wph wa vy wex wa vx nfe1 vy cv vx cv wceq vy wal vz cv vx cv wceq vw cv
      vy cv wceq wa wph wa vy wex vz cv vx cv wceq vw cv vy cv wceq wph wa vy
      wex wa vx wex wi vy cv vx cv wceq vy wal vz cv vx cv wceq vw cv vy cv
      wceq wa wph wa vy wex vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex wa
      vy wex vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex wa vx wex vy cv vx
      cv wceq vy wal vz cv vx cv wceq vw cv vy cv wceq wa wph wa vz cv vx cv
      wceq vw cv vy cv wceq wph wa vy wex wa vy vy cv vx cv wceq vy nfa1 vz cv
      vx cv wceq vw cv vy cv wceq wa wph wa vz cv vx cv wceq vw cv vy cv wceq
      wph wa wa vy cv vx cv wceq vy wal vz cv vx cv wceq vw cv vy cv wceq wph
      wa vy wex wa vz cv vx cv wceq vw cv vy cv wceq wph anass vy cv vx cv wceq
      vy wal vw cv vy cv wceq wph wa vw cv vy cv wceq wph wa vy wex vz cv vx cv
      wceq vw cv vy cv wceq wph wa vw cv vy cv wceq wph wa vy wex wi vy cv vx
      cv wceq vy wal vw cv vy cv wceq wph wa vy 19.8a a1i anim2d syl5bi eximd
      vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex wa vz cv vx cv wceq vw cv
      vy cv wceq wph wa vy wex wa vy vx vy cv vx cv wceq vy wal vz cv vx cv
      wceq vw cv vy cv wceq wph wa vy wex wa biidd drex1 sylibd vy cv vx cv
      wceq vy wal wn vz cv vx cv wceq vw cv vy cv wceq wa wph wa vy wex vz cv
      vx cv wceq vw cv vy cv wceq wph wa vy wex wa vz cv vx cv wceq vw cv vy cv
      wceq wph wa vy wex wa vx wex vz cv vx cv wceq vw cv vy cv wceq wa wph wa
      vy wex vz cv vx cv wceq vw cv vy cv wceq wph wa wa vy wex vy cv vx cv
      wceq vy wal wn vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex wa vz cv
      vx cv wceq vw cv vy cv wceq wa wph wa vz cv vx cv wceq vw cv vy cv wceq
      wph wa wa vy vz cv vx cv wceq vw cv vy cv wceq wph anass exbii vz cv vx
      cv wceq vw cv vy cv wceq wph wa wa vy wex vz cv vx cv wceq vy wex vw cv
      vy cv wceq wph wa vy wex wa vy cv vx cv wceq vy wal wn vz cv vx cv wceq
      vw cv vy cv wceq wph wa vy wex wa vz cv vx cv wceq vw cv vy cv wceq wph
      wa vy 19.40 vy cv vx cv wceq vy wal wn vz cv vx cv wceq vy wex vz cv vx
      cv wceq vw cv vy cv wceq wph wa vy wex vz cv vx cv wceq vy cv vx cv wceq
      vy wal wn vy vy cv vx cv wceq vy wal wn vz cv vx cv wceq vy vy vx vy
      nfnae vy vx vz dveeq2 nfd 19.9d anim1d syl5 syl5bi vz cv vx cv wceq vw cv
      vy cv wceq wph wa vy wex wa vx 19.8a syl6 pm2.61i exlimi vz cv vx cv wceq
      vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex wa vx wex vw cv vy cv
      wceq wph wa vy wex vw cv vy cv wceq wph vz cv vx cv wceq vw cv vy cv wceq
      wph wa vy wex wa vx wex vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex
      vz cv vx cv wceq vx weu vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex
      wa vx wex vz cv vx cv wceq vw cv vy cv wceq wph wa vy wex wi vx cv vz cv
      wceq vx weu vz cv vx cv wceq vx weu vx vz euequ1 vx cv vz cv wceq vz cv
      vx cv wceq vx vx vz equcom eubii mpbi vz cv vx cv wceq vw cv vy cv wceq
      wph wa vy wex vx eupick mpan com12 vw cv vy cv wceq wph wa vy wex vw cv
      vy cv wceq wph vw cv vy cv wceq vy weu vw cv vy cv wceq wph wa vy wex vw
      cv vy cv wceq wph wi vy cv vw cv wceq vy weu vw cv vy cv wceq vy weu vy
      vw euequ1 vy cv vw cv wceq vw cv vy cv wceq vy vy cv vw cv eqcom eubii
      mpbi vw cv vy cv wceq wph vy eupick mpan com12 sylan9 syl5 syl5bi sylbi
      impbid cA vz cv vw cv cop wceq cA vx cv vy cv cop wceq vz cv vw cv cop vx
      cv vy cv cop wceq wph cA vx cv vy cv cop wceq wph wa vy wex vx wex wb wph
      vz cv vw cv cop vx cv vy cv cop wceq wph wa vy wex vx wex wb cA vz cv vw
      cv cop vx cv vy cv cop eqeq1 cA vz cv vw cv cop wceq cA vx cv vy cv cop
      wceq wph wa vy wex vx wex vz cv vw cv cop vx cv vy cv cop wceq wph wa vy
      wex vx wex wph cA vz cv vw cv cop wceq cA vx cv vy cv cop wceq wph wa vz
      cv vw cv cop vx cv vy cv cop wceq wph wa vx vy cA vz cv vw cv cop wceq cA
      vx cv vy cv cop wceq vz cv vw cv cop vx cv vy cv cop wceq wph cA vz cv vw
      cv cop vx cv vy cv cop eqeq1 anbi1d 2exbidv bibi2d imbi12d mpbiri adantr
      exlimivv sylbi pm2.43i $.
  $}

  ${
    $d x y ps $.  $d x y A $.  $d x y B $.
    $( Closed theorem form of ~ copsex2g .  (Contributed by NM,
       17-Feb-2013.) $)
    copsex2t $p |- ( ( A. x A. y ( ( x = A /\ y = B ) -> ( ph <-> ps ) )
      /\ ( A e. V /\ B e. W ) ) ->
                  ( E. x E. y ( <. A , B >. = <. x , y >. /\ ph ) <-> ps ) ) $=
      cA cV wcel cB cW wcel wa vx cv cA wceq vy cv cB wceq wa wph wps wb wi vy
      wal vx wal vx cv cA wceq vy cv cB wceq wa vy wex vx wex cA cB cop vx cv
      vy cv cop wceq wph wa vy wex vx wex wps wb cA cV wcel cB cW wcel wa vx cv
      cA wceq vx wex vy cv cB wceq vy wex wa vx cv cA wceq vy cv cB wceq wa vy
      wex vx wex cA cV wcel vx cv cA wceq vx wex cB cW wcel vy cv cB wceq vy
      wex vx cA cV elisset vy cB cW elisset anim12i vx cv cA wceq vy cv cB wceq
      vx vy eeanv sylibr vx cv cA wceq vy cv cB wceq wa wph wps wb wi vy wal vx
      wal vx cv cA wceq vy cv cB wceq wa vy wex vx wex cA cB cop vx cv vy cv
      cop wceq wph wa vy wex vx wex wps wb vx cv cA wceq vy cv cB wceq wa wph
      wps wb wi vy wal vx wal vx cv cA wceq vy cv cB wceq wa vy wex cA cB cop
      vx cv vy cv cop wceq wph wa vy wex vx wex wps wb vx vx cv cA wceq vy cv
      cB wceq wa wph wps wb wi vy wal vx nfa1 cA cB cop vx cv vy cv cop wceq
      wph wa vy wex vx wex wps vx cA cB cop vx cv vy cv cop wceq wph wa vy wex
      vx nfe1 wps vx nfv nfbi vx cv cA wceq vy cv cB wceq wa wph wps wb wi vy
      wal vx wal vx cv cA wceq vy cv cB wceq wa cA cB cop vx cv vy cv cop wceq
      wph wa vy wex vx wex wps wb vy vx cv cA wceq vy cv cB wceq wa wph wps wb
      wi vy vx nfa2 cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wps vy
      cA cB cop vx cv vy cv cop wceq wph wa vy wex vy vx cA cB cop vx cv vy cv
      cop wceq wph wa vy nfe1 nfex wps vy nfv nfbi vx cv cA wceq vy cv cB wceq
      wa wph wps wb wi vy wal vx wal vx cv cA wceq vy cv cB wceq wa cA cB cop
      vx cv vy cv cop wceq wph wa vy wex vx wex wps wb vx cv cA wceq vy cv cB
      wceq wa wph wps wb wi vy wal vx wal vx cv cA wceq vy cv cB wceq wa wa wph
      cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wps vx cv cA wceq vy
      cv cB wceq wa wph cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wb
      vx cv cA wceq vy cv cB wceq wa wph wps wb wi vy wal vx wal vx cv cA wceq
      vy cv cB wceq wa vx cv vy cv cop cA cB cop wceq wph cA cB cop vx cv vy cv
      cop wceq wph wa vy wex vx wex wb vx cv vy cv cA cB opeq12 wph cA cB cop
      vx cv vy cv cop wceq wph wa vy wex vx wex wb cA cB cop vx cv vy cv cop
      wph vx vy cA cB cop copsexg eqcoms syl adantl vx cv cA wceq vy cv cB wceq
      wa wph wps wb wi vy wal vx wal vx cv cA wceq vy cv cB wceq wa wph wps wb
      vx cv cA wceq vy cv cB wceq wa wph wps wb wi vy wal vx wal vx cv cA wceq
      vy cv cB wceq wa wph wps wb wi vy vx cv cA wceq vy cv cB wceq wa wph wps
      wb wi vy wal vx sp 19.21bi imp bitr3d ex exlimd exlimd imp sylan2 $.
  $}

  ${
    $d x y ps $.  $d x y A $.  $d x y B $.
    copsex2g.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Implicit substitution inference for ordered pairs.  (Contributed by NM,
       28-May-1995.) $)
    copsex2g $p |- ( ( A e. V /\ B e. W ) ->
                  ( E. x E. y ( <. A , B >. = <. x , y >. /\ ph ) <-> ps ) ) $=
      cA cV wcel vx cv cA wceq vx wex vy cv cB wceq vy wex cA cB cop vx cv vy
      cv cop wceq wph wa vy wex vx wex wps wb cB cW wcel vx cA cV elisset vy cB
      cW elisset vx cv cA wceq vx wex vy cv cB wceq vy wex wa vx cv cA wceq vy
      cv cB wceq wa vy wex vx wex cA cB cop vx cv vy cv cop wceq wph wa vy wex
      vx wex wps wb vx cv cA wceq vy cv cB wceq vx vy eeanv vx cv cA wceq vy cv
      cB wceq wa vy wex cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wps
      wb vx cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wps vx cA cB
      cop vx cv vy cv cop wceq wph wa vy wex vx nfe1 wps vx nfv nfbi vx cv cA
      wceq vy cv cB wceq wa cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex
      wps wb vy cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wps vy cA
      cB cop vx cv vy cv cop wceq wph wa vy wex vy vx cA cB cop vx cv vy cv cop
      wceq wph wa vy nfe1 nfex wps vy nfv nfbi vx cv cA wceq vy cv cB wceq wa
      wph cA cB cop vx cv vy cv cop wceq wph wa vy wex vx wex wps vx cv cA wceq
      vy cv cB wceq wa vx cv vy cv cop cA cB cop wceq wph cA cB cop vx cv vy cv
      cop wceq wph wa vy wex vx wex wb vx cv vy cv cA cB opeq12 wph cA cB cop
      vx cv vy cv cop wceq wph wa vy wex vx wex wb cA cB cop vx cv vy cv cop
      wph vx vy cA cB cop copsexg eqcoms syl copsex2g.1 bitr3d exlimi exlimi
      sylbir syl2an $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d x y z w D $.
    $d x y z w ps $.  $d x y z w R $.  $d x y z w S $.
    copsex4g.1 $e |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) ->
                     ( ph <-> ps ) ) $.
    $( An implicit substitution inference for 2 ordered pairs.  (Contributed by
       NM, 5-Aug-1995.) $)
    copsex4g $p |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) ->
                      ( E. x E. y E. z E. w ( ( <. A , B >. = <. x , y >. /\
                      <. C , D >. = <. z , w >. ) /\ ph ) <-> ps ) ) $=
      cA cR wcel cB cS wcel wa cC cR wcel cD cS wcel wa wa cA cB cop vx cv vy
      cv cop wceq cC cD cop vz cv vw cv cop wceq wa wph wa vw wex vz wex vy wex
      vx wex vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa
      wph wa vw wex vz wex vy wex vx wex wps cA cR wcel cB cS wcel wa cC cR
      wcel cD cS wcel wa wa cA cB cop vx cv vy cv cop wceq cC cD cop vz cv vw
      cv cop wceq wa wph wa vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv
      cD wceq wa wa wph wa vx vy vz vw cA cB cop vx cv vy cv cop wceq cC cD cop
      vz cv vw cv cop wceq wa wph wa vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wa wa wph wa wb cA cR wcel cB cS wcel wa cC cR wcel cD
      cS wcel wa wa cA cB cop vx cv vy cv cop wceq cC cD cop vz cv vw cv cop
      wceq wa vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa
      wph cA cB cop vx cv vy cv cop wceq vx cv cA wceq vy cv cB wceq wa cC cD
      cop vz cv vw cv cop wceq vz cv cC wceq vw cv cD wceq wa cA cB cop vx cv
      vy cv cop wceq vx cv vy cv cop cA cB cop wceq vx cv cA wceq vy cv cB wceq
      wa cA cB cop vx cv vy cv cop eqcom vx cv vy cv cA cB vx vex vy vex opth
      bitri cC cD cop vz cv vw cv cop wceq vz cv vw cv cop cC cD cop wceq vz cv
      cC wceq vw cv cD wceq wa cC cD cop vz cv vw cv cop eqcom vz cv vw cv cC
      cD vz vex vw vex opth bitri anbi12i anbi1i a1i 4exbidv wph wps vx cv cA
      wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vx vy vz vw cA cB
      cC cD cR cS vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa
      wa id copsex4g.1 cgsex4g bitrd $.
  $}

  $( A property of ordered pairs.  (Contributed by Mario Carneiro,
     26-Apr-2015.) $)
  0nelop $p |- -. (/) e. <. A , B >. $=
    c0 cA cB cop wcel c0 cA csn wceq c0 cA cB cpr wceq wo c0 cA cB cop wcel c0
    cA csn cA cB cpr cpr wcel c0 cA csn wceq c0 cA cB cpr wceq wo c0 cA cB cop
    wcel c0 cA cB cop cA csn cA cB cpr cpr c0 cA cB cop wcel id c0 cA cB cop
    wcel cA cvv wcel cB cvv wcel wa cA cB cop cA csn cA cB cpr cpr wceq cA cB
    c0 oprcl cA cB cvv cvv dfopg syl eleqtrd c0 cA csn cA cB cpr elpri syl c0
    cA cB cop wcel c0 cA csn wne c0 cA cB cpr wne wa c0 cA csn wceq c0 cA cB
    cpr wceq wo wn c0 cA cB cop wcel c0 cA csn wne c0 cA cB cpr wne c0 cA cB
    cop wcel cA csn c0 c0 cA cB cop wcel cA cvv wcel cA csn c0 wne c0 cA cB cop
    wcel cA cvv wcel cB cvv wcel cA cB c0 oprcl simpld cA cvv snnzg syl necomd
    c0 cA cB cop wcel cA cB cpr c0 c0 cA cB cop wcel cA cvv wcel cA cB cpr c0
    wne c0 cA cB cop wcel cA cvv wcel cB cvv wcel cA cB c0 oprcl simpld cA cB
    cvv prnzg syl necomd jca c0 cA csn c0 cA cB cpr neanior sylib pm2.65i $.

  $( Equivalence of existence implied by equality of ordered pairs.
     (Contributed by NM, 28-May-2008.) $)
  opeqex $p |- ( <. A , B >. = <. C , D >. ->
    ( ( A e. _V /\ B e. _V ) <-> ( C e. _V /\ D e. _V ) ) ) $=
    cA cB cop cC cD cop wceq cA cB cop c0 wne cC cD cop c0 wne cA cvv wcel cB
    cvv wcel wa cC cvv wcel cD cvv wcel wa cA cB cop cC cD cop c0 neeq1 cA cB
    opnz cC cD opnz 3bitr3g $.

  $( Equivalence of existence implied by equality of ordered triples.
     (Contributed by NM, 26-Apr-2015.) $)
  oteqex2 $p |- ( <. <. A , B >. , C >. = <. <. R , S >. , T >. ->
    ( C e. _V <-> T e. _V ) ) $=
    cA cB cop cC cop cR cS cop cT cop wceq cA cB cop cvv wcel cC cvv wcel wa cR
    cS cop cvv wcel cT cvv wcel wa cC cvv wcel cT cvv wcel cA cB cop cC cR cS
    cop cT opeqex cA cB cop cvv wcel cC cvv wcel cA cB opex biantrur cR cS cop
    cvv wcel cT cvv wcel cR cS opex biantrur 3bitr4g $.

  $( Equivalence of existence implied by equality of ordered triples.
     (Contributed by NM, 28-May-2008.)  (Revised by Mario Carneiro,
     26-Apr-2015.) $)
  oteqex $p |- ( <. <. A , B >. , C >. = <. <. R , S >. , T >. ->
    ( ( A e. _V /\ B e. _V /\ C e. _V ) <->
      ( R e. _V /\ S e. _V /\ T e. _V ) ) ) $=
    cA cB cop cC cop cR cS cop cT cop wceq cC cvv wcel cA cvv wcel cB cvv wcel
    cC cvv wcel w3a cR cvv wcel cS cvv wcel cT cvv wcel w3a cA cvv wcel cB cvv
    wcel cC cvv wcel w3a cC cvv wcel wi cA cB cop cC cop cR cS cop cT cop wceq
    cA cvv wcel cB cvv wcel cC cvv wcel simp3 a1i cR cvv wcel cS cvv wcel cT
    cvv wcel w3a cC cvv wcel cA cB cop cC cop cR cS cop cT cop wceq cT cvv wcel
    cR cvv wcel cS cvv wcel cT cvv wcel simp3 cA cB cC cR cS cT oteqex2 syl5ibr
    cC cvv wcel cA cB cop cC cop cR cS cop cT cop wceq cA cvv wcel cB cvv wcel
    cC cvv wcel w3a cR cvv wcel cS cvv wcel cT cvv wcel w3a wb cC cvv wcel cA
    cB cop cC cop cR cS cop cT cop wceq wa cA cvv wcel cB cvv wcel wa cC cvv
    wcel wa cR cvv wcel cS cvv wcel wa cT cvv wcel wa cA cvv wcel cB cvv wcel
    cC cvv wcel w3a cR cvv wcel cS cvv wcel cT cvv wcel w3a cC cvv wcel cA cB
    cop cC cop cR cS cop cT cop wceq wa cA cvv wcel cB cvv wcel wa cR cvv wcel
    cS cvv wcel wa cC cvv wcel cT cvv wcel cC cvv wcel cA cB cop cC cop cR cS
    cop cT cop wceq wa cA cB cop cR cS cop wceq cA cvv wcel cB cvv wcel wa cR
    cvv wcel cS cvv wcel wa wb cC cvv wcel cA cB cop cC cop cR cS cop cT cop
    wceq cA cB cop cR cS cop wceq cC cT wceq cA cB cop cvv wcel cC cvv wcel cA
    cB cop cC cop cR cS cop cT cop wceq cA cB cop cR cS cop wceq cC cT wceq wa
    wb cA cB opex cA cB cop cC cR cS cop cT cvv cvv opthg mpan simprbda cA cB
    cR cS opeqex syl cA cB cop cC cop cR cS cop cT cop wceq cC cvv wcel cT cvv
    wcel wb cC cvv wcel cA cB cC cR cS cT oteqex2 adantl anbi12d cA cvv wcel cB
    cvv wcel cC cvv wcel df-3an cR cvv wcel cS cvv wcel cT cvv wcel df-3an
    3bitr4g expcom pm5.21ndd $.

  ${
    opcom.1 $e |- A e. _V $.
    opcom.2 $e |- B e. _V $.
    $( An ordered pair commutes iff its members are equal.  (Contributed by NM,
       28-May-2009.) $)
    opcom $p |- ( <. A , B >. = <. B , A >. <-> A = B ) $=
      cA cB cop cB cA cop wceq cA cB wceq cB cA wceq wa cA cB wceq cA cB wceq
      wa cA cB wceq cA cB cB cA opcom.1 opcom.2 opth cB cA wceq cA cB wceq cA
      cB wceq cB cA eqcom anbi2i cA cB wceq anidm 3bitri $.
  $}

  ${
    $d x y z A $.  $d y z B $.
    moop2.1 $e |- B e. _V $.
    $( "At most one" property of an ordered pair.  (Contributed by NM,
       11-Apr-2004.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    moop2 $p |- E* x A = <. B , x >. $=
      cA cB vx cv cop wceq vx wmo cA cB vx cv cop wceq cA vx vy cv cB csb vy cv
      cop wceq wa vx cv vy cv wceq wi vy wal vx wal cA cB vx cv cop wceq cA vx
      vy cv cB csb vy cv cop wceq wa vx cv vy cv wceq wi vx vy cA cB vx cv cop
      wceq cA vx vy cv cB csb vy cv cop wceq wa cB vx cv cop vx vy cv cB csb vy
      cv cop wceq vx cv vy cv wceq cA cB vx cv cop vx vy cv cB csb vy cv cop
      eqtr2 cB vx cv cop vx vy cv cB csb vy cv cop wceq cB vx vy cv cB csb wceq
      vx cv vy cv wceq cB vx cv vx vy cv cB csb vy cv moop2.1 vx vex opth
      simprbi syl gen2 cA cB vx cv cop wceq cA vx vy cv cB csb vy cv cop wceq
      vx vy vx cA vx vy cv cB csb vy cv cop vx vx vy cv cB csb vy cv vx vy cv
      cB nfcsb1v vx vy cv nfcv nfop nfeq2 vx cv vy cv wceq cB vx cv cop vx vy
      cv cB csb vy cv cop cA vx cv vy cv wceq cB vx vy cv cB csb vx cv vy cv vx
      vy cv cB csbeq1a vx cv vy cv wceq id opeq12d eqeq2d mo4f mpbir $.
  $}

  ${
    opeqsn.1 $e |- A e. _V $.
    opeqsn.2 $e |- B e. _V $.
    opeqsn.3 $e |- C e. _V $.
    $( Equivalence for an ordered pair equal to a singleton.  (Contributed by
       NM, 3-Jun-2008.) $)
    opeqsn $p |- ( <. A , B >. = { C } <-> ( A = B /\ C = { A } ) ) $=
      cA cB cop cC csn wceq cA csn cA cB cpr cpr cC csn wceq cA csn cA cB cpr
      wceq cA cB cpr cC wceq wa cA cB wceq cC cA csn wceq wa cA cB cop cA csn
      cA cB cpr cpr cC csn cA cB opeqsn.1 opeqsn.2 dfop eqeq1i cA csn cA cB cpr
      cC cA snex cA cB prex opeqsn.3 preqsn cA csn cA cB cpr wceq cA cB cpr cC
      wceq wa cA cB wceq cA cB cpr cC wceq wa cA cB wceq cC cA csn wceq wa cA
      csn cA cB cpr wceq cA cB wceq cA cB cpr cC wceq cA csn cA cB cpr wceq cA
      cB cpr cA csn wceq cA cB wceq cB cA wceq wa cA cB wceq cA csn cA cB cpr
      eqcom cA cB cA opeqsn.1 opeqsn.2 opeqsn.1 preqsn cA cB wceq cB cA wceq wa
      cA cB wceq cA cB wceq wa cA cB wceq cB cA wceq cA cB wceq cA cB wceq cB
      cA eqcom anbi2i cA cB wceq anidm bitri 3bitri anbi1i cA cB wceq cA cB cpr
      cC wceq cC cA csn wceq cA cB wceq cA cB cpr cC wceq cA csn cC wceq cC cA
      csn wceq cA cB wceq cA cB cpr cA csn cC cA cB wceq cA csn cA cA cpr cA cB
      cpr cA dfsn2 cA cB cA preq2 syl5req eqeq1d cA csn cC eqcom syl6bb pm5.32i
      bitri 3bitri $.
  $}

  ${
    opeqpr.1 $e |- A e. _V $.
    opeqpr.2 $e |- B e. _V $.
    opeqpr.3 $e |- C e. _V $.
    opeqpr.4 $e |- D e. _V $.
    $( Equivalence for an ordered pair equal to an unordered pair.
       (Contributed by NM, 3-Jun-2008.) $)
    opeqpr $p |- ( <. A , B >. = { C , D }
  <-> ( ( C = { A } /\ D = { A , B } ) \/ ( C = { A , B } /\ D = { A } ) ) ) $=
      cA cB cop cC cD cpr wceq cC cD cpr cA cB cop wceq cC cD cpr cA csn cA cB
      cpr cpr wceq cC cA csn wceq cD cA cB cpr wceq wa cC cA cB cpr wceq cD cA
      csn wceq wa wo cA cB cop cC cD cpr eqcom cA cB cop cA csn cA cB cpr cpr
      cC cD cpr cA cB opeqpr.1 opeqpr.2 dfop eqeq2i cC cD cA csn cA cB cpr
      opeqpr.3 opeqpr.4 cA snex cA cB prex preq12b 3bitri $.
  $}

  ${
    $d x y z A $.
    $( "At most one" remains true inside ordered pair quantification.
       (Contributed by NM, 28-Aug-2007.) $)
    mosubopt $p |- ( A. y A. z E* x ph ->
                 E* x E. y E. z ( A = <. y , z >. /\ ph ) ) $=
      wph vx wmo vz wal vy wal cA vy cv vz cv cop wceq vz wex vy wex cA vy cv
      vz cv cop wceq wph wa vz wex vy wex vx wmo wph vx wmo vz wal vy wal cA vy
      cv vz cv cop wceq vz wex cA vy cv vz cv cop wceq wph wa vz wex vy wex vx
      wmo vy wph vx wmo vz wal vy nfa1 cA vy cv vz cv cop wceq wph wa vz wex vy
      wex vy vx cA vy cv vz cv cop wceq wph wa vz wex vy nfe1 nfmo wph vx wmo
      vz wal cA vy cv vz cv cop wceq vz wex cA vy cv vz cv cop wceq wph wa vz
      wex vy wex vx wmo wi vy wph vx wmo vz wal cA vy cv vz cv cop wceq cA vy
      cv vz cv cop wceq wph wa vz wex vy wex vx wmo vz wph vx wmo vz nfa1 cA vy
      cv vz cv cop wceq wph wa vz wex vy wex vz vx cA vy cv vz cv cop wceq wph
      wa vz wex vz vy cA vy cv vz cv cop wceq wph wa vz nfe1 nfex nfmo wph vx
      wmo cA vy cv vz cv cop wceq cA vy cv vz cv cop wceq wph wa vz wex vy wex
      vx wmo wi vz cA vy cv vz cv cop wceq wph vx wmo cA vy cv vz cv cop wceq
      wph wa vz wex vy wex vx wmo cA vy cv vz cv cop wceq wph cA vy cv vz cv
      cop wceq wph wa vz wex vy wex vx wph vy vz cA copsexg mobidv biimpcd sps
      exlimd sps exlimd cA vy cv vz cv cop wceq vz wex vy wex wn cA vy cv vz cv
      cop wceq wph wa vz wex vy wex vx wex wn cA vy cv vz cv cop wceq wph wa vz
      wex vy wex vx wmo cA vy cv vz cv cop wceq wph wa vz wex vy wex vx wex cA
      vy cv vz cv cop wceq vz wex vy wex cA vy cv vz cv cop wceq wph wa vz wex
      vy wex cA vy cv vz cv cop wceq vz wex vy wex vx cA vy cv vz cv cop wceq
      wph wa cA vy cv vz cv cop wceq vy vz cA vy cv vz cv cop wceq wph simpl
      2eximi exlimiv con3i cA vy cv vz cv cop wceq wph wa vz wex vy wex vx wex
      cA vy cv vz cv cop wceq wph wa vz wex vy wex vx wmo cA vy cv vz cv cop
      wceq wph wa vz wex vy wex vx exmo ori syl pm2.61d1 $.
  $}

  ${
    $d x y z A $.
    mosubop.1 $e |- E* x ph $.
    $( "At most one" remains true inside ordered pair quantification.
       (Contributed by NM, 28-May-1995.) $)
    mosubop $p |- E* x E. y E. z ( A = <. y , z >. /\ ph ) $=
      wph vx wmo vz wal vy wal cA vy cv vz cv cop wceq wph wa vz wex vy wex vx
      wmo wph vx wmo vy vz mosubop.1 gen2 wph vx vy vz cA mosubopt ax-mp $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x y $.
    euop2.1 $e |- A e. _V $.
    $( Transfer existential uniqueness to second member of an ordered pair.
       (Contributed by NM, 10-Apr-2004.) $)
    euop2 $p |- ( E! x E. y ( x = <. A , y >. /\ ph ) <-> E! y ph ) $=
      wph vx vy cA vy cv cop cA vy cv opex vy vx cv cA euop2.1 moop2 euxfr2 $.
  $}

  ${
    $d a b c x y A $.  $d a b c x y B $.  $d a b c x y C $.  $d a b c x ph $.
    $d y ps $.
    euotd.1 $e |- ( ph -> A e. _V ) $.
    euotd.2 $e |- ( ph -> B e. _V ) $.
    euotd.3 $e |- ( ph -> C e. _V ) $.
    euotd.4 $e |- ( ph -> ( ps <-> ( a = A /\ b = B /\ c = C ) ) ) $.
    $( Prove existential uniqueness for an ordered triple.  (Contributed by
       Mario Carneiro, 20-May-2015.) $)
    euotd $p |- ( ph -> E! x E. a E. b E. c ( x = <. a , b , c >. /\ ps ) ) $=
      wph vx cv va cv vb cv vc cv cotp wceq wps wa vc wex vb wex va wex vx cv
      vy cv wceq wb vx wal vy wex vx cv va cv vb cv vc cv cotp wceq wps wa vc
      wex vb wex va wex vx weu wph vx cv va cv vb cv vc cv cotp wceq wps wa vc
      wex vb wex va wex vx cv cA cB cC cotp wceq wb vx wal vx cv va cv vb cv vc
      cv cotp wceq wps wa vc wex vb wex va wex vx cv vy cv wceq wb vx wal vy
      wex wph vx cv va cv vb cv vc cv cotp wceq wps wa vc wex vb wex va wex vx
      cv cA cB cC cotp wceq wb vx wph vx cv va cv vb cv vc cv cotp wceq wps wa
      vc wex vb wex va wex vx cv cA cB cC cotp wceq wph vx cv va cv vb cv vc cv
      cotp wceq wps wa vc wex vx cv cA cB cC cotp wceq va vb wph vx cv va cv vb
      cv vc cv cotp wceq wps wa vx cv cA cB cC cotp wceq vc wph vx cv va cv vb
      cv vc cv cotp wceq wps vx cv cA cB cC cotp wceq wph wps vx cv va cv vb cv
      vc cv cotp wceq vx cv cA cB cC cotp wceq wph wps wa vx cv va cv vb cv vc
      cv cotp wceq vx cv cA cB cC cotp wceq wph wps wa va cv vb cv vc cv cotp
      cA cB cC cotp vx cv wph wps wa va cv cA wceq vb cv cB wceq vc cv cC wceq
      w3a va cv vb cv vc cv cotp cA cB cC cotp wceq wph wps va cv cA wceq vb cv
      cB wceq vc cv cC wceq w3a euotd.4 biimpa va cv vb cv cA cB vc cv cC va
      vex vb vex vc vex otth sylibr eqeq2d biimpd impancom expimpd exlimdv
      exlimdvv wph vx cv va cv vb cv vc cv cotp wceq wps wa vc wex vb wex va
      wex vx cv cA cB cC cotp wceq cA cB cC cotp va cv vb cv vc cv cotp wceq
      wps wa vc wex vb wex va wex wph cA cB cC cotp va cv vb cv vc cv cotp wceq
      wps wa va wex vb wex vc wex cA cB cC cotp va cv vb cv vc cv cotp wceq wps
      wa vc wex vb wex va wex wph cC cvv wcel cA cB cC cotp va cv vb cv vc cv
      cotp wceq wps wa vc cC wsbc va wex vb wex cA cB cC cotp va cv vb cv vc cv
      cotp wceq wps wa va wex vb wex vc wex euotd.3 wph cB cvv wcel cA cB cC
      cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB wsbc va wex cA
      cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc va wex vb wex
      euotd.2 wph cA cvv wcel cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa
      vc cC wsbc vb cB wsbc va cA wsbc cA cB cC cotp va cv vb cv vc cv cotp
      wceq wps wa vc cC wsbc vb cB wsbc va wex euotd.1 wph cA cB cC cotp va cv
      vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB wsbc va cA wsbc wtru tru
      wph cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB
      wsbc wtru va cA cvv euotd.1 wph va cv cA wceq wa cA cB cC cotp va cv vb
      cv vc cv cotp wceq wps wa vc cC wsbc wtru vb cB cvv wph cB cvv wcel va cv
      cA wceq euotd.2 adantr wph va cv cA wceq wa vb cv cB wceq wa cA cB cC
      cotp va cv vb cv vc cv cotp wceq wps wa wtru vc cC cvv wph cC cvv wcel va
      cv cA wceq vb cv cB wceq euotd.3 ad2antrr wph va cv cA wceq vb cv cB wceq
      vc cv cC wceq cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa wtru wb
      wph va cv cA wceq vb cv cB wceq vc cv cC wceq cA cB cC cotp va cv vb cv
      vc cv cotp wceq wps wa wtru wb wph va cv cA wceq vb cv cB wceq vc cv cC
      wceq w3a wa cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa wtru wph va
      cv cA wceq vb cv cB wceq vc cv cC wceq w3a wa cA cB cC cotp va cv vb cv
      vc cv cotp wceq wps wph va cv cA wceq vb cv cB wceq vc cv cC wceq w3a wa
      va cv vb cv vc cv cotp cA cB cC cotp wph va cv cA wceq vb cv cB wceq vc
      cv cC wceq w3a wa va cv cA wceq vb cv cB wceq vc cv cC wceq w3a va cv vb
      cv vc cv cotp cA cB cC cotp wceq wph va cv cA wceq vb cv cB wceq vc cv cC
      wceq w3a simpr va cv vb cv cA cB vc cv cC va vex vb vex vc vex otth
      sylibr eqcomd wph wps va cv cA wceq vb cv cB wceq vc cv cC wceq w3a
      euotd.4 biimpar jca wph va cv cA wceq vb cv cB wceq vc cv cC wceq w3a wa
      a1tru 2thd 3exp2 imp41 sbcied sbcied sbcied mpbiri cA cB cC cotp va cv vb
      cv vc cv cotp wceq wps wa vc cC wsbc vb cB wsbc cA cB cC cotp va cv vb cv
      vc cv cotp wceq wps wa vc cC wsbc vb cB wsbc va cA wsbc va cA cvv va cA
      nfcv cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB
      wsbc va cA nfsbc1v cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC
      wsbc vb cB wsbc va cA sbceq1a spcegf sylc cA cB cC cotp va cv vb cv vc cv
      cotp wceq wps wa vc cC wsbc va wex cA cB cC cotp va cv vb cv vc cv cotp
      wceq wps wa vc cC wsbc vb cB wsbc va wex vb cB cvv vb cB nfcv cA cB cC
      cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB wsbc vb va cA cB
      cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB nfsbc1v nfex
      vb cv cB wceq cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc
      cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB wsbc va
      cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc vb cB sbceq1a
      exbidv spcegf sylc cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa va
      wex vb wex cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC wsbc va
      wex vb wex vc cC cvv vc cC nfcv cA cB cC cotp va cv vb cv vc cv cotp wceq
      wps wa vc cC wsbc va wex vc vb cA cB cC cotp va cv vb cv vc cv cotp wceq
      wps wa vc cC wsbc vc va cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa
      vc cC nfsbc1v nfex nfex vc cv cC wceq cA cB cC cotp va cv vb cv vc cv
      cotp wceq wps wa cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC
      wsbc vb va cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc cC sbceq1a
      2exbidv spcegf sylc cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa vc
      vb va excom13 sylib vx cv cA cB cC cotp wceq vx cv va cv vb cv vc cv cotp
      wceq wps wa cA cB cC cotp va cv vb cv vc cv cotp wceq wps wa va vb vc vx
      cv cA cB cC cotp wceq vx cv va cv vb cv vc cv cotp wceq cA cB cC cotp va
      cv vb cv vc cv cotp wceq wps vx cv cA cB cC cotp va cv vb cv vc cv cotp
      eqeq1 anbi1d 3exbidv syl5ibrcom impbid alrimiv vx cv va cv vb cv vc cv
      cotp wceq wps wa vc wex vb wex va wex vx cv vy cv wceq wb vx wal vx cv va
      cv vb cv vc cv cotp wceq wps wa vc wex vb wex va wex vx cv cA cB cC cotp
      wceq wb vx wal vy cA cB cC cotp cA cB cC otex vy cv cA cB cC cotp wceq vx
      cv va cv vb cv vc cv cotp wceq wps wa vc wex vb wex va wex vx cv vy cv
      wceq wb vx cv va cv vb cv vc cv cotp wceq wps wa vc wex vb wex va wex vx
      cv cA cB cC cotp wceq wb vx vy cv cA cB cC cotp wceq vx cv vy cv wceq vx
      cv cA cB cC cotp wceq vx cv va cv vb cv vc cv cotp wceq wps wa vc wex vb
      wex va wex vy cv cA cB cC cotp vx cv eqeq2 bibi2d albidv spcev syl vx cv
      va cv vb cv vc cv cotp wceq wps wa vc wex vb wex va wex vx vy df-eu
      sylibr $.
  $}

  ${
    opthw.1 $e |- A e. _V $.
    opthw.2 $e |- B e. _V $.
    $( Justification theorem for the ordered pair definition in Norbert Wiener,
       "A simplification of the logic of relations," _Proc. of the Cambridge
       Philos.  Soc_., 1914, vol. 17, pp.387-390.  It is also shown as a
       definition in [Enderton] p. 36 and as Exercise 4.8(b) of [Mendelson]
       p. 230.  It is meaningful only for classes that exist as sets (i.e. are
       not proper classes).  See ~ df-op for other ordered pair definitions.
       (Contributed by NM, 28-Sep-2003.) $)
    opthwiener $p |- ( { { { A } , (/) } , { { B } } } =
                    { { { C } , (/) } , { { D } } } <-> ( A = C /\ B = D ) ) $=
      cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr wceq cA cC wceq
      cB cD wceq wa cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr
      wceq cA cC wceq cB cD wceq cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD
      csn csn cpr wceq cA csn cC csn wceq cA cC wceq cA csn c0 cpr cB csn csn
      cpr cC csn c0 cpr cD csn csn cpr wceq cA csn c0 cpr cC csn c0 cpr wceq cA
      csn cC csn wceq cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr
      wceq cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cB csn csn cpr wceq cA
      csn c0 cpr cC csn c0 cpr wceq cA csn c0 cpr cB csn csn cpr cC csn c0 cpr
      cD csn csn cpr wceq cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn
      cpr cC csn c0 cpr cB csn csn cpr cA csn c0 cpr cB csn csn cpr cC csn c0
      cpr cD csn csn cpr wceq id cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD
      csn csn cpr wceq cB csn csn cD csn csn cC csn c0 cpr cA csn c0 cpr cB csn
      csn cpr cC csn c0 cpr cD csn csn cpr wceq cB csn csn cC csn c0 cpr wceq
      cB csn csn cD csn csn wceq wo cB csn csn cD csn csn wceq cA csn c0 cpr cB
      csn csn cpr cC csn c0 cpr cD csn csn cpr wceq cB csn csn cC csn c0 cpr cD
      csn csn cpr wcel cB csn csn cC csn c0 cpr wceq cB csn csn cD csn csn wceq
      wo cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr wceq cB csn
      csn cA csn c0 cpr cB csn csn cpr wcel cB csn csn cC csn c0 cpr cD csn csn
      cpr wcel cA csn c0 cpr cB csn csn cB csn snex prid2 cA csn c0 cpr cB csn
      csn cpr cC csn c0 cpr cD csn csn cpr cB csn csn eleq2 mpbii cB csn csn cC
      csn c0 cpr cD csn csn cB csn snex elpr sylib cB csn csn cC csn c0 cpr
      wceq wn cB csn csn cD csn csn wceq cB csn csn cC csn c0 cpr wceq cB csn
      csn cD csn csn wceq wo wb cC csn c0 cpr cB csn csn wceq cB csn csn cC csn
      c0 cpr wceq c0 cC csn c0 cpr wcel c0 cB csn csn wcel wn cC csn c0 cpr cB
      csn csn wceq wn cC csn c0 0ex prid2 c0 cB csn csn wcel cB csn c0 cB
      opthw.2 snnz c0 cB csn csn wcel c0 cB csn wceq cB csn c0 wceq c0 cB csn
      0ex elsnc c0 cB csn eqcom bitri nemtbir c0 cC csn c0 cpr cB csn csn
      nelneq2 mp2an cC csn c0 cpr cB csn csn eqcom mtbi cB csn csn cC csn c0
      cpr wceq cB csn csn cD csn csn wceq biorf ax-mp sylibr preq2d eqtr4d cA
      csn c0 cpr cC csn c0 cpr cB csn csn cA csn c0 prex cC csn c0 prex preqr1
      syl cA csn cC csn c0 cA snex cC snex preqr1 syl cA cC opthw.1 sneqr syl
      cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr wceq cB csn cD
      csn wceq cB cD wceq cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn
      cpr wceq cB csn csn cD csn csn wceq cB csn cD csn wceq cA csn c0 cpr cB
      csn csn cpr cC csn c0 cpr cD csn csn cpr wceq cB csn csn cC csn c0 cpr
      wceq cB csn csn cD csn csn wceq wo cB csn csn cD csn csn wceq cA csn c0
      cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr wceq cB csn csn cC csn c0
      cpr cD csn csn cpr wcel cB csn csn cC csn c0 cpr wceq cB csn csn cD csn
      csn wceq wo cA csn c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr
      wceq cB csn csn cA csn c0 cpr cB csn csn cpr wcel cB csn csn cC csn c0
      cpr cD csn csn cpr wcel cA csn c0 cpr cB csn csn cB csn snex prid2 cA csn
      c0 cpr cB csn csn cpr cC csn c0 cpr cD csn csn cpr cB csn csn eleq2 mpbii
      cB csn csn cC csn c0 cpr cD csn csn cB csn snex elpr sylib cB csn csn cC
      csn c0 cpr wceq wn cB csn csn cD csn csn wceq cB csn csn cC csn c0 cpr
      wceq cB csn csn cD csn csn wceq wo wb cC csn c0 cpr cB csn csn wceq cB
      csn csn cC csn c0 cpr wceq c0 cC csn c0 cpr wcel c0 cB csn csn wcel wn cC
      csn c0 cpr cB csn csn wceq wn cC csn c0 0ex prid2 c0 cB csn csn wcel cB
      csn c0 cB opthw.2 snnz c0 cB csn csn wcel c0 cB csn wceq cB csn c0 wceq
      c0 cB csn 0ex elsnc c0 cB csn eqcom bitri nemtbir c0 cC csn c0 cpr cB csn
      csn nelneq2 mp2an cC csn c0 cpr cB csn csn eqcom mtbi cB csn csn cC csn
      c0 cpr wceq cB csn csn cD csn csn wceq biorf ax-mp sylibr cB csn cD csn
      cB snex sneqr syl cB cD opthw.2 sneqr syl jca cA cC wceq cB cD wceq cA
      csn c0 cpr cB csn csn cpr cC csn c0 cpr cB csn csn cpr cC csn c0 cpr cD
      csn csn cpr cA cC wceq cA csn c0 cpr cC csn c0 cpr cB csn csn cA cC wceq
      cA csn cC csn c0 cA cC sneq preq1d preq1d cB cD wceq cB csn csn cD csn
      csn cC csn c0 cpr cB cD wceq cB csn cD csn wceq cB csn csn cD csn csn
      wceq cB cD sneq cB csn cD csn sneq syl preq2d sylan9eq impbii $.

    $( The union of an ordered pair.  Theorem 65 of [Suppes] p. 39.
       (Contributed by NM, 17-Aug-2004.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    uniop $p |- U. <. A , B >. = { A , B } $=
      cA cB cop cuni cA csn cA cB cpr cpr cuni cA csn cA cB cpr cun cA cB cpr
      cA cB cop cA csn cA cB cpr cpr cA cB opthw.1 opthw.2 dfop unieqi cA csn
      cA cB cpr cA snex cA cB prex unipr cA csn cA cB cpr wss cA csn cA cB cpr
      cun cA cB cpr wceq cA cB snsspr1 cA csn cA cB cpr ssequn1 mpbi 3eqtri $.

    $( Ordered pair membership is inherited by class union.  (Contributed by
       NM, 13-May-2008.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    uniopel $p |- ( <. A , B >. e. C -> U. <. A , B >. e. U. C ) $=
      cA cB cop cC wcel cA cB cop cuni cA cB cop wcel cA cB cop cuni cC cuni
      wcel cA cB cop cuni cA cB cpr cA cB cop cA cB opthw.1 opthw.2 uniop cA cB
      opthw.1 opthw.2 opi2 eqeltri cA cB cop cC wcel cA cB cop cC cuni cA cB
      cop cuni cA cB cop cC elssuni sseld mpi $.
  $}


