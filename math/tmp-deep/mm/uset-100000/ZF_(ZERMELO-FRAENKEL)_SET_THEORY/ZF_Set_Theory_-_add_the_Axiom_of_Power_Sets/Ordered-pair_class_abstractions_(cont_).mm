
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Ordered_pair_theorem.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                Ordered-pair class abstractions (cont.)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z w v $.  $d y z w v $.  $d ph z w v $.
    $( The law of concretion.  Special case of Theorem 9.5 of [Quine] p. 61.
       (Contributed by NM, 14-Apr-1995.)  (Proof shortened by Andrew Salmon,
       25-Jul-2011.) $)
    opabid $p |- ( <. x , y >. e. { <. x , y >. | ph } <-> ph ) $=
      vz cv vx cv vy cv cop wceq wph wa vy wex vx wex wph vz vx cv vy cv cop
      wph vx vy copab vx cv vy cv opex vz cv vx cv vy cv cop wceq wph vz cv vx
      cv vy cv cop wceq wph wa vy wex vx wex wph vx vy vz cv copsexg bicomd wph
      vx vy vz df-opab elab2 $.
  $}

  ${
    $d x z A $.  $d y z A $.  $d z ph $.
    $( Membership in a class abstraction of pairs.  (Contributed by NM,
       24-Mar-1998.) $)
    elopab $p |- ( A e. { <. x , y >. | ph } <->
                 E. x E. y ( A = <. x , y >. /\ ph ) ) $=
      cA wph vx vy copab wcel cA cvv wcel cA vx cv vy cv cop wceq wph wa vy wex
      vx wex cA wph vx vy copab elex cA vx cv vy cv cop wceq wph wa cA cvv wcel
      vx vy cA vx cv vy cv cop wceq cA cvv wcel wph cA vx cv vy cv cop wceq cA
      cvv wcel vx cv vy cv cop cvv wcel vx cv vy cv opex cA vx cv vy cv cop cvv
      eleq1 mpbiri adantr exlimivv vz cv vx cv vy cv cop wceq wph wa vy wex vx
      wex cA vx cv vy cv cop wceq wph wa vy wex vx wex vz cA wph vx vy copab
      cvv vz cv cA wceq vz cv vx cv vy cv cop wceq wph wa cA vx cv vy cv cop
      wceq wph wa vx vy vz cv cA wceq vz cv vx cv vy cv cop wceq cA vx cv vy cv
      cop wceq wph vz cv cA vx cv vy cv cop eqeq1 anbi1d 2exbidv wph vx vy vz
      df-opab elab2g pm5.21nii $.
  $}

  ${
    $d x y z v $.  $d x y w v $.  $d v ph $.
    $( The law of concretion in terms of substitutions.  (Contributed by NM,
       30-Sep-2002.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.)
       (New usage is discouraged.) $)
    opelopabsbOLD $p |- ( <. z , w >. e. { <. x , y >. | ph }
                 <-> [ w / y ] [ z / x ] ph ) $=
      vz cv vw cv cop vx cv vy cv cop wceq wph wa vy wex vx wex vy cv vw cv
      wceq vx cv vz cv wceq wa wph wa vx wex vy wex vz cv vw cv cop wph vx vy
      copab wcel wph vx vz wsb vy vw wsb vz cv vw cv cop vx cv vy cv cop wceq
      wph wa vy wex vx wex vz cv vw cv cop vx cv vy cv cop wceq wph wa vx wex
      vy wex vy cv vw cv wceq vx cv vz cv wceq wa wph wa vx wex vy wex vz cv vw
      cv cop vx cv vy cv cop wceq wph wa vx vy excom vz cv vw cv cop vx cv vy
      cv cop wceq wph wa vy cv vw cv wceq vx cv vz cv wceq wa wph wa vy vx vz
      cv vw cv cop vx cv vy cv cop wceq vy cv vw cv wceq vx cv vz cv wceq wa
      wph vz cv vw cv cop vx cv vy cv cop wceq vz cv vx cv wceq vw cv vy cv
      wceq wa vy cv vw cv wceq vx cv vz cv wceq wa vz cv vw cv vx cv vy cv vz
      vex vw vex opth vz cv vx cv wceq vx cv vz cv wceq vw cv vy cv wceq vy cv
      vw cv wceq vz vx equcom vw vy equcom anbi12ci bitri anbi1i 2exbii bitri
      wph vx vy vz cv vw cv cop elopab wph vy vx vw vz 2sb5 3bitr4i $.

    brabsbOLD.1 $e |- R = { <. x , y >. | ph } $.
    $( The law of concretion in terms of substitutions.  (Contributed by NM,
       17-Mar-2008.)  (New usage is discouraged.) $)
    brabsbOLD $p |- ( z R w <-> [ w / y ] [ z / x ] ph ) $=
      vz cv vw cv cR wbr vz cv vw cv wph vx vy copab wbr vz cv vw cv cop wph vx
      vy copab wcel wph vx vz wsb vy vw wsb vz cv vw cv cR wph vx vy copab
      brabsbOLD.1 breqi vz cv vw cv wph vx vy copab df-br wph vx vy vz vw
      opelopabsbOLD 3bitri $.
  $}

  ${
    $d x y z w $.  $d w z A $.  $d w x B $.  $d w z ph $.
    $( The law of concretion in terms of substitutions.  (Contributed by NM,
       30-Sep-2002.)  (Revised by Mario Carneiro, 18-Nov-2016.) $)
    opelopabsb $p |- ( <. A , B >. e. { <. x , y >. | ph }
                 <-> [. A / x ]. [. B / y ]. ph ) $=
      cA cB cop wph vx vy copab wcel cA cvv wcel cB cvv wcel wa wph vy cB wsbc
      vx cA wsbc cA cB cop wph vx vy copab wcel cA cB cop c0 wne cA cvv wcel cB
      cvv wcel wa cA cB cop wph vx vy copab wcel cA cB cop c0 cA cB cop c0 wceq
      cA cB cop wph vx vy copab wcel c0 wph vx vy copab wcel c0 wph vx vy copab
      wcel c0 vx cv vy cv cop wceq wph wa vy wex vx wex c0 vx cv vy cv cop wceq
      wph wa vy wex vx c0 vx cv vy cv cop wceq wph wa vy vx cv vy cv cop c0 wne
      c0 vx cv vy cv cop wceq wph wa wn vx cv vy cv vx vex vy vex opnzi c0 vx
      cv vy cv cop wceq wph wa vx cv vy cv cop c0 c0 vx cv vy cv cop wceq wph
      wa c0 vx cv vy cv cop c0 vx cv vy cv cop wceq wph simpl eqcomd necon3ai
      ax-mp nex nex wph vx vy c0 elopab mtbir cA cB cop c0 wph vx vy copab
      eleq1 mtbiri necon2ai cA cB opnz sylib wph vy cB wsbc vx cA wsbc cA cvv
      wcel cB cvv wcel wph vy cB wsbc vx cA sbcex wph vy cB wsbc vx cA wsbc wph
      vy cB wsbc vx wex cB cvv wcel wph vy cB wsbc vx cA spesbc wph vy cB wsbc
      cB cvv wcel vx wph vy cB sbcex exlimiv syl jca vz cv vw cv cop wph vx vy
      copab wcel wph vy vw wsb vx vz wsb wb cA vw cv cop wph vx vy copab wcel
      wph vy vw wsb vx cA wsbc wb cA cB cop wph vx vy copab wcel wph vy cB wsbc
      vx cA wsbc wb vz vw cA cB cvv cvv vz cv cA wceq vz cv vw cv cop wph vx vy
      copab wcel cA vw cv cop wph vx vy copab wcel wph vy vw wsb vx vz wsb wph
      vy vw wsb vx cA wsbc vz cv cA wceq vz cv vw cv cop cA vw cv cop wph vx vy
      copab vz cv cA vw cv opeq1 eleq1d wph vy vw wsb vx vz cA dfsbcq2 bibi12d
      vw cv cB wceq cA vw cv cop wph vx vy copab wcel cA cB cop wph vx vy copab
      wcel wph vy vw wsb vx cA wsbc wph vy cB wsbc vx cA wsbc vw cv cB wceq cA
      vw cv cop cA cB cop wph vx vy copab vw cv cB cA opeq2 eleq1d vw cv cB
      wceq wph vy vw wsb wph vy cB wsbc vx cA wph vy vw cB dfsbcq2 sbcbidv
      bibi12d vx cv vw cv cop wph vx vy copab wcel wph vy vw wsb wb vz cv vw cv
      cop wph vx vy copab wcel wph vy vw wsb vx vz wsb wb vx vz vz cv vw cv cop
      wph vx vy copab wcel wph vy vw wsb vx vz wsb vx vx vz cv vw cv cop wph vx
      vy copab wph vx vy nfopab1 nfel2 wph vy vw wsb vx vz nfs1v nfbi vx vz weq
      vx cv vw cv cop wph vx vy copab wcel vz cv vw cv cop wph vx vy copab wcel
      wph vy vw wsb wph vy vw wsb vx vz wsb vx vz weq vx cv vw cv cop vz cv vw
      cv cop wph vx vy copab vx cv vz cv vw cv opeq1 eleq1d wph vy vw wsb vx vz
      sbequ12 bibi12d vx cv vy cv cop wph vx vy copab wcel wph wb vx cv vw cv
      cop wph vx vy copab wcel wph vy vw wsb wb vy vw vx cv vw cv cop wph vx vy
      copab wcel wph vy vw wsb vy vy vx cv vw cv cop wph vx vy copab wph vx vy
      nfopab2 nfel2 wph vy vw nfs1v nfbi vy vw weq vx cv vy cv cop wph vx vy
      copab wcel vx cv vw cv cop wph vx vy copab wcel wph wph vy vw wsb vy vw
      weq vx cv vy cv cop vx cv vw cv cop wph vx vy copab vy cv vw cv vx cv
      opeq2 eleq1d wph vy vw sbequ12 bibi12d wph vx vy opabid chvar chvar
      vtocl2g pm5.21nii $.

    brabsb.1 $e |- R = { <. x , y >. | ph } $.
    $( The law of concretion in terms of substitutions.  (Contributed by NM,
       17-Mar-2008.) $)
    brabsb $p |- ( A R B <-> [. A / x ]. [. B / y ]. ph ) $=
      cA cB cR wbr cA cB cop cR wcel cA cB cop wph vx vy copab wcel wph vy cB
      wsbc vx cA wsbc cA cB cR df-br cR wph vx vy copab cA cB cop brabsb.1
      eleq2i wph vx vy cA cB opelopabsb 3bitri $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y ch $.  $d z ph $.
    $( Closed theorem form of ~ opelopab .  (Contributed by NM,
       19-Feb-2013.) $)
    opelopabt $p |- ( ( A. x A. y ( x = A -> ( ph <-> ps ) )
                     /\ A. x A. y ( y = B -> ( ps <-> ch ) )
                     /\ ( A e. V /\ B e. W ) ) ->
                    ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) ) $=
      cA cB cop wph vx vy copab wcel cA cB cop vx cv vy cv cop wceq wph wa vy
      wex vx wex vx cv cA wceq wph wps wb wi vy wal vx wal vy cv cB wceq wps
      wch wb wi vy wal vx wal cA cV wcel cB cW wcel wa w3a wch wph vx vy cA cB
      cop elopab vx cv cA wceq wph wps wb wi vy wal vx wal vy cv cB wceq wps
      wch wb wi vy wal vx wal cA cV wcel cB cW wcel wa cA cB cop vx cv vy cv
      cop wceq wph wa vy wex vx wex wch wb vx cv cA wceq wph wps wb wi vy wal
      vx wal vy cv cB wceq wps wch wb wi vy wal vx wal wa vx cv cA wceq vy cv
      cB wceq wa wph wch wb wi vy wal vx wal cA cV wcel cB cW wcel wa cA cB cop
      vx cv vy cv cop wceq wph wa vy wex vx wex wch wb vx cv cA wceq wph wps wb
      wi vy wal vx wal vy cv cB wceq wps wch wb wi vy wal vx wal wa vx cv cA
      wceq wph wps wb wi vy cv cB wceq wps wch wb wi wa vy wal vx wal vx cv cA
      wceq vy cv cB wceq wa wph wch wb wi vy wal vx wal vx cv cA wceq wph wps
      wb wi vy cv cB wceq wps wch wb wi vx vy 19.26-2 vx cv cA wceq wph wps wb
      wi vy cv cB wceq wps wch wb wi wa vx cv cA wceq vy cv cB wceq wa wph wch
      wb wi vx vy vx cv cA wceq wph wps wb wi vy cv cB wceq wps wch wb wi wa vx
      cv cA wceq vy cv cB wceq wa wph wps wb wps wch wb wa wph wch wb vx cv cA
      wceq wph wps wb vy cv cB wceq wps wch wb prth wph wps wch bitr syl6
      2alimi sylbir wph wch vx vy cA cB cV cW copsex2t sylan 3impa syl5bb $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ps $.
    opelopabga.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       Mario Carneiro, 19-Dec-2013.) $)
    opelopabga $p |- ( ( A e. V /\ B e. W ) ->
                    ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) ) $=
      cA cB cop wph vx vy copab wcel cA cB cop vx cv vy cv cop wceq wph wa vy
      wex vx wex cA cV wcel cB cW wcel wa wps wph vx vy cA cB cop elopab wph
      wps vx vy cA cB cV cW opelopabga.1 copsex2g syl5bb $.

    ${
      brabga.2 $e |- R = { <. x , y >. | ph } $.
      $( The law of concretion for a binary relation.  (Contributed by Mario
         Carneiro, 19-Dec-2013.) $)
      brabga $p |- ( ( A e. V /\ B e. W ) -> ( A R B <-> ps ) ) $=
        cA cB cR wbr cA cB cop wph vx vy copab wcel cA cV wcel cB cW wcel wa
        wps cA cB cR wbr cA cB cop cR wcel cA cB cop wph vx vy copab wcel cA cB
        cR df-br cR wph vx vy copab cA cB cop brabga.2 eleq2i bitri wph wps vx
        vy cA cB cV cW opelopabga.1 opelopabga syl5bb $.
    $}

    $d x y C $.  $d x y D $.
    $( Ordered pair membership in an ordered pair class abstraction.
       (Contributed by Mario Carneiro, 19-Dec-2013.) $)
    opelopab2a $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e.
                 { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ps ) ) $=
      cA cC wcel cB cD wcel wa cA cB cop vx cv cC wcel vy cv cD wcel wa wph wa
      vx vy copab wcel wps vx cv cC wcel vy cv cD wcel wa wph wa cA cC wcel cB
      cD wcel wa wps wa vx vy cA cB cC cD vx cv cA wceq vy cv cB wceq wa vx cv
      cC wcel vy cv cD wcel wa cA cC wcel cB cD wcel wa wph wps vx cv cA wceq
      vx cv cC wcel cA cC wcel vy cv cB wceq vy cv cD wcel cB cD wcel vx cv cA
      cC eleq1 vy cv cB cD eleq1 bi2anan9 opelopabga.1 anbi12d opelopabga
      bianabs $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ps $.
    opelopaba.1 $e |- A e. _V $.
    opelopaba.2 $e |- B e. _V $.
    opelopaba.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       Mario Carneiro, 19-Dec-2013.) $)
    opelopaba $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) $=
      cA cvv wcel cB cvv wcel cA cB cop wph vx vy copab wcel wps wb opelopaba.1
      opelopaba.2 wph wps vx vy cA cB cvv cvv opelopaba.3 opelopabga mp2an $.

    ${
      braba.4 $e |- R = { <. x , y >. | ph } $.
      $( The law of concretion for a binary relation.  (Contributed by NM,
         19-Dec-2013.) $)
      braba $p |- ( A R B <-> ps ) $=
        cA cvv wcel cB cvv wcel cA cB cR wbr wps wb opelopaba.1 opelopaba.2 wph
        wps vx vy cA cB cR cvv cvv opelopaba.3 braba.4 brabga mp2an $.
    $}
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ch $.
    opelopabg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    opelopabg.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       NM, 28-May-1995.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)
    opelopabg $p |- ( ( A e. V /\ B e. W ) ->
                    ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) ) $=
      wph wch vx vy cA cB cV cW vx cv cA wceq wph wps vy cv cB wceq wch
      opelopabg.1 opelopabg.2 sylan9bb opelopabga $.

    ${
      brabg.5 $e |- R = { <. x , y >. | ph } $.
      $( The law of concretion for a binary relation.  (Contributed by NM,
         16-Aug-1999.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)
      brabg $p |- ( ( A e. C /\ B e. D ) -> ( A R B <-> ch ) ) $=
        wph wch vx vy cA cB cR cC cD vx cv cA wceq wph wps vy cv cB wceq wch
        opelopabg.1 opelopabg.2 sylan9bb brabg.5 brabga $.
    $}
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y ch $.
    opelopab2.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    opelopab2.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( Ordered pair membership in an ordered pair class abstraction.
       (Contributed by NM, 14-Oct-2007.)  (Revised by Mario Carneiro,
       19-Dec-2013.) $)
    opelopab2 $p |- ( ( A e. C /\ B e. D ) -> ( <. A , B >. e.
                 { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } <-> ch ) ) $=
      wph wch vx vy cA cB cC cD vx cv cA wceq wph wps vy cv cB wceq wch
      opelopab2.1 opelopab2.2 sylan9bb opelopab2a $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ch $.
    opelopab.1 $e |- A e. _V $.
    opelopab.2 $e |- B e. _V $.
    opelopab.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    opelopab.4 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  (Contributed by
       NM, 16-May-1995.) $)
    opelopab $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) $=
      cA cvv wcel cB cvv wcel cA cB cop wph vx vy copab wcel wch wb opelopab.1
      opelopab.2 wph wps wch vx vy cA cB cvv cvv opelopab.3 opelopab.4
      opelopabg mp2an $.

    ${
      brab.5 $e |- R = { <. x , y >. | ph } $.
      $( The law of concretion for a binary relation.  (Contributed by NM,
         16-Aug-1999.) $)
      brab $p |- ( A R B <-> ch ) $=
        cA cvv wcel cB cvv wcel cA cB cR wbr wch wb opelopab.1 opelopab.2 wph
        wps wch vx vy cA cB cvv cvv cR opelopab.3 opelopab.4 brab.5 brabg mp2an
        $.
    $}
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w z ph $.  $d w z ps $.
    opelopabaf.x $e |- F/ x ps $.
    opelopabaf.y $e |- F/ y ps $.
    opelopabaf.1 $e |- A e. _V $.
    opelopabaf.2 $e |- B e. _V $.
    opelopabaf.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  This version of
       ~ opelopab uses bound-variable hypotheses in place of distinct variable
       conditions."  (Contributed by Mario Carneiro, 19-Dec-2013.)  (Proof
       shortened by Mario Carneiro, 18-Nov-2016.) $)
    opelopabaf $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ps ) $=
      cA cB cop wph vx vy copab wcel wph vy cB wsbc vx cA wsbc wps wph vx vy cA
      cB opelopabsb cA cvv wcel cB cvv wcel wph vy cB wsbc vx cA wsbc wps wb
      opelopabaf.1 opelopabaf.2 wph wps vx vy cA cB cvv cvv opelopabaf.x
      opelopabaf.y cB cvv wcel vx nfv opelopabaf.3 sbc2iegf mp2an bitri $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w z ch $.  $d w z ph $.
    opelopabf.x $e |- F/ x ps $.
    opelopabf.y $e |- F/ y ch $.
    opelopabf.1 $e |- A e. _V $.
    opelopabf.2 $e |- B e. _V $.
    opelopabf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    opelopabf.4 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( The law of concretion.  Theorem 9.5 of [Quine] p. 61.  This version of
       ~ opelopab uses bound-variable hypotheses in place of distinct variable
       conditions."  (Contributed by NM, 19-Dec-2008.) $)
    opelopabf $p |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) $=
      cA cB cop wph vx vy copab wcel wph vy cB wsbc vx cA wsbc wps vy cB wsbc
      wch wph vx vy cA cB opelopabsb cA cvv wcel wph vy cB wsbc vx cA wsbc wps
      vy cB wsbc wb opelopabf.1 wph vy cB wsbc wps vy cB wsbc vx cA cvv wps vx
      vy cB vx cB nfcv opelopabf.x nfsbc vx cv cA wceq wph wps vy cB
      opelopabf.3 sbcbidv sbciegf ax-mp cB cvv wcel wps vy cB wsbc wch wb
      opelopabf.2 wps wch vy cB cvv opelopabf.y opelopabf.4 sbciegf ax-mp
      3bitri $.
  $}

  ${
    $d ph z $.  $d ps z $.  $d x z $.  $d y z $.
    $( Equivalence of ordered pair abstraction subclass and implication.
       (Contributed by NM, 27-Dec-1996.)  (Revised by Mario Carneiro,
       19-May-2013.) $)
    ssopab2 $p |- ( A. x A. y ( ph -> ps ) ->
        { <. x , y >. | ph } C_ { <. x , y >. | ps } ) $=
      wph wps wi vy wal vx wal vz cv vx cv vy cv cop wceq wph wa vy wex vx wex
      vz cab vz cv vx cv vy cv cop wceq wps wa vy wex vx wex vz cab wph vx vy
      copab wps vx vy copab wph wps wi vy wal vx wal vz cv vx cv vy cv cop wceq
      wph wa vy wex vx wex vz cv vx cv vy cv cop wceq wps wa vy wex vx wex vz
      wph wps wi vy wal vx wal vz cv vx cv vy cv cop wceq wph wa vy wex vz cv
      vx cv vy cv cop wceq wps wa vy wex vx wph wps wi vy wal vx nfa1 wph wps
      wi vy wal vz cv vx cv vy cv cop wceq wph wa vy wex vz cv vx cv vy cv cop
      wceq wps wa vy wex wi vx wph wps wi vy wal vz cv vx cv vy cv cop wceq wph
      wa vz cv vx cv vy cv cop wceq wps wa vy wph wps wi vy nfa1 wph wps wi vy
      wal wph wps vz cv vx cv vy cv cop wceq wph wps wi vy sp anim2d eximd sps
      eximd ss2abdv wph vx vy vz df-opab wps vx vy vz df-opab 3sstr4g $.
  $}

  ${
    $d ph z $.  $d ps z $.  $d x z $.  $d y z $.
    $( Equivalence of ordered pair abstraction subclass and implication.
       (Contributed by NM, 27-Dec-1996.)  (Proof shortened by Mario Carneiro,
       18-Nov-2016.) $)
    ssopab2b $p |- ( { <. x , y >. | ph } C_ { <. x , y >. | ps } <->
               A. x A. y ( ph -> ps ) ) $=
      wph vx vy copab wps vx vy copab wss wph wps wi vy wal vx wal wph vx vy
      copab wps vx vy copab wss wph wps wi vy wal vx vx wph vx vy copab wps vx
      vy copab wph vx vy nfopab1 wps vx vy nfopab1 nfss wph vx vy copab wps vx
      vy copab wss wph wps wi vy vy wph vx vy copab wps vx vy copab wph vx vy
      nfopab2 wps vx vy nfopab2 nfss wph vx vy copab wps vx vy copab wss vx cv
      vy cv cop wph vx vy copab wcel vx cv vy cv cop wps vx vy copab wcel wph
      wps wph vx vy copab wps vx vy copab vx cv vy cv cop ssel wph vx vy opabid
      wps vx vy opabid 3imtr3g alrimi alrimi wph wps vx vy ssopab2 impbii $.
  $}

  ${
    ssopab2i.1 $e |- ( ph -> ps ) $.
    $( Inference of ordered pair abstraction subclass from implication.
       (Contributed by NM, 5-Apr-1995.) $)
    ssopab2i $p |- { <. x , y >. | ph } C_ { <. x , y >. | ps } $=
      wph wps wi vy wal wph vx vy copab wps vx vy copab wss vx wph wps vx vy
      ssopab2 wph wps wi vy ssopab2i.1 ax-gen mpg $.
  $}

  ${
    $d x ph $.  $d y ph $.
    ssopab2dv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference of ordered pair abstraction subclass from implication.
       (Contributed by NM, 19-Jan-2014.)  (Revised by Mario Carneiro,
       24-Jun-2014.) $)
    ssopab2dv $p |- ( ph -> { <. x , y >. | ps } C_ { <. x , y >. | ch } ) $=
      wph wps wch wi vy wal vx wal wps vx vy copab wch vx vy copab wss wph wps
      wch wi vx vy ssopab2dv.1 alrimivv wps wch vx vy ssopab2 syl $.
  $}

  ${
    $d ph z $.  $d ps z $.  $d x z $.  $d y z $.
    $( Equivalence of ordered pair abstraction equality and biconditional.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    eqopab2b $p |- ( { <. x , y >. | ph } = { <. x , y >. | ps } <->
               A. x A. y ( ph <-> ps ) ) $=
      wph vx vy copab wps vx vy copab wss wps vx vy copab wph vx vy copab wss
      wa wph wps wi vy wal vx wal wps wph wi vy wal vx wal wa wph vx vy copab
      wps vx vy copab wceq wph wps wb vy wal vx wal wph vx vy copab wps vx vy
      copab wss wph wps wi vy wal vx wal wps vx vy copab wph vx vy copab wss
      wps wph wi vy wal vx wal wph wps vx vy ssopab2b wps wph vx vy ssopab2b
      anbi12i wph vx vy copab wps vx vy copab eqss wph wps vx vy 2albiim
      3bitr4i $.
  $}

  ${
    $d z ph $.  $d z x $.  $d z y $.
    $( Non-empty ordered pair class abstraction.  (Contributed by NM,
       10-Oct-2007.) $)
    opabn0 $p |- ( { <. x , y >. | ph } =/= (/) <-> E. x E. y ph ) $=
      wph vx vy copab c0 wne vz cv wph vx vy copab wcel vz wex wph vy wex vx
      wex vz wph vx vy copab n0 vz cv wph vx vy copab wcel vz wex vz cv vx cv
      vy cv cop wceq wph wa vy wex vx wex vz wex wph vy wex vx wex vz cv wph vx
      vy copab wcel vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz wph vx
      vy vz cv elopab exbii vz cv vx cv vy cv cop wceq wph wa vy wex vx wex vz
      wex vz cv vx cv vy cv cop wceq wph wa vz wex vy wex vx wex wph vy wex vx
      wex vz cv vx cv vy cv cop wceq wph wa vz vx vy exrot3 vz cv vx cv vy cv
      cop wceq wph wa vz wex wph vx vy vz cv vx cv vy cv cop wceq wph wa vz wex
      vz cv vx cv vy cv cop wceq vz wex wph vz vx cv vy cv cop vx cv vy cv opex
      isseti vz cv vx cv vy cv cop wceq wph vz 19.41v mpbiran 2exbii bitri
      bitri bitri $.
  $}

  ${
    $d ph w $.  $d A w x $.  $d A y $.  $d w y z $.  $d x z $.
    $( Move indexed union inside an ordered-pair abstraction.  (Contributed by
       Stefan O'Rear, 20-Feb-2015.) $)
    iunopab $p |- U_ z e. A { <. x , y >. | ph } =
        { <. x , y >. | E. z e. A ph } $=
      vw cv wph vx vy copab wcel vz cA wrex vw cab vw cv vx cv vy cv cop wceq
      wph vz cA wrex wa vy wex vx wex vw cab vz cA wph vx vy copab ciun wph vz
      cA wrex vx vy copab vw cv wph vx vy copab wcel vz cA wrex vw cv vx cv vy
      cv cop wceq wph vz cA wrex wa vy wex vx wex vw vw cv wph vx vy copab wcel
      vz cA wrex vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cA wrex vw
      cv vx cv vy cv cop wceq wph vz cA wrex wa vy wex vx wex vw cv wph vx vy
      copab wcel vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vz cA wph vx
      vy vw cv elopab rexbii vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vz
      cA wrex vw cv vx cv vy cv cop wceq wph wa vy wex vz cA wrex vx wex vw cv
      vx cv vy cv cop wceq wph vz cA wrex wa vy wex vx wex vw cv vx cv vy cv
      cop wceq wph wa vy wex vz vx cA rexcom4 vw cv vx cv vy cv cop wceq wph wa
      vy wex vz cA wrex vw cv vx cv vy cv cop wceq wph vz cA wrex wa vy wex vx
      vw cv vx cv vy cv cop wceq wph wa vy wex vz cA wrex vw cv vx cv vy cv cop
      wceq wph wa vz cA wrex vy wex vw cv vx cv vy cv cop wceq wph vz cA wrex
      wa vy wex vw cv vx cv vy cv cop wceq wph wa vz vy cA rexcom4 vw cv vx cv
      vy cv cop wceq wph wa vz cA wrex vw cv vx cv vy cv cop wceq wph vz cA
      wrex wa vy vw cv vx cv vy cv cop wceq wph vz cA r19.42v exbii bitri exbii
      bitri bitri abbii vz vw cA wph vx vy copab df-iun wph vz cA wrex vx vy vw
      df-opab 3eqtr4i $.
  $}


