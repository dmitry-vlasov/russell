
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Unordered_and_ordered_pairs.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                       The union of a class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare class union symbol. $)
  $c U. $. $( Big cup $)

  $( Extend class notation to include the union of a class (read:  'union
     ` A ` ') $)
  cuni $a class U. A $.

  ${
    $d x y A $.
    $( Define the union of a class i.e. the collection of all members of the
       members of the class.  Definition 5.5 of [TakeutiZaring] p. 16.  For
       example, ` U. { { 1 , 3 } , { 1 , 8 } } = { 1 , 3 , 8 } ` ( ~ ex-uni ).
       This is similar to the union of two classes ~ df-un .  (Contributed by
       NM, 23-Aug-1993.) $)
    df-uni $a |- U. A = { x | E. y ( x e. y /\ y e. A ) } $.
  $}

  ${
    $d x y A $.
    $( Alternate definition of class union.  (Contributed by NM,
       28-Jun-1998.) $)
    dfuni2 $p |- U. A = { x | E. y e. A x e. y } $=
      cA cuni vx cv vy cv wcel vy cv cA wcel wa vy wex vx cab vx cv vy cv wcel
      vy cA wrex vx cab vx vy cA df-uni vx cv vy cv wcel vy cv cA wcel wa vy
      wex vx cv vy cv wcel vy cA wrex vx vx cv vy cv wcel vy cv cA wcel wa vy
      wex vy cv cA wcel vx cv vy cv wcel wa vy wex vx cv vy cv wcel vy cA wrex
      vx cv vy cv wcel vy cv cA wcel vy exancom vx cv vy cv wcel vy cA df-rex
      bitr4i abbii eqtri $.
  $}

  ${
    $d x A y $.  $d x B y $.
    $( Membership in class union.  (Contributed by NM, 22-May-1994.) $)
    eluni $p |- ( A e. U. B <-> E. x ( A e. x /\ x e. B ) ) $=
      cA cB cuni wcel cA cvv wcel cA vx cv wcel vx cv cB wcel wa vx wex cA cB
      cuni elex cA vx cv wcel vx cv cB wcel wa cA cvv wcel vx cA vx cv wcel cA
      cvv wcel vx cv cB wcel cA vx cv elex adantr exlimiv vy cv vx cv wcel vx
      cv cB wcel wa vx wex cA vx cv wcel vx cv cB wcel wa vx wex vy cA cB cuni
      cvv vy cv cA wceq vy cv vx cv wcel vx cv cB wcel wa cA vx cv wcel vx cv
      cB wcel wa vx vy cv cA wceq vy cv vx cv wcel cA vx cv wcel vx cv cB wcel
      vy cv cA vx cv eleq1 anbi1d exbidv vy vx cB df-uni elab2g pm5.21nii $.

    $( Membership in class union.  Restricted quantifier version.  (Contributed
       by NM, 31-Aug-1999.) $)
    eluni2 $p |- ( A e. U. B <-> E. x e. B A e. x ) $=
      cA vx cv wcel vx cv cB wcel wa vx wex vx cv cB wcel cA vx cv wcel wa vx
      wex cA cB cuni wcel cA vx cv wcel vx cB wrex cA vx cv wcel vx cv cB wcel
      vx exancom vx cA cB eluni cA vx cv wcel vx cB df-rex 3bitr4i $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Membership in class union.  (Contributed by NM, 24-Mar-1995.) $)
    elunii $p |- ( ( A e. B /\ B e. C ) -> A e. U. C ) $=
      cA cB wcel cB cC wcel wa cA vx cv wcel vx cv cC wcel wa vx wex cA cC cuni
      wcel cA cB wcel cB cC wcel cA vx cv wcel vx cv cC wcel wa vx wex cA vx cv
      wcel vx cv cC wcel wa cA cB wcel cB cC wcel wa vx cB cC vx cv cB wceq cA
      vx cv wcel cA cB wcel vx cv cC wcel cB cC wcel vx cv cB cA eleq2 vx cv cB
      cC eleq1 anbi12d spcegv anabsi7 vx cA cC eluni sylibr $.
  $}

  ${
    $d y z A $.  $d x y z $.
    nfuni.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for union.  (Contributed by NM,
       30-Dec-1996.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    nfuni $p |- F/_ x U. A $=
      vx cA cuni vy cv vz cv wcel vz cA wrex vy cab vy vz cA dfuni2 vy cv vz cv
      wcel vz cA wrex vx vy vy cv vz cv wcel vx vz cA nfuni.1 vy cv vz cv wcel
      vx nfv nfrex nfab nfcxfr $.
  $}

  ${
    $d y z A $.  $d x y z $.  $d y z ph $.
    nfunid.3 $e |- ( ph -> F/_ x A ) $.
    $( Deduction version of ~ nfuni .  (Contributed by NM, 18-Feb-2013.) $)
    nfunid $p |- ( ph -> F/_ x U. A ) $=
      wph vx cA cuni vy cv vz cv wcel vz cA wrex vy cab vy vz cA dfuni2 wph vy
      cv vz cv wcel vz cA wrex vx vy wph vy nfv wph vy cv vz cv wcel vx vz cA
      wph vz nfv nfunid.3 wph vy cv vz cv wcel vx nfvd nfrexd nfabd nfcxfrd $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d V y z $.  $d x y z $.
    $( Distribute proper substitution through the union of a class.
       (Contributed by Alan Sare, 10-Nov-2012.) $)
    csbunig $p |- ( A e. V -> [_ A / x ]_ U. B = U. [_ A / x ]_ B ) $=
      cA cV wcel vx cA vz cv vy cv wcel vy cv cB wcel wa vy wex vz cab csb vz
      cv vy cv wcel vy cv vx cA cB csb wcel wa vy wex vz cab vx cA cB cuni csb
      vx cA cB csb cuni cA cV wcel vx cA vz cv vy cv wcel vy cv cB wcel wa vy
      wex vz cab csb vz cv vy cv wcel vy cv cB wcel wa vy wex vx cA wsbc vz cab
      vz cv vy cv wcel vy cv vx cA cB csb wcel wa vy wex vz cab vz cv vy cv
      wcel vy cv cB wcel wa vy wex vx vz cA cV csbabg cA cV wcel vz cv vy cv
      wcel vy cv cB wcel wa vy wex vx cA wsbc vz cv vy cv wcel vy cv vx cA cB
      csb wcel wa vy wex vz cA cV wcel vz cv vy cv wcel vy cv cB wcel wa vy wex
      vx cA wsbc vz cv vy cv wcel vy cv cB wcel wa vx cA wsbc vy wex vz cv vy
      cv wcel vy cv vx cA cB csb wcel wa vy wex vz cv vy cv wcel vy cv cB wcel
      wa vy vx cA cV sbcexg cA cV wcel vz cv vy cv wcel vy cv cB wcel wa vx cA
      wsbc vz cv vy cv wcel vy cv vx cA cB csb wcel wa vy cA cV wcel vz cv vy
      cv wcel vy cv cB wcel wa vx cA wsbc vz cv vy cv wcel vx cA wsbc vy cv cB
      wcel vx cA wsbc wa vz cv vy cv wcel vy cv vx cA cB csb wcel wa vz cv vy
      cv wcel vy cv cB wcel vx cA cV sbcang cA cV wcel vz cv vy cv wcel vx cA
      wsbc vz cv vy cv wcel vy cv cB wcel vx cA wsbc vy cv vx cA cB csb wcel vz
      cv vy cv wcel vx cA cV sbcg vx cA vy cv cB cV sbcel2g anbi12d bitrd
      exbidv bitrd abbidv eqtrd vx cA cB cuni vz cv vy cv wcel vy cv cB wcel wa
      vy wex vz cab vz vy cB df-uni csbeq2i vz vy vx cA cB csb df-uni 3eqtr4g
      $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Equality theorem for class union.  Exercise 15 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 10-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 29-Jun-2011.) $)
    unieq $p |- ( A = B -> U. A = U. B ) $=
      cA cB wceq vy cv vx cv wcel vx cA wrex vy cab vy cv vx cv wcel vx cB wrex
      vy cab cA cuni cB cuni cA cB wceq vy cv vx cv wcel vx cA wrex vy cv vx cv
      wcel vx cB wrex vy vy cv vx cv wcel vx cA cB rexeq abbidv vy vx cA dfuni2
      vy vx cB dfuni2 3eqtr4g $.
  $}

  ${
    unieqi.1 $e |- A = B $.
    $( Inference of equality of two class unions.  (Contributed by NM,
       30-Aug-1993.) $)
    unieqi $p |- U. A = U. B $=
      cA cB wceq cA cuni cB cuni wceq unieqi.1 cA cB unieq ax-mp $.
  $}

  ${
    unieqd.1 $e |- ( ph -> A = B ) $.
    $( Deduction of equality of two class unions.  (Contributed by NM,
       21-Apr-1995.) $)
    unieqd $p |- ( ph -> U. A = U. B ) $=
      wph cA cB wceq cA cuni cB cuni wceq unieqd.1 cA cB unieq syl $.
  $}

  ${
    $d x A y $.  $d ph y $.
    $( Membership in union of a class abstraction.  (Contributed by NM,
       11-Aug-1994.)  (Revised by Mario Carneiro, 14-Nov-2016.) $)
    eluniab $p |- ( A e. U. { x | ph } <-> E. x ( A e. x /\ ph ) ) $=
      cA wph vx cab cuni wcel cA vy cv wcel vy cv wph vx cab wcel wa vy wex cA
      vx cv wcel wph wa vx wex vy cA wph vx cab eluni cA vy cv wcel vy cv wph
      vx cab wcel wa cA vx cv wcel wph wa vy vx cA vy cv wcel vy cv wph vx cab
      wcel vx cA vy cv wcel vx nfv wph vx vy nfsab1 nfan cA vx cv wcel wph wa
      vy nfv vy cv vx cv wceq cA vy cv wcel cA vx cv wcel vy cv wph vx cab wcel
      wph vy cv vx cv cA eleq2 vy cv vx cv wceq vy cv wph vx cab wcel vx cv wph
      vx cab wcel wph vy cv vx cv wph vx cab eleq1 wph vx abid syl6bb anbi12d
      cbvex bitri $.

    $( Membership in union of a class abstraction.  (Contributed by NM,
       4-Oct-2006.) $)
    elunirab $p |- ( A e. U. { x e. B | ph } <->
                   E. x e. B ( A e. x /\ ph ) ) $=
      cA vx cv cB wcel wph wa vx cab cuni wcel cA vx cv wcel vx cv cB wcel wph
      wa wa vx wex cA wph vx cB crab cuni wcel cA vx cv wcel wph wa vx cB wrex
      vx cv cB wcel wph wa vx cA eluniab wph vx cB crab cuni vx cv cB wcel wph
      wa vx cab cuni cA wph vx cB crab vx cv cB wcel wph wa vx cab wph vx cB
      df-rab unieqi eleq2i cA vx cv wcel wph wa vx cB wrex vx cv cB wcel cA vx
      cv wcel wph wa wa vx wex cA vx cv wcel vx cv cB wcel wph wa wa vx wex cA
      vx cv wcel wph wa vx cB df-rex vx cv cB wcel cA vx cv wcel wph wa wa cA
      vx cv wcel vx cv cB wcel wph wa wa vx vx cv cB wcel cA vx cv wcel wph
      an12 exbii bitri 3bitr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    unipr.1 $e |- A e. _V $.
    unipr.2 $e |- B e. _V $.
    $( The union of a pair is the union of its members.  Proposition 5.7 of
       [TakeutiZaring] p. 16.  (Contributed by NM, 23-Aug-1993.) $)
    unipr $p |- U. { A , B } = ( A u. B ) $=
      vx cv cA wcel vx cv cB wcel wo vx cab vx cv vy cv wcel vy cv cA cB cpr
      wcel wa vy wex vx cab cA cB cun cA cB cpr cuni vx cv cA wcel vx cv cB
      wcel wo vx cv vy cv wcel vy cv cA cB cpr wcel wa vy wex vx vx cv vy cv
      wcel vy cv cA wceq wa vx cv vy cv wcel vy cv cB wceq wa wo vy wex vx cv
      vy cv wcel vy cv cA wceq wa vy wex vx cv vy cv wcel vy cv cB wceq wa vy
      wex wo vx cv vy cv wcel vy cv cA cB cpr wcel wa vy wex vx cv cA wcel vx
      cv cB wcel wo vx cv vy cv wcel vy cv cA wceq wa vx cv vy cv wcel vy cv cB
      wceq wa vy 19.43 vx cv vy cv wcel vy cv cA cB cpr wcel wa vx cv vy cv
      wcel vy cv cA wceq wa vx cv vy cv wcel vy cv cB wceq wa wo vy vx cv vy cv
      wcel vy cv cA cB cpr wcel wa vx cv vy cv wcel vy cv cA wceq vy cv cB wceq
      wo wa vx cv vy cv wcel vy cv cA wceq wa vx cv vy cv wcel vy cv cB wceq wa
      wo vy cv cA cB cpr wcel vy cv cA wceq vy cv cB wceq wo vx cv vy cv wcel
      vy cv cA cB vy vex elpr anbi2i vx cv vy cv wcel vy cv cA wceq vy cv cB
      wceq andi bitri exbii vx cv cA wcel vx cv vy cv wcel vy cv cA wceq wa vy
      wex vx cv cB wcel vx cv vy cv wcel vy cv cB wceq wa vy wex vx cv cA wcel
      vy cv cA wceq vx cv vy cv wcel wa vy wex vx cv vy cv wcel vy cv cA wceq
      wa vy wex vy vx cv cA unipr.1 clel3 vy cv cA wceq vx cv vy cv wcel vy
      exancom bitri vx cv cB wcel vy cv cB wceq vx cv vy cv wcel wa vy wex vx
      cv vy cv wcel vy cv cB wceq wa vy wex vy vx cv cB unipr.2 clel3 vy cv cB
      wceq vx cv vy cv wcel vy exancom bitri orbi12i 3bitr4ri abbii vx cA cB
      df-un vx vy cA cB cpr df-uni 3eqtr4ri $.
  $}

  ${
    $d x y A $.  $d y B $.
    $( The union of a pair is the union of its members.  Proposition 5.7 of
       [TakeutiZaring] p. 16.  (Contributed by NM, 25-Aug-2006.) $)
    uniprg $p |- ( ( A e. V /\ B e. W ) -> U. { A , B } = ( A u. B ) ) $=
      vx cv vy cv cpr cuni vx cv vy cv cun wceq cA vy cv cpr cuni cA vy cv cun
      wceq cA cB cpr cuni cA cB cun wceq vx vy cA cB cV cW vx cv cA wceq vx cv
      vy cv cpr cuni cA vy cv cpr cuni vx cv vy cv cun cA vy cv cun vx cv cA
      wceq vx cv vy cv cpr cA vy cv cpr vx cv cA vy cv preq1 unieqd vx cv cA vy
      cv uneq1 eqeq12d vy cv cB wceq cA vy cv cpr cuni cA cB cpr cuni cA vy cv
      cun cA cB cun vy cv cB wceq cA vy cv cpr cA cB cpr vy cv cB cA preq2
      unieqd vy cv cB cA uneq2 eqeq12d vx cv vy cv vx vex vy vex unipr vtocl2g
      $.
  $}

  ${
    unisn.1 $e |- A e. _V $.
    $( A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       (Contributed by NM, 30-Aug-1993.) $)
    unisn $p |- U. { A } = A $=
      cA csn cuni cA cA cpr cuni cA cA cun cA cA csn cA cA cpr cA dfsn2 unieqi
      cA cA unisn.1 unisn.1 unipr cA unidm 3eqtri $.
  $}

  ${
    $d x A $.
    $( A set equals the union of its singleton.  Theorem 8.2 of [Quine] p. 53.
       (Contributed by NM, 13-Aug-2002.) $)
    unisng $p |- ( A e. V -> U. { A } = A ) $=
      vx cv csn cuni vx cv wceq cA csn cuni cA wceq vx cA cV vx cv cA wceq vx
      cv csn cuni cA csn cuni vx cv cA vx cv cA wceq vx cv csn cA csn vx cv cA
      sneq unieqd vx cv cA wceq id eqeq12d vx cv vx vex unisn vtoclg $.
  $}

  ${
    $d x y $.  $d y A $.
    $( An alternative statement of the effective freeness of a class ` A ` ,
       when it is a set.  (Contributed by Mario Carneiro, 14-Oct-2016.) $)
    dfnfc2 $p |- ( A. x A e. V -> ( F/_ x A <-> A. y F/ x y = A ) ) $=
      cA cV wcel vx wal vx cA wnfc vy cv cA wceq vx wnf vy wal vx cA wnfc vy cv
      cA wceq vx wnf vy vx cA wnfc vx vy cv cA vx cA wnfc vx vy cv nfcvd vx cA
      wnfc id nfeqd alrimiv cA cV wcel vx wal vy cv cA wceq vx wnf vy wal vx cA
      wnfc cA cV wcel vx wal vy cv cA wceq vx wnf vy wal wa vx cA csn cuni wnfc
      vx cA wnfc cA cV wcel vx wal vy cv cA wceq vx wnf vy wal wa vx cA csn cA
      cV wcel vx wal vy cv cA wceq vx wnf vy wal wa vy cv cA wceq vx wnf vy wal
      vx cA csn wnfc cA cV wcel vx wal vy cv cA wceq vx wnf vy wal simpr vx cA
      csn wnfc vy cv cA csn wcel vx wnf vy wal vy cv cA wceq vx wnf vy wal vx
      vy cA csn df-nfc vy cv cA csn wcel vx wnf vy cv cA wceq vx wnf vy vy cv
      cA csn wcel vy cv cA wceq vx vy cA elsn nfbii albii bitri sylibr nfunid
      cA cV wcel vx wal vy cv cA wceq vx wnf vy wal wa vx cA csn cuni cA cA cV
      wcel vx wal vy cv cA wceq vx wnf vy wal vx cA cV wcel vx nfa1 vy cv cA
      wceq vx wnf vx vy vy cv cA wceq vx nfnf1 nfal nfan cA cV wcel vx wal cA
      csn cuni cA wceq vy cv cA wceq vx wnf vy wal cA cV wcel cA csn cuni cA
      wceq vx cA cV unisng sps adantr nfceqdf mpbid ex impbid2 $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The class union of the union of two classes.  Theorem 8.3 of [Quine]
       p. 53.  (Contributed by NM, 20-Aug-1993.) $)
    uniun $p |- U. ( A u. B ) = ( U. A u. U. B ) $=
      vx cA cB cun cuni cA cuni cB cuni cun vx cv vy cv wcel vy cv cA cB cun
      wcel wa vy wex vx cv cA cuni wcel vx cv cB cuni wcel wo vx cv cA cB cun
      cuni wcel vx cv cA cuni cB cuni cun wcel vx cv vy cv wcel vy cv cA wcel
      wa vx cv vy cv wcel vy cv cB wcel wa wo vy wex vx cv vy cv wcel vy cv cA
      wcel wa vy wex vx cv vy cv wcel vy cv cB wcel wa vy wex wo vx cv vy cv
      wcel vy cv cA cB cun wcel wa vy wex vx cv cA cuni wcel vx cv cB cuni wcel
      wo vx cv vy cv wcel vy cv cA wcel wa vx cv vy cv wcel vy cv cB wcel wa vy
      19.43 vx cv vy cv wcel vy cv cA cB cun wcel wa vx cv vy cv wcel vy cv cA
      wcel wa vx cv vy cv wcel vy cv cB wcel wa wo vy vx cv vy cv wcel vy cv cA
      cB cun wcel wa vx cv vy cv wcel vy cv cA wcel vy cv cB wcel wo wa vx cv
      vy cv wcel vy cv cA wcel wa vx cv vy cv wcel vy cv cB wcel wa wo vy cv cA
      cB cun wcel vy cv cA wcel vy cv cB wcel wo vx cv vy cv wcel vy cv cA cB
      elun anbi2i vx cv vy cv wcel vy cv cA wcel vy cv cB wcel andi bitri exbii
      vx cv cA cuni wcel vx cv vy cv wcel vy cv cA wcel wa vy wex vx cv cB cuni
      wcel vx cv vy cv wcel vy cv cB wcel wa vy wex vy vx cv cA eluni vy vx cv
      cB eluni orbi12i 3bitr4i vy vx cv cA cB cun eluni vx cv cA cuni cB cuni
      elun 3bitr4i eqriv $.

    $( The class union of the intersection of two classes.  Exercise 4.12(n) of
       [Mendelson] p. 235.  See ~ uninqs for a condition where equality holds.
       (Contributed by NM, 4-Dec-2003.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    uniin $p |- U. ( A i^i B ) C_ ( U. A i^i U. B ) $=
      vx cA cB cin cuni cA cuni cB cuni cin vx cv vy cv wcel vy cv cA cB cin
      wcel wa vy wex vx cv cA cuni wcel vx cv cB cuni wcel wa vx cv cA cB cin
      cuni wcel vx cv cA cuni cB cuni cin wcel vx cv vy cv wcel vy cv cA wcel
      wa vx cv vy cv wcel vy cv cB wcel wa wa vy wex vx cv vy cv wcel vy cv cA
      wcel wa vy wex vx cv vy cv wcel vy cv cB wcel wa vy wex wa vx cv vy cv
      wcel vy cv cA cB cin wcel wa vy wex vx cv cA cuni wcel vx cv cB cuni wcel
      wa vx cv vy cv wcel vy cv cA wcel wa vx cv vy cv wcel vy cv cB wcel wa vy
      19.40 vx cv vy cv wcel vy cv cA cB cin wcel wa vx cv vy cv wcel vy cv cA
      wcel wa vx cv vy cv wcel vy cv cB wcel wa wa vy vx cv vy cv wcel vy cv cA
      cB cin wcel wa vx cv vy cv wcel vy cv cA wcel vy cv cB wcel wa wa vx cv
      vy cv wcel vy cv cA wcel wa vx cv vy cv wcel vy cv cB wcel wa wa vy cv cA
      cB cin wcel vy cv cA wcel vy cv cB wcel wa vx cv vy cv wcel vy cv cA cB
      elin anbi2i vx cv vy cv wcel vy cv cA wcel vy cv cB wcel anandi bitri
      exbii vx cv cA cuni wcel vx cv vy cv wcel vy cv cA wcel wa vy wex vx cv
      cB cuni wcel vx cv vy cv wcel vy cv cB wcel wa vy wex vy vx cv cA eluni
      vy vx cv cB eluni anbi12i 3imtr4i vy vx cv cA cB cin eluni vx cv cA cuni
      cB cuni elin 3imtr4i ssriv $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Subclass relationship for class union.  Theorem 61 of [Suppes] p. 39.
       (Contributed by NM, 22-Mar-1998.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    uniss $p |- ( A C_ B -> U. A C_ U. B ) $=
      cA cB wss vx cA cuni cB cuni cA cB wss vx cv vy cv wcel vy cv cA wcel wa
      vy wex vx cv vy cv wcel vy cv cB wcel wa vy wex vx cv cA cuni wcel vx cv
      cB cuni wcel cA cB wss vx cv vy cv wcel vy cv cA wcel wa vx cv vy cv wcel
      vy cv cB wcel wa vy cA cB wss vy cv cA wcel vy cv cB wcel vx cv vy cv
      wcel cA cB vy cv ssel anim2d eximdv vy vx cv cA eluni vy vx cv cB eluni
      3imtr4g ssrdv $.

    $( Subclass relationship for class union.  (Contributed by NM,
       24-May-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    ssuni $p |- ( ( A C_ B /\ B e. C ) -> A C_ U. C ) $=
      cB cC wcel cA cB wss cA cC cuni wss cB cC wcel vy cv cA wcel vy cv cB
      wcel wi vy wal vy cv cA wcel vy cv cC cuni wcel wi vy wal cA cB wss cA cC
      cuni wss cB cC wcel vy cv cA wcel vy cv cB wcel wi vy cv cA wcel vy cv cC
      cuni wcel wi vy cB cC wcel vy cv cB wcel vy cv cC cuni wcel vy cv cA wcel
      vy cv vx cv wcel vy cv cC cuni wcel wi vy cv cB wcel vy cv cC cuni wcel
      wi vx cB cC vx cv cB wceq vy cv vx cv wcel vy cv cB wcel vy cv cC cuni
      wcel vx cv cB vy cv eleq2 imbi1d vy cv vx cv wcel vx cv cC wcel vy cv cC
      cuni wcel vy cv vx cv cC elunii expcom vtoclga imim2d alimdv vy cA cB
      dfss2 vy cA cC cuni dfss2 3imtr4g impcom $.
  $}

  ${
    unissi.1 $e |- A C_ B $.
    $( Subclass relationship for subclass union.  Inference form of ~ uniss .
       (Contributed by David Moews, 1-May-2017.) $)
    unissi $p |- U. A C_ U. B $=
      cA cB wss cA cuni cB cuni wss unissi.1 cA cB uniss ax-mp $.
  $}

  ${
    unissd.1 $e |- ( ph -> A C_ B ) $.
    $( Subclass relationship for subclass union.  Deduction form of ~ uniss .
       (Contributed by David Moews, 1-May-2017.) $)
    unissd $p |- ( ph -> U. A C_ U. B ) $=
      wph cA cB wss cA cuni cB cuni wss unissd.1 cA cB uniss syl $.
  $}

  ${
    $d x y A $.
    $( The union of a set is empty iff the set is included in the singleton of
       the empty set.  (Contributed by NM, 12-Sep-2004.) $)
    uni0b $p |- ( U. A = (/) <-> A C_ { (/) } ) $=
      vx cv c0 csn wcel vx cA wral vx cv c0 wceq vx cA wral cA c0 csn wss cA
      cuni c0 wceq vx cv c0 csn wcel vx cv c0 wceq vx cA vx c0 elsn ralbii vx
      cA c0 csn dfss3 cA cuni c0 wceq vx cv c0 wceq vx cA wral cA cuni c0 wceq
      wn vy cv cA cuni wcel vy wex vx cv c0 wceq wn vx cA wrex vx cv c0 wceq vx
      cA wral wn vy cA cuni neq0 vy cv vx cv wcel vy wex vx cA wrex vy cv vx cv
      wcel vx cA wrex vy wex vx cv c0 wceq wn vx cA wrex vy cv cA cuni wcel vy
      wex vy cv vx cv wcel vx vy cA rexcom4 vx cv c0 wceq wn vy cv vx cv wcel
      vy wex vx cA vy vx cv neq0 rexbii vy cv cA cuni wcel vy cv vx cv wcel vx
      cA wrex vy vx vy cv cA eluni2 exbii 3bitr4ri vx cv c0 wceq vx cA rexnal
      3bitri con4bii 3bitr4ri $.

    $( The union of a set is empty iff all of its members are empty.
       (Contributed by NM, 16-Aug-2006.) $)
    uni0c $p |- ( U. A = (/) <-> A. x e. A x = (/) ) $=
      cA cuni c0 wceq cA c0 csn wss vx cv c0 csn wcel vx cA wral vx cv c0 wceq
      vx cA wral cA uni0b vx cA c0 csn dfss3 vx cv c0 csn wcel vx cv c0 wceq vx
      cA vx c0 elsn ralbii 3bitri $.
  $}

  $( The union of the empty set is the empty set.  Theorem 8.7 of [Quine]
     p. 54.  (Reproved without relying on ~ ax-nul by Eric Schmidt.)
     (Contributed by NM, 16-Sep-1993.)  (Revised by Eric Schmidt,
     4-Apr-2007.) $)
  uni0 $p |- U. (/) = (/) $=
    c0 cuni c0 wceq c0 c0 csn wss c0 csn 0ss c0 uni0b mpbir $.

  $( An element of a class is a subclass of its union.  Theorem 8.6 of [Quine]
     p. 54.  Also the basis for Proposition 7.20 of [TakeutiZaring] p. 40.
     (Contributed by NM, 6-Jun-1994.) $)
  elssuni $p |- ( A e. B -> A C_ U. B ) $=
    cA cA wss cA cB wcel cA cB cuni wss cA ssid cA cA cB ssuni mpan $.

  $( Condition turning a subclass relationship for union into an equality.
     (Contributed by NM, 18-Jul-2006.) $)
  unissel $p |- ( ( U. A C_ B /\ B e. A ) -> U. A = B ) $=
    cA cuni cB wss cB cA wcel wa cA cuni cB cA cuni cB wss cB cA wcel simpl cB
    cA wcel cB cA cuni wss cA cuni cB wss cB cA elssuni adantl eqssd $.

  ${
    $d x y A $.  $d x y B $.
    $( Relationship involving membership, subset, and union.  Exercise 5 of
       [Enderton] p. 26 and its converse.  (Contributed by NM, 20-Sep-2003.) $)
    unissb $p |- ( U. A C_ B <-> A. x e. A x C_ B ) $=
      vy cv cA cuni wcel vy cv cB wcel wi vy wal vx cv cA wcel vx cv cB wss wi
      vx wal cA cuni cB wss vx cv cB wss vx cA wral vy cv cA cuni wcel vy cv cB
      wcel wi vy wal vy cv vx cv wcel vx cv cA wcel wa vy cv cB wcel wi vx wal
      vy wal vx cv cA wcel vx cv cB wss wi vx wal vy cv cA cuni wcel vy cv cB
      wcel wi vy cv vx cv wcel vx cv cA wcel wa vy cv cB wcel wi vx wal vy vy
      cv cA cuni wcel vy cv cB wcel wi vy cv vx cv wcel vx cv cA wcel wa vx wex
      vy cv cB wcel wi vy cv vx cv wcel vx cv cA wcel wa vy cv cB wcel wi vx
      wal vy cv cA cuni wcel vy cv vx cv wcel vx cv cA wcel wa vx wex vy cv cB
      wcel vx vy cv cA eluni imbi1i vy cv vx cv wcel vx cv cA wcel wa vy cv cB
      wcel vx 19.23v bitr4i albii vy cv vx cv wcel vx cv cA wcel wa vy cv cB
      wcel wi vx wal vy wal vy cv vx cv wcel vx cv cA wcel wa vy cv cB wcel wi
      vy wal vx wal vx cv cA wcel vx cv cB wss wi vx wal vy cv vx cv wcel vx cv
      cA wcel wa vy cv cB wcel wi vy vx alcom vy cv vx cv wcel vx cv cA wcel wa
      vy cv cB wcel wi vy wal vx cv cA wcel vx cv cB wss wi vx vx cv cA wcel vy
      cv vx cv wcel vy cv cB wcel wi wi vy wal vx cv cA wcel vy cv vx cv wcel
      vy cv cB wcel wi vy wal wi vy cv vx cv wcel vx cv cA wcel wa vy cv cB
      wcel wi vy wal vx cv cA wcel vx cv cB wss wi vx cv cA wcel vy cv vx cv
      wcel vy cv cB wcel wi vy 19.21v vy cv vx cv wcel vx cv cA wcel wa vy cv
      cB wcel wi vx cv cA wcel vy cv vx cv wcel vy cv cB wcel wi wi vy vy cv vx
      cv wcel vx cv cA wcel wa vy cv cB wcel wi vy cv vx cv wcel vx cv cA wcel
      vy cv cB wcel wi wi vx cv cA wcel vy cv vx cv wcel vy cv cB wcel wi wi vy
      cv vx cv wcel vx cv cA wcel vy cv cB wcel impexp vy cv vx cv wcel vx cv
      cA wcel vy cv cB wcel bi2.04 bitri albii vx cv cB wss vy cv vx cv wcel vy
      cv cB wcel wi vy wal vx cv cA wcel vy vx cv cB dfss2 imbi2i 3bitr4i albii
      bitri bitri vy cA cuni cB dfss2 vx cv cB wss vx cA df-ral 3bitr4i $.
  $}

  ${
    $d x A $.  $d x y B $.
    $( A subclass condition on the members of two classes that implies a
       subclass relation on their unions.  Proposition 8.6 of [TakeutiZaring]
       p. 59.  See ~ iunss2 for a generalization to indexed unions.
       (Contributed by NM, 22-Mar-2004.) $)
    uniss2 $p |- ( A. x e. A E. y e. B x C_ y -> U. A C_ U. B ) $=
      vx cv vy cv wss vy cB wrex vx cA wral vx cv cB cuni wss vx cA wral cA
      cuni cB cuni wss vx cv vy cv wss vy cB wrex vx cv cB cuni wss vx cA vx cv
      vy cv wss vx cv cB cuni wss vy cB vx cv vy cv wss vy cv cB wcel vx cv cB
      cuni wss vx cv vy cv cB ssuni expcom rexlimiv ralimi vx cA cB cuni unissb
      sylibr $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( If the difference ` A \ B ` contains the largest members of ` A ` , then
       the union of the difference is the union of ` A ` .  (Contributed by NM,
       22-Mar-2004.) $)
    unidif $p |- ( A. x e. A E. y e. ( A \ B ) x C_ y ->
               U. ( A \ B ) = U. A ) $=
      vx cv vy cv wss vy cA cB cdif wrex vx cA wral cA cB cdif cuni cA cuni wss
      cA cuni cA cB cdif cuni wss wa cA cB cdif cuni cA cuni wceq vx cv vy cv
      wss vy cA cB cdif wrex vx cA wral cA cuni cA cB cdif cuni wss cA cB cdif
      cuni cA cuni wss vx vy cA cA cB cdif uniss2 cA cB cdif cA wss cA cB cdif
      cuni cA cuni wss cA cB difss cA cB cdif cA uniss ax-mp jctil cA cB cdif
      cuni cA cuni eqss sylibr $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Relationship implying union.  (Contributed by NM, 10-Nov-1999.) $)
    ssunieq $p |- ( ( A e. B /\ A. x e. B x C_ A ) -> A = U. B ) $=
      cA cB wcel vx cv cA wss vx cB wral wa cA cB cuni wss cB cuni cA wss wa cA
      cB cuni wceq cA cB wcel cA cB cuni wss vx cv cA wss vx cB wral cB cuni cA
      wss cA cB elssuni cB cuni cA wss vx cv cA wss vx cB wral vx cB cA unissb
      biimpri anim12i cA cB cuni eqss sylibr $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Any member of a class is the largest of those members that it includes.
       (Contributed by NM, 13-Aug-2002.) $)
    unimax $p |- ( A e. B -> U. { x e. B | x C_ A } = A ) $=
      cA cB wcel cA vx cv cA wss vx cB crab wcel vy cv cA wss vy vx cv cA wss
      vx cB crab wral vx cv cA wss vx cB crab cuni cA wceq cA cB wcel cA vx cv
      cA wss vx cB crab wcel cA cA wss cA ssid vx cv cA wss cA cA wss vx cA cB
      vx cv cA cA sseq1 elrab3 mpbiri vy cv cA wss vy vx cv cA wss vx cB crab
      vy cv vx cv cA wss vx cB crab wcel vy cv cB wcel vy cv cA wss vx cv cA
      wss vy cv cA wss vx vy cv cB vx cv vy cv cA sseq1 elrab simprbi rgen cA
      vx cv cA wss vx cB crab wcel vy cv cA wss vy vx cv cA wss vx cB crab wral
      wa cA vx cv cA wss vx cB crab cuni vy cA vx cv cA wss vx cB crab ssunieq
      eqcomd sylancl $.
  $}


