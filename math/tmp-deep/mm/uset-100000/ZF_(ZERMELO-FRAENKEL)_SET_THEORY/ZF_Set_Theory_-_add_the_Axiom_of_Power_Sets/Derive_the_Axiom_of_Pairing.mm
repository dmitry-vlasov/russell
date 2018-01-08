
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets/Introduce_the_Axiom_of_Power_Sets.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                   Derive the Axiom of Pairing

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x z w v $.  $d y z w v $.
    $( The Axiom of Pairing of Zermelo-Fraenkel set theory.  Axiom 2 of
       [TakeutiZaring] p. 15.  In some textbooks this is stated as a separate
       axiom; here we show it is redundant since it can be derived from the
       other axioms.

       This theorem should not be referenced by any proof other than ~ axpr .
       Instead, use ~ zfpair2 below so that the uses of the Axiom of Pairing
       can be more easily identified.  (Contributed by NM, 18-Oct-1995.)
       (New usage is discouraged.) $)
    zfpair $p |- { x , y } e. _V $=
      vx cv vy cv cpr vw cv vx cv wceq vw cv vy cv wceq wo vw cab cvv vw vx cv
      vy cv dfpr2 vw cv vx cv wceq vw cv vy cv wceq wo vw cab vz cv c0 wceq vz
      cv c0 csn wceq wo vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn wceq vw
      cv vy cv wceq wa wo wa vz wex vw cab cvv vw cv vx cv wceq vw cv vy cv
      wceq wo vz cv c0 wceq vz cv c0 csn wceq wo vz cv c0 wceq vw cv vx cv wceq
      wa vz cv c0 csn wceq vw cv vy cv wceq wa wo wa vz wex vw vz cv c0 wceq vw
      cv vx cv wceq wa vz cv c0 csn wceq vw cv vy cv wceq wa wo vz wex vz cv c0
      wceq vw cv vx cv wceq wa vz wex vz cv c0 csn wceq vw cv vy cv wceq wa vz
      wex wo vz cv c0 wceq vz cv c0 csn wceq wo vz cv c0 wceq vw cv vx cv wceq
      wa vz cv c0 csn wceq vw cv vy cv wceq wa wo wa vz wex vw cv vx cv wceq vw
      cv vy cv wceq wo vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn wceq vw
      cv vy cv wceq wa vz 19.43 vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn
      wceq vw cv vy cv wceq wa wo vz cv c0 wceq vz cv c0 csn wceq wo vz cv c0
      wceq vw cv vx cv wceq wa vz cv c0 csn wceq vw cv vy cv wceq wa wo wa vz
      vz cv c0 wceq vw cv vx cv wceq vz cv c0 csn wceq vw cv vy cv wceq prlem2
      exbii vz cv c0 wceq vw cv vx cv wceq wa vz wex vw cv vx cv wceq vz cv c0
      csn wceq vw cv vy cv wceq wa vz wex vw cv vy cv wceq vz cv c0 wceq vw cv
      vx cv wceq wa vz wex vz cv c0 wceq vz wex vw cv vx cv wceq vz c0 0ex
      isseti vz cv c0 wceq vw cv vx cv wceq vz 19.41v mpbiran vz cv c0 csn wceq
      vw cv vy cv wceq wa vz wex vz cv c0 csn wceq vz wex vw cv vy cv wceq vz
      c0 csn p0ex isseti vz cv c0 csn wceq vw cv vy cv wceq vz 19.41v mpbiran
      orbi12i 3bitr3ri abbii vz cv c0 wceq vz cv c0 csn wceq wo vz cv c0 wceq
      vw cv vx cv wceq wa vz cv c0 csn wceq vw cv vy cv wceq wa wo vz vw vv c0
      c0 csn cpr vz cv c0 wceq vz cv c0 csn wceq wo vz cab cvv vz c0 c0 csn
      dfpr2 pp0ex eqeltrri vz cv c0 wceq vz cv c0 wceq vw cv vx cv wceq wa vz
      cv c0 csn wceq vw cv vy cv wceq wa wo vw cv vv cv wceq wi vw wal vv wex
      vz cv c0 csn wceq vz cv c0 wceq vz cv c0 wceq vw cv vx cv wceq wa vz cv
      c0 csn wceq vw cv vy cv wceq wa wo vw cv vv cv wceq wi vw wal vv vx vv cv
      vx cv wceq vz cv c0 wceq vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn
      wceq vw cv vy cv wceq wa wo vw cv vv cv wceq wi vw vv cv vx cv wceq vz cv
      c0 wceq vw cv vx cv wceq vz cv c0 csn wceq vw cv vy cv wceq vw cv vv cv
      wceq vv vx vw equequ2 vz cv 0inp0 prlem1 alrimdv spimev vz cv c0 csn wceq
      vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn wceq vw cv vy cv wceq wa
      wo vw cv vv cv wceq wi vw wal vv vy vv cv vy cv wceq vz cv c0 csn wceq vz
      cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn wceq vw cv vy cv wceq wa wo
      vw cv vv cv wceq wi vw vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn
      wceq vw cv vy cv wceq wa wo vz cv c0 csn wceq vw cv vy cv wceq wa vz cv
      c0 wceq vw cv vx cv wceq wa wo vv cv vy cv wceq vz cv c0 csn wceq vw cv
      vv cv wceq vz cv c0 wceq vw cv vx cv wceq wa vz cv c0 csn wceq vw cv vy
      cv wceq wa orcom vv cv vy cv wceq vz cv c0 csn wceq vw cv vy cv wceq vz
      cv c0 wceq vw cv vx cv wceq vw cv vv cv wceq vv vy vw equequ2 vz cv c0
      wceq vz cv c0 csn wceq vz cv 0inp0 con2i prlem1 syl7bi alrimdv spimev
      jaoi zfrep4 eqeltri eqeltri $.

    $( Unabbreviated version of the Axiom of Pairing of ZF set theory, derived
       as a theorem from the other axioms.

       This theorem should not be referenced by any proof.  Instead, use
       ~ ax-pr below so that the uses of the Axiom of Pairing can be more
       easily identified.  (Contributed by NM, 14-Nov-2006.)
       (New usage is discouraged.) $)
    axpr $p |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $=
      vz cv vx cv vy cv cpr wceq vz wex vw cv vx cv wceq vw cv vy cv wceq wo vw
      cv vz cv wcel wi vw wal vz wex vz vx cv vy cv cpr vx vy zfpair isseti vz
      cv vx cv vy cv cpr wceq vw cv vx cv wceq vw cv vy cv wceq wo vw cv vz cv
      wcel wi vw wal vz vz cv vx cv vy cv cpr wceq vw cv vz cv wcel vw cv vx cv
      vy cv cpr wcel wb vw wal vw cv vx cv wceq vw cv vy cv wceq wo vw cv vz cv
      wcel wi vw wal vw vz cv vx cv vy cv cpr dfcleq vw cv vz cv wcel vw cv vx
      cv vy cv cpr wcel wb vw cv vx cv wceq vw cv vy cv wceq wo vw cv vz cv
      wcel wi vw vw cv vz cv wcel vw cv vx cv vy cv cpr wcel wb vw cv vz cv
      wcel vw cv vx cv wceq vw cv vy cv wceq wo wb vw cv vx cv wceq vw cv vy cv
      wceq wo vw cv vz cv wcel wi vw cv vx cv vy cv cpr wcel vw cv vx cv wceq
      vw cv vy cv wceq wo vw cv vz cv wcel vw cv vx cv vy cv vw vex elpr bibi2i
      vw cv vz cv wcel vw cv vx cv wceq vw cv vy cv wceq wo bi2 sylbi alimi
      sylbi eximi ax-mp $.

    $( The Axiom of Pairing of ZF set theory.  It was derived as theorem ~ axpr
       above and is therefore redundant, but we state it as a separate axiom
       here so that its uses can be identified more easily.  (Contributed by
       NM, 14-Nov-2006.) $)
    ax-pr $a |- E. z A. w ( ( w = x \/ w = y ) -> w e. z ) $.

    $( Derive the abbreviated version of the Axiom of Pairing from ~ ax-pr .
       See ~ zfpair for its derivation from the other axioms.  (Contributed by
       NM, 14-Nov-2006.) $)
    zfpair2 $p |- { x , y } e. _V $=
      vz vx cv vy cv cpr vz cv vx cv vy cv cpr wceq vz wex vw cv vz cv wcel vw
      cv vx cv wceq vw cv vy cv wceq wo wb vw wal vz wex vw cv vx cv wceq vw cv
      vy cv wceq wo vz vw vx vy vz vw ax-pr bm1.3ii vz cv vx cv vy cv cpr wceq
      vw cv vz cv wcel vw cv vx cv wceq vw cv vy cv wceq wo wb vw wal vz vz cv
      vx cv vy cv cpr wceq vw cv vz cv wcel vw cv vx cv vy cv cpr wcel wb vw
      wal vw cv vz cv wcel vw cv vx cv wceq vw cv vy cv wceq wo wb vw wal vw vz
      cv vx cv vy cv cpr dfcleq vw cv vz cv wcel vw cv vx cv vy cv cpr wcel wb
      vw cv vz cv wcel vw cv vx cv wceq vw cv vy cv wceq wo wb vw vw cv vx cv
      vy cv cpr wcel vw cv vx cv wceq vw cv vy cv wceq wo vw cv vz cv wcel vw
      cv vx cv vy cv vw vex elpr bibi2i albii bitri exbii mpbir issetri $.
  $}

  ${
    $d x A $.
    $( A singleton is a set.  Theorem 7.13 of [Quine] p. 51, proved using
       Extensionality, Separation, and Pairing.  See also ~ snexALT .
       (Contributed by NM, 7-Aug-1994.)  (Revised by Mario Carneiro,
       19-May-2013.)  (Proof modification is discouraged.) $)
    snex $p |- { A } e. _V $=
      cA cvv wcel cA csn cvv wcel cA cvv wcel cA csn cA cA cpr cvv cA dfsn2 vx
      cv vx cv cpr cvv wcel cA cA cpr cvv wcel vx cA cvv vx cv cA wceq vx cv vx
      cv cpr cA cA cpr cvv vx cv cA wceq vx cv vx cv cpr cA cA cpr wceq vx cv
      vx cv cA cA preq12 anidms eleq1d vx vx zfpair2 vtoclg syl5eqel cA cvv
      wcel wn cA csn c0 cvv cA cvv wcel wn cA csn c0 wceq cA snprc biimpi 0ex
      syl6eqel pm2.61i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The Axiom of Pairing using class variables.  Theorem 7.13 of [Quine]
       p. 51.  By virtue of its definition, an unordered pair remains a set
       (even though no longer a pair) even when its components are proper
       classes (see ~ prprc ), so we can dispense with hypotheses requiring
       them to be sets.  (Contributed by NM, 5-Aug-1993.) $)
    prex $p |- { A , B } e. _V $=
      cA cvv wcel cB cvv wcel cA cB cpr cvv wcel cB cvv wcel cA cB cpr cvv wcel
      wi vx cA cvv cB cvv wcel vx cv cB cpr cvv wcel vx cv cA wceq cA cB cpr
      cvv wcel vx cv vy cv cpr cvv wcel vx cv cB cpr cvv wcel vy cB cvv vy cv
      cB wceq vx cv vy cv cpr vx cv cB cpr cvv vy cv cB vx cv preq2 eleq1d vx
      vy zfpair2 vtoclg vx cv cA wceq vx cv cB cpr cA cB cpr cvv vx cv cA cB
      preq1 eleq1d syl5ib vtocleg cA cvv wcel wn cA cB cpr cB csn cvv cA cB
      prprc1 cB snex syl6eqel cB cvv wcel wn cA cB cpr cA csn cvv cA cB prprc2
      cA snex syl6eqel pm2.61nii $.
  $}

  ${
    $d x y $.
    $( Every set is an element of some other set.  This has a shorter proof
       than ~ el but uses more axioms.  (Contributed by NM, 4-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    elALT $p |- E. y x e. y $=
      vx cv vx cv csn wcel vx cv vy cv wcel vy wex vx cv vx vex snid vx cv vy
      cv wcel vx cv vx cv csn wcel vy vx cv csn vx cv snex vy cv vx cv csn vx
      cv eleq2 spcev ax-mp $.
  $}

  ${
    $d x y $.
    $( An alternative proof of ~ dtru ("two things exist") using ~ ax-pr
       instead of ~ ax-pow .  (Contributed by Mario Carneiro, 31-Aug-2015.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dtruALT2 $p |- -. A. x x = y $=
      vy cv vx cv wceq wn vx wex vx cv vy cv wceq vx wal wn vy cv c0 wceq vy cv
      vx cv wceq wn vx wex vy cv c0 wceq vy cv c0 csn wceq wn vy cv vx cv wceq
      wn vx wex vy cv 0inp0 vy cv vx cv wceq wn vy cv c0 csn wceq wn vx c0 csn
      c0 snex vx cv c0 csn wceq vy cv vx cv wceq vy cv c0 csn wceq vx cv c0 csn
      vy cv eqeq2 notbid spcev syl vy cv vx cv wceq wn vy cv c0 wceq wn vx c0
      0ex vx cv c0 wceq vy cv vx cv wceq vy cv c0 wceq vx cv c0 vy cv eqeq2
      notbid spcev pm2.61i vy cv vx cv wceq wn vx wex vy cv vx cv wceq vx wal
      vx cv vy cv wceq vx wal vy cv vx cv wceq vx exnal vy cv vx cv wceq vx cv
      vy cv wceq vx vy cv vx cv eqcom albii xchbinx mpbi $.
  $}

  ${
    $( A singleton of a set belongs to the power class of a class containing
       the set.  (Contributed by Alan Sare, 25-Aug-2011.) $)
    snelpwi $p |- ( A e. B -> { A } e. ~P B ) $=
      cA cB wcel cA csn cB wss cA csn cB cpw wcel cA cB snssi cA csn cB cA snex
      elpw sylibr $.
  $}

  ${
    snelpw.1 $e |- A e. _V $.
    $( A singleton of a set belongs to the power class of a class containing
       the set.  (Contributed by NM, 1-Apr-1998.) $)
    snelpw $p |- ( A e. B <-> { A } e. ~P B ) $=
      cA cB wcel cA csn cB wss cA csn cB cpw wcel cA cB snelpw.1 snss cA csn cB
      cA snex elpw bitr4i $.
  $}

  ${
    $d x y z $.
    $( A theorem similar to extensionality, requiring the existence of a
       singleton.  Exercise 8 of [TakeutiZaring] p. 16.  (Contributed by NM,
       10-Aug-1993.) $)
    rext $p |- ( A. z ( x e. z -> y e. z ) -> x = y ) $=
      vx cv vz cv wcel vy cv vz cv wcel wi vz wal vy cv vx cv csn wcel vx cv vy
      cv wceq vx cv vz cv wcel vy cv vz cv wcel wi vz wal vx cv vx cv csn wcel
      vy cv vx cv csn wcel vx cv vx vex snid vx cv vz cv wcel vy cv vz cv wcel
      wi vx cv vx cv csn wcel vy cv vx cv csn wcel wi vz vx cv csn vx cv snex
      vz cv vx cv csn wceq vx cv vz cv wcel vx cv vx cv csn wcel vy cv vz cv
      wcel vy cv vx cv csn wcel vz cv vx cv csn vx cv eleq2 vz cv vx cv csn vy
      cv eleq2 imbi12d spcv mpi vy cv vx cv csn wcel vy cv vx cv wceq vx cv vy
      cv wceq vy vx cv elsn vy vx equcomi sylbi syl $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Classes are subclasses if and only if their power classes are
       subclasses.  Exercise 18 of [TakeutiZaring] p. 18.  (Contributed by NM,
       13-Oct-1996.) $)
    sspwb $p |- ( A C_ B <-> ~P A C_ ~P B ) $=
      cA cB wss cA cpw cB cpw wss cA cB wss vx cA cpw cB cpw cA cB wss vx cv cA
      wss vx cv cB wss vx cv cA cpw wcel vx cv cB cpw wcel vx cv cA wss cA cB
      wss vx cv cB wss vx cv cA cB sstr2 com12 vx cv cA vx vex elpw vx cv cB vx
      vex elpw 3imtr4g ssrdv cA cpw cB cpw wss vx cA cB cA cpw cB cpw wss vx cv
      csn cA cpw wcel vx cv csn cB cpw wcel vx cv cA wcel vx cv cB wcel cA cpw
      cB cpw vx cv csn ssel vx cv csn cA cpw wcel vx cv csn cA wss vx cv cA
      wcel vx cv csn cA vx cv snex elpw vx cv cA vx vex snss bitr4i vx cv csn
      cB cpw wcel vx cv csn cB wss vx cv cB wcel vx cv csn cB vx cv snex elpw
      vx cv cB vx vex snss bitr4i 3imtr3g ssrdv impbii $.
  $}

  ${
    $d A x y $.
    $( A class equals the union of its power class.  Exercise 6(a) of
       [Enderton] p. 38.  (Contributed by NM, 14-Oct-1996.)  (Proof shortened
       by Alan Sare, 28-Dec-2008.) $)
    unipw $p |- U. ~P A = A $=
      vx cA cpw cuni cA vx cv cA cpw cuni wcel vx cv cA wcel vx cv cA cpw cuni
      wcel vx cv vy cv wcel vy cv cA cpw wcel wa vy wex vx cv cA wcel vy vx cv
      cA cpw eluni vx cv vy cv wcel vy cv cA cpw wcel wa vx cv cA wcel vy vx cv
      vy cv cA elelpwi exlimiv sylbi vx cv cA wcel vx cv vx cv csn wcel vx cv
      csn cA cpw wcel vx cv cA cpw cuni wcel vx cv vx vex snid vx cv cA snelpwi
      vx cv vx cv csn cA cpw elunii sylancr impbii eqriv $.
  $}

  $( Membership of a power class.  Exercise 10 of [Enderton] p. 26.
     (Contributed by NM, 13-Jan-2007.) $)
  pwel $p |- ( A e. B -> ~P A e. ~P ~P U. B ) $=
    cA cB wcel cA cpw cB cuni cpw cpw wcel cA cpw cB cuni cpw wss cA cB wcel cA
    cB cuni wss cA cpw cB cuni cpw wss cA cB elssuni cA cB cuni sspwb sylib cA
    cB wcel cA cpw cvv wcel cA cpw cB cuni cpw cpw wcel cA cpw cB cuni cpw wss
    wb cA cB pwexg cA cpw cB cuni cpw cvv elpwg syl mpbird $.

  $( A class is transitive iff its power class is transitive.  (Contributed by
     Alan Sare, 25-Aug-2011.)  (Revised by Mario Carneiro, 15-Jun-2014.) $)
  pwtr $p |- ( Tr A <-> Tr ~P A ) $=
    cA cpw cuni cA cpw wss cA cA cpw wss cA cpw wtr cA wtr cA cpw cuni cA cA
    cpw cA unipw sseq1i cA cpw df-tr cA dftr4 3bitr4ri $.

  ${
    $d A x $.  $d B x $.
    $( An extensionality-like principle defining subclass in terms of subsets.
       (Contributed by NM, 30-Jun-2004.) $)
    ssextss $p |- ( A C_ B <-> A. x ( x C_ A -> x C_ B ) ) $=
      cA cB wss cA cpw cB cpw wss vx cv cA cpw wcel vx cv cB cpw wcel wi vx wal
      vx cv cA wss vx cv cB wss wi vx wal cA cB sspwb vx cA cpw cB cpw dfss2 vx
      cv cA cpw wcel vx cv cB cpw wcel wi vx cv cA wss vx cv cB wss wi vx vx cv
      cA cpw wcel vx cv cA wss vx cv cB cpw wcel vx cv cB wss vx cv cA vx vex
      elpw vx cv cB vx vex elpw imbi12i albii 3bitri $.

    $( An extensionality-like principle that uses the subset instead of the
       membership relation: two classes are equal iff they have the same
       subsets.  (Contributed by NM, 30-Jun-2004.) $)
    ssext $p |- ( A = B <-> A. x ( x C_ A <-> x C_ B ) ) $=
      cA cB wss cB cA wss wa vx cv cA wss vx cv cB wss wi vx wal vx cv cB wss
      vx cv cA wss wi vx wal wa cA cB wceq vx cv cA wss vx cv cB wss wb vx wal
      cA cB wss vx cv cA wss vx cv cB wss wi vx wal cB cA wss vx cv cB wss vx
      cv cA wss wi vx wal vx cA cB ssextss vx cB cA ssextss anbi12i cA cB eqss
      vx cv cA wss vx cv cB wss vx albiim 3bitr4i $.

    $( Negation of subclass relationship.  Compare ~ nss .  (Contributed by NM,
       30-Jun-2004.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    nssss $p |- ( -. A C_ B <-> E. x ( x C_ A /\ -. x C_ B ) ) $=
      vx cv cA wss vx cv cB wss wn wa vx wex cA cB wss wn vx cv cA wss vx cv cB
      wss wn wa vx wex vx cv cA wss vx cv cB wss wi vx wal cA cB wss vx cv cA
      wss vx cv cB wss vx exanali vx cA cB ssextss xchbinxr bicomi $.
  $}

  $( Classes are equal if and only if their power classes are equal.  Exercise
     19 of [TakeutiZaring] p. 18.  (Contributed by NM, 13-Oct-1996.) $)
  pweqb $p |- ( A = B <-> ~P A = ~P B ) $=
    cA cB wss cB cA wss wa cA cpw cB cpw wss cB cpw cA cpw wss wa cA cB wceq cA
    cpw cB cpw wceq cA cB wss cA cpw cB cpw wss cB cA wss cB cpw cA cpw wss cA
    cB sspwb cB cA sspwb anbi12i cA cB eqss cA cpw cB cpw eqss 3bitr4i $.

  ${
    $d x A $.
    intid.1 $e |- A e. _V $.
    $( The intersection of all sets to which a set belongs is the singleton of
       that set.  (Contributed by NM, 5-Jun-2009.) $)
    intid $p |- |^| { x | A e. x } = { A } $=
      cA vx cv wcel vx cab cint cA csn cA csn cvv wcel cA vx cv wcel vx cab
      cint cA csn wss cA snex cA vx cv wcel cA cA csn wcel vx cA csn cvv vx cv
      cA csn cA eleq2 cA intid.1 snid intmin3 ax-mp cA cA vx cv wcel vx cab
      cint wcel cA csn cA vx cv wcel vx cab cint wss cA cA vx cv wcel vx cab
      cint wcel cA vx cv wcel cA vx cv wcel wi vx cA vx cv wcel vx cA intid.1
      elintab cA vx cv wcel id mpgbir cA cA vx cv wcel vx cab cint snssi ax-mp
      eqssi $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( "At most one" existence implies a class abstraction exists.
       (Contributed by NM, 30-Dec-1996.) $)
    moabex $p |- ( E* x ph -> { x | ph } e. _V ) $=
      wph vx wmo wph vx cv vy cv wceq wi vx wal vy wex wph vx cab cvv wcel wph
      vx vy wph vy nfv mo2 wph vx cv vy cv wceq wi vx wal wph vx cab cvv wcel
      vy wph vx cv vy cv wceq wi vx wal wph vx cab vy cv csn wss wph vx cab cvv
      wcel wph vx cab vy cv csn wss wph vx cv vy cv csn wcel wi vx wal wph vx
      cv vy cv wceq wi vx wal wph vx vy cv csn abss wph vx cv vy cv csn wcel wi
      wph vx cv vy cv wceq wi vx vx cv vy cv csn wcel vx cv vy cv wceq wph vx
      vy cv elsn imbi2i albii bitri wph vx cab vy cv csn vy cv snex ssex sylbir
      exlimiv sylbi $.
  $}

  $( Restricted "at most one" existence implies a restricted class abstraction
     exists.  (Contributed by NM, 17-Jun-2017.) $)
  rmorabex $p |- ( E* x e. A ph -> { x e. A | ph } e. _V ) $=
    vx cv cA wcel wph wa vx wmo vx cv cA wcel wph wa vx cab cvv wcel wph vx cA
    wrmo wph vx cA crab cvv wcel vx cv cA wcel wph wa vx moabex wph vx cA
    df-rmo wph vx cA crab vx cv cA wcel wph wa vx cab cvv wph vx cA df-rab
    eleq1i 3imtr4i $.

  $( The abstraction of a wff with existential uniqueness exists.  (Contributed
     by NM, 25-Nov-1994.) $)
  euabex $p |- ( E! x ph -> { x | ph } e. _V ) $=
    wph vx weu wph vx wmo wph vx cab cvv wcel wph vx eumo wph vx moabex syl $.

  ${
    $d x y A $.
    $( A non-empty class (even if proper) has a non-empty subset.  (Contributed
       by NM, 23-Aug-2003.) $)
    nnullss $p |- ( A =/= (/) -> E. x ( x C_ A /\ x =/= (/) ) ) $=
      cA c0 wne vy cv cA wcel vy wex vx cv cA wss vx cv c0 wne wa vx wex vy cA
      n0 vy cv cA wcel vx cv cA wss vx cv c0 wne wa vx wex vy vy cv cA wcel vy
      cv csn cA wss vx cv cA wss vx cv c0 wne wa vx wex vy cv cA vy vex snss vy
      cv csn cA wss vy cv csn c0 wne vx cv cA wss vx cv c0 wne wa vx wex vy cv
      vy vex snnz vx cv cA wss vx cv c0 wne wa vy cv csn cA wss vy cv csn c0
      wne wa vx vy cv csn vy cv snex vx cv vy cv csn wceq vx cv cA wss vy cv
      csn cA wss vx cv c0 wne vy cv csn c0 wne vx cv vy cv csn cA sseq1 vx cv
      vy cv csn c0 neeq1 anbi12d spcev mpan2 sylbi exlimiv sylbi $.
  $}

  ${
    $d x y z A $.  $d y z ph $.
    $( Restricted existence in a class (even if proper) implies restricted
       existence in a subset.  (Contributed by NM, 23-Aug-2003.) $)
    exss $p |- ( E. x e. A ph -> E. y ( y C_ A /\ E. x e. y ph ) ) $=
      wph vx cA wrex vz cv vx cv cA wcel wph wa vx cab wcel vz wex vy cv cA wss
      wph vx vy cv wrex wa vy wex wph vx cA crab c0 wne vx cv cA wcel wph wa vx
      cab c0 wne wph vx cA wrex vz cv vx cv cA wcel wph wa vx cab wcel vz wex
      wph vx cA crab vx cv cA wcel wph wa vx cab c0 wph vx cA df-rab neeq1i wph
      vx cA rabn0 vz vx cv cA wcel wph wa vx cab n0 3bitr3i vz cv vx cv cA wcel
      wph wa vx cab wcel vy cv cA wss wph vx vy cv wrex wa vy wex vz vz cv vx
      cv cA wcel wph wa vx cab wcel vz cv csn cA wss wph vx vz cv csn wrex vy
      cv cA wss wph vx vy cv wrex wa vy wex vz cv vx cv cA wcel wph wa vx cab
      wcel vz cv csn vx cv cA wcel wph wa vx cab wss vz cv csn cA wss vz cv vx
      cv cA wcel wph wa vx cab vz vex snss vz cv csn vx cv cA wcel wph wa vx
      cab wss vx cv cA wcel wph wa vx cab cA wss vz cv csn cA wss wph vx cA
      ssab2 vz cv csn vx cv cA wcel wph wa vx cab cA sstr2 mpi sylbi vz cv vx
      cv cA wcel wph wa vx cab wcel wph vx vz cv csn crab c0 wne wph vx vz cv
      csn wrex vz cv vx cv cA wcel wph wa vx cab wcel vz cv wph vx vz cv csn
      crab wcel wph vx vz cv csn crab c0 wne vx cv cA wcel vx vz wsb wph vx vz
      wsb wa vx cv vz cv csn wcel vx vz wsb wph vx vz wsb wa vz cv vx cv cA
      wcel wph wa vx cab wcel vz cv wph vx vz cv csn crab wcel vx cv cA wcel vx
      vz wsb wph vx vz wsb wa wph vx vz wsb vx cv vz cv csn wcel vx vz wsb vx
      cv cA wcel vx vz wsb wph vx vz wsb simpr vx cv vz cv csn wcel vx vz wsb
      vx cv vz cv wceq vx vz wsb vx vz equsb1 vx cv vz cv csn wcel vx cv vz cv
      wceq vx vz vx vz cv elsn sbbii mpbir jctil vz cv vx cv cA wcel wph wa vx
      cab wcel vx cv cA wcel wph wa vx vz wsb vx cv cA wcel vx vz wsb wph vx vz
      wsb wa vx cv cA wcel wph wa vz vx df-clab vx cv cA wcel wph vx vz sban
      bitri vz cv wph vx vz cv csn crab wcel vz cv vx cv vz cv csn wcel wph wa
      vx cab wcel vx cv vz cv csn wcel vx vz wsb wph vx vz wsb wa wph vx vz cv
      csn crab vx cv vz cv csn wcel wph wa vx cab vz cv wph vx vz cv csn df-rab
      eleq2i vz cv vx cv vz cv csn wcel wph wa vx cab wcel vx cv vz cv csn wcel
      wph wa vx vz wsb vx cv vz cv csn wcel vx vz wsb wph vx vz wsb wa vx cv vz
      cv csn wcel wph wa vz vx df-clab vx cv vz cv csn wcel wph vx vz sban
      bitri bitri 3imtr4i wph vx vz cv csn crab vz cv ne0i syl wph vx vz cv csn
      rabn0 sylib vy cv cA wss wph vx vy cv wrex wa vz cv csn cA wss wph vx vz
      cv csn wrex wa vy vz cv csn vz cv snex vy cv vz cv csn wceq vy cv cA wss
      vz cv csn cA wss wph vx vy cv wrex wph vx vz cv csn wrex vy cv vz cv csn
      cA sseq1 wph vx vy cv vz cv csn rexeq anbi12d spcev syl2anc exlimiv sylbi
      $.
  $}

  $( An ordered pair of classes is a set.  Exercise 7 of [TakeutiZaring]
     p. 16.  (Contributed by NM, 18-Aug-1993.)  (Revised by Mario Carneiro,
     26-Apr-2015.) $)
  opex $p |- <. A , B >. e. _V $=
    cA cB cop cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif cvv cA cB
    dfopif cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cA csn cA cB cpr
    prex 0ex ifex eqeltri $.

  $( An ordered triple of classes is a set.  (Contributed by NM,
     3-Apr-2015.) $)
  otex $p |- <. A , B , C >. e. _V $=
    cA cB cC cotp cA cB cop cC cop cvv cA cB cC df-ot cA cB cop cC opex eqeltri
    $.

  ${
    elop.1 $e |- A e. _V $.
    elop.2 $e |- B e. _V $.
    elop.3 $e |- C e. _V $.
    $( An ordered pair has two elements.  Exercise 3 of [TakeutiZaring] p. 15.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    elop $p |- ( A e. <. B , C >. <-> ( A = { B } \/ A = { B , C } ) ) $=
      cA cB cC cop wcel cA cB csn cB cC cpr cpr wcel cA cB csn wceq cA cB cC
      cpr wceq wo cB cC cop cB csn cB cC cpr cpr cA cB cC elop.2 elop.3 dfop
      eleq2i cA cB csn cB cC cpr elop.1 elpr bitri $.
  $}

  ${
    opi1.1 $e |- A e. _V $.
    opi1.2 $e |- B e. _V $.
    $( One of the two elements in an ordered pair.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    opi1 $p |- { A } e. <. A , B >. $=
      cA csn cA csn cA cB cpr cpr cA cB cop cA csn cA cB cpr cA snex prid1 cA
      cB opi1.1 opi1.2 dfop eleqtrri $.

    $( One of the two elements of an ordered pair.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    opi2 $p |- { A , B } e. <. A , B >. $=
      cA cB cpr cA csn cA cB cpr cpr cA cB cop cA csn cA cB cpr cA cB prex
      prid2 cA cB opi1.1 opi1.2 dfop eleqtrri $.
  $}


