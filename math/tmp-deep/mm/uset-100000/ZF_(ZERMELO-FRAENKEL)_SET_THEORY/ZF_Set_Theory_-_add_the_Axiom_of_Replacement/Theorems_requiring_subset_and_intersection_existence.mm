
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Derive_the_Null_Set_Axiom.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Theorems requiring subset and intersection existence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x y z $.
    $( No set contains all sets.  Theorem 41 of [Suppes] p. 30.  (Contributed
       by NM, 23-Aug-1993.) $)
    nalset $p |- -. E. x A. y y e. x $=
      vy cv vx cv wcel wn vy wex vy cv vx cv wcel vy wal vx wex wn vx vy cv vx
      cv wcel vx vy alexn vz cv vy cv wcel vz cv vx cv wcel vz cv vz cv wcel wn
      wa wb vz wal vy wex vy cv vx cv wcel wn vy wex vz cv vz cv wcel wn vz vy
      vx ax-sep vz cv vy cv wcel vz cv vx cv wcel vz cv vz cv wcel wn wa wb vz
      wal vy cv vx cv wcel wn vy vz cv vy cv wcel vz cv vx cv wcel vz cv vz cv
      wcel wn wa wb vz wal vy cv vy cv wcel vy cv vx cv wcel vy cv vy cv wcel
      wn wa wb vy cv vx cv wcel wn vz cv vy cv wcel vz cv vx cv wcel vz cv vz
      cv wcel wn wa wb vy cv vy cv wcel vy cv vx cv wcel vy cv vy cv wcel wn wa
      wb vz vy vz cv vy cv wceq vz cv vy cv wcel vy cv vy cv wcel vz cv vx cv
      wcel vz cv vz cv wcel wn wa vy cv vx cv wcel vy cv vy cv wcel wn wa vz vy
      vy elequ1 vz cv vy cv wceq vz cv vx cv wcel vy cv vx cv wcel vz cv vz cv
      wcel wn vy cv vy cv wcel wn vz vy vx elequ1 vz cv vy cv wceq vz cv vz cv
      wcel vy cv vy cv wcel vz cv vy cv wceq vz cv vz cv wcel vy cv vz cv wcel
      vy cv vy cv wcel vz vy vz elequ1 vz vy vy elequ2 bitrd notbid anbi12d
      bibi12d spv vy cv vy cv wcel vy cv vx cv wcel pclem6 syl eximi ax-mp
      mpgbi $.
  $}

  ${
    $d x y $.
    $( The universal class is not a member of itself (and thus is not a set).
       Proposition 5.21 of [TakeutiZaring] p. 21; our proof, however, does not
       depend on the Axiom of Regularity.  (Contributed by NM, 23-Aug-1993.) $)
    vprc $p |- -. _V e. _V $=
      cvv cvv wcel vx cv cvv wceq vx wex vy cv vx cv wcel vy wal vx wex vx cv
      cvv wceq vx wex vx vy nalset vy cv vx cv wcel vy wal vx cv cvv wceq vx vy
      cv vx cv wcel vy wal vy cv vx cv wcel vy cv cvv wcel wb vy wal vx cv cvv
      wceq vy cv vx cv wcel vy cv vx cv wcel vy cv cvv wcel wb vy vy cv cvv
      wcel vy cv vx cv wcel vy vex tbt albii vy vx cv cvv dfcleq bitr4i exbii
      mtbi vx cvv isset mtbir $.
  $}

  $( The universal class doesn't belong to any class.  (Contributed by FL,
     31-Dec-2006.) $)
  nvel $p |- -. _V e. A $=
    cvv cA wcel cvv cvv wcel vprc cvv cA elex mto $.

  $( The universal class does not exist.  (Contributed by NM, 4-Jul-2005.) $)
  vnex $p |- -. E. x x = _V $=
    cvv cvv wcel vx cv cvv wceq vx wex vprc vx cvv isset mtbi $.

  ${
    $d A x y $.  $d B x y $.
    inex1.1 $e |- A e. _V $.
    $( Separation Scheme (Aussonderung) using class notation.  Compare Exercise
       4 of [TakeutiZaring] p. 22.  (Contributed by NM, 5-Aug-1993.) $)
    inex1 $p |- ( A i^i B ) e. _V $=
      vx cA cB cin vx cv cA cB cin wceq vx wex vy cv vx cv wcel vy cv cA wcel
      vy cv cB wcel wa wb vy wal vx wex vy cv cB wcel vy vx cA inex1.1 zfauscl
      vx cv cA cB cin wceq vy cv vx cv wcel vy cv cA wcel vy cv cB wcel wa wb
      vy wal vx vx cv cA cB cin wceq vy cv vx cv wcel vy cv cA cB cin wcel wb
      vy wal vy cv vx cv wcel vy cv cA wcel vy cv cB wcel wa wb vy wal vy vx cv
      cA cB cin dfcleq vy cv vx cv wcel vy cv cA cB cin wcel wb vy cv vx cv
      wcel vy cv cA wcel vy cv cB wcel wa wb vy vy cv cA cB cin wcel vy cv cA
      wcel vy cv cB wcel wa vy cv vx cv wcel vy cv cA cB elin bibi2i albii
      bitri exbii mpbir issetri $.
  $}

  ${
    inex2.1 $e |- A e. _V $.
    $( Separation Scheme (Aussonderung) using class notation.  (Contributed by
       NM, 27-Apr-1994.) $)
    inex2 $p |- ( B i^i A ) e. _V $=
      cB cA cin cA cB cin cvv cB cA incom cA cB inex2.1 inex1 eqeltri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Closed-form, generalized Separation Scheme.  (Contributed by NM,
       7-Apr-1995.) $)
    inex1g $p |- ( A e. V -> ( A i^i B ) e. _V ) $=
      vx cv cB cin cvv wcel cA cB cin cvv wcel vx cA cV vx cv cA wceq vx cv cB
      cin cA cB cin cvv vx cv cA cB ineq1 eleq1d vx cv cB vx vex inex1 vtoclg
      $.
  $}

  ${
    ssex.1 $e |- B e. _V $.
    $( The subset of a set is also a set.  Exercise 3 of [TakeutiZaring]
       p. 22.  This is one way to express the Axiom of Separation ~ ax-sep
       (a.k.a.  Subset Axiom).  (Contributed by NM, 27-Apr-1994.) $)
    ssex $p |- ( A C_ B -> A e. _V ) $=
      cA cB wss cA cB cin cA wceq cA cvv wcel cA cB df-ss cA cB cin cA wceq cA
      cB cin cvv wcel cA cvv wcel cB cA ssex.1 inex2 cA cB cin cA cvv eleq1
      mpbii sylbi $.
  $}

  ${
    ssexi.1 $e |- B e. _V $.
    ssexi.2 $e |- A C_ B $.
    $( The subset of a set is also a set.  (Contributed by NM, 9-Sep-1993.) $)
    ssexi $p |- A e. _V $=
      cA cB wss cA cvv wcel ssexi.2 cA cB ssexi.1 ssex ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The subset of a set is also a set.  Exercise 3 of [TakeutiZaring] p. 22
       (generalized).  (Contributed by NM, 14-Aug-1994.) $)
    ssexg $p |- ( ( A C_ B /\ B e. C ) -> A e. _V ) $=
      cB cC wcel cA cB wss cA cvv wcel cA vx cv wss cA cvv wcel wi cA cB wss cA
      cvv wcel wi vx cB cC vx cv cB wceq cA vx cv wss cA cB wss cA cvv wcel vx
      cv cB cA sseq2 imbi1d cA vx cv vx vex ssex vtoclg impcom $.
  $}

  ${
    ssexd.1 $e |- ( ph -> B e. C ) $.
    ssexd.2 $e |- ( ph -> A C_ B ) $.
    $( A subclass of a set is a set.  Deduction form of ~ ssexg .  (Contributed
       by David Moews, 1-May-2017.) $)
    ssexd $p |- ( ph -> A e. _V ) $=
      wph cA cB wss cB cC wcel cA cvv wcel ssexd.2 ssexd.1 cA cB cC ssexg
      syl2anc $.
  $}

  $( Existence of a difference.  (Contributed by NM, 26-May-1998.) $)
  difexg $p |- ( A e. V -> ( A \ B ) e. _V ) $=
    cA cB cdif cA wss cA cV wcel cA cB cdif cvv wcel cA cB difss cA cB cdif cA
    cV ssexg mpan $.

  ${
    $d x y A $.  $d y ph $.
    zfausab.1 $e |- A e. _V $.
    $( Separation Scheme (Aussonderung) in terms of a class abstraction.
       (Contributed by NM, 8-Jun-1994.) $)
    zfausab $p |- { x | ( x e. A /\ ph ) } e. _V $=
      vx cv cA wcel wph wa vx cab cA zfausab.1 wph vx cA ssab2 ssexi $.
  $}

  ${
    $d x A $.
    $( Separation Scheme in terms of a restricted class abstraction.
       (Contributed by NM, 23-Oct-1999.) $)
    rabexg $p |- ( A e. V -> { x e. A | ph } e. _V ) $=
      wph vx cA crab cA wss cA cV wcel wph vx cA crab cvv wcel wph vx cA ssrab2
      wph vx cA crab cA cV ssexg mpan $.
  $}

  ${
    $d x A $.
    rabex.1 $e |- A e. _V $.
    $( Separation Scheme in terms of a restricted class abstraction.
       (Contributed by NM, 19-Jul-1996.) $)
    rabex $p |- { x e. A | ph } e. _V $=
      cA cvv wcel wph vx cA crab cvv wcel rabex.1 wph vx cA cvv rabexg ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    elssabg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction involving a subset.  Unlike ~ elabg ,
       ` A ` does not have to be a set.  (Contributed by NM, 29-Aug-2006.) $)
    elssabg $p |- ( B e. V ->
                  ( A e. { x | ( x C_ B /\ ph ) } <-> ( A C_ B /\ ps ) ) ) $=
      cB cV wcel cA cB wss wps wa cA cvv wcel wi cA vx cv cB wss wph wa vx cab
      wcel cA cB wss wps wa wb cB cV wcel cA cB wss cA cvv wcel wps cA cB wss
      cB cV wcel cA cvv wcel cA cB cV ssexg expcom adantrd vx cv cB wss wph wa
      cA cB wss wps wa vx cA cvv vx cv cA wceq vx cv cB wss cA cB wss wph wps
      vx cv cA cB sseq1 elssabg.1 anbi12d elab3g syl $.
  $}

  ${
    $d x A $.
    $( The intersection of a non-empty class exists.  Exercise 5 of
       [TakeutiZaring] p. 44 and its converse.  (Contributed by NM,
       13-Aug-2002.) $)
    intex $p |- ( A =/= (/) <-> |^| A e. _V ) $=
      cA c0 wne cA cint cvv wcel cA c0 wne vx cv cA wcel vx wex cA cint cvv
      wcel vx cA n0 vx cv cA wcel cA cint cvv wcel vx vx cv cA wcel cA cint vx
      cv wss cA cint cvv wcel vx cv cA intss1 cA cint vx cv vx vex ssex syl
      exlimiv sylbi cA cint cvv wcel cA c0 cA c0 wceq cA cint cvv wcel cvv cvv
      wcel vprc cA c0 wceq cA cint cvv cvv cA c0 wceq cA cint c0 cint cvv cA c0
      inteq int0 syl6eq eleq1d mtbiri necon2ai impbii $.
  $}

  $( If a class intersection is not a set, it must be the universe.
     (Contributed by NM, 3-Jul-2005.) $)
  intnex $p |- ( -. |^| A e. _V <-> |^| A = _V ) $=
    cA cint cvv wcel wn cA cint cvv wceq cA cint cvv wcel wn cA c0 wceq cA cint
    cvv wceq cA cint cvv wcel cA c0 cA intex necon1bbii cA c0 wceq cA cint c0
    cint cvv cA c0 inteq int0 syl6eq sylbi cA cint cvv wceq cA cint cvv wcel
    cvv cvv wcel vprc cA cint cvv cvv eleq1 mtbiri impbii $.

  ${
    $d x y $.  $d ph y $.
    $( The intersection of a non-empty class abstraction exists.  (Contributed
       by NM, 21-Oct-2003.) $)
    intexab $p |- ( E. x ph <-> |^| { x | ph } e. _V ) $=
      wph vx wex wph vx cab c0 wne wph vx cab cint cvv wcel wph vx abn0 wph vx
      cab intex bitr3i $.
  $}

  $( The intersection of a non-empty restricted class abstraction exists.
     (Contributed by NM, 21-Oct-2003.) $)
  intexrab $p |- ( E. x e. A ph <-> |^| { x e. A | ph } e. _V ) $=
    vx cv cA wcel wph wa vx wex vx cv cA wcel wph wa vx cab cint cvv wcel wph
    vx cA wrex wph vx cA crab cint cvv wcel vx cv cA wcel wph wa vx intexab wph
    vx cA df-rex wph vx cA crab cint vx cv cA wcel wph wa vx cab cint cvv wph
    vx cA crab vx cv cA wcel wph wa vx cab wph vx cA df-rab inteqi eleq1i
    3bitr4i $.

  ${
    $d A x y $.  $d B y $.
    $( The existence of an indexed union. ` x ` is normally a free-variable
       parameter in ` B ` , which should be read ` B ( x ) ` .  (Contributed by
       FL, 19-Sep-2011.) $)
    iinexg $p |- ( ( A =/= (/) /\ A. x e. A B e. C )
    -> |^|_ x e. A B e. _V ) $=
      cA c0 wne cB cC wcel vx cA wral wa vx cA cB ciin vy cv cB wceq vx cA wrex
      vy cab cint cvv cB cC wcel vx cA wral vx cA cB ciin vy cv cB wceq vx cA
      wrex vy cab cint wceq cA c0 wne vx vy cA cB cC dfiin2g adantl cA c0 wne
      cB cC wcel vx cA wral wa vy cv cB wceq vx cA wrex vy cab c0 wne vy cv cB
      wceq vx cA wrex vy cab cint cvv wcel cA c0 wne cB cC wcel vx cA wral wa
      vy cv cB wceq vx cA wrex vy wex vy cv cB wceq vx cA wrex vy cab c0 wne cA
      c0 wne cB cC wcel vx cA wral wa vy cv cB wceq vy wex vx cA wrex vy cv cB
      wceq vx cA wrex vy wex cA c0 wne cB cC wcel vx cA wral vy cv cB wceq vy
      wex vx cA wrex cA c0 wne cB cC wcel vy cv cB wceq vy wex wi vx cA wrex cB
      cC wcel vx cA wral vy cv cB wceq vy wex vx cA wrex wi cA c0 wne cB cC
      wcel vy cv cB wceq vy wex wi vx cA wral cB cC wcel vy cv cB wceq vy wex
      wi vx cA wrex cB cC wcel vy cv cB wceq vy wex wi vx cA vy cB cC elisset
      rgenw cB cC wcel vy cv cB wceq vy wex wi vx cA r19.2z mpan2 cB cC wcel vy
      cv cB wceq vy wex vx cA r19.35 sylib imp vy cv cB wceq vx vy cA rexcom4
      sylib vy cv cB wceq vx cA wrex vy abn0 sylibr vy cv cB wceq vx cA wrex vy
      cab intex sylib eqeltrd $.
  $}

  ${
    $d x y $.  $d x A $.  $d y ph $.  $d x ps $.  $d x ch $.
    intabs.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    intabs.2 $e |- ( x = |^| { y | ps } -> ( ph <-> ch ) ) $.
    intabs.3 $e |- ( |^| { y | ps } C_ A /\ ch ) $.
    $( Absorption of a redundant conjunct in the intersection of a class
       abstraction.  (Contributed by NM, 3-Jul-2005.) $)
    intabs $p |- |^| { x | ( x C_ A /\ ph ) } = |^| { x | ph } $=
      vx cv cA wss wph wa vx cab cint wph vx cab cint vx cv cA wss wph wa vx
      cab cint wps vy cab cint wph vx cab cint wps vy cab cint cvv wcel vx cv
      cA wss wph wa vx cab cint wps vy cab cint wss vx cv cA wss wph wa wps vy
      cab cint cA wss wch wa vx wps vy cab cint cvv vx cv wps vy cab cint wceq
      vx cv cA wss wps vy cab cint cA wss wph wch vx cv wps vy cab cint cA
      sseq1 intabs.2 anbi12d intabs.3 intmin3 wps vy cab cint cvv wcel wn wps
      vy cab cint cvv wceq vx cv cA wss wph wa vx cab cint wps vy cab cint wss
      wps vy cab intnex wps vy cab cint cvv wceq vx cv cA wss wph wa vx cab
      cint wps vy cab cint wss vx cv cA wss wph wa vx cab cint cvv wss vx cv cA
      wss wph wa vx cab cint ssv wps vy cab cint cvv vx cv cA wss wph wa vx cab
      cint sseq2 mpbiri sylbi pm2.61i wph vx cab wps vy cab wph wps vx vy
      intabs.1 cbvabv inteqi sseqtr4i vx cv cA wss wph wa vx cab wph vx cab wss
      wph vx cab cint vx cv cA wss wph wa vx cab cint wss vx cv cA wss wph wa
      wph vx vx cv cA wss wph simpr ss2abi vx cv cA wss wph wa vx cab wph vx
      cab intss ax-mp eqssi $.
  $}

  ${
    $d A x y z $.  $d B x y z $.
    $( The intersection of a union ` U. A ` with a class ` B ` is equal to the
       union of the intersections of each element of ` A ` with ` B ` .
       (Contributed by FL, 24-Mar-2007.) $)
    inuni $p |- ( U. A i^i B ) = U. { x | E. y e. A x = ( y i^i B ) } $=
      vz cA cuni cB cin vx cv vy cv cB cin wceq vy cA wrex vx cab cuni vz cv cA
      cuni cB cin wcel vz cv vx cv wcel vx cv vy cv cB cin wceq vy cA wrex wa
      vx wex vz cv vx cv vy cv cB cin wceq vy cA wrex vx cab cuni wcel vz cv cA
      cuni wcel vz cv cB wcel wa vz cv vy cv wcel vy cA wrex vz cv cB wcel wa
      vz cv cA cuni cB cin wcel vz cv vx cv wcel vx cv vy cv cB cin wceq vy cA
      wrex wa vx wex vz cv cA cuni wcel vz cv vy cv wcel vy cA wrex vz cv cB
      wcel vy vz cv cA eluni2 anbi1i vz cv cA cuni cB elin vz cv vx cv wcel vx
      cv vy cv cB cin wceq vy cA wrex wa vx wex vx cv vy cv cB cin wceq vz cv
      vx cv wcel wa vx wex vy cA wrex vz cv vy cv wcel vy cA wrex vz cv cB wcel
      wa vz cv vx cv wcel vx cv vy cv cB cin wceq vy cA wrex wa vx wex vx cv vy
      cv cB cin wceq vz cv vx cv wcel wa vy cA wrex vx wex vx cv vy cv cB cin
      wceq vz cv vx cv wcel wa vx wex vy cA wrex vz cv vx cv wcel vx cv vy cv
      cB cin wceq vy cA wrex wa vx cv vy cv cB cin wceq vz cv vx cv wcel wa vy
      cA wrex vx vz cv vx cv wcel vx cv vy cv cB cin wceq vy cA wrex wa vx cv
      vy cv cB cin wceq vy cA wrex vz cv vx cv wcel wa vx cv vy cv cB cin wceq
      vz cv vx cv wcel wa vy cA wrex vz cv vx cv wcel vx cv vy cv cB cin wceq
      vy cA wrex ancom vx cv vy cv cB cin wceq vz cv vx cv wcel vy cA r19.41v
      bitr4i exbii vx cv vy cv cB cin wceq vz cv vx cv wcel wa vy vx cA rexcom4
      bitr4i vx cv vy cv cB cin wceq vz cv vx cv wcel wa vx wex vy cA wrex vz
      cv vy cv wcel vz cv cB wcel wa vy cA wrex vz cv vy cv wcel vy cA wrex vz
      cv cB wcel wa vx cv vy cv cB cin wceq vz cv vx cv wcel wa vx wex vz cv vy
      cv wcel vz cv cB wcel wa vy cA vx cv vy cv cB cin wceq vz cv vx cv wcel
      wa vx wex vz cv vy cv cB cin wcel vz cv vy cv wcel vz cv cB wcel wa vz cv
      vx cv wcel vz cv vy cv cB cin wcel vx vy cv cB cin vy cv cB vy vex inex1
      vx cv vy cv cB cin vz cv eleq2 ceqsexv vz cv vy cv cB elin bitri rexbii
      vz cv vy cv wcel vz cv cB wcel vy cA r19.41v bitri bitri 3bitr4i vx cv vy
      cv cB cin wceq vy cA wrex vx vz cv eluniab bitr4i eqriv $.
  $}

  $( Membership in a power class.  Theorem 86 of [Suppes] p. 47.  (Contributed
     by NM, 7-Aug-2000.) $)
  elpw2g $p |- ( B e. V -> ( A e. ~P B <-> A C_ B ) ) $=
    cB cV wcel cA cB cpw wcel cA cB wss cA cB elpwi cA cB wss cB cV wcel cA cB
    cpw wcel cA cB wss cB cV wcel cA cvv wcel cA cB cpw wcel cA cB cV ssexg cA
    cvv wcel cA cB cpw wcel cA cB wss cA cB cvv elpwg biimparc syldan expcom
    impbid2 $.

  ${
    elpw2.1 $e |- B e. _V $.
    $( Membership in a power class.  Theorem 86 of [Suppes] p. 47.
       (Contributed by NM, 11-Oct-2007.) $)
    elpw2 $p |- ( A e. ~P B <-> A C_ B ) $=
      cB cvv wcel cA cB cpw wcel cA cB wss wb elpw2.1 cA cB cvv elpw2g ax-mp $.
  $}


  ${
    $d A x y $.  $d V x y $.
    $( The power set of a set is never a subset.  (Contributed by Stefan
       O'Rear, 22-Feb-2015.) $)
    pwnss $p |- ( A e. V -> -. ~P A C_ A ) $=
      cA cpw cA wss vx cv vx cv wnel vx cA crab cA cpw wcel cA cV wcel cA cpw
      cA wss vx cv vx cv wnel vx cA crab cA cpw wcel vx cv vx cv wnel vx cA
      crab cA wcel vx cv vx cv wnel vx cA crab vx cv vx cv wnel vx cA crab wcel
      vx cv vx cv wnel vx cA crab cA wcel vx cv vx cv wnel vx cA crab vx cv vx
      cv wnel vx cA crab wcel wn wa wb vx cv vx cv wnel vx cA crab cA wcel wn
      vy cv vy cv wcel wn vx cv vx cv wnel vx cA crab vx cv vx cv wnel vx cA
      crab wcel wn vy vx cv vx cv wnel vx cA crab cA vx cv vx cv wnel vx cA
      crab vy cv vx cv vx cv wnel vx cA crab wceq vy cv vy cv wcel vx cv vx cv
      wnel vx cA crab vx cv vx cv wnel vx cA crab wcel vy cv vx cv vx cv wnel
      vx cA crab wceq vy cv vy cv wcel vx cv vx cv wnel vx cA crab vx cv vx cv
      wnel vx cA crab wcel wb vy cv vx cv vx cv wnel vx cA crab vy cv vx cv vx
      cv wnel vx cA crab eleq12 anidms notbid vx cv vx cv wnel vy cv vy cv wcel
      wn vx vy cA vx cv vx cv wnel vx cv vx cv wcel wn vx cv vy cv wceq vy cv
      vy cv wcel wn vx cv vx cv df-nel vx cv vy cv wceq vx cv vx cv wcel vy cv
      vy cv wcel vx cv vy cv wceq vx cv vx cv wcel vy cv vy cv wcel wb vx cv vy
      cv vx cv vy cv eleq12 anidms notbid syl5bb cbvrabv elrab2 vx cv vx cv
      wnel vx cA crab vx cv vx cv wnel vx cA crab wcel vx cv vx cv wnel vx cA
      crab cA wcel pclem6 ax-mp cA cpw cA vx cv vx cv wnel vx cA crab ssel mtoi
      cA cV wcel vx cv vx cv wnel vx cA crab cA cpw wcel vx cv vx cv wnel vx cA
      crab cA wss vx cv vx cv wnel vx cA ssrab2 vx cv vx cv wnel vx cA crab cA
      cV elpw2g mpbiri nsyl3 $.
  $}

  $( No set equals its power set.  The sethood antecedent is necessary; compare
     ~ pwv .  (Contributed by NM, 17-Nov-2008.)  (Proof shortened by Mario
     Carneiro, 23-Dec-2016.) $)
  pwne $p |- ( A e. V -> ~P A =/= A ) $=
    cA cV wcel cA cpw cA wss wn cA cpw cA wne cA cV pwnss cA cpw cA wss cA cpw
    cA cA cpw cA eqimss necon3bi syl $.



