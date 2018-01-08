
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_difference,_union,_and_intersection_of_two_classes.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           The empty set

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the symbol for the empty or null set. $)
  $c (/) $. $( null set $)

  $( Extend class notation to include the empty set. $)
  c0 $a class (/) $.

  $( Define the empty set.  Special case of Exercise 4.10(o) of [Mendelson]
     p. 231.  For a more traditional definition, but requiring a dummy
     variable, see ~ dfnul2 .  (Contributed by NM, 5-Aug-1993.) $)
  df-nul $a |- (/) = ( _V \ _V ) $.

  $( Alternate definition of the empty set.  Definition 5.14 of [TakeutiZaring]
     p. 20.  (Contributed by NM, 26-Dec-1996.) $)
  dfnul2 $p |- (/) = { x | -. x = x } $=
    vx cv vx cv wceq wn vx c0 vx cv c0 wcel vx cv cvv cvv cdif wcel vx cv cvv
    wcel vx cv cvv wcel wn wa vx cv vx cv wceq wn c0 cvv cvv cdif vx cv df-nul
    eleq2i vx cv cvv cvv eldif vx cv vx cv wceq vx cv cvv wcel vx cv cvv wcel
    wn wa vx cv vx cv wceq vx cv cvv wcel vx cv cvv wcel wn wa wn vx cv eqid vx
    cv cvv wcel pm3.24 2th con2bii 3bitri abbi2i $.

  $( Alternate definition of the empty set.  (Contributed by NM,
     25-Mar-2004.) $)
  dfnul3 $p |- (/) = { x e. A | -. x e. A } $=
    vx cv vx cv wceq wn vx cab vx cv cA wcel vx cv cA wcel wn wa vx cab c0 vx
    cv cA wcel wn vx cA crab vx cv vx cv wceq wn vx cv cA wcel vx cv cA wcel wn
    wa vx vx cv cA wcel vx cv cA wcel wn wa vx cv vx cv wceq vx cv cA wcel vx
    cv cA wcel wn wa wn vx cv vx cv wceq vx cv cA wcel pm3.24 vx cv eqid 2th
    con1bii abbii vx dfnul2 vx cv cA wcel wn vx cA df-rab 3eqtr4i $.

  $( The empty set has no elements.  Theorem 6.14 of [Quine] p. 44.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Mario Carneiro,
     1-Sep-2015.) $)
  noel $p |- -. A e. (/) $=
    cA c0 wcel cA cvv cvv cdif wcel cA cvv cvv cdif wcel cA cvv wcel cA cvv cvv
    eldifi cA cvv cvv eldifn pm2.65i c0 cvv cvv cdif cA df-nul eleq2i mtbir $.

  $( If a set has elements, it is not empty.  (Contributed by NM,
     31-Dec-1993.) $)
  n0i $p |- ( B e. A -> -. A = (/) ) $=
    cA c0 wceq cB cA wcel cA c0 wceq cB cA wcel cB c0 wcel cB noel cA c0 cB
    eleq2 mtbiri con2i $.

  $( If a set has elements, it is not empty.  (Contributed by NM,
     31-Dec-1993.) $)
  ne0i $p |- ( B e. A -> A =/= (/) ) $=
    cB cA wcel cA c0 wceq wn cA c0 wne cA cB n0i cA c0 df-ne sylibr $.

  $( The universal class is not equal to the empty set.  (Contributed by NM,
     11-Sep-2008.) $)
  vn0 $p |- _V =/= (/) $=
    vx cv cvv wcel cvv c0 wne vx vex cvv vx cv ne0i ax-mp $.

  ${
    $d x y $.  $d y A $.
    n0f.1 $e |- F/_ x A $.
    $( A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  This version of ~ n0 requires only that ` x `
       not be free in, rather than not occur in, ` A ` .  (Contributed by NM,
       17-Oct-2003.) $)
    n0f $p |- ( A =/= (/) <-> E. x x e. A ) $=
      cA c0 wne vx cv cA wcel wn vx wal wn vx cv cA wcel vx wex vx cv cA wcel
      wn vx wal cA c0 cA c0 wceq vx cv cA wcel vx cv c0 wcel wb vx wal vx cv cA
      wcel wn vx wal vx cA c0 n0f.1 vx c0 nfcv cleqf vx cv cA wcel wn vx cv cA
      wcel vx cv c0 wcel wb vx vx cv c0 wcel vx cv cA wcel vx cv noel nbn albii
      bitr4i necon3abii vx cv cA wcel vx df-ex bitr4i $.
  $}

  ${
    $d x y A $.
    $( A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  (Contributed by NM, 29-Sep-2006.) $)
    n0 $p |- ( A =/= (/) <-> E. x x e. A ) $=
      vx cA vx cA nfcv n0f $.

    $( A nonempty class has at least one element.  Proposition 5.17(1) of
       [TakeutiZaring] p. 20.  (Contributed by NM, 5-Aug-1993.) $)
    neq0 $p |- ( -. A = (/) <-> E. x x e. A ) $=
      cA c0 wceq wn cA c0 wne vx cv cA wcel vx wex cA c0 df-ne vx cA n0 bitr3i
      $.
  $}

  ${
    $d x A $.  $d x ph $.
    reximdva0.1 $e |- ( ( ph /\ x e. A ) -> ps ) $.
    $( Restricted existence deduced from non-empty class.  (Contributed by NM,
       1-Feb-2012.) $)
    reximdva0 $p |- ( ( ph /\ A =/= (/) ) -> E. x e. A ps ) $=
      wph cA c0 wne wa vx cv cA wcel wps wa vx wex wps vx cA wrex cA c0 wne wph
      vx cv cA wcel vx wex vx cv cA wcel wps wa vx wex vx cA n0 wph vx cv cA
      wcel vx wex vx cv cA wcel wps wa vx wex wph vx cv cA wcel vx cv cA wcel
      wps wa vx wph vx cv cA wcel wps wph vx cv cA wcel wps reximdva0.1 ex
      ancld eximdv imp sylan2b wps vx cA df-rex sylibr $.
  $}

  ${
    $d A x $.
    $( A case of equivalence of "at most one" and "only one".  (Contributed by
       FL, 6-Dec-2010.) $)
    n0moeu $p |- ( A =/= (/) -> ( E* x x e. A <-> E! x x e. A ) ) $=
      cA c0 wne vx cv cA wcel vx wmo vx cv cA wcel vx wex vx cv cA wcel vx wmo
      wa vx cv cA wcel vx weu cA c0 wne vx cv cA wcel vx wex vx cv cA wcel vx
      wmo cA c0 wne vx cv cA wcel vx wex vx cA n0 biimpi biantrurd vx cv cA
      wcel vx eu5 syl6bbr $.
  $}

  $( Vacuous existential quantification is false.  (Contributed by NM,
     15-Oct-2003.) $)
  rex0 $p |- -. E. x e. (/) ph $=
    wph vx c0 vx cv c0 wcel wph wn vx cv noel pm2.21i nrex $.

  ${
    $d x A $.
    $( The empty set has no elements.  Theorem 2 of [Suppes] p. 22.
       (Contributed by NM, 29-Aug-1993.) $)
    eq0 $p |- ( A = (/) <-> A. x -. x e. A ) $=
      cA c0 wceq vx cv cA wcel wn vx wal cA c0 wceq wn vx cv cA wcel vx wex vx
      cv cA wcel wn vx wal wn vx cA neq0 vx cv cA wcel vx df-ex bitri con4bii
      $.

    $( The universe contains every set.  (Contributed by NM, 11-Sep-2006.) $)
    eqv $p |- ( A = _V <-> A. x x e. A ) $=
      cA cvv wceq vx cv cA wcel vx cv cvv wcel wb vx wal vx cv cA wcel vx wal
      vx cA cvv dfcleq vx cv cA wcel vx cv cA wcel vx cv cvv wcel wb vx vx cv
      cvv wcel vx cv cA wcel vx vex tbt albii bitr4i $.
  $}

  ${
    $d x A $.  $d x y $.
    $( Membership of the empty set in another class.  (Contributed by NM,
       29-Jun-2004.) $)
    0el $p |- ( (/) e. A <-> E. x e. A A. y -. y e. x ) $=
      c0 cA wcel vx cv c0 wceq vx cA wrex vy cv vx cv wcel wn vy wal vx cA wrex
      vx c0 cA risset vx cv c0 wceq vy cv vx cv wcel wn vy wal vx cA vy vx cv
      eq0 rexbii bitri $.
  $}

  ${
    $d x ph $.
    $( The class builder of a wff not containing the abstraction variable is
       either the universal class or the empty set.  (Contributed by Mario
       Carneiro, 29-Aug-2013.) $)
    abvor0 $p |- ( { x | ph } = _V \/ { x | ph } = (/) ) $=
      wph vx cab cvv wceq wph vx cab c0 wceq wph vx cab cvv wceq wn wph wn wph
      vx cab c0 wceq wph wph vx cab cvv wceq wph wph vx cvv wph wph vx cv cvv
      wcel wph id vx cv cvv wcel wph vx vex a1i 2thd abbi1dv con3i wph wn wph
      vx c0 wph wn wph vx cv c0 wcel wph wn id vx cv c0 wcel wn wph wn vx cv
      noel a1i 2falsed abbi1dv syl orri $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Nonempty class abstraction.  (Contributed by NM, 26-Dec-1996.)  (Proof
       shortened by Mario Carneiro, 11-Nov-2016.) $)
    abn0 $p |- ( { x | ph } =/= (/) <-> E. x ph ) $=
      wph vx cab c0 wne vx cv wph vx cab wcel vx wex wph vx wex vx wph vx cab
      wph vx nfab1 n0f vx cv wph vx cab wcel wph vx wph vx abid exbii bitri $.
  $}

  $( Non-empty restricted class abstraction.  (Contributed by NM,
     29-Aug-1999.) $)
  rabn0 $p |- ( { x e. A | ph } =/= (/) <-> E. x e. A ph ) $=
    vx cv cA wcel wph wa vx cab c0 wne vx cv cA wcel wph wa vx wex wph vx cA
    crab c0 wne wph vx cA wrex vx cv cA wcel wph wa vx abn0 wph vx cA crab vx
    cv cA wcel wph wa vx cab c0 wph vx cA df-rab neeq1i wph vx cA df-rex
    3bitr4i $.

  $( Any restricted class abstraction restricted to the empty set is empty.
     (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)
  rab0 $p |- { x e. (/) | ph } = (/) $=
    vx cv c0 wcel wph wa vx cab vx cv vx cv wceq wn vx cab wph vx c0 crab c0 vx
    cv c0 wcel wph wa vx cv vx cv wceq wn vx vx cv vx cv wceq vx cv c0 wcel wph
    wa vx cv vx cv wceq vx cv c0 wcel wph wa wn vx equid vx cv c0 wcel wph vx
    cv noel intnanr 2th con2bii abbii wph vx c0 df-rab vx dfnul2 3eqtr4i $.

  $( Condition for a restricted class abstraction to be empty.  (Contributed by
     Jeff Madsen, 7-Jun-2010.) $)
  rabeq0 $p |- ( { x e. A | ph } = (/) <-> A. x e. A -. ph ) $=
    wph wn vx cA wral wph vx cA wrex wn wph vx cA crab c0 wceq wph vx cA ralnex
    wph vx cA wrex wph vx cA crab c0 wph vx cA rabn0 necon1bbii bitr2i $.

  ${
    $d A x $.
    $( Law of excluded middle, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) $)
    rabxm $p |- A = ( { x e. A | ph } u. { x e. A | -. ph } ) $=
      cA wph wph wn wo vx cA crab wph vx cA crab wph wn vx cA crab cun cA wph
      wph wn wo vx cA crab wceq wph wph wn wo vx cA wph wph wn wo vx cA rabid2
      wph wph wn wo vx cv cA wcel wph exmid a1i mprgbir wph wph wn vx cA unrab
      eqtr4i $.

    $( Law of noncontradiction, in terms of restricted class abstractions.
       (Contributed by Jeff Madsen, 20-Jun-2011.) $)
    rabnc $p |- ( { x e. A | ph } i^i { x e. A | -. ph } ) = (/) $=
      wph vx cA crab wph wn vx cA crab cin wph wph wn wa vx cA crab c0 wph wph
      wn vx cA inrab wph wph wn wa vx cA crab c0 wceq wph wph wn wa wn vx cA
      wph wph wn wa vx cA rabeq0 wph wph wn wa wn vx cv cA wcel wph pm3.24 a1i
      mprgbir eqtri $.
  $}

  ${
    $d x A $.
    $( The union of a class with the empty set is itself.  Theorem 24 of
       [Suppes] p. 27.  (Contributed by NM, 5-Aug-1993.) $)
    un0 $p |- ( A u. (/) ) = A $=
      vx cA c0 cA vx cv cA wcel vx cv cA wcel vx cv c0 wcel wo vx cv c0 wcel vx
      cv cA wcel vx cv noel biorfi bicomi uneqri $.

    $( The intersection of a class with the empty set is the empty set.
       Theorem 16 of [Suppes] p. 26.  (Contributed by NM, 5-Aug-1993.) $)
    in0 $p |- ( A i^i (/) ) = (/) $=
      vx cA c0 c0 vx cv c0 wcel vx cv cA wcel vx cv c0 wcel wa vx cv c0 wcel vx
      cv cA wcel vx cv noel bianfi bicomi ineqri $.
  $}

  $( The intersection of a class with the universal class is itself.  Exercise
     4.10(k) of [Mendelson] p. 231.  (Contributed by NM, 17-May-1998.) $)
  inv1 $p |- ( A i^i _V ) = A $=
    cA cvv cin cA cA cvv inss1 cA cA cvv cA ssid cA ssv ssini eqssi $.

  $( The union of a class with the universal class is the universal class.
     Exercise 4.10(l) of [Mendelson] p. 231.  (Contributed by NM,
     17-May-1998.) $)
  unv $p |- ( A u. _V ) = _V $=
    cA cvv cun cvv cA cvv cun ssv cvv cA ssun2 eqssi $.

  ${
    $d A x $.
    $( The null set is a subset of any class.  Part of Exercise 1 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 5-Aug-1993.) $)
    0ss $p |- (/) C_ A $=
      vx c0 cA vx cv c0 wcel vx cv cA wcel vx cv noel pm2.21i ssriv $.
  $}

  $( Any subset of the empty set is empty.  Theorem 5 of [Suppes] p. 23 and its
     converse.  (Contributed by NM, 17-Sep-2003.) $)
  ss0b $p |- ( A C_ (/) <-> A = (/) ) $=
    cA c0 wceq cA c0 wss cA c0 wceq cA c0 wss c0 cA wss cA 0ss cA c0 eqss
    mpbiran2 bicomi $.

  $( Any subset of the empty set is empty.  Theorem 5 of [Suppes] p. 23.
     (Contributed by NM, 13-Aug-1994.) $)
  ss0 $p |- ( A C_ (/) -> A = (/) ) $=
    cA c0 wss cA c0 wceq cA ss0b biimpi $.

  $( A subclass of an empty class is empty.  (Contributed by NM, 7-Mar-2007.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  sseq0 $p |- ( ( A C_ B /\ B = (/) ) -> A = (/) ) $=
    cB c0 wceq cA cB wss cA c0 wceq cB c0 wceq cA cB wss cA c0 wss cA c0 wceq
    cB c0 cA sseq2 cA ss0 syl6bi impcom $.

  $( A class with a nonempty subclass is nonempty.  (Contributed by NM,
     17-Feb-2007.) $)
  ssn0 $p |- ( ( A C_ B /\ A =/= (/) ) -> B =/= (/) ) $=
    cA cB wss cA c0 wne cB c0 wne cA cB wss cB c0 cA c0 cA cB wss cB c0 wceq cA
    c0 wceq cA cB sseq0 ex necon3d imp $.

  ${
    abf.1 $e |- -. ph $.
    $( A class builder with a false argument is empty.  (Contributed by NM,
       20-Jan-2012.) $)
    abf $p |- { x | ph } = (/) $=
      wph vx cab c0 wss wph vx cab c0 wceq wph vx c0 wph vx cv c0 wcel abf.1
      pm2.21i abssi wph vx cab ss0 ax-mp $.
  $}

  ${
    $d x A $.  $d x ph $.
    eq0rdv.1 $e |- ( ph -> -. x e. A ) $.
    $( Deduction rule for equality to the empty set.  (Contributed by NM,
       11-Jul-2014.) $)
    eq0rdv $p |- ( ph -> A = (/) ) $=
      wph cA c0 wss cA c0 wceq wph vx cA c0 wph vx cv cA wcel vx cv c0 wcel
      eq0rdv.1 pm2.21d ssrdv cA ss0 syl $.
  $}

  $( Two classes are empty iff their union is empty.  (Contributed by NM,
     11-Aug-2004.) $)
  un00 $p |- ( ( A = (/) /\ B = (/) ) <-> ( A u. B ) = (/) ) $=
    cA c0 wceq cB c0 wceq wa cA cB cun c0 wceq cA c0 wceq cB c0 wceq wa cA cB
    cun c0 c0 cun c0 cA c0 cB c0 uneq12 c0 un0 syl6eq cA cB cun c0 wceq cA c0
    wceq cB c0 wceq cA cB cun c0 wceq cA c0 wss cA c0 wceq cA cB cun c0 wceq cA
    cA cB cun wss cA c0 wss cA cB ssun1 cA cB cun c0 cA sseq2 mpbii cA ss0b
    sylib cA cB cun c0 wceq cB c0 wss cB c0 wceq cA cB cun c0 wceq cB cA cB cun
    wss cB c0 wss cB cA ssun2 cA cB cun c0 cB sseq2 mpbii cB ss0b sylib jca
    impbii $.

  $( Only the universal class has the universal class as a subclass.
     (Contributed by NM, 17-Sep-2003.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)
  vss $p |- ( _V C_ A <-> A = _V ) $=
    cvv cA wss cA cvv wss cvv cA wss wa cA cvv wceq cA cvv wss cvv cA wss cA
    ssv biantrur cA cvv eqss bitr4i $.

  $( The null set is a proper subset of any non-empty set.  (Contributed by NM,
     27-Feb-1996.) $)
  0pss $p |- ( (/) C. A <-> A =/= (/) ) $=
    c0 cA wpss c0 cA wne cA c0 wne c0 cA wpss c0 cA wss c0 cA wne cA 0ss c0 cA
    df-pss mpbiran c0 cA necom bitri $.

  $( No set is a proper subset of the empty set.  (Contributed by NM,
     17-Jun-1998.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  npss0 $p |- -. A C. (/) $=
    cA c0 wpss cA c0 wss c0 cA wss wn wa cA c0 wss c0 cA wss wi cA c0 wss c0 cA
    wss wn wa wn c0 cA wss cA c0 wss cA 0ss a1i cA c0 wss c0 cA wss iman mpbi
    cA c0 dfpss3 mtbir $.

  $( Any non-universal class is a proper subclass of the universal class.
     (Contributed by NM, 17-May-1998.) $)
  pssv $p |- ( A C. _V <-> -. A = _V ) $=
    cA cvv wpss cA cvv wss cA cvv wceq wn cA ssv cA cvv dfpss2 mpbiran $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Two ways of saying that two classes are disjoint (have no members in
       common).  (Contributed by NM, 17-Feb-2004.) $)
    disj $p |- ( ( A i^i B ) = (/) <-> A. x e. A -. x e. B ) $=
      cA cB cin c0 wceq vx cv cA wcel vx cv cB wcel wn wi vx wal vx cv cB wcel
      wn vx cA wral cA cB cin c0 wceq vx cv cA wcel vx cv cB wcel wa vx cab c0
      wceq vx cv cA wcel vx cv cB wcel wa vx cv c0 wcel wb vx wal vx cv cA wcel
      vx cv cB wcel wn wi vx wal cA cB cin vx cv cA wcel vx cv cB wcel wa vx
      cab c0 vx cA cB df-in eqeq1i vx cv cA wcel vx cv cB wcel wa vx c0 abeq1
      vx cv cA wcel vx cv cB wcel wa vx cv c0 wcel wb vx cv cA wcel vx cv cB
      wcel wn wi vx vx cv cA wcel vx cv cB wcel wn wi vx cv cA wcel vx cv cB
      wcel wa wn vx cv cA wcel vx cv cB wcel wa vx cv c0 wcel wb vx cv cA wcel
      vx cv cB wcel imnan vx cv c0 wcel vx cv cA wcel vx cv cB wcel wa vx cv
      noel nbn bitr2i albii 3bitri vx cv cB wcel wn vx cA df-ral bitr4i $.

    $( Two ways of saying that two classes are disjoint.  (Contributed by Jeff
       Madsen, 19-Jun-2011.) $)
    disjr $p |- ( ( A i^i B ) = (/) <-> A. x e. B -. x e. A ) $=
      cA cB cin c0 wceq cB cA cin c0 wceq vx cv cA wcel wn vx cB wral cA cB cin
      cB cA cin c0 cA cB incom eqeq1i vx cB cA disj bitri $.

    $( Two ways of saying that two classes are disjoint (have no members in
       common).  (Contributed by NM, 19-Aug-1993.) $)
    disj1 $p |- ( ( A i^i B ) = (/) <-> A. x ( x e. A -> -. x e. B ) ) $=
      cA cB cin c0 wceq vx cv cB wcel wn vx cA wral vx cv cA wcel vx cv cB wcel
      wn wi vx wal vx cA cB disj vx cv cB wcel wn vx cA df-ral bitri $.

    $( Two ways of saying that two classes are disjoint, using the complement
       of ` B ` relative to a universe ` C ` .  (Contributed by NM,
       15-Feb-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    reldisj $p |- ( A C_ C -> ( ( A i^i B ) = (/) <-> A C_ ( C \ B ) ) ) $=
      cA cC wss vx cv cA wcel vx cv cB wcel wn wi vx wal vx cv cA wcel vx cv cC
      cB cdif wcel wi vx wal cA cB cin c0 wceq cA cC cB cdif wss cA cC wss vx
      cv cA wcel vx cv cB wcel wn wi vx cv cA wcel vx cv cC cB cdif wcel wi vx
      cA cC wss vx cv cA wcel vx cv cC wcel wi vx wal vx cv cA wcel vx cv cB
      wcel wn wi vx cv cA wcel vx cv cC cB cdif wcel wi wb vx cA cC dfss2 vx cv
      cA wcel vx cv cC wcel wi vx cv cA wcel vx cv cB wcel wn wi vx cv cA wcel
      vx cv cC cB cdif wcel wi wb vx vx cv cA wcel vx cv cC wcel wi vx cv cA
      wcel vx cv cB wcel wn wi vx cv cA wcel vx cv cC wcel vx cv cB wcel wn wa
      wi vx cv cA wcel vx cv cC cB cdif wcel wi vx cv cA wcel vx cv cC wcel vx
      cv cB wcel wn pm5.44 vx cv cC cB cdif wcel vx cv cC wcel vx cv cB wcel wn
      wa vx cv cA wcel vx cv cC cB eldif imbi2i syl6bbr sps sylbi albidv vx cA
      cB disj1 vx cA cC cB cdif dfss2 3bitr4g $.

    $( Two ways of saying that two classes are disjoint.  (Contributed by NM,
       19-May-1998.) $)
    disj3 $p |- ( ( A i^i B ) = (/) <-> A = ( A \ B ) ) $=
      vx cv cA wcel vx cv cB wcel wn wi vx wal vx cv cA wcel vx cv cA cB cdif
      wcel wb vx wal cA cB cin c0 wceq cA cA cB cdif wceq vx cv cA wcel vx cv
      cB wcel wn wi vx cv cA wcel vx cv cA cB cdif wcel wb vx vx cv cA wcel vx
      cv cB wcel wn wi vx cv cA wcel vx cv cA wcel vx cv cB wcel wn wa wb vx cv
      cA wcel vx cv cA cB cdif wcel wb vx cv cA wcel vx cv cB wcel wn pm4.71 vx
      cv cA cB cdif wcel vx cv cA wcel vx cv cB wcel wn wa vx cv cA wcel vx cv
      cA cB eldif bibi2i bitr4i albii vx cA cB disj1 vx cA cA cB cdif dfcleq
      3bitr4i $.

    $( Members of disjoint sets are not equal.  (Contributed by NM,
       28-Mar-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    disjne $p |- ( ( ( A i^i B ) = (/) /\ C e. A /\ D e. B ) -> C =/= D ) $=
      cA cB cin c0 wceq cC cA wcel cD cB wcel cC cD wne cA cB cin c0 wceq vx cv
      cB wcel wn vx cA wral cC cA wcel cD cB wcel cC cD wne wi vx cA cB disj vx
      cv cB wcel wn vx cA wral cC cA wcel wa cC cB wcel wn cD cB wcel cC cD wne
      vx cv cB wcel wn cC cB wcel wn vx cC cA vx cv cC wceq vx cv cB wcel cC cB
      wcel vx cv cC cB eleq1 notbid rspccva cD cB wcel cC cB wcel cC cD cD cB
      cC eleq1a necon3bd syl5com sylanb 3impia $.
  $}

  $( A set can't belong to both members of disjoint classes.  (Contributed by
     NM, 28-Feb-2015.) $)
  disjel $p |- ( ( ( A i^i B ) = (/) /\ C e. A ) -> -. C e. B ) $=
    cA cB cin c0 wceq cC cA wcel cC cB wcel wn cA cB cin c0 wceq cA cA cB cdif
    wceq cC cA wcel cC cB wcel wn wi cA cB disj3 cA cA cB cdif wceq cC cA wcel
    cC cA cB cdif wcel cC cB wcel wn cA cA cB cdif cC eleq2 cC cA cB eldifn
    syl6bi sylbi imp $.

  $( Two ways of saying that two classes are disjoint.  (Contributed by NM,
     17-May-1998.) $)
  disj2 $p |- ( ( A i^i B ) = (/) <-> A C_ ( _V \ B ) ) $=
    cA cvv wss cA cB cin c0 wceq cA cvv cB cdif wss wb cA ssv cA cB cvv reldisj
    ax-mp $.

  $( Two ways of saying that two classes are disjoint.  (Contributed by NM,
     21-Mar-2004.) $)
  disj4 $p |- ( ( A i^i B ) = (/) <-> -. ( A \ B ) C. A ) $=
    cA cB cin c0 wceq cA cA cB cdif wceq cA cB cdif cA wceq cA cB cdif cA wpss
    wn cA cB disj3 cA cA cB cdif eqcom cA cB cdif cA wpss cA cB cdif cA wceq cA
    cB cdif cA wpss cA cB cdif cA wss cA cB cdif cA wceq wn cA cB difss cA cB
    cdif cA dfpss2 mpbiran con2bii 3bitri $.

  $( Intersection with a subclass of a disjoint class.  (Contributed by FL,
     24-Jan-2007.) $)
  ssdisj $p |- ( ( A C_ B /\ ( B i^i C ) = (/) ) -> ( A i^i C ) = (/) ) $=
    cA cB wss cB cC cin c0 wceq wa cA cC cin c0 wss cA cC cin c0 wceq cA cB wss
    cB cC cin c0 wceq cA cC cin c0 wss cB cC cin c0 wceq cB cC cin c0 wss cA cB
    wss cA cC cin c0 wss cB cC cin ss0b cA cB wss cA cC cin cB cC cin wss cB cC
    cin c0 wss cA cC cin c0 wss wi cA cB cC ssrin cA cC cin cB cC cin c0 sstr2
    syl syl5bir imp cA cC cin ss0 syl $.

  $( A class is a proper subset of its union with a disjoint nonempty class.
     (Contributed by NM, 15-Sep-2004.) $)
  disjpss $p |- ( ( ( A i^i B ) = (/) /\ B =/= (/) ) -> A C. ( A u. B ) ) $=
    cA cB cin c0 wceq cB c0 wne wa cB cA wss wn cA cA cB cun wpss cA cB cin c0
    wceq cB c0 wne cB cA wss wn cA cB cin c0 wceq cB cA wss cB c0 cA cB cin c0
    wceq cB cA wss cB c0 wss cB c0 wceq cB cA wss cB cA cB cin wss cA cB cin c0
    wceq cB c0 wss cB cA wss cB cA wss cB cB wss wa cB cA cB cin wss cB cB wss
    cB cA wss cB ssid biantru cB cA cB ssin bitri cA cB cin c0 cB sseq2 syl5bb
    cB ss0 syl6bi necon3ad imp cB cA wss wn cA cB cA cun wpss cA cA cB cun wpss
    cB cA nsspssun cB cA cun cA cB cun cA cB cA uncom psseq2i bitri sylib $.

  $( The union of disjoint classes is disjoint.  (Contributed by NM,
     26-Sep-2004.) $)
  undisj1 $p |- ( ( ( A i^i C ) = (/) /\ ( B i^i C ) = (/) ) <->
               ( ( A u. B ) i^i C ) = (/) ) $=
    cA cC cin c0 wceq cB cC cin c0 wceq wa cA cC cin cB cC cin cun c0 wceq cA
    cB cun cC cin c0 wceq cA cC cin cB cC cin un00 cA cB cun cC cin cA cC cin
    cB cC cin cun c0 cA cB cC indir eqeq1i bitr4i $.

  $( The union of disjoint classes is disjoint.  (Contributed by NM,
     13-Sep-2004.) $)
  undisj2 $p |- ( ( ( A i^i B ) = (/) /\ ( A i^i C ) = (/) ) <->
               ( A i^i ( B u. C ) ) = (/) ) $=
    cA cB cin c0 wceq cA cC cin c0 wceq wa cA cB cin cA cC cin cun c0 wceq cA
    cB cC cun cin c0 wceq cA cB cin cA cC cin un00 cA cB cC cun cin cA cB cin
    cA cC cin cun c0 cA cB cC indi eqeq1i bitr4i $.

  $( Subclass expressed in terms of intersection with difference from the
     universal class.  (Contributed by NM, 17-Sep-2003.) $)
  ssindif0 $p |- ( A C_ B <-> ( A i^i ( _V \ B ) ) = (/) ) $=
    cA cvv cB cdif cin c0 wceq cA cvv cvv cB cdif cdif wss cA cB wss cA cvv cB
    cdif disj2 cvv cvv cB cdif cdif cB cA cB ddif sseq2i bitr2i $.

  $( The intersection of classes with a common member is nonempty.
     (Contributed by NM, 7-Apr-1994.) $)
  inelcm $p |- ( ( A e. B /\ A e. C ) -> ( B i^i C ) =/= (/) ) $=
    cA cB wcel cA cC wcel wa cA cB cC cin wcel cB cC cin c0 wne cA cB cC elin
    cB cC cin cA ne0i sylbir $.

  $( A minimum element of a class has no elements in common with the class.
     (Contributed by NM, 22-Jun-1994.) $)
  minel $p |- ( ( A e. B /\ ( C i^i B ) = (/) ) -> -. A e. C ) $=
    cC cB cin c0 wceq cA cB wcel cA cC wcel wn cC cB cin c0 wceq cA cC wcel cA
    cB wcel cC cB cin c0 wceq cA cC wcel cA cB wcel wa wn cA cC wcel cA cB wcel
    wn wi cA cC wcel cA cB wcel wa cC cB cin c0 cA cC cB inelcm necon2bi cA cC
    wcel cA cB wcel imnan sylibr con2d impcom $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Distribute union over difference.  (Contributed by NM, 17-May-1998.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    undif4 $p |- ( ( A i^i C ) = (/) ->
                 ( A u. ( B \ C ) ) = ( ( A u. B ) \ C ) ) $=
      vx cv cA wcel vx cv cC wcel wn wi vx wal vx cv cA cB cC cdif cun wcel vx
      cv cA cB cun cC cdif wcel wb vx wal cA cC cin c0 wceq cA cB cC cdif cun
      cA cB cun cC cdif wceq vx cv cA wcel vx cv cC wcel wn wi vx cv cA cB cC
      cdif cun wcel vx cv cA cB cun cC cdif wcel wb vx vx cv cA wcel vx cv cC
      wcel wn wi vx cv cA wcel vx cv cB cC cdif wcel wo vx cv cA cB cun wcel vx
      cv cC wcel wn wa vx cv cA cB cC cdif cun wcel vx cv cA cB cun cC cdif
      wcel vx cv cA wcel vx cv cC wcel wn wi vx cv cA wcel vx cv cB wcel wo vx
      cv cA wcel vx cv cC wcel wn wo wa vx cv cA wcel vx cv cB wcel wo vx cv cC
      wcel wn wa vx cv cA wcel vx cv cB cC cdif wcel wo vx cv cA cB cun wcel vx
      cv cC wcel wn wa vx cv cA wcel vx cv cC wcel wn wi vx cv cA wcel vx cv cC
      wcel wn wo vx cv cC wcel wn vx cv cA wcel vx cv cB wcel wo vx cv cA wcel
      vx cv cC wcel wn wi vx cv cA wcel vx cv cC wcel wn wo vx cv cC wcel wn vx
      cv cA wcel vx cv cC wcel wn pm2.621 vx cv cC wcel wn vx cv cA wcel olc
      impbid1 anbi2d vx cv cA wcel vx cv cB cC cdif wcel wo vx cv cA wcel vx cv
      cB wcel vx cv cC wcel wn wa wo vx cv cA wcel vx cv cB wcel wo vx cv cA
      wcel vx cv cC wcel wn wo wa vx cv cB cC cdif wcel vx cv cB wcel vx cv cC
      wcel wn wa vx cv cA wcel vx cv cB cC eldif orbi2i vx cv cA wcel vx cv cB
      wcel vx cv cC wcel wn ordi bitri vx cv cA cB cun wcel vx cv cA wcel vx cv
      cB wcel wo vx cv cC wcel wn vx cv cA cB elun anbi1i 3bitr4g vx cv cA cB
      cC cdif elun vx cv cA cB cun cC eldif 3bitr4g alimi vx cA cC disj1 vx cA
      cB cC cdif cun cA cB cun cC cdif dfcleq 3imtr4i $.

    $( Subset relation for disjoint classes.  (Contributed by NM,
       25-Oct-2005.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    disjssun $p |- ( ( A i^i B ) = (/) -> ( A C_ ( B u. C ) <-> A C_ C ) ) $=
      cA cB cin c0 wceq cA cB cC cun cin cA wceq cA cC cin cA wceq cA cB cC cun
      wss cA cC wss cA cB cin c0 wceq cA cB cC cun cin cA cC cin cA cA cB cin
      c0 wceq cA cB cC cun cin cA cC cin cA cB cin cun cA cC cin cA cB cC cun
      cin cA cB cin cA cC cin cA cB cC indi equncomi cA cB cin c0 wceq cA cC
      cin cA cB cin cun cA cC cin c0 cun cA cC cin cA cB cin c0 cA cC cin uneq2
      cA cC cin un0 syl6eq syl5eq eqeq1d cA cB cC cun df-ss cA cC df-ss 3bitr4g
      $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Subclass expressed in terms of difference.  Exercise 7 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 29-Apr-1994.) $)
    ssdif0 $p |- ( A C_ B <-> ( A \ B ) = (/) ) $=
      vx cv cA wcel vx cv cB wcel wi vx wal vx cv cA cB cdif wcel wn vx wal cA
      cB wss cA cB cdif c0 wceq vx cv cA wcel vx cv cB wcel wi vx cv cA cB cdif
      wcel wn vx vx cv cA wcel vx cv cB wcel wi vx cv cA wcel vx cv cB wcel wn
      wa vx cv cA cB cdif wcel vx cv cA wcel vx cv cB wcel iman vx cv cA cB
      eldif xchbinxr albii vx cA cB dfss2 vx cA cB cdif eq0 3bitr4i $.
  $}

  $( Universal class equality in terms of empty difference.  (Contributed by
     NM, 17-Sep-2003.) $)
  vdif0 $p |- ( A = _V <-> ( _V \ A ) = (/) ) $=
    cA cvv wceq cvv cA wss cvv cA cdif c0 wceq cA vss cvv cA ssdif0 bitr3i $.

  $( A proper subclass has a nonempty difference.  (Contributed by NM,
     3-May-1994.) $)
  pssdifn0 $p |- ( ( A C_ B /\ A =/= B ) -> ( B \ A ) =/= (/) ) $=
    cA cB wss cA cB wne cB cA cdif c0 wne cA cB wss cB cA cdif c0 cA cB cB cA
    cdif c0 wceq cB cA wss cA cB wss cA cB wceq cB cA ssdif0 cA cB wceq cA cB
    wss cB cA wss cA cB eqss simplbi2 syl5bir necon3d imp $.

  $( A proper subclass has a nonempty difference.  (Contributed by Mario
     Carneiro, 27-Apr-2016.) $)
  pssdif $p |- ( A C. B -> ( B \ A ) =/= (/) ) $=
    cA cB wpss cA cB wss cA cB wne wa cB cA cdif c0 wne cA cB df-pss cA cB
    pssdifn0 sylbi $.

  $( A subclass missing a member is a proper subclass.  (Contributed by NM,
     12-Jan-2002.) $)
  ssnelpss $p |- ( A C_ B -> ( ( C e. B /\ -. C e. A ) -> A C. B ) ) $=
    cC cB wcel cC cA wcel wn wa cA cB wceq wn cA cB wss cA cB wpss cC cB wcel
    cC cA wcel wn wa cB cA wceq cA cB wceq cC cB cA nelneq2 cB cA eqcom sylnib
    cA cB wpss cA cB wss cA cB wceq wn cA cB dfpss2 baibr syl5ib $.

  ${
    ssnelpssd.1 $e |- ( ph -> A C_ B ) $.
    ssnelpssd.2 $e |- ( ph -> C e. B ) $.
    ssnelpssd.3 $e |- ( ph -> -. C e. A ) $.
    $( Subclass inclusion with one element of the superclass missing is proper
       subclass inclusion.  Deduction form of ~ ssnelpss .  (Contributed by
       David Moews, 1-May-2017.) $)
    ssnelpssd $p |- ( ph -> A C. B ) $=
      wph cC cB wcel cC cA wcel wn cA cB wpss ssnelpssd.2 ssnelpssd.3 wph cA cB
      wss cC cB wcel cC cA wcel wn wa cA cB wpss wi ssnelpssd.1 cA cB cC
      ssnelpss syl mp2and $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A proper subclass has a member in one argument that's not in both.
       (Contributed by NM, 29-Feb-1996.) $)
    pssnel $p |- ( A C. B -> E. x ( x e. B /\ -. x e. A ) ) $=
      cA cB wpss vx cv cB cA cdif wcel vx wex vx cv cB wcel vx cv cA wcel wn wa
      vx wex cA cB wpss cB cA cdif c0 wne vx cv cB cA cdif wcel vx wex cA cB
      pssdif vx cB cA cdif n0 sylib vx cv cB cA cdif wcel vx cv cB wcel vx cv
      cA wcel wn wa vx vx cv cB cA eldif exbii sylib $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Difference, intersection, and subclass relationship.  (Contributed by
       NM, 30-Apr-1994.)  (Proof shortened by Wolf Lammen, 30-Sep-2014.) $)
    difin0ss $p |- ( ( ( A \ B ) i^i C ) = (/) -> ( C C_ A -> C C_ B ) ) $=
      cA cB cdif cC cin c0 wceq vx cv cA cB cdif cC cin wcel wn vx wal cC cA
      wss cC cB wss wi vx cA cB cdif cC cin eq0 vx cv cA cB cdif cC cin wcel wn
      vx wal vx cv cC wcel vx cv cA wcel wi vx wal vx cv cC wcel vx cv cB wcel
      wi vx wal cC cA wss cC cB wss vx cv cA cB cdif cC cin wcel wn vx cv cC
      wcel vx cv cA wcel wi vx cv cC wcel vx cv cB wcel wi vx vx cv cA cB cdif
      cC cin wcel wn vx cv cC wcel vx cv cA wcel vx cv cB wcel wi wi vx cv cC
      wcel vx cv cA wcel wi vx cv cC wcel vx cv cB wcel wi wi vx cv cC wcel vx
      cv cA wcel vx cv cB wcel wi wi vx cv cC wcel vx cv cA wcel vx cv cB wcel
      wi wn wa vx cv cA cB cdif cC cin wcel vx cv cC wcel vx cv cA wcel vx cv
      cB wcel wi iman vx cv cA cB cdif cC cin wcel vx cv cA wcel vx cv cB wcel
      wn wa vx cv cC wcel wa vx cv cC wcel vx cv cA wcel vx cv cB wcel wn wa wa
      vx cv cC wcel vx cv cA wcel vx cv cB wcel wi wn wa vx cv cA cB cdif cC
      cin wcel vx cv cA cB cdif wcel vx cv cC wcel wa vx cv cA wcel vx cv cB
      wcel wn wa vx cv cC wcel wa vx cv cA cB cdif cC elin vx cv cA cB cdif
      wcel vx cv cA wcel vx cv cB wcel wn wa vx cv cC wcel vx cv cA cB eldif
      anbi1i bitri vx cv cC wcel vx cv cA wcel vx cv cB wcel wn wa ancom vx cv
      cA wcel vx cv cB wcel wn wa vx cv cA wcel vx cv cB wcel wi wn vx cv cC
      wcel vx cv cA wcel vx cv cB wcel annim anbi2i 3bitr2i xchbinxr vx cv cC
      wcel vx cv cA wcel vx cv cB wcel ax-2 sylbir al2imi vx cC cA dfss2 vx cC
      cB dfss2 3imtr4g sylbi $.

    $( Intersection, subclass, and difference relationship.  (Contributed by
       NM, 27-Oct-1996.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.)
       (Proof shortened by Wolf Lammen, 30-Sep-2014.) $)
    inssdif0 $p |- ( ( A i^i B ) C_ C <-> ( A i^i ( B \ C ) ) = (/) ) $=
      vx cv cA cB cin wcel vx cv cC wcel wi vx wal vx cv cA cB cC cdif cin wcel
      wn vx wal cA cB cin cC wss cA cB cC cdif cin c0 wceq vx cv cA cB cin wcel
      vx cv cC wcel wi vx cv cA cB cC cdif cin wcel wn vx vx cv cA cB cin wcel
      vx cv cC wcel wi vx cv cA wcel vx cv cB wcel wa vx cv cC wcel wn wa vx cv
      cA cB cC cdif cin wcel vx cv cA cB cin wcel vx cv cC wcel wi vx cv cA
      wcel vx cv cB wcel wa vx cv cC wcel wi vx cv cA wcel vx cv cB wcel wa vx
      cv cC wcel wn wa wn vx cv cA cB cin wcel vx cv cA wcel vx cv cB wcel wa
      vx cv cC wcel vx cv cA cB elin imbi1i vx cv cA wcel vx cv cB wcel wa vx
      cv cC wcel iman bitri vx cv cA wcel vx cv cB cC cdif wcel wa vx cv cA
      wcel vx cv cB wcel vx cv cC wcel wn wa wa vx cv cA cB cC cdif cin wcel vx
      cv cA wcel vx cv cB wcel wa vx cv cC wcel wn wa vx cv cB cC cdif wcel vx
      cv cB wcel vx cv cC wcel wn wa vx cv cA wcel vx cv cB cC eldif anbi2i vx
      cv cA cB cC cdif elin vx cv cA wcel vx cv cB wcel vx cv cC wcel wn anass
      3bitr4ri xchbinx albii vx cA cB cin cC dfss2 vx cA cB cC cdif cin eq0
      3bitr4i $.
  $}

  $( The difference between a class and itself is the empty set.  Proposition
     5.15 of [TakeutiZaring] p. 20.  Also Theorem 32 of [Suppes] p. 28.
     (Contributed by NM, 22-Apr-2004.) $)
  difid $p |- ( A \ A ) = (/) $=
    cA cA wss cA cA cdif c0 wceq cA ssid cA cA ssdif0 mpbi $.

  ${
    $d x A $.
    $( The difference between a class and itself is the empty set.  Proposition
       5.15 of [TakeutiZaring] p. 20.  Also Theorem 32 of [Suppes] p. 28.
       Alternate proof of ~ difid .  (Contributed by David Abernethy,
       17-Jun-2012.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    difidALT $p |- ( A \ A ) = (/) $=
      cA cA cdif vx cv cA wcel wn vx cA crab c0 vx cA cA dfdif2 vx cA dfnul3
      eqtr4i $.
  $}

  $( The difference between a class and the empty set.  Part of Exercise 4.4 of
     [Stoll] p. 16.  (Contributed by NM, 17-Aug-2004.) $)
  dif0 $p |- ( A \ (/) ) = A $=
    cA cA cA cdif cdif cA c0 cdif cA cA cA cdif c0 cA cA difid difeq2i cA cA
    difdif eqtr3i $.

  $( The difference between the empty set and a class.  Part of Exercise 4.4 of
     [Stoll] p. 16.  (Contributed by NM, 17-Aug-2004.) $)
  0dif $p |- ( (/) \ A ) = (/) $=
    c0 cA cdif c0 wss c0 cA cdif c0 wceq c0 cA difss c0 cA cdif ss0 ax-mp $.

  $( A class and its relative complement are disjoint.  Theorem 38 of [Suppes]
     p. 29.  (Contributed by NM, 24-Mar-1998.) $)
  disjdif $p |- ( A i^i ( B \ A ) ) = (/) $=
    cA cB cin cA wss cA cB cA cdif cin c0 wceq cA cB inss1 cA cB cA inssdif0
    mpbi $.

  $( The difference of a class from its intersection is empty.  Theorem 37 of
     [Suppes] p. 29.  (Contributed by NM, 17-Aug-2004.)  (Proof shortened by
     Andrew Salmon, 26-Jun-2011.) $)
  difin0 $p |- ( ( A i^i B ) \ B ) = (/) $=
    cA cB cin cB wss cA cB cin cB cdif c0 wceq cA cB inss2 cA cB cin cB ssdif0
    mpbi $.

  $( The union of a class and its complement is the universe.  Theorem 5.1(5)
     of [Stoll] p. 17.  (Contributed by NM, 17-Aug-2004.) $)
  undifv $p |- ( A u. ( _V \ A ) ) = _V $=
    cA cvv cA cdif cun cvv cvv cA cdif cvv cvv cA cdif cdif cin cdif cvv c0
    cdif cvv cA cvv cA cdif dfun3 cvv cA cdif cvv cvv cA cdif cdif cin c0 cvv
    cvv cA cdif cvv disjdif difeq2i cvv dif0 3eqtri $.

  $( Absorption of difference by union.  This decomposes a union into two
     disjoint classes (see ~ disjdif ).  Theorem 35 of [Suppes] p. 29.
     (Contributed by NM, 19-May-1998.) $)
  undif1 $p |- ( ( A \ B ) u. B ) = ( A u. B ) $=
    cA cvv cB cdif cin cB cun cA cB cun cvv cB cdif cB cun cin cA cB cdif cB
    cun cA cB cun cA cvv cB cdif cB undir cA cvv cB cdif cin cA cB cdif cB cA
    cB invdif uneq1i cA cB cun cvv cB cdif cB cun cin cA cB cun cvv cin cA cB
    cun cvv cB cdif cB cun cvv cA cB cun cvv cB cdif cB cun cB cvv cB cdif cun
    cvv cvv cB cdif cB uncom cB undifv eqtri ineq2i cA cB cun inv1 eqtri
    3eqtr3i $.

  $( Absorption of difference by union.  This decomposes a union into two
     disjoint classes (see ~ disjdif ).  Part of proof of Corollary 6K of
     [Enderton] p. 144.  (Contributed by NM, 19-May-1998.) $)
  undif2 $p |- ( A u. ( B \ A ) ) = ( A u. B ) $=
    cA cB cA cdif cun cB cA cdif cA cun cB cA cun cA cB cun cA cB cA cdif uncom
    cB cA undif1 cB cA uncom 3eqtri $.

  $( Absorption of difference by union.  (Contributed by NM, 18-Aug-2013.) $)
  undifabs $p |- ( A u. ( A \ B ) ) = A $=
    cA cA cB cdif cun cA cA cun cB cA cdif cdif cA cB cA cdif cdif cA cA cA cB
    undif3 cA cA cun cA cB cA cdif cA unidm difeq1i cA cB difdif 3eqtri $.

  ${
    $d x A $.  $d x B $.
    $( The intersection and class difference of a class with another class
       unite to give the original class.  (Contributed by Paul Chapman,
       5-Jun-2009.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    inundif $p |- ( ( A i^i B ) u. ( A \ B ) ) = A $=
      vx cA cB cin cA cB cdif cA vx cv cA cB cin wcel vx cv cA cB cdif wcel wo
      vx cv cA wcel vx cv cB wcel wa vx cv cA wcel vx cv cB wcel wn wa wo vx cv
      cA wcel vx cv cA cB cin wcel vx cv cA wcel vx cv cB wcel wa vx cv cA cB
      cdif wcel vx cv cA wcel vx cv cB wcel wn wa vx cv cA cB elin vx cv cA cB
      eldif orbi12i vx cv cA wcel vx cv cB wcel pm4.42 bitr4i uneqri $.
  $}

  $( Absorption of union by difference.  Theorem 36 of [Suppes] p. 29.
     (Contributed by NM, 19-May-1998.) $)
  difun2 $p |- ( ( A u. B ) \ B ) = ( A \ B ) $=
    cA cB cun cB cdif cA cB cdif cB cB cdif cun cA cB cdif c0 cun cA cB cdif cA
    cB cB difundir cB cB cdif c0 cA cB cdif cB difid uneq2i cA cB cdif un0
    3eqtri $.

  $( Union of complementary parts into whole.  (Contributed by NM,
     22-Mar-1998.) $)
  undif $p |- ( A C_ B <-> ( A u. ( B \ A ) ) = B ) $=
    cA cB wss cA cB cun cB wceq cA cB cA cdif cun cB wceq cA cB ssequn1 cA cB
    cA cdif cun cA cB cun cB cA cB undif2 eqeq1i bitr4i $.

  $( A subset of a difference does not intersect the subtrahend.  (Contributed
     by Jeff Hankins, 1-Sep-2013.)  (Proof shortened by Mario Carneiro,
     24-Aug-2015.) $)
  ssdifin0 $p |- ( A C_ ( B \ C ) -> ( A i^i C ) = (/) ) $=
    cA cB cC cdif wss cA cC cin cB cC cdif cC cin wss cB cC cdif cC cin c0 wceq
    cA cC cin c0 wceq cA cB cC cdif cC ssrin cB cC cdif cC cin cC cB cC cdif
    cin c0 cB cC cdif cC incom cC cB disjdif eqtri cA cC cin cB cC cdif cC cin
    sseq0 sylancl $.

  $( A class is a subclass of itself subtracted from another iff it is the
     empty set.  (Contributed by Steve Rodriguez, 20-Nov-2015.) $)
  ssdifeq0 $p |- ( A C_ ( B \ A ) <-> A = (/) ) $=
    cA cB cA cdif wss cA c0 wceq cA cB cA cdif wss cA cA cA cin c0 cA inidm cA
    cB cA ssdifin0 syl5eqr cA c0 wceq cA cB cA cdif wss c0 cB c0 cdif wss cB c0
    cdif 0ss cA c0 wceq cA c0 cB cA cdif cB c0 cdif cA c0 wceq id cA c0 cB
    difeq2 sseq12d mpbiri impbii $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( A condition equivalent to inclusion in the union of two classes.
       (Contributed by NM, 26-Mar-2007.) $)
    ssundif $p |- ( A C_ ( B u. C ) <-> ( A \ B ) C_ C ) $=
      vx cv cA wcel vx cv cB cC cun wcel wi vx wal vx cv cA cB cdif wcel vx cv
      cC wcel wi vx wal cA cB cC cun wss cA cB cdif cC wss vx cv cA wcel vx cv
      cB cC cun wcel wi vx cv cA cB cdif wcel vx cv cC wcel wi vx vx cv cA wcel
      vx cv cB wcel wn wa vx cv cC wcel wi vx cv cA wcel vx cv cB wcel vx cv cC
      wcel wo wi vx cv cA cB cdif wcel vx cv cC wcel wi vx cv cA wcel vx cv cB
      cC cun wcel wi vx cv cA wcel vx cv cB wcel vx cv cC wcel pm5.6 vx cv cA
      cB cdif wcel vx cv cA wcel vx cv cB wcel wn wa vx cv cC wcel vx cv cA cB
      eldif imbi1i vx cv cB cC cun wcel vx cv cB wcel vx cv cC wcel wo vx cv cA
      wcel vx cv cB cC elun imbi2i 3bitr4ri albii vx cA cB cC cun dfss2 vx cA
      cB cdif cC dfss2 3bitr4i $.
  $}

  $( Swap the arguments of a class difference.  (Contributed by NM,
     29-Mar-2007.) $)
  difcom $p |- ( ( A \ B ) C_ C <-> ( A \ C ) C_ B ) $=
    cA cB cC cun wss cA cC cB cun wss cA cB cdif cC wss cA cC cdif cB wss cB cC
    cun cC cB cun cA cB cC uncom sseq2i cA cB cC ssundif cA cC cB ssundif
    3bitr3i $.

  $( Two ways to express overlapping subsets.  (Contributed by Stefan O'Rear,
     31-Oct-2014.) $)
  pssdifcom1 $p |- ( ( A C_ C /\ B C_ C ) ->
    ( ( C \ A ) C. B <-> ( C \ B ) C. A ) ) $=
    cA cC wss cB cC wss wa cC cA cdif cB wss cB cC cA cdif wss wn wa cC cB cdif
    cA wss cA cC cB cdif wss wn wa cC cA cdif cB wpss cC cB cdif cA wpss cA cC
    wss cB cC wss wa cC cA cdif cB wss cC cB cdif cA wss cB cC cA cdif wss wn
    cA cC cB cdif wss wn cC cA cdif cB wss cC cB cdif cA wss wb cA cC wss cB cC
    wss wa cC cA cB difcom a1i cA cC wss cB cC wss wa cB cC cA cdif wss cA cC
    cB cdif wss cB cC wss cA cC wss cB cC cA cdif wss cA cC cB cdif wss wb cB
    cA cC ssconb ancoms notbid anbi12d cC cA cdif cB dfpss3 cC cB cdif cA
    dfpss3 3bitr4g $.

  $( Two ways to express non-covering pairs of subsets.  (Contributed by Stefan
     O'Rear, 31-Oct-2014.) $)
  pssdifcom2 $p |- ( ( A C_ C /\ B C_ C ) ->
    ( B C. ( C \ A ) <-> A C. ( C \ B ) ) ) $=
    cA cC wss cB cC wss wa cB cC cA cdif wss cC cA cdif cB wss wn wa cA cC cB
    cdif wss cC cB cdif cA wss wn wa cB cC cA cdif wpss cA cC cB cdif wpss cA
    cC wss cB cC wss wa cB cC cA cdif wss cA cC cB cdif wss cC cA cdif cB wss
    wn cC cB cdif cA wss wn cB cC wss cA cC wss cB cC cA cdif wss cA cC cB cdif
    wss wb cB cA cC ssconb ancoms cA cC wss cB cC wss wa cC cA cdif cB wss cC
    cB cdif cA wss cC cA cdif cB wss cC cB cdif cA wss wb cA cC wss cB cC wss
    wa cC cA cB difcom a1i notbid anbi12d cB cC cA cdif dfpss3 cA cC cB cdif
    dfpss3 3bitr4g $.

  $( Distributive law for class difference.  Exercise 4.8 of [Stoll] p. 16.
     (Contributed by NM, 18-Aug-2004.) $)
  difdifdir $p |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ ( B \ C ) ) $=
    cA cB cdif cC cdif cA cC cdif cvv cB cdif cC cun cin cA cC cdif cvv cB cC
    cdif cdif cin cA cC cdif cB cC cdif cdif cA cB cdif cC cdif cA cC cdif cvv
    cB cdif cin c0 cun cA cC cdif cvv cB cdif cC cun cin cA cB cdif cC cdif cA
    cC cdif cvv cB cdif cin cA cC cdif cvv cB cdif cin c0 cun cA cB cdif cC
    cdif cA cC cdif cB cdif cA cC cdif cvv cB cdif cin cA cB cC dif32 cA cC
    cdif cB invdif eqtr4i cA cC cdif cvv cB cdif cin un0 eqtr4i cA cC cdif cvv
    cB cdif cC cun cin cA cC cdif cvv cB cdif cin cA cC cdif cC cin cun cA cC
    cdif cvv cB cdif cin c0 cun cA cC cdif cvv cB cdif cC indi c0 cA cC cdif cC
    cin cA cC cdif cvv cB cdif cin cC cA cC cdif cin c0 cA cC cdif cC cin cC cA
    disjdif cC cA cC cdif incom eqtr3i uneq2i eqtr4i eqtr4i cvv cB cdif cC cun
    cvv cB cC cdif cdif cA cC cdif cvv cB cdif cvv cvv cC cdif cdif cun cvv cB
    cdif cC cun cvv cB cC cdif cdif cvv cvv cC cdif cdif cC cvv cB cdif cC ddif
    uneq2i cvv cB cvv cC cdif cin cdif cvv cB cdif cvv cvv cC cdif cdif cun cvv
    cB cC cdif cdif cB cvv cC cdif indm cB cvv cC cdif cin cB cC cdif cvv cB cC
    invdif difeq2i eqtr3i eqtr3i ineq2i cA cC cdif cB cC cdif invdif 3eqtri $.

  $( Two ways to say that ` A ` and ` B ` partition ` C ` (when ` A ` and ` B `
     don't overlap and ` A ` is a part of ` C ` ).  (Contributed by FL,
     17-Nov-2008.) $)
  uneqdifeq $p |- ( ( A C_ C /\ ( A i^i B ) = (/) )
     -> ( ( A u. B ) = C <-> ( C \ A ) = B ) ) $=
    cA cC wss cA cB cin c0 wceq wa cA cB cun cC wceq cC cA cdif cB wceq cA cB
    cin c0 wceq cA cB cun cC wceq cC cA cdif cB wceq wi cA cC wss cA cB cun cC
    wceq cA cB cin c0 wceq cC cA cdif cB wceq cB cA cun cA cB cun wceq cA cB
    cun cC wceq cA cB cin c0 wceq cC cA cdif cB wceq wi cB cA uncom cB cA cun
    cA cB cun wceq cA cB cun cC wceq wa cC cB cA cun wceq cA cB cin c0 wceq cC
    cA cdif cB wceq wi cB cA cun cA cB cun wceq cA cB cun cC wceq wa cB cA cun
    cC cB cA cun cA cB cun cC eqtr eqcomd cC cB cA cun wceq cC cA cdif cB cA
    cun cA cdif wceq cB cA cun cA cdif cB cA cdif wceq cA cB cin c0 wceq cC cA
    cdif cB wceq wi cC cB cA cun cA difeq1 cB cA difun2 cC cA cdif cB cA cun cA
    cdif wceq cB cA cun cA cdif cB cA cdif wceq wa cC cA cdif cB cA cdif wceq
    cA cB cin c0 wceq cC cA cdif cB wceq cC cA cdif cB cA cun cA cdif cB cA
    cdif eqtr cA cB cin c0 wceq cB cB cA cdif wceq cC cA cdif cB cA cdif wceq
    cC cA cdif cB wceq wi cA cB cin c0 wceq cB cA cin c0 wceq cB cB cA cdif
    wceq cA cB cin cB cA cin c0 cA cB incom eqeq1i cB cA disj3 bitri cC cA cdif
    cB cA cdif wceq cC cA cdif cB wceq wi cB cA cdif cB cC cA cdif cB cA cdif
    wceq cB cA cdif cB wceq cC cA cdif cB wceq cC cA cdif cB cA cdif cB eqtr
    expcom eqcoms sylbi syl5com sylancl syl mpan com12 adantl cA cC wss cA cB
    cin c0 wceq wa cC cA cdif cB wceq cA cB cun cC wceq cA cC wss cA cB cin c0
    wceq wa cC cA cdif cB wceq wa cA cB cun cC cA cC wss cA cB cin c0 wceq wa
    cC cA cdif cB wceq cA cB cun cC wss cA cC wss cC cA cdif cB wceq cA cB cun
    cC wss wi cA cB cin c0 wceq cC cA cdif cB wceq cA cC wss cA cB cun cC wss
    cC cA cdif cB wceq cC cA cdif cC wss cA cC wss cA cB cun cC wss wi cC cA
    difss cC cA cdif cB wceq cC cA cdif cC wss cB cC wss cA cC wss cA cB cun cC
    wss wi cC cA cdif cB cC sseq1 cA cC wss cB cC wss cA cB cun cC wss cA cC
    wss cB cC wss wa cA cB cun cC wss cA cB cC unss biimpi expcom syl6bi mpi
    com12 adantr imp cA cC wss cC cA cdif cB wceq cC cA cB cun wss cA cB cin c0
    wceq cA cC wss cC cA cdif cB wceq wa cC cA cdif cB wss cC cA cB cun wss cC
    cA cdif cB wceq cC cA cdif cB wss cA cC wss cC cA cdif cB eqimss adantl cC
    cA cB ssundif sylibr adantlr eqssd ex impbid $.

  ${
    $d x A $.
    $( Theorem 19.2 of [Margaris] p. 89 with restricted quantifiers (compare
       ~ 19.2 ).  The restricted version is valid only when the domain of
       quantification is not empty.  (Contributed by NM, 15-Nov-2003.) $)
    r19.2z $p |- ( ( A =/= (/) /\ A. x e. A ph ) -> E. x e. A ph ) $=
      wph vx cA wral cA c0 wne wph vx cA wrex wph vx cA wral vx cv cA wcel vx
      wex vx cv cA wcel wph wa vx wex cA c0 wne wph vx cA wrex wph vx cA wral
      vx cv cA wcel wph wi vx wal vx cv cA wcel vx wex vx cv cA wcel wph wa vx
      wex wi wph vx cA df-ral vx cv cA wcel wph vx exintr sylbi vx cA n0 wph vx
      cA df-rex 3imtr4g impcom $.

    $( A response to the notion that the condition ` A =/= (/) ` can be removed
       in ~ r19.2z .  Interestingly enough, ` ph ` does not figure in the
       left-hand side.  (Contributed by Jeff Hankins, 24-Aug-2009.) $)
    r19.2zb $p |- ( A =/= (/) <-> ( A. x e. A ph -> E. x e. A ph ) ) $=
      cA c0 wne wph vx cA wral wph vx cA wrex wi cA c0 wne wph vx cA wral wph
      vx cA wrex wph vx cA r19.2z ex wph vx cA wral wph vx cA wrex cA c0 wne
      wph vx cA wral cA c0 cA c0 wceq wph vx cA wral wph vx c0 wral wph vx c0
      vx cv c0 wcel wph vx cv noel pm2.21i rgen wph vx cA c0 raleq mpbiri
      necon3bi vx cv cA wcel wph wa vx wex vx cv cA wcel vx wex wph vx cA wrex
      cA c0 wne vx cv cA wcel wph vx exsimpl wph vx cA df-rex vx cA n0 3imtr4i
      ja impbii $.
  $}

  ${
    $d x A $.
    r19.3rz.1 $e |- F/ x ph $.
    $( Restricted quantification of wff not containing quantified variable.
       (Contributed by FL, 3-Jan-2008.) $)
    r19.3rz $p |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) ) $=
      cA c0 wne wph vx cv cA wcel vx wex wph wi wph vx cA wral cA c0 wne vx cv
      cA wcel vx wex wph vx cv cA wcel vx wex wph wi wb vx cA n0 vx cv cA wcel
      vx wex wph biimt sylbi wph vx cA wral vx cv cA wcel wph wi vx wal vx cv
      cA wcel vx wex wph wi wph vx cA df-ral vx cv cA wcel wph vx r19.3rz.1
      19.23 bitri syl6bbr $.

    $( Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 26-Oct-2010.) $)
    r19.28z $p |- ( A =/= (/) ->
                   ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) ) $=
      cA c0 wne wph wps vx cA wral wa wph vx cA wral wps vx cA wral wa wph wps
      wa vx cA wral cA c0 wne wph wph vx cA wral wps vx cA wral wph vx cA
      r19.3rz.1 r19.3rz anbi1d wph wps vx cA r19.26 syl6rbbr $.
  $}

  ${
    $d x A $.  $d x ph $.
    $( Restricted quantification of wff not containing quantified variable.
       (Contributed by NM, 10-Mar-1997.) $)
    r19.3rzv $p |- ( A =/= (/) -> ( ph <-> A. x e. A ph ) ) $=
      cA c0 wne wph vx cv cA wcel vx wex wph wi wph vx cA wral cA c0 wne vx cv
      cA wcel vx wex wph vx cv cA wcel vx wex wph wi wb vx cA n0 vx cv cA wcel
      vx wex wph biimt sylbi wph vx cA wral vx cv cA wcel wph wi vx wal vx cv
      cA wcel vx wex wph wi wph vx cA df-ral vx cv cA wcel wph vx 19.23v bitri
      syl6bbr $.

    $( Restricted quantification of wff not containing quantified variable.
       (Contributed by NM, 27-May-1998.) $)
    r19.9rzv $p |- ( A =/= (/) -> ( ph <-> E. x e. A ph ) ) $=
      cA c0 wne wph wph wn vx cA wral wn wph vx cA wrex cA c0 wne wph wn vx cA
      wral wph cA c0 wne wph wn wph wn vx cA wral wph wn vx cA r19.3rzv bicomd
      con2bid wph vx cA dfrex2 syl6bbr $.

    $( Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 19-Aug-2004.) $)
    r19.28zv $p |- ( A =/= (/) ->
                   ( A. x e. A ( ph /\ ps ) <-> ( ph /\ A. x e. A ps ) ) ) $=
      cA c0 wne wph wps vx cA wral wa wph vx cA wral wps vx cA wral wa wph wps
      wa vx cA wral cA c0 wne wph wph vx cA wral wps vx cA wral wph vx cA
      r19.3rzv anbi1d wph wps vx cA r19.26 syl6rbbr $.

    $( Restricted quantifier version of Theorem 19.37 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by Paul Chapman, 8-Oct-2007.) $)
    r19.37zv $p |- ( A =/= (/) ->
                   ( E. x e. A ( ph -> ps ) <-> ( ph -> E. x e. A ps ) ) ) $=
      cA c0 wne wph wps vx cA wrex wi wph vx cA wral wps vx cA wrex wi wph wps
      wi vx cA wrex cA c0 wne wph wph vx cA wral wps vx cA wrex wph vx cA
      r19.3rzv imbi1d wph wps vx cA r19.35 syl6rbbr $.

    $( Restricted version of Theorem 19.45 of [Margaris] p. 90.  (Contributed
       by NM, 27-May-1998.) $)
    r19.45zv $p |- ( A =/= (/) ->
                   ( E. x e. A ( ph \/ ps ) <-> ( ph \/ E. x e. A ps ) ) ) $=
      cA c0 wne wph wps vx cA wrex wo wph vx cA wrex wps vx cA wrex wo wph wps
      wo vx cA wrex cA c0 wne wph wph vx cA wrex wps vx cA wrex wph vx cA
      r19.9rzv orbi1d wph wps vx cA r19.43 syl6rbbr $.
  $}

  ${
    $d x A $.
    r19.27z.1 $e |- F/ x ps $.
    $( Restricted quantifier version of Theorem 19.27 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 26-Oct-2010.) $)
    r19.27z $p |- ( A =/= (/) ->
                   ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) ) $=
      cA c0 wne wph vx cA wral wps wa wph vx cA wral wps vx cA wral wa wph wps
      wa vx cA wral cA c0 wne wps wps vx cA wral wph vx cA wral wps vx cA
      r19.27z.1 r19.3rz anbi2d wph wps vx cA r19.26 syl6rbbr $.
  $}

  ${
    $d x A $.  $d x ps $.
    $( Restricted quantifier version of Theorem 19.27 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 19-Aug-2004.) $)
    r19.27zv $p |- ( A =/= (/) ->
                   ( A. x e. A ( ph /\ ps ) <-> ( A. x e. A ph /\ ps ) ) ) $=
      cA c0 wne wph vx cA wral wps wa wph vx cA wral wps vx cA wral wa wph wps
      wa vx cA wral cA c0 wne wps wps vx cA wral wph vx cA wral wps vx cA
      r19.3rzv anbi2d wph wps vx cA r19.26 syl6rbbr $.

    $( Restricted quantifier version of Theorem 19.36 of [Margaris] p. 90.  It
       is valid only when the domain of quantification is not empty.
       (Contributed by NM, 20-Sep-2003.) $)
    r19.36zv $p |- ( A =/= (/) ->
                   ( E. x e. A ( ph -> ps ) <-> ( A. x e. A ph -> ps ) ) ) $=
      cA c0 wne wph vx cA wral wps wi wph vx cA wral wps vx cA wrex wi wph wps
      wi vx cA wrex cA c0 wne wps wps vx cA wrex wph vx cA wral wps vx cA
      r19.9rzv imbi2d wph wps vx cA r19.35 syl6rbbr $.
  $}

  ${
    $d x A $.
    $( Vacuous quantification is always true.  (Contributed by NM,
       11-Mar-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    rzal $p |- ( A = (/) -> A. x e. A ph ) $=
      cA c0 wceq wph vx cA cA c0 wceq vx cv cA wcel wph vx cv cA wcel cA c0 cA
      vx cv ne0i necon2bi pm2.21d ralrimiv $.

    $( Restricted existential quantification implies its restriction is
       nonempty.  (Contributed by Szymon Jaroszewicz, 3-Apr-2007.) $)
    rexn0 $p |- ( E. x e. A ph -> A =/= (/) ) $=
      wph cA c0 wne vx cA vx cv cA wcel cA c0 wne wph cA vx cv ne0i a1d
      rexlimiv $.

    $( Idempotent law for restricted quantifier.  (Contributed by NM,
       28-Mar-1997.) $)
    ralidm $p |- ( A. x e. A A. x e. A ph <-> A. x e. A ph ) $=
      cA c0 wceq wph vx cA wral vx cA wral wph vx cA wral wb cA c0 wceq wph vx
      cA wral vx cA wral wph vx cA wral wph vx cA wral vx cA rzal wph vx cA
      rzal 2thd cA c0 wceq wn vx cv cA wcel vx wex wph vx cA wral vx cA wral
      wph vx cA wral wb vx cA neq0 vx cv cA wcel vx wex wph vx cA wral vx cv cA
      wcel vx wex wph vx cA wral wi wph vx cA wral vx cA wral vx cv cA wcel vx
      wex wph vx cA wral biimt wph vx cA wral vx cA wral vx cv cA wcel wph vx
      cA wral wi vx wal vx cv cA wcel vx wex wph vx cA wral wi wph vx cA wral
      vx cA df-ral vx cv cA wcel wph vx cA wral vx wph vx cA nfra1 19.23 bitri
      syl6rbbr sylbi pm2.61i $.
  $}

  $( Vacuous universal quantification is always true.  (Contributed by NM,
     20-Oct-2005.) $)
  ral0 $p |- A. x e. (/) ph $=
    wph vx c0 vx cv c0 wcel wph vx cv noel pm2.21i rgen $.

  ${
    $d x A $.
    rgenz.1 $e |- ( ( A =/= (/) /\ x e. A ) -> ph ) $.
    $( Generalization rule that eliminates a non-zero class requirement.
       (Contributed by NM, 8-Dec-2012.) $)
    rgenz $p |- A. x e. A ph $=
      wph vx cA wral cA c0 wph vx cA rzal cA c0 wne wph vx cA rgenz.1 ralrimiva
      pm2.61ine $.
  $}

  ${
    $d x A $.
    ralf0.1 $e |- -. ph $.
    $( The quantification of a falsehood is vacuous when true.  (Contributed by
       NM, 26-Nov-2005.) $)
    ralf0 $p |- ( A. x e. A ph <-> A = (/) ) $=
      wph vx cA wral cA c0 wceq vx cv cA wcel wph wi vx wal vx cv cA wcel wn vx
      wal wph vx cA wral cA c0 wceq vx cv cA wcel wph wi vx cv cA wcel wn vx vx
      cv cA wcel wph wi wph wn vx cv cA wcel wn ralf0.1 vx cv cA wcel wph con3
      mpi alimi wph vx cA df-ral vx cA eq0 3imtr4i wph vx cA rzal impbii $.
  $}

  $( TODO - shorten r19.3zv, r19.27zv, r19.28zv, raaanv w/ non-v $)
  ${
    $d x y A $.
    raaan.1 $e |- F/ y ph $.
    raaan.2 $e |- F/ x ps $.
    $( Rearrange restricted quantifiers.  (Contributed by NM, 26-Oct-2010.) $)
    raaan $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <->
                  ( A. x e. A ph /\ A. y e. A ps ) ) $=
      wph wps wa vy cA wral vx cA wral wph vx cA wral wps vy cA wral wa wb cA
      c0 cA c0 wceq wph wps wa vy cA wral vx cA wral wph vx cA wral wps vy cA
      wral wph wps wa vy cA wral vx cA wral wph vx cA wral wps vy cA wral wa wb
      wph wps wa vy cA wral vx cA rzal wph vx cA rzal wps vy cA rzal wph wps wa
      vy cA wral vx cA wral wph vx cA wral wps vy cA wral wa pm5.1 syl12anc cA
      c0 wne wph wps wa vy cA wral vx cA wral wph wps vy cA wral wa vx cA wral
      wph vx cA wral wps vy cA wral wa cA c0 wne wph wps wa vy cA wral wph wps
      vy cA wral wa vx cA wph wps vy cA raaan.1 r19.28z ralbidv wph wps vy cA
      wral vx cA wps vx vy cA vx cA nfcv raaan.2 nfral r19.27z bitrd pm2.61ine
      $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y A $.
    $( Rearrange restricted quantifiers.  (Contributed by NM, 11-Mar-1997.) $)
    raaanv $p |- ( A. x e. A A. y e. A ( ph /\ ps ) <->
                  ( A. x e. A ph /\ A. y e. A ps ) ) $=
      wph wps wa vy cA wral vx cA wral wph vx cA wral wps vy cA wral wa wb cA
      c0 cA c0 wceq wph wps wa vy cA wral vx cA wral wph vx cA wral wps vy cA
      wral wph wps wa vy cA wral vx cA wral wph vx cA wral wps vy cA wral wa wb
      wph wps wa vy cA wral vx cA rzal wph vx cA rzal wps vy cA rzal wph wps wa
      vy cA wral vx cA wral wph vx cA wral wps vy cA wral wa pm5.1 syl12anc cA
      c0 wne wph wps wa vy cA wral vx cA wral wph wps vy cA wral wa vx cA wral
      wph vx cA wral wps vy cA wral wa cA c0 wne wph wps wa vy cA wral wph wps
      vy cA wral wa vx cA wph wps vy cA r19.28zv ralbidv wph wps vy cA wral vx
      cA r19.27zv bitrd pm2.61ine $.
  $}

  ${
    $d z y $.  $d z x A $.
    $( Set substitution into the first argument of a subset relation.
       (Contributed by Rodolfo Medina, 7-Jul-2010.)  (Proof shortened by Mario
       Carneiro, 14-Nov-2016.) $)
    sbss $p |- ( [ y / x ] x C_ A <-> y C_ A ) $=
      vx cv cA wss vx vz wsb vz cv cA wss vx cv cA wss vx vy wsb vy cv cA wss
      vz vy cv vy vex vx cv cA wss vz vy vx sbequ vz cv vy cv cA sseq1 vx cv cA
      wss vz cv cA wss vx vz vz cv cA wss vx nfv vx cv vz cv cA sseq1 sbie
      vtoclb $.
  $}

  ${
    $d A y $.  $d B y $.  $d C y $.  $d D y $.  $d x y $.
    $( Distribute proper substitution through a subclass relation.
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Alexander
       van der Vekens, 23-Jul-2017.) $)
    sbcss $p |- ( A e. B -> ( [. A / x ]. C C_ D <->
      [_ A / x ]_ C C_ [_ A / x ]_ D ) ) $=
      cA cB wcel vy cv cC wcel vy cv cD wcel wi vy wal vx cA wsbc vy cv vx cA
      cC csb wcel vy cv vx cA cD csb wcel wi vy wal cC cD wss vx cA wsbc vx cA
      cC csb vx cA cD csb wss cA cB wcel vy cv cC wcel vy cv cD wcel wi vy wal
      vx cA wsbc vy cv cC wcel vy cv cD wcel wi vx cA wsbc vy wal vy cv vx cA
      cC csb wcel vy cv vx cA cD csb wcel wi vy wal vy cv cC wcel vy cv cD wcel
      wi vy vx cA cB sbcalg cA cB wcel vy cv cC wcel vy cv cD wcel wi vx cA
      wsbc vy cv vx cA cC csb wcel vy cv vx cA cD csb wcel wi vy cA cB wcel vy
      cv cC wcel vy cv cD wcel wi vx cA wsbc vy cv cC wcel vx cA wsbc vy cv cD
      wcel vx cA wsbc wi vy cv vx cA cC csb wcel vy cv vx cA cD csb wcel wi vy
      cv cC wcel vy cv cD wcel vx cA cB sbcimg cA cB wcel vy cv cC wcel vx cA
      wsbc vy cv vx cA cC csb wcel vy cv cD wcel vx cA wsbc vy cv vx cA cD csb
      wcel vx cA vy cv cC cB sbcel2g vx cA vy cv cD cB sbcel2g imbi12d bitrd
      albidv bitrd cC cD wss vy cv cC wcel vy cv cD wcel wi vy wal vx cA vy cC
      cD dfss2 sbcbii vy vx cA cC csb vx cA cD csb dfss2 3bitr4g $.

  $}


