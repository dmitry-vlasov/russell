
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Power_Sets.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                  Introduce the Axiom of Union

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d w x y z $.
    $( Axiom of Union.  An axiom of Zermelo-Fraenkel set theory.  It states
       that a set ` y ` exists that includes the union of a given set ` x `
       i.e. the collection of all members of the members of ` x ` .  The
       variant ~ axun2 states that the union itself exists.  A version with the
       standard abbreviation for union is ~ uniex2 .  A version using class
       notation is ~ uniex .

       The union of a class ~ df-uni should not be confused with the union of
       two classes ~ df-un .  Their relationship is shown in ~ unipr .
       (Contributed by NM, 23-Dec-1993.) $)
    ax-un $a |- E. y A. z ( E. w ( z e. w /\ w e. x ) -> z e. y ) $.

    $( Axiom of Union expressed with the fewest number of different variables.
       (Contributed by NM, 14-Aug-2003.) $)
    zfun $p |- E. x A. y ( E. x ( y e. x /\ x e. z ) -> y e. x ) $=
      vy cv vw cv wcel vw cv vz cv wcel wa vw wex vy cv vx cv wcel wi vy wal vx
      wex vy cv vx cv wcel vx cv vz cv wcel wa vx wex vy cv vx cv wcel wi vy
      wal vx wex vz vx vy vw ax-un vy cv vw cv wcel vw cv vz cv wcel wa vw wex
      vy cv vx cv wcel wi vy wal vy cv vx cv wcel vx cv vz cv wcel wa vx wex vy
      cv vx cv wcel wi vy wal vx vy cv vw cv wcel vw cv vz cv wcel wa vw wex vy
      cv vx cv wcel wi vy cv vx cv wcel vx cv vz cv wcel wa vx wex vy cv vx cv
      wcel wi vy vy cv vw cv wcel vw cv vz cv wcel wa vw wex vy cv vx cv wcel
      vx cv vz cv wcel wa vx wex vy cv vx cv wcel vy cv vw cv wcel vw cv vz cv
      wcel wa vy cv vx cv wcel vx cv vz cv wcel wa vw vx vw cv vx cv wceq vy cv
      vw cv wcel vy cv vx cv wcel vw cv vz cv wcel vx cv vz cv wcel vw vx vy
      elequ2 vw vx vz elequ1 anbi12d cbvexv imbi1i albii exbii mpbi $.

    $( A variant of the Axiom of Union ~ ax-un .  For any set ` x ` , there
       exists a set ` y ` whose members are exactly the members of the members
       of ` x ` i.e. the union of ` x ` .  Axiom Union of [BellMachover]
       p. 466.  (Contributed by NM, 4-Jun-2006.) $)
    axun2 $p |- E. y A. z ( z e. y <-> E. w ( z e. w /\ w e. x ) ) $=
      vz cv vw cv wcel vw cv vx cv wcel wa vw wex vy vz vx vy vz vw ax-un
      bm1.3ii $.

    $( The Axiom of Union using the standard abbreviation for union.  Given any
       set ` x ` , its union ` y ` exists.  (Contributed by NM, 4-Jun-2006.) $)
    uniex2 $p |- E. y y = U. x $=
      vy cv vx cv cuni wceq vy wex vz cv vy cv wcel vz cv vx cv cuni wcel wb vz
      wal vy wex vz cv vx cv cuni wcel vy vz vz cv vx cv cuni wcel vz cv vy cv
      wcel wi vz wal vy wex vz cv vy cv wcel vy cv vx cv wcel wa vy wex vz cv
      vy cv wcel wi vz wal vy wex vy vz vx zfun vz cv vx cv cuni wcel vz cv vy
      cv wcel wi vz wal vz cv vy cv wcel vy cv vx cv wcel wa vy wex vz cv vy cv
      wcel wi vz wal vy vz cv vx cv cuni wcel vz cv vy cv wcel wi vz cv vy cv
      wcel vy cv vx cv wcel wa vy wex vz cv vy cv wcel wi vz vz cv vx cv cuni
      wcel vz cv vy cv wcel vy cv vx cv wcel wa vy wex vz cv vy cv wcel vy vz
      cv vx cv eluni imbi1i albii exbii mpbir bm1.3ii vy cv vx cv cuni wceq vz
      cv vy cv wcel vz cv vx cv cuni wcel wb vz wal vy vz vy cv vx cv cuni
      dfcleq exbii mpbir $.
  $}

  ${
    $d x y A $.
    uniex.1 $e |- A e. _V $.
    $( The Axiom of Union in class notation.  This says that if ` A ` is a set
       i.e. ` A e. _V ` (see ~ isset ), then the union of ` A ` is also a set.
       Same as Axiom 3 of [TakeutiZaring] p. 16.  (Contributed by NM,
       11-Aug-1993.) $)
    uniex $p |- U. A e. _V $=
      vx cv cuni cvv wcel cA cuni cvv wcel vx cA uniex.1 vx cv cA wceq vx cv
      cuni cA cuni cvv vx cv cA unieq eleq1d vy vx cv cuni vx vy uniex2 issetri
      vtocl $.
  $}

  ${
    $d x A $.
    $( The ZF Axiom of Union in class notation, in the form of a theorem
       instead of an inference.  We use the antecedent ` A e. V ` instead of
       ` A e. _V ` to make the theorem more general and thus shorten some
       proofs; obviously the universal class constant ` _V ` is one possible
       substitution for class variable ` V ` .  (Contributed by NM,
       25-Nov-1994.) $)
    uniexg $p |- ( A e. V -> U. A e. _V ) $=
      vx cv cuni cvv wcel cA cuni cvv wcel vx cA cV vx cv cA wceq vx cv cuni cA
      cuni cvv vx cv cA unieq eleq1d vx cv vx vex uniex vtoclg $.
  $}

  ${
    unex.1 $e |- A e. _V $.
    unex.2 $e |- B e. _V $.
    $( The union of two sets is a set.  Corollary 5.8 of [TakeutiZaring]
       p. 16.  (Contributed by NM, 1-Jul-1994.) $)
    unex $p |- ( A u. B ) e. _V $=
      cA cB cpr cuni cA cB cun cvv cA cB unex.1 unex.2 unipr cA cB cpr cA cB
      prex uniex eqeltrri $.
  $}

  $( A triple of classes exists.  (Contributed by NM, 10-Apr-1994.) $)
  tpex $p |- { A , B , C } e. _V $=
    cA cB cC ctp cA cB cpr cC csn cun cvv cA cB cC df-tp cA cB cpr cC csn cA cB
    prex cC snex unex eqeltri $.

  ${
    $d x y A $.  $d x y B $.
    $( Existence of union is equivalent to existence of its components.
       (Contributed by NM, 11-Jun-1998.) $)
    unexb $p |- ( ( A e. _V /\ B e. _V ) <-> ( A u. B ) e. _V ) $=
      cA cvv wcel cB cvv wcel wa cA cB cun cvv wcel vx cv vy cv cun cvv wcel cA
      vy cv cun cvv wcel cA cB cun cvv wcel vx vy cA cB cvv cvv vx cv cA wceq
      vx cv vy cv cun cA vy cv cun cvv vx cv cA vy cv uneq1 eleq1d vy cv cB
      wceq cA vy cv cun cA cB cun cvv vy cv cB cA uneq2 eleq1d vx cv vy cv vx
      vex vy vex unex vtocl2g cA cB cun cvv wcel cA cvv wcel cB cvv wcel cA cA
      cB cun wss cA cB cun cvv wcel cA cvv wcel cA cB ssun1 cA cA cB cun cvv
      ssexg mpan cB cA cB cun wss cA cB cun cvv wcel cB cvv wcel cB cA ssun2 cB
      cA cB cun cvv ssexg mpan jca impbii $.
  $}

  $( A union of two sets is a set.  Corollary 5.8 of [TakeutiZaring] p. 16.
     (Contributed by NM, 18-Sep-2006.) $)
  unexg $p |- ( ( A e. V /\ B e. W ) -> ( A u. B ) e. _V ) $=
    cA cV wcel cA cvv wcel cB cvv wcel cA cB cun cvv wcel cB cW wcel cA cV elex
    cB cW elex cA cvv wcel cB cvv wcel wa cA cB cun cvv wcel cA cB unexb biimpi
    syl2an $.

  ${
    $( A version of ~ unisn without the ` A e. _V ` hypothesis.  (Contributed
       by Stefan Allan, 14-Mar-2006.) $)
    unisn2 $p |- U. { A } e. { (/) , A } $=
      cA cvv wcel cA csn cuni c0 cA cpr wcel cA cvv wcel cA csn cuni cA c0 cA
      cpr cA cvv unisng c0 cA cvv prid2g eqeltrd cA cvv wcel wn cA csn cuni c0
      cuni c0 cA cpr cA cvv wcel wn cA csn c0 cA cvv wcel wn cA csn c0 wceq cA
      snprc biimpi unieqd c0 cuni c0 c0 cA cpr uni0 c0 cA 0ex prid1 eqeltri
      syl6eqel pm2.61i $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Union of a singleton in the form of a restricted class abstraction.
       (Contributed by NM, 3-Jul-2008.) $)
    unisn3 $p |- ( A e. B -> U. { x e. B | x = A } = A ) $=
      cA cB wcel vx cv cA wceq vx cB crab cuni cA csn cuni cA cA cB wcel vx cv
      cA wceq vx cB crab cA csn vx cB cA rabsn unieqd cA cB unisng eqtrd $.
  $}

  ${
    $d x y z $.
    $( The class of all singletons is a proper class.  (Contributed by NM,
       10-Oct-2008.)  (Proof shortened by Eric Schmidt, 7-Dec-2008.) $)
    snnex $p |- { x | E. y x = { y } } e/ _V $=
      vx cv vy cv csn wceq vy wex vx cab cvv wnel vx cv vy cv csn wceq vy wex
      vx cab cvv wcel wn vx cv vy cv csn wceq vy wex vx cab cvv wcel vx cv vy
      cv csn wceq vy wex vx cab cuni cvv wcel vx cv vy cv csn wceq vy wex vx
      cab cuni cvv wcel cvv cvv wcel vprc vx cv vy cv csn wceq vy wex vx cab
      cuni cvv cvv vz vx cv vy cv csn wceq vy wex vx cab cuni cvv vz cv vx cv
      vy cv csn wceq vy wex vx cab cuni wcel vz cv cvv wcel vz cv vx cv vy cv
      csn wceq vy wex vx cab cuni wcel vz cv vx cv wcel vx cv vy cv csn wceq vy
      wex wa vx wex vz cv vz cv csn wcel vz cv csn vy cv csn wceq vy wex vz cv
      vx cv wcel vx cv vy cv csn wceq vy wex wa vx wex vz cv vz vex snid vy cv
      vz cv wceq vy wex vz cv csn vy cv csn wceq vy wex vy vz a9ev vy cv vz cv
      wceq vz cv csn vy cv csn wceq vy vz cv csn vy cv csn wceq vz cv vy cv vz
      cv vy cv sneq eqcoms eximi ax-mp vz cv vx cv wcel vx cv vy cv csn wceq vy
      wex wa vz cv vz cv csn wcel vz cv csn vy cv csn wceq vy wex wa vx vz cv
      csn vz cv snex vx cv vz cv csn wceq vz cv vx cv wcel vz cv vz cv csn wcel
      vx cv vy cv csn wceq vy wex vz cv csn vy cv csn wceq vy wex vx cv vz cv
      csn vz cv eleq2 vx cv vz cv csn wceq vx cv vy cv csn wceq vz cv csn vy cv
      csn wceq vy vx cv vz cv csn vy cv csn eqeq1 exbidv anbi12d spcev mp2an vx
      cv vy cv csn wceq vy wex vx vz cv eluniab mpbir vz vex 2th eqriv eleq1i
      mtbir vx cv vy cv csn wceq vy wex vx cab cvv uniexg mto vx cv vy cv csn
      wceq vy wex vx cab cvv df-nel mpbir $.
  $}

  $( If the subtrahend of a class difference exists, then the minuend exists
     iff the difference exists.  (Contributed by NM, 12-Nov-2003.)  (Proof
     shortened by Andrew Salmon, 12-Aug-2011.) $)
  difex2 $p |- ( B e. C -> ( A e. _V <-> ( A \ B ) e. _V ) ) $=
    cB cC wcel cA cvv wcel cA cB cdif cvv wcel cA cB cvv difexg cA cB cdif cvv
    wcel cB cC wcel cA cvv wcel cA cB cdif cvv wcel cB cC wcel wa cA cA cB cdif
    cB cun wss cA cB cdif cB cun cvv wcel cA cvv wcel cA cB cA cun cA cB cdif
    cB cun cA cB ssun2 cA cB cdif cB cun cB cA cB cdif cun cB cA cun cA cB cdif
    cB uncom cB cA undif2 eqtr2i sseqtri cA cB cdif cB cvv cC unexg cA cA cB
    cdif cB cun cvv ssexg sylancr expcom impbid2 $.

  ${
    opeluu.1 $e |- A e. _V $.
    opeluu.2 $e |- B e. _V $.
    $( Each member of an ordered pair belongs to the union of the union of a
       class to which the ordered pair belongs.  Lemma 3D of [Enderton] p. 41.
       (Contributed by NM, 31-Mar-1995.)  (Revised by Mario Carneiro,
       27-Feb-2016.) $)
    opeluu $p |- ( <. A , B >. e. C ->
                 ( A e. U. U. C /\ B e. U. U. C ) ) $=
      cA cB cop cC wcel cA cC cuni cuni wcel cB cC cuni cuni wcel cA cB cop cC
      wcel cA cA cB cpr wcel cA cB cpr cC cuni wcel cA cC cuni cuni wcel cA cB
      opeluu.1 prid1 cA cB cpr cA cB cop wcel cA cB cop cC wcel cA cB cpr cC
      cuni wcel cA cB opeluu.1 opeluu.2 opi2 cA cB cpr cA cB cop cC elunii mpan
      cA cA cB cpr cC cuni elunii sylancr cA cB cop cC wcel cB cA cB cpr wcel
      cA cB cpr cC cuni wcel cB cC cuni cuni wcel cA cB opeluu.2 prid2 cA cB
      cpr cA cB cop wcel cA cB cop cC wcel cA cB cpr cC cuni wcel cA cB
      opeluu.1 opeluu.2 opi2 cA cB cpr cA cB cop cC elunii mpan cB cA cB cpr cC
      cuni elunii sylancr jca $.
  $}

  ${
    $d A x y v z $.  $d A x y u z $.
    $( Expression for double union that moves union into a class builder.
       (Contributed by FL, 28-May-2007.) $)
    uniuni $p |- U. U. A = U. { x | E. y ( x = U. y /\ y e. A ) } $=
      vz cv vu cv wcel vu cv cA cuni wcel wa vu wex vz cab vz cv vv cv wcel vv
      cv vx cv vy cv cuni wceq vy cv cA wcel wa vy wex vx cab wcel wa vv wex vz
      cab cA cuni cuni vx cv vy cv cuni wceq vy cv cA wcel wa vy wex vx cab
      cuni vz cv vu cv wcel vu cv cA cuni wcel wa vu wex vz cv vv cv wcel vv cv
      vx cv vy cv cuni wceq vy cv cA wcel wa vy wex vx cab wcel wa vv wex vz vz
      cv vu cv wcel vu cv cA cuni wcel wa vu wex vz cv vu cv wcel vu cv vy cv
      wcel vy cv cA wcel wa vy wex wa vu wex vy cv cA wcel vz cv vy cv cuni
      wcel wa vy wex vz cv vv cv wcel vv cv vx cv vy cv cuni wceq vy cv cA wcel
      wa vy wex vx cab wcel wa vv wex vz cv vu cv wcel vu cv cA cuni wcel wa vz
      cv vu cv wcel vu cv vy cv wcel vy cv cA wcel wa vy wex wa vu vu cv cA
      cuni wcel vu cv vy cv wcel vy cv cA wcel wa vy wex vz cv vu cv wcel vy vu
      cv cA eluni anbi2i exbii vz cv vu cv wcel vu cv vy cv wcel vy cv cA wcel
      wa vy wex wa vu wex vz cv vu cv wcel vu cv vy cv wcel vy cv cA wcel wa wa
      vy wex vu wex vy cv cA wcel vz cv vu cv wcel vu cv vy cv wcel wa vu wex
      wa vy wex vy cv cA wcel vz cv vy cv cuni wcel wa vy wex vz cv vu cv wcel
      vu cv vy cv wcel vy cv cA wcel wa vy wex wa vz cv vu cv wcel vu cv vy cv
      wcel vy cv cA wcel wa wa vy wex vu vz cv vu cv wcel vu cv vy cv wcel vy
      cv cA wcel wa wa vy wex vz cv vu cv wcel vu cv vy cv wcel vy cv cA wcel
      wa vy wex wa vz cv vu cv wcel vu cv vy cv wcel vy cv cA wcel wa vy 19.42v
      bicomi exbii vz cv vu cv wcel vu cv vy cv wcel vy cv cA wcel wa wa vy wex
      vu wex vz cv vu cv wcel vu cv vy cv wcel vy cv cA wcel wa wa vu wex vy
      wex vy cv cA wcel vz cv vu cv wcel vu cv vy cv wcel wa wa vu wex vy wex
      vy cv cA wcel vz cv vu cv wcel vu cv vy cv wcel wa vu wex wa vy wex vz cv
      vu cv wcel vu cv vy cv wcel vy cv cA wcel wa wa vu vy excom vz cv vu cv
      wcel vu cv vy cv wcel vy cv cA wcel wa wa vy cv cA wcel vz cv vu cv wcel
      vu cv vy cv wcel wa wa vy vu vz cv vu cv wcel vu cv vy cv wcel vy cv cA
      wcel wa wa vz cv vu cv wcel vu cv vy cv wcel wa vy cv cA wcel wa vy cv cA
      wcel vz cv vu cv wcel vu cv vy cv wcel wa wa vz cv vu cv wcel vu cv vy cv
      wcel vy cv cA wcel anass vz cv vu cv wcel vu cv vy cv wcel wa vy cv cA
      wcel ancom bitr3i 2exbii vy cv cA wcel vz cv vu cv wcel vu cv vy cv wcel
      wa vy vu exdistr 3bitri vy cv cA wcel vz cv vu cv wcel vu cv vy cv wcel
      wa vu wex wa vy cv cA wcel vz cv vy cv cuni wcel wa vy vz cv vu cv wcel
      vu cv vy cv wcel wa vu wex vz cv vy cv cuni wcel vy cv cA wcel vz cv vy
      cv cuni wcel vz cv vu cv wcel vu cv vy cv wcel wa vu wex vu vz cv vy cv
      eluni bicomi anbi2i exbii 3bitri vy cv cA wcel vz cv vy cv cuni wcel wa
      vy wex vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA wcel wa wa vv wex
      vy wex vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA wcel wa wa vy wex
      vv wex vz cv vv cv wcel vv cv vx cv vy cv cuni wceq vy cv cA wcel wa vy
      wex vx cab wcel wa vv wex vy cv cA wcel vz cv vy cv cuni wcel wa vz cv vv
      cv wcel vv cv vy cv cuni wceq vy cv cA wcel wa wa vv wex vy vy cv cA wcel
      vz cv vy cv cuni wcel wa vy cv cA wcel vz cv vv cv wcel vv cv vy cv cuni
      wceq wa vv wex wa vy cv cA wcel vz cv vv cv wcel vv cv vy cv cuni wceq wa
      wa vv wex vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA wcel wa wa vv
      wex vz cv vy cv cuni wcel vz cv vv cv wcel vv cv vy cv cuni wceq wa vv
      wex vy cv cA wcel vz cv vy cv cuni wcel vv cv vy cv cuni wceq vz cv vv cv
      wcel wa vv wex vz cv vv cv wcel vv cv vy cv cuni wceq wa vv wex vz cv vv
      cv wcel vz cv vy cv cuni wcel vv vy cv cuni vy cv vy vex uniex vv cv vy
      cv cuni vz cv eleq2 ceqsexv vv cv vy cv cuni wceq vz cv vv cv wcel vv
      exancom bitr3i anbi2i vy cv cA wcel vz cv vv cv wcel vv cv vy cv cuni
      wceq wa vv 19.42v vy cv cA wcel vz cv vv cv wcel vv cv vy cv cuni wceq wa
      wa vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA wcel wa wa vv vy cv cA
      wcel vz cv vv cv wcel vv cv vy cv cuni wceq wa wa vz cv vv cv wcel vv cv
      vy cv cuni wceq wa vy cv cA wcel wa vz cv vv cv wcel vv cv vy cv cuni
      wceq vy cv cA wcel wa wa vy cv cA wcel vz cv vv cv wcel vv cv vy cv cuni
      wceq wa ancom vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA wcel anass
      bitri exbii 3bitr2i exbii vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA
      wcel wa wa vy vv excom vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA
      wcel wa wa vy wex vv wex vz cv vv cv wcel vv cv vy cv cuni wceq vy cv cA
      wcel wa vy wex wa vv wex vz cv vv cv wcel vv cv vx cv vy cv cuni wceq vy
      cv cA wcel wa vy wex vx cab wcel wa vv wex vz cv vv cv wcel vv cv vy cv
      cuni wceq vy cv cA wcel wa vv vy exdistr vz cv vv cv wcel vv cv vy cv
      cuni wceq vy cv cA wcel wa vy wex wa vz cv vv cv wcel vv cv vx cv vy cv
      cuni wceq vy cv cA wcel wa vy wex vx cab wcel wa vv vv cv vy cv cuni wceq
      vy cv cA wcel wa vy wex vv cv vx cv vy cv cuni wceq vy cv cA wcel wa vy
      wex vx cab wcel vz cv vv cv wcel vv cv vx cv vy cv cuni wceq vy cv cA
      wcel wa vy wex vx cab wcel vv cv vy cv cuni wceq vy cv cA wcel wa vy wex
      vx cv vy cv cuni wceq vy cv cA wcel wa vy wex vv cv vy cv cuni wceq vy cv
      cA wcel wa vy wex vx vv cv vv vex vx cv vv cv wceq vx cv vy cv cuni wceq
      vy cv cA wcel wa vv cv vy cv cuni wceq vy cv cA wcel wa vy vx cv vv cv
      wceq vx cv vy cv cuni wceq vv cv vy cv cuni wceq vy cv cA wcel vx cv vv
      cv vy cv cuni eqeq1 anbi1d exbidv elab bicomi anbi2i exbii bitri 3bitri
      3bitri abbii vz vu cA cuni df-uni vz vv vx cv vy cv cuni wceq vy cv cA
      wcel wa vy wex vx cab df-uni 3eqtr4i $.
  $}

  ${
    $d x y z $.  $d A y z $.
    $( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by NM, 14-Oct-2010.) $)
    eusv1 $p |- ( E! y A. x y = A <-> E. y A. x y = A ) $=
      vy cv cA wceq vx wal vy weu vy cv cA wceq vx wal vy wex vy cv cA wceq vx
      wal vz cv cA wceq vx wal wa vy cv vz cv wceq wi vz wal vy wal vy cv cA
      wceq vx wal vz cv cA wceq vx wal wa vy cv vz cv wceq wi vy vz vy cv cA
      wceq vx wal vy cv cA wceq vz cv cA wceq vy cv vz cv wceq vz cv cA wceq vx
      wal vy cv cA wceq vx sp vz cv cA wceq vx sp vy cv vz cv cA eqtr3 syl2an
      gen2 vy cv cA wceq vx wal vz cv cA wceq vx wal vy vz vy cv vz cv wceq vy
      cv cA wceq vz cv cA wceq vx vy cv vz cv cA eqeq1 albidv eu4 mpbiran2 $.
  $}

  ${
    $d x y z w $.  $d A y z w $.
    $( Even if ` x ` is free in ` A ` , it is effectively bound when
       ` A ( x ) ` is single-valued.  (Contributed by NM, 14-Oct-2010.)
       (Revised by Mario Carneiro, 14-Oct-2016.) $)
    eusvnf $p |- ( E! y A. x y = A -> F/_ x A ) $=
      vy cv cA wceq vx wal vy weu vy cv cA wceq vx wal vy wex vx cA wnfc vy cv
      cA wceq vx wal vy euex vy cv cA wceq vx wal vx cA wnfc vy vy cv cA wceq
      vx wal vx vz cv cA csb vx vw cv cA csb wceq vw wal vz wal vx cA wnfc vy
      cv cA wceq vx wal vx vz cv cA csb vx vw cv cA csb wceq vz vw vy cv cA
      wceq vx wal vy cv vx vz cv cA csb vx vw cv cA csb vz cv cvv wcel vy cv cA
      wceq vx wal vy cv vx vz cv cA csb wceq wi vz vex vy cv cA wceq vy cv vx
      vz cv cA csb wceq vx vz cv cvv vx vz cv nfcv vx vy cv vx vz cv cA csb vx
      vz cv cA nfcsb1v nfeq2 vx cv vz cv wceq cA vx vz cv cA csb vy cv vx vz cv
      cA csbeq1a eqeq2d spcgf ax-mp vw cv cvv wcel vy cv cA wceq vx wal vy cv
      vx vw cv cA csb wceq wi vw vex vy cv cA wceq vy cv vx vw cv cA csb wceq
      vx vw cv cvv vx vw cv nfcv vx vy cv vx vw cv cA csb vx vw cv cA nfcsb1v
      nfeq2 vx cv vw cv wceq cA vx vw cv cA csb vy cv vx vw cv cA csbeq1a
      eqeq2d spcgf ax-mp eqtr3d alrimivv vx vz vw cA sbnfc2 sylibr exlimiv syl
      $.

    $( Two ways to say that ` A ( x ) ` is a set expression that does not
       depend on ` x ` .  (Contributed by Mario Carneiro, 18-Nov-2016.) $)
    eusvnfb $p |- ( E! y A. x y = A <-> ( F/_ x A /\ A e. _V ) ) $=
      vy cv cA wceq vx wal vy weu vx cA wnfc cA cvv wcel wa vy cv cA wceq vx
      wal vy weu vx cA wnfc cA cvv wcel vx vy cA eusvnf vy cv cA wceq vx wal vy
      weu vy cv cA wceq vx wal vy wex cA cvv wcel vy cv cA wceq vx wal vy euex
      vy cv cA wceq vx wal cA cvv wcel vy vy cv cA wceq cA cvv wcel vx vy cv cA
      wceq cA vy cv cvv vy cv cA wceq id vy vex syl6eqelr sps exlimiv syl jca
      vx cA wnfc cA cvv wcel wa vy cv cA wceq vx wal vy wex vy cv cA wceq vx
      wal vy weu vx cA wnfc cA cvv wcel vy cv cA wceq vx wal vy wex cA cvv wcel
      vy cv cA wceq vy wex vx cA wnfc vy cv cA wceq vx wal vy wex vy cA isset
      vx cA wnfc vy cv cA wceq vy cv cA wceq vx wal vy vx cA wnfc vy cv cA wceq
      vx vx cA wnfc vx vy cv cA vx cA wnfc vx vy cv nfcvd vx cA wnfc id nfeqd
      nfrd eximdv syl5bi imp vx vy cA eusv1 sylibr impbii $.
  $}

  ${
    $d x y $.  $d A y $.
    $( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by NM, 14-Oct-2010.)  (Revised by Mario
       Carneiro, 18-Nov-2016.) $)
    eusv2i $p |- ( E! y A. x y = A -> E! y E. x y = A ) $=
      vy cv cA wceq vx wal vy weu vy cv cA wceq vx wex vy weu vy cv cA wceq vx
      wal vy weu vy cv cA wceq vx wex vy cv cA wceq vx wal vy vy cv cA wceq vx
      wal vy nfeu1 vy cv cA wceq vx wal vy weu vy cv cA wceq vx wex vy cv cA
      wceq vx wal vy cv cA wceq vx wal vy weu vy cv cA wceq vx wnf vy cv cA
      wceq vx wex vy cv cA wceq vx wal wi vy cv cA wceq vx wal vy weu vx vy cv
      cA vy cv cA wceq vx wal vy weu vx vy cv nfcvd vx vy cA eusvnf nfeqd vy cv
      cA wceq vx nf2 sylib vy cv cA wceq vx 19.2 impbid1 eubid ibir $.
  $}

  ${
    $d x y z v w $.  $d A y z w v $.
    eusv2.1 $e |- A e. _V $.
    $( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by Mario Carneiro, 18-Nov-2016.) $)
    eusv2nf $p |- ( E! y E. x y = A <-> F/_ x A ) $=
      vy cv cA wceq vx wex vy weu vx cA wnfc vy cv cA wceq vx wex vy weu vy cv
      cA wceq vx wnf vy wal vx cA wnfc vy cv cA wceq vx wex vy weu vy cv cA
      wceq vx wnf vy vy cv cA wceq vx wex vy nfeu1 vy cv cA wceq vx wex vy weu
      vy cv cA wceq vx wex vy cv cA wceq wi vx wal vy cv cA wceq vx wnf vy cv
      cA wceq vx wex vy weu vy cv cA wceq vx wex vy cv cA wceq wi vx vy cv cA
      wceq vx wex vx vy vy cv cA wceq vx nfe1 nfeu vy cv cA wceq vx wex vy weu
      vy cv cA wceq vx wex vy cv cA wceq wa vy wex vy cv cA wceq vx wex vy cv
      cA wceq wi vy cv cA wceq vy wex vy cv cA wceq vx wex vy cv cA wceq wa vy
      wex vy cA eusv2.1 isseti vy cv cA wceq vy cv cA wceq vx wex vy cv cA wceq
      wa vy vy cv cA wceq vy cv cA wceq vx wex vy cv cA wceq vx 19.8a ancri
      eximi ax-mp vy cv cA wceq vx wex vy cv cA wceq vy eupick mpan2 alrimi vy
      cv cA wceq vx nf3 sylibr alrimi cA cvv wcel vx cA wnfc vy cv cA wceq vx
      wnf vy wal wb vx vx vy cA cvv dfnfc2 eusv2.1 mpg sylibr vx cA wnfc vy cv
      cA wceq vx wal vy weu vy cv cA wceq vx wex vy weu vy cv cA wceq vx wal vy
      weu vx cA wnfc cA cvv wcel eusv2.1 vx vy cA eusvnfb mpbiran2 vx vy cA
      eusv2i sylbir impbii $.

    $( Two ways to express single-valuedness of a class expression
       ` A ( x ) ` .  (Contributed by NM, 15-Oct-2010.)  (Proof shortened by
       Mario Carneiro, 18-Nov-2016.) $)
    eusv2 $p |- ( E! y E. x y = A <-> E! y A. x y = A ) $=
      vy cv cA wceq vx wex vy weu vx cA wnfc vy cv cA wceq vx wal vy weu vx vy
      cA eusv2.1 eusv2nf vy cv cA wceq vx wal vy weu vx cA wnfc cA cvv wcel
      eusv2.1 vx vy cA eusvnfb mpbiran2 bitr4i $.
  $}

  ${
    $d x z A $.  $d w x z B $.  $d x z C $.  $d w x z ph $.  $d w x y z $.
    $( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  (Contributed by NM, 16-Dec-2012.)  (Proof shortened by
       Mario Carneiro, 18-Nov-2016.) $)
    reusv1 $p |- ( E. y e. B ph -> ( E! x e. A A. y e. B ( ph -> x = C )
                   <-> E. x e. A A. y e. B ( ph -> x = C ) ) ) $=
      wph vy cB wrex wph vx cv cC wceq wi vy cB wral vx wmo wph vx cv cC wceq
      wi vy cB wral vx cA wrmo wph vx cv cC wceq wi vy cB wral vx cA wreu wph
      vx cv cC wceq wi vy cB wral vx cA wrex wb wph wph vx cv cC wceq wi vy cB
      wral vx wmo vy cB wph vx cv cC wceq wi vy cB wral vy vx wph vx cv cC wceq
      wi vy cB nfra1 nfmo vy cv cB wcel wph wph vx cv cC wceq wi vy cB wral vx
      wmo vy cv cB wcel wph wa wph vx cv cC wceq wi vy cB wral vx cv cC wceq wi
      vx wal vx cv cC wceq vx wmo wph vx cv cC wceq wi vy cB wral vx wmo vy cv
      cB wcel wph wa wph vx cv cC wceq wi vy cB wral vx cv cC wceq wi vx wph vx
      cv cC wceq wi vy cB wral vy cv cB wcel wph wa vx cv cC wceq wph vx cv cC
      wceq wi vy cB wral vy cv cB wcel wph vx cv cC wceq wph vx cv cC wceq wi
      vy cB rsp imp3a com12 alrimiv vx cC moeq wph vx cv cC wceq wi vy cB wral
      vx cv cC wceq vx moim ee10 ex rexlimi wph vx cv cC wceq wi vy cB wral vx
      cA mormo wph vx cv cC wceq wi vy cB wral vx cA wreu wph vx cv cC wceq wi
      vy cB wral vx cA wrex wph vx cv cC wceq wi vy cB wral vx cA wrmo wph vx
      cv cC wceq wi vy cB wral vx cA reu5 rbaib 3syl $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d x z C $.  $d x z ph $.
    $( Lemma for ~ reusv2 .  (Contributed by NM, 22-Oct-2010.)  (Proof
       shortened by Mario Carneiro, 19-Nov-2016.) $)
    reusv2lem1 $p |- ( A =/= (/) -> ( E! x A. y e. A x = B
                     <-> E. x A. y e. A x = B ) ) $=
      cA c0 wne vx cv cB wceq vy cA wral vx wmo vx cv cB wceq vy cA wral vx weu
      vx cv cB wceq vy cA wral vx wex wb cA c0 wne vy cv cA wcel vy wex vx cv
      cB wceq vy cA wral vx wmo vy cA n0 vy cv cA wcel vx cv cB wceq vy cA wral
      vx wmo vy vx cv cB wceq vy cA wral vy vx vx cv cB wceq vy cA nfra1 nfmo
      vy cv cA wcel vx cv cB wceq vy cA wral vx cv cB wceq wi vx wal vx cv cB
      wceq vx wmo vx cv cB wceq vy cA wral vx wmo vy cv cA wcel vx cv cB wceq
      vy cA wral vx cv cB wceq wi vx vx cv cB wceq vy cA wral vy cv cA wcel vx
      cv cB wceq vx cv cB wceq vy cA rsp com12 alrimiv vx cB moeq vx cv cB wceq
      vy cA wral vx cv cB wceq vx moim ee10 exlimi sylbi vx cv cB wceq vy cA
      wral vx weu vx cv cB wceq vy cA wral vx wex vx cv cB wceq vy cA wral vx
      wmo vx cv cB wceq vy cA wral vx eu5 rbaib syl $.

    $( Lemma for ~ reusv2 .  (Contributed by NM, 27-Oct-2010.)  (Proof
       shortened by Mario Carneiro, 19-Nov-2016.) $)
    reusv2lem2 $p |- ( E! x A. y e. A x = B -> E! x E. y e. A x = B ) $=
      vx cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA wrex vx weu wi cA c0
      cA c0 wceq vx cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA wrex vx
      weu vx cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA wral vx wal cA c0
      wceq vx cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA wral wn vx wex
      vx cv cB wceq vy cA wral vx wal wn vx cv cB wceq vy cA wral vx eunex vx
      cv cB wceq vy cA wral vx exnal sylib cA c0 wceq vx cv cB wceq vy cA wral
      vx vx cv cB wceq vy cA rzal alrimiv nsyl3 pm2.21d cA c0 wne vx cv cB wceq
      vy cA wral vx weu vx cv cB wceq vy cA wrex vx weu cA c0 wne vx cv cB wceq
      vy cA wral vx weu wa vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA
      wral vx weu cA c0 wne vx cv cB wceq vy cA wral vx weu simpr cA c0 wne vx
      cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA wrex vx weu vx cv cB
      wceq vy cA wral vx weu wb vx cv cB wceq vy cA wral vx weu vz cv cB wceq
      vy cA wral vz wex cA c0 wne vx cv cB wceq vy cA wrex vx weu vx cv cB wceq
      vy cA wral vx weu wb vx cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA
      wral vx wex vz cv cB wceq vy cA wral vz wex vx cv cB wceq vy cA wral vx
      euex vx cv cB wceq vy cA wral vz cv cB wceq vy cA wral vx vz vx cv vz cv
      wceq vx cv cB wceq vz cv cB wceq vy cA vx cv vz cv cB eqeq1 ralbidv
      cbvexv sylib cA c0 wne vz cv cB wceq vy cA wral vx cv cB wceq vy cA wrex
      vx weu vx cv cB wceq vy cA wral vx weu wb vz cA c0 wne vz cv cB wceq vy
      cA wral vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA wral vx weu
      wb cA c0 wne vz cv cB wceq vy cA wral wa vx cv cB wceq vy cA wrex vx cv
      cB wceq vy cA wral vx cA c0 wne vz cv cB wceq vy cA wral wa vx cv cB wceq
      vy cA wrex vx cv cB wceq vy cA wral cA c0 wne vz cv cB wceq vy cA wral wa
      vx cv cB wceq vx cv cB wceq vy cA wral vy cA cA c0 wne vz cv cB wceq vy
      cA wral vy cA c0 wne vy nfv vz cv cB wceq vy cA nfra1 nfan vx cv cB wceq
      vy cA nfra1 cA c0 wne vz cv cB wceq vy cA wral wa vy cv cA wcel vx cv cB
      wceq vx cv cB wceq vy cA wral cA c0 wne vz cv cB wceq vy cA wral wa vy cv
      cA wcel vx cv cB wceq wa wa vx cv vz cv wceq vx cv cB wceq vy cA wral cA
      c0 wne vz cv cB wceq vy cA wral wa vy cv cA wcel vx cv cB wceq wa wa vx
      cv cB vz cv cA c0 wne vz cv cB wceq vy cA wral wa vy cv cA wcel vx cv cB
      wceq simprr vz cv cB wceq vy cA wral vy cv cA wcel vz cv cB wceq cA c0
      wne vx cv cB wceq vz cv cB wceq vy cA wral vy cv cA wcel vz cv cB wceq vz
      cv cB wceq vy cA rsp imp ad2ant2lr eqtr4d cA c0 wne vz cv cB wceq vy cA
      wral wa vy cv cA wcel vx cv cB wceq wa wa vx cv cB wceq vy cA wral vx cv
      vz cv wceq vz cv cB wceq vy cA wral cA c0 wne vz cv cB wceq vy cA wral vy
      cv cA wcel vx cv cB wceq wa simplr vx cv vz cv wceq vx cv cB wceq vz cv
      cB wceq vy cA vx cv vz cv cB eqeq1 ralbidv syl5ibrcom mpd exp32 rexlimd
      cA c0 wne vx cv cB wceq vy cA wral vx cv cB wceq vy cA wrex wi vz cv cB
      wceq vy cA wral cA c0 wne vx cv cB wceq vy cA wral vx cv cB wceq vy cA
      wrex vx cv cB wceq vy cA r19.2z ex adantr impbid eubidv ex exlimdv syl5
      imp mpbird ex pm2.61ine $.

    $( Lemma for ~ reusv2 .  (Contributed by NM, 14-Dec-2012.)  (Proof
       shortened by Mario Carneiro, 19-Nov-2016.) $)
    reusv2lem3 $p |- ( A. y e. A B e. _V ->
          ( E! x E. y e. A x = B <-> E! x A. y e. A x = B ) ) $=
      cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy
      cA wral vx weu cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu vx
      cv cB wceq vy cA wral vx weu cB cvv wcel vy cA wral vx cv cB wceq vy cA
      wrex vx weu wa vx cv cB wceq vy cA wral vx weu vx cv cB wceq vy cA wrex
      vx weu cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu simpr cB
      cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu wa vx cv cB wceq vy
      cA wral vx cv cB wceq vy cA wrex vx cB cvv wcel vy cA wral vx cv cB wceq
      vy cA wrex vx weu vx cB cvv wcel vy cA wral vx nfv vx cv cB wceq vy cA
      wrex vx nfeu1 nfan cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu
      wa vx cv cB wceq vy cA wral vx cv cB wceq vy cA wrex cB cvv wcel vy cA
      wral vx cv cB wceq vy cA wrex vx weu wa cA c0 wne vx cv cB wceq vy cA
      wral vx cv cB wceq vy cA wrex wi vx cv cB wceq vy cA wrex vx weu cA c0
      wne cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu vx cv cB wceq
      vy cA wrex vx wex cA c0 wne vx cv cB wceq vy cA wrex vx euex vx cv cB
      wceq vy cA wrex cA c0 wne vx vx cv cB wceq vy cA rexn0 exlimiv syl adantl
      cA c0 wne vx cv cB wceq vy cA wral vx cv cB wceq vy cA wrex vx cv cB wceq
      vy cA r19.2z ex syl cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx
      weu wa vx cv cB wceq vy cA wrex vx cv cB wceq vy cA cB cvv wcel vy cA
      wral vx cv cB wceq vy cA wrex vx weu vy cB cvv wcel vy cA nfra1 vx cv cB
      wceq vy cA wrex vy vx vx cv cB wceq vy cA nfre1 nfeu nfan vx cv cB wceq
      vy cA nfre1 cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu wa vy
      cv cA wcel vx cv cB wceq vy cA wrex vx cv cB wceq cB cvv wcel vy cA wral
      vx cv cB wceq vy cA wrex vx weu wa vy cv cA wcel vx cv cB wceq vy cA wrex
      vx cv cB wceq wi cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu
      wa vy cv cA wcel wa vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA
      wrex vx cv cB wceq wa vx wex vx cv cB wceq vy cA wrex vx cv cB wceq wi cB
      cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu vy cv cA wcel simplr
      cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu wa vy cv cA wcel
      wa vy cv cA wcel vx cv cB wceq vx wex vx cv cB wceq vy cA wrex vx cv cB
      wceq wa vx wex cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx weu wa
      vy cv cA wcel simpr cB cvv wcel vy cA wral vx cv cB wceq vy cA wrex vx
      weu wa vy cv cA wcel wa cB cvv wcel vx cv cB wceq vx wex cB cvv wcel vy
      cA wral vx cv cB wceq vy cA wrex vx weu wa vy cv cA wcel cB cvv wcel cB
      cvv wcel vy cA wral vy cv cA wcel cB cvv wcel wi vx cv cB wceq vy cA wrex
      vx weu cB cvv wcel vy cA rsp adantr imp vx cB isset sylib vy cv cA wcel
      vx cv cB wceq vx cv cB wceq vy cA wrex vx cv cB wceq wa vx vy cv cA wcel
      vx cv cB wceq vx cv cB wceq vy cA wrex vy cv cA wcel vx cv cB wceq vx cv
      cB wceq vy cA wrex vx cv cB wceq vy cA rspe ex ancrd eximdv sylc vx cv cB
      wceq vy cA wrex vx cv cB wceq vx eupick syl2anc ex com23 ralrimd impbid
      eubid mpbird ex vx vy cA cB reusv2lem2 impbid1 $.

    $( Lemma for ~ reusv2 .  (Contributed by NM, 13-Dec-2012.) $)
    reusv2lem4 $p |- ( E! x e. A E. y e. B ( ph /\ x = C )
            <-> E! x A. y e. B ( ( C e. A /\ ph ) -> x = C ) ) $=
      wph vx cv cC wceq wa vy cB wrex vx cA wreu vx cv cA wcel wph vx cv cC
      wceq wa vy cB wrex wa vx weu vx cv vy vz cv cC csb wceq vz cC cA wcel wph
      wa vy cB crab wrex vx weu cC cA wcel wph wa vx cv cC wceq wi vy cB wral
      vx weu wph vx cv cC wceq wa vy cB wrex vx cA df-reu vx cv cA wcel wph vx
      cv cC wceq wa vy cB wrex wa vx cv vy vz cv cC csb wceq vz cC cA wcel wph
      wa vy cB crab wrex vx vx cv cA wcel wph vx cv cC wceq wa wa vy cB wrex vx
      cv cC wceq vy cC cA wcel wph wa vy cB crab wrex vx cv cA wcel wph vx cv
      cC wceq wa vy cB wrex wa vx cv vy vz cv cC csb wceq vz cC cA wcel wph wa
      vy cB crab wrex vx cv cA wcel wph vx cv cC wceq wa wa vx cv cC wceq vy cB
      cC cA wcel wph wa vy cB crab vy cv cB wcel cC cA wcel wph wa vx cv cC
      wceq wa wa vy cv cB wcel cC cA wcel wph wa wa vx cv cC wceq wa vy cv cB
      wcel vx cv cA wcel wph vx cv cC wceq wa wa wa vy cv cC cA wcel wph wa vy
      cB crab wcel vx cv cC wceq wa vy cv cB wcel cC cA wcel wph wa wa vx cv cC
      wceq wa vy cv cB wcel cC cA wcel wph wa vx cv cC wceq wa wa vy cv cB wcel
      cC cA wcel wph wa vx cv cC wceq anass bicomi vx cv cA wcel wph vx cv cC
      wceq wa wa cC cA wcel wph wa vx cv cC wceq wa vy cv cB wcel vx cv cA wcel
      wph vx cv cC wceq wa wa vx cv cA wcel wph wa vx cv cC wceq wa cC cA wcel
      wph wa vx cv cC wceq wa vx cv cA wcel wph vx cv cC wceq anass vx cv cC
      wceq vx cv cA wcel wph wa cC cA wcel wph wa vx cv cC wceq vx cv cA wcel
      cC cA wcel wph vx cv cC cA eleq1 anbi1d pm5.32ri bitr3i anbi2i vy cv cC
      cA wcel wph wa vy cB crab wcel vy cv cB wcel cC cA wcel wph wa wa vx cv
      cC wceq cC cA wcel wph wa vy cB rabid anbi1i 3bitr4i rexbii2 vx cv cA
      wcel wph vx cv cC wceq wa vy cB r19.42v vx cv cC wceq vx cv vy vz cv cC
      csb wceq vy vz cC cA wcel wph wa vy cB crab cC cA wcel wph wa vy cB
      nfrab1 vz cC cA wcel wph wa vy cB crab nfcv vx cv cC wceq vz nfv vy vx cv
      vy vz cv cC csb vy vz cv cC nfcsb1v nfeq2 vy cv vz cv wceq cC vy vz cv cC
      csb vx cv vy vz cv cC csbeq1a eqeq2d cbvrexf 3bitr3i eubii vx cv vy vz cv
      cC csb wceq vz cC cA wcel wph wa vy cB crab wrex vx weu vx cv vy vz cv cC
      csb wceq vz cC cA wcel wph wa vy cB crab wral vx weu cC cA wcel wph wa vx
      cv cC wceq wi vy cB wral vx weu vy vz cv cC csb cvv wcel vz cC cA wcel
      wph wa vy cB crab wral vx cv vy vz cv cC csb wceq vz cC cA wcel wph wa vy
      cB crab wrex vx weu vx cv vy vz cv cC csb wceq vz cC cA wcel wph wa vy cB
      crab wral vx weu wb cC cvv wcel vy cC cA wcel wph wa vy cB crab wral vy
      vz cv cC csb cvv wcel vz cC cA wcel wph wa vy cB crab wral cC cvv wcel vy
      cC cA wcel wph wa vy cB crab vy cv cC cA wcel wph wa vy cB crab wcel vy
      cv cB wcel cC cA wcel wph wa wa cC cvv wcel cC cA wcel wph wa vy cB rabid
      cC cA wcel cC cvv wcel vy cv cB wcel wph cC cA elex ad2antrl sylbi rgen
      cC cvv wcel vy vz cv cC csb cvv wcel vy vz cC cA wcel wph wa vy cB crab
      cC cA wcel wph wa vy cB nfrab1 vz cC cA wcel wph wa vy cB crab nfcv cC
      cvv wcel vz nfv vy vy vz cv cC csb cvv vy vz cv cC nfcsb1v nfel1 vy cv vz
      cv wceq cC vy vz cv cC csb cvv vy vz cv cC csbeq1a eleq1d cbvralf mpbi vx
      vz cC cA wcel wph wa vy cB crab vy vz cv cC csb reusv2lem3 ax-mp vx cv vy
      vz cv cC csb wceq vz cC cA wcel wph wa vy cB crab wral cC cA wcel wph wa
      vx cv cC wceq wi vy cB wral vx vx cv vy vz cv cC csb wceq vz cC cA wcel
      wph wa vy cB crab wral vz cv cC cA wcel wph wa vy cB crab wcel vx cv vy
      vz cv cC csb wceq wi vz wal vy cv cC cA wcel wph wa vy cB crab wcel vx cv
      cC wceq wi vy wal cC cA wcel wph wa vx cv cC wceq wi vy cB wral vx cv vy
      vz cv cC csb wceq vz cC cA wcel wph wa vy cB crab df-ral vy cv cC cA wcel
      wph wa vy cB crab wcel vx cv cC wceq wi vz cv cC cA wcel wph wa vy cB
      crab wcel vx cv vy vz cv cC csb wceq wi vy vz vy cv cC cA wcel wph wa vy
      cB crab wcel vx cv cC wceq wi vz nfv vz cv cC cA wcel wph wa vy cB crab
      wcel vx cv vy vz cv cC csb wceq vy vy vz cv cC cA wcel wph wa vy cB crab
      cC cA wcel wph wa vy cB nfrab1 nfel2 vy vx cv vy vz cv cC csb vy vz cv cC
      nfcsb1v nfeq2 nfim vy cv vz cv wceq vy cv cC cA wcel wph wa vy cB crab
      wcel vz cv cC cA wcel wph wa vy cB crab wcel vx cv cC wceq vx cv vy vz cv
      cC csb wceq vy cv vz cv cC cA wcel wph wa vy cB crab eleq1 vy cv vz cv
      wceq cC vy vz cv cC csb vx cv vy vz cv cC csbeq1a eqeq2d imbi12d cbval vy
      cv cC cA wcel wph wa vy cB crab wcel vx cv cC wceq wi vy wal vy cv cB
      wcel cC cA wcel wph wa vx cv cC wceq wi wi vy wal cC cA wcel wph wa vx cv
      cC wceq wi vy cB wral vy cv cC cA wcel wph wa vy cB crab wcel vx cv cC
      wceq wi vy cv cB wcel cC cA wcel wph wa vx cv cC wceq wi wi vy vy cv cC
      cA wcel wph wa vy cB crab wcel vx cv cC wceq wi vy cv cB wcel cC cA wcel
      wph wa wa vx cv cC wceq wi vy cv cB wcel cC cA wcel wph wa vx cv cC wceq
      wi wi vy cv cC cA wcel wph wa vy cB crab wcel vy cv cB wcel cC cA wcel
      wph wa wa vx cv cC wceq cC cA wcel wph wa vy cB rabid imbi1i vy cv cB
      wcel cC cA wcel wph wa vx cv cC wceq impexp bitri albii cC cA wcel wph wa
      vx cv cC wceq wi vy cB df-ral bitr4i 3bitr2i eubii bitri 3bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x C $.
    $( Lemma for ~ reusv2 .  (Contributed by NM, 4-Jan-2013.)  (Proof shortened
       by Mario Carneiro, 19-Nov-2016.) $)
    reusv2lem5 $p |- ( ( A. y e. B C e. A /\ B =/= (/) )
          -> ( E! x e. A E. y e. B x = C <-> E! x e. A A. y e. B x = C ) ) $=
      cC cA wcel vy cB wral cB c0 wne wa cC cA wcel wtru wa vx cv cC wceq wi vy
      cB wral vx weu vx cv cA wcel vx cv cC wceq vy cB wral wa vx weu vx cv cC
      wceq vy cB wrex vx cA wreu vx cv cC wceq vy cB wral vx cA wreu cC cA wcel
      vy cB wral cC cA wcel wtru wa vx cv cC wceq wi vy cB wral vx weu vx cv cA
      wcel vx cv cC wceq wa vy cB wral vx weu cB c0 wne vx cv cA wcel vx cv cC
      wceq vy cB wral wa vx weu cC cA wcel vy cB wral cC cA wcel wtru wa vx cv
      cC wceq wi vy cB wral vx cv cA wcel vx cv cC wceq wa vy cB wral vx cC cA
      wcel vy cB wral cC cA wcel wtru wa vx cv cC wceq wi vx cv cA wcel vx cv
      cC wceq wa wb vy cB wral cC cA wcel wtru wa vx cv cC wceq wi vy cB wral
      vx cv cA wcel vx cv cC wceq wa vy cB wral wb cC cA wcel cC cA wcel wtru
      wa vx cv cC wceq wi vx cv cA wcel vx cv cC wceq wa wb vy cB cC cA wcel cC
      cA wcel wtru wa vx cv cC wceq wi cC cA wcel vx cv cC wceq wa vx cv cA
      wcel vx cv cC wceq wa cC cA wcel vx cv cC wceq cC cA wcel wtru wa vx cv
      cC wceq wi cC cA wcel vx cv cC wceq wa cC cA wcel wtru vx cv cC wceq cC
      cA wcel wtru wa vx cv cC wceq wi wb tru cC cA wcel wtru wa vx cv cC wceq
      biimt mpan2 cC cA wcel vx cv cC wceq ibar bitr3d vx cv cC wceq vx cv cA
      wcel cC cA wcel vx cv cC cA eleq1 pm5.32ri syl6bbr ralimi cC cA wcel wtru
      wa vx cv cC wceq wi vx cv cA wcel vx cv cC wceq wa vy cB ralbi syl eubidv
      cB c0 wne vx cv cA wcel vx cv cC wceq wa vy cB wral vx cv cA wcel vx cv
      cC wceq vy cB wral wa vx vx cv cA wcel vx cv cC wceq vy cB r19.28zv
      eubidv sylan9bb vx cv cC wceq vy cB wrex vx cA wreu wtru vx cv cC wceq wa
      vy cB wrex vx cA wreu cC cA wcel wtru wa vx cv cC wceq wi vy cB wral vx
      weu vx cv cC wceq vy cB wrex wtru vx cv cC wceq wa vy cB wrex vx cA vx cv
      cC wceq wtru vx cv cC wceq wa vy cB wtru vx cv cC wceq tru biantrur
      rexbii reubii wtru vx vy cA cB cC reusv2lem4 bitri vx cv cC wceq vy cB
      wral vx cA df-reu 3bitr4g $.
  $}

  ${
    $d w x y z A $.  $d w x z B $.  $d w x z C $.  $d w x z ph $.
    $( Two ways to express single-valuedness of a class expression ` C ( y ) `
       that is constant for those ` y e. B ` such that ` ph ` .  The first
       antecedent ensures that the constant value belongs to the existential
       uniqueness domain ` A ` , and the second ensures that ` C ( y ) ` is
       evaluated for at least one ` y ` .  (Contributed by NM, 4-Jan-2013.)
       (Proof shortened by Mario Carneiro, 19-Nov-2016.) $)
    reusv2 $p |- ( ( A. y e. B ( ph -> C e. A ) /\ E. y e. B ph )
          -> ( E! x e. A E. y e. B ( ph /\ x = C )
                   <-> E! x e. A A. y e. B ( ph -> x = C ) ) ) $=
      wph cC cA wcel wi vy cB wral vy vz cv cC csb cA wcel vz wph vy cB crab
      wral wph vy cB crab c0 wne wph vx cv cC wceq wa vy cB wrex vx cA wreu wph
      vx cv cC wceq wi vy cB wral vx cA wreu wb wph vy cB wrex vy vz cv cC csb
      cA wcel vz wph vy cB crab wral cC cA wcel vy wph vy cB crab wral wph cC
      cA wcel wi vy cB wral cC cA wcel vy vz cv cC csb cA wcel vy vz wph vy cB
      crab wph vy cB nfrab1 vz wph vy cB crab nfcv cC cA wcel vz nfv vy vy vz
      cv cC csb cA vy vz cv cC nfcsb1v nfel1 vy cv vz cv wceq cC vy vz cv cC
      csb cA vy vz cv cC csbeq1a eleq1d cbvralf cC cA wcel wph cC cA wcel wi vy
      wph vy cB crab cB vy cv wph vy cB crab wcel cC cA wcel wi vy cv cB wcel
      wph wa cC cA wcel wi vy cv cB wcel wph cC cA wcel wi wi vy cv wph vy cB
      crab wcel vy cv cB wcel wph wa cC cA wcel wph vy cB rabid imbi1i vy cv cB
      wcel wph cC cA wcel impexp bitri ralbii2 bitr3i wph vy cB rabn0 vy vz cv
      cC csb cA wcel vz wph vy cB crab wral wph vy cB crab c0 wne wa vx cv vy
      vz cv cC csb wceq vz wph vy cB crab wrex vx cA wreu vx cv vy vz cv cC csb
      wceq vz wph vy cB crab wral vx cA wreu wph vx cv cC wceq wa vy cB wrex vx
      cA wreu wph vx cv cC wceq wi vy cB wral vx cA wreu vx vz cA wph vy cB
      crab vy vz cv cC csb reusv2lem5 vx cv vy vz cv cC csb wceq vz wph vy cB
      crab wrex wph vx cv cC wceq wa vy cB wrex vx cA vx cv vy vz cv cC csb
      wceq vz wph vy cB crab wrex vx cv cC wceq vy wph vy cB crab wrex wph vx
      cv cC wceq wa vy cB wrex vx cv cC wceq vx cv vy vz cv cC csb wceq vy vz
      wph vy cB crab wph vy cB nfrab1 vz wph vy cB crab nfcv vx cv cC wceq vz
      nfv vy vx cv vy vz cv cC csb vy vz cv cC nfcsb1v nfeq2 vy cv vz cv wceq
      cC vy vz cv cC csb vx cv vy vz cv cC csbeq1a eqeq2d cbvrexf vx cv cC wceq
      wph vx cv cC wceq wa vy wph vy cB crab cB vy cv wph vy cB crab wcel vx cv
      cC wceq wa vy cv cB wcel wph wa vx cv cC wceq wa vy cv cB wcel wph vx cv
      cC wceq wa wa vy cv wph vy cB crab wcel vy cv cB wcel wph wa vx cv cC
      wceq wph vy cB rabid anbi1i vy cv cB wcel wph vx cv cC wceq anass bitri
      rexbii2 bitr3i reubii vx cv vy vz cv cC csb wceq vz wph vy cB crab wral
      wph vx cv cC wceq wi vy cB wral vx cA vx cv vy vz cv cC csb wceq vz wph
      vy cB crab wral vx cv cC wceq vy wph vy cB crab wral wph vx cv cC wceq wi
      vy cB wral vx cv cC wceq vx cv vy vz cv cC csb wceq vy vz wph vy cB crab
      wph vy cB nfrab1 vz wph vy cB crab nfcv vx cv cC wceq vz nfv vy vx cv vy
      vz cv cC csb vy vz cv cC nfcsb1v nfeq2 vy cv vz cv wceq cC vy vz cv cC
      csb vx cv vy vz cv cC csbeq1a eqeq2d cbvralf vx cv cC wceq wph vx cv cC
      wceq wi vy wph vy cB crab cB vy cv wph vy cB crab wcel vx cv cC wceq wi
      vy cv cB wcel wph wa vx cv cC wceq wi vy cv cB wcel wph vx cv cC wceq wi
      wi vy cv wph vy cB crab wcel vy cv cB wcel wph wa vx cv cC wceq wph vy cB
      rabid imbi1i vy cv cB wcel wph vx cv cC wceq impexp bitri ralbii2 bitr3i
      reubii 3bitr3g syl2anbr $.
  $}

  ${
    $d x y z B $.  $d x z C $.  $d x y D $.  $d x z ph $.  $d x y ps $.
    reusv3.1 $e |- ( y = z -> ( ph <-> ps ) ) $.
    reusv3.2 $e |- ( y = z -> C = D ) $.
    $( Two ways of expressing existential uniqueness via an indirect equality.
       (Contributed by NM, 23-Dec-2012.) $)
    reusv3i $p |- ( E. x e. A A. y e. B ( ph -> x = C )
            -> A. y e. B A. z e. B ( ( ph /\ ps ) -> C = D ) ) $=
      wph vx cv cC wceq wi vy cB wral wph wps wa cC cD wceq wi vz cB wral vy cB
      wral vx cA wph vx cv cC wceq wi vy cB wral wps vx cv cD wceq wi vz cB
      wral wph wps wa cC cD wceq wi vz cB wral vy cB wral wph vx cv cC wceq wi
      vy cB wral wps vx cv cD wceq wi vz cB wral wph vx cv cC wceq wi wps vx cv
      cD wceq wi vy vz cB vy cv vz cv wceq wph wps vx cv cC wceq vx cv cD wceq
      reusv3.1 vy cv vz cv wceq cC cD vx cv reusv3.2 eqeq2d imbi12d cbvralv
      biimpi wph vx cv cC wceq wi vy cB wral wps vx cv cD wceq wi vz cB wral wa
      wph vx cv cC wceq wi wps vx cv cD wceq wi wa vz cB wral vy cB wral wph
      wps wa cC cD wceq wi vz cB wral vy cB wral wph vx cv cC wceq wi wps vx cv
      cD wceq wi vy vz cB raaanv wph vx cv cC wceq wi wps vx cv cD wceq wi wa
      vz cB wral wph wps wa cC cD wceq wi vz cB wral vy cB wph vx cv cC wceq wi
      wps vx cv cD wceq wi wa wph wps wa cC cD wceq wi vz cB wph vx cv cC wceq
      wi wps vx cv cD wceq wi wa wph wps wa vx cv cC wceq vx cv cD wceq wa cC
      cD wceq wph vx cv cC wceq wps vx cv cD wceq prth vx cv cC cD eqtr2 syl6
      ralimi ralimi sylbir mpdan rexlimivw $.

    $d x y z A $.
    $( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  See ~ reusv1 for the connection to uniqueness.
       (Contributed by NM, 27-Dec-2012.) $)
    reusv3 $p |- ( E. y e. B ( ph /\ C e. A )
          -> ( A. y e. B A. z e. B ( ( ph /\ ps ) -> C = D )
                   <-> E. x e. A A. y e. B ( ph -> x = C ) ) ) $=
      wph cC cA wcel wa vy cB wrex wph wps wa cC cD wceq wi vz cB wral vy cB
      wral wph vx cv cC wceq wi vy cB wral vx cA wrex wph cC cA wcel wa vy cB
      wrex wps cD cA wcel wa vz cB wrex wph wps wa cC cD wceq wi vz cB wral vy
      cB wral wph vx cv cC wceq wi vy cB wral vx cA wrex wi wph cC cA wcel wa
      wps cD cA wcel wa vy vz cB vy cv vz cv wceq wph wps cC cA wcel cD cA wcel
      reusv3.1 vy cv vz cv wceq cC cD cA reusv3.2 eleq1d anbi12d cbvrexv wps cD
      cA wcel wa wph wps wa cC cD wceq wi vz cB wral vy cB wral wph vx cv cC
      wceq wi vy cB wral vx cA wrex wi vz cB wph wps wa cC cD wceq wi vz cB
      wral vy cB wral wph vx cv cC wceq wi vy cB wral vx cA wrex vz wph wps wa
      cC cD wceq wi vy vz cB cB nfra2 wph vx cv cC wceq wi vy cB wral vx cA
      wrex vz nfv nfim vz cv cB wcel wps cD cA wcel wph wps wa cC cD wceq wi vz
      cB wral vy cB wral wph vx cv cC wceq wi vy cB wral vx cA wrex wi cD cA
      wcel vx cv cD wceq vx cA wrex vz cv cB wcel wps wa wph wps wa cC cD wceq
      wi vz cB wral vy cB wral wph vx cv cC wceq wi vy cB wral vx cA wrex wi vx
      cD cA risset vz cv cB wcel wps wa wph wps wa cC cD wceq wi vz cB wral vy
      cB wral vx cv cD wceq vx cA wrex wph vx cv cC wceq wi vy cB wral vx cA
      wrex vz cv cB wcel wps wa wph wps wa cC cD wceq wi vz cB wral vy cB wral
      vx cv cD wceq vx cA wrex wph vx cv cC wceq wi vy cB wral vx cA wrex wi vz
      cv cB wcel wps wa wph wps wa cC cD wceq wi vz cB wral vy cB wral wa vx cv
      cD wceq wph vx cv cC wceq wi vy cB wral vx cA vz cv cB wcel wps wa wph
      wps wa cC cD wceq wi vz cB wral vy cB wral wa wph vx cv cC wceq wi vy cB
      wral vx cv cD wceq wph cC cD wceq wi vy cB wral vz cv cB wcel wps wph wps
      wa cC cD wceq wi vz cB wral vy cB wral wph cC cD wceq wi vy cB wral wph
      wps wa cC cD wceq wi vz cB wral vy cB wral vz cv cB wcel wps wph cC cD
      wceq wi vy cB wral wph wps wa cC cD wceq wi vz cB wral vy cB wral wps wph
      cC cD wceq wi vy cB wral wi vz cB wral vz cv cB wcel wps wph cC cD wceq
      wi vy cB wral wi wi wph wps wa cC cD wceq wi vz cB wral vy cB wral wph
      wps wa cC cD wceq wi vy cB wral vz cB wral wps wph cC cD wceq wi vy cB
      wral wi vz cB wral wph wps wa cC cD wceq wi vy vz cB cB ralcom wph wps wa
      cC cD wceq wi vy cB wral wps wph cC cD wceq wi vy cB wral wi vz cB wph
      wps wa cC cD wceq wi vy cB wral wps wph cC cD wceq wi wi vy cB wral wps
      wph cC cD wceq wi vy cB wral wi wph wps wa cC cD wceq wi wps wph cC cD
      wceq wi wi vy cB wph wps wa cC cD wceq wi wph wps cC cD wceq wi wi wps
      wph cC cD wceq wi wi wph wps cC cD wceq impexp wph wps cC cD wceq bi2.04
      bitri ralbii wps wph cC cD wceq wi vy cB r19.21v bitri ralbii bitri wps
      wph cC cD wceq wi vy cB wral wi vz cB rsp sylbi com3l imp31 vx cv cD wceq
      wph vx cv cC wceq wi wph cC cD wceq wi vy cB vx cv cD wceq vx cv cC wceq
      cC cD wceq wph vx cv cD wceq vx cv cC wceq cD cC wceq cC cD wceq vx cv cD
      cC eqeq1 cD cC eqcom syl6bb imbi2d ralbidv syl5ibrcom reximdv ex com23
      syl5bi expimpd rexlimi sylbi wph wps vx vy vz cA cB cC cD reusv3.1
      reusv3.2 reusv3i impbid1 $.
  $}

  ${
    $d x y z A $.  $d x z B $.
    eusv4.1 $e |- B e. _V $.
    $( Two ways to express single-valuedness of a class expression
       ` B ( x ) ` .  (Contributed by NM, 27-Oct-2010.) $)
    eusv4 $p |- ( E! x E. y e. A x = B <-> E! x A. y e. A x = B ) $=
      cB cvv wcel vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA wral vx
      weu wb vy cA vx vy cA cB reusv2lem3 cB cvv wcel vy cv cA wcel eusv4.1 a1i
      mprg $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x C $.  $d x y $.
    $( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  (Contributed by NM, 16-Dec-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    reusv5OLD $p |- ( B =/= (/) -> ( E! x e. A A. y e. B x = C
                     <-> E. x e. A A. y e. B x = C ) ) $=
      cB c0 wne vy cv vy cv wceq vy cB wrex vx cv cC wceq vy cB wral vx cA wreu
      vx cv cC wceq vy cB wral vx cA wrex wb vy cv cB wcel vy wex vy cv cB wcel
      vy cv vy cv wceq wa vy wex cB c0 wne vy cv vy cv wceq vy cB wrex vy cv cB
      wcel vy cv cB wcel vy cv vy cv wceq wa vy vy cv vy cv wceq vy cv cB wcel
      vy equid biantru exbii vy cB n0 vy cv vy cv wceq vy cB df-rex 3bitr4i vy
      cv vy cv wceq vy cB wrex vy cv vy cv wceq vx cv cC wceq wi vy cB wral vx
      cA wreu vy cv vy cv wceq vx cv cC wceq wi vy cB wral vx cA wrex vx cv cC
      wceq vy cB wral vx cA wreu vx cv cC wceq vy cB wral vx cA wrex vy cv vy
      cv wceq vx vy cA cB cC reusv1 vx cv cC wceq vy cB wral vy cv vy cv wceq
      vx cv cC wceq wi vy cB wral vx cA vx cv cC wceq vy cv vy cv wceq vx cv cC
      wceq wi vy cB vy cv vy cv wceq vx cv cC wceq vy equid a1bi ralbii reubii
      vx cv cC wceq vy cB wral vy cv vy cv wceq vx cv cC wceq wi vy cB wral vx
      cA vx cv cC wceq vy cv vy cv wceq vx cv cC wceq wi vy cB vy cv vy cv wceq
      vx cv cC wceq vy equid a1bi ralbii rexbii 3bitr4g sylbi $.
  $}

  ${
    $d v w x y z A $.  $d v w x y z B $.  $d v w x z C $.
    $( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  The converse does not hold.  Note that ` U. A = |^| A `
       means ` A ` is a singleton ( ~ uniintsn ).  (Contributed by NM,
       30-Oct-2010.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    reusv6OLD $p |- ( ( U. A =/= |^| A \/ B =/= (/) )
          -> ( E! x e. A A. y e. B x = C -> E! x e. A E. y e. B x = C ) ) $=
      cA cuni cA cint wne vx cv cC wceq vy cB wral vx cA wreu vx cv cC wceq vy
      cB wrex vx cA wreu wi cB c0 wne cA cuni cA cint wne vx cv cC wceq vy cB
      wral vx cA wreu vx cv cC wceq vy cB wrex vx cA wreu wi wi cB c0 cB c0
      wceq cA cuni cA cint wne vx cv cC wceq vy cB wral vx cA wreu wn vx cv cC
      wceq vy cB wral vx cA wreu vx cv cC wceq vy cB wrex vx cA wreu wi cB c0
      wceq vx cv cC wceq vy cB wral vx cA wreu cA cuni cA cint cB c0 wceq vx cv
      cC wceq vy cB wral vx cA wreu vx cv cC wceq vy c0 wral vx cA wreu cA cuni
      cA cint wceq cB c0 wceq vx cv cC wceq vy cB wral vx cv cC wceq vy c0 wral
      vx cA vx cv cC wceq vy cB c0 raleq reubidv vx cv cC wceq vy c0 wral vx cA
      wreu vx cv cA wcel vx cv cC wceq vy c0 wral wa vx weu cA cuni cA cint
      wceq vx cv cC wceq vy c0 wral vx cA df-reu cA cuni cA cint wceq cA vx cv
      csn wceq vx wex vx cv cA wcel vx weu vx cv cA wcel vx cv cC wceq vy c0
      wral wa vx weu vx cA uniintsn vx cA eusn vx cv cA wcel vx cv cA wcel vx
      cv cC wceq vy c0 wral wa vx vx cv cC wceq vy c0 wral vx cv cA wcel vx cv
      cC wceq vy ral0 biantru eubii 3bitr2i bitr4i syl6bb necon3bbid vx cv cC
      wceq vy cB wral vx cA wreu vx cv cC wceq vy cB wrex vx cA wreu pm2.21
      syl6bir cB c0 wne vx cv cC wceq vy cB wral vx cA wreu vx cv cC wceq vy cB
      wrex vx cA wreu wi cA cuni cA cint wne cB c0 wne vx cv cC wceq vy cB wral
      vx cA crab vz cv csn wceq vz wex vx cv cC wceq vy cB wrex vx cA crab vz
      cv csn wceq vz wex vx cv cC wceq vy cB wral vx cA wreu vx cv cC wceq vy
      cB wrex vx cA wreu cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq vx cv cC wceq vy cB wrex vx cA crab vz cv csn wceq vz cB c0 wne
      vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cC wceq vy cB
      wrex vx cA crab vz cv csn wceq cB c0 wne vx cv cC wceq vy cB wral vx cA
      crab vz cv csn wceq wa vx cv cC wceq vy cB wrex vx cA crab vx cv cC wceq
      vy cB wral vx cA crab vz cv csn cB c0 wne vx cv cC wceq vy cB wral vx cA
      crab vz cv csn wceq wa vx cv cC wceq vy cB wrex vx cA crab vx cv cC wceq
      vy cB wral vx cA crab cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq wa vx cv cC wceq vy cB wrex vx cA crab vz cv csn vx cv cC wceq
      vy cB wral vx cA crab cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq wa vx cv cC wceq vy cB wrex vx cv vz cv csn wcel wi vx cA wral
      vx cv cC wceq vy cB wrex vx cA crab vz cv csn wss cB c0 wne vx cv cC wceq
      vy cB wral vx cA crab vz cv csn wceq wa vx cv cC wceq vy cB wrex vx cv vz
      cv csn wcel wi vx cA cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq vx cB c0 wne vx nfv vx vx cv cC wceq vy cB wral vx cA crab vz cv
      csn vx cv cC wceq vy cB wral vx cA nfrab1 nfeq1 nfan cB c0 wne vx cv cC
      wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel vx cv cC wceq vy
      cB wrex vx cv vz cv csn wcel wi cB c0 wne vx cv cC wceq vy cB wral vx cA
      crab vz cv csn wceq vx cv cA wcel w3a vx cv cC wceq vx cv vz cv csn wcel
      vy cB cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv
      cA wcel vy cB c0 wne vy nfv vy vx cv cC wceq vy cB wral vx cA crab vz cv
      csn vx cv cC wceq vy cB wral vy vx cA vx cv cC wceq vy cB nfra1 vy cA
      nfcv nfrab nfeq1 vx cv cA wcel vy nfv nf3an vx cv vz cv csn wcel vy nfv
      cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA
      wcel w3a vy cv cB wcel vx cv cC wceq vx cv vz cv csn wcel wi cB c0 wne vx
      cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vy cv
      cB wcel wa vx cv cC wceq vx cv vz cv wceq vx cv vz cv csn wcel cB c0 wne
      vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vy
      cv cB wcel wa vx cv vz cv wceq vx cv cC wceq cB c0 wne vx cv cC wceq vy
      cB wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vy cv cB wcel wa vz
      cv cC vx cv cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq
      vx cv cA wcel w3a vz cv cC wceq vy cB cB c0 wne vx cv cC wceq vy cB wral
      vx cA crab vz cv csn wceq vx cv cA wcel w3a vz cv vx cv cC wceq vy cB
      wral vx cA crab wcel vz cv cC wceq vy cB wral cB c0 wne vx cv cC wceq vy
      cB wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vz cv vz cv csn vx cv
      cC wceq vy cB wral vx cA crab vz cv vz vex snid cB c0 wne vx cv cC wceq
      vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel simp2 syl5eleqr vz cv
      vx cv cC wceq vy cB wral vx cA crab wcel vz cv cA wcel vz cv cC wceq vy
      cB wral vx cv cC wceq vy cB wral vz cv cC wceq vy cB wral vx vz cv cA vx
      cv vz cv wceq vx cv cC wceq vz cv cC wceq vy cB vx cv vz cv cC eqeq1
      ralbidv elrab simprbi syl r19.21bi eqeq2d biimprd vx vz cv elsn syl6ibr
      ex rexlimd 3expia ralrimi vx cv cC wceq vy cB wrex vx cA vz cv csn rabss
      sylibr cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq simpr
      sseqtr4d cB c0 wne vx cv cC wceq vy cB wral vx cA crab vx cv cC wceq vy
      cB wrex vx cA crab wss vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq
      cB c0 wne vx cv cC wceq vy cB wral vx cv cC wceq vy cB wrex vx cA cB c0
      wne vx cv cC wceq vy cB wral vx cv cC wceq vy cB wrex wi vx cv cA wcel cB
      c0 wne vx cv cC wceq vy cB wral vx cv cC wceq vy cB wrex vx cv cC wceq vy
      cB r19.2z ex adantr ss2rabdv adantr eqssd cB c0 wne vx cv cC wceq vy cB
      wral vx cA crab vz cv csn wceq simpr eqtrd ex eximdv vx cv cC wceq vy cB
      wral vx vz cA reusn vx cv cC wceq vy cB wrex vx vz cA reusn 3imtr4g a1d
      pm2.61ine cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vz
      wex vx cv cC wceq vy cB wrex vx cA crab vz cv csn wceq vz wex vx cv cC
      wceq vy cB wral vx cA wreu vx cv cC wceq vy cB wrex vx cA wreu cB c0 wne
      vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cC wceq vy cB
      wrex vx cA crab vz cv csn wceq vz cB c0 wne vx cv cC wceq vy cB wral vx
      cA crab vz cv csn wceq vx cv cC wceq vy cB wrex vx cA crab vz cv csn wceq
      cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq wa vx cv cC
      wceq vy cB wrex vx cA crab vx cv cC wceq vy cB wral vx cA crab vz cv csn
      cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq wa vx cv cC
      wceq vy cB wrex vx cA crab vx cv cC wceq vy cB wral vx cA crab cB c0 wne
      vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq wa vx cv cC wceq vy cB
      wrex vx cA crab vz cv csn vx cv cC wceq vy cB wral vx cA crab cB c0 wne
      vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq wa vx cv cC wceq vy cB
      wrex vx cv vz cv csn wcel wi vx cA wral vx cv cC wceq vy cB wrex vx cA
      crab vz cv csn wss cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq wa vx cv cC wceq vy cB wrex vx cv vz cv csn wcel wi vx cA cB c0
      wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cB c0 wne vx
      nfv vx vx cv cC wceq vy cB wral vx cA crab vz cv csn vx cv cC wceq vy cB
      wral vx cA nfrab1 nfeq1 nfan cB c0 wne vx cv cC wceq vy cB wral vx cA
      crab vz cv csn wceq vx cv cA wcel vx cv cC wceq vy cB wrex vx cv vz cv
      csn wcel wi cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq
      vx cv cA wcel w3a vx cv cC wceq vx cv vz cv csn wcel vy cB cB c0 wne vx
      cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel vy cB c0
      wne vy nfv vy vx cv cC wceq vy cB wral vx cA crab vz cv csn vx cv cC wceq
      vy cB wral vy vx cA vx cv cC wceq vy cB nfra1 vy cA nfcv nfrab nfeq1 vx
      cv cA wcel vy nfv nf3an vx cv vz cv csn wcel vy nfv cB c0 wne vx cv cC
      wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vy cv cB wcel
      vx cv cC wceq vx cv vz cv csn wcel wi cB c0 wne vx cv cC wceq vy cB wral
      vx cA crab vz cv csn wceq vx cv cA wcel w3a vy cv cB wcel wa vx cv cC
      wceq vx cv vz cv wceq vx cv vz cv csn wcel cB c0 wne vx cv cC wceq vy cB
      wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vy cv cB wcel wa vx cv
      vz cv wceq vx cv cC wceq cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz
      cv csn wceq vx cv cA wcel w3a vy cv cB wcel wa vz cv cC vx cv cB c0 wne
      vx cv cC wceq vy cB wral vx cA crab vz cv csn wceq vx cv cA wcel w3a vz
      cv cC wceq vy cB cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv csn
      wceq vx cv cA wcel w3a vz cv vx cv cC wceq vy cB wral vx cA crab wcel vz
      cv cC wceq vy cB wral cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq vx cv cA wcel w3a vz cv vz cv csn vx cv cC wceq vy cB wral vx cA
      crab vz cv vz vex snid cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz
      cv csn wceq vx cv cA wcel simp2 syl5eleqr vz cv vx cv cC wceq vy cB wral
      vx cA crab wcel vz cv cA wcel vz cv cC wceq vy cB wral vx cv cC wceq vy
      cB wral vz cv cC wceq vy cB wral vx vz cv cA vx cv vz cv wceq vx cv cC
      wceq vz cv cC wceq vy cB vx cv vz cv cC eqeq1 ralbidv elrab simprbi syl
      r19.21bi eqeq2d biimprd vx vz cv elsn syl6ibr ex rexlimd 3expia ralrimi
      vx cv cC wceq vy cB wrex vx cA vz cv csn rabss sylibr cB c0 wne vx cv cC
      wceq vy cB wral vx cA crab vz cv csn wceq simpr sseqtr4d cB c0 wne vx cv
      cC wceq vy cB wral vx cA crab vx cv cC wceq vy cB wrex vx cA crab wss vx
      cv cC wceq vy cB wral vx cA crab vz cv csn wceq cB c0 wne vx cv cC wceq
      vy cB wral vx cv cC wceq vy cB wrex vx cA cB c0 wne vx cv cC wceq vy cB
      wral vx cv cC wceq vy cB wrex wi vx cv cA wcel cB c0 wne vx cv cC wceq vy
      cB wral vx cv cC wceq vy cB wrex vx cv cC wceq vy cB r19.2z ex adantr
      ss2rabdv adantr eqssd cB c0 wne vx cv cC wceq vy cB wral vx cA crab vz cv
      csn wceq simpr eqtrd ex eximdv vx cv cC wceq vy cB wral vx vz cA reusn vx
      cv cC wceq vy cB wrex vx vz cA reusn 3imtr4g jaoi $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x C $.
    reusv7.1 $e |- ( y e. B -> C e. A ) $.
    $( Two ways to express single-valuedness of a class expression
       ` C ( y ) ` .  Note that ` U. A = |^| A ` means ` A ` is a singleton
       ( ~ uniintsn ).  (Contributed by NM, 14-Dec-2012.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    reusv7OLD $p |- ( ( U. A =/= |^| A \/ B =/= (/) )
          -> ( E! x e. A E. y e. B x = C <-> E! x e. A A. y e. B x = C ) ) $=
      cA cuni cA cint wne vx cv cC wceq vy cB wrex vx cA wreu vx cv cC wceq vy
      cB wral vx cA wreu wb cB c0 wne cA cuni cA cint wne vx cv cC wceq vy cB
      wrex vx cA wreu vx cv cC wceq vy cB wral vx cA wreu wb wi cB c0 cB c0
      wceq cA cuni cA cint wne vx cv cC wceq vy cB wrex vx cA wreu wn vx cv cC
      wceq vy cB wral vx cA wreu wn wa vx cv cC wceq vy cB wrex vx cA wreu vx
      cv cC wceq vy cB wral vx cA wreu wb cB c0 wceq cA cuni cA cint wne vx cv
      cC wceq vy cB wral vx cA wreu wn vx cv cC wceq vy cB wrex vx cA wreu wn
      cB c0 wceq vx cv cC wceq vy cB wral vx cA wreu wn cA cuni cA cint wne cB
      c0 wceq vx cv cC wceq vy cB wral vx cA wreu cA cuni cA cint cB c0 wceq vx
      cv cC wceq vy cB wral vx cA wreu vx cv cC wceq vy c0 wral vx cA wreu cA
      cuni cA cint wceq cB c0 wceq vx cv cC wceq vy cB wral vx cv cC wceq vy c0
      wral vx cA vx cv cC wceq vy cB c0 raleq reubidv vx cv cC wceq vy c0 wral
      vx cA wreu vx cv cA wcel vx cv cC wceq vy c0 wral wa vx weu cA cuni cA
      cint wceq vx cv cC wceq vy c0 wral vx cA df-reu cA cuni cA cint wceq cA
      vx cv csn wceq vx wex vx cv cA wcel vx weu vx cv cA wcel vx cv cC wceq vy
      c0 wral wa vx weu vx cA uniintsn vx cA eusn vx cv cA wcel vx cv cA wcel
      vx cv cC wceq vy c0 wral wa vx vx cv cC wceq vy c0 wral vx cv cA wcel vx
      cv cC wceq vy ral0 biantru eubii 3bitr2i bitr4i syl6bb necon3bbid biimprd
      vx cv cC wceq vy cB wrex vx cA wreu cB c0 vx cv cC wceq vy cB wrex vx cA
      wreu vx cv cC wceq vy cB wrex vx cA wrex cB c0 wne vx cv cC wceq vy cB
      wrex vx cA reurex vx cv cC wceq vy cB wrex cB c0 wne vx cA vx cv cC wceq
      vy cB rexn0 rexlimivw syl necon2bi jctild vx cv cC wceq vy cB wrex vx cA
      wreu vx cv cC wceq vy cB wral vx cA wreu pm5.21 syl6 cB c0 wne vx cv cC
      wceq vy cB wrex vx cA wreu vx cv cC wceq vy cB wral vx cA wreu wb cA cuni
      cA cint wne cB c0 wne vx cv cA wcel vx cv cC wceq wa vy cB wral vx weu vx
      cv cA wcel vx cv cC wceq vy cB wral wa vx weu vx cv cC wceq vy cB wrex vx
      cA wreu vx cv cC wceq vy cB wral vx cA wreu cB c0 wne vx cv cA wcel vx cv
      cC wceq wa vy cB wral vx cv cA wcel vx cv cC wceq vy cB wral wa vx vx cv
      cA wcel vx cv cC wceq vy cB r19.28zv eubidv vy cv vy cv wceq vx cv cC
      wceq wa vy cB wrex vx cA wreu cC cA wcel vy cv vy cv wceq wa vx cv cC
      wceq wi vy cB wral vx weu vx cv cC wceq vy cB wrex vx cA wreu vx cv cA
      wcel vx cv cC wceq wa vy cB wral vx weu vy cv vy cv wceq vx vy cA cB cC
      reusv2lem4 vx cv cC wceq vy cB wrex vy cv vy cv wceq vx cv cC wceq wa vy
      cB wrex vx cA vx cv cC wceq vy cv vy cv wceq vx cv cC wceq wa vy cB vy cv
      vy cv wceq vx cv cC wceq vy equid biantrur rexbii reubii vx cv cA wcel vx
      cv cC wceq wa vy cB wral cC cA wcel vy cv vy cv wceq wa vx cv cC wceq wi
      vy cB wral vx vx cv cA wcel vx cv cC wceq wa cC cA wcel vy cv vy cv wceq
      wa vx cv cC wceq wi vy cB vy cv cB wcel vx cv cA wcel vx cv cC wceq wa cC
      cA wcel vx cv cC wceq wi cC cA wcel vy cv vy cv wceq wa vx cv cC wceq wi
      vy cv cB wcel vx cv cA wcel vx cv cC wceq wa vx cv cC wceq cC cA wcel vx
      cv cC wceq wi vy cv cB wcel vx cv cC wceq cC cA wcel vx cv cC wceq wa vx
      cv cA wcel vx cv cC wceq wa vy cv cB wcel cC cA wcel vx cv cC wceq
      reusv7.1 biantrurd vx cv cC wceq vx cv cA wcel cC cA wcel vx cv cC cA
      eleq1 pm5.32ri syl6rbbr vy cv cB wcel cC cA wcel vx cv cC wceq cC cA wcel
      vx cv cC wceq wi wb reusv7.1 cC cA wcel vx cv cC wceq biimt syl bitrd cC
      cA wcel cC cA wcel vy cv vy cv wceq wa vx cv cC wceq vy cv vy cv wceq cC
      cA wcel vy equid biantru imbi1i syl6bb ralbiia eubii 3bitr4i vx cv cC
      wceq vy cB wral vx cA df-reu 3bitr4g a1d pm2.61ine cB c0 wne vx cv cA
      wcel vx cv cC wceq wa vy cB wral vx weu vx cv cA wcel vx cv cC wceq vy cB
      wral wa vx weu vx cv cC wceq vy cB wrex vx cA wreu vx cv cC wceq vy cB
      wral vx cA wreu cB c0 wne vx cv cA wcel vx cv cC wceq wa vy cB wral vx cv
      cA wcel vx cv cC wceq vy cB wral wa vx vx cv cA wcel vx cv cC wceq vy cB
      r19.28zv eubidv vy cv vy cv wceq vx cv cC wceq wa vy cB wrex vx cA wreu
      cC cA wcel vy cv vy cv wceq wa vx cv cC wceq wi vy cB wral vx weu vx cv
      cC wceq vy cB wrex vx cA wreu vx cv cA wcel vx cv cC wceq wa vy cB wral
      vx weu vy cv vy cv wceq vx vy cA cB cC reusv2lem4 vx cv cC wceq vy cB
      wrex vy cv vy cv wceq vx cv cC wceq wa vy cB wrex vx cA vx cv cC wceq vy
      cv vy cv wceq vx cv cC wceq wa vy cB vy cv vy cv wceq vx cv cC wceq vy
      equid biantrur rexbii reubii vx cv cA wcel vx cv cC wceq wa vy cB wral cC
      cA wcel vy cv vy cv wceq wa vx cv cC wceq wi vy cB wral vx vx cv cA wcel
      vx cv cC wceq wa cC cA wcel vy cv vy cv wceq wa vx cv cC wceq wi vy cB vy
      cv cB wcel vx cv cA wcel vx cv cC wceq wa cC cA wcel vx cv cC wceq wi cC
      cA wcel vy cv vy cv wceq wa vx cv cC wceq wi vy cv cB wcel vx cv cA wcel
      vx cv cC wceq wa vx cv cC wceq cC cA wcel vx cv cC wceq wi vy cv cB wcel
      vx cv cC wceq cC cA wcel vx cv cC wceq wa vx cv cA wcel vx cv cC wceq wa
      vy cv cB wcel cC cA wcel vx cv cC wceq reusv7.1 biantrurd vx cv cC wceq
      vx cv cA wcel cC cA wcel vx cv cC cA eleq1 pm5.32ri syl6rbbr vy cv cB
      wcel cC cA wcel vx cv cC wceq cC cA wcel vx cv cC wceq wi wb reusv7.1 cC
      cA wcel vx cv cC wceq biimt syl bitrd cC cA wcel cC cA wcel vy cv vy cv
      wceq wa vx cv cC wceq vy cv vy cv wceq cC cA wcel vy equid biantru imbi1i
      syl6bb ralbiia eubii 3bitr4i vx cv cC wceq vy cB wral vx cA df-reu
      3bitr4g jaoi $.
  $}

  ${
    $d x A $.  $d y ph $.  $d x ps $.  $d x y $.
    alxfr.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       18-Feb-2007.) $)
    alxfr $p |- ( ( A. y A e. B /\ A. x E. y x = A ) ->
                ( A. x ph <-> A. y ps ) ) $=
      cA cB wcel vy wal vx cv cA wceq vy wex vx wal wa wph vx wal wps vy wal cA
      cB wcel vy wal wph vx wal wps vy wal wi vx cv cA wceq vy wex vx wal wph
      vx wal cA cB wcel vy wal wps vy wal wph vx wal cA cB wcel wps vy cA cB
      wcel wph vx wal wps wph wps vx cA cB alxfr.1 spcgv com12 alimdv com12
      adantr vx cv cA wceq vy wex vx wal wps vy wal wph vx wal wi cA cB wcel vy
      wal wps vy wal vx cv cA wceq vy wex vx wal wph vx wal wps vy wal vx cv cA
      wceq vy wex wph vx wps vy wal vx cv cA wceq wph vy wps vy nfa1 wph vy nfv
      wps vy wal wph vx cv cA wceq wps wps vy sp alxfr.1 syl5ibrcom exlimd
      alimdv com12 adantl impbid $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x C $.  $d x ch $.  $d x y ph $.  $d y ps $.
    ralxfrd.1 $e |- ( ( ph /\ y e. C ) -> A e. B ) $.
    ralxfrd.2 $e |- ( ( ph /\ x e. B ) -> E. y e. C x = A ) $.
    ralxfrd.3 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       15-Aug-2014.)  (Proof shortened by Mario Carneiro, 19-Nov-2016.) $)
    ralxfrd $p |- ( ph -> ( A. x e. B ps <-> A. y e. C ch ) ) $=
      wph wps vx cB wral wch vy cC wral wph wps vx cB wral wch vy cC wph vy cv
      cC wcel wa wps wch vx cA cB ralxfrd.1 wph vx cv cA wceq wps wch wb vy cv
      cC wcel ralxfrd.3 adantlr rspcdv ralrimdva wph wch vy cC wral wps vx cB
      wph vx cv cB wcel wa wch vy cC wral vx cv cA wceq vy cC wrex wps
      ralxfrd.2 wch vy cC wral vx cv cA wceq vy cC wrex wa wch vx cv cA wceq wa
      vy cC wrex wph vx cv cB wcel wa wps wch vx cv cA wceq vy cC r19.29 wph vx
      cv cB wcel wa wch vx cv cA wceq wa wps vy cC wph wch vx cv cA wceq wa wps
      wi vx cv cB wcel vy cv cC wcel wph vx cv cA wceq wch wps wph vx cv cA
      wceq wch wps wph vx cv cA wceq wa wps wch ralxfrd.3 biimprd expimpd
      ancomsd ad2antrr rexlimdva syl5 mpan2d ralrimdva impbid $.

    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by FL,
       10-Apr-2007.)  (Revised by Mario Carneiro, 15-Aug-2014.) $)
    rexxfrd $p |- ( ph -> ( E. x e. B ps <-> E. y e. C ch ) ) $=
      wph wps wn vx cB wral wn wch wn vy cC wral wn wps vx cB wrex wch vy cC
      wrex wph wps wn vx cB wral wch wn vy cC wral wph wps wn wch wn vx vy cA
      cB cC ralxfrd.1 ralxfrd.2 wph vx cv cA wceq wa wps wch ralxfrd.3 notbid
      ralxfrd notbid wps vx cB dfrex2 wch vy cC dfrex2 3bitr4g $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x C $.  $d x ch $.  $d x y ph $.  $d y ps $.
    ralxfr2d.1 $e |- ( ( ph /\ y e. C ) -> A e. V ) $.
    ralxfr2d.2 $e |- ( ph -> ( x e. B <-> E. y e. C x = A ) ) $.
    ralxfr2d.3 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by Mario
       Carneiro, 20-Aug-2014.) $)
    ralxfr2d $p |- ( ph -> ( A. x e. B ps <-> A. y e. C ch ) ) $=
      wph wps wch vx vy cA cB cC wph vy cv cC wcel wa vx cv cA wceq vx wex cA
      cB wcel wph vy cv cC wcel wa cA cV wcel vx cv cA wceq vx wex ralxfr2d.1
      vx cA cV elisset syl wph vy cv cC wcel wa vx cv cA wceq cA cB wcel vx vx
      cv cA wceq vx cv cB wcel cA cB wcel wph vy cv cC wcel wa wph vx cv cA
      wceq vx cv cB wcel wi vy cC wph vx cv cA wceq vy cC wrex vx cv cB wcel wi
      vx cv cA wceq vx cv cB wcel wi vy cC wral wph vx cv cB wcel vx cv cA wceq
      vy cC wrex ralxfr2d.2 biimprd vx cv cA wceq vx cv cB wcel vy cC r19.23v
      sylibr r19.21bi vx cv cA cB eleq1 mpbidi exlimdv mpd wph vx cv cB wcel vx
      cv cA wceq vy cC wrex ralxfr2d.2 biimpa ralxfr2d.3 ralxfrd $.

    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by Mario
       Carneiro, 20-Aug-2014.)  (Proof shortened by Mario Carneiro,
       19-Nov-2016.) $)
    rexxfr2d $p |- ( ph -> ( E. x e. B ps <-> E. y e. C ch ) ) $=
      wph wps wn vx cB wral wn wch wn vy cC wral wn wps vx cB wrex wch vy cC
      wrex wph wps wn vx cB wral wch wn vy cC wral wph wps wn wch wn vx vy cA
      cB cC cV ralxfr2d.1 ralxfr2d.2 wph vx cv cA wceq wa wps wch ralxfr2d.3
      notbid ralxfr2d notbid wps vx cB dfrex2 wch vy cC dfrex2 3bitr4g $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x A $.  $d x y B $.  $d x C $.
    ralxfr.1 $e |- ( y e. C -> A e. B ) $.
    ralxfr.2 $e |- ( x e. B -> E. y e. C x = A ) $.
    ralxfr.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       10-Jun-2005.)  (Revised by Mario Carneiro, 15-Aug-2014.) $)
    ralxfr $p |- ( A. x e. B ph <-> A. y e. C ps ) $=
      wph vx cB wral wps vy cC wral wb wtru wph wps vx vy cA cB cC vy cv cC
      wcel cA cB wcel wtru ralxfr.1 adantl vx cv cB wcel vx cv cA wceq vy cC
      wrex wtru ralxfr.2 adantl vx cv cA wceq wph wps wb wtru ralxfr.3 adantl
      ralxfrd trud $.

    $( Transfer universal quantification from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  This proof does not use
       ~ ralxfrd .  (Contributed by NM, 10-Jun-2005.)  (Revised by Mario
       Carneiro, 15-Aug-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ralxfrALT $p |- ( A. x e. B ph <-> A. y e. C ps ) $=
      wph vx cB wral wps vy cC wral wph vx cB wral wps vy cC vy cv cC wcel wph
      vx cB wral wps vy cv cC wcel cA cB wcel wph vx cB wral wps wi ralxfr.1
      wph wps vx cA cB ralxfr.3 rspcv syl com12 ralrimiv wps vy cC wral wph vx
      cB vx cv cB wcel vx cv cA wceq vy cC wrex wps vy cC wral wph ralxfr.2 wps
      vy cC wral vx cv cA wceq wph vy cC wps vy cC nfra1 wph vy nfv wps vy cC
      wral vy cv cC wcel wps vx cv cA wceq wph wi wps vy cC rsp vx cv cA wceq
      wph wps ralxfr.3 biimprcd syl6 rexlimd syl5 ralrimiv impbii $.

    $( Transfer existence from a variable ` x ` to another variable ` y `
       contained in expression ` A ` .  (Contributed by NM, 10-Jun-2005.)
       (Revised by Mario Carneiro, 15-Aug-2014.) $)
    rexxfr $p |- ( E. x e. B ph <-> E. y e. C ps ) $=
      wph vx cB wrex wph wn vx cB wral wn wps vy cC wrex wph vx cB dfrex2 wps
      vy cC wrex wps wn vy cC wral wph wn vx cB wral wps vy cC dfrex2 wph wn
      wps wn vx vy cA cB cC ralxfr.1 ralxfr.2 vx cv cA wceq wph wps ralxfr.3
      notbid ralxfr xchbinxr bitr4i $.
  $}

  ${
    $d x A $.  $d x y D $.  $d y ph $.  $d y ps $.  $d x ch $.
    rabxfrd.1 $e |- F/_ y B $.
    rabxfrd.2 $e |- F/_ y C $.
    rabxfrd.3 $e |- ( ( ph /\ y e. D ) -> A e. D ) $.
    rabxfrd.4 $e |- ( x = A -> ( ps <-> ch ) ) $.
    rabxfrd.5 $e |- ( y = B -> A = C ) $.
    $( Class builder membership after substituting an expression ` A `
       (containing ` y ` ) for ` x ` in the class expression ` ch ` .
       (Contributed by NM, 16-Jan-2012.) $)
    rabxfrd $p |- ( ( ph /\ B e. D ) ->
                 ( C e. { x e. D | ps } <-> B e. { y e. D | ch } ) ) $=
      wph cB cD wcel cC wps vx cD crab wcel cB wch vy cD crab wcel wb wph cB cD
      wcel cC wps vx cD crab wcel wa cB cD wcel cB wch vy cD crab wcel wa wb cB
      cD wcel cC wps vx cD crab wcel cB wch vy cD crab wcel wb wi wph cB cA wps
      vx cD crab wcel vy cD crab wcel cB vy cv wch vy cD crab wcel vy cD crab
      wcel cB cD wcel cC wps vx cD crab wcel wa cB cD wcel cB wch vy cD crab
      wcel wa wph cA wps vx cD crab wcel vy cD crab vy cv wch vy cD crab wcel
      vy cD crab cB wph cA wps vx cD crab wcel vy cv wch vy cD crab wcel vy cD
      wph vy cv cD wcel wa cA cD wcel wch wa vy cv cD wcel wch wa cA wps vx cD
      crab wcel vy cv wch vy cD crab wcel wph vy cv cD wcel wa cA cD wcel vy cv
      cD wcel wch wph vy cv cD wcel cA cD wcel vy cv cD wcel wb wph vy cv cD
      wcel cA cD wcel wi vy cv cD wcel cA cD wcel vy cv cD wcel wb wi wph vy cv
      cD wcel cA cD wcel rabxfrd.3 ex vy cv cD wcel cA cD wcel ibibr sylib imp
      anbi1d wps wch vx cA cD rabxfrd.4 elrab wch vy cD rabid 3bitr4g rabbidva
      eleq2d cA wps vx cD crab wcel cC wps vx cD crab wcel vy cB cD rabxfrd.1
      vy cD nfcv vy cC wps vx cD crab rabxfrd.2 nfel1 vy cv cB wceq cA cC wps
      vx cD crab rabxfrd.5 eleq1d elrabf vy cv wch vy cD crab wcel cB wch vy cD
      crab wcel vy cB cD rabxfrd.1 vy cD nfcv vy cB wch vy cD crab rabxfrd.1
      wch vy cD nfrab1 nfel vy cv cB wch vy cD crab eleq1 elrabf 3bitr3g cB cD
      wcel cC wps vx cD crab wcel cB wch vy cD crab wcel pm5.32 sylibr imp $.
  $}

  ${
    $d x A $.  $d z B $.  $d z C $.  $d x y z D $.  $d y z ph $.  $d x z ps $.
    rabxfr.1 $e |- F/_ y B $.
    rabxfr.2 $e |- F/_ y C $.
    rabxfr.3 $e |- ( y e. D -> A e. D ) $.
    rabxfr.4 $e |- ( x = A -> ( ph <-> ps ) ) $.
    rabxfr.5 $e |- ( y = B -> A = C ) $.
    $( Class builder membership after substituting an expression ` A `
       (containing ` y ` ) for ` x ` in the class expression ` ph ` .
       (Contributed by NM, 10-Jun-2005.) $)
    rabxfr $p |- ( B e. D ->
                 ( C e. { x e. D | ph } <-> B e. { y e. D | ps } ) ) $=
      wtru cB cD wcel cC wph vx cD crab wcel cB wps vy cD crab wcel wb tru wtru
      wph wps vx vy cA cB cC cD rabxfr.1 rabxfr.2 vy cv cD wcel cA cD wcel wtru
      rabxfr.3 adantl rabxfr.4 rabxfr.5 rabxfrd mpan $.
  $}

  ${
    $d x y ph $.  $d x ps $.  $d x A $.  $d x y B $.
    reuxfr2d.1 $e |- ( ( ph /\ y e. B ) -> A e. B ) $.
    reuxfr2d.2 $e |- ( ( ph /\ x e. B ) -> E* y e. B x = A ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       16-Jan-2012.)  (Revised by NM, 16-Jun-2017.) $)
    reuxfr2d $p |- ( ph
        -> ( E! x e. B E. y e. B ( x = A /\ ps ) <-> E! y e. B ps ) ) $=
      wph vx cv cA wceq wps wa vy cB wrex vx cB wreu vx cv cA wceq wps wa vx cB
      wrex vy cB wreu wps vy cB wreu wph vx cv cA wceq wps wa vy cB wrex vx cB
      wreu vx cv cA wceq wps wa vx cB wrex vy cB wreu wph vx cv cA wceq wps wa
      vy cB wrmo vx cB wral vx cv cA wceq wps wa vy cB wrex vx cB wreu vx cv cA
      wceq wps wa vx cB wrex vy cB wreu wi wph vx cv cA wceq wps wa vy cB wrmo
      vx cB wph vx cv cB wcel wa wps vx cv cA wceq wa vy cB wrmo vx cv cA wceq
      wps wa vy cB wrmo wph vx cv cB wcel wa vx cv cA wceq vy cB wrmo wps vx cv
      cA wceq wa vy cB wrmo reuxfr2d.2 vx cv cA wceq wps vy cB rmoan syl wps vx
      cv cA wceq wa vx cv cA wceq wps wa vy cB wps vx cv cA wceq ancom rmobii
      sylib ralrimiva vx cv cA wceq wps wa vx vy cB cB 2reuswap syl vx cv cB
      wcel vx cv cA wceq wps wa wa vx wmo vx cv cA wceq wps wa vx cB wrex vy cB
      wreu vx cv cA wceq wps wa vy cB wrex vx cB wreu wi vy cB vx cv cB wcel vx
      cv cA wceq wps wa wa vx wmo vy cB wral vx cv cA wceq wps wa vx cB wrmo vy
      cB wral vx cv cA wceq wps wa vx cB wrex vy cB wreu vx cv cA wceq wps wa
      vy cB wrex vx cB wreu wi vx cv cA wceq wps wa vx cB wrmo vx cv cB wcel vx
      cv cA wceq wps wa wa vx wmo vy cB vx cv cA wceq wps wa vx cB df-rmo
      ralbii vx cv cA wceq wps wa vy vx cB cB 2reuswap sylbir vx cv cB wcel vx
      cv cA wceq wps wa wa vx wmo vy cv cB wcel vx cv cB wcel wps wa vx cv cA
      wceq wa vx wmo vx cv cB wcel vx cv cA wceq wps wa wa vx wmo vx cv cA wceq
      vx cv cB wcel wps wa vx vx cA moeq moani vx cv cB wcel wps wa vx cv cA
      wceq wa vx cv cB wcel vx cv cA wceq wps wa wa vx vx cv cB wcel wps wa vx
      cv cA wceq wa vx cv cA wceq vx cv cB wcel wps wa wa vx cv cB wcel vx cv
      cA wceq wps wa wa vx cv cB wcel wps wa vx cv cA wceq ancom vx cv cA wceq
      vx cv cB wcel wps an12 bitri mobii mpbi a1i mprg impbid1 wph vx cv cA
      wceq wps wa vx cB wrex wps vy cB wph vy cv cB wcel wa cA cB wcel vx cv cA
      wceq wps wa vx cB wrex wps wb reuxfr2d.1 wps wps vx cA cB vx cv cA wceq
      wps biidd ceqsrexv syl reubidva bitrd $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x y B $.
    reuxfr2.1 $e |- ( y e. B -> A e. B ) $.
    reuxfr2.2 $e |- ( x e. B -> E* y e. B x = A ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.)  (Revised by NM, 16-Jun-2017.) $)
    reuxfr2 $p |- ( E! x e. B E. y e. B ( x = A /\ ph ) <-> E! y e. B ph ) $=
      vx cv cA wceq wph wa vy cB wrex vx cB wreu wph vy cB wreu wb wtru wph vx
      vy cA cB vy cv cB wcel cA cB wcel wtru reuxfr2.1 adantl vx cv cB wcel vx
      cv cA wceq vy cB wrmo wtru reuxfr2.2 adantl reuxfr2d trud $.
  $}

  ${
    $d x y ph $.  $d y ps $.  $d x ch $.  $d x A $.  $d x y B $.
    reuxfrd.1 $e |- ( ( ph /\ y e. B ) -> A e. B ) $.
    reuxfrd.2 $e |- ( ( ph /\ x e. B ) -> E! y e. B x = A ) $.
    reuxfrd.3 $e |- ( x = A -> ( ps <-> ch ) ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Use ~ reuhypd to
       eliminate the second hypothesis.  (Contributed by NM, 16-Jan-2012.) $)
    reuxfrd $p |- ( ph -> ( E! x e. B ps <-> E! y e. B ch ) ) $=
      wph wps vx cB wreu vx cv cA wceq wch wa vy cB wrex vx cB wreu wch vy cB
      wreu wph wps vx cv cA wceq wch wa vy cB wrex vx cB wph vx cv cB wcel wa
      wps vx cv cA wceq vy cB wrex wps wa vx cv cA wceq wch wa vy cB wrex wph
      vx cv cB wcel wa vx cv cA wceq vy cB wrex wps wph vx cv cB wcel wa vx cv
      cA wceq vy cB wreu vx cv cA wceq vy cB wrex reuxfrd.2 vx cv cA wceq vy cB
      reurex syl biantrurd vx cv cA wceq vy cB wrex wps wa vx cv cA wceq wps wa
      vy cB wrex vx cv cA wceq wch wa vy cB wrex vx cv cA wceq wps vy cB
      r19.41v vx cv cA wceq wps wa vx cv cA wceq wch wa vy cB vx cv cA wceq wps
      wch reuxfrd.3 pm5.32i rexbii bitr3i syl6bb reubidva wph wch vx vy cA cB
      reuxfrd.1 wph vx cv cB wcel wa vx cv cA wceq vy cB wreu vx cv cA wceq vy
      cB wrmo reuxfrd.2 vx cv cA wceq vy cB reurmo syl reuxfr2d bitrd $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x A $.  $d x y B $.
    reuxfr.1 $e |- ( y e. B -> A e. B ) $.
    reuxfr.2 $e |- ( x e. B -> E! y e. B x = A ) $.
    reuxfr.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  Use ~ reuhyp to
       eliminate the second hypothesis.  (Contributed by NM, 14-Nov-2004.) $)
    reuxfr $p |- ( E! x e. B ph <-> E! y e. B ps ) $=
      wph vx cB wreu wps vy cB wreu wb wtru wph wps vx vy cA cB vy cv cB wcel
      cA cB wcel wtru reuxfr.1 adantl vx cv cB wcel vx cv cA wceq vy cB wreu
      wtru reuxfr.2 adantl reuxfr.3 reuxfrd trud $.
  $}

  ${
    $d y ph $.  $d y B $.  $d y C $.  $d x y $.
    reuhypd.1 $e |- ( ( ph /\ x e. C ) -> B e. C ) $.
    reuhypd.2 $e |- ( ( ph /\ x e. C /\ y e. C ) -> ( x = A <-> y = B ) ) $.
    $( A theorem useful for eliminating the restricted existential uniqueness
       hypotheses in ~ riotaxfrd .  (Contributed by NM, 16-Jan-2012.) $)
    reuhypd $p |- ( ( ph /\ x e. C ) -> E! y e. C x = A ) $=
      wph vx cv cC wcel wa vy cv cC wcel vx cv cA wceq wa vy weu vx cv cA wceq
      vy cC wreu wph vx cv cC wcel wa vy cv cB wceq vy weu vy cv cC wcel vx cv
      cA wceq wa vy weu wph vx cv cC wcel wa cB cvv wcel vy cv cB wceq vy weu
      wph vx cv cC wcel wa cB cC wcel cB cvv wcel reuhypd.1 cB cC elex syl vy
      cB eueq sylib wph vx cv cC wcel wa vy cv cB wceq vy cv cC wcel vx cv cA
      wceq wa vy wph vx cv cC wcel wa vy cv cB wceq vy cv cC wcel vy cv cB wceq
      wa vy cv cC wcel vx cv cA wceq wa wph vx cv cC wcel wa vy cv cB wceq vy
      cv cC wcel wph vx cv cC wcel wa vy cv cC wcel vy cv cB wceq cB cC wcel
      reuhypd.1 vy cv cB cC eleq1 syl5ibrcom pm4.71rd wph vx cv cC wcel wa vy
      cv cC wcel vx cv cA wceq vy cv cB wceq wph vx cv cC wcel vy cv cC wcel vx
      cv cA wceq vy cv cB wceq wb reuhypd.2 3expa pm5.32da bitr4d eubidv mpbid
      vx cv cA wceq vy cC df-reu sylibr $.
  $}

  ${
    $d y B $.  $d y C $.  $d x y $.
    reuhyp.1 $e |- ( x e. C -> B e. C ) $.
    reuhyp.2 $e |- ( ( x e. C /\ y e. C ) -> ( x = A <-> y = B ) ) $.
    $( A theorem useful for eliminating the restricted existential uniqueness
       hypotheses in ~ reuxfr .  (Contributed by NM, 15-Nov-2004.) $)
    reuhyp $p |- ( x e. C -> E! y e. C x = A ) $=
      wtru vx cv cC wcel vx cv cA wceq vy cC wreu tru wtru vx vy cA cB cC vx cv
      cC wcel cB cC wcel wtru reuhyp.1 adantl vx cv cC wcel vy cv cC wcel vx cv
      cA wceq vy cv cB wceq wb wtru reuhyp.2 3adant1 reuhypd mpan $.
  $}

  $( The Axiom of Union and its converse.  A class is a set iff its union is a
     set.  (Contributed by NM, 11-Nov-2003.) $)
  uniexb $p |- ( A e. _V <-> U. A e. _V ) $=
    cA cvv wcel cA cuni cvv wcel cA cvv uniexg cA cuni cvv wcel cA cA cuni cpw
    wss cA cuni cpw cvv wcel cA cvv wcel cA pwuni cA cuni cvv pwexg cA cA cuni
    cpw cvv ssexg sylancr impbii $.

  $( The Axiom of Power Sets and its converse.  A class is a set iff its power
     class is a set.  (Contributed by NM, 11-Nov-2003.) $)
  pwexb $p |- ( A e. _V <-> ~P A e. _V ) $=
    cA cpw cvv wcel cA cpw cuni cvv wcel cA cvv wcel cA cpw uniexb cA cpw cuni
    cA cvv cA unipw eleq1i bitr2i $.

  $( The union of the universe is the universe.  Exercise 4.12(c) of
     [Mendelson] p. 235.  (Contributed by NM, 14-Sep-2003.) $)
  univ $p |- U. _V = _V $=
    cvv cpw cuni cvv cuni cvv cvv cpw cvv pwv unieqi cvv unipw eqtr3i $.

  ${
    eldifpw.1 $e |- C e. _V $.
    $( Membership in a power class difference.  (Contributed by NM,
       25-Mar-2007.) $)
    eldifpw $p |- ( ( A e. ~P B /\ -. C C_ B ) ->
                   ( A u. C ) e. ( ~P ( B u. C ) \ ~P B ) ) $=
      cA cB cpw wcel cC cB wss wn wa cA cC cun cB cC cun cpw wcel cA cC cun cB
      cpw wcel wn wa cA cC cun cB cC cun cpw cB cpw cdif wcel cA cB cpw wcel cA
      cC cun cB cC cun cpw wcel cC cB wss wn cA cC cun cB cpw wcel wn cA cB cpw
      wcel cA cB wss cA cC cun cB cC cun cpw wcel cA cB elpwi cA cB wss cA cC
      cun cB cC cun cpw wcel cA cB cpw wcel cA cC cun cB cC cun wss cA cB cC
      unss1 cA cB cpw wcel cA cC cun cvv wcel cA cC cun cB cC cun cpw wcel cA
      cC cun cB cC cun wss wb cA cB cpw wcel cC cvv wcel cA cC cun cvv wcel
      eldifpw.1 cA cC cB cpw cvv unexg mpan2 cA cC cun cB cC cun cvv elpwg syl
      syl5ibr mpd cA cC cun cB cpw wcel cC cB wss cA cC cun cB cpw wcel cA cC
      cun cB wss cC cB wss cA cC cun cB elpwi cA cC cun cB wss cA cB wss cC cB
      wss wa cC cB wss cA cC cB unss cA cB wss cC cB wss simpr sylbir syl con3i
      anim12i cA cC cun cB cC cun cpw cB cpw eldif sylibr $.

    $( Membership in the power class of a union.  (Contributed by NM,
       26-Mar-2007.) $)
    elpwun $p |- ( A e. ~P ( B u. C ) <-> ( A \ C ) e. ~P B ) $=
      cA cB cC cun cpw wcel cA cvv wcel cA cC cdif cB cpw wcel cA cB cC cun cpw
      elex cA cC cdif cB cpw wcel cA cC cdif cvv wcel cA cvv wcel cA cC cdif cB
      cpw elex cC cvv wcel cA cvv wcel cA cC cdif cvv wcel wb eldifpw.1 cA cC
      cvv difex2 ax-mp sylibr cA cvv wcel cA cB cC cun cpw wcel cA cB cC cun
      wss cA cC cdif cB cpw wcel cA cB cC cun cvv elpwg cA cvv wcel cA cC cdif
      cB cpw wcel cA cC cdif cB wss cA cB cC cun wss cA cvv wcel cA cC cdif cvv
      wcel cA cC cdif cB cpw wcel cA cC cdif cB wss wb cA cC cvv difexg cA cC
      cdif cB cvv elpwg syl cA cB cC cun wss cA cC cB cun wss cA cC cdif cB wss
      cB cC cun cC cB cun cA cB cC uncom sseq2i cA cC cB ssundif bitri syl6rbbr
      bitrd pm5.21nii $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Membership in an extension of a power class.  (Contributed by NM,
       26-Mar-2007.) $)
    elpwunsn $p |- ( A e. ( ~P ( B u. { C } ) \ ~P B ) -> C e. A ) $=
      cA cB cC csn cun cpw cB cpw cdif wcel cA cB cC csn cun cpw wcel cA cB cpw
      wcel wn wa cC cA wcel cA cB cC csn cun cpw cB cpw eldif cA cB cC csn cun
      cpw wcel cA cB cpw wcel wn vx cv cB wcel wn vx cA wrex cC cA wcel cA cB
      cC csn cun cpw wcel cA cB cpw wcel wn wa vx cv cB wcel vx cA wral wn vx
      cv cB wcel wn vx cA wrex cA cB cC csn cun cpw wcel cA cB cpw wcel wn vx
      cv cB wcel vx cA wral wn cA cB cC csn cun cpw wcel cA cB cpw wcel vx cv
      cB wcel vx cA wral cA cB cC csn cun cpw wcel cA cB cpw wcel cA cB wss vx
      cv cB wcel vx cA wral cA cB cB cC csn cun cpw elpwg vx cA cB dfss3 syl6bb
      notbid biimpa vx cv cB wcel vx cA rexnal sylibr cA cB cC csn cun cpw wcel
      vx cv cB wcel wn vx cA wrex cC cA wcel cA cB cC csn cun cpw wcel vx cv cB
      wcel wn cC cA wcel vx cA cA cB cC csn cun cpw wcel vx cv cA wcel vx cv cB
      wcel wn cC cA wcel wi cA cB cC csn cun cpw wcel vx cv cA wcel vx cv cB
      wcel wn vx cv cA wcel cC cA wcel cA cB cC csn cun cpw wcel vx cv cA wcel
      vx cv cB wcel wn vx cv cA wcel cC cA wcel wi cA cB cC csn cun cpw wcel vx
      cv cA wcel vx cv cB wcel wn wa vx cv cC wceq vx cv cA wcel cC cA wcel wi
      cA cB cC csn cun cpw wcel cA cB cC csn cun wss vx cv cA wcel vx cv cB cC
      csn cun wcel wi vx cv cA wcel vx cv cB wcel wn wa vx cv cC wceq wi cA cB
      cC csn cun elpwi cA cB cC csn cun vx cv ssel vx cv cA wcel vx cv cB cC
      csn cun wcel wi vx cv cA wcel vx cv cB wcel wn vx cv cC wceq vx cv cB cC
      csn cun wcel vx cv cB wcel wn vx cv cC wceq wi vx cv cA wcel vx cv cB cC
      csn cun wcel vx cv cB wcel vx cv cC csn wcel wo vx cv cB wcel wn vx cv cC
      wceq wi vx cv cB cC csn elun vx cv cB wcel vx cv cC csn wcel wo vx cv cB
      wcel vx cv cC wceq vx cv cC csn wcel vx cv cC wceq vx cv cB wcel vx cv cC
      elsni orim2i ord sylbi imim2i imp3a 3syl vx cv cC wceq vx cv cA wcel cC
      cA wcel vx cv cC cA eleq1 biimpd syl6 exp3a com4r pm2.43b rexlimdv imp
      syldan sylbi $.
  $}

  ${
    op1stb.1 $e |- A e. _V $.
    op1stb.2 $e |- B e. _V $.
    $( Extract the first member of an ordered pair.  Theorem 73 of [Suppes]
       p. 42.  (See ~ op2ndb to extract the second member, ~ op1sta for an
       alternate version, and ~ op1st for the preferred version.)  (Contributed
       by NM, 25-Nov-2003.) $)
    op1stb $p |- |^| |^| <. A , B >. = A $=
      cA cB cop cint cint cA csn cint cA cA cB cop cint cA csn cA cB cop cint
      cA csn cA cB cpr cpr cint cA csn cA cB cop cA csn cA cB cpr cpr cA cB
      op1stb.1 op1stb.2 dfop inteqi cA csn cA cB cpr cpr cint cA csn cA cB cpr
      cin cA csn cA csn cA cB cpr cA snex cA cB prex intpr cA csn cA cB cpr wss
      cA csn cA cB cpr cin cA csn wceq cA cB snsspr1 cA csn cA cB cpr df-ss
      mpbi eqtri eqtri inteqi cA op1stb.1 intsn eqtri $.
  $}

  ${
    $d x y A $.
    iunpw.1 $e |- A e. _V $.
    $( An indexed union of a power class in terms of the power class of the
       union of its index.  Part of Exercise 24(b) of [Enderton] p. 33.
       (Contributed by NM, 29-Nov-2003.) $)
    iunpw $p |- ( E. x e. A x = U. A <-> ~P U. A = U_ x e. A ~P x ) $=
      vx cv cA cuni wceq vx cA wrex cA cuni cpw vx cA vx cv cpw ciun wceq vx cv
      cA cuni wceq vx cA wrex vy cA cuni cpw vx cA vx cv cpw ciun vx cv cA cuni
      wceq vx cA wrex vy cv cA cuni wss vy cv vx cv wss vx cA wrex vy cv cA
      cuni cpw wcel vy cv vx cA vx cv cpw ciun wcel vx cv cA cuni wceq vx cA
      wrex vy cv cA cuni wss vy cv vx cv wss vx cA wrex vy cv cA cuni wss vx cv
      cA cuni wceq vx cA wrex vy cv vx cv wss vx cA wrex vy cv cA cuni wss vx
      cv cA cuni wceq vy cv vx cv wss vx cA vx cv cA cuni wceq vy cv vx cv wss
      vy cv cA cuni wss vx cv cA cuni vy cv sseq2 biimprcd reximdv com12 vy cv
      vx cv wss vx cA wrex vy cv vx cA vx cv ciun cA cuni vx cA vx cv vy cv
      ssiun vx cA uniiun syl6sseqr impbid1 vy cv cA cuni vy vex elpw vy cv vx
      cA vx cv cpw ciun wcel vy cv vx cv cpw wcel vx cA wrex vy cv vx cv wss vx
      cA wrex vx vy cv cA vx cv cpw eliun vy cv vx cv cpw wcel vy cv vx cv wss
      vx cA vy cv vx cv wss vy vx cv cpw vy vx cv df-pw abeq2i rexbii bitri
      3bitr4g eqrdv cA cuni cpw vx cA vx cv cpw ciun wceq cA cuni vx cv cpw
      wcel vx cA wrex vx cv cA cuni wceq vx cA wrex cA cuni cpw vx cA vx cv cpw
      ciun wceq cA cuni vx cA vx cv cpw ciun wcel cA cuni vx cv cpw wcel vx cA
      wrex cA cuni cpw vx cA vx cv cpw ciun wceq cA cuni cA cuni wss cA cuni vx
      cA vx cv cpw ciun wcel cA cuni ssid cA cuni cA cuni wss cA cuni cA cuni
      cpw wcel cA cuni cpw vx cA vx cv cpw ciun wceq cA cuni vx cA vx cv cpw
      ciun wcel cA cuni cA cuni cA iunpw.1 uniex elpw cA cuni cpw vx cA vx cv
      cpw ciun cA cuni eleq2 syl5bbr mpbii vx cA cuni cA vx cv cpw eliun sylib
      cA cuni vx cv cpw wcel vx cv cA cuni wceq vx cA vx cv cA wcel cA cuni vx
      cv cpw wcel vx cv cA cuni wceq vx cv cA wcel cA cuni vx cv cpw wcel wa vx
      cv cA cuni wss cA cuni vx cv wss wa vx cv cA cuni wceq vx cv cA wcel vx
      cv cA cuni wss cA cuni vx cv cpw wcel cA cuni vx cv wss vx cv cA elssuni
      cA cuni vx cv elpwi anim12i vx cv cA cuni eqss sylibr ex reximia syl
      impbii $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y R $.
    $( A well-founded relation has no 3-cycle loops.  Special case of
       Proposition 6.23 of [TakeutiZaring] p. 30.  (Contributed by NM,
       10-Apr-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)
    fr3nr $p |- ( ( R Fr A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
                -. ( B R C /\ C R D /\ D R B ) ) $=
      cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cD cB cR wbr cB cC cR
      wbr cC cD cR wbr w3a cB cC cR wbr cC cD cR wbr cD cB cR wbr w3a cA cR wfr
      cB cA wcel cC cA wcel cD cA wcel w3a wa cD cB cR wbr wn cB cC cR wbr wn
      cC cD cR wbr wn w3o cD cB cR wbr cB cC cR wbr cC cD cR wbr w3a wn cA cR
      wfr cB cA wcel cC cA wcel cD cA wcel w3a wa vy cv cB cR wbr wn vy cB cC
      cD ctp wral vy cv cC cR wbr wn vy cB cC cD ctp wral vy cv cD cR wbr wn vy
      cB cC cD ctp wral w3o cD cB cR wbr wn cB cC cR wbr wn cC cD cR wbr wn w3o
      cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa vy cv vx cv cR wbr wn
      vy cB cC cD ctp wral vx cB cC cD ctp wrex vy cv cB cR wbr wn vy cB cC cD
      ctp wral vy cv cC cR wbr wn vy cB cC cD ctp wral vy cv cD cR wbr wn vy cB
      cC cD ctp wral w3o cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB
      cC cD ctp cvv wcel cA cR wfr cB cC cD ctp cA wss cB cC cD ctp c0 wne vy
      cv vx cv cR wbr wn vy cB cC cD ctp wral vx cB cC cD ctp wrex cB cC cD ctp
      cvv wcel cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB cC cD tpex
      a1i cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a simpl cA cR wfr cB cA
      wcel cC cA wcel cD cA wcel w3a wa cB cC cD ctp cB cC cpr cD csn cun cA cB
      cC cD df-tp cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB cC cpr
      cD csn cA cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB cA wcel cC
      cA wcel cB cC cpr cA wss cA cR wfr cB cA wcel cC cA wcel cD cA wcel
      simpr1 cA cR wfr cB cA wcel cC cA wcel cD cA wcel simpr2 cB cC cA prssi
      syl2anc cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cD cA cA cR wfr
      cB cA wcel cC cA wcel cD cA wcel simpr3 snssd unssd syl5eqss cA cR wfr cB
      cA wcel cC cA wcel cD cA wcel w3a wa cB cB cC cD ctp wcel cB cC cD ctp c0
      wne cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB cB cC cD ctp
      wcel cB csn cB cC cD ctp wss cB cC cD snsstp1 cA cR wfr cB cA wcel cC cA
      wcel cD cA wcel w3a wa cB cA wcel cB cB cC cD ctp wcel cB csn cB cC cD
      ctp wss wb cA cR wfr cB cA wcel cC cA wcel cD cA wcel simpr1 cB cB cC cD
      ctp cA snssg syl mpbiri cB cC cD ctp cB ne0i syl vx vy cA cB cC cD ctp
      cvv cR fri syl22anc cB cA wcel cC cA wcel cD cA wcel w3a vy cv vx cv cR
      wbr wn vy cB cC cD ctp wral vx cB cC cD ctp wrex vy cv cB cR wbr wn vy cB
      cC cD ctp wral vy cv cC cR wbr wn vy cB cC cD ctp wral vy cv cD cR wbr wn
      vy cB cC cD ctp wral w3o wb cA cR wfr vy cv vx cv cR wbr wn vy cB cC cD
      ctp wral vy cv cB cR wbr wn vy cB cC cD ctp wral vy cv cC cR wbr wn vy cB
      cC cD ctp wral vy cv cD cR wbr wn vy cB cC cD ctp wral vx cB cC cD cA cA
      cA vx cv cB wceq vy cv vx cv cR wbr wn vy cv cB cR wbr wn vy cB cC cD ctp
      vx cv cB wceq vy cv vx cv cR wbr vy cv cB cR wbr vx cv cB vy cv cR breq2
      notbid ralbidv vx cv cC wceq vy cv vx cv cR wbr wn vy cv cC cR wbr wn vy
      cB cC cD ctp vx cv cC wceq vy cv vx cv cR wbr vy cv cC cR wbr vx cv cC vy
      cv cR breq2 notbid ralbidv vx cv cD wceq vy cv vx cv cR wbr wn vy cv cD
      cR wbr wn vy cB cC cD ctp vx cv cD wceq vy cv vx cv cR wbr vy cv cD cR
      wbr vx cv cD vy cv cR breq2 notbid ralbidv rextpg adantl mpbid cA cR wfr
      cB cA wcel cC cA wcel cD cA wcel w3a wa vy cv cB cR wbr wn vy cB cC cD
      ctp wral cD cB cR wbr wn vy cv cC cR wbr wn vy cB cC cD ctp wral cB cC cR
      wbr wn vy cv cD cR wbr wn vy cB cC cD ctp wral cC cD cR wbr wn cA cR wfr
      cB cA wcel cC cA wcel cD cA wcel w3a wa cD cB cC cD ctp wcel vy cv cB cR
      wbr wn vy cB cC cD ctp wral cD cB cR wbr wn wi cA cR wfr cB cA wcel cC cA
      wcel cD cA wcel w3a wa cD cB cC cD ctp wcel cD csn cB cC cD ctp wss cB cC
      cD snsstp3 cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cD cA wcel
      cD cB cC cD ctp wcel cD csn cB cC cD ctp wss wb cA cR wfr cB cA wcel cC
      cA wcel cD cA wcel simpr3 cD cB cC cD ctp cA snssg syl mpbiri vy cv cB cR
      wbr wn cD cB cR wbr wn vy cD cB cC cD ctp vy cv cD wceq vy cv cB cR wbr
      cD cB cR wbr vy cv cD cB cR breq1 notbid rspcv syl cA cR wfr cB cA wcel
      cC cA wcel cD cA wcel w3a wa cB cB cC cD ctp wcel vy cv cC cR wbr wn vy
      cB cC cD ctp wral cB cC cR wbr wn wi cA cR wfr cB cA wcel cC cA wcel cD
      cA wcel w3a wa cB cB cC cD ctp wcel cB csn cB cC cD ctp wss cB cC cD
      snsstp1 cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB cA wcel cB
      cB cC cD ctp wcel cB csn cB cC cD ctp wss wb cA cR wfr cB cA wcel cC cA
      wcel cD cA wcel simpr1 cB cB cC cD ctp cA snssg syl mpbiri vy cv cC cR
      wbr wn cB cC cR wbr wn vy cB cB cC cD ctp vy cv cB wceq vy cv cC cR wbr
      cB cC cR wbr vy cv cB cC cR breq1 notbid rspcv syl cA cR wfr cB cA wcel
      cC cA wcel cD cA wcel w3a wa cC cB cC cD ctp wcel vy cv cD cR wbr wn vy
      cB cC cD ctp wral cC cD cR wbr wn wi cA cR wfr cB cA wcel cC cA wcel cD
      cA wcel w3a wa cC cB cC cD ctp wcel cC csn cB cC cD ctp wss cB cC cD
      snsstp2 cA cR wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cC cA wcel cC
      cB cC cD ctp wcel cC csn cB cC cD ctp wss wb cA cR wfr cB cA wcel cC cA
      wcel cD cA wcel simpr2 cC cB cC cD ctp cA snssg syl mpbiri vy cv cD cR
      wbr wn cC cD cR wbr wn vy cC cB cC cD ctp vy cv cC wceq vy cv cD cR wbr
      cC cD cR wbr vy cv cC cD cR breq1 notbid rspcv syl 3orim123d mpd cD cB cR
      wbr cB cC cR wbr cC cD cR wbr 3ianor sylibr cD cB cR wbr cB cC cR wbr cC
      cD cR wbr 3anrot sylnib $.
  $}

  $( A set well-founded by epsilon contains no 3-cycle loops.  (Contributed by
     NM, 19-Apr-1994.)  (Revised by Mario Carneiro, 22-Jun-2015.) $)
  epne3 $p |- ( ( _E Fr A /\ ( B e. A /\ C e. A /\ D e. A ) ) ->
                -. ( B e. C /\ C e. D /\ D e. B ) ) $=
    cA cep wfr cB cA wcel cC cA wcel cD cA wcel w3a wa cB cC cep wbr cC cD cep
    wbr cD cB cep wbr w3a cB cC wcel cC cD wcel cD cB wcel w3a cA cB cC cD cep
    fr3nr cB cA wcel cC cA wcel cD cA wcel w3a cB cC cep wbr cC cD cep wbr cD
    cB cep wbr w3a cB cC wcel cC cD wcel cD cB wcel w3a wb cA cep wfr cB cA
    wcel cC cA wcel cD cA wcel w3a cB cC cep wbr cB cC wcel cC cD cep wbr cC cD
    wcel cD cB cep wbr cD cB wcel cC cA wcel cB cA wcel cB cC cep wbr cB cC
    wcel wb cD cA wcel cB cC cA epelg 3ad2ant2 cD cA wcel cB cA wcel cC cD cep
    wbr cC cD wcel wb cC cA wcel cC cD cA epelg 3ad2ant3 cB cA wcel cC cA wcel
    cD cB cep wbr cD cB wcel wb cD cA wcel cD cB cA epelg 3ad2ant1 3anbi123d
    adantl mtbid $.

  ${
    $d x y z R $.  $d x y z A $.
    $( Alternate definition of well-ordering.  Definition 6.24(2) of
       [TakeutiZaring] p. 30.  (Contributed by NM, 16-Mar-1997.)  (Proof
       shortened by Andrew Salmon, 12-Aug-2011.) $)
    dfwe2 $p |- ( R We A <-> ( R Fr A /\ A. x e. A A. y e. A
                ( x R y \/ x = y \/ y R x ) ) ) $=
      cA cR wwe cA cR wfr cA cR wor wa cA cR wfr vx cv vy cv cR wbr vx cv vy cv
      wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral wa cA cR df-we cA cR
      wfr cA cR wor vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o
      vy cA wral vx cA wral cA cR wor cA cR wpo vx cv vy cv cR wbr vx cv vy cv
      wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral wa cA cR wfr vx cv vy
      cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral
      vx vy cA cR df-so cA cR wfr cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq
      vy cv vx cv cR wbr w3o vy cA wral vx cA wral wa vx cv vy cv cR wbr vx cv
      vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral cA cR wpo vx cv
      vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cA
      wral simpr cA cR wfr vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR
      wbr w3o vy cA wral vx cA wral cA cR wpo cA cR wfr vx cv vz cv cR wbr vx
      cv vz cv wceq vz cv vx cv cR wbr w3o vz cA wral vy cA wral vx cA wral vx
      cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv
      cR wbr wi wa vz cA wral vy cA wral vx cA wral vx cv vy cv cR wbr vx cv vy
      cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cA wral cA cR wpo cA cR wfr
      vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a vx cv vz cv cR wbr vx cv vz
      cv wceq vz cv vx cv cR wbr w3o wi vz wal vy wal vx wal vx cv cA wcel vy
      cv cA wcel vz cv cA wcel w3a vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy
      cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa wi vz wal vy wal vx wal vx cv
      vz cv cR wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vz cA wral vy cA
      wral vx cA wral vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi wa vz cA wral vy cA wral vx cA wral cA cR
      wfr vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a vx cv vz cv cR wbr vx
      cv vz cv wceq vz cv vx cv cR wbr w3o wi vz wal vx cv cA wcel vy cv cA
      wcel vz cv cA wcel w3a vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz
      cv cR wbr wa vx cv vz cv cR wbr wi wa wi vz wal vx vy cA cR wfr vx cv cA
      wcel vy cv cA wcel vz cv cA wcel w3a vx cv vz cv cR wbr vx cv vz cv wceq
      vz cv vx cv cR wbr w3o wi vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa wi vz cA cR wfr vx cv cA wcel vy cv cA wcel vz cv cA wcel
      w3a vx cv vz cv cR wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vx cv vx
      cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi wa cA cR wfr vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a vx cv vz cv
      cR wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vx cv vx cv cR wbr wn vx
      cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa wi cA cR
      wfr vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a wa vx cv vz cv cR wbr
      vx cv vz cv wceq vz cv vx cv cR wbr w3o vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi vx cv vx cv cR wbr wn cA cR wfr vx cv cA
      wcel vy cv cA wcel vz cv cA wcel w3a wa vx cv vz cv cR wbr vx cv vy cv cR
      wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vx cv vz cv wceq vz cv vx
      cv cR wbr vx cv vz cv cR wbr vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx
      cv vz cv cR wbr wi wi cA cR wfr vx cv cA wcel vy cv cA wcel vz cv cA wcel
      w3a wa vx cv vz cv cR wbr vx cv vy cv cR wbr vy cv vz cv cR wbr wa ax-1
      a1i cA cR wfr vx cv cA wcel vy cv cA wcel vz cv cA wcel w3a wa vx cv vz
      cv wceq vx cv vy cv cR wbr vy cv vz cv cR wbr wa wn vx cv vy cv cR wbr vy
      cv vz cv cR wbr wa vx cv vz cv cR wbr wi cA cR wfr vx cv cA wcel vy cv cA
      wcel vz cv cA wcel w3a wa vx cv vy cv cR wbr vy cv vx cv cR wbr wa wn vx
      cv vz cv wceq vx cv vy cv cR wbr vy cv vz cv cR wbr wa wn cA cR wfr vx cv
      cA wcel vy cv cA wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa wn vz cv
      cA wcel cA vx cv vy cv cR fr2nr 3adantr3 vx cv vz cv wceq vx cv vy cv cR
      wbr vy cv vx cv cR wbr wa vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv
      vz cv wceq vy cv vx cv cR wbr vy cv vz cv cR wbr vx cv vy cv cR wbr vx cv
      vz cv vy cv cR breq2 anbi2d notbid syl5ibcom vx cv vy cv cR wbr vy cv vz
      cv cR wbr wa vx cv vz cv cR wbr pm2.21 syl6 cA cR wfr vx cv cA wcel vy cv
      cA wcel vz cv cA wcel w3a wa vz cv vx cv cR wbr vx cv vy cv cR wbr vy cv
      vz cv cR wbr wa vx cv vz cv cR wbr cA cR wfr vx cv cA wcel vy cv cA wcel
      vz cv cA wcel w3a wa vz cv vx cv cR wbr vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa wa vx cv vz cv cR wbr cA cR wfr vx cv cA wcel vy cv cA wcel vz cv
      cA wcel w3a wa vx cv vy cv cR wbr vy cv vz cv cR wbr vz cv vx cv cR wbr
      w3a vz cv vx cv cR wbr vx cv vy cv cR wbr vy cv vz cv cR wbr wa wa cA vx
      cv vy cv vz cv cR fr3nr vx cv vy cv cR wbr vy cv vz cv cR wbr wa vz cv vx
      cv cR wbr vx cv vy cv cR wbr vy cv vz cv cR wbr vz cv vx cv cR wbr w3a vx
      cv vy cv cR wbr vy cv vz cv cR wbr vz cv vx cv cR wbr w3a vx cv vy cv cR
      wbr vy cv vz cv cR wbr wa vz cv vx cv cR wbr wa vx cv vy cv cR wbr vy cv
      vz cv cR wbr vz cv vx cv cR wbr df-3an biimpri ancoms nsyl pm2.21d exp3a
      3jaod cA cR wfr vy cv cA wcel vx cv cA wcel vx cv vx cv cR wbr wn vz cv
      cA wcel cA vx cv cR frirr 3ad2antr1 jctild ex a2d alimdv 2alimdv vx cv vz
      cv cR wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vx vy vz cA cA cA r3al
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa vx vy vz cA cA cA r3al 3imtr4g vx cv vy cv cR wbr vx cv
      vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cv vz cv cR wbr vx cv vz
      cv wceq vz cv vx cv cR wbr w3o vz cA wral vy cA wral vx cA vx cv vy cv cR
      wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cv vy cv cR wbr
      vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vy cA wral vx cv vz cv
      cR wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vz cA wral vy cA wral vx
      cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA ralidm vx
      cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cv
      vz cv cR wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vz cA wral vy cA vx
      cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vx cv vz cv cR
      wbr vx cv vz cv wceq vz cv vx cv cR wbr w3o vy vz cA vy cv vz cv wceq vx
      cv vy cv cR wbr vx cv vz cv cR wbr vx cv vy cv wceq vx cv vz cv wceq vy
      cv vx cv cR wbr vz cv vx cv cR wbr vy cv vz cv vx cv cR breq2 vy vz vx
      equequ2 vy cv vz cv vx cv cR breq1 3orbi123d cbvralv ralbii bitr3i ralbii
      vx vy vz cA cR df-po 3imtr4g ancrd impbid2 syl5bb pm5.32i bitri $.
  $}



