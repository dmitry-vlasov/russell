
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Replacement/Theorems_requiring_subset_and_intersection_existence.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                 Theorems requiring empty set existence

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.
    $( Construct, from any class ` A ` , a set equal to it when the class
       exists and equal to the empty set when the class is proper.  This
       theorem shows that the constructed set always exists.  (Contributed by
       NM, 16-Oct-2003.) $)
    class2set $p |- { x e. A | A e. _V } e. _V $=
      cA cvv wcel cA cvv wcel vx cA crab cvv wcel cA cvv wcel vx cA cvv rabexg
      cA cvv wcel wn cA cvv wcel vx cA crab c0 cvv cA cvv wcel wn cA cvv wcel
      vx cA wrex wn cA cvv wcel vx cA crab c0 wceq cA cvv wcel wn cA cvv wcel
      vx cA cA cvv wcel wn vx cv cA wcel simpl nrexdv cA cvv wcel vx cA wrex cA
      cvv wcel vx cA crab c0 cA cvv wcel vx cA rabn0 necon1bbii sylib 0ex
      syl6eqel pm2.61i $.

    $( Equality theorem based on ~ class2set .  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Raph Levien, 30-Jun-2006.) $)
    class2seteq $p |- ( A e. V -> { x e. A | A e. _V } = A ) $=
      cA cV wcel cA cvv wcel cA cvv wcel vx cA crab cA wceq cA cV elex cA cvv
      wcel cA cA cvv wcel vx cA crab cA cvv wcel cA cvv wcel vx cA wral cA cA
      cvv wcel vx cA crab wceq cA cvv wcel cA cvv wcel vx cA cA cvv wcel vx cv
      cA wcel ax-1 ralrimiv cA cvv wcel vx cA rabid2 sylibr eqcomd syl $.
  $}

  $( Every power class contains the empty set.  (Contributed by NM,
     25-Oct-2007.) $)
  0elpw $p |- (/) e. ~P A $=
    c0 cA cpw wcel c0 cA wss cA 0ss c0 cA 0ex elpw mpbir $.

  $( The empty set and its power set are not equal.  (Contributed by NM,
     23-Dec-1993.) $)
  0nep0 $p |- (/) =/= { (/) } $=
    c0 csn c0 c0 0ex snnz necomi $.

  $( Something cannot be equal to both the null set and the power set of the
     null set.  (Contributed by NM, 30-Sep-2003.) $)
  0inp0 $p |- ( A = (/) -> -. A = { (/) } ) $=
    cA c0 wceq cA c0 csn cA c0 wceq cA c0 csn wne c0 c0 csn wne 0nep0 cA c0 c0
    csn neeq1 mpbiri neneqd $.

  $( The removal of the empty set from a class does not affect its union.
     (Contributed by NM, 22-Mar-2004.) $)
  unidif0 $p |- U. ( A \ { (/) } ) = U. A $=
    cA c0 csn cdif cuni c0 cA cuni cun cA cuni c0 cun cA cuni cA c0 csn cdif
    cuni c0 csn cA cun cuni c0 csn cuni cA cuni cun c0 cA cuni cun cA c0 csn
    cdif c0 csn cun cuni cA c0 csn cdif cuni c0 csn cuni cun c0 csn cA cun cuni
    cA c0 csn cdif cuni cA c0 csn cdif c0 csn uniun c0 csn cA cun cA c0 csn
    cdif c0 csn cun cA c0 csn cdif c0 csn cun cA c0 csn cun c0 csn cA cun cA c0
    csn undif1 cA c0 csn uncom eqtr2i unieqi cA c0 csn cdif cuni c0 csn cuni
    cun cA c0 csn cdif cuni c0 cun cA c0 csn cdif cuni c0 csn cuni c0 cA c0 csn
    cdif cuni c0 0ex unisn uneq2i cA c0 csn cdif cuni un0 eqtr2i 3eqtr4ri c0
    csn cA uniun c0 csn cuni c0 cA cuni c0 0ex unisn uneq1i 3eqtri c0 cA cuni
    uncom cA cuni un0 3eqtri $.

  ${
    $d x y A $.  $d y B $.
    $( An indexed intersection of the empty set, with a non-empty index set, is
       empty.  (Contributed by NM, 20-Oct-2005.) $)
    iin0 $p |- ( A =/= (/) <-> |^|_ x e. A (/) = (/) ) $=
      cA c0 wne vx cA c0 ciin c0 wceq vx cA c0 iinconst vx cA c0 ciin c0 wceq
      cA c0 cA c0 wceq vx cA c0 ciin c0 wceq vx c0 c0 ciin c0 wceq vx c0 c0
      ciin c0 wceq cvv c0 wceq c0 cvv wcel cvv c0 wceq wn 0ex cvv c0 n0i ax-mp
      vx c0 c0 ciin cvv c0 vx c0 0iin eqeq1i mtbir cA c0 wceq vx cA c0 ciin vx
      c0 c0 ciin c0 vx cA c0 c0 iineq1 eqeq1d mtbiri necon2ai impbii $.
  $}

  ${
    $d x A $.
    notzfaus.1 $e |- A = { (/) } $.
    notzfaus.2 $e |- ( ph <-> -. x e. y ) $.
    $( In the Separation Scheme ~ zfauscl , we require that ` y ` not occur in
       ` ph ` (which can be generalized to "not be free in").  Here we show
       special cases of ` A ` and ` ph ` that result in a contradiction by
       violating this requirement.  (Contributed by NM, 8-Feb-2006.) $)
    notzfaus $p |- -. E. y A. x ( x e. y <-> ( x e. A /\ ph ) ) $=
      vx cv vy cv wcel vx cv cA wcel wph wa wb vx wal vy vx cv vy cv wcel vx cv
      cA wcel wph wa wb wn vx wex vx cv vy cv wcel vx cv cA wcel wph wa wb vx
      wal wn vx cv cA wcel vx wex vx cv vy cv wcel vx cv cA wcel wph wa wb wn
      vx wex cA c0 wne vx cv cA wcel vx wex cA c0 csn c0 notzfaus.1 c0 0ex snnz
      eqnetri vx cA n0 mpbi vx cv cA wcel vx cv vy cv wcel vx cv cA wcel wph wa
      wb wn vx vx cv cA wcel vx cv vy cv wcel vx cv cA wcel wph wa wn wb vx cv
      vy cv wcel vx cv cA wcel wph wa wb wn vx cv cA wcel vx cv vy cv wcel vx
      cv cA wcel vx cv vy cv wcel wi vx cv cA wcel wph wa wn vx cv cA wcel vx
      cv vy cv wcel biimt vx cv cA wcel vx cv vy cv wcel wi vx cv cA wcel vx cv
      vy cv wcel wn wa vx cv cA wcel wph wa vx cv cA wcel vx cv vy cv wcel iman
      wph vx cv vy cv wcel wn vx cv cA wcel notzfaus.2 anbi2i xchbinxr syl6bb
      vx cv vy cv wcel vx cv cA wcel wph wa xor3 sylibr eximi ax-mp vx cv vy cv
      wcel vx cv cA wcel wph wa wb vx exnal mpbi nex $.
  $}

  $( The intersection of the universal class is empty.  (Contributed by NM,
     11-Sep-2008.) $)
  intv $p |- |^| _V = (/) $=
    c0 cvv wcel cvv cint c0 wceq 0ex cvv int0el ax-mp $.

  ${
    $d x y z A $.
    axpweq.1 $e |- A e. _V $.
    $( Two equivalent ways to express the Power Set Axiom.  Note that ~ ax-pow
       is not used by the proof.  (Contributed by NM, 22-Jun-2009.) $)
    axpweq $p |- ( ~P A e. _V
                <-> E. x A. y ( A. z ( z e. y -> z e. A ) -> y e. x ) ) $=
      cA cpw cvv wcel cA cpw vx cv cpw wcel vx wex vz cv vy cv wcel vz cv cA
      wcel wi vz wal vy cv vx cv wcel wi vy wal vx wex cA cpw cvv wcel cA cpw
      vx cv cpw wcel vx wex cA cpw cvv wcel cA cpw cA cpw cpw wcel cA cpw vx cv
      cpw wcel vx wex cA cpw cvv pwidg cA cpw vx cv cpw wcel cA cpw cA cpw cpw
      wcel vx cA cpw cvv vx cv cA cpw wceq vx cv cpw cA cpw cpw cA cpw vx cv cA
      cpw pweq eleq2d spcegv mpd cA cpw vx cv cpw wcel cA cpw cvv wcel vx cA
      cpw vx cv cpw elex exlimiv impbii cA cpw vx cv cpw wcel vz cv vy cv wcel
      vz cv cA wcel wi vz wal vy cv vx cv wcel wi vy wal vx cA cpw vx cv cpw
      wcel cA cpw vx cv wss vz cv vy cv wcel vz cv cA wcel wi vz wal vy cv vx
      cv wcel wi vy wal cA cpw vx cv vx vex elpw2 cA cpw vx cv wss vy cv cA wss
      vy cv vx cv wcel wi vy wal vz cv vy cv wcel vz cv cA wcel wi vz wal vy cv
      vx cv wcel wi vy wal vy cA vx cv pwss vy cv cA wss vy cv vx cv wcel wi vz
      cv vy cv wcel vz cv cA wcel wi vz wal vy cv vx cv wcel wi vy vy cv cA wss
      vz cv vy cv wcel vz cv cA wcel wi vz wal vy cv vx cv wcel vz vy cv cA
      dfss2 imbi1i albii bitri bitri exbii bitri $.
  $}


