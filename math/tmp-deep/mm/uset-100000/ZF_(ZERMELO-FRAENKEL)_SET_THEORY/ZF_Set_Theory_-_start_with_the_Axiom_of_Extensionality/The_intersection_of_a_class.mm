
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_union_of_a_class.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The intersection of a class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare class intersection symbol. $)
  $c |^| $. $( Big cap $)

  $( Extend class notation to include the intersection of a class (read:
     'intersect ` A ` '). $)
  cint $a class |^| A $.

  ${
    $d x y A $.
    $( Define the intersection of a class.  Definition 7.35 of [TakeutiZaring]
       p. 44.  For example, ` |^| { { 1 , 3 } , { 1 , 8 } } = { 1 } ` .
       Compare this with the intersection of two classes, ~ df-in .
       (Contributed by NM, 18-Aug-1993.) $)
    df-int $a |- |^| A = { x | A. y ( y e. A -> x e. y ) } $.
  $}

  ${
    $d x y A $.
    $( Alternate definition of class intersection.  (Contributed by NM,
       28-Jun-1998.) $)
    dfint2 $p |- |^| A = { x | A. y e. A x e. y } $=
      cA cint vy cv cA wcel vx cv vy cv wcel wi vy wal vx cab vx cv vy cv wcel
      vy cA wral vx cab vx vy cA df-int vx cv vy cv wcel vy cA wral vy cv cA
      wcel vx cv vy cv wcel wi vy wal vx vx cv vy cv wcel vy cA df-ral abbii
      eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Equality law for intersection.  (Contributed by NM, 13-Sep-1999.) $)
    inteq $p |- ( A = B -> |^| A = |^| B ) $=
      cA cB wceq vx cv vy cv wcel vy cA wral vx cab vx cv vy cv wcel vy cB wral
      vx cab cA cint cB cint cA cB wceq vx cv vy cv wcel vy cA wral vx cv vy cv
      wcel vy cB wral vx vx cv vy cv wcel vy cA cB raleq abbidv vx vy cA dfint2
      vx vy cB dfint2 3eqtr4g $.
  $}

  ${
    inteqi.1 $e |- A = B $.
    $( Equality inference for class intersection.  (Contributed by NM,
       2-Sep-2003.) $)
    inteqi $p |- |^| A = |^| B $=
      cA cB wceq cA cint cB cint wceq inteqi.1 cA cB inteq ax-mp $.
  $}

  ${
    inteqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for class intersection.  (Contributed by NM,
       2-Sep-2003.) $)
    inteqd $p |- ( ph -> |^| A = |^| B ) $=
      wph cA cB wceq cA cint cB cint wceq inteqd.1 cA cB inteq syl $.
  $}

  ${
    $d x A y $.  $d x B y $.
    elint.1 $e |- A e. _V $.
    $( Membership in class intersection.  (Contributed by NM, 21-May-1994.) $)
    elint $p |- ( A e. |^| B <-> A. x ( x e. B -> A e. x ) ) $=
      vx cv cB wcel vy cv vx cv wcel wi vx wal vx cv cB wcel cA vx cv wcel wi
      vx wal vy cA cB cint elint.1 vy cv cA wceq vx cv cB wcel vy cv vx cv wcel
      wi vx cv cB wcel cA vx cv wcel wi vx vy cv cA wceq vy cv vx cv wcel cA vx
      cv wcel vx cv cB wcel vy cv cA vx cv eleq1 imbi2d albidv vy vx cB df-int
      elab2 $.
  $}

  ${
    $d x A $.  $d x B $.
    elint2.1 $e |- A e. _V $.
    $( Membership in class intersection.  (Contributed by NM, 14-Oct-1999.) $)
    elint2 $p |- ( A e. |^| B <-> A. x e. B A e. x ) $=
      cA cB cint wcel vx cv cB wcel cA vx cv wcel wi vx wal cA vx cv wcel vx cB
      wral vx cA cB elint2.1 elint cA vx cv wcel vx cB df-ral bitr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Membership in class intersection, with the sethood requirement expressed
       as an antecedent.  (Contributed by NM, 20-Nov-2003.) $)
    elintg $p |- ( A e. V -> ( A e. |^| B <-> A. x e. B A e. x ) ) $=
      vy cv cB cint wcel vy cv vx cv wcel vx cB wral cA cB cint wcel cA vx cv
      wcel vx cB wral vy cA cV vy cv cA cB cint eleq1 vy cv cA wceq vy cv vx cv
      wcel cA vx cv wcel vx cB vy cv cA vx cv eleq1 ralbidv vx vy cv cB vy vex
      elint2 vtoclbg $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Membership in class intersection.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    elinti $p |- ( A e. |^| B -> ( C e. B -> A e. C ) ) $=
      cA cB cint wcel cC cB wcel cA cC wcel wi cA cB cint wcel cA cB cint wcel
      cA vx cv wcel vx cB wral cC cB wcel cA cC wcel wi vx cA cB cB cint elintg
      cA vx cv wcel cA cC wcel vx cC cB vx cv cC cA eleq2 rspccv syl6bi pm2.43i
      $.
  $}

  ${
    $d y z A $.  $d x y z $.
    nfint.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for intersection.  (Contributed by NM,
       2-Feb-1997.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.) $)
    nfint $p |- F/_ x |^| A $=
      vx cA cint vy cv vz cv wcel vz cA wral vy cab vy vz cA dfint2 vy cv vz cv
      wcel vz cA wral vx vy vy cv vz cv wcel vx vz cA nfint.1 vy cv vz cv wcel
      vx nfv nfral nfab nfcxfr $.
  $}

  ${
    $d A x y $.  $d ph y $.
    inteqab.1 $e |- A e. _V $.
    $( Membership in the intersection of a class abstraction.  (Contributed by
       NM, 30-Aug-1993.) $)
    elintab $p |- ( A e. |^| { x | ph } <-> A. x ( ph -> A e. x ) ) $=
      cA wph vx cab cint wcel vy cv wph vx cab wcel cA vy cv wcel wi vy wal wph
      cA vx cv wcel wi vx wal vy cA wph vx cab inteqab.1 elint vy cv wph vx cab
      wcel cA vy cv wcel wi wph cA vx cv wcel wi vy vx vy cv wph vx cab wcel cA
      vy cv wcel vx wph vx vy nfsab1 cA vy cv wcel vx nfv nfim wph cA vx cv
      wcel wi vy nfv vy cv vx cv wceq vy cv wph vx cab wcel wph cA vy cv wcel
      cA vx cv wcel vy cv vx cv wceq vy cv wph vx cab wcel vx cv wph vx cab
      wcel wph vy cv vx cv wph vx cab eleq1 wph vx abid syl6bb vy cv vx cv cA
      eleq2 imbi12d cbval bitri $.

    $( Membership in the intersection of a class abstraction.  (Contributed by
       NM, 17-Oct-1999.) $)
    elintrab $p |- ( A e. |^| { x e. B | ph } <->
                 A. x e. B ( ph -> A e. x ) ) $=
      cA vx cv cB wcel wph wa vx cab cint wcel vx cv cB wcel wph cA vx cv wcel
      wi wi vx wal cA wph vx cB crab cint wcel wph cA vx cv wcel wi vx cB wral
      cA vx cv cB wcel wph wa vx cab cint wcel vx cv cB wcel wph wa cA vx cv
      wcel wi vx wal vx cv cB wcel wph cA vx cv wcel wi wi vx wal vx cv cB wcel
      wph wa vx cA inteqab.1 elintab vx cv cB wcel wph wa cA vx cv wcel wi vx
      cv cB wcel wph cA vx cv wcel wi wi vx vx cv cB wcel wph cA vx cv wcel
      impexp albii bitri wph vx cB crab cint vx cv cB wcel wph wa vx cab cint
      cA wph vx cB crab vx cv cB wcel wph wa vx cab wph vx cB df-rab inteqi
      eleq2i wph cA vx cv wcel wi vx cB df-ral 3bitr4i $.
  $}

  ${
    $d x y A $.  $d y B $.  $d y ph $.
    $( Membership in the intersection of a class abstraction.  (Contributed by
       NM, 17-Feb-2007.) $)
    elintrabg $p |- ( A e. V -> ( A e. |^| { x e. B | ph } <->
                 A. x e. B ( ph -> A e. x ) ) ) $=
      vy cv wph vx cB crab cint wcel wph vy cv vx cv wcel wi vx cB wral cA wph
      vx cB crab cint wcel wph cA vx cv wcel wi vx cB wral vy cA cV vy cv cA
      wph vx cB crab cint eleq1 vy cv cA wceq wph vy cv vx cv wcel wi wph cA vx
      cv wcel wi vx cB vy cv cA wceq vy cv vx cv wcel cA vx cv wcel wph vy cv
      cA vx cv eleq1 imbi2d ralbidv wph vx vy cv cB vy vex elintrab vtoclbg $.

    $( The intersection of the empty set is the universal class.  Exercise 2 of
       [TakeutiZaring] p. 44.  (Contributed by NM, 18-Aug-1993.) $)
    int0 $p |- |^| (/) = _V $=
      vy cv c0 wcel vx cv vy cv wcel wi vy wal vx cab vx cv vx cv wceq vx cab
      c0 cint cvv vy cv c0 wcel vx cv vy cv wcel wi vy wal vx cv vx cv wceq vx
      vy cv c0 wcel vx cv vy cv wcel wi vy wal vx cv vx cv wceq vy cv c0 wcel
      vx cv vy cv wcel wi vy vy cv c0 wcel vx cv vy cv wcel vy cv noel pm2.21i
      ax-gen vx cv eqid 2th abbii vx vy c0 df-int vx df-v 3eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y ph $.
    $( An element of a class includes the intersection of the class.  Exercise
       4 of [TakeutiZaring] p. 44 (with correction), generalized to classes.
       (Contributed by NM, 18-Nov-1995.) $)
    intss1 $p |- ( A e. B -> |^| B C_ A ) $=
      cA cB wcel vx cB cint cA vx cv cB cint wcel vy cv cB wcel vx cv vy cv
      wcel wi vy wal cA cB wcel vx cv cA wcel vy vx cv cB vx vex elint vy cv cB
      wcel vx cv vy cv wcel wi vy wal cA cB wcel vx cv cA wcel vy cv cB wcel vx
      cv vy cv wcel wi cA cB wcel vx cv cA wcel wi vy cA cB vy cv cA wceq vy cv
      cB wcel cA cB wcel vx cv vy cv wcel vx cv cA wcel vy cv cA cB eleq1 vy cv
      cA vx cv eleq2 imbi12d spcgv pm2.43a syl5bi ssrdv $.

    $( Subclass of a class intersection.  Theorem 5.11(viii) of [Monk1] p. 52
       and its converse.  (Contributed by NM, 14-Oct-1999.) $)
    ssint $p |- ( A C_ |^| B <-> A. x e. B A C_ x ) $=
      cA cB cint wss vy cv cB cint wcel vy cA wral vy cv vx cv wcel vx cB wral
      vy cA wral cA vx cv wss vx cB wral vy cA cB cint dfss3 vy cv cB cint wcel
      vy cv vx cv wcel vx cB wral vy cA vx vy cv cB vy vex elint2 ralbii vy cv
      vx cv wcel vx cB wral vy cA wral vy cv vx cv wcel vy cA wral vx cB wral
      cA vx cv wss vx cB wral vy cv vx cv wcel vy vx cA cB ralcom cA vx cv wss
      vy cv vx cv wcel vy cA wral vx cB vy cA vx cv dfss3 ralbii bitr4i 3bitri
      $.

    $( Subclass of the intersection of a class abstraction.  (Contributed by
       NM, 31-Jul-2006.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    ssintab $p |- ( A C_ |^| { x | ph } <-> A. x ( ph -> A C_ x ) ) $=
      cA wph vx cab cint wss cA vy cv wss vy wph vx cab wral wph cA vx cv wss
      wi vx wal vy cA wph vx cab ssint wph cA vy cv wss cA vx cv wss vy vx vy
      cv vx cv cA sseq2 ralab2 bitri $.

    $( Subclass of the least upper bound.  (Contributed by NM, 8-Aug-2000.) $)
    ssintub $p |- A C_ |^| { x e. B | A C_ x } $=
      cA cA vx cv wss vx cB crab cint wss cA vy cv wss vy cA vx cv wss vx cB
      crab vy cA cA vx cv wss vx cB crab ssint vy cv cA vx cv wss vx cB crab
      wcel vy cv cB wcel cA vy cv wss cA vx cv wss cA vy cv wss vx vy cv cB vx
      cv vy cv cA sseq2 elrab simprbi mprgbir $.

    $( Subclass of the minimum value of class of supersets.  (Contributed by
       NM, 10-Aug-2006.) $)
    ssmin $p |- A C_ |^| { x | ( A C_ x /\ ph ) } $=
      cA cA vx cv wss wph wa vx cab cint wss cA vx cv wss wph wa cA vx cv wss
      wi vx cA vx cv wss wph wa vx cA ssintab cA vx cv wss wph simpl mpgbir $.

    $( Any member of a class is the smallest of those members that include it.
       (Contributed by NM, 13-Aug-2002.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    intmin $p |- ( A e. B -> |^| { x e. B | A C_ x } = A ) $=
      cA cB wcel cA vx cv wss vx cB crab cint cA cA cB wcel vy cA vx cv wss vx
      cB crab cint cA vy cv cA vx cv wss vx cB crab cint wcel cA vx cv wss vy
      cv vx cv wcel wi vx cB wral cA cB wcel vy cv cA wcel cA vx cv wss vx vy
      cv cB vy vex elintrab cA cB wcel cA vx cv wss vy cv vx cv wcel wi vx cB
      wral cA cA wss vy cv cA wcel cA ssid cA vx cv wss vy cv vx cv wcel wi cA
      cA wss vy cv cA wcel wi vx cA cB vx cv cA wceq cA vx cv wss cA cA wss vy
      cv vx cv wcel vy cv cA wcel vx cv cA cA sseq2 vx cv cA vy cv eleq2
      imbi12d rspcv mpii syl5bi ssrdv cA cA vx cv wss vx cB crab cint wss cA cB
      wcel vx cA cB ssintub a1i eqssd $.

    $( Intersection of subclasses.  (Contributed by NM, 14-Oct-1999.) $)
    intss $p |- ( A C_ B -> |^| B C_ |^| A ) $=
      vy cv cA wcel vy cv cB wcel wi vy wal vx cv cB cint wcel vx cv cA cint
      wcel wi vx wal cA cB wss cB cint cA cint wss vy cv cA wcel vy cv cB wcel
      wi vy wal vx cv cB cint wcel vx cv cA cint wcel wi vx vy cv cA wcel vy cv
      cB wcel wi vy wal vy cv cB wcel vx cv vy cv wcel wi vy wal vy cv cA wcel
      vx cv vy cv wcel wi vy wal vx cv cB cint wcel vx cv cA cint wcel vy cv cA
      wcel vy cv cB wcel wi vy cv cB wcel vx cv vy cv wcel wi vy cv cA wcel vx
      cv vy cv wcel wi vy vy cv cA wcel vy cv cB wcel vx cv vy cv wcel imim1
      al2imi vy vx cv cB vx vex elint vy vx cv cA vx vex elint 3imtr4g alrimiv
      vy cA cB dfss2 vx cB cint cA cint dfss2 3imtr4i $.

    $( The intersection of a nonempty set is a subclass of its union.
       (Contributed by NM, 29-Jul-2006.) $)
    intssuni $p |- ( A =/= (/) -> |^| A C_ U. A ) $=
      cA c0 wne vx cA cint cA cuni cA c0 wne vx cv vy cv wcel vy cA wral vx cv
      vy cv wcel vy cA wrex vx cv cA cint wcel vx cv cA cuni wcel cA c0 wne vx
      cv vy cv wcel vy cA wral vx cv vy cv wcel vy cA wrex vx cv vy cv wcel vy
      cA r19.2z ex vy vx cv cA vx vex elint2 vy vx cv cA eluni2 3imtr4g ssrdv
      $.
  $}

  ${
    $d x A $.
    $( Subclass of the intersection of a restricted class builder.
       (Contributed by NM, 30-Jan-2015.) $)
    ssintrab $p |- ( A C_ |^| { x e. B | ph }
           <-> A. x e. B ( ph -> A C_ x ) ) $=
      cA wph vx cB crab cint wss cA vx cv cB wcel wph wa vx cab cint wss wph cA
      vx cv wss wi vx cB wral wph vx cB crab cint vx cv cB wcel wph wa vx cab
      cint cA wph vx cB crab vx cv cB wcel wph wa vx cab wph vx cB df-rab
      inteqi sseq2i vx cv cB wcel wph wa cA vx cv wss wi vx wal vx cv cB wcel
      wph cA vx cv wss wi wi vx wal cA vx cv cB wcel wph wa vx cab cint wss wph
      cA vx cv wss wi vx cB wral vx cv cB wcel wph wa cA vx cv wss wi vx cv cB
      wcel wph cA vx cv wss wi wi vx vx cv cB wcel wph cA vx cv wss impexp
      albii vx cv cB wcel wph wa vx cA ssintab wph cA vx cv wss wi vx cB df-ral
      3bitr4i bitri $.
  $}

  $( If the union of a class is included in its intersection, the class is
     either the empty set or a singleton ( ~ uniintsn ).  (Contributed by NM,
     30-Oct-2010.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
  unissint $p |- ( U. A C_ |^| A <-> ( A = (/) \/ U. A = |^| A ) ) $=
    cA cuni cA cint wss cA c0 wceq cA cuni cA cint wceq wo cA cuni cA cint wss
    cA c0 wceq cA cuni cA cint wceq cA cuni cA cint wss cA c0 wceq wn cA cuni
    cA cint wceq cA cuni cA cint wss cA c0 wceq wn wa cA cuni cA cint cA cuni
    cA cint wss cA c0 wceq wn simpl cA c0 wceq wn cA cint cA cuni wss cA cuni
    cA cint wss cA c0 wceq wn cA c0 wne cA cint cA cuni wss cA c0 df-ne cA
    intssuni sylbir adantl eqssd ex orrd cA c0 wceq cA cuni cA cint wss cA cuni
    cA cint wceq cA c0 wceq c0 cint cA cuni cA cint cA cuni cvv c0 cint cA cuni
    ssv int0 sseqtr4i cA c0 inteq syl5sseqr cA cuni cA cint eqimss jaoi impbii
    $.

  $( Subclass relationship for intersection and union.  (Contributed by NM,
     29-Jul-2006.) $)
  intssuni2 $p |- ( ( A C_ B /\ A =/= (/) ) -> |^| A C_ U. B ) $=
    cA c0 wne cA cB wss cA cint cA cuni cB cuni cA intssuni cA cB uniss
    sylan9ssr $.

  ${
    $d x A $.  $d x B $.  $d x ps $.
    intminss.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Under subset ordering, the intersection of a restricted class
       abstraction is less than or equal to any of its members.  (Contributed
       by NM, 7-Sep-2013.) $)
    intminss $p |- ( ( A e. B /\ ps ) -> |^| { x e. B | ph } C_ A ) $=
      cA cB wcel wps wa cA wph vx cB crab wcel wph vx cB crab cint cA wss wph
      wps vx cA cB intminss.1 elrab cA wph vx cB crab intss1 sylbir $.
  $}

  ${
    $d x A $.
    intmin2.1 $e |- A e. _V $.
    $( Any set is the smallest of all sets that include it.  (Contributed by
       NM, 20-Sep-2003.) $)
    intmin2 $p |- |^| { x | A C_ x } = A $=
      cA vx cv wss vx cvv crab cint cA vx cv wss vx cab cint cA cA vx cv wss vx
      cvv crab cA vx cv wss vx cab cA vx cv wss vx rabab inteqi cA cvv wcel cA
      vx cv wss vx cvv crab cint cA wceq intmin2.1 vx cA cvv intmin ax-mp
      eqtr3i $.
  $}

  ${
    $d x A $.  $d x ps $.
    intmin3.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    intmin3.3 $e |- ps $.
    $( Under subset ordering, the intersection of a class abstraction is less
       than or equal to any of its members.  (Contributed by NM,
       3-Jul-2005.) $)
    intmin3 $p |- ( A e. V -> |^| { x | ph } C_ A ) $=
      cA cV wcel cA wph vx cab wcel wph vx cab cint cA wss cA cV wcel cA wph vx
      cab wcel wps intmin3.3 wph wps vx cA cV intmin3.2 elabg mpbiri cA wph vx
      cab intss1 syl $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( Elimination of a conjunct in a class intersection.  (Contributed by NM,
       31-Jul-2006.) $)
    intmin4 $p |- ( A C_ |^| { x | ph } ->
                  |^| { x | ( A C_ x /\ ph ) } = |^| { x | ph } ) $=
      cA wph vx cab cint wss vy cA vx cv wss wph wa vx cab cint wph vx cab cint
      cA wph vx cab cint wss cA vx cv wss wph wa vy cv vx cv wcel wi vx wal wph
      vy cv vx cv wcel wi vx wal vy cv cA vx cv wss wph wa vx cab cint wcel vy
      cv wph vx cab cint wcel cA wph vx cab cint wss wph cA vx cv wss wi vx wal
      cA vx cv wss wph wa vy cv vx cv wcel wi vx wal wph vy cv vx cv wcel wi vx
      wal wb wph vx cA ssintab wph cA vx cv wss wi vx wal cA vx cv wss wph wa
      vy cv vx cv wcel wi wph vy cv vx cv wcel wi wb vx wal cA vx cv wss wph wa
      vy cv vx cv wcel wi vx wal wph vy cv vx cv wcel wi vx wal wb wph cA vx cv
      wss wi cA vx cv wss wph wa vy cv vx cv wcel wi wph vy cv vx cv wcel wi wb
      vx wph cA vx cv wss wi cA vx cv wss wph wa wph vy cv vx cv wcel wph cA vx
      cv wss wi cA vx cv wss wph wa wph cA vx cv wss wph simpr wph cA vx cv wss
      ancr impbid2 imbi1d alimi cA vx cv wss wph wa vy cv vx cv wcel wi wph vy
      cv vx cv wcel wi vx albi syl sylbi cA vx cv wss wph wa vx vy cv vy vex
      elintab wph vx vy cv vy vex elintab 3bitr4g eqrdv $.
  $}

  ${
    $d x z A $.  $d x z ph $.  $d x y z $.
    intab.1 $e |- A e. _V $.
    intab.2 $e |- { x | E. y ( ph /\ x = A ) } e. _V $.
    $( The intersection of a special case of a class abstraction. ` y ` may be
       free in ` ph ` and ` A ` , which can be thought of a ` ph ( y ) ` and
       ` A ( y ) ` .  Typically, ~ abrexex2 or ~ abexssex can be used to
       satisfy the second hypothesis.  (Contributed by NM, 28-Jul-2006.)
       (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)
    intab $p |- |^| { x | A. y ( ph -> A e. x ) } =
                { x | E. y ( ph /\ x = A ) } $=
      wph cA vx cv wcel wi vy wal vx cab cint wph vz cv cA wceq wa vy wex vz
      cab wph vx cv cA wceq wa vy wex vx cab wph cA vx cv wcel wi vy wal vx cab
      cint wph vz cv cA wceq wa vy wex vz cab wph vz cv cA wceq wa vy wex vz
      cab wph cA vx cv wcel wi vy wal vx cab wcel wph cA vx cv wcel wi vy wal
      vx cab cint wph vz cv cA wceq wa vy wex vz cab wss wph vz cv cA wceq wa
      vy wex vz cab wph cA vx cv wcel wi vy wal vx cab wcel wph cA wph vz cv cA
      wceq wa vy wex vz cab wcel wi vy wph cA vx cv wcel wi vy wal wph cA wph
      vz cv cA wceq wa vy wex vz cab wcel wi vy wal vx wph vz cv cA wceq wa vy
      wex vz cab wph vz cv cA wceq wa vy wex vz cab wph vx cv cA wceq wa vy wex
      vx cab cvv wph vz cv cA wceq wa vy wex wph vx cv cA wceq wa vy wex vz vx
      vz cv vx cv wceq wph vz cv cA wceq wa wph vx cv cA wceq wa vy vz cv vx cv
      wceq vz cv cA wceq vx cv cA wceq wph vz cv vx cv cA eqeq1 anbi2d exbidv
      cbvabv intab.2 eqeltri vx cv wph vz cv cA wceq wa vy wex vz cab wceq wph
      cA vx cv wcel wi wph cA wph vz cv cA wceq wa vy wex vz cab wcel wi vy vy
      vx cv wph vz cv cA wceq wa vy wex vz cab wph vz cv cA wceq wa vy wex vy
      vz wph vz cv cA wceq wa vy nfe1 nfab nfeq2 vx cv wph vz cv cA wceq wa vy
      wex vz cab wceq cA vx cv wcel cA wph vz cv cA wceq wa vy wex vz cab wcel
      wph vx cv wph vz cv cA wceq wa vy wex vz cab cA eleq2 imbi2d albid elab
      wph wph vz cv cA wceq wa vy wex vz cA wsbc cA wph vz cv cA wceq wa vy wex
      vz cab wcel wph vz cv cA wceq wph vz cv cA wceq wa vy wex wi vz wal wph
      vz cv cA wceq wa vy wex vz cA wsbc wph vz cv cA wceq wph vz cv cA wceq wa
      vy wex wi vz wph vz cv cA wceq wph vz cv cA wceq wa vy wex wph vz cv cA
      wceq wa vy 19.8a ex alrimiv wph vz cv cA wceq wa vy wex vz cA intab.1
      sbc6 sylibr wph vz cv cA wceq wa vy wex vz cA df-sbc sylib mpgbir wph vz
      cv cA wceq wa vy wex vz cab wph cA vx cv wcel wi vy wal vx cab intss1
      ax-mp wph vz cv cA wceq wa vy wex vz wph cA vx cv wcel wi vy wal vx cab
      cint wph vz cv cA wceq wa vy wex wph cA vx cv wcel wi vy wal vz cv vx cv
      wcel wi vx wal vz cv wph cA vx cv wcel wi vy wal vx cab cint wcel wph vz
      cv cA wceq wa vy wex wph cA vx cv wcel wi vy wal vz cv vx cv wcel wi vx
      wph vz cv cA wceq wa vy wex wph cA vx cv wcel wi vy wal vz cv vx cv wcel
      wph vz cv cA wceq wa vy wex wph cA vx cv wcel wi vy wal wa wph vz cv cA
      wceq wa wph cA vx cv wcel wi wa vy wex vz cv vx cv wcel wph vz cv cA wceq
      wa wph cA vx cv wcel wi vy 19.29r wph vz cv cA wceq wa wph cA vx cv wcel
      wi wa vz cv vx cv wcel vy wph vz cv cA wceq wa wph cA vx cv wcel wi wa vz
      cv cA vx cv wph vz cv cA wceq wph cA vx cv wcel wi simplr wph wph cA vx
      cv wcel wi cA vx cv wcel vz cv cA wceq wph cA vx cv wcel pm3.35 adantlr
      eqeltrd exlimiv syl ex alrimiv wph cA vx cv wcel wi vy wal vx vz cv vz
      vex elintab sylibr abssi eqssi wph vz cv cA wceq wa vy wex wph vx cv cA
      wceq wa vy wex vz vx vz cv vx cv wceq wph vz cv cA wceq wa wph vx cv cA
      wceq wa vy vz cv vx cv wceq vz cv cA wceq vx cv cA wceq wph vz cv vx cv
      cA eqeq1 anbi2d exbidv cbvabv eqtri $.
  $}

  $( The intersection of a class containing the empty set is empty.
     (Contributed by NM, 24-Apr-2004.) $)
  int0el $p |- ( (/) e. A -> |^| A = (/) ) $=
    c0 cA wcel cA cint c0 c0 cA intss1 c0 cA cint wss c0 cA wcel cA cint 0ss
    a1i eqssd $.

  ${
    $d x y A $.  $d x y B $.
    $( The class intersection of the union of two classes.  Theorem 78 of
       [Suppes] p. 42.  (Contributed by NM, 22-Sep-2002.) $)
    intun $p |- |^| ( A u. B ) = ( |^| A i^i |^| B ) $=
      vx cA cB cun cint cA cint cB cint cin vy cv cA cB cun wcel vx cv vy cv
      wcel wi vy wal vx cv cA cint wcel vx cv cB cint wcel wa vx cv cA cB cun
      cint wcel vx cv cA cint cB cint cin wcel vy cv cA wcel vx cv vy cv wcel
      wi vy cv cB wcel vx cv vy cv wcel wi wa vy wal vy cv cA wcel vx cv vy cv
      wcel wi vy wal vy cv cB wcel vx cv vy cv wcel wi vy wal wa vy cv cA cB
      cun wcel vx cv vy cv wcel wi vy wal vx cv cA cint wcel vx cv cB cint wcel
      wa vy cv cA wcel vx cv vy cv wcel wi vy cv cB wcel vx cv vy cv wcel wi vy
      19.26 vy cv cA cB cun wcel vx cv vy cv wcel wi vy cv cA wcel vx cv vy cv
      wcel wi vy cv cB wcel vx cv vy cv wcel wi wa vy vy cv cA cB cun wcel vx
      cv vy cv wcel wi vy cv cA wcel vy cv cB wcel wo vx cv vy cv wcel wi vy cv
      cA wcel vx cv vy cv wcel wi vy cv cB wcel vx cv vy cv wcel wi wa vy cv cA
      cB cun wcel vy cv cA wcel vy cv cB wcel wo vx cv vy cv wcel vy cv cA cB
      elun imbi1i vy cv cA wcel vx cv vy cv wcel vy cv cB wcel jaob bitri albii
      vx cv cA cint wcel vy cv cA wcel vx cv vy cv wcel wi vy wal vx cv cB cint
      wcel vy cv cB wcel vx cv vy cv wcel wi vy wal vy vx cv cA vx vex elint vy
      vx cv cB vx vex elint anbi12i 3bitr4i vy vx cv cA cB cun vx vex elint vx
      cv cA cint cB cint elin 3bitr4i eqriv $.
  $}

  ${
    $d x y A $.  $d x y B $.
    intpr.1 $e |- A e. _V $.
    intpr.2 $e |- B e. _V $.
    $( The intersection of a pair is the intersection of its members.  Theorem
       71 of [Suppes] p. 42.  (Contributed by NM, 14-Oct-1999.) $)
    intpr $p |- |^| { A , B } = ( A i^i B ) $=
      vx cA cB cpr cint cA cB cin vy cv cA cB cpr wcel vx cv vy cv wcel wi vy
      wal vx cv cA wcel vx cv cB wcel wa vx cv cA cB cpr cint wcel vx cv cA cB
      cin wcel vy cv cA wceq vx cv vy cv wcel wi vy cv cB wceq vx cv vy cv wcel
      wi wa vy wal vy cv cA wceq vx cv vy cv wcel wi vy wal vy cv cB wceq vx cv
      vy cv wcel wi vy wal wa vy cv cA cB cpr wcel vx cv vy cv wcel wi vy wal
      vx cv cA wcel vx cv cB wcel wa vy cv cA wceq vx cv vy cv wcel wi vy cv cB
      wceq vx cv vy cv wcel wi vy 19.26 vy cv cA cB cpr wcel vx cv vy cv wcel
      wi vy cv cA wceq vx cv vy cv wcel wi vy cv cB wceq vx cv vy cv wcel wi wa
      vy vy cv cA cB cpr wcel vx cv vy cv wcel wi vy cv cA wceq vy cv cB wceq
      wo vx cv vy cv wcel wi vy cv cA wceq vx cv vy cv wcel wi vy cv cB wceq vx
      cv vy cv wcel wi wa vy cv cA cB cpr wcel vy cv cA wceq vy cv cB wceq wo
      vx cv vy cv wcel vy cv cA cB vy vex elpr imbi1i vy cv cA wceq vx cv vy cv
      wcel vy cv cB wceq jaob bitri albii vx cv cA wcel vy cv cA wceq vx cv vy
      cv wcel wi vy wal vx cv cB wcel vy cv cB wceq vx cv vy cv wcel wi vy wal
      vy vx cv cA intpr.1 clel4 vy vx cv cB intpr.2 clel4 anbi12i 3bitr4i vy vx
      cv cA cB cpr vx vex elint vx cv cA cB elin 3bitr4i eqriv $.
  $}

  ${
    $d x y A $.  $d y B $.
    $( The intersection of a pair is the intersection of its members.  Closed
       form of ~ intpr .  Theorem 71 of [Suppes] p. 42.  (Contributed by FL,
       27-Apr-2008.) $)
    intprg $p |- ( ( A e. V /\ B e. W ) -> |^| { A , B } = ( A i^i B ) ) $=
      vx cv vy cv cpr cint vx cv vy cv cin wceq cA vy cv cpr cint cA vy cv cin
      wceq cA cB cpr cint cA cB cin wceq vx vy cA cB cV cW vx cv cA wceq vx cv
      vy cv cpr cint cA vy cv cpr cint vx cv vy cv cin cA vy cv cin vx cv cA
      wceq vx cv vy cv cpr cA vy cv cpr vx cv cA vy cv preq1 inteqd vx cv cA vy
      cv ineq1 eqeq12d vy cv cB wceq cA vy cv cpr cint cA cB cpr cint cA vy cv
      cin cA cB cin vy cv cB wceq cA vy cv cpr cA cB cpr vy cv cB cA preq2
      inteqd vy cv cB cA ineq2 eqeq12d vx cv vy cv vx vex vy vex intpr vtocl2g
      $.
  $}

  $( Intersection of a singleton.  (Contributed by Stefan O'Rear,
     22-Feb-2015.) $)
  intsng $p |- ( A e. V -> |^| { A } = A ) $=
    cA cV wcel cA csn cint cA cA cpr cint cA cA csn cA cA cpr cA dfsn2 inteqi
    cA cV wcel cA cA cpr cint cA cA cin cA cA cV wcel cA cA cpr cint cA cA cin
    wceq cA cA cV cV intprg anidms cA inidm syl6eq syl5eq $.

  ${
    intsn.1 $e |- A e. _V $.
    $( The intersection of a singleton is its member.  Theorem 70 of [Suppes]
       p. 41.  (Contributed by NM, 29-Sep-2002.) $)
    intsn $p |- |^| { A } = A $=
      cA cvv wcel cA csn cint cA wceq intsn.1 cA cvv intsng ax-mp $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( Two ways to express " ` A ` is a singleton."  See also ~ en1 , ~ en1b ,
       ~ card1 , and ~ eusn .  (Contributed by NM, 2-Aug-2010.) $)
    uniintsn $p |- ( U. A = |^| A <-> E. x A = { x } ) $=
      cA cuni cA cint wceq cA vx cv csn wceq vx wex cA cuni cA cint wceq vx cv
      cA wcel vx wex vx cv cA wcel vy cv cA wcel wa vx cv vy cv wceq wi vy wal
      vx wal wa cA vx cv csn wceq vx wex cA cuni cA cint wceq vx cv cA wcel vx
      wex vx cv cA wcel vy cv cA wcel wa vx cv vy cv wceq wi vy wal vx wal cA
      cuni cA cint wceq cA c0 wne vx cv cA wcel vx wex cA cuni cA cint wceq cvv
      c0 wne cA c0 wne vn0 cA cuni cA cint wceq cA c0 cvv c0 cA cuni cA cint
      wceq cA c0 wceq cvv c0 wceq cA cuni cA cint wceq cA c0 wceq wa cA cint
      cvv c0 cA c0 wceq cA cint cvv wceq cA cuni cA cint wceq cA c0 wceq cA
      cint c0 cint cvv cA c0 inteq int0 syl6eq adantl cA cuni cA cint wceq cA
      c0 wceq cA cint c0 wceq cA c0 wceq cA cuni c0 wceq cA cuni cA cint wceq
      cA cint c0 wceq cA c0 wceq cA cuni c0 cuni c0 cA c0 unieq uni0 syl6eq cA
      cuni cA cint c0 eqeq1 syl5ib imp eqtr3d ex necon3d mpi vx cA n0 sylib cA
      cuni cA cint wceq vx cv cA wcel vy cv cA wcel wa vx cv vy cv wceq wi vx
      vy vx cv cA wcel vy cv cA wcel wa vx cv vy cv cpr cA wss cA cuni cA cint
      wceq vx cv vy cv wceq vx cv vy cv cA vx vex vy vex prss cA cuni cA cint
      wceq vx cv vy cv cpr cA wss vx cv vy cv wceq cA cuni cA cint wceq vx cv
      vy cv cpr cA wss wa vx cv vy cv cun vx cv vy cv cin wss vx cv vy cv cin
      vx cv vy cv cun wss wa vx cv vy cv wceq cA cuni cA cint wceq vx cv vy cv
      cpr cA wss wa vx cv vy cv cun vx cv vy cv cin wss vx cv vy cv cin vx cv
      vy cv cun wss cA cuni cA cint wceq vx cv vy cv cpr cA wss wa vx cv vy cv
      cpr cuni vx cv vy cv cpr cint vx cv vy cv cun vx cv vy cv cin cA cuni cA
      cint wceq vx cv vy cv cpr cA wss wa vx cv vy cv cpr cuni cA cint vx cv vy
      cv cpr cint cA cuni cA cint wceq vx cv vy cv cpr cA wss wa vx cv vy cv
      cpr cuni cA cuni cA cint vx cv vy cv cpr cA wss vx cv vy cv cpr cuni cA
      cuni wss cA cuni cA cint wceq vx cv vy cv cpr cA uniss adantl cA cuni cA
      cint wceq vx cv vy cv cpr cA wss simpl sseqtrd vx cv vy cv cpr cA wss cA
      cint vx cv vy cv cpr cint wss cA cuni cA cint wceq vx cv vy cv cpr cA
      intss adantl sstrd vx cv vy cv vx vex vy vex unipr vx cv vy cv vx vex vy
      vex intpr 3sstr3g vx cv vy cv cin vx cv vx cv vy cv cun vx cv vy cv inss1
      vx cv vy cv ssun1 sstri jctir vx cv vy cv cun vx cv vy cv cin wss vx cv
      vy cv cin vx cv vy cv cun wss wa vx cv vy cv cun vx cv vy cv cin wceq vx
      cv vy cv wceq vx cv vy cv cun vx cv vy cv cin eqss vx cv vy cv uneqin
      bitr3i sylib ex syl5bi alrimivv jca vx cv cA wcel vx weu vx cv cA wcel vx
      cab vx cv csn wceq vx wex vx cv cA wcel vx wex vx cv cA wcel vy cv cA
      wcel wa vx cv vy cv wceq wi vy wal vx wal wa cA vx cv csn wceq vx wex vx
      cv cA wcel vx euabsn vx cv cA wcel vy cv cA wcel vx vy vx cv vy cv cA
      eleq1 eu4 vx cv cA wcel vx cab vx cv csn wceq cA vx cv csn wceq vx vx cv
      cA wcel vx cab cA vx cv csn vx cA abid2 eqeq1i exbii 3bitr3i sylib cA vx
      cv csn wceq cA cuni cA cint wceq vx cA vx cv csn wceq vx cv csn cuni vx
      cv cA cuni cA cint vx cv vx vex unisn cA vx cv csn unieq cA vx cv csn
      wceq cA cint vx cv csn cint vx cv cA vx cv csn inteq vx cv vx vex intsn
      syl6eq 3eqtr4a exlimiv impbii $.

    $( The union and the intersection of a class abstraction are equal exactly
       when there is a unique satisfying value of ` ph ( x ) ` .  (Contributed
       by Mario Carneiro, 24-Dec-2016.) $)
    uniintab $p |- ( E! x ph <-> U. { x | ph } = |^| { x | ph } ) $=
      wph vx weu wph vx cab vy cv csn wceq vy wex wph vx cab cuni wph vx cab
      cint wceq wph vx vy euabsn2 vy wph vx cab uniintsn bitr4i $.
  $}

  ${
    intunsn.1 $e |- B e. _V $.
    $( Theorem joining a singleton to an intersection.  (Contributed by NM,
       29-Sep-2002.) $)
    intunsn $p |- |^| ( A u. { B } ) = ( |^| A i^i B ) $=
      cA cB csn cun cint cA cint cB csn cint cin cA cint cB cin cA cB csn intun
      cB csn cint cB cA cint cB intunsn.1 intsn ineq2i eqtri $.
  $}

  $( Relative intersection of an empty set.  (Contributed by Stefan O'Rear,
     3-Apr-2015.) $)
  rint0 $p |- ( X = (/) -> ( A i^i |^| X ) = A ) $=
    cX c0 wceq cA cX cint cin cA c0 cint cin cA cX c0 wceq cX cint c0 cint cA
    cX c0 inteq ineq2d cA c0 cint cin cA cvv cin cA c0 cint cvv cA int0 ineq2i
    cA inv1 eqtri syl6eq $.

  ${
    $d B y $.  $d X y $.
    $( Membership in a restricted intersection.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) $)
    elrint $p |- ( X e. ( A i^i |^| B ) <-> ( X e. A /\ A. y e. B X e. y ) ) $=
      cX cA cB cint cin wcel cX cA wcel cX cB cint wcel wa cX cA wcel cX vy cv
      wcel vy cB wral wa cX cA cB cint elin cX cA wcel cX cB cint wcel cX vy cv
      wcel vy cB wral vy cX cB cA elintg pm5.32i bitri $.

    $( Membership in a restricted intersection.  (Contributed by Stefan O'Rear,
       3-Apr-2015.) $)
    elrint2 $p |- ( X e. A -> ( X e. ( A i^i |^| B ) <->
          A. y e. B X e. y ) ) $=
      cX cA cB cint cin wcel cX cA wcel cX vy cv wcel vy cB wral vy cA cB cX
      elrint baib $.
  $}


