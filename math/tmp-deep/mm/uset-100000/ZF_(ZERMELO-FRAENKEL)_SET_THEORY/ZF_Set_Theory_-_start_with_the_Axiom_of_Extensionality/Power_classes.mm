
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/_Weak_deduction_theorem__for_set_theory.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                          Power classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the symbol for power class. $)
  $c ~P $.  $( Calligraphic P $)

  $( Extend class notation to include power class.  (The tilde in the Metamath
     token is meant to suggest the calligraphic font of the P.) $)
  cpw $a class ~P A $.

  ${
    $d x A $.  $d y A $.  $d w x $.  $d w y $.  $d w A $.  $d w z $.  $d z x $.
    $d z y $.  $d z A $.
    $( Soundness justification theorem for ~ df-pw .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    pwjust $p |- { x | x C_ A } = { y | y C_ A } $=
      vx cv cA wss vx cab vz cv cA wss vz cab vy cv cA wss vy cab vx cv cA wss
      vz cv cA wss vx vz vx cv vz cv cA sseq1 cbvabv vz cv cA wss vy cv cA wss
      vz vy vz cv vy cv cA sseq1 cbvabv eqtri $.
  $}

  ${
    $d x A $.
    $( Define power class.  Definition 5.10 of [TakeutiZaring] p. 17, but we
       also let it apply to proper classes, i.e. those that are not members of
       ` _V ` .  When applied to a set, this produces its power set.  A power
       set of S is the set of all subsets of S, including the empty set and S
       itself.  For example, if ` A = { 3 , 5 , 7 } ` , then
       ` ~P A = { (/) , { 3 } , { 5 } , { 7 } , { 3 , 5 } , `
       ` { 3 , 7 } , { 5 , 7 } , { 3 , 5 , 7 } } ` ( ~ ex-pw ).  We will later
       introduce the Axiom of Power Sets ~ ax-pow , which can be expressed in
       class notation per ~ pwexg .  Still later we will prove, in ~ hashpw ,
       that the size of the power set of a finite set is 2 raised to the power
       of the size of the set.  (Contributed by NM, 5-Aug-1993.) $)
    df-pw $a |- ~P A = { x | x C_ A } $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Equality theorem for power class.  (Contributed by NM, 5-Aug-1993.) $)
    pweq $p |- ( A = B -> ~P A = ~P B ) $=
      cA cB wceq vx cv cA wss vx cab vx cv cB wss vx cab cA cpw cB cpw cA cB
      wceq vx cv cA wss vx cv cB wss vx cA cB vx cv sseq2 abbidv vx cA df-pw vx
      cB df-pw 3eqtr4g $.
  $}

  ${
    pweqi.1 $e |- A = B $.
    $( Equality inference for power class.  (Contributed by NM,
       27-Nov-2013.) $)
    pweqi $p |- ~P A = ~P B $=
      cA cB wceq cA cpw cB cpw wceq pweqi.1 cA cB pweq ax-mp $.
  $}

  ${
    pweqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for power class.  (Contributed by NM,
       27-Nov-2013.) $)
    pweqd $p |- ( ph -> ~P A = ~P B ) $=
      wph cA cB wceq cA cpw cB cpw wceq pweqd.1 cA cB pweq syl $.
  $}

  ${
    $d A x $.  $d B x $.
    ${
      elpw.1 $e |- A e. _V $.
      $( Membership in a power class.  Theorem 86 of [Suppes] p. 47.
         (Contributed by NM, 31-Dec-1993.) $)
      elpw $p |- ( A e. ~P B <-> A C_ B ) $=
        vx cv cB wss cA cB wss vx cA cB cpw elpw.1 vx cv cA cB sseq1 vx cB
        df-pw elab2 $.
    $}

    $( Membership in a power class.  Theorem 86 of [Suppes] p. 47.  See also
       ~ elpw2g .  (Contributed by NM, 6-Aug-2000.) $)
    elpwg $p |- ( A e. V -> ( A e. ~P B <-> A C_ B ) ) $=
      vx cv cB cpw wcel vx cv cB wss cA cB cpw wcel cA cB wss vx cA cV vx cv cA
      cB cpw eleq1 vx cv cA cB sseq1 vx cv cB vx vex elpw vtoclbg $.
  $}

  $( Subset relation implied by membership in a power class.  (Contributed by
     NM, 17-Feb-2007.) $)
  elpwi $p |- ( A e. ~P B -> A C_ B ) $=
    cA cB cpw wcel cA cB wss cA cB cB cpw elpwg ibi $.

  ${
    elpwid.1 $e |- ( ph -> A e. ~P B ) $.
    $( An element of a power class is a subclass.  Deduction form of ~ elpwi .
       (Contributed by David Moews, 1-May-2017.) $)
    elpwid $p |- ( ph -> A C_ B ) $=
      wph cA cB cpw wcel cA cB wss elpwid.1 cA cB elpwi syl $.
  $}

  $( If ` A ` belongs to a part of ` C ` then ` A ` belongs to ` C ` .
     (Contributed by FL, 3-Aug-2009.) $)
  elelpwi $p |- ( ( A e. B /\ B e. ~P C ) -> A e. C ) $=
    cB cC cpw wcel cA cB wcel cA cC wcel cB cC cpw wcel cB cC cA cB cC elpwi
    sseld impcom $.

  ${
    $d y z A $.  $d x y z $.
    nfpw.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for power class.  (Contributed by NM,
       28-Oct-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)
    nfpw $p |- F/_ x ~P A $=
      vx cA cpw vy cv cA wss vy cab vy cA df-pw vy cv cA wss vx vy vx vy cv cA
      vx vy cv nfcv nfpw.1 nfss nfab nfcxfr $.
  $}

  $( Membership of the original in a power set.  (Contributed by Stefan O'Rear,
     1-Feb-2015.) $)
  pwidg $p |- ( A e. V -> A e. ~P A ) $=
    cA cV wcel cA cA cpw wcel cA cA wss cA ssid cA cA cV elpwg mpbiri $.

  ${
    pwid.1 $e |- A e. _V $.
    $( A set is a member of its power class.  Theorem 87 of [Suppes] p. 47.
       (Contributed by NM, 5-Aug-1993.) $)
    pwid $p |- A e. ~P A $=
      cA cvv wcel cA cA cpw wcel pwid.1 cA cvv pwidg ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Subclass relationship for power class.  (Contributed by NM,
       21-Jun-2009.) $)
    pwss $p |- ( ~P A C_ B <-> A. x ( x C_ A -> x e. B ) ) $=
      cA cpw cB wss vx cv cA cpw wcel vx cv cB wcel wi vx wal vx cv cA wss vx
      cv cB wcel wi vx wal vx cA cpw cB dfss2 vx cv cA cpw wcel vx cv cB wcel
      wi vx cv cA wss vx cv cB wcel wi vx vx cv cA cpw wcel vx cv cA wss vx cv
      cB wcel vx cv cA wss vx cA cpw vx cA df-pw abeq2i imbi1i albii bitri $.
  $}



