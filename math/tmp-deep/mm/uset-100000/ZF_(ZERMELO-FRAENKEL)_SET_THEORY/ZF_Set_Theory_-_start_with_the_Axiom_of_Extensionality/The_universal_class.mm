
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Restricted_quantification.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The universal class

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare the symbol for the universal class. $)
  $c _V $. $( Letter V (for the universal class) $)

  $( Extend class notation to include the universal class symbol. $)
  cvv $a class _V $.

  ${
    $d z x $.  $d z y $.
    $( Soundness justification theorem for ~ df-v .  (Contributed by Rodolfo
       Medina, 27-Apr-2010.) $)
    vjust $p |- { x | x = x } = { y | y = y } $=
      vz vx cv vx cv wceq vx cab vy cv vy cv wceq vy cab vx cv vx cv wceq vx vz
      wsb vy cv vy cv wceq vy vz wsb vz cv vx cv vx cv wceq vx cab wcel vz cv
      vy cv vy cv wceq vy cab wcel vx cv vx cv wceq vx vz wsb vy cv vy cv wceq
      vy vz wsb vx cv vx cv wceq vx vz vx equid sbt vy cv vy cv wceq vy vz vy
      equid sbt 2th vx cv vx cv wceq vz vx df-clab vy cv vy cv wceq vz vy
      df-clab 3bitr4i eqriv $.
  $}

  $( Define the universal class.  Definition 5.20 of [TakeutiZaring] p. 21.
     Also Definition 2.9 of [Quine] p. 19.  (Contributed by NM, 5-Aug-1993.) $)
  df-v $a |- _V = { x | x = x } $.

  $( All set variables are sets (see ~ isset ).  Theorem 6.8 of [Quine] p. 43.
     (Contributed by NM, 5-Aug-1993.) $)
  vex $p |- x e. _V $=
    vx cv cvv wcel vx cv vx cv wceq vx cv eqid vx cv vx cv wceq vx cvv vx df-v
    abeq2i mpbir $.

  ${
    $d x A $.
    $( Two ways to say " ` A ` is a set":  A class ` A ` is a member of the
       universal class ` _V ` (see ~ df-v ) if and only if the class ` A `
       exists (i.e. there exists some set ` x ` equal to class ` A ` ).
       Theorem 6.9 of [Quine] p. 43. _Notational convention_:  We will use the
       notational device " ` A e. _V ` " to mean " ` A ` is a set" very
       frequently, for example in ~ uniex .  Note the when ` A ` is not a set,
       it is called a proper class.  In some theorems, such as ~ uniexg , in
       order to shorten certain proofs we use the more general antecedent
       ` A e. V ` instead of ` A e. _V ` to mean " ` A ` is a set."

       Note that a constant is implicitly considered distinct from all
       variables.  This is why ` _V ` is not included in the distinct variable
       list, even though ~ df-clel requires that the expression substituted for
       ` B ` not contain ` x ` .  (Also, the Metamath spec does not allow
       constants in the distinct variable list.)  (Contributed by NM,
       5-Aug-1993.) $)
    isset $p |- ( A e. _V <-> E. x x = A ) $=
      cA cvv wcel vx cv cA wceq vx cv cvv wcel wa vx wex vx cv cA wceq vx wex
      vx cA cvv df-clel vx cv cA wceq vx cv cA wceq vx cv cvv wcel wa vx vx cv
      cvv wcel vx cv cA wceq vx vex biantru exbii bitr4i $.
  $}

  ${
    $d A y $.  $d x y $.
    issetf.1 $e |- F/_ x A $.
    $( A version of isset that does not require x and A to be distinct.
       (Contributed by Andrew Salmon, 6-Jun-2011.)  (Revised by Mario Carneiro,
       10-Oct-2016.) $)
    issetf $p |- ( A e. _V <-> E. x x = A ) $=
      cA cvv wcel vy cv cA wceq vy wex vx cv cA wceq vx wex vy cA isset vy cv
      cA wceq vx cv cA wceq vy vx vx vy cv cA issetf.1 nfeq2 vx cv cA wceq vy
      nfv vy cv vx cv cA eqeq1 cbvex bitri $.
  $}

  ${
    $d x A $.
    isseti.1 $e |- A e. _V $.
    $( A way to say " ` A ` is a set" (inference rule).  (Contributed by NM,
       5-Aug-1993.) $)
    isseti $p |- E. x x = A $=
      cA cvv wcel vx cv cA wceq vx wex isseti.1 vx cA isset mpbi $.
  $}

  ${
    $d x A $.
    issetri.1 $e |- E. x x = A $.
    $( A way to say " ` A ` is a set" (inference rule).  (Contributed by NM,
       5-Aug-1993.) $)
    issetri $p |- A e. _V $=
      cA cvv wcel vx cv cA wceq vx wex issetri.1 vx cA isset mpbir $.
  $}

  ${
    $d x A $.  $d x B $.
    $( If a class is a member of another class, it is a set.  Theorem 6.12 of
       [Quine] p. 44.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by
       Andrew Salmon, 8-Jun-2011.) $)
    elex $p |- ( A e. B -> A e. _V ) $=
      vx cv cA wceq vx cv cB wcel wa vx wex vx cv cA wceq vx wex cA cB wcel cA
      cvv wcel vx cv cA wceq vx cv cB wcel vx exsimpl vx cA cB df-clel vx cA
      isset 3imtr4i $.
  $}

  ${
    elisseti.1 $e |- A e. B $.
    $( If a class is a member of another class, it is a set.  (Contributed by
       NM, 11-Jun-1994.) $)
    elexi $p |- A e. _V $=
      cA cB wcel cA cvv wcel elisseti.1 cA cB elex ax-mp $.
  $}

  ${
    $d x A $.
    $( An element of a class exists.  (Contributed by NM, 1-May-1995.) $)
    elisset $p |- ( A e. V -> E. x x = A ) $=
      cA cV wcel cA cvv wcel vx cv cA wceq vx wex cA cV elex vx cA isset sylib
      $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( If two classes each contain another class, then both contain some set.
       (Contributed by Alan Sare, 24-Oct-2011.) $)
    elex22 $p |- ( ( A e. B /\ A e. C ) -> E. x ( x e. B /\ x e. C ) ) $=
      cA cB wcel cA cC wcel wa vx cv cA wceq vx cv cB wcel vx cv cC wcel wa wi
      vx wal vx cv cA wceq vx wex vx cv cB wcel vx cv cC wcel wa vx wex cA cB
      wcel cA cC wcel wa vx cv cA wceq vx cv cB wcel vx cv cC wcel wa wi vx cA
      cB wcel vx cv cA wceq vx cv cB wcel cA cC wcel vx cv cC wcel cA cB vx cv
      eleq1a cA cC vx cv eleq1a anim12ii alrimiv cA cB wcel vx cv cA wceq vx
      wex cA cC wcel vx cA cB elisset adantr vx cv cA wceq vx cv cB wcel vx cv
      cC wcel wa vx exim sylc $.
  $}

  ${
    $d x A $.  $d x B $.
    $( If a class contains another class, then it contains some set.
       (Contributed by Alan Sare, 25-Sep-2011.) $)
    elex2 $p |- ( A e. B -> E. x x e. B ) $=
      cA cB wcel vx cv cA wceq vx cv cB wcel wi vx wal vx cv cA wceq vx wex vx
      cv cB wcel vx wex cA cB wcel vx cv cA wceq vx cv cB wcel wi vx cA cB vx
      cv eleq1a alrimiv vx cA cB elisset vx cv cA wceq vx cv cB wcel vx exim
      sylc $.
  $}

  $( A universal quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 26-Mar-2004.) $)
  ralv $p |- ( A. x e. _V ph <-> A. x ph ) $=
    wph vx cvv wral vx cv cvv wcel wph wi vx wal wph vx wal wph vx cvv df-ral
    wph vx cv cvv wcel wph wi vx vx cv cvv wcel wph vx vex a1bi albii bitr4i $.

  $( An existential quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 26-Mar-2004.) $)
  rexv $p |- ( E. x e. _V ph <-> E. x ph ) $=
    wph vx cvv wrex vx cv cvv wcel wph wa vx wex wph vx wex wph vx cvv df-rex
    wph vx cv cvv wcel wph wa vx vx cv cvv wcel wph vx vex biantrur exbii
    bitr4i $.

  $( A uniqueness quantifier restricted to the universe is unrestricted.
     (Contributed by NM, 1-Nov-2010.) $)
  reuv $p |- ( E! x e. _V ph <-> E! x ph ) $=
    wph vx cvv wreu vx cv cvv wcel wph wa vx weu wph vx weu wph vx cvv df-reu
    wph vx cv cvv wcel wph wa vx vx cv cvv wcel wph vx vex biantrur eubii
    bitr4i $.

  $( A uniqueness quantifier restricted to the universe is unrestricted.
     (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
  rmov $p |- ( E* x e. _V ph <-> E* x ph ) $=
    wph vx cvv wrmo vx cv cvv wcel wph wa vx wmo wph vx wmo wph vx cvv df-rmo
    wph vx cv cvv wcel wph wa vx vx cv cvv wcel wph vx vex biantrur mobii
    bitr4i $.

  $( A class abstraction restricted to the universe is unrestricted.
     (Contributed by NM, 27-Dec-2004.)  (Proof shortened by Andrew Salmon,
     8-Jun-2011.) $)
  rabab $p |- { x e. _V | ph } = { x | ph } $=
    wph vx cvv crab vx cv cvv wcel wph wa vx cab wph vx cab wph vx cvv df-rab
    wph vx cv cvv wcel wph wa vx vx cv cvv wcel wph vx vex biantrur abbii
    eqtr4i $.

  ${
    $d x y $.  $d y A $.
    $( Commutation of restricted and unrestricted universal quantifiers.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
    ralcom4 $p |- ( A. x e. A A. y ph <-> A. y A. x e. A ph ) $=
      wph vy cvv wral vx cA wral wph vx cA wral vy cvv wral wph vy wal vx cA
      wral wph vx cA wral vy wal wph vx vy cA cvv ralcom wph vy cvv wral wph vy
      wal vx cA wph vy ralv ralbii wph vx cA wral vy ralv 3bitr3i $.

    $( Commutation of restricted and unrestricted existential quantifiers.
       (Contributed by NM, 12-Apr-2004.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
    rexcom4 $p |- ( E. x e. A E. y ph <-> E. y E. x e. A ph ) $=
      wph vy cvv wrex vx cA wrex wph vx cA wrex vy cvv wrex wph vy wex vx cA
      wrex wph vx cA wrex vy wex wph vx vy cA cvv rexcom wph vy cvv wrex wph vy
      wex vx cA wph vy rexv rexbii wph vx cA wrex vy rexv 3bitr3i $.
  $}

  ${
    $d A x $.  $d x y $.  $d ph x $.
    $( Specialized existential commutation lemma.  (Contributed by Jeff Madsen,
       1-Jun-2011.) $)
    rexcom4a $p |- ( E. x E. y e. A ( ph /\ ps )
                          <-> E. y e. A ( ph /\ E. x ps ) ) $=
      wph wps wa vy cA wrex vx wex wph wps wa vx wex vy cA wrex wph wps vx wex
      wa vy cA wrex wph wps wa vy vx cA rexcom4 wph wps wa vx wex wph wps vx
      wex wa vy cA wph wps vx 19.42v rexbii bitr3i $.

    $d B x $.
    rexcom4b.1 $e |- B e. _V $.
    $( Specialized existential commutation lemma.  (Contributed by Jeff Madsen,
       1-Jun-2011.) $)
    rexcom4b $p |- ( E. x E. y e. A ( ph /\ x = B ) <-> E. y e. A ph ) $=
      wph vx cv cB wceq wa vy cA wrex vx wex wph vx cv cB wceq vx wex wa vy cA
      wrex wph vy cA wrex wph vx cv cB wceq vx vy cA rexcom4a wph wph vx cv cB
      wceq vx wex wa vy cA vx cv cB wceq vx wex wph vx cB rexcom4b.1 isseti
      biantru rexbii bitr4i $.
  $}

  ${
    $d x A $.
    $( Closed theorem version of ~ ceqsalg .  (Contributed by NM,
       28-Feb-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
    ceqsalt $p |- ( ( F/ x ps /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. V )
         -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      wps vx wnf vx cv cA wceq wph wps wb wi vx wal cA cV wcel w3a vx cv cA
      wceq wph wi vx wal wps wps vx wnf vx cv cA wceq wph wps wb wi vx wal cA
      cV wcel w3a vx cv cA wceq wph wi vx wal vx cv cA wceq vx wex wps cA cV
      wcel wps vx wnf vx cv cA wceq vx wex vx cv cA wceq wph wps wb wi vx wal
      vx cA cV elisset 3ad2ant3 wps vx wnf vx cv cA wceq wph wps wb wi vx wal
      cA cV wcel w3a vx cv cA wceq wph wi vx wal vx cv cA wceq wps wi vx wal vx
      cv cA wceq vx wex wps wi vx cv cA wceq wph wps wb wi vx wal wps vx wnf vx
      cv cA wceq wph wi vx wal vx cv cA wceq wps wi vx wal wi cA cV wcel vx cv
      cA wceq wph wps wb wi vx cv cA wceq wph wi vx cv cA wceq wps wi vx wph
      wps wb wph wps vx cv cA wceq wph wps bi1 imim3i al2imi 3ad2ant2 wps vx
      wnf vx cv cA wceq wph wps wb wi vx wal vx cv cA wceq wps wi vx wal vx cv
      cA wceq vx wex wps wi wb cA cV wcel vx cv cA wceq wps vx 19.23t 3ad2ant1
      sylibd mpid wps vx wnf vx cv cA wceq wph wps wb wi vx wal cA cV wcel w3a
      wps vx cv cA wceq wph wi wi vx wal wps vx cv cA wceq wph wi vx wal wi vx
      cv cA wceq wph wps wb wi vx wal wps vx wnf wps vx cv cA wceq wph wi wi vx
      wal cA cV wcel vx cv cA wceq wph wps wb wi wps vx cv cA wceq wph wi wi vx
      vx cv cA wceq wph wps wb wi vx cv cA wceq wps wph wph wps wb wps wph wi
      vx cv cA wceq wph wps bi2 imim2i com23 alimi 3ad2ant2 wps vx wnf vx cv cA
      wceq wph wps wb wi vx wal wps vx cv cA wceq wph wi wi vx wal wps vx cv cA
      wceq wph wi vx wal wi wb cA cV wcel wps vx cv cA wceq wph wi vx 19.21t
      3ad2ant1 mpbid impbid $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Restricted quantifier version of ~ ceqsalt .  (Contributed by NM,
       28-Feb-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
    ceqsralt $p |- ( ( F/ x ps
              /\ A. x ( x = A -> ( ph <-> ps ) ) /\ A e. B )
         -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $=
      wps vx wnf vx cv cA wceq wph wps wb wi vx wal cA cB wcel w3a vx cv cA
      wceq wph wi vx cB wral cA cB wcel vx cv cA wceq wph wi vx wal wi vx cv cA
      wceq wph wi vx wal wps wps vx wnf vx cv cA wceq wph wps wb wi vx wal cA
      cB wcel w3a vx cv cA wceq wph wi vx cB wral cA cB wcel vx cv cA wceq wph
      wi wi vx wal cA cB wcel vx cv cA wceq wph wi vx wal wi vx cv cA wceq wph
      wi vx cB wral vx cv cB wcel vx cv cA wceq wph wi wi vx wal wps vx wnf vx
      cv cA wceq wph wps wb wi vx wal cA cB wcel w3a cA cB wcel vx cv cA wceq
      wph wi wi vx wal vx cv cA wceq wph wi vx cB df-ral vx cv cB wcel vx cv cA
      wceq wph wi wi vx wal cA cB wcel vx cv cA wceq wph wi wi vx wal wb wps vx
      wnf vx cv cA wceq wph wps wb wi vx wal cA cB wcel w3a vx cv cB wcel vx cv
      cA wceq wph wi wi cA cB wcel vx cv cA wceq wph wi wi vx vx cv cB wcel vx
      cv cA wceq wa wph wi cA cB wcel vx cv cA wceq wa wph wi vx cv cB wcel vx
      cv cA wceq wph wi wi cA cB wcel vx cv cA wceq wph wi wi vx cv cB wcel vx
      cv cA wceq wa cA cB wcel vx cv cA wceq wa wph vx cv cA wceq vx cv cB wcel
      cA cB wcel vx cv cA cB eleq1 pm5.32ri imbi1i vx cv cB wcel vx cv cA wceq
      wph impexp cA cB wcel vx cv cA wceq wph impexp 3bitr3i albii a1i syl5bb
      cA cB wcel vx cv cA wceq wph wi vx 19.21v syl6bb cA cB wcel wps vx wnf vx
      cv cA wceq wph wi vx wal cA cB wcel vx cv cA wceq wph wi vx wal wi wb vx
      cv cA wceq wph wps wb wi vx wal cA cB wcel vx cv cA wceq wph wi vx wal
      biimt 3ad2ant3 wph wps vx cA cB ceqsalt 3bitr2d $.
  $}

  ${
    $d x A $.
    ceqsalg.1 $e |- F/ x ps $.
    ceqsalg.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       29-Oct-2003.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    ceqsalg $p |- ( A e. V -> ( A. x ( x = A -> ph ) <-> ps ) ) $=
      cA cV wcel vx cv cA wceq wph wi vx wal wps cA cV wcel vx cv cA wceq vx
      wex vx cv cA wceq wph wi vx wal wps vx cA cV elisset vx cv cA wceq wph wi
      vx wal vx cv cA wceq wps vx vx cv cA wceq wph wi vx nfa1 ceqsalg.1 vx cv
      cA wceq wph wi vx cv cA wceq wps wi vx vx cv cA wceq wph wps vx cv cA
      wceq wph wps ceqsalg.2 biimpd a2i sps exlimd syl5com wps vx cv cA wceq
      wph wi vx ceqsalg.1 vx cv cA wceq wph wps ceqsalg.2 biimprcd alrimi
      impbid1 $.
  $}

  ${
    $d x A $.
    ceqsal.1 $e |- F/ x ps $.
    ceqsal.2 $e |- A e. _V $.
    ceqsal.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       18-Aug-1993.) $)
    ceqsal $p |- ( A. x ( x = A -> ph ) <-> ps ) $=
      cA cvv wcel vx cv cA wceq wph wi vx wal wps wb ceqsal.2 wph wps vx cA cvv
      ceqsal.1 ceqsal.3 ceqsalg ax-mp $.
  $}

  ${
    $d x A $.  $d x ps $.
    ceqsalv.1 $e |- A e. _V $.
    ceqsalv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       18-Aug-1993.) $)
    ceqsalv $p |- ( A. x ( x = A -> ph ) <-> ps ) $=
      wph wps vx cA wps vx nfv ceqsalv.1 ceqsalv.2 ceqsal $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    ceqsralv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Restricted quantifier version of ~ ceqsalv .  (Contributed by NM,
       21-Jun-2013.) $)
    ceqsralv $p |- ( A e. B -> ( A. x e. B ( x = A -> ph ) <-> ps ) ) $=
      wps vx wnf vx cv cA wceq wph wps wb wi vx wal cA cB wcel vx cv cA wceq
      wph wi vx cB wral wps wb wps vx nfv vx cv cA wceq wph wps wb wi vx
      ceqsralv.2 ax-gen wph wps vx cA cB ceqsralt mp3an12 $.
  $}

  ${
    $d x ps $.
    gencl.1 $e |- ( th <-> E. x ( ch /\ A = B ) ) $.
    gencl.2 $e |- ( A = B -> ( ph <-> ps ) ) $.
    gencl.3 $e |- ( ch -> ph ) $.
    $( Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)
    gencl $p |- ( th -> ps ) $=
      wth wch cA cB wceq wa vx wex wps gencl.1 wch cA cB wceq wa wps vx cA cB
      wceq wch wps wch wph cA cB wceq wps gencl.3 gencl.2 syl5ib impcom exlimiv
      sylbi $.
  $}

  ${
    $d x y $.  $d x R $.  $d x ps $.  $d y C $.  $d y S $.  $d y ch $.
    2gencl.1 $e |- ( C e. S <-> E. x e. R A = C ) $.
    2gencl.2 $e |- ( D e. S <-> E. y e. R B = D ) $.
    2gencl.3 $e |- ( A = C -> ( ph <-> ps ) ) $.
    2gencl.4 $e |- ( B = D -> ( ps <-> ch ) ) $.
    2gencl.5 $e |- ( ( x e. R /\ y e. R ) -> ph ) $.
    $( Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)
    2gencl $p |- ( ( C e. S /\ D e. S ) -> ch ) $=
      cD cS wcel cC cS wcel wch cC cS wcel wps wi cC cS wcel wch wi vy cv cR
      wcel cD cS wcel vy cB cD cD cS wcel cB cD wceq vy cR wrex vy cv cR wcel
      cB cD wceq wa vy wex 2gencl.2 cB cD wceq vy cR df-rex bitri cB cD wceq
      wps wch cC cS wcel 2gencl.4 imbi2d cC cS wcel vy cv cR wcel wps vy cv cR
      wcel wph wi vy cv cR wcel wps wi vx cv cR wcel cC cS wcel vx cA cC cC cS
      wcel cA cC wceq vx cR wrex vx cv cR wcel cA cC wceq wa vx wex 2gencl.1 cA
      cC wceq vx cR df-rex bitri cA cC wceq wph wps vy cv cR wcel 2gencl.3
      imbi2d vx cv cR wcel vy cv cR wcel wph 2gencl.5 ex gencl com12 gencl
      impcom $.
  $}

  ${
    $d x y z $.  $d y z D $.  $d z F $.  $d x y R $.  $d y z S $.  $d x ps $.
    $d y ch $.  $d z th $.
    3gencl.1 $e |- ( D e. S <-> E. x e. R A = D ) $.
    3gencl.2 $e |- ( F e. S <-> E. y e. R B = F ) $.
    3gencl.3 $e |- ( G e. S <-> E. z e. R C = G ) $.
    3gencl.4 $e |- ( A = D -> ( ph <-> ps ) ) $.
    3gencl.5 $e |- ( B = F -> ( ps <-> ch ) ) $.
    3gencl.6 $e |- ( C = G -> ( ch <-> th ) ) $.
    3gencl.7 $e |- ( ( x e. R /\ y e. R /\ z e. R ) -> ph ) $.
    $( Implicit substitution for class with embedded variable.  (Contributed by
       NM, 17-May-1996.) $)
    3gencl $p |- ( ( D e. S /\ F e. S /\ G e. S ) -> th ) $=
      cD cS wcel cF cS wcel cG cS wcel wth cG cS wcel cD cS wcel cF cS wcel wa
      wth cD cS wcel cF cS wcel wa wch wi cD cS wcel cF cS wcel wa wth wi vz cv
      cR wcel cG cS wcel vz cC cG cG cS wcel cC cG wceq vz cR wrex vz cv cR
      wcel cC cG wceq wa vz wex 3gencl.3 cC cG wceq vz cR df-rex bitri cC cG
      wceq wch wth cD cS wcel cF cS wcel wa 3gencl.6 imbi2d cD cS wcel cF cS
      wcel wa vz cv cR wcel wch vz cv cR wcel wph wi vz cv cR wcel wps wi vz cv
      cR wcel wch wi vx vy cA cB cD cF cR cS 3gencl.1 3gencl.2 cA cD wceq wph
      wps vz cv cR wcel 3gencl.4 imbi2d cB cF wceq wps wch vz cv cR wcel
      3gencl.5 imbi2d vx cv cR wcel vy cv cR wcel vz cv cR wcel wph 3gencl.7
      3expia 2gencl com12 gencl com12 3impia $.
  $}

  ${
    $d x A $.  $d x ps $.
    cgsexg.1 $e |- ( x = A -> ch ) $.
    cgsexg.2 $e |- ( ch -> ( ph <-> ps ) ) $.
    $( Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Aug-2007.) $)
    cgsexg $p |- ( A e. V ->
                     ( E. x ( ch /\ ph ) <-> ps ) ) $=
      cA cV wcel wch wph wa vx wex wps wch wph wa wps vx wch wph wps cgsexg.2
      biimpa exlimiv cA cV wcel wch vx wex wps wch wph wa vx wex cA cV wcel vx
      cv cA wceq vx wex wch vx wex vx cA cV elisset vx cv cA wceq wch vx
      cgsexg.1 eximi syl wps wch wch wph wa vx wps wch wph wch wph wps cgsexg.2
      biimprcd ancld eximdv syl5com impbid2 $.
  $}

  ${
    $d x y ps $.  $d x y A $.  $d x y B $.
    cgsex2g.1 $e |- ( ( x = A /\ y = B ) -> ch ) $.
    cgsex2g.2 $e |- ( ch -> ( ph <-> ps ) ) $.
    $( Implicit substitution inference for general classes.  (Contributed by
       NM, 26-Jul-1995.) $)
    cgsex2g $p |- ( ( A e. V /\ B e. W ) ->
                     ( E. x E. y ( ch /\ ph ) <-> ps ) ) $=
      cA cV wcel cB cW wcel wa wch wph wa vy wex vx wex wps wch wph wa wps vx
      vy wch wph wps cgsex2g.2 biimpa exlimivv cA cV wcel cB cW wcel wa wch vy
      wex vx wex wps wch wph wa vy wex vx wex cA cV wcel cB cW wcel wa vx cv cA
      wceq vy cv cB wceq wa vy wex vx wex wch vy wex vx wex cA cV wcel cB cW
      wcel wa vx cv cA wceq vx wex vy cv cB wceq vy wex wa vx cv cA wceq vy cv
      cB wceq wa vy wex vx wex cA cV wcel vx cv cA wceq vx wex cB cW wcel vy cv
      cB wceq vy wex vx cA cV elisset vy cB cW elisset anim12i vx cv cA wceq vy
      cv cB wceq vx vy eeanv sylibr vx cv cA wceq vy cv cB wceq wa wch vx vy
      cgsex2g.1 2eximi syl wps wch wch wph wa vx vy wps wch wph wch wph wps
      cgsex2g.2 biimprcd ancld 2eximdv syl5com impbid2 $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d x y z w D $.
    $d x y z w ps $.
    cgsex4g.1 $e |- ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) ) -> ch ) $.
    cgsex4g.2 $e |- ( ch -> ( ph <-> ps ) ) $.
    $( An implicit substitution inference for 4 general classes.  (Contributed
       by NM, 5-Aug-1995.) $)
    cgsex4g $p |- ( ( ( A e. R /\ B e. S ) /\ ( C e. R /\ D e. S ) ) ->
                    ( E. x E. y E. z E. w ( ch /\ ph ) <-> ps ) ) $=
      cA cR wcel cB cS wcel wa cC cR wcel cD cS wcel wa wa wch wph wa vw wex vz
      wex vy wex vx wex wps wch wph wa vw wex vz wex wps vx vy wch wph wa wps
      vz vw wch wph wps cgsex4g.2 biimpa exlimivv exlimivv cA cR wcel cB cS
      wcel wa cC cR wcel cD cS wcel wa wa wch vw wex vz wex vy wex vx wex wps
      wch wph wa vw wex vz wex vy wex vx wex cA cR wcel cB cS wcel wa cC cR
      wcel cD cS wcel wa wa vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv
      cD wceq wa wa vw wex vz wex vy wex vx wex wch vw wex vz wex vy wex vx wex
      cA cR wcel cB cS wcel wa cC cR wcel cD cS wcel wa wa vx cv cA wceq vy cv
      cB wceq wa vy wex vx wex vz cv cC wceq vw cv cD wceq wa vw wex vz wex wa
      vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vw wex
      vz wex vy wex vx wex cA cR wcel cB cS wcel wa vx cv cA wceq vy cv cB wceq
      wa vy wex vx wex cC cR wcel cD cS wcel wa vz cv cC wceq vw cv cD wceq wa
      vw wex vz wex cA cR wcel cB cS wcel wa vx cv cA wceq vx wex vy cv cB wceq
      vy wex wa vx cv cA wceq vy cv cB wceq wa vy wex vx wex cA cR wcel vx cv
      cA wceq vx wex cB cS wcel vy cv cB wceq vy wex vx cA cR elisset vy cB cS
      elisset anim12i vx cv cA wceq vy cv cB wceq vx vy eeanv sylibr cC cR wcel
      cD cS wcel wa vz cv cC wceq vz wex vw cv cD wceq vw wex wa vz cv cC wceq
      vw cv cD wceq wa vw wex vz wex cC cR wcel vz cv cC wceq vz wex cD cS wcel
      vw cv cD wceq vw wex vz cC cR elisset vw cD cS elisset anim12i vz cv cC
      wceq vw cv cD wceq vz vw eeanv sylibr anim12i vx cv cA wceq vy cv cB wceq
      wa vz cv cC wceq vw cv cD wceq wa vx vy vz vw ee4anv sylibr vx cv cA wceq
      vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vw wex vz wex wch vw
      wex vz wex vx vy vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD
      wceq wa wa wch vz vw cgsex4g.1 2eximi 2eximi syl wps wch vw wex vz wex
      wch wph wa vw wex vz wex vx vy wps wch wch wph wa vz vw wps wch wph wch
      wph wps cgsex4g.2 biimprcd ancld 2eximdv 2eximdv syl5com impbid2 $.
  $}

  ${
    $d x A $.
    ceqsex.1 $e |- F/ x ps $.
    ceqsex.2 $e |- A e. _V $.
    ceqsex.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 2-Mar-1995.)  (Revised by Mario Carneiro,
       10-Oct-2016.) $)
    ceqsex $p |- ( E. x ( x = A /\ ph ) <-> ps ) $=
      vx cv cA wceq wph wa vx wex wps vx cv cA wceq wph wa wps vx ceqsex.1 vx
      cv cA wceq wph wps ceqsex.3 biimpa exlimi wps vx cv cA wceq wph wi vx wal
      vx cv cA wceq vx wex vx cv cA wceq wph wa vx wex wps vx cv cA wceq wph wi
      vx ceqsex.1 vx cv cA wceq wph wps ceqsex.3 biimprcd alrimi vx cA ceqsex.2
      isseti vx cv cA wceq wph vx exintr ee10 impbii $.
  $}

  ${
    $d x A $.  $d x ps $.
    ceqsexv.1 $e |- A e. _V $.
    ceqsexv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 2-Mar-1995.) $)
    ceqsexv $p |- ( E. x ( x = A /\ ph ) <-> ps ) $=
      wph wps vx cA wps vx nfv ceqsexv.1 ceqsexv.2 ceqsex $.
  $}

  ${
    $d x y A $.  $d x y B $.
    ceqsex2.1 $e |- F/ x ps $.
    ceqsex2.2 $e |- F/ y ch $.
    ceqsex2.3 $e |- A e. _V $.
    ceqsex2.4 $e |- B e. _V $.
    ceqsex2.5 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsex2.6 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( Elimination of two existential quantifiers, using implicit
       substitution.  (Contributed by Scott Fenton, 7-Jun-2006.) $)
    ceqsex2 $p |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch ) $=
      vx cv cA wceq vy cv cB wceq wph w3a vy wex vx wex vx cv cA wceq vy cv cB
      wceq wph wa vy wex wa vx wex vy cv cB wceq wps wa vy wex wch vx cv cA
      wceq vy cv cB wceq wph w3a vy wex vx cv cA wceq vy cv cB wceq wph wa vy
      wex wa vx vx cv cA wceq vy cv cB wceq wph w3a vy wex vx cv cA wceq vy cv
      cB wceq wph wa wa vy wex vx cv cA wceq vy cv cB wceq wph wa vy wex wa vx
      cv cA wceq vy cv cB wceq wph w3a vx cv cA wceq vy cv cB wceq wph wa wa vy
      vx cv cA wceq vy cv cB wceq wph 3anass exbii vx cv cA wceq vy cv cB wceq
      wph wa vy 19.42v bitri exbii vy cv cB wceq wph wa vy wex vy cv cB wceq
      wps wa vy wex vx cA vy cv cB wceq wps wa vx vy vy cv cB wceq wps vx vy cv
      cB wceq vx nfv ceqsex2.1 nfan nfex ceqsex2.3 vx cv cA wceq vy cv cB wceq
      wph wa vy cv cB wceq wps wa vy vx cv cA wceq wph wps vy cv cB wceq
      ceqsex2.5 anbi2d exbidv ceqsex wps wch vy cB ceqsex2.2 ceqsex2.4
      ceqsex2.6 ceqsex 3bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x ps $.  $d y ch $.
    ceqsex2v.1 $e |- A e. _V $.
    ceqsex2v.2 $e |- B e. _V $.
    ceqsex2v.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsex2v.4 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( Elimination of two existential quantifiers, using implicit
       substitution.  (Contributed by Scott Fenton, 7-Jun-2006.) $)
    ceqsex2v $p |- ( E. x E. y ( x = A /\ y = B /\ ph ) <-> ch ) $=
      wph wps wch vx vy cA cB wps vx nfv wch vy nfv ceqsex2v.1 ceqsex2v.2
      ceqsex2v.3 ceqsex2v.4 ceqsex2 $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x ps $.  $d y ch $.
    $d z th $.
    ceqsex3v.1 $e |- A e. _V $.
    ceqsex3v.2 $e |- B e. _V $.
    ceqsex3v.3 $e |- C e. _V $.
    ceqsex3v.4 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsex3v.5 $e |- ( y = B -> ( ps <-> ch ) ) $.
    ceqsex3v.6 $e |- ( z = C -> ( ch <-> th ) ) $.
    $( Elimination of three existential quantifiers, using implicit
       substitution.  (Contributed by NM, 16-Aug-2011.) $)
    ceqsex3v $p |- ( E. x E. y E. z ( ( x = A /\ y = B /\ z = C ) /\ ph )
                 <-> th ) $=
      vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a wph wa vz wex vy wex vx wex
      vx cv cA wceq vy cv cB wceq vz cv cC wceq wph w3a vz wex vy wex wa vx wex
      wth vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a wph wa vz wex vy wex vx
      cv cA wceq vy cv cB wceq vz cv cC wceq wph w3a vz wex vy wex wa vx vx cv
      cA wceq vy cv cB wceq vz cv cC wceq w3a wph wa vz wex vy wex vx cv cA
      wceq vy cv cB wceq vz cv cC wceq wph w3a wa vz wex vy wex vx cv cA wceq
      vy cv cB wceq vz cv cC wceq wph w3a vz wex vy wex wa vx cv cA wceq vy cv
      cB wceq vz cv cC wceq w3a wph wa vx cv cA wceq vy cv cB wceq vz cv cC
      wceq wph w3a wa vy vz vx cv cA wceq vy cv cB wceq vz cv cC wceq wa wa wph
      wa vx cv cA wceq vy cv cB wceq vz cv cC wceq wa wph wa wa vx cv cA wceq
      vy cv cB wceq vz cv cC wceq w3a wph wa vx cv cA wceq vy cv cB wceq vz cv
      cC wceq wph w3a wa vx cv cA wceq vy cv cB wceq vz cv cC wceq wa wph anass
      vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vx cv cA wceq vy cv cB wceq
      vz cv cC wceq wa wa wph vx cv cA wceq vy cv cB wceq vz cv cC wceq 3anass
      anbi1i vy cv cB wceq vz cv cC wceq wph w3a vy cv cB wceq vz cv cC wceq wa
      wph wa vx cv cA wceq vy cv cB wceq vz cv cC wceq wph df-3an anbi2i
      3bitr4i 2exbii vx cv cA wceq vy cv cB wceq vz cv cC wceq wph w3a vy vz
      19.42vv bitri exbii vx cv cA wceq vy cv cB wceq vz cv cC wceq wph w3a vz
      wex vy wex wa vx wex vy cv cB wceq vz cv cC wceq wps w3a vz wex vy wex
      wth vy cv cB wceq vz cv cC wceq wph w3a vz wex vy wex vy cv cB wceq vz cv
      cC wceq wps w3a vz wex vy wex vx cA ceqsex3v.1 vx cv cA wceq vy cv cB
      wceq vz cv cC wceq wph w3a vy cv cB wceq vz cv cC wceq wps w3a vy vz vx
      cv cA wceq wph wps vy cv cB wceq vz cv cC wceq ceqsex3v.4 3anbi3d 2exbidv
      ceqsexv wps wch wth vy vz cB cC ceqsex3v.2 ceqsex3v.3 ceqsex3v.5
      ceqsex3v.6 ceqsex2v bitri bitri $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d x y z w D $.
    $d x ps $.  $d y ch $.  $d z th $.  $d w ta $.
    ceqsex4v.1 $e |- A e. _V $.
    ceqsex4v.2 $e |- B e. _V $.
    ceqsex4v.3 $e |- C e. _V $.
    ceqsex4v.4 $e |- D e. _V $.
    ceqsex4v.7 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsex4v.8 $e |- ( y = B -> ( ps <-> ch ) ) $.
    ceqsex4v.9 $e |- ( z = C -> ( ch <-> th ) ) $.
    ceqsex4v.10 $e |- ( w = D -> ( th <-> ta ) ) $.
    $( Elimination of four existential quantifiers, using implicit
       substitution.  (Contributed by NM, 23-Sep-2011.) $)
    ceqsex4v $p |- ( E. x E. y E. z E. w
          ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) /\ ph ) <-> ta ) $=
      vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wph w3a vw
      wex vz wex vy wex vx wex vx cv cA wceq vy cv cB wceq vz cv cC wceq vw cv
      cD wceq wph w3a vw wex vz wex w3a vy wex vx wex vz cv cC wceq vw cv cD
      wceq wch w3a vw wex vz wex wta vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wa wph w3a vw wex vz wex vx cv cA wceq vy cv cB wceq
      vz cv cC wceq vw cv cD wceq wph w3a vw wex vz wex w3a vx vy vx cv cA wceq
      vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wph w3a wa vw wex vz wex vx
      cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wph w3a vw wex vz
      wex wa vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wph
      w3a vw wex vz wex vx cv cA wceq vy cv cB wceq vz cv cC wceq vw cv cD wceq
      wph w3a vw wex vz wex w3a vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw
      cv cD wceq wph w3a vz vw 19.42vv vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wa wph w3a vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wph w3a wa vz vw vx cv cA wceq vy cv cB wceq wa vz cv
      cC wceq vw cv cD wceq wa wph w3a vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wa wph wa wa vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wph w3a wa vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wa wph 3anass vz cv cC wceq vw cv cD wceq wph w3a vz
      cv cC wceq vw cv cD wceq wa wph wa vx cv cA wceq vy cv cB wceq wa vz cv
      cC wceq vw cv cD wceq wph df-3an anbi2i bitr4i 2exbii vx cv cA wceq vy cv
      cB wceq vz cv cC wceq vw cv cD wceq wph w3a vw wex vz wex df-3an 3bitr4i
      2exbii vz cv cC wceq vw cv cD wceq wph w3a vw wex vz wex vz cv cC wceq vw
      cv cD wceq wps w3a vw wex vz wex vz cv cC wceq vw cv cD wceq wch w3a vw
      wex vz wex vx vy cA cB ceqsex4v.1 ceqsex4v.2 vx cv cA wceq vz cv cC wceq
      vw cv cD wceq wph w3a vz cv cC wceq vw cv cD wceq wps w3a vz vw vx cv cA
      wceq wph wps vz cv cC wceq vw cv cD wceq ceqsex4v.7 3anbi3d 2exbidv vy cv
      cB wceq vz cv cC wceq vw cv cD wceq wps w3a vz cv cC wceq vw cv cD wceq
      wch w3a vz vw vy cv cB wceq wps wch vz cv cC wceq vw cv cD wceq
      ceqsex4v.8 3anbi3d 2exbidv ceqsex2v wch wth wta vz vw cC cD ceqsex4v.3
      ceqsex4v.4 ceqsex4v.9 ceqsex4v.10 ceqsex2v 3bitri $.
  $}

  ${
    $d x y z w v u A $.  $d x y z w v u B $.  $d x y z w v u C $.
    $d x y z w v u D $.  $d x y z w v u E $.  $d x y z w v u F $.  $d x ps $.
    $d y ch $.  $d z th $.  $d w ta $.  $d v et $.  $d u ze $.
    ceqsex6v.1 $e |- A e. _V $.
    ceqsex6v.2 $e |- B e. _V $.
    ceqsex6v.3 $e |- C e. _V $.
    ceqsex6v.4 $e |- D e. _V $.
    ceqsex6v.5 $e |- E e. _V $.
    ceqsex6v.6 $e |- F e. _V $.
    ceqsex6v.7 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsex6v.8 $e |- ( y = B -> ( ps <-> ch ) ) $.
    ceqsex6v.9 $e |- ( z = C -> ( ch <-> th ) ) $.
    ceqsex6v.10 $e |- ( w = D -> ( th <-> ta ) ) $.
    ceqsex6v.11 $e |- ( v = E -> ( ta <-> et ) ) $.
    ceqsex6v.12 $e |- ( u = F -> ( et <-> ze ) ) $.
    $( Elimination of six existential quantifiers, using implicit
       substitution.  (Contributed by NM, 21-Sep-2011.) $)
    ceqsex6v $p |- ( E. x E. y E. z E. w E. v E. u
          ( ( x = A /\ y = B /\ z = C ) /\ ( w = D /\ v = E /\ u = F ) /\ ph )
                 <-> ze ) $=
      vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq
      vu cv cF wceq w3a wph w3a vu wex vv wex vw wex vz wex vy wex vx wex vx cv
      cA wceq vy cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv
      cF wceq w3a wph wa vu wex vv wex vw wex wa vz wex vy wex vx wex wze vx cv
      cA wceq vy cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv
      cF wceq w3a wph w3a vu wex vv wex vw wex vx cv cA wceq vy cv cB wceq vz
      cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv cF wceq w3a wph wa vu
      wex vv wex vw wex wa vx vy vz vx cv cA wceq vy cv cB wceq vz cv cC wceq
      w3a vw cv cD wceq vv cv cE wceq vu cv cF wceq w3a wph w3a vu wex vv wex
      vw wex vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv
      cE wceq vu cv cF wceq w3a wph wa wa vu wex vv wex vw wex vx cv cA wceq vy
      cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv cF wceq
      w3a wph wa vu wex vv wex vw wex wa vx cv cA wceq vy cv cB wceq vz cv cC
      wceq w3a vw cv cD wceq vv cv cE wceq vu cv cF wceq w3a wph w3a vx cv cA
      wceq vy cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv cF
      wceq w3a wph wa wa vw vv vu vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a
      vw cv cD wceq vv cv cE wceq vu cv cF wceq w3a wph 3anass 3exbii vx cv cA
      wceq vy cv cB wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv cF
      wceq w3a wph wa vw vv vu 19.42vvv bitri 3exbii vx cv cA wceq vy cv cB
      wceq vz cv cC wceq w3a vw cv cD wceq vv cv cE wceq vu cv cF wceq w3a wph
      wa vu wex vv wex vw wex wa vz wex vy wex vx wex vw cv cD wceq vv cv cE
      wceq vu cv cF wceq w3a wth wa vu wex vv wex vw wex wze vw cv cD wceq vv
      cv cE wceq vu cv cF wceq w3a wph wa vu wex vv wex vw wex vw cv cD wceq vv
      cv cE wceq vu cv cF wceq w3a wps wa vu wex vv wex vw wex vw cv cD wceq vv
      cv cE wceq vu cv cF wceq w3a wch wa vu wex vv wex vw wex vw cv cD wceq vv
      cv cE wceq vu cv cF wceq w3a wth wa vu wex vv wex vw wex vx vy vz cA cB
      cC ceqsex6v.1 ceqsex6v.2 ceqsex6v.3 vx cv cA wceq vw cv cD wceq vv cv cE
      wceq vu cv cF wceq w3a wph wa vw cv cD wceq vv cv cE wceq vu cv cF wceq
      w3a wps wa vw vv vu vx cv cA wceq wph wps vw cv cD wceq vv cv cE wceq vu
      cv cF wceq w3a ceqsex6v.7 anbi2d 3exbidv vy cv cB wceq vw cv cD wceq vv
      cv cE wceq vu cv cF wceq w3a wps wa vw cv cD wceq vv cv cE wceq vu cv cF
      wceq w3a wch wa vw vv vu vy cv cB wceq wps wch vw cv cD wceq vv cv cE
      wceq vu cv cF wceq w3a ceqsex6v.8 anbi2d 3exbidv vz cv cC wceq vw cv cD
      wceq vv cv cE wceq vu cv cF wceq w3a wch wa vw cv cD wceq vv cv cE wceq
      vu cv cF wceq w3a wth wa vw vv vu vz cv cC wceq wch wth vw cv cD wceq vv
      cv cE wceq vu cv cF wceq w3a ceqsex6v.9 anbi2d 3exbidv ceqsex3v wth wta
      wet wze vw vv vu cD cE cF ceqsex6v.4 ceqsex6v.5 ceqsex6v.6 ceqsex6v.10
      ceqsex6v.11 ceqsex6v.12 ceqsex3v bitri bitri $.
  $}

  ${
    $d x y z w v u t s A $.  $d x y z w v u t s B $.  $d x y z w v u t s C $.
    $d x y z w v u t s D $.  $d x y z w v u t s E $.  $d x y z w v u t s F $.
    $d x y z w v u t s G $.  $d x y z w v u t s H $.  $d x ps $.  $d y ch $.
    $d z th $.  $d w ta $.  $d v et $.  $d u ze $.  $d t si $.  $d s rh $.
    ceqsex8v.1 $e |- A e. _V $.
    ceqsex8v.2 $e |- B e. _V $.
    ceqsex8v.3 $e |- C e. _V $.
    ceqsex8v.4 $e |- D e. _V $.
    ceqsex8v.5 $e |- E e. _V $.
    ceqsex8v.6 $e |- F e. _V $.
    ceqsex8v.7 $e |- G e. _V $.
    ceqsex8v.8 $e |- H e. _V $.
    ceqsex8v.9 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsex8v.10 $e |- ( y = B -> ( ps <-> ch ) ) $.
    ceqsex8v.11 $e |- ( z = C -> ( ch <-> th ) ) $.
    ceqsex8v.12 $e |- ( w = D -> ( th <-> ta ) ) $.
    ceqsex8v.13 $e |- ( v = E -> ( ta <-> et ) ) $.
    ceqsex8v.14 $e |- ( u = F -> ( et <-> ze ) ) $.
    ceqsex8v.15 $e |- ( t = G -> ( ze <-> si ) ) $.
    ceqsex8v.16 $e |- ( s = H -> ( si <-> rh ) ) $.
    $( Elimination of eight existential quantifiers, using implicit
       substitution.  (Contributed by NM, 23-Sep-2011.) $)
    ceqsex8v $p |- ( E. x E. y E. z E. w E. v E. u E. t E. s
              ( ( ( x = A /\ y = B ) /\ ( z = C /\ w = D ) )
         /\ ( ( v = E /\ u = F ) /\ ( t = G /\ s = H ) ) /\ ph ) <-> rh ) $=
      vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wa wph w3a vs wex vt
      wex vu wex vv wex vw wex vz wex vy wex vx wex vx cv cA wceq vy cv cB wceq
      wa vz cv cC wceq vw cv cD wceq wa vv cv cE wceq vu cv cF wceq wa vt cv cG
      wceq vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex w3a vw wex vz
      wex vy wex vx wex wrh vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv
      cD wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq
      wa wa wph w3a vs wex vt wex vu wex vv wex vw wex vz wex vx cv cA wceq vy
      cv cB wceq wa vz cv cC wceq vw cv cD wceq wa vv cv cE wceq vu cv cF wceq
      wa vt cv cG wceq vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex w3a
      vw wex vz wex vx vy vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD
      wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa
      wa wph w3a vs wex vt wex vu wex vv wex vx cv cA wceq vy cv cB wceq wa vz
      cv cC wceq vw cv cD wceq wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq
      vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex w3a vz vw vx cv cA
      wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu
      cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a wa vs wex vt wex vu
      wex vv wex vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa
      wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a
      vs wex vt wex vu wex vv wex wa vx cv cA wceq vy cv cB wceq wa vz cv cC
      wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs
      cv cH wceq wa wa wph w3a vs wex vt wex vu wex vv wex vx cv cA wceq vy cv
      cB wceq wa vz cv cC wceq vw cv cD wceq wa vv cv cE wceq vu cv cF wceq wa
      vt cv cG wceq vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex w3a vx
      cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a wa vs wex vt
      wex vu wex vv wex vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD
      wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa
      wph w3a vs wex vt wex wa vu wex vv wex vx cv cA wceq vy cv cB wceq wa vz
      cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG
      wceq vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex wa vx cv cA
      wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu
      cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a wa vs wex vt wex vx
      cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a vs wex vt
      wex wa vv vu vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq
      wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph
      w3a vt vs 19.42vv 2exbii vx cv cA wceq vy cv cB wceq wa vz cv cC wceq vw
      cv cD wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH
      wceq wa wph w3a vs wex vt wex vv vu 19.42vv bitri vx cv cA wceq vy cv cB
      wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF wceq wa
      vt cv cG wceq vs cv cH wceq wa wa wph w3a vs wex vt wex vx cv cA wceq vy
      cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF
      wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a wa vs wex vt wex vv vu vx
      cv cA wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wa wph w3a vx cv cA
      wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu
      cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wph w3a wa vt vs vx cv cA
      wceq vy cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu
      cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wa wph w3a vx cv cA wceq vy
      cv cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF
      wceq wa vt cv cG wceq vs cv cH wceq wa wa wph wa wa vx cv cA wceq vy cv
      cB wceq wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF wceq
      wa vt cv cG wceq vs cv cH wceq wa wph w3a wa vx cv cA wceq vy cv cB wceq
      wa vz cv cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv
      cG wceq vs cv cH wceq wa wa wph 3anass vv cv cE wceq vu cv cF wceq wa vt
      cv cG wceq vs cv cH wceq wa wph w3a vv cv cE wceq vu cv cF wceq wa vt cv
      cG wceq vs cv cH wceq wa wa wph wa vx cv cA wceq vy cv cB wceq wa vz cv
      cC wceq vw cv cD wceq wa wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq
      vs cv cH wceq wa wph df-3an anbi2i bitr4i 2exbii 2exbii vx cv cA wceq vy
      cv cB wceq wa vz cv cC wceq vw cv cD wceq wa vv cv cE wceq vu cv cF wceq
      wa vt cv cG wceq vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex
      df-3an 3bitr4i 2exbii 2exbii vx cv cA wceq vy cv cB wceq wa vz cv cC wceq
      vw cv cD wceq wa vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH
      wceq wa wph w3a vs wex vt wex vu wex vv wex w3a vw wex vz wex vy wex vx
      wex vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wta w3a
      vs wex vt wex vu wex vv wex wrh vv cv cE wceq vu cv cF wceq wa vt cv cG
      wceq vs cv cH wceq wa wph w3a vs wex vt wex vu wex vv wex vv cv cE wceq
      vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wps w3a vs wex vt wex vu
      wex vv wex vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa
      wch w3a vs wex vt wex vu wex vv wex vv cv cE wceq vu cv cF wceq wa vt cv
      cG wceq vs cv cH wceq wa wth w3a vs wex vt wex vu wex vv wex vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wta w3a vs wex vt
      wex vu wex vv wex vx vy vz vw cA cB cC cD ceqsex8v.1 ceqsex8v.2
      ceqsex8v.3 ceqsex8v.4 vx cv cA wceq vv cv cE wceq vu cv cF wceq wa vt cv
      cG wceq vs cv cH wceq wa wph w3a vv cv cE wceq vu cv cF wceq wa vt cv cG
      wceq vs cv cH wceq wa wps w3a vv vu vt vs vx cv cA wceq wph wps vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa ceqsex8v.9 3anbi3d
      4exbidv vy cv cB wceq vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv
      cH wceq wa wps w3a vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH
      wceq wa wch w3a vv vu vt vs vy cv cB wceq wps wch vv cv cE wceq vu cv cF
      wceq wa vt cv cG wceq vs cv cH wceq wa ceqsex8v.10 3anbi3d 4exbidv vz cv
      cC wceq vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wch
      w3a vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wth w3a
      vv vu vt vs vz cv cC wceq wch wth vv cv cE wceq vu cv cF wceq wa vt cv cG
      wceq vs cv cH wceq wa ceqsex8v.11 3anbi3d 4exbidv vw cv cD wceq vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wth w3a vv cv cE
      wceq vu cv cF wceq wa vt cv cG wceq vs cv cH wceq wa wta w3a vv vu vt vs
      vw cv cD wceq wth wta vv cv cE wceq vu cv cF wceq wa vt cv cG wceq vs cv
      cH wceq wa ceqsex8v.12 3anbi3d 4exbidv ceqsex4v wta wet wze wsi wrh vv vu
      vt vs cE cF cG cH ceqsex8v.5 ceqsex8v.6 ceqsex8v.7 ceqsex8v.8 ceqsex8v.13
      ceqsex8v.14 ceqsex8v.15 ceqsex8v.16 ceqsex4v bitri bitri $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x th $.  $d y ch $.  $d y A $.
    gencbvex.1 $e |- A e. _V $.
    gencbvex.2 $e |- ( A = y -> ( ph <-> ps ) ) $.
    gencbvex.3 $e |- ( A = y -> ( ch <-> th ) ) $.
    gencbvex.4 $e |- ( th <-> E. x ( ch /\ A = y ) ) $.
    $( Change of bound variable using implicit substitution.  (Contributed by
       NM, 17-May-1996.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    gencbvex $p |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) ) $=
      vy cv cA wceq wth wps wa wa vy wex vx wex vy cv cA wceq wth wps wa wa vx
      wex vy wex wch wph wa vx wex wth wps wa vy wex vy cv cA wceq wth wps wa
      wa vx vy excom vy cv cA wceq wth wps wa wa vy wex wch wph wa vx wth wps
      wa wch wph wa vy cA gencbvex.1 wth wps wa wch wph wa wb cA vy cv cA vy cv
      wceq wch wph wa wth wps wa cA vy cv wceq wch wth wph wps gencbvex.3
      gencbvex.2 anbi12d bicomd eqcoms ceqsexv exbii vy cv cA wceq wth wps wa
      wa vx wex wth wps wa vy vy cv cA wceq wth wps wa wa vx wex vy cv cA wceq
      vx wex wth wps wa wa wth wps wa vy cv cA wceq wth wps wa vx 19.41v vy cv
      cA wceq vx wex wth wps wa wa wth wps wa vy cv cA wceq vx wex wth wps wa
      simpr wth wps wa vy cv cA wceq vx wex wth vy cv cA wceq vx wex wps wth
      wch cA vy cv wceq wa vx wex vy cv cA wceq vx wex gencbvex.4 wch cA vy cv
      wceq wa vy cv cA wceq vx cA vy cv wceq vy cv cA wceq wch cA vy cv wceq vy
      cv cA wceq cA vy cv eqcom biimpi adantl eximi sylbi adantr ancri impbii
      bitri exbii 3bitr3i $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x th $.  $d y ch $.  $d y A $.
    gencbvex2.1 $e |- A e. _V $.
    gencbvex2.2 $e |- ( A = y -> ( ph <-> ps ) ) $.
    gencbvex2.3 $e |- ( A = y -> ( ch <-> th ) ) $.
    gencbvex2.4 $e |- ( th -> E. x ( ch /\ A = y ) ) $.
    $( Restatement of ~ gencbvex with weaker hypotheses.  (Contributed by
       Jeffrey Hankins, 6-Dec-2006.) $)
    gencbvex2 $p |- ( E. x ( ch /\ ph ) <-> E. y ( th /\ ps ) ) $=
      wph wps wch wth vx vy cA gencbvex2.1 gencbvex2.2 gencbvex2.3 wth wch cA
      vy cv wceq wa vx wex gencbvex2.4 wch cA vy cv wceq wa wth vx cA vy cv
      wceq wch wth gencbvex2.3 biimpac exlimiv impbii gencbvex $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x th $.  $d y ch $.  $d y A $.
    gencbval.1 $e |- A e. _V $.
    gencbval.2 $e |- ( A = y -> ( ph <-> ps ) ) $.
    gencbval.3 $e |- ( A = y -> ( ch <-> th ) ) $.
    gencbval.4 $e |- ( th <-> E. x ( ch /\ A = y ) ) $.
    $( Change of bound variable using implicit substitution.  (Contributed by
       NM, 17-May-1996.) $)
    gencbval $p |- ( A. x ( ch -> ph ) <-> A. y ( th -> ps ) ) $=
      wch wph wi vx wal wth wps wi vy wal wch wph wn wa vx wex wth wps wn wa vy
      wex wch wph wi vx wal wn wth wps wi vy wal wn wph wn wps wn wch wth vx vy
      cA gencbval.1 cA vy cv wceq wph wps gencbval.2 notbid gencbval.3
      gencbval.4 gencbvex wch wph vx exanali wth wps vy exanali 3bitr3i con4bii
      $.
  $}

  ${
    $d A x $.  $d x y $.
    sbhypf.1 $e |- F/ x ps $.
    sbhypf.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Introduce an explicit substitution into an implicit substitution
       hypothesis.  See also ~ csbhypf .  (Contributed by Raph Levien,
       10-Apr-2004.) $)
    sbhypf $p |- ( y = A -> ( [ y / x ] ph <-> ps ) ) $=
      vy cv cA wceq vx cv vy cv wceq vx cv cA wceq wa vx wex wph vx vy wsb wps
      wb vx cv cA wceq vy cv cA wceq vx vy cv vy vex vx cv vy cv cA eqeq1
      ceqsexv vx cv vy cv wceq vx cv cA wceq wa wph vx vy wsb wps wb vx wph vx
      vy wsb wps vx wph vx vy nfs1v sbhypf.1 nfbi vx cv vy cv wceq wph vx vy
      wsb wph vx cv cA wceq wps vx cv vy cv wceq wph wph vx vy wsb wph vx vy
      sbequ12 bicomd sbhypf.2 sylan9bb exlimi sylbir $.
  $}

  ${
    $d y z A $.  $d x z $.  $d y z $.
    $( Closed theorem form of ~ vtoclgf .  (Contributed by NM, 17-Feb-2013.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)
    vtoclgft $p |- ( ( ( F/_ x A /\ F/ x ps )
                  /\ ( A. x ( x = A -> ( ph <-> ps ) )
                     /\ A. x ph ) /\ A e. V ) -> ps ) $=
      cA cV wcel vx cA wnfc wps vx wnf wa vx cv cA wceq wph wps wb wi vx wal
      wph vx wal wa cA cvv wcel wps cA cV elex vx cA wnfc wps vx wnf wa vx cv
      cA wceq wph wps wb wi vx wal wph vx wal wa cA cvv wcel w3a vx cv cA wceq
      vx wex wps vx cA wnfc wps vx wnf wa vx cv cA wceq wph wps wb wi vx wal
      wph vx wal wa cA cvv wcel w3a vz cv cA wceq vz wex vx cv cA wceq vx wex
      cA cvv wcel vx cA wnfc wps vx wnf wa vz cv cA wceq vz wex vx cv cA wceq
      wph wps wb wi vx wal wph vx wal wa vz cA cvv elisset 3ad2ant3 vx cA wnfc
      wps vx wnf wa vx cv cA wceq wph wps wb wi vx wal wph vx wal wa vz cv cA
      wceq vz wex vx cv cA wceq vx wex wb cA cvv wcel vx cA wnfc vz cv cA wceq
      vz wex vx cv cA wceq vx wex wb wps vx wnf vx cv cA wceq wph wps wb wi vx
      wal wph vx wal wa vx cA wnfc vz cv cA wceq vx cv cA wceq vz vx vx cA
      nfnfc1 vx cA wnfc vx vz cv cA vx cA wnfc vx vz cv nfcvd vx cA wnfc id
      nfeqd vz cv vx cv wceq vz cv cA wceq vx cv cA wceq wb wi vx cA wnfc vz cv
      vx cv cA eqeq1 a1i cbvexd ad2antrr 3adant3 mpbid vx cA wnfc wps vx wnf wa
      vx cv cA wceq wph wps wb wi vx wal wph vx wal wa cA cvv wcel w3a vx cv cA
      wceq wps wi vx wal vx cv cA wceq vx wex wps wi vx cv cA wceq wph wps wb
      wi vx wal wph vx wal wa vx cA wnfc wps vx wnf wa vx cv cA wceq wps wi vx
      wal cA cvv wcel vx cv cA wceq wph wps wb wi wph vx cv cA wceq wps wi vx
      vx cv cA wceq wph wps wb wi wph vx cv cA wceq wps wi vx cv cA wceq wph
      wps wb wi vx cv cA wceq wph wps wph wps wb wph wps wi vx cv cA wceq wph
      wps bi1 imim2i com23 imp alanimi 3ad2ant2 vx cA wnfc wps vx wnf wa vx cv
      cA wceq wph wps wb wi vx wal wph vx wal wa cA cvv wcel w3a wps vx wnf vx
      cv cA wceq wps wi vx wal vx cv cA wceq vx wex wps wi wb vx cA wnfc wps vx
      wnf vx cv cA wceq wph wps wb wi vx wal wph vx wal wa cA cvv wcel simp1r
      vx cv cA wceq wps vx 19.23t syl mpbid mpd syl3an3 $.
  $}

  ${
    vtocld.1 $e |- ( ph -> A e. V ) $.
    vtocld.2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    vtocld.3 $e |- ( ph -> ps ) $.
    ${
      vtocldf.4 $e |- F/ x ph $.
      vtocldf.5 $e |- ( ph -> F/_ x A ) $.
      vtocldf.6 $e |- ( ph -> F/ x ch ) $.
      $( Implicit substitution of a class for a set variable.  (Contributed by
         Mario Carneiro, 15-Oct-2016.) $)
      vtocldf $p |- ( ph -> ch ) $=
        wph vx cA wnfc wch vx wnf vx cv cA wceq wps wch wb wi vx wal wps vx wal
        cA cV wcel wch vtocldf.5 vtocldf.6 wph vx cv cA wceq wps wch wb wi vx
        vtocldf.4 wph vx cv cA wceq wps wch wb vtocld.2 ex alrimi wph wps vx
        vtocldf.4 vtocld.3 alrimi vtocld.1 wps wch vx cA cV vtoclgft syl221anc
        $.
    $}

    $d x A $.  $d x ph $.  $d x ch $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       Mario Carneiro, 15-Oct-2016.) $)
    vtocld $p |- ( ph -> ch ) $=
      wph wps wch vx cA cV vtocld.1 vtocld.2 vtocld.3 wph vx nfv wph vx cA
      nfcvd wph wch vx nfvd vtocldf $.
  $}

  ${
    $d x A $.
    vtoclf.1 $e |- F/ x ps $.
    vtoclf.2 $e |- A e. _V $.
    vtoclf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtoclf.4 $e |- ph $.
    $( Implicit substitution of a class for a set variable.  This is a
       generalization of ~ chvar .  (Contributed by NM, 30-Aug-1993.) $)
    vtoclf $p |- ps $=
      wph wps vx wph wps vx vtoclf.1 vx cv cA wceq vx wex wph wps wi vx wex vx
      cA vtoclf.2 isseti vx cv cA wceq wph wps wi vx vx cv cA wceq wph wps
      vtoclf.3 biimpd eximi ax-mp 19.36i vtoclf.4 mpg $.
  $}

  ${
    $d x A $.  $d x ps $.
    vtocl.1 $e |- A e. _V $.
    vtocl.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl.3 $e |- ph $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 30-Aug-1993.) $)
    vtocl $p |- ps $=
      wph wps vx cA wps vx nfv vtocl.1 vtocl.2 vtocl.3 vtoclf $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ps $.
    vtocl2.1 $e |- A e. _V $.
    vtocl2.2 $e |- B e. _V $.
    vtocl2.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    vtocl2.4 $e |- ph $.
    $( Implicit substitution of classes for set variables.  (Contributed by NM,
       26-Jul-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    vtocl2 $p |- ps $=
      wph vy wal wps vx wph vy wal wps vx wph wps wi vy wex vx wex wph vy wal
      wps wi vx wex vx cv cA wceq vx wex vy cv cB wceq vy wex wph wps wi vy wex
      vx wex vx cA vtocl2.1 isseti vy cB vtocl2.2 isseti vx cv cA wceq vx wex
      vy cv cB wceq vy wex wa vx cv cA wceq vy cv cB wceq wa vy wex vx wex wph
      wps wi vy wex vx wex vx cv cA wceq vy cv cB wceq vx vy eeanv vx cv cA
      wceq vy cv cB wceq wa wph wps wi vx vy vx cv cA wceq vy cv cB wceq wa wph
      wps vtocl2.3 biimpd 2eximi sylbir mp2an wph wps wi vy wex wph vy wal wps
      wi vx wph wps vy 19.36v exbii mpbi 19.36aiv wph vy vtocl2.4 ax-gen mpg $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z ps $.
    vtocl3.1 $e |- A e. _V $.
    vtocl3.2 $e |- B e. _V $.
    vtocl3.3 $e |- C e. _V $.
    vtocl3.4 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    vtocl3.5 $e |- ph $.
    $( Implicit substitution of classes for set variables.  (Contributed by NM,
       3-Jun-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    vtocl3 $p |- ps $=
      wph vz wal vy wal wps vx wph vz wal vy wal wps vx wph vz wal wps wi vy
      wex vx wex wph vz wal vy wal wps wi vx wex wph wps wi vz wex vy wex vx
      wex wph vz wal wps wi vy wex vx wex vx cv cA wceq vx wex vy cv cB wceq vy
      wex vz cv cC wceq vz wex wph wps wi vz wex vy wex vx wex vx cA vtocl3.1
      isseti vy cB vtocl3.2 isseti vz cC vtocl3.3 isseti vx cv cA wceq vx wex
      vy cv cB wceq vy wex vz cv cC wceq vz wex w3a vx cv cA wceq vy cv cB wceq
      vz cv cC wceq w3a vz wex vy wex vx wex wph wps wi vz wex vy wex vx wex vx
      cv cA wceq vy cv cB wceq vz cv cC wceq vx vy vz eeeanv vx cv cA wceq vy
      cv cB wceq vz cv cC wceq w3a vz wex wph wps wi vz wex vx vy vx cv cA wceq
      vy cv cB wceq vz cv cC wceq w3a wph wps wi vz vx cv cA wceq vy cv cB wceq
      vz cv cC wceq w3a wph wps vtocl3.4 biimpd eximi 2eximi sylbir mp3an wph
      wps wi vz wex wph vz wal wps wi vx vy wph wps vz 19.36v 2exbii mpbi wph
      vz wal wps wi vy wex wph vz wal vy wal wps wi vx wph vz wal wps vy 19.36v
      exbii mpbi 19.36aiv wph vy vz vtocl3.5 gen2 mpg $.
  $}

  ${
    $d x A $.  $d x ch $.  $d x th $.
    vtoclb.1 $e |- A e. _V $.
    vtoclb.2 $e |- ( x = A -> ( ph <-> ch ) ) $.
    vtoclb.3 $e |- ( x = A -> ( ps <-> th ) ) $.
    vtoclb.4 $e |- ( ph <-> ps ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 23-Dec-1993.) $)
    vtoclb $p |- ( ch <-> th ) $=
      wph wps wb wch wth wb vx cA vtoclb.1 vx cv cA wceq wph wch wps wth
      vtoclb.2 vtoclb.3 bibi12d vtoclb.4 vtocl $.
  $}

  ${
    vtoclgf.1 $e |- F/_ x A $.
    vtoclgf.2 $e |- F/ x ps $.
    vtoclgf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtoclgf.4 $e |- ph $.
    $( Implicit substitution of a class for a set variable, with bound-variable
       hypotheses in place of distinct variable restrictions.  (Contributed by
       NM, 21-Sep-2003.)  (Proof shortened by Mario Carneiro, 10-Oct-2016.) $)
    vtoclgf $p |- ( A e. V -> ps ) $=
      cA cV wcel cA cvv wcel wps cA cV elex cA cvv wcel vx cv cA wceq vx wex
      wps vx cA vtoclgf.1 issetf vx cv cA wceq wps vx vtoclgf.2 vx cv cA wceq
      wph wps vtoclgf.4 vtoclgf.3 mpbii exlimi sylbi syl $.
  $}

  ${
    $d x A $.  $d x ps $.
    vtoclg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtoclg.2 $e |- ph $.
    $( Implicit substitution of a class expression for a set variable.
       (Contributed by NM, 17-Apr-1995.) $)
    vtoclg $p |- ( A e. V -> ps ) $=
      wph wps vx cA cV vx cA nfcv wps vx nfv vtoclg.1 vtoclg.2 vtoclgf $.
  $}

  ${
    $d x A $.  $d x ch $.  $d x th $.
    vtoclbg.1 $e |- ( x = A -> ( ph <-> ch ) ) $.
    vtoclbg.2 $e |- ( x = A -> ( ps <-> th ) ) $.
    vtoclbg.3 $e |- ( ph <-> ps ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 29-Apr-1994.) $)
    vtoclbg $p |- ( A e. V -> ( ch <-> th ) ) $=
      wph wps wb wch wth wb vx cA cV vx cv cA wceq wph wch wps wth vtoclbg.1
      vtoclbg.2 bibi12d vtoclbg.3 vtoclg $.
  $}

  ${
    vtocl2gf.1 $e |- F/_ x A $.
    vtocl2gf.2 $e |- F/_ y A $.
    vtocl2gf.3 $e |- F/_ y B $.
    vtocl2gf.4 $e |- F/ x ps $.
    vtocl2gf.5 $e |- F/ y ch $.
    vtocl2gf.6 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl2gf.7 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl2gf.8 $e |- ph $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 25-Apr-1995.) $)
    vtocl2gf $p |- ( ( A e. V /\ B e. W ) -> ch ) $=
      cA cV wcel cA cvv wcel cB cW wcel wch cA cV elex cA cvv wcel wps wi cA
      cvv wcel wch wi vy cB cW vtocl2gf.3 cA cvv wcel wch vy vy cA cvv
      vtocl2gf.2 nfel1 vtocl2gf.5 nfim vy cv cB wceq wps wch cA cvv wcel
      vtocl2gf.7 imbi2d wph wps vx cA cvv vtocl2gf.1 vtocl2gf.4 vtocl2gf.6
      vtocl2gf.8 vtoclgf vtoclgf mpan9 $.
  $}

  ${
    $d w A $.  $d w B $.  $d w C $.  $d w y $.  $d w z $.
    vtocl3gf.a $e |- F/_ x A $.
    vtocl3gf.b $e |- F/_ y A $.
    vtocl3gf.c $e |- F/_ z A $.
    vtocl3gf.d $e |- F/_ y B $.
    vtocl3gf.e $e |- F/_ z B $.
    vtocl3gf.f $e |- F/_ z C $.
    vtocl3gf.1 $e |- F/ x ps $.
    vtocl3gf.2 $e |- F/ y ch $.
    vtocl3gf.3 $e |- F/ z th $.
    vtocl3gf.4 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl3gf.5 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl3gf.6 $e |- ( z = C -> ( ch <-> th ) ) $.
    vtocl3gf.7 $e |- ph $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 10-Aug-2013.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
    vtocl3gf $p |- ( ( A e. V /\ B e. W /\ C e. X ) -> th ) $=
      cA cV wcel cB cW wcel cC cX wcel wth cA cV wcel cA cvv wcel cB cW wcel cC
      cX wcel wa wth cA cV elex cA cvv wcel wps wi cA cvv wcel wch wi cA cvv
      wcel wth wi vy vz cB cC cW cX vtocl3gf.d vtocl3gf.e vtocl3gf.f cA cvv
      wcel wch vy vy cA cvv vtocl3gf.b nfel1 vtocl3gf.2 nfim cA cvv wcel wth vz
      vz cA cvv vtocl3gf.c nfel1 vtocl3gf.3 nfim vy cv cB wceq wps wch cA cvv
      wcel vtocl3gf.5 imbi2d vz cv cC wceq wch wth cA cvv wcel vtocl3gf.6
      imbi2d wph wps vx cA cvv vtocl3gf.a vtocl3gf.1 vtocl3gf.4 vtocl3gf.7
      vtoclgf vtocl2gf mpan9 3impb $.
  $}

  ${
    $d w x A $.  $d y A $.  $d w y B $.  $d x ps $.  $d y ch $.
    vtocl2g.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl2g.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl2g.3 $e |- ph $.
    $( Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 25-Apr-1995.) $)
    vtocl2g $p |- ( ( A e. V /\ B e. W ) -> ch ) $=
      wph wps wch vx vy cA cB cV cW vx cA nfcv vy cA nfcv vy cB nfcv wps vx nfv
      wch vy nfv vtocl2g.1 vtocl2g.2 vtocl2g.3 vtocl2gf $.
  $}

  ${
    $d y A $.  $d x B z $.
    vtoclgaf.1 $e |- F/_ x A $.
    vtoclgaf.2 $e |- F/ x ps $.
    vtoclgaf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtoclgaf.4 $e |- ( x e. B -> ph ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 17-Feb-2006.)  (Revised by Mario Carneiro, 10-Oct-2016.) $)
    vtoclgaf $p |- ( A e. B -> ps ) $=
      cA cB wcel wps vx cv cB wcel wph wi cA cB wcel wps wi vx cA cB vtoclgaf.1
      cA cB wcel wps vx vx cA cB vtoclgaf.1 nfel1 vtoclgaf.2 nfim vx cv cA wceq
      vx cv cB wcel cA cB wcel wph wps vx cv cA cB eleq1 vtoclgaf.3 imbi12d
      vtoclgaf.4 vtoclgf pm2.43i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x ps $.
    vtoclga.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtoclga.2 $e |- ( x e. B -> ph ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 20-Aug-1995.) $)
    vtoclga $p |- ( A e. B -> ps ) $=
      wph wps vx cA cB vx cA nfcv wps vx nfv vtoclga.1 vtoclga.2 vtoclgaf $.
  $}

  ${
    $d x y C $.  $d x y D $.
    vtocl2gaf.a $e |- F/_ x A $.
    vtocl2gaf.b $e |- F/_ y A $.
    vtocl2gaf.c $e |- F/_ y B $.
    vtocl2gaf.1 $e |- F/ x ps $.
    vtocl2gaf.2 $e |- F/ y ch $.
    vtocl2gaf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl2gaf.4 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl2gaf.5 $e |- ( ( x e. C /\ y e. D ) -> ph ) $.
    $( Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 10-Aug-2013.) $)
    vtocl2gaf $p |- ( ( A e. C /\ B e. D ) -> ch ) $=
      cA cC wcel cB cD wcel wa wch vx cv cC wcel vy cv cD wcel wa wph wi cA cC
      wcel vy cv cD wcel wa wps wi cA cC wcel cB cD wcel wa wch wi vx vy cA cB
      cC cD vtocl2gaf.a vtocl2gaf.b vtocl2gaf.c cA cC wcel vy cv cD wcel wa wps
      vx cA cC wcel vy cv cD wcel vx vx cA cC vtocl2gaf.a nfel1 vy cv cD wcel
      vx nfv nfan vtocl2gaf.1 nfim cA cC wcel cB cD wcel wa wch vy cA cC wcel
      cB cD wcel vy vy cA cC vtocl2gaf.b nfel1 vy cB cD vtocl2gaf.c nfel1 nfan
      vtocl2gaf.2 nfim vx cv cA wceq vx cv cC wcel vy cv cD wcel wa cA cC wcel
      vy cv cD wcel wa wph wps vx cv cA wceq vx cv cC wcel cA cC wcel vy cv cD
      wcel vx cv cA cC eleq1 anbi1d vtocl2gaf.3 imbi12d vy cv cB wceq cA cC
      wcel vy cv cD wcel wa cA cC wcel cB cD wcel wa wps wch vy cv cB wceq vy
      cv cD wcel cB cD wcel cA cC wcel vy cv cB cD eleq1 anbi2d vtocl2gaf.4
      imbi12d vtocl2gaf.5 vtocl2gf pm2.43i $.
  $}

  ${
    $d w x y A $.  $d w y B $.  $d w x y C $.  $d w x y D $.  $d x ps $.
    $d y ch $.
    vtocl2ga.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl2ga.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl2ga.3 $e |- ( ( x e. C /\ y e. D ) -> ph ) $.
    $( Implicit substitution of 2 classes for 2 set variables.  (Contributed by
       NM, 20-Aug-1995.) $)
    vtocl2ga $p |- ( ( A e. C /\ B e. D ) -> ch ) $=
      wph wps wch vx vy cA cB cC cD vx cA nfcv vy cA nfcv vy cB nfcv wps vx nfv
      wch vy nfv vtocl2ga.1 vtocl2ga.2 vtocl2ga.3 vtocl2gaf $.
  $}

  ${
    $d w A $.  $d w B $.  $d w C $.  $d w x y z R $.  $d w x y z S $.
    $d w x y z T $.
    vtocl3gaf.a $e |- F/_ x A $.
    vtocl3gaf.b $e |- F/_ y A $.
    vtocl3gaf.c $e |- F/_ z A $.
    vtocl3gaf.d $e |- F/_ y B $.
    vtocl3gaf.e $e |- F/_ z B $.
    vtocl3gaf.f $e |- F/_ z C $.
    vtocl3gaf.1 $e |- F/ x ps $.
    vtocl3gaf.2 $e |- F/ y ch $.
    vtocl3gaf.3 $e |- F/ z th $.
    vtocl3gaf.4 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl3gaf.5 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl3gaf.6 $e |- ( z = C -> ( ch <-> th ) ) $.
    vtocl3gaf.7 $e |- ( ( x e. R /\ y e. S /\ z e. T ) -> ph ) $.
    $( Implicit substitution of 3 classes for 3 set variables.  (Contributed by
       NM, 10-Aug-2013.)  (Revised by Mario Carneiro, 11-Oct-2016.) $)
    vtocl3gaf $p |- ( ( A e. R /\ B e. S /\ C e. T ) -> th ) $=
      cA cR wcel cB cS wcel cC cT wcel w3a wth vx cv cR wcel vy cv cS wcel vz
      cv cT wcel w3a wph wi cA cR wcel vy cv cS wcel vz cv cT wcel w3a wps wi
      cA cR wcel cB cS wcel vz cv cT wcel w3a wch wi cA cR wcel cB cS wcel cC
      cT wcel w3a wth wi vx vy vz cA cB cC cR cS cT vtocl3gaf.a vtocl3gaf.b
      vtocl3gaf.c vtocl3gaf.d vtocl3gaf.e vtocl3gaf.f cA cR wcel vy cv cS wcel
      vz cv cT wcel w3a wps vx cA cR wcel vy cv cS wcel vz cv cT wcel vx vx cA
      cR vtocl3gaf.a nfel1 vy cv cS wcel vx nfv vz cv cT wcel vx nfv nf3an
      vtocl3gaf.1 nfim cA cR wcel cB cS wcel vz cv cT wcel w3a wch vy cA cR
      wcel cB cS wcel vz cv cT wcel vy vy cA cR vtocl3gaf.b nfel1 vy cB cS
      vtocl3gaf.d nfel1 vz cv cT wcel vy nfv nf3an vtocl3gaf.2 nfim cA cR wcel
      cB cS wcel cC cT wcel w3a wth vz cA cR wcel cB cS wcel cC cT wcel vz vz
      cA cR vtocl3gaf.c nfel1 vz cB cS vtocl3gaf.e nfel1 vz cC cT vtocl3gaf.f
      nfel1 nf3an vtocl3gaf.3 nfim vx cv cA wceq vx cv cR wcel vy cv cS wcel vz
      cv cT wcel w3a cA cR wcel vy cv cS wcel vz cv cT wcel w3a wph wps vx cv
      cA wceq vx cv cR wcel cA cR wcel vy cv cS wcel vz cv cT wcel vx cv cA cR
      eleq1 3anbi1d vtocl3gaf.4 imbi12d vy cv cB wceq cA cR wcel vy cv cS wcel
      vz cv cT wcel w3a cA cR wcel cB cS wcel vz cv cT wcel w3a wps wch vy cv
      cB wceq vy cv cS wcel cB cS wcel cA cR wcel vz cv cT wcel vy cv cB cS
      eleq1 3anbi2d vtocl3gaf.5 imbi12d vz cv cC wceq cA cR wcel cB cS wcel vz
      cv cT wcel w3a cA cR wcel cB cS wcel cC cT wcel w3a wch wth vz cv cC wceq
      vz cv cT wcel cC cT wcel cA cR wcel cB cS wcel vz cv cC cT eleq1 3anbi3d
      vtocl3gaf.6 imbi12d vtocl3gaf.7 vtocl3gf pm2.43i $.
  $}

  ${
    $d w x y z A $.  $d w y z B $.  $d w z C $.  $d w x y z D $.
    $d w x y z R $.  $d w x y z S $.  $d x ps $.  $d y ch $.  $d z th $.
    vtocl3ga.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtocl3ga.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    vtocl3ga.3 $e |- ( z = C -> ( ch <-> th ) ) $.
    vtocl3ga.4 $e |- ( ( x e. D /\ y e. R /\ z e. S ) -> ph ) $.
    $( Implicit substitution of 3 classes for 3 set variables.  (Contributed by
       NM, 20-Aug-1995.) $)
    vtocl3ga $p |- ( ( A e. D /\ B e. R /\ C e. S ) -> th ) $=
      wph wps wch wth vx vy vz cA cB cC cD cR cS vx cA nfcv vy cA nfcv vz cA
      nfcv vy cB nfcv vz cB nfcv vz cC nfcv wps vx nfv wch vy nfv wth vz nfv
      vtocl3ga.1 vtocl3ga.2 vtocl3ga.3 vtocl3ga.4 vtocl3gaf $.
  $}

  ${
    $d x A $.  $d x ph $.
    vtocleg.1 $e |- ( x = A -> ph ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 10-Jan-2004.) $)
    vtocleg $p |- ( A e. V -> ph ) $=
      cA cV wcel vx cv cA wceq vx wex wph vx cA cV elisset vx cv cA wceq wph vx
      vtocleg.1 exlimiv syl $.
  $}

  ${
    $d x A $.
    $( Implicit substitution of a class for a set variable.  (Closed theorem
       version of ~ vtoclef .)  (Contributed by NM, 7-Nov-2005.)  (Revised by
       Mario Carneiro, 11-Oct-2016.) $)
    vtoclegft $p |- ( ( A e. B /\ F/ x ph /\
                   A. x ( x = A -> ph ) ) -> ph ) $=
      cA cB wcel wph vx wnf vx cv cA wceq wph wi vx wal w3a wph vx wex wph cA
      cB wcel vx cv cA wceq wph wi vx wal wph vx wex wph vx wnf cA cB wcel vx
      cv cA wceq vx wex vx cv cA wceq wph wi vx wal wph vx wex vx cA cB elisset
      vx cv cA wceq wph vx exim mpan9 3adant2 wph vx wnf cA cB wcel wph vx wex
      wph wb vx cv cA wceq wph wi vx wal wph vx 19.9t 3ad2ant2 mpbid $.
  $}

  ${
    $d x A $.
    vtoclef.1 $e |- F/ x ph $.
    vtoclef.2 $e |- A e. _V $.
    vtoclef.3 $e |- ( x = A -> ph ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 18-Aug-1993.) $)
    vtoclef $p |- ph $=
      vx cv cA wceq vx wex wph vx cA vtoclef.2 isseti vx cv cA wceq wph vx
      vtoclef.1 vtoclef.3 exlimi ax-mp $.
  $}

  ${
    $d x A $.  $d x ph $.
    vtocle.1 $e |- A e. _V $.
    vtocle.2 $e |- ( x = A -> ph ) $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 9-Sep-1993.) $)
    vtocle $p |- ph $=
      cA cvv wcel wph vtocle.1 wph vx cA cvv vtocle.2 vtocleg ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    vtoclri.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    vtoclri.2 $e |- A. x e. B ph $.
    $( Implicit substitution of a class for a set variable.  (Contributed by
       NM, 21-Nov-1994.) $)
    vtoclri $p |- ( A e. B -> ps ) $=
      wph wps vx cA cB vtoclri.1 wph vx cB vtoclri.2 rspec vtoclga $.
  $}

  ${
    $d x y $.  $d y A $.
    spcimgft.1 $e |- F/ x ps $.
    spcimgft.2 $e |- F/_ x A $.
    $( A closed version of ~ spcimgf .  (Contributed by Mario Carneiro,
       4-Jan-2017.) $)
    spcimgft $p |- ( A. x ( x = A -> ( ph -> ps ) ) -> ( A e. B ->
                      ( A. x ph -> ps ) ) ) $=
      cA cB wcel cA cvv wcel vx cv cA wceq wph wps wi wi vx wal wph vx wal wps
      wi cA cB elex vx cv cA wceq wph wps wi wi vx wal cA cvv wcel wph wps wi
      vx wex wph vx wal wps wi cA cvv wcel vx cv cA wceq vx wex vx cv cA wceq
      wph wps wi wi vx wal wph wps wi vx wex vx cA spcimgft.2 issetf vx cv cA
      wceq wph wps wi vx exim syl5bi wph wps vx spcimgft.1 19.36 syl6ib syl5 $.

    $( A closed version of ~ spcgf .  (Contributed by Andrew Salmon,
       6-Jun-2011.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)
    spcgft $p |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B ->
                      ( A. x ph -> ps ) ) ) $=
      vx cv cA wceq wph wps wb wi vx wal vx cv cA wceq wph wps wi wi vx wal cA
      cB wcel wph vx wal wps wi wi vx cv cA wceq wph wps wb wi vx cv cA wceq
      wph wps wi wi vx wph wps wb wph wps wi vx cv cA wceq wph wps bi1 imim2i
      alimi wph wps vx cA cB spcimgft.1 spcimgft.2 spcimgft syl $.
  $}

  ${
    spcimgf.1 $e |- F/_ x A $.
    spcimgf.2 $e |- F/ x ps $.
    ${
      spcimgf.3 $e |- ( x = A -> ( ph -> ps ) ) $.
      $( Rule of specialization, using implicit substitution.  Compare Theorem
         7.3 of [Quine] p. 44.  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
      spcimgf $p |- ( A e. V -> ( A. x ph -> ps ) ) $=
        vx cv cA wceq wph wps wi wi cA cV wcel wph vx wal wps wi wi vx wph wps
        vx cA cV spcimgf.2 spcimgf.1 spcimgft spcimgf.3 mpg $.
    $}

    spcimegf.3 $e |- ( x = A -> ( ps -> ph ) ) $.
    $( Existential specialization, using implicit substitution.  (Contributed
       by Mario Carneiro, 4-Jan-2017.) $)
    spcimegf $p |- ( A e. V -> ( ps -> E. x ph ) ) $=
      cA cV wcel wps wph wn vx wal wn wph vx wex cA cV wcel wph wn vx wal wps
      wph wn wps wn vx cA cV spcimgf.1 wps vx spcimgf.2 nfn vx cv cA wceq wps
      wph spcimegf.3 con3d spcimgf con2d wph vx df-ex syl6ibr $.
  $}

  ${
    $d y A z $.  $d x z $.
    spcgf.1 $e |- F/_ x A $.
    spcgf.2 $e |- F/ x ps $.
    spcgf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Rule of specialization, using implicit substitution.  Compare Theorem
       7.3 of [Quine] p. 44.  (Contributed by NM, 2-Feb-1997.)  (Revised by
       Andrew Salmon, 12-Aug-2011.) $)
    spcgf $p |- ( A e. V -> ( A. x ph -> ps ) ) $=
      vx cv cA wceq wph wps wb wi cA cV wcel wph vx wal wps wi wi vx wph wps vx
      cA cV spcgf.2 spcgf.1 spcgft spcgf.3 mpg $.

    $( Existential specialization, using implicit substitution.  (Contributed
       by NM, 2-Feb-1997.) $)
    spcegf $p |- ( A e. V -> ( ps -> E. x ph ) ) $=
      cA cV wcel wps wph wn vx wal wn wph vx wex cA cV wcel wph wn vx wal wps
      wph wn wps wn vx cA cV spcgf.1 wps vx spcgf.2 nfn vx cv cA wceq wph wps
      spcgf.3 notbid spcgf con2d wph vx df-ex syl6ibr $.
  $}

  ${
    $d x A $.  $d x ph $.  $d x ch $.
    spcimdv.1 $e |- ( ph -> A e. B ) $.
    ${
      spcimdv.2 $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
      $( Restricted specialization, using implicit substitution.  (Contributed
         by Mario Carneiro, 4-Jan-2017.) $)
      spcimdv $p |- ( ph -> ( A. x ps -> ch ) ) $=
        wph vx cv cA wceq wps wch wi wi vx wal cA cB wcel wps vx wal wch wi wph
        vx cv cA wceq wps wch wi wi vx wph vx cv cA wceq wps wch wi spcimdv.2
        ex alrimiv spcimdv.1 wps wch vx cA cB wch vx nfv vx cA nfcv spcimgft
        sylc $.
    $}

    ${
      spcdv.2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
      $( Rule of specialization, using implicit substitution.  Analogous to
         ~ rspcdv .  (Contributed by David Moews, 1-May-2017.) $)
      spcdv $p |- ( ph -> ( A. x ps -> ch ) ) $=
        wph wps wch vx cA cB spcimdv.1 wph vx cv cA wceq wa wps wch spcdv.2
        biimpd spcimdv $.
    $}

    spcimedv.2 $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
    $( Restricted existential specialization, using implicit substitution.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    spcimedv $p |- ( ph -> ( ch -> E. x ps ) ) $=
      wph wch wps wn vx wal wn wps vx wex wph wps wn vx wal wch wph wps wn wch
      wn vx cA cB spcimdv.1 wph vx cv cA wceq wa wch wps spcimedv.2 con3d
      spcimdv con2d wps vx df-ex syl6ibr $.
  $}

  ${
    $d x ps $.  $d x y A $.
    spcgv.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Rule of specialization, using implicit substitution.  Compare Theorem
       7.3 of [Quine] p. 44.  (Contributed by NM, 22-Jun-1994.) $)
    spcgv $p |- ( A e. V -> ( A. x ph -> ps ) ) $=
      wph wps vx cA cV vx cA nfcv wps vx nfv spcgv.1 spcgf $.

    $( Existential specialization, using implicit substitution.  (Contributed
       by NM, 14-Aug-1994.) $)
    spcegv $p |- ( A e. V -> ( ps -> E. x ph ) ) $=
      wph wps vx cA cV vx cA nfcv wps vx nfv spcgv.1 spcegf $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ps $.
    spc2egv.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Existential specialization with 2 quantifiers, using implicit
       substitution.  (Contributed by NM, 3-Aug-1995.) $)
    spc2egv $p |- ( ( A e. V /\ B e. W ) -> ( ps -> E. x E. y ph ) ) $=
      cA cV wcel cB cW wcel wa vx cv cA wceq vy cv cB wceq wa vy wex vx wex wps
      wph vy wex vx wex cA cV wcel cB cW wcel wa vx cv cA wceq vx wex vy cv cB
      wceq vy wex wa vx cv cA wceq vy cv cB wceq wa vy wex vx wex cA cV wcel vx
      cv cA wceq vx wex cB cW wcel vy cv cB wceq vy wex vx cA cV elisset vy cB
      cW elisset anim12i vx cv cA wceq vy cv cB wceq vx vy eeanv sylibr wps vx
      cv cA wceq vy cv cB wceq wa wph vx vy vx cv cA wceq vy cv cB wceq wa wph
      wps spc2egv.1 biimprcd 2eximdv syl5com $.

    $( Specialization with 2 quantifiers, using implicit substitution.
       (Contributed by NM, 27-Apr-2004.) $)
    spc2gv $p |- ( ( A e. V /\ B e. W ) -> ( A. x A. y ph -> ps ) ) $=
      cA cV wcel cB cW wcel wa wps wph vy wal vx wal cA cV wcel cB cW wcel wa
      wps wn wph wn vy wex vx wex wph vy wal vx wal wn wph wn wps wn vx vy cA
      cB cV cW vx cv cA wceq vy cv cB wceq wa wph wps spc2egv.1 notbid spc2egv
      wph vx vy 2nalexn syl6ibr con4d $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z ps $.
    spc3egv.1 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    $( Existential specialization with 3 quantifiers, using implicit
       substitution.  (Contributed by NM, 12-May-2008.) $)
    spc3egv $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
               ( ps -> E. x E. y E. z ph ) ) $=
      cA cV wcel cB cW wcel cC cX wcel w3a vx cv cA wceq vy cv cB wceq vz cv cC
      wceq w3a vz wex vy wex vx wex wps wph vz wex vy wex vx wex cA cV wcel cB
      cW wcel cC cX wcel w3a vx cv cA wceq vx wex vy cv cB wceq vy wex vz cv cC
      wceq vz wex w3a vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vz wex vy
      wex vx wex cA cV wcel vx cv cA wceq vx wex cB cW wcel vy cv cB wceq vy
      wex cC cX wcel vz cv cC wceq vz wex vx cA cV elisset vy cB cW elisset vz
      cC cX elisset 3anim123i vx cv cA wceq vy cv cB wceq vz cv cC wceq vx vy
      vz eeeanv sylibr wps vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vz wex
      wph vz wex vx vy wps vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a wph vz
      vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a wph wps spc3egv.1 biimprcd
      eximdv 2eximdv syl5com $.

    $( Specialization with 3 quantifiers, using implicit substitution.
       (Contributed by NM, 12-May-2008.) $)
    spc3gv $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
               ( A. x A. y A. z ph -> ps ) ) $=
      cA cV wcel cB cW wcel cC cX wcel w3a wps wph vz wal vy wal vx wal cA cV
      wcel cB cW wcel cC cX wcel w3a wps wn wph wn vz wex vy wex vx wex wph vz
      wal vy wal vx wal wn wph wn wps wn vx vy vz cA cB cC cV cW cX vx cv cA
      wceq vy cv cB wceq vz cv cC wceq w3a wph wps spc3egv.1 notbid spc3egv wph
      wn vz wex vy wex vx wex wph vz wal vy wal wn vx wex wph vz wal vy wal vx
      wal wn wph wn vz wex vy wex wph vz wal vy wal wn vx wph wn vz wex vy wex
      wph vz wal wn vy wex wph vz wal vy wal wn wph wn vz wex wph vz wal wn vy
      wph vz exnal exbii wph vz wal vy exnal bitri exbii wph vz wal vy wal vx
      exnal bitr2i syl6ibr con4d $.
  $}

  ${
    $d x A $.  $d x ps $.
    spcv.1 $e |- A e. _V $.
    spcv.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Rule of specialization, using implicit substitution.  (Contributed by
       NM, 22-Jun-1994.) $)
    spcv $p |- ( A. x ph -> ps ) $=
      cA cvv wcel wph vx wal wps wi spcv.1 wph wps vx cA cvv spcv.2 spcgv ax-mp
      $.

    $( Existential specialization, using implicit substitution.  (Contributed
       by NM, 31-Dec-1993.)  (Proof shortened by Eric Schmidt, 22-Dec-2006.) $)
    spcev $p |- ( ps -> E. x ph ) $=
      cA cvv wcel wps wph vx wex wi spcv.1 wph wps vx cA cvv spcv.2 spcegv
      ax-mp $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ps $.
    spc2ev.1 $e |- A e. _V $.
    spc2ev.2 $e |- B e. _V $.
    spc2ev.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Existential specialization, using implicit substitution.  (Contributed
       by NM, 3-Aug-1995.) $)
    spc2ev $p |- ( ps -> E. x E. y ph ) $=
      cA cvv wcel cB cvv wcel wps wph vy wex vx wex wi spc2ev.1 spc2ev.2 wph
      wps vx vy cA cB cvv cvv spc2ev.3 spc2egv mp2an $.
  $}

  ${
    $d x A $.  $d x B $.
    rspct.1 $e |- F/ x ps $.
    $( A closed version of ~ rspc .  (Contributed by Andrew Salmon,
       6-Jun-2011.) $)
    rspct $p |- ( A. x ( x = A -> ( ph <-> ps ) ) -> ( A e. B ->
                   ( A. x e. B ph -> ps ) ) ) $=
      vx cv cA wceq wph wps wb wi vx wal cA cB wcel wph vx cB wral wps wi vx cv
      cA wceq wph wps wb wi vx wal cA cB wcel wph vx cB wral cA cB wcel wps wph
      vx cB wral vx cv cB wcel wph wi vx wal vx cv cA wceq wph wps wb wi vx wal
      cA cB wcel cA cB wcel wps wi wph vx cB df-ral vx cv cA wceq wph wps wb wi
      vx wal vx cv cA wceq vx cv cB wcel wph wi cA cB wcel wps wi wb wi vx wal
      cA cB wcel vx cv cB wcel wph wi vx wal cA cB wcel wps wi wi wi vx cv cA
      wceq wph wps wb wi vx cv cA wceq vx cv cB wcel wph wi cA cB wcel wps wi
      wb wi vx vx cv cA wceq wph wps wb vx cv cB wcel wph wi cA cB wcel wps wi
      wb vx cv cA wceq wph wps wb vx cv cB wcel wph wi cA cB wcel wps wi wb vx
      cv cA wceq wph wps wb wa vx cv cB wcel cA cB wcel wph wps vx cv cA wceq
      vx cv cB wcel cA cB wcel wb wph wps wb vx cv cA cB eleq1 adantr vx cv cA
      wceq wph wps wb simpr imbi12d ex a2i alimi vx cv cB wcel wph wi cA cB
      wcel wps wi vx cA cB cA cB wcel wps vx cA cB wcel vx nfv rspct.1 nfim vx
      cA nfcv spcgft syl syl7bi com34 pm2.43d $.
  $}

  ${
    $d x y A $.  $d x B $.
    rspc.1 $e |- F/ x ps $.
    rspc.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 19-Apr-2005.)  (Revised by Mario Carneiro, 11-Oct-2016.) $)
    rspc $p |- ( A e. B -> ( A. x e. B ph -> ps ) ) $=
      wph vx cB wral vx cv cB wcel wph wi vx wal cA cB wcel wps wph vx cB
      df-ral vx cv cB wcel wph wi vx wal cA cB wcel wps vx cv cB wcel wph wi cA
      cB wcel wps wi vx cA cB vx cA nfcv cA cB wcel wps vx cA cB wcel vx nfv
      rspc.1 nfim vx cv cA wceq vx cv cB wcel cA cB wcel wph wps vx cv cA cB
      eleq1 rspc.2 imbi12d spcgf pm2.43a syl5bi $.

    $( Restricted existential specialization, using implicit substitution.
       (Contributed by NM, 26-May-1998.)  (Revised by Mario Carneiro,
       11-Oct-2016.) $)
    rspce $p |- ( ( A e. B /\ ps ) -> E. x e. B ph ) $=
      cA cB wcel wps wa vx cv cB wcel wph wa vx wex wph vx cB wrex cA cB wcel
      wps vx cv cB wcel wph wa vx wex vx cv cB wcel wph wa cA cB wcel wps wa vx
      cA cB vx cA nfcv cA cB wcel wps vx cA cB wcel vx nfv rspc.1 nfan vx cv cA
      wceq vx cv cB wcel cA cB wcel wph wps vx cv cA cB eleq1 rspc.2 anbi12d
      spcegf anabsi5 wph vx cB df-rex sylibr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    rspcv.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-May-1998.) $)
    rspcv $p |- ( A e. B -> ( A. x e. B ph -> ps ) ) $=
      wph wps vx cA cB wps vx nfv rspcv.1 rspc $.

    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 2-Feb-2006.) $)
    rspccv $p |- ( A. x e. B ph -> ( A e. B -> ps ) ) $=
      cA cB wcel wph vx cB wral wps wph wps vx cA cB rspcv.1 rspcv com12 $.

    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 13-Sep-2005.) $)
    rspcva $p |- ( ( A e. B /\ A. x e. B ph ) -> ps ) $=
      cA cB wcel wph vx cB wral wps wph wps vx cA cB rspcv.1 rspcv imp $.

    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 26-Jul-2006.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    rspccva $p |- ( ( A. x e. B ph /\ A e. B ) -> ps ) $=
      cA cB wcel wph vx cB wral wps wph wps vx cA cB rspcv.1 rspcv impcom $.

    $( Restricted existential specialization, using implicit substitution.
       (Contributed by NM, 26-May-1998.) $)
    rspcev $p |- ( ( A e. B /\ ps ) -> E. x e. B ph ) $=
      wph wps vx cA cB wps vx nfv rspcv.1 rspce $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.  $d x ch $.
    rspcimdv.1 $e |- ( ph -> A e. B ) $.
    ${
      rspcimdv.2 $e |- ( ( ph /\ x = A ) -> ( ps -> ch ) ) $.
      $( Restricted specialization, using implicit substitution.  (Contributed
         by Mario Carneiro, 4-Jan-2017.) $)
      rspcimdv $p |- ( ph -> ( A. x e. B ps -> ch ) ) $=
        wps vx cB wral vx cv cB wcel wps wi vx wal wph wch wps vx cB df-ral wph
        vx cv cB wcel wps wi vx wal cA cB wcel wch rspcimdv.1 wph vx cv cB wcel
        wps wi cA cB wcel wch wi vx cA cB rspcimdv.1 wph vx cv cA wceq wa cA cB
        wcel vx cv cB wcel wps wch wph vx cv cA wceq wa vx cv cB wcel cA cB
        wcel wph vx cv cA wceq wa vx cv cA cB wph vx cv cA wceq simpr eleq1d
        biimprd rspcimdv.2 imim12d spcimdv mpid syl5bi $.
    $}

    rspcimedv.2 $e |- ( ( ph /\ x = A ) -> ( ch -> ps ) ) $.
    $( Restricted existential specialization, using implicit substitution.
       (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    rspcimedv $p |- ( ph -> ( ch -> E. x e. B ps ) ) $=
      wph wch wps wn vx cB wral wn wps vx cB wrex wph wps wn vx cB wral wch wph
      wps wn wch wn vx cA cB rspcimdv.1 wph vx cv cA wceq wa wch wps
      rspcimedv.2 con3d rspcimdv con2d wps vx cB dfrex2 syl6ibr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.  $d x ch $.
    rspcdv.1 $e |- ( ph -> A e. B ) $.
    rspcdv.2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    $( Restricted specialization, using implicit substitution.  (Contributed by
       NM, 17-Feb-2007.)  (Revised by Mario Carneiro, 4-Jan-2017.) $)
    rspcdv $p |- ( ph -> ( A. x e. B ps -> ch ) ) $=
      wph wps wch vx cA cB rspcdv.1 wph vx cv cA wceq wa wps wch rspcdv.2
      biimpd rspcimdv $.

    $( Restricted existential specialization, using implicit substitution.
       (Contributed by FL, 17-Apr-2007.)  (Revised by Mario Carneiro,
       4-Jan-2017.) $)
    rspcedv $p |- ( ph -> ( ch -> E. x e. B ps ) ) $=
      wph wps wch vx cA cB rspcdv.1 wph vx cv cA wceq wa wps wch rspcdv.2
      biimprd rspcimedv $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x C $.  $d x y D $.
    rspc2.1 $e |- F/ x ch $.
    rspc2.2 $e |- F/ y ps $.
    rspc2.3 $e |- ( x = A -> ( ph <-> ch ) ) $.
    rspc2.4 $e |- ( y = B -> ( ch <-> ps ) ) $.
    $( 2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 9-Nov-2012.) $)
    rspc2 $p |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph ->
                  ps ) ) $=
      cA cC wcel wph vy cD wral vx cC wral wch vy cD wral cB cD wcel wps wph vy
      cD wral wch vy cD wral vx cA cC wch vx vy cD vx cD nfcv rspc2.1 nfral vx
      cv cA wceq wph wch vy cD rspc2.3 ralbidv rspc wch wps vy cB cD rspc2.2
      rspc2.4 rspc sylan9 $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x C $.  $d x y D $.  $d x ch $.  $d y ps $.
    rspc2v.1 $e |- ( x = A -> ( ph <-> ch ) ) $.
    rspc2v.2 $e |- ( y = B -> ( ch <-> ps ) ) $.
    $( 2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 13-Sep-1999.) $)
    rspc2v $p |- ( ( A e. C /\ B e. D ) -> ( A. x e. C A. y e. D ph ->
                  ps ) ) $=
      wph wps wch vx vy cA cB cC cD wch vx nfv wps vy nfv rspc2v.1 rspc2v.2
      rspc2 $.

    $( 2-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 18-Jun-2014.) $)
    rspc2va $p |- ( ( ( A e. C /\ B e. D ) /\ A. x e. C A. y e. D ph ) ->
                  ps ) $=
      cA cC wcel cB cD wcel wa wph vy cD wral vx cC wral wps wph wps wch vx vy
      cA cB cC cD rspc2v.1 rspc2v.2 rspc2v imp $.

    $( 2-variable restricted existential specialization, using implicit
       substitution.  (Contributed by NM, 16-Oct-1999.) $)
    rspc2ev $p |- ( ( A e. C /\ B e. D /\ ps ) -> E. x e. C E. y e. D ph ) $=
      cA cC wcel cB cD wcel wps w3a cA cC wcel wch vy cD wrex wa wph vy cD wrex
      vx cC wrex cA cC wcel cB cD wcel wps cA cC wcel wch vy cD wrex wa cB cD
      wcel wps wa wch vy cD wrex cA cC wcel wch wps vy cB cD rspc2v.2 rspcev
      anim2i 3impb wph vy cD wrex wch vy cD wrex vx cA cC vx cv cA wceq wph wch
      vy cD rspc2v.1 rexbidv rspcev syl $.
  $}

  ${
    $d z ps $.  $d x ch $.  $d y th $.  $d x y z A $.  $d y z B $.  $d z C $.
    $d x R $.  $d x y S $.  $d x y z T $.
    rspc3v.1 $e |- ( x = A -> ( ph <-> ch ) ) $.
    rspc3v.2 $e |- ( y = B -> ( ch <-> th ) ) $.
    rspc3v.3 $e |- ( z = C -> ( th <-> ps ) ) $.
    $( 3-variable restricted specialization, using implicit substitution.
       (Contributed by NM, 10-May-2005.) $)
    rspc3v $p |- ( ( A e. R /\ B e. S /\ C e. T ) ->
                  ( A. x e. R A. y e. S A. z e. T ph -> ps ) ) $=
      cA cR wcel cB cS wcel cC cT wcel wph vz cT wral vy cS wral vx cR wral wps
      wi cA cR wcel cB cS wcel wa wph vz cT wral vy cS wral vx cR wral wth vz
      cT wral cC cT wcel wps wph vz cT wral wth vz cT wral wch vz cT wral vx vy
      cA cB cR cS vx cv cA wceq wph wch vz cT rspc3v.1 ralbidv vy cv cB wceq
      wch wth vz cT rspc3v.2 ralbidv rspc2v wth wps vz cC cT rspc3v.3 rspcv
      sylan9 3impa $.

    $( 3-variable restricted existentional specialization, using implicit
       substitution.  (Contributed by NM, 25-Jul-2012.) $)
    rspc3ev $p |- ( ( ( A e. R /\ B e. S /\ C e. T ) /\ ps ) ->
                  E. x e. R E. y e. S E. z e. T ph ) $=
      cA cR wcel cB cS wcel cC cT wcel w3a wps wa cA cR wcel cB cS wcel wth vz
      cT wrex wph vz cT wrex vy cS wrex vx cR wrex cA cR wcel cB cS wcel cC cT
      wcel wps simpl1 cA cR wcel cB cS wcel cC cT wcel wps simpl2 cC cT wcel cA
      cR wcel wps wth vz cT wrex cB cS wcel wth wps vz cC cT rspc3v.3 rspcev
      3ad2antl3 wph vz cT wrex wth vz cT wrex wch vz cT wrex vx vy cA cB cR cS
      vx cv cA wceq wph wch vz cT rspc3v.1 rexbidv vy cv cB wceq wch wth vz cT
      rspc3v.2 rexbidv rspc2ev syl3anc $.
  $}

  ${
    $d x A y z $.  $d x B y z $.
    eqvinc.1 $e |- A e. _V $.
    $( A variable introduction law for class equality.  (Contributed by NM,
       14-Apr-1995.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    eqvinc $p |- ( A = B <-> E. x ( x = A /\ x = B ) ) $=
      cA cB wceq vx cv cA wceq vx cv cB wceq wa vx wex cA cB wceq vx cv cA wceq
      vx cv cB wceq wa vx vx cv cA wceq vx wex cA cB wceq vx cv cA wceq wi cA
      cB wceq vx cv cB wceq wi wa vx wex cA cB wceq vx cv cA wceq vx cv cB wceq
      wa wi vx wex vx cA eqvinc.1 isseti vx cv cA wceq cA cB wceq vx cv cA wceq
      wi cA cB wceq vx cv cB wceq wi wa vx vx cv cA wceq cA cB wceq vx cv cA
      wceq wi cA cB wceq vx cv cB wceq wi vx cv cA wceq cA cB wceq ax-1 vx cv
      cA wceq cA cB wceq vx cv cB wceq vx cv cA cB eqtr ex jca eximi cA cB wceq
      vx cv cA wceq wi cA cB wceq vx cv cB wceq wi wa cA cB wceq vx cv cA wceq
      vx cv cB wceq wa wi vx cA cB wceq vx cv cA wceq vx cv cB wceq pm3.43
      eximi mp2b 19.37aiv vx cv cA wceq vx cv cB wceq wa cA cB wceq vx vx cv cA
      cB eqtr2 exlimiv impbii $.
  $}

  ${
    $d A y $.  $d B y $.  $d x y $.
    eqvincf.1 $e |- F/_ x A $.
    eqvincf.2 $e |- F/_ x B $.
    eqvincf.3 $e |- A e. _V $.
    $( A variable introduction law for class equality, using bound-variable
       hypotheses instead of distinct variable conditions.  (Contributed by NM,
       14-Sep-2003.) $)
    eqvincf $p |- ( A = B <-> E. x ( x = A /\ x = B ) ) $=
      cA cB wceq vy cv cA wceq vy cv cB wceq wa vy wex vx cv cA wceq vx cv cB
      wceq wa vx wex vy cA cB eqvincf.3 eqvinc vy cv cA wceq vy cv cB wceq wa
      vx cv cA wceq vx cv cB wceq wa vy vx vy cv cA wceq vy cv cB wceq vx vx vy
      cv cA eqvincf.1 nfeq2 vx vy cv cB eqvincf.2 nfeq2 nfan vx cv cA wceq vx
      cv cB wceq wa vy nfv vy cv vx cv wceq vy cv cA wceq vx cv cA wceq vy cv
      cB wceq vx cv cB wceq vy cv vx cv cA eqeq1 vy cv vx cv cB eqeq1 anbi12d
      cbvex bitri $.
  $}

  ${
    $d x A y $.  $d ph y $.
    alexeq.1 $e |- A e. _V $.
    $( Two ways to express substitution of ` A ` for ` x ` in ` ph ` .
       (Contributed by NM, 2-Mar-1995.) $)
    alexeq $p |- ( A. x ( x = A -> ph ) <-> E. x ( x = A /\ ph ) ) $=
      vx cv cA wceq wph wa vx wex vx cv cA wceq wph wi vx wal vx cv vy cv wceq
      wph wa vx wex vx cv vy cv wceq wph wi vx wal vx cv cA wceq wph wa vx wex
      vx cv cA wceq wph wi vx wal vy cA alexeq.1 vy cv cA wceq vx cv vy cv wceq
      wph wa vx cv cA wceq wph wa vx vy cv cA wceq vx cv vy cv wceq vx cv cA
      wceq wph vy cv cA vx cv eqeq2 anbi1d exbidv vy cv cA wceq vx cv vy cv
      wceq wph wi vx cv cA wceq wph wi vx vy cv cA wceq vx cv vy cv wceq vx cv
      cA wceq wph vy cv cA vx cv eqeq2 imbi1d albidv wph vx vy sb56 vtoclb
      bicomi $.
  $}

  ${
    $d x A y $.  $d ph y $.
    $( Equality implies equivalence with substitution.  (Contributed by NM,
       2-Mar-1995.) $)
    ceqex $p |- ( x = A -> ( ph <-> E. x ( x = A /\ ph ) ) ) $=
      cA cvv wcel vx cv cA wceq wph vx cv cA wceq wph wa vx wex wb vx cv cA
      wceq vx cv cA wceq vx wex cA cvv wcel vx cv cA wceq vx 19.8a vx cA isset
      sylibr vx cv vy cv wceq wph vx cv vy cv wceq wph wa vx wex wb wi vx cv cA
      wceq wph vx cv cA wceq wph wa vx wex wb wi vy cA cvv vy cv cA wceq vx cv
      vy cv wceq vx cv cA wceq wph vx cv vy cv wceq wph wa vx wex wb wph vx cv
      cA wceq wph wa vx wex wb vy cv cA vx cv eqeq2 vy cv cA wceq vx cv vy cv
      wceq wph wa vx wex vx cv cA wceq wph wa vx wex wph vy cv cA wceq vx cv vy
      cv wceq wph wa vx cv cA wceq wph wa vx vy cv cA wceq vx cv vy cv wceq vx
      cv cA wceq wph vy cv cA vx cv eqeq2 anbi1d exbidv bibi2d imbi12d vx cv vy
      cv wceq wph vx cv vy cv wceq wph wa vx wex vx cv vy cv wceq wph vx cv vy
      cv wceq wph wa vx wex vx cv vy cv wceq wph wa vx 19.8a ex vx cv vy cv
      wceq wph wa vx wex vx cv vy cv wceq wph wi vx wal vx cv vy cv wceq wph
      wph vx vy cv vy vex alexeq vx cv vy cv wceq wph wi vx wal vx cv vy cv
      wceq wph vx cv vy cv wceq wph wi vx sp com12 syl5bir impbid vtoclg mpcom
      $.
  $}

  ${
    $d x y A $.
    ceqsexg.1 $e |- F/ x ps $.
    ceqsexg.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( A representation of explicit substitution of a class for a variable,
       inferred from an implicit substitution hypothesis.  (Contributed by NM,
       11-Oct-2004.) $)
    ceqsexg $p |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) ) $=
      wph wph wb vx cv cA wceq wph wa vx wex wps wb vx cA cV vx cA nfcv vx cv
      cA wceq wph wa vx wex wps vx vx cv cA wceq wph wa vx nfe1 ceqsexg.1 nfbi
      vx cv cA wceq wph vx cv cA wceq wph wa vx wex wph wps wph vx cA ceqex
      ceqsexg.2 bibi12d wph biid vtoclgf $.
  $}

  ${
    $d x y A $.  $d x ps $.
    ceqsexgv.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Elimination of an existential quantifier, using implicit substitution.
       (Contributed by NM, 29-Dec-1996.) $)
    ceqsexgv $p |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) ) $=
      wph wps vx cA cV wps vx nfv ceqsexgv.1 ceqsexg $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    ceqsrexv.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by NM, 30-Apr-2004.) $)
    ceqsrexv $p |- ( A e. B -> ( E. x e. B ( x = A /\ ph ) <-> ps ) ) $=
      vx cv cA wceq wph wa vx cB wrex vx cv cA wceq vx cv cB wcel wph wa wa vx
      wex cA cB wcel wps vx cv cA wceq wph wa vx cB wrex vx cv cB wcel vx cv cA
      wceq wph wa wa vx wex vx cv cA wceq vx cv cB wcel wph wa wa vx wex vx cv
      cA wceq wph wa vx cB df-rex vx cv cA wceq vx cv cB wcel wph wa wa vx cv
      cB wcel vx cv cA wceq wph wa wa vx vx cv cA wceq vx cv cB wcel wph an12
      exbii bitr4i cA cB wcel vx cv cA wceq vx cv cB wcel wph wa wa vx wex wps
      vx cv cB wcel wph wa cA cB wcel wps wa vx cA cB vx cv cA wceq vx cv cB
      wcel cA cB wcel wph wps vx cv cA cB eleq1 ceqsrexv.1 anbi12d ceqsexgv
      bianabs syl5bb $.

    $( Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by Mario Carneiro, 14-Mar-2014.) $)
    ceqsrexbv $p |- ( E. x e. B ( x = A /\ ph ) <-> ( A e. B /\ ps ) ) $=
      cA cB wcel vx cv cA wceq wph wa wa vx cB wrex cA cB wcel vx cv cA wceq
      wph wa vx cB wrex wa vx cv cA wceq wph wa vx cB wrex cA cB wcel wps wa cA
      cB wcel vx cv cA wceq wph wa vx cB r19.42v cA cB wcel vx cv cA wceq wph
      wa wa vx cv cA wceq wph wa vx cB cA cB wcel vx cv cA wceq wph wa wa vx cv
      cB wcel vx cv cA wceq wph wa vx cv cB wcel vx cv cA wceq wph wa wa cA cB
      wcel vx cv cA wceq wph wa wa vx cv cA wceq wph wa vx cv cB wcel cA cB
      wcel vx cv cA wceq vx cv cB wcel cA cB wcel wb wph vx cv cA cB eleq1
      adantr pm5.32ri bicomi baib rexbiia cA cB wcel vx cv cA wceq wph wa vx cB
      wrex wps wph wps vx cA cB ceqsrexv.1 ceqsrexv pm5.32i 3bitr3i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x C $.  $d x y D $.  $d x ps $.  $d y ch $.
    ceqsrex2v.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ceqsrex2v.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    $( Elimination of a restricted existential quantifier, using implicit
       substitution.  (Contributed by NM, 29-Oct-2005.) $)
    ceqsrex2v $p |- ( ( A e. C /\ B e. D ) ->
      ( E. x e. C E. y e. D ( ( x = A /\ y = B ) /\ ph ) <-> ch ) ) $=
      cA cC wcel vx cv cA wceq vy cv cB wceq wa wph wa vy cD wrex vx cC wrex vy
      cv cB wceq wps wa vy cD wrex cB cD wcel wch vx cv cA wceq vy cv cB wceq
      wa wph wa vy cD wrex vx cC wrex vx cv cA wceq vy cv cB wceq wph wa vy cD
      wrex wa vx cC wrex cA cC wcel vy cv cB wceq wps wa vy cD wrex vx cv cA
      wceq vy cv cB wceq wa wph wa vy cD wrex vx cv cA wceq vy cv cB wceq wph
      wa vy cD wrex wa vx cC vx cv cA wceq vy cv cB wceq wa wph wa vy cD wrex
      vx cv cA wceq vy cv cB wceq wph wa wa vy cD wrex vx cv cA wceq vy cv cB
      wceq wph wa vy cD wrex wa vx cv cA wceq vy cv cB wceq wa wph wa vx cv cA
      wceq vy cv cB wceq wph wa wa vy cD vx cv cA wceq vy cv cB wceq wph anass
      rexbii vx cv cA wceq vy cv cB wceq wph wa vy cD r19.42v bitri rexbii vy
      cv cB wceq wph wa vy cD wrex vy cv cB wceq wps wa vy cD wrex vx cA cC vx
      cv cA wceq vy cv cB wceq wph wa vy cv cB wceq wps wa vy cD vx cv cA wceq
      wph wps vy cv cB wceq ceqsrex2v.1 anbi2d rexbidv ceqsrexv syl5bb wps wch
      vy cB cD ceqsrex2v.2 ceqsrexv sylan9bb $.
  $}

  ${
    $d x A $.  $d x B $.
    clel2.1 $e |- A e. _V $.
    $( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)
    clel2 $p |- ( A e. B <-> A. x ( x = A -> x e. B ) ) $=
      vx cv cA wceq vx cv cB wcel wi vx wal cA cB wcel vx cv cB wcel cA cB wcel
      vx cA clel2.1 vx cv cA cB eleq1 ceqsalv bicomi $.
  $}

  ${
    $d x A $.  $d x B $.
    $( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 13-Aug-2005.) $)
    clel3g $p |- ( B e. V -> ( A e. B <-> E. x ( x = B /\ A e. x ) ) ) $=
      cB cV wcel vx cv cB wceq cA vx cv wcel wa vx wex cA cB wcel cA vx cv wcel
      cA cB wcel vx cB cV vx cv cB cA eleq2 ceqsexgv bicomd $.
  $}

  ${
    $d x A $.  $d x B $.
    clel3.1 $e |- B e. _V $.
    $( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)
    clel3 $p |- ( A e. B <-> E. x ( x = B /\ A e. x ) ) $=
      cB cvv wcel cA cB wcel vx cv cB wceq cA vx cv wcel wa vx wex wb clel3.1
      vx cA cB cvv clel3g ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.
    clel4.1 $e |- B e. _V $.
    $( An alternate definition of class membership when the class is a set.
       (Contributed by NM, 18-Aug-1993.) $)
    clel4 $p |- ( A e. B <-> A. x ( x = B -> A e. x ) ) $=
      vx cv cB wceq cA vx cv wcel wi vx wal cA cB wcel cA vx cv wcel cA cB wcel
      vx cB clel4.1 vx cv cB cA eleq2 ceqsalv bicomi $.
  $}

  ${
    $d y A z $.  $d y B z $.
    $( Compare theorem *13.183 in [WhiteheadRussell] p. 178.  Only ` A ` is
       required to be a set.  (Contributed by Andrew Salmon, 3-Jun-2011.) $)
    pm13.183 $p |- ( A e. V -> ( A = B <-> A. z ( z = A <-> z = B ) ) ) $=
      vy cv cB wceq vz cv vy cv wceq vz cv cB wceq wb vz wal cA cB wceq vz cv
      cA wceq vz cv cB wceq wb vz wal vy cA cV vy cv cA cB eqeq1 vy cv cA wceq
      vz cv vy cv wceq vz cv cB wceq wb vz cv cA wceq vz cv cB wceq wb vz vy cv
      cA wceq vz cv vy cv wceq vz cv cA wceq vz cv cB wceq vy cv cA vz cv eqeq2
      bibi1d albidv vy cv cB wceq vz cv vy cv wceq vz cv cB wceq wb vz wal vy
      cv cB wceq vz cv vy cv wceq vz cv cB wceq wb vz vy cv cB vz cv eqeq2
      alrimiv vz cv vy cv wceq vz cv cB wceq wb vz wal vz cv vy cv wceq vz cv
      cB wceq wb vz vy wsb vy cv cB wceq vz cv vy cv wceq vz cv cB wceq wb vz
      vy stdpc4 vz cv vy cv wceq vz cv cB wceq wb vz vy wsb vz cv vy cv wceq vz
      vy wsb vz cv cB wceq vz vy wsb wb vy cv cB wceq vz cv vy cv wceq vz cv cB
      wceq vz vy sbbi vz cv vy cv wceq vz vy wsb vz cv cB wceq vz vy wsb wb vz
      cv vy cv wceq vz vy wsb vy cv cB wceq wb vy cv cB wceq vz cv cB wceq vz
      vy wsb vy cv cB wceq vz cv vy cv wceq vz vy wsb vy vz cB eqsb3 bibi2i vz
      cv vy cv wceq vz vy wsb vy cv cB wceq wb vz cv vy cv wceq vz vy wsb vy cv
      cB wceq vz vy equsb1 vz cv vy cv wceq vz vy wsb vy cv cB wceq bi1 mpi
      sylbi sylbi syl impbii vtoclbg $.
  $}

  ${
    $d y A $.  $d x y $.  $d y ph $.
    $( Restricted quantifier version of Theorem 19.3 of [Margaris] p. 89.  We
       don't need the non-empty class condition of ~ r19.3rzv when there is an
       outer quantifier.  (Contributed by NM, 25-Oct-2012.) $)
    rr19.3v $p |- ( A. x e. A A. y e. A ph <-> A. x e. A ph ) $=
      wph vy cA wral vx cA wral wph vx cA wral wph vy cA wral wph vx cA wph wph
      vy vx cv cA vy cv vx cv wceq wph biidd rspcv ralimia wph wph vy cA wral
      vx cA wph wph vy cA wph vy cv cA wcel ax-1 ralrimiv ralimi impbii $.

    $( Restricted quantifier version of Theorem 19.28 of [Margaris] p. 90.  We
       don't need the non-empty class condition of ~ r19.28zv when there is an
       outer quantifier.  (Contributed by NM, 29-Oct-2012.) $)
    rr19.28v $p |- ( A. x e. A A. y e. A ( ph /\ ps )
                      <-> A. x e. A ( ph /\ A. y e. A ps ) ) $=
      wph wps wa vy cA wral vx cA wral wph wps vy cA wral wa vx cA wral wph wps
      wa vy cA wral wph wps vy cA wral wa vx cA vx cv cA wcel wph wps wa vy cA
      wral wph wps vy cA wral wph wps wa vy cA wral wph vy cA wral vx cv cA
      wcel wph wph wps wa wph vy cA wph wps simpl ralimi wph wph vy vx cv cA vy
      cv vx cv wceq wph biidd rspcv syl5 wph wps wa vy cA wral wps vy cA wral
      wi vx cv cA wcel wph wps wa wps vy cA wph wps simpr ralimi a1i jcad
      ralimia wph wps vy cA wral wa wph wps wa vy cA wral vx cA wph wps vy cA
      r19.28av ralimi impbii $.
  $}

  ${
    $d x y A $.  $d y ph $.  $d x ps $.
    $( Membership in a class abstraction, using implicit substitution.  (Closed
       theorem version of ~ elabg .)  (Contributed by NM, 7-Nov-2005.)  (Proof
       shortened by Andrew Salmon, 8-Jun-2011.) $)
    elabgt $p |- ( ( A e. B /\ A. x ( x = A -> ( ph <-> ps ) ) ) ->
                 ( A e. { x | ph } <-> ps ) ) $=
      vx cv cA wceq wph wps wb wi vx wal cA cB wcel vx cv cA wceq cA wph vx cab
      wcel wps wb wi vx wal cA wph vx cab wcel wps wb vx cv cA wceq wph wps wb
      wi vx cv cA wceq cA wph vx cab wcel wps wb wi vx vx cv cA wceq wph wps wb
      cA wph vx cab wcel wps wb vx cv cA wceq wph wps wb cA wph vx cab wcel wps
      wb vx cv cA wceq wph cA wph vx cab wcel wps wph vx cv wph vx cab wcel vx
      cv cA wceq cA wph vx cab wcel wph vx abid vx cv cA wph vx cab eleq1
      syl5bbr bibi1d biimpd a2i alimi cA cB wcel vx cv cA wceq cA wph vx cab
      wcel wps wb wi vx wal cA wph vx cab wcel wps wb vx cv cA wceq cA wph vx
      cab wcel wps wb wi cA wph vx cab wcel wps wb vx cA cB vx cA nfcv cA wph
      vx cab wcel wps vx vx cA wph vx cab wph vx nfab1 nfel2 wps vx nfv nfbi vx
      cv cA wceq cA wph vx cab wcel wps wb pm5.5 spcgf imp sylan2 $.
  $}

  ${
    elabgf.1 $e |- F/_ x A $.
    elabgf.2 $e |- F/ x ps $.
    elabgf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  This version has bound-variable
       hypotheses in place of distinct variable restrictions.  (Contributed by
       NM, 21-Sep-2003.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)
    elabgf $p |- ( A e. B -> ( A e. { x | ph } <-> ps ) ) $=
      vx cv wph vx cab wcel wph wb cA wph vx cab wcel wps wb vx cA cB elabgf.1
      cA wph vx cab wcel wps vx vx cA wph vx cab elabgf.1 wph vx nfab1 nfel
      elabgf.2 nfbi vx cv cA wceq vx cv wph vx cab wcel cA wph vx cab wcel wph
      wps vx cv cA wph vx cab eleq1 elabgf.3 bibi12d wph vx abid vtoclgf $.
  $}

  ${
    $d ps y $.  $d x A y $.  $d y ph $.
    elabf.1 $e |- F/ x ps $.
    elabf.2 $e |- A e. _V $.
    elabf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 1-Aug-1994.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)
    elabf $p |- ( A e. { x | ph } <-> ps ) $=
      cA cvv wcel cA wph vx cab wcel wps wb elabf.2 wph wps vx cA cvv vx cA
      nfcv elabf.1 elabf.3 elabgf ax-mp $.
  $}

  ${
    $d x ps $.  $d x A $.
    elab.1 $e |- A e. _V $.
    elab.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  (Contributed by NM, 1-Aug-1994.) $)
    elab $p |- ( A e. { x | ph } <-> ps ) $=
      wph wps vx cA wps vx nfv elab.1 elab.2 elabf $.
  $}

  ${
    $d x ps $.  $d x y A $.
    elabg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction, using implicit substitution.  Compare
       Theorem 6.13 of [Quine] p. 44.  (Contributed by NM, 14-Apr-1995.) $)
    elabg $p |- ( A e. V -> ( A e. { x | ph } <-> ps ) ) $=
      wph wps vx cA cV vx cA nfcv wps vx nfv elabg.1 elabgf $.
  $}

  ${
    $d x ps $.  $d x A $.
    elab2g.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    elab2g.2 $e |- B = { x | ph } $.
    $( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 13-Sep-1995.) $)
    elab2g $p |- ( A e. V -> ( A e. B <-> ps ) ) $=
      cA cB wcel cA wph vx cab wcel cA cV wcel wps cB wph vx cab cA elab2g.2
      eleq2i wph wps vx cA cV elab2g.1 elabg syl5bb $.
  $}

  ${
    $d x ps $.  $d x A $.
    elab2.1 $e |- A e. _V $.
    elab2.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    elab2.3 $e |- B = { x | ph } $.
    $( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 13-Sep-1995.) $)
    elab2 $p |- ( A e. B <-> ps ) $=
      cA cvv wcel cA cB wcel wps wb elab2.1 wph wps vx cA cB cvv elab2.2
      elab2.3 elab2g ax-mp $.
  $}

  ${
    $d x ps $.  $d x A $.
    elab4g.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    elab4g.2 $e |- B = { x | ph } $.
    $( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 17-Oct-2012.) $)
    elab4g $p |- ( A e. B <-> ( A e. _V /\ ps ) ) $=
      cA cB wcel cA cvv wcel wps cA cB elex wph wps vx cA cB cvv elab4g.1
      elab4g.2 elab2g biadan2 $.
  $}

  ${
    $d y A $.
    elab3gf.1 $e |- F/_ x A $.
    elab3gf.2 $e |- F/ x ps $.
    elab3gf.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction, with a weaker antecedent than
       ~ elabgf .  (Contributed by NM, 6-Sep-2011.) $)
    elab3gf $p |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) ) $=
      wps cA cB wcel cA wph vx cab wcel wps wb wps wn cA wph vx cab wcel wps cA
      wph vx cab wcel wps wph wps vx cA wph vx cab elab3gf.1 elab3gf.2
      elab3gf.3 elabgf ibi wps cA wph vx cab wcel pm2.21 impbid2 wph wps vx cA
      cB elab3gf.1 elab3gf.2 elab3gf.3 elabgf ja $.
  $}

  ${
    $d x ps $.  $d x y A $.
    elab3g.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction, with a weaker antecedent than
       ~ elabg .  (Contributed by NM, 29-Aug-2006.) $)
    elab3g $p |- ( ( ps -> A e. B ) -> ( A e. { x | ph } <-> ps ) ) $=
      wph wps vx cA cB vx cA nfcv wps vx nfv elab3g.1 elab3gf $.
  $}

  ${
    $d x ps $.  $d x A $.
    elab3.1 $e |- ( ps -> A e. _V ) $.
    elab3.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a class abstraction using implicit substitution.
       (Contributed by NM, 10-Nov-2000.) $)
    elab3 $p |- ( A e. { x | ph } <-> ps ) $=
      wps cA cvv wcel wi cA wph vx cab wcel wps wb elab3.1 wph wps vx cA cvv
      elab3.2 elab3g ax-mp $.
  $}

  ${
    elrabf.1 $e |- F/_ x A $.
    elrabf.2 $e |- F/_ x B $.
    elrabf.3 $e |- F/ x ps $.
    elrabf.4 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a restricted class abstraction, using implicit
       substitution.  This version has bound-variable hypotheses in place of
       distinct variable restrictions.  (Contributed by NM, 21-Sep-2003.) $)
    elrabf $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) ) $=
      cA wph vx cB crab wcel cA cvv wcel cA cB wcel wps wa cA wph vx cB crab
      elex cA cB wcel cA cvv wcel wps cA cB elex adantr cA wph vx cB crab wcel
      cA vx cv cB wcel wph wa vx cab wcel cA cvv wcel cA cB wcel wps wa wph vx
      cB crab vx cv cB wcel wph wa vx cab cA wph vx cB df-rab eleq2i vx cv cB
      wcel wph wa cA cB wcel wps wa vx cA cvv elrabf.1 cA cB wcel wps vx vx cA
      cB elrabf.1 elrabf.2 nfel elrabf.3 nfan vx cv cA wceq vx cv cB wcel cA cB
      wcel wph wps vx cv cA cB eleq1 elrabf.4 anbi12d elabgf syl5bb pm5.21nii
      $.
  $}

  ${
    $d x ps $.  $d x y A $.  $d x y B $.
    elrab.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Membership in a restricted class abstraction, using implicit
       substitution.  (Contributed by NM, 21-May-1999.) $)
    elrab $p |- ( A e. { x e. B | ph } <-> ( A e. B /\ ps ) ) $=
      wph wps vx cA cB vx cA nfcv vx cB nfcv wps vx nfv elrab.1 elrabf $.

    $( Membership in a restricted class abstraction, using implicit
       substitution.  (Contributed by NM, 5-Oct-2006.) $)
    elrab3 $p |- ( A e. B -> ( A e. { x e. B | ph } <-> ps ) ) $=
      cA wph vx cB crab wcel cA cB wcel wps wph wps vx cA cB elrab.1 elrab baib
      $.
  $}

  ${
    $d x ps $.  $d x y A $.  $d x y B $.
    elrab2.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    elrab2.2 $e |- C = { x e. B | ph } $.
    $( Membership in a class abstraction, using implicit substitution.
       (Contributed by NM, 2-Nov-2006.) $)
    elrab2 $p |- ( A e. C <-> ( A e. B /\ ps ) ) $=
      cA cC wcel cA wph vx cB crab wcel cA cB wcel wps wa cC wph vx cB crab cA
      elrab2.2 eleq2i wph wps vx cA cB elrab2.1 elrab bitri $.
  $}

  ${
    $d x y $.  $d y A $.  $d y ps $.
    ralab.1 $e |- ( y = x -> ( ph <-> ps ) ) $.
    $( Universal quantification over a class abstraction.  (Contributed by Jeff
       Madsen, 10-Jun-2010.) $)
    ralab $p |- ( A. x e. { y | ph } ch <-> A. x ( ps -> ch ) ) $=
      wch vx wph vy cab wral vx cv wph vy cab wcel wch wi vx wal wps wch wi vx
      wal wch vx wph vy cab df-ral vx cv wph vy cab wcel wch wi wps wch wi vx
      vx cv wph vy cab wcel wps wch wph wps vy vx cv vx vex ralab.1 elab imbi1i
      albii bitri $.

    $( Universal quantification over a restricted class abstraction.
       (Contributed by Jeff Madsen, 10-Jun-2010.) $)
    ralrab $p |- ( A. x e. { y e. A | ph } ch <-> A. x e. A ( ps -> ch ) ) $=
      wch wps wch wi vx wph vy cA crab cA vx cv wph vy cA crab wcel wch wi vx
      cv cA wcel wps wa wch wi vx cv cA wcel wps wch wi wi vx cv wph vy cA crab
      wcel vx cv cA wcel wps wa wch wph wps vy vx cv cA ralab.1 elrab imbi1i vx
      cv cA wcel wps wch impexp bitri ralbii2 $.

    $( Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 23-Jan-2014.)  (Revised by Mario Carneiro,
       3-Sep-2015.) $)
    rexab $p |- ( E. x e. { y | ph } ch <-> E. x ( ps /\ ch ) ) $=
      wch vx wph vy cab wrex vx cv wph vy cab wcel wch wa vx wex wps wch wa vx
      wex wch vx wph vy cab df-rex vx cv wph vy cab wcel wch wa wps wch wa vx
      vx cv wph vy cab wcel wps wch wph wps vy vx cv vx vex ralab.1 elab anbi1i
      exbii bitri $.

    $( Existential quantification over a class abstraction.  (Contributed by
       Jeff Madsen, 17-Jun-2011.)  (Revised by Mario Carneiro, 3-Sep-2015.) $)
    rexrab $p |- ( E. x e. { y e. A | ph } ch <-> E. x e. A ( ps /\ ch ) ) $=
      wch wps wch wa vx wph vy cA crab cA vx cv wph vy cA crab wcel wch wa vx
      cv cA wcel wps wa wch wa vx cv cA wcel wps wch wa wa vx cv wph vy cA crab
      wcel vx cv cA wcel wps wa wch wph wps vy vx cv cA ralab.1 elrab anbi1i vx
      cv cA wcel wps wch anass bitri rexbii2 $.
  $}

  ${
    $d x y $.  $d x A $.  $d x ch $.  $d x ph $.  $d y ps $.
    ralab2.1 $e |- ( x = y -> ( ps <-> ch ) ) $.
    $( Universal quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)
    ralab2 $p |- ( A. x e. { y | ph } ps <-> A. y ( ph -> ch ) ) $=
      wps vx wph vy cab wral vx cv wph vy cab wcel wps wi vx wal wph wch wi vy
      wal wps vx wph vy cab df-ral vx cv wph vy cab wcel wps wi wph wch wi vx
      vy vx cv wph vy cab wcel wps vy wph vy vx nfsab1 wps vy nfv nfim wph wch
      wi vx nfv vx cv vy cv wceq vx cv wph vy cab wcel wph wps wch vx cv vy cv
      wceq vx cv wph vy cab wcel vy cv wph vy cab wcel wph vx cv vy cv wph vy
      cab eleq1 wph vy abid syl6bb ralab2.1 imbi12d cbval bitri $.

    $( Universal quantification over a restricted class abstraction.
       (Contributed by Mario Carneiro, 3-Sep-2015.) $)
    ralrab2 $p |- ( A. x e. { y e. A | ph } ps <-> A. y e. A ( ph -> ch ) ) $=
      wps vx wph vy cA crab wral wps vx vy cv cA wcel wph wa vy cab wral vy cv
      cA wcel wph wa wch wi vy wal wph wch wi vy cA wral wps vx wph vy cA crab
      vy cv cA wcel wph wa vy cab wph vy cA df-rab raleqi vy cv cA wcel wph wa
      wps wch vx vy ralab2.1 ralab2 vy cv cA wcel wph wa wch wi vy wal vy cv cA
      wcel wph wch wi wi vy wal wph wch wi vy cA wral vy cv cA wcel wph wa wch
      wi vy cv cA wcel wph wch wi wi vy vy cv cA wcel wph wch impexp albii wph
      wch wi vy cA df-ral bitr4i 3bitri $.

    $( Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)
    rexab2 $p |- ( E. x e. { y | ph } ps <-> E. y ( ph /\ ch ) ) $=
      wps vx wph vy cab wrex vx cv wph vy cab wcel wps wa vx wex wph wch wa vy
      wex wps vx wph vy cab df-rex vx cv wph vy cab wcel wps wa wph wch wa vx
      vy vx cv wph vy cab wcel wps vy wph vy vx nfsab1 wps vy nfv nfan wph wch
      wa vx nfv vx cv vy cv wceq vx cv wph vy cab wcel wph wps wch vx cv vy cv
      wceq vx cv wph vy cab wcel vy cv wph vy cab wcel wph vx cv vy cv wph vy
      cab eleq1 wph vy abid syl6bb ralab2.1 anbi12d cbvex bitri $.

    $( Existential quantification over a class abstraction.  (Contributed by
       Mario Carneiro, 3-Sep-2015.) $)
    rexrab2 $p |- ( E. x e. { y e. A | ph } ps <-> E. y e. A ( ph /\ ch ) ) $=
      wps vx wph vy cA crab wrex wps vx vy cv cA wcel wph wa vy cab wrex vy cv
      cA wcel wph wa wch wa vy wex wph wch wa vy cA wrex wps vx wph vy cA crab
      vy cv cA wcel wph wa vy cab wph vy cA df-rab rexeqi vy cv cA wcel wph wa
      wps wch vx vy ralab2.1 rexab2 vy cv cA wcel wph wa wch wa vy wex vy cv cA
      wcel wph wch wa wa vy wex wph wch wa vy cA wrex vy cv cA wcel wph wa wch
      wa vy cv cA wcel wph wch wa wa vy vy cv cA wcel wph wch anass exbii wph
      wch wa vy cA df-rex bitr4i 3bitri $.
  $}

  ${
    $d w y A $.  $d w x z $.  $d x y $.  $d A z $.
    $( Identity used to create closed-form versions of bound-variable
       hypothesis builders for class expressions.  (Contributed by NM,
       10-Nov-2005.)  (Proof shortened by Mario Carneiro, 12-Oct-2016.) $)
    abidnf $p |- ( F/_ x A -> { z | A. x z e. A } = A ) $=
      vx cA wnfc vz cv cA wcel vx wal vz cA vx cA wnfc vz cv cA wcel vx wal vz
      cv cA wcel vz cv cA wcel vx sp vx cA wnfc vz cv cA wcel vx vx vz cA nfcr
      nfrd impbid2 abbi1dv $.
  $}

  ${
    $d y A $.  $d x z $.  $d x y $.  $d z A $.
    dedhb.1 $e |- ( A = { z | A. x z e. A } -> ( ph <-> ps ) ) $.
    dedhb.2 $e |- ps $.
    $( A deduction theorem for converting the inference ` |- F/_ x A ` =>
       ` |- ph ` into a closed theorem.  Use ~ nfa1 and ~ nfab to eliminate the
       hypothesis of the substitution instance ` ps ` of the inference.  For
       converting the inference form into a deduction form, ~ abidnf is
       useful.  (Contributed by NM, 8-Dec-2006.) $)
    dedhb $p |- ( F/_ x A -> ph ) $=
      vx cA wnfc wph wps dedhb.2 vx cA wnfc cA vz cv cA wcel vx wal vz cab wceq
      wph wps wb vx cA wnfc vz cv cA wcel vx wal vz cab cA vx vz cA abidnf
      eqcomd dedhb.1 syl mpbiri $.
  $}

  ${
    $d y ph $.  $d x y ps $.  $d x y A $.
    eqeu.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( A condition which implies existential uniqueness.  (Contributed by Jeff
       Hankins, 8-Sep-2009.) $)
    eqeu $p |- ( ( A e. B /\ ps /\ A. x ( ph -> x = A ) ) -> E! x ph ) $=
      cA cB wcel wps wph vx cv cA wceq wi vx wal w3a wph vx wex wph vx cv vy cv
      wceq wi vx wal vy wex wph vx weu cA cB wcel wps wph vx wex wph vx cv cA
      wceq wi vx wal cA cB wcel wps wph vx wex wph wps vx cA cB eqeu.1 spcegv
      imp 3adant3 cA cB wcel wph vx cv cA wceq wi vx wal wph vx cv vy cv wceq
      wi vx wal vy wex wps cA cB wcel wph vx cv cA wceq wi vx wal wph vx cv vy
      cv wceq wi vx wal vy wex wph vx cv vy cv wceq wi vx wal wph vx cv cA wceq
      wi vx wal vy cA cB vy cv cA wceq wph vx cv vy cv wceq wi wph vx cv cA
      wceq wi vx vy cv cA wceq vx cv vy cv wceq vx cv cA wceq wph vy cv cA vx
      cv eqeq2 imbi2d albidv spcegv imp 3adant2 wph vx vy wph vy nfv eu3
      sylanbrc $.
  $}

  ${
    $d x y A $.
    $( Equality has existential uniqueness.  (Contributed by NM,
       25-Nov-1994.) $)
    eueq $p |- ( A e. _V <-> E! x x = A ) $=
      vx cv cA wceq vx wex vx cv cA wceq vx wex vx cv cA wceq vy cv cA wceq wa
      vx cv vy cv wceq wi vy wal vx wal wa cA cvv wcel vx cv cA wceq vx weu vx
      cv cA wceq vy cv cA wceq wa vx cv vy cv wceq wi vy wal vx wal vx cv cA
      wceq vx wex vx cv cA wceq vy cv cA wceq wa vx cv vy cv wceq wi vx vy vx
      cv vy cv cA eqtr3 gen2 biantru vx cA isset vx cv cA wceq vy cv cA wceq vx
      vy vx cv vy cv cA eqeq1 eu4 3bitr4i $.
  $}

  ${
    $d x A $.
    eueq1.1 $e |- A e. _V $.
    $( Equality has existential uniqueness.  (Contributed by NM,
       5-Apr-1995.) $)
    eueq1 $p |- E! x x = A $=
      cA cvv wcel vx cv cA wceq vx weu eueq1.1 vx cA eueq mpbi $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x B $.
    eueq2.1 $e |- A e. _V $.
    eueq2.2 $e |- B e. _V $.
    $( Equality has existential uniqueness (split into 2 cases).  (Contributed
       by NM, 5-Apr-1995.) $)
    eueq2 $p |- E! x ( ( ph /\ x = A ) \/ ( -. ph /\ x = B ) ) $=
      wph wph vx cv cA wceq wa wph wn vx cv cB wceq wa wo vx weu wph wph wn wph
      vx cv cA wceq wa wo vx weu wph vx cv cA wceq wa wph wn vx cv cB wceq wa
      wo vx weu wph wph wn wn wph vx cv cA wceq wa vx weu wph wn wph vx cv cA
      wceq wa wo vx weu wph notnot1 wph vx cv cA wceq vx weu wph vx cv cA wceq
      wa vx weu vx cA eueq2.1 eueq1 wph vx cv cA wceq wa vx weu wph vx cv cA
      wceq vx weu wa wph vx cv cA wceq vx euanv biimpri mpan2 wph wn wph vx cv
      cA wceq wa vx euorv syl2anc wph wph wn wph vx cv cA wceq wa wo wph vx cv
      cA wceq wa wph wn vx cv cB wceq wa wo vx wph wn wph vx cv cA wceq wa wo
      wph vx cv cA wceq wa wph wn wo wph wph vx cv cA wceq wa wph wn vx cv cB
      wceq wa wo wph wn wph vx cv cA wceq wa orcom wph wph wn wph wn vx cv cB
      wceq wa wph vx cv cA wceq wa wph wph wn vx cv cB wceq wph notnot1 bianfd
      orbi2d syl5bb eubidv mpbid wph wn wph wph wn vx cv cB wceq wa wo vx weu
      wph vx cv cA wceq wa wph wn vx cv cB wceq wa wo vx weu wph wn wph wn vx
      cv cB wceq wa vx weu wph wph wn vx cv cB wceq wa wo vx weu wph wn vx cv
      cB wceq vx weu wph wn vx cv cB wceq wa vx weu vx cB eueq2.2 eueq1 wph wn
      vx cv cB wceq wa vx weu wph wn vx cv cB wceq vx weu wa wph wn vx cv cB
      wceq vx euanv biimpri mpan2 wph wph wn vx cv cB wceq wa vx euorv mpdan
      wph wn wph wph wn vx cv cB wceq wa wo wph vx cv cA wceq wa wph wn vx cv
      cB wceq wa wo vx wph wn wph wph vx cv cA wceq wa wph wn vx cv cB wceq wa
      wph wn wph vx cv cA wceq wph wn id bianfd orbi1d eubidv mpbid pm2.61i $.
  $}

  ${
    $d x ph $.  $d x ps $.  $d x A $.  $d x B $.  $d x C $.
    eueq3.1 $e |- A e. _V $.
    eueq3.2 $e |- B e. _V $.
    eueq3.3 $e |- C e. _V $.
    eueq3.4 $e |- -. ( ph /\ ps ) $.
    $( Equality has existential uniqueness (split into 3 cases).  (Contributed
       by NM, 5-Apr-1995.)  (Proof shortened by Mario Carneiro,
       28-Sep-2015.) $)
    eueq3 $p |- E! x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B )
                \/ ( ps /\ x = C ) ) $=
      wph wps wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC
      wceq wa w3o vx weu wph vx cv cA wceq vx weu wph vx cv cA wceq wa wph wps
      wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx weu vx cA eueq3.1
      eueq1 wph vx cv cA wceq wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq
      wa wps vx cv cC wceq wa w3o vx wph vx cv cA wceq wph wps wo wn vx cv cB
      wceq wa wps vx cv cC wceq wa wo wph vx cv cA wceq wa wo wph vx cv cA wceq
      wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wph vx cv cA
      wceq wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC
      wceq wa wo wph vx cv cA wceq wa wo wph vx cv cA wceq ibar wph wph wps wo
      wn vx cv cB wceq wa wps vx cv cC wceq wa wo wn wph vx cv cA wceq wa wph
      wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa wo wph vx cv cA wceq wa
      wo wb wph wph wps wo wn wps wo wph wps wo wn vx cv cB wceq wa wps vx cv
      cC wceq wa wo wph wps wo wn wps wo wph wph wps wo wn wph wn wps wph wps
      pm2.45 wph wps wph wps eueq3.4 imnani con2i jaoi con2i wph wph wps wo wn
      wph wps wo wn vx cv cB wceq wa wps wps vx cv cC wceq wa wph wph wps wo wn
      vx cv cB wceq wph wps wo wn wph wph wps pm2.45 con2i bianfd wph wps vx cv
      cC wceq wph wps eueq3.4 imnani bianfd orbi12d mtbid wph wps wo wn vx cv
      cB wceq wa wps vx cv cC wceq wa wo wph vx cv cA wceq wa biorf syl bitrd
      wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa
      w3o wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa wph vx cv cA wceq
      wa w3o wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa wo wph vx cv
      cA wceq wa wo wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx
      cv cC wceq wa 3orrot wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa
      wph vx cv cA wceq wa df-3or bitri syl6bbr eubidv mpbii wps vx cv cC wceq
      vx weu wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC
      wceq wa w3o vx weu vx cC eueq3.3 eueq1 wps vx cv cC wceq wph vx cv cA
      wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx wps vx
      cv cC wceq wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wo wps vx
      cv cC wceq wa wo wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps
      vx cv cC wceq wa w3o wps vx cv cC wceq wps vx cv cC wceq wa wph vx cv cA
      wceq wa wph wps wo wn vx cv cB wceq wa wo wps vx cv cC wceq wa wo wps vx
      cv cC wceq ibar wps wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa
      wo wn wps vx cv cC wceq wa wph vx cv cA wceq wa wph wps wo wn vx cv cB
      wceq wa wo wps vx cv cC wceq wa wo wb wph vx cv cA wceq wa wph wps wo wn
      vx cv cB wceq wa wo wps wph vx cv cA wceq wa wps wn wph wps wo wn vx cv
      cB wceq wa wph wps wn vx cv cA wceq wph wps eueq3.4 imnani adantr wph wps
      wo wn wps wn vx cv cB wceq wph wps pm2.46 adantr jaoi con2i wph vx cv cA
      wceq wa wph wps wo wn vx cv cB wceq wa wo wps vx cv cC wceq wa biorf syl
      bitrd wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC
      wceq wa df-3or syl6bbr eubidv mpbii wph wps wo wn vx cv cB wceq vx weu
      wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa
      w3o vx weu vx cB eueq3.2 eueq1 wph wps wo wn vx cv cB wceq wph vx cv cA
      wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx wph
      wps wo wn vx cv cB wceq wph vx cv cA wceq wa wps vx cv cC wceq wa wo wph
      wps wo wn vx cv cB wceq wa wo wph vx cv cA wceq wa wph wps wo wn vx cv cB
      wceq wa wps vx cv cC wceq wa w3o wph wps wo wn vx cv cB wceq wph wps wo
      wn vx cv cB wceq wa wph vx cv cA wceq wa wps vx cv cC wceq wa wo wph wps
      wo wn vx cv cB wceq wa wo wph wps wo wn vx cv cB wceq ibar wph wps wo wn
      wph vx cv cA wceq wa wps vx cv cC wceq wa wo wn wph wps wo wn vx cv cB
      wceq wa wph vx cv cA wceq wa wps vx cv cC wceq wa wo wph wps wo wn vx cv
      cB wceq wa wo wb wph vx cv cA wceq wa wps vx cv cC wceq wa wo wph wps wo
      wph vx cv cA wceq wa wph wps vx cv cC wceq wa wps wph vx cv cA wceq simpl
      wps vx cv cC wceq simpl orim12i con3i wph vx cv cA wceq wa wps vx cv cC
      wceq wa wo wph wps wo wn vx cv cB wceq wa biorf syl bitrd wph vx cv cA
      wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wph vx cv
      cA wceq wa wps vx cv cC wceq wa wph wps wo wn vx cv cB wceq wa w3o wph vx
      cv cA wceq wa wps vx cv cC wceq wa wo wph wps wo wn vx cv cB wceq wa wo
      wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa
      3orcomb wph vx cv cA wceq wa wps vx cv cC wceq wa wph wps wo wn vx cv cB
      wceq wa df-3or bitri syl6bbr eubidv mpbii ecase3 $.
  $}

  ${
    $d x A $.
    $( There is at most one set equal to a class.  (Contributed by NM,
       8-Mar-1995.) $)
    moeq $p |- E* x x = A $=
      vx cv cA wceq vx wmo vx cv cA wceq vx wex vx cv cA wceq vx weu wi vx cv
      cA wceq vx wex vx cv cA wceq vx weu vx cv cA wceq vx wex cA cvv wcel vx
      cv cA wceq vx weu vx cA isset vx cA eueq bitr3i biimpi vx cv cA wceq vx
      df-mo mpbir $.
  $}

  ${
    $d x y ph $.  $d x y ps $.  $d x y A $.  $d x y B $.  $d x y C $.
    moeq3.1 $e |- B e. _V $.
    moeq3.2 $e |- C e. _V $.
    moeq3.3 $e |- -. ( ph /\ ps ) $.
    $( "At most one" property of equality (split into 3 cases).  (The first 2
       hypotheses could be eliminated with longer proof.)  (Contributed by NM,
       23-Apr-1995.) $)
    moeq3 $p |- E* x ( ( ph /\ x = A ) \/ ( -. ( ph \/ ps ) /\ x = B )
                \/ ( ps /\ x = C ) ) $=
      cA cvv wcel wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv
      cC wceq wa w3o vx wmo cA cvv wcel wph vx cv cA wceq wa wph wps wo wn vx
      cv cB wceq wa wps vx cv cC wceq wa w3o vx weu wph vx cv cA wceq wa wph
      wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx wmo wph vx cv vy
      cv wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx weu
      wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa
      w3o vx weu vy cA cvv vy cv cA wceq wph vx cv vy cv wceq wa wph wps wo wn
      vx cv cB wceq wa wps vx cv cC wceq wa w3o wph vx cv cA wceq wa wph wps wo
      wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx vy cv cA wceq wph vx cv
      vy cv wceq wa wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wph wps
      wo wn vx cv cB wceq wa wps vx cv cC wceq wa wps vx cv cC wceq wa vy cv cA
      wceq vx cv vy cv wceq vx cv cA wceq wph vy cv cA vx cv eqeq2 anbi2d vy cv
      cA wceq wph wps wo wn vx cv cB wceq wa biidd vy cv cA wceq wps vx cv cC
      wceq wa biidd 3orbi123d eubidv wph wps vx vy cv cB cC vy vex moeq3.1
      moeq3.2 moeq3.3 eueq3 vtoclg wph vx cv cA wceq wa wph wps wo wn vx cv cB
      wceq wa wps vx cv cC wceq wa w3o vx eumo syl cA cvv wcel wn wph vx cv cA
      wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wph vx cv
      vy cv wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wi
      vx wal wph vx cv vy cv wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv
      cC wceq wa w3o vx weu wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa
      wps vx cv cC wceq wa w3o vx wmo cA cvv wcel wn wph vx cv cA wceq wa wph
      wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wph vx cv vy cv wceq
      wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wi vx cA cvv
      wcel wn wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC
      wceq wa wo wo wph vx cv vy cv wceq wa wph wps wo wn vx cv cB wceq wa wps
      vx cv cC wceq wa wo wo wph vx cv cA wceq wa wph wps wo wn vx cv cB wceq
      wa wps vx cv cC wceq wa w3o wph vx cv vy cv wceq wa wph wps wo wn vx cv
      cB wceq wa wps vx cv cC wceq wa w3o cA cvv wcel wn wph vx cv cA wceq wa
      wph vx cv vy cv wceq wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq
      wa wo cA cvv wcel wn vx cv cA wceq vx cv vy cv wceq wph vx cv cA wceq cA
      cvv wcel cA cvv wcel wn vx cv vy cv wceq vx cv cA wceq vx cv cvv wcel cA
      cvv wcel vx vex vx cv cA cvv eleq1 mpbii cA cvv wcel vx cv vy cv wceq
      pm2.21 syl5 anim2d orim1d wph vx cv cA wceq wa wph wps wo wn vx cv cB
      wceq wa wps vx cv cC wceq wa 3orass wph vx cv vy cv wceq wa wph wps wo wn
      vx cv cB wceq wa wps vx cv cC wceq wa 3orass 3imtr4g alrimiv wph wps vx
      vy cv cB cC vy vex moeq3.1 moeq3.2 moeq3.3 eueq3 wph vx cv cA wceq wa wph
      wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o wph vx cv vy cv wceq
      wa wph wps wo wn vx cv cB wceq wa wps vx cv cC wceq wa w3o vx euimmo ee10
      pm2.61i $.
  $}

  ${
    $d x y A $.
    mosub.1 $e |- E* x ph $.
    $( "At most one" remains true after substitution.  (Contributed by NM,
       9-Mar-1995.) $)
    mosub $p |- E* x E. y ( y = A /\ ph ) $=
      vy cv cA wceq vy wmo wph vx wmo vy wal vy cv cA wceq wph wa vy wex vx wmo
      vy cA moeq wph vx wmo vy mosub.1 ax-gen vy cv cA wceq wph vy vx moexexv
      mp2an $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( Theorem for inferring "at most one."  (Contributed by NM,
       17-Oct-1996.) $)
    mo2icl $p |- ( A. x ( ph -> x = A ) -> E* x ph ) $=
      cA cvv wcel wph vx cv cA wceq wi vx wal wph vx wmo wi wph vx cv vy cv
      wceq wi vx wal wph vx wmo wi wph vx cv cA wceq wi vx wal wph vx wmo wi vy
      cA cvv vy cv cA wceq wph vx cv vy cv wceq wi vx wal wph vx cv cA wceq wi
      vx wal wph vx wmo vy cv cA wceq wph vx cv vy cv wceq wi wph vx cv cA wceq
      wi vx vy cv cA wceq vx cv vy cv wceq vx cv cA wceq wph vy cv cA vx cv
      eqeq2 imbi2d albidv imbi1d wph vx cv vy cv wceq wi vx wal wph vx cv vy cv
      wceq wi vx wal vy wex wph vx wmo wph vx cv vy cv wceq wi vx wal vy 19.8a
      wph vx vy wph vy nfv mo2 sylibr vtoclg cA cvv wcel wn wph vx cv cA wceq
      wi vx wal wph wn vx wal wph vx wmo cA cvv wcel wn wph vx cv cA wceq wi
      wph wn vx wph vx cv cA wceq wi wph cA cvv wcel vx cv cA wceq cA cvv wcel
      wph vx cv cA wceq vx cv cvv wcel cA cvv wcel vx vex vx cv cA cvv eleq1
      mpbii imim2i con3rr3 alimdv wph wn vx wal wph vx wex wn wph vx wmo wph vx
      alnex wph vx wex wph vx wmo wph vx exmo ori sylbi syl6 pm2.61i $.
  $}

  ${
    $d x y A $.  $d y ph $.  $d x y ps $.
    moi2.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Consequence of "at most one."  (Contributed by NM, 2-Jan-2015.) $)
    mob2 $p |- ( ( A e. B /\ E* x ph /\ ph ) -> ( x = A <-> ps ) ) $=
      cA cB wcel wph vx wmo wph w3a vx cv cA wceq wps cA cB wcel wph vx wmo wph
      w3a wph vx cv cA wceq wps cA cB wcel wph vx wmo wph simp3 moi2.1
      syl5ibcom cA cB wcel wph vx wmo wph wps vx cv cA wceq wi cA cB wcel wph
      vx wmo wa wph wps vx cv cA wceq cA cB wcel wph vx wmo wph wps wa vx cv cA
      wceq wi wph vx wmo wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal cA cB
      wcel wph wps wa vx cv cA wceq wi wph vx wmo wph wph vx vy wsb wa vx cv vy
      cv wceq wi vy wal vx wal wph wph vx vy wsb wa vx cv vy cv wceq wi vy wal
      wph wph vx vy wsb vx vy wph vx vy nfs1v wph vx vy sbequ12 mo4f wph wph vx
      vy wsb wa vx cv vy cv wceq wi vy wal vx sp sylbi wph wph vx vy wsb wa vx
      cv vy cv wceq wi wph wps wa vx cv cA wceq wi vy cA cB vy cv cA wceq wph
      wph vx vy wsb wa wph wps wa vx cv vy cv wceq vx cv cA wceq vy cv cA wceq
      wph vx vy wsb wps wph wph wps vx vy cA wps vx nfv moi2.1 sbhypf anbi2d vy
      cv cA vx cv eqeq2 imbi12d spcgv syl5 imp exp3a 3impia impbid $.

    $( Consequence of "at most one."  (Contributed by NM, 29-Jun-2008.) $)
    moi2 $p |- ( ( ( A e. B /\ E* x ph ) /\ ( ph /\ ps ) ) -> x = A ) $=
      cA cB wcel wph vx wmo wa wph wps vx cv cA wceq cA cB wcel wph vx wmo wa
      wph wa vx cv cA wceq wps cA cB wcel wph vx wmo wph vx cv cA wceq wps wb
      wph wps vx cA cB moi2.1 mob2 3expa biimprd impr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ch $.  $d y ph $.  $d x y ps $.
    moi.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    moi.2 $e |- ( x = B -> ( ph <-> ch ) ) $.
    $( Equality implied by "at most one."  (Contributed by NM, 18-Feb-2006.) $)
    mob $p |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ps ) ->
                ( A = B <-> ch ) ) $=
      cA cC wcel cB cD wcel wa wph vx wmo wps cA cB wceq wch wb cA cC wcel cB
      cD wcel wph vx wmo wps wa cA cB wceq wch wb wi cB cD wcel wph vx wmo wps
      wa cA cC wcel cA cB wceq wch wb cB cD wcel cB cvv wcel wph vx wmo wps wa
      cA cC wcel cA cB wceq wch wb wi wi cB cD elex cB cvv wcel wph vx wmo wps
      cA cC wcel cA cB wceq wch wb wi cA cC wcel cB cvv wcel wph vx wmo wps w3a
      cA cB wceq wch wb cB cvv wcel wph vx wmo wph w3a vx cv cB wceq wch wb wi
      cB cvv wcel wph vx wmo wps w3a cA cB wceq wch wb wi vx cA cC vx cA nfcv
      cB cvv wcel wph vx wmo wps w3a cA cB wceq wch wb vx cB cvv wcel wph vx
      wmo wps vx cB cvv wcel vx nfv wph vx nfmo1 wps vx nfv nf3an cA cB wceq
      wch wb vx nfv nfim vx cv cA wceq cB cvv wcel wph vx wmo wph w3a cB cvv
      wcel wph vx wmo wps w3a vx cv cB wceq wch wb cA cB wceq wch wb vx cv cA
      wceq wph wps cB cvv wcel wph vx wmo moi.1 3anbi3d vx cv cA wceq vx cv cB
      wceq cA cB wceq wch vx cv cA cB eqeq1 bibi1d imbi12d wph wch vx cB cvv
      moi.2 mob2 vtoclgf com12 3expib syl com3r imp 3impib $.

    $( Equality implied by "at most one."  (Contributed by NM, 18-Feb-2006.) $)
    moi $p |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ( ps /\ ch ) ) ->
              A = B ) $=
      cA cC wcel cB cD wcel wa wph vx wmo wps wch wa cA cB wceq cA cC wcel cB
      cD wcel wa wph vx wmo wa wps wch cA cB wceq cA cC wcel cB cD wcel wa wph
      vx wmo wps wch cA cB wceq wi cA cC wcel cB cD wcel wa wph vx wmo wps w3a
      cA cB wceq wch wph wps wch vx cA cB cC cD moi.1 moi.2 mob biimprd 3expia
      imp3a 3impia $.
  $}

  ${
    $d B x y $.  $d A x y $.  $d ph y $.  $d ps x y $.
    morex.1 $e |- B e. _V $.
    morex.2 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( Derive membership from uniqueness.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    morex $p |- ( ( E. x e. A ph /\ E* x ph ) -> ( ps -> B e. A ) ) $=
      wph vx wmo wph vx cA wrex wps cB cA wcel wi wph vx cA wrex wph vx wmo wph
      vx cv cA wcel wa vx wex wps cB cA wcel wi wph vx cA wrex vx cv cA wcel
      wph wa vx wex wph vx cv cA wcel wa vx wex wph vx cA df-rex vx cv cA wcel
      wph vx exancom bitri wph vx wmo wph vx cv cA wcel wa vx wex wa wph vx cv
      cA wcel wi vx wal wps cB cA wcel wi wph vx wmo wph vx cv cA wcel wa vx
      wex wa wph vx cv cA wcel wi vx wph vx wmo wph vx cv cA wcel wa vx wex vx
      wph vx nfmo1 wph vx cv cA wcel wa vx nfe1 nfan wph vx cv cA wcel vx
      mopick alrimi wph vx cv cA wcel wi wps cB cA wcel wi vx cB morex.1 vx cv
      cB wceq wph wps vx cv cA wcel cB cA wcel morex.2 vx cv cB cA eleq1
      imbi12d spcv syl sylan2b ancoms $.
  $}

  ${
    $d x ph $.  $d x A $.
    euxfr2.1 $e |- A e. _V $.
    euxfr2.2 $e |- E* y x = A $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.) $)
    euxfr2 $p |- ( E! x E. y ( x = A /\ ph ) <-> E! y ph ) $=
      vx cv cA wceq wph wa vy wex vx weu vx cv cA wceq wph wa vx wex vy weu wph
      vy weu vx cv cA wceq wph wa vy wex vx weu vx cv cA wceq wph wa vx wex vy
      weu vx cv cA wceq wph wa vy wmo vx cv cA wceq wph wa vy wex vx weu vx cv
      cA wceq wph wa vx wex vy weu wi vx vx cv cA wceq wph wa vx vy 2euswap wph
      vx cv cA wceq wa vy wmo vx cv cA wceq wph wa vy wmo vx cv cA wceq wph vy
      euxfr2.2 moani wph vx cv cA wceq wa vx cv cA wceq wph wa vy wph vx cv cA
      wceq ancom mobii mpbi mpg vx cv cA wceq wph wa vx wmo vx cv cA wceq wph
      wa vx wex vy weu vx cv cA wceq wph wa vy wex vx weu wi vy vx cv cA wceq
      wph wa vy vx 2euswap wph vx cv cA wceq wa vx wmo vx cv cA wceq wph wa vx
      wmo vx cv cA wceq wph vx vx cA moeq moani wph vx cv cA wceq wa vx cv cA
      wceq wph wa vx wph vx cv cA wceq ancom mobii mpbi mpg impbii vx cv cA
      wceq wph wa vx wex wph vy wph wph vx cA euxfr2.1 vx cv cA wceq wph biidd
      ceqsexv eubii bitri $.
  $}

  ${
    $d x ps $.  $d y ph $.  $d x A $.
    euxfr.1 $e |- A e. _V $.
    euxfr.2 $e |- E! y x = A $.
    euxfr.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Transfer existential uniqueness from a variable ` x ` to another
       variable ` y ` contained in expression ` A ` .  (Contributed by NM,
       14-Nov-2004.) $)
    euxfr $p |- ( E! x ph <-> E! y ps ) $=
      wph vx weu vx cv cA wceq wps wa vy wex vx weu wps vy weu wph vx cv cA
      wceq wps wa vy wex vx wph vx cv cA wceq vy wex wph wa vx cv cA wceq wph
      wa vy wex vx cv cA wceq wps wa vy wex vx cv cA wceq vy wex wph vx cv cA
      wceq vy weu vx cv cA wceq vy wex euxfr.2 vx cv cA wceq vy euex ax-mp
      biantrur vx cv cA wceq wph vy 19.41v vx cv cA wceq wph wa vx cv cA wceq
      wps wa vy vx cv cA wceq wph wps euxfr.3 pm5.32i exbii 3bitr2i eubii wps
      vx vy cA euxfr.1 vx cv cA wceq vy euxfr.2 eumoi euxfr2 bitri $.
  $}

  ${
    $d y z w ph $.  $d x z ps $.  $d y z w A $.  $d x z B $.  $d x y w $.
    euind.1 $e |- B e. _V $.
    euind.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    euind.3 $e |- ( x = y -> A = B ) $.
    $( Existential uniqueness via an indirect equality.  (Contributed by NM,
       11-Oct-2010.) $)
    euind $p |- ( ( A. x A. y ( ( ph /\ ps ) -> A = B ) /\ E. x ph )
                 -> E! z A. x ( ph -> z = A ) ) $=
      wph wps wa cA cB wceq wi vy wal vx wal wph vx wex wa wph vz cv cA wceq wi
      vx wal vz wex wph vz cv cA wceq wi vx wal wph vw cv cA wceq wi vx wal wa
      vz cv vw cv wceq wi vw wal vz wal wph vz cv cA wceq wi vx wal vz weu wph
      wps wa cA cB wceq wi vy wal vx wal wph vx wex wph vz cv cA wceq wi vx wal
      vz wex wph vx wex vz cv cB wceq wps wa vy wex vz wex wph wps wa cA cB
      wceq wi vy wal vx wal wph vz cv cA wceq wi vx wal vz wex wph vx wex wps
      vy wex vz cv cB wceq wps wa vy wex vz wex wph wps vx vy euind.2 cbvexv
      wps vy wex vz cv cB wceq vz wex wps wa vy wex vz cv cB wceq wps wa vy wex
      vz wex wps vz cv cB wceq vz wex wps wa vy vz cv cB wceq vz wex wps vz cB
      euind.1 isseti biantrur exbii vz cv cB wceq vz wex wps wa vy wex vz cv cB
      wceq wps wa vz wex vy wex vz cv cB wceq wps wa vy wex vz wex vz cv cB
      wceq wps wa vz wex vz cv cB wceq vz wex wps wa vy vz cv cB wceq wps vz
      19.41v exbii vz cv cB wceq wps wa vy vz excom bitr3i bitri bitri wph wps
      wa cA cB wceq wi vy wal vx wal vz cv cB wceq wps wa vy wex wph vz cv cA
      wceq wi vx wal vz wph wps wa cA cB wceq wi vy wal vx wal vz cv cB wceq
      wps wa wph vz cv cA wceq wi wi vy wal vx wal vz cv cB wceq wps wa vy wex
      wph vz cv cA wceq wi vx wal wi wph wps wa cA cB wceq wi vz cv cB wceq wps
      wa wph vz cv cA wceq wi wi vx vy wph wps wa cA cB wceq wi wph wps wa vz
      cv cA wceq vz cv cB wceq wb wi vz cv cB wceq wps wa wph vz cv cA wceq wi
      wi cA cB wceq vz cv cA wceq vz cv cB wceq wb wph wps wa cA cB vz cv eqeq2
      imim2i wph wps wa vz cv cA wceq vz cv cB wceq wb wi wph wps wa vz cv cB
      wceq vz cv cA wceq wi wi vz cv cB wceq wps wa wph vz cv cA wceq wi wi vz
      cv cA wceq vz cv cB wceq wb vz cv cB wceq vz cv cA wceq wi wph wps wa vz
      cv cA wceq vz cv cB wceq bi2 imim2i wph wps wa vz cv cB wceq wa vz cv cA
      wceq wi vz cv cB wceq wps wa wph wa vz cv cA wceq wi wph wps wa vz cv cB
      wceq vz cv cA wceq wi wi vz cv cB wceq wps wa wph vz cv cA wceq wi wi wph
      wps wa vz cv cB wceq wa vz cv cB wceq wps wa wph wa vz cv cA wceq wph wps
      vz cv cB wceq an31 imbi1i wph wps wa vz cv cB wceq vz cv cA wceq impexp
      vz cv cB wceq wps wa wph vz cv cA wceq impexp 3bitr3i sylib syl 2alimi vz
      cv cB wceq wps wa wph vz cv cA wceq wi wi vy wal vx wal vz cv cB wceq wps
      wa vy wex wph vz cv cA wceq wi wi vx wal vz cv cB wceq wps wa vy wex wph
      vz cv cA wceq wi vx wal wi vz cv cB wceq wps wa wph vz cv cA wceq wi wi
      vy wal vz cv cB wceq wps wa vy wex wph vz cv cA wceq wi wi vx vz cv cB
      wceq wps wa wph vz cv cA wceq wi vy 19.23v albii vz cv cB wceq wps wa vy
      wex wph vz cv cA wceq wi vx 19.21v bitri sylib eximdv syl5bi imp wph vx
      wex wph vz cv cA wceq wi vx wal wph vw cv cA wceq wi vx wal wa vz cv vw
      cv wceq wi vw wal vz wal wph wps wa cA cB wceq wi vy wal vx wal wph vx
      wex wph vz cv cA wceq wi vx wal wph vw cv cA wceq wi vx wal wa vz cv vw
      cv wceq wi vz vw wph vz cv cA wceq wi vx wal wph vw cv cA wceq wi vx wal
      wa wph vz cv vw cv wceq wi vx wal wph vx wex vz cv vw cv wceq wph vz cv
      cA wceq wi wph vw cv cA wceq wi wph vz cv vw cv wceq wi vx wph wph wph wa
      wph vz cv cA wceq wi wph vw cv cA wceq wi wa vz cv cA wceq vw cv cA wceq
      wa vz cv vw cv wceq wph wph wph wa wph pm4.24 biimpi wph vz cv cA wceq
      wph vw cv cA wceq prth vz cv vw cv cA eqtr3 syl56 alanimi wph vz cv vw cv
      wceq wi vx wal wph vx wex vz cv vw cv wceq wph vz cv vw cv wceq wi vx wal
      wph vx wex vz cv vw cv wceq wi wph vz cv vw cv wceq vx 19.23v biimpi
      com12 syl5 alrimivv adantl wph vz cv cA wceq wi vx wal wph vw cv cA wceq
      wi vx wal vz vw vz cv vw cv wceq wph vz cv cA wceq wi wph vw cv cA wceq
      wi vx vz cv vw cv wceq vz cv cA wceq vw cv cA wceq wph vz cv vw cv cA
      eqeq1 imbi2d albidv eu4 sylanbrc $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y ph $.  $d x ps $.
    $( A way to express restricted uniqueness.  (Contributed by NM,
       22-Nov-1994.) $)
    reu2 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\
               A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) ) $=
      vx cv cA wcel wph wa vx weu vx cv cA wcel wph wa vx wex vx cv cA wcel wph
      wa vx cv cA wcel wph wa vx vy wsb wa vx cv vy cv wceq wi vy wal vx wal wa
      wph vx cA wreu wph vx cA wrex wph wph vx vy wsb wa vx cv vy cv wceq wi vy
      cA wral vx cA wral wa vx cv cA wcel wph wa vx vy vx cv cA wcel wph wa vy
      nfv eu2 wph vx cA df-reu wph vx cA wrex vx cv cA wcel wph wa vx wex wph
      wph vx vy wsb wa vx cv vy cv wceq wi vy cA wral vx cA wral vx cv cA wcel
      wph wa vx cv cA wcel wph wa vx vy wsb wa vx cv vy cv wceq wi vy wal vx
      wal wph vx cA df-rex wph wph vx vy wsb wa vx cv vy cv wceq wi vy cA wral
      vx cA wral vx cv cA wcel wph wph vx vy wsb wa vx cv vy cv wceq wi vy cA
      wral wi vx wal vx cv cA wcel wph wa vx cv cA wcel wph wa vx vy wsb wa vx
      cv vy cv wceq wi vy wal vx wal wph wph vx vy wsb wa vx cv vy cv wceq wi
      vy cA wral vx cA df-ral vx cv cA wcel wph wa vx cv cA wcel wph wa vx vy
      wsb wa vx cv vy cv wceq wi vy wal vx cv cA wcel wph wph vx vy wsb wa vx
      cv vy cv wceq wi vy cA wral wi vx vx cv cA wcel vy cv cA wcel wph wph vx
      vy wsb wa vx cv vy cv wceq wi wi wi vy wal vx cv cA wcel vy cv cA wcel
      wph wph vx vy wsb wa vx cv vy cv wceq wi wi vy wal wi vx cv cA wcel wph
      wa vx cv cA wcel wph wa vx vy wsb wa vx cv vy cv wceq wi vy wal vx cv cA
      wcel wph wph vx vy wsb wa vx cv vy cv wceq wi vy cA wral wi vx cv cA wcel
      vy cv cA wcel wph wph vx vy wsb wa vx cv vy cv wceq wi wi vy 19.21v vx cv
      cA wcel wph wa vx cv cA wcel wph wa vx vy wsb wa vx cv vy cv wceq wi vx
      cv cA wcel vy cv cA wcel wph wph vx vy wsb wa vx cv vy cv wceq wi wi wi
      vy vx cv cA wcel wph wa vx cv cA wcel wph wa vx vy wsb wa vx cv vy cv
      wceq wi vx cv cA wcel vy cv cA wcel wa wph wph vx vy wsb wa wa vx cv vy
      cv wceq wi vx cv cA wcel vy cv cA wcel wa wph wph vx vy wsb wa vx cv vy
      cv wceq wi wi vx cv cA wcel vy cv cA wcel wph wph vx vy wsb wa vx cv vy
      cv wceq wi wi wi vx cv cA wcel wph wa vx cv cA wcel wph wa vx vy wsb wa
      vx cv cA wcel vy cv cA wcel wa wph wph vx vy wsb wa wa vx cv vy cv wceq
      vx cv cA wcel wph wa vx cv cA wcel wph wa vx vy wsb wa vx cv cA wcel wph
      wa vy cv cA wcel wph vx vy wsb wa wa vx cv cA wcel vy cv cA wcel wa wph
      wph vx vy wsb wa wa vx cv cA wcel wph wa vx vy wsb vy cv cA wcel wph vx
      vy wsb wa vx cv cA wcel wph wa vx cv cA wcel wph wa vy cv cA wcel wph vx
      vy wsb wa vx vy vy cv cA wcel wph vx vy wsb vx vy cv cA wcel vx nfv wph
      vx vy nfs1v nfan vx cv vy cv wceq vx cv cA wcel vy cv cA wcel wph wph vx
      vy wsb vx cv vy cv cA eleq1 wph vx vy sbequ12 anbi12d sbie anbi2i vx cv
      cA wcel wph vy cv cA wcel wph vx vy wsb an4 bitri imbi1i vx cv cA wcel vy
      cv cA wcel wa wph wph vx vy wsb wa vx cv vy cv wceq impexp vx cv cA wcel
      vy cv cA wcel wph wph vx vy wsb wa vx cv vy cv wceq wi impexp 3bitri
      albii wph wph vx vy wsb wa vx cv vy cv wceq wi vy cA wral vy cv cA wcel
      wph wph vx vy wsb wa vx cv vy cv wceq wi wi vy wal vx cv cA wcel wph wph
      vx vy wsb wa vx cv vy cv wceq wi vy cA df-ral imbi2i 3bitr4i albii bitr4i
      anbi12i 3bitr4i $.

    $( A way to express restricted uniqueness.  (Contributed by NM,
       20-Oct-2006.) $)
    reu6 $p |- ( E! x e. A ph <-> E. y e. A A. x e. A ( ph <-> x = y ) ) $=
      wph vx cA wreu vx cv cA wcel wph wa vx weu wph vx cv vy cv wceq wb vx cA
      wral vy cA wrex wph vx cA df-reu vx cv cA wcel wph wa vx cv vy cv wceq wb
      vx wal vy wex vy cv cA wcel wph vx cv vy cv wceq wb vx cA wral wa vy wex
      vx cv cA wcel wph wa vx weu wph vx cv vy cv wceq wb vx cA wral vy cA wrex
      vx cv cA wcel wph wa vx cv vy cv wceq wb vx wal vy cv cA wcel wph vx cv
      vy cv wceq wb vx cA wral wa vy vy cv cA wcel vx cv cA wcel wph vx cv vy
      cv wceq wb wi wa vx wal vy cv cA wcel vx cv cA wcel wph vx cv vy cv wceq
      wb wi vx wal wa vx cv cA wcel wph wa vx cv vy cv wceq wb vx wal vy cv cA
      wcel wph vx cv vy cv wceq wb vx cA wral wa vy cv cA wcel vx cv cA wcel
      wph vx cv vy cv wceq wb wi vx 19.28v vx cv cA wcel wph wa vx cv vy cv
      wceq wb vx wal vy cv cA wcel vx cv cA wcel wph vx cv vy cv wceq wb wi wa
      vx wal vx cv cA wcel wph wa vx cv vy cv wceq wb vy cv cA wcel vx cv cA
      wcel wph vx cv vy cv wceq wb wi wa vx vx cv cA wcel wph wa vx cv vy cv
      wceq wb vx wal vy cv cA wcel vx cv cA wcel wph vx cv vy cv wceq wb wi vx
      cv cA wcel wph wa vx cv vy cv wceq wb vy cv cA wcel vx vy vx cv vy cv
      wceq vx cv cA wcel wph wa vx cv vy cv wceq wb vy cv cA wcel wph vx vy wsb
      wa vy cv vy cv wceq wb vy cv cA wcel vx cv vy cv wceq vx cv cA wcel wph
      wa vy cv cA wcel wph vx vy wsb wa vx cv vy cv wceq vy cv vy cv wceq vx cv
      vy cv wceq vx cv cA wcel vy cv cA wcel wph wph vx vy wsb vx cv vy cv cA
      eleq1 wph vx vy sbequ12 anbi12d vx cv vy cv vy cv eqeq1 bibi12d vy cv cA
      wcel wph vx vy wsb wa vy cv vy cv wceq wb vy cv cA wcel wph vx vy wsb wa
      vy cv cA wcel vy cv vy cv wceq vy cv cA wcel wph vx vy wsb wa vy cv eqid
      tbt vy cv cA wcel wph vx vy wsb simpl sylbir syl6bi spimv vx cv cA wcel
      wph wa vx cv vy cv wceq wb vx cv cA wcel wph vx cv vy cv wceq wb wi vx vx
      cv cA wcel wph wa vx cv vy cv wceq wb vx cv cA wcel wph vx cv vy cv wceq
      wb vx cv cA wcel wph wa vx cv vy cv wceq wb vx cv cA wcel wa wph vx cv vy
      cv wceq vx cv cA wcel wph wa vx cv vy cv wceq wb vx cv cA wcel wph vx cv
      vy cv wceq vx cv cA wcel wph wa vx cv vy cv wceq bi1 expdimp vx cv cA
      wcel wph wa vx cv vy cv wceq wb vx cv vy cv wceq wph wi vx cv cA wcel vx
      cv cA wcel wph wa vx cv vy cv wceq wb vx cv vy cv wceq vx cv cA wcel wph
      wa wph vx cv cA wcel wph wa vx cv vy cv wceq bi2 vx cv cA wcel wph simpr
      syl6 adantr impbid ex sps jca a5i vy cv cA wcel vx cv cA wcel wph vx cv
      vy cv wceq wb wi wa vx cv cA wcel wph wa vx cv vy cv wceq wb vx vy cv cA
      wcel vx cv cA wcel wph vx cv vy cv wceq wb wi wa vx cv cA wcel wph wa vx
      cv vy cv wceq vx cv cA wcel wph vx cv vy cv wceq wb wi vx cv cA wcel wph
      wa vx cv vy cv wceq wi vy cv cA wcel vx cv cA wcel wph vx cv vy cv wceq
      wb wi vx cv cA wcel wph vx cv vy cv wceq wph vx cv vy cv wceq wb wph vx
      cv vy cv wceq wi vx cv cA wcel wph vx cv vy cv wceq bi1 imim2i imp3a
      adantl vy cv cA wcel vx cv cA wcel wph vx cv vy cv wceq wb wi wa vx cv vy
      cv wceq vx cv cA wcel wph wa vy cv cA wcel vx cv cA wcel wph vx cv vy cv
      wceq wb wi wa vx cv vy cv wceq wa vx cv cA wcel wph vy cv cA wcel vx cv
      cA wcel wph vx cv vy cv wceq wb wi wa vx cv vy cv wceq vx cv cA wcel vy
      cv cA wcel vx cv vy cv wceq vx cv cA wcel wi vx cv cA wcel wph vx cv vy
      cv wceq wb wi vy cv cA vx cv eleq1a adantr imp vx cv cA wcel wph vx cv vy
      cv wceq wb wi vx cv vy cv wceq vx cv cA wcel wph wi vy cv cA wcel vx cv
      cA wcel wph vx cv vy cv wceq wb wi vx cv vy cv wceq vx cv cA wcel wph wi
      vx cv cA wcel wph vx cv vy cv wceq wb wi vx cv cA wcel vx cv vy cv wceq
      wph wph vx cv vy cv wceq wb vx cv vy cv wceq wph wi vx cv cA wcel wph vx
      cv vy cv wceq bi2 imim2i com23 imp adantll jcai ex impbid alimi impbii
      wph vx cv vy cv wceq wb vx cA wral vx cv cA wcel wph vx cv vy cv wceq wb
      wi vx wal vy cv cA wcel wph vx cv vy cv wceq wb vx cA df-ral anbi2i
      3bitr4i exbii vx cv cA wcel wph wa vx vy df-eu wph vx cv vy cv wceq wb vx
      cA wral vy cA df-rex 3bitr4i bitri $.

    $( A way to express restricted uniqueness.  (Contributed by NM,
       24-Oct-2006.) $)
    reu3 $p |- ( E! x e. A ph <->
               ( E. x e. A ph /\ E. y e. A A. x e. A ( ph -> x = y ) ) ) $=
      wph vx cA wreu wph vx cA wrex wph vx cv vy cv wceq wi vx cA wral vy cA
      wrex wa wph vx cA wreu wph vx cA wrex wph vx cv vy cv wceq wi vx cA wral
      vy cA wrex wph vx cA reurex wph vx cA wreu wph vx cv vy cv wceq wb vx cA
      wral vy cA wrex wph vx cv vy cv wceq wi vx cA wral vy cA wrex wph vx vy
      cA reu6 wph vx cv vy cv wceq wb vx cA wral wph vx cv vy cv wceq wi vx cA
      wral vy cA wph vx cv vy cv wceq wb wph vx cv vy cv wceq wi vx cA wph vx
      cv vy cv wceq bi1 ralimi reximi sylbi jca wph vx cA wrex wph vx cv vy cv
      wceq wi vx cA wral vy cA wrex wa wph vx cA wrex wph vx cv vy cv wceq wi
      vx cA wral vy wex wa wph vx cA wreu wph vx cv vy cv wceq wi vx cA wral vy
      cA wrex wph vx cv vy cv wceq wi vx cA wral vy wex wph vx cA wrex wph vx
      cv vy cv wceq wi vx cA wral vy cA rexex anim2i vx cv cA wcel wph wa vx
      weu vx cv cA wcel wph wa vx wex vx cv cA wcel wph wa vx cv vy cv wceq wi
      vx wal vy wex wa wph vx cA wreu wph vx cA wrex wph vx cv vy cv wceq wi vx
      cA wral vy wex wa vx cv cA wcel wph wa vx vy vx cv cA wcel wph wa vy nfv
      eu3 wph vx cA df-reu wph vx cA wrex vx cv cA wcel wph wa vx wex wph vx cv
      vy cv wceq wi vx cA wral vy wex vx cv cA wcel wph wa vx cv vy cv wceq wi
      vx wal vy wex wph vx cA df-rex wph vx cv vy cv wceq wi vx cA wral vx cv
      cA wcel wph wa vx cv vy cv wceq wi vx wal vy wph vx cv vy cv wceq wi vx
      cA wral vx cv cA wcel wph vx cv vy cv wceq wi wi vx wal vx cv cA wcel wph
      wa vx cv vy cv wceq wi vx wal wph vx cv vy cv wceq wi vx cA df-ral vx cv
      cA wcel wph wa vx cv vy cv wceq wi vx cv cA wcel wph vx cv vy cv wceq wi
      wi vx vx cv cA wcel wph vx cv vy cv wceq impexp albii bitr4i exbii
      anbi12i 3bitr4i sylibr impbii $.

    $( A condition which implies existential uniqueness.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)
    reu6i $p |- ( ( B e. A /\ A. x e. A ( ph <-> x = B ) ) -> E! x e. A ph ) $=
      cB cA wcel wph vx cv cB wceq wb vx cA wral wa wph vx cv vy cv wceq wb vx
      cA wral vy cA wrex wph vx cA wreu wph vx cv vy cv wceq wb vx cA wral wph
      vx cv cB wceq wb vx cA wral vy cB cA vy cv cB wceq wph vx cv vy cv wceq
      wb wph vx cv cB wceq wb vx cA vy cv cB wceq vx cv vy cv wceq vx cv cB
      wceq wph vy cv cB vx cv eqeq2 bibi2d ralbidv rspcev wph vx vy cA reu6
      sylibr $.

    eqreu.1 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( A condition which implies existential uniqueness.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)
    eqreu $p |- ( ( B e. A /\ ps /\ A. x e. A ( ph -> x = B ) ) ->
      E! x e. A ph ) $=
      cB cA wcel wph vx cv cB wceq wi vx cA wral wps wph vx cA wreu cB cA wcel
      wph vx cv cB wceq wi vx cA wral wps wph vx cA wreu cB cA wcel wph vx cv
      cB wceq wi vx cA wral wps wa wph vx cv cB wceq wb vx cA wral wph vx cA
      wreu wph vx cv cB wceq wb vx cA wral wph vx cv cB wceq wi vx cA wral vx
      cv cB wceq wph wi vx cA wral wa cB cA wcel wph vx cv cB wceq wi vx cA
      wral wps wa wph vx cv cB wceq vx cA ralbiim cB cA wcel vx cv cB wceq wph
      wi vx cA wral wps wph vx cv cB wceq wi vx cA wral wph wps vx cB cA
      eqreu.1 ceqsralv anbi2d syl5bb cB cA wcel wph vx cv cB wceq wb vx cA wral
      wph vx cA wreu wph vx cA cB reu6i ex sylbird 3impib 3com23 $.
  $}

  ${
    $d x y z A $.  $d y z ph $.  $d x z ps $.
    rmo4.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Restricted "at most one" using implicit substitution.  (Contributed by
       NM, 24-Oct-2006.)  (Revised by NM, 16-Jun-2017.) $)
    rmo4 $p |- ( E* x e. A ph <->
               A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) $=
      wph vx cA wrmo vx cv cA wcel wph wa vx wmo wph wps wa vx vy weq wi vy cA
      wral vx cA wral wph vx cA df-rmo vx cv cA wcel wph wa vy cv cA wcel wps
      wa wa vx vy weq wi vy wal vx wal vx cv cA wcel wph wps wa vx vy weq wi vy
      cA wral wi vx wal vx cv cA wcel wph wa vx wmo wph wps wa vx vy weq wi vy
      cA wral vx cA wral vx cv cA wcel wph wa vy cv cA wcel wps wa wa vx vy weq
      wi vy wal vx cv cA wcel wph wps wa vx vy weq wi vy cA wral wi vx vx cv cA
      wcel wph wa vy cv cA wcel wps wa wa vx vy weq wi vy wal vy cv cA wcel vx
      cv cA wcel wph wps wa vx vy weq wi wi wi vy wal vx cv cA wcel wph wps wa
      vx vy weq wi wi vy cA wral vx cv cA wcel wph wps wa vx vy weq wi vy cA
      wral wi vx cv cA wcel wph wa vy cv cA wcel wps wa wa vx vy weq wi vy cv
      cA wcel vx cv cA wcel wph wps wa vx vy weq wi wi wi vy vx cv cA wcel wph
      wa vy cv cA wcel wps wa wa vx vy weq wi vy cv cA wcel vx cv cA wcel wa
      wph wps wa wa vx vy weq wi vy cv cA wcel vx cv cA wcel wa wph wps wa vx
      vy weq wi wi vy cv cA wcel vx cv cA wcel wph wps wa vx vy weq wi wi wi vx
      cv cA wcel wph wa vy cv cA wcel wps wa wa vy cv cA wcel vx cv cA wcel wa
      wph wps wa wa vx vy weq vx cv cA wcel wph wa vy cv cA wcel wps wa wa vx
      cv cA wcel vy cv cA wcel wa wph wps wa wa vy cv cA wcel vx cv cA wcel wa
      wph wps wa wa vx cv cA wcel wph vy cv cA wcel wps an4 vx cv cA wcel vy cv
      cA wcel wa vy cv cA wcel vx cv cA wcel wa wph wps wa vx cv cA wcel vy cv
      cA wcel ancom anbi1i bitri imbi1i vy cv cA wcel vx cv cA wcel wa wph wps
      wa vx vy weq impexp vy cv cA wcel vx cv cA wcel wph wps wa vx vy weq wi
      impexp 3bitri albii vx cv cA wcel wph wps wa vx vy weq wi wi vy cA df-ral
      vx cv cA wcel wph wps wa vx vy weq wi vy cA r19.21v 3bitr2i albii vx cv
      cA wcel wph wa vy cv cA wcel wps wa vx vy vx vy weq vx cv cA wcel vy cv
      cA wcel wph wps vx cv vy cv cA eleq1 rmo4.1 anbi12d mo4 wph wps wa vx vy
      weq wi vy cA wral vx cA df-ral 3bitr4i bitri $.

    $( Restricted uniqueness using implicit substitution.  (Contributed by NM,
       23-Nov-1994.) $)
    reu4 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\
             A. x e. A A. y e. A ( ( ph /\ ps ) -> x = y ) ) ) $=
      wph vx cA wreu wph vx cA wrex wph vx cA wrmo wa wph vx cA wrex wph wps wa
      vx vy weq wi vy cA wral vx cA wral wa wph vx cA reu5 wph vx cA wrmo wph
      wps wa vx vy weq wi vy cA wral vx cA wral wph vx cA wrex wph wps vx vy cA
      rmo4.1 rmo4 anbi2i bitri $.

    $( Restricted uniqueness using implicit substitution.  (Contributed by NM,
       24-Oct-2006.) $)
    reu7 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\
             E. x e. A A. y e. A ( ps -> x = y ) ) ) $=
      wph vx cA wreu wph vx cA wrex wph vx cv vz cv wceq wi vx cA wral vz cA
      wrex wa wph vx cA wrex wps vx cv vy cv wceq wi vy cA wral vx cA wrex wa
      wph vx vz cA reu3 wph vx cv vz cv wceq wi vx cA wral vz cA wrex wps vx cv
      vy cv wceq wi vy cA wral vx cA wrex wph vx cA wrex wph vx cv vz cv wceq
      wi vx cA wral vz cA wrex wps vz cv vy cv wceq wi vy cA wral vz cA wrex
      wps vx cv vy cv wceq wi vy cA wral vx cA wrex wph vx cv vz cv wceq wi vx
      cA wral wps vz cv vy cv wceq wi vy cA wral vz cA wph vx cv vz cv wceq wi
      wps vz cv vy cv wceq wi vx vy cA vx cv vy cv wceq wph wps vx cv vz cv
      wceq vz cv vy cv wceq rmo4.1 vx cv vy cv wceq vx cv vz cv wceq vy cv vz
      cv wceq vz cv vy cv wceq vx cv vy cv vz cv eqeq1 vy cv vz cv eqcom syl6bb
      imbi12d cbvralv rexbii wps vz cv vy cv wceq wi vy cA wral wps vx cv vy cv
      wceq wi vy cA wral vz vx cA vz cv vx cv wceq wps vz cv vy cv wceq wi wps
      vx cv vy cv wceq wi vy cA vz cv vx cv wceq vz cv vy cv wceq vx cv vy cv
      wceq wps vz cv vx cv vy cv eqeq1 imbi2d ralbidv cbvrexv bitri anbi2i
      bitri $.

    $( Restricted uniqueness using implicit substitution.  (Contributed by NM,
       24-Oct-2006.) $)
    reu8 $p |- ( E! x e. A ph <-> E. x e. A ( ph /\
                A. y e. A ( ps -> x = y ) ) ) $=
      wph vx cA wreu wps vy cA wreu wps vy cv vx cv wceq wb vy cA wral vx cA
      wrex wph wps vx cv vy cv wceq wi vy cA wral wa vx cA wrex wph wps vx vy
      cA rmo4.1 cbvreuv wps vy vx cA reu6 wps vy cv vx cv wceq wb vy cA wral
      wph wps vx cv vy cv wceq wi vy cA wral wa vx cA wps vy cv vx cv wceq wb
      vy cA wral wps vy cv vx cv wceq wi vy cv vx cv wceq wps wi wa vy cA wral
      vx cv cA wcel wph wps vx cv vy cv wceq wi vy cA wral wa wps vy cv vx cv
      wceq wb wps vy cv vx cv wceq wi vy cv vx cv wceq wps wi wa vy cA wps vy
      cv vx cv wceq dfbi2 ralbii vx cv cA wcel wph wps vx cv vy cv wceq wi vy
      cA wral wa wps vy cv vx cv wceq wi vy cA wral vy cv vx cv wceq wps wi vy
      cA wral wa wps vy cv vx cv wceq wi vy cv vx cv wceq wps wi wa vy cA wral
      wph wps vx cv vy cv wceq wi vy cA wral wa wps vx cv vy cv wceq wi vy cA
      wral wph wa vx cv cA wcel wps vy cv vx cv wceq wi vy cA wral vy cv vx cv
      wceq wps wi vy cA wral wa wph wps vx cv vy cv wceq wi vy cA wral ancom vx
      cv cA wcel wps vx cv vy cv wceq wi vy cA wral wps vy cv vx cv wceq wi vy
      cA wral wph vy cv vx cv wceq wps wi vy cA wral wps vx cv vy cv wceq wi vy
      cA wral wps vy cv vx cv wceq wi vy cA wral wb vx cv cA wcel wps vx cv vy
      cv wceq wi wps vy cv vx cv wceq wi vy cA vx cv vy cv wceq vy cv vx cv
      wceq wps vx vy equcom imbi2i ralbii a1i vx cv cA wcel wph vx cv cA wcel
      wph wi vy cv vx cv wceq wps wi vy cA wral vx cv cA wcel wph biimt vy cv
      vx cv wceq wps wi vy cA wral vy cv cA wcel vy cv vx cv wceq wps wi wi vy
      wal vy cv vx cv wceq vy cv cA wcel wps wi wi vy wal vx cv cA wcel wph wi
      vy cv vx cv wceq wps wi vy cA df-ral vy cv cA wcel vy cv vx cv wceq wps
      wi wi vy cv vx cv wceq vy cv cA wcel wps wi wi vy vy cv cA wcel vy cv vx
      cv wceq wps bi2.04 albii vy cv cA wcel wps wi vx cv cA wcel wph wi vy vx
      cv vx vex vy cv cA wcel wps wi vx cv cA wcel wph wi wb vx vy vx cv vy cv
      wceq vx cv cA wcel wph wi vy cv cA wcel wps wi vx cv vy cv wceq vx cv cA
      wcel vy cv cA wcel wph wps vx cv vy cv cA eleq1 rmo4.1 imbi12d bicomd
      equcoms ceqsalv 3bitrri syl6bb anbi12d syl5bb wps vy cv vx cv wceq wi vy
      cv vx cv wceq wps wi vy cA r19.26 syl6rbbr syl5bb rexbiia 3bitri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Equality has existential uniqueness.  (Contributed by Mario Carneiro,
       1-Sep-2015.) $)
    reueq $p |- ( B e. A <-> E! x e. A x = B ) $=
      cB cA wcel vx cv cB wceq vx cA wrex vx cv cB wceq vx cA wreu vx cB cA
      risset vx cv cB wceq vx cA wreu vx cv cB wceq vx cA wrex vx cv cB wceq vx
      cA wrmo vx cv cB wceq vx wmo vx cv cB wceq vx cA wrmo vx cB moeq vx cv cB
      wceq vx cA mormo ax-mp vx cv cB wceq vx cA reu5 mpbiran2 bitr4i $.
  $}

  $( Restricted "at most one" still holds when a conjunct is added.
     (Contributed by NM, 16-Jun-2017.) $)
  rmoan $p |- ( E* x e. A ph -> E* x e. A ( ps /\ ph ) ) $=
    vx cv cA wcel wph wa vx wmo vx cv cA wcel wps wph wa wa vx wmo wph vx cA
    wrmo wps wph wa vx cA wrmo vx cv cA wcel wph wa vx wmo wps vx cv cA wcel
    wph wa wa vx wmo vx cv cA wcel wps wph wa wa vx wmo vx cv cA wcel wph wa
    wps vx moan wps vx cv cA wcel wph wa wa vx cv cA wcel wps wph wa wa vx wps
    vx cv cA wcel wph an12 mobii sylib wph vx cA df-rmo wps wph wa vx cA df-rmo
    3imtr4i $.

  $( Restricted "at most one" is preserved through implication (note wff
     reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
  rmoim $p |- ( A. x e. A ( ph -> ps )
        -> ( E* x e. A ps -> E* x e. A ph ) ) $=
    wph wps wi vx cA wral vx cv cA wcel wph wa vx cv cA wcel wps wa wi vx wal
    wps vx cA wrmo wph vx cA wrmo wi wph wps wi vx cA wral vx cv cA wcel wph
    wps wi wi vx wal vx cv cA wcel wph wa vx cv cA wcel wps wa wi vx wal wph
    wps wi vx cA df-ral vx cv cA wcel wph wps wi wi vx cv cA wcel wph wa vx cv
    cA wcel wps wa wi vx vx cv cA wcel wph wps imdistan albii bitri vx cv cA
    wcel wph wa vx cv cA wcel wps wa wi vx wal vx cv cA wcel wps wa vx wmo vx
    cv cA wcel wph wa vx wmo wps vx cA wrmo wph vx cA wrmo vx cv cA wcel wph wa
    vx cv cA wcel wps wa vx moim wps vx cA df-rmo wph vx cA df-rmo 3imtr4g
    sylbi $.

  ${
    rmoimia.1 $e |- ( x e. A -> ( ph -> ps ) ) $.
    $( Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
    rmoimia $p |- ( E* x e. A ps -> E* x e. A ph ) $=
      wph wps wi wps vx cA wrmo wph vx cA wrmo wi vx cA wph wps vx cA rmoim
      rmoimia.1 mprg $.
  $}

  ${
    rmoimi2.1 $e |- A. x ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) ) $.
    $( Restricted "at most one" is preserved through implication (note wff
       reversal).  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
    rmoimi2 $p |- ( E* x e. B ps -> E* x e. A ph ) $=
      vx cv cB wcel wps wa vx wmo vx cv cA wcel wph wa vx wmo wps vx cB wrmo
      wph vx cA wrmo vx cv cA wcel wph wa vx cv cB wcel wps wa wi vx wal vx cv
      cB wcel wps wa vx wmo vx cv cA wcel wph wa vx wmo wi rmoimi2.1 vx cv cA
      wcel wph wa vx cv cB wcel wps wa vx moim ax-mp wps vx cB df-rmo wph vx cA
      df-rmo 3imtr4i $.
  $}

  ${
    $d x y A $.  $d x B $.
    $( A condition allowing swap of uniqueness and existential quantifiers.
       (Contributed by Thierry Arnoux, 7-Apr-2017.)  (Revised by NM,
       16-Jun-2017.) $)
    2reuswap $p |- ( A. x e. A E* y e. B ph ->
                   ( E! x e. A E. y e. B ph -> E! y e. B E. x e. A ph ) ) $=
      wph vy cB wrmo vx cA wral vy cv cB wcel wph wa vy wmo vx cA wral wph vy
      cB wrex vx cA wreu wph vx cA wrex vy cB wreu wi wph vy cB wrmo vy cv cB
      wcel wph wa vy wmo vx cA wph vy cB df-rmo ralbii vy cv cB wcel wph wa vy
      wmo vx cA wral vx cv cA wcel vy cv cB wcel wph wa wa vy wmo vx wal wph vy
      cB wrex vx cA wreu wph vx cA wrex vy cB wreu wi vy cv cB wcel wph wa vy
      wmo vx cA wral vx cv cA wcel vy cv cB wcel wph wa vy wmo wi vx wal vx cv
      cA wcel vy cv cB wcel wph wa wa vy wmo vx wal vy cv cB wcel wph wa vy wmo
      vx cA df-ral vx cv cA wcel vy cv cB wcel wph wa wa vy wmo vx cv cA wcel
      vy cv cB wcel wph wa vy wmo wi vx vx cv cA wcel vy cv cB wcel wph wa vy
      moanimv albii bitr4i vx cv cA wcel vy cv cB wcel wph wa wa vy wmo vx wal
      vx cv cA wcel vy cv cB wcel wph wa wa vy wex vx weu vx cv cA wcel vy cv
      cB wcel wph wa wa vx wex vy weu wph vy cB wrex vx cA wreu wph vx cA wrex
      vy cB wreu vx cv cA wcel vy cv cB wcel wph wa wa vx vy 2euswap wph vy cB
      wrex vx cA wreu vx cv cA wcel wph vy cB wrex wa vx weu vx cv cA wcel vy
      cv cB wcel wph wa wa vy wex vx weu wph vy cB wrex vx cA df-reu vx cv cA
      wcel wph vy cB wrex wa vx cv cA wcel vy cv cB wcel wph wa wa vy wex vx vx
      cv cA wcel wph vy cB wrex wa vy cv cB wcel vx cv cA wcel wph wa wa vy wex
      vx cv cA wcel vy cv cB wcel wph wa wa vy wex vx cv cA wcel wph vy cB wrex
      wa vx cv cA wcel wph wa vy cB wrex vy cv cB wcel vx cv cA wcel wph wa wa
      vy wex vx cv cA wcel wph vy cB r19.42v vx cv cA wcel wph wa vy cB df-rex
      bitr3i vy cv cB wcel vx cv cA wcel wph wa wa vx cv cA wcel vy cv cB wcel
      wph wa wa vy vy cv cB wcel vx cv cA wcel wph an12 exbii bitri eubii bitri
      wph vx cA wrex vy cB wreu vy cv cB wcel wph vx cA wrex wa vy weu vx cv cA
      wcel vy cv cB wcel wph wa wa vx wex vy weu wph vx cA wrex vy cB df-reu vy
      cv cB wcel wph vx cA wrex wa vx cv cA wcel vy cv cB wcel wph wa wa vx wex
      vy vy cv cB wcel wph vx cA wrex wa vy cv cB wcel wph wa vx cA wrex vx cv
      cA wcel vy cv cB wcel wph wa wa vx wex vy cv cB wcel wph vx cA r19.42v vy
      cv cB wcel wph wa vx cA df-rex bitr3i eubii bitri 3imtr4g sylbi sylbi $.
  $}

  ${
    $d w y z A $.  $d x z B $.  $d w x y z C $.  $d w y z ph $.  $d x z ps $.
    reuind.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    reuind.2 $e |- ( x = y -> A = B ) $.
    $( Existential uniqueness via an indirect equality.  (Contributed by NM,
       16-Oct-2010.) $)
    reuind $p |- ( ( A. x A. y ( ( ( A e. C /\ ph ) /\ ( B e. C /\ ps ) )
         -> A = B ) /\ E. x ( A e. C /\ ph ) )
                 -> E! z e. C A. x ( ( A e. C /\ ph ) -> z = A ) ) $=
      cA cC wcel wph wa cB cC wcel wps wa wa cA cB wceq wi vy wal vx wal cA cC
      wcel wph wa vx wex wa cA cC wcel wph wa vz cv cA wceq wi vx wal vz cC
      wrex cA cC wcel wph wa vz cv cA wceq wi vx wal cA cC wcel wph wa vw cv cA
      wceq wi vx wal wa vz cv vw cv wceq wi vw cC wral vz cC wral cA cC wcel
      wph wa vz cv cA wceq wi vx wal vz cC wreu cA cC wcel wph wa cB cC wcel
      wps wa wa cA cB wceq wi vy wal vx wal cA cC wcel wph wa vx wex cA cC wcel
      wph wa vz cv cA wceq wi vx wal vz cC wrex cA cC wcel wph wa vx wex vz cv
      cB wceq wps wa vy wex vz cC wrex cA cC wcel wph wa cB cC wcel wps wa wa
      cA cB wceq wi vy wal vx wal cA cC wcel wph wa vz cv cA wceq wi vx wal vz
      cC wrex cA cC wcel wph wa vx wex cB cC wcel wps wa vy wex vz cv cB wceq
      wps wa vy wex vz cC wrex cA cC wcel wph wa cB cC wcel wps wa vx vy vx cv
      vy cv wceq cA cC wcel cB cC wcel wph wps vx cv vy cv wceq cA cB cC
      reuind.2 eleq1d reuind.1 anbi12d cbvexv vz cv cB wceq wps wa vz cC wrex
      vy wex vz cv cB wceq vz cC wrex wps wa vy wex vz cv cB wceq wps wa vy wex
      vz cC wrex cB cC wcel wps wa vy wex vz cv cB wceq wps wa vz cC wrex vz cv
      cB wceq vz cC wrex wps wa vy vz cv cB wceq wps vz cC r19.41v exbii vz cv
      cB wceq wps wa vz vy cC rexcom4 cB cC wcel wps wa vz cv cB wceq vz cC
      wrex wps wa vy cB cC wcel vz cv cB wceq vz cC wrex wps vz cB cC risset
      anbi1i exbii 3bitr4ri bitri cA cC wcel wph wa cB cC wcel wps wa wa cA cB
      wceq wi vy wal vx wal vz cv cB wceq wps wa vy wex cA cC wcel wph wa vz cv
      cA wceq wi vx wal vz cC cA cC wcel wph wa cB cC wcel wps wa wa cA cB wceq
      wi vy wal vx wal vz cv cC wcel vz cv cB wceq wps wa vy wex cA cC wcel wph
      wa vz cv cA wceq wi vx wal cA cC wcel wph wa cB cC wcel wps wa wa cA cB
      wceq wi vy wal vx wal vz cv cB wceq cB cC wcel wps wa wa cA cC wcel wph
      wa vz cv cA wceq wi wi vy wal vx wal vz cv cC wcel vz cv cB wceq wps wa
      vy wex wa cA cC wcel wph wa vz cv cA wceq wi vx wal wi cA cC wcel wph wa
      cB cC wcel wps wa wa cA cB wceq wi vz cv cB wceq cB cC wcel wps wa wa cA
      cC wcel wph wa vz cv cA wceq wi wi vx vy cA cC wcel wph wa cB cC wcel wps
      wa wa cA cB wceq wi cA cC wcel wph wa cB cC wcel wps wa wa vz cv cA wceq
      vz cv cB wceq wb wi vz cv cB wceq cB cC wcel wps wa wa cA cC wcel wph wa
      vz cv cA wceq wi wi cA cB wceq vz cv cA wceq vz cv cB wceq wb cA cC wcel
      wph wa cB cC wcel wps wa wa cA cB vz cv eqeq2 imim2i cA cC wcel wph wa cB
      cC wcel wps wa wa vz cv cA wceq vz cv cB wceq wb wi cA cC wcel wph wa cB
      cC wcel wps wa wa vz cv cB wceq vz cv cA wceq wi wi vz cv cB wceq cB cC
      wcel wps wa wa cA cC wcel wph wa vz cv cA wceq wi wi vz cv cA wceq vz cv
      cB wceq wb vz cv cB wceq vz cv cA wceq wi cA cC wcel wph wa cB cC wcel
      wps wa wa vz cv cA wceq vz cv cB wceq bi2 imim2i cA cC wcel wph wa cB cC
      wcel wps wa wa vz cv cB wceq wa vz cv cA wceq wi vz cv cB wceq cB cC wcel
      wps wa wa cA cC wcel wph wa wa vz cv cA wceq wi cA cC wcel wph wa cB cC
      wcel wps wa wa vz cv cB wceq vz cv cA wceq wi wi vz cv cB wceq cB cC wcel
      wps wa wa cA cC wcel wph wa vz cv cA wceq wi wi cA cC wcel wph wa cB cC
      wcel wps wa wa vz cv cB wceq wa vz cv cB wceq cB cC wcel wps wa wa cA cC
      wcel wph wa wa vz cv cA wceq cA cC wcel wph wa cB cC wcel wps wa vz cv cB
      wceq an31 imbi1i cA cC wcel wph wa cB cC wcel wps wa wa vz cv cB wceq vz
      cv cA wceq impexp vz cv cB wceq cB cC wcel wps wa wa cA cC wcel wph wa vz
      cv cA wceq impexp 3bitr3i sylib syl 2alimi vz cv cB wceq cB cC wcel wps
      wa wa cA cC wcel wph wa vz cv cA wceq wi wi vy wal vx wal vz cv cC wcel
      vz cv cB wceq wps wa vy wex wa cA cC wcel wph wa vz cv cA wceq wi wi vx
      wal vz cv cC wcel vz cv cB wceq wps wa vy wex wa cA cC wcel wph wa vz cv
      cA wceq wi vx wal wi vz cv cB wceq cB cC wcel wps wa wa cA cC wcel wph wa
      vz cv cA wceq wi wi vy wal vz cv cC wcel vz cv cB wceq wps wa vy wex wa
      cA cC wcel wph wa vz cv cA wceq wi wi vx vz cv cB wceq cB cC wcel wps wa
      wa cA cC wcel wph wa vz cv cA wceq wi wi vy wal vz cv cB wceq cB cC wcel
      wps wa wa vy wex cA cC wcel wph wa vz cv cA wceq wi wi vz cv cC wcel vz
      cv cB wceq wps wa vy wex wa cA cC wcel wph wa vz cv cA wceq wi wi vz cv
      cB wceq cB cC wcel wps wa wa cA cC wcel wph wa vz cv cA wceq wi vy 19.23v
      vz cv cB wceq cB cC wcel wps wa wa vy wex vz cv cC wcel vz cv cB wceq wps
      wa vy wex wa cA cC wcel wph wa vz cv cA wceq wi vz cv cB wceq cB cC wcel
      wps wa wa vy wex vz cv cC wcel vz cv cB wceq wps wa wa vy wex vz cv cC
      wcel vz cv cB wceq wps wa vy wex wa vz cv cB wceq cB cC wcel wps wa wa vz
      cv cC wcel vz cv cB wceq wps wa wa vy vz cv cB wceq cB cC wcel wps wa wa
      cB cC wcel vz cv cB wceq wps wa wa vz cv cC wcel vz cv cB wceq wps wa wa
      vz cv cB wceq cB cC wcel wps an12 vz cv cB wceq wps wa vz cv cC wcel cB
      cC wcel vz cv cB wceq vz cv cC wcel cB cC wcel wb wps vz cv cB cC eleq1
      adantr pm5.32ri bitr4i exbii vz cv cC wcel vz cv cB wceq wps wa vy 19.42v
      bitri imbi1i bitri albii vz cv cC wcel vz cv cB wceq wps wa vy wex wa cA
      cC wcel wph wa vz cv cA wceq wi vx 19.21v bitri sylib exp3a reximdvai
      syl5bi imp cA cC wcel wph wa vx wex cA cC wcel wph wa vz cv cA wceq wi vx
      wal cA cC wcel wph wa vw cv cA wceq wi vx wal wa vz cv vw cv wceq wi vw
      cC wral vz cC wral cA cC wcel wph wa cB cC wcel wps wa wa cA cB wceq wi
      vy wal vx wal cA cC wcel wph wa vx wex cA cC wcel wph wa vz cv cA wceq wi
      vx wal cA cC wcel wph wa vw cv cA wceq wi vx wal wa vz cv vw cv wceq wi
      vz vw cC cC cA cC wcel wph wa vx wex cA cC wcel wph wa vz cv cA wceq wi
      vx wal cA cC wcel wph wa vw cv cA wceq wi vx wal wa vz cv vw cv wceq wi
      vz cv cC wcel vw cv cC wcel wa cA cC wcel wph wa vz cv cA wceq wi vx wal
      cA cC wcel wph wa vw cv cA wceq wi vx wal wa cA cC wcel wph wa vz cv vw
      cv wceq wi vx wal cA cC wcel wph wa vx wex vz cv vw cv wceq cA cC wcel
      wph wa vz cv cA wceq wi cA cC wcel wph wa vw cv cA wceq wi cA cC wcel wph
      wa vz cv vw cv wceq wi vx cA cC wcel wph wa cA cC wcel wph wa cA cC wcel
      wph wa wa cA cC wcel wph wa vz cv cA wceq wi cA cC wcel wph wa vw cv cA
      wceq wi wa vz cv cA wceq vw cv cA wceq wa vz cv vw cv wceq cA cC wcel wph
      wa cA cC wcel wph wa cA cC wcel wph wa wa cA cC wcel wph wa pm4.24 biimpi
      cA cC wcel wph wa vz cv cA wceq cA cC wcel wph wa vw cv cA wceq prth vz
      cv vw cv cA eqtr3 syl56 alanimi cA cC wcel wph wa vz cv vw cv wceq wi vx
      wal cA cC wcel wph wa vx wex vz cv vw cv wceq cA cC wcel wph wa vz cv vw
      cv wceq wi vx wal cA cC wcel wph wa vx wex vz cv vw cv wceq wi cA cC wcel
      wph wa vz cv vw cv wceq vx 19.23v biimpi com12 syl5 a1d ralrimivv adantl
      cA cC wcel wph wa vz cv cA wceq wi vx wal cA cC wcel wph wa vw cv cA wceq
      wi vx wal vz vw cC vz cv vw cv wceq cA cC wcel wph wa vz cv cA wceq wi cA
      cC wcel wph wa vw cv cA wceq wi vx vz cv vw cv wceq vz cv cA wceq vw cv
      cA wceq cA cC wcel wph wa vz cv vw cv cA eqeq1 imbi2d albidv reu4
      sylanbrc $.
  $}

  ${
    $d y A $.  $d x B $.  $d x y $.
    $( Double restricted quantification with "at most one," analogous to
       ~ 2moex .  (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
    2rmorex $p |- ( E* x e. A E. y e. B ph -> A. y e. B E* x e. A ph ) $=
      wph vy cB wrex vx cA wrmo wph vx cA wrmo vy cB wph vy cB wrex vy vx cA vy
      cA nfcv wph vy cB nfre1 nfrmo vy cv cB wcel wph vy cB wrex vx cA wrmo wph
      vx cA wrmo vy cv cB wcel wph wph vy cB wrex wi vx cA wral wph vy cB wrex
      vx cA wrmo wph vx cA wrmo wi vy cv cB wcel wph wph vy cB wrex wi vx cA vy
      cv cB wcel wph wph vy cB wrex wph vy cB rspe ex ralrimivw wph wph vy cB
      wrex vx cA rmoim syl com12 ralrimi $.

    $( Lemma for ~ 2reu5 .  Note that ` E! x e. A E! y e. B ph ` does not mean
       "there is exactly one ` x ` in ` A ` and exactly one ` y ` in ` B ` such
       that ` ph ` holds;" see comment for ~ 2eu5 .  (Contributed by Alexander
       van der Vekens, 17-Jun-2017.) $)
    2reu5lem1 $p |- ( E! x e. A E! y e. B ph <->
                   E! x E! y ( x e. A /\ y e. B /\ ph ) ) $=
      wph vy cB wreu vx cA wreu vy cv cB wcel wph wa vy weu vx cA wreu vx cv cA
      wcel vy cv cB wcel wph w3a vy weu vx weu wph vy cB wreu vy cv cB wcel wph
      wa vy weu vx cA wph vy cB df-reu reubii vy cv cB wcel wph wa vy weu vx cA
      wreu vx cv cA wcel vy cv cB wcel wph wa vy weu wa vx weu vx cv cA wcel vy
      cv cB wcel wph w3a vy weu vx weu vy cv cB wcel wph wa vy weu vx cA df-reu
      vx cv cA wcel vy cv cB wcel wph wa vy weu wa vx cv cA wcel vy cv cB wcel
      wph w3a vy weu vx vx cv cA wcel vy cv cB wcel wph wa vy weu wa vx cv cA
      wcel vy cv cB wcel wph wa wa vy weu vx cv cA wcel vy cv cB wcel wph w3a
      vy weu vx cv cA wcel vy cv cB wcel wph wa wa vy weu vx cv cA wcel vy cv
      cB wcel wph wa vy weu wa vx cv cA wcel vy cv cB wcel wph wa vy euanv
      bicomi vx cv cA wcel vy cv cB wcel wph wa wa vx cv cA wcel vy cv cB wcel
      wph w3a vy vx cv cA wcel vy cv cB wcel wph w3a vx cv cA wcel vy cv cB
      wcel wph wa wa vx cv cA wcel vy cv cB wcel wph 3anass bicomi eubii bitri
      eubii bitri bitri $.

    $( Lemma for ~ 2reu5 .  (Contributed by Alexander van der Vekens,
       17-Jun-2017.) $)
    2reu5lem2 $p |- ( A. x e. A E* y e. B ph <->
                   A. x E* y ( x e. A /\ y e. B /\ ph ) ) $=
      wph vy cB wrmo vx cA wral vy cv cB wcel wph wa vy wmo vx cA wral vx cv cA
      wcel vy cv cB wcel wph w3a vy wmo vx wal wph vy cB wrmo vy cv cB wcel wph
      wa vy wmo vx cA wph vy cB df-rmo ralbii vy cv cB wcel wph wa vy wmo vx cA
      wral vx cv cA wcel vy cv cB wcel wph wa vy wmo wi vx wal vx cv cA wcel vy
      cv cB wcel wph w3a vy wmo vx wal vy cv cB wcel wph wa vy wmo vx cA df-ral
      vx cv cA wcel vy cv cB wcel wph wa vy wmo wi vx cv cA wcel vy cv cB wcel
      wph w3a vy wmo vx vx cv cA wcel vy cv cB wcel wph wa vy wmo wi vx cv cA
      wcel vy cv cB wcel wph wa wa vy wmo vx cv cA wcel vy cv cB wcel wph w3a
      vy wmo vx cv cA wcel vy cv cB wcel wph wa wa vy wmo vx cv cA wcel vy cv
      cB wcel wph wa vy wmo wi vx cv cA wcel vy cv cB wcel wph wa vy moanimv
      bicomi vx cv cA wcel vy cv cB wcel wph wa wa vx cv cA wcel vy cv cB wcel
      wph w3a vy vx cv cA wcel vy cv cB wcel wph w3a vx cv cA wcel vy cv cB
      wcel wph wa wa vx cv cA wcel vy cv cB wcel wph 3anass bicomi mobii bitri
      albii bitri bitri $.
  $}

  ${
    $d w y z A $.  $d w x z B $.  $d x y $.  $d ph w $.  $d ph z $.
    $( Lemma for ~ 2reu5 .  This lemma is interesting in its own right, showing
       that existential restriction in the last conjunct (the "at most one"
       part) is optional; compare ~ rmo2 .  (Contributed by Alexander van der
       Vekens, 17-Jun-2017.) $)
    2reu5lem3 $p |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph )
                   <-> ( E. x e. A E. y e. B ph
                         /\ E. z E. w A. x e. A A. y e. B
                            ( ph -> ( x = z /\ y = w ) ) ) ) $=
      wph vy cB wreu vx cA wreu wph vy cB wrmo vx cA wral wa vx cv cA wcel vy
      cv cB wcel wph w3a vy weu vx weu vx cv cA wcel vy cv cB wcel wph w3a vy
      wmo vx wal wa vx cv cA wcel vy cv cB wcel wph w3a vy wex vx wex vx cv cA
      wcel vy cv cB wcel wph w3a vx vz weq vy vw weq wa wi vy wal vx wal vw wex
      vz wex wa wph vy cB wrex vx cA wrex wph vx vz weq vy vw weq wa wi vy cB
      wral vx cA wral vw wex vz wex wa wph vy cB wreu vx cA wreu vx cv cA wcel
      vy cv cB wcel wph w3a vy weu vx weu wph vy cB wrmo vx cA wral vx cv cA
      wcel vy cv cB wcel wph w3a vy wmo vx wal wph vx vy cA cB 2reu5lem1 wph vx
      vy cA cB 2reu5lem2 anbi12i vx cv cA wcel vy cv cB wcel wph w3a vx vy vz
      vw 2eu5 vx cv cA wcel vy cv cB wcel wph w3a vy wex vx wex wph vy cB wrex
      vx cA wrex vx cv cA wcel vy cv cB wcel wph w3a vx vz weq vy vw weq wa wi
      vy wal vx wal vw wex vz wex wph vx vz weq vy vw weq wa wi vy cB wral vx
      cA wral vw wex vz wex vx cv cA wcel vy cv cB wcel wph w3a vy wex vx wex
      vx cv cA wcel wph vy cB wrex wa vx wex wph vy cB wrex vx cA wrex vx cv cA
      wcel vy cv cB wcel wph w3a vy wex vx cv cA wcel wph vy cB wrex wa vx vx
      cv cA wcel vy cv cB wcel wph w3a vy wex vx cv cA wcel vy cv cB wcel wph
      wa wa vy wex vx cv cA wcel vy cv cB wcel wph wa vy wex wa vx cv cA wcel
      wph vy cB wrex wa vx cv cA wcel vy cv cB wcel wph w3a vx cv cA wcel vy cv
      cB wcel wph wa wa vy vx cv cA wcel vy cv cB wcel wph 3anass exbii vx cv
      cA wcel vy cv cB wcel wph wa vy 19.42v vy cv cB wcel wph wa vy wex wph vy
      cB wrex vx cv cA wcel wph vy cB wrex vy cv cB wcel wph wa vy wex wph vy
      cB df-rex bicomi anbi2i 3bitri exbii wph vy cB wrex vx cA df-rex bitr4i
      vx cv cA wcel vy cv cB wcel wph w3a vx vz weq vy vw weq wa wi vy wal vx
      wal vw wex wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw wex vz
      vx cv cA wcel vy cv cB wcel wph w3a vx vz weq vy vw weq wa wi vy wal vx
      wal wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw vx cv cA wcel
      vy cv cB wcel wph w3a vx vz weq vy vw weq wa wi vy wal vx wal vx cv cA
      wcel wph vx vz weq vy vw weq wa wi vy cB wral wi vx wal wph vx vz weq vy
      vw weq wa wi vy cB wral vx cA wral vx cv cA wcel vy cv cB wcel wph w3a vx
      vz weq vy vw weq wa wi vy wal vx cv cA wcel wph vx vz weq vy vw weq wa wi
      vy cB wral wi vx vx cv cA wcel vy cv cB wcel wph w3a vx vz weq vy vw weq
      wa wi vy wal vy cv cB wcel vx cv cA wcel wph vx vz weq vy vw weq wa wi wi
      wi vy wal vx cv cA wcel wph vx vz weq vy vw weq wa wi wi vy cB wral vx cv
      cA wcel wph vx vz weq vy vw weq wa wi vy cB wral wi vx cv cA wcel vy cv
      cB wcel wph w3a vx vz weq vy vw weq wa wi vy cv cB wcel vx cv cA wcel wph
      vx vz weq vy vw weq wa wi wi wi vy vx cv cA wcel vy cv cB wcel wph w3a vx
      vz weq vy vw weq wa wi vy cv cB wcel vx cv cA wcel wph wa wa vx vz weq vy
      vw weq wa wi vy cv cB wcel vx cv cA wcel wph wa vx vz weq vy vw weq wa wi
      wi vy cv cB wcel vx cv cA wcel wph vx vz weq vy vw weq wa wi wi wi vx cv
      cA wcel vy cv cB wcel wph w3a vy cv cB wcel vx cv cA wcel wph wa wa vx vz
      weq vy vw weq wa vx cv cA wcel vy cv cB wcel wph 3anan12 imbi1i vy cv cB
      wcel vx cv cA wcel wph wa vx vz weq vy vw weq wa impexp vx cv cA wcel wph
      wa vx vz weq vy vw weq wa wi vx cv cA wcel wph vx vz weq vy vw weq wa wi
      wi vy cv cB wcel vx cv cA wcel wph vx vz weq vy vw weq wa impexp imbi2i
      3bitri albii vx cv cA wcel wph vx vz weq vy vw weq wa wi wi vy cB df-ral
      vx cv cA wcel wph vx vz weq vy vw weq wa wi vy cB r19.21v 3bitr2i albii
      wph vx vz weq vy vw weq wa wi vy cB wral vx cA df-ral bitr4i exbii exbii
      anbi12i 3bitri $.

    $d x A $.  $d y B $.
    $( Double restricted existential uniqueness in terms of restricted
       existential quantification and restricted universal quantification,
       analogous to ~ 2eu5 and ~ reu3 .  (Contributed by Alexander van der
       Vekens, 17-Jun-2017.) $)
    2reu5 $p |- ( ( E! x e. A E! y e. B ph /\ A. x e. A E* y e. B ph )
                  <-> ( E. x e. A E. y e. B ph
                        /\ E. z e. A E. w e. B A. x e. A A. y e. B
                           ( ph -> ( x = z /\ y = w ) ) ) ) $=
      wph vy cB wrex vx cA wrex wph vx vz weq vy vw weq wa wi vy cB wral vx cA
      wral vw wex vz wex wa wph vy cB wrex vx cA wrex vw cv cB wcel vz cv cA
      wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral wa wa vw wex vz
      wex wa wph vy cB wreu vx cA wreu wph vy cB wrmo vx cA wral wa wph vy cB
      wrex vx cA wrex wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw cB
      wrex vz cA wrex wa wph vy cB wrex vx cA wrex wph vx vz weq vy vw weq wa
      wi vy cB wral vx cA wral vw wex vz wex vw cv cB wcel vz cv cA wcel wph vx
      vz weq vy vw weq wa wi vy cB wral vx cA wral wa wa vw wex vz wex wph vy
      cB wrex vx cA wrex wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw
      cv cB wcel vz cv cA wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA
      wral wa wa vz vw wph vy cB wrex vx cA wrex wph vx vz weq vy vw weq wa wi
      vy cB wral vx cA wral vw cv cB wcel vz cv cA wcel wa wph vx vz weq vy vw
      weq wa wi vy cB wral vx cA wral wa vw cv cB wcel vz cv cA wcel wph vx vz
      weq vy vw weq wa wi vy cB wral vx cA wral wa wa wph vy cB wrex vx cA wrex
      wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw cv cB wcel vz cv
      cA wcel wa wph vy cB wrex vx cA wrex wph vx vz weq vy vw weq wa wi vy cB
      wral vx cA wral vw cv cB wcel vz cv cA wcel wa wph vy cB wrex vx cA wrex
      wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral wa wph vy cB wrex wph
      vx vz weq vy vw weq wa wi vy cB wral wa vx cA wrex wph wph vx vz weq vy
      vw weq wa wi wa vy cB wrex vx cA wrex vw cv cB wcel vz cv cA wcel wa wph
      vy cB wrex wph vx vz weq vy vw weq wa wi vy cB wral vx cA r19.29r wph vy
      cB wrex wph vx vz weq vy vw weq wa wi vy cB wral wa wph wph vx vz weq vy
      vw weq wa wi wa vy cB wrex vx cA wph wph vx vz weq vy vw weq wa wi vy cB
      r19.29r reximi wph wph vx vz weq vy vw weq wa wi wa vy cB wrex vx cA wrex
      vx vz weq vy vw weq wa vy cB wrex vx cA wrex vw cv cB wcel vz cv cA wcel
      wa wph wph vx vz weq vy vw weq wa wi wa vy cB wrex vx vz weq vy vw weq wa
      vy cB wrex vx cA wph wph vx vz weq vy vw weq wa wi wa vx vz weq vy vw weq
      wa vy cB wph vx vz weq vy vw weq wa pm3.35 reximi reximi vx vz weq vy vw
      weq wa vw cv cB wcel vz cv cA wcel wa vx vy cA cB vx cv cA wcel vy cv cB
      wcel wa vx vz weq vy vw weq wa vw cv cB wcel vz cv cA wcel wa vx cv cA
      wcel vy cv cB wcel wa vx vz weq vy vw weq wa wa vz cv cA wcel vw cv cB
      wcel vx vz weq vy vw weq wa vx cv cA wcel vy cv cB wcel wa vz cv cA wcel
      vw cv cB wcel wa vx vz weq vx cv cA wcel vz cv cA wcel vy vw weq vy cv cB
      wcel vw cv cB wcel vx cv vz cv cA eleq1 vy cv vw cv cB eleq1 bi2anan9
      biimpac ancomd ex rexlimivv syl 3syl ex pm4.71rd vw cv cB wcel vz cv cA
      wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral anass syl6bb
      2exbidv pm5.32i wph vx vy vz vw cA cB 2reu5lem3 wph vx vz weq vy vw weq
      wa wi vy cB wral vx cA wral vw cB wrex vz cA wrex vw cv cB wcel vz cv cA
      wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral wa wa vw wex vz
      wex wph vy cB wrex vx cA wrex wph vx vz weq vy vw weq wa wi vy cB wral vx
      cA wral vw cB wrex vz cA wrex vz cv cA wcel wph vx vz weq vy vw weq wa wi
      vy cB wral vx cA wral vw cB wrex wa vz wex vw cv cB wcel vz cv cA wcel
      wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral wa wa vw wex vz wex
      wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw cB wrex vz cA
      df-rex vz cv cA wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral
      vw cB wrex wa vw cv cB wcel vz cv cA wcel wph vx vz weq vy vw weq wa wi
      vy cB wral vx cA wral wa wa vw wex vz vz cv cA wcel wph vx vz weq vy vw
      weq wa wi vy cB wral vx cA wral vw cB wrex wa vz cv cA wcel wph vx vz weq
      vy vw weq wa wi vy cB wral vx cA wral wa vw cB wrex vw cv cB wcel vz cv
      cA wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral wa wa vw wex
      vz cv cA wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral vw cB
      r19.42v vz cv cA wcel wph vx vz weq vy vw weq wa wi vy cB wral vx cA wral
      wa vw cB df-rex bitr3i exbii bitri anbi2i 3bitr4i $.
  $}


