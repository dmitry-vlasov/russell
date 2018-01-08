
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Subclasses_and_subsets.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        The difference, union, and intersection of two classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Equality theorem for class difference.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    difeq1 $p |- ( A = B -> ( A \ C ) = ( B \ C ) ) $=
      cA cB wceq vx cv cC wcel wn vx cA crab vx cv cC wcel wn vx cB crab cA cC
      cdif cB cC cdif vx cv cC wcel wn vx cA cB rabeq vx cA cC dfdif2 vx cB cC
      dfdif2 3eqtr4g $.

    $( Equality theorem for class difference.  (Contributed by NM,
       10-Feb-1997.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    difeq2 $p |- ( A = B -> ( C \ A ) = ( C \ B ) ) $=
      cA cB wceq vx cv cA wcel wn vx cC crab vx cv cB wcel wn vx cC crab cC cA
      cdif cC cB cdif cA cB wceq vx cv cA wcel wn vx cv cB wcel wn vx cC cA cB
      wceq vx cv cA wcel vx cv cB wcel cA cB vx cv eleq2 notbid rabbidv vx cC
      cA dfdif2 vx cC cB dfdif2 3eqtr4g $.
  $}

  $( Equality theorem for class difference.  (Contributed by FL,
     31-Aug-2009.) $)
  difeq12 $p |- ( ( A = B /\ C = D ) -> ( A \ C ) = ( B \ D ) ) $=
    cA cB wceq cC cD wceq cA cC cdif cB cC cdif cB cD cdif cA cB cC difeq1 cC
    cD cB difeq2 sylan9eq $.

  ${
    difeq1i.1 $e |- A = B $.
    $( Inference adding difference to the right in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
    difeq1i $p |- ( A \ C ) = ( B \ C ) $=
      cA cB wceq cA cC cdif cB cC cdif wceq difeq1i.1 cA cB cC difeq1 ax-mp $.

    $( Inference adding difference to the left in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
    difeq2i $p |- ( C \ A ) = ( C \ B ) $=
      cA cB wceq cC cA cdif cC cB cdif wceq difeq1i.1 cA cB cC difeq2 ax-mp $.

    ${
      difeq12i.2 $e |- C = D $.
      $( Equality inference for class difference.  (Contributed by NM,
         29-Aug-2004.) $)
      difeq12i $p |- ( A \ C ) = ( B \ D ) $=
        cA cC cdif cB cC cdif cB cD cdif cA cB cC difeq1i.1 difeq1i cC cD cB
        difeq12i.2 difeq2i eqtri $.
    $}
  $}

  ${
    difeq1d.1 $e |- ( ph -> A = B ) $.
    $( Deduction adding difference to the right in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
    difeq1d $p |- ( ph -> ( A \ C ) = ( B \ C ) ) $=
      wph cA cB wceq cA cC cdif cB cC cdif wceq difeq1d.1 cA cB cC difeq1 syl
      $.

    $( Deduction adding difference to the left in a class equality.
       (Contributed by NM, 15-Nov-2002.) $)
    difeq2d $p |- ( ph -> ( C \ A ) = ( C \ B ) ) $=
      wph cA cB wceq cC cA cdif cC cB cdif wceq difeq1d.1 cA cB cC difeq2 syl
      $.
  $}

  ${
    difeq12d.1 $e |- ( ph -> A = B ) $.
    difeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for class difference.  (Contributed by FL,
       29-May-2014.) $)
    difeq12d $p |- ( ph -> ( A \ C ) = ( B \ D ) ) $=
      wph cA cC cdif cB cC cdif cB cD cdif wph cA cB cC difeq12d.1 difeq1d wph
      cC cD cB difeq12d.2 difeq2d eqtrd $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    difeqri.1 $e |- ( ( x e. A /\ -. x e. B ) <-> x e. C ) $.
    $( Inference from membership to difference.  (Contributed by NM,
       17-May-1998.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    difeqri $p |- ( A \ B ) = C $=
      vx cA cB cdif cC vx cv cA cB cdif wcel vx cv cA wcel vx cv cB wcel wn wa
      vx cv cC wcel vx cv cA cB eldif difeqri.1 bitri eqriv $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    nfdif.1 $e |- F/_ x A $.
    nfdif.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for class difference.  (Contributed by
       NM, 3-Dec-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)
    nfdif $p |- F/_ x ( A \ B ) $=
      vx cA cB cdif vy cv cB wcel wn vy cA crab vy cA cB dfdif2 vy cv cB wcel
      wn vx vy cA vy cv cB wcel vx vx vy cB nfdif.2 nfcri nfn nfdif.1 nfrab
      nfcxfr $.
  $}

  $( Implication of membership in a class difference.  (Contributed by NM,
     29-Apr-1994.) $)
  eldifi $p |- ( A e. ( B \ C ) -> A e. B ) $=
    cA cB cC cdif wcel cA cB wcel cA cC wcel wn cA cB cC eldif simplbi $.

  $( Implication of membership in a class difference.  (Contributed by NM,
     3-May-1994.) $)
  eldifn $p |- ( A e. ( B \ C ) -> -. A e. C ) $=
    cA cB cC cdif wcel cA cB wcel cA cC wcel wn cA cB cC eldif simprbi $.

  $( A set does not belong to a class excluding it.  (Contributed by NM,
     27-Jun-1994.) $)
  elndif $p |- ( A e. B -> -. A e. ( C \ B ) ) $=
    cA cC cB cdif wcel cA cB wcel cA cC cB eldifn con2i $.

  $( Implication of membership in a class difference.  (Contributed by NM,
     28-Jun-1994.) $)
  neldif $p |- ( ( A e. B /\ -. A e. ( B \ C ) ) -> A e. C ) $=
    cA cB wcel cA cB cC cdif wcel wn cA cC wcel cA cB wcel cA cC wcel cA cB cC
    cdif wcel cA cB cC cdif wcel cA cB wcel cA cC wcel wn cA cB cC eldif
    simplbi2 con1d imp $.

  ${
    $d x A $.  $d x B $.
    $( Double class difference.  Exercise 11 of [TakeutiZaring] p. 22.
       (Contributed by NM, 17-May-1998.) $)
    difdif $p |- ( A \ ( B \ A ) ) = A $=
      vx cA cB cA cdif cA vx cv cA wcel vx cv cA wcel vx cv cB wcel vx cv cA
      wcel wi wa vx cv cA wcel vx cv cB cA cdif wcel wn wa vx cv cA wcel vx cv
      cB wcel pm4.45im vx cv cB wcel vx cv cA wcel wi vx cv cB cA cdif wcel wn
      vx cv cA wcel vx cv cB wcel vx cv cA wcel wi vx cv cB wcel vx cv cA wcel
      wn wa vx cv cB cA cdif wcel vx cv cB wcel vx cv cA wcel iman vx cv cB cA
      eldif xchbinxr anbi2i bitr2i difeqri $.

    $( Subclass relationship for class difference.  Exercise 14 of
       [TakeutiZaring] p. 22.  (Contributed by NM, 29-Apr-1994.) $)
    difss $p |- ( A \ B ) C_ A $=
      vx cA cB cdif cA vx cv cA cB eldifi ssriv $.
  $}

  $( A difference of two classes is contained in the minuend.  Deduction form
     of ~ difss .  (Contributed by David Moews, 1-May-2017.) $)
  difssd $p |- ( ph -> ( A \ B ) C_ A ) $=
    cA cB cdif cA wss wph cA cB difss a1i $.

  $( If a class is contained in a difference, it is contained in the minuend.
     (Contributed by David Moews, 1-May-2017.) $)
  difss2 $p |- ( A C_ ( B \ C ) -> A C_ B ) $=
    cA cB cC cdif wss cA cB cC cdif cB cA cB cC cdif wss id cB cC difss syl6ss
    $.

  ${
    difss2d.1 $e |- ( ph -> A C_ ( B \ C ) ) $.
    $( If a class is contained in a difference, it is contained in the
       minuend.  Deduction form of ~ difss2 .  (Contributed by David Moews,
       1-May-2017.) $)
    difss2d $p |- ( ph -> A C_ B ) $=
      wph cA cB cC cdif wss cA cB wss difss2d.1 cA cB cC difss2 syl $.
  $}

  $( Preservation of a subclass relationship by class difference.  (Contributed
     by NM, 15-Feb-2007.) $)
  ssdifss $p |- ( A C_ B -> ( A \ C ) C_ B ) $=
    cA cC cdif cA wss cA cB wss cA cC cdif cB wss cA cC difss cA cC cdif cA cB
    sstr mpan $.

  ${
    $d x A $.
    $( Double complement under universal class.  Exercise 4.10(s) of
       [Mendelson] p. 231.  (Contributed by NM, 8-Jan-2002.) $)
    ddif $p |- ( _V \ ( _V \ A ) ) = A $=
      vx cvv cvv cA cdif cA vx cv cA wcel vx cv cvv cA cdif wcel wn vx cv cvv
      wcel vx cv cvv cA cdif wcel wn wa vx cv cvv cA cdif wcel vx cv cA wcel vx
      cv cvv cA cdif wcel vx cv cvv wcel vx cv cA wcel wn vx vex vx cv cvv cA
      eldif mpbiran con2bii vx cv cvv wcel vx cv cvv cA cdif wcel wn vx vex
      biantrur bitr2i difeqri $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Contraposition law for subsets.  (Contributed by NM, 22-Mar-1998.) $)
    ssconb $p |- ( ( A C_ C /\ B C_ C ) ->
                  ( A C_ ( C \ B ) <-> B C_ ( C \ A ) ) ) $=
      cA cC wss cB cC wss wa vx cv cA wcel vx cv cC cB cdif wcel wi vx wal vx
      cv cB wcel vx cv cC cA cdif wcel wi vx wal cA cC cB cdif wss cB cC cA
      cdif wss cA cC wss cB cC wss wa vx cv cA wcel vx cv cC cB cdif wcel wi vx
      cv cB wcel vx cv cC cA cdif wcel wi vx cA cC wss cB cC wss wa vx cv cA
      wcel vx cv cC wcel vx cv cB wcel wn wa wi vx cv cB wcel vx cv cC wcel vx
      cv cA wcel wn wa wi vx cv cA wcel vx cv cC cB cdif wcel wi vx cv cB wcel
      vx cv cC cA cdif wcel wi cA cC wss cB cC wss wa vx cv cA wcel vx cv cC
      wcel wi vx cv cA wcel vx cv cB wcel wn wi wa vx cv cB wcel vx cv cC wcel
      wi vx cv cB wcel vx cv cA wcel wn wi wa vx cv cA wcel vx cv cC wcel vx cv
      cB wcel wn wa wi vx cv cB wcel vx cv cC wcel vx cv cA wcel wn wa wi cA cC
      wss cB cC wss wa vx cv cA wcel vx cv cC wcel wi vx cv cB wcel vx cv cC
      wcel wi vx cv cA wcel vx cv cB wcel wn wi vx cv cB wcel vx cv cA wcel wn
      wi cA cC wss vx cv cA wcel vx cv cC wcel wi vx cv cB wcel vx cv cC wcel
      wi vx cv cA wcel vx cv cC wcel wi vx cv cB wcel vx cv cC wcel wi wb cB cC
      wss cA cC vx cv ssel cB cC vx cv ssel vx cv cA wcel vx cv cC wcel wi vx
      cv cB wcel vx cv cC wcel wi pm5.1 syl2an vx cv cA wcel vx cv cB wcel wn
      wi vx cv cB wcel vx cv cA wcel wn wi wb cA cC wss cB cC wss wa vx cv cA
      wcel vx cv cB wcel con2b a1i anbi12d vx cv cA wcel vx cv cC wcel vx cv cB
      wcel wn jcab vx cv cB wcel vx cv cC wcel vx cv cA wcel wn jcab 3bitr4g vx
      cv cC cB cdif wcel vx cv cC wcel vx cv cB wcel wn wa vx cv cA wcel vx cv
      cC cB eldif imbi2i vx cv cC cA cdif wcel vx cv cC wcel vx cv cA wcel wn
      wa vx cv cB wcel vx cv cC cA eldif imbi2i 3bitr4g albidv vx cA cC cB cdif
      dfss2 vx cB cC cA cdif dfss2 3bitr4g $.

    $( Contraposition law for subsets.  Exercise 15 of [TakeutiZaring] p. 22.
       (Contributed by NM, 22-Mar-1998.) $)
    sscon $p |- ( A C_ B -> ( C \ B ) C_ ( C \ A ) ) $=
      cA cB wss vx cC cB cdif cC cA cdif cA cB wss vx cv cC wcel vx cv cB wcel
      wn wa vx cv cC wcel vx cv cA wcel wn wa vx cv cC cB cdif wcel vx cv cC cA
      cdif wcel cA cB wss vx cv cB wcel wn vx cv cA wcel wn vx cv cC wcel cA cB
      wss vx cv cA wcel vx cv cB wcel cA cB vx cv ssel con3d anim2d vx cv cC cB
      eldif vx cv cC cA eldif 3imtr4g ssrdv $.

    $( Difference law for subsets.  (Contributed by NM, 28-May-1998.) $)
    ssdif $p |- ( A C_ B -> ( A \ C ) C_ ( B \ C ) ) $=
      cA cB wss vx cA cC cdif cB cC cdif cA cB wss vx cv cA wcel vx cv cC wcel
      wn wa vx cv cB wcel vx cv cC wcel wn wa vx cv cA cC cdif wcel vx cv cB cC
      cdif wcel cA cB wss vx cv cA wcel vx cv cB wcel vx cv cC wcel wn cA cB vx
      cv ssel anim1d vx cv cA cC eldif vx cv cB cC eldif 3imtr4g ssrdv $.
  $}

  ${
    ssdifd.1 $e |- ( ph -> A C_ B ) $.
    $( If ` A ` is contained in ` B ` , then ` ( A \ C ) ` is contained in
       ` ( B \ C ) ` .  Deduction form of ~ ssdif .  (Contributed by David
       Moews, 1-May-2017.) $)
    ssdifd $p |- ( ph -> ( A \ C ) C_ ( B \ C ) ) $=
      wph cA cB wss cA cC cdif cB cC cdif wss ssdifd.1 cA cB cC ssdif syl $.

    $( If ` A ` is contained in ` B ` , then ` ( C \ B ) ` is contained in
       ` ( C \ A ) ` .  Deduction form of ~ sscon .  (Contributed by David
       Moews, 1-May-2017.) $)
    sscond $p |- ( ph -> ( C \ B ) C_ ( C \ A ) ) $=
      wph cA cB wss cC cB cdif cC cA cdif wss ssdifd.1 cA cB cC sscon syl $.

    $( If ` A ` is contained in ` B ` , then ` ( A \ C ) ` is also contained in
       ` B ` .  Deduction form of ~ ssdifss .  (Contributed by David Moews,
       1-May-2017.) $)
    ssdifssd $p |- ( ph -> ( A \ C ) C_ B ) $=
      wph cA cB wss cA cC cdif cB wss ssdifd.1 cA cB cC ssdifss syl $.

    ssdif2d.2 $e |- ( ph -> C C_ D ) $.
    $( If ` A ` is contained in ` B ` and ` C ` is contained in ` D ` , then
       ` ( A \ D ) ` is contained in ` ( B \ C ) ` .  Deduction form.
       (Contributed by David Moews, 1-May-2017.) $)
    ssdif2d $p |- ( ph -> ( A \ D ) C_ ( B \ C ) ) $=
      wph cA cD cdif cA cC cdif cB cC cdif wph cC cD cA ssdif2d.2 sscond wph cA
      cB cC ssdifd.1 ssdifd sstrd $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Expansion of membership in class union.  Theorem 12 of [Suppes] p. 25.
       (Contributed by NM, 7-Aug-1994.) $)
    elun $p |- ( A e. ( B u. C ) <-> ( A e. B \/ A e. C ) ) $=
      cA cB cC cun wcel cA cvv wcel cA cB wcel cA cC wcel wo cA cB cC cun elex
      cA cB wcel cA cvv wcel cA cC wcel cA cB elex cA cC elex jaoi vx cv cB
      wcel vx cv cC wcel wo cA cB wcel cA cC wcel wo vx cA cB cC cun cvv vx cv
      cA wceq vx cv cB wcel cA cB wcel vx cv cC wcel cA cC wcel vx cv cA cB
      eleq1 vx cv cA cC eleq1 orbi12d vx cB cC df-un elab2g pm5.21nii $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    uneqri.1 $e |- ( ( x e. A \/ x e. B ) <-> x e. C ) $.
    $( Inference from membership to union.  (Contributed by NM, 5-Aug-1993.) $)
    uneqri $p |- ( A u. B ) = C $=
      vx cA cB cun cC vx cv cA cB cun wcel vx cv cA wcel vx cv cB wcel wo vx cv
      cC wcel vx cv cA cB elun uneqri.1 bitri eqriv $.
  $}

  ${
    $d x A $.
    $( Idempotent law for union of classes.  Theorem 23 of [Suppes] p. 27.
       (Contributed by NM, 5-Aug-1993.) $)
    unidm $p |- ( A u. A ) = A $=
      vx cA cA cA vx cv cA wcel oridm uneqri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Commutative law for union of classes.  Exercise 6 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 25-Jun-1998.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
    uncom $p |- ( A u. B ) = ( B u. A ) $=
      vx cA cB cB cA cun vx cv cA wcel vx cv cB wcel wo vx cv cB wcel vx cv cA
      wcel wo vx cv cB cA cun wcel vx cv cA wcel vx cv cB wcel orcom vx cv cB
      cA elun bitr4i uneqri $.
  $}

  ${
    $( If a class equals the union of two other classes, then it equals the
       union of those two classes commuted. ~ equncom was automatically derived
       from ~ equncomVD using the tools program
       translate_without_overwriting.cmd and minimizing.  (Contributed by Alan
       Sare, 18-Feb-2012.) $)
    equncom $p |- ( A = ( B u. C ) <-> A = ( C u. B ) ) $=
      cB cC cun cC cB cun cA cB cC uncom eqeq2i $.
  $}

  ${
    equncomi.1 $e |- A = ( B u. C ) $.
    $( Inference form of ~ equncom . ~ equncomi was automatically derived from
       ~ equncomiVD using the tools program translate_without_overwriting.cmd
       and minimizing.  (Contributed by Alan Sare, 18-Feb-2012.) $)
    equncomi $p |- A = ( C u. B ) $=
      cA cB cC cun wceq cA cC cB cun wceq equncomi.1 cA cB cC equncom mpbi $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Equality theorem for union of two classes.  (Contributed by NM,
       5-Aug-1993.) $)
    uneq1 $p |- ( A = B -> ( A u. C ) = ( B u. C ) ) $=
      cA cB wceq vx cA cC cun cB cC cun cA cB wceq vx cv cA wcel vx cv cC wcel
      wo vx cv cB wcel vx cv cC wcel wo vx cv cA cC cun wcel vx cv cB cC cun
      wcel cA cB wceq vx cv cA wcel vx cv cB wcel vx cv cC wcel cA cB vx cv
      eleq2 orbi1d vx cv cA cC elun vx cv cB cC elun 3bitr4g eqrdv $.
  $}

  $( Equality theorem for the union of two classes.  (Contributed by NM,
     5-Aug-1993.) $)
  uneq2 $p |- ( A = B -> ( C u. A ) = ( C u. B ) ) $=
    cA cB wceq cA cC cun cB cC cun cC cA cun cC cB cun cA cB cC uneq1 cC cA
    uncom cC cB uncom 3eqtr4g $.

  $( Equality theorem for union of two classes.  (Contributed by NM,
     29-Mar-1998.) $)
  uneq12 $p |- ( ( A = B /\ C = D ) -> ( A u. C ) = ( B u. D ) ) $=
    cA cB wceq cC cD wceq cA cC cun cB cC cun cB cD cun cA cB cC uneq1 cC cD cB
    uneq2 sylan9eq $.

  ${
    uneq1i.1 $e |- A = B $.
    $( Inference adding union to the right in a class equality.  (Contributed
       by NM, 30-Aug-1993.) $)
    uneq1i $p |- ( A u. C ) = ( B u. C ) $=
      cA cB wceq cA cC cun cB cC cun wceq uneq1i.1 cA cB cC uneq1 ax-mp $.

    $( Inference adding union to the left in a class equality.  (Contributed by
       NM, 30-Aug-1993.) $)
    uneq2i $p |- ( C u. A ) = ( C u. B ) $=
      cA cB wceq cC cA cun cC cB cun wceq uneq1i.1 cA cB cC uneq2 ax-mp $.

    ${
      uneq12i.2 $e |- C = D $.
      $( Equality inference for union of two classes.  (Contributed by NM,
         12-Aug-2004.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)
      uneq12i $p |- ( A u. C ) = ( B u. D ) $=
        cA cB wceq cC cD wceq cA cC cun cB cD cun wceq uneq1i.1 uneq12i.2 cA cB
        cC cD uneq12 mp2an $.
    $}
  $}

  ${
    uneq1d.1 $e |- ( ph -> A = B ) $.
    $( Deduction adding union to the right in a class equality.  (Contributed
       by NM, 29-Mar-1998.) $)
    uneq1d $p |- ( ph -> ( A u. C ) = ( B u. C ) ) $=
      wph cA cB wceq cA cC cun cB cC cun wceq uneq1d.1 cA cB cC uneq1 syl $.

    $( Deduction adding union to the left in a class equality.  (Contributed by
       NM, 29-Mar-1998.) $)
    uneq2d $p |- ( ph -> ( C u. A ) = ( C u. B ) ) $=
      wph cA cB wceq cC cA cun cC cB cun wceq uneq1d.1 cA cB cC uneq2 syl $.

    ${
      uneq12d.2 $e |- ( ph -> C = D ) $.
      $( Equality deduction for union of two classes.  (Contributed by NM,
         29-Sep-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
      uneq12d $p |- ( ph -> ( A u. C ) = ( B u. D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cun cB cD cun wceq uneq1d.1 uneq12d.2
        cA cB cC cD uneq12 syl2anc $.
    $}
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    nfun.1 $e |- F/_ x A $.
    nfun.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for the union of classes.
       (Contributed by NM, 15-Sep-2003.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
    nfun $p |- F/_ x ( A u. B ) $=
      vx cA cB cun vy cv cA wcel vy cv cB wcel wo vy cab vy cA cB df-un vy cv
      cA wcel vy cv cB wcel wo vx vy vy cv cA wcel vy cv cB wcel vx vx vy cA
      nfun.1 nfcri vx vy cB nfun.2 nfcri nfor nfab nfcxfr $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( Associative law for union of classes.  Exercise 8 of [TakeutiZaring]
       p. 17.  (Contributed by NM, 3-May-1994.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
    unass $p |- ( ( A u. B ) u. C ) = ( A u. ( B u. C ) ) $=
      vx cA cB cun cC cA cB cC cun cun vx cv cA cB cC cun cun wcel vx cv cA
      wcel vx cv cB cC cun wcel wo vx cv cA wcel vx cv cB wcel vx cv cC wcel wo
      wo vx cv cA cB cun wcel vx cv cC wcel wo vx cv cA cB cC cun elun vx cv cB
      cC cun wcel vx cv cB wcel vx cv cC wcel wo vx cv cA wcel vx cv cB cC elun
      orbi2i vx cv cA cB cun wcel vx cv cC wcel wo vx cv cA wcel vx cv cB wcel
      wo vx cv cC wcel wo vx cv cA wcel vx cv cB wcel vx cv cC wcel wo wo vx cv
      cA cB cun wcel vx cv cA wcel vx cv cB wcel wo vx cv cC wcel vx cv cA cB
      elun orbi1i vx cv cA wcel vx cv cB wcel vx cv cC wcel orass bitr2i
      3bitrri uneqri $.
  $}

  $( A rearrangement of union.  (Contributed by NM, 12-Aug-2004.) $)
  un12 $p |- ( A u. ( B u. C ) ) = ( B u. ( A u. C ) ) $=
    cA cB cun cC cun cB cA cun cC cun cA cB cC cun cun cB cA cC cun cun cA cB
    cun cB cA cun cC cA cB uncom uneq1i cA cB cC unass cB cA cC unass 3eqtr3i
    $.

  $( A rearrangement of union.  (Contributed by NM, 12-Aug-2004.)  (Proof
     shortened by Andrew Salmon, 26-Jun-2011.) $)
  un23 $p |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. B ) $=
    cA cB cun cC cun cA cB cC cun cun cB cA cC cun cun cA cC cun cB cun cA cB
    cC unass cA cB cC un12 cB cA cC cun uncom 3eqtri $.

  $( A rearrangement of the union of 4 classes.  (Contributed by NM,
     12-Aug-2004.) $)
  un4 $p |- ( ( A u. B ) u. ( C u. D ) ) =
            ( ( A u. C ) u. ( B u. D ) ) $=
    cA cB cC cD cun cun cun cA cC cB cD cun cun cun cA cB cun cC cD cun cun cA
    cC cun cB cD cun cun cB cC cD cun cun cC cB cD cun cun cA cB cC cD un12
    uneq2i cA cB cC cD cun unass cA cC cB cD cun unass 3eqtr4i $.

  $( Union distributes over itself.  (Contributed by NM, 17-Aug-2004.) $)
  unundi $p |- ( A u. ( B u. C ) ) = ( ( A u. B ) u. ( A u. C ) ) $=
    cA cA cun cB cC cun cun cA cB cC cun cun cA cB cun cA cC cun cun cA cA cun
    cA cB cC cun cA unidm uneq1i cA cA cB cC un4 eqtr3i $.

  $( Union distributes over itself.  (Contributed by NM, 17-Aug-2004.) $)
  unundir $p |- ( ( A u. B ) u. C ) = ( ( A u. C ) u. ( B u. C ) ) $=
    cA cB cun cC cC cun cun cA cB cun cC cun cA cC cun cB cC cun cun cC cC cun
    cC cA cB cun cC unidm uneq2i cA cB cC cC un4 eqtr3i $.

  ${
    $d x A $.  $d x B $.
    $( Subclass relationship for union of classes.  Theorem 25 of [Suppes]
       p. 27.  (Contributed by NM, 5-Aug-1993.) $)
    ssun1 $p |- A C_ ( A u. B ) $=
      vx cA cA cB cun vx cv cA wcel vx cv cA wcel vx cv cB wcel wo vx cv cA cB
      cun wcel vx cv cA wcel vx cv cB wcel orc vx cv cA cB elun sylibr ssriv $.
  $}

  $( Subclass relationship for union of classes.  (Contributed by NM,
     30-Aug-1993.) $)
  ssun2 $p |- A C_ ( B u. A ) $=
    cA cA cB cun cB cA cun cA cB ssun1 cA cB uncom sseqtri $.

  $( Subclass law for union of classes.  (Contributed by NM, 5-Aug-1993.) $)
  ssun3 $p |- ( A C_ B -> A C_ ( B u. C ) ) $=
    cA cB wss cB cB cC cun wss cA cB cC cun wss cB cC ssun1 cA cB cB cC cun
    sstr2 mpi $.

  $( Subclass law for union of classes.  (Contributed by NM, 14-Aug-1994.) $)
  ssun4 $p |- ( A C_ B -> A C_ ( C u. B ) ) $=
    cA cB wss cB cC cB cun wss cA cC cB cun wss cB cC ssun2 cA cB cC cB cun
    sstr2 mpi $.

  $( Membership law for union of classes.  (Contributed by NM, 5-Aug-1993.) $)
  elun1 $p |- ( A e. B -> A e. ( B u. C ) ) $=
    cB cB cC cun cA cB cC ssun1 sseli $.

  $( Membership law for union of classes.  (Contributed by NM, 30-Aug-1993.) $)
  elun2 $p |- ( A e. B -> A e. ( C u. B ) ) $=
    cB cC cB cun cA cB cC ssun2 sseli $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Subclass law for union of classes.  (Contributed by NM, 14-Oct-1999.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    unss1 $p |- ( A C_ B -> ( A u. C ) C_ ( B u. C ) ) $=
      cA cB wss vx cA cC cun cB cC cun cA cB wss vx cv cA wcel vx cv cC wcel wo
      vx cv cB wcel vx cv cC wcel wo vx cv cA cC cun wcel vx cv cB cC cun wcel
      cA cB wss vx cv cA wcel vx cv cB wcel vx cv cC wcel cA cB vx cv ssel
      orim1d vx cv cA cC elun vx cv cB cC elun 3imtr4g ssrdv $.

    $( A relationship between subclass and union.  Theorem 26 of [Suppes]
       p. 27.  (Contributed by NM, 30-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
    ssequn1 $p |- ( A C_ B <-> ( A u. B ) = B ) $=
      vx cv cA wcel vx cv cB wcel wi vx wal vx cv cA cB cun wcel vx cv cB wcel
      wb vx wal cA cB wss cA cB cun cB wceq vx cv cA wcel vx cv cB wcel wi vx
      cv cA cB cun wcel vx cv cB wcel wb vx vx cv cB wcel vx cv cA wcel vx cv
      cB wcel wo wb vx cv cA wcel vx cv cB wcel wo vx cv cB wcel wb vx cv cA
      wcel vx cv cB wcel wi vx cv cA cB cun wcel vx cv cB wcel wb vx cv cB wcel
      vx cv cA wcel vx cv cB wcel wo bicom vx cv cA wcel vx cv cB wcel pm4.72
      vx cv cA cB cun wcel vx cv cA wcel vx cv cB wcel wo vx cv cB wcel vx cv
      cA cB elun bibi1i 3bitr4i albii vx cA cB dfss2 vx cA cB cun cB dfcleq
      3bitr4i $.
  $}

  $( Subclass law for union of classes.  Exercise 7 of [TakeutiZaring] p. 18.
     (Contributed by NM, 14-Oct-1999.) $)
  unss2 $p |- ( A C_ B -> ( C u. A ) C_ ( C u. B ) ) $=
    cA cB wss cA cC cun cB cC cun cC cA cun cC cB cun cA cB cC unss1 cC cA
    uncom cC cB uncom 3sstr4g $.

  $( Subclass law for union of classes.  (Contributed by NM, 2-Jun-2004.) $)
  unss12 $p |- ( ( A C_ B /\ C C_ D ) -> ( A u. C ) C_ ( B u. D ) ) $=
    cA cB wss cC cD wss cA cC cun cB cC cun cB cD cun cA cB cC unss1 cC cD cB
    unss2 sylan9ss $.

  $( A relationship between subclass and union.  (Contributed by NM,
     13-Jun-1994.) $)
  ssequn2 $p |- ( A C_ B <-> ( B u. A ) = B ) $=
    cA cB wss cA cB cun cB wceq cB cA cun cB wceq cA cB ssequn1 cA cB cun cB cA
    cun cB cA cB uncom eqeq1i bitri $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( The union of two subclasses is a subclass.  Theorem 27 of [Suppes] p. 27
       and its converse.  (Contributed by NM, 11-Jun-2004.) $)
    unss $p |- ( ( A C_ C /\ B C_ C ) <-> ( A u. B ) C_ C ) $=
      cA cB cun cC wss vx cv cA cB cun wcel vx cv cC wcel wi vx wal cA cC wss
      cB cC wss wa vx cA cB cun cC dfss2 vx cv cA wcel vx cv cC wcel wi vx cv
      cB wcel vx cv cC wcel wi wa vx wal vx cv cA wcel vx cv cC wcel wi vx wal
      vx cv cB wcel vx cv cC wcel wi vx wal wa vx cv cA cB cun wcel vx cv cC
      wcel wi vx wal cA cC wss cB cC wss wa vx cv cA wcel vx cv cC wcel wi vx
      cv cB wcel vx cv cC wcel wi vx 19.26 vx cv cA cB cun wcel vx cv cC wcel
      wi vx cv cA wcel vx cv cC wcel wi vx cv cB wcel vx cv cC wcel wi wa vx vx
      cv cA cB cun wcel vx cv cC wcel wi vx cv cA wcel vx cv cB wcel wo vx cv
      cC wcel wi vx cv cA wcel vx cv cC wcel wi vx cv cB wcel vx cv cC wcel wi
      wa vx cv cA cB cun wcel vx cv cA wcel vx cv cB wcel wo vx cv cC wcel vx
      cv cA cB elun imbi1i vx cv cA wcel vx cv cC wcel vx cv cB wcel jaob bitri
      albii cA cC wss vx cv cA wcel vx cv cC wcel wi vx wal cB cC wss vx cv cB
      wcel vx cv cC wcel wi vx wal vx cA cC dfss2 vx cB cC dfss2 anbi12i
      3bitr4i bitr2i $.
  $}

  ${
    unssi.1 $e |- A C_ C $.
    unssi.2 $e |- B C_ C $.
    $( An inference showing the union of two subclasses is a subclass.
       (Contributed by Raph Levien, 10-Dec-2002.) $)
    unssi $p |- ( A u. B ) C_ C $=
      cA cC wss cB cC wss wa cA cB cun cC wss cA cC wss cB cC wss unssi.1
      unssi.2 pm3.2i cA cB cC unss mpbi $.
  $}

  ${
    unssd.1 $e |- ( ph -> A C_ C ) $.
    unssd.2 $e |- ( ph -> B C_ C ) $.
    $( A deduction showing the union of two subclasses is a subclass.
       (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    unssd $p |- ( ph -> ( A u. B ) C_ C ) $=
      wph cA cC wss cB cC wss cA cB cun cC wss unssd.1 unssd.2 cA cC wss cB cC
      wss wa cA cB cun cC wss cA cB cC unss biimpi syl2anc $.
  $}

  ${
    unssad.1 $e |- ( ph -> ( A u. B ) C_ C ) $.
    $( If ` ( A u. B ) ` is contained in ` C ` , so is ` A ` .  One-way
       deduction form of ~ unss .  Partial converse of ~ unssd .  (Contributed
       by David Moews, 1-May-2017.) $)
    unssad $p |- ( ph -> A C_ C ) $=
      wph cA cC wss cB cC wss wph cA cB cun cC wss cA cC wss cB cC wss wa
      unssad.1 cA cB cC unss sylibr simpld $.

    $( If ` ( A u. B ) ` is contained in ` C ` , so is ` B ` .  One-way
       deduction form of ~ unss .  Partial converse of ~ unssd .  (Contributed
       by David Moews, 1-May-2017.) $)
    unssbd $p |- ( ph -> B C_ C ) $=
      wph cA cC wss cB cC wss wph cA cB cun cC wss cA cC wss cB cC wss wa
      unssad.1 cA cB cC unss sylibr simprd $.
  $}

  $( A condition that implies inclusion in the union of two classes.
     (Contributed by NM, 23-Nov-2003.) $)
  ssun $p |- ( ( A C_ B \/ A C_ C ) -> A C_ ( B u. C ) ) $=
    cA cB wss cA cB cC cun wss cA cC wss cA cB cC ssun3 cA cC cB ssun4 jaoi $.

  $( Restricted existential quantification over union.  (Contributed by Jeff
     Madsen, 5-Jan-2011.) $)
  rexun $p |- ( E. x e. ( A u. B ) ph <->
                          ( E. x e. A ph \/ E. x e. B ph ) ) $=
    wph vx cA cB cun wrex vx cv cA cB cun wcel wph wa vx wex wph vx cA wrex wph
    vx cB wrex wo wph vx cA cB cun df-rex vx cv cA wcel wph wa vx cv cB wcel
    wph wa wo vx wex vx cv cA wcel wph wa vx wex vx cv cB wcel wph wa vx wex wo
    vx cv cA cB cun wcel wph wa vx wex wph vx cA wrex wph vx cB wrex wo vx cv
    cA wcel wph wa vx cv cB wcel wph wa vx 19.43 vx cv cA cB cun wcel wph wa vx
    cv cA wcel wph wa vx cv cB wcel wph wa wo vx vx cv cA cB cun wcel wph wa vx
    cv cA wcel vx cv cB wcel wo wph wa vx cv cA wcel wph wa vx cv cB wcel wph
    wa wo vx cv cA cB cun wcel vx cv cA wcel vx cv cB wcel wo wph vx cv cA cB
    elun anbi1i vx cv cA wcel vx cv cB wcel wph andir bitri exbii wph vx cA
    wrex vx cv cA wcel wph wa vx wex wph vx cB wrex vx cv cB wcel wph wa vx wex
    wph vx cA df-rex wph vx cB df-rex orbi12i 3bitr4i bitri $.

  $( Restricted quantification over a union.  (Contributed by Scott Fenton,
     12-Apr-2011.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
  ralunb $p |- ( A. x e. ( A u. B ) ph <->
                 ( A. x e. A ph /\ A. x e. B ph ) ) $=
    vx cv cA cB cun wcel wph wi vx wal vx cv cA wcel wph wi vx wal vx cv cB
    wcel wph wi vx wal wa wph vx cA cB cun wral wph vx cA wral wph vx cB wral
    wa vx cv cA cB cun wcel wph wi vx wal vx cv cA wcel wph wi vx cv cB wcel
    wph wi wa vx wal vx cv cA wcel wph wi vx wal vx cv cB wcel wph wi vx wal wa
    vx cv cA cB cun wcel wph wi vx cv cA wcel wph wi vx cv cB wcel wph wi wa vx
    vx cv cA cB cun wcel wph wi vx cv cA wcel vx cv cB wcel wo wph wi vx cv cA
    wcel wph wi vx cv cB wcel wph wi wa vx cv cA cB cun wcel vx cv cA wcel vx
    cv cB wcel wo wph vx cv cA cB elun imbi1i vx cv cA wcel wph vx cv cB wcel
    jaob bitri albii vx cv cA wcel wph wi vx cv cB wcel wph wi vx 19.26 bitri
    wph vx cA cB cun df-ral wph vx cA wral vx cv cA wcel wph wi vx wal wph vx
    cB wral vx cv cB wcel wph wi vx wal wph vx cA df-ral wph vx cB df-ral
    anbi12i 3bitr4i $.

  $( Restricted quantification over union.  (Contributed by Jeff Madsen,
     2-Sep-2009.) $)
  ralun $p |- ( ( A. x e. A ph /\ A. x e. B ph ) -> A. x e. ( A u. B ) ph ) $=
    wph vx cA cB cun wral wph vx cA wral wph vx cB wral wa wph vx cA cB ralunb
    biimpri $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Expansion of membership in an intersection of two classes.  Theorem 12
       of [Suppes] p. 25.  (Contributed by NM, 29-Apr-1994.) $)
    elin $p |- ( A e. ( B i^i C ) <-> ( A e. B /\ A e. C ) ) $=
      cA cB cC cin wcel cA cvv wcel cA cB wcel cA cC wcel wa cA cB cC cin elex
      cA cC wcel cA cvv wcel cA cB wcel cA cC elex adantl vx cv cB wcel vx cv
      cC wcel wa cA cB wcel cA cC wcel wa vx cA cB cC cin cvv vx cv cA wceq vx
      cv cB wcel cA cB wcel vx cv cC wcel cA cC wcel vx cv cA cB eleq1 vx cv cA
      cC eleq1 anbi12d vx cB cC df-in elab2g pm5.21nii $.
  $}

  ${
    elin2.x $e |- X = ( B i^i C ) $.
    $( Membership in a class defined as an intersection.  (Contributed by
       Stefan O'Rear, 29-Mar-2015.) $)
    elin2 $p |- ( A e. X <-> ( A e. B /\ A e. C ) ) $=
      cA cX wcel cA cB cC cin wcel cA cB wcel cA cC wcel wa cX cB cC cin cA
      elin2.x eleq2i cA cB cC elin bitri $.
  $}

  ${
    elin3.x $e |- X = ( ( B i^i C ) i^i D ) $.
    $( Membership in a class defined as a ternary intersection.  (Contributed
       by Stefan O'Rear, 29-Mar-2015.) $)
    elin3 $p |- ( A e. X <-> ( A e. B /\ A e. C /\ A e. D ) ) $=
      cA cB cC cin wcel cA cD wcel wa cA cB wcel cA cC wcel wa cA cD wcel wa cA
      cX wcel cA cB wcel cA cC wcel cA cD wcel w3a cA cB cC cin wcel cA cB wcel
      cA cC wcel wa cA cD wcel cA cB cC elin anbi1i cA cB cC cin cD cX elin3.x
      elin2 cA cB wcel cA cC wcel cA cD wcel df-3an 3bitr4i $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Commutative law for intersection of classes.  Exercise 7 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 5-Aug-1993.) $)
    incom $p |- ( A i^i B ) = ( B i^i A ) $=
      vx cA cB cin cB cA cin vx cv cA wcel vx cv cB wcel wa vx cv cB wcel vx cv
      cA wcel wa vx cv cA cB cin wcel vx cv cB cA cin wcel vx cv cA wcel vx cv
      cB wcel ancom vx cv cA cB elin vx cv cB cA elin 3bitr4i eqriv $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    ineqri.1 $e |- ( ( x e. A /\ x e. B ) <-> x e. C ) $.
    $( Inference from membership to intersection.  (Contributed by NM,
       5-Aug-1993.) $)
    ineqri $p |- ( A i^i B ) = C $=
      vx cA cB cin cC vx cv cA cB cin wcel vx cv cA wcel vx cv cB wcel wa vx cv
      cC wcel vx cv cA cB elin ineqri.1 bitri eqriv $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Equality theorem for intersection of two classes.  (Contributed by NM,
       14-Dec-1993.) $)
    ineq1 $p |- ( A = B -> ( A i^i C ) = ( B i^i C ) ) $=
      cA cB wceq vx cA cC cin cB cC cin cA cB wceq vx cv cA wcel vx cv cC wcel
      wa vx cv cB wcel vx cv cC wcel wa vx cv cA cC cin wcel vx cv cB cC cin
      wcel cA cB wceq vx cv cA wcel vx cv cB wcel vx cv cC wcel cA cB vx cv
      eleq2 anbi1d vx cv cA cC elin vx cv cB cC elin 3bitr4g eqrdv $.
  $}

  $( Equality theorem for intersection of two classes.  (Contributed by NM,
     26-Dec-1993.) $)
  ineq2 $p |- ( A = B -> ( C i^i A ) = ( C i^i B ) ) $=
    cA cB wceq cA cC cin cB cC cin cC cA cin cC cB cin cA cB cC ineq1 cC cA
    incom cC cB incom 3eqtr4g $.

  $( Equality theorem for intersection of two classes.  (Contributed by NM,
     8-May-1994.) $)
  ineq12 $p |- ( ( A = B /\ C = D ) -> ( A i^i C ) = ( B i^i D ) ) $=
    cA cB wceq cC cD wceq cA cC cin cB cC cin cB cD cin cA cB cC ineq1 cC cD cB
    ineq2 sylan9eq $.

  ${
    ineq1i.1 $e |- A = B $.
    $( Equality inference for intersection of two classes.  (Contributed by NM,
       26-Dec-1993.) $)
    ineq1i $p |- ( A i^i C ) = ( B i^i C ) $=
      cA cB wceq cA cC cin cB cC cin wceq ineq1i.1 cA cB cC ineq1 ax-mp $.

    $( Equality inference for intersection of two classes.  (Contributed by NM,
       26-Dec-1993.) $)
    ineq2i $p |- ( C i^i A ) = ( C i^i B ) $=
      cA cB wceq cC cA cin cC cB cin wceq ineq1i.1 cA cB cC ineq2 ax-mp $.

    ${
      ineq12i.2 $e |- C = D $.
      $( Equality inference for intersection of two classes.  (Contributed by
         NM, 24-Jun-2004.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)
      ineq12i $p |- ( A i^i C ) = ( B i^i D ) $=
        cA cB wceq cC cD wceq cA cC cin cB cD cin wceq ineq1i.1 ineq12i.2 cA cB
        cC cD ineq12 mp2an $.
    $}
  $}

  ${
    ineq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for intersection of two classes.  (Contributed by NM,
       10-Apr-1994.) $)
    ineq1d $p |- ( ph -> ( A i^i C ) = ( B i^i C ) ) $=
      wph cA cB wceq cA cC cin cB cC cin wceq ineq1d.1 cA cB cC ineq1 syl $.

    $( Equality deduction for intersection of two classes.  (Contributed by NM,
       10-Apr-1994.) $)
    ineq2d $p |- ( ph -> ( C i^i A ) = ( C i^i B ) ) $=
      wph cA cB wceq cC cA cin cC cB cin wceq ineq1d.1 cA cB cC ineq2 syl $.

    ${
      ineq12d.2 $e |- ( ph -> C = D ) $.
      $( Equality deduction for intersection of two classes.  (Contributed by
         NM, 24-Jun-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
      ineq12d $p |- ( ph -> ( A i^i C ) = ( B i^i D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cin cB cD cin wceq ineq1d.1 ineq12d.2
        cA cB cC cD ineq12 syl2anc $.
    $}

    ${
      ineqan12d.2 $e |- ( ps -> C = D ) $.
      $( Equality deduction for intersection of two classes.  (Contributed by
         NM, 7-Feb-2007.) $)
      ineqan12d $p |- ( ( ph /\ ps ) -> ( A i^i C ) = ( B i^i D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cin cB cD cin wceq wps ineq1d.1
        ineqan12d.2 cA cB cC cD ineq12 syl2an $.
    $}
  $}

  $( A frequently-used variant of subclass definition ~ df-ss .  (Contributed
     by NM, 10-Jan-2015.) $)
  dfss1 $p |- ( A C_ B <-> ( B i^i A ) = A ) $=
    cA cB wss cA cB cin cA wceq cB cA cin cA wceq cA cB df-ss cA cB cin cB cA
    cin cA cA cB incom eqeq1i bitri $.

  $( Another definition of subclasshood.  Similar to ~ df-ss , ~ dfss , and
     ~ dfss1 .  (Contributed by David Moews, 1-May-2017.) $)
  dfss5 $p |- ( A C_ B <-> A = ( B i^i A ) ) $=
    cA cB wss cB cA cin cA wceq cA cB cA cin wceq cA cB dfss1 cB cA cin cA
    eqcom bitri $.

  ${
    $d x y $.  $d y A $.  $d y B $.
    nfin.1 $e |- F/_ x A $.
    nfin.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for the intersection of classes.
       (Contributed by NM, 15-Sep-2003.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
    nfin $p |- F/_ x ( A i^i B ) $=
      vx cA cB cin vy cv cB wcel vy cA crab vy cA cB dfin5 vy cv cB wcel vx vy
      cA vx vy cB nfin.2 nfcri nfin.1 nfrab nfcxfr $.
  $}

  ${
    $d A y $.  $d C y z $.  $d D y z $.  $d x y z $.
    $( Distribute proper substitution through an intersection relation.
       (Contributed by Alan Sare, 22-Jul-2012.) $)
    csbing $p |- ( A e. B -> [_ A / x ]_ ( C i^i D ) =
                  ( [_ A / x ]_ C i^i [_ A / x ]_ D ) ) $=
      vx vy cv cC cD cin csb vx vy cv cC csb vx vy cv cD csb cin wceq vx cA cC
      cD cin csb vx cA cC csb vx cA cD csb cin wceq vy cA cB vy cv cA wceq vx
      vy cv cC cD cin csb vx cA cC cD cin csb vx vy cv cC csb vx vy cv cD csb
      cin vx cA cC csb vx cA cD csb cin vx vy cv cA cC cD cin csbeq1 vy cv cA
      wceq vx vy cv cC csb vx cA cC csb vx vy cv cD csb vx cA cD csb vx vy cv
      cA cC csbeq1 vx vy cv cA cD csbeq1 ineq12d eqeq12d vx vy cv cC cD cin vx
      vy cv cC csb vx vy cv cD csb cin vy vex vx vx vy cv cC csb vx vy cv cD
      csb vx vy cv cC nfcsb1v vx vy cv cD nfcsb1v nfin vx cv vy cv wceq cC vx
      vy cv cC csb cD vx vy cv cD csb vx vy cv cC csbeq1a vx vy cv cD csbeq1a
      ineq12d csbief vtoclg $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x B $.
    rabbi2dva.1 $e |- ( ( ph /\ x e. A ) -> ( x e. B <-> ps ) ) $.
    $( Deduction from a wff to a restricted class abstraction.  (Contributed by
       NM, 14-Jan-2014.) $)
    rabbi2dva $p |- ( ph -> ( A i^i B ) = { x e. A | ps } ) $=
      wph cA cB cin vx cv cB wcel vx cA crab wps vx cA crab vx cA cB dfin5 wph
      vx cv cB wcel wps vx cA rabbi2dva.1 rabbidva syl5eq $.
  $}

  ${
    $d x A $.
    $( Idempotent law for intersection of classes.  Theorem 15 of [Suppes]
       p. 26.  (Contributed by NM, 5-Aug-1993.) $)
    inidm $p |- ( A i^i A ) = A $=
      vx cA cA cA vx cv cA wcel anidm ineqri $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( Associative law for intersection of classes.  Exercise 9 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 3-May-1994.) $)
    inass $p |- ( ( A i^i B ) i^i C ) = ( A i^i ( B i^i C ) ) $=
      vx cA cB cin cC cA cB cC cin cin vx cv cA wcel vx cv cB wcel wa vx cv cC
      wcel wa vx cv cA wcel vx cv cB cC cin wcel wa vx cv cA cB cin wcel vx cv
      cC wcel wa vx cv cA cB cC cin cin wcel vx cv cA wcel vx cv cB wcel wa vx
      cv cC wcel wa vx cv cA wcel vx cv cB wcel vx cv cC wcel wa wa vx cv cA
      wcel vx cv cB cC cin wcel wa vx cv cA wcel vx cv cB wcel vx cv cC wcel
      anass vx cv cB cC cin wcel vx cv cB wcel vx cv cC wcel wa vx cv cA wcel
      vx cv cB cC elin anbi2i bitr4i vx cv cA cB cin wcel vx cv cA wcel vx cv
      cB wcel wa vx cv cC wcel vx cv cA cB elin anbi1i vx cv cA cB cC cin elin
      3bitr4i ineqri $.
  $}

  $( A rearrangement of intersection.  (Contributed by NM, 21-Apr-2001.) $)
  in12 $p |- ( A i^i ( B i^i C ) ) = ( B i^i ( A i^i C ) ) $=
    cA cB cin cC cin cB cA cin cC cin cA cB cC cin cin cB cA cC cin cin cA cB
    cin cB cA cin cC cA cB incom ineq1i cA cB cC inass cB cA cC inass 3eqtr3i
    $.

  $( A rearrangement of intersection.  (Contributed by NM, 21-Apr-2001.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  in32 $p |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i B ) $=
    cA cB cin cC cin cA cB cC cin cin cB cA cC cin cin cA cC cin cB cin cA cB
    cC inass cA cB cC in12 cB cA cC cin incom 3eqtri $.

  $( A rearrangement of intersection.  (Contributed by NM, 27-Aug-2012.) $)
  in13 $p |- ( A i^i ( B i^i C ) ) = ( C i^i ( B i^i A ) ) $=
    cB cC cin cA cin cB cA cin cC cin cA cB cC cin cin cC cB cA cin cin cB cC
    cA in32 cA cB cC cin incom cC cB cA cin incom 3eqtr4i $.

  $( A rearrangement of intersection.  (Contributed by NM, 27-Aug-2012.) $)
  in31 $p |- ( ( A i^i B ) i^i C ) = ( ( C i^i B ) i^i A ) $=
    cC cA cB cin cin cA cC cB cin cin cA cB cin cC cin cC cB cin cA cin cC cA
    cB in12 cA cB cin cC incom cC cB cin cA incom 3eqtr4i $.

  $( Rotate the intersection of 3 classes.  (Contributed by NM,
     27-Aug-2012.) $)
  inrot $p |- ( ( A i^i B ) i^i C ) = ( ( C i^i A ) i^i B ) $=
    cA cB cin cC cin cC cB cin cA cin cC cA cin cB cin cA cB cC in31 cC cB cA
    in32 eqtri $.

  $( Rearrangement of intersection of 4 classes.  (Contributed by NM,
     21-Apr-2001.) $)
  in4 $p |- ( ( A i^i B ) i^i ( C i^i D ) ) =
            ( ( A i^i C ) i^i ( B i^i D ) ) $=
    cA cB cC cD cin cin cin cA cC cB cD cin cin cin cA cB cin cC cD cin cin cA
    cC cin cB cD cin cin cB cC cD cin cin cC cB cD cin cin cA cB cC cD in12
    ineq2i cA cB cC cD cin inass cA cC cB cD cin inass 3eqtr4i $.

  $( Intersection distributes over itself.  (Contributed by NM, 6-May-1994.) $)
  inindi $p |- ( A i^i ( B i^i C ) ) = ( ( A i^i B ) i^i ( A i^i C ) ) $=
    cA cA cin cB cC cin cin cA cB cC cin cin cA cB cin cA cC cin cin cA cA cin
    cA cB cC cin cA inidm ineq1i cA cA cB cC in4 eqtr3i $.

  $( Intersection distributes over itself.  (Contributed by NM,
     17-Aug-2004.) $)
  inindir $p |- ( ( A i^i B ) i^i C ) = ( ( A i^i C ) i^i ( B i^i C ) ) $=
    cA cB cin cC cC cin cin cA cB cin cC cin cA cC cin cB cC cin cin cC cC cin
    cC cA cB cin cC inidm ineq2i cA cB cC cC in4 eqtr3i $.

  $( A relationship between subclass and intersection.  Similar to Exercise 9
     of [TakeutiZaring] p. 18.  (Contributed by NM, 17-May-1994.) $)
  sseqin2 $p |- ( A C_ B <-> ( B i^i A ) = A ) $=
    cA cB dfss1 $.

  ${
    $d x A $.  $d x B $.
    $( The intersection of two classes is a subset of one of them.  Part of
       Exercise 12 of [TakeutiZaring] p. 18.  (Contributed by NM,
       27-Apr-1994.) $)
    inss1 $p |- ( A i^i B ) C_ A $=
      vx cA cB cin cA vx cv cA cB cin wcel vx cv cA wcel vx cv cB wcel vx cv cA
      cB elin simplbi ssriv $.
  $}

  $( The intersection of two classes is a subset of one of them.  Part of
     Exercise 12 of [TakeutiZaring] p. 18.  (Contributed by NM,
     27-Apr-1994.) $)
  inss2 $p |- ( A i^i B ) C_ B $=
    cA cB cin cB cA cin cB cB cA incom cB cA inss1 eqsstr3i $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Subclass of intersection.  Theorem 2.8(vii) of [Monk1] p. 26.
       (Contributed by NM, 15-Jun-2004.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    ssin $p |- ( ( A C_ B /\ A C_ C ) <-> A C_ ( B i^i C ) ) $=
      vx cv cA wcel vx cv cB wcel wi vx wal vx cv cA wcel vx cv cC wcel wi vx
      wal wa vx cv cA wcel vx cv cB cC cin wcel wi vx wal cA cB wss cA cC wss
      wa cA cB cC cin wss vx cv cA wcel vx cv cB cC cin wcel wi vx wal vx cv cA
      wcel vx cv cB wcel vx cv cC wcel wa wi vx wal vx cv cA wcel vx cv cB wcel
      wi vx cv cA wcel vx cv cC wcel wi wa vx wal vx cv cA wcel vx cv cB wcel
      wi vx wal vx cv cA wcel vx cv cC wcel wi vx wal wa vx cv cA wcel vx cv cB
      cC cin wcel wi vx cv cA wcel vx cv cB wcel vx cv cC wcel wa wi vx vx cv
      cB cC cin wcel vx cv cB wcel vx cv cC wcel wa vx cv cA wcel vx cv cB cC
      elin imbi2i albii vx cv cA wcel vx cv cB wcel vx cv cC wcel wa wi vx cv
      cA wcel vx cv cB wcel wi vx cv cA wcel vx cv cC wcel wi wa vx vx cv cA
      wcel vx cv cB wcel vx cv cC wcel jcab albii vx cv cA wcel vx cv cB wcel
      wi vx cv cA wcel vx cv cC wcel wi vx 19.26 3bitrri cA cB wss vx cv cA
      wcel vx cv cB wcel wi vx wal cA cC wss vx cv cA wcel vx cv cC wcel wi vx
      wal vx cA cB dfss2 vx cA cC dfss2 anbi12i vx cA cB cC cin dfss2 3bitr4i
      $.
  $}

  ${
    ssini.1 $e |- A C_ B $.
    ssini.2 $e |- A C_ C $.
    $( An inference showing that a subclass of two classes is a subclass of
       their intersection.  (Contributed by NM, 24-Nov-2003.) $)
    ssini $p |- A C_ ( B i^i C ) $=
      cA cB wss cA cC wss wa cA cB cC cin wss cA cB wss cA cC wss ssini.1
      ssini.2 pm3.2i cA cB cC ssin mpbi $.
  $}

  ${
    ssind.1 $e |- ( ph -> A C_ B ) $.
    ssind.2 $e |- ( ph -> A C_ C ) $.
    $( A deduction showing that a subclass of two classes is a subclass of
       their intersection.  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    ssind $p |- ( ph -> A C_ ( B i^i C ) ) $=
      wph cA cB wss cA cC wss cA cB cC cin wss ssind.1 ssind.2 cA cB wss cA cC
      wss wa cA cB cC cin wss cA cB cC ssin biimpi syl2anc $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Add right intersection to subclass relation.  (Contributed by NM,
       16-Aug-1994.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    ssrin $p |- ( A C_ B -> ( A i^i C ) C_ ( B i^i C ) ) $=
      cA cB wss vx cA cC cin cB cC cin cA cB wss vx cv cA wcel vx cv cC wcel wa
      vx cv cB wcel vx cv cC wcel wa vx cv cA cC cin wcel vx cv cB cC cin wcel
      cA cB wss vx cv cA wcel vx cv cB wcel vx cv cC wcel cA cB vx cv ssel
      anim1d vx cv cA cC elin vx cv cB cC elin 3imtr4g ssrdv $.

    $( Add left intersection to subclass relation.  (Contributed by NM,
       19-Oct-1999.) $)
    sslin $p |- ( A C_ B -> ( C i^i A ) C_ ( C i^i B ) ) $=
      cA cB wss cA cC cin cB cC cin cC cA cin cC cB cin cA cB cC ssrin cC cA
      incom cC cB incom 3sstr4g $.
  $}

  $( Intersection of subclasses.  (Contributed by NM, 5-May-2000.) $)
  ss2in $p |- ( ( A C_ B /\ C C_ D ) -> ( A i^i C ) C_ ( B i^i D ) ) $=
    cA cB wss cC cD wss cA cC cin cB cC cin cB cD cin cA cB cC ssrin cC cD cB
    sslin sylan9ss $.

  $( Intersection preserves subclass relationship.  (Contributed by NM,
     14-Sep-1999.) $)
  ssinss1 $p |- ( A C_ C -> ( A i^i B ) C_ C ) $=
    cA cB cin cA wss cA cC wss cA cB cin cC wss wi cA cB inss1 cA cB cin cA cC
    sstr2 ax-mp $.

  $( Inclusion of an intersection of two classes.  (Contributed by NM,
     30-Oct-2014.) $)
  inss $p |- ( ( A C_ C \/ B C_ C ) -> ( A i^i B ) C_ C ) $=
    cA cC wss cA cB cin cC wss cB cC wss cA cB cC ssinss1 cB cC wss cA cB cin
    cB cA cin cC cA cB incom cB cA cC ssinss1 syl5eqss jaoi $.

  $( Absorption law for union.  (Contributed by NM, 16-Apr-2006.) $)
  unabs $p |- ( A u. ( A i^i B ) ) = A $=
    cA cB cin cA wss cA cA cB cin cun cA wceq cA cB inss1 cA cB cin cA ssequn2
    mpbi $.

  $( Absorption law for intersection.  (Contributed by NM, 16-Apr-2006.) $)
  inabs $p |- ( A i^i ( A u. B ) ) = A $=
    cA cA cB cun wss cA cA cB cun cin cA wceq cA cB ssun1 cA cA cB cun df-ss
    mpbi $.

  $( Negation of subclass expressed in terms of intersection and proper
     subclass.  (Contributed by NM, 30-Jun-2004.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
  nssinpss $p |- ( -. A C_ B <-> ( A i^i B ) C. A ) $=
    cA cB cin cA wne cA cB cin cA wss cA cB cin cA wne wa cA cB wss wn cA cB
    cin cA wpss cA cB cin cA wss cA cB cin cA wne cA cB inss1 biantrur cA cB
    wss cA cB cin cA cA cB df-ss necon3bbii cA cB cin cA df-pss 3bitr4i $.

  $( Negation of subclass expressed in terms of proper subclass and union.
     (Contributed by NM, 15-Sep-2004.) $)
  nsspssun $p |- ( -. A C_ B <-> B C. ( A u. B ) ) $=
    cA cB wss wn cB cA cB cun wss cA cB cun cB wss wn wa cB cA cB cun wpss cA
    cB cun cB wss cB cA cB cun wss cA cB cun cB wss wn wa cA cB wss cB cA cB
    cun wss cA cB cun cB wss wn cB cA ssun2 biantrur cA cB wss cA cB wss cB cB
    wss wa cA cB cun cB wss cB cB wss cA cB wss cB ssid biantru cA cB cB unss
    bitri xchnxbir cB cA cB cun dfpss3 bitr4i $.

  ${
    $d x A $.  $d x B $.
    $( Subclass defined in terms of class difference.  See comments under
       ~ dfun2 .  (Contributed by NM, 22-Mar-1998.)  (Proof shortened by Andrew
       Salmon, 26-Jun-2011.) $)
    dfss4 $p |- ( A C_ B <-> ( B \ ( B \ A ) ) = A ) $=
      cA cB wss cB cA cin cA wceq cB cB cA cdif cdif cA wceq cA cB sseqin2 cB
      cB cA cdif cdif cB cA cin cA vx cB cB cA cdif cB cA cin vx cv cB wcel vx
      cv cB cA cdif wcel wn wa vx cv cB wcel vx cv cB wcel vx cv cA wcel wn wa
      wn wa vx cv cB cA cin wcel vx cv cB cA cdif wcel wn vx cv cB wcel vx cv
      cA wcel wn wa wn vx cv cB wcel vx cv cB cA cdif wcel vx cv cB wcel vx cv
      cA wcel wn wa vx cv cB cA eldif notbii anbi2i vx cv cB cA cin wcel vx cv
      cB wcel vx cv cA wcel wa vx cv cB wcel vx cv cB wcel vx cv cA wcel wi wa
      vx cv cB wcel vx cv cB wcel vx cv cA wcel wn wa wn wa vx cv cB cA elin vx
      cv cB wcel vx cv cA wcel abai vx cv cB wcel vx cv cA wcel wi vx cv cB
      wcel vx cv cA wcel wn wa wn vx cv cB wcel vx cv cB wcel vx cv cA wcel
      iman anbi2i 3bitri bitr4i difeqri eqeq1i bitr4i $.

    $( An alternate definition of the union of two classes in terms of class
       difference, requiring no dummy variables.  Along with ~ dfin2 and
       ~ dfss4 it shows we can express union, intersection, and subset directly
       in terms of the single "primitive" operation ` \ ` (class difference).
       (Contributed by NM, 10-Jun-2004.) $)
    dfun2 $p |- ( A u. B ) = ( _V \ ( ( _V \ A ) \ B ) ) $=
      vx cA cB cvv cvv cA cdif cB cdif cdif vx cv cA wcel vx cv cB wcel wo vx
      cv cvv cA cdif cB cdif wcel wn vx cv cvv cvv cA cdif cB cdif cdif wcel vx
      cv cvv cA cdif cB cdif wcel vx cv cA wcel vx cv cB wcel wo vx cv cvv cA
      cdif wcel vx cv cB wcel wn wa vx cv cA wcel wn vx cv cB wcel wn wa vx cv
      cvv cA cdif cB cdif wcel vx cv cA wcel vx cv cB wcel wo wn vx cv cvv cA
      cdif wcel vx cv cA wcel wn vx cv cB wcel wn vx cv cvv cA cdif wcel vx cv
      cvv wcel vx cv cA wcel wn vx vex vx cv cvv cA eldif mpbiran anbi1i vx cv
      cvv cA cdif cB eldif vx cv cA wcel vx cv cB wcel ioran 3bitr4i con2bii vx
      cv cvv cvv cA cdif cB cdif cdif wcel vx cv cvv wcel vx cv cvv cA cdif cB
      cdif wcel wn vx vex vx cv cvv cvv cA cdif cB cdif eldif mpbiran bitr4i
      uneqri $.

    $( An alternate definition of the intersection of two classes in terms of
       class difference, requiring no dummy variables.  See comments under
       ~ dfun2 .  Another version is given by ~ dfin4 .  (Contributed by NM,
       10-Jun-2004.) $)
    dfin2 $p |- ( A i^i B ) = ( A \ ( _V \ B ) ) $=
      vx cA cB cA cvv cB cdif cdif vx cv cA wcel vx cv cB wcel wa vx cv cA wcel
      vx cv cvv cB cdif wcel wn wa vx cv cA cvv cB cdif cdif wcel vx cv cB wcel
      vx cv cvv cB cdif wcel wn vx cv cA wcel vx cv cvv cB cdif wcel vx cv cB
      wcel vx cv cvv cB cdif wcel vx cv cvv wcel vx cv cB wcel wn vx vex vx cv
      cvv cB eldif mpbiran con2bii anbi2i vx cv cA cvv cB cdif eldif bitr4i
      ineqri $.

    $( Difference with intersection.  Theorem 33 of [Suppes] p. 29.
       (Contributed by NM, 31-Mar-1998.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    difin $p |- ( A \ ( A i^i B ) ) = ( A \ B ) $=
      vx cA cA cB cin cA cB cdif vx cv cA wcel vx cv cB wcel wi wn vx cv cA
      wcel vx cv cB wcel wn wa vx cv cA wcel vx cv cA cB cin wcel wn wa vx cv
      cA cB cdif wcel vx cv cA wcel vx cv cB wcel pm4.61 vx cv cA wcel vx cv cB
      wcel wi vx cv cA wcel vx cv cA cB cin wcel wn wa vx cv cA wcel vx cv cB
      wcel wi vx cv cA wcel vx cv cA wcel vx cv cB wcel wa wi vx cv cA wcel vx
      cv cA cB cin wcel wi vx cv cA wcel vx cv cA cB cin wcel wn wa wn vx cv cA
      wcel vx cv cB wcel anclb vx cv cA cB cin wcel vx cv cA wcel vx cv cB wcel
      wa vx cv cA wcel vx cv cA cB elin imbi2i vx cv cA wcel vx cv cA cB cin
      wcel iman 3bitr2i con2bii vx cv cA cB eldif 3bitr4i difeqri $.
  $}

  $( Union defined in terms of intersection (De Morgan's law).  Definition of
     union in [Mendelson] p. 231.  (Contributed by NM, 8-Jan-2002.) $)
  dfun3 $p |- ( A u. B ) = ( _V \ ( ( _V \ A ) i^i ( _V \ B ) ) ) $=
    cA cB cun cvv cvv cA cdif cB cdif cdif cvv cvv cA cdif cvv cB cdif cin cdif
    cA cB dfun2 cvv cA cdif cB cdif cvv cA cdif cvv cB cdif cin cvv cvv cA cdif
    cvv cB cdif cin cvv cA cdif cvv cvv cB cdif cdif cdif cvv cA cdif cB cdif
    cvv cA cdif cvv cB cdif dfin2 cvv cvv cB cdif cdif cB cvv cA cdif cB ddif
    difeq2i eqtr2i difeq2i eqtri $.

  $( Intersection defined in terms of union (De Morgan's law.  Similar to
     Exercise 4.10(n) of [Mendelson] p. 231.  (Contributed by NM,
     8-Jan-2002.) $)
  dfin3 $p |- ( A i^i B ) = ( _V \ ( ( _V \ A ) u. ( _V \ B ) ) ) $=
    cvv cvv cA cvv cB cdif cdif cdif cdif cA cvv cB cdif cdif cvv cvv cA cdif
    cvv cB cdif cun cdif cA cB cin cA cvv cB cdif cdif ddif cvv cA cdif cvv cB
    cdif cun cvv cA cvv cB cdif cdif cdif cvv cvv cA cdif cvv cB cdif cun cvv
    cvv cvv cA cdif cdif cvv cB cdif cdif cdif cvv cA cvv cB cdif cdif cdif cvv
    cA cdif cvv cB cdif dfun2 cvv cvv cA cdif cdif cvv cB cdif cdif cA cvv cB
    cdif cdif cvv cvv cvv cA cdif cdif cA cvv cB cdif cA ddif difeq1i difeq2i
    eqtri difeq2i cA cB dfin2 3eqtr4ri $.

  $( Alternate definition of the intersection of two classes.  Exercise 4.10(q)
     of [Mendelson] p. 231.  (Contributed by NM, 25-Nov-2003.) $)
  dfin4 $p |- ( A i^i B ) = ( A \ ( A \ B ) ) $=
    cA cA cA cB cin cdif cdif cA cB cin cA cA cB cdif cdif cA cB cin cA wss cA
    cA cA cB cin cdif cdif cA cB cin wceq cA cB inss1 cA cB cin cA dfss4 mpbi
    cA cA cB cin cdif cA cB cdif cA cA cB difin difeq2i eqtr3i $.

  $( Intersection with universal complement.  Remark in [Stoll] p. 20.
     (Contributed by NM, 17-Aug-2004.) $)
  invdif $p |- ( A i^i ( _V \ B ) ) = ( A \ B ) $=
    cA cvv cB cdif cin cA cvv cvv cB cdif cdif cdif cA cB cdif cA cvv cB cdif
    dfin2 cvv cvv cB cdif cdif cB cA cB ddif difeq2i eqtri $.

  $( Intersection with class difference.  Theorem 34 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)
  indif $p |- ( A i^i ( A \ B ) ) = ( A \ B ) $=
    cA cA cB cdif cin cA cA cA cB cdif cdif cdif cA cA cB cin cdif cA cB cdif
    cA cA cB cdif dfin4 cA cB cin cA cA cB cdif cdif cA cA cB dfin4 difeq2i cA
    cB difin 3eqtr2i $.

  $( Bring an intersection in and out of a class difference.  (Contributed by
     Jeff Hankins, 15-Jul-2009.) $)
  indif2 $p |- ( A i^i ( B \ C ) ) = ( ( A i^i B ) \ C ) $=
    cA cB cin cvv cC cdif cin cA cB cvv cC cdif cin cin cA cB cin cC cdif cA cB
    cC cdif cin cA cB cvv cC cdif inass cA cB cin cC invdif cB cvv cC cdif cin
    cB cC cdif cA cB cC invdif ineq2i 3eqtr3ri $.

  $( Bring an intersection in and out of a class difference.  (Contributed by
     Mario Carneiro, 15-May-2015.) $)
  indif1 $p |- ( ( A \ C ) i^i B ) = ( ( A i^i B ) \ C ) $=
    cB cA cC cdif cin cB cA cin cC cdif cA cC cdif cB cin cA cB cin cC cdif cB
    cA cC indif2 cB cA cC cdif incom cB cA cin cA cB cin cC cB cA incom difeq1i
    3eqtr3i $.

  $( Commutation law for intersection and difference.  (Contributed by Scott
     Fenton, 18-Feb-2013.) $)
  indifcom $p |- ( A i^i ( B \ C ) ) = ( B i^i ( A \ C ) ) $=
    cA cB cin cC cdif cB cA cin cC cdif cA cB cC cdif cin cB cA cC cdif cin cA
    cB cin cB cA cin cC cA cB incom difeq1i cA cB cC indif2 cB cA cC indif2
    3eqtr4i $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Distributive law for intersection over union.  Exercise 10 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 30-Sep-2002.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)
    indi $p |- ( A i^i ( B u. C ) ) = ( ( A i^i B ) u. ( A i^i C ) ) $=
      vx cA cB cC cun cA cB cin cA cC cin cun vx cv cA wcel vx cv cB wcel vx cv
      cC wcel wo wa vx cv cA cB cin wcel vx cv cA cC cin wcel wo vx cv cA wcel
      vx cv cB cC cun wcel wa vx cv cA cB cin cA cC cin cun wcel vx cv cA wcel
      vx cv cB wcel vx cv cC wcel wo wa vx cv cA wcel vx cv cB wcel wa vx cv cA
      wcel vx cv cC wcel wa wo vx cv cA cB cin wcel vx cv cA cC cin wcel wo vx
      cv cA wcel vx cv cB wcel vx cv cC wcel andi vx cv cA cB cin wcel vx cv cA
      wcel vx cv cB wcel wa vx cv cA cC cin wcel vx cv cA wcel vx cv cC wcel wa
      vx cv cA cB elin vx cv cA cC elin orbi12i bitr4i vx cv cB cC cun wcel vx
      cv cB wcel vx cv cC wcel wo vx cv cA wcel vx cv cB cC elun anbi2i vx cv
      cA cB cin cA cC cin elun 3bitr4i ineqri $.

    $( Distributive law for union over intersection.  Exercise 11 of
       [TakeutiZaring] p. 17.  (Contributed by NM, 30-Sep-2002.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)
    undi $p |- ( A u. ( B i^i C ) ) = ( ( A u. B ) i^i ( A u. C ) ) $=
      vx cA cB cC cin cA cB cun cA cC cun cin vx cv cA wcel vx cv cB cC cin
      wcel wo vx cv cA wcel vx cv cB wcel vx cv cC wcel wa wo vx cv cA wcel vx
      cv cB wcel wo vx cv cA wcel vx cv cC wcel wo wa vx cv cA cB cun cA cC cun
      cin wcel vx cv cB cC cin wcel vx cv cB wcel vx cv cC wcel wa vx cv cA
      wcel vx cv cB cC elin orbi2i vx cv cA wcel vx cv cB wcel vx cv cC wcel
      ordi vx cv cA cB cun cA cC cun cin wcel vx cv cA cB cun wcel vx cv cA cC
      cun wcel wa vx cv cA wcel vx cv cB wcel wo vx cv cA wcel vx cv cC wcel wo
      wa vx cv cA cB cun cA cC cun elin vx cv cA cB cun wcel vx cv cA wcel vx
      cv cB wcel wo vx cv cA cC cun wcel vx cv cA wcel vx cv cC wcel wo vx cv
      cA cB elun vx cv cA cC elun anbi12i bitr2i 3bitri uneqri $.
  $}

  $( Distributive law for intersection over union.  Theorem 28 of [Suppes]
     p. 27.  (Contributed by NM, 30-Sep-2002.) $)
  indir $p |- ( ( A u. B ) i^i C ) = ( ( A i^i C ) u. ( B i^i C ) ) $=
    cC cA cB cun cin cC cA cin cC cB cin cun cA cB cun cC cin cA cC cin cB cC
    cin cun cC cA cB indi cA cB cun cC incom cA cC cin cC cA cin cB cC cin cC
    cB cin cA cC incom cB cC incom uneq12i 3eqtr4i $.

  $( Distributive law for union over intersection.  Theorem 29 of [Suppes]
     p. 27.  (Contributed by NM, 30-Sep-2002.) $)
  undir $p |- ( ( A i^i B ) u. C ) = ( ( A u. C ) i^i ( B u. C ) ) $=
    cC cA cB cin cun cC cA cun cC cB cun cin cA cB cin cC cun cA cC cun cB cC
    cun cin cC cA cB undi cA cB cin cC uncom cA cC cun cC cA cun cB cC cun cC
    cB cun cA cC uncom cB cC uncom ineq12i 3eqtr4i $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Infer equality from equalities of union and intersection.  Exercise 20
       of [Enderton] p. 32 and its converse.  (Contributed by NM,
       10-Aug-2004.) $)
    unineq $p |- ( ( ( A u. C ) = ( B u. C ) /\ ( A i^i C ) = ( B i^i C ) )
                 <-> A = B ) $=
      cA cC cun cB cC cun wceq cA cC cin cB cC cin wceq wa cA cB wceq cA cC cun
      cB cC cun wceq cA cC cin cB cC cin wceq wa vx cA cB vx cv cC wcel cA cC
      cun cB cC cun wceq cA cC cin cB cC cin wceq wa vx cv cA wcel vx cv cB
      wcel wb wi vx cv cC wcel cA cC cin cB cC cin wceq vx cv cA wcel vx cv cB
      wcel wb cA cC cun cB cC cun wceq cA cC cin cB cC cin wceq vx cv cA wcel
      vx cv cB wcel wb vx cv cC wcel vx cv cA wcel vx cv cC wcel wa vx cv cB
      wcel vx cv cC wcel wa wb cA cC cin cB cC cin wceq vx cv cA cC cin wcel vx
      cv cB cC cin wcel vx cv cA wcel vx cv cC wcel wa vx cv cB wcel vx cv cC
      wcel wa cA cC cin cB cC cin vx cv eleq2 vx cv cA cC elin vx cv cB cC elin
      3bitr3g vx cv cC wcel vx cv cA wcel vx cv cA wcel vx cv cC wcel wa vx cv
      cB wcel vx cv cB wcel vx cv cC wcel wa vx cv cC wcel vx cv cA wcel iba vx
      cv cC wcel vx cv cB wcel iba bibi12d syl5ibr adantld vx cv cC wcel wn cA
      cC cun cB cC cun wceq vx cv cA wcel vx cv cB wcel wb cA cC cin cB cC cin
      wceq cA cC cun cB cC cun wceq vx cv cA wcel vx cv cB wcel wb vx cv cC
      wcel wn vx cv cC wcel vx cv cA wcel wo vx cv cC wcel vx cv cB wcel wo wb
      cA cC cun cB cC cun wceq vx cv cC cA cun wcel vx cv cC cB cun wcel vx cv
      cC wcel vx cv cA wcel wo vx cv cC wcel vx cv cB wcel wo cA cC cun cB cC
      cun wceq cC cA cun cC cB cun wceq vx cv cC cA cun wcel vx cv cC cB cun
      wcel wb cA cC cun cC cA cun cB cC cun cC cB cun cA cC uncom cB cC uncom
      eqeq12i cC cA cun cC cB cun vx cv eleq2 sylbi vx cv cC cA elun vx cv cC
      cB elun 3bitr3g vx cv cC wcel wn vx cv cA wcel vx cv cC wcel vx cv cA
      wcel wo vx cv cB wcel vx cv cC wcel vx cv cB wcel wo vx cv cC wcel vx cv
      cA wcel biorf vx cv cC wcel vx cv cB wcel biorf bibi12d syl5ibr adantrd
      pm2.61i eqrdv cA cB wceq cA cC cun cB cC cun wceq cA cC cin cB cC cin
      wceq cA cB cC uneq1 cA cB cC ineq1 jca impbii $.
  $}

  $( Equality of union and intersection implies equality of their arguments.
     (Contributed by NM, 16-Apr-2006.)  (Proof shortened by Andrew Salmon,
     26-Jun-2011.) $)
  uneqin $p |- ( ( A u. B ) = ( A i^i B ) <-> A = B ) $=
    cA cB cun cA cB cin wceq cA cB wceq cA cB cun cA cB cin wceq cA cB wss cB
    cA wss wa cA cB wceq cA cB cun cA cB cin wceq cA cB cun cA cB cin wss cA cB
    wss cB cA wss wa cA cB cun cA cB cin eqimss cA cB cun cA cB cin wss cA cA
    cB cin wss cB cA cB cin wss wa cA cB wss cB cA wss wa cA cB cA cB cin unss
    cA cA cB cin wss cA cB wss cB cA cB cin wss cB cA wss cA cA cB cin wss cA
    cA wss cA cB wss wa cA cB wss cA cA cB ssin cA cA cB sstr sylbir cB cA cB
    cin wss cB cA wss cB cB wss wa cB cA wss cB cA cB ssin cB cA wss cB cB wss
    simpl sylbir anim12i sylbir syl cA cB eqss sylibr cA cB wceq cA cA cun cA
    cA cin cA cB cun cA cB cin cA cA cun cA cA cA cin cA unidm cA inidm eqtr4i
    cA cB cA uneq2 cA cB cA ineq2 3eqtr3a impbii $.

  $( Distributive law for class difference.  Theorem 39 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)
  difundi $p |- ( A \ ( B u. C ) ) = ( ( A \ B ) i^i ( A \ C ) ) $=
    cA cB cC cun cdif cA cvv cvv cB cdif cvv cC cdif cin cdif cdif cA cB cdif
    cA cC cdif cin cB cC cun cvv cvv cB cdif cvv cC cdif cin cdif cA cB cC
    dfun3 difeq2i cA cvv cB cdif cvv cC cdif cin cin cA cvv cB cdif cin cA cvv
    cC cdif cin cin cA cvv cvv cB cdif cvv cC cdif cin cdif cdif cA cB cdif cA
    cC cdif cin cA cvv cB cdif cvv cC cdif inindi cA cvv cB cdif cvv cC cdif
    cin dfin2 cA cvv cB cdif cin cA cB cdif cA cvv cC cdif cin cA cC cdif cA cB
    invdif cA cC invdif ineq12i 3eqtr3i eqtri $.

  $( Distributive law for class difference.  (Contributed by NM,
     17-Aug-2004.) $)
  difundir $p |- ( ( A u. B ) \ C ) = ( ( A \ C ) u. ( B \ C ) ) $=
    cA cB cun cvv cC cdif cin cA cvv cC cdif cin cB cvv cC cdif cin cun cA cB
    cun cC cdif cA cC cdif cB cC cdif cun cA cB cvv cC cdif indir cA cB cun cC
    invdif cA cvv cC cdif cin cA cC cdif cB cvv cC cdif cin cB cC cdif cA cC
    invdif cB cC invdif uneq12i 3eqtr3i $.

  $( Distributive law for class difference.  Theorem 40 of [Suppes] p. 29.
     (Contributed by NM, 17-Aug-2004.) $)
  difindi $p |- ( A \ ( B i^i C ) ) = ( ( A \ B ) u. ( A \ C ) ) $=
    cA cB cC cin cdif cA cvv cvv cB cdif cvv cC cdif cun cdif cdif cA cB cdif
    cA cC cdif cun cB cC cin cvv cvv cB cdif cvv cC cdif cun cdif cA cB cC
    dfin3 difeq2i cA cvv cB cdif cvv cC cdif cun cin cA cvv cB cdif cin cA cvv
    cC cdif cin cun cA cvv cvv cB cdif cvv cC cdif cun cdif cdif cA cB cdif cA
    cC cdif cun cA cvv cB cdif cvv cC cdif indi cA cvv cB cdif cvv cC cdif cun
    dfin2 cA cvv cB cdif cin cA cB cdif cA cvv cC cdif cin cA cC cdif cA cB
    invdif cA cC invdif uneq12i 3eqtr3i eqtri $.

  $( Distributive law for class difference.  (Contributed by NM,
     17-Aug-2004.) $)
  difindir $p |- ( ( A i^i B ) \ C ) = ( ( A \ C ) i^i ( B \ C ) ) $=
    cA cB cin cvv cC cdif cin cA cvv cC cdif cin cB cvv cC cdif cin cin cA cB
    cin cC cdif cA cC cdif cB cC cdif cin cA cB cvv cC cdif inindir cA cB cin
    cC invdif cA cvv cC cdif cin cA cC cdif cB cvv cC cdif cin cB cC cdif cA cC
    invdif cB cC invdif ineq12i 3eqtr3i $.

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( Distribute intersection over difference.  (Contributed by Scott Fenton,
       14-Apr-2011.) $)
    indifdir $p |- ( ( A \ B ) i^i C ) = ( ( A i^i C ) \ ( B i^i C ) ) $=
      vx cA cB cdif cC cin cA cC cin cB cC cin cdif vx cv cA wcel vx cv cB wcel
      wn wa vx cv cC wcel wa vx cv cA wcel vx cv cC wcel wa vx cv cB wcel vx cv
      cC wcel wa wn wa vx cv cA cB cdif cC cin wcel vx cv cA cC cin cB cC cin
      cdif wcel vx cv cA wcel vx cv cB wcel wn wa vx cv cC wcel wa vx cv cA
      wcel vx cv cC wcel wa vx cv cB wcel wn vx cv cC wcel wn wo wa vx cv cA
      wcel vx cv cC wcel wa vx cv cB wcel vx cv cC wcel wa wn wa vx cv cA wcel
      vx cv cC wcel wa vx cv cB wcel wn wa vx cv cA wcel vx cv cC wcel wa vx cv
      cB wcel wn wa vx cv cA wcel vx cv cC wcel wa vx cv cC wcel wn wa wo vx cv
      cA wcel vx cv cB wcel wn wa vx cv cC wcel wa vx cv cA wcel vx cv cC wcel
      wa vx cv cB wcel wn vx cv cC wcel wn wo wa vx cv cA wcel vx cv cC wcel wa
      vx cv cC wcel wn wa vx cv cA wcel vx cv cC wcel wa vx cv cB wcel wn wa vx
      cv cA wcel vx cv cC wcel wa vx cv cC wcel wn wa vx cv cA wcel vx cv cC
      wcel vx cv cC wcel wn wa wa vx cv cC wcel vx cv cC wcel wn wa vx cv cA
      wcel vx cv cC wcel pm3.24 intnan vx cv cA wcel vx cv cC wcel vx cv cC
      wcel wn anass mtbir biorfi vx cv cA wcel vx cv cB wcel wn vx cv cC wcel
      an32 vx cv cA wcel vx cv cC wcel wa vx cv cB wcel wn vx cv cC wcel wn
      andi 3bitr4i vx cv cB wcel vx cv cC wcel wa wn vx cv cB wcel wn vx cv cC
      wcel wn wo vx cv cA wcel vx cv cC wcel wa vx cv cB wcel vx cv cC wcel
      ianor anbi2i bitr4i vx cv cA cB cdif cC cin wcel vx cv cA cB cdif wcel vx
      cv cC wcel wa vx cv cA wcel vx cv cB wcel wn wa vx cv cC wcel wa vx cv cA
      cB cdif cC elin vx cv cA cB cdif wcel vx cv cA wcel vx cv cB wcel wn wa
      vx cv cC wcel vx cv cA cB eldif anbi1i bitri vx cv cA cC cin cB cC cin
      cdif wcel vx cv cA cC cin wcel vx cv cB cC cin wcel wn wa vx cv cA wcel
      vx cv cC wcel wa vx cv cB wcel vx cv cC wcel wa wn wa vx cv cA cC cin cB
      cC cin eldif vx cv cA cC cin wcel vx cv cA wcel vx cv cC wcel wa vx cv cB
      cC cin wcel wn vx cv cB wcel vx cv cC wcel wa wn vx cv cA cC elin vx cv
      cB cC cin wcel vx cv cB wcel vx cv cC wcel wa vx cv cB cC elin notbii
      anbi12i bitri 3bitr4i eqriv $.
  $}

  $( De Morgan's law for union.  Theorem 5.2(13) of [Stoll] p. 19.
     (Contributed by NM, 18-Aug-2004.) $)
  undm $p |- ( _V \ ( A u. B ) ) = ( ( _V \ A ) i^i ( _V \ B ) ) $=
    cvv cA cB difundi $.

  $( De Morgan's law for intersection.  Theorem 5.2(13') of [Stoll] p. 19.
     (Contributed by NM, 18-Aug-2004.) $)
  indm $p |- ( _V \ ( A i^i B ) ) = ( ( _V \ A ) u. ( _V \ B ) ) $=
    cvv cA cB difindi $.

  $( A relationship involving double difference and union.  (Contributed by NM,
     29-Aug-2004.) $)
  difun1 $p |- ( A \ ( B u. C ) ) = ( ( A \ B ) \ C ) $=
    cA cvv cB cdif cin cC cdif cA cB cC cun cdif cA cB cdif cC cdif cA cvv cB
    cdif cvv cC cdif cin cin cA cvv cB cdif cin cC cdif cA cB cC cun cdif cA
    cvv cB cdif cin cvv cC cdif cin cA cvv cB cdif cvv cC cdif cin cin cA cvv
    cB cdif cin cC cdif cA cvv cB cdif cvv cC cdif inass cA cvv cB cdif cin cC
    invdif eqtr3i cA cvv cB cC cun cdif cin cA cvv cB cdif cvv cC cdif cin cin
    cA cB cC cun cdif cvv cB cC cun cdif cvv cB cdif cvv cC cdif cin cA cB cC
    undm ineq2i cA cB cC cun invdif eqtr3i eqtr3i cA cvv cB cdif cin cA cB cdif
    cC cA cB invdif difeq1i eqtr3i $.

  ${
    $d A x $.  $d B x $.  $d C x $.
    $( An equality involving class union and class difference.  The first
       equality of Exercise 13 of [TakeutiZaring] p. 22.  (Contributed by Alan
       Sare, 17-Apr-2012.) $)
    undif3 $p |- ( A u. ( B \ C ) ) = ( ( A u. B ) \ ( C \ A ) ) $=
      vx cA cB cC cdif cun cA cB cun cC cA cdif cdif vx cv cA cB cun wcel vx cv
      cC cA cdif wcel wn wa vx cv cA wcel vx cv cB wcel wo vx cv cC wcel wn vx
      cv cA wcel wo wa vx cv cA cB cun cC cA cdif cdif wcel vx cv cA cB cC cdif
      cun wcel vx cv cA cB cun wcel vx cv cA wcel vx cv cB wcel wo vx cv cC cA
      cdif wcel wn vx cv cC wcel wn vx cv cA wcel wo vx cv cA cB elun vx cv cC
      wcel vx cv cA wcel wn wa vx cv cC wcel wn vx cv cA wcel wo vx cv cC cA
      cdif wcel vx cv cC wcel vx cv cA wcel pm4.53 vx cv cC cA eldif xchnxbir
      anbi12i vx cv cA cB cun cC cA cdif eldif vx cv cA cB cC cdif cun wcel vx
      cv cA wcel vx cv cB cC cdif wcel wo vx cv cA wcel vx cv cB wcel vx cv cC
      wcel wn wa wo vx cv cA wcel vx cv cB wcel wo vx cv cC wcel wn vx cv cA
      wcel wo wa vx cv cA cB cC cdif elun vx cv cB cC cdif wcel vx cv cB wcel
      vx cv cC wcel wn wa vx cv cA wcel vx cv cB cC eldif orbi2i vx cv cA wcel
      vx cv cB wcel vx cv cC wcel wn wa wo vx cv cA wcel vx cv cB wcel wo vx cv
      cC wcel wn vx cv cA wcel wo wa vx cv cA wcel vx cv cA wcel vx cv cB wcel
      wo vx cv cC wcel wn vx cv cA wcel wo wa vx cv cB wcel vx cv cC wcel wn wa
      vx cv cA wcel vx cv cA wcel vx cv cB wcel wo vx cv cC wcel wn vx cv cA
      wcel wo vx cv cA wcel vx cv cB wcel orc vx cv cA wcel vx cv cC wcel wn
      olc jca vx cv cB wcel vx cv cA wcel vx cv cB wcel wo vx cv cC wcel wn vx
      cv cC wcel wn vx cv cA wcel wo vx cv cB wcel vx cv cA wcel olc vx cv cC
      wcel wn vx cv cA wcel orc anim12i jaoi vx cv cA wcel vx cv cC wcel wn vx
      cv cB wcel vx cv cA wcel vx cv cA wcel vx cv cB wcel vx cv cC wcel wn wa
      wo vx cv cA wcel vx cv cC wcel wn wa vx cv cA wcel vx cv cB wcel vx cv cC
      wcel wn wa vx cv cA wcel vx cv cC wcel wn simpl orcd vx cv cB wcel vx cv
      cC wcel wn wa vx cv cA wcel olc vx cv cA wcel vx cv cA wcel vx cv cB wcel
      vx cv cC wcel wn wa wo vx cv cA wcel vx cv cA wcel vx cv cB wcel vx cv cC
      wcel wn wa orc adantr vx cv cA wcel vx cv cA wcel vx cv cB wcel vx cv cC
      wcel wn wa wo vx cv cB wcel vx cv cA wcel vx cv cB wcel vx cv cC wcel wn
      wa orc adantl ccase impbii 3bitri 3bitr4ri eqriv $.

    $( Represent a set difference as an intersection with a larger difference.
       (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    difin2 $p |- ( A C_ C -> ( A \ B ) = ( ( C \ B ) i^i A ) ) $=
      cA cC wss vx cA cB cdif cC cB cdif cA cin cA cC wss vx cv cA wcel vx cv
      cB wcel wn wa vx cv cA wcel vx cv cC wcel wa vx cv cB wcel wn wa vx cv cA
      cB cdif wcel vx cv cC cB cdif cA cin wcel cA cC wss vx cv cA wcel vx cv
      cA wcel vx cv cC wcel wa vx cv cB wcel wn cA cC wss vx cv cA wcel vx cv
      cC wcel cA cC vx cv ssel pm4.71d anbi1d vx cv cA cB eldif vx cv cC cB
      cdif cA cin wcel vx cv cC cB cdif wcel vx cv cA wcel wa vx cv cC wcel vx
      cv cB wcel wn wa vx cv cA wcel wa vx cv cA wcel vx cv cC wcel wa vx cv cB
      wcel wn wa vx cv cC cB cdif cA elin vx cv cC cB cdif wcel vx cv cC wcel
      vx cv cB wcel wn wa vx cv cA wcel vx cv cC cB eldif anbi1i vx cv cC wcel
      vx cv cB wcel wn wa vx cv cA wcel wa vx cv cA wcel vx cv cC wcel vx cv cB
      wcel wn wa wa vx cv cA wcel vx cv cC wcel wa vx cv cB wcel wn wa vx cv cC
      wcel vx cv cB wcel wn wa vx cv cA wcel ancom vx cv cA wcel vx cv cC wcel
      vx cv cB wcel wn anass bitr4i 3bitri 3bitr4g eqrdv $.
  $}

  $( Swap second and third argument of double difference.  (Contributed by NM,
     18-Aug-2004.) $)
  dif32 $p |- ( ( A \ B ) \ C ) = ( ( A \ C ) \ B ) $=
    cA cB cC cun cdif cA cC cB cun cdif cA cB cdif cC cdif cA cC cdif cB cdif
    cB cC cun cC cB cun cA cB cC uncom difeq2i cA cB cC difun1 cA cC cB difun1
    3eqtr3i $.

  $( Absorption-like law for class difference: you can remove a class only
     once.  (Contributed by FL, 2-Aug-2009.) $)
  difabs $p |- ( ( A \ B ) \ B ) = ( A \ B ) $=
    cA cB cB cun cdif cA cB cdif cB cdif cA cB cdif cA cB cB difun1 cB cB cun
    cB cA cB unidm difeq2i eqtr3i $.

  $( Two ways to express symmetric difference.  This theorem shows the
     equivalence of the definition of symmetric difference in [Stoll] p. 13 and
     the restated definition in Example 4.1 of [Stoll] p. 262.  (Contributed by
     NM, 17-Aug-2004.) $)
  symdif1 $p |- ( ( A \ B ) u. ( B \ A ) ) = ( ( A u. B ) \ ( A i^i B ) ) $=
    cA cB cun cA cB cin cdif cA cA cB cin cdif cB cA cB cin cdif cun cA cB cdif
    cB cA cdif cun cA cB cA cB cin difundir cA cA cB cin cdif cA cB cdif cB cA
    cB cin cdif cB cA cdif cA cB difin cB cA cB cin cdif cB cB cA cin cdif cB
    cA cdif cA cB cin cB cA cin cB cA cB incom difeq2i cB cA difin eqtri
    uneq12i eqtr2i $.

  ${
    $d x A $.  $d x B $.
    $( Two ways to express symmetric difference.  (Contributed by NM,
       17-Aug-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    symdif2 $p |- ( ( A \ B ) u. ( B \ A ) ) =
                  { x | -. ( x e. A <-> x e. B ) } $=
      vx cv cA wcel vx cv cB wcel wb wn vx cA cB cdif cB cA cdif cun vx cv cA
      cB cdif wcel vx cv cB cA cdif wcel wo vx cv cA wcel vx cv cB wcel wn wa
      vx cv cB wcel vx cv cA wcel wn wa wo vx cv cA cB cdif cB cA cdif cun wcel
      vx cv cA wcel vx cv cB wcel wb wn vx cv cA cB cdif wcel vx cv cA wcel vx
      cv cB wcel wn wa vx cv cB cA cdif wcel vx cv cB wcel vx cv cA wcel wn wa
      vx cv cA cB eldif vx cv cB cA eldif orbi12i vx cv cA cB cdif cB cA cdif
      elun vx cv cA wcel vx cv cB wcel xor 3bitr4i abbi2i $.
  $}

  ${
    $d x y $.  $d ph y $.  $d ps y $.
    $( Union of two class abstractions.  (Contributed by NM, 29-Sep-2002.)
       (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    unab $p |- ( { x | ph } u. { x | ps } ) = { x | ( ph \/ ps ) } $=
      vy wph vx cab wps vx cab wph wps wo vx cab wph wps wo vx vy wsb wph vx vy
      wsb wps vx vy wsb wo vy cv wph wps wo vx cab wcel vy cv wph vx cab wcel
      vy cv wps vx cab wcel wo wph wps vx vy sbor wph wps wo vy vx df-clab vy
      cv wph vx cab wcel wph vx vy wsb vy cv wps vx cab wcel wps vx vy wsb wph
      vy vx df-clab wps vy vx df-clab orbi12i 3bitr4ri uneqri $.

    $( Intersection of two class abstractions.  (Contributed by NM,
       29-Sep-2002.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    inab $p |- ( { x | ph } i^i { x | ps } ) = { x | ( ph /\ ps ) } $=
      vy wph vx cab wps vx cab wph wps wa vx cab wph wps wa vx vy wsb wph vx vy
      wsb wps vx vy wsb wa vy cv wph wps wa vx cab wcel vy cv wph vx cab wcel
      vy cv wps vx cab wcel wa wph wps vx vy sban wph wps wa vy vx df-clab vy
      cv wph vx cab wcel wph vx vy wsb vy cv wps vx cab wcel wps vx vy wsb wph
      vy vx df-clab wps vy vx df-clab anbi12i 3bitr4ri ineqri $.

    $( Difference of two class abstractions.  (Contributed by NM,
       23-Oct-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    difab $p |- ( { x | ph } \ { x | ps } ) = { x | ( ph /\ -. ps ) } $=
      vy wph vx cab wps vx cab wph wps wn wa vx cab vy cv wph wps wn wa vx cab
      wcel wph wps wn wa vx vy wsb wph vx vy wsb wps wn vx vy wsb wa vy cv wph
      vx cab wcel vy cv wps vx cab wcel wn wa wph wps wn wa vy vx df-clab wph
      wps wn vx vy sban wph vx vy wsb vy cv wph vx cab wcel wps wn vx vy wsb vy
      cv wps vx cab wcel wn vy cv wph vx cab wcel wph vx vy wsb wph vy vx
      df-clab bicomi wps wn vx vy wsb wps vx vy wsb vy cv wps vx cab wcel wps
      vx vy sbn wps vy vx df-clab xchbinxr anbi12i 3bitrri difeqri $.
  $}

  $( A class builder defined by a negation.  (Contributed by FL,
     18-Sep-2010.) $)
  notab $p |- { x | -. ph } = ( _V \ { x | ph } ) $=
    vx cv cvv wcel wph wn wa vx cab wph wn vx cab cvv wph vx cab cdif wph wn vx
    cvv crab vx cv cvv wcel wph wn wa vx cab wph wn vx cab wph wn vx cvv df-rab
    wph wn vx rabab eqtr3i vx cv cvv wcel vx cab wph vx cab cdif vx cv cvv wcel
    wph wn wa vx cab cvv wph vx cab cdif vx cv cvv wcel wph vx difab vx cv cvv
    wcel vx cab cvv wph vx cab vx cvv abid2 difeq1i eqtr3i eqtr3i $.

  $( Union of two restricted class abstractions.  (Contributed by NM,
     25-Mar-2004.) $)
  unrab $p |- ( { x e. A | ph } u. { x e. A | ps } ) =
              { x e. A | ( ph \/ ps ) } $=
    wph vx cA crab wps vx cA crab cun vx cv cA wcel wph wa vx cab vx cv cA wcel
    wps wa vx cab cun wph wps wo vx cA crab wph vx cA crab vx cv cA wcel wph wa
    vx cab wps vx cA crab vx cv cA wcel wps wa vx cab wph vx cA df-rab wps vx
    cA df-rab uneq12i wph wps wo vx cA crab vx cv cA wcel wph wps wo wa vx cab
    vx cv cA wcel wph wa vx cab vx cv cA wcel wps wa vx cab cun wph wps wo vx
    cA df-rab vx cv cA wcel wph wa vx cab vx cv cA wcel wps wa vx cab cun vx cv
    cA wcel wph wa vx cv cA wcel wps wa wo vx cab vx cv cA wcel wph wps wo wa
    vx cab vx cv cA wcel wph wa vx cv cA wcel wps wa vx unab vx cv cA wcel wph
    wps wo wa vx cv cA wcel wph wa vx cv cA wcel wps wa wo vx vx cv cA wcel wph
    wps andi abbii eqtr4i eqtr4i eqtr4i $.

  $( Intersection of two restricted class abstractions.  (Contributed by NM,
     1-Sep-2006.) $)
  inrab $p |- ( { x e. A | ph } i^i { x e. A | ps } ) =
              { x e. A | ( ph /\ ps ) } $=
    wph vx cA crab wps vx cA crab cin vx cv cA wcel wph wa vx cab vx cv cA wcel
    wps wa vx cab cin wph wps wa vx cA crab wph vx cA crab vx cv cA wcel wph wa
    vx cab wps vx cA crab vx cv cA wcel wps wa vx cab wph vx cA df-rab wps vx
    cA df-rab ineq12i wph wps wa vx cA crab vx cv cA wcel wph wps wa wa vx cab
    vx cv cA wcel wph wa vx cab vx cv cA wcel wps wa vx cab cin wph wps wa vx
    cA df-rab vx cv cA wcel wph wa vx cab vx cv cA wcel wps wa vx cab cin vx cv
    cA wcel wph wa vx cv cA wcel wps wa wa vx cab vx cv cA wcel wph wps wa wa
    vx cab vx cv cA wcel wph wa vx cv cA wcel wps wa vx inab vx cv cA wcel wph
    wps wa wa vx cv cA wcel wph wa vx cv cA wcel wps wa wa vx vx cv cA wcel wph
    wps anandi abbii eqtr4i eqtr4i eqtr4i $.

  ${
    $d x B $.
    $( Intersection with a restricted class abstraction.  (Contributed by NM,
       19-Nov-2007.) $)
    inrab2 $p |- ( { x e. A | ph } i^i B ) = { x e. ( A i^i B ) | ph } $=
      wph vx cA crab cB cin vx cv cA wcel wph wa vx cab vx cv cB wcel vx cab
      cin wph vx cA cB cin crab wph vx cA crab vx cv cA wcel wph wa vx cab cB
      vx cv cB wcel vx cab wph vx cA df-rab vx cv cB wcel vx cab cB vx cB abid2
      eqcomi ineq12i wph vx cA cB cin crab vx cv cA cB cin wcel wph wa vx cab
      vx cv cA wcel wph wa vx cab vx cv cB wcel vx cab cin wph vx cA cB cin
      df-rab vx cv cA wcel wph wa vx cab vx cv cB wcel vx cab cin vx cv cA wcel
      wph wa vx cv cB wcel wa vx cab vx cv cA cB cin wcel wph wa vx cab vx cv
      cA wcel wph wa vx cv cB wcel vx inab vx cv cA cB cin wcel wph wa vx cv cA
      wcel wph wa vx cv cB wcel wa vx vx cv cA cB cin wcel wph wa vx cv cA wcel
      vx cv cB wcel wa wph wa vx cv cA wcel wph wa vx cv cB wcel wa vx cv cA cB
      cin wcel vx cv cA wcel vx cv cB wcel wa wph vx cv cA cB elin anbi1i vx cv
      cA wcel vx cv cB wcel wph an32 bitri abbii eqtr4i eqtr4i eqtr4i $.
  $}

  $( Difference of two restricted class abstractions.  (Contributed by NM,
     23-Oct-2004.) $)
  difrab $p |- ( { x e. A | ph } \ { x e. A | ps } ) =
              { x e. A | ( ph /\ -. ps ) } $=
    wph vx cA crab wps vx cA crab cdif vx cv cA wcel wph wa vx cab vx cv cA
    wcel wps wa vx cab cdif wph wps wn wa vx cA crab wph vx cA crab vx cv cA
    wcel wph wa vx cab wps vx cA crab vx cv cA wcel wps wa vx cab wph vx cA
    df-rab wps vx cA df-rab difeq12i wph wps wn wa vx cA crab vx cv cA wcel wph
    wps wn wa wa vx cab vx cv cA wcel wph wa vx cab vx cv cA wcel wps wa vx cab
    cdif wph wps wn wa vx cA df-rab vx cv cA wcel wph wa vx cab vx cv cA wcel
    wps wa vx cab cdif vx cv cA wcel wph wa vx cv cA wcel wps wa wn wa vx cab
    vx cv cA wcel wph wps wn wa wa vx cab vx cv cA wcel wph wa vx cv cA wcel
    wps wa vx difab vx cv cA wcel wph wps wn wa wa vx cv cA wcel wph wa vx cv
    cA wcel wps wa wn wa vx vx cv cA wcel wph wps wn wa wa vx cv cA wcel wph wa
    wps wn wa vx cv cA wcel wph wa vx cv cA wcel wps wa wn wa vx cv cA wcel wph
    wps wn anass vx cv cA wcel wph wa wps wn wa vx cv cA wcel wph wa vx cv cA
    wcel wps wa wn wa wps wn vx cv cA wcel wps wa wn vx cv cA wcel wph wa vx cv
    cA wcel wps wa wps vx cv cA wcel wps simpr con3i anim2i vx cv cA wcel wph
    wa vx cv cA wcel wps wa wn wps wn vx cv cA wcel wph wa wps vx cv cA wcel
    wps wa vx cv cA wcel wps vx cv cA wcel wps wa wi wph vx cv cA wcel wps
    pm3.2 adantr con3d imdistani impbii bitr3i abbii eqtr4i eqtr4i eqtr4i $.

  ${
    $d x A $.  $d x B $.
    $( Alternate definition of restricted class abstraction.  (Contributed by
       NM, 20-Sep-2003.) $)
    dfrab2 $p |- { x e. A | ph } = ( { x | ph } i^i A ) $=
      wph vx cA crab vx cv cA wcel wph wa vx cab cA wph vx cab cin wph vx cab
      cA cin wph vx cA df-rab vx cv cA wcel vx cab wph vx cab cin vx cv cA wcel
      wph wa vx cab cA wph vx cab cin vx cv cA wcel wph vx inab vx cv cA wcel
      vx cab cA wph vx cab vx cA abid2 ineq1i eqtr3i cA wph vx cab incom 3eqtri
      $.

    $( Alternate definition of restricted class abstraction.  (Contributed by
       Mario Carneiro, 8-Sep-2013.) $)
    dfrab3 $p |- { x e. A | ph } = ( A i^i { x | ph } ) $=
      wph vx cA crab vx cv cA wcel wph wa vx cab vx cv cA wcel vx cab wph vx
      cab cin cA wph vx cab cin wph vx cA df-rab vx cv cA wcel wph vx inab vx
      cv cA wcel vx cab cA wph vx cab vx cA abid2 ineq1i 3eqtr2i $.

    $( Complementation of restricted class abstractions.  (Contributed by Mario
       Carneiro, 3-Sep-2015.) $)
    notrab $p |- ( A \ { x e. A | ph } ) = { x e. A | -. ph } $=
      vx cv cA wcel vx cab wph vx cab cdif vx cv cA wcel wph wn wa vx cab cA
      wph vx cA crab cdif wph wn vx cA crab vx cv cA wcel wph vx difab cA cA
      wph vx cab cin cdif cA wph vx cab cdif cA wph vx cA crab cdif vx cv cA
      wcel vx cab wph vx cab cdif cA wph vx cab difin wph vx cA crab cA wph vx
      cab cin cA wph vx cA dfrab3 difeq2i vx cv cA wcel vx cab cA wph vx cab vx
      cA abid2 difeq1i 3eqtr4i wph wn vx cA df-rab 3eqtr4i $.

    $( Restricted class abstraction with a common superset.  (Contributed by
       Stefan O'Rear, 12-Sep-2015.)  (Proof shortened by Mario Carneiro,
       8-Nov-2015.) $)
    dfrab3ss $p |- ( A C_ B -> { x e. A | ph } = ( A i^i { x e. B | ph } ) ) $=
      cA cB wss cA wph vx cab cin cA cB cin wph vx cab cin wph vx cA crab cA
      wph vx cB crab cin cA cB wss cA cB cin cA wceq cA wph vx cab cin cA cB
      cin wph vx cab cin wceq cA cB df-ss cA cB cin cA wceq cA cB cin wph vx
      cab cin cA wph vx cab cin cA cB cin cA wph vx cab ineq1 eqcomd sylbi wph
      vx cA dfrab3 cA wph vx cB crab cin cA cB wph vx cab cin cin cA cB cin wph
      vx cab cin wph vx cB crab cB wph vx cab cin cA wph vx cB dfrab3 ineq2i cA
      cB wph vx cab inass eqtr4i 3eqtr4g $.
  $}

  $( Abstraction restricted to a union.  (Contributed by Stefan O'Rear,
     5-Feb-2015.) $)
  rabun2 $p |- { x e. ( A u. B ) | ph } =
      ( { x e. A | ph } u. { x e. B | ph } ) $=
    wph vx cA cB cun crab vx cv cA cB cun wcel wph wa vx cab wph vx cA crab wph
    vx cB crab cun wph vx cA cB cun df-rab wph vx cA crab wph vx cB crab cun vx
    cv cA wcel wph wa vx cab vx cv cB wcel wph wa vx cab cun vx cv cA cB cun
    wcel wph wa vx cab wph vx cA crab vx cv cA wcel wph wa vx cab wph vx cB
    crab vx cv cB wcel wph wa vx cab wph vx cA df-rab wph vx cB df-rab uneq12i
    vx cv cA cB cun wcel wph wa vx cab vx cv cA wcel wph wa vx cv cB wcel wph
    wa wo vx cab vx cv cA wcel wph wa vx cab vx cv cB wcel wph wa vx cab cun vx
    cv cA cB cun wcel wph wa vx cv cA wcel wph wa vx cv cB wcel wph wa wo vx vx
    cv cA cB cun wcel wph wa vx cv cA wcel vx cv cB wcel wo wph wa vx cv cA
    wcel wph wa vx cv cB wcel wph wa wo vx cv cA cB cun wcel vx cv cA wcel vx
    cv cB wcel wo wph vx cv cA cB elun anbi1i vx cv cA wcel vx cv cB wcel wph
    andir bitri abbii vx cv cA wcel wph wa vx cv cB wcel wph wa vx unab eqtr4i
    eqtr4i eqtr4i $.

  ${
    $d x A $.  $d x B $.
    $( Transfer uniqueness to a smaller subclass.  (Contributed by NM,
       20-Oct-2005.) $)
    reuss2 $p |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\
                 ( E. x e. A ph /\ E! x e. B ps ) ) -> E! x e. A ph ) $=
      wph vx cA wrex wps vx cB wreu wa cA cB wss wph wps wi vx cA wral wa vx cv
      cA wcel wph wa vx wex vx cv cB wcel wps wa vx weu wa wph vx cA wreu wph
      vx cA wrex vx cv cA wcel wph wa vx wex wps vx cB wreu vx cv cB wcel wps
      wa vx weu wph vx cA df-rex wps vx cB df-reu anbi12i cA cB wss wph wps wi
      vx cA wral wa vx cv cA wcel wph wa vx wex vx cv cB wcel wps wa vx weu wa
      wa vx cv cA wcel wph wa vx weu wph vx cA wreu cA cB wss wph wps wi vx cA
      wral wa vx cv cA wcel wph wa vx wex vx cv cB wcel wps wa vx weu vx cv cA
      wcel wph wa vx weu cA cB wss wph wps wi vx cA wral wa vx cv cB wcel wps
      wa vx weu vx cv cA wcel wph wa vx wmo vx cv cA wcel wph wa vx wex vx cv
      cA wcel wph wa vx weu cA cB wss wph wps wi vx cA wral wa vx cv cA wcel
      wph wa vx cv cB wcel wps wa wi vx wal vx cv cB wcel wps wa vx weu vx cv
      cA wcel wph wa vx wmo wi wph wps wi vx cA wral cA cB wss vx cv cA wcel
      wph wps wi wi vx wal vx cv cA wcel wph wa vx cv cB wcel wps wa wi vx wal
      wph wps wi vx cA df-ral cA cB wss vx cv cA wcel wph wps wi wi vx wal vx
      cv cA wcel wph wa vx cv cB wcel wps wa wi vx wal cA cB wss vx cv cA wcel
      wph wps wi wi vx cv cA wcel wph wa vx cv cB wcel wps wa wi vx cA cB wss
      vx cv cA wcel wph wps wi wi vx cv cA wcel wph vx cv cB wcel wps wa cA cB
      wss vx cv cA wcel wph wps wi wph vx cv cB wcel wps wa wi cA cB wss wph
      wps wi vx cv cA wcel wph vx cv cB wcel wps wa wi cA cB wss wph wps wi vx
      cv cA wcel wph vx cv cB wcel wps wa cA cB wss vx cv cA wcel vx cv cB wcel
      wi wph wps wi vx cv cA wcel wph wa vx cv cB wcel wps wa wi cA cB vx cv
      ssel vx cv cA wcel vx cv cB wcel wph wps prth sylan exp4b com23 a2d imp4a
      alimdv imp sylan2b vx cv cA wcel wph wa vx cv cB wcel wps wa vx euimmo
      syl vx cv cA wcel wph wa vx weu vx cv cA wcel wph wa vx wex vx cv cA wcel
      wph wa vx wmo vx cv cA wcel wph wa vx eu5 simplbi2 syl9 imp32 wph vx cA
      df-reu sylibr sylan2b $.

    $( Transfer uniqueness to a smaller subclass.  (Contributed by NM,
       21-Aug-1999.) $)
    reuss $p |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) ->
                E! x e. A ph ) $=
      cA cB wss wph vx cA wrex wph vx cB wreu wph vx cA wreu cA cB wss wph wph
      wi vx cA wral wph vx cA wrex wph vx cB wreu wa wph vx cA wreu wph wph wi
      vx cA vx cv cA wcel wph idd rgen wph wph vx cA cB reuss2 mpanl2 3impb $.

    $( Transfer uniqueness to a smaller class.  (Contributed by NM,
       21-Oct-2005.) $)
    reuun1 $p |- ( ( E. x e. A ph /\ E! x e. ( A u. B ) ( ph \/ ps ) )
                 -> E! x e. A ph ) $=
      cA cA cB cun wss wph wph wps wo wi vx cA wral wph vx cA wrex wph wps wo
      vx cA cB cun wreu wa wph vx cA wreu cA cB ssun1 wph wph wps wo wi vx cA
      wph wps orc rgenw wph wph wps wo vx cA cA cB cun reuss2 mpanl12 $.

    $( Transfer uniqueness to a smaller or larger class.  (Contributed by NM,
       21-Oct-2005.) $)
    reuun2 $p |- ( -. E. x e. B ph ->
             ( E! x e. ( A u. B ) ph <-> E! x e. A ph ) ) $=
      wph vx cB wrex wn vx cv cB wcel wph wa vx cv cA wcel wph wa wo vx weu vx
      cv cA wcel wph wa vx weu wph vx cA cB cun wreu wph vx cA wreu wph vx cB
      wrex vx cv cB wcel wph wa vx wex vx cv cB wcel wph wa vx cv cA wcel wph
      wa wo vx weu vx cv cA wcel wph wa vx weu wb wph vx cB df-rex vx cv cB
      wcel wph wa vx cv cA wcel wph wa vx euor2 sylnbi wph vx cA cB cun wreu vx
      cv cA cB cun wcel wph wa vx weu vx cv cB wcel wph wa vx cv cA wcel wph wa
      wo vx weu wph vx cA cB cun df-reu vx cv cA cB cun wcel wph wa vx cv cB
      wcel wph wa vx cv cA wcel wph wa wo vx vx cv cA cB cun wcel wph wa vx cv
      cA wcel vx cv cB wcel wo wph wa vx cv cB wcel wph wa vx cv cA wcel wph wa
      wo vx cv cA cB cun wcel vx cv cA wcel vx cv cB wcel wo wph vx cv cA cB
      elun anbi1i vx cv cA wcel vx cv cB wcel wo wph wa vx cv cA wcel wph wa vx
      cv cB wcel wph wa wo vx cv cB wcel wph wa vx cv cA wcel wph wa wo vx cv
      cA wcel vx cv cB wcel wph andir vx cv cA wcel wph wa vx cv cB wcel wph wa
      orcom bitri bitri eubii bitri wph vx cA df-reu 3bitr4g $.

    $( Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       NM, 21-Aug-1999.) $)
    reupick $p |- ( ( ( A C_ B /\ ( E. x e. A ph /\ E! x e. B ph ) ) /\ ph ) ->
                  ( x e. A <-> x e. B ) ) $=
      cA cB wss wph vx cA wrex wph vx cB wreu wa wa wph wa vx cv cA wcel vx cv
      cB wcel cA cB wss vx cv cA wcel vx cv cB wcel wi wph vx cA wrex wph vx cB
      wreu wa wph cA cB vx cv ssel ad2antrr cA cB wss wph vx cA wrex wph vx cB
      wreu wa wa wph vx cv cB wcel vx cv cA wcel wi cA cB wss wph vx cA wrex
      wph vx cB wreu wa wa vx cv cB wcel wph vx cv cA wcel wph vx cA wrex wph
      vx cB wreu wa cA cB wss vx cv cA wcel wph wa vx wex vx cv cB wcel wph wa
      vx weu wa vx cv cB wcel wph wa vx cv cA wcel wi wph vx cA wrex vx cv cA
      wcel wph wa vx wex wph vx cB wreu vx cv cB wcel wph wa vx weu wph vx cA
      df-rex wph vx cB df-reu anbi12i cA cB wss vx cv cA wcel wph wa vx wex vx
      cv cB wcel wph wa vx weu vx cv cB wcel wph wa vx cv cA wcel wi cA cB wss
      vx cv cB wcel wph wa vx weu vx cv cA wcel wph wa vx wex vx cv cB wcel wph
      wa vx cv cA wcel wi cA cB wss vx cv cA wcel wph wa vx wex vx cv cB wcel
      wph wa vx cv cA wcel wa vx wex vx cv cB wcel wph wa vx weu vx cv cB wcel
      wph wa vx cv cA wcel wi cA cB wss vx cv cA wcel wph wa vx cv cB wcel wph
      wa vx cv cA wcel wa vx cA cB wss vx cv cA wcel wph wa vx cv cB wcel vx cv
      cA wcel wa wph wa vx cv cB wcel wph wa vx cv cA wcel wa cA cB wss vx cv
      cA wcel vx cv cB wcel vx cv cA wcel wa wph cA cB wss vx cv cA wcel vx cv
      cB wcel cA cB vx cv ssel ancrd anim1d vx cv cB wcel vx cv cA wcel wph
      an32 syl6ib eximdv vx cv cB wcel wph wa vx weu vx cv cB wcel wph wa vx cv
      cA wcel wa vx wex vx cv cB wcel wph wa vx cv cA wcel wi vx cv cB wcel wph
      wa vx cv cA wcel vx eupick ex syl9 com23 imp32 sylan2b exp3acom23 imp
      impbid $.

    $( Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       Mario Carneiro, 19-Nov-2016.) $)
    reupick3 $p  |- ( ( E! x e. A ph /\ E. x e. A ( ph /\ ps ) /\ x e. A ) ->
       ( ph -> ps ) ) $=
      wph vx cA wreu wph wps wa vx cA wrex vx cv cA wcel wph wps wi wph vx cA
      wreu wph wps wa vx cA wrex wa vx cv cA wcel wph wps wph vx cA wreu vx cv
      cA wcel wph wa vx weu vx cv cA wcel wph wa wps wa vx wex vx cv cA wcel
      wph wa wps wi wph wps wa vx cA wrex wph vx cA df-reu wph wps wa vx cA
      wrex vx cv cA wcel wph wps wa wa vx wex vx cv cA wcel wph wa wps wa vx
      wex wph wps wa vx cA df-rex vx cv cA wcel wph wa wps wa vx cv cA wcel wph
      wps wa wa vx vx cv cA wcel wph wps anass exbii bitr4i vx cv cA wcel wph
      wa wps vx eupick syl2anb exp3a 3impia $.

    $( Restricted uniqueness "picks" a member of a subclass.  (Contributed by
       Mario Carneiro, 15-Dec-2013.)  (Proof shortened by Mario Carneiro,
       19-Nov-2016.) $)
    reupick2 $p |- ( ( ( A. x e. A ( ps -> ph ) /\ E. x e. A ps /\
                       E! x e. A ph ) /\ x e. A ) -> ( ph <-> ps ) ) $=
      wps wph wi vx cA wral wps vx cA wrex wph vx cA wreu w3a vx cv cA wcel wa
      wph wps wps wph wi vx cA wral wps vx cA wrex wph vx cA wreu vx cv cA wcel
      wph wps wi wps wph wi vx cA wral wps vx cA wrex wph wps wa vx cA wrex wph
      vx cA wreu vx cv cA wcel wph wps wi wi wi wps wph wi vx cA wral wps wph
      wps wa wi vx cA wral wps vx cA wrex wph wps wa vx cA wrex wi wps wph wi
      wps wph wps wa wi vx cA wps wph ancr ralimi wps wph wps wa vx cA rexim
      syl wph vx cA wreu wph wps wa vx cA wrex vx cv cA wcel wph wps wi wi wph
      vx cA wreu wph wps wa vx cA wrex vx cv cA wcel wph wps wi wph wps vx cA
      reupick3 3exp com12 syl6 3imp1 wps wph wi vx cA wral wps vx cA wrex wph
      vx cA wreu w3a vx cv cA wcel wps wph wi wps wph wi vx cA wral wps vx cA
      wrex vx cv cA wcel wps wph wi wi wph vx cA wreu wps wph wi vx cA rsp
      3ad2ant1 imp impbid $.
  $}


