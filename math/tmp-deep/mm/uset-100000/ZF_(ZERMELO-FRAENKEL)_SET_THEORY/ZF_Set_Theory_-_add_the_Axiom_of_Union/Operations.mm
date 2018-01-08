
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Functions.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Operations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend class notation to include the value of an operation ` F ` (such as
     ` + ` ) for two arguments ` A ` and ` B ` .  Note that the syntax is
     simply three class symbols in a row surrounded by parentheses.  Since
     operation values are the only possible class expressions consisting of
     three class expressions in a row surrounded by parentheses, the syntax is
     unambiguous.  (For an example of how syntax could become ambiguous if we
     are not careful, see the comment in ~ cneg .) $)
  co $a class ( A F B ) $.

  $( Extend class notation to include class abstraction (class builder) of
     nested ordered pairs. $)
  coprab $a class { <. <. x , y >. , z >. | ph } $.

  $( Extend the definition of a class to include maps-to notation for defining
     an operation via a rule. $)
  cmpt2 $a class ( x e. A , y e. B |-> C ) $.

  $( Define the value of an operation.  Definition of operation value in
     [Enderton] p. 79.  Note that the syntax is simply three class expressions
     in a row bracketed by parentheses.  There are no restrictions of any kind
     on what those class expressions may be, although only certain kinds of
     class expressions - a binary operation ` F ` and its arguments ` A ` and
     ` B ` - will be useful for proving meaningful theorems.  For example, if
     class ` F ` is the operation ` + ` and arguments ` A ` and ` B ` are ` 3 `
     and ` 2 ` , the expression ` ( 3 + 2 ) ` can be proved to equal ` 5 ` (see
     ~ 3p2e5 ).  This definition is well-defined, although not very meaningful,
     when classes ` A ` and/or ` B ` are proper classes (i.e. are not sets);
     see ~ ovprc1 and ~ ovprc2 .  On the other hand, we often find uses for
     this definition when ` F ` is a proper class, such as ` +o ` in ~ oav .
     ` F ` is normally equal to a class of nested ordered pairs of the form
     defined by ~ df-oprab .  (Contributed by NM, 28-Feb-1995.) $)
  df-ov $a |- ( A F B ) = ( F ` <. A , B >. ) $.

  ${
    $d x w $.  $d y w $.  $d z w $.  $d w ph $.
    $( Define the class abstraction (class builder) of a collection of nested
       ordered pairs (for use in defining operations).  This is a special case
       of Definition 4.16 of [TakeutiZaring] p. 14.  Normally ` x ` , ` y ` ,
       and ` z ` are distinct, although the definition doesn't strictly require
       it.  See ~ df-ov for the value of an operation.  The brace notation is
       called "class abstraction" by Quine; it is also called a "class builder"
       in the literature.  The value of the most common operation class builder
       is given by ~ ovmpt2 .  (Contributed by NM, 12-Mar-1995.) $)
    df-oprab $a |- { <. <. x , y >. , z >. | ph } =
                  { w | E. x E. y E. z ( w = <. <. x , y >. , z >. /\ ph ) } $.
  $}

  ${
    $d x z $.  $d y z $.  $d z A $.  $d z B $.  $d z C $.
    $( Define maps-to notation for defining an operation via a rule.  Read as
       "the operation defined by the map from ` x , y ` (in ` A X. B ` ) to
       ` B ( x , y ) ` ."  An extension of ~ df-mpt for two arguments.
       (Contributed by NM, 17-Feb-2008.) $)
    df-mpt2 $a |- ( x e. A , y e. B |-> C ) =
             { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ z = C ) } $.
  $}

  $( Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)
  oveq $p |- ( F = G -> ( A F B ) = ( A G B ) ) $=
    cF cG wceq cA cB cop cF cfv cA cB cop cG cfv cA cB cF co cA cB cG co cA cB
    cop cF cG fveq1 cA cB cF df-ov cA cB cG df-ov 3eqtr4g $.

  $( Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)
  oveq1 $p |- ( A = B -> ( A F C ) = ( B F C ) ) $=
    cA cB wceq cA cC cop cF cfv cB cC cop cF cfv cA cC cF co cB cC cF co cA cB
    wceq cA cC cop cB cC cop cF cA cB cC opeq1 fveq2d cA cC cF df-ov cB cC cF
    df-ov 3eqtr4g $.

  $( Equality theorem for operation value.  (Contributed by NM,
     28-Feb-1995.) $)
  oveq2 $p |- ( A = B -> ( C F A ) = ( C F B ) ) $=
    cA cB wceq cC cA cop cF cfv cC cB cop cF cfv cC cA cF co cC cB cF co cA cB
    wceq cC cA cop cC cB cop cF cA cB cC opeq2 fveq2d cC cA cF df-ov cC cB cF
    df-ov 3eqtr4g $.

  $( Equality theorem for operation value.  (Contributed by NM,
     16-Jul-1995.) $)
  oveq12 $p |- ( ( A = B /\ C = D ) -> ( A F C ) = ( B F D ) ) $=
    cA cB wceq cC cD wceq cA cC cF co cB cC cF co cB cD cF co cA cB cC cF oveq1
    cC cD cB cF oveq2 sylan9eq $.

  ${
    oveq1i.1 $e |- A = B $.
    $( Equality inference for operation value.  (Contributed by NM,
       28-Feb-1995.) $)
    oveq1i $p |- ( A F C ) = ( B F C ) $=
      cA cB wceq cA cC cF co cB cC cF co wceq oveq1i.1 cA cB cC cF oveq1 ax-mp
      $.

    $( Equality inference for operation value.  (Contributed by NM,
       28-Feb-1995.) $)
    oveq2i $p |- ( C F A ) = ( C F B ) $=
      cA cB wceq cC cA cF co cC cB cF co wceq oveq1i.1 cA cB cC cF oveq2 ax-mp
      $.

    ${
      oveq12i.2 $e |- C = D $.
      $( Equality inference for operation value.  (Contributed by NM,
         28-Feb-1995.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
      oveq12i $p |- ( A F C ) = ( B F D ) $=
        cA cB wceq cC cD wceq cA cC cF co cB cD cF co wceq oveq1i.1 oveq12i.2
        cA cB cC cD cF oveq12 mp2an $.
    $}

    $( Equality inference for operation value.  (Contributed by NM,
       24-Nov-2007.) $)
    oveqi $p |- ( C A D ) = ( C B D ) $=
      cA cB wceq cC cD cA co cC cD cB co wceq oveq1i.1 cC cD cA cB oveq ax-mp
      $.
  $}

  ${
    oveq123i.1 $e |- A = C $.
    oveq123i.2 $e |- B = D $.
    oveq123i.3 $e |- F = G $.
    $( Equality inference for operation value.  (Contributed by FL,
       11-Jul-2010.) $)
    oveq123i $p |- ( A F B ) = ( C G D ) $=
      cA cB cF co cC cD cF co cC cD cG co cA cC cB cD cF oveq123i.1 oveq123i.2
      oveq12i cF cG cC cD oveq123i.3 oveqi eqtri $.
  $}

  ${
    oveq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) $)
    oveq1d $p |- ( ph -> ( A F C ) = ( B F C ) ) $=
      wph cA cB wceq cA cC cF co cB cC cF co wceq oveq1d.1 cA cB cC cF oveq1
      syl $.

    $( Equality deduction for operation value.  (Contributed by NM,
       13-Mar-1995.) $)
    oveq2d $p |- ( ph -> ( C F A ) = ( C F B ) ) $=
      wph cA cB wceq cC cA cF co cC cB cF co wceq oveq1d.1 cA cB cC cF oveq2
      syl $.

    $( Equality deduction for operation value.  (Contributed by NM,
       9-Sep-2006.) $)
    oveqd $p |- ( ph -> ( C A D ) = ( C B D ) ) $=
      wph cA cB wceq cC cD cA co cC cD cB co wceq oveq1d.1 cC cD cA cB oveq syl
      $.

    ${
      oveq12d.2 $e |- ( ph -> C = D ) $.
      $( Equality deduction for operation value.  (Contributed by NM,
         13-Mar-1995.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
      oveq12d $p |- ( ph -> ( A F C ) = ( B F D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cF co cB cD cF co wceq oveq1d.1
        oveq12d.2 cA cB cC cD cF oveq12 syl2anc $.
    $}

    ${
      opreqan12i.2 $e |- ( ps -> C = D ) $.
      $( Equality deduction for operation value.  (Contributed by NM,
         10-Aug-1995.) $)
      oveqan12d $p |- ( ( ph /\ ps ) -> ( A F C ) = ( B F D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cF co cB cD cF co wceq wps oveq1d.1
        opreqan12i.2 cA cB cC cD cF oveq12 syl2an $.

      $( Equality deduction for operation value.  (Contributed by NM,
         10-Aug-1995.) $)
      oveqan12rd $p |- ( ( ps /\ ph ) -> ( A F C ) = ( B F D ) ) $=
        wph wps cA cC cF co cB cD cF co wceq wph wps cA cB cC cD cF oveq1d.1
        opreqan12i.2 oveqan12d ancoms $.
    $}
  $}

  ${
    oveq123d.1 $e |- ( ph -> F = G ) $.
    oveq123d.2 $e |- ( ph -> A = B ) $.
    oveq123d.3 $e |- ( ph -> C = D ) $.
    $( Equality deduction for operation value.  (Contributed by FL,
       22-Dec-2008.) $)
    oveq123d $p |- ( ph -> ( A F C ) = ( B G D ) ) $=
      wph cA cC cF co cA cC cG co cB cD cG co wph cF cG cA cC oveq123d.1 oveqd
      wph cA cB cC cD cG oveq123d.2 oveq123d.3 oveq12d eqtrd $.
  $}

  ${
    nfovd.2 $e |- ( ph -> F/_ x A ) $.
    nfovd.3 $e |- ( ph -> F/_ x F ) $.
    nfovd.4 $e |- ( ph -> F/_ x B ) $.
    $( Deduction version of bound-variable hypothesis builder ~ nfov .
       (Contributed by NM, 13-Dec-2005.)  (Proof shortened by Andrew Salmon,
       22-Oct-2011.) $)
    nfovd $p |- ( ph -> F/_ x ( A F B ) ) $=
      wph vx cA cB cF co cA cB cop cF cfv cA cB cF df-ov wph vx cA cB cop cF
      nfovd.3 wph vx cA cB nfovd.2 nfovd.4 nfopd nffvd nfcxfrd $.
  $}

  ${
    nfov.1 $e |- F/_ x A $.
    nfov.2 $e |- F/_ x F $.
    nfov.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for operation value.  (Contributed by
       NM, 4-May-2004.) $)
    nfov $p |- F/_ x ( A F B ) $=
      vx cA cB cF co wnfc wtru vx cA cB cF vx cA wnfc wtru nfov.1 a1i vx cF
      wnfc wtru nfov.2 a1i vx cB wnfc wtru nfov.3 a1i nfovd trud $.
  $}

  ${
    $d a ph r s t w $.  $d a r s t w x $.  $d a r s t w y $.  $d a r s t w z $.
    $( The law of concretion.  Special case of Theorem 9.5 of [Quine] p. 61.
       (Contributed by Mario Carneiro, 20-Mar-2013.) $)
    oprabid $p |- ( <. <. x , y >. , z >. e.
        { <. <. x , y >. , z >. | ph } <-> ph ) $=
      vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex wph vw
      vx cv vy cv cop vz cv cop wph vx vy vz coprab vx cv vy cv cop vz cv opex
      vw cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex wph vw cv va cv vt cv cop wceq va cv vt cv
      cop vx cv vy cv cop vz cv cop wceq wa vt wex va wex vw cv vx cv vy cv cop
      vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex
      vx wex wph wi vw cv vx cv vy cv cop vz cv cop wceq vw cv va cv vt cv cop
      wceq va cv vt cv cop vx cv vy cv cop vz cv cop wceq wa vt wex va wex va
      vt vw cv vx cv vy cv cop vz cv vx cv vy cv opex vz vex eqvinop biimpi vw
      cv va cv vt cv cop wceq va cv vt cv cop vx cv vy cv cop vz cv cop wceq wa
      vw cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex wph wi wi va vt vw cv va cv vt cv cop wceq vw
      cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex wph wi wi va cv vt cv cop vx cv vy cv cop vz
      cv cop wceq vw cv va cv vt cv cop wceq vw cv vx cv vy cv cop vz cv cop
      wceq va cv vx cv vy cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq wph
      wa vz wex vy wex vx wex wph wi vw cv va cv vt cv cop wceq vw cv vx cv vy
      cv cop vz cv cop wceq va cv vt cv cop vx cv vy cv cop vz cv cop wceq va
      cv vx cv vy cv cop wceq vw cv va cv vt cv cop vx cv vy cv cop vz cv cop
      eqeq1 va cv vt cv vx cv vy cv cop vz cv va vex vt vex opth1 syl6bi va cv
      vx cv vy cv cop wceq vw cv va cv vt cv cop wceq vw cv vx cv vy cv cop vz
      cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx
      wex wph wi va cv vx cv vy cv cop wceq va cv vr cv vs cv cop wceq vr cv vs
      cv cop vx cv vy cv cop wceq wa vs wex vr wex vw cv va cv vt cv cop wceq
      vw cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex wph wi wi wi vr vs va cv vx cv vy cv vx vex
      vy vex eqvinop va cv vr cv vs cv cop wceq vr cv vs cv cop vx cv vy cv cop
      wceq wa vw cv va cv vt cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq
      vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex wph wi
      wi wi vr vs va cv vr cv vs cv cop wceq vw cv va cv vt cv cop wceq vw cv
      vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq wph
      wa vz wex vy wex vx wex wph wi wi wi vr cv vs cv cop vx cv vy cv cop wceq
      va cv vr cv vs cv cop wceq vw cv va cv vt cv cop wceq vw cv vr cv vs cv
      cop vt cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv
      cop vz cv cop wceq wph wa vz wex vy wex vx wex wph wi wi va cv vr cv vs
      cv cop wceq va cv vt cv cop vr cv vs cv cop vt cv cop vw cv va cv vr cv
      vs cv cop vt cv opeq1 eqeq2d vw cv vr cv vs cv cop vt cv cop wceq vw cv
      vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop vz cv cop wceq wph
      wa vz wex vy wex vx wex wph wi wi vx cv vy cv cop vz cv cop vr cv vs cv
      cop vt cv cop wceq vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop
      wceq wph wa vz wex vy wex vx wex wph wi wi vx cv vy cv cop vz cv cop vr
      cv vs cv cop vt cv cop wceq wph wa vz wex vy wex vx wex vx cv vr cv wceq
      vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex wa vy wex wa vx wex vx cv
      vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq wph vx cv vy cv cop vz
      cv cop vr cv vs cv cop vt cv cop wceq wph wa vz wex vy wex vx wex vx cv
      vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa wa vz wex vy wex
      vx wex vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex
      wa vy wex wa vx wex vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop
      wceq wph wa vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa
      wa vx vy vz vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq wph
      wa vx cv vr cv wceq vy cv vs cv wceq wa vz cv vt cv wceq wa wph wa vx cv
      vr cv wceq vy cv vs cv wceq wa vz cv vt cv wceq wph wa wa vx cv vr cv
      wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa wa vx cv vy cv cop vz cv
      cop vr cv vs cv cop vt cv cop wceq vx cv vr cv wceq vy cv vs cv wceq wa
      vz cv vt cv wceq wa wph vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv
      cop wceq vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq w3a vx cv vr
      cv wceq vy cv vs cv wceq wa vz cv vt cv wceq wa vx cv vy cv vr cv vs cv
      vz cv vt cv vx vex vy vex vz vex otth2 vx cv vr cv wceq vy cv vs cv wceq
      vz cv vt cv wceq df-3an bitri anbi1i vx cv vr cv wceq vy cv vs cv wceq wa
      vz cv vt cv wceq wph anass vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv
      wceq wph wa anass 3bitri 3exbii vx cv vr cv wceq vy cv vs cv wceq vz cv
      vt cv wceq wph wa wa wa vz wex vy wex vx wex vx cv vr cv wceq vy cv vs cv
      wceq vz cv vt cv wceq wph wa wa vz wex wa vy wex vx wex vx cv vr cv wceq
      vy cv vs cv wceq vz cv vt cv wceq wph wa wa vz wex vy wex wa vx wex vx cv
      vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex wa vy wex wa
      vx wex vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa wa vz
      wex vx wex vy wex vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph
      wa wa vz wex wa vx wex vy wex vx cv vr cv wceq vy cv vs cv wceq vz cv vt
      cv wceq wph wa wa wa vz wex vy wex vx wex vx cv vr cv wceq vy cv vs cv
      wceq vz cv vt cv wceq wph wa wa vz wex wa vy wex vx wex vx cv vr cv wceq
      vy cv vs cv wceq vz cv vt cv wceq wph wa wa wa vz wex vx wex vx cv vr cv
      wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa vz wex wa vx wex vy vx
      cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa vx vz vx cv vz
      cv wceq vx wal wn vz vx cv vr cv vx vz nfcvf2 vx cv vz cv wceq vx wal wn
      vz vr cv nfcvd nfeqd exdistrf eximi vx cv vr cv wceq vy cv vs cv wceq vz
      cv vt cv wceq wph wa wa wa vz wex vx vy excom vx cv vr cv wceq vy cv vs
      cv wceq vz cv vt cv wceq wph wa wa vz wex wa vx vy excom 3imtr4i vx cv vr
      cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa wa vz wex vx vy vx cv vy
      cv wceq vx wal wn vy vx cv vr cv vx vy nfcvf2 vx cv vy cv wceq vx wal wn
      vy vr cv nfcvd nfeqd exdistrf vx cv vr cv wceq vy cv vs cv wceq vz cv vt
      cv wceq wph wa wa vz wex vy wex wa vx cv vr cv wceq vy cv vs cv wceq vz
      cv vt cv wceq wph wa vz wex wa vy wex wa vx vy cv vs cv wceq vz cv vt cv
      wceq wph wa wa vz wex vy wex vy cv vs cv wceq vz cv vt cv wceq wph wa vz
      wex wa vy wex vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa
      vy vz vy cv vz cv wceq vy wal wn vz vy cv vs cv vy vz nfcvf2 vy cv vz cv
      wceq vy wal wn vz vs cv nfcvd nfeqd exdistrf anim2i eximi 3syl sylbi vx
      cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex wa vy wex
      wa vx wex vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq wph vx
      cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq vx cv vr cv wceq vy
      cv vs cv wceq vz cv vt cv wceq w3a vx cv vr cv wceq vy cv vs cv wceq vz
      cv vt cv wceq wph wa vz wex wa vy wex wa vx wex wph vx cv vy cv vr cv vs
      cv vz cv vt cv vx vex vy vex vz vex otth2 vx cv vr cv wceq vy cv vs cv
      wceq vz cv vt cv wceq wph wa vz wex wa vy wex wa vx wex vx cv vr cv wceq
      vy cv vs cv wceq vz cv vt cv wceq wph vx cv vr cv wceq vy cv vs cv wceq
      vz cv vt cv wceq wph wa vz wex wa vy wex wa vx wex vx cv vr cv wceq vy cv
      vs cv wceq vz cv vt cv wceq wph wa vz wex wa vy wex vy cv vs cv wceq vz
      cv vt cv wceq wph wi wi vx cv vr cv wceq vx weu vx cv vr cv wceq vy cv vs
      cv wceq vz cv vt cv wceq wph wa vz wex wa vy wex wa vx wex vx cv vr cv
      wceq vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex wa vy wex wi vx vr
      euequ1 vx cv vr cv wceq vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex
      wa vy wex vx eupick mpan vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex
      wa vy wex vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex vz cv vt cv
      wceq wph wi vy cv vs cv wceq vy weu vy cv vs cv wceq vz cv vt cv wceq wph
      wa vz wex wa vy wex vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex wi vy
      vs euequ1 vy cv vs cv wceq vz cv vt cv wceq wph wa vz wex vy eupick mpan
      vz cv vt cv wceq vz weu vz cv vt cv wceq wph wa vz wex vz cv vt cv wceq
      wph wi vz vt euequ1 vz cv vt cv wceq wph vz eupick mpan syl6 syl6 3impd
      syl5bi com12 syl5 vw cv vr cv vs cv cop vt cv cop wceq vw cv vx cv vy cv
      cop vz cv cop wceq vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop
      wceq vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex wph
      wi vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq wph wa vz wex
      vy wex vx wex wph wi vw cv vr cv vs cv cop vt cv cop wceq vw cv vx cv vy
      cv cop vz cv cop wceq vr cv vs cv cop vt cv cop vx cv vy cv cop vz cv cop
      wceq vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq vw cv vr cv
      vs cv cop vt cv cop vx cv vy cv cop vz cv cop eqeq1 vr cv vs cv cop vt cv
      cop vx cv vy cv cop vz cv cop eqcom syl6bb vw cv vr cv vs cv cop vt cv
      cop wceq vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex
      vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq wph wa vz wex vy
      wex vx wex wph vw cv vr cv vs cv cop vt cv cop wceq vw cv vx cv vy cv cop
      vz cv cop wceq wph wa vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop
      wceq wph wa vx vy vz vw cv vr cv vs cv cop vt cv cop wceq vw cv vx cv vy
      cv cop vz cv cop wceq vx cv vy cv cop vz cv cop vr cv vs cv cop vt cv cop
      wceq wph vw cv vr cv vs cv cop vt cv cop wceq vw cv vx cv vy cv cop vz cv
      cop wceq vr cv vs cv cop vt cv cop vx cv vy cv cop vz cv cop wceq vx cv
      vy cv cop vz cv cop vr cv vs cv cop vt cv cop wceq vw cv vr cv vs cv cop
      vt cv cop vx cv vy cv cop vz cv cop eqeq1 vr cv vs cv cop vt cv cop vx cv
      vy cv cop vz cv cop eqcom syl6bb anbi1d 3exbidv imbi1d imbi12d mpbiri
      syl6bi adantr exlimivv sylbi com3l mpdd adantr exlimivv mpcom vw cv vx cv
      vy cv cop vz cv cop wceq wph vw cv vx cv vy cv cop vz cv cop wceq wph wa
      vz wex vy wex vx wex vw cv vx cv vy cv cop vz cv cop wceq wph wa vw cv vx
      cv vy cv cop vz cv cop wceq wph wa vz wex vw cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vw cv vx cv vy cv cop vz cv cop wceq wph wa vz
      wex vy wex vx wex vw cv vx cv vy cv cop vz cv cop wceq wph wa vz 19.8a vw
      cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy 19.8a vw cv vx cv vy
      cv cop vz cv cop wceq wph wa vz wex vy wex vx 19.8a 3syl ex impbid wph vx
      vy vz vw df-oprab elab2 $.
  $}

  $( The result of an operation is a set.  (Contributed by NM, 13-Mar-1995.) $)
  ovex $p |- ( A F B ) e. _V $=
    cA cB cF co cA cB cop cF cfv cvv cA cB cF df-ov cA cB cop cF fvex eqeltri
    $.

  $( The result of an operation value is always a subset of the union of the
     range.  (Contributed by Mario Carneiro, 12-Jan-2017.) $)
  ovssunirn $p |- ( X F Y ) C_ U. ran F $=
    cX cY cF co cX cY cop cF cfv cF crn cuni cX cY cF df-ov cF cX cY cop
    fvssunirn eqsstri $.

  ${
    ovprc1.1 $e |- Rel dom F $.
    $( The value of an operation when the one of the arguments is a proper
       class.  Note: this theorem is dependent on our particular definitions of
       operation value, function value, and ordered pair.  (Contributed by
       Mario Carneiro, 26-Apr-2015.) $)
    ovprc $p |- ( -. ( A e. _V /\ B e. _V ) -> ( A F B ) = (/) ) $=
      cA cvv wcel cB cvv wcel wa wn cA cB cF co cA cB cop cF cfv c0 cA cB cF
      df-ov cA cvv wcel cB cvv wcel wa wn cA cB cop cF cdm wcel wn cA cB cop cF
      cfv c0 wceq cA cB cop cF cdm wcel cA cvv wcel cB cvv wcel wa cA cB cop cF
      cdm wcel cA cB cF cdm wbr cA cvv wcel cB cvv wcel wa cA cB cF cdm df-br
      cF cdm wrel cA cB cF cdm wbr cA cvv wcel cB cvv wcel wa ovprc1.1 cA cB cF
      cdm brrelex12 mpan sylbir con3i cA cB cop cF ndmfv syl syl5eq $.

    $( The value of an operation when the first argument is a proper class.
       (Contributed by NM, 16-Jun-2004.) $)
    ovprc1 $p |- ( -. A e. _V -> ( A F B ) = (/) ) $=
      cA cvv wcel wn cA cvv wcel cB cvv wcel wa wn cA cB cF co c0 wceq cA cvv
      wcel cB cvv wcel wa cA cvv wcel cA cvv wcel cB cvv wcel simpl con3i cA cB
      cF ovprc1.1 ovprc syl $.

    $( The value of an operation when the second argument is a proper class.
       (Contributed by Mario Carneiro, 26-Apr-2015.) $)
    ovprc2 $p |- ( -. B e. _V -> ( A F B ) = (/) ) $=
      cB cvv wcel wn cA cvv wcel cB cvv wcel wa wn cA cB cF co c0 wceq cA cvv
      wcel cB cvv wcel wa cB cvv wcel cA cvv wcel cB cvv wcel simpr con3i cA cB
      cF ovprc1.1 ovprc syl $.

    $( Reverse closure for an operation value.  (Contributed by Mario Carneiro,
       5-May-2015.) $)
    ovrcl $p |- ( C e. ( A F B ) -> ( A e. _V /\ B e. _V ) ) $=
      cC cA cB cF co wcel cA cB cF co c0 wceq cA cvv wcel cB cvv wcel wa cA cB
      cF co cC n0i cA cB cF ovprc1.1 ovprc nsyl2 $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z C $.  $d y z D $.  $d y z F $.
    $d x y z $.
    $( Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.)  (Proof shortened by Mario Carneiro, 5-Dec-2016.) $)
    csbovg $p |- ( A e. D -> [_ A / x ]_ ( B F C ) =
           ( [_ A / x ]_ B [_ A / x ]_ F [_ A / x ]_ C ) ) $=
      vx vy cv cB cC cF co csb vx vy cv cB csb vx vy cv cC csb vx vy cv cF csb
      co wceq vx cA cB cC cF co csb vx cA cB csb vx cA cC csb vx cA cF csb co
      wceq vy cA cD vy cv cA wceq vx vy cv cB cC cF co csb vx cA cB cC cF co
      csb vx vy cv cB csb vx vy cv cC csb vx vy cv cF csb co vx cA cB csb vx cA
      cC csb vx cA cF csb co vx vy cv cA cB cC cF co csbeq1 vy cv cA wceq vx vy
      cv cB csb vx cA cB csb vx vy cv cC csb vx cA cC csb vx vy cv cF csb vx cA
      cF csb vx vy cv cA cF csbeq1 vx vy cv cA cB csbeq1 vx vy cv cA cC csbeq1
      oveq123d eqeq12d vx vy cv cB cC cF co vx vy cv cB csb vx vy cv cC csb vx
      vy cv cF csb co vy vex vx vx vy cv cB csb vx vy cv cC csb vx vy cv cF csb
      vx vy cv cB nfcsb1v vx vy cv cF nfcsb1v vx vy cv cC nfcsb1v nfov vx cv vy
      cv wceq cB vx vy cv cB csb cC vx vy cv cC csb cF vx vy cv cF csb vx vy cv
      cF csbeq1a vx vy cv cB csbeq1a vx vy cv cC csbeq1a oveq123d csbief vtoclg
      $.
  $}

  ${
    $d y A $.  $d y C $.  $d y D $.  $d x y F $.
    $( Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) $)
    csbov12g $p |- ( A e. D ->
                 [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F [_ A / x ]_ C ) ) $=
      cA cD wcel vx cA cB cC cF co csb vx cA cB csb vx cA cC csb vx cA cF csb
      co vx cA cB csb vx cA cC csb cF co vx cA cB cC cD cF csbovg cA cD wcel vx
      cA cF csb cF vx cA cB csb vx cA cC csb vx cA cF cD csbconstg oveqd eqtrd
      $.
  $}

  ${
    $d y A $.  $d x y C $.  $d y D $.  $d x y F $.
    $( Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) $)
    csbov1g $p |- ( A e. D ->
                  [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F C ) ) $=
      cA cD wcel vx cA cB cC cF co csb vx cA cB csb vx cA cC csb cF co vx cA cB
      csb cC cF co vx cA cB cC cD cF csbov12g cA cD wcel vx cA cC csb cC vx cA
      cB csb cF vx cA cC cD csbconstg oveq2d eqtrd $.
  $}

  ${
    $d y A $.  $d x y B $.  $d y D $.  $d x y F $.
    $( Move class substitution in and out of an operation.  (Contributed by NM,
       12-Nov-2005.) $)
    csbov2g $p |- ( A e. D ->
                  [_ A / x ]_ ( B F C ) = ( B F [_ A / x ]_ C ) ) $=
      cA cD wcel vx cA cB cC cF co csb vx cA cB csb vx cA cC csb cF co cB vx cA
      cC csb cF co vx cA cB cC cD cF csbov12g cA cD wcel vx cA cB csb cB vx cA
      cC csb cF vx cA cB cD csbconstg oveq1d eqtrd $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x y C $.  $d y D $.  $d x y F $.  $d x y S $.
    $( A frequently used special case of ~ rspc2ev for operation values.
       (Contributed by NM, 21-Mar-2007.) $)
    rspceov $p |- ( ( C e. A /\ D e. B /\ S = ( C F D ) ) ->
                 E. x e. A E. y e. B S = ( x F y ) ) $=
      cS vx cv vy cv cF co wceq cS cC cD cF co wceq cS cC vy cv cF co wceq vx
      vy cC cD cA cB vx cv cC wceq vx cv vy cv cF co cC vy cv cF co cS vx cv cC
      vy cv cF oveq1 eqeq2d vy cv cD wceq cC vy cv cF co cC cD cF co cS vy cv
      cD cC cF oveq2 eqeq2d rspc2ev $.
  $}

  ${
    $( Equivalence of operation value and ordered triple membership, analogous
       to ~ fnopfvb .  (Contributed by NM, 17-Dec-2008.)  (Revised by Mario
       Carneiro, 28-Apr-2015.) $)
    fnotovb $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) ->
                   ( ( C F D ) = R <-> <. C , D , R >. e. F ) ) $=
      cF cA cB cxp wfn cC cA wcel cD cB wcel w3a cC cD cop cF cfv cR wceq cC cD
      cop cR cop cF wcel cC cD cF co cR wceq cC cD cR cotp cF wcel cF cA cB cxp
      wfn cC cA wcel cD cB wcel cC cD cop cF cfv cR wceq cC cD cop cR cop cF
      wcel wb cC cA wcel cD cB wcel wa cF cA cB cxp wfn cC cD cop cA cB cxp
      wcel cC cD cop cF cfv cR wceq cC cD cop cR cop cF wcel wb cC cD cA cB
      opelxpi cA cB cxp cC cD cop cR cF fnopfvb sylan2 3impb cC cD cF co cC cD
      cop cF cfv cR cC cD cF df-ov eqeq1i cC cD cR cotp cC cD cop cR cop cF cC
      cD cR df-ot eleq1i 3bitr4g $.
  $}

  ${
    $d x z w v $.  $d y z w v $.  $d w ph v $.
    $( Class abstraction for operations in terms of class abstraction of
       ordered pairs.  (Contributed by NM, 12-Mar-1995.) $)
    dfoprab2 $p |- { <. <. x , y >. , z >. | ph } =
                   { <. w , z >. | E. x E. y ( w = <. x , y >. /\ ph ) } $=
      vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex vv cab
      vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa vy wex vx
      wex wa vz wex vw wex vv cab wph vx vy vz coprab vw cv vx cv vy cv cop
      wceq wph wa vy wex vx wex vw vz copab vv cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vx wex vv cv vw cv vz cv cop wceq vw cv vx cv
      vy cv cop wceq wph wa vy wex vx wex wa vz wex vw wex vv vv cv vw cv vz cv
      cop wceq vw cv vx cv vy cv cop wceq wph wa wa vy wex vx wex vw wex vz wex
      vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa wa vy wex vx
      wex vz wex vw wex vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy
      wex vx wex vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa
      vy wex vx wex wa vz wex vw wex vv cv vw cv vz cv cop wceq vw cv vx cv vy
      cv cop wceq wph wa wa vy wex vx wex vz vw excom vv cv vw cv vz cv cop
      wceq vw cv vx cv vy cv cop wceq wph wa wa vy wex vx wex vw wex vz wex vv
      cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa wa vw wex vz
      wex vy wex vx wex vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy
      wex vx wex vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa
      wa vz vw vx vy exrot4 vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop
      wceq wph wa wa vw wex vv cv vx cv vy cv cop vz cv cop wceq wph wa vx vy
      vz vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa wa vw wex
      vv cv vx cv vy cv cop vz cv cop wceq wph wa vw cv vx cv vy cv cop wceq wa
      vw wex vv cv vx cv vy cv cop vz cv cop wceq wph wa vv cv vw cv vz cv cop
      wceq vw cv vx cv vy cv cop wceq wph wa wa vv cv vx cv vy cv cop vz cv cop
      wceq wph wa vw cv vx cv vy cv cop wceq wa vw vv cv vw cv vz cv cop wceq
      vw cv vx cv vy cv cop wceq wa wph wa vv cv vx cv vy cv cop vz cv cop wceq
      vw cv vx cv vy cv cop wceq wa wph wa vv cv vw cv vz cv cop wceq vw cv vx
      cv vy cv cop wceq wph wa wa vv cv vx cv vy cv cop vz cv cop wceq wph wa
      vw cv vx cv vy cv cop wceq wa vv cv vw cv vz cv cop wceq vw cv vx cv vy
      cv cop wceq wa vv cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop
      wceq wa wph vw cv vx cv vy cv cop wceq vv cv vw cv vz cv cop wceq vv cv
      vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop wceq vw cv vz cv cop
      vx cv vy cv cop vz cv cop vv cv vw cv vx cv vy cv cop vz cv opeq1 eqeq2d
      pm5.32ri anbi1i vv cv vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq wph
      anass vv cv vx cv vy cv cop vz cv cop wceq vw cv vx cv vy cv cop wceq wph
      an32 3bitr3i exbii vv cv vx cv vy cv cop vz cv cop wceq wph wa vw cv vx
      cv vy cv cop wceq wa vw wex vv cv vx cv vy cv cop vz cv cop wceq wph wa
      vw cv vx cv vy cv cop wceq vw wex vw vx cv vy cv cop vx cv vy cv opex
      isseti vv cv vx cv vy cv cop vz cv cop wceq wph wa vw cv vx cv vy cv cop
      wceq vw 19.42v mpbiran2 bitri 3exbii bitri vv cv vw cv vz cv cop wceq vw
      cv vx cv vy cv cop wceq wph wa wa vy wex vx wex vv cv vw cv vz cv cop
      wceq vw cv vx cv vy cv cop wceq wph wa vy wex vx wex wa vw vz vv cv vw cv
      vz cv cop wceq vw cv vx cv vy cv cop wceq wph wa vx vy 19.42vv 2exbii
      3bitr3i abbii wph vx vy vz vv df-oprab vw cv vx cv vy cv cop wceq wph wa
      vy wex vx wex vw vz vv df-opab 3eqtr4i $.

    $( An operation class abstraction is a relation.  (Contributed by NM,
       16-Jun-2004.) $)
    reloprab $p |- Rel { <. <. x , y >. , z >. | ph } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw vz wph vx vy vz coprab
      wph vx vy vz vw dfoprab2 relopabi $.
  $}

$(
  @{
    @d x y z w v @.  @d ph v @.
    dfoprab2f.1 @e |- ( ph -> A. w ph ) @.
    @( Class abstraction for operations in terms of class abstraction of
       ordered pairs.  This is a version of ~ dfoprab2 with bound-variable
       hypothesis instead of distinct variable requirement. @)
    dfoprab2f @p |- { <. <. x , y >. , z >. | ph } =
                   { <. w , z >. | E. x E. y ( w = <. x , y >. /\ ph ) } @=
      ( vv coprab cv cop wceq wa wex copab dfoprab2 ax-17 hban hbex weq
      eqeq1 anbi1d 2exbidv cbvopab1
      eqtri ) ABCDHGIZBICIJZKZALZCMZBMZGDNEIZUFKZALZCMBM
      ZEDNABCDGOUJUNGDEUIEBUHECUGAEUGEPFQRRUNGPGESZUHUMBCUOUGULAUEUKUFTUAUBUCUD
      @.
  @}
$)

  ${
    $d w x $.  $d w y $.  $d w z $.  $d w ph $.
    $( The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 25-Apr-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) $)
    nfoprab1 $p |- F/_ x { <. <. x , y >. , z >. | ph } $=
      vx wph vx vy vz coprab vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex
      vy wex vx wex vw cab wph vx vy vz vw df-oprab vw cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vx wex vx vw vw cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vx nfe1 nfab nfcxfr $.

    $( The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 25-Apr-1995.)  (Revised by David Abernethy,
       30-Jul-2012.) $)
    nfoprab2 $p |- F/_ y { <. <. x , y >. , z >. | ph } $=
      vy wph vx vy vz coprab vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex
      vy wex vx wex vw cab wph vx vy vz vw df-oprab vw cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vx wex vy vw vw cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vy vx vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy nfe1 nfex nfab nfcxfr $.

    $( The abstraction variables in an operation class abstraction are not
       free.  (Contributed by NM, 22-Aug-2013.) $)
    nfoprab3 $p |- F/_ z { <. <. x , y >. , z >. | ph } $=
      vz wph vx vy vz coprab vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex
      vy wex vx wex vw cab wph vx vy vz vw df-oprab vw cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vx wex vz vw vw cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vz vx vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vz vy vw cv vx cv vy cv cop vz cv cop wceq wph wa vz nfe1
      nfex nfex nfab nfcxfr $.
  $}

  ${
    $d v w x $.  $d v w y $.  $d v w z $.  $d v ph $.
    nfoprab.1 $e |- F/ w ph $.
    $( Bound-variable hypothesis builder for an operation class abstraction.
       (Contributed by NM, 22-Aug-2013.) $)
    nfoprab $p |- F/_ w { <. <. x , y >. , z >. | ph } $=
      vw wph vx vy vz coprab vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex
      vy wex vx wex vv cab wph vx vy vz vv df-oprab vv cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vx wex vw vv vv cv vx cv vy cv cop vz cv
      cop wceq wph wa vz wex vy wex vw vx vv cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vw vy vv cv vx cv vy cv cop vz cv cop wceq wph wa vw vz vv
      cv vx cv vy cv cop vz cv cop wceq wph vw vv cv vx cv vy cv cop vz cv cop
      wceq vw nfv nfoprab.1 nfan nfex nfex nfex nfab nfcxfr $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d w ph $.  $d w ps $.  $d w ch $.
    oprabbid.1 $e |- F/ x ph $.
    oprabbid.2 $e |- F/ y ph $.
    oprabbid.3 $e |- F/ z ph $.
    oprabbid.4 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal operation class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.)  (Revised by Mario Carneiro,
       24-Jun-2014.) $)
    oprabbid $p |- ( ph ->
           { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } ) $=
      wph vw cv vx cv vy cv cop vz cv cop wceq wps wa vz wex vy wex vx wex vw
      cab vw cv vx cv vy cv cop vz cv cop wceq wch wa vz wex vy wex vx wex vw
      cab wps vx vy vz coprab wch vx vy vz coprab wph vw cv vx cv vy cv cop vz
      cv cop wceq wps wa vz wex vy wex vx wex vw cv vx cv vy cv cop vz cv cop
      wceq wch wa vz wex vy wex vx wex vw wph vw cv vx cv vy cv cop vz cv cop
      wceq wps wa vz wex vy wex vw cv vx cv vy cv cop vz cv cop wceq wch wa vz
      wex vy wex vx oprabbid.1 wph vw cv vx cv vy cv cop vz cv cop wceq wps wa
      vz wex vw cv vx cv vy cv cop vz cv cop wceq wch wa vz wex vy oprabbid.2
      wph vw cv vx cv vy cv cop vz cv cop wceq wps wa vw cv vx cv vy cv cop vz
      cv cop wceq wch wa vz oprabbid.3 wph wps wch vw cv vx cv vy cv cop vz cv
      cop wceq oprabbid.4 anbi2d exbid exbid exbid abbidv wps vx vy vz vw
      df-oprab wch vx vy vz vw df-oprab 3eqtr4g $.
  $}

  ${
    $d x z w ph $.  $d y z w ph $.  $d w ps $.  $d w ch $.
    oprabbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal operation class abstractions (deduction
       rule).  (Contributed by NM, 21-Feb-2004.) $)
    oprabbidv $p |- ( ph ->
           { <. <. x , y >. , z >. | ps } = { <. <. x , y >. , z >. | ch } ) $=
      wph wps wch vx vy vz wph vx nfv wph vy nfv wph vz nfv oprabbidv.1
      oprabbid $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d w ph $.  $d w ps $.
    oprabbii.1 $e |- ( ph <-> ps ) $.
    $( Equivalent wff's yield equal operation class abstractions.  (Contributed
       by NM, 28-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    oprabbii $p |- { <. <. x , y >. , z >. | ph }
                 = { <. <. x , y >. , z >. | ps } $=
      vw cv vw cv wceq wph vx vy vz coprab wps vx vy vz coprab wceq vw cv eqid
      vw cv vw cv wceq wph wps vx vy vz wph wps wb vw cv vw cv wceq oprabbii.1
      a1i oprabbidv ax-mp $.
  $}

  ${
    $d ph w $.  $d ps w $.  $d x w $.  $d y w $.  $d z w $.
    $( Equivalence of ordered pair abstraction subclass and implication.
       Compare ~ ssopab2 .  (Contributed by FL, 6-Nov-2013.)  (Proof shortened
       by Mario Carneiro, 11-Dec-2016.) $)
    ssoprab2 $p |- ( A. x A. y A. z ( ph -> ps ) ->
        { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } ) $=
      wph wps wi vz wal vy wal vx wal vw cv vx cv vy cv cop vz cv cop wceq wph
      wa vz wex vy wex vx wex vw cab vw cv vx cv vy cv cop vz cv cop wceq wps
      wa vz wex vy wex vx wex vw cab wph vx vy vz coprab wps vx vy vz coprab
      wph wps wi vz wal vy wal vx wal vw cv vx cv vy cv cop vz cv cop wceq wph
      wa vz wex vy wex vx wex vw cv vx cv vy cv cop vz cv cop wceq wps wa vz
      wex vy wex vx wex vw wph wps wi vz wal vy wal vx wal vw cv vx cv vy cv
      cop vz cv cop wceq wph wa vz wex vy wex vw cv vx cv vy cv cop vz cv cop
      wceq wps wa vz wex vy wex wi vx wal vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex vw cv vx cv vy cv cop vz cv cop wceq wps wa
      vz wex vy wex vx wex wi wph wps wi vz wal vy wal vw cv vx cv vy cv cop vz
      cv cop wceq wph wa vz wex vy wex vw cv vx cv vy cv cop vz cv cop wceq wps
      wa vz wex vy wex wi vx wph wps wi vz wal vy wal vw cv vx cv vy cv cop vz
      cv cop wceq wph wa vz wex vw cv vx cv vy cv cop vz cv cop wceq wps wa vz
      wex wi vy wal vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex
      vw cv vx cv vy cv cop vz cv cop wceq wps wa vz wex vy wex wi wph wps wi
      vz wal vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vw cv vx cv vy
      cv cop vz cv cop wceq wps wa vz wex wi vy wph wps wi vz wal vw cv vx cv
      vy cv cop vz cv cop wceq wph wa vw cv vx cv vy cv cop vz cv cop wceq wps
      wa wi vz wal vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vw cv vx
      cv vy cv cop vz cv cop wceq wps wa vz wex wi wph wps wi vw cv vx cv vy cv
      cop vz cv cop wceq wph wa vw cv vx cv vy cv cop vz cv cop wceq wps wa wi
      vz wph wps wi wph wps vw cv vx cv vy cv cop vz cv cop wceq wph wps wi id
      anim2d alimi vw cv vx cv vy cv cop vz cv cop wceq wph wa vw cv vx cv vy
      cv cop vz cv cop wceq wps wa vz exim syl alimi vw cv vx cv vy cv cop vz
      cv cop wceq wph wa vz wex vw cv vx cv vy cv cop vz cv cop wceq wps wa vz
      wex vy exim syl alimi vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex
      vy wex vw cv vx cv vy cv cop vz cv cop wceq wps wa vz wex vy wex vx exim
      syl ss2abdv wph vx vy vz vw df-oprab wps vx vy vz vw df-oprab 3sstr4g $.
  $}

  $( Equivalence of ordered pair abstraction subclass and implication.  Compare
     ~ ssopab2b .  (Contributed by FL, 6-Nov-2013.)  (Proof shortened by Mario
     Carneiro, 11-Dec-2016.) $)
  ssoprab2b $p |- ( { <. <. x , y >. , z >. | ph } C_
    { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph -> ps ) ) $=
    wph vx vy vz coprab wps vx vy vz coprab wss wph wps wi vz wal vy wal vx wal
    wph vx vy vz coprab wps vx vy vz coprab wss wph wps wi vz wal vy wal vx vx
    wph vx vy vz coprab wps vx vy vz coprab wph vx vy vz nfoprab1 wps vx vy vz
    nfoprab1 nfss wph vx vy vz coprab wps vx vy vz coprab wss wph wps wi vz wal
    vy vy wph vx vy vz coprab wps vx vy vz coprab wph vx vy vz nfoprab2 wps vx
    vy vz nfoprab2 nfss wph vx vy vz coprab wps vx vy vz coprab wss wph wps wi
    vz vz wph vx vy vz coprab wps vx vy vz coprab wph vx vy vz nfoprab3 wps vx
    vy vz nfoprab3 nfss wph vx vy vz coprab wps vx vy vz coprab wss vx cv vy cv
    cop vz cv cop wph vx vy vz coprab wcel vx cv vy cv cop vz cv cop wps vx vy
    vz coprab wcel wph wps wph vx vy vz coprab wps vx vy vz coprab vx cv vy cv
    cop vz cv cop ssel wph vx vy vz oprabid wps vx vy vz oprabid 3imtr3g alrimi
    alrimi alrimi wph wps vx vy vz ssoprab2 impbii $.

  $( Equivalence of ordered pair abstraction subclass and biconditional.
     Compare ~ eqopab2b .  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
  eqoprab2b $p |- ( { <. <. x , y >. , z >. | ph } =
    { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph <-> ps ) ) $=
    wph vx vy vz coprab wps vx vy vz coprab wss wps vx vy vz coprab wph vx vy
    vz coprab wss wa wph wps wi vz wal vy wal vx wal wps wph wi vz wal vy wal
    vx wal wa wph vx vy vz coprab wps vx vy vz coprab wceq wph wps wb vz wal vy
    wal vx wal wph vx vy vz coprab wps vx vy vz coprab wss wph wps wi vz wal vy
    wal vx wal wps vx vy vz coprab wph vx vy vz coprab wss wps wph wi vz wal vy
    wal vx wal wph wps vx vy vz ssoprab2b wps wph vx vy vz ssoprab2b anbi12i
    wph vx vy vz coprab wps vx vy vz coprab eqss wph wps wb vz wal vy wal vx
    wal wph wps wi vz wal vy wal wps wph wi vz wal vy wal wa vx wal wph wps wi
    vz wal vy wal vx wal wps wph wi vz wal vy wal vx wal wa wph wps wb vz wal
    vy wal wph wps wi vz wal vy wal wps wph wi vz wal vy wal wa vx wph wps vy
    vz 2albiim albii wph wps wi vz wal vy wal wps wph wi vz wal vy wal vx 19.26
    bitri 3bitr4i $.

  ${
    $d x y z A $.  $d y z B $.  $d x y z D $.  $d y z E $.  $d z C $.
    $d z F $.
    $( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.)  (Revised by Mario Carneiro, 19-Mar-2015.) $)
    mpt2eq123 $p |- ( ( A = D /\ A. x e. A ( B = E /\ A. y e. B C = F ) ) ->
                 ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $=
      cA cD wceq cB cE wceq cC cF wceq vy cB wral wa vx cA wral wa vx cv cA
      wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab vx cv cD wcel vy
      cv cE wcel wa vz cv cF wceq wa vx vy vz coprab vx vy cA cB cC cmpt2 vx vy
      cD cE cF cmpt2 cA cD wceq cB cE wceq cC cF wceq vy cB wral wa vx cA wral
      wa vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx cv cD wcel vy cv cE
      wcel wa vz cv cF wceq wa vx vy vz cA cD wceq cB cE wceq cC cF wceq vy cB
      wral wa vx cA wral vx cA cD wceq vx nfv cB cE wceq cC cF wceq vy cB wral
      wa vx cA nfra1 nfan cA cD wceq cB cE wceq cC cF wceq vy cB wral wa vx cA
      wral vy cA cD wceq vy nfv cB cE wceq cC cF wceq vy cB wral wa vy vx cA vy
      cA nfcv cB cE wceq cC cF wceq vy cB wral vy cB cE wceq vy nfv cC cF wceq
      vy cB nfra1 nfan nfral nfan cA cD wceq cB cE wceq cC cF wceq vy cB wral
      wa vx cA wral wa vz nfv cA cD wceq cB cE wceq cC cF wceq vy cB wral wa vx
      cA wral wa vx cv cA wcel vy cv cB wcel vz cv cC wceq wa wa vx cv cD wcel
      vy cv cE wcel vz cv cF wceq wa wa vx cv cA wcel vy cv cB wcel wa vz cv cC
      wceq wa vx cv cD wcel vy cv cE wcel wa vz cv cF wceq wa cB cE wceq cC cF
      wceq vy cB wral wa vx cA wral vx cv cA wcel vy cv cB wcel vz cv cC wceq
      wa wa vx cv cA wcel vy cv cE wcel vz cv cF wceq wa wa cA cD wceq vx cv cD
      wcel vy cv cE wcel vz cv cF wceq wa wa cB cE wceq cC cF wceq vy cB wral
      wa vx cA wral vx cv cA wcel vy cv cB wcel vz cv cC wceq wa vy cv cE wcel
      vz cv cF wceq wa cB cE wceq cC cF wceq vy cB wral wa vx cA wral vx cv cA
      wcel cB cE wceq cC cF wceq vy cB wral wa vy cv cB wcel vz cv cC wceq wa
      vy cv cE wcel vz cv cF wceq wa wb cB cE wceq cC cF wceq vy cB wral wa vx
      cA rsp cC cF wceq vy cB wral vy cv cB wcel vz cv cC wceq wa vy cv cB wcel
      vz cv cF wceq wa cB cE wceq vy cv cE wcel vz cv cF wceq wa cC cF wceq vy
      cB wral vy cv cB wcel vz cv cC wceq vz cv cF wceq cC cF wceq vy cB wral
      vy cv cB wcel cC cF wceq vz cv cC wceq vz cv cF wceq wb cC cF wceq vy cB
      rsp cC cF vz cv eqeq2 syl6 pm5.32d cB cE wceq vy cv cB wcel vy cv cE wcel
      vz cv cF wceq cB cE vy cv eleq2 anbi1d sylan9bbr syl6 pm5.32d cA cD wceq
      vx cv cA wcel vx cv cD wcel vy cv cE wcel vz cv cF wceq wa cA cD vx cv
      eleq2 anbi1d sylan9bbr vx cv cA wcel vy cv cB wcel vz cv cC wceq anass vx
      cv cD wcel vy cv cE wcel vz cv cF wceq anass 3bitr4g oprabbid vx vy vz cA
      cB cC df-mpt2 vx vy vz cD cE cF df-mpt2 3eqtr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.
    $( An equality theorem for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
    mpt2eq12 $p |- ( ( A = C /\ B = D ) ->
                 ( x e. A , y e. B |-> E ) = ( x e. C , y e. D |-> E ) ) $=
      cB cD wceq cA cC wceq cB cD wceq cE cE wceq vy cB wral wa vx cA wral vx
      vy cA cB cE cmpt2 vx vy cC cD cE cmpt2 wceq cB cD wceq cB cD wceq cE cE
      wceq vy cB wral wa vx cA cB cD wceq cE cE wceq vy cB wral cE cE wceq vy
      cB cE eqid rgenw jctr ralrimivw vx vy cA cB cE cC cD cE mpt2eq123 sylan2
      $.
  $}

  ${
    $d z A $.  $d z B $.  $d z C $.  $d z D $.  $d z E $.  $d x z ph $.
    $d z F $.  $d y z ph $.
    mpt2eq123dv.1 $e |- ( ph -> A = D ) $.
    ${
      mpt2eq123dva.2 $e |- ( ( ph /\ x e. A ) -> B = E ) $.
      mpt2eq123dva.3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> C = F ) $.
      $( An equality deduction for the maps to notation.  (Contributed by Mario
         Carneiro, 26-Jan-2017.) $)
      mpt2eq123dva $p |- ( ph
              -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $=
        wph vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab vx
        cv cD wcel vy cv cE wcel wa vz cv cF wceq wa vx vy vz coprab vx vy cA
        cB cC cmpt2 vx vy cD cE cF cmpt2 wph vx cv cA wcel vy cv cB wcel wa vz
        cv cC wceq wa vx cv cD wcel vy cv cE wcel wa vz cv cF wceq wa vx vy vz
        wph vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx cv cA wcel vy cv
        cB wcel wa vz cv cF wceq wa vx cv cD wcel vy cv cE wcel wa vz cv cF
        wceq wa wph vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv cF wceq
        wph vx cv cA wcel vy cv cB wcel wa wa cC cF vz cv mpt2eq123dva.3 eqeq2d
        pm5.32da wph vx cv cA wcel vy cv cB wcel wa vx cv cD wcel vy cv cE wcel
        wa vz cv cF wceq wph vx cv cA wcel vy cv cB wcel wa vx cv cA wcel vy cv
        cE wcel wa vx cv cD wcel vy cv cE wcel wa wph vx cv cA wcel vy cv cB
        wcel vy cv cE wcel wph vx cv cA wcel wa cB cE vy cv mpt2eq123dva.2
        eleq2d pm5.32da wph vx cv cA wcel vx cv cD wcel vy cv cE wcel wph cA cD
        vx cv mpt2eq123dv.1 eleq2d anbi1d bitrd anbi1d bitrd oprabbidv vx vy vz
        cA cB cC df-mpt2 vx vy vz cD cE cF df-mpt2 3eqtr4g $.
    $}

    mpt2eq123dv.2 $e |- ( ph -> B = E ) $.
    mpt2eq123dv.3 $e |- ( ph -> C = F ) $.
    $( An equality deduction for the maps to notation.  (Contributed by NM,
       12-Sep-2011.) $)
    mpt2eq123dv $p |- ( ph
            -> ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) ) $=
      wph vx vy cA cB cC cD cE cF mpt2eq123dv.1 wph cB cE wceq vx cv cA wcel
      mpt2eq123dv.2 adantr wph cC cF wceq vx cv cA wcel vy cv cB wcel wa
      mpt2eq123dv.3 adantr mpt2eq123dva $.
  $}

  ${
    mpt2eq123i.1 $e |- A = D $.
    mpt2eq123i.2 $e |- B = E $.
    mpt2eq123i.3 $e |- C = F $.
    $( An equality inference for the maps to notation.  (Contributed by NM,
       15-Jul-2013.) $)
    mpt2eq123i $p |- ( x e. A , y e. B |-> C ) = ( x e. D , y e. E |-> F ) $=
      vx vy cA cB cC cmpt2 vx vy cD cE cF cmpt2 wceq wtru vx vy cA cB cC cD cE
      cF cA cD wceq wtru mpt2eq123i.1 a1i cB cE wceq wtru mpt2eq123i.2 a1i cC
      cF wceq wtru mpt2eq123i.3 a1i mpt2eq123dv trud $.
  $}

  ${
    $d x z ph $.  $d y z ph $.  $d z A $.  $d z B $.  $d z C $.  $d z D $.
    mpt2eq3dva.1 $e |- ( ( ph /\ x e. A /\ y e. B ) -> C = D ) $.
    $( Slightly more general equality inference for the maps to notation.
       (Contributed by NM, 17-Oct-2013.) $)
    mpt2eq3dva $p |- ( ph -> ( x e. A , y e. B |-> C )
              = ( x e. A , y e. B |-> D ) ) $=
      wph vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab vx cv
      cA wcel vy cv cB wcel wa vz cv cD wceq wa vx vy vz coprab vx vy cA cB cC
      cmpt2 vx vy cA cB cD cmpt2 wph vx cv cA wcel vy cv cB wcel wa vz cv cC
      wceq wa vx cv cA wcel vy cv cB wcel wa vz cv cD wceq wa vx vy vz wph vx
      cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv cD wceq wph vx cv cA wcel
      vy cv cB wcel wa wa cC cD vz cv wph vx cv cA wcel vy cv cB wcel cC cD
      wceq mpt2eq3dva.1 3expb eqeq2d pm5.32da oprabbidv vx vy vz cA cB cC
      df-mpt2 vx vy vz cA cB cD df-mpt2 3eqtr4g $.
  $}

  ${
    mpt2eq3ia.1 $e |- ( ( x e. A /\ y e. B ) -> C = D ) $.
    $( An equality inference for the maps to notation.  (Contributed by Mario
       Carneiro, 16-Dec-2013.) $)
    mpt2eq3ia $p |- ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) $=
      vx vy cA cB cC cmpt2 vx vy cA cB cD cmpt2 wceq wtru vx vy cA cB cC cD vx
      cv cA wcel vy cv cB wcel cC cD wceq wtru mpt2eq3ia.1 3adant1 mpt2eq3dva
      trud $.
  $}

  ${
    $d z A $.  $d z B $.  $d z C $.  $d z x $.  $d z y $.
    $( Bound-variable hypothesis builder for an operation in maps-to notation.
       (Contributed by NM, 27-Aug-2013.) $)
    nfmpt21 $p |- F/_ x ( x e. A , y e. B |-> C ) $=
      vx vx vy cA cB cC cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa
      vx vy vz coprab vx vy vz cA cB cC df-mpt2 vx cv cA wcel vy cv cB wcel wa
      vz cv cC wceq wa vx vy vz nfoprab1 nfcxfr $.

    $( Bound-variable hypothesis builder for an operation in maps-to notation.
       (Contributed by NM, 27-Aug-2013.) $)
    nfmpt22 $p |- F/_ y ( x e. A , y e. B |-> C ) $=
      vy vx vy cA cB cC cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa
      vx vy vz coprab vx vy vz cA cB cC df-mpt2 vx cv cA wcel vy cv cB wcel wa
      vz cv cC wceq wa vx vy vz nfoprab2 nfcxfr $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w A $.  $d w B $.  $d w C $.
    nfmpt2.1 $e |- F/_ z A $.
    nfmpt2.2 $e |- F/_ z B $.
    nfmpt2.3 $e |- F/_ z C $.
    $( Bound-variable hypothesis builder for the maps-to notation.
       (Contributed by NM, 20-Feb-2013.) $)
    nfmpt2 $p |- F/_ z ( x e. A , y e. B |-> C ) $=
      vz vx vy cA cB cC cmpt2 vx cv cA wcel vy cv cB wcel wa vw cv cC wceq wa
      vx vy vw coprab vx vy vw cA cB cC df-mpt2 vx cv cA wcel vy cv cB wcel wa
      vw cv cC wceq wa vx vy vw vz vx cv cA wcel vy cv cB wcel wa vw cv cC wceq
      vz vx cv cA wcel vy cv cB wcel vz vz vx cA nfmpt2.1 nfcri vz vy cB
      nfmpt2.2 nfcri nfan vz vw cv cC nfmpt2.3 nfeq2 nfan nfoprab nfcxfr $.
  $}

  ${
    $d x y z $.
    $( Two ways to state the domain of an operation.  (Contributed by FL,
       24-Jan-2010.) $)
    oprab4 $p |-
      { <. <. x , y >. , z >. | ( <. x , y >. e. ( A X. B ) /\ ph ) } =
        { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $=
      vx cv vy cv cop cA cB cxp wcel wph wa vx cv cA wcel vy cv cB wcel wa wph
      wa vx vy vz vx cv vy cv cop cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa
      wph vx cv vy cv cA cB opelxp anbi1i oprabbii $.
  $}

  ${
    $d x y z w v $.  $d v ph $.  $d v ps $.
    cbvoprab1.1 $e |- F/ w ph $.
    cbvoprab1.2 $e |- F/ x ps $.
    cbvoprab1.3 $e |- ( x = w -> ( ph <-> ps ) ) $.
    $( Rule used to change first bound variable in an operation abstraction,
       using implicit substitution.  (Contributed by NM, 20-Dec-2008.)
       (Revised by Mario Carneiro, 5-Dec-2016.) $)
    cbvoprab1 $p |- { <. <. x , y >. , z >. | ph }
                  = { <. <. w , y >. , z >. | ps } $=
      vv cv vx cv vy cv cop wceq wph wa vy wex vx wex vv vz copab vv cv vw cv
      vy cv cop wceq wps wa vy wex vw wex vv vz copab wph vx vy vz coprab wps
      vw vy vz coprab vv cv vx cv vy cv cop wceq wph wa vy wex vx wex vv cv vw
      cv vy cv cop wceq wps wa vy wex vw wex vv vz vv cv vx cv vy cv cop wceq
      wph wa vy wex vv cv vw cv vy cv cop wceq wps wa vy wex vx vw vv cv vx cv
      vy cv cop wceq wph wa vw vy vv cv vx cv vy cv cop wceq wph vw vv cv vx cv
      vy cv cop wceq vw nfv cbvoprab1.1 nfan nfex vv cv vw cv vy cv cop wceq
      wps wa vx vy vv cv vw cv vy cv cop wceq wps vx vv cv vw cv vy cv cop wceq
      vx nfv cbvoprab1.2 nfan nfex vx cv vw cv wceq vv cv vx cv vy cv cop wceq
      wph wa vv cv vw cv vy cv cop wceq wps wa vy vx cv vw cv wceq vv cv vx cv
      vy cv cop wceq vv cv vw cv vy cv cop wceq wph wps vx cv vw cv wceq vx cv
      vy cv cop vw cv vy cv cop vv cv vx cv vw cv vy cv opeq1 eqeq2d
      cbvoprab1.3 anbi12d exbidv cbvex opabbii wph vx vy vz vv dfoprab2 wps vw
      vy vz vv dfoprab2 3eqtr4i $.
  $}

  ${
    $d v w x y z $.  $d ph v $.  $d ps v $.
    cbvoprab2.1 $e |- F/ w ph $.
    cbvoprab2.2 $e |- F/ y ps $.
    cbvoprab2.3 $e |- ( y = w -> ( ph <-> ps ) ) $.
    $( Change the second bound variable in an operation abstraction.
       (Contributed by Jeff Madsen, 11-Jun-2010.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    cbvoprab2 $p |- { <. <. x , y >. , z >. | ph } =
                    { <. <. x , w >. , z >. | ps } $=
      vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex vv cab
      vv cv vx cv vw cv cop vz cv cop wceq wps wa vz wex vw wex vx wex vv cab
      wph vx vy vz coprab wps vx vw vz coprab vv cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vx wex vv cv vx cv vw cv cop vz cv cop wceq wps
      wa vz wex vw wex vx wex vv vv cv vx cv vy cv cop vz cv cop wceq wph wa vz
      wex vy wex vv cv vx cv vw cv cop vz cv cop wceq wps wa vz wex vw wex vx
      vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vv cv vx cv vw cv cop
      vz cv cop wceq wps wa vz wex vy vw vv cv vx cv vy cv cop vz cv cop wceq
      wph wa vw vz vv cv vx cv vy cv cop vz cv cop wceq wph vw vv cv vx cv vy
      cv cop vz cv cop wceq vw nfv cbvoprab2.1 nfan nfex vv cv vx cv vw cv cop
      vz cv cop wceq wps wa vy vz vv cv vx cv vw cv cop vz cv cop wceq wps vy
      vv cv vx cv vw cv cop vz cv cop wceq vy nfv cbvoprab2.2 nfan nfex vy cv
      vw cv wceq vv cv vx cv vy cv cop vz cv cop wceq wph wa vv cv vx cv vw cv
      cop vz cv cop wceq wps wa vz vy cv vw cv wceq vv cv vx cv vy cv cop vz cv
      cop wceq vv cv vx cv vw cv cop vz cv cop wceq wph wps vy cv vw cv wceq vx
      cv vy cv cop vz cv cop vx cv vw cv cop vz cv cop vv cv vy cv vw cv wceq
      vx cv vy cv cop vx cv vw cv cop vz cv vy cv vw cv vx cv opeq2 opeq1d
      eqeq2d cbvoprab2.3 anbi12d exbidv cbvex exbii abbii wph vx vy vz vv
      df-oprab wps vx vw vz vv df-oprab 3eqtr4i $.
  $}

  ${
    $d x y z w v u $.  $d u ph $.  $d u ps $.
    cbvoprab12.1 $e |- F/ w ph $.
    cbvoprab12.2 $e |- F/ v ph $.
    cbvoprab12.3 $e |- F/ x ps $.
    cbvoprab12.4 $e |- F/ y ps $.
    cbvoprab12.5 $e |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) ) $.
    $( Rule used to change first two bound variables in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       21-Feb-2004.)  (Proof shortened by Andrew Salmon, 22-Oct-2011.) $)
    cbvoprab12 $p |- { <. <. x , y >. , z >. | ph }
                   = { <. <. w , v >. , z >. | ps } $=
      vu cv vx cv vy cv cop wceq wph wa vy wex vx wex vu vz copab vu cv vw cv
      vv cv cop wceq wps wa vv wex vw wex vu vz copab wph vx vy vz coprab wps
      vw vv vz coprab vu cv vx cv vy cv cop wceq wph wa vy wex vx wex vu cv vw
      cv vv cv cop wceq wps wa vv wex vw wex vu vz vu cv vx cv vy cv cop wceq
      wph wa vu cv vw cv vv cv cop wceq wps wa vx vy vw vv vu cv vx cv vy cv
      cop wceq wph vw vu cv vx cv vy cv cop wceq vw nfv cbvoprab12.1 nfan vu cv
      vx cv vy cv cop wceq wph vv vu cv vx cv vy cv cop wceq vv nfv
      cbvoprab12.2 nfan vu cv vw cv vv cv cop wceq wps vx vu cv vw cv vv cv cop
      wceq vx nfv cbvoprab12.3 nfan vu cv vw cv vv cv cop wceq wps vy vu cv vw
      cv vv cv cop wceq vy nfv cbvoprab12.4 nfan vx cv vw cv wceq vy cv vv cv
      wceq wa vu cv vx cv vy cv cop wceq vu cv vw cv vv cv cop wceq wph wps vx
      cv vw cv wceq vy cv vv cv wceq wa vx cv vy cv cop vw cv vv cv cop vu cv
      vx cv vy cv vw cv vv cv opeq12 eqeq2d cbvoprab12.5 anbi12d cbvex2 opabbii
      wph vx vy vz vu dfoprab2 wps vw vv vz vu dfoprab2 3eqtr4i $.
  $}

  ${
    $d x y z w v u $.  $d u w v ph $.  $d u x y ps $.
    cbvoprab12v.1 $e |- ( ( x = w /\ y = v ) -> ( ph <-> ps ) ) $.
    $( Rule used to change first two bound variables in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       8-Oct-2004.) $)
    cbvoprab12v $p |- { <. <. x , y >. , z >. | ph }
                    = { <. <. w , v >. , z >. | ps } $=
      wph wps vx vy vz vw vv wph vw nfv wph vv nfv wps vx nfv wps vy nfv
      cbvoprab12v.1 cbvoprab12 $.
  $}

  ${
    $d x z w v $.  $d y z w v $.  $d v ph $.  $d v ps $.
    cbvoprab3.1 $e |- F/ w ph $.
    cbvoprab3.2 $e |- F/ z ps $.
    cbvoprab3.3 $e |- ( z = w -> ( ph <-> ps ) ) $.
    $( Rule used to change the third bound variable in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       22-Aug-2013.) $)
    cbvoprab3 $p |- { <. <. x , y >. , z >. | ph } =
                     { <. <. x , y >. , w >. | ps } $=
      vv cv vx cv vy cv cop wceq wph wa vy wex vx wex vv vz copab vv cv vx cv
      vy cv cop wceq wps wa vy wex vx wex vv vw copab wph vx vy vz coprab wps
      vx vy vw coprab vv cv vx cv vy cv cop wceq wph wa vy wex vx wex vv cv vx
      cv vy cv cop wceq wps wa vy wex vx wex vv vz vw vv cv vx cv vy cv cop
      wceq wph wa vy wex vw vx vv cv vx cv vy cv cop wceq wph wa vw vy vv cv vx
      cv vy cv cop wceq wph vw vv cv vx cv vy cv cop wceq vw nfv cbvoprab3.1
      nfan nfex nfex vv cv vx cv vy cv cop wceq wps wa vy wex vz vx vv cv vx cv
      vy cv cop wceq wps wa vz vy vv cv vx cv vy cv cop wceq wps vz vv cv vx cv
      vy cv cop wceq vz nfv cbvoprab3.2 nfan nfex nfex vz cv vw cv wceq vv cv
      vx cv vy cv cop wceq wph wa vv cv vx cv vy cv cop wceq wps wa vx vy vz cv
      vw cv wceq wph wps vv cv vx cv vy cv cop wceq cbvoprab3.3 anbi2d 2exbidv
      cbvopab2 wph vx vy vz vv dfoprab2 wps vx vy vw vv dfoprab2 3eqtr4i $.
  $}

  ${
    $d x z w v $.  $d y z w v $.  $d w v ph $.  $d z v ps $.
    cbvoprab3v.1 $e |- ( z = w -> ( ph <-> ps ) ) $.
    $( Rule used to change the third bound variable in an operation
       abstraction, using implicit substitution.  (Contributed by NM,
       8-Oct-2004.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    cbvoprab3v $p |- { <. <. x , y >. , z >. | ph } =
                     { <. <. x , y >. , w >. | ps } $=
      wph wps vx vy vz vw wph vw nfv wps vz nfv cbvoprab3v.1 cbvoprab3 $.
  $}

  ${
    $d u v w x y z $.  $d u w x y z A $.  $d u w B $.  $d u C $.  $d u y D $.
    $d u E $.
    cbvmpt2x.1 $e |- F/_ z B $.
    cbvmpt2x.2 $e |- F/_ x D $.
    cbvmpt2x.3 $e |- F/_ z C $.
    cbvmpt2x.4 $e |- F/_ w C $.
    cbvmpt2x.5 $e |- F/_ x E $.
    cbvmpt2x.6 $e |- F/_ y E $.
    cbvmpt2x.7 $e |- ( x = z -> B = D ) $.
    cbvmpt2x.8 $e |- ( ( x = z /\ y = w ) -> C = E ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  This version of ~ cbvmpt2 allows ` B ` to be a function
       of ` x ` .  (Contributed by NM, 29-Dec-2014.) $)
    cbvmpt2x $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. D |-> E ) $=
      vx cv cA wcel vy cv cB wcel wa vu cv cC wceq wa vx vy vu coprab vz cv cA
      wcel vw cv cD wcel wa vu cv cE wceq wa vz vw vu coprab vx vy cA cB cC
      cmpt2 vz vw cA cD cE cmpt2 vx cv cA wcel vy cv cB wcel wa vu cv cC wceq
      wa vz cv cA wcel vw cv cD wcel wa vu cv cE wceq wa vx vy vu vz vw vx cv
      cA wcel vy cv cB wcel wa vu cv cC wceq vz vx cv cA wcel vy cv cB wcel vz
      vx cv cA wcel vz nfv vz vy cB cbvmpt2x.1 nfcri nfan vz vu cv cC
      cbvmpt2x.3 nfeq2 nfan vx cv cA wcel vy cv cB wcel wa vu cv cC wceq vw vx
      cv cA wcel vy cv cB wcel vw vx cv cA wcel vw nfv vw vy cB vw cB nfcv
      nfcri nfan vw vu cv cC cbvmpt2x.4 nfeq2 nfan vz cv cA wcel vw cv cD wcel
      wa vu cv cE wceq vx vz cv cA wcel vw cv cD wcel vx vz cv cA wcel vx nfv
      vx vw cD cbvmpt2x.2 nfcri nfan vx vu cv cE cbvmpt2x.5 nfeq2 nfan vz cv cA
      wcel vw cv cD wcel wa vu cv cE wceq vy vz cv cA wcel vw cv cD wcel wa vy
      nfv vy vu cv cE cbvmpt2x.6 nfeq2 nfan vx cv vz cv wceq vy cv vw cv wceq
      wa vx cv cA wcel vy cv cB wcel wa vz cv cA wcel vw cv cD wcel wa vu cv cC
      wceq vu cv cE wceq vx cv vz cv wceq vy cv vw cv wceq wa vx cv cA wcel vz
      cv cA wcel vy cv cB wcel vw cv cD wcel vx cv vz cv wceq vx cv cA wcel vz
      cv cA wcel wb vy cv vw cv wceq vx cv vz cv cA eleq1 adantr vx cv vz cv
      wceq vy cv cB wcel vy cv cD wcel vy cv vw cv wceq vw cv cD wcel vx cv vz
      cv wceq cB cD vy cv cbvmpt2x.7 eleq2d vy cv vw cv cD eleq1 sylan9bb
      anbi12d vx cv vz cv wceq vy cv vw cv wceq wa cC cE vu cv cbvmpt2x.8
      eqeq2d anbi12d cbvoprab12 vx vy vu cA cB cC df-mpt2 vz vw vu cA cD cE
      df-mpt2 3eqtr4i $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.
    cbvmpt2.1 $e |- F/_ z C $.
    cbvmpt2.2 $e |- F/_ w C $.
    cbvmpt2.3 $e |- F/_ x D $.
    cbvmpt2.4 $e |- F/_ y D $.
    cbvmpt2.5 $e |- ( ( x = z /\ y = w ) -> C = D ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  (Contributed by NM, 17-Dec-2013.) $)
    cbvmpt2 $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D ) $=
      vx vy vz vw cA cB cC cB cD vz cB nfcv vx cB nfcv cbvmpt2.1 cbvmpt2.2
      cbvmpt2.3 cbvmpt2.4 vx cv vz cv wceq cB eqidd cbvmpt2.5 cbvmpt2x $.
  $}

  ${
    $d v w x y z A $.  $d v w x y z B $.  $d v w z C $.  $d v x y D $.
    cbvmpt2v.1 $e |- ( x = z -> C = E ) $.
    cbvmpt2v.2 $e |- ( y = w -> E = D ) $.
    $( Rule to change the bound variable in a maps-to function, using implicit
       substitution.  With a longer proof analogous to ~ cbvmpt , some distinct
       variable requirements could be eliminated.  (Contributed by NM,
       11-Jun-2013.) $)
    cbvmpt2v $p |- ( x e. A , y e. B |-> C ) = ( z e. A , w e. B |-> D ) $=
      vx vy vz vw cA cB cC cD vz cC nfcv vw cC nfcv vx cD nfcv vy cD nfcv vx cv
      vz cv wceq vy cv vw cv wceq cC cE cD cbvmpt2v.1 cbvmpt2v.2 sylan9eq
      cbvmpt2 $.
  $}

  ${
    elimdelov.1 $e |- ( ph -> C e. ( A F B ) ) $.
    elimdelov.2 $e |- Z e. ( X F Y ) $.
    $( Eliminate a hypothesis which is a predicate expressing membership in the
       result of an operator (deduction version).  See ~ ghomgrplem for an
       example of its use.  (Contributed by Paul Chapman, 25-Mar-2008.) $)
    elimdelov $p |- if ( ph , C , Z ) e.
                     ( if ( ph , A , X ) F if ( ph , B , Y ) ) $=
      wph wph cC cZ cif wph cA cX cif wph cB cY cif cF co wcel wph wph cC cZ
      cif cA cB cF co wph cA cX cif wph cB cY cif cF co wph wph cC cZ cif cC cA
      cB cF co wph cC cZ iftrue elimdelov.1 eqeltrd wph wph cA cX cif cA wph cB
      cY cif cB cF wph cA cX iftrue wph cB cY iftrue oveq12d eleqtrrd wph wn
      wph cC cZ cif cX cY cF co wph cA cX cif wph cB cY cif cF co wph wn wph cC
      cZ cif cZ cX cY cF co wph cC cZ iffalse elimdelov.2 syl6eqel wph wn wph
      cA cX cif cX wph cB cY cif cY cF wph cA cX iffalse wph cB cY iffalse
      oveq12d eleqtrrd pm2.61i $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d w ph $.
    $( The domain of an operation class abstraction.  (Contributed by NM,
       17-Mar-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    dmoprab $p |- dom { <. <. x , y >. , z >. | ph } =
                  { <. x , y >. | E. z ph } $=
      wph vx vy vz coprab cdm vw cv vx cv vy cv cop wceq wph wa vy wex vx wex
      vw vz copab cdm vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vz wex vw
      cab wph vz wex vx vy copab wph vx vy vz coprab vw cv vx cv vy cv cop wceq
      wph wa vy wex vx wex vw vz copab wph vx vy vz vw dfoprab2 dmeqi vw cv vx
      cv vy cv cop wceq wph wa vy wex vx wex vw vz dmopab vw cv vx cv vy cv cop
      wceq wph wa vy wex vx wex vz wex vw cab vw cv vx cv vy cv cop wceq wph vz
      wex wa vy wex vx wex vw cab wph vz wex vx vy copab vw cv vx cv vy cv cop
      wceq wph wa vy wex vx wex vz wex vw cv vx cv vy cv cop wceq wph vz wex wa
      vy wex vx wex vw vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vz wex
      vw cv vx cv vy cv cop wceq wph wa vz wex vy wex vx wex vw cv vx cv vy cv
      cop wceq wph vz wex wa vy wex vx wex vw cv vx cv vy cv cop wceq wph wa vz
      vx vy exrot3 vw cv vx cv vy cv cop wceq wph wa vz wex vw cv vx cv vy cv
      cop wceq wph vz wex wa vx vy vw cv vx cv vy cv cop wceq wph vz 19.42v
      2exbii bitri abbii wph vz wex vx vy vw df-opab eqtr4i 3eqtri $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( The domain of an operation class abstraction.  (Contributed by NM,
       24-Aug-1995.) $)
    dmoprabss $p |- dom { <. <. x , y >. , z >. |
           ( ( x e. A /\ y e. B ) /\ ph ) } C_ ( A X. B ) $=
      vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz coprab cdm vx cv cA wcel
      vy cv cB wcel wa wph wa vz wex vx vy copab cA cB cxp vx cv cA wcel vy cv
      cB wcel wa wph wa vx vy vz dmoprab vx cv cA wcel vy cv cB wcel wa wph wa
      vz wex vx vy copab vx cv cA wcel vy cv cB wcel wa wph vz wex wa vx vy
      copab cA cB cxp vx cv cA wcel vy cv cB wcel wa wph wa vz wex vx cv cA
      wcel vy cv cB wcel wa wph vz wex wa vx vy vx cv cA wcel vy cv cB wcel wa
      wph vz 19.42v opabbii wph vz wex vx vy cA cB opabssxp eqsstri eqsstri $.
  $}

  ${
    $d x z w $.  $d y z w $.  $d w ph $.
    $( The range of an operation class abstraction.  (Contributed by NM,
       30-Aug-2004.)  (Revised by David Abernethy, 19-Apr-2013.) $)
    rnoprab $p |- ran { <. <. x , y >. , z >. | ph } =
                  { z | E. x E. y ph } $=
      wph vx vy vz coprab crn vw cv vx cv vy cv cop wceq wph wa vy wex vx wex
      vw vz copab crn vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw wex vz
      cab wph vy wex vx wex vz cab wph vx vy vz coprab vw cv vx cv vy cv cop
      wceq wph wa vy wex vx wex vw vz copab wph vx vy vz vw dfoprab2 rneqi vw
      cv vx cv vy cv cop wceq wph wa vy wex vx wex vw vz rnopab vw cv vx cv vy
      cv cop wceq wph wa vy wex vx wex vw wex wph vy wex vx wex vz vw cv vx cv
      vy cv cop wceq wph wa vy wex vx wex vw wex vw cv vx cv vy cv cop wceq wph
      wa vw wex vy wex vx wex wph vy wex vx wex vw cv vx cv vy cv cop wceq wph
      wa vw vx vy exrot3 vw cv vx cv vy cv cop wceq wph wa vw wex wph vx vy vw
      cv vx cv vy cv cop wceq wph wa vw wex vw cv vx cv vy cv cop wceq vw wex
      wph vw vx cv vy cv cop vx cv vy cv opex isseti vw cv vx cv vy cv cop wceq
      wph vw 19.41v mpbiran 2exbii bitri abbii 3eqtri $.
  $}

  ${
    $d A y $.  $d x y z $.
    $( The range of a restricted operation class abstraction.  (Contributed by
       Scott Fenton, 21-Mar-2012.) $)
    rnoprab2 $p |- ran { <. <. x , y >. , z >. |
                          ( ( x e. A /\ y e. B ) /\ ph ) } =
                    { z | E. x e. A E. y e. B ph } $=
      vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz coprab crn vx cv cA wcel
      vy cv cB wcel wa wph wa vy wex vx wex vz cab wph vy cB wrex vx cA wrex vz
      cab vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz rnoprab wph vy cB wrex
      vx cA wrex vx cv cA wcel vy cv cB wcel wa wph wa vy wex vx wex vz wph vx
      vy cA cB r2ex abbii eqtr4i $.
  $}

  ${
    $d x y z $.
    $( The domain of an operation class abstraction is a relation.
       (Contributed by NM, 17-Mar-1995.) $)
    reldmoprab $p |- Rel dom { <. <. x , y >. , z >. | ph } $=
      wph vz wex vx vy wph vx vy vz coprab cdm wph vx vy vz dmoprab relopabi $.

    $( Structure of an operation class abstraction.  (Contributed by NM,
       28-Nov-2006.) $)
    oprabss $p |- { <. <. x , y >. , z >. | ph } C_ ( ( _V X. _V ) X. _V ) $=
      wph vx vy vz coprab wph vx vy vz coprab cdm wph vx vy vz coprab crn cxp
      cvv cvv cxp cvv cxp wph vx vy vz coprab wrel wph vx vy vz coprab wph vx
      vy vz coprab cdm wph vx vy vz coprab crn cxp wss wph vx vy vz reloprab
      wph vx vy vz coprab relssdmrn ax-mp wph vx vy vz coprab cdm cvv cvv cxp
      wss wph vx vy vz coprab crn cvv wss wph vx vy vz coprab cdm wph vx vy vz
      coprab crn cxp cvv cvv cxp cvv cxp wss wph vx vy vz coprab cdm wrel wph
      vx vy vz coprab cdm cvv cvv cxp wss wph vx vy vz reldmoprab wph vx vy vz
      coprab cdm df-rel mpbi wph vx vy vz coprab crn ssv wph vx vy vz coprab
      cdm cvv cvv cxp wph vx vy vz coprab crn cvv xpss12 mp2an sstri $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d w ph $.
    $d x y z w ps $.
    eloprabga.1 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    $( The law of concretion for operation class abstraction.  Compare
       ~ elopab .  (Contributed by NM, 14-Sep-1999.)  (Unnecessary distinct
       variable restrictions were removed by David Abernethy, 19-Jun-2012.)
       (Revised by Mario Carneiro, 19-Dec-2013.) $)
    eloprabga $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
       ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> ps ) ) $=
      cA cV wcel cA cvv wcel cB cW wcel cB cvv wcel cC cX wcel cC cvv wcel cA
      cB cop cC cop wph vx vy vz coprab wcel wps wb cA cV elex cB cW elex cC cX
      elex cA cvv wcel cB cvv wcel cC cvv wcel w3a cA cB cop cC cop wph vx vy
      vz coprab wcel wps wb wi vw cA cB cop cC cop cA cB cop cC opex cA cvv
      wcel cB cvv wcel cC cvv wcel w3a vw cv cA cB cop cC cop wceq cA cB cop cC
      cop wph vx vy vz coprab wcel wps wb cA cvv wcel cB cvv wcel cC cvv wcel
      w3a vw cv cA cB cop cC cop wceq wa vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a
      wps wa vz wex vy wex vx wex cA cB cop cC cop wph vx vy vz coprab wcel wps
      cA cvv wcel cB cvv wcel cC cvv wcel w3a vw cv cA cB cop cC cop wceq wa vw
      cv vx cv vy cv cop vz cv cop wceq wph wa vx cv cA wceq vy cv cB wceq vz
      cv cC wceq w3a wps wa vx vy vz cA cvv wcel cB cvv wcel cC cvv wcel w3a vw
      cv cA cB cop cC cop wceq wa vw cv vx cv vy cv cop vz cv cop wceq wph wa
      vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a wph wa vx cv cA wceq vy cv
      cB wceq vz cv cC wceq w3a wps wa cA cvv wcel cB cvv wcel cC cvv wcel w3a
      vw cv cA cB cop cC cop wceq wa vw cv vx cv vy cv cop vz cv cop wceq vx cv
      cA wceq vy cv cB wceq vz cv cC wceq w3a wph cA cvv wcel cB cvv wcel cC
      cvv wcel w3a vw cv cA cB cop cC cop wceq wa vw cv vx cv vy cv cop vz cv
      cop wceq cA cB cop cC cop vx cv vy cv cop vz cv cop wceq vx cv cA wceq vy
      cv cB wceq vz cv cC wceq w3a cA cvv wcel cB cvv wcel cC cvv wcel w3a vw
      cv cA cB cop cC cop wceq wa vw cv cA cB cop cC cop vx cv vy cv cop vz cv
      cop cA cvv wcel cB cvv wcel cC cvv wcel w3a vw cv cA cB cop cC cop wceq
      simpr eqeq1d cA cB cop cC cop vx cv vy cv cop vz cv cop wceq vx cv vy cv
      cop vz cv cop cA cB cop cC cop wceq vx cv cA wceq vy cv cB wceq vz cv cC
      wceq w3a cA cB cop cC cop vx cv vy cv cop vz cv cop eqcom vx cv vy cv cA
      cB vz cv cC vx vex vy vex vz vex otth2 bitri syl6bb anbi1d vx cv cA wceq
      vy cv cB wceq vz cv cC wceq w3a wph wps eloprabga.1 pm5.32i syl6bb
      3exbidv vw cv cA cB cop cC cop wceq vw cv vx cv vy cv cop vz cv cop wceq
      wph wa vz wex vy wex vx wex cA cB cop cC cop wph vx vy vz coprab wcel wb
      cA cvv wcel cB cvv wcel cC cvv wcel w3a vw cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vx wex vw cv wph vx vy vz coprab wcel vw cv cA
      cB cop cC cop wceq cA cB cop cC cop wph vx vy vz coprab wcel vw cv wph vx
      vy vz coprab wcel vw cv vw cv vx cv vy cv cop vz cv cop wceq wph wa vz
      wex vy wex vx wex vw cab wcel vw cv vx cv vy cv cop vz cv cop wceq wph wa
      vz wex vy wex vx wex wph vx vy vz coprab vw cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vx wex vw cab vw cv wph vx vy vz vw df-oprab
      eleq2i vw cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex
      vw abid bitr2i vw cv cA cB cop cC cop wph vx vy vz coprab eleq1 syl5bb
      adantl cA cvv wcel cB cvv wcel cC cvv wcel w3a vx cv cA wceq vy cv cB
      wceq vz cv cC wceq w3a wps wa vz wex vy wex vx wex wps wb vw cv cA cB cop
      cC cop wceq cA cvv wcel cB cvv wcel cC cvv wcel w3a wps vx cv cA wceq vy
      cv cB wceq vz cv cC wceq w3a vz wex vy wex vx wex wps wa vx cv cA wceq vy
      cv cB wceq vz cv cC wceq w3a wps wa vz wex vy wex vx wex cA cvv wcel cB
      cvv wcel cC cvv wcel w3a vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vz
      wex vy wex vx wex wps cA cvv wcel cB cvv wcel cC cvv wcel w3a vx cv cA
      wceq vx wex vy cv cB wceq vy wex vz cv cC wceq vz wex w3a vx cv cA wceq
      vy cv cB wceq vz cv cC wceq w3a vz wex vy wex vx wex cA cvv wcel vx cv cA
      wceq vx wex cB cvv wcel vy cv cB wceq vy wex cC cvv wcel vz cv cC wceq vz
      wex vx cA cvv elisset vy cB cvv elisset vz cC cvv elisset 3anim123i vx cv
      cA wceq vy cv cB wceq vz cv cC wceq vx vy vz eeeanv sylibr biantrurd vx
      cv cA wceq vy cv cB wceq vz cv cC wceq w3a wps vx vy vz 19.41vvv syl6rbbr
      adantr 3bitr3d expcom vtocle syl3an $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d w ph $.
    $d x y z w th $.
    eloprabg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    eloprabg.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    eloprabg.3 $e |- ( z = C -> ( ch <-> th ) ) $.
    $( The law of concretion for operation class abstraction.  Compare
       ~ elopab .  (Contributed by NM, 14-Sep-1999.)  (Revised by David
       Abernethy, 19-Jun-2012.) $)
    eloprabg $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
       ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> th ) ) $=
      wph wth vx vy vz cA cB cC cV cW cX vx cv cA wceq wph wps vy cv cB wceq
      wch vz cv cC wceq wth eloprabg.1 eloprabg.2 eloprabg.3 syl3an9b eloprabga
      $.
  $}

  ${
    $d ph w $.  $d ps w $.  $d x z w $.  $d y z w $.
    ssoprab2i.1 $e |- ( ph -> ps ) $.
    $( Inference of operation class abstraction subclass from implication.
       (Contributed by NM, 11-Nov-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) $)
    ssoprab2i $p |- { <. <. x , y >. , z >. | ph } C_
                    { <. <. x , y >. , z >. | ps } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw vz copab vw cv vx cv
      vy cv cop wceq wps wa vy wex vx wex vw vz copab wph vx vy vz coprab wps
      vx vy vz coprab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw cv vx
      cv vy cv cop wceq wps wa vy wex vx wex vw vz vw cv vx cv vy cv cop wceq
      wph wa vw cv vx cv vy cv cop wceq wps wa vx vy wph wps vw cv vx cv vy cv
      cop wceq ssoprab2i.1 anim2i 2eximi ssopab2i wph vx vy vz vw dfoprab2 wps
      vx vy vz vw dfoprab2 3sstr4i $.
  $}

  ${
    $d x z $.  $d y z $.  $d z C $.
    $( Operation with universal domain in maps-to notation.  (Contributed by
       NM, 16-Aug-2013.) $)
    mpt2v $p |- ( x e. _V , y e. _V |-> C )
                     = { <. <. x , y >. , z >. | z = C } $=
      vx vy cvv cvv cC cmpt2 vx cv cvv wcel vy cv cvv wcel wa vz cv cC wceq wa
      vx vy vz coprab vz cv cC wceq vx vy vz coprab vx vy vz cvv cvv cC df-mpt2
      vz cv cC wceq vx cv cvv wcel vy cv cvv wcel wa vz cv cC wceq wa vx vy vz
      vx cv cvv wcel vy cv cvv wcel wa vz cv cC wceq vx cv cvv wcel vy cv cvv
      wcel vx vex vy vex pm3.2i biantrur oprabbii eqtr4i $.
  $}

  ${
    $d w x y z A $.  $d w y z B $.  $d w x y C $.  $d w z D $.
    mpt2mpt.1 $e |- ( z = <. x , y >. -> C = D ) $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  In this version ` B ( x ) ` is not assumed to be constant
       w.r.t ` x ` .  (Contributed by Mario Carneiro, 29-Dec-2014.) $)
    mpt2mptx $p |- ( z e. U_ x e. A ( { x } X. B ) |-> C ) =
      ( x e. A , y e. B |-> D ) $=
      vz vx cA vx cv csn cB cxp ciun cC cmpt vz cv vx cA vx cv csn cB cxp ciun
      wcel vw cv cC wceq wa vz vw copab vx vy cA cB cD cmpt2 vz vw vx cA vx cv
      csn cB cxp ciun cC df-mpt vx vy cA cB cD cmpt2 vx cv cA wcel vy cv cB
      wcel wa vw cv cD wceq wa vx vy vw coprab vz cv vx cA vx cv csn cB cxp
      ciun wcel vw cv cC wceq wa vz vw copab vx vy vw cA cB cD df-mpt2 vz cv vx
      cA vx cv csn cB cxp ciun wcel vw cv cC wceq wa vz vw copab vz cv vx cv vy
      cv cop wceq vx cv cA wcel vy cv cB wcel wa vw cv cD wceq wa wa vy wex vx
      wex vz vw copab vx cv cA wcel vy cv cB wcel wa vw cv cD wceq wa vx vy vw
      coprab vz cv vx cA vx cv csn cB cxp ciun wcel vw cv cC wceq wa vz cv vx
      cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa vw cv cD wceq wa wa vy
      wex vx wex vz vw vz cv vx cA vx cv csn cB cxp ciun wcel vw cv cC wceq wa
      vz cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wa vy wex vx
      wex vw cv cC wceq wa vz cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB
      wcel wa wa vw cv cC wceq wa vy wex vx wex vz cv vx cv vy cv cop wceq vx
      cv cA wcel vy cv cB wcel wa vw cv cD wceq wa wa vy wex vx wex vz cv vx cA
      vx cv csn cB cxp ciun wcel vz cv vx cv vy cv cop wceq vx cv cA wcel vy cv
      cB wcel wa wa vy wex vx wex vw cv cC wceq vx vy cA cB vz cv eliunxp
      anbi1i vz cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wa vw cv
      cC wceq vx vy 19.41vv vz cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB
      wcel wa wa vw cv cC wceq wa vz cv vx cv vy cv cop wceq vx cv cA wcel vy
      cv cB wcel wa vw cv cD wceq wa wa vx vy vz cv vx cv vy cv cop wceq vx cv
      cA wcel vy cv cB wcel wa wa vw cv cC wceq wa vz cv vx cv vy cv cop wceq
      vx cv cA wcel vy cv cB wcel wa vw cv cC wceq wa wa vz cv vx cv vy cv cop
      wceq vx cv cA wcel vy cv cB wcel wa vw cv cD wceq wa wa vz cv vx cv vy cv
      cop wceq vx cv cA wcel vy cv cB wcel wa vw cv cC wceq anass vz cv vx cv
      vy cv cop wceq vx cv cA wcel vy cv cB wcel wa vw cv cC wceq wa vx cv cA
      wcel vy cv cB wcel wa vw cv cD wceq wa vz cv vx cv vy cv cop wceq vw cv
      cC wceq vw cv cD wceq vx cv cA wcel vy cv cB wcel wa vz cv vx cv vy cv
      cop wceq cC cD vw cv mpt2mpt.1 eqeq2d anbi2d pm5.32i bitri 2exbii 3bitr2i
      opabbii vx cv cA wcel vy cv cB wcel wa vw cv cD wceq wa vx vy vw vz
      dfoprab2 eqtr4i eqtr4i eqtr4i $.

    $d x B $.
    $( Express a two-argument function as a one-argument function, or
       vice-versa.  (Contributed by Mario Carneiro, 17-Dec-2013.)  (Revised by
       Mario Carneiro, 29-Dec-2014.) $)
    mpt2mpt $p |- ( z e. ( A X. B ) |-> C ) = ( x e. A , y e. B |-> D ) $=
      vz vx cA vx cv csn cB cxp ciun cC cmpt vz cA cB cxp cC cmpt vx vy cA cB
      cD cmpt2 vx cA vx cv csn cB cxp ciun cA cB cxp wceq vz vx cA vx cv csn cB
      cxp ciun cC cmpt vz cA cB cxp cC cmpt wceq vx cA cB iunxpconst vz vx cA
      vx cv csn cB cxp ciun cA cB cxp cC mpteq1 ax-mp vx vy vz cA cB cC cD
      mpt2mpt.1 mpt2mptx eqtr3i $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w ph $.
    $( Restriction of an operation class abstraction.  (Contributed by NM,
       10-Feb-2007.) $)
    resoprab $p |- ( { <. <. x , y >. , z >. | ph } |` ( A X. B ) ) =
                  { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B ) /\ ph ) } $=
      vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw vz copab cA cB cxp
      cres vw cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wph wa wa
      vy wex vx wex vw vz copab wph vx vy vz coprab cA cB cxp cres vx cv cA
      wcel vy cv cB wcel wa wph wa vx vy vz coprab vw cv vx cv vy cv cop wceq
      wph wa vy wex vx wex vw vz copab cA cB cxp cres vw cv cA cB cxp wcel vw
      cv vx cv vy cv cop wceq wph wa vy wex vx wex wa vw vz copab vw cv vx cv
      vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wph wa wa vy wex vx wex vw
      vz copab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex vw vz cA cB cxp
      resopab vw cv cA cB cxp wcel vw cv vx cv vy cv cop wceq wph wa vy wex vx
      wex wa vw cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wph wa
      wa vy wex vx wex vw vz vw cv cA cB cxp wcel vw cv vx cv vy cv cop wceq
      wph wa vy wex vx wex wa vw cv cA cB cxp wcel vw cv vx cv vy cv cop wceq
      wph wa wa vy wex vx wex vw cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB
      wcel wa wph wa wa vy wex vx wex vw cv cA cB cxp wcel vw cv vx cv vy cv
      cop wceq wph wa vx vy 19.42vv vw cv cA cB cxp wcel vw cv vx cv vy cv cop
      wceq wph wa wa vw cv vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa
      wph wa wa vx vy vw cv cA cB cxp wcel vw cv vx cv vy cv cop wceq wph wa wa
      vw cv vx cv vy cv cop wceq vw cv cA cB cxp wcel wph wa wa vw cv vx cv vy
      cv cop wceq vx cv cA wcel vy cv cB wcel wa wph wa wa vw cv cA cB cxp wcel
      vw cv vx cv vy cv cop wceq wph an12 vw cv vx cv vy cv cop wceq vw cv cA
      cB cxp wcel wph wa vx cv cA wcel vy cv cB wcel wa wph wa vw cv vx cv vy
      cv cop wceq vw cv cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa wph vw cv
      vx cv vy cv cop wceq vw cv cA cB cxp wcel vx cv vy cv cop cA cB cxp wcel
      vx cv cA wcel vy cv cB wcel wa vw cv vx cv vy cv cop cA cB cxp eleq1 vx
      cv vy cv cA cB opelxp syl6bb anbi1d pm5.32i bitri 2exbii bitr3i opabbii
      eqtri wph vx vy vz coprab vw cv vx cv vy cv cop wceq wph wa vy wex vx wex
      vw vz copab cA cB cxp wph vx vy vz vw dfoprab2 reseq1i vx cv cA wcel vy
      cv cB wcel wa wph wa vx vy vz vw dfoprab2 3eqtr4i $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.  $d D x y z $.  $d E z $.
    $( Restriction of an operator abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    resoprab2 $p |- ( ( C C_ A /\ D C_ B ) -> ( { <. <. x , y >. , z >. |
                  ( ( x e. A /\ y e. B ) /\ ph ) } |` ( C X. D ) ) =
              { <. <. x , y >. , z >. | ( ( x e. C /\ y e. D ) /\ ph ) } ) $=
      cC cA wss cD cB wss wa vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz
      coprab cC cD cxp cres vx cv cC wcel vy cv cD wcel wa vx cv cA wcel vy cv
      cB wcel wa wph wa wa vx vy vz coprab vx cv cC wcel vy cv cD wcel wa wph
      wa vx vy vz coprab vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz cC cD
      resoprab cC cA wss cD cB wss wa vx cv cC wcel vy cv cD wcel wa vx cv cA
      wcel vy cv cB wcel wa wph wa wa vx cv cC wcel vy cv cD wcel wa wph wa vx
      vy vz vx cv cC wcel vy cv cD wcel wa vx cv cA wcel vy cv cB wcel wa wph
      wa wa vx cv cC wcel vy cv cD wcel wa vx cv cA wcel vy cv cB wcel wa wa
      wph wa cC cA wss cD cB wss wa vx cv cC wcel vy cv cD wcel wa wph wa vx cv
      cC wcel vy cv cD wcel wa vx cv cA wcel vy cv cB wcel wa wph anass cC cA
      wss cD cB wss wa vx cv cC wcel vy cv cD wcel wa vx cv cA wcel vy cv cB
      wcel wa wa vx cv cC wcel vy cv cD wcel wa wph vx cv cC wcel vy cv cD wcel
      wa vx cv cA wcel vy cv cB wcel wa wa vx cv cC wcel vx cv cA wcel wa vy cv
      cD wcel vy cv cB wcel wa wa cC cA wss cD cB wss wa vx cv cC wcel vy cv cD
      wcel wa vx cv cC wcel vy cv cD wcel vx cv cA wcel vy cv cB wcel an4 cC cA
      wss vx cv cC wcel vx cv cA wcel wa vx cv cC wcel cD cB wss vy cv cD wcel
      vy cv cB wcel wa vy cv cD wcel cC cA wss vx cv cC wcel vx cv cC wcel vx
      cv cA wcel wa cC cA wss vx cv cC wcel vx cv cA wcel cC cA vx cv ssel
      pm4.71d bicomd cD cB wss vy cv cD wcel vy cv cD wcel vy cv cB wcel wa cD
      cB wss vy cv cD wcel vy cv cB wcel cD cB vy cv ssel pm4.71d bicomd
      bi2anan9 syl5bb anbi1d syl5bbr oprabbidv syl5eq $.

    $( Restriction of the mapping operation.  (Contributed by Mario Carneiro,
       17-Dec-2013.) $)
    resmpt2 $p |- ( ( C C_ A /\ D C_ B ) ->
                    ( ( x e. A , y e. B |-> E ) |` ( C X. D ) ) =
                      ( x e. C , y e. D |-> E ) ) $=
      cC cA wss cD cB wss wa vx cv cA wcel vy cv cB wcel wa vz cv cE wceq wa vx
      vy vz coprab cC cD cxp cres vx cv cC wcel vy cv cD wcel wa vz cv cE wceq
      wa vx vy vz coprab vx vy cA cB cE cmpt2 cC cD cxp cres vx vy cC cD cE
      cmpt2 vz cv cE wceq vx vy vz cA cB cC cD resoprab2 vx vy cA cB cE cmpt2
      vx cv cA wcel vy cv cB wcel wa vz cv cE wceq wa vx vy vz coprab cC cD cxp
      vx vy vz cA cB cE df-mpt2 reseq1i vx vy vz cC cD cE df-mpt2 3eqtr4g $.
  $}

  ${
    $d x y z w $.  $d w ph $.
    $( "At most one" is a sufficient condition for an operation class
       abstraction to be a function.  (Contributed by NM, 28-Aug-2007.) $)
    funoprabg $p |- ( A. x A. y E* z ph ->
                    Fun { <. <. x , y >. , z >. | ph } ) $=
      wph vz wmo vy wal vx wal vw cv vx cv vy cv cop wceq wph wa vy wex vx wex
      vz wmo vw wal wph vx vy vz coprab wfun wph vz wmo vy wal vx wal vw cv vx
      cv vy cv cop wceq wph wa vy wex vx wex vz wmo vw wph vz vx vy vw cv
      mosubopt alrimiv wph vx vy vz coprab wfun vw cv vx cv vy cv cop wceq wph
      wa vy wex vx wex vw vz copab wfun vw cv vx cv vy cv cop wceq wph wa vy
      wex vx wex vz wmo vw wal wph vx vy vz coprab vw cv vx cv vy cv cop wceq
      wph wa vy wex vx wex vw vz copab wph vx vy vz vw dfoprab2 funeqi vw cv vx
      cv vy cv cop wceq wph wa vy wex vx wex vw vz funopab bitr2i sylib $.
  $}

  ${
    $d x y z w $.  $d w ph $.
    funoprab.1 $e |- E* z ph $.
    $( "At most one" is a sufficient condition for an operation class
       abstraction to be a function.  (Contributed by NM, 17-Mar-1995.) $)
    funoprab $p |- Fun { <. <. x , y >. , z >. | ph } $=
      wph vz wmo vy wal vx wal wph vx vy vz coprab wfun wph vz wmo vx vy
      funoprab.1 gen2 wph vx vy vz funoprabg ax-mp $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Functionality and domain of an operation class abstraction.
       (Contributed by NM, 28-Aug-2007.) $)
    fnoprabg $p |- ( A. x A. y ( ph -> E! z ps ) ->
  { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn { <. x , y >. | ph } ) $=
      wph wps vz weu wi vy wal vx wal wph wps wa vx vy vz coprab wfun wph wps
      wa vx vy vz coprab cdm wph vx vy copab wceq wph wps wa vx vy vz coprab
      wph vx vy copab wfn wph wps vz weu wi vy wal vx wal wph wps wa vz wmo vy
      wal vx wal wph wps wa vx vy vz coprab wfun wph wps vz weu wi wph wps wa
      vz wmo vx vy wph wps vz weu wi wph wps vz wmo wi wph wps wa vz wmo wps vz
      weu wps vz wmo wph wps vz eumo imim2i wph wps vz moanimv sylibr 2alimi
      wph wps wa vx vy vz funoprabg syl wph wps vz weu wi vy wal vx wal wph wps
      wa vx vy vz coprab cdm wph wps wa vz wex vx vy copab wph vx vy copab wph
      wps wa vx vy vz dmoprab wph wps vz weu wi vy wal vx wal wph wps wa vz wex
      wph vx vy wph wps vz weu wi vy wal vx nfa1 wph wps vz weu wi vy vx nfa2
      wph wps vz weu wi vy wal wph wps wa vz wex wph wb vx wph wps vz weu wi
      wph wps wa vz wex wph wb vy wph wps vz weu wi wph wps wa vz wex wph wph
      wps wa wph vz wph wps simpl exlimiv wph wps vz weu wi wph wph wps vz wex
      wa wph wps wa vz wex wph wps vz weu wi wph wps vz wex wps vz weu wps vz
      wex wph wps vz euex imim2i ancld wph wps vz 19.42v syl6ibr impbid2 sps
      sps opabbid syl5eq wph wps wa vx vy vz coprab wph vx vy copab df-fn
      sylanbrc $.
  $}

  ${
    $d A w z $.  $d B w z $.  $d C w z $.  $d x y w z $.
    mpt2fun.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( The maps-to notation for an operation is always a function.
       (Contributed by Scott Fenton, 21-Mar-2012.) $)
    mpt2fun $p |- Fun F $=
      cF wfun vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab
      wfun vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz vx cv cA
      wcel vy cv cB wcel wa vz cv cC wceq wa vz wmo vx cv cA wcel vy cv cB wcel
      wa vz cv cC wceq wa vx cv cA wcel vy cv cB wcel wa vw cv cC wceq wa wa vz
      vw weq wi vw wal vz wal vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa
      vx cv cA wcel vy cv cB wcel wa vw cv cC wceq wa wa vz vw weq wi vz vw vz
      cv cC wceq vw cv cC wceq vz vw weq vx cv cA wcel vy cv cB wcel wa vx cv
      cA wcel vy cv cB wcel wa vz cv vw cv cC eqtr3 ad2ant2l gen2 vx cv cA wcel
      vy cv cB wcel wa vz cv cC wceq wa vx cv cA wcel vy cv cB wcel wa vw cv cC
      wceq wa vz vw vz vw weq vz cv cC wceq vw cv cC wceq vx cv cA wcel vy cv
      cB wcel wa vz cv vw cv cC eqeq1 anbi2d mo4 mpbir funoprab cF vx cv cA
      wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab cF vx vy cA cB cC
      cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab
      mpt2fun.1 vx vy vz cA cB cC df-mpt2 eqtri funeqi mpbir $.
  $}

  ${
    $d x y z $.  $d z ph $.
    fnoprab.1 $e |- ( ph -> E! z ps ) $.
    $( Functionality and domain of an operation class abstraction.
       (Contributed by NM, 15-May-1995.) $)
    fnoprab $p |- { <. <. x , y >. , z >. | ( ph /\ ps ) } Fn
                    { <. x , y >. | ph } $=
      wph wps vz weu wi vy wal vx wal wph wps wa vx vy vz coprab wph vx vy
      copab wfn wph wps vz weu wi vx vy fnoprab.1 gen2 wph wps vx vy vz
      fnoprabg ax-mp $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.  $d x y z w F $.
    $( An operation maps to a class to which all values belong.  (Contributed
       by NM, 7-Feb-2004.) $)
    ffnov $p |- ( F : ( A X. B ) --> C <-> ( F Fn ( A X. B ) /\
         A. x e. A A. y e. B ( x F y ) e. C ) ) $=
      cA cB cxp cC cF wf cF cA cB cxp wfn vw cv cF cfv cC wcel vw cA cB cxp
      wral wa cF cA cB cxp wfn vx cv vy cv cF co cC wcel vy cB wral vx cA wral
      wa vw cA cB cxp cC cF ffnfv vw cv cF cfv cC wcel vw cA cB cxp wral vx cv
      vy cv cF co cC wcel vy cB wral vx cA wral cF cA cB cxp wfn vw cv cF cfv
      cC wcel vx cv vy cv cF co cC wcel vw vx vy cA cB vw cv vx cv vy cv cop
      wceq vw cv cF cfv vx cv vy cv cF co cC vw cv vx cv vy cv cop wceq vw cv
      cF cfv vx cv vy cv cop cF cfv vx cv vy cv cF co vw cv vx cv vy cv cop cF
      fveq2 vx cv vy cv cF df-ov syl6eqr eleq1d ralxp anbi2i bitri $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y F $.  $d x y R $.  $d x y S $.
    fovcl.1 $e |- F : ( R X. S ) --> C $.
    $( Closure law for an operation.  (Contributed by NM, 19-Apr-2007.) $)
    fovcl $p |- ( ( A e. R /\ B e. S ) -> ( A F B ) e. C ) $=
      cA cR wcel cB cS wcel wa vx cv vy cv cF co cC wcel vy cS wral vx cR wral
      cA cB cF co cC wcel cR cS cxp cC cF wf vx cv vy cv cF co cC wcel vy cS
      wral vx cR wral fovcl.1 cR cS cxp cC cF wf cF cR cS cxp wfn vx cv vy cv
      cF co cC wcel vy cS wral vx cR wral vx vy cR cS cC cF ffnov simprbi ax-mp
      vx cv vy cv cF co cC wcel cA cB cF co cC wcel cA vy cv cF co cC wcel vx
      vy cA cB cR cS vx cv cA wceq vx cv vy cv cF co cA vy cv cF co cC vx cv cA
      vy cv cF oveq1 eleq1d vy cv cB wceq cA vy cv cF co cA cB cF co cC vy cv
      cB cA cF oveq2 eleq1d rspc2v mpi $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d z C $.  $d z D $.  $d x y z F $.
    $d x y z G $.
    $( Equality of two operations is determined by their values.  (Contributed
       by NM, 1-Sep-2005.) $)
    eqfnov $p |- ( ( F Fn ( A X. B ) /\ G Fn ( C X. D ) ) -> ( F = G <->
( ( A X. B ) = ( C X. D ) /\ A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) ) $=
      cF cA cB cxp wfn cG cC cD cxp wfn wa cF cG wceq cA cB cxp cC cD cxp wceq
      vz cv cF cfv vz cv cG cfv wceq vz cA cB cxp wral wa cA cB cxp cC cD cxp
      wceq vx cv vy cv cF co vx cv vy cv cG co wceq vy cB wral vx cA wral wa vz
      cA cB cxp cC cD cxp cF cG eqfnfv2 vz cv cF cfv vz cv cG cfv wceq vz cA cB
      cxp wral vx cv vy cv cF co vx cv vy cv cG co wceq vy cB wral vx cA wral
      cA cB cxp cC cD cxp wceq vz cv cF cfv vz cv cG cfv wceq vx cv vy cv cF co
      vx cv vy cv cG co wceq vz vx vy cA cB vz cv vx cv vy cv cop wceq vz cv cF
      cfv vz cv cG cfv wceq vx cv vy cv cop cF cfv vx cv vy cv cop cG cfv wceq
      vx cv vy cv cF co vx cv vy cv cG co wceq vz cv vx cv vy cv cop wceq vz cv
      cF cfv vx cv vy cv cop cF cfv vz cv cG cfv vx cv vy cv cop cG cfv vz cv
      vx cv vy cv cop cF fveq2 vz cv vx cv vy cv cop cG fveq2 eqeq12d vx cv vy
      cv cF co vx cv vy cv cop cF cfv vx cv vy cv cG co vx cv vy cv cop cG cfv
      vx cv vy cv cF df-ov vx cv vy cv cG df-ov eqeq12i syl6bbr ralxp anbi2i
      syl6bb $.
  $}

  ${
    $d A x y $.  $d B x y $.  $d F x y $.  $d G x y $.
    $( Two operators with the same domain are equal iff their values at each
       point in the domain are equal.  (Contributed by Jeff Madsen,
       7-Jun-2010.) $)
    eqfnov2 $p |- ( ( F Fn ( A X. B ) /\ G Fn ( A X. B ) ) ->
                  ( F = G <-> A. x e. A A. y e. B ( x F y ) = ( x G y ) ) ) $=
      cF cA cB cxp wfn cG cA cB cxp wfn wa cF cG wceq cA cB cxp cA cB cxp wceq
      vx cv vy cv cF co vx cv vy cv cG co wceq vy cB wral vx cA wral wa vx cv
      vy cv cF co vx cv vy cv cG co wceq vy cB wral vx cA wral vx vy cA cB cA
      cB cF cG eqfnov cA cB cxp cA cB cxp wceq vx cv vy cv cF co vx cv vy cv cG
      co wceq vy cB wral vx cA wral wa vx cv vy cv cF co vx cv vy cv cG co wceq
      vy cB wral vx cA wral cA cB cxp cA cB cxp wceq vx cv vy cv cF co vx cv vy
      cv cG co wceq vy cB wral vx cA wral simpr vx cv vy cv cF co vx cv vy cv
      cG co wceq vy cB wral vx cA wral cA cB cxp cA cB cxp wceq vx cv vy cv cF
      co vx cv vy cv cG co wceq vy cB wral vx cA wral cA cB cxp eqidd ancri
      impbii syl6bb $.
  $}

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w F $.
    $( Representation of a function in terms of its values.  (Contributed by
       NM, 7-Feb-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    fnov $p |- ( F Fn ( A X. B ) <->
                    F = ( x e. A , y e. B |-> ( x F y ) ) ) $=
      cF cA cB cxp wfn cF vz cA cB cxp vz cv cF cfv cmpt wceq cF vx vy cA cB vx
      cv vy cv cF co cmpt2 wceq vz cA cB cxp cF dffn5 vz cA cB cxp vz cv cF cfv
      cmpt vx vy cA cB vx cv vy cv cF co cmpt2 cF vx vy vz cA cB vz cv cF cfv
      vx cv vy cv cF co vz cv vx cv vy cv cop wceq vz cv cF cfv vx cv vy cv cop
      cF cfv vx cv vy cv cF co vz cv vx cv vy cv cop cF fveq2 vx cv vy cv cF
      df-ov syl6eqr mpt2mpt eqeq2i bitri $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d z C $.  $d z D $.
    $( Bidirectional equality theorem for a mapping abstraction.  Equivalent to
       ~ eqfnov2 .  (Contributed by Mario Carneiro, 4-Jan-2017.) $)
    mpt22eqb $p |- ( A. x e. A A. y e. B C e. V ->
      ( ( x e. A , y e. B |-> C ) = ( x e. A , y e. B |-> D ) <->
        A. x e. A A. y e. B C = D ) ) $=
      cC cV wcel vy cB wral vx cA wral cC cD wceq vy cB wral vx cA wral vz cv
      cC wceq vz cv cD wceq wb vz wal vy cB wral vx cA wral vx vy cA cB cC
      cmpt2 vx vy cA cB cD cmpt2 wceq cC cV wcel vy cB wral vx cA wral cC cD
      wceq vy cB wral vz cv cC wceq vz cv cD wceq wb vz wal vy cB wral wb vx cA
      wral cC cD wceq vy cB wral vx cA wral vz cv cC wceq vz cv cD wceq wb vz
      wal vy cB wral vx cA wral wb cC cV wcel vy cB wral cC cD wceq vy cB wral
      vz cv cC wceq vz cv cD wceq wb vz wal vy cB wral wb vx cA cC cV wcel vy
      cB wral cC cD wceq vz cv cC wceq vz cv cD wceq wb vz wal wb vy cB wral cC
      cD wceq vy cB wral vz cv cC wceq vz cv cD wceq wb vz wal vy cB wral wb cC
      cV wcel cC cD wceq vz cv cC wceq vz cv cD wceq wb vz wal wb vy cB vz cC
      cD cV pm13.183 ralimi cC cD wceq vz cv cC wceq vz cv cD wceq wb vz wal vy
      cB ralbi syl ralimi cC cD wceq vy cB wral vz cv cC wceq vz cv cD wceq wb
      vz wal vy cB wral vx cA ralbi syl vx vy cA cB cC cmpt2 vx vy cA cB cD
      cmpt2 wceq vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz
      coprab vx cv cA wcel vy cv cB wcel wa vz cv cD wceq wa vx vy vz coprab
      wceq vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx cv cA wcel vy cv
      cB wcel wa vz cv cD wceq wa wb vz wal vy wal vx wal vz cv cC wceq vz cv
      cD wceq wb vz wal vy cB wral vx cA wral vx vy cA cB cC cmpt2 vx cv cA
      wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab vx vy cA cB cD
      cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cD wceq wa vx vy vz coprab vx
      vy vz cA cB cC df-mpt2 vx vy vz cA cB cD df-mpt2 eqeq12i vx cv cA wcel vy
      cv cB wcel wa vz cv cC wceq wa vx cv cA wcel vy cv cB wcel wa vz cv cD
      wceq wa vx vy vz eqoprab2b vx cv cA wcel vy cv cB wcel wa vz cv cC wceq
      wa vx cv cA wcel vy cv cB wcel wa vz cv cD wceq wa wb vz wal vy wal vx
      wal vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv cD wceq wb vz wal
      wi vy wal vx wal vz cv cC wceq vz cv cD wceq wb vz wal vy cB wral vx cA
      wral vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx cv cA wcel vy cv
      cB wcel wa vz cv cD wceq wa wb vz wal vx cv cA wcel vy cv cB wcel wa vz
      cv cC wceq vz cv cD wceq wb vz wal wi vx vy vx cv cA wcel vy cv cB wcel
      wa vz cv cC wceq wa vx cv cA wcel vy cv cB wcel wa vz cv cD wceq wa wb vz
      wal vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv cD wceq wb wi vz
      wal vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv cD wceq wb vz wal
      wi vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv cD wceq wb wi vx cv
      cA wcel vy cv cB wcel wa vz cv cC wceq wa vx cv cA wcel vy cv cB wcel wa
      vz cv cD wceq wa wb vz vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv
      cD wceq pm5.32 albii vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vz cv
      cD wceq wb vz 19.21v bitr3i 2albii vz cv cC wceq vz cv cD wceq wb vz wal
      vx vy cA cB r2al bitr4i 3bitri syl6rbbr $.
  $}

  ${
    $d w x $.  $d w y z A $.  $d w z B $.  $d w z C $.  $d w z F $.  $d z ps $.
    $d x y z D $.  $d x y ph $.
    rngop.1 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( The range of an operation given by the "maps to" notation.  (Contributed
       by FL, 20-Jun-2011.) $)
    rnmpt2 $p |- ran F = { z | E. x e. A E. y e. B z = C } $=
      cF crn vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab
      crn vz cv cC wceq vy cB wrex vx cA wrex vz cab cF vx cv cA wcel vy cv cB
      wcel wa vz cv cC wceq wa vx vy vz coprab cF vx vy cA cB cC cmpt2 vx cv cA
      wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz coprab rngop.1 vx vy vz
      cA cB cC df-mpt2 eqtri rneqi vz cv cC wceq vx vy vz cA cB rnoprab2 eqtri
      $.

    $( The domain of an operation defined by maps-to notation is a relation.
       (Contributed by Stefan O'Rear, 27-Nov-2014.) $)
    reldmmpt2 $p |- Rel dom F $=
      cF cdm wrel vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz
      coprab cdm wrel vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz
      reldmoprab cF cdm vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy
      vz coprab cdm cF vx cv cA wcel vy cv cB wcel wa vz cv cC wceq wa vx vy vz
      coprab cF vx vy cA cB cC cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cC
      wceq wa vx vy vz coprab rngop.1 vx vy vz cA cB cC df-mpt2 eqtri dmeqi
      releqi mpbir $.

    $( Membership in the range of an operation class abstraction.  (Contributed
       by NM, 27-Aug-2007.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    elrnmpt2g $p |- ( D e. V ->
                     ( D e. ran F <-> E. x e. A E. y e. B D = C ) ) $=
      vz cv cC wceq vy cB wrex vx cA wrex cD cC wceq vy cB wrex vx cA wrex vz
      cD cF crn cV vz cv cD wceq vz cv cC wceq cD cC wceq vx vy cA cB vz cv cD
      cC eqeq1 2rexbidv vx vy vz cA cB cC cF rngop.1 rnmpt2 elab2g $.

    ${
      elrnmpt2.1 $e |- C e. _V $.
      $( Membership in the range of an operation class abstraction.
         (Contributed by NM, 1-Aug-2004.)  (Revised by Mario Carneiro,
         31-Aug-2015.) $)
      elrnmpt2 $p |- ( D e. ran F <-> E. x e. A E. y e. B D = C ) $=
        cD cF crn wcel cD vz cv cC wceq vy cB wrex vx cA wrex vz cab wcel cD cC
        wceq vy cB wrex vx cA wrex cF crn vz cv cC wceq vy cB wrex vx cA wrex
        vz cab cD vx vy vz cA cB cC cF rngop.1 rnmpt2 eleq2i vz cv cC wceq vy
        cB wrex vx cA wrex cD cC wceq vy cB wrex vx cA wrex vz cD cD cC wceq vy
        cB wrex cD cvv wcel vx cA cD cC wceq cD cvv wcel vy cB cD cC wceq cD
        cvv wcel cC cvv wcel elrnmpt2.1 cD cC cvv eleq1 mpbiri rexlimivw
        rexlimivw vz cv cD wceq vz cv cC wceq cD cC wceq vx vy cA cB vz cv cD
        cC eqeq1 2rexbidv elab3 bitri $.
    $}

    ralrnmpt2.2 $e |- ( z = C -> ( ph <-> ps ) ) $.
    $( A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 1-Sep-2015.) $)
    ralrnmpt2 $p |- ( A. x e. A A. y e. B C e. V ->
      ( A. z e. ran F ph <-> A. x e. A A. y e. B ps ) ) $=
      wph vz cF crn wral vz cv cC wceq vy cB wrex wph wi vz wal vx cA wral cC
      cV wcel vy cB wral vx cA wral wps vy cB wral vx cA wral wph vz cF crn
      wral wph vz vw cv cC wceq vy cB wrex vx cA wrex vw cab wral vz cv cC wceq
      vy cB wrex vx cA wrex wph wi vz wal vz cv cC wceq vy cB wrex wph wi vz
      wal vx cA wral wph vz cF crn vw cv cC wceq vy cB wrex vx cA wrex vw cab
      vx vy vw cA cB cC cF rngop.1 rnmpt2 raleqi vw cv cC wceq vy cB wrex vx cA
      wrex vz cv cC wceq vy cB wrex vx cA wrex wph vz vw vw cv vz cv wceq vw cv
      cC wceq vz cv cC wceq vx vy cA cB vw cv vz cv cC eqeq1 2rexbidv ralab vz
      cv cC wceq vy cB wrex wph wi vz wal vx cA wral vz cv cC wceq vy cB wrex
      wph wi vx cA wral vz wal vz cv cC wceq vy cB wrex vx cA wrex wph wi vz
      wal vz cv cC wceq vy cB wrex wph wi vx vz cA ralcom4 vz cv cC wceq vy cB
      wrex wph wi vx cA wral vz cv cC wceq vy cB wrex vx cA wrex wph wi vz vz
      cv cC wceq vy cB wrex wph vx cA r19.23v albii bitr2i 3bitri cC cV wcel vy
      cB wral vx cA wral vz cv cC wceq vy cB wrex wph wi vz wal wps vy cB wral
      wb vx cA wral vz cv cC wceq vy cB wrex wph wi vz wal vx cA wral wps vy cB
      wral vx cA wral wb cC cV wcel vy cB wral vz cv cC wceq vy cB wrex wph wi
      vz wal wps vy cB wral wb vx cA vz cv cC wceq vy cB wrex wph wi vz wal vz
      cv cC wceq wph wi vz wal vy cB wral cC cV wcel vy cB wral wps vy cB wral
      vz cv cC wceq wph wi vz wal vy cB wral vz cv cC wceq wph wi vy cB wral vz
      wal vz cv cC wceq vy cB wrex wph wi vz wal vz cv cC wceq wph wi vy vz cB
      ralcom4 vz cv cC wceq wph wi vy cB wral vz cv cC wceq vy cB wrex wph wi
      vz vz cv cC wceq wph vy cB r19.23v albii bitri cC cV wcel vy cB wral vz
      cv cC wceq wph wi vz wal wps wb vy cB wral vz cv cC wceq wph wi vz wal vy
      cB wral wps vy cB wral wb cC cV wcel vz cv cC wceq wph wi vz wal wps wb
      vy cB wph wps vz cC cV wps vz nfv ralrnmpt2.2 ceqsalg ralimi vz cv cC
      wceq wph wi vz wal wps vy cB ralbi syl syl5bbr ralimi vz cv cC wceq vy cB
      wrex wph wi vz wal wps vy cB wral vx cA ralbi syl syl5bb $.

    $( A restricted quantifier over an image set.  (Contributed by Mario
       Carneiro, 1-Sep-2015.) $)
    rexrnmpt2 $p |- ( A. x e. A A. y e. B C e. V ->
      ( E. z e. ran F ph <-> E. x e. A E. y e. B ps ) ) $=
      cC cV wcel vy cB wral vx cA wral wph wn vz cF crn wral wn wps wn vy cB
      wral vx cA wral wn wph vz cF crn wrex wps vy cB wrex vx cA wrex cC cV
      wcel vy cB wral vx cA wral wph wn vz cF crn wral wps wn vy cB wral vx cA
      wral wph wn wps wn vx vy vz cA cB cC cF cV rngop.1 vz cv cC wceq wph wps
      ralrnmpt2.2 notbid ralrnmpt2 notbid wph vz cF crn dfrex2 wps vy cB wrex
      vx cA wrex wps wn vy cB wral wn vx cA wrex wps wn vy cB wral vx cA wral
      wn wps vy cB wrex wps wn vy cB wral wn vx cA wps vy cB dfrex2 rexbii wps
      wn vy cB wral vx cA rexnal bitri 3bitr4g $.
  $}

  ${
    $d A x y z $.  $d B x y z $.  $d ph x y z $.
    oprabexd.1 $e |- ( ph -> A e. _V ) $.
    oprabexd.2 $e |- ( ph -> B e. _V ) $.
    oprabexd.3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> E* z ps ) $.
    oprabexd.4 $e |- ( ph -> F = { <. <. x , y >. , z >. |
                                        ( ( x e. A /\ y e. B ) /\ ps ) } ) $.
    $( Existence of an operator abstraction.  (Contributed by Jeff Madsen,
       2-Sep-2009.) $)
    oprabexd $p |- ( ph -> F e. _V ) $=
      wph cF vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz coprab cvv
      oprabexd.4 wph vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz coprab wfun
      vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz coprab cdm cvv wcel vx cv
      cA wcel vy cv cB wcel wa wps wa vx vy vz coprab cvv wcel wph vx cv cA
      wcel vy cv cB wcel wa wps wa vz wmo vy wal vx wal vx cv cA wcel vy cv cB
      wcel wa wps wa vx vy vz coprab wfun wph vx cv cA wcel vy cv cB wcel wa
      wps wa vz wmo vx vy wph vx cv cA wcel vy cv cB wcel wa wps vz wmo wi vx
      cv cA wcel vy cv cB wcel wa wps wa vz wmo wph vx cv cA wcel vy cv cB wcel
      wa wps vz wmo oprabexd.3 ex vx cv cA wcel vy cv cB wcel wa wps vz moanimv
      sylibr alrimivv vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz funoprabg
      syl wph vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz coprab cdm cA cB
      cxp wss cA cB cxp cvv wcel vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz
      coprab cdm cvv wcel wps vx vy vz cA cB dmoprabss wph cA cvv wcel cB cvv
      wcel cA cB cxp cvv wcel oprabexd.1 oprabexd.2 cA cB cvv cvv xpexg syl2anc
      vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz coprab cdm cA cB cxp cvv
      ssexg sylancr cvv vx cv cA wcel vy cv cB wcel wa wps wa vx vy vz coprab
      funex syl2anc eqeltrd $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    oprabex.1 $e |- A e. _V $.
    oprabex.2 $e |- B e. _V $.
    oprabex.3 $e |- ( ( x e. A /\ y e. B ) -> E* z ph ) $.
    oprabex.4 $e |- F = { <. <. x , y >. , z >. | ( ( x e. A /\ y e. B )
             /\ ph ) } $.
    $( Existence of an operation class abstraction.  (Contributed by NM,
       19-Oct-2004.) $)
    oprabex $p |- F e. _V $=
      cF vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz coprab cvv oprabex.4 vx
      cv cA wcel vy cv cB wcel wa wph wa vx vy vz coprab wfun vx cv cA wcel vy
      cv cB wcel wa wph wa vx vy vz coprab cdm cvv wcel vx cv cA wcel vy cv cB
      wcel wa wph wa vx vy vz coprab cvv wcel vx cv cA wcel vy cv cB wcel wa
      wph wa vx vy vz vx cv cA wcel vy cv cB wcel wa wph wa vz wmo vx cv cA
      wcel vy cv cB wcel wa wph vz wmo wi oprabex.3 vx cv cA wcel vy cv cB wcel
      wa wph vz moanimv mpbir funoprab vx cv cA wcel vy cv cB wcel wa wph wa vx
      vy vz coprab cdm cA cB cxp cA cB oprabex.1 oprabex.2 xpex wph vx vy vz cA
      cB dmoprabss ssexi cvv vx cv cA wcel vy cv cB wcel wa wph wa vx vy vz
      coprab funex mp2an eqeltri $.
  $}

  ${
    $d x y z w v u f A $.  $d x y z w v u f B $.  $d x y z w v u f C $.
    $d x y z w v u f D $.  $d x y z w v u f H $.  $d x y z R $.
    $d x y z w v u f S $.
    oprabex3.1 $e |- H e. _V $.
    oprabex3.2 $e |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\
                      y e. ( H X. H ) ) /\
                      E. w E. v E. u E. f ( ( x = <. w , v >. /\
                      y = <. u , f >. ) /\ z = R ) ) } $.
    $( Existence of an operation class abstraction (special case).
       (Contributed by NM, 19-Oct-2004.) $)
    oprabex3 $p |- F e. _V $=
      vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa
      vf wex vu wex vv wex vw wex vx vy vz cH cH cxp cH cH cxp cF cH cH
      oprabex3.1 oprabex3.1 xpex cH cH oprabex3.1 oprabex3.1 xpex vx cv vw cv
      vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu
      wex vv wex vw wex vz wmo vx cv cH cH cxp wcel vy cv cH cH cxp wcel wa vx
      cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf
      wex vu wex vv wex vw wex vz wmo vx cv vw cv vv cv cop wceq vy cv vu cv vf
      cv cop wceq vz cv cR wceq wa vf wex vu wex wa vv wex vw wex vz wmo vy cv
      vu cv vf cv cop wceq vz cv cR wceq wa vf wex vu wex vz vw vv vx cv vz cv
      cR wceq vz vu vf vy cv vz cR moeq mosubop mosubop vx cv vw cv vv cv cop
      wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex
      vw wex vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR
      wceq wa vf wex vu wex wa vv wex vw wex vz vx cv vw cv vv cv cop wceq vy
      cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vx cv vw cv vv
      cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq wa vf wex vu wex wa
      vw vv vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR
      wceq wa vf wex vu wex vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop
      wceq vz cv cR wceq wa wa vf wex vu wex vx cv vw cv vv cv cop wceq vy cv
      vu cv vf cv cop wceq vz cv cR wceq wa vf wex vu wex wa vx cv vw cv vv cv
      cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vx cv vw cv vv cv
      cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq wa wa vu vf vx cv vw cv
      vv cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq anass 2exbii vx
      cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq wa vu vf
      19.42vv bitri 2exbii mobii mpbir a1i oprabex3.2 oprabex $.
  $}

  ${
    $d A v x y z w $.  $d ph v $.
    oprabrexex2.1 $e |- A e. _V $.
    oprabrexex2.2 $e |- { <. <. x , y >. , z >. | ph } e. _V $.
    $( Existence of an existentially restricted operation abstraction.
       (Contributed by Jeff Madsen, 11-Jun-2010.) $)
    oprabrexex2 $p |- { <. <. x , y >. , z >. | E. w e. A ph } e. _V $=
      wph vw cA wrex vx vy vz coprab vv cv vx cv vy cv cop vz cv cop wceq wph
      wa vz wex vy wex vx wex vw cA wrex vv cab cvv wph vw cA wrex vx vy vz
      coprab vv cv vx cv vy cv cop vz cv cop wceq wph vw cA wrex wa vz wex vy
      wex vx wex vv cab vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy
      wex vx wex vw cA wrex vv cab wph vw cA wrex vx vy vz vv df-oprab vv cv vx
      cv vy cv cop vz cv cop wceq wph vw cA wrex wa vz wex vy wex vx wex vv cv
      vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex vw cA wrex vv
      vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex vw cA
      wrex vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vw cA wrex
      vx wex vv cv vx cv vy cv cop vz cv cop wceq wph vw cA wrex wa vz wex vy
      wex vx wex vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vw
      vx cA rexcom4 vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex
      vw cA wrex vv cv vx cv vy cv cop vz cv cop wceq wph vw cA wrex wa vz wex
      vy wex vx vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vw cA
      wrex vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vw cA wrex vy wex
      vv cv vx cv vy cv cop vz cv cop wceq wph vw cA wrex wa vz wex vy wex vv
      cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vw vy cA rexcom4 vv cv vx
      cv vy cv cop vz cv cop wceq wph wa vz wex vw cA wrex vv cv vx cv vy cv
      cop vz cv cop wceq wph vw cA wrex wa vz wex vy vv cv vx cv vy cv cop vz
      cv cop wceq wph wa vz wex vw cA wrex vv cv vx cv vy cv cop vz cv cop wceq
      wph wa vw cA wrex vz wex vv cv vx cv vy cv cop vz cv cop wceq wph vw cA
      wrex wa vz wex vv cv vx cv vy cv cop vz cv cop wceq wph wa vw vz cA
      rexcom4 vv cv vx cv vy cv cop vz cv cop wceq wph wa vw cA wrex vv cv vx
      cv vy cv cop vz cv cop wceq wph vw cA wrex wa vz vv cv vx cv vy cv cop vz
      cv cop wceq wph vw cA r19.42v exbii bitri exbii bitri exbii bitr2i abbii
      eqtri vv cv vx cv vy cv cop vz cv cop wceq wph wa vz wex vy wex vx wex vw
      vv cA oprabrexex2.1 wph vx vy vz coprab vv cv vx cv vy cv cop vz cv cop
      wceq wph wa vz wex vy wex vx wex vv cab cvv wph vx vy vz vv df-oprab
      oprabrexex2.2 eqeltrri abrexex2 eqeltri $.
  $}

  ${
    $d x y z $.  $d z R $.  $d z S $.
    ovid.1 $e |- ( ( x e. R /\ y e. S ) -> E! z ph ) $.
    ovid.2 $e |- F =
                  { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
    $( The value of an operation class abstraction.  (Contributed by NM,
       16-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    ovid $p |- ( ( x e. R /\ y e. S ) -> ( ( x F y ) = z <-> ph ) ) $=
      vx cv vy cv cF co vz cv wceq vx cv vy cv cop cF cfv vz cv wceq vx cv cR
      wcel vy cv cS wcel wa wph vx cv vy cv cF co vx cv vy cv cop cF cfv vz cv
      vx cv vy cv cF df-ov eqeq1i vx cv cR wcel vy cv cS wcel wa vx cv vy cv
      cop cF cfv vz cv wceq vx cv vy cv cop vz cv cop cF wcel wph vx cv cR wcel
      vy cv cS wcel wa cF vx cv cR wcel vy cv cS wcel wa vx vy copab wfn vx cv
      vy cv cop vx cv cR wcel vy cv cS wcel wa vx vy copab wcel vx cv vy cv cop
      cF cfv vz cv wceq vx cv vy cv cop vz cv cop cF wcel wb cF vx cv cR wcel
      vy cv cS wcel wa vx vy copab wfn vx cv cR wcel vy cv cS wcel wa wph wa vx
      vy vz coprab vx cv cR wcel vy cv cS wcel wa vx vy copab wfn vx cv cR wcel
      vy cv cS wcel wa wph vx vy vz ovid.1 fnoprab vx cv cR wcel vy cv cS wcel
      wa vx vy copab cF vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab
      ovid.2 fneq1i mpbir vx cv vy cv cop vx cv cR wcel vy cv cS wcel wa vx vy
      copab wcel vx cv cR wcel vy cv cS wcel wa vx cv cR wcel vy cv cS wcel wa
      vx vy opabid biimpri vx cv cR wcel vy cv cS wcel wa vx vy copab vx cv vy
      cv cop vz cv cF fnopfvb sylancr vx cv vy cv cop vz cv cop cF wcel vx cv
      cR wcel vy cv cS wcel wa wph vx cv vy cv cop vz cv cop cF wcel vx cv vy
      cv cop vz cv cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab
      wcel vx cv cR wcel vy cv cS wcel wa wph wa cF vx cv cR wcel vy cv cS wcel
      wa wph wa vx vy vz coprab vx cv vy cv cop vz cv cop ovid.2 eleq2i vx cv
      cR wcel vy cv cS wcel wa wph wa vx vy vz oprabid bitri baib bitrd syl5bb
      $.
  $}

  ${
    $d x y z $.
    ovidig.1 $e |- E* z ph $.
    ovidig.2 $e |- F = { <. <. x , y >. , z >. | ph } $.
    $( The value of an operation class abstraction.  Compare ~ ovidi .  The
       condition ` ( x e. R /\ y e. S ) ` is been removed.  (Contributed by
       Mario Carneiro, 29-Dec-2014.) $)
    ovidig $p |- ( ph -> ( x F y ) = z ) $=
      wph vx cv vy cv cF co vx cv vy cv cop cF cfv vz cv vx cv vy cv cF df-ov
      cF wfun wph vx cv vy cv cop vz cv cop cF wcel vx cv vy cv cop cF cfv vz
      cv wceq cF wfun wph vx vy vz coprab wfun wph vx vy vz ovidig.1 funoprab
      cF wph vx vy vz coprab ovidig.2 funeqi mpbir wph vx cv vy cv cop vz cv
      cop wph vx vy vz coprab cF vx cv vy cv cop vz cv cop wph vx vy vz coprab
      wcel wph wph vx vy vz oprabid biimpri ovidig.2 syl6eleqr vx cv vy cv cop
      vz cv cF funopfv mpsyl syl5eq $.
  $}

  ${
    $d x y z $.  $d z R $.  $d z S $.
    ovidi.2 $e |- ( ( x e. R /\ y e. S ) -> E* z ph ) $.
    ovidi.3 $e |- F =
                  { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
    $( The value of an operation class abstraction (weak version).
       (Contributed by Mario Carneiro, 29-Dec-2014.) $)
    ovidi $p |- ( ( x e. R /\ y e. S ) -> ( ph -> ( x F y ) = z ) ) $=
      vx cv cR wcel vy cv cS wcel wa wph vx cv vy cv cF co vz cv wceq vx cv cR
      wcel vy cv cS wcel wa wph wa vx vy vz cF vx cv cR wcel vy cv cS wcel wa
      wph wa vz wmo vx cv cR wcel vy cv cS wcel wa wph vz wmo wi ovidi.2 vx cv
      cR wcel vy cv cS wcel wa wph vz moanimv mpbir ovidi.3 ovidig ex $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z R $.  $d x y z S $.
    $d x y z th $.
    ov.1 $e |- C e. _V $.
    ov.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ov.3 $e |- ( y = B -> ( ps <-> ch ) ) $.
    ov.4 $e |- ( z = C -> ( ch <-> th ) ) $.
    ov.5 $e |- ( ( x e. R /\ y e. S ) -> E! z ph ) $.
    ov.6 $e |- F =
                  { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
    $( The value of an operation class abstraction.  (Contributed by NM,
       16-May-1995.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    ov $p |- ( ( A e. R /\ B e. S ) -> ( ( A F B ) = C <-> th ) ) $=
      cA cR wcel cB cS wcel wa cA cB cF co cC wceq wth cA cB cF co cC wceq cA
      cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC wceq
      cA cR wcel cB cS wcel wa cA cR wcel cB cS wcel wa wth wa cA cB cF co cA
      cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC cA cB
      cF co cA cB cop cF cfv cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx
      vy vz coprab cfv cA cB cF df-ov cA cB cop cF vx cv cR wcel vy cv cS wcel
      wa wph wa vx vy vz coprab ov.6 fveq1i eqtri eqeq1i cA cR wcel cB cS wcel
      wa cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC
      wceq cA cB cop cC cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz
      coprab wcel cA cR wcel cB cS wcel wa wth wa cA cR wcel cB cS wcel wa vx
      cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab vx cv cR wcel vy cv cS
      wcel wa vx vy copab wfn cA cB cop vx cv cR wcel vy cv cS wcel wa vx vy
      copab wcel cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz
      coprab cfv cC wceq cA cB cop cC cop vx cv cR wcel vy cv cS wcel wa wph wa
      vx vy vz coprab wcel wb vx cv cR wcel vy cv cS wcel wa wph vx vy vz ov.5
      fnoprab cA cR wcel cB cS wcel wa cA cB cop vx cv cR wcel vy cv cS wcel wa
      vx vy copab wcel vx cv cR wcel vy cv cS wcel wa cA cR wcel vy cv cS wcel
      wa cA cR wcel cB cS wcel wa vx vy cA cB cR cS vx cv cA wceq vx cv cR wcel
      cA cR wcel vy cv cS wcel vx cv cA cR eleq1 anbi1d vy cv cB wceq vy cv cS
      wcel cB cS wcel cA cR wcel vy cv cB cS eleq1 anbi2d opelopabg ibir vx cv
      cR wcel vy cv cS wcel wa vx vy copab cA cB cop cC vx cv cR wcel vy cv cS
      wcel wa wph wa vx vy vz coprab fnopfvb sylancr cA cR wcel cB cS wcel cC
      cvv wcel cA cB cop cC cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz
      coprab wcel cA cR wcel cB cS wcel wa wth wa wb ov.1 vx cv cR wcel vy cv
      cS wcel wa wph wa cA cR wcel vy cv cS wcel wa wps wa cA cR wcel cB cS
      wcel wa wch wa cA cR wcel cB cS wcel wa wth wa vx vy vz cA cB cC cR cS
      cvv vx cv cA wceq vx cv cR wcel vy cv cS wcel wa cA cR wcel vy cv cS wcel
      wa wph wps vx cv cA wceq vx cv cR wcel cA cR wcel vy cv cS wcel vx cv cA
      cR eleq1 anbi1d ov.2 anbi12d vy cv cB wceq cA cR wcel vy cv cS wcel wa cA
      cR wcel cB cS wcel wa wps wch vy cv cB wceq vy cv cS wcel cB cS wcel cA
      cR wcel vy cv cB cS eleq1 anbi2d ov.3 anbi12d vz cv cC wceq wch wth cA cR
      wcel cB cS wcel wa ov.4 anbi2d eloprabg mp3an3 bitrd syl5bb bianabs $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z ps $.
    ovigg.1 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    ovigg.4 $e |- E* z ph $.
    ovigg.5 $e |- F = { <. <. x , y >. , z >. | ph } $.
    $( The value of an operation class abstraction.  Compare ~ ovig .  The
       condition ` ( x e. R /\ y e. S ) ` is been removed.  (Contributed by FL,
       24-Mar-2007.)  (Revised by Mario Carneiro, 19-Dec-2013.) $)
    ovigg $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
                         ( ps -> ( A F B ) = C ) ) $=
      cA cV wcel cB cW wcel cC cX wcel w3a wps cA cB cop cC cop wph vx vy vz
      coprab wcel cA cB cF co cC wceq wph wps vx vy vz cA cB cC cV cW cX
      ovigg.1 eloprabga cA cB cop cC cop wph vx vy vz coprab wcel cA cB cF co
      cA cB cop wph vx vy vz coprab cfv cC cA cB cF co cA cB cop cF cfv cA cB
      cop wph vx vy vz coprab cfv cA cB cF df-ov cA cB cop cF wph vx vy vz
      coprab ovigg.5 fveq1i eqtri wph vx vy vz coprab wfun cA cB cop cC cop wph
      vx vy vz coprab wcel cA cB cop wph vx vy vz coprab cfv cC wceq wi wph vx
      vy vz ovigg.4 funoprab cA cB cop cC wph vx vy vz coprab funopfv ax-mp
      syl5eq syl6bir $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z R $.  $d x y z S $.
    $d x y z ps $.
    ovig.1 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    ovig.2 $e |- ( ( x e. R /\ y e. S ) -> E* z ph ) $.
    ovig.3 $e |- F =
                  { <. <. x , y >. , z >. | ( ( x e. R /\ y e. S ) /\ ph ) } $.
    $( The value of an operation class abstraction (weak version).
       (Unnecessary distinct variable restrictions were removed by David
       Abernethy, 19-Jun-2012.)  (Contributed by NM, 14-Sep-1999.)  (Revised by
       Mario Carneiro, 19-Dec-2013.) $)
    ovig $p |- ( ( A e. R /\ B e. S /\ C e. D ) ->
                         ( ps -> ( A F B ) = C ) ) $=
      cA cR wcel cB cS wcel cC cD wcel w3a cA cR wcel cB cS wcel wa wps cA cB
      cF co cC wceq cA cR wcel cB cS wcel cC cD wcel 3simpa vx cv cR wcel vy cv
      cS wcel wa wph wa cA cR wcel cB cS wcel wa wps wa vx vy vz cA cB cC cF cR
      cS cD vx cv cA wceq vy cv cB wceq vz cv cC wceq w3a vx cv cR wcel vy cv
      cS wcel wa cA cR wcel cB cS wcel wa wph wps vx cv cA wceq vy cv cB wceq
      vx cv cR wcel vy cv cS wcel wa cA cR wcel cB cS wcel wa wb vz cv cC wceq
      vx cv cA wceq vx cv cR wcel cA cR wcel vy cv cB wceq vy cv cS wcel cB cS
      wcel vx cv cA cR eleq1 vy cv cB cS eleq1 bi2anan9 3adant3 ovig.1 anbi12d
      vx cv cR wcel vy cv cS wcel wa wph wa vz wmo vx cv cR wcel vy cv cS wcel
      wa wph vz wmo wi ovig.2 vx cv cR wcel vy cv cS wcel wa wph vz moanimv
      mpbir ovig.3 ovigg mpand $.
  $}

  ${
    $d x y z $.  $d z A $.  $d z B $.  $d z C $.  $d z F $.
    ovmpt4g.3 $e |- F = ( x e. A , y e. B |-> C ) $.
    $( Value of a function given by the "maps to" notation.  (This is the
       operation analog of ~ fvmpt2 .)  (Contributed by NM, 21-Feb-2004.)
       (Revised by Mario Carneiro, 1-Sep-2015.) $)
    ovmpt4g $p |- ( ( x e. A /\ y e. B /\ C e. V ) -> ( x F y ) = C ) $=
      vx cv cA wcel vy cv cB wcel cC cV wcel vx cv vy cv cF co cC wceq cC cV
      wcel vz cv cC wceq vz wex vx cv cA wcel vy cv cB wcel wa vx cv vy cv cF
      co cC wceq vz cC cV elisset vx cv cA wcel vy cv cB wcel wa vz cv cC wceq
      vx cv vy cv cF co cC wceq vz vz cv cC wceq vx cv vy cv cF co vz cv wceq
      vx cv vy cv cF co cC wceq vx cv cA wcel vy cv cB wcel wa vz cv cC wceq vx
      vy vz cA cB cF vz cv cC wceq vz wmo vx cv cA wcel vy cv cB wcel wa vz cC
      moeq a1i cF vx vy cA cB cC cmpt2 vx cv cA wcel vy cv cB wcel wa vz cv cC
      wceq wa vx vy vz coprab ovmpt4g.3 vx vy vz cA cB cC df-mpt2 eqtri ovidi
      vz cv cC vx cv vy cv cF co eqeq2 mpbidi exlimdv syl5 3impia $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.  $d z F $.
    $d z R $.
    ovmpt2s.3 $e |- F = ( x e. C , y e. D |-> R ) $.
    $( Value of a function given by the "maps to" notation, expressed using
       explicit substitution.  (Contributed by Mario Carneiro, 30-Apr-2015.) $)
    ovmpt2s $p |- ( ( A e. C /\ B e. D /\ [_ A / x ]_ [_ B / y ]_ R e. V ) ->
      ( A F B ) = [_ A / x ]_ [_ B / y ]_ R ) $=
      cA cC wcel cB cD wcel vx cA vy cB cR csb csb cV wcel cA cB cF co vx cA vy
      cB cR csb csb wceq vx cA vy cB cR csb csb cV wcel vx cA vy cB cR csb csb
      cvv wcel cA cC wcel cB cD wcel wa cA cB cF co vx cA vy cB cR csb csb wceq
      vx cA vy cB cR csb csb cV elex cA cC wcel cB cD wcel wa vy cB vx cA cR
      csb csb cvv wcel cA cB cF co vy cB vx cA cR csb csb wceq vx cA vy cB cR
      csb csb cvv wcel cA cB cF co vx cA vy cB cR csb csb wceq cR cvv wcel vx
      cv vy cv cF co cR wceq wi vx cA cR csb cvv wcel cA vy cv cF co vx cA cR
      csb wceq wi vy cB vx cA cR csb csb cvv wcel cA cB cF co vy cB vx cA cR
      csb csb wceq wi vx vy cA cB cC cD vx cA nfcv vy cA nfcv vy cB nfcv vx cA
      cR csb cvv wcel cA vy cv cF co vx cA cR csb wceq vx vx vx cA cR csb cvv
      vx cA cR nfcsb1v nfel1 vx cA vy cv cF co vx cA cR csb vx cA vy cv cF vx
      cA nfcv vx cF vx vy cC cD cR cmpt2 ovmpt2s.3 vx vy cC cD cR nfmpt21
      nfcxfr vx vy cv nfcv nfov vx cA cR nfcsb1v nfeq nfim vy cB vx cA cR csb
      csb cvv wcel cA cB cF co vy cB vx cA cR csb csb wceq vy vy vy cB vx cA cR
      csb csb cvv vy cB vx cA cR csb nfcsb1v nfel1 vy cA cB cF co vy cB vx cA
      cR csb csb vy cA cB cF vy cA nfcv vy cF vx vy cC cD cR cmpt2 ovmpt2s.3 vx
      vy cC cD cR nfmpt22 nfcxfr vy cB nfcv nfov vy cB vx cA cR csb nfcsb1v
      nfeq nfim vx cv cA wceq cR cvv wcel vx cA cR csb cvv wcel vx cv vy cv cF
      co cR wceq cA vy cv cF co vx cA cR csb wceq vx cv cA wceq cR vx cA cR csb
      cvv vx cA cR csbeq1a eleq1d vx cv cA wceq vx cv vy cv cF co cA vy cv cF
      co cR vx cA cR csb vx cv cA vy cv cF oveq1 vx cA cR csbeq1a eqeq12d
      imbi12d vy cv cB wceq vx cA cR csb cvv wcel vy cB vx cA cR csb csb cvv
      wcel cA vy cv cF co vx cA cR csb wceq cA cB cF co vy cB vx cA cR csb csb
      wceq vy cv cB wceq vx cA cR csb vy cB vx cA cR csb csb cvv vy cB vx cA cR
      csb csbeq1a eleq1d vy cv cB wceq cA vy cv cF co cA cB cF co vx cA cR csb
      vy cB vx cA cR csb csb vy cv cB cA cF oveq2 vy cB vx cA cR csb csbeq1a
      eqeq12d imbi12d vx cv cC wcel vy cv cD wcel cR cvv wcel vx cv vy cv cF co
      cR wceq vx vy cC cD cR cF cvv ovmpt2s.3 ovmpt4g 3expia vtocl2gaf cA cC
      wcel cB cD wcel wa vx cA vy cB cR csb csb vy cB vx cA cR csb csb cvv vx
      vy cA cB cR cC cD csbcomg eleq1d cA cC wcel cB cD wcel wa vx cA vy cB cR
      csb csb vy cB vx cA cR csb csb cA cB cF co vx vy cA cB cR cC cD csbcomg
      eqeq2d 3imtr4d syl5 3impia $.
  $}

  ${
    $d t u v w A $.  $d t u v w B $.  $d t u v w x y z C $.  $d t u v w z R $.
    $d t u v w x y z D $.  $d w F $.  $d w G $.  $d t u v w S $.
    ov2gf.a $e |- F/_ x A $.
    ov2gf.c $e |- F/_ y A $.
    ov2gf.d $e |- F/_ y B $.
    ov2gf.1 $e |- F/_ x G $.
    ov2gf.2 $e |- F/_ y S $.
    ov2gf.3 $e |- ( x = A -> R = G ) $.
    ov2gf.4 $e |- ( y = B -> G = S ) $.
    ov2gf.5 $e |- F = ( x e. C , y e. D |-> R ) $.
    $( The value of an operation class abstraction.  A version of ~ ovmpt2g
       using bound-variable hypotheses.  (Contributed by NM, 17-Aug-2006.)
       (Revised by Mario Carneiro, 19-Dec-2013.) $)
    ov2gf $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $=
      cA cC wcel cB cD wcel cS cH wcel cA cB cF co cS wceq cS cH wcel cS cvv
      wcel cA cC wcel cB cD wcel wa cA cB cF co cS wceq cS cH elex cR cvv wcel
      vx cv vy cv cF co cR wceq wi cG cvv wcel cA vy cv cF co cG wceq wi cS cvv
      wcel cA cB cF co cS wceq wi vx vy cA cB cC cD ov2gf.a ov2gf.c ov2gf.d cG
      cvv wcel cA vy cv cF co cG wceq vx vx cG cvv ov2gf.1 nfel1 vx cA vy cv cF
      co cG vx cA vy cv cF ov2gf.a vx cF vx vy cC cD cR cmpt2 ov2gf.5 vx vy cC
      cD cR nfmpt21 nfcxfr vx vy cv nfcv nfov ov2gf.1 nfeq nfim cS cvv wcel cA
      cB cF co cS wceq vy vy cS cvv ov2gf.2 nfel1 vy cA cB cF co cS vy cA cB cF
      ov2gf.c vy cF vx vy cC cD cR cmpt2 ov2gf.5 vx vy cC cD cR nfmpt22 nfcxfr
      ov2gf.d nfov ov2gf.2 nfeq nfim vx cv cA wceq cR cvv wcel cG cvv wcel vx
      cv vy cv cF co cR wceq cA vy cv cF co cG wceq vx cv cA wceq cR cG cvv
      ov2gf.3 eleq1d vx cv cA wceq vx cv vy cv cF co cA vy cv cF co cR cG vx cv
      cA vy cv cF oveq1 ov2gf.3 eqeq12d imbi12d vy cv cB wceq cG cvv wcel cS
      cvv wcel cA vy cv cF co cG wceq cA cB cF co cS wceq vy cv cB wceq cG cS
      cvv ov2gf.4 eleq1d vy cv cB wceq cA vy cv cF co cA cB cF co cG cS vy cv
      cB cA cF oveq2 ov2gf.4 eqeq12d imbi12d vx cv cC wcel vy cv cD wcel cR cvv
      wcel vx cv vy cv cF co cR wceq vx vy cC cD cR cF cvv ov2gf.5 ovmpt4g
      3expia vtocl2gaf syl5 3impia $.
  $}

  ${
    $d x y z $.  $d x z A $.  $d y z B $.  $d z C $.  $d z D $.  $d z R $.
    $d z S $.
    ovmpt2dx.1 $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
    ovmpt2dx.2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
    ovmpt2dx.3 $e |- ( ( ph /\ x = A ) -> D = L ) $.
    ovmpt2dx.4 $e |- ( ph -> A e. C ) $.
    ovmpt2dx.5 $e |- ( ph -> B e. L ) $.
    ovmpt2dx.6 $e |- ( ph -> S e. X ) $.
    ${
      ovmpt2dxf.px $e |- F/ x ph $.
      ovmpt2dxf.py $e |- F/ y ph $.
      ovmpt2dxf.ay $e |- F/_ y A $.
      ovmpt2dxf.bx $e |- F/_ x B $.
      ovmpt2dxf.sx $e |- F/_ x S $.
      ovmpt2dxf.sy $e |- F/_ y S $.
      $( Value of an operation given by a maps-to rule, deduction form.
         (Contributed by Mario Carneiro, 29-Dec-2014.) $)
      ovmpt2dxf $p |- ( ph -> ( A F B ) = S ) $=
        wph cA cB cF co cA cB vx vy cC cD cR cmpt2 co cS wph cF vx vy cC cD cR
        cmpt2 cA cB ovmpt2dx.1 oveqd wph vx cv cC wcel vy cv cD wcel cR cvv
        wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq wi vy cB wsbc vx
        cA wsbc cA cB vx vy cC cD cR cmpt2 co cS wceq wph cA cC wcel vx cv cC
        wcel vy cv cD wcel cR cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co
        cR wceq wi vy cB wsbc vx wal vx cv cC wcel vy cv cD wcel cR cvv wcel
        w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq wi vy cB wsbc vx cA
        wsbc ovmpt2dx.4 wph vx cv cC wcel vy cv cD wcel cR cvv wcel w3a vx cv
        vy cv vx vy cC cD cR cmpt2 co cR wceq wi vy cB wsbc vx ovmpt2dxf.px wph
        cB cL wcel vx cv cC wcel vy cv cD wcel cR cvv wcel w3a vx cv vy cv vx
        vy cC cD cR cmpt2 co cR wceq wi vy wal vx cv cC wcel vy cv cD wcel cR
        cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq wi vy cB wsbc
        ovmpt2dx.5 wph vx cv cC wcel vy cv cD wcel cR cvv wcel w3a vx cv vy cv
        vx vy cC cD cR cmpt2 co cR wceq wi vy ovmpt2dxf.py vx cv cC wcel vy cv
        cD wcel cR cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq wi
        wph vx vy cC cD cR vx vy cC cD cR cmpt2 cvv vx vy cC cD cR cmpt2 eqid
        ovmpt4g a1i alrimi vx cv cC wcel vy cv cD wcel cR cvv wcel w3a vx cv vy
        cv vx vy cC cD cR cmpt2 co cR wceq wi vy cB cL spsbc sylc alrimi vx cv
        cC wcel vy cv cD wcel cR cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2
        co cR wceq wi vy cB wsbc vx cA cC spsbc sylc wph vx cv cC wcel vy cv cD
        wcel cR cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq wi vy
        cB wsbc cA cB vx vy cC cD cR cmpt2 co cS wceq vx cA cC ovmpt2dx.4 wph
        vx cv cA wceq wa vx cv cC wcel vy cv cD wcel cR cvv wcel w3a vx cv vy
        cv vx vy cC cD cR cmpt2 co cR wceq wi cA cB vx vy cC cD cR cmpt2 co cS
        wceq vy cB cL wph cB cL wcel vx cv cA wceq ovmpt2dx.5 adantr wph vx cv
        cA wceq wa vy cv cB wceq wa vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq
        vx cv cC wcel vy cv cD wcel cR cvv wcel w3a vx cv vy cv vx vy cC cD cR
        cmpt2 co cR wceq wi cA cB vx vy cC cD cR cmpt2 co cS wceq wph vx cv cA
        wceq wa vy cv cB wceq wa vx cv cC wcel vy cv cD wcel cR cvv wcel vx cv
        vy cv vx vy cC cD cR cmpt2 co cR wceq vx cv cC wcel vy cv cD wcel cR
        cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq wi wb wph vx
        cv cA wceq wa vy cv cB wceq wa vx cv cA cC wph vx cv cA wceq vy cv cB
        wceq simplr wph cA cC wcel vx cv cA wceq vy cv cB wceq ovmpt2dx.4
        ad2antrr eqeltrd wph vx cv cA wceq wa vy cv cB wceq wa vy cv cD wcel cB
        cL wcel wph cB cL wcel vx cv cA wceq vy cv cB wceq ovmpt2dx.5 ad2antrr
        wph vx cv cA wceq wa vy cv cB wceq wa vy cv cB cD cL wph vx cv cA wceq
        wa vy cv cB wceq simpr wph vx cv cA wceq wa cD cL wceq vy cv cB wceq
        ovmpt2dx.3 adantr eleq12d mpbird wph vx cv cA wceq wa vy cv cB wceq wa
        cR cS cvv wph vx cv cA wceq vy cv cB wceq cR cS wceq ovmpt2dx.2 anassrs
        wph cS cvv wcel vx cv cA wceq vy cv cB wceq wph cS cX wcel cS cvv wcel
        ovmpt2dx.6 cS cX elex syl ad2antrr eqeltrd vx cv cC wcel vy cv cD wcel
        cR cvv wcel w3a vx cv vy cv vx vy cC cD cR cmpt2 co cR wceq biimt
        syl3anc wph vx cv cA wceq wa vy cv cB wceq wa vx cv vy cv vx vy cC cD
        cR cmpt2 co cA cB vx vy cC cD cR cmpt2 co cR cS wph vx cv cA wceq wa vy
        cv cB wceq wa vx cv cA vy cv cB vx vy cC cD cR cmpt2 wph vx cv cA wceq
        vy cv cB wceq simplr wph vx cv cA wceq wa vy cv cB wceq simpr oveq12d
        wph vx cv cA wceq vy cv cB wceq cR cS wceq ovmpt2dx.2 anassrs eqeq12d
        bitr3d wph vx cv cA wceq vy ovmpt2dxf.py vy vx cv cA ovmpt2dxf.ay nfeq2
        nfan cA cB vx vy cC cD cR cmpt2 co cS wceq vy wnf wph vx cv cA wceq wa
        vy cA cB vx vy cC cD cR cmpt2 co cS vy cA cB vx vy cC cD cR cmpt2
        ovmpt2dxf.ay vx vy cC cD cR nfmpt22 vy cB nfcv nfov ovmpt2dxf.sy nfeq
        a1i sbciedf ovmpt2dxf.px cA cB vx vy cC cD cR cmpt2 co cS wceq vx wnf
        wph vx cA cB vx vy cC cD cR cmpt2 co cS vx cA cB vx vy cC cD cR cmpt2
        vx cA nfcv vx vy cC cD cR nfmpt21 ovmpt2dxf.bx nfov ovmpt2dxf.sx nfeq
        a1i sbciedf mpbid eqtrd $.
    $}

    $d y A $.  $d x B $.  $d x y S $.  $d x y ph $.
    $( Value of an operation given by a maps-to rule, deduction form.
       (Contributed by Mario Carneiro, 29-Dec-2014.) $)
    ovmpt2dx $p |- ( ph -> ( A F B ) = S ) $=
      wph vx vy cA cB cC cD cR cS cF cL cX ovmpt2dx.1 ovmpt2dx.2 ovmpt2dx.3
      ovmpt2dx.4 ovmpt2dx.5 ovmpt2dx.6 wph vx nfv wph vy nfv vy cA nfcv vx cB
      nfcv vx cS nfcv vy cS nfcv ovmpt2dxf $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y S $.  $d x y ph $.
    ovmpt2d.1 $e |- ( ph -> F = ( x e. C , y e. D |-> R ) ) $.
    ovmpt2d.2 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
    ovmpt2d.3 $e |- ( ph -> A e. C ) $.
    ovmpt2d.4 $e |- ( ph -> B e. D ) $.
    ovmpt2d.5 $e |- ( ph -> S e. X ) $.
    $( Value of an operation given by a maps-to rule, deduction form.
       (Contributed by Mario Carneiro, 7-Dec-2014.) $)
    ovmpt2d $p |- ( ph -> ( A F B ) = S ) $=
      wph vx vy cA cB cC cD cR cS cF cD cX ovmpt2d.1 ovmpt2d.2 wph vx cv cA
      wceq wa cD eqidd ovmpt2d.3 ovmpt2d.4 ovmpt2d.5 ovmpt2dx $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y L $.  $d x y S $.
    ovmpt2x.1 $e |- ( ( x = A /\ y = B ) -> R = S ) $.
    ovmpt2x.2 $e |- ( x = A -> D = L ) $.
    ovmpt2x.3 $e |- F = ( x e. C , y e. D |-> R ) $.
    $( The value of an operation class abstraction.  Variant of ~ ovmpt2ga
       which does not require ` D ` and ` x ` to be distinct.  (Contributed by
       Jeff Madsen, 10-Jun-2010.)  (Revised by Mario Carneiro, 20-Dec-2013.) $)
    ovmpt2x $p |- ( ( A e. C /\ B e. L /\ S e. H ) -> ( A F B ) = S ) $=
      cS cH wcel cA cC wcel cB cL wcel cS cvv wcel cA cB cF co cS wceq cS cH
      elex cA cC wcel cB cL wcel cS cvv wcel w3a vx vy cA cB cC cD cR cS cF cL
      cvv cF vx vy cC cD cR cmpt2 wceq cA cC wcel cB cL wcel cS cvv wcel w3a
      ovmpt2x.3 a1i vx cv cA wceq vy cv cB wceq wa cR cS wceq cA cC wcel cB cL
      wcel cS cvv wcel w3a ovmpt2x.1 adantl vx cv cA wceq cD cL wceq cA cC wcel
      cB cL wcel cS cvv wcel w3a ovmpt2x.2 adantl cA cC wcel cB cL wcel cS cvv
      wcel simp1 cA cC wcel cB cL wcel cS cvv wcel simp2 cA cC wcel cB cL wcel
      cS cvv wcel simp3 ovmpt2dx syl3an3 $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y S $.
    ovmpt2ga.1 $e |- ( ( x = A /\ y = B ) -> R = S ) $.
    ovmpt2ga.2 $e |- F = ( x e. C , y e. D |-> R ) $.
    $( Value of an operation given by a maps-to rule.  (Contributed by Mario
       Carneiro, 19-Dec-2013.) $)
    ovmpt2ga $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $=
      cS cH wcel cA cC wcel cB cD wcel cS cvv wcel cA cB cF co cS wceq cS cH
      elex cA cC wcel cB cD wcel cS cvv wcel w3a vx vy cA cB cC cD cR cS cF cvv
      cF vx vy cC cD cR cmpt2 wceq cA cC wcel cB cD wcel cS cvv wcel w3a
      ovmpt2ga.2 a1i vx cv cA wceq vy cv cB wceq wa cR cS wceq cA cC wcel cB cD
      wcel cS cvv wcel w3a ovmpt2ga.1 adantl cA cC wcel cB cD wcel cS cvv wcel
      simp1 cA cC wcel cB cD wcel cS cvv wcel simp2 cA cC wcel cB cD wcel cS
      cvv wcel simp3 ovmpt2d syl3an3 $.

    ovmpt2a.4 $e |- S e. _V $.
    $( Value of an operation given by a maps-to rule.  (Contributed by NM,
       19-Dec-2013.) $)
    ovmpt2a $p |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S ) $=
      cA cC wcel cB cD wcel cS cvv wcel cA cB cF co cS wceq ovmpt2a.4 vx vy cA
      cB cC cD cR cS cF cvv ovmpt2ga.1 ovmpt2ga.2 ovmpt2ga mp3an3 $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y ph $.
    ovmpt2df.1 $e |- ( ph -> A e. C ) $.
    ovmpt2df.2 $e |- ( ( ph /\ x = A ) -> B e. D ) $.
    ovmpt2df.3 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
    ovmpt2df.4 $e |- ( ( ph /\ ( x = A /\ y = B ) ) ->
      ( ( A F B ) = R -> ps ) ) $.
    ${
      ovmpt2df.5 $e |- F/_ x F $.
      ovmpt2df.6 $e |- F/ x ps $.
      ovmpt2df.7 $e |- F/_ y F $.
      ovmpt2df.8 $e |- F/ y ps $.
      $( Alternate deduction version of ~ ovmpt2 , suitable for iteration.
         (Contributed by Mario Carneiro, 7-Jan-2017.) $)
      ovmpt2df $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) ) $=
        wph vx cv cA wceq vx wex cF vx vy cC cD cR cmpt2 wceq wps wi wph cA cvv
        wcel vx cv cA wceq vx wex wph cA cC wcel cA cvv wcel ovmpt2df.1 cA cC
        elex syl vx cA isset sylib wph vx cv cA wceq cF vx vy cC cD cR cmpt2
        wceq wps wi vx wph vx nfv cF vx vy cC cD cR cmpt2 wceq wps vx vx cF vx
        vy cC cD cR cmpt2 ovmpt2df.5 vx vy cC cD cR nfmpt21 nfeq ovmpt2df.6
        nfim wph vx cv cA wceq cF vx vy cC cD cR cmpt2 wceq wps wi wph vx cv cA
        wceq wa vy cv cB wceq vy wex cF vx vy cC cD cR cmpt2 wceq wps wi wph vx
        cv cA wceq wa cB cvv wcel vy cv cB wceq vy wex wph vx cv cA wceq wa cB
        cD wcel cB cvv wcel ovmpt2df.2 cB cD elex syl vy cB isset sylib wph vx
        cv cA wceq wa vy cv cB wceq cF vx vy cC cD cR cmpt2 wceq wps wi vy wph
        vx cv cA wceq wa vy nfv cF vx vy cC cD cR cmpt2 wceq wps vy vy cF vx vy
        cC cD cR cmpt2 ovmpt2df.7 vx vy cC cD cR nfmpt22 nfeq ovmpt2df.8 nfim
        wph vx cv cA wceq vy cv cB wceq cF vx vy cC cD cR cmpt2 wceq wps wi cF
        vx vy cC cD cR cmpt2 wceq cA cB cF co cA cB vx vy cC cD cR cmpt2 co
        wceq wph vx cv cA wceq vy cv cB wceq wa wa wps cA cB cF vx vy cC cD cR
        cmpt2 oveq wph vx cv cA wceq vy cv cB wceq wa wa cA cB cF co cA cB vx
        vy cC cD cR cmpt2 co wceq cA cB cF co cR wceq wps wph vx cv cA wceq vy
        cv cB wceq wa wa cA cB vx vy cC cD cR cmpt2 co cR cA cB cF co wph vx cv
        cA wceq vy cv cB wceq wa wa vx cv vy cv vx vy cC cD cR cmpt2 co cA cB
        vx vy cC cD cR cmpt2 co cR wph vx cv cA wceq vy cv cB wceq wa wa vx cv
        cA vy cv cB vx vy cC cD cR cmpt2 wph vx cv cA wceq vy cv cB wceq simprl
        wph vx cv cA wceq vy cv cB wceq simprr oveq12d wph vx cv cA wceq vy cv
        cB wceq wa wa vx cv cC wcel vy cv cD wcel cR cV wcel vx cv vy cv vx vy
        cC cD cR cmpt2 co cR wceq wph vx cv cA wceq vy cv cB wceq wa wa vx cv
        cA cC wph vx cv cA wceq vy cv cB wceq simprl wph cA cC wcel vx cv cA
        wceq vy cv cB wceq wa ovmpt2df.1 adantr eqeltrd wph vx cv cA wceq vy cv
        cB wceq wa wa vy cv cB cD wph vx cv cA wceq vy cv cB wceq simprr wph vx
        cv cA wceq cB cD wcel vy cv cB wceq ovmpt2df.2 adantrr eqeltrd
        ovmpt2df.3 vx vy cC cD cR vx vy cC cD cR cmpt2 cV vx vy cC cD cR cmpt2
        eqid ovmpt4g syl3anc eqtr3d eqeq2d ovmpt2df.4 sylbid syl5 expr exlimd
        mpd ex exlimd mpd $.
    $}

    $d x y F $.  $d x y ps $.
    $( Alternate deduction version of ~ ovmpt2 , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) $)
    ovmpt2dv $p |- ( ph -> ( F = ( x e. C , y e. D |-> R ) -> ps ) ) $=
      wph wps vx vy cA cB cC cD cR cF cV ovmpt2df.1 ovmpt2df.2 ovmpt2df.3
      ovmpt2df.4 vx cF nfcv wps vx nfv vy cF nfcv wps vy nfv ovmpt2df $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ph $.  $d x y S $.
    ovmpt2dv2.1 $e |- ( ph -> A e. C ) $.
    ovmpt2dv2.2 $e |- ( ( ph /\ x = A ) -> B e. D ) $.
    ovmpt2dv2.3 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R e. V ) $.
    ovmpt2dv2.4 $e |- ( ( ph /\ ( x = A /\ y = B ) ) -> R = S ) $.
    $( Alternate deduction version of ~ ovmpt2 , suitable for iteration.
       (Contributed by Mario Carneiro, 7-Jan-2017.) $)
    ovmpt2dv2 $p |- ( ph ->
      ( F = ( x e. C , y e. D |-> R ) -> ( A F B ) = S ) ) $=
      wph cA cB cF co cS wceq cF vx vy cC cD cR cmpt2 wceq cA cB vx vy cC cD cR
      cmpt2 co cS wceq wph vx vy cC cD cR cmpt2 vx vy cC cD cR cmpt2 wceq cA cB
      vx vy cC cD cR cmpt2 co cS wceq wph vx vy cC cD cR cmpt2 eqidd wph cA cB
      vx vy cC cD cR cmpt2 co cS wceq vx vy cA cB cC cD cR vx vy cC cD cR cmpt2
      cV ovmpt2dv2.1 ovmpt2dv2.2 ovmpt2dv2.3 wph vx cv cA wceq vy cv cB wceq wa
      wa cA cB vx vy cC cD cR cmpt2 co cR wceq cA cB vx vy cC cD cR cmpt2 co cS
      wceq wph vx cv cA wceq vy cv cB wceq wa wa cR cS cA cB vx vy cC cD cR
      cmpt2 co ovmpt2dv2.4 eqeq2d biimpd vx vy cC cD cR nfmpt21 vx cA cB vx vy
      cC cD cR cmpt2 co cS vx cA cB vx vy cC cD cR cmpt2 vx cA nfcv vx vy cC cD
      cR nfmpt21 vx cB nfcv nfov nfeq1 vx vy cC cD cR nfmpt22 vy cA cB vx vy cC
      cD cR cmpt2 co cS vy cA cB vx vy cC cD cR cmpt2 vy cA nfcv vx vy cC cD cR
      nfmpt22 vy cB nfcv nfov nfeq1 ovmpt2df mpd cF vx vy cC cD cR cmpt2 wceq
      cA cB cF co cA cB vx vy cC cD cR cmpt2 co cS cA cB cF vx vy cC cD cR
      cmpt2 oveq eqeq1d syl5ibrcom $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y S $.
    ovmpt2g.1 $e |- ( x = A -> R = G ) $.
    ovmpt2g.2 $e |- ( y = B -> G = S ) $.
    ovmpt2g.3 $e |- F = ( x e. C , y e. D |-> R ) $.
    $( Value of an operation given by a maps-to rule.  Special case.
       (Contributed by NM, 14-Sep-1999.)  (Revised by David Abernethy,
       19-Jun-2012.) $)
    ovmpt2g $p |- ( ( A e. C /\ B e. D /\ S e. H ) -> ( A F B ) = S ) $=
      vx vy cA cB cC cD cR cS cF cH vx cv cA wceq vy cv cB wceq cR cG cS
      ovmpt2g.1 ovmpt2g.2 sylan9eq ovmpt2g.3 ovmpt2ga $.

    ovmpt2.4 $e |- S e. _V $.
    $( Value of an operation given by a maps-to rule.  Special case.
       (Contributed by NM, 16-May-1995.)  (Revised by David Abernethy,
       19-Jun-2012.) $)
    ovmpt2 $p |- ( ( A e. C /\ B e. D ) -> ( A F B ) = S ) $=
      cA cC wcel cB cD wcel cS cvv wcel cA cB cF co cS wceq ovmpt2.4 vx vy cA
      cB cC cD cR cS cF cG cvv ovmpt2g.1 ovmpt2g.2 ovmpt2g.3 ovmpt2g mp3an3 $.
  $}

  ${
    $d f t u v w x y z A $.  $d f t u v w x y z B $.  $d t F $.  $d x y z R $.
    $d f t u v w y z C $.  $d f t u v w y z D $.  $d f t u v w x y z H $.
    $d f t u v w z S $.
    ov3.1 $e |- S e. _V $.
    ov3.2 $e |- ( ( ( w = A /\ v = B ) /\ ( u = C /\ f = D ) ) ->
         R = S ) $.
    ov3.3 $e |- F = { <. <. x , y >. , z >. | ( ( x e. ( H X. H ) /\
                      y e. ( H X. H ) ) /\
                      E. w E. v E. u E. f ( ( x = <. w , v >. /\
                      y = <. u , f >. ) /\ z = R ) ) } $.
    $( The value of an operation class abstraction.  Special case.
       (Contributed by NM, 28-May-1995.)  (Revised by Mario Carneiro,
       29-Dec-2014.) $)
    ov3 $p |- ( ( ( A e. H /\ B e. H ) /\ ( C e. H /\ D e. H ) ) ->
        ( <. A , B >. F <. C , D >. ) = S ) $=
      cA cH wcel cB cH wcel wa cC cH wcel cD cH wcel wa wa vz cv cS wceq vz wex
      cA cB cop cC cD cop cF co cS wceq vz cS ov3.1 isseti cA cH wcel cB cH
      wcel wa cC cH wcel cD cH wcel wa wa vz cv cS wceq cA cB cop cC cD cop cF
      co cS wceq vz cA cH wcel cB cH wcel wa cC cH wcel cD cH wcel wa wa vz nfv
      vz cA cB cop cC cD cop cF co cS vz cA cB cop cC cD cop cF vz cA cB cop
      nfcv vz cF vx cv cH cH cxp wcel vy cv cH cH cxp wcel wa vx cv vw cv vv cv
      cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv
      wex vw wex wa vx vy vz coprab ov3.3 vx cv cH cH cxp wcel vy cv cH cH cxp
      wcel wa vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR
      wceq wa vf wex vu wex vv wex vw wex wa vx vy vz nfoprab3 nfcxfr vz cC cD
      cop nfcv nfov nfeq1 vz cv cS wceq cA cB cop cC cD cop cF co vz cv wceq cA
      cB cop cC cD cop cF co cS wceq cA cH wcel cB cH wcel wa cC cH wcel cD cH
      wcel wa wa cA cH wcel cB cH wcel wa cC cH wcel cD cH wcel wa wa vz cv cS
      wceq cA cB cop vw cv vv cv cop wceq cC cD cop vu cv vf cv cop wceq wa vz
      cv cR wceq wa vf wex vu wex vv wex vw wex cA cB cop cC cD cop cF co vz cv
      wceq vz cv cR wceq vz cv cS wceq vw vv vu vf cA cB cC cD cH cH vw cv cA
      wceq vv cv cB wceq wa vu cv cC wceq vf cv cD wceq wa wa cR cS vz cv ov3.2
      eqeq2d copsex4g cA cH wcel cB cH wcel wa cA cB cop cH cH cxp wcel cC cD
      cop cH cH cxp wcel cA cB cop vw cv vv cv cop wceq cC cD cop vu cv vf cv
      cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw wex cA cB cop cC cD
      cop cF co vz cv wceq wi cC cH wcel cD cH wcel wa cA cB cH cH opelxpi cC
      cD cH cH opelxpi vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa
      vz cv cR wceq wa vf wex vu wex vv wex vw wex vx cv vy cv cF co vz cv wceq
      wi cA cB cop vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR
      wceq wa vf wex vu wex vv wex vw wex cA cB cop vy cv cF co vz cv wceq wi
      cA cB cop vw cv vv cv cop wceq cC cD cop vu cv vf cv cop wceq wa vz cv cR
      wceq wa vf wex vu wex vv wex vw wex cA cB cop cC cD cop cF co vz cv wceq
      wi vx vy cA cB cop cC cD cop cH cH cxp cH cH cxp vx cA cB cop nfcv vy cA
      cB cop nfcv vy cC cD cop nfcv cA cB cop vw cv vv cv cop wceq vy cv vu cv
      vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw wex cA cB cop
      vy cv cF co vz cv wceq vx cA cB cop vw cv vv cv cop wceq vy cv vu cv vf
      cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw wex vx nfv vx cA
      cB cop vy cv cF co vz cv vx cA cB cop vy cv cF vx cA cB cop nfcv vx cF vx
      cv cH cH cxp wcel vy cv cH cH cxp wcel wa vx cv vw cv vv cv cop wceq vy
      cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw wex
      wa vx vy vz coprab ov3.3 vx cv cH cH cxp wcel vy cv cH cH cxp wcel wa vx
      cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf
      wex vu wex vv wex vw wex wa vx vy vz nfoprab1 nfcxfr vx vy cv nfcv nfov
      nfeq1 nfim cA cB cop vw cv vv cv cop wceq cC cD cop vu cv vf cv cop wceq
      wa vz cv cR wceq wa vf wex vu wex vv wex vw wex cA cB cop cC cD cop cF co
      vz cv wceq vy cA cB cop vw cv vv cv cop wceq cC cD cop vu cv vf cv cop
      wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw wex vy nfv vy cA cB cop
      cC cD cop cF co vz cv vy cA cB cop cC cD cop cF vy cA cB cop nfcv vy cF
      vx cv cH cH cxp wcel vy cv cH cH cxp wcel wa vx cv vw cv vv cv cop wceq
      vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw
      wex wa vx vy vz coprab ov3.3 vx cv cH cH cxp wcel vy cv cH cH cxp wcel wa
      vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa
      vf wex vu wex vv wex vw wex wa vx vy vz nfoprab2 nfcxfr vy cC cD cop nfcv
      nfov nfeq1 nfim vx cv cA cB cop wceq vx cv vw cv vv cv cop wceq vy cv vu
      cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw wex cA cB
      cop vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa
      vf wex vu wex vv wex vw wex vx cv vy cv cF co vz cv wceq cA cB cop vy cv
      cF co vz cv wceq vx cv cA cB cop wceq vx cv vw cv vv cv cop wceq vy cv vu
      cv vf cv cop wceq wa vz cv cR wceq wa cA cB cop vw cv vv cv cop wceq vy
      cv vu cv vf cv cop wceq wa vz cv cR wceq wa vw vv vu vf vx cv cA cB cop
      wceq vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa cA cB cop
      vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq vx cv cA
      cB cop wceq vx cv vw cv vv cv cop wceq cA cB cop vw cv vv cv cop wceq vy
      cv vu cv vf cv cop wceq vx cv cA cB cop vw cv vv cv cop eqeq1 anbi1d
      anbi1d 4exbidv vx cv cA cB cop wceq vx cv vy cv cF co cA cB cop vy cv cF
      co vz cv vx cv cA cB cop vy cv cF oveq1 eqeq1d imbi12d vy cv cC cD cop
      wceq cA cB cop vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv
      cR wceq wa vf wex vu wex vv wex vw wex cA cB cop vw cv vv cv cop wceq cC
      cD cop vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex vw
      wex cA cB cop vy cv cF co vz cv wceq cA cB cop cC cD cop cF co vz cv wceq
      vy cv cC cD cop wceq cA cB cop vw cv vv cv cop wceq vy cv vu cv vf cv cop
      wceq wa vz cv cR wceq wa cA cB cop vw cv vv cv cop wceq cC cD cop vu cv
      vf cv cop wceq wa vz cv cR wceq wa vw vv vu vf vy cv cC cD cop wceq cA cB
      cop vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa cA cB cop vw cv vv
      cv cop wceq cC cD cop vu cv vf cv cop wceq wa vz cv cR wceq vy cv cC cD
      cop wceq vy cv vu cv vf cv cop wceq cC cD cop vu cv vf cv cop wceq cA cB
      cop vw cv vv cv cop wceq vy cv cC cD cop vu cv vf cv cop eqeq1 anbi2d
      anbi1d 4exbidv vy cv cC cD cop wceq cA cB cop vy cv cF co cA cB cop cC cD
      cop cF co vz cv vy cv cC cD cop cA cB cop cF oveq2 eqeq1d imbi12d vx cv
      vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf
      wex vu wex vv wex vw wex vx vy vz cH cH cxp cH cH cxp cF vx cv vw cv vv
      cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex
      vv wex vw wex vz wmo vx cv cH cH cxp wcel vy cv cH cH cxp wcel wa vx cv
      vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf
      wex vu wex vv wex vw wex vz wmo vx cv vw cv vv cv cop wceq vy cv vu cv vf
      cv cop wceq vz cv cR wceq wa vf wex vu wex wa vv wex vw wex vz wmo vy cv
      vu cv vf cv cop wceq vz cv cR wceq wa vf wex vu wex vz vw vv vx cv vz cv
      cR wceq vz vu vf vy cv vz cR moeq mosubop mosubop vx cv vw cv vv cv cop
      wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vv wex
      vw wex vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR
      wceq wa vf wex vu wex wa vv wex vw wex vz vx cv vw cv vv cv cop wceq vy
      cv vu cv vf cv cop wceq wa vz cv cR wceq wa vf wex vu wex vx cv vw cv vv
      cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq wa vf wex vu wex wa
      vw vv vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR
      wceq wa vf wex vu wex vx cv vw cv vv cv cop wceq vy cv vu cv vf cv cop
      wceq vz cv cR wceq wa wa vf wex vu wex vx cv vw cv vv cv cop wceq vy cv
      vu cv vf cv cop wceq vz cv cR wceq wa vf wex vu wex wa vx cv vw cv vv cv
      cop wceq vy cv vu cv vf cv cop wceq wa vz cv cR wceq wa vx cv vw cv vv cv
      cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq wa wa vu vf vx cv vw cv
      vv cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq anass 2exbii vx
      cv vw cv vv cv cop wceq vy cv vu cv vf cv cop wceq vz cv cR wceq wa vu vf
      19.42vv bitri 2exbii mobii mpbir a1i ov3.3 ovidi vtocl2gaf syl2an sylbird
      vz cv cS cA cB cop cC cD cop cF co eqeq2 mpbidi exlimd mpi $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w x y z C $.  $d w z R $.
    $d w x y z S $.
    ov6g.1 $e |- ( <. x , y >. = <. A , B >. -> R = S ) $.
    ov6g.2 $e |- F = { <. <. x , y >. , z >. | ( <. x , y >. e. C
                      /\ z = R ) } $.
    $( The value of an operation class abstraction.  Special case.
       (Contributed by NM, 13-Nov-2006.) $)
    ov6g $p |- ( ( ( A e. G /\ B e. H /\ <. A , B >. e. C ) /\ S e. J )
                     -> ( A F B ) = S ) $=
      cA cG wcel cB cH wcel cA cB cop cC wcel w3a cS cJ wcel wa cA cB cF co cA
      cB cop cF cfv cS cA cB cF df-ov cA cG wcel cB cH wcel cA cB cop cC wcel
      w3a cS cJ wcel wa cA cB cop vx cv vy cv cop wceq cS cS wceq wa vy wex vx
      wex cA cB cop cF cfv cS wceq cA cG wcel cB cH wcel cA cB cop cC wcel w3a
      cA cB cop vx cv vy cv cop wceq cS cS wceq wa vy wex vx wex cS cJ wcel cA
      cG wcel cB cH wcel cA cB cop vx cv vy cv cop wceq cS cS wceq wa vy wex vx
      wex cA cB cop cC wcel cA cG wcel cB cH wcel wa cA cB cop vx cv vy cv cop
      wceq cS cS wceq wa vy wex vx wex cS cS wceq cS eqid cS cS wceq cS cS wceq
      vx vy cA cB cG cH vx cv cA wceq vy cv cB wceq wa cS cS wceq biidd
      copsex2g mpbiri 3adant3 adantr cA cB cop cC wcel cA cG wcel cS cJ wcel cA
      cB cop vx cv vy cv cop wceq cS cS wceq wa vy wex vx wex cA cB cop cF cfv
      cS wceq wi cB cH wcel vw cv vx cv vy cv cop wceq vz cv cR wceq wa vy wex
      vx wex cA cB cop vx cv vy cv cop wceq vz cv cS wceq wa vy wex vx wex cA
      cB cop vx cv vy cv cop wceq cS cS wceq wa vy wex vx wex vw vz cA cB cop
      cS cC cJ cF vw cv cA cB cop wceq vw cv vx cv vy cv cop wceq vz cv cR wceq
      wa cA cB cop vx cv vy cv cop wceq vz cv cS wceq wa vx vy vw cv cA cB cop
      wceq vw cv vx cv vy cv cop wceq vz cv cR wceq wa cA cB cop vx cv vy cv
      cop wceq vz cv cR wceq wa cA cB cop vx cv vy cv cop wceq vz cv cS wceq wa
      vw cv cA cB cop wceq vw cv vx cv vy cv cop wceq cA cB cop vx cv vy cv cop
      wceq vz cv cR wceq vw cv cA cB cop vx cv vy cv cop eqeq1 anbi1d cA cB cop
      vx cv vy cv cop wceq vz cv cR wceq vz cv cS wceq vz cv cR wceq vz cv cS
      wceq wb vx cv vy cv cop cA cB cop vx cv vy cv cop cA cB cop wceq cR cS vz
      cv ov6g.1 eqeq2d eqcoms pm5.32i syl6bb 2exbidv vz cv cS wceq cA cB cop vx
      cv vy cv cop wceq vz cv cS wceq wa cA cB cop vx cv vy cv cop wceq cS cS
      wceq wa vx vy vz cv cS wceq vz cv cS wceq cS cS wceq cA cB cop vx cv vy
      cv cop wceq vz cv cS cS eqeq1 anbi2d 2exbidv vw cv vx cv vy cv cop wceq
      vz cv cR wceq wa vy wex vx wex vz wmo vw cv cC wcel vz cv cR wceq vz vx
      vy vw cv vz cR moeq mosubop a1i cF vx cv vy cv cop cC wcel vz cv cR wceq
      wa vx vy vz coprab vw cv vx cv vy cv cop wceq vx cv vy cv cop cC wcel vz
      cv cR wceq wa wa vy wex vx wex vw vz copab vw cv cC wcel vw cv vx cv vy
      cv cop wceq vz cv cR wceq wa vy wex vx wex wa vw vz copab ov6g.2 vx cv vy
      cv cop cC wcel vz cv cR wceq wa vx vy vz vw dfoprab2 vw cv vx cv vy cv
      cop wceq vx cv vy cv cop cC wcel vz cv cR wceq wa wa vy wex vx wex vw cv
      cC wcel vw cv vx cv vy cv cop wceq vz cv cR wceq wa vy wex vx wex wa vw
      vz vw cv vx cv vy cv cop wceq vx cv vy cv cop cC wcel vz cv cR wceq wa wa
      vy wex vx wex vw cv cC wcel vw cv vx cv vy cv cop wceq vz cv cR wceq wa
      wa vy wex vx wex vw cv cC wcel vw cv vx cv vy cv cop wceq vz cv cR wceq
      wa vy wex vx wex wa vw cv vx cv vy cv cop wceq vx cv vy cv cop cC wcel vz
      cv cR wceq wa wa vw cv cC wcel vw cv vx cv vy cv cop wceq vz cv cR wceq
      wa wa vx vy vw cv vx cv vy cv cop wceq vx cv vy cv cop cC wcel vz cv cR
      wceq wa wa vw cv vx cv vy cv cop wceq vw cv cC wcel vz cv cR wceq wa wa
      vw cv cC wcel vw cv vx cv vy cv cop wceq vz cv cR wceq wa wa vw cv vx cv
      vy cv cop wceq vw cv cC wcel vz cv cR wceq wa vx cv vy cv cop cC wcel vz
      cv cR wceq wa vw cv vx cv vy cv cop wceq vw cv cC wcel vx cv vy cv cop cC
      wcel vz cv cR wceq vw cv vx cv vy cv cop cC eleq1 anbi1d pm5.32i vw cv vx
      cv vy cv cop wceq vw cv cC wcel vz cv cR wceq an12 bitr3i 2exbii vw cv cC
      wcel vw cv vx cv vy cv cop wceq vz cv cR wceq wa vx vy 19.42vv bitri
      opabbii 3eqtri fvopab3ig 3ad2antl3 mpd syl5eq $.
  $}

  ${
    $d ph c $.  $d ps x $.  $d ch x y $.  $d th x y z $.  $d ta x y c $.
    $d R x y z c $.  $d S x y z c $.  $d A x y z c $.  $d B x y z c $.
    $d C x y z c $.
    ovg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ovg.2 $e |- ( y = B -> ( ps <-> ch ) ) $.
    ovg.3 $e |- ( z = C -> ( ch <-> th ) ) $.
    ovg.4 $e |- ( ( ta /\ ( x e. R /\ y e. S ) ) -> E! z ph ) $.
    ovg.5 $e |- F = { <. <. x , y >. , z >. |
                                            ( ( x e. R /\ y e. S ) /\ ph ) } $.
    $( The value of an operation class abstraction.  (Contributed by Jeff
       Madsen, 10-Jun-2010.) $)
    ovg $p |- ( ( ta /\ ( A e. R /\ B e. S /\ C e. D ) )
                                            -> ( ( A F B ) = C <-> th ) ) $=
      wta cA cR wcel cB cS wcel cC cD wcel w3a wa cA cB cF co cC wceq cA cR
      wcel cB cS wcel wa wth wa wth cA cB cF co cC wceq cA cB cop vx cv cR wcel
      vy cv cS wcel wa wph wa vx vy vz coprab cfv cC wceq wta cA cR wcel cB cS
      wcel cC cD wcel w3a wa cA cR wcel cB cS wcel wa wth wa cA cB cF co cA cB
      cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC cA cB cF
      co cA cB cop cF cfv cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy
      vz coprab cfv cA cB cF df-ov cA cB cop cF vx cv cR wcel vy cv cS wcel wa
      wph wa vx vy vz coprab ovg.5 fveq1i eqtri eqeq1i wta cA cR wcel cB cS
      wcel cC cD wcel w3a wa cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx
      vy vz coprab cfv cC wceq cA cB cop cC cop vx cv cR wcel vy cv cS wcel wa
      wph wa vx vy vz coprab wcel cA cR wcel cB cS wcel wa wth wa wta cA cR
      wcel cB cS wcel cC cD wcel cA cB cop vx cv cR wcel vy cv cS wcel wa wph
      wa vx vy vz coprab cfv cC wceq cA cB cop cC cop vx cv cR wcel vy cv cS
      wcel wa wph wa vx vy vz coprab wcel wb wta cA cR wcel cB cS wcel cC cD
      wcel cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv
      cC wceq cA cB cop cC cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz
      coprab wcel wb wi cC cD wcel wta cA cR wcel cB cS wcel wa wa cA cB cop vx
      cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC wceq cA cB cop
      cC cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab wcel wb wta
      cA cR wcel cB cS wcel wa wa cA cB cop vx cv cR wcel vy cv cS wcel wa wph
      wa vx vy vz coprab cfv vc cv wceq cA cB cop vc cv cop vx cv cR wcel vy cv
      cS wcel wa wph wa vx vy vz coprab wcel wb wi wta cA cR wcel cB cS wcel wa
      wa cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC
      wceq cA cB cop cC cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz
      coprab wcel wb wi vc cC cD vc cv cC wceq cA cB cop vx cv cR wcel vy cv cS
      wcel wa wph wa vx vy vz coprab cfv vc cv wceq cA cB cop vc cv cop vx cv
      cR wcel vy cv cS wcel wa wph wa vx vy vz coprab wcel wb cA cB cop vx cv
      cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv cC wceq cA cB cop cC
      cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab wcel wb wta cA
      cR wcel cB cS wcel wa wa vc cv cC wceq cA cB cop vx cv cR wcel vy cv cS
      wcel wa wph wa vx vy vz coprab cfv vc cv wceq cA cB cop vx cv cR wcel vy
      cv cS wcel wa wph wa vx vy vz coprab cfv cC wceq cA cB cop vc cv cop vx
      cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab wcel cA cB cop cC cop
      vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab wcel vc cv cC cA cB
      cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab cfv eqeq2 vc cv
      cC wceq cA cB cop vc cv cop cA cB cop cC cop vx cv cR wcel vy cv cS wcel
      wa wph wa vx vy vz coprab vc cv cC cA cB cop opeq2 eleq1d bibi12d imbi2d
      wta vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab vx cv cR wcel
      vy cv cS wcel wa vx vy copab wfn cA cB cop vx cv cR wcel vy cv cS wcel wa
      vx vy copab wcel cA cB cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz
      coprab cfv vc cv wceq cA cB cop vc cv cop vx cv cR wcel vy cv cS wcel wa
      wph wa vx vy vz coprab wcel wb cA cR wcel cB cS wcel wa wta vx cv cR wcel
      vy cv cS wcel wa wph vz weu wi vy wal vx wal vx cv cR wcel vy cv cS wcel
      wa wph wa vx vy vz coprab vx cv cR wcel vy cv cS wcel wa vx vy copab wfn
      wta vx cv cR wcel vy cv cS wcel wa wph vz weu wi vx vy wta vx cv cR wcel
      vy cv cS wcel wa wph vz weu ovg.4 ex alrimivv vx cv cR wcel vy cv cS wcel
      wa wph vx vy vz fnoprabg syl cA cR wcel cB cS wcel wa cA cB cop vx cv cR
      wcel vy cv cS wcel wa vx vy copab wcel vx cv cR wcel vy cv cS wcel wa cA
      cR wcel vy cv cS wcel wa cA cR wcel cB cS wcel wa vx vy cA cB cR cS vx cv
      cA wceq vx cv cR wcel cA cR wcel vy cv cS wcel vx cv cA cR eleq1 anbi1d
      vy cv cB wceq vy cv cS wcel cB cS wcel cA cR wcel vy cv cB cS eleq1
      anbi2d opelopabg ibir vx cv cR wcel vy cv cS wcel wa vx vy copab cA cB
      cop vc cv vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab fnopfvb
      syl2an vtoclg com12 exp32 3imp2 cA cR wcel cB cS wcel cC cD wcel w3a cA
      cB cop cC cop vx cv cR wcel vy cv cS wcel wa wph wa vx vy vz coprab wcel
      cA cR wcel cB cS wcel wa wth wa wb wta vx cv cR wcel vy cv cS wcel wa wph
      wa cA cR wcel vy cv cS wcel wa wps wa cA cR wcel cB cS wcel wa wch wa cA
      cR wcel cB cS wcel wa wth wa vx vy vz cA cB cC cR cS cD vx cv cA wceq vx
      cv cR wcel vy cv cS wcel wa cA cR wcel vy cv cS wcel wa wph wps vx cv cA
      wceq vx cv cR wcel cA cR wcel vy cv cS wcel vx cv cA cR eleq1 anbi1d
      ovg.1 anbi12d vy cv cB wceq cA cR wcel vy cv cS wcel wa cA cR wcel cB cS
      wcel wa wps wch vy cv cB wceq vy cv cS wcel cB cS wcel cA cR wcel vy cv
      cB cS eleq1 anbi2d ovg.2 anbi12d vz cv cC wceq wch wth cA cR wcel cB cS
      wcel wa ovg.3 anbi2d eloprabg adantl bitrd syl5bb cA cR wcel cB cS wcel
      cC cD wcel w3a cA cR wcel cB cS wcel wa wth wa wth wb wta cA cR wcel cB
      cS wcel cA cR wcel cB cS wcel wa wth wa wth wb cC cD wcel cA cR wcel cB
      cS wcel wa cA cR wcel cB cS wcel wa wth wa wth cA cR wcel cB cS wcel wa
      cA cR wcel cB cS wcel wa wth wa biidd bianabs 3adant3 adantl bitrd $.
  $}

  $( The value of a restricted operation.  (Contributed by FL, 10-Nov-2006.) $)
  ovres $p |- ( ( A e. C /\ B e. D ) -> ( A ( F |` ( C X. D ) ) B )
    = ( A F B ) ) $=
    cA cC wcel cB cD wcel wa cA cB cop cF cC cD cxp cres cfv cA cB cop cF cfv
    cA cB cF cC cD cxp cres co cA cB cF co cA cC wcel cB cD wcel wa cA cB cop
    cC cD cxp wcel cA cB cop cF cC cD cxp cres cfv cA cB cop cF cfv wceq cA cB
    cC cD opelxpi cA cB cop cC cD cxp cF fvres syl cA cB cF cC cD cxp cres
    df-ov cA cB cF df-ov 3eqtr4g $.

  ${
    ovresd.1 $e |- ( ph -> A e. X ) $.
    ovresd.2 $e |- ( ph -> B e. X ) $.
    $( Lemma for converting metric theorems to metric space theorems.
       (Contributed by Mario Carneiro, 2-Oct-2015.) $)
    ovresd $p |- ( ph -> ( A ( D |` ( X X. X ) ) B ) = ( A D B ) ) $=
      wph cA cX wcel cB cX wcel cA cB cD cX cX cxp cres co cA cB cD co wceq
      ovresd.1 ovresd.2 cA cB cX cX cD ovres syl2anc $.
  $}

  $( The value of a member of the domain of a subclass of an operation.
     (Contributed by NM, 23-Aug-2007.) $)
  oprssov $p |- ( ( ( Fun F /\ G Fn ( C X. D ) /\ G C_ F ) /\
        ( A e. C /\ B e. D ) ) -> ( A F B ) = ( A G B ) ) $=
    cF wfun cG cC cD cxp wfn cG cF wss w3a cA cC wcel cB cD wcel wa wa cA cB cF
    cC cD cxp cres co cA cB cF co cA cB cG co cA cC wcel cB cD wcel wa cA cB cF
    cC cD cxp cres co cA cB cF co wceq cF wfun cG cC cD cxp wfn cG cF wss w3a
    cA cB cC cD cF ovres adantl cF wfun cG cC cD cxp wfn cG cF wss w3a cA cB cF
    cC cD cxp cres co cA cB cG co wceq cA cC wcel cB cD wcel wa cF wfun cG cC
    cD cxp wfn cG cF wss w3a cF cC cD cxp cres cG cA cB cF wfun cG cC cD cxp
    wfn cG cF wss w3a cF cG cdm cres cF cC cD cxp cres cG cG cC cD cxp wfn cF
    wfun cF cG cdm cres cF cC cD cxp cres wceq cG cF wss cG cC cD cxp wfn cG
    cdm cC cD cxp cF cC cD cxp cG fndm reseq2d 3ad2ant2 cF wfun cG cF wss cF cG
    cdm cres cG wceq cG cC cD cxp wfn cF cG funssres 3adant2 eqtr3d oveqd
    adantr eqtr3d $.

  $( An operation's value belongs to its codomain.  (Contributed by NM,
     27-Aug-2006.) $)
  fovrn $p |- ( ( F : ( R X. S ) --> C /\ A e. R /\ B e. S ) ->
               ( A F B ) e. C ) $=
    cR cS cxp cC cF wf cA cR wcel cB cS wcel cA cB cF co cC wcel cA cR wcel cB
    cS wcel wa cR cS cxp cC cF wf cA cB cop cR cS cxp wcel cA cB cF co cC wcel
    cA cB cR cS opelxpi cR cS cxp cC cF wf cA cB cop cR cS cxp wcel wa cA cB cF
    co cA cB cop cF cfv cC cA cB cF df-ov cR cS cxp cC cA cB cop cF ffvelrn
    syl5eqel sylan2 3impb $.

  ${
    fovrnd.1 $e |- ( ph -> F : ( R X. S ) --> C ) $.
    $( An operation's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) $)
    fovrnda $p |- ( ( ph /\ ( A e. R /\ B e. S ) ) -> ( A F B ) e. C ) $=
      wph cA cR wcel cB cS wcel cA cB cF co cC wcel wph cR cS cxp cC cF wf cA
      cR wcel cB cS wcel cA cB cF co cC wcel fovrnd.1 cA cB cC cR cS cF fovrn
      syl3an1 3expb $.

    fovrnd.2 $e |- ( ph -> A e. R ) $.
    fovrnd.3 $e |- ( ph -> B e. S ) $.
    $( An operation's value belongs to its codomain.  (Contributed by Mario
       Carneiro, 29-Dec-2016.) $)
    fovrnd $p |- ( ph -> ( A F B ) e. C ) $=
      wph cR cS cxp cC cF wf cA cR wcel cB cS wcel cA cB cF co cC wcel fovrnd.1
      fovrnd.2 fovrnd.3 cA cB cC cR cS cF fovrn syl3anc $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w z C $.  $d w x y z F $.
    $( The range of an operation expressed as a collection of the operation's
       values.  (Contributed by NM, 29-Oct-2006.) $)
    fnrnov $p |- ( F Fn ( A X. B ) -> ran F = { z | E. x e. A E. y e. B
                     z = ( x F y ) } ) $=
      cF cA cB cxp wfn cF crn vz cv vw cv cF cfv wceq vw cA cB cxp wrex vz cab
      vz cv vx cv vy cv cF co wceq vy cB wrex vx cA wrex vz cab vw vz cA cB cxp
      cF fnrnfv vz cv vw cv cF cfv wceq vw cA cB cxp wrex vz cv vx cv vy cv cF
      co wceq vy cB wrex vx cA wrex vz vz cv vw cv cF cfv wceq vz cv vx cv vy
      cv cF co wceq vw vx vy cA cB vw cv vx cv vy cv cop wceq vw cv cF cfv vx
      cv vy cv cF co vz cv vw cv vx cv vy cv cop wceq vw cv cF cfv vx cv vy cv
      cop cF cfv vx cv vy cv cF co vw cv vx cv vy cv cop cF fveq2 vx cv vy cv
      cF df-ov syl6eqr eqeq2d rexxp abbii syl6eq $.

    $( An onto mapping of an operation expressed in terms of operation values.
       (Contributed by NM, 29-Oct-2006.) $)
    foov $p |- ( F : ( A X. B ) -onto-> C <-> ( F : ( A X. B ) --> C /\
                  A. z e. C E. x e. A E. y e. B z = ( x F y ) ) ) $=
      cA cB cxp cC cF wfo cA cB cxp cC cF wf vz cv vw cv cF cfv wceq vw cA cB
      cxp wrex vz cC wral wa cA cB cxp cC cF wf vz cv vx cv vy cv cF co wceq vy
      cB wrex vx cA wrex vz cC wral wa vw vz cA cB cxp cC cF dffo3 vz cv vw cv
      cF cfv wceq vw cA cB cxp wrex vz cC wral vz cv vx cv vy cv cF co wceq vy
      cB wrex vx cA wrex vz cC wral cA cB cxp cC cF wf vz cv vw cv cF cfv wceq
      vw cA cB cxp wrex vz cv vx cv vy cv cF co wceq vy cB wrex vx cA wrex vz
      cC vz cv vw cv cF cfv wceq vz cv vx cv vy cv cF co wceq vw vx vy cA cB vw
      cv vx cv vy cv cop wceq vw cv cF cfv vx cv vy cv cF co vz cv vw cv vx cv
      vy cv cop wceq vw cv cF cfv vx cv vy cv cop cF cfv vx cv vy cv cF co vw
      cv vx cv vy cv cop cF fveq2 vx cv vy cv cF df-ov syl6eqr eqeq2d rexxp
      ralbii anbi2i bitri $.
  $}

  $( An operation's value belongs to its range.  (Contributed by NM,
     10-Feb-2007.) $)
  fnovrn $p |- ( ( F Fn ( A X. B ) /\ C e. A /\ D e. B ) ->
                   ( C F D ) e. ran F ) $=
    cF cA cB cxp wfn cC cA wcel cD cB wcel cC cD cF co cF crn wcel cC cA wcel
    cD cB wcel wa cF cA cB cxp wfn cC cD cop cA cB cxp wcel cC cD cF co cF crn
    wcel cC cD cA cB opelxpi cF cA cB cxp wfn cC cD cop cA cB cxp wcel wa cC cD
    cF co cC cD cop cF cfv cF crn cC cD cF df-ov cA cB cxp cC cD cop cF
    fnfvelrn syl5eqel sylan2 3impb $.

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.  $d x y z F $.
    $( A member of an operation's range is a value of the operation.
       (Contributed by NM, 7-Feb-2007.)  (Revised by Mario Carneiro,
       30-Jan-2014.) $)
    ovelrn $p |- ( F Fn ( A X. B ) -> ( C e. ran F <->
                  E. x e. A E. y e. B C = ( x F y ) ) ) $=
      cF cA cB cxp wfn cC cF crn wcel cC vz cv vx cv vy cv cF co wceq vy cB
      wrex vx cA wrex vz cab wcel cC vx cv vy cv cF co wceq vy cB wrex vx cA
      wrex cF cA cB cxp wfn cF crn vz cv vx cv vy cv cF co wceq vy cB wrex vx
      cA wrex vz cab cC vx vy vz cA cB cF fnrnov eleq2d vz cv vx cv vy cv cF co
      wceq vy cB wrex vx cA wrex cC vx cv vy cv cF co wceq vy cB wrex vx cA
      wrex vz cC cC vx cv vy cv cF co wceq vy cB wrex cC cvv wcel vx cA cC vx
      cv vy cv cF co wceq cC cvv wcel vy cB cC vx cv vy cv cF co wceq cC cvv
      wcel vx cv vy cv cF co cvv wcel vx cv vy cv cF ovex cC vx cv vy cv cF co
      cvv eleq1 mpbiri rexlimivw rexlimivw vz cv cC wceq vz cv vx cv vy cv cF
      co wceq cC vx cv vy cv cF co wceq vx vy cA cB vz cv cC vx cv vy cv cF co
      eqeq1 2rexbidv elab3 syl6bb $.

    $( Membership relation for the values of a function whose image is a
       subclass.  (Contributed by Mario Carneiro, 23-Dec-2013.) $)
    funimassov $p |- ( ( Fun F /\ ( A X. B ) C_ dom F ) ->
        ( ( F " ( A X. B ) ) C_ C <-> A. x e. A A. y e. B ( x F y ) e. C ) ) $=
      cF wfun cA cB cxp cF cdm wss wa cF cA cB cxp cima cC wss vz cv cF cfv cC
      wcel vz cA cB cxp wral vx cv vy cv cF co cC wcel vy cB wral vx cA wral vz
      cA cB cxp cC cF funimass4 vz cv cF cfv cC wcel vx cv vy cv cF co cC wcel
      vz vx vy cA cB vz cv vx cv vy cv cop wceq vz cv cF cfv vx cv vy cv cF co
      cC vz cv vx cv vy cv cop wceq vz cv cF cfv vx cv vy cv cop cF cfv vx cv
      vy cv cF co vz cv vx cv vy cv cop cF fveq2 vx cv vy cv cF df-ov syl6eqr
      eleq1d ralxp syl6bb $.

    $( Operation value in an image.  (Contributed by Mario Carneiro,
       23-Dec-2013.)  (Revised by Mario Carneiro, 29-Jan-2014.) $)
    ovelimab $p |- ( ( F Fn A /\ ( B X. C ) C_ A ) ->
        ( D e. ( F " ( B X. C ) ) <-> E. x e. B E. y e. C D = ( x F y ) ) ) $=
      cF cA wfn cB cC cxp cA wss wa cD cF cB cC cxp cima wcel vz cv cF cfv cD
      wceq vz cB cC cxp wrex cD vx cv vy cv cF co wceq vy cC wrex vx cB wrex vz
      cA cB cC cxp cD cF fvelimab vz cv cF cfv cD wceq cD vx cv vy cv cF co
      wceq vz vx vy cB cC vz cv vx cv vy cv cop wceq vz cv cF cfv cD wceq vx cv
      vy cv cF co cD wceq cD vx cv vy cv cF co wceq vz cv vx cv vy cv cop wceq
      vz cv cF cfv vx cv vy cv cF co cD vz cv vx cv vy cv cop wceq vz cv cF cfv
      vx cv vy cv cop cF cfv vx cv vy cv cF co vz cv vx cv vy cv cop cF fveq2
      vx cv vy cv cF df-ov syl6eqr eqeq1d vx cv vy cv cF co cD eqcom syl6bb
      rexxp syl6bb $.
  $}

  ${
    oprvalconst2.1 $e |- C e. _V $.
    $( The value of a constant operation.  (Contributed by NM, 5-Nov-2006.) $)
    ovconst2 $p |- ( ( R e. A /\ S e. B ) ->
                       ( R ( ( A X. B ) X. { C } ) S ) = C ) $=
      cR cA wcel cS cB wcel wa cR cS cA cB cxp cC csn cxp co cR cS cop cA cB
      cxp cC csn cxp cfv cC cR cS cA cB cxp cC csn cxp df-ov cR cA wcel cS cB
      wcel wa cR cS cop cA cB cxp wcel cR cS cop cA cB cxp cC csn cxp cfv cC
      wceq cR cS cA cB opelxpi cA cB cxp cC cR cS cop oprvalconst2.1 fvconst2
      syl syl5eq $.
  $}

  ${
    $d x z A $.  $d y z B $.  $d z C $.
    ab2rexex.1 $e |- A e. _V $.
    ab2rexex.2 $e |- B e. _V $.
    $( Existence of a class abstraction of existentially restricted sets.
       Variables ` x ` and ` y ` are normally free-variable parameters in the
       class expression substituted for ` C ` , which can be thought of as
       ` C ( x , y ) ` .  See comments for ~ abrexex .  (Contributed by NM,
       20-Sep-2011.) $)
    ab2rexex $p |- { z | E. x e. A E. y e. B z = C } e. _V $=
      vz cv cC wceq vy cB wrex vx vz cA ab2rexex.1 vy vz cB cC ab2rexex.2
      abrexex abrexex2 $.
  $}

  ${
    $d x z A $.  $d y z B $.
    ab2rexex2.1 $e |- A e. _V $.
    ab2rexex2.2 $e |- B e. _V $.
    ab2rexex2.3 $e |- { z | ph } e. _V $.
    $( Existence of an existentially restricted class abstraction. ` ph ` is
       normally has free-variable parameters ` x ` , ` y ` , and ` z ` .
       Compare ~ abrexex2 .  (Contributed by NM, 20-Sep-2011.) $)
    ab2rexex2 $p |- { z | E. x e. A E. y e. B ph } e. _V $=
      wph vy cB wrex vx vz cA ab2rexex2.1 wph vy vz cB ab2rexex2.2 ab2rexex2.3
      abrexex2 abrexex2 $.
  $}

  ${
    $d x y S $.  $d x y F $.
    oprssdm.1 $e |- -. (/) e. S $.
    oprssdm.2 $e |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S ) $.
    $( Domain of closure of an operation.  (Contributed by NM, 24-Aug-1995.) $)
    oprssdm $p |- ( S X. S ) C_ dom F $=
      vx vy cS cS cxp cF cdm cS cS relxp vx cv vy cv cop cS cS cxp wcel vx cv
      cS wcel vy cv cS wcel wa vx cv vy cv cop cF cdm wcel vx cv vy cv cS cS
      opelxp vx cv cS wcel vy cv cS wcel wa vx cv vy cv cop cF cfv cS wcel vx
      cv vy cv cop cF cdm wcel vx cv cS wcel vy cv cS wcel wa vx cv vy cv cop
      cF cfv vx cv vy cv cF co cS vx cv vy cv cF df-ov oprssdm.2 syl5eqelr vx
      cv vy cv cop cF cdm wcel vx cv vy cv cop cF cfv cS wcel vx cv vy cv cop
      cF cdm wcel wn vx cv vy cv cop cF cfv cS wcel c0 cS wcel oprssdm.1 vx cv
      vy cv cop cF cdm wcel wn vx cv vy cv cop cF cfv c0 cS vx cv vy cv cop cF
      ndmfv eleq1d mtbiri con4i syl sylbi relssi $.
  $}

  $( The value of an operation outside its domain.  (Contributed by NM,
     28-Mar-2008.) $)
  ndmovg $p |- ( ( dom F = ( R X. S ) /\ -. ( A e. R /\ B e. S ) )
              -> ( A F B ) = (/) ) $=
    cF cdm cR cS cxp wceq cA cR wcel cB cS wcel wa wn wa cA cB cF co cA cB cop
    cF cfv c0 cA cB cF df-ov cF cdm cR cS cxp wceq cA cR wcel cB cS wcel wa wn
    cA cB cop cF cfv c0 wceq cF cdm cR cS cxp wceq cA cR wcel cB cS wcel wa wn
    cA cB cop cF cdm wcel wn cA cB cop cF cfv c0 wceq cF cdm cR cS cxp wceq cA
    cB cop cF cdm wcel cA cR wcel cB cS wcel wa cF cdm cR cS cxp wceq cA cB cop
    cF cdm wcel cA cB cop cR cS cxp wcel cA cR wcel cB cS wcel wa cF cdm cR cS
    cxp cA cB cop eleq2 cA cB cR cS opelxp syl6bb notbid cA cB cop cF ndmfv
    syl6bir imp syl5eq $.

  ${
    ndmov.1 $e |- dom F = ( S X. S ) $.
    $( The value of an operation outside its domain.  (Contributed by NM,
       24-Aug-1995.) $)
    ndmov $p |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = (/) ) $=
      cF cdm cS cS cxp wceq cA cS wcel cB cS wcel wa wn cA cB cF co c0 wceq
      ndmov.1 cA cB cS cS cF ndmovg mpan $.

    ${
      ndmovcl.2 $e |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S ) $.
      ndmovcl.3 $e |- (/) e. S $.
      $( The closure of an operation outside its domain, when the domain
         includes the empty set.  This technical lemma can make the operation
         more convenient to work in some cases.  It is dependent on our
         particular definitions of operation value, function value, and ordered
         pair.  (Contributed by NM, 24-Sep-2004.) $)
      ndmovcl $p |- ( A F B ) e. S $=
        cA cS wcel cB cS wcel wa cA cB cF co cS wcel ndmovcl.2 cA cS wcel cB cS
        wcel wa wn cA cB cF co c0 cS cA cB cS cF ndmov.1 ndmov ndmovcl.3
        syl6eqel pm2.61i $.
    $}

    ${
      ndmovrcl.3 $e |- -. (/) e. S $.
      $( Reverse closure law, when an operation's domain doesn't contain the
         empty set.  (Contributed by NM, 3-Feb-1996.) $)
      ndmovrcl $p |- ( ( A F B ) e. S -> ( A e. S /\ B e. S ) ) $=
        cA cS wcel cB cS wcel wa cA cB cF co cS wcel cA cS wcel cB cS wcel wa
        wn cA cB cF co cS wcel c0 cS wcel ndmovrcl.3 cA cS wcel cB cS wcel wa
        wn cA cB cF co c0 cS cA cB cS cF ndmov.1 ndmov eleq1d mtbiri con4i $.
    $}

    $( Any operation is commutative outside its domain.  (Contributed by NM,
       24-Aug-1995.) $)
    ndmovcom $p |- ( -. ( A e. S /\ B e. S ) -> ( A F B ) = ( B F A ) ) $=
      cA cS wcel cB cS wcel wa wn cA cB cF co c0 cB cA cF co cA cB cS cF
      ndmov.1 ndmov cA cS wcel cB cS wcel wa cB cS wcel cA cS wcel wa cB cA cF
      co c0 wceq cA cS wcel cB cS wcel ancom cB cA cS cF ndmov.1 ndmov sylnbi
      eqtr4d $.

    ${
      ndmov.5 $e |- -. (/) e. S $.
      $( Any operation is associative outside its domain, if the domain doesn't
         contain the empty set.  (Contributed by NM, 24-Aug-1995.) $)
      ndmovass $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) ->
              ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $=
        cA cS wcel cB cS wcel cC cS wcel w3a wn cA cB cF co cC cF co c0 cA cB
        cC cF co cF co cA cS wcel cB cS wcel cC cS wcel w3a wn cA cB cF co cS
        wcel cC cS wcel wa wn cA cB cF co cC cF co c0 wceq cA cB cF co cS wcel
        cC cS wcel wa cA cS wcel cB cS wcel cC cS wcel w3a cA cB cF co cS wcel
        cC cS wcel wa cA cS wcel cB cS wcel wa cC cS wcel wa cA cS wcel cB cS
        wcel cC cS wcel w3a cA cB cF co cS wcel cA cS wcel cB cS wcel wa cC cS
        wcel cA cB cS cF ndmov.1 ndmov.5 ndmovrcl anim1i cA cS wcel cB cS wcel
        cC cS wcel df-3an sylibr con3i cA cB cF co cC cS cF ndmov.1 ndmov syl
        cA cS wcel cB cS wcel cC cS wcel w3a wn cA cS wcel cB cC cF co cS wcel
        wa wn cA cB cC cF co cF co c0 wceq cA cS wcel cB cC cF co cS wcel wa cA
        cS wcel cB cS wcel cC cS wcel w3a cA cS wcel cB cC cF co cS wcel wa cA
        cS wcel cB cS wcel cC cS wcel wa wa cA cS wcel cB cS wcel cC cS wcel
        w3a cB cC cF co cS wcel cB cS wcel cC cS wcel wa cA cS wcel cB cC cS cF
        ndmov.1 ndmov.5 ndmovrcl anim2i cA cS wcel cB cS wcel cC cS wcel 3anass
        sylibr con3i cA cB cC cF co cS cF ndmov.1 ndmov syl eqtr4d $.

      ndmov.6 $e |- dom G = ( S X. S ) $.
      $( Any operation is distributive outside its domain, if the domain
         doesn't contain the empty set.  (Contributed by NM, 24-Aug-1995.) $)
      ndmovdistr $p |- ( -. ( A e. S /\ B e. S /\ C e. S ) ->
          ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) ) $=
        cA cS wcel cB cS wcel cC cS wcel w3a wn cA cB cC cF co cG co c0 cA cB
        cG co cA cC cG co cF co cA cS wcel cB cS wcel cC cS wcel w3a wn cA cS
        wcel cB cC cF co cS wcel wa wn cA cB cC cF co cG co c0 wceq cA cS wcel
        cB cC cF co cS wcel wa cA cS wcel cB cS wcel cC cS wcel w3a cA cS wcel
        cB cC cF co cS wcel wa cA cS wcel cB cS wcel cC cS wcel wa wa cA cS
        wcel cB cS wcel cC cS wcel w3a cB cC cF co cS wcel cB cS wcel cC cS
        wcel wa cA cS wcel cB cC cS cF ndmov.1 ndmov.5 ndmovrcl anim2i cA cS
        wcel cB cS wcel cC cS wcel 3anass sylibr con3i cA cB cC cF co cS cG
        ndmov.6 ndmov syl cA cS wcel cB cS wcel cC cS wcel w3a wn cA cB cG co
        cS wcel cA cC cG co cS wcel wa wn cA cB cG co cA cC cG co cF co c0 wceq
        cA cB cG co cS wcel cA cC cG co cS wcel wa cA cS wcel cB cS wcel cC cS
        wcel w3a cA cB cG co cS wcel cA cC cG co cS wcel wa cA cS wcel cB cS
        wcel wa cA cS wcel cC cS wcel wa wa cA cS wcel cB cS wcel cC cS wcel
        w3a cA cB cG co cS wcel cA cS wcel cB cS wcel wa cA cC cG co cS wcel cA
        cS wcel cC cS wcel wa cA cB cS cG ndmov.6 ndmov.5 ndmovrcl cA cC cS cG
        ndmov.6 ndmov.5 ndmovrcl anim12i cA cS wcel cB cS wcel cC cS wcel w3a
        cA cS wcel cB cS wcel cC cS wcel wa wa cA cS wcel cB cS wcel wa cA cS
        wcel cC cS wcel wa wa cA cS wcel cB cS wcel cC cS wcel 3anass cA cS
        wcel cB cS wcel cC cS wcel anandi bitri sylibr con3i cA cB cG co cA cC
        cG co cS cF ndmov.1 ndmov syl eqtr4d $.
    $}

    ndmovord.4 $e |- R C_ ( S X. S ) $.
    ndmovord.5 $e |- -. (/) e. S $.
    ndmovord.6 $e |- ( ( A e. S /\ B e. S /\ C e. S ) ->
                   ( A R B <-> ( C F A ) R ( C F B ) ) ) $.
    $( Elimination of redundant antecedents in an ordering law.  (Contributed
       by NM, 7-Mar-1996.) $)
    ndmovord $p |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $=
      cA cS wcel cB cS wcel wa cC cS wcel cA cB cR wbr cC cA cF co cC cB cF co
      cR wbr wb wi cA cS wcel cB cS wcel cC cS wcel cA cB cR wbr cC cA cF co cC
      cB cF co cR wbr wb ndmovord.6 3expia cA cS wcel cB cS wcel wa wn cA cB cR
      wbr cC cA cF co cC cB cF co cR wbr wb cC cS wcel cA cB cR wbr cA cS wcel
      cB cS wcel wa cC cA cF co cC cB cF co cR wbr cA cB cS cS cR ndmovord.4
      brel cC cA cF co cC cB cF co cR wbr cC cA cF co cS wcel cC cB cF co cS
      wcel wa cA cS wcel cB cS wcel wa cC cA cF co cC cB cF co cS cS cR
      ndmovord.4 brel cC cA cF co cS wcel cA cS wcel cC cB cF co cS wcel cB cS
      wcel cC cA cF co cS wcel cC cS wcel cA cS wcel cC cA cS cF ndmov.1
      ndmovord.5 ndmovrcl simprd cC cB cF co cS wcel cC cS wcel cB cS wcel cC
      cB cS cF ndmov.1 ndmovord.5 ndmovrcl simprd anim12i syl pm5.21ni a1d
      pm2.61i $.
  $}

  ${
    ndmovordi.2 $e |- dom F = ( S X. S ) $.
    ndmovordi.4 $e |- R C_ ( S X. S ) $.
    ndmovordi.5 $e |- -. (/) e. S $.
    ndmovordi.6 $e |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $.
    $( Elimination of redundant antecedent in an ordering law.  (Contributed by
       NM, 25-Jun-1998.) $)
    ndmovordi $p |- ( ( C F A ) R ( C F B ) -> A R B ) $=
      cC cS wcel cC cA cF co cC cB cF co cR wbr cA cB cR wbr cC cA cF co cC cB
      cF co cR wbr cC cA cF co cS wcel cC cS wcel cC cA cF co cC cB cF co cR
      wbr cC cA cF co cS wcel cC cB cF co cS wcel cC cA cF co cC cB cF co cS cS
      cR ndmovordi.4 brel simpld cC cA cF co cS wcel cC cS wcel cA cS wcel cC
      cA cS cF ndmovordi.2 ndmovordi.5 ndmovrcl simpld syl cC cS wcel cA cB cR
      wbr cC cA cF co cC cB cF co cR wbr ndmovordi.6 biimprd mpcom $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d x y D $.  $d x y E $.  $d x y ph $.
    $d x y F $.
    caovclg.1 $e |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E ) $.
    $( Convert an operation closure law to class notation.  (Contributed by
       Mario Carneiro, 26-May-2014.) $)
    caovclg $p |- ( ( ph /\ ( A e. C /\ B e. D ) ) -> ( A F B ) e. E ) $=
      wph vx cv vy cv cF co cE wcel vy cD wral vx cC wral cA cC wcel cB cD wcel
      wa cA cB cF co cE wcel wph vx cv vy cv cF co cE wcel vx vy cC cD
      caovclg.1 ralrimivva vx cv vy cv cF co cE wcel cA cB cF co cE wcel cA vy
      cv cF co cE wcel vx vy cA cB cC cD vx cv cA wceq vx cv vy cv cF co cA vy
      cv cF co cE vx cv cA vy cv cF oveq1 eleq1d vy cv cB wceq cA vy cv cF co
      cA cB cF co cE vy cv cB cA cF oveq2 eleq1d rspc2v mpan9 $.

    caovcld.2 $e |- ( ph -> A e. C ) $.
    caovcld.3 $e |- ( ph -> B e. D ) $.
    $( Convert an operation closure law to class notation.  (Contributed by
       Mario Carneiro, 30-Dec-2014.) $)
    caovcld $p |- ( ph -> ( A F B ) e. E ) $=
      wph wph cA cC wcel cB cD wcel cA cB cF co cE wcel wph id caovcld.2
      caovcld.3 wph vx vy cA cB cC cD cE cF caovclg.1 caovclg syl12anc $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y F $.  $d x y ph $.  $d x y S $.
    caovcl.1 $e |- ( ( x e. S /\ y e. S ) -> ( x F y ) e. S ) $.
    $( Convert an operation closure law to class notation.  (Contributed by NM,
       4-Aug-1995.)  (Revised by Mario Carneiro, 26-May-2014.) $)
    caovcl $p |- ( ( A e. S /\ B e. S ) -> ( A F B ) e. S ) $=
      wtru cA cS wcel cB cS wcel wa cA cB cF co cS wcel tru wtru vx vy cA cB cS
      cS cS cF vx cv cS wcel vy cv cS wcel wa vx cv vy cv cF co cS wcel wtru
      caovcl.1 adantl caovclg mpan $.
  $}

  ${
    $( General laws for commutative, associative, distributive operations. $)
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.  $d x y z ph $.
    $d x y z F $.  $d x y z G $.  $d x y z H $.  $d x y z K $.  $d x y z R $.
    $d x y z S $.  $d x y z T $.
    ${
      caovcomg.1 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                          ( x F y ) = ( y F x ) ) $.
      $( Convert an operation commutative law to class notation.  (Contributed
         by Mario Carneiro, 1-Jun-2013.) $)
      caovcomg $p |- ( ( ph /\ ( A e. S /\ B e. S ) ) ->
                        ( A F B ) = ( B F A ) ) $=
        wph vx cv vy cv cF co vy cv vx cv cF co wceq vy cS wral vx cS wral cA
        cS wcel cB cS wcel wa cA cB cF co cB cA cF co wceq wph vx cv vy cv cF
        co vy cv vx cv cF co wceq vx vy cS cS caovcomg.1 ralrimivva vx cv vy cv
        cF co vy cv vx cv cF co wceq cA cB cF co cB cA cF co wceq cA vy cv cF
        co vy cv cA cF co wceq vx vy cA cB cS cS vx cv cA wceq vx cv vy cv cF
        co cA vy cv cF co vy cv vx cv cF co vy cv cA cF co vx cv cA vy cv cF
        oveq1 vx cv cA vy cv cF oveq2 eqeq12d vy cv cB wceq cA vy cv cF co cA
        cB cF co vy cv cA cF co cB cA cF co vy cv cB cA cF oveq2 vy cv cB cA cF
        oveq1 eqeq12d rspc2v mpan9 $.

      caovcomd.2 $e |- ( ph -> A e. S ) $.
      caovcomd.3 $e |- ( ph -> B e. S ) $.
      $( Convert an operation commutative law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovcomd $p |- ( ph -> ( A F B ) = ( B F A ) ) $=
        wph wph cA cS wcel cB cS wcel cA cB cF co cB cA cF co wceq wph id
        caovcomd.2 caovcomd.3 wph vx vy cA cB cS cF caovcomg.1 caovcomg
        syl12anc $.
    $}

    ${
      caovcom.1 $e |- A e. _V $.
      caovcom.2 $e |- B e. _V $.
      caovcom.3 $e |- ( x F y ) = ( y F x ) $.
      $( Convert an operation commutative law to class notation.  (Contributed
         by NM, 26-Aug-1995.)  (Revised by Mario Carneiro, 1-Jun-2013.) $)
      caovcom $p |- ( A F B ) = ( B F A ) $=
        cA cvv wcel cA cvv wcel cB cvv wcel wa cA cB cF co cB cA cF co wceq
        caovcom.1 cA cvv wcel cB cvv wcel caovcom.1 caovcom.2 pm3.2i cA cvv
        wcel vx vy cA cB cvv cF vx cv vy cv cF co vy cv vx cv cF co wceq cA cvv
        wcel vx cv cvv wcel vy cv cvv wcel wa wa caovcom.3 a1i caovcomg mp2an
        $.
    $}

    ${
      caovassg.1 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
        ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
      $( Convert an operation associative law to class notation.  (Contributed
         by Mario Carneiro, 1-Jun-2013.)  (Revised by Mario Carneiro,
         26-May-2014.) $)
      caovassg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) ->
          ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $=
        wph vx cv vy cv cF co vz cv cF co vx cv vy cv vz cv cF co cF co wceq vz
        cS wral vy cS wral vx cS wral cA cS wcel cB cS wcel cC cS wcel w3a cA
        cB cF co cC cF co cA cB cC cF co cF co wceq wph vx cv vy cv cF co vz cv
        cF co vx cv vy cv vz cv cF co cF co wceq vx vy vz cS cS cS caovassg.1
        ralrimivvva vx cv vy cv cF co vz cv cF co vx cv vy cv vz cv cF co cF co
        wceq cA cB cF co cC cF co cA cB cC cF co cF co wceq cA vy cv cF co vz
        cv cF co cA vy cv vz cv cF co cF co wceq cA cB cF co vz cv cF co cA cB
        vz cv cF co cF co wceq vx vy vz cA cB cC cS cS cS vx cv cA wceq vx cv
        vy cv cF co vz cv cF co cA vy cv cF co vz cv cF co vx cv vy cv vz cv cF
        co cF co cA vy cv vz cv cF co cF co vx cv cA wceq vx cv vy cv cF co cA
        vy cv cF co vz cv cF vx cv cA vy cv cF oveq1 oveq1d vx cv cA vy cv vz
        cv cF co cF oveq1 eqeq12d vy cv cB wceq cA vy cv cF co vz cv cF co cA
        cB cF co vz cv cF co cA vy cv vz cv cF co cF co cA cB vz cv cF co cF co
        vy cv cB wceq cA vy cv cF co cA cB cF co vz cv cF vy cv cB cA cF oveq2
        oveq1d vy cv cB wceq vy cv vz cv cF co cB vz cv cF co cA cF vy cv cB vz
        cv cF oveq1 oveq2d eqeq12d vz cv cC wceq cA cB cF co vz cv cF co cA cB
        cF co cC cF co cA cB vz cv cF co cF co cA cB cC cF co cF co vz cv cC cA
        cB cF co cF oveq2 vz cv cC wceq cB vz cv cF co cB cC cF co cA cF vz cv
        cC cB cF oveq2 oveq2d eqeq12d rspc3v mpan9 $.

      caovassd.2 $e |- ( ph -> A e. S ) $.
      caovassd.3 $e |- ( ph -> B e. S ) $.
      caovassd.4 $e |- ( ph -> C e. S ) $.
      $( Convert an operation associative law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovassd $p |- ( ph -> ( ( A F B ) F C ) = ( A F ( B F C ) ) ) $=
        wph wph cA cS wcel cB cS wcel cC cS wcel cA cB cF co cC cF co cA cB cC
        cF co cF co wceq wph id caovassd.2 caovassd.3 caovassd.4 wph vx vy vz
        cA cB cC cS cF caovassg.1 caovassg syl13anc $.
    $}

    ${
      caovass.1 $e |- A e. _V $.
      caovass.2 $e |- B e. _V $.
      caovass.3 $e |- C e. _V $.
      caovass.4 $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
      $( Convert an operation associative law to class notation.  (Contributed
         by NM, 26-Aug-1995.)  (Revised by Mario Carneiro, 26-May-2014.) $)
      caovass $p |- ( ( A F B ) F C ) = ( A F ( B F C ) ) $=
        cA cvv wcel cB cvv wcel cC cvv wcel cA cB cF co cC cF co cA cB cC cF co
        cF co wceq caovass.1 caovass.2 caovass.3 wtru cA cvv wcel cB cvv wcel
        cC cvv wcel w3a cA cB cF co cC cF co cA cB cC cF co cF co wceq tru wtru
        vx vy vz cA cB cC cvv cF vx cv vy cv cF co vz cv cF co vx cv vy cv vz
        cv cF co cF co wceq wtru vx cv cvv wcel vy cv cvv wcel vz cv cvv wcel
        w3a wa caovass.4 a1i caovassg mpan mp3an $.
    $}

    ${
      caovcang.1 $e |- ( ( ph /\ ( x e. T /\ y e. S /\ z e. S ) ) ->
                         ( ( x F y ) = ( x F z ) <-> y = z ) ) $.
      $( Convert an operation cancellation law to class notation.  (Contributed
         by NM, 20-Aug-1995.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)
      caovcang $p |- ( ( ph /\ ( A e. T /\ B e. S /\ C e. S ) ) ->
                       ( ( A F B ) = ( A F C ) <-> B = C ) ) $=
        wph vx cv vy cv cF co vx cv vz cv cF co wceq vy cv vz cv wceq wb vz cS
        wral vy cS wral vx cT wral cA cT wcel cB cS wcel cC cS wcel w3a cA cB
        cF co cA cC cF co wceq cB cC wceq wb wph vx cv vy cv cF co vx cv vz cv
        cF co wceq vy cv vz cv wceq wb vx vy vz cT cS cS caovcang.1 ralrimivvva
        vx cv vy cv cF co vx cv vz cv cF co wceq vy cv vz cv wceq wb cA cB cF
        co cA cC cF co wceq cB cC wceq wb cA vy cv cF co cA vz cv cF co wceq vy
        cv vz cv wceq wb cA cB cF co cA vz cv cF co wceq cB vz cv wceq wb vx vy
        vz cA cB cC cT cS cS vx cv cA wceq vx cv vy cv cF co vx cv vz cv cF co
        wceq cA vy cv cF co cA vz cv cF co wceq vy cv vz cv wceq vx cv cA wceq
        vx cv vy cv cF co cA vy cv cF co vx cv vz cv cF co cA vz cv cF co vx cv
        cA vy cv cF oveq1 vx cv cA vz cv cF oveq1 eqeq12d bibi1d vy cv cB wceq
        cA vy cv cF co cA vz cv cF co wceq cA cB cF co cA vz cv cF co wceq vy
        cv vz cv wceq cB vz cv wceq vy cv cB wceq cA vy cv cF co cA cB cF co cA
        vz cv cF co vy cv cB cA cF oveq2 eqeq1d vy cv cB vz cv eqeq1 bibi12d vz
        cv cC wceq cA cB cF co cA vz cv cF co wceq cA cB cF co cA cC cF co wceq
        cB vz cv wceq cB cC wceq vz cv cC wceq cA vz cv cF co cA cC cF co cA cB
        cF co vz cv cC cA cF oveq2 eqeq2d vz cv cC cB eqeq2 bibi12d rspc3v
        mpan9 $.

      caovcand.2 $e |- ( ph -> A e. T ) $.
      caovcand.3 $e |- ( ph -> B e. S ) $.
      caovcand.4 $e |- ( ph -> C e. S ) $.
      $( Convert an operation cancellation law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovcand $p |- ( ph -> ( ( A F B ) = ( A F C ) <-> B = C ) ) $=
        wph wph cA cT wcel cB cS wcel cC cS wcel cA cB cF co cA cC cF co wceq
        cB cC wceq wb wph id caovcand.2 caovcand.3 caovcand.4 wph vx vy vz cA
        cB cC cS cT cF caovcang.1 caovcang syl13anc $.

      caovcanrd.5 $e |- ( ph -> A e. S ) $.
      caovcanrd.6 $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                          ( x F y ) = ( y F x ) ) $.
      $( Commute the arguments of an operation cancellation law.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovcanrd $p |- ( ph -> ( ( B F A ) = ( C F A ) <-> B = C ) ) $=
        wph cA cB cF co cA cC cF co wceq cB cA cF co cC cA cF co wceq cB cC
        wceq wph cA cB cF co cB cA cF co cA cC cF co cC cA cF co wph vx vy cA
        cB cS cF caovcanrd.6 caovcanrd.5 caovcand.3 caovcomd wph vx vy cA cC cS
        cF caovcanrd.6 caovcanrd.5 caovcand.4 caovcomd eqeq12d wph vx vy vz cA
        cB cC cS cT cF caovcang.1 caovcand.2 caovcand.3 caovcand.4 caovcand
        bitr3d $.
    $}

    ${
      caovcan.1 $e |- C e. _V $.
      caovcan.2 $e |- ( ( x e. S /\ y e. S ) ->
                   ( ( x F y ) = ( x F z ) -> y = z ) ) $.
      $( Convert an operation cancellation law to class notation.  (Contributed
         by NM, 20-Aug-1995.) $)
      caovcan $p |- ( ( A e. S /\ B e. S ) ->
                   ( ( A F B ) = ( A F C ) -> B = C ) ) $=
        vx cv vy cv cF co vx cv cC cF co wceq vy cv cC wceq wi cA vy cv cF co
        cA cC cF co wceq vy cv cC wceq wi cA cB cF co cA cC cF co wceq cB cC
        wceq wi vx vy cA cB cS cS vx cv cA wceq vx cv vy cv cF co vx cv cC cF
        co wceq cA vy cv cF co cA cC cF co wceq vy cv cC wceq vx cv cA wceq vx
        cv vy cv cF co cA vy cv cF co vx cv cC cF co cA cC cF co vx cv cA vy cv
        cF oveq1 vx cv cA cC cF oveq1 eqeq12d imbi1d vy cv cB wceq cA vy cv cF
        co cA cC cF co wceq cA cB cF co cA cC cF co wceq vy cv cC wceq cB cC
        wceq vy cv cB wceq cA vy cv cF co cA cB cF co cA cC cF co vy cv cB cA
        cF oveq2 eqeq1d vy cv cB cC eqeq1 imbi12d vx cv cS wcel vy cv cS wcel
        wa vx cv vy cv cF co vx cv vz cv cF co wceq vy cv vz cv wceq wi wi vx
        cv cS wcel vy cv cS wcel wa vx cv vy cv cF co vx cv cC cF co wceq vy cv
        cC wceq wi wi vz cC caovcan.1 vz cv cC wceq vx cv vy cv cF co vx cv vz
        cv cF co wceq vy cv vz cv wceq wi vx cv vy cv cF co vx cv cC cF co wceq
        vy cv cC wceq wi vx cv cS wcel vy cv cS wcel wa vz cv cC wceq vx cv vy
        cv cF co vx cv vz cv cF co wceq vx cv vy cv cF co vx cv cC cF co wceq
        vy cv vz cv wceq vy cv cC wceq vz cv cC wceq vx cv vz cv cF co vx cv cC
        cF co vx cv vy cv cF co vz cv cC vx cv cF oveq2 eqeq2d vz cv cC vy cv
        eqeq2 imbi12d imbi2d caovcan.2 vtocl vtocl2ga $.
    $}

    ${
      caovordig.1 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
                         ( x R y -> ( z F x ) R ( z F y ) ) ) $.
      $( Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 31-Dec-2014.) $)
      caovordig $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) ->
                      ( A R B -> ( C F A ) R ( C F B ) ) ) $=
        wph vx cv vy cv cR wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr wi vz
        cS wral vy cS wral vx cS wral cA cS wcel cB cS wcel cC cS wcel w3a cA
        cB cR wbr cC cA cF co cC cB cF co cR wbr wi wph vx cv vy cv cR wbr vz
        cv vx cv cF co vz cv vy cv cF co cR wbr wi vx vy vz cS cS cS
        caovordig.1 ralrimivvva vx cv vy cv cR wbr vz cv vx cv cF co vz cv vy
        cv cF co cR wbr wi cA cB cR wbr cC cA cF co cC cB cF co cR wbr wi cA vy
        cv cR wbr vz cv cA cF co vz cv vy cv cF co cR wbr wi cA cB cR wbr vz cv
        cA cF co vz cv cB cF co cR wbr wi vx vy vz cA cB cC cS cS cS vx cv cA
        wceq vx cv vy cv cR wbr cA vy cv cR wbr vz cv vx cv cF co vz cv vy cv
        cF co cR wbr vz cv cA cF co vz cv vy cv cF co cR wbr vx cv cA vy cv cR
        breq1 vx cv cA wceq vz cv vx cv cF co vz cv cA cF co vz cv vy cv cF co
        cR vx cv cA vz cv cF oveq2 breq1d imbi12d vy cv cB wceq cA vy cv cR wbr
        cA cB cR wbr vz cv cA cF co vz cv vy cv cF co cR wbr vz cv cA cF co vz
        cv cB cF co cR wbr vy cv cB cA cR breq2 vy cv cB wceq vz cv vy cv cF co
        vz cv cB cF co vz cv cA cF co cR vy cv cB vz cv cF oveq2 breq2d imbi12d
        vz cv cC wceq vz cv cA cF co vz cv cB cF co cR wbr cC cA cF co cC cB cF
        co cR wbr cA cB cR wbr vz cv cC wceq vz cv cA cF co cC cA cF co vz cv
        cB cF co cC cB cF co cR vz cv cC cA cF oveq1 vz cv cC cB cF oveq1
        breq12d imbi2d rspc3v mpan9 $.

      caovordid.2 $e |- ( ph -> A e. S ) $.
      caovordid.3 $e |- ( ph -> B e. S ) $.
      caovordid.4 $e |- ( ph -> C e. S ) $.
      $( Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 31-Dec-2014.) $)
      caovordid $p |- ( ph -> ( A R B -> ( C F A ) R ( C F B ) ) ) $=
        wph wph cA cS wcel cB cS wcel cC cS wcel cA cB cR wbr cC cA cF co cC cB
        cF co cR wbr wi wph id caovordid.2 caovordid.3 caovordid.4 wph vx vy vz
        cA cB cC cR cS cF caovordig.1 caovordig syl13anc $.
    $}

    ${
      caovordg.1 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
                         ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
      $( Convert an operation ordering law to class notation.  (Contributed by
         NM, 19-Feb-1996.)  (Revised by Mario Carneiro, 30-Dec-2014.) $)
      caovordg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. S ) ) ->
                      ( A R B <-> ( C F A ) R ( C F B ) ) ) $=
        wph vx cv vy cv cR wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr wb vz
        cS wral vy cS wral vx cS wral cA cS wcel cB cS wcel cC cS wcel w3a cA
        cB cR wbr cC cA cF co cC cB cF co cR wbr wb wph vx cv vy cv cR wbr vz
        cv vx cv cF co vz cv vy cv cF co cR wbr wb vx vy vz cS cS cS caovordg.1
        ralrimivvva vx cv vy cv cR wbr vz cv vx cv cF co vz cv vy cv cF co cR
        wbr wb cA cB cR wbr cC cA cF co cC cB cF co cR wbr wb cA vy cv cR wbr
        vz cv cA cF co vz cv vy cv cF co cR wbr wb cA cB cR wbr vz cv cA cF co
        vz cv cB cF co cR wbr wb vx vy vz cA cB cC cS cS cS vx cv cA wceq vx cv
        vy cv cR wbr cA vy cv cR wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr
        vz cv cA cF co vz cv vy cv cF co cR wbr vx cv cA vy cv cR breq1 vx cv
        cA wceq vz cv vx cv cF co vz cv cA cF co vz cv vy cv cF co cR vx cv cA
        vz cv cF oveq2 breq1d bibi12d vy cv cB wceq cA vy cv cR wbr cA cB cR
        wbr vz cv cA cF co vz cv vy cv cF co cR wbr vz cv cA cF co vz cv cB cF
        co cR wbr vy cv cB cA cR breq2 vy cv cB wceq vz cv vy cv cF co vz cv cB
        cF co vz cv cA cF co cR vy cv cB vz cv cF oveq2 breq2d bibi12d vz cv cC
        wceq vz cv cA cF co vz cv cB cF co cR wbr cC cA cF co cC cB cF co cR
        wbr cA cB cR wbr vz cv cC wceq vz cv cA cF co cC cA cF co vz cv cB cF
        co cC cB cF co cR vz cv cC cA cF oveq1 vz cv cC cB cF oveq1 breq12d
        bibi2d rspc3v mpan9 $.

      caovordd.2 $e |- ( ph -> A e. S ) $.
      caovordd.3 $e |- ( ph -> B e. S ) $.
      caovordd.4 $e |- ( ph -> C e. S ) $.
      $( Convert an operation ordering law to class notation.  (Contributed by
         Mario Carneiro, 30-Dec-2014.) $)
      caovordd $p |- ( ph -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $=
        wph wph cA cS wcel cB cS wcel cC cS wcel cA cB cR wbr cC cA cF co cC cB
        cF co cR wbr wb wph id caovordd.2 caovordd.3 caovordd.4 wph vx vy vz cA
        cB cC cR cS cF caovordg.1 caovordg syl13anc $.

      caovord2d.com $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                            ( x F y ) = ( y F x ) ) $.
      $( Operation ordering law with commuted arguments.  (Contributed by Mario
         Carneiro, 30-Dec-2014.) $)
      caovord2d $p |- ( ph -> ( A R B <-> ( A F C ) R ( B F C ) ) ) $=
        wph cA cB cR wbr cC cA cF co cC cB cF co cR wbr cA cC cF co cB cC cF co
        cR wbr wph vx vy vz cA cB cC cR cS cF caovordg.1 caovordd.2 caovordd.3
        caovordd.4 caovordd wph cC cA cF co cA cC cF co cC cB cF co cB cC cF co
        cR wph vx vy cC cA cS cF caovord2d.com caovordd.4 caovordd.2 caovcomd
        wph vx vy cC cB cS cF caovord2d.com caovordd.4 caovordd.3 caovcomd
        breq12d bitrd $.

      caovord3d.5 $e |- ( ph -> D e. S ) $.
      $( Ordering law.  (Contributed by Mario Carneiro, 30-Dec-2014.) $)
      caovord3d $p |- ( ph ->
        ( ( A F B ) = ( C F D ) -> ( A R C <-> D R B ) ) ) $=
        cA cB cF co cC cD cF co wceq cA cC cR wbr cD cB cR wbr wb wph cA cB cF
        co cC cB cF co cR wbr cC cD cF co cC cB cF co cR wbr wb cA cB cF co cC
        cD cF co cC cB cF co cR breq1 wph cA cC cR wbr cA cB cF co cC cB cF co
        cR wbr cD cB cR wbr cC cD cF co cC cB cF co cR wbr wph vx vy vz cA cC
        cB cR cS cF caovordg.1 caovordd.2 caovordd.4 caovordd.3 caovord2d.com
        caovord2d wph vx vy vz cD cB cC cR cS cF caovordg.1 caovord3d.5
        caovordd.3 caovordd.4 caovordd bibi12d syl5ibr $.
    $}

    ${
      caovord.1 $e |- A e. _V $.
      caovord.2 $e |- B e. _V $.
      caovord.3 $e |- ( z e. S -> ( x R y <-> ( z F x ) R ( z F y ) ) ) $.
      $( Convert an operation ordering law to class notation.  (Contributed by
         NM, 19-Feb-1996.) $)
      caovord $p |- ( C e. S -> ( A R B <-> ( C F A ) R ( C F B ) ) ) $=
        cA cB cR wbr vz cv cA cF co vz cv cB cF co cR wbr wb cA cB cR wbr cC cA
        cF co cC cB cF co cR wbr wb vz cC cS vz cv cC wceq vz cv cA cF co vz cv
        cB cF co cR wbr cC cA cF co cC cB cF co cR wbr cA cB cR wbr vz cv cC
        wceq vz cv cA cF co cC cA cF co vz cv cB cF co cC cB cF co cR vz cv cC
        cA cF oveq1 vz cv cC cB cF oveq1 breq12d bibi2d vz cv cS wcel vx cv vy
        cv cR wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr wb wi vz cv cS
        wcel cA cB cR wbr vz cv cA cF co vz cv cB cF co cR wbr wb wi vx vy cA
        cB caovord.1 caovord.2 vx cv cA wceq vy cv cB wceq wa vx cv vy cv cR
        wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr wb cA cB cR wbr vz cv cA
        cF co vz cv cB cF co cR wbr wb vz cv cS wcel vx cv cA wceq vx cv vy cv
        cR wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr wb cA vy cv cR wbr vz
        cv cA cF co vz cv vy cv cF co cR wbr wb vy cv cB wceq cA cB cR wbr vz
        cv cA cF co vz cv cB cF co cR wbr wb vx cv cA wceq vx cv vy cv cR wbr
        cA vy cv cR wbr vz cv vx cv cF co vz cv vy cv cF co cR wbr vz cv cA cF
        co vz cv vy cv cF co cR wbr vx cv cA vy cv cR breq1 vx cv cA wceq vz cv
        vx cv cF co vz cv cA cF co vz cv vy cv cF co cR vx cv cA vz cv cF oveq2
        breq1d bibi12d vy cv cB wceq cA vy cv cR wbr cA cB cR wbr vz cv cA cF
        co vz cv vy cv cF co cR wbr vz cv cA cF co vz cv cB cF co cR wbr vy cv
        cB cA cR breq2 vy cv cB wceq vz cv vy cv cF co vz cv cB cF co vz cv cA
        cF co cR vy cv cB vz cv cF oveq2 breq2d bibi12d sylan9bb imbi2d
        caovord.3 vtocl2 vtoclga $.

      $( (We don't bother to eliminate this redundant hypothesis.) $)
      caovord2.3 $e |- C e. _V $.
      caovord2.com $e |- ( x F y ) = ( y F x ) $.
      $( Operation ordering law with commuted arguments.  (Contributed by NM,
         27-Feb-1996.) $)
      caovord2 $p |- ( C e. S -> ( A R B <-> ( A F C ) R ( B F C ) ) ) $=
        cC cS wcel cA cB cR wbr cC cA cF co cC cB cF co cR wbr cA cC cF co cB
        cC cF co cR wbr vx vy vz cA cB cC cR cS cF caovord.1 caovord.2
        caovord.3 caovord cC cA cF co cA cC cF co cC cB cF co cB cC cF co cR vx
        vy cC cA cF caovord2.3 caovord.1 caovord2.com caovcom vx vy cC cB cF
        caovord2.3 caovord.2 caovord2.com caovcom breq12i syl6bb $.

      $( (We don't bother to eliminate redundant hypotheses.) $)
      caovord3.4 $e |- D e. _V $.
      $( Ordering law.  (Contributed by NM, 29-Feb-1996.) $)
      caovord3 $p |- ( ( ( B e. S /\ C e. S ) /\
                ( A F B ) = ( C F D ) ) -> ( A R C <-> D R B ) ) $=
        cB cS wcel cC cS wcel wa cA cB cF co cC cD cF co wceq wa cA cC cR wbr
        cC cD cF co cC cB cF co cR wbr cD cB cR wbr cB cS wcel cC cS wcel wa cA
        cC cR wbr cA cB cF co cC cB cF co cR wbr cA cB cF co cC cD cF co wceq
        cC cD cF co cC cB cF co cR wbr cB cS wcel cA cC cR wbr cA cB cF co cC
        cB cF co cR wbr wb cC cS wcel vx vy vz cA cC cB cR cS cF caovord.1
        caovord2.3 caovord.3 caovord.2 caovord2.com caovord2 adantr cA cB cF co
        cC cD cF co cC cB cF co cR breq1 sylan9bb cC cS wcel cD cB cR wbr cC cD
        cF co cC cB cF co cR wbr wb cB cS wcel cA cB cF co cC cD cF co wceq vx
        vy vz cD cB cC cR cS cF caovord3.4 caovord.2 caovord.3 caovord ad2antlr
        bitr4d $.
    $}

    ${
      caovdig.1 $e |- ( ( ph /\ ( x e. K /\ y e. S /\ z e. S ) ) ->
        ( x G ( y F z ) ) = ( ( x G y ) H ( x G z ) ) ) $.
      $( Convert an operation distributive law to class notation.  (Contributed
         by NM, 25-Aug-1995.)  (Revised by Mario Carneiro, 26-Jul-2014.) $)
      caovdig $p |- ( ( ph /\ ( A e. K /\ B e. S /\ C e. S ) ) ->
        ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) ) $=
        wph vx cv vy cv vz cv cF co cG co vx cv vy cv cG co vx cv vz cv cG co
        cH co wceq vz cS wral vy cS wral vx cK wral cA cK wcel cB cS wcel cC cS
        wcel w3a cA cB cC cF co cG co cA cB cG co cA cC cG co cH co wceq wph vx
        cv vy cv vz cv cF co cG co vx cv vy cv cG co vx cv vz cv cG co cH co
        wceq vx vy vz cK cS cS caovdig.1 ralrimivvva vx cv vy cv vz cv cF co cG
        co vx cv vy cv cG co vx cv vz cv cG co cH co wceq cA cB cC cF co cG co
        cA cB cG co cA cC cG co cH co wceq cA vy cv vz cv cF co cG co cA vy cv
        cG co cA vz cv cG co cH co wceq cA cB vz cv cF co cG co cA cB cG co cA
        vz cv cG co cH co wceq vx vy vz cA cB cC cK cS cS vx cv cA wceq vx cv
        vy cv vz cv cF co cG co cA vy cv vz cv cF co cG co vx cv vy cv cG co vx
        cv vz cv cG co cH co cA vy cv cG co cA vz cv cG co cH co vx cv cA vy cv
        vz cv cF co cG oveq1 vx cv cA wceq vx cv vy cv cG co cA vy cv cG co vx
        cv vz cv cG co cA vz cv cG co cH vx cv cA vy cv cG oveq1 vx cv cA vz cv
        cG oveq1 oveq12d eqeq12d vy cv cB wceq cA vy cv vz cv cF co cG co cA cB
        vz cv cF co cG co cA vy cv cG co cA vz cv cG co cH co cA cB cG co cA vz
        cv cG co cH co vy cv cB wceq vy cv vz cv cF co cB vz cv cF co cA cG vy
        cv cB vz cv cF oveq1 oveq2d vy cv cB wceq cA vy cv cG co cA cB cG co cA
        vz cv cG co cH vy cv cB cA cG oveq2 oveq1d eqeq12d vz cv cC wceq cA cB
        vz cv cF co cG co cA cB cC cF co cG co cA cB cG co cA vz cv cG co cH co
        cA cB cG co cA cC cG co cH co vz cv cC wceq cB vz cv cF co cB cC cF co
        cA cG vz cv cC cB cF oveq2 oveq2d vz cv cC wceq cA vz cv cG co cA cC cG
        co cA cB cG co cH vz cv cC cA cG oveq2 oveq2d eqeq12d rspc3v mpan9 $.

      caovdid.2 $e |- ( ph -> A e. K ) $.
      caovdid.3 $e |- ( ph -> B e. S ) $.
      caovdid.4 $e |- ( ph -> C e. S ) $.
      $( Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovdid $p |- ( ph -> ( A G ( B F C ) ) = ( ( A G B ) H ( A G C ) ) ) $=
        wph wph cA cK wcel cB cS wcel cC cS wcel cA cB cC cF co cG co cA cB cG
        co cA cC cG co cH co wceq wph id caovdid.2 caovdid.3 caovdid.4 wph vx
        vy vz cA cB cC cS cF cG cH cK caovdig.1 caovdig syl13anc $.
    $}

    ${
      caovdir2d.1 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
        ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) ) $.
      caovdir2d.2 $e |- ( ph -> A e. S ) $.
      caovdir2d.3 $e |- ( ph -> B e. S ) $.
      caovdir2d.4 $e |- ( ph -> C e. S ) $.
      caovdir2d.cl $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                           ( x F y ) e. S ) $.
      caovdir2d.com $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
                            ( x G y ) = ( y G x ) ) $.
      $( Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovdir2d $p |- ( ph
          -> ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) ) $=
        wph cC cA cB cF co cG co cC cA cG co cC cB cG co cF co cA cB cF co cC
        cG co cA cC cG co cB cC cG co cF co wph vx vy vz cC cA cB cS cF cG cF
        cS caovdir2d.1 caovdir2d.4 caovdir2d.2 caovdir2d.3 caovdid wph vx vy cA
        cB cF co cC cS cG caovdir2d.com wph vx vy cA cB cS cS cS cF
        caovdir2d.cl caovdir2d.2 caovdir2d.3 caovcld caovdir2d.4 caovcomd wph
        cA cC cG co cC cA cG co cB cC cG co cC cB cG co cF wph vx vy cA cC cS
        cG caovdir2d.com caovdir2d.2 caovdir2d.4 caovcomd wph vx vy cB cC cS cG
        caovdir2d.com caovdir2d.3 caovdir2d.4 caovcomd oveq12d 3eqtr4d $.
    $}

    ${
      caovdirg.1 $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. K ) ) ->
        ( ( x F y ) G z ) = ( ( x G z ) H ( y G z ) ) ) $.
      $( Convert an operation reverse distributive law to class notation.
         (Contributed by Mario Carneiro, 19-Oct-2014.) $)
      caovdirg $p |- ( ( ph /\ ( A e. S /\ B e. S /\ C e. K ) ) ->
        ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) ) $=
        wph vx cv vy cv cF co vz cv cG co vx cv vz cv cG co vy cv vz cv cG co
        cH co wceq vz cK wral vy cS wral vx cS wral cA cS wcel cB cS wcel cC cK
        wcel w3a cA cB cF co cC cG co cA cC cG co cB cC cG co cH co wceq wph vx
        cv vy cv cF co vz cv cG co vx cv vz cv cG co vy cv vz cv cG co cH co
        wceq vx vy vz cS cS cK caovdirg.1 ralrimivvva vx cv vy cv cF co vz cv
        cG co vx cv vz cv cG co vy cv vz cv cG co cH co wceq cA cB cF co cC cG
        co cA cC cG co cB cC cG co cH co wceq cA vy cv cF co vz cv cG co cA vz
        cv cG co vy cv vz cv cG co cH co wceq cA cB cF co vz cv cG co cA vz cv
        cG co cB vz cv cG co cH co wceq vx vy vz cA cB cC cS cS cK vx cv cA
        wceq vx cv vy cv cF co vz cv cG co cA vy cv cF co vz cv cG co vx cv vz
        cv cG co vy cv vz cv cG co cH co cA vz cv cG co vy cv vz cv cG co cH co
        vx cv cA wceq vx cv vy cv cF co cA vy cv cF co vz cv cG vx cv cA vy cv
        cF oveq1 oveq1d vx cv cA wceq vx cv vz cv cG co cA vz cv cG co vy cv vz
        cv cG co cH vx cv cA vz cv cG oveq1 oveq1d eqeq12d vy cv cB wceq cA vy
        cv cF co vz cv cG co cA cB cF co vz cv cG co cA vz cv cG co vy cv vz cv
        cG co cH co cA vz cv cG co cB vz cv cG co cH co vy cv cB wceq cA vy cv
        cF co cA cB cF co vz cv cG vy cv cB cA cF oveq2 oveq1d vy cv cB wceq vy
        cv vz cv cG co cB vz cv cG co cA vz cv cG co cH vy cv cB vz cv cG oveq1
        oveq2d eqeq12d vz cv cC wceq cA cB cF co vz cv cG co cA cB cF co cC cG
        co cA vz cv cG co cB vz cv cG co cH co cA cC cG co cB cC cG co cH co vz
        cv cC cA cB cF co cG oveq2 vz cv cC wceq cA vz cv cG co cA cC cG co cB
        vz cv cG co cB cC cG co cH vz cv cC cA cG oveq2 vz cv cC cB cG oveq2
        oveq12d eqeq12d rspc3v mpan9 $.

      caovdird.2 $e |- ( ph -> A e. S ) $.
      caovdird.3 $e |- ( ph -> B e. S ) $.
      caovdird.4 $e |- ( ph -> C e. K ) $.
      $( Convert an operation distributive law to class notation.  (Contributed
         by Mario Carneiro, 30-Dec-2014.) $)
      caovdird $p |- ( ph -> ( ( A F B ) G C ) = ( ( A G C ) H ( B G C ) ) ) $=
        wph wph cA cS wcel cB cS wcel cC cK wcel cA cB cF co cC cG co cA cC cG
        co cB cC cG co cH co wceq wph id caovdird.2 caovdird.3 caovdird.4 wph
        vx vy vz cA cB cC cS cF cG cH cK caovdirg.1 caovdirg syl13anc $.
    $}

    ${
      caovdi.1 $e |- A e. _V $.
      caovdi.2 $e |- B e. _V $.
      caovdi.3 $e |- C e. _V $.
      caovdi.4 $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
      $( Convert an operation distributive law to class notation.  (Contributed
         by NM, 25-Aug-1995.)  (Revised by Mario Carneiro, 28-Jun-2013.) $)
      caovdi $p |- ( A G ( B F C ) ) = ( ( A G B ) F ( A G C ) ) $=
        cA cvv wcel cB cvv wcel cC cvv wcel cA cB cC cF co cG co cA cB cG co cA
        cC cG co cF co wceq caovdi.1 caovdi.2 caovdi.3 wtru cA cvv wcel cB cvv
        wcel cC cvv wcel w3a cA cB cC cF co cG co cA cB cG co cA cC cG co cF co
        wceq tru wtru vx vy vz cA cB cC cvv cF cG cF cvv vx cv vy cv vz cv cF
        co cG co vx cv vy cv cG co vx cv vz cv cG co cF co wceq wtru vx cv cvv
        wcel vy cv cvv wcel vz cv cvv wcel w3a wa caovdi.4 a1i caovdig mpan
        mp3an $.
    $}

    ${
      caovd.1 $e |- ( ph -> A e. S ) $.
      caovd.2 $e |- ( ph -> B e. S ) $.
      caovd.3 $e |- ( ph -> C e. S ) $.
      caovd.com $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) ->
        ( x F y ) = ( y F x ) ) $.
      caovd.ass $e |- ( ( ph /\ ( x e. S /\ y e. S /\ z e. S ) ) ->
        ( ( x F y ) F z ) = ( x F ( y F z ) ) ) $.
      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)
      caov32d $p |- ( ph -> ( ( A F B ) F C ) = ( ( A F C ) F B ) ) $=
        wph cA cB cC cF co cF co cA cC cB cF co cF co cA cB cF co cC cF co cA
        cC cF co cB cF co wph cB cC cF co cC cB cF co cA cF wph vx vy cB cC cS
        cF caovd.com caovd.2 caovd.3 caovcomd oveq2d wph vx vy vz cA cB cC cS
        cF caovd.ass caovd.1 caovd.2 caovd.3 caovassd wph vx vy vz cA cC cB cS
        cF caovd.ass caovd.1 caovd.3 caovd.2 caovassd 3eqtr4d $.

      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)
      caov12d $p |- ( ph -> ( A F ( B F C ) ) = ( B F ( A F C ) ) ) $=
        wph cA cB cF co cC cF co cB cA cF co cC cF co cA cB cC cF co cF co cB
        cA cC cF co cF co wph cA cB cF co cB cA cF co cC cF wph vx vy cA cB cS
        cF caovd.com caovd.1 caovd.2 caovcomd oveq1d wph vx vy vz cA cB cC cS
        cF caovd.ass caovd.1 caovd.2 caovd.3 caovassd wph vx vy vz cB cA cC cS
        cF caovd.ass caovd.2 caovd.1 caovd.3 caovassd 3eqtr3d $.

      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)
      caov31d $p |- ( ph -> ( ( A F B ) F C ) = ( ( C F B ) F A ) ) $=
        wph cA cC cF co cB cF co cC cA cF co cB cF co cA cB cF co cC cF co cC
        cB cF co cA cF co wph cA cC cF co cC cA cF co cB cF wph vx vy cA cC cS
        cF caovd.com caovd.1 caovd.3 caovcomd oveq1d wph vx vy vz cA cB cC cS
        cF caovd.1 caovd.2 caovd.3 caovd.com caovd.ass caov32d wph vx vy vz cC
        cB cA cS cF caovd.3 caovd.2 caovd.1 caovd.com caovd.ass caov32d 3eqtr4d
        $.

      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
         30-Dec-2014.) $)
      caov13d $p |- ( ph -> ( A F ( B F C ) ) = ( C F ( B F A ) ) ) $=
        wph cA cB cF co cC cF co cC cB cF co cA cF co cA cB cC cF co cF co cC
        cB cA cF co cF co wph vx vy vz cA cB cC cS cF caovd.1 caovd.2 caovd.3
        caovd.com caovd.ass caov31d wph vx vy vz cA cB cC cS cF caovd.ass
        caovd.1 caovd.2 caovd.3 caovassd wph vx vy vz cC cB cA cS cF caovd.ass
        caovd.3 caovd.2 caovd.1 caovassd 3eqtr3d $.

      ${
        caovd.4 $e |- ( ph -> D e. S ) $.
        caovd.cl $e |- ( ( ph /\ ( x e. S /\ y e. S ) ) -> ( x F y ) e. S ) $.
        $( Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) $)
        caov4d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) =
                             ( ( A F C ) F ( B F D ) ) ) $=
          wph cA cB cC cD cF co cF co cF co cA cC cB cD cF co cF co cF co cA cB
          cF co cC cD cF co cF co cA cC cF co cB cD cF co cF co wph cB cC cD cF
          co cF co cC cB cD cF co cF co cA cF wph vx vy vz cB cC cD cS cF
          caovd.2 caovd.3 caovd.4 caovd.com caovd.ass caov12d oveq2d wph vx vy
          vz cA cB cC cD cF co cS cF caovd.ass caovd.1 caovd.2 wph vx vy cC cD
          cS cS cS cF caovd.cl caovd.3 caovd.4 caovcld caovassd wph vx vy vz cA
          cC cB cD cF co cS cF caovd.ass caovd.1 caovd.3 wph vx vy cB cD cS cS
          cS cF caovd.cl caovd.2 caovd.4 caovcld caovassd 3eqtr4d $.

        $( Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) $)
        caov411d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) =
                               ( ( C F B ) F ( A F D ) ) ) $=
          wph cB cA cF co cC cD cF co cF co cB cC cF co cA cD cF co cF co cA cB
          cF co cC cD cF co cF co cC cB cF co cA cD cF co cF co wph vx vy vz cB
          cA cC cD cS cF caovd.2 caovd.1 caovd.3 caovd.com caovd.ass caovd.4
          caovd.cl caov4d wph cB cA cF co cA cB cF co cC cD cF co cF wph vx vy
          cB cA cS cF caovd.com caovd.2 caovd.1 caovcomd oveq1d wph cB cC cF co
          cC cB cF co cA cD cF co cF wph vx vy cB cC cS cF caovd.com caovd.2
          caovd.3 caovcomd oveq1d 3eqtr3d $.

        $( Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.)  (Revised by Mario Carneiro,
           30-Dec-2014.) $)
        caov42d $p |- ( ph -> ( ( A F B ) F ( C F D ) ) =
                              ( ( A F C ) F ( D F B ) ) ) $=
          wph cA cB cF co cC cD cF co cF co cA cC cF co cB cD cF co cF co cA cC
          cF co cD cB cF co cF co wph vx vy vz cA cB cC cD cS cF caovd.1
          caovd.2 caovd.3 caovd.com caovd.ass caovd.4 caovd.cl caov4d wph cB cD
          cF co cD cB cF co cA cC cF co cF wph vx vy cB cD cS cF caovd.com
          caovd.2 caovd.4 caovcomd oveq2d eqtrd $.
      $}
    $}

    ${
      caov.1 $e |- A e. _V $.
      caov.2 $e |- B e. _V $.
      caov.3 $e |- C e. _V $.
      caov.com $e |- ( x F y ) = ( y F x ) $.
      caov.ass $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)
      caov32 $p |- ( ( A F B ) F C ) = ( ( A F C ) F B ) $=
        cA cB cC cF co cF co cA cC cB cF co cF co cA cB cF co cC cF co cA cC cF
        co cB cF co cB cC cF co cC cB cF co cA cF vx vy cB cC cF caov.2 caov.3
        caov.com caovcom oveq2i vx vy vz cA cB cC cF caov.1 caov.2 caov.3
        caov.ass caovass vx vy vz cA cC cB cF caov.1 caov.3 caov.2 caov.ass
        caovass 3eqtr4i $.

      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)
      caov12 $p |- ( A F ( B F C ) ) = ( B F ( A F C ) ) $=
        cA cB cF co cC cF co cB cA cF co cC cF co cA cB cC cF co cF co cB cA cC
        cF co cF co cA cB cF co cB cA cF co cC cF vx vy cA cB cF caov.1 caov.2
        caov.com caovcom oveq1i vx vy vz cA cB cC cF caov.1 caov.2 caov.3
        caov.ass caovass vx vy vz cB cA cC cF caov.2 caov.1 caov.3 caov.ass
        caovass 3eqtr3i $.

      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)
      caov31 $p |- ( ( A F B ) F C ) = ( ( C F B ) F A ) $=
        cA cC cF co cB cF co cC cA cB cF co cF co cA cB cF co cC cF co cC cB cF
        co cA cF co cA cC cF co cB cF co cA cC cB cF co cF co cC cA cB cF co cF
        co vx vy vz cA cC cB cF caov.1 caov.3 caov.2 caov.ass caovass vx vy vz
        cA cC cB cF caov.1 caov.3 caov.2 caov.com caov.ass caov12 eqtri vx vy
        vz cA cB cC cF caov.1 caov.2 caov.3 caov.com caov.ass caov32 cC cA cF
        co cB cF co cC cB cF co cA cF co cC cA cB cF co cF co vx vy vz cC cA cB
        cF caov.3 caov.1 caov.2 caov.com caov.ass caov32 vx vy vz cC cA cB cF
        caov.3 caov.1 caov.2 caov.ass caovass eqtr3i 3eqtr4i $.

      $( Rearrange arguments in a commutative, associative operation.
         (Contributed by NM, 26-Aug-1995.) $)
      caov13 $p |- ( A F ( B F C ) ) = ( C F ( B F A ) ) $=
        cA cB cF co cC cF co cC cB cF co cA cF co cA cB cC cF co cF co cC cB cA
        cF co cF co vx vy vz cA cB cC cF caov.1 caov.2 caov.3 caov.com caov.ass
        caov31 vx vy vz cA cB cC cF caov.1 caov.2 caov.3 caov.ass caovass vx vy
        vz cC cB cA cF caov.3 caov.2 caov.1 caov.ass caovass 3eqtr3i $.

      ${
        caov.4 $e |- D e. _V $.
        $( Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) $)
        caov4 $p |- ( ( A F B ) F ( C F D ) ) = ( ( A F C ) F ( B F D ) ) $=
          cA cB cC cD cF co cF co cF co cA cC cB cD cF co cF co cF co cA cB cF
          co cC cD cF co cF co cA cC cF co cB cD cF co cF co cB cC cD cF co cF
          co cC cB cD cF co cF co cA cF vx vy vz cB cC cD cF caov.2 caov.3
          caov.4 caov.com caov.ass caov12 oveq2i vx vy vz cA cB cC cD cF co cF
          caov.1 caov.2 cC cD cF ovex caov.ass caovass vx vy vz cA cC cB cD cF
          co cF caov.1 caov.3 cB cD cF ovex caov.ass caovass 3eqtr4i $.

        $( Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) $)
        caov411 $p |- ( ( A F B ) F ( C F D ) ) = ( ( C F B ) F ( A F D ) ) $=
          cA cB cF co cC cF co cD cF co cC cB cF co cA cF co cD cF co cA cB cF
          co cC cD cF co cF co cC cB cF co cA cD cF co cF co cA cB cF co cC cF
          co cC cB cF co cA cF co cD cF vx vy vz cA cB cC cF caov.1 caov.2
          caov.3 caov.com caov.ass caov31 oveq1i vx vy vz cA cB cF co cC cD cF
          cA cB cF ovex caov.3 caov.4 caov.ass caovass vx vy vz cC cB cF co cA
          cD cF cC cB cF ovex caov.1 caov.4 caov.ass caovass 3eqtr3i $.

        $( Rearrange arguments in a commutative, associative operation.
           (Contributed by NM, 26-Aug-1995.) $)
        caov42 $p |- ( ( A F B ) F ( C F D ) ) =
                        ( ( A F C ) F ( D F B ) ) $=
          cA cB cF co cC cD cF co cF co cA cC cF co cB cD cF co cF co cA cC cF
          co cD cB cF co cF co vx vy vz cA cB cC cD cF caov.1 caov.2 caov.3
          caov.com caov.ass caov.4 caov4 cB cD cF co cD cB cF co cA cC cF co cF
          vx vy cB cD cF caov.2 caov.4 caov.com caovcom oveq2i eqtri $.
      $}
    $}

    ${
      caovdir.1 $e |- A e. _V $.
      caovdir.2 $e |- B e. _V $.
      caovdir.3 $e |- C e. _V $.
      caovdir.com $e |- ( x G y ) = ( y G x ) $.
      caovdir.distr $e |- ( x G ( y F z ) ) = ( ( x G y ) F ( x G z ) ) $.
      $( Reverse distributive law.  (Contributed by NM, 26-Aug-1995.) $)
      caovdir $p |- ( ( A F B ) G C ) = ( ( A G C ) F ( B G C ) ) $=
        cC cA cB cF co cG co cC cA cG co cC cB cG co cF co cA cB cF co cC cG co
        cA cC cG co cB cC cG co cF co vx vy vz cC cA cB cF cG caovdir.3
        caovdir.1 caovdir.2 caovdir.distr caovdi vx vy cC cA cB cF co cG
        caovdir.3 cA cB cF ovex caovdir.com caovcom cC cA cG co cA cC cG co cC
        cB cG co cB cC cG co cF vx vy cC cA cG caovdir.3 caovdir.1 caovdir.com
        caovcom vx vy cC cB cG caovdir.3 caovdir.2 caovdir.com caovcom oveq12i
        3eqtr3i $.

      $d x y z H $.  $d x y z R $.
      caovdl.4 $e |- D e. _V $.
      caovdl.5 $e |- H e. _V $.
      caovdl.ass $e |- ( ( x G y ) G z ) = ( x G ( y G z ) ) $.
      $( Lemma used by real number construction.  (Contributed by NM,
         26-Aug-1995.) $)
      caovdilem $p |- ( ( ( A G C ) F ( B G D ) ) G H ) =
                       ( ( A G ( C G H ) ) F ( B G ( D G H ) ) ) $=
        cA cC cG co cB cD cG co cF co cH cG co cA cC cG co cH cG co cB cD cG co
        cH cG co cF co cA cC cH cG co cG co cB cD cH cG co cG co cF co vx vy vz
        cA cC cG co cB cD cG co cH cF cG cA cC cG ovex cB cD cG ovex caovdl.5
        caovdir.com caovdir.distr caovdir cA cC cG co cH cG co cA cC cH cG co
        cG co cB cD cG co cH cG co cB cD cH cG co cG co cF vx vy vz cA cC cH cG
        caovdir.1 caovdir.3 caovdl.5 caovdl.ass caovass vx vy vz cB cD cH cG
        caovdir.2 caovdl.4 caovdl.5 caovdl.ass caovass oveq12i eqtri $.

      caovdl2.6 $e |- R e. _V $.
      caovdl2.com $e |- ( x F y ) = ( y F x ) $.
      caovdl2.ass $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
      $( Lemma used in real number construction.  (Contributed by NM,
         26-Aug-1995.) $)
      caovlem2 $p |- ( ( ( ( A G C ) F ( B G D ) ) G H ) F
                        ( ( ( A G D ) F ( B G C ) ) G R ) ) =
   ( ( A G ( ( C G H ) F ( D G R ) ) ) F ( B G ( ( C G R ) F ( D G H ) ) ) ) $=
        cA cC cH cG co cG co cB cD cH cG co cG co cF co cA cD cR cG co cG co cB
        cC cR cG co cG co cF co cF co cA cC cH cG co cG co cA cD cR cG co cG co
        cF co cB cC cR cG co cG co cB cD cH cG co cG co cF co cF co cA cC cG co
        cB cD cG co cF co cH cG co cA cD cG co cB cC cG co cF co cR cG co cF co
        cA cC cH cG co cD cR cG co cF co cG co cB cC cR cG co cD cH cG co cF co
        cG co cF co vx vy vz cA cC cH cG co cG co cB cD cH cG co cG co cA cD cR
        cG co cG co cB cC cR cG co cG co cF cA cC cH cG co cG ovex cB cD cH cG
        co cG ovex cA cD cR cG co cG ovex caovdl2.com caovdl2.ass cB cC cR cG
        co cG ovex caov42 cA cC cG co cB cD cG co cF co cH cG co cA cC cH cG co
        cG co cB cD cH cG co cG co cF co cA cD cG co cB cC cG co cF co cR cG co
        cA cD cR cG co cG co cB cC cR cG co cG co cF co cF vx vy vz cA cB cC cD
        cF cG cH caovdir.1 caovdir.2 caovdir.3 caovdir.com caovdir.distr
        caovdl.4 caovdl.5 caovdl.ass caovdilem vx vy vz cA cB cD cC cF cG cR
        caovdir.1 caovdir.2 caovdl.4 caovdir.com caovdir.distr caovdir.3
        caovdl2.6 caovdl.ass caovdilem oveq12i cA cC cH cG co cD cR cG co cF co
        cG co cA cC cH cG co cG co cA cD cR cG co cG co cF co cB cC cR cG co cD
        cH cG co cF co cG co cB cC cR cG co cG co cB cD cH cG co cG co cF co cF
        vx vy vz cA cC cH cG co cD cR cG co cF cG caovdir.1 cC cH cG ovex cD cR
        cG ovex caovdir.distr caovdi vx vy vz cB cC cR cG co cD cH cG co cF cG
        caovdir.2 cC cR cG ovex cD cH cG ovex caovdir.distr caovdi oveq12i
        3eqtr4i $.
    $}

    ${
      $d u w A $.  $d u v w x y B $.  $d u v w x y z F $.  $d w x S $.
      $( Identity element. $)
      caovmo.2 $e |- B e. S $.
      caovmo.dom $e |- dom F = ( S X. S ) $.
      caovmo.3 $e |- -. (/) e. S $.
      caovmo.com $e |- ( x F y ) = ( y F x ) $.
      caovmo.ass $e |- ( ( x F y ) F z ) = ( x F ( y F z ) ) $.
      caovmo.id $e |- ( x e. S -> ( x F B ) = x ) $.
      $( Uniqueness of inverse element in commutative, associative operation
         with identity.  Remark in proof of Proposition 9-2.4 of [Gleason]
         p. 119.  (Contributed by NM, 4-Mar-1996.) $)
      caovmo $p |- E* w ( A F w ) = B $=
        cA cS wcel cA vw cv cF co cB wceq wa vw wmo cA vw cv cF co cB wceq vw
        wmo cA cS wcel cA vw cv cF co cB wceq wa vw wmo cA cS wcel cA vw cv cF
        co cB wceq vw wmo wi vu cv vw cv cF co cB wceq vw wmo cA vw cv cF co cB
        wceq vw wmo vu cA cS vu cv cA wceq vu cv vw cv cF co cB wceq cA vw cv
        cF co cB wceq vw vu cv cA wceq vu cv vw cv cF co cA vw cv cF co cB vu
        cv cA vw cv cF oveq1 eqeq1d mobidv vu cv vw cv cF co cB wceq vw wmo vu
        cv vw cv cF co cB wceq vu cv vv cv cF co cB wceq wa vw cv vv cv wceq wi
        vv wal vw vu cv vw cv cF co cB wceq vu cv vv cv cF co cB wceq vw vv vw
        cv vv cv wceq vu cv vw cv cF co vu cv vv cv cF co cB vw cv vv cv vu cv
        cF oveq2 eqeq1d mo4 vu cv vw cv cF co cB wceq vu cv vv cv cF co cB wceq
        wa vw cv vv cv wceq wi vv vu cv vw cv cF co cB wceq vu cv vv cv cF co
        cB wceq wa vw cv cB cF co vv cv cB cF co vw cv vv cv vu cv vw cv cF co
        cB wceq vu cv vv cv cF co cB wceq wa vw cv vu cv vv cv cF co cF co vw
        cv cB cF co vv cv cB cF co vu cv vw cv cF co cB wceq vu cv vv cv cF co
        cB wceq wa vu cv vv cv cF co cB vw cv cF vu cv vw cv cF co cB wceq vu
        cv vv cv cF co cB wceq simpr oveq2d vu cv vw cv cF co cB wceq vu cv vv
        cv cF co cB wceq wa vu cv vw cv cF co vv cv cF co cB vv cv cF co vw cv
        vu cv vv cv cF co cF co vv cv cB cF co vu cv vw cv cF co cB wceq vu cv
        vv cv cF co cB wceq wa vu cv vw cv cF co cB vv cv cF vu cv vw cv cF co
        cB wceq vu cv vv cv cF co cB wceq simpl oveq1d vu cv vw cv cF co vv cv
        cF co vu cv vw cv vv cv cF co cF co vw cv vu cv vv cv cF co cF co vx vy
        vz vu cv vw cv vv cv cF vu vex vw vex vv vex caovmo.ass caovass vx vy
        vz vu cv vw cv vv cv cF vu vex vw vex vv vex caovmo.com caovmo.ass
        caov12 eqtri vx vy cB vv cv cF cB cS caovmo.2 elexi vv vex caovmo.com
        caovcom 3eqtr3g eqtr3d vu cv vw cv cF co cB wceq vu cv vv cv cF co cB
        wceq wa vw cv cS wcel vw cv cB cF co vw cv wceq vu cv vw cv cF co cB
        wceq vu cv vv cv cF co cB wceq wa vu cv cS wcel vw cv cS wcel vu cv vw
        cv cF co cB wceq vu cv vv cv cF co cB wceq wa vu cv vw cv cF co cS wcel
        vu cv cS wcel vw cv cS wcel wa vu cv vw cv cF co cB wceq vu cv vv cv cF
        co cB wceq wa vu cv vw cv cF co cB cS vu cv vw cv cF co cB wceq vu cv
        vv cv cF co cB wceq simpl caovmo.2 syl6eqel vu cv vw cv cS cF
        caovmo.dom caovmo.3 ndmovrcl syl simprd vx cv cB cF co vx cv wceq vw cv
        cB cF co vw cv wceq vx vw cv cS vx cv vw cv wceq vx cv cB cF co vw cv
        cB cF co vx cv vw cv vx cv vw cv cB cF oveq1 vx cv vw cv wceq id
        eqeq12d caovmo.id vtoclga syl vu cv vw cv cF co cB wceq vu cv vv cv cF
        co cB wceq wa vv cv cS wcel vv cv cB cF co vv cv wceq vu cv vw cv cF co
        cB wceq vu cv vv cv cF co cB wceq wa vu cv cS wcel vv cv cS wcel vu cv
        vw cv cF co cB wceq vu cv vv cv cF co cB wceq wa vu cv vv cv cF co cS
        wcel vu cv cS wcel vv cv cS wcel wa vu cv vw cv cF co cB wceq vu cv vv
        cv cF co cB wceq wa vu cv vv cv cF co cB cS vu cv vw cv cF co cB wceq
        vu cv vv cv cF co cB wceq simpr caovmo.2 syl6eqel vu cv vv cv cS cF
        caovmo.dom caovmo.3 ndmovrcl syl simprd vx cv cB cF co vx cv wceq vv cv
        cB cF co vv cv wceq vx vv cv cS vx cv vv cv wceq vx cv cB cF co vv cv
        cB cF co vx cv vv cv vx cv vv cv cB cF oveq1 vx cv vv cv wceq id
        eqeq12d caovmo.id vtoclga syl 3eqtr3d ax-gen mpgbir vtoclg cA cS wcel
        cA vw cv cF co cB wceq vw moanimv mpbir cA vw cv cF co cB wceq cA cS
        wcel cA vw cv cF co cB wceq wa vw cA vw cv cF co cB wceq cA cS wcel cA
        vw cv cF co cB wceq cA cS wcel vw cv cS wcel cA vw cv cF co cB wceq cA
        vw cv cF co cS wcel cA cS wcel vw cv cS wcel wa cA vw cv cF co cB wceq
        cA vw cv cF co cS wcel cB cS wcel caovmo.2 cA vw cv cF co cB cS eleq1
        mpbiri cA vw cv cS cF caovmo.dom caovmo.3 ndmovrcl syl simpld ancri
        moimi ax-mp $.
    $}
  $}

  ${
    $d n u v w x y z B $.  $d n u v w x y z O $.  $d n u v w x y z ph $.
    $d u v w y z N $.  $d n u v w x y z .+ $.  $d u v w y z X $.
    $d u v w y ps $.
    grprinvlem.c $e |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B ) $.
    grprinvlem.o $e |- ( ph -> O e. B ) $.
    grprinvlem.i $e |- ( ( ph /\ x e. B ) -> ( O .+ x ) = x ) $.
    grprinvlem.a $e |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) )
          -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) ) $.
    grprinvlem.n $e |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = O ) $.
    ${
      grprinvlem.x $e |- ( ( ph /\ ps ) -> X e. B ) $.
      grprinvlem.e $e |- ( ( ph /\ ps ) -> ( X .+ X ) = X ) $.
      $( Lemma for ~ grprinvd .  (Contributed by NM, 9-Aug-2013.) $)
      grprinvlem $p |- ( ( ph /\ ps ) -> X = O ) $=
        wph wps wa vy cv cX c.pl co cO wceq vy cB wrex cX cO wceq wph wps cX cB
        wcel vy cv cX c.pl co cO wceq vy cB wrex grprinvlem.x wph vy cv vz cv
        c.pl co cO wceq vy cB wrex vz cB wral cX cB wcel vy cv cX c.pl co cO
        wceq vy cB wrex wph vy cv vx cv c.pl co cO wceq vy cB wrex vx cB wral
        vy cv vz cv c.pl co cO wceq vy cB wrex vz cB wral wph vy cv vx cv c.pl
        co cO wceq vy cB wrex vx cB grprinvlem.n ralrimiva vy cv vx cv c.pl co
        cO wceq vy cB wrex vy cv vz cv c.pl co cO wceq vy cB wrex vx vz cB vx
        cv vz cv wceq vy cv vx cv c.pl co cO wceq vy cv vz cv c.pl co cO wceq
        vy cB vx cv vz cv wceq vy cv vx cv c.pl co vy cv vz cv c.pl co cO vx cv
        vz cv vy cv c.pl oveq2 eqeq1d rexbidv cbvralv sylib vy cv vz cv c.pl co
        cO wceq vy cB wrex vy cv cX c.pl co cO wceq vy cB wrex vz cX cB vz cv
        cX wceq vy cv vz cv c.pl co cO wceq vy cv cX c.pl co cO wceq vy cB vz
        cv cX wceq vy cv vz cv c.pl co vy cv cX c.pl co cO vz cv cX vy cv c.pl
        oveq2 eqeq1d rexbidv rspccva sylan syldan wph wps wa vy cv cX c.pl co
        cO wceq cX cO wceq vy cB wph wps wa vy cv cB wcel vy cv cX c.pl co cO
        wceq cX cO wceq wph wps wa vy cv cB wcel vy cv cX c.pl co cO wceq wa wa
        vy cv cX cX c.pl co c.pl co vy cv cX c.pl co cX cO wph wps wa vy cv cX
        cX c.pl co c.pl co vy cv cX c.pl co wceq vy cv cB wcel vy cv cX c.pl co
        cO wceq wa wph wps wa cX cX c.pl co cX vy cv c.pl grprinvlem.e oveq2d
        adantr wph wps wa vy cv cB wcel vy cv cX c.pl co cO wceq wa wa vy cv cX
        c.pl co cX c.pl co cO cX c.pl co vy cv cX cX c.pl co c.pl co cX wph wps
        wa vy cv cB wcel vy cv cX c.pl co cO wceq wa wa vy cv cX c.pl co cO cX
        c.pl wph wps wa vy cv cB wcel vy cv cX c.pl co cO wceq simprr oveq1d
        wph wps wa vy cv cB wcel vy cv cX c.pl co cO wceq wa wa vu vv vw vy cv
        cX cX cB c.pl wph wps wa vy cv cB wcel vy cv cX c.pl co cO wceq wa wa
        wph vu cv cB wcel vv cv cB wcel vw cv cB wcel w3a vu cv vv cv c.pl co
        vw cv c.pl co vu cv vv cv vw cv c.pl co c.pl co wceq wph wps vy cv cB
        wcel vy cv cX c.pl co cO wceq wa simpll wph vx vy vz vu cv vv cv vw cv
        cB c.pl grprinvlem.a caovassg sylan wph wps wa vy cv cB wcel vy cv cX
        c.pl co cO wceq simprl wph wps wa cX cB wcel vy cv cB wcel vy cv cX
        c.pl co cO wceq wa grprinvlem.x adantr wph wps wa cX cB wcel vy cv cB
        wcel vy cv cX c.pl co cO wceq wa grprinvlem.x adantr caovassd wph wps
        wa cO cX c.pl co cX wceq vy cv cB wcel vy cv cX c.pl co cO wceq wa wph
        wps wa cX cB wcel cO vy cv c.pl co vy cv wceq vy cB wral cO cX c.pl co
        cX wceq grprinvlem.x wph cO vy cv c.pl co vy cv wceq vy cB wral wps wph
        cO vx cv c.pl co vx cv wceq vx cB wral cO vy cv c.pl co vy cv wceq vy
        cB wral wph cO vx cv c.pl co vx cv wceq vx cB grprinvlem.i ralrimiva cO
        vx cv c.pl co vx cv wceq cO vy cv c.pl co vy cv wceq vx vy cB vx cv vy
        cv wceq cO vx cv c.pl co cO vy cv c.pl co vx cv vy cv vx cv vy cv cO
        c.pl oveq2 vx cv vy cv wceq id eqeq12d cbvralv sylib adantr cO vy cv
        c.pl co vy cv wceq cO cX c.pl co cX wceq vy cX cB vy cv cX wceq cO vy
        cv c.pl co cO cX c.pl co vy cv cX vy cv cX cO c.pl oveq2 vy cv cX wceq
        id eqeq12d rspcv sylc adantr 3eqtr3d wph wps wa vy cv cB wcel vy cv cX
        c.pl co cO wceq simprr 3eqtr3d expr rexlimdva mpd $.
    $}

    ${
      grprinvd.x $e |- ( ( ph /\ ps ) -> X e. B ) $.
      grprinvd.n $e |- ( ( ph /\ ps ) -> N e. B ) $.
      grprinvd.e $e |- ( ( ph /\ ps ) -> ( N .+ X ) = O ) $.
      $( Deduce right inverse from left inverse and left identity in an
         associative structure (such as a group).  (Contributed by NM,
         10-Aug-2013.)  (Proof shortened by Mario Carneiro, 6-Jan-2015.) $)
      grprinvd $p |- ( ( ph /\ ps ) -> ( X .+ N ) = O ) $=
        wph wps vx vy vz cB c.pl cO cX cN c.pl co grprinvlem.c grprinvlem.o
        grprinvlem.i grprinvlem.a grprinvlem.n wph wps wa vu vv cX cN cB cB cB
        c.pl wph vu cv cB wcel vv cv cB wcel wa vu cv vv cv c.pl co cB wcel wps
        wph vx vy vu cv vv cv cB cB cB c.pl wph vx cv cB wcel vy cv cB wcel vx
        cv vy cv c.pl co cB wcel grprinvlem.c 3expb caovclg adantlr grprinvd.x
        grprinvd.n caovcld wph wps wa cX cN c.pl co cX cN c.pl co c.pl co cX cN
        cX cN c.pl co c.pl co c.pl co cX cN c.pl co wph wps wa vu vv vw cX cN
        cX cN c.pl co cB c.pl wph vu cv cB wcel vv cv cB wcel vw cv cB wcel w3a
        vu cv vv cv c.pl co vw cv c.pl co vu cv vv cv vw cv c.pl co c.pl co
        wceq wps wph vx vy vz vu cv vv cv vw cv cB c.pl grprinvlem.a caovassg
        adantlr grprinvd.x grprinvd.n wph wps wa vu vv cX cN cB cB cB c.pl wph
        vu cv cB wcel vv cv cB wcel wa vu cv vv cv c.pl co cB wcel wps wph vx
        vy vu cv vv cv cB cB cB c.pl wph vx cv cB wcel vy cv cB wcel vx cv vy
        cv c.pl co cB wcel grprinvlem.c 3expb caovclg adantlr grprinvd.x
        grprinvd.n caovcld caovassd wph wps wa cN cX cN c.pl co c.pl co cN cX
        c.pl wph wps wa cN cX c.pl co cN c.pl co cO cN c.pl co cN cX cN c.pl co
        c.pl co cN wph wps wa cN cX c.pl co cO cN c.pl grprinvd.e oveq1d wph
        wps wa vu vv vw cN cX cN cB c.pl wph vu cv cB wcel vv cv cB wcel vw cv
        cB wcel w3a vu cv vv cv c.pl co vw cv c.pl co vu cv vv cv vw cv c.pl co
        c.pl co wceq wps wph vx vy vz vu cv vv cv vw cv cB c.pl grprinvlem.a
        caovassg adantlr grprinvd.n grprinvd.x grprinvd.n caovassd wph wps wa
        cN cB wcel cO vy cv c.pl co vy cv wceq vy cB wral cO cN c.pl co cN wceq
        grprinvd.n wph cO vy cv c.pl co vy cv wceq vy cB wral wps wph cO vx cv
        c.pl co vx cv wceq vx cB wral cO vy cv c.pl co vy cv wceq vy cB wral
        wph cO vx cv c.pl co vx cv wceq vx cB grprinvlem.i ralrimiva cO vx cv
        c.pl co vx cv wceq cO vy cv c.pl co vy cv wceq vx vy cB vx cv vy cv
        wceq cO vx cv c.pl co cO vy cv c.pl co vx cv vy cv vx cv vy cv cO c.pl
        oveq2 vx cv vy cv wceq id eqeq12d cbvralv sylib adantr cO vy cv c.pl co
        vy cv wceq cO cN c.pl co cN wceq vy cN cB vy cv cN wceq cO vy cv c.pl
        co cO cN c.pl co vy cv cN vy cv cN cO c.pl oveq2 vy cv cN wceq id
        eqeq12d rspcv sylc 3eqtr3d oveq2d eqtrd grprinvlem $.
    $}

    $( Deduce right identity from left inverse and left identity in an
       associative structure (such as a group).  (Contributed by NM,
       10-Aug-2013.)  (Proof shortened by Mario Carneiro, 6-Jan-2015.) $)
    grpridd $p |- ( ( ph /\ x e. B ) -> ( x .+ O ) = x ) $=
      wph vx cv cB wcel wa cO vx cv c.pl co vx cv cO c.pl co vx cv wph vx cv cB
      wcel wa vn cv vx cv c.pl co cO wceq vn cB wrex cO vx cv c.pl co vx cv cO
      c.pl co wceq wph vx cv cB wcel wa vy cv vx cv c.pl co cO wceq vy cB wrex
      vn cv vx cv c.pl co cO wceq vn cB wrex grprinvlem.n vy cv vx cv c.pl co
      cO wceq vn cv vx cv c.pl co cO wceq vy vn cB vy cv vn cv wceq vy cv vx cv
      c.pl co vn cv vx cv c.pl co cO vy cv vn cv vx cv c.pl oveq1 eqeq1d
      cbvrexv sylib wph vx cv cB wcel wa vn cv vx cv c.pl co cO wceq cO vx cv
      c.pl co vx cv cO c.pl co wceq vn cB wph vx cv cB wcel wa vn cv cB wcel vn
      cv vx cv c.pl co cO wceq cO vx cv c.pl co vx cv cO c.pl co wceq wph vx cv
      cB wcel vn cv cB wcel vn cv vx cv c.pl co cO wceq wa cO vx cv c.pl co vx
      cv cO c.pl co wceq wph vx cv cB wcel vn cv cB wcel vn cv vx cv c.pl co cO
      wceq wa wa wa vx cv vn cv c.pl co vx cv c.pl co vx cv vn cv vx cv c.pl co
      c.pl co cO vx cv c.pl co vx cv cO c.pl co wph vx cv cB wcel vn cv cB wcel
      vn cv vx cv c.pl co cO wceq wa wa wa vu vv vw vx cv vn cv vx cv cB c.pl
      wph vu cv cB wcel vv cv cB wcel vw cv cB wcel w3a vu cv vv cv c.pl co vw
      cv c.pl co vu cv vv cv vw cv c.pl co c.pl co wceq vx cv cB wcel vn cv cB
      wcel vn cv vx cv c.pl co cO wceq wa wa wph vx vy vz vu cv vv cv vw cv cB
      c.pl grprinvlem.a caovassg adantlr wph vx cv cB wcel vn cv cB wcel vn cv
      vx cv c.pl co cO wceq wa simprl wph vx cv cB wcel vn cv cB wcel vn cv vx
      cv c.pl co cO wceq simprrl wph vx cv cB wcel vn cv cB wcel vn cv vx cv
      c.pl co cO wceq wa simprl caovassd wph vx cv cB wcel vn cv cB wcel vn cv
      vx cv c.pl co cO wceq wa wa wa vx cv vn cv c.pl co cO vx cv c.pl wph vx
      cv cB wcel vn cv cB wcel vn cv vx cv c.pl co cO wceq wa wa vx vy vz cB
      c.pl vn cv cO vx cv grprinvlem.c grprinvlem.o grprinvlem.i grprinvlem.a
      grprinvlem.n wph vx cv cB wcel vn cv cB wcel vn cv vx cv c.pl co cO wceq
      wa simprl wph vx cv cB wcel vn cv cB wcel vn cv vx cv c.pl co cO wceq
      simprrl wph vx cv cB wcel vn cv cB wcel vn cv vx cv c.pl co cO wceq
      simprrr grprinvd oveq1d wph vx cv cB wcel vn cv cB wcel vn cv vx cv c.pl
      co cO wceq wa wa wa vn cv vx cv c.pl co cO vx cv c.pl wph vx cv cB wcel
      vn cv cB wcel vn cv vx cv c.pl co cO wceq simprrr oveq2d 3eqtr3d anassrs
      expr rexlimdva mpd grprinvlem.i eqtr3d $.
  $}


