
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Finite_induction_(for_finite_ordinals).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                              Relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Introduce new constant symbols. $)
  $c X. $. $( Times symbol (cross product symbol) (read: 'cross') $)
  $c `' $. $( Small elevated smiley (converse operation) $)
  $c dom $. $( Domain $)
  $c ran $. $( Range $)
  $c |` $. $( Right hook (restriction symbol) $)
  $c " $. $( Left quote (image symbol) $)
  $c o. $. $( Small circle (composition symbol) $)
  $c Rel $. $( Relation predicate $)

  $( Extend the definition of a class to include the cross product. $)
  cxp $a class ( A X. B ) $.

  $( Extend the definition of a class to include the converse of a class. $)
  ccnv $a class `' A $.

  $( Extend the definition of a class to include the domain of a class. $)
  cdm $a class dom A $.

  $( Extend the definition of a class to include the range of a class. $)
  crn $a class ran A $.

  $( Extend the definition of a class to include the restriction of a class.
     (Read:  The restriction of ` A ` to ` B ` .) $)
  cres $a class ( A |` B ) $.

  $( Extend the definition of a class to include the image of a class.  (Read:
     The image of ` B ` under ` A ` .) $)
  cima $a class ( A " B ) $.

  $( Extend the definition of a class to include the composition of two
     classes.  (Read:  The composition of ` A ` and ` B ` .) $)
  ccom $a class ( A o. B ) $.

  $( Extend the definition of a wff to include the relation predicate.  (Read:
     ` A ` is a relation.) $)
  wrel $a wff Rel A $.

  ${
    $d x y z A $.  $d x y z B $.
    $( Define the cross product of two classes.  Definition 9.11 of [Quine]
       p. 64.  For example, ` ( { 1 , 5 } X. { 2 , 7 } ) = `
       ` ( { <. 1 , 2 >. , <. 1 , 7 >. } u. { <. 5 , 2 >. , <. 5 , 7 >. } ) `
       ( ~ ex-xp ).  Another example is that the set of rational numbers are
       defined in ~ df-q using the cross-product ` ( ZZ X. NN ) ` ; the left-
       and right-hand sides of the cross-product represent the top (integer)
       and bottom (natural) numbers of a fraction.  (Contributed by NM,
       4-Jul-1994.) $)
    df-xp $a |- ( A X. B ) = { <. x , y >. | ( x e. A /\ y e. B ) } $.

    $( Define the relation predicate.  Definition 6.4(1) of [TakeutiZaring]
       p. 23.  For alternate definitions, see ~ dfrel2 and ~ dfrel3 .
       (Contributed by NM, 1-Aug-1994.) $)
    df-rel $a |- ( Rel A <-> A C_ ( _V X. _V ) ) $.

    $( Define the converse of a class.  Definition 9.12 of [Quine] p. 64.  The
       converse of a binary relation swaps its arguments, i.e., if ` A e. _V `
       and ` B e. _V ` then ` ( A ``' R B <-> B R A ) ` , as proven in ~ brcnv
       (see ~ df-br and ~ df-rel for more on relations).  For example,
       ` ``' { <. 2 , 6 >. , <. 3 , 9 >. } = { <. 6 , 2 >. , <. 9 , 3 >. } `
       ( ~ ex-cnv ).  We use Quine's breve accent (smile) notation.  Like
       Quine, we use it as a prefix, which eliminates the need for
       parentheses.  Many authors use the postfix superscript "to the minus
       one."  "Converse" is Quine's terminology; some authors call it
       "inverse," especially when the argument is a function.  (Contributed by
       NM, 4-Jul-1994.) $)
    df-cnv $a |- `' A = { <. x , y >. | y A x } $.

    $( Define the composition of two classes.  Definition 6.6(3) of
       [TakeutiZaring] p. 24.  For example, ` ( ( exp o. cos ) `` 0 ) = _e `
       ( ~ ex-co ) because ` ( cos `` 0 ) = 1 ` (see ~ cos0 ) and
       ` ( exp `` 1 ) = _e ` (see ~ df-e ).  Note that Definition 7 of [Suppes]
       p. 63 reverses ` A ` and ` B ` , uses ` /. ` instead of ` o. ` , and
       calls the operation "relative product."  (Contributed by NM,
       4-Jul-1994.) $)
    df-co $a |- ( A o. B ) = { <. x , y >. | E. z ( x B z /\ z A y ) } $.

    $( Define the domain of a class.  Definition 3 of [Suppes] p. 59.  For
       example, ` F = { <. 2 , 6 >. , <. 3 , 9 >. } -> dom F = { 2 , 3 } `
       ( ~ ex-dm ).  Another example is the domain of the complex arctangent,
       ` ( A e. dom arctan <-> ( A e. CC /\ A =/= -u _i /\ A =/= _i ) ) ` (for
       proof see ~ atandm ).  Contrast with range (defined in ~ df-rn ).  For
       alternate definitions see ~ dfdm2 , ~ dfdm3 , and ~ dfdm4 .  The
       notation " ` dom ` " is used by Enderton; other authors sometimes use
       script D. (Contributed by NM, 1-Aug-1994.) $)
    df-dm $a |- dom A = { x | E. y x A y } $.

    $( Define the range of a class.  For example,
       ` F = { <. 2 , 6 >. , <. 3 , 9 >. } -> ran F = { 6 , 9 } ` ( ~ ex-rn ).
       Contrast with domain (defined in ~ df-dm ).  For alternate definitions,
       see ~ dfrn2 , ~ dfrn3 , and ~ dfrn4 .  The notation " ` ran ` " is used
       by Enderton; other authors sometimes use script R or script W.
       (Contributed by NM, 1-Aug-1994.) $)
    df-rn $a |- ran A = dom `' A $.

    $( Define the restriction of a class.  Definition 6.6(1) of [TakeutiZaring]
       p. 24.  For example, the expression ` ( exp |`` RR ) ` (used in
       ~ reeff1 ) means "the exponential function e to the x, but the exponent
       x must be in the reals" ( ~ df-ef defines the exponential function,
       which normally allows the exponent to be a complex number).  Another
       example is that ` ( F = { <. 2 , 6 >. , <. 3 , 9 >. } `
       ` /\ B = { 1 , 2 } ) -> ( F |`` B ) = { <. 2 , 6 >. } ` ( ~ ex-res ).
       (Contributed by NM, 2-Aug-1994.) $)
    df-res $a |- ( A |` B ) = ( A i^i ( B X. _V ) ) $.

    $( Define the image of a class (as restricted by another class).
       Definition 6.6(2) of [TakeutiZaring] p. 24.  For example,
` ( F = { <. 2 , 6 >. , <. 3 , 9 >. } /\ B = { 1 , 2 } ) -> ( F " B ) = { 6 } `
       ( ~ ex-ima ).  Contrast with restriction ( ~ df-res ) and range
       ( ~ df-rn ).  For an alternate definition, see ~ dfima2 .  (Contributed
       by NM, 2-Aug-1994.) $)
    df-ima $a |- ( A " B ) = ran ( A |` B ) $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.
    $( Equality theorem for cross product.  (Contributed by NM, 4-Jul-1994.) $)
    xpeq1 $p |- ( A = B -> ( A X. C ) = ( B X. C ) ) $=
      cA cB wceq vx cv cA wcel vy cv cC wcel wa vx vy copab vx cv cB wcel vy cv
      cC wcel wa vx vy copab cA cC cxp cB cC cxp cA cB wceq vx cv cA wcel vy cv
      cC wcel wa vx cv cB wcel vy cv cC wcel wa vx vy cA cB wceq vx cv cA wcel
      vx cv cB wcel vy cv cC wcel cA cB vx cv eleq2 anbi1d opabbidv vx vy cA cC
      df-xp vx vy cB cC df-xp 3eqtr4g $.

    $( Equality theorem for cross product.  (Contributed by NM, 5-Jul-1994.) $)
    xpeq2 $p |- ( A = B -> ( C X. A ) = ( C X. B ) ) $=
      cA cB wceq vx cv cC wcel vy cv cA wcel wa vx vy copab vx cv cC wcel vy cv
      cB wcel wa vx vy copab cC cA cxp cC cB cxp cA cB wceq vx cv cC wcel vy cv
      cA wcel wa vx cv cC wcel vy cv cB wcel wa vx vy cA cB wceq vy cv cA wcel
      vy cv cB wcel vx cv cC wcel cA cB vy cv eleq2 anbi2d opabbidv vx vy cC cA
      df-xp vx vy cC cB df-xp 3eqtr4g $.

    $( Membership in a cross product.  Uses fewer axioms than ~ elxp .
       (Contributed by NM, 4-Jul-1994.) $)
    elxpi $p |- ( A e. ( B X. C ) -> E. x E. y ( A = <. x , y >. /\
               ( x e. B /\ y e. C ) ) ) $=
      cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vx wex
      cA vz cv vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vx
      wex vz cab cB cC cxp cA vz cv vx cv vy cv cop wceq vx cv cB wcel vy cv cC
      wcel wa wa vy wex vx wex vz cab wcel cA vx cv vy cv cop wceq vx cv cB
      wcel vy cv cC wcel wa wa vy wex vx wex vz cv vx cv vy cv cop wceq vx cv
      cB wcel vy cv cC wcel wa wa vy wex vx wex cA vx cv vy cv cop wceq vx cv
      cB wcel vy cv cC wcel wa wa vy wex vx wex vz cA vz cv vx cv vy cv cop
      wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vx wex vz cab vz cv cA wceq
      vz cv vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa cA vx cv vy
      cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vx vy vz cv cA wceq vz cv
      vx cv vy cv cop wceq cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel
      wa vz cv cA vx cv vy cv cop eqeq1 anbi1d 2exbidv elabg ibi cB cC cxp vx
      cv cB wcel vy cv cC wcel wa vx vy copab vz cv vx cv vy cv cop wceq vx cv
      cB wcel vy cv cC wcel wa wa vy wex vx wex vz cab vx vy cB cC df-xp vx cv
      cB wcel vy cv cC wcel wa vx vy vz df-opab eqtri eleq2s $.

    $( Membership in a cross product.  (Contributed by NM, 4-Jul-1994.) $)
    elxp $p |- ( A e. ( B X. C ) <-> E. x E. y ( A = <. x , y >. /\
               ( x e. B /\ y e. C ) ) ) $=
      cA cB cC cxp wcel cA vx cv cB wcel vy cv cC wcel wa vx vy copab wcel cA
      vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vx wex cB
      cC cxp vx cv cB wcel vy cv cC wcel wa vx vy copab cA vx vy cB cC df-xp
      eleq2i vx cv cB wcel vy cv cC wcel wa vx vy cA elopab bitri $.

    $( Membership in a cross product.  (Contributed by NM, 23-Feb-2004.) $)
    elxp2 $p |- ( A e. ( B X. C ) <-> E. x e. B E. y e. C A = <. x , y >. ) $=
      vx cv cB wcel cA vx cv vy cv cop wceq vy cC wrex wa vx wex cA vx cv vy cv
      cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vx wex cA vx cv vy cv
      cop wceq vy cC wrex vx cB wrex cA cB cC cxp wcel vx cv cB wcel cA vx cv
      vy cv cop wceq vy cC wrex wa cA vx cv vy cv cop wceq vx cv cB wcel vy cv
      cC wcel wa wa vy wex vx vx cv cB wcel cA vx cv vy cv cop wceq wa vy cC
      wrex vy cv cC wcel vx cv cB wcel cA vx cv vy cv cop wceq wa wa vy wex vx
      cv cB wcel cA vx cv vy cv cop wceq vy cC wrex wa cA vx cv vy cv cop wceq
      vx cv cB wcel vy cv cC wcel wa wa vy wex vx cv cB wcel cA vx cv vy cv cop
      wceq wa vy cC df-rex vx cv cB wcel cA vx cv vy cv cop wceq vy cC r19.42v
      vy cv cC wcel vx cv cB wcel cA vx cv vy cv cop wceq wa wa cA vx cv vy cv
      cop wceq vx cv cB wcel vy cv cC wcel wa wa vy vy cv cC wcel vx cv cB wcel
      cA vx cv vy cv cop wceq an13 exbii 3bitr3i exbii cA vx cv vy cv cop wceq
      vy cC wrex vx cB df-rex vx vy cA cB cC elxp 3bitr4ri $.
  $}

  $( Equality theorem for cross product.  (Contributed by FL, 31-Aug-2009.) $)
  xpeq12 $p |- ( ( A = B /\ C = D ) -> ( A X. C ) = ( B X. D ) ) $=
    cA cB wceq cC cD wceq cA cC cxp cB cC cxp cB cD cxp cA cB cC xpeq1 cC cD cB
    xpeq2 sylan9eq $.

  ${
    xpeq1i.1 $e |- A = B $.
    $( Equality inference for cross product.  (Contributed by NM,
       21-Dec-2008.) $)
    xpeq1i $p |- ( A X. C ) = ( B X. C ) $=
      cA cB wceq cA cC cxp cB cC cxp wceq xpeq1i.1 cA cB cC xpeq1 ax-mp $.

    $( Equality inference for cross product.  (Contributed by NM,
       21-Dec-2008.) $)
    xpeq2i $p |- ( C X. A ) = ( C X. B ) $=
      cA cB wceq cC cA cxp cC cB cxp wceq xpeq1i.1 cA cB cC xpeq2 ax-mp $.
  $}

  ${
    xpeq12i.1 $e |- A = B $.
    xpeq12i.2 $e |- C = D $.
    $( Equality inference for cross product.  (Contributed by FL,
       31-Aug-2009.) $)
    xpeq12i $p |- ( A X. C ) = ( B X. D ) $=
      cA cB wceq cC cD wceq cA cC cxp cB cD cxp wceq xpeq12i.1 xpeq12i.2 cA cB
      cC cD xpeq12 mp2an $.
  $}

  ${
    xpeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for cross product.  (Contributed by Jeff Madsen,
       17-Jun-2010.) $)
    xpeq1d $p |- ( ph -> ( A X. C ) = ( B X. C ) ) $=
      wph cA cB wceq cA cC cxp cB cC cxp wceq xpeq1d.1 cA cB cC xpeq1 syl $.

    $( Equality deduction for cross product.  (Contributed by Jeff Madsen,
       17-Jun-2010.) $)
    xpeq2d $p |- ( ph -> ( C X. A ) = ( C X. B ) ) $=
      wph cA cB wceq cC cA cxp cC cB cxp wceq xpeq1d.1 cA cB cC xpeq2 syl $.

    xpeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for cross product.  (Contributed by NM,
       8-Dec-2013.) $)
    xpeq12d $p |- ( ph -> ( A X. C ) = ( B X. D ) ) $=
      wph cA cB wceq cC cD wceq cA cC cxp cB cD cxp wceq xpeq1d.1 xpeq12d.2 cA
      cB cC cD xpeq12 syl2anc $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d x y z $.
    nfxp.1 $e |- F/_ x A $.
    nfxp.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for cross product.  (Contributed by
       NM, 15-Sep-2003.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nfxp $p |- F/_ x ( A X. B ) $=
      vx cA cB cxp vy cv cA wcel vz cv cB wcel wa vy vz copab vy vz cA cB df-xp
      vy cv cA wcel vz cv cB wcel wa vy vz vx vy cv cA wcel vz cv cB wcel vx vx
      vy cA nfxp.1 nfcri vx vz cB nfxp.2 nfcri nfan nfopab nfcxfr $.
  $}

  ${
    $d A w y z $.  $d B w y z $.  $d C w y z $.  $d D w y z $.  $d w x y z $.
    $( Distribute proper substitution through the cross product of two
       classes.  (Contributed by Alan Sare, 10-Nov-2012.) $)
    csbxpg $p |- ( A e. D -> [_ A / x ]_ ( B X. C ) =
                ( [_ A / x ]_ B X. [_ A / x ]_ C ) ) $=
      cA cD wcel vx cA vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel
      wa wa vy wex vw wex vz cab csb vz cv vw cv vy cv cop wceq vw cv vx cA cB
      csb wcel vy cv vx cA cC csb wcel wa wa vy wex vw wex vz cab vx cA cB cC
      cxp csb vx cA cB csb vx cA cC csb cxp cA cD wcel vx cA vz cv vw cv vy cv
      cop wceq vw cv cB wcel vy cv cC wcel wa wa vy wex vw wex vz cab csb vz cv
      vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel wa wa vy wex vw wex vx
      cA wsbc vz cab vz cv vw cv vy cv cop wceq vw cv vx cA cB csb wcel vy cv
      vx cA cC csb wcel wa wa vy wex vw wex vz cab vz cv vw cv vy cv cop wceq
      vw cv cB wcel vy cv cC wcel wa wa vy wex vw wex vx vz cA cD csbabg cA cD
      wcel vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel wa wa vy wex
      vw wex vx cA wsbc vz cv vw cv vy cv cop wceq vw cv vx cA cB csb wcel vy
      cv vx cA cC csb wcel wa wa vy wex vw wex vz cA cD wcel vz cv vw cv vy cv
      cop wceq vw cv cB wcel vy cv cC wcel wa wa vy wex vw wex vx cA wsbc vz cv
      vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel wa wa vy wex vx cA wsbc
      vw wex vz cv vw cv vy cv cop wceq vw cv vx cA cB csb wcel vy cv vx cA cC
      csb wcel wa wa vy wex vw wex vz cv vw cv vy cv cop wceq vw cv cB wcel vy
      cv cC wcel wa wa vy wex vw vx cA cD sbcexg cA cD wcel vz cv vw cv vy cv
      cop wceq vw cv cB wcel vy cv cC wcel wa wa vy wex vx cA wsbc vz cv vw cv
      vy cv cop wceq vw cv vx cA cB csb wcel vy cv vx cA cC csb wcel wa wa vy
      wex vw cA cD wcel vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel
      wa wa vy wex vx cA wsbc vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv cC
      wcel wa wa vx cA wsbc vy wex vz cv vw cv vy cv cop wceq vw cv vx cA cB
      csb wcel vy cv vx cA cC csb wcel wa wa vy wex vz cv vw cv vy cv cop wceq
      vw cv cB wcel vy cv cC wcel wa wa vy vx cA cD sbcexg cA cD wcel vz cv vw
      cv vy cv cop wceq vw cv cB wcel vy cv cC wcel wa wa vx cA wsbc vz cv vw
      cv vy cv cop wceq vw cv vx cA cB csb wcel vy cv vx cA cC csb wcel wa wa
      vy cA cD wcel vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel wa
      wa vx cA wsbc vz cv vw cv vy cv cop wceq vx cA wsbc vw cv cB wcel vy cv
      cC wcel wa vx cA wsbc wa vz cv vw cv vy cv cop wceq vw cv vx cA cB csb
      wcel vy cv vx cA cC csb wcel wa wa vz cv vw cv vy cv cop wceq vw cv cB
      wcel vy cv cC wcel wa vx cA cD sbcang cA cD wcel vz cv vw cv vy cv cop
      wceq vx cA wsbc vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv cC wcel wa
      vx cA wsbc vw cv vx cA cB csb wcel vy cv vx cA cC csb wcel wa vz cv vw cv
      vy cv cop wceq vx cA cD sbcg cA cD wcel vw cv cB wcel vy cv cC wcel wa vx
      cA wsbc vw cv cB wcel vx cA wsbc vy cv cC wcel vx cA wsbc wa vw cv vx cA
      cB csb wcel vy cv vx cA cC csb wcel wa vw cv cB wcel vy cv cC wcel vx cA
      cD sbcang cA cD wcel vw cv cB wcel vx cA wsbc vw cv vx cA cB csb wcel vy
      cv cC wcel vx cA wsbc vy cv vx cA cC csb wcel vx cA vw cv cB cD sbcel2g
      vx cA vy cv cC cD sbcel2g anbi12d bitrd anbi12d bitrd exbidv bitrd exbidv
      bitrd abbidv eqtrd vx cA cB cC cxp vz cv vw cv vy cv cop wceq vw cv cB
      wcel vy cv cC wcel wa wa vy wex vw wex vz cab cB cC cxp vw cv cB wcel vy
      cv cC wcel wa vw vy copab vz cv vw cv vy cv cop wceq vw cv cB wcel vy cv
      cC wcel wa wa vy wex vw wex vz cab vw vy cB cC df-xp vw cv cB wcel vy cv
      cC wcel wa vw vy vz df-opab eqtri csbeq2i vx cA cB csb vx cA cC csb cxp
      vw cv vx cA cB csb wcel vy cv vx cA cC csb wcel wa vw vy copab vz cv vw
      cv vy cv cop wceq vw cv vx cA cB csb wcel vy cv vx cA cC csb wcel wa wa
      vy wex vw wex vz cab vw vy vx cA cB csb vx cA cC csb df-xp vw cv vx cA cB
      csb wcel vy cv vx cA cC csb wcel wa vw vy vz df-opab eqtri 3eqtr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( The empty set is not a member of a cross product.  (Contributed by NM,
       2-May-1996.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    0nelxp $p |- -. (/) e. ( A X. B ) $=
      c0 cA cB cxp wcel c0 vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa
      wa vy wex vx wex c0 vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa
      wa vy wex vx c0 vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wa vy
      vx cv vy cv cop c0 wne c0 vx cv vy cv cop wceq vx cv cA wcel vy cv cB
      wcel wa wa wn vx cv vy cv vx vex vy vex opnzi c0 vx cv vy cv cop wceq vx
      cv cA wcel vy cv cB wcel wa wa vx cv vy cv cop c0 c0 vx cv vy cv cop wceq
      vx cv cA wcel vy cv cB wcel wa wa c0 vx cv vy cv cop c0 vx cv vy cv cop
      wceq vx cv cA wcel vy cv cB wcel wa simpl eqcomd necon3ai ax-mp nex nex
      vx vy c0 cA cB elxp mtbir $.

    $( A member of a cross product (ordered pair) doesn't contain the empty
       set.  (Contributed by NM, 15-Dec-2008.) $)
    0nelelxp $p |- ( C e. ( A X. B ) -> -. (/) e. C ) $=
      cC cA cB cxp wcel cC vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa
      wa vy wex vx wex c0 cC wcel wn vx vy cC cA cB elxp cC vx cv vy cv cop
      wceq vx cv cA wcel vy cv cB wcel wa wa c0 cC wcel wn vx vy cC vx cv vy cv
      cop wceq vx cv cA wcel vy cv cB wcel wa wa c0 cC wcel c0 vx cv vy cv cop
      wcel vx cv vy cv 0nelop cC vx cv vy cv cop wceq vx cv cA wcel vy cv cB
      wcel wa wa cC vx cv vy cv cop c0 cC vx cv vy cv cop wceq vx cv cA wcel vy
      cv cB wcel wa simpl eleq2d mtbiri exlimivv sylbi $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.
    $( Ordered pair membership in a cross product.  (Contributed by NM,
       15-Nov-1994.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)
       (Revised by Mario Carneiro, 26-Apr-2015.) $)
    opelxp $p |- ( <. A , B >. e. ( C X. D ) <-> ( A e. C /\ B e. D ) ) $=
      cA cB cop cC cD cxp wcel cA cB cop vx cv vy cv cop wceq vy cD wrex vx cC
      wrex cA cC wcel cB cD wcel wa vx vy cA cB cop cC cD elxp2 cA cB cop vx cv
      vy cv cop wceq vy cD wrex vx cC wrex cA cC wcel cB cD wcel wa cA cB cop
      vx cv vy cv cop wceq cA cC wcel cB cD wcel wa vx vy cC cD cA cB cop vx cv
      vy cv cop wceq cA cC wcel cB cD wcel wa vx cv cC wcel vy cv cD wcel wa cA
      cB cop vx cv vy cv cop wceq cA vx cv wceq cB vy cv wceq wa cA cC wcel cB
      cD wcel wa vx cv cC wcel vy cv cD wcel wa wb cA cB vx cv vy cv vx vex vy
      vex opth2 cA vx cv wceq cA cC wcel vx cv cC wcel cB vy cv wceq cB cD wcel
      vy cv cD wcel cA vx cv cC eleq1 cB vy cv cD eleq1 bi2anan9 sylbi biimprcd
      rexlimivv cA cC wcel cB cD wcel cA cB cop cA cB cop wceq cA cB cop vx cv
      vy cv cop wceq vy cD wrex vx cC wrex cA cB cop eqid cA cB cop vx cv vy cv
      cop wceq cA cB cop cA cB cop wceq cA cB cop cA vy cv cop wceq vx vy cA cB
      cC cD vx cv cA wceq vx cv vy cv cop cA vy cv cop cA cB cop vx cv cA vy cv
      opeq1 eqeq2d vy cv cB wceq cA vy cv cop cA cB cop cA cB cop vy cv cB cA
      opeq2 eqeq2d rspc2ev mp3an3 impbii bitri $.

    $( Binary relation on a cross product.  (Contributed by NM,
       22-Apr-2004.) $)
    brxp $p |- ( A ( C X. D ) B <-> ( A e. C /\ B e. D ) ) $=
      cA cB cC cD cxp wbr cA cB cop cC cD cxp wcel cA cC wcel cB cD wcel wa cA
      cB cC cD cxp df-br cA cB cC cD opelxp bitri $.
  $}

  $( Ordered pair membership in a cross product (implication).  (Contributed by
     NM, 28-May-1995.) $)
  opelxpi $p |- ( ( A e. C /\ B e. D ) -> <. A , B >. e. ( C X. D ) ) $=
    cA cB cop cC cD cxp wcel cA cC wcel cB cD wcel wa cA cB cC cD opelxp
    biimpri $.

  $( The first member of an ordered pair of classes in a cross product belongs
     to first cross product argument.  (Contributed by NM, 28-May-2008.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)
  opelxp1 $p |- ( <. A , B >. e. ( C X. D ) -> A e. C ) $=
    cA cB cop cC cD cxp wcel cA cC wcel cB cD wcel cA cB cC cD opelxp simplbi
    $.

  $( The second member of an ordered pair of classes in a cross product belongs
     to second cross product argument.  (Contributed by Mario Carneiro,
     26-Apr-2015.) $)
  opelxp2 $p |- ( <. A , B >. e. ( C X. D ) -> B e. D ) $=
    cA cB cop cC cD cxp wcel cA cC wcel cB cD wcel cA cB cC cD opelxp simprbi
    $.

  $( The first member of an ordered triple of classes in a cross product
     belongs to first cross product argument.  (Contributed by NM,
     28-May-2008.) $)
  otelxp1 $p |- ( <. <. A , B >. , C >. e. ( ( R X. S ) X. T )
          -> A e. R ) $=
    cA cB cop cC cop cR cS cxp cT cxp wcel cA cB cop cR cS cxp wcel cA cR wcel
    cA cB cop cC cR cS cxp cT opelxp1 cA cB cR cS opelxp1 syl $.

  ${
    $d x y z A $.  $d x y z B $.  $d y z ph $.  $d x ps $.
    rabxp.1 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
    $( Membership in a class builder restricted to a cross product.
       (Contributed by NM, 20-Feb-2014.) $)
    rabxp $p |- { x e. ( A X. B ) | ph }
             = { <. y , z >. | ( y e. A /\ z e. B /\ ps ) } $=
      vx cv cA cB cxp wcel wph wa vx cab vx cv vy cv vz cv cop wceq vy cv cA
      wcel vz cv cB wcel wps w3a wa vz wex vy wex vx cab wph vx cA cB cxp crab
      vy cv cA wcel vz cv cB wcel wps w3a vy vz copab vx cv cA cB cxp wcel wph
      wa vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wps w3a wa vz
      wex vy wex vx vx cv cA cB cxp wcel wph wa vx cv vy cv vz cv cop wceq vy
      cv cA wcel vz cv cB wcel wa wa vz wex vy wex wph wa vx cv vy cv vz cv cop
      wceq vy cv cA wcel vz cv cB wcel wa wa wph wa vz wex vy wex vx cv vy cv
      vz cv cop wceq vy cv cA wcel vz cv cB wcel wps w3a wa vz wex vy wex vx cv
      cA cB cxp wcel vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wa
      wa vz wex vy wex wph vy vz vx cv cA cB elxp anbi1i vx cv vy cv vz cv cop
      wceq vy cv cA wcel vz cv cB wcel wa wa wph vy vz 19.41vv vx cv vy cv vz
      cv cop wceq vy cv cA wcel vz cv cB wcel wa wa wph wa vx cv vy cv vz cv
      cop wceq vy cv cA wcel vz cv cB wcel wps w3a wa vy vz vx cv vy cv vz cv
      cop wceq vy cv cA wcel vz cv cB wcel wa wa wph wa vx cv vy cv vz cv cop
      wceq vy cv cA wcel vz cv cB wcel wa wph wa wa vx cv vy cv vz cv cop wceq
      vy cv cA wcel vz cv cB wcel wps w3a wa vx cv vy cv vz cv cop wceq vy cv
      cA wcel vz cv cB wcel wa wph anass vx cv vy cv vz cv cop wceq vy cv cA
      wcel vz cv cB wcel wa wph wa vy cv cA wcel vz cv cB wcel wps w3a vx cv vy
      cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wa wph wa vy cv cA wcel vz
      cv cB wcel wa wps wa vy cv cA wcel vz cv cB wcel wps w3a vx cv vy cv vz
      cv cop wceq wph wps vy cv cA wcel vz cv cB wcel wa rabxp.1 anbi2d vy cv
      cA wcel vz cv cB wcel wps df-3an syl6bbr pm5.32i bitri 2exbii 3bitr2i
      abbii wph vx cA cB cxp df-rab vy cv cA wcel vz cv cB wcel wps w3a vy vz
      vx df-opab 3eqtr4i $.
  $}

  $( A true binary relation on a relation implies the arguments are sets.
     (This is a property of our ordered pair definition.)  (Contributed by
     Mario Carneiro, 26-Apr-2015.) $)
  brrelex12 $p |- ( ( Rel R /\ A R B ) -> ( A e. _V /\ B e. _V ) ) $=
    cR wrel cA cB cR wbr wa cA cB cvv cvv cxp wbr cA cvv wcel cB cvv wcel wa cR
    wrel cA cB cR wbr cA cB cvv cvv cxp wbr cR wrel cR cvv cvv cxp cA cB cR
    wrel cR cvv cvv cxp wss cR df-rel biimpi ssbrd imp cA cB cvv cvv brxp sylib
    $.

  $( A true binary relation on a relation implies the first argument is a set.
     (This is a property of our ordered pair definition.)  (Contributed by NM,
     18-May-2004.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
  brrelex $p |- ( ( Rel R /\ A R B ) -> A e. _V ) $=
    cR wrel cA cB cR wbr wa cA cvv wcel cB cvv wcel cA cB cR brrelex12 simpld
    $.

  $( A true binary relation on a relation implies the second argument is a
     set.  (This is a property of our ordered pair definition.)  (Contributed
     by Mario Carneiro, 26-Apr-2015.) $)
  brrelex2 $p |- ( ( Rel R /\ A R B ) -> B e. _V ) $=
    cR wrel cA cB cR wbr wa cA cvv wcel cB cvv wcel cA cB cR brrelex12 simprd
    $.

  ${
    brrelexi.1 $e |- Rel R $.
    $( The first argument of a binary relation exists.  (An artifact of our
       ordered pair definition.)  (Contributed by NM, 4-Jun-1998.) $)
    brrelexi $p |- ( A R B -> A e. _V ) $=
      cR wrel cA cB cR wbr cA cvv wcel brrelexi.1 cA cB cR brrelex mpan $.

    $( The second argument of a binary relation exists.  (An artifact of our
       ordered pair definition.)  (Contributed by Mario Carneiro,
       26-Apr-2015.) $)
    brrelex2i $p |- ( A R B -> B e. _V ) $=
      cR wrel cA cB cR wbr cB cvv wcel brrelexi.1 cA cB cR brrelex2 mpan $.
  $}

  ${
    nprrel.1 $e |- Rel R $.
    nprrel.2 $e |- -. A e. _V $.
    $( No proper class is related to anything via any relation.  (Contributed
       by Roy F. Longton, 30-Jul-2005.) $)
    nprrel $p |- -. A R B $=
      cA cB cR wbr cA cvv wcel nprrel.2 cA cB cR nprrel.1 brrelexi mto $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Representation of a constant function using the mapping operation.
       (Note that ` x ` cannot appear free in ` B ` .)  (Contributed by NM,
       12-Oct-1999.)  (Revised by Mario Carneiro, 16-Nov-2013.) $)
    fconstmpt $p |- ( A X. { B } ) = ( x e. A |-> B ) $=
      vx cv cA wcel vy cv cB csn wcel wa vx vy copab vx cv cA wcel vy cv cB
      wceq wa vx vy copab cA cB csn cxp vx cA cB cmpt vx cv cA wcel vy cv cB
      csn wcel wa vx cv cA wcel vy cv cB wceq wa vx vy vy cv cB csn wcel vy cv
      cB wceq vx cv cA wcel vy cB elsn anbi2i opabbii vx vy cA cB csn df-xp vx
      vy cA cB df-mpt 3eqtr4i $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y z C $.  $d x y z R $.
    vtoclr.1 $e |- Rel R $.
    vtoclr.2 $e |- ( ( x R y /\ y R z ) -> x R z ) $.
    $( Variable to class conversion of transitive relation.  (Contributed by
       NM, 9-Jun-1998.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    vtoclr $p |- ( ( A R B /\ B R C ) -> A R C ) $=
      cA cB cR wbr cB cC cR wbr wa cA cC cR wbr cA cB cR wbr cB cC cR wbr cA cB
      cR wbr cB cC cR wbr wa cA cC cR wbr wi cA cB cR wbr cA cvv wcel cB cvv
      wcel wa cB cC cR wbr cC cvv wcel cA cB cR wbr cB cC cR wbr wa cA cC cR
      wbr wi cA cB cR wbr cA cvv wcel cB cvv wcel cA cB cR vtoclr.1 brrelexi cA
      cB cR vtoclr.1 brrelex2i jca cB cC cR vtoclr.1 brrelex2i cC cvv wcel vx
      cv vy cv cR wbr vy cv cC cR wbr wa vx cv cC cR wbr wi wi cC cvv wcel cA
      vy cv cR wbr vy cv cC cR wbr wa cA cC cR wbr wi wi cC cvv wcel cA cB cR
      wbr cB cC cR wbr wa cA cC cR wbr wi wi vx vy cA cB cvv cvv vx cv cA wceq
      vx cv vy cv cR wbr vy cv cC cR wbr wa vx cv cC cR wbr wi cA vy cv cR wbr
      vy cv cC cR wbr wa cA cC cR wbr wi cC cvv wcel vx cv cA wceq vx cv vy cv
      cR wbr vy cv cC cR wbr wa cA vy cv cR wbr vy cv cC cR wbr wa vx cv cC cR
      wbr cA cC cR wbr vx cv cA wceq vx cv vy cv cR wbr cA vy cv cR wbr vy cv
      cC cR wbr vx cv cA vy cv cR breq1 anbi1d vx cv cA cC cR breq1 imbi12d
      imbi2d vy cv cB wceq cA vy cv cR wbr vy cv cC cR wbr wa cA cC cR wbr wi
      cA cB cR wbr cB cC cR wbr wa cA cC cR wbr wi cC cvv wcel vy cv cB wceq cA
      vy cv cR wbr vy cv cC cR wbr wa cA cB cR wbr cB cC cR wbr wa cA cC cR wbr
      vy cv cB wceq cA vy cv cR wbr cA cB cR wbr vy cv cC cR wbr cB cC cR wbr
      vy cv cB cA cR breq2 vy cv cB cC cR breq1 anbi12d imbi1d imbi2d vx cv vy
      cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vx cv vy cv cR wbr
      vy cv cC cR wbr wa vx cv cC cR wbr wi vz cC cvv vz cv cC wceq vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vy cv cR wbr vy cv cC cR wbr wa vx cv
      vz cv cR wbr vx cv cC cR wbr vz cv cC wceq vy cv vz cv cR wbr vy cv cC cR
      wbr vx cv vy cv cR wbr vz cv cC vy cv cR breq2 anbi2d vz cv cC vx cv cR
      breq2 imbi12d vtoclr.2 vtoclg vtocl2g syl2im imp pm2.43i $.
  $}

  $( Ordered pair membership in the universal class of ordered pairs.
     (Contributed by Mario Carneiro, 3-May-2015.) $)
  opelvvg $p |- ( ( A e. V /\ B e. W ) -> <. A , B >. e. ( _V X. _V ) ) $=
    cA cV wcel cA cvv wcel cB cvv wcel cA cB cop cvv cvv cxp wcel cB cW wcel cA
    cV elex cB cW elex cA cB cvv cvv opelxpi syl2an $.

  ${
    opelvv.1 $e |- A e. _V $.
    opelvv.2 $e |- B e. _V $.
    $( Ordered pair membership in the universal class of ordered pairs.
       (Contributed by NM, 22-Aug-2013.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    opelvv $p |- <. A , B >. e. ( _V X. _V ) $=
      cA cvv wcel cB cvv wcel cA cB cop cvv cvv cxp wcel opelvv.1 opelvv.2 cA
      cB cvv cvv opelxpi mp2an $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.
    $( Justification theorem for an ordered pair definition that works for any
       classes, including proper classes.  This is a possible definition
       implied by the footnote in [Jech] p. 78, which says, "The sophisticated
       reader will not object to our use of a pair of classes."  (Contributed
       by NM, 28-Sep-2003.) $)
    opthprc $p |- ( ( ( A X. { (/) } ) u. ( B X. { { (/) } } ) ) =
                    ( ( C X. { (/) } ) u. ( D X. { { (/) } } ) )
                  <-> ( A = C /\ B = D ) ) $=
      cA c0 csn cxp cB c0 csn csn cxp cun cC c0 csn cxp cD c0 csn csn cxp cun
      wceq cA cC wceq cB cD wceq wa cA c0 csn cxp cB c0 csn csn cxp cun cC c0
      csn cxp cD c0 csn csn cxp cun wceq cA cC wceq cB cD wceq cA c0 csn cxp cB
      c0 csn csn cxp cun cC c0 csn cxp cD c0 csn csn cxp cun wceq vx cA cC cA
      c0 csn cxp cB c0 csn csn cxp cun cC c0 csn cxp cD c0 csn csn cxp cun wceq
      vx cv c0 cop cA c0 csn cxp cB c0 csn csn cxp cun wcel vx cv c0 cop cC c0
      csn cxp cD c0 csn csn cxp cun wcel vx cv cA wcel vx cv cC wcel cA c0 csn
      cxp cB c0 csn csn cxp cun cC c0 csn cxp cD c0 csn csn cxp cun vx cv c0
      cop eleq2 vx cv c0 cop cA c0 csn cxp wcel vx cv c0 cop cB c0 csn csn cxp
      wcel wo vx cv cA wcel c0 c0 csn csn wcel wo vx cv c0 cop cA c0 csn cxp cB
      c0 csn csn cxp cun wcel vx cv cA wcel vx cv c0 cop cA c0 csn cxp wcel vx
      cv cA wcel vx cv c0 cop cB c0 csn csn cxp wcel c0 c0 csn csn wcel vx cv
      c0 cop cA c0 csn cxp wcel vx cv cA wcel c0 c0 csn wcel c0 0ex snid vx cv
      c0 cA c0 csn opelxp mpbiran2 vx cv c0 cop cB c0 csn csn cxp wcel vx cv cB
      wcel c0 c0 csn csn wcel wa c0 c0 csn csn wcel vx cv c0 cB c0 csn csn
      opelxp c0 c0 csn csn wcel vx cv cB wcel c0 c0 csn csn wcel c0 c0 csn
      0nep0 c0 c0 csn 0ex elsnc nemtbir bianfi bitr4i orbi12i vx cv c0 cop cA
      c0 csn cxp cB c0 csn csn cxp elun c0 c0 csn csn wcel vx cv cA wcel c0 c0
      csn csn wcel c0 c0 csn 0nep0 c0 c0 csn 0ex elsnc nemtbir biorfi 3bitr4ri
      vx cv c0 cop cC c0 csn cxp wcel vx cv c0 cop cD c0 csn csn cxp wcel wo vx
      cv cC wcel c0 c0 csn csn wcel wo vx cv c0 cop cC c0 csn cxp cD c0 csn csn
      cxp cun wcel vx cv cC wcel vx cv c0 cop cC c0 csn cxp wcel vx cv cC wcel
      vx cv c0 cop cD c0 csn csn cxp wcel c0 c0 csn csn wcel vx cv c0 cop cC c0
      csn cxp wcel vx cv cC wcel c0 c0 csn wcel c0 0ex snid vx cv c0 cC c0 csn
      opelxp mpbiran2 vx cv c0 cop cD c0 csn csn cxp wcel vx cv cD wcel c0 c0
      csn csn wcel wa c0 c0 csn csn wcel vx cv c0 cD c0 csn csn opelxp c0 c0
      csn csn wcel vx cv cD wcel c0 c0 csn csn wcel c0 c0 csn 0nep0 c0 c0 csn
      0ex elsnc nemtbir bianfi bitr4i orbi12i vx cv c0 cop cC c0 csn cxp cD c0
      csn csn cxp elun c0 c0 csn csn wcel vx cv cC wcel c0 c0 csn csn wcel c0
      c0 csn 0nep0 c0 c0 csn 0ex elsnc nemtbir biorfi 3bitr4ri 3bitr4g eqrdv cA
      c0 csn cxp cB c0 csn csn cxp cun cC c0 csn cxp cD c0 csn csn cxp cun wceq
      vx cB cD cA c0 csn cxp cB c0 csn csn cxp cun cC c0 csn cxp cD c0 csn csn
      cxp cun wceq vx cv c0 csn cop cA c0 csn cxp cB c0 csn csn cxp cun wcel vx
      cv c0 csn cop cC c0 csn cxp cD c0 csn csn cxp cun wcel vx cv cB wcel vx
      cv cD wcel cA c0 csn cxp cB c0 csn csn cxp cun cC c0 csn cxp cD c0 csn
      csn cxp cun vx cv c0 csn cop eleq2 vx cv c0 csn cop cA c0 csn cxp wcel vx
      cv c0 csn cop cB c0 csn csn cxp wcel wo c0 csn c0 csn wcel vx cv cB wcel
      wo vx cv c0 csn cop cA c0 csn cxp cB c0 csn csn cxp cun wcel vx cv cB
      wcel vx cv c0 csn cop cA c0 csn cxp wcel c0 csn c0 csn wcel vx cv c0 csn
      cop cB c0 csn csn cxp wcel vx cv cB wcel vx cv c0 csn cop cA c0 csn cxp
      wcel vx cv cA wcel c0 csn c0 csn wcel wa c0 csn c0 csn wcel vx cv c0 csn
      cA c0 csn opelxp c0 csn c0 csn wcel vx cv cA wcel c0 csn c0 csn wcel c0
      c0 csn 0nep0 c0 csn c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0
      p0ex elsnc c0 csn c0 eqcom bitri nemtbir bianfi bitr4i vx cv c0 csn cop
      cB c0 csn csn cxp wcel vx cv cB wcel c0 csn c0 csn csn wcel c0 csn p0ex
      snid vx cv c0 csn cB c0 csn csn opelxp mpbiran2 orbi12i vx cv c0 csn cop
      cA c0 csn cxp cB c0 csn csn cxp elun c0 csn c0 csn wcel wn vx cv cB wcel
      c0 csn c0 csn wcel vx cv cB wcel wo wb c0 csn c0 csn wcel c0 c0 csn 0nep0
      c0 csn c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0
      csn c0 eqcom bitri nemtbir c0 csn c0 csn wcel vx cv cB wcel biorf ax-mp
      3bitr4ri vx cv c0 csn cop cC c0 csn cxp wcel vx cv c0 csn cop cD c0 csn
      csn cxp wcel wo c0 csn c0 csn wcel vx cv cD wcel wo vx cv c0 csn cop cC
      c0 csn cxp cD c0 csn csn cxp cun wcel vx cv cD wcel vx cv c0 csn cop cC
      c0 csn cxp wcel c0 csn c0 csn wcel vx cv c0 csn cop cD c0 csn csn cxp
      wcel vx cv cD wcel vx cv c0 csn cop cC c0 csn cxp wcel vx cv cC wcel c0
      csn c0 csn wcel wa c0 csn c0 csn wcel vx cv c0 csn cC c0 csn opelxp c0
      csn c0 csn wcel vx cv cC wcel c0 csn c0 csn wcel c0 c0 csn 0nep0 c0 csn
      c0 csn wcel c0 csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0 csn c0
      eqcom bitri nemtbir bianfi bitr4i vx cv c0 csn cop cD c0 csn csn cxp wcel
      vx cv cD wcel c0 csn c0 csn csn wcel c0 csn p0ex snid vx cv c0 csn cD c0
      csn csn opelxp mpbiran2 orbi12i vx cv c0 csn cop cC c0 csn cxp cD c0 csn
      csn cxp elun c0 csn c0 csn wcel wn vx cv cD wcel c0 csn c0 csn wcel vx cv
      cD wcel wo wb c0 csn c0 csn wcel c0 c0 csn 0nep0 c0 csn c0 csn wcel c0
      csn c0 wceq c0 c0 csn wceq c0 csn c0 p0ex elsnc c0 csn c0 eqcom bitri
      nemtbir c0 csn c0 csn wcel vx cv cD wcel biorf ax-mp 3bitr4ri 3bitr4g
      eqrdv jca cA cC wceq cA c0 csn cxp cC c0 csn cxp wceq cB c0 csn csn cxp
      cD c0 csn csn cxp wceq cA c0 csn cxp cB c0 csn csn cxp cun cC c0 csn cxp
      cD c0 csn csn cxp cun wceq cB cD wceq cA cC c0 csn xpeq1 cB cD c0 csn csn
      xpeq1 cA c0 csn cxp cC c0 csn cxp cB c0 csn csn cxp cD c0 csn csn cxp
      uneq12 syl2an impbii $.
  $}

  ${
    brel.1 $e |- R C_ ( C X. D ) $.
    $( Two things in a binary relation belong to the relation's domain.
       (Contributed by NM, 17-May-1996.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    brel $p |- ( A R B -> ( A e. C /\ B e. D ) ) $=
      cA cB cR wbr cA cB cC cD cxp wbr cA cC wcel cB cD wcel wa cR cC cD cxp cA
      cB brel.1 ssbri cA cB cC cD brxp sylib $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y ps $.
    brab2a.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    brab2a.2 $e |- R = { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } $.
    $( Ordered pair membership in an ordered pair class abstraction.
       (Contributed by Mario Carneiro, 9-Nov-2015.) $)
    brab2a $p |- ( A R B <-> ( ( A e. C /\ B e. D ) /\ ps ) ) $=
      cA cB cR wbr cA cC wcel cB cD wcel wa wps cA cB cC cD cR vx cv cC wcel vy
      cv cD wcel wa wph wa vx vy copab vx cv cC wcel vy cv cD wcel wa vx vy
      copab cR cC cD cxp vx cv cC wcel vy cv cD wcel wa wph wa vx cv cC wcel vy
      cv cD wcel wa vx vy vx cv cC wcel vy cv cD wcel wa wph simpl ssopab2i
      brab2a.2 vx vy cC cD df-xp 3sstr4i brel cA cB cR wbr cA cB cop vx cv cC
      wcel vy cv cD wcel wa wph wa vx vy copab wcel cA cC wcel cB cD wcel wa
      wps cA cB cR wbr cA cB cop cR wcel cA cB cop vx cv cC wcel vy cv cD wcel
      wa wph wa vx vy copab wcel cA cB cR df-br cR vx cv cC wcel vy cv cD wcel
      wa wph wa vx vy copab cA cB cop brab2a.2 eleq2i bitri wph wps vx vy cA cB
      cC cD brab2a.1 opelopab2a syl5bb biadan2 $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Membership in a cross product.  (Contributed by NM, 5-Mar-1995.) $)
    elxp3 $p |- ( A e. ( B X. C ) <->
            E. x E. y ( <. x , y >. = A /\ <. x , y >. e. ( B X. C ) ) ) $=
      cA cB cC cxp wcel cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa
      wa vy wex vx wex vx cv vy cv cop cA wceq vx cv vy cv cop cB cC cxp wcel
      wa vy wex vx wex vx vy cA cB cC elxp vx cv vy cv cop cA wceq vx cv vy cv
      cop cB cC cxp wcel wa cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel
      wa wa vx vy vx cv vy cv cop cA wceq cA vx cv vy cv cop wceq vx cv vy cv
      cop cB cC cxp wcel vx cv cB wcel vy cv cC wcel wa vx cv vy cv cop cA
      eqcom vx cv vy cv cB cC opelxp anbi12i 2exbii bitr4i $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z C $.  $d x y z $.
    $( Membership in a union of cross products.  (Contributed by Mario
       Carneiro, 29-Dec-2014.)  (Revised by Mario Carneiro, 1-Jan-2017.) $)
    opeliunxp $p |- ( <. x , C >. e. U_ x e. A ( { x } X. B ) <->
                     ( x e. A /\ C e. B ) ) $=
      vx cv cC cop vx cA vx cv csn cB cxp ciun wcel vx cv cC cop vy cv vx cv
      csn cB cxp wcel vx cA wrex vy cab wcel vx cv cA wcel vx vz wsb vx cv cC
      cop vz cv csn vx vz cv cB csb cxp wcel wa vz wex vx cv cA wcel cC cB wcel
      wa vx cA vx cv csn cB cxp ciun vy cv vx cv csn cB cxp wcel vx cA wrex vy
      cab vx cv cC cop vx vy cA vx cv csn cB cxp df-iun eleq2i vy cv vx cv csn
      cB cxp wcel vx cA wrex vx cv cA wcel vx vz wsb vx cv cC cop vz cv csn vx
      vz cv cB csb cxp wcel wa vz wex vy vx cv cC cop vx cv cC opex vy cv vx cv
      csn cB cxp wcel vx cA wrex vx cv cA wcel vx vz wsb vy cv vz cv csn vx vz
      cv cB csb cxp wcel wa vz wex vy cv vx cv cC cop wceq vx cv cA wcel vx vz
      wsb vx cv cC cop vz cv csn vx vz cv cB csb cxp wcel wa vz wex vy cv vx cv
      csn cB cxp wcel vx cA wrex vx cv cA wcel vy cv vx cv csn cB cxp wcel wa
      vx wex vx cv cA wcel vx vz wsb vy cv vz cv csn vx vz cv cB csb cxp wcel
      wa vz wex vy cv vx cv csn cB cxp wcel vx cA df-rex vx cv cA wcel vy cv vx
      cv csn cB cxp wcel wa vx cv cA wcel vx vz wsb vy cv vz cv csn vx vz cv cB
      csb cxp wcel wa vx vz vx cv cA wcel vy cv vx cv csn cB cxp wcel wa vz nfv
      vx cv cA wcel vx vz wsb vy cv vz cv csn vx vz cv cB csb cxp wcel vx vx cv
      cA wcel vx vz nfs1v vx vy vz cv csn vx vz cv cB csb cxp vx vz cv csn vx
      vz cv cB csb vx vz cv csn nfcv vx vz cv cB nfcsb1v nfxp nfcri nfan vx cv
      vz cv wceq vx cv cA wcel vx cv cA wcel vx vz wsb vy cv vx cv csn cB cxp
      wcel vy cv vz cv csn vx vz cv cB csb cxp wcel vx cv cA wcel vx vz sbequ12
      vx cv vz cv wceq vx cv csn cB cxp vz cv csn vx vz cv cB csb cxp vy cv vx
      cv vz cv wceq vx cv csn vz cv csn cB vx vz cv cB csb vx cv vz cv sneq vx
      vz cv cB csbeq1a xpeq12d eleq2d anbi12d cbvex bitri vy cv vx cv cC cop
      wceq vx cv cA wcel vx vz wsb vy cv vz cv csn vx vz cv cB csb cxp wcel wa
      vx cv cA wcel vx vz wsb vx cv cC cop vz cv csn vx vz cv cB csb cxp wcel
      wa vz vy cv vx cv cC cop wceq vy cv vz cv csn vx vz cv cB csb cxp wcel vx
      cv cC cop vz cv csn vx vz cv cB csb cxp wcel vx cv cA wcel vx vz wsb vy
      cv vx cv cC cop vz cv csn vx vz cv cB csb cxp eleq1 anbi2d exbidv syl5bb
      elab vx cv cA wcel vx vz wsb vx cv cC cop vz cv csn vx vz cv cB csb cxp
      wcel wa vz wex vz cv vx cv wceq vx cv cA wcel vx vz wsb cC vx vz cv cB
      csb wcel wa wa vz wex vx cv cA wcel cC cB wcel wa vx cv cA wcel vx vz wsb
      vx cv cC cop vz cv csn vx vz cv cB csb cxp wcel wa vz cv vx cv wceq vx cv
      cA wcel vx vz wsb cC vx vz cv cB csb wcel wa wa vz vx cv cA wcel vx vz
      wsb vx cv cC cop vz cv csn vx vz cv cB csb cxp wcel wa vx cv cA wcel vx
      vz wsb vx cv vz cv csn wcel cC vx vz cv cB csb wcel wa wa vx cv vz cv csn
      wcel vx cv cA wcel vx vz wsb cC vx vz cv cB csb wcel wa wa vz cv vx cv
      wceq vx cv cA wcel vx vz wsb cC vx vz cv cB csb wcel wa wa vx cv cC cop
      vz cv csn vx vz cv cB csb cxp wcel vx cv vz cv csn wcel cC vx vz cv cB
      csb wcel wa vx cv cA wcel vx vz wsb vx cv cC vz cv csn vx vz cv cB csb
      opelxp anbi2i vx cv cA wcel vx vz wsb vx cv vz cv csn wcel cC vx vz cv cB
      csb wcel an12 vx cv vz cv csn wcel vz cv vx cv wceq vx cv cA wcel vx vz
      wsb cC vx vz cv cB csb wcel wa vx cv vz cv csn wcel vx cv vz cv wceq vz
      cv vx cv wceq vx vz cv elsn vx cv vz cv eqcom bitri anbi1i 3bitri exbii
      vx cv cA wcel vx vz wsb cC vx vz cv cB csb wcel wa vx cv cA wcel cC cB
      wcel wa vz vx cv vx vex vz cv vx cv wceq vx cv cA wcel vx vz wsb vx cv cA
      wcel cC vx vz cv cB csb wcel cC cB wcel vx cv cA wcel vz vx sbequ12r vz
      cv vx cv wceq vx vz cv cB csb cB cC vz cv vx cv wceq cB vx vz cv cB csb
      cB vx vz cv cB csb wceq vx cv vz cv vx vz cv cB csbeq1a eqcoms eqcomd
      eleq2d anbi12d ceqsexv bitri 3bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Distributive law for cross product over union.  Theorem 103 of [Suppes]
       p. 52.  (Contributed by NM, 12-Aug-2004.) $)
    xpundi $p |- ( A X. ( B u. C ) ) = ( ( A X. B ) u. ( A X. C ) ) $=
      cA cB cC cun cxp vx cv cA wcel vy cv cB cC cun wcel wa vx vy copab cA cB
      cxp cA cC cxp cun vx vy cA cB cC cun df-xp cA cB cxp cA cC cxp cun vx cv
      cA wcel vy cv cB wcel wa vx vy copab vx cv cA wcel vy cv cC wcel wa vx vy
      copab cun vx cv cA wcel vy cv cB cC cun wcel wa vx vy copab cA cB cxp vx
      cv cA wcel vy cv cB wcel wa vx vy copab cA cC cxp vx cv cA wcel vy cv cC
      wcel wa vx vy copab vx vy cA cB df-xp vx vy cA cC df-xp uneq12i vx cv cA
      wcel vy cv cB cC cun wcel wa vx vy copab vx cv cA wcel vy cv cB wcel wa
      vx cv cA wcel vy cv cC wcel wa wo vx vy copab vx cv cA wcel vy cv cB wcel
      wa vx vy copab vx cv cA wcel vy cv cC wcel wa vx vy copab cun vx cv cA
      wcel vy cv cB cC cun wcel wa vx cv cA wcel vy cv cB wcel wa vx cv cA wcel
      vy cv cC wcel wa wo vx vy vx cv cA wcel vy cv cB cC cun wcel wa vx cv cA
      wcel vy cv cB wcel vy cv cC wcel wo wa vx cv cA wcel vy cv cB wcel wa vx
      cv cA wcel vy cv cC wcel wa wo vy cv cB cC cun wcel vy cv cB wcel vy cv
      cC wcel wo vx cv cA wcel vy cv cB cC elun anbi2i vx cv cA wcel vy cv cB
      wcel vy cv cC wcel andi bitri opabbii vx cv cA wcel vy cv cB wcel wa vx
      cv cA wcel vy cv cC wcel wa vx vy unopab eqtr4i eqtr4i eqtr4i $.

    $( Distributive law for cross product over union.  Similar to Theorem 103
       of [Suppes] p. 52.  (Contributed by NM, 30-Sep-2002.) $)
    xpundir $p |- ( ( A u. B ) X. C ) = ( ( A X. C ) u. ( B X. C ) ) $=
      cA cB cun cC cxp vx cv cA cB cun wcel vy cv cC wcel wa vx vy copab cA cC
      cxp cB cC cxp cun vx vy cA cB cun cC df-xp cA cC cxp cB cC cxp cun vx cv
      cA wcel vy cv cC wcel wa vx vy copab vx cv cB wcel vy cv cC wcel wa vx vy
      copab cun vx cv cA cB cun wcel vy cv cC wcel wa vx vy copab cA cC cxp vx
      cv cA wcel vy cv cC wcel wa vx vy copab cB cC cxp vx cv cB wcel vy cv cC
      wcel wa vx vy copab vx vy cA cC df-xp vx vy cB cC df-xp uneq12i vx cv cA
      cB cun wcel vy cv cC wcel wa vx vy copab vx cv cA wcel vy cv cC wcel wa
      vx cv cB wcel vy cv cC wcel wa wo vx vy copab vx cv cA wcel vy cv cC wcel
      wa vx vy copab vx cv cB wcel vy cv cC wcel wa vx vy copab cun vx cv cA cB
      cun wcel vy cv cC wcel wa vx cv cA wcel vy cv cC wcel wa vx cv cB wcel vy
      cv cC wcel wa wo vx vy vx cv cA cB cun wcel vy cv cC wcel wa vx cv cA
      wcel vx cv cB wcel wo vy cv cC wcel wa vx cv cA wcel vy cv cC wcel wa vx
      cv cB wcel vy cv cC wcel wa wo vx cv cA cB cun wcel vx cv cA wcel vx cv
      cB wcel wo vy cv cC wcel vx cv cA cB elun anbi1i vx cv cA wcel vx cv cB
      wcel vy cv cC wcel andir bitri opabbii vx cv cA wcel vy cv cC wcel wa vx
      cv cB wcel vy cv cC wcel wa vx vy unopab eqtr4i eqtr4i eqtr4i $.
  $}

  ${
    $d w y z A $.  $d w y z B $.  $d w x y z C $.  $d x F $.
    $( Distributive law for cross product over indexed union.  (Contributed by
       Mario Carneiro, 27-Apr-2014.) $)
    xpiundi $p |- ( C X. U_ x e. A B ) = U_ x e. A ( C X. B ) $=
      vz cC vx cA cB ciun cxp vx cA cC cB cxp ciun vz cv vw cv vy cv cop wceq
      vy vx cA cB ciun wrex vw cC wrex vz cv cC cB cxp wcel vx cA wrex vz cv cC
      vx cA cB ciun cxp wcel vz cv vx cA cC cB cxp ciun wcel vz cv vw cv vy cv
      cop wceq vy cB wrex vx cA wrex vw cC wrex vz cv vw cv vy cv cop wceq vy
      cB wrex vw cC wrex vx cA wrex vz cv vw cv vy cv cop wceq vy vx cA cB ciun
      wrex vw cC wrex vz cv cC cB cxp wcel vx cA wrex vz cv vw cv vy cv cop
      wceq vy cB wrex vw vx cC cA rexcom vz cv vw cv vy cv cop wceq vy vx cA cB
      ciun wrex vz cv vw cv vy cv cop wceq vy cB wrex vx cA wrex vw cC vy cv vx
      cA cB ciun wcel vz cv vw cv vy cv cop wceq wa vy wex vy cv cB wcel vx cA
      wrex vz cv vw cv vy cv cop wceq wa vy wex vz cv vw cv vy cv cop wceq vy
      vx cA cB ciun wrex vz cv vw cv vy cv cop wceq vy cB wrex vx cA wrex vy cv
      vx cA cB ciun wcel vz cv vw cv vy cv cop wceq wa vy cv cB wcel vx cA wrex
      vz cv vw cv vy cv cop wceq wa vy vy cv vx cA cB ciun wcel vy cv cB wcel
      vx cA wrex vz cv vw cv vy cv cop wceq vx vy cv cA cB eliun anbi1i exbii
      vz cv vw cv vy cv cop wceq vy vx cA cB ciun df-rex vz cv vw cv vy cv cop
      wceq vy cB wrex vx cA wrex vy cv cB wcel vz cv vw cv vy cv cop wceq wa vy
      wex vx cA wrex vy cv cB wcel vz cv vw cv vy cv cop wceq wa vx cA wrex vy
      wex vy cv cB wcel vx cA wrex vz cv vw cv vy cv cop wceq wa vy wex vz cv
      vw cv vy cv cop wceq vy cB wrex vy cv cB wcel vz cv vw cv vy cv cop wceq
      wa vy wex vx cA vz cv vw cv vy cv cop wceq vy cB df-rex rexbii vy cv cB
      wcel vz cv vw cv vy cv cop wceq wa vx vy cA rexcom4 vy cv cB wcel vz cv
      vw cv vy cv cop wceq wa vx cA wrex vy cv cB wcel vx cA wrex vz cv vw cv
      vy cv cop wceq wa vy vy cv cB wcel vz cv vw cv vy cv cop wceq vx cA
      r19.41v exbii 3bitri 3bitr4i rexbii vz cv cC cB cxp wcel vz cv vw cv vy
      cv cop wceq vy cB wrex vw cC wrex vx cA vw vy vz cv cC cB elxp2 rexbii
      3bitr4i vw vy vz cv cC vx cA cB ciun elxp2 vx vz cv cA cC cB cxp eliun
      3bitr4i eqriv $.

    $( Distributive law for cross product over indexed union.  (Contributed by
       Mario Carneiro, 27-Apr-2014.) $)
    xpiundir $p |- ( U_ x e. A B X. C ) = U_ x e. A ( B X. C ) $=
      vz vx cA cB ciun cC cxp vx cA cB cC cxp ciun vz cv vy cv vw cv cop wceq
      vw cC wrex vy vx cA cB ciun wrex vz cv cB cC cxp wcel vx cA wrex vz cv vx
      cA cB ciun cC cxp wcel vz cv vx cA cB cC cxp ciun wcel vy cv vx cA cB
      ciun wcel vz cv vy cv vw cv cop wceq vw cC wrex wa vy wex vz cv vy cv vw
      cv cop wceq vw cC wrex vy cB wrex vx cA wrex vz cv vy cv vw cv cop wceq
      vw cC wrex vy vx cA cB ciun wrex vz cv cB cC cxp wcel vx cA wrex vy cv cB
      wcel vz cv vy cv vw cv cop wceq vw cC wrex wa vy wex vx cA wrex vy cv cB
      wcel vz cv vy cv vw cv cop wceq vw cC wrex wa vx cA wrex vy wex vz cv vy
      cv vw cv cop wceq vw cC wrex vy cB wrex vx cA wrex vy cv vx cA cB ciun
      wcel vz cv vy cv vw cv cop wceq vw cC wrex wa vy wex vy cv cB wcel vz cv
      vy cv vw cv cop wceq vw cC wrex wa vx vy cA rexcom4 vz cv vy cv vw cv cop
      wceq vw cC wrex vy cB wrex vy cv cB wcel vz cv vy cv vw cv cop wceq vw cC
      wrex wa vy wex vx cA vz cv vy cv vw cv cop wceq vw cC wrex vy cB df-rex
      rexbii vy cv vx cA cB ciun wcel vz cv vy cv vw cv cop wceq vw cC wrex wa
      vy cv cB wcel vz cv vy cv vw cv cop wceq vw cC wrex wa vx cA wrex vy vy
      cv vx cA cB ciun wcel vz cv vy cv vw cv cop wceq vw cC wrex wa vy cv cB
      wcel vx cA wrex vz cv vy cv vw cv cop wceq vw cC wrex wa vy cv cB wcel vz
      cv vy cv vw cv cop wceq vw cC wrex wa vx cA wrex vy cv vx cA cB ciun wcel
      vy cv cB wcel vx cA wrex vz cv vy cv vw cv cop wceq vw cC wrex vx vy cv
      cA cB eliun anbi1i vy cv cB wcel vz cv vy cv vw cv cop wceq vw cC wrex vx
      cA r19.41v bitr4i exbii 3bitr4ri vz cv vy cv vw cv cop wceq vw cC wrex vy
      vx cA cB ciun df-rex vz cv cB cC cxp wcel vz cv vy cv vw cv cop wceq vw
      cC wrex vy cB wrex vx cA vy vw vz cv cB cC elxp2 rexbii 3bitr4i vy vw vz
      cv vx cA cB ciun cC elxp2 vx vz cv cA cB cC cxp eliun 3bitr4i eqriv $.

    $( Obsolete proof of ~ resiun2 as of 5-Apr-2016.  Distributive law for
       cross product over restriction.  (Contributed by Mario Carneiro,
       11-Nov-2014.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    resiundiOLD $p |- ( F |` U_ x e. A B ) = U_ x e. A ( F |` B ) $=
      cF vx cA cB ciun cvv cxp cin vx cA cF cB cvv cxp cin ciun cF vx cA cB
      ciun cres vx cA cF cB cres ciun cF vx cA cB ciun cvv cxp cin cF vx cA cB
      cvv cxp ciun cin vx cA cF cB cvv cxp cin ciun vx cA cB ciun cvv cxp vx cA
      cB cvv cxp ciun cF vx cA cB cvv xpiundir ineq2i vx cA cF cB cvv cxp
      iunin2 eqtr4i cF vx cA cB ciun df-res vx cA cF cB cres cF cB cvv cxp cin
      cF cB cres cF cB cvv cxp cin wceq vx cv cA wcel cF cB df-res a1i iuneq2i
      3eqtr4i $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Membership in a union of cross products when the second factor is
       constant.  (Contributed by Mario Carneiro, 29-Dec-2014.) $)
    iunxpconst $p |- U_ x e. A ( { x } X. B ) = ( A X. B ) $=
      vx cA vx cv csn ciun cB cxp vx cA vx cv csn cB cxp ciun cA cB cxp vx cA
      vx cv csn cB xpiundir vx cA vx cv csn ciun cA cB vx cA iunid xpeq1i
      eqtr3i $.
  $}

  $( The cross product of two unions.  (Contributed by NM, 12-Aug-2004.) $)
  xpun $p |- ( ( A u. B ) X. ( C u. D ) ) =
            ( ( ( A X. C ) u. ( A X. D ) ) u. ( ( B X. C ) u. ( B X. D ) ) ) $=
    cA cB cun cC cD cun cxp cA cB cun cC cxp cA cB cun cD cxp cun cA cC cxp cB
    cC cxp cun cA cD cxp cB cD cxp cun cun cA cC cxp cA cD cxp cun cB cC cxp cB
    cD cxp cun cun cA cB cun cC cD xpundi cA cB cun cC cxp cA cC cxp cB cC cxp
    cun cA cB cun cD cxp cA cD cxp cB cD cxp cun cA cB cC xpundir cA cB cD
    xpundir uneq12i cA cC cxp cB cC cxp cA cD cxp cB cD cxp un4 3eqtri $.

  ${
    $d w x y z A $.
    $( Membership in universal class of ordered pairs.  (Contributed by NM,
       4-Jul-1994.) $)
    elvv $p |- ( A e. ( _V X. _V ) <-> E. x E. y A = <. x , y >. ) $=
      cA cvv cvv cxp wcel cA vx cv vy cv cop wceq vx cv cvv wcel vy cv cvv wcel
      wa wa vy wex vx wex cA vx cv vy cv cop wceq vy wex vx wex vx vy cA cvv
      cvv elxp cA vx cv vy cv cop wceq cA vx cv vy cv cop wceq vx cv cvv wcel
      vy cv cvv wcel wa wa vx vy vx cv cvv wcel vy cv cvv wcel wa cA vx cv vy
      cv cop wceq vx cv cvv wcel vy cv cvv wcel vx vex vy vex pm3.2i biantru
      2exbii bitr4i $.

    $( Membership in universal class of ordered triples.  (Contributed by NM,
       17-Dec-2008.) $)
    elvvv $p |- ( A e. ( ( _V X. _V ) X. _V )
                 <-> E. x E. y E. z A = <. <. x , y >. , z >. ) $=
      cA cvv cvv cxp cvv cxp wcel cA vw cv vz cv cop wceq vw cv cvv cvv cxp
      wcel vz cv cvv wcel wa wa vz wex vw wex cA vx cv vy cv cop vz cv cop wceq
      vz wex vy wex vx wex vw vz cA cvv cvv cxp cvv elxp cA vw cv vz cv cop
      wceq vw cv cvv cvv cxp wcel vz cv cvv wcel wa wa vz wex vw wex vw cv vx
      cv vy cv cop wceq cA vw cv vz cv cop wceq wa vy wex vx wex vz wex vw wex
      cA vx cv vy cv cop vz cv cop wceq vz wex vy wex vx wex cA vw cv vz cv cop
      wceq vw cv cvv cvv cxp wcel vz cv cvv wcel wa wa vw cv vx cv vy cv cop
      wceq cA vw cv vz cv cop wceq wa vy wex vx wex vw vz cA vw cv vz cv cop
      wceq vw cv cvv cvv cxp wcel vz cv cvv wcel wa wa cA vw cv vz cv cop wceq
      vw cv cvv cvv cxp wcel wa vz cv cvv wcel wa vw cv vx cv vy cv cop wceq cA
      vw cv vz cv cop wceq wa vy wex vx wex cA vw cv vz cv cop wceq vw cv cvv
      cvv cxp wcel vz cv cvv wcel anass cA vw cv vz cv cop wceq vw cv vx cv vy
      cv cop wceq wa vy wex vx wex cA vw cv vz cv cop wceq vw cv vx cv vy cv
      cop wceq vy wex vx wex wa vw cv vx cv vy cv cop wceq cA vw cv vz cv cop
      wceq wa vy wex vx wex cA vw cv vz cv cop wceq vw cv cvv cvv cxp wcel wa
      vz cv cvv wcel wa cA vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq vx
      vy 19.42vv vw cv vx cv vy cv cop wceq cA vw cv vz cv cop wceq wa cA vw cv
      vz cv cop wceq vw cv vx cv vy cv cop wceq wa vx vy vw cv vx cv vy cv cop
      wceq cA vw cv vz cv cop wceq ancom 2exbii cA vw cv vz cv cop wceq vw cv
      cvv cvv cxp wcel wa vz cv cvv wcel wa cA vw cv vz cv cop wceq vw cv cvv
      cvv cxp wcel wa cA vw cv vz cv cop wceq vw cv vx cv vy cv cop wceq vy wex
      vx wex wa vz cv cvv wcel cA vw cv vz cv cop wceq vw cv cvv cvv cxp wcel
      wa vz vex biantru vw cv cvv cvv cxp wcel vw cv vx cv vy cv cop wceq vy
      wex vx wex cA vw cv vz cv cop wceq vx vy vw cv elvv anbi2i bitr3i
      3bitr4ri bitr3i 2exbii vw cv vx cv vy cv cop wceq cA vw cv vz cv cop wceq
      wa vy wex vx wex vz wex vw wex vw cv vx cv vy cv cop wceq cA vw cv vz cv
      cop wceq wa vz wex vw wex vy wex vx wex cA vx cv vy cv cop vz cv cop wceq
      vz wex vy wex vx wex vw cv vx cv vy cv cop wceq cA vw cv vz cv cop wceq
      wa vx vy vw vz exrot4 vw cv vx cv vy cv cop wceq cA vw cv vz cv cop wceq
      wa vz wex vw wex cA vx cv vy cv cop vz cv cop wceq vz wex vx vy vw cv vx
      cv vy cv cop wceq cA vw cv vz cv cop wceq wa vz wex vw wex vw cv vx cv vy
      cv cop wceq cA vw cv vz cv cop wceq wa vw wex vz wex cA vx cv vy cv cop
      vz cv cop wceq vz wex vw cv vx cv vy cv cop wceq cA vw cv vz cv cop wceq
      wa vw vz excom vw cv vx cv vy cv cop wceq cA vw cv vz cv cop wceq wa vw
      wex cA vx cv vy cv cop vz cv cop wceq vz cA vw cv vz cv cop wceq cA vx cv
      vy cv cop vz cv cop wceq vw vx cv vy cv cop vx cv vy cv opex vw cv vx cv
      vy cv cop wceq vw cv vz cv cop vx cv vy cv cop vz cv cop cA vw cv vx cv
      vy cv cop vz cv opeq1 eqeq2d ceqsexv exbii bitri 2exbii bitr3i bitri
      bitri $.

    $( An ordered pair contains its union.  (Contributed by NM,
       16-Sep-2006.) $)
    elvvuni $p |- ( A e. ( _V X. _V ) -> U. A e. A ) $=
      cA cvv cvv cxp wcel cA vx cv vy cv cop wceq vy wex vx wex cA cuni cA wcel
      vx vy cA elvv cA vx cv vy cv cop wceq cA cuni cA wcel vx vy cA vx cv vy
      cv cop wceq cA cuni cA wcel vx cv vy cv cop cuni vx cv vy cv cop wcel vx
      cv vy cv cop cuni vx cv vy cv cpr vx cv vy cv cop vx cv vy cv vx vex vy
      vex uniop vx cv vy cv vx vex vy vex opi2 eqeltri cA vx cv vy cv cop wceq
      cA cuni vx cv vy cv cop cuni cA vx cv vy cv cop cA vx cv vy cv cop unieq
      cA vx cv vy cv cop wceq id eleq12d mpbiri exlimivv sylbi $.
  $}

  $( Intersection of binary relation with cross product.  (Contributed by NM,
     3-Mar-2007.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
  brinxp2 $p |- ( A ( R i^i ( C X. D ) ) B <->
                ( A e. C /\ B e. D /\ A R B ) ) $=
    cA cB cR cC cD cxp cin wbr cA cB cR wbr cA cB cC cD cxp wbr wa cA cB cC cD
    cxp wbr cA cB cR wbr wa cA cC wcel cB cD wcel cA cB cR wbr w3a cA cB cR cC
    cD cxp brin cA cB cR wbr cA cB cC cD cxp wbr ancom cA cB cC cD cxp wbr cA
    cB cR wbr wa cA cC wcel cB cD wcel wa cA cB cR wbr wa cA cC wcel cB cD wcel
    cA cB cR wbr w3a cA cB cC cD cxp wbr cA cC wcel cB cD wcel wa cA cB cR wbr
    cA cB cC cD brxp anbi1i cA cC wcel cB cD wcel cA cB cR wbr df-3an bitr4i
    3bitri $.

  $( Intersection of binary relation with cross product.  (Contributed by NM,
     9-Mar-1997.) $)
  brinxp $p |- ( ( A e. C /\ B e. D ) ->
               ( A R B <-> A ( R i^i ( C X. D ) ) B ) ) $=
    cA cB cR cC cD cxp cin wbr cA cC wcel cB cD wcel wa cA cB cR wbr cA cB cR
    cC cD cxp cin wbr cA cC wcel cB cD wcel cA cB cR wbr w3a cA cC wcel cB cD
    wcel wa cA cB cR wbr wa cA cB cC cD cR brinxp2 cA cC wcel cB cD wcel cA cB
    cR wbr df-3an bitri baibr $.

  ${
    $d x y z A $.  $d x y z R $.
    $( Intersection of partial order with cross product of its field.
       (Contributed by Mario Carneiro, 10-Jul-2014.) $)
    poinxp $p |- ( R Po A <-> ( R i^i ( A X. A ) ) Po A ) $=
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa vz cA wral vy cA wral vx cA wral vx cv vx cv cR cA cA cxp
      cin wbr wn vx cv vy cv cR cA cA cxp cin wbr vy cv vz cv cR cA cA cxp cin
      wbr wa vx cv vz cv cR cA cA cxp cin wbr wi wa vz cA wral vy cA wral vx cA
      wral cA cR wpo cA cR cA cA cxp cin wpo vx cv vx cv cR wbr wn vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vy cA
      wral vx cv vx cv cR cA cA cxp cin wbr wn vx cv vy cv cR cA cA cxp cin wbr
      vy cv vz cv cR cA cA cxp cin wbr wa vx cv vz cv cR cA cA cxp cin wbr wi
      wa vz cA wral vy cA wral vx cA vx cv cA wcel vx cv vx cv cR wbr wn vx cv
      vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vx
      cv vx cv cR cA cA cxp cin wbr wn vx cv vy cv cR cA cA cxp cin wbr vy cv
      vz cv cR cA cA cxp cin wbr wa vx cv vz cv cR cA cA cxp cin wbr wi wa vz
      cA wral vy cA vx cv cA wcel vy cv cA wcel wa vx cv vx cv cR wbr wn vx cv
      vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vx cv vx cv
      cR cA cA cxp cin wbr wn vx cv vy cv cR cA cA cxp cin wbr vy cv vz cv cR
      cA cA cxp cin wbr wa vx cv vz cv cR cA cA cxp cin wbr wi wa vz cA vx cv
      cA wcel vy cv cA wcel wa vz cv cA wcel wa vx cv vx cv cR wbr wn vx cv vx
      cv cR cA cA cxp cin wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv
      vz cv cR wbr wi vx cv vy cv cR cA cA cxp cin wbr vy cv vz cv cR cA cA cxp
      cin wbr wa vx cv vz cv cR cA cA cxp cin wbr wi vx cv cA wcel vy cv cA
      wcel wa vz cv cA wcel wa vx cv vx cv cR wbr vx cv vx cv cR cA cA cxp cin
      wbr vx cv cA wcel vy cv cA wcel wa vz cv cA wcel wa vx cv cA wcel vx cv
      cA wcel vx cv vx cv cR wbr vx cv vx cv cR cA cA cxp cin wbr wb vx cv cA
      wcel vy cv cA wcel vz cv cA wcel simpll vx cv cA wcel vy cv cA wcel vz cv
      cA wcel simpll vx cv vx cv cA cA cR brinxp syl2anc notbid vx cv cA wcel
      vy cv cA wcel wa vz cv cA wcel wa vx cv vy cv cR wbr vy cv vz cv cR wbr
      wa vx cv vy cv cR cA cA cxp cin wbr vy cv vz cv cR cA cA cxp cin wbr wa
      vx cv vz cv cR wbr vx cv vz cv cR cA cA cxp cin wbr vx cv cA wcel vy cv
      cA wcel wa vz cv cA wcel wa vx cv vy cv cR wbr vx cv vy cv cR cA cA cxp
      cin wbr vy cv vz cv cR wbr vy cv vz cv cR cA cA cxp cin wbr vx cv cA wcel
      vy cv cA wcel wa vx cv vy cv cR wbr vx cv vy cv cR cA cA cxp cin wbr wb
      vz cv cA wcel vx cv vy cv cA cA cR brinxp adantr vy cv cA wcel vz cv cA
      wcel vy cv vz cv cR wbr vy cv vz cv cR cA cA cxp cin wbr wb vx cv cA wcel
      vy cv vz cv cA cA cR brinxp adantll anbi12d vx cv cA wcel vz cv cA wcel
      vx cv vz cv cR wbr vx cv vz cv cR cA cA cxp cin wbr wb vy cv cA wcel vx
      cv vz cv cA cA cR brinxp adantlr imbi12d anbi12d ralbidva ralbidva
      ralbiia vx vy vz cA cR df-po vx vy vz cA cR cA cA cxp cin df-po 3bitr4i
      $.

    $( Intersection of total order with cross product of its field.
       (Contributed by Mario Carneiro, 10-Jul-2014.) $)
    soinxp $p |- ( R Or A <-> ( R i^i ( A X. A ) ) Or A ) $=
      cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy
      cA wral vx cA wral wa cA cR cA cA cxp cin wpo vx cv vy cv cR cA cA cxp
      cin wbr vx cv vy cv wceq vy cv vx cv cR cA cA cxp cin wbr w3o vy cA wral
      vx cA wral wa cA cR wor cA cR cA cA cxp cin wor cA cR wpo cA cR cA cA cxp
      cin wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA
      wral vx cA wral vx cv vy cv cR cA cA cxp cin wbr vx cv vy cv wceq vy cv
      vx cv cR cA cA cxp cin wbr w3o vy cA wral vx cA wral cA cR poinxp vx cv
      vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx cv vy
      cv cR cA cA cxp cin wbr vx cv vy cv wceq vy cv vx cv cR cA cA cxp cin wbr
      w3o vy cA wral vx cA vx cv cA wcel vx cv vy cv cR wbr vx cv vy cv wceq vy
      cv vx cv cR wbr w3o vx cv vy cv cR cA cA cxp cin wbr vx cv vy cv wceq vy
      cv vx cv cR cA cA cxp cin wbr w3o vy cA vx cv cA wcel vy cv cA wcel wa vx
      cv vy cv cR wbr vx cv vy cv cR cA cA cxp cin wbr vx cv vy cv wceq vx cv
      vy cv wceq vy cv vx cv cR wbr vy cv vx cv cR cA cA cxp cin wbr vx cv vy
      cv cA cA cR brinxp vx cv cA wcel vy cv cA wcel wa vx cv vy cv wceq biidd
      vy cv cA wcel vx cv cA wcel vy cv vx cv cR wbr vy cv vx cv cR cA cA cxp
      cin wbr wb vy cv vx cv cA cA cR brinxp ancoms 3orbi123d ralbidva ralbiia
      anbi12i vx vy cA cR df-so vx vy cA cR cA cA cxp cin df-so 3bitr4i $.

    $( Intersection of well-founded relation with cross product of its field.
       (Contributed by Mario Carneiro, 10-Jul-2014.) $)
    frinxp $p |- ( R Fr A <-> ( R i^i ( A X. A ) ) Fr A ) $=
      vz cv cA wss vz cv c0 wne wa vy cv vx cv cR wbr wn vy vz cv wral vx vz cv
      wrex wi vz wal vz cv cA wss vz cv c0 wne wa vy cv vx cv cR cA cA cxp cin
      wbr wn vy vz cv wral vx vz cv wrex wi vz wal cA cR wfr cA cR cA cA cxp
      cin wfr vz cv cA wss vz cv c0 wne wa vy cv vx cv cR wbr wn vy vz cv wral
      vx vz cv wrex wi vz cv cA wss vz cv c0 wne wa vy cv vx cv cR cA cA cxp
      cin wbr wn vy vz cv wral vx vz cv wrex wi vz vz cv cA wss vz cv c0 wne wa
      vy cv vx cv cR wbr wn vy vz cv wral vx vz cv wrex vy cv vx cv cR cA cA
      cxp cin wbr wn vy vz cv wral vx vz cv wrex vz cv cA wss vy cv vx cv cR
      wbr wn vy vz cv wral vx vz cv wrex vy cv vx cv cR cA cA cxp cin wbr wn vy
      vz cv wral vx vz cv wrex wb vz cv c0 wne vz cv cA wss vy cv vx cv cR wbr
      wn vy vz cv wral vy cv vx cv cR cA cA cxp cin wbr wn vy vz cv wral vx vz
      cv vz cv cA wss vx cv vz cv wcel wa vy cv vx cv cR wbr wn vy cv vx cv cR
      cA cA cxp cin wbr wn vy vz cv vz cv cA wss vx cv vz cv wcel wa vy cv vz
      cv wcel wa vy cv vx cv cR wbr vy cv vx cv cR cA cA cxp cin wbr vz cv cA
      wss vx cv vz cv wcel vy cv vz cv wcel vy cv vx cv cR wbr vy cv vx cv cR
      cA cA cxp cin wbr wb vz cv cA wss vx cv vz cv wcel vy cv vz cv wcel wa vx
      cv cA wcel vy cv cA wcel wa vy cv vx cv cR wbr vy cv vx cv cR cA cA cxp
      cin wbr wb vz cv cA wss vx cv vz cv wcel vx cv cA wcel vy cv vz cv wcel
      vy cv cA wcel vz cv cA vx cv ssel vz cv cA vy cv ssel anim12d vy cv cA
      wcel vx cv cA wcel vy cv vx cv cR wbr vy cv vx cv cR cA cA cxp cin wbr wb
      vy cv vx cv cA cA cR brinxp ancoms syl6 impl notbid ralbidva rexbidva
      adantr pm5.74i albii vz vx vy cA cR df-fr vz vx vy cA cR cA cA cxp cin
      df-fr 3bitr4i $.

    $( Intersection of set-like relation with cross product of its field.
       (Contributed by Mario Carneiro, 22-Jun-2015.) $)
    seinxp $p |- ( R Se A <-> ( R i^i ( A X. A ) ) Se A ) $=
      vy cv vx cv cR wbr vy cA crab cvv wcel vx cA wral vy cv vx cv cR cA cA
      cxp cin wbr vy cA crab cvv wcel vx cA wral cA cR wse cA cR cA cA cxp cin
      wse vy cv vx cv cR wbr vy cA crab cvv wcel vy cv vx cv cR cA cA cxp cin
      wbr vy cA crab cvv wcel vx cA vx cv cA wcel vy cv vx cv cR wbr vy cA crab
      vy cv vx cv cR cA cA cxp cin wbr vy cA crab cvv vx cv cA wcel vy cv vx cv
      cR wbr vy cv vx cv cR cA cA cxp cin wbr vy cA vy cv cA wcel vx cv cA wcel
      vy cv vx cv cR wbr vy cv vx cv cR cA cA cxp cin wbr wb vy cv vx cv cA cA
      cR brinxp ancoms rabbidva eleq1d ralbiia vx vy cA cR df-se vx vy cA cR cA
      cA cxp cin df-se 3bitr4i $.

    $( Intersection of well-ordering with cross product of its field.
       (Contributed by NM, 9-Mar-1997.)  (Revised by Mario Carneiro,
       10-Jul-2014.) $)
    weinxp $p |- ( R We A <-> ( R i^i ( A X. A ) ) We A ) $=
      cA cR wfr cA cR wor wa cA cR cA cA cxp cin wfr cA cR cA cA cxp cin wor wa
      cA cR wwe cA cR cA cA cxp cin wwe cA cR wfr cA cR cA cA cxp cin wfr cA cR
      wor cA cR cA cA cxp cin wor cA cR frinxp cA cR soinxp anbi12i cA cR df-we
      cA cR cA cA cxp cin df-we 3bitr4i $.
  $}

  ${
    $d x y z A $.  $d x y z R $.
    $( Partial ordering of a singleton.  (Contributed by NM, 27-Apr-2009.)
       (Revised by Mario Carneiro, 23-Apr-2015.) $)
    posn $p |- ( Rel R -> ( R Po { A } <-> -. A R A ) ) $=
      cR wrel cA cvv wcel cA csn cR wpo cA cA cR wbr wn wb cA csn cR wpo vx cv
      vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi wa vz cA csn wral vy cA csn wral vx cA csn wral cR wrel cA cvv
      wcel wa cA cA cR wbr wn vx vy vz cA csn cR df-po cA cvv wcel vx cv vx cv
      cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi
      wa vz cA csn wral vy cA csn wral vx cA csn wral cA cA cR wbr wn wb cR
      wrel cA cvv wcel vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi wa vz cA csn wral vy cA csn wral vx cA csn
      wral vx cv vx cv cR wbr wn vx cA csn wral cA cA cR wbr wn cA cvv wcel vx
      cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv
      cR wbr wi wa vz cA csn wral vy cA csn wral vx cv vx cv cR wbr wn vx cA
      csn cA cvv wcel vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi wa vz cA csn wral vy cA csn wral vx cv vx cv
      cR wbr wn vx cv vy cv cR wbr vy cv cA cR wbr wa vx cv cA cR wbr wi wa vy
      cA csn wral vx cv vx cv cR wbr wn cA cvv wcel vx cv vx cv cR wbr wn vx cv
      vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA csn
      wral vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv cA cR wbr wa vx cv cA
      cR wbr wi wa vy cA csn vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz
      cv cR wbr wa vx cv vz cv cR wbr wi wa vx cv vx cv cR wbr wn vx cv vy cv
      cR wbr vy cv cA cR wbr wa vx cv cA cR wbr wi wa vz cA cvv vz cv cA wceq
      vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vx cv vy
      cv cR wbr vy cv cA cR wbr wa vx cv cA cR wbr wi vx cv vx cv cR wbr wn vz
      cv cA wceq vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vy cv cR wbr vy
      cv cA cR wbr wa vx cv vz cv cR wbr vx cv cA cR wbr vz cv cA wceq vy cv vz
      cv cR wbr vy cv cA cR wbr vx cv vy cv cR wbr vz cv cA vy cv cR breq2
      anbi2d vz cv cA vx cv cR breq2 imbi12d anbi2d ralsng ralbidv vx cv vx cv
      cR wbr wn vx cv vy cv cR wbr vy cv cA cR wbr wa vx cv cA cR wbr wi wa vx
      cv vx cv cR wbr wn vy cA cvv vy cv cA wceq vx cv vx cv cR wbr wn vx cv vx
      cv cR wbr wn vx cv vy cv cR wbr vy cv cA cR wbr wa vx cv cA cR wbr wi wa
      vy cv cA wceq vx cv vy cv cR wbr vy cv cA cR wbr wa vx cv cA cR wbr wi vx
      cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv cA cR wbr wa vx cv vy cv cR
      wbr vy cv cA wceq vx cv cA cR wbr vx cv vy cv cR wbr vy cv cA cR wbr
      simpl vy cv cA vx cv cR breq2 syl5ib biantrud bicomd ralsng bitrd ralbidv
      vx cv vx cv cR wbr wn cA cA cR wbr wn vx cA cvv vx cv cA wceq vx cv vx cv
      cR wbr cA cA cR wbr vx cv cA wceq vx cv vx cv cR wbr cA cA cR wbr wb vx
      cv cA vx cv cA cR breq12 anidms notbid ralsng bitrd adantl syl5bb cR wrel
      cA cvv wcel wn wa cA csn cR wpo cA cA cR wbr wn cA cvv wcel wn cA csn cR
      wpo cR wrel cA cvv wcel wn cA csn cR wpo c0 cR wpo cR po0 cA cvv wcel wn
      cA csn c0 wceq cA csn cR wpo c0 cR wpo wb cA snprc cA csn c0 cR poeq2
      sylbi mpbiri adantl cR wrel cA cA cR wbr cA cvv wcel cR wrel cA cA cR wbr
      cA cvv wcel cA cA cR brrelex ex con3and 2thd pm2.61dan $.

    $( Strict ordering on a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.) $)
    sosn $p |- ( Rel R -> ( R Or { A } <-> -. A R A ) ) $=
      cA csn cR wor cA csn cR wpo cR wrel cA cA cR wbr wn cA csn cR wor cA csn
      cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA
      csn wral vx cA csn wral vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv
      cR wbr w3o vx vy cA csn vx cv cA csn wcel vy cv cA csn wcel wa vx cv vy
      cv wceq vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vx cv
      cA csn wcel vy cv cA csn wcel vx cv cA vy cv vx cv cA elsni vy cv cA csn
      wcel vy cv cA vy cv cA elsni eqcomd sylan9eq vx cv vy cv wceq vx cv vy cv
      cR wbr vy cv vx cv cR wbr 3mix2 syl rgen2a vx vy cA csn cR df-so mpbiran2
      cA cR posn syl5bb $.

    $( Founded relation on a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    frsn $p |- ( Rel R -> ( R Fr { A } <-> -. A R A ) ) $=
      cR wrel cA cvv wcel cA csn cR wfr cA cA cR wbr wn wb cR wrel cA cvv wcel
      wa cA csn cR wfr vz cv vy cv cR wbr wn vz cA csn wral vy cA csn wrex cA
      cA cR wbr wn cA csn cR wfr vx cv cA csn wss vx cv c0 wne wa vz cv vy cv
      cR wbr wn vz vx cv wral vy vx cv wrex wi vx wal cR wrel cA cvv wcel wa vz
      cv vy cv cR wbr wn vz cA csn wral vy cA csn wrex vx vy vz cA csn cR df-fr
      cR wrel cA cvv wcel wa vx cv cA csn wss vx cv c0 wne wa vz cv vy cv cR
      wbr wn vz vx cv wral vy vx cv wrex wi vx wal vx cv cA csn wceq vz cv vy
      cv cR wbr wn vz vx cv wral vy vx cv wrex wi vx wal vz cv vy cv cR wbr wn
      vz cA csn wral vy cA csn wrex cR wrel cA cvv wcel wa vx cv cA csn wss vx
      cv c0 wne wa vz cv vy cv cR wbr wn vz vx cv wral vy vx cv wrex wi vx cv
      cA csn wceq vz cv vy cv cR wbr wn vz vx cv wral vy vx cv wrex wi vx cR
      wrel cA cvv wcel wa vx cv cA csn wss vx cv c0 wne wa vx cv cA csn wceq vz
      cv vy cv cR wbr wn vz vx cv wral vy vx cv wrex cR wrel cA cvv wcel wa vx
      cv cA csn wss vx cv c0 wne wa vx cv cA csn wceq cR wrel cA cvv wcel wa vx
      cv cA csn wss vx cv c0 wne vx cv cA csn wceq vx cv c0 wne vx cv c0 wceq
      wn cR wrel cA cvv wcel wa vx cv cA csn wss wa vx cv cA csn wceq vx cv c0
      df-ne cR wrel cA cvv wcel wa vx cv cA csn wss wa vx cv c0 wceq vx cv cA
      csn wceq cR wrel cA cvv wcel wa vx cv cA csn wss wa vx cv cA csn wss vx
      cv c0 wceq vx cv cA csn wceq wo cR wrel cA cvv wcel wa vx cv cA csn wss
      simpr vx cv cA sssn sylib ord syl5bi impr cR wrel cA cvv wcel wa vx cv cA
      csn wceq wa vx cv cA csn wss vx cv c0 wne vx cv cA csn wceq vx cv cA csn
      wss cR wrel cA cvv wcel wa vx cv cA csn eqimss adantl cR wrel cA cvv wcel
      wa vx cv cA csn wceq wa vx cv cA csn c0 cR wrel cA cvv wcel wa vx cv cA
      csn wceq simpr cA cvv wcel cA csn c0 wne cR wrel vx cv cA csn wceq cA cvv
      snnzg ad2antlr eqnetrd jca impbida imbi1d albidv vz cv vy cv cR wbr wn vz
      vx cv wral vy vx cv wrex vz cv vy cv cR wbr wn vz cA csn wral vy cA csn
      wrex vx cA csn cA snex vz cv vy cv cR wbr wn vz vx cv wral vz cv vy cv cR
      wbr wn vz cA csn wral vy vx cv cA csn vz cv vy cv cR wbr wn vz vx cv cA
      csn raleq rexeqbi1dv ceqsalv syl6bb syl5bb cA cvv wcel vz cv vy cv cR wbr
      wn vz cA csn wral vy cA csn wrex cA cA cR wbr wn wb cR wrel cA cvv wcel
      vz cv vy cv cR wbr wn vz cA csn wral vy cA csn wrex vz cv cA cR wbr wn vz
      cA csn wral cA cA cR wbr wn vz cv vy cv cR wbr wn vz cA csn wral vz cv cA
      cR wbr wn vz cA csn wral vy cA cvv vy cv cA wceq vz cv vy cv cR wbr wn vz
      cv cA cR wbr wn vz cA csn vy cv cA wceq vz cv vy cv cR wbr vz cv cA cR
      wbr vy cv cA vz cv cR breq2 notbid ralbidv rexsng vz cv cA cR wbr wn cA
      cA cR wbr wn vz cA cvv vz cv cA wceq vz cv cA cR wbr cA cA cR wbr vz cv
      cA cA cR breq1 notbid ralsng bitrd adantl bitrd cR wrel cA cvv wcel wn wa
      cA csn cR wfr cA cA cR wbr wn cA cvv wcel wn cA csn cR wfr cR wrel cA cvv
      wcel wn cA csn c0 wceq cA csn cR wfr cA snprc cA csn c0 wceq cA csn cR
      wfr c0 cR wfr cR fr0 cA csn c0 cR freq2 mpbiri sylbi adantl cR wrel cA cA
      cR wbr cA cvv wcel cR wrel cA cA cR wbr cA cvv wcel cA cA cR brrelex ex
      con3and 2thd pm2.61dan $.

    $( Well-ordering of a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.) $)
    wesn $p |- ( Rel R -> ( R We { A } <-> -. A R A ) ) $=
      cR wrel cA csn cR wfr cA csn cR wor wa cA cA cR wbr wn cA cA cR wbr wn wa
      cA csn cR wwe cA cA cR wbr wn cR wrel cA csn cR wfr cA cA cR wbr wn cA
      csn cR wor cA cA cR wbr wn cA cR frsn cA cR sosn anbi12d cA csn cR df-we
      cA cA cR wbr wn pm4.24 3bitr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( An abstraction relation is a subset of a related cross product.
       (Contributed by NM, 16-Jul-1995.) $)
    opabssxp $p |- { <. x , y >. | ( ( x e. A /\ y e. B ) /\ ph ) }
                   C_ ( A X. B ) $=
      vx cv cA wcel vy cv cB wcel wa wph wa vx vy copab vx cv cA wcel vy cv cB
      wcel wa vx vy copab cA cB cxp vx cv cA wcel vy cv cB wcel wa wph wa vx cv
      cA wcel vy cv cB wcel wa vx vy vx cv cA wcel vy cv cB wcel wa wph simpl
      ssopab2i vx vy cA cB df-xp sseqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d x y ps $.
    brab2ga.1 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    brab2ga.2 $e |- R = { <. x , y >. | ( ( x e. C /\ y e. D ) /\ ph ) } $.
    $( The law of concretion for a binary relation.  See ~ brab2a for alternate
       proof.  TODO: should one of them be deleted?  (Contributed by Mario
       Carneiro, 28-Apr-2015.)  (Proof modification is discouraged.) $)
    brab2ga $p |- ( A R B <-> ( ( A e. C /\ B e. D ) /\ ps ) ) $=
      cA cB cR wbr cA cC wcel cB cD wcel wa wps cA cB cC cD cR cR vx cv cC wcel
      vy cv cD wcel wa wph wa vx vy copab cC cD cxp brab2ga.2 wph vx vy cC cD
      opabssxp eqsstri brel cA cB cR wbr cA cB cop vx cv cC wcel vy cv cD wcel
      wa wph wa vx vy copab wcel cA cC wcel cB cD wcel wa wps cA cB cR wbr cA
      cB cop cR wcel cA cB cop vx cv cC wcel vy cv cD wcel wa wph wa vx vy
      copab wcel cA cB cR df-br cR vx cv cC wcel vy cv cD wcel wa wph wa vx vy
      copab cA cB cop brab2ga.2 eleq2i bitri wph wps vx vy cA cB cC cD
      brab2ga.1 opelopab2a syl5bb biadan2 $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y ps $.
    optocl.1 $e |- D = ( B X. C ) $.
    optocl.2 $e |- ( <. x , y >. = A -> ( ph <-> ps ) ) $.
    optocl.3 $e |- ( ( x e. B /\ y e. C ) -> ph ) $.
    $( Implicit substitution of class for ordered pair.  (Contributed by NM,
       5-Mar-1995.) $)
    optocl $p |- ( A e. D -> ps ) $=
      wps cA cB cC cxp cD cA cB cC cxp wcel vx cv vy cv cop cA wceq vx cv vy cv
      cop cB cC cxp wcel wa vy wex vx wex wps vx vy cA cB cC elxp3 vx cv vy cv
      cop cA wceq vx cv vy cv cop cB cC cxp wcel wa wps vx vy vx cv vy cv cop
      cA wceq vx cv vy cv cop cB cC cxp wcel wps vx cv vy cv cop cB cC cxp wcel
      wph vx cv vy cv cop cA wceq wps vx cv vy cv cop cB cC cxp wcel vx cv cB
      wcel vy cv cC wcel wa wph vx cv vy cv cB cC opelxp optocl.3 sylbi
      optocl.2 syl5ib imp exlimivv sylbi optocl.1 eleq2s $.
  $}

  ${
    $d x y z w A $.  $d z w B $.  $d x y z w C $.  $d x y z w D $.
    $d x y ps $.  $d z w ch $.  $d z w R $.
    2optocl.1 $e |- R = ( C X. D ) $.
    2optocl.2 $e |- ( <. x , y >. = A -> ( ph <-> ps ) ) $.
    2optocl.3 $e |- ( <. z , w >. = B -> ( ps <-> ch ) ) $.
    2optocl.4 $e |- ( ( ( x e. C /\ y e. D ) /\ ( z e. C /\ w e. D ) ) ->
                   ph ) $.
    $( Implicit substitution of classes for ordered pairs.  (Contributed by NM,
       12-Mar-1995.) $)
    2optocl $p |- ( ( A e. R /\ B e. R ) -> ch ) $=
      cB cR wcel cA cR wcel wch cA cR wcel wps wi cA cR wcel wch wi vz vw cB cC
      cD cR 2optocl.1 vz cv vw cv cop cB wceq wps wch cA cR wcel 2optocl.3
      imbi2d cA cR wcel vz cv cC wcel vw cv cD wcel wa wps vz cv cC wcel vw cv
      cD wcel wa wph wi vz cv cC wcel vw cv cD wcel wa wps wi vx vy cA cC cD cR
      2optocl.1 vx cv vy cv cop cA wceq wph wps vz cv cC wcel vw cv cD wcel wa
      2optocl.2 imbi2d vx cv cC wcel vy cv cD wcel wa vz cv cC wcel vw cv cD
      wcel wa wph 2optocl.4 ex optocl com12 optocl impcom $.
  $}

  ${
    $d x y z w v u A $.  $d z w v u B $.  $d v u C $.  $d x y z w v u D $.
    $d x y z w v u F $.  $d z w v u R $.  $d x y ps $.  $d z w ch $.
    $d v u th $.
    3optocl.1 $e |- R = ( D X. F ) $.
    3optocl.2 $e |- ( <. x , y >. = A -> ( ph <-> ps ) ) $.
    3optocl.3 $e |- ( <. z , w >. = B -> ( ps <-> ch ) ) $.
    3optocl.4 $e |- ( <. v , u >. = C -> ( ch <-> th ) ) $.
    3optocl.5 $e |- ( ( ( x e. D /\ y e. F ) /\ ( z e. D /\ w e. F )
                    /\ ( v e. D /\ u e. F ) ) -> ph ) $.
    $( Implicit substitution of classes for ordered pairs.  (Contributed by NM,
       12-Mar-1995.) $)
    3optocl $p |- ( ( A e. R /\ B e. R /\ C e. R ) -> th ) $=
      cA cR wcel cB cR wcel cC cR wcel wth cC cR wcel cA cR wcel cB cR wcel wa
      wth cA cR wcel cB cR wcel wa wch wi cA cR wcel cB cR wcel wa wth wi vv vu
      cC cD cF cR 3optocl.1 vv cv vu cv cop cC wceq wch wth cA cR wcel cB cR
      wcel wa 3optocl.4 imbi2d cA cR wcel cB cR wcel wa vv cv cD wcel vu cv cF
      wcel wa wch vv cv cD wcel vu cv cF wcel wa wph wi vv cv cD wcel vu cv cF
      wcel wa wps wi vv cv cD wcel vu cv cF wcel wa wch wi vx vy vz vw cA cB cD
      cF cR 3optocl.1 vx cv vy cv cop cA wceq wph wps vv cv cD wcel vu cv cF
      wcel wa 3optocl.2 imbi2d vz cv vw cv cop cB wceq wps wch vv cv cD wcel vu
      cv cF wcel wa 3optocl.3 imbi2d vx cv cD wcel vy cv cF wcel wa vz cv cD
      wcel vw cv cF wcel wa vv cv cD wcel vu cv cF wcel wa wph 3optocl.5 3expia
      2optocl com12 optocl impcom 3impa $.
  $}

  ${
    $d x y z w v u A $.  $d x y z w v u B $.  $d x y z w v u C $.
    $d x y z w v u D $.  $d x y z w v u S $.  $d x y ph $.  $d z w v u ps $.
    opbrop.1 $e |- ( ( ( z = A /\ w = B ) /\ ( v = C /\ u = D ) ) ->
                     ( ph <-> ps ) ) $.
    opbrop.2 $e |- R = { <. x , y >. | ( ( x e. ( S X. S ) /\
                      y e. ( S X. S ) ) /\
                      E. z E. w E. v E. u ( ( x = <. z , w >. /\
                      y = <. v , u >. ) /\ ph ) ) } $.
    $( Ordered pair membership in a relation.  Special case.  (Contributed by
       NM, 5-Aug-1995.) $)
    opbrop $p |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) ->
                   ( <. A , B >. R <. C , D >. <-> ps ) ) $=
      cA cS wcel cB cS wcel wa cC cS wcel cD cS wcel wa wa cA cB cop cC cD cop
      cR wbr cA cB cop cS cS cxp wcel cC cD cop cS cS cxp wcel wa wps wa wps cA
      cB cop cC cD cop cR wbr cA cB cop cS cS cxp wcel cC cD cop cS cS cxp wcel
      wa cA cB cop vz cv vw cv cop wceq cC cD cop vv cv vu cv cop wceq wa wph
      wa vu wex vv wex vw wex vz wex wa cA cS wcel cB cS wcel wa cC cS wcel cD
      cS wcel wa wa cA cB cop cS cS cxp wcel cC cD cop cS cS cxp wcel wa wps wa
      vx cv cS cS cxp wcel vy cv cS cS cxp wcel wa vx cv vz cv vw cv cop wceq
      vy cv vv cv vu cv cop wceq wa wph wa vu wex vv wex vw wex vz wex wa cA cB
      cop cS cS cxp wcel vy cv cS cS cxp wcel wa cA cB cop vz cv vw cv cop wceq
      vy cv vv cv vu cv cop wceq wa wph wa vu wex vv wex vw wex vz wex wa cA cB
      cop cS cS cxp wcel cC cD cop cS cS cxp wcel wa cA cB cop vz cv vw cv cop
      wceq cC cD cop vv cv vu cv cop wceq wa wph wa vu wex vv wex vw wex vz wex
      wa vx vy cA cB cop cC cD cop cR cA cB opex cC cD opex vx cv cA cB cop
      wceq vx cv cS cS cxp wcel vy cv cS cS cxp wcel wa cA cB cop cS cS cxp
      wcel vy cv cS cS cxp wcel wa vx cv vz cv vw cv cop wceq vy cv vv cv vu cv
      cop wceq wa wph wa vu wex vv wex vw wex vz wex cA cB cop vz cv vw cv cop
      wceq vy cv vv cv vu cv cop wceq wa wph wa vu wex vv wex vw wex vz wex vx
      cv cA cB cop wceq vx cv cS cS cxp wcel cA cB cop cS cS cxp wcel vy cv cS
      cS cxp wcel vx cv cA cB cop cS cS cxp eleq1 anbi1d vx cv cA cB cop wceq
      vx cv vz cv vw cv cop wceq vy cv vv cv vu cv cop wceq wa wph wa cA cB cop
      vz cv vw cv cop wceq vy cv vv cv vu cv cop wceq wa wph wa vz vw vv vu vx
      cv cA cB cop wceq vx cv vz cv vw cv cop wceq vy cv vv cv vu cv cop wceq
      wa cA cB cop vz cv vw cv cop wceq vy cv vv cv vu cv cop wceq wa wph vx cv
      cA cB cop wceq vx cv vz cv vw cv cop wceq cA cB cop vz cv vw cv cop wceq
      vy cv vv cv vu cv cop wceq vx cv cA cB cop vz cv vw cv cop eqeq1 anbi1d
      anbi1d 4exbidv anbi12d vy cv cC cD cop wceq cA cB cop cS cS cxp wcel vy
      cv cS cS cxp wcel wa cA cB cop cS cS cxp wcel cC cD cop cS cS cxp wcel wa
      cA cB cop vz cv vw cv cop wceq vy cv vv cv vu cv cop wceq wa wph wa vu
      wex vv wex vw wex vz wex cA cB cop vz cv vw cv cop wceq cC cD cop vv cv
      vu cv cop wceq wa wph wa vu wex vv wex vw wex vz wex vy cv cC cD cop wceq
      vy cv cS cS cxp wcel cC cD cop cS cS cxp wcel cA cB cop cS cS cxp wcel vy
      cv cC cD cop cS cS cxp eleq1 anbi2d vy cv cC cD cop wceq cA cB cop vz cv
      vw cv cop wceq vy cv vv cv vu cv cop wceq wa wph wa cA cB cop vz cv vw cv
      cop wceq cC cD cop vv cv vu cv cop wceq wa wph wa vz vw vv vu vy cv cC cD
      cop wceq cA cB cop vz cv vw cv cop wceq vy cv vv cv vu cv cop wceq wa cA
      cB cop vz cv vw cv cop wceq cC cD cop vv cv vu cv cop wceq wa wph vy cv
      cC cD cop wceq vy cv vv cv vu cv cop wceq cC cD cop vv cv vu cv cop wceq
      cA cB cop vz cv vw cv cop wceq vy cv cC cD cop vv cv vu cv cop eqeq1
      anbi2d anbi1d 4exbidv anbi12d opbrop.2 brab cA cS wcel cB cS wcel wa cC
      cS wcel cD cS wcel wa wa cA cB cop vz cv vw cv cop wceq cC cD cop vv cv
      vu cv cop wceq wa wph wa vu wex vv wex vw wex vz wex wps cA cB cop cS cS
      cxp wcel cC cD cop cS cS cxp wcel wa wph wps vz vw vv vu cA cB cC cD cS
      cS opbrop.1 copsex4g anbi2d syl5bb cA cS wcel cB cS wcel wa cC cS wcel cD
      cS wcel wa wa cA cB cop cS cS cxp wcel cC cD cop cS cS cxp wcel wa wps cA
      cS wcel cB cS wcel wa cA cB cop cS cS cxp wcel cC cS wcel cD cS wcel wa
      cC cD cop cS cS cxp wcel cA cB cS cS opelxpi cC cD cS cS opelxpi anim12i
      biantrurd bitr4d $.
  $}

  ${
    $d x y z A $.
    $( The cross product with the empty set is empty.  Part of Theorem 3.13(ii)
       of [Monk1] p. 37.  (Contributed by NM, 4-Jul-1994.) $)
    xp0r $p |- ( (/) X. A ) = (/) $=
      vz c0 cA cxp c0 vz cv c0 cA cxp wcel vz cv vx cv vy cv cop wceq vx cv c0
      wcel vy cv cA wcel wa wa vy wex vx wex vz cv c0 wcel vx vy vz cv c0 cA
      elxp vz cv vx cv vy cv cop wceq vx cv c0 wcel vy cv cA wcel wa wa vy wex
      vx wex vz cv c0 wcel vz cv vx cv vy cv cop wceq vx cv c0 wcel vy cv cA
      wcel wa wa vy wex vx vz cv vx cv vy cv cop wceq vx cv c0 wcel vy cv cA
      wcel wa wa vy vz cv vx cv vy cv cop wceq vx cv c0 wcel vy cv cA wcel wa
      wa vx cv c0 wcel vx cv noel vz cv vx cv vy cv cop wceq vx cv c0 wcel vy
      cv cA wcel simprl mto nex nex vz cv noel 2false bitri eqriv $.
  $}

  ${
    $d x y z $.
    $( Ordinal numbers and ordered pairs are disjoint collections.  This
       theorem can be used if we want to extend a set of ordinal numbers or
       ordered pairs with disjoint elements.  See also ~ snsn0non .
       (Contributed by NM, 1-Jun-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    onxpdisj $p |- ( On i^i ( _V X. _V ) ) = (/) $=
      con0 cvv cvv cxp cin c0 wceq vx cv cvv cvv cxp wcel wn vx con0 vx con0
      cvv cvv cxp disj vx cv con0 wcel vx cv c0 wceq c0 vx cv wcel wo vx cv cvv
      cvv cxp wcel wn vx cv on0eqel vx cv c0 wceq vx cv cvv cvv cxp wcel wn c0
      vx cv wcel vx cv c0 wceq vx cv cvv cvv cxp wcel c0 cvv cvv cxp wcel cvv
      cvv 0nelxp vx cv c0 cvv cvv cxp eleq1 mtbiri vx cv cvv cvv cxp wcel c0 vx
      cv wcel cvv cvv vx cv 0nelelxp con2i jaoi syl mprgbir $.
  $}

  $( The class of ordinal numbers is not equal to the universe.  (Contributed
     by NM, 16-Jun-2007.)  (Proof shortened by Mario Carneiro, 10-Jan-2013.) $)
  onnev $p |- On =/= _V $=
    c0 csn csn con0 wcel wn con0 cvv wne snsn0non c0 csn csn con0 wcel con0 cvv
    con0 cvv wceq c0 csn csn cvv con0 c0 csn snex con0 cvv wceq id syl5eleqr
    necon3bi ax-mp $.

  $( Equality theorem for the relation predicate.  (Contributed by NM,
     1-Aug-1994.) $)
  releq $p |- ( A = B -> ( Rel A <-> Rel B ) ) $=
    cA cB wceq cA cvv cvv cxp wss cB cvv cvv cxp wss cA wrel cB wrel cA cB cvv
    cvv cxp sseq1 cA df-rel cB df-rel 3bitr4g $.

  ${
    releqi.1 $e |- A = B $.
    $( Equality inference for the relation predicate.  (Contributed by NM,
       8-Dec-2006.) $)
    releqi $p |- ( Rel A <-> Rel B ) $=
      cA cB wceq cA wrel cB wrel wb releqi.1 cA cB releq ax-mp $.
  $}

  ${
    releqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for the relation predicate.  (Contributed by NM,
       8-Mar-2014.) $)
    releqd $p |- ( ph -> ( Rel A <-> Rel B ) ) $=
      wph cA cB wceq cA wrel cB wrel wb releqd.1 cA cB releq syl $.
  $}

  ${
    $d y A $.  $d x y $.
    nfrel.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for a relation.  (Contributed by NM,
       31-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nfrel $p |- F/ x Rel A $=
      cA wrel cA cvv cvv cxp wss vx cA df-rel vx cA cvv cvv cxp nfrel.1 vx cvv
      cvv cxp nfcv nfss nfxfr $.
  $}

  $( Subclass theorem for relation predicate.  Theorem 2 of [Suppes] p. 58.
     (Contributed by NM, 15-Aug-1994.) $)
  relss $p |- ( A C_ B -> ( Rel B -> Rel A ) ) $=
    cA cB wss cB cvv cvv cxp wss cA cvv cvv cxp wss cB wrel cA wrel cA cB cvv
    cvv cxp sstr2 cB df-rel cA df-rel 3imtr4g $.

  ${
    $d x y z A $.  $d x y z B $.
    $( A subclass relationship depends only on a relation's ordered pairs.
       Theorem 3.2(i) of [Monk1] p. 33.  (Contributed by NM, 2-Aug-1994.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    ssrel $p |- ( Rel A -> ( A C_ B <->
                A. x A. y ( <. x , y >. e. A -> <. x , y >. e. B ) ) ) $=
      cA wrel cA cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vy
      wal vx wal cA cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi
      vx vy cA cB vx cv vy cv cop ssel alrimivv vx cv vy cv cop cA wcel vx cv
      vy cv cop cB wcel wi vy wal vx wal cA wrel cA cB wss vx cv vy cv cop cA
      wcel vx cv vy cv cop cB wcel wi vy wal vx wal vz cv cA wcel vz cv vx cv
      vy cv cop wceq vy wex vx wex wi vz wal vz cv cA wcel vz cv cB wcel wi vz
      wal cA wrel cA cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi
      vy wal vx wal vz cv cA wcel vz cv vx cv vy cv cop wceq vy wex vx wex wi
      vz cv cA wcel vz cv cB wcel wi vz vx cv vy cv cop cA wcel vx cv vy cv cop
      cB wcel wi vy wal vx wal vz cv cA wcel vz cv vx cv vy cv cop wceq vy wex
      vx wex vz cv cB wcel vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi
      vy wal vx wal vz cv vx cv vy cv cop wceq vy wex vx wex vz cv cA wcel vz
      cv cB wcel vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vy wal vx
      wal vz cv vx cv vy cv cop wceq vz cv cA wcel vz cv cB wcel wi wi vy wal
      vx wal vz cv vx cv vy cv cop wceq vy wex vx wex vz cv cA wcel vz cv cB
      wcel wi wi vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vz cv vx cv
      vy cv cop wceq vz cv cA wcel vz cv cB wcel wi wi vx vy vz cv vx cv vy cv
      cop wceq vz cv cA wcel vz cv cB wcel wi vx cv vy cv cop cA wcel vx cv vy
      cv cop cB wcel wi vz cv vx cv vy cv cop wceq vz cv cA wcel vx cv vy cv
      cop cA wcel vz cv cB wcel vx cv vy cv cop cB wcel vz cv vx cv vy cv cop
      cA eleq1 vz cv vx cv vy cv cop cB eleq1 imbi12d biimprcd 2alimi vz cv vx
      cv vy cv cop wceq vz cv cA wcel vz cv cB wcel wi vx vy 19.23vv sylib
      com23 a2d alimdv cA wrel cA cvv cvv cxp wss vz cv cA wcel vz cv cvv cvv
      cxp wcel wi vz wal vz cv cA wcel vz cv vx cv vy cv cop wceq vy wex vx wex
      wi vz wal cA df-rel vz cA cvv cvv cxp dfss2 vz cv cA wcel vz cv cvv cvv
      cxp wcel wi vz cv cA wcel vz cv vx cv vy cv cop wceq vy wex vx wex wi vz
      vz cv cvv cvv cxp wcel vz cv vx cv vy cv cop wceq vy wex vx wex vz cv cA
      wcel vx vy vz cv elvv imbi2i albii 3bitri vz cA cB dfss2 3imtr4g com12
      impbid2 $.

    $( Extensionality principle for relations.  Theorem 3.2(ii) of [Monk1]
       p. 33.  (Contributed by NM, 2-Aug-1994.) $)
    eqrel $p |- ( ( Rel A /\ Rel B ) -> ( A = B <->
                A. x A. y ( <. x , y >. e. A <-> <. x , y >. e. B ) ) ) $=
      cA wrel cB wrel wa cA cB wss cB cA wss wa vx cv vy cv cop cA wcel vx cv
      vy cv cop cB wcel wi vy wal vx wal vx cv vy cv cop cB wcel vx cv vy cv
      cop cA wcel wi vy wal vx wal wa cA cB wceq vx cv vy cv cop cA wcel vx cv
      vy cv cop cB wcel wb vy wal vx wal cA wrel cA cB wss vx cv vy cv cop cA
      wcel vx cv vy cv cop cB wcel wi vy wal vx wal cB wrel cB cA wss vx cv vy
      cv cop cB wcel vx cv vy cv cop cA wcel wi vy wal vx wal vx vy cA cB ssrel
      vx vy cB cA ssrel bi2anan9 cA cB eqss vx cv vy cv cop cA wcel vx cv vy cv
      cop cB wcel vx vy 2albiim 3bitr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.
    relssi.1 $e |- Rel A $.
    relssi.2 $e |- ( <. x , y >. e. A -> <. x , y >. e. B ) $.
    $( Inference from subclass principle for relations.  (Contributed by NM,
       31-Mar-1998.) $)
    relssi $p |- A C_ B $=
      cA cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vy wal vx cA
      wrel cA cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vy wal
      vx wal wb relssi.1 vx vy cA cB ssrel ax-mp vx cv vy cv cop cA wcel vx cv
      vy cv cop cB wcel wi vy relssi.2 ax-gen mpgbir $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y ph $.
    relssdv.1 $e |- ( ph -> Rel A ) $.
    relssdv.2 $e |- ( ph -> ( <. x , y >. e. A -> <. x , y >. e. B ) ) $.
    $( Deduction from subclass principle for relations.  (Contributed by NM,
       11-Sep-2004.) $)
    relssdv $p |- ( ph -> A C_ B ) $=
      wph cA cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vy wal
      vx wal wph vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wi vx vy
      relssdv.2 alrimivv wph cA wrel cA cB wss vx cv vy cv cop cA wcel vx cv vy
      cv cop cB wcel wi vy wal vx wal wb relssdv.1 vx vy cA cB ssrel syl mpbird
      $.
  $}

  ${
    $d x y A $.  $d x y B $.
    eqrelriv.1 $e |- ( <. x , y >. e. A <-> <. x , y >. e. B ) $.
    $( Inference from extensionality principle for relations.  (Contributed by
       FL, 15-Oct-2012.) $)
    eqrelriv $p |- ( ( Rel A /\ Rel B ) -> A = B ) $=
      cA wrel cB wrel wa cA cB wceq vx cv vy cv cop cA wcel vx cv vy cv cop cB
      wcel wb vy wal vx wal vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wb
      vx vy eqrelriv.1 gen2 vx vy cA cB eqrel mpbiri $.
  $}

  ${
    $d x y A $.  $d x y B $.
    eqreliiv.1 $e |- Rel A $.
    eqreliiv.2 $e |- Rel B $.
    eqreliiv.3 $e |- ( <. x , y >. e. A <-> <. x , y >. e. B ) $.
    $( Inference from extensionality principle for relations.  (Contributed by
       NM, 17-Mar-1995.) $)
    eqrelriiv $p |- A = B $=
      cA wrel cB wrel cA cB wceq eqreliiv.1 eqreliiv.2 vx vy cA cB eqreliiv.3
      eqrelriv mp2an $.
  $}

  ${
    $d x y A $.  $d x y B $.
    eqbrriv.1 $e |- Rel A $.
    eqbrriv.2 $e |- Rel B $.
    eqbrriv.3 $e |- ( x A y <-> x B y ) $.
    $( Inference from extensionality principle for relations.  (Contributed by
       NM, 12-Dec-2006.) $)
    eqbrriv $p |- A = B $=
      vx vy cA cB eqbrriv.1 eqbrriv.2 vx cv vy cv cA wbr vx cv vy cv cB wbr vx
      cv vy cv cop cA wcel vx cv vy cv cop cB wcel eqbrriv.3 vx cv vy cv cA
      df-br vx cv vy cv cB df-br 3bitr3i eqrelriiv $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d ph x $.  $d ph y $.
    eqrelrdv.1 $e |- Rel A $.
    eqrelrdv.2 $e |- Rel B $.
    eqrelrdv.3 $e |- ( ph -> ( <. x , y >. e. A <-> <. x , y >. e. B ) ) $.
    $( Deduce equality of relations from equivalence of membership.
       (Contributed by Rodolfo Medina, 10-Oct-2010.) $)
    eqrelrdv $p |- ( ph -> A = B ) $=
      wph vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wb vy wal vx wal cA
      cB wceq wph vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wb vx vy
      eqrelrdv.3 alrimivv cA wrel cB wrel cA cB wceq vx cv vy cv cop cA wcel vx
      cv vy cv cop cB wcel wb vy wal vx wal wb eqrelrdv.1 eqrelrdv.2 vx vy cA
      cB eqrel mp2an sylibr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d ph x $.  $d ph y $.
    eqbrrdv.1 $e |- ( ph -> Rel A ) $.
    eqbrrdv.2 $e |- ( ph -> Rel B ) $.
    eqbrrdv.3 $e |- ( ph -> ( x A y <-> x B y ) ) $.
    $( Deduction from extensionality principle for relations.  (Contributed by
       Mario Carneiro, 3-Jan-2017.) $)
    eqbrrdv $p |- ( ph -> A = B ) $=
      wph cA cB wceq vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wb vy wal
      vx wal wph vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wb vx vy wph
      vx cv vy cv cA wbr vx cv vy cv cB wbr vx cv vy cv cop cA wcel vx cv vy cv
      cop cB wcel eqbrrdv.3 vx cv vy cv cA df-br vx cv vy cv cB df-br 3bitr3g
      alrimivv wph cA wrel cB wrel cA cB wceq vx cv vy cv cop cA wcel vx cv vy
      cv cop cB wcel wb vy wal vx wal wb eqbrrdv.1 eqbrrdv.2 vx vy cA cB eqrel
      syl2anc mpbird $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d ph x $.  $d ph y $.
    eqbrrdiv.1 $e |- Rel A $.
    eqbrrdiv.2 $e |- Rel B $.
    eqbrrdiv.3 $e |- ( ph -> ( x A y <-> x B y ) ) $.
    $( Deduction from extensionality principle for relations.  (Contributed by
       Rodolfo Medina, 10-Oct-2010.) $)
    eqbrrdiv $p |- ( ph -> A = B ) $=
      wph vx vy cA cB eqbrrdiv.1 eqbrrdiv.2 wph vx cv vy cv cA wbr vx cv vy cv
      cB wbr vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel eqbrrdiv.3 vx cv
      vy cv cA df-br vx cv vy cv cB df-br 3bitr3g eqrelrdv $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d ph x $.  $d ph y $.
    eqrelrdv2.1 $e |- ( ph
       -> ( <. x , y >. e. A <-> <. x , y >. e. B ) ) $.
    $( A version of ~ eqrelrdv .  (Contributed by Rodolfo Medina,
       10-Oct-2010.) $)
    eqrelrdv2 $p |- ( ( ( Rel A /\ Rel B ) /\ ph ) -> A = B ) $=
      cA wrel cB wrel wa wph wa cA cB wceq vx cv vy cv cop cA wcel vx cv vy cv
      cop cB wcel wb vy wal vx wal wph vx cv vy cv cop cA wcel vx cv vy cv cop
      cB wcel wb vy wal vx wal cA wrel cB wrel wa wph vx cv vy cv cop cA wcel
      vx cv vy cv cop cB wcel wb vx vy eqrelrdv2.1 alrimivv adantl cA wrel cB
      wrel wa cA cB wceq vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wb vy
      wal vx wal wb wph vx vy cA cB eqrel adantr mpbird $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.
    $( A subclass relationship determined by ordered triples.  Use ~ relrelss
       to express the antecedent in terms of the relation predicate.
       (Contributed by NM, 17-Dec-2008.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    ssrelrel $p |- ( A C_ ( ( _V X. _V ) X. _V ) -> ( A C_ B <->
                   A. x A. y A. z ( <. <. x , y >. , z >. e. A
                       -> <. <. x , y >. , z >. e. B ) ) ) $=
      cA cvv cvv cxp cvv cxp wss cA cB wss vx cv vy cv cop vz cv cop cA wcel vx
      cv vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal cA cB wss vx cv vy
      cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz wal vx
      vy cA cB wss vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop
      cB wcel wi vz cA cB vx cv vy cv cop vz cv cop ssel alrimiv alrimivv vx cv
      vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz wal
      vy wal vx wal cA cvv cvv cxp cvv cxp wss cA cB wss vx cv vy cv cop vz cv
      cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal vw
      cv cA wcel vw cv cvv cvv cxp cvv cxp wcel wi vw wal vw cv cA wcel vw cv
      cB wcel wi vw wal cA cvv cvv cxp cvv cxp wss cA cB wss vx cv vy cv cop vz
      cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal
      vw cv cA wcel vw cv cvv cvv cxp cvv cxp wcel wi vw cv cA wcel vw cv cB
      wcel wi vw vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB
      wcel wi vz wal vy wal vx wal vw cv cA wcel vw cv cvv cvv cxp cvv cxp wcel
      vw cv cB wcel vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop
      cB wcel wi vz wal vy wal vx wal vw cv cvv cvv cxp cvv cxp wcel vw cv cA
      wcel vw cv cB wcel vw cv cvv cvv cxp cvv cxp wcel vw cv vx cv vy cv cop
      vz cv cop wceq vz wex vy wex vx wex vx cv vy cv cop vz cv cop cA wcel vx
      cv vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal vw cv cA wcel vw
      cv cB wcel wi vx vy vz vw cv elvvv vx cv vy cv cop vz cv cop cA wcel vx
      cv vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal vw cv vx cv vy cv
      cop vz cv cop wceq vz wex vw cv cA wcel vw cv cB wcel wi wi vy wal vx wal
      vw cv vx cv vy cv cop vz cv cop wceq vz wex vy wex vx wex vw cv cA wcel
      vw cv cB wcel wi wi vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz
      cv cop cB wcel wi vz wal vw cv vx cv vy cv cop vz cv cop wceq vz wex vw
      cv cA wcel vw cv cB wcel wi wi vx vy vx cv vy cv cop vz cv cop cA wcel vx
      cv vy cv cop vz cv cop cB wcel wi vz wal vw cv vx cv vy cv cop vz cv cop
      wceq vw cv cA wcel vw cv cB wcel wi wi vz wal vw cv vx cv vy cv cop vz cv
      cop wceq vz wex vw cv cA wcel vw cv cB wcel wi wi vx cv vy cv cop vz cv
      cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vw cv vx cv vy cv cop vz
      cv cop wceq vw cv cA wcel vw cv cB wcel wi wi vz vw cv vx cv vy cv cop vz
      cv cop wceq vw cv cA wcel vw cv cB wcel wi vx cv vy cv cop vz cv cop cA
      wcel vx cv vy cv cop vz cv cop cB wcel wi vw cv vx cv vy cv cop vz cv cop
      wceq vw cv cA wcel vx cv vy cv cop vz cv cop cA wcel vw cv cB wcel vx cv
      vy cv cop vz cv cop cB wcel vw cv vx cv vy cv cop vz cv cop cA eleq1 vw
      cv vx cv vy cv cop vz cv cop cB eleq1 imbi12d biimprcd alimi vw cv vx cv
      vy cv cop vz cv cop wceq vw cv cA wcel vw cv cB wcel wi vz 19.23v sylib
      2alimi vw cv vx cv vy cv cop vz cv cop wceq vz wex vw cv cA wcel vw cv cB
      wcel wi vx vy 19.23vv sylib syl5bi com23 a2d alimdv vw cA cvv cvv cxp cvv
      cxp dfss2 vw cA cB dfss2 3imtr4g com12 impbid2 $.

    $( Extensionality principle for ordered triples (used by 2-place operations
       ~ df-oprab ), analogous to ~ eqrel .  Use ~ relrelss to express the
       antecedent in terms of the relation predicate.  (Contributed by NM,
       17-Dec-2008.) $)
    eqrelrel $p |- ( ( A u. B ) C_ ( ( _V X. _V ) X. _V ) -> ( A = B <->
                   A. x A. y A. z ( <. <. x , y >. , z >. e. A
                       <-> <. <. x , y >. , z >. e. B ) ) ) $=
      cA cB cun cvv cvv cxp cvv cxp wss cA cvv cvv cxp cvv cxp wss cB cvv cvv
      cxp cvv cxp wss wa cA cB wceq vx cv vy cv cop vz cv cop cA wcel vx cv vy
      cv cop vz cv cop cB wcel wb vz wal vy wal vx wal wb cA cB cvv cvv cxp cvv
      cxp unss cA cvv cvv cxp cvv cxp wss cB cvv cvv cxp cvv cxp wss wa cA cB
      wss cB cA wss wa vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv
      cop cB wcel wi vz wal vy wal vx wal vx cv vy cv cop vz cv cop cB wcel vx
      cv vy cv cop vz cv cop cA wcel wi vz wal vy wal vx wal wa cA cB wceq vx
      cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wb vz
      wal vy wal vx wal cA cvv cvv cxp cvv cxp wss cA cB wss vx cv vy cv cop vz
      cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal
      cB cvv cvv cxp cvv cxp wss cB cA wss vx cv vy cv cop vz cv cop cB wcel vx
      cv vy cv cop vz cv cop cA wcel wi vz wal vy wal vx wal vx vy vz cA cB
      ssrelrel vx vy vz cB cA ssrelrel bi2anan9 cA cB eqss vx cv vy cv cop vz
      cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wb vz wal vy wal vx wal
      vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz
      wal vy wal vx cv vy cv cop vz cv cop cB wcel vx cv vy cv cop vz cv cop cA
      wcel wi vz wal vy wal wa vx wal vx cv vy cv cop vz cv cop cA wcel vx cv
      vy cv cop vz cv cop cB wcel wi vz wal vy wal vx wal vx cv vy cv cop vz cv
      cop cB wcel vx cv vy cv cop vz cv cop cA wcel wi vz wal vy wal vx wal wa
      vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wb vz
      wal vy wal vx cv vy cv cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB
      wcel wi vz wal vy wal vx cv vy cv cop vz cv cop cB wcel vx cv vy cv cop
      vz cv cop cA wcel wi vz wal vy wal wa vx vx cv vy cv cop vz cv cop cA
      wcel vx cv vy cv cop vz cv cop cB wcel vy vz 2albiim albii vx cv vy cv
      cop vz cv cop cA wcel vx cv vy cv cop vz cv cop cB wcel wi vz wal vy wal
      vx cv vy cv cop vz cv cop cB wcel vx cv vy cv cop vz cv cop cA wcel wi vz
      wal vy wal vx 19.26 bitri 3bitr4g sylbir $.
  $}

  ${
    $d x y A $.
    $( A member of a relation is an ordered pair.  (Contributed by NM,
       17-Sep-2006.) $)
    elrel $p |- ( ( Rel R /\ A e. R ) -> E. x E. y A = <. x , y >. ) $=
      cR wrel cA cR wcel wa cA cvv cvv cxp wcel cA vx cv vy cv cop wceq vy wex
      vx wex cR wrel cR cvv cvv cxp cA cR wrel cR cvv cvv cxp wss cR df-rel
      biimpi sselda vx vy cA elvv sylib $.
  $}

  ${
    relsn.1 $e |- A e. _V $.
    $( A singleton is a relation iff it is an ordered pair.  (Contributed by
       NM, 24-Sep-2013.) $)
    relsn $p |- ( Rel { A } <-> A e. ( _V X. _V ) ) $=
      cA csn wrel cA csn cvv cvv cxp wss cA cvv cvv cxp wcel cA csn df-rel cA
      cvv cvv cxp relsn.1 snss bitr4i $.

    relsnop.2 $e |- B e. _V $.
    $( A singleton of an ordered pair is a relation.  (Contributed by NM,
       17-May-1998.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    relsnop $p |- Rel { <. A , B >. } $=
      cA cB cop csn wrel cA cB cop cvv cvv cxp wcel cA cB relsn.1 relsnop.2
      opelvv cA cB cop cA cB opex relsn mpbir $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d x y D $.
    $( Subset theorem for cross product.  Generalization of Theorem 101 of
       [Suppes] p. 52.  (Contributed by NM, 26-Aug-1995.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
    xpss12 $p |- ( ( A C_ B /\ C C_ D ) -> ( A X. C ) C_ ( B X. D ) ) $=
      cA cB wss cC cD wss wa vx cv cA wcel vy cv cC wcel wa vx vy copab vx cv
      cB wcel vy cv cD wcel wa vx vy copab cA cC cxp cB cD cxp cA cB wss cC cD
      wss wa vx cv cA wcel vy cv cC wcel wa vx cv cB wcel vy cv cD wcel wa vx
      vy cA cB wss vx cv cA wcel vx cv cB wcel cC cD wss vy cv cC wcel vy cv cD
      wcel cA cB vx cv ssel cC cD vy cv ssel im2anan9 ssopab2dv vx vy cA cC
      df-xp vx vy cB cD df-xp 3sstr4g $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( A cross product is included in the ordered pair universe.  Exercise 3 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 2-Aug-1994.) $)
    xpss $p |- ( A X. B ) C_ ( _V X. _V ) $=
      cA cvv wss cB cvv wss cA cB cxp cvv cvv cxp wss cA ssv cB ssv cA cvv cB
      cvv xpss12 mp2an $.
  $}

  $( A cross product is a relation.  Theorem 3.13(i) of [Monk1] p. 37.
     (Contributed by NM, 2-Aug-1994.) $)
  relxp $p |- Rel ( A X. B ) $=
    cA cB cxp wrel cA cB cxp cvv cvv cxp wss cA cB xpss cA cB cxp df-rel mpbir
    $.

  $( Subset relation for cross product.  (Contributed by Jeff Hankins,
     30-Aug-2009.) $)
  xpss1 $p |- ( A C_ B -> ( A X. C ) C_ ( B X. C ) ) $=
    cA cB wss cC cC wss cA cC cxp cB cC cxp wss cC ssid cA cB cC cC xpss12
    mpan2 $.

  $( Subset relation for cross product.  (Contributed by Jeff Hankins,
     30-Aug-2009.) $)
  xpss2 $p |- ( A C_ B -> ( C X. A ) C_ ( C X. B ) ) $=
    cC cC wss cA cB wss cC cA cxp cC cB cxp wss cC ssid cC cC cA cB xpss12 mpan
    $.

  ${
    $d A x y z $.  $d B x y z $.
    $( A cross product is included in the power of the power of the union of
       its arguments.  (Contributed by NM, 13-Sep-2006.) $)
    xpsspw $p |- ( A X. B ) C_ ~P ~P ( A u. B ) $=
      vz cA cB cxp cA cB cun cpw cpw vz cv cA cB cxp wcel vz cv cA cB cun cpw
      wss vz cv cA cB cun cpw cpw wcel vz cv cA cB cxp wcel vz cv vx cv vy cv
      cop wceq vx cv cA wcel vy cv cB wcel wa wa vy wex vx wex vz cv cA cB cun
      cpw wss vx vy vz cv cA cB elxpi vz cv vx cv vy cv cop wceq vx cv cA wcel
      vy cv cB wcel wa wa vz cv cA cB cun cpw wss vx vy vx cv cA wcel vy cv cB
      wcel wa vz cv vx cv vy cv cop wceq vx cv vy cv cop cA cB cun cpw wss vz
      cv cA cB cun cpw wss vx cv cA wcel vy cv cB wcel wa vx cv vy cv cop vx cv
      csn vx cv vy cv cpr cpr cA cB cun cpw vx cv vy cv vx vex vy vex dfop vx
      cv cA wcel vy cv cB wcel wa vz vx cv csn vx cv vy cv cpr cpr cA cB cun
      cpw vx cv cA wcel vy cv cB wcel wa vz cv vx cv csn wceq vz cv vx cv vy cv
      cpr wceq wo vz cv cA cB cun wss vz cv vx cv csn vx cv vy cv cpr cpr wcel
      vz cv cA cB cun cpw wcel vx cv cA wcel vy cv cB wcel wa vz cv vx cv csn
      wceq vz cv cA cB cun wss vz cv vx cv vy cv cpr wceq vx cv cA wcel vy cv
      cB wcel wa vz cv cA cB cun wss vz cv vx cv csn wceq vx cv csn cA cB cun
      wss vx cv cA wcel vx cv csn cA cB cun wss vy cv cB wcel vx cv cA wcel vx
      cv csn cA wss vx cv csn cA cB cun wss vx cv cA snssi vx cv csn cA cB
      ssun3 syl adantr vz cv vx cv csn cA cB cun sseq1 syl5ibrcom vx cv cA wcel
      vy cv cB wcel wa vz cv cA cB cun wss vz cv vx cv vy cv cpr wceq vx cv vy
      cv cpr cA cB cun wss vx cv cA wcel vy cv cB wcel wa vx cv vy cv cpr vx cv
      csn vy cv csn cun cA cB cun vx cv vy cv df-pr vx cv cA wcel vy cv cB wcel
      wa vx cv csn cA cB cun wss vy cv csn cA cB cun wss wa vx cv csn vy cv csn
      cun cA cB cun wss vx cv cA wcel vx cv csn cA cB cun wss vy cv cB wcel vy
      cv csn cA cB cun wss vx cv cA wcel vx cv csn cA wss vx cv csn cA cB cun
      wss vx cv cA snssi vx cv csn cA cB ssun3 syl vy cv cB wcel vy cv csn cB
      wss vy cv csn cA cB cun wss vy cv cB snssi vy cv csn cB cA ssun4 syl
      anim12i vx cv csn vy cv csn cA cB cun unss sylib syl5eqss vz cv vx cv vy
      cv cpr cA cB cun sseq1 syl5ibrcom jaod vz cv vx cv csn vx cv vy cv cpr vz
      vex elpr vz cv cA cB cun vz vex elpw 3imtr4g ssrdv syl5eqss vz cv vx cv
      vy cv cop wceq vz cv cA cB cun cpw wss vx cv vy cv cop cA cB cun cpw wss
      vz cv vx cv vy cv cop cA cB cun cpw sseq1 biimpar sylan2 exlimivv syl vz
      cv cA cB cun cpw vz vex elpw sylibr ssriv $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( A cross product is included in the power of the power of the union of
       its arguments.  (Contributed by NM, 13-Sep-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    xpsspwOLD $p |- ( A X. B ) C_ ~P ~P ( A u. B ) $=
      vx vy cA cB cxp cA cB cun cpw cpw cA cB relxp vx cv vy cv cop cA cB cxp
      wcel vx cv cA wcel vy cv cB wcel wa vx cv vy cv cop cA cB cun cpw cpw
      wcel vx cv vy cv cA cB opelxp vx cv cA wcel vy cv cB wcel wa vx cv csn cA
      cB cun cpw wcel vx cv vy cv cpr cA cB cun cpw wcel wa vx cv vy cv cop cA
      cB cun cpw cpw wcel vx cv cA wcel vy cv cB wcel wa vx cv csn cA cB cun
      cpw wcel vx cv vy cv cpr cA cB cun cpw wcel vx cv cA wcel vx cv csn cA cB
      cun cpw wcel vy cv cB wcel vx cv cA wcel vx cv csn cA cB cun wss vx cv
      csn cA cB cun cpw wcel vx cv cA wcel vx cv csn cA wss vx cv csn cA cB cun
      wss vx cv cA snssi vx cv csn cA cB ssun3 syl vx cv csn cA cB cun vx cv
      snex elpw sylibr adantr vx cv cA wcel vy cv cB wcel wa vx cv vy cv cpr cA
      cB cun wss vx cv vy cv cpr cA cB cun cpw wcel vx cv cA wcel vy cv cB wcel
      wa vx cv vy cv cpr vx cv csn vy cv csn cun cA cB cun vx cv vy cv df-pr vx
      cv cA wcel vy cv cB wcel wa vx cv csn cA cB cun wss vy cv csn cA cB cun
      wss wa vx cv csn vy cv csn cun cA cB cun wss vx cv cA wcel vx cv csn cA
      cB cun wss vy cv cB wcel vy cv csn cA cB cun wss vx cv cA wcel vx cv csn
      cA wss vx cv csn cA cB cun wss vx cv cA snssi vx cv csn cA cB ssun3 syl
      vy cv cB wcel vy cv csn cB wss vy cv csn cA cB cun wss vy cv cB snssi vy
      cv csn cB cA ssun4 syl anim12i vx cv csn vy cv csn cA cB cun unss sylib
      syl5eqss vx cv vy cv cpr cA cB cun vx vy zfpair2 elpw sylibr jca vx cv
      csn vx cv vy cv cpr cpr cA cB cun cpw cpw wcel vx cv csn vx cv vy cv cpr
      cpr cA cB cun cpw wss vx cv vy cv cop cA cB cun cpw cpw wcel vx cv csn cA
      cB cun cpw wcel vx cv vy cv cpr cA cB cun cpw wcel wa vx cv csn vx cv vy
      cv cpr cpr cA cB cun cpw vx cv csn vx cv vy cv cpr prex elpw vx cv vy cv
      cop vx cv csn vx cv vy cv cpr cpr cA cB cun cpw cpw vx cv vy cv vx vex vy
      vex dfop eleq1i vx cv csn vx cv vy cv cpr cA cB cun cpw vx cv snex vx vy
      zfpair2 prss 3bitr4ri sylib sylbi relssi $.
  $}

  $( The double class union of a cross product is included in the union of its
     arguments.  (Contributed by NM, 16-Sep-2006.) $)
  unixpss $p |- U. U. ( A X. B ) C_ ( A u. B ) $=
    cA cB cxp cuni cuni cA cB cun cpw cuni cA cB cun cA cB cxp cuni cA cB cun
    cpw wss cA cB cxp cuni cuni cA cB cun cpw cuni wss cA cB cxp cuni cA cB cun
    cpw cpw cuni cA cB cun cpw cA cB cxp cA cB cun cpw cpw wss cA cB cxp cuni
    cA cB cun cpw cpw cuni wss cA cB xpsspw cA cB cxp cA cB cun cpw cpw uniss
    ax-mp cA cB cun cpw unipw sseqtri cA cB cxp cuni cA cB cun cpw uniss ax-mp
    cA cB cun unipw sseqtri $.

  $( The cross product of two sets is a set.  Proposition 6.2 of
     [TakeutiZaring] p. 23.  See also ~ xpexgALT .  (Contributed by NM,
     14-Aug-1994.) $)
  xpexg $p |- ( ( A e. V /\ B e. W ) -> ( A X. B ) e. _V ) $=
    cA cV wcel cB cW wcel wa cA cB cxp cA cB cun cpw cpw wss cA cB cun cpw cpw
    cvv wcel cA cB cxp cvv wcel cA cB xpsspw cA cV wcel cB cW wcel wa cA cB cun
    cvv wcel cA cB cun cpw cvv wcel cA cB cun cpw cpw cvv wcel cA cB cV cW
    unexg cA cB cun cvv pwexg cA cB cun cpw cvv pwexg 3syl cA cB cxp cA cB cun
    cpw cpw cvv ssexg sylancr $.

  ${
    xpex.1 $e |- A e. _V $.
    xpex.2 $e |- B e. _V $.
    $( The cross product of two sets is a set.  Proposition 6.2 of
       [TakeutiZaring] p. 23.  (Contributed by NM, 14-Aug-1994.) $)
    xpex $p |- ( A X. B ) e. _V $=
      cA cvv wcel cB cvv wcel cA cB cxp cvv wcel xpex.1 xpex.2 cA cB cvv cvv
      xpexg mp2an $.
  $}

  $( The union of two relations is a relation.  Compare Exercise 5 of
     [TakeutiZaring] p. 25.  (Contributed by NM, 12-Aug-1994.) $)
  relun $p |- ( Rel ( A u. B ) <-> ( Rel A /\ Rel B ) ) $=
    cA cvv cvv cxp wss cB cvv cvv cxp wss wa cA cB cun cvv cvv cxp wss cA wrel
    cB wrel wa cA cB cun wrel cA cB cvv cvv cxp unss cA wrel cA cvv cvv cxp wss
    cB wrel cB cvv cvv cxp wss cA df-rel cB df-rel anbi12i cA cB cun df-rel
    3bitr4ri $.

  $( The intersection with a relation is a relation.  (Contributed by NM,
     16-Aug-1994.) $)
  relin1 $p |- ( Rel A -> Rel ( A i^i B ) ) $=
    cA cB cin cA wss cA wrel cA cB cin wrel wi cA cB inss1 cA cB cin cA relss
    ax-mp $.

  $( The intersection with a relation is a relation.  (Contributed by NM,
     17-Jan-2006.) $)
  relin2 $p |- ( Rel B -> Rel ( A i^i B ) ) $=
    cA cB cin cB wss cB wrel cA cB cin wrel wi cA cB inss2 cA cB cin cB relss
    ax-mp $.

  $( A difference cutting down a relation is a relation.  (Contributed by NM,
     31-Mar-1998.) $)
  reldif $p |- ( Rel A -> Rel ( A \ B ) ) $=
    cA cB cdif cA wss cA wrel cA cB cdif wrel wi cA cB difss cA cB cdif cA
    relss ax-mp $.

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( An indexed union is a relation iff each member of its indexed family is
       a relation.  (Contributed by NM, 19-Dec-2008.) $)
    reliun $p |- ( Rel U_ x e. A B <-> A. x e. A Rel B ) $=
      vx cA cB ciun wrel vy cv cB wcel vx cA wrex vy cab wrel vy cv cB wcel vx
      cA wrex vy cab cvv cvv cxp wss cB wrel vx cA wral vx cA cB ciun vy cv cB
      wcel vx cA wrex vy cab vx vy cA cB df-iun releqi vy cv cB wcel vx cA wrex
      vy cab df-rel vy cv cB wcel vx cA wrex vy cab cvv cvv cxp wss vy cv cB
      wcel vx cA wrex vy cv cvv cvv cxp wcel wi vy wal cB wrel vx cA wral vy cv
      cB wcel vx cA wrex vy cvv cvv cxp abss cB wrel vx cA wral vy cv cB wcel
      vy cv cvv cvv cxp wcel wi vy wal vx cA wral vy cv cB wcel vy cv cvv cvv
      cxp wcel wi vx cA wral vy wal vy cv cB wcel vx cA wrex vy cv cvv cvv cxp
      wcel wi vy wal cB wrel vy cv cB wcel vy cv cvv cvv cxp wcel wi vy wal vx
      cA cB wrel cB cvv cvv cxp wss vy cv cB wcel vy cv cvv cvv cxp wcel wi vy
      wal cB df-rel vy cB cvv cvv cxp dfss2 bitri ralbii vy cv cB wcel vy cv
      cvv cvv cxp wcel wi vx vy cA ralcom4 vy cv cB wcel vy cv cvv cvv cxp wcel
      wi vx cA wral vy cv cB wcel vx cA wrex vy cv cvv cvv cxp wcel wi vy vy cv
      cB wcel vy cv cvv cvv cxp wcel vx cA r19.23v albii 3bitri bitr4i 3bitri
      $.
  $}

  $( An indexed intersection is a relation if at least one of the member of the
     indexed family is a relation.  (Contributed by NM, 8-Mar-2014.) $)
  reliin $p |- ( E. x e. A Rel B -> Rel |^|_ x e. A B ) $=
    cB cvv cvv cxp wss vx cA wrex vx cA cB ciin cvv cvv cxp wss cB wrel vx cA
    wrex vx cA cB ciin wrel vx cA cB cvv cvv cxp iinss cB wrel cB cvv cvv cxp
    wss vx cA cB df-rel rexbii vx cA cB ciin df-rel 3imtr4i $.

  ${
    $d x A $.
    $( The union of a class is a relation iff any member is a relation.
       Exercise 6 of [TakeutiZaring] p. 25 and its converse.  (Contributed by
       NM, 13-Aug-2004.) $)
    reluni $p |- ( Rel U. A <-> A. x e. A Rel x ) $=
      cA cuni wrel vx cA vx cv ciun wrel vx cv wrel vx cA wral cA cuni vx cA vx
      cv ciun vx cA uniiun releqi vx cA vx cv reliun bitri $.

    $( The intersection of a class is a relation if at least one member is a
       relation.  (Contributed by NM, 8-Mar-2014.) $)
    relint $p |- ( E. x e. A Rel x -> Rel |^| A ) $=
      vx cv wrel vx cA wrex vx cA vx cv ciin wrel cA cint wrel vx cA vx cv
      reliin cA cint vx cA vx cv ciin vx cA intiin releqi sylibr $.
  $}

  $( The empty set is a relation.  (Contributed by NM, 26-Apr-1998.) $)
  rel0 $p |- Rel (/) $=
    c0 wrel c0 cvv cvv cxp wss cvv cvv cxp 0ss c0 df-rel mpbir $.

  ${
    $d ph z $.  $d u v x z $.  $d u v y z $.
    relopabi.1 $e |- A = { <. x , y >. | ph } $.
    $( A class of ordered pairs is a relation.  (Contributed by Mario Carneiro,
       21-Dec-2013.) $)
    relopabi $p |- Rel A $=
      cA wrel cA cvv cvv cxp wss cA vz cv vx cv vy cv cop wceq wph wa vy wex vx
      wex vz cab cvv cvv cxp cA wph vx vy copab vz cv vx cv vy cv cop wceq wph
      wa vy wex vx wex vz cab relopabi.1 wph vx vy vz df-opab eqtri vz cv vx cv
      vy cv cop wceq wph wa vy wex vx wex vz cvv cvv cxp vz cv vx cv vy cv cop
      wceq wph wa vz cv cvv cvv cxp wcel vx vy vz cv vx cv vy cv cop wceq vz cv
      cvv cvv cxp wcel wph vz cv vx cv vy cv cop wceq vz cv cvv cvv cxp wcel vx
      cv vy cv cop cvv cvv cxp wcel vx cv vy cv vx vex vy vex opelvv vz cv vx
      cv vy cv cop cvv cvv cxp eleq1 mpbiri adantr exlimivv abssi eqsstri cA
      df-rel mpbir $.
  $}

  $( A class of ordered pairs is a relation.  (Contributed by NM, 8-Mar-1995.)
     (Unnecessary distinct variable restrictions were removed by Alan Sare,
     9-Jul-2013.)  (Proof shortened by Mario Carneiro, 21-Dec-2013.) $)
  relopab $p |- Rel { <. x , y >. | ph } $=
    wph vx vy wph vx vy copab wph vx vy copab eqid relopabi $.

  ${
    $d w x y z A $.  $d x y B $.  $d x y C $.  $d x y D $.  $d ph z w $.
    $d ps z w $.
    $( The identity relation is a relation.  Part of Exercise 4.12(p) of
       [Mendelson] p. 235.  (Contributed by NM, 26-Apr-1998.)  (Revised by
       Mario Carneiro, 21-Dec-2013.) $)
    reli $p |- Rel _I $=
      vx cv vy cv wceq vx vy cid vx vy dfid3 relopabi $.

    $( The membership relation is a relation.  (Contributed by NM,
       26-Apr-1998.)  (Revised by Mario Carneiro, 21-Dec-2013.) $)
    rele $p |- Rel _E $=
      vx cv vy cv wcel vx vy cep vx vy df-eprel relopabi $.

    $( A relation expressed as an ordered pair abstraction.  (Contributed by
       NM, 11-Dec-2006.) $)
    opabid2 $p |- ( Rel A -> { <. x , y >. | <. x , y >. e. A } = A ) $=
      cA wrel vx cv vy cv cop cA wcel vx vy copab cA wceq vz cv vw cv cop vx cv
      vy cv cop cA wcel vx vy copab wcel vz cv vw cv cop cA wcel wb vw wal vz
      wal vz cv vw cv cop vx cv vy cv cop cA wcel vx vy copab wcel vz cv vw cv
      cop cA wcel wb vz vw vx cv vy cv cop cA wcel vz cv vy cv cop cA wcel vz
      cv vw cv cop cA wcel vx vy vz cv vw cv vz vex vw vex vx cv vz cv wceq vx
      cv vy cv cop vz cv vy cv cop cA vx cv vz cv vy cv opeq1 eleq1d vy cv vw
      cv wceq vz cv vy cv cop vz cv vw cv cop cA vy cv vw cv vz cv opeq2 eleq1d
      opelopab gen2 vx cv vy cv cop cA wcel vx vy copab wrel cA wrel vx cv vy
      cv cop cA wcel vx vy copab cA wceq vz cv vw cv cop vx cv vy cv cop cA
      wcel vx vy copab wcel vz cv vw cv cop cA wcel wb vw wal vz wal wb vx cv
      vy cv cop cA wcel vx vy relopab vz vw vx cv vy cv cop cA wcel vx vy copab
      cA eqrel mpan mpbiri $.

    $( Intersection of two ordered pair class abstractions.  (Contributed by
       NM, 30-Sep-2002.) $)
    inopab $p |- ( { <. x , y >. | ph } i^i { <. x , y >. | ps } ) =
               { <. x , y >. | ( ph /\ ps ) } $=
      vz vw wph vx vy copab wps vx vy copab cin wph wps wa vx vy copab wph vx
      vy copab wrel wph vx vy copab wps vx vy copab cin wrel wph vx vy relopab
      wph vx vy copab wps vx vy copab relin1 ax-mp wph wps wa vx vy relopab vz
      cv vw cv cop wph vx vy copab wcel vz cv vw cv cop wps vx vy copab wcel wa
      wph wps wa vx vz wsb vy vw wsb vz cv vw cv cop wph vx vy copab wps vx vy
      copab cin wcel vz cv vw cv cop wph wps wa vx vy copab wcel wph vx vz wsb
      wps vx vz wsb wa vy vw wsb wph vx vz wsb vy vw wsb wps vx vz wsb vy vw
      wsb wa wph wps wa vx vz wsb vy vw wsb vz cv vw cv cop wph vx vy copab
      wcel vz cv vw cv cop wps vx vy copab wcel wa wph vx vz wsb wps vx vz wsb
      vy vw sban wph wps wa vx vz wsb wph vx vz wsb wps vx vz wsb wa vy vw wph
      wps vx vz sban sbbii vz cv vw cv cop wph vx vy copab wcel wph vx vz wsb
      vy vw wsb vz cv vw cv cop wps vx vy copab wcel wps vx vz wsb vy vw wsb
      wph vx vy vz vw opelopabsbOLD wps vx vy vz vw opelopabsbOLD anbi12i
      3bitr4ri vz cv vw cv cop wph vx vy copab wps vx vy copab elin wph wps wa
      vx vy vz vw opelopabsbOLD 3bitr4i eqrelriiv $.

    $( The difference of two ordered-pair abstractions.  (Contributed by Stefan
       O'Rear, 17-Jan-2015.) $)
    difopab $p |- ( { <. x , y >. | ph } \ { <. x , y >. | ps } ) =
        { <. x , y >. | ( ph /\ -. ps ) } $=
      vz vw wph vx vy copab wps vx vy copab cdif wph wps wn wa vx vy copab wph
      vx vy copab wrel wph vx vy copab wps vx vy copab cdif wrel wph vx vy
      relopab wph vx vy copab wps vx vy copab reldif ax-mp wph wps wn wa vx vy
      relopab vz cv vw cv cop wph vx vy copab wcel vz cv vw cv cop wps vx vy
      copab wcel wn wa wph wps wn wa vy vw cv wsbc vx vz cv wsbc vz cv vw cv
      cop wph vx vy copab wps vx vy copab cdif wcel vz cv vw cv cop wph wps wn
      wa vx vy copab wcel wph vy vw cv wsbc wps wn vy vw cv wsbc wa vx vz cv
      wsbc wph vy vw cv wsbc vx vz cv wsbc wps wn vy vw cv wsbc vx vz cv wsbc
      wa wph wps wn wa vy vw cv wsbc vx vz cv wsbc vz cv vw cv cop wph vx vy
      copab wcel vz cv vw cv cop wps vx vy copab wcel wn wa wph vy vw cv wsbc
      wps wn vy vw cv wsbc vx vz cv sbcan wph wps wn wa vy vw cv wsbc wph vy vw
      cv wsbc wps wn vy vw cv wsbc wa vx vz cv wph wps wn vy vw cv sbcan sbcbii
      vz cv vw cv cop wph vx vy copab wcel wph vy vw cv wsbc vx vz cv wsbc vz
      cv vw cv cop wps vx vy copab wcel wn wps wn vy vw cv wsbc vx vz cv wsbc
      wph vx vy vz cv vw cv opelopabsb wps vy vw cv wsbc wn vx vz cv wsbc wps
      vy vw cv wsbc vx vz cv wsbc wn wps wn vy vw cv wsbc vx vz cv wsbc vz cv
      vw cv cop wps vx vy copab wcel wn vz cv cvv wcel wps vy vw cv wsbc wn vx
      vz cv wsbc wps vy vw cv wsbc vx vz cv wsbc wn wb vz vex wps vy vw cv wsbc
      vx vz cv cvv sbcng ax-mp wps wn vy vw cv wsbc wps vy vw cv wsbc wn vx vz
      cv vw cv cvv wcel wps wn vy vw cv wsbc wps vy vw cv wsbc wn wb vw vex wps
      vy vw cv cvv sbcng ax-mp sbcbii vz cv vw cv cop wps vx vy copab wcel wps
      vy vw cv wsbc vx vz cv wsbc wps vx vy vz cv vw cv opelopabsb notbii
      3bitr4ri anbi12i 3bitr4ri vz cv vw cv cop wph vx vy copab wps vx vy copab
      eldif wph wps wn wa vx vy vz cv vw cv opelopabsb 3bitr4i eqrelriiv $.

    $( The intersection of two cross products.  Exercise 9 of [TakeutiZaring]
       p. 25.  (Contributed by NM, 3-Aug-1994.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    inxp $p |- ( ( A X. B ) i^i ( C X. D ) ) =
                   ( ( A i^i C ) X. ( B i^i D ) ) $=
      vx cv cA wcel vy cv cB wcel wa vx vy copab vx cv cC wcel vy cv cD wcel wa
      vx vy copab cin vx cv cA cC cin wcel vy cv cB cD cin wcel wa vx vy copab
      cA cB cxp cC cD cxp cin cA cC cin cB cD cin cxp vx cv cA wcel vy cv cB
      wcel wa vx vy copab vx cv cC wcel vy cv cD wcel wa vx vy copab cin vx cv
      cA wcel vy cv cB wcel wa vx cv cC wcel vy cv cD wcel wa wa vx vy copab vx
      cv cA cC cin wcel vy cv cB cD cin wcel wa vx vy copab vx cv cA wcel vy cv
      cB wcel wa vx cv cC wcel vy cv cD wcel wa vx vy inopab vx cv cA wcel vy
      cv cB wcel wa vx cv cC wcel vy cv cD wcel wa wa vx cv cA cC cin wcel vy
      cv cB cD cin wcel wa vx vy vx cv cA wcel vy cv cB wcel wa vx cv cC wcel
      vy cv cD wcel wa wa vx cv cA wcel vx cv cC wcel wa vy cv cB wcel vy cv cD
      wcel wa wa vx cv cA cC cin wcel vy cv cB cD cin wcel wa vx cv cA wcel vy
      cv cB wcel vx cv cC wcel vy cv cD wcel an4 vx cv cA cC cin wcel vx cv cA
      wcel vx cv cC wcel wa vy cv cB cD cin wcel vy cv cB wcel vy cv cD wcel wa
      vx cv cA cC elin vy cv cB cD elin anbi12i bitr4i opabbii eqtri cA cB cxp
      vx cv cA wcel vy cv cB wcel wa vx vy copab cC cD cxp vx cv cC wcel vy cv
      cD wcel wa vx vy copab vx vy cA cB df-xp vx vy cC cD df-xp ineq12i vx vy
      cA cC cin cB cD cin df-xp 3eqtr4i $.

    $( Distributive law for cross product over intersection.  Theorem 102 of
       [Suppes] p. 52.  (Contributed by NM, 26-Sep-2004.) $)
    xpindi $p |- ( A X. ( B i^i C ) ) = ( ( A X. B ) i^i ( A X. C ) ) $=
      cA cB cxp cA cC cxp cin cA cA cin cB cC cin cxp cA cB cC cin cxp cA cB cA
      cC inxp cA cA cin cA cB cC cin cA inidm xpeq1i eqtr2i $.

    $( Distributive law for cross product over intersection.  Similar to
       Theorem 102 of [Suppes] p. 52.  (Contributed by NM, 26-Sep-2004.) $)
    xpindir $p |- ( ( A i^i B ) X. C ) = ( ( A X. C ) i^i ( B X. C ) ) $=
      cA cC cxp cB cC cxp cin cA cB cin cC cC cin cxp cA cB cin cC cxp cA cC cB
      cC inxp cC cC cin cC cA cB cin cC inidm xpeq2i eqtr2i $.
  $}

  ${
    $d x y z A $.  $d x y z C $.  $d y z B $.
    $( Distributive law for cross product over indexed intersection.
       (Contributed by Mario Carneiro, 21-Mar-2015.) $)
    xpiindi $p |- ( A =/= (/) ->
      ( C X. |^|_ x e. A B ) = |^|_ x e. A ( C X. B ) ) $=
      cC vx cA cB ciin cxp wrel vx cA cC cB cxp ciin wrel wa cA c0 wne cC vx cA
      cB ciin cxp vx cA cC cB cxp ciin wceq cA c0 wne vx cA cC cB cxp ciin wrel
      cC vx cA cB ciin cxp wrel cA c0 wne cC cB cxp wrel vx cA wrex vx cA cC cB
      cxp ciin wrel cA c0 wne cC cB cxp wrel vx cA wral cC cB cxp wrel vx cA
      wrex cC cB cxp wrel vx cA cC cB relxp rgenw cC cB cxp wrel vx cA r19.2z
      mpan2 vx cA cC cB cxp reliin syl cC vx cA cB ciin relxp jctil cA c0 wne
      vy vz cC vx cA cB ciin cxp vx cA cC cB cxp ciin cA c0 wne vy cv cC wcel
      vz cv vx cA cB ciin wcel wa vy cv vz cv cop cC cB cxp wcel vx cA wral vy
      cv vz cv cop cC vx cA cB ciin cxp wcel vy cv vz cv cop vx cA cC cB cxp
      ciin wcel cA c0 wne vy cv cC wcel vz cv cB wcel vx cA wral wa vy cv cC
      wcel vz cv cB wcel wa vx cA wral vy cv cC wcel vz cv vx cA cB ciin wcel
      wa vy cv vz cv cop cC cB cxp wcel vx cA wral cA c0 wne vy cv cC wcel vz
      cv cB wcel wa vx cA wral vy cv cC wcel vz cv cB wcel vx cA wral wa vy cv
      cC wcel vz cv cB wcel vx cA r19.28zv bicomd vz cv vx cA cB ciin wcel vz
      cv cB wcel vx cA wral vy cv cC wcel vz cv cvv wcel vz cv vx cA cB ciin
      wcel vz cv cB wcel vx cA wral wb vz vex vx vz cv cA cB cvv eliin ax-mp
      anbi2i vy cv vz cv cop cC cB cxp wcel vy cv cC wcel vz cv cB wcel wa vx
      cA vy cv vz cv cC cB opelxp ralbii 3bitr4g vy cv vz cv cC vx cA cB ciin
      opelxp vy cv vz cv cop cvv wcel vy cv vz cv cop vx cA cC cB cxp ciin wcel
      vy cv vz cv cop cC cB cxp wcel vx cA wral wb vy cv vz cv opex vx vy cv vz
      cv cop cA cC cB cxp cvv eliin ax-mp 3bitr4g eqrelrdv2 mpancom $.

    $( Distributive law for cross product over relativized indexed
       intersection.  (Contributed by Mario Carneiro, 21-Mar-2015.) $)
    xpriindi $p |- ( C X. ( D i^i |^|_ x e. A B ) ) =
      ( ( C X. D ) i^i |^|_ x e. A ( C X. B ) ) $=
      cC cD vx cA cB ciin cin cxp cC cD cxp vx cA cC cB cxp ciin cin wceq cA c0
      cA c0 wceq cC cD vx cA cB ciin cin cxp cC cD cxp cC cD cxp vx cA cC cB
      cxp ciin cin cA c0 wceq cD vx cA cB ciin cin cD cC cA c0 wceq cD vx cA cB
      ciin cin cD cvv cin cD cA c0 wceq vx cA cB ciin cvv cD cA c0 wceq vx cA
      cB ciin vx c0 cB ciin cvv vx cA c0 cB iineq1 vx cB 0iin syl6eq ineq2d cD
      inv1 syl6eq xpeq2d cA c0 wceq cC cD cxp vx cA cC cB cxp ciin cin cC cD
      cxp cvv cin cC cD cxp cA c0 wceq vx cA cC cB cxp ciin cvv cC cD cxp cA c0
      wceq vx cA cC cB cxp ciin vx c0 cC cB cxp ciin cvv vx cA c0 cC cB cxp
      iineq1 vx cC cB cxp 0iin syl6eq ineq2d cC cD cxp inv1 syl6eq eqtr4d cA c0
      wne cC cD vx cA cB ciin cin cxp cC cD cxp cC vx cA cB ciin cxp cin cC cD
      cxp vx cA cC cB cxp ciin cin cC cD vx cA cB ciin xpindi cA c0 wne cC vx
      cA cB ciin cxp vx cA cC cB cxp ciin cC cD cxp vx cA cB cC xpiindi ineq2d
      syl5eq pm2.61ine $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y C $.  $d x y D $.  $d x E $.  $d x V $.
    $( Membership in a union of cross products.  Analogue of ~ elxp for
       nonconstant ` B ( x ) ` .  (Contributed by Mario Carneiro,
       29-Dec-2014.) $)
    eliunxp $p |- ( C e. U_ x e. A ( { x } X. B ) <->
      E. x E. y ( C = <. x , y >. /\ ( x e. A /\ y e. B ) ) ) $=
      cC vx cA vx cv csn cB cxp ciun wcel cC vx cv vy cv cop wceq vy wex vx wex
      cC vx cA vx cv csn cB cxp ciun wcel wa cC vx cv vy cv cop wceq vy wex cC
      vx cA vx cv csn cB cxp ciun wcel wa vx wex cC vx cv vy cv cop wceq vx cv
      cA wcel vy cv cB wcel wa wa vy wex vx wex cC vx cA vx cv csn cB cxp ciun
      wcel cC vx cv vy cv cop wceq vy wex vx wex vx cA vx cv csn cB cxp ciun
      wrel cC vx cA vx cv csn cB cxp ciun wcel cC vx cv vy cv cop wceq vy wex
      vx wex vx cA vx cv csn cB cxp ciun wrel vx cv csn cB cxp wrel vx cA wral
      vx cv csn cB cxp wrel vx cA vx cv csn cB relxp rgenw vx cA vx cv csn cB
      cxp reliun mpbir vx vy cC vx cA vx cv csn cB cxp ciun elrel mpan pm4.71ri
      cC vx cv vy cv cop wceq vy wex cC vx cA vx cv csn cB cxp ciun wcel vx vx
      cC vx cA vx cv csn cB cxp ciun vx cA vx cv csn cB cxp nfiu1 nfel2 19.41
      cC vx cv vy cv cop wceq vy wex cC vx cA vx cv csn cB cxp ciun wcel wa cC
      vx cv vy cv cop wceq vx cv cA wcel vy cv cB wcel wa wa vy wex vx cC vx cv
      vy cv cop wceq vy wex cC vx cA vx cv csn cB cxp ciun wcel wa cC vx cv vy
      cv cop wceq cC vx cA vx cv csn cB cxp ciun wcel wa vy wex cC vx cv vy cv
      cop wceq vx cv cA wcel vy cv cB wcel wa wa vy wex cC vx cv vy cv cop wceq
      cC vx cA vx cv csn cB cxp ciun wcel vy 19.41v cC vx cv vy cv cop wceq cC
      vx cA vx cv csn cB cxp ciun wcel wa cC vx cv vy cv cop wceq vx cv cA wcel
      vy cv cB wcel wa wa vy cC vx cv vy cv cop wceq cC vx cA vx cv csn cB cxp
      ciun wcel vx cv cA wcel vy cv cB wcel wa cC vx cv vy cv cop wceq cC vx cA
      vx cv csn cB cxp ciun wcel vx cv vy cv cop vx cA vx cv csn cB cxp ciun
      wcel vx cv cA wcel vy cv cB wcel wa cC vx cv vy cv cop vx cA vx cv csn cB
      cxp ciun eleq1 vx cA cB vy cv opeliunxp syl6bb pm5.32i exbii bitr3i exbii
      3bitr2i $.

    $d x A $.
    opeliunxp2.1 $e |- ( x = C -> B = E ) $.
    $( Membership in a union of cross products.  (Contributed by Mario
       Carneiro, 14-Feb-2015.) $)
    opeliunxp2 $p |- ( <. C , D >. e. U_ x e. A ( { x } X. B ) <->
      ( C e. A /\ D e. E ) ) $=
      cC cD cop vx cA vx cv csn cB cxp ciun wcel cC cvv wcel cC cA wcel cD cE
      wcel wa cC cD cop vx cA vx cv csn cB cxp ciun wcel cC cD vx cA vx cv csn
      cB cxp ciun wbr cC cvv wcel cC cD vx cA vx cv csn cB cxp ciun df-br cC cD
      vx cA vx cv csn cB cxp ciun vx cA vx cv csn cB cxp ciun wrel vx cv csn cB
      cxp wrel vx cA wral vx cv csn cB cxp wrel vx cA vx cv csn cB relxp rgenw
      vx cA vx cv csn cB cxp reliun mpbir brrelexi sylbir cC cA wcel cC cvv
      wcel cD cE wcel cC cA elex adantr vx cv cD cop vx cA vx cv csn cB cxp
      ciun wcel vx cv cA wcel cD cB wcel wa wb cC cD cop vx cA vx cv csn cB cxp
      ciun wcel cC cA wcel cD cE wcel wa wb vx cC cvv vx cC nfcv cC cD cop vx
      cA vx cv csn cB cxp ciun wcel cC cA wcel cD cE wcel wa vx vx cC cD cop vx
      cA vx cv csn cB cxp ciun vx cA vx cv csn cB cxp nfiu1 nfel2 cC cA wcel cD
      cE wcel wa vx nfv nfbi vx cv cC wceq vx cv cD cop vx cA vx cv csn cB cxp
      ciun wcel cC cD cop vx cA vx cv csn cB cxp ciun wcel vx cv cA wcel cD cB
      wcel wa cC cA wcel cD cE wcel wa vx cv cC wceq vx cv cD cop cC cD cop vx
      cA vx cv csn cB cxp ciun vx cv cC cD opeq1 eleq1d vx cv cC wceq vx cv cA
      wcel cC cA wcel cD cB wcel cD cE wcel vx cv cC cA eleq1 vx cv cC wceq cB
      cE cD opeliunxp2.1 eleq2d anbi12d bibi12d vx cA cB cD opeliunxp vtoclgf
      pm5.21nii $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d y z ph $.  $d x ps $.
    ralxp.1 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
    $( Write a double restricted quantification as one universal quantifier.
       In this version of ~ ralxp , ` B ( y ) ` is not assumed to be constant.
       (Contributed by Mario Carneiro, 29-Dec-2014.) $)
    raliunxp $p |- ( A. x e. U_ y e. A ( { y } X. B ) ph <->
      A. y e. A A. z e. B ps ) $=
      vx cv vy cA vy cv csn cB cxp ciun wcel wph wi vx wal vy cv cA wcel vz cv
      cB wcel wa wps wi vz wal vy wal wph vx vy cA vy cv csn cB cxp ciun wral
      wps vz cB wral vy cA wral vx cv vy cA vy cv csn cB cxp ciun wcel wph wi
      vx wal vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wa wa wph
      wi vz wal vy wal vx wal vy cv cA wcel vz cv cB wcel wa wps wi vz wal vy
      wal vx cv vy cA vy cv csn cB cxp ciun wcel wph wi vx cv vy cv vz cv cop
      wceq vy cv cA wcel vz cv cB wcel wa wa wph wi vz wal vy wal vx vx cv vy
      cA vy cv csn cB cxp ciun wcel wph wi vx cv vy cv vz cv cop wceq vy cv cA
      wcel vz cv cB wcel wa wa vz wex vy wex wph wi vx cv vy cv vz cv cop wceq
      vy cv cA wcel vz cv cB wcel wa wa wph wi vz wal vy wal vx cv vy cA vy cv
      csn cB cxp ciun wcel vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB
      wcel wa wa vz wex vy wex wph vy vz cA cB vx cv eliunxp imbi1i vx cv vy cv
      vz cv cop wceq vy cv cA wcel vz cv cB wcel wa wa wph vy vz 19.23vv bitr4i
      albii vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wa wa wph wi
      vz wal vy wal vx wal vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB
      wcel wa wa wph wi vx wal vz wal vy wal vy cv cA wcel vz cv cB wcel wa wps
      wi vz wal vy wal vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel
      wa wa wph wi vx vy vz alrot3 vx cv vy cv vz cv cop wceq vy cv cA wcel vz
      cv cB wcel wa wa wph wi vx wal vy cv cA wcel vz cv cB wcel wa wps wi vy
      vz vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wa wa wph wi vx
      wal vx cv vy cv vz cv cop wceq vy cv cA wcel vz cv cB wcel wa wph wi wi
      vx wal vy cv cA wcel vz cv cB wcel wa wps wi vx cv vy cv vz cv cop wceq
      vy cv cA wcel vz cv cB wcel wa wa wph wi vx cv vy cv vz cv cop wceq vy cv
      cA wcel vz cv cB wcel wa wph wi wi vx vx cv vy cv vz cv cop wceq vy cv cA
      wcel vz cv cB wcel wa wph impexp albii vy cv cA wcel vz cv cB wcel wa wph
      wi vy cv cA wcel vz cv cB wcel wa wps wi vx vy cv vz cv cop vy cv vz cv
      opex vx cv vy cv vz cv cop wceq wph wps vy cv cA wcel vz cv cB wcel wa
      ralxp.1 imbi2d ceqsalv bitri 2albii bitri bitri wph vx vy cA vy cv csn cB
      cxp ciun df-ral wps vy vz cA cB r2al 3bitr4i $.

    $( Write a double restricted quantification as one universal quantifier.
       In this version of ~ rexxp , ` B ( y ) ` is not assumed to be constant.
       (Contributed by Mario Carneiro, 14-Feb-2015.) $)
    rexiunxp $p |- ( E. x e. U_ y e. A ( { y } X. B ) ph <->
      E. y e. A E. z e. B ps ) $=
      wph wn vx vy cA vy cv csn cB cxp ciun wral wn wps vz cB wrex wn vy cA
      wral wn wph vx vy cA vy cv csn cB cxp ciun wrex wps vz cB wrex vy cA wrex
      wph wn vx vy cA vy cv csn cB cxp ciun wral wps vz cB wrex wn vy cA wral
      wph wn vx vy cA vy cv csn cB cxp ciun wral wps wn vz cB wral vy cA wral
      wps vz cB wrex wn vy cA wral wph wn wps wn vx vy vz cA cB vx cv vy cv vz
      cv cop wceq wph wps ralxp.1 notbid raliunxp wps wn vz cB wral wps vz cB
      wrex wn vy cA wps vz cB ralnex ralbii bitri notbii wph vx vy cA vy cv csn
      cB cxp ciun dfrex2 wps vz cB wrex vy cA dfrex2 3bitr4i $.

    $d y B $.
    $( Universal quantification restricted to a cross product is equivalent to
       a double restricted quantification.  The hypothesis specifies an
       implicit substitution.  (Contributed by NM, 7-Feb-2004.)  (Revised by
       Mario Carneiro, 29-Dec-2014.) $)
    ralxp $p |- ( A. x e. ( A X. B ) ph <-> A. y e. A A. z e. B ps ) $=
      wph vx cA cB cxp wral wph vx vy cA vy cv csn cB cxp ciun wral wps vz cB
      wral vy cA wral wph vx vy cA vy cv csn cB cxp ciun cA cB cxp vy cA cB
      iunxpconst raleqi wph wps vx vy vz cA cB ralxp.1 raliunxp bitr3i $.

    $( Existential quantification restricted to a cross product is equivalent
       to a double restricted quantification.  (Contributed by NM,
       11-Nov-1995.)  (Revised by Mario Carneiro, 14-Feb-2015.) $)
    rexxp $p |- ( E. x e. ( A X. B ) ph <-> E. y e. A E. z e. B ps ) $=
      wph vx cA cB cxp wrex wph vx vy cA vy cv csn cB cxp ciun wrex wps vz cB
      wrex vy cA wrex wph vx vy cA vy cv csn cB cxp ciun cA cB cxp vy cA cB
      iunxpconst rexeqi wph wps vx vy vz cA cB ralxp.1 rexiunxp bitr3i $.
  $}

  ${
    $d x A $.
    $( Disjoint union is a subset of a cross product.  (Contributed by Stefan
       O'Rear, 21-Nov-2014.) $)
    djussxp $p |- U_ x e. A ( { x } X. B ) C_ ( A X. _V ) $=
      vx cA vx cv csn cB cxp ciun cA cvv cxp wss vx cv csn cB cxp cA cvv cxp
      wss vx cA vx cA vx cv csn cB cxp cA cvv cxp iunss vx cv cA wcel vx cv csn
      cA wss cB cvv wss vx cv csn cB cxp cA cvv cxp wss vx cv cA snssi cB ssv
      vx cv csn cA cB cvv xpss12 sylancl mprgbir $.
  $}

  ${
    $d u v w x y A $.  $d u v w x y z B $.  $d u v w ph $.  $d u v w ps $.
    ralxpf.1 $e |- F/ y ph $.
    ralxpf.2 $e |- F/ z ph $.
    ralxpf.3 $e |- F/ x ps $.
    ralxpf.4 $e |- ( x = <. y , z >. -> ( ph <-> ps ) ) $.
    $( Version of ~ ralxp with bound-variable hypotheses.  (Contributed by NM,
       18-Aug-2006.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    ralxpf $p |- ( A. x e. ( A X. B ) ph <-> A. y e. A A. z e. B ps ) $=
      wph vx cA cB cxp wral wph vx vw wsb vw cA cB cxp wral wps vz cB wral vy
      cA wral wph vx vw cA cB cxp cbvralsv wps vy vu wsb vz cB wral vu cA wral
      wps vy vu wsb vz vv wsb vv cB wral vu cA wral wps vz cB wral vy cA wral
      wph vx vw wsb vw cA cB cxp wral wps vy vu wsb vz cB wral wps vy vu wsb vz
      vv wsb vv cB wral vu cA wps vy vu wsb vz vv cB cbvralsv ralbii wps vz cB
      wral wps vy vu wsb vz cB wral vy vu cA wps vz cB wral vu nfv wps vy vu
      wsb vy vz cB vy cB nfcv wps vy vu nfs1v nfral vy cv vu cv wceq wps wps vy
      vu wsb vz cB wps vy vu sbequ12 ralbidv cbvral wph vx vw wsb wps vy vu wsb
      vz vv wsb vw vu vv cA cB vw cv vu cv vv cv cop wceq vw cv vy cv vz cv cop
      wceq vy cv vz cv cop vu cv vv cv cop wceq wa vz wex vy wex wph vx vw wsb
      wps vy vu wsb vz vv wsb wb vy vz vw cv vu cv vv cv vu vex vv vex eqvinop
      vw cv vy cv vz cv cop wceq vy cv vz cv cop vu cv vv cv cop wceq wa vz wex
      wph vx vw wsb wps vy vu wsb vz vv wsb wb vy wph vx vw wsb wps vy vu wsb
      vz vv wsb vy wph vx vw vy ralxpf.1 nfsb wps vy vu wsb vz vv vy wps vy vu
      nfs1v nfsb nfbi vw cv vy cv vz cv cop wceq vy cv vz cv cop vu cv vv cv
      cop wceq wa wph vx vw wsb wps vy vu wsb vz vv wsb wb vz wph vx vw wsb wps
      vy vu wsb vz vv wsb vz wph vx vw vz ralxpf.2 nfsb wps vy vu wsb vz vv
      nfs1v nfbi vw cv vy cv vz cv cop wceq wph vx vw wsb wps vy cv vz cv cop
      vu cv vv cv cop wceq wps vy vu wsb vz vv wsb wph wps vx vw vy cv vz cv
      cop ralxpf.3 ralxpf.4 sbhypf vy cv vz cv cop vu cv vv cv cop wceq vy cv
      vu cv wceq vz cv vv cv wceq wa wps wps vy vu wsb vz vv wsb wb vy cv vz cv
      vu cv vv cv vy vex vz vex opth vy cv vu cv wceq wps wps vy vu wsb vz cv
      vv cv wceq wps vy vu wsb vz vv wsb wps vy vu sbequ12 wps vy vu wsb vz vv
      sbequ12 sylan9bb sylbi sylan9bb exlimi exlimi sylbi ralxp 3bitr4ri bitri
      $.

    $( Version of ~ rexxp with bound-variable hypotheses.  (Contributed by NM,
       19-Dec-2008.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    rexxpf $p |- ( E. x e. ( A X. B ) ph <-> E. y e. A E. z e. B ps ) $=
      wph wn vx cA cB cxp wral wn wps vz cB wrex wn vy cA wral wn wph vx cA cB
      cxp wrex wps vz cB wrex vy cA wrex wph wn vx cA cB cxp wral wps vz cB
      wrex wn vy cA wral wph wn vx cA cB cxp wral wps wn vz cB wral vy cA wral
      wps vz cB wrex wn vy cA wral wph wn wps wn vx vy vz cA cB wph vy ralxpf.1
      nfn wph vz ralxpf.2 nfn wps vx ralxpf.3 nfn vx cv vy cv vz cv cop wceq
      wph wps ralxpf.4 notbid ralxpf wps wn vz cB wral wps vz cB wrex wn vy cA
      wps vz cB ralnex ralbii bitri notbii wph vx cA cB cxp dfrex2 wps vz cB
      wrex vy cA dfrex2 3bitr4i $.
  $}

  ${
    $d w x y A $.  $d w x y z B $.  $d w C $.  $d w D $.
    iunxpf.1 $e |- F/_ y C $.
    iunxpf.2 $e |- F/_ z C $.
    iunxpf.3 $e |- F/_ x D $.
    iunxpf.4 $e |- ( x = <. y , z >. -> C = D ) $.
    $( Indexed union on a cross product is equals a double indexed union.  The
       hypothesis specifies an implicit substitution.  (Contributed by NM,
       19-Dec-2008.) $)
    iunxpf $p |- U_ x e. ( A X. B ) C = U_ y e. A U_ z e. B D $=
      vw vx cA cB cxp cC ciun vy cA vz cB cD ciun ciun vw cv cC wcel vx cA cB
      cxp wrex vw cv cD wcel vz cB wrex vy cA wrex vw cv vx cA cB cxp cC ciun
      wcel vw cv vy cA vz cB cD ciun ciun wcel vw cv cC wcel vw cv cD wcel vx
      vy vz cA cB vy vw cC iunxpf.1 nfcri vz vw cC iunxpf.2 nfcri vx vw cD
      iunxpf.3 nfcri vx cv vy cv vz cv cop wceq cC cD vw cv iunxpf.4 eleq2d
      rexxpf vx vw cv cA cB cxp cC eliun vw cv vy cA vz cB cD ciun ciun wcel vw
      cv vz cB cD ciun wcel vy cA wrex vw cv cD wcel vz cB wrex vy cA wrex vy
      vw cv cA vz cB cD ciun eliun vw cv vz cB cD ciun wcel vw cv cD wcel vz cB
      wrex vy cA vz vw cv cB cD eliun rexbii bitri 3bitr4i eqriv $.
  $}

  ${
    $d x y A $.  $d x y ph $.
    opabbi2dv.1 $e |- Rel A $.
    opabbi2dv.3 $e |- ( ph -> ( <. x , y >. e. A <-> ps ) ) $.
    $( Deduce equality of a relation and an ordered-pair class builder.
       Compare ~ abbi2dv .  (Contributed by NM, 24-Feb-2014.) $)
    opabbi2dv $p |- ( ph -> A = { <. x , y >. | ps } ) $=
      wph cA vx cv vy cv cop cA wcel vx vy copab wps vx vy copab cA wrel vx cv
      vy cv cop cA wcel vx vy copab cA wceq opabbi2dv.1 vx vy cA opabid2 ax-mp
      wph vx cv vy cv cop cA wcel wps vx vy opabbi2dv.3 opabbidv syl5eqr $.
  $}

  ${
    $d v w x y z A $.  $d v w x y z B $.
    relop.1 $e |- A e. _V $.
    relop.2 $e |- B e. _V $.
    $( A necessary and sufficient condition for a Kuratowski ordered pair to be
       a relation.  (Contributed by NM, 3-Jun-2008.) $)
    relop $p |- ( Rel <. A , B >.
             <-> E. x E. y ( A = { x } /\ B = { x , y } ) ) $=
      cA cB cop wrel cA cB cop cvv cvv cxp wss cA vx cv csn wceq cB vx cv vy cv
      cpr wceq wa vy wex vx wex cA cB cop df-rel cA cB cop cvv cvv cxp wss cA
      vx cv csn wceq cB vx cv vy cv cpr wceq wa vy wex vx wex cA cB cop cvv cvv
      cxp wss vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz
      wal vz cv cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz
      wal wa cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vy wex vx wex cA cB
      cop cvv cvv cxp wss vz cv cA cB cop wcel vz cv cvv cvv cxp wcel wi vz wal
      vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal vz
      cv cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal wa
      vz cA cB cop cvv cvv cxp dfss2 vz cv cA cB cop wcel vz cv cvv cvv cxp
      wcel wi vz wal vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex
      wi vz cv cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi wa vz
      wal vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal
      vz cv cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal
      wa vz cv cA cB cop wcel vz cv cvv cvv cxp wcel wi vz cv cA csn wceq vz cv
      vx cv vy cv cop wceq vy wex vx wex wi vz cv cA cB cpr wceq vz cv vx cv vy
      cv cop wceq vy wex vx wex wi wa vz vz cv cA cB cop wcel vz cv cvv cvv cxp
      wcel wi vz cv cA csn wceq vz cv cA cB cpr wceq wo vz cv vx cv vy cv cop
      wceq vy wex vx wex wi vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex
      vx wex wi vz cv cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex
      wi wa vz cv cA cB cop wcel vz cv cA csn wceq vz cv cA cB cpr wceq wo vz
      cv cvv cvv cxp wcel vz cv vx cv vy cv cop wceq vy wex vx wex vz cv cA cB
      vz vex relop.1 relop.2 elop vx vy vz cv elvv imbi12i vz cv cA csn wceq vz
      cv vx cv vy cv cop wceq vy wex vx wex vz cv cA cB cpr wceq jaob bitri
      albii vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz cv
      cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz 19.26 bitri
      bitri vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz
      wal cA vw cv csn wceq vw wex cA cB cpr vx cv vy cv cop wceq vy wex vx wex
      cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vy wex vx wex vz cv cA cB
      cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal vz cv cA csn
      wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal cA csn cA csn
      wceq vx cv vy cv wceq cA vx cv csn wceq wa vy wex vx wex wi cA vw cv csn
      wceq vw wex vz cv cA csn wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi
      cA csn cA csn wceq vx cv vy cv wceq cA vx cv csn wceq wa vy wex vx wex wi
      vz cA csn cA snex vz cv cA csn wceq vz cv cA csn wceq cA csn cA csn wceq
      vz cv vx cv vy cv cop wceq vy wex vx wex vx cv vy cv wceq cA vx cv csn
      wceq wa vy wex vx wex vz cv cA csn cA csn eqeq1 vz cv cA csn wceq vz cv
      vx cv vy cv cop wceq vx cv vy cv wceq cA vx cv csn wceq wa vx vy vz cv cA
      csn wceq vz cv vx cv vy cv cop wceq cA csn vx cv vy cv cop wceq vx cv vy
      cv wceq cA vx cv csn wceq wa vz cv cA csn vx cv vy cv cop eqeq1 cA csn vx
      cv vy cv cop wceq vx cv vy cv cop cA csn wceq vx cv vy cv wceq cA vx cv
      csn wceq wa cA csn vx cv vy cv cop eqcom vx cv vy cv cA vx vex vy vex
      relop.1 opeqsn bitri syl6bb 2exbidv imbi12d spcv cA vw cv csn wceq vw wex
      cA vx cv csn wceq vx wex vx cv vy cv wceq cA vx cv csn wceq wa vy wex vx
      wex cA csn cA csn wceq vx cv vy cv wceq cA vx cv csn wceq wa vy wex vx
      wex wi cA vw cv csn wceq cA vx cv csn wceq vw vx vw cv vx cv wceq vw cv
      csn vx cv csn cA vw cv vx cv sneq eqeq2d cbvexv vx cv vy cv wceq cA vx cv
      csn wceq wa vy wex cA vx cv csn wceq vx vx cv vy cv wceq cA vx cv csn
      wceq wa vy wex vx cv vy cv wceq vy wex cA vx cv csn wceq vy cv vx cv wceq
      vy wex vx cv vy cv wceq vy wex vy vx a9ev vy cv vx cv wceq vx cv vy cv
      wceq vy vy vx equcom exbii mpbi vx cv vy cv wceq cA vx cv csn wceq vy
      19.41v mpbiran exbii cA csn cA csn wceq vx cv vy cv wceq cA vx cv csn
      wceq wa vy wex vx wex cA csn eqid a1bi 3bitr2ri sylib vz cv cA cB cpr
      wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi vz wal cA cB cpr cA cB
      cpr wceq cA cB cpr vx cv vy cv cop wceq vy wex vx wex cA cB cpr eqid vz
      cv cA cB cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex wi cA cB cpr
      cA cB cpr wceq cA cB cpr vx cv vy cv cop wceq vy wex vx wex wi vz cA cB
      cpr cA cB prex vz cv cA cB cpr wceq vz cv cA cB cpr wceq cA cB cpr cA cB
      cpr wceq vz cv vx cv vy cv cop wceq vy wex vx wex cA cB cpr vx cv vy cv
      cop wceq vy wex vx wex vz cv cA cB cpr cA cB cpr eqeq1 vz cv cA cB cpr
      wceq vz cv vx cv vy cv cop wceq cA cB cpr vx cv vy cv cop wceq vx vy vz
      cv cA cB cpr vx cv vy cv cop eqeq1 2exbidv imbi12d spcv mpi cA vw cv csn
      wceq vw wex cA cB cpr vx cv vy cv cop wceq vy wex vx wex cA vx cv csn
      wceq cB vx cv vy cv cpr wceq wa vy wex vx wex cA vw cv csn wceq cA cB cpr
      vx cv vy cv cop wceq vy wex vx wex cA vx cv csn wceq cB vx cv vy cv cpr
      wceq wa vy wex vx wex wi vw cA vw cv csn wceq cA cB cpr vx cv vy cv cop
      wceq cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vx vy cA cB cpr vx cv
      vy cv cop wceq cA vx cv csn wceq cB vx cv vy cv cpr wceq wa cA vx cv vy
      cv cpr wceq cB vx cv csn wceq wa wo cA vw cv csn wceq cA vx cv csn wceq
      cB vx cv vy cv cpr wceq wa cA cB cpr vx cv vy cv cop wceq vx cv vy cv cop
      cA cB cpr wceq cA vx cv csn wceq cB vx cv vy cv cpr wceq wa cA vx cv vy
      cv cpr wceq cB vx cv csn wceq wa wo cA cB cpr vx cv vy cv cop eqcom vx cv
      vy cv cA cB vx vex vy vex relop.1 relop.2 opeqpr bitri cA vw cv csn wceq
      cA vx cv csn wceq cB vx cv vy cv cpr wceq wa cA vx cv csn wceq cB vx cv
      vy cv cpr wceq wa cA vx cv vy cv cpr wceq cB vx cv csn wceq wa cA vw cv
      csn wceq cA vx cv csn wceq cB vx cv vy cv cpr wceq wa idd cA vw cv csn
      wceq cA vx cv vy cv cpr wceq cB vx cv csn wceq cA vx cv csn wceq cB vx cv
      vy cv cpr wceq wa cA vx cv vy cv cpr wceq cA vw cv csn wceq cB vx cv csn
      wceq cA vx cv csn wceq cB vx cv vy cv cpr wceq wa wi cA vx cv vy cv cpr
      wceq cA vw cv csn wceq wa vx cv vy cv wceq cB vx cv csn wceq cA vx cv csn
      wceq cB vx cv vy cv cpr wceq wa wi cA vx cv vy cv cpr wceq cA vw cv csn
      wceq wa vx cv vy cv cpr vw cv csn wceq vx cv vy cv wceq cA vx cv vy cv
      cpr vw cv csn eqtr2 vx cv vy cv cpr vw cv csn wceq vx cv vy cv wceq vy cv
      vw cv wceq vx cv vy cv vw cv vx vex vy vex vw vex preqsn simplbi syl cA
      vx cv vy cv cpr wceq vx cv vy cv wceq cB vx cv csn wceq cA vx cv csn wceq
      cB vx cv vy cv cpr wceq wa wi wi cA vw cv csn wceq vx cv vy cv wceq cA vx
      cv vy cv cpr wceq cB vx cv csn wceq cA vx cv csn wceq cB vx cv vy cv cpr
      wceq wa wi vx cv vy cv wceq cA vx cv vy cv cpr wceq cB vx cv csn wceq cA
      vx cv csn wceq cB vx cv vy cv cpr wceq wa vx cv vy cv wceq cA vx cv vy cv
      cpr wceq cB vx cv csn wceq wa cA vx cv csn wceq cB vx cv vy cv cpr wceq
      wa vx cv vy cv wceq cA vx cv vy cv cpr wceq cA vx cv csn wceq cB vx cv
      csn wceq cB vx cv vy cv cpr wceq vx cv vy cv wceq vx cv vy cv cpr vx cv
      csn cA vx cv vy cv wceq vx cv csn vx cv vx cv cpr vx cv vy cv cpr vx cv
      dfsn2 vx cv vy cv vx cv preq2 syl5req eqeq2d vx cv vy cv wceq vx cv csn
      vx cv vy cv cpr cB vx cv vy cv wceq vx cv csn vx cv vx cv cpr vx cv vy cv
      cpr vx cv dfsn2 vx cv vy cv vx cv preq2 syl5eq eqeq2d anbi12d biimpd
      exp3a com12 adantr mpd expcom imp3a jaod syl5bi 2eximdv exlimiv imp
      syl2an sylbi cA vx cv csn wceq cB vx cv vy cv cpr wceq wa cA cB cop cvv
      cvv cxp wss vx vy cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vz cA cB
      cop cvv cvv cxp cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vz cv cA csn
      wceq vz cv cA cB cpr wceq wo vz cv vw cv vv cv cop wceq vv wex vw wex vz
      cv cA cB cop wcel vz cv cvv cvv cxp wcel cA vx cv csn wceq cB vx cv vy cv
      cpr wceq wa vz cv cA csn wceq vz cv cA cB cpr wceq wo vz cv vw cv vv cv
      cop wceq vv wex vw wex cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vz cv
      cA csn wceq vz cv vw cv vv cv cop wceq vv wex vw wex vz cv cA cB cpr wceq
      cA vx cv csn wceq vz cv cA csn wceq vz cv vw cv vv cv cop wceq vv wex vw
      wex cB vx cv vy cv cpr wceq cA vx cv csn wceq vz cv cA csn wceq wa vz cv
      vx cv vx cv cop wceq vz cv vw cv vv cv cop wceq vv wex vw wex cA vx cv
      csn wceq vz cv cA csn wceq wa vz cv cA csn vx cv vx cv cop cA vx cv csn
      wceq vz cv cA csn wceq simpr cA vx cv csn wceq vx cv vx cv cop cA csn
      wceq vz cv cA csn wceq cA vx cv csn wceq vx cv vx cv wceq cA vx cv csn
      wceq wa vx cv vx cv cop cA csn wceq cA vx cv csn wceq vx cv vx cv wceq vx
      equid jctl vx cv vx cv cA vx vex vx vex relop.1 opeqsn sylibr adantr
      eqtr4d vz cv vw cv vv cv cop wceq vz cv vx cv vx cv cop wceq vw vv vx cv
      vx cv vx vex vx vex vw cv vx cv wceq vv cv vx cv wceq wa vw cv vv cv cop
      vx cv vx cv cop vz cv vw cv vv cv vx cv vx cv opeq12 eqeq2d spc2ev syl
      adantlr cA vx cv csn wceq cB vx cv vy cv cpr wceq wa vz cv cA cB cpr wceq
      wa vz cv vx cv vy cv cop wceq vz cv vw cv vv cv cop wceq vv wex vw wex cA
      vx cv csn wceq cB vx cv vy cv cpr wceq wa vz cv cA cB cpr wceq wa vz cv
      vx cv csn vx cv vy cv cpr cpr vx cv vy cv cop cA vx cv csn wceq cB vx cv
      vy cv cpr wceq wa vz cv cA cB cpr wceq vz cv vx cv csn vx cv vy cv cpr
      cpr wceq cA vx cv csn wceq cB vx cv vy cv cpr wceq wa cA cB cpr vx cv csn
      vx cv vy cv cpr cpr vz cv cA cB vx cv csn vx cv vy cv cpr preq12 eqeq2d
      biimpa vx cv vy cv vx vex vy vex dfop syl6eqr vz cv vw cv vv cv cop wceq
      vz cv vx cv vy cv cop wceq vw vv vx cv vy cv vx vex vy vex vw cv vx cv
      wceq vv cv vy cv wceq wa vw cv vv cv cop vx cv vy cv cop vz cv vw cv vv
      cv vx cv vy cv opeq12 eqeq2d spc2ev syl jaodan ex vz cv cA cB vz vex
      relop.1 relop.2 elop vw vv vz cv elvv 3imtr4g ssrdv exlimivv impbii bitri
      $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( For sets, the identity relation is the same as equality.  (Contributed
       by NM, 30-Apr-2004.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    ideqg $p |- ( B e. V -> ( A _I B <-> A = B ) ) $=
      cB cV wcel cA cB cid wbr cA cB wceq cA cvv wcel cB cV wcel wa cB cV wcel
      cA cB cid wbr wa cA cvv wcel cB cV wcel cA cB cid wbr cA cvv wcel cB cV
      wcel cA cB cid reli brrelexi adantl cB cV wcel cA cB cid wbr simpl jca cB
      cV wcel cA cB wceq wa cA cvv wcel cB cV wcel cB cV wcel cA cB wceq wa cA
      cV wcel cA cvv wcel cA cB wceq cA cV wcel cB cV wcel cA cB cV eleq1
      biimparc cA cV elex syl cB cV wcel cA cB wceq simpl jca vx cv vy cv wceq
      cA vy cv wceq cA cB wceq vx vy cA cB cvv cV cid vx cv cA vy cv eqeq1 vy
      cv cB cA eqeq2 vx vy df-id brabg pm5.21nd $.
  $}

  ${
    ideq.1 $e |- B e. _V $.
    $( For sets, the identity relation is the same as equality.  (Contributed
       by NM, 13-Aug-1995.) $)
    ideq $p |- ( A _I B <-> A = B ) $=
      cB cvv wcel cA cB cid wbr cA cB wceq wb ideq.1 cA cB cvv ideqg ax-mp $.
  $}

  ${
    $d x A $.
    $( A set is identical to itself.  (Contributed by NM, 28-May-2008.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    ididg $p |- ( A e. V -> A _I A ) $=
      cA cV wcel cA cA cid wbr cA cA wceq cA eqid cA cA cV ideqg mpbiri $.
  $}

  $( Two ways of expressing set existence.  (Contributed by NM, 16-Feb-2008.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) $)
  issetid $p |- ( A e. _V <-> A _I A ) $=
    cA cvv wcel cA cA cid wbr cA cvv ididg cA cA cid reli brrelexi impbii $.

  ${
    $d A x y z $.  $d B x y z $.  $d C x y z $.
    $( Subclass theorem for composition.  (Contributed by FL, 30-Dec-2010.) $)
    coss1 $p |- ( A C_ B -> ( A o. C ) C_ ( B o. C ) ) $=
      cA cB wss vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex vx vz copab vx
      cv vy cv cC wbr vy cv vz cv cB wbr wa vy wex vx vz copab cA cC ccom cB cC
      ccom cA cB wss vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex vx cv vy
      cv cC wbr vy cv vz cv cB wbr wa vy wex vx vz cA cB wss vx cv vy cv cC wbr
      vy cv vz cv cA wbr wa vx cv vy cv cC wbr vy cv vz cv cB wbr wa vy cA cB
      wss vy cv vz cv cA wbr vy cv vz cv cB wbr vx cv vy cv cC wbr cA cB wss cA
      cB vy cv vz cv cA cB wss id ssbrd anim2d eximdv ssopab2dv vx vz vy cA cC
      df-co vx vz vy cB cC df-co 3sstr4g $.

    $( Subclass theorem for composition.  (Contributed by NM, 5-Apr-2013.) $)
    coss2 $p |- ( A C_ B -> ( C o. A ) C_ ( C o. B ) ) $=
      cA cB wss vx cv vy cv cA wbr vy cv vz cv cC wbr wa vy wex vx vz copab vx
      cv vy cv cB wbr vy cv vz cv cC wbr wa vy wex vx vz copab cC cA ccom cC cB
      ccom cA cB wss vx cv vy cv cA wbr vy cv vz cv cC wbr wa vy wex vx cv vy
      cv cB wbr vy cv vz cv cC wbr wa vy wex vx vz cA cB wss vx cv vy cv cA wbr
      vy cv vz cv cC wbr wa vx cv vy cv cB wbr vy cv vz cv cC wbr wa vy cA cB
      wss vx cv vy cv cA wbr vx cv vy cv cB wbr vy cv vz cv cC wbr cA cB wss cA
      cB vx cv vy cv cA cB wss id ssbrd anim1d eximdv ssopab2dv vx vz vy cC cA
      df-co vx vz vy cC cB df-co 3sstr4g $.
  $}

  $( Equality theorem for composition of two classes.  (Contributed by NM,
     3-Jan-1997.) $)
  coeq1 $p |- ( A = B -> ( A o. C ) = ( B o. C ) ) $=
    cA cB wss cB cA wss wa cA cC ccom cB cC ccom wss cB cC ccom cA cC ccom wss
    wa cA cB wceq cA cC ccom cB cC ccom wceq cA cB wss cA cC ccom cB cC ccom
    wss cB cA wss cB cC ccom cA cC ccom wss cA cB cC coss1 cB cA cC coss1
    anim12i cA cB eqss cA cC ccom cB cC ccom eqss 3imtr4i $.

  $( Equality theorem for composition of two classes.  (Contributed by NM,
     3-Jan-1997.) $)
  coeq2 $p |- ( A = B -> ( C o. A ) = ( C o. B ) ) $=
    cA cB wss cB cA wss wa cC cA ccom cC cB ccom wss cC cB ccom cC cA ccom wss
    wa cA cB wceq cC cA ccom cC cB ccom wceq cA cB wss cC cA ccom cC cB ccom
    wss cB cA wss cC cB ccom cC cA ccom wss cA cB cC coss2 cB cA cC coss2
    anim12i cA cB eqss cC cA ccom cC cB ccom eqss 3imtr4i $.

  ${
    coeq1i.1 $e |- A = B $.
    $( Equality inference for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
    coeq1i $p |- ( A o. C ) = ( B o. C ) $=
      cA cB wceq cA cC ccom cB cC ccom wceq coeq1i.1 cA cB cC coeq1 ax-mp $.

    $( Equality inference for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
    coeq2i $p |- ( C o. A ) = ( C o. B ) $=
      cA cB wceq cC cA ccom cC cB ccom wceq coeq1i.1 cA cB cC coeq2 ax-mp $.
  $}

  ${
    coeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
    coeq1d $p |- ( ph -> ( A o. C ) = ( B o. C ) ) $=
      wph cA cB wceq cA cC ccom cB cC ccom wceq coeq1d.1 cA cB cC coeq1 syl $.

    $( Equality deduction for composition of two classes.  (Contributed by NM,
       16-Nov-2000.) $)
    coeq2d $p |- ( ph -> ( C o. A ) = ( C o. B ) ) $=
      wph cA cB wceq cC cA ccom cC cB ccom wceq coeq1d.1 cA cB cC coeq2 syl $.
  $}

  ${
    coeq12i.1 $e |- A = B $.
    coeq12i.2 $e |- C = D $.
    $( Equality inference for composition of two classes.  (Contributed by FL,
       7-Jun-2012.) $)
    coeq12i $p |- ( A o. C ) = ( B o. D ) $=
      cA cC ccom cB cC ccom cB cD ccom cA cB cC coeq12i.1 coeq1i cC cD cB
      coeq12i.2 coeq2i eqtri $.
  $}

  ${
    coeq12d.1 $e |- ( ph -> A = B ) $.
    coeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for composition of two classes.  (Contributed by FL,
       7-Jun-2012.) $)
    coeq12d $p |- ( ph -> ( A o. C ) = ( B o. D ) ) $=
      wph cA cC ccom cB cC ccom cB cD ccom wph cA cB cC coeq12d.1 coeq1d wph cC
      cD cB coeq12d.2 coeq2d eqtrd $.
  $}

  ${
    $d w x y z $.  $d y z w A $.  $d y z w B $.
    nfco.1 $e |- F/_ x A $.
    nfco.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for function value.  (Contributed by
       NM, 1-Sep-1999.) $)
    nfco $p |- F/_ x ( A o. B ) $=
      vx cA cB ccom vy cv vw cv cB wbr vw cv vz cv cA wbr wa vw wex vy vz copab
      vy vz vw cA cB df-co vy cv vw cv cB wbr vw cv vz cv cA wbr wa vw wex vy
      vz vx vy cv vw cv cB wbr vw cv vz cv cA wbr wa vx vw vy cv vw cv cB wbr
      vw cv vz cv cA wbr vx vx vy cv vw cv cB vx vy cv nfcv nfco.2 vx vw cv
      nfcv nfbr vx vw cv vz cv cA vx vw cv nfcv nfco.1 vx vz cv nfcv nfbr nfan
      nfex nfopab nfcxfr $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.
    $( Ordered pair membership in a composition.  (Contributed by NM,
       24-Feb-2015.) $)
    brcog $p |- ( ( A e. V /\ B e. W ) -> ( A ( C o. D ) B <->
                   E. x ( A D x /\ x C B ) ) ) $=
      vy cv vx cv cD wbr vx cv vz cv cC wbr wa vx wex cA vx cv cD wbr vx cv cB
      cC wbr wa vx wex vy vz cA cB cC cD ccom cV cW vy cv cA wceq vz cv cB wceq
      wa vy cv vx cv cD wbr vx cv vz cv cC wbr wa cA vx cv cD wbr vx cv cB cC
      wbr wa vx vy cv cA wceq vy cv vx cv cD wbr cA vx cv cD wbr vz cv cB wceq
      vx cv vz cv cC wbr vx cv cB cC wbr vy cv cA vx cv cD breq1 vz cv cB vx cv
      cC breq2 bi2anan9 exbidv vy vz vx cC cD df-co brabga $.

    $( Ordered pair membership in a composition.  (Contributed by NM,
       27-Jan-1997.)  (Revised by Mario Carneiro, 24-Feb-2015.) $)
    opelco2g $p |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. ( C o. D ) <->
                   E. x ( <. A , x >. e. D /\ <. x , B >. e. C ) ) ) $=
      cA cV wcel cB cW wcel wa cA cB cC cD ccom wbr cA vx cv cD wbr vx cv cB cC
      wbr wa vx wex cA cB cop cC cD ccom wcel cA vx cv cop cD wcel vx cv cB cop
      cC wcel wa vx wex vx cA cB cC cD cV cW brcog cA cB cC cD ccom df-br cA vx
      cv cD wbr vx cv cB cC wbr wa cA vx cv cop cD wcel vx cv cB cop cC wcel wa
      vx cA vx cv cD wbr cA vx cv cop cD wcel vx cv cB cC wbr vx cv cB cop cC
      wcel cA vx cv cD df-br vx cv cB cC df-br anbi12i exbii 3bitr3g $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z C $.  $d x y z D $.
    opelco.1 $e |- A e. _V $.
    opelco.2 $e |- B e. _V $.
    $( Binary relation on a composition.  (Contributed by NM, 21-Sep-2004.)
       (Revised by Mario Carneiro, 24-Feb-2015.) $)
    brco $p |- ( A ( C o. D ) B <-> E. x ( A D x /\ x C B ) ) $=
      cA cvv wcel cB cvv wcel cA cB cC cD ccom wbr cA vx cv cD wbr vx cv cB cC
      wbr wa vx wex wb opelco.1 opelco.2 vx cA cB cC cD cvv cvv brcog mp2an $.

    $( Ordered pair membership in a composition.  (Contributed by NM,
       27-Dec-1996.)  (Revised by Mario Carneiro, 24-Feb-2015.) $)
    opelco $p |- ( <. A , B >. e. ( C o. D ) <-> E. x ( A D x /\ x C B ) ) $=
      cA cB cop cC cD ccom wcel cA cB cC cD ccom wbr cA vx cv cD wbr vx cv cB
      cC wbr wa vx wex cA cB cC cD ccom df-br vx cA cB cC cD opelco.1 opelco.2
      brco bitr3i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Subset theorem for converse.  (Contributed by NM, 22-Mar-1998.) $)
    cnvss $p |- ( A C_ B -> `' A C_ `' B ) $=
      cA cB wss vy cv vx cv cA wbr vx vy copab vy cv vx cv cB wbr vx vy copab
      cA ccnv cB ccnv cA cB wss vy cv vx cv cA wbr vy cv vx cv cB wbr vx vy cA
      cB wss vy cv vx cv cop cA wcel vy cv vx cv cop cB wcel vy cv vx cv cA wbr
      vy cv vx cv cB wbr cA cB vy cv vx cv cop ssel vy cv vx cv cA df-br vy cv
      vx cv cB df-br 3imtr4g ssopab2dv vx vy cA df-cnv vx vy cB df-cnv 3sstr4g
      $.
  $}

  $( Equality theorem for converse.  (Contributed by NM, 13-Aug-1995.) $)
  cnveq $p |- ( A = B -> `' A = `' B ) $=
    cA cB wss cB cA wss wa cA ccnv cB ccnv wss cB ccnv cA ccnv wss wa cA cB
    wceq cA ccnv cB ccnv wceq cA cB wss cA ccnv cB ccnv wss cB cA wss cB ccnv
    cA ccnv wss cA cB cnvss cB cA cnvss anim12i cA cB eqss cA ccnv cB ccnv eqss
    3imtr4i $.

  ${
    cnveqi.1 $e |- A = B $.
    $( Equality inference for converse.  (Contributed by NM, 23-Dec-2008.) $)
    cnveqi $p |- `' A = `' B $=
      cA cB wceq cA ccnv cB ccnv wceq cnveqi.1 cA cB cnveq ax-mp $.
  $}

  ${
    cnveqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for converse.  (Contributed by NM, 6-Dec-2013.) $)
    cnveqd $p |- ( ph -> `' A = `' B ) $=
      wph cA cB wceq cA ccnv cB ccnv wceq cnveqd.1 cA cB cnveq syl $.
  $}

  ${
    $d x y A $.  $d x y R $.
    $( Membership in a converse.  Equation 5 of [Suppes] p. 62.  (Contributed
       by NM, 24-Mar-1998.) $)
    elcnv $p |- ( A e. `' R <-> E. x E. y ( A = <. x , y >. /\ y R x ) ) $=
      cA cR ccnv wcel cA vy cv vx cv cR wbr vx vy copab wcel cA vx cv vy cv cop
      wceq vy cv vx cv cR wbr wa vy wex vx wex cR ccnv vy cv vx cv cR wbr vx vy
      copab cA vx vy cR df-cnv eleq2i vy cv vx cv cR wbr vx vy cA elopab bitri
      $.

    $( Membership in a converse.  Equation 5 of [Suppes] p. 62.  (Contributed
       by NM, 11-Aug-2004.) $)
    elcnv2 $p |- ( A e. `' R <->
                 E. x E. y ( A = <. x , y >. /\ <. y , x >. e. R ) ) $=
      cA cR ccnv wcel cA vx cv vy cv cop wceq vy cv vx cv cR wbr wa vy wex vx
      wex cA vx cv vy cv cop wceq vy cv vx cv cop cR wcel wa vy wex vx wex vx
      vy cA cR elcnv cA vx cv vy cv cop wceq vy cv vx cv cR wbr wa cA vx cv vy
      cv cop wceq vy cv vx cv cop cR wcel wa vx vy vy cv vx cv cR wbr vy cv vx
      cv cop cR wcel cA vx cv vy cv cop wceq vy cv vx cv cR df-br anbi2i 2exbii
      bitri $.
  $}

  ${
    $d y z A $.  $d x y z $.
    nfcnv.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for converse.  (Contributed by NM,
       31-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nfcnv $p |- F/_ x `' A $=
      vx cA ccnv vz cv vy cv cA wbr vy vz copab vy vz cA df-cnv vz cv vy cv cA
      wbr vy vz vx vx vz cv vy cv cA vx vz cv nfcv nfcnv.1 vx vy cv nfcv nfbr
      nfopab nfcxfr $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y R $.
    $( Ordered-pair membership in converse.  (Contributed by NM, 13-May-1999.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    opelcnvg $p |- ( ( A e. C /\ B e. D ) ->
                     ( <. A , B >. e. `' R <-> <. B , A >. e. R ) ) $=
      cA cC wcel cB cD wcel wa cA cB cR ccnv wbr cB cA cR wbr cA cB cop cR ccnv
      wcel cB cA cop cR wcel vy cv vx cv cR wbr vy cv cA cR wbr cB cA cR wbr vx
      vy cA cB cC cD cR ccnv vx cv cA vy cv cR breq2 vy cv cB cA cR breq1 vx vy
      cR df-cnv brabg cA cB cR ccnv df-br cB cA cR df-br 3bitr3g $.
  $}

  $( The converse of a binary relation swaps arguments.  Theorem 11 of [Suppes]
     p. 61.  (Contributed by NM, 10-Oct-2005.) $)
  brcnvg $p |- ( ( A e. C /\ B e. D ) -> ( A `' R B <-> B R A ) ) $=
    cA cC wcel cB cD wcel wa cA cB cop cR ccnv wcel cB cA cop cR wcel cA cB cR
    ccnv wbr cB cA cR wbr cA cB cC cD cR opelcnvg cA cB cR ccnv df-br cB cA cR
    df-br 3bitr4g $.

  ${
    opelcnv.1 $e |- A e. _V $.
    opelcnv.2 $e |- B e. _V $.
    $( Ordered-pair membership in converse.  (Contributed by NM,
       13-Aug-1995.) $)
    opelcnv $p |- ( <. A , B >. e. `' R <-> <. B , A >. e. R ) $=
      cA cvv wcel cB cvv wcel cA cB cop cR ccnv wcel cB cA cop cR wcel wb
      opelcnv.1 opelcnv.2 cA cB cvv cvv cR opelcnvg mp2an $.

    $( The converse of a binary relation swaps arguments.  Theorem 11 of
       [Suppes] p. 61.  (Contributed by NM, 13-Aug-1995.) $)
    brcnv $p |- ( A `' R B <-> B R A ) $=
      cA cvv wcel cB cvv wcel cA cB cR ccnv wbr cB cA cR wbr wb opelcnv.1
      opelcnv.2 cA cB cvv cvv cR brcnvg mp2an $.
  $}

  ${
    $d x y z A $.  $d x y z B $.
    $( Distributive law of converse over class composition.  Theorem 26 of
       [Suppes] p. 64.  (Contributed by NM, 19-Mar-1998.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
    cnvco $p |- `' ( A o. B ) = ( `' B o. `' A ) $=
      vx cv vy cv cA cB ccom wbr vy vx copab vy cv vz cv cA ccnv wbr vz cv vx
      cv cB ccnv wbr wa vz wex vy vx copab cA cB ccom ccnv cB ccnv cA ccnv ccom
      vx cv vy cv cA cB ccom wbr vy cv vz cv cA ccnv wbr vz cv vx cv cB ccnv
      wbr wa vz wex vy vx vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vz cv
      vy cv cA wbr vx cv vz cv cB wbr wa vz wex vx cv vy cv cA cB ccom wbr vy
      cv vz cv cA ccnv wbr vz cv vx cv cB ccnv wbr wa vz wex vx cv vz cv cB wbr
      vz cv vy cv cA wbr vz exancom vz vx cv vy cv cA cB vx vex vy vex brco vy
      cv vz cv cA ccnv wbr vz cv vx cv cB ccnv wbr wa vz cv vy cv cA wbr vx cv
      vz cv cB wbr wa vz vy cv vz cv cA ccnv wbr vz cv vy cv cA wbr vz cv vx cv
      cB ccnv wbr vx cv vz cv cB wbr vy cv vz cv cA vy vex vz vex brcnv vz cv
      vx cv cB vz vex vx vex brcnv anbi12i exbii 3bitr4i opabbii vy vx cA cB
      ccom df-cnv vy vx vz cB ccnv cA ccnv df-co 3eqtr4i $.
  $}

  ${
    $d x y z w A $.
    $( The converse of a class union is the (indexed) union of the converses of
       its members.  (Contributed by NM, 11-Aug-2004.) $)
    cnvuni $p |- `' U. A = U_ x e. A `' x $=
      vy cA cuni ccnv vx cA vx cv ccnv ciun vy cv cA cuni ccnv wcel vy cv vx cv
      ccnv wcel vx cA wrex vy cv vx cA vx cv ccnv ciun wcel vy cv cA cuni ccnv
      wcel vy cv vz cv vw cv cop wceq vw cv vz cv cop cA cuni wcel wa vw wex vz
      wex vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa vx cA wrex
      vw wex vz wex vy cv vx cv ccnv wcel vx cA wrex vz vw vy cv cA cuni elcnv2
      vy cv vz cv vw cv cop wceq vw cv vz cv cop cA cuni wcel wa vy cv vz cv vw
      cv cop wceq vw cv vz cv cop vx cv wcel wa vx cA wrex vz vw vy cv vz cv vw
      cv cop wceq vw cv vz cv cop cA cuni wcel wa vy cv vz cv vw cv cop wceq vw
      cv vz cv cop vx cv wcel vx cA wrex wa vy cv vz cv vw cv cop wceq vw cv vz
      cv cop vx cv wcel wa vx cA wrex vw cv vz cv cop cA cuni wcel vw cv vz cv
      cop vx cv wcel vx cA wrex vy cv vz cv vw cv cop wceq vx vw cv vz cv cop
      cA eluni2 anbi2i vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel vx
      cA r19.42v bitr4i 2exbii vy cv vx cv ccnv wcel vx cA wrex vy cv vz cv vw
      cv cop wceq vw cv vz cv cop vx cv wcel wa vw wex vz wex vx cA wrex vy cv
      vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa vw wex vx cA wrex vz
      wex vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa vx cA wrex
      vw wex vz wex vy cv vx cv ccnv wcel vy cv vz cv vw cv cop wceq vw cv vz
      cv cop vx cv wcel wa vw wex vz wex vx cA vz vw vy cv vx cv elcnv2 rexbii
      vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa vw wex vx vz cA
      rexcom4 vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa vw wex
      vx cA wrex vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa vx cA
      wrex vw wex vz vy cv vz cv vw cv cop wceq vw cv vz cv cop vx cv wcel wa
      vx vw cA rexcom4 exbii 3bitrri 3bitri vx vy cv cA vx cv ccnv eliun bitr4i
      eqriv $.
  $}

  ${
    $d x y A $.
    $( Alternate definition of domain.  Definition 6.5(1) of [TakeutiZaring]
       p. 24.  (Contributed by NM, 28-Dec-1996.) $)
    dfdm3 $p |- dom A = { x | E. y <. x , y >. e. A } $=
      cA cdm vx cv vy cv cA wbr vy wex vx cab vx cv vy cv cop cA wcel vy wex vx
      cab vx vy cA df-dm vx cv vy cv cA wbr vy wex vx cv vy cv cop cA wcel vy
      wex vx vx cv vy cv cA wbr vx cv vy cv cop cA wcel vy vx cv vy cv cA df-br
      exbii abbii eqtri $.

    $( Alternate definition of range.  Definition 4 of [Suppes] p. 60.
       (Contributed by NM, 27-Dec-1996.) $)
    dfrn2 $p |- ran A = { y | E. x x A y } $=
      cA crn cA ccnv cdm vy cv vx cv cA ccnv wbr vx wex vy cab vx cv vy cv cA
      wbr vx wex vy cab cA df-rn vy vx cA ccnv df-dm vy cv vx cv cA ccnv wbr vx
      wex vx cv vy cv cA wbr vx wex vy vy cv vx cv cA ccnv wbr vx cv vy cv cA
      wbr vx vy cv vx cv cA vy vex vx vex brcnv exbii abbii 3eqtri $.

    $( Alternate definition of range.  Definition 6.5(2) of [TakeutiZaring]
       p. 24.  (Contributed by NM, 28-Dec-1996.) $)
    dfrn3 $p |- ran A = { y | E. x <. x , y >. e. A } $=
      cA crn vx cv vy cv cA wbr vx wex vy cab vx cv vy cv cop cA wcel vx wex vy
      cab vx vy cA dfrn2 vx cv vy cv cA wbr vx wex vx cv vy cv cop cA wcel vx
      wex vy vx cv vy cv cA wbr vx cv vy cv cop cA wcel vx vx cv vy cv cA df-br
      exbii abbii eqtri $.
  $}

  ${
    $d A x y $.  $d B x y $.
    $( Membership in a range.  (Contributed by Scott Fenton, 2-Feb-2011.) $)
    elrn2g $p |- ( A e. V -> ( A e. ran B <-> E. x <. x , A >. e. B ) ) $=
      vx cv vy cv cop cB wcel vx wex vx cv cA cop cB wcel vx wex vy cA cB crn
      cV vy cv cA wceq vx cv vy cv cop cB wcel vx cv cA cop cB wcel vx vy cv cA
      wceq vx cv vy cv cop vx cv cA cop cB vy cv cA vx cv opeq2 eleq1d exbidv
      vx vy cB dfrn3 elab2g $.

    $( Membership in a range.  (Contributed by Scott Fenton, 2-Feb-2011.) $)
    elrng $p |- ( A e. V -> ( A e. ran B <-> E. x x B A ) ) $=
      cA cV wcel cA cB crn wcel vx cv cA cop cB wcel vx wex vx cv cA cB wbr vx
      wex vx cA cB cV elrn2g vx cv cA cB wbr vx cv cA cop cB wcel vx vx cv cA
      cB df-br exbii syl6bbr $.
  $}

  ${
    $d x y A $.
    $( Alternate definition of domain.  (Contributed by NM, 28-Dec-1996.) $)
    dfdm4 $p |- dom A = ran `' A $=
      vy cv vx cv cA ccnv wbr vy wex vx cab vx cv vy cv cA wbr vy wex vx cab cA
      ccnv crn cA cdm vy cv vx cv cA ccnv wbr vy wex vx cv vy cv cA wbr vy wex
      vx vy cv vx cv cA ccnv wbr vx cv vy cv cA wbr vy vy cv vx cv cA vy vex vx
      vex brcnv exbii abbii vy vx cA ccnv dfrn2 vx vy cA df-dm 3eqtr4ri $.
  $}

  ${
    $d x y w v $.  $d w v A $.
    dfdmf.1 $e |- F/_ x A $.
    dfdmf.2 $e |- F/_ y A $.
    $( Definition of domain, using bound-variable hypotheses instead of
       distinct variable conditions.  (Contributed by NM, 8-Mar-1995.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    dfdmf $p |- dom A = { x | E. y x A y } $=
      cA cdm vw cv vv cv cA wbr vv wex vw cab vw cv vy cv cA wbr vy wex vw cab
      vx cv vy cv cA wbr vy wex vx cab vw vv cA df-dm vw cv vv cv cA wbr vv wex
      vw cv vy cv cA wbr vy wex vw vw cv vv cv cA wbr vw cv vy cv cA wbr vv vy
      vy vw cv vv cv cA vy vw cv nfcv dfdmf.2 vy vv cv nfcv nfbr vw cv vy cv cA
      wbr vv nfv vv cv vy cv vw cv cA breq2 cbvex abbii vw cv vy cv cA wbr vy
      wex vx cv vy cv cA wbr vy wex vw vx vw cv vy cv cA wbr vx vy vx vw cv vy
      cv cA vx vw cv nfcv dfdmf.1 vx vy cv nfcv nfbr nfex vx cv vy cv cA wbr vy
      wex vw nfv vw cv vx cv wceq vw cv vy cv cA wbr vx cv vy cv cA wbr vy vw
      cv vx cv vy cv cA breq1 exbidv cbvab 3eqtri $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Domain membership.  Theorem 4 of [Suppes] p. 59.  (Contributed by Mario
       Carneiro, 9-Jul-2014.) $)
    eldmg $p |- ( A e. V -> ( A e. dom B <-> E. y A B y ) ) $=
      vx cv vy cv cB wbr vy wex cA vy cv cB wbr vy wex vx cA cB cdm cV vx cv cA
      wceq vx cv vy cv cB wbr cA vy cv cB wbr vy vx cv cA vy cv cB breq1 exbidv
      vx vy cB df-dm elab2g $.

    $( Domain membership.  Theorem 4 of [Suppes] p. 59.  (Contributed by NM,
       27-Jan-1997.)  (Revised by Mario Carneiro, 9-Jul-2014.) $)
    eldm2g $p |- ( A e. V -> ( A e. dom B <-> E. y <. A , y >. e. B ) ) $=
      cA cV wcel cA cB cdm wcel cA vy cv cB wbr vy wex cA vy cv cop cB wcel vy
      wex vy cA cB cV eldmg cA vy cv cB wbr cA vy cv cop cB wcel vy cA vy cv cB
      df-br exbii syl6bb $.
  $}

  ${
    $d x y A $.  $d x y B $.
    eldm.1 $e |- A e. _V $.
    $( Membership in a domain.  Theorem 4 of [Suppes] p. 59.  (Contributed by
       NM, 2-Apr-2004.) $)
    eldm $p |- ( A e. dom B <-> E. y A B y ) $=
      cA cvv wcel cA cB cdm wcel cA vy cv cB wbr vy wex wb eldm.1 vy cA cB cvv
      eldmg ax-mp $.

    $( Membership in a domain.  Theorem 4 of [Suppes] p. 59.  (Contributed by
       NM, 1-Aug-1994.) $)
    eldm2 $p |- ( A e. dom B <-> E. y <. A , y >. e. B ) $=
      cA cvv wcel cA cB cdm wcel cA vy cv cop cB wcel vy wex wb eldm.1 vy cA cB
      cvv eldm2g ax-mp $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Subset theorem for domain.  (Contributed by NM, 11-Aug-1994.) $)
    dmss $p |- ( A C_ B -> dom A C_ dom B ) $=
      cA cB wss vx cA cdm cB cdm cA cB wss vx cv vy cv cop cA wcel vy wex vx cv
      vy cv cop cB wcel vy wex vx cv cA cdm wcel vx cv cB cdm wcel cA cB wss vx
      cv vy cv cop cA wcel vx cv vy cv cop cB wcel vy cA cB vx cv vy cv cop
      ssel eximdv vy vx cv cA vx vex eldm2 vy vx cv cB vx vex eldm2 3imtr4g
      ssrdv $.
  $}

  $( Equality theorem for domain.  (Contributed by NM, 11-Aug-1994.) $)
  dmeq $p |- ( A = B -> dom A = dom B ) $=
    cA cB wss cB cA wss wa cA cdm cB cdm wss cB cdm cA cdm wss wa cA cB wceq cA
    cdm cB cdm wceq cA cB wss cA cdm cB cdm wss cB cA wss cB cdm cA cdm wss cA
    cB dmss cB cA dmss anim12i cA cB eqss cA cdm cB cdm eqss 3imtr4i $.

  ${
    dmeqi.1 $e |- A = B $.
    $( Equality inference for domain.  (Contributed by NM, 4-Mar-2004.) $)
    dmeqi $p |- dom A = dom B $=
      cA cB wceq cA cdm cB cdm wceq dmeqi.1 cA cB dmeq ax-mp $.
  $}

  ${
    dmeqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for domain.  (Contributed by NM, 4-Mar-2004.) $)
    dmeqd $p |- ( ph -> dom A = dom B ) $=
      wph cA cB wceq cA cdm cB cdm wceq dmeqd.1 cA cB dmeq syl $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.
    opeldm.1 $e |- A e. _V $.
    opeldm.2 $e |- B e. _V $.
    $( Membership of first of an ordered pair in a domain.  (Contributed by NM,
       30-Jul-1995.) $)
    opeldm $p |- ( <. A , B >. e. C -> A e. dom C ) $=
      cA cB cop cC wcel cA vy cv cop cC wcel vy wex cA cC cdm wcel cA vy cv cop
      cC wcel cA cB cop cC wcel vy cB opeldm.2 vy cv cB wceq cA vy cv cop cA cB
      cop cC vy cv cB cA opeq2 eleq1d spcev vy cA cC opeldm.1 eldm2 sylibr $.

    $( Membership of first of a binary relation in a domain.  (Contributed by
       NM, 30-Jul-1995.) $)
    breldm $p |- ( A R B -> A e. dom R ) $=
      cA cB cR wbr cA cB cop cR wcel cA cR cdm wcel cA cB cR df-br cA cB cR
      opeldm.1 opeldm.2 opeldm sylbi $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x R $.
    $( Membership of first of a binary relation in a domain.  (Contributed by
       NM, 21-Mar-2007.) $)
    breldmg $p |- ( ( A e. C /\ B e. D /\ A R B ) -> A e. dom R ) $=
      cA cC wcel cB cD wcel cA cB cR wbr w3a cA cR cdm wcel cA vx cv cR wbr vx
      wex cB cD wcel cA cB cR wbr cA vx cv cR wbr vx wex cA cC wcel cB cD wcel
      cA cB cR wbr cA vx cv cR wbr vx wex cA vx cv cR wbr cA cB cR wbr vx cB cD
      vx cv cB cA cR breq2 spcegv imp 3adant1 cA cC wcel cB cD wcel cA cR cdm
      wcel cA vx cv cR wbr vx wex wb cA cB cR wbr vx cA cR cC eldmg 3ad2ant1
      mpbird $.

    $( The domain of a union is the union of domains.  Exercise 56(a) of
       [Enderton] p. 65.  (Contributed by NM, 12-Aug-1994.)  (Proof shortened
       by Andrew Salmon, 27-Aug-2011.) $)
    dmun $p |- dom ( A u. B ) = ( dom A u. dom B ) $=
      vy cv vx cv cA wbr vx wex vy cab vy cv vx cv cB wbr vx wex vy cab cun vy
      cv vx cv cA cB cun wbr vx wex vy cab cA cdm cB cdm cun cA cB cun cdm vy
      cv vx cv cA wbr vx wex vy cab vy cv vx cv cB wbr vx wex vy cab cun vy cv
      vx cv cA wbr vx wex vy cv vx cv cB wbr vx wex wo vy cab vy cv vx cv cA cB
      cun wbr vx wex vy cab vy cv vx cv cA wbr vx wex vy cv vx cv cB wbr vx wex
      vy unab vy cv vx cv cA wbr vx wex vy cv vx cv cB wbr vx wex wo vy cv vx
      cv cA cB cun wbr vx wex vy vy cv vx cv cA cB cun wbr vx wex vy cv vx cv
      cA wbr vy cv vx cv cB wbr wo vx wex vy cv vx cv cA wbr vx wex vy cv vx cv
      cB wbr vx wex wo vy cv vx cv cA cB cun wbr vy cv vx cv cA wbr vy cv vx cv
      cB wbr wo vx vy cv vx cv cA cB brun exbii vy cv vx cv cA wbr vy cv vx cv
      cB wbr vx 19.43 bitr2i abbii eqtri cA cdm vy cv vx cv cA wbr vx wex vy
      cab cB cdm vy cv vx cv cB wbr vx wex vy cab vy vx cA df-dm vy vx cB df-dm
      uneq12i vy vx cA cB cun df-dm 3eqtr4ri $.

    $( The domain of an intersection belong to the intersection of domains.
       Theorem 6 of [Suppes] p. 60.  (Contributed by NM, 15-Sep-2004.) $)
    dmin $p |- dom ( A i^i B ) C_ ( dom A i^i dom B ) $=
      vx cA cB cin cdm cA cdm cB cdm cin vx cv vy cv cop cA wcel vx cv vy cv
      cop cB wcel wa vy wex vx cv vy cv cop cA wcel vy wex vx cv vy cv cop cB
      wcel vy wex wa vx cv cA cB cin cdm wcel vx cv cA cdm cB cdm cin wcel vx
      cv vy cv cop cA wcel vx cv vy cv cop cB wcel vy 19.40 vx cv cA cB cin cdm
      wcel vx cv vy cv cop cA cB cin wcel vy wex vx cv vy cv cop cA wcel vx cv
      vy cv cop cB wcel wa vy wex vy vx cv cA cB cin vx vex eldm2 vx cv vy cv
      cop cA cB cin wcel vx cv vy cv cop cA wcel vx cv vy cv cop cB wcel wa vy
      vx cv vy cv cop cA cB elin exbii bitri vx cv cA cdm cB cdm cin wcel vx cv
      cA cdm wcel vx cv cB cdm wcel wa vx cv vy cv cop cA wcel vy wex vx cv vy
      cv cop cB wcel vy wex wa vx cv cA cdm cB cdm elin vx cv cA cdm wcel vx cv
      vy cv cop cA wcel vy wex vx cv cB cdm wcel vx cv vy cv cop cB wcel vy wex
      vy vx cv cA vx vex eldm2 vy vx cv cB vx vex eldm2 anbi12i bitri 3imtr4i
      ssriv $.

  $}

  ${
    $d x y z $.  $d y z A $.  $d y z B $.
    $( The domain of an indexed union.  (Contributed by Mario Carneiro,
       26-Apr-2016.) $)
    dmiun $p |- dom U_ x e. A B = U_ x e. A dom B $=
      vy vx cA cB ciun cdm vx cA cB cdm ciun vy cv vz cv cop vx cA cB ciun wcel
      vz wex vy cv cB cdm wcel vx cA wrex vy cv vx cA cB ciun cdm wcel vy cv vx
      cA cB cdm ciun wcel vy cv vz cv cop cB wcel vz wex vx cA wrex vy cv vz cv
      cop cB wcel vx cA wrex vz wex vy cv cB cdm wcel vx cA wrex vy cv vz cv
      cop vx cA cB ciun wcel vz wex vy cv vz cv cop cB wcel vx vz cA rexcom4 vy
      cv cB cdm wcel vy cv vz cv cop cB wcel vz wex vx cA vz vy cv cB vy vex
      eldm2 rexbii vy cv vz cv cop vx cA cB ciun wcel vy cv vz cv cop cB wcel
      vx cA wrex vz vx vy cv vz cv cop cA cB eliun exbii 3bitr4ri vz vy cv vx
      cA cB ciun vy vex eldm2 vx vy cv cA cB cdm eliun 3bitr4i eqriv $.

    $d x A $.
    $( The domain of a union.  Part of Exercise 8 of [Enderton] p. 41.
       (Contributed by NM, 3-Feb-2004.) $)
    dmuni $p |- dom U. A = U_ x e. A dom x $=
      vy cA cuni cdm vx cA vx cv cdm ciun vy cv vz cv cop cA cuni wcel vz wex
      vy cv vx cv cdm wcel vx cA wrex vy cv cA cuni cdm wcel vy cv vx cA vx cv
      cdm ciun wcel vy cv vz cv cop vx cv wcel vx cv cA wcel wa vx wex vz wex
      vx cv cA wcel vy cv vx cv cdm wcel wa vx wex vy cv vz cv cop cA cuni wcel
      vz wex vy cv vx cv cdm wcel vx cA wrex vy cv vz cv cop vx cv wcel vx cv
      cA wcel wa vx wex vz wex vy cv vz cv cop vx cv wcel vx cv cA wcel wa vz
      wex vx wex vx cv cA wcel vy cv vx cv cdm wcel wa vx wex vy cv vz cv cop
      vx cv wcel vx cv cA wcel wa vz vx excom vy cv vz cv cop vx cv wcel vx cv
      cA wcel wa vz wex vx cv cA wcel vy cv vx cv cdm wcel wa vx vy cv vz cv
      cop vx cv wcel vz wex vx cv cA wcel wa vx cv cA wcel vy cv vz cv cop vx
      cv wcel vz wex wa vy cv vz cv cop vx cv wcel vx cv cA wcel wa vz wex vx
      cv cA wcel vy cv vx cv cdm wcel wa vy cv vz cv cop vx cv wcel vz wex vx
      cv cA wcel ancom vy cv vz cv cop vx cv wcel vx cv cA wcel vz 19.41v vy cv
      vx cv cdm wcel vy cv vz cv cop vx cv wcel vz wex vx cv cA wcel vz vy cv
      vx cv vy vex eldm2 anbi2i 3bitr4i exbii bitri vy cv vz cv cop cA cuni
      wcel vy cv vz cv cop vx cv wcel vx cv cA wcel wa vx wex vz vx vy cv vz cv
      cop cA eluni exbii vy cv vx cv cdm wcel vx cA df-rex 3bitr4i vz vy cv cA
      cuni vy vex eldm2 vx vy cv cA vx cv cdm eliun 3bitr4i eqriv $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( The domain of a class of ordered pairs.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 4-Dec-2016.) $)
    dmopab $p |- dom { <. x , y >. | ph } = { x | E. y ph } $=
      wph vx vy copab cdm vx cv vy cv wph vx vy copab wbr vy wex vx cab wph vy
      wex vx cab vx vy wph vx vy copab wph vx vy nfopab1 wph vx vy nfopab2
      dfdmf vx cv vy cv wph vx vy copab wbr vy wex wph vy wex vx vx cv vy cv
      wph vx vy copab wbr wph vy vx cv vy cv wph vx vy copab wbr vx cv vy cv
      cop wph vx vy copab wcel wph vx cv vy cv wph vx vy copab df-br wph vx vy
      opabid bitri exbii abbii eqtri $.
  $}

  ${
    $d x y A $.
    $( Upper bound for the domain of a restricted class of ordered pairs.
       (Contributed by NM, 31-Jan-2004.) $)
    dmopabss $p |- dom { <. x , y >. | ( x e. A /\ ph ) } C_ A $=
      vx cv cA wcel wph wa vx vy copab cdm vx cv cA wcel wph wa vy wex vx cab
      cA vx cv cA wcel wph wa vx vy dmopab vx cv cA wcel wph wa vy wex vx cab
      vx cv cA wcel wph vy wex wa vx cab cA vx cv cA wcel wph wa vy wex vx cv
      cA wcel wph vy wex wa vx vx cv cA wcel wph vy 19.42v abbii wph vy wex vx
      cA ssab2 eqsstri eqsstri $.
  $}

  ${
    $d x y A $.
    $( The domain of a restricted class of ordered pairs.  (Contributed by NM,
       31-Jan-2004.) $)
    dmopab3 $p |- ( A. x e. A E. y ph <->
               dom { <. x , y >. | ( x e. A /\ ph ) } = A ) $=
      wph vy wex vx cA wral vx cv cA wcel wph vy wex wi vx wal vx cv cA wcel vx
      cv cA wcel wph vy wex wa wb vx wal vx cv cA wcel wph wa vx vy copab cdm
      cA wceq wph vy wex vx cA df-ral vx cv cA wcel wph vy wex wi vx cv cA wcel
      vx cv cA wcel wph vy wex wa wb vx vx cv cA wcel wph vy wex pm4.71 albii
      vx cv cA wcel wph wa vx vy copab cdm cA wceq vx cv cA wcel wph vy wex wa
      vx cab cA wceq cA vx cv cA wcel wph vy wex wa vx cab wceq vx cv cA wcel
      vx cv cA wcel wph vy wex wa wb vx wal vx cv cA wcel wph wa vx vy copab
      cdm vx cv cA wcel wph vy wex wa vx cab cA vx cv cA wcel wph wa vx vy
      copab cdm vx cv cA wcel wph wa vy wex vx cab vx cv cA wcel wph vy wex wa
      vx cab vx cv cA wcel wph wa vx vy dmopab vx cv cA wcel wph wa vy wex vx
      cv cA wcel wph vy wex wa vx vx cv cA wcel wph vy 19.42v abbii eqtri
      eqeq1i cA vx cv cA wcel wph vy wex wa vx cab eqcom vx cv cA wcel wph vy
      wex wa vx cA abeq2 3bitr2ri 3bitri $.
  $}

  ${
    $d x y $.
    $( The domain of the empty set is empty.  Part of Theorem 3.8(v) of [Monk1]
       p. 36.  (Contributed by NM, 4-Jul-1994.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    dm0 $p |- dom (/) = (/) $=
      c0 cdm c0 wceq vx cv c0 cdm wcel wn vx vx c0 cdm eq0 vx cv c0 cdm wcel vx
      cv vy cv cop c0 wcel vy wex vx cv vy cv cop c0 wcel vy vx cv vy cv cop
      noel nex vy vx cv c0 vx vex eldm2 mtbir mpgbir $.

    $( The domain of the identity relation is the universe.  (Contributed by
       NM, 30-Apr-1998.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    dmi $p |- dom _I = _V $=
      cid cdm cvv wceq vx cv cid cdm wcel vx vx cid cdm eqv vx cv cid cdm wcel
      vx cv vy cv cid wbr vy wex vx cv vy cv cid wbr vy wex vy cv vx cv wceq vy
      wex vy vx a9ev vx cv vy cv cid wbr vy cv vx cv wceq vy vx cv vy cv cid
      wbr vx cv vy cv wceq vy cv vx cv wceq vx cv vy cv vy vex ideq vx vy
      equcom bitri exbii mpbir vy vx cv cid vx vex eldm mpbir mpgbir $.

    $( The domain of the universe is the universe.  (Contributed by NM,
       8-Aug-2003.) $)
    dmv $p |- dom _V = _V $=
      cvv cdm cvv cvv cdm ssv cvv cid cdm cvv cdm dmi cid cvv wss cid cdm cvv
      cdm wss cid ssv cid cvv dmss ax-mp eqsstr3i eqssi $.
  $}

  ${
    $d x y A $.
    $( An empty domain implies an empty range.  (Contributed by NM,
       21-May-1998.) $)
    dm0rn0 $p |- ( dom A = (/) <-> ran A = (/) ) $=
      vx cv vy cv cA wbr vy wex vx cab c0 wceq vx cv vy cv cA wbr vx wex vy cab
      c0 wceq cA cdm c0 wceq cA crn c0 wceq vx cv vy cv cA wbr vy wex vx cv c0
      wcel wb vx wal vx cv vy cv cA wbr vx wex vy cv c0 wcel wb vy wal vx cv vy
      cv cA wbr vy wex vx cab c0 wceq vx cv vy cv cA wbr vx wex vy cab c0 wceq
      vx cv vy cv cA wbr vy wex wn vx wal vx cv vy cv cA wbr vx wex wn vy wal
      vx cv vy cv cA wbr vy wex vx cv c0 wcel wb vx wal vx cv vy cv cA wbr vx
      wex vy cv c0 wcel wb vy wal vx cv vy cv cA wbr vy wex wn vx wal vx cv vy
      cv cA wbr vx wex vy wex wn vx cv vy cv cA wbr vx wex wn vy wal vx cv vy
      cv cA wbr vy wex wn vx wal vx cv vy cv cA wbr vy wex vx wex vx cv vy cv
      cA wbr vx wex vy wex vx cv vy cv cA wbr vy wex vx alnex vx cv vy cv cA
      wbr vx vy excom xchbinx vx cv vy cv cA wbr vx wex vy alnex bitr4i vx cv
      vy cv cA wbr vy wex wn vx cv vy cv cA wbr vy wex vx cv c0 wcel wb vx vx
      cv c0 wcel vx cv vy cv cA wbr vy wex vx cv noel nbn albii vx cv vy cv cA
      wbr vx wex wn vx cv vy cv cA wbr vx wex vy cv c0 wcel wb vy vy cv c0 wcel
      vx cv vy cv cA wbr vx wex vy cv noel nbn albii 3bitr3i vx cv vy cv cA wbr
      vy wex vx c0 abeq1 vx cv vy cv cA wbr vx wex vy c0 abeq1 3bitr4i cA cdm
      vx cv vy cv cA wbr vy wex vx cab c0 vx vy cA df-dm eqeq1i cA crn vx cv vy
      cv cA wbr vx wex vy cab c0 vx vy cA dfrn2 eqeq1i 3bitr4i $.

    $( A relation is empty iff its domain is empty.  (Contributed by NM,
       15-Sep-2004.) $)
    reldm0 $p |- ( Rel A -> ( A = (/) <-> dom A = (/) ) ) $=
      cA wrel cA c0 wceq vx cv vy cv cop cA wcel vx cv vy cv cop c0 wcel wb vy
      wal vx wal cA cdm c0 wceq cA wrel c0 wrel cA c0 wceq vx cv vy cv cop cA
      wcel vx cv vy cv cop c0 wcel wb vy wal vx wal wb rel0 vx vy cA c0 eqrel
      mpan2 cA cdm c0 wceq vx cv cA cdm wcel wn vx wal vx cv vy cv cop cA wcel
      vx cv vy cv cop c0 wcel wb vy wal vx wal vx cA cdm eq0 vx cv cA cdm wcel
      wn vx cv vy cv cop cA wcel vx cv vy cv cop c0 wcel wb vy wal vx vx cv cA
      cdm wcel wn vx cv vy cv cop cA wcel wn vy wal vx cv vy cv cop cA wcel vx
      cv vy cv cop c0 wcel wb vy wal vx cv vy cv cop cA wcel wn vy wal vx cv vy
      cv cop cA wcel vy wex vx cv cA cdm wcel vx cv vy cv cop cA wcel vy alnex
      vy vx cv cA vx vex eldm2 xchbinxr vx cv vy cv cop cA wcel wn vx cv vy cv
      cop cA wcel vx cv vy cv cop c0 wcel wb vy vx cv vy cv cop c0 wcel vx cv
      vy cv cop cA wcel vx cv vy cv cop noel nbn albii bitr3i albii bitr2i
      syl6bb $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The domain of a cross product.  Part of Theorem 3.13(x) of [Monk1]
       p. 37.  (Contributed by NM, 28-Jul-1995.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    dmxp $p |- ( B =/= (/) -> dom ( A X. B ) = A ) $=
      cB c0 wne cA cB cxp cdm vy cv cA wcel vx cv cB wcel wa vy vx copab cdm cA
      cA cB cxp vy cv cA wcel vx cv cB wcel wa vy vx copab vy vx cA cB df-xp
      dmeqi cB c0 wne vx cv cB wcel vx wex vy cA wral vy cv cA wcel vx cv cB
      wcel wa vy vx copab cdm cA wceq cB c0 wne vx cv cB wcel vx wex vy cA cB
      c0 wne vx cv cB wcel vx wex vx cB n0 biimpi ralrimivw vx cv cB wcel vy vx
      cA dmopab3 sylib syl5eq $.
  $}

  $( The domain of a square cross product.  (Contributed by NM,
     28-Jul-1995.) $)
  dmxpid $p |- dom ( A X. A ) = A $=
    cA cA cxp cdm cA wceq cA c0 cA c0 wceq c0 cdm c0 cA cA cxp cdm cA dm0 cA c0
    wceq cA cA cxp c0 cA c0 wceq cA cA cxp c0 cA cxp c0 cA c0 cA xpeq1 cA xp0r
    syl6eq dmeqd cA c0 wceq id 3eqtr4a cA cA dmxp pm2.61ine $.

  $( The domain of the intersection of two square cross products.  Unlike
     ~ dmin , equality holds.  (Contributed by NM, 29-Jan-2008.) $)
  dmxpin $p |- dom ( ( A X. A ) i^i ( B X. B ) ) = ( A i^i B ) $=
    cA cA cxp cB cB cxp cin cdm cA cB cin cA cB cin cxp cdm cA cB cin cA cA cxp
    cB cB cxp cin cA cB cin cA cB cin cxp cA cA cB cB inxp dmeqi cA cB cin
    dmxpid eqtri $.

  $( The cross product of a class with itself is one-to-one.  (Contributed by
     NM, 5-Nov-2006.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  xpid11 $p |- ( ( A X. A ) = ( B X. B ) <-> A = B ) $=
    cA cA cxp cB cB cxp wceq cA cB wceq cA cA cxp cB cB cxp wceq cA cA cxp cdm
    cB cB cxp cdm cA cB cA cA cxp cB cB cxp dmeq cA dmxpid cB dmxpid 3eqtr3g cA
    cB wceq cA cA cxp cB cB cxp wceq cA cB cA cB xpeq12 anidms impbii $.

  $( The domain of the double converse of a class (which doesn't have to be a
     relation as in ~ dfrel2 ).  (Contributed by NM, 8-Apr-2007.) $)
  dmcnvcnv $p |- dom `' `' A = dom A $=
    cA cdm cA ccnv crn cA ccnv ccnv cdm cA dfdm4 cA ccnv df-rn eqtr2i $.

  $( The range of the double converse of a class.  (Contributed by NM,
     8-Apr-2007.) $)
  rncnvcnv $p |- ran `' `' A = ran A $=
    cA crn cA ccnv cdm cA ccnv ccnv crn cA df-rn cA ccnv dfdm4 eqtr2i $.

  ${
    $d x y A $.  $d x y B $.
    $( The first member of an ordered pair in a relation belongs to the domain
       of the relation.  (Contributed by NM, 28-Jul-2004.) $)
    elreldm $p |- ( ( Rel A /\ B e. A ) -> |^| |^| B e. dom A ) $=
      cA wrel cB cA wcel cB cint cint cA cdm wcel cB cA wcel cA wrel cB vx cv
      vy cv cop wceq vy wex vx wex cB cint cint cA cdm wcel cA wrel cB cA wcel
      cB cvv cvv cxp wcel cB vx cv vy cv cop wceq vy wex vx wex cA wrel cA cvv
      cvv cxp wss cB cA wcel cB cvv cvv cxp wcel wi cA df-rel cA cvv cvv cxp cB
      ssel sylbi vx vy cB elvv syl6ib cB vx cv vy cv cop wceq cB cA wcel cB
      cint cint cA cdm wcel wi vx vy cB vx cv vy cv cop wceq cB cA wcel vx cv
      cA cdm wcel cB cint cint cA cdm wcel cB vx cv vy cv cop wceq cB cA wcel
      vx cv vy cv cop cA wcel vx cv cA cdm wcel cB vx cv vy cv cop cA eleq1 vx
      cv vy cv cA vx vex vy vex opeldm syl6bi cB vx cv vy cv cop wceq cB cint
      cint vx cv cA cdm cB vx cv vy cv cop wceq cB cint cint vx cv vy cv cop
      cint cint vx cv cB vx cv vy cv cop wceq cB cint vx cv vy cv cop cint cB
      vx cv vy cv cop inteq inteqd vx cv vy cv vx vex vy vex op1stb syl6eq
      eleq1d sylibrd exlimivv syli imp $.
  $}

  $( Equality theorem for range.  (Contributed by NM, 29-Dec-1996.) $)
  rneq $p |- ( A = B -> ran A = ran B ) $=
    cA cB wceq cA ccnv cdm cB ccnv cdm cA crn cB crn cA cB wceq cA ccnv cB ccnv
    cA cB cnveq dmeqd cA df-rn cB df-rn 3eqtr4g $.

  ${
    rneqi.1 $e |- A = B $.
    $( Equality inference for range.  (Contributed by NM, 4-Mar-2004.) $)
    rneqi $p |- ran A = ran B $=
      cA cB wceq cA crn cB crn wceq rneqi.1 cA cB rneq ax-mp $.
  $}

  ${
    rneqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for range.  (Contributed by NM, 4-Mar-2004.) $)
    rneqd $p |- ( ph -> ran A = ran B ) $=
      wph cA cB wceq cA crn cB crn wceq rneqd.1 cA cB rneq syl $.
  $}

  $( Subset theorem for range.  (Contributed by NM, 22-Mar-1998.) $)
  rnss $p |- ( A C_ B -> ran A C_ ran B ) $=
    cA cB wss cA ccnv cdm cB ccnv cdm cA crn cB crn cA cB wss cA ccnv cB ccnv
    wss cA ccnv cdm cB ccnv cdm wss cA cB cnvss cA ccnv cB ccnv dmss syl cA
    df-rn cB df-rn 3sstr4g $.

  $( The second argument of a binary relation belongs to its range.
     (Contributed by NM, 29-Jun-2008.) $)
  brelrng $p |- ( ( A e. F /\ B e. G /\ A C B ) -> B e. ran C ) $=
    cA cF wcel cB cG wcel cA cB cC wbr w3a cB cC ccnv cdm cC crn cA cF wcel cB
    cG wcel cA cB cC wbr cB cA cC ccnv wbr cB cC ccnv cdm wcel cA cF wcel cB cG
    wcel cB cA cC ccnv wbr cA cB cC wbr cB cG wcel cA cF wcel cB cA cC ccnv wbr
    cA cB cC wbr wb cB cA cG cF cC brcnvg ancoms biimp3ar cB cG wcel cA cF wcel
    cB cA cC ccnv wbr cB cC ccnv cdm wcel cB cA cG cF cC ccnv breldmg 3com12
    syld3an3 cC df-rn syl6eleqr $.

  ${
    brelrn.1 $e |- A e. _V $.
    brelrn.2 $e |- B e. _V $.
    $( The second argument of a binary relation belongs to its range.
       (Contributed by NM, 13-Aug-2004.) $)
    brelrn $p |- ( A C B -> B e. ran C ) $=
      cA cvv wcel cB cvv wcel cA cB cC wbr cB cC crn wcel brelrn.1 brelrn.2 cA
      cB cC cvv cvv brelrng mp3an12 $.

    $( Membership of second member of an ordered pair in a range.  (Contributed
       by NM, 23-Feb-1997.) $)
    opelrn $p |- ( <. A , B >. e. C -> B e. ran C ) $=
      cA cB cop cC wcel cA cB cC wbr cB cC crn wcel cA cB cC df-br cA cB cC
      brelrn.1 brelrn.2 brelrn sylbir $.
  $}

  $( The first argument of a binary relation belongs to its domain.
     (Contributed by NM, 2-Jul-2008.) $)
  releldm $p |- ( ( Rel R /\ A R B ) -> A e. dom R ) $=
    cR wrel cA cB cR wbr wa cA cvv wcel cB cvv wcel cA cB cR wbr cA cR cdm wcel
    cA cB cR brrelex cA cB cR brrelex2 cR wrel cA cB cR wbr simpr cA cB cvv cvv
    cR breldmg syl3anc $.

  $( The second argument of a binary relation belongs to its range.
     (Contributed by NM, 2-Jul-2008.) $)
  relelrn $p |- ( ( Rel R /\ A R B ) -> B e. ran R ) $=
    cR wrel cA cB cR wbr wa cA cvv wcel cB cvv wcel cA cB cR wbr cB cR crn wcel
    cA cB cR brrelex cA cB cR brrelex2 cR wrel cA cB cR wbr simpr cA cB cR cvv
    cvv brelrng syl3anc $.

  ${
    $d x A $.  $d x R $.
    $( Membership in a domain.  (Contributed by Mario Carneiro, 5-Nov-2015.) $)
    releldmb $p |- ( Rel R -> ( A e. dom R <-> E. x A R x ) ) $=
      cR wrel cA cR cdm wcel cA vx cv cR wbr vx wex cA cR cdm wcel cA vx cv cR
      wbr vx wex vx cA cR cR cdm eldmg ibi cR wrel cA vx cv cR wbr cA cR cdm
      wcel vx cR wrel cA vx cv cR wbr cA cR cdm wcel cA vx cv cR releldm ex
      exlimdv impbid2 $.

    $( Membership in a range.  (Contributed by Mario Carneiro, 5-Nov-2015.) $)
    relelrnb $p |- ( Rel R -> ( A e. ran R <-> E. x x R A ) ) $=
      cR wrel cA cR crn wcel vx cv cA cR wbr vx wex cA cR crn wcel vx cv cA cR
      wbr vx wex vx cA cR cR crn elrng ibi cR wrel vx cv cA cR wbr cA cR crn
      wcel vx cR wrel vx cv cA cR wbr cA cR crn wcel vx cv cA cR relelrn ex
      exlimdv impbid2 $.
  $}

  ${
    releldm.1 $e |- Rel R $.
    $( The first argument of a binary relation belongs to its domain.
       (Contributed by NM, 28-Apr-2015.) $)
    releldmi $p |- ( A R B -> A e. dom R ) $=
      cR wrel cA cB cR wbr cA cR cdm wcel releldm.1 cA cB cR releldm mpan $.

    $( The second argument of a binary relation belongs to its range.
       (Contributed by NM, 28-Apr-2015.) $)
    relelrni $p |- ( A R B -> B e. ran R ) $=
      cR wrel cA cB cR wbr cB cR crn wcel releldm.1 cA cB cR relelrn mpan $.
  $}

  ${
    $d x y w v $.  $d w v A $.
    dfrnf.1 $e |- F/_ x A $.
    dfrnf.2 $e |- F/_ y A $.
    $( Definition of range, using bound-variable hypotheses instead of distinct
       variable conditions.  (Contributed by NM, 14-Aug-1995.)  (Revised by
       Mario Carneiro, 15-Oct-2016.) $)
    dfrnf $p |- ran A = { y | E. x x A y } $=
      cA crn vv cv vw cv cA wbr vv wex vw cab vx cv vw cv cA wbr vx wex vw cab
      vx cv vy cv cA wbr vx wex vy cab vv vw cA dfrn2 vv cv vw cv cA wbr vv wex
      vx cv vw cv cA wbr vx wex vw vv cv vw cv cA wbr vx cv vw cv cA wbr vv vx
      vx vv cv vw cv cA vx vv cv nfcv dfrnf.1 vx vw cv nfcv nfbr vx cv vw cv cA
      wbr vv nfv vv cv vx cv vw cv cA breq1 cbvex abbii vx cv vw cv cA wbr vx
      wex vx cv vy cv cA wbr vx wex vw vy vx cv vw cv cA wbr vy vx vy vx cv vw
      cv cA vy vx cv nfcv dfrnf.2 vy vw cv nfcv nfbr nfex vx cv vy cv cA wbr vx
      wex vw nfv vw cv vy cv wceq vx cv vw cv cA wbr vx cv vy cv cA wbr vx vw
      cv vy cv vx cv cA breq2 exbidv cbvab 3eqtri $.
  $}

  ${
    $d x y A $.  $d x y B $.
    elrn.1 $e |- A e. _V $.
    $( Membership in a range.  (Contributed by NM, 10-Jul-1994.) $)
    elrn2 $p |- ( A e. ran B <-> E. x <. x , A >. e. B ) $=
      vx cv vy cv cop cB wcel vx wex vx cv cA cop cB wcel vx wex vy cA cB crn
      elrn.1 vy cv cA wceq vx cv vy cv cop cB wcel vx cv cA cop cB wcel vx vy
      cv cA wceq vx cv vy cv cop vx cv cA cop cB vy cv cA vx cv opeq2 eleq1d
      exbidv vx vy cB dfrn3 elab2 $.

    $( Membership in a range.  (Contributed by NM, 2-Apr-2004.) $)
    elrn $p |- ( A e. ran B <-> E. x x B A ) $=
      cA cB crn wcel vx cv cA cop cB wcel vx wex vx cv cA cB wbr vx wex vx cA
      cB elrn.1 elrn2 vx cv cA cB wbr vx cv cA cop cB wcel vx vx cv cA cB df-br
      exbii bitr4i $.
  $}

  ${
    $d x y z $.  $d y z A $.
    nfrn.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for domain.  (Contributed by NM,
       30-Jan-2004.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nfdm $p |- F/_ x dom A $=
      vx cA cdm vy cv vz cv cA wbr vz wex vy cab vy vz cA df-dm vy cv vz cv cA
      wbr vz wex vx vy vy cv vz cv cA wbr vx vz vx vy cv vz cv cA vx vy cv nfcv
      nfrn.1 vx vz cv nfcv nfbr nfex nfab nfcxfr $.

    $( Bound-variable hypothesis builder for range.  (Contributed by NM,
       1-Sep-1999.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nfrn $p |- F/_ x ran A $=
      vx cA crn cA ccnv cdm cA df-rn vx cA ccnv vx cA nfrn.1 nfcnv nfdm nfcxfr
      $.
  $}

  ${
    $d A z $.  $d B z $.  $d x z $.
    $( Domain of an intersection.  (Contributed by FL, 15-Oct-2012.) $)
    dmiin $p |- dom |^|_ x e. A B C_ |^|_ x e. A dom B $=
      vx cA cB ciin cdm vx cA cB cdm ciin wss vx cA cB ciin cdm cB cdm wss vx
      cA vx cA cB cdm vx cA cB ciin cdm vx vx cA cB ciin vx cA cB nfii1 nfdm
      ssiinf vx cv cA wcel vx cA cB ciin cB wss vx cA cB ciin cdm cB cdm wss vx
      cA cB iinss2 vx cA cB ciin cB dmss syl mprgbir $.
  $}

  ${
    $d A w y $.  $d B w y $.  $d V w y $.  $d x w y $.
    $( Distribute proper substitution through the range of a class.
       (Contributed by Alan Sare, 10-Nov-2012.) $)
    csbrng $p |- ( A e. V -> [_ A / x ]_ ran B = ran [_ A / x ]_ B ) $=
      cA cV wcel vx cA vw cv vy cv cop cB wcel vw wex vy cab csb vw cv vy cv
      cop vx cA cB csb wcel vw wex vy cab vx cA cB crn csb vx cA cB csb crn cA
      cV wcel vx cA vw cv vy cv cop cB wcel vw wex vy cab csb vw cv vy cv cop
      cB wcel vw wex vx cA wsbc vy cab vw cv vy cv cop vx cA cB csb wcel vw wex
      vy cab vw cv vy cv cop cB wcel vw wex vx vy cA cV csbabg cA cV wcel vw cv
      vy cv cop cB wcel vw wex vx cA wsbc vw cv vy cv cop vx cA cB csb wcel vw
      wex vy cA cV wcel vw cv vy cv cop cB wcel vw wex vx cA wsbc vw cv vy cv
      cop cB wcel vx cA wsbc vw wex vw cv vy cv cop vx cA cB csb wcel vw wex vw
      cv vy cv cop cB wcel vw vx cA cV sbcexg cA cV wcel vw cv vy cv cop cB
      wcel vx cA wsbc vw cv vy cv cop vx cA cB csb wcel vw vx cA vw cv vy cv
      cop cB cV sbcel2g exbidv bitrd abbidv eqtrd vx cA cB crn vw cv vy cv cop
      cB wcel vw wex vy cab vw vy cB dfrn3 csbeq2i vw vy vx cA cB csb dfrn3
      3eqtr4g $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( The range of a class of ordered pairs.  (Contributed by NM,
       14-Aug-1995.)  (Revised by Mario Carneiro, 4-Dec-2016.) $)
    rnopab $p |- ran { <. x , y >. | ph } = { y | E. x ph } $=
      wph vx vy copab crn vx cv vy cv wph vx vy copab wbr vx wex vy cab wph vx
      wex vy cab vx vy wph vx vy copab wph vx vy nfopab1 wph vx vy nfopab2
      dfrnf vx cv vy cv wph vx vy copab wbr vx wex wph vx wex vy vx cv vy cv
      wph vx vy copab wbr wph vx vx cv vy cv wph vx vy copab wbr vx cv vy cv
      cop wph vx vy copab wcel wph vx cv vy cv wph vx vy copab df-br wph vx vy
      opabid bitri exbii abbii eqtri $.
  $}

  ${
    $d w y z A $.  $d w y z B $.  $d w x y z C $.
    rnmpt.1 $e |- F = ( x e. A |-> B ) $.
    $( The range of a function in maps-to notation.  (Contributed by Scott
       Fenton, 21-Mar-2011.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    rnmpt $p |- ran F = { y | E. x e. A y = B } $=
      vx cv cA wcel vy cv cB wceq wa vx vy copab crn vx cv cA wcel vy cv cB
      wceq wa vx wex vy cab cF crn vy cv cB wceq vx cA wrex vy cab vx cv cA
      wcel vy cv cB wceq wa vx vy rnopab cF vx cv cA wcel vy cv cB wceq wa vx
      vy copab cF vx cA cB cmpt vx cv cA wcel vy cv cB wceq wa vx vy copab
      rnmpt.1 vx vy cA cB df-mpt eqtri rneqi vy cv cB wceq vx cA wrex vx cv cA
      wcel vy cv cB wceq wa vx wex vy vy cv cB wceq vx cA df-rex abbii 3eqtr4i
      $.

    $( The range of a function in maps-to notation.  (Contributed by Mario
       Carneiro, 20-Feb-2015.) $)
    elrnmpt $p |- ( C e. V -> ( C e. ran F <-> E. x e. A C = B ) ) $=
      vy cv cB wceq vx cA wrex cC cB wceq vx cA wrex vy cC cF crn cV vy cv cC
      wceq vy cv cB wceq cC cB wceq vx cA vy cv cC cB eqeq1 rexbidv vx vy cA cB
      cF rnmpt.1 rnmpt elab2g $.

    ${
      $d x A $.  $d x D $.
      elrnmpt1s.1 $e |- ( x = D -> B = C ) $.
      $( Elementhood in an image set.  (Contributed by Mario Carneiro,
         12-Sep-2015.) $)
      elrnmpt1s $p |- ( ( D e. A /\ C e. V ) -> C e. ran F ) $=
        cD cA wcel cC cB wceq vx cA wrex cC cV wcel cC cF crn wcel cD cA wcel
        cC cC wceq cC cB wceq vx cA wrex cC eqid cC cB wceq cC cC wceq vx cD cA
        vx cv cD wceq cB cC cC elrnmpt1s.1 eqeq2d rspcev mpan2 cC cV wcel cC cF
        crn wcel cC cB wceq vx cA wrex vx cA cB cC cF cV rnmpt.1 elrnmpt
        biimparc sylan $.
    $}

    $( Elementhood in an image set.  (Contributed by Mario Carneiro,
       31-Aug-2015.) $)
    elrnmpt1 $p |- ( ( x e. A /\ B e. V ) -> B e. ran F ) $=
      cB cV wcel vx cv cA wcel cB cF crn wcel vx cv cA wcel cB cF crn wcel cB
      cV wcel vz cv vx vz cv cA csb wcel cB vx vz cv cB csb wceq wa vz wex vz
      cv vx vz cv cA csb wcel cB vx vz cv cB csb wceq wa vx cv cA wcel vz vx cv
      vx vex vz cv vx vz cv cA csb wcel cB vx vz cv cB csb wceq wa vx cv cA
      wcel wb vx cv vz cv vx cv vz cv wceq vx cv cA wcel vz cv vx vz cv cA csb
      wcel vz cv vx vz cv cA csb wcel cB vx vz cv cB csb wceq wa vx cv vz cv
      wceq vx cv vz cv cA vx vz cv cA csb vx cv vz cv wceq id vx vz cv cA
      csbeq1a eleq12d vx cv vz cv wceq cB vx vz cv cB csb wceq vz cv vx vz cv
      cA csb wcel vx vz cv cB csbeq1a biantrud bitr2d eqcoms spcev vy cv cB
      wceq vx cA wrex vz cv vx vz cv cA csb wcel cB vx vz cv cB csb wceq wa vz
      wex vy cB cF crn cV vy cv cB wceq vx cA wrex vz cv vx vz cv cA csb wcel
      vy cv vx vz cv cB csb wceq wa vz wex vy cv cB wceq vz cv vx vz cv cA csb
      wcel cB vx vz cv cB csb wceq wa vz wex vy cv cB wceq vx cA wrex vx cv cA
      wcel vy cv cB wceq wa vx wex vz cv vx vz cv cA csb wcel vy cv vx vz cv cB
      csb wceq wa vz wex vy cv cB wceq vx cA df-rex vx cv cA wcel vy cv cB wceq
      wa vz cv vx vz cv cA csb wcel vy cv vx vz cv cB csb wceq wa vx vz vx cv
      cA wcel vy cv cB wceq wa vz nfv vz cv vx vz cv cA csb wcel vy cv vx vz cv
      cB csb wceq vx vx vz cv vx vz cv cA csb vx vz cv cA nfcsb1v nfel2 vx vy
      cv vx vz cv cB csb vx vz cv cB nfcsb1v nfeq2 nfan vx cv vz cv wceq vx cv
      cA wcel vz cv vx vz cv cA csb wcel vy cv cB wceq vy cv vx vz cv cB csb
      wceq vx cv vz cv wceq vx cv vz cv cA vx vz cv cA csb vx cv vz cv wceq id
      vx vz cv cA csbeq1a eleq12d vx cv vz cv wceq cB vx vz cv cB csb vy cv vx
      vz cv cB csbeq1a eqeq2d anbi12d cbvex bitri vy cv cB wceq vz cv vx vz cv
      cA csb wcel vy cv vx vz cv cB csb wceq wa vz cv vx vz cv cA csb wcel cB
      vx vz cv cB csb wceq wa vz vy cv cB wceq vy cv vx vz cv cB csb wceq cB vx
      vz cv cB csb wceq vz cv vx vz cv cA csb wcel vy cv cB vx vz cv cB csb
      eqeq1 anbi2d exbidv syl5bb vx vy cA cB cF rnmpt.1 rnmpt elab2g syl5ibr
      impcom $.

    $( Membership in the range of a function.  (Contributed by NM,
       27-Aug-2007.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    elrnmptg $p |- ( A. x e. A B e. V ->
      ( C e. ran F <-> E. x e. A C = B ) ) $=
      cC cF crn wcel cC vy cv cB wceq vx cA wrex vy cab wcel cB cV wcel vx cA
      wral cC cB wceq vx cA wrex cF crn vy cv cB wceq vx cA wrex vy cab cC vx
      vy cA cB cF rnmpt.1 rnmpt eleq2i cB cV wcel vx cA wral cC cB wceq vx cA
      wrex cC cvv wcel wi cC vy cv cB wceq vx cA wrex vy cab wcel cC cB wceq vx
      cA wrex wb cB cV wcel vx cA wral cC cB wceq vx cA wrex cC cvv wcel cB cV
      wcel vx cA wral cC cB wceq vx cA wrex wa cB cV wcel cC cB wceq wa vx cA
      wrex cC cvv wcel cB cV wcel cC cB wceq vx cA r19.29 cB cV wcel cC cB wceq
      wa cC cvv wcel vx cA cB cV wcel cC cB wceq wa cC cV wcel cC cvv wcel cC
      cB wceq cC cV wcel cB cV wcel cC cB cV eleq1 biimparc cC cV elex syl
      rexlimivw syl ex vy cv cB wceq vx cA wrex cC cB wceq vx cA wrex vy cC cvv
      vy cv cC wceq vy cv cB wceq cC cB wceq vx cA vy cv cC cB eqeq1 rexbidv
      elab3g syl syl5bb $.

    elrnmpti.2 $e |- B e. _V $.
    $( Membership in the range of a function.  (Contributed by NM,
       30-Aug-2004.)  (Revised by Mario Carneiro, 31-Aug-2015.) $)
    elrnmpti $p |- ( C e. ran F <-> E. x e. A C = B ) $=
      cB cvv wcel vx cA wral cC cF crn wcel cC cB wceq vx cA wrex wb cB cvv
      wcel vx cA elrnmpti.2 rgenw vx cA cB cC cF cvv rnmpt.1 elrnmptg ax-mp $.
  $}

  ${
    $d y z w A $.  $d y z w B $.  $d w C z $.  $d w x y z $.
    $( Alternate definition of indexed union when ` B ` is a set.  (Contributed
       by Mario Carneiro, 31-Aug-2015.) $)
    dfiun3g $p |- ( A. x e. A B e. C ->
                  U_ x e. A B = U. ran ( x e. A |-> B ) ) $=
      cB cC wcel vx cA wral vx cA cB ciun vy cv cB wceq vx cA wrex vy cab cuni
      vx cA cB cmpt crn cuni vx vy cA cB cC dfiun2g vx cA cB cmpt crn vy cv cB
      wceq vx cA wrex vy cab vx vy cA cB vx cA cB cmpt vx cA cB cmpt eqid rnmpt
      unieqi syl6eqr $.

    $( Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Mario Carneiro, 31-Aug-2015.) $)
    dfiin3g $p |- ( A. x e. A B e. C
               -> |^|_ x e. A B = |^| ran ( x e. A |-> B ) ) $=
      cB cC wcel vx cA wral vx cA cB ciin vy cv cB wceq vx cA wrex vy cab cint
      vx cA cB cmpt crn cint vx vy cA cB cC dfiin2g vx cA cB cmpt crn vy cv cB
      wceq vx cA wrex vy cab vx vy cA cB vx cA cB cmpt vx cA cB cmpt eqid rnmpt
      inteqi syl6eqr $.
  $}

  ${
    dfiun3.1 $e |- B e. _V $.
    $( Alternate definition of indexed union when ` B ` is a set.  (Contributed
       by Mario Carneiro, 31-Aug-2015.) $)
    dfiun3 $p |- U_ x e. A B = U. ran ( x e. A |-> B ) $=
      cB cvv wcel vx cA cB ciun vx cA cB cmpt crn cuni wceq vx cA vx cA cB cvv
      dfiun3g cB cvv wcel vx cv cA wcel dfiun3.1 a1i mprg $.

    $( Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Mario Carneiro, 31-Aug-2015.) $)
    dfiin3 $p |- |^|_ x e. A B = |^| ran ( x e. A |-> B ) $=
      cB cvv wcel vx cA cB ciin vx cA cB cmpt crn cint wceq vx cA vx cA cB cvv
      dfiin3g cB cvv wcel vx cv cA wcel dfiun3.1 a1i mprg $.
  $}

  ${
    $d I x $.  $d S x $.  $d V k $.  $d X k $.  $d k x $.
    $( Express a relative indexed intersection as an intersection.
       (Contributed by Stefan O'Rear, 22-Feb-2015.) $)
    riinint $p |- ( ( X e. V /\ A. k e. I S C_ X ) ->
        ( X i^i |^|_ k e. I S ) = |^| ( { X } u. ran ( k e. I |-> S ) ) ) $=
      cX cV wcel cS cX wss vk cI wral wa cX vk cI cS ciin cin cX vk cI cS cmpt
      crn cint cin cX csn vk cI cS cmpt crn cun cint cX cV wcel cS cX wss vk cI
      wral wa vk cI cS ciin vk cI cS cmpt crn cint cX cX cV wcel cS cX wss vk
      cI wral wa cS cvv wcel vk cI wral vk cI cS ciin vk cI cS cmpt crn cint
      wceq cX cV wcel cS cX wss vk cI wral cS cvv wcel vk cI wral cX cV wcel cS
      cX wss cS cvv wcel vk cI cS cX wss cX cV wcel cS cvv wcel cS cX cV ssexg
      expcom ralimdv imp vk cI cS cvv dfiin3g syl ineq2d cX cV wcel cS cX wss
      vk cI wral wa cX csn vk cI cS cmpt crn cun cint cX csn cint vk cI cS cmpt
      crn cint cin cX vk cI cS cmpt crn cint cin cX csn vk cI cS cmpt crn intun
      cX cV wcel cS cX wss vk cI wral wa cX csn cint cX vk cI cS cmpt crn cint
      cX cV wcel cX csn cint cX wceq cS cX wss vk cI wral cX cV intsng adantr
      ineq1d syl5eq eqtr4d $.
  $}

  $( The range of the empty set is empty.  Part of Theorem 3.8(v) of [Monk1]
     p. 36.  (Contributed by NM, 4-Jul-1994.) $)
  rn0 $p |- ran (/) = (/) $=
    c0 cdm c0 wceq c0 crn c0 wceq dm0 c0 dm0rn0 mpbi $.

  ${
    $d x y A $.
    $( A relation is empty iff its range is empty.  (Contributed by NM,
       15-Sep-2004.) $)
    relrn0 $p |- ( Rel A -> ( A = (/) <-> ran A = (/) ) ) $=
      cA wrel cA c0 wceq cA cdm c0 wceq cA crn c0 wceq cA reldm0 cA dm0rn0
      syl6bb $.

    $( The domain and range of a class are included in its double union.
       (Contributed by NM, 13-May-2008.) $)
    dmrnssfld $p |- ( dom A u. ran A ) C_ U. U. A $=
      cA cdm cA crn cA cuni cuni vx cA cdm cA cuni cuni vx cv cA cdm wcel vx cv
      vy cv cop cA wcel vy wex vx cv cA cuni cuni wcel vy vx cv cA vx vex eldm2
      vx cv vy cv cop cA wcel vx cv cA cuni cuni wcel vy vx cv vy cv cop cA
      wcel vx cv vx cv vy cv cpr wcel vx cv cA cuni cuni wcel vx cv vy cv vx
      vex prid1 vx cv vy cv cop cA wcel vx cv vy cv cpr cA cuni cuni vx cv vx
      cv vy cv cop cA wcel vx cv vy cv cpr cA cuni wcel vx cv vy cv cpr cA cuni
      cuni wss vx cv vy cv cop cA wcel vx cv vy cv cpr vx cv vy cv cop cuni cA
      cuni vx cv vy cv vx vex vy vex uniop vx cv vy cv cA vx vex vy vex uniopel
      syl5eqelr vx cv vy cv cpr cA cuni elssuni syl sseld mpi exlimiv sylbi
      ssriv vy cA crn cA cuni cuni vy cv cA crn wcel vx cv vy cv cop cA wcel vx
      wex vy cv cA cuni cuni wcel vx vy cv cA vy vex elrn2 vx cv vy cv cop cA
      wcel vy cv cA cuni cuni wcel vx vx cv vy cv cop cA wcel vy cv vx cv vy cv
      cpr wcel vy cv cA cuni cuni wcel vx cv vy cv vy vex prid2 vx cv vy cv cop
      cA wcel vx cv vy cv cpr cA cuni cuni vy cv vx cv vy cv cop cA wcel vx cv
      vy cv cpr cA cuni wcel vx cv vy cv cpr cA cuni cuni wss vx cv vy cv cop
      cA wcel vx cv vy cv cpr vx cv vy cv cop cuni cA cuni vx cv vy cv vx vex
      vy vex uniop vx cv vy cv cA vx vex vy vex uniopel syl5eqelr vx cv vy cv
      cpr cA cuni elssuni syl sseld mpi exlimiv sylbi ssriv unssi $.
  $}

  $( The domain of a set is a set.  Corollary 6.8(2) of [TakeutiZaring] p. 26.
     (Contributed by NM, 7-Apr-1995.) $)
  dmexg $p |- ( A e. V -> dom A e. _V ) $=
    cA cV wcel cA cuni cvv wcel cA cuni cuni cvv wcel cA cdm cvv wcel cA cV
    uniexg cA cuni cvv uniexg cA cdm cA cuni cuni wss cA cuni cuni cvv wcel cA
    cdm cvv wcel cA cdm cA cdm cA crn cun cA cuni cuni cA cdm cA crn ssun1 cA
    dmrnssfld sstri cA cdm cA cuni cuni cvv ssexg mpan 3syl $.

  $( The range of a set is a set.  Corollary 6.8(3) of [TakeutiZaring] p. 26.
     Similar to Lemma 3D of [Enderton] p. 41.  (Contributed by NM,
     31-Mar-1995.) $)
  rnexg $p |- ( A e. V -> ran A e. _V ) $=
    cA cV wcel cA cuni cvv wcel cA cuni cuni cvv wcel cA crn cvv wcel cA cV
    uniexg cA cuni cvv uniexg cA crn cA cuni cuni wss cA cuni cuni cvv wcel cA
    crn cvv wcel cA crn cA cdm cA crn cun cA cuni cuni cA crn cA cdm ssun2 cA
    dmrnssfld sstri cA crn cA cuni cuni cvv ssexg mpan 3syl $.

  ${
    dmex.1 $e |- A e. _V $.
    $( The domain of a set is a set.  Corollary 6.8(2) of [TakeutiZaring]
       p. 26.  (Contributed by NM, 7-Jul-2008.) $)
    dmex $p |- dom A e. _V $=
      cA cvv wcel cA cdm cvv wcel dmex.1 cA cvv dmexg ax-mp $.

    $( The range of a set is a set.  Corollary 6.8(3) of [TakeutiZaring]
       p. 26.  Similar to Lemma 3D of [Enderton] p. 41.  (Contributed by NM,
       7-Jul-2008.) $)
    rnex $p |- ran A e. _V $=
      cA cvv wcel cA crn cvv wcel dmex.1 cA cvv rnexg ax-mp $.
  $}

  $( The identity function is a proper class.  This means, for example, that we
     cannot use it as a member of the class of continuous functions unless it
     is restricted to a set, as in ~ idcn .  (Contributed by NM,
     1-Jan-2007.) $)
  iprc $p |- -. _I e. _V $=
    cid cvv wcel cid cdm cvv wcel cid cdm cvv wcel cvv cvv wcel vprc cid cdm
    cvv cvv dmi eleq1i mtbir cid cvv dmexg mto $.

  ${
    $d x y z A $.  $d x y z B $.
    $( Domain of a composition.  Theorem 21 of [Suppes] p. 63.  (Contributed by
       NM, 19-Mar-1998.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    dmcoss $p |- dom ( A o. B ) C_ dom B $=
      vx cA cB ccom cdm cB cdm vx cv vy cv cop cA cB ccom wcel vy wex vx cv vy
      cv cB wbr vy wex vx cv cA cB ccom cdm wcel vx cv cB cdm wcel vx cv vy cv
      cop cA cB ccom wcel vx cv vy cv cB wbr vy wex vy vx cv vy cv cB wbr vy
      nfe1 vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx cv vz cv cB wbr
      vz wex vx cv vy cv cop cA cB ccom wcel vx cv vy cv cB wbr vy wex vx cv vz
      cv cB wbr vz cv vy cv cA wbr vz exsimpl vz vx cv vy cv cA cB vx vex vy
      vex opelco vx cv vy cv cB wbr vx cv vz cv cB wbr vy vz vy cv vz cv vx cv
      cB breq2 cbvexv 3imtr4i exlimi vy vx cv cA cB ccom vx vex eldm2 vy vx cv
      cB vx vex eldm 3imtr4i ssriv $.
  $}

  $( Range of a composition.  (Contributed by NM, 19-Mar-1998.) $)
  rncoss $p |- ran ( A o. B ) C_ ran A $=
    cB ccnv cA ccnv ccom cdm cA ccnv cdm cA cB ccom crn cA crn cB ccnv cA ccnv
    dmcoss cA cB ccom crn cA cB ccom ccnv cdm cB ccnv cA ccnv ccom cdm cA cB
    ccom df-rn cA cB ccom ccnv cB ccnv cA ccnv ccom cA cB cnvco dmeqi eqtri cA
    df-rn 3sstr4i $.

  ${
    $d x y z A $.  $d x y z B $.
    $( Domain of a composition.  (Contributed by NM, 28-May-1998.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    dmcosseq $p |- ( ran B C_ dom A -> dom ( A o. B ) = dom B ) $=
      cB crn cA cdm wss cA cB ccom cdm cB cdm cA cB ccom cdm cB cdm wss cB crn
      cA cdm wss cA cB dmcoss a1i cB crn cA cdm wss vx cB cdm cA cB ccom cdm cB
      crn cA cdm wss vx cv vy cv cB wbr vy wex vx cv vz cv cop cA cB ccom wcel
      vz wex vx cv cB cdm wcel vx cv cA cB ccom cdm wcel cB crn cA cdm wss vx
      cv vy cv cB wbr vy wex vx cv vy cv cB wbr vy cv vz cv cA wbr wa vy wex vz
      wex vx cv vz cv cop cA cB ccom wcel vz wex cB crn cA cdm wss vx cv vy cv
      cB wbr vy wex vx cv vy cv cB wbr vy cv vz cv cA wbr wa vz wex vy wex vx
      cv vy cv cB wbr vy cv vz cv cA wbr wa vy wex vz wex cB crn cA cdm wss vx
      cv vy cv cB wbr vx cv vy cv cB wbr vy cv vz cv cA wbr wa vz wex vy cB crn
      cA cdm wss vy cv cB crn wcel vy cv cA cdm wcel wi vx cv vy cv cB wbr vx
      cv vy cv cB wbr vy cv vz cv cA wbr wa vz wex wi cB crn cA cdm vy cv ssel
      vy cv cB crn wcel vy cv cA cdm wcel wi vx cv vy cv cB wbr vx wex vy cv vz
      cv cA wbr vz wex wi vx cv vy cv cB wbr vx cv vy cv cB wbr vy cv vz cv cA
      wbr wa vz wex wi vy cv cB crn wcel vx cv vy cv cB wbr vx wex vy cv cA cdm
      wcel vy cv vz cv cA wbr vz wex vx vy cv cB vy vex elrn vz vy cv cA vy vex
      eldm imbi12i vx cv vy cv cB wbr vx wex vy cv vz cv cA wbr vz wex wi vx cv
      vy cv cB wbr vy cv vz cv cA wbr vz wex vx cv vy cv cB wbr vy cv vz cv cA
      wbr wa vz wex vx cv vy cv cB wbr vx cv vy cv cB wbr vx wex vy cv vz cv cA
      wbr vz wex vx cv vy cv cB wbr vx 19.8a imim1i vx cv vy cv cB wbr vy cv vz
      cv cA wbr vx cv vy cv cB wbr vy cv vz cv cA wbr wa vz vx cv vy cv cB wbr
      vy cv vz cv cA wbr pm3.2 eximdv sylcom sylbi syl eximdv vx cv vy cv cB
      wbr vy cv vz cv cA wbr wa vz vy excom syl6ibr vx cv vz cv cop cA cB ccom
      wcel vx cv vy cv cB wbr vy cv vz cv cA wbr wa vy wex vz vy vx cv vz cv cA
      cB vx vex vz vex opelco exbii syl6ibr vy vx cv cB vx vex eldm vz vx cv cA
      cB ccom vx vex eldm2 3imtr4g ssrdv eqssd $.

    $( Domain of a composition.  (Contributed by NM, 19-Mar-1998.) $)
    dmcoeq $p |- ( dom A = ran B -> dom ( A o. B ) = dom B ) $=
      cA cdm cB crn wceq cB crn cA cdm wss cA cB ccom cdm cB cdm wceq cB crn cA
      cdm eqimss2 cA cB dmcosseq syl $.
  $}

  $( Range of a composition.  (Contributed by NM, 19-Mar-1998.) $)
  rncoeq $p |- ( dom A = ran B -> ran ( A o. B ) = ran A ) $=
    cB ccnv cdm cA ccnv crn wceq cB ccnv cA ccnv ccom cdm cA ccnv cdm wceq cA
    cdm cB crn wceq cA cB ccom crn cA crn wceq cB ccnv cA ccnv dmcoeq cA cdm cB
    crn wceq cB crn cA cdm wceq cB ccnv cdm cA ccnv crn wceq cA cdm cB crn
    eqcom cB crn cB ccnv cdm cA cdm cA ccnv crn cB df-rn cA dfdm4 eqeq12i bitri
    cA cB ccom crn cB ccnv cA ccnv ccom cdm cA crn cA ccnv cdm cA cB ccom crn
    cA cB ccom ccnv cdm cB ccnv cA ccnv ccom cdm cA cB ccom df-rn cA cB ccom
    ccnv cB ccnv cA ccnv ccom cA cB cnvco dmeqi eqtri cA df-rn eqeq12i 3imtr4i
    $.

  $( Equality theorem for restrictions.  (Contributed by NM, 7-Aug-1994.) $)
  reseq1 $p |- ( A = B -> ( A |` C ) = ( B |` C ) ) $=
    cA cB wceq cA cC cvv cxp cin cB cC cvv cxp cin cA cC cres cB cC cres cA cB
    cC cvv cxp ineq1 cA cC df-res cB cC df-res 3eqtr4g $.

  $( Equality theorem for restrictions.  (Contributed by NM, 8-Aug-1994.) $)
  reseq2 $p |- ( A = B -> ( C |` A ) = ( C |` B ) ) $=
    cA cB wceq cC cA cvv cxp cin cC cB cvv cxp cin cC cA cres cC cB cres cA cB
    wceq cA cvv cxp cB cvv cxp cC cA cB cvv xpeq1 ineq2d cC cA df-res cC cB
    df-res 3eqtr4g $.

  ${
    reseqi.1 $e |- A = B $.
    $( Equality inference for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
    reseq1i $p |- ( A |` C ) = ( B |` C ) $=
      cA cB wceq cA cC cres cB cC cres wceq reseqi.1 cA cB cC reseq1 ax-mp $.

    $( Equality inference for restrictions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    reseq2i $p |- ( C |` A ) = ( C |` B ) $=
      cA cB wceq cC cA cres cC cB cres wceq reseqi.1 cA cB cC reseq2 ax-mp $.

    reseqi.2 $e |- C = D $.
    $( Equality inference for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
    reseq12i $p |- ( A |` C ) = ( B |` D ) $=
      cA cC cres cB cC cres cB cD cres cA cB cC reseqi.1 reseq1i cC cD cB
      reseqi.2 reseq2i eqtri $.
  $}

  ${
    reseqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
    reseq1d $p |- ( ph -> ( A |` C ) = ( B |` C ) ) $=
      wph cA cB wceq cA cC cres cB cC cres wceq reseqd.1 cA cB cC reseq1 syl $.

    $( Equality deduction for restrictions.  (Contributed by Paul Chapman,
       22-Jun-2011.) $)
    reseq2d $p |- ( ph -> ( C |` A ) = ( C |` B ) ) $=
      wph cA cB wceq cC cA cres cC cB cres wceq reseqd.1 cA cB cC reseq2 syl $.

    reseqd.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for restrictions.  (Contributed by NM,
       21-Oct-2014.) $)
    reseq12d $p |- ( ph -> ( A |` C ) = ( B |` D ) ) $=
      wph cA cC cres cB cC cres cB cD cres wph cA cB cC reseqd.1 reseq1d wph cC
      cD cB reseqd.2 reseq2d eqtrd $.
  $}

  ${
    $d y B $.  $d x y $.
    nfres.1 $e |- F/_ x A $.
    nfres.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for restriction.  (Contributed by NM,
       15-Sep-2003.)  (Revised by David Abernethy, 19-Jun-2012.) $)
    nfres $p |- F/_ x ( A |` B ) $=
      vx cA cB cres cA cB cvv cxp cin cA cB df-res vx cA cB cvv cxp nfres.1 vx
      cB cvv nfres.2 vx cvv nfcv nfxp nfin nfcxfr $.
  $}

  $( Distribute proper substitution through the restriction of a class.
     ~ csbresg is derived from the virtual deduction proof ~ csbresgVD .
     (Contributed by Alan Sare, 10-Nov-2012.) $)
  csbresg $p |- ( A e. V -> [_ A / x ]_ ( B |` C ) =
                 ( [_ A / x ]_ B |` [_ A / x ]_ C ) ) $=
    cA cV wcel vx cA cB cC cvv cxp cin csb vx cA cB csb vx cA cC csb cvv cxp
    cin vx cA cB cC cres csb vx cA cB csb vx cA cC csb cres cA cV wcel vx cA cB
    cC cvv cxp cin csb vx cA cB csb vx cA cC cvv cxp csb cin vx cA cB csb vx cA
    cC csb cvv cxp cin vx cA cV cB cC cvv cxp csbing cA cV wcel vx cA cC cvv
    cxp csb vx cA cC csb cvv cxp vx cA cB csb cA cV wcel vx cA cC cvv cxp csb
    vx cA cC csb vx cA cvv csb cxp vx cA cC csb cvv cxp vx cA cC cvv cV csbxpg
    cA cV wcel vx cA cvv csb cvv vx cA cC csb vx cA cvv cV csbconstg xpeq2d
    eqtrd ineq2d eqtrd vx cA cB cC cres cB cC cvv cxp cin cB cC df-res csbeq2i
    vx cA cB csb vx cA cC csb df-res 3eqtr4g $.

  $( A restriction to the empty set is empty.  (Contributed by NM,
     12-Nov-1994.) $)
  res0 $p |- ( A |` (/) ) = (/) $=
    cA c0 cres cA c0 cvv cxp cin cA c0 cin c0 cA c0 df-res c0 cvv cxp c0 cA cvv
    xp0r ineq2i cA in0 3eqtri $.

  ${
    opelres.1 $e |- B e. _V $.
    $( Ordered pair membership in a restriction.  Exercise 13 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 13-Nov-1995.) $)
    opelres $p |- ( <. A , B >. e. ( C |` D ) <->
                    ( <. A , B >. e. C /\ A e. D ) ) $=
      cA cB cop cC cD cres wcel cA cB cop cC cD cvv cxp cin wcel cA cB cop cC
      wcel cA cB cop cD cvv cxp wcel wa cA cB cop cC wcel cA cD wcel wa cC cD
      cres cC cD cvv cxp cin cA cB cop cC cD df-res eleq2i cA cB cop cC cD cvv
      cxp elin cA cB cop cD cvv cxp wcel cA cD wcel cA cB cop cC wcel cA cB cop
      cD cvv cxp wcel cA cD wcel cB cvv wcel opelres.1 cA cB cD cvv opelxp
      mpbiran2 anbi2i 3bitri $.

    $( Binary relation on a restriction.  (Contributed by NM, 12-Dec-2006.) $)
    brres $p |- ( A ( C |` D ) B <-> ( A C B /\ A e. D ) ) $=
      cA cB cop cC cD cres wcel cA cB cop cC wcel cA cD wcel wa cA cB cC cD
      cres wbr cA cB cC wbr cA cD wcel wa cA cB cC cD opelres.1 opelres cA cB
      cC cD cres df-br cA cB cC wbr cA cB cop cC wcel cA cD wcel cA cB cC df-br
      anbi1i 3bitr4i $.
  $}

  ${
    $d y A $.  $d y B $.  $d y C $.  $d y D $.
    $( Ordered pair membership in a restriction.  Exercise 13 of
       [TakeutiZaring] p. 25.  (Contributed by NM, 14-Oct-2005.) $)
    opelresg $p |- ( B e. V -> ( <. A , B >. e. ( C |` D ) <->
                    ( <. A , B >. e. C /\ A e. D ) ) ) $=
      cA vy cv cop cC cD cres wcel cA vy cv cop cC wcel cA cD wcel wa cA cB cop
      cC cD cres wcel cA cB cop cC wcel cA cD wcel wa vy cB cV vy cv cB wceq cA
      vy cv cop cA cB cop cC cD cres vy cv cB cA opeq2 eleq1d vy cv cB wceq cA
      vy cv cop cC wcel cA cB cop cC wcel cA cD wcel vy cv cB wceq cA vy cv cop
      cA cB cop cC vy cv cB cA opeq2 eleq1d anbi1d cA vy cv cC cD vy vex
      opelres vtoclbg $.

    $( Binary relation on a restriction.  (Contributed by Mario Carneiro,
       4-Nov-2015.) $)
    brresg $p |- ( B e. V -> ( A ( C |` D ) B <-> ( A C B /\ A e. D ) ) ) $=
      cB cV wcel cA cB cop cC cD cres wcel cA cB cop cC wcel cA cD wcel wa cA
      cB cC cD cres wbr cA cB cC wbr cA cD wcel wa cA cB cC cD cV opelresg cA
      cB cC cD cres df-br cA cB cC wbr cA cB cop cC wcel cA cD wcel cA cB cC
      df-br anbi1i 3bitr4g $.
  $}

  ${
    opres.1 $e |- B e. _V $.
    $( Ordered pair membership in a restriction when the first member belongs
       to the restricting class.  (Contributed by NM, 30-Apr-2004.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    opres $p |- ( A e. D ->
                    ( <. A , B >. e. ( C |` D ) <-> <. A , B >. e. C ) ) $=
      cA cB cop cC cD cres wcel cA cB cop cC wcel cA cD wcel cA cB cC cD
      opres.1 opelres rbaib $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( A restricted identity relation is equivalent to equality in its domain.
       (Contributed by NM, 30-Apr-2004.) $)
    resieq $p |- ( ( B e. A /\ C e. A ) -> ( B ( _I |` A ) C <-> B = C ) ) $=
      cC cA wcel cB cA wcel cB cC cid cA cres wbr cB cC wceq wb cB cA wcel cB
      vx cv cid cA cres wbr cB vx cv wceq wb wi cB cA wcel cB cC cid cA cres
      wbr cB cC wceq wb wi vx cC cA vx cv cC wceq cB vx cv cid cA cres wbr cB
      vx cv wceq wb cB cC cid cA cres wbr cB cC wceq wb cB cA wcel vx cv cC
      wceq cB vx cv cid cA cres wbr cB cC cid cA cres wbr cB vx cv wceq cB cC
      wceq vx cv cC cB cid cA cres breq2 vx cv cC cB eqeq2 bibi12d imbi2d cB cA
      wcel cB vx cv cop cid cA cres wcel cB vx cv cop cid wcel cB vx cv cid cA
      cres wbr cB vx cv wceq cB vx cv cid cA vx vex opres cB vx cv cid cA cres
      df-br cB vx cv wceq cB vx cv cid wbr cB vx cv cop cid wcel cB vx cv vx
      vex ideq cB vx cv cid df-br bitr3i 3bitr4g vtoclg impcom $.
  $}

  $( ` <. A , A >. ` belongs to a restriction of the identity class iff ` A `
     belongs to the restricting class.  (Contributed by FL, 27-Oct-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  opelresiOLD $p |- ( A e. V -> ( A e. B <-> <. A , A >. e. ( _I |` B ) ) ) $=
    cA cV wcel cA cB wcel cA cA cop cid wcel cA cB wcel wa cA cA cop cid cB
    cres wcel cA cV wcel cA cA cop cid wcel cA cB wcel cA cV wcel cA cA cid wbr
    cA cA cop cid wcel cA cV ididg cA cA cid df-br sylib biantrurd cA cA cid cB
    cV opelresg bitr4d $.

  $( ` <. A , A >. ` belongs to a restriction of the identity class iff ` A `
     belongs to the restricting class.  (Contributed by FL, 27-Oct-2008.)
     (Revised by NM, 30-Mar-2016.) $)
  opelresi $p |- ( A e. V -> ( <. A , A >. e. ( _I |` B ) <-> A e. B ) ) $=
    cA cV wcel cA cA cop cid cB cres wcel cA cA cop cid wcel cA cB wcel wa cA
    cB wcel cA cA cid cB cV opelresg cA cV wcel cA cA cop cid wcel cA cB wcel
    cA cV wcel cA cA cid wbr cA cA cop cid wcel cA cV ididg cA cA cid df-br
    sylib biantrurd bitr4d $.

  $( The restriction of a restriction.  (Contributed by NM, 27-Mar-2008.) $)
  resres $p |- ( ( A |` B ) |` C ) = ( A |` ( B i^i C ) ) $=
    cA cB cres cC cres cA cB cres cC cvv cxp cin cA cB cvv cxp cin cC cvv cxp
    cin cA cB cC cin cres cA cB cres cC df-res cA cB cres cA cB cvv cxp cin cC
    cvv cxp cA cB df-res ineq1i cA cB cC cin cvv cxp cin cA cB cvv cxp cC cvv
    cxp cin cin cA cB cC cin cres cA cB cvv cxp cin cC cvv cxp cin cB cC cin
    cvv cxp cB cvv cxp cC cvv cxp cin cA cB cC cvv xpindir ineq2i cA cB cC cin
    df-res cA cB cvv cxp cC cvv cxp inass 3eqtr4ri 3eqtri $.

  $( Distributive law for restriction over union.  Theorem 31 of [Suppes]
     p. 65.  (Contributed by NM, 30-Sep-2002.) $)
  resundi $p |- ( A |` ( B u. C ) ) = ( ( A |` B ) u. ( A |` C ) ) $=
    cA cB cC cun cvv cxp cin cA cB cvv cxp cin cA cC cvv cxp cin cun cA cB cC
    cun cres cA cB cres cA cC cres cun cA cB cC cun cvv cxp cin cA cB cvv cxp
    cC cvv cxp cun cin cA cB cvv cxp cin cA cC cvv cxp cin cun cB cC cun cvv
    cxp cB cvv cxp cC cvv cxp cun cA cB cC cvv xpundir ineq2i cA cB cvv cxp cC
    cvv cxp indi eqtri cA cB cC cun df-res cA cB cres cA cB cvv cxp cin cA cC
    cres cA cC cvv cxp cin cA cB df-res cA cC df-res uneq12i 3eqtr4i $.

  $( Distributive law for restriction over union.  (Contributed by NM,
     23-Sep-2004.) $)
  resundir $p |- ( ( A u. B ) |` C ) = ( ( A |` C ) u. ( B |` C ) ) $=
    cA cB cun cC cvv cxp cin cA cC cvv cxp cin cB cC cvv cxp cin cun cA cB cun
    cC cres cA cC cres cB cC cres cun cA cB cC cvv cxp indir cA cB cun cC
    df-res cA cC cres cA cC cvv cxp cin cB cC cres cB cC cvv cxp cin cA cC
    df-res cB cC df-res uneq12i 3eqtr4i $.

  $( Class restriction distributes over intersection.  (Contributed by FL,
     6-Oct-2008.) $)
  resindi $p |- ( A |` ( B i^i C ) ) = ( ( A |` B ) i^i ( A |` C ) ) $=
    cA cB cC cin cvv cxp cin cA cB cvv cxp cin cA cC cvv cxp cin cin cA cB cC
    cin cres cA cB cres cA cC cres cin cA cB cC cin cvv cxp cin cA cB cvv cxp
    cC cvv cxp cin cin cA cB cvv cxp cin cA cC cvv cxp cin cin cB cC cin cvv
    cxp cB cvv cxp cC cvv cxp cin cA cB cC cvv xpindir ineq2i cA cB cvv cxp cC
    cvv cxp inindi eqtri cA cB cC cin df-res cA cB cres cA cB cvv cxp cin cA cC
    cres cA cC cvv cxp cin cA cB df-res cA cC df-res ineq12i 3eqtr4i $.

  $( Class restriction distributes over intersection.  (Contributed by NM,
     18-Dec-2008.) $)
  resindir $p |- ( ( A i^i B ) |` C ) = ( ( A |` C ) i^i ( B |` C ) ) $=
    cA cB cin cC cvv cxp cin cA cC cvv cxp cin cB cC cvv cxp cin cin cA cB cin
    cC cres cA cC cres cB cC cres cin cA cB cC cvv cxp inindir cA cB cin cC
    df-res cA cC cres cA cC cvv cxp cin cB cC cres cB cC cvv cxp cin cA cC
    df-res cB cC df-res ineq12i 3eqtr4i $.

  $( Move intersection into class restriction.  (Contributed by NM,
     18-Dec-2008.) $)
  inres $p |- ( A i^i ( B |` C ) ) = ( ( A i^i B ) |` C ) $=
    cA cB cin cC cvv cxp cin cA cB cC cvv cxp cin cin cA cB cin cC cres cA cB
    cC cres cin cA cB cC cvv cxp inass cA cB cin cC df-res cB cC cres cB cC cvv
    cxp cin cA cB cC df-res ineq2i 3eqtr4ri $.

  ${
    $d x C $.
    $( Distribution of restriction over indexed union.  (Contributed by Mario
       Carneiro, 29-May-2015.) $)
    resiun1 $p |- ( U_ x e. A B |` C ) = U_ x e. A ( B |` C ) $=
      vx cA cC cvv cxp cB cin ciun cC cvv cxp vx cA cB ciun cin vx cA cB cC
      cres ciun vx cA cB ciun cC cres vx cA cC cvv cxp cB iunin2 vx cA cB cC
      cres cC cvv cxp cB cin cB cC cres cC cvv cxp cB cin wceq vx cv cA wcel cB
      cC cres cB cC cvv cxp cin cC cvv cxp cB cin cB cC df-res cB cC cvv cxp
      incom eqtri a1i iuneq2i vx cA cB ciun cC cres vx cA cB ciun cC cvv cxp
      cin cC cvv cxp vx cA cB ciun cin vx cA cB ciun cC df-res vx cA cB ciun cC
      cvv cxp incom eqtri 3eqtr4ri $.

    $( Distribution of restriction over indexed union.  (Contributed by Mario
       Carneiro, 29-May-2015.) $)
    resiun2 $p |- ( C |` U_ x e. A B ) = U_ x e. A ( C |` B ) $=
      cC vx cA cB ciun cres cC vx cA cB ciun cvv cxp cin vx cA cC cB cres ciun
      cC vx cA cB ciun df-res vx cA cC cB cres ciun vx cA cC cB cvv cxp cin
      ciun cC vx cA cB ciun cvv cxp cin vx cA cC cB cres cC cB cvv cxp cin cC
      cB cres cC cB cvv cxp cin wceq vx cv cA wcel cC cB df-res a1i iuneq2i cC
      vx cA cB ciun cvv cxp cin cC vx cA cB cvv cxp ciun cin vx cA cC cB cvv
      cxp cin ciun vx cA cB ciun cvv cxp vx cA cB cvv cxp ciun cC vx cA cB cvv
      xpiundir ineq2i vx cA cC cB cvv cxp iunin2 eqtr4i eqtr4i eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The domain of a restriction.  Exercise 14 of [TakeutiZaring] p. 25.
       (Contributed by NM, 1-Aug-1994.) $)
    dmres $p |- dom ( A |` B ) = ( B i^i dom A ) $=
      cA cdm cB cin cA cB cres cdm cB cA cdm cin vx cA cdm cB cA cB cres cdm vx
      cv cA cB cres cdm wcel vx cv vy cv cop cA cB cres wcel vy wex vx cv cA
      cdm wcel vx cv cB wcel wa vy vx cv cA cB cres vx vex eldm2 vx cv vy cv
      cop cA wcel vx cv cB wcel wa vy wex vx cv vy cv cop cA wcel vy wex vx cv
      cB wcel wa vx cv vy cv cop cA cB cres wcel vy wex vx cv cA cdm wcel vx cv
      cB wcel wa vx cv vy cv cop cA wcel vx cv cB wcel vy 19.41v vx cv vy cv
      cop cA cB cres wcel vx cv vy cv cop cA wcel vx cv cB wcel wa vy vx cv vy
      cv cA cB vy vex opelres exbii vx cv cA cdm wcel vx cv vy cv cop cA wcel
      vy wex vx cv cB wcel vy vx cv cA vx vex eldm2 anbi1i 3bitr4i bitr2i
      ineqri cA cdm cB incom eqtr3i $.
  $}

  $( A domain restricted to a subclass equals the subclass.  (Contributed by
     NM, 2-Mar-1997.) $)
  ssdmres $p |- ( A C_ dom B <-> dom ( B |` A ) = A ) $=
    cA cB cdm wss cA cB cdm cin cA wceq cB cA cres cdm cA wceq cA cB cdm df-ss
    cB cA cres cdm cA cB cdm cin cA cB cA dmres eqeq1i bitr4i $.

  $( The domain of a restriction to a set exists.  (Contributed by NM,
     7-Apr-1995.) $)
  dmresexg $p |- ( B e. V -> dom ( A |` B ) e. _V ) $=
    cB cV wcel cA cB cres cdm cB cA cdm cin cvv cA cB dmres cB cA cdm cV inex1g
    syl5eqel $.

  $( A class includes its restriction.  Exercise 15 of [TakeutiZaring] p. 25.
     (Contributed by NM, 2-Aug-1994.) $)
  resss $p |- ( A |` B ) C_ A $=
    cA cB cres cA cB cvv cxp cin cA cA cB df-res cA cB cvv cxp inss1 eqsstri $.

  $( Commutative law for restriction.  (Contributed by NM, 27-Mar-1998.) $)
  rescom $p |- ( ( A |` B ) |` C ) = ( ( A |` C ) |` B ) $=
    cA cB cC cin cres cA cC cB cin cres cA cB cres cC cres cA cC cres cB cres
    cB cC cin cC cB cin cA cB cC incom reseq2i cA cB cC resres cA cC cB resres
    3eqtr4i $.

  $( Subclass theorem for restriction.  (Contributed by NM, 16-Aug-1994.) $)
  ssres $p |- ( A C_ B -> ( A |` C ) C_ ( B |` C ) ) $=
    cA cB wss cA cC cvv cxp cin cB cC cvv cxp cin cA cC cres cB cC cres cA cB
    cC cvv cxp ssrin cA cC df-res cB cC df-res 3sstr4g $.

  $( Subclass theorem for restriction.  (Contributed by NM, 22-Mar-1998.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  ssres2 $p |- ( A C_ B -> ( C |` A ) C_ ( C |` B ) ) $=
    cA cB wss cC cA cvv cxp cin cC cB cvv cxp cin cC cA cres cC cB cres cA cB
    wss cA cvv cxp cB cvv cxp wss cC cA cvv cxp cin cC cB cvv cxp cin wss cA cB
    cvv xpss1 cA cvv cxp cB cvv cxp cC sslin syl cC cA df-res cC cB df-res
    3sstr4g $.

  $( A restriction is a relation.  Exercise 12 of [TakeutiZaring] p. 25.
     (Contributed by NM, 2-Aug-1994.)  (Proof shortened by Andrew Salmon,
     27-Aug-2011.) $)
  relres $p |- Rel ( A |` B ) $=
    cA cB cres cB cvv cxp wss cB cvv cxp wrel cA cB cres wrel cA cB cres cA cB
    cvv cxp cin cB cvv cxp cA cB df-res cA cB cvv cxp inss2 eqsstri cB cvv
    relxp cA cB cres cB cvv cxp relss mp2 $.

  $( Absorption law for restriction.  Exercise 17 of [TakeutiZaring] p. 25.
     (Contributed by NM, 9-Aug-1994.) $)
  resabs1 $p |- ( B C_ C -> ( ( A |` C ) |` B ) = ( A |` B ) ) $=
    cB cC wss cA cC cres cB cres cA cC cB cin cres cA cB cres cA cC cB resres
    cB cC wss cC cB cin cB wceq cA cC cB cin cres cA cB cres wceq cB cC sseqin2
    cC cB cin cB cA reseq2 sylbi syl5eq $.

  $( Absorption law for restriction.  (Contributed by NM, 27-Mar-1998.) $)
  resabs2 $p |- ( B C_ C -> ( ( A |` B ) |` C ) = ( A |` B ) ) $=
    cB cC wss cA cB cres cC cres cA cC cres cB cres cA cB cres cA cB cC rescom
    cA cB cC resabs1 syl5eq $.

  $( Idempotent law for restriction.  (Contributed by NM, 27-Mar-1998.) $)
  residm $p |- ( ( A |` B ) |` B ) = ( A |` B ) $=
    cB cB wss cA cB cres cB cres cA cB cres wceq cB ssid cA cB cB resabs2 ax-mp
    $.

  $( A restriction to an image.  (Contributed by NM, 29-Sep-2004.) $)
  resima $p |- ( ( A |` B ) " B ) = ( A " B ) $=
    cA cB cres cB cres crn cA cB cres crn cA cB cres cB cima cA cB cima cA cB
    cres cB cres cA cB cres cA cB residm rneqi cA cB cres cB df-ima cA cB
    df-ima 3eqtr4i $.

  $( Image under a restricted class.  (Contributed by FL, 31-Aug-2009.) $)
  resima2 $p |- ( B C_ C -> ( ( A |` C ) " B ) = ( A " B ) ) $=
    cB cC wss cA cC cres cB cima cA cC cres cB cres crn cA cB cima cA cC cres
    cB df-ima cB cC wss cA cC cres cB cres crn cA cC cB cin cres crn cA cB cima
    cA cC cres cB cres cA cC cB cin cres cA cC cB resres rneqi cB cC wss cB cC
    cin cB wceq cA cC cB cin cres crn cA cB cima wceq cB cC df-ss cB cC cin cB
    wceq cA cC cB cin cres crn cA cB cC cin cres crn cA cB cima cB cC cin cB
    wceq cA cC cB cin cres cA cB cC cin cres cB cC cin cB wceq cC cB cin cB cC
    cin cA cC cB cin cB cC cin wceq cB cC cin cB wceq cC cB incom a1i reseq2d
    rneqd cB cC cin cB wceq cA cB cC cin cres crn cA cB cres crn cA cB cima cB
    cC cin cB wceq cA cB cC cin cres cA cB cres cB cC cin cB cA reseq2 rneqd cA
    cB df-ima syl6eqr eqtrd sylbi syl5eq syl5eq $.

  $( Restriction of a constant function (or other cross product).  (Contributed
     by Stefan O'Rear, 24-Jan-2015.) $)
  xpssres $p |- ( C C_ A -> ( ( A X. B ) |` C ) = ( C X. B ) ) $=
    cC cA wss cA cB cxp cC cres cC cA cin cB cxp cC cB cxp cA cB cxp cC cres cA
    cB cxp cC cvv cxp cin cA cC cin cB cvv cin cxp cC cA cin cB cxp cA cB cxp
    cC df-res cA cB cC cvv inxp cA cC cin cC cA cin cB cvv cin cB cA cC incom
    cB inv1 xpeq12i 3eqtri cC cA wss cC cA cin cC cB cC cA wss cC cA cin cC
    wceq cC cA df-ss biimpi xpeq1d syl5eq $.

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Membership in a restriction.  (Contributed by Scott Fenton,
       17-Mar-2011.) $)
    elres $p |- ( A e. ( B |` C )
          <-> E. x e. C E. y ( A = <. x , y >. /\ <. x , y >. e. B ) ) $=
      cA cB cC cres wcel cA vx cv vy cv cop wceq vx cv vy cv cop cB wcel wa vy
      wex vx cC wrex cA cB cC cres wcel vx cv cC wcel cA vx cv vy cv cop wceq
      vx cv vy cv cop cB wcel wa wa vy wex vx wex cA vx cv vy cv cop wceq vx cv
      vy cv cop cB wcel wa vy wex vx cC wrex cA cB cC cres wcel cA vx cv vy cv
      cop wceq vy wex vx wex vx cv cC wcel cA vx cv vy cv cop wceq vx cv vy cv
      cop cB wcel wa wa vy wex vx wex cB cC cres wrel cA cB cC cres wcel cA vx
      cv vy cv cop wceq vy wex vx wex cB cC relres vx vy cA cB cC cres elrel
      mpan cA cB cC cres wcel cA vx cv vy cv cop wceq vx cv cC wcel cA vx cv vy
      cv cop wceq vx cv vy cv cop cB wcel wa wa vx vy cA cB cC cres wcel cA vx
      cv vy cv cop wceq cA vx cv vy cv cop wceq vx cv cC wcel vx cv vy cv cop
      cB wcel wa wa vx cv cC wcel cA vx cv vy cv cop wceq vx cv vy cv cop cB
      wcel wa wa cA cB cC cres wcel cA vx cv vy cv cop wceq vx cv cC wcel vx cv
      vy cv cop cB wcel wa cA vx cv vy cv cop wceq cA cB cC cres wcel vx cv vy
      cv cop cB cC cres wcel vx cv cC wcel vx cv vy cv cop cB wcel wa cA vx cv
      vy cv cop wceq cA cB cC cres wcel vx cv vy cv cop cB cC cres wcel cA vx
      cv vy cv cop cB cC cres eleq1 biimpd vx cv vy cv cop cB cC cres wcel vx
      cv vy cv cop cB wcel vx cv cC wcel vx cv vy cv cop cB cC cres wcel vx cv
      vy cv cop cB wcel vx cv cC wcel wa vx cv vy cv cB cC vy vex opelres
      biimpi ancomd syl6com ancld cA vx cv vy cv cop wceq vx cv cC wcel vx cv
      vy cv cop cB wcel an12 syl6ib 2eximdv mpd cA vx cv vy cv cop wceq vx cv
      vy cv cop cB wcel wa vy wex vx cC wrex cA vx cv vy cv cop wceq vx cv vy
      cv cop cB wcel wa vx cC wrex vy wex vx cv cC wcel cA vx cv vy cv cop wceq
      vx cv vy cv cop cB wcel wa wa vx wex vy wex vx cv cC wcel cA vx cv vy cv
      cop wceq vx cv vy cv cop cB wcel wa wa vy wex vx wex cA vx cv vy cv cop
      wceq vx cv vy cv cop cB wcel wa vx vy cC rexcom4 cA vx cv vy cv cop wceq
      vx cv vy cv cop cB wcel wa vx cC wrex vx cv cC wcel cA vx cv vy cv cop
      wceq vx cv vy cv cop cB wcel wa wa vx wex vy cA vx cv vy cv cop wceq vx
      cv vy cv cop cB wcel wa vx cC df-rex exbii vx cv cC wcel cA vx cv vy cv
      cop wceq vx cv vy cv cop cB wcel wa wa vy vx excom 3bitri sylibr cA vx cv
      vy cv cop wceq vx cv vy cv cop cB wcel wa vy wex cA cB cC cres wcel vx cC
      vx cv cC wcel cA vx cv vy cv cop wceq vx cv vy cv cop cB wcel wa cA cB cC
      cres wcel vy vx cv cC wcel cA vx cv vy cv cop wceq vx cv vy cv cop cB
      wcel cA cB cC cres wcel vx cv cC wcel vx cv vy cv cop cB wcel vx cv vy cv
      cop cB cC cres wcel cA vx cv vy cv cop wceq cA cB cC cres wcel vx cv vy
      cv cop cB cC cres wcel vx cv vy cv cop cB wcel vx cv cC wcel vx cv vy cv
      cB cC vy vex opelres simplbi2com cA vx cv vy cv cop wceq cA cB cC cres
      wcel vx cv vy cv cop cB cC cres wcel cA vx cv vy cv cop cB cC cres eleq1
      biimprd syl9 imp3a exlimdv rexlimiv impbii $.

    ${
      elsnres.1 $e |- C e. _V $.
      $( Memebership in restriction to a singleton.  (Contributed by Scott
         Fenton, 17-Mar-2011.) $)
      elsnres $p |- ( A e. ( B |` { C } )
            <-> E. y ( A = <. C , y >. /\ <. C , y >. e. B ) ) $=
        cA cB cC csn cres wcel cA vx cv vy cv cop wceq vx cv vy cv cop cB wcel
        wa vy wex vx cC csn wrex cA vx cv vy cv cop wceq vx cv vy cv cop cB
        wcel wa vx cC csn wrex vy wex cA cC vy cv cop wceq cC vy cv cop cB wcel
        wa vy wex vx vy cA cB cC csn elres cA vx cv vy cv cop wceq vx cv vy cv
        cop cB wcel wa vx vy cC csn rexcom4 cA vx cv vy cv cop wceq vx cv vy cv
        cop cB wcel wa vx cC csn wrex cA cC vy cv cop wceq cC vy cv cop cB wcel
        wa vy cA vx cv vy cv cop wceq vx cv vy cv cop cB wcel wa cA cC vy cv
        cop wceq cC vy cv cop cB wcel wa vx cC elsnres.1 vx cv cC wceq cA vx cv
        vy cv cop wceq cA cC vy cv cop wceq vx cv vy cv cop cB wcel cC vy cv
        cop cB wcel vx cv cC wceq vx cv vy cv cop cC vy cv cop cA vx cv cC vy
        cv opeq1 eqeq2d vx cv cC wceq vx cv vy cv cop cC vy cv cop cB vx cv cC
        vy cv opeq1 eleq1d anbi12d rexsn exbii 3bitri $.
    $}

    $( Simplification law for restriction.  (Contributed by NM,
       16-Aug-1994.) $)
    relssres $p |- ( ( Rel A /\ dom A C_ B ) -> ( A |` B ) = A ) $=
      cA wrel cA cdm cB wss wa cA cB cres cA wss cA cA cB cres wss wa cA cB
      cres cA wceq cA wrel cA cdm cB wss wa cA cA cB cres wss cA cB cres cA wss
      cA wrel cA cdm cB wss wa vx vy cA cA cB cres cA wrel cA cdm cB wss simpl
      cA cdm cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cA cB cres wcel wi
      cA wrel cA cdm cB wss vx cv vy cv cop cA wcel vx cv vy cv cop cA wcel vx
      cv cB wcel wa vx cv vy cv cop cA cB cres wcel cA cdm cB wss vx cv vy cv
      cop cA wcel vx cv cB wcel vx cv vy cv cop cA wcel vx cv cA cdm wcel cA
      cdm cB wss vx cv cB wcel vx cv vy cv cA vx vex vy vex opeldm cA cdm cB vx
      cv ssel syl5 ancld vx cv vy cv cA cB vy vex opelres syl6ibr adantl
      relssdv cA cB resss jctil cA cB cres cA eqss sylibr $.
  $}

  $( A relation restricted to its domain equals itself.  (Contributed by NM,
     12-Dec-2006.) $)
  resdm $p |- ( Rel A -> ( A |` dom A ) = A ) $=
    cA wrel cA cdm cA cdm wss cA cA cdm cres cA wceq cA cdm ssid cA cA cdm
    relssres mpan2 $.

  $( The restriction of a set is a set.  (Contributed by NM, 28-Mar-1998.)
     (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  resexg $p |- ( A e. V -> ( A |` B ) e. _V ) $=
    cA cB cres cA wss cA cV wcel cA cB cres cvv wcel cA cB resss cA cB cres cA
    cV ssexg mpan $.

  ${
    resex.1 $e |- A e. _V $.
    $( The restriction of a set is a set.  (Contributed by Jeff Madsen,
       19-Jun-2011.) $)
    resex $p |- ( A |` B ) e. _V $=
      cA cvv wcel cA cB cres cvv wcel resex.1 cA cB cvv resexg ax-mp $.
  $}

  ${
    $d x y A $.
    $( Restriction of a class abstraction of ordered pairs.  (Contributed by
       NM, 5-Nov-2002.) $)
    resopab $p |- ( { <. x , y >. | ph } |` A ) =
                  { <. x , y >. | ( x e. A /\ ph ) } $=
      wph vx vy copab cA cres wph vx vy copab cA cvv cxp cin vx cv cA wcel wph
      wa vx vy copab wph vx vy copab cA df-res wph vx vy copab cA cvv cxp cin
      vx cv cA wcel vx vy copab wph vx vy copab cin vx cv cA wcel wph wa vx vy
      copab wph vx vy copab cA cvv cxp cin wph vx vy copab vx cv cA wcel vx vy
      copab cin vx cv cA wcel vx vy copab wph vx vy copab cin cA cvv cxp vx cv
      cA wcel vx vy copab wph vx vy copab cA cvv cxp vx cv cA wcel vy cv cvv
      wcel wa vx vy copab vx cv cA wcel vx vy copab vx vy cA cvv df-xp vx cv cA
      wcel vx cv cA wcel vy cv cvv wcel wa vx vy vy cv cvv wcel vx cv cA wcel
      vy vex biantru opabbii eqtr4i ineq2i wph vx vy copab vx cv cA wcel vx vy
      copab incom eqtri vx cv cA wcel wph vx vy inopab eqtri eqtri $.

    $( The existence of a restricted identity function, proved without using
       the Axiom of Replacement (unlike ~ resfunexg ).  (Contributed by NM,
       13-Jan-2007.) $)
    resiexg $p |- ( A e. V -> ( _I |` A ) e. _V ) $=
      cA cV wcel cid cA cres cA cA cxp wss cA cA cxp cvv wcel cid cA cres cvv
      wcel vx vy cid cA cres cA cA cxp cid cA relres vx cv vy cv wceq vx cv cA
      wcel wa vx cv cA wcel vy cv cA wcel wa vx cv vy cv cop cid cA cres wcel
      vx cv vy cv cop cA cA cxp wcel vx cv vy cv wceq vx cv cA wcel wa vx cv cA
      wcel vy cv cA wcel vx cv vy cv wceq vx cv cA wcel simpr vx cv vy cv wceq
      vx cv cA wcel vy cv cA wcel vx cv vy cv cA eleq1 biimpa jca vx cv vy cv
      cop cid cA cres wcel vx cv vy cv cop cid wcel vx cv cA wcel wa vx cv vy
      cv wceq vx cv cA wcel wa vx cv vy cv cid cA vy vex opelres vx cv vy cv
      cop cid wcel vx cv vy cv wceq vx cv cA wcel vx cv vy cv cop cid wcel vx
      cv vy cv cid wbr vx cv vy cv wceq vx cv vy cv cid df-br vx cv vy cv vy
      vex ideq bitr3i anbi1i bitri vx cv vy cv cA cA opelxp 3imtr4i relssi cA
      cV wcel cA cA cxp cvv wcel cA cA cV cV xpexg anidms cid cA cres cA cA cxp
      cvv ssexg sylancr $.

    $( A subclass of the identity function is the identity function restricted
       to its domain.  (Contributed by NM, 13-Dec-2003.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
    iss $p |- ( A C_ _I <-> A = ( _I |` dom A ) ) $=
      cA cid wss cA cid cA cdm cres wceq cA cid wss cA cid cA cdm cres wceq vx
      cv vy cv cop cA wcel vx cv vy cv cop cid cA cdm cres wcel wb vy wal vx
      wal cA cid wss vx cv vy cv cop cA wcel vx cv vy cv cop cid cA cdm cres
      wcel wb vx vy cA cid wss vx cv vy cv cop cA wcel vx cv vy cv cop cid wcel
      vx cv cA cdm wcel wa vx cv vy cv cop cid cA cdm cres wcel cA cid wss vx
      cv vy cv cop cA wcel vx cv vy cv cop cid wcel vx cv cA cdm wcel wa cA cid
      wss vx cv vy cv cop cA wcel vx cv vy cv cop cid wcel vx cv cA cdm wcel cA
      cid vx cv vy cv cop ssel vx cv vy cv cop cA wcel vx cv cA cdm wcel wi cA
      cid wss vx cv vy cv cA vx vex vy vex opeldm a1i jcad cA cid wss vx cv vy
      cv cop cid wcel vx cv cA cdm wcel vx cv vy cv cop cA wcel vx cv vy cv cop
      cid wcel vx cv vy cv wceq cA cid wss vx cv cA cdm wcel vx cv vy cv cop cA
      wcel wi vx cv vy cv cop cid wcel vx cv vy cv cid wbr vx cv vy cv wceq vx
      cv vy cv cid df-br vx cv vy cv vy vex ideq bitr3i cA cid wss vx cv cA cdm
      wcel vx cv vx cv cop cA wcel wi vx cv vy cv wceq vx cv cA cdm wcel vx cv
      vy cv cop cA wcel wi vx cv cA cdm wcel vx cv vy cv cop cA wcel vy wex cA
      cid wss vx cv vx cv cop cA wcel vy vx cv cA vx vex eldm2 cA cid wss vx cv
      vy cv cop cA wcel vx cv vx cv cop cA wcel vy cA cid wss vx cv vy cv cop
      cA wcel vx cv vy cv cop cid wcel vx cv vx cv cop cA wcel cA cid vx cv vy
      cv cop ssel vx cv vy cv cop cid wcel vx cv vy cv wceq vx cv vy cv cop cA
      wcel vx cv vx cv cop cA wcel vx cv vy cv cop cid wcel vx cv vy cv cid wbr
      vx cv vy cv wceq vx cv vy cv cid df-br vx cv vy cv vy vex ideq bitr3i vx
      cv vy cv wceq vx cv vx cv cop cA wcel vx cv vy cv cop cA wcel vx cv vy cv
      wceq vx cv vx cv cop vx cv vy cv cop cA vx cv vy cv vx cv opeq2 eleq1d
      biimprcd syl5bi sylcom exlimdv syl5bi vx cv vy cv wceq vx cv vx cv cop cA
      wcel vx cv vy cv cop cA wcel vx cv cA cdm wcel vx cv vy cv wceq vx cv vx
      cv cop vx cv vy cv cop cA vx cv vy cv vx cv opeq2 eleq1d imbi2d syl5ibcom
      syl5bi imp3a impbid vx cv vy cv cid cA cdm vy vex opelres syl6bbr
      alrimivv cA cid wss cA wrel cid cA cdm cres wrel cA cid cA cdm cres wceq
      vx cv vy cv cop cA wcel vx cv vy cv cop cid cA cdm cres wcel wb vy wal vx
      wal wb cA cid wss cid wrel cA wrel reli cA cid relss mpi cid cA cdm
      relres vx vy cA cid cA cdm cres eqrel sylancl mpbird cA cid cA cdm cres
      wceq cA cid wss cid cA cdm cres cid wss cid cA cdm resss cA cid cA cdm
      cres cid sseq1 mpbiri impbii $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.
    $( Restriction of a class abstraction of ordered pairs.  (Contributed by
       NM, 24-Aug-2007.) $)
    resopab2 $p |- ( A C_ B -> ( { <. x , y >. | ( x e. B /\ ph ) } |` A ) =
                  { <. x , y >. | ( x e. A /\ ph ) } ) $=
      cA cB wss vx cv cB wcel wph wa vx vy copab cA cres vx cv cA wcel vx cv cB
      wcel wph wa wa vx vy copab vx cv cA wcel wph wa vx vy copab vx cv cB wcel
      wph wa vx vy cA resopab cA cB wss vx cv cA wcel vx cv cB wcel wph wa wa
      vx cv cA wcel wph wa vx vy cA cB wss vx cv cA wcel wph wa vx cv cA wcel
      vx cv cB wcel wa wph wa vx cv cA wcel vx cv cB wcel wph wa wa cA cB wss
      vx cv cA wcel vx cv cA wcel vx cv cB wcel wa wph cA cB wss vx cv cA wcel
      vx cv cB wcel cA cB vx cv ssel pm4.71d anbi1d vx cv cA wcel vx cv cB wcel
      wph anass syl6rbb opabbidv syl5eq $.

    $( Restriction of the mapping operation.  (Contributed by Mario Carneiro,
       15-Jul-2013.) $)
    resmpt $p |- ( B C_ A -> ( ( x e. A |-> C ) |` B ) = ( x e. B |-> C ) ) $=
      cB cA wss vx cv cA wcel vy cv cC wceq wa vx vy copab cB cres vx cv cB
      wcel vy cv cC wceq wa vx vy copab vx cA cC cmpt cB cres vx cB cC cmpt vy
      cv cC wceq vx vy cB cA resopab2 vx cA cC cmpt vx cv cA wcel vy cv cC wceq
      wa vx vy copab cB vx vy cA cC df-mpt reseq1i vx vy cB cC df-mpt 3eqtr4g
      $.

    $( Unconditional restriction of the mapping operation.  (Contributed by
       Stefan O'Rear, 24-Jan-2015.)  (Proof shortened by Mario Carneiro,
       22-Mar-2015.) $)
    resmpt3 $p |- ( ( x e. A |-> C ) |` B ) = ( x e. ( A i^i B ) |-> C ) $=
      vx cA cC cmpt cA cres cB cres vx cA cC cmpt cA cB cin cres vx cA cC cmpt
      cB cres vx cA cB cin cC cmpt vx cA cC cmpt cA cB resres vx cA cC cmpt cA
      cres vx cA cC cmpt cB cA cA wss vx cA cC cmpt cA cres vx cA cC cmpt wceq
      cA ssid vx cA cA cC resmpt ax-mp reseq1i cA cB cin cA wss vx cA cC cmpt
      cA cB cin cres vx cA cB cin cC cmpt wceq cA cB inss1 vx cA cA cB cin cC
      resmpt ax-mp 3eqtr3i $.
  $}

  ${
    $d w x y z A $.  $d w x y z R $.
    $( Alternate definition of the restriction operation.  (Contributed by
       Mario Carneiro, 5-Nov-2013.) $)
    dfres2 $p |- ( R |` A ) = { <. x , y >. | ( x e. A /\ x R y ) } $=
      vz vw cR cA cres vx cv cA wcel vx cv vy cv cR wbr wa vx vy copab cR cA
      relres vx cv cA wcel vx cv vy cv cR wbr wa vx vy relopab vz cv vw cv cop
      cR cA cres wcel vz cv cA wcel vz cv vw cv cR wbr wa vz cv vw cv cop vx cv
      cA wcel vx cv vy cv cR wbr wa vx vy copab wcel vz cv vw cv cR cA cres wbr
      vz cv vw cv cR wbr vz cv cA wcel wa vz cv vw cv cop cR cA cres wcel vz cv
      cA wcel vz cv vw cv cR wbr wa vz cv vw cv cR cA vw vex brres vz cv vw cv
      cR cA cres df-br vz cv vw cv cR wbr vz cv cA wcel ancom 3bitr3i vx cv cA
      wcel vx cv vy cv cR wbr wa vz cv cA wcel vz cv vy cv cR wbr wa vz cv cA
      wcel vz cv vw cv cR wbr wa vx vy vz cv vw cv vz vex vw vex vx cv vz cv
      wceq vx cv cA wcel vz cv cA wcel vx cv vy cv cR wbr vz cv vy cv cR wbr vx
      cv vz cv cA eleq1 vx cv vz cv vy cv cR breq1 anbi12d vy cv vw cv wceq vz
      cv vy cv cR wbr vz cv vw cv cR wbr vz cv cA wcel vy cv vw cv vz cv cR
      breq2 anbi2d opelopab bitr4i eqrelriiv $.
  $}

  ${
    $d A x y $.
    $( The restricted identity expressed with the class builder.  (Contributed
       by FL, 25-Apr-2012.) $)
    opabresid $p |- { <. x , y >. | ( x e. A /\ y = x ) } = ( _I |` A ) $=
      vy vx weq vx vy copab cA cres vx cv cA wcel vy vx weq wa vx vy copab cid
      cA cres vy vx weq vx vy cA resopab vy vx weq vx vy copab cid cA vy vx weq
      vx vy copab vx vy weq vx vy copab cid vy vx weq vx vy weq vx vy vy vx
      equcom opabbii vx vy dfid3 eqtr4i reseq1i eqtr3i $.
  $}

  ${
    $d A x y $.
    $( The restricted identity expressed with the "maps to" notation.
       (Contributed by FL, 25-Apr-2012.) $)
    mptresid $p |- ( x e. A |-> x ) = ( _I |` A ) $=
      vx cA vx cv cmpt vx cv cA wcel vy vx weq wa vx vy copab cid cA cres vx vy
      cA vx cv df-mpt vx vy cA opabresid eqtri $.
  $}

  $( The domain of a restricted identity function.  (Contributed by NM,
     27-Aug-2004.) $)
  dmresi $p |- dom ( _I |` A ) = A $=
    cA cid cdm wss cid cA cres cdm cA wceq cA cvv cid cdm cA ssv dmi sseqtr4i
    cA cid ssdmres mpbi $.

  $( TODO - delete this and replace w/ dfres3 (in FL's mathbox) $)
  $( Any relation restricted to the universe is itself.  (Contributed by NM,
     16-Mar-2004.) $)
  resid $p |- ( Rel A -> ( A |` _V ) = A ) $=
    cA wrel cA cdm cvv wss cA cvv cres cA wceq cA cdm ssv cA cvv relssres mpan2
    $.

  $( Equality theorem for image.  (Contributed by NM, 14-Aug-1994.) $)
  imaeq1 $p |- ( A = B -> ( A " C ) = ( B " C ) ) $=
    cA cB wceq cA cC cres crn cB cC cres crn cA cC cima cB cC cima cA cB wceq
    cA cC cres cB cC cres cA cB cC reseq1 rneqd cA cC df-ima cB cC df-ima
    3eqtr4g $.

  $( Equality theorem for image.  (Contributed by NM, 14-Aug-1994.) $)
  imaeq2 $p |- ( A = B -> ( C " A ) = ( C " B ) ) $=
    cA cB wceq cC cA cres crn cC cB cres crn cC cA cima cC cB cima cA cB wceq
    cC cA cres cC cB cres cA cB cC reseq2 rneqd cC cA df-ima cC cB df-ima
    3eqtr4g $.

  ${
    imaeq1i.1 $e |- A = B $.
    $( Equality theorem for image.  (Contributed by NM, 21-Dec-2008.) $)
    imaeq1i $p |- ( A " C ) = ( B " C ) $=
      cA cB wceq cA cC cima cB cC cima wceq imaeq1i.1 cA cB cC imaeq1 ax-mp $.

    $( Equality theorem for image.  (Contributed by NM, 21-Dec-2008.) $)
    imaeq2i $p |- ( C " A ) = ( C " B ) $=
      cA cB wceq cC cA cima cC cB cima wceq imaeq1i.1 cA cB cC imaeq2 ax-mp $.
  $}

  ${
    imaeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for image.  (Contributed by FL, 15-Dec-2006.) $)
    imaeq1d $p |- ( ph -> ( A " C ) = ( B " C ) ) $=
      wph cA cB wceq cA cC cima cB cC cima wceq imaeq1d.1 cA cB cC imaeq1 syl
      $.

    $( Equality theorem for image.  (Contributed by FL, 15-Dec-2006.) $)
    imaeq2d $p |- ( ph -> ( C " A ) = ( C " B ) ) $=
      wph cA cB wceq cC cA cima cC cB cima wceq imaeq1d.1 cA cB cC imaeq2 syl
      $.

    imaeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality theorem for image.  (Contributed by Mario Carneiro,
       4-Dec-2016.) $)
    imaeq12d $p |- ( ph -> ( A " C ) = ( B " D ) ) $=
      wph cA cC cima cB cC cima cB cD cima wph cA cB cC imaeq1d.1 imaeq1d wph
      cC cD cB imaeq12d.2 imaeq2d eqtrd $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Alternate definition of image.  Compare definition (d) of [Enderton]
       p. 44.  (Contributed by NM, 19-Apr-2004.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    dfima2 $p |- ( A " B ) = { y | E. x e. B x A y } $=
      cA cB cima cA cB cres crn vx cv vy cv cA cB cres wbr vx wex vy cab vx cv
      vy cv cA wbr vx cB wrex vy cab cA cB df-ima vx vy cA cB cres dfrn2 vx cv
      vy cv cA cB cres wbr vx wex vx cv vy cv cA wbr vx cB wrex vy vx cv vy cv
      cA cB cres wbr vx wex vx cv cB wcel vx cv vy cv cA wbr wa vx wex vx cv vy
      cv cA wbr vx cB wrex vx cv vy cv cA cB cres wbr vx cv cB wcel vx cv vy cv
      cA wbr wa vx vx cv vy cv cA cB cres wbr vx cv vy cv cA wbr vx cv cB wcel
      wa vx cv cB wcel vx cv vy cv cA wbr wa vx cv vy cv cA cB vy vex brres vx
      cv vy cv cA wbr vx cv cB wcel ancom bitri exbii vx cv vy cv cA wbr vx cB
      df-rex bitr4i abbii 3eqtri $.

    $( Alternate definition of image.  Compare definition (d) of [Enderton]
       p. 44.  (Contributed by NM, 14-Aug-1994.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    dfima3 $p |- ( A " B ) = { y | E. x ( x e. B /\ <. x , y >. e. A ) } $=
      cA cB cima vx cv vy cv cA wbr vx cB wrex vy cab vx cv cB wcel vx cv vy cv
      cop cA wcel wa vx wex vy cab vx vy cA cB dfima2 vx cv vy cv cA wbr vx cB
      wrex vx cv cB wcel vx cv vy cv cop cA wcel wa vx wex vy vx cv vy cv cA
      wbr vx cB wrex vx cv vy cv cop cA wcel vx cB wrex vx cv cB wcel vx cv vy
      cv cop cA wcel wa vx wex vx cv vy cv cA wbr vx cv vy cv cop cA wcel vx cB
      vx cv vy cv cA df-br rexbii vx cv vy cv cop cA wcel vx cB df-rex bitri
      abbii eqtri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 20-Jan-2007.) $)
    elimag $p |- ( A e. V -> ( A e. ( B " C ) <-> E. x e. C x B A ) ) $=
      vx cv vy cv cB wbr vx cC wrex vx cv cA cB wbr vx cC wrex vy cA cB cC cima
      cV vy cv cA wceq vx cv vy cv cB wbr vx cv cA cB wbr vx cC vy cv cA vx cv
      cB breq2 rexbidv vx vy cB cC dfima2 elab2g $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    elima.1 $e |- A e. _V $.
    $( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 19-Apr-2004.) $)
    elima $p |- ( A e. ( B " C ) <-> E. x e. C x B A ) $=
      cA cvv wcel cA cB cC cima wcel vx cv cA cB wbr vx cC wrex wb elima.1 vx
      cA cB cC cvv elimag ax-mp $.

    $( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 11-Aug-2004.) $)
    elima2 $p |- ( A e. ( B " C ) <-> E. x ( x e. C /\ x B A ) ) $=
      cA cB cC cima wcel vx cv cA cB wbr vx cC wrex vx cv cC wcel vx cv cA cB
      wbr wa vx wex vx cA cB cC elima.1 elima vx cv cA cB wbr vx cC df-rex
      bitri $.

    $( Membership in an image.  Theorem 34 of [Suppes] p. 65.  (Contributed by
       NM, 14-Aug-1994.) $)
    elima3 $p |- ( A e. ( B " C ) <-> E. x ( x e. C /\ <. x , A >. e. B ) ) $=
      cA cB cC cima wcel vx cv cC wcel vx cv cA cB wbr wa vx wex vx cv cC wcel
      vx cv cA cop cB wcel wa vx wex vx cA cB cC elima.1 elima2 vx cv cC wcel
      vx cv cA cB wbr wa vx cv cC wcel vx cv cA cop cB wcel wa vx vx cv cA cB
      wbr vx cv cA cop cB wcel vx cv cC wcel vx cv cA cB df-br anbi2i exbii
      bitri $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d x y z w $.
    nfima.1 $e |- F/_ x A $.
    nfima.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for image.  (Contributed by NM,
       30-Dec-1996.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    nfima $p |- F/_ x ( A " B ) $=
      vx cA cB cima cA cB cres crn cA cB df-ima vx cA cB cres vx cA cB nfima.1
      nfima.2 nfres nfrn nfcxfr $.
  $}

  ${
    $d x y z $.  $d B y z $.  $d A y z $.  $d ph y $.
    nfimad.2 $e |- ( ph -> F/_ x A ) $.
    nfimad.3 $e |- ( ph -> F/_ x B ) $.
    $( Deduction version of bound-variable hypothesis builder ~ nfima .
       (Contributed by FL, 15-Dec-2006.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
    nfimad $p |- ( ph -> F/_ x ( A " B ) ) $=
      wph vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz cab cima wnfc
      vx cA cB cima wnfc vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz
      cab vz cv cA wcel vx vz nfaba1 vz cv cB wcel vx vz nfaba1 nfima wph vx cA
      wnfc vx cB wnfc vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz
      cab cima wnfc vx cA cB cima wnfc wb nfimad.2 nfimad.3 vx cA wnfc vx cB
      wnfc wa vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz cab cima
      cA cB cima vx cA wnfc vx cB wnfc vx vx cA nfnfc1 vx cB nfnfc1 nfan vx cA
      wnfc vx cB wnfc vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz cab
      cima cA vz cv cB wcel vx wal vz cab cima cA cB cima vx cA wnfc vz cv cA
      wcel vx wal vz cab cA vz cv cB wcel vx wal vz cab vx vz cA abidnf imaeq1d
      vx cB wnfc vz cv cB wcel vx wal vz cab cB cA vx vz cB abidnf imaeq2d
      sylan9eq nfceqdf syl2anc mpbii $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d C y z $.  $d x y z $.  $d F y z $.
    $( Move class substitution in and out of the image of a function.
       (Contributed by FL, 15-Dec-2006.)  (Proof shortened by Mario Carneiro,
       4-Dec-2016.) $)
    csbima12g $p |- ( A e. C -> [_ A / x ]_ ( F " B ) =
                 ( [_ A / x ]_ F " [_ A / x ]_ B ) ) $=
      vx vy cv cF cB cima csb vx vy cv cF csb vx vy cv cB csb cima wceq vx cA
      cF cB cima csb vx cA cF csb vx cA cB csb cima wceq vy cA cC vy cv cA wceq
      vx vy cv cF cB cima csb vx cA cF cB cima csb vx vy cv cF csb vx vy cv cB
      csb cima vx cA cF csb vx cA cB csb cima vx vy cv cA cF cB cima csbeq1 vy
      cv cA wceq vx vy cv cF csb vx cA cF csb vx vy cv cB csb vx cA cB csb vx
      vy cv cA cF csbeq1 vx vy cv cA cB csbeq1 imaeq12d eqeq12d vx vy cv cF cB
      cima vx vy cv cF csb vx vy cv cB csb cima vy vex vx vx vy cv cF csb vx vy
      cv cB csb vx vy cv cF nfcsb1v vx vy cv cB nfcsb1v nfima vx cv vy cv wceq
      cF vx vy cv cF csb cB vx vy cv cB csb vx vy cv cF csbeq1a vx vy cv cB
      csbeq1a imaeq12d csbief vtoclg $.
  $}

  $( Move class substitution in and out of the image of a function.  (This is
     ~ csbima12g with a shortened proof, shortened by Alan Sare, 10-Nov-2012.)
     The proof is derived from the virtual deduction proof ~ csbima12gALTVD .
     Although the proof is shorter, the total number of steps of all theorems
     used in the proof is probably longer.  (Contributed by NM, 10-Nov-2012.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  csbima12gALT $p |- ( A e. C -> [_ A / x ]_ ( F " B ) =
                 ( [_ A / x ]_ F " [_ A / x ]_ B ) ) $=
    cA cC wcel vx cA cF cB cres crn csb vx cA cF csb vx cA cB csb cres crn vx
    cA cF cB cima csb vx cA cF csb vx cA cB csb cima cA cC wcel vx cA cF cB
    cres crn csb vx cA cF cB cres csb crn vx cA cF csb vx cA cB csb cres crn vx
    cA cF cB cres cC csbrng cA cC wcel vx cA cF cB cres csb vx cA cF csb vx cA
    cB csb cres vx cA cF cB cC csbresg rneqd eqtrd vx cA cF cB cima cF cB cres
    crn cF cB df-ima csbeq2i vx cA cF csb vx cA cB csb df-ima 3eqtr4g $.

  ${
    $d x y A $.  $d x y B $.
    $( The image of the domain of a class is the range of the class.
       (Contributed by NM, 14-Aug-1994.) $)
    imadmrn $p |- ( A " dom A ) = ran A $=
      vx cv cA cdm wcel vx cv vy cv cop cA wcel wa vx wex vy cab vx cv vy cv
      cop cA wcel vx wex vy cab cA cA cdm cima cA crn vx cv cA cdm wcel vx cv
      vy cv cop cA wcel wa vx wex vx cv vy cv cop cA wcel vx wex vy vx cv cA
      cdm wcel vx cv vy cv cop cA wcel wa vx cv vy cv cop cA wcel vx vx cv vy
      cv cop cA wcel vx cv vy cv cop cA wcel vx cv cA cdm wcel wa vx cv cA cdm
      wcel vx cv vy cv cop cA wcel wa vx cv vy cv cop cA wcel vx cv cA cdm wcel
      vx cv vy cv cA vx vex vy vex opeldm pm4.71i vx cv vy cv cop cA wcel vx cv
      cA cdm wcel ancom bitr2i exbii abbii vx vy cA cA cdm dfima3 vx vy cA
      dfrn3 3eqtr4i $.

    $( The image of a class is a subset of its range.  Theorem 3.16(xi) of
       [Monk1] p. 39.  (Contributed by NM, 31-Mar-1995.) $)
    imassrn $p |- ( A " B ) C_ ran A $=
      vx cv cB wcel vx cv vy cv cop cA wcel wa vx wex vy cab vx cv vy cv cop cA
      wcel vx wex vy cab cA cB cima cA crn vx cv cB wcel vx cv vy cv cop cA
      wcel wa vx wex vx cv vy cv cop cA wcel vx wex vy vx cv cB wcel vx cv vy
      cv cop cA wcel wa vx cv vy cv cop cA wcel vx vx cv cB wcel vx cv vy cv
      cop cA wcel simpr eximi ss2abi vx vy cA cB dfima3 vx vy cA dfrn3 3sstr4i
      $.
  $}

  $( The image of a set is a set.  Theorem 3.17 of [Monk1] p. 39.  (Contributed
     by NM, 24-Jul-1995.) $)
  imaexg $p |- ( A e. V -> ( A " B ) e. _V ) $=
    cA cV wcel cA cB cima cA crn wss cA crn cvv wcel cA cB cima cvv wcel cA cB
    imassrn cA cV rnexg cA cB cima cA crn cvv ssexg sylancr $.

  ${
    $d x y A $.
    $( Image under the identity relation.  Theorem 3.16(viii) of [Monk1]
       p. 38.  (Contributed by NM, 30-Apr-1998.) $)
    imai $p |- ( _I " A ) = A $=
      cid cA cima vx cv cA wcel vx cv vy cv cop cid wcel wa vx wex vy cab vy cv
      cA wcel vy cab cA vx vy cid cA dfima3 vx cv cA wcel vx cv vy cv cop cid
      wcel wa vx wex vy cv cA wcel vy vx cv cA wcel vx cv vy cv cop cid wcel wa
      vx wex vx cv vy cv wceq vx cv cA wcel wa vx wex vy cv cA wcel vx cv cA
      wcel vx cv vy cv cop cid wcel wa vx cv vy cv wceq vx cv cA wcel wa vx vx
      cv cA wcel vx cv vy cv cop cid wcel wa vx cv cA wcel vx cv vy cv wceq wa
      vx cv vy cv wceq vx cv cA wcel wa vx cv vy cv cop cid wcel vx cv vy cv
      wceq vx cv cA wcel vx cv vy cv cop cid wcel vx cv vy cv cid wbr vx cv vy
      cv wceq vx cv vy cv cid df-br vx cv vy cv vy vex ideq bitr3i anbi2i vx cv
      cA wcel vx cv vy cv wceq ancom bitri exbii vx cv cA wcel vy cv cA wcel vx
      vy cv vy vex vx cv vy cv cA eleq1 ceqsexv bitri abbii vy cA abid2 3eqtri
      $.
  $}

  $( The range of the restricted identity function.  (Contributed by NM,
     27-Aug-2004.) $)
  rnresi $p |- ran ( _I |` A ) = A $=
    cid cA cima cid cA cres crn cA cid cA df-ima cA imai eqtr3i $.

  $( The image of a restriction of the identity function.  (Contributed by FL,
     31-Dec-2006.) $)
  resiima $p |- ( B C_ A -> ( ( _I |` A ) " B ) = B ) $=
    cB cA wss cid cA cres cB cima cid cA cres cB cres crn cid cB cres crn cB
    cid cA cres cB cima cid cA cres cB cres crn wceq cB cA wss cid cA cres cB
    df-ima a1i cB cA wss cid cA cres cB cres cid cB cres cid cB cA resabs1
    rneqd cid cB cres crn cB wceq cB cA wss cB rnresi a1i 3eqtrd $.

  $( Image of the empty set.  Theorem 3.16(ii) of [Monk1] p. 38.  (Contributed
     by NM, 20-May-1998.) $)
  ima0 $p |- ( A " (/) ) = (/) $=
    cA c0 cima cA c0 cres crn c0 crn c0 cA c0 df-ima cA c0 cres c0 cA res0
    rneqi rn0 3eqtri $.

  $( Image under the empty relation.  (Contributed by FL, 11-Jan-2007.) $)
  0ima $p |- ( (/) " A ) = (/) $=
    c0 cA cima c0 c0 cA cima c0 crn c0 c0 cA imassrn rn0 sseqtri c0 cA cima 0ss
    eqssi $.

  $( A class whose image under another is empty is disjoint with the other's
     domain.  (Contributed by FL, 24-Jan-2007.) $)
  imadisj $p |- ( ( A " B ) = (/) <-> ( dom A i^i B ) = (/) ) $=
    cA cB cima c0 wceq cA cB cres crn c0 wceq cA cB cres cdm c0 wceq cA cdm cB
    cin c0 wceq cA cB cima cA cB cres crn c0 cA cB df-ima eqeq1i cA cB cres
    dm0rn0 cA cB cres cdm cA cdm cB cin c0 cA cB cres cdm cB cA cdm cin cA cdm
    cB cin cA cB dmres cB cA cdm incom eqtri eqeq1i 3bitr2i $.

  $( A preimage under any class is included in the domain of the class.
     (Contributed by FL, 29-Jan-2007.) $)
  cnvimass $p |- ( `' A " B ) C_ dom A $=
    cA ccnv cB cima cA ccnv crn cA cdm cA ccnv cB imassrn cA dfdm4 sseqtr4i $.

  $( The preimage of the range of a class is the domain of the class.
     (Contributed by Jeff Hankins, 15-Jul-2009.) $)
  cnvimarndm $p |- ( `' A " ran A ) = dom A $=
    cA ccnv cA ccnv cdm cima cA ccnv crn cA ccnv cA crn cima cA cdm cA ccnv
    imadmrn cA crn cA ccnv cdm cA ccnv cA df-rn imaeq2i cA dfdm4 3eqtr4i $.

  ${
    $d x y A $.  $d x B $.  $d x y R $.
    $( The image of a singleton.  (Contributed by NM, 8-May-2005.) $)
    imasng $p |- ( A e. B -> ( R " { A } ) = { y | A R y } ) $=
      cA cB wcel cA cvv wcel cR cA csn cima cA vy cv cR wbr vy cab wceq cA cB
      elex cA cvv wcel cR cA csn cima vx cv vy cv cR wbr vx cA csn wrex vy cab
      cA vy cv cR wbr vy cab vx vy cR cA csn dfima2 cA cvv wcel vx cv vy cv cR
      wbr vx cA csn wrex cA vy cv cR wbr vy vx cv vy cv cR wbr cA vy cv cR wbr
      vx cA cvv vx cv cA vy cv cR breq1 rexsng abbidv syl5eq syl $.

    $( The image of a singleton.  (Contributed by NM, 20-May-1998.) $)
    relimasn $p |- ( Rel R -> ( R " { A } ) = { y | A R y } ) $=
      cR wrel cA cvv wcel cR cA csn cima cA vy cv cR wbr vy cab wceq cR wrel cA
      cvv wcel wn cR cA csn cima cA vy cv cR wbr vy cab wceq cR wrel cA cvv
      wcel wn wa cR cA csn cima c0 cA vy cv cR wbr vy cab cA cvv wcel wn cR cA
      csn cima c0 wceq cR wrel cA cvv wcel wn cR cA csn cima cR c0 cima c0 cA
      cvv wcel wn cA csn c0 wceq cR cA csn cima cR c0 cima wceq cA snprc cA csn
      c0 cR imaeq2 sylbi cR ima0 syl6eq adantl cR wrel cA cvv wcel wn wa cA vy
      cv cR wbr vy wex wn cA vy cv cR wbr vy cab c0 wceq cR wrel cA cvv wcel wn
      wa cA vy cv cR wbr vy cR wrel cA vy cv cR wbr cA cvv wcel cR wrel cA vy
      cv cR wbr cA cvv wcel cA vy cv cR brrelex ex con3and nexdv cA vy cv cR
      wbr vy wex cA vy cv cR wbr vy cab c0 cA vy cv cR wbr vy abn0 necon1bbii
      sylib eqtr4d ex vy cA cvv cR imasng pm2.61d2 $.

    $( Elementhood in the image of a singleton.  (Contributed by Mario
       Carneiro, 3-Nov-2015.) $)
    elrelimasn $p |- ( Rel R -> ( B e. ( R " { A } ) <-> A R B ) ) $=
      cR wrel cB cR cA csn cima wcel cB cA vx cv cR wbr vx cab wcel cA cB cR
      wbr cR wrel cR cA csn cima cA vx cv cR wbr vx cab cB vx cA cR relimasn
      eleq2d cR wrel cA cB cR wbr cB cvv wcel wi cB cA vx cv cR wbr vx cab wcel
      cA cB cR wbr wb cR wrel cA cB cR wbr cB cvv wcel cA cB cR brrelex2 ex cA
      vx cv cR wbr cA cB cR wbr vx cB cvv vx cv cB cA cR breq2 elab3g syl bitrd
      $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    elimasn.1 $e |- B e. _V $.
    elimasn.2 $e |- C e. _V $.
    $( Membership in an image of a singleton.  (Contributed by NM,
       15-Mar-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    elimasn $p |- ( C e. ( A " { B } ) <-> <. B , C >. e. A ) $=
      cC cA cB csn cima wcel cB cC cA wbr cB cC cop cA wcel cB vx cv cA wbr cB
      cC cA wbr vx cC cA cB csn cima elimasn.2 vx cv cC cB cA breq2 cB cvv wcel
      cA cB csn cima cB vx cv cA wbr vx cab wceq elimasn.1 vx cB cvv cA imasng
      ax-mp elab2 cB cC cA df-br bitri $.
  $}

  ${
    $d A y z $.  $d B y z $.  $d C y z $.
    $( Membership in an image of a singleton.  (Contributed by Raph Levien,
       21-Oct-2006.) $)
    elimasng $p |- ( ( B e. V /\ C e. W ) ->
                   ( C e. ( A " { B } ) <-> <. B , C >. e. A ) ) $=
      vz cv cA vy cv csn cima wcel vy cv vz cv cop cA wcel wb vz cv cA cB csn
      cima wcel cB vz cv cop cA wcel wb cC cA cB csn cima wcel cB cC cop cA
      wcel wb vy vz cB cC cV cW vy cv cB wceq vz cv cA vy cv csn cima wcel vz
      cv cA cB csn cima wcel vy cv vz cv cop cA wcel cB vz cv cop cA wcel vy cv
      cB wceq cA vy cv csn cima cA cB csn cima vz cv vy cv cB wceq vy cv csn cB
      csn cA vy cv cB sneq imaeq2d eleq2d vy cv cB wceq vy cv vz cv cop cB vz
      cv cop cA vy cv cB vz cv opeq1 eleq1d bibi12d vz cv cC wceq vz cv cA cB
      csn cima wcel cC cA cB csn cima wcel cB vz cv cop cA wcel cB cC cop cA
      wcel vz cv cC cA cB csn cima eleq1 vz cv cC wceq cB vz cv cop cB cC cop
      cA vz cv cC cB opeq2 eleq1d bibi12d cA vy cv vz cv vy vex vz vex elimasn
      vtocl2g $.
  $}

  $( Membership in an image of a singleton.  (Contributed by NM,
     5-Aug-2010.) $)
  elimasni $p |- ( C e. ( A " { B } ) -> B A C ) $=
    cB cvv wcel cC cvv wcel wa cC cA cB csn cima wcel cB cC cA wbr cC cA cB csn
    cima wcel cB cvv wcel cC cvv wcel cB cvv wcel cC cA cB csn cima wcel cB cvv
    wcel wn cC cA cB csn cima wcel cC c0 wcel cC noel cB cvv wcel wn cA cB csn
    cima c0 cC cB cvv wcel wn cA cB csn cima cA c0 cima c0 cB cvv wcel wn cB
    csn c0 cA cB cvv wcel wn cB csn c0 wceq cB snprc biimpi imaeq2d cA ima0
    syl6eq eleq2d mtbiri con4i cC cA cB csn cima elex jca cB cvv wcel cC cvv
    wcel wa cC cA cB csn cima wcel cB cC cA wbr cB cvv wcel cC cvv wcel wa cC
    cA cB csn cima wcel cB cC cop cA wcel cB cC cA wbr cA cB cC cvv cvv
    elimasng cB cC cA df-br syl6bbr biimpd mpcom $.

  ${
    $d y F $.  $d x y $.
    $( Two ways to express the class of unique-valued arguments of ` F ` ,
       which is the same as the domain of ` F ` whenever ` F ` is a function.
       The left-hand side of the equality is from Definition 10.2 of [Quine]
       p. 65.  Quine uses the notation "arg ` F ` " for this class (for which
       we have no separate notation).  Observe the resemblance to the
       alternative definition ~ dffv4 of function value, which is based on the
       idea in Quine's definition.  (Contributed by NM, 8-May-2005.) $)
    args $p |- { x | E. y ( F " { x } ) = { y } } = { x | E! y x F y } $=
      cF vx cv csn cima vy cv csn wceq vy wex vx cv vy cv cF wbr vy weu vx cF
      vx cv csn cima vy cv csn wceq vy wex vx cv vy cv cF wbr vy cab vy cv csn
      wceq vy wex vx cv vy cv cF wbr vy weu cF vx cv csn cima vy cv csn wceq vx
      cv vy cv cF wbr vy cab vy cv csn wceq vy cF vx cv csn cima vx cv vy cv cF
      wbr vy cab vy cv csn vx cv cvv wcel cF vx cv csn cima vx cv vy cv cF wbr
      vy cab wceq vx vex vy vx cv cvv cF imasng ax-mp eqeq1i exbii vx cv vy cv
      cF wbr vy euabsn bitr4i abbii $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    eliniseg.1 $e |- C e. _V $.
    $( Membership in an initial segment.  The idiom ` ( ``' A " { B } ) ` ,
       meaning ` { x | x A B } ` , is used to specify an initial segment in
       (for example) Definition 6.21 of [TakeutiZaring] p. 30.  (Contributed by
       NM, 28-Apr-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    eliniseg $p |- ( B e. V -> ( C e. ( `' A " { B } ) <-> C A B ) ) $=
      cB cV wcel cC cvv wcel cC cA ccnv cB csn cima wcel cC cB cA wbr wb
      eliniseg.1 cB cV wcel cC cvv wcel wa cC cA ccnv cB csn cima wcel cB cC cA
      ccnv wbr cC cB cA wbr cB cV wcel cC cvv wcel wa cC cA ccnv cB csn cima
      wcel cB cC cop cA ccnv wcel cB cC cA ccnv wbr cA ccnv cB cC cV cvv
      elimasng cB cC cA ccnv df-br syl6bbr cB cC cV cvv cA brcnvg bitrd mpan2
      $.
  $}

  ${
    $d A x y $.
    epini.1 $e |- A e. _V $.
    $( Any set is equal to its preimage under the converse epsilon relation.
       (Contributed by Mario Carneiro, 9-Mar-2013.) $)
    epini $p |- ( `' _E " { A } ) = A $=
      vx cep ccnv cA csn cima cA vx cv cep ccnv cA csn cima wcel vx cv cA cep
      wbr vx cv cA wcel cA cvv wcel vx cv cep ccnv cA csn cima wcel vx cv cA
      cep wbr wb epini.1 cep cA vx cv cvv vx vex eliniseg ax-mp vx cv cA
      epini.1 epelc bitri eqriv $.
  $}

  ${
    $d x A $.  $d x B $.
    $( An idiom that signifies an initial segment of an ordering, used, for
       example, in Definition 6.21 of [TakeutiZaring] p. 30.  (Contributed by
       NM, 28-Apr-2004.) $)
    iniseg $p |- ( B e. V -> ( `' A " { B } ) = { x | x A B } ) $=
      cB cV wcel cB cvv wcel cA ccnv cB csn cima vx cv cB cA wbr vx cab wceq cB
      cV elex cB cvv wcel vx cv cB cA wbr vx cA ccnv cB csn cima cA cB vx cv
      cvv vx vex eliniseg abbi2dv syl $.
  $}

  ${
    $d x y z A $.  $d x y z R $.
    $( Alternate definition of well-founded relation.  Definition 6.21 of
       [TakeutiZaring] p. 30.  (Contributed by NM, 23-Apr-2004.)  (Revised by
       Mario Carneiro, 23-Jun-2015.) $)
    dffr3 $p |- ( R Fr A <-> A. x ( ( x C_ A /\ x =/= (/) ) ->
                E. y e. x ( x i^i ( `' R " { y } ) ) = (/) ) ) $=
      cA cR wfr vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr vz vx cv crab
      c0 wceq vy vx cv wrex wi vx wal vx cv cA wss vx cv c0 wne wa vx cv cR
      ccnv vy cv csn cima cin c0 wceq vy vx cv wrex wi vx wal vx vy vz cA cR
      dffr2 vx cv cA wss vx cv c0 wne wa vx cv cR ccnv vy cv csn cima cin c0
      wceq vy vx cv wrex wi vx cv cA wss vx cv c0 wne wa vz cv vy cv cR wbr vz
      vx cv crab c0 wceq vy vx cv wrex wi vx vx cv cR ccnv vy cv csn cima cin
      c0 wceq vy vx cv wrex vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx cv
      wrex vx cv cA wss vx cv c0 wne wa vx cv cR ccnv vy cv csn cima cin c0
      wceq vz cv vy cv cR wbr vz vx cv crab c0 wceq vy vx cv vx cv cR ccnv vy
      cv csn cima cin vz cv vy cv cR wbr vz vx cv crab c0 vx cv cR ccnv vy cv
      csn cima cin vx cv vz cv vy cv cR wbr vz cab cin vz cv vy cv cR wbr vz vx
      cv crab cR ccnv vy cv csn cima vz cv vy cv cR wbr vz cab vx cv vy cv cvv
      wcel cR ccnv vy cv csn cima vz cv vy cv cR wbr vz cab wceq vy vex vz cR
      vy cv cvv iniseg ax-mp ineq2i vz cv vy cv cR wbr vz vx cv dfrab3 eqtr4i
      eqeq1i rexbii imbi2i albii bitr4i $.
  $}

  ${
    $d x y A $.  $d x y R $.  $d x V $.
    $( Alternate definition of set-like relation.  (Contributed by Mario
       Carneiro, 23-Jun-2015.) $)
    dfse2 $p |- ( R Se A <-> A. x e. A ( A i^i ( `' R " { x } ) ) e. _V ) $=
      cA cR wse vy cv vx cv cR wbr vy cA crab cvv wcel vx cA wral cA cR ccnv vx
      cv csn cima cin cvv wcel vx cA wral vx vy cA cR df-se vy cv vx cv cR wbr
      vy cA crab cvv wcel cA cR ccnv vx cv csn cima cin cvv wcel vx cA vy cv vx
      cv cR wbr vy cA crab cA cR ccnv vx cv csn cima cin cvv vy cv vx cv cR wbr
      vy cA crab cA vy cv vx cv cR wbr vy cab cin cA cR ccnv vx cv csn cima cin
      vy cv vx cv cR wbr vy cA dfrab3 cR ccnv vx cv csn cima vy cv vx cv cR wbr
      vy cab cA vx cv cvv wcel cR ccnv vx cv csn cima vy cv vx cv cR wbr vy cab
      wceq vx vex vy cR vx cv cvv iniseg ax-mp ineq2i eqtr4i eleq1i ralbii
      bitri $.

    $( Any set relation is set-like.  (Contributed by Mario Carneiro,
       22-Jun-2015.) $)
    exse2 $p |- ( R e. V -> R Se A ) $=
      cR cV wcel vy cv vx cv cR wbr vy cA crab cvv wcel vx cA wral cA cR wse cR
      cV wcel vy cv vx cv cR wbr vy cA crab cvv wcel vx cA cR cV wcel vy cv vx
      cv cR wbr vy cA crab cR cdm wss cR cdm cvv wcel vy cv vx cv cR wbr vy cA
      crab cvv wcel vy cv vx cv cR wbr vy cA crab vy cv cA wcel vy cv vx cv cR
      wbr wa vy cab cR cdm vy cv vx cv cR wbr vy cA df-rab vy cv cA wcel vy cv
      vx cv cR wbr wa vy cR cdm vy cv vx cv cR wbr vy cv cR cdm wcel vy cv cA
      wcel vy cv vx cv cR vy vex vx vex breldm adantl abssi eqsstri cR cV dmexg
      vy cv vx cv cR wbr vy cA crab cR cdm cvv ssexg sylancr ralrimivw vx vy cA
      cR df-se sylibr $.
  $}

  $( Subset theorem for image.  (Contributed by NM, 16-Mar-2004.) $)
  imass1 $p |- ( A C_ B -> ( A " C ) C_ ( B " C ) ) $=
    cA cB wss cA cC cres crn cB cC cres crn cA cC cima cB cC cima cA cB wss cA
    cC cres cB cC cres wss cA cC cres crn cB cC cres crn wss cA cB cC ssres cA
    cC cres cB cC cres rnss syl cA cC df-ima cB cC df-ima 3sstr4g $.

  $( Subset theorem for image.  Exercise 22(a) of [Enderton] p. 53.
     (Contributed by NM, 22-Mar-1998.) $)
  imass2 $p |- ( A C_ B -> ( C " A ) C_ ( C " B ) ) $=
    cA cB wss cC cA cres crn cC cB cres crn cC cA cima cC cB cima cA cB wss cC
    cA cres cC cB cres wss cC cA cres crn cC cB cres crn wss cA cB cC ssres2 cC
    cA cres cC cB cres rnss syl cC cA df-ima cC cB df-ima 3sstr4g $.

  $( The image of a singleton outside the domain is empty.  (Contributed by NM,
     22-May-1998.) $)
  ndmima $p |- ( -. A e. dom B -> ( B " { A } ) = (/) ) $=
    cA cB cdm wcel wn cB cA csn cima cB cA csn cres crn c0 cB cA csn df-ima cA
    cB cdm wcel wn cB cA csn cres cdm c0 wceq cB cA csn cres crn c0 wceq cA cB
    cdm wcel wn cB cA csn cres cdm cB cdm cA csn cin c0 cB cA csn cres cdm cA
    csn cB cdm cin cB cdm cA csn cin cB cA csn dmres cA csn cB cdm incom eqtri
    cB cdm cA csn cin c0 wceq cA cB cdm wcel wn cB cdm cA disjsn biimpri syl5eq
    cB cA csn cres dm0rn0 sylib syl5eq $.

  ${
    $d x y A $.
    $( A converse is a relation.  Theorem 12 of [Suppes] p. 62.  (Contributed
       by NM, 29-Oct-1996.) $)
    relcnv $p |- Rel `' A $=
      vy cv vx cv cA wbr vx vy cA ccnv vx vy cA df-cnv relopabi $.
  $}

  ${
    $( When ` R ` is a relation, the sethood assumptions on ~ brcnv can be
       omitted.  (Contributed by Mario Carneiro, 28-Apr-2015.) $)
    relbrcnvg $p |- ( Rel R -> ( A `' R B <-> B R A ) ) $=
      cR wrel cA cvv wcel cB cvv wcel wa cA cB cR ccnv wbr cB cA cR wbr cA cB
      cR ccnv wbr cA cvv wcel cB cvv wcel wa wi cR wrel cR ccnv wrel cA cB cR
      ccnv wbr cA cvv wcel cB cvv wcel wa cR relcnv cA cB cR ccnv brrelex12
      mpan a1i cR wrel cB cA cR wbr cA cvv wcel cB cvv wcel wa cR wrel cB cA cR
      wbr wa cB cvv wcel cA cvv wcel cB cA cR brrelex12 ancomd ex cA cvv wcel
      cB cvv wcel wa cA cB cR ccnv wbr cB cA cR wbr wb wi cR wrel cA cB cvv cvv
      cR brcnvg a1i pm5.21ndd $.

    $( Eliminate the class existence constraint in ~ eliniseg .  (Contributed
       by Mario Carneiro, 5-Dec-2014.)  (Revised by Mario Carneiro,
       17-Nov-2015.) $)
    eliniseg2 $p |- ( Rel A -> ( C e. ( `' A " { B } ) <-> C A B ) ) $=
      cC cA ccnv cB csn cima wcel cB cC cA ccnv wbr cA wrel cC cB cA wbr cA
      ccnv wrel cC cA ccnv cB csn cima wcel cB cC cA ccnv wbr wb cA relcnv cB
      cC cA ccnv elrelimasn ax-mp cB cC cA relbrcnvg syl5bb $.

    relbrcnv.1 $e |- Rel R $.
    $( When ` R ` is a relation, the sethood assumptions on ~ brcnv can be
       omitted.  (Contributed by Mario Carneiro, 28-Apr-2015.) $)
    relbrcnv $p |- ( A `' R B <-> B R A ) $=
      cR wrel cA cB cR ccnv wbr cB cA cR wbr wb relbrcnv.1 cA cB cR relbrcnvg
      ax-mp $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y z R $.
    $( Two ways of saying a relation is transitive.  Definition of transitivity
       in [Schechter] p. 51.  (Contributed by NM, 27-Dec-1996.)  (Proof
       shortened by Andrew Salmon, 27-Aug-2011.) $)
    cotr $p |- ( ( R o. R ) C_ R <->
             A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) ) $=
      cR cR ccom cR wss vx cv vz cv cop cR cR ccom wcel vx cv vz cv cop cR wcel
      wi vz wal vx wal vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi vz wal vy wal vx wal cR cR ccom wrel cR cR ccom cR wss vx cv vz cv
      cop cR cR ccom wcel vx cv vz cv cop cR wcel wi vz wal vx wal wb vx cv vy
      cv cR wbr vy cv vz cv cR wbr wa vy wex vx vz cR cR ccom vx vz vy cR cR
      df-co relopabi vx vz cR cR ccom cR ssrel ax-mp vx cv vz cv cop cR cR ccom
      wcel vx cv vz cv cop cR wcel wi vz wal vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi vz wal vy wal vx vx cv vz cv cop cR cR ccom
      wcel vx cv vz cv cop cR wcel wi vz wal vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi vy wal vz wal vx cv vy cv cR wbr vy cv vz cv
      cR wbr wa vx cv vz cv cR wbr wi vz wal vy wal vx cv vz cv cop cR cR ccom
      wcel vx cv vz cv cop cR wcel wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa
      vx cv vz cv cR wbr wi vy wal vz vx cv vz cv cop cR cR ccom wcel vx cv vz
      cv cop cR wcel wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vy wex vx cv
      vz cv cR wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi vy wal vx cv vz cv cop cR cR ccom wcel vx cv vy cv cR wbr vy cv vz
      cv cR wbr wa vy wex vx cv vz cv cop cR wcel vx cv vz cv cR wbr vy vx cv
      vz cv cR cR vx vex vz vex opelco vx cv vz cv cR wbr vx cv vz cv cop cR
      wcel vx cv vz cv cR df-br bicomi imbi12i vx cv vy cv cR wbr vy cv vz cv
      cR wbr wa vx cv vz cv cR wbr vy 19.23v bitr4i albii vx cv vy cv cR wbr vy
      cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz vy alcom bitri albii bitri $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x y z R $.  $d x y z S $.  $d z V $.
    $d z W $.
    $( Two ways to state a relation is reflexive.  Adapted from Tarski.
       (Contributed by FL, 15-Jan-2012.)  (Revised by NM, 30-Mar-2016.) $)
    issref $p |- ( ( _I |` A ) C_ R <-> A. x e. A x R x ) $=
      vx cv vx cv cR wbr vx cA wral vx cv cA wcel vx cv vx cv cR wbr wi vx wal
      vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi vx wal cid cA
      cres cR wss vx cv vx cv cR wbr vx cA df-ral vx cv vx cv cop cid cA cres
      wcel vx cv vx cv cop cR wcel wi vx cv cA wcel vx cv vx cv cR wbr wi vx vx
      cv vx cv cop cid cA cres wcel vx cv cA wcel vx cv vx cv cop cR wcel vx cv
      vx cv cR wbr vx cv cvv wcel vx cv vx cv cop cid cA cres wcel vx cv cA
      wcel wb vx vex vx cv cA cvv opelresi ax-mp vx cv vx cv cR wbr vx cv vx cv
      cop cR wcel vx cv vx cv cR df-br bicomi imbi12i albii vx cv vx cv cop cid
      cA cres wcel vx cv vx cv cop cR wcel wi vx wal cid cA cres cR wss vx cv
      vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi vx wal vy cv cid cA
      cres wcel vy cv cR wcel wi vy wal cid cA cres cR wss vx cv vx cv cop cid
      cA cres wcel vx cv vx cv cop cR wcel wi vx wal vx cv vx cv cop cid cA
      cres wcel vx cv vx cv cop cR wcel wi vx cvv wral vx cvv wral vy cv cid cA
      cres wcel vy cv cR wcel wi vy wal vx cv vx cv cop cid cA cres wcel vx cv
      vx cv cop cR wcel wi vx cvv wral vx cvv wral vx cv vx cv cop cid cA cres
      wcel vx cv vx cv cop cR wcel wi vx cvv wral vx cv vx cv cop cid cA cres
      wcel vx cv vx cv cop cR wcel wi vx wal vx cv vx cv cop cid cA cres wcel
      vx cv vx cv cop cR wcel wi vx cvv ralidm vx cv vx cv cop cid cA cres wcel
      vx cv vx cv cop cR wcel wi vx ralv bitri vx cv vx cv cop cid cA cres wcel
      vx cv vx cv cop cR wcel wi vx cvv wral vx cvv wral vy cv cid cA cres wcel
      vy cv cR wcel wi vy cvv cvv cxp wral vy cv cid cA cres wcel vy cv cR wcel
      wi vy wal vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi vx
      cvv wral vx cvv wral vx cv vz cv cop cid cA cres wcel vx cv vz cv cop cR
      wcel wi vz cvv wral vx cvv wral vy cv cid cA cres wcel vy cv cR wcel wi
      vy cvv cvv cxp wral vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR
      wcel wi vx cvv wral vx cv vz cv cop cid cA cres wcel vx cv vz cv cop cR
      wcel wi vz cvv wral vx cvv vx cv vx cv cop cid cA cres wcel vx cv vx cv
      cop cR wcel wi vx cvv wral vx cv cvv wcel vx cv vx cv cop cid cA cres
      wcel vx cv vx cv cop cR wcel wi wi vx wal vx cv vz cv cop cid cA cres
      wcel vx cv vz cv cop cR wcel wi vz cvv wral vx cv vx cv cop cid cA cres
      wcel vx cv vx cv cop cR wcel wi vx cvv df-ral vx cv cvv wcel vx cv vx cv
      cop cid cA cres wcel vx cv vx cv cop cR wcel wi wi vx cv vz cv cop cid cA
      cres wcel vx cv vz cv cop cR wcel wi vz cvv wral vx vx cv cvv wcel vx cv
      cvv wcel vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi wi
      vx cv vz cv cop cid cA cres wcel vx cv vz cv cop cR wcel wi vz cvv wral
      wi vx vex vx cv cvv wcel vx cv cvv wcel vx cv vx cv cop cid cA cres wcel
      vx cv vx cv cop cR wcel wi wi vx cv vx cv cop cid cA cres wcel vx cv vx
      cv cop cR wcel wi vx cv vz cv cop cid cA cres wcel vx cv vz cv cop cR
      wcel wi vz cvv wral vx cv cvv wcel vx cv vx cv cop cid cA cres wcel vx cv
      vx cv cop cR wcel wi pm2.27 vx cv vx cv cop cid cA cres wcel vx cv vx cv
      cop cR wcel wi vx cv vz cv cop cid cA cres wcel vx cv vz cv cop cR wcel
      wi vz cvv vz cv cvv wcel vx cv vz cv cop cid cA cres wcel vx cv vx cv cop
      cid cA cres wcel vx cv vx cv cop cR wcel wi vx cv vz cv cop cR wcel vz cv
      cvv wcel vx cv vz cv cop cid cA cres wcel vx cv vz cv cop cid wcel vx cv
      cA wcel wa vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi vx
      cv vz cv cop cR wcel wi vx cv vz cv cid cA cvv opelresg vx cv vz cv cop
      cid wcel vx cv cA wcel vx cv vx cv cop cid cA cres wcel vx cv vx cv cop
      cR wcel wi vx cv vz cv cop cR wcel wi vx cv vz cv cop cid wcel vx cv vz
      cv cid wbr vx cv cA wcel vx cv vx cv cop cid cA cres wcel vx cv vx cv cop
      cR wcel wi vx cv vz cv cop cR wcel wi wi vx cv vz cv cid df-br vx cv vz
      cv cid wbr vx vz weq vx cv cA wcel vx cv vx cv cop cid cA cres wcel vx cv
      vx cv cop cR wcel wi vx cv vz cv cop cR wcel wi wi vx cv vz cv vz vex
      ideq vx cv cA wcel vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR
      wcel wi vx vz weq vx cv vz cv cop cR wcel vx cv cA wcel vx cv vx cv cop
      cid cA cres wcel vx cv vx cv cop cR wcel wi vx vz weq vx cv vz cv cop cR
      wcel wi wi vx cv cA wcel vx cv cA wcel vx cv vx cv cop cid cA cres wcel
      vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi vx vz weq vx
      cv vz cv cop cR wcel wi wi vx cv cA cA opelresi vx cv vx cv cop cid cA
      cres wcel vx cv vx cv cop cid cA cres wcel vx cv vx cv cop cR wcel wi vx
      cv vx cv cop cR wcel vx vz weq vx cv vz cv cop cR wcel wi vx cv vx cv cop
      cid cA cres wcel vx cv vx cv cop cR wcel pm2.27 vx vz weq vx cv vx cv cop
      cR wcel vx cv vz cv cop cR wcel vx vz weq vx cv vx cv cop vx cv vz cv cop
      cR vx cv vz cv vx cv opeq2 eleq1d biimpcd syl6 syl6bir pm2.43i com3r
      sylbi sylbir imp syl6bi com3r ralrimiv syl6 ax-mp sps sylbi ralimi vy cv
      cid cA cres wcel vy cv cR wcel wi vx cv vz cv cop cid cA cres wcel vx cv
      vz cv cop cR wcel wi vy vx vz cvv cvv vy cv vx cv vz cv cop wceq vy cv
      cid cA cres wcel vx cv vz cv cop cid cA cres wcel vy cv cR wcel vx cv vz
      cv cop cR wcel vy cv vx cv vz cv cop cid cA cres eleq1 vy cv vx cv vz cv
      cop cR eleq1 imbi12d ralxp sylibr vy cv cid cA cres wcel vy cv cR wcel wi
      vy cvv cvv cxp wral vy cv cvv cvv cxp wcel vy cv cid cA cres wcel vy cv
      cR wcel wi wi vy wal vy cv cid cA cres wcel vy cv cR wcel wi vy wal vy cv
      cid cA cres wcel vy cv cR wcel wi vy cvv cvv cxp df-ral vy cv cvv cvv cxp
      wcel vy cv cid cA cres wcel vy cv cR wcel wi wi vy cv cid cA cres wcel vy
      cv cR wcel wi vy vy cv cid cA cres wcel vy cv cvv cvv cxp wcel vy cv cid
      cA cres wcel wa vy cv cvv cvv cxp wcel vy cv cid cA cres wcel vy cv cR
      wcel wi wi vy cv cR wcel vy cv cid cA cres wcel vy cv cvv cvv cxp wcel
      cid cA cres cvv cvv cxp vy cv cid cA cres wrel cid cA cres cvv cvv cxp
      wss cid cA relres cid cA cres df-rel mpbi sseli ancri vy cv cvv cvv cxp
      wcel vy cv cid cA cres wcel vy cv cR wcel pm3.31 syl5 alimi sylbi syl
      sylbir vy cid cA cres cR dfss2 sylibr cid cA cres cR wss vx cv vx cv cop
      cid cA cres wcel vx cv vx cv cop cR wcel wi vx cid cA cres cR vx cv vx cv
      cop ssel alrimiv impbii 3bitr2ri $.

    $( Two ways of saying a relation is symmetric.  Similar to definition of
       symmetry in [Schechter] p. 51.  (Contributed by NM, 28-Dec-1996.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    cnvsym $p |- ( `' R C_ R <-> A. x A. y ( x R y -> y R x ) ) $=
      vy cv vx cv cop cR ccnv wcel vy cv vx cv cop cR wcel wi vx wal vy wal vy
      cv vx cv cop cR ccnv wcel vy cv vx cv cop cR wcel wi vy wal vx wal cR
      ccnv cR wss vx cv vy cv cR wbr vy cv vx cv cR wbr wi vy wal vx wal vy cv
      vx cv cop cR ccnv wcel vy cv vx cv cop cR wcel wi vy vx alcom cR ccnv
      wrel cR ccnv cR wss vy cv vx cv cop cR ccnv wcel vy cv vx cv cop cR wcel
      wi vx wal vy wal wb cR relcnv vy vx cR ccnv cR ssrel ax-mp vx cv vy cv cR
      wbr vy cv vx cv cR wbr wi vy cv vx cv cop cR ccnv wcel vy cv vx cv cop cR
      wcel wi vx vy vx cv vy cv cR wbr vy cv vx cv cop cR ccnv wcel vy cv vx cv
      cR wbr vy cv vx cv cop cR wcel vx cv vy cv cR wbr vy cv vx cv cR ccnv wbr
      vy cv vx cv cop cR ccnv wcel vy cv vx cv cR vy vex vx vex brcnv vy cv vx
      cv cR ccnv df-br bitr3i vy cv vx cv cR df-br imbi12i 2albii 3bitr4i $.

    $( Two ways of saying a relation is antisymmetric.  Definition of
       antisymmetry in [Schechter] p. 51.  (Contributed by NM, 9-Sep-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    intasym $p |- ( ( R i^i `' R ) C_ _I <->
                  A. x A. y ( ( x R y /\ y R x ) -> x = y ) ) $=
      cR cR ccnv cin cid wss vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv
      cop cid wcel wi vy wal vx wal vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx
      cv vy cv wceq wi vy wal vx wal cR ccnv wrel cR cR ccnv cin wrel cR cR
      ccnv cin cid wss vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cid
      wcel wi vy wal vx wal wb cR relcnv cR cR ccnv relin2 vx vy cR cR ccnv cin
      cid ssrel mp2b vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cid
      wcel wi vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vx
      vy vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cR wbr vy cv vx cv cR
      wbr wa vx cv vy cv cop cid wcel vx cv vy cv wceq vx cv vy cv cop cR cR
      ccnv cin wcel vx cv vy cv cop cR wcel vx cv vy cv cop cR ccnv wcel wa vx
      cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv cop cR cR ccnv elin vx
      cv vy cv cR wbr vx cv vy cv cop cR wcel vy cv vx cv cR wbr vx cv vy cv
      cop cR ccnv wcel vx cv vy cv cR df-br vy cv vx cv cR wbr vx cv vy cv cR
      ccnv wbr vx cv vy cv cop cR ccnv wcel vx cv vy cv cR vx vex vy vex brcnv
      vx cv vy cv cR ccnv df-br bitr3i anbi12i bitr4i vx cv vy cv cop cid wcel
      vx cv vy cv cid wbr vx cv vy cv wceq vx cv vy cv cid df-br vx cv vy cv vy
      vex ideq bitr3i imbi12i 2albii bitri $.

    $( Two ways of saying a relation is antisymmetric and reflexive.
       ` U. U. R ` is the field of a relation by ~ relfld .  (Contributed by
       NM, 6-May-2008.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    asymref $p |- ( ( R i^i `' R ) = ( _I |` U. U. R ) <->
       A. x e. U. U. R A. y ( ( x R y /\ y R x ) <-> x = y ) ) $=
      vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cid cR cuni cuni cres
      wcel wb vy wal vx wal vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx
      cv cR wbr wa vx cv vy cv wceq wb vy wal wi vx wal cR cR ccnv cin cid cR
      cuni cuni cres wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv
      wceq wb vy wal vx cR cuni cuni wral vx cv vy cv cop cR cR ccnv cin wcel
      vx cv vy cv cop cid cR cuni cuni cres wcel wb vy wal vx cv cR cuni cuni
      wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wb vy wal
      wi vx vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cid cR cuni
      cuni cres wcel wb vy wal vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv
      vx cv cR wbr wa vx cv vy cv wceq wb wi vy wal vx cv cR cuni cuni wcel vx
      cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wb vy wal wi vx cv
      vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cid cR cuni cuni cres wcel
      wb vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv
      vy cv wceq wb wi vy vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv cR
      cuni cuni wcel vx cv vy cv wceq wa wb vx cv cR cuni cuni wcel vx cv vy cv
      cR wbr vy cv vx cv cR wbr wa wa vx cv cR cuni cuni wcel vx cv vy cv wceq
      wa wb vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cid cR cuni
      cuni cres wcel wb vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx cv
      cR wbr wa vx cv vy cv wceq wb wi vx cv vy cv cR wbr vy cv vx cv cR wbr wa
      vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa wa vx cv
      cR cuni cuni wcel vx cv vy cv wceq wa vx cv vy cv cR wbr vy cv vx cv cR
      wbr wa vx cv cR cuni cuni wcel vx cv vy cv cR wbr vx cv cR cuni cuni wcel
      vy cv vx cv cR wbr vx cv vy cv cR wbr vx cv cR cuni cuni wcel vy cv cR
      cuni cuni wcel vx cv vy cv cR wbr vx cv vy cv cop cR wcel vx cv cR cuni
      cuni wcel vy cv cR cuni cuni wcel wa vx cv vy cv cR df-br vx cv vy cv cR
      vx vex vy vex opeluu sylbi simpld adantr pm4.71ri bibi1i vx cv vy cv cop
      cR cR ccnv cin wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv
      cop cid cR cuni cuni cres wcel vx cv cR cuni cuni wcel vx cv vy cv wceq
      wa vx cv vy cv cop cR cR ccnv cin wcel vx cv vy cv cop cR wcel vx cv vy
      cv cop cR ccnv wcel wa vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy
      cv cop cR cR ccnv elin vx cv vy cv cR wbr vx cv vy cv cop cR wcel vy cv
      vx cv cR wbr vx cv vy cv cop cR ccnv wcel vx cv vy cv cR df-br vy cv vx
      cv cR wbr vx cv vy cv cR ccnv wbr vx cv vy cv cop cR ccnv wcel vx cv vy
      cv cR vx vex vy vex brcnv vx cv vy cv cR ccnv df-br bitr3i anbi12i bitr4i
      vx cv vy cv cop cid cR cuni cuni cres wcel vx cv vy cv cop cid wcel vx cv
      cR cuni cuni wcel wa vx cv cR cuni cuni wcel vx cv vy cv wceq wa vx cv vy
      cv cid cR cuni cuni vy vex opelres vx cv vy cv cop cid wcel vx cv vy cv
      wceq vx cv cR cuni cuni wcel vx cv vy cv cop cid wcel vx cv vy cv cid wbr
      vx cv vy cv wceq vx cv vy cv cid df-br vx cv vy cv vy vex ideq bitr3i
      anbi2ci bitri bibi12i vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx
      cv cR wbr wa vx cv vy cv wceq pm5.32 3bitr4i albii vx cv cR cuni cuni
      wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wb vy
      19.21v bitri albii cR cR ccnv cin wrel cid cR cuni cuni cres wrel cR cR
      ccnv cin cid cR cuni cuni cres wceq vx cv vy cv cop cR cR ccnv cin wcel
      vx cv vy cv cop cid cR cuni cuni cres wcel wb vy wal vx wal wb cR ccnv
      wrel cR cR ccnv cin wrel cR relcnv cR cR ccnv relin2 ax-mp cid cR cuni
      cuni relres vx vy cR cR ccnv cin cid cR cuni cuni cres eqrel mp2an vx cv
      vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wb vy wal vx cR cuni
      cuni df-ral 3bitr4i $.

    $( Two ways of saying a relation is antisymmetric and reflexive.
       (Contributed by NM, 6-May-2008.)  (Proof shortened by Mario Carneiro,
       4-Dec-2016.) $)
    asymref2 $p |- ( ( R i^i `' R ) = ( _I |` U. U. R ) <->
   ( A. x e. U. U. R x R x /\ A. x A. y ( ( x R y /\ y R x ) -> x = y ) ) ) $=
      cR cR ccnv cin cid cR cuni cuni cres wceq vx cv vy cv cR wbr vy cv vx cv
      cR wbr wa vx cv vy cv wceq wb vy wal vx cR cuni cuni wral vx cv vy cv cR
      wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cv vy cv wceq vx
      cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy wal wa vx cR cuni cuni wral
      vx cv vx cv cR wbr vx cR cuni cuni wral vx cv vy cv cR wbr vy cv vx cv cR
      wbr wa vx cv vy cv wceq wi vy wal vx wal wa vx vy cR asymref vx cv vy cv
      cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wb vy wal vx cv vy cv cR
      wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cv vy cv wceq vx
      cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy wal wa vx cR cuni cuni vx cv
      vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq vy albiim ralbii vx
      cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cv vy
      cv wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy wal wa vx cR cuni
      cuni wral vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy
      wal vx cR cuni cuni wral vx cv vy cv wceq vx cv vy cv cR wbr vy cv vx cv
      cR wbr wa wi vy wal vx cR cuni cuni wral wa vx cv vy cv wceq vx cv vy cv
      cR wbr vy cv vx cv cR wbr wa wi vy wal vx cR cuni cuni wral vx cv vy cv
      cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cR cuni cuni
      wral wa vx cv vx cv cR wbr vx cR cuni cuni wral vx cv vy cv cR wbr vy cv
      vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx wal wa vx cv vy cv cR wbr
      vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cv vy cv wceq vx cv
      vy cv cR wbr vy cv vx cv cR wbr wa wi vy wal vx cR cuni cuni r19.26 vx cv
      vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cR cuni
      cuni wral vx cv vy cv wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy
      wal vx cR cuni cuni wral ancom vx cv vy cv wceq vx cv vy cv cR wbr vy cv
      vx cv cR wbr wa wi vy wal vx cR cuni cuni wral vx cv vx cv cR wbr vx cR
      cuni cuni wral vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq
      wi vy wal vx cR cuni cuni wral vx cv vy cv cR wbr vy cv vx cv cR wbr wa
      vx cv vy cv wceq wi vy wal vx wal vx cv vy cv wceq vx cv vy cv cR wbr vy
      cv vx cv cR wbr wa wi vy wal vx cv vx cv cR wbr vx cR cuni cuni vx cv vy
      cv wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy wal vy cv vx cv
      wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy wal vx cv vx cv cR
      wbr vx cv vy cv wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy cv vx
      cv wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa wi vy vx cv vy cv wceq
      vy cv vx cv wceq vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx vy equcom
      imbi1i albii vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vx cv cR wbr
      vy vx vx cv vx cv cR wbr vy nfv vy cv vx cv wceq vx cv vy cv cR wbr vy cv
      vx cv cR wbr wa vx cv vx cv cR wbr vx cv vx cv cR wbr wa vx cv vx cv cR
      wbr vy cv vx cv wceq vx cv vy cv cR wbr vx cv vx cv cR wbr vy cv vx cv cR
      wbr vx cv vx cv cR wbr vy cv vx cv vx cv cR breq2 vy cv vx cv vx cv cR
      breq1 anbi12d vx cv vx cv cR wbr anidm syl6bb equsal bitri ralbii vx cv
      vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cR cuni
      cuni wral vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx cv cR wbr
      wa vx cv vy cv wceq wi vy wal wi vx wal vx cv vy cv cR wbr vy cv vx cv cR
      wbr wa vx cv vy cv wceq wi vy wal vx wal vx cv vy cv cR wbr vy cv vx cv
      cR wbr wa vx cv vy cv wceq wi vy wal vx cR cuni cuni df-ral vx cv cR cuni
      cuni wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy
      wal wi vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy
      wal vx vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wa
      vx cv vy cv wceq wi vy wal wi vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx
      cv vy cv wceq wi vy wal vx cv cR cuni cuni wcel vx cv vy cv cR wbr vy cv
      vx cv cR wbr wa vx cv vy cv wceq wi vy wal vx cv vy cv cR wbr vy cv vx cv
      cR wbr wa vx cv vy cv wceq wi vy wal vx cv cR cuni cuni wcel wn vx cv vy
      cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq wi vy vx cv vy cv cR wbr
      vy cv vx cv cR wbr wa vx cv cR cuni cuni wcel wn vx cv vy cv wceq vx cv
      vy cv cR wbr vy cv vx cv cR wbr wa vx cv cR cuni cuni wcel vx cv vy cv
      wceq vx cv vy cv cR wbr vx cv cR cuni cuni wcel vy cv vx cv cR wbr vx cv
      vy cv cR wbr vx cv vy cv cop cR wcel vx cv cR cuni cuni wcel vx cv vy cv
      cR df-br vx cv vy cv cop cR wcel vx cv cR cuni cuni wcel vy cv cR cuni
      cuni wcel vx cv vy cv cR vx vex vy vex opeluu simpld sylbi adantr pm2.24d
      com12 alrimiv vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq
      wi vy wal id ja vx cv vy cv cR wbr vy cv vx cv cR wbr wa vx cv vy cv wceq
      wi vy wal vx cv cR cuni cuni wcel ax-1 impbii albii bitri anbi12i 3bitri
      3bitri $.

    $( Two ways of saying a relation is irreflexive.  Definition of
       irreflexivity in [Schechter] p. 51.  (Contributed by NM, 9-Sep-2004.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    intirr $p |- ( ( R i^i _I ) = (/) <-> A. x -. x R x ) $=
      cR cid cin c0 wceq vx cv vy cv cop cid wcel vx cv vy cv cop cvv cR cdif
      wcel wi vy wal vx wal vy cv vx cv wceq vx cv vy cv cR wbr wn wi vy wal vx
      wal vx cv vx cv cR wbr wn vx wal cR cid cin c0 wceq cid cR cin c0 wceq
      cid cvv cR cdif wss vx cv vy cv cop cid wcel vx cv vy cv cop cvv cR cdif
      wcel wi vy wal vx wal cR cid cin cid cR cin c0 cR cid incom eqeq1i cid cR
      disj2 cid wrel cid cvv cR cdif wss vx cv vy cv cop cid wcel vx cv vy cv
      cop cvv cR cdif wcel wi vy wal vx wal wb reli vx vy cid cvv cR cdif ssrel
      ax-mp 3bitri vy cv vx cv wceq vx cv vy cv cR wbr wn wi vx cv vy cv cop
      cid wcel vx cv vy cv cop cvv cR cdif wcel wi vx vy vy cv vx cv wceq vx cv
      vy cv cop cid wcel vx cv vy cv cR wbr wn vx cv vy cv cop cvv cR cdif wcel
      vy cv vx cv wceq vx cv vy cv wceq vx cv vy cv cid wbr vx cv vy cv cop cid
      wcel vy cv vx cv eqcom vx cv vy cv vy vex ideq vx cv vy cv cid df-br
      3bitr2i vx cv vy cv cop cR wcel vx cv vy cv cop cvv cR cdif wcel vx cv vy
      cv cR wbr vx cv vy cv cop cR wcel wn vx cv vy cv cop cvv wcel vx cv vy cv
      cop cR wcel wn wa vx cv vy cv cop cvv cR cdif wcel vx cv vy cv cop cvv
      wcel vx cv vy cv cop cR wcel wn vx cv vy cv opex biantrur vx cv vy cv cop
      cvv cR eldif bitr4i vx cv vy cv cR df-br xchnxbir imbi12i 2albii vy cv vx
      cv wceq vx cv vy cv cR wbr wn wi vy wal vx cv vx cv cR wbr wn vx vx cv vy
      cv cR wbr wn vx cv vx cv cR wbr wn vy vx vx cv vx cv cR wbr wn vy nfv vy
      cv vx cv wceq vx cv vy cv cR wbr vx cv vx cv cR wbr vy cv vx cv vx cv cR
      breq2 notbid equsal albii 3bitr2i $.

    $( Two ways of saying that two elements have an upper bound.  (Contributed
       by Mario Carneiro, 3-Nov-2015.) $)
    brcodir $p |- ( ( A e. V /\ B e. W ) ->
      ( A ( `' R o. R ) B <-> E. z ( A R z /\ B R z ) ) ) $=
      cA cV wcel cB cW wcel wa cA cB cR ccnv cR ccom wbr cA vz cv cR wbr vz cv
      cB cR ccnv wbr wa vz wex cA vz cv cR wbr cB vz cv cR wbr wa vz wex vz cA
      cB cR ccnv cR cV cW brcog cA cV wcel cB cW wcel wa cA vz cv cR wbr vz cv
      cB cR ccnv wbr wa cA vz cv cR wbr cB vz cv cR wbr wa vz cB cW wcel cA vz
      cv cR wbr vz cv cB cR ccnv wbr wa cA vz cv cR wbr cB vz cv cR wbr wa wb
      cA cV wcel cB cW wcel vz cv cB cR ccnv wbr cB vz cv cR wbr cA vz cv cR
      wbr vz cv cvv wcel cB cW wcel vz cv cB cR ccnv wbr cB vz cv cR wbr wb vz
      vex vz cv cB cvv cW cR brcnvg mpan anbi2d adantl exbidv bitrd $.

    $( Two ways of saying a relation is directed.  (Contributed by Mario
       Carneiro, 22-Nov-2013.) $)
    codir $p |- ( ( A X. B ) C_ ( `' R o. R ) <-> A. x e. A A. y e. B
      E. z ( x R z /\ y R z ) ) $=
      vx cv vy cv cop cA cB cxp wcel vx cv vy cv cop cR ccnv cR ccom wcel wi vy
      wal vx wal vx cv cA wcel vy cv cB wcel wa vx cv vz cv cR wbr vy cv vz cv
      cR wbr wa vz wex wi vy wal vx wal cA cB cxp cR ccnv cR ccom wss vx cv vz
      cv cR wbr vy cv vz cv cR wbr wa vz wex vy cB wral vx cA wral vx cv vy cv
      cop cA cB cxp wcel vx cv vy cv cop cR ccnv cR ccom wcel wi vx cv cA wcel
      vy cv cB wcel wa vx cv vz cv cR wbr vy cv vz cv cR wbr wa vz wex wi vx vy
      vx cv vy cv cop cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa vx cv vy cv
      cop cR ccnv cR ccom wcel vx cv vz cv cR wbr vy cv vz cv cR wbr wa vz wex
      vx cv vy cv cA cB opelxp vx cv vy cv cop cR ccnv cR ccom wcel vx cv vy cv
      cR ccnv cR ccom wbr vx cv vz cv cR wbr vy cv vz cv cR wbr wa vz wex vx cv
      vy cv cR ccnv cR ccom df-br vx cv cvv wcel vy cv cvv wcel vx cv vy cv cR
      ccnv cR ccom wbr vx cv vz cv cR wbr vy cv vz cv cR wbr wa vz wex wb vx
      vex vy vex vz vx cv vy cv cR cvv cvv brcodir mp2an bitr3i imbi12i 2albii
      cA cB cxp wrel cA cB cxp cR ccnv cR ccom wss vx cv vy cv cop cA cB cxp
      wcel vx cv vy cv cop cR ccnv cR ccom wcel wi vy wal vx wal wb cA cB relxp
      vx vy cA cB cxp cR ccnv cR ccom ssrel ax-mp vx cv vz cv cR wbr vy cv vz
      cv cR wbr wa vz wex vx vy cA cB r2al 3bitr4i $.

    $( A quantifier-free way of expressing the total order predicate.
       (Contributed by Mario Carneiro, 22-Nov-2013.) $)
    qfto $p |- ( ( A X. B ) C_ ( R u. `' R ) <->
                 A. x e. A A. y e. B ( x R y \/ y R x ) ) $=
      vx cv vy cv cop cA cB cxp wcel vx cv vy cv cop cR cR ccnv cun wcel wi vy
      wal vx wal vx cv cA wcel vy cv cB wcel wa vx cv vy cv cR wbr vy cv vx cv
      cR wbr wo wi vy wal vx wal cA cB cxp cR cR ccnv cun wss vx cv vy cv cR
      wbr vy cv vx cv cR wbr wo vy cB wral vx cA wral vx cv vy cv cop cA cB cxp
      wcel vx cv vy cv cop cR cR ccnv cun wcel wi vx cv cA wcel vy cv cB wcel
      wa vx cv vy cv cR wbr vy cv vx cv cR wbr wo wi vx vy vx cv vy cv cop cA
      cB cxp wcel vx cv cA wcel vy cv cB wcel wa vx cv vy cv cop cR cR ccnv cun
      wcel vx cv vy cv cR wbr vy cv vx cv cR wbr wo vx cv vy cv cA cB opelxp vx
      cv vy cv cR cR ccnv cun wbr vx cv vy cv cR wbr vx cv vy cv cR ccnv wbr wo
      vx cv vy cv cop cR cR ccnv cun wcel vx cv vy cv cR wbr vy cv vx cv cR wbr
      wo vx cv vy cv cR cR ccnv brun vx cv vy cv cR cR ccnv cun df-br vx cv vy
      cv cR ccnv wbr vy cv vx cv cR wbr vx cv vy cv cR wbr vx cv vy cv cR vx
      vex vy vex brcnv orbi2i 3bitr3i imbi12i 2albii cA cB cxp wrel cA cB cxp
      cR cR ccnv cun wss vx cv vy cv cop cA cB cxp wcel vx cv vy cv cop cR cR
      ccnv cun wcel wi vy wal vx wal wb cA cB relxp vx vy cA cB cxp cR cR ccnv
      cun ssrel ax-mp vx cv vy cv cR wbr vy cv vx cv cR wbr wo vx vy cA cB r2al
      3bitr4i $.

    $( A square cross product ` ( A X. A ) ` is a transitive relation.
       (Contributed by FL, 31-Jul-2009.) $)
    xpidtr $p |- ( ( A X. A ) o. ( A X. A ) ) C_ ( A X. A ) $=
      cA cA cxp cA cA cxp ccom cA cA cxp wss vx cv vy cv cA cA cxp wbr vy cv vz
      cv cA cA cxp wbr wa vx cv vz cv cA cA cxp wbr wi vz wal vy wal vx wal vx
      cv vy cv cA cA cxp wbr vy cv vz cv cA cA cxp wbr wa vx cv vz cv cA cA cxp
      wbr wi vz wal vx vy vx cv vy cv cA cA cxp wbr vy cv vz cv cA cA cxp wbr
      wa vx cv vz cv cA cA cxp wbr wi vz vx cv vy cv cA cA cxp wbr vy cv vz cv
      cA cA cxp wbr vx cv vz cv cA cA cxp wbr vx cv vy cv cA cA cxp wbr vx cv
      cA wcel vy cv cA wcel wa vy cv vz cv cA cA cxp wbr vx cv vz cv cA cA cxp
      wbr wi vx cv vy cv cA cA brxp vx cv cA wcel vy cv vz cv cA cA cxp wbr vx
      cv vz cv cA cA cxp wbr wi vy cv cA wcel vy cv vz cv cA cA cxp wbr vx cv
      cA wcel vx cv vz cv cA cA cxp wbr vy cv vz cv cA cA cxp wbr vy cv cA wcel
      vz cv cA wcel wa vx cv cA wcel vx cv vz cv cA cA cxp wbr wi vy cv vz cv
      cA cA brxp vz cv cA wcel vx cv cA wcel vx cv vz cv cA cA cxp wbr wi vy cv
      cA wcel vx cv vz cv cA cA cxp wbr vx cv cA wcel vz cv cA wcel vx cv vz cv
      cA cA brxp simplbi2com adantl sylbi com12 adantr sylbi imp ax-gen gen2 vx
      vy vz cA cA cxp cotr mpbir $.

    $( The intersection of two transitive classes is transitive.  (Contributed
       by FL, 31-Jul-2009.) $)
    trin2 $p |- ( ( ( R o. R ) C_ R /\ ( S o. S ) C_ S )
      -> ( ( R i^i S ) o. ( R i^i S ) ) C_ ( R i^i S ) ) $=
      cR cR ccom cR wss cS cS ccom cS wss wa vx cv vy cv cR cS cin wbr vy cv vz
      cv cR cS cin wbr wa vx cv vz cv cR cS cin wbr wi vz wal vy wal vx wal cR
      cS cin cR cS cin ccom cR cS cin wss cR cR ccom cR wss cS cS ccom cS wss
      vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx cv vz cv cR cS
      cin wbr wi vz wal vy wal vx wal cR cR ccom cR wss vx cv vy cv cR wbr vy
      cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz wal vy wal vx wal cS cS ccom
      cS wss vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx cv vz cv
      cR cS cin wbr wi vz wal vy wal vx wal wi vx vy vz cR cotr cS cS ccom cS
      wss vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz wal
      vy wal vx wal vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx
      cv vz cv cR cS cin wbr wi vz wal vy wal vx wal cS cS ccom cS wss vx cv vy
      cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi vz wal vy wal vx
      wal vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz wal
      vy wal vx wal vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx
      cv vz cv cR cS cin wbr wi vz wal vy wal vx wal wi vx vy vz cS cotr vx cv
      vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi vz wal vy wal vx
      wal vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz wal
      vy wal vx wal vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx
      cv vz cv cR cS cin wbr wi vz wal vy wal vx wal vx cv vy cv cS wbr vy cv
      vz cv cS wbr wa vx cv vz cv cS wbr wi vz wal vy wal vx cv vy cv cR wbr vy
      cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz wal vy wal vx cv vy cv cR cS
      cin wbr vy cv vz cv cR cS cin wbr wa vx cv vz cv cR cS cin wbr wi vz wal
      vy wal vx vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi
      vz wal vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz
      wal vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx cv vz cv cR
      cS cin wbr wi vz wal vy vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz
      cv cS wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr
      wi vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx cv vz cv cR
      cS cin wbr wi vz vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS
      wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa
      vx cv vy cv cR cS cin wbr vy cv vz cv cR cS cin wbr wa vx cv vz cv cR wbr
      vx cv vz cv cS wbr wa vx cv vz cv cR cS cin wbr vx cv vy cv cR cS cin wbr
      vy cv vz cv cR cS cin wbr wa vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx
      cv vz cv cS wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv
      cR wbr wi wa vx cv vz cv cR wbr vx cv vz cv cS wbr wa vx cv vy cv cR cS
      cin wbr vx cv vy cv cR wbr vx cv vy cv cS wbr wa vy cv vz cv cR wbr vy cv
      vz cv cS wbr wa vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS
      wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa
      vx cv vz cv cR wbr vx cv vz cv cS wbr wa wi vy cv vz cv cR cS cin wbr vx
      cv vy cv cR cS brin vy cv vz cv cR cS brin vx cv vy cv cR wbr vy cv vz cv
      cR wbr vx cv vy cv cS wbr vy cv vz cv cS wbr vx cv vy cv cS wbr vy cv vz
      cv cS wbr wa vx cv vz cv cS wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr
      wa vx cv vz cv cR wbr wi wa vx cv vz cv cR wbr vx cv vz cv cS wbr wa wi
      vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi vx cv vy
      cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vx cv vy cv cR
      wbr vy cv vz cv cR wbr wa vx cv vy cv cS wbr vy cv vz cv cS wbr wa wa vx
      cv vz cv cR wbr vx cv vz cv cS wbr wa vx cv vy cv cS wbr vy cv vz cv cS
      wbr wa vx cv vz cv cS wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx
      cv vz cv cR wbr wi wa vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr vx cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr vx
      cv vy cv cS wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi simpr vx cv vy cv cS
      wbr vy cv vz cv cS wbr wa vx cv vz cv cS wbr wi vx cv vy cv cR wbr vy cv
      vz cv cR wbr wa vx cv vz cv cR wbr wi simpl anim12d com12 an4s syl2anb
      com12 vx cv vz cv cR cS brin syl6ibr alanimi alanimi alanimi ex sylbi
      com12 sylbi imp vx vy vz cR cS cin cotr sylibr $.

    $( A partial order relation is irreflexive.  (Contributed by Mario
       Carneiro, 2-Nov-2015.) $)
    poirr2 $p |- ( R Po A -> ( R i^i ( _I |` A ) ) = (/) ) $=
      cA cR wpo cR cid cA cres cin c0 wss cR cid cA cres cin c0 wceq cA cR wpo
      vx vy cR cid cA cres cin c0 cid cA cres wrel cR cid cA cres cin wrel cA
      cR wpo cid cA relres cR cid cA cres relin2 mp1i vx cv vy cv cop cR cid cA
      cres cin wcel vx cv vy cv cR wbr vx cv vy cv cid cA cres wbr wa cA cR wpo
      vx cv vy cv cop c0 wcel vx cv vy cv cop cR cid cA cres cin wcel vx cv vy
      cv cR cid cA cres cin wbr vx cv vy cv cR wbr vx cv vy cv cid cA cres wbr
      wa vx cv vy cv cR cid cA cres cin df-br vx cv vy cv cR cid cA cres brin
      bitr3i cA cR wpo vx cv vy cv cR wbr vx cv vy cv cid cA cres wbr wa vx cv
      vy cv cop c0 wcel cA cR wpo vx cv vy cv cR wbr vx cv vy cv cid cA cres
      wbr wn wi vx cv vy cv cR wbr vx cv vy cv cid cA cres wbr wa wn cA cR wpo
      vx cv vy cv cid cA cres wbr vx cv vy cv cR wbr vx cv vy cv cid cA cres
      wbr vx cv vy cv cid wbr vx cv cA wcel wa cA cR wpo vx cv vy cv cR wbr wn
      vx cv vy cv cid cA vy vex brres cA cR wpo vx cv cA wcel vx cv vy cv cid
      wbr vx cv vy cv cR wbr wn cA cR wpo vx cv cA wcel vx cv vy cv cid wbr vx
      cv vy cv cR wbr wn cA cR wpo vx cv cA wcel wa vx cv vx cv cR wbr wn vx cv
      vy cv cid wbr vx cv vy cv cR wbr wn cA vx cv cR poirr vx cv vy cv cid wbr
      vx cv vx cv cR wbr vx cv vy cv cR wbr vx cv vy cv cid wbr vx cv vy cv
      wceq vx cv vx cv cR wbr vx cv vy cv cR wbr wb vx cv vy cv vy vex ideq vx
      cv vy cv vx cv cR breq2 sylbi notbid syl5ibcom expimpd ancomsd syl5bi
      con2d vx cv vy cv cR wbr vx cv vy cv cid cA cres wbr imnan sylib pm2.21d
      syl5bi relssdv cR cid cA cres cin ss0 syl $.
  $}

  $( The relation induced by a transitive relation on a part of its field is
     transitive.  (Taking the intersection of a relation with a square cross
     product is a way to restrict it to a subset of its field.)  (Contributed
     by FL, 31-Jul-2009.) $)
  trinxp $p |- ( ( R o. R ) C_ R ->
  ( ( R i^i ( A X. A ) ) o. ( R i^i ( A X. A ) ) ) C_ ( R i^i ( A X. A ) ) ) $=
    cR cR ccom cR wss cA cA cxp cA cA cxp ccom cA cA cxp wss cR cA cA cxp cin
    cR cA cA cxp cin ccom cR cA cA cxp cin wss cA xpidtr cR cA cA cxp trin2
    mpan2 $.

  ${
    soi.1 $e |- R Or S $.
    soi.2 $e |- R C_ ( S X. S ) $.
    $( A strict order relation is irreflexive.  (Contributed by NM,
       10-Feb-1996.)  (Revised by Mario Carneiro, 10-May-2013.) $)
    soirri $p |- -. A R A $=
      cA cS wcel cA cS wcel wa cA cA cR wbr wn cA cS wcel cA cA cR wbr wn cA cS
      wcel cS cR wor cA cS wcel cA cA cR wbr wn soi.1 cS cA cR sonr mpan adantl
      cA cA cR wbr cA cS wcel cA cS wcel wa cA cA cS cS cR soi.2 brel con3i
      pm2.61i $.

    ${
      $d A x $.  $d B x $.  $d R x $.
      $( A strict order relation is a transitive relation.  (Contributed by NM,
         10-Feb-1996.)  (Revised by Mario Carneiro, 10-May-2013.) $)
      sotri $p |- ( ( A R B /\ B R C ) -> A R C ) $=
        cA cS wcel cB cS wcel cC cS wcel wa wa cA cB cR wbr cB cC cR wbr wa cA
        cC cR wbr cA cB cR wbr cA cS wcel cB cC cR wbr cB cS wcel cC cS wcel wa
        cA cB cR wbr cA cS wcel cB cS wcel cA cB cS cS cR soi.2 brel simpld cB
        cC cS cS cR soi.2 brel anim12i cA cS wcel cB cS wcel cC cS wcel cA cB
        cR wbr cB cC cR wbr wa cA cC cR wbr wi cS cR wor cA cS wcel cB cS wcel
        cC cS wcel w3a cA cB cR wbr cB cC cR wbr wa cA cC cR wbr wi soi.1 cS cA
        cB cC cR sotr mpan 3expb mpcom $.

      $( A strict order relation has no 2-cycle loops.  (Contributed by NM,
         10-Feb-1996.)  (Revised by Mario Carneiro, 10-May-2013.) $)
      son2lpi $p |- -. ( A R B /\ B R A ) $=
        cA cB cR wbr cB cA cR wbr wa cA cA cR wbr cA cR cS soi.1 soi.2 soirri
        cA cB cA cR cS soi.1 soi.2 sotri mto $.

      $( A transitivity relation.  (Read ` A <_ B ` and ` B < C ` implies
         ` A < C ` .)  (Contributed by Mario Carneiro, 10-May-2013.) $)
      sotri2 $p |- ( ( A e. S /\ -. B R A /\ B R C ) -> A R C ) $=
        cA cS wcel cB cA cR wbr wn cB cC cR wbr cA cC cR wbr cB cC cR wbr cA cS
        wcel cB cA cR wbr wn cA cC cR wbr cB cC cR wbr cB cS wcel cA cS wcel cB
        cA cR wbr wn cA cC cR wbr wi cB cC cR wbr cB cS wcel cC cS wcel cB cC
        cS cS cR soi.2 brel simpld cB cS wcel cA cS wcel wa cB cA cR wbr wn cB
        cC cR wbr cA cC cR wbr cB cS wcel cA cS wcel wa cB cA cR wbr wn cB cA
        wceq cA cB cR wbr wo cB cC cR wbr cA cC cR wbr wi cB cS wcel cA cS wcel
        wa cB cA cR wbr cB cA wceq cA cB cR wbr wo cS cR wor cB cS wcel cA cS
        wcel wa cB cA cR wbr cB cA wceq cA cB cR wbr wo wn wb soi.1 cS cB cA cR
        sotric mpan con2bid cB cA wceq cB cC cR wbr cA cC cR wbr wi cA cB cR
        wbr cB cA wceq cB cC cR wbr cA cC cR wbr cB cA cC cR breq1 biimpd cA cB
        cR wbr cB cC cR wbr cA cC cR wbr cA cB cC cR cS soi.1 soi.2 sotri ex
        jaoi syl6bir com3r mpand com3l 3imp $.

      $( A transitivity relation.  (Read ` A < B ` and ` B <_ C ` implies
         ` A < C ` .)  (Contributed by Mario Carneiro, 10-May-2013.) $)
      sotri3 $p |- ( ( C e. S /\ A R B /\ -. C R B ) -> A R C ) $=
        cC cS wcel cA cB cR wbr cC cB cR wbr wn cA cC cR wbr cA cB cR wbr cC cS
        wcel cC cB cR wbr wn cA cC cR wbr wi cA cB cR wbr cC cS wcel cB cS wcel
        cC cB cR wbr wn cA cC cR wbr wi cA cB cR wbr cA cS wcel cB cS wcel cA
        cB cS cS cR soi.2 brel simprd cC cS wcel cB cS wcel wa cC cB cR wbr wn
        cA cB cR wbr cA cC cR wbr cC cS wcel cB cS wcel wa cC cB cR wbr wn cC
        cB wceq cB cC cR wbr wo cA cB cR wbr cA cC cR wbr wi cC cS wcel cB cS
        wcel wa cC cB cR wbr cC cB wceq cB cC cR wbr wo cS cR wor cC cS wcel cB
        cS wcel wa cC cB cR wbr cC cB wceq cB cC cR wbr wo wn wb soi.1 cS cC cB
        cR sotric mpan con2bid cC cB wceq cA cB cR wbr cA cC cR wbr wi cB cC cR
        wbr cC cB wceq cA cC cR wbr cA cB cR wbr cC cB cA cR breq2 biimprd cA
        cB cR wbr cB cC cR wbr cA cC cR wbr cA cB cC cR cS soi.1 soi.2 sotri
        expcom jaoi syl6bir com3r mpan2d com12 3imp $.
    $}
  $}

  ${
    soiOLD.1 $e |- A e. _V $.
    soiOLD.2 $e |- R Or S $.
    soiOLD.3 $e |- R C_ ( S X. S ) $.
    $( A strict order relation is irreflexive.  (Contributed by NM,
       10-Feb-1996.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    soirriOLD $p |- -. A R A $=
      cA cS wcel cA cS wcel wa cA cA cR wbr wn cA cS wcel cA cA cR wbr wn cA cS
      wcel cS cR wor cA cS wcel cA cA cR wbr wn soiOLD.2 cS cA cR sonr mpan
      adantl cA cA cR wbr cA cS wcel cA cS wcel wa cA cA cS cS cR soiOLD.3 brel
      con3i pm2.61i $.

    ${
      sotriOLD.4 $e |- B e. _V $.
      sotriOLD.5 $e |- C e. _V $.
      $( A strict order relation is a transitive relation.  (Contributed by NM,
         10-Feb-1996.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      sotriOLD $p |- ( ( A R B /\ B R C ) -> A R C ) $=
        cA cS wcel cB cS wcel cC cS wcel w3a cA cB cR wbr cB cC cR wbr wa cA cC
        cR wbr cA cB cR wbr cA cS wcel cB cS wcel wa cB cS wcel cC cS wcel wa
        cA cS wcel cB cS wcel cC cS wcel w3a cB cC cR wbr cA cB cS cS cR
        soiOLD.3 brel cB cC cS cS cR soiOLD.3 brel cA cS wcel cB cS wcel cB cS
        wcel cC cS wcel cA cS wcel cB cS wcel cC cS wcel w3a cA cS wcel cB cS
        wcel cC cS wcel cA cS wcel cB cS wcel cC cS wcel w3a wi cB cS wcel cA
        cS wcel cB cS wcel cC cS wcel cA cS wcel cB cS wcel cC cS wcel w3a cA
        cS wcel cB cS wcel cC cS wcel w3a id 3exp a1dd imp43 syl2an cS cR wor
        cA cS wcel cB cS wcel cC cS wcel w3a cA cB cR wbr cB cC cR wbr wa cA cC
        cR wbr wi soiOLD.2 cS cA cB cC cR sotr mpan mpcom $.
    $}

    ${
      son2lpiOLD.4 $e |- B e. _V $.
      $( A strict order relation has no 2-cycle loops.  (Contributed by NM,
         10-Feb-1996.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      son2lpiOLD $p |- -. ( A R B /\ B R A ) $=
        cA cB cR wbr cB cA cR wbr wa cA cA cR wbr cA cR cS soiOLD.2 soiOLD.3
        soirri cA cB cA cR cS soiOLD.2 soiOLD.3 sotri mto $.
    $}
  $}

  $( Express "less than or equals" for general strict orders.  (Contributed by
     Stefan O'Rear, 17-Jan-2015.) $)
  poleloe $p |- ( B e. V -> ( A ( R u. _I ) B <-> ( A R B \/ A = B ) ) ) $=
    cA cB cR cid cun wbr cA cB cR wbr cA cB cid wbr wo cB cV wcel cA cB cR wbr
    cA cB wceq wo cA cB cR cid brun cB cV wcel cA cB cid wbr cA cB wceq cA cB
    cR wbr cA cB cV ideqg orbi2d syl5bb $.

  $( Transitive law for general strict orders.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
  poltletr $p |- ( ( R Po X /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
      ( ( A R B /\ B ( R u. _I ) C ) -> A R C ) ) $=
    cX cR wpo cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cR wbr cB cC cR cid
    cun wbr wa cA cB cR wbr cB cC cR wbr cB cC wceq wo wa cA cC cR wbr cX cR
    wpo cA cX wcel cB cX wcel cC cX wcel w3a wa cB cC cR cid cun wbr cB cC cR
    wbr cB cC wceq wo cA cB cR wbr cA cX wcel cB cX wcel cC cX wcel w3a cB cC
    cR cid cun wbr cB cC cR wbr cB cC wceq wo wb cX cR wpo cC cX wcel cA cX
    wcel cB cC cR cid cun wbr cB cC cR wbr cB cC wceq wo wb cB cX wcel cB cC cR
    cX poleloe 3ad2ant3 adantl anbi2d cA cB cR wbr cB cC cR wbr cB cC wceq wo
    wa cX cR wpo cA cX wcel cB cX wcel cC cX wcel w3a wa cA cC cR wbr cA cB cR
    wbr cB cC cR wbr cX cR wpo cA cX wcel cB cX wcel cC cX wcel w3a wa cA cC cR
    wbr wi cB cC wceq cX cR wpo cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB
    cR wbr cB cC cR wbr wa cA cC cR wbr cX cA cB cC cR potr com12 cA cB cR wbr
    cB cC wceq wa cA cC cR wbr cX cR wpo cA cX wcel cB cX wcel cC cX wcel w3a
    wa cB cC wceq cA cB cR wbr cA cC cR wbr cB cC cA cR breq2 biimpac a1d
    jaodan com12 sylbid $.

  $( Property of a minimum in a strict order.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
  somin1 $p |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) ->
      if ( A R B , A , B ) ( R u. _I ) A ) $=
    cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr cA cB cif cA cR cid cun
    wbr cA cB cR wbr cA cB cif cA cR wbr cA cB cR wbr cA cB cif cA wceq wo cX
    cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr cA cB cR wbr cA cB cif cA
    cR wbr cA cB cR wbr cA cB cif cA wceq wo cA cB cR wbr cA cB cR wbr cA cB
    cif cA cR wbr cA cB cR wbr cA cB cif cA wceq wo cX cR wor cA cX wcel cB cX
    wcel wa wa cA cB cR wbr cA cB cR wbr cA cB cif cA wceq cA cB cR wbr cA cB
    cif cA cR wbr cA cB cR wbr cA cB iftrue olcd adantl cX cR wor cA cX wcel cB
    cX wcel wa wa cA cB cR wbr wn wa cA cB cR wbr cA cB cif cA cR wbr cA cB cR
    wbr cA cB cif cA wceq wo cB cA cR wbr cB cA wceq wo cX cR wor cA cX wcel cB
    cX wcel wa wa cB cA cR wbr cB cA wceq wo cA cB cR wbr wn cX cR wor cA cX
    wcel cB cX wcel wa wa cA cB cR wbr cB cA cR wbr cB cA wceq wo cX cR wor cA
    cX wcel cB cX wcel wa wa cA cB cR wbr cA cB wceq cB cA cR wbr wo wn cB cA
    cR wbr cB cA wceq wo wn cX cA cB cR sotric cA cB wceq cB cA cR wbr wo cB cA
    cR wbr cB cA wceq wo cA cB wceq cB cA cR wbr wo cB cA cR wbr cA cB wceq wo
    cB cA cR wbr cB cA wceq wo cA cB wceq cB cA cR wbr orcom cA cB wceq cB cA
    wceq cB cA cR wbr cA cB eqcom orbi2i bitri notbii syl6bb con2bid biimpar cA
    cB cR wbr wn cA cB cR wbr cA cB cif cA cR wbr cA cB cR wbr cA cB cif cA
    wceq wo cB cA cR wbr cB cA wceq wo wb cX cR wor cA cX wcel cB cX wcel wa wa
    cA cB cR wbr wn cA cB cR wbr cA cB cif cB wceq cA cB cR wbr cA cB cif cA cR
    wbr cA cB cR wbr cA cB cif cA wceq wo cB cA cR wbr cB cA wceq wo wb cA cB
    cR wbr cA cB iffalse cA cB cR wbr cA cB cif cB wceq cA cB cR wbr cA cB cif
    cA cR wbr cB cA cR wbr cA cB cR wbr cA cB cif cA wceq cB cA wceq cA cB cR
    wbr cA cB cif cB cA cR breq1 cA cB cR wbr cA cB cif cB cA eqeq1 orbi12d syl
    adantl mpbird pm2.61dan cA cX wcel cA cB cR wbr cA cB cif cA cR cid cun wbr
    cA cB cR wbr cA cB cif cA cR wbr cA cB cR wbr cA cB cif cA wceq wo wb cX cR
    wor cB cX wcel cA cB cR wbr cA cB cif cA cR cX poleloe ad2antrl mpbird $.

  $( Commutativity of minimum in a total order.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
  somincom $p |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) ->
      if ( A R B , A , B ) = if ( B R A , B , A ) ) $=
    cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr cA cB cR wbr cA cB cif
    cB cA cR wbr cB cA cif wceq cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR
    wbr wa cA cB cR wbr cA cB cif cA cB cA cR wbr cB cA cif cA cB cR wbr cA cB
    cR wbr cA cB cif cA wceq cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr
    cA cB iftrue adantl cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr wa
    cB cA cR wbr cB cA cif cA cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR
    wbr wa cB cA cR wbr wn cB cA cR wbr cB cA cif cA wceq cX cR wor cA cX wcel
    cB cX wcel wa wa cA cB cR wbr cB cA cR wbr wa wn wi cX cR wor cA cX wcel cB
    cX wcel wa wa cA cB cR wbr wa cB cA cR wbr wn wi cX cA cB cR so2nr cX cR
    wor cA cX wcel cB cX wcel wa wa cA cB cR wbr cB cA cR wbr nan mpbi cB cA cR
    wbr cB cA iffalse syl eqcomd eqtrd cX cR wor cA cX wcel cB cX wcel wa wa cA
    cB cR wbr wn wa cA cB cR wbr cA cB cif cB cB cA cR wbr cB cA cif cA cB cR
    wbr wn cA cB cR wbr cA cB cif cB wceq cX cR wor cA cX wcel cB cX wcel wa wa
    cA cB cR wbr cA cB iffalse adantl cX cR wor cA cX wcel cB cX wcel wa wa cA
    cB cR wbr wn cB cB cA cR wbr cB cA cif wceq cX cR wor cA cX wcel cB cX wcel
    wa wa cA cB cR wbr wn cA cB wceq cB cA cR wbr wo cB cB cA cR wbr cB cA cif
    wceq cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr cA cB wceq cB cA cR
    wbr wo cX cA cB cR sotric con2bid cA cB wceq cB cB cA cR wbr cB cA cif wceq
    cB cA cR wbr cA cB wceq cB cA cR wbr cB cA cif cB cA cR wbr cB cB cif cB cB
    cA cR wbr cA cB cB ifeq2 cB cA cR wbr cB ifid syl6req cB cA cR wbr cB cA cR
    wbr cB cA cif cB cB cA cR wbr cB cA iftrue eqcomd jaoi syl6bir imp eqtrd
    pm2.61dan $.

  $( Property of a minimum in a strict order.  (Contributed by Stefan O'Rear,
     17-Jan-2015.) $)
  somin2 $p |- ( ( R Or X /\ ( A e. X /\ B e. X ) ) ->
      if ( A R B , A , B ) ( R u. _I ) B ) $=
    cX cR wor cA cX wcel cB cX wcel wa wa cA cB cR wbr cA cB cif cB cA cR wbr
    cB cA cif cB cR cid cun cA cB cR cX somincom cX cR wor cB cX wcel cA cX
    wcel cB cA cR wbr cB cA cif cB cR cid cun wbr cB cA cR cX somin1 ancom2s
    eqbrtrd $.

  $( Being less than a minimum, for a general total order.  (Contributed by
     Stefan O'Rear, 17-Jan-2015.) $)
  soltmin $p |- ( ( R Or X /\ ( A e. X /\ B e. X /\ C e. X ) ) ->
      ( A R if ( B R C , B , C ) <-> ( A R B /\ A R C ) ) ) $=
    cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif
    cR wbr cA cB cR wbr cA cC cR wbr wa cX cR wor cA cX wcel cB cX wcel cC cX
    wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr cA cB cR wbr cA cC cR wbr wa
    cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif
    cR wbr wa cA cB cR wbr cA cC cR wbr cX cR wor cA cX wcel cB cX wcel cC cX
    wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr wa cX cR wpo cA cX wcel cB cC
    cR wbr cB cC cif cX wcel cB cX wcel w3a cA cB cC cR wbr cB cC cif cR wbr cB
    cC cR wbr cB cC cif cB cR cid cun wbr cA cB cR wbr cX cR wor cX cR wpo cA
    cX wcel cB cX wcel cC cX wcel w3a cA cB cC cR wbr cB cC cif cR wbr cX cR
    sopo ad2antrr cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR
    wbr cB cC cif cR wbr wa cA cX wcel cB cC cR wbr cB cC cif cX wcel cB cX
    wcel cA cX wcel cB cX wcel cC cX wcel cX cR wor cA cB cC cR wbr cB cC cif
    cR wbr simplr1 cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC
    cR wbr cB cC cif cR wbr wa cB cX wcel cC cX wcel cB cC cR wbr cB cC cif cX
    wcel cA cX wcel cB cX wcel cC cX wcel cX cR wor cA cB cC cR wbr cB cC cif
    cR wbr simplr2 cA cX wcel cB cX wcel cC cX wcel cX cR wor cA cB cC cR wbr
    cB cC cif cR wbr simplr3 cB cC cR wbr cB cC cX ifcl syl2anc cA cX wcel cB
    cX wcel cC cX wcel cX cR wor cA cB cC cR wbr cB cC cif cR wbr simplr2 3jca
    cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif
    cR wbr simpr cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR
    wbr cB cC cif cR wbr wa cX cR wor cB cX wcel cC cX wcel cB cC cR wbr cB cC
    cif cB cR cid cun wbr cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a cA cB
    cC cR wbr cB cC cif cR wbr simpll cA cX wcel cB cX wcel cC cX wcel cX cR
    wor cA cB cC cR wbr cB cC cif cR wbr simplr2 cA cX wcel cB cX wcel cC cX
    wcel cX cR wor cA cB cC cR wbr cB cC cif cR wbr simplr3 cB cC cR cX somin1
    syl12anc cX cR wpo cA cX wcel cB cC cR wbr cB cC cif cX wcel cB cX wcel w3a
    wa cA cB cC cR wbr cB cC cif cR wbr cB cC cR wbr cB cC cif cB cR cid cun
    wbr wa cA cB cR wbr cA cB cC cR wbr cB cC cif cB cR cX poltletr imp
    syl22anc cX cR wor cA cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr
    cB cC cif cR wbr wa cX cR wpo cA cX wcel cB cC cR wbr cB cC cif cX wcel cC
    cX wcel w3a cA cB cC cR wbr cB cC cif cR wbr cB cC cR wbr cB cC cif cC cR
    cid cun wbr cA cC cR wbr cX cR wor cX cR wpo cA cX wcel cB cX wcel cC cX
    wcel w3a cA cB cC cR wbr cB cC cif cR wbr cX cR sopo ad2antrr cX cR wor cA
    cX wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr wa cA
    cX wcel cB cC cR wbr cB cC cif cX wcel cC cX wcel cA cX wcel cB cX wcel cC
    cX wcel cX cR wor cA cB cC cR wbr cB cC cif cR wbr simplr1 cX cR wor cA cX
    wcel cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr wa cB cX
    wcel cC cX wcel cB cC cR wbr cB cC cif cX wcel cA cX wcel cB cX wcel cC cX
    wcel cX cR wor cA cB cC cR wbr cB cC cif cR wbr simplr2 cA cX wcel cB cX
    wcel cC cX wcel cX cR wor cA cB cC cR wbr cB cC cif cR wbr simplr3 cB cC cR
    wbr cB cC cX ifcl syl2anc cA cX wcel cB cX wcel cC cX wcel cX cR wor cA cB
    cC cR wbr cB cC cif cR wbr simplr3 3jca cX cR wor cA cX wcel cB cX wcel cC
    cX wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr simpr cX cR wor cA cX wcel
    cB cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr wa cX cR wor
    cB cX wcel cC cX wcel cB cC cR wbr cB cC cif cC cR cid cun wbr cX cR wor cA
    cX wcel cB cX wcel cC cX wcel w3a cA cB cC cR wbr cB cC cif cR wbr simpll
    cA cX wcel cB cX wcel cC cX wcel cX cR wor cA cB cC cR wbr cB cC cif cR wbr
    simplr2 cA cX wcel cB cX wcel cC cX wcel cX cR wor cA cB cC cR wbr cB cC
    cif cR wbr simplr3 cB cC cR cX somin2 syl12anc cX cR wpo cA cX wcel cB cC
    cR wbr cB cC cif cX wcel cC cX wcel w3a wa cA cB cC cR wbr cB cC cif cR wbr
    cB cC cR wbr cB cC cif cC cR cid cun wbr wa cA cC cR wbr cA cB cC cR wbr cB
    cC cif cC cR cX poltletr imp syl22anc jca ex cB cC cR wbr cA cB cR wbr cA
    cC cR wbr cA cB cC cR wbr cB cC cif cR wbr cB cC cB cB cC cR wbr cB cC cif
    cA cR breq2 cC cB cC cR wbr cB cC cif cA cR breq2 ifboth impbid1 $.

  ${
    $d x y z w $.  $d z w ph $.
    $( The converse of a class abstraction of ordered pairs.  (Contributed by
       NM, 11-Dec-2003.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    cnvopab $p |- `' { <. x , y >. | ph } = { <. y , x >. | ph } $=
      vz vw wph vx vy copab ccnv wph vy vx copab wph vx vy copab relcnv wph vy
      vx relopab vw cv vz cv cop wph vx vy copab wcel wph vy vz wsb vx vw wsb
      vz cv vw cv cop wph vx vy copab ccnv wcel vz cv vw cv cop wph vy vx copab
      wcel vw cv vz cv cop wph vx vy copab wcel wph vx vw wsb vy vz wsb wph vy
      vz wsb vx vw wsb wph vx vy vw vz opelopabsbOLD wph vx vw vy vz sbcom2
      bitri vz cv vw cv wph vx vy copab vz vex vw vex opelcnv wph vy vx vz vw
      opelopabsbOLD 3bitr4i eqrelriiv $.
  $}

  ${
    $d x y $.
    $( The converse of the empty set.  (Contributed by NM, 6-Apr-1998.) $)
    cnv0 $p |- `' (/) = (/) $=
      vx vy c0 ccnv c0 c0 relcnv rel0 vx cv vy cv cop c0 ccnv wcel vy cv vx cv
      cop c0 wcel vx cv vy cv cop c0 wcel vx cv vy cv c0 vx vex vy vex opelcnv
      vx cv vy cv cop c0 wcel vy cv vx cv cop c0 wcel vx cv vy cv cop noel vy
      cv vx cv cop noel 2false bitr4i eqrelriiv $.

    $( The converse of the identity relation.  Theorem 3.7(ii) of [Monk1]
       p. 36.  (Contributed by NM, 26-Apr-1998.)  (Proof shortened by Andrew
       Salmon, 27-Aug-2011.) $)
    cnvi $p |- `' _I = _I $=
      vy cv vx cv cid wbr vx vy copab vx cv vy cv wceq vx vy copab cid ccnv cid
      vy cv vx cv cid wbr vx cv vy cv wceq vx vy vy cv vx cv cid wbr vy cv vx
      cv wceq vx cv vy cv wceq vy cv vx cv vx vex ideq vy vx equcom bitri
      opabbii vx vy cid df-cnv vx vy df-id 3eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The converse of a union is the union of converses.  Theorem 16 of
       [Suppes] p. 62.  (Contributed by NM, 25-Mar-1998.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
    cnvun $p |- `' ( A u. B ) = ( `' A u. `' B ) $=
      cA cB cun ccnv vy cv vx cv cA wbr vx vy copab vy cv vx cv cB wbr vx vy
      copab cun cA ccnv cB ccnv cun cA cB cun ccnv vy cv vx cv cA cB cun wbr vx
      vy copab vy cv vx cv cA wbr vx vy copab vy cv vx cv cB wbr vx vy copab
      cun vx vy cA cB cun df-cnv vy cv vx cv cA wbr vx vy copab vy cv vx cv cB
      wbr vx vy copab cun vy cv vx cv cA wbr vy cv vx cv cB wbr wo vx vy copab
      vy cv vx cv cA cB cun wbr vx vy copab vy cv vx cv cA wbr vy cv vx cv cB
      wbr vx vy unopab vy cv vx cv cA cB cun wbr vy cv vx cv cA wbr vy cv vx cv
      cB wbr wo vx vy vy cv vx cv cA cB brun opabbii eqtr4i eqtr4i cA ccnv vy
      cv vx cv cA wbr vx vy copab cB ccnv vy cv vx cv cB wbr vx vy copab vx vy
      cA df-cnv vx vy cB df-cnv uneq12i eqtr4i $.

    $( Distributive law for converse over set difference.  (Contributed by
       Mario Carneiro, 26-Jun-2014.) $)
    cnvdif $p |- `' ( A \ B ) = ( `' A \ `' B ) $=
      vx vy cA cB cdif ccnv cA ccnv cB ccnv cdif cA cB cdif relcnv cA ccnv cB
      ccnv cdif cA ccnv wss cA ccnv wrel cA ccnv cB ccnv cdif wrel cA ccnv cB
      ccnv difss cA relcnv cA ccnv cB ccnv cdif cA ccnv relss mp2 vy cv vx cv
      cop cA cB cdif wcel vy cv vx cv cop cA wcel vy cv vx cv cop cB wcel wn wa
      vx cv vy cv cop cA cB cdif ccnv wcel vx cv vy cv cop cA ccnv cB ccnv cdif
      wcel vy cv vx cv cop cA cB eldif vx cv vy cv cA cB cdif vx vex vy vex
      opelcnv vx cv vy cv cop cA ccnv cB ccnv cdif wcel vx cv vy cv cop cA ccnv
      wcel vx cv vy cv cop cB ccnv wcel wn wa vy cv vx cv cop cA wcel vy cv vx
      cv cop cB wcel wn wa vx cv vy cv cop cA ccnv cB ccnv eldif vx cv vy cv
      cop cA ccnv wcel vy cv vx cv cop cA wcel vx cv vy cv cop cB ccnv wcel wn
      vy cv vx cv cop cB wcel wn vx cv vy cv cA vx vex vy vex opelcnv vx cv vy
      cv cop cB ccnv wcel vy cv vx cv cop cB wcel vx cv vy cv cB vx vex vy vex
      opelcnv notbii anbi12i bitri 3bitr4i eqrelriiv $.

    $( Distributive law for converse over intersection.  Theorem 15 of [Suppes]
       p. 62.  (Contributed by NM, 25-Mar-1998.)  (Revised by Mario Carneiro,
       26-Jun-2014.) $)
    cnvin $p |- `' ( A i^i B ) = ( `' A i^i `' B ) $=
      cA cA cB cdif cdif ccnv cA ccnv cA ccnv cB ccnv cdif cdif cA cB cin ccnv
      cA ccnv cB ccnv cin cA cA cB cdif cdif ccnv cA ccnv cA cB cdif ccnv cdif
      cA ccnv cA ccnv cB ccnv cdif cdif cA cA cB cdif cnvdif cA cB cdif ccnv cA
      ccnv cB ccnv cdif cA ccnv cA cB cnvdif difeq2i eqtri cA cB cin cA cA cB
      cdif cdif cA cB dfin4 cnveqi cA ccnv cB ccnv dfin4 3eqtr4i $.
  $}

  $( Distributive law for range over union.  Theorem 8 of [Suppes] p. 60.
     (Contributed by NM, 24-Mar-1998.) $)
  rnun $p |- ran ( A u. B ) = ( ran A u. ran B ) $=
    cA cB cun ccnv cdm cA ccnv cdm cB ccnv cdm cun cA cB cun crn cA crn cB crn
    cun cA cB cun ccnv cdm cA ccnv cB ccnv cun cdm cA ccnv cdm cB ccnv cdm cun
    cA cB cun ccnv cA ccnv cB ccnv cun cA cB cnvun dmeqi cA ccnv cB ccnv dmun
    eqtri cA cB cun df-rn cA crn cA ccnv cdm cB crn cB ccnv cdm cA df-rn cB
    df-rn uneq12i 3eqtr4i $.

  $( The range of an intersection belongs the intersection of ranges.  Theorem
     9 of [Suppes] p. 60.  (Contributed by NM, 15-Sep-2004.) $)
  rnin $p |- ran ( A i^i B ) C_ ( ran A i^i ran B ) $=
    cA cB cin ccnv cdm cA ccnv cdm cB ccnv cdm cin cA cB cin crn cA crn cB crn
    cin cA cB cin ccnv cdm cA ccnv cB ccnv cin cdm cA ccnv cdm cB ccnv cdm cin
    cA cB cin ccnv cA ccnv cB ccnv cin cA cB cnvin dmeqi cA ccnv cB ccnv dmin
    eqsstri cA cB cin df-rn cA crn cA ccnv cdm cB crn cB ccnv cdm cA df-rn cB
    df-rn ineq12i 3sstr4i $.

  ${
    $d x y z $.  $d y z A $.  $d y z B $.
    $( The range of an indexed union.  (Contributed by Mario Carneiro,
       29-May-2015.) $)
    rniun $p |- ran U_ x e. A B = U_ x e. A ran B $=
      vz vx cA cB ciun crn vx cA cB crn ciun vy cv vz cv cop vx cA cB ciun wcel
      vy wex vz cv cB crn wcel vx cA wrex vz cv vx cA cB ciun crn wcel vz cv vx
      cA cB crn ciun wcel vy cv vz cv cop cB wcel vy wex vx cA wrex vy cv vz cv
      cop cB wcel vx cA wrex vy wex vz cv cB crn wcel vx cA wrex vy cv vz cv
      cop vx cA cB ciun wcel vy wex vy cv vz cv cop cB wcel vx vy cA rexcom4 vz
      cv cB crn wcel vy cv vz cv cop cB wcel vy wex vx cA vy vz cv cB vz vex
      elrn2 rexbii vy cv vz cv cop vx cA cB ciun wcel vy cv vz cv cop cB wcel
      vx cA wrex vy vx vy cv vz cv cop cA cB eliun exbii 3bitr4ri vy vz cv vx
      cA cB ciun vz vex elrn2 vx vz cv cA cB crn eliun 3bitr4i eqriv $.

    $d x A $.
    $( The range of a union.  Part of Exercise 8 of [Enderton] p. 41.
       (Contributed by NM, 17-Mar-2004.)  (Revised by Mario Carneiro,
       29-May-2015.) $)
    rnuni $p |- ran U. A = U_ x e. A ran x $=
      cA cuni crn vx cA vx cv ciun crn vx cA vx cv crn ciun cA cuni vx cA vx cv
      ciun vx cA uniiun rneqi vx cA vx cv rniun eqtri $.
  $}

  $( Distributive law for image over union.  Theorem 35 of [Suppes] p. 65.
     (Contributed by NM, 30-Sep-2002.) $)
  imaundi $p |- ( A " ( B u. C ) ) = ( ( A " B ) u. ( A " C ) ) $=
    cA cB cC cun cres crn cA cB cres crn cA cC cres crn cun cA cB cC cun cima
    cA cB cima cA cC cima cun cA cB cC cun cres crn cA cB cres cA cC cres cun
    crn cA cB cres crn cA cC cres crn cun cA cB cC cun cres cA cB cres cA cC
    cres cun cA cB cC resundi rneqi cA cB cres cA cC cres rnun eqtri cA cB cC
    cun df-ima cA cB cima cA cB cres crn cA cC cima cA cC cres crn cA cB df-ima
    cA cC df-ima uneq12i 3eqtr4i $.

  $( The image of a union.  (Contributed by Jeff Hoffman, 17-Feb-2008.) $)
  imaundir $p |- ( ( A u. B ) " C ) = ( ( A " C ) u. ( B " C ) ) $=
    cA cB cun cC cima cA cC cres crn cB cC cres crn cun cA cC cima cB cC cima
    cun cA cB cun cC cima cA cB cun cC cres crn cA cC cres cB cC cres cun crn
    cA cC cres crn cB cC cres crn cun cA cB cun cC df-ima cA cB cun cC cres cA
    cC cres cB cC cres cun cA cB cC resundir rneqi cA cC cres cB cC cres rnun
    3eqtri cA cC cima cA cC cres crn cB cC cima cB cC cres crn cA cC df-ima cB
    cC df-ima uneq12i eqtr4i $.

  ${
    $d x y A $.  $d x y B $.  $d x y R $.
    $( An upper bound for intersection with a domain.  Theorem 40 of [Suppes]
       p. 66, who calls it "somewhat surprising."  (Contributed by NM,
       11-Aug-2004.) $)
    dminss $p |- ( dom R i^i A ) C_ ( `' R " ( R " A ) ) $=
      vx cR cdm cA cin cR ccnv cR cA cima cima vx cv vy cv cR wbr vx cv cA wcel
      wa vy wex vy cv cR cA cima wcel vy cv vx cv cR ccnv wbr wa vy wex vx cv
      cR cdm cA cin wcel vx cv cR ccnv cR cA cima cima wcel vx cv vy cv cR wbr
      vx cv cA wcel wa vy cv cR cA cima wcel vy cv vx cv cR ccnv wbr wa vy vx
      cv vy cv cR wbr vx cv cA wcel wa vy cv cR cA cima wcel vy cv vx cv cR
      ccnv wbr vx cv vy cv cR wbr vx cv cA wcel wa vx cv cA wcel vx cv vy cv cR
      wbr wa vx wex vy cv cR cA cima wcel vx cv cA wcel vx cv vy cv cR wbr vx
      cv cA wcel vx cv vy cv cR wbr wa vx wex vx cv cA wcel vx cv vy cv cR wbr
      wa vx 19.8a ancoms vx vy cv cR cA vy vex elima2 sylibr vx cv vy cv cR wbr
      vx cv cA wcel wa vx cv vy cv cR wbr vy cv vx cv cR ccnv wbr vx cv vy cv
      cR wbr vx cv cA wcel simpl vy cv vx cv cR vy vex vx vex brcnv sylibr jca
      eximi vx cv cR cdm wcel vx cv cA wcel wa vx cv vy cv cR wbr vy wex vx cv
      cA wcel wa vx cv cR cdm cA cin wcel vx cv vy cv cR wbr vx cv cA wcel wa
      vy wex vx cv cR cdm wcel vx cv vy cv cR wbr vy wex vx cv cA wcel vy vx cv
      cR vx vex eldm anbi1i vx cv cR cdm cA elin vx cv vy cv cR wbr vx cv cA
      wcel vy 19.41v 3bitr4i vy vx cv cR ccnv cR cA cima vx vex elima2 3imtr4i
      ssriv $.

    $( An upper bound for intersection with an image.  Theorem 41 of [Suppes]
       p. 66.  (Contributed by NM, 11-Aug-2004.) $)
    imainss $p |- ( ( R " A ) i^i B ) C_ ( R " ( A i^i ( `' R " B ) ) ) $=
      vy cR cA cima cB cin cR cA cR ccnv cB cima cin cima vx cv cA wcel vx cv
      vy cv cR wbr wa vy cv cB wcel wa vx wex vx cv cA cR ccnv cB cima cin wcel
      vx cv vy cv cR wbr wa vx wex vy cv cR cA cima cB cin wcel vy cv cR cA cR
      ccnv cB cima cin cima wcel vx cv cA wcel vx cv vy cv cR wbr wa vy cv cB
      wcel wa vx cv cA cR ccnv cB cima cin wcel vx cv vy cv cR wbr wa vx vx cv
      cA wcel vx cv vy cv cR wbr wa vy cv cB wcel wa vx cv cA wcel vy cv cB
      wcel vy cv vx cv cR ccnv wbr wa vy wex wa vx cv vy cv cR wbr wa vx cv cA
      cR ccnv cB cima cin wcel vx cv vy cv cR wbr wa vx cv cA wcel vx cv vy cv
      cR wbr vy cv cB wcel vx cv cA wcel vy cv cB wcel vy cv vx cv cR ccnv wbr
      wa vy wex wa vx cv vy cv cR wbr wa vx cv cA wcel vx cv vy cv cR wbr vy cv
      cB wcel wa wa vx cv cA wcel vy cv cB wcel vy cv vx cv cR ccnv wbr wa vy
      wex wa vx cv vy cv cR wbr vx cv vy cv cR wbr vy cv cB wcel wa vy cv cB
      wcel vy cv vx cv cR ccnv wbr wa vy wex vx cv cA wcel vy cv cB wcel vx cv
      vy cv cR wbr vy cv cB wcel vy cv vx cv cR ccnv wbr wa vy wex vx cv vy cv
      cR wbr vy cv cB wcel vy cv vx cv cR ccnv wbr vy cv cB wcel vy cv vx cv cR
      ccnv wbr wa vy wex vy cv vx cv cR vy vex vx vex brcnv vy cv cB wcel vy cv
      vx cv cR ccnv wbr wa vy 19.8a sylan2br ancoms anim2i vx cv cA wcel vx cv
      vy cv cR wbr vy cv cB wcel simprl jca anassrs vx cv cA cR ccnv cB cima
      cin wcel vx cv cA wcel vy cv cB wcel vy cv vx cv cR ccnv wbr wa vy wex wa
      vx cv vy cv cR wbr vx cv cA cR ccnv cB cima cin wcel vx cv cA wcel vx cv
      cR ccnv cB cima wcel wa vx cv cA wcel vy cv cB wcel vy cv vx cv cR ccnv
      wbr wa vy wex wa vx cv cA cR ccnv cB cima elin vx cv cR ccnv cB cima wcel
      vy cv cB wcel vy cv vx cv cR ccnv wbr wa vy wex vx cv cA wcel vy vx cv cR
      ccnv cB vx vex elima2 anbi2i bitri anbi1i sylibr eximi vy cv cR cA cima
      wcel vy cv cB wcel wa vx cv cA wcel vx cv vy cv cR wbr wa vx wex vy cv cB
      wcel wa vy cv cR cA cima cB cin wcel vx cv cA wcel vx cv vy cv cR wbr wa
      vy cv cB wcel wa vx wex vy cv cR cA cima wcel vx cv cA wcel vx cv vy cv
      cR wbr wa vx wex vy cv cB wcel vx vy cv cR cA vy vex elima2 anbi1i vy cv
      cR cA cima cB elin vx cv cA wcel vx cv vy cv cR wbr wa vy cv cB wcel vx
      19.41v 3bitr4i vx vy cv cR cA cR ccnv cB cima cin vy vex elima2 3imtr4i
      ssriv $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( The converse of a cross product.  Exercise 11 of [Suppes] p. 67.
       (Contributed by NM, 14-Aug-1999.)  (Proof shortened by Andrew Salmon,
       27-Aug-2011.) $)
    cnvxp $p |- `' ( A X. B ) = ( B X. A ) $=
      vy cv cA wcel vx cv cB wcel wa vy vx copab ccnv vx cv cB wcel vy cv cA
      wcel wa vx vy copab cA cB cxp ccnv cB cA cxp vy cv cA wcel vx cv cB wcel
      wa vy vx copab ccnv vy cv cA wcel vx cv cB wcel wa vx vy copab vx cv cB
      wcel vy cv cA wcel wa vx vy copab vy cv cA wcel vx cv cB wcel wa vy vx
      cnvopab vy cv cA wcel vx cv cB wcel wa vx cv cB wcel vy cv cA wcel wa vx
      vy vy cv cA wcel vx cv cB wcel ancom opabbii eqtri cA cB cxp vy cv cA
      wcel vx cv cB wcel wa vy vx copab vy vx cA cB df-xp cnveqi vx vy cB cA
      df-xp 3eqtr4i $.
  $}

  $( The cross product with the empty set is empty.  Part of Theorem 3.13(ii)
     of [Monk1] p. 37.  (Contributed by NM, 12-Apr-2004.) $)
  xp0 $p |- ( A X. (/) ) = (/) $=
    c0 cA cxp ccnv c0 ccnv cA c0 cxp c0 c0 cA cxp c0 cA xp0r cnveqi c0 cA cnvxp
    cnv0 3eqtr3i $.

  ${
    $d x y z A $.  $d x y z B $.
    $( The cross product of nonempty classes is nonempty.  (Variation of a
       theorem contributed by Raph Levien, 30-Jun-2006.)  (Contributed by NM,
       30-Jun-2006.) $)
    xpnz $p |- ( ( A =/= (/) /\ B =/= (/) ) <-> ( A X. B ) =/= (/) ) $=
      cA c0 wne cB c0 wne wa cA cB cxp c0 wne cA c0 wne cB c0 wne wa vx cv cA
      wcel vy cv cB wcel wa vy wex vx wex cA cB cxp c0 wne cA c0 wne cB c0 wne
      wa vx cv cA wcel vx wex vy cv cB wcel vy wex wa vx cv cA wcel vy cv cB
      wcel wa vy wex vx wex cA c0 wne vx cv cA wcel vx wex cB c0 wne vy cv cB
      wcel vy wex vx cA n0 vy cB n0 anbi12i vx cv cA wcel vy cv cB wcel vx vy
      eeanv bitr4i vx cv cA wcel vy cv cB wcel wa cA cB cxp c0 wne vx vy vx cv
      cA wcel vy cv cB wcel wa vz cv cA cB cxp wcel vz wex cA cB cxp c0 wne vz
      cv cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa vz vx cv vy cv cop vx cv
      vy cv opex vz cv vx cv vy cv cop wceq vz cv cA cB cxp wcel vx cv vy cv
      cop cA cB cxp wcel vx cv cA wcel vy cv cB wcel wa vz cv vx cv vy cv cop
      cA cB cxp eleq1 vx cv vy cv cA cB opelxp syl6bb spcev vz cA cB cxp n0
      sylibr exlimivv sylbi cA cB cxp c0 wne cA c0 wne cB c0 wne cA c0 cA cB
      cxp c0 cA c0 wceq cA cB cxp c0 cB cxp c0 cA c0 cB xpeq1 cB xp0r syl6eq
      necon3i cB c0 cA cB cxp c0 cB c0 wceq cA cB cxp cA c0 cxp c0 cB c0 cA
      xpeq2 cA xp0 syl6eq necon3i jca impbii $.
  $}

  $( At least one member of an empty cross product is empty.  (Contributed by
     NM, 27-Aug-2006.) $)
  xpeq0 $p |- ( ( A X. B ) = (/) <-> ( A = (/) \/ B = (/) ) ) $=
    cA cB cxp c0 wceq cA c0 wne cB c0 wne wa wn cA c0 wne wn cB c0 wne wn wo cA
    c0 wceq cB c0 wceq wo cA c0 wne cB c0 wne wa cA cB cxp c0 cA cB xpnz
    necon2bbii cA c0 wne cB c0 wne ianor cA c0 wne wn cA c0 wceq cB c0 wne wn
    cB c0 wceq cA c0 nne cB c0 nne orbi12i 3bitri $.

  $( Cross products with disjoint sets are disjoint.  (Contributed by NM,
     13-Sep-2004.) $)
  xpdisj1 $p |- ( ( A i^i B ) = (/) -> ( ( A X. C ) i^i ( B X. D ) ) = (/) ) $=
    cA cB cin c0 wceq cA cC cxp cB cD cxp cin cA cB cin cC cD cin cxp c0 cA cC
    cB cD inxp cA cB cin c0 wceq cA cB cin cC cD cin cxp c0 cC cD cin cxp c0 cA
    cB cin c0 cC cD cin xpeq1 cC cD cin xp0r syl6eq syl5eq $.

  $( Cross products with disjoint sets are disjoint.  (Contributed by NM,
     13-Sep-2004.) $)
  xpdisj2 $p |- ( ( A i^i B ) = (/) -> ( ( C X. A ) i^i ( D X. B ) ) = (/) ) $=
    cA cB cin c0 wceq cC cA cxp cD cB cxp cin cC cD cin cA cB cin cxp c0 cC cA
    cD cB inxp cA cB cin c0 wceq cC cD cin cA cB cin cxp cC cD cin c0 cxp c0 cA
    cB cin c0 cC cD cin xpeq2 cC cD cin xp0 syl6eq syl5eq $.

  $( Cross products with two different singletons are disjoint.  (Contributed
     by NM, 28-Jul-2004.) $)
  xpsndisj $p |- ( B =/= D -> ( ( A X. { B } ) i^i ( C X. { D } ) ) = (/) ) $=
    cB cD wne cB csn cD csn cin c0 wceq cA cB csn cxp cC cD csn cxp cin c0 wceq
    cB cD disjsn2 cB csn cD csn cA cC xpdisj2 syl $.

  ${
    $d x A $.  $d y B $.
    $( Disjoint unions with disjoint index sets are disjoint.  (Contributed by
       Stefan O'Rear, 21-Nov-2014.) $)
    djudisj $p |- ( ( A i^i B ) = (/) -> ( U_ x e. A ( { x } X. C ) i^i
            U_ y e. B ( { y } X. D ) ) = (/) ) $=
      cA cB cin c0 wceq vx cA vx cv csn cC cxp ciun cA cvv cxp wss cA cvv cxp
      vy cB vy cv csn cD cxp ciun cin c0 wceq vx cA vx cv csn cC cxp ciun vy cB
      vy cv csn cD cxp ciun cin c0 wceq vx cA cC djussxp cA cB cin c0 wceq cA
      cvv cxp vy cB vy cv csn cD cxp ciun cin vy cB vy cv csn cD cxp ciun cA
      cvv cxp cin c0 cA cvv cxp vy cB vy cv csn cD cxp ciun incom cA cB cin c0
      wceq vy cB vy cv csn cD cxp ciun cB cvv cxp wss cB cvv cxp cA cvv cxp cin
      c0 wceq vy cB vy cv csn cD cxp ciun cA cvv cxp cin c0 wceq vy cB cD
      djussxp cA cB cin c0 wceq cB cvv cxp cA cvv cxp cin cA cvv cxp cB cvv cxp
      cin c0 cB cvv cxp cA cvv cxp incom cA cB cvv cvv xpdisj1 syl5eq vy cB vy
      cv csn cD cxp ciun cB cvv cxp cA cvv cxp ssdisj sylancr syl5eq vx cA vx
      cv csn cC cxp ciun cA cvv cxp vy cB vy cv csn cD cxp ciun ssdisj sylancr
      $.
  $}

  $( A double restriction to disjoint classes is the empty set.  (Contributed
     by NM, 7-Oct-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  resdisj $p |- ( ( A i^i B ) = (/) -> ( ( C |` A ) |` B ) = (/) ) $=
    cA cB cin c0 wceq cC cA cres cB cres cC cA cB cin cres c0 cC cA cB resres
    cA cB cin c0 wceq cC cA cB cin cres cC c0 cres c0 cA cB cin c0 cC reseq2 cC
    res0 syl6eq syl5eq $.

  $( The range of a cross product.  Part of Theorem 3.13(x) of [Monk1] p. 37.
     (Contributed by NM, 12-Apr-2004.) $)
  rnxp $p |- ( A =/= (/) -> ran ( A X. B ) = B ) $=
    cA c0 wne cA cB cxp crn cB cA cxp cdm cB cA cB cxp crn cA cB cxp ccnv cdm
    cB cA cxp cdm cA cB cxp df-rn cA cB cxp ccnv cB cA cxp cA cB cnvxp dmeqi
    eqtri cB cA dmxp syl5eq $.

  $( The domain of a cross product is a subclass of the first factor.
     (Contributed by NM, 19-Mar-2007.) $)
  dmxpss $p |- dom ( A X. B ) C_ A $=
    cA cB cxp cdm cA wss cB c0 cB c0 wceq cA cB cxp cdm cA wss c0 cA wss cA 0ss
    cB c0 wceq cA cB cxp cdm c0 cA cB c0 wceq cA cB cxp cdm c0 cdm c0 cB c0
    wceq cA cB cxp c0 cB c0 wceq cA cB cxp cA c0 cxp c0 cB c0 cA xpeq2 cA xp0
    syl6eq dmeqd dm0 syl6eq sseq1d mpbiri cB c0 wne cA cB cxp cdm cA wceq cA cB
    cxp cdm cA wss cA cB dmxp cA cB cxp cdm cA eqimss syl pm2.61ine $.

  $( The range of a cross product is a subclass of the second factor.
     (Contributed by NM, 16-Jan-2006.)  (Proof shortened by Andrew Salmon,
     27-Aug-2011.) $)
  rnxpss $p |- ran ( A X. B ) C_ B $=
    cA cB cxp crn cA cB cxp ccnv cdm cB cA cB cxp df-rn cA cB cxp ccnv cdm cB
    cA cxp cdm cB cA cB cxp ccnv cB cA cxp cA cB cnvxp dmeqi cB cA dmxpss
    eqsstri eqsstri $.

  $( The range of a square cross product.  (Contributed by FL, 17-May-2010.) $)
  rnxpid $p |- ran ( A X. A ) = A $=
    cA cA cxp crn cA wceq cA c0 cA c0 wceq c0 crn c0 cA cA cxp crn cA rn0 cA c0
    wceq cA cA cxp c0 cA c0 wceq cA cA cxp cA c0 cxp c0 cA c0 cA xpeq2 cA xp0
    syl6eq rneqd cA c0 wceq id 3eqtr4a cA cA rnxp pm2.61ine $.

  $( A cross-product subclass relationship is equivalent to the relationship
     for it components.  (Contributed by NM, 17-Dec-2008.) $)
  ssxpb $p |- ( ( A X. B ) =/= (/) -> ( ( A X. B ) C_ ( C X. D ) <->
              ( A C_ C /\ B C_ D ) ) ) $=
    cA cB cxp c0 wne cA cB cxp cC cD cxp wss cA cC wss cB cD wss wa cA cB cxp
    c0 wne cA cB cxp cC cD cxp wss cA cC wss cB cD wss wa cA cB cxp c0 wne cA
    cB cxp cC cD cxp wss wa cA cC wss cB cD wss cA cB cxp c0 wne cA cB cxp cC
    cD cxp wss wa cA cC cD cxp cdm cC cA cB cxp c0 wne cA cB cxp cC cD cxp wss
    wa cA cA cB cxp cdm cC cD cxp cdm cA cB cxp c0 wne cA cB cxp cdm cA wceq cA
    cB cxp cC cD cxp wss cA cB cxp c0 wne cA c0 wne cB c0 wne wa cA cB cxp cdm
    cA wceq cA cB xpnz cB c0 wne cA cB cxp cdm cA wceq cA c0 wne cA cB dmxp
    adantl sylbir adantr cA cB cxp cC cD cxp wss cA cB cxp cdm cC cD cxp cdm
    wss cA cB cxp c0 wne cA cB cxp cC cD cxp dmss adantl eqsstr3d cC cD dmxpss
    syl6ss cA cB cxp c0 wne cA cB cxp cC cD cxp wss wa cB cC cD cxp crn cD cA
    cB cxp c0 wne cA cB cxp cC cD cxp wss wa cB cA cB cxp crn cC cD cxp crn cA
    cB cxp c0 wne cA cB cxp crn cB wceq cA cB cxp cC cD cxp wss cA cB cxp c0
    wne cA c0 wne cB c0 wne wa cA cB cxp crn cB wceq cA cB xpnz cA c0 wne cA cB
    cxp crn cB wceq cB c0 wne cA cB rnxp adantr sylbir adantr cA cB cxp cC cD
    cxp wss cA cB cxp crn cC cD cxp crn wss cA cB cxp c0 wne cA cB cxp cC cD
    cxp rnss adantl eqsstr3d cC cD rnxpss syl6ss jca ex cA cC cB cD xpss12
    impbid1 $.

  $( The cross product of non-empty classes is one-to-one.  (Contributed by NM,
     31-May-2008.) $)
  xp11 $p |- ( ( A =/= (/) /\ B =/= (/) )
      -> ( ( A X. B ) = ( C X. D ) <-> ( A = C /\ B = D ) ) ) $=
    cA c0 wne cB c0 wne wa cA cB cxp cC cD cxp wceq cA cC wceq cB cD wceq wa cA
    c0 wne cB c0 wne wa cA cB cxp c0 wne cA cB cxp cC cD cxp wceq cA cC wceq cB
    cD wceq wa wi cA cB xpnz cA cB cxp cC cD cxp wceq cA cB cxp c0 wne cA cC
    wceq cB cD wceq wa cA cB cxp cC cD cxp wceq cA cB cxp c0 wne cA cB cxp c0
    wne cC cD cxp c0 wne wa cA cC wceq cB cD wceq wa cA cB cxp c0 wne cA cB cxp
    c0 wne cA cB cxp c0 wne wa cA cB cxp cC cD cxp wceq cA cB cxp c0 wne cC cD
    cxp c0 wne wa cA cB cxp c0 wne anidm cA cB cxp cC cD cxp wceq cA cB cxp c0
    wne cC cD cxp c0 wne cA cB cxp c0 wne cA cB cxp cC cD cxp c0 neeq1 anbi2d
    syl5bbr cA cB cxp cC cD cxp wceq cA cB cxp c0 wne cC cD cxp c0 wne wa cA cC
    wss cB cD wss wa cC cA wss cD cB wss wa wa cA cC wceq cB cD wceq wa cA cB
    cxp cC cD cxp wceq cA cB cxp c0 wne cA cC wss cB cD wss wa cC cD cxp c0 wne
    cC cA wss cD cB wss wa cA cB cxp cC cD cxp wceq cA cB cxp cC cD cxp wss cA
    cB cxp c0 wne cA cC wss cB cD wss wa cA cB cxp cC cD cxp eqimss cA cB cC cD
    ssxpb syl5ibcom cA cB cxp cC cD cxp wceq cC cD cxp cA cB cxp wss cC cD cxp
    c0 wne cC cA wss cD cB wss wa cC cD cxp cA cB cxp eqimss2 cC cD cA cB ssxpb
    syl5ibcom anim12d cA cC wss cB cD wss wa cC cA wss cD cB wss wa wa cA cC
    wss cC cA wss wa cB cD wss cD cB wss wa wa cA cC wceq cB cD wceq wa cA cC
    wss cB cD wss cC cA wss cD cB wss an4 cA cC wceq cA cC wss cC cA wss wa cB
    cD wceq cB cD wss cD cB wss wa cA cC eqss cB cD eqss anbi12i bitr4i syl6ib
    sylbid com12 sylbi cA cC cB cD xpeq12 impbid1 $.

  $( Cancellation law for cross-product.  (Contributed by NM, 30-Aug-2011.) $)
  xpcan $p |- ( C =/= (/) -> ( ( C X. A ) = ( C X. B ) <-> A = B ) ) $=
    cC c0 wne cA c0 wne cC cA cxp cC cB cxp wceq cA cB wceq wb cC c0 wne cA c0
    wne wa cC cA cxp cC cB cxp wceq cC cC wceq cA cB wceq wa cA cB wceq cC cA
    cC cB xp11 cC cC wceq cA cB wceq cC eqid biantrur syl6bbr cC c0 wne cA c0
    wne wn wa cC cA cxp cC cB cxp wceq cA cB wceq cA c0 wne wn cC c0 wne cA c0
    wceq cC cA cxp cC cB cxp wceq cA cB wceq wi cA c0 nne cC c0 wne cA c0 wceq
    wa cA c0 wceq cC cA cxp cC cB cxp wceq cB c0 wceq cA cB wceq cC c0 wne cA
    c0 wceq simpr cC c0 wne cA c0 wceq wa cC cA cxp cC cB cxp wceq cC cB cxp c0
    wceq cB c0 wceq cA c0 wceq cC cA cxp cC cB cxp wceq cC cB cxp c0 wceq wb cC
    c0 wne cA c0 wceq cC cA cxp cC cB cxp wceq c0 cC cB cxp wceq cC cB cxp c0
    wceq cA c0 wceq cC cA cxp c0 cC cB cxp cA c0 wceq cC cA cxp cC c0 cxp c0 cA
    c0 cC xpeq2 cC xp0 syl6eq eqeq1d c0 cC cB cxp eqcom syl6bb adantl cC c0 wne
    cC cB cxp c0 wceq cB c0 wceq wi cA c0 wceq cC c0 wne cC c0 wceq wn cC cB
    cxp c0 wceq cB c0 wceq wi cC c0 df-ne cC cB cxp c0 wceq cC c0 wceq cB c0
    wceq wo cC c0 wceq wn cB c0 wceq cC cB xpeq0 cC c0 wceq cB c0 wceq orel1
    syl5bi sylbi adantr sylbid cA cB c0 eqtr3 ee12an sylan2b cA cB cC xpeq2
    impbid1 pm2.61dan $.

  $( Cancellation law for cross-product.  (Contributed by NM, 30-Aug-2011.) $)
  xpcan2 $p |- ( C =/= (/) -> ( ( A X. C ) = ( B X. C ) <-> A = B ) ) $=
    cA c0 wne cC c0 wne cA cC cxp cB cC cxp wceq cA cB wceq wb cA c0 wne cC c0
    wne wa cA cC cxp cB cC cxp wceq cA cB wceq cC cC wceq wa cA cB wceq cA cC
    cB cC xp11 cC cC wceq cA cB wceq cC eqid biantru syl6bbr cA c0 wne wn cA c0
    wceq cC c0 wne cA cC cxp cB cC cxp wceq cA cB wceq wb cA c0 nne cA c0 wceq
    cC c0 wne wa cA cC cxp cB cC cxp wceq cA cB wceq cA c0 wceq cC c0 wne wa cA
    c0 wceq cA cC cxp cB cC cxp wceq cB c0 wceq cA cB wceq cA c0 wceq cC c0 wne
    simpl cA c0 wceq cC c0 wne wa cA cC cxp cB cC cxp wceq cB cC cxp c0 wceq cB
    c0 wceq cA c0 wceq cA cC cxp cB cC cxp wceq cB cC cxp c0 wceq wb cC c0 wne
    cA c0 wceq cA cC cxp cB cC cxp wceq c0 cB cC cxp wceq cB cC cxp c0 wceq cA
    c0 wceq cA cC cxp c0 cB cC cxp cA c0 wceq cA cC cxp c0 cC cxp c0 cA c0 cC
    xpeq1 cC xp0r syl6eq eqeq1d c0 cB cC cxp eqcom syl6bb adantr cC c0 wne cB
    cC cxp c0 wceq cB c0 wceq wi cA c0 wceq cC c0 wne cC c0 wceq wn cB cC cxp
    c0 wceq cB c0 wceq wi cC c0 df-ne cB cC cxp c0 wceq cB c0 wceq cC c0 wceq
    wo cC c0 wceq wn cB c0 wceq cB cC xpeq0 cC c0 wceq cB c0 wceq orel2 syl5bi
    sylbi adantl sylbid cA cB c0 eqtr3 ee12an cA cB cC xpeq1 impbid1 sylanb
    pm2.61ian $.

  $( If a cross product is a set, one of its components must be a set.
     (Contributed by NM, 27-Aug-2006.) $)
  xpexr $p |- ( ( A X. B ) e. C -> ( A e. _V \/ B e. _V ) ) $=
    cA cB cxp cC wcel cA cvv wcel cB cvv wcel cA cB cxp cC wcel cA cvv wcel wn
    cB cvv wcel wi wi cA c0 cA c0 wceq cA cvv wcel wn cB cvv wcel wi cA cB cxp
    cC wcel cA c0 wceq cA cvv wcel cB cvv wcel cA c0 wceq cA cvv wcel c0 cvv
    wcel 0ex cA c0 cvv eleq1 mpbiri pm2.24d a1d cA c0 wne cA cB cxp cC wcel cB
    cvv wcel cA cvv wcel wn cA cB cxp cC wcel cA cB cxp crn cvv wcel cA c0 wne
    cB cvv wcel cA cB cxp cC rnexg cA c0 wne cA cB cxp crn cB cvv cA cB rnxp
    eleq1d syl5ib a1dd pm2.61ine orrd $.

  $( If a nonempty cross product is a set, so are both of its components.
     (Contributed by NM, 27-Aug-2006.) $)
  xpexr2 $p |- ( ( ( A X. B ) e. C /\ ( A X. B ) =/= (/) ) ->
               ( A e. _V /\ B e. _V ) ) $=
    cA cB cxp c0 wne cA cB cxp cC wcel cA c0 wne cB c0 wne wa cA cvv wcel cB
    cvv wcel wa cA cB xpnz cA cB cxp cC wcel cB c0 wne cA c0 wne cA cvv wcel cB
    cvv wcel wa cA cB cxp cC wcel cB c0 wne cA cvv wcel cA c0 wne cB cvv wcel
    cA cB cxp cC wcel cB c0 wne wa cA cB cxp cdm cA cvv cB c0 wne cA cB cxp cdm
    cA wceq cA cB cxp cC wcel cA cB dmxp adantl cA cB cxp cC wcel cA cB cxp cdm
    cvv wcel cB c0 wne cA cB cxp cC dmexg adantr eqeltrrd cA cB cxp cC wcel cA
    c0 wne wa cA cB cxp crn cB cvv cA c0 wne cA cB cxp crn cB wceq cA cB cxp cC
    wcel cA cB rnxp adantl cA cB cxp cC wcel cA cB cxp crn cvv wcel cA c0 wne
    cA cB cxp cC rnexg adantr eqeltrrd anim12dan ancom2s sylan2br $.

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Subset of the range of a restriction.  (Contributed by NM,
       16-Jan-2006.) $)
    ssrnres $p |- ( B C_ ran ( C |` A ) <-> ran ( C i^i ( A X. B ) ) = B ) $=
      cC cA cB cxp cin crn cB wceq cB cC cA cB cxp cin crn wss cB cC cA cres
      crn wss cC cA cB cxp cin crn cB wceq cC cA cB cxp cin crn cB wss cB cC cA
      cB cxp cin crn wss cC cA cB cxp cin crn cA cB cxp crn cB cC cA cB cxp cin
      cA cB cxp wss cC cA cB cxp cin crn cA cB cxp crn wss cC cA cB cxp inss2
      cC cA cB cxp cin cA cB cxp rnss ax-mp cA cB rnxpss sstri cC cA cB cxp cin
      crn cB eqss mpbiran cB cC cA cB cxp cin crn wss cB cC cA cres crn wss cB
      cC cA cB cxp cin crn wss cC cA cB cxp cin crn cC cA cres crn wss cB cC cA
      cres crn wss cC cA cB cxp cin cC cA cres wss cC cA cB cxp cin crn cC cA
      cres crn wss cC cA cB cxp cin cC cA cvv cxp cin cC cA cres cA cB cxp cA
      cvv cxp wss cC cA cB cxp cin cC cA cvv cxp cin wss cA cA wss cB cvv wss
      cA cB cxp cA cvv cxp wss cA ssid cB ssv cA cA cB cvv xpss12 mp2an cA cB
      cxp cA cvv cxp cC sslin ax-mp cC cA df-res sseqtr4i cC cA cB cxp cin cC
      cA cres rnss ax-mp cB cC cA cB cxp cin crn cC cA cres crn sstr mpan2 cB
      cC cA cres crn wss vy cB cC cA cB cxp cin crn cB cC cA cres crn wss vy cv
      cB wcel vx cv vy cv cop cC cA cres wcel vx wex vy cv cB wcel wa vy cv cC
      cA cB cxp cin crn wcel cB cC cA cres crn wss vy cv cB wcel vx cv vy cv
      cop cC cA cres wcel vx wex cB cC cA cres crn wss vy cv cB wcel vy cv cC
      cA cres crn wcel vx cv vy cv cop cC cA cres wcel vx wex cB cC cA cres crn
      vy cv ssel vx vy cv cC cA cres vy vex elrn2 syl6ib ancrd vy cv cC cA cB
      cxp cin crn wcel vx cv vy cv cop cC cA cB cxp cin wcel vx wex vx cv vy cv
      cop cC cA cres wcel vy cv cB wcel wa vx wex vx cv vy cv cop cC cA cres
      wcel vx wex vy cv cB wcel wa vx vy cv cC cA cB cxp cin vy vex elrn2 vx cv
      vy cv cop cC cA cB cxp cin wcel vx cv vy cv cop cC cA cres wcel vy cv cB
      wcel wa vx vx cv vy cv cop cC cA cB cxp cin wcel vx cv vy cv cop cC wcel
      vx cv vy cv cop cA cB cxp wcel wa vx cv vy cv cop cC wcel vx cv cA wcel
      vy cv cB wcel wa wa vx cv vy cv cop cC cA cres wcel vy cv cB wcel wa vx
      cv vy cv cop cC cA cB cxp elin vx cv vy cv cop cA cB cxp wcel vx cv cA
      wcel vy cv cB wcel wa vx cv vy cv cop cC wcel vx cv vy cv cA cB opelxp
      anbi2i vx cv vy cv cop cC cA cres wcel vy cv cB wcel wa vx cv vy cv cop
      cC wcel vx cv cA wcel wa vy cv cB wcel wa vx cv vy cv cop cC wcel vx cv
      cA wcel vy cv cB wcel wa wa vx cv vy cv cop cC cA cres wcel vx cv vy cv
      cop cC wcel vx cv cA wcel wa vy cv cB wcel vx cv vy cv cC cA vy vex
      opelres anbi1i vx cv vy cv cop cC wcel vx cv cA wcel vy cv cB wcel anass
      bitr2i 3bitri exbii vx cv vy cv cop cC cA cres wcel vy cv cB wcel vx
      19.41v 3bitri syl6ibr ssrdv impbii bitr2i $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.
    $( Range of the intersection with a cross product.  (Contributed by NM,
       17-Jan-2006.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    rninxp $p |- ( ran ( C i^i ( A X. B ) ) = B <->
                 A. y e. B E. x e. A x C y ) $=
      cB cC cA cres crn wss vy cv cC cA cres crn wcel vy cB wral cC cA cB cxp
      cin crn cB wceq vx cv vy cv cC wbr vx cA wrex vy cB wral vy cB cC cA cres
      crn dfss3 cA cB cC ssrnres vy cv cC cA cres crn wcel vx cv vy cv cC wbr
      vx cA wrex vy cB vy cv cC cA cres crn wcel vy cv cC cA cima wcel vx cv vy
      cv cC wbr vx cA wrex cC cA cima cC cA cres crn vy cv cC cA df-ima eleq2i
      vx vy cv cC cA vy vex elima bitr3i ralbii 3bitr3i $.
  $}

  ${
    $d x A $.  $d x y B $.  $d x y C $.
    $( Domain of the intersection with a cross product.  (Contributed by NM,
       17-Jan-2006.) $)
    dminxp $p |- ( dom ( C i^i ( A X. B ) ) = A <->
                 A. x e. A E. y e. B x C y ) $=
      cC cA cB cxp cin cdm cA wceq cC ccnv cB cA cxp cin crn cA wceq vy cv vx
      cv cC ccnv wbr vy cB wrex vx cA wral vx cv vy cv cC wbr vy cB wrex vx cA
      wral cC cA cB cxp cin cdm cC ccnv cB cA cxp cin crn cA cC cA cB cxp cin
      cdm cC cA cB cxp cin ccnv crn cC ccnv cB cA cxp cin crn cC cA cB cxp cin
      dfdm4 cC cA cB cxp cin ccnv cC ccnv cB cA cxp cin cC cA cB cxp cin ccnv
      cC ccnv cA cB cxp ccnv cin cC ccnv cB cA cxp cin cC cA cB cxp cnvin cA cB
      cxp ccnv cB cA cxp cC ccnv cA cB cnvxp ineq2i eqtri rneqi eqtri eqeq1i vy
      vx cB cA cC ccnv rninxp vy cv vx cv cC ccnv wbr vy cB wrex vx cv vy cv cC
      wbr vy cB wrex vx cA vy cv vx cv cC ccnv wbr vx cv vy cv cC wbr vy cB vy
      cv vx cv cC vy vex vx vex brcnv rexbii ralbii 3bitri $.
  $}

  $( Image of a relation restricted to a rectangular region.  (Contributed by
     Stefan O'Rear, 19-Feb-2015.) $)
  imainrect $p |- ( ( G i^i ( A X. B ) ) " Y ) =
      ( ( G " ( Y i^i A ) ) i^i B ) $=
    cG cA cB cxp cin cY cres crn cG cA cB cxp cin cY cvv cxp cin crn cG cA cB
    cxp cin cY cima cG cY cA cin cima cB cin cG cA cB cxp cin cY cres cG cA cB
    cxp cin cY cvv cxp cin cG cA cB cxp cin cY df-res rneqi cG cA cB cxp cin cY
    df-ima cG cY cA cin cima cB cin cG cY cA cin cvv cxp cin crn cB cin cG cA
    cB cxp cin cY cvv cxp cin crn cG cY cA cin cima cG cY cA cin cvv cxp cin
    crn cB cG cY cA cin cima cG cY cA cin cres crn cG cY cA cin cvv cxp cin crn
    cG cY cA cin df-ima cG cY cA cin cres cG cY cA cin cvv cxp cin cG cY cA cin
    df-res rneqi eqtri ineq1i cG cY cA cin cvv cxp cin ccnv cB cres cdm cG cA
    cB cxp cin cY cvv cxp cin ccnv cdm cG cY cA cin cvv cxp cin crn cB cin cG
    cA cB cxp cin cY cvv cxp cin crn cG cY cA cin cvv cxp cin ccnv cB cres cG
    cA cB cxp cin cY cvv cxp cin ccnv cG cY cA cin cvv cxp cin cvv cB cxp cin
    ccnv cG cY cA cin cvv cxp cin ccnv cvv cB cxp ccnv cin cG cA cB cxp cin cY
    cvv cxp cin ccnv cG cY cA cin cvv cxp cin ccnv cB cres cG cY cA cin cvv cxp
    cin cvv cB cxp cnvin cG cA cB cxp cin cY cvv cxp cin cG cY cA cin cvv cxp
    cin cvv cB cxp cin cG cY cvv cxp cin cA cB cxp cin cG cY cvv cxp cin cA cvv
    cxp cvv cB cxp cin cin cG cA cB cxp cin cY cvv cxp cin cG cY cA cin cvv cxp
    cin cvv cB cxp cin cA cB cxp cA cvv cxp cvv cB cxp cin cG cY cvv cxp cin cA
    cvv cxp cvv cB cxp cin cA cvv cin cvv cB cin cxp cA cB cxp cA cvv cvv cB
    inxp cA cvv cin cA cvv cB cin cB cA inv1 cvv cB cin cB cvv cin cB cvv cB
    incom cB inv1 eqtri xpeq12i eqtr2i ineq2i cG cA cB cxp cY cvv cxp in32 cG
    cY cA cin cvv cxp cin cvv cB cxp cin cG cY cvv cxp cin cA cvv cxp cin cvv
    cB cxp cin cG cY cvv cxp cin cA cvv cxp cvv cB cxp cin cin cG cY cA cin cvv
    cxp cin cG cY cvv cxp cin cA cvv cxp cin cvv cB cxp cG cY cA cin cvv cxp
    cin cG cY cvv cxp cA cvv cxp cin cin cG cY cvv cxp cin cA cvv cxp cin cY cA
    cin cvv cxp cY cvv cxp cA cvv cxp cin cG cY cA cvv xpindir ineq2i cG cY cvv
    cxp cA cvv cxp inass eqtr4i ineq1i cG cY cvv cxp cin cA cvv cxp cvv cB cxp
    inass eqtri 3eqtr4i cnveqi cG cY cA cin cvv cxp cin ccnv cB cres cG cY cA
    cin cvv cxp cin ccnv cB cvv cxp cin cG cY cA cin cvv cxp cin ccnv cvv cB
    cxp ccnv cin cG cY cA cin cvv cxp cin ccnv cB df-res cvv cB cxp ccnv cB cvv
    cxp cG cY cA cin cvv cxp cin ccnv cvv cB cnvxp ineq2i eqtr4i 3eqtr4ri dmeqi
    cB cG cY cA cin cvv cxp cin ccnv cdm cin cG cY cA cin cvv cxp cin ccnv cdm
    cB cin cG cY cA cin cvv cxp cin ccnv cB cres cdm cG cY cA cin cvv cxp cin
    crn cB cin cB cG cY cA cin cvv cxp cin ccnv cdm incom cG cY cA cin cvv cxp
    cin ccnv cB dmres cG cY cA cin cvv cxp cin crn cG cY cA cin cvv cxp cin
    ccnv cdm cB cG cY cA cin cvv cxp cin df-rn ineq1i 3eqtr4ri cG cA cB cxp cin
    cY cvv cxp cin df-rn 3eqtr4ri eqtr4i 3eqtr4i $.

  ${
    $d x y A $.  $d x B $.  $d x y R $.  $d x V $.
    $( The base set of a strict order is contained in the field of the
       relation, except possibly for one element (note that
       ` (/) Or { B } ` ).  (Contributed by Mario Carneiro, 27-Apr-2015.) $)
    sossfld $p |- ( ( R Or A /\ B e. A ) ->
      ( A \ { B } ) C_ ( dom R u. ran R ) ) $=
      cA cR wor cB cA wcel wa vx cA cB csn cdif cR cdm cR crn cun vx cv cA cB
      csn cdif wcel vx cv cA wcel vx cv cB wne wa cA cR wor cB cA wcel wa vx cv
      cR cdm cR crn cun wcel vx cv cA cB eldifsn cA cR wor cB cA wcel wa vx cv
      cA wcel vx cv cB wne vx cv cR cdm cR crn cun wcel cA cR wor cB cA wcel wa
      vx cv cA wcel wa vx cv cB wne vx cv cB cR wbr cB vx cv cR wbr wo vx cv cR
      cdm cR crn cun wcel cA cR wor vx cv cA wcel cB cA wcel vx cv cB cR wbr cB
      vx cv cR wbr wo vx cv cB wne wb cA cR wor vx cv cA wcel cB cA wcel wa wa
      vx cv cB cR wbr cB vx cv cR wbr wo vx cv cB cA vx cv cB cR sotrieq
      necon2abid anass1rs cA cR wor cB cA wcel wa vx cv cA wcel wa vx cv cB cR
      wbr cB vx cv cR wbr wo vx cv cR cdm wcel vx cv cR crn wcel wo vx cv cR
      cdm cR crn cun wcel cA cR wor cB cA wcel wa vx cv cA wcel wa vx cv cB cR
      wbr vx cv cR cdm wcel cB vx cv cR wbr vx cv cR crn wcel cA cR wor vx cv
      cA wcel cB cA wcel vx cv cB cR wbr vx cv cR cdm wcel wi vx cv cA wcel cB
      cA wcel vx cv cB cR wbr vx cv cR cdm wcel wi cA cR wor vx cv cA wcel cB
      cA wcel vx cv cB cR wbr vx cv cR cdm wcel vx cv cB cA cA cR breldmg
      3expia adantll an32s cB cA wcel vx cv cA wcel cB vx cv cR wbr vx cv cR
      crn wcel wi cA cR wor cB cA wcel vx cv cA wcel cB vx cv cR wbr vx cv cR
      crn wcel cB vx cv cR cA cA brelrng 3expia adantll orim12d vx cv cR cdm cR
      crn elun syl6ibr sylbird expimpd syl5bi ssrdv $.

    $( The base set of a nonempty strict order is the same as the field of the
       relation.  (Contributed by Mario Carneiro, 15-May-2015.) $)
    sofld $p |- ( ( R Or A /\ R C_ ( A X. A ) /\ R =/= (/) ) ->
      A = ( dom R u. ran R ) ) $=
      cA cR wor cR cA cA cxp wss cR c0 wne w3a cA cR cdm cR crn cun cA cR wor
      cR cA cA cxp wss cR c0 wne cA cR cdm cR crn cun wss cA cR wor cR cA cA
      cxp wss wa cA cR cdm cR crn cun wss cR c0 cA cR wor cR cA cA cxp wss wa
      cA cR cdm cR crn cun wss wn cR c0 wceq cA cR wor cR cA cA cxp wss wa cA
      cR cdm cR crn cun wss wn wa cR c0 wss cR c0 wceq cA cR wor cR cA cA cxp
      wss wa cA cR cdm cR crn cun wss wn wa vx vy cR c0 cR cA cA cxp wss cR
      wrel cA cR wor cA cR cdm cR crn cun wss wn cR cA cA cxp wss cA cA cxp
      wrel cR wrel cA cA relxp cR cA cA cxp relss mpi ad2antlr cA cR wor cR cA
      cA cxp wss wa cA cR cdm cR crn cun wss wn wa vx cv vy cv cop cR wcel vx
      cv vy cv cop c0 wcel cA cR wor cR cA cA cxp wss wa vx cv vy cv cop cR
      wcel cA cR cdm cR crn cun wss vx cv vy cv cop cR wcel vx cv vy cv cR wbr
      cA cR wor cR cA cA cxp wss wa cA cR cdm cR crn cun wss vx cv vy cv cR
      df-br cA cR wor cR cA cA cxp wss wa vx cv vy cv cR wbr cA cR cdm cR crn
      cun wss cA cR wor cR cA cA cxp wss wa vx cv vy cv cR wbr wa cA cA vx cv
      csn cdif vx cv csn cun cR cdm cR crn cun cA cA vx cv csn cun cA vx cv csn
      cdif vx cv csn cun cA vx cv csn ssun1 cA vx cv csn undif1 sseqtr4i cA cR
      wor cR cA cA cxp wss wa vx cv vy cv cR wbr wa cA vx cv csn cdif vx cv csn
      cR cdm cR crn cun cA cR wor cR cA cA cxp wss wa vx cv vy cv cR wbr wa cA
      cR wor vx cv cA wcel cA vx cv csn cdif cR cdm cR crn cun wss cA cR wor cR
      cA cA cxp wss vx cv vy cv cR wbr simpll cA cR wor cR cA cA cxp wss wa vx
      cv vy cv cR wbr wa cR cdm cA vx cv cR cA cA cxp wss cR cdm cA wss cA cR
      wor vx cv vy cv cR wbr cR cA cA cxp wss cR cdm cA cA cxp cdm cA cR cA cA
      cxp dmss cA dmxpid syl6sseq ad2antlr cA cR wor cR cA cA cxp wss wa vx cv
      vy cv cR wbr cR wrel vx cv cR cdm wcel cR cA cA cxp wss cR wrel cA cR wor
      vx cv vy cv cR wbr cR cA cA cxp wss cA cA cxp wrel cR wrel cA cA relxp cR
      cA cA cxp relss mpi ad2antlr vx cv vy cv cR releldm sylancom sseldd cA vx
      cv cR sossfld syl2anc cA cR wor cR cA cA cxp wss wa vx cv vy cv cR wbr wa
      vx cv cR cdm cR crn cun cA cR wor cR cA cA cxp wss wa vx cv vy cv cR wbr
      wa cR cdm cR cdm cR crn cun vx cv cR cdm cR crn ssun1 cA cR wor cR cA cA
      cxp wss wa vx cv vy cv cR wbr cR wrel vx cv cR cdm wcel cR cA cA cxp wss
      cR wrel cA cR wor vx cv vy cv cR wbr cR cA cA cxp wss cA cA cxp wrel cR
      wrel cA cA relxp cR cA cA cxp relss mpi ad2antlr vx cv vy cv cR releldm
      sylancom sseldi snssd unssd syl5ss ex syl5bir con3and pm2.21d relssdv cR
      ss0 syl ex necon1ad 3impia cR cA cA cxp wss cA cR wor cR cdm cR crn cun
      cA wss cR c0 wne cR cA cA cxp wss cR cdm cR crn cA cR cA cA cxp wss cR
      cdm cA cA cxp cdm cA cR cA cA cxp dmss cA dmxpid syl6sseq cR cA cA cxp
      wss cR crn cA cA cxp crn cA cR cA cA cxp rnss cA rnxpid syl6sseq unssd
      3ad2ant2 eqssd $.

    $( If the relation in a strict order is a set, then the base field is also
       a set.  (Contributed by Mario Carneiro, 27-Apr-2015.) $)
    soex $p |- ( ( R Or A /\ R e. V ) -> A e. _V ) $=
      cA cR wor cR cV wcel wa cA cvv wcel cA c0 cA cR wor cR cV wcel wa cA c0
      wceq wa cA c0 cvv cA cR wor cR cV wcel wa cA c0 wceq simpr 0ex syl6eqel
      cA c0 wne cA cR wor cR cV wcel wa vx cv cA wcel vx wex cA cvv wcel vx cA
      n0 cA cR wor cR cV wcel wa vx cv cA wcel vx wex cA cvv wcel cA cR wor cR
      cV wcel wa vx cv cA wcel cA cvv wcel vx cA cR wor cR cV wcel wa vx cv cA
      wcel cA cvv wcel cA cR wor cR cV wcel wa vx cv cA wcel wa cA vx cv csn cR
      cdm cR crn cun cun wss vx cv csn cR cdm cR crn cun cun cvv wcel cA cvv
      wcel cA cR wor cR cV wcel wa vx cv cA wcel wa cA vx cv csn cdif cR cdm cR
      crn cun wss cA vx cv csn cR cdm cR crn cun cun wss cA cR wor vx cv cA
      wcel cA vx cv csn cdif cR cdm cR crn cun wss cR cV wcel cA vx cv cR
      sossfld adantlr cA vx cv csn cR cdm cR crn cun ssundif sylibr cR cV wcel
      vx cv csn cR cdm cR crn cun cun cvv wcel cA cR wor vx cv cA wcel cR cV
      wcel vx cv csn cvv wcel cR cdm cR crn cun cvv wcel vx cv csn cR cdm cR
      crn cun cun cvv wcel vx cv snex cR cV wcel cR cdm cvv wcel cR crn cvv
      wcel cR cdm cR crn cun cvv wcel cR cV dmexg cR cV rnexg cR cdm cR crn cvv
      cvv unexg syl2anc vx cv csn cR cdm cR crn cun cvv cvv unexg sylancr
      ad2antlr cA vx cv csn cR cdm cR crn cun cun cvv ssexg syl2anc ex exlimdv
      imp sylan2b pm2.61dane $.
  $}

  ${
    $d x y R $.
    $( The set of all ordered pairs in a class is the same as the double
       converse.  (Contributed by Mario Carneiro, 16-Aug-2015.) $)
    cnvcnv3 $p |- `' `' R = { <. x , y >. | x R y } $=
      cR ccnv ccnv vy cv vx cv cR ccnv wbr vx vy copab vx cv vy cv cR wbr vx vy
      copab vx vy cR ccnv df-cnv vy cv vx cv cR ccnv wbr vx cv vy cv cR wbr vx
      vy vy cv vx cv cR vy vex vx vex brcnv opabbii eqtri $.

    $( Alternate definition of relation.  Exercise 2 of [TakeutiZaring] p. 25.
       (Contributed by NM, 29-Dec-1996.) $)
    dfrel2 $p |- ( Rel R <-> `' `' R = R ) $=
      cR wrel cR ccnv ccnv cR wceq cR ccnv ccnv wrel cR wrel cR ccnv ccnv cR
      wceq cR ccnv relcnv vx vy cR ccnv ccnv cR vx cv vy cv cop cR ccnv ccnv
      wcel vy cv vx cv cop cR ccnv wcel vx cv vy cv cop cR wcel vx cv vy cv cR
      ccnv vx vex vy vex opelcnv vy cv vx cv cR vy vex vx vex opelcnv bitri
      eqrelriv mpan cR ccnv ccnv cR wceq cR ccnv ccnv wrel cR wrel cR ccnv
      relcnv cR ccnv ccnv cR releq mpbii impbii $.

    $( A relation can be expressed as the set of ordered pairs in it.  An
       analogue of ~ dffn5 for relations.  (Contributed by Mario Carneiro,
       16-Aug-2015.) $)
    dfrel4v $p |- ( Rel R <-> R = { <. x , y >. | x R y } ) $=
      cR wrel cR ccnv ccnv cR wceq cR cR ccnv ccnv wceq cR vx cv vy cv cR wbr
      vx vy copab wceq cR dfrel2 cR ccnv ccnv cR eqcom cR ccnv ccnv vx cv vy cv
      cR wbr vx vy copab cR vx vy cR cnvcnv3 eqeq2i 3bitri $.
  $}

  $( The double converse of a class strips out all elements that are not
     ordered pairs.  (Contributed by NM, 8-Dec-2003.) $)
  cnvcnv $p |- `' `' A = ( A i^i ( _V X. _V ) ) $=
    cA ccnv ccnv cA ccnv ccnv cvv cvv cxp ccnv ccnv cin cA ccnv cvv cvv cxp
    ccnv cin ccnv cA cvv cvv cxp cin cA ccnv ccnv cvv cvv cxp ccnv ccnv wss cA
    ccnv ccnv cA ccnv ccnv cvv cvv cxp ccnv ccnv cin wceq cA ccnv ccnv cvv cvv
    cxp cvv cvv cxp ccnv ccnv cA ccnv ccnv wrel cA ccnv ccnv cvv cvv cxp wss cA
    ccnv relcnv cA ccnv ccnv df-rel mpbi cvv cvv cxp wrel cvv cvv cxp ccnv ccnv
    cvv cvv cxp wceq cvv cvv relxp cvv cvv cxp dfrel2 mpbi sseqtr4i cA ccnv
    ccnv cvv cvv cxp ccnv ccnv dfss mpbi cA ccnv cvv cvv cxp ccnv cnvin cA cvv
    cvv cxp cin ccnv ccnv cA ccnv cvv cvv cxp ccnv cin ccnv cA cvv cvv cxp cin
    cA cvv cvv cxp cin ccnv cA ccnv cvv cvv cxp ccnv cin cA cvv cvv cxp cnvin
    cnveqi cA cvv cvv cxp cin wrel cA cvv cvv cxp cin ccnv ccnv cA cvv cvv cxp
    cin wceq cA cvv cvv cxp cin wrel cA cvv cvv cxp cin cvv cvv cxp wss cA cvv
    cvv cxp inss2 cA cvv cvv cxp cin df-rel mpbir cA cvv cvv cxp cin dfrel2
    mpbi eqtr3i 3eqtr2i $.

  $( The double converse of a class equals its restriction to the universe.
     (Contributed by NM, 8-Oct-2007.) $)
  cnvcnv2 $p |- `' `' A = ( A |` _V ) $=
    cA ccnv ccnv cA cvv cvv cxp cin cA cvv cres cA cnvcnv cA cvv df-res eqtr4i
    $.

  $( The double converse of a class is a subclass.  Exercise 2 of
     [TakeutiZaring] p. 25.  (Contributed by NM, 23-Jul-2004.) $)
  cnvcnvss $p |- `' `' A C_ A $=
    cA ccnv ccnv cA cvv cvv cxp cin cA cA cnvcnv cA cvv cvv cxp inss1 eqsstri
    $.

  $( Equality theorem for converse.  (Contributed by FL, 19-Sep-2011.) $)
  cnveqb $p |- ( ( Rel A /\ Rel B ) -> ( A = B <-> `' A = `' B ) ) $=
    cA wrel cB wrel wa cA cB wceq cA ccnv cB ccnv wceq cA cB cnveq cA wrel cB
    wrel cA ccnv cB ccnv wceq cA cB wceq wi cA wrel cA ccnv ccnv cA wceq cB
    wrel cA ccnv cB ccnv wceq cA cB wceq wi wi cA dfrel2 cB wrel cA ccnv cB
    ccnv wceq cA cB wceq wi wi cA cA ccnv ccnv cB wrel cA ccnv cB ccnv wceq cA
    cB wceq wi cA cA ccnv ccnv wceq cA ccnv cB ccnv wceq cA ccnv ccnv cB wceq
    wi cB wrel cB ccnv ccnv cB wceq cA ccnv cB ccnv wceq cA ccnv ccnv cB wceq
    wi cB dfrel2 cA ccnv cB ccnv wceq cA ccnv ccnv cB wceq wi cB cB ccnv ccnv
    cA ccnv cB ccnv wceq cA ccnv ccnv cB wceq cB cB ccnv ccnv wceq cA ccnv ccnv
    cB ccnv ccnv wceq cA ccnv cB ccnv cnveq cB cB ccnv ccnv cA ccnv ccnv eqeq2
    syl5ibr eqcoms sylbi cA cA ccnv ccnv wceq cA cB wceq cA ccnv ccnv cB wceq
    cA ccnv cB ccnv wceq cA cA ccnv ccnv cB eqeq1 imbi2d syl5ibr eqcoms sylbi
    imp impbid2 $.

  $( A relation empty iff its converse is empty.  (Contributed by FL,
     19-Sep-2011.) $)
  cnveq0 $p |- ( Rel A -> ( A = (/) <-> `' A = (/) ) ) $=
    c0 ccnv c0 wceq cA wrel cA c0 wceq cA ccnv c0 wceq wb wi cnv0 cA wrel cA c0
    wceq cA ccnv c0 wceq wb wi c0 c0 ccnv cA wrel cA c0 wceq cA ccnv c0 wceq wb
    c0 c0 ccnv wceq cA c0 wceq cA ccnv c0 ccnv wceq wb cA wrel c0 wrel cA c0
    wceq cA ccnv c0 ccnv wceq wb rel0 cA c0 cnveqb mpan2 c0 c0 ccnv wceq cA
    ccnv c0 wceq cA ccnv c0 ccnv wceq cA c0 wceq c0 c0 ccnv cA ccnv eqeq2
    bibi2d syl5ibr eqcoms ax-mp $.
    $( [19-Sep-2011] $)

  $( Alternate definition of relation.  (Contributed by NM, 14-May-2008.) $)
  dfrel3 $p |- ( Rel R <-> ( R |` _V ) = R ) $=
    cR wrel cR ccnv ccnv cR wceq cR cvv cres cR wceq cR dfrel2 cR ccnv ccnv cR
    cvv cres cR cR cnvcnv2 eqeq1i bitri $.

  $( The domain of a universal restriction.  (Contributed by NM,
     14-May-2008.) $)
  dmresv $p |- dom ( A |` _V ) = dom A $=
    cA cvv cres cdm cvv cA cdm cin cA cdm cvv cin cA cdm cA cvv dmres cvv cA
    cdm incom cA cdm inv1 3eqtri $.

  $( The range of a universal restriction.  (Contributed by NM,
     14-May-2008.) $)
  rnresv $p |- ran ( A |` _V ) = ran A $=
    cA ccnv ccnv crn cA cvv cres crn cA crn cA ccnv ccnv cA cvv cres cA cnvcnv2
    rneqi cA rncnvcnv eqtr3i $.

  $( Range defined in terms of image.  (Contributed by NM, 14-May-2008.) $)
  dfrn4 $p |- ran A = ( A " _V ) $=
    cA cvv cima cA cvv cres crn cA crn cA cvv df-ima cA rnresv eqtr2i $.

  $( The restriction of the double converse of a class.  (Contributed by NM,
     8-Apr-2007.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
  rescnvcnv $p |- ( `' `' A |` B ) = ( A |` B ) $=
    cA ccnv ccnv cB cres cA cvv cres cB cres cA cvv cB cin cres cA cB cres cA
    ccnv ccnv cA cvv cres cB cA cnvcnv2 reseq1i cA cvv cB resres cvv cB cin cB
    cA cB cvv wss cvv cB cin cB wceq cB ssv cB cvv sseqin2 mpbi reseq2i 3eqtri
    $.

  $( The double converse of the restriction of a class.  (Contributed by NM,
     3-Jun-2007.) $)
  cnvcnvres $p |- `' `' ( A |` B ) = ( `' `' A |` B ) $=
    cA cB cres ccnv ccnv cA cB cres cA ccnv ccnv cB cres cA cB cres wrel cA cB
    cres ccnv ccnv cA cB cres wceq cA cB relres cA cB cres dfrel2 mpbi cA cB
    rescnvcnv eqtr4i $.

  $( The image of the double converse of a class.  (Contributed by NM,
     8-Apr-2007.) $)
  imacnvcnv $p |- ( `' `' A " B ) = ( A " B ) $=
    cA ccnv ccnv cB cres crn cA cB cres crn cA ccnv ccnv cB cima cA cB cima cA
    ccnv ccnv cB cres cA cB cres cA cB rescnvcnv rneqi cA ccnv ccnv cB df-ima
    cA cB df-ima 3eqtr4i $.

  ${
    $d x y A $.
    $( The domain of a singleton is nonzero iff the singleton argument is an
       ordered pair.  (Contributed by NM, 14-Dec-2008.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.) $)
    dmsnn0 $p |- ( A e. ( _V X. _V ) <-> dom { A } =/= (/) ) $=
      cA vx cv vy cv cop wceq vy wex vx wex vx cv cA csn cdm wcel vx wex cA cvv
      cvv cxp wcel cA csn cdm c0 wne cA vx cv vy cv cop wceq vy wex vx cv cA
      csn cdm wcel vx vx cv cA csn cdm wcel vx cv vy cv cA csn wbr vy wex cA vx
      cv vy cv cop wceq vy wex vy vx cv cA csn vx vex eldm vx cv vy cv cA csn
      wbr cA vx cv vy cv cop wceq vy vx cv vy cv cA csn wbr vx cv vy cv cop cA
      csn wcel vx cv vy cv cop cA wceq cA vx cv vy cv cop wceq vx cv vy cv cA
      csn df-br vx cv vy cv cop cA vx cv vy cv opex elsnc vx cv vy cv cop cA
      eqcom 3bitri exbii bitr2i exbii vx vy cA elvv vx cA csn cdm n0 3bitr4i $.
  $}

  $( The range of a singleton is nonzero iff the singleton argument is an
     ordered pair.  (Contributed by NM, 14-Dec-2008.) $)
  rnsnn0 $p |- ( A e. ( _V X. _V ) <-> ran { A } =/= (/) ) $=
    cA cvv cvv cxp wcel cA csn cdm c0 wne cA csn crn c0 wne cA dmsnn0 cA csn
    cdm c0 cA csn crn c0 cA csn dm0rn0 necon3bii bitri $.

  $( The domain of the singleton of the empty set is empty.  (Contributed by
     NM, 30-Jan-2004.) $)
  dmsn0 $p |- dom { (/) } = (/) $=
    c0 csn cdm c0 wceq c0 cvv cvv cxp wcel wn cvv cvv 0nelxp c0 cvv cvv cxp
    wcel c0 csn cdm c0 c0 dmsnn0 necon2bbii mpbir $.

  $( The converse of the singleton of the empty set is empty.  (Contributed by
     Mario Carneiro, 30-Aug-2015.) $)
  cnvsn0 $p |- `' { (/) } = (/) $=
    c0 csn ccnv c0 wceq c0 csn ccnv crn c0 wceq c0 csn cdm c0 csn ccnv crn c0
    c0 csn dfdm4 dmsn0 eqtr3i c0 csn ccnv wrel c0 csn ccnv c0 wceq c0 csn ccnv
    crn c0 wceq wb c0 csn relcnv c0 csn ccnv relrn0 ax-mp mpbir $.

  $( The domain of a singleton is empty if the singleton's argument contains
     the empty set.  (Contributed by NM, 15-Dec-2008.) $)
  dmsn0el $p |- ( (/) e. A -> dom { A } = (/) ) $=
    c0 cA wcel cA csn cdm c0 cA csn cdm c0 wne cA cvv cvv cxp wcel c0 cA wcel
    wn cA dmsnn0 cvv cvv cA 0nelelxp sylbir necon4ai $.

  ${
    relsn2.1 $e |- A e. _V $.
    $( A singleton is a relation iff it has a nonempty domain.  (Contributed by
       NM, 25-Sep-2013.) $)
    relsn2 $p |- ( Rel { A } <-> dom { A } =/= (/) ) $=
      cA csn wrel cA cvv cvv cxp wcel cA csn cdm c0 wne cA relsn2.1 relsn cA
      dmsnn0 bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x V $.
    $( The domain of a singleton of an ordered pair is the singleton of the
       first member.  (Contributed by Mario Carneiro, 26-Apr-2015.) $)
    dmsnopg $p |- ( B e. V -> dom { <. A , B >. } = { A } ) $=
      cB cV wcel vx cA cB cop csn cdm cA csn cB cV wcel vx cv vy cv cop cA cB
      cop wceq vy wex vx cv cA wceq vx cv cA cB cop csn cdm wcel vx cv cA csn
      wcel cB cV wcel vx cv vy cv cop cA cB cop wceq vy wex vx cv cA wceq vx cv
      vy cv cop cA cB cop wceq vx cv cA wceq vy vx cv vy cv cA cB vx vex vy vex
      opth1 exlimiv vx cv cA wceq vx cv cB cop cA cB cop wceq cB cV wcel vx cv
      vy cv cop cA cB cop wceq vy wex vx cv cA cB opeq1 vx cv vy cv cop cA cB
      cop wceq vx cv cB cop cA cB cop wceq vy cB cV vy cv cB wceq vx cv vy cv
      cop vx cv cB cop cA cB cop vy cv cB vx cv opeq2 eqeq1d spcegv syl5
      impbid2 vx cv cA cB cop csn cdm wcel vx cv vy cv cop cA cB cop csn wcel
      vy wex vx cv vy cv cop cA cB cop wceq vy wex vy vx cv cA cB cop csn vx
      vex eldm2 vx cv vy cv cop cA cB cop csn wcel vx cv vy cv cop cA cB cop
      wceq vy vx cv vy cv cop cA cB cop vx cv vy cv opex elsnc exbii bitri vx
      cA elsn 3bitr4g eqrdv $.

    $( The domain of a singleton of an ordered pair is a subset of the
       singleton of the first member (with no sethood assumptions on ` B ` ).
       (Contributed by Mario Carneiro, 30-Apr-2015.) $)
    dmsnopss $p |- dom { <. A , B >. } C_ { A } $=
      cB cvv wcel cA cB cop csn cdm cA csn wss cB cvv wcel cA cB cop csn cdm cA
      csn wceq cA cB cop csn cdm cA csn wss cA cB cvv dmsnopg cA cB cop csn cdm
      cA csn eqimss syl cB cvv wcel wn cA cB cop csn cdm c0 cA csn cB cvv wcel
      wn cA cB cop csn cdm c0 csn cdm c0 cB cvv wcel wn cA cB cop csn c0 csn cB
      cvv wcel wn cA cB cop c0 cA cB opprc2 sneqd dmeqd dmsn0 syl6eq c0 cA csn
      wss cB cvv wcel wn cA csn 0ss a1i eqsstrd pm2.61i $.

    $( The domain of an unordered pair of ordered pairs.  (Contributed by Mario
       Carneiro, 26-Apr-2015.) $)
    dmpropg $p |- ( ( B e. V /\ D e. W ) ->
        dom { <. A , B >. , <. C , D >. } = { A , C } ) $=
      cB cV wcel cD cW wcel wa cA cB cop csn cdm cC cD cop csn cdm cun cA csn
      cC csn cun cA cB cop cC cD cop cpr cdm cA cC cpr cB cV wcel cA cB cop csn
      cdm cA csn wceq cC cD cop csn cdm cC csn wceq cA cB cop csn cdm cC cD cop
      csn cdm cun cA csn cC csn cun wceq cD cW wcel cA cB cV dmsnopg cC cD cW
      dmsnopg cA cB cop csn cdm cA csn cC cD cop csn cdm cC csn uneq12 syl2an
      cA cB cop cC cD cop cpr cdm cA cB cop csn cC cD cop csn cun cdm cA cB cop
      csn cdm cC cD cop csn cdm cun cA cB cop cC cD cop cpr cA cB cop csn cC cD
      cop csn cun cA cB cop cC cD cop df-pr dmeqi cA cB cop csn cC cD cop csn
      dmun eqtri cA cC df-pr 3eqtr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.
    dmsnop.1 $e |- B e. _V $.
    $( The domain of a singleton of an ordered pair is the singleton of the
       first member.  (Contributed by NM, 30-Jan-2004.)  (Proof shortened by
       Andrew Salmon, 27-Aug-2011.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    dmsnop $p |- dom { <. A , B >. } = { A } $=
      cB cvv wcel cA cB cop csn cdm cA csn wceq dmsnop.1 cA cB cvv dmsnopg
      ax-mp $.

    dmprop.1 $e |- D e. _V $.
    $( The domain of an unordered pair of ordered pairs.  (Contributed by NM,
       13-Sep-2011.) $)
    dmprop $p |- dom { <. A , B >. , <. C , D >. } = { A , C } $=
      cB cvv wcel cD cvv wcel cA cB cop cC cD cop cpr cdm cA cC cpr wceq
      dmsnop.1 dmprop.1 cA cB cC cD cvv cvv dmpropg mp2an $.

    dmtpop.1 $e |- F e. _V $.
    $( The domain of an unordered triple of ordered pairs.  (Contributed by NM,
       14-Sep-2011.) $)
    dmtpop $p |- dom { <. A , B >. , <. C , D >. , <. E , F >. }
                        = { A , C , E } $=
      cA cB cop cC cD cop cE cF cop ctp cdm cA cC cpr cE csn cun cA cC cE ctp
      cA cB cop cC cD cop cE cF cop ctp cdm cA cB cop cC cD cop cpr cE cF cop
      csn cun cdm cA cB cop cC cD cop cpr cdm cE cF cop csn cdm cun cA cC cpr
      cE csn cun cA cB cop cC cD cop cE cF cop ctp cA cB cop cC cD cop cpr cE
      cF cop csn cun cA cB cop cC cD cop cE cF cop df-tp dmeqi cA cB cop cC cD
      cop cpr cE cF cop csn dmun cA cB cop cC cD cop cpr cdm cA cC cpr cE cF
      cop csn cdm cE csn cA cB cC cD dmsnop.1 dmprop.1 dmprop cE cF dmtpop.1
      dmsnop uneq12i 3eqtri cA cC cE df-tp eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Double converse of a singleton of an ordered pair.  (Unlike ~ cnvsn ,
       this does not need any sethood assumptions on ` A ` and ` B ` .)
       (Contributed by Mario Carneiro, 26-Apr-2015.) $)
    cnvcnvsn $p |- `' `' { <. A , B >. } = `' { <. B , A >. } $=
      vx vy cA cB cop csn ccnv ccnv cB cA cop csn ccnv cA cB cop csn ccnv
      relcnv cB cA cop csn relcnv vx cv vy cv cop cA cB cop csn ccnv ccnv wcel
      vy cv vx cv cop cA cB cop csn ccnv wcel vx cv vy cv cop cB cA cop csn
      ccnv wcel vx cv vy cv cA cB cop csn ccnv vx vex vy vex opelcnv vx cv vy
      cv cop cA cB cop csn wcel vy cv vx cv cop cB cA cop csn wcel vy cv vx cv
      cop cA cB cop csn ccnv wcel vx cv vy cv cop cB cA cop csn ccnv wcel vx cv
      vy cv cop cA cB cop wceq vy cv vx cv cop cB cA cop wceq vx cv vy cv cop
      cA cB cop csn wcel vy cv vx cv cop cB cA cop csn wcel vx cv cA wceq vy cv
      cB wceq wa vy cv cB wceq vx cv cA wceq wa vx cv vy cv cop cA cB cop wceq
      vy cv vx cv cop cB cA cop wceq vx cv cA wceq vy cv cB wceq ancom vx cv vy
      cv cA cB vx vex vy vex opth vy cv vx cv cB cA vy vex vx vex opth 3bitr4i
      vx cv vy cv cop cA cB cop vx cv vy cv opex elsnc vy cv vx cv cop cB cA
      cop vy cv vx cv opex elsnc 3bitr4i vy cv vx cv cA cB cop csn vy vex vx
      vex opelcnv vx cv vy cv cB cA cop csn vx vex vy vex opelcnv 3bitr4i bitri
      eqrelriiv $.

    $( The domain of the singleton of the singleton of a singleton.
       (Contributed by NM, 15-Sep-2004.)  (Revised by Mario Carneiro,
       26-Apr-2015.) $)
    dmsnsnsn $p |- dom { { { A } } } = { A } $=
      cA cvv wcel cA csn csn csn cdm cA csn wceq vx cv vx cv cop csn cdm vx cv
      csn wceq cA csn csn csn cdm cA csn wceq vx cA cvv vx cv cA wceq vx cv vx
      cv cop csn cdm cA csn csn csn cdm vx cv csn cA csn vx cv cA wceq vx cv vx
      cv cop csn cA csn csn csn vx cv cA wceq vx cv vx cv cop cA csn csn vx cv
      cA wceq vx cv vx cv cop vx cv csn csn cA csn csn vx cv vx vex opid vx cv
      cA wceq vx cv csn cA csn vx cv cA sneq sneqd syl5eq sneqd dmeqd vx cv cA
      sneq eqeq12d vx cv vx cv vx vex dmsnop vtoclg cA cvv wcel wn c0 csn csn
      cdm c0 cA csn csn csn cdm cA csn c0 c0 csn wcel c0 csn csn cdm c0 wceq c0
      0ex snid c0 csn dmsn0el ax-mp cA cvv wcel wn cA csn csn csn c0 csn csn cA
      cvv wcel wn cA csn csn c0 csn cA cvv wcel wn cA csn c0 cA cvv wcel wn cA
      csn c0 wceq cA snprc biimpi sneqd sneqd dmeqd cA cvv wcel wn cA csn c0
      wceq cA snprc biimpi 3eqtr4a pm2.61i $.
  $}

  $( The range of a singleton of an ordered pair is the singleton of the second
     member.  (Contributed by NM, 24-Jul-2004.)  (Revised by Mario Carneiro,
     30-Apr-2015.) $)
  rnsnopg $p |- ( A e. V -> ran { <. A , B >. } = { B } ) $=
    cA cV wcel cA cB cop csn crn cB cA cop csn cdm cB csn cA cB cop csn crn cA
    cB cop csn ccnv cdm cB cA cop csn cdm cA cB cop csn df-rn cB cA cop csn cdm
    cB cA cop csn ccnv crn cB cA cop csn ccnv ccnv cdm cA cB cop csn ccnv cdm
    cB cA cop csn dfdm4 cB cA cop csn ccnv df-rn cB cA cop csn ccnv ccnv cA cB
    cop csn ccnv cB cA cnvcnvsn dmeqi 3eqtri eqtr4i cB cA cV dmsnopg syl5eq $.

  ${
    $d x y A $.  $d x y B $.
    cnvsn.1 $e |- A e. _V $.
    $( The range of a singleton of an ordered pair is the singleton of the
       second member.  (Contributed by NM, 24-Jul-2004.)  (Revised by Mario
       Carneiro, 26-Apr-2015.) $)
    rnsnop $p |- ran { <. A , B >. } = { B } $=
      cA cvv wcel cA cB cop csn crn cB csn wceq cnvsn.1 cA cB cvv rnsnopg ax-mp
      $.

    cnvsn.2 $e |- B e. _V $.
    $( Extract the first member of an ordered pair.  (See ~ op2nda to extract
       the second member, ~ op1stb for an alternate version, and ~ op1st for
       the preferred version.)  (Contributed by Raph Levien, 4-Dec-2003.) $)
    op1sta $p |- U. dom { <. A , B >. } = A $=
      cA cB cop csn cdm cuni cA csn cuni cA cA cB cop csn cdm cA csn cA cB
      cnvsn.2 dmsnop unieqi cA cnvsn.1 unisn eqtri $.

    $( Converse of a singleton of an ordered pair.  (Contributed by NM,
       11-May-1998.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    cnvsn $p |- `' { <. A , B >. } = { <. B , A >. } $=
      cB cA cop csn ccnv ccnv cA cB cop csn ccnv cB cA cop csn cB cA cnvcnvsn
      cB cA cop csn wrel cB cA cop csn ccnv ccnv cB cA cop csn wceq cB cA
      cnvsn.2 cnvsn.1 relsnop cB cA cop csn dfrel2 mpbi eqtr3i $.

    $( Extract the second member of an ordered pair.  Theorem 5.12(ii) of
       [Monk1] p. 52.  (See ~ op1stb to extract the first member, ~ op2nda for
       an alternate version, and ~ op2nd for the preferred version.)
       (Contributed by NM, 25-Nov-2003.) $)
    op2ndb $p |- |^| |^| |^| `' { <. A , B >. } = B $=
      cA cB cop csn ccnv cint cint cint cB cA cop cint cint cB cA cB cop csn
      ccnv cint cint cB cA cop cint cA cB cop csn ccnv cint cB cA cop cA cB cop
      csn ccnv cint cB cA cop csn cint cB cA cop cA cB cop csn ccnv cB cA cop
      csn cA cB cnvsn.1 cnvsn.2 cnvsn inteqi cB cA cop cB cA opex intsn eqtri
      inteqi inteqi cB cA cnvsn.2 cnvsn.1 op1stb eqtri $.

    $( Extract the second member of an ordered pair.  (See ~ op1sta to extract
       the first member, ~ op2ndb for an alternate version, and ~ op2nd for the
       preferred version.)  (Contributed by NM, 17-Feb-2004.)  (Proof shortened
       by Andrew Salmon, 27-Aug-2011.) $)
    op2nda $p |- U. ran { <. A , B >. } = B $=
      cA cB cop csn crn cuni cB csn cuni cB cA cB cop csn crn cB csn cA cB
      cnvsn.1 rnsnop unieqi cB cnvsn.2 unisn eqtri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.
    $( Converse of a singleton of an ordered pair.  (Contributed by NM,
       23-Jan-2015.) $)
    cnvsng $p |- ( ( A e. V /\ B e. W ) ->
      `' { <. A , B >. } = { <. B , A >. } ) $=
      vx cv vy cv cop csn ccnv vy cv vx cv cop csn wceq cA vy cv cop csn ccnv
      vy cv cA cop csn wceq cA cB cop csn ccnv cB cA cop csn wceq vx vy cA cB
      cV cW vx cv cA wceq vx cv vy cv cop csn ccnv cA vy cv cop csn ccnv vy cv
      vx cv cop csn vy cv cA cop csn vx cv cA wceq vx cv vy cv cop csn cA vy cv
      cop csn vx cv cA wceq vx cv vy cv cop cA vy cv cop vx cv cA vy cv opeq1
      sneqd cnveqd vx cv cA wceq vy cv vx cv cop vy cv cA cop vx cv cA vy cv
      opeq2 sneqd eqeq12d vy cv cB wceq cA vy cv cop csn ccnv cA cB cop csn
      ccnv vy cv cA cop csn cB cA cop csn vy cv cB wceq cA vy cv cop csn cA cB
      cop csn vy cv cB wceq cA vy cv cop cA cB cop vy cv cB cA opeq2 sneqd
      cnveqd vy cv cB wceq vy cv cA cop cB cA cop vy cv cB cA opeq1 sneqd
      eqeq12d vx cv vy cv vx vex vy vex cnvsn vtocl2g $.

    $( Swap the members of an ordered pair.  (Contributed by NM, 14-Dec-2008.)
       (Revised by Mario Carneiro, 30-Aug-2015.) $)
    opswap $p |- U. `' { <. A , B >. } = <. B , A >. $=
      cA cvv wcel cB cvv wcel wa cA cB cop csn ccnv cuni cB cA cop wceq cA cvv
      wcel cB cvv wcel wa cA cB cop csn ccnv cuni cB cA cop csn cuni cB cA cop
      cA cvv wcel cB cvv wcel wa cA cB cop csn ccnv cB cA cop csn cA cB cvv cvv
      cnvsng unieqd cB cA cop cB cA opex unisn syl6eq cA cvv wcel cB cvv wcel
      wa wn c0 cuni c0 cA cB cop csn ccnv cuni cB cA cop uni0 cA cvv wcel cB
      cvv wcel wa wn cA cB cop csn ccnv c0 cA cvv wcel cB cvv wcel wa wn cA cB
      cop csn ccnv c0 csn ccnv c0 cA cvv wcel cB cvv wcel wa wn cA cB cop csn
      c0 csn cA cvv wcel cB cvv wcel wa wn cA cB cop c0 cA cB opprc sneqd
      cnveqd cnvsn0 syl6eq unieqd cA cvv wcel cB cvv wcel wa cB cvv wcel cA cvv
      wcel wa cB cA cop c0 wceq cA cvv wcel cB cvv wcel ancom cB cA opprc
      sylnbi 3eqtr4a pm2.61i $.

    $( Membership in a cross product.  This version requires no quantifiers or
       dummy variables.  See also ~ elxp5 , ~ elxp6 , and ~ elxp7 .
       (Contributed by NM, 17-Feb-2004.) $)
    elxp4 $p |- ( A e. ( B X. C ) <-> ( A = <. U. dom { A } , U. ran { A } >.
                 /\ ( U. dom { A } e. B /\ U. ran { A } e. C ) ) ) $=
      cA cB cC cxp wcel cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa
      wa vy wex vx wex vx cv cA csn cdm cuni wceq cA vx cv cA csn crn cuni cop
      wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa vx wex cA cA csn cdm
      cuni cA csn crn cuni cop wceq cA csn cdm cuni cB wcel cA csn crn cuni cC
      wcel wa wa vx vy cA cB cC elxp cA vx cv vy cv cop wceq vx cv cB wcel vy
      cv cC wcel wa wa vy wex vx cv cA csn cdm cuni wceq cA vx cv cA csn crn
      cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa vx cA vx cv
      vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex cA vx cv cA csn
      crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa vx cv cA
      csn cdm cuni wceq cA vx cv cA csn crn cuni cop wceq wa vx cv cB wcel cA
      csn crn cuni cC wcel wa wa vx cv cA csn cdm cuni wceq cA vx cv cA csn crn
      cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa cA vx cv vy
      cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vy cv cA csn crn
      cuni wceq cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa wa vy
      wex cA vx cv cA csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC
      wcel wa wa cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy
      cv cA csn crn cuni wceq cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC
      wcel wa wa wa vy cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa
      wa vy cv cA csn crn cuni wceq cA vx cv vy cv cop wceq wa vx cv cB wcel vy
      cv cC wcel wa wa vy cv cA csn crn cuni wceq cA vx cv vy cv cop wceq vx cv
      cB wcel vy cv cC wcel wa wa wa cA vx cv vy cv cop wceq vy cv cA csn crn
      cuni wceq cA vx cv vy cv cop wceq wa vx cv cB wcel vy cv cC wcel wa cA vx
      cv vy cv cop wceq vy cv cA csn crn cuni wceq cA vx cv vy cv cop wceq cA
      csn crn cuni vx cv vy cv cop csn crn cuni vy cv cA vx cv vy cv cop wceq
      cA csn crn vx cv vy cv cop csn crn cA vx cv vy cv cop wceq cA csn vx cv
      vy cv cop csn cA vx cv vy cv cop sneq rneqd unieqd vx cv vy cv vx vex vy
      vex op2nda syl6req pm4.71ri anbi1i vy cv cA csn crn cuni wceq cA vx cv vy
      cv cop wceq vx cv cB wcel vy cv cC wcel wa anass bitri exbii cA vx cv vy
      cv cop wceq vx cv cB wcel vy cv cC wcel wa wa cA vx cv cA csn crn cuni
      cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa vy cA csn crn cuni
      cA csn crn cA csn cA snex rnex uniex vy cv cA csn crn cuni wceq cA vx cv
      vy cv cop wceq cA vx cv cA csn crn cuni cop wceq vx cv cB wcel vy cv cC
      wcel wa vx cv cB wcel cA csn crn cuni cC wcel wa vy cv cA csn crn cuni
      wceq vx cv vy cv cop vx cv cA csn crn cuni cop cA vy cv cA csn crn cuni
      vx cv opeq2 eqeq2d vy cv cA csn crn cuni wceq vy cv cC wcel cA csn crn
      cuni cC wcel vx cv cB wcel vy cv cA csn crn cuni cC eleq1 anbi2d anbi12d
      ceqsexv bitri cA vx cv cA csn crn cuni cop wceq vx cv cA csn cdm cuni
      wceq cA vx cv cA csn crn cuni cop wceq wa vx cv cB wcel cA csn crn cuni
      cC wcel wa cA vx cv cA csn crn cuni cop wceq vx cv cA csn cdm cuni wceq
      cA vx cv cA csn crn cuni cop wceq cA csn cdm cuni vx cv cA csn crn cuni
      cop csn cdm cuni vx cv cA vx cv cA csn crn cuni cop wceq cA csn cdm vx cv
      cA csn crn cuni cop csn cdm cA vx cv cA csn crn cuni cop wceq cA csn vx
      cv cA csn crn cuni cop csn cA vx cv cA csn crn cuni cop sneq dmeqd unieqd
      vx cv cA csn crn cuni vx vex cA csn crn cA csn cA snex rnex uniex op1sta
      syl6req pm4.71ri anbi1i vx cv cA csn cdm cuni wceq cA vx cv cA csn crn
      cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa anass 3bitri exbii
      cA vx cv cA csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel
      wa wa cA cA csn cdm cuni cA csn crn cuni cop wceq cA csn cdm cuni cB wcel
      cA csn crn cuni cC wcel wa wa vx cA csn cdm cuni cA csn cdm cA csn cA
      snex dmex uniex vx cv cA csn cdm cuni wceq cA vx cv cA csn crn cuni cop
      wceq cA cA csn cdm cuni cA csn crn cuni cop wceq vx cv cB wcel cA csn crn
      cuni cC wcel wa cA csn cdm cuni cB wcel cA csn crn cuni cC wcel wa vx cv
      cA csn cdm cuni wceq vx cv cA csn crn cuni cop cA csn cdm cuni cA csn crn
      cuni cop cA vx cv cA csn cdm cuni cA csn crn cuni opeq1 eqeq2d vx cv cA
      csn cdm cuni wceq vx cv cB wcel cA csn cdm cuni cB wcel cA csn crn cuni
      cC wcel vx cv cA csn cdm cuni cB eleq1 anbi1d anbi12d ceqsexv 3bitri $.

    $( Membership in a cross product requiring no quantifiers or dummy
       variables.  Provides a slightly shorter version of ~ elxp4 when the
       double intersection does not create class existence problems (caused by
       ~ int0 ).  (Contributed by NM, 1-Aug-2004.) $)
    elxp5 $p |- ( A e. ( B X. C ) <-> ( A = <. |^| |^| A , U. ran { A } >.
                 /\ ( |^| |^| A e. B /\ U. ran { A } e. C ) ) ) $=
      cA cB cC cxp wcel cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa
      wa vy wex vx wex vx cv cA cint cint wceq cA vx cv cA csn crn cuni cop
      wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa vx wex cA cA cint
      cint cA csn crn cuni cop wceq cA cint cint cB wcel cA csn crn cuni cC
      wcel wa wa vx vy cA cB cC elxp cA vx cv vy cv cop wceq vx cv cB wcel vy
      cv cC wcel wa wa vy wex vx cv cA cint cint wceq cA vx cv cA csn crn cuni
      cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa vx cA vx cv vy cv
      cop wceq vx cv cB wcel vy cv cC wcel wa wa vy wex cA vx cv cA csn crn
      cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa vx cv cA cint
      cint wceq cA vx cv cA csn crn cuni cop wceq wa vx cv cB wcel cA csn crn
      cuni cC wcel wa wa vx cv cA cint cint wceq cA vx cv cA csn crn cuni cop
      wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa cA vx cv vy cv cop
      wceq vx cv cB wcel vy cv cC wcel wa wa vy wex vy cv cA csn crn cuni wceq
      cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa wa vy wex cA vx
      cv cA csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa
      cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy cv cA csn
      crn cuni wceq cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa
      wa vy cA vx cv vy cv cop wceq vx cv cB wcel vy cv cC wcel wa wa vy cv cA
      csn crn cuni wceq cA vx cv vy cv cop wceq wa vx cv cB wcel vy cv cC wcel
      wa wa vy cv cA csn crn cuni wceq cA vx cv vy cv cop wceq vx cv cB wcel vy
      cv cC wcel wa wa wa cA vx cv vy cv cop wceq vy cv cA csn crn cuni wceq cA
      vx cv vy cv cop wceq wa vx cv cB wcel vy cv cC wcel wa cA vx cv vy cv cop
      wceq vy cv cA csn crn cuni wceq cA vx cv vy cv cop wceq cA csn crn cuni
      vx cv vy cv cop csn crn cuni vy cv cA vx cv vy cv cop wceq cA csn crn vx
      cv vy cv cop csn crn cA vx cv vy cv cop wceq cA csn vx cv vy cv cop csn
      cA vx cv vy cv cop sneq rneqd unieqd vx cv vy cv vx vex vy vex op2nda
      syl6req pm4.71ri anbi1i vy cv cA csn crn cuni wceq cA vx cv vy cv cop
      wceq vx cv cB wcel vy cv cC wcel wa anass bitri exbii cA vx cv vy cv cop
      wceq vx cv cB wcel vy cv cC wcel wa wa cA vx cv cA csn crn cuni cop wceq
      vx cv cB wcel cA csn crn cuni cC wcel wa wa vy cA csn crn cuni cA csn crn
      cA csn cA snex rnex uniex vy cv cA csn crn cuni wceq cA vx cv vy cv cop
      wceq cA vx cv cA csn crn cuni cop wceq vx cv cB wcel vy cv cC wcel wa vx
      cv cB wcel cA csn crn cuni cC wcel wa vy cv cA csn crn cuni wceq vx cv vy
      cv cop vx cv cA csn crn cuni cop cA vy cv cA csn crn cuni vx cv opeq2
      eqeq2d vy cv cA csn crn cuni wceq vy cv cC wcel cA csn crn cuni cC wcel
      vx cv cB wcel vy cv cA csn crn cuni cC eleq1 anbi2d anbi12d ceqsexv bitri
      cA vx cv cA csn crn cuni cop wceq vx cv cA cint cint wceq cA vx cv cA csn
      crn cuni cop wceq wa vx cv cB wcel cA csn crn cuni cC wcel wa cA vx cv cA
      csn crn cuni cop wceq vx cv cA cint cint wceq cA vx cv cA csn crn cuni
      cop wceq cA cint cint vx cv cA csn crn cuni cop cint cint vx cv cA vx cv
      cA csn crn cuni cop wceq cA cint vx cv cA csn crn cuni cop cint cA vx cv
      cA csn crn cuni cop inteq inteqd vx cv cA csn crn cuni vx vex cA csn crn
      cA csn cA snex rnex uniex op1stb syl6req pm4.71ri anbi1i vx cv cA cint
      cint wceq cA vx cv cA csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni
      cC wcel wa anass 3bitri exbii vx cv cA cint cint wceq cA vx cv cA csn crn
      cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa vx wex cA
      cint cint cvv wcel cA cA cint cint cA csn crn cuni cop wceq cA cint cint
      cB wcel cA csn crn cuni cC wcel wa wa vx cv cA cint cint wceq cA vx cv cA
      csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa wa cA
      cint cint cvv wcel vx vx cv cA cint cint wceq cA cint cint cvv wcel cA vx
      cv cA csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel wa wa
      vx cv cA cint cint wceq vx cv cvv wcel cA cint cint cvv wcel vx vex vx cv
      cA cint cint cvv eleq1 mpbii adantr exlimiv cA cint cint cB wcel cA cint
      cint cvv wcel cA cA cint cint cA csn crn cuni cop wceq cA csn crn cuni cC
      wcel cA cint cint cB elex ad2antrl cA vx cv cA csn crn cuni cop wceq vx
      cv cB wcel cA csn crn cuni cC wcel wa wa cA cA cint cint cA csn crn cuni
      cop wceq cA cint cint cB wcel cA csn crn cuni cC wcel wa wa vx cA cint
      cint cvv vx cv cA cint cint wceq cA vx cv cA csn crn cuni cop wceq cA cA
      cint cint cA csn crn cuni cop wceq vx cv cB wcel cA csn crn cuni cC wcel
      wa cA cint cint cB wcel cA csn crn cuni cC wcel wa vx cv cA cint cint
      wceq vx cv cA csn crn cuni cop cA cint cint cA csn crn cuni cop cA vx cv
      cA cint cint cA csn crn cuni opeq1 eqeq2d vx cv cA cint cint wceq vx cv
      cB wcel cA cint cint cB wcel cA csn crn cuni cC wcel vx cv cA cint cint
      cB eleq1 anbi1d anbi12d ceqsexgv pm5.21nii 3bitri $.
  $}

  ${
    $d s t A $.  $d s t B $.  $d s t F $.
    $( An image under the converse of a restriction.  (Contributed by Jeff
       Hankins, 12-Jul-2009.) $)
    cnvresima $p |- ( `' ( F |` A ) " B ) = ( ( `' F " B ) i^i A ) $=
      vt cF cA cres ccnv cB cima cF ccnv cB cima cA cin vt cv cF cA cres ccnv
      cB cima wcel vs cv cB wcel vs cv vt cv cop cF cA cres ccnv wcel wa vs wex
      vt cv cF ccnv cB cima cA cin wcel vs vt cv cF cA cres ccnv cB vt vex
      elima3 vt cv cF ccnv cB cima wcel vt cv cA wcel wa vs cv cB wcel vs cv vt
      cv cop cF ccnv wcel wa vs wex vt cv cA wcel wa vt cv cF ccnv cB cima cA
      cin wcel vs cv cB wcel vs cv vt cv cop cF cA cres ccnv wcel wa vs wex vt
      cv cF ccnv cB cima wcel vs cv cB wcel vs cv vt cv cop cF ccnv wcel wa vs
      wex vt cv cA wcel vs vt cv cF ccnv cB vt vex elima3 anbi1i vt cv cF ccnv
      cB cima cA elin vs cv cB wcel vs cv vt cv cop cF cA cres ccnv wcel wa vs
      wex vs cv cB wcel vs cv vt cv cop cF ccnv wcel wa vt cv cA wcel wa vs wex
      vs cv cB wcel vs cv vt cv cop cF ccnv wcel wa vs wex vt cv cA wcel wa vs
      cv cB wcel vs cv vt cv cop cF cA cres ccnv wcel wa vs cv cB wcel vs cv vt
      cv cop cF ccnv wcel wa vt cv cA wcel wa vs vs cv cB wcel vs cv vt cv cop
      cF cA cres ccnv wcel wa vs cv cB wcel vs cv vt cv cop cF ccnv wcel vt cv
      cA wcel wa wa vs cv cB wcel vs cv vt cv cop cF ccnv wcel wa vt cv cA wcel
      wa vs cv vt cv cop cF cA cres ccnv wcel vs cv vt cv cop cF ccnv wcel vt
      cv cA wcel wa vs cv cB wcel vs cv vt cv cop cF cA cres ccnv wcel vt cv vs
      cv cop cF cA cres wcel vs cv vt cv cop cF ccnv wcel vt cv cA wcel wa vs
      cv vt cv cF cA cres vs vex vt vex opelcnv vt cv vs cv cop cF cA cres wcel
      vt cv vs cv cop cF wcel vt cv cA wcel wa vs cv vt cv cop cF ccnv wcel vt
      cv cA wcel wa vt cv vs cv cF cA vs vex opelres vs cv vt cv cop cF ccnv
      wcel vt cv vs cv cop cF wcel vt cv cA wcel vs cv vt cv cF vs vex vt vex
      opelcnv anbi1i bitr4i bitri anbi2i vs cv cB wcel vs cv vt cv cop cF ccnv
      wcel vt cv cA wcel anass bitr4i exbii vs cv cB wcel vs cv vt cv cop cF
      ccnv wcel wa vt cv cA wcel vs 19.41v bitri 3bitr4ri bitri eqriv $.
  $}

  $( A class restricted to its domain equals its double converse.  (Contributed
     by NM, 8-Apr-2007.) $)
  resdm2 $p |- ( A |` dom A ) = `' `' A $=
    cA ccnv ccnv cA ccnv ccnv cdm cres cA cA ccnv ccnv cdm cres cA ccnv ccnv cA
    cA cdm cres cA cA ccnv ccnv cdm rescnvcnv cA ccnv ccnv wrel cA ccnv ccnv cA
    ccnv ccnv cdm cres cA ccnv ccnv wceq cA ccnv relcnv cA ccnv ccnv resdm
    ax-mp cA ccnv ccnv cdm cA cdm cA cA dmcnvcnv reseq2i 3eqtr3ri $.

  $( Restriction to the domain of a restriction.  (Contributed by NM,
     8-Apr-2007.) $)
  resdmres $p |- ( A |` dom ( A |` B ) ) = ( A |` B ) $=
    cA cA cB cres cdm cres cA ccnv ccnv cB cres cA cB cres cA cB cvv cxp cA cdm
    cvv cxp cin cin cA ccnv ccnv cB cvv cxp cin cA cA cB cres cdm cres cA ccnv
    ccnv cB cres cA cB cvv cxp cA cdm cvv cxp cin cin cB cvv cxp cA cA cdm cvv
    cxp cin cin cB cvv cxp cA ccnv ccnv cin cA ccnv ccnv cB cvv cxp cin cA cB
    cvv cxp cA cdm cvv cxp in12 cA cA cdm cvv cxp cin cA ccnv ccnv cB cvv cxp
    cA cA cdm cres cA cA cdm cvv cxp cin cA ccnv ccnv cA cA cdm df-res cA
    resdm2 eqtr3i ineq2i cB cvv cxp cA ccnv ccnv incom 3eqtri cA cA cB cres cdm
    cres cA cA cB cres cdm cvv cxp cin cA cB cvv cxp cA cdm cvv cxp cin cin cA
    cA cB cres cdm df-res cA cB cres cdm cvv cxp cB cvv cxp cA cdm cvv cxp cin
    cA cA cB cres cdm cvv cxp cB cA cdm cin cvv cxp cB cvv cxp cA cdm cvv cxp
    cin cA cB cres cdm cB cA cdm cin cvv cA cB dmres xpeq1i cB cA cdm cvv
    xpindir eqtri ineq2i eqtri cA ccnv ccnv cB df-res 3eqtr4i cA cB rescnvcnv
    eqtri $.

  $( The image of the domain of a restriction.  (Contributed by NM,
     8-Apr-2007.) $)
  imadmres $p |- ( A " dom ( A |` B ) ) = ( A " B ) $=
    cA cA cB cres cdm cres crn cA cB cres crn cA cA cB cres cdm cima cA cB cima
    cA cA cB cres cdm cres cA cB cres cA cB resdmres rneqi cA cA cB cres cdm
    df-ima cA cB df-ima 3eqtr4i $.

  ${
    $d x y C $.  $d y A $.  $d y B $.  $d y F $.  $d x V $.
    dmmpt2.1 $e |- F = ( x e. A |-> B ) $.
    $( The preimage of a function in maps-to notation.  (Contributed by Stefan
       O'Rear, 25-Jan-2015.) $)
    mptpreima $p |- ( `' F " C ) = { x e. A | B e. C } $=
      cF ccnv cC cima vx cv cA wcel vy cv cB wceq wa vy vx copab cC cima cB cC
      wcel vx cA crab cF ccnv vx cv cA wcel vy cv cB wceq wa vy vx copab cC cF
      ccnv vx cv cA wcel vy cv cB wceq wa vx vy copab ccnv vx cv cA wcel vy cv
      cB wceq wa vy vx copab cF vx cv cA wcel vy cv cB wceq wa vx vy copab cF
      vx cA cB cmpt vx cv cA wcel vy cv cB wceq wa vx vy copab dmmpt2.1 vx vy
      cA cB df-mpt eqtri cnveqi vx cv cA wcel vy cv cB wceq wa vx vy cnvopab
      eqtri imaeq1i vx cv cA wcel vy cv cB wceq wa vy vx copab cC cima vx cv cA
      wcel vy cv cB wceq wa vy vx copab cC cres crn cB cC wcel vx cA crab vx cv
      cA wcel vy cv cB wceq wa vy vx copab cC df-ima vx cv cA wcel vy cv cB
      wceq wa vy vx copab cC cres crn vy cv cC wcel vx cv cA wcel vy cv cB wceq
      wa wa vy vx copab crn cB cC wcel vx cA crab vx cv cA wcel vy cv cB wceq
      wa vy vx copab cC cres vy cv cC wcel vx cv cA wcel vy cv cB wceq wa wa vy
      vx copab vx cv cA wcel vy cv cB wceq wa vy vx cC resopab rneqi vy cv cC
      wcel vx cv cA wcel vy cv cB wceq wa wa vy wex vx cab vx cv cA wcel cB cC
      wcel wa vx cab vy cv cC wcel vx cv cA wcel vy cv cB wceq wa wa vy vx
      copab crn cB cC wcel vx cA crab vy cv cC wcel vx cv cA wcel vy cv cB wceq
      wa wa vy wex vx cv cA wcel cB cC wcel wa vx vy cv cC wcel vx cv cA wcel
      vy cv cB wceq wa wa vy wex vx cv cA wcel vy cv cB wceq vy cv cC wcel wa
      wa vy wex vx cv cA wcel cB cC wcel wa vy cv cC wcel vx cv cA wcel vy cv
      cB wceq wa wa vx cv cA wcel vy cv cB wceq vy cv cC wcel wa wa vy vy cv cC
      wcel vx cv cA wcel vy cv cB wceq wa wa vx cv cA wcel vy cv cB wceq wa vy
      cv cC wcel wa vx cv cA wcel vy cv cB wceq vy cv cC wcel wa wa vy cv cC
      wcel vx cv cA wcel vy cv cB wceq wa ancom vx cv cA wcel vy cv cB wceq vy
      cv cC wcel anass bitri exbii vx cv cA wcel vy cv cB wceq vy cv cC wcel wa
      wa vy wex vx cv cA wcel vy cv cB wceq vy cv cC wcel wa vy wex wa vx cv cA
      wcel cB cC wcel wa vx cv cA wcel vy cv cB wceq vy cv cC wcel wa vy 19.42v
      vy cv cB wceq vy cv cC wcel wa vy wex cB cC wcel vx cv cA wcel cB cC wcel
      vy cv cB wceq vy cv cC wcel wa vy wex vy cB cC df-clel bicomi anbi2i
      bitri bitri abbii vy cv cC wcel vx cv cA wcel vy cv cB wceq wa wa vy vx
      rnopab cB cC wcel vx cA df-rab 3eqtr4i eqtri eqtri eqtri $.

    $( Converse singleton image of a function defined by maps-to.  (Contributed
       by Stefan O'Rear, 25-Jan-2015.) $)
    mptiniseg $p |- ( C e. V -> ( `' F " { C } ) = { x e. A | B = C } ) $=
      cC cV wcel cF ccnv cC csn cima cB cC csn wcel vx cA crab cB cC wceq vx cA
      crab vx cA cB cC csn cF dmmpt2.1 mptpreima cC cV wcel cB cC csn wcel cB
      cC wceq vx cA cB cC cV elsnc2g rabbidv syl5eq $.

    $( The domain of the mapping operation in general.  (Contributed by NM,
       16-May-1995.)  (Revised by Mario Carneiro, 22-Mar-2015.) $)
    dmmpt $p |- dom F = { x e. A | B e. _V } $=
      cF cdm cF ccnv crn cF ccnv cvv cima cB cvv wcel vx cA crab cF dfdm4 cF
      ccnv dfrn4 vx cA cB cvv cF dmmpt2.1 mptpreima 3eqtri $.

    $d x A $.
    $( The domain of a mapping is a subset of its base class.  (Contributed by
       Scott Fenton, 17-Jun-2013.) $)
    dmmptss $p |- dom F C_ A $=
      cF cdm cB cvv wcel vx cA crab cA vx cA cB cF dmmpt2.1 dmmpt cB cvv wcel
      vx cA ssrab2 eqsstri $.
  $}

  ${
    $d A x y $.  $d B y $.
    $( The domain of the mapping operation is the stated domain, if the
       function value is always a set.  (Contributed by Mario Carneiro,
       9-Feb-2013.)  (Revised by Mario Carneiro, 14-Sep-2013.) $)
    dmmptg $p |- ( A. x e. A B e. V -> dom ( x e. A |-> B ) = A ) $=
      cB cV wcel vx cA wral cA cB cvv wcel vx cA crab vx cA cB cmpt cdm cB cV
      wcel vx cA wral cB cvv wcel vx cA wral cA cB cvv wcel vx cA crab wceq cB
      cV wcel cB cvv wcel vx cA cB cV elex ralimi cB cvv wcel vx cA rabid2
      sylibr vx cA cB vx cA cB cmpt vx cA cB cmpt eqid dmmpt syl6reqr $.
  $}

  ${
    $d w x y z A $.  $d w x y z B $.  $d w x y z C $.
    $( A composition is a relation.  Exercise 24 of [TakeutiZaring] p. 25.
       (Contributed by NM, 26-Jan-1997.) $)
    relco $p |- Rel ( A o. B ) $=
      vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx vy cA cB ccom vx vy vz
      cA cB df-co relopabi $.

    $( Alternate definition of a class composition, using only one bound
       variable.  (Contributed by NM, 19-Dec-2008.) $)
    dfco2 $p |- ( A o. B )
                = U_ x e. _V ( ( `' B " { x } ) X. ( A " { x } ) ) $=
      vy vz cA cB ccom vx cvv cB ccnv vx cv csn cima cA vx cv csn cima cxp ciun
      cA cB relco vx cvv cB ccnv vx cv csn cima cA vx cv csn cima cxp ciun wrel
      cB ccnv vx cv csn cima cA vx cv csn cima cxp wrel vx cvv vx cvv cB ccnv
      vx cv csn cima cA vx cv csn cima cxp reliun cB ccnv vx cv csn cima cA vx
      cv csn cima cxp wrel vx cv cvv wcel cB ccnv vx cv csn cima cA vx cv csn
      cima relxp a1i mprgbir vy cv vz cv cop cA cB ccom wcel vy cv vx cv cop cB
      wcel vx cv vz cv cop cA wcel wa vx wex vy cv vz cv cop vx cvv cB ccnv vx
      cv csn cima cA vx cv csn cima cxp ciun wcel vy cv cvv wcel vz cv cvv wcel
      vy cv vz cv cop cA cB ccom wcel vy cv vx cv cop cB wcel vx cv vz cv cop
      cA wcel wa vx wex wb vy vex vz vex vx vy cv vz cv cA cB cvv cvv opelco2g
      mp2an vy cv vz cv cop vx cvv cB ccnv vx cv csn cima cA vx cv csn cima cxp
      ciun wcel vy cv vz cv cop cB ccnv vx cv csn cima cA vx cv csn cima cxp
      wcel vx cvv wrex vy cv vz cv cop cB ccnv vx cv csn cima cA vx cv csn cima
      cxp wcel vx wex vy cv vx cv cop cB wcel vx cv vz cv cop cA wcel wa vx wex
      vx vy cv vz cv cop cvv cB ccnv vx cv csn cima cA vx cv csn cima cxp eliun
      vy cv vz cv cop cB ccnv vx cv csn cima cA vx cv csn cima cxp wcel vx rexv
      vy cv vz cv cop cB ccnv vx cv csn cima cA vx cv csn cima cxp wcel vy cv
      vx cv cop cB wcel vx cv vz cv cop cA wcel wa vx vy cv vz cv cop cB ccnv
      vx cv csn cima cA vx cv csn cima cxp wcel vy cv cB ccnv vx cv csn cima
      wcel vz cv cA vx cv csn cima wcel wa vy cv vx cv cop cB wcel vx cv vz cv
      cop cA wcel wa vy cv vz cv cB ccnv vx cv csn cima cA vx cv csn cima
      opelxp vy cv cB ccnv vx cv csn cima wcel vy cv vx cv cop cB wcel vz cv cA
      vx cv csn cima wcel vx cv vz cv cop cA wcel vy cv cB ccnv vx cv csn cima
      wcel vx cv vy cv cop cB ccnv wcel vy cv vx cv cop cB wcel cB ccnv vx cv
      vy cv vx vex vy vex elimasn vx cv vy cv cB vx vex vy vex opelcnv bitri cA
      vx cv vz cv vx vex vz vex elimasn anbi12i bitri exbii 3bitrri bitri
      eqrelriiv $.

    $( Generalization of ~ dfco2 , where ` C ` can have any value between
       ` dom A i^i ran B ` and ` _V ` .  (Contributed by NM, 21-Dec-2008.)
       (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    dfco2a $p |- ( ( dom A i^i ran B ) C_ C -> ( A o. B )
         = U_ x e. C ( ( `' B " { x } ) X. ( A " { x } ) ) ) $=
      cA cdm cB crn cin cC wss cA cB ccom vx cvv cB ccnv vx cv csn cima cA vx
      cv csn cima cxp ciun vx cC cB ccnv vx cv csn cima cA vx cv csn cima cxp
      ciun vx cA cB dfco2 cA cdm cB crn cin cC wss vy vx cvv cB ccnv vx cv csn
      cima cA vx cv csn cima cxp ciun vx cC cB ccnv vx cv csn cima cA vx cv csn
      cima cxp ciun cA cdm cB crn cin cC wss vy cv cB ccnv vx cv csn cima cA vx
      cv csn cima cxp wcel vx cvv wrex vy cv cB ccnv vx cv csn cima cA vx cv
      csn cima cxp wcel vx cC wrex vy cv vx cvv cB ccnv vx cv csn cima cA vx cv
      csn cima cxp ciun wcel vy cv vx cC cB ccnv vx cv csn cima cA vx cv csn
      cima cxp ciun wcel cA cdm cB crn cin cC wss vy cv cB ccnv vx cv csn cima
      cA vx cv csn cima cxp wcel vx wex vx cv cC wcel vy cv cB ccnv vx cv csn
      cima cA vx cv csn cima cxp wcel wa vx wex vy cv cB ccnv vx cv csn cima cA
      vx cv csn cima cxp wcel vx cvv wrex vy cv cB ccnv vx cv csn cima cA vx cv
      csn cima cxp wcel vx cC wrex cA cdm cB crn cin cC wss vy cv cB ccnv vx cv
      csn cima cA vx cv csn cima cxp wcel vx cv cC wcel vy cv cB ccnv vx cv csn
      cima cA vx cv csn cima cxp wcel wa vx cA cdm cB crn cin cC wss vy cv cB
      ccnv vx cv csn cima cA vx cv csn cima cxp wcel vx cv cC wcel vy cv cB
      ccnv vx cv csn cima cA vx cv csn cima cxp wcel vx cv cA cdm cB crn cin
      wcel cA cdm cB crn cin cC wss vx cv cC wcel vy cv vz cv vw cv cop wceq vz
      cv cB ccnv vx cv csn cima wcel vw cv cA vx cv csn cima wcel wa wa vw wex
      vz wex vx cv cA cdm wcel vx cv cB crn wcel wa vy cv cB ccnv vx cv csn
      cima cA vx cv csn cima cxp wcel vx cv cA cdm cB crn cin wcel vy cv vz cv
      vw cv cop wceq vz cv cB ccnv vx cv csn cima wcel vw cv cA vx cv csn cima
      wcel wa wa vx cv cA cdm wcel vx cv cB crn wcel wa vz vw vz cv cB ccnv vx
      cv csn cima wcel vw cv cA vx cv csn cima wcel wa vx cv cA cdm wcel vx cv
      cB crn wcel wa vy cv vz cv vw cv cop wceq vz cv cB ccnv vx cv csn cima
      wcel vx cv cB crn wcel vw cv cA vx cv csn cima wcel vx cv cA cdm wcel vz
      cv cB ccnv vx cv csn cima wcel vz cv vx cv cB wbr vx cv cB crn wcel vx cv
      cvv wcel vz cv cB ccnv vx cv csn cima wcel vz cv vx cv cB wbr wb vx vex
      cB vx cv vz cv cvv vz vex eliniseg ax-mp vz cv vx cv cB vz vex vx vex
      brelrn sylbi vw cv cA vx cv csn cima wcel vx cv vw cv cop cA wcel vx cv
      cA cdm wcel cA vx cv vw cv vx vex vw vex elimasn vx cv vw cv cA vx vex vw
      vex opeldm sylbi anim12ci adantl exlimivv vz vw vy cv cB ccnv vx cv csn
      cima cA vx cv csn cima elxp vx cv cA cdm cB crn elin 3imtr4i cA cdm cB
      crn cin cC vx cv ssel syl5 pm4.71rd exbidv vy cv cB ccnv vx cv csn cima
      cA vx cv csn cima cxp wcel vx rexv vy cv cB ccnv vx cv csn cima cA vx cv
      csn cima cxp wcel vx cC df-rex 3bitr4g vx vy cv cvv cB ccnv vx cv csn
      cima cA vx cv csn cima cxp eliun vx vy cv cC cB ccnv vx cv csn cima cA vx
      cv csn cima cxp eliun 3bitr4g eqrdv syl5eq $.

    $( Class composition distributes over union.  (Contributed by NM,
       21-Dec-2008.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    coundi $p |- ( A o. ( B u. C ) ) = ( ( A o. B ) u. ( A o. C ) ) $=
      vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx vy copab vx cv vz cv
      cC wbr vz cv vy cv cA wbr wa vz wex vx vy copab cun vx cv vz cv cB cC cun
      wbr vz cv vy cv cA wbr wa vz wex vx vy copab cA cB ccom cA cC ccom cun cA
      cB cC cun ccom vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx vy
      copab vx cv vz cv cC wbr vz cv vy cv cA wbr wa vz wex vx vy copab cun vx
      cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx cv vz cv cC wbr vz cv vy
      cv cA wbr wa vz wex wo vx vy copab vx cv vz cv cB cC cun wbr vz cv vy cv
      cA wbr wa vz wex vx vy copab vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz
      wex vx cv vz cv cC wbr vz cv vy cv cA wbr wa vz wex vx vy unopab vx cv vz
      cv cB wbr vz cv vy cv cA wbr wa vz wex vx cv vz cv cC wbr vz cv vy cv cA
      wbr wa vz wex wo vx cv vz cv cB cC cun wbr vz cv vy cv cA wbr wa vz wex
      vx vy vx cv vz cv cB cC cun wbr vz cv vy cv cA wbr wa vz wex vx cv vz cv
      cB wbr vz cv vy cv cA wbr wa vx cv vz cv cC wbr vz cv vy cv cA wbr wa wo
      vz wex vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx cv vz cv cC wbr
      vz cv vy cv cA wbr wa vz wex wo vx cv vz cv cB cC cun wbr vz cv vy cv cA
      wbr wa vx cv vz cv cB wbr vz cv vy cv cA wbr wa vx cv vz cv cC wbr vz cv
      vy cv cA wbr wa wo vz vx cv vz cv cB cC cun wbr vz cv vy cv cA wbr wa vx
      cv vz cv cB wbr vx cv vz cv cC wbr wo vz cv vy cv cA wbr wa vx cv vz cv
      cB wbr vz cv vy cv cA wbr wa vx cv vz cv cC wbr vz cv vy cv cA wbr wa wo
      vx cv vz cv cB cC cun wbr vx cv vz cv cB wbr vx cv vz cv cC wbr wo vz cv
      vy cv cA wbr vx cv vz cv cB cC brun anbi1i vx cv vz cv cB wbr vx cv vz cv
      cC wbr vz cv vy cv cA wbr andir bitri exbii vx cv vz cv cB wbr vz cv vy
      cv cA wbr wa vx cv vz cv cC wbr vz cv vy cv cA wbr wa vz 19.43 bitr2i
      opabbii eqtri cA cB ccom vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex
      vx vy copab cA cC ccom vx cv vz cv cC wbr vz cv vy cv cA wbr wa vz wex vx
      vy copab vx vy vz cA cB df-co vx vy vz cA cC df-co uneq12i vx vy vz cA cB
      cC cun df-co 3eqtr4ri $.

    $( Class composition distributes over union.  (Contributed by NM,
       21-Dec-2008.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    coundir $p |- ( ( A u. B ) o. C ) = ( ( A o. C ) u. ( B o. C ) ) $=
      vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex vx vz copab vx cv vy cv
      cC wbr vy cv vz cv cB wbr wa vy wex vx vz copab cun vx cv vy cv cC wbr vy
      cv vz cv cA cB cun wbr wa vy wex vx vz copab cA cC ccom cB cC ccom cun cA
      cB cun cC ccom vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex vx vz
      copab vx cv vy cv cC wbr vy cv vz cv cB wbr wa vy wex vx vz copab cun vx
      cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex vx cv vy cv cC wbr vy cv vz
      cv cB wbr wa vy wex wo vx vz copab vx cv vy cv cC wbr vy cv vz cv cA cB
      cun wbr wa vy wex vx vz copab vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy
      wex vx cv vy cv cC wbr vy cv vz cv cB wbr wa vy wex vx vz unopab vx cv vy
      cv cC wbr vy cv vz cv cA wbr wa vy wex vx cv vy cv cC wbr vy cv vz cv cB
      wbr wa vy wex wo vx cv vy cv cC wbr vy cv vz cv cA cB cun wbr wa vy wex
      vx vz vx cv vy cv cC wbr vy cv vz cv cA cB cun wbr wa vy wex vx cv vy cv
      cC wbr vy cv vz cv cA wbr wa vx cv vy cv cC wbr vy cv vz cv cB wbr wa wo
      vy wex vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex vx cv vy cv cC wbr
      vy cv vz cv cB wbr wa vy wex wo vx cv vy cv cC wbr vy cv vz cv cA cB cun
      wbr wa vx cv vy cv cC wbr vy cv vz cv cA wbr wa vx cv vy cv cC wbr vy cv
      vz cv cB wbr wa wo vy vx cv vy cv cC wbr vy cv vz cv cA cB cun wbr wa vx
      cv vy cv cC wbr vy cv vz cv cA wbr vy cv vz cv cB wbr wo wa vx cv vy cv
      cC wbr vy cv vz cv cA wbr wa vx cv vy cv cC wbr vy cv vz cv cB wbr wa wo
      vy cv vz cv cA cB cun wbr vy cv vz cv cA wbr vy cv vz cv cB wbr wo vx cv
      vy cv cC wbr vy cv vz cv cA cB brun anbi2i vx cv vy cv cC wbr vy cv vz cv
      cA wbr vy cv vz cv cB wbr andi bitri exbii vx cv vy cv cC wbr vy cv vz cv
      cA wbr wa vx cv vy cv cC wbr vy cv vz cv cB wbr wa vy 19.43 bitr2i
      opabbii eqtri cA cC ccom vx cv vy cv cC wbr vy cv vz cv cA wbr wa vy wex
      vx vz copab cB cC ccom vx cv vy cv cC wbr vy cv vz cv cB wbr wa vy wex vx
      vz copab vx vz vy cA cC df-co vx vz vy cB cC df-co uneq12i vx vz vy cA cB
      cun cC df-co 3eqtr4ri $.

    $( Restricted first member of a class composition.  (Contributed by NM,
       12-Oct-2004.)  (Proof shortened by Andrew Salmon, 27-Aug-2011.) $)
    cores $p |- ( ran B C_ C -> ( ( A |` C ) o. B ) = ( A o. B ) ) $=
      cB crn cC wss vz cv vy cv cB wbr vy cv vx cv cA cC cres wbr wa vy wex vz
      vx copab vz cv vy cv cB wbr vy cv vx cv cA wbr wa vy wex vz vx copab cA
      cC cres cB ccom cA cB ccom cB crn cC wss vz cv vy cv cB wbr vy cv vx cv
      cA cC cres wbr wa vy wex vz cv vy cv cB wbr vy cv vx cv cA wbr wa vy wex
      vz vx cB crn cC wss vz cv vy cv cB wbr vy cv vx cv cA cC cres wbr wa vz
      cv vy cv cB wbr vy cv vx cv cA wbr wa vy cB crn cC wss vz cv vy cv cB wbr
      vy cv vx cv cA cC cres wbr vy cv vx cv cA wbr vz cv vy cv cB wbr vy cv cB
      crn wcel cB crn cC wss vy cv cC wcel vy cv vx cv cA cC cres wbr vy cv vx
      cv cA wbr wb vz cv vy cv cB vz vex vy vex brelrn cB crn cC vy cv ssel vy
      cv vx cv cA cC cres wbr vy cv vx cv cA wbr vy cv cC wcel vy cv vx cv cA
      cC vx vex brres rbaib syl56 pm5.32d exbidv opabbidv vz vx vy cA cC cres
      cB df-co vz vx vy cA cB df-co 3eqtr4g $.

    $( Associative law for the restriction of a composition.  (Contributed by
       NM, 12-Dec-2006.) $)
    resco $p |- ( ( A o. B ) |` C ) = ( A o. ( B |` C ) ) $=
      vx vy cA cB ccom cC cres cA cB cC cres ccom cA cB ccom cC relres cA cB cC
      cres relco vx cv vy cv cA cB ccom wbr vx cv cC wcel wa vx cv vz cv cB cC
      cres wbr vz cv vy cv cA wbr wa vz wex vx cv vy cv cA cB ccom cC cres wbr
      vx cv vy cv cA cB cC cres ccom wbr vx cv vy cv cA cB ccom wbr vx cv cC
      wcel wa vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx cv cC wcel wa
      vx cv vz cv cB wbr vz cv vy cv cA wbr wa vx cv cC wcel wa vz wex vx cv vz
      cv cB cC cres wbr vz cv vy cv cA wbr wa vz wex vx cv vy cv cA cB ccom wbr
      vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx cv cC wcel vz vx cv vy
      cv cA cB vx vex vy vex brco anbi1i vx cv vz cv cB wbr vz cv vy cv cA wbr
      wa vx cv cC wcel vz 19.41v vx cv vz cv cB wbr vz cv vy cv cA wbr wa vx cv
      cC wcel wa vx cv vz cv cB cC cres wbr vz cv vy cv cA wbr wa vz vx cv vz
      cv cB wbr vz cv vy cv cA wbr wa vx cv cC wcel wa vx cv vz cv cB wbr vx cv
      cC wcel wa vz cv vy cv cA wbr wa vx cv vz cv cB cC cres wbr vz cv vy cv
      cA wbr wa vx cv vz cv cB wbr vz cv vy cv cA wbr vx cv cC wcel an32 vx cv
      vz cv cB cC cres wbr vx cv vz cv cB wbr vx cv cC wcel wa vz cv vy cv cA
      wbr vx cv vz cv cB cC vz vex brres anbi1i bitr4i exbii 3bitr2i vx cv vy
      cv cA cB ccom cC vy vex brres vz vx cv vy cv cA cB cC cres vx vex vy vex
      brco 3bitr4i eqbrriv $.

    $( Image of the composition of two classes.  (Contributed by Jason
       Orendorff, 12-Dec-2006.) $)
    imaco $p |- ( ( A o. B ) " C ) = ( A " ( B " C ) ) $=
      vx cA cB ccom cC cima cA cB cC cima cima vy cv vx cv cA wbr vy cB cC cima
      wrex vy cv cB cC cima wcel vy cv vx cv cA wbr wa vy wex vx cv cA cB cC
      cima cima wcel vx cv cA cB ccom cC cima wcel vy cv vx cv cA wbr vy cB cC
      cima df-rex vy vx cv cA cB cC cima vx vex elima vz cv vy cv cB wbr vy cv
      vx cv cA wbr wa vy wex vz cC wrex vz cv vy cv cB wbr vz cC wrex vy cv vx
      cv cA wbr wa vy wex vx cv cA cB ccom cC cima wcel vy cv cB cC cima wcel
      vy cv vx cv cA wbr wa vy wex vz cv vy cv cB wbr vy cv vx cv cA wbr wa vy
      wex vz cC wrex vz cv vy cv cB wbr vy cv vx cv cA wbr wa vz cC wrex vy wex
      vz cv vy cv cB wbr vz cC wrex vy cv vx cv cA wbr wa vy wex vz cv vy cv cB
      wbr vy cv vx cv cA wbr wa vz vy cC rexcom4 vz cv vy cv cB wbr vy cv vx cv
      cA wbr wa vz cC wrex vz cv vy cv cB wbr vz cC wrex vy cv vx cv cA wbr wa
      vy vz cv vy cv cB wbr vy cv vx cv cA wbr vz cC r19.41v exbii bitri vx cv
      cA cB ccom cC cima wcel vz cv vx cv cA cB ccom wbr vz cC wrex vz cv vy cv
      cB wbr vy cv vx cv cA wbr wa vy wex vz cC wrex vz vx cv cA cB ccom cC vx
      vex elima vz cv vx cv cA cB ccom wbr vz cv vy cv cB wbr vy cv vx cv cA
      wbr wa vy wex vz cC vy vz cv vx cv cA cB vz vex vx vex brco rexbii bitri
      vy cv cB cC cima wcel vy cv vx cv cA wbr wa vz cv vy cv cB wbr vz cC wrex
      vy cv vx cv cA wbr wa vy vy cv cB cC cima wcel vz cv vy cv cB wbr vz cC
      wrex vy cv vx cv cA wbr vz vy cv cB cC vy vex elima anbi1i exbii 3bitr4i
      3bitr4ri eqriv $.

    $( The range of the composition of two classes.  (Contributed by NM,
       12-Dec-2006.) $)
    rnco $p |- ran ( A o. B ) = ran ( A |` ran B ) $=
      vy cA cB ccom crn cA cB crn cres crn vx cv vy cv cA cB ccom wbr vx wex vz
      cv vy cv cA cB crn cres wbr vz wex vy cv cA cB ccom crn wcel vy cv cA cB
      crn cres crn wcel vx cv vy cv cA cB ccom wbr vx wex vx cv vz cv cB wbr vz
      cv vy cv cA wbr wa vz wex vx wex vx cv vz cv cB wbr vz cv vy cv cA wbr wa
      vx wex vz wex vz cv vy cv cA cB crn cres wbr vz wex vx cv vy cv cA cB
      ccom wbr vx cv vz cv cB wbr vz cv vy cv cA wbr wa vz wex vx vz vx cv vy
      cv cA cB vx vex vy vex brco exbii vx cv vz cv cB wbr vz cv vy cv cA wbr
      wa vx vz excom vx cv vz cv cB wbr vz cv vy cv cA wbr wa vx wex vz cv vy
      cv cA cB crn cres wbr vz vx cv vz cv cB wbr vz cv vy cv cA wbr wa vx wex
      vz cv vy cv cA wbr vz cv cB crn wcel wa vz cv vy cv cA cB crn cres wbr vx
      cv vz cv cB wbr vx wex vz cv vy cv cA wbr wa vz cv vy cv cA wbr vx cv vz
      cv cB wbr vx wex wa vx cv vz cv cB wbr vz cv vy cv cA wbr wa vx wex vz cv
      vy cv cA wbr vz cv cB crn wcel wa vx cv vz cv cB wbr vx wex vz cv vy cv
      cA wbr ancom vx cv vz cv cB wbr vz cv vy cv cA wbr vx 19.41v vz cv cB crn
      wcel vx cv vz cv cB wbr vx wex vz cv vy cv cA wbr vx vz cv cB vz vex elrn
      anbi2i 3bitr4i vz cv vy cv cA cB crn vy vex brres bitr4i exbii 3bitri vx
      vy cv cA cB ccom vy vex elrn vz vy cv cA cB crn cres vy vex elrn 3bitr4i
      eqriv $.
  $}

  $( The range of the composition of two classes.  (Contributed by NM,
     27-Mar-2008.) $)
  rnco2 $p |- ran ( A o. B ) = ( A " ran B ) $=
    cA cB ccom crn cA cB crn cres crn cA cB crn cima cA cB rnco cA cB crn
    df-ima eqtr4i $.

  $( The domain of a composition.  Exercise 27 of [Enderton] p. 53.
     (Contributed by NM, 4-Feb-2004.) $)
  dmco $p |- dom ( A o. B ) = ( `' B " dom A ) $=
    cA cB ccom cdm cA cB ccom ccnv crn cB ccnv cA ccnv ccom crn cB ccnv cA cdm
    cima cA cB ccom dfdm4 cA cB ccom ccnv cB ccnv cA ccnv ccom cA cB cnvco
    rneqi cB ccnv cA ccnv ccom crn cB ccnv cA ccnv crn cima cB ccnv cA cdm cima
    cB ccnv cA ccnv rnco2 cA cdm cA ccnv crn cB ccnv cA dfdm4 imaeq2i eqtr4i
    3eqtri $.

  ${
    $d w x y z A $.  $d w y z B $.  $d w y z C $.
    $( Composition with an indexed union.  (Contributed by NM, 21-Dec-2008.) $)
    coiun $p |- ( A o. U_ x e. C B ) = U_ x e. C ( A o. B ) $=
      vy vz cA vx cC cB ciun ccom vx cC cA cB ccom ciun cA vx cC cB ciun relco
      vx cC cA cB ccom ciun wrel cA cB ccom wrel vx cC vx cC cA cB ccom reliun
      cA cB ccom wrel vx cv cC wcel cA cB relco a1i mprgbir vy cv vw cv vx cC
      cB ciun wbr vw cv vz cv cA wbr wa vw wex vy cv vw cv cB wbr vw cv vz cv
      cA wbr wa vw wex vx cC wrex vy cv vz cv cop cA vx cC cB ciun ccom wcel vy
      cv vz cv cop vx cC cA cB ccom ciun wcel vy cv vw cv vx cC cB ciun wbr vw
      cv vz cv cA wbr wa vw wex vy cv vw cv cB wbr vw cv vz cv cA wbr wa vx cC
      wrex vw wex vy cv vw cv cB wbr vw cv vz cv cA wbr wa vw wex vx cC wrex vy
      cv vw cv vx cC cB ciun wbr vw cv vz cv cA wbr wa vy cv vw cv cB wbr vw cv
      vz cv cA wbr wa vx cC wrex vw vy cv vw cv vx cC cB ciun wbr vw cv vz cv
      cA wbr wa vy cv vw cv cB wbr vx cC wrex vw cv vz cv cA wbr wa vy cv vw cv
      cB wbr vw cv vz cv cA wbr wa vx cC wrex vy cv vw cv vx cC cB ciun wbr vy
      cv vw cv cB wbr vx cC wrex vw cv vz cv cA wbr vy cv vw cv cop vx cC cB
      ciun wcel vy cv vw cv cop cB wcel vx cC wrex vy cv vw cv vx cC cB ciun
      wbr vy cv vw cv cB wbr vx cC wrex vx vy cv vw cv cop cC cB eliun vy cv vw
      cv vx cC cB ciun df-br vy cv vw cv cB wbr vy cv vw cv cop cB wcel vx cC
      vy cv vw cv cB df-br rexbii 3bitr4i anbi1i vy cv vw cv cB wbr vw cv vz cv
      cA wbr vx cC r19.41v bitr4i exbii vy cv vw cv cB wbr vw cv vz cv cA wbr
      wa vx vw cC rexcom4 bitr4i vw vy cv vz cv cA vx cC cB ciun vy vex vz vex
      opelco vy cv vz cv cop vx cC cA cB ccom ciun wcel vy cv vz cv cop cA cB
      ccom wcel vx cC wrex vy cv vw cv cB wbr vw cv vz cv cA wbr wa vw wex vx
      cC wrex vx vy cv vz cv cop cC cA cB ccom eliun vy cv vz cv cop cA cB ccom
      wcel vy cv vw cv cB wbr vw cv vz cv cA wbr wa vw wex vx cC vw vy cv vz cv
      cA cB vy vex vz vex opelco rexbii bitri 3bitr4i eqrelriiv $.
  $}

  $( A composition is not affected by a double converse of its first argument.
     (Contributed by NM, 8-Oct-2007.) $)
  cocnvcnv1 $p |- ( `' `' A o. B ) = ( A o. B ) $=
    cA ccnv ccnv cB ccom cA cvv cres cB ccom cA cB ccom cA ccnv ccnv cA cvv
    cres cB cA cnvcnv2 coeq1i cB crn cvv wss cA cvv cres cB ccom cA cB ccom
    wceq cB crn ssv cA cB cvv cores ax-mp eqtri $.

  $( A composition is not affected by a double converse of its second
     argument.  (Contributed by NM, 8-Oct-2007.) $)
  cocnvcnv2 $p |- ( A o. `' `' B ) = ( A o. B ) $=
    cA cB ccnv ccnv ccom cA cB cvv cres ccom cA cB ccom cvv cres cA cB ccom cB
    ccnv ccnv cB cvv cres cA cB cnvcnv2 coeq2i cA cB cvv resco cA cB ccom wrel
    cA cB ccom cvv cres cA cB ccom wceq cA cB relco cA cB ccom dfrel3 mpbi
    3eqtr2i $.

  $( Absorption of a reverse (preimage) restriction of the second member of a
     class composition.  (Contributed by NM, 11-Dec-2006.) $)
  cores2 $p |- ( dom A C_ C -> ( A o. `' ( `' B |` C ) ) = ( A o. B ) ) $=
    cA cdm cC wss cA cB ccnv cC cres ccnv ccom ccnv ccnv cA cB ccom ccnv ccnv
    cA cB ccnv cC cres ccnv ccom cA cB ccom cA cdm cC wss cA cB ccnv cC cres
    ccnv ccom ccnv cA cB ccom ccnv cA cdm cC wss cB ccnv cC cres cA ccnv ccom
    cB ccnv cA ccnv ccom cA cB ccnv cC cres ccnv ccom ccnv cA cB ccom ccnv cA
    cdm cC wss cA ccnv crn cC wss cB ccnv cC cres cA ccnv ccom cB ccnv cA ccnv
    ccom wceq cA cdm cA ccnv crn cC cA dfdm4 sseq1i cB ccnv cA ccnv cC cores
    sylbi cA cB ccnv cC cres ccnv ccom ccnv cB ccnv cC cres ccnv ccnv cA ccnv
    ccom cB ccnv cC cres cA ccnv ccom cA cB ccnv cC cres ccnv cnvco cB ccnv cC
    cres cA ccnv cocnvcnv1 eqtri cA cB cnvco 3eqtr4g cnveqd cA cB ccnv cC cres
    ccnv ccom wrel cA cB ccnv cC cres ccnv ccom ccnv ccnv cA cB ccnv cC cres
    ccnv ccom wceq cA cB ccnv cC cres ccnv relco cA cB ccnv cC cres ccnv ccom
    dfrel2 mpbi cA cB ccom wrel cA cB ccom ccnv ccnv cA cB ccom wceq cA cB
    relco cA cB ccom dfrel2 mpbi 3eqtr3g $.

  ${
    $d x y z A $.
    $( Composition with the empty set.  Theorem 20 of [Suppes] p. 63.
       (Contributed by NM, 24-Apr-2004.) $)
    co02 $p |- ( A o. (/) ) = (/) $=
      vx vy cA c0 ccom c0 cA c0 relco rel0 vx cv vy cv cop cA c0 ccom wcel vx
      cv vy cv cop c0 wcel vx cv vy cv cop cA c0 ccom wcel vx cv vz cv c0 wbr
      vz cv vy cv cA wbr wa vz wex vx cv vz cv c0 wbr vz cv vy cv cA wbr wa vz
      vx cv vz cv c0 wbr vz cv vy cv cA wbr vx cv vz cv c0 wbr vx cv vz cv cop
      c0 wcel vx cv vz cv cop noel vx cv vz cv c0 df-br mtbir intnanr nex vz vx
      cv vy cv cA c0 vx vex vy vex opelco mtbir vx cv vy cv cop noel 2false
      eqrelriiv $.

    $( Composition with the empty set.  (Contributed by NM, 24-Apr-2004.) $)
    co01 $p |- ( (/) o. A ) = (/) $=
      c0 ccnv ccnv c0 cA ccom ccnv ccnv c0 c0 cA ccom c0 ccnv c0 cA ccom ccnv
      c0 ccnv c0 c0 cA ccom ccnv cnv0 c0 cA ccom ccnv cA ccnv c0 ccnv ccom cA
      ccnv c0 ccom c0 c0 cA cnvco c0 ccnv c0 cA ccnv cnv0 coeq2i cA ccnv co02
      3eqtri eqtr4i cnveqi c0 wrel c0 ccnv ccnv c0 wceq rel0 c0 dfrel2 mpbi c0
      cA ccom wrel c0 cA ccom ccnv ccnv c0 cA ccom wceq c0 cA relco c0 cA ccom
      dfrel2 mpbi 3eqtr3ri $.

    $( Composition with the identity relation.  Part of Theorem 3.7(i) of
       [Monk1] p. 36.  (Contributed by NM, 22-Apr-2004.) $)
    coi1 $p |- ( Rel A -> ( A o. _I ) = A ) $=
      cA cid ccom wrel cA wrel cA cid ccom cA wceq cA cid relco vx vy cA cid
      ccom cA vx cv vy cv cop cA cid ccom wcel vx cv vy cv cA wbr vx cv vy cv
      cop cA wcel vx cv vy cv cop cA cid ccom wcel vx cv vz cv cid wbr vz cv vy
      cv cA wbr wa vz wex vx cv vy cv cA wbr vz vx cv vy cv cA cid vx vex vy
      vex opelco vx cv vz cv cid wbr vz cv vy cv cA wbr wa vz wex vz cv vx cv
      wceq vz cv vy cv cA wbr wa vz wex vx cv vy cv cA wbr vx cv vz cv cid wbr
      vz cv vy cv cA wbr wa vz cv vx cv wceq vz cv vy cv cA wbr wa vz vx cv vz
      cv cid wbr vz cv vx cv wceq vz cv vy cv cA wbr vx cv vz cv cid wbr vx cv
      vz cv wceq vz cv vx cv wceq vx cv vz cv vz vex ideq vx vz equcom bitri
      anbi1i exbii vz cv vy cv cA wbr vx cv vy cv cA wbr vz vx cv vx vex vz cv
      vx cv vy cv cA breq1 ceqsexv bitri bitri vx cv vy cv cA df-br bitri
      eqrelriv mpan $.

    $( Composition with the identity relation.  Part of Theorem 3.7(i) of
       [Monk1] p. 36.  (Contributed by NM, 22-Apr-2004.) $)
    coi2 $p |- ( Rel A -> ( _I o. A ) = A ) $=
      cA wrel cid ccnv cA ccnv ccnv ccom cA ccnv ccnv cid cA ccom cA cA ccnv
      cid ccom ccnv cid ccnv cA ccnv ccnv ccom cA ccnv ccnv cA ccnv cid cnvco
      cA ccnv cid ccom cA ccnv cA ccnv wrel cA ccnv cid ccom cA ccnv wceq cA
      relcnv cA ccnv coi1 ax-mp cnveqi eqtr3i cA wrel cA ccnv ccnv cA wceq cid
      ccnv cA ccnv ccnv ccom cid cA ccom wceq cA dfrel2 cA ccnv ccnv cA wceq
      cid ccnv cid wceq cid ccnv cA ccnv ccnv ccom cid cA ccom wceq cnvi cA
      ccnv ccnv cA wceq cid ccnv cid wceq cid ccnv cA ccnv ccnv ccom cid ccnv
      cA ccom cid cA ccom cA ccnv ccnv cA cid ccnv coeq2 cid ccnv cid cA coeq1
      sylan9eq mpan2 sylbi cA wrel cA ccnv ccnv cA wceq cA dfrel2 biimpi
      3eqtr3a $.
  $}

  $( Composition with a restricted identity relation.  (Contributed by FL,
     19-Jun-2011.)  (Revised by Stefan O'Rear, 7-Mar-2015.) $)
  coires1 $p |- ( A o. ( _I |` B ) ) = ( A |` B ) $=
    cA ccnv ccnv cB cres cA cid cB cres ccom cA cB cres cA cid ccom cB cres cA
    ccnv ccnv cB cres cA cid cB cres ccom cA cid ccom cA ccnv ccnv cB cA ccnv
    ccnv cid ccom cA cid ccom cA ccnv ccnv cA cid cocnvcnv1 cA ccnv ccnv wrel
    cA ccnv ccnv cid ccom cA ccnv ccnv wceq cA ccnv relcnv cA ccnv ccnv coi1
    ax-mp eqtr3i reseq1i cA cid cB resco eqtr3i cA cB rescnvcnv eqtr3i $.

  ${
    $d x y z w A $.  $d x y z w B $.  $d x y z w C $.
    $( Associative law for class composition.  Theorem 27 of [Suppes] p. 64.
       Also Exercise 21 of [Enderton] p. 53.  Interestingly, this law holds for
       any classes whatsoever, not just functions or even relations.
       (Contributed by NM, 27-Jan-1997.) $)
    coass $p |- ( ( A o. B ) o. C ) = ( A o. ( B o. C ) ) $=
      vx vy cA cB ccom cC ccom cA cB cC ccom ccom cA cB ccom cC relco cA cB cC
      ccom relco vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy cv cA wbr wa wa
      vw wex vz wex vx cv vz cv cC wbr vz cv vw cv cB wbr wa vw cv vy cv cA wbr
      wa vz wex vw wex vx cv vy cv cop cA cB ccom cC ccom wcel vx cv vy cv cop
      cA cB cC ccom ccom wcel vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy cv
      cA wbr wa wa vw wex vz wex vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy
      cv cA wbr wa wa vz wex vw wex vx cv vz cv cC wbr vz cv vw cv cB wbr wa vw
      cv vy cv cA wbr wa vz wex vw wex vx cv vz cv cC wbr vz cv vw cv cB wbr vw
      cv vy cv cA wbr wa wa vz vw excom vx cv vz cv cC wbr vz cv vw cv cB wbr
      wa vw cv vy cv cA wbr wa vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy
      cv cA wbr wa wa vw vz vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy cv
      cA wbr anass 2exbii bitr4i vx cv vz cv cC wbr vz cv vy cv cA cB ccom wbr
      wa vz wex vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy cv cA wbr wa vw
      wex wa vz wex vx cv vy cv cop cA cB ccom cC ccom wcel vx cv vz cv cC wbr
      vz cv vw cv cB wbr vw cv vy cv cA wbr wa wa vw wex vz wex vx cv vz cv cC
      wbr vz cv vy cv cA cB ccom wbr wa vx cv vz cv cC wbr vz cv vw cv cB wbr
      vw cv vy cv cA wbr wa vw wex wa vz vz cv vy cv cA cB ccom wbr vz cv vw cv
      cB wbr vw cv vy cv cA wbr wa vw wex vx cv vz cv cC wbr vw vz cv vy cv cA
      cB vz vex vy vex brco anbi2i exbii vz vx cv vy cv cA cB ccom cC vx vex vy
      vex opelco vx cv vz cv cC wbr vz cv vw cv cB wbr vw cv vy cv cA wbr wa vz
      vw exdistr 3bitr4i vx cv vw cv cB cC ccom wbr vw cv vy cv cA wbr wa vw
      wex vx cv vz cv cC wbr vz cv vw cv cB wbr wa vz wex vw cv vy cv cA wbr wa
      vw wex vx cv vy cv cop cA cB cC ccom ccom wcel vx cv vz cv cC wbr vz cv
      vw cv cB wbr wa vw cv vy cv cA wbr wa vz wex vw wex vx cv vw cv cB cC
      ccom wbr vw cv vy cv cA wbr wa vx cv vz cv cC wbr vz cv vw cv cB wbr wa
      vz wex vw cv vy cv cA wbr wa vw vx cv vw cv cB cC ccom wbr vx cv vz cv cC
      wbr vz cv vw cv cB wbr wa vz wex vw cv vy cv cA wbr vz vx cv vw cv cB cC
      vx vex vw vex brco anbi1i exbii vw vx cv vy cv cA cB cC ccom vx vex vy
      vex opelco vx cv vz cv cC wbr vz cv vw cv cB wbr wa vw cv vy cv cA wbr wa
      vz wex vx cv vz cv cC wbr vz cv vw cv cB wbr wa vz wex vw cv vy cv cA wbr
      wa vw vx cv vz cv cC wbr vz cv vw cv cB wbr wa vw cv vy cv cA wbr vz
      19.41v exbii 3bitr4i 3bitr4i eqrelriiv $.
  $}

  $( A relation is transitive iff its converse is transitive.  (Contributed by
     FL, 19-Sep-2011.) $)
  relcnvtr $p |- ( Rel R ->
     ( ( R o. R ) C_ R <-> ( `' R o. `' R ) C_ `' R ) ) $=
    cR wrel cR cR ccom cR wss cR ccnv cR ccnv ccom cR ccnv wss cR cR ccom cR
    wss cR ccnv cR ccnv ccom cR cR ccom ccnv cR ccnv cR cR cnvco cR cR ccom cR
    cnvss syl5eqssr cR ccnv cR ccnv ccom cR ccnv wss cR wrel cR cR ccom cR wss
    cR ccnv cR ccnv ccom ccnv cR ccnv ccnv cR ccnv ccnv ccom wceq cR ccnv cR
    ccnv ccom cR ccnv wss cR ccnv cR ccnv ccom ccnv cR ccnv ccnv wss cR wrel cR
    cR ccom cR wss wi cR ccnv cR ccnv cnvco cR ccnv cR ccnv ccom cR ccnv cnvss
    cR ccnv cR ccnv ccom ccnv cR ccnv ccnv cR ccnv ccnv ccom wceq cR ccnv cR
    ccnv ccom ccnv cR ccnv ccnv wss cR ccnv ccnv cR ccnv ccnv ccom cR ccnv ccnv
    wss cR wrel cR cR ccom cR wss wi cR ccnv cR ccnv ccom ccnv cR ccnv ccnv cR
    ccnv ccnv ccom cR ccnv ccnv sseq1 cR wrel cR ccnv ccnv cR ccnv ccnv ccom cR
    ccnv ccnv wss cR cR ccom cR wss cR wrel cR ccnv ccnv cR wceq cR ccnv ccnv
    cR ccnv ccnv ccom cR ccnv ccnv wss cR cR ccom cR wss wi cR dfrel2 cR ccnv
    ccnv cR wceq cR ccnv ccnv cR ccnv ccnv ccom cR ccnv ccnv wss cR cR ccom cR
    wss cR ccnv ccnv cR wceq cR ccnv ccnv cR ccnv ccnv ccom cR cR ccom cR ccnv
    ccnv cR cR ccnv ccnv cR wceq cR ccnv ccnv cR ccnv ccnv ccom cR cR ccnv ccnv
    ccom cR cR ccom cR ccnv ccnv cR cR ccnv ccnv coeq1 cR ccnv ccnv cR cR coeq2
    eqtrd cR ccnv ccnv cR wceq id sseq12d biimpd sylbi com12 syl6bi mpsyl com12
    impbid2 $.

  ${
    $d x y A $.
    $( A relation is included in the cross product of its domain and range.
       Exercise 4.12(t) of [Mendelson] p. 235.  (Contributed by NM,
       3-Aug-1994.) $)
    relssdmrn $p |- ( Rel A -> A C_ ( dom A X. ran A ) ) $=
      cA wrel vx vy cA cA cdm cA crn cxp cA wrel id vx cv vy cv cop cA wcel vx
      cv vy cv cop cA cdm cA crn cxp wcel wi cA wrel vx cv vy cv cop cA wcel vx
      cv vy cv cop cA wcel vy wex vx cv vy cv cop cA wcel vx wex vx cv vy cv
      cop cA cdm cA crn cxp wcel vx cv vy cv cop cA wcel vy 19.8a vx cv vy cv
      cop cA wcel vx 19.8a vx cv vy cv cop cA cdm cA crn cxp wcel vx cv cA cdm
      wcel vy cv cA crn wcel wa vx cv vy cv cop cA wcel vy wex vx cv vy cv cop
      cA wcel vx wex wa vx cv vy cv cA cdm cA crn opelxp vx cv cA cdm wcel vx
      cv vy cv cop cA wcel vy wex vy cv cA crn wcel vx cv vy cv cop cA wcel vx
      wex vy vx cv cA vx vex eldm2 vx vy cv cA vy vex elrn2 anbi12i bitri
      sylanbrc a1i relssdv $.
  $}

  $( The converse is a subset of the cartesian product of range and domain.
     (Contributed by Mario Carneiro, 2-Jan-2017.) $)
  cnvssrndm $p |- `' A C_ ( ran A X. dom A ) $=
    cA ccnv cA ccnv cdm cA ccnv crn cxp cA crn cA cdm cxp cA ccnv wrel cA ccnv
    cA ccnv cdm cA ccnv crn cxp wss cA relcnv cA ccnv relssdmrn ax-mp cA crn cA
    ccnv cdm cA cdm cA ccnv crn cA df-rn cA dfdm4 xpeq12i sseqtr4i $.

  $( Composition as a subset of the cross product of factors.  (Contributed by
     Mario Carneiro, 12-Jan-2017.) $)
  cossxp $p |- ( A o. B ) C_ ( dom B X. ran A ) $=
    cA cB ccom cA cB ccom cdm cA cB ccom crn cxp cB cdm cA crn cxp cA cB ccom
    wrel cA cB ccom cA cB ccom cdm cA cB ccom crn cxp wss cA cB relco cA cB
    ccom relssdmrn ax-mp cA cB ccom cdm cB cdm wss cA cB ccom crn cA crn wss cA
    cB ccom cdm cA cB ccom crn cxp cB cdm cA crn cxp wss cA cB dmcoss cA cB
    rncoss cA cB ccom cdm cB cdm cA cB ccom crn cA crn xpss12 mp2an sstri $.

  $( Two ways to describe the structure of a two-place operation.  (Contributed
     by NM, 17-Dec-2008.) $)
  relrelss $p |- ( ( Rel A /\ Rel dom A ) <-> A C_ ( ( _V X. _V ) X. _V ) ) $=
    cA wrel cA cdm wrel wa cA wrel cA cdm cvv cvv cxp wss wa cA cvv cvv cxp cvv
    cxp wss cA cdm wrel cA cdm cvv cvv cxp wss cA wrel cA cdm df-rel anbi2i cA
    wrel cA cdm cvv cvv cxp wss wa cA cvv cvv cxp cvv cxp wss cA wrel cA cdm
    cvv cvv cxp wss cA cA cdm cA crn cxp cvv cvv cxp cvv cxp cA relssdmrn cA
    cdm cvv cvv cxp wss cA crn cvv wss cA cdm cA crn cxp cvv cvv cxp cvv cxp
    wss cA crn ssv cA cdm cvv cvv cxp cA crn cvv xpss12 mpan2 sylan9ss cA cvv
    cvv cxp cvv cxp wss cA wrel cA cdm cvv cvv cxp wss cA cvv cvv cxp cvv cxp
    wss cA cvv cvv cxp wss cA wrel cA cvv cvv cxp cvv cxp wss cvv cvv cxp cvv
    cxp cvv cvv cxp wss cA cvv cvv cxp wss cvv cvv cxp cvv xpss cA cvv cvv cxp
    cvv cxp cvv cvv cxp sstr mpan2 cA df-rel sylibr cA cvv cvv cxp cvv cxp wss
    cA cdm cvv cvv cxp cvv cxp cdm cvv cvv cxp cA cvv cvv cxp cvv cxp dmss cvv
    c0 wne cvv cvv cxp cvv cxp cdm cvv cvv cxp wceq vn0 cvv cvv cxp cvv dmxp
    ax-mp syl6sseq jca impbii bitri $.

  ${
    $d x y A $.  $d x y R $.
    $( The membership relation for a relation is inherited by class union.
       (Contributed by NM, 17-Sep-2006.) $)
    unielrel $p |- ( ( Rel R /\ A e. R ) -> U. A e. U. R ) $=
      cR wrel cA cR wcel wa cA vx cv vy cv cop wceq vy wex vx wex cA cR wcel cA
      cuni cR cuni wcel vx vy cA cR elrel cR wrel cA cR wcel simpr cA vx cv vy
      cv cop wceq cA cR wcel cA cuni cR cuni wcel wi vx vy cA vx cv vy cv cop
      wceq vx cv vy cv cop cR wcel vx cv vy cv cop cuni cR cuni wcel cA cR wcel
      cA cuni cR cuni wcel vx cv vy cv cop cR wcel vx cv vy cv cop cuni cR cuni
      wcel wi cA vx cv vy cv cop wceq vx cv vy cv cR vx vex vy vex uniopel a1i
      cA vx cv vy cv cop cR eleq1 cA vx cv vy cv cop wceq cA cuni vx cv vy cv
      cop cuni cR cuni cA vx cv vy cv cop unieq eleq1d 3imtr4d exlimivv sylc $.
  $}

  $( The double union of a relation is its field.  (Contributed by NM,
     17-Sep-2006.) $)
  relfld $p |- ( Rel R -> U. U. R = ( dom R u. ran R ) ) $=
    cR wrel cR cuni cuni cR cdm cR crn cun cR wrel cR cuni cuni cR cdm cR crn
    cxp cuni cuni cR cdm cR crn cun cR wrel cR cR cdm cR crn cxp wss cR cuni cR
    cdm cR crn cxp cuni wss cR cuni cuni cR cdm cR crn cxp cuni cuni wss cR
    relssdmrn cR cR cdm cR crn cxp uniss cR cuni cR cdm cR crn cxp cuni uniss
    3syl cR cdm cR crn unixpss syl6ss cR cdm cR crn cun cR cuni cuni wss cR
    wrel cR dmrnssfld a1i eqssd $.

  $( Restriction of a relation to its field.  (Contributed by FL,
     15-Apr-2012.) $)
  relresfld $p |- ( Rel R -> ( R |` U. U. R ) = R ) $=
    cR wrel cR cR cuni cuni cres cR wceq cR wrel cR cR cuni cuni cres cR cR cdm
    cR crn cun cres wceq cR cR cdm cR crn cun cres cR cR cdm cres cR cR crn
    cres cun wceq cR wrel cR cR cuni cuni cres cR wceq wi cR wrel cR cuni cuni
    cR cdm cR crn cun cR cR relfld reseq2d cR cR cdm cR crn resundi cR cR cuni
    cuni cres cR cR cdm cR crn cun cres wceq cR cR cdm cR crn cun cres cR cR
    cdm cres cR cR crn cres cun wceq wa cR cR cuni cuni cres cR cR cdm cres cR
    cR crn cres cun wceq cR wrel cR cR cuni cuni cres cR wceq cR cR cuni cuni
    cres cR cR cdm cR crn cun cres cR cR cdm cres cR cR crn cres cun eqtr cR cR
    crn cres cR wss cR wrel cR cR cdm cres cR wceq cR cR cuni cuni cres cR cR
    cdm cres cR cR crn cres cun wceq cR cR cuni cuni cres cR wceq wi cR cR crn
    resss cR resdm cR cR crn cres cR wss cR cR cR crn cres cun cR wceq cR cR
    cdm cres cR wceq cR cR cuni cuni cres cR cR cdm cres cR cR crn cres cun
    wceq cR cR cuni cuni cres cR wceq wi wi cR cR crn cres cR ssequn2 cR cR cdm
    cres cR wceq cR cR cuni cuni cres cR cR cdm cres cR cR crn cres cun wceq cR
    cR cR crn cres cun cR wceq cR cR cuni cuni cres cR wceq cR cR cdm cres cR
    wceq cR cR cuni cuni cres cR cR cdm cres cR cR crn cres cun wceq cR cR cuni
    cuni cres cR cR cR crn cres cun wceq cR cR cR crn cres cun cR wceq cR cR
    cuni cuni cres cR wceq wi cR cR cdm cres cR wceq cR cR cdm cres cR cR crn
    cres cun cR cR cR crn cres cun cR cR cuni cuni cres cR cR cdm cres cR cR cR
    crn cres uneq1 eqeq2d cR cR cuni cuni cres cR cR cR crn cres cun wceq cR cR
    cR crn cres cun cR wceq cR cR cuni cuni cres cR wceq cR cR cuni cuni cres
    cR cR cR crn cres cun cR eqtr ex syl6bi com3r sylbi mpsyl syl5com sylancl
    pm2.43i $.

  $( Composition with the identity relation restricted to a relation's field.
     (Contributed by FL, 2-May-2011.) $)
  relcoi2 $p |- ( Rel R -> ( ( _I |` U. U. R ) o. R ) = R ) $=
    cR wrel cid cR cuni cuni cres cR ccom cid cR ccom cR cR crn cR cuni cuni
    wss cid cR cuni cuni cres cR ccom cid cR ccom wceq cR wrel cR cdm cR crn
    cun cR cuni cuni wss cR crn cR cuni cuni wss cR dmrnssfld cR cdm cR crn cun
    cR cuni cuni wss cR cdm cR cuni cuni wss cR crn cR cuni cuni wss wa cR crn
    cR cuni cuni wss cR cdm cR crn cR cuni cuni unss cR cdm cR cuni cuni wss cR
    crn cR cuni cuni wss simpr sylbir ax-mp cid cR cR cuni cuni cores mp1i cR
    coi2 eqtrd $.

  $( Composition with the identity relation restricted to a relation's field.
     (Contributed by FL, 8-May-2011.) $)
  relcoi1 $p |- ( Rel R -> ( R o. ( _I |` U. U. R ) ) = R ) $=
    cR wrel cR cid cR cuni cuni cres ccom cR cid ccom cR cR cuni cuni cR cdm cR
    crn cun wceq cR wrel cR cid cR cuni cuni cres ccom cR cid ccom wceq cR
    relfld cR wrel cR cid cR cuni cuni cres ccom cR cid ccom wceq cR cuni cuni
    cR cdm cR crn cun wceq cR cid cR cdm cR crn cun cres ccom cR cid ccom wceq
    cid cR cdm cR crn cun cres cid cR cdm cres cid cR crn cres cun wceq cR cid
    cR cdm cR crn cun cres ccom cR cid cR cdm cres cid cR crn cres cun ccom
    wceq cR wrel cR cid cR cdm cR crn cun cres ccom cR cid ccom wceq wi cid cR
    cdm cR crn resundi cid cR cdm cR crn cun cres cid cR cdm cres cid cR crn
    cres cun cR coeq2 cR wrel cR cid cR cdm cR crn cun cres ccom cR cid ccom
    wceq cR cid cR cdm cR crn cun cres ccom cR cid cR cdm cres cid cR crn cres
    cun ccom wceq cR cid cR cdm cres cid cR crn cres cun ccom cR cid ccom wceq
    cR wrel cR cid cR cdm cres cid cR crn cres cun ccom cR cid cR cdm cres ccom
    cR cid cR crn cres ccom cun cR cid ccom cR cid cR cdm cres cid cR crn cres
    coundi cR wrel cR cid ccom cR cdm cres cR cid cR cdm cres ccom wceq cR cid
    cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq cR cid cR cdm
    resco cR cid ccom cR wceq cR wrel cR cid ccom cR cdm cres cR cid cR cdm
    cres ccom wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid
    ccom wceq wi cR coi1 cR cid ccom cR wceq cR cid ccom cR cdm cres cR cR cdm
    cres wceq cR wrel cR cid ccom cR cdm cres cR cid cR cdm cres ccom wceq cR
    cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi cR cid
    ccom cR cR cdm reseq1 cR cR cdm cres cR wceq cR wrel cR cid ccom cR cdm
    cres cR cR cdm cres wceq cR cid ccom cR cdm cres cR cid cR cdm cres ccom
    wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq
    wi wi cR resdm cR cid ccom cR cdm cres cR cR cdm cres wceq cR cR cdm cres
    cR wceq cR wrel cR cid ccom cR cdm cres cR cid cR cdm cres ccom wceq cR cid
    cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi cR cid
    ccom cR cdm cres cR cR cdm cres wceq cR cR cdm cres cR wceq cR wrel cR cid
    ccom cR cdm cres cR cid cR cdm cres ccom wceq cR cid cR cdm cres ccom cR
    cid cR crn cres ccom cun cR cid ccom wceq wi wi cR cid ccom cR cdm cres cR
    cR cdm cres wceq cR cR cdm cres cR wceq wa cR cid ccom cR cdm cres cR wceq
    cR wrel cR cid ccom cR cdm cres cR cid cR cdm cres ccom wceq cR cid cR cdm
    cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi wi cR cid ccom cR
    cdm cres cR cR cdm cres cR eqtr cR cid ccom cR cdm cres cR cid cR cdm cres
    ccom wceq cR cid ccom cR cdm cres cR wceq cR wrel cR cid cR cdm cres ccom
    cR cid cR crn cres ccom cun cR cid ccom wceq cR cid ccom cR cdm cres cR
    wceq cR wrel cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid
    ccom wceq wi wi cR cid cR cdm cres ccom cR cid ccom cR cdm cres cR cid cR
    cdm cres ccom cR cid ccom cR cdm cres wceq cR cid ccom cR cdm cres cR wceq
    cR wrel cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom
    wceq wi cR cid cR cdm cres ccom cR cid ccom cR cdm cres wceq cR cid ccom cR
    cdm cres cR wceq wa cR cid cR cdm cres ccom cR wceq cR wrel cR cid cR cdm
    cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi cR cid cR cdm
    cres ccom cR cid ccom cR cdm cres cR eqtr cR cid ccom cR crn cres cR cid cR
    crn cres ccom wceq cR cid cR cdm cres ccom cR wceq cR cid cR cdm cres ccom
    cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun wceq cR wrel cR
    cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi cR cid
    cR crn resco cR cid cR cdm cres ccom cR cR cid cR crn cres ccom uneq1 cR
    wrel cR cid ccom cR crn cres cR cid cR crn cres ccom wceq cR cid cR cdm
    cres ccom cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun wceq
    cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq cR cid
    ccom cR wceq cR wrel cR cid ccom cR crn cres cR cid cR crn cres ccom wceq
    cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cR cid cR crn cres
    ccom cun wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid
    ccom wceq wi wi cR coi1 cR cid ccom cR wceq cR cid ccom cR crn cres cR cR
    crn cres wceq cR wrel cR cid ccom cR crn cres cR cid cR crn cres ccom wceq
    cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cR cid cR crn cres
    ccom cun wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid
    ccom wceq wi wi wi cR cid ccom cR cR crn reseq1 cR cid ccom cR crn cres cR
    cid cR crn cres ccom wceq cR cid ccom cR crn cres cR cR crn cres wceq cR
    wrel cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cR cid cR crn
    cres ccom cun wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR
    cid ccom wceq wi cR cid ccom cR crn cres cR cR crn cres wceq cR wrel cR cid
    cR cdm cres ccom cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun
    wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq
    wi wi wi cR cid cR crn cres ccom cR cid ccom cR crn cres cR cid cR crn cres
    ccom cR cid ccom cR crn cres wceq cR cid ccom cR crn cres cR cR crn cres
    wceq cR wrel cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cR cid
    cR crn cres ccom cun wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom
    cun cR cid ccom wceq wi wi cR cid cR crn cres ccom cR cid ccom cR crn cres
    wceq cR cid ccom cR crn cres cR cR crn cres wceq wa cR cR cid cR crn cres
    ccom cun cR cR cR crn cres cun wceq cR wrel cR cid cR cdm cres ccom cR cid
    cR crn cres ccom cun cR cR cid cR crn cres ccom cun wceq cR cid cR cdm cres
    ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi wi cR cid cR crn cres
    ccom cR cid ccom cR crn cres wceq cR cid ccom cR crn cres cR cR crn cres
    wceq wa cR cid cR crn cres ccom cR cR crn cres cR cR cid cR crn cres ccom
    cR cid ccom cR crn cres cR cR crn cres eqtr uneq2d cR cid cR cdm cres ccom
    cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun wceq cR cR cid
    cR crn cres ccom cun cR cR cR crn cres cun wceq cR wrel cR cid cR cdm cres
    ccom cR cid cR crn cres ccom cun cR cid ccom wceq cR cid cR cdm cres ccom
    cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun wceq cR cR cid
    cR crn cres ccom cun cR cR cR crn cres cun wceq cR wrel cR cid cR cdm cres
    ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi cR cid cR cdm cres
    ccom cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun wceq cR cR
    cid cR crn cres ccom cun cR cR cR crn cres cun wceq wa cR cid cR cdm cres
    ccom cR cid cR crn cres ccom cun cR cR cR crn cres cun wceq cR wrel cR cid
    cR cdm cres ccom cR cid cR crn cres ccom cun cR cid ccom wceq wi cR cid cR
    cdm cres ccom cR cid cR crn cres ccom cun cR cR cid cR crn cres ccom cun cR
    cR cR crn cres cun eqtr cR wrel cR cid cR cdm cres ccom cR cid cR crn cres
    ccom cun cR cid ccom wceq cR cid cR cdm cres ccom cR cid cR crn cres ccom
    cun cR cR cR crn cres cun wceq cR cR cR crn cres cun cR cid ccom wceq cR
    wrel cR cid ccom cR cR cR cR crn cres cun cR coi1 cR cR crn cres cR wss cR
    cR cR crn cres cun cR wceq cR cR crn resss cR cR crn cres cR ssequn2 mpbi
    syl6reqr cR cid cR cdm cres ccom cR cid cR crn cres ccom cun cR cR cR crn
    cres cun cR cid ccom eqeq1 syl5ibr syl ex com3l syl ex eqcoms com3l syl
    mpcom com3l mpsyl syl ex eqcoms com3l syl ex com3l mpcom syl5com mpcom mpi
    syl5eq cR cid cR cdm cR crn cun cres ccom cR cid cR cdm cres cid cR crn
    cres cun ccom cR cid ccom eqeq1 syl5ibr mp2b cR cuni cuni cR cdm cR crn cun
    wceq cR cid cR cuni cuni cres ccom cR cid cR cdm cR crn cun cres ccom cR
    cid ccom cR cuni cuni cR cdm cR crn cun wceq cid cR cuni cuni cres cid cR
    cdm cR crn cun cres cR cR cuni cuni cR cdm cR crn cun cid reseq2 coeq2d
    eqeq1d syl5ibr mpcom cR coi1 eqtrd $.

  $( The double union of the converse of a class is its field.  (Contributed by
     NM, 4-Jun-2008.) $)
  unidmrn $p |- U. U. `' A = ( dom A u. ran A ) $=
    cA ccnv cuni cuni cA ccnv crn cA ccnv cdm cun cA cdm cA crn cun cA ccnv
    cuni cuni cA ccnv cdm cA ccnv crn cA ccnv wrel cA ccnv cuni cuni cA ccnv
    cdm cA ccnv crn cun wceq cA relcnv cA ccnv relfld ax-mp equncomi cA cdm cA
    ccnv crn cA crn cA ccnv cdm cA dfdm4 cA df-rn uneq12i eqtr4i $.

  $( if ` R ` is a relation, its double union equals the double union of its
     converse.  (Contributed by FL, 5-Jan-2009.) $)
  relcnvfld $p |- ( Rel R -> U. U. R = U. U. `' R ) $=
    cR wrel cR cuni cuni cR cdm cR crn cun cR ccnv cuni cuni cR relfld cR
    unidmrn syl6eqr $.

  $( Alternate definition of domain ~ df-dm that doesn't require dummy
     variables.  (Contributed by NM, 2-Aug-2010.) $)
  dfdm2 $p |- dom A = U. U. ( `' A o. A ) $=
    cA ccnv cA ccom cuni cuni cA ccnv cA ccom cdm cA ccnv cA ccom crn cun cA
    cdm cA cdm cun cA cdm cA ccnv cA ccom ccnv cuni cuni cA ccnv cA ccom cuni
    cuni cA ccnv cA ccom cdm cA ccnv cA ccom crn cun cA ccnv cA ccom ccnv cuni
    cA ccnv cA ccom cuni cA ccnv cA ccom ccnv cA ccnv cA ccom cA ccnv cA ccom
    ccnv cA ccnv cA ccnv ccnv ccom cA ccnv cA ccom cA ccnv cA cnvco cA ccnv cA
    cocnvcnv2 eqtri unieqi unieqi cA ccnv cA ccom unidmrn eqtr3i cA ccnv cA
    ccom cdm cA cdm cA ccnv cA ccom crn cA cdm cA ccnv cdm cA crn wceq cA ccnv
    cA ccom cdm cA cdm wceq cA crn cA ccnv cdm cA df-rn eqcomi cA ccnv cA
    dmcoeq ax-mp cA ccnv cA ccom crn cA ccnv crn cA cdm cA ccnv cdm cA crn wceq
    cA ccnv cA ccom crn cA ccnv crn wceq cA crn cA ccnv cdm cA df-rn eqcomi cA
    ccnv cA rncoeq ax-mp cA dfdm4 eqtr4i uneq12i cA cdm unidm 3eqtrri $.

  $( The double class union of a non-empty cross product is the union of it
     members.  (Contributed by NM, 17-Sep-2006.) $)
  unixp $p |- ( ( A X. B ) =/= (/) -> U. U. ( A X. B ) = ( A u. B ) ) $=
    cA cB cxp c0 wne cA cB cxp cuni cuni cA cB cxp cdm cA cB cxp crn cun cA cB
    cun cA cB cxp wrel cA cB cxp cuni cuni cA cB cxp cdm cA cB cxp crn cun wceq
    cA cB relxp cA cB cxp relfld ax-mp cA cB cxp c0 wne cB c0 wne cA c0 wne cA
    cB cxp cdm cA cB cxp crn cun cA cB cun wceq cB c0 cA cB cxp c0 cB c0 wceq
    cA cB cxp cA c0 cxp c0 cB c0 cA xpeq2 cA xp0 syl6eq necon3i cA c0 cA cB cxp
    c0 cA c0 wceq cA cB cxp c0 cB cxp c0 cA c0 cB xpeq1 cB xp0r syl6eq necon3i
    cB c0 wne cA cB cxp cdm cA wceq cA cB cxp crn cB wceq cA cB cxp cdm cA cB
    cxp crn cun cA cB cun wceq cA c0 wne cA cB dmxp cA cB rnxp cA cB cxp cdm cA
    cA cB cxp crn cB uneq12 syl2an syl2anc syl5eq $.

  ${
    $d x y z A $.  $d x y z B $.
    $( A cross product is empty iff its union is empty.  (Contributed by NM,
       20-Sep-2006.) $)
    unixp0 $p |- ( ( A X. B ) = (/) <-> U. ( A X. B ) = (/) ) $=
      cA cB cxp c0 wceq cA cB cxp cuni c0 wceq cA cB cxp c0 wceq cA cB cxp cuni
      c0 cuni c0 cA cB cxp c0 unieq uni0 syl6eq cA cB cxp c0 cA cB cxp cuni c0
      cA cB cxp c0 wne vz cv cA cB cxp wcel vz wex cA cB cxp cuni c0 wne vz cA
      cB cxp n0 vz cv cA cB cxp wcel cA cB cxp cuni c0 wne vz vz cv cA cB cxp
      wcel vx cv vy cv cop vz cv wceq vx cv vy cv cop cA cB cxp wcel wa vy wex
      vx wex cA cB cxp cuni c0 wne vx vy vz cv cA cB elxp3 vx cv vy cv cop vz
      cv wceq vx cv vy cv cop cA cB cxp wcel wa cA cB cxp cuni c0 wne vx vy vx
      cv vy cv cop cA cB cxp wcel cA cB cxp cuni c0 wne vx cv vy cv cop vz cv
      wceq vx cv vy cv cop cA cB cxp wcel vx cv vy cv cop cA cB cxp cuni wss vx
      cv vy cv cop c0 wne cA cB cxp cuni c0 wne vx cv vy cv cop cA cB cxp
      elssuni vx cv vy cv vx vex vy vex opnzi vx cv vy cv cop cA cB cxp cuni
      ssn0 sylancl adantl exlimivv sylbi exlimiv sylbi necon4i impbii $.
  $}

  $( Field of a square cross product.  (Contributed by FL, 10-Oct-2009.) $)
  unixpid $p |- U. U. ( A X. A ) = A $=
    cA c0 wceq cA cA cxp cuni cuni cA wceq cA cA cxp c0 wceq cA c0 wceq cA cA
    cxp cuni cuni cA wceq cA c0 wceq cA cA cxp c0 cA cxp c0 cA c0 cA xpeq1 cA
    xp0r syl6eq cA cA cxp c0 wceq cA cA cxp cuni cuni c0 cuni cuni wceq c0 cuni
    cuni c0 wceq cA c0 wceq cA cA cxp cuni cuni cA wceq wi cA cA cxp c0 wceq cA
    cA cxp cuni c0 cuni cA cA cxp c0 unieq unieqd c0 cuni cuni c0 cuni c0 c0
    cuni c0 uni0 unieqi uni0 eqtri cA cA cxp cuni cuni c0 cuni cuni wceq c0
    cuni cuni c0 wceq wa cA cA cxp cuni cuni c0 wceq cA c0 wceq cA cA cxp cuni
    cuni cA wceq cA cA cxp cuni cuni c0 cuni cuni c0 eqtr cA cA cxp cuni cuni
    c0 wceq cA cA cxp cuni cuni cA wceq wi c0 cA cA cA cxp cuni cuni c0 wceq c0
    cA wceq cA cA cxp cuni cuni cA wceq cA cA cxp cuni cuni c0 cA eqtr expcom
    eqcoms syl5com sylancl mpcom cA c0 wceq wn cA c0 wne cA c0 wne cA cA cxp
    cuni cuni cA wceq cA c0 df-ne cA c0 df-ne cA c0 wne cA c0 wne wa cA cA cxp
    c0 wne cA cA cxp cuni cuni cA wceq cA cA xpnz cA cA cxp c0 wne cA cA cxp
    cuni cuni cA cA cun cA cA cA unixp cA unidm syl6eq sylbi sylancbr pm2.61i
    $.

  $( The converse of a set is a set.  Corollary 6.8(1) of [TakeutiZaring]
     p. 26.  (Contributed by NM, 17-Mar-1998.) $)
  cnvexg $p |- ( A e. V -> `' A e. _V ) $=
    cA cV wcel cA ccnv cA ccnv cdm cA ccnv crn cxp wss cA ccnv cdm cA ccnv crn
    cxp cvv wcel cA ccnv cvv wcel cA ccnv wrel cA ccnv cA ccnv cdm cA ccnv crn
    cxp wss cA relcnv cA ccnv relssdmrn ax-mp cA cV wcel cA ccnv cdm cvv wcel
    cA ccnv crn cvv wcel cA ccnv cdm cA ccnv crn cxp cvv wcel cA cV wcel cA
    ccnv cdm cA crn cvv cA df-rn cA cV rnexg syl5eqelr cA cV wcel cA ccnv crn
    cA cdm cvv cA dfdm4 cA cV dmexg syl5eqelr cA ccnv cdm cA ccnv crn cvv cvv
    xpexg syl2anc cA ccnv cA ccnv cdm cA ccnv crn cxp cvv ssexg sylancr $.

  ${
    cnvex.1 $e |- A e. _V $.
    $( The converse of a set is a set.  Corollary 6.8(1) of [TakeutiZaring]
       p. 26.  (Contributed by NM, 19-Dec-2003.) $)
    cnvex $p |- `' A e. _V $=
      cA cvv wcel cA ccnv cvv wcel cnvex.1 cA cvv cnvexg ax-mp $.
  $}

  $( A relation is a set iff its converse is a set.  (Contributed by FL,
     3-Mar-2007.) $)
  relcnvexb $p |- ( Rel R -> ( R e. _V <-> `' R e. _V ) ) $=
    cR wrel cR cvv wcel cR ccnv cvv wcel cR cvv cnvexg cR wrel cR ccnv ccnv cR
    wceq cR ccnv cvv wcel cR cvv wcel wi cR dfrel2 cR ccnv cvv wcel cR ccnv
    ccnv cvv wcel cR ccnv ccnv cR wceq cR cvv wcel cR ccnv cvv cnvexg cR ccnv
    ccnv cR cvv eleq1 syl5ib sylbi impbid2 $.

  ${
    $d x y A $.  $d x y B $.
    $( Restriction of a class to a singleton.  (Contributed by Mario Carneiro,
       28-Dec-2014.) $)
    ressn $p |- ( A |` { B } ) = ( { B } X. ( A " { B } ) ) $=
      vx vy cA cB csn cres cB csn cA cB csn cima cxp cA cB csn relres cB csn cA
      cB csn cima relxp vx cv vy cv cop cA wcel vx cv cB csn wcel wa vx cv cB
      csn wcel vy cv cA cB csn cima wcel wa vx cv vy cv cop cA cB csn cres wcel
      vx cv vy cv cop cB csn cA cB csn cima cxp wcel vx cv vy cv cop cA wcel vx
      cv cB csn wcel wa vx cv cB csn wcel vx cv vy cv cop cA wcel wa vx cv cB
      csn wcel vy cv cA cB csn cima wcel wa vx cv vy cv cop cA wcel vx cv cB
      csn wcel ancom vx cv cB csn wcel vx cv vy cv cop cA wcel vy cv cA cB csn
      cima wcel vx cv vy cv cop cA wcel vy cv cA vx cv csn cima wcel vx cv cB
      csn wcel vy cv cA cB csn cima wcel cA vx cv vy cv vx vex vy vex elimasn
      vx cv cB csn wcel cA vx cv csn cima cA cB csn cima vy cv vx cv cB csn
      wcel vx cv csn cB csn cA vx cv cB csn wcel vx cv cB vx cv cB elsni sneqd
      imaeq2d eleq2d syl5bbr pm5.32i bitri vx cv vy cv cA cB csn vy vex opelres
      vx cv vy cv cB csn cA cB csn cima opelxp 3bitr4i eqrelriiv $.
  $}

  ${
    $d A a b x $.  $d B a b $.
    $( The converse of an intersection is the intersection of the converse.
       (Contributed by FL, 15-Oct-2012.) $)
    cnviin $p |- ( A =/= (/) -> `' |^|_ x e. A B = |^|_ x e. A `' B ) $=
      cA c0 wne vx cA cB ciin ccnv wrel vx cA cB ccnv ciin wrel vx cA cB ciin
      ccnv vx cA cB ccnv ciin wceq vx cA cB ciin relcnv cA c0 wne vx cA cB ccnv
      ciin cvv cvv cxp wss vx cA cB ccnv ciin wrel cA c0 wne cB ccnv cvv cvv
      cxp wss vx cA wrex vx cA cB ccnv ciin cvv cvv cxp wss cB ccnv cvv cvv cxp
      wss cA c0 wne cB ccnv cvv cvv cxp wss vx cA wrex wi vx cA cA c0 wne cB
      ccnv cvv cvv cxp wss vx cA wral cB ccnv cvv cvv cxp wss vx cA wrex cB
      ccnv cvv cvv cxp wss vx cA r19.2z expcom cB ccnv cvv cvv cxp wss vx cv cA
      wcel cB ccnv wrel cB ccnv cvv cvv cxp wss cB relcnv cB ccnv df-rel mpbi
      a1i mprg vx cA cB ccnv cvv cvv cxp iinss syl vx cA cB ccnv ciin df-rel
      sylibr va vb vx cA cB ciin ccnv vx cA cB ccnv ciin vb cv va cv cop vx cA
      cB ciin wcel vb cv va cv cop cB wcel vx cA wral va cv vb cv cop vx cA cB
      ciin ccnv wcel va cv vb cv cop vx cA cB ccnv ciin wcel vb cv va cv cop
      cvv wcel vb cv va cv cop vx cA cB ciin wcel vb cv va cv cop cB wcel vx cA
      wral wb vb cv va cv opex vx vb cv va cv cop cA cB cvv eliin ax-mp va cv
      vb cv vx cA cB ciin va vex vb vex opelcnv va cv vb cv cop vx cA cB ccnv
      ciin wcel va cv vb cv cop cB ccnv wcel vx cA wral vb cv va cv cop cB wcel
      vx cA wral va cv vb cv cop cvv wcel va cv vb cv cop vx cA cB ccnv ciin
      wcel va cv vb cv cop cB ccnv wcel vx cA wral wb va cv vb cv opex vx va cv
      vb cv cop cA cB ccnv cvv eliin ax-mp va cv vb cv cop cB ccnv wcel vb cv
      va cv cop cB wcel vx cA va cv vb cv cB va vex vb vex opelcnv ralbii bitri
      3bitr4i eqrelriv sylancr $.
  $}

  ${
    $d x y z A $.  $d x y z R $.
    $( The converse of a partial order relation is a partial order relation.
       (Contributed by NM, 15-Jun-2005.) $)
    cnvpo $p |- ( R Po A <-> `' R Po A ) $=
      vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi wa vz cA wral vy cA wral vx cA wral vz cv vz cv cR ccnv wbr
      wn vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx cv cR ccnv
      wbr wi wa vx cA wral vy cA wral vz cA wral cA cR wpo cA cR ccnv wpo vx cv
      vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi wa vz cA wral vx cA wral vy cA wral vz cv vz cv cR ccnv wbr wn vz
      cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx cv cR ccnv wbr
      wi wa vx cA wral vz cA wral vy cA wral vx cv vx cv cR wbr wn vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vy cA
      wral vx cA wral vz cv vz cv cR ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv
      vx cv cR ccnv wbr wa vz cv vx cv cR ccnv wbr wi wa vx cA wral vy cA wral
      vz cA wral vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa
      vx cv vz cv cR wbr wi wa vz cA wral vx cA wral vz cv vz cv cR ccnv wbr wn
      vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx cv cR ccnv
      wbr wi wa vx cA wral vz cA wral vy cA vx cv vx cv cR wbr wn vx cv vy cv
      cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vx cA
      wral vx cv vx cv cR wbr wn vx cA wral vx cv vy cv cR wbr vy cv vz cv cR
      wbr wa vx cv vz cv cR wbr wi vz cA wral wa vx cA wral vz cv vz cv cR ccnv
      wbr wn vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx cv cR
      ccnv wbr wi wa vx cA wral vz cA wral vx cv vx cv cR wbr wn vz cA wral vx
      cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral wa
      vx cA wral vx cv vx cv cR wbr wn vx cA wral vx cA wral vx cv vy cv cR wbr
      vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral vx cA wral wa vx
      cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv
      cR wbr wi wa vz cA wral vx cA wral vx cv vx cv cR wbr wn vx cA wral vx cv
      vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral wa vx
      cA wral vx cv vx cv cR wbr wn vz cA wral vx cv vy cv cR wbr vy cv vz cv
      cR wbr wa vx cv vz cv cR wbr wi vz cA wral wa vx cA wral vx cv vx cv cR
      wbr wn vz cA wral vx cA wral vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx
      cv vz cv cR wbr wi vz cA wral vx cA wral wa vx cv vx cv cR wbr wn vx cA
      wral vx cA wral vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR
      wbr wi vz cA wral vx cA wral wa vx cv vx cv cR wbr wn vz cA wral vx cv vy
      cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral vx cA
      r19.26 vx cv vx cv cR wbr wn vz cA wral vx cA wral vx cv vx cv cR wbr wn
      vx cA wral vx cA wral vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz
      cv cR wbr wi vz cA wral vx cA wral vx cv vx cv cR wbr wn vx cA wral vx cA
      wral vx cv vx cv cR wbr wn vx cA wral vx cv vx cv cR wbr wn vz cA wral vx
      cA wral vx cv vx cv cR wbr wn vx cA ralidm vx cv vx cv cR wbr wn vx cA
      wral vx cv vx cv cR wbr wn vz cA wral vx cA wral wb cA c0 cA c0 wceq vx
      cv vx cv cR wbr wn vx cA wral vx cv vx cv cR wbr wn vz cA wral vx cA wral
      vx cv vx cv cR wbr wn vx cA rzal vx cv vx cv cR wbr wn vz cA wral vx cA
      rzal 2thd cA c0 wne vx cv vx cv cR wbr wn vx cv vx cv cR wbr wn vz cA
      wral vx cA vx cv vx cv cR wbr wn vz cA r19.3rzv ralbidv pm2.61ine bitr2i
      anbi1i bitri vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr
      wa vx cv vz cv cR wbr wi wa vz cA wral vx cv vx cv cR wbr wn vz cA wral
      vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral
      wa vx cA vx cv vx cv cR wbr wn vx cv vy cv cR wbr vy cv vz cv cR wbr wa
      vx cv vz cv cR wbr wi vz cA r19.26 ralbii vx cv vx cv cR wbr wn vx cA
      wral vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA
      wral vx cA r19.26 3bitr4i vx cv vx cv cR wbr wn vx cA wral vx cv vy cv cR
      wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral wa vx cA wral
      vz cv vz cv cR ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv
      wbr wa vz cv vx cv cR ccnv wbr wi wa vz cA wral vx cA wral vz cv vz cv cR
      ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx
      cv cR ccnv wbr wi wa vx cA wral vz cA wral vx cv vx cv cR wbr wn vx cA
      wral vx cv vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA
      wral wa vz cv vz cv cR ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv vx cv cR
      ccnv wbr wa vz cv vx cv cR ccnv wbr wi wa vz cA wral vx cA vz cv vz cv cR
      ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx
      cv cR ccnv wbr wi wa vz cA wral vz cv vz cv cR ccnv wbr wn vz cA wral vz
      cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx cv cR ccnv wbr
      wi vz cA wral wa vx cv vx cv cR wbr wn vx cA wral vx cv vy cv cR wbr vy
      cv vz cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral wa vz cv vz cv cR
      ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx
      cv cR ccnv wbr wi vz cA r19.26 vz cv vz cv cR ccnv wbr wn vz cA wral vx
      cv vx cv cR wbr wn vx cA wral vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv
      wbr wa vz cv vx cv cR ccnv wbr wi vz cA wral vx cv vy cv cR wbr vy cv vz
      cv cR wbr wa vx cv vz cv cR wbr wi vz cA wral vz cv vz cv cR ccnv wbr wn
      vx cv vx cv cR wbr wn vz vx cA vz cv vx cv wceq vz cv vz cv cR ccnv wbr
      vx cv vx cv cR wbr vz cv vz cv cR ccnv wbr vz cv vz cv cR wbr vz cv vx cv
      wceq vx cv vx cv cR wbr vz cv vz cv cR vz vex vz vex brcnv vz cv vx cv
      wceq vz cv vx cv vz cv vx cv cR vz cv vx cv wceq id vz cv vx cv wceq id
      breq12d syl5bb notbid cbvralv vz cv vy cv cR ccnv wbr vy cv vx cv cR ccnv
      wbr wa vz cv vx cv cR ccnv wbr wi vx cv vy cv cR wbr vy cv vz cv cR wbr
      wa vx cv vz cv cR wbr wi vz cA vz cv vy cv cR ccnv wbr vy cv vx cv cR
      ccnv wbr wa vx cv vy cv cR wbr vy cv vz cv cR wbr wa vz cv vx cv cR ccnv
      wbr vx cv vz cv cR wbr vz cv vy cv cR ccnv wbr vy cv vz cv cR wbr vy cv
      vx cv cR ccnv wbr vx cv vy cv cR wbr vz cv vy cv cR vz vex vy vex brcnv
      vy cv vx cv cR vy vex vx vex brcnv anbi12ci vz cv vx cv cR vz vex vx vex
      brcnv imbi12i ralbii anbi12i bitr2i ralbii vz cv vz cv cR ccnv wbr wn vz
      cv vy cv cR ccnv wbr vy cv vx cv cR ccnv wbr wa vz cv vx cv cR ccnv wbr
      wi wa vx vz cA cA ralcom bitri bitri ralbii vx cv vx cv cR wbr wn vx cv
      vy cv cR wbr vy cv vz cv cR wbr wa vx cv vz cv cR wbr wi wa vz cA wral vx
      vy cA cA ralcom vz cv vz cv cR ccnv wbr wn vz cv vy cv cR ccnv wbr vy cv
      vx cv cR ccnv wbr wa vz cv vx cv cR ccnv wbr wi wa vx cA wral vz vy cA cA
      ralcom 3bitr4i vx vy vz cA cR df-po vz vy vx cA cR ccnv df-po 3bitr4i $.

    $( The converse of a strict order relation is a strict order relation.
       (Contributed by NM, 15-Jun-2005.) $)
    cnvso $p |- ( R Or A <-> `' R Or A ) $=
      cA cR wpo vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy
      cA wral vx cA wral wa cA cR ccnv wpo vy cv vx cv cR ccnv wbr vy cv vx cv
      wceq vx cv vy cv cR ccnv wbr w3o vx cA wral vy cA wral wa cA cR wor cA cR
      ccnv wor cA cR wpo cA cR ccnv wpo vx cv vy cv cR wbr vx cv vy cv wceq vy
      cv vx cv cR wbr w3o vy cA wral vx cA wral vy cv vx cv cR ccnv wbr vy cv
      vx cv wceq vx cv vy cv cR ccnv wbr w3o vx cA wral vy cA wral cA cR cnvpo
      vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vy cA wral vx
      cA wral vx cv vy cv cR wbr vx cv vy cv wceq vy cv vx cv cR wbr w3o vx cA
      wral vy cA wral vy cv vx cv cR ccnv wbr vy cv vx cv wceq vx cv vy cv cR
      ccnv wbr w3o vx cA wral vy cA wral vx cv vy cv cR wbr vx cv vy cv wceq vy
      cv vx cv cR wbr w3o vx vy cA cA ralcom vy cv vx cv cR ccnv wbr vy cv vx
      cv wceq vx cv vy cv cR ccnv wbr w3o vx cv vy cv cR wbr vx cv vy cv wceq
      vy cv vx cv cR wbr w3o vy vx cA cA vy cv vx cv cR ccnv wbr vx cv vy cv cR
      wbr vy cv vx cv wceq vx cv vy cv wceq vx cv vy cv cR ccnv wbr vy cv vx cv
      cR wbr vy cv vx cv cR vy vex vx vex brcnv vy vx equcom vx cv vy cv cR vx
      vex vy vex brcnv 3orbi123i 2ralbii bitr4i anbi12i vx vy cA cR df-so vy vx
      cA cR ccnv df-so 3bitr4i $.
  $}

  $( The composition of two sets is a set.  (Contributed by NM,
     19-Mar-1998.) $)
  coexg $p |- ( ( A e. V /\ B e. W ) -> ( A o. B ) e. _V ) $=
    cA cV wcel cB cW wcel wa cA cB ccom cB cdm cA crn cxp wss cB cdm cA crn cxp
    cvv wcel cA cB ccom cvv wcel cA cB ccom wrel cA cB ccom cB cdm cA crn cxp
    wss cA cB relco cA cB ccom wrel cA cB ccom cA cB ccom cdm cA cB ccom crn
    cxp cB cdm cA crn cxp cA cB ccom relssdmrn cA cB ccom cdm cB cdm wss cA cB
    ccom crn cA crn wss cA cB ccom cdm cA cB ccom crn cxp cB cdm cA crn cxp wss
    cA cB dmcoss cA cB rncoss cA cB ccom cdm cB cdm cA cB ccom crn cA crn
    xpss12 mp2an syl6ss ax-mp cB cW wcel cB cdm cvv wcel cA crn cvv wcel cB cdm
    cA crn cxp cvv wcel cA cV wcel cB cW dmexg cA cV rnexg cB cdm cA crn cvv
    cvv xpexg syl2anr cA cB ccom cB cdm cA crn cxp cvv ssexg sylancr $.

  ${
    coex.1 $e |- A e. _V $.
    coex.2 $e |- B e. _V $.
    $( The composition of two sets is a set.  (Contributed by NM,
       15-Dec-2003.) $)
    coex $p |- ( A o. B ) e. _V $=
      cA cvv wcel cB cvv wcel cA cB ccom cvv wcel coex.1 coex.2 cA cB cvv cvv
      coexg mp2an $.
  $}



