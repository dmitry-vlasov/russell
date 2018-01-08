
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Proper_substitution_of_classes_for_sets.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper substitution of classes for sets into classes

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [_ $.  $( Underlined left bracket $)
  $c ]_ $.  $( Underlined right bracket $)

  $( Extend class notation to include the proper substitution of a class for a
     set into another class. $)
  csb $a class [_ A / x ]_ B $.

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( Define the proper substitution of a class for a set into another class.
       The underlined brackets distinguish it from the substitution into a wff,
       ~ wsbc , to prevent ambiguity.  Theorem ~ sbcel1g shows an example of
       how ambiguity could arise if we didn't use distinguished brackets.
       Theorem ~ sbccsbg recreates substitution into a wff from this
       definition.  (Contributed by NM, 10-Nov-2005.) $)
    df-csb $a |- [_ A / x ]_ B = { y | [. A / x ]. y e. B } $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y $.
    $( Alternate expression for the proper substitution into a class, without
       referencing substitution into a wff.  Note that ` x ` can be free in
       ` B ` but cannot occur in ` A ` .  (Contributed by NM, 2-Dec-2013.) $)
    csb2 $p |- [_ A / x ]_ B = { y | E. x ( x = A /\ y e. B ) } $=
      vx cA cB csb vy cv cB wcel vx cA wsbc vy cab vx cv cA wceq vy cv cB wcel
      wa vx wex vy cab vx vy cA cB df-csb vy cv cB wcel vx cA wsbc vx cv cA
      wceq vy cv cB wcel wa vx wex vy vy cv cB wcel vx cA sbc5 abbii eqtri $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( Analog of ~ dfsbcq for proper substitution into a class.  (Contributed
       by NM, 10-Nov-2005.) $)
    csbeq1 $p |- ( A = B -> [_ A / x ]_ C = [_ B / x ]_ C ) $=
      cA cB wceq vy cv cC wcel vx cA wsbc vy cab vy cv cC wcel vx cB wsbc vy
      cab vx cA cC csb vx cB cC csb cA cB wceq vy cv cC wcel vx cA wsbc vy cv
      cC wcel vx cB wsbc vy vy cv cC wcel vx cA cB dfsbcq abbidv vx vy cA cC
      df-csb vx vy cB cC df-csb 3eqtr4g $.
  $}

  ${
    $d x z $.  $d y z $.  $d z A $.  $d z C $.  $d z D $.
    cbvcsb.1 $e |- F/_ y C $.
    cbvcsb.2 $e |- F/_ x D $.
    cbvcsb.3 $e |- ( x = y -> C = D ) $.
    $( Change bound variables in a class substitution.  Interestingly, this
       does not require any bound variable conditions on ` A ` .  (Contributed
       by Jeff Hankins, 13-Sep-2009.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    cbvcsb $p |- [_ A / x ]_ C = [_ A / y ]_ D $=
      vz cv cC wcel vx cA wsbc vz cab vz cv cD wcel vy cA wsbc vz cab vx cA cC
      csb vy cA cD csb vz cv cC wcel vx cA wsbc vz cv cD wcel vy cA wsbc vz vz
      cv cC wcel vz cv cD wcel vx vy cA vy vz cC cbvcsb.1 nfcri vx vz cD
      cbvcsb.2 nfcri vx cv vy cv wceq cC cD vz cv cbvcsb.3 eleq2d cbvsbc abbii
      vx vz cA cC df-csb vy vz cA cD df-csb 3eqtr4i $.
  $}

  ${
    $d x y $.  $d z A $.  $d y z B $.  $d x z C $.
    cbvcsbv.1 $e |- ( x = y -> B = C ) $.
    $( Change the bound variable of a proper substitution into a class using
       implicit substitution.  (Contributed by NM, 30-Sep-2008.)  (Revised by
       Mario Carneiro, 13-Oct-2016.) $)
    cbvcsbv $p |- [_ A / x ]_ B = [_ A / y ]_ C $=
      vx vy cA cB cC vy cB nfcv vx cC nfcv cbvcsbv.1 cbvcsb $.
  $}

  ${
    csbeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for proper substitution into a class.  (Contributed
       by NM, 3-Dec-2005.) $)
    csbeq1d $p |- ( ph -> [_ A / x ]_ C = [_ B / x ]_ C ) $=
      wph cA cB wceq vx cA cC csb vx cB cC csb wceq csbeq1d.1 vx cA cB cC
      csbeq1 syl $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Analog of ~ sbid for proper substitution into a class.  (Contributed by
       NM, 10-Nov-2005.) $)
    csbid $p |- [_ x / x ]_ A = A $=
      vx vx cv cA csb vy cv cA wcel vx vx cv wsbc vy cab vy cv cA wcel vy cab
      cA vx vy vx cv cA df-csb vy cv cA wcel vx vx cv wsbc vy cv cA wcel vy vy
      cv cA wcel vx vx cv wsbc vy cv cA wcel vx vx wsb vy cv cA wcel vy cv cA
      wcel vx vx sbsbc vy cv cA wcel vx sbid bitr3i abbii vy cA abid2 3eqtri $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    $( Equality theorem for proper substitution into a class.  (Contributed by
       NM, 10-Nov-2005.) $)
    csbeq1a $p |- ( x = A -> B = [_ A / x ]_ B ) $=
      vx cv cA wceq cB vx vx cv cB csb vx cA cB csb vx cB csbid vx vx cv cA cB
      csbeq1 syl5eqr $.
  $}

  ${
    $d z A $.  $d y z B $.  $d z V $.  $d x z $.
    $( Composition law for chained substitutions into a class.  (Contributed by
       NM, 10-Nov-2005.) $)
    csbco $p |- [_ A / y ]_ [_ y / x ]_ B = [_ A / x ]_ B $=
      vz cv vx vy cv cB csb wcel vy cA wsbc vz cab vz cv cB wcel vx cA wsbc vz
      cab vy cA vx vy cv cB csb csb vx cA cB csb vz cv vx vy cv cB csb wcel vy
      cA wsbc vz cv cB wcel vx cA wsbc vz vz cv vx vy cv cB csb wcel vy cA wsbc
      vz cv cB wcel vx vy cv wsbc vy cA wsbc vz cv cB wcel vx cA wsbc vz cv vx
      vy cv cB csb wcel vz cv cB wcel vx vy cv wsbc vy cA vz cv cB wcel vx vy
      cv wsbc vz vx vy cv cB csb vx vz vy cv cB df-csb abeq2i sbcbii vz cv cB
      wcel vx vy cA sbcco bitri abbii vy vz cA vx vy cv cB csb df-csb vx vz cA
      cB df-csb 3eqtr4i $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( The existence of proper substitution into a class.  (Contributed by NM,
       10-Nov-2005.) $)
    csbexg $p |- ( ( A e. V /\ A. x B e. W ) -> [_ A / x ]_ B e. _V ) $=
      cA cV wcel cB cW wcel vx wal wa vx cA cB csb vy cv cB wcel vx cA wsbc vy
      cab cvv vx vy cA cB df-csb cA cV wcel cB cW wcel vx wal wa vy cv cB wcel
      vy cab cvv wcel vx cA wsbc vy cv cB wcel vx cA wsbc vy cab cvv wcel cA cV
      wcel cB cW wcel vx wal vy cv cB wcel vy cab cvv wcel vx cA wsbc cB cW
      wcel vx wal vy cv cB wcel vy cab cvv wcel vx wal cA cV wcel vy cv cB wcel
      vy cab cvv wcel vx cA wsbc cB cW wcel vy cv cB wcel vy cab cvv wcel vx cB
      cW wcel vy cv cB wcel vy cab cB cvv vy cB abid2 cB cW elex syl5eqel alimi
      vy cv cB wcel vy cab cvv wcel vx cA cV spsbc syl5 imp cA cV wcel vy cv cB
      wcel vy cab cvv wcel vx cA wsbc vy cv cB wcel vx cA wsbc vy cab cvv wcel
      wb cB cW wcel vx wal vy cv cB wcel vx vy cA cvv cV vx cvv nfcv sbcabel
      adantr mpbid syl5eqel $.
  $}

  ${
    csbex.1 $e |- A e. _V $.
    csbex.2 $e |- B e. _V $.
    $( The existence of proper substitution into a class.  (Contributed by NM,
       7-Aug-2007.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    csbex $p |- [_ A / x ]_ B e. _V $=
      cB cvv wcel vx cA cB csb cvv wcel vx cA cvv wcel cB cvv wcel vx wal vx cA
      cB csb cvv wcel csbex.1 vx cA cB cvv cvv csbexg mpan csbex.2 mpg $.
  $}

  ${
    $d y A $.  $d y B $.  $d y V $.  $d x y $.
    $( Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free).  (Contributed by Mario Carneiro, 14-Oct-2016.) $)
    csbtt $p |- ( ( A e. V /\ F/_ x B ) -> [_ A / x ]_ B = B ) $=
      cA cV wcel vx cB wnfc wa vx cA cB csb vy cv cB wcel vx cA wsbc vy cab cB
      vx vy cA cB df-csb cA cV wcel vx cB wnfc wa vy cv cB wcel vx cA wsbc vy
      cB vx cB wnfc cA cV wcel vy cv cB wcel vx wnf vy cv cB wcel vx cA wsbc vy
      cv cB wcel wb vx vy cB nfcr vy cv cB wcel vx cA cV sbctt sylan2 abbi1dv
      syl5eq $.
  $}

  ${
    csbconstgf.1 $e |- F/_ x B $.
    $( Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free).  (Contributed by NM, 10-Nov-2005.) $)
    csbconstgf $p |- ( A e. V -> [_ A / x ]_ B = B ) $=
      cA cV wcel vx cB wnfc vx cA cB csb cB wceq csbconstgf.1 vx cA cB cV csbtt
      mpan2 $.
  $}

  ${
    $d A y $.  $d B x y $.  $d V y $.
    $( Substitution doesn't affect a constant ` B ` (in which ` x ` is not
       free). ~ csbconstgf with distinct variable requirement.  (Contributed by
       Alan Sare, 22-Jul-2012.) $)
    csbconstg $p |- ( A e. V -> [_ A / x ]_ B = B ) $=
      vx cA cB cV vx cB nfcv csbconstgf $.
  $}

  ${
    $d w x y z $.  $d w y z A $.  $d w y z B $.  $d w y z C $.
    $( Distribute proper substitution through a membership relation.
       (Contributed by NM, 10-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    sbcel12g $p |- ( A e. V -> ( [. A / x ]. B e. C <->
                   [_ A / x ]_ B e. [_ A / x ]_ C ) ) $=
      cA cV wcel cB cC wcel vx cA wsbc vy cv cB wcel vx cA wsbc vy cab vy cv cC
      wcel vx cA wsbc vy cab wcel vx cA cB csb vx cA cC csb wcel cB cC wcel vx
      vz wsb vy cv cB wcel vx vz wsb vy cab vy cv cC wcel vx vz wsb vy cab wcel
      cB cC wcel vx cA wsbc vy cv cB wcel vx cA wsbc vy cab vy cv cC wcel vx cA
      wsbc vy cab wcel vz cA cV cB cC wcel vx vz cA dfsbcq2 vz cv cA wceq vy cv
      cB wcel vx vz wsb vy cab vy cv cB wcel vx cA wsbc vy cab vy cv cC wcel vx
      vz wsb vy cab vy cv cC wcel vx cA wsbc vy cab vz cv cA wceq vy cv cB wcel
      vx vz wsb vy cv cB wcel vx cA wsbc vy vy cv cB wcel vx vz cA dfsbcq2
      abbidv vz cv cA wceq vy cv cC wcel vx vz wsb vy cv cC wcel vx cA wsbc vy
      vy cv cC wcel vx vz cA dfsbcq2 abbidv eleq12d cB cC wcel vy cv cB wcel vx
      vz wsb vy cab vy cv cC wcel vx vz wsb vy cab wcel vx vz vx vy cv cB wcel
      vx vz wsb vy cab vy cv cC wcel vx vz wsb vy cab vy cv cB wcel vx vz wsb
      vx vy vy cv cB wcel vx vz nfs1v nfab vy cv cC wcel vx vz wsb vx vy vy cv
      cC wcel vx vz nfs1v nfab nfel vx vz weq cB vy cv cB wcel vx vz wsb vy cab
      cC vy cv cC wcel vx vz wsb vy cab vx vz vy cB sbab vx vz vy cC sbab
      eleq12d sbie vtoclbg vx cA cB csb vy cv cB wcel vx cA wsbc vy cab vx cA
      cC csb vy cv cC wcel vx cA wsbc vy cab vx vy cA cB df-csb vx vy cA cC
      df-csb eleq12i syl6bbr $.

    $( Distribute proper substitution through an equality relation.
       (Contributed by NM, 10-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    sbceqg $p |- ( A e. V -> ( [. A / x ]. B = C <->
                   [_ A / x ]_ B = [_ A / x ]_ C ) ) $=
      cA cV wcel cB cC wceq vx cA wsbc vy cv cB wcel vx cA wsbc vy cab vy cv cC
      wcel vx cA wsbc vy cab wceq vx cA cB csb vx cA cC csb wceq cB cC wceq vx
      vz wsb vy cv cB wcel vx vz wsb vy cab vy cv cC wcel vx vz wsb vy cab wceq
      cB cC wceq vx cA wsbc vy cv cB wcel vx cA wsbc vy cab vy cv cC wcel vx cA
      wsbc vy cab wceq vz cA cV cB cC wceq vx vz cA dfsbcq2 vz cv cA wceq vy cv
      cB wcel vx vz wsb vy cab vy cv cB wcel vx cA wsbc vy cab vy cv cC wcel vx
      vz wsb vy cab vy cv cC wcel vx cA wsbc vy cab vz cv cA wceq vy cv cB wcel
      vx vz wsb vy cv cB wcel vx cA wsbc vy vy cv cB wcel vx vz cA dfsbcq2
      abbidv vz cv cA wceq vy cv cC wcel vx vz wsb vy cv cC wcel vx cA wsbc vy
      vy cv cC wcel vx vz cA dfsbcq2 abbidv eqeq12d cB cC wceq vy cv cB wcel vx
      vz wsb vy cab vy cv cC wcel vx vz wsb vy cab wceq vx vz vx vy cv cB wcel
      vx vz wsb vy cab vy cv cC wcel vx vz wsb vy cab vy cv cB wcel vx vz wsb
      vx vy vy cv cB wcel vx vz nfs1v nfab vy cv cC wcel vx vz wsb vx vy vy cv
      cC wcel vx vz nfs1v nfab nfeq vx vz weq cB vy cv cB wcel vx vz wsb vy cab
      cC vy cv cC wcel vx vz wsb vy cab vx vz vy cB sbab vx vz vy cC sbab
      eqeq12d sbie vtoclbg vx cA cB csb vy cv cB wcel vx cA wsbc vy cab vx cA
      cC csb vy cv cC wcel vx cA wsbc vy cab vx vy cA cB df-csb vx vy cA cC
      df-csb eqeq12i syl6bbr $.
  $}

  $( Distribute proper substitution through negated membership.  (Contributed
     by Andrew Salmon, 18-Jun-2011.) $)
  sbcnel12g $p |- ( A e. V -> ( [. A / x ]. B e/ C <-> [_ A / x ]_ B e/
                    [_ A / x ]_ C ) ) $=
    cA cV wcel cB cC wnel vx cA wsbc cB cC wcel wn vx cA wsbc cB cC wcel vx cA
    wsbc wn vx cA cB csb vx cA cC csb wnel cB cC wnel vx cA wsbc cB cC wcel wn
    vx cA wsbc wb cA cV wcel cB cC wnel cB cC wcel wn vx cA cB cC df-nel sbcbii
    a1i cB cC wcel vx cA cV sbcng cA cV wcel cB cC wcel vx cA wsbc wn vx cA cB
    csb vx cA cC csb wcel wn vx cA cB csb vx cA cC csb wnel cA cV wcel cB cC
    wcel vx cA wsbc vx cA cB csb vx cA cC csb wcel vx cA cB cC cV sbcel12g
    notbid vx cA cB csb vx cA cC csb df-nel syl6bbr 3bitrd $.

  $( Distribute proper substitution through an inequality.  (Contributed by
     Andrew Salmon, 18-Jun-2011.) $)
  sbcne12g $p |- ( A e. V -> ( [. A / x ]. B =/= C <-> [_ A / x ]_ B =/=
                   [_ A / x ]_ C ) ) $=
    cA cV wcel cB cC wne vx cA wsbc vx cA cB csb vx cA cC csb wne cA cV wcel cB
    cC wne wn vx cA wsbc cB cC wceq vx cA wsbc cB cC wne vx cA wsbc wn vx cA cB
    csb vx cA cC csb wne wn cB cC wne wn vx cA wsbc cB cC wceq vx cA wsbc wb cA
    cV wcel cB cC wne wn cB cC wceq vx cA cB cC nne sbcbii a1i cB cC wne vx cA
    cV sbcng cA cV wcel cB cC wceq vx cA wsbc vx cA cB csb vx cA cC csb wceq vx
    cA cB csb vx cA cC csb wne wn vx cA cB cC cV sbceqg vx cA cB csb vx cA cC
    csb nne syl6bbr 3bitr3d con4bid $.

  ${
    $d y A $.  $d x y C $.  $d y V $.
    $( Move proper substitution in and out of a membership relation.  Note that
       the scope of ` [. A / x ]. ` is the wff ` B e. C ` , whereas the scope
       of ` [_ A / x ]_ ` is the class ` B ` .  (Contributed by NM,
       10-Nov-2005.) $)
    sbcel1g $p |- ( A e. V -> ( [. A / x ]. B e. C <->
                    [_ A / x ]_ B e. C ) ) $=
      cA cV wcel cB cC wcel vx cA wsbc vx cA cB csb vx cA cC csb wcel vx cA cB
      csb cC wcel vx cA cB cC cV sbcel12g cA cV wcel vx cA cC csb cC vx cA cB
      csb vx cA cC cV csbconstg eleq2d bitrd $.

    $( Move proper substitution to first argument of an equality.  (Contributed
       by NM, 30-Nov-2005.) $)
    sbceq1g $p |- ( A e. V -> ( [. A / x ]. B = C <->
                    [_ A / x ]_ B = C ) ) $=
      cA cV wcel cB cC wceq vx cA wsbc vx cA cB csb vx cA cC csb wceq vx cA cB
      csb cC wceq vx cA cB cC cV sbceqg cA cV wcel vx cA cC csb cC vx cA cB csb
      vx cA cC cV csbconstg eqeq2d bitrd $.
  $}

  ${
    $d y A $.  $d x y B $.  $d y V $.
    $( Move proper substitution in and out of a membership relation.
       (Contributed by NM, 14-Nov-2005.) $)
    sbcel2g $p |- ( A e. V -> ( [. A / x ]. B e. C <->
                    B e. [_ A / x ]_ C ) ) $=
      cA cV wcel cB cC wcel vx cA wsbc vx cA cB csb vx cA cC csb wcel cB vx cA
      cC csb wcel vx cA cB cC cV sbcel12g cA cV wcel vx cA cB csb cB vx cA cC
      csb vx cA cB cV csbconstg eleq1d bitrd $.

    $( Move proper substitution to second argument of an equality.
       (Contributed by NM, 30-Nov-2005.) $)
    sbceq2g $p |- ( A e. V -> ( [. A / x ]. B = C <->
                    B = [_ A / x ]_ C ) ) $=
      cA cV wcel cB cC wceq vx cA wsbc vx cA cB csb vx cA cC csb wceq cB vx cA
      cC csb wceq vx cA cB cC cV sbceqg cA cV wcel vx cA cB csb cB vx cA cC csb
      vx cA cB cV csbconstg eqeq1d bitrd $.
  $}

  ${
    $d y z A $.  $d x z B $.  $d z C $.  $d x y $.
    $( Commutative law for double substitution into a class.  (Contributed by
       NM, 14-Nov-2005.) $)
    csbcomg $p |- ( ( A e. V /\ B e. W ) ->
                 [_ A / x ]_ [_ B / y ]_ C = [_ B / y ]_ [_ A / x ]_ C ) $=
      cA cV wcel cA cvv wcel cB cvv wcel vx cA vy cB cC csb csb vy cB vx cA cC
      csb csb wceq cB cW wcel cA cV elex cB cW elex cA cvv wcel cB cvv wcel wa
      vz vx cA vy cB cC csb csb vy cB vx cA cC csb csb cA cvv wcel cB cvv wcel
      wa vz cv vy cB cC csb wcel vx cA wsbc vz cv vx cA cC csb wcel vy cB wsbc
      vz cv vx cA vy cB cC csb csb wcel vz cv vy cB vx cA cC csb csb wcel cA
      cvv wcel cB cvv wcel wa vz cv cC wcel vy cB wsbc vx cA wsbc vz cv cC wcel
      vx cA wsbc vy cB wsbc vz cv vy cB cC csb wcel vx cA wsbc vz cv vx cA cC
      csb wcel vy cB wsbc vz cv cC wcel vy cB wsbc vx cA wsbc vz cv cC wcel vx
      cA wsbc vy cB wsbc wb cA cvv wcel cB cvv wcel wa vz cv cC wcel vx vy cA
      cB sbccom a1i cB cvv wcel vz cv cC wcel vy cB wsbc vx cA wsbc vz cv vy cB
      cC csb wcel vx cA wsbc wb cA cvv wcel cB cvv wcel vz cv cC wcel vy cB
      wsbc vz cv vy cB cC csb wcel vx cA vy cB vz cv cC cvv sbcel2g sbcbidv
      adantl cA cvv wcel vz cv cC wcel vx cA wsbc vy cB wsbc vz cv vx cA cC csb
      wcel vy cB wsbc wb cB cvv wcel cA cvv wcel vz cv cC wcel vx cA wsbc vz cv
      vx cA cC csb wcel vy cB vx cA vz cv cC cvv sbcel2g sbcbidv adantr 3bitr3d
      cA cvv wcel vz cv vy cB cC csb wcel vx cA wsbc vz cv vx cA vy cB cC csb
      csb wcel wb cB cvv wcel vx cA vz cv vy cB cC csb cvv sbcel2g adantr cB
      cvv wcel vz cv vx cA cC csb wcel vy cB wsbc vz cv vy cB vx cA cC csb csb
      wcel wb cA cvv wcel vy cB vz cv vx cA cC csb cvv sbcel2g adantl 3bitr3d
      eqrdv syl2an $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.  $d y ph $.
    csbeq2d.1 $e |- F/ x ph $.
    csbeq2d.2 $e |- ( ph -> B = C ) $.
    $( Formula-building deduction rule for class substitution.  (Contributed by
       NM, 22-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
    csbeq2d $p |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C ) $=
      wph vy cv cB wcel vx cA wsbc vy cab vy cv cC wcel vx cA wsbc vy cab vx cA
      cB csb vx cA cC csb wph vy cv cB wcel vx cA wsbc vy cv cC wcel vx cA wsbc
      vy wph vy cv cB wcel vy cv cC wcel vx cA csbeq2d.1 wph cB cC vy cv
      csbeq2d.2 eleq2d sbcbid abbidv vx vy cA cB df-csb vx vy cA cC df-csb
      3eqtr4g $.
  $}

  ${
    $d x ph $.
    csbeq2dv.1 $e |- ( ph -> B = C ) $.
    $( Formula-building deduction rule for class substitution.  (Contributed by
       NM, 10-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
    csbeq2dv $p |- ( ph -> [_ A / x ]_ B = [_ A / x ]_ C ) $=
      wph vx cA cB cC wph vx nfv csbeq2dv.1 csbeq2d $.
  $}

  ${
    csbeq2i.1 $e |- B = C $.
    $( Formula-building inference rule for class substitution.  (Contributed by
       NM, 10-Nov-2005.)  (Revised by Mario Carneiro, 1-Sep-2015.) $)
    csbeq2i $p |- [_ A / x ]_ B = [_ A / x ]_ C $=
      vx cA cB csb vx cA cC csb wceq wtru vx cA cB cC cB cC wceq wtru csbeq2i.1
      a1i csbeq2dv trud $.
  $}

  ${
    $d y z A $.  $d x y z $.
    $( The proper substitution of a class for set variable results in the class
       (if the class exists).  (Contributed by NM, 10-Nov-2005.) $)
    csbvarg $p |- ( A e. V -> [_ A / x ]_ x = A ) $=
      cA cV wcel cA cvv wcel vx cA vx cv csb cA wceq cA cV elex cA cvv wcel vx
      cA vx cv csb vz cv vy cv wcel vy cA wsbc vz cab cA vy cA vx vy cv vx cv
      csb csb vy cA vy cv csb vx cA vx cv csb vz cv vy cv wcel vy cA wsbc vz
      cab vy cA vx vy cv vx cv csb vy cv vy cv cvv wcel vx vy cv vx cv csb vy
      cv wceq vy vex vy cv cvv wcel vx vy cv vx cv csb vz cv vx cv wcel vx vy
      cv wsbc vz cab vy cv vx vz vy cv vx cv df-csb vy cv cvv wcel vz cv vx cv
      wcel vx vy cv wsbc vz vy cv vx vz cv vy cv cvv sbcel2gv abbi1dv syl5eq
      ax-mp csbeq2i vx vy cA vx cv csbco vy vz cA vy cv df-csb 3eqtr3i cA cvv
      wcel vz cv vy cv wcel vy cA wsbc vz cA vy vz cv cA cvv sbcel2gv abbi1dv
      syl5eq syl $.
  $}

  ${
    $d x y $.
    $( Substitution into a wff expressed in terms of substitution into a
       class.  (Contributed by NM, 15-Aug-2007.) $)
    sbccsbg $p |- ( A e. V ->
                 ( [. A / x ]. ph <-> y e. [_ A / x ]_ { y | ph } ) ) $=
      wph vx cA wsbc vy cv wph vy cab wcel vx cA wsbc cA cV wcel vy cv vx cA
      wph vy cab csb wcel vy cv wph vy cab wcel wph vx cA wph vy abid sbcbii vx
      cA vy cv wph vy cab cV sbcel2g syl5bbr $.
  $}

  $( Substitution into a wff expressed in using substitution into a class.
     (Contributed by NM, 27-Nov-2005.) $)
  sbccsb2g $p |- ( A e. V ->
               ( [. A / x ]. ph <-> A e. [_ A / x ]_ { x | ph } ) ) $=
    wph vx cA wsbc vx cv wph vx cab wcel vx cA wsbc cA cV wcel cA vx cA wph vx
    cab csb wcel vx cv wph vx cab wcel wph vx cA wph vx abid sbcbii cA cV wcel
    vx cv wph vx cab wcel vx cA wsbc vx cA vx cv csb vx cA wph vx cab csb wcel
    cA vx cA wph vx cab csb wcel vx cA vx cv wph vx cab cV sbcel12g cA cV wcel
    vx cA vx cv csb cA vx cA wph vx cab csb vx cA cV csbvarg eleq1d bitrd
    syl5bbr $.

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y ph $.
    nfcsb1d.1 $e |- ( ph -> F/_ x A ) $.
    $( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)
    nfcsb1d $p |- ( ph -> F/_ x [_ A / x ]_ B ) $=
      wph vx vx cA cB csb vy cv cB wcel vx cA wsbc vy cab vx vy cA cB df-csb
      wph vy cv cB wcel vx cA wsbc vx vy wph vy nfv wph vy cv cB wcel vx cA
      nfcsb1d.1 nfsbc1d nfabd nfcxfrd $.
  $}

  ${
    $d y z A $.  $d z B $.  $d x y z $.
    nfcsb1.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)
    nfcsb1 $p |- F/_ x [_ A / x ]_ B $=
      vx vx cA cB csb wnfc wtru vx cA cB vx cA wnfc wtru nfcsb1.1 a1i nfcsb1d
      trud $.
  $}

  ${
    $d x y A $.
    $( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by NM, 17-Aug-2006.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)
    nfcsb1v $p |- F/_ x [_ A / x ]_ B $=
      vx cA cB vx cA nfcv nfcsb1 $.
  $}

  ${
    $d x z $.  $d y z $.  $d z A $.  $d z B $.  $d z ph $.
    nfcsbd.1 $e |- F/ y ph $.
    nfcsbd.2 $e |- ( ph -> F/_ x A ) $.
    nfcsbd.3 $e |- ( ph -> F/_ x B ) $.
    $( Deduction version of ~ nfcsb .  (Contributed by NM, 21-Nov-2005.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)
    nfcsbd $p |- ( ph -> F/_ x [_ A / y ]_ B ) $=
      wph vx vy cA cB csb vz cv cB wcel vy cA wsbc vz cab vy vz cA cB df-csb
      wph vz cv cB wcel vy cA wsbc vx vz wph vz nfv wph vz cv cB wcel vx vy cA
      nfcsbd.1 nfcsbd.2 wph vx vz cB nfcsbd.3 nfcrd nfsbcd nfabd nfcxfrd $.
  $}

  ${
    nfcsb.1 $e |- F/_ x A $.
    nfcsb.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for substitution into a class.
       (Contributed by Mario Carneiro, 12-Oct-2016.) $)
    nfcsb $p |- F/_ x [_ A / y ]_ B $=
      vx vy cA cB csb wnfc wtru vx vy cA cB vy nftru vx cA wnfc wtru nfcsb.1
      a1i vx cB wnfc wtru nfcsb.2 a1i nfcsbd trud $.
  $}

  ${
    $d x y $.
    csbhypf.1 $e |- F/_ x A $.
    csbhypf.2 $e |- F/_ x C $.
    csbhypf.3 $e |- ( x = A -> B = C ) $.
    $( Introduce an explicit substitution into an implicit substitution
       hypothesis.  See ~ sbhypf for class substitution version.  (Contributed
       by NM, 19-Dec-2008.) $)
    csbhypf $p |- ( y = A -> [_ y / x ]_ B = C ) $=
      vx cv cA wceq cB cC wceq wi vy cv cA wceq vx vy cv cB csb cC wceq wi vx
      vy vy cv cA wceq vx vy cv cB csb cC wceq vx vx vy cv cA csbhypf.1 nfeq2
      vx vx vy cv cB csb cC vx vy cv cB nfcsb1v csbhypf.2 nfeq nfim vx cv vy cv
      wceq vx cv cA wceq vy cv cA wceq cB cC wceq vx vy cv cB csb cC wceq vx cv
      vy cv cA eqeq1 vx cv vy cv wceq cB vx vy cv cB csb cC vx vy cv cB csbeq1a
      eqeq1d imbi12d csbhypf.3 chvar $.
  $}

  ${
    $d x A $.
    $( Conversion of implicit substitution to explicit substitution into a
       class.  (Closed theorem version of ~ csbiegf .)  (Contributed by NM,
       11-Nov-2005.) $)
    csbiebt $p |- ( ( A e. V /\ F/_ x C ) ->
                 ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) ) $=
      cA cV wcel cA cvv wcel vx cC wnfc vx cv cA wceq cB cC wceq wi vx wal vx
      cA cB csb cC wceq wb cA cV elex cA cvv wcel vx cC wnfc wa vx cv cA wceq
      cB cC wceq wi vx wal vx cA cB csb cC wceq cA cvv wcel vx cC wnfc wa vx cv
      cA wceq cB cC wceq wi vx wal vx cv cA wceq cB cC wceq wi vx cA wsbc vx cA
      cB csb cC wceq cA cvv wcel vx cv cA wceq cB cC wceq wi vx wal vx cv cA
      wceq cB cC wceq wi vx cA wsbc wi vx cC wnfc vx cv cA wceq cB cC wceq wi
      vx cA cvv spsbc adantr cA cvv wcel vx cC wnfc wa vx cv cA wceq cB cC wceq
      wi vx cA cB csb cC wceq vx cA cvv cA cvv wcel vx cC wnfc simpl vx cv cA
      wceq vx cv cA wceq cB cC wceq wi vx cA cB csb cC wceq wb cA cvv wcel vx
      cC wnfc wa vx cv cA wceq cB cC wceq vx cv cA wceq cB cC wceq wi vx cA cB
      csb cC wceq vx cv cA wceq cB cC wceq biimt vx cv cA wceq cB vx cA cB csb
      cC vx cA cB csbeq1a eqeq1d bitr3d adantl cA cvv wcel vx cC wnfc vx cA cvv
      wcel vx nfv vx cC nfnfc1 nfan cA cvv wcel vx cC wnfc wa vx vx cA cB csb
      cC vx vx cA cB csb wnfc cA cvv wcel vx cC wnfc wa vx cA cB nfcsb1v a1i cA
      cvv wcel vx cC wnfc simpr nfeqd sbciedf sylibd vx cC wnfc vx cA cB csb cC
      wceq vx cv cA wceq cB cC wceq wi vx wal wi cA cvv wcel vx cC wnfc vx cA
      cB csb cC wceq vx cv cA wceq cB cC wceq wi vx wal vx cC wnfc vx cA cB csb
      cC wceq wa vx cv cA wceq cB cC wceq wi vx vx cC wnfc vx cA cB csb cC wceq
      vx vx cC nfnfc1 vx cC wnfc vx vx cA cB csb cC vx vx cA cB csb wnfc vx cC
      wnfc vx cA cB nfcsb1v a1i vx cC wnfc id nfeqd nfan1 vx cA cB csb cC wceq
      vx cv cA wceq cB cC wceq wi vx cC wnfc vx cv cA wceq cB cC wceq vx cA cB
      csb cC wceq vx cv cA wceq cB vx cA cB csb cC vx cA cB csbeq1a eqeq1d
      biimprcd adantl alrimi ex adantl impbid sylan $.

    csbiedf.1 $e |- F/ x ph $.
    csbiedf.2 $e |- ( ph -> F/_ x C ) $.
    csbiedf.3 $e |- ( ph -> A e. V ) $.
    csbiedf.4 $e |- ( ( ph /\ x = A ) -> B = C ) $.
    $( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by Mario Carneiro, 13-Oct-2016.) $)
    csbiedf $p |- ( ph -> [_ A / x ]_ B = C ) $=
      wph vx cv cA wceq cB cC wceq wi vx wal vx cA cB csb cC wceq wph vx cv cA
      wceq cB cC wceq wi vx csbiedf.1 wph vx cv cA wceq cB cC wceq csbiedf.4 ex
      alrimi wph cA cV wcel vx cC wnfc vx cv cA wceq cB cC wceq wi vx wal vx cA
      cB csb cC wceq wb csbiedf.3 csbiedf.2 vx cA cB cC cV csbiebt syl2anc
      mpbid $.
  $}

  ${
    $d x z A $.  $d z B $.  $d y C $.  $d x y $.
    csbieb.1 $e |- A e. _V $.
    csbieb.2 $e |- F/_ x C $.
    $( Bidirectional conversion between an implicit class substitution
       hypothesis ` x = A -> B = C ` and its explicit substitution equivalent.
       (Contributed by NM, 2-Mar-2008.) $)
    csbieb $p |- ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) $=
      cA cvv wcel vx cC wnfc vx cv cA wceq cB cC wceq wi vx wal vx cA cB csb cC
      wceq wb csbieb.1 csbieb.2 vx cA cB cC cvv csbiebt mp2an $.
  $}

  ${
    $d a x A $.  $d a B $.  $d a y C $.  $d x y $.
    csbiebg.2 $e |- F/_ x C $.
    $( Bidirectional conversion between an implicit class substitution
       hypothesis ` x = A -> B = C ` and its explicit substitution equivalent.
       (Contributed by NM, 24-Mar-2013.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    csbiebg $p |- ( A e. V ->
          ( A. x ( x = A -> B = C ) <-> [_ A / x ]_ B = C ) ) $=
      vx cv va cv wceq cB cC wceq wi vx wal vx va cv cB csb cC wceq vx cv cA
      wceq cB cC wceq wi vx wal vx cA cB csb cC wceq va cA cV va cv cA wceq vx
      cv va cv wceq cB cC wceq wi vx cv cA wceq cB cC wceq wi vx va cv cA wceq
      vx cv va cv wceq vx cv cA wceq cB cC wceq va cv cA vx cv eqeq2 imbi1d
      albidv va cv cA wceq vx va cv cB csb vx cA cB csb cC vx va cv cA cB
      csbeq1 eqeq1d vx va cv cB cC va vex csbiebg.2 csbieb vtoclbg $.
  $}

  ${
    $d x y A $.  $d y C $.  $d x y V $.
    csbiegf.1 $e |- ( A e. V -> F/_ x C ) $.
    csbiegf.2 $e |- ( x = A -> B = C ) $.
    $( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 11-Nov-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)
    csbiegf $p |- ( A e. V -> [_ A / x ]_ B = C ) $=
      cA cV wcel vx cv cA wceq cB cC wceq wi vx wal vx cA cB csb cC wceq vx cv
      cA wceq cB cC wceq wi vx csbiegf.2 ax-gen cA cV wcel vx cC wnfc vx cv cA
      wceq cB cC wceq wi vx wal vx cA cB csb cC wceq wb csbiegf.1 vx cA cB cC
      cV csbiebt mpdan mpbii $.
  $}

  ${
    $d x A $.  $d y C $.  $d x y $.
    csbief.1 $e |- A e. _V $.
    csbief.2 $e |- F/_ x C $.
    csbief.3 $e |- ( x = A -> B = C ) $.
    $( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 26-Nov-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)
    csbief $p |- [_ A / x ]_ B = C $=
      cA cvv wcel vx cA cB csb cC wceq csbief.1 vx cA cB cC cvv vx cC wnfc cA
      cvv wcel csbief.2 a1i csbief.3 csbiegf ax-mp $.
  $}

  ${
    $d x A $.  $d x y C $.  $d x y ph $.
    csbied.1 $e |- ( ph -> A e. V ) $.
    csbied.2 $e |- ( ( ph /\ x = A ) -> B = C ) $.
    $( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by Mario Carneiro, 2-Dec-2014.)  (Revised by Mario
       Carneiro, 13-Oct-2016.) $)
    csbied $p |- ( ph -> [_ A / x ]_ B = C ) $=
      wph vx cA cB cC cV wph vx nfv wph vx cC nfcvd csbied.1 csbied.2 csbiedf
      $.
  $}

  ${
    $d x A $.  $d x ph $.  $d x D $.
    csbied2.1 $e |- ( ph -> A e. V ) $.
    csbied2.2 $e |- ( ph -> A = B ) $.
    csbied2.3 $e |- ( ( ph /\ x = B ) -> C = D ) $.
    $( Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by Mario Carneiro, 2-Jan-2017.) $)
    csbied2 $p |- ( ph -> [_ A / x ]_ C = D ) $=
      wph vx cA cC cD cV csbied2.1 wph vx cv cA wceq vx cv cB wceq cC cD wceq
      vx cv cA wceq wph vx cv cA cB vx cv cA wceq id csbied2.2 sylan9eqr
      csbied2.3 syldan csbied $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d z C $.  $d x y z D $.
    csbie2t.1 $e |- A e. _V $.
    csbie2t.2 $e |- B e. _V $.
    $( Conversion of implicit substitution to explicit substitution into a
       class (closed form of ~ csbie2 ).  (Contributed by NM, 3-Sep-2007.)
       (Revised by Mario Carneiro, 13-Oct-2016.) $)
    csbie2t $p |- ( A. x A. y ( ( x = A /\ y = B ) -> C = D ) ->
                  [_ A / x ]_ [_ B / y ]_ C = D ) $=
      vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx wal vx cA vy cB cC
      csb cD cvv vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx nfa1 vx
      cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx wal vx cD nfcvd cA
      cvv wcel vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx wal
      csbie2t.1 a1i vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx wal
      vx cv cA wceq wa vy cB cC cD cvv vx cv cA wceq vy cv cB wceq wa cC cD
      wceq wi vy wal vx wal vx cv cA wceq vy vx cv cA wceq vy cv cB wceq wa cC
      cD wceq wi vy vx nfa2 vx cv cA wceq vy nfv nfan vx cv cA wceq vy cv cB
      wceq wa cC cD wceq wi vy wal vx wal vx cv cA wceq wa vy cD nfcvd cB cvv
      wcel vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx wal vx cv cA
      wceq wa csbie2t.2 a1i vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal
      vx wal vx cv cA wceq vy cv cB wceq cC cD wceq vx cv cA wceq vy cv cB wceq
      wa cC cD wceq wi vy wal vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vx
      vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy sp sps impl csbiedf
      csbiedf $.

    csbie2.3 $e |- ( ( x = A /\ y = B ) -> C = D ) $.
    $( Conversion of implicit substitution to explicit substitution into a
       class.  (Contributed by NM, 27-Aug-2007.) $)
    csbie2 $p |- [_ A / x ]_ [_ B / y ]_ C = D $=
      vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vy wal vx wal vx cA vy cB cC
      csb csb cD wceq vx cv cA wceq vy cv cB wceq wa cC cD wceq wi vx vy
      csbie2.3 gen2 vx vy cA cB cC cD csbie2t.1 csbie2t.2 csbie2t ax-mp $.
  $}

  ${
    $d x y z $.  $d A y z $.  $d B y z $.  $d C x $.  $d D y z $.  $d V z $.
    csbie2g.1 $e |- ( x = y -> B = C ) $.
    csbie2g.2 $e |- ( y = A -> C = D ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       This version of ~ sbcie avoids a disjointness condition on ` x , A ` by
       substituting twice.  (Contributed by Mario Carneiro, 11-Nov-2016.) $)
    csbie2g $p |- ( A e. V -> [_ A / x ]_ B = D ) $=
      cA cV wcel vx cA cB csb vz cv cB wcel vx cA wsbc vz cab cD vx vz cA cB
      df-csb cA cV wcel vz cv cB wcel vx cA wsbc vz cD vz cv cB wcel vz cv cC
      wcel vz cv cD wcel vx vy cA cV vx cv vy cv wceq cB cC vz cv csbie2g.1
      eleq2d vy cv cA wceq cC cD vz cv csbie2g.2 eleq2d sbcie2g abbi1dv syl5eq
      $.
  $}

  ${
    $d x z $.  $d y z $.  $d z A $.  $d z B $.  $d z C $.  $d z ph $.
    $( Nest the composition of two substitutions.  (Contributed by Mario
       Carneiro, 11-Nov-2016.) $)
    sbcnestgf $p |- ( ( A e. V /\ A. y F/ x ph ) ->
         ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) ) $=
      cA cV wcel wph vx wnf vy wal wph vy cB wsbc vx cA wsbc wph vy vx cA cB
      csb wsbc wb wph vx wnf vy wal wph vy cB wsbc vx vz cv wsbc wph vy vx vz
      cv cB csb wsbc wb wi wph vx wnf vy wal wph vy cB wsbc vx cA wsbc wph vy
      vx cA cB csb wsbc wb wi vz cA cV vz cv cA wceq wph vy cB wsbc vx vz cv
      wsbc wph vy vx vz cv cB csb wsbc wb wph vy cB wsbc vx cA wsbc wph vy vx
      cA cB csb wsbc wb wph vx wnf vy wal vz cv cA wceq wph vy cB wsbc vx vz cv
      wsbc wph vy cB wsbc vx cA wsbc wph vy vx vz cv cB csb wsbc wph vy vx cA
      cB csb wsbc wph vy cB wsbc vx vz cv cA dfsbcq vz cv cA wceq vx vz cv cB
      csb vx cA cB csb wceq wph vy vx vz cv cB csb wsbc wph vy vx cA cB csb
      wsbc wb vx vz cv cA cB csbeq1 wph vy vx vz cv cB csb vx cA cB csb dfsbcq
      syl bibi12d imbi2d wph vx wnf vy wal wph vy cB wsbc wph vy vx vz cv cB
      csb wsbc vx vz cv cvv vz cv cvv wcel wph vx wnf vy wal vz vex a1i vx cv
      vz cv wceq wph vy cB wsbc wph vy vx vz cv cB csb wsbc wb wph vx wnf vy
      wal vx cv vz cv wceq cB vx vz cv cB csb wceq wph vy cB wsbc wph vy vx vz
      cv cB csb wsbc wb vx vz cv cB csbeq1a wph vy cB vx vz cv cB csb dfsbcq
      syl adantl wph vx wnf vx vy wph vx nfnf1 nfal wph vx wnf vy wal wph vx vy
      vx vz cv cB csb wph vx wnf vy nfa1 vx vx vz cv cB csb wnfc wph vx wnf vy
      wal vx vz cv cB nfcsb1v a1i wph vx wnf vy sp nfsbcd sbciedf vtoclg imp $.

    $( Nest the composition of two substitutions.  (Contributed by NM,
       23-Nov-2005.)  (Proof shortened by Mario Carneiro, 10-Nov-2016.) $)
    csbnestgf $p |- ( ( A e. V /\ A. y F/_ x C ) ->
         [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $=
      cA cV wcel vx cC wnfc vy wal wa vz cv vy cB cC csb wcel vx cA wsbc vz cab
      vz cv cC wcel vy vx cA cB csb wsbc vz cab vx cA vy cB cC csb csb vy vx cA
      cB csb cC csb cA cV wcel cA cvv wcel vx cC wnfc vy wal vz cv vy cB cC csb
      wcel vx cA wsbc vz cab vz cv cC wcel vy vx cA cB csb wsbc vz cab wceq cA
      cV elex cA cvv wcel vx cC wnfc vy wal wa vz cv vy cB cC csb wcel vx cA
      wsbc vz cv cC wcel vy vx cA cB csb wsbc vz vz cv vy cB cC csb wcel vx cA
      wsbc vz cv cC wcel vy cB wsbc vx cA wsbc cA cvv wcel vx cC wnfc vy wal wa
      vz cv cC wcel vy vx cA cB csb wsbc vz cv vy cB cC csb wcel vz cv cC wcel
      vy cB wsbc vx cA vz cv cC wcel vy cB wsbc vz vy cB cC csb vy vz cB cC
      df-csb abeq2i sbcbii vx cC wnfc vy wal cA cvv wcel vz cv cC wcel vx wnf
      vy wal vz cv cC wcel vy cB wsbc vx cA wsbc vz cv cC wcel vy vx cA cB csb
      wsbc wb vx cC wnfc vz cv cC wcel vx wnf vy vx vz cC nfcr alimi vz cv cC
      wcel vx vy cA cB cvv sbcnestgf sylan2 syl5bb abbidv sylan vx vz cA vy cB
      cC csb df-csb vy vz vx cA cB csb cC df-csb 3eqtr4g $.

    $d x ph $.
    $( Nest the composition of two substitutions.  (Contributed by NM,
       27-Nov-2005.)  (Proof shortened by Mario Carneiro, 11-Nov-2016.) $)
    sbcnestg $p |- ( A e. V ->
          ( [. A / x ]. [. B / y ]. ph <-> [. [_ A / x ]_ B / y ]. ph ) ) $=
      cA cV wcel wph vx wnf vy wal wph vy cB wsbc vx cA wsbc wph vy vx cA cB
      csb wsbc wb wph vx wnf vy wph vx nfv ax-gen wph vx vy cA cB cV sbcnestgf
      mpan2 $.

    $d x C $.
    $( Nest the composition of two substitutions.  (Contributed by NM,
       23-Nov-2005.)  (Proof shortened by Mario Carneiro, 10-Nov-2016.) $)
    csbnestg $p |- ( A e. V ->
          [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $=
      cA cV wcel vx cC wnfc vy wal vx cA vy cB cC csb csb vy vx cA cB csb cC
      csb wceq vx cC wnfc vy vx cC nfcv ax-gen vx vy cA cB cC cV csbnestgf
      mpan2 $.
  $}

  ${
    $d x C $.
    $( Nest the composition of two substitutions.  (New usage is discouraged.)
       (Contributed by NM, 23-Nov-2005.) $)
    csbnestgOLD $p |- ( ( A e. V /\ A. x B e. W ) ->
                  [_ A / x ]_ [_ B / y ]_ C = [_ [_ A / x ]_ B / y ]_ C ) $=
      cA cV wcel vx cA vy cB cC csb csb vy vx cA cB csb cC csb wceq cB cW wcel
      vx wal vx vy cA cB cC cV csbnestg adantr $.
  $}

  ${
    $d x y $.  $d y C $.
    $( Nest the composition of two substitutions.  (Contributed by NM,
       23-May-2006.)  (Proof shortened by Mario Carneiro, 11-Nov-2016.) $)
    csbnest1g $p |- ( A e. V ->
         [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C ) $=
      cA cV wcel vx cA vy cB vx vy cv cC csb csb csb vy vx cA cB csb vx vy cv
      cC csb csb vx cA vx cB cC csb csb vx vx cA cB csb cC csb cA cV wcel vx vx
      vy cv cC csb wnfc vy wal vx cA vy cB vx vy cv cC csb csb csb vy vx cA cB
      csb vx vy cv cC csb csb wceq vx vx vy cv cC csb wnfc vy vx vy cv cC
      nfcsb1v ax-gen vx vy cA cB vx vy cv cC csb cV csbnestgf mpan2 vx cA vy cB
      vx vy cv cC csb csb vx cB cC csb vx vy cB cC csbco csbeq2i vx vy vx cA cB
      csb cC csbco 3eqtr3g $.
  $}

  ${
    $d x y A $.  $d y B $.  $d y C $.  $d y W $.
    $( Nest the composition of two substitutions.  Obsolete as of 11-Nov-2016.
       (Contributed by NM, 23-May-2006.)  (New usage is discouraged.) $)
    csbnest1gOLD $p |- ( ( A e. V /\ A. x B e. W ) ->
                  [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C ) $=
      cA cV wcel vx cA vx cB cC csb csb vx vx cA cB csb cC csb wceq cB cW wcel
      vx wal vx cA cB cC cV csbnest1g adantr $.
  $}

  ${
    $d x A $.
    $( Idempotent law for class substitutions.  (Contributed by NM,
       1-Mar-2008.) $)
    csbidmg $p |- ( A e. V -> [_ A / x ]_ [_ A / x ]_ B = [_ A / x ]_ B ) $=
      cA cV wcel cA cvv wcel vx cA vx cA cB csb csb vx cA cB csb wceq cA cV
      elex cA cvv wcel vx cA vx cA cB csb csb vx vx cA cA csb cB csb vx cA cB
      csb vx cA cA cB cvv csbnest1g cA cvv wcel vx vx cA cA csb cA cB vx cA cA
      cvv csbconstg csbeq1d eqtrd syl $.
  $}

  ${
    $d x A $.  $d x ph $.  $d x C $.  $d x D $.
    sbcco3g.1 $e |- ( x = A -> B = C ) $.
    $( Composition of two substitutions.  (Contributed by NM, 27-Nov-2005.)
       (Revised by Mario Carneiro, 11-Nov-2016.) $)
    sbcco3g $p |- ( A e. V ->
         ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) ) $=
      cA cV wcel wph vy cB wsbc vx cA wsbc wph vy vx cA cB csb wsbc wph vy cC
      wsbc wph vx vy cA cB cV sbcnestg cA cV wcel cA cvv wcel vx cA cB csb cC
      wceq wph vy vx cA cB csb wsbc wph vy cC wsbc wb cA cV elex vx cA cB cC
      cvv cA cvv wcel vx cC nfcvd sbcco3g.1 csbiegf wph vy vx cA cB csb cC
      dfsbcq 3syl bitrd $.

    $( Composition of two substitutions.  (Contributed by NM, 27-Nov-2005.)
       (New usage is discouraged.) $)
    sbcco3gOLD $p |- ( ( A e. V /\ A. x B e. W ) ->
                ( [. A / x ]. [. B / y ]. ph <-> [. C / y ]. ph ) ) $=
      cA cV wcel wph vy cB wsbc vx cA wsbc wph vy cC wsbc wb cB cW wcel vx wal
      wph vx vy cA cB cC cV sbcco3g.1 sbcco3g adantr $.

    $( Composition of two class substitutions.  (Contributed by NM,
       27-Nov-2005.)  (Revised by Mario Carneiro, 11-Nov-2016.) $)
    csbco3g $p |- ( A e. V ->
                 [_ A / x ]_ [_ B / y ]_ D = [_ C / y ]_ D ) $=
      cA cV wcel vx cA vy cB cD csb csb vy vx cA cB csb cD csb vy cC cD csb vx
      vy cA cB cD cV csbnestg cA cV wcel vy vx cA cB csb cC cD cA cV wcel cA
      cvv wcel vx cA cB csb cC wceq cA cV elex vx cA cB cC cvv cA cvv wcel vx
      cC nfcvd sbcco3g.1 csbiegf syl csbeq1d eqtrd $.
  $}

  ${
    $d x A $.  $d x C $.  $d x z D $.  $d x y $.
    csbco3g.1 $e |- ( x = A -> B = D ) $.
    $( Composition of two class substitutions.  Obsolete as of 11-Nov-2016.
       (Contributed by NM, 27-Nov-2005.)  (New usage is discouraged.) $)
    csbco3gOLD $p |- ( ( A e. V /\ A. x B e. W ) ->
                 [_ A / x ]_ [_ B / y ]_ C = [_ D / y ]_ C ) $=
      cA cV wcel vx cA vy cB cC csb csb vy cD cC csb wceq cB cW wcel vx wal vx
      vy cA cB cD cC cV csbco3g.1 csbco3g adantr $.
  $}

  ${
    $d x B $.  $d x D $.
    $( Special case related to ~ rspsbc .  (Contributed by NM, 10-Dec-2005.)
       (Proof shortened by Eric Schmidt, 17-Jan-2007.) $)
    rspcsbela $p |- ( ( A e. B /\ A. x e. B C e. D ) -> [_ A / x ]_ C e. D ) $=
      cA cB wcel cC cD wcel vx cB wral vx cA cC csb cD wcel cA cB wcel cC cD
      wcel vx cB wral cC cD wcel vx cA wsbc vx cA cC csb cD wcel cC cD wcel vx
      cA cB rspsbc vx cA cC cD cB sbcel1g sylibd imp $.
  $}

  ${
    $d w x y z $.  $d w y z A $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` A ` ."
       (Contributed by Mario Carneiro, 14-Oct-2016.) $)
    sbnfc2 $p |- ( F/_ x A <-> A. y A. z [_ y / x ]_ A = [_ z / x ]_ A ) $=
      vx cA wnfc vx vy cv cA csb vx vz cv cA csb wceq vz wal vy wal vx cA wnfc
      vx vy cv cA csb vx vz cv cA csb wceq vy vz vx cA wnfc vx vy cv cA csb cA
      vx vz cv cA csb vy cv cvv wcel vx cA wnfc vx vy cv cA csb cA wceq vy vex
      vx vy cv cA cvv csbtt mpan vz cv cvv wcel vx cA wnfc vx vz cv cA csb cA
      wceq vz vex vx vz cv cA cvv csbtt mpan eqtr4d alrimivv vx vy cv cA csb vx
      vz cv cA csb wceq vz wal vy wal vx vw cA vx vy cv cA csb vx vz cv cA csb
      wceq vz wal vy wal vw nfv vx vy cv cA csb vx vz cv cA csb wceq vz wal vy
      wal vw cv cA wcel vx vy wsb vw cv cA wcel vx vz wsb wb vz wal vy wal vw
      cv cA wcel vx wnf vx vy cv cA csb vx vz cv cA csb wceq vw cv cA wcel vx
      vy wsb vw cv cA wcel vx vz wsb wb vy vz vx vy cv cA csb vx vz cv cA csb
      wceq vw cv vx vy cv cA csb wcel vw cv vx vz cv cA csb wcel vw cv cA wcel
      vx vy wsb vw cv cA wcel vx vz wsb vx vy cv cA csb vx vz cv cA csb vw cv
      eleq2 vw cv cA wcel vx vy wsb vw cv cA wcel vx vy cv wsbc vw cv vx vy cv
      cA csb wcel vw cv cA wcel vx vy sbsbc vy cv cvv wcel vw cv cA wcel vx vy
      cv wsbc vw cv vx vy cv cA csb wcel wb vy vex vx vy cv vw cv cA cvv
      sbcel2g ax-mp bitri vw cv cA wcel vx vz wsb vw cv cA wcel vx vz cv wsbc
      vw cv vx vz cv cA csb wcel vw cv cA wcel vx vz sbsbc vz cv cvv wcel vw cv
      cA wcel vx vz cv wsbc vw cv vx vz cv cA csb wcel wb vz vex vx vz cv vw cv
      cA cvv sbcel2g ax-mp bitri 3bitr4g 2alimi vw cv cA wcel vx vy vz sbnf2
      sylibr nfcd impbii $.
  $}

  ${
    $d y z A $.  $d z ph $.  $d x y z $.  $d V z $.
    $( Move substitution into a class abstraction.  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    csbabg $p |- ( A e. V ->
                 [_ A / x ]_ { y | ph } = { y | [. A / x ]. ph } ) $=
      cA cV wcel vz vx cA wph vy cab csb wph vx cA wsbc vy cab vz cv wph vx cA
      wsbc vy cab wcel vz cv wph vy cab wcel vx cA wsbc cA cV wcel vz cv vx cA
      wph vy cab csb wcel wph vx cA wsbc vy vz cv wsbc wph vy vz cv wsbc vx cA
      wsbc vz cv wph vx cA wsbc vy cab wcel vz cv wph vy cab wcel vx cA wsbc
      wph vy vx vz cv cA sbccom vz cv wph vx cA wsbc vy cab wcel wph vx cA wsbc
      vy vz wsb wph vx cA wsbc vy vz cv wsbc wph vx cA wsbc vz vy df-clab wph
      vx cA wsbc vy vz sbsbc bitri vz cv wph vy cab wcel wph vy vz cv wsbc vx
      cA vz cv wph vy cab wcel wph vy vz wsb wph vy vz cv wsbc wph vz vy
      df-clab wph vy vz sbsbc bitri sbcbii 3bitr4i vx cA vz cv wph vy cab cV
      sbcel2g syl5rbb eqrdv $.
  $}

  ${
    $d x v z $.  $d y v z $.  $d A w v z $.  $d B w v z $.  $d ph v z $.
    $d ps v z $.
    cbvralcsf.1 $e |- F/_ y A $.
    cbvralcsf.2 $e |- F/_ x B $.
    cbvralcsf.3 $e |- F/ y ph $.
    cbvralcsf.4 $e |- F/ x ps $.
    cbvralcsf.5 $e |- ( x = y -> A = B ) $.
    cbvralcsf.6 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A more general version of ~ cbvralf that doesn't require ` A ` and ` B `
       to be distinct from ` x ` or ` y ` .  Changes bound variables using
       implicit substitution.  (Contributed by Andrew Salmon, 13-Jul-2011.) $)
    cbvralcsf $p |- ( A. x e. A ph <-> A. y e. B ps ) $=
      vx cv cA wcel wph wi vx wal vy cv cB wcel wps wi vy wal wph vx cA wral
      wps vy cB wral vx cv cA wcel wph wi vx wal vz cv vx vz cv cA csb wcel wph
      vx vz cv wsbc wi vz wal vy cv cB wcel wps wi vy wal vx cv cA wcel wph wi
      vz cv vx vz cv cA csb wcel wph vx vz cv wsbc wi vx vz vx cv cA wcel wph
      wi vz nfv vz cv vx vz cv cA csb wcel wph vx vz cv wsbc vx vx vz vx vz cv
      cA csb vx vz cv cA nfcsb1v nfcri wph vx vz cv nfsbc1v nfim vx cv vz cv
      wceq vx cv cA wcel vz cv vx vz cv cA csb wcel wph wph vx vz cv wsbc vx cv
      vz cv wceq vx cv vz cv cA vx vz cv cA csb vx cv vz cv wceq id vx vz cv cA
      csbeq1a eleq12d wph vx vz cv sbceq1a imbi12d cbval vz cv vx vz cv cA csb
      wcel wph vx vz cv wsbc wi vy cv cB wcel wps wi vz vy vz cv vx vz cv cA
      csb wcel wph vx vz cv wsbc vy vy vz vx vz cv cA csb vy vx vz cv cA vy vz
      cv nfcv cbvralcsf.1 nfcsb nfcri wph vy vx vz cv vy vz cv nfcv cbvralcsf.3
      nfsbc nfim vy cv cB wcel wps wi vz nfv vz cv vy cv wceq vz cv vx vz cv cA
      csb wcel vy cv cB wcel wph vx vz cv wsbc wps vz cv vy cv wceq vz cv vy cv
      vx vz cv cA csb cB vz cv vy cv wceq id vz cv vy cv wceq vx vz cv cA csb
      vx vy cv cA csb cB vx vz cv vy cv cA csbeq1 vx vy cv cA csb vv cv cA wcel
      vx vy cv wsbc vv cab cB vx vv vy cv cA df-csb vv cv cA wcel vx vy cv wsbc
      vv cB vv cv cB wcel vv cv cA wcel vx vy wsb vv cv cA wcel vx vy cv wsbc
      vv cv cA wcel vv cv cB wcel vx vy vx vv cB cbvralcsf.2 nfcri vx vy weq cA
      cB vv cv cbvralcsf.5 eleq2d sbie vv cv cA wcel vx vy sbsbc bitr3i abbi2i
      eqtr4i syl6eq eleq12d vz cv vy cv wceq wph vx vz cv wsbc wph vx vy cv
      wsbc wps wph vx vz cv vy cv dfsbcq wph vx vy cv wsbc wph vx vy wsb wps
      wph vx vy sbsbc wph wps vx vy cbvralcsf.4 cbvralcsf.6 sbie bitr3i syl6bb
      imbi12d cbval bitri wph vx cA df-ral wps vy cB df-ral 3bitr4i $.

    $( A more general version of ~ cbvrexf that has no distinct variable
       restrictions.  Changes bound variables using implicit substitution.
       (Contributed by Andrew Salmon, 13-Jul-2011.)  (Proof shortened by Mario
       Carneiro, 7-Dec-2014.) $)
    cbvrexcsf $p |- ( E. x e. A ph <-> E. y e. B ps ) $=
      wph wn vx cA wral wn wps wn vy cB wral wn wph vx cA wrex wps vy cB wrex
      wph wn vx cA wral wps wn vy cB wral wph wn wps wn vx vy cA cB cbvralcsf.1
      cbvralcsf.2 wph vy cbvralcsf.3 nfn wps vx cbvralcsf.4 nfn cbvralcsf.5 vx
      cv vy cv wceq wph wps cbvralcsf.6 notbid cbvralcsf notbii wph vx cA
      dfrex2 wps vy cB dfrex2 3bitr4i $.

    $( A more general version of ~ cbvreuv that has no distinct variable
       rextrictions.  Changes bound variables using implicit substitution.
       (Contributed by Andrew Salmon, 13-Jul-2011.) $)
    cbvreucsf $p |- ( E! x e. A ph <-> E! y e. B ps ) $=
      vx cv cA wcel wph wa vx weu vy cv cB wcel wps wa vy weu wph vx cA wreu
      wps vy cB wreu vx cv cA wcel wph wa vx weu vz cv vx vz cv cA csb wcel wph
      vx vz wsb wa vz weu vy cv cB wcel wps wa vy weu vx cv cA wcel wph wa vz
      cv vx vz cv cA csb wcel wph vx vz wsb wa vx vz vx cv cA wcel wph wa vz
      nfv vz cv vx vz cv cA csb wcel wph vx vz wsb vx vx vz vx vz cv cA csb vx
      vz cv cA nfcsb1v nfcri wph vx vz nfs1v nfan vx cv vz cv wceq vx cv cA
      wcel vz cv vx vz cv cA csb wcel wph wph vx vz wsb vx cv vz cv wceq vx cv
      vz cv cA vx vz cv cA csb vx cv vz cv wceq id vx vz cv cA csbeq1a eleq12d
      wph vx vz sbequ12 anbi12d cbveu vz cv vx vz cv cA csb wcel wph vx vz wsb
      wa vy cv cB wcel wps wa vz vy vz cv vx vz cv cA csb wcel wph vx vz wsb vy
      vy vz vx vz cv cA csb vy vx vz cv cA vy vz cv nfcv cbvralcsf.1 nfcsb
      nfcri wph vx vz vy cbvralcsf.3 nfsb nfan vy cv cB wcel wps wa vz nfv vz
      cv vy cv wceq vz cv vx vz cv cA csb wcel vy cv cB wcel wph vx vz wsb wps
      vz cv vy cv wceq vz cv vy cv vx vz cv cA csb cB vz cv vy cv wceq id vz cv
      vy cv wceq vx vz cv cA csb vx vy cv cA csb cB vx vz cv vy cv cA csbeq1 vv
      cv cA wcel vx vy wsb vv cab vv cv cA wcel vx vy cv wsbc vv cab cB vx vy
      cv cA csb vv cv cA wcel vx vy wsb vv cv cA wcel vx vy cv wsbc vv vv cv cA
      wcel vx vy sbsbc abbii vv cv cA wcel vx vy wsb vv cB vv cv cA wcel vx vy
      wsb vv cv cB wcel vv cv cA wcel vv cv cB wcel vx vy vx vv cB cbvralcsf.2
      nfcri vx cv vy cv wceq cA cB vv cv cbvralcsf.5 eleq2d sbie bicomi abbi2i
      vx vv vy cv cA df-csb 3eqtr4ri syl6eq eleq12d vz cv vy cv wceq wph vx vz
      wsb wph vx vy wsb wps wph vz vy vx sbequ wph wps vx vy cbvralcsf.4
      cbvralcsf.6 sbie syl6bb anbi12d cbveu bitri wph vx cA df-reu wps vy cB
      df-reu 3bitr4i $.

    $( A more general version of ~ cbvrab with no distinct variable
       restrictions.  (Contributed by Andrew Salmon, 13-Jul-2011.) $)
    cbvrabcsf $p |- { x e. A | ph } = { y e. B | ps } $=
      vx cv cA wcel wph wa vx cab vy cv cB wcel wps wa vy cab wph vx cA crab
      wps vy cB crab vx cv cA wcel wph wa vx cab vz cv vx vz cv cA csb wcel wph
      vx vz wsb wa vz cab vy cv cB wcel wps wa vy cab vx cv cA wcel wph wa vz
      cv vx vz cv cA csb wcel wph vx vz wsb wa vx vz vx cv cA wcel wph wa vz
      nfv vz cv vx vz cv cA csb wcel wph vx vz wsb vx vx vz vx vz cv cA csb vx
      vz cv cA nfcsb1v nfcri wph vx vz nfs1v nfan vx cv vz cv wceq vx cv cA
      wcel vz cv vx vz cv cA csb wcel wph wph vx vz wsb vx cv vz cv wceq vx cv
      vz cv cA vx vz cv cA csb vx cv vz cv wceq id vx vz cv cA csbeq1a eleq12d
      wph vx vz sbequ12 anbi12d cbvab vz cv vx vz cv cA csb wcel wph vx vz wsb
      wa vy cv cB wcel wps wa vz vy vz cv vx vz cv cA csb wcel wph vx vz wsb vy
      vy vz vx vz cv cA csb vy vx vz cv cA vy vz cv nfcv cbvralcsf.1 nfcsb
      nfcri wph vx vz vy cbvralcsf.3 nfsb nfan vy cv cB wcel wps wa vz nfv vz
      cv vy cv wceq vz cv vx vz cv cA csb wcel vy cv cB wcel wph vx vz wsb wps
      vz cv vy cv wceq vz cv vy cv vx vz cv cA csb cB vz cv vy cv wceq id vz cv
      vy cv wceq vx vz cv cA csb vx vy cv cA csb cB vx vz cv vy cv cA csbeq1 vx
      vy cv cA csb vv cv cA wcel vx vy cv wsbc vv cab cB vx vv vy cv cA df-csb
      vv cv cA wcel vx vy cv wsbc vv cB vv cv cB wcel vv cv cA wcel vx vy wsb
      vv cv cA wcel vx vy cv wsbc vv cv cA wcel vv cv cB wcel vx vy vx vv cB
      cbvralcsf.2 nfcri vx vy weq cA cB vv cv cbvralcsf.5 eleq2d sbie vv cv cA
      wcel vx vy sbsbc bitr3i abbi2i eqtr4i syl6eq eleq12d vz cv vy cv wceq wph
      vx vz wsb wph vx vy wsb wps wph vz vy vx sbequ wph wps vx vy cbvralcsf.4
      cbvralcsf.6 sbie syl6bb anbi12d cbvab eqtri wph vx cA df-rab wps vy cB
      df-rab 3eqtr4i $.
  $}

  ${
    $d A y $.  $d ps y $.  $d B x $.  $d ch x $.
    cbvralv2.1 $e |- ( x = y -> ( ps <-> ch ) ) $.
    cbvralv2.2 $e |- ( x = y -> A = B ) $.
    $( Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution which also changes the quantifier
       domain.  (Contributed by David Moews, 1-May-2017.) $)
    cbvralv2 $p |- ( A. x e. A ps <-> A. y e. B ch ) $=
      wps wch vx vy cA cB vy cA nfcv vx cB nfcv wps vy nfv wch vx nfv
      cbvralv2.2 cbvralv2.1 cbvralcsf $.

    $( Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution which also changes the quantifier
       domain.  (Contributed by David Moews, 1-May-2017.) $)
    cbvrexv2 $p |- ( E. x e. A ps <-> E. y e. B ch ) $=
      wps wch vx vy cA cB vy cA nfcv vx cB nfcv wps vy nfv wch vx nfv
      cbvralv2.2 cbvralv2.1 cbvrexcsf $.
  $}



