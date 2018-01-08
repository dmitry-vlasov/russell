
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Cantor_s_Theorem.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
      Undefined values and restricted iota (description binder)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c Undef $.
  $c iota_ $.

  $( Extend class notation with undefined value function. $)
  cund $a class Undef $.

  $( Extend class notation with restricted description binder. $)
  crio $a class ( iota_ x e. A ph ) $.

  $( Define the undefined value function, whose value at set ` s ` is
     guaranteed not to be a member of ` s ` (see ~ pwuninel ).  (Contributed by
     NM, 15-Sep-2011.) $)
  df-undef $a |- Undef = ( s e. _V |-> ~P U. s ) $.

  $( Direct proof of ~ pwuninel avoiding functions and thus several ZF axioms.
     (Contributed by Stefan O'Rear, 22-Feb-2015.) $)
  pwuninel2 $p |- ( U. A e. V -> -. ~P U. A e. A ) $=
    cA cuni cV wcel cA cuni cpw cA cuni wss cA cuni cpw cA wcel cA cuni cV
    pwnss cA cuni cpw cA elssuni nsyl $.

  $( The power set of the union of a set does not belong to the set.  This
     theorem provides a way of constructing a new set that doesn't belong to a
     given set.  See also ~ pwuninel2 .  (Contributed by NM, 27-Jun-2008.)
     (Proof shortened by Mario Carneiro, 23-Dec-2016.) $)
  pwuninel $p |- -. ~P U. A e. A $=
    cA cuni cpw cA wcel cA cuni cpw cA wcel wn cA cuni cpw cA wcel cA cuni cvv
    wcel cA cuni cpw cA wcel wn cA cuni cpw cA wcel cA cuni cpw cvv wcel cA
    cuni cvv wcel cA cuni cpw cA elex cA cuni pwexb sylibr cA cvv pwuninel2 syl
    cA cuni cpw cA wcel wn id pm2.61i $.

  ${
    $d s S $.
    $( Value of the undefined value function.  Normally we will not reference
       the explicit value but will use ~ undefnel instead.  (Contributed by NM,
       15-Sep-2011.)  (Revised by Mario Carneiro, 24-Dec-2016.) $)
    undefval $p |- ( S e. V -> ( Undef ` S ) = ~P U. S ) $=
      cS cV wcel cS cvv wcel cS cuni cpw cvv wcel cS cund cfv cS cuni cpw wceq
      cS cV elex cS cV wcel cS cuni cvv wcel cS cuni cpw cvv wcel cS cV uniexg
      cS cuni cvv pwexg syl vs cS vs cv cuni cpw cS cuni cpw cvv cvv cund vs cv
      cS wceq vs cv cuni cS cuni vs cv cS unieq pweqd vs df-undef fvmptg
      syl2anc $.
  $}

  $( The undefined value generated from a set is not a member of the set.
     (Contributed by NM, 15-Sep-2011.) $)
  undefnel2 $p |- ( S e. V -> -. ( Undef ` S ) e. S ) $=
    cS cV wcel cS cund cfv cS wcel cS cuni cpw cS wcel cS pwuninel cS cV wcel
    cS cund cfv cS cuni cpw cS cS cV undefval eleq1d mtbiri $.

  $( The undefined value generated from a set is not a member of the set.
     (Contributed by NM, 15-Sep-2011.) $)
  undefnel $p |- ( S e. V -> ( Undef ` S ) e/ S ) $=
    cS cV wcel cS cund cfv cS wcel wn cS cund cfv cS wnel cS cV undefnel2 cS
    cund cfv cS df-nel sylibr $.

  ${
    $( Define restricted description binder.  In case it doesn't exist, we
       return a set which is not a member of the domain of discourse ` A ` .
       See also comments for ~ df-iota .  (Contributed by NM, 15-Sep-2011.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    df-riota $a |- ( iota_ x e. A ph ) = if ( E! x e. A ph ,
      ( iota x ( x e. A /\ ph ) ) , ( Undef ` { x | x e. A } ) ) $.
  $}

  ${
    $d x ph $.
    riotaeqdv.1 $e |- ( ph -> A = B ) $.
    $( Formula-building deduction rule for iota.  (Contributed by NM,
       15-Sep-2011.) $)
    riotaeqdv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ps ) ) $=
      wph wps vx cA wreu vx cv cA wcel wps wa vx cio vx cv cA wcel vx cab cund
      cfv cif wps vx cB wreu vx cv cB wcel wps wa vx cio vx cv cB wcel vx cab
      cund cfv cif wps vx cA crio wps vx cB crio wph wps vx cA wreu wps vx cB
      wreu vx cv cA wcel wps wa vx cio vx cv cA wcel vx cab cund cfv vx cv cB
      wcel wps wa vx cio vx cv cB wcel vx cab cund cfv wph vx cv cA wcel wps wa
      vx weu vx cv cB wcel wps wa vx weu wps vx cA wreu wps vx cB wreu wph vx
      cv cA wcel wps wa vx cv cB wcel wps wa vx wph vx cv cA wcel vx cv cB wcel
      wps wph cA cB vx cv riotaeqdv.1 eleq2d anbi1d eubidv wps vx cA df-reu wps
      vx cB df-reu 3bitr4g wph vx cv cA wcel wps wa vx cv cB wcel wps wa vx wph
      vx cv cA wcel vx cv cB wcel wps wph cA cB vx cv riotaeqdv.1 eleq2d anbi1d
      iotabidv wph vx cv cA wcel vx cab vx cv cB wcel vx cab cund wph vx cv cA
      wcel vx cv cB wcel vx wph cA cB vx cv riotaeqdv.1 eleq2d abbidv fveq2d
      ifbieq12d wps vx cA df-riota wps vx cB df-riota 3eqtr4g $.
  $}

  ${
    $d x ph $.
    riotabidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building deduction rule for restricted iota.  (Contributed by
       NM, 15-Sep-2011.) $)
    riotabidv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) ) $=
      wph wps vx cA wreu vx cv cA wcel wps wa vx cio vx cv cA wcel vx cab cund
      cfv cif wch vx cA wreu vx cv cA wcel wch wa vx cio vx cv cA wcel vx cab
      cund cfv cif wps vx cA crio wch vx cA crio wph wps vx cA wreu wch vx cA
      wreu vx cv cA wcel wps wa vx cio vx cv cA wcel vx cab cund cfv vx cv cA
      wcel wch wa vx cio vx cv cA wcel vx cab cund cfv wph wps wch vx cA
      riotabidv.1 reubidv wph vx cv cA wcel wps wa vx cv cA wcel wch wa vx wph
      wps wch vx cv cA wcel riotabidv.1 anbi2d iotabidv wph vx cv cA wcel vx
      cab cund cfv eqidd ifbieq12d wps vx cA df-riota wch vx cA df-riota
      3eqtr4g $.
  $}

  ${
    $d x ph $.
    riotaeqbidv.1 $e |- ( ph -> A = B ) $.
    riotaeqbidv.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 15-Sep-2011.) $)
    riotaeqbidv $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. B ch ) ) $=
      wph wps vx cA crio wch vx cA crio wch vx cB crio wph wps wch vx cA
      riotaeqbidv.2 riotabidv wph wch vx cA cB riotaeqbidv.1 riotaeqdv eqtrd $.
  $}

  $( Restricted iota is a set.  (Contributed by NM, 15-Sep-2011.) $)
  riotaex $p |- ( iota_ x e. A ps ) e. _V $=
    wps vx cA crio wps vx cA wreu vx cv cA wcel wps wa vx cio vx cv cA wcel vx
    cab cund cfv cif cvv wps vx cA df-riota wps vx cA wreu vx cv cA wcel wps wa
    vx cio vx cv cA wcel vx cab cund cfv vx cv cA wcel wps wa vx iotaex vx cv
    cA wcel vx cab cund fvex ifex eqeltri $.

  $( An iota restricted to the universe is unrestricted.  (Contributed by NM,
     18-Sep-2011.) $)
  riotav $p |- ( iota_ x e. _V ph ) = ( iota x ph ) $=
    wph vx cvv crio wph vx cvv wreu vx cv cvv wcel wph wa vx cio vx cv cvv wcel
    vx cab cund cfv cif wph vx cio wph vx cvv df-riota wph vx cvv wreu wph vx
    cio wph vx cvv wreu vx cv cvv wcel wph wa vx cio vx cv cvv wcel vx cab cund
    cfv cif wceq wph vx cvv wreu wph vx cvv wreu vx cv cvv wcel wph wa vx cio
    vx cv cvv wcel vx cab cund cfv cif vx cv cvv wcel wph wa vx cio wph vx cio
    wph vx cvv wreu vx cv cvv wcel wph wa vx cio vx cv cvv wcel vx cab cund cfv
    iftrue wph vx cv cvv wcel wph wa vx vx cv cvv wcel wph vx vex biantrur
    iotabii syl6reqr wph vx cvv wreu wn wph vx cio vx cv cvv wcel vx cab cund
    cfv wph vx cvv wreu vx cv cvv wcel wph wa vx cio vx cv cvv wcel vx cab cund
    cfv cif wph vx cvv wreu wn wph vx cio c0 vx cv cvv wcel vx cab cund cfv wph
    vx cvv wreu wph vx weu wph vx cio c0 wceq wph vx reuv wph vx iotanul sylnbi
    vx cv cvv wcel vx cab cund cfv cvv cund cfv c0 vx cv cvv wcel vx cab cvv
    cund vx cvv abid2 fveq2i cvv cvv wcel wn cvv cund cfv c0 wceq vprc cvv cund
    fvprc ax-mp eqtri syl6eqr wph vx cvv wreu vx cv cvv wcel wph wa vx cio vx
    cv cvv wcel vx cab cund cfv iffalse eqtr4d pm2.61i eqtr4i $.

  $( Restricted iota in terms of iota.  (Contributed by NM, 15-Sep-2011.) $)
  riotaiota $p |- ( E! x e. A ph
         -> ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) ) ) $=
    wph vx cA wreu wph vx cA crio wph vx cA wreu vx cv cA wcel wph wa vx cio vx
    cv cA wcel vx cab cund cfv cif vx cv cA wcel wph wa vx cio wph vx cA
    df-riota wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv cA wcel vx cab
    cund cfv iftrue syl5eq $.

  $( Restricted iota in terms of class union.  (Contributed by NM,
     11-Oct-2011.) $)
  riotauni $p |- ( E! x e. A ph
                    -> ( iota_ x e. A ph ) = U. { x e. A | ph } ) $=
    wph vx cA wreu wph vx cA crio vx cv cA wcel wph wa vx cio wph vx cA crab
    cuni wph vx cA riotaiota wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv
    cA wcel wph wa vx cab cuni wph vx cA crab cuni wph vx cA wreu vx cv cA wcel
    wph wa vx weu vx cv cA wcel wph wa vx cio vx cv cA wcel wph wa vx cab cuni
    wceq wph vx cA df-reu vx cv cA wcel wph wa vx iotauni sylbi wph vx cA crab
    vx cv cA wcel wph wa vx cab wph vx cA df-rab unieqi syl6eqr eqtrd $.

  ${
    $d x y A $.  $d y ph $.
    $( The abstraction variable in a restricted iota descriptor isn't free.
       (Contributed by NM, 12-Oct-2011.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
    nfriota1 $p |- F/_ x ( iota_ x e. A ph ) $=
      vx wph vx cA crio wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv cA
      wcel vx cab cund cfv cif wph vx cA df-riota wph vx cA wreu vx vx cv cA
      wcel wph wa vx cio vx cv cA wcel vx cab cund cfv wph vx cA nfreu1 vx cv
      cA wcel wph wa vx nfiota1 vx vx cv cA wcel vx cab cund vx cund nfcv vx cv
      cA wcel vx nfab1 nffv nfif nfcxfr $.
  $}

  ${
    nfriotad.1 $e |- F/ y ph $.
    nfriotad.2 $e |- ( ph -> F/ x ps ) $.
    nfriotad.3 $e |- ( ph -> F/_ x A ) $.
    $( Deduction version of ~ nfriota .  (Contributed by NM, 18-Feb-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    nfriotad $p |- ( ph -> F/_ x ( iota_ y e. A ps ) ) $=
      wph vx wps vy cA crio wps vy cA wreu vy cv cA wcel wps wa vy cio vy cv cA
      wcel vy cab cund cfv cif wps vy cA df-riota wph wps vy cA wreu vx vy cv
      cA wcel wps wa vy cio vy cv cA wcel vy cab cund cfv wph wps vx vy cA
      nfriotad.1 nfriotad.3 nfriotad.2 nfreud wph vx cv vy cv wceq vx wal vx vy
      cv cA wcel wps wa vy cio wnfc wph vx cv vy cv wceq vx wal wn vx vy cv cA
      wcel wps wa vy cio wnfc wph vx cv vy cv wceq vx wal wn wa vy cv cA wcel
      wps wa vx vy wph vx cv vy cv wceq vx wal wn vy nfriotad.1 vx vy vy nfnae
      nfan wph vx cv vy cv wceq vx wal wn wa vy cv cA wcel wps vx wph vx cv vy
      cv wceq vx wal wn wa vx vy cv cA vx cv vy cv wceq vx wal wn vx vy cv wnfc
      wph vx vy nfcvf adantl wph vx cA wnfc vx cv vy cv wceq vx wal wn
      nfriotad.3 adantr nfeld wph wps vx wnf vx cv vy cv wceq vx wal wn
      nfriotad.2 adantr nfand nfiotad ex vx cv vy cv wceq vx wal vx vy cv cA
      wcel wps wa vy cio wnfc vy vy cv cA wcel wps wa vy cio wnfc vy cv cA wcel
      wps wa vy nfiota1 vx vy vy cv cA wcel wps wa vy cio vy cv cA wcel wps wa
      vy cio vx cv vy cv wceq vx wal vy cv cA wcel wps wa vy cio eqidd drnfc1
      mpbiri pm2.61d2 wph vx vy cv cA wcel vy cab cund wph vx cund nfcvd wph vy
      cv cA wcel vx vy nfriotad.1 wph vx cv vy cv wceq vx wal wn wa vx vy cv cA
      vx cv vy cv wceq vx wal wn vx vy cv wnfc wph vx vy nfcvf adantl wph vx cA
      wnfc vx cv vy cv wceq vx wal wn nfriotad.3 adantr nfeld nfabd2 nffvd
      nfifd nfcxfrd $.
  $}

  ${
    $d x y z $.  $d z A $.  $d z ph $.
    nfriota.1 $e |- F/ x ph $.
    nfriota.2 $e |- F/_ x A $.
    $( A variable not free in a wff remains so in a restricted iota
       descriptor.  (Contributed by NM, 12-Oct-2011.) $)
    nfriota $p |- F/_ x ( iota_ y e. A ph ) $=
      vx wph vy cA crio wnfc wtru wph vx vy cA vy nftru wph vx wnf wtru
      nfriota.1 a1i vx cA wnfc wtru nfriota.2 a1i nfriotad trud $.
  $}

  ${
    $d x z A $.  $d y z A $.  $d z ph $.  $d z ps $.
    cbvriota.1 $e |- F/ y ph $.
    cbvriota.2 $e |- F/ x ps $.
    cbvriota.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable in a restricted description binder.  (Contributed
       by NM, 18-Mar-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    cbvriota $p |- ( iota_ x e. A ph ) = ( iota_ y e. A ps ) $=
      wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv cA wcel vx cab cund cfv
      cif wps vy cA wreu vy cv cA wcel wps wa vy cio vy cv cA wcel vy cab cund
      cfv cif wph vx cA crio wps vy cA crio wph vx cA wreu wps vy cA wreu vx cv
      cA wcel wph wa vx cio vx cv cA wcel vx cab cund cfv vy cv cA wcel wps wa
      vy cio vy cv cA wcel vy cab cund cfv wph wps vx vy cA cbvriota.1
      cbvriota.2 cbvriota.3 cbvreu vx cv cA wcel wph wa vx cio vz cv cA wcel
      wph vx vz wsb wa vz cio vy cv cA wcel wps wa vy cio vx cv cA wcel wph wa
      vz cv cA wcel wph vx vz wsb wa vx vz vx cv vz cv wceq vx cv cA wcel vz cv
      cA wcel wph wph vx vz wsb vx cv vz cv cA eleq1 wph vx vz sbequ12 anbi12d
      vx cv cA wcel wph wa vz nfv vz cv cA wcel wph vx vz wsb vx vz cv cA wcel
      vx nfv wph vx vz nfs1v nfan cbviota vz cv cA wcel wph vx vz wsb wa vy cv
      cA wcel wps wa vz vy vz cv vy cv wceq vz cv cA wcel vy cv cA wcel wph vx
      vz wsb wps vz cv vy cv cA eleq1 vz cv vy cv wceq wph vx vz wsb wph vx vy
      wsb wps wph vz vy vx sbequ wph wps vx vy cbvriota.2 cbvriota.3 sbie
      syl6bb anbi12d vz cv cA wcel wph vx vz wsb vy vz cv cA wcel vy nfv wph vx
      vz vy cbvriota.1 nfsb nfan vy cv cA wcel wps wa vz nfv cbviota eqtri vx
      cv cA wcel vx cab vy cv cA wcel vy cab cund vx cv cA wcel vx cab cA vy cv
      cA wcel vy cab vx cA abid2 vy cA abid2 eqtr4i fveq2i ifbieq12i wph vx cA
      df-riota wps vy cA df-riota 3eqtr4i $.
  $}

  ${
    $d x A $.  $d y A $.  $d y ph $.  $d x ps $.
    cbvriotav.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variable in a restricted description binder.  (Contributed
       by NM, 18-Mar-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    cbvriotav $p |- ( iota_ x e. A ph ) = ( iota_ y e. A ps ) $=
      wph wps vx vy cA wph vy nfv wps vx nfv cbvriotav.1 cbvriota $.
  $}

  ${
    $d y z A $.  $d x z w B $.  $d w z ph $.  $d w x y $.
    $( Interchange class substitution and restricted description binder.
       (Contributed by NM, 24-Feb-2013.) $)
    csbriotag $p |- ( A e. V
      -> [_ A / x ]_ ( iota_ y e. B ph ) = ( iota_ y e. B [. A / x ]. ph ) ) $=
      vx vz cv wph vy cB crio csb wph vx vz wsb vy cB crio wceq vx cA wph vy cB
      crio csb wph vx cA wsbc vy cB crio wceq vz cA cV vz cv cA wceq vx vz cv
      wph vy cB crio csb vx cA wph vy cB crio csb wph vx vz wsb vy cB crio wph
      vx cA wsbc vy cB crio vx vz cv cA wph vy cB crio csbeq1 vz cv cA wceq wph
      vx vz wsb wph vx cA wsbc vy cB wph vx vz cA dfsbcq2 riotabidv eqeq12d vx
      vz cv wph vy cB crio wph vx vz wsb vy cB crio vz vex wph vx vz wsb vx vy
      cB wph vx vz nfs1v vx cB nfcv nfriota vx vz weq wph wph vx vz wsb vy cB
      wph vx vz sbequ12 riotabidv csbief vtoclg $.
  $}

  $( Membership law for "the unique element in ` A ` such that ` ph ` ."

     This can useful for expanding an iota-based definition (see ~ df-iota ).
     If you have an unbounded iota, ~ iotacl may be useful.

     (Contributed by NM, 21-Aug-2011.)  (Revised by Mario Carneiro,
     23-Dec-2016.) $)
  riotacl2 $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. { x e. A | ph } ) $=
    wph vx cA wreu wph vx cA crio vx cv cA wcel wph wa vx cio wph vx cA crab
    wph vx cA riotaiota wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv cA
    wcel wph wa vx cab wph vx cA crab wph vx cA wreu vx cv cA wcel wph wa vx
    weu vx cv cA wcel wph wa vx cio vx cv cA wcel wph wa vx cab wcel wph vx cA
    df-reu vx cv cA wcel wph wa vx iotacl sylbi wph vx cA df-rab syl6eleqr
    eqeltrd $.

  ${
    $d x A $.
    $( Closure of restricted iota.  (Contributed by NM, 21-Aug-2011.) $)
    riotacl $p |- ( E! x e. A ph -> ( iota_ x e. A ph ) e. A ) $=
      wph vx cA wreu wph vx cA crab cA wph vx cA crio wph vx cA ssrab2 wph vx
      cA riotacl2 sseldi $.
  $}

  $( Substitution law for descriptions.  Compare ~ iotasbc .  (Contributed by
     NM, 23-Aug-2011.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)
  riotasbc $p |- ( E! x e. A ph -> [. ( iota_ x e. A ph ) / x ]. ph ) $=
    wph vx cA wreu wph vx cA crio wph vx cab wcel wph vx wph vx cA crio wsbc
    wph vx cA wreu wph vx cA crab wph vx cab wph vx cA crio wph vx cA rabssab
    wph vx cA riotacl2 sseldi wph vx wph vx cA crio df-sbc sylibr $.

  ${
    $d x ph $.
    riotabidva.1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  ( ~ rabbidva analog.)  (Contributed by NM, 17-Jan-2012.) $)
    riotabidva $p |- ( ph -> ( iota_ x e. A ps ) = ( iota_ x e. A ch ) ) $=
      wph wps vx cA wreu vx cv cA wcel wps wa vx cio vx cv cA wcel vx cab cund
      cfv cif wch vx cA wreu vx cv cA wcel wch wa vx cio vx cv cA wcel vx cab
      cund cfv cif wps vx cA crio wch vx cA crio wph wps vx cA wreu vx cv cA
      wcel wps wa vx cio vx cv cA wcel vx cab cund cfv cif wps vx cA wreu vx cv
      cA wcel wch wa vx cio vx cv cA wcel vx cab cund cfv cif wch vx cA wreu vx
      cv cA wcel wch wa vx cio vx cv cA wcel vx cab cund cfv cif wph wps vx cA
      wreu vx cv cA wcel wps wa vx cio vx cv cA wcel wch wa vx cio vx cv cA
      wcel vx cab cund cfv wph vx cv cA wcel wps wa vx cio vx cv cA wcel wch wa
      vx cio wceq wps vx cA wreu wph vx cv cA wcel wps wa vx cv cA wcel wch wa
      vx wph vx cv cA wcel wps wch riotabidva.1 pm5.32da iotabidv adantr
      ifeq1da wph wps vx cA wreu wch vx cA wreu vx cv cA wcel wch wa vx cio vx
      cv cA wcel vx cab cund cfv wph wps wch vx cA riotabidva.1 reubidva ifbid
      eqtrd wps vx cA df-riota wch vx cA df-riota 3eqtr4g $.
  $}

  ${
    riotabiia.1 $e |- ( x e. A -> ( ph <-> ps ) ) $.
    $( Equivalent wff's yield equal restricted iotas (inference rule).
       ( ~ rabbiia analog.)  (Contributed by NM, 16-Jan-2012.) $)
    riotabiia $p |- ( iota_ x e. A ph ) = ( iota_ x e. A ps ) $=
      cvv cvv wceq wph vx cA crio wps vx cA crio wceq cvv eqid cvv cvv wceq wph
      wps vx cA vx cv cA wcel wph wps wb cvv cvv wceq riotabiia.1 adantl
      riotabidva ax-mp $.
  $}

  ${
    $d x y A $.
    $( Property of restricted iota.  Compare ~ iota1 .  (Contributed by Mario
       Carneiro, 15-Oct-2016.) $)
    riota1 $p |- ( E! x e. A ph ->
      ( ( x e. A /\ ph ) <-> ( iota_ x e. A ph ) = x ) ) $=
      wph vx cA wreu vx cv cA wcel wph wa vx cv cA wcel wph wa vx cio vx cv
      wceq wph vx cA crio vx cv wceq wph vx cA wreu vx cv cA wcel wph wa vx weu
      vx cv cA wcel wph wa vx cv cA wcel wph wa vx cio vx cv wceq wb wph vx cA
      df-reu vx cv cA wcel wph wa vx iota1 sylbi wph vx cA wreu wph vx cA crio
      vx cv cA wcel wph wa vx cio vx cv wph vx cA riotaiota eqeq1d bitr4d $.
  $}

  $( Property of iota.  (Contributed by NM, 23-Aug-2011.) $)
  riota1a $p |- ( ( x e. A /\ E! x e. A ph ) ->
          ( ph <-> ( iota x ( x e. A /\ ph ) ) = x ) ) $=
    vx cv cA wcel wph vx cv cA wcel wph wa wph vx cA wreu vx cv cA wcel wph wa
    vx cio vx cv wceq vx cv cA wcel wph ibar wph vx cA wreu vx cv cA wcel wph
    wa vx weu vx cv cA wcel wph wa vx cv cA wcel wph wa vx cio vx cv wceq wb
    wph vx cA df-reu vx cv cA wcel wph wa vx iota1 sylbi sylan9bb $.

  ${
    $d x A $.
    riota2df.1 $e |- F/ x ph $.
    riota2df.2 $e |- ( ph -> F/_ x B ) $.
    riota2df.3 $e |- ( ph -> F/ x ch ) $.
    riota2df.4 $e |- ( ph -> B e. A ) $.
    riota2df.5 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
    $( A deduction version of ~ riota2f .  (Contributed by NM, 17-Feb-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    riota2df $p |- ( ( ph /\ E! x e. A ps ) ->
            ( ch <-> ( iota_ x e. A ps ) = B ) ) $=
      wph wps vx cA wreu wa wch vx cv cA wcel wps wa vx cio cB wceq wps vx cA
      crio cB wceq wph wps vx cA wreu wa vx cv cA wcel wps wa wch vx cB cA wph
      cB cA wcel wps vx cA wreu riota2df.4 adantr wph wps vx cA wreu wa wps vx
      cA wreu vx cv cA wcel wps wa vx weu wph wps vx cA wreu simpr wps vx cA
      df-reu sylib wph wps vx cA wreu wa vx cv cB wceq wa wps vx cv cA wcel wps
      wa wch wph wps vx cA wreu wa vx cv cB wceq wa vx cv cA wcel wps wph wps
      vx cA wreu wa vx cv cB wceq wa vx cv cB cA wph wps vx cA wreu wa vx cv cB
      wceq simpr wph wps vx cA wreu wa cB cA wcel vx cv cB wceq wph cB cA wcel
      wps vx cA wreu riota2df.4 adantr adantr eqeltrd biantrurd wph vx cv cB
      wceq wps wch wb wps vx cA wreu riota2df.5 adantlr bitr3d wph wps vx cA
      wreu vx riota2df.1 wps vx cA nfreu1 nfan wph wch vx wnf wps vx cA wreu
      riota2df.3 adantr wph vx cB wnfc wps vx cA wreu riota2df.2 adantr iota2df
      wph wps vx cA wreu wa wps vx cA crio vx cv cA wcel wps wa vx cio cB wps
      vx cA wreu wps vx cA crio vx cv cA wcel wps wa vx cio wceq wph wps vx cA
      riotaiota adantl eqeq1d bitr4d $.
  $}

  ${
    $d y ph $.  $d x y A $.  $d y B $.
    riota2f.1 $e |- F/_ x B $.
    riota2f.2 $e |- F/ x ps $.
    riota2f.3 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( This theorem shows a condition that allows us to represent a descriptor
       with a class expression ` B ` .  (Contributed by NM, 23-Aug-2011.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    riota2f $p |- ( ( B e. A /\ E! x e. A ph ) ->
            ( ps <-> ( iota_ x e. A ph ) = B ) ) $=
      cB cA wcel wph wps vx cA cB vx cB cA riota2f.1 nfel1 vx cB wnfc cB cA
      wcel riota2f.1 a1i wps vx wnf cB cA wcel riota2f.2 a1i cB cA wcel id vx
      cv cB wceq wph wps wb cB cA wcel riota2f.3 adantl riota2df $.
  $}

  ${
    $d x ps $.  $d x A $.  $d x B $.
    riota2.1 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( This theorem shows a condition that allows us to represent a descriptor
       with a class expression ` B ` .  (Contributed by NM, 23-Aug-2011.)
       (Revised by Mario Carneiro, 10-Dec-2016.) $)
    riota2 $p |- ( ( B e. A /\ E! x e. A ph ) ->
            ( ps <-> ( iota_ x e. A ph ) = B ) ) $=
      wph wps vx cA cB vx cB nfcv wps vx nfv riota2.1 riota2f $.
  $}

  ${
    $d y ph $.  $d x y A $.  $d y B $.
    riotaprop.0 $e |- F/ x ps $.
    riotaprop.1 $e |- B = ( iota_ x e. A ph ) $.
    riotaprop.3 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( Properties of a restricted definite description operator.  Todo: can
       some uses of ~ riota2f be shortened with this?  (Contributed by NM,
       23-Nov-2013.) $)
    riotaprop $p |- ( E! x e. A ph -> ( B e. A /\ ps ) ) $=
      wph vx cA wreu cB cA wcel wps wph vx cA wreu cB wph vx cA crio cA
      riotaprop.1 wph vx cA riotacl syl5eqel cB cA wcel wph vx cA wreu wps wph
      vx cA wreu cB wph vx cA crio cA riotaprop.1 wph vx cA riotacl syl5eqel cB
      cA wcel wph vx cA wreu wa wps wph vx cA crio cB wceq cB wph vx cA crio
      riotaprop.1 eqcomi wph wps vx cA cB vx cB wph vx cA crio riotaprop.1 wph
      vx cA nfriota1 nfcxfr riotaprop.0 riotaprop.3 riota2f mpbiri mpancom jca
      $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y ph $.  $d y ps $.
    riota5f.1 $e |- ( ph -> F/_ x B ) $.
    riota5f.2 $e |- ( ph -> B e. A ) $.
    riota5f.3 $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
    $( A method for computing restricted iota.  (Contributed by NM,
       16-Apr-2013.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    riota5f $p |- ( ph -> ( iota_ x e. A ps ) = B ) $=
      wph wps vx cv cB wceq wb vx cA wral wps vx cA crio cB wceq wph wps vx cv
      cB wceq wb vx cA riota5f.3 ralrimiva wph wps vx cv vy cv wceq wb vx cA
      wral wps vx cA crio vy cv wceq wi vy cB wsbc wps vx cv cB wceq wb vx cA
      wral wps vx cA crio cB wceq wi wph cB cA wcel wps vx cv vy cv wceq wb vx
      cA wral wps vx cA crio vy cv wceq wi vy cA wral wps vx cv vy cv wceq wb
      vx cA wral wps vx cA crio vy cv wceq wi vy cB wsbc riota5f.2 wph wps vx
      cv vy cv wceq wb vx cA wral wps vx cA crio vy cv wceq wi vy cA wph vy cv
      cA wcel wps vx cv vy cv wceq wb vx cA wral wps vx cA crio vy cv wceq wph
      vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa wa wtru wps vx cA
      crio vy cv wceq wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa
      wa a1tru wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa wa wps
      vx cA wreu wtru wps vx cA crio vy cv wceq wb vy cv cA wcel wps vx cv vy
      cv wceq wb vx cA wral wa wps vx cA wreu wph wps vx cA vy cv reu6i adantl
      wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa wa wps wtru vx cA
      vy cv wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa vx wph vx
      nfv vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral vx vy cv cA wcel vx
      nfv wps vx cv vy cv wceq wb vx cA nfra1 nfan nfan wph vy cv cA wcel wps
      vx cv vy cv wceq wb vx cA wral wa wa vx vy cv nfcvd wph vy cv cA wcel wps
      vx cv vy cv wceq wb vx cA wral wa wa wtru vx nfvd wph vy cv cA wcel wps
      vx cv vy cv wceq wb vx cA wral simprl wph vy cv cA wcel wps vx cv vy cv
      wceq wb vx cA wral wa wa vx cv vy cv wceq wa wps wtru wph vy cv cA wcel
      wps vx cv vy cv wceq wb vx cA wral wa wa vx cv vy cv wceq wa wps vx cv vy
      cv wceq wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa wa vx cv
      vy cv wceq simpr wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA wral wa
      wa vx cv vy cv wceq wa wps vx cv vy cv wceq wb vx cA wral vx cv cA wcel
      wps vx cv vy cv wceq wb wph vy cv cA wcel wps vx cv vy cv wceq wb vx cA
      wral vx cv vy cv wceq simplrr wph vy cv cA wcel wps vx cv vy cv wceq wb
      vx cA wral wa wa vx cv vy cv wceq wa vx cv vy cv cA wph vy cv cA wcel wps
      vx cv vy cv wceq wb vx cA wral wa wa vx cv vy cv wceq simpr wph vy cv cA
      wcel wps vx cv vy cv wceq wb vx cA wral vx cv vy cv wceq simplrl eqeltrd
      wps vx cv vy cv wceq wb vx cA rsp sylc mpbird wph vy cv cA wcel wps vx cv
      vy cv wceq wb vx cA wral wa wa vx cv vy cv wceq wa a1tru 2thd riota2df
      mpdan mpbid expr ralrimiva wps vx cv vy cv wceq wb vx cA wral wps vx cA
      crio vy cv wceq wi vy cB cA rspsbc sylc wph wps vx cv vy cv wceq wb vx cA
      wral wps vx cA crio vy cv wceq wi wps vx cv cB wceq wb vx cA wral wps vx
      cA crio cB wceq wi vy cB cA riota5f.2 wph vy cv cB wceq wa wps vx cv vy
      cv wceq wb vx cA wral wps vx cv cB wceq wb vx cA wral wps vx cA crio vy
      cv wceq wps vx cA crio cB wceq wph vy cv cB wceq wa wps vx cv vy cv wceq
      wb wps vx cv cB wceq wb vx cA wph vy cv cB wceq vx wph vx nfv wph vx vy
      cv cB wph vx vy cv nfcvd riota5f.1 nfeqd nfan1 wph vy cv cB wceq wa vx cv
      vy cv wceq vx cv cB wceq wps wph vy cv cB wceq wa vy cv cB vx cv wph vy
      cv cB wceq simpr eqeq2d bibi2d ralbid wph vy cv cB wceq wa vy cv cB wps
      vx cA crio wph vy cv cB wceq simpr eqeq2d imbi12d sbcied mpbid mpd $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    riota5.1 $e |- ( ph -> B e. A ) $.
    riota5.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> x = B ) ) $.
    $( A method for computing restricted iota.  (Contributed by NM,
       20-Oct-2011.)  (Revised by Mario Carneiro, 6-Dec-2016.) $)
    riota5 $p |- ( ph -> ( iota_ x e. A ps ) = B ) $=
      wph wps vx cA cB wph vx cB nfcvd riota5.1 riota5.2 riota5f $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x ph $.  $d y ps $.
    riota5OLD.1 $e |- ( ( ph /\ B e. A /\ x e. A ) -> ( ps <-> x = B ) ) $.
    $( A method for computing restricted iota.  (Contributed by NM,
       20-Oct-2011.)  (New usage is discouraged.) $)
    riota5OLD $p |- ( ( ph /\ B e. A ) -> ( iota_ x e. A ps ) = B ) $=
      wph cB cA wcel wa wps vx cA cB wph cB cA wcel simpr wph cB cA wcel vx cv
      cA wcel wps vx cv cB wceq wb riota5OLD.1 3expa riota5 $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Restriction of a unique element to a smaller class.  (Contributed by NM,
       21-Aug-2011.)  (Revised by NM, 22-Mar-2013.) $)
    riotass2 $p |- ( ( ( A C_ B /\ A. x e. A ( ph -> ps ) ) /\ ( E. x e. A ph
           /\ E! x e. B ps ) )
         -> ( iota_ x e. A ph ) = ( iota_ x e. B ps ) ) $=
      cA cB wss wph wps wi vx cA wral wa wph vx cA wrex wps vx cB wreu wa wa
      wps vx cB crio wph vx cA crio cA cB wss wph wps wi vx cA wral wa wph vx
      cA wrex wps vx cB wreu wa wa wps vx wph vx cA crio wsbc wps vx cB crio
      wph vx cA crio wceq cA cB wss wph wps wi vx cA wral wa wph vx cA wrex wps
      vx cB wreu wa wa wph vx cA wreu wph wps wi vx cA wral wps vx wph vx cA
      crio wsbc wph wps vx cA cB reuss2 cA cB wss wph wps wi vx cA wral wph vx
      cA wrex wps vx cB wreu wa simplr wph vx cA wreu wph wps wi vx cA wral wph
      vx wph vx cA crio wsbc wps vx wph vx cA crio wsbc wph vx cA riotasbc wph
      vx cA wreu wph vx cA crio cA wcel wph wps wi vx cA wral wph vx wph vx cA
      crio wsbc wps vx wph vx cA crio wsbc wi wi wph vx cA riotacl wph vx cA
      crio cA wcel wph wps wi vx cA wral wph wps wi vx wph vx cA crio wsbc wph
      vx wph vx cA crio wsbc wps vx wph vx cA crio wsbc wi wph wps wi vx wph vx
      cA crio cA rspsbc wph wps vx wph vx cA crio cA sbcimg sylibd syl mpid
      sylc cA cB wss wph wps wi vx cA wral wa wph vx cA wrex wps vx cB wreu wa
      wa wph vx cA crio cB wcel wps vx cB wreu wps vx wph vx cA crio wsbc wps
      vx cB crio wph vx cA crio wceq wb cA cB wss wph wps wi vx cA wral wa wph
      vx cA wrex wps vx cB wreu wa wa wph vx cA crio cA wcel wph vx cA crio cB
      wcel cA cB wss wph wps wi vx cA wral wa wph vx cA wrex wps vx cB wreu wa
      wa wph vx cA wreu wph vx cA crio cA wcel wph wps vx cA cB reuss2 wph vx
      cA riotacl syl cA cB wss wph vx cA crio cA wcel wph vx cA crio cB wcel wi
      wph wps wi vx cA wral wph vx cA wrex wps vx cB wreu wa cA cB wph vx cA
      crio ssel ad2antrr mpd cA cB wss wph wps wi vx cA wral wa wph vx cA wrex
      wps vx cB wreu simprr wps wps vx wph vx cA crio wsbc vx cB wph vx cA crio
      wph vx cA nfriota1 wps vx wph vx cA crio wph vx cA nfriota1 nfsbc1 wps vx
      wph vx cA crio sbceq1a riota2f syl2anc mpbid eqcomd $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y ph $.
    $( Restriction of a unique element to a smaller class.  (Contributed by NM,
       19-Oct-2005.)  (Revised by Mario Carneiro, 24-Dec-2016.) $)
    riotass $p |- ( ( A C_ B /\ E. x e. A ph /\ E! x e. B ph ) ->
                ( iota_ x e. A ph ) = ( iota_ x e. B ph ) ) $=
      cA cB wss wph vx cA wrex wph vx cB wreu w3a wph vx cB crio wph vx cA crio
      cA cB wss wph vx cA wrex wph vx cB wreu w3a wph vx wph vx cA crio wsbc
      wph vx cB crio wph vx cA crio wceq cA cB wss wph vx cA wrex wph vx cB
      wreu w3a wph vx cA wreu wph vx wph vx cA crio wsbc wph vx cA cB reuss wph
      vx cA riotasbc syl cA cB wss wph vx cA wrex wph vx cB wreu w3a wph vx cA
      crio cB wcel wph vx cB wreu wph vx wph vx cA crio wsbc wph vx cB crio wph
      vx cA crio wceq wb cA cB wss wph vx cA wrex wph vx cB wreu w3a cA cB wph
      vx cA crio cA cB wss wph vx cA wrex wph vx cB wreu simp1 cA cB wss wph vx
      cA wrex wph vx cB wreu w3a wph vx cA wreu wph vx cA crio cA wcel wph vx
      cA cB reuss wph vx cA riotacl syl sseldd cA cB wss wph vx cA wrex wph vx
      cB wreu simp3 wph wph vx wph vx cA crio wsbc vx cB wph vx cA crio wph vx
      cA nfriota1 wph vx wph vx cA crio wph vx cA nfriota1 nfsbc1 wph vx wph vx
      cA crio sbceq1a riota2f syl2anc mpbid eqcomd $.

    $( Restriction of a unique element to a smaller class.  (Contributed by NM,
       19-Feb-2006.)  (Revised by NM, 16-Jun-2017.) $)
    moriotass $p |- ( ( A C_ B /\ E. x e. A ph /\ E* x e. B ph ) ->
                ( iota_ x e. A ph ) = ( iota_ x e. B ph ) ) $=
      cA cB wss wph vx cA wrex wph vx cB wrmo wph vx cB wreu wph vx cA crio wph
      vx cB crio wceq cA cB wss wph vx cA wrex wph vx cB wrmo w3a wph vx cB
      wrex wph vx cB wrmo wph vx cB wreu cA cB wss wph vx cA wrex wph vx cB
      wrex wph vx cB wrmo cA cB wss wph vx cA wrex wph vx cB wrex wph vx cA cB
      ssrexv imp 3adant3 cA cB wss wph vx cA wrex wph vx cB wrmo simp3 wph vx
      cB reu5 sylanbrc wph vx cA cB riotass syld3an3 $.
  $}

  ${
    $d y A $.  $d y ph $.  $d x y $.
    $( A restricted class abstraction with a unique member can be expressed as
       a singleton.  (Contributed by NM, 30-May-2006.) $)
    snriota $p |- ( E! x e. A ph ->
                   { x e. A | ph } = { ( iota_ x e. A ph ) } ) $=
      wph vx cA wreu wph vx cA crab vx cv cA wcel wph wa vx cio csn wph vx cA
      crio csn wph vx cA wreu wph vx cA crab vx cv cA wcel wph wa vx cab vx cv
      cA wcel wph wa vx cio csn wph vx cA df-rab wph vx cA wreu vx cv cA wcel
      wph wa vx weu vx cv cA wcel wph wa vx cab vx cv cA wcel wph wa vx cio csn
      wceq wph vx cA df-reu vx cv cA wcel wph wa vx sniota sylbi syl5eq wph vx
      cA wreu wph vx cA crio vx cv cA wcel wph wa vx cio wph vx cA riotaiota
      sneqd eqtr4d $.
  $}

  ${
    $d x B $.  $d x z C $.  $d x y z A $.  $d x y ph $.  $d ps y z $.
    $d ch x z $.
    riotaxfrd.1 $e |- F/_ y C $.
    riotaxfrd.2 $e |- ( ( ph /\ y e. A ) -> B e. A ) $.
    riotaxfrd.3 $e |- ( ( ph /\ ( iota_ y e. A ch ) e. A ) -> C e. A ) $.
    riotaxfrd.4 $e |- ( x = B -> ( ps <-> ch ) ) $.
    riotaxfrd.5 $e |- ( y = ( iota_ y e. A ch ) -> B = C ) $.
    riotaxfrd.6 $e |- ( ( ph /\ x e. A ) -> E! y e. A x = B ) $.
    $( Change the variable ` x ` in the expression for "the unique ` x ` such
       that ` ps ` " to another variable ` y ` contained in expression ` B ` .
       Use ~ reuhypd to eliminate the last hypothesis.  (Contributed by NM,
       16-Jan-2012.)  (Revised by Mario Carneiro, 15-Oct-2016.) $)
    riotaxfrd $p |- ( ( ph /\ E! x e. A ps ) -> ( iota_ x e. A ps ) = C ) $=
      wph wps vx cA wreu wa wps vx cA crio vx cv wps vx cA crab wcel vx cA crio
      cC vx cv wps vx cA crab wcel wps vx cA vx cv wps vx cA crab wcel vx cv cA
      wcel wps wps vx cA rabid baib riotabiia wph wps vx cA wreu wa cC wps vx
      cA crab wcel vx cv wps vx cA crab wcel vx cA crio cC wceq wph wps vx cA
      wreu cC wps vx cA crab wcel wph wps vx cA wreu wch vy cA wreu cC wps vx
      cA crab wcel wph wps wch vx vy cB cA riotaxfrd.2 riotaxfrd.6 riotaxfrd.4
      reuxfrd wph wch vy cA wreu cC wps vx cA crab wcel wph wch vy cA wreu wa
      cC wps vx cA crab wcel wch vy cA crio wch vy cA crab wcel wch vy cA wreu
      wch vy cA crio wch vy cA crab wcel wph wch vy cA riotacl2 adantl wch vy
      cA wreu wph wch vy cA crio cA wcel cC wps vx cA crab wcel wch vy cA crio
      wch vy cA crab wcel wb wch vy cA riotacl wph wps wch vx vy cB wch vy cA
      crio cC cA wch vy cA nfriota1 riotaxfrd.1 riotaxfrd.2 riotaxfrd.4
      riotaxfrd.5 rabxfrd sylan2 mpbird ex sylbid imp wph wps vx cA wreu wa cC
      cA wcel vx cv wps vx cA crab wcel vx cA wreu cC wps vx cA crab wcel vx cv
      wps vx cA crab wcel vx cA crio cC wceq wb wph wps vx cA wreu cC cA wcel
      wph wps vx cA wreu wch vy cA wreu cC cA wcel wph wps wch vx vy cB cA
      riotaxfrd.2 riotaxfrd.6 riotaxfrd.4 reuxfrd wch vy cA wreu wch vy cA crio
      cA wcel wph cC cA wcel wch vy cA riotacl wph wch vy cA crio cA wcel cC cA
      wcel riotaxfrd.3 ex syl5 sylbid imp wps vx cA wreu vx cv wps vx cA crab
      wcel vx cA wreu wph wps vx cA wreu vx cv wps vx cA crab wcel vx cA wreu
      wps vx cv wps vx cA crab wcel vx cA vx cv wps vx cA crab wcel vx cv cA
      wcel wps wps vx cA rabid baibr reubiia biimpi adantl vx cv wps vx cA crab
      wcel cC wps vx cA crab wcel vx cA cC vx cC nfcv vx cC wps vx cA crab wps
      vx cA nfrab1 nfel2 vx cv cC wps vx cA crab eleq1 riota2f syl2anc mpbid
      syl5eqr $.
  $}

  ${
    $d x y z A $.  $d x z B $.
    eusvobj1.1 $e |- B e. _V $.
    $( Specify the same property in two ways when class ` B ( y ) ` is
       single-valued.  (Contributed by NM, 1-Nov-2010.)  (Proof shortened by
       Mario Carneiro, 24-Dec-2016.) $)
    eusvobj2 $p |- ( E! x E. y e. A x = B
       -> ( E. y e. A x = B <-> A. y e. A x = B ) ) $=
      vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA wrex vx cv cB wceq vy
      cA wral vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA wrex vx cab
      vz cv csn wceq vz wex vx cv cB wceq vy cA wrex vx cv cB wceq vy cA wral
      wi vx cv cB wceq vy cA wrex vx vz euabsn2 vx cv cB wceq vy cA wrex vx cab
      vz cv csn wceq vx cv cB wceq vy cA wrex vx cv cB wceq vy cA wral wi vz vx
      cv cB wceq vy cA wrex vx cab vz cv csn wceq vx cv cB wceq vy cA wrex vx
      cv vz cv wceq vx cv cB wceq vy cA wral vx cv cB wceq vy cA wrex vx cab vz
      cv csn wceq vx cv vx cv cB wceq vy cA wrex vx cab wcel vx cv vz cv csn
      wcel vx cv cB wceq vy cA wrex vx cv vz cv wceq vx cv cB wceq vy cA wrex
      vx cab vz cv csn vx cv eleq2 vx cv cB wceq vy cA wrex vx abid vx vz cv
      elsn 3bitr3g vx cv cB wceq vy cA wrex vx cab vz cv csn wceq vx cv cB wceq
      vy cA wral vx cv vz cv wceq vz cv cB wceq vy cA wral vx cv cB wceq vy cA
      wrex vx cab vz cv csn wceq vz cv cB wceq vy cA vy vx cv cB wceq vy cA
      wrex vx cab vz cv csn vx cv cB wceq vy cA wrex vy vx vx cv cB wceq vy cA
      nfre1 nfab nfeq1 vy cv cA wcel cB vx cv cB wceq vy cA wrex vx cab wcel vx
      cv cB wceq vy cA wrex vx cab vz cv csn wceq vz cv cB wceq vy vx cA cB
      eusvobj1.1 elabrex vx cv cB wceq vy cA wrex vx cab vz cv csn wceq cB vx
      cv cB wceq vy cA wrex vx cab wcel cB vz cv csn wcel vz cv cB wceq vx cv
      cB wceq vy cA wrex vx cab vz cv csn cB eleq2 cB vz cv csn wcel cB vz cv
      wceq vz cv cB wceq cB vz cv eusvobj1.1 elsnc cB vz cv eqcom bitri syl6bb
      syl5ib ralrimi vx cv vz cv wceq vx cv cB wceq vz cv cB wceq vy cA vx cv
      vz cv cB eqeq1 ralbidv syl5ibrcom sylbid exlimiv sylbi vx cv cB wceq vy
      cA wrex vx weu vx cv cB wceq vy cA wrex vx wex cA c0 wne vx cv cB wceq vy
      cA wral vx cv cB wceq vy cA wrex wi vx cv cB wceq vy cA wrex vx euex vx
      cv cB wceq vy cA wrex cA c0 wne vx vx cv cB wceq vy cA rexn0 exlimiv cA
      c0 wne vx cv cB wceq vy cA wral vx cv cB wceq vy cA wrex vx cv cB wceq vy
      cA r19.2z ex 3syl impbid $.

    $( Specify the same object in two ways when class ` B ( y ) ` is
       single-valued.  (Contributed by NM, 1-Nov-2010.)  (Proof shortened by
       Mario Carneiro, 19-Nov-2016.) $)
    eusvobj1 $p |- ( E! x E. y e. A x = B
       -> ( iota x E. y e. A x = B ) = ( iota x A. y e. A x = B ) ) $=
      vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA wrex vx cv cB wceq vy
      cA wral wb vx wal vx cv cB wceq vy cA wrex vx cio vx cv cB wceq vy cA
      wral vx cio wceq vx cv cB wceq vy cA wrex vx weu vx cv cB wceq vy cA wrex
      vx cv cB wceq vy cA wral wb vx vx cv cB wceq vy cA wrex vx nfeu1 vx vy cA
      cB eusvobj1.1 eusvobj2 alrimi vx cv cB wceq vy cA wrex vx cv cB wceq vy
      cA wral vx iotabi syl $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x F $.
    $( There is one domain element for each value of a one-to-one onto
       function.  (Contributed by NM, 26-May-2006.) $)
    f1ofveu $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) ->
                  E! x e. A ( F ` x ) = C ) $=
      cA cB cF wf1o cC cB wcel wa vx cv cF cfv cC wceq vx cA wreu cC vx cv cop
      cF ccnv wcel vx cA wreu cA cB cF wf1o cB cA cF ccnv wf cC cB wcel cC vx
      cv cop cF ccnv wcel vx cA wreu cA cB cF wf1o cB cA cF ccnv wf1o cB cA cF
      ccnv wf cA cB cF f1ocnv cB cA cF ccnv f1of syl vx cB cA cC cF ccnv feu
      sylan cA cB cF wf1o cC cB wcel wa vx cv cF cfv cC wceq cC vx cv cop cF
      ccnv wcel vx cA cA cB cF wf1o cC cB wcel vx cv cA wcel vx cv cF cfv cC
      wceq cC vx cv cop cF ccnv wcel wb cA cB cF wf1o cC cB wcel vx cv cA wcel
      w3a vx cv cF cfv cC wceq cC cF ccnv cfv vx cv wceq cC vx cv cop cF ccnv
      wcel cA cB cF wf1o vx cv cA wcel cC cB wcel vx cv cF cfv cC wceq cC cF
      ccnv cfv vx cv wceq wb cA cB vx cv cC cF f1ocnvfvb 3com23 cA cB cF wf1o
      cF ccnv cB wfn cC cB wcel vx cv cA wcel cC cF ccnv cfv vx cv wceq cC vx
      cv cop cF ccnv wcel wb cA cB cF wf1o cF cA wfn cF ccnv cB wfn cA cB cF
      dff1o4 simprbi cF ccnv cB wfn cC cB wcel cC cF ccnv cfv vx cv wceq cC vx
      cv cop cF ccnv wcel wb vx cv cA wcel cB cC vx cv cF ccnv fnopfvb 3adant3
      syl3an1 bitrd 3expa reubidva mpbird $.

    $( Value of the converse of a one-to-one onto function.  (Contributed by
       NM, 26-May-2006.)  (Proof shortened by Mario Carneiro, 24-Dec-2016.) $)
    f1ocnvfv3 $p |- ( ( F : A -1-1-onto-> B /\ C e. B ) ->
                  ( `' F ` C ) = ( iota_ x e. A ( F ` x ) = C ) ) $=
      cA cB cF wf1o cC cB wcel wa vx cv cF cfv cC wceq vx cA crio cC cF ccnv
      cfv cA cB cF wf1o cC cB wcel wa vx cv cF cfv cC wceq vx cA cC cF ccnv cfv
      cA cB cC cF f1ocnvdm cA cB cF wf1o cC cB wcel wa vx cv cA wcel wa vx cv
      cF cfv cC wceq cC cF ccnv cfv vx cv wceq vx cv cC cF ccnv cfv wceq cA cB
      cF wf1o vx cv cA wcel cC cB wcel vx cv cF cfv cC wceq cC cF ccnv cfv vx
      cv wceq wb cA cB cF wf1o vx cv cA wcel cC cB wcel vx cv cF cfv cC wceq cC
      cF ccnv cfv vx cv wceq wb cA cB vx cv cC cF f1ocnvfvb 3expa an32s vx cv
      cC cF ccnv cfv eqcom syl6bbr riota5 eqcomd $.
  $}

  ${
    $d x A $.
    $( Restricted iota equals the undefined value of its domain of discourse
       ` A ` when not meaningful.  (Contributed by NM, 16-Jan-2012.)  (Revised
       by Mario Carneiro, 15-Oct-2016.) $)
    riotaund $p |- ( -. E! x e. A ph
                      -> ( iota_ x e. A ph ) = ( Undef ` A ) ) $=
      wph vx cA wreu wn wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv cA
      wcel vx cab cund cfv cif vx cv cA wcel vx cab cund cfv wph vx cA crio cA
      cund cfv wph vx cA wreu vx cv cA wcel wph wa vx cio vx cv cA wcel vx cab
      cund cfv iffalse wph vx cA df-riota cA vx cv cA wcel vx cab cund vx cv cA
      wcel vx cab cA vx cA abid2 eqcomi fveq2i 3eqtr4g $.

    $( For proper classes, restricted and unrestricted iota are the same.
       (Contributed by NM, 15-Sep-2011.) $)
    riotaprc $p |- ( -. A e. _V
           -> ( iota_ x e. A ph ) = ( iota x ( x e. A /\ ph ) ) ) $=
      cA cvv wcel wn wph vx cA wreu wph vx cA crio vx cv cA wcel wph wa vx cio
      wceq cA cvv wcel wn wph vx cA wreu wn wph vx cA crio vx cv cA wcel wph wa
      vx cio wceq cA cvv wcel wn wph vx cA wreu wn wa cA cund cfv c0 wph vx cA
      crio vx cv cA wcel wph wa vx cio cA cvv wcel wn cA cund cfv c0 wceq wph
      vx cA wreu wn cA cund fvprc adantr wph vx cA wreu wn wph vx cA crio cA
      cund cfv wceq cA cvv wcel wn wph vx cA riotaund adantl wph vx cA wreu wn
      vx cv cA wcel wph wa vx cio c0 wceq cA cvv wcel wn wph vx cA wreu vx cv
      cA wcel wph wa vx weu vx cv cA wcel wph wa vx cio c0 wceq wph vx cA
      df-reu vx cv cA wcel wph wa vx iotanul sylnbi adantl 3eqtr4d ex wph vx cA
      riotaiota pm2.61d2 $.

    $( The restricted iota class is limited in size by the base set.
       (Contributed by Mario Carneiro, 24-Dec-2016.) $)
    riotassuni $p |- ( iota_ x e. A ph ) C_ ( ~P U. A u. U. A ) $=
      wph vx cA wreu wph vx cA crio cA cuni cpw cA cuni cun wss wph vx cA wreu
      wph vx cA crio wph vx cA crab cuni cA cuni cpw cA cuni cun wph vx cA
      riotauni wph vx cA crab cuni cA cuni cpw cA cuni cun wss wph vx cA wreu
      wph vx cA crab cuni cA cuni cA cuni cpw cA cuni cun wph vx cA crab cA wss
      wph vx cA crab cuni cA cuni wss wph vx cA ssrab2 wph vx cA crab cA uniss
      ax-mp cA cuni cA cuni cpw ssun2 sstri a1i eqsstrd wph vx cA wreu wn wph
      vx cA crio cA cund cfv cA cuni cpw cA cuni cun wph vx cA riotaund wph vx
      cA wreu wn cA cvv wcel cA cund cfv cA cuni cpw cA cuni cun wss wph vx cA
      wreu wn cA cvv wcel wa cA cund cfv cA cuni cpw cA cuni cpw cA cuni cun cA
      cvv wcel cA cund cfv cA cuni cpw wceq wph vx cA wreu wn cA cvv undefval
      adantl cA cuni cpw cA cuni cpw cA cuni cun wss wph vx cA wreu wn cA cvv
      wcel wa cA cuni cpw cA cuni ssun1 a1i eqsstrd wph vx cA wreu wn cA cvv
      wcel wn wa cA cund cfv c0 cA cuni cpw cA cuni cun cA cvv wcel wn cA cund
      cfv c0 wceq wph vx cA wreu wn cA cund fvprc adantl c0 cA cuni cpw cA cuni
      cun wss wph vx cA wreu wn cA cvv wcel wn wa cA cuni cpw cA cuni cun 0ss
      a1i eqsstrd pm2.61dan eqsstrd pm2.61i $.

    $( Closure of restricted iota.  (Contributed by NM, 28-Feb-2013.)  (Revised
       by Mario Carneiro, 24-Dec-2016.) $)
    riotaclbg $p |- ( A e. V
          -> ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) ) $=
      cA cV wcel wph vx cA wreu wph vx cA crio cA wcel wph vx cA riotacl cA cV
      wcel wph vx cA wreu wph vx cA crio cA wcel cA cV wcel wph vx cA crio cA
      wcel wn wph vx cA wreu wn cA cund cfv cA wcel wn cA cV undefnel2 wph vx
      cA wreu wn wph vx cA crio cA wcel cA cund cfv cA wcel wph vx cA wreu wn
      wph vx cA crio cA cund cfv cA wph vx cA riotaund eleq1d notbid syl5ibrcom
      con4d impbid2 $.

    riotaclb.1 $e |- A e. _V $.
    $( Closure of restricted iota.  (Contributed by NM, 15-Sep-2011.) $)
    riotaclb $p |- ( E! x e. A ph <-> ( iota_ x e. A ph ) e. A ) $=
      cA cvv wcel wph vx cA wreu wph vx cA crio cA wcel wb riotaclb.1 wph vx cA
      cvv riotaclbg ax-mp $.

    $( Restricted iota equals the undefined value of its domain of discourse
       ` A ` when not meaningful.  (Contributed by NM, 26-Sep-2011.) $)
    riotaundb $p |- ( -. E! x e. A ph
                      <-> ( iota_ x e. A ph ) = ( Undef ` A ) ) $=
      wph vx cA wreu wn wph vx cA crio cA cund cfv wceq wph vx cA riotaund wph
      vx cA wreu wph vx cA crio cA cund cfv wph vx cA wreu wph vx cA crio cA
      wcel cA cund cfv cA wcel wn wph vx cA crio cA cund cfv wne wph vx cA
      riotacl cA cvv wcel cA cund cfv cA wcel wn riotaclb.1 cA cvv undefnel2
      ax-mp wph vx cA crio cA cund cfv cA nelne2 sylancl necon2bi impbii $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d x z C $.  $d z D $.  $d z ph $.
    $d x z ps $.
    riotasvd.1 $e |- ( ph
        -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
    riotasvd.2 $e |- ( ph -> D e. A ) $.
    $( Deduction version of ~ riotasv .  (Contributed by NM, 4-Mar-2013.)
       (Revised by Mario Carneiro, 15-Oct-2016.) $)
    riotasvd $p |- ( ( ph /\ A e. V ) -> ( ( y e. B /\ ps ) -> D = C ) ) $=
      wph cA cV wcel wa vy cv cB wcel wps wa wps vx cv cC wceq wi vy cB wral vx
      cA crio cC wceq cD cC wceq wph cA cV wcel wa vy cv cB wcel wps wps vx cv
      cC wceq wi vy cB wral vx cA crio cC wceq wph cA cV wcel wa wps wps vx cv
      cC wceq wi vy cB wral vx cA crio cC wceq wi vy cB wral vy cv cB wcel wps
      wps vx cv cC wceq wi vy cB wral vx cA crio cC wceq wi wi wph cA cV wcel
      wa wps vx cv cC wceq wi vy cB wral vx wps vx cv cC wceq wi vy cB wral vx
      cA crio wsbc wps wps vx cv cC wceq wi vy cB wral vx cA crio cC wceq wi vy
      cB wral wph cA cV wcel wa wps vx cv cC wceq wi vy cB wral vx cA wreu wps
      vx cv cC wceq wi vy cB wral vx wps vx cv cC wceq wi vy cB wral vx cA crio
      wsbc wph cA cV wcel wa wps vx cv cC wceq wi vy cB wral vx cA wreu wps vx
      cv cC wceq wi vy cB wral vx cA crio cA wcel wph cA cV wcel wa cD wps vx
      cv cC wceq wi vy cB wral vx cA crio cA wph cD wps vx cv cC wceq wi vy cB
      wral vx cA crio wceq cA cV wcel riotasvd.1 adantr wph cD cA wcel cA cV
      wcel riotasvd.2 adantr eqeltrrd cA cV wcel wps vx cv cC wceq wi vy cB
      wral vx cA wreu wps vx cv cC wceq wi vy cB wral vx cA crio cA wcel wb wph
      wps vx cv cC wceq wi vy cB wral vx cA cV riotaclbg adantl mpbird wps vx
      cv cC wceq wi vy cB wral vx cA riotasbc syl wph cA cV wcel wa wps vx cv
      cC wceq wi vy cB wral vx cA crio cA wcel wps vx cv cC wceq wi vy cB wral
      vx wps vx cv cC wceq wi vy cB wral vx cA crio wsbc wps wps vx cv cC wceq
      wi vy cB wral vx cA crio cC wceq wi vy cB wral wb wph cA cV wcel wa cD
      wps vx cv cC wceq wi vy cB wral vx cA crio cA wph cD wps vx cv cC wceq wi
      vy cB wral vx cA crio wceq cA cV wcel riotasvd.1 adantr wph cD cA wcel cA
      cV wcel riotasvd.2 adantr eqeltrrd wps vx cv cC wceq wi vy cB wral wps vz
      cv cC wceq wi vy cB wral wps wps vx cv cC wceq wi vy cB wral vx cA crio
      cC wceq wi vy cB wral vx vz wps vx cv cC wceq wi vy cB wral vx cA crio cA
      vx cv vz cv wceq wps vx cv cC wceq wi wps vz cv cC wceq wi vy cB vx cv vz
      cv wceq vx cv cC wceq vz cv cC wceq wps vx cv vz cv cC eqeq1 imbi2d
      ralbidv vz cv wps vx cv cC wceq wi vy cB wral vx cA crio wceq wps vz cv
      cC wceq wi wps wps vx cv cC wceq wi vy cB wral vx cA crio cC wceq wi vy
      cB vy vz cv wps vx cv cC wceq wi vy cB wral vx cA crio wps vx cv cC wceq
      wi vy cB wral vy vx cA wps vx cv cC wceq wi vy cB nfra1 vy cA nfcv
      nfriota nfeq2 vz cv wps vx cv cC wceq wi vy cB wral vx cA crio wceq vz cv
      cC wceq wps vx cv cC wceq wi vy cB wral vx cA crio cC wceq wps vz cv wps
      vx cv cC wceq wi vy cB wral vx cA crio cC eqeq1 imbi2d ralbid sbcie2g syl
      mpbid wps wps vx cv cC wceq wi vy cB wral vx cA crio cC wceq wi vy cB rsp
      syl imp3a wph cA cV wcel wa cD wps vx cv cC wceq wi vy cB wral vx cA crio
      cC wph cD wps vx cv cC wceq wi vy cB wral vx cA crio wceq cA cV wcel
      riotasvd.1 adantr eqeq1d sylibrd $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d x z C $.  $d z D $.  $d z ph $.
    $d x z ps $.
    riotasvdOLD.1 $e |- ( ph -> A. x ph ) $.
    riotasvdOLD.2 $e |- ( ph -> A. y ph ) $.
    riotasvdOLD.3 $e |- ( ph
        -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
    $( Deduction version of ~ riotasv .  (Contributed by NM, 1-Feb-2013.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    riotasvdOLD $p |- ( ( ( ph /\ A e. V ) /\ D e. A /\ ( y e. B /\ ps ) )
         -> D = C ) $=
      wph cA cV wcel wa cD cA wcel vy cv cB wcel wps wa cD cC wceq wph cA cV
      wcel wa cD cA wcel vy cv cB wcel wps cD cC wceq wph cA cV wcel wa cD cA
      wcel wps cD cC wceq wi vy cB wral vy cv cB wcel wps cD cC wceq wi wi wph
      cA cV wcel wa cD cA wcel wps cD cC wceq wi vy cB wral wph cA cV wcel wa
      cD cA wcel wa wps cD cC wceq wi vy cB wral wps vx cv cC wceq wi vy cB
      wral vx cA crio cD wceq wph wps vx cv cC wceq wi vy cB wral vx cA crio cD
      wceq cA cV wcel cD cA wcel wph cD wps vx cv cC wceq wi vy cB wral vx cA
      crio riotasvdOLD.3 eqcomd ad2antrr wph cA cV wcel wa cD cA wcel wa wps vx
      cv cC wceq wi vy cB wral vx cA wreu wps cD cC wceq wi vy cB wral wps vx
      cv cC wceq wi vy cB wral vx cA crio cD wceq wb wph cA cV wcel wa cD cA
      wcel wps vx cv cC wceq wi vy cB wral vx cA wreu wph cA cV wcel wa cD cA
      wcel wps vx cv cC wceq wi vy cB wral vx cA crio cA wcel wps vx cv cC wceq
      wi vy cB wral vx cA wreu wph cD cA wcel wps vx cv cC wceq wi vy cB wral
      vx cA crio cA wcel wb cA cV wcel wph cD wps vx cv cC wceq wi vy cB wral
      vx cA crio cA riotasvdOLD.3 eleq1d adantr cA cV wcel wps vx cv cC wceq wi
      vy cB wral vx cA wreu wps vx cv cC wceq wi vy cB wral vx cA crio cA wcel
      wb wph wps vx cv cC wceq wi vy cB wral vx cA cV riotaclbg adantl bitr4d
      biimpa wph cD cA wcel wps vx cv cC wceq wi vy cB wral vx cA wreu wps cD
      cC wceq wi vy cB wral wps vx cv cC wceq wi vy cB wral vx cA crio cD wceq
      wb cA cV wcel wph cD cA wcel wa wps vx cv cC wceq wi vy cB wral wps cD cC
      wceq wi vy cB wral vx cA cD wph cD cA wcel vx wph vx riotasvdOLD.1 nfi
      wph vx cD cA wph vx cD wnfc vx wps vx cv cC wceq wi vy cB wral vx cA crio
      wnfc wps vx cv cC wceq wi vy cB wral vx cA nfriota1 wph vx cD wps vx cv
      cC wceq wi vy cB wral vx cA crio wph vx riotasvdOLD.1 nfi riotasvdOLD.3
      nfceqdf mpbiri wph vx cA nfcvd nfeld nfan1 wph vx cD wnfc cD cA wcel wph
      vx cD wnfc vx wps vx cv cC wceq wi vy cB wral vx cA crio wnfc wps vx cv
      cC wceq wi vy cB wral vx cA nfriota1 wph vx cD wps vx cv cC wceq wi vy cB
      wral vx cA crio wph vx riotasvdOLD.1 nfi riotasvdOLD.3 nfceqdf mpbiri
      adantr wph cD cA wcel wa wps cD cC wceq wi vx vy cB wph cD cA wcel vy wph
      vy riotasvdOLD.2 nfi wph vy cD cA wph vy cD wnfc vy wps vx cv cC wceq wi
      vy cB wral vx cA crio wnfc wps vx cv cC wceq wi vy cB wral vy vx cA wps
      vx cv cC wceq wi vy cB nfra1 vy cA nfcv nfriota wph vy cD wps vx cv cC
      wceq wi vy cB wral vx cA crio wph vy riotasvdOLD.2 nfi riotasvdOLD.3
      nfceqdf mpbiri wph vy cA nfcvd nfeld nfan1 wph cD cA wcel wa vx cB nfcvd
      wph cD cA wcel wa wps cD cC wceq vx wph cD cA wcel wa wps vx nfvd wph cD
      cA wcel wa vx cD cC wph vx cD wnfc cD cA wcel wph vx cD wnfc vx wps vx cv
      cC wceq wi vy cB wral vx cA crio wnfc wps vx cv cC wceq wi vy cB wral vx
      cA nfriota1 wph vx cD wps vx cv cC wceq wi vy cB wral vx cA crio wph vx
      riotasvdOLD.1 nfi riotasvdOLD.3 nfceqdf mpbiri adantr wph cD cA wcel wa
      vx cC nfcvd nfeqd nfimd nfrald wph cD cA wcel simpr wph vx cv cD wceq wps
      vx cv cC wceq wi vy cB wral wps cD cC wceq wi vy cB wral wb cD cA wcel
      wph vx cv cD wceq wa wps vx cv cC wceq wi wps cD cC wceq wi vy cB wph vx
      cv cD wceq vy wph vy riotasvdOLD.2 nfi wph vy vx cv cD wph vy vx cv nfcvd
      wph vy cD wnfc vy wps vx cv cC wceq wi vy cB wral vx cA crio wnfc wps vx
      cv cC wceq wi vy cB wral vy vx cA wps vx cv cC wceq wi vy cB nfra1 vy cA
      nfcv nfriota wph vy cD wps vx cv cC wceq wi vy cB wral vx cA crio wph vy
      riotasvdOLD.2 nfi riotasvdOLD.3 nfceqdf mpbiri nfeqd nfan1 wph vx cv cD
      wceq wa vx cv cC wceq cD cC wceq wps vx cv cD wceq vx cv cC wceq cD cC
      wceq wb wph vx cv cD cC eqeq1 adantl imbi2d ralbid adantlr riota2df
      adantllr mpdan mpbird ex wps cD cC wceq wi vy cB rsp syl6 imp4a 3imp $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x z C $.  $d z D $.  $d y z E $.
    $d z F $.  $d z ph $.  $d x z ps $.
    riotasv2d.1 $e |- F/ y ph $.
    riotasv2d.2 $e |- ( ph -> F/_ y F ) $.
    riotasv2d.3 $e |- ( ph -> F/ y ch ) $.
    riotasv2d.4 $e |- ( ph
        -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
    riotasv2d.5 $e |- ( ( ph /\ y = E ) -> ( ps <-> ch ) ) $.
    riotasv2d.6 $e |- ( ( ph /\ y = E ) -> C = F ) $.
    riotasv2d.7 $e |- ( ph -> D e. A ) $.
    riotasv2d.8 $e |- ( ph -> E e. B ) $.
    riotasv2d.9 $e |- ( ph -> ch ) $.
    $( Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 2-Mar-2013.) $)
    riotasv2d $p |- ( ( ph /\ A e. V ) -> D = F ) $=
      cA cV wcel wph cA cvv wcel cD cF wceq cA cV elex wph cA cvv wcel wa cE cB
      wcel wch cD cF wceq wph cE cB wcel cA cvv wcel riotasv2d.8 adantr wph wch
      cA cvv wcel riotasv2d.9 adantr wph cA cvv wcel wa vy cv cB wcel wps wa cD
      cC wceq wi cE cB wcel wch wa cD cF wceq wi vy cE cB wph cE cB wcel cA cvv
      wcel riotasv2d.8 adantr wph vy cv cE wceq vy cv cB wcel wps wa cD cC wceq
      wi cE cB wcel wch wa cD cF wceq wi wb cA cvv wcel wph vy cv cE wceq wa vy
      cv cB wcel wps wa cE cB wcel wch wa cD cC wceq cD cF wceq wph vy cv cE
      wceq wa vy cv cB wcel cE cB wcel wps wch vy cv cE wceq vy cv cB wcel cE
      cB wcel wb wph vy cv cE cB eleq1 adantl riotasv2d.5 anbi12d wph vy cv cE
      wceq wa cC cF cD riotasv2d.6 eqeq2d imbi12d adantlr wph wps vx vy cA cB
      cC cD cvv riotasv2d.4 riotasv2d.7 riotasvd wph cA cvv wcel vy riotasv2d.1
      cA cvv wcel vy nfv nfan wph cA cvv wcel wa vy cE nfcvd wph cE cB wcel wch
      wa cD cF wceq wi vy wnf cA cvv wcel wph cE cB wcel wch wa cD cF wceq vy
      wph cE cB wcel wch vy wph cE cB wcel vy nfvd riotasv2d.3 nfand wph vy cD
      cF wph vy cD wnfc vy wps vx cv cC wceq wi vy cB wral vx cA crio wnfc wps
      vx cv cC wceq wi vy cB wral vy vx cA wps vx cv cC wceq wi vy cB nfra1 vy
      cA nfcv nfriota wph vy cD wps vx cv cC wceq wi vy cB wral vx cA crio
      riotasv2d.1 riotasv2d.4 nfceqdf mpbiri riotasv2d.2 nfeqd nfimd adantr
      vtocldf mp2and sylan2 $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x z C $.  $d z D $.  $d y z E $.
    $d z F $.  $d z ph $.  $d x z ps $.
    riotasv2dOLD.1 $e |- ( ph -> A. x ph ) $.
    riotasv2dOLD.2 $e |- ( ph -> A. y ph ) $.
    riotasv2dOLD.3 $e |- ( ph -> ( z e. F -> A. y z e. F ) ) $.
    riotasv2dOLD.4 $e |- ( ph -> ( ch -> A. y ch ) ) $.
    riotasv2dOLD.5 $e |- ( ph
        -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
    riotasv2dOLD.6 $e |- ( ph -> ( y = E -> ( ps <-> ch ) ) ) $.
    riotasv2dOLD.7 $e |- ( ph -> ( y = E -> C = F ) ) $.
    $( Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 1-Feb-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    riotasv2dOLD $p |- ( ( ( ph /\ A e. V ) /\ ( D e. A /\ E e. B /\ ch ) )
             -> D = F ) $=
      cA cV wcel wph cA cvv wcel cD cA wcel cE cB wcel wch w3a cD cF wceq cA cV
      elex wph cA cvv wcel wa cD cA wcel cE cB wcel wch cD cF wceq wph cA cvv
      wcel wa cE cB wcel cD cA wcel wch cD cF wceq wi wph cA cvv wcel wa cE cB
      wcel cD cA wcel wch cD cF wceq wi wi wph cA cvv wcel wa cE cB wcel cE cB
      wcel cD cA wcel wch cD cF wceq wi wi wi wph cA cvv wcel wa cE cB wcel wa
      cD cA wcel cE cB wcel wch cD cF wceq wi wph cA cvv wcel wa cE cB wcel wa
      cD cA wcel cE cB wcel wch cD cF wceq wph cA cvv wcel wa cE cB wcel wa vy
      cE wnfc cD cA wcel cE cB wcel wch w3a cD cF wceq wi vy wnf vy cv cE wceq
      cD cA wcel vy cv cB wcel wps w3a cD cC wceq wi cD cA wcel cE cB wcel wch
      w3a cD cF wceq wi wb wi vy wal cD cA wcel vy cv cB wcel wps w3a cD cC
      wceq wi vy wal cE cB wcel cD cA wcel cE cB wcel wch w3a cD cF wceq wi wph
      cA cvv wcel wa cE cB wcel wa vy cE nfcvd wph cA cvv wcel wa cE cB wcel wa
      cD cA wcel cE cB wcel wch w3a cD cF wceq vy wph cA cvv wcel wa cE cB wcel
      wa cD cA wcel cE cB wcel wch vy wph cA cvv wcel wa cE cB wcel wa vy cD cA
      wph cA cvv wcel wa cE cB wcel wa vy cD wnfc vy wps vx cv cC wceq wi vy cB
      wral vx cA crio wnfc wps vx cv cC wceq wi vy cB wral vy vx cA wps vx cv
      cC wceq wi vy cB nfra1 vy cA nfcv nfriota wph cA cvv wcel wa cE cB wcel
      wa vy cD wps vx cv cC wceq wi vy cB wral vx cA crio wph cA cvv wcel wa cE
      cB wcel vy wph cA cvv wcel vy wph vy riotasv2dOLD.2 nfi cA cvv wcel vy
      nfv nfan cE cB wcel vy nfv nfan wph cD wps vx cv cC wceq wi vy cB wral vx
      cA crio wceq cA cvv wcel cE cB wcel riotasv2dOLD.5 ad2antrr nfceqdf
      mpbiri wph cA cvv wcel wa cE cB wcel wa vy cA nfcvd nfeld wph cA cvv wcel
      wa cE cB wcel wa cE cB wcel vy nfvd wph wch vy wnf cA cvv wcel cE cB wcel
      wph wch vy wph vy riotasv2dOLD.2 nfi riotasv2dOLD.4 nfd ad2antrr nf3and
      wph cA cvv wcel wa cE cB wcel wa vy cD cF wph cA cvv wcel wa cE cB wcel
      wa vy cD wnfc vy wps vx cv cC wceq wi vy cB wral vx cA crio wnfc wps vx
      cv cC wceq wi vy cB wral vy vx cA wps vx cv cC wceq wi vy cB nfra1 vy cA
      nfcv nfriota wph cA cvv wcel wa cE cB wcel wa vy cD wps vx cv cC wceq wi
      vy cB wral vx cA crio wph cA cvv wcel wa cE cB wcel vy wph cA cvv wcel vy
      wph vy riotasv2dOLD.2 nfi cA cvv wcel vy nfv nfan cE cB wcel vy nfv nfan
      wph cD wps vx cv cC wceq wi vy cB wral vx cA crio wceq cA cvv wcel cE cB
      wcel riotasv2dOLD.5 ad2antrr nfceqdf mpbiri wph vy cF wnfc cA cvv wcel cE
      cB wcel wph vy vz cF wph vz nfv wph vz cv cF wcel vy wph vy
      riotasv2dOLD.2 nfi riotasv2dOLD.3 nfd nfcd ad2antrr nfeqd nfimd wph cA
      cvv wcel wa cE cB wcel wa vy cv cE wceq cD cA wcel vy cv cB wcel wps w3a
      cD cC wceq wi cD cA wcel cE cB wcel wch w3a cD cF wceq wi wb wi vy wph cA
      cvv wcel wa cE cB wcel vy wph cA cvv wcel vy wph vy riotasv2dOLD.2 nfi cA
      cvv wcel vy nfv nfan cE cB wcel vy nfv nfan wph vy cv cE wceq cD cA wcel
      vy cv cB wcel wps w3a cD cC wceq wi cD cA wcel cE cB wcel wch w3a cD cF
      wceq wi wb wi cA cvv wcel cE cB wcel wph vy cv cE wceq cD cA wcel vy cv
      cB wcel wps w3a cD cC wceq wi cD cA wcel cE cB wcel wch w3a cD cF wceq wi
      wb wph vy cv cE wceq wa cD cA wcel vy cv cB wcel wps w3a cD cA wcel cE cB
      wcel wch w3a cD cC wceq cD cF wceq wph vy cv cE wceq wa vy cv cB wcel cE
      cB wcel wps wch cD cA wcel vy cv cE wceq vy cv cB wcel cE cB wcel wb wph
      vy cv cE cB eleq1 adantl wph vy cv cE wceq wps wch wb riotasv2dOLD.6 imp
      3anbi23d wph vy cv cE wceq wa cC cF cD wph vy cv cE wceq cC cF wceq
      riotasv2dOLD.7 imp eqeq2d imbi12d ex ad2antrr alrimi wph cA cvv wcel wa
      cD cA wcel vy cv cB wcel wps w3a cD cC wceq wi vy wal cE cB wcel wph cA
      cvv wcel wa cD cA wcel vy cv cB wcel wps w3a cD cC wceq wi vy wph cA cvv
      wcel vy wph vy riotasv2dOLD.2 nfi cA cvv wcel vy nfv nfan wph cA cvv wcel
      wa cD cA wcel vy cv cB wcel wps cD cC wceq wph cA cvv wcel wa cD cA wcel
      vy cv cB wcel wps cD cC wceq wph cA cvv wcel wa cD cA wcel vy cv cB wcel
      wps wa cD cC wceq wph wps vx vy cA cB cC cD cvv riotasv2dOLD.1
      riotasv2dOLD.2 riotasv2dOLD.5 riotasvdOLD 3exp exp4a 3impd alrimi adantr
      wph cA cvv wcel wa cE cB wcel simpr cD cA wcel vy cv cB wcel wps w3a cD
      cC wceq wi cD cA wcel cE cB wcel wch w3a cD cF wceq wi vy cE cB vtoclgft
      syl221anc 3expd com23 ex pm2.43d com23 3imp2 sylanl2 $.
  $}

  ${
    $d x y z A $.  $d x y z B $.  $d x z C $.  $d z D $.  $d x y z E $.
    $d x z ph $.
    riotasv2s.2 $e |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) ) $.
    $( The value of description binder ` D ` for a single-valued class
       expression ` C ( y ) ` (as in e.g. ~ reusv2 ) in the form of a
       substitution instance.  Special case of ~ riota2f .  (Contributed by NM,
       3-Mar-2013.)  (Proof shortened by Mario Carneiro, 6-Dec-2016.) $)
    riotasv2s $p |- ( ( A e. V /\ D e. A /\ ( E e. B /\ [. E / y ]. ph ) )
            -> D = [_ E / y ]_ C ) $=
      cA cV wcel cD cA wcel cE cB wcel wph vy cE wsbc wa w3a cD cA wcel cE cB
      wcel wph vy cE wsbc wa wa cA cV wcel cD vy cE cC csb wceq cA cV wcel cD
      cA wcel cE cB wcel wph vy cE wsbc wa 3simpc cA cV wcel cD cA wcel cE cB
      wcel wph vy cE wsbc wa simp1 cD cA wcel cE cB wcel wph vy cE wsbc wa wa
      wph wph vy cE wsbc vx vy cA cB cC cD cE vy cE cC csb cV cD cA wcel cE cB
      wcel wph vy cE wsbc wa vy vy cD cA vy cD wph vx cv cC wceq wi vy cB wral
      vx cA crio riotasv2s.2 wph vx cv cC wceq wi vy cB wral vy vx cA wph vx cv
      cC wceq wi vy cB nfra1 vy cA nfcv nfriota nfcxfr nfel1 cE cB wcel wph vy
      cE wsbc vy cE cB wcel vy nfv wph vy cE nfsbc1v nfan nfan vy vy cE cC csb
      wnfc cD cA wcel cE cB wcel wph vy cE wsbc wa wa vy cE cC nfcsb1v a1i wph
      vy cE wsbc vy wnf cD cA wcel cE cB wcel wph vy cE wsbc wa wa wph vy cE
      nfsbc1v a1i cD wph vx cv cC wceq wi vy cB wral vx cA crio wceq cD cA wcel
      cE cB wcel wph vy cE wsbc wa wa riotasv2s.2 a1i vy cv cE wceq wph wph vy
      cE wsbc wb cD cA wcel cE cB wcel wph vy cE wsbc wa wa wph vy cE sbceq1a
      adantl vy cv cE wceq cC vy cE cC csb wceq cD cA wcel cE cB wcel wph vy cE
      wsbc wa wa vy cE cC csbeq1a adantl cD cA wcel cE cB wcel wph vy cE wsbc
      wa simpl cD cA wcel cE cB wcel wph vy cE wsbc simprl cD cA wcel cE cB
      wcel wph vy cE wsbc simprr riotasv2d syl2anc $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d x z C $.  $d x z ph $.  $d z D $.
    riotasv.1 $e |- A e. _V $.
    riotasv.2 $e |- D = ( iota_ x e. A A. y e. B ( ph -> x = C ) ) $.
    $( Value of description binder ` D ` for a single-valued class expression
       ` C ( y ) ` (as in e.g. ~ reusv2 ).  Special case of ~ riota2f .
       (Contributed by NM, 26-Jan-2013.)  (Proof shortened by Mario Carneiro,
       6-Dec-2016.) $)
    riotasv $p |- ( ( D e. A /\ y e. B /\ ph ) -> D = C ) $=
      cD cA wcel vy cv cB wcel wph cD cC wceq cD cA wcel cA cvv wcel vy cv cB
      wcel wph wa cD cC wceq wi riotasv.1 cD cA wcel wph vx vy cA cB cC cD cvv
      cD wph vx cv cC wceq wi vy cB wral vx cA crio wceq cD cA wcel riotasv.2
      a1i cD cA wcel id riotasvd mpan2 3impib $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d x z C $.  $d z D $.  $d z ph $.
    $d x z ps $.
    riotasv3d.1 $e |- F/ y ph $.
    riotasv3d.2 $e |- ( ph -> F/ y th ) $.
    riotasv3d.3 $e |- ( ph
           -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
    riotasv3d.4 $e |- ( ( ph /\ C = D ) -> ( ch <-> th ) ) $.
    riotasv3d.5 $e |- ( ph -> ( ( y e. B /\ ps ) -> ch ) ) $.
    riotasv3d.6 $e |- ( ph -> D e. A ) $.
    riotasv3d.7 $e |- ( ph -> E. y e. B ps ) $.
    $( A property ` ch ` holding for a representative of a single-valued class
       expression ` C ( y ) ` (see e.g. ~ reusv2 ) also holds for its
       description binder ` D ` (in the form of property ` th ` ).
       (Contributed by NM, 5-Mar-2013.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
    riotasv3d $p |- ( ( ph /\ A e. V ) -> th ) $=
      cA cV wcel wph cA cvv wcel wth cA cV elex wph cA cvv wcel wa wps vy cB
      wrex wth wph wps vy cB wrex cA cvv wcel riotasv3d.7 adantr wph cA cvv
      wcel wps vy cB wrex wth wi wph cA cvv wcel wps wth wi vy cB wral wps vy
      cB wrex wth wi wph cA cvv wcel wps wth wi vy cB riotasv3d.1 cA cvv wcel
      vy nfv wph cA cvv wcel vy cv cB wcel wps wth wph cA cvv wcel vy cv cB
      wcel wps wa wa wa wch wth wph vy cv cB wcel wps wa wch cA cvv wcel wph vy
      cv cB wcel wps wa wch riotasv3d.5 imp adantrl wph cA cvv wcel vy cv cB
      wcel wps wa wa cC cD wceq wch wth wb wph cA cvv wcel vy cv cB wcel wps wa
      wa wa cD cC wph cA cvv wcel vy cv cB wcel wps wa cD cC wceq wph wps vx vy
      cA cB cC cD cvv riotasv3d.3 riotasv3d.6 riotasvd impr eqcomd riotasv3d.4
      syldan mpbid exp45 ralrimd wph wth vy wnf wps wth wi vy cB wral wps vy cB
      wrex wth wi wb riotasv3d.2 wps wth vy cB r19.23t syl sylibd imp mpd
      sylan2 $.
  $}

  ${
    $d x y z A $.  $d x z B $.  $d x z C $.  $d z D $.  $d z ph $.
    $d x z ps $.
    riotasv3dOLD.1 $e |- ( ph -> A. x ph ) $.
    riotasv3dOLD.2 $e |- ( ph -> A. y ph ) $.
    riotasv3dOLD.3 $e |- ( ph -> ( th -> A. y th ) ) $.
    riotasv3dOLD.4 $e |- ( ph
           -> D = ( iota_ x e. A A. y e. B ( ps -> x = C ) ) ) $.
    riotasv3dOLD.5 $e |- ( ph -> ( C = D -> ( ch <-> th ) ) ) $.
    riotasv3dOLD.6 $e |- ( ph -> ( ( y e. B /\ ps ) -> ch ) ) $.
    $( A property ` ch ` holding for a representative of a single-valued class
       expression ` C ( y ) ` (see e.g. ~ reusv2 ) also holds for its
       description binder ` D ` (in the form of property ` th ` ).
       (Contributed by NM, 1-Feb-2013.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    riotasv3dOLD $p |- ( ( ph /\ ( A e. V /\ D e. A /\ E. y e. B ps ) )
          -> th ) $=
      wph cA cV wcel cD cA wcel wps vy cB wrex wth cA cV wcel cA cvv wcel wph
      cD cA wcel wps vy cB wrex wth wi wi cA cV elex wph cA cvv wcel cD cA wcel
      wps vy cB wrex wth wi wph cA cvv wcel cD cA wcel wa wps wth wi vy cB wral
      wps vy cB wrex wth wi wph cA cvv wcel cD cA wcel wa wps wth wi wi vy cB
      wral cA cvv wcel cD cA wcel wa wps wth wi vy cB wral wi wph cA cvv wcel
      cD cA wcel wa wps wth wi wi vy cB wph vy riotasv3dOLD.2 nfi wph cA cvv
      wcel cD cA wcel wa vy cv cB wcel wps wth wi wph cA cvv wcel cD cA wcel wa
      vy cv cB wcel wps wth wph cA cvv wcel cD cA wcel wa vy cv cB wcel wps wa
      wa wa wch wth wph vy cv cB wcel wps wa wch cA cvv wcel cD cA wcel wa wph
      vy cv cB wcel wps wa wch riotasv3dOLD.6 imp adantrl wph cA cvv wcel cD cA
      wcel wa vy cv cB wcel wps wa wa wch wth wb wph cA cvv wcel cD cA wcel wa
      vy cv cB wcel wps wa wa cC cD wceq wch wth wb wph cA cvv wcel cD cA wcel
      vy cv cB wcel wps wa cC cD wceq wph cA cvv wcel cD cA wcel vy cv cB wcel
      wps wa cC cD wceq wi wi wph cA cvv wcel wa cD cA wcel vy cv cB wcel wps
      wa cC cD wceq wph cA cvv wcel wa cD cA wcel vy cv cB wcel wps wa w3a cD
      cC wph wps vx vy cA cB cC cD cvv riotasv3dOLD.1 riotasv3dOLD.2
      riotasv3dOLD.4 riotasvdOLD eqcomd 3exp ex imp4c riotasv3dOLD.5 syld imp
      mpbid exp45 com23 ralrimi wph cA cvv wcel cD cA wcel wa vy wnf cA cvv
      wcel cD cA wcel wa wps wth wi wi vy cB wral cA cvv wcel cD cA wcel wa wps
      wth wi vy cB wral wi wb wph cA cvv wcel cD cA wcel vy wph cA cvv wcel vy
      nfvd wph vy cD cA wph vy cD wnfc vy wps vx cv cC wceq wi vy cB wral vx cA
      crio wnfc wps vx cv cC wceq wi vy cB wral vy vx cA wps vx cv cC wceq wi
      vy cB nfra1 vy cA nfcv nfriota wph vy cD wps vx cv cC wceq wi vy cB wral
      vx cA crio wph vy riotasv3dOLD.2 nfi riotasv3dOLD.4 nfceqdf mpbiri wph vy
      cA nfcvd nfeld nfand cA cvv wcel cD cA wcel wa wps wth wi vy cB r19.21t
      syl mpbid wph wth vy wnf wps wth wi vy cB wral wps vy cB wrex wth wi wb
      wph wth vy wph vy riotasv3dOLD.2 nfi riotasv3dOLD.3 nfd wps wth vy cB
      r19.23t syl sylibd exp3a syl5 3imp2 $.
  $}


