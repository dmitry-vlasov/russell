
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_intersection_of_a_class.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Indexed union and intersection

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c U_ $. $( Underlined big cup. $)
  $c |^|_ $. $( Underlined big cap. $)

  $( Extend class notation to include indexed union.  Note:  Historically
     (prior to 21-Oct-2005), set.mm used the notation ` U. x e. A B ` , with
     the same union symbol as ~ cuni .  While that syntax was unambiguous, it
     did not allow for LALR parsing of the syntax constructions in set.mm.  The
     new syntax uses as distinguished symbol ` U_ ` instead of ` U. ` and does
     allow LALR parsing.  Thanks to Peter Backes for suggesting this change. $)
  ciun $a class U_ x e. A B $.

  $( Extend class notation to include indexed intersection.  Note:
     Historically (prior to 21-Oct-2005), set.mm used the notation
     ` |^| x e. A B ` , with the same intersection symbol as ~ cint .  Although
     that syntax was unambiguous, it did not allow for LALR parsing of the
     syntax constructions in set.mm.  The new syntax uses a distinguished
     symbol ` |^|_ ` instead of ` |^| ` and does allow LALR parsing.  Thanks to
     Peter Backes for suggesting this change. $)
  ciin $a class |^|_ x e. A B $.

  ${
    $d x y $.  $d y A $.  $d y B $.
    $( Define indexed union.  Definition indexed union in [Stoll] p. 45.  In
       most applications, ` A ` is independent of ` x ` (although this is not
       required by the definition), and ` B ` depends on ` x ` i.e. can be read
       informally as ` B ( x ) ` .  We call ` x ` the index, ` A ` the index
       set, and ` B ` the indexed set.  In most books, ` x e. A ` is written as
       a subscript or underneath a union symbol ` U. ` .  We use a special
       union symbol ` U_ ` to make it easier to distinguish from plain class
       union.  In many theorems, you will see that ` x ` and ` A ` are in the
       same distinct variable group (meaning ` A ` cannot depend on ` x ` ) and
       that ` B ` and ` x ` do not share a distinct variable group (meaning
       that can be thought of as ` B ( x ) ` i.e. can be substituted with a
       class expression containing ` x ` ).  An alternate definition tying
       indexed union to ordinary union is ~ dfiun2 .  Theorem ~ uniiun provides
       a definition of ordinary union in terms of indexed union.  Theorems
       ~ fniunfv and ~ funiunfv are useful when ` B ` is a function.
       (Contributed by NM, 27-Jun-1998.) $)
    df-iun $a |- U_ x e. A B = { y | E. x e. A y e. B } $.

    $( Define indexed intersection.  Definition of [Stoll] p. 45.  See the
       remarks for its sibling operation of indexed union ~ df-iun .  An
       alternate definition tying indexed intersection to ordinary intersection
       is ~ dfiin2 .  Theorem ~ intiin provides a definition of ordinary
       intersection in terms of indexed intersection.  (Contributed by NM,
       27-Jun-1998.) $)
    df-iin $a |- |^|_ x e. A B = { y | A. x e. A y e. B } $.
  $}

  ${
    $d x y A $.  $d y B $.  $d y C $.
    $( Membership in indexed union.  (Contributed by NM, 3-Sep-2003.) $)
    eliun $p |- ( A e. U_ x e. B C <-> E. x e. B A e. C ) $=
      cA vx cB cC ciun wcel cA cvv wcel cA cC wcel vx cB wrex cA vx cB cC ciun
      elex cA cC wcel cA cvv wcel vx cB cA cC elex rexlimivw vy cv cC wcel vx
      cB wrex cA cC wcel vx cB wrex vy cA vx cB cC ciun cvv vy cv cA wceq vy cv
      cC wcel cA cC wcel vx cB vy cv cA cC eleq1 rexbidv vx vy cB cC df-iun
      elab2g pm5.21nii $.

    $( Membership in indexed intersection.  (Contributed by NM, 3-Sep-2003.) $)
    eliin $p |- ( A e. V -> ( A e. |^|_ x e. B C <-> A. x e. B A e. C ) ) $=
      vy cv cC wcel vx cB wral cA cC wcel vx cB wral vy cA vx cB cC ciin cV vy
      cv cA wceq vy cv cC wcel cA cC wcel vx cB vy cv cA cC eleq1 ralbidv vx vy
      cB cC df-iin elab2g $.
  $}

  ${
    $d y z A $.  $d x z B $.  $d z C $.  $d x y $.
    $( Commutation of indexed unions.  (Contributed by NM, 18-Dec-2008.) $)
    iuncom $p |- U_ x e. A U_ y e. B C = U_ y e. B U_ x e. A C $=
      vz vx cA vy cB cC ciun ciun vy cB vx cA cC ciun ciun vz cv vy cB cC ciun
      wcel vx cA wrex vz cv vx cA cC ciun wcel vy cB wrex vz cv vx cA vy cB cC
      ciun ciun wcel vz cv vy cB vx cA cC ciun ciun wcel vz cv cC wcel vy cB
      wrex vx cA wrex vz cv cC wcel vx cA wrex vy cB wrex vz cv vy cB cC ciun
      wcel vx cA wrex vz cv vx cA cC ciun wcel vy cB wrex vz cv cC wcel vx vy
      cA cB rexcom vz cv vy cB cC ciun wcel vz cv cC wcel vy cB wrex vx cA vy
      vz cv cB cC eliun rexbii vz cv vx cA cC ciun wcel vz cv cC wcel vx cA
      wrex vy cB vx vz cv cA cC eliun rexbii 3bitr4i vx vz cv cA vy cB cC ciun
      eliun vy vz cv cB vx cA cC ciun eliun 3bitr4i eqriv $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d x y z $.
    $( Commutation of union with indexed union.  (Contributed by Mario
       Carneiro, 18-Jan-2014.) $)
    iuncom4 $p |- U_ x e. A U. B = U. U_ x e. A B $=
      vy vx cA cB cuni ciun vx cA cB ciun cuni vy cv cB cuni wcel vx cA wrex vy
      cv vz cv wcel vz vx cA cB ciun wrex vy cv vx cA cB cuni ciun wcel vy cv
      vx cA cB ciun cuni wcel vy cv vz cv wcel vz cB wrex vx cA wrex vz cv cB
      wcel vx cA wrex vy cv vz cv wcel wa vz wex vy cv cB cuni wcel vx cA wrex
      vy cv vz cv wcel vz vx cA cB ciun wrex vy cv vz cv wcel vz cB wrex vx cA
      wrex vz cv cB wcel vy cv vz cv wcel wa vx cA wrex vz wex vz cv cB wcel vx
      cA wrex vy cv vz cv wcel wa vz wex vy cv vz cv wcel vz cB wrex vx cA wrex
      vz cv cB wcel vy cv vz cv wcel wa vz wex vx cA wrex vz cv cB wcel vy cv
      vz cv wcel wa vx cA wrex vz wex vy cv vz cv wcel vz cB wrex vz cv cB wcel
      vy cv vz cv wcel wa vz wex vx cA vy cv vz cv wcel vz cB df-rex rexbii vz
      cv cB wcel vy cv vz cv wcel wa vx vz cA rexcom4 bitri vz cv cB wcel vy cv
      vz cv wcel wa vx cA wrex vz cv cB wcel vx cA wrex vy cv vz cv wcel wa vz
      vz cv cB wcel vy cv vz cv wcel vx cA r19.41v exbii bitri vy cv cB cuni
      wcel vy cv vz cv wcel vz cB wrex vx cA vz vy cv cB eluni2 rexbii vy cv vz
      cv wcel vz vx cA cB ciun wrex vz cv vx cA cB ciun wcel vy cv vz cv wcel
      wa vz wex vz cv cB wcel vx cA wrex vy cv vz cv wcel wa vz wex vy cv vz cv
      wcel vz vx cA cB ciun df-rex vz cv vx cA cB ciun wcel vy cv vz cv wcel wa
      vz cv cB wcel vx cA wrex vy cv vz cv wcel wa vz vz cv vx cA cB ciun wcel
      vz cv cB wcel vx cA wrex vy cv vz cv wcel vx vz cv cA cB eliun anbi1i
      exbii bitri 3bitr4i vx vy cv cA cB cuni eliun vz vy cv vx cA cB ciun
      eluni2 3bitr4i eqriv $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Indexed union of a constant class, i.e. where ` B ` does not depend on
       ` x ` .  (Contributed by NM, 5-Sep-2004.)  (Proof shortened by Andrew
       Salmon, 25-Jul-2011.) $)
    iunconst $p |- ( A =/= (/) -> U_ x e. A B = B ) $=
      cA c0 wne vy vx cA cB ciun cB cA c0 wne vy cv cB wcel vy cv cB wcel vx cA
      wrex vy cv vx cA cB ciun wcel vy cv cB wcel vx cA r19.9rzv vx vy cv cA cB
      eliun syl6rbbr eqrdv $.

    $( Indexed intersection of a constant class, i.e. where ` B ` does not
       depend on ` x ` .  (Contributed by Mario Carneiro, 6-Feb-2015.) $)
    iinconst $p |- ( A =/= (/) -> |^|_ x e. A B = B ) $=
      cA c0 wne vy vx cA cB ciin cB cA c0 wne vy cv cB wcel vy cv cB wcel vx cA
      wral vy cv vx cA cB ciin wcel vy cv cB wcel vx cA r19.3rzv vy cv cvv wcel
      vy cv vx cA cB ciin wcel vy cv cB wcel vx cA wral wb vy vex vx vy cv cA
      cB cvv eliin ax-mp syl6rbbr eqrdv $.
  $}

  ${
    $d x y $.  $d y z A $.  $d x z B $.  $d z C $.
    $( Law combining indexed union with indexed intersection.  Eq. 14 in
       [KuratowskiMostowski] p. 109.  This theorem also appears as the last
       example at ~ http://en.wikipedia.org/wiki/Union%5F%28set%5Ftheory%29 .
       (Contributed by NM, 17-Aug-2004.)  (Proof shortened by Andrew Salmon,
       25-Jul-2011.) $)
    iuniin $p |- U_ x e. A |^|_ y e. B C C_ |^|_ y e. B U_ x e. A C $=
      vz vx cA vy cB cC ciin ciun vy cB vx cA cC ciun ciin vz cv vy cB cC ciin
      wcel vx cA wrex vz cv vx cA cC ciun wcel vy cB wral vz cv vx cA vy cB cC
      ciin ciun wcel vz cv vy cB vx cA cC ciun ciin wcel vz cv cC wcel vy cB
      wral vx cA wrex vz cv cC wcel vx cA wrex vy cB wral vz cv vy cB cC ciin
      wcel vx cA wrex vz cv vx cA cC ciun wcel vy cB wral vz cv cC wcel vx vy
      cA cB r19.12 vz cv vy cB cC ciin wcel vz cv cC wcel vy cB wral vx cA vz
      cv cvv wcel vz cv vy cB cC ciin wcel vz cv cC wcel vy cB wral wb vz vex
      vy vz cv cB cC cvv eliin ax-mp rexbii vz cv vx cA cC ciun wcel vz cv cC
      wcel vx cA wrex vy cB vx vz cv cA cC eliun ralbii 3imtr4i vx vz cv cA vy
      cB cC ciin eliun vz cv cvv wcel vz cv vy cB vx cA cC ciun ciin wcel vz cv
      vx cA cC ciun wcel vy cB wral wb vz vex vy vz cv cB vx cA cC ciun cvv
      eliin ax-mp 3imtr4i ssriv $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.
    $( Subclass theorem for indexed union.  (Contributed by NM, 10-Dec-2004.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    iunss1 $p |- ( A C_ B -> U_ x e. A C C_ U_ x e. B C ) $=
      cA cB wss vy vx cA cC ciun vx cB cC ciun cA cB wss vy cv cC wcel vx cA
      wrex vy cv cC wcel vx cB wrex vy cv vx cA cC ciun wcel vy cv vx cB cC
      ciun wcel vy cv cC wcel vx cA cB ssrexv vx vy cv cA cC eliun vx vy cv cB
      cC eliun 3imtr4g ssrdv $.

    $( Subclass theorem for indexed union.  (Contributed by NM,
       24-Jan-2012.) $)
    iinss1 $p |- ( A C_ B -> |^|_ x e. B C C_ |^|_ x e. A C ) $=
      cA cB wss vy vx cB cC ciin vx cA cC ciin cA cB wss vy cv cC wcel vx cB
      wral vy cv cC wcel vx cA wral vy cv vx cB cC ciin wcel vy cv vx cA cC
      ciin wcel vy cv cC wcel vx cA cB ssralv vy cv cvv wcel vy cv vx cB cC
      ciin wcel vy cv cC wcel vx cB wral wb vy vex vx vy cv cB cC cvv eliin
      ax-mp vy cv cvv wcel vy cv vx cA cC ciin wcel vy cv cC wcel vx cA wral wb
      vy vex vx vy cv cA cC cvv eliin ax-mp 3imtr4g ssrdv $.

    $( Equality theorem for indexed union.  (Contributed by NM,
       27-Jun-1998.) $)
    iuneq1 $p |- ( A = B -> U_ x e. A C = U_ x e. B C ) $=
      cA cB wss cB cA wss wa vx cA cC ciun vx cB cC ciun wss vx cB cC ciun vx
      cA cC ciun wss wa cA cB wceq vx cA cC ciun vx cB cC ciun wceq cA cB wss
      vx cA cC ciun vx cB cC ciun wss cB cA wss vx cB cC ciun vx cA cC ciun wss
      vx cA cB cC iunss1 vx cB cA cC iunss1 anim12i cA cB eqss vx cA cC ciun vx
      cB cC ciun eqss 3imtr4i $.

    $( Equality theorem for restricted existential quantifier.  (Contributed by
       NM, 27-Jun-1998.) $)
    iineq1 $p |- ( A = B -> |^|_ x e. A C = |^|_ x e. B C ) $=
      cA cB wceq vy cv cC wcel vx cA wral vy cab vy cv cC wcel vx cB wral vy
      cab vx cA cC ciin vx cB cC ciin cA cB wceq vy cv cC wcel vx cA wral vy cv
      cC wcel vx cB wral vy vy cv cC wcel vx cA cB raleq abbidv vx vy cA cC
      df-iin vx vy cB cC df-iin 3eqtr4g $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( Subclass theorem for indexed union.  (Contributed by NM, 26-Nov-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    ss2iun $p |- ( A. x e. A B C_ C -> U_ x e. A B C_ U_ x e. A C ) $=
      cB cC wss vx cA wral vy vx cA cB ciun vx cA cC ciun cB cC wss vx cA wral
      vy cv cB wcel vx cA wrex vy cv cC wcel vx cA wrex vy cv vx cA cB ciun
      wcel vy cv vx cA cC ciun wcel cB cC wss vx cA wral vy cv cB wcel vy cv cC
      wcel wi vx cA wral vy cv cB wcel vx cA wrex vy cv cC wcel vx cA wrex wi
      cB cC wss vy cv cB wcel vy cv cC wcel wi vx cA cB cC vy cv ssel ralimi vy
      cv cB wcel vy cv cC wcel vx cA rexim syl vx vy cv cA cB eliun vx vy cv cA
      cC eliun 3imtr4g ssrdv $.

    $( Equality theorem for indexed union.  (Contributed by NM,
       22-Oct-2003.) $)
    iuneq2 $p |- ( A. x e. A B = C -> U_ x e. A B = U_ x e. A C ) $=
      cB cC wss vx cA wral cC cB wss vx cA wral wa vx cA cB ciun vx cA cC ciun
      wss vx cA cC ciun vx cA cB ciun wss wa cB cC wceq vx cA wral vx cA cB
      ciun vx cA cC ciun wceq cB cC wss vx cA wral vx cA cB ciun vx cA cC ciun
      wss cC cB wss vx cA wral vx cA cC ciun vx cA cB ciun wss vx cA cB cC
      ss2iun vx cA cC cB ss2iun anim12i cB cC wceq vx cA wral cB cC wss cC cB
      wss wa vx cA wral cB cC wss vx cA wral cC cB wss vx cA wral wa cB cC wceq
      cB cC wss cC cB wss wa vx cA cB cC eqss ralbii cB cC wss cC cB wss vx cA
      r19.26 bitri vx cA cB ciun vx cA cC ciun eqss 3imtr4i $.

    $( Equality theorem for indexed intersection.  (Contributed by NM,
       22-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    iineq2 $p |- ( A. x e. A B = C -> |^|_ x e. A B = |^|_ x e. A C ) $=
      cB cC wceq vx cA wral vy cv cB wcel vx cA wral vy cab vy cv cC wcel vx cA
      wral vy cab vx cA cB ciin vx cA cC ciin cB cC wceq vx cA wral vy cv cB
      wcel vx cA wral vy cv cC wcel vx cA wral vy cB cC wceq vx cA wral vy cv
      cB wcel vy cv cC wcel wb vx cA wral vy cv cB wcel vx cA wral vy cv cC
      wcel vx cA wral wb cB cC wceq vy cv cB wcel vy cv cC wcel wb vx cA cB cC
      vy cv eleq2 ralimi vy cv cB wcel vy cv cC wcel vx cA ralbi syl abbidv vx
      vy cA cB df-iin vx vy cA cC df-iin 3eqtr4g $.
  $}

  ${
    iuneq2i.1 $e |- ( x e. A -> B = C ) $.
    $( Equality inference for indexed union.  (Contributed by NM,
       22-Oct-2003.) $)
    iuneq2i $p |- U_ x e. A B = U_ x e. A C $=
      cB cC wceq vx cA cB ciun vx cA cC ciun wceq vx cA vx cA cB cC iuneq2
      iuneq2i.1 mprg $.

    $( Equality inference for indexed intersection.  (Contributed by NM,
       22-Oct-2003.) $)
    iineq2i $p |- |^|_ x e. A B = |^|_ x e. A C $=
      cB cC wceq vx cA cB ciin vx cA cC ciin wceq vx cA vx cA cB cC iineq2
      iuneq2i.1 mprg $.
  $}

  ${
    iineq2d.1 $e |- F/ x ph $.
    iineq2d.2 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
    $( Equality deduction for indexed intersection.  (Contributed by NM,
       7-Dec-2011.) $)
    iineq2d $p |- ( ph -> |^|_ x e. A B = |^|_ x e. A C ) $=
      wph cB cC wceq vx cA wral vx cA cB ciin vx cA cC ciin wceq wph cB cC wceq
      vx cA iineq2d.1 wph vx cv cA wcel cB cC wceq iineq2d.2 ex ralrimi vx cA
      cB cC iineq2 syl $.
  $}

  ${
    $d x ph $.
    iuneq2dv.1 $e |- ( ( ph /\ x e. A ) -> B = C ) $.
    $( Equality deduction for indexed union.  (Contributed by NM,
       3-Aug-2004.) $)
    iuneq2dv $p |- ( ph -> U_ x e. A B = U_ x e. A C ) $=
      wph cB cC wceq vx cA wral vx cA cB ciun vx cA cC ciun wceq wph cB cC wceq
      vx cA iuneq2dv.1 ralrimiva vx cA cB cC iuneq2 syl $.

    $( Equality deduction for indexed intersection.  (Contributed by NM,
       3-Aug-2004.) $)
    iineq2dv $p |- ( ph -> |^|_ x e. A B = |^|_ x e. A C ) $=
      wph vx cA cB cC wph vx nfv iuneq2dv.1 iineq2d $.
  $}

  ${
    $d x A $.  $d x B $.
    iuneq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for indexed union, deduction version.  (Contributed by
       Drahflow, 22-Oct-2015.) $)
    iuneq1d $p |- ( ph -> U_ x e. A C = U_ x e. B C ) $=
      wph cA cB wceq vx cA cC ciun vx cB cC ciun wceq iuneq1d.1 vx cA cB cC
      iuneq1 syl $.

    ${
      $d x ph $.
      iuneq12d.2 $e |- ( ph -> C = D ) $.
      $( Equality deduction for indexed union, deduction version.  (Contributed
         by Drahflow, 22-Oct-2015.) $)
      iuneq12d $p |- ( ph -> U_ x e. A C = U_ x e. B D ) $=
        wph vx cA cC ciun vx cB cC ciun vx cB cD ciun wph vx cA cB cC iuneq1d.1
        iuneq1d wph vx cB cC cD wph cC cD wceq vx cv cB wcel iuneq12d.2 adantr
        iuneq2dv eqtrd $.
    $}
  $}

  ${
    $d x ph $.  $d x A $.
    iuneq2d.2 $e |- ( ph -> B = C ) $.
    $( Equality deduction for indexed union.  (Contributed by Drahflow,
       22-Oct-2015.) $)
    iuneq2d $p |- ( ph -> U_ x e. A B = U_ x e. A C ) $=
      wph vx cA cB cC wph cB cC wceq vx cv cA wcel iuneq2d.2 adantr iuneq2dv $.
  $}

  ${
    $d z A $.  $d z B $.  $d x z $.  $d y z $.
    nfiun.1 $e |- F/_ y A $.
    nfiun.2 $e |- F/_ y B $.
    $( Bound-variable hypothesis builder for indexed union.  (Contributed by
       Mario Carneiro, 25-Jan-2014.) $)
    nfiun $p |- F/_ y U_ x e. A B $=
      vy vx cA cB ciun vz cv cB wcel vx cA wrex vz cab vx vz cA cB df-iun vz cv
      cB wcel vx cA wrex vy vz vz cv cB wcel vy vx cA nfiun.1 vy vz cB nfiun.2
      nfcri nfrex nfab nfcxfr $.

    $( Bound-variable hypothesis builder for indexed intersection.
       (Contributed by Mario Carneiro, 25-Jan-2014.) $)
    nfiin $p |- F/_ y |^|_ x e. A B $=
      vy vx cA cB ciin vz cv cB wcel vx cA wral vz cab vx vz cA cB df-iin vz cv
      cB wcel vx cA wral vy vz vz cv cB wcel vy vx cA nfiun.1 vy vz cB nfiun.2
      nfcri nfral nfab nfcxfr $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( Bound-variable hypothesis builder for indexed union.  (Contributed by
       NM, 12-Oct-2003.) $)
    nfiu1 $p |- F/_ x U_ x e. A B $=
      vx vx cA cB ciun vy cv cB wcel vx cA wrex vy cab vx vy cA cB df-iun vy cv
      cB wcel vx cA wrex vx vy vy cv cB wcel vx cA nfre1 nfab nfcxfr $.

    $( Bound-variable hypothesis builder for indexed intersection.
       (Contributed by NM, 15-Oct-2003.) $)
    nfii1 $p |- F/_ x |^|_ x e. A B $=
      vx vx cA cB ciin vy cv cB wcel vx cA wral vy cab vx vy cA cB df-iin vy cv
      cB wcel vx cA wral vx vy vy cv cB wcel vx cA nfra1 nfab nfcxfr $.
  $}

  ${
    $d y z w A $.  $d y z w B $.  $d w C z $.  $d w x y z $.
    $( Alternate definition of indexed union when ` B ` is a set.  Definition
       15(a) of [Suppes] p. 44.  (Contributed by NM, 23-Mar-2006.)  (Proof
       shortened by Andrew Salmon, 25-Jul-2011.) $)
    dfiun2g $p |- ( A. x e. A B e. C ->
                  U_ x e. A B = U. { y | E. x e. A y = B } ) $=
      cB cC wcel vx cA wral vz vx cA cB ciun vy cv cB wceq vx cA wrex vy cab
      cuni cB cC wcel vx cA wral vz cv cB wcel vx cA wrex vz cv vy cv wcel vy
      cv cB wceq vx cA wrex wa vy wex vz cv vx cA cB ciun wcel vz cv vy cv cB
      wceq vx cA wrex vy cab cuni wcel cB cC wcel vx cA wral vz cv cB wcel vx
      cA wrex vy cv cB wceq vz cv vy cv wcel wa vx cA wrex vy wex vz cv vy cv
      wcel vy cv cB wceq vx cA wrex wa vy wex cB cC wcel vx cA wral vz cv cB
      wcel vx cA wrex vy cv cB wceq vz cv vy cv wcel wa vy wex vx cA wrex vy cv
      cB wceq vz cv vy cv wcel wa vx cA wrex vy wex cB cC wcel vx cA wral vz cv
      cB wcel vy cv cB wceq vz cv vy cv wcel wa vy wex vx cA cB cC wcel vx cA
      nfra1 cB cC wcel vx cA wral vx cv cA wcel vz cv cB wcel vy cv cB wceq vz
      cv vy cv wcel wa vy wex wb cB cC wcel vx cA wral vx cv cA wcel cB cC wcel
      vz cv cB wcel vy cv cB wceq vz cv vy cv wcel wa vy wex wb cB cC wcel vx
      cA rsp vy vz cv cB cC clel3g syl6 imp rexbida vy cv cB wceq vz cv vy cv
      wcel wa vx vy cA rexcom4 syl6bb vy cv cB wceq vz cv vy cv wcel wa vx cA
      wrex vy wex vy cv cB wceq vx cA wrex vz cv vy cv wcel wa vy wex vz cv vy
      cv wcel vy cv cB wceq vx cA wrex wa vy wex vy cv cB wceq vz cv vy cv wcel
      wa vx cA wrex vy cv cB wceq vx cA wrex vz cv vy cv wcel wa vy vy cv cB
      wceq vz cv vy cv wcel vx cA r19.41v exbii vy cv cB wceq vx cA wrex vz cv
      vy cv wcel vy exancom bitri syl6bb vx vz cv cA cB eliun vy cv cB wceq vx
      cA wrex vy vz cv eluniab 3bitr4g eqrdv $.

    $( Alternate definition of indexed intersection when ` B ` is a set.
       (Contributed by Jeff Hankins, 27-Aug-2009.) $)
    dfiin2g $p |- ( A. x e. A B e. C
               -> |^|_ x e. A B = |^| { y | E. x e. A y = B } ) $=
      cB cC wcel vx cA wral vw cv cB wcel vx cA wral vw cab vz cv vy cv cB wceq
      vx cA wrex vy cab wcel vw cv vz cv wcel wi vz wal vw cab vx cA cB ciin vy
      cv cB wceq vx cA wrex vy cab cint cB cC wcel vx cA wral vw cv cB wcel vx
      cA wral vz cv vy cv cB wceq vx cA wrex vy cab wcel vw cv vz cv wcel wi vz
      wal vw vw cv cB wcel vx cA wral vx cv cA wcel vw cv cB wcel wi vx wal cB
      cC wcel vx cA wral vz cv vy cv cB wceq vx cA wrex vy cab wcel vw cv vz cv
      wcel wi vz wal vw cv cB wcel vx cA df-ral cB cC wcel vx cA wral vx cv cA
      wcel vw cv cB wcel wi vx wal vx cv cA wcel vz cv cB wceq vw cv vz cv wcel
      wi vz wal wi vx wal vz cv vy cv cB wceq vx cA wrex vy cab wcel vw cv vz
      cv wcel wi vz wal cB cC wcel vx cA wral vx cv cA wcel cB cC wcel wi vx
      wal vx cv cA wcel vw cv cB wcel wi vx wal vx cv cA wcel vz cv cB wceq vw
      cv vz cv wcel wi vz wal wi vx wal wb cB cC wcel vx cA df-ral vx cv cA
      wcel cB cC wcel wi vx wal vx cv cA wcel vw cv cB wcel wi vx cv cA wcel vz
      cv cB wceq vw cv vz cv wcel wi vz wal wi wb vx wal vx cv cA wcel vw cv cB
      wcel wi vx wal vx cv cA wcel vz cv cB wceq vw cv vz cv wcel wi vz wal wi
      vx wal wb vx cv cA wcel cB cC wcel wi vx cv cA wcel vw cv cB wcel wi vx
      cv cA wcel vz cv cB wceq vw cv vz cv wcel wi vz wal wi wb vx vx cv cA
      wcel cB cC wcel wi vx cv cA wcel vw cv cB wcel vz cv cB wceq vw cv vz cv
      wcel wi vz wal cB cC wcel vw cv cB wcel vz cv cB wceq vw cv vz cv wcel wi
      vz wal wb vx cv cA wcel cB cC wcel vw cv cB wcel vz cv cB wceq vw cv vz
      cv wcel wi vz wal vw cv cB wcel vz cv cB wceq vw cv vz cv wcel wi vz vz
      cv cB wceq vw cv vz cv wcel vw cv cB wcel vz cv cB vw cv eleq2 biimprcd
      alrimiv cB cC wcel vz cv cB wceq vw cv vz cv wcel wi vz wal cB cB wceq vw
      cv cB wcel cB eqid vz cv cB wceq vw cv vz cv wcel wi cB cB wceq vw cv cB
      wcel wi vz cB cC vz cv cB wceq vz cv cB wceq cB cB wceq vw cv vz cv wcel
      vw cv cB wcel vz cv cB cB eqeq1 vz cv cB vw cv eleq2 imbi12d spcgv mpii
      impbid2 imim2i pm5.74d alimi vx cv cA wcel vw cv cB wcel wi vx cv cA wcel
      vz cv cB wceq vw cv vz cv wcel wi vz wal wi vx albi syl sylbi vz cv cB
      wceq vw cv vz cv wcel wi vx cA wral vz wal vx cv cA wcel vz cv cB wceq vw
      cv vz cv wcel wi wi vz wal vx wal vz cv vy cv cB wceq vx cA wrex vy cab
      wcel vw cv vz cv wcel wi vz wal vx cv cA wcel vz cv cB wceq vw cv vz cv
      wcel wi vz wal wi vx wal vz cv cB wceq vw cv vz cv wcel wi vx cA wral vz
      wal vx cv cA wcel vz cv cB wceq vw cv vz cv wcel wi wi vx wal vz wal vx
      cv cA wcel vz cv cB wceq vw cv vz cv wcel wi wi vz wal vx wal vz cv cB
      wceq vw cv vz cv wcel wi vx cA wral vx cv cA wcel vz cv cB wceq vw cv vz
      cv wcel wi wi vx wal vz vz cv cB wceq vw cv vz cv wcel wi vx cA df-ral
      albii vx cv cA wcel vz cv cB wceq vw cv vz cv wcel wi wi vx vz alcom
      bitr4i vz cv cB wceq vw cv vz cv wcel wi vx cA wral vz cv vy cv cB wceq
      vx cA wrex vy cab wcel vw cv vz cv wcel wi vz vz cv cB wceq vw cv vz cv
      wcel wi vx cA wral vz cv cB wceq vx cA wrex vw cv vz cv wcel wi vz cv vy
      cv cB wceq vx cA wrex vy cab wcel vw cv vz cv wcel wi vz cv cB wceq vw cv
      vz cv wcel vx cA r19.23v vz cv vy cv cB wceq vx cA wrex vy cab wcel vz cv
      cB wceq vx cA wrex vw cv vz cv wcel vy cv cB wceq vx cA wrex vz cv cB
      wceq vx cA wrex vy vz cv vz vex vy cv vz cv wceq vy cv cB wceq vz cv cB
      wceq vx cA vy cv vz cv cB eqeq1 rexbidv elab imbi1i bitr4i albii vx cv cA
      wcel vz cv cB wceq vw cv vz cv wcel wi wi vz wal vx cv cA wcel vz cv cB
      wceq vw cv vz cv wcel wi vz wal wi vx vx cv cA wcel vz cv cB wceq vw cv
      vz cv wcel wi vz 19.21v albii 3bitr3ri syl6bb syl5bb abbidv vx vw cA cB
      df-iin vw vz vy cv cB wceq vx cA wrex vy cab df-int 3eqtr4g $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    dfiun2.1 $e |- B e. _V $.
    $( Alternate definition of indexed union when ` B ` is a set.  Definition
       15(a) of [Suppes] p. 44.  (Contributed by NM, 27-Jun-1998.)  (Revised by
       David Abernethy, 19-Jun-2012.) $)
    dfiun2 $p |- U_ x e. A B = U. { y | E. x e. A y = B } $=
      cB cvv wcel vx cA cB ciun vy cv cB wceq vx cA wrex vy cab cuni wceq vx cA
      vx vy cA cB cvv dfiun2g cB cvv wcel vx cv cA wcel dfiun2.1 a1i mprg $.

    $( Alternate definition of indexed intersection when ` B ` is a set.
       Definition 15(b) of [Suppes] p. 44.  (Contributed by NM, 28-Jun-1998.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    dfiin2 $p |- |^|_ x e. A B = |^| { y | E. x e. A y = B } $=
      cB cvv wcel vx cA cB ciin vy cv cB wceq vx cA wrex vy cab cint wceq vx cA
      vx vy cA cB cvv dfiin2g cB cvv wcel vx cv cA wcel dfiun2.1 a1i mprg $.
  $}

  ${
    $d z y A $.  $d z x A $.  $d z B $.  $d z C $.
    cbviun.1 $e |- F/_ y B $.
    cbviun.2 $e |- F/_ x C $.
    cbviun.3 $e |- ( x = y -> B = C ) $.
    $( Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 26-Mar-2006.)  (Revised by Andrew Salmon, 25-Jul-2011.) $)
    cbviun $p |- U_ x e. A B = U_ y e. A C $=
      vz cv cB wcel vx cA wrex vz cab vz cv cC wcel vy cA wrex vz cab vx cA cB
      ciun vy cA cC ciun vz cv cB wcel vx cA wrex vz cv cC wcel vy cA wrex vz
      vz cv cB wcel vz cv cC wcel vx vy cA vy vz cB cbviun.1 nfcri vx vz cC
      cbviun.2 nfcri vx cv vy cv wceq cB cC vz cv cbviun.3 eleq2d cbvrex abbii
      vx vz cA cB df-iun vy vz cA cC df-iun 3eqtr4i $.

    $( Change bound variables in an indexed intersection.  (Contributed by Jeff
       Hankins, 26-Aug-2009.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
    cbviin $p |- |^|_ x e. A B = |^|_ y e. A C $=
      vz cv cB wcel vx cA wral vz cab vz cv cC wcel vy cA wral vz cab vx cA cB
      ciin vy cA cC ciin vz cv cB wcel vx cA wral vz cv cC wcel vy cA wral vz
      vz cv cB wcel vz cv cC wcel vx vy cA vy vz cB cbviun.1 nfcri vx vz cC
      cbviun.2 nfcri vx cv vy cv wceq cB cC vz cv cbviun.3 eleq2d cbvral abbii
      vx vz cA cB df-iin vy vz cA cC df-iin 3eqtr4i $.
  $}

  ${
    $d x A $.  $d y A $.  $d y z B $.  $d x z C $.
    cbviunv.1 $e |- ( x = y -> B = C ) $.
    $( Rule used to change the bound variables in an indexed union, with the
       substitution specified implicitly by the hypothesis.  (Contributed by
       NM, 15-Sep-2003.) $)
    cbviunv $p |- U_ x e. A B = U_ y e. A C $=
      vx vy cA cB cC vy cB nfcv vx cC nfcv cbviunv.1 cbviun $.

    $( Change bound variables in an indexed intersection.  (Contributed by Jeff
       Hankins, 26-Aug-2009.) $)
    cbviinv $p |- |^|_ x e. A B = |^|_ y e. A C $=
      vx vy cA cB cC vy cB nfcv vx cC nfcv cbviunv.1 cbviin $.
  $}

  ${
    $d x y C $.  $d y A $.  $d y B $.
    $( Subset theorem for an indexed union.  (Contributed by NM, 13-Sep-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    iunss $p |- ( U_ x e. A B C_ C <-> A. x e. A B C_ C ) $=
      vx cA cB ciun cC wss vy cv cB wcel vx cA wrex vy cab cC wss vy cv cB wcel
      vx cA wrex vy cv cC wcel wi vy wal cB cC wss vx cA wral vx cA cB ciun vy
      cv cB wcel vx cA wrex vy cab cC vx vy cA cB df-iun sseq1i vy cv cB wcel
      vx cA wrex vy cC abss cB cC wss vx cA wral vy cv cB wcel vy cv cC wcel wi
      vy wal vx cA wral vy cv cB wcel vy cv cC wcel wi vx cA wral vy wal vy cv
      cB wcel vx cA wrex vy cv cC wcel wi vy wal cB cC wss vy cv cB wcel vy cv
      cC wcel wi vy wal vx cA vy cB cC dfss2 ralbii vy cv cB wcel vy cv cC wcel
      wi vx vy cA ralcom4 vy cv cB wcel vy cv cC wcel wi vx cA wral vy cv cB
      wcel vx cA wrex vy cv cC wcel wi vy vy cv cB wcel vy cv cC wcel vx cA
      r19.23v albii 3bitrri 3bitri $.
  $}

  ${
    $d x y C $.  $d y A $.  $d y B $.
    $( Subset implication for an indexed union.  (Contributed by NM,
       3-Sep-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    ssiun $p |- ( E. x e. A C C_ B -> C C_ U_ x e. A B ) $=
      cC cB wss vx cA wrex vy cC vx cA cB ciun cC cB wss vx cA wrex vy cv cC
      wcel vy cv cB wcel vx cA wrex vy cv vx cA cB ciun wcel cC cB wss vx cA
      wrex vy cv cC wcel vy cv cB wcel wi vx cA wrex vy cv cC wcel vy cv cB
      wcel vx cA wrex wi cC cB wss vy cv cC wcel vy cv cB wcel wi vx cA cC cB
      vy cv ssel reximi vy cv cC wcel vy cv cB wcel vx cA r19.37av syl vx vy cv
      cA cB eliun syl6ibr ssrdv $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    $( Identity law for subset of an indexed union.  (Contributed by NM,
       12-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    ssiun2 $p |- ( x e. A -> B C_ U_ x e. A B ) $=
      vx cv cA wcel vy cB vx cA cB ciun vx cv cA wcel vy cv cB wcel vy cv cB
      wcel vx cA wrex vy cv vx cA cB ciun wcel vx cv cA wcel vy cv cB wcel vy
      cv cB wcel vx cA wrex vy cv cB wcel vx cA rspe ex vx vy cv cA cB eliun
      syl6ibr ssrdv $.
  $}

  ${
    $d x A $.  $d x C $.  $d x D $.
    ssiun2s.1 $e |- ( x = C -> B = D ) $.
    $( Subset relationship for an indexed union.  (Contributed by NM,
       26-Oct-2003.) $)
    ssiun2s $p |- ( C e. A -> D C_ U_ x e. A B ) $=
      cB vx cA cB ciun wss cD vx cA cB ciun wss vx cC cA vx cC nfcv vx cD vx cA
      cB ciun vx cD nfcv vx cA cB nfiu1 nfss vx cv cC wceq cB cD vx cA cB ciun
      ssiun2s.1 sseq1d vx cA cB ssiun2 vtoclgaf $.
  $}

  ${
    $d x y $.  $d x B $.  $d y C $.  $d x D $.
    $( A subclass condition on the members of two indexed classes ` C ( x ) `
       and ` D ( y ) ` that implies a subclass relation on their indexed
       unions.  Generalization of Proposition 8.6 of [TakeutiZaring] p. 59.
       Compare ~ uniss2 .  (Contributed by NM, 9-Dec-2004.) $)
    iunss2 $p |- ( A. x e. A E. y e. B C C_ D ->
                 U_ x e. A C C_ U_ y e. B D ) $=
      cC cD wss vy cB wrex vx cA wral cC vy cB cD ciun wss vx cA wral vx cA cC
      ciun vy cB cD ciun wss cC cD wss vy cB wrex cC vy cB cD ciun wss vx cA vy
      cB cD cC ssiun ralimi vx cA cC vy cB cD ciun iunss sylibr $.
  $}

  ${
    $d y A $.  $d x y $.  $d x B $.
    $( The indexed union of a class abstraction.  (Contributed by NM,
       27-Dec-2004.) $)
    iunab $p |- U_ x e. A { y | ph } = { y | E. x e. A ph } $=
      vx cA wph vy cab ciun wph vx cA wrex vy cab wceq vy cv vx cA wph vy cab
      ciun wcel vy cv wph vx cA wrex vy cab wcel wb vy vy vx cA wph vy cab ciun
      wph vx cA wrex vy cab vx vy cA wph vy cab vy cA nfcv wph vy nfab1 nfiun
      wph vx cA wrex vy nfab1 cleqf vy cv wph vy cab wcel vx cA wrex wph vx cA
      wrex vy cv vx cA wph vy cab ciun wcel vy cv wph vx cA wrex vy cab wcel vy
      cv wph vy cab wcel wph vx cA wph vy abid rexbii vx vy cv cA wph vy cab
      eliun wph vx cA wrex vy abid 3bitr4i mpgbir $.

    $( The indexed union of a restricted class abstraction.  (Contributed by
       NM, 3-Jan-2004.)  (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)
    iunrab $p |- U_ x e. A { y e. B | ph } = { y e. B | E. x e. A ph } $=
      vx cA vy cv cB wcel wph wa vy cab ciun vy cv cB wcel wph wa vx cA wrex vy
      cab vx cA wph vy cB crab ciun wph vx cA wrex vy cB crab vy cv cB wcel wph
      wa vx vy cA iunab vx cA wph vy cB crab vy cv cB wcel wph wa vy cab wph vy
      cB crab vy cv cB wcel wph wa vy cab wceq vx cv cA wcel wph vy cB df-rab
      a1i iuneq2i wph vx cA wrex vy cB crab vy cv cB wcel wph vx cA wrex wa vy
      cab vy cv cB wcel wph wa vx cA wrex vy cab wph vx cA wrex vy cB df-rab vy
      cv cB wcel wph wa vx cA wrex vy cv cB wcel wph vx cA wrex wa vy vy cv cB
      wcel wph vx cA r19.42v abbii eqtr4i 3eqtr4i $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x D $.
    iunxdif2.1 $e |- ( x = y -> C = D ) $.
    $( Indexed union with a class difference as its index.  (Contributed by NM,
       10-Dec-2004.) $)
    iunxdif2 $p |- ( A. x e. A E. y e. ( A \ B ) C C_ D ->
                 U_ y e. ( A \ B ) D = U_ x e. A C ) $=
      cC cD wss vy cA cB cdif wrex vx cA wral vy cA cB cdif cD ciun vx cA cC
      ciun wss vx cA cC ciun vy cA cB cdif cD ciun wss wa vy cA cB cdif cD ciun
      vx cA cC ciun wceq cC cD wss vy cA cB cdif wrex vx cA wral vx cA cC ciun
      vy cA cB cdif cD ciun wss vy cA cB cdif cD ciun vx cA cC ciun wss vx vy
      cA cA cB cdif cC cD iunss2 vy cA cB cdif cD ciun vy cA cD ciun vx cA cC
      ciun cA cB cdif cA wss vy cA cB cdif cD ciun vy cA cD ciun wss cA cB
      difss vy cA cB cdif cA cD iunss1 ax-mp vx vy cA cC cD iunxdif2.1 cbviunv
      sseqtr4i jctil vy cA cB cdif cD ciun vx cA cC ciun eqss sylibr $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z C $.  $d x y z $.
    ssiinf.1 $e |- F/_ x C $.
    $( Subset theorem for an indexed intersection.  (Contributed by FL,
       15-Oct-2012.)  (Proof shortened by Mario Carneiro, 14-Oct-2016.) $)
    ssiinf $p |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B ) $=
      vy cv vx cA cB ciin wcel vy cC wral vy cv cB wcel vy cC wral vx cA wral
      cC vx cA cB ciin wss cC cB wss vx cA wral vy cv vx cA cB ciin wcel vy cC
      wral vy cv cB wcel vx cA wral vy cC wral vy cv cB wcel vy cC wral vx cA
      wral vy cv vx cA cB ciin wcel vy cv cB wcel vx cA wral vy cC vy cv cvv
      wcel vy cv vx cA cB ciin wcel vy cv cB wcel vx cA wral wb vy vex vx vy cv
      cA cB cvv eliin ax-mp ralbii vy cv cB wcel vy vx cC cA ssiinf.1 vy cA
      nfcv ralcomf bitri vy cC vx cA cB ciin dfss3 cC cB wss vy cv cB wcel vy
      cC wral vx cA vy cC cB dfss3 ralbii 3bitr4i $.
  $}

  ${
    $d x C $.
    $( Subset theorem for an indexed intersection.  (Contributed by NM,
       15-Oct-2003.) $)
    ssiin $p |- ( C C_ |^|_ x e. A B <-> A. x e. A C C_ B ) $=
      vx cA cB cC vx cC nfcv ssiinf $.
  $}

  ${
    $d x y C $.  $d y A $.  $d y B $.
    $( Subset implication for an indexed intersection.  (Contributed by NM,
       15-Oct-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    iinss $p |- ( E. x e. A B C_ C -> |^|_ x e. A B C_ C ) $=
      cB cC wss vx cA wrex vy vx cA cB ciin cC vy cv vx cA cB ciin wcel vy cv
      cB wcel vx cA wral cB cC wss vx cA wrex vy cv cC wcel vy cv cvv wcel vy
      cv vx cA cB ciin wcel vy cv cB wcel vx cA wral wb vy vex vx vy cv cA cB
      cvv eliin ax-mp cB cC wss vx cA wrex vy cv cB wcel vy cv cC wcel wi vx cA
      wrex vy cv cB wcel vx cA wral vy cv cC wcel wi cB cC wss vy cv cB wcel vy
      cv cC wcel wi vx cA cB cC vy cv ssel reximi vy cv cB wcel vy cv cC wcel
      vx cA r19.36av syl syl5bi ssrdv $.
  $}

  ${
    $d A y $.  $d B y $.  $d x y $.
    $( An indexed intersection is included in any of its members.  (Contributed
       by FL, 15-Oct-2012.) $)
    iinss2 $p |- ( x e. A -> |^|_ x e. A B C_ B ) $=
      vx cv cA wcel vy vx cA cB ciin cB vy cv vx cA cB ciin wcel vx cv cA wcel
      vy cv cB wcel vy cv vx cA cB ciin wcel vy cv cB wcel vx cA wral vx cv cA
      wcel vy cv cB wcel wi vy cv cvv wcel vy cv vx cA cB ciin wcel vy cv cB
      wcel vx cA wral wb vy vex vx vy cv cA cB cvv eliin ax-mp vy cv cB wcel vx
      cA rsp sylbi com12 ssrdv $.
  $}

  ${
    $d x y A $.
    $( Class union in terms of indexed union.  Definition in [Stoll] p. 43.
       (Contributed by NM, 28-Jun-1998.) $)
    uniiun $p |- U. A = U_ x e. A x $=
      cA cuni vy cv vx cv wcel vx cA wrex vy cab vx cA vx cv ciun vy vx cA
      dfuni2 vx vy cA vx cv df-iun eqtr4i $.

    $( Class intersection in terms of indexed intersection.  Definition in
       [Stoll] p. 44.  (Contributed by NM, 28-Jun-1998.) $)
    intiin $p |- |^| A = |^|_ x e. A x $=
      cA cint vy cv vx cv wcel vx cA wral vy cab vx cA vx cv ciin vy vx cA
      dfint2 vx vy cA vx cv df-iin eqtr4i $.

    $( An indexed union of singletons recovers the index set.  (Contributed by
       NM, 6-Sep-2005.) $)
    iunid $p |- U_ x e. A { x } = A $=
      vx cA vx cv csn ciun vx cA vx cv vy cv wceq vy cab ciun cA vx cA vx cv
      csn vx cv vy cv wceq vy cab vx cv csn vx cv vy cv wceq vy cab wceq vx cv
      cA wcel vx cv csn vy cv vx cv wceq vy cab vx cv vy cv wceq vy cab vy vx
      cv df-sn vy cv vx cv wceq vx cv vy cv wceq vy vy vx equcom abbii eqtri
      a1i iuneq2i vx cA vx cv vy cv wceq vy cab ciun vx cv vy cv wceq vx cA
      wrex vy cab vy cv cA wcel vy cab cA vx cv vy cv wceq vx vy cA iunab vy cv
      cA wcel vx cv vy cv wceq vx cA wrex vy vx vy cv cA risset abbii vy cA
      abid2 3eqtr2i eqtri $.
  $}

  ${
    $d x y $.  $d y A $.
    $( An indexed union of the empty set is empty.  (Contributed by NM,
       26-Mar-2003.)  (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    iun0 $p |- U_ x e. A (/) = (/) $=
      vy vx cA c0 ciun c0 vy cv vx cA c0 ciun wcel vy cv c0 wcel vy cv vx cA c0
      ciun wcel vy cv c0 wcel vx cA wrex vy cv c0 wcel vx cA vy cv c0 wcel wn
      vx cv cA wcel vy cv noel a1i nrex vx vy cv cA c0 eliun mtbir vy cv noel
      2false eqriv $.

    $( An empty indexed union is empty.  (Contributed by NM, 4-Dec-2004.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    0iun $p |- U_ x e. (/) A = (/) $=
      vy vx c0 cA ciun c0 vy cv vx c0 cA ciun wcel vy cv c0 wcel vy cv vx c0 cA
      ciun wcel vy cv cA wcel vx c0 wrex vy cv cA wcel vx rex0 vx vy cv c0 cA
      eliun mtbir vy cv noel 2false eqriv $.

    $( An empty indexed intersection is the universal class.  (Contributed by
       NM, 20-Oct-2005.) $)
    0iin $p |- |^|_ x e. (/) A = _V $=
      vx c0 cA ciin vy cv cA wcel vx c0 wral vy cab cvv vx vy c0 cA df-iin vy
      cv cA wcel vx c0 wral vy cvv vy cv cvv wcel vy cv cA wcel vx c0 wral vy
      vex vy cv cA wcel vx ral0 2th abbi2i eqtr4i $.

    $( Indexed intersection with a universal index class.  When ` A ` doesn't
       depend on ` x ` , this evaluates to ` A ` by ~ 19.3 and ~ abid2 .  When
       ` A = x ` , this evaluates to ` (/) ` by ~ intiin and ~ intv .
       (Contributed by NM, 11-Sep-2008.) $)
    viin $p |- |^|_ x e. _V A = { y | A. x y e. A } $=
      vx cvv cA ciin vy cv cA wcel vx cvv wral vy cab vy cv cA wcel vx wal vy
      cab vx vy cvv cA df-iin vy cv cA wcel vx cvv wral vy cv cA wcel vx wal vy
      vy cv cA wcel vx ralv abbii eqtri $.
  $}

  ${
    $d x y A $.  $d y B $.
    $( There is a non-empty class in an indexed collection ` B ( x ) ` iff the
       indexed union of them is non-empty.  (Contributed by NM, 15-Oct-2003.)
       (Proof shortened by Andrew Salmon, 25-Jul-2011.) $)
    iunn0 $p |- ( E. x e. A B =/= (/) <-> U_ x e. A B =/= (/) ) $=
      vy cv cB wcel vy wex vx cA wrex vy cv vx cA cB ciun wcel vy wex cB c0 wne
      vx cA wrex vx cA cB ciun c0 wne vy cv cB wcel vy wex vx cA wrex vy cv cB
      wcel vx cA wrex vy wex vy cv vx cA cB ciun wcel vy wex vy cv cB wcel vx
      vy cA rexcom4 vy cv vx cA cB ciun wcel vy cv cB wcel vx cA wrex vy vx vy
      cv cA cB eliun exbii bitr4i cB c0 wne vy cv cB wcel vy wex vx cA vy cB n0
      rexbii vy vx cA cB ciun n0 3bitr4i $.
  $}

  ${
    $d y A $.  $d x y $.
    $( Indexed intersection of a class builder.  (Contributed by NM,
       6-Dec-2011.) $)
    iinab $p |- |^|_ x e. A { y | ph } = { y | A. x e. A ph } $=
      vx cA wph vy cab ciin wph vx cA wral vy cab wceq vy cv vx cA wph vy cab
      ciin wcel vy cv wph vx cA wral vy cab wcel wb vy vy vx cA wph vy cab ciin
      wph vx cA wral vy cab vx vy cA wph vy cab vy cA nfcv wph vy nfab1 nfiin
      wph vx cA wral vy nfab1 cleqf vy cv wph vy cab wcel vx cA wral wph vx cA
      wral vy cv vx cA wph vy cab ciin wcel vy cv wph vx cA wral vy cab wcel vy
      cv wph vy cab wcel wph vx cA wph vy abid ralbii vy cv cvv wcel vy cv vx
      cA wph vy cab ciin wcel vy cv wph vy cab wcel vx cA wral wb vy vex vx vy
      cv cA wph vy cab cvv eliin ax-mp wph vx cA wral vy abid 3bitr4i mpgbir $.

    $d x A $.  $d x B $.
    $( Indexed intersection of a restricted class builder.  (Contributed by NM,
       6-Dec-2011.) $)
    iinrab $p |- ( A =/= (/)
          -> |^|_ x e. A { y e. B | ph } = { y e. B | A. x e. A ph } ) $=
      cA c0 wne vy cv cB wcel wph wa vx cA wral vy cab vy cv cB wcel wph vx cA
      wral wa vy cab vx cA wph vy cB crab ciin wph vx cA wral vy cB crab cA c0
      wne vy cv cB wcel wph wa vx cA wral vy cv cB wcel wph vx cA wral wa vy vy
      cv cB wcel wph vx cA r19.28zv abbidv vx cA wph vy cB crab ciin vx cA vy
      cv cB wcel wph wa vy cab ciin vy cv cB wcel wph wa vx cA wral vy cab vx
      cA wph vy cB crab vy cv cB wcel wph wa vy cab wph vy cB crab vy cv cB
      wcel wph wa vy cab wceq vx cv cA wcel wph vy cB df-rab a1i iineq2i vy cv
      cB wcel wph wa vx vy cA iinab eqtri wph vx cA wral vy cB df-rab 3eqtr4g
      $.

    $d y B $.
    $( Indexed intersection of a restricted class builder.  (Contributed by NM,
       6-Dec-2011.) $)
    iinrab2 $p |- ( |^|_ x e. A { y e. B | ph } i^i B )
                      = { y e. B | A. x e. A ph } $=
      vx cA wph vy cB crab ciin cB cin wph vx cA wral vy cB crab wceq cA c0 cA
      c0 wceq vx cA wph vy cB crab ciin cB cin cB wph vx cA wral vy cB crab cA
      c0 wceq vx cA wph vy cB crab ciin cB cin cvv cB cin cB cA c0 wceq vx cA
      wph vy cB crab ciin cvv cB cA c0 wceq vx cA wph vy cB crab ciin vx c0 wph
      vy cB crab ciin cvv vx cA c0 wph vy cB crab iineq1 vx wph vy cB crab 0iin
      syl6eq ineq1d cvv cB cin cB cvv cin cB cvv cB incom cB inv1 eqtri syl6eq
      cA c0 wceq wph vy cB wral vx cA wral cB wph vx cA wral vy cB crab wceq
      wph vy cB wral vx cA rzal cB wph vx cA wral vy cB crab wceq wph vx cA
      wral vy cB wral wph vy cB wral vx cA wral wph vx cA wral vy cB rabid2 wph
      vy vx cB cA ralcom bitr2i sylib eqtrd cA c0 wne vx cA wph vy cB crab ciin
      cB cin wph vx cA wral vy cB crab cB cin wph vx cA wral vy cB crab cA c0
      wne vx cA wph vy cB crab ciin wph vx cA wral vy cB crab cB wph vx vy cA
      cB iinrab ineq1d wph vx cA wral vy cB crab cB wss wph vx cA wral vy cB
      crab wph vx cA wral vy cB crab cB cin wceq wph vx cA wral vy cB ssrab2
      wph vx cA wral vy cB crab cB dfss mpbi syl6eqr pm2.61ine $.
  $}

  ${
    $d y A $.  $d x y B $.  $d y C $.
    $( Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 26-Mar-2004.) $)
    iunin2 $p |- U_ x e. A ( B i^i C ) = ( B i^i U_ x e. A C ) $=
      vy vx cA cB cC cin ciun cB vx cA cC ciun cin vy cv cB cC cin wcel vx cA
      wrex vy cv cB wcel vy cv vx cA cC ciun wcel wa vy cv vx cA cB cC cin ciun
      wcel vy cv cB vx cA cC ciun cin wcel vy cv cB wcel vy cv cC wcel wa vx cA
      wrex vy cv cB wcel vy cv cC wcel vx cA wrex wa vy cv cB cC cin wcel vx cA
      wrex vy cv cB wcel vy cv vx cA cC ciun wcel wa vy cv cB wcel vy cv cC
      wcel vx cA r19.42v vy cv cB cC cin wcel vy cv cB wcel vy cv cC wcel wa vx
      cA vy cv cB cC elin rexbii vy cv vx cA cC ciun wcel vy cv cC wcel vx cA
      wrex vy cv cB wcel vx vy cv cA cC eliun anbi2i 3bitr4i vx vy cv cA cB cC
      cin eliun vy cv cB vx cA cC ciun elin 3bitr4i eqriv $.

    $( Indexed union of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 30-Aug-2015.) $)
    iunin1 $p |- U_ x e. A ( C i^i B ) = ( U_ x e. A C i^i B ) $=
      vx cA cB cC cin ciun cB vx cA cC ciun cin vx cA cC cB cin ciun vx cA cC
      ciun cB cin vx cA cB cC iunin2 vx cA cC cB cin cB cC cin cC cB cin cB cC
      cin wceq vx cv cA wcel cC cB incom a1i iuneq2i vx cA cC ciun cB incom
      3eqtr4i $.

    $( Indexed intersection of union.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by NM, 19-Aug-2004.) $)
    iinun2 $p |- |^|_ x e. A ( B u. C ) = ( B u. |^|_ x e. A C ) $=
      vy vx cA cB cC cun ciin cB vx cA cC ciin cun vy cv cB cC cun wcel vx cA
      wral vy cv cB wcel vy cv vx cA cC ciin wcel wo vy cv vx cA cB cC cun ciin
      wcel vy cv cB vx cA cC ciin cun wcel vy cv cB wcel vy cv cC wcel wo vx cA
      wral vy cv cB wcel vy cv cC wcel vx cA wral wo vy cv cB cC cun wcel vx cA
      wral vy cv cB wcel vy cv vx cA cC ciin wcel wo vy cv cB wcel vy cv cC
      wcel vx cA r19.32v vy cv cB cC cun wcel vy cv cB wcel vy cv cC wcel wo vx
      cA vy cv cB cC elun ralbii vy cv vx cA cC ciin wcel vy cv cC wcel vx cA
      wral vy cv cB wcel vy cv cvv wcel vy cv vx cA cC ciin wcel vy cv cC wcel
      vx cA wral wb vy vex vx vy cv cA cC cvv eliin ax-mp orbi2i 3bitr4i vy cv
      cvv wcel vy cv vx cA cB cC cun ciin wcel vy cv cB cC cun wcel vx cA wral
      wb vy vex vx vy cv cA cB cC cun cvv eliin ax-mp vy cv cB vx cA cC ciin
      elun 3bitr4i eqriv $.

    $( Indexed union of class difference.  Generalization of half of theorem
       "De Morgan's laws" in [Enderton] p. 31.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by NM, 19-Aug-2004.) $)
    iundif2 $p |- U_ x e. A ( B \ C ) = ( B \ |^|_ x e. A C ) $=
      vy vx cA cB cC cdif ciun cB vx cA cC ciin cdif vy cv cB cC cdif wcel vx
      cA wrex vy cv cB wcel vy cv vx cA cC ciin wcel wn wa vy cv vx cA cB cC
      cdif ciun wcel vy cv cB vx cA cC ciin cdif wcel vy cv cB cC cdif wcel vx
      cA wrex vy cv cB wcel vy cv cC wcel wn wa vx cA wrex vy cv cB wcel vy cv
      cC wcel wn vx cA wrex wa vy cv cB wcel vy cv vx cA cC ciin wcel wn wa vy
      cv cB cC cdif wcel vy cv cB wcel vy cv cC wcel wn wa vx cA vy cv cB cC
      eldif rexbii vy cv cB wcel vy cv cC wcel wn vx cA r19.42v vy cv cC wcel
      wn vx cA wrex vy cv vx cA cC ciin wcel wn vy cv cB wcel vy cv cC wcel wn
      vx cA wrex vy cv cC wcel vx cA wral vy cv vx cA cC ciin wcel vy cv cC
      wcel vx cA rexnal vy cv cvv wcel vy cv vx cA cC ciin wcel vy cv cC wcel
      vx cA wral wb vy vex vx vy cv cA cC cvv eliin ax-mp xchbinxr anbi2i
      3bitri vx vy cv cA cB cC cdif eliun vy cv cB vx cA cC ciin eldif 3bitr4i
      eqriv $.
  $}

  ${
    $d x B $.  $d y C $.  $d x D $.  $d x y $.
    $( Rearrange indexed unions over intersection.  (Contributed by NM,
       18-Dec-2008.) $)
    2iunin $p |- U_ x e. A U_ y e. B ( C i^i D )
        = ( U_ x e. A C i^i U_ y e. B D ) $=
      vx cA vy cB cC cD cin ciun ciun vx cA cC vy cB cD ciun cin ciun vx cA cC
      ciun vy cB cD ciun cin vx cA vy cB cC cD cin ciun cC vy cB cD ciun cin vy
      cB cC cD cin ciun cC vy cB cD ciun cin wceq vx cv cA wcel vy cB cC cD
      iunin2 a1i iuneq2i vx cA vy cB cD ciun cC iunin1 eqtri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.
    $( Indexed intersection of class difference.  Generalization of half of
       theorem "De Morgan's laws" in [Enderton] p. 31.  Use ~ uniiun to recover
       Enderton's theorem.  (Contributed by NM, 5-Oct-2006.) $)
    iindif2 $p |- ( A =/= (/) ->
                 |^|_ x e. A ( B \ C ) = ( B \ U_ x e. A C ) ) $=
      cA c0 wne vy vx cA cB cC cdif ciin cB vx cA cC ciun cdif cA c0 wne vy cv
      cB cC cdif wcel vx cA wral vy cv cB wcel vy cv vx cA cC ciun wcel wn wa
      vy cv vx cA cB cC cdif ciin wcel vy cv cB vx cA cC ciun cdif wcel cA c0
      wne vy cv cB wcel vy cv cC wcel wn wa vx cA wral vy cv cB wcel vy cv cC
      wcel wn vx cA wral wa vy cv cB cC cdif wcel vx cA wral vy cv cB wcel vy
      cv vx cA cC ciun wcel wn wa vy cv cB wcel vy cv cC wcel wn vx cA r19.28zv
      vy cv cB wcel vy cv cC wcel wn wa vy cv cB cC cdif wcel vx cA vy cv cB cC
      cdif wcel vy cv cB wcel vy cv cC wcel wn wa vy cv cB cC eldif bicomi
      ralbii vy cv cC wcel wn vx cA wral vy cv vx cA cC ciun wcel wn vy cv cB
      wcel vy cv cC wcel wn vx cA wral vy cv cC wcel vx cA wrex vy cv vx cA cC
      ciun wcel vy cv cC wcel vx cA ralnex vx vy cv cA cC eliun xchbinxr anbi2i
      3bitr3g vy cv cvv wcel vy cv vx cA cB cC cdif ciin wcel vy cv cB cC cdif
      wcel vx cA wral wb vy vex vx vy cv cA cB cC cdif cvv eliin ax-mp vy cv cB
      vx cA cC ciun eldif 3bitr4g eqrdv $.

    $( Indexed intersection of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 19-Mar-2015.) $)
    iinin2 $p |- ( A =/= (/) ->
      |^|_ x e. A ( B i^i C ) = ( B i^i |^|_ x e. A C ) ) $=
      cA c0 wne vy vx cA cB cC cin ciin cB vx cA cC ciin cin cA c0 wne vy cv cB
      cC cin wcel vx cA wral vy cv cB wcel vy cv vx cA cC ciin wcel wa vy cv vx
      cA cB cC cin ciin wcel vy cv cB vx cA cC ciin cin wcel cA c0 wne vy cv cB
      wcel vy cv cC wcel wa vx cA wral vy cv cB wcel vy cv cC wcel vx cA wral
      wa vy cv cB cC cin wcel vx cA wral vy cv cB wcel vy cv vx cA cC ciin wcel
      wa vy cv cB wcel vy cv cC wcel vx cA r19.28zv vy cv cB cC cin wcel vy cv
      cB wcel vy cv cC wcel wa vx cA vy cv cB cC elin ralbii vy cv vx cA cC
      ciin wcel vy cv cC wcel vx cA wral vy cv cB wcel vy cv cvv wcel vy cv vx
      cA cC ciin wcel vy cv cC wcel vx cA wral wb vy vex vx vy cv cA cC cvv
      eliin ax-mp anbi2i 3bitr4g vy cv cvv wcel vy cv vx cA cB cC cin ciin wcel
      vy cv cB cC cin wcel vx cA wral wb vy vex vx vy cv cA cB cC cin cvv eliin
      ax-mp vy cv cB vx cA cC ciin elin 3bitr4g eqrdv $.

    $( Indexed intersection of intersection.  Generalization of half of theorem
       "Distributive laws" in [Enderton] p. 30.  Use ~ intiin to recover
       Enderton's theorem.  (Contributed by Mario Carneiro, 19-Mar-2015.) $)
    iinin1 $p |- ( A =/= (/) ->
      |^|_ x e. A ( C i^i B ) = ( |^|_ x e. A C i^i B ) ) $=
      cA c0 wne vx cA cB cC cin ciin cB vx cA cC ciin cin vx cA cC cB cin ciin
      vx cA cC ciin cB cin vx cA cB cC iinin2 vx cA cC cB cin cB cC cin cC cB
      cin cB cC cin wceq vx cv cA wcel cC cB incom a1i iineq2i vx cA cC ciin cB
      incom 3eqtr4g $.
  $}

  ${
    $d A x y $.  $d X x y $.  $d B x $.
    $( Elementhood in a relative intersection.  (Contributed by Mario Carneiro,
       30-Dec-2016.) $)
    elriin $p |- ( B e. ( A i^i |^|_ x e. X S ) <->
      ( B e. A /\ A. x e. X B e. S ) ) $=
      cB cA vx cX cS ciin cin wcel cB cA wcel cB vx cX cS ciin wcel wa cB cA
      wcel cB cS wcel vx cX wral wa cB cA vx cX cS ciin elin cB cA wcel cB vx
      cX cS ciin wcel cB cS wcel vx cX wral vx cB cX cS cA eliin pm5.32i bitri
      $.

    $( Relative intersection of an empty family.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
    riin0 $p |- ( X = (/) -> ( A i^i |^|_ x e. X S ) = A ) $=
      cX c0 wceq cA vx cX cS ciin cin cA vx c0 cS ciin cin cA cX c0 wceq vx cX
      cS ciin vx c0 cS ciin cA vx cX c0 cS iineq1 ineq2d cA vx c0 cS ciin cin
      cA cvv cin cA vx c0 cS ciin cvv cA vx cS 0iin ineq2i cA inv1 eqtri syl6eq
      $.

    $( Relative intersection of a nonempty family.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
    riinn0 $p |- ( ( A. x e. X S C_ A /\ X =/= (/) ) ->
        ( A i^i |^|_ x e. X S ) = |^|_ x e. X S ) $=
      cS cA wss vx cX wral cX c0 wne wa cA vx cX cS ciin cin vx cX cS ciin cA
      cin vx cX cS ciin cA vx cX cS ciin incom cS cA wss vx cX wral cX c0 wne
      wa vx cX cS ciin cA wss vx cX cS ciin cA cin vx cX cS ciin wceq cS cA wss
      vx cX wral cX c0 wne wa cS cA wss vx cX wrex vx cX cS ciin cA wss cX c0
      wne cS cA wss vx cX wral cS cA wss vx cX wrex cS cA wss vx cX r19.2z
      ancoms vx cX cS cA iinss syl vx cX cS ciin cA df-ss sylib syl5eq $.

    $( Relative intersection of a relative abstraction.  (Contributed by Stefan
       O'Rear, 3-Apr-2015.) $)
    riinrab $p |- ( A i^i |^|_ x e. X { y e. A | ph } ) =
        { y e. A | A. x e. X ph } $=
      cA vx cX wph vy cA crab ciin cin wph vx cX wral vy cA crab wceq cX c0 cX
      c0 wceq cA vx cX wph vy cA crab ciin cin cA wph vx cX wral vy cA crab vx
      cA wph vy cA crab cX riin0 cX c0 wceq wph vx cX wral vy cA wral cA wph vx
      cX wral vy cA crab wceq cX c0 wceq wph vx cX wral vy cA wph vx cX rzal
      ralrimivw wph vx cX wral vy cA rabid2 sylibr eqtrd cX c0 wne cA vx cX wph
      vy cA crab ciin cin vx cX wph vy cA crab ciin wph vx cX wral vy cA crab
      wph vy cA crab cA wss vx cX wral cX c0 wne cA vx cX wph vy cA crab ciin
      cin vx cX wph vy cA crab ciin wceq wph vy cA crab cA wss vx cX wph vy cA
      ssrab2 rgenw vx cA wph vy cA crab cX riinn0 mpan wph vx vy cX cA iinrab
      eqtrd pm2.61ine $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d y V $.
    iinxsng.1 $e |- ( x = A -> B = C ) $.
    $( A singleton index picks out an instance of an indexed intersection's
       argument.  (Contributed by NM, 15-Jan-2012.)  (Proof shortened by Mario
       Carneiro, 17-Nov-2016.) $)
    iinxsng $p |- ( A e. V -> |^|_ x e. { A } B = C ) $=
      cA cV wcel vx cA csn cB ciin vy cv cB wcel vx cA csn wral vy cab cC vx vy
      cA csn cB df-iin cA cV wcel vy cv cB wcel vx cA csn wral vy cC vy cv cB
      wcel vy cv cC wcel vx cA cV vx cv cA wceq cB cC vy cv iinxsng.1 eleq2d
      ralsng abbi1dv syl5eq $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y C $.  $d x y D $.  $d x y E $.  $d y V $.
    $d y W $.
    iinxprg.1 $e |- ( x = A -> C = D ) $.
    iinxprg.2 $e |- ( x = B -> C = E ) $.
    $( Indexed intersection with an unordered pair index.  (Contributed by NM,
       25-Jan-2012.) $)
    iinxprg $p |- ( ( A e. V /\ B e. W )
        -> |^|_ x e. { A , B } C = ( D i^i E ) ) $=
      cA cV wcel cB cW wcel wa vy cv cC wcel vx cA cB cpr wral vy cab vy cv cD
      wcel vy cv cE wcel wa vy cab vx cA cB cpr cC ciin cD cE cin cA cV wcel cB
      cW wcel wa vy cv cC wcel vx cA cB cpr wral vy cv cD wcel vy cv cE wcel wa
      vy vy cv cC wcel vy cv cD wcel vy cv cE wcel vx cA cB cV cW vx cv cA wceq
      cC cD vy cv iinxprg.1 eleq2d vx cv cB wceq cC cE vy cv iinxprg.2 eleq2d
      ralprg abbidv vx vy cA cB cpr cC df-iin vy cD cE df-in 3eqtr4g $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.  $d y V $.
    iunxsng.1 $e |- ( x = A -> B = C ) $.
    $( A singleton index picks out an instance of an indexed union's argument.
       (Contributed by Mario Carneiro, 25-Jun-2016.) $)
    iunxsng $p |- ( A e. V -> U_ x e. { A } B = C ) $=
      cA cV wcel vy vx cA csn cB ciun cC vy cv vx cA csn cB ciun wcel vy cv cB
      wcel vx cA csn wrex cA cV wcel vy cv cC wcel vx vy cv cA csn cB eliun vy
      cv cB wcel vy cv cC wcel vx cA cV vx cv cA wceq cB cC vy cv iunxsng.1
      eleq2d rexsng syl5bb eqrdv $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.
    iunxsn.1 $e |- A e. _V $.
    iunxsn.2 $e |- ( x = A -> B = C ) $.
    $( A singleton index picks out an instance of an indexed union's argument.
       (Contributed by NM, 26-Mar-2004.)  (Proof shortened by Mario Carneiro,
       25-Jun-2016.) $)
    iunxsn $p |- U_ x e. { A } B = C $=
      cA cvv wcel vx cA csn cB ciun cC wceq iunxsn.1 vx cA cB cC cvv iunxsn.2
      iunxsng ax-mp $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y C $.
    $( Separate a union in an indexed union.  (Contributed by NM,
       27-Dec-2004.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
    iunun $p |- U_ x e. A ( B u. C ) = ( U_ x e. A B u. U_ x e. A C ) $=
      vy vx cA cB cC cun ciun vx cA cB ciun vx cA cC ciun cun vy cv cB cC cun
      wcel vx cA wrex vy cv vx cA cB ciun wcel vy cv vx cA cC ciun wcel wo vy
      cv vx cA cB cC cun ciun wcel vy cv vx cA cB ciun vx cA cC ciun cun wcel
      vy cv cB wcel vy cv cC wcel wo vx cA wrex vy cv cB wcel vx cA wrex vy cv
      cC wcel vx cA wrex wo vy cv cB cC cun wcel vx cA wrex vy cv vx cA cB ciun
      wcel vy cv vx cA cC ciun wcel wo vy cv cB wcel vy cv cC wcel vx cA r19.43
      vy cv cB cC cun wcel vy cv cB wcel vy cv cC wcel wo vx cA vy cv cB cC
      elun rexbii vy cv vx cA cB ciun wcel vy cv cB wcel vx cA wrex vy cv vx cA
      cC ciun wcel vy cv cC wcel vx cA wrex vx vy cv cA cB eliun vx vy cv cA cC
      eliun orbi12i 3bitr4i vx vy cv cA cB cC cun eliun vy cv vx cA cB ciun vx
      cA cC ciun elun 3bitr4i eqriv $.

    $( Separate a union in the index of an indexed union.  (Contributed by NM,
       26-Mar-2004.)  (Proof shortened by Mario Carneiro, 17-Nov-2016.) $)
    iunxun $p |- U_ x e. ( A u. B ) C = ( U_ x e. A C u. U_ x e. B C ) $=
      vy vx cA cB cun cC ciun vx cA cC ciun vx cB cC ciun cun vy cv cC wcel vx
      cA cB cun wrex vy cv vx cA cC ciun wcel vy cv vx cB cC ciun wcel wo vy cv
      vx cA cB cun cC ciun wcel vy cv vx cA cC ciun vx cB cC ciun cun wcel vy
      cv cC wcel vx cA cB cun wrex vy cv cC wcel vx cA wrex vy cv cC wcel vx cB
      wrex wo vy cv vx cA cC ciun wcel vy cv vx cB cC ciun wcel wo vy cv cC
      wcel vx cA cB rexun vy cv vx cA cC ciun wcel vy cv cC wcel vx cA wrex vy
      cv vx cB cC ciun wcel vy cv cC wcel vx cB wrex vx vy cv cA cC eliun vx vy
      cv cB cC eliun orbi12i bitr4i vx vy cv cA cB cun cC eliun vy cv vx cA cC
      ciun vx cB cC ciun elun 3bitr4i eqriv $.
  $}

  ${
    $d x y z $.  $d x z A $.  $d z B $.  $d y z C $.
    $( Separate an indexed union in the index of an indexed union.
       (Contributed by Mario Carneiro, 5-Dec-2016.) $)
    iunxiun $p |- U_ x e. U_ y e. A B C = U_ y e. A U_ x e. B C $=
      vz vx vy cA cB ciun cC ciun vy cA vx cB cC ciun ciun vz cv cC wcel vx vy
      cA cB ciun wrex vz cv vx cB cC ciun wcel vy cA wrex vz cv vx vy cA cB
      ciun cC ciun wcel vz cv vy cA vx cB cC ciun ciun wcel vx cv vy cA cB ciun
      wcel vz cv cC wcel wa vx wex vx cv cB wcel vz cv cC wcel wa vx wex vy cA
      wrex vz cv cC wcel vx vy cA cB ciun wrex vz cv vx cB cC ciun wcel vy cA
      wrex vx cv vy cA cB ciun wcel vz cv cC wcel wa vx wex vx cv cB wcel vz cv
      cC wcel wa vy cA wrex vx wex vx cv cB wcel vz cv cC wcel wa vx wex vy cA
      wrex vx cv vy cA cB ciun wcel vz cv cC wcel wa vx cv cB wcel vz cv cC
      wcel wa vy cA wrex vx vx cv vy cA cB ciun wcel vz cv cC wcel wa vx cv cB
      wcel vy cA wrex vz cv cC wcel wa vx cv cB wcel vz cv cC wcel wa vy cA
      wrex vx cv vy cA cB ciun wcel vx cv cB wcel vy cA wrex vz cv cC wcel vy
      vx cv cA cB eliun anbi1i vx cv cB wcel vz cv cC wcel vy cA r19.41v bitr4i
      exbii vx cv cB wcel vz cv cC wcel wa vy vx cA rexcom4 bitr4i vz cv cC
      wcel vx vy cA cB ciun df-rex vz cv vx cB cC ciun wcel vx cv cB wcel vz cv
      cC wcel wa vx wex vy cA vz cv vx cB cC ciun wcel vz cv cC wcel vx cB wrex
      vx cv cB wcel vz cv cC wcel wa vx wex vx vz cv cB cC eliun vz cv cC wcel
      vx cB df-rex bitri rexbii 3bitr4i vx vz cv vy cA cB ciun cC eliun vy vz
      cv cA vx cB cC ciun eliun 3bitr4i eqriv $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( A relationship involving union and indexed intersection.  Exercise 23 of
       [Enderton] p. 33.  (Contributed by NM, 25-Nov-2003.)  (Proof shortened
       by Mario Carneiro, 17-Nov-2016.) $)
    iinuni $p |- ( A u. |^| B ) = |^|_ x e. B ( A u. x ) $=
      vy cv cA wcel vy cv cB cint wcel wo vy cab vy cv cA vx cv cun wcel vx cB
      wral vy cab cA cB cint cun vx cB cA vx cv cun ciin vy cv cA wcel vy cv cB
      cint wcel wo vy cv cA vx cv cun wcel vx cB wral vy vy cv cA wcel vy cv vx
      cv wcel wo vx cB wral vy cv cA wcel vy cv vx cv wcel vx cB wral wo vy cv
      cA vx cv cun wcel vx cB wral vy cv cA wcel vy cv cB cint wcel wo vy cv cA
      wcel vy cv vx cv wcel vx cB r19.32v vy cv cA vx cv cun wcel vy cv cA wcel
      vy cv vx cv wcel wo vx cB vy cv cA vx cv elun ralbii vy cv cB cint wcel
      vy cv vx cv wcel vx cB wral vy cv cA wcel vx vy cv cB vy vex elint2
      orbi2i 3bitr4ri abbii vy cA cB cint df-un vx vy cB cA vx cv cun df-iin
      3eqtr4i $.

    $( A relationship involving union and indexed union.  Exercise 25 of
       [Enderton] p. 33.  (Contributed by NM, 25-Nov-2003.)  (Proof shortened
       by Mario Carneiro, 17-Nov-2016.) $)
    iununi $p |- ( ( B = (/) -> A = (/) ) <->
                ( A u. U. B ) = U_ x e. B ( A u. x ) ) $=
      cB c0 wceq cA c0 wceq wi cA cB cuni cun vx cB cA vx cv cun ciun wceq cB
      c0 wceq cA c0 wceq wi cA vx cB vx cv ciun cun vx cB cA ciun vx cB vx cv
      ciun cun cA cB cuni cun vx cB cA vx cv cun ciun cB c0 wceq cA c0 wceq wi
      cA vx cB cA ciun vx cB vx cv ciun cB c0 wceq cA c0 wceq wi vx cB cA ciun
      cA cB c0 wceq cA c0 wceq vx cB cA ciun cA wceq cB c0 wceq wn cB c0 wne vx
      cB cA ciun cA wceq cB c0 df-ne vx cB cA iunconst sylbir cA c0 wceq vx cB
      c0 ciun c0 vx cB cA ciun cA vx cB iun0 cA c0 wceq vx cB cA c0 cA c0 wceq
      id iuneq2d cA c0 wceq id 3eqtr4a ja eqcomd uneq1d cB cuni vx cB vx cv
      ciun cA vx cB uniiun uneq2i vx cB cA vx cv iunun 3eqtr4g cB c0 wceq cA cB
      cuni cun vx cB cA vx cv cun ciun wceq cA c0 wceq cB c0 wceq cA cB cuni
      cun cA vx cB cA vx cv cun ciun c0 cB c0 wceq cA cB cuni cun cA c0 cun cA
      cB c0 wceq cB cuni c0 cA cB c0 wceq cB cuni c0 cuni c0 cB c0 unieq uni0
      syl6eq uneq2d cA un0 syl6eq cB c0 wceq vx cB cA vx cv cun ciun vx c0 cA
      vx cv cun ciun c0 vx cB c0 cA vx cv cun iuneq1 vx cA vx cv cun 0iun
      syl6eq eqeq12d biimpcd impbii $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Subclass relationship for power class and union.  (Contributed by NM,
       18-Jul-2006.) $)
    sspwuni $p |- ( A C_ ~P B <-> U. A C_ B ) $=
      vx cv cB cpw wcel vx cA wral vx cv cB wss vx cA wral cA cB cpw wss cA
      cuni cB wss vx cv cB cpw wcel vx cv cB wss vx cA vx cv cB vx vex elpw
      ralbii vx cA cB cpw dfss3 vx cA cB unissb 3bitr4i $.

    $( Two ways to express a collection of subclasses.  (Contributed by NM,
       19-Jul-2006.) $)
    pwssb $p |- ( A C_ ~P B <-> A. x e. A x C_ B ) $=
      cA cB cpw wss cA cuni cB wss vx cv cB wss vx cA wral cA cB sspwuni vx cA
      cB unissb bitri $.
  $}

  $( Relationship for power class and union.  (Contributed by NM,
     18-Jul-2006.) $)
  elpwuni $p |- ( B e. A -> ( A C_ ~P B <-> U. A = B ) ) $=
    cA cB cpw wss cA cuni cB wss cB cA wcel cA cuni cB wceq cA cB sspwuni cB cA
    wcel cA cuni cB wss cA cuni cB wceq cA cuni cB wss cB cA wcel cA cuni cB
    wceq cA cB unissel expcom cA cuni cB eqimss impbid1 syl5bb $.

  ${
    $d x y A $.
    $( The power class of an intersection in terms of indexed intersection.
       Exercise 24(a) of [Enderton] p. 33.  (Contributed by NM,
       29-Nov-2003.) $)
    iinpw $p |- ~P |^| A = |^|_ x e. A ~P x $=
      vy cA cint cpw vx cA vx cv cpw ciin vy cv cA cint wss vy cv vx cv cpw
      wcel vx cA wral vy cv cA cint cpw wcel vy cv vx cA vx cv cpw ciin wcel vy
      cv cA cint wss vy cv vx cv wss vx cA wral vy cv vx cv cpw wcel vx cA wral
      vx vy cv cA ssint vy cv vx cv cpw wcel vy cv vx cv wss vx cA vy cv vx cv
      vy vex elpw ralbii bitr4i vy cv cA cint vy vex elpw vy cv cvv wcel vy cv
      vx cA vx cv cpw ciin wcel vy cv vx cv cpw wcel vx cA wral wb vy vex vx vy
      cv cA vx cv cpw cvv eliin ax-mp 3bitr4i eqriv $.

    $( Inclusion of an indexed union of a power class in the power class of the
       union of its index.  Part of Exercise 24(b) of [Enderton] p. 33.
       (Contributed by NM, 25-Nov-2003.) $)
    iunpwss $p |- U_ x e. A ~P x C_ ~P U. A $=
      vy vx cA vx cv cpw ciun cA cuni cpw vy cv vx cv wss vx cA wrex vy cv vx
      cA vx cv ciun wss vy cv vx cA vx cv cpw ciun wcel vy cv cA cuni cpw wcel
      vx cA vx cv vy cv ssiun vy cv vx cA vx cv cpw ciun wcel vy cv vx cv cpw
      wcel vx cA wrex vy cv vx cv wss vx cA wrex vx vy cv cA vx cv cpw eliun vy
      cv vx cv cpw wcel vy cv vx cv wss vx cA vy cv vx cv vy vex elpw rexbii
      bitri vy cv cA cuni cpw wcel vy cv cA cuni wss vy cv vx cA vx cv ciun wss
      vy cv cA cuni vy vex elpw cA cuni vx cA vx cv ciun vy cv vx cA uniiun
      sseq2i bitri 3imtr4i ssriv $.
  $}

  $( Relative intersection of a nonempty set.  (Contributed by Stefan O'Rear,
     3-Apr-2015.)  (Revised by Mario Carneiro, 5-Jun-2015.) $)
  rintn0 $p |- ( ( X C_ ~P A /\ X =/= (/) ) -> ( A i^i |^| X ) = |^| X ) $=
    cX cA cpw wss cX c0 wne wa cA cX cint cin cX cint cA cin cX cint cA cX cint
    incom cX cA cpw wss cX c0 wne wa cX cint cA wss cX cint cA cin cX cint wceq
    cX cA cpw wss cX c0 wne wa cX cint cA cpw cuni cA cX cA cpw intssuni2 cA
    cpw cA cpw wss cA cpw cuni cA wss cA cpw ssid cA cpw cA sspwuni mpbi syl6ss
    cX cint cA df-ss sylib syl5eq $.


