
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Russell_s_Paradox.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Proper substitution of classes for sets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c [. $.
  $c ]. $.

  $( Extend wff notation to include the proper substitution of a class for a
     set.  Read this notation as "the proper substitution of class ` A ` for
     set variable ` x ` in wff ` ph ` ." $)
  wsbc $a wff [. A / x ]. ph $.

  $( Define the proper substitution of a class for a set.

     When ` A ` is a proper class, our definition evaluates to false.  This is
     somewhat arbitrary: we could have, instead, chosen the conclusion of
     ~ sbc6 for our definition, which always evaluates to true for proper
     classes.

     Our definition also does not produce the same results as discussed in the
     proof of Theorem 6.6 of [Quine] p. 42 (although Theorem 6.6 itself does
     hold, as shown by ~ dfsbcq below).  For example, if ` A ` is a proper
     class, Quine's substitution of ` A ` for ` y ` in ` 0 e. y ` evaluates to
     ` 0 e. A ` rather than our falsehood.  (This can be seen by substituting
     ` A ` , ` y ` , and ` 0 ` for alpha, beta, and gamma in Subcase 1 of
     Quine's discussion on p. 42.)  Unfortunately, Quine's definition requires
     a recursive syntactical breakdown of ` ph ` , and it does not seem
     possible to express it with a single closed formula.

     If we did not want to commit to any specific proper class behavior, we
     could use this definition _only_ to prove theorem ~ dfsbcq , which holds
     for both our definition and Quine's, and from which we can derive a weaker
     version of ~ df-sbc in the form of ~ sbc8g .  However, the behavior of
     Quine's definition at proper classes is similarly arbitrary, and for
     practical reasons (to avoid having to prove sethood of ` A ` in every use
     of this definition) we allow direct reference to ~ df-sbc and assert that
     ` [. A / x ]. ph ` is always false when ` A ` is a proper class.

     The theorem ~ sbc2or shows the apparently "strongest" statement we can
     make regarding behavior at proper classes if we start from ~ dfsbcq .

     The related definition ~ df-csb defines proper substitution into a class
     variable (as opposed to a wff variable).  (Contributed by NM,
     14-Apr-1995.)  (Revised by NM, 25-Dec-2016.) $)
  df-sbc $a |- ( [. A / x ]. ph <-> A e. { x | ph } ) $.

  $( --- Start of old code before overloading prevention patch. $)
  $(
  @( Extend wff notation to include the proper substitution of a class for a
     set.  This definition "overloads" the previously defined variable
     substitution ~ wsb (where the first argument is a set variable rather
     than a class variable).  We take care to ensure that this new definition
     is a conservative extension.  Read this notation as "the proper
     substitution of class ` A ` for set variable ` x ` in wff ` ph ` ." @)
  wsbcSBC @a wff [ A / x ] ph @.
  $)
  $( --- End of old code before overloading prevention patch. $)

  $( This theorem, which is similar to Theorem 6.7 of [Quine] p. 42 and holds
     under both our definition and Quine's, provides us with a weak definition
     of the proper substitution of a class for a set.  Since our ~ df-sbc does
     not result in the same behavior as Quine's for proper classes, if we
     wished to avoid conflict with Quine's definition we could start with this
     theorem and ~ dfsbcq2 instead of ~ df-sbc .  ( ~ dfsbcq2 is needed because
     unlike Quine we do not overload the ~ df-sb syntax.)  As a consequence of
     these theorems, we can derive ~ sbc8g , which is a weaker version of
     ~ df-sbc that leaves substitution undefined when ` A ` is a proper class.

     However, it is often a nuisance to have to prove the sethood hypothesis of
     ~ sbc8g , so we will allow direct use of ~ df-sbc after theorem ~ sbc2or
     below.  Proper substiution with a proper class is rarely needed, and when
     it is, we can simply use the expansion of Quine's definition.
     (Contributed by NM, 14-Apr-1995.) $)
  dfsbcq $p |- ( A = B -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $=
    cA cB wceq cA wph vx cab wcel cB wph vx cab wcel wph vx cA wsbc wph vx cB
    wsbc cA cB wph vx cab eleq1 wph vx cA df-sbc wph vx cB df-sbc 3bitr4g $.

  $( This theorem, which is similar to Theorem 6.7 of [Quine] p. 42 and holds
     under both our definition and Quine's, relates logic substitution ~ df-sb
     and substitution for class variables ~ df-sbc .  Unlike Quine, we use a
     different syntax for each in order to avoid overloading it.  See remarks
     in ~ dfsbcq .  (Contributed by NM, 31-Dec-2016.) $)
  dfsbcq2 $p |- ( y = A -> ( [ y / x ] ph <-> [. A / x ]. ph ) ) $=
    vy cv cA wceq vy cv wph vx cab wcel cA wph vx cab wcel wph vx vy wsb wph vx
    cA wsbc vy cv cA wph vx cab eleq1 wph vy vx df-clab wph vx cA wsbc cA wph
    vx cab wcel wph vx cA df-sbc bicomi 3bitr3g $.

  $( Show that ~ df-sb and ~ df-sbc are equivalent when the class term ` A ` in
     ~ df-sbc is a set variable.  This theorem lets us reuse theorems based on
     ~ df-sb for proofs involving ~ df-sbc .  (Contributed by NM,
     31-Dec-2016.)  (Proof modification is discouraged.) $)
  sbsbc $p |- ( [ y / x ] ph <-> [. y / x ]. ph ) $=
    vy vy weq wph vx vy wsb wph vx vy cv wsbc wb vy cv eqid wph vx vy vy cv
    dfsbcq2 ax-mp $.

  ${
    sbceq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for class substitution.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    sbceq1d $p |- ( ph -> ( [. A / x ]. ph <-> [. B / x ]. ph ) ) $=
      wph cA cB wceq wph vx cA wsbc wph vx cB wsbc wb sbceq1d.1 wph vx cA cB
      dfsbcq syl $.

    sbceq1dd.2 $e |- ( ph -> [. A / x ]. ph ) $.
    $( Equality theorem for class substitution.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    sbceq1dd $p |- ( ph -> [. B / x ]. ph ) $=
      wph wph vx cA wsbc wph vx cB wsbc sbceq1dd.2 wph vx cA cB sbceq1d.1
      sbceq1d mpbid $.
  $}

  ${
    $d y A $.  $d y ph $.  $d x y $.
    $( This is the closest we can get to ~ df-sbc if we start from ~ dfsbcq
       (see its comments) and ~ dfsbcq2 .  (Contributed by NM, 18-Nov-2008.)
       (Proof shortened by Andrew Salmon, 29-Jun-2011.)
       (Proof modification is discouraged.) $)
    sbc8g $p |- ( A e. V -> ( [. A / x ]. ph <-> A e. { x | ph } ) ) $=
      wph vx vy cv wsbc vy cv wph vx cab wcel wph vx cA wsbc cA wph vx cab wcel
      vy cA cV wph vx vy cv cA dfsbcq vy cv cA wph vx cab eleq1 vy cv wph vx
      cab wcel wph vx vy wsb wph vx vy cv wsbc wph vy vx df-clab vy vy weq wph
      vx vy wsb wph vx vy cv wsbc wb vy equid wph vx vy vy cv dfsbcq2 ax-mp
      bitr2i vtoclbg $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( The disjunction of two equivalences for class substitution does not
       require a class existence hypothesis.  This theorem tells us that there
       are only 2 possibilities for ` [ A / x ] ph ` behavior at proper
       classes, matching the ~ sbc5 (false) and ~ sbc6 (true) conclusions.
       This is interesting since ~ dfsbcq and ~ dfsbcq2 (from which it is
       derived) do not appear to say anything obvious about proper class
       behavior.  Note that this theorem doesn't tell us that it is always one
       or the other at proper classes; it could "flip" between false (the first
       disjunct) and true (the second disjunct) as a function of some other
       variable ` y ` that ` ph ` or ` A ` may contain.  (Contributed by NM,
       11-Oct-2004.)  (Proof modification is discouraged.) $)
    sbc2or $p |- ( ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) \/
                  ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) ) $=
      cA cvv wcel wph vx cA wsbc vx cv cA wceq wph wa vx wex wb wph vx cA wsbc
      vx cv cA wceq wph wi vx wal wb wo cA cvv wcel wph vx cA wsbc vx cv cA
      wceq wph wa vx wex wb wph vx cA wsbc vx cv cA wceq wph wi vx wal wb wph
      vx vy wsb vx vy weq wph wa vx wex wph vx cA wsbc vx cv cA wceq wph wa vx
      wex vy cA cvv wph vx vy cA dfsbcq2 vy cv cA wceq vx vy weq wph wa vx cv
      cA wceq wph wa vx vy cv cA wceq vx vy weq vx cv cA wceq wph vy cv cA vx
      cv eqeq2 anbi1d exbidv wph vx vy sb5 vtoclbg orcd cA cvv wcel wn wph vx
      cA wsbc vx cv cA wceq wph wa vx wex wb wph vx cA wsbc vx cv cA wceq wph
      wa vx wex wn wb wo wph vx cA wsbc vx cv cA wceq wph wa vx wex wb wph vx
      cA wsbc vx cv cA wceq wph wi vx wal wb wo wph vx cA wsbc vx cv cA wceq
      wph wa vx wex pm5.15 cA cvv wcel wn wph vx cA wsbc vx cv cA wceq wph wa
      vx wex wn wb wph vx cA wsbc vx cv cA wceq wph wi vx wal wb wph vx cA wsbc
      vx cv cA wceq wph wa vx wex wb cA cvv wcel wn vx cv cA wceq wph wa vx wex
      wn vx cv cA wceq wph wi vx wal wph vx cA wsbc cA cvv wcel wn vx cv cA
      wceq wph wa vx wex wn vx cv cA wceq wph wi vx wal cA cvv wcel wn vx cv cA
      wceq wph wa vx vx cv cA wceq wph wa cA cvv wcel vx cv cA wceq cA cvv wcel
      wph vx cv cA wceq vx cv cvv wcel cA cvv wcel vx vex vx cv cA cvv eleq1
      mpbii adantr con3i nexdv cA cvv wcel wn vx cv cA wceq wph wi vx cA cvv
      wcel wn vx cv cA wceq wph vx cv cA wceq cA cvv wcel vx cv cA wceq vx cv
      cvv wcel cA cvv wcel vx vex vx cv cA cvv eleq1 mpbii con3i pm2.21d
      alrimiv 2thd bibi2d orbi2d mpbii pm2.61i $.
  $}

  $( By our definition of proper substitution, it can only be true if the
     substituted expression is a set.  (Contributed by Mario Carneiro,
     13-Oct-2016.) $)
  sbcex $p |- ( [. A / x ]. ph -> A e. _V ) $=
    wph vx cA wsbc cA wph vx cab wcel cA cvv wcel wph vx cA df-sbc cA wph vx
    cab elex sylbi $.

  $( Equality theorem for class substitution.  Class version of ~ sbequ12 .
     (Contributed by NM, 26-Sep-2003.) $)
  sbceq1a $p |- ( x = A -> ( ph <-> [. A / x ]. ph ) ) $=
    wph wph vx vx wsb vx cv cA wceq wph vx cA wsbc wph vx sbid wph vx vx cA
    dfsbcq2 syl5bbr $.

  $( Equality theorem for class substitution.  Class version of ~ sbequ12r .
     (Contributed by NM, 4-Jan-2017.) $)
  sbceq2a $p |- ( A = x -> ( [. A / x ]. ph <-> ph ) ) $=
    cA vx cv wceq wph wph vx cA wsbc wph wph vx cA wsbc wb vx cv cA wph vx cA
    sbceq1a eqcoms bicomd $.

  ${
    $d ph y $.  $d A y $.  $d x y $.
    $( Specialization: if a formula is true for all sets, it is true for any
       class which is a set.  Similar to Theorem 6.11 of [Quine] p. 44.  See
       also ~ stdpc4 and ~ rspsbc .  (Contributed by NM, 16-Jan-2004.) $)
    spsbc $p |- ( A e. V -> ( A. x ph -> [. A / x ]. ph ) ) $=
      wph vx wal wph vx cA wsbc wi vy cA cV wph vx wal wph vx vy cv wsbc vy cv
      cA wceq wph vx cA wsbc wph vx wal wph vx vy wsb wph vx vy cv wsbc wph vx
      vy stdpc4 wph vx vy sbsbc sylib wph vx vy cv cA dfsbcq syl5ib vtocleg $.

    spsbcd.1 $e |- ( ph -> A e. V ) $.
    spsbcd.2 $e |- ( ph -> A. x ps ) $.
    $( Specialization: if a formula is true for all sets, it is true for any
       class which is a set.  Similar to Theorem 6.11 of [Quine] p. 44.  See
       also ~ stdpc4 and ~ rspsbc .  (Contributed by Mario Carneiro,
       9-Feb-2017.) $)
    spsbcd $p |- ( ph -> [. A / x ]. ps ) $=
      wph cA cV wcel wps vx wal wps vx cA wsbc spsbcd.1 spsbcd.2 wps vx cA cV
      spsbc sylc $.
  $}

  ${
    sbcth.1 $e |- ph $.
    $( A substitution into a theorem remains true (when ` A ` is a set).
       (Contributed by NM, 5-Nov-2005.) $)
    sbcth $p |- ( A e. V -> [. A / x ]. ph ) $=
      cA cV wcel wph vx wal wph vx cA wsbc wph vx sbcth.1 ax-gen wph vx cA cV
      spsbc mpi $.
  $}

  ${
    $d x ph $.
    sbcthdv.1 $e |- ( ph -> ps ) $.
    $( Deduction version of ~ sbcth .  (Contributed by NM, 30-Nov-2005.)
       (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    sbcthdv $p |- ( ( ph /\ A e. V ) -> [. A / x ]. ps ) $=
      wph wps vx wal cA cV wcel wps vx cA wsbc wph wps vx sbcthdv.1 alrimiv wps
      vx cA cV spsbc mpan9 $.
  $}

  $( An identity theorem for substitution.  See ~ sbid .  (Contributed by Mario
     Carneiro, 18-Feb-2017.) $)
  sbcid $p |- ( [. x / x ]. ph <-> ph )
    $=
    wph vx vx cv wsbc wph vx vx wsb wph wph vx vx sbsbc wph vx sbid bitr3i $.

  ${
    nfsbc1d.2 $e |- ( ph -> F/_ x A ) $.
    $( Deduction version of ~ nfsbc1 .  (Contributed by NM, 23-May-2006.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)
    nfsbc1d $p |- ( ph -> F/ x [. A / x ]. ps ) $=
      wps vx cA wsbc cA wps vx cab wcel wph vx wps vx cA df-sbc wph vx cA wps
      vx cab nfsbc1d.2 vx wps vx cab wnfc wph wps vx nfab1 a1i nfeld nfxfrd $.
  $}

  ${
    nfsbc1.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for class substitution.  (Contributed
       by Mario Carneiro, 12-Oct-2016.) $)
    nfsbc1 $p |- F/ x [. A / x ]. ph $=
      wph vx cA wsbc vx wnf wtru wph vx cA vx cA wnfc wtru nfsbc1.1 a1i nfsbc1d
      trud $.
  $}

  ${
    $d x A $.
    $( Bound-variable hypothesis builder for class substitution.  (Contributed
       by Mario Carneiro, 12-Oct-2016.) $)
    nfsbc1v $p |- F/ x [. A / x ]. ph $=
      wph vx cA vx cA nfcv nfsbc1 $.
  $}

  ${
    nfsbcd.1 $e |- F/ y ph $.
    nfsbcd.2 $e |- ( ph -> F/_ x A ) $.
    nfsbcd.3 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfsbc .  (Contributed by NM, 23-Nov-2005.)
       (Revised by Mario Carneiro, 12-Oct-2016.) $)
    nfsbcd $p |- ( ph -> F/ x [. A / y ]. ps ) $=
      wps vy cA wsbc cA wps vy cab wcel wph vx wps vy cA df-sbc wph vx cA wps
      vy cab nfsbcd.2 wph wps vx vy nfsbcd.1 nfsbcd.3 nfabd nfeld nfxfrd $.
  $}

  ${
    nfsbc.1 $e |- F/_ x A $.
    nfsbc.2 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for class substitution.  (Contributed
       by NM, 7-Sep-2014.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)
    nfsbc $p |- F/ x [. A / y ]. ph $=
      wph vy cA wsbc vx wnf wtru wph vx vy cA vy nftru vx cA wnfc wtru nfsbc.1
      a1i wph vx wnf wtru nfsbc.2 a1i nfsbcd trud $.
  $}

  ${
    $d x z $.  $d z A $.  $d y z ph $.
    $( A composition law for class substitution.  (Contributed by NM,
       26-Sep-2003.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)
    sbcco $p |- ( [. A / y ]. [. y / x ]. ph <-> [. A / x ]. ph ) $=
      wph vx vy cv wsbc vy cA wsbc cA cvv wcel wph vx cA wsbc wph vx vy cv wsbc
      vy cA sbcex wph vx cA sbcex wph vx vy cv wsbc vy vz cv wsbc wph vx vz cv
      wsbc wph vx vy cv wsbc vy cA wsbc wph vx cA wsbc vz cA cvv wph vx vy cv
      wsbc vy vz cv cA dfsbcq wph vx vz cv cA dfsbcq wph vx vy cv wsbc vy vz cv
      wsbc wph vx vz wsb wph vx vz cv wsbc wph vx vy wsb vy vz wsb wph vx vy cv
      wsbc vy vz wsb wph vx vz wsb wph vx vy cv wsbc vy vz cv wsbc wph vx vy
      wsb wph vx vy cv wsbc vy vz wph vx vy sbsbc sbbii wph vx vz vy wph vy nfv
      sbco2 wph vx vy cv wsbc vy vz sbsbc 3bitr3ri wph vx vz sbsbc bitri
      vtoclbg pm5.21nii $.
  $}

  ${
    $d x y $.  $d y ph $.  $d A y $.
    sbcco2.1 $e |- ( x = y -> A = B ) $.
    $( A composition law for class substitution.  Importantly, ` x ` may occur
       free in the class expression substituted for ` A ` .  (Contributed by
       NM, 5-Sep-2004.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    sbcco2 $p |- ( [. x / y ]. [. B / x ]. ph <-> [. A / x ]. ph ) $=
      wph vx cB wsbc vy vx cv wsbc wph vx cB wsbc vy vx wsb wph vx cA wsbc wph
      vx cB wsbc vy vx sbsbc wph vx cB wsbc wph vx cA wsbc vy vx wph vx cA wsbc
      vy nfv vy vx weq cA cB wceq wph vx cB wsbc wph vx cA wsbc wb cA cB wceq
      vx cv vy cv sbcco2.1 eqcoms cA cB wceq wph vx cA wsbc wph vx cB wsbc wph
      vx cA cB dfsbcq bicomd syl sbie bitr3i $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( An equivalence for class substitution.  (Contributed by NM,
       23-Aug-1993.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)
    sbc5 $p |- ( [. A / x ]. ph <-> E. x ( x = A /\ ph ) ) $=
      wph vx cA wsbc cA cvv wcel vx cv cA wceq wph wa vx wex wph vx cA sbcex vx
      cv cA wceq wph wa vx wex vx cv cA wceq vx wex cA cvv wcel vx cv cA wceq
      wph vx exsimpl vx cA isset sylibr wph vx vy wsb vx vy weq wph wa vx wex
      wph vx cA wsbc vx cv cA wceq wph wa vx wex vy cA cvv wph vx vy cA dfsbcq2
      vy cv cA wceq vx vy weq wph wa vx cv cA wceq wph wa vx vy cv cA wceq vx
      vy weq vx cv cA wceq wph vy cv cA vx cv eqeq2 anbi1d exbidv wph vx vy sb5
      vtoclbg pm5.21nii $.
  $}

  ${
    $d x y A $.
    $( An equivalence for class substitution.  (Contributed by NM,
       11-Oct-2004.)  (Proof shortened by Andrew Salmon, 8-Jun-2011.) $)
    sbc6g $p |- ( A e. V -> ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) ) $=
      cA cV wcel vx cv cA wceq wph wi vx wal vx cv cA wceq wph wa vx wex wph vx
      cA wsbc wph vx cv cA wceq wph wa vx wex vx cA cV vx cv cA wceq wph wa vx
      nfe1 wph vx cA ceqex ceqsalg wph vx cA sbc5 syl6rbbr $.
  $}

  ${
    $d x A $.
    sbc6.1 $e |- A e. _V $.
    $( An equivalence for class substitution.  (Contributed by NM,
       23-Aug-1993.)  (Proof shortened by Eric Schmidt, 17-Jan-2007.) $)
    sbc6 $p |- ( [. A / x ]. ph <-> A. x ( x = A -> ph ) ) $=
      cA cvv wcel wph vx cA wsbc vx cv cA wceq wph wi vx wal wb sbc6.1 wph vx
      cA cvv sbc6g ax-mp $.
  $}

  ${
    $d y A $.  $d y ph $.  $d x y $.
    $( An equivalence for class substitution in the spirit of ~ df-clab .  Note
       that ` x ` and ` A ` don't have to be distinct.  (Contributed by NM,
       18-Nov-2008.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)
    sbc7 $p |- ( [. A / x ]. ph <-> E. y ( y = A /\ [. y / x ]. ph ) ) $=
      wph vx cA wsbc wph vx vy cv wsbc vy cA wsbc vy cv cA wceq wph vx vy cv
      wsbc wa vy wex wph vx vy cA sbcco wph vx vy cv wsbc vy cA sbc5 bitr3i $.
  $}

  ${
    cbvsbc.1 $e |- F/ y ph $.
    cbvsbc.2 $e |- F/ x ps $.
    cbvsbc.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variables in a wff substitution.  (Contributed by Jeff
       Hankins, 19-Sep-2009.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
    cbvsbc $p |- ( [. A / x ]. ph <-> [. A / y ]. ps ) $=
      cA wph vx cab wcel cA wps vy cab wcel wph vx cA wsbc wps vy cA wsbc wph
      vx cab wps vy cab cA wph wps vx vy cbvsbc.1 cbvsbc.2 cbvsbc.3 cbvab
      eleq2i wph vx cA df-sbc wps vy cA df-sbc 3bitr4i $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvsbcv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change the bound variable of a class substitution using implicit
       substitution.  (Contributed by NM, 30-Sep-2008.)  (Revised by Mario
       Carneiro, 13-Oct-2016.) $)
    cbvsbcv $p |- ( [. A / x ]. ph <-> [. A / y ]. ps ) $=
      wph wps vx vy cA wph vy nfv wps vx nfv cbvsbcv.1 cbvsbc $.
  $}

  ${
    $d x y A $.  $d y ps $.
    $( Conversion of implicit substitution to explicit class substitution,
       using a bound-variable hypothesis instead of distinct variables.
       (Closed theorem version of ~ sbciegf .)  (Contributed by NM,
       10-Nov-2005.)  (Revised by Mario Carneiro, 13-Oct-2016.) $)
    sbciegft $p |- ( ( A e. V /\ F/ x ps /\
            A. x ( x = A -> ( ph <-> ps ) ) ) -> ( [. A / x ]. ph <-> ps ) ) $=
      cA cV wcel wps vx wnf vx cv cA wceq wph wps wb wi vx wal w3a wph vx cA
      wsbc wps wph vx cA wsbc vx cv cA wceq wph wa vx wex cA cV wcel wps vx wnf
      vx cv cA wceq wph wps wb wi vx wal w3a wps wph vx cA sbc5 wps vx wnf vx
      cv cA wceq wph wps wb wi vx wal vx cv cA wceq wph wa vx wex wps wi cA cV
      wcel vx cv cA wceq wph wps wb wi vx wal wps vx wnf vx cv cA wceq wph wa
      wps wi vx wal vx cv cA wceq wph wa vx wex wps wi vx cv cA wceq wph wps wb
      wi vx cv cA wceq wph wa wps wi vx vx cv cA wceq wph wps wb wi vx cv cA
      wceq wph wps wph wps wb wph wps wi vx cv cA wceq wph wps bi1 imim2i imp3a
      alimi wps vx wnf vx cv cA wceq wph wa wps wi vx wal vx cv cA wceq wph wa
      vx wex wps wi vx cv cA wceq wph wa wps vx 19.23t biimpa sylan2 3adant1
      syl5bi cA cV wcel wps vx wnf vx cv cA wceq wph wps wb wi vx wal w3a wps
      vx cv cA wceq wph wi vx wal wph vx cA wsbc wps vx wnf vx cv cA wceq wph
      wps wb wi vx wal wps vx cv cA wceq wph wi vx wal wi cA cV wcel vx cv cA
      wceq wph wps wb wi vx wal wps vx wnf wps vx cv cA wceq wph wi wi vx wal
      wps vx cv cA wceq wph wi vx wal wi vx cv cA wceq wph wps wb wi wps vx cv
      cA wceq wph wi wi vx vx cv cA wceq wph wps wb wi vx cv cA wceq wps wph
      wph wps wb wps wph wi vx cv cA wceq wph wps bi2 imim2i com23 alimi wps vx
      wnf wps vx cv cA wceq wph wi wi vx wal wps vx cv cA wceq wph wi vx wal wi
      wps vx cv cA wceq wph wi vx 19.21t biimpa sylan2 3adant1 cA cV wcel wps
      vx wnf wph vx cA wsbc vx cv cA wceq wph wi vx wal wb vx cv cA wceq wph
      wps wb wi vx wal wph vx cA cV sbc6g 3ad2ant1 sylibrd impbid $.
  $}

  ${
    $d x A $.
    sbciegf.1 $e |- F/ x ps $.
    sbciegf.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       13-Oct-2016.) $)
    sbciegf $p |- ( A e. V -> ( [. A / x ]. ph <-> ps ) ) $=
      cA cV wcel wps vx wnf vx cv cA wceq wph wps wb wi vx wal wph vx cA wsbc
      wps wb sbciegf.1 vx cv cA wceq wph wps wb wi vx sbciegf.2 ax-gen wph wps
      vx cA cV sbciegft mp3an23 $.
  $}

  ${
    $d x A $.  $d x ps $.
    sbcieg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 10-Nov-2005.) $)
    sbcieg $p |- ( A e. V -> ( [. A / x ]. ph <-> ps ) ) $=
      cA cV wcel cA cvv wcel wph vx cA wsbc wps wb cA cV elex wph wps vx cA cvv
      wps vx nfv sbcieg.1 sbciegf syl $.
  $}

  ${
    $d x y $.  $d A y $.  $d ch y $.  $d ph y $.  $d ps x $.
    sbcie2g.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    sbcie2g.2 $e |- ( y = A -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       This version of ~ sbcie avoids a disjointness condition on ` x , A ` by
       substituting twice.  (Contributed by Mario Carneiro, 15-Oct-2016.) $)
    sbcie2g $p |- ( A e. V -> ( [. A / x ]. ph <-> ch ) ) $=
      wph vx vy cv wsbc wps wph vx cA wsbc wch vy cA cV wph vx vy cv cA dfsbcq
      sbcie2g.2 wph vx vy cv wsbc wph vx vy wsb wps wph vx vy sbsbc wph wps vx
      vy wps vx nfv sbcie2g.1 sbie bitr3i vtoclbg $.
  $}

  ${
    $d x A $.  $d x ps $.
    sbcie.1 $e |- A e. _V $.
    sbcie.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 4-Sep-2004.) $)
    sbcie $p |- ( [. A / x ]. ph <-> ps ) $=
      cA cvv wcel wph vx cA wsbc wps wb sbcie.1 wph wps vx cA cvv sbcie.2
      sbcieg ax-mp $.
  $}

  ${
    $d x A $.
    sbcied.1 $e |- ( ph -> A e. V ) $.
    sbcied.2 $e |- ( ( ph /\ x = A ) -> ( ps <-> ch ) ) $.
    ${
      sbciedf.3 $e |- F/ x ph $.
      sbciedf.4 $e |- ( ph -> F/ x ch ) $.
      $( Conversion of implicit substitution to explicit class substitution,
         deduction form.  (Contributed by NM, 29-Dec-2014.) $)
      sbciedf $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $=
        wph cA cV wcel wch vx wnf vx cv cA wceq wps wch wb wi vx wal wps vx cA
        wsbc wch wb sbcied.1 sbciedf.4 wph vx cv cA wceq wps wch wb wi vx
        sbciedf.3 wph vx cv cA wceq wps wch wb sbcied.2 ex alrimi wps wch vx cA
        cV sbciegft syl3anc $.
    $}

    $d x ph $.  $d x ch $.
    $( Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by NM, 13-Dec-2014.) $)
    sbcied $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $=
      wph wps wch vx cA cV sbcied.1 sbcied.2 wph vx nfv wph wch vx nfvd sbciedf
      $.
  $}

  ${
    $d x A $.  $d x ph $.  $d x ch $.
    sbcied2.1 $e |- ( ph -> A e. V ) $.
    sbcied2.2 $e |- ( ph -> A = B ) $.
    sbcied2.3 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit class substitution,
       deduction form.  (Contributed by NM, 13-Dec-2014.) $)
    sbcied2 $p |- ( ph -> ( [. A / x ]. ps <-> ch ) ) $=
      wph wps wch vx cA cV sbcied2.1 wph vx cv cA wceq vx cv cB wceq wps wch wb
      vx cv cA wceq wph vx cv cA cB vx cv cA wceq id sbcied2.2 sylan9eqr
      sbcied2.3 syldan sbcied $.
  $}

  ${
    $d y A $.  $d y B $.  $d y ph $.  $d x y $.
    elrabsf.1 $e |- F/_ x B $.
    $( Membership in a restricted class abstraction, expressed with explicit
       class substitution.  (The variation ~ elrabf has implicit
       substitution).  The hypothesis specifies that ` x ` must not be a free
       variable in ` B ` .  (Contributed by NM, 30-Sep-2003.)  (Proof shortened
       by Mario Carneiro, 13-Oct-2016.) $)
    elrabsf $p |- ( A e. { x e. B | ph }
          <-> ( A e. B /\ [. A / x ]. ph ) ) $=
      wph vx vy cv wsbc wph vx cA wsbc vy cA cB wph vx cB crab wph vx vy cv cA
      dfsbcq wph wph vx vy cv wsbc vx vy cB elrabsf.1 vy cB nfcv wph vy nfv wph
      vx vy cv nfsbc1v wph vx vy cv sbceq1a cbvrab elrab2 $.
  $}

  ${
    $d x y B $.  $d y A $.
    $( Substitution applied to an atomic wff.  Set theory version of ~ eqsb3 .
       (Contributed by Andrew Salmon, 29-Jun-2011.) $)
    eqsbc3 $p |- ( A e. V -> ( [. A / x ]. x = B <-> A = B ) ) $=
      vx cv cB wceq vx vy cv wsbc vy cv cB wceq vx cv cB wceq vx cA wsbc cA cB
      wceq vy cA cV vx cv cB wceq vx vy cv cA dfsbcq vy cv cA cB eqeq1 vx cv cB
      wceq vx vy cv wsbc vx cv cB wceq vx vy wsb vy cv cB wceq vx cv cB wceq vx
      vy sbsbc vy vx cB eqsb3 bitr3i vtoclbg $.
  $}

  ${
    $d x y $.  $d y A $.  $d y ph $.  $d y ps $.
    $( Move negation in and out of class substitution.  (Contributed by NM,
       16-Jan-2004.) $)
    sbcng $p |- ( A e. V -> ( [. A / x ]. -. ph <-> -. [. A / x ]. ph ) ) $=
      wph wn vx vy wsb wph vx vy wsb wn wph wn vx cA wsbc wph vx cA wsbc wn vy
      cA cV wph wn vx vy cA dfsbcq2 vy cv cA wceq wph vx vy wsb wph vx cA wsbc
      wph vx vy cA dfsbcq2 notbid wph vx vy sbn vtoclbg $.

    $( Distribution of class substitution over implication.  (Contributed by
       NM, 16-Jan-2004.) $)
    sbcimg $p |- ( A e. V ->
     ( [. A / x ]. ( ph -> ps ) <-> ( [. A / x ]. ph -> [. A / x ]. ps ) ) ) $=
      wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wph wps wi vx cA wsbc
      wph vx cA wsbc wps vx cA wsbc wi vy cA cV wph wps wi vx vy cA dfsbcq2 vy
      cv cA wceq wph vx vy wsb wph vx cA wsbc wps vx vy wsb wps vx cA wsbc wph
      vx vy cA dfsbcq2 wps vx vy cA dfsbcq2 imbi12d wph wps vx vy sbim vtoclbg
      $.

    $( Distribution of class substitution over conjunction.  (Contributed by
       NM, 31-Dec-2016.) $)
    sbcan $p |- ( [. A / x ]. ( ph /\ ps )
        <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) ) $=
      wph wps wa vx cA wsbc cA cvv wcel wph vx cA wsbc wps vx cA wsbc wa wph
      wps wa vx cA sbcex wps vx cA wsbc cA cvv wcel wph vx cA wsbc wps vx cA
      sbcex adantl wph wps wa vx vy wsb wph vx vy wsb wps vx vy wsb wa wph wps
      wa vx cA wsbc wph vx cA wsbc wps vx cA wsbc wa vy cA cvv wph wps wa vx vy
      cA dfsbcq2 vy cv cA wceq wph vx vy wsb wph vx cA wsbc wps vx vy wsb wps
      vx cA wsbc wph vx vy cA dfsbcq2 wps vx vy cA dfsbcq2 anbi12d wph wps vx
      vy sban vtoclbg pm5.21nii $.

    $( Distribution of class substitution over conjunction.  (Contributed by
       NM, 21-May-2004.) $)
    sbcang $p |- ( A e. V ->
     ( [. A / x ]. ( ph /\ ps ) <-> ( [. A / x ]. ph /\ [. A / x ]. ps ) ) ) $=
      wph wps wa vx vy wsb wph vx vy wsb wps vx vy wsb wa wph wps wa vx cA wsbc
      wph vx cA wsbc wps vx cA wsbc wa vy cA cV wph wps wa vx vy cA dfsbcq2 vy
      cv cA wceq wph vx vy wsb wph vx cA wsbc wps vx vy wsb wps vx cA wsbc wph
      vx vy cA dfsbcq2 wps vx vy cA dfsbcq2 anbi12d wph wps vx vy sban vtoclbg
      $.

    $( Distribution of class substitution over disjunction.  (Contributed by
       NM, 31-Dec-2016.) $)
    sbcor $p |- ( [. A / x ]. ( ph \/ ps )
         <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) $=
      wph wps wo vx cA wsbc cA cvv wcel wph vx cA wsbc wps vx cA wsbc wo wph
      wps wo vx cA sbcex wph vx cA wsbc cA cvv wcel wps vx cA wsbc wph vx cA
      sbcex wps vx cA sbcex jaoi wph wps wo vx vy wsb wph vx vy wsb wps vx vy
      wsb wo wph wps wo vx cA wsbc wph vx cA wsbc wps vx cA wsbc wo vy cA cvv
      wph wps wo vx vy cA dfsbcq2 vy cv cA wceq wph vx vy wsb wph vx cA wsbc
      wps vx vy wsb wps vx cA wsbc wph vx vy cA dfsbcq2 wps vx vy cA dfsbcq2
      orbi12d wph wps vx vy sbor vtoclbg pm5.21nii $.

    $( Distribution of class substitution over disjunction.  (Contributed by
       NM, 21-May-2004.) $)
    sbcorg $p |- ( A e. V ->
     ( [. A / x ]. ( ph \/ ps ) <-> ( [. A / x ]. ph \/ [. A / x ]. ps ) ) ) $=
      wph wps wo vx vy wsb wph vx vy wsb wps vx vy wsb wo wph wps wo vx cA wsbc
      wph vx cA wsbc wps vx cA wsbc wo vy cA cV wph wps wo vx vy cA dfsbcq2 vy
      cv cA wceq wph vx vy wsb wph vx cA wsbc wps vx vy wsb wps vx cA wsbc wph
      vx vy cA dfsbcq2 wps vx vy cA dfsbcq2 orbi12d wph wps vx vy sbor vtoclbg
      $.

    $( Distribution of class substitution over biconditional.  (Contributed by
       Raph Levien, 10-Apr-2004.) $)
    sbcbig $p |- ( A e. V ->
   ( [. A / x ]. ( ph <-> ps ) <-> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) ) $=
      wph wps wb vx vy wsb wph vx vy wsb wps vx vy wsb wb wph wps wb vx cA wsbc
      wph vx cA wsbc wps vx cA wsbc wb vy cA cV wph wps wb vx vy cA dfsbcq2 vy
      cv cA wceq wph vx vy wsb wph vx cA wsbc wps vx vy wsb wps vx cA wsbc wph
      vx vy cA dfsbcq2 wps vx vy cA dfsbcq2 bibi12d wph wps vx vy sbbi vtoclbg
      $.
  $}

  ${
    $d x z A $.  $d x y z $.  $d z ph $.
    $( Move universal quantifier in and out of class substitution.
       (Contributed by NM, 31-Dec-2016.) $)
    sbcal $p |- ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) $=
      wph vx wal vy cA wsbc cA cvv wcel wph vy cA wsbc vx wal wph vx wal vy cA
      sbcex wph vy cA wsbc cA cvv wcel vx wph vy cA sbcex sps wph vx wal vy vz
      wsb wph vy vz wsb vx wal wph vx wal vy cA wsbc wph vy cA wsbc vx wal vz
      cA cvv wph vx wal vy vz cA dfsbcq2 vz cv cA wceq wph vy vz wsb wph vy cA
      wsbc vx wph vy vz cA dfsbcq2 albidv wph vx vy vz sbal vtoclbg pm5.21nii
      $.

    $( Move universal quantifier in and out of class substitution.
       (Contributed by NM, 16-Jan-2004.) $)
    sbcalg $p |- ( A e. V
        -> ( [. A / y ]. A. x ph <-> A. x [. A / y ]. ph ) ) $=
      wph vx wal vy vz wsb wph vy vz wsb vx wal wph vx wal vy cA wsbc wph vy cA
      wsbc vx wal vz cA cV wph vx wal vy vz cA dfsbcq2 vz cv cA wceq wph vy vz
      wsb wph vy cA wsbc vx wph vy vz cA dfsbcq2 albidv wph vx vy vz sbal
      vtoclbg $.

    $( Move existential quantifier in and out of class substitution.
       (Contributed by NM, 21-May-2004.) $)
    sbcex2 $p |- ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) $=
      wph vx wex vy cA wsbc cA cvv wcel wph vy cA wsbc vx wex wph vx wex vy cA
      sbcex wph vy cA wsbc cA cvv wcel vx wph vy cA sbcex exlimiv wph vx wex vy
      vz wsb wph vy vz wsb vx wex wph vx wex vy cA wsbc wph vy cA wsbc vx wex
      vz cA cvv wph vx wex vy vz cA dfsbcq2 vz cv cA wceq wph vy vz wsb wph vy
      cA wsbc vx wph vy vz cA dfsbcq2 exbidv wph vx vy vz sbex vtoclbg
      pm5.21nii $.

    $( Move existential quantifier in and out of class substitution.
       (Contributed by NM, 21-May-2004.) $)
    sbcexg $p |- ( A e. V
         -> ( [. A / y ]. E. x ph <-> E. x [. A / y ]. ph ) ) $=
      wph vx wex vy vz wsb wph vy vz wsb vx wex wph vx wex vy cA wsbc wph vy cA
      wsbc vx wex vz cA cV wph vx wex vy vz cA dfsbcq2 vz cv cA wceq wph vy vz
      wsb wph vy cA wsbc vx wph vy vz cA dfsbcq2 exbidv wph vx vy vz sbex
      vtoclbg $.
  $}

  ${
    $d x B $.  $d x A $.
    $( Set theory version of ~ sbeqal1 .  (Contributed by Andrew Salmon,
       28-Jun-2011.) $)
    sbceqal $p |- ( A e. V -> ( A. x ( x = A -> x = B ) -> A = B ) ) $=
      cA cV wcel vx cv cA wceq vx cv cB wceq wi vx wal vx cv cA wceq vx cv cB
      wceq wi vx cA wsbc cA cB wceq vx cv cA wceq vx cv cB wceq wi vx cA cV
      spsbc cA cV wcel vx cv cA wceq vx cv cB wceq wi vx cA wsbc vx cv cA wceq
      vx cA wsbc vx cv cB wceq vx cA wsbc wi vx cv cB wceq vx cA wsbc cA cB
      wceq vx cv cA wceq vx cv cB wceq vx cA cV sbcimg cA cV wcel vx cv cA wceq
      vx cA wsbc vx cv cA wceq vx cA wsbc vx cv cB wceq vx cA wsbc wi vx cv cB
      wceq vx cA wsbc wb cA cV wcel vx cv cA wceq vx cA wsbc cA cA wceq cA eqid
      vx cA cA cV eqsbc3 mpbiri vx cv cA wceq vx cA wsbc vx cv cB wceq vx cA
      wsbc pm5.5 syl vx cA cB cV eqsbc3 3bitrd sylibd $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Theorem *14.121 in [WhiteheadRussell] p. 185.  (Contributed by Andrew
       Salmon, 28-Jun-2011.)  (Proof shortened by Wolf Lammen, 9-May-2013.) $)
    sbeqalb $p |- ( A e. V -> ( ( A. x ( ph <-> x = A ) /\ A. x ( ph <->
      x = B ) ) -> A = B ) ) $=
      wph vx cv cA wceq wb vx wal wph vx cv cB wceq wb vx wal wa vx cv cA wceq
      vx cv cB wceq wi vx wal cA cV wcel cA cB wceq wph vx cv cA wceq wb wph vx
      cv cB wceq wb vx cv cA wceq vx cv cB wceq wi vx wph vx cv cA wceq wb wph
      vx cv cB wceq wb wa vx cv cA wceq vx cv cB wceq wph vx cv cA wceq wb wph
      vx cv cB wceq wb vx cv cA wceq vx cv cB wceq wb wph vx cv cA wceq vx cv
      cB wceq bibi1 biimpa biimpd alanimi vx cA cB cV sbceqal syl5 $.
  $}

  ${
    sbcbid.1 $e |- F/ x ph $.
    sbcbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building deduction rule for class substitution.  (Contributed by
       NM, 29-Dec-2014.) $)
    sbcbid $p |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) ) $=
      wph cA wps vx cab wcel cA wch vx cab wcel wps vx cA wsbc wch vx cA wsbc
      wph wps vx cab wch vx cab cA wph wps wch vx sbcbid.1 sbcbid.2 abbid
      eleq2d wps vx cA df-sbc wch vx cA df-sbc 3bitr4g $.
  $}

  ${
    $d x ph $.
    sbcbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building deduction rule for class substitution.  (Contributed by
       NM, 29-Dec-2014.) $)
    sbcbidv $p |- ( ph -> ( [. A / x ]. ps <-> [. A / x ]. ch ) ) $=
      wph wps wch vx cA wph vx nfv sbcbidv.1 sbcbid $.
  $}

  ${
    sbcbii.1 $e |- ( ph <-> ps ) $.
    $( Formula-building inference rule for class substitution.  (Contributed by
       NM, 11-Nov-2005.) $)
    sbcbii $p |- ( [. A / x ]. ph <-> [. A / x ]. ps ) $=
      wph vx cA wsbc wps vx cA wsbc wb wtru wph wps vx cA wph wps wb wtru
      sbcbii.1 a1i sbcbidv trud $.

    $( Formula-building inference rule for class substitution.  (Contributed by
       NM, 11-Nov-2005.)  (New usage is discouraged.) $)
    sbcbiiOLD $p |- ( A e. V -> ( [. A / x ]. ph <-> [. A / x ]. ps ) ) $=
      wph vx cA wsbc wps vx cA wsbc wb cA cV wcel wph wps vx cA sbcbii.1 sbcbii
      a1i $.
  $}

  ${
    $d x C $.  $d x A $.
    $( ~ eqsbc3 with set variable on right side of equals sign.  This proof was
       automatically generated from the virtual deduction proof ~ eqsbc3rVD
       using a translation program.  (Contributed by Alan Sare,
       24-Oct-2011.) $)
    eqsbc3r $p |- ( A e. B -> ( [. A / x ]. C = x <-> C = A ) ) $=
      cA cB wcel cC vx cv wceq vx cA wsbc cC cA wceq cA cB wcel cC vx cv wceq
      vx cA wsbc cA cC wceq cC cA wceq cC vx cv wceq vx cA wsbc vx cv cC wceq
      vx cA wsbc cA cB wcel cA cC wceq cC vx cv wceq vx cA wsbc vx cv cC wceq
      vx cA wsbc cC vx cv wceq vx cv cC wceq vx cA cC vx cv eqcom sbcbii biimpi
      vx cA cC cB eqsbc3 syl5ib cA cC eqcom syl6ib cA cB wcel cC cA wceq vx cv
      cC wceq vx cA wsbc cC vx cv wceq vx cA wsbc cA cB wcel cC cA wceq cA cC
      wceq vx cv cC wceq vx cA wsbc cA cB wcel cC cA wceq cC cA wceq cA cC wceq
      cA cB wcel cC cA wceq idd cA cC eqcom syl6ibr vx cA cC cB eqsbc3 sylibrd
      cC vx cv wceq vx cv cC wceq vx cA cC vx cv eqcom sbcbii syl6ibr impbid $.
  $}

  ${
    $d y ch $.  $d y ps $.  $d y ph $.  $d y A $.  $d x y $.
    $( Distribution of class substitution over triple conjunction.
       (Contributed by NM, 14-Dec-2006.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    sbc3ang $p |- ( A e. V -> ( [. A / x ]. ( ph /\ ps /\ ch ) <->
                ( [. A / x ]. ph /\ [. A / x ]. ps /\ [. A / x ]. ch ) ) ) $=
      wph wps wch w3a vx vy wsb wph vx vy wsb wps vx vy wsb wch vx vy wsb w3a
      wph wps wch w3a vx cA wsbc wph vx cA wsbc wps vx cA wsbc wch vx cA wsbc
      w3a vy cA cV wph wps wch w3a vx vy cA dfsbcq2 vy cv cA wceq wph vx vy wsb
      wph vx cA wsbc wps vx vy wsb wps vx cA wsbc wch vx vy wsb wch vx cA wsbc
      wph vx vy cA dfsbcq2 wps vx vy cA dfsbcq2 wch vx vy cA dfsbcq2 3anbi123d
      wph wps wch vx vy sb3an vtoclbg $.
  $}

  ${
    $d y z A $.  $d x y B $.
    $( Class substitution into a membership relation.  (Contributed by NM,
       17-Nov-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    sbcel1gv $p |- ( A e. V -> ( [. A / x ]. x e. B <-> A e. B ) ) $=
      vx cv cB wcel vx vy wsb vy cv cB wcel vx cv cB wcel vx cA wsbc cA cB wcel
      vy cA cV vx cv cB wcel vx vy cA dfsbcq2 vy cv cA cB eleq1 vy vx cB
      clelsb3 vtoclbg $.
  $}

  ${
    $d y z B $.  $d x y A $.
    $( Class substitution into a membership relation.  (Contributed by NM,
       17-Nov-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    sbcel2gv $p |- ( B e. V -> ( [. B / x ]. A e. x <-> A e. B ) ) $=
      cA vx cv wcel vx vy wsb cA vy cv wcel cA vx cv wcel vx cB wsbc cA cB wcel
      vy cB cV cA vx cv wcel vx vy cB dfsbcq2 vy cv cB cA eleq2 cA vx cv wcel
      cA vy cv wcel vx vy cA vy cv wcel vx nfv vx cv vy cv cA eleq2 sbie
      vtoclbg $.
  $}

  ${
    $d x ph $.
    sbcimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Substitution analog of Theorem 19.20 of [Margaris] p. 90.  (Contributed
       by NM, 11-Nov-2005.) $)
    sbcimdv $p |- ( ( ph /\ A e. V ) ->
          ( [. A / x ]. ps -> [. A / x ]. ch ) ) $=
      cA cV wcel wph wps vx cA wsbc wch vx cA wsbc wi cA cV wcel wph wps wch wi
      vx cA wsbc wps vx cA wsbc wch vx cA wsbc wi wph wps wch wi vx wal cA cV
      wcel wps wch wi vx cA wsbc wph wps wch wi vx sbcimdv.1 alrimiv wps wch wi
      vx cA cV spsbc syl5 wps wch vx cA cV sbcimg sylibd impcom $.
  $}

  ${
    $d x y $.  $d y A $.  $d y ph $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by Mario Carneiro, 14-Oct-2016.) $)
    sbctt $p |- ( ( A e. V /\ F/ x ph ) -> ( [. A / x ]. ph <-> ph ) ) $=
      cA cV wcel wph vx wnf wph vx cA wsbc wph wb wph vx wnf wph vx vy wsb wph
      wb wi wph vx wnf wph vx cA wsbc wph wb wi vy cA cV vy cv cA wceq wph vx
      vy wsb wph wb wph vx cA wsbc wph wb wph vx wnf vy cv cA wceq wph vx vy
      wsb wph vx cA wsbc wph wph vx vy cA dfsbcq2 bibi1d imbi2d wph vx vy sbft
      vtoclg imp $.
  $}

  ${
    $d y A $.  $d y ph $.  $d x y $.
    sbcgf.1 $e |- F/ x ph $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 11-Oct-2004.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    sbcgf $p |- ( A e. V -> ( [. A / x ]. ph <-> ph ) ) $=
      cA cV wcel wph vx wnf wph vx cA wsbc wph wb sbcgf.1 wph vx cA cV sbctt
      mpan2 $.

    $( Substitution for a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 11-Oct-2004.) $)
    sbc19.21g $p |- ( A e. V ->
            ( [. A / x ]. ( ph -> ps ) <-> ( ph -> [. A / x ]. ps ) ) ) $=
      cA cV wcel wph wps wi vx cA wsbc wph vx cA wsbc wps vx cA wsbc wi wph wps
      vx cA wsbc wi wph wps vx cA cV sbcimg cA cV wcel wph vx cA wsbc wph wps
      vx cA wsbc wph vx cA cV sbcgf.1 sbcgf imbi1d bitrd $.
  $}

  ${
    $d x ph $.
    $( Substitution for a variable not occurring in a wff does not affect it.
       Distinct variable form of ~ sbcgf .  (Contributed by Alan Sare,
       10-Nov-2012.) $)
    sbcg $p |- ( A e. V -> ( [. A / x ]. ph <-> ph ) ) $=
      wph vx cA cV wph vx nfv sbcgf $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x V $.  $d y W $.
    sbc2iegf.1 $e |- F/ x ps $.
    sbc2iegf.2 $e |- F/ y ps $.
    sbc2iegf.3 $e |- F/ x B e. W $.
    sbc2iegf.4 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by Mario Carneiro, 19-Dec-2013.) $)
    sbc2iegf $p |- ( ( A e. V /\ B e. W ) ->
            ( [. A / x ]. [. B / y ]. ph <-> ps ) ) $=
      cA cV wcel cB cW wcel wa wph vy cB wsbc wps vx cA cV cA cV wcel cB cW
      wcel simpl cB cW wcel vx cv cA wceq wph vy cB wsbc wps wb cA cV wcel cB
      cW wcel vx cv cA wceq wa wph wps vy cB cW cB cW wcel vx cv cA wceq simpl
      vx cv cA wceq vy cv cB wceq wph wps wb cB cW wcel sbc2iegf.4 adantll cB
      cW wcel vx cv cA wceq wa vy nfv wps vy wnf cB cW wcel vx cv cA wceq wa
      sbc2iegf.2 a1i sbciedf adantll cA cV wcel cB cW wcel vx cA cV wcel vx nfv
      sbc2iegf.3 nfan wps vx wnf cA cV wcel cB cW wcel wa sbc2iegf.1 a1i
      sbciedf $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y ps $.
    sbc2ie.1 $e |- A e. _V $.
    sbc2ie.2 $e |- B e. _V $.
    sbc2ie.3 $e |- ( ( x = A /\ y = B ) -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 16-Dec-2008.)  (Revised by Mario Carneiro,
       19-Dec-2013.) $)
    sbc2ie $p |- ( [. A / x ]. [. B / y ]. ph <-> ps ) $=
      cA cvv wcel cB cvv wcel wph vy cB wsbc vx cA wsbc wps wb sbc2ie.1
      sbc2ie.2 wph wps vx vy cA cB cvv cvv wps vx nfv wps vy nfv cB cvv wcel vx
      sbc2ie.2 nfth sbc2ie.3 sbc2iegf mp2an $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y ph $.  $d x y ch $.
    sbc2iedv.1 $e |- A e. _V $.
    sbc2iedv.2 $e |- B e. _V $.
    sbc2iedv.3 $e |- ( ph -> ( ( x = A /\ y = B ) -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by NM, 16-Dec-2008.)  (Proof shortened by Mario Carneiro,
       18-Oct-2016.) $)
    sbc2iedv $p |- ( ph -> ( [. A / x ]. [. B / y ]. ps <-> ch ) ) $=
      wph wps vy cB wsbc wch vx cA cvv cA cvv wcel wph sbc2iedv.1 a1i wph vx cv
      cA wceq wa wps wch vy cB cvv cB cvv wcel wph vx cv cA wceq wa sbc2iedv.2
      a1i wph vx cv cA wceq vy cv cB wceq wps wch wb sbc2iedv.3 impl sbcied
      sbcied $.
  $}

  ${
    $d x y z A $.  $d y z B $.  $d z C $.  $d x y z ps $.
    sbc3ie.1 $e |- A e. _V $.
    sbc3ie.2 $e |- B e. _V $.
    sbc3ie.3 $e |- C e. _V $.
    sbc3ie.4 $e |- ( ( x = A /\ y = B /\ z = C ) -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit class substitution.
       (Contributed by Mario Carneiro, 19-Jun-2014.)  (Revised by Mario
       Carneiro, 29-Dec-2014.) $)
    sbc3ie $p |- ( [. A / x ]. [. B / y ]. [. C / z ]. ph <-> ps ) $=
      wph vz cC wsbc wps vx vy cA cB sbc3ie.1 sbc3ie.2 vx cv cA wceq vy cv cB
      wceq wa wph wps vz cC cvv cC cvv wcel vx cv cA wceq vy cv cB wceq wa
      sbc3ie.3 a1i vx cv cA wceq vy cv cB wceq vz cv cC wceq wph wps wb
      sbc3ie.4 3expa sbcied sbc2ie $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d y V $.  $d x W $.
    $( Lemma for ~ sbccom .  (Contributed by NM, 14-Nov-2005.)  (Revised by
       Mario Carneiro, 18-Oct-2016.) $)
    sbccomlem $p |- ( [. A / x ]. [. B / y ]. ph
         <-> [. B / y ]. [. A / x ]. ph ) $=
      vy cv cB wceq wph wa vy wex vx cA wsbc vx cv cA wceq wph wa vx wex vy cB
      wsbc wph vy cB wsbc vx cA wsbc wph vx cA wsbc vy cB wsbc vx cv cA wceq vy
      cv cB wceq wph wa vy wex wa vx wex vy cv cB wceq vx cv cA wceq wph wa vx
      wex wa vy wex vy cv cB wceq wph wa vy wex vx cA wsbc vx cv cA wceq wph wa
      vx wex vy cB wsbc vx cv cA wceq vy cv cB wceq wph wa wa vy wex vx wex vx
      cv cA wceq vy cv cB wceq wph wa wa vx wex vy wex vx cv cA wceq vy cv cB
      wceq wph wa vy wex wa vx wex vy cv cB wceq vx cv cA wceq wph wa vx wex wa
      vy wex vx cv cA wceq vy cv cB wceq wph wa wa vx vy excom vx cv cA wceq vy
      cv cB wceq wph wa vx vy exdistr vx cv cA wceq vy cv cB wceq wph wa wa vx
      wex vy cv cB wceq vx cv cA wceq wph wa vx wex wa vy vx cv cA wceq vy cv
      cB wceq wph wa wa vx wex vy cv cB wceq vx cv cA wceq wph wa wa vx wex vy
      cv cB wceq vx cv cA wceq wph wa vx wex wa vx cv cA wceq vy cv cB wceq wph
      wa wa vy cv cB wceq vx cv cA wceq wph wa wa vx vx cv cA wceq vy cv cB
      wceq wph an12 exbii vy cv cB wceq vx cv cA wceq wph wa vx 19.42v bitri
      exbii 3bitr3i vy cv cB wceq wph wa vy wex vx cA sbc5 vx cv cA wceq wph wa
      vx wex vy cB sbc5 3bitr4i wph vy cB wsbc vy cv cB wceq wph wa vy wex vx
      cA wph vy cB sbc5 sbcbii wph vx cA wsbc vx cv cA wceq wph wa vx wex vy cB
      wph vx cA sbc5 sbcbii 3bitr4i $.
  $}

  ${
    $d w y z A $.  $d w x z B $.  $d w z ph $.  $d x y $.
    $( Commutative law for double class substitution.  (Contributed by NM,
       15-Nov-2005.)  (Proof shortened by Mario Carneiro, 18-Oct-2016.) $)
    sbccom $p |- ( [. A / x ]. [. B / y ]. ph
          <-> [. B / y ]. [. A / x ]. ph ) $=
      wph vy vw cv wsbc vw cB wsbc vx cA wsbc wph vx vz cv wsbc vz cA wsbc vy
      cB wsbc wph vy cB wsbc vx cA wsbc wph vx cA wsbc vy cB wsbc wph vy vw cv
      wsbc vw cB wsbc vx vz cv wsbc vz cA wsbc wph vx vz cv wsbc vz cA wsbc vy
      vw cv wsbc vw cB wsbc wph vy vw cv wsbc vw cB wsbc vx cA wsbc wph vx vz
      cv wsbc vz cA wsbc vy cB wsbc wph vx vz cv wsbc vy vw cv wsbc vw cB wsbc
      vz cA wsbc wph vx vz cv wsbc vy vw cv wsbc vz cA wsbc vw cB wsbc wph vy
      vw cv wsbc vw cB wsbc vx vz cv wsbc vz cA wsbc wph vx vz cv wsbc vz cA
      wsbc vy vw cv wsbc vw cB wsbc wph vx vz cv wsbc vy vw cv wsbc vz vw cA cB
      sbccomlem wph vx vz cv wsbc vy vw cv wsbc vw cB wsbc wph vy vw cv wsbc vw
      cB wsbc vx vz cv wsbc vz cA wph vx vz cv wsbc vy vw cv wsbc vw cB wsbc
      wph vy vw cv wsbc vx vz cv wsbc vw cB wsbc wph vy vw cv wsbc vw cB wsbc
      vx vz cv wsbc wph vx vz cv wsbc vy vw cv wsbc wph vy vw cv wsbc vx vz cv
      wsbc vw cB wph vy vx vw cv vz cv sbccomlem sbcbii wph vy vw cv wsbc vw vx
      cB vz cv sbccomlem bitri sbcbii wph vx vz cv wsbc vy vw cv wsbc vz cA
      wsbc wph vx vz cv wsbc vz cA wsbc vy vw cv wsbc vw cB wph vx vz cv wsbc
      vz vy cA vw cv sbccomlem sbcbii 3bitr3i wph vy vw cv wsbc vw cB wsbc vx
      vz cA sbcco wph vx vz cv wsbc vz cA wsbc vy vw cB sbcco 3bitr3i wph vy vw
      cv wsbc vw cB wsbc wph vy cB wsbc vx cA wph vy vw cB sbcco sbcbii wph vx
      vz cv wsbc vz cA wsbc wph vx cA wsbc vy cB wph vx vz cA sbcco sbcbii
      3bitr3i $.
  $}

  ${
    $d x y z $.  $d A z $.  $d B x z $.  $d V z $.  $d ph z $.
    $( Interchange class substitution and restricted quantifier.  (Contributed
       by NM, 1-Mar-2008.)  (Revised by David Abernethy, 22-Feb-2010.) $)
    sbcralt $p |- ( ( A e. V /\ F/_ y A ) ->
           ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) ) $=
      wph vy cB wral vx cA wsbc wph vy cB wral vx vz cv wsbc vz cA wsbc cA cV
      wcel vy cA wnfc wa wph vx cA wsbc vy cB wral wph vy cB wral vx vz cA
      sbcco cA cV wcel vy cA wnfc wa wph vy cB wral vx vz cv wsbc wph vx cA
      wsbc vy cB wral vz cA cV cA cV wcel vy cA wnfc simpl wph vy cB wral vx vz
      cv wsbc wph vx vz wsb vy cB wral cA cV wcel vy cA wnfc wa vz cv cA wceq
      wa wph vx cA wsbc vy cB wral wph vy cB wral vx vz cv wsbc wph vy cB wral
      vx vz wsb wph vx vz wsb vy cB wral wph vy cB wral vx vz sbsbc wph vy cB
      wral wph vx vz wsb vy cB wral vx vz wph vx vz wsb vx vy cB vx cB nfcv wph
      vx vz nfs1v nfral vx vz weq wph wph vx vz wsb vy cB wph vx vz sbequ12
      ralbidv sbie bitr3i vy cA wnfc vz cv cA wceq wph vx vz wsb vy cB wral wph
      vx cA wsbc vy cB wral wb cA cV wcel vy cA wnfc vz cv cA wceq wa wph vx vz
      wsb wph vx cA wsbc vy cB vy cA wnfc vz cv cA wceq vy vy cA nfnfc1 vy cA
      wnfc vy vz cv cA vy cA wnfc vy vz cv nfcvd vy cA wnfc id nfeqd nfan1 vz
      cv cA wceq wph vx vz wsb wph vx cA wsbc wb vy cA wnfc wph vx vz cA
      dfsbcq2 adantl ralbid adantll syl5bb sbcied syl5bbr $.

    $( Interchange class substitution and restricted existential quantifier.
       (Contributed by NM, 1-Mar-2008.)  (Proof shortened by Mario Carneiro,
       13-Oct-2016.) $)
    sbcrext $p |- ( ( A e. V /\ F/_ y A ) ->
          ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) ) $=
      cA cV wcel cA cvv wcel vy cA wnfc wph vy cB wrex vx cA wsbc wph vx cA
      wsbc vy cB wrex wb cA cV elex cA cvv wcel vy cA wnfc wa wph wn vy cB wral
      wn vx cA wsbc wph vx cA wsbc wn vy cB wral wn wph vy cB wrex vx cA wsbc
      wph vx cA wsbc vy cB wrex cA cvv wcel vy cA wnfc wa wph wn vy cB wral wn
      vx cA wsbc wph wn vy cB wral vx cA wsbc wn wph vx cA wsbc wn vy cB wral
      wn cA cvv wcel wph wn vy cB wral wn vx cA wsbc wph wn vy cB wral vx cA
      wsbc wn wb vy cA wnfc wph wn vy cB wral vx cA cvv sbcng adantr cA cvv
      wcel vy cA wnfc wa wph wn vy cB wral vx cA wsbc wph vx cA wsbc wn vy cB
      wral cA cvv wcel vy cA wnfc wa wph wn vy cB wral vx cA wsbc wph wn vx cA
      wsbc vy cB wral wph vx cA wsbc wn vy cB wral wph wn vx vy cA cB cvv
      sbcralt vy cA wnfc cA cvv wcel wph wn vx cA wsbc vy cB wral wph vx cA
      wsbc wn vy cB wral wb vy cA wnfc cA cvv wcel wa wph wn vx cA wsbc wph vx
      cA wsbc wn vy cB vy cA wnfc cA cvv wcel vy vy cA nfnfc1 vy cA wnfc vy cA
      cvv vy cA wnfc id vy cA wnfc vy cvv nfcvd nfeld nfan1 cA cvv wcel wph wn
      vx cA wsbc wph vx cA wsbc wn wb vy cA wnfc wph vx cA cvv sbcng adantl
      ralbid ancoms bitrd notbid bitrd wph vy cB wrex wph wn vy cB wral wn vx
      cA wph vy cB dfrex2 sbcbii wph vx cA wsbc vy cB dfrex2 3bitr4g sylan $.
  $}

  ${
    $d y z A $.  $d x B $.  $d x y z $.  $d ph z $.  $d B z $.
    $( Interchange class substitution and restricted quantifier.  (Contributed
       by NM, 15-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    sbcralg $p |- ( A e. V ->
                 ( [. A / x ]. A. y e. B ph <-> A. y e. B [. A / x ]. ph ) ) $=
      wph vy cB wral vx vz wsb wph vx vz wsb vy cB wral wph vy cB wral vx cA
      wsbc wph vx cA wsbc vy cB wral vz cA cV wph vy cB wral vx vz cA dfsbcq2
      vz cv cA wceq wph vx vz wsb wph vx cA wsbc vy cB wph vx vz cA dfsbcq2
      ralbidv wph vy cB wral wph vx vz wsb vy cB wral vx vz wph vx vz wsb vx vy
      cB vx cB nfcv wph vx vz nfs1v nfral vx vz weq wph wph vx vz wsb vy cB wph
      vx vz sbequ12 ralbidv sbie vtoclbg $.

    $( Interchange class substitution and restricted existential quantifier.
       (Contributed by NM, 15-Nov-2005.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    sbcrexg $p |- ( A e. V ->
                 ( [. A / x ]. E. y e. B ph <-> E. y e. B [. A / x ]. ph ) ) $=
      wph vy cB wrex vx vz wsb wph vx vz wsb vy cB wrex wph vy cB wrex vx cA
      wsbc wph vx cA wsbc vy cB wrex vz cA cV wph vy cB wrex vx vz cA dfsbcq2
      vz cv cA wceq wph vx vz wsb wph vx cA wsbc vy cB wph vx vz cA dfsbcq2
      rexbidv wph vy cB wrex wph vx vz wsb vy cB wrex vx vz wph vx vz wsb vx vy
      cB vx cB nfcv wph vx vz nfs1v nfrex vx vz weq wph wph vx vz wsb vy cB wph
      vx vz sbequ12 rexbidv sbie vtoclbg $.

    $( Interchange class substitution and restricted uniqueness quantifier.
       (Contributed by NM, 24-Feb-2013.) $)
    sbcreug $p |- ( A e. V ->
                 ( [. A / x ]. E! y e. B ph <-> E! y e. B [. A / x ]. ph ) ) $=
      wph vy cB wreu vx vz wsb wph vx vz wsb vy cB wreu wph vy cB wreu vx cA
      wsbc wph vx cA wsbc vy cB wreu vz cA cV wph vy cB wreu vx vz cA dfsbcq2
      vz cv cA wceq wph vx vz wsb wph vx cA wsbc vy cB wph vx vz cA dfsbcq2
      reubidv wph vy cB wreu wph vx vz wsb vy cB wreu vx vz wph vx vz wsb vx vy
      cB vx cB nfcv wph vx vz nfs1v nfreu vx vz weq wph wph vx vz wsb vy cB wph
      vx vz sbequ12 reubidv sbie vtoclbg $.
  $}

  ${
    $d y w A $.  $d w z B $.  $d w ph $.  $d x y $.  $d w x z $.
    sbcabel.1 $e |- F/_ x B $.
    $( Interchange class substitution and class abstraction.  (Contributed by
       NM, 5-Nov-2005.) $)
    sbcabel $p |- ( A e. V -> ( [. A / x ]. { y | ph } e. B <->
                  { y | [. A / x ]. ph } e. B ) ) $=
      cA cV wcel cA cvv wcel wph vy cab cB wcel vx cA wsbc wph vx cA wsbc vy
      cab cB wcel wb cA cV elex cA cvv wcel vw cv wph vy cab wceq vw cv cB wcel
      wa vw wex vx cA wsbc vw cv wph vx cA wsbc vy cab wceq vw cv cB wcel wa vw
      wex wph vy cab cB wcel vx cA wsbc wph vx cA wsbc vy cab cB wcel cA cvv
      wcel vw cv wph vy cab wceq vw cv cB wcel wa vw wex vx cA wsbc vw cv wph
      vy cab wceq vw cv cB wcel wa vx cA wsbc vw wex vw cv wph vx cA wsbc vy
      cab wceq vw cv cB wcel wa vw wex vw cv wph vy cab wceq vw cv cB wcel wa
      vw vx cA cvv sbcexg cA cvv wcel vw cv wph vy cab wceq vw cv cB wcel wa vx
      cA wsbc vw cv wph vx cA wsbc vy cab wceq vw cv cB wcel wa vw cA cvv wcel
      vw cv wph vy cab wceq vw cv cB wcel wa vx cA wsbc vw cv wph vy cab wceq
      vx cA wsbc vw cv cB wcel vx cA wsbc wa vw cv wph vx cA wsbc vy cab wceq
      vw cv cB wcel wa vw cv wph vy cab wceq vw cv cB wcel vx cA cvv sbcang cA
      cvv wcel vw cv wph vy cab wceq vx cA wsbc vw cv wph vx cA wsbc vy cab
      wceq vw cv cB wcel vx cA wsbc vw cv cB wcel cA cvv wcel vw cv wph vy cab
      wceq vx cA wsbc vy cv vw cv wcel wph vx cA wsbc wb vy wal vw cv wph vx cA
      wsbc vy cab wceq vw cv wph vy cab wceq vx cA wsbc vy cv vw cv wcel wph wb
      vy wal vx cA wsbc cA cvv wcel vy cv vw cv wcel wph vx cA wsbc wb vy wal
      vw cv wph vy cab wceq vy cv vw cv wcel wph wb vy wal vx cA wph vy vw cv
      abeq2 sbcbii cA cvv wcel vy cv vw cv wcel wph wb vy wal vx cA wsbc vy cv
      vw cv wcel wph wb vx cA wsbc vy wal vy cv vw cv wcel wph vx cA wsbc wb vy
      wal vy cv vw cv wcel wph wb vy vx cA cvv sbcalg cA cvv wcel vy cv vw cv
      wcel wph wb vx cA wsbc vy cv vw cv wcel wph vx cA wsbc wb vy cA cvv wcel
      vy cv vw cv wcel wph wb vx cA wsbc vy cv vw cv wcel vx cA wsbc wph vx cA
      wsbc wb vy cv vw cv wcel wph vx cA wsbc wb vy cv vw cv wcel wph vx cA cvv
      sbcbig cA cvv wcel vy cv vw cv wcel vx cA wsbc vy cv vw cv wcel wph vx cA
      wsbc vy cv vw cv wcel vx cA cvv sbcg bibi1d bitrd albidv bitrd syl5bb wph
      vx cA wsbc vy vw cv abeq2 syl6bbr vw cv cB wcel vx cA cvv vx vw cB
      sbcabel.1 nfcri sbcgf anbi12d bitrd exbidv bitrd wph vy cab cB wcel vw cv
      wph vy cab wceq vw cv cB wcel wa vw wex vx cA vw wph vy cab cB df-clel
      sbcbii vw wph vx cA wsbc vy cab cB df-clel 3bitr4g syl $.
  $}

  ${
    $d y A $.  $d x y B $.  $d y ph $.
    $( Restricted quantifier version of Axiom 4 of [Mendelson] p. 69.  This
       provides an axiom for a predicate calculus for a restricted domain.
       This theorem generalizes the unrestricted ~ stdpc4 and ~ spsbc .  See
       also ~ rspsbca and ~ rspcsbela .  (Contributed by NM, 17-Nov-2006.)
       (Proof shortened by Mario Carneiro, 13-Oct-2016.) $)
    rspsbc $p |- ( A e. B -> ( A. x e. B ph -> [. A / x ]. ph ) ) $=
      wph vx cB wral wph vx vy wsb vy cB wral cA cB wcel wph vx cA wsbc wph vx
      vy cB cbvralsv wph vx vy wsb wph vx cA wsbc vy cA cB wph vx vy cA dfsbcq2
      rspcv syl5bi $.

    $( Restricted quantifier version of Axiom 4 of [Mendelson] p. 69.
       (Contributed by NM, 14-Dec-2005.) $)
    rspsbca $p |- ( ( A e. B /\ A. x e. B ph ) -> [. A / x ]. ph ) $=
      cA cB wcel wph vx cB wral wph vx cA wsbc wph vx cA cB rspsbc imp $.

    $( Existence form of ~ rspsbca .  (Contributed by NM, 29-Feb-2008.)  (Proof
       shortened by Mario Carneiro, 13-Oct-2016.) $)
    rspesbca $p |- ( ( A e. B /\ [. A / x ]. ph ) -> E. x e. B ph ) $=
      cA cB wcel wph vx cA wsbc wa wph vx vy wsb vy cB wrex wph vx cB wrex wph
      vx vy wsb wph vx cA wsbc vy cA cB wph vx vy cA dfsbcq2 rspcev wph vx vy
      cB cbvrexsv sylibr $.

    $( Existence form of ~ spsbc .  (Contributed by Mario Carneiro,
       18-Nov-2016.) $)
    spesbc $p |- ( [. A / x ]. ph -> E. x ph ) $=
      wph vx cA wsbc wph vx cvv wrex wph vx wex cA cvv wcel wph vx cA wsbc wph
      vx cvv wrex wph vx cA sbcex wph vx cA cvv rspesbca mpancom wph vx rexv
      sylib $.

    spesbcd.1 $e |- ( ph -> [. A / x ]. ps ) $.
    $( form of ~ spsbc .  (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    spesbcd $p |- ( ph -> E. x ps ) $=
      wph wps vx cA wsbc wps vx wex spesbcd.1 wps vx cA spesbc syl $.
  $}

  ${
    $d x B $.
    sbcth2.1 $e |- ( x e. B -> ph ) $.
    $( A substitution into a theorem.  (Contributed by NM, 1-Mar-2008.)  (Proof
       shortened by Mario Carneiro, 13-Oct-2016.) $)
    sbcth2 $p |- ( A e. B -> [. A / x ]. ph ) $=
      cA cB wcel wph vx cB wral wph vx cA wsbc wph vx cB sbcth2.1 rgen wph vx
      cA cB rspsbc mpi $.
  $}

  ${
    ra5.1 $e |- F/ x ph $.
    $( Restricted quantifier version of Axiom 5 of [Mendelson] p. 69.  This is
       an axiom of a predicate calculus for a restricted domain.  Compare the
       unrestricted ~ stdpc5 .  (Contributed by NM, 16-Jan-2004.) $)
    ra5 $p |- ( A. x e. A ( ph -> ps ) -> ( ph -> A. x e. A ps ) ) $=
      wph wps wi vx cA wral wph vx cv cA wcel wps wi vx wal wps vx cA wral wph
      wps wi vx cA wral wph vx cv cA wcel wps wi wi vx wal wph vx cv cA wcel
      wps wi vx wal wi wph wps wi vx cA wral vx cv cA wcel wph wps wi wi vx wal
      wph vx cv cA wcel wps wi wi vx wal wph wps wi vx cA df-ral vx cv cA wcel
      wph wps wi wi wph vx cv cA wcel wps wi wi vx vx cv cA wcel wph wps bi2.04
      albii bitri wph vx cv cA wcel wps wi vx ra5.1 stdpc5 sylbi wps vx cA
      df-ral syl6ibr $.
  $}

  ${
    $d x y A $.
    rmo2.1 $e |- F/ y ph $.
    $( Alternate definition of restricted "at most one."  Note that
       ` E* x e. A ph ` is not equivalent to
       ` E. y e. A A. x e. A ( ph -> x = y ) ` (in analogy to ~ reu6 ); to see
       this, let ` A ` be the empty set.  However, one direction of this
       pattern holds; see ~ rmo2i .  (Contributed by NM, 17-Jun-2017.) $)
    rmo2 $p |- ( E* x e. A ph <-> E. y A. x e. A ( ph -> x = y ) ) $=
      wph vx cA wrmo vx cv cA wcel wph wa vx wmo vx cv cA wcel wph wa vx vy weq
      wi vx wal vy wex wph vx vy weq wi vx cA wral vy wex wph vx cA df-rmo vx
      cv cA wcel wph wa vx vy vx cv cA wcel wph vy vx cv cA wcel vy nfv rmo2.1
      nfan mo2 vx cv cA wcel wph wa vx vy weq wi vx wal wph vx vy weq wi vx cA
      wral vy vx cv cA wcel wph wa vx vy weq wi vx wal vx cv cA wcel wph vx vy
      weq wi wi vx wal wph vx vy weq wi vx cA wral vx cv cA wcel wph wa vx vy
      weq wi vx cv cA wcel wph vx vy weq wi wi vx vx cv cA wcel wph vx vy weq
      impexp albii wph vx vy weq wi vx cA df-ral bitr4i exbii 3bitri $.

    $( Condition implying restricted "at most one."  (Contributed by NM,
       17-Jun-2017.) $)
    rmo2i $p |- ( E. y e. A A. x e. A ( ph -> x = y ) -> E* x e. A ph ) $=
      wph vx vy weq wi vx cA wral vy cA wrex wph vx vy weq wi vx cA wral vy wex
      wph vx cA wrmo wph vx vy weq wi vx cA wral vy cA rexex wph vx vy cA
      rmo2.1 rmo2 sylibr $.

    $( Restricted "at most one" using explicit substitution.  (Contributed by
       NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.) $)
    rmo3 $p |- ( E* x e. A ph <->
               A. x e. A A. y e. A ( ( ph /\ [ y / x ] ph ) -> x = y ) ) $=
      wph vx cA wrmo vx cv cA wcel wph wa vx wmo wph wph vx vy wsb wa vx vy weq
      wi vy cA wral vx cA wral wph vx cA df-rmo vx cv cA wcel wph wa vx cv cA
      wcel wph wa vx vy wsb wa vx vy weq wi vy wal vx wal vx cv cA wcel wph wph
      vx vy wsb wa vx vy weq wi vy cA wral wi vx wal vx cv cA wcel wph wa vx
      wmo wph wph vx vy wsb wa vx vy weq wi vy cA wral vx cA wral vx cv cA wcel
      wph wa vx cv cA wcel wph wa vx vy wsb wa vx vy weq wi vy wal vx cv cA
      wcel wph wph vx vy wsb wa vx vy weq wi vy cA wral wi vx vx cv cA wcel wph
      wa vx cv cA wcel wph wa vx vy wsb wa vx vy weq wi vy wal vy cv cA wcel vx
      cv cA wcel wph wph vx vy wsb wa vx vy weq wi wi wi vy wal vx cv cA wcel
      wph wph vx vy wsb wa vx vy weq wi wi vy cA wral vx cv cA wcel wph wph vx
      vy wsb wa vx vy weq wi vy cA wral wi vx cv cA wcel wph wa vx cv cA wcel
      wph wa vx vy wsb wa vx vy weq wi vy cv cA wcel vx cv cA wcel wph wph vx
      vy wsb wa vx vy weq wi wi wi vy vx cv cA wcel wph wa vx cv cA wcel wph wa
      vx vy wsb wa vx vy weq wi vy cv cA wcel vx cv cA wcel wa wph wph vx vy
      wsb wa wa vx vy weq wi vy cv cA wcel vx cv cA wcel wa wph wph vx vy wsb
      wa vx vy weq wi wi vy cv cA wcel vx cv cA wcel wph wph vx vy wsb wa vx vy
      weq wi wi wi vx cv cA wcel wph wa vx cv cA wcel wph wa vx vy wsb wa vy cv
      cA wcel vx cv cA wcel wa wph wph vx vy wsb wa wa vx vy weq vx cv cA wcel
      wph wa vx cv cA wcel wph wa vx vy wsb wa vx cv cA wcel wph wa vy cv cA
      wcel wph vx vy wsb wa wa vx cv cA wcel vy cv cA wcel wa wph wph vx vy wsb
      wa wa vy cv cA wcel vx cv cA wcel wa wph wph vx vy wsb wa wa vx cv cA
      wcel wph wa vx vy wsb vy cv cA wcel wph vx vy wsb wa vx cv cA wcel wph wa
      vx cv cA wcel wph wa vx vy wsb vx cv cA wcel vx vy wsb wph vx vy wsb wa
      vy cv cA wcel wph vx vy wsb wa vx cv cA wcel wph vx vy sban vx cv cA wcel
      vx vy wsb vy cv cA wcel wph vx vy wsb vy vx cA clelsb3 anbi1i bitri
      anbi2i vx cv cA wcel wph vy cv cA wcel wph vx vy wsb an4 vx cv cA wcel vy
      cv cA wcel wa vy cv cA wcel vx cv cA wcel wa wph wph vx vy wsb wa vx cv
      cA wcel vy cv cA wcel ancom anbi1i 3bitri imbi1i vy cv cA wcel vx cv cA
      wcel wa wph wph vx vy wsb wa vx vy weq impexp vy cv cA wcel vx cv cA wcel
      wph wph vx vy wsb wa vx vy weq wi impexp 3bitri albii vx cv cA wcel wph
      wph vx vy wsb wa vx vy weq wi wi vy cA df-ral vx cv cA wcel wph wph vx vy
      wsb wa vx vy weq wi vy cA r19.21v 3bitr2i albii vx cv cA wcel wph wa vx
      vy vx cv cA wcel wph vy vx cv cA wcel vy nfv rmo2.1 nfan mo3 wph wph vx
      vy wsb wa vx vy weq wi vy cA wral vx cA df-ral 3bitr4i bitri $.
  $}

  ${
    $d x y A $.  $d x y B $.  $d x y C $.  $d y ph $.  $d x y ps $.  $d x ch $.
    rmoi.b $e |- ( x = B -> ( ph <-> ps ) ) $.
    rmoi.c $e |- ( x = C -> ( ph <-> ch ) ) $.
    $( Consequence of "at most one", using implicit substitution.  (Contributed
       by NM, 2-Jan-2015.)  (Revised by NM, 16-Jun-2017.) $)
    rmob $p |- ( ( E* x e. A ph /\ ( B e. A /\ ps ) ) ->
        ( B = C <-> ( C e. A /\ ch ) ) ) $=
      wph vx cA wrmo vx cv cA wcel wph wa vx wmo cB cA wcel wps wa cB cC wceq
      cC cA wcel wch wa wb wph vx cA df-rmo vx cv cA wcel wph wa vx wmo cB cA
      wcel wps wa wa cC cA wcel cB cC wceq cC cA wcel wch wa vx cv cA wcel wph
      wa vx wmo cB cA wcel wps wa wa cB cA wcel cB cC wceq cC cA wcel vx cv cA
      wcel wph wa vx wmo cB cA wcel wps simprl cB cC cA eleq1 syl5ibcom cC cA
      wcel wch wa cC cA wcel wi vx cv cA wcel wph wa vx wmo cB cA wcel wps wa
      wa cC cA wcel wch simpl a1i vx cv cA wcel wph wa vx wmo cB cA wcel wps wa
      wa cC cA wcel cB cC wceq cC cA wcel wch wa wb vx cv cA wcel wph wa vx wmo
      cB cA wcel wps wa wa cC cA wcel wa cB cA wcel cC cA wcel vx cv cA wcel
      wph wa vx wmo cB cA wcel wps cB cC wceq cC cA wcel wch wa wb vx cv cA
      wcel wph wa vx wmo cB cA wcel wps cC cA wcel simplrl vx cv cA wcel wph wa
      vx wmo cB cA wcel wps wa wa cC cA wcel simpr vx cv cA wcel wph wa vx wmo
      cB cA wcel wps wa cC cA wcel simpll vx cv cA wcel wph wa vx wmo cB cA
      wcel wps cC cA wcel simplrl vx cv cA wcel wph wa vx wmo cB cA wcel wps cC
      cA wcel simplrr vx cv cA wcel wph wa cB cA wcel wps wa cC cA wcel wch wa
      vx cB cC cA cA vx cv cB wceq vx cv cA wcel cB cA wcel wph wps vx cv cB cA
      eleq1 rmoi.b anbi12d vx cv cC wceq vx cv cA wcel cC cA wcel wph wch vx cv
      cC cA eleq1 rmoi.c anbi12d mob syl212anc ex pm5.21ndd sylanb $.

    $( Consequence of "at most one", using implicit substitution.  (Contributed
       by NM, 4-Nov-2012.)  (Revised by NM, 16-Jun-2017.) $)
    rmoi $p |- ( ( E* x e. A ph
          /\ ( B e. A /\ ps ) /\ ( C e. A /\ ch ) ) -> B = C ) $=
      wph vx cA wrmo cB cA wcel wps wa cB cC wceq cC cA wcel wch wa wph wps wch
      vx cA cB cC rmoi.b rmoi.c rmob biimp3ar $.
  $}


