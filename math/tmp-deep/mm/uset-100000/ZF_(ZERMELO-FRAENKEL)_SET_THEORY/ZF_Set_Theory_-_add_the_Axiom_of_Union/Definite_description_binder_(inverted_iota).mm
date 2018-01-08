
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_add_the_Axiom_of_Union/Relations.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Definite description binder (inverted iota)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c iota $.
  $( Extend class notation with Russell's definition description binder
     (inverted iota). $)
  cio $a class ( iota x ph ) $.

  ${
    $d w x z $.  $d ph w z $.  $d ph w y $.  $d x y $.
    $( Soundness justification theorem for ~ df-iota .  (Contributed by Andrew
       Salmon, 29-Jun-2011.) $)
    iotajust $p |- U. { y | { x | ph } = { y } } =
       U. { z | { x | ph } = { z } } $=
      wph vx cab vy cv csn wceq vy cab wph vx cab vz cv csn wceq vz cab wph vx
      cab vy cv csn wceq vy cab wph vx cab vw cv csn wceq vw cab wph vx cab vz
      cv csn wceq vz cab wph vx cab vy cv csn wceq wph vx cab vw cv csn wceq vy
      vw vy cv vw cv wceq vy cv csn vw cv csn wph vx cab vy cv vw cv sneq
      eqeq2d cbvabv wph vx cab vw cv csn wceq wph vx cab vz cv csn wceq vw vz
      vw cv vz cv wceq vw cv csn vz cv csn wph vx cab vw cv vz cv sneq eqeq2d
      cbvabv eqtri unieqi $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( Define Russell's definition description binder, which can be read as
       "the unique ` x ` such that ` ph ` ," where ` ph ` ordinarily contains
       ` x ` as a free variable.  Our definition is meaningful only when there
       is exactly one ` x ` such that ` ph ` is true (see ~ iotaval );
       otherwise, it evaluates to the empty set (see ~ iotanul ).  Russell used
       the inverted iota symbol ` iota ` to represent the binder.

       Sometimes proofs need to expand an iota-based definition.  That is,
       given "X = the x for which ... x ... x ..." holds, the proof needs to
       get to "...  X ...  X ...".  A general strategy to do this is to use
       ~ riotacl2 (or ~ iotacl for unbounded iota), as demonstrated in the
       proof of ~ supub .  This can be easier than applying ~ riotasbc or a
       version that applies an explicit substitution, because substituting an
       iota into its own property always has a bound variable clash which must
       be first renamed or else guarded with NF.

       (Contributed by Andrew Salmon, 30-Jun-2011.) $)
    df-iota $a |- ( iota x ph ) = U. { y | { x | ph } = { y } } $.
  $}

  ${
    $d y x $.  $d y ph $.
    $( Alternate definition for descriptions.  Definition 8.18 in [Quine]
       p. 56.  (Contributed by Andrew Salmon, 30-Jun-2011.) $)
    dfiota2 $p |- ( iota x ph ) = U. { y | A. x ( ph <-> x = y ) } $=
      wph vx cio wph vx cab vy cv csn wceq vy cab cuni wph vx cv vy cv wceq wb
      vx wal vy cab cuni wph vx vy df-iota wph vx cab vy cv csn wceq vy cab wph
      vx cv vy cv wceq wb vx wal vy cab wph vx cab vy cv csn wceq wph vx cv vy
      cv wceq wb vx wal vy wph vx cab vy cv csn wceq wph vx cab vx cv vy cv
      wceq vx cab wceq wph vx cv vy cv wceq wb vx wal vy cv csn vx cv vy cv
      wceq vx cab wph vx cab vx vy cv df-sn eqeq2i wph vx cv vy cv wceq vx abbi
      bitr4i abbii unieqi eqtri $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( Bound-variable hypothesis builder for the ` iota ` class.  (Contributed
       by Andrew Salmon, 11-Jul-2011.)  (Revised by Mario Carneiro,
       15-Oct-2016.) $)
    nfiota1 $p |- F/_ x ( iota x ph ) $=
      vx wph vx cio wph vx cv vy cv wceq wb vx wal vy cab cuni wph vx vy
      dfiota2 vx wph vx cv vy cv wceq wb vx wal vy cab wph vx cv vy cv wceq wb
      vx vy nfaba1 nfuni nfcxfr $.
  $}

  ${
    $d z ps $.  $d z ph $.  $d x z $.  $d y z $.
    nfiotad.1 $e |- F/ y ph $.
    nfiotad.2 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfiota .  (Contributed by NM, 18-Feb-2013.) $)
    nfiotad $p |- ( ph -> F/_ x ( iota y ps ) ) $=
      wph vx wps vy cio wps vy cv vz cv wceq wb vy wal vz cab cuni wps vy vz
      dfiota2 wph vx wps vy cv vz cv wceq wb vy wal vz cab wph wps vy cv vz cv
      wceq wb vy wal vx vz wph vz nfv wph wps vy cv vz cv wceq wb vx vy
      nfiotad.1 wph vx cv vy cv wceq vx wal wn wa wps vy cv vz cv wceq vx wph
      wps vx wnf vx cv vy cv wceq vx wal wn nfiotad.2 adantr wph vx cv vy cv
      wceq vx wal wn wa vx vy cv vz cv vx cv vy cv wceq vx wal wn vx vy cv wnfc
      wph vx vy nfcvf adantl wph vx cv vy cv wceq vx wal wn wa vx vz cv nfcvd
      nfeqd nfbid nfald2 nfabd nfunid nfcxfrd $.
  $}

  ${
    $d w z ph $.  $d w x z $.  $d w y z $.
    nfiota.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for the ` iota ` class.  (Contributed
       by NM, 23-Aug-2011.) $)
    nfiota $p |- F/_ x ( iota y ph ) $=
      vx wph vy cio wnfc wtru wph vx vy vy nftru wph vx wnf wtru nfiota.1 a1i
      nfiotad trud $.
  $}

  ${
    $d z w x $.  $d z w y $.  $d z w ph $.  $d z w ps $.
    cbviota.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    cbviota.2 $e |- F/ y ph $.
    cbviota.3 $e |- F/ x ps $.
    $( Change bound variables in a description binder.  (Contributed by Andrew
       Salmon, 1-Aug-2011.) $)
    cbviota $p |- ( iota x ph ) = ( iota y ps ) $=
      wph vx cv vw cv wceq wb vx wal vw cab cuni wps vy cv vw cv wceq wb vy wal
      vw cab cuni wph vx cio wps vy cio wph vx cv vw cv wceq wb vx wal vw cab
      wps vy cv vw cv wceq wb vy wal vw cab wph vx cv vw cv wceq wb vx wal wps
      vy cv vw cv wceq wb vy wal vw wph vx cv vw cv wceq wb vx wal wph vx vz
      wsb vz cv vw cv wceq wb vz wal wps vy cv vw cv wceq wb vy wal wph vx cv
      vw cv wceq wb wph vx vz wsb vz cv vw cv wceq wb vx vz wph vx cv vw cv
      wceq wb vz nfv wph vx vz wsb vz cv vw cv wceq vx wph vx vz nfs1v vz cv vw
      cv wceq vx nfv nfbi vx cv vz cv wceq wph wph vx vz wsb vx cv vw cv wceq
      vz cv vw cv wceq wph vx vz sbequ12 vx vz vw equequ1 bibi12d cbval wph vx
      vz wsb vz cv vw cv wceq wb wps vy cv vw cv wceq wb vz vy wph vx vz wsb vz
      cv vw cv wceq vy wph vx vz vy cbviota.2 nfsb vz cv vw cv wceq vy nfv nfbi
      wps vy cv vw cv wceq wb vz nfv vz cv vy cv wceq wph vx vz wsb wps vz cv
      vw cv wceq vy cv vw cv wceq vz cv vy cv wceq wph vx vz wsb wph vx vy wsb
      wps wph vz vy vx sbequ wph wps vx vy cbviota.3 cbviota.1 sbie syl6bb vz
      vy vw equequ1 bibi12d cbval bitri abbii unieqi wph vx vw dfiota2 wps vy
      vw dfiota2 3eqtr4i $.
  $}

  ${
    $d ph y $.  $d ps x $.
    cbviotav.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change bound variables in a description binder.  (Contributed by Andrew
       Salmon, 1-Aug-2011.) $)
    cbviotav $p |- ( iota x ph ) = ( iota y ps ) $=
      wph wps vx vy cbviotav.1 wph vy nfv wps vx nfv cbviota $.
  $}

  ${
    $d w z ph $.  $d w z x $.  $d w z y $.
    sb8iota.1 $e |- F/ y ph $.
    $( Variable substitution in description binder.  Compare ~ sb8eu .
       (Contributed by NM, 18-Mar-2013.) $)
    sb8iota $p |- ( iota x ph ) = ( iota y [ y / x ] ph ) $=
      wph vx cv vz cv wceq wb vx wal vz cab cuni wph vx vy wsb vy cv vz cv wceq
      wb vy wal vz cab cuni wph vx cio wph vx vy wsb vy cio wph vx cv vz cv
      wceq wb vx wal vz cab wph vx vy wsb vy cv vz cv wceq wb vy wal vz cab wph
      vx cv vz cv wceq wb vx wal wph vx vy wsb vy cv vz cv wceq wb vy wal vz
      wph vx cv vz cv wceq wb vx wal wph vx cv vz cv wceq wb vx vw wsb vw wal
      wph vx cv vz cv wceq wb vx vy wsb vy wal wph vx vy wsb vy cv vz cv wceq
      wb vy wal wph vx cv vz cv wceq wb vx vw wph vx cv vz cv wceq wb vw nfv
      sb8 wph vx cv vz cv wceq wb vx vw wsb wph vx cv vz cv wceq wb vx vy wsb
      vw vy wph vx cv vz cv wceq wb vx vw wsb wph vx vw wsb vx cv vz cv wceq vx
      vw wsb wb vy wph vx cv vz cv wceq vx vw sbbi wph vx vw wsb vx cv vz cv
      wceq vx vw wsb vy wph vx vw vy sb8iota.1 nfsb vx cv vz cv wceq vx vw wsb
      vw cv vz cv wceq vy vw vx vz cv eqsb3 vw cv vz cv wceq vy nfv nfxfr nfbi
      nfxfr wph vx cv vz cv wceq wb vx vy wsb vw nfv wph vx cv vz cv wceq wb vw
      vy vx sbequ cbval wph vx cv vz cv wceq wb vx vy wsb wph vx vy wsb vy cv
      vz cv wceq wb vy vx cv vz cv wceq vy cv vz cv wceq wph vx vy vy vx vz
      equsb3 sblbis albii 3bitri abbii unieqi wph vx vz dfiota2 wph vx vy wsb
      vy vz dfiota2 3eqtr4i $.
  $}

  ${
    $d y z $.  $d x z $.  $d ph z $.
    $( Equality theorem for descriptions.  (Contributed by Andrew Salmon,
       30-Jun-2011.) $)
    iotaeq $p |- ( A. x x = y -> ( iota x ph ) = ( iota y ph ) ) $=
      vx cv vy cv wceq vx wal wph vx cab vz cv csn wceq vz cab cuni wph vy cab
      vz cv csn wceq vz cab cuni wph vx cio wph vy cio vx cv vy cv wceq vx wal
      wph vx cab vz cv csn wceq vz cab wph vy cab vz cv csn wceq vz cab vx cv
      vy cv wceq vx wal wph vx cab vz cv csn wceq wph vy cab vz cv csn wceq vz
      vx cv vy cv wceq vx wal wph vx cab wph vy cab vz cv csn vx cv vy cv wceq
      vx wal vz wph vx cab wph vy cab vx cv vy cv wceq vx wal wph vx vz wsb wph
      vy vz wsb vz cv wph vx cab wcel vz cv wph vy cab wcel wph vx vy vz drsb1
      wph vz vx df-clab wph vz vy df-clab 3bitr4g eqrdv eqeq1d abbidv unieqd
      wph vx vz df-iota wph vy vz df-iota 3eqtr4g $.
  $}

  ${
    $d ph z $.  $d ps z $.  $d x y z $.
    $( Equivalence theorem for descriptions.  (Contributed by Andrew Salmon,
       30-Jun-2011.) $)
    iotabi $p |- ( A. x ( ph <-> ps ) -> ( iota x ph ) = ( iota x ps ) ) $=
      wph wps wb vx wal wph vx cab vz cv csn wceq vz cab cuni wps vx cab vz cv
      csn wceq vz cab cuni wph vx cio wps vx cio wph wps wb vx wal wph vx cab
      vz cv csn wceq vz cab wps vx cab vz cv csn wceq vz cab wph wps wb vx wal
      wph vx cab vz cv csn wceq wps vx cab vz cv csn wceq vz wph wps wb vx wal
      wph vx cab wps vx cab vz cv csn wph wps wb vx wal wph vx cab wps vx cab
      wceq wph wps vx abbi biimpi eqeq1d abbidv unieqd wph vx vz df-iota wps vx
      vz df-iota 3eqtr4g $.

    $( Part of Theorem 8.17 in [Quine] p. 56.  This theorem serves as a lemma
       for the fundamental property of iota.  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)
    uniabio $p |- ( A. x ( ph <-> x = y ) -> U. { x | ph } = y ) $=
      wph vx cv vy cv wceq wb vx wal wph vx cab cuni vy cv csn cuni vy cv wph
      vx cv vy cv wceq wb vx wal wph vx cab vy cv csn wph vx cv vy cv wceq wb
      vx wal wph vx cab vx cv vy cv wceq vx cab vy cv csn wph vx cv vy cv wceq
      wb vx wal wph vx cab vx cv vy cv wceq vx cab wceq wph vx cv vy cv wceq vx
      abbi biimpi vx vy cv df-sn syl6eqr unieqd vy cv vy vex unisn syl6eq $.

    $( Theorem 8.19 in [Quine] p. 57.  This theorem is the fundamental property
       of iota.  (Contributed by Andrew Salmon, 11-Jul-2011.) $)
    iotaval $p |- ( A. x ( ph <-> x = y ) -> ( iota x ph ) = y ) $=
      wph vx cv vy cv wceq wb vx wal wph vx cio wph vx cv vz cv wceq wb vx wal
      vz cab cuni vy cv wph vx vz dfiota2 wph vx cv vy cv wceq wb vx wal wph vx
      cv vz cv wceq wb vx wal vz cv vy cv wceq wb vz wal wph vx cv vz cv wceq
      wb vx wal vz cab cuni vy cv wceq wph vx cv vy cv wceq wb vx wal wph vx cv
      vz cv wceq wb vx wal vz cv vy cv wceq wb vz wph vx cv vy cv wceq wb vx
      wal wph vx cv vz cv wceq wb vx wal vz cv vy cv wceq wph vx cv vy cv wceq
      wb vx wal wph vx cv vz cv wceq wb vx wal vz cv vy cv wceq vy cv cvv wcel
      wph vx cv vy cv wceq wb vx wal wph vx cv vz cv wceq wb vx wal wa vz cv vy
      cv wceq wi vy vex vy cv cvv wcel wph vx cv vy cv wceq wb vx wal wph vx cv
      vz cv wceq wb vx wal wa vy cv vz cv wceq vz cv vy cv wceq wph vx vy cv vz
      cv cvv sbeqalb vy vz equcomi syl6 ax-mp ex vz cv vy cv wceq wph vx cv vy
      cv wceq wb vx wal wph vx cv vz cv wceq wb vx wal vz cv vy cv wceq wph vx
      cv vy cv wceq wb wph vx cv vz cv wceq wb vx vz cv vy cv wceq wph vx cv vy
      cv wceq wb wph vx cv vz cv wceq wb vz cv vy cv wceq vx cv vy cv wceq vx
      cv vz cv wceq wph vx cv vy cv wceq vx cv vz cv wceq wb vy cv vz cv vy vz
      vx equequ2 eqcoms bibi2d biimpd alimdv com12 impbid alrimiv wph vx cv vz
      cv wceq wb vx wal vz vy uniabio syl syl5eq $.

    $( Equivalence between two different forms of ` iota ` .  (Contributed by
       Andrew Salmon, 12-Jul-2011.) $)
    iotauni $p |- ( E! x ph -> ( iota x ph ) = U. { x | ph } ) $=
      wph vx weu wph vx cv vz cv wceq wb vx wal vz wex wph vx cio wph vx cab
      cuni wceq wph vx vz df-eu wph vx cv vz cv wceq wb vx wal wph vx cio wph
      vx cab cuni wceq vz wph vx cv vz cv wceq wb vx wal wph vx cio vz cv wph
      vx cab cuni wph vx vz iotaval wph vx vz uniabio eqtr4d exlimiv sylbi $.

    $( Equivalence between two different forms of ` iota ` .  (Contributed by
       Mario Carneiro, 24-Dec-2016.) $)
    iotaint $p |- ( E! x ph -> ( iota x ph ) = |^| { x | ph } ) $=
      wph vx weu wph vx cio wph vx cab cuni wph vx cab cint wph vx iotauni wph
      vx weu wph vx cab cuni wph vx cab cint wceq wph vx uniintab biimpi eqtrd
      $.

    $( Property of iota.  (Contributed by NM, 23-Aug-2011.)  (Revised by Mario
       Carneiro, 23-Dec-2016.) $)
    iota1 $p |- ( E! x ph -> ( ph <-> ( iota x ph ) = x ) ) $=
      wph vx weu wph vx cv vz cv wceq wb vx wal vz wex wph wph vx cio vx cv
      wceq wb wph vx vz df-eu wph vx cv vz cv wceq wb vx wal wph wph vx cio vx
      cv wceq wb vz wph vx cv vz cv wceq wb vx wal wph vx cv wph vx cio wceq
      wph vx cio vx cv wceq wph vx cv vz cv wceq wb vx wal wph vx cv vz cv wceq
      vx cv wph vx cio wceq wph vx cv vz cv wceq wb vx sp wph vx cv vz cv wceq
      wb vx wal wph vx cio vz cv vx cv wph vx vz iotaval eqeq2d bitr4d vx cv
      wph vx cio eqcom syl6bb exlimiv sylbi $.

    $( Theorem 8.22 in [Quine] p. 57.  This theorem is the result if there
       isn't exactly one ` x ` that satisfies ` ph ` .  (Contributed by Andrew
       Salmon, 11-Jul-2011.) $)
    iotanul $p |- ( -. E! x ph -> ( iota x ph ) = (/) ) $=
      wph vx weu wph vx cv vz cv wceq wb vx wal vz wex wph vx cio c0 wceq wph
      vx vz df-eu wph vx cv vz cv wceq wb vx wal vz wex wn wph vx cio wph vx cv
      vz cv wceq wb vx wal vz cab cuni c0 wph vx vz dfiota2 wph vx cv vz cv
      wceq wb vx wal vz wex wn wph vx cv vz cv wceq wb vx wal vz cab cuni c0
      cuni c0 wph vx cv vz cv wceq wb vx wal vz wex wn wph vx cv vz cv wceq wb
      vx wal vz cab c0 wph vx cv vz cv wceq wb vx wal vz wex wn wph vx cv vz cv
      wceq wb vx wal wn vz wal wph vx cv vz cv wceq wb vx wal vz cab c0 wceq
      wph vx cv vz cv wceq wb vx wal vz alnex wph vx cv vz cv wceq wb vx wal wn
      vz wal wph vx cv vz cv wceq wb vx wal vz cab vz cv vz cv wceq wn vz cab
      c0 wph vx cv vz cv wceq wb vx wal wn vz wal wph vx cv vz cv wceq wb vx
      wal vz cv vz cv wceq wn wb vz wal wph vx cv vz cv wceq wb vx wal vz cab
      vz cv vz cv wceq wn vz cab wceq wph vx cv vz cv wceq wb vx wal wn wph vx
      cv vz cv wceq wb vx wal vz cv vz cv wceq wn wb vz wph vx cv vz cv wceq wb
      vx wal wn vz cv vz cv wceq wph vx cv vz cv wceq wb vx wal wph vx cv vz cv
      wceq wb vx wal wn vz cv vz cv wceq wph vx cv vz cv wceq wb vx wal wn wph
      vx cv vz cv wceq wb vx wal wn vz cv vz cv wceq ax-1 wph vx cv vz cv wceq
      wb vx wal wn vz cv eqidd impbid1 con2bid alimi wph vx cv vz cv wceq wb vx
      wal vz cv vz cv wceq wn vz abbi sylib vz dfnul2 syl6eqr sylbir unieqd
      uni0 syl6eq syl5eq sylnbi $.

    $( The ` iota ` class is a subset of the union of all elements satisfying
       ` ph ` .  (Contributed by Mario Carneiro, 24-Dec-2016.) $)
    iotassuni $p |- ( iota x ph ) C_ U. { x | ph } $=
      wph vx weu wph vx cio wph vx cab cuni wss wph vx weu wph vx cio wph vx
      cab cuni wceq wph vx cio wph vx cab cuni wss wph vx iotauni wph vx cio
      wph vx cab cuni eqimss syl wph vx weu wn wph vx cio wph vx cab cuni wss
      c0 wph vx cab cuni wss wph vx cab cuni 0ss wph vx weu wn wph vx cio c0
      wph vx cab cuni wph vx iotanul sseq1d mpbiri pm2.61i $.

    $( Theorem 8.23 in [Quine] p. 58.  This theorem proves the existence of the
       ` iota ` class under our definition.  (Contributed by Andrew Salmon,
       11-Jul-2011.) $)
    iotaex $p |- ( iota x ph ) e. _V $=
      wph vx weu wph vx cio cvv wcel wph vx cv vz cv wceq wb vx wal vz wex vz
      cv wph vx cio wceq vz wex wph vx weu wph vx cio cvv wcel wph vx cv vz cv
      wceq wb vx wal vz cv wph vx cio wceq vz wph vx cv vz cv wceq wb vx wal
      wph vx cio vz cv wph vx vz iotaval eqcomd eximi wph vx vz df-eu vz wph vx
      cio isset 3imtr4i wph vx weu wn wph vx cio c0 cvv wph vx iotanul 0ex
      syl6eqel pm2.61i $.

    $( Theorem *14.22 in [WhiteheadRussell] p. 190.  (Contributed by Andrew
       Salmon, 12-Jul-2011.) $)
    iota4 $p |- ( E! x ph -> [. ( iota x ph ) / x ]. ph ) $=
      wph vx weu wph vx vz weq wb vx wal vz wex wph vx wph vx cio wsbc wph vx
      vz df-eu wph vx vz weq wb vx wal wph vx wph vx cio wsbc vz wph vx vz weq
      wb vx wal wph vx vz wsb wph vx wph vx cio wsbc wph vx vz weq wb vx wal vx
      vz weq wph wi vx wal wph vx vz wsb wph vx vz weq wb vx vz weq wph wi vx
      wph vx vz weq bi2 alimi wph vx vz sb2 syl wph vx vz weq wb vx wal vz cv
      wph vx cio wceq wph vx vz wsb wph vx wph vx cio wsbc wb wph vx vz weq wb
      vx wal wph vx cio vz cv wph vx vz iotaval eqcomd wph vx vz wph vx cio
      dfsbcq2 syl mpbid exlimiv sylbi $.
  $}

  $( Theorem *14.23 in [WhiteheadRussell] p. 191.  (Contributed by Andrew
     Salmon, 12-Jul-2011.) $)
  iota4an $p |- ( E! x ( ph /\ ps )
            -> [. ( iota x ( ph /\ ps ) ) / x ]. ph ) $=
    wph wps wa vx weu wph wps wa vx wph wps wa vx cio wsbc wph vx wph wps wa vx
    cio wsbc wph wps wa vx iota4 wph wps wa wph wi vx wph wps wa vx cio wsbc
    wph wps wa vx wph wps wa vx cio wsbc wph vx wph wps wa vx cio wsbc wi wph
    wps wa vx cio cvv wcel wph wps wa wph wi vx wph wps wa vx cio wsbc wph wps
    wa vx iotaex wph wps wa wph wi vx wph wps wa vx cio cvv wph wps simpl sbcth
    ax-mp wph wps wa vx cio cvv wcel wph wps wa wph wi vx wph wps wa vx cio
    wsbc wph wps wa vx wph wps wa vx cio wsbc wph vx wph wps wa vx cio wsbc wi
    wb wph wps wa vx iotaex wph wps wa wph vx wph wps wa vx cio cvv sbcimg
    ax-mp mpbi syl $.

  ${
    $d x y A $.  $d x V $.  $d x ph $.  $d y ps $.
    iota5.1 $e |- ( ( ph /\ A e. V ) -> ( ps <-> x = A ) ) $.
    $( A method for computing iota.  (Contributed by NM, 17-Sep-2013.) $)
    iota5 $p |- ( ( ph /\ A e. V ) -> ( iota x ps ) = A ) $=
      wph cA cV wcel wa wps vx cv cA wceq wb vx wal wps vx cio cA wceq wph cA
      cV wcel wa wps vx cv cA wceq wb vx iota5.1 alrimiv cA cV wcel wps vx cv
      cA wceq wb vx wal wps vx cio cA wceq wi wph wps vx cv vy cv wceq wb vx
      wal wps vx cio vy cv wceq wi wps vx cv cA wceq wb vx wal wps vx cio cA
      wceq wi vy cA cV vy cv cA wceq wps vx cv vy cv wceq wb vx wal wps vx cv
      cA wceq wb vx wal wps vx cio vy cv wceq wps vx cio cA wceq vy cv cA wceq
      wps vx cv vy cv wceq wb wps vx cv cA wceq wb vx vy cv cA wceq vx cv vy cv
      wceq vx cv cA wceq wps vy cv cA vx cv eqeq2 bibi2d albidv vy cv cA wps vx
      cio eqeq2 imbi12d wps vx vy iotaval vtoclg adantl mpd $.
  $}

  ${
    $d x ph $.
    iotabidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building deduction rule for iota.  (Contributed by NM,
       20-Aug-2011.) $)
    iotabidv $p |- ( ph -> ( iota x ps ) = ( iota x ch ) ) $=
      wph wps wch wb vx wal wps vx cio wch vx cio wceq wph wps wch wb vx
      iotabidv.1 alrimiv wps wch vx iotabi syl $.
  $}

  ${
    iotabii.1 $e |- ( ph <-> ps ) $.
    $( Formula-building deduction rule for iota.  (Contributed by Mario
       Carneiro, 2-Oct-2015.) $)
    iotabii $p |- ( iota x ph ) = ( iota x ps ) $=
      wph wps wb wph vx cio wps vx cio wceq vx wph wps vx iotabi iotabii.1 mpg
      $.
  $}

  $( Membership law for descriptions.

     This can useful for expanding an unbounded iota-based definition (see
     ~ df-iota ).  If you have a bounded iota-based definition, ~ riotacl2 may
     be useful.

     (Contributed by Andrew Salmon, 1-Aug-2011.) $)
  iotacl $p |- ( E! x ph -> ( iota x ph ) e. { x | ph } ) $=
    wph vx weu wph vx wph vx cio wsbc wph vx cio wph vx cab wcel wph vx iota4
    wph vx wph vx cio df-sbc sylib $.

  ${
    $d x y $.  $d y B $.  $d y ps $.
    iota2df.1 $e |- ( ph -> B e. V ) $.
    iota2df.2 $e |- ( ph -> E! x ps ) $.
    iota2df.3 $e |- ( ( ph /\ x = B ) -> ( ps <-> ch ) ) $.
    ${
      iota2df.4 $e |- F/ x ph $.
      iota2df.5 $e |- ( ph -> F/ x ch ) $.
      iota2df.6 $e |- ( ph -> F/_ x B ) $.
      $( A condition that allows us to represent "the unique element such that
         ` ph ` " with a class expression ` A ` .  (Contributed by NM,
         30-Dec-2014.) $)
      iota2df $p |- ( ph -> ( ch <-> ( iota x ps ) = B ) ) $=
        wph vx cB wnfc wch wps vx cio cB wceq wb vx wnf vx cv cB wceq wps wps
        vx cio vx cv wceq wb wch wps vx cio cB wceq wb wb wi vx wal wps wps vx
        cio vx cv wceq wb vx wal cB cV wcel wch wps vx cio cB wceq wb iota2df.6
        wph wch wps vx cio cB wceq vx iota2df.5 wph vx wps vx cio cB vx wps vx
        cio wnfc wph wps vx nfiota1 a1i iota2df.6 nfeqd nfbid wph vx cv cB wceq
        wps wps vx cio vx cv wceq wb wch wps vx cio cB wceq wb wb wi vx
        iota2df.4 wph vx cv cB wceq wps wps vx cio vx cv wceq wb wch wps vx cio
        cB wceq wb wb wph vx cv cB wceq wa wps wch wps vx cio vx cv wceq wps vx
        cio cB wceq iota2df.3 wph vx cv cB wceq wa vx cv cB wps vx cio wph vx
        cv cB wceq simpr eqeq2d bibi12d ex alrimi wph wps wps vx cio vx cv wceq
        wb vx iota2df.4 wph wps vx weu wps wps vx cio vx cv wceq wb iota2df.2
        wps vx iota1 syl alrimi iota2df.1 wps wps vx cio vx cv wceq wb wch wps
        vx cio cB wceq wb vx cB cV vtoclgft syl221anc $.
    $}

    $d x B $.  $d x ph $.  $d x ch $.
    $( A condition that allows us to represent "the unique element such that
       ` ph ` " with a class expression ` A ` .  (Contributed by NM,
       30-Dec-2014.) $)
    iota2d $p |- ( ph -> ( ch <-> ( iota x ps ) = B ) ) $=
      wph wps wch vx cB cV iota2df.1 iota2df.2 iota2df.3 wph vx nfv wph wch vx
      nfvd wph vx cB nfcvd iota2df $.
  $}

  ${
    $d A x $.  $d ps x $.
    iota2.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( The unique element such that ` ph ` .  (Contributed by Jeff Madsen,
       1-Jun-2011.)  (Revised by Mario Carneiro, 23-Dec-2016.) $)
    iota2 $p |- ( ( A e. B /\ E! x ph ) -> ( ps <-> ( iota x ph ) = A ) ) $=
      cA cB wcel cA cvv wcel wph vx weu wps wph vx cio cA wceq wb cA cB elex cA
      cvv wcel wph vx weu wa wph wps vx cA cvv cA cvv wcel wph vx weu simpl cA
      cvv wcel wph vx weu simpr vx cv cA wceq wph wps wb cA cvv wcel wph vx weu
      wa iota2.1 adantl cA cvv wcel wph vx weu vx cA cvv wcel vx nfv wph vx
      nfeu1 nfan cA cvv wcel wph vx weu wa wps vx nfvd cA cvv wcel wph vx weu
      wa vx cA nfcvd iota2df sylan $.
  $}

  $( A class abstraction with a unique member can be expressed as a singleton.
     (Contributed by Mario Carneiro, 23-Dec-2016.) $)
  sniota $p |- ( E! x ph -> { x | ph } = { ( iota x ph ) } ) $=
    wph vx weu vx cv wph vx cab wcel vx cv wph vx cio csn wcel wb vx wal wph vx
    cab wph vx cio csn wceq wph vx weu vx cv wph vx cab wcel vx cv wph vx cio
    csn wcel wb vx wph vx nfeu1 wph vx weu wph vx cv wph vx cio wceq vx cv wph
    vx cab wcel vx cv wph vx cio csn wcel wph vx weu wph wph vx cio vx cv wceq
    vx cv wph vx cio wceq wph vx iota1 wph vx cio vx cv eqcom syl6bb wph vx
    abid vx cv wph vx cio vx vex elsnc 3bitr4g alrimi vx wph vx cab wph vx cio
    csn wph vx nfab1 vx wph vx cio wph vx nfiota1 nfsn cleqf sylibr $.

  ${
    $( The ` iota ` operation using the ` if ` operator.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)
    dfiota4 $p |- ( iota x ph ) = if ( E! x ph , U. { x | ph } , (/) ) $=
      wph vx weu wph vx cio wph vx weu wph vx cab cuni c0 cif wceq wph vx weu
      wph vx cio wph vx cab cuni wph vx weu wph vx cab cuni c0 cif wph vx
      iotauni wph vx weu wph vx cab cuni c0 iftrue eqtr4d wph vx weu wn wph vx
      cio c0 wph vx weu wph vx cab cuni c0 cif wph vx iotanul wph vx weu wph vx
      cab cuni c0 iffalse eqtr4d pm2.61i $.
  $}

  ${
    $d A y z $.  $d x y z $.  $d ph z $.
    $( Class substitution within a description binder.  (Contributed by Scott
       Fenton, 6-Oct-2017.) $)
    csbiotag $p |- ( A e. V ->
        [_ A / x ]_ ( iota y ph ) = ( iota y [. A / x ]. ph ) ) $=
      vx vz cv wph vy cio csb wph vx vz wsb vy cio wceq vx cA wph vy cio csb
      wph vx cA wsbc vy cio wceq vz cA cV vz cv cA wceq vx vz cv wph vy cio csb
      vx cA wph vy cio csb wph vx vz wsb vy cio wph vx cA wsbc vy cio vx vz cv
      cA wph vy cio csbeq1 vz cv cA wceq wph vx vz wsb wph vx cA wsbc vy wph vx
      vz cA dfsbcq2 iotabidv eqeq12d vx vz cv wph vy cio wph vx vz wsb vy cio
      vz vex wph vx vz wsb vx vy wph vx vz nfs1v nfiota vx vz weq wph wph vx vz
      wsb vy wph vx vz sbequ12 iotabidv csbief vtoclg $.
  $}


