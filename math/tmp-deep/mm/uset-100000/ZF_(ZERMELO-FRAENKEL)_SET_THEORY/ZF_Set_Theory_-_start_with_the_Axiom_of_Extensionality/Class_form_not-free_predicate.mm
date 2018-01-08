
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Class_abstractions_(a_k_a__class_builders).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Class form not-free predicate

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c F/_ $.  $( Underlined not-free symbol. $)

  $( Extend wff definition to include the not-free predicate for classes. $)
  wnfc $a wff F/_ x A $.

  ${
    $d x y z $.  $d y z A $.
    $( Justification theorem for ~ df-nfc .  (Contributed by Mario Carneiro,
       13-Oct-2016.) $)
    nfcjust $p |- ( A. y F/ x y e. A <-> A. z F/ x z e. A ) $=
      vy cv cA wcel vx wnf vz cv cA wcel vx wnf vy vz vy cv vz cv wceq vy cv cA
      wcel vz cv cA wcel vx vy cv vz cv wceq vx nfv vy cv vz cv cA eleq1 nfbidf
      cbvalv $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Define the not-free predicate for classes.  This is read " ` x ` is not
       free in ` A ` ".  Not-free means that the value of ` x ` cannot affect
       the value of ` A ` , e.g., any occurrence of ` x ` in ` A ` is
       effectively bound by a "for all" or something that expands to one (such
       as "there exists").  It is defined in terms of the not-free predicate
       ~ df-nf for wffs; see that definition for more information.
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    df-nfc $a |- ( F/_ x A <-> A. y F/ x y e. A ) $.

    ${
      nfci.1 $e |- F/ x y e. A $.
      $( Deduce that a class ` A ` does not have ` x ` free in it.
         (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfci $p |- F/_ x A $=
        vx cA wnfc vy cv cA wcel vx wnf vy vx vy cA df-nfc nfci.1 mpgbir $.
    $}

    ${
      nfcii.1 $e |- ( y e. A -> A. x y e. A ) $.
      $( Deduce that a class ` A ` does not have ` x ` free in it.
         (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfcii $p |- F/_ x A $=
        vx vy cA vy cv cA wcel vx nfcii.1 nfi nfci $.
    $}

    $( Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfcr $p |- ( F/_ x A -> F/ x y e. A ) $=
      vx cA wnfc vy cv cA wcel vx wnf vy wal vy cv cA wcel vx wnf vx vy cA
      df-nfc vy cv cA wcel vx wnf vy sp sylbi $.
  $}

  ${
    $d x y z $.  $d z A $.
    nfcri.1 $e |- F/_ x A $.
    $( Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfcrii $p |- ( y e. A -> A. x y e. A ) $=
      vx vz vy cA vz cv cA wcel vx vx cA wnfc vz cv cA wcel vx wnf nfcri.1 vx
      vz cA nfcr ax-mp nfri hblem $.

    $( Consequence of the not-free predicate.  (Note that unlike ~ nfcr , this
       does not require ` y ` and ` A ` to be disjoint.)  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfcri $p |- F/ x y e. A $=
      vy cv cA wcel vx vx vy cA nfcri.1 nfcrii nfi $.
  $}

  ${
    $d x y $.  $d y A $.
    nfcd.1 $e |- F/ y ph $.
    nfcd.2 $e |- ( ph -> F/ x y e. A ) $.
    $( Deduce that a class ` A ` does not have ` x ` free in it.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
    nfcd $p |- ( ph -> F/_ x A ) $=
      wph vy cv cA wcel vx wnf vy wal vx cA wnfc wph vy cv cA wcel vx wnf vy
      nfcd.1 nfcd.2 alrimi vx vy cA df-nfc sylibr $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    nfceqi.1 $e |- A = B $.
    $( Equality theorem for class not-free.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfceqi $p |- ( F/_ x A <-> F/_ x B ) $=
      vy cv cA wcel vx wnf vy wal vy cv cB wcel vx wnf vy wal vx cA wnfc vx cB
      wnfc vy cv cA wcel vx wnf vy cv cB wcel vx wnf vy vy cv cA wcel vy cv cB
      wcel vx cA cB vy cv nfceqi.1 eleq2i nfbii albii vx vy cA df-nfc vx vy cB
      df-nfc 3bitr4i $.

    ${
      nfcxfr.2 $e |- F/_ x B $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfcxfr $p |- F/_ x A $=
        vx cA wnfc vx cB wnfc nfcxfr.2 vx cA cB nfceqi.1 nfceqi mpbir $.
    $}

    ${
      nfcxfrd.2 $e |- ( ph -> F/_ x B ) $.
      $( A utility lemma to transfer a bound-variable hypothesis builder into a
         definition.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
      nfcxfrd $p |- ( ph -> F/_ x A ) $=
        wph vx cB wnfc vx cA wnfc nfcxfrd.2 vx cA cB nfceqi.1 nfceqi sylibr $.
    $}
  $}

  ${
    $d x y $.  $d A y $.  $d B y $.  $d ph y $.
    nfceqdf.1 $e |- F/ x ph $.
    nfceqdf.2 $e |- ( ph -> A = B ) $.
    $( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)
    nfceqdf $p |- ( ph -> ( F/_ x A <-> F/_ x B ) ) $=
      wph vy cv cA wcel vx wnf vy wal vy cv cB wcel vx wnf vy wal vx cA wnfc vx
      cB wnfc wph vy cv cA wcel vx wnf vy cv cB wcel vx wnf vy wph vy cv cA
      wcel vy cv cB wcel vx nfceqdf.1 wph cA cB vy cv nfceqdf.2 eleq2d nfbidf
      albidv vx vy cA df-nfc vx vy cB df-nfc 3bitr4g $.
  $}

  ${
    $d x y A $.
    $( If ` x ` is disjoint from ` A ` , then ` x ` is not free in ` A ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfcv $p |- F/_ x A $=
      vx vy cA vy cv cA wcel vx nfv nfci $.

    $( If ` x ` is disjoint from ` A ` , then ` x ` is not free in ` A ` .
       (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    nfcvd $p |- ( ph -> F/_ x A ) $=
      vx cA wnfc wph vx cA nfcv a1i $.
  $}

  ${
    $d x y $.  $d y A $.  $d y ph $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
    nfab1 $p |- F/_ x { x | ph } $=
      vx vy wph vx cab wph vx vy nfsab1 nfci $.

    $( ` x ` is bound in ` F/_ x A ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfnfc1 $p |- F/ x F/_ x A $=
      vx cA wnfc vy cv cA wcel vx wnf vy wal vx vx vy cA df-nfc vy cv cA wcel
      vx wnf vx vy vy cv cA wcel vx nfnf1 nfal nfxfr $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    nfab.1 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 11-Aug-2016.) $)
    nfab $p |- F/_ x { y | ph } $=
      vx vz wph vy cab wph vx vy vz nfab.1 nfsab nfci $.
  $}

  ${
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 14-Oct-2016.) $)
    nfaba1 $p |- F/_ x { y | A. x ph } $=
      wph vx wal vx vy wph vx nfa1 nfab $.
  $}

  ${
    $d x z $.  $d y z $.  $d z A $.  $d z B $.
    nfnfc.1 $e |- F/_ x A $.
    $( Hypothesis builder for ` F/_ y A ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfnfc $p |- F/ x F/_ y A $=
      vy cA wnfc vz cv cA wcel vy wnf vz wal vx vy vz cA df-nfc vz cv cA wcel
      vy wnf vx vz vz cv cA wcel vx vy vx vz cA nfnfc.1 nfcri nfnf nfal nfxfr
      $.

    nfeq.2 $e |- F/_ x B $.
    $( Hypothesis builder for equality.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfeq $p |- F/ x A = B $=
      cA cB wceq vz cv cA wcel vz cv cB wcel wb vz wal vx vz cA cB dfcleq vz cv
      cA wcel vz cv cB wcel wb vx vz vz cv cA wcel vz cv cB wcel vx vx vz cA
      nfnfc.1 nfcri vx vz cB nfeq.2 nfcri nfbi nfal nfxfr $.

    $( Hypothesis builder for elementhood.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfel $p |- F/ x A e. B $=
      cA cB wcel vz cv cA wceq vz cv cB wcel wa vz wex vx vz cA cB df-clel vz
      cv cA wceq vz cv cB wcel wa vx vz vz cv cA wceq vz cv cB wcel vx vx vz cv
      cA vx vz cv nfcv nfnfc.1 nfeq vx vz cB nfeq.2 nfcri nfan nfex nfxfr $.
  $}

  ${
    $d x B $.
    nfeq1.1 $e |- F/_ x A $.
    $( Hypothesis builder for equality, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
    nfeq1 $p |- F/ x A = B $=
      vx cA cB nfeq1.1 vx cB nfcv nfeq $.

    $( Hypothesis builder for elementhood, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
    nfel1 $p |- F/ x A e. B $=
      vx cA cB nfeq1.1 vx cB nfcv nfel $.
  $}

  ${
    $d x A $.
    nfeq2.1 $e |- F/_ x B $.
    $( Hypothesis builder for equality, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
    nfeq2 $p |- F/ x A = B $=
      vx cA cB vx cA nfcv nfeq2.1 nfeq $.

    $( Hypothesis builder for elementhood, special case.  (Contributed by Mario
       Carneiro, 10-Oct-2016.) $)
    nfel2 $p |- F/ x A e. B $=
      vx cA cB vx cA nfcv nfeq2.1 nfel $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.
    nfeqd.1 $e |- ( ph -> F/_ x A ) $.
    $( Consequence of the not-free predicate.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfcrd $p |- ( ph -> F/ x y e. A ) $=
      wph vx cA wnfc vy cv cA wcel vx wnf nfeqd.1 vx vy cA nfcr syl $.

    $d y ph $.
    nfeqd.2 $e |- ( ph -> F/_ x B ) $.
    $( Hypothesis builder for equality.  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
    nfeqd $p |- ( ph -> F/ x A = B ) $=
      cA cB wceq vy cv cA wcel vy cv cB wcel wb vy wal wph vx vy cA cB dfcleq
      wph vy cv cA wcel vy cv cB wcel wb vx vy wph vy nfv wph vy cv cA wcel vy
      cv cB wcel vx wph vx vy cA nfeqd.1 nfcrd wph vx vy cB nfeqd.2 nfcrd nfbid
      nfald nfxfrd $.

    $( Hypothesis builder for elementhood.  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
    nfeld $p |- ( ph -> F/ x A e. B ) $=
      cA cB wcel vy cv cA wceq vy cv cB wcel wa vy wex wph vx vy cA cB df-clel
      wph vy cv cA wceq vy cv cB wcel wa vx vy wph vy nfv wph vy cv cA wceq vy
      cv cB wcel vx wph vx vy cv cA wph vx vy cv nfcvd nfeqd.1 nfeqd wph vx vy
      cB nfeqd.2 nfcrd nfand nfexd nfxfrd $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.  $d w A $.  $d w B $.
    drnfc1.1 $e |- ( A. x x = y -> A = B ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
    drnfc1 $p |- ( A. x x = y -> ( F/_ x A <-> F/_ y B ) ) $=
      vx cv vy cv wceq vx wal vw cv cA wcel vx wnf vw wal vw cv cB wcel vy wnf
      vw wal vx cA wnfc vy cB wnfc vw cv cA wcel vx wnf vw cv cB wcel vy wnf vx
      vy vw vw cv cA wcel vw cv cB wcel vx vy vx cv vy cv wceq vx wal cA cB vw
      cv drnfc1.1 eleq2d drnf1 dral2 vx vw cA df-nfc vy vw cB df-nfc 3bitr4g $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
    drnfc2 $p |- ( A. x x = y -> ( F/_ z A <-> F/_ z B ) ) $=
      vx cv vy cv wceq vx wal vw cv cA wcel vz wnf vw wal vw cv cB wcel vz wnf
      vw wal vz cA wnfc vz cB wnfc vw cv cA wcel vz wnf vw cv cB wcel vz wnf vx
      vy vw vw cv cA wcel vw cv cB wcel vx vy vz vx cv vy cv wceq vx wal cA cB
      vw cv drnfc1.1 eleq2d drnf2 dral2 vz vw cA df-nfc vz vw cB df-nfc 3bitr4g
      $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.  $d z ps $.
    nfabd2.1 $e |- F/ y ph $.
    nfabd2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 8-Oct-2016.) $)
    nfabd2 $p |- ( ph -> F/_ x { y | ps } ) $=
      wph vx cv vy cv wceq vx wal vx wps vy cab wnfc wph vx cv vy cv wceq vx
      wal wn vx wps vy cab wnfc wph vx cv vy cv wceq vx wal wn wa vx vz wps vy
      cab wph vx cv vy cv wceq vx wal wn wa vz nfv vz cv wps vy cab wcel wps vy
      vz wsb wph vx cv vy cv wceq vx wal wn wa vx wps vz vy df-clab wph vx cv
      vy cv wceq vx wal wn wa wps vy vz vx wph vx cv vy cv wceq vx wal wn vy
      nfabd2.1 vx vy vy nfnae nfan nfabd2.2 nfsbd nfxfrd nfcd ex vx cv vy cv
      wceq vx wal vx wps vy cab wnfc vy wps vy cab wnfc wps vy nfab1 vx vy wps
      vy cab wps vy cab vx cv vy cv wceq vx wal wps vy cab eqidd drnfc1 mpbiri
      pm2.61d2 $.
  $}

  ${
    nfabd.1 $e |- F/ y ph $.
    nfabd.2 $e |- ( ph -> F/ x ps ) $.
    $( Bound-variable hypothesis builder for a class abstraction.  (Contributed
       by Mario Carneiro, 8-Oct-2016.) $)
    nfabd $p |- ( ph -> F/_ x { y | ps } ) $=
      wph wps vx vy nfabd.1 wph wps vx wnf vx cv vy cv wceq vx wal wn nfabd.2
      adantr nfabd2 $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.  $d w A $.  $d w B $.  $d w ph $.
    dvelimdc.1 $e |- F/ x ph $.
    dvelimdc.2 $e |- F/ z ph $.
    dvelimdc.3 $e |- ( ph -> F/_ x A ) $.
    dvelimdc.4 $e |- ( ph -> F/_ z B ) $.
    dvelimdc.5 $e |- ( ph -> ( z = y -> A = B ) ) $.
    $( Deduction form of ~ dvelimc .  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    dvelimdc $p |- ( ph -> ( -. A. x x = y -> F/_ x B ) ) $=
      wph vx cv vy cv wceq vx wal wn vx cB wnfc wph vx cv vy cv wceq vx wal wn
      wa vx vw cB wph vx cv vy cv wceq vx wal wn wa vw nfv wph vx cv vy cv wceq
      vx wal wn vw cv cB wcel vx wnf wph vw cv cA wcel vw cv cB wcel vx vy vz
      dvelimdc.1 dvelimdc.2 wph vx vw cA dvelimdc.3 nfcrd wph vz vw cB
      dvelimdc.4 nfcrd wph vz cv vy cv wceq cA cB wceq vw cv cA wcel vw cv cB
      wcel wb dvelimdc.5 cA cB vw cv eleq2 syl6 dvelimdf imp nfcd ex $.
  $}

  ${
    dvelimc.1 $e |- F/_ x A $.
    dvelimc.2 $e |- F/_ z B $.
    dvelimc.3 $e |- ( z = y -> A = B ) $.
    $( Version of ~ dvelim for classes.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    dvelimc $p |- ( -. A. x x = y -> F/_ x B ) $=
      vx cv vy cv wceq vx wal wn vx cB wnfc wi wtru vx vy vz cA cB vx nftru vz
      nftru vx cA wnfc wtru dvelimc.1 a1i vz cB wnfc wtru dvelimc.2 a1i vz cv
      vy cv wceq cA cB wceq wi wtru dvelimc.3 a1i dvelimdc trud $.
  $}

  ${
    $d x z $.  $d y z $.
    $( If ` x ` and ` y ` are distinct, then ` x ` is not free in ` y ` .
       (Contributed by Mario Carneiro, 8-Oct-2016.) $)
    nfcvf $p |- ( -. A. x x = y -> F/_ x y ) $=
      vx vy vz vz cv vy cv vx vz cv nfcv vz vy cv nfcv vz cv vy cv wceq id
      dvelimc $.

    $( If ` x ` and ` y ` are distinct, then ` y ` is not free in ` x ` .
       (Contributed by Mario Carneiro, 5-Dec-2016.) $)
    nfcvf2 $p |- ( -. A. x x = y -> F/_ y x ) $=
      vy vx cv wnfc vy vx vy vx nfcvf naecoms $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    cleqf.1 $e |- F/_ x A $.
    cleqf.2 $e |- F/_ x B $.
    $( Establish equality between classes, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
    cleqf $p |- ( A = B <-> A. x ( x e. A <-> x e. B ) ) $=
      cA cB wceq vy cv cA wcel vy cv cB wcel wb vy wal vx cv cA wcel vx cv cB
      wcel wb vx wal vy cA cB dfcleq vx cv cA wcel vx cv cB wcel wb vy cv cA
      wcel vy cv cB wcel wb vx vy vx cv cA wcel vx cv cB wcel wb vy nfv vy cv
      cA wcel vy cv cB wcel vx vx vy cA cleqf.1 nfcri vx vy cB cleqf.2 nfcri
      nfbi vx cv vy cv wceq vx cv cA wcel vy cv cA wcel vx cv cB wcel vy cv cB
      wcel vx cv vy cv cA eleq1 vx cv vy cv cB eleq1 bibi12d cbval bitr4i $.
  $}

  ${
    $d y A $.  $d x y $.
    abid2f.1 $e |- F/_ x A $.
    $( A simplification of class abstraction.  Theorem 5.2 of [Quine] p. 35.
       (Contributed by NM, 5-Sep-2011.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    abid2f $p |- { x | x e. A } = A $=
      cA vx cv cA wcel vx cab cA vx cv cA wcel vx cab wceq vx cv cA wcel vx cv
      cA wcel wb vx cA vx cv cA wcel vx cab wceq vx cv cA wcel vx cv vx cv cA
      wcel vx cab wcel wb vx wal vx cv cA wcel vx cv cA wcel wb vx wal vx cA vx
      cv cA wcel vx cab abid2f.1 vx cv cA wcel vx nfab1 cleqf vx cv cA wcel vx
      cv vx cv cA wcel vx cab wcel wb vx cv cA wcel vx cv cA wcel wb vx vx cv
      vx cv cA wcel vx cab wcel vx cv cA wcel vx cv cA wcel vx cv cA wcel vx
      abid bibi2i albii bitri vx cv cA wcel biid mpgbir eqcomi $.
  $}

  ${
    $d v A w $.  $d x z v u $.  $d y z v u $.  $d v ph $.
    sbabel.1 $e |- F/_ x A $.
    $( Theorem to move a substitution in and out of a class abstraction.
       (Contributed by NM, 27-Sep-2003.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    sbabel $p |- ( [ y / x ] { z | ph } e. A <-> { z | [ y / x ] ph } e. A ) $=
      vv cv wph vz cab wceq vv cv cA wcel wa vv wex vx vy wsb vv cv wph vx vy
      wsb vz cab wceq vv cv cA wcel wa vv wex wph vz cab cA wcel vx vy wsb wph
      vx vy wsb vz cab cA wcel vv cv wph vz cab wceq vv cv cA wcel wa vv wex vx
      vy wsb vv cv wph vz cab wceq vv cv cA wcel wa vx vy wsb vv wex vv cv wph
      vx vy wsb vz cab wceq vv cv cA wcel wa vv wex vv cv wph vz cab wceq vv cv
      cA wcel wa vv vx vy sbex vv cv wph vz cab wceq vv cv cA wcel wa vx vy wsb
      vv cv wph vx vy wsb vz cab wceq vv cv cA wcel wa vv vv cv wph vz cab wceq
      vv cv cA wcel wa vx vy wsb vv cv wph vz cab wceq vx vy wsb vv cv cA wcel
      vx vy wsb wa vv cv wph vx vy wsb vz cab wceq vv cv cA wcel wa vv cv wph
      vz cab wceq vv cv cA wcel vx vy sban vv cv wph vz cab wceq vx vy wsb vv
      cv wph vx vy wsb vz cab wceq vv cv cA wcel vx vy wsb vv cv cA wcel vz cv
      vv cv wcel wph wb vz wal vx vy wsb vz cv vv cv wcel wph vx vy wsb wb vz
      wal vv cv wph vz cab wceq vx vy wsb vv cv wph vx vy wsb vz cab wceq vz cv
      vv cv wcel wph wb vz cv vv cv wcel wph vx vy wsb wb vx vy vz vz cv vv cv
      wcel vz cv vv cv wcel wph vx vy vz cv vv cv wcel vx vy vz cv vv cv wcel
      vx nfv sbf sbrbis sbalv vv cv wph vz cab wceq vz cv vv cv wcel wph wb vz
      wal vx vy wph vz vv cv abeq2 sbbii wph vx vy wsb vz vv cv abeq2 3bitr4i
      vv cv cA wcel vx vy vx vv cA sbabel.1 nfcri sbf anbi12i bitri exbii bitri
      wph vz cab cA wcel vv cv wph vz cab wceq vv cv cA wcel wa vv wex vx vy vv
      wph vz cab cA df-clel sbbii vv wph vx vy wsb vz cab cA df-clel 3bitr4i $.
  $}


