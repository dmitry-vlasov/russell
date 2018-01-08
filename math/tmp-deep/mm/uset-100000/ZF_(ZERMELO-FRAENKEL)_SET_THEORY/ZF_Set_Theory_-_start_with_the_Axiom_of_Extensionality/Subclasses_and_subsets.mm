
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Define_basic_set_operations_and_relations.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Subclasses and subsets

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)
  $( Define the subclass relationship.  Exercise 9 of [TakeutiZaring] p. 18.
     For example, ` { 1 , 2 } C_ { 1 , 2 , 3 } ` ( ~ ex-ss ).  Note that
     ` A C_ A ` (proved in ~ ssid ).  Contrast this relationship with the
     relationship ` A C. B ` (as will be defined in ~ df-pss ).  For a more
     traditional definition, but requiring a dummy variable, see ~ dfss2 .
     Other possible definitions are given by ~ dfss3 , ~ dfss4 , ~ sspss ,
     ~ ssequn1 , ~ ssequn2 , ~ sseqin2 , and ~ ssdif0 .  (Contributed by NM,
     27-Apr-1994.) $)
  df-ss $a |- ( A C_ B <-> ( A i^i B ) = A ) $.

  $( Variant of subclass definition ~ df-ss .  (Contributed by NM,
     3-Sep-2004.) $)
  dfss $p |- ( A C_ B <-> A = ( A i^i B ) ) $=
    cA cB wss cA cB cin cA wceq cA cA cB cin wceq cA cB df-ss cA cB cin cA
    eqcom bitri $.

  $( Define proper subclass relationship between two classes.  Definition 5.9
     of [TakeutiZaring] p. 17.  For example, ` { 1 , 2 } C. { 1 , 2 , 3 } `
     ( ~ ex-pss ).  Note that ` -. A C. A ` (proved in ~ pssirr ).  Contrast
     this relationship with the relationship ` A C_ B ` (as defined in
     ~ df-ss ).  Other possible definitions are given by ~ dfpss2 and
     ~ dfpss3 .  (Contributed by NM, 7-Feb-1996.) $)
  df-pss $a |- ( A C. B <-> ( A C_ B /\ A =/= B ) ) $.

  ${
    $d x A $.  $d x B $.
    $( Alternate definition of the subclass relationship between two classes.
       Definition 5.9 of [TakeutiZaring] p. 17.  (Contributed by NM,
       8-Jan-2002.) $)
    dfss2 $p |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $=
      cA cB wss vx cv cA wcel vx cv cA wcel vx cv cB wcel wa wb vx wal vx cv cA
      wcel vx cv cB wcel wi vx wal cA cB wss cA cA cB cin wceq cA vx cv cA wcel
      vx cv cB wcel wa vx cab wceq vx cv cA wcel vx cv cA wcel vx cv cB wcel wa
      wb vx wal cA cB dfss cA cB cin vx cv cA wcel vx cv cB wcel wa vx cab cA
      vx cA cB df-in eqeq2i vx cv cA wcel vx cv cB wcel wa vx cA abeq2 3bitri
      vx cv cA wcel vx cv cB wcel wi vx cv cA wcel vx cv cA wcel vx cv cB wcel
      wa wb vx vx cv cA wcel vx cv cB wcel pm4.71 albii bitr4i $.

    $( Alternate definition of subclass relationship.  (Contributed by NM,
       14-Oct-1999.) $)
    dfss3 $p |- ( A C_ B <-> A. x e. A x e. B ) $=
      cA cB wss vx cv cA wcel vx cv cB wcel wi vx wal vx cv cB wcel vx cA wral
      vx cA cB dfss2 vx cv cB wcel vx cA df-ral bitr4i $.
  $}

  ${
    $d z y A $.  $d z y B $.  $d x z $.
    dfss2f.1 $e |- F/_ x A $.
    dfss2f.2 $e |- F/_ x B $.
    $( Equivalence for subclass relation, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       3-Jul-1994.)  (Revised by Andrew Salmon, 27-Aug-2011.) $)
    dfss2f $p |- ( A C_ B <-> A. x ( x e. A -> x e. B ) ) $=
      cA cB wss vz cv cA wcel vz cv cB wcel wi vz wal vx cv cA wcel vx cv cB
      wcel wi vx wal vz cA cB dfss2 vz cv cA wcel vz cv cB wcel wi vx cv cA
      wcel vx cv cB wcel wi vz vx vz cv cA wcel vz cv cB wcel vx vx vz cA
      dfss2f.1 nfcri vx vz cB dfss2f.2 nfcri nfim vx cv cA wcel vx cv cB wcel
      wi vz nfv vz cv vx cv wceq vz cv cA wcel vx cv cA wcel vz cv cB wcel vx
      cv cB wcel vz cv vx cv cA eleq1 vz cv vx cv cB eleq1 imbi12d cbval bitri
      $.

    $d y A $.  $d y B $.
    $( Equivalence for subclass relation, using bound-variable hypotheses
       instead of distinct variable conditions.  (Contributed by NM,
       20-Mar-2004.) $)
    dfss3f $p |- ( A C_ B <-> A. x e. A x e. B ) $=
      cA cB wss vx cv cA wcel vx cv cB wcel wi vx wal vx cv cB wcel vx cA wral
      vx cA cB dfss2f.1 dfss2f.2 dfss2f vx cv cB wcel vx cA df-ral bitr4i $.

    $( If ` x ` is not free in ` A ` and ` B ` , it is not free in
       ` A C_ B ` .  (Contributed by NM, 27-Dec-1996.) $)
    nfss $p |- F/ x A C_ B $=
      cA cB wss vx cv cB wcel vx cA wral vx vx cA cB dfss2f.1 dfss2f.2 dfss3f
      vx cv cB wcel vx cA nfra1 nfxfr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Membership relationships follow from a subclass relationship.
       (Contributed by NM, 5-Aug-1993.) $)
    ssel $p |- ( A C_ B -> ( C e. A -> C e. B ) ) $=
      cA cB wss vx cv cC wceq vx cv cA wcel wa vx wex vx cv cC wceq vx cv cB
      wcel wa vx wex cC cA wcel cC cB wcel cA cB wss vx cv cC wceq vx cv cA
      wcel wa vx cv cC wceq vx cv cB wcel wa vx cA cB wss vx cv cA wcel vx cv
      cB wcel vx cv cC wceq cA cB wss vx cv cA wcel vx cv cB wcel wi vx cA cB
      wss vx cv cA wcel vx cv cB wcel wi vx wal vx cA cB dfss2 biimpi 19.21bi
      anim2d eximdv vx cC cA df-clel vx cC cB df-clel 3imtr4g $.
  $}

  $( Membership relationships follow from a subclass relationship.
     (Contributed by NM, 7-Jun-2004.) $)
  ssel2 $p |- ( ( A C_ B /\ C e. A ) -> C e. B ) $=
    cA cB wss cC cA wcel cC cB wcel cA cB cC ssel imp $.

  ${
    sseli.1 $e |- A C_ B $.
    $( Membership inference from subclass relationship.  (Contributed by NM,
       5-Aug-1993.) $)
    sseli $p |- ( C e. A -> C e. B ) $=
      cA cB wss cC cA wcel cC cB wcel wi sseli.1 cA cB cC ssel ax-mp $.

    ${
      sselii.2 $e |- C e. A $.
      $( Membership inference from subclass relationship.  (Contributed by NM,
         31-May-1999.) $)
      sselii $p |- C e. B $=
        cC cA wcel cC cB wcel sselii.2 cA cB cC sseli.1 sseli ax-mp $.
    $}

    ${
      sseldi.2 $e |- ( ph -> C e. A ) $.
      $( Membership inference from subclass relationship.  (Contributed by NM,
         25-Jun-2014.) $)
      sseldi $p |- ( ph -> C e. B ) $=
        wph cC cA wcel cC cB wcel sseldi.2 cA cB cC sseli.1 sseli syl $.
    $}
  $}

  ${
    sseld.1 $e |- ( ph -> A C_ B ) $.
    $( Membership deduction from subclass relationship.  (Contributed by NM,
       15-Nov-1995.) $)
    sseld $p |- ( ph -> ( C e. A -> C e. B ) ) $=
      wph cA cB wss cC cA wcel cC cB wcel wi sseld.1 cA cB cC ssel syl $.

    $( Membership deduction from subclass relationship.  (Contributed by NM,
       26-Jun-2014.) $)
    sselda $p |- ( ( ph /\ C e. A ) -> C e. B ) $=
      wph cC cA wcel cC cB wcel wph cA cB cC sseld.1 sseld imp $.

    ${
      sseldd.2 $e |- ( ph -> C e. A ) $.
      $( Membership inference from subclass relationship.  (Contributed by NM,
         14-Dec-2004.) $)
      sseldd $p |- ( ph -> C e. B ) $=
        wph cC cA wcel cC cB wcel sseldd.2 wph cA cB cC sseld.1 sseld mpd $.
    $}
  $}

  ${
    ssneld.1 $e |- ( ph -> A C_ B ) $.
    $( If a class is not in another class, it is also not in a subclass of that
       class.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
    ssneld $p |- ( ph -> ( -. C e. B -> -. C e. A ) ) $=
      wph cC cA wcel cC cB wcel wph cA cB cC ssneld.1 sseld con3d $.

    ssneldd.2 $e |- ( ph -> -. C e. B ) $.
    $( If an element is not in a class, it is also not in a subclass of that
       class.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
    ssneldd $p |- ( ph -> -. C e. A ) $=
      wph cC cB wcel wn cC cA wcel wn ssneldd.2 wph cA cB cC ssneld.1 ssneld
      mpd $.
  $}

  ${
    $d x A $.  $d x B $.
    ssriv.1 $e |- ( x e. A -> x e. B ) $.
    $( Inference rule based on subclass definition.  (Contributed by NM,
       5-Aug-1993.) $)
    ssriv $p |- A C_ B $=
      cA cB wss vx cv cA wcel vx cv cB wcel wi vx vx cA cB dfss2 ssriv.1 mpgbir
      $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    ssrdv.1 $e |- ( ph -> ( x e. A -> x e. B ) ) $.
    $( Deduction rule based on subclass definition.  (Contributed by NM,
       15-Nov-1995.) $)
    ssrdv $p |- ( ph -> A C_ B ) $=
      wph vx cv cA wcel vx cv cB wcel wi vx wal cA cB wss wph vx cv cA wcel vx
      cv cB wcel wi vx ssrdv.1 alrimiv vx cA cB dfss2 sylibr $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Transitivity of subclasses.  Exercise 5 of [TakeutiZaring] p. 17.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    sstr2 $p |- ( A C_ B -> ( B C_ C -> A C_ C ) ) $=
      cA cB wss vx cv cB wcel vx cv cC wcel wi vx wal vx cv cA wcel vx cv cC
      wcel wi vx wal cB cC wss cA cC wss cA cB wss vx cv cB wcel vx cv cC wcel
      wi vx cv cA wcel vx cv cC wcel wi vx cA cB wss vx cv cA wcel vx cv cB
      wcel vx cv cC wcel cA cB vx cv ssel imim1d alimdv vx cB cC dfss2 vx cA cC
      dfss2 3imtr4g $.
  $}

  $( Transitivity of subclasses.  Theorem 6 of [Suppes] p. 23.  (Contributed by
     NM, 5-Sep-2003.) $)
  sstr $p |- ( ( A C_ B /\ B C_ C ) -> A C_ C ) $=
    cA cB wss cB cC wss cA cC wss cA cB cC sstr2 imp $.

  ${
    sstri.1 $e |- A C_ B $.
    sstri.2 $e |- B C_ C $.
    $( Subclass transitivity inference.  (Contributed by NM, 5-May-2000.) $)
    sstri $p |- A C_ C $=
      cA cB wss cB cC wss cA cC wss sstri.1 sstri.2 cA cB cC sstr2 mp2 $.
  $}

  ${
    sstrd.1 $e |- ( ph -> A C_ B ) $.
    sstrd.2 $e |- ( ph -> B C_ C ) $.
    $( Subclass transitivity deduction.  (Contributed by NM, 2-Jun-2004.) $)
    sstrd $p |- ( ph -> A C_ C ) $=
      wph cA cB wss cB cC wss cA cC wss sstrd.1 sstrd.2 cA cB cC sstr syl2anc
      $.
  $}

  ${
    syl5ss.1 $e |- A C_ B $.
    syl5ss.2 $e |- ( ph -> B C_ C ) $.
    $( Subclass transitivity deduction.  (Contributed by NM, 6-Feb-2014.) $)
    syl5ss $p |- ( ph -> A C_ C ) $=
      wph cA cB cC cA cB wss wph syl5ss.1 a1i syl5ss.2 sstrd $.
  $}

  ${
    syl6ss.1 $e |- ( ph -> A C_ B ) $.
    syl6ss.2 $e |- B C_ C $.
    $( Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    syl6ss $p |- ( ph -> A C_ C ) $=
      wph cA cB cC syl6ss.1 cB cC wss wph syl6ss.2 a1i sstrd $.
  $}

  ${
    sylan9ss.1 $e |- ( ph -> A C_ B ) $.
    sylan9ss.2 $e |- ( ps -> B C_ C ) $.
    $( A subclass transitivity deduction.  (Contributed by NM, 27-Sep-2004.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    sylan9ss $p |- ( ( ph /\ ps ) -> A C_ C ) $=
      wph cA cB wss cB cC wss cA cC wss wps sylan9ss.1 sylan9ss.2 cA cB cC sstr
      syl2an $.
  $}

  ${
    sylan9ssr.1 $e |- ( ph -> A C_ B ) $.
    sylan9ssr.2 $e |- ( ps -> B C_ C ) $.
    $( A subclass transitivity deduction.  (Contributed by NM, 27-Sep-2004.) $)
    sylan9ssr $p |- ( ( ps /\ ph ) -> A C_ C ) $=
      wph wps cA cC wss wph wps cA cB cC sylan9ssr.1 sylan9ssr.2 sylan9ss
      ancoms $.
  $}

  ${
    $d x A $.  $d x B $.
    $( The subclass relationship is antisymmetric.  Compare Theorem 4 of
       [Suppes] p. 22.  (Contributed by NM, 5-Aug-1993.) $)
    eqss $p |- ( A = B <-> ( A C_ B /\ B C_ A ) ) $=
      vx cv cA wcel vx cv cB wcel wb vx wal vx cv cA wcel vx cv cB wcel wi vx
      wal vx cv cB wcel vx cv cA wcel wi vx wal wa cA cB wceq cA cB wss cB cA
      wss wa vx cv cA wcel vx cv cB wcel vx albiim vx cA cB dfcleq cA cB wss vx
      cv cA wcel vx cv cB wcel wi vx wal cB cA wss vx cv cB wcel vx cv cA wcel
      wi vx wal vx cA cB dfss2 vx cB cA dfss2 anbi12i 3bitr4i $.
  $}

  ${
    eqssi.1 $e |- A C_ B $.
    eqssi.2 $e |- B C_ A $.
    $( Infer equality from two subclass relationships.  Compare Theorem 4 of
       [Suppes] p. 22.  (Contributed by NM, 9-Sep-1993.) $)
    eqssi $p |- A = B $=
      cA cB wceq cA cB wss cB cA wss eqssi.1 eqssi.2 cA cB eqss mpbir2an $.
  $}

  ${
    eqssd.1 $e |- ( ph -> A C_ B ) $.
    eqssd.2 $e |- ( ph -> B C_ A ) $.
    $( Equality deduction from two subclass relationships.  Compare Theorem 4
       of [Suppes] p. 22.  (Contributed by NM, 27-Jun-2004.) $)
    eqssd $p |- ( ph -> A = B ) $=
      wph cA cB wss cB cA wss cA cB wceq eqssd.1 eqssd.2 cA cB eqss sylanbrc $.
  $}

  ${
    $d A x $.
    $( Any class is a subclass of itself.  Exercise 10 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 14-Jun-2011.) $)
    ssid $p |- A C_ A $=
      vx cA cA vx cv cA wcel id ssriv $.
  $}

  ${
    $d A x $.
    $( Any class is a subclass of the universal class.  (Contributed by NM,
       31-Oct-1995.) $)
    ssv $p |- A C_ _V $=
      vx cA cvv vx cv cA elex ssriv $.
  $}

  $( Equality theorem for subclasses.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 21-Jun-2011.) $)
  sseq1 $p |- ( A = B -> ( A C_ C <-> B C_ C ) ) $=
    cA cB wceq cA cB wss cB cA wss wa cA cC wss cB cC wss wb cA cB eqss cA cB
    wss cB cA wss wa cA cC wss cB cC wss cB cA wss cA cC wss cB cC wss wi cA cB
    wss cB cA cC sstr2 adantl cA cB wss cB cC wss cA cC wss wi cB cA wss cA cB
    cC sstr2 adantr impbid sylbi $.

  $( Equality theorem for the subclass relationship.  (Contributed by NM,
     25-Jun-1998.) $)
  sseq2 $p |- ( A = B -> ( C C_ A <-> C C_ B ) ) $=
    cA cB wss cB cA wss wa cC cA wss cC cB wss wi cC cB wss cC cA wss wi wa cA
    cB wceq cC cA wss cC cB wss wb cA cB wss cC cA wss cC cB wss wi cB cA wss
    cC cB wss cC cA wss wi cC cA wss cA cB wss cC cB wss cC cA cB sstr2 com12
    cC cB wss cB cA wss cC cA wss cC cB cA sstr2 com12 anim12i cA cB eqss cC cA
    wss cC cB wss dfbi2 3imtr4i $.

  $( Equality theorem for the subclass relationship.  (Contributed by NM,
     31-May-1999.) $)
  sseq12 $p |- ( ( A = B /\ C = D ) -> ( A C_ C <-> B C_ D ) ) $=
    cA cB wceq cA cC wss cB cC wss cC cD wceq cB cD wss cA cB cC sseq1 cC cD cB
    sseq2 sylan9bb $.

  ${
    sseq1i.1 $e |- A = B $.
    $( An equality inference for the subclass relationship.  (Contributed by
       NM, 18-Aug-1993.) $)
    sseq1i $p |- ( A C_ C <-> B C_ C ) $=
      cA cB wceq cA cC wss cB cC wss wb sseq1i.1 cA cB cC sseq1 ax-mp $.

    $( An equality inference for the subclass relationship.  (Contributed by
       NM, 30-Aug-1993.) $)
    sseq2i $p |- ( C C_ A <-> C C_ B ) $=
      cA cB wceq cC cA wss cC cB wss wb sseq1i.1 cA cB cC sseq2 ax-mp $.

    ${
      sseq12i.2 $e |- C = D $.
      $( An equality inference for the subclass relationship.  (Contributed by
         NM, 31-May-1999.)  (Proof shortened by Eric Schmidt, 26-Jan-2007.) $)
      sseq12i $p |- ( A C_ C <-> B C_ D ) $=
        cA cB wceq cC cD wceq cA cC wss cB cD wss wb sseq1i.1 sseq12i.2 cA cB
        cC cD sseq12 mp2an $.
    $}
  $}

  ${
    sseq1d.1 $e |- ( ph -> A = B ) $.
    $( An equality deduction for the subclass relationship.  (Contributed by
       NM, 14-Aug-1994.) $)
    sseq1d $p |- ( ph -> ( A C_ C <-> B C_ C ) ) $=
      wph cA cB wceq cA cC wss cB cC wss wb sseq1d.1 cA cB cC sseq1 syl $.

    $( An equality deduction for the subclass relationship.  (Contributed by
       NM, 14-Aug-1994.) $)
    sseq2d $p |- ( ph -> ( C C_ A <-> C C_ B ) ) $=
      wph cA cB wceq cC cA wss cC cB wss wb sseq1d.1 cA cB cC sseq2 syl $.

    ${
      sseq12d.2 $e |- ( ph -> C = D ) $.
      $( An equality deduction for the subclass relationship.  (Contributed by
         NM, 31-May-1999.) $)
      sseq12d $p |- ( ph -> ( A C_ C <-> B C_ D ) ) $=
        wph cA cC wss cB cC wss cB cD wss wph cA cB cC sseq1d.1 sseq1d wph cC
        cD cB sseq12d.2 sseq2d bitrd $.
    $}
  $}

  ${
    eqsstr.1 $e |- A = B $.
    eqsstr.2 $e |- B C_ C $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 16-Jul-1995.) $)
    eqsstri $p |- A C_ C $=
      cA cC wss cB cC wss eqsstr.2 cA cB cC eqsstr.1 sseq1i mpbir $.
  $}

  ${
    eqsstr3.1 $e |- B = A $.
    eqsstr3.2 $e |- B C_ C $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 19-Oct-1999.) $)
    eqsstr3i $p |- A C_ C $=
      cA cB cC cB cA eqsstr3.1 eqcomi eqsstr3.2 eqsstri $.
  $}

  ${
    sseqtr.1 $e |- A C_ B $.
    sseqtr.2 $e |- B = C $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 28-Jul-1995.) $)
    sseqtri $p |- A C_ C $=
      cA cB wss cA cC wss sseqtr.1 cB cC cA sseqtr.2 sseq2i mpbi $.
  $}

  ${
    sseqtr4.1 $e |- A C_ B $.
    sseqtr4.2 $e |- C = B $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 4-Apr-1995.) $)
    sseqtr4i $p |- A C_ C $=
      cA cB cC sseqtr4.1 cC cB sseqtr4.2 eqcomi sseqtri $.
  $}

  ${
    eqsstrd.1 $e |- ( ph -> A = B ) $.
    eqsstrd.2 $e |- ( ph -> B C_ C ) $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
    eqsstrd $p |- ( ph -> A C_ C ) $=
      wph cA cC wss cB cC wss eqsstrd.2 wph cA cB cC eqsstrd.1 sseq1d mpbird $.
  $}

  ${
    eqsstr3d.1 $e |- ( ph -> B = A ) $.
    eqsstr3d.2 $e |- ( ph -> B C_ C ) $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
    eqsstr3d $p |- ( ph -> A C_ C ) $=
      wph cA cB cC wph cB cA eqsstr3d.1 eqcomd eqsstr3d.2 eqsstrd $.
  $}

  ${
    sseqtrd.1 $e |- ( ph -> A C_ B ) $.
    sseqtrd.2 $e |- ( ph -> B = C ) $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
    sseqtrd $p |- ( ph -> A C_ C ) $=
      wph cA cB wss cA cC wss sseqtrd.1 wph cB cC cA sseqtrd.2 sseq2d mpbid $.
  $}

  ${
    sseqtr4d.1 $e |- ( ph -> A C_ B ) $.
    sseqtr4d.2 $e |- ( ph -> C = B ) $.
    $( Substitution of equality into a subclass relationship.  (Contributed by
       NM, 25-Apr-2004.) $)
    sseqtr4d $p |- ( ph -> A C_ C ) $=
      wph cA cB cC sseqtr4d.1 wph cC cB sseqtr4d.2 eqcomd sseqtrd $.
  $}

  ${
    3sstr3.1 $e |- A C_ B $.
    3sstr3.2 $e |- A = C $.
    3sstr3.3 $e |- B = D $.
    $( Substitution of equality in both sides of a subclass relationship.
       (Contributed by NM, 13-Jan-1996.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
    3sstr3i $p |- C C_ D $=
      cA cB wss cC cD wss 3sstr3.1 cA cC cB cD 3sstr3.2 3sstr3.3 sseq12i mpbi
      $.
  $}

  ${
    3sstr4.1 $e |- A C_ B $.
    3sstr4.2 $e |- C = A $.
    3sstr4.3 $e |- D = B $.
    $( Substitution of equality in both sides of a subclass relationship.
       (Contributed by NM, 13-Jan-1996.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
    3sstr4i $p |- C C_ D $=
      cC cD wss cA cB wss 3sstr4.1 cC cA cD cB 3sstr4.2 3sstr4.3 sseq12i mpbir
      $.
  $}

  ${
    3sstr3g.1 $e |- ( ph -> A C_ B ) $.
    3sstr3g.2 $e |- A = C $.
    3sstr3g.3 $e |- B = D $.
    $( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 1-Oct-2000.) $)
    3sstr3g $p |- ( ph -> C C_ D ) $=
      wph cA cB wss cC cD wss 3sstr3g.1 cA cC cB cD 3sstr3g.2 3sstr3g.3 sseq12i
      sylib $.
  $}

  ${
    3sstr4g.1 $e |- ( ph -> A C_ B ) $.
    3sstr4g.2 $e |- C = A $.
    3sstr4g.3 $e |- D = B $.
    $( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 16-Aug-1994.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
    3sstr4g $p |- ( ph -> C C_ D ) $=
      wph cA cB wss cC cD wss 3sstr4g.1 cC cA cD cB 3sstr4g.2 3sstr4g.3 sseq12i
      sylibr $.
  $}

  ${
    3sstr3d.1 $e |- ( ph -> A C_ B ) $.
    3sstr3d.2 $e |- ( ph -> A = C ) $.
    3sstr3d.3 $e |- ( ph -> B = D ) $.
    $( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 1-Oct-2000.) $)
    3sstr3d $p |- ( ph -> C C_ D ) $=
      wph cA cB wss cC cD wss 3sstr3d.1 wph cA cC cB cD 3sstr3d.2 3sstr3d.3
      sseq12d mpbid $.
  $}

  ${
    3sstr4d.1 $e |- ( ph -> A C_ B ) $.
    3sstr4d.2 $e |- ( ph -> C = A ) $.
    3sstr4d.3 $e |- ( ph -> D = B ) $.
    $( Substitution of equality into both sides of a subclass relationship.
       (Contributed by NM, 30-Nov-1995.)  (Proof shortened by Eric Schmidt,
       26-Jan-2007.) $)
    3sstr4d $p |- ( ph -> C C_ D ) $=
      wph cC cD wss cA cB wss 3sstr4d.1 wph cC cA cD cB 3sstr4d.2 3sstr4d.3
      sseq12d mpbird $.
  $}

  ${
    syl5eqss.1 $e |- A = B $.
    syl5eqss.2 $e |- ( ph -> B C_ C ) $.
    $( B chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
    syl5eqss $p |- ( ph -> A C_ C ) $=
      wph cB cC wss cA cC wss syl5eqss.2 cA cB cC syl5eqss.1 sseq1i sylibr $.
  $}

  ${
    syl5eqssr.1 $e |- B = A $.
    syl5eqssr.2 $e |- ( ph -> B C_ C ) $.
    $( B chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
    syl5eqssr $p |- ( ph -> A C_ C ) $=
      wph cA cB cC cB cA syl5eqssr.1 eqcomi syl5eqssr.2 syl5eqss $.
  $}

  ${
    syl6sseq.1 $e |- ( ph -> A C_ B ) $.
    syl6sseq.2 $e |- B = C $.
    $( A chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
    syl6sseq $p |- ( ph -> A C_ C ) $=
      wph cA cB wss cA cC wss syl6sseq.1 cB cC cA syl6sseq.2 sseq2i sylib $.
  $}

  ${
    syl6ssr.1 $e |- ( ph -> A C_ B ) $.
    syl6ssr.2 $e |- C = B $.
    $( A chained subclass and equality deduction.  (Contributed by NM,
       25-Apr-2004.) $)
    syl6sseqr $p |- ( ph -> A C_ C ) $=
      wph cA cB cC syl6ssr.1 cC cB syl6ssr.2 eqcomi syl6sseq $.
  $}

  ${
    syl5sseq.1 $e |- B C_ A $.
    syl5sseq.2 $e |- ( ph -> A = C ) $.
    $( Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    syl5sseq $p |- ( ph -> B C_ C ) $=
      wph cA cC wceq cB cA wss cB cC wss syl5sseq.2 syl5sseq.1 cA cC wceq cB cA
      wss cB cC wss cA cC cB sseq2 biimpa sylancl $.
  $}

  ${
    syl5sseqr.1 $e |- B C_ A $.
    syl5sseqr.2 $e |- ( ph -> C = A ) $.
    $( Subclass transitivity deduction.  (Contributed by Jonathan Ben-Naim,
       3-Jun-2011.) $)
    syl5sseqr $p |- ( ph -> B C_ C ) $=
      wph cB cA cC cB cA wss wph syl5sseqr.1 a1i syl5sseqr.2 sseqtr4d $.
  $}

  ${
    syl6eqss.1 $e |- ( ph -> A = B ) $.
    syl6eqss.2 $e |- B C_ C $.
    $( A chained subclass and equality deduction.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    syl6eqss $p |- ( ph -> A C_ C ) $=
      wph cA cB cC syl6eqss.1 cB cC wss wph syl6eqss.2 a1i eqsstrd $.
  $}

  ${
    syl6eqssr.1 $e |- ( ph -> B = A ) $.
    syl6eqssr.2 $e |- B C_ C $.
    $( A chained subclass and equality deduction.  (Contributed by Mario
       Carneiro, 2-Jan-2017.) $)
    syl6eqssr $p |- ( ph -> A C_ C ) $=
      wph cA cB cC wph cB cA syl6eqssr.1 eqcomd syl6eqssr.2 syl6eqss $.
  $}

  $( Equality implies the subclass relation.  (Contributed by NM, 5-Aug-1993.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
  eqimss $p |- ( A = B -> A C_ B ) $=
    cA cB wceq cA cB wss cB cA wss cA cB eqss simplbi $.

  $( Equality implies the subclass relation.  (Contributed by NM,
     23-Nov-2003.) $)
  eqimss2 $p |- ( B = A -> A C_ B ) $=
    cA cB wss cA cB cA cB eqimss eqcoms $.

  ${
    eqimssi.1 $e |- A = B $.
    $( Infer subclass relationship from equality.  (Contributed by NM,
       6-Jan-2007.) $)
    eqimssi $p |- A C_ B $=
      cA cA cB cA ssid eqimssi.1 sseqtri $.

    $( Infer subclass relationship from equality.  (Contributed by NM,
       7-Jan-2007.) $)
    eqimss2i $p |- B C_ A $=
      cB cB cA cB ssid eqimssi.1 sseqtr4i $.
  $}

  $( Two classes are different if they don't include the same class.
     (Contributed by NM, 23-Apr-2015.) $)
  nssne1 $p |- ( ( A C_ B /\ -. A C_ C ) -> B =/= C ) $=
    cA cB wss cA cC wss wn cB cC wne cA cB wss cA cC wss cB cC cB cC wceq cA cB
    wss cA cC wss cB cC cA sseq2 biimpcd necon3bd imp $.

  $( Two classes are different if they are not subclasses of the same class.
     (Contributed by NM, 23-Apr-2015.) $)
  nssne2 $p |- ( ( A C_ C /\ -. B C_ C ) -> A =/= B ) $=
    cA cC wss cB cC wss wn cA cB wne cA cC wss cB cC wss cA cB cA cB wceq cA cC
    wss cB cC wss cA cB cC sseq1 biimpcd necon3bd imp $.

  ${
    $d x A $.  $d x B $.
    $( Negation of subclass relationship.  Exercise 13 of [TakeutiZaring]
       p. 18.  (Contributed by NM, 25-Feb-1996.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.) $)
    nss $p |- ( -. A C_ B <-> E. x ( x e. A /\ -. x e. B ) ) $=
      vx cv cA wcel vx cv cB wcel wn wa vx wex cA cB wss wn vx cv cA wcel vx cv
      cB wcel wn wa vx wex vx cv cA wcel vx cv cB wcel wi vx wal cA cB wss vx
      cv cA wcel vx cv cB wcel vx exanali vx cA cB dfss2 xchbinxr bicomi $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Quantification restricted to a subclass.  (Contributed by NM,
       11-Mar-2006.) $)
    ssralv $p |- ( A C_ B -> ( A. x e. B ph -> A. x e. A ph ) ) $=
      cA cB wss wph wph vx cB cA cA cB wss vx cv cA wcel vx cv cB wcel wph cA
      cB vx cv ssel imim1d ralimdv2 $.

    $( Existential quantification restricted to a subclass.  (Contributed by
       NM, 11-Jan-2007.) $)
    ssrexv $p |- ( A C_ B -> ( E. x e. A ph -> E. x e. B ph ) ) $=
      cA cB wss wph wph vx cA cB cA cB wss vx cv cA wcel vx cv cB wcel wph cA
      cB vx cv ssel anim1d reximdv2 $.
  $}

  ${
    $d A x $.  $d B x $.
    $( Restricted universal quantification on a subset in terms of superset.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    ralss $p |- ( A C_ B -> ( A. x e. A ph <->
          A. x e. B ( x e. A -> ph ) ) ) $=
      cA cB wss wph vx cv cA wcel wph wi vx cA cB cA cB wss vx cv cA wcel wph
      wi vx cv cB wcel vx cv cA wcel wa wph wi vx cv cB wcel vx cv cA wcel wph
      wi wi cA cB wss vx cv cA wcel vx cv cB wcel vx cv cA wcel wa wph cA cB
      wss vx cv cA wcel vx cv cB wcel cA cB vx cv ssel pm4.71rd imbi1d vx cv cB
      wcel vx cv cA wcel wph impexp syl6bb ralbidv2 $.

    $( Restricted existential quantification on a subset in terms of superset.
       (Contributed by Stefan O'Rear, 3-Apr-2015.) $)
    rexss $p |- ( A C_ B -> ( E. x e. A ph <->
          E. x e. B ( x e. A /\ ph ) ) ) $=
      cA cB wss wph vx cv cA wcel wph wa vx cA cB cA cB wss vx cv cA wcel wph
      wa vx cv cB wcel vx cv cA wcel wa wph wa vx cv cB wcel vx cv cA wcel wph
      wa wa cA cB wss vx cv cA wcel vx cv cB wcel vx cv cA wcel wa wph cA cB
      wss vx cv cA wcel vx cv cB wcel cA cB vx cv ssel pm4.71rd anbi1d vx cv cB
      wcel vx cv cA wcel wph anass syl6bb rexbidv2 $.
  $}

  ${
    $d ph y $.  $d ps y $.  $d x y $.
    $( Class abstractions in a subclass relationship.  (Contributed by NM,
       3-Jul-1994.) $)
    ss2ab $p |- ( { x | ph } C_ { x | ps } <-> A. x ( ph -> ps ) ) $=
      wph vx cab wps vx cab wss vx cv wph vx cab wcel vx cv wps vx cab wcel wi
      vx wal wph wps wi vx wal vx wph vx cab wps vx cab wph vx nfab1 wps vx
      nfab1 dfss2f vx cv wph vx cab wcel vx cv wps vx cab wcel wi wph wps wi vx
      vx cv wph vx cab wcel wph vx cv wps vx cab wcel wps wph vx abid wps vx
      abid imbi12i albii bitri $.
  $}

  ${
    $d x A $.
    $( Class abstraction in a subclass relationship.  (Contributed by NM,
       16-Aug-2006.) $)
    abss $p |- ( { x | ph } C_ A <-> A. x ( ph -> x e. A ) ) $=
      wph vx cab cA wss wph vx cab vx cv cA wcel vx cab wss wph vx cv cA wcel
      wi vx wal vx cv cA wcel vx cab cA wph vx cab vx cA abid2 sseq2i wph vx cv
      cA wcel vx ss2ab bitr3i $.

    $( Subclass of a class abstraction.  (Contributed by NM, 16-Aug-2006.) $)
    ssab $p |- ( A C_ { x | ph } <-> A. x ( x e. A -> ph ) ) $=
      cA wph vx cab wss vx cv cA wcel vx cab wph vx cab wss vx cv cA wcel wph
      wi vx wal vx cv cA wcel vx cab cA wph vx cab vx cA abid2 sseq1i vx cv cA
      wcel wph vx ss2ab bitr3i $.

    $( The relation for a subclass of a class abstraction is equivalent to
       restricted quantification.  (Contributed by NM, 6-Sep-2006.) $)
    ssabral $p |- ( A C_ { x | ph } <-> A. x e. A ph ) $=
      cA wph vx cab wss vx cv cA wcel wph wi vx wal wph vx cA wral wph vx cA
      ssab wph vx cA df-ral bitr4i $.
  $}

  ${
    ss2abi.1 $e |- ( ph -> ps ) $.
    $( Inference of abstraction subclass from implication.  (Contributed by NM,
       31-Mar-1995.) $)
    ss2abi $p |- { x | ph } C_ { x | ps } $=
      wph vx cab wps vx cab wss wph wps wi vx wph wps vx ss2ab ss2abi.1 mpgbir
      $.
  $}

  ${
    $d x ph $.
    ss2abdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction of abstraction subclass from implication.  (Contributed by NM,
       29-Jul-2011.) $)
    ss2abdv $p |- ( ph -> { x | ps } C_ { x | ch } ) $=
      wph wps wch wi vx wal wps vx cab wch vx cab wss wph wps wch wi vx
      ss2abdv.1 alrimiv wps wch vx ss2ab sylibr $.
  $}

  ${
    $d x ph $.  $d x A $.
    abssdv.1 $e |- ( ph -> ( ps -> x e. A ) ) $.
    $( Deduction of abstraction subclass from implication.  (Contributed by NM,
       20-Jan-2006.) $)
    abssdv $p |- ( ph -> { x | ps } C_ A ) $=
      wph wps vx cv cA wcel wi vx wal wps vx cab cA wss wph wps vx cv cA wcel
      wi vx abssdv.1 alrimiv wps vx cA abss sylibr $.
  $}

  ${
    $d x A $.
    abssi.1 $e |- ( ph -> x e. A ) $.
    $( Inference of abstraction subclass from implication.  (Contributed by NM,
       20-Jan-2006.) $)
    abssi $p |- { x | ph } C_ A $=
      wph vx cab vx cv cA wcel vx cab cA wph vx cv cA wcel vx abssi.1 ss2abi vx
      cA abid2 sseqtri $.
  $}

  $( Restricted abstraction classes in a subclass relationship.  (Contributed
     by NM, 30-May-1999.) $)
  ss2rab $p |- ( { x e. A | ph } C_ { x e. A | ps } <->
               A. x e. A ( ph -> ps ) ) $=
    wph vx cA crab wps vx cA crab wss vx cv cA wcel wph wa vx cab vx cv cA wcel
    wps wa vx cab wss vx cv cA wcel wph wa vx cv cA wcel wps wa wi vx wal wph
    wps wi vx cA wral wph vx cA crab vx cv cA wcel wph wa vx cab wps vx cA crab
    vx cv cA wcel wps wa vx cab wph vx cA df-rab wps vx cA df-rab sseq12i vx cv
    cA wcel wph wa vx cv cA wcel wps wa vx ss2ab wph wps wi vx cA wral vx cv cA
    wcel wph wps wi wi vx wal vx cv cA wcel wph wa vx cv cA wcel wps wa wi vx
    wal wph wps wi vx cA df-ral vx cv cA wcel wph wps wi wi vx cv cA wcel wph
    wa vx cv cA wcel wps wa wi vx vx cv cA wcel wph wps imdistan albii bitr2i
    3bitri $.

  ${
    $d x B $.
    $( Restricted class abstraction in a subclass relationship.  (Contributed
       by NM, 16-Aug-2006.) $)
    rabss $p |- ( { x e. A | ph } C_ B <-> A. x e. A ( ph -> x e. B ) ) $=
      wph vx cA crab cB wss vx cv cA wcel wph wa vx cab cB wss vx cv cA wcel
      wph wa vx cv cB wcel wi vx wal wph vx cv cB wcel wi vx cA wral wph vx cA
      crab vx cv cA wcel wph wa vx cab cB wph vx cA df-rab sseq1i vx cv cA wcel
      wph wa vx cB abss vx cv cA wcel wph wa vx cv cB wcel wi vx wal vx cv cA
      wcel wph vx cv cB wcel wi wi vx wal wph vx cv cB wcel wi vx cA wral vx cv
      cA wcel wph wa vx cv cB wcel wi vx cv cA wcel wph vx cv cB wcel wi wi vx
      vx cv cA wcel wph vx cv cB wcel impexp albii wph vx cv cB wcel wi vx cA
      df-ral bitr4i 3bitri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Subclass of a restricted class abstraction.  (Contributed by NM,
       16-Aug-2006.) $)
    ssrab $p |- ( B C_ { x e. A | ph } <-> ( B C_ A /\ A. x e. B ph ) ) $=
      cB wph vx cA crab wss cB vx cv cA wcel wph wa vx cab wss vx cv cB wcel vx
      cv cA wcel wph wa wi vx wal cB cA wss wph vx cB wral wa wph vx cA crab vx
      cv cA wcel wph wa vx cab cB wph vx cA df-rab sseq2i vx cv cA wcel wph wa
      vx cB ssab cB cA wss wph vx cB wral wa vx cv cA wcel vx cB wral wph vx cB
      wral wa vx cv cA wcel wph wa vx cB wral vx cv cB wcel vx cv cA wcel wph
      wa wi vx wal cB cA wss vx cv cA wcel vx cB wral wph vx cB wral vx cB cA
      dfss3 anbi1i vx cv cA wcel wph vx cB r19.26 vx cv cA wcel wph wa vx cB
      df-ral 3bitr2ri 3bitri $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    ssrabdv.1 $e |- ( ph -> B C_ A ) $.
    ssrabdv.2 $e |- ( ( ph /\ x e. B ) -> ps ) $.
    $( Subclass of a restricted class abstraction (deduction rule).
       (Contributed by NM, 31-Aug-2006.) $)
    ssrabdv $p |- ( ph -> B C_ { x e. A | ps } ) $=
      wph cB cA wss wps vx cB wral cB wps vx cA crab wss ssrabdv.1 wph wps vx
      cB ssrabdv.2 ralrimiva wps vx cA cB ssrab sylanbrc $.
  $}

  ${
    $d x B $.  $d x ph $.
    rabssdv.1 $e |- ( ( ph /\ x e. A /\ ps ) -> x e. B ) $.
    $( Subclass of a restricted class abstraction (deduction rule).
       (Contributed by NM, 2-Feb-2015.) $)
    rabssdv $p |- ( ph -> { x e. A | ps } C_ B ) $=
      wph wps vx cv cB wcel wi vx cA wral wps vx cA crab cB wss wph wps vx cv
      cB wcel wi vx cA wph vx cv cA wcel wps vx cv cB wcel rabssdv.1 3exp
      ralrimiv wps vx cA cB rabss sylibr $.
  $}

  ${
    $d x ph $.
    ss2rabdv.1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Deduction of restricted abstraction subclass from implication.
       (Contributed by NM, 30-May-2006.) $)
    ss2rabdv $p |- ( ph -> { x e. A | ps } C_ { x e. A | ch } ) $=
      wph wps wch wi vx cA wral wps vx cA crab wch vx cA crab wss wph wps wch
      wi vx cA ss2rabdv.1 ralrimiva wps wch vx cA ss2rab sylibr $.
  $}

  ${
    ss2rabi.1 $e |- ( x e. A -> ( ph -> ps ) ) $.
    $( Inference of restricted abstraction subclass from implication.
       (Contributed by NM, 14-Oct-1999.) $)
    ss2rabi $p |- { x e. A | ph } C_ { x e. A | ps } $=
      wph vx cA crab wps vx cA crab wss wph wps wi vx cA wph wps vx cA ss2rab
      ss2rabi.1 mprgbir $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Subclass law for restricted abstraction.  (Contributed by NM,
       18-Dec-2004.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
    rabss2 $p |- ( A C_ B -> { x e. A | ph } C_ { x e. B | ph } ) $=
      cA cB wss vx cv cA wcel wph wa vx cab vx cv cB wcel wph wa vx cab wph vx
      cA crab wph vx cB crab vx cv cA wcel vx cv cB wcel wi vx wal vx cv cA
      wcel wph wa vx cv cB wcel wph wa wi vx wal cA cB wss vx cv cA wcel wph wa
      vx cab vx cv cB wcel wph wa vx cab wss vx cv cA wcel vx cv cB wcel wi vx
      cv cA wcel wph wa vx cv cB wcel wph wa wi vx vx cv cA wcel vx cv cB wcel
      wph pm3.45 alimi vx cA cB dfss2 vx cv cA wcel wph wa vx cv cB wcel wph wa
      vx ss2ab 3imtr4i wph vx cA df-rab wph vx cB df-rab 3sstr4g $.

    $( Subclass relation for the restriction of a class abstraction.
       (Contributed by NM, 31-Mar-1995.) $)
    ssab2 $p |- { x | ( x e. A /\ ph ) } C_ A $=
      vx cv cA wcel wph wa vx cA vx cv cA wcel wph simpl abssi $.

    $( Subclass relation for a restricted class.  (Contributed by NM,
       19-Mar-1997.) $)
    ssrab2 $p |- { x e. A | ph } C_ A $=
      wph vx cA crab vx cv cA wcel wph wa vx cab cA wph vx cA df-rab wph vx cA
      ssab2 eqsstri $.
  $}

  $( A restricted class is a subclass of the corresponding unrestricted class.
     (Contributed by Mario Carneiro, 23-Dec-2016.) $)
  rabssab $p |- { x e. A | ph } C_ { x | ph } $=
    wph vx cA crab vx cv cA wcel wph wa vx cab wph vx cab wph vx cA df-rab vx
    cv cA wcel wph wa wph vx vx cv cA wcel wph simpr ss2abi eqsstri $.

  ${
    $d x y $.  $d y z A $.  $d y z B $.  $d x z C $.
    $( A subset relationship useful for converting union to indexed union using
       ~ dfiun2 or ~ dfiun2g and intersection to indexed intersection using
       ~ dfiin2 .  (Contributed by NM, 5-Oct-2006.)  (Proof shortened by Mario
       Carneiro, 26-Sep-2015.) $)
    uniiunlem $p |- ( A. x e. A B e. D ->
                     ( A. x e. A B e. C <-> { y | E. x e. A y = B } C_ C ) ) $=
      vy cv cB wceq vx cA wrex vy cab cC wss vz cv cB wceq vz cv cC wcel wi vz
      wal vx cA wral cB cD wcel vx cA wral cB cC wcel vx cA wral vy cv cB wceq
      vx cA wrex vy cab cC wss vz cv cB wceq vx cA wrex vz cab cC wss vz cv cB
      wceq vz cv cC wcel wi vz wal vx cA wral vy cv cB wceq vx cA wrex vy cab
      vz cv cB wceq vx cA wrex vz cab cC vy cv cB wceq vx cA wrex vz cv cB wceq
      vx cA wrex vy vz vy cv vz cv wceq vy cv cB wceq vz cv cB wceq vx cA vy cv
      vz cv cB eqeq1 rexbidv cbvabv sseq1i vz cv cB wceq vz cv cC wcel wi vx cA
      wral vz wal vz cv cB wceq vx cA wrex vz cv cC wcel wi vz wal vz cv cB
      wceq vz cv cC wcel wi vz wal vx cA wral vz cv cB wceq vx cA wrex vz cab
      cC wss vz cv cB wceq vz cv cC wcel wi vx cA wral vz cv cB wceq vx cA wrex
      vz cv cC wcel wi vz vz cv cB wceq vz cv cC wcel vx cA r19.23v albii vz cv
      cB wceq vz cv cC wcel wi vx vz cA ralcom4 vz cv cB wceq vx cA wrex vz cC
      abss 3bitr4i bitr4i cB cD wcel vx cA wral vz cv cB wceq vz cv cC wcel wi
      vz wal cB cC wcel wb vx cA wral vz cv cB wceq vz cv cC wcel wi vz wal vx
      cA wral cB cC wcel vx cA wral wb cB cD wcel vz cv cB wceq vz cv cC wcel
      wi vz wal cB cC wcel wb vx cA vz cv cC wcel cB cC wcel vz cB cD cB cC
      wcel vz nfv vz cv cB cC eleq1 ceqsalg ralimi vz cv cB wceq vz cv cC wcel
      wi vz wal cB cC wcel vx cA ralbi syl syl5rbb $.
  $}

  $( Alternate definition of proper subclass.  (Contributed by NM,
     7-Feb-1996.) $)
  dfpss2 $p |- ( A C. B <-> ( A C_ B /\ -. A = B ) ) $=
    cA cB wpss cA cB wss cA cB wne wa cA cB wss cA cB wceq wn wa cA cB df-pss
    cA cB wne cA cB wceq wn cA cB wss cA cB df-ne anbi2i bitri $.

  $( Alternate definition of proper subclass.  (Contributed by NM,
     7-Feb-1996.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  dfpss3 $p |- ( A C. B <-> ( A C_ B /\ -. B C_ A ) ) $=
    cA cB wpss cA cB wss cA cB wceq wn wa cA cB wss cB cA wss wn wa cA cB
    dfpss2 cA cB wss cA cB wceq wn cB cA wss wn cA cB wss cA cB wceq cB cA wss
    cA cB wceq cA cB wss cB cA wss cA cB eqss baib notbid pm5.32i bitri $.

  $( Equality theorem for proper subclass.  (Contributed by NM, 7-Feb-1996.) $)
  psseq1 $p |- ( A = B -> ( A C. C <-> B C. C ) ) $=
    cA cB wceq cA cC wss cA cC wne wa cB cC wss cB cC wne wa cA cC wpss cB cC
    wpss cA cB wceq cA cC wss cB cC wss cA cC wne cB cC wne cA cB cC sseq1 cA
    cB cC neeq1 anbi12d cA cC df-pss cB cC df-pss 3bitr4g $.

  $( Equality theorem for proper subclass.  (Contributed by NM, 7-Feb-1996.) $)
  psseq2 $p |- ( A = B -> ( C C. A <-> C C. B ) ) $=
    cA cB wceq cC cA wss cC cA wne wa cC cB wss cC cB wne wa cC cA wpss cC cB
    wpss cA cB wceq cC cA wss cC cB wss cC cA wne cC cB wne cA cB cC sseq2 cA
    cB cC neeq2 anbi12d cC cA df-pss cC cB df-pss 3bitr4g $.

  ${
    psseq1i.1 $e |- A = B $.
    $( An equality inference for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
    psseq1i $p |- ( A C. C <-> B C. C ) $=
      cA cB wceq cA cC wpss cB cC wpss wb psseq1i.1 cA cB cC psseq1 ax-mp $.

    $( An equality inference for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
    psseq2i $p |- ( C C. A <-> C C. B ) $=
      cA cB wceq cC cA wpss cC cB wpss wb psseq1i.1 cA cB cC psseq2 ax-mp $.

    ${
      psseq12i.2 $e |- C = D $.
      $( An equality inference for the proper subclass relationship.
         (Contributed by NM, 9-Jun-2004.) $)
      psseq12i $p |- ( A C. C <-> B C. D ) $=
        cA cC wpss cB cC wpss cB cD wpss cA cB cC psseq1i.1 psseq1i cC cD cB
        psseq12i.2 psseq2i bitri $.
    $}
  $}

  ${
    psseq1d.1 $e |- ( ph -> A = B ) $.
    $( An equality deduction for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
    psseq1d $p |- ( ph -> ( A C. C <-> B C. C ) ) $=
      wph cA cB wceq cA cC wpss cB cC wpss wb psseq1d.1 cA cB cC psseq1 syl $.

    $( An equality deduction for the proper subclass relationship.
       (Contributed by NM, 9-Jun-2004.) $)
    psseq2d $p |- ( ph -> ( C C. A <-> C C. B ) ) $=
      wph cA cB wceq cC cA wpss cC cB wpss wb psseq1d.1 cA cB cC psseq2 syl $.

    ${
      psseq12d.2 $e |- ( ph -> C = D ) $.
      $( An equality deduction for the proper subclass relationship.
         (Contributed by NM, 9-Jun-2004.) $)
      psseq12d $p |- ( ph -> ( A C. C <-> B C. D ) ) $=
        wph cA cC wpss cB cC wpss cB cD wpss wph cA cB cC psseq1d.1 psseq1d wph
        cC cD cB psseq12d.2 psseq2d bitrd $.
    $}
  $}

  $( A proper subclass is a subclass.  Theorem 10 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)
  pssss $p |- ( A C. B -> A C_ B ) $=
    cA cB wpss cA cB wss cA cB wne cA cB df-pss simplbi $.

  $( Two classes in a proper subclass relationship are not equal.  (Contributed
     by NM, 16-Feb-2015.) $)
  pssne $p |- ( A C. B -> A =/= B ) $=
    cA cB wpss cA cB wss cA cB wne cA cB df-pss simprbi $.

  ${
    pssssd.1 $e |- ( ph -> A C. B ) $.
    $( Deduce subclass from proper subclass.  (Contributed by NM,
       29-Feb-1996.) $)
    pssssd $p |- ( ph -> A C_ B ) $=
      wph cA cB wpss cA cB wss pssssd.1 cA cB pssss syl $.

    $( Proper subclasses are unequal.  Deduction form of ~ pssne .
       (Contributed by David Moews, 1-May-2017.) $)
    pssned $p |- ( ph -> A =/= B ) $=
      wph cA cB wpss cA cB wne pssssd.1 cA cB pssne syl $.
  $}

  $( Subclass in terms of proper subclass.  (Contributed by NM,
     25-Feb-1996.) $)
  sspss $p |- ( A C_ B <-> ( A C. B \/ A = B ) ) $=
    cA cB wss cA cB wpss cA cB wceq wo cA cB wss cA cB wpss cA cB wceq cA cB
    wss cA cB wceq cA cB wpss cA cB wpss cA cB wss cA cB wceq wn cA cB dfpss2
    simplbi2 con1d orrd cA cB wpss cA cB wss cA cB wceq cA cB pssss cA cB
    eqimss jaoi impbii $.

  $( Proper subclass is irreflexive.  Theorem 7 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)
  pssirr $p |- -. A C. A $=
    cA cA wpss cA cA wss cA cA wss wn wa cA cA wss pm3.24 cA cA dfpss3 mtbir $.

  $( Proper subclass has no 2-cycle loops.  Compare Theorem 8 of [Suppes]
     p. 23.  (Contributed by NM, 7-Feb-1996.)  (Proof shortened by Andrew
     Salmon, 26-Jun-2011.) $)
  pssn2lp $p |- -. ( A C. B /\ B C. A ) $=
    cA cB wpss cB cA wpss wn wi cA cB wpss cB cA wpss wa wn cA cB wpss cB cA
    wss cB cA wpss cA cB wpss cA cB wss cB cA wss wn cA cB dfpss3 simprbi cB cA
    pssss nsyl cA cB wpss cB cA wpss imnan mpbi $.

  $( Two ways of stating trichotomy with respect to inclusion.  (Contributed by
     NM, 12-Aug-2004.) $)
  sspsstri $p |- ( ( A C_ B \/ B C_ A ) <-> ( A C. B \/ A = B \/ B C. A ) ) $=
    cA cB wpss cB cA wpss wo cA cB wceq wo cA cB wpss cA cB wceq wo cB cA wpss
    wo cA cB wss cB cA wss wo cA cB wpss cA cB wceq cB cA wpss w3o cA cB wpss
    cB cA wpss cA cB wceq or32 cA cB wss cB cA wss wo cA cB wpss cA cB wceq wo
    cB cA wpss cA cB wceq wo wo cA cB wpss cB cA wpss wo cA cB wceq wo cA cB
    wss cA cB wpss cA cB wceq wo cB cA wss cB cA wpss cA cB wceq wo cA cB sspss
    cB cA wss cB cA wpss cB cA wceq wo cB cA wpss cA cB wceq wo cB cA sspss cB
    cA wceq cA cB wceq cB cA wpss cB cA eqcom orbi2i bitri orbi12i cA cB wpss
    cB cA wpss cA cB wceq orordir bitr4i cA cB wpss cA cB wceq cB cA wpss
    df-3or 3bitr4i $.

  $( Partial trichotomy law for subclasses.  (Contributed by NM, 16-May-1996.)
     (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  ssnpss $p |- ( A C_ B -> -. B C. A ) $=
    cB cA wpss cA cB wss cB cA wpss cB cA wss cA cB wss wn cB cA dfpss3 simprbi
    con2i $.

  $( Transitive law for proper subclass.  Theorem 9 of [Suppes] p. 23.
     (Contributed by NM, 7-Feb-1996.) $)
  psstr $p |- ( ( A C. B /\ B C. C ) -> A C. C ) $=
    cA cB wpss cB cC wpss wa cA cC wss cA cC wceq wn cA cC wpss cA cB wpss cB
    cC wpss cA cB cC cA cB pssss cB cC pssss sylan9ss cA cC wceq cA cB wpss cB
    cC wpss wa cA cC wceq cA cB wpss cB cC wpss wa cC cB wpss cB cC wpss wa cC
    cB pssn2lp cA cC wceq cA cB wpss cC cB wpss cB cC wpss cA cC cB psseq1
    anbi1d mtbiri con2i cA cC dfpss2 sylanbrc $.

  $( Transitive law for subclass and proper subclass.  (Contributed by NM,
     3-Apr-1996.) $)
  sspsstr $p |- ( ( A C_ B /\ B C. C ) -> A C. C ) $=
    cA cB wss cA cB wpss cA cB wceq wo cB cC wpss cA cC wpss cA cB sspss cA cB
    wpss cA cB wceq wo cB cC wpss cA cC wpss cA cB wpss cB cC wpss cA cC wpss
    wi cA cB wceq cA cB wpss cB cC wpss cA cC wpss cA cB cC psstr ex cA cB wceq
    cA cC wpss cB cC wpss cA cB cC psseq1 biimprd jaoi imp sylanb $.

  $( Transitive law for subclass and proper subclass.  (Contributed by NM,
     3-Apr-1996.) $)
  psssstr $p |- ( ( A C. B /\ B C_ C ) -> A C. C ) $=
    cB cC wss cA cB wpss cB cC wpss cB cC wceq wo cA cC wpss cB cC sspss cA cB
    wpss cB cC wpss cB cC wceq wo cA cC wpss cA cB wpss cB cC wpss cA cC wpss
    cB cC wceq cA cB wpss cB cC wpss cA cC wpss cA cB cC psstr ex cB cC wceq cA
    cB wpss cA cC wpss cB cC cA psseq2 biimpcd jaod imp sylan2b $.

  ${
    psstrd.1 $e |- ( ph -> A C. B ) $.
    psstrd.2 $e |- ( ph -> B C. C ) $.
    $( Proper subclass inclusion is transitive.  Deduction form of ~ psstr .
       (Contributed by David Moews, 1-May-2017.) $)
    psstrd $p |- ( ph -> A C. C ) $=
      wph cA cB wpss cB cC wpss cA cC wpss psstrd.1 psstrd.2 cA cB cC psstr
      syl2anc $.
  $}

  ${
    sspsstrd.1 $e |- ( ph -> A C_ B ) $.
    sspsstrd.2 $e |- ( ph -> B C. C ) $.
    $( Transitivity involving subclass and proper subclass inclusion.
       Deduction form of ~ sspsstr .  (Contributed by David Moews,
       1-May-2017.) $)
    sspsstrd $p |- ( ph -> A C. C ) $=
      wph cA cB wss cB cC wpss cA cC wpss sspsstrd.1 sspsstrd.2 cA cB cC
      sspsstr syl2anc $.
  $}

  ${
    psssstrd.1 $e |- ( ph -> A C. B ) $.
    psssstrd.2 $e |- ( ph -> B C_ C ) $.
    $( Transitivity involving subclass and proper subclass inclusion.
       Deduction form of ~ psssstr .  (Contributed by David Moews,
       1-May-2017.) $)
    psssstrd $p |- ( ph -> A C. C ) $=
      wph cA cB wpss cB cC wss cA cC wpss psssstrd.1 psssstrd.2 cA cB cC
      psssstr syl2anc $.
  $}

  $( A class is not a proper subclass of another iff it satisfies a
     one-directional form of ~ eqss .  (Contributed by Mario Carneiro,
     15-May-2015.) $)
  npss $p |- ( -. A C. B <-> ( A C_ B -> A = B ) ) $=
    cA cB wss cA cB wceq wi cA cB wpss cA cB wss cA cB wceq wi wn cA cB wss cA
    cB wceq wn wa cA cB wpss cA cB wss cA cB wceq pm4.61 cA cB dfpss2 bitr4i
    con1bii $.


