
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Negated_equality_and_membership.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Restricted quantification

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff notation to include restricted universal quantification. $)
  wral $a wff A. x e. A ph $.

  $( Extend wff notation to include restricted existential quantification. $)
  wrex $a wff E. x e. A ph $.

  $( Extend wff notation to include restricted existential uniqueness. $)
  wreu $a wff E! x e. A ph $.

  $( Extend wff notation to include restricted "at most one." $)
  wrmo $a wff E* x e. A ph $.

  $( Extend class notation to include the restricted class abstraction (class
     builder). $)
  crab $a class { x e. A | ph } $.

  $( Define restricted universal quantification.  Special case of Definition
     4.15(3) of [TakeutiZaring] p. 22.  (Contributed by NM, 19-Aug-1993.) $)
  df-ral $a |- ( A. x e. A ph <-> A. x ( x e. A -> ph ) ) $.

  $( Define restricted existential quantification.  Special case of Definition
     4.15(4) of [TakeutiZaring] p. 22.  (Contributed by NM, 30-Aug-1993.) $)
  df-rex $a |- ( E. x e. A ph <-> E. x ( x e. A /\ ph ) ) $.

  $( Define restricted existential uniqueness.  (Contributed by NM,
     22-Nov-1994.) $)
  df-reu $a |- ( E! x e. A ph <-> E! x ( x e. A /\ ph ) ) $.

  $( Define restricted "at most one".  (Contributed by NM, 16-Jun-2017.) $)
  df-rmo $a |- ( E* x e. A ph <-> E* x ( x e. A /\ ph ) ) $.

  $( Define a restricted class abstraction (class builder), which is the class
     of all ` x ` in ` A ` such that ` ph ` is true.  Definition of
     [TakeutiZaring] p. 20.  (Contributed by NM, 22-Nov-1994.) $)
  df-rab $a |- { x e. A | ph } = { x | ( x e. A /\ ph ) } $.

  $( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
  ralnex $p |- ( A. x e. A -. ph <-> -. E. x e. A ph ) $=
    wph wn vx cA wral vx cv cA wcel wph wn wi vx wal wph vx cA wrex wn wph wn
    vx cA df-ral vx cv cA wcel wph wn wi vx wal vx cv cA wcel wph wa vx wex wph
    vx cA wrex vx cv cA wcel wph vx alinexa wph vx cA df-rex xchbinxr bitri $.

  $( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
  rexnal $p |- ( E. x e. A -. ph <-> -. A. x e. A ph ) $=
    wph wn vx cA wrex vx cv cA wcel wph wn wa vx wex wph vx cA wral wn wph wn
    vx cA df-rex vx cv cA wcel wph wn wa vx wex vx cv cA wcel wph wi vx wal wph
    vx cA wral vx cv cA wcel wph vx exanali wph vx cA df-ral xchbinxr bitri $.

  $( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
  dfral2 $p |- ( A. x e. A ph <-> -. E. x e. A -. ph ) $=
    wph wn vx cA wrex wph vx cA wral wph vx cA rexnal con2bii $.

  $( Relationship between restricted universal and existential quantifiers.
     (Contributed by NM, 21-Jan-1997.) $)
  dfrex2 $p |- ( E. x e. A ph <-> -. A. x e. A -. ph ) $=
    wph wn vx cA wral wph vx cA wrex wph vx cA ralnex con2bii $.

  ${
    ralbida.1 $e |- F/ x ph $.
    ralbida.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 6-Oct-2003.) $)
    ralbida $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $=
      wph vx cv cA wcel wps wi vx wal vx cv cA wcel wch wi vx wal wps vx cA
      wral wch vx cA wral wph vx cv cA wcel wps wi vx cv cA wcel wch wi vx
      ralbida.1 wph vx cv cA wcel wps wch ralbida.2 pm5.74da albid wps vx cA
      df-ral wch vx cA df-ral 3bitr4g $.

    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 6-Oct-2003.) $)
    rexbida $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $=
      wph vx cv cA wcel wps wa vx wex vx cv cA wcel wch wa vx wex wps vx cA
      wrex wch vx cA wrex wph vx cv cA wcel wps wa vx cv cA wcel wch wa vx
      ralbida.1 wph vx cv cA wcel wps wch ralbida.2 pm5.32da exbid wps vx cA
      df-rex wch vx cA df-rex 3bitr4g $.
  $}

  ${
    $d x ph $.
    ralbidva.1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 4-Mar-1997.) $)
    ralbidva $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv ralbidva.1 ralbida $.

    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 9-Mar-1997.) $)
    rexbidva $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv ralbidva.1 rexbida $.
  $}

  ${
    ralbid.1 $e |- F/ x ph $.
    ralbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 27-Jun-1998.) $)
    ralbid $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $=
      wph wps wch vx cA ralbid.1 wph wps wch wb vx cv cA wcel ralbid.2 adantr
      ralbida $.

    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 27-Jun-1998.) $)
    rexbid $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $=
      wph wps wch vx cA ralbid.1 wph wps wch wb vx cv cA wcel ralbid.2 adantr
      rexbida $.
  $}

  ${
    $d x ph $.
    ralbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 20-Nov-1994.) $)
    ralbidv $p |- ( ph -> ( A. x e. A ps <-> A. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv ralbidv.1 ralbid $.

    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 20-Nov-1994.) $)
    rexbidv $p |- ( ph -> ( E. x e. A ps <-> E. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv ralbidv.1 rexbid $.
  $}

  ${
    $d x ph $.
    ralbidv2.1 $e |- ( ph -> ( ( x e. A -> ps ) <-> ( x e. B -> ch ) ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 6-Apr-1997.) $)
    ralbidv2 $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $=
      wph vx cv cA wcel wps wi vx wal vx cv cB wcel wch wi vx wal wps vx cA
      wral wch vx cB wral wph vx cv cA wcel wps wi vx cv cB wcel wch wi vx
      ralbidv2.1 albidv wps vx cA df-ral wch vx cB df-ral 3bitr4g $.
  $}

  ${
    $d x ph $.
    rexbidv2.1 $e |- ( ph -> ( ( x e. A /\ ps ) <-> ( x e. B /\ ch ) ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 22-May-1999.) $)
    rexbidv2 $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $=
      wph vx cv cA wcel wps wa vx wex vx cv cB wcel wch wa vx wex wps vx cA
      wrex wch vx cB wrex wph vx cv cA wcel wps wa vx cv cB wcel wch wa vx
      rexbidv2.1 exbidv wps vx cA df-rex wch vx cB df-rex 3bitr4g $.
  $}

  ${
    ralbii.1 $e |- ( ph <-> ps ) $.
    $( Inference adding restricted universal quantifier to both sides of an
       equivalence.  (Contributed by NM, 23-Nov-1994.)  (Revised by Mario
       Carneiro, 17-Oct-2016.) $)
    ralbii $p |- ( A. x e. A ph <-> A. x e. A ps ) $=
      wph vx cA wral wps vx cA wral wb wtru wph wps vx cA wph wps wb wtru
      ralbii.1 a1i ralbidv trud $.

    $( Inference adding restricted existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 23-Nov-1994.)  (Revised by Mario
       Carneiro, 17-Oct-2016.) $)
    rexbii $p |- ( E. x e. A ph <-> E. x e. A ps ) $=
      wph vx cA wrex wps vx cA wrex wb wtru wph wps vx cA wph wps wb wtru
      ralbii.1 a1i rexbidv trud $.

    $( Inference adding two restricted universal quantifiers to both sides of
       an equivalence.  (Contributed by NM, 1-Aug-2004.) $)
    2ralbii $p |- ( A. x e. A A. y e. B ph <-> A. x e. A A. y e. B ps ) $=
      wph vy cB wral wps vy cB wral vx cA wph wps vy cB ralbii.1 ralbii ralbii
      $.

    $( Inference adding two restricted existential quantifiers to both sides of
       an equivalence.  (Contributed by NM, 11-Nov-1995.) $)
    2rexbii $p |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps ) $=
      wph vy cB wrex wps vy cB wrex vx cA wph wps vy cB ralbii.1 rexbii rexbii
      $.
  $}

  ${
    ralbii2.1 $e |- ( ( x e. A -> ph ) <-> ( x e. B -> ps ) ) $.
    $( Inference adding different restricted universal quantifiers to each side
       of an equivalence.  (Contributed by NM, 15-Aug-2005.) $)
    ralbii2 $p |- ( A. x e. A ph <-> A. x e. B ps ) $=
      vx cv cA wcel wph wi vx wal vx cv cB wcel wps wi vx wal wph vx cA wral
      wps vx cB wral vx cv cA wcel wph wi vx cv cB wcel wps wi vx ralbii2.1
      albii wph vx cA df-ral wps vx cB df-ral 3bitr4i $.
  $}

  ${
    rexbii2.1 $e |- ( ( x e. A /\ ph ) <-> ( x e. B /\ ps ) ) $.
    $( Inference adding different restricted existential quantifiers to each
       side of an equivalence.  (Contributed by NM, 4-Feb-2004.) $)
    rexbii2 $p |- ( E. x e. A ph <-> E. x e. B ps ) $=
      vx cv cA wcel wph wa vx wex vx cv cB wcel wps wa vx wex wph vx cA wrex
      wps vx cB wrex vx cv cA wcel wph wa vx cv cB wcel wps wa vx rexbii2.1
      exbii wph vx cA df-rex wps vx cB df-rex 3bitr4i $.
  $}

  ${
    raleqbii.1 $e |- A = B $.
    raleqbii.2 $e |- ( ps <-> ch ) $.
    $( Equality deduction for restricted universal quantifier, changing both
       formula and quantifier domain.  Inference form.  (Contributed by David
       Moews, 1-May-2017.) $)
    raleqbii $p |- ( A. x e. A ps <-> A. x e. B ch ) $=
      wps wch vx cA cB vx cv cA wcel vx cv cB wcel wps wch cA cB vx cv
      raleqbii.1 eleq2i raleqbii.2 imbi12i ralbii2 $.

    $( Equality deduction for restricted existential quantifier, changing both
       formula and quantifier domain.  Inference form.  (Contributed by David
       Moews, 1-May-2017.) $)
    rexeqbii $p |- ( E. x e. A ps <-> E. x e. B ch ) $=
      wps wch vx cA cB vx cv cA wcel vx cv cB wcel wps wch cA cB vx cv
      raleqbii.1 eleq2i raleqbii.2 anbi12i rexbii2 $.
  $}

  ${
    ralbiia.1 $e |- ( x e. A -> ( ph <-> ps ) ) $.
    $( Inference adding restricted universal quantifier to both sides of an
       equivalence.  (Contributed by NM, 26-Nov-2000.) $)
    ralbiia $p |- ( A. x e. A ph <-> A. x e. A ps ) $=
      wph wps vx cA cA vx cv cA wcel wph wps ralbiia.1 pm5.74i ralbii2 $.

    $( Inference adding restricted existential quantifier to both sides of an
       equivalence.  (Contributed by NM, 26-Oct-1999.) $)
    rexbiia $p |- ( E. x e. A ph <-> E. x e. A ps ) $=
      wph wps vx cA cA vx cv cA wcel wph wps ralbiia.1 pm5.32i rexbii2 $.
  $}

  ${
    $d x y $.  $d y A $.
    2rexbiia.1 $e |- ( ( x e. A /\ y e. B ) -> ( ph <-> ps ) ) $.
    $( Inference adding two restricted existential quantifiers to both sides of
       an equivalence.  (Contributed by NM, 1-Aug-2004.) $)
    2rexbiia $p |- ( E. x e. A E. y e. B ph <-> E. x e. A E. y e. B ps ) $=
      wph vy cB wrex wps vy cB wrex vx cA vx cv cA wcel wph wps vy cB
      2rexbiia.1 rexbidva rexbiia $.
  $}

  ${
    $d x y $.
    r2alf.1 $e |- F/_ y A $.
    $( Double restricted universal quantification.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)
    r2alf $p |- ( A. x e. A A. y e. B ph <->
               A. x A. y ( ( x e. A /\ y e. B ) -> ph ) ) $=
      wph vy cB wral vx cA wral vx cv cA wcel wph vy cB wral wi vx wal vx cv cA
      wcel vy cv cB wcel wa wph wi vy wal vx wal wph vy cB wral vx cA df-ral vx
      cv cA wcel vy cv cB wcel wa wph wi vy wal vx cv cA wcel wph vy cB wral wi
      vx vx cv cA wcel vy cv cB wcel wph wi wi vy wal vx cv cA wcel vy cv cB
      wcel wph wi vy wal wi vx cv cA wcel vy cv cB wcel wa wph wi vy wal vx cv
      cA wcel wph vy cB wral wi vx cv cA wcel vy cv cB wcel wph wi vy vy vx cA
      r2alf.1 nfcri 19.21 vx cv cA wcel vy cv cB wcel wa wph wi vx cv cA wcel
      vy cv cB wcel wph wi wi vy vx cv cA wcel vy cv cB wcel wph impexp albii
      wph vy cB wral vy cv cB wcel wph wi vy wal vx cv cA wcel wph vy cB df-ral
      imbi2i 3bitr4i albii bitr4i $.

    $( Double restricted existential quantification.  (Contributed by Mario
       Carneiro, 14-Oct-2016.) $)
    r2exf $p |- ( E. x e. A E. y e. B ph <->
               E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) ) $=
      wph vy cB wrex vx cA wrex vx cv cA wcel wph vy cB wrex wa vx wex vx cv cA
      wcel vy cv cB wcel wa wph wa vy wex vx wex wph vy cB wrex vx cA df-rex vx
      cv cA wcel vy cv cB wcel wa wph wa vy wex vx cv cA wcel wph vy cB wrex wa
      vx vx cv cA wcel vy cv cB wcel wph wa wa vy wex vx cv cA wcel vy cv cB
      wcel wph wa vy wex wa vx cv cA wcel vy cv cB wcel wa wph wa vy wex vx cv
      cA wcel wph vy cB wrex wa vx cv cA wcel vy cv cB wcel wph wa vy vy vx cA
      r2alf.1 nfcri 19.42 vx cv cA wcel vy cv cB wcel wa wph wa vx cv cA wcel
      vy cv cB wcel wph wa wa vy vx cv cA wcel vy cv cB wcel wph anass exbii
      wph vy cB wrex vy cv cB wcel wph wa vy wex vx cv cA wcel wph vy cB df-rex
      anbi2i 3bitr4i exbii bitr4i $.
  $}

  ${
    $d x y $.  $d y A $.
    $( Double restricted universal quantification.  (Contributed by NM,
       19-Nov-1995.) $)
    r2al $p |- ( A. x e. A A. y e. B ph <->
               A. x A. y ( ( x e. A /\ y e. B ) -> ph ) ) $=
      wph vx vy cA cB vy cA nfcv r2alf $.

    $( Double restricted existential quantification.  (Contributed by NM,
       11-Nov-1995.) $)
    r2ex $p |- ( E. x e. A E. y e. B ph <->
               E. x E. y ( ( x e. A /\ y e. B ) /\ ph ) ) $=
      wph vx vy cA cB vy cA nfcv r2exf $.
  $}

  ${
    $d x y $.  $d y A $.
    2ralbida.1 $e |- F/ x ph $.
    2ralbida.2 $e |- F/ y ph $.
    2ralbida.3 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifier (deduction
       rule).  (Contributed by NM, 24-Feb-2004.) $)
    2ralbida $p |- ( ph ->
                     ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $=
      wph wps vy cB wral wch vy cB wral vx cA 2ralbida.1 wph vx cv cA wcel wa
      wps wch vy cB wph vx cv cA wcel vy 2ralbida.2 vx cv cA wcel vy nfv nfan
      wph vx cv cA wcel vy cv cB wcel wps wch wb 2ralbida.3 anassrs ralbida
      ralbida $.
  $}

  ${
    $d x y ph $.  $d y A $.
    2ralbidva.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifiers (deduction
       rule).  (Contributed by NM, 4-Mar-1997.) $)
    2ralbidva $p |- ( ph ->
                     ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $=
      wph wps wch vx vy cA cB wph vx nfv wph vy nfv 2ralbidva.1 2ralbida $.

    $( Formula-building rule for restricted existential quantifiers (deduction
       rule).  (Contributed by NM, 15-Dec-2004.) $)
    2rexbidva $p |- ( ph ->
                    ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) ) $=
      wph wps vy cB wrex wch vy cB wrex vx cA wph vx cv cA wcel wa wps wch vy
      cB wph vx cv cA wcel vy cv cB wcel wps wch wb 2ralbidva.1 anassrs
      rexbidva rexbidva $.
  $}

  ${
    $d x ph $.  $d y ph $.
    2ralbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted universal quantifiers (deduction
       rule).  (Contributed by NM, 28-Jan-2006.)  (Revised by Szymon
       Jaroszewicz, 16-Mar-2007.) $)
    2ralbidv $p |- ( ph ->
                     ( A. x e. A A. y e. B ps <-> A. x e. A A. y e. B ch ) ) $=
      wph wps vy cB wral wch vy cB wral vx cA wph wps wch vy cB 2ralbidv.1
      ralbidv ralbidv $.

    $( Formula-building rule for restricted existential quantifiers (deduction
       rule).  (Contributed by NM, 28-Jan-2006.) $)
    2rexbidv $p |- ( ph ->
                    ( E. x e. A E. y e. B ps <-> E. x e. A E. y e. B ch ) ) $=
      wph wps vy cB wrex wch vy cB wrex vx cA wph wps wch vy cB 2ralbidv.1
      rexbidv rexbidv $.

    $( Formula-building rule for restricted quantifiers (deduction rule).
       (Contributed by NM, 28-Jan-2006.) $)
    rexralbidv $p |- ( ph ->
                    ( E. x e. A A. y e. B ps <-> E. x e. A A. y e. B ch ) ) $=
      wph wps vy cB wral wch vy cB wral vx cA wph wps wch vy cB 2ralbidv.1
      ralbidv rexbidv $.
  $}

  $( A transformation of restricted quantifiers and logical connectives.
     (Contributed by NM, 4-Sep-2005.) $)
  ralinexa $p |- ( A. x e. A ( ph -> -. ps ) <-> -. E. x e. A ( ph /\ ps ) ) $=
    wph wps wn wi vx cA wral wph wps wa wn vx cA wral wph wps wa vx cA wrex wn
    wph wps wn wi wph wps wa wn vx cA wph wps imnan ralbii wph wps wa vx cA
    ralnex bitri $.

  $( A transformation of restricted quantifiers and logical connectives.
     (Contributed by NM, 4-Sep-2005.) $)
  rexanali $p |- ( E. x e. A ( ph /\ -. ps ) <-> -. A. x e. A ( ph -> ps ) ) $=
    wph wps wn wa vx cA wrex wph wps wi wn vx cA wrex wph wps wi vx cA wral wn
    wph wps wn wa wph wps wi wn vx cA wph wps annim rexbii wph wps wi vx cA
    rexnal bitri $.

  ${
    $d x A $.  $d x B $.
    $( Two ways to say " ` A ` belongs to ` B ` ."  (Contributed by NM,
       22-Nov-1994.) $)
    risset $p |- ( A e. B <-> E. x e. B x = A ) $=
      vx cv cB wcel vx cv cA wceq wa vx wex vx cv cA wceq vx cv cB wcel wa vx
      wex vx cv cA wceq vx cB wrex cA cB wcel vx cv cB wcel vx cv cA wceq vx
      exancom vx cv cA wceq vx cB df-rex vx cA cB df-clel 3bitr4ri $.
  $}

  ${
    hbral.1 $e |- ( y e. A -> A. x y e. A ) $.
    hbral.2 $e |- ( ph -> A. x ph ) $.
    $( Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by David Abernethy,
       13-Dec-2009.) $)
    hbral $p |- ( A. y e. A ph -> A. x A. y e. A ph ) $=
      wph vy cA wral vy cv cA wcel wph wi vy wal vx wph vy cA df-ral vy cv cA
      wcel wph wi vx vy vy cv cA wcel wph vx hbral.1 hbral.2 hbim hbal hbxfrbi
      $.
  $}

  $( ` x ` is not free in ` A. x e. A ph ` .  (Contributed by NM,
     18-Oct-1996.) $)
  hbra1 $p |- ( A. x e. A ph -> A. x A. x e. A ph ) $=
    wph vx cA wral vx cv cA wcel wph wi vx wal vx wph vx cA df-ral vx cv cA
    wcel wph wi vx hba1 hbxfrbi $.

  $( ` x ` is not free in ` A. x e. A ph ` .  (Contributed by NM,
     18-Oct-1996.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
  nfra1 $p |- F/ x A. x e. A ph $=
    wph vx cA wral vx cv cA wcel wph wi vx wal vx wph vx cA df-ral vx cv cA
    wcel wph wi vx nfa1 nfxfr $.

  ${
    nfrald.2 $e |- F/ y ph $.
    nfrald.3 $e |- ( ph -> F/_ x A ) $.
    nfrald.4 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfral .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 7-Oct-2016.) $)
    nfrald $p |- ( ph -> F/ x A. y e. A ps ) $=
      wps vy cA wral vy cv cA wcel wps wi vy wal wph vx wps vy cA df-ral wph vy
      cv cA wcel wps wi vx vy nfrald.2 wph vx cv vy cv wceq vx wal wn wa vy cv
      cA wcel wps vx wph vx cv vy cv wceq vx wal wn wa vx vy cv cA vx cv vy cv
      wceq vx wal wn vx vy cv wnfc wph vx vy nfcvf adantl wph vx cA wnfc vx cv
      vy cv wceq vx wal wn nfrald.3 adantr nfeld wph wps vx wnf vx cv vy cv
      wceq vx wal wn nfrald.4 adantr nfimd nfald2 nfxfrd $.

    $( Deduction version of ~ nfrex .  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)
    nfrexd $p |- ( ph -> F/ x E. y e. A ps ) $=
      wps vy cA wrex wps wn vy cA wral wn wph vx wps vy cA dfrex2 wph wps wn vy
      cA wral vx wph wps wn vx vy cA nfrald.2 nfrald.3 wph wps vx nfrald.4 nfnd
      nfrald nfnd nfxfrd $.
  $}

  ${
    nfral.1 $e |- F/_ x A $.
    nfral.2 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    nfral $p |- F/ x A. y e. A ph $=
      wph vy cA wral vx wnf wtru wph vx vy cA vy nftru vx cA wnfc wtru nfral.1
      a1i wph vx wnf wtru nfral.2 a1i nfrald trud $.
  $}

  ${
    $d A y $.
    $( Similar to Lemma 24 of [Monk2] p. 114, except the quantification of the
       antecedent is restricted.  Derived automatically from ~ hbra2VD .
       Contributed by Alan Sare 31-Dec-2011.  (Contributed by NM,
       31-Dec-2011.) $)
    nfra2 $p |- F/ y A. x e. A A. y e. B ph $=
      wph vy cB wral vy vx cA vy cA nfcv wph vy cB nfra1 nfral $.
  $}

  ${
    nfrex.1 $e |- F/_ x A $.
    nfrex.2 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for restricted quantification.
       (Contributed by NM, 1-Sep-1999.)  (Revised by Mario Carneiro,
       7-Oct-2016.) $)
    nfrex $p |- F/ x E. y e. A ph $=
      wph vy cA wrex wph wn vy cA wral wn vx wph vy cA dfrex2 wph wn vy cA wral
      vx wph wn vx vy cA nfrex.1 wph vx nfrex.2 nfn nfral nfn nfxfr $.
  $}

  $( ` x ` is not free in ` E. x e. A ph ` .  (Contributed by NM,
     19-Mar-1997.)  (Revised by Mario Carneiro, 7-Oct-2016.) $)
  nfre1 $p |- F/ x E. x e. A ph $=
    wph vx cA wrex vx cv cA wcel wph wa vx wex vx wph vx cA df-rex vx cv cA
    wcel wph wa vx nfe1 nfxfr $.

  ${
    $d x y z $.  $d y z A $.  $d z B $.
    $( Triple restricted universal quantification.  (Contributed by NM,
       19-Nov-1995.) $)
    r3al $p |- ( A. x e. A A. y e. B A. z e. C ph <->
               A. x A. y A. z ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) ) $=
      vy cv cB wcel vz cv cC wcel wa wph wi vz wal vy wal vx cA wral vx cv cA
      wcel vy cv cB wcel vz cv cC wcel wa wph wi vz wal vy wal wi vx wal wph vz
      cC wral vy cB wral vx cA wral vx cv cA wcel vy cv cB wcel vz cv cC wcel
      w3a wph wi vz wal vy wal vx wal vy cv cB wcel vz cv cC wcel wa wph wi vz
      wal vy wal vx cA df-ral wph vz cC wral vy cB wral vy cv cB wcel vz cv cC
      wcel wa wph wi vz wal vy wal vx cA wph vy vz cB cC r2al ralbii vx cv cA
      wcel vy cv cB wcel vz cv cC wcel w3a wph wi vz wal vy wal vx cv cA wcel
      vy cv cB wcel vz cv cC wcel wa wph wi vz wal vy wal wi vx vx cv cA wcel
      vy cv cB wcel vz cv cC wcel w3a wph wi vz wal vy wal vx cv cA wcel vy cv
      cB wcel vz cv cC wcel wa wph wi vz wal wi vy wal vx cv cA wcel vy cv cB
      wcel vz cv cC wcel wa wph wi vz wal vy wal wi vx cv cA wcel vy cv cB wcel
      vz cv cC wcel w3a wph wi vz wal vx cv cA wcel vy cv cB wcel vz cv cC wcel
      wa wph wi vz wal wi vy vx cv cA wcel vy cv cB wcel vz cv cC wcel w3a wph
      wi vz wal vx cv cA wcel vy cv cB wcel vz cv cC wcel wa wph wi wi vz wal
      vx cv cA wcel vy cv cB wcel vz cv cC wcel wa wph wi vz wal wi vx cv cA
      wcel vy cv cB wcel vz cv cC wcel w3a wph wi vx cv cA wcel vy cv cB wcel
      vz cv cC wcel wa wph wi wi vz vx cv cA wcel vy cv cB wcel vz cv cC wcel
      w3a wph wi vx cv cA wcel vy cv cB wcel vz cv cC wcel wa wa wph wi vx cv
      cA wcel vy cv cB wcel vz cv cC wcel wa wph wi wi vx cv cA wcel vy cv cB
      wcel vz cv cC wcel w3a vx cv cA wcel vy cv cB wcel vz cv cC wcel wa wa
      wph vx cv cA wcel vy cv cB wcel vz cv cC wcel 3anass imbi1i vx cv cA wcel
      vy cv cB wcel vz cv cC wcel wa wph impexp bitri albii vx cv cA wcel vy cv
      cB wcel vz cv cC wcel wa wph wi vz 19.21v bitri albii vx cv cA wcel vy cv
      cB wcel vz cv cC wcel wa wph wi vz wal vy 19.21v bitri albii 3bitr4i $.
  $}

  $( Universal quantification implies restricted quantification.  (Contributed
     by NM, 20-Oct-2006.) $)
  alral $p |- ( A. x ph -> A. x e. A ph ) $=
    wph vx wal vx cv cA wcel wph wi vx wal wph vx cA wral wph vx cv cA wcel wph
    wi vx wph vx cv cA wcel ax-1 alimi wph vx cA df-ral sylibr $.

  $( Restricted existence implies existence.  (Contributed by NM,
     11-Nov-1995.) $)
  rexex $p |- ( E. x e. A ph -> E. x ph ) $=
    wph vx cA wrex vx cv cA wcel wph wa vx wex wph vx wex wph vx cA df-rex vx
    cv cA wcel wph wa wph vx vx cv cA wcel wph simpr eximi sylbi $.

  $( Restricted specialization.  (Contributed by NM, 17-Oct-1996.) $)
  rsp $p |- ( A. x e. A ph -> ( x e. A -> ph ) ) $=
    wph vx cA wral vx cv cA wcel wph wi vx wal vx cv cA wcel wph wi wph vx cA
    df-ral vx cv cA wcel wph wi vx sp sylbi $.

  $( Restricted specialization.  (Contributed by NM, 12-Oct-1999.) $)
  rspe $p |- ( ( x e. A /\ ph ) -> E. x e. A ph ) $=
    vx cv cA wcel wph wa vx cv cA wcel wph wa vx wex wph vx cA wrex vx cv cA
    wcel wph wa vx 19.8a wph vx cA df-rex sylibr $.

  $( Restricted specialization.  (Contributed by NM, 11-Feb-1997.) $)
  rsp2 $p |- ( A. x e. A A. y e. B ph -> ( ( x e. A /\ y e. B ) -> ph ) ) $=
    wph vy cB wral vx cA wral vx cv cA wcel vy cv cB wcel wph wph vy cB wral vx
    cA wral vx cv cA wcel wph vy cB wral vy cv cB wcel wph wi wph vy cB wral vx
    cA rsp wph vy cB rsp syl6 imp3a $.

  $( Restricted specialization.  (Contributed by FL, 4-Jun-2012.) $)
  rsp2e $p |- ( ( x e. A /\ y e. B /\ ph ) -> E. x e. A E. y e. B ph ) $=
    vx cv cA wcel vy cv cB wcel wph w3a vx cv cA wcel wph vy cB wrex wa vx wex
    wph vy cB wrex vx cA wrex vx cv cA wcel vy cv cB wcel wph w3a vx cv cA wcel
    wph vy cB wrex vx cv cA wcel wph vy cB wrex wa vx wex vx cv cA wcel vy cv
    cB wcel wph simp1 vy cv cB wcel wph wph vy cB wrex vx cv cA wcel wph vy cB
    rspe 3adant1 vx cv cA wcel wph vy cB wrex wa vx 19.8a syl2anc wph vy cB
    wrex vx cA df-rex sylibr $.

  ${
    rspec.1 $e |- A. x e. A ph $.
    $( Specialization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)
    rspec $p |- ( x e. A -> ph ) $=
      wph vx cA wral vx cv cA wcel wph wi rspec.1 wph vx cA rsp ax-mp $.
  $}

  ${
    rgen.1 $e |- ( x e. A -> ph ) $.
    $( Generalization rule for restricted quantification.  (Contributed by NM,
       19-Nov-1994.) $)
    rgen $p |- A. x e. A ph $=
      wph vx cA wral vx cv cA wcel wph wi vx wph vx cA df-ral rgen.1 mpgbir $.
  $}

  ${
    $d y z A $.  $d x z $.
    rgen2a.1 $e |- ( ( x e. A /\ y e. A ) -> ph ) $.
    $( Generalization rule for restricted quantification.  Note that ` x ` and
       ` y ` needn't be distinct (and illustrates the use of ~ dvelim ).
       (Contributed by NM, 23-Nov-1994.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged. $)
    rgen2a $p |- A. x e. A A. y e. A ph $=
      wph vy cA wral vx cA vx cv cA wcel vy cv cA wcel wph wi vy wal wph vy cA
      wral vy cv vx cv wceq vy wal vx cv cA wcel vy cv cA wcel wph wi vy wal wi
      vy cv vx cv wceq vy wal vy cv cA wcel wph wi vy wal vx cv cA wcel vy cv
      vx cv wceq vy cv cA wcel wph wi vy vy cv vx cv wceq vy cv cA wcel wph vy
      cv vx cv wceq vy cv cA wcel vx cv cA wcel vy cv cA wcel wph wi vy cv vx
      cv cA eleq1 vx cv cA wcel vy cv cA wcel wph rgen2a.1 ex syl6bi pm2.43d
      alimi a1d vy cv vx cv wceq vy wal wn vx cv cA wcel vx cv cA wcel vy wal
      vy cv cA wcel wph wi vy wal vz cv cA wcel vx cv cA wcel vy vx vz vz cv vx
      cv cA eleq1 dvelimv vx cv cA wcel vy cv cA wcel wph wi vy vx cv cA wcel
      vy cv cA wcel wph rgen2a.1 ex alimi syl6 pm2.61i wph vy cA df-ral sylibr
      rgen $.
  $}

  ${
    rgenw.1 $e |- ph $.
    $( Generalization rule for restricted quantification.  (Contributed by NM,
       18-Jun-2014.) $)
    rgenw $p |- A. x e. A ph $=
      wph vx cA wph vx cv cA wcel rgenw.1 a1i rgen $.

    $( Generalization rule for restricted quantification.  Note that ` x ` and
       ` y ` needn't be distinct.  (Contributed by NM, 18-Jun-2014.) $)
    rgen2w $p |- A. x e. A A. y e. B ph $=
      wph vy cB wral vx cA wph vy cB rgenw.1 rgenw rgenw $.
  $}

  ${
    mprg.1 $e |- ( A. x e. A ph -> ps ) $.
    mprg.2 $e |- ( x e. A -> ph ) $.
    $( Modus ponens combined with restricted generalization.  (Contributed by
       NM, 10-Aug-2004.) $)
    mprg $p |- ps $=
      wph vx cA wral wps wph vx cA mprg.2 rgen mprg.1 ax-mp $.
  $}

  ${
    mprgbir.1 $e |- ( ph <-> A. x e. A ps ) $.
    mprgbir.2 $e |- ( x e. A -> ps ) $.
    $( Modus ponens on biconditional combined with restricted generalization.
       (Contributed by NM, 21-Mar-2004.) $)
    mprgbir $p |- ph $=
      wph wps vx cA wral wps vx cA mprgbir.2 rgen mprgbir.1 mpbir $.
  $}

  $( Distribution of restricted quantification over implication.  (Contributed
     by NM, 9-Feb-1997.) $)
  ralim $p |- ( A. x e. A ( ph -> ps ) ->
               ( A. x e. A ph -> A. x e. A ps ) ) $=
    wph wps wi vx cA wral vx cv cA wcel wph wi vx wal vx cv cA wcel wps wi vx
    wal wph vx cA wral wps vx cA wral wph wps wi vx cA wral vx cv cA wcel wph
    wps wi wi vx wal vx cv cA wcel wph wi vx wal vx cv cA wcel wps wi vx wal wi
    wph wps wi vx cA df-ral vx cv cA wcel wph wps wi wi vx cv cA wcel wph wi vx
    cv cA wcel wps wi vx vx cv cA wcel wph wps ax-2 al2imi sylbi wph vx cA
    df-ral wps vx cA df-ral 3imtr4g $.

  ${
    ralimi2.1 $e |- ( ( x e. A -> ph ) -> ( x e. B -> ps ) ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 22-Feb-2004.) $)
    ralimi2 $p |- ( A. x e. A ph -> A. x e. B ps ) $=
      vx cv cA wcel wph wi vx wal vx cv cB wcel wps wi vx wal wph vx cA wral
      wps vx cB wral vx cv cA wcel wph wi vx cv cB wcel wps wi vx ralimi2.1
      alimi wph vx cA df-ral wps vx cB df-ral 3imtr4i $.
  $}

  ${
    ralimia.1 $e |- ( x e. A -> ( ph -> ps ) ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 19-Jul-1996.) $)
    ralimia $p |- ( A. x e. A ph -> A. x e. A ps ) $=
      wph wps vx cA cA vx cv cA wcel wph wps ralimia.1 a2i ralimi2 $.
  $}

  ${
    ralimiaa.1 $e |- ( ( x e. A /\ ph ) -> ps ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 4-Aug-2007.) $)
    ralimiaa $p |- ( A. x e. A ph -> A. x e. A ps ) $=
      wph wps vx cA vx cv cA wcel wph wps ralimiaa.1 ex ralimia $.
  $}

  ${
    ralimi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent, with strong
       hypothesis.  (Contributed by NM, 4-Mar-1997.) $)
    ralimi $p |- ( A. x e. A ph -> A. x e. A ps ) $=
      wph wps vx cA wph wps wi vx cv cA wcel ralimi.1 a1i ralimia $.
  $}

  ${
    ral2imi.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference quantifying antecedent, nested antecedent, and consequent,
       with a strong hypothesis.  (Contributed by NM, 19-Dec-2006.) $)
    ral2imi $p |- ( A. x e. A ph -> ( A. x e. A ps -> A. x e. A ch ) ) $=
      wph vx cA wral wps wch wi vx cA wral wps vx cA wral wch vx cA wral wi wph
      wps wch wi vx cA ral2imi.1 ralimi wps wch vx cA ralim syl $.
  $}

  ${
    ralimdaa.1 $e |- F/ x ph $.
    ralimdaa.2 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 22-Sep-2003.) $)
    ralimdaa $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $=
      wph vx cv cA wcel wps wi vx wal vx cv cA wcel wch wi vx wal wps vx cA
      wral wch vx cA wral wph vx cv cA wcel wps wi vx cv cA wcel wch wi vx
      ralimdaa.1 wph vx cv cA wcel wps wch wph vx cv cA wcel wps wch wi
      ralimdaa.2 ex a2d alimd wps vx cA df-ral wch vx cA df-ral 3imtr4g $.
  $}

  ${
    $d x ph $.
    ralimdva.1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 22-May-1999.) $)
    ralimdva $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv ralimdva.1 ralimdaa $.
  $}

  ${
    $d x ph $.
    ralimdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction quantifying both antecedent and consequent, based on Theorem
       19.20 of [Margaris] p. 90.  (Contributed by NM, 8-Oct-2003.) $)
    ralimdv $p |- ( ph -> ( A. x e. A ps -> A. x e. A ch ) ) $=
      wph wps wch vx cA wph wps wch wi vx cv cA wcel ralimdv.1 adantr ralimdva
      $.
  $}

  ${
    $d x ph $.
    ralimdv2.1 $e |- ( ph -> ( ( x e. A -> ps ) -> ( x e. B -> ch ) ) ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 1-Feb-2005.) $)
    ralimdv2 $p |- ( ph -> ( A. x e. A ps -> A. x e. B ch ) ) $=
      wph vx cv cA wcel wps wi vx wal vx cv cB wcel wch wi vx wal wps vx cA
      wral wch vx cB wral wph vx cv cA wcel wps wi vx cv cB wcel wch wi vx
      ralimdv2.1 alimdv wps vx cA df-ral wch vx cB df-ral 3imtr4g $.
  $}

  ${
    ralrimi.1 $e |- F/ x ph $.
    ralrimi.2 $e |- ( ph -> ( x e. A -> ps ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 10-Oct-1999.) $)
    ralrimi $p |- ( ph -> A. x e. A ps ) $=
      wph vx cv cA wcel wps wi vx wal wps vx cA wral wph vx cv cA wcel wps wi
      vx ralrimi.1 ralrimi.2 alrimi wps vx cA df-ral sylibr $.
  $}

  ${
    $d x ph $.
    ralrimiv.1 $e |- ( ph -> ( x e. A -> ps ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 22-Nov-1994.) $)
    ralrimiv $p |- ( ph -> A. x e. A ps ) $=
      wph wps vx cA wph vx nfv ralrimiv.1 ralrimi $.
  $}

  ${
    $d x ph $.
    ralrimiva.1 $e |- ( ( ph /\ x e. A ) -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Jan-2006.) $)
    ralrimiva $p |- ( ph -> A. x e. A ps ) $=
      wph wps vx cA wph vx cv cA wcel wps ralrimiva.1 ex ralrimiv $.
  $}

  ${
    $d x ph $.
    ralrimivw.1 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 18-Jun-2014.) $)
    ralrimivw $p |- ( ph -> A. x e. A ps ) $=
      wph wps vx cA wph wps vx cv cA wcel ralrimivw.1 a1d ralrimiv $.
  $}

  ${
    $( Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers (closed
       theorem version).  (Contributed by NM, 1-Mar-2008.) $)
    r19.21t $p |- ( F/ x ph ->
             ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) ) $=
      wph vx wnf vx cv cA wcel wph wps wi wi vx wal wph vx cv cA wcel wps wi vx
      wal wi wph wps wi vx cA wral wph wps vx cA wral wi vx cv cA wcel wph wps
      wi wi vx wal wph vx cv cA wcel wps wi wi vx wal wph vx wnf wph vx cv cA
      wcel wps wi vx wal wi vx cv cA wcel wph wps wi wi wph vx cv cA wcel wps
      wi wi vx vx cv cA wcel wph wps bi2.04 albii wph vx cv cA wcel wps wi vx
      19.21t syl5bb wph wps wi vx cA df-ral wps vx cA wral vx cv cA wcel wps wi
      vx wal wph wps vx cA df-ral imbi2i 3bitr4g $.
  $}

  ${
    r19.21.1 $e |- F/ x ph $.
    $( Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by Scott Fenton, 30-Mar-2011.) $)
    r19.21 $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $=
      wph vx wnf wph wps wi vx cA wral wph wps vx cA wral wi wb r19.21.1 wph
      wps vx cA r19.21t ax-mp $.
  $}

  ${
    $d x ph $.
    $( Theorem 19.21 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)
    r19.21v $p |- ( A. x e. A ( ph -> ps ) <-> ( ph -> A. x e. A ps ) ) $=
      wph wps vx cA wph vx nfv r19.21 $.
  $}

  ${
    ralrimd.1 $e |- F/ x ph $.
    ralrimd.2 $e |- F/ x ps $.
    ralrimd.3 $e |- ( ph -> ( ps -> ( x e. A -> ch ) ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 16-Feb-2004.) $)
    ralrimd $p |- ( ph -> ( ps -> A. x e. A ch ) ) $=
      wph wps vx cv cA wcel wch wi vx wal wch vx cA wral wph wps vx cv cA wcel
      wch wi vx ralrimd.1 ralrimd.2 ralrimd.3 alrimd wch vx cA df-ral syl6ibr
      $.
  $}

  ${
    $d x ph $.  $d x ps $.
    ralrimdv.1 $e |- ( ph -> ( ps -> ( x e. A -> ch ) ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 27-May-1998.) $)
    ralrimdv $p |- ( ph -> ( ps -> A. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv wps vx nfv ralrimdv.1 ralrimd $.
  $}

  ${
    $d x ph $.  $d x ps $.
    ralrimdva.1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 2-Feb-2008.) $)
    ralrimdva $p |- ( ph -> ( ps -> A. x e. A ch ) ) $=
      wph wps wch vx cA wph vx cv cA wcel wps wch wph vx cv cA wcel wps wch wi
      ralrimdva.1 ex com23 ralrimdv $.
  $}

  ${
    $d x y ph $.  $d y A $.
    ralrimivv.1 $e |- ( ph -> ( ( x e. A /\ y e. B ) -> ps ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       24-Jul-2004.) $)
    ralrimivv $p |- ( ph -> A. x e. A A. y e. B ps ) $=
      wph wps vy cB wral vx cA wph vx cv cA wcel wps vy cB wph vx cv cA wcel vy
      cv cB wcel wps ralrimivv.1 exp3a ralrimdv ralrimiv $.
  $}

  ${
    $d ph x y $.  $d A y $.
    ralrimivva.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by Jeff
       Madsen, 19-Jun-2011.) $)
    ralrimivva $p |- ( ph -> A. x e. A A. y e. B ps ) $=
      wph wps vx vy cA cB wph vx cv cA wcel vy cv cB wcel wa wps ralrimivva.1
      ex ralrimivv $.
  $}

  ${
    $d ph x y z $.  $d A y z $.  $d B z $.
    ralrimivvva.1 $e |- ( ( ph /\ ( x e. A /\ y e. B /\ z e. C ) ) -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with triple quantification.)  (Contributed by Mario
       Carneiro, 9-Jul-2014.) $)
    ralrimivvva $p |- ( ph -> A. x e. A A. y e. B A. z e. C ps ) $=
      wph wps vz cC wral vy cB wral vx cA wph vx cv cA wcel wa wps vz cC wral
      vy cB wph vx cv cA wcel wa vy cv cB wcel wa wps vz cC wph vx cv cA wcel
      vy cv cB wcel vz cv cC wcel wps wph vx cv cA wcel vy cv cB wcel vz cv cC
      wcel wps ralrimivvva.1 3exp2 imp41 ralrimiva ralrimiva ralrimiva $.
  $}

  ${
    $d x y ph $.  $d x y ps $.  $d y A $.
    ralrimdvv.1 $e |- ( ph -> ( ps -> ( ( x e. A /\ y e. B ) -> ch ) ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       1-Jun-2005.) $)
    ralrimdvv $p |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) ) $=
      wph wps wch vy cB wral vx cA wral wph wps wa wch vx vy cA cB wph wps vx
      cv cA wcel vy cv cB wcel wa wch wi ralrimdvv.1 imp ralrimivv ex $.
  $}

  ${
    $d x y ph $.  $d x y ps $.  $d y A $.
    ralrimdvva.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version with double quantification.)  (Contributed by NM,
       2-Feb-2008.) $)
    ralrimdvva $p |- ( ph -> ( ps -> A. x e. A A. y e. B ch ) ) $=
      wph wps wch vx vy cA cB wph vx cv cA wcel vy cv cB wcel wa wps wch wph vx
      cv cA wcel vy cv cB wcel wa wps wch wi ralrimdvva.1 ex com23 ralrimdvv $.
  $}

  ${
    $d x y $.  $d y A $.
    rgen2.1 $e |- ( ( x e. A /\ y e. B ) -> ph ) $.
    $( Generalization rule for restricted quantification.  (Contributed by NM,
       30-May-1999.) $)
    rgen2 $p |- A. x e. A A. y e. B ph $=
      wph vy cB wral vx cA vx cv cA wcel wph vy cB rgen2.1 ralrimiva rgen $.
  $}

  ${
    $d y z A $.  $d z B $.  $d x y z $.
    rgen3.1 $e |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) $.
    $( Generalization rule for restricted quantification.  (Contributed by NM,
       12-Jan-2008.) $)
    rgen3 $p |- A. x e. A A. y e. B A. z e. C ph $=
      wph vz cC wral vx vy cA cB vx cv cA wcel vy cv cB wcel wa wph vz cC vx cv
      cA wcel vy cv cB wcel vz cv cC wcel wph rgen3.1 3expa ralrimiva rgen2 $.
  $}

  ${
    r19.21bi.1 $e |- ( ph -> A. x e. A ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 20-Nov-1994.) $)
    r19.21bi $p |- ( ( ph /\ x e. A ) -> ps ) $=
      wph vx cv cA wcel wps wph vx cv cA wcel wps wi vx wph wps vx cA wral vx
      cv cA wcel wps wi vx wal r19.21bi.1 wps vx cA df-ral sylib 19.21bi imp $.
  $}

  ${
    rspec2.1 $e |- A. x e. A A. y e. B ph $.
    $( Specialization rule for restricted quantification.  (Contributed by NM,
       20-Nov-1994.) $)
    rspec2 $p |- ( ( x e. A /\ y e. B ) -> ph ) $=
      vx cv cA wcel wph vy cB wph vy cB wral vx cA rspec2.1 rspec r19.21bi $.
  $}

  ${
    rspec3.1 $e |- A. x e. A A. y e. B A. z e. C ph $.
    $( Specialization rule for restricted quantification.  (Contributed by NM,
       20-Nov-1994.) $)
    rspec3 $p |- ( ( x e. A /\ y e. B /\ z e. C ) -> ph ) $=
      vx cv cA wcel vy cv cB wcel vz cv cC wcel wph vx cv cA wcel vy cv cB wcel
      wa wph vz cC wph vz cC wral vx vy cA cB rspec3.1 rspec2 r19.21bi 3impa $.
  $}

  ${
    r19.21be.1 $e |- ( ph -> A. x e. A ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 21-Nov-1994.) $)
    r19.21be $p |- A. x e. A ( ph -> ps ) $=
      wph wps wi vx cA wph vx cv cA wcel wps wph wps vx cA r19.21be.1 r19.21bi
      expcom rgen $.
  $}

  ${
    nrex.1 $e |- ( x e. A -> -. ps ) $.
    $( Inference adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)
    nrex $p |- -. E. x e. A ps $=
      wps wn vx cA wral wps vx cA wrex wn wps wn vx cA nrex.1 rgen wps vx cA
      ralnex mpbi $.
  $}

  ${
    $d x ph $.
    nrexdv.1 $e |- ( ( ph /\ x e. A ) -> -. ps ) $.
    $( Deduction adding restricted existential quantifier to negated wff.
       (Contributed by NM, 16-Oct-2003.) $)
    nrexdv $p |- ( ph -> -. E. x e. A ps ) $=
      wph wps wn vx cA wral wps vx cA wrex wn wph wps wn vx cA nrexdv.1
      ralrimiva wps vx cA ralnex sylib $.
  $}

  $( Theorem 19.22 of [Margaris] p. 90.  (Restricted quantifier version.)
     (Contributed by NM, 22-Nov-1994.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)
  rexim $p |- ( A. x e. A ( ph -> ps ) ->
               ( E. x e. A ph -> E. x e. A ps ) ) $=
    wph wps wi vx cA wral wph wn vx cA wral wn wps wn vx cA wral wn wph vx cA
    wrex wps vx cA wrex wph wps wi vx cA wral wps wn vx cA wral wph wn vx cA
    wral wph wps wi wps wn wph wn vx cA wph wps con3 ral2imi con3d wph vx cA
    dfrex2 wps vx cA dfrex2 3imtr4g $.

  ${
    reximia.1 $e |- ( x e. A -> ( ph -> ps ) ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 10-Feb-1997.) $)
    reximia $p |- ( E. x e. A ph -> E. x e. A ps ) $=
      wph wps wi wph vx cA wrex wps vx cA wrex wi vx cA wph wps vx cA rexim
      reximia.1 mprg $.
  $}

  ${
    reximi2.1 $e |- ( ( x e. A /\ ph ) -> ( x e. B /\ ps ) ) $.
    $( Inference quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 8-Nov-2004.) $)
    reximi2 $p |- ( E. x e. A ph -> E. x e. B ps ) $=
      vx cv cA wcel wph wa vx wex vx cv cB wcel wps wa vx wex wph vx cA wrex
      wps vx cB wrex vx cv cA wcel wph wa vx cv cB wcel wps wa vx reximi2.1
      eximi wph vx cA df-rex wps vx cB df-rex 3imtr4i $.
  $}

  ${
    reximi.1 $e |- ( ph -> ps ) $.
    $( Inference quantifying both antecedent and consequent.  (Contributed by
       NM, 18-Oct-1996.) $)
    reximi $p |- ( E. x e. A ph -> E. x e. A ps ) $=
      wph wps vx cA wph wps wi vx cv cA wcel reximi.1 a1i reximia $.
  $}

  ${
    reximdai.1 $e |- F/ x ph $.
    reximdai.2 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 31-Aug-1999.) $)
    reximdai $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $=
      wph wps wch wi vx cA wral wps vx cA wrex wch vx cA wrex wi wph wps wch wi
      vx cA reximdai.1 reximdai.2 ralrimi wps wch vx cA rexim syl $.
  $}

  ${
    $d x ph $.
    reximdv2.1 $e |- ( ph -> ( ( x e. A /\ ps ) -> ( x e. B /\ ch ) ) ) $.
    $( Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 17-Sep-2003.) $)
    reximdv2 $p |- ( ph -> ( E. x e. A ps -> E. x e. B ch ) ) $=
      wph vx cv cA wcel wps wa vx wex vx cv cB wcel wch wa vx wex wps vx cA
      wrex wch vx cB wrex wph vx cv cA wcel wps wa vx cv cB wcel wch wa vx
      reximdv2.1 eximdv wps vx cA df-rex wch vx cB df-rex 3imtr4g $.
  $}

  ${
    $d x ph $.
    reximdvai.1 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
    $( Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 14-Nov-2002.) $)
    reximdvai $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv reximdvai.1 reximdai $.
  $}

  ${
    $d x ph $.
    reximdv.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Restricted
       quantifier version with strong hypothesis.)  (Contributed by NM,
       24-Jun-1998.) $)
    reximdv $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $=
      wph wps wch vx cA wph wps wch wi vx cv cA wcel reximdv.1 a1d reximdvai $.
  $}

  ${
    $d x ph $.
    reximdva.1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Deduction quantifying both antecedent and consequent, based on Theorem
       19.22 of [Margaris] p. 90.  (Contributed by NM, 22-May-1999.) $)
    reximdva $p |- ( ph -> ( E. x e. A ps -> E. x e. A ch ) ) $=
      wph wps wch vx cA wph vx cv cA wcel wps wch wi reximdva.1 ex reximdvai $.
  $}

  ${
    $d x y $.  $d y A $.  $d x B $.
    $( Theorem 19.12 of [Margaris] p. 89 with restricted quantifiers.
       (Contributed by NM, 15-Oct-2003.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)
    r19.12 $p |- ( E. x e. A A. y e. B ph -> A. y e. B E. x e. A ph ) $=
      wph vy cB wral vx cA wrex wph vy cB wral vx cA wrex vy cB wral wph vx cA
      wrex vy cB wral wph vy cB wral vx cA wrex wph vy cB wral vx cA wrex vy cB
      wph vy cB wral vy vx cA vy cA nfcv wph vy cB nfra1 nfrex wph vy cB wral
      vx cA wrex vy cv cB wcel ax-1 ralrimi wph vy cB wral vx cA wrex wph vx cA
      wrex vy cB vy cv cB wcel wph vy cB wral wph vx cA wph vy cB wral vy cv cB
      wcel wph wph vy cB rsp com12 reximdv ralimia syl $.
  $}

  $( Closed theorem form of ~ r19.23 .  (Contributed by NM, 4-Mar-2013.)
     (Revised by Mario Carneiro, 8-Oct-2016.) $)
  r19.23t $p |- ( F/ x ps ->
    ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) ) $=
    wps vx wnf vx cv cA wcel wph wa wps wi vx wal vx cv cA wcel wph wa vx wex
    wps wi wph wps wi vx cA wral wph vx cA wrex wps wi vx cv cA wcel wph wa wps
    vx 19.23t wph wps wi vx cA wral vx cv cA wcel wph wps wi wi vx wal vx cv cA
    wcel wph wa wps wi vx wal wph wps wi vx cA df-ral vx cv cA wcel wph wa wps
    wi vx cv cA wcel wph wps wi wi vx vx cv cA wcel wph wps impexp albii bitr4i
    wph vx cA wrex vx cv cA wcel wph wa vx wex wps wph vx cA df-rex imbi1i
    3bitr4g $.

  ${
    r19.23.1 $e |- F/ x ps $.
    $( Theorem 19.23 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 22-Oct-2010.)  (Proof shortened by Mario Carneiro,
       8-Oct-2016.) $)
    r19.23 $p |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) $=
      wps vx wnf wph wps wi vx cA wral wph vx cA wrex wps wi wb r19.23.1 wph
      wps vx cA r19.23t ax-mp $.
  $}

  ${
    $d x ps $.
    $( Theorem 19.23 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 31-Aug-1999.) $)
    r19.23v $p |- ( A. x e. A ( ph -> ps ) <-> ( E. x e. A ph -> ps ) ) $=
      wph wps vx cA wps vx nfv r19.23 $.
  $}

  ${
    rexlimi.1 $e |- F/ x ps $.
    rexlimi.2 $e |- ( x e. A -> ( ph -> ps ) ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 30-Nov-2003.)  (Proof
       shortened by Andrew Salmon, 30-May-2011.) $)
    rexlimi $p |- ( E. x e. A ph -> ps ) $=
      wph wps wi vx cA wral wph vx cA wrex wps wi wph wps wi vx cA rexlimi.2
      rgen wph wps vx cA rexlimi.1 r19.23 mpbi $.
  $}

  ${
    $d x ps $.
    rexlimiv.1 $e |- ( x e. A -> ( ph -> ps ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 20-Nov-1994.) $)
    rexlimiv $p |- ( E. x e. A ph -> ps ) $=
      wph wps vx cA wps vx nfv rexlimiv.1 rexlimi $.
  $}

  ${
    $d x ps $.
    rexlimiva.1 $e |- ( ( x e. A /\ ph ) -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 18-Dec-2006.) $)
    rexlimiva $p |- ( E. x e. A ph -> ps ) $=
      wph wps vx cA vx cv cA wcel wph wps rexlimiva.1 ex rexlimiv $.
  $}

  ${
    $d ps x $.
    rexlimivw.1 $e |- ( ph -> ps ) $.
    $( Weaker version of ~ rexlimiv .  (Contributed by FL, 19-Sep-2011.) $)
    rexlimivw $p |- ( E. x e. A ph -> ps ) $=
      wph wps vx cA wph wps wi vx cv cA wcel rexlimivw.1 a1i rexlimiv $.
  $}

  ${
    rexlimd.1 $e |- F/ x ph $.
    rexlimd.2 $e |- F/ x ch $.
    rexlimd.3 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 27-May-1998.)  (Proof shortened by Andrew
       Salmon, 30-May-2011.) $)
    rexlimd $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch wi vx cA wral wps vx cA wrex wch wi wph wps wch wi vx cA
      rexlimd.1 rexlimd.3 ralrimi wps wch vx cA rexlimd.2 r19.23 sylib $.
  $}

  ${
    rexlimd2.1 $e |- F/ x ph $.
    rexlimd2.2 $e |- ( ph -> F/ x ch ) $.
    rexlimd2.3 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
    $( Version of ~ rexlimd with deduction version of second hypothesis.
       (Contributed by NM, 21-Jul-2013.)  (Revised by Mario Carneiro,
       8-Oct-2016.) $)
    rexlimd2 $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch wi vx cA wral wps vx cA wrex wch wi wph wps wch wi vx cA
      rexlimd2.1 rexlimd2.3 ralrimi wph wch vx wnf wps wch wi vx cA wral wps vx
      cA wrex wch wi wb rexlimd2.2 wps wch vx cA r19.23t syl mpbid $.
  $}

  ${
    $d x ph $.  $d x ch $.
    rexlimdv.1 $e |- ( ph -> ( x e. A -> ( ps -> ch ) ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 14-Nov-2002.)  (Proof shortened by Eric
       Schmidt, 22-Dec-2006.) $)
    rexlimdv $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch vx cA wph vx nfv wch vx nfv rexlimdv.1 rexlimd $.
  $}

  ${
    $d x ph $.  $d x ch $.
    rexlimdva.1 $e |- ( ( ph /\ x e. A ) -> ( ps -> ch ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 20-Jan-2007.) $)
    rexlimdva $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch vx cA wph vx cv cA wcel wps wch wi rexlimdva.1 ex rexlimdv $.
  $}

  ${
    $d x ph $.  $d x ch $.
    rexlimdvaa.1 $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by Mario Carneiro, 15-Jun-2016.) $)
    rexlimdvaa $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch vx cA wph vx cv cA wcel wps wch rexlimdvaa.1 expr rexlimdva
      $.
  $}

  ${
    $d x ph $.  $d x ch $.
    rexlimdv3a.1 $e |- ( ( ph /\ x e. A /\ ps ) -> ch ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  Frequently-used variant of ~ rexlimdv .  (Contributed by NM,
       7-Jun-2015.) $)
    rexlimdv3a $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch vx cA wph vx cv cA wcel wps wch rexlimdv3a.1 3exp rexlimdv $.
  $}

  ${
    $d x ph $.  $d x ch $.
    rexlimdvw.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 18-Jun-2014.) $)
    rexlimdvw $p |- ( ph -> ( E. x e. A ps -> ch ) ) $=
      wph wps wch vx cA wph wps wch wi vx cv cA wcel rexlimdvw.1 a1d rexlimdv
      $.
  $}

  ${
    $d x ph $.  $d x ch $.
    rexlimddv.1 $e |- ( ph -> E. x e. A ps ) $.
    rexlimddv.2 $e |- ( ( ph /\ ( x e. A /\ ps ) ) -> ch ) $.
    $( Restricted existential elimination rule of natural deduction.
       (Contributed by Mario Carneiro, 15-Jun-2016.) $)
    rexlimddv $p |- ( ph -> ch ) $=
      wph wps vx cA wrex wch rexlimddv.1 wph wps wch vx cA rexlimddv.2
      rexlimdvaa mpd $.
  $}

  ${
    $d x y ps $.  $d y A $.
    rexlimivv.1 $e |- ( ( x e. A /\ y e. B ) -> ( ph -> ps ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90 (restricted quantifier
       version).  (Contributed by NM, 17-Feb-2004.) $)
    rexlimivv $p |- ( E. x e. A E. y e. B ph -> ps ) $=
      wph vy cB wrex wps vx cA vx cv cA wcel wph wps vy cB rexlimivv.1
      rexlimdva rexlimiv $.
  $}

  ${
    $d x y ph $.  $d x y ch $.  $d y A $.
    rexlimdvv.1 $e |- ( ph -> ( ( x e. A /\ y e. B ) -> ( ps -> ch ) ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 22-Jul-2004.) $)
    rexlimdvv $p |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) ) $=
      wph wps vy cB wrex wch vx cA wph vx cv cA wcel wa wps wch vy cB wph vx cv
      cA wcel vy cv cB wcel wps wch wi rexlimdvv.1 expdimp rexlimdv rexlimdva
      $.
  $}

  ${
    $d x y ph $.  $d x y ch $.  $d y A $.
    rexlimdvva.1 $e |- ( ( ph /\ ( x e. A /\ y e. B ) ) -> ( ps -> ch ) ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Restricted
       quantifier version.)  (Contributed by NM, 18-Jun-2014.) $)
    rexlimdvva $p |- ( ph -> ( E. x e. A E. y e. B ps -> ch ) ) $=
      wph wps wch vx vy cA cB wph vx cv cA wcel vy cv cB wcel wa wps wch wi
      rexlimdvva.1 ex rexlimdvv $.
  $}

  $( Theorem 19.26 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by NM, 28-Jan-1997.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)
  r19.26 $p |- ( A. x e. A ( ph /\ ps ) <->
               ( A. x e. A ph /\ A. x e. A ps ) ) $=
    wph wps wa vx cA wral wph vx cA wral wps vx cA wral wa wph wps wa vx cA
    wral wph vx cA wral wps vx cA wral wph wps wa wph vx cA wph wps simpl
    ralimi wph wps wa wps vx cA wph wps simpr ralimi jca wph vx cA wral wps vx
    cA wral wph wps wa vx cA wral wph wps wph wps wa vx cA wph wps pm3.2
    ral2imi imp impbii $.

  $( Theorem 19.26 of [Margaris] p. 90 with 2 restricted quantifiers.
     (Contributed by NM, 10-Aug-2004.) $)
  r19.26-2 $p |- ( A. x e. A A. y e. B ( ph /\ ps ) <->
               ( A. x e. A A. y e. B ph /\ A. x e. A A. y e. B ps ) ) $=
    wph wps wa vy cB wral vx cA wral wph vy cB wral wps vy cB wral wa vx cA
    wral wph vy cB wral vx cA wral wps vy cB wral vx cA wral wa wph wps wa vy
    cB wral wph vy cB wral wps vy cB wral wa vx cA wph wps vy cB r19.26 ralbii
    wph vy cB wral wps vy cB wral vx cA r19.26 bitri $.

  $( Theorem 19.26 of [Margaris] p. 90 with 3 restricted quantifiers.
     (Contributed by FL, 22-Nov-2010.) $)
  r19.26-3 $p |- ( A. x e. A ( ph /\ ps /\ ch ) <->
               ( A. x e. A ph /\ A. x e. A ps /\ A. x e. A ch ) ) $=
    wph wps wch w3a vx cA wral wph wps wa wch wa vx cA wral wph wps wa vx cA
    wral wch vx cA wral wa wph vx cA wral wps vx cA wral wch vx cA wral w3a wph
    wps wch w3a wph wps wa wch wa vx cA wph wps wch df-3an ralbii wph wps wa
    wch vx cA r19.26 wph wps wa vx cA wral wch vx cA wral wa wph vx cA wral wps
    vx cA wral wa wch vx cA wral wa wph vx cA wral wps vx cA wral wch vx cA
    wral w3a wph wps wa vx cA wral wph vx cA wral wps vx cA wral wa wch vx cA
    wral wph wps vx cA r19.26 anbi1i wph vx cA wral wps vx cA wral wch vx cA
    wral df-3an bitr4i 3bitri $.

  $( Theorem 19.26 of [Margaris] p. 90 with mixed quantifiers.  (Contributed by
     NM, 22-Feb-2004.) $)
  r19.26m $p |- ( A. x ( ( x e. A -> ph ) /\ ( x e. B -> ps ) ) <->
               ( A. x e. A ph /\ A. x e. B ps ) ) $=
    vx cv cA wcel wph wi vx cv cB wcel wps wi wa vx wal vx cv cA wcel wph wi vx
    wal vx cv cB wcel wps wi vx wal wa wph vx cA wral wps vx cB wral wa vx cv
    cA wcel wph wi vx cv cB wcel wps wi vx 19.26 wph vx cA wral vx cv cA wcel
    wph wi vx wal wps vx cB wral vx cv cB wcel wps wi vx wal wph vx cA df-ral
    wps vx cB df-ral anbi12i bitr4i $.

  $( Distribute a restricted universal quantifier over a biconditional.
     Theorem 19.15 of [Margaris] p. 90 with restricted quantification.
     (Contributed by NM, 6-Oct-2003.) $)
  ralbi $p |- ( A. x e. A ( ph <-> ps ) ->
               ( A. x e. A ph <-> A. x e. A ps ) ) $=
    wph wps wb vx cA wral wph wps vx cA wph wps wb vx cA nfra1 wph wps wb vx cA
    wral vx cv cA wcel wph wps wb wph wps wb vx cA rsp imp ralbida $.

  $( Split a biconditional and distribute quantifier.  (Contributed by NM,
     3-Jun-2012.) $)
  ralbiim $p |- ( A. x e. A ( ph <-> ps ) <->
             ( A. x e. A ( ph -> ps ) /\ A. x e. A ( ps -> ph ) ) ) $=
    wph wps wb vx cA wral wph wps wi wps wph wi wa vx cA wral wph wps wi vx cA
    wral wps wph wi vx cA wral wa wph wps wb wph wps wi wps wph wi wa vx cA wph
    wps dfbi2 ralbii wph wps wi wps wph wi vx cA r19.26 bitri $.

  ${
    $d x ps $.
    $( Restricted version of one direction of Theorem 19.27 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 3-Jun-2004.)  (Proof shortened by Andrew Salmon,
       30-May-2011.) $)
    r19.27av $p |- ( ( A. x e. A ph /\ ps ) -> A. x e. A ( ph /\ ps ) ) $=
      wph vx cA wral wps wa wph vx cA wral wps vx cA wral wa wph wps wa vx cA
      wral wps wps vx cA wral wph vx cA wral wps wps vx cA wps vx cv cA wcel
      ax-1 ralrimiv anim2i wph wps vx cA r19.26 sylibr $.
  $}

  ${
    $d x ph $.
    $( Restricted version of one direction of Theorem 19.28 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)
    r19.28av $p |- ( ( ph /\ A. x e. A ps ) -> A. x e. A ( ph /\ ps ) ) $=
      wps vx cA wral wph wa wps wph wa vx cA wral wph wps vx cA wral wa wph wps
      wa vx cA wral wps wph vx cA r19.27av wph wps vx cA wral ancom wph wps wa
      wps wph wa vx cA wph wps ancom ralbii 3imtr4i $.
  $}

  $( Theorem 19.29 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by NM, 31-Aug-1999.)  (Proof shortened by Andrew Salmon,
     30-May-2011.) $)
  r19.29 $p |- ( ( A. x e. A ph /\ E. x e. A ps ) ->
               E. x e. A ( ph /\ ps ) ) $=
    wph vx cA wral wps vx cA wrex wph wps wa vx cA wrex wph vx cA wral wps wph
    wps wa wi vx cA wral wps vx cA wrex wph wps wa vx cA wrex wi wph wps wph
    wps wa wi vx cA wph wps pm3.2 ralimi wps wph wps wa vx cA rexim syl imp $.

  $( Variation of Theorem 19.29 of [Margaris] p. 90 with restricted
     quantifiers.  (Contributed by NM, 31-Aug-1999.) $)
  r19.29r $p |- ( ( E. x e. A ph /\ A. x e. A ps ) ->
                E. x e. A ( ph /\ ps ) ) $=
    wps vx cA wral wph vx cA wrex wa wps wph wa vx cA wrex wph vx cA wrex wps
    vx cA wral wa wph wps wa vx cA wrex wps wph vx cA r19.29 wph vx cA wrex wps
    vx cA wral ancom wph wps wa wps wph wa vx cA wph wps ancom rexbii 3imtr4i
    $.

  $( Theorem 19.30 of [Margaris] p. 90 with restricted quantifiers.
     (Contributed by Scott Fenton, 25-Feb-2011.) $)
  r19.30 $p |- ( A. x e. A ( ph \/ ps ) ->
                 ( A. x e. A ph \/ E. x e. A ps ) ) $=
    wps wn wph wi vx cA wral wps wn vx cA wral wph vx cA wral wi wph wps wo vx
    cA wral wph vx cA wral wps vx cA wrex wo wps wn wph vx cA ralim wph wps wo
    wps wn wph wi vx cA wph wps wo wps wph wo wps wn wph wi wph wps orcom wps
    wph df-or bitri ralbii wph vx cA wral wps wn vx cA wral wn wo wps wn vx cA
    wral wn wph vx cA wral wo wph vx cA wral wps vx cA wrex wo wps wn vx cA
    wral wph vx cA wral wi wph vx cA wral wps wn vx cA wral wn orcom wps vx cA
    wrex wps wn vx cA wral wn wph vx cA wral wps vx cA dfrex2 orbi2i wps wn vx
    cA wral wph vx cA wral imor 3bitr4i 3imtr4i $.

  ${
    $d x ph $.
    $( Theorem 19.32 of [Margaris] p. 90 with restricted quantifiers.
       (Contributed by NM, 25-Nov-2003.) $)
    r19.32v $p |- ( A. x e. A ( ph \/ ps ) <-> ( ph \/ A. x e. A ps ) ) $=
      wph wn wps wi vx cA wral wph wn wps vx cA wral wi wph wps wo vx cA wral
      wph wps vx cA wral wo wph wn wps vx cA r19.21v wph wps wo wph wn wps wi
      vx cA wph wps df-or ralbii wph wps vx cA wral df-or 3bitr4i $.
  $}

  $( Restricted quantifier version of Theorem 19.35 of [Margaris] p. 90.
     (Contributed by NM, 20-Sep-2003.) $)
  r19.35 $p |- ( E. x e. A ( ph -> ps ) <->
               ( A. x e. A ph -> E. x e. A ps ) ) $=
    wph vx cA wral wps wn vx cA wral wn wi wph wps wi wn vx cA wral wn wph vx
    cA wral wps vx cA wrex wi wph wps wi vx cA wrex wph wps wi wn vx cA wral
    wph vx cA wral wps wn vx cA wral wn wi wph wps wn wa vx cA wral wph vx cA
    wral wps wn vx cA wral wa wph wps wi wn vx cA wral wph vx cA wral wps wn vx
    cA wral wn wi wn wph wps wn vx cA r19.26 wph wps wn wa wph wps wi wn vx cA
    wph wps annim ralbii wph vx cA wral wps wn vx cA wral df-an 3bitr3i con2bii
    wps vx cA wrex wps wn vx cA wral wn wph vx cA wral wps vx cA dfrex2 imbi2i
    wph wps wi vx cA dfrex2 3bitr4ri $.

  ${
    $d x ps $.
    $( One direction of a restricted quantifier version of Theorem 19.36 of
       [Margaris] p. 90.  The other direction doesn't hold when ` A ` is
       empty.  (Contributed by NM, 22-Oct-2003.) $)
    r19.36av $p |- ( E. x e. A ( ph -> ps ) -> ( A. x e. A ph -> ps ) ) $=
      wph wps wi vx cA wrex wph vx cA wral wps vx cA wrex wi wph vx cA wral wps
      wi wph wps vx cA r19.35 wps vx cA wrex wps wph vx cA wral wps wps vx cA
      vx cv cA wcel wps idd rexlimiv imim2i sylbi $.
  $}

  ${
    r19.37.1 $e |- F/ x ph $.
    $( Restricted version of one direction of Theorem 19.37 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by FL, 13-May-2012.)  (Revised by Mario Carneiro,
       11-Dec-2016.) $)
    r19.37 $p |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) ) $=
      wph wps wi vx cA wrex wph vx cA wral wps vx cA wrex wi wph wps vx cA wrex
      wi wph wps vx cA r19.35 wph wph vx cA wral wps vx cA wrex wph wph vx cA
      r19.37.1 wph vx cv cA wcel ax-1 ralrimi imim1i sylbi $.
  $}

  ${
    $d x ph $.
    $( Restricted version of one direction of Theorem 19.37 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)
    r19.37av $p |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) ) $=
      wph wps vx cA wph vx nfv r19.37 $.
  $}

  $( Restricted quantifier version of Theorem 19.40 of [Margaris] p. 90.
     (Contributed by NM, 2-Apr-2004.) $)
  r19.40 $p |- ( E. x e. A ( ph /\ ps ) ->
               ( E. x e. A ph /\ E. x e. A ps ) ) $=
    wph wps wa vx cA wrex wph vx cA wrex wps vx cA wrex wph wps wa wph vx cA
    wph wps simpl reximi wph wps wa wps vx cA wph wps simpr reximi jca $.

  ${
    r19.41.1 $e |- F/ x ps $.
    $( Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       (Contributed by NM, 1-Nov-2010.) $)
    r19.41 $p |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) ) $=
      vx cv cA wcel wph wps wa wa vx wex vx cv cA wcel wph wa vx wex wps wa wph
      wps wa vx cA wrex wph vx cA wrex wps wa vx cv cA wcel wph wps wa wa vx
      wex vx cv cA wcel wph wa wps wa vx wex vx cv cA wcel wph wa vx wex wps wa
      vx cv cA wcel wph wa wps wa vx cv cA wcel wph wps wa wa vx vx cv cA wcel
      wph wps anass exbii vx cv cA wcel wph wa wps vx r19.41.1 19.41 bitr3i wph
      wps wa vx cA df-rex wph vx cA wrex vx cv cA wcel wph wa vx wex wps wph vx
      cA df-rex anbi1i 3bitr4i $.
  $}

  ${
    $d x ps $.
    $( Restricted quantifier version of Theorem 19.41 of [Margaris] p. 90.
       (Contributed by NM, 17-Dec-2003.) $)
    r19.41v $p |- ( E. x e. A ( ph /\ ps ) <-> ( E. x e. A ph /\ ps ) ) $=
      wph wps vx cA wps vx nfv r19.41 $.
  $}

  ${
    $d x ph $.
    $( Restricted version of Theorem 19.42 of [Margaris] p. 90.  (Contributed
       by NM, 27-May-1998.) $)
    r19.42v $p |- ( E. x e. A ( ph /\ ps ) <-> ( ph /\ E. x e. A ps ) ) $=
      wps wph wa vx cA wrex wps vx cA wrex wph wa wph wps wa vx cA wrex wph wps
      vx cA wrex wa wps wph vx cA r19.41v wph wps wa wps wph wa vx cA wph wps
      ancom rexbii wph wps vx cA wrex ancom 3bitr4i $.
  $}

  $( Restricted version of Theorem 19.43 of [Margaris] p. 90.  (Contributed by
     NM, 27-May-1998.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)
  r19.43 $p |- ( E. x e. A ( ph \/ ps ) <->
               ( E. x e. A ph \/ E. x e. A ps ) ) $=
    wph wn wps wi vx cA wrex wph wn vx cA wral wps vx cA wrex wi wph wps wo vx
    cA wrex wph vx cA wrex wps vx cA wrex wo wph wn wps vx cA r19.35 wph wps wo
    wph wn wps wi vx cA wph wps df-or rexbii wph vx cA wrex wps vx cA wrex wo
    wph vx cA wrex wn wps vx cA wrex wi wph wn vx cA wral wps vx cA wrex wi wph
    vx cA wrex wps vx cA wrex df-or wph wn vx cA wral wph vx cA wrex wn wps vx
    cA wrex wph vx cA ralnex imbi1i bitr4i 3bitr4i $.

  ${
    $d x ps $.
    $( One direction of a restricted quantifier version of Theorem 19.44 of
       [Margaris] p. 90.  The other direction doesn't hold when ` A ` is
       empty.  (Contributed by NM, 2-Apr-2004.) $)
    r19.44av $p |- ( E. x e. A ( ph \/ ps ) -> ( E. x e. A ph \/ ps ) ) $=
      wph wps wo vx cA wrex wph vx cA wrex wps vx cA wrex wo wph vx cA wrex wps
      wo wph wps vx cA r19.43 wps vx cA wrex wps wph vx cA wrex wps wps vx cA
      vx cv cA wcel wps idd rexlimiv orim2i sylbi $.
  $}

  ${
    $d x ph $.
    $( Restricted version of one direction of Theorem 19.45 of [Margaris]
       p. 90.  (The other direction doesn't hold when ` A ` is empty.)
       (Contributed by NM, 2-Apr-2004.) $)
    r19.45av $p |- ( E. x e. A ( ph \/ ps ) -> ( ph \/ E. x e. A ps ) ) $=
      wph wps wo vx cA wrex wph vx cA wrex wps vx cA wrex wo wph wps vx cA wrex
      wo wph wps vx cA r19.43 wph vx cA wrex wph wps vx cA wrex wph wph vx cA
      vx cv cA wcel wph idd rexlimiv orim1i sylbi $.
  $}

  ${
    $d x y $.
    ralcomf.1 $e |- F/_ y A $.
    ralcomf.2 $e |- F/_ x B $.
    $( Commutation of restricted quantifiers.  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)
    ralcomf $p |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph ) $=
      vx cv cA wcel vy cv cB wcel wa wph wi vy wal vx wal vy cv cB wcel vx cv
      cA wcel wa wph wi vx wal vy wal wph vy cB wral vx cA wral wph vx cA wral
      vy cB wral vx cv cA wcel vy cv cB wcel wa wph wi vy wal vx wal vy cv cB
      wcel vx cv cA wcel wa wph wi vy wal vx wal vy cv cB wcel vx cv cA wcel wa
      wph wi vx wal vy wal vx cv cA wcel vy cv cB wcel wa wph wi vy cv cB wcel
      vx cv cA wcel wa wph wi vx vy vx cv cA wcel vy cv cB wcel wph ancomsimp
      2albii vy cv cB wcel vx cv cA wcel wa wph wi vx vy alcom bitri wph vx vy
      cA cB ralcomf.1 r2alf wph vy vx cB cA ralcomf.2 r2alf 3bitr4i $.

    $( Commutation of restricted quantifiers.  (Contributed by Mario Carneiro,
       14-Oct-2016.) $)
    rexcomf $p |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $=
      vx cv cA wcel vy cv cB wcel wa wph wa vy wex vx wex vy cv cB wcel vx cv
      cA wcel wa wph wa vx wex vy wex wph vy cB wrex vx cA wrex wph vx cA wrex
      vy cB wrex vx cv cA wcel vy cv cB wcel wa wph wa vy wex vx wex vy cv cB
      wcel vx cv cA wcel wa wph wa vy wex vx wex vy cv cB wcel vx cv cA wcel wa
      wph wa vx wex vy wex vx cv cA wcel vy cv cB wcel wa wph wa vy cv cB wcel
      vx cv cA wcel wa wph wa vx vy vx cv cA wcel vy cv cB wcel wa vy cv cB
      wcel vx cv cA wcel wa wph vx cv cA wcel vy cv cB wcel ancom anbi1i 2exbii
      vy cv cB wcel vx cv cA wcel wa wph wa vx vy excom bitri wph vx vy cA cB
      ralcomf.1 r2exf wph vy vx cB cA ralcomf.2 r2exf 3bitr4i $.
  $}

  ${
    $d x y $.  $d x B $.  $d y A $.
    $( Commutation of restricted quantifiers.  (Contributed by NM,
       13-Oct-1999.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
    ralcom $p |- ( A. x e. A A. y e. B ph <-> A. y e. B A. x e. A ph ) $=
      wph vx vy cA cB vy cA nfcv vx cB nfcv ralcomf $.

    $( Commutation of restricted quantifiers.  (Contributed by NM,
       19-Nov-1995.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
    rexcom $p |- ( E. x e. A E. y e. B ph <-> E. y e. B E. x e. A ph ) $=
      wph vx vy cA cB vy cA nfcv vx cB nfcv rexcomf $.
  $}

  ${
    $d y z A $.  $d x z B $.  $d x y C $.
    $( Swap 1st and 3rd restricted existential quantifiers.  (Contributed by
       NM, 8-Apr-2015.) $)
    rexcom13 $p |- ( E. x e. A E. y e. B E. z e. C ph
         <-> E. z e. C E. y e. B E. x e. A ph ) $=
      wph vz cC wrex vy cB wrex vx cA wrex wph vz cC wrex vx cA wrex vy cB wrex
      wph vx cA wrex vz cC wrex vy cB wrex wph vx cA wrex vy cB wrex vz cC wrex
      wph vz cC wrex vx vy cA cB rexcom wph vz cC wrex vx cA wrex wph vx cA
      wrex vz cC wrex vy cB wph vx vz cA cC rexcom rexbii wph vx cA wrex vy vz
      cB cC rexcom 3bitri $.
  $}

  ${
    $d w z A $.  $d w z B $.  $d w x y C $.  $d x y z D $.
    $( Rotate existential restricted quantifiers twice.  (Contributed by NM,
       8-Apr-2015.) $)
    rexrot4 $p |- ( E. x e. A E. y e. B E. z e. C E. w e. D ph
        <-> E. z e. C E. w e. D E. x e. A E. y e. B ph ) $=
      wph vw cD wrex vz cC wrex vy cB wrex vx cA wrex wph vy cB wrex vz cC wrex
      vw cD wrex vx cA wrex wph vy cB wrex vx cA wrex vw cD wrex vz cC wrex wph
      vw cD wrex vz cC wrex vy cB wrex wph vy cB wrex vz cC wrex vw cD wrex vx
      cA wph vy vz vw cB cC cD rexcom13 rexbii wph vy cB wrex vx vw vz cA cD cC
      rexcom13 bitri $.
  $}

  ${
    $d y z A $.  $d x z A $.
    $( Commutation of restricted quantifiers.  Note that ` x ` and ` y `
       needn't be distinct (this makes the proof longer).  (Contributed by NM,
       24-Nov-1994.)  (Proof shortened by Mario Carneiro, 17-Oct-2016.) $)
    ralcom2 $p |- ( A. x e. A A. y e. A ph -> A. y e. A A. x e. A ph ) $=
      vx cv vy cv wceq vx wal wph vy cA wral vx cA wral wph vx cA wral vy cA
      wral wi vx cv vy cv wceq vx wal wph vy cA wral vx cA wral wph vx cA wral
      vy cA wral vx cv vy cv wceq vx wal vx cv cA wcel wph vy cA wral wi vx wal
      vy cv cA wcel wph vx cA wral wi vy wal wph vy cA wral vx cA wral wph vx
      cA wral vy cA wral vx cv cA wcel wph vy cA wral wi vy cv cA wcel wph vx
      cA wral wi vx vy vx cv vy cv wceq vx wal vx cv cA wcel vy cv cA wcel wph
      vy cA wral wph vx cA wral vx cv vy cv wceq vx cv cA wcel vy cv cA wcel wb
      vx vx cv vy cv cA eleq1 sps vx cv vy cv wceq vx wal vy cv cA wcel wph wi
      vy wal vx cv cA wcel wph wi vx wal wph vy cA wral wph vx cA wral vx cv vy
      cv wceq vx wal vx cv cA wcel wph wi vx wal vy cv cA wcel wph wi vy wal vx
      cv cA wcel wph wi vy cv cA wcel wph wi vx vy vx cv vy cv wceq vx wal vx
      cv cA wcel vy cv cA wcel wph vx cv vy cv wceq vx cv cA wcel vy cv cA wcel
      wb vx vx cv vy cv cA eleq1 sps imbi1d dral1 bicomd wph vy cA df-ral wph
      vx cA df-ral 3bitr4g imbi12d dral1 wph vy cA wral vx cA df-ral wph vx cA
      wral vy cA df-ral 3bitr4g biimpd vx cv vy cv wceq vx wal wn wph vy cA
      wral vx cA wral wph vx cA wral vy cA wral vx cv vy cv wceq vx wal wn wph
      vy cA wral vx cA wral wa wph vx cA wral vy cA vx cv vy cv wceq vx wal wn
      wph vy cA wral vx cA wral vy vx vy vy nfnae wph vx vy cA cA nfra2 nfan vx
      cv vy cv wceq vx wal wn wph vy cA wral vx cA wral wa vy cv cA wcel wph vx
      cA wral vx cv vy cv wceq vx wal wn wph vy cA wral vx cA wral wa vy cv cA
      wcel wa wph vx cA vx cv vy cv wceq vx wal wn wph vy cA wral vx cA wral wa
      vy cv cA wcel vx vx cv vy cv wceq vx wal wn wph vy cA wral vx cA wral vx
      vx vy vx nfnae wph vy cA wral vx cA nfra1 nfan vx cv vy cv wceq vx wal wn
      wph vy cA wral vx cA wral wa vx vy cv cA vx cv vy cv wceq vx wal wn vx vy
      cv wnfc wph vy cA wral vx cA wral vx vy nfcvf adantr vx cv vy cv wceq vx
      wal wn wph vy cA wral vx cA wral wa vx cA nfcvd nfeld nfan1 wph vy cA
      wral vx cA wral vy cv cA wcel vx cv cA wcel wph wi vx cv vy cv wceq vx
      wal wn wph vy cA wral vx cA wral vy cv cA wcel vx cv cA wcel wph wph vy
      cA wral vx cA wral vx cv cA wcel vy cv cA wcel wph wph vx vy cA cA rsp2
      ancomsd expdimp adantll ralrimi ex ralrimi ex pm2.61i $.
  $}

  ${
    $( A commutative law for restricted quantifiers that swaps the domain of
       the restriction.  (Contributed by NM, 22-Feb-2004.) $)
    ralcom3 $p |- ( A. x e. A ( x e. B -> ph ) <->
                    A. x e. B ( x e. A -> ph ) ) $=
      vx cv cB wcel wph wi vx cA wral vx cv cA wcel wph wi vx cB wral vx cv cB
      wcel wph wi vx cv cA wcel wph wi vx cA cB vx cv cA wcel vx cv cB wcel wph
      pm2.04 ralimi2 vx cv cA wcel wph wi vx cv cB wcel wph wi vx cB cA vx cv
      cB wcel vx cv cA wcel wph pm2.04 ralimi2 impbii $.
  $}

  ${
    $d y A $.  $d x B $.  $d x y $.
    reean.1 $e |- F/ y ph $.
    reean.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Proof shortened by Andrew Salmon, 30-May-2011.) $)
    reean $p |- ( E. x e. A E. y e. B ( ph /\ ps ) <->
                 ( E. x e. A ph /\ E. y e. B ps ) ) $=
      vx cv cA wcel vy cv cB wcel wa wph wps wa wa vy wex vx wex vx cv cA wcel
      wph wa vx wex vy cv cB wcel wps wa vy wex wa wph wps wa vy cB wrex vx cA
      wrex wph vx cA wrex wps vy cB wrex wa vx cv cA wcel vy cv cB wcel wa wph
      wps wa wa vy wex vx wex vx cv cA wcel wph wa vy cv cB wcel wps wa wa vy
      wex vx wex vx cv cA wcel wph wa vx wex vy cv cB wcel wps wa vy wex wa vx
      cv cA wcel vy cv cB wcel wa wph wps wa wa vx cv cA wcel wph wa vy cv cB
      wcel wps wa wa vx vy vx cv cA wcel vy cv cB wcel wph wps an4 2exbii vx cv
      cA wcel wph wa vy cv cB wcel wps wa vx vy vx cv cA wcel wph vy vx cv cA
      wcel vy nfv reean.1 nfan vy cv cB wcel wps vx vy cv cB wcel vx nfv
      reean.2 nfan eean bitri wph wps wa vx vy cA cB r2ex wph vx cA wrex vx cv
      cA wcel wph wa vx wex wps vy cB wrex vy cv cB wcel wps wa vy wex wph vx
      cA df-rex wps vy cB df-rex anbi12i 3bitr4i $.
  $}

  ${
    $d y ph $.  $d x ps $.  $d x y $.  $d y A $.  $d x B $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 9-May-1999.) $)
    reeanv $p |- ( E. x e. A E. y e. B ( ph /\ ps ) <->
                 ( E. x e. A ph /\ E. y e. B ps ) ) $=
      wph wps vx vy cA cB wph vy nfv wps vx nfv reean $.
  $}

  ${
    $d ph y z $.  $d ps x z $.  $d ch x y $.  $d A y $.  $d B x z $.
    $d C x y $.
    $( Rearrange three existential quantifiers.  (Contributed by Jeff Madsen,
       11-Jun-2010.) $)
    3reeanv $p |- ( E. x e. A E. y e. B E. z e. C ( ph /\ ps /\ ch )
                      <-> ( E. x e. A ph /\ E. y e. B ps /\ E. z e. C ch ) ) $=
      wph wps wa vy cB wrex wch vz cC wrex wa vx cA wrex wph vx cA wrex wps vy
      cB wrex wa wch vz cC wrex wa wph wps wch w3a vz cC wrex vy cB wrex vx cA
      wrex wph vx cA wrex wps vy cB wrex wch vz cC wrex w3a wph wps wa vy cB
      wrex wch vz cC wrex wa vx cA wrex wph wps wa vy cB wrex vx cA wrex wch vz
      cC wrex wa wph vx cA wrex wps vy cB wrex wa wch vz cC wrex wa wph wps wa
      vy cB wrex wch vz cC wrex vx cA r19.41v wph wps wa vy cB wrex vx cA wrex
      wph vx cA wrex wps vy cB wrex wa wch vz cC wrex wph wps vx vy cA cB
      reeanv anbi1i bitri wph wps wch w3a vz cC wrex vy cB wrex wph wps wa vy
      cB wrex wch vz cC wrex wa vx cA wph wps wch w3a vz cC wrex vy cB wrex wph
      wps wa wch wa vz cC wrex vy cB wrex wph wps wa vy cB wrex wch vz cC wrex
      wa wph wps wch w3a wph wps wa wch wa vy vz cB cC wph wps wch df-3an
      2rexbii wph wps wa wch vy vz cB cC reeanv bitri rexbii wph vx cA wrex wps
      vy cB wrex wch vz cC wrex df-3an 3bitr4i $.
  $}

  ${
    $d ph y $.  $d ps x $.  $d A y $.  $d B x $.  $d x y $.
    $( Distribute quantification over "or".  (Contributed by Jeff Madsen,
       19-Jun-2010.) $)
    2ralor $p |- ( A. x e. A A. y e. B ( ph \/ ps ) <->
                  ( A. x e. A ph \/ A. y e. B ps ) ) $=
      wph wps wo vy cB wral vx cA wral wph vx cA wral wps vy cB wral wo wph wn
      vx cA wrex wps wn vy cB wrex wa wph vx cA wral wn wps vy cB wral wn wa
      wph wps wo vy cB wral vx cA wral wn wph vx cA wral wps vy cB wral wo wn
      wph wn vx cA wrex wph vx cA wral wn wps wn vy cB wrex wps vy cB wral wn
      wph vx cA rexnal wps vy cB rexnal anbi12i wph wn wps wn wa vy cB wrex vx
      cA wrex wph wps wo vy cB wral wn vx cA wrex wph wn vx cA wrex wps wn vy
      cB wrex wa wph wps wo vy cB wral vx cA wral wn wph wn wps wn wa vy cB
      wrex wph wps wo vy cB wral wn vx cA wph wn wps wn wa vy cB wrex wph wps
      wo wn vy cB wrex wph wps wo vy cB wral wn wph wps wo wn wph wn wps wn wa
      vy cB wph wps ioran rexbii wph wps wo vy cB rexnal bitr3i rexbii wph wn
      wps wn vx vy cA cB reeanv wph wps wo vy cB wral vx cA rexnal 3bitr3ri wph
      vx cA wral wps vy cB wral ioran 3bitr4i con4bii $.
  $}

  $( ` x ` is not free in ` E! x e. A ph ` .  (Contributed by NM,
     19-Mar-1997.) $)
  nfreu1 $p |- F/ x E! x e. A ph $=
    wph vx cA wreu vx cv cA wcel wph wa vx weu vx wph vx cA df-reu vx cv cA
    wcel wph wa vx nfeu1 nfxfr $.

  $( ` x ` is not free in ` E* x e. A ph ` .  (Contributed by NM,
     16-Jun-2017.) $)
  nfrmo1 $p |- F/ x E* x e. A ph $=
    wph vx cA wrmo vx cv cA wcel wph wa vx wmo vx wph vx cA df-rmo vx cv cA
    wcel wph wa vx nfmo1 nfxfr $.

  ${
    $d x z $.  $d y z $.  $d A z $.  $d ph z $.
    nfreud.1 $e |- F/ y ph $.
    nfreud.2 $e |- ( ph -> F/_ x A ) $.
    nfreud.3 $e |- ( ph -> F/ x ps ) $.
    $( Deduction version of ~ nfreu .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 8-Oct-2016.) $)
    nfreud $p |- ( ph -> F/ x E! y e. A ps ) $=
      wps vy cA wreu vy cv cA wcel wps wa vy weu wph vx wps vy cA df-reu wph vy
      cv cA wcel wps wa vx vy nfreud.1 wph vx cv vy cv wceq vx wal wn wa vy cv
      cA wcel wps vx wph vx cv vy cv wceq vx wal wn wa vx vy cv cA vx cv vy cv
      wceq vx wal wn vx vy cv wnfc wph vx vy nfcvf adantl wph vx cA wnfc vx cv
      vy cv wceq vx wal wn nfreud.2 adantr nfeld wph wps vx wnf vx cv vy cv
      wceq vx wal wn nfreud.3 adantr nfand nfeud2 nfxfrd $.

    $( Deduction version of ~ nfrmo .  (Contributed by NM, 17-Jun-2017.) $)
    nfrmod $p |- ( ph -> F/ x E* y e. A ps ) $=
      wps vy cA wrmo vy cv cA wcel wps wa vy wmo wph vx wps vy cA df-rmo wph vy
      cv cA wcel wps wa vx vy nfreud.1 wph vx vy weq vx wal wn wa vy cv cA wcel
      wps vx wph vx vy weq vx wal wn wa vx vy cv cA vx vy weq vx wal wn vx vy
      cv wnfc wph vx vy nfcvf adantl wph vx cA wnfc vx vy weq vx wal wn
      nfreud.2 adantr nfeld wph wps vx wnf vx vy weq vx wal wn nfreud.3 adantr
      nfand nfmod2 nfxfrd $.
  $}

  ${
    nfreu.1 $e |- F/_ x A $.
    nfreu.2 $e |- F/ x ph $.
    $( Bound-variable hypothesis builder for restricted uniqueness.
       (Contributed by NM, 30-Oct-2010.)  (Revised by Mario Carneiro,
       8-Oct-2016.) $)
    nfreu $p |- F/ x E! y e. A ph $=
      wph vy cA wreu vx wnf wtru wph vx vy cA vy nftru vx cA wnfc wtru nfreu.1
      a1i wph vx wnf wtru nfreu.2 a1i nfreud trud $.

    $( Bound-variable hypothesis builder for restricted uniqueness.
       (Contributed by NM, 16-Jun-2017.) $)
    nfrmo $p |- F/ x E* y e. A ph $=
      wph vy cA wrmo vy cv cA wcel wph wa vy wmo vx wph vy cA df-rmo vy cv cA
      wcel wph wa vy wmo vx wnf wtru vy cv cA wcel wph wa vx vy vy nftru vx vy
      weq vx wal wn vy cv cA wcel wph wa vx wnf wtru vx vy weq vx wal wn vy cv
      cA wcel wph vx vx vy weq vx wal wn vx vy cv cA vx vy nfcvf vx cA wnfc vx
      vy weq vx wal wn nfreu.1 a1i nfeld wph vx wnf vx vy weq vx wal wn nfreu.2
      a1i nfand adantl nfmod2 trud nfxfr $.
  $}

  $( An "identity" law of concretion for restricted abstraction.  Special case
     of Definition 2.1 of [Quine] p. 16.  (Contributed by NM, 9-Oct-2003.) $)
  rabid $p |- ( x e. { x e. A | ph } <-> ( x e. A /\ ph ) ) $=
    vx cv cA wcel wph wa vx wph vx cA crab wph vx cA df-rab abeq2i $.

  ${
    $d x A $.
    $( An "identity" law for restricted class abstraction.  (Contributed by NM,
       9-Oct-2003.)  (Proof shortened by Andrew Salmon, 30-May-2011.) $)
    rabid2 $p |- ( A = { x e. A | ph } <-> A. x e. A ph ) $=
      cA vx cv cA wcel wph wa vx cab wceq vx cv cA wcel wph wi vx wal cA wph vx
      cA crab wceq wph vx cA wral cA vx cv cA wcel wph wa vx cab wceq vx cv cA
      wcel vx cv cA wcel wph wa wb vx wal vx cv cA wcel wph wi vx wal vx cv cA
      wcel wph wa vx cA abeq2 vx cv cA wcel wph wi vx cv cA wcel vx cv cA wcel
      wph wa wb vx vx cv cA wcel wph pm4.71 albii bitr4i wph vx cA crab vx cv
      cA wcel wph wa vx cab cA wph vx cA df-rab eqeq2i wph vx cA df-ral 3bitr4i
      $.
  $}

  ${
    $( Equivalent wff's correspond to equal restricted class abstractions.
       Closed theorem form of ~ rabbidva .  (Contributed by NM,
       25-Nov-2013.) $)
    rabbi $p |- ( A. x e. A ( ps <-> ch )
         <-> { x e. A | ps } = { x e. A | ch } ) $=
      vx cv cA wcel wps wa vx cv cA wcel wch wa wb vx wal vx cv cA wcel wps wa
      vx cab vx cv cA wcel wch wa vx cab wceq wps wch wb vx cA wral wps vx cA
      crab wch vx cA crab wceq vx cv cA wcel wps wa vx cv cA wcel wch wa vx
      abbi wps wch wb vx cA wral vx cv cA wcel wps wch wb wi vx wal vx cv cA
      wcel wps wa vx cv cA wcel wch wa wb vx wal wps wch wb vx cA df-ral vx cv
      cA wcel wps wch wb wi vx cv cA wcel wps wa vx cv cA wcel wch wa wb vx vx
      cv cA wcel wps wch pm5.32 albii bitri wps vx cA crab vx cv cA wcel wps wa
      vx cab wch vx cA crab vx cv cA wcel wch wa vx cab wps vx cA df-rab wch vx
      cA df-rab eqeq12i 3bitr4i $.
  $}

  $( Swap with a membership relation in a restricted class abstraction.
     (Contributed by NM, 4-Jul-2005.) $)
  rabswap $p |- { x e. A | x e. B } = { x e. B | x e. A } $=
    vx cv cA wcel vx cv cB wcel wa vx cab vx cv cB wcel vx cv cA wcel wa vx cab
    vx cv cB wcel vx cA crab vx cv cA wcel vx cB crab vx cv cA wcel vx cv cB
    wcel wa vx cv cB wcel vx cv cA wcel wa vx vx cv cA wcel vx cv cB wcel ancom
    abbii vx cv cB wcel vx cA df-rab vx cv cA wcel vx cB df-rab 3eqtr4i $.

  ${
    $d x y $.
    $( The abstraction variable in a restricted class abstraction isn't free.
       (Contributed by NM, 19-Mar-1997.) $)
    nfrab1 $p |- F/_ x { x e. A | ph } $=
      vx wph vx cA crab vx cv cA wcel wph wa vx cab wph vx cA df-rab vx cv cA
      wcel wph wa vx nfab1 nfcxfr $.
  $}

  ${
    $d x z $.  $d y z $.  $d z A $.
    nfrab.1 $e |- F/ x ph $.
    nfrab.2 $e |- F/_ x A $.
    $( A variable not free in a wff remains so in a restricted class
       abstraction.  (Contributed by NM, 13-Oct-2003.)  (Revised by Mario
       Carneiro, 9-Oct-2016.) $)
    nfrab $p |- F/_ x { y e. A | ph } $=
      vx wph vy cA crab vy cv cA wcel wph wa vy cab wph vy cA df-rab vx vy cv
      cA wcel wph wa vy cab wnfc wtru vy cv cA wcel wph wa vx vy vy nftru vx cv
      vy cv wceq vx wal wn vy cv cA wcel wph wa vx wnf wtru vx cv vy cv wceq vx
      wal wn vy cv cA wcel wph vx vz cv cA wcel vy cv cA wcel vx vy vz vx vz cA
      nfrab.2 nfcri vz cv vy cv cA eleq1 dvelimnf wph vx wnf vx cv vy cv wceq
      vx wal wn nfrab.1 a1i nfand adantl nfabd2 trud nfcxfr $.
  $}

  ${
    reubida.1 $e |- F/ x ph $.
    reubida.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by Mario Carneiro, 19-Nov-2016.) $)
    reubida $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $=
      wph vx cv cA wcel wps wa vx weu vx cv cA wcel wch wa vx weu wps vx cA
      wreu wch vx cA wreu wph vx cv cA wcel wps wa vx cv cA wcel wch wa vx
      reubida.1 wph vx cv cA wcel wps wch reubida.2 pm5.32da eubid wps vx cA
      df-reu wch vx cA df-reu 3bitr4g $.
  $}

  ${
    $d x ph $.
    reubidva.1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 13-Nov-2004.) $)
    reubidva $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv reubidva.1 reubida $.
  $}

  ${
    $d x ph $.
    reubidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 17-Oct-1996.) $)
    reubidv $p |- ( ph -> ( E! x e. A ps <-> E! x e. A ch ) ) $=
      wph wps wch vx cA wph wps wch wb vx cv cA wcel reubidv.1 adantr reubidva
      $.
  $}

  ${
    reubiia.1 $e |- ( x e. A -> ( ph <-> ps ) ) $.
    $( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 14-Nov-2004.) $)
    reubiia $p |- ( E! x e. A ph <-> E! x e. A ps ) $=
      vx cv cA wcel wph wa vx weu vx cv cA wcel wps wa vx weu wph vx cA wreu
      wps vx cA wreu vx cv cA wcel wph wa vx cv cA wcel wps wa vx vx cv cA wcel
      wph wps reubiia.1 pm5.32i eubii wph vx cA df-reu wps vx cA df-reu 3bitr4i
      $.
  $}

  ${
    reubii.1 $e |- ( ph <-> ps ) $.
    $( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 22-Oct-1999.) $)
    reubii $p |- ( E! x e. A ph <-> E! x e. A ps ) $=
      wph wps vx cA wph wps wb vx cv cA wcel reubii.1 a1i reubiia $.
  $}

  ${
    rmobida.1 $e |- F/ x ph $.
    rmobida.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)
    rmobida $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $=
      wph vx cv cA wcel wps wa vx wmo vx cv cA wcel wch wa vx wmo wps vx cA
      wrmo wch vx cA wrmo wph vx cv cA wcel wps wa vx cv cA wcel wch wa vx
      rmobida.1 wph vx cv cA wcel wps wch rmobida.2 pm5.32da mobid wps vx cA
      df-rmo wch vx cA df-rmo 3bitr4g $.
  $}

  ${
    $d x ph $.
    rmobidva.1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)
    rmobidva $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $=
      wph wps wch vx cA wph vx nfv rmobidva.1 rmobida $.
  $}

  ${
    $d x ph $.
    rmobidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for restricted existential quantifier (deduction
       rule).  (Contributed by NM, 16-Jun-2017.) $)
    rmobidv $p |- ( ph -> ( E* x e. A ps <-> E* x e. A ch ) ) $=
      wph wps wch vx cA wph wps wch wb vx cv cA wcel rmobidv.1 adantr rmobidva
      $.
  $}

  ${
    rmobiia.1 $e |- ( x e. A -> ( ph <-> ps ) ) $.
    $( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 16-Jun-2017.) $)
    rmobiia $p |- ( E* x e. A ph <-> E* x e. A ps ) $=
      vx cv cA wcel wph wa vx wmo vx cv cA wcel wps wa vx wmo wph vx cA wrmo
      wps vx cA wrmo vx cv cA wcel wph wa vx cv cA wcel wps wa vx vx cv cA wcel
      wph wps rmobiia.1 pm5.32i mobii wph vx cA df-rmo wps vx cA df-rmo 3bitr4i
      $.
  $}

  ${
    rmobii.1 $e |- ( ph <-> ps ) $.
    $( Formula-building rule for restricted existential quantifier (inference
       rule).  (Contributed by NM, 16-Jun-2017.) $)
    rmobii $p |- ( E* x e. A ph <-> E* x e. A ps ) $=
      wph wps vx cA wph wps wb vx cv cA wcel rmobii.1 a1i rmobiia $.
  $}

  ${
    $d y A $.  $d y B $.
    raleq1f.1 $e |- F/_ x A $.
    raleq1f.2 $e |- F/_ x B $.
    $( Equality theorem for restricted universal quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 7-Mar-2004.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
    raleqf $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) ) $=
      cA cB wceq vx cv cA wcel wph wi vx wal vx cv cB wcel wph wi vx wal wph vx
      cA wral wph vx cB wral cA cB wceq vx cv cA wcel wph wi vx cv cB wcel wph
      wi vx vx cA cB raleq1f.1 raleq1f.2 nfeq cA cB wceq vx cv cA wcel vx cv cB
      wcel wph cA cB vx cv eleq2 imbi1d albid wph vx cA df-ral wph vx cB df-ral
      3bitr4g $.

    $( Equality theorem for restricted existential quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 9-Oct-2003.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
    rexeqf $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) ) $=
      cA cB wceq vx cv cA wcel wph wa vx wex vx cv cB wcel wph wa vx wex wph vx
      cA wrex wph vx cB wrex cA cB wceq vx cv cA wcel wph wa vx cv cB wcel wph
      wa vx vx cA cB raleq1f.1 raleq1f.2 nfeq cA cB wceq vx cv cA wcel vx cv cB
      wcel wph cA cB vx cv eleq2 anbi1d exbid wph vx cA df-rex wph vx cB df-rex
      3bitr4g $.

    $( Equality theorem for restricted uniqueness quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by NM, 5-Apr-2004.)  (Revised by Andrew Salmon,
       11-Jul-2011.) $)
    reueq1f $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) ) $=
      cA cB wceq vx cv cA wcel wph wa vx weu vx cv cB wcel wph wa vx weu wph vx
      cA wreu wph vx cB wreu cA cB wceq vx cv cA wcel wph wa vx cv cB wcel wph
      wa vx vx cA cB raleq1f.1 raleq1f.2 nfeq cA cB wceq vx cv cA wcel vx cv cB
      wcel wph cA cB vx cv eleq2 anbi1d eubid wph vx cA df-reu wph vx cB df-reu
      3bitr4g $.

    $( Equality theorem for restricted uniqueness quantifier, with
       bound-variable hypotheses instead of distinct variable restrictions.
       (Contributed by Alexander van der Vekens, 17-Jun-2017.) $)
    rmoeq1f $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) ) $=
      cA cB wceq vx cv cA wcel wph wa vx wmo vx cv cB wcel wph wa vx wmo wph vx
      cA wrmo wph vx cB wrmo cA cB wceq vx cv cA wcel wph wa vx cv cB wcel wph
      wa vx vx cA cB raleq1f.1 raleq1f.2 nfeq cA cB wceq vx cv cA wcel vx cv cB
      wcel wph cA cB vx cv eleq2 anbi1d mobid wph vx cA df-rmo wph vx cB df-rmo
      3bitr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Equality theorem for restricted universal quantifier.  (Contributed by
       NM, 16-Nov-1995.) $)
    raleq $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ph ) ) $=
      wph vx cA cB vx cA nfcv vx cB nfcv raleqf $.

    $( Equality theorem for restricted existential quantifier.  (Contributed by
       NM, 29-Oct-1995.) $)
    rexeq $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ph ) ) $=
      wph vx cA cB vx cA nfcv vx cB nfcv rexeqf $.

    $( Equality theorem for restricted uniqueness quantifier.  (Contributed by
       NM, 5-Apr-2004.) $)
    reueq1 $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ph ) ) $=
      wph vx cA cB vx cA nfcv vx cB nfcv reueq1f $.

    $( Equality theorem for restricted uniqueness quantifier.  (Contributed by
       Alexander van der Vekens, 17-Jun-2017.) $)
    rmoeq1 $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ph ) ) $=
      wph vx cA cB vx cA nfcv vx cB nfcv rmoeq1f $.
  $}

  ${
    $d A x $.  $d B x $.
    raleq1i.1 $e |- A = B $.
    $( Equality inference for restricted universal qualifier.  (Contributed by
       Paul Chapman, 22-Jun-2011.) $)
    raleqi $p |- ( A. x e. A ph <-> A. x e. B ph ) $=
      cA cB wceq wph vx cA wral wph vx cB wral wb raleq1i.1 wph vx cA cB raleq
      ax-mp $.

    $( Equality inference for restricted existential qualifier.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)
    rexeqi $p |- ( E. x e. A ph <-> E. x e. B ph ) $=
      cA cB wceq wph vx cA wrex wph vx cB wrex wb raleq1i.1 wph vx cA cB rexeq
      ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.
    raleq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 13-Nov-2005.) $)
    raleqdv $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ps ) ) $=
      wph cA cB wceq wps vx cA wral wps vx cB wral wb raleq1d.1 wps vx cA cB
      raleq syl $.

    $( Equality deduction for restricted existential quantifier.  (Contributed
       by NM, 14-Jan-2007.) $)
    rexeqdv $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ps ) ) $=
      wph cA cB wceq wps vx cA wrex wps vx cB wrex wb raleq1d.1 wps vx cA cB
      rexeq syl $.
  $}

  ${
    $d x A $.  $d x B $.
    raleqd.1 $e |- ( A = B -> ( ph <-> ps ) ) $.
    $( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 16-Nov-1995.) $)
    raleqbi1dv $p |- ( A = B -> ( A. x e. A ph <-> A. x e. B ps ) ) $=
      cA cB wceq wph vx cA wral wph vx cB wral wps vx cB wral wph vx cA cB
      raleq cA cB wceq wph wps vx cB raleqd.1 ralbidv bitrd $.

    $( Equality deduction for restricted existential quantifier.  (Contributed
       by NM, 18-Mar-1997.) $)
    rexeqbi1dv $p |- ( A = B -> ( E. x e. A ph <-> E. x e. B ps ) ) $=
      cA cB wceq wph vx cA wrex wph vx cB wrex wps vx cB wrex wph vx cA cB
      rexeq cA cB wceq wph wps vx cB raleqd.1 rexbidv bitrd $.

    $( Equality deduction for restricted uniqueness quantifier.  (Contributed
       by NM, 5-Apr-2004.) $)
    reueqd $p |- ( A = B -> ( E! x e. A ph <-> E! x e. B ps ) ) $=
      cA cB wceq wph vx cA wreu wph vx cB wreu wps vx cB wreu wph vx cA cB
      reueq1 cA cB wceq wph wps vx cB raleqd.1 reubidv bitrd $.

    $( Equality deduction for restricted uniqueness quantifier.  (Contributed
       by Alexander van der Vekens, 17-Jun-2017.) $)
    rmoeqd $p |- ( A = B -> ( E* x e. A ph <-> E* x e. B ps ) ) $=
      cA cB wceq wph vx cA wrmo wph vx cB wrmo wps vx cB wrmo wph vx cA cB
      rmoeq1 cA cB wceq wph wps vx cB raleqd.1 rmobidv bitrd $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    raleqbidv.1 $e |- ( ph -> A = B ) $.
    raleqbidv.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 6-Nov-2007.) $)
    raleqbidv $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $=
      wph wps vx cA wral wps vx cB wral wch vx cB wral wph wps vx cA cB
      raleqbidv.1 raleqdv wph wps wch vx cB raleqbidv.2 ralbidv bitrd $.

    $( Equality deduction for restricted universal quantifier.  (Contributed by
       NM, 6-Nov-2007.) $)
    rexeqbidv $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $=
      wph wps vx cA wrex wps vx cB wrex wch vx cB wrex wph wps vx cA cB
      raleqbidv.1 rexeqdv wph wps wch vx cB raleqbidv.2 rexbidv bitrd $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ph $.
    raleqbidva.1 $e |- ( ph -> A = B ) $.
    raleqbidva.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Equality deduction for restricted universal quantifier.  (Contributed by
       Mario Carneiro, 5-Jan-2017.) $)
    raleqbidva $p |- ( ph -> ( A. x e. A ps <-> A. x e. B ch ) ) $=
      wph wps vx cA wral wch vx cA wral wch vx cB wral wph wps wch vx cA
      raleqbidva.2 ralbidva wph wch vx cA cB raleqbidva.1 raleqdv bitrd $.

    $( Equality deduction for restricted universal quantifier.  (Contributed by
       Mario Carneiro, 5-Jan-2017.) $)
    rexeqbidva $p |- ( ph -> ( E. x e. A ps <-> E. x e. B ch ) ) $=
      wph wps vx cA wrex wch vx cA wrex wch vx cB wrex wph wps wch vx cA
      raleqbidva.2 rexbidva wph wch vx cA cB raleqbidva.1 rexeqdv bitrd $.
  $}

  $( Unrestricted "at most one" implies restricted "at most one".  (Contributed
     by NM, 16-Jun-2017.) $)
  mormo $p |- ( E* x ph -> E* x e. A ph ) $=
    wph vx wmo vx cv cA wcel wph wa vx wmo wph vx cA wrmo wph vx cv cA wcel vx
    moan wph vx cA df-rmo sylibr $.

  $( Restricted uniqueness in terms of "at most one."  (Contributed by NM,
     23-May-1999.)  (Revised by NM, 16-Jun-2017.) $)
  reu5 $p |- ( E! x e. A ph <-> ( E. x e. A ph /\ E* x e. A ph ) ) $=
    vx cv cA wcel wph wa vx weu vx cv cA wcel wph wa vx wex vx cv cA wcel wph
    wa vx wmo wa wph vx cA wreu wph vx cA wrex wph vx cA wrmo wa vx cv cA wcel
    wph wa vx eu5 wph vx cA df-reu wph vx cA wrex vx cv cA wcel wph wa vx wex
    wph vx cA wrmo vx cv cA wcel wph wa vx wmo wph vx cA df-rex wph vx cA
    df-rmo anbi12i 3bitr4i $.

  $( Restricted unique existence implies restricted existence.  (Contributed by
     NM, 19-Aug-1999.) $)
  reurex $p |- ( E! x e. A ph -> E. x e. A ph ) $=
    wph vx cA wreu wph vx cA wrex wph vx cA wrmo wph vx cA reu5 simplbi $.

  $( Restricted existential uniqueness implies restricted "at most one."
     (Contributed by NM, 16-Jun-2017.) $)
  reurmo $p |- ( E! x e. A ph -> E* x e. A ph ) $=
    wph vx cA wreu wph vx cA wrex wph vx cA wrmo wph vx cA reu5 simprbi $.

  $( Restricted "at most one" in term of uniqueness.  (Contributed by NM,
     16-Jun-2017.) $)
  rmo5 $p |- ( E* x e. A ph <-> ( E. x e. A ph -> E! x e. A ph ) ) $=
    vx cv cA wcel wph wa vx wmo vx cv cA wcel wph wa vx wex vx cv cA wcel wph
    wa vx weu wi wph vx cA wrmo wph vx cA wrex wph vx cA wreu wi vx cv cA wcel
    wph wa vx df-mo wph vx cA df-rmo wph vx cA wrex vx cv cA wcel wph wa vx wex
    wph vx cA wreu vx cv cA wcel wph wa vx weu wph vx cA df-rex wph vx cA
    df-reu imbi12i 3bitr4i $.

  $( Nonexistence implies restricted "at most one".  (Contributed by NM,
     17-Jun-2017.) $)
  nrexrmo $p |- ( -. E. x e. A ph -> E* x e. A ph ) $=
    wph vx cA wrex wn wph vx cA wrex wph vx cA wreu wi wph vx cA wrmo wph vx cA
    wrex wph vx cA wreu pm2.21 wph vx cA rmo5 sylibr $.

  ${
    $d x z $.  $d y z $.  $d z A $.  $d z ps $.  $d z ph $.
    cbvralf.1 $e |- F/_ x A $.
    cbvralf.2 $e |- F/_ y A $.
    cbvralf.3 $e |- F/ y ph $.
    cbvralf.4 $e |- F/ x ps $.
    cbvralf.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 7-Mar-2004.)  (Revised by Mario Carneiro,
       9-Oct-2016.) $)
    cbvralf $p |- ( A. x e. A ph <-> A. y e. A ps ) $=
      vx cv cA wcel wph wi vx wal vy cv cA wcel wps wi vy wal wph vx cA wral
      wps vy cA wral vx cv cA wcel wph wi vx wal vz cv cA wcel wph vx vz wsb wi
      vz wal vy cv cA wcel wps wi vy wal vx cv cA wcel wph wi vz cv cA wcel wph
      vx vz wsb wi vx vz vx cv cA wcel wph wi vz nfv vz cv cA wcel wph vx vz
      wsb vx vx vz cA cbvralf.1 nfcri wph vx vz nfs1v nfim vx cv vz cv wceq vx
      cv cA wcel vz cv cA wcel wph wph vx vz wsb vx cv vz cv cA eleq1 wph vx vz
      sbequ12 imbi12d cbval vz cv cA wcel wph vx vz wsb wi vy cv cA wcel wps wi
      vz vy vz cv cA wcel wph vx vz wsb vy vy vz cA cbvralf.2 nfcri wph vx vz
      vy cbvralf.3 nfsb nfim vy cv cA wcel wps wi vz nfv vz cv vy cv wceq vz cv
      cA wcel vy cv cA wcel wph vx vz wsb wps vz cv vy cv cA eleq1 vz cv vy cv
      wceq wph vx vz wsb wph vx vy wsb wps wph vz vy vx sbequ wph wps vx vy
      cbvralf.4 cbvralf.5 sbie syl6bb imbi12d cbval bitri wph vx cA df-ral wps
      vy cA df-ral 3bitr4i $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by FL, 27-Apr-2008.)  (Revised by Mario Carneiro,
       9-Oct-2016.) $)
    cbvrexf $p |- ( E. x e. A ph <-> E. y e. A ps ) $=
      wph wn vx cA wral wn wps wn vy cA wral wn wph vx cA wrex wps vy cA wrex
      wph wn vx cA wral wps wn vy cA wral wph wn wps wn vx vy cA cbvralf.1
      cbvralf.2 wph vy cbvralf.3 nfn wps vx cbvralf.4 nfn vx cv vy cv wceq wph
      wps cbvralf.5 notbid cbvralf notbii wph vx cA dfrex2 wps vy cA dfrex2
      3bitr4i $.
  $}

  ${
    $d x z A $.  $d y z A $.  $d z ph $.  $d z ps $.
    cbvral.1 $e |- F/ y ph $.
    cbvral.2 $e |- F/ x ps $.
    cbvral.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 31-Jul-2003.) $)
    cbvral $p |- ( A. x e. A ph <-> A. y e. A ps ) $=
      wph wps vx vy cA vx cA nfcv vy cA nfcv cbvral.1 cbvral.2 cbvral.3 cbvralf
      $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 31-Jul-2003.)  (Proof shortened by Andrew Salmon,
       8-Jun-2011.) $)
    cbvrex $p |- ( E. x e. A ph <-> E. y e. A ps ) $=
      wph wps vx vy cA vx cA nfcv vy cA nfcv cbvral.1 cbvral.2 cbvral.3 cbvrexf
      $.

    $( Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by Mario Carneiro, 15-Oct-2016.) $)
    cbvreu $p |- ( E! x e. A ph <-> E! y e. A ps ) $=
      vx cv cA wcel wph wa vx weu vy cv cA wcel wps wa vy weu wph vx cA wreu
      wps vy cA wreu vx cv cA wcel wph wa vx weu vx cv cA wcel wph wa vx vz wsb
      vz weu vx cv cA wcel vx vz wsb wph vx vz wsb wa vz weu vy cv cA wcel wps
      wa vy weu vx cv cA wcel wph wa vx vz vx cv cA wcel wph wa vz nfv sb8eu vx
      cv cA wcel wph wa vx vz wsb vx cv cA wcel vx vz wsb wph vx vz wsb wa vz
      vx cv cA wcel wph vx vz sban eubii vx cv cA wcel vx vz wsb wph vx vz wsb
      wa vz weu vz cv cA wcel wph vx vz wsb wa vz weu vy cv cA wcel wps wa vy
      weu vx cv cA wcel vx vz wsb wph vx vz wsb wa vz cv cA wcel wph vx vz wsb
      wa vz vx cv cA wcel vx vz wsb vz cv cA wcel wph vx vz wsb vz vx cA
      clelsb3 anbi1i eubii vz cv cA wcel wph vx vz wsb wa vy cv cA wcel wps wa
      vz vy vz cv cA wcel wph vx vz wsb vy vz cv cA wcel vy nfv wph vx vz vy
      cbvral.1 nfsb nfan vy cv cA wcel wps wa vz nfv vz cv vy cv wceq vz cv cA
      wcel vy cv cA wcel wph vx vz wsb wps vz cv vy cv cA eleq1 vz cv vy cv
      wceq wph vx vz wsb wph vx vy wsb wps wph vz vy vx sbequ wph wps vx vy
      cbvral.2 cbvral.3 sbie syl6bb anbi12d cbveu bitri 3bitri wph vx cA df-reu
      wps vy cA df-reu 3bitr4i $.

    $( Change the bound variable of restricted "at most one" using implicit
       substitution.  (Contributed by NM, 16-Jun-2017.) $)
    cbvrmo $p |- ( E* x e. A ph <-> E* y e. A ps ) $=
      wph vx cA wrex wph vx cA wreu wi wps vy cA wrex wps vy cA wreu wi wph vx
      cA wrmo wps vy cA wrmo wph vx cA wrex wps vy cA wrex wph vx cA wreu wps
      vy cA wreu wph wps vx vy cA cbvral.1 cbvral.2 cbvral.3 cbvrex wph wps vx
      vy cA cbvral.1 cbvral.2 cbvral.3 cbvreu imbi12i wph vx cA rmo5 wps vy cA
      rmo5 3bitr4i $.
  $}

  ${
    $d z x A $.  $d y A $.  $d z y ph $.  $d z x ps $.
    cbvralv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Change the bound variable of a restricted universal quantifier using
       implicit substitution.  (Contributed by NM, 28-Jan-1997.) $)
    cbvralv $p |- ( A. x e. A ph <-> A. y e. A ps ) $=
      wph wps vx vy cA wph vy nfv wps vx nfv cbvralv.1 cbvral $.

    $( Change the bound variable of a restricted existential quantifier using
       implicit substitution.  (Contributed by NM, 2-Jun-1998.) $)
    cbvrexv $p |- ( E. x e. A ph <-> E. y e. A ps ) $=
      wph wps vx vy cA wph vy nfv wps vx nfv cbvralv.1 cbvrex $.

    $( Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by NM, 5-Apr-2004.)  (Revised by
       Mario Carneiro, 15-Oct-2016.) $)
    cbvreuv $p |- ( E! x e. A ph <-> E! y e. A ps ) $=
      wph wps vx vy cA wph vy nfv wps vx nfv cbvralv.1 cbvreu $.

    $( Change the bound variable of a restricted uniqueness quantifier using
       implicit substitution.  (Contributed by Alexander van der Vekens,
       17-Jun-2017.) $)
    cbvrmov $p |- ( E* x e. A ph <-> E* y e. A ps ) $=
      wph wps vx vy cA wph vy nfv wps vx nfv cbvralv.1 cbvrmo $.
  $}

  ${
    $d A y $.  $d ps y $.  $d B x $.  $d ch x $.  $d x ph y $.
    cbvraldva2.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    cbvraldva2.2 $e |- ( ( ph /\ x = y ) -> A = B ) $.
    $( Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution which also changes the quantifier
       domain.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
    cbvraldva2 $p |- ( ph -> ( A. x e. A ps <-> A. y e. B ch ) ) $=
      wph vx cv cA wcel wps wi vx wal vy cv cB wcel wch wi vy wal wps vx cA
      wral wch vy cB wral wph vx cv cA wcel wps wi vy cv cB wcel wch wi vx vy
      wph vx vy weq wa vx cv cA wcel vy cv cB wcel wps wch wph vx vy weq wa vx
      cv vy cv cA cB wph vx vy weq simpr cbvraldva2.2 eleq12d cbvraldva2.1
      imbi12d cbvaldva wps vx cA df-ral wch vy cB df-ral 3bitr4g $.

    $( Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution which also changes the quantifier
       domain.  Deduction form.  (Contributed by David Moews, 1-May-2017.) $)
    cbvrexdva2 $p |- ( ph -> ( E. x e. A ps <-> E. y e. B ch ) ) $=
      wph vx cv cA wcel wps wa vx wex vy cv cB wcel wch wa vy wex wps vx cA
      wrex wch vy cB wrex wph vx cv cA wcel wps wa vy cv cB wcel wch wa vx vy
      wph vx vy weq wa vx cv cA wcel vy cv cB wcel wps wch wph vx vy weq wa vx
      cv vy cv cA cB wph vx vy weq simpr cbvraldva2.2 eleq12d cbvraldva2.1
      anbi12d cbvexdva wps vx cA df-rex wch vy cB df-rex 3bitr4g $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d A x y $.  $d x ph y $.
    cbvraldva.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a restricted universal
       quantifier with implicit substitution.  Deduction form.  (Contributed by
       David Moews, 1-May-2017.) $)
    cbvraldva $p |- ( ph -> ( A. x e. A ps <-> A. y e. A ch ) ) $=
      wph wps wch vx vy cA cA cbvraldva.1 wph vx vy weq wa cA eqidd cbvraldva2
      $.

    $( Rule used to change the bound variable in a restricted existential
       quantifier with implicit substitution.  Deduction form.  (Contributed by
       David Moews, 1-May-2017.) $)
    cbvrexdva $p |- ( ph -> ( E. x e. A ps <-> E. y e. A ch ) ) $=
      wph wps wch vx vy cA cA cbvraldva.1 wph vx vy weq wa cA eqidd cbvrexdva2
      $.
  $}

  ${
    $d x A $.  $d z A $.  $d x y B $.  $d z y B $.  $d w B $.  $d z ph $.
    $d y ps $.  $d x ch $.  $d w ch $.
    cbvral2v.1 $e |- ( x = z -> ( ph <-> ch ) ) $.
    cbvral2v.2 $e |- ( y = w -> ( ch <-> ps ) ) $.
    $( Change bound variables of double restricted universal quantification,
       using implicit substitution.  (Contributed by NM, 10-Aug-2004.) $)
    cbvral2v $p |- ( A. x e. A A. y e. B ph <-> A. z e. A A. w e. B ps ) $=
      wph vy cB wral vx cA wral wch vy cB wral vz cA wral wps vw cB wral vz cA
      wral wph vy cB wral wch vy cB wral vx vz cA vx cv vz cv wceq wph wch vy
      cB cbvral2v.1 ralbidv cbvralv wch vy cB wral wps vw cB wral vz cA wch wps
      vy vw cB cbvral2v.2 cbvralv ralbii bitri $.
  $}

  ${
    $d A x $.  $d A z $.  $d B w $.  $d B x y $.  $d B z y $.  $d ch w $.
    $d ch x $.  $d ph z $.  $d ps y $.
    cbvrex2v.1 $e |- ( x = z -> ( ph <-> ch ) ) $.
    cbvrex2v.2 $e |- ( y = w -> ( ch <-> ps ) ) $.
    $( Change bound variables of double restricted universal quantification,
       using implicit substitution.  (Contributed by FL, 2-Jul-2012.) $)
    cbvrex2v $p |- ( E. x e. A E. y e. B ph <-> E. z e. A E. w e. B ps ) $=
      wph vy cB wrex vx cA wrex wch vy cB wrex vz cA wrex wps vw cB wrex vz cA
      wrex wph vy cB wrex wch vy cB wrex vx vz cA vx vz weq wph wch vy cB
      cbvrex2v.1 rexbidv cbvrexv wch vy cB wrex wps vw cB wrex vz cA wch wps vy
      vw cB cbvrex2v.2 cbvrexv rexbii bitri $.
  $}

  ${
    $d w ph $.  $d z ps $.  $d x ch $.  $d v ch $.  $d y u th $.  $d x A $.
    $d w A $.  $d x y B $.  $d w y B $.  $d v B $.  $d x y z C $.
    $d w y z C $.  $d v z C $.  $d z y C $.  $d z C $.  $d u C $.
    cbvral3v.1 $e |- ( x = w -> ( ph <-> ch ) ) $.
    cbvral3v.2 $e |- ( y = v -> ( ch <-> th ) ) $.
    cbvral3v.3 $e |- ( z = u -> ( th <-> ps ) ) $.
    $( Change bound variables of triple restricted universal quantification,
       using implicit substitution.  (Contributed by NM, 10-May-2005.) $)
    cbvral3v $p |- ( A. x e. A A. y e. B A. z e. C ph <->
                     A. w e. A A. v e. B A. u e. C ps ) $=
      wph vz cC wral vy cB wral vx cA wral wch vz cC wral vy cB wral vw cA wral
      wps vu cC wral vv cB wral vw cA wral wph vz cC wral vy cB wral wch vz cC
      wral vy cB wral vx vw cA vx cv vw cv wceq wph wch vy vz cB cC cbvral3v.1
      2ralbidv cbvralv wch vz cC wral vy cB wral wps vu cC wral vv cB wral vw
      cA wch wps wth vy vz vv vu cB cC cbvral3v.2 cbvral3v.3 cbvral2v ralbii
      bitri $.
  $}

  ${
    $d z x A $.  $d y A $.  $d z y ph $.
    $( Change bound variable by using a substitution.  (Contributed by NM,
       20-Nov-2005.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
    cbvralsv $p |- ( A. x e. A ph <-> A. y e. A [ y / x ] ph ) $=
      wph vx cA wral wph vx vz wsb vz cA wral wph vx vy wsb vy cA wral wph wph
      vx vz wsb vx vz cA wph vz nfv wph vx vz nfs1v wph vx vz sbequ12 cbvral
      wph vx vz wsb wph vx vy wsb vz vy cA wph vx vz vy wph vy nfv nfsb wph vx
      vy wsb vz nfv wph vz vy vx sbequ cbvral bitri $.
  $}

  ${
    $d z x A $.  $d y z ph $.  $d y A $.
    $( Change bound variable by using a substitution.  (Contributed by NM,
       2-Mar-2008.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
    cbvrexsv $p |- ( E. x e. A ph <-> E. y e. A [ y / x ] ph ) $=
      wph vx cA wrex wph vx vz wsb vz cA wrex wph vx vy wsb vy cA wrex wph wph
      vx vz wsb vx vz cA wph vz nfv wph vx vz nfs1v wph vx vz sbequ12 cbvrex
      wph vx vz wsb wph vx vy wsb vz vy cA wph vx vz vy wph vy nfv nfsb wph vx
      vy wsb vz nfv wph vz vy vx sbequ cbvrex bitri $.
  $}

  ${
    $d x y z $.  $d y z ph $.  $d x z ps $.
    sbralie.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Implicit to explicit substitution that swaps variables in a quantified
       expression.  (Contributed by NM, 5-Sep-2004.) $)
    sbralie $p |- ( [ x / y ] A. x e. y ph <-> A. y e. x ps ) $=
      wph vx vy cv wral vy vx wsb wph vx vz wsb vz vx cv wral wps vy vx cv wral
      wph vx vy cv wral vy vx wsb wph vx vz wsb vz vy cv wral vy vx wsb wph vx
      vz wsb vz vx cv wral wph vx vy cv wral wph vx vz wsb vz vy cv wral vy vx
      wph vx vz vy cv cbvralsv sbbii wph vx vz wsb vz vy cv wral wph vx vz wsb
      vz vx cv wral vy vx wph vx vz wsb vz vx cv wral vy nfv wph vx vz wsb vz
      vy cv vx cv raleq sbie bitri wph vx vz wsb vz vx cv wral wph vx vz wsb vz
      vy wsb vy vx cv wral wps vy vx cv wral wph vx vz wsb vz vy vx cv cbvralsv
      wph vx vz wsb vz vy wsb wps vy vx cv wph vx vz wsb vz vy wsb wph vx vy
      wsb wps wph vx vy vz wph vz nfv sbco2 wph wps vx vy wps vx nfv sbralie.1
      sbie bitri ralbii bitri bitri $.
  $}

  ${
    rabbiia.1 $e |- ( x e. A -> ( ph <-> ps ) ) $.
    $( Equivalent wff's yield equal restricted class abstractions (inference
       rule).  (Contributed by NM, 22-May-1999.) $)
    rabbiia $p |- { x e. A | ph } = { x e. A | ps } $=
      vx cv cA wcel wph wa vx cab vx cv cA wcel wps wa vx cab wph vx cA crab
      wps vx cA crab vx cv cA wcel wph wa vx cv cA wcel wps wa vx vx cv cA wcel
      wph wps rabbiia.1 pm5.32i abbii wph vx cA df-rab wps vx cA df-rab 3eqtr4i
      $.
  $}

  ${
    $d x ph $.
    rabbidva.1 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  (Contributed by NM, 28-Nov-2003.) $)
    rabbidva $p |- ( ph -> { x e. A | ps } = { x e. A | ch } ) $=
      wph wps wch wb vx cA wral wps vx cA crab wch vx cA crab wceq wph wps wch
      wb vx cA rabbidva.1 ralrimiva wps wch vx cA rabbi sylib $.
  $}

  ${
    $d x ph $.
    rabbidv.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalent wff's yield equal restricted class abstractions (deduction
       rule).  (Contributed by NM, 10-Feb-1995.) $)
    rabbidv $p |- ( ph -> { x e. A | ps } = { x e. A | ch } ) $=
      wph wps wch vx cA wph wps wch wb vx cv cA wcel rabbidv.1 adantr rabbidva
      $.
  $}

  ${
    $d y A $.  $d y B $.
    rabeqf.1 $e |- F/_ x A $.
    rabeqf.2 $e |- F/_ x B $.
    $( Equality theorem for restricted class abstractions, with bound-variable
       hypotheses instead of distinct variable restrictions.  (Contributed by
       NM, 7-Mar-2004.) $)
    rabeqf $p |- ( A = B -> { x e. A | ph } = { x e. B | ph } ) $=
      cA cB wceq vx cv cA wcel wph wa vx cab vx cv cB wcel wph wa vx cab wph vx
      cA crab wph vx cB crab cA cB wceq vx cv cA wcel wph wa vx cv cB wcel wph
      wa vx vx cA cB rabeqf.1 rabeqf.2 nfeq cA cB wceq vx cv cA wcel vx cv cB
      wcel wph cA cB vx cv eleq2 anbi1d abbid wph vx cA df-rab wph vx cB df-rab
      3eqtr4g $.
  $}

  ${
    $d x y A $.  $d x y B $.
    $( Equality theorem for restricted class abstractions.  (Contributed by NM,
       15-Oct-2003.) $)
    rabeq $p |- ( A = B -> { x e. A | ph } = { x e. B | ph } ) $=
      wph vx cA cB vx cA nfcv vx cB nfcv rabeqf $.
  $}

  ${
    $d A x $.  $d B x $.  $d ph x $.
    rabeqbidv.1 $e |- ( ph -> A = B ) $.
    rabeqbidv.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equality of restricted class abstractions.  (Contributed by Jeff Madsen,
       1-Dec-2009.) $)
    rabeqbidv $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $=
      wph wps vx cA crab wps vx cB crab wch vx cB crab wph cA cB wceq wps vx cA
      crab wps vx cB crab wceq rabeqbidv.1 wps vx cA cB rabeq syl wph wps wch
      vx cB rabeqbidv.2 rabbidv eqtrd $.
  $}

  ${
    $d A x $.  $d B x $.  $d ph x $.
    rabeqbidva.1 $e |- ( ph -> A = B ) $.
    rabeqbidva.2 $e |- ( ( ph /\ x e. A ) -> ( ps <-> ch ) ) $.
    $( Equality of restricted class abstractions.  (Contributed by Mario
       Carneiro, 26-Jan-2017.) $)
    rabeqbidva $p |- ( ph -> { x e. A | ps } = { x e. B | ch } ) $=
      wph wps vx cA crab wch vx cA crab wch vx cB crab wph wps wch vx cA
      rabeqbidva.2 rabbidva wph cA cB wceq wch vx cA crab wch vx cB crab wceq
      rabeqbidva.1 wch vx cA cB rabeq syl eqtrd $.
  $}

  ${
    rabeqi.1 $e |- A = { x e. B | ph } $.
    $( Inference rule from equality of a class variable and a restricted class
       abstraction.  (Contributed by NM, 16-Feb-2004.) $)
    rabeq2i $p |- ( x e. A <-> ( x e. B /\ ph ) ) $=
      vx cv cA wcel vx cv wph vx cB crab wcel vx cv cB wcel wph wa cA wph vx cB
      crab vx cv rabeqi.1 eleq2i wph vx cB rabid bitri $.
  $}

  ${
    $d x z $.  $d y z $.  $d A z $.  $d ph z $.  $d ps z $.
    cbvrab.1 $e |- F/_ x A $.
    cbvrab.2 $e |- F/_ y A $.
    cbvrab.3 $e |- F/ y ph $.
    cbvrab.4 $e |- F/ x ps $.
    cbvrab.5 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule to change the bound variable in a restricted class abstraction,
       using implicit substitution.  This version has bound-variable hypotheses
       in place of distinct variable conditions.  (Contributed by Andrew
       Salmon, 11-Jul-2011.)  (Revised by Mario Carneiro, 9-Oct-2016.) $)
    cbvrab $p |- { x e. A | ph } = { y e. A | ps } $=
      vx cv cA wcel wph wa vx cab vy cv cA wcel wps wa vy cab wph vx cA crab
      wps vy cA crab vx cv cA wcel wph wa vx cab vz cv cA wcel wph vx vz wsb wa
      vz cab vy cv cA wcel wps wa vy cab vx cv cA wcel wph wa vz cv cA wcel wph
      vx vz wsb wa vx vz vx cv cA wcel wph wa vz nfv vz cv cA wcel wph vx vz
      wsb vx vx vz cA cbvrab.1 nfcri wph vx vz nfs1v nfan vx cv vz cv wceq vx
      cv cA wcel vz cv cA wcel wph wph vx vz wsb vx cv vz cv cA eleq1 wph vx vz
      sbequ12 anbi12d cbvab vz cv cA wcel wph vx vz wsb wa vy cv cA wcel wps wa
      vz vy vz cv cA wcel wph vx vz wsb vy vy vz cA cbvrab.2 nfcri wph vx vz vy
      cbvrab.3 nfsb nfan vy cv cA wcel wps wa vz nfv vz cv vy cv wceq vz cv cA
      wcel vy cv cA wcel wph vx vz wsb wps vz cv vy cv cA eleq1 vz cv vy cv
      wceq wph vx vz wsb wph vx vy wsb wps wph vz vy vx sbequ wph wps vx vy
      cbvrab.4 cbvrab.5 sbie syl6bb anbi12d cbvab eqtri wph vx cA df-rab wps vy
      cA df-rab 3eqtr4i $.
  $}

  ${
    $d x y z A $.  $d y ph $.  $d x ps $.
    cbvrabv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule to change the bound variable in a restricted class abstraction,
       using implicit substitution.  (Contributed by NM, 26-May-1999.) $)
    cbvrabv $p |- { x e. A | ph } = { y e. A | ps } $=
      wph wps vx vy cA vx cA nfcv vy cA nfcv wph vy nfv wps vx nfv cbvrabv.1
      cbvrab $.
  $}


