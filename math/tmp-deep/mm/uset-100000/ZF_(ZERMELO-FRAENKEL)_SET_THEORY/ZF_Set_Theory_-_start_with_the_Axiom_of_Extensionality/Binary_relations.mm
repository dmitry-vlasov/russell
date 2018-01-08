
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Disjointness.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                     Binary relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Extend wff notation to include the general binary relation predicate.
     Note that the syntax is simply three class symbols in a row.  Since binary
     relations are the only possible wff expressions consisting of three class
     expressions in a row, the syntax is unambiguous.  (For an example of how
     syntax could become ambiguous if we are not careful, see the comment in
     ~ cneg .) $)
  wbr $a wff A R B $.

  $( Define a general binary relation.  Note that the syntax is simply three
     class symbols in a row.  Definition 6.18 of [TakeutiZaring] p. 29
     generalized to arbitrary classes.  Class ` R ` often denotes a relation
     such as " ` < ` " that compares two classes ` A ` and ` B ` , which might
     be numbers such as ` 1 ` and ` 2 ` (see ~ df-ltxr for the specific
     definition of ` < ` ).  As a wff, relations are true or false.  For
     example, ` ( R = { <. 2 , 6 >. , <. 3 , 9 >. } -> 3 R 9 ) ` ( ~ ex-br ).
     Often class ` R ` meets the ` Rel ` criteria to be defined in ~ df-rel ,
     and in particular ` R ` may be a function (see ~ df-fun ).  This
     definition of relations is well-defined, although not very meaningful,
     when classes ` A ` and/or ` B ` are proper classes (i.e. are not sets).
     On the other hand, we often find uses for this definition when ` R ` is a
     proper class.  (Contributed by NM, 31-Dec-1993.) $)
  df-br $a |- ( A R B <-> <. A , B >. e. R ) $.

  $( Equality theorem for binary relations.  (Contributed by NM,
     4-Jun-1995.) $)
  breq $p |- ( R = S -> ( A R B <-> A S B ) ) $=
    cR cS wceq cA cB cop cR wcel cA cB cop cS wcel cA cB cR wbr cA cB cS wbr cR
    cS cA cB cop eleq2 cA cB cR df-br cA cB cS df-br 3bitr4g $.

  $( Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)
  breq1 $p |- ( A = B -> ( A R C <-> B R C ) ) $=
    cA cB wceq cA cC cop cR wcel cB cC cop cR wcel cA cC cR wbr cB cC cR wbr cA
    cB wceq cA cC cop cB cC cop cR cA cB cC opeq1 eleq1d cA cC cR df-br cB cC
    cR df-br 3bitr4g $.

  $( Equality theorem for a binary relation.  (Contributed by NM,
     31-Dec-1993.) $)
  breq2 $p |- ( A = B -> ( C R A <-> C R B ) ) $=
    cA cB wceq cC cA cop cR wcel cC cB cop cR wcel cC cA cR wbr cC cB cR wbr cA
    cB wceq cC cA cop cC cB cop cR cA cB cC opeq2 eleq1d cC cA cR df-br cC cB
    cR df-br 3bitr4g $.

  $( Equality theorem for a binary relation.  (Contributed by NM,
     8-Feb-1996.) $)
  breq12 $p |- ( ( A = B /\ C = D ) -> ( A R C <-> B R D ) ) $=
    cA cB wceq cA cC cR wbr cB cC cR wbr cC cD wceq cB cD cR wbr cA cB cC cR
    breq1 cC cD cB cR breq2 sylan9bb $.

  ${
    breqi.1 $e |- R = S $.
    $( Equality inference for binary relations.  (Contributed by NM,
       19-Feb-2005.) $)
    breqi $p |- ( A R B <-> A S B ) $=
      cR cS wceq cA cB cR wbr cA cB cS wbr wb breqi.1 cA cB cR cS breq ax-mp $.
  $}

  ${
    breq1i.1 $e |- A = B $.
    $( Equality inference for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
    breq1i $p |- ( A R C <-> B R C ) $=
      cA cB wceq cA cC cR wbr cB cC cR wbr wb breq1i.1 cA cB cC cR breq1 ax-mp
      $.

    $( Equality inference for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
    breq2i $p |- ( C R A <-> C R B ) $=
      cA cB wceq cC cA cR wbr cC cB cR wbr wb breq1i.1 cA cB cC cR breq2 ax-mp
      $.

    ${
      breq12i.2 $e |- C = D $.
      $( Equality inference for a binary relation.  (Contributed by NM,
         8-Feb-1996.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)
      breq12i $p |- ( A R C <-> B R D ) $=
        cA cB wceq cC cD wceq cA cC cR wbr cB cD cR wbr wb breq1i.1 breq12i.2
        cA cB cC cD cR breq12 mp2an $.
    $}
  $}

  ${
    breq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
    breq1d $p |- ( ph -> ( A R C <-> B R C ) ) $=
      wph cA cB wceq cA cC cR wbr cB cC cR wbr wb breq1d.1 cA cB cC cR breq1
      syl $.

    $( Equality deduction for a binary relation.  (Contributed by NM,
       29-Oct-2011.) $)
    breqd $p |- ( ph -> ( C A D <-> C B D ) ) $=
      wph cA cB wceq cC cD cA wbr cC cD cB wbr wb breq1d.1 cC cD cA cB breq syl
      $.

    $( Equality deduction for a binary relation.  (Contributed by NM,
       8-Feb-1996.) $)
    breq2d $p |- ( ph -> ( C R A <-> C R B ) ) $=
      wph cA cB wceq cC cA cR wbr cC cB cR wbr wb breq1d.1 cA cB cC cR breq2
      syl $.

    ${
      breq12d.2 $e |- ( ph -> C = D ) $.
      $( Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
      breq12d $p |- ( ph -> ( A R C <-> B R D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cR wbr cB cD cR wbr wb breq1d.1
        breq12d.2 cA cB cC cD cR breq12 syl2anc $.
    $}

    ${
      breq123d.2 $e |- ( ph -> R = S ) $.
      breq123d.3 $e |- ( ph -> C = D ) $.
      $( Equality deduction for a binary relation.  (Contributed by NM,
         29-Oct-2011.) $)
      breq123d $p |- ( ph -> ( A R C <-> B S D ) ) $=
        wph cA cC cR wbr cB cD cR wbr cB cD cS wbr wph cA cB cC cD cR breq1d.1
        breq123d.3 breq12d wph cR cS cB cD breq123d.2 breqd bitrd $.
    $}

    ${
      breqan12i.2 $e |- ( ps -> C = D ) $.
      $( Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.) $)
      breqan12d $p |- ( ( ph /\ ps ) -> ( A R C <-> B R D ) ) $=
        wph cA cB wceq cC cD wceq cA cC cR wbr cB cD cR wbr wb wps breq1d.1
        breqan12i.2 cA cB cC cD cR breq12 syl2an $.

      $( Equality deduction for a binary relation.  (Contributed by NM,
         8-Feb-1996.) $)
      breqan12rd $p |- ( ( ps /\ ph ) -> ( A R C <-> B R D ) ) $=
        wph wps cA cC cR wbr cB cD cR wbr wb wph wps cA cB cC cD cR breq1d.1
        breqan12i.2 breqan12d ancoms $.
    $}
  $}

  $( Two classes are different if they don't have the same relationship to a
     third class.  (Contributed by NM, 3-Jun-2012.) $)
  nbrne1 $p |- ( ( A R B /\ -. A R C ) -> B =/= C ) $=
    cA cB cR wbr cA cC cR wbr wn cB cC wne cA cB cR wbr cA cC cR wbr cB cC cB
    cC wceq cA cB cR wbr cA cC cR wbr cB cC cA cR breq2 biimpcd necon3bd imp $.

  $( Two classes are different if they don't have the same relationship to a
     third class.  (Contributed by NM, 3-Jun-2012.) $)
  nbrne2 $p |- ( ( A R C /\ -. B R C ) -> A =/= B ) $=
    cA cC cR wbr cB cC cR wbr wn cA cB wne cA cC cR wbr cB cC cR wbr cA cB cA
    cB wceq cA cC cR wbr cB cC cR wbr cA cB cC cR breq1 biimpcd necon3bd imp $.

  ${
    eqbrtr.1 $e |- A = B $.
    eqbrtr.2 $e |- B R C $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    eqbrtri $p |- A R C $=
      cA cC cR wbr cB cC cR wbr eqbrtr.2 cA cB cC cR eqbrtr.1 breq1i mpbir $.
  $}

  ${
    eqbrtrd.1 $e |- ( ph -> A = B ) $.
    eqbrtrd.2 $e |- ( ph -> B R C ) $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 8-Oct-1999.) $)
    eqbrtrd $p |- ( ph -> A R C ) $=
      wph cA cC cR wbr cB cC cR wbr eqbrtrd.2 wph cA cB cC cR eqbrtrd.1 breq1d
      mpbird $.
  $}

  ${
    eqbrtrr.1 $e |- A = B $.
    eqbrtrr.2 $e |- A R C $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    eqbrtrri $p |- B R C $=
      cB cA cC cR cA cB eqbrtrr.1 eqcomi eqbrtrr.2 eqbrtri $.
  $}

  ${
    eqbrtrrd.1 $e |- ( ph -> A = B ) $.
    eqbrtrrd.2 $e |- ( ph -> A R C ) $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)
    eqbrtrrd $p |- ( ph -> B R C ) $=
      wph cB cA cC cR wph cA cB eqbrtrrd.1 eqcomd eqbrtrrd.2 eqbrtrd $.
  $}

  ${
    breqtr.1 $e |- A R B $.
    breqtr.2 $e |- B = C $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    breqtri $p |- A R C $=
      cA cB cR wbr cA cC cR wbr breqtr.1 cB cC cA cR breqtr.2 breq2i mpbi $.
  $}

  ${
    breqtrd.1 $e |- ( ph -> A R B ) $.
    breqtrd.2 $e |- ( ph -> B = C ) $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)
    breqtrd $p |- ( ph -> A R C ) $=
      wph cA cB cR wbr cA cC cR wbr breqtrd.1 wph cB cC cA cR breqtrd.2 breq2d
      mpbid $.
  $}

  ${
    breqtrr.1 $e |- A R B $.
    breqtrr.2 $e |- C = B $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 5-Aug-1993.) $)
    breqtrri $p |- A R C $=
      cA cB cC cR breqtrr.1 cC cB breqtrr.2 eqcomi breqtri $.
  $}

  ${
    breqtrrd.1 $e |- ( ph -> A R B ) $.
    breqtrrd.2 $e |- ( ph -> C = B ) $.
    $( Substitution of equal classes into a binary relation.  (Contributed by
       NM, 24-Oct-1999.) $)
    breqtrrd $p |- ( ph -> A R C ) $=
      wph cA cB cC cR breqtrrd.1 wph cC cB breqtrrd.2 eqcomd breqtrd $.
  $}

  ${
    3brtr3.1 $e |- A R B $.
    3brtr3.2 $e |- A = C $.
    3brtr3.3 $e |- B = D $.
    $( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 11-Aug-1999.) $)
    3brtr3i $p |- C R D $=
      cC cB cD cR cA cC cB cR 3brtr3.2 3brtr3.1 eqbrtrri 3brtr3.3 breqtri $.
  $}

  ${
    3brtr4.1 $e |- A R B $.
    3brtr4.2 $e |- C = A $.
    3brtr4.3 $e |- D = B $.
    $( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 11-Aug-1999.) $)
    3brtr4i $p |- C R D $=
      cC cB cD cR cC cA cB cR 3brtr4.2 3brtr4.1 eqbrtri 3brtr4.3 breqtrri $.
  $}

  ${
    3brtr3d.1 $e |- ( ph -> A R B ) $.
    3brtr3d.2 $e |- ( ph -> A = C ) $.
    3brtr3d.3 $e |- ( ph -> B = D ) $.
    $( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 18-Oct-1999.) $)
    3brtr3d $p |- ( ph -> C R D ) $=
      wph cA cB cR wbr cC cD cR wbr 3brtr3d.1 wph cA cC cB cD cR 3brtr3d.2
      3brtr3d.3 breq12d mpbid $.
  $}

  ${
    3brtr4d.1 $e |- ( ph -> A R B ) $.
    3brtr4d.2 $e |- ( ph -> C = A ) $.
    3brtr4d.3 $e |- ( ph -> D = B ) $.
    $( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 21-Feb-2005.) $)
    3brtr4d $p |- ( ph -> C R D ) $=
      wph cC cD cR wbr cA cB cR wbr 3brtr4d.1 wph cC cA cD cB cR 3brtr4d.2
      3brtr4d.3 breq12d mpbird $.
  $}

  ${
    3brtr3g.1 $e |- ( ph -> A R B ) $.
    3brtr3g.2 $e |- A = C $.
    3brtr3g.3 $e |- B = D $.
    $( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 16-Jan-1997.) $)
    3brtr3g $p |- ( ph -> C R D ) $=
      wph cA cB cR wbr cC cD cR wbr 3brtr3g.1 cA cC cB cD cR 3brtr3g.2
      3brtr3g.3 breq12i sylib $.
  $}

  ${
    3brtr4g.1 $e |- ( ph -> A R B ) $.
    3brtr4g.2 $e |- C = A $.
    3brtr4g.3 $e |- D = B $.
    $( Substitution of equality into both sides of a binary relation.
       (Contributed by NM, 16-Jan-1997.) $)
    3brtr4g $p |- ( ph -> C R D ) $=
      wph cA cB cR wbr cC cD cR wbr 3brtr4g.1 cC cA cD cB cR 3brtr4g.2
      3brtr4g.3 breq12i sylibr $.
  $}

  ${
    syl5eqbr.1 $e |- A = B $.
    syl5eqbr.2 $e |- ( ph -> B R C ) $.
    $( B chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)
    syl5eqbr $p |- ( ph -> A R C ) $=
      wph cB cC cA cC cR syl5eqbr.2 syl5eqbr.1 cC eqid 3brtr4g $.
  $}

  ${
    syl5eqbrr.1 $e |- B = A $.
    syl5eqbrr.2 $e |- ( ph -> B R C ) $.
    $( B chained equality inference for a binary relation.  (Contributed by NM,
       17-Sep-2004.) $)
    syl5eqbrr $p |- ( ph -> A R C ) $=
      wph cB cC cA cC cR syl5eqbrr.2 syl5eqbrr.1 cC eqid 3brtr3g $.
  $}

  ${
    syl5breq.1 $e |- A R B $.
    syl5breq.2 $e |- ( ph -> B = C ) $.
    $( B chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)
    syl5breq $p |- ( ph -> A R C ) $=
      wph cA cB cC cR cA cB cR wbr wph syl5breq.1 a1i syl5breq.2 breqtrd $.
  $}

  ${
    syl5breqr.1 $e |- A R B $.
    syl5breqr.2 $e |- ( ph -> C = B ) $.
    $( B chained equality inference for a binary relation.  (Contributed by NM,
       24-Apr-2005.) $)
    syl5breqr $p |- ( ph -> A R C ) $=
      wph cA cB cC cR syl5breqr.1 wph cC cB syl5breqr.2 eqcomd syl5breq $.
  $}

  ${
    syl6eqbr.1 $e |- ( ph -> A = B ) $.
    syl6eqbr.2 $e |- B R C $.
    $( A chained equality inference for a binary relation.  (Contributed by NM,
       12-Oct-1999.) $)
    syl6eqbr $p |- ( ph -> A R C ) $=
      wph cA cC cR wbr cB cC cR wbr syl6eqbr.2 wph cA cB cC cR syl6eqbr.1
      breq1d mpbiri $.
  $}

  ${
    syl6eqbrr.1 $e |- ( ph -> B = A ) $.
    syl6eqbrr.2 $e |- B R C $.
    $( A chained equality inference for a binary relation.  (Contributed by NM,
       4-Jan-2006.) $)
    syl6eqbrr $p |- ( ph -> A R C ) $=
      wph cA cB cC cR wph cB cA syl6eqbrr.1 eqcomd syl6eqbrr.2 syl6eqbr $.
  $}

  ${
    syl6breq.1 $e |- ( ph -> A R B ) $.
    syl6breq.2 $e |- B = C $.
    $( A chained equality inference for a binary relation.  (Contributed by NM,
       11-Oct-1999.) $)
    syl6breq $p |- ( ph -> A R C ) $=
      wph cA cB cA cC cR syl6breq.1 cA eqid syl6breq.2 3brtr3g $.
  $}

  ${
    syl6breqr.1 $e |- ( ph -> A R B ) $.
    syl6breqr.2 $e |- C = B $.
    $( A chained equality inference for a binary relation.  (Contributed by NM,
       24-Apr-2005.) $)
    syl6breqr $p |- ( ph -> A R C ) $=
      wph cA cB cC cR syl6breqr.1 cC cB syl6breqr.2 eqcomi syl6breq $.
  $}


  ${
    ssbrd.1 $e |- ( ph -> A C_ B ) $.
    $( Deduction from a subclass relationship of binary relations.
       (Contributed by NM, 30-Apr-2004.) $)
    ssbrd $p |- ( ph -> ( C A D -> C B D ) ) $=
      wph cC cD cop cA wcel cC cD cop cB wcel cC cD cA wbr cC cD cB wbr wph cA
      cB cC cD cop ssbrd.1 sseld cC cD cA df-br cC cD cB df-br 3imtr4g $.
  $}

  ${
    ssbri.1 $e |- A C_ B $.
    $( Inference from a subclass relationship of binary relations.
       (Contributed by NM, 28-Mar-2007.)  (Revised by Mario Carneiro,
       8-Feb-2015.) $)
    ssbri $p |- ( C A D -> C B D ) $=
      cC cD cA wbr cC cD cB wbr wi wtru cA cB cC cD cA cB wss wtru ssbri.1 a1i
      ssbrd trud $.
  $}

  ${
    $d y z A $.  $d y z B $.  $d y z R $.  $d x y z $.  $d y ph $.
    nfbrd.2 $e |- ( ph -> F/_ x A ) $.
    nfbrd.3 $e |- ( ph -> F/_ x R ) $.
    nfbrd.4 $e |- ( ph -> F/_ x B ) $.
    $( Deduction version of bound-variable hypothesis builder ~ nfbr .
       (Contributed by NM, 13-Dec-2005.)  (Revised by Mario Carneiro,
       14-Oct-2016.) $)
    nfbrd $p |- ( ph -> F/ x A R B ) $=
      cA cB cR wbr cA cB cop cR wcel wph vx cA cB cR df-br wph vx cA cB cop cR
      wph vx cA cB nfbrd.2 nfbrd.4 nfopd nfbrd.3 nfeld nfxfrd $.
  $}

  ${
    $d y A $.  $d y B $.  $d y R $.  $d x y $.
    nfbr.1 $e |- F/_ x A $.
    nfbr.2 $e |- F/_ x R $.
    nfbr.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for binary relation.  (Contributed by
       NM, 1-Sep-1999.)  (Revised by Mario Carneiro, 14-Oct-2016.) $)
    nfbr $p |- F/ x A R B $=
      cA cB cR wbr vx wnf wtru vx cA cB cR vx cA wnfc wtru nfbr.1 a1i vx cR
      wnfc wtru nfbr.2 a1i vx cB wnfc wtru nfbr.3 a1i nfbrd trud $.
  $}

  ${
    $d x y $.  $d y z A $.  $d y z R $.
    $( Relationship between a binary relation and a class abstraction.
       (Contributed by Andrew Salmon, 8-Jul-2011.) $)
    brab1 $p |- ( x R A <-> x e. { z | z R A } ) $=
      vx cv cA cR wbr vz cv cA cR wbr vz vx cv wsbc vx cv vz cv cA cR wbr vz
      cab wcel vx cv cvv wcel vz cv cA cR wbr vz vx cv wsbc vx cv cA cR wbr wb
      vx vex vz cv cA cR wbr vy cv cA cR wbr vx cv cA cR wbr vz vy vx cv cvv vz
      cv vy cv cA cR breq1 vy cv vx cv cA cR breq1 sbcie2g ax-mp vz cv cA cR
      wbr vz vx cv df-sbc bitr3i $.
  $}

  $( The union of two binary relations.  (Contributed by NM, 21-Dec-2008.) $)
  brun $p |- ( A ( R u. S ) B <-> ( A R B \/ A S B ) ) $=
    cA cB cop cR cS cun wcel cA cB cop cR wcel cA cB cop cS wcel wo cA cB cR cS
    cun wbr cA cB cR wbr cA cB cS wbr wo cA cB cop cR cS elun cA cB cR cS cun
    df-br cA cB cR wbr cA cB cop cR wcel cA cB cS wbr cA cB cop cS wcel cA cB
    cR df-br cA cB cS df-br orbi12i 3bitr4i $.

  $( The intersection of two relations.  (Contributed by FL, 7-Oct-2008.) $)
  brin $p |- ( A ( R i^i S ) B <-> ( A R B /\ A S B ) ) $=
    cA cB cop cR cS cin wcel cA cB cop cR wcel cA cB cop cS wcel wa cA cB cR cS
    cin wbr cA cB cR wbr cA cB cS wbr wa cA cB cop cR cS elin cA cB cR cS cin
    df-br cA cB cR wbr cA cB cop cR wcel cA cB cS wbr cA cB cop cS wcel cA cB
    cR df-br cA cB cS df-br anbi12i 3bitr4i $.

  $( The difference of two binary relations.  (Contributed by Scott Fenton,
     11-Apr-2011.) $)
  brdif $p |- ( A ( R \ S ) B <-> ( A R B /\ -. A S B ) ) $=
    cA cB cop cR cS cdif wcel cA cB cop cR wcel cA cB cop cS wcel wn wa cA cB
    cR cS cdif wbr cA cB cR wbr cA cB cS wbr wn wa cA cB cop cR cS eldif cA cB
    cR cS cdif df-br cA cB cR wbr cA cB cop cR wcel cA cB cS wbr wn cA cB cop
    cS wcel wn cA cB cR df-br cA cB cS wbr cA cB cop cS wcel cA cB cS df-br
    notbii anbi12i 3bitr4i $.

  ${
    $d y z A $.  $d y z B $.  $d y z C $.  $d y z D $.  $d y z R $.
    $d x y z $.
    $( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.)  (Proof shortened by Andrew Salmon, 9-Jul-2011.) $)
    sbcbrg $p |- ( A e. D -> ( [. A / x ]. B R C <->
           [_ A / x ]_ B [_ A / x ]_ R [_ A / x ]_ C ) ) $=
      cB cC cR wbr vx vy wsb vx vy cv cB csb vx vy cv cC csb vx vy cv cR csb
      wbr cB cC cR wbr vx cA wsbc vx cA cB csb vx cA cC csb vx cA cR csb wbr vy
      cA cD cB cC cR wbr vx vy cA dfsbcq2 vy cv cA wceq vx vy cv cB csb vx cA
      cB csb vx vy cv cC csb vx cA cC csb vx vy cv cR csb vx cA cR csb vx vy cv
      cA cB csbeq1 vx vy cv cA cR csbeq1 vx vy cv cA cC csbeq1 breq123d cB cC
      cR wbr vx vy cv cB csb vx vy cv cC csb vx vy cv cR csb wbr vx vy vx vx vy
      cv cB csb vx vy cv cC csb vx vy cv cR csb vx vy cv cB nfcsb1v vx vy cv cR
      nfcsb1v vx vy cv cC nfcsb1v nfbr vx vy weq cB vx vy cv cB csb cC vx vy cv
      cC csb cR vx vy cv cR csb vx vy cv cB csbeq1a vx vy cv cR csbeq1a vx vy
      cv cC csbeq1a breq123d sbie vtoclbg $.
  $}

  ${
    $d y A $.  $d y C $.  $d y D $.  $d x y R $.
    $( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)
    sbcbr12g $p |- ( A e. D ->
                 ( [. A / x ]. B R C <-> [_ A / x ]_ B R [_ A / x ]_ C ) ) $=
      cA cD wcel cB cC cR wbr vx cA wsbc vx cA cB csb vx cA cC csb vx cA cR csb
      wbr vx cA cB csb vx cA cC csb cR wbr vx cA cB cC cD cR sbcbrg cA cD wcel
      vx cA cR csb cR vx cA cB csb vx cA cC csb vx cA cR cD csbconstg breqd
      bitrd $.
  $}

  ${
    $d y A $.  $d x y C $.  $d y D $.  $d x y R $.
    $( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)
    sbcbr1g $p |- ( A e. D ->
                  ( [. A / x ]. B R C <-> [_ A / x ]_ B R C ) ) $=
      cA cD wcel cB cC cR wbr vx cA wsbc vx cA cB csb vx cA cC csb cR wbr vx cA
      cB csb cC cR wbr vx cA cB cC cD cR sbcbr12g cA cD wcel vx cA cC csb cC vx
      cA cB csb cR vx cA cC cD csbconstg breq2d bitrd $.
  $}

  ${
    $d y A $.  $d x y B $.  $d y D $.  $d x y R $.
    $( Move substitution in and out of a binary relation.  (Contributed by NM,
       13-Dec-2005.) $)
    sbcbr2g $p |- ( A e. D ->
                  ( [. A / x ]. B R C <-> B R [_ A / x ]_ C ) ) $=
      cA cD wcel cB cC cR wbr vx cA wsbc vx cA cB csb vx cA cC csb cR wbr cB vx
      cA cC csb cR wbr vx cA cB cC cD cR sbcbr12g cA cD wcel vx cA cB csb cB vx
      cA cC csb cR vx cA cB cD csbconstg breq1d bitrd $.
  $}


