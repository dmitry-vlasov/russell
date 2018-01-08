
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Power_classes.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Unordered and ordered pairs

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols needed. $)
  $c <. $.  $( Bracket (the period distinguishes it from 'less than') $)
  $c >. $.  $( Bracket (the period distinguishes it from 'greater than') $)

  $( Extend class notation to include singleton. $)
  csn $a class { A } $.
  $( Extend class notation to include unordered pair. $)
  cpr $a class { A , B } $.
  $( Extend class notation to include unordered triplet. $)
  ctp $a class { A , B , C } $.
  $( Extend class notation to include ordered pair. $)
  cop $a class <. A , B >. $.
  $( Extend class notation to include ordered triple. $)
  cotp $a class <. A , B , C >. $.

  ${
    $d x A $.  $d y A $.  $d z x $.  $d z y $.  $d z A $.
    $( Soundness justification theorem for ~ df-sn .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    snjust $p |- { x | x = A } = { y | y = A } $=
      vx cv cA wceq vx cab vz cv cA wceq vz cab vy cv cA wceq vy cab vx cv cA
      wceq vz cv cA wceq vx vz vx cv vz cv cA eqeq1 cbvabv vz cv cA wceq vy cv
      cA wceq vz vy vz cv vy cv cA eqeq1 cbvabv eqtri $.
  $}

  ${
    $d x A $.
    $( Define the singleton of a class.  Definition 7.1 of [Quine] p. 48.  For
       convenience, it is well-defined for proper classes, i.e., those that are
       not elements of ` _V ` , although it is not very meaningful in this
       case.  For an alternate definition see ~ dfsn2 .  (Contributed by NM,
       5-Aug-1993.) $)
    df-sn $a |- { A } = { x | x = A } $.
  $}

  $( Define unordered pair of classes.  Definition 7.1 of [Quine] p. 48.  For
     example, ` A e. { 1 , -u 1 } -> ( A ^ 2 ) = 1 ` ( ~ ex-pr ).  They are
     unordered, so ` { A , B } = { B , A } ` as proven by ~ prcom .  For a more
     traditional definition, but requiring a dummy variable, see ~ dfpr2 .
     (Contributed by NM, 5-Aug-1993.) $)
  df-pr $a |- { A , B } = ( { A } u. { B } ) $.

  $( Define unordered triple of classes.  Definition of [Enderton] p. 19.
     (Contributed by NM, 9-Apr-1994.) $)
  df-tp $a |- { A , B , C } = ( { A , B } u. { C } ) $.

  ${
    $d x A $.  $d x B $.
    $( Definition of an ordered pair, equivalent to Kuratowski's definition
       ` { { A } , { A , B } } ` when the arguments are sets.  Since the
       behavior of Kuratowski definition is not very useful for proper classes,
       we define it to be empty in this case (see ~ opprc1 , ~ opprc2 , and
       ~ 0nelop ).  For Kuratowski's actual definition when the arguments are
       sets, see ~ dfop .  For the justifying theorem (for sets) see ~ opth .
       See ~ dfopif for an equivalent formulation using the ` if ` operation.

       Definition 9.1 of [Quine] p. 58 defines an ordered pair unconditionally
       as ` <. A , B >. = { { A } , { A , B } } ` , which has different
       behavior from our ~ df-op when the arguments are proper classes.
       Ordinarily this difference is not important, since neither definition is
       meaningful in that case.  Our ~ df-op was chosen because it often makes
       proofs shorter by eliminating unnecessary sethood hypotheses.

       There are other ways to define ordered pairs.  The basic requirement is
       that two ordered pairs are equal iff their respective members are
       equal.  In 1914 Norbert Wiener gave the first successful definition
       ` <. A , B >. ` _2 ` = { { { A } , (/) } , { { B } } } ` , justified by
       ~ opthwiener .  This was simplified by Kazimierz Kuratowski in 1921 to
       our present definition.  An even simpler definition ` <. A , B >. ` _3
       ` = { A , { A , B } } ` is justified by ~ opthreg , but it requires the
       Axiom of Regularity for its justification and is not commonly used.  A
       definition that also works for proper classes is ` <. A , B >. ` _4
       ` = ( ( A X. { (/) } ) u. ( B X. { { (/) } } ) ) ` , justified by
       ~ opthprc .  If we restrict our sets to nonnegative integers, an ordered
       pair definition that involves only elementary arithmetic is provided by
       ~ nn0opthi .  Finally, an ordered pair of real numbers can be
       represented by a complex number as shown by ~ cru .  (Contributed by NM,
       28-May-1995.)  (Revised by Mario Carneiro, 26-Apr-2015.) $)
    df-op $a |- <. A , B >. = { x |
      ( A e. _V /\ B e. _V /\ x e. { { A } , { A , B } } ) } $.
  $}

  $( Define ordered triple of classes.  Definition of ordered triple in [Stoll]
     p. 25.  (Contributed by NM, 3-Apr-2015.) $)
  df-ot $a |- <. A , B , C >. = <. <. A , B >. , C >. $.

  ${
    $d x A $.  $d x B $.
    $( Equality theorem for singletons.  Part of Exercise 4 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 5-Aug-1993.) $)
    sneq $p |- ( A = B -> { A } = { B } ) $=
      cA cB wceq vx cv cA wceq vx cab vx cv cB wceq vx cab cA csn cB csn cA cB
      wceq vx cv cA wceq vx cv cB wceq vx cA cB vx cv eqeq2 abbidv vx cA df-sn
      vx cB df-sn 3eqtr4g $.
  $}

  ${
    sneqi.1 $e |- A = B $.
    $( Equality inference for singletons.  (Contributed by NM, 22-Jan-2004.) $)
    sneqi $p |- { A } = { B } $=
      cA cB wceq cA csn cB csn wceq sneqi.1 cA cB sneq ax-mp $.
  $}

  ${
    sneqd.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for singletons.  (Contributed by NM, 22-Jan-2004.) $)
    sneqd $p |- ( ph -> { A } = { B } ) $=
      wph cA cB wceq cA csn cB csn wceq sneqd.1 cA cB sneq syl $.
  $}

  $( Alternate definition of singleton.  Definition 5.1 of [TakeutiZaring]
     p. 15.  (Contributed by NM, 24-Apr-1994.) $)
  dfsn2 $p |- { A } = { A , A } $=
    cA cA cpr cA csn cA csn cun cA csn cA cA df-pr cA csn unidm eqtr2i $.

  ${
    $d x A $.
    $( There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 5-Aug-1993.) $)
    elsn $p |- ( x e. { A } <-> x = A ) $=
      vx cv cA wceq vx cA csn vx cA df-sn abeq2i $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Alternate definition of unordered pair.  Definition 5.1 of
       [TakeutiZaring] p. 15.  (Contributed by NM, 24-Apr-1994.) $)
    dfpr2 $p |- { A , B } = { x | ( x = A \/ x = B ) } $=
      cA cB cpr cA csn cB csn cun vx cv cA wceq vx cv cB wceq wo vx cab cA cB
      df-pr vx cv cA wceq vx cv cB wceq wo vx cA csn cB csn cun vx cv cA csn cB
      csn cun wcel vx cv cA csn wcel vx cv cB csn wcel wo vx cv cA wceq vx cv
      cB wceq wo vx cv cA csn cB csn elun vx cv cA csn wcel vx cv cA wceq vx cv
      cB csn wcel vx cv cB wceq vx cA elsn vx cB elsn orbi12i bitri abbi2i
      eqtri $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15, generalized.  (Contributed by NM,
       13-Sep-1995.) $)
    elprg $p |- ( A e. V -> ( A e. { B , C } <-> ( A = B \/ A = C ) ) ) $=
      vx cv cB wceq vx cv cC wceq wo cA cB wceq cA cC wceq wo vx cA cB cC cpr
      cV vx cv cA wceq vx cv cB wceq cA cB wceq vx cv cC wceq cA cC wceq vx cv
      cA cB eqeq1 vx cv cA cC eqeq1 orbi12d vx cB cC dfpr2 elab2g $.
  $}

  ${
    elpr.1 $e |- A e. _V $.
    $( A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15.  (Contributed by NM,
       13-Sep-1995.) $)
    elpr $p |- ( A e. { B , C } <-> ( A = B \/ A = C ) ) $=
      cA cvv wcel cA cB cC cpr wcel cA cB wceq cA cC wceq wo wb elpr.1 cA cB cC
      cvv elprg ax-mp $.
  $}

  ${
    elpr2.1 $e |- B e. _V $.
    elpr2.2 $e |- C e. _V $.
    $( A member of an unordered pair of classes is one or the other of them.
       Exercise 1 of [TakeutiZaring] p. 15.  (Contributed by NM,
       14-Oct-2005.) $)
    elpr2 $p |- ( A e. { B , C } <-> ( A = B \/ A = C ) ) $=
      cA cB cC cpr wcel cA cB wceq cA cC wceq wo cA cB cC cpr wcel cA cB wceq
      cA cC wceq wo cA cB cC cB cC cpr elprg ibi cA cB wceq cA cC wceq wo cA cB
      cC cpr wcel cA cB wceq cA cC wceq wo cA cvv wcel cA cB cC cpr wcel cA cB
      wceq cA cC wceq wo wb cA cB wceq cA cvv wcel cA cC wceq cA cB wceq cA cvv
      wcel cB cvv wcel elpr2.1 cA cB cvv eleq1 mpbiri cA cC wceq cA cvv wcel cC
      cvv wcel elpr2.2 cA cC cvv eleq1 mpbiri jaoi cA cB cC cvv elprg syl ibir
      impbii $.
  $}

  $( If a class is an element of a pair, then it is one of the two paired
     elements.  (Contributed by Scott Fenton, 1-Apr-2011.) $)
  elpri $p |- ( A e. { B , C } -> ( A = B \/ A = C ) ) $=
    cA cB cC cpr wcel cA cB wceq cA cC wceq wo cA cB cC cB cC cpr elprg ibi $.

  ${
    nelpri.1 $e |- A =/= B $.
    nelpri.2 $e |- A =/= C $.
    $( If an element doesn't match the items in an unordered pair, it is not in
       the unordered pair.  (Contributed by David A. Wheeler, 10-May-2015.) $)
    nelpri $p |- -. A e. { B , C } $=
      cA cB wne cA cC wne cA cB cC cpr wcel wn nelpri.1 nelpri.2 cA cB wne cA
      cC wne wa cA cB wceq cA cC wceq wo wn cA cB cC cpr wcel wn cA cB cA cC
      neanior cA cB cC cpr wcel cA cB wceq cA cC wceq wo cA cB cC elpri con3i
      sylbi mp2an $.
  $}

  ${
    $d A x $.  $d B x $.
    $( There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15 (generalized).  (Contributed by NM, 13-Sep-1995.)  (Proof
       shortened by Andrew Salmon, 29-Jun-2011.) $)
    elsncg $p |- ( A e. V -> ( A e. { B } <-> A = B ) ) $=
      vx cv cB wceq cA cB wceq vx cA cB csn cV vx cv cA cB eqeq1 vx cB df-sn
      elab2g $.
  $}

  ${
    elsnc.1 $e |- A e. _V $.
    $( There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  (Contributed by NM, 13-Sep-1995.) $)
    elsnc $p |- ( A e. { B } <-> A = B ) $=
      cA cvv wcel cA cB csn wcel cA cB wceq wb elsnc.1 cA cB cvv elsncg ax-mp
      $.
  $}

  $( There is only one element in a singleton.  (Contributed by NM,
     5-Jun-1994.) $)
  elsni $p |- ( A e. { B } -> A = B ) $=
    cA cB csn wcel cA cB wceq cA cB cB csn elsncg ibi $.

  $( A set is a member of its singleton.  Part of Theorem 7.6 of [Quine]
     p. 49.  (Contributed by NM, 28-Oct-2003.) $)
  snidg $p |- ( A e. V -> A e. { A } ) $=
    cA cV wcel cA cA csn wcel cA cA wceq cA eqid cA cA cV elsncg mpbiri $.

  $( A class is a set iff it is a member of its singleton.  (Contributed by NM,
     5-Apr-2004.) $)
  snidb $p |- ( A e. _V <-> A e. { A } ) $=
    cA cvv wcel cA cA csn wcel cA cvv snidg cA cA csn elex impbii $.

  ${
    snid.1 $e |- A e. _V $.
    $( A set is a member of its singleton.  Part of Theorem 7.6 of [Quine]
       p. 49.  (Contributed by NM, 31-Dec-1993.) $)
    snid $p |- A e. { A } $=
      cA cvv wcel cA cA csn wcel snid.1 cA snidb mpbi $.
  $}

  $( There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
     p. 15.  This variation requires only that ` B ` , rather than ` A ` , be a
     set.  (Contributed by NM, 28-Oct-2003.) $)
  elsnc2g $p |- ( B e. V -> ( A e. { B } <-> A = B ) ) $=
    cB cV wcel cA cB csn wcel cA cB wceq cA cB elsni cB cV wcel cA cB csn wcel
    cA cB wceq cB cB csn wcel cB cV snidg cA cB cB csn eleq1 syl5ibrcom impbid2
    $.

  ${
    elsnc2.1 $e |- B e. _V $.
    $( There is only one element in a singleton.  Exercise 2 of [TakeutiZaring]
       p. 15.  This variation requires only that ` B ` , rather than ` A ` , be
       a set.  (Contributed by NM, 12-Jun-1994.) $)
    elsnc2 $p |- ( A e. { B } <-> A = B ) $=
      cB cvv wcel cA cB csn wcel cA cB wceq wb elsnc2.1 cA cB cvv elsnc2g ax-mp
      $.
  $}

  ${
    $d A x $.  $d ps x $.
    $( Substitution expressed in terms of quantification over a singleton.
       (Contributed by Mario Carneiro, 23-Apr-2015.) $)
    ralsns $p |- ( A e. V -> ( A. x e. { A } ph <-> [. A / x ]. ph ) ) $=
      cA cV wcel wph vx cA wsbc vx cv cA wceq wph wi vx wal wph vx cA csn wral
      wph vx cA cV sbc6g wph vx cA csn wral vx cv cA csn wcel wph wi vx wal vx
      cv cA wceq wph wi vx wal wph vx cA csn df-ral vx cv cA csn wcel wph wi vx
      cv cA wceq wph wi vx vx cv cA csn wcel vx cv cA wceq wph vx cA elsn
      imbi1i albii bitri syl6rbbr $.

    $( Restricted existential quantification over a singleton.  (Contributed by
       Mario Carneiro, 23-Apr-2015.) $)
    rexsns $p |- ( A e. V -> ( E. x e. { A } ph <-> [. A / x ]. ph ) ) $=
      cA cV wcel wph vx cA wsbc vx cv cA wceq wph wa vx wex wph vx cA csn wrex
      wph vx cA wsbc vx cv cA wceq wph wa vx wex wb cA cV wcel wph vx cA sbc5
      a1i wph vx cA csn wrex vx cv cA csn wcel wph wa vx wex vx cv cA wceq wph
      wa vx wex wph vx cA csn df-rex vx cv cA csn wcel wph wa vx cv cA wceq wph
      wa vx vx cv cA csn wcel vx cv cA wceq wph vx cA elsn anbi1i exbii bitri
      syl6rbbr $.

    ralsng.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Substitution expressed in terms of quantification over a singleton.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       23-Apr-2015.) $)
    ralsng $p |- ( A e. V -> ( A. x e. { A } ph <-> ps ) ) $=
      cA cV wcel wph vx cA csn wral wph vx cA wsbc wps wph vx cA cV ralsns wph
      wps vx cA cV ralsng.1 sbcieg bitrd $.

    $( Restricted existential quantification over a singleton.  (Contributed by
       NM, 29-Jan-2012.) $)
    rexsng $p |- ( A e. V -> ( E. x e. { A } ph <-> ps ) ) $=
      cA cV wcel wph vx cA csn wrex wph vx cA wsbc wps wph vx cA cV rexsns wph
      wps vx cA cV ralsng.1 sbcieg bitrd $.
  $}

  ${
    $d A x $.  $d ps x $.
    ralsn.1 $e |- A e. _V $.
    ralsn.2 $e |- ( x = A -> ( ph <-> ps ) ) $.
    $( Convert a quantification over a singleton to a substitution.
       (Contributed by NM, 27-Apr-2009.) $)
    ralsn $p |- ( A. x e. { A } ph <-> ps ) $=
      cA cvv wcel wph vx cA csn wral wps wb ralsn.1 wph wps vx cA cvv ralsn.2
      ralsng ax-mp $.

    $( Restricted existential quantification over a singleton.  (Contributed by
       Jeff Madsen, 5-Jan-2011.) $)
    rexsn $p |- ( E. x e. { A } ph <-> ps ) $=
      cA cvv wcel wph vx cA csn wrex wps wb ralsn.1 wph wps vx cA cvv ralsn.2
      rexsng ax-mp $.
  $}

  ${
    $( Members of an unordered triple of classes.  (Contributed by FL,
       2-Feb-2014.)  (Proof shortened by Mario Carneiro, 11-Feb-2015.) $)
    eltpg $p |- ( A e. V -> ( A e. { B , C , D } <->
       ( A = B \/ A = C \/ A = D ) ) ) $=
      cA cV wcel cA cB cC cpr wcel cA cD csn wcel wo cA cB wceq cA cC wceq wo
      cA cD wceq wo cA cB cC cD ctp wcel cA cB wceq cA cC wceq cA cD wceq w3o
      cA cV wcel cA cB cC cpr wcel cA cB wceq cA cC wceq wo cA cD csn wcel cA
      cD wceq cA cB cC cV elprg cA cD cV elsncg orbi12d cA cB cC cD ctp wcel cA
      cB cC cpr cD csn cun wcel cA cB cC cpr wcel cA cD csn wcel wo cB cC cD
      ctp cB cC cpr cD csn cun cA cB cC cD df-tp eleq2i cA cB cC cpr cD csn
      elun bitri cA cB wceq cA cC wceq cA cD wceq df-3or 3bitr4g $.
  $}

  ${
    $( A member of an unordered triple of classes is one of them.  (Contributed
       by Mario Carneiro, 11-Feb-2015.) $)
    eltpi $p |- ( A e. { B , C , D } -> ( A = B \/ A = C \/ A = D ) ) $=
      cA cB cC cD ctp wcel cA cB wceq cA cC wceq cA cD wceq w3o cA cB cC cD cB
      cC cD ctp eltpg ibi $.
  $}

  ${
    eltp.1 $e |- A e. _V $.
    $( A member of an unordered triple of classes is one of them.  Special case
       of Exercise 1 of [TakeutiZaring] p. 17.  (Contributed by NM,
       8-Apr-1994.)  (Revised by Mario Carneiro, 11-Feb-2015.) $)
    eltp $p |- ( A e. { B , C , D } <-> ( A = B \/ A = C \/ A = D ) ) $=
      cA cvv wcel cA cB cC cD ctp wcel cA cB wceq cA cC wceq cA cD wceq w3o wb
      eltp.1 cA cB cC cD cvv eltpg ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Alternate definition of unordered triple of classes.  Special case of
       Definition 5.3 of [TakeutiZaring] p. 16.  (Contributed by NM,
       8-Apr-1994.) $)
    dftp2 $p |- { A , B , C } = { x | ( x = A \/ x = B \/ x = C ) } $=
      vx cv cA wceq vx cv cB wceq vx cv cC wceq w3o vx cA cB cC ctp vx cv cA cB
      cC vx vex eltp abbi2i $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y $.
    nfpr.1 $e |- F/_ x A $.
    nfpr.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for unordered pairs.  (Contributed by
       NM, 14-Nov-1995.) $)
    nfpr $p |- F/_ x { A , B } $=
      vx cA cB cpr vy cv cA wceq vy cv cB wceq wo vy cab vy cA cB dfpr2 vy cv
      cA wceq vy cv cB wceq wo vx vy vy cv cA wceq vy cv cB wceq vx vx vy cv cA
      nfpr.1 nfeq2 vx vy cv cB nfpr.2 nfeq2 nfor nfab nfcxfr $.
  $}

  $( Membership of a conditional operator in an unordered pair.  (Contributed
     by NM, 17-Jun-2007.) $)
  ifpr $p |- ( ( A e. C /\ B e. D ) -> if ( ph , A , B ) e. { A , B } ) $=
    cA cC wcel cA cvv wcel cB cvv wcel wph cA cB cif cA cB cpr wcel cB cD wcel
    cA cC elex cB cD elex cA cvv wcel cB cvv wcel wa wph cA cB cif cvv wcel wph
    cA cB cif cA cB cpr wcel wph cA cB cvv ifcl wph cA cB cif cvv wcel wph cA
    cB cif cA cB cpr wcel wph cA cB cif cA wceq wph cA cB cif cB wceq wo wph cA
    cB ifeqor wph cA cB cif cA cB cvv elprg mpbiri syl syl2an $.

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x ps $.  $d x ch $.  $d x th $.
    ralprg.1 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ralprg.2 $e |- ( x = B -> ( ph <-> ch ) ) $.
    $( Convert a quantification over a pair to a conjunction.  (Contributed by
       NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    ralprg $p |- ( ( A e. V /\ B e. W ) ->
      ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) ) $=
      wph vx cA cB cpr wral wph vx cA csn wral wph vx cB csn wral wa cA cV wcel
      cB cW wcel wa wps wch wa wph vx cA cB cpr wral wph vx cA csn cB csn cun
      wral wph vx cA csn wral wph vx cB csn wral wa wph vx cA cB cpr cA csn cB
      csn cun cA cB df-pr raleqi wph vx cA csn cB csn ralunb bitri cA cV wcel
      wph vx cA csn wral wps cB cW wcel wph vx cB csn wral wch wph wps vx cA cV
      ralprg.1 ralsng wph wch vx cB cW ralprg.2 ralsng bi2anan9 syl5bb $.

    $( Convert a quantification over a pair to a disjunction.  (Contributed by
       NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    rexprg $p |- ( ( A e. V /\ B e. W ) ->
      ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) ) $=
      wph vx cA cB cpr wrex wph vx cA csn wrex wph vx cB csn wrex wo cA cV wcel
      cB cW wcel wa wps wch wo wph vx cA cB cpr wrex wph vx cA csn cB csn cun
      wrex wph vx cA csn wrex wph vx cB csn wrex wo wph vx cA cB cpr cA csn cB
      csn cun cA cB df-pr rexeqi wph vx cA csn cB csn rexun bitri cA cV wcel
      wph vx cA csn wrex wph vx cB csn wrex wo wps wph vx cB csn wrex wo cB cW
      wcel wps wch wo cA cV wcel wph vx cA csn wrex wps wph vx cB csn wrex wph
      wps vx cA cV ralprg.1 rexsng orbi1d cB cW wcel wph vx cB csn wrex wch wps
      wph wch vx cB cW ralprg.2 rexsng orbi2d sylan9bb syl5bb $.

    raltpg.3 $e |- ( x = C -> ( ph <-> th ) ) $.
    $( Convert a quantification over a triple to a conjunction.  (Contributed
       by NM, 17-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    raltpg $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
      ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) ) $=
      cA cV wcel cB cW wcel cC cX wcel w3a wph vx cA cB cpr wral wph vx cC csn
      wral wa wps wch wa wth wa wph vx cA cB cC ctp wral wps wch wth w3a cA cV
      wcel cB cW wcel cC cX wcel wph vx cA cB cpr wral wph vx cC csn wral wa
      wps wch wa wth wa wb cA cV wcel cB cW wcel wa wph vx cA cB cpr wral wps
      wch wa cC cX wcel wph vx cC csn wral wth wph wps wch vx cA cB cV cW
      ralprg.1 ralprg.2 ralprg wph wth vx cC cX raltpg.3 ralsng bi2anan9 3impa
      wph vx cA cB cC ctp wral wph vx cA cB cpr cC csn cun wral wph vx cA cB
      cpr wral wph vx cC csn wral wa wph vx cA cB cC ctp cA cB cpr cC csn cun
      cA cB cC df-tp raleqi wph vx cA cB cpr cC csn ralunb bitri wps wch wth
      df-3an 3bitr4g $.

    $( Convert a quantification over a triple to a disjunction.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)
    rextpg $p |- ( ( A e. V /\ B e. W /\ C e. X ) ->
      ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) ) $=
      cA cV wcel cB cW wcel cC cX wcel w3a wph vx cA cB cpr wrex wph vx cC csn
      wrex wo wps wch wo wth wo wph vx cA cB cC ctp wrex wps wch wth w3o cA cV
      wcel cB cW wcel cC cX wcel wph vx cA cB cpr wrex wph vx cC csn wrex wo
      wps wch wo wth wo wb cA cV wcel cB cW wcel wa wph vx cA cB cpr wrex wph
      vx cC csn wrex wo wps wch wo wph vx cC csn wrex wo cC cX wcel wps wch wo
      wth wo cA cV wcel cB cW wcel wa wph vx cA cB cpr wrex wps wch wo wph vx
      cC csn wrex wph wps wch vx cA cB cV cW ralprg.1 ralprg.2 rexprg orbi1d cC
      cX wcel wph vx cC csn wrex wth wps wch wo wph wth vx cC cX raltpg.3
      rexsng orbi2d sylan9bb 3impa wph vx cA cB cC ctp wrex wph vx cA cB cpr cC
      csn cun wrex wph vx cA cB cpr wrex wph vx cC csn wrex wo wph vx cA cB cC
      ctp cA cB cpr cC csn cun cA cB cC df-tp rexeqi wph vx cA cB cpr cC csn
      rexun bitri wps wch wth df-3or 3bitr4g $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.  $d x ch $.
    ralpr.1 $e |- A e. _V $.
    ralpr.2 $e |- B e. _V $.
    ralpr.3 $e |- ( x = A -> ( ph <-> ps ) ) $.
    ralpr.4 $e |- ( x = B -> ( ph <-> ch ) ) $.
    $( Convert a quantification over a pair to a conjunction.  (Contributed by
       NM, 3-Jun-2007.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    ralpr $p |- ( A. x e. { A , B } ph <-> ( ps /\ ch ) ) $=
      cA cvv wcel cB cvv wcel wph vx cA cB cpr wral wps wch wa wb ralpr.1
      ralpr.2 wph wps wch vx cA cB cvv cvv ralpr.3 ralpr.4 ralprg mp2an $.

    $( Convert an existential quantification over a pair to a disjunction.
       (Contributed by NM, 3-Jun-2007.)  (Revised by Mario Carneiro,
       23-Apr-2015.) $)
    rexpr $p |- ( E. x e. { A , B } ph <-> ( ps \/ ch ) ) $=
      cA cvv wcel cB cvv wcel wph vx cA cB cpr wrex wps wch wo wb ralpr.1
      ralpr.2 wph wps wch vx cA cB cvv cvv ralpr.3 ralpr.4 rexprg mp2an $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x ps $.  $d x ch $.  $d x th $.
    raltp.1 $e |- A e. _V $.
    raltp.2 $e |- B e. _V $.
    raltp.3 $e |- C e. _V $.
    raltp.4 $e |- ( x = A -> ( ph <-> ps ) ) $.
    raltp.5 $e |- ( x = B -> ( ph <-> ch ) ) $.
    raltp.6 $e |- ( x = C -> ( ph <-> th ) ) $.
    $( Convert a quantification over a triple to a conjunction.  (Contributed
       by NM, 13-Sep-2011.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    raltp $p |- ( A. x e. { A , B , C } ph <-> ( ps /\ ch /\ th ) ) $=
      cA cvv wcel cB cvv wcel cC cvv wcel wph vx cA cB cC ctp wral wps wch wth
      w3a wb raltp.1 raltp.2 raltp.3 wph wps wch wth vx cA cB cC cvv cvv cvv
      raltp.4 raltp.5 raltp.6 raltpg mp3an $.

    $( Convert a quantification over a triple to a disjunction.  (Contributed
       by Mario Carneiro, 23-Apr-2015.) $)
    rextp $p |- ( E. x e. { A , B , C } ph <-> ( ps \/ ch \/ th ) ) $=
      cA cvv wcel cB cvv wcel cC cvv wcel wph vx cA cB cC ctp wrex wps wch wth
      w3o wb raltp.1 raltp.2 raltp.3 wph wps wch wth vx cA cB cC cvv cvv cvv
      raltp.4 raltp.5 raltp.6 rextpg mp3an $.
  $}

  ${
    $d x y A $.  $d y ph $.
    $( TODO - make obsolete; use ralsnsSBC instead - also,
       shorten posn w/ ralsn or ralsng $)
    $( Substitution expressed in terms of quantification over a singleton.
       (Contributed by NM, 14-Dec-2005.)  (Revised by Mario Carneiro,
       23-Apr-2015.) $)
    sbcsng $p |- ( A e. V -> ( [. A / x ]. ph <-> A. x e. { A } ph ) ) $=
      cA cV wcel wph vx cA csn wral wph vx cA wsbc wph vx cA cV ralsns bicomd
      $.
  $}

  ${
    nfsn.1 $e |- F/_ x A $.
    $( Bound-variable hypothesis builder for singletons.  (Contributed by NM,
       14-Nov-1995.) $)
    nfsn $p |- F/_ x { A } $=
      vx cA csn cA cA cpr cA dfsn2 vx cA cA nfsn.1 nfsn.1 nfpr nfcxfr $.
  $}

  ${
    $d A y $.  $d B y $.  $d V y $.  $d x y $.
    $( Distribute proper substitution through the singleton of a class.
       ~ csbsng is derived from the virtual deduction proof ~ csbsngVD .
       (Contributed by Alan Sare, 10-Nov-2012.) $)
    csbsng $p |- ( A e. V -> [_ A / x ]_ { B } = { [_ A / x ]_ B } ) $=
      cA cV wcel vx cA vy cv cB wceq vy cab csb vy cv vx cA cB csb wceq vy cab
      vx cA cB csn csb vx cA cB csb csn cA cV wcel vx cA vy cv cB wceq vy cab
      csb vy cv cB wceq vx cA wsbc vy cab vy cv vx cA cB csb wceq vy cab vy cv
      cB wceq vx vy cA cV csbabg cA cV wcel vy cv cB wceq vx cA wsbc vy cv vx
      cA cB csb wceq vy vx cA vy cv cB cV sbceq2g abbidv eqtrd vx cA cB csn vy
      cv cB wceq vy cab vy cB df-sn csbeq2i vy vx cA cB csb df-sn 3eqtr4g $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Intersection with the singleton of a non-member is disjoint.
       (Contributed by NM, 22-May-1998.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.)  (Proof shortened by Wolf Lammen, 30-Sep-2014.) $)
    disjsn $p |- ( ( A i^i { B } ) = (/) <-> -. B e. A ) $=
      cA cB csn cin c0 wceq vx cv cA wcel vx cv cB csn wcel wn wi vx wal vx cv
      cB wceq vx cv cA wcel wa wn vx wal cB cA wcel wn vx cA cB csn disj1 vx cv
      cA wcel vx cv cB csn wcel wn wi vx cv cB wceq vx cv cA wcel wa wn vx vx
      cv cA wcel vx cv cB csn wcel wn wi vx cv cB csn wcel vx cv cA wcel wn wi
      vx cv cB wceq vx cv cA wcel wn wi vx cv cB wceq vx cv cA wcel wa wn vx cv
      cA wcel vx cv cB csn wcel con2b vx cv cB csn wcel vx cv cB wceq vx cv cA
      wcel wn vx cB elsn imbi1i vx cv cB wceq vx cv cA wcel imnan 3bitri albii
      vx cv cB wceq vx cv cA wcel wa wn vx wal vx cv cB wceq vx cv cA wcel wa
      vx wex cB cA wcel vx cv cB wceq vx cv cA wcel wa vx alnex vx cB cA
      df-clel xchbinxr 3bitri $.
  $}

  $( Intersection of distinct singletons is disjoint.  (Contributed by NM,
     25-May-1998.) $)
  disjsn2 $p |- ( A =/= B -> ( { A } i^i { B } ) = (/) ) $=
    cA cB wne cB cA csn wcel wn cA csn cB csn cin c0 wceq cB cA csn wcel cA cB
    cB cA csn wcel cB cA cB cA elsni eqcomd necon3ai cA csn cB disjsn sylibr $.

  ${
    $d x A $.
    $( The singleton of a proper class (one that doesn't exist) is the empty
       set.  Theorem 7.2 of [Quine] p. 48.  (Contributed by NM, 5-Aug-1993.) $)
    snprc $p |- ( -. A e. _V <-> { A } = (/) ) $=
      cA csn c0 wceq cA cvv wcel vx cv cA csn wcel vx wex vx cv cA wceq vx wex
      cA csn c0 wceq wn cA cvv wcel vx cv cA csn wcel vx cv cA wceq vx vx cA
      elsn exbii vx cA csn neq0 vx cA isset 3bitr4i con1bii $.
  $}

  ${
    $d x y A $.  $d x B $.
    r19.12sn.1 $e |- A e. _V $.
    $( Special case of ~ r19.12 where its converse holds.  (Contributed by NM,
       19-May-2008.)  (Revised by Mario Carneiro, 23-Apr-2015.) $)
    r19.12sn $p |- ( E. x e. { A } A. y e. B ph
                <-> A. y e. B E. x e. { A } ph ) $=
      cA cvv wcel wph vy cB wral vx cA csn wrex wph vx cA csn wrex vy cB wral
      wb r19.12sn.1 cA cvv wcel wph vy cB wral vx cA wsbc wph vx cA wsbc vy cB
      wral wph vy cB wral vx cA csn wrex wph vx cA csn wrex vy cB wral wph vx
      vy cA cB cvv sbcralg wph vy cB wral vx cA cvv rexsns cA cvv wcel wph vx
      cA csn wrex wph vx cA wsbc vy cB wph vx cA cvv rexsns ralbidv 3bitr4d
      ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Condition where a restricted class abstraction is a singleton.
       (Contributed by NM, 28-May-2006.) $)
    rabsn $p |- ( B e. A -> { x e. A | x = B } = { B } ) $=
      cB cA wcel vx cv cA wcel vx cv cB wceq wa vx cab vx cv cB wceq vx cab vx
      cv cB wceq vx cA crab cB csn cB cA wcel vx cv cA wcel vx cv cB wceq wa vx
      cv cB wceq vx vx cv cA wcel vx cv cB wceq wa cB cA wcel vx cv cB wceq vx
      cv cB wceq vx cv cA wcel cB cA wcel vx cv cB cA eleq1 pm5.32ri baib
      abbidv vx cv cB wceq vx cA df-rab vx cB df-sn 3eqtr4g $.
  $}

  ${
    $d x y $.  $d y ph $.  $d y A $.
    $( Another way to express existential uniqueness of a wff: its class
       abstraction is a singleton.  (Contributed by Mario Carneiro,
       14-Nov-2016.) $)
    euabsn2 $p |- ( E! x ph <-> E. y { x | ph } = { y } ) $=
      wph vx weu wph vx cv vy cv wceq wb vx wal vy wex wph vx cab vy cv csn
      wceq vy wex wph vx vy df-eu wph vx cab vy cv csn wceq wph vx cv vy cv
      wceq wb vx wal vy wph vx cab vy cv csn wceq wph vx cv vy cv csn wcel wb
      vx wal wph vx cv vy cv wceq wb vx wal wph vx vy cv csn abeq1 wph vx cv vy
      cv csn wcel wb wph vx cv vy cv wceq wb vx vx cv vy cv csn wcel vx cv vy
      cv wceq wph vx vy cv elsn bibi2i albii bitri exbii bitr4i $.

    $( Another way to express existential uniqueness of a wff: its class
       abstraction is a singleton.  (Contributed by NM, 22-Feb-2004.) $)
    euabsn $p |- ( E! x ph <-> E. x { x | ph } = { x } ) $=
      wph vx weu wph vx cab vy cv csn wceq vy wex wph vx cab vx cv csn wceq vx
      wex wph vx vy euabsn2 wph vx cab vx cv csn wceq wph vx cab vy cv csn wceq
      vx vy wph vx cab vx cv csn wceq vy nfv vx wph vx cab vy cv csn wph vx
      nfab1 nfeq1 vx cv vy cv wceq vx cv csn vy cv csn wph vx cab vx cv vy cv
      sneq eqeq2d cbvex bitr4i $.

    $( A way to express restricted existential uniqueness of a wff: its
       restricted class abstraction is a singleton.  (Contributed by NM,
       30-May-2006.)  (Proof shortened by Mario Carneiro, 14-Nov-2016.) $)
    reusn $p |- ( E! x e. A ph <-> E. y { x e. A | ph } = { y } ) $=
      vx cv cA wcel wph wa vx weu vx cv cA wcel wph wa vx cab vy cv csn wceq vy
      wex wph vx cA wreu wph vx cA crab vy cv csn wceq vy wex vx cv cA wcel wph
      wa vx vy euabsn2 wph vx cA df-reu wph vx cA crab vy cv csn wceq vx cv cA
      wcel wph wa vx cab vy cv csn wceq vy wph vx cA crab vx cv cA wcel wph wa
      vx cab vy cv csn wph vx cA df-rab eqeq1i exbii 3bitr4i $.

    $( Restricted existential uniqueness determined by a singleton.
       (Contributed by NM, 29-May-2006.) $)
    absneu $p |- ( ( A e. V /\ { x | ph } = { A } ) -> E! x ph ) $=
      cA cV wcel wph vx cab cA csn wceq wa wph vx cab vy cv csn wceq vy wex wph
      vx weu cA cV wcel wph vx cab cA csn wceq wph vx cab vy cv csn wceq vy wex
      wph vx cab vy cv csn wceq wph vx cab cA csn wceq vy cA cV vy cv cA wceq
      vy cv csn cA csn wph vx cab vy cv cA sneq eqeq2d spcegv imp wph vx vy
      euabsn2 sylibr $.

    $( Restricted existential uniqueness determined by a singleton.
       (Contributed by NM, 29-May-2006.)  (Revised by Mario Carneiro,
       23-Dec-2016.) $)
    rabsneu $p |- ( ( A e. V /\ { x e. B | ph } = { A } ) -> E! x e. B ph ) $=
      cA cV wcel wph vx cB crab cA csn wceq wa vx cv cB wcel wph wa vx weu wph
      vx cB wreu wph vx cB crab cA csn wceq cA cV wcel vx cv cB wcel wph wa vx
      cab cA csn wceq vx cv cB wcel wph wa vx weu wph vx cB crab vx cv cB wcel
      wph wa vx cab cA csn wph vx cB df-rab eqeq1i vx cv cB wcel wph wa vx cA
      cV absneu sylan2b wph vx cB df-reu sylibr $.
  $}

  ${
    $d x A $.
    $( Two ways to express " ` A ` is a singleton."  (Contributed by NM,
       30-Oct-2010.) $)
    eusn $p |- ( E! x x e. A <-> E. x A = { x } ) $=
      vx cv cA wcel vx weu vx cv cA wcel vx cab vx cv csn wceq vx wex cA vx cv
      csn wceq vx wex vx cv cA wcel vx euabsn vx cv cA wcel vx cab vx cv csn
      wceq cA vx cv csn wceq vx vx cv cA wcel vx cab cA vx cv csn vx cA abid2
      eqeq1i exbii bitri $.
  $}

  ${
    $d x A $.  $d x B $.  $d x ps $.
    rabsnt.1 $e |- B e. _V $.
    rabsnt.2 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( Truth implied by equality of a restricted class abstraction and a
       singleton.  (Contributed by NM, 29-May-2006.)  (Proof shortened by Mario
       Carneiro, 23-Dec-2016.) $)
    rabsnt $p |- ( { x e. A | ph } = { B } -> ps ) $=
      wph vx cA crab cB csn wceq cB wph vx cA crab wcel wps wph vx cA crab cB
      csn wceq cB cB csn wph vx cA crab cB rabsnt.1 snid wph vx cA crab cB csn
      wceq id syl5eleqr cB wph vx cA crab wcel cB cA wcel wps wph wps vx cB cA
      rabsnt.2 elrab simprbi syl $.
  $}

  $( Commutative law for unordered pairs.  (Contributed by NM, 5-Aug-1993.) $)
  prcom $p |- { A , B } = { B , A } $=
    cA csn cB csn cun cB csn cA csn cun cA cB cpr cB cA cpr cA csn cB csn uncom
    cA cB df-pr cB cA df-pr 3eqtr4i $.

  $( Equality theorem for unordered pairs.  (Contributed by NM,
     29-Mar-1998.) $)
  preq1 $p |- ( A = B -> { A , C } = { B , C } ) $=
    cA cB wceq cA csn cC csn cun cB csn cC csn cun cA cC cpr cB cC cpr cA cB
    wceq cA csn cB csn cC csn cA cB sneq uneq1d cA cC df-pr cB cC df-pr 3eqtr4g
    $.

  $( Equality theorem for unordered pairs.  (Contributed by NM, 5-Aug-1993.) $)
  preq2 $p |- ( A = B -> { C , A } = { C , B } ) $=
    cA cB wceq cA cC cpr cB cC cpr cC cA cpr cC cB cpr cA cB cC preq1 cC cA
    prcom cC cB prcom 3eqtr4g $.

  $( Equality theorem for unordered pairs.  (Contributed by NM,
     19-Oct-2012.) $)
  preq12 $p |- ( ( A = C /\ B = D ) -> { A , B } = { C , D } ) $=
    cA cC wceq cB cD wceq cA cB cpr cC cB cpr cC cD cpr cA cC cB preq1 cB cD cC
    preq2 sylan9eq $.

  ${
    preq1i.1 $e |- A = B $.
    $( Equality inference for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)
    preq1i $p |- { A , C } = { B , C } $=
      cA cB wceq cA cC cpr cB cC cpr wceq preq1i.1 cA cB cC preq1 ax-mp $.

    $( Equality inference for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)
    preq2i $p |- { C , A } = { C , B } $=
      cA cB wceq cC cA cpr cC cB cpr wceq preq1i.1 cA cB cC preq2 ax-mp $.

    ${
      preq12i.2 $e |- C = D $.
      $( Equality inference for unordered pairs.  (Contributed by NM,
         19-Oct-2012.) $)
      preq12i $p |- { A , C } = { B , D } $=
        cA cB wceq cC cD wceq cA cC cpr cB cD cpr wceq preq1i.1 preq12i.2 cA cC
        cB cD preq12 mp2an $.
    $}
  $}

  ${
    preq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)
    preq1d $p |- ( ph -> { A , C } = { B , C } ) $=
      wph cA cB wceq cA cC cpr cB cC cpr wceq preq1d.1 cA cB cC preq1 syl $.

    $( Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)
    preq2d $p |- ( ph -> { C , A } = { C , B } ) $=
      wph cA cB wceq cC cA cpr cC cB cpr wceq preq1d.1 cA cB cC preq2 syl $.

    preq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for unordered pairs.  (Contributed by NM,
       19-Oct-2012.) $)
    preq12d $p |- ( ph -> { A , C } = { B , D } ) $=
      wph cA cB wceq cC cD wceq cA cC cpr cB cD cpr wceq preq1d.1 preq12d.2 cA
      cC cB cD preq12 syl2anc $.
  $}

  $( Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) $)
  tpeq1 $p |- ( A = B -> { A , C , D } = { B , C , D } ) $=
    cA cB wceq cA cC cpr cD csn cun cB cC cpr cD csn cun cA cC cD ctp cB cC cD
    ctp cA cB wceq cA cC cpr cB cC cpr cD csn cA cB cC preq1 uneq1d cA cC cD
    df-tp cB cC cD df-tp 3eqtr4g $.

  $( Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) $)
  tpeq2 $p |- ( A = B -> { C , A , D } = { C , B , D } ) $=
    cA cB wceq cC cA cpr cD csn cun cC cB cpr cD csn cun cC cA cD ctp cC cB cD
    ctp cA cB wceq cC cA cpr cC cB cpr cD csn cA cB cC preq2 uneq1d cC cA cD
    df-tp cC cB cD df-tp 3eqtr4g $.

  $( Equality theorem for unordered triples.  (Contributed by NM,
     13-Sep-2011.) $)
  tpeq3 $p |- ( A = B -> { C , D , A } = { C , D , B } ) $=
    cA cB wceq cC cD cpr cA csn cun cC cD cpr cB csn cun cC cD cA ctp cC cD cB
    ctp cA cB wceq cA csn cB csn cC cD cpr cA cB sneq uneq2d cC cD cA df-tp cC
    cD cB df-tp 3eqtr4g $.

  ${
    tpeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)
    tpeq1d $p |- ( ph -> { A , C , D } = { B , C , D } ) $=
      wph cA cB wceq cA cC cD ctp cB cC cD ctp wceq tpeq1d.1 cA cB cC cD tpeq1
      syl $.

    $( Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)
    tpeq2d $p |- ( ph -> { C , A , D } = { C , B , D } ) $=
      wph cA cB wceq cC cA cD ctp cC cB cD ctp wceq tpeq1d.1 cA cB cC cD tpeq2
      syl $.

    $( Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)
    tpeq3d $p |- ( ph -> { C , D , A } = { C , D , B } ) $=
      wph cA cB wceq cC cD cA ctp cC cD cB ctp wceq tpeq1d.1 cA cB cC cD tpeq3
      syl $.

    tpeq123d.2 $e |- ( ph -> C = D ) $.
    tpeq123d.3 $e |- ( ph -> E = F ) $.
    $( Equality theorem for unordered triples.  (Contributed by NM,
       22-Jun-2014.) $)
    tpeq123d $p |- ( ph -> { A , C , E } = { B , D , F } ) $=
      wph cA cC cE ctp cB cC cE ctp cB cD cE ctp cB cD cF ctp wph cA cB cC cE
      tpeq1d.1 tpeq1d wph cC cD cB cE tpeq123d.2 tpeq2d wph cE cF cB cD
      tpeq123d.3 tpeq3d 3eqtrd $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Rotation of the elements of an unordered triple.  (Contributed by Alan
       Sare, 24-Oct-2011.) $)
    tprot $p |- { A , B , C } = { B , C , A } $=
      vx cv cA wceq vx cv cB wceq vx cv cC wceq w3o vx cab vx cv cB wceq vx cv
      cC wceq vx cv cA wceq w3o vx cab cA cB cC ctp cB cC cA ctp vx cv cA wceq
      vx cv cB wceq vx cv cC wceq w3o vx cv cB wceq vx cv cC wceq vx cv cA wceq
      w3o vx vx cv cA wceq vx cv cB wceq vx cv cC wceq 3orrot abbii vx cA cB cC
      dftp2 vx cB cC cA dftp2 3eqtr4i $.
  $}

  $( Swap 1st and 2nd members of an undordered triple.  (Contributed by NM,
     22-May-2015.) $)
  tpcoma $p |- { A , B , C } = { B , A , C } $=
    cA cB cpr cC csn cun cB cA cpr cC csn cun cA cB cC ctp cB cA cC ctp cA cB
    cpr cB cA cpr cC csn cA cB prcom uneq1i cA cB cC df-tp cB cA cC df-tp
    3eqtr4i $.

  $( Swap 2nd and 3rd members of an undordered triple.  (Contributed by NM,
     22-May-2015.) $)
  tpcomb $p |- { A , B , C } = { A , C , B } $=
    cB cC cA ctp cC cB cA ctp cA cB cC ctp cA cC cB ctp cB cC cA tpcoma cA cB
    cC tprot cA cC cB tprot 3eqtr4i $.

  $( Split off the first element of an unordered triple.  (Contributed by Mario
     Carneiro, 5-Jan-2016.) $)
  tpass $p |- { A , B , C } = ( { A } u. { B , C } ) $=
    cB cC cA ctp cB cC cpr cA csn cun cA cB cC ctp cA csn cB cC cpr cun cB cC
    cA df-tp cA cB cC tprot cA csn cB cC cpr uncom 3eqtr4i $.

  $( Two ways to write an unordered quadruple.  (Contributed by Mario Carneiro,
     5-Jan-2016.) $)
  qdass $p |- ( { A , B } u. { C , D } ) = ( { A , B , C } u. { D } ) $=
    cA cB cpr cC csn cun cD csn cun cA cB cpr cC csn cD csn cun cun cA cB cC
    ctp cD csn cun cA cB cpr cC cD cpr cun cA cB cpr cC csn cD csn unass cA cB
    cC ctp cA cB cpr cC csn cun cD csn cA cB cC df-tp uneq1i cC cD cpr cC csn
    cD csn cun cA cB cpr cC cD df-pr uneq2i 3eqtr4ri $.

  $( Two ways to write an unordered quadruple.  (Contributed by Mario Carneiro,
     5-Jan-2016.) $)
  qdassr $p |- ( { A , B } u. { C , D } ) = ( { A } u. { B , C , D } ) $=
    cA csn cB csn cun cC cD cpr cun cA csn cB csn cC cD cpr cun cun cA cB cpr
    cC cD cpr cun cA csn cB cC cD ctp cun cA csn cB csn cC cD cpr unass cA cB
    cpr cA csn cB csn cun cC cD cpr cA cB df-pr uneq1i cB cC cD ctp cB csn cC
    cD cpr cun cA csn cB cC cD tpass uneq2i 3eqtr4i $.

  $( Unordered triple ` { A , A , B } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)
  tpidm12 $p |- { A , A , B } = { A , B } $=
    cA csn cB csn cun cA cA cpr cB csn cun cA cB cpr cA cA cB ctp cA csn cA cA
    cpr cB csn cA dfsn2 uneq1i cA cB df-pr cA cA cB df-tp 3eqtr4ri $.

  $( Unordered triple ` { A , B , A } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)
  tpidm13 $p |- { A , B , A } = { A , B } $=
    cA cA cB ctp cA cB cA ctp cA cB cpr cA cA cB tprot cA cB tpidm12 eqtr3i $.

  $( Unordered triple ` { A , B , B } ` is just an overlong way to write
     ` { A , B } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)
  tpidm23 $p |- { A , B , B } = { A , B } $=
    cA cB cB ctp cB cB cA ctp cB cA cpr cA cB cpr cA cB cB tprot cB cA tpidm12
    cB cA prcom 3eqtri $.

  $( Unordered triple ` { A , A , A } ` is just an overlong way to write
     ` { A } ` .  (Contributed by David A. Wheeler, 10-May-2015.) $)
  tpidm $p |- { A , A , A } = { A } $=
    cA cA cA ctp cA cA cpr cA csn cA cA tpidm12 cA dfsn2 eqtr4i $.

  $( An unordered pair contains its first member.  Part of Theorem 7.6 of
     [Quine] p. 49.  (Contributed by Stefan Allan, 8-Nov-2008.) $)
  prid1g $p |- ( A e. V -> A e. { A , B } ) $=
    cA cV wcel cA cA cB cpr wcel cA cA wceq cA cB wceq wo cA cA wceq cA cB wceq
    cA eqid orci cA cA cB cV elprg mpbiri $.

  $( An unordered pair contains its second member.  Part of Theorem 7.6 of
     [Quine] p. 49.  (Contributed by Stefan Allan, 8-Nov-2008.) $)
  prid2g $p |- ( B e. V -> B e. { A , B } ) $=
    cB cV wcel cB cB cA cpr cA cB cpr cB cA cV prid1g cB cA prcom syl6eleq $.

  ${
    prid1.1 $e |- A e. _V $.
    $( An unordered pair contains its first member.  Part of Theorem 7.6 of
       [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) $)
    prid1 $p |- A e. { A , B } $=
      cA cvv wcel cA cA cB cpr wcel prid1.1 cA cB cvv prid1g ax-mp $.
  $}

  ${
    prid2.1 $e |- B e. _V $.
    $( An unordered pair contains its second member.  Part of Theorem 7.6 of
       [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) $)
    prid2 $p |- B e. { A , B } $=
      cB cB cA cpr cA cB cpr cB cA prid2.1 prid1 cB cA prcom eleqtri $.
  $}

  $( A proper class vanishes in an unordered pair.  (Contributed by NM,
     5-Aug-1993.) $)
  prprc1 $p |- ( -. A e. _V -> { A , B } = { B } ) $=
    cA cvv wcel wn cA csn c0 wceq cA cB cpr cB csn wceq cA snprc cA csn c0 wceq
    cA csn cB csn cun c0 cB csn cun cA cB cpr cB csn cA csn c0 cB csn uneq1 cA
    cB df-pr c0 cB csn cun cB csn c0 cun cB csn c0 cB csn uncom cB csn un0
    eqtr2i 3eqtr4g sylbi $.

  $( A proper class vanishes in an unordered pair.  (Contributed by NM,
     22-Mar-2006.) $)
  prprc2 $p |- ( -. B e. _V -> { A , B } = { A } ) $=
    cB cvv wcel wn cA cB cpr cB cA cpr cA csn cA cB prcom cB cA prprc1 syl5eq
    $.

  $( An unordered pair containing two proper classes is the empty set.
     (Contributed by NM, 22-Mar-2006.) $)
  prprc $p |- ( ( -. A e. _V /\ -. B e. _V ) -> { A , B } = (/) ) $=
    cA cvv wcel wn cB cvv wcel wn cA cB cpr cB csn c0 cA cB prprc1 cB cvv wcel
    wn cB csn c0 wceq cB snprc biimpi sylan9eq $.

  ${
    tpid1.1 $e |- A e. _V $.
    $( One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    tpid1 $p |- A e. { A , B , C } $=
      cA cA cB cC ctp wcel cA cA wceq cA cB wceq cA cC wceq w3o cA cA wceq cA
      cB wceq cA cC wceq cA eqid 3mix1i cA cA cB cC tpid1.1 eltp mpbir $.
  $}

  ${
    tpid2.1 $e |- B e. _V $.
    $( One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    tpid2 $p |- B e. { A , B , C } $=
      cB cA cB cC ctp wcel cB cA wceq cB cB wceq cB cC wceq w3o cB cB wceq cB
      cA wceq cB cC wceq cB eqid 3mix2i cB cA cB cC tpid2.1 eltp mpbir $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.  $d x D $.  $d x ps $.
    $( Closed theorem form of ~ tpid3 .  This proof was automatically generated
       from the virtual deduction proof ~ tpid3gVD using a translation
       program.  (Contributed by Alan Sare, 24-Oct-2011.) $)
    tpid3g $p |- ( A e. B -> A e. { C , D , A } ) $=
      cA cB wcel vx cv cA wceq vx wex cA cC cD cA ctp wcel vx cA cB elisset cA
      cB wcel vx cv cA wceq cA cC cD cA ctp wcel vx vx cv cA wceq vx cv cC cD
      cA ctp wcel cA cC cD cA ctp wcel cA cB wcel cA cB wcel vx cv cA wceq vx
      cv vx cv cC wceq vx cv cD wceq vx cv cA wceq w3o vx cab wcel vx cv cC cD
      cA ctp wcel cA cB wcel vx cv cA wceq vx cv cC wceq vx cv cD wceq vx cv cA
      wceq w3o vx cv vx cv cC wceq vx cv cD wceq vx cv cA wceq w3o vx cab wcel
      vx cv cA wceq vx cv cC wceq vx cv cD wceq vx cv cA wceq w3o wi cA cB wcel
      vx cv cA wceq vx cv cC wceq vx cv cD wceq 3mix3 a1i vx cv cC wceq vx cv
      cD wceq vx cv cA wceq w3o vx abid syl6ibr cC cD cA ctp vx cv cC wceq vx
      cv cD wceq vx cv cA wceq w3o vx cab vx cv vx cC cD cA dftp2 eleq2i
      syl6ibr vx cv cA cC cD cA ctp eleq1 mpbidi exlimdv mpd $.
  $}

  ${
    tpid3.1 $e |- C e. _V $.
    $( One of the three elements of an unordered triple.  (Contributed by NM,
       7-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    tpid3 $p |- C e. { A , B , C } $=
      cC cA cB cC ctp wcel cC cA wceq cC cB wceq cC cC wceq w3o cC cC wceq cC
      cA wceq cC cB wceq cC eqid 3mix3i cC cA cB cC tpid3.1 eltp mpbir $.
  $}

  $( The singleton of a set is not empty.  (Contributed by NM, 14-Dec-2008.) $)
  snnzg $p |- ( A e. V -> { A } =/= (/) ) $=
    cA cV wcel cA cA csn wcel cA csn c0 wne cA cV snidg cA csn cA ne0i syl $.

  ${
    snnz.1 $e |- A e. _V $.
    $( The singleton of a set is not empty.  (Contributed by NM,
       10-Apr-1994.) $)
    snnz $p |- { A } =/= (/) $=
      cA cvv wcel cA csn c0 wne snnz.1 cA cvv snnzg ax-mp $.
  $}

  ${
    prnz.1 $e |- A e. _V $.
    $( A pair containing a set is not empty.  (Contributed by NM,
       9-Apr-1994.) $)
    prnz $p |- { A , B } =/= (/) $=
      cA cA cB cpr wcel cA cB cpr c0 wne cA cB prnz.1 prid1 cA cB cpr cA ne0i
      ax-mp $.
  $}

  ${
    $d x A $.  $d x B $.
    $( A pair containing a set is not empty.  (Contributed by FL,
       19-Sep-2011.) $)
    prnzg $p |- ( A e. V -> { A , B } =/= (/) ) $=
      vx cv cB cpr c0 wne cA cB cpr c0 wne vx cA cV vx cv cA wceq vx cv cB cpr
      cA cB cpr c0 vx cv cA cB preq1 neeq1d vx cv cB vx vex prnz vtoclg $.
  $}

  ${
    tpnz.1 $e |- A e. _V $.
    $( A triplet containing a set is not empty.  (Contributed by NM,
       10-Apr-1994.) $)
    tpnz $p |- { A , B , C } =/= (/) $=
      cA cA cB cC ctp wcel cA cB cC ctp c0 wne cA cB cC tpnz.1 tpid1 cA cB cC
      ctp cA ne0i ax-mp $.
  $}

  ${
    $d A x $.  $d B x $.
    snss.1 $e |- A e. _V $.
    $( The singleton of an element of a class is a subset of the class.
       Theorem 7.4 of [Quine] p. 49.  (Contributed by NM, 5-Aug-1993.) $)
    snss $p |- ( A e. B <-> { A } C_ B ) $=
      vx cv cA csn wcel vx cv cB wcel wi vx wal vx cv cA wceq vx cv cB wcel wi
      vx wal cA csn cB wss cA cB wcel vx cv cA csn wcel vx cv cB wcel wi vx cv
      cA wceq vx cv cB wcel wi vx vx cv cA csn wcel vx cv cA wceq vx cv cB wcel
      vx cA elsn imbi1i albii vx cA csn cB dfss2 vx cA cB snss.1 clel2 3bitr4ri
      $.
  $}

  $( Membership in a set with an element removed.  (Contributed by NM,
     10-Oct-2007.) $)
  eldifsn $p |- ( A e. ( B \ { C } ) <-> ( A e. B /\ A =/= C ) ) $=
    cA cB cC csn cdif wcel cA cB wcel cA cC csn wcel wn wa cA cB wcel cA cC wne
    wa cA cB cC csn eldif cA cB wcel cA cC csn wcel wn cA cC wne cA cB wcel cA
    cC csn wcel cA cC cA cC cB elsncg necon3bbid pm5.32i bitri $.

  $( Membership in a set with an element removed.  (Contributed by NM,
     10-Mar-2015.) $)
  eldifsni $p |- ( A e. ( B \ { C } ) -> A =/= C ) $=
    cA cB cC csn cdif wcel cA cB wcel cA cC wne cA cB cC eldifsn simprbi $.

  $( ` A ` is not in ` ( B \ { A } ) ` .  (Contributed by David Moews,
     1-May-2017.) $)
  neldifsn $p |- -. A e. ( B \ { A } ) $=
    cA cB cA csn cdif wcel cA cA wne cA neirr cA cB cA eldifsni mto $.

  $( ` A ` is not in ` ( B \ { A } ) ` .  Deduction form.  (Contributed by
     David Moews, 1-May-2017.) $)
  neldifsnd $p |- ( ph -> -. A e. ( B \ { A } ) ) $=
    cA cB cA csn cdif wcel wn wph cA cB neldifsn a1i $.

  $( Restricted existential quantification over a set with an element removed.
     (Contributed by NM, 4-Feb-2015.) $)
  rexdifsn $p |- ( E. x e. ( A \ { B } ) ph
      <-> E. x e. A ( x =/= B /\ ph ) ) $=
    wph vx cv cB wne wph wa vx cA cB csn cdif cA vx cv cA cB csn cdif wcel wph
    wa vx cv cA wcel vx cv cB wne wa wph wa vx cv cA wcel vx cv cB wne wph wa
    wa vx cv cA cB csn cdif wcel vx cv cA wcel vx cv cB wne wa wph vx cv cA cB
    eldifsn anbi1i vx cv cA wcel vx cv cB wne wph anass bitri rexbii2 $.

  ${
    $d A x $.  $d B x $.
    $( The singleton of an element of a class is a subset of the class.
       Theorem 7.4 of [Quine] p. 49.  (Contributed by NM, 22-Jul-2001.) $)
    snssg $p |- ( A e. V -> ( A e. B <-> { A } C_ B ) ) $=
      vx cv cB wcel vx cv csn cB wss cA cB wcel cA csn cB wss vx cA cV vx cv cA
      cB eleq1 vx cv cA wceq vx cv csn cA csn cB vx cv cA sneq sseq1d vx cv cB
      vx vex snss vtoclbg $.

    $( An element not in a set can be removed without affecting the set.
       (Contributed by NM, 16-Mar-2006.)  (Proof shortened by Andrew Salmon,
       29-Jun-2011.) $)
    difsn $p |- ( -. A e. B -> ( B \ { A } ) = B ) $=
      cA cB wcel wn vx cB cA csn cdif cB vx cv cB cA csn cdif wcel vx cv cB
      wcel vx cv cA wne wa cA cB wcel wn vx cv cB wcel vx cv cB cA eldifsn cA
      cB wcel wn vx cv cB wcel vx cv cA wne wa vx cv cB wcel vx cv cB wcel vx
      cv cA wne simpl cA cB wcel wn vx cv cB wcel vx cv cA wne vx cv cB wcel cA
      cB wcel wn vx cv cA wne vx cv cB wcel cA cB wcel vx cv cA vx cv cA wceq
      vx cv cB wcel cA cB wcel vx cv cA cB eleq1 biimpcd necon3bd com12 ancld
      impbid2 syl5bb eqrdv $.

    $( Removal of a singleton from an unordered pair.  (Contributed by NM,
       16-Mar-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    difprsn $p |- ( { A , B } \ { A } ) C_ { B } $=
      vx cA cB cpr cA csn cdif cB csn vx cv cA cB cpr wcel vx cv cA csn wcel wn
      wa vx cv cB wceq vx cv cA cB cpr cA csn cdif wcel vx cv cB csn wcel vx cv
      cA cB cpr wcel vx cv cA wceq vx cv cB wceq wo vx cv cA wceq wn vx cv cB
      wceq vx cv cA csn wcel wn vx cv cA cB vx vex elpr vx cv cA csn wcel vx cv
      cA wceq vx cA elsn notbii vx cv cA wceq wn vx cv cB wceq vx cv cA wceq vx
      cv cB wceq wo vx cv cA wceq vx cv cB wceq biorf biimparc syl2anb vx cv cA
      cB cpr cA csn eldif vx cB elsn 3imtr4i ssriv $.
  $}

  $( ` ( B \ { A } ) ` equals ` B ` if and only if ` A ` is not a member of
     ` B ` .  Generalization of ~ difsn .  (Contributed by David Moews,
     1-May-2017.) $)
  difsneq $p |- ( -. A e. B <-> ( B \ { A } ) = B ) $=
    cA cB wcel wn cB cA csn cdif cB wceq cA cB difsn cA cB wcel cB cA csn cdif
    cB cA cB wcel cB cB cA csn cdif cA cB wcel cA cB cA csn cdif wcel wn cB cB
    cA csn cdif wne cA cB wcel cA cB neldifsnd cA cB cB cA csn cdif nelne1
    mpdan necomd necon2bi impbii $.

  $( ` ( B \ { A } ) ` is a proper subclass of ` B ` if and only if ` A ` is a
     member of ` B ` .  (Contributed by David Moews, 1-May-2017.) $)
  difsnpss $p |- ( A e. B <-> ( B \ { A } ) C. B ) $=
    cA cB wcel cA cB wcel wn wn cB cA csn cdif cB wpss cA cB wcel notnot cB cA
    csn cdif cB wne cB cA csn cdif cB wss cB cA csn cdif cB wne wa cA cB wcel
    wn wn cB cA csn cdif cB wpss cB cA csn cdif cB wss cB cA csn cdif cB wne cB
    cA csn difss biantrur cA cB wcel wn cB cA csn cdif cB cA cB difsneq
    necon3bbii cB cA csn cdif cB df-pss 3bitr4i bitri $.

  $( The singleton of an element of a class is a subset of the class.
     (Contributed by NM, 6-Jun-1994.) $)
  snssi $p |- ( A e. B -> { A } C_ B ) $=
    cA cB wcel cA csn cB wss cA cB cB snssg ibi $.

  ${
    snssd.1 $e |- ( ph -> A e. B ) $.
    $( The singleton of an element of a class is a subset of the class
       (deduction rule).  (Contributed by Jonathan Ben-Naim, 3-Jun-2011.) $)
    snssd $p |- ( ph -> { A } C_ B ) $=
      wph cA cB wcel cA csn cB wss snssd.1 wph cA cB wcel cA cB wcel cA csn cB
      wss wb snssd.1 cA cB cB snssg syl mpbid $.
  $}

  $( If we remove a single element from a class then put it back in, we end up
     with the original class.  (Contributed by NM, 2-Oct-2006.) $)
  difsnid $p |- ( B e. A -> ( ( A \ { B } ) u. { B } ) = A ) $=
    cB cA wcel cA cB csn cdif cB csn cun cB csn cA cB csn cdif cun cA cA cB csn
    cdif cB csn uncom cB cA wcel cB csn cA wss cB csn cA cB csn cdif cun cA
    wceq cB cA snssi cB csn cA undif sylib syl5eq $.

  $( Note that ` x ` is a dummy variable in the proof below. $)
  $( Compute the power set of the empty set.  Theorem 89 of [Suppes] p. 47.
     (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
     29-Jun-2011.) $)
  pw0 $p |- ~P (/) = { (/) } $=
    vx cv c0 wss vx cab vx cv c0 wceq vx cab c0 cpw c0 csn vx cv c0 wss vx cv
    c0 wceq vx vx cv ss0b abbii vx c0 df-pw vx c0 df-sn 3eqtr4i $.

  ${
    $d x y $.
    $( Compute the power set of the power set of the empty set.  (See ~ pw0 for
       the power set of the empty set.)  Theorem 90 of [Suppes] p. 48.
       Although this theorem is a special case of ~ pwsn , we have chosen to
       show a direct elementary proof.  (Contributed by NM, 7-Aug-1994.) $)
    pwpw0 $p |- ~P { (/) } = { (/) , { (/) } } $=
      vx cv c0 csn wss vx cab vx cv c0 wceq vx cv c0 csn wceq wo vx cab c0 csn
      cpw c0 c0 csn cpr vx cv c0 csn wss vx cv c0 wceq vx cv c0 csn wceq wo vx
      vx cv c0 csn wss vx cv c0 wceq vx cv c0 csn wceq wo vx cv c0 csn wss vx
      cv c0 wceq vx cv c0 csn wceq vx cv c0 csn wss vx cv c0 wceq wn vx cv c0
      csn wss c0 csn vx cv wss wa vx cv c0 csn wceq vx cv c0 csn wss vx cv c0
      wceq wn c0 csn vx cv wss vx cv c0 csn wss vy cv vx cv wcel vy cv c0 wceq
      wi vy wal vx cv c0 wceq wn c0 csn vx cv wss wi vx cv c0 csn wss vy cv vx
      cv wcel vy cv c0 csn wcel wi vy wal vy cv vx cv wcel vy cv c0 wceq wi vy
      wal vy vx cv c0 csn dfss2 vy cv vx cv wcel vy cv c0 csn wcel wi vy cv vx
      cv wcel vy cv c0 wceq wi vy vy cv c0 csn wcel vy cv c0 wceq vy cv vx cv
      wcel vy c0 elsn imbi2i albii bitri vy cv vx cv wcel vy cv c0 wceq wi vy
      wal vx cv c0 wceq wn vy cv vx cv wcel vy cv c0 wceq wa vy wex c0 csn vx
      cv wss vx cv c0 wceq wn vy cv vx cv wcel vy wex vy cv vx cv wcel vy cv c0
      wceq wi vy wal vy cv vx cv wcel vy cv c0 wceq wa vy wex vy vx cv neq0 vy
      cv vx cv wcel vy cv c0 wceq vy exintr syl5bi vy cv vx cv wcel vy cv c0
      wceq wa vy wex c0 vx cv wcel c0 csn vx cv wss vy cv vx cv wcel vy cv c0
      wceq wa vy wex vy cv c0 wceq vy cv vx cv wcel wa vy wex c0 vx cv wcel vy
      cv vx cv wcel vy cv c0 wceq vy exancom vy c0 vx cv df-clel bitr4i c0 vx
      cv snssi sylbi syl6 sylbi anc2li vx cv c0 csn eqss syl6ibr orrd vx cv c0
      wceq vx cv c0 csn wss vx cv c0 csn wceq vx cv c0 wceq vx cv c0 csn wss c0
      c0 csn wss c0 csn 0ss vx cv c0 c0 csn sseq1 mpbiri vx cv c0 csn eqimss
      jaoi impbii abbii vx c0 csn df-pw vx c0 c0 csn dfpr2 3eqtr4i $.
  $}

  $( A singleton is a subset of an unordered pair containing its member.
     (Contributed by NM, 27-Aug-2004.) $)
  snsspr1 $p |- { A } C_ { A , B } $=
    cA csn cA csn cB csn cun cA cB cpr cA csn cB csn ssun1 cA cB df-pr sseqtr4i
    $.

  $( A singleton is a subset of an unordered pair containing its member.
     (Contributed by NM, 2-May-2009.) $)
  snsspr2 $p |- { B } C_ { A , B } $=
    cB csn cA csn cB csn cun cA cB cpr cB csn cA csn ssun2 cA cB df-pr sseqtr4i
    $.

  $( A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) $)
  snsstp1 $p |- { A } C_ { A , B , C } $=
    cA csn cA cB cpr cC csn cun cA cB cC ctp cA csn cA cB cpr cA cB cpr cC csn
    cun cA cB snsspr1 cA cB cpr cC csn ssun1 sstri cA cB cC df-tp sseqtr4i $.

  $( A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) $)
  snsstp2 $p |- { B } C_ { A , B , C } $=
    cB csn cA cB cpr cC csn cun cA cB cC ctp cB csn cA cB cpr cA cB cpr cC csn
    cun cA cB snsspr2 cA cB cpr cC csn ssun1 sstri cA cB cC df-tp sseqtr4i $.

  $( A singleton is a subset of an unordered triple containing its member.
     (Contributed by NM, 9-Oct-2013.) $)
  snsstp3 $p |- { C } C_ { A , B , C } $=
    cC csn cA cB cpr cC csn cun cA cB cC ctp cC csn cA cB cpr ssun2 cA cB cC
    df-tp sseqtr4i $.

  ${
    $d A x $.  $d B x $.  $d C x $.
    prss.1 $e |- A e. _V $.
    prss.2 $e |- B e. _V $.
    $( A pair of elements of a class is a subset of the class.  Theorem 7.5 of
       [Quine] p. 49.  (Contributed by NM, 30-May-1994.)  (Proof shortened by
       Andrew Salmon, 29-Jun-2011.) $)
    prss $p |- ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) $=
      cA csn cC wss cB csn cC wss wa cA csn cB csn cun cC wss cA cC wcel cB cC
      wcel wa cA cB cpr cC wss cA csn cB csn cC unss cA cC wcel cA csn cC wss
      cB cC wcel cB csn cC wss cA cC prss.1 snss cB cC prss.2 snss anbi12i cA
      cB cpr cA csn cB csn cun cC cA cB df-pr sseq1i 3bitr4i $.
  $}

  ${
    $d x y A $.  $d y B $.  $d x y C $.
    $( A pair of elements of a class is a subset of the class.  Theorem 7.5 of
       [Quine] p. 49.  (Contributed by NM, 22-Mar-2006.)  (Proof shortened by
       Andrew Salmon, 29-Jun-2011.) $)
    prssg $p |- ( ( A e. V /\ B e. W ) ->
                ( ( A e. C /\ B e. C ) <-> { A , B } C_ C ) ) $=
      cA cV wcel cB cW wcel wa cA cC wcel cB cC wcel wa cA csn cC wss cB csn cC
      wss wa cA cB cpr cC wss cA cV wcel cA cC wcel cA csn cC wss cB cW wcel cB
      cC wcel cB csn cC wss cA cC cV snssg cB cC cW snssg bi2anan9 cA csn cC
      wss cB csn cC wss wa cA csn cB csn cun cC wss cA cB cpr cC wss cA csn cB
      csn cC unss cA cB cpr cA csn cB csn cun cC cA cB df-pr sseq1i bitr4i
      syl6bb $.
  $}

  $( A pair of elements of a class is a subset of the class.  (Contributed by
     NM, 16-Jan-2015.) $)
  prssi $p |- ( ( A e. C /\ B e. C ) -> { A , B } C_ C ) $=
    cA cC wcel cB cC wcel wa cA cB cpr cC wss cA cB cC cC cC prssg ibi $.

  ${
    $d x A $.  $d x B $.
    $( The subsets of a singleton.  (Contributed by NM, 24-Apr-2004.) $)
    sssn $p |- ( A C_ { B } <-> ( A = (/) \/ A = { B } ) ) $=
      cA cB csn wss cA c0 wceq cA cB csn wceq wo cA cB csn wss cA c0 wceq cA cB
      csn wceq cA cB csn wss cA c0 wceq wn cA cB csn wss cB csn cA wss wa cA cB
      csn wceq cA cB csn wss cA c0 wceq wn cB csn cA wss cA cB csn wss cA c0
      wceq wn cB cA wcel cB csn cA wss cA c0 wceq wn vx cv cA wcel vx wex cA cB
      csn wss cB cA wcel vx cA neq0 cA cB csn wss vx cv cA wcel cB cA wcel vx
      cA cB csn wss vx cv cA wcel cB cA wcel cA cB csn wss vx cv cA wcel vx cv
      cB wceq vx cv cA wcel cB cA wcel wb cA cB csn wss vx cv cA wcel vx cv cB
      csn wcel vx cv cB wceq cA cB csn vx cv ssel vx cv cB elsni syl6 vx cv cB
      cA eleq1 syl6 ibd exlimdv syl5bi cB cA snssi syl6 anc2li cA cB csn eqss
      syl6ibr orrd cA c0 wceq cA cB csn wss cA cB csn wceq cA c0 wceq cA cB csn
      wss c0 cB csn wss cB csn 0ss cA c0 cB csn sseq1 mpbiri cA cB csn eqimss
      jaoi impbii $.

    $( The property of being sandwiched between two sets naturally splits under
       union with a singleton.  This is the induction hypothesis for the
       determination of large powersets such as ~ pwtp .  (Contributed by Mario
       Carneiro, 2-Jul-2016.) $)
    ssunsn2 $p |- ( ( B C_ A /\ A C_ ( C u. { D } ) ) <->
                    ( ( B C_ A /\ A C_ C ) \/
                      ( ( B u. { D } ) C_ A /\ A C_ ( C u. { D } ) ) ) ) $=
      cD cA wcel cB cA wss cA cC cD csn cun wss wa cB cA wss cA cC wss wa cB cD
      csn cun cA wss cA cC cD csn cun wss wa wo wb cD cA wcel cB cA wss cA cC
      cD csn cun wss wa cB cD csn cun cA wss cA cC cD csn cun wss wa cB cA wss
      cA cC wss wa cB cD csn cun cA wss cA cC cD csn cun wss wa wo cD cA wcel
      cB cA wss cB cD csn cun cA wss cA cC cD csn cun wss cD cA wcel cD csn cA
      wss cB cA wss cB cD csn cun cA wss wb cD cA snssi cB cD csn cun cA wss cB
      cA wss cD csn cA wss cB cA wss cD csn cA wss wa cB cD csn cun cA wss cB
      cD csn cA unss bicomi rbaibr syl anbi1d cD cA wcel cB cA wss cA cC wss wa
      cB cD csn cun cA wss cA cC cD csn cun wss wa wi cB cD csn cun cA wss cA
      cC cD csn cun wss wa cB cA wss cA cC wss wa cB cD csn cun cA wss cA cC cD
      csn cun wss wa wo wb cD cA wcel cB cA wss cB cD csn cun cA wss cA cC wss
      cA cC cD csn cun wss cD cA wcel cD csn cA wss cB cA wss cB cD csn cun cA
      wss wi cD cA snssi cB cA wss cD csn cA wss cB cD csn cun cA wss cB cA wss
      cD csn cA wss wa cB cD csn cun cA wss cB cD csn cA unss biimpi expcom syl
      cA cC wss cA cC cD csn cun wss wi cD cA wcel cA cC cD csn ssun3 a1i
      anim12d cB cA wss cA cC wss wa cB cD csn cun cA wss cA cC cD csn cun wss
      wa pm4.72 sylib bitrd cD cA wcel wn cB cA wss cA cC cD csn cun wss wa cB
      cA wss cA cC wss wa cB cA wss cA cC wss wa cB cD csn cun cA wss cA cC cD
      csn cun wss wa wo cD cA wcel wn cA cC cD csn cun wss cA cC wss cB cA wss
      cD cA wcel wn cA cC wss cA cD csn cdif cC wss cA cC cD csn cun wss cD cA
      wcel wn cA cA cD csn cdif wceq cA cC wss cA cD csn cdif cC wss wb cD cA
      wcel wn cA cD csn cin c0 wceq cA cA cD csn cdif wceq cA cD disjsn cA cD
      csn disj3 bitr3i cA cA cD csn cdif cC sseq1 sylbi cA cC cD csn cun wss cA
      cD csn cC cun wss cA cD csn cdif cC wss cD csn cC cun cC cD csn cun cA cD
      csn cC uncom sseq2i cA cD csn cC ssundif bitr3i syl6rbbr anbi2d cD cA
      wcel wn cB cA wss cA cC wss wa cB cD csn cun cA wss cA cC cD csn cun wss
      wa cB cA wss cA cC wss wa wo cB cA wss cA cC wss wa cB cD csn cun cA wss
      cA cC cD csn cun wss wa wo cD cA wcel wn cB cD csn cun cA wss cA cC cD
      csn cun wss wa cB cA wss cA cC wss wa wi cB cA wss cA cC wss wa cB cD csn
      cun cA wss cA cC cD csn cun wss wa cB cA wss cA cC wss wa wo wb cD cA
      wcel wn cB cD csn cun cA wss cB cA wss cA cC cD csn cun wss cA cC wss cB
      cD csn cun cA wss cB cA wss wi cD cA wcel wn cB cD csn cun cA wss cB cA
      wss cD csn cA wss cB cA wss cD csn cA wss wa cB cD csn cun cA wss cB cD
      csn cA unss bicomi simplbi a1i cD cA wcel wn cA cC cD csn cun wss cA cC
      wss cD cA wcel wn cA cC wss cA cD csn cdif cC wss cA cC cD csn cun wss cD
      cA wcel wn cA cA cD csn cdif wceq cA cC wss cA cD csn cdif cC wss wb cD
      cA wcel wn cA cD csn cin c0 wceq cA cA cD csn cdif wceq cA cD disjsn cA
      cD csn disj3 bitr3i cA cA cD csn cdif cC sseq1 sylbi cA cC cD csn cun wss
      cA cD csn cC cun wss cA cD csn cdif cC wss cD csn cC cun cC cD csn cun cA
      cD csn cC uncom sseq2i cA cD csn cC ssundif bitr3i syl6rbbr biimpd
      anim12d cB cD csn cun cA wss cA cC cD csn cun wss wa cB cA wss cA cC wss
      wa pm4.72 sylib cB cD csn cun cA wss cA cC cD csn cun wss wa cB cA wss cA
      cC wss wa orcom syl6bb bitrd pm2.61i $.

    $( Possible values for a set sandwiched between another set and it plus a
       singleton.  (Contributed by Mario Carneiro, 2-Jul-2016.) $)
    ssunsn $p |- ( ( B C_ A /\ A C_ ( B u. { C } ) ) <->
      ( A = B \/ A = ( B u. { C } ) ) ) $=
      cB cA wss cA cB cC csn cun wss wa cB cA wss cA cB wss wa cB cC csn cun cA
      wss cA cB cC csn cun wss wa wo cA cB wceq cA cB cC csn cun wceq wo cA cB
      cB cC ssunsn2 cB cA wss cA cB wss wa cA cB wceq cB cC csn cun cA wss cA
      cB cC csn cun wss wa cA cB cC csn cun wceq cB cA wss cA cB wss wa cA cB
      wss cB cA wss wa cA cB wceq cB cA wss cA cB wss ancom cA cB eqss bitr4i
      cB cC csn cun cA wss cA cB cC csn cun wss wa cA cB cC csn cun wss cB cC
      csn cun cA wss wa cA cB cC csn cun wceq cB cC csn cun cA wss cA cB cC csn
      cun wss ancom cA cB cC csn cun eqss bitr4i orbi12i bitri $.

    $( Two ways to express that a nonempty set equals a singleton.
       (Contributed by NM, 15-Dec-2007.) $)
    eqsn $p |- ( A =/= (/) -> ( A = { B } <-> A. x e. A x = B ) ) $=
      cA c0 wne cA cB csn wceq cA cB csn wss vx cv cB wceq vx cA wral cA c0 wne
      cA cB csn wceq cA cB csn wss cA cB csn eqimss cA cB csn wss cA c0 wne cA
      cB csn wceq cA c0 wne cA c0 wceq wn cA cB csn wss cA cB csn wceq cA c0
      df-ne cA cB csn wss cA c0 wceq cA cB csn wceq cA cB csn wss cA c0 wceq cA
      cB csn wceq wo cA cB sssn biimpi ord syl5bi com12 impbid2 cA cB csn wss
      vx cv cB csn wcel vx cA wral vx cv cB wceq vx cA wral vx cA cB csn dfss3
      vx cv cB csn wcel vx cv cB wceq vx cA vx cB elsn ralbii bitri syl6bb $.
  $}

  ${
    $( Possible values for a set sandwiched between another set and it plus a
       singleton.  (Contributed by Mario Carneiro, 2-Jul-2016.) $)
    ssunpr $p |- ( ( B C_ A /\ A C_ ( B u. { C , D } ) ) <->
      ( ( A = B \/ A = ( B u. { C } ) ) \/
        ( A = ( B u. { D } ) \/ A = ( B u. { C , D } ) ) ) ) $=
      cB cA wss cA cB cC cD cpr cun wss wa cB cA wss cA cB cC csn cun cD csn
      cun wss wa cB cA wss cA cB cC csn cun wss wa cB cD csn cun cA wss cA cB
      cC csn cun cD csn cun wss wa wo cA cB wceq cA cB cC csn cun wceq wo cA cB
      cD csn cun wceq cA cB cC cD cpr cun wceq wo wo cA cB cC cD cpr cun wss cA
      cB cC csn cun cD csn cun wss cB cA wss cB cC cD cpr cun cB cC csn cun cD
      csn cun cA cB cC cD cpr cun cB cC csn cD csn cun cun cB cC csn cun cD csn
      cun cC cD cpr cC csn cD csn cun cB cC cD df-pr uneq2i cB cC csn cD csn
      unass eqtr4i sseq2i anbi2i cA cB cB cC csn cun cD ssunsn2 cB cA wss cA cB
      cC csn cun wss wa cA cB wceq cA cB cC csn cun wceq wo cB cD csn cun cA
      wss cA cB cC csn cun cD csn cun wss wa cA cB cD csn cun wceq cA cB cC cD
      cpr cun wceq wo cA cB cC ssunsn cB cD csn cun cA wss cA cB cC csn cun cD
      csn cun wss wa cB cD csn cun cA wss cA cB cD csn cun cC csn cun wss wa cA
      cB cD csn cun wceq cA cB cD csn cun cC csn cun wceq wo cA cB cD csn cun
      wceq cA cB cC cD cpr cun wceq wo cA cB cC csn cun cD csn cun wss cA cB cD
      csn cun cC csn cun wss cB cD csn cun cA wss cB cC csn cun cD csn cun cB
      cD csn cun cC csn cun cA cB cC csn cD csn un23 sseq2i anbi2i cA cB cD csn
      cun cC ssunsn cA cB cD csn cun cC csn cun wceq cA cB cC cD cpr cun wceq
      cA cB cD csn cun wceq cB cD csn cun cC csn cun cB cC cD cpr cun cA cB cC
      cD cpr cun cB cC csn cun cD csn cun cB cD csn cun cC csn cun cB cC cD cpr
      cun cB cC csn cD csn cun cun cB cC csn cun cD csn cun cC cD cpr cC csn cD
      csn cun cB cC cD df-pr uneq2i cB cC csn cD csn unass eqtr4i cB cC csn cD
      csn un23 eqtr2i eqeq2i orbi2i 3bitri orbi12i 3bitri $.

    $( The subsets of a pair.  (Contributed by NM, 16-Mar-2006.)  (Proof
       shortened by Mario Carneiro, 2-Jul-2016.) $)
    sspr $p |- ( A C_ { B , C } <->
     ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) ) $=
      cA cB cC cpr wss c0 cA wss cA c0 cB cC cpr cun wss wa cA c0 wceq cA c0 cB
      csn cun wceq wo cA c0 cC csn cun wceq cA c0 cB cC cpr cun wceq wo wo cA
      c0 wceq cA cB csn wceq wo cA cC csn wceq cA cB cC cpr wceq wo wo cA cB cC
      cpr wss cA c0 cB cC cpr cun wss c0 cA wss cA c0 cB cC cpr cun wss wa c0
      cB cC cpr cun cB cC cpr cA c0 cB cC cpr cun cB cC cpr c0 cun cB cC cpr c0
      cB cC cpr uncom cB cC cpr un0 eqtri sseq2i c0 cA wss cA c0 cB cC cpr cun
      wss cA 0ss biantrur bitr3i cA c0 cB cC ssunpr cA c0 wceq cA c0 cB csn cun
      wceq wo cA c0 wceq cA cB csn wceq wo cA c0 cC csn cun wceq cA c0 cB cC
      cpr cun wceq wo cA cC csn wceq cA cB cC cpr wceq wo cA c0 cB csn cun wceq
      cA cB csn wceq cA c0 wceq c0 cB csn cun cB csn cA c0 cB csn cun cB csn c0
      cun cB csn c0 cB csn uncom cB csn un0 eqtri eqeq2i orbi2i cA c0 cC csn
      cun wceq cA cC csn wceq cA c0 cB cC cpr cun wceq cA cB cC cpr wceq c0 cC
      csn cun cC csn cA c0 cC csn cun cC csn c0 cun cC csn c0 cC csn uncom cC
      csn un0 eqtri eqeq2i c0 cB cC cpr cun cB cC cpr cA c0 cB cC cpr cun cB cC
      cpr c0 cun cB cC cpr c0 cB cC cpr uncom cB cC cpr un0 eqtri eqeq2i
      orbi12i orbi12i 3bitri $.

    $( The subsets of a triple.  (Contributed by Mario Carneiro,
       2-Jul-2016.) $)
    sstp $p |- ( A C_ { B , C , D } <->
      ( ( ( A = (/) \/ A = { B } ) \/ ( A = { C } \/ A = { B , C } ) ) \/
        ( ( A = { D } \/ A = { B , D } ) \/
          ( A = { C , D } \/ A = { B , C , D } ) ) ) ) $=
      cA cB cC cD ctp wss cA cB cC cpr cD csn cun wss c0 cA wss cA cB cC cpr cD
      csn cun wss wa cA c0 wceq cA cB csn wceq wo cA cC csn wceq cA cB cC cpr
      wceq wo wo cA cD csn wceq cA cB cD cpr wceq wo cA cC cD cpr wceq cA cB cC
      cD ctp wceq wo wo wo cB cC cD ctp cB cC cpr cD csn cun cA cB cC cD df-tp
      sseq2i c0 cA wss cA cB cC cpr cD csn cun wss cA 0ss biantrur c0 cA wss cA
      cB cC cpr cD csn cun wss wa c0 cA wss cA cB cC cpr wss wa c0 cD csn cun
      cA wss cA cB cC cpr cD csn cun wss wa wo cA c0 wceq cA cB csn wceq wo cA
      cC csn wceq cA cB cC cpr wceq wo wo cA cD csn wceq cA cB cD cpr wceq wo
      cA cC cD cpr wceq cA cB cC cD ctp wceq wo wo wo cA c0 cB cC cpr cD
      ssunsn2 c0 cA wss cA cB cC cpr wss wa cA c0 wceq cA cB csn wceq wo cA cC
      csn wceq cA cB cC cpr wceq wo wo c0 cD csn cun cA wss cA cB cC cpr cD csn
      cun wss wa cA cD csn wceq cA cB cD cpr wceq wo cA cC cD cpr wceq cA cB cC
      cD ctp wceq wo wo c0 cA wss cA cB cC cpr wss wa cA cB cC cpr wss cA c0
      wceq cA cB csn wceq wo cA cC csn wceq cA cB cC cpr wceq wo wo c0 cA wss
      cA cB cC cpr wss cA 0ss biantrur cA cB cC sspr bitr3i c0 cD csn cun cA
      wss cA cB cC cpr cD csn cun wss wa cD csn cA wss cA cD csn cB cC cpr cun
      wss wa cA cD csn wceq cA cD csn cB csn cun wceq wo cA cD csn cC csn cun
      wceq cA cD csn cB cC cpr cun wceq wo wo cA cD csn wceq cA cB cD cpr wceq
      wo cA cC cD cpr wceq cA cB cC cD ctp wceq wo wo c0 cD csn cun cA wss cD
      csn cA wss cA cB cC cpr cD csn cun wss cA cD csn cB cC cpr cun wss c0 cD
      csn cun cD csn cA c0 cD csn cun cD csn c0 cun cD csn c0 cD csn uncom cD
      csn un0 eqtri sseq1i cB cC cpr cD csn cun cD csn cB cC cpr cun cA cB cC
      cpr cD csn uncom sseq2i anbi12i cA cD csn cB cC ssunpr cA cD csn wceq cA
      cD csn cB csn cun wceq wo cA cD csn wceq cA cB cD cpr wceq wo cA cD csn
      cC csn cun wceq cA cD csn cB cC cpr cun wceq wo cA cC cD cpr wceq cA cB
      cC cD ctp wceq wo cA cD csn cB csn cun wceq cA cB cD cpr wceq cA cD csn
      wceq cD csn cB csn cun cB cD cpr cA cD csn cB csn cun cB csn cD csn cun
      cB cD cpr cD csn cB csn uncom cB cD df-pr eqtr4i eqeq2i orbi2i cA cD csn
      cC csn cun wceq cA cC cD cpr wceq cA cD csn cB cC cpr cun wceq cA cB cC
      cD ctp wceq cD csn cC csn cun cC cD cpr cA cD csn cC csn cun cC csn cD
      csn cun cC cD cpr cD csn cC csn uncom cC cD df-pr eqtr4i eqeq2i cD csn cB
      cC cpr cun cB cC cD ctp cA cB cC cD ctp cB cC cpr cD csn cun cD csn cB cC
      cpr cun cB cC cD df-tp cB cC cpr cD csn uncom eqtr2i eqeq2i orbi12i
      orbi12i 3bitri orbi12i bitri 3bitri $.
  $}

  ${
    $d A x $.  $d B x $.  $d C x $.  $d D x $.
    tpss.1 $e |- A e. _V $.
    tpss.2 $e |- B e. _V $.
    tpss.3 $e |- C e. _V $.
    $( A triplet of elements of a class is a subset of the class.  (Contributed
       by NM, 9-Apr-1994.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    tpss $p |- ( ( A e. D /\ B e. D /\ C e. D ) <-> { A , B , C } C_ D ) $=
      cA cB cpr cD wss cC csn cD wss wa cA cB cpr cC csn cun cD wss cA cD wcel
      cB cD wcel cC cD wcel w3a cA cB cC ctp cD wss cA cB cpr cC csn cD unss cA
      cD wcel cB cD wcel cC cD wcel w3a cA cD wcel cB cD wcel wa cC cD wcel wa
      cA cB cpr cD wss cC csn cD wss wa cA cD wcel cB cD wcel cC cD wcel df-3an
      cA cD wcel cB cD wcel wa cA cB cpr cD wss cC cD wcel cC csn cD wss cA cB
      cD tpss.1 tpss.2 prss cC cD tpss.3 snss anbi12i bitri cA cB cC ctp cA cB
      cpr cC csn cun cD cA cB cC df-tp sseq1i 3bitr4i $.
  $}

  ${
    sneqr.1 $e |- A e. _V $.
    $( If the singletons of two sets are equal, the two sets are equal.  Part
       of Exercise 4 of [TakeutiZaring] p. 15.  (Contributed by NM,
       27-Aug-1993.) $)
    sneqr $p |- ( { A } = { B } -> A = B ) $=
      cA csn cB csn wceq cA cB csn wcel cA cB wceq cA csn cB csn wceq cA cA csn
      wcel cA cB csn wcel cA sneqr.1 snid cA csn cB csn cA eleq2 mpbii cA cB
      sneqr.1 elsnc sylib $.

    $( If a singleton is a subset of another, their members are equal.
       (Contributed by NM, 28-May-2006.) $)
    snsssn $p |- ( { A } C_ { B } -> A = B ) $=
      cA csn cB csn wss cA csn c0 wceq cA csn cB csn wceq wo cA cB wceq cA csn
      cB sssn cA csn c0 wceq cA cB wceq cA csn cB csn wceq cA csn c0 wceq cA cB
      wceq cA csn c0 wne cA csn c0 wceq wn cA sneqr.1 snnz cA csn c0 df-ne mpbi
      pm2.21i cA cB sneqr.1 sneqr jaoi sylbi $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Closed form of ~ sneqr .  (Contributed by Scott Fenton, 1-Apr-2011.) $)
    sneqrg $p |- ( A e. V -> ( { A } = { B } -> A = B ) ) $=
      vx cv csn cB csn wceq vx cv cB wceq wi cA csn cB csn wceq cA cB wceq wi
      vx cA cV vx cv cA wceq vx cv csn cB csn wceq cA csn cB csn wceq vx cv cB
      wceq cA cB wceq vx cv cA wceq vx cv csn cA csn cB csn vx cv cA sneq
      eqeq1d vx cv cA cB eqeq1 imbi12d vx cv cB vx vex sneqr vtoclg $.

  $}

  $( Two singletons of sets are equal iff their elements are equal.
     (Contributed by Scott Fenton, 16-Apr-2012.) $)
  sneqbg $p |- ( A e. V -> ( { A } = { B } <-> A = B ) ) $=
    cA cV wcel cA csn cB csn wceq cA cB wceq cA cB cV sneqrg cA cB sneq impbid1
    $.

  ${
    $d x A $.
    $( The singleton of a class is a subset of its power class.  (Contributed
       by NM, 5-Aug-1993.) $)
    snsspw $p |- { A } C_ ~P A $=
      vx cA csn cA cpw vx cv cA wceq vx cv cA wss vx cv cA csn wcel vx cv cA
      cpw wcel vx cv cA eqimss vx cA elsn vx cv cA wss vx cA cpw vx cA df-pw
      abeq2i 3imtr4i ssriv $.
  $}


  ${
    $d x A $.  $d x B $.  $d x C $.
    prsspw.1 $e |- A e. _V $.
    prsspw.2 $e |- B e. _V $.
    $( An unordered pair belongs to the power class of a class iff each member
       belongs to the class.  (Contributed by NM, 10-Dec-2003.)  (Proof
       shortened by Andrew Salmon, 26-Jun-2011.) $)
    prsspw $p |- ( { A , B } C_ ~P C <-> ( A C_ C /\ B C_ C ) ) $=
      cA cB cpr cC cpw wss cA cC cpw wcel cB cC cpw wcel wa cA cC wss cB cC wss
      wa cA cB cC cpw prsspw.1 prsspw.2 prss cA cC cpw wcel cA cC wss cB cC cpw
      wcel cB cC wss cA cC prsspw.1 elpw cB cC prsspw.2 elpw anbi12i bitr3i $.
  $}

  ${
    preqr1.1 $e |- A e. _V $.
    preqr1.2 $e |- B e. _V $.
    $( Reverse equality lemma for unordered pairs.  If two unordered pairs have
       the same second element, the first elements are equal.  (Contributed by
       NM, 18-Oct-1995.) $)
    preqr1 $p |- ( { A , C } = { B , C } -> A = B ) $=
      cA cC cpr cB cC cpr wceq cA cB wceq cA cC wceq cB cA wceq cB cC wceq cA
      cC cpr cB cC cpr wceq cA cB cC cpr wcel cA cB wceq cA cC wceq wo cA cC
      cpr cB cC cpr wceq cA cA cC cpr wcel cA cB cC cpr wcel cA cC preqr1.1
      prid1 cA cC cpr cB cC cpr cA eleq2 mpbii cA cB cC preqr1.1 elpr sylib cA
      cC cpr cB cC cpr wceq cB cA cC cpr wcel cB cA wceq cB cC wceq wo cA cC
      cpr cB cC cpr wceq cB cA cC cpr wcel cB cB cC cpr wcel cB cC preqr1.2
      prid1 cA cC cpr cB cC cpr cB eleq2 mpbiri cB cA cC preqr1.2 elpr sylib cA
      cB eqcom cA cC cB eqeq2 oplem1 $.
  $}

  ${
    preqr2.1 $e |- A e. _V $.
    preqr2.2 $e |- B e. _V $.
    $( Reverse equality lemma for unordered pairs.  If two unordered pairs have
       the same first element, the second elements are equal.  (Contributed by
       NM, 5-Aug-1993.) $)
    preqr2 $p |- ( { C , A } = { C , B } -> A = B ) $=
      cC cA cpr cC cB cpr wceq cA cC cpr cB cC cpr wceq cA cB wceq cC cA cpr cA
      cC cpr cC cB cpr cB cC cpr cC cA prcom cC cB prcom eqeq12i cA cB cC
      preqr2.1 preqr2.2 preqr1 sylbi $.
  $}

  ${
    preq12b.1 $e |- A e. _V $.
    preq12b.2 $e |- B e. _V $.
    preq12b.3 $e |- C e. _V $.
    preq12b.4 $e |- D e. _V $.
    $( Equality relationship for two unordered pairs.  (Contributed by NM,
       17-Oct-1996.) $)
    preq12b $p |- ( { A , B } = { C , D } <->
                   ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) $=
      cA cB cpr cC cD cpr wceq cA cC wceq cB cD wceq wa cA cD wceq cB cC wceq
      wa wo cA cB cpr cC cD cpr wceq cA cC wceq cA cD wceq wo cA cC wceq cB cD
      wceq wa cA cD wceq cB cC wceq wa wo cA cB cpr cC cD cpr wceq cA cC cD cpr
      wcel cA cC wceq cA cD wceq wo cA cB cpr cC cD cpr wceq cA cA cB cpr wcel
      cA cC cD cpr wcel cA cB preq12b.1 prid1 cA cB cpr cC cD cpr cA eleq2
      mpbii cA cC cD preq12b.1 elpr sylib cA cB cpr cC cD cpr wceq cA cC wceq
      cA cC wceq cB cD wceq wa cA cD wceq cA cD wceq cB cC wceq wa cA cB cpr cC
      cD cpr wceq cA cC wceq cB cD wceq cA cC wceq cA cB cpr cC cD cpr wceq cB
      cD wceq cA cC wceq cA cB cpr cC cD cpr wceq cC cB cpr cC cD cpr wceq cB
      cD wceq cA cC wceq cA cB cpr cC cB cpr cC cD cpr cA cC cB preq1 eqeq1d cB
      cD cC preq12b.2 preq12b.4 preqr2 syl6bi com12 ancld cA cB cpr cC cD cpr
      wceq cA cD wceq cB cC wceq cA cB cpr cC cD cpr wceq cA cB cpr cD cC cpr
      wceq cA cD wceq cB cC wceq wi cC cD cpr cD cC cpr cA cB cpr cC cD prcom
      eqeq2i cA cD wceq cA cB cpr cD cC cpr wceq cB cC wceq cA cD wceq cA cB
      cpr cD cC cpr wceq cD cB cpr cD cC cpr wceq cB cC wceq cA cD wceq cA cB
      cpr cD cB cpr cD cC cpr cA cD cB preq1 eqeq1d cB cC cD preq12b.2
      preq12b.3 preqr2 syl6bi com12 sylbi ancld orim12d mpd cA cC wceq cB cD
      wceq wa cA cB cpr cC cD cpr wceq cA cD wceq cB cC wceq wa cA cB cC cD
      preq12 cA cD wceq cB cC wceq cA cB cpr cB cD cpr cC cD cpr cA cD wceq cA
      cB cpr cD cB cpr cB cD cpr cA cD cB preq1 cD cB prcom syl6eq cB cC cD
      preq1 sylan9eq jaoi impbii $.

    $( Equality of two unordered pairs.  (Contributed by NM, 17-Oct-1996.) $)
    prel12 $p |- ( -. A = B -> ( { A , B } = { C , D } <->
                   ( A e. { C , D } /\ B e. { C , D } ) ) ) $=
      cA cB wceq wn cA cB cpr cC cD cpr wceq cA cC cD cpr wcel cB cC cD cpr
      wcel wa cA cB cpr cC cD cpr wceq cA cC cD cpr wcel cB cC cD cpr wcel cA
      cB cpr cC cD cpr wceq cA cA cB cpr wcel cA cC cD cpr wcel cA cB preq12b.1
      prid1 cA cB cpr cC cD cpr cA eleq2 mpbii cA cB cpr cC cD cpr wceq cB cA
      cB cpr wcel cB cC cD cpr wcel cA cB preq12b.2 prid2 cA cB cpr cC cD cpr
      cB eleq2 mpbii jca cA cB wceq wn cA cC cD cpr wcel cB cC cD cpr wcel cA
      cB cpr cC cD cpr wceq cA cC cD cpr wcel cA cC wceq cA cD wceq wo cA cB
      wceq wn cB cC cD cpr wcel cA cB cpr cC cD cpr wceq wi cA cC cD preq12b.1
      elpr cA cB wceq wn cA cC wceq cA cD wceq wo cB cC cD cpr wcel cA cB cpr
      cC cD cpr wceq wi cA cB wceq wn cA cC wceq cA cD wceq wo wa cB cD wceq cB
      cC wceq wo cA cC wceq cB cD wceq wa cA cD wceq cB cC wceq wa wo cB cC cD
      cpr wcel cA cB cpr cC cD cpr wceq cA cB wceq wn cA cC wceq cA cD wceq wo
      wa cB cD wceq cA cC wceq cB cD wceq wa cB cC wceq cA cD wceq cB cC wceq
      wa cA cB wceq wn cA cC wceq cA cD wceq wo wa cB cD wceq cA cC wceq cA cB
      wceq wn cA cC wceq cA cD wceq wo cB cD wceq cA cC wceq wi cB cD wceq cA
      cB wceq wn cA cC wceq cA cD wceq wo cA cC wceq cB cD wceq cA cB wceq wn
      cA cD wceq wn cA cC wceq cA cD wceq wo cA cC wceq wi cB cD wceq cA cB
      wceq cA cD wceq cB cD cA eqeq2 notbid cA cD wceq cA cC wceq orel2 syl6bi
      com3l imp ancrd cA cB wceq wn cA cC wceq cA cD wceq wo wa cB cC wceq cA
      cD wceq cA cB wceq wn cA cC wceq cA cD wceq wo cB cC wceq cA cD wceq wi
      cB cC wceq cA cB wceq wn cA cC wceq cA cD wceq wo cA cD wceq cB cC wceq
      cA cB wceq wn cA cC wceq wn cA cC wceq cA cD wceq wo cA cD wceq wi cB cC
      wceq cA cB wceq cA cC wceq cB cC cA eqeq2 notbid cA cC wceq cA cD wceq
      orel1 syl6bi com3l imp ancrd orim12d cB cC cD cpr wcel cB cC wceq cB cD
      wceq wo cB cD wceq cB cC wceq wo cB cC cD preq12b.2 elpr cB cC wceq cB cD
      wceq orcom bitri cA cB cC cD preq12b.1 preq12b.2 preq12b.3 preq12b.4
      preq12b 3imtr4g ex syl5bi imp3a impbid2 $.

    $( A way to represent ordered pairs using unordered pairs with distinct
       members.  (Contributed by NM, 27-Mar-2007.) $)
    opthpr $p |- ( A =/= D ->
                 ( { A , B } = { C , D } <-> ( A = C /\ B = D ) ) ) $=
      cA cB cpr cC cD cpr wceq cA cC wceq cB cD wceq wa cA cD wceq cB cC wceq
      wa wo cA cD wne cA cC wceq cB cD wceq wa cA cB cC cD preq12b.1 preq12b.2
      preq12b.3 preq12b.4 preq12b cA cD wne cA cC wceq cB cD wceq wa cA cD wceq
      cB cC wceq wa wo cA cC wceq cB cD wceq wa cA cD wne cA cC wceq cB cD wceq
      wa cA cC wceq cB cD wceq wa cA cD wceq cB cC wceq wa cA cD wne cA cC wceq
      cB cD wceq wa idd cA cD wne cA cD wceq cB cC wceq cA cC wceq cB cD wceq
      wa cA cD wne cA cD wceq wn cA cD wceq cB cC wceq cA cC wceq cB cD wceq wa
      wi wi cA cD df-ne cA cD wceq cB cC wceq cA cC wceq cB cD wceq wa wi
      pm2.21 sylbi imp3a jaod cA cC wceq cB cD wceq wa cA cD wceq cB cC wceq wa
      orc impbid1 syl5bb $.
  $}

  ${
    $d A x y z w $.  $d B x y z w $.  $d C x y z w $.  $d D x y z w $.
    $d V x y z w $.  $d W x y z w $.  $d X x y z w $.  $d Y x y z w $.
    $( Closed form of ~ preq12b .  (Contributed by Scott Fenton,
       28-Mar-2014.) $)
    preq12bg $p |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) ->
       ( { A , B } = { C , D } <->
         ( ( A = C /\ B = D ) \/ ( A = D /\ B = C ) ) ) ) $=
      cA cV wcel cB cW wcel wa cC cX wcel cD cY wcel cA cB cpr cC cD cpr wceq
      cA cC wceq cB cD wceq wa cA cD wceq cB cC wceq wa wo wb cA cV wcel cB cW
      wcel cC cX wcel cD cY wcel cA cB cpr cC cD cpr wceq cA cC wceq cB cD wceq
      wa cA cD wceq cB cC wceq wa wo wb wi cD cY wcel vx cv vy cv cpr vz cv cD
      cpr wceq vx vz weq vy cv cD wceq wa vx cv cD wceq vy vz weq wa wo wb wi
      cD cY wcel cA vy cv cpr vz cv cD cpr wceq cA vz cv wceq vy cv cD wceq wa
      cA cD wceq vy vz weq wa wo wb wi cD cY wcel cA cB cpr vz cv cD cpr wceq
      cA vz cv wceq cB cD wceq wa cA cD wceq cB vz cv wceq wa wo wb wi cD cY
      wcel cA cB cpr cC cD cpr wceq cA cC wceq cB cD wceq wa cA cD wceq cB cC
      wceq wa wo wb wi vx vy vz cA cB cC cV cW cX vx cv cA wceq vx cv vy cv cpr
      vz cv cD cpr wceq vx vz weq vy cv cD wceq wa vx cv cD wceq vy vz weq wa
      wo wb cA vy cv cpr vz cv cD cpr wceq cA vz cv wceq vy cv cD wceq wa cA cD
      wceq vy vz weq wa wo wb cD cY wcel vx cv cA wceq vx cv vy cv cpr vz cv cD
      cpr wceq cA vy cv cpr vz cv cD cpr wceq vx vz weq vy cv cD wceq wa vx cv
      cD wceq vy vz weq wa wo cA vz cv wceq vy cv cD wceq wa cA cD wceq vy vz
      weq wa wo vx cv cA wceq vx cv vy cv cpr cA vy cv cpr vz cv cD cpr vx cv
      cA vy cv preq1 eqeq1d vx cv cA wceq vx vz weq vy cv cD wceq wa cA vz cv
      wceq vy cv cD wceq wa vx cv cD wceq vy vz weq wa cA cD wceq vy vz weq wa
      vx cv cA wceq vx vz weq cA vz cv wceq vy cv cD wceq vx cv cA vz cv eqeq1
      anbi1d vx cv cA wceq vx cv cD wceq cA cD wceq vy vz weq vx cv cA cD eqeq1
      anbi1d orbi12d bibi12d imbi2d vy cv cB wceq cA vy cv cpr vz cv cD cpr
      wceq cA vz cv wceq vy cv cD wceq wa cA cD wceq vy vz weq wa wo wb cA cB
      cpr vz cv cD cpr wceq cA vz cv wceq cB cD wceq wa cA cD wceq cB vz cv
      wceq wa wo wb cD cY wcel vy cv cB wceq cA vy cv cpr vz cv cD cpr wceq cA
      cB cpr vz cv cD cpr wceq cA vz cv wceq vy cv cD wceq wa cA cD wceq vy vz
      weq wa wo cA vz cv wceq cB cD wceq wa cA cD wceq cB vz cv wceq wa wo vy
      cv cB wceq cA vy cv cpr cA cB cpr vz cv cD cpr vy cv cB cA preq2 eqeq1d
      vy cv cB wceq cA vz cv wceq vy cv cD wceq wa cA vz cv wceq cB cD wceq wa
      cA cD wceq vy vz weq wa cA cD wceq cB vz cv wceq wa vy cv cB wceq vy cv
      cD wceq cB cD wceq cA vz cv wceq vy cv cB cD eqeq1 anbi2d vy cv cB wceq
      vy vz weq cB vz cv wceq cA cD wceq vy cv cB vz cv eqeq1 anbi2d orbi12d
      bibi12d imbi2d vz cv cC wceq cA cB cpr vz cv cD cpr wceq cA vz cv wceq cB
      cD wceq wa cA cD wceq cB vz cv wceq wa wo wb cA cB cpr cC cD cpr wceq cA
      cC wceq cB cD wceq wa cA cD wceq cB cC wceq wa wo wb cD cY wcel vz cv cC
      wceq cA cB cpr vz cv cD cpr wceq cA cB cpr cC cD cpr wceq cA vz cv wceq
      cB cD wceq wa cA cD wceq cB vz cv wceq wa wo cA cC wceq cB cD wceq wa cA
      cD wceq cB cC wceq wa wo vz cv cC wceq vz cv cD cpr cC cD cpr cA cB cpr
      vz cv cC cD preq1 eqeq2d vz cv cC wceq cA vz cv wceq cB cD wceq wa cA cC
      wceq cB cD wceq wa cA cD wceq cB vz cv wceq wa cA cD wceq cB cC wceq wa
      vz cv cC wceq cA vz cv wceq cA cC wceq cB cD wceq vz cv cC cA eqeq2
      anbi1d vz cv cC wceq cB vz cv wceq cB cC wceq cA cD wceq vz cv cC cB
      eqeq2 anbi2d orbi12d bibi12d imbi2d cD cY wcel vx cv vy cv cpr vz cv cD
      cpr wceq vx vz weq vy cv cD wceq wa vx cv cD wceq vy vz weq wa wo wb wi
      vx cv cV wcel vy cv cW wcel vz cv cX wcel w3a vx cv vy cv cpr vz cv vw cv
      cpr wceq vx vz weq vy vw weq wa vx vw weq vy vz weq wa wo vx cv vy cv cpr
      vz cv cD cpr wceq vx vz weq vy cv cD wceq wa vx cv cD wceq vy vz weq wa
      wo vw cD cY vw cv cD wceq vz cv vw cv cpr vz cv cD cpr vx cv vy cv cpr vw
      cv cD vz cv preq2 eqeq2d vw cv cD wceq vx vz weq vy vw weq wa vx vz weq
      vy cv cD wceq wa vx vw weq vy vz weq wa vx cv cD wceq vy vz weq wa vw cv
      cD wceq vy vw weq vy cv cD wceq vx vz weq vw cv cD vy cv eqeq2 anbi2d vw
      cv cD wceq vx vw weq vx cv cD wceq vy vz weq vw cv cD vx cv eqeq2 anbi1d
      orbi12d vx cv vy cv vz cv vw cv vx vex vy vex vz vex vw vex preq12b
      vtoclbg a1i vtocl3ga 3expa impr $.
  $}

  ${
    preqsn.1 $e |- A e. _V $.
    preqsn.2 $e |- B e. _V $.
    preqsn.3 $e |- C e. _V $.
    $( Equivalence for a pair equal to a singleton.  (Contributed by NM,
       3-Jun-2008.) $)
    preqsn $p |- ( { A , B } = { C } <-> ( A = B /\ B = C ) ) $=
      cA cB cpr cC csn wceq cA cB cpr cC cC cpr wceq cA cB wceq cB cC wceq wa
      cC csn cC cC cpr cA cB cpr cC dfsn2 eqeq2i cA cB cpr cC cC cpr wceq cA cC
      wceq cB cC wceq wa cA cC wceq cB cC wceq wa wo cA cB wceq cB cC wceq wa
      cA cB cC cC preqsn.1 preqsn.2 preqsn.3 preqsn.3 preq12b cA cC wceq cB cC
      wceq wa cA cC wceq cB cC wceq wa wo cA cC wceq cB cC wceq wa cA cB wceq
      cB cC wceq wa cA cC wceq cB cC wceq wa oridm cA cC wceq cB cC wceq wa cA
      cB wceq cB cC wceq wa cA cC wceq cB cC wceq wa cA cB wceq cB cC wceq cA
      cB cC eqtr3 cA cC wceq cB cC wceq simpr jca cA cB wceq cB cC wceq wa cA
      cC wceq cB cC wceq cA cB cC eqtr cA cB wceq cB cC wceq simpr jca impbii
      bitri bitri bitri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Rewrite ~ df-op using ` if ` .  When both arguments are sets, it reduces
       to the standard Kuratowski definition; otherwise, it is defined to be
       the empty set.  (Contributed by Mario Carneiro, 26-Apr-2015.) $)
    dfopif $p |- <. A , B >. =
      if ( ( A e. _V /\ B e. _V ) , { { A } , { A , B } } , (/) ) $=
      cA cB cop cA cvv wcel cB cvv wcel vx cv cA csn cA cB cpr cpr wcel w3a vx
      cab cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel wa vx cab
      cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif vx cA cB df-op cA
      cvv wcel cB cvv wcel vx cv cA csn cA cB cpr cpr wcel w3a cA cvv wcel cB
      cvv wcel wa vx cv cA csn cA cB cpr cpr wcel wa vx cA cvv wcel cB cvv wcel
      vx cv cA csn cA cB cpr cpr wcel df-3an abbii cA cvv wcel cB cvv wcel wa
      cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel wa vx cab cA
      cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif wceq cA cvv wcel cB
      cvv wcel wa cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif cA csn
      cA cB cpr cpr cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel
      wa vx cab cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 iftrue cA
      cvv wcel cB cvv wcel wa cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr
      cpr wcel wa vx cA csn cA cB cpr cpr cA cvv wcel cB cvv wcel wa vx cv cA
      csn cA cB cpr cpr wcel ibar abbi2dv eqtr2d cA cvv wcel cB cvv wcel wa wn
      cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel wa vx cab c0
      cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif cA cvv wcel cB cvv
      wcel wa wn cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel wa
      vx cab c0 wss cA cvv wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel
      wa vx cab c0 wceq cA cvv wcel cB cvv wcel wa wn cA cvv wcel cB cvv wcel
      wa vx cv cA csn cA cB cpr cpr wcel wa vx c0 cA cvv wcel cB cvv wcel wa wn
      cA cvv wcel cB cvv wcel wa vx cv c0 wcel vx cv cA csn cA cB cpr cpr wcel
      cA cvv wcel cB cvv wcel wa vx cv c0 wcel pm2.21 adantrd abssdv cA cvv
      wcel cB cvv wcel wa vx cv cA csn cA cB cpr cpr wcel wa vx cab ss0 syl cA
      cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 iffalse eqtr4d pm2.61i
      3eqtri $.
  $}

  $( Value of the ordered pair when the arguments are sets.  (Contributed by
     Mario Carneiro, 26-Apr-2015.) $)
  dfopg $p |- ( ( A e. V /\ B e. W ) ->
    <. A , B >. = { { A } , { A , B } } ) $=
    cA cV wcel cA cvv wcel cB cvv wcel cA cB cop cA csn cA cB cpr cpr wceq cB
    cW wcel cA cV elex cB cW elex cA cvv wcel cB cvv wcel wa cA cB cop cA cvv
    wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif cA csn cA cB cpr cpr cA cB
    dfopif cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 iftrue syl5eq
    syl2an $.

  ${
    dfop.1 $e |- A e. _V $.
    dfop.2 $e |- B e. _V $.
    $( Value of an ordered pair when the arguments are sets, with the
       conclusion corresponding to Kuratowski's original definition.
       (Contributed by NM, 25-Jun-1998.) $)
    dfop $p |- <. A , B >. = { { A } , { A , B } } $=
      cA cvv wcel cB cvv wcel cA cB cop cA csn cA cB cpr cpr wceq dfop.1 dfop.2
      cA cB cvv cvv dfopg mp2an $.
  $}

  $( Equality theorem for ordered pairs.  (Contributed by NM, 25-Jun-1998.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)
  opeq1 $p |- ( A = B -> <. A , C >. = <. B , C >. ) $=
    cA cB wceq cA cvv wcel cC cvv wcel wa cA csn cA cC cpr cpr c0 cif cB cvv
    wcel cC cvv wcel wa cB csn cB cC cpr cpr c0 cif cA cC cop cB cC cop cA cB
    wceq cA cvv wcel cC cvv wcel wa cB cvv wcel cC cvv wcel wa cA csn cA cC cpr
    cpr c0 cB csn cB cC cpr cpr c0 cA cB wceq cA cvv wcel cB cvv wcel cC cvv
    wcel cA cB cvv eleq1 anbi1d cA cB wceq cA csn cB csn cA cC cpr cB cC cpr cA
    cB sneq cA cB cC preq1 preq12d cA cB wceq c0 eqidd ifbieq12d cA cC dfopif
    cB cC dfopif 3eqtr4g $.

  $( Equality theorem for ordered pairs.  (Contributed by NM, 25-Jun-1998.)
     (Revised by Mario Carneiro, 26-Apr-2015.) $)
  opeq2 $p |- ( A = B -> <. C , A >. = <. C , B >. ) $=
    cA cB wceq cC cvv wcel cA cvv wcel wa cC csn cC cA cpr cpr c0 cif cC cvv
    wcel cB cvv wcel wa cC csn cC cB cpr cpr c0 cif cC cA cop cC cB cop cA cB
    wceq cC cvv wcel cA cvv wcel wa cC cvv wcel cB cvv wcel wa cC csn cC cA cpr
    cpr c0 cC csn cC cB cpr cpr c0 cA cB wceq cA cvv wcel cB cvv wcel cC cvv
    wcel cA cB cvv eleq1 anbi2d cA cB wceq cC cA cpr cC cB cpr cC csn cA cB cC
    preq2 preq2d cA cB wceq c0 eqidd ifbieq12d cC cA dfopif cC cB dfopif
    3eqtr4g $.

  $( Equality theorem for ordered pairs.  (Contributed by NM, 28-May-1995.) $)
  opeq12 $p |- ( ( A = C /\ B = D ) -> <. A , B >. = <. C , D >. ) $=
    cA cC wceq cB cD wceq cA cB cop cC cB cop cC cD cop cA cC cB opeq1 cB cD cC
    opeq2 sylan9eq $.

  ${
    opeq1i.1 $e |- A = B $.
    $( Equality inference for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)
    opeq1i $p |- <. A , C >. = <. B , C >. $=
      cA cB wceq cA cC cop cB cC cop wceq opeq1i.1 cA cB cC opeq1 ax-mp $.

    $( Equality inference for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)
    opeq2i $p |- <. C , A >. = <. C , B >. $=
      cA cB wceq cC cA cop cC cB cop wceq opeq1i.1 cA cB cC opeq2 ax-mp $.

    ${
      opeq12i.2 $e |- C = D $.
      $( Equality inference for ordered pairs.  (Contributed by NM,
         16-Dec-2006.)  (Proof shortened by Eric Schmidt, 4-Apr-2007.) $)
      opeq12i $p |- <. A , C >. = <. B , D >. $=
        cA cB wceq cC cD wceq cA cC cop cB cD cop wceq opeq1i.1 opeq12i.2 cA cC
        cB cD opeq12 mp2an $.
    $}
  $}

  ${
    opeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)
    opeq1d $p |- ( ph -> <. A , C >. = <. B , C >. ) $=
      wph cA cB wceq cA cC cop cB cC cop wceq opeq1d.1 cA cB cC opeq1 syl $.

    $( Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.) $)
    opeq2d $p |- ( ph -> <. C , A >. = <. C , B >. ) $=
      wph cA cB wceq cC cA cop cC cB cop wceq opeq1d.1 cA cB cC opeq2 syl $.

    opeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for ordered pairs.  (Contributed by NM,
       16-Dec-2006.)  (Proof shortened by Andrew Salmon, 29-Jun-2011.) $)
    opeq12d $p |- ( ph -> <. A , C >. = <. B , D >. ) $=
      wph cA cB wceq cC cD wceq cA cC cop cB cD cop wceq opeq1d.1 opeq12d.2 cA
      cC cB cD opeq12 syl2anc $.
  $}

  $( Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) $)
  oteq1 $p |- ( A = B -> <. A , C , D >. = <. B , C , D >. ) $=
    cA cB wceq cA cC cop cD cop cB cC cop cD cop cA cC cD cotp cB cC cD cotp cA
    cB wceq cA cC cop cB cC cop cD cA cB cC opeq1 opeq1d cA cC cD df-ot cB cC
    cD df-ot 3eqtr4g $.

  $( Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) $)
  oteq2 $p |- ( A = B -> <. C , A , D >. = <. C , B , D >. ) $=
    cA cB wceq cC cA cop cD cop cC cB cop cD cop cC cA cD cotp cC cB cD cotp cA
    cB wceq cC cA cop cC cB cop cD cA cB cC opeq2 opeq1d cC cA cD df-ot cC cB
    cD df-ot 3eqtr4g $.

  $( Equality theorem for ordered triples.  (Contributed by NM, 3-Apr-2015.) $)
  oteq3 $p |- ( A = B -> <. C , D , A >. = <. C , D , B >. ) $=
    cA cB wceq cC cD cop cA cop cC cD cop cB cop cC cD cA cotp cC cD cB cotp cA
    cB cC cD cop opeq2 cC cD cA df-ot cC cD cB df-ot 3eqtr4g $.

  ${
    oteq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    oteq1d $p |- ( ph -> <. A , C , D >. = <. B , C , D >. ) $=
      wph cA cB wceq cA cC cD cotp cB cC cD cotp wceq oteq1d.1 cA cB cC cD
      oteq1 syl $.

    $( Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    oteq2d $p |- ( ph -> <. C , A , D >. = <. C , B , D >. ) $=
      wph cA cB wceq cC cA cD cotp cC cB cD cotp wceq oteq1d.1 cA cB cC cD
      oteq2 syl $.

    $( Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    oteq3d $p |- ( ph -> <. C , D , A >. = <. C , D , B >. ) $=
      wph cA cB wceq cC cD cA cotp cC cD cB cotp wceq oteq1d.1 cA cB cC cD
      oteq3 syl $.

    oteq123d.2 $e |- ( ph -> C = D ) $.
    oteq123d.3 $e |- ( ph -> E = F ) $.
    $( Equality deduction for ordered triples.  (Contributed by Mario Carneiro,
       11-Jan-2017.) $)
    oteq123d $p |- ( ph -> <. A , C , E >. = <. B , D , F >. ) $=
      wph cA cC cE cotp cB cC cE cotp cB cD cE cotp cB cD cF cotp wph cA cB cC
      cE oteq1d.1 oteq1d wph cC cD cB cE oteq123d.2 oteq2d wph cE cF cB cD
      oteq123d.3 oteq3d 3eqtrd $.
  $}

  ${
    nfop.1 $e |- F/_ x A $.
    nfop.2 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for ordered pairs.  (Contributed by
       NM, 14-Nov-1995.) $)
    nfop $p |- F/_ x <. A , B >. $=
      vx cA cB cop cA cvv wcel cB cvv wcel wa cA csn cA cB cpr cpr c0 cif cA cB
      dfopif cA cvv wcel cB cvv wcel wa vx cA csn cA cB cpr cpr c0 cA cvv wcel
      cB cvv wcel vx vx cA cvv nfop.1 nfel1 vx cB cvv nfop.2 nfel1 nfan vx cA
      csn cA cB cpr vx cA nfop.1 nfsn vx cA cB nfop.1 nfop.2 nfpr nfpr vx c0
      nfcv nfif nfcxfr $.
  $}

  ${
    $d z B $.  $d z A $.  $d x z $.
    nfopd.2 $e |- ( ph -> F/_ x A ) $.
    nfopd.3 $e |- ( ph -> F/_ x B ) $.
    $( Deduction version of bound-variable hypothesis builder ~ nfop .  This
       shows how the deduction version of a not-free theorem such as ~ nfop can
       be created from the corresponding not-free inference theorem.
       (Contributed by NM, 4-Feb-2008.) $)
    nfopd $p |- ( ph -> F/_ x <. A , B >. ) $=
      wph vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz cab cop wnfc
      vx cA cB cop wnfc vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz
      cab vz cv cA wcel vx vz nfaba1 vz cv cB wcel vx vz nfaba1 nfop wph vx cA
      wnfc vx cB wnfc vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz
      cab cop wnfc vx cA cB cop wnfc wb nfopd.2 nfopd.3 vx cA wnfc vx cB wnfc
      wa vx vz cv cA wcel vx wal vz cab vz cv cB wcel vx wal vz cab cop cA cB
      cop vx cA wnfc vx cB wnfc vx vx cA nfnfc1 vx cB nfnfc1 nfan vx cA wnfc vx
      cB wnfc wa vz cv cA wcel vx wal vz cab cA vz cv cB wcel vx wal vz cab cB
      vx cA wnfc vz cv cA wcel vx wal vz cab cA wceq vx cB wnfc vx vz cA abidnf
      adantr vx cB wnfc vz cv cB wcel vx wal vz cab cB wceq vx cA wnfc vx vz cB
      abidnf adantl opeq12d nfceqdf syl2anc mpbii $.
  $}

  ${
    opid.1 $e |- A e. _V $.
    $( The ordered pair ` <. A , A >. ` in Kuratowski's representation.
       (Contributed by FL, 28-Dec-2011.) $)
    opid $p |- <. A , A >. = { { A } } $=
      cA csn cA cA cpr cpr cA csn cA csn cpr cA cA cop cA csn csn cA cA cpr cA
      csn cA csn cA csn cA cA cpr cA dfsn2 eqcomi preq2i cA cA opid.1 opid.1
      dfop cA csn dfsn2 3eqtr4i $.
  $}

  ${
    $d B x $.  $d ps x $.
    ralunsn.1 $e |- ( x = B -> ( ph <-> ps ) ) $.
    $( Restricted quantification over the union of a set and a singleton, using
       implicit substitution.  (Contributed by Paul Chapman, 17-Nov-2012.)
       (Revised by Mario Carneiro, 23-Apr-2015.) $)
    ralunsn $p |- ( B e. C -> ( A. x e. ( A u. { B } ) ph <->
                                ( A. x e. A ph /\ ps ) ) ) $=
      wph vx cA cB csn cun wral wph vx cA wral wph vx cB csn wral wa cB cC wcel
      wph vx cA wral wps wa wph vx cA cB csn ralunb cB cC wcel wph vx cB csn
      wral wps wph vx cA wral wph wps vx cB cC ralunsn.1 ralsng anbi2d syl5bb
      $.
  $}

  ${
    $d A x $.  $d B x y $.  $d C x $.  $d ch x $.  $d ps y $.  $d th x $.
    2ralunsn.1 $e |- ( x = B -> ( ph <-> ch ) ) $.
    2ralunsn.2 $e |- ( y = B -> ( ph <-> ps ) ) $.
    2ralunsn.3 $e |- ( x = B -> ( ps <-> th ) ) $.
    $( Double restricted quantification over the union of a set and a
       singleton, using implicit substitution.  (Contributed by Paul Chapman,
       17-Nov-2012.) $)
    2ralunsn $p |- ( B e. C ->
                     ( A. x e. ( A u. { B } ) A. y e. ( A u. { B } ) ph <->
                       ( ( A. x e. A A. y e. A ph /\ A. x e. A ps ) /\
                         ( A. y e. A ch /\ th ) ) ) ) $=
      cB cC wcel wph vy cA cB csn cun wral vx cA cB csn cun wral wph vy cA wral
      wps wa vx cA cB csn cun wral wph vy cA wral vx cA wral wps vx cA wral wa
      wch vy cA wral wth wa wa cB cC wcel wph vy cA cB csn cun wral wph vy cA
      wral wps wa vx cA cB csn cun wph wps vy cA cB cC 2ralunsn.2 ralunsn
      ralbidv cB cC wcel wph vy cA wral wps wa vx cA cB csn cun wral wph vy cA
      wral wps wa vx cA wral wch vy cA wral wth wa wa wph vy cA wral vx cA wral
      wps vx cA wral wa wch vy cA wral wth wa wa wph vy cA wral wps wa wch vy
      cA wral wth wa vx cA cB cC vx cv cB wceq wph vy cA wral wch vy cA wral
      wps wth vx cv cB wceq wph wch vy cA 2ralunsn.1 ralbidv 2ralunsn.3 anbi12d
      ralunsn wph vy cA wral wps wa vx cA wral wph vy cA wral vx cA wral wps vx
      cA wral wa wch vy cA wral wth wa wph vy cA wral wps vx cA r19.26 anbi1i
      syl6bb bitrd $.
  $}

  $( Expansion of an ordered pair when either member is a proper class.
     (Contributed by Mario Carneiro, 26-Apr-2015.) $)
  opprc $p |- ( -. ( A e. _V /\ B e. _V ) -> <. A , B >. = (/) ) $=
    cA cvv wcel cB cvv wcel wa wn cA cB cop cA cvv wcel cB cvv wcel wa cA csn
    cA cB cpr cpr c0 cif c0 cA cB dfopif cA cvv wcel cB cvv wcel wa cA csn cA
    cB cpr cpr c0 iffalse syl5eq $.

  $( Expansion of an ordered pair when the first member is a proper class.  See
     also ~ opprc .  (Contributed by NM, 10-Apr-2004.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) $)
  opprc1 $p |- ( -. A e. _V -> <. A , B >. = (/) ) $=
    cA cvv wcel wn cA cvv wcel cB cvv wcel wa wn cA cB cop c0 wceq cA cvv wcel
    cB cvv wcel wa cA cvv wcel cA cvv wcel cB cvv wcel simpl con3i cA cB opprc
    syl $.

  $( Expansion of an ordered pair when the second member is a proper class.
     See also ~ opprc .  (Contributed by NM, 15-Nov-1994.)  (Revised by Mario
     Carneiro, 26-Apr-2015.) $)
  opprc2 $p |- ( -. B e. _V -> <. A , B >. = (/) ) $=
    cB cvv wcel wn cA cvv wcel cB cvv wcel wa wn cA cB cop c0 wceq cA cvv wcel
    cB cvv wcel wa cB cvv wcel cA cvv wcel cB cvv wcel simpr con3i cA cB opprc
    syl $.

  $( If an ordered pair has an element, then its arguments are sets.
     (Contributed by Mario Carneiro, 26-Apr-2015.) $)
  oprcl $p |- ( C e. <. A , B >. -> ( A e. _V /\ B e. _V ) ) $=
    cC cA cB cop wcel cA cB cop c0 wceq cA cvv wcel cB cvv wcel wa cA cB cop cC
    n0i cA cB opprc nsyl2 $.

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( The power set of a singleton.  (Contributed by NM, 5-Jun-2006.) $)
    pwsn $p |- ~P { A } = { (/) , { A } } $=
      vx cv cA csn wss vx cab vx cv c0 wceq vx cv cA csn wceq wo vx cab cA csn
      cpw c0 cA csn cpr vx cv cA csn wss vx cv c0 wceq vx cv cA csn wceq wo vx
      vx cv cA sssn abbii vx cA csn df-pw vx c0 cA csn dfpr2 3eqtr4i $.

    $d x y $.  $d y A $.
    $( The power set of a singleton (direct proof).  TO DO - should we keep
       this?  (Contributed by NM, 5-Jun-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    pwsnALT $p |- ~P { A } = { (/) , { A } } $=
      vx cv cA csn wss vx cab vx cv c0 wceq vx cv cA csn wceq wo vx cab cA csn
      cpw c0 cA csn cpr vx cv cA csn wss vx cv c0 wceq vx cv cA csn wceq wo vx
      vx cv cA csn wss vx cv c0 wceq vx cv cA csn wceq wo vx cv cA csn wss vx
      cv c0 wceq vx cv cA csn wceq vx cv cA csn wss vx cv c0 wceq wn vx cv cA
      csn wss cA csn vx cv wss wa vx cv cA csn wceq vx cv cA csn wss vx cv c0
      wceq wn cA csn vx cv wss vx cv cA csn wss vy cv vx cv wcel vy cv cA wceq
      wi vy wal vx cv c0 wceq wn cA csn vx cv wss wi vx cv cA csn wss vy cv vx
      cv wcel vy cv cA csn wcel wi vy wal vy cv vx cv wcel vy cv cA wceq wi vy
      wal vy vx cv cA csn dfss2 vy cv vx cv wcel vy cv cA csn wcel wi vy cv vx
      cv wcel vy cv cA wceq wi vy vy cv cA csn wcel vy cv cA wceq vy cv vx cv
      wcel vy cA elsn imbi2i albii bitri vy cv vx cv wcel vy cv cA wceq wi vy
      wal vx cv c0 wceq wn vy cv vx cv wcel vy cv cA wceq wa vy wex cA csn vx
      cv wss vx cv c0 wceq wn vy cv vx cv wcel vy wex vy cv vx cv wcel vy cv cA
      wceq wi vy wal vy cv vx cv wcel vy cv cA wceq wa vy wex vy vx cv neq0 vy
      cv vx cv wcel vy cv cA wceq vy exintr syl5bi vy cv vx cv wcel vy cv cA
      wceq wa vy wex cA vx cv wcel cA csn vx cv wss cA vx cv wcel vy cv cA wceq
      vy cv vx cv wcel wa vy wex vy cv vx cv wcel vy cv cA wceq wa vy wex vy cA
      vx cv df-clel vy cv cA wceq vy cv vx cv wcel vy exancom bitr2i cA vx cv
      snssi sylbi syl6 sylbi anc2li vx cv cA csn eqss syl6ibr orrd vx cv c0
      wceq vx cv cA csn wss vx cv cA csn wceq vx cv c0 wceq vx cv cA csn wss c0
      cA csn wss cA csn 0ss vx cv c0 cA csn sseq1 mpbiri vx cv cA csn eqimss
      jaoi impbii abbii vx cA csn df-pw vx c0 cA csn dfpr2 3eqtr4i $.

    $( The power set of an unordered pair.  (Contributed by NM, 1-May-2009.) $)
    pwpr $p |- ~P { A , B } = ( { (/) , { A } } u. { { B } , { A , B } } ) $=
      vx cA cB cpr cpw c0 cA csn cpr cB csn cA cB cpr cpr cun vx cv cA cB cpr
      wss vx cv c0 cA csn cpr wcel vx cv cB csn cA cB cpr cpr wcel wo vx cv cA
      cB cpr cpw wcel vx cv c0 cA csn cpr cB csn cA cB cpr cpr cun wcel vx cv
      cA cB cpr wss vx cv c0 wceq vx cv cA csn wceq wo vx cv cB csn wceq vx cv
      cA cB cpr wceq wo wo vx cv c0 cA csn cpr wcel vx cv cB csn cA cB cpr cpr
      wcel wo vx cv cA cB sspr vx cv c0 cA csn cpr wcel vx cv c0 wceq vx cv cA
      csn wceq wo vx cv cB csn cA cB cpr cpr wcel vx cv cB csn wceq vx cv cA cB
      cpr wceq wo vx cv c0 cA csn vx vex elpr vx cv cB csn cA cB cpr vx vex
      elpr orbi12i bitr4i vx cv cA cB cpr vx vex elpw vx cv c0 cA csn cpr cB
      csn cA cB cpr cpr elun 3bitr4i eqriv $.

    $( The power set of an unordered triple.  (Contributed by Mario Carneiro,
       2-Jul-2016.) $)
    pwtp $p |- ~P { A , B , C } =
      ( ( { (/) , { A } } u. { { B } , { A , B } } ) u.
        ( { { C } , { A , C } } u. { { B , C } , { A , B , C } } ) ) $=
      vx cA cB cC ctp cpw c0 cA csn cpr cB csn cA cB cpr cpr cun cC csn cA cC
      cpr cpr cB cC cpr cA cB cC ctp cpr cun cun vx cv cA cB cC ctp cpw wcel vx
      cv cA cB cC ctp wss vx cv c0 cA csn cpr cB csn cA cB cpr cpr cun cC csn
      cA cC cpr cpr cB cC cpr cA cB cC ctp cpr cun cun wcel vx cv cA cB cC ctp
      vx vex elpw vx cv c0 cA csn cpr cB csn cA cB cpr cpr cun wcel vx cv cC
      csn cA cC cpr cpr cB cC cpr cA cB cC ctp cpr cun wcel wo vx cv c0 wceq vx
      cv cA csn wceq wo vx cv cB csn wceq vx cv cA cB cpr wceq wo wo vx cv cC
      csn wceq vx cv cA cC cpr wceq wo vx cv cB cC cpr wceq vx cv cA cB cC ctp
      wceq wo wo wo vx cv c0 cA csn cpr cB csn cA cB cpr cpr cun cC csn cA cC
      cpr cpr cB cC cpr cA cB cC ctp cpr cun cun wcel vx cv cA cB cC ctp wss vx
      cv c0 cA csn cpr cB csn cA cB cpr cpr cun wcel vx cv c0 wceq vx cv cA csn
      wceq wo vx cv cB csn wceq vx cv cA cB cpr wceq wo wo vx cv cC csn cA cC
      cpr cpr cB cC cpr cA cB cC ctp cpr cun wcel vx cv cC csn wceq vx cv cA cC
      cpr wceq wo vx cv cB cC cpr wceq vx cv cA cB cC ctp wceq wo wo vx cv c0
      cA csn cpr cB csn cA cB cpr cpr cun wcel vx cv c0 cA csn cpr wcel vx cv
      cB csn cA cB cpr cpr wcel wo vx cv c0 wceq vx cv cA csn wceq wo vx cv cB
      csn wceq vx cv cA cB cpr wceq wo wo vx cv c0 cA csn cpr cB csn cA cB cpr
      cpr elun vx cv c0 cA csn cpr wcel vx cv c0 wceq vx cv cA csn wceq wo vx
      cv cB csn cA cB cpr cpr wcel vx cv cB csn wceq vx cv cA cB cpr wceq wo vx
      cv c0 cA csn vx vex elpr vx cv cB csn cA cB cpr vx vex elpr orbi12i bitri
      vx cv cC csn cA cC cpr cpr cB cC cpr cA cB cC ctp cpr cun wcel vx cv cC
      csn cA cC cpr cpr wcel vx cv cB cC cpr cA cB cC ctp cpr wcel wo vx cv cC
      csn wceq vx cv cA cC cpr wceq wo vx cv cB cC cpr wceq vx cv cA cB cC ctp
      wceq wo wo vx cv cC csn cA cC cpr cpr cB cC cpr cA cB cC ctp cpr elun vx
      cv cC csn cA cC cpr cpr wcel vx cv cC csn wceq vx cv cA cC cpr wceq wo vx
      cv cB cC cpr cA cB cC ctp cpr wcel vx cv cB cC cpr wceq vx cv cA cB cC
      ctp wceq wo vx cv cC csn cA cC cpr vx vex elpr vx cv cB cC cpr cA cB cC
      ctp vx vex elpr orbi12i bitri orbi12i vx cv c0 cA csn cpr cB csn cA cB
      cpr cpr cun cC csn cA cC cpr cpr cB cC cpr cA cB cC ctp cpr cun elun vx
      cv cA cB cC sstp 3bitr4ri bitri eqriv $.
  $}

  ${
    $d x y $.
    $( Compute the power set of the power set of the power set of the empty
       set.  (See also ~ pw0 and ~ pwpw0 .)  (Contributed by NM,
       2-May-2009.) $)
    pwpwpw0 $p |- ~P { (/) , { (/) } } =
                ( { (/) , { (/) } } u. { { { (/) } } , { (/) , { (/) } } } ) $=
      c0 c0 csn pwpr $.
  $}

  ${

    $( The power class of the universe is the universe.  Exercise 4.12(d) of
       [Mendelson] p. 235.  (Contributed by NM, 14-Sep-2003.) $)
    pwv $p |- ~P _V = _V $=
      vx cvv cpw cvv vx cv cvv cpw wcel vx cv cvv wcel vx cv cvv cpw wcel vx cv
      cvv wss vx cv ssv vx cv cvv vx vex elpw mpbir vx vex 2th eqriv $.
  $}



