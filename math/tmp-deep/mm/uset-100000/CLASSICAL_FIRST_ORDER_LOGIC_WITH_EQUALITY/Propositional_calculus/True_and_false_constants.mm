
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical__xor_.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
                True and false constants

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $c T. $.
  $c F. $.

  $( ` T. ` is a wff. $)
  wtru $a wff T. $.

  $( ` F. ` is a wff. $)
  wfal $a wff F. $.

  $( Soundness justification theorem for ~ df-tru .  (Contributed by Mario
     Carneiro, 17-Nov-2013.) $)
  trujust $p |- ( ( ph <-> ph ) <-> ( ps <-> ps ) ) $=
    wph wph wb wps wps wb wph biid wps biid 2th $.

  $( Definition of ` T. ` , a tautology. ` T. ` is a constant true.  In this
     definition ~ biid is used as an antecedent, however, any true wff, such as
     an axiom, can be used in its place.  (Contributed by Anthony Hart,
     13-Oct-2010.) $)
  df-tru $a |- ( T. <-> ( ph <-> ph ) ) $.

  $( Definition of ` F. ` , a contradiction. ` F. ` is a constant false.
     (Contributed by Anthony Hart, 22-Oct-2010.) $)
  df-fal $a |- ( F. <-> -. T. ) $.

  $( ` T. ` is provable.  (Contributed by Anthony Hart, 13-Oct-2010.) $)
  tru $p |- T. $=
    wtru wph wph wb wph biid wph df-tru mpbir $.

  $( ` F. ` is refutable.  (Contributed by Anthony Hart, 22-Oct-2010.)  (Proof
     shortened by Mel L. O'Cat, 11-Mar-2012.) $)
  fal $p |- -. F. $=
    wfal wtru wn wtru tru notnoti df-fal mtbir $.

  ${
    trud.1 $e |- ( T. -> ph ) $.
    $( Eliminate ` T. ` as an antecedent.  (Contributed by Mario Carneiro,
       13-Mar-2014.) $)
    trud $p |- ph $=
      wtru wph tru trud.1 ax-mp $.
  $}

  $( If something is true, it outputs ` T. ` .  (Contributed by Anthony Hart,
     14-Aug-2011.) $)
  tbtru $p |- ( ph <-> ( ph <-> T. ) ) $=
    wtru wph tru tbt $.

  $( If something is not true, it outputs ` F. ` .  (Contributed by Anthony
     Hart, 14-Aug-2011.) $)
  nbfal $p |- ( -. ph <-> ( ph <-> F. ) ) $=
    wfal wph fal nbn $.

  ${
    bitru.1 $e |- ph $.
    $( A theorem is equivalent to truth.  (Contributed by Mario Carneiro,
       9-May-2015.) $)
    bitru $p |- ( ph <-> T. ) $=
      wph wtru bitru.1 tru 2th $.
  $}

  ${
    bifal.1 $e |- -. ph $.
    $( A contradiction is equivalent to falsehood.  (Contributed by Mario
       Carneiro, 9-May-2015.) $)
    bifal $p |- ( ph <-> F. ) $=
      wph wfal bifal.1 fal 2false $.
  $}

  $( ` F. ` implies anything.  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
  falim $p |- ( F. -> ph ) $=
    wfal wph fal pm2.21i $.

  $( ` F. ` implies anything.  (Contributed by Mario Carneiro, 9-Feb-2017.) $)
  falimd $p |- ( ( ph /\ F. ) -> ps ) $=
    wfal wps wph wps falim adantl $.

  $( Anything implies ` T. ` .  (Contributed by FL, 20-Mar-2011.)  (Proof
     shortened by Anthony Hart, 1-Aug-2011.) $)
  a1tru $p |- ( ph -> T. ) $=
    wtru wph tru a1i $.

  $( Given falsum, we can define the negation of a wff ` ph ` as the statement
     that a contradiction follows from assuming ` ph ` .  (Contributed by Mario
     Carneiro, 9-Feb-2017.) $)
  dfnot $p |- ( -. ph <-> ( ph -> F. ) ) $=
    wph wn wph wfal wi wph wfal pm2.21 wph wfal wph wn wph wn id wph wn falim
    ja impbii $.

  ${
    inegd.1 $e |- ( ( ph /\ ps ) -> F. ) $.
    $( Negation introduction rule from natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    inegd $p |- ( ph -> -. ps ) $=
      wph wps wfal wi wps wn wph wps wfal inegd.1 ex wps dfnot sylibr $.
  $}

  ${
    efald.1 $e |- ( ( ph /\ -. ps ) -> F. ) $.
    $( Deduction based on reductio ad absurdum.  (Contributed by Mario
       Carneiro, 9-Feb-2017.) $)
    efald $p |- ( ph -> ps ) $=
      wph wps wph wps wn efald.1 inegd notnotrd $.
  $}

  ${
    pm2.21fal.1 $e |- ( ph -> ps ) $.
    pm2.21fal.2 $e |- ( ph -> -. ps ) $.
    $( If a wff and its negation are provable, then falsum is provable.
       (Contributed by Mario Carneiro, 9-Feb-2017.) $)
    pm2.21fal $p |- ( ph -> F. ) $=
      wph wps wfal pm2.21fal.1 pm2.21fal.2 pm2.21dd $.
  $}


