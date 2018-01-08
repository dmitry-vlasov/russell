
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Logical__nand__(Sheffer_stroke).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'xor'

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for exclusive disjunction ('xor'). $)
  $c \/_ $. $( Underlined 'vee' (read:  'xor') $)

  $( Extend wff definition to include exclusive disjunction ('xor'). $)
  wxo $a wff ( ph \/_ ps ) $.

  $( Define exclusive disjunction (logical 'xor').  Return true if either the
     left or right, but not both, are true.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. \/_ T. ) <-> F. ) `
     ( ~ truxortru ), ` ( ( T. \/_ F. ) <-> T. ) ` ( ~ truxorfal ),
     ` ( ( F. \/_ T. ) <-> T. ) ` ( ~ falxortru ), and
     ` ( ( F. \/_ F. ) <-> F. ) ` ( ~ falxorfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` -/\ `
     ( ~ df-nan ) .  (Contributed by FL, 22-Nov-2010.) $)
  df-xor $a |- ( ( ph \/_ ps ) <-> -. ( ph <-> ps ) ) $.

  $( Two ways to write XNOR. (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  xnor $p |- ( ( ph <-> ps ) <-> -. ( ph \/_ ps ) ) $=
    wph wps wxo wph wps wb wph wps df-xor con2bii $.

  $( ` \/_ ` is commutative.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  xorcom $p |- ( ( ph \/_ ps ) <-> ( ps \/_ ph ) ) $=
    wph wps wb wn wps wph wb wn wph wps wxo wps wph wxo wph wps wb wps wph wb
    wph wps bicom notbii wph wps df-xor wps wph df-xor 3bitr4i $.

  $( ` \/_ ` is associative.  (Contributed by FL, 22-Nov-2010.)  (Proof
     shortened by Andrew Salmon, 8-Jun-2011.) $)
  xorass $p |- ( ( ( ph \/_ ps ) \/_ ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $=
    wph wps wxo wch wb wn wph wps wch wxo wb wn wph wps wxo wch wxo wph wps wch
    wxo wxo wph wps wxo wch wb wph wps wch wxo wb wph wps wb wn wch wb wph wps
    wch wb wn wb wph wps wxo wch wb wph wps wch wxo wb wph wps wb wch wb wn wph
    wps wch wb wb wn wph wps wb wn wch wb wph wps wch wb wn wb wph wps wb wch
    wb wph wps wch wb wb wph wps wch biass notbii wph wps wb wch nbbn wph wps
    wch wb wb wph wps wch wb wn wb wph wps wch wb pm5.18 con2bii 3bitr4i wph
    wps wxo wph wps wb wn wch wph wps df-xor bibi1i wps wch wxo wps wch wb wn
    wph wps wch df-xor bibi2i 3bitr4i notbii wph wps wxo wch df-xor wph wps wch
    wxo df-xor 3bitr4i $.

  $( This tautology shows that xor is really exclusive.  (Contributed by FL,
     22-Nov-2010.) $)
  excxor $p |- ( ( ph \/_ ps ) <->
       ( ( ph /\ -. ps ) \/ ( -. ph /\ ps ) ) ) $=
    wph wps wxo wph wps wb wn wph wps wn wa wps wph wn wa wo wph wps wn wa wph
    wn wps wa wo wph wps df-xor wph wps xor wps wph wn wa wph wn wps wa wph wps
    wn wa wps wph wn ancom orbi2i 3bitri $.

  $( Two ways to express "exclusive or."  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  xor2 $p |- ( ( ph \/_ ps ) <->
       ( ( ph \/ ps ) /\ -. ( ph /\ ps ) ) ) $=
    wph wps wxo wph wps wb wn wph wps wo wph wps wa wn wa wph wps df-xor wph
    wps nbi2 bitri $.

  $( ` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  xorneg1 $p |- ( ( -. ph \/_ ps ) <-> -. ( ph \/_ ps ) ) $=
    wph wn wps wxo wph wn wps wb wn wph wps wb wph wps wxo wn wph wn wps df-xor
    wph wn wps wb wph wps wb wph wps nbbn con2bii wph wps xnor 3bitr2i $.

  $( ` \/_ ` is negated under negation of one argument.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  xorneg2 $p |- ( ( ph \/_ -. ps ) <-> -. ( ph \/_ ps ) ) $=
    wps wn wph wxo wps wph wxo wn wph wps wn wxo wph wps wxo wn wps wph xorneg1
    wph wps wn xorcom wph wps wxo wps wph wxo wph wps xorcom notbii 3bitr4i $.

  $( ` \/_ ` is unchanged under negation of both arguments.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  xorneg $p |- ( ( -. ph \/_ -. ps ) <-> ( ph \/_ ps ) ) $=
    wph wn wps wn wxo wph wps wn wxo wn wph wps wxo wph wps wn xorneg1 wph wps
    wn wxo wph wps wxo wph wps xorneg2 con2bii bitr4i $.

  ${
    xorbi12.1 $e |- ( ph <-> ps ) $.
    xorbi12.2 $e |- ( ch <-> th ) $.
    $( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    xorbi12i $p |- ( ( ph \/_ ch ) <-> ( ps \/_ th ) ) $=
      wph wch wb wn wps wth wb wn wph wch wxo wps wth wxo wph wch wb wps wth wb
      wph wps wch wth xorbi12.1 xorbi12.2 bibi12i notbii wph wch df-xor wps wth
      df-xor 3bitr4i $.
  $}

  ${
    xor12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    xor12d.2 $e |- ( ph -> ( th <-> ta ) ) $.
    $( Equality property for XOR. (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    xorbi12d $p |- ( ph -> ( ( ps \/_ th ) <-> ( ch \/_ ta ) ) ) $=
      wph wps wth wb wn wch wta wb wn wps wth wxo wch wta wxo wph wps wth wb
      wch wta wb wph wps wch wth wta xor12d.1 xor12d.2 bibi12d notbid wps wth
      df-xor wch wta df-xor 3bitr4g $.
  $}


