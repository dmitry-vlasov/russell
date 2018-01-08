
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Abbreviated_conjunction_and_disjunction_of_three_wff_s.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Logical 'nand' (Sheffer stroke)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare connective for alternative denial ('nand'). $)
  $c -/\ $. $( Overlined 'wedge' (read:  'nand') $)

  $( Extend wff definition to include alternative denial ('nand'). $)
  wnan $a wff ( ph -/\ ps ) $.

  $( Define incompatibility, or alternative denial ('not-and' or 'nand').  This
     is also called the Sheffer stroke, represented by a vertical bar, but we
     use a different symbol to avoid ambiguity with other uses of the vertical
     bar.  In the second edition of Principia Mathematica (1927), Russell and
     Whitehead used the Sheffer stroke and suggested it as a replacement for
     the "or" and "not" operations of the first edition.  However, in practice,
     "or" and "not" are more widely used.  After we define the constant true
     ` T. ` ( ~ df-tru ) and the constant false ` F. ` ( ~ df-fal ), we will be
     able to prove these truth table values: ` ( ( T. -/\ T. ) <-> F. ) `
     ( ~ trunantru ), ` ( ( T. -/\ F. ) <-> T. ) ` ( ~ trunanfal ),
     ` ( ( F. -/\ T. ) <-> T. ) ` ( ~ falnantru ), and
     ` ( ( F. -/\ F. ) <-> T. ) ` ( ~ falnanfal ).  Contrast with ` /\ `
     ( ~ df-an ), ` \/ ` ( ~ df-or ), ` -> ` ( ~ wi ), and ` \/_ `
     ( ~ df-xor ) .  (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  df-nan $a |- ( ( ph -/\ ps ) <-> -. ( ph /\ ps ) ) $.

  $( Write 'and' in terms of 'nand'.  (Contributed by Mario Carneiro,
     9-May-2015.) $)
  nanan $p |- ( ( ph /\ ps ) <-> -. ( ph -/\ ps ) ) $=
    wph wps wnan wph wps wa wph wps df-nan con2bii $.

  $( The 'nand' operator commutes.  (Contributed by Mario Carneiro,
     9-May-2015.) $)
  nancom $p |- ( ( ph -/\ ps ) <-> ( ps -/\ ph ) ) $=
    wph wps wa wn wps wph wa wn wph wps wnan wps wph wnan wph wps wa wps wph wa
    wph wps ancom notbii wph wps df-nan wps wph df-nan 3bitr4i $.

  $( Lemma for handling nested 'nand's.  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nannan $p |- ( ( ph -/\ ( ch -/\ ps ) ) <-> ( ph -> ( ch /\ ps ) ) ) $=
    wph wch wps wnan wnan wph wch wps wa wn wa wn wph wch wps wa wi wph wch wps
    wnan wnan wph wch wps wnan wa wph wch wps wa wn wa wph wch wps wnan df-nan
    wch wps wnan wch wps wa wn wph wch wps df-nan anbi2i xchbinx wph wch wps wa
    iman bitr4i $.

  $( Show equivalence between implication and the Nicod version.  To derive
     ~ nic-dfim , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nanim $p |- ( ( ph -> ps ) <-> ( ph -/\ ( ps -/\ ps ) ) ) $=
    wph wps wps wnan wnan wph wps wps wa wi wph wps wi wph wps wps nannan wph
    wps anidmdbi bitr2i $.

  $( Show equivalence between negation and the Nicod version.  To derive
     ~ nic-dfneg , apply ~ nanbi .  (Contributed by Jeff Hoffman,
     19-Nov-2007.) $)
  nannot $p |- ( -. ps <-> ( ps -/\ ps ) ) $=
    wps wps wnan wps wn wps wps wnan wps wps wa wps wps wps df-nan wps anidm
    xchbinx bicomi $.

  $( Show equivalence between the bidirectional and the Nicod version.
     (Contributed by Jeff Hoffman, 19-Nov-2007.) $)
  nanbi $p |- ( ( ph <-> ps ) <->
          ( ( ph -/\ ps ) -/\ ( ( ph -/\ ph ) -/\ ( ps -/\ ps ) ) ) ) $=
    wph wps wa wn wph wn wps wn wa wn wa wn wph wps wa wph wn wps wn wa wo wph
    wps wnan wph wph wnan wps wps wnan wnan wnan wph wps wb wph wps wa wph wn
    wps wn wa pm4.57 wph wps wnan wph wph wnan wps wps wnan wnan wnan wph wps
    wnan wph wph wnan wps wps wnan wnan wa wph wps wa wn wph wn wps wn wa wn wa
    wph wps wnan wph wph wnan wps wps wnan wnan df-nan wph wps wnan wph wps wa
    wn wph wph wnan wps wps wnan wnan wph wn wps wn wa wn wph wps df-nan wph
    wph wnan wps wps wnan wnan wph wph wnan wps wps wnan wa wph wn wps wn wa
    wph wph wnan wps wps wnan df-nan wph wn wph wph wnan wps wn wps wps wnan
    wph nannot wps nannot anbi12i xchbinxr anbi12i xchbinx wph wps dfbi3
    3bitr4ri $.


