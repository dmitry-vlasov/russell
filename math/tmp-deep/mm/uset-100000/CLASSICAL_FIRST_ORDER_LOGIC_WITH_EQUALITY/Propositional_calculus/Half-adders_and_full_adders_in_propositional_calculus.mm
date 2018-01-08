
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Auxiliary_theorems_for_Alan_Sare_s_virtual_deduction_tool,_part_1.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Half-adders and full adders in propositional calculus

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Propositional calculus deals with truth values, which can be interpreted as
  bits. Using this, we can define the half-adder in pure propositional
  calculus, and show its basic properties.

$)

  $c hadd cadd $.
  $c , $.  $( Comma (also used for unordered pair notation later) $)

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  whad $a wff hadd ( ph , ps , ch ) $.

  $( Define the half adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  wcad $a wff cadd ( ph , ps , ch ) $.

  $( Define the half adder (triple XOR).  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  df-had $a |- ( hadd ( ph , ps , ch ) <-> ( ( ph \/_ ps ) \/_ ch ) ) $.

  $( Define the half adder carry, which is true when at least two arguments are
     true.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  df-cad $a |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ch /\ ( ph \/_ ps ) ) ) ) $.

  ${
    hadbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    hadbid.2 $e |- ( ph -> ( th <-> ta ) ) $.
    hadbid.3 $e |- ( ph -> ( et <-> ze ) ) $.
    $( Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    hadbi123d $p |- ( ph ->
      ( hadd ( ps , th , et ) <-> hadd ( ch , ta , ze ) ) ) $=
      wph wps wth wxo wet wxo wch wta wxo wze wxo wps wth wet whad wch wta wze
      whad wph wps wth wxo wch wta wxo wet wze wph wps wch wth wta hadbid.1
      hadbid.2 xorbi12d hadbid.3 xorbi12d wps wth wet df-had wch wta wze df-had
      3bitr4g $.

    $( Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    cadbi123d $p |- ( ph ->
      ( cadd ( ps , th , et ) <-> cadd ( ch , ta , ze ) ) ) $=
      wph wps wth wa wet wps wth wxo wa wo wch wta wa wze wch wta wxo wa wo wps
      wth wet wcad wch wta wze wcad wph wps wth wa wch wta wa wet wps wth wxo
      wa wze wch wta wxo wa wph wps wch wth wta hadbid.1 hadbid.2 anbi12d wph
      wet wze wps wth wxo wch wta wxo hadbid.3 wph wps wch wth wta hadbid.1
      hadbid.2 xorbi12d anbi12d orbi12d wps wth wet df-cad wch wta wze df-cad
      3bitr4g $.
  $}

  ${
    hadbii.1 $e |- ( ph <-> ps ) $.
    hadbii.2 $e |- ( ch <-> th ) $.
    hadbii.3 $e |- ( ta <-> et ) $.
    $( Equality theorem for half adder.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    hadbi123i $p |- ( hadd ( ph , ch , ta ) <-> hadd ( ps , th , et ) ) $=
      wph wch wta whad wps wth wet whad wb wtru wph wps wch wth wta wet wph wps
      wb wtru hadbii.1 a1i wch wth wb wtru hadbii.2 a1i wta wet wb wtru
      hadbii.3 a1i hadbi123d trud $.

    $( Equality theorem for adder carry.  (Contributed by Mario Carneiro,
       4-Sep-2016.) $)
    cadbi123i $p |- ( cadd ( ph , ch , ta ) <-> cadd ( ps , th , et ) ) $=
      wph wch wta wcad wps wth wet wcad wb wtru wph wps wch wth wta wet wph wps
      wb wtru hadbii.1 a1i wch wth wb wtru hadbii.2 a1i wta wet wb wtru
      hadbii.3 a1i cadbi123d trud $.
  $}

  $( Associative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadass $p |- ( hadd ( ph , ps , ch ) <-> ( ph \/_ ( ps \/_ ch ) ) ) $=
    wph wps wch whad wph wps wxo wch wxo wph wps wch wxo wxo wph wps wch df-had
    wph wps wch xorass bitri $.

  $( The half adder is the same as the triple biconditional.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  hadbi $p |- ( hadd ( ph , ps , ch ) <-> ( ( ph <-> ps ) <-> ch ) ) $=
    wph wps wxo wch wxo wph wps wxo wch wb wn wph wps wch whad wph wps wb wch
    wb wph wps wxo wch df-xor wph wps wch df-had wph wps wb wch wb wph wps wxo
    wn wch wb wph wps wxo wch wb wn wph wps wb wph wps wxo wn wch wph wps xnor
    bibi1i wph wps wxo wch nbbn bitri 3bitr4i $.

  $( Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadcoma $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ph , ch ) ) $=
    wph wps wxo wch wxo wps wph wxo wch wxo wph wps wch whad wps wph wch whad
    wph wps wxo wps wph wxo wch wch wph wps xorcom wch biid xorbi12i wph wps
    wch df-had wps wph wch df-had 3bitr4i $.

  $( Commutative law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadcomb $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ph , ch , ps ) ) $=
    wph wps wch wxo wxo wph wch wps wxo wxo wph wps wch whad wph wch wps whad
    wph wph wps wch wxo wch wps wxo wph biid wps wch xorcom xorbi12i wph wps
    wch hadass wph wch wps hadass 3bitr4i $.

  $( Rotation law for triple XOR. (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadrot $p |- ( hadd ( ph , ps , ch ) <-> hadd ( ps , ch , ph ) ) $=
    wph wps wch whad wps wph wch whad wps wch wph whad wph wps wch hadcoma wps
    wph wch hadcomb bitri $.

  $( Write the adder carry in disjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cador $p |- ( cadd ( ph , ps , ch ) <->
    ( ( ph /\ ps ) \/ ( ph /\ ch ) \/ ( ps /\ ch ) ) ) $=
    wph wps wch wcad wph wps wa wch wph wps wxo wa wo wph wps wa wph wch wa wps
    wch wa w3o wph wps wch df-cad wph wps wa wn wch wph wps wxo wa wi wph wps
    wa wn wph wch wa wps wch wa wo wi wph wps wa wch wph wps wxo wa wo wph wps
    wa wph wch wa wps wch wa w3o wph wps wa wn wch wph wps wxo wa wph wch wa
    wps wch wa wo wph wps wa wn wph wps wxo wch wa wph wps wo wch wa wch wph
    wps wxo wa wph wch wa wps wch wa wo wph wps wa wn wph wps wxo wph wps wo
    wch wph wps wxo wph wps wo wph wps wa wn wph wps xor2 rbaib anbi1d wph wps
    wxo wch ancom wph wps wch andir 3bitr3g pm5.74i wph wps wa wch wph wps wxo
    wa df-or wph wps wa wph wch wa wps wch wa w3o wph wps wa wph wch wa wps wch
    wa wo wo wph wps wa wn wph wch wa wps wch wa wo wi wph wps wa wph wch wa
    wps wch wa 3orass wph wps wa wph wch wa wps wch wa wo df-or bitri 3bitr4i
    bitri $.

  $( Write the adder carry in conjunctive normal form.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cadan $p |- ( cadd ( ph , ps , ch ) <->
    ( ( ph \/ ps ) /\ ( ph \/ ch ) /\ ( ps \/ ch ) ) ) $=
    wph wps wa wph wch wa wps wch wa w3o wph wps wo wph wch wo wa wps wch wo wa
    wph wps wch wcad wph wps wo wph wch wo wps wch wo w3a wph wps wa wph wch wa
    wo wps wch wa wo wph wps wo wps wch wo wa wph wch wo wps wch wo wa wa wph
    wps wa wph wch wa wps wch wa w3o wph wps wo wph wch wo wa wps wch wo wa wph
    wps wa wph wch wa wo wps wch wa wo wph wps wa wph wch wa wo wps wo wph wps
    wa wph wch wa wo wch wo wa wph wps wo wps wch wo wa wph wch wo wps wch wo
    wa wa wph wps wa wph wch wa wo wps wch ordi wph wps wa wph wch wa wo wps wo
    wph wps wo wps wch wo wa wph wps wa wph wch wa wo wch wo wph wch wo wps wch
    wo wa wph wch wa wps wo wph wps wo wch wps wo wa wph wps wa wph wch wa wo
    wps wo wph wps wo wps wch wo wa wph wch wps ordir wps wph wch wa wo wps wph
    wps wa wph wch wa wo wo wph wch wa wps wo wph wps wa wph wch wa wo wps wo
    wps wn wph wch wa wi wps wn wph wps wa wph wch wa wo wi wps wph wch wa wo
    wps wph wps wa wph wch wa wo wo wps wn wph wch wa wph wps wa wph wch wa wo
    wps wn wph wps wa wn wph wch wa wph wps wa wph wch wa wo wb wph wps wa wps
    wph wps simpr con3i wph wps wa wph wch wa biorf syl pm5.74i wps wph wch wa
    df-or wps wph wps wa wph wch wa wo df-or 3bitr4i wph wch wa wps orcom wph
    wps wa wph wch wa wo wps orcom 3bitr4i wch wps wo wps wch wo wph wps wo wch
    wps orcom anbi2i 3bitr3i wph wps wa wph wch wa wo wch wo wph wps wa wch wo
    wph wch wo wps wch wo wa wch wph wps wa wo wch wph wps wa wph wch wa wo wo
    wph wps wa wch wo wph wps wa wph wch wa wo wch wo wch wn wph wps wa wi wch
    wn wph wps wa wph wch wa wo wi wch wph wps wa wo wch wph wps wa wph wch wa
    wo wo wch wn wph wps wa wph wps wa wph wch wa wo wch wn wph wch wa wn wph
    wps wa wph wps wa wph wch wa wo wb wph wch wa wch wph wch simpr con3i wph
    wch wa wn wph wps wa wph wch wa wph wps wa wo wph wps wa wph wch wa wo wph
    wch wa wph wps wa biorf wph wch wa wph wps wa orcom syl6bb syl pm5.74i wch
    wph wps wa df-or wch wph wps wa wph wch wa wo df-or 3bitr4i wph wps wa wch
    orcom wph wps wa wph wch wa wo wch orcom 3bitr4i wph wps wch ordir bitr3i
    anbi12i bitri wph wps wa wph wch wa wps wch wa df-3or wph wps wo wph wch wo
    wps wch wo anandir 3bitr4i wph wps wch cador wph wps wo wph wch wo wps wch
    wo df-3an 3bitr4i $.

  $( The half adder distributes over negation.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  hadnot $p |- ( -. hadd ( ph , ps , ch ) <->
    hadd ( -. ph , -. ps , -. ch ) ) $=
    wph wps wxo wch wxo wn wph wn wps wn wxo wch wn wxo wph wps wch whad wn wph
    wn wps wn wch wn whad wph wn wps wn wxo wch wn wxo wph wps wxo wch wn wxo
    wph wps wxo wch wxo wn wph wn wps wn wxo wph wps wxo wch wn wch wn wph wps
    xorneg wch wn biid xorbi12i wph wps wxo wch xorneg2 bitr2i wph wps wch whad
    wph wps wxo wch wxo wph wps wch df-had notbii wph wn wps wn wch wn df-had
    3bitr4i $.

  $( The adder carry distributes over negation.  (Contributed by Mario
     Carneiro, 4-Sep-2016.) $)
  cadnot $p |- ( -. cadd ( ph , ps , ch ) <->
    cadd ( -. ph , -. ps , -. ch ) ) $=
    wph wps wa wph wch wa wps wch wa w3o wn wph wn wps wn wo wph wn wch wn wo
    wps wn wch wn wo w3a wph wps wch wcad wn wph wn wps wn wch wn wcad wph wps
    wa wph wch wa wps wch wa w3o wn wph wps wa wn wph wch wa wn wps wch wa wn
    w3a wph wn wps wn wo wph wn wch wn wo wps wn wch wn wo w3a wph wps wa wph
    wch wa wps wch wa 3ioran wph wps wa wn wph wn wps wn wo wph wch wa wn wph
    wn wch wn wo wps wch wa wn wps wn wch wn wo wph wps ianor wph wch ianor wps
    wch ianor 3anbi123i bitri wph wps wch wcad wph wps wa wph wch wa wps wch wa
    w3o wph wps wch cador notbii wph wn wps wn wch wn cadan 3bitr4i $.

  $( Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadcoma $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ph , ch ) ) $=
    wph wps wa wch wph wps wxo wa wo wps wph wa wch wps wph wxo wa wo wph wps
    wch wcad wps wph wch wcad wph wps wa wps wph wa wch wph wps wxo wa wch wps
    wph wxo wa wph wps ancom wph wps wxo wps wph wxo wch wph wps xorcom anbi2i
    orbi12i wph wps wch df-cad wps wph wch df-cad 3bitr4i $.

  $( Commutative law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadcomb $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ph , ch , ps ) ) $=
    wph wps wa wph wch wa wps wch wa w3o wph wch wa wph wps wa wch wps wa w3o
    wph wps wch wcad wph wch wps wcad wph wps wa wph wch wa wps wch wa w3o wph
    wch wa wph wps wa wps wch wa w3o wph wch wa wph wps wa wch wps wa w3o wph
    wps wa wph wch wa wps wch wa 3orcoma wph wch wa wph wch wa wph wps wa wph
    wps wa wps wch wa wch wps wa wph wch wa biid wph wps wa biid wps wch ancom
    3orbi123i bitri wph wps wch cador wph wch wps cador 3bitr4i $.

  $( Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadrot $p |- ( cadd ( ph , ps , ch ) <-> cadd ( ps , ch , ph ) ) $=
    wph wps wch wcad wps wph wch wcad wps wch wph wcad wph wps wch cadcoma wps
    wph wch cadcomb bitri $.

  $( If one parameter is true, the adder carry is true exactly when at least
     one of the other parameters is true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)
  cad1 $p |- ( ch -> ( cadd ( ph , ps , ch ) <-> ( ph \/ ps ) ) ) $=
    wch wph wps wa wch wph wps wxo wa wo wph wps wa wph wps wxo wo wph wps wch
    wcad wph wps wo wch wch wph wps wxo wa wph wps wxo wph wps wa wch wph wps
    wxo wch wph wps wxo wa wch wph wps wxo ibar bicomd orbi2d wph wps wch
    df-cad wph wps wa wph wps wo wo wph wps wa wph wps wa wn wph wps wo wa wo
    wph wps wo wph wps wa wph wps wxo wo wph wps wa wph wps wo pm5.63 wph wps
    wo wph wps wa wph wps wo wo wph wps wo wph wps wa olc wph wps wa wph wps wo
    wph wps wo wph wph wps wo wps wph wps orc adantr wph wps wo id jaoi impbii
    wph wps wxo wph wps wa wn wph wps wo wa wph wps wa wph wps wxo wph wps wo
    wph wps wa wn wa wph wps wa wn wph wps wo wa wph wps xor2 wph wps wo wph
    wps wa wn ancom bitri orbi2i 3bitr4i 3bitr4g $.

  $( If two parameters are true, the adder carry is true.  (Contributed by
     Mario Carneiro, 4-Sep-2016.) $)
  cad11 $p |- ( ( ph /\ ps ) -> cadd ( ph , ps , ch ) ) $=
    wph wps wa wph wps wa wch wph wps wxo wa wo wph wps wch wcad wph wps wa wch
    wph wps wxo wa orc wph wps wch df-cad sylibr $.

  $( If one parameter is false, the adder carry is true exactly when both of
     the other two parameters are true.  (Contributed by Mario Carneiro,
     8-Sep-2016.) $)
  cad0 $p |- ( -. ch -> ( cadd ( ph , ps , ch ) <-> ( ph /\ ps ) ) ) $=
    wph wps wch wcad wph wps wa wch wph wps wxo wa wo wch wn wph wps wa wph wps
    wch df-cad wch wn wph wps wa wch wph wps wxo wa wo wph wps wa wch wn wph
    wps wa wph wps wa wch wph wps wxo wa wch wn wph wps wa idd wch wn wch wph
    wps wa wph wps wxo wch wph wps wa pm2.21 adantrd jaod wph wps wa wch wph
    wps wxo wa orc impbid1 syl5bb $.

  $( Rotation law for adder carry.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  cadtru $p |- cadd ( T. , T. , ph ) $=
    wtru wtru wtru wtru wph wcad tru tru wtru wtru wph cad11 mp2an $.

  $( If the first parameter is true, the half adder is equivalent to the
     equality of the other two inputs.  (Contributed by Mario Carneiro,
     4-Sep-2016.) $)
  had1 $p |- ( ph -> ( hadd ( ph , ps , ch ) <-> ( ps <-> ch ) ) ) $=
    wph wps wch whad wph wps wch wb wb wph wps wch wb wph wps wch whad wph wps
    wb wch wb wph wps wch wb wb wph wps wch hadbi wph wps wch biass bitri wph
    wph wps wch wb wps wch wb wb wb wph wps wch wb wb wps wch wb wb wph wph wps
    wch wb wps wch wb wb wph id wph wps wch wb biidd 2thd wph wps wch wb wps
    wch wb biass sylibr syl5bb $.

  $( If the first parameter is false, the half adder is equivalent to the XOR
     of the other two inputs.  (Contributed by Mario Carneiro, 4-Sep-2016.) $)
  had0 $p |- ( -. ph -> ( hadd ( ph , ps , ch ) <-> ( ps \/_ ch ) ) ) $=
    wph wn wph wps wch whad wps wch wxo wph wn wph wn wps wn wch wn whad wps wn
    wch wn wb wph wps wch whad wn wps wch wxo wn wph wn wps wn wch wn had1 wph
    wps wch hadnot wps wn wch wn wb wps wch wxo wps wn wch wn wb wn wps wn wch
    wn wxo wps wch wxo wps wn wch wn df-xor wps wch xorneg bitr3i con1bii
    3bitr4g con4bid $.


