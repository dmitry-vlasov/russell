
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Propositional_calculus/Truth_tables.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
       Auxiliary theorems for Alan Sare's virtual deduction tool, part 1

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  ${
    ee22.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee22.2 $e |- ( ph -> ( ps -> th ) ) $.
    ee22.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( Virtual deduction rule ~ e22 without virtual deduction connectives.
       Special theorem needed for Alan Sare's virtual deduction translation
       tool.  (Contributed by Alan Sare, 2-May-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. $)
    ee22 $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wch wth wta ee22.1 ee22.2 ee22.3 syl6c $.
  $}

  ${
    ee12an.1 $e |- ( ph -> ps ) $.
    ee12an.2 $e |- ( ph -> ( ch -> th ) ) $.
    ee12an.3 $e |- ( ( ps /\ th ) -> ta ) $.
    $( ~ e12an without virtual deduction connectives.  Special theorem needed
       for Alan Sare's virtual deduction translation tool.  (Contributed by
       Alan Sare, 28-Oct-2011.)  TODO: this is frequently used; come up with
       better label. $)
    ee12an $p |- ( ph -> ( ch -> ta ) ) $=
      wph wch wps wth wa wta wph wch wth wps ee12an.2 ee12an.1 jctild ee12an.3
      syl6 $.
  $}

  ${
    ee23.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee23.2 $e |- ( ph -> ( ps -> ( th -> ta ) ) ) $.
    ee23.3 $e |- ( ch -> ( ta -> et ) ) $.
    $( ~ e23 without virtual deductions.  (Contributed by Alan Sare,
       17-Jul-2011.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)
    ee23 $p |- ( ph -> ( ps -> ( th -> et ) ) ) $=
      wph wps wth wta wet ee23.2 wph wps wch wta wet wi ee23.1 ee23.3 syl6
      syldd $.
  $}

  $( Exportation implication also converting head from biconditional to
     conditional.  This proof is ~ exbirVD automatically translated and
     minimized.  (Contributed by Alan Sare, 31-Dec-2011.)
     (New usage is discouraged.)  TODO: decide if this is worth keeping. $)
  exbir $p |- ( ( ( ph /\ ps ) -> ( ch <-> th ) ) ->
              ( ph -> ( ps -> ( th -> ch ) ) ) ) $=
    wph wps wa wch wth wb wi wph wps wth wch wi wch wth wb wth wch wi wph wps
    wa wch wth bi2 imim2i exp3a $.

  $( ~ impexp with a 3-conjunct antecedent.  (Contributed by Alan Sare,
     31-Dec-2011.) $)
  3impexp $p |- ( ( ( ph /\ ps /\ ch ) -> th ) <->
                ( ph -> ( ps -> ( ch -> th ) ) ) ) $=
    wph wps wch w3a wth wi wph wps wch wth wi wi wi wph wps wch w3a wth wi wph
    wps wch wth wph wps wch w3a wth wi id 3expd wph wps wch wth wi wi wi wph
    wps wch wth wph wps wch wth wi wi wi id 3impd impbii $.

  $( ~ 3impexp with biconditional consequent of antecedent that is commuted in
     consequent.  Derived automatically from ~ 3impexpVD .  (Contributed by
     Alan Sare, 31-Dec-2011.)  (New usage is discouraged.)  TODO: decide if
     this is worth keeping. $)
  3impexpbicom $p |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <->
                     ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) ) $=
    wph wps wch w3a wth wta wb wi wph wps wch wta wth wb wi wi wi wph wps wch
    w3a wth wta wb wi wph wps wch wta wth wb wph wps wch w3a wth wta wb wi wth
    wta wb wta wth wb wb wph wps wch w3a wta wth wb wi wth wta bicom wth wta wb
    wta wth wb wb wph wps wch w3a wth wta wb wi wph wps wch w3a wta wth wb wi
    wth wta wb wta wth wb wph wps wch w3a imbi2 biimpcd mpi 3expd wph wps wch
    wta wth wb wi wi wi wph wps wch w3a wta wth wb wth wta wb wph wps wch w3a
    wta wth wb wi wph wps wch wta wth wb wi wi wi wph wps wch wta wth wb
    3impexp biimpri wth wta bicom syl6ibr impbii $.

  ${
    3impexpbicomi.1 $e |- ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) $.
    $( Deduction form of ~ 3impexpbicom .  Derived automatically from
       ~ 3impexpbicomiVD .  (Contributed by Alan Sare, 31-Dec-2011.)
       (New usage is discouraged.)  TODO: decide if this is worth keeping. $)
    3impexpbicomi $p |- ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) $=
      wph wps wch wta wth wb wph wps wch w3a wth wta 3impexpbicomi.1 bicomd
      3exp $.
  $}

  $( Closed form of ~ ancoms .  Derived automatically from ~ ancomsimpVD .
     (Contributed by Alan Sare, 31-Dec-2011.) $)
  ancomsimp $p |- ( ( ( ph /\ ps ) -> ch ) <-> ( ( ps /\ ph ) -> ch ) ) $=
    wph wps wa wps wph wa wch wph wps ancom imbi1i $.

  ${
    exp3acom3r.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( Export and commute antecedents.  (Contributed by Alan Sare,
       18-Mar-2012.) $)
    exp3acom3r $p |- ( ps -> ( ch -> ( ph -> th ) ) ) $=
      wph wps wch wth wph wps wch wth exp3acom3r.1 exp3a com3l $.
  $}

  $( Implication form of ~ exp3acom23 .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. $)
  exp3acom23g $p |- ( ( ph -> ( ( ps /\ ch ) -> th ) ) <->
                        ( ph -> ( ch -> ( ps -> th ) ) ) ) $=
    wps wch wa wth wi wch wps wth wi wi wph wps wch wa wth wi wch wps wa wth wi
    wch wps wth wi wi wps wch wth ancomsimp wch wps wth impexp bitri imbi2i $.

  ${
    exp3acom23.1 $e |- ( ph -> ( ( ps /\ ch ) -> th ) ) $.
    $( The exportation deduction ~ exp3a with commutation of the conjoined
       wwfs.  (Contributed by Alan Sare, 22-Jul-2012.) $)
    exp3acom23 $p |- ( ph -> ( ch -> ( ps -> th ) ) ) $=
      wph wps wch wth wph wps wch wth exp3acom23.1 exp3a com23 $.
  $}

  $( Implication form of ~ simplbi2com .  (Contributed by Alan Sare,
     22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is worth
     keeping. $)
  simplbi2comg $p |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) ) $=
    wph wps wch wa wb wps wch wph wph wps wch wa bi2 exp3acom23 $.

  ${
    simplbi2com.1 $e |- ( ph <-> ( ps /\ ch ) ) $.
    $( A deduction eliminating a conjunct, similar to ~ simplbi2 .
       (Contributed by Alan Sare, 22-Jul-2012.)  (Proof shortened by Wolf
       Lammen, 10-Nov-2012.) $)
    simplbi2com $p |- ( ch -> ( ps -> ph ) ) $=
      wps wch wph wph wps wch simplbi2com.1 simplbi2 com12 $.
  $}

  ${
    ee21.1 $e |- ( ph -> ( ps -> ch ) ) $.
    ee21.2 $e |- ( ph -> th ) $.
    ee21.3 $e |- ( ch -> ( th -> ta ) ) $.
    $( ~ e21 without virtual deductions.  (Contributed by Alan Sare,
       18-Mar-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)
    ee21 $p |- ( ph -> ( ps -> ta ) ) $=
      wph wps wch wth wta ee21.1 wph wth wps ee21.2 a1d ee21.3 ee22 $.
  $}

  ${
    ee10.1 $e |- ( ph -> ps ) $.
    ee10.2 $e |- ch $.
    ee10.3 $e |- ( ps -> ( ch -> th ) ) $.
    $( ~ e10 without virtual deductions.  (Contributed by Alan Sare,
       25-Jul-2011.)  TODO: this is frequently used; come up with better
       label. $)
    ee10 $p |- ( ph -> th ) $=
      wph wps wth ee10.1 wps wch wth ee10.2 ee10.3 mpi syl $.
  $}

  ${
    ee02.1 $e |- ph $.
    ee02.2 $e |- ( ps -> ( ch -> th ) ) $.
    ee02.3 $e |- ( ph -> ( th -> ta ) ) $.
    $( ~ e02 without virtual deductions.  (Contributed by Alan Sare,
       22-Jul-2012.)  (New usage is discouraged.)  TODO: decide if this is
       worth keeping. $)
    ee02 $p |- ( ps -> ( ch -> ta ) ) $=
      wps wph wch wth wta wph wps ee02.1 a1i ee02.2 ee02.3 sylsyld $.
  $}

$( End of auxiliary theorems for Alan Sare's virtual deduction tool, part 1 $)


