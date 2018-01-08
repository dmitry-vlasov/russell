
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-7_(Quantifier_Commutation).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           Axiom scheme ax-11 (Substitution)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Substitution.  One of the 5 equality axioms of predicate
     calculus.  The final consequent ` A. x ( x = y -> ph ) ` is a way of
     expressing " ` y ` substituted for ` x ` in wff ` ph ` " (cf. ~ sb6 ).  It
     is based on Lemma 16 of [Tarski] p. 70 and Axiom C8 of [Monk2] p. 105,
     from which it can be proved by cases.

     The original version of this axiom was ~ ax-11o ("o" for "old") and was
     replaced with this shorter ~ ax-11 in Jan. 2007.  The old axiom is proved
     from this one as theorem ~ ax11o .  Conversely, this axiom is proved from
     ~ ax-11o as theorem ~ ax11 .

     Juha Arpiainen proved the metalogical independence of this axiom (in the
     form of the older axiom ~ ax-11o ) from the others on 19-Jan-2006.  See
     item 9a at ~ http://us.metamath.org/award2003.html .

     See ~ ax11v and ~ ax11v2 for other equivalents of this axiom that (unlike
     this axiom) have distinct variable restrictions.

     This axiom scheme is logically redundant (see ~ ax11w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     22-Jan-2007.) $)
  ax-11 $a |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $.

  ${
    $d x w $.  $d w ph $.
    $( Specialization.  A universally quantified wff implies the wff without a
       quantifier Axiom scheme B5 of [Tarski] p. 67 (under his system S2,
       defined in the last paragraph on p. 77).  Also appears as Axiom scheme
       C5' in [Megill] p. 448 (p. 16 of the preprint).

       For the axiom of specialization presented in many logic textbooks, see
       theorem ~ stdpc4 .

       This theorem shows that our obsolete axiom ~ ax-4 can be derived from
       the others.  The proof uses ideas from the proof of Lemma 21 of [Monk2]
       p. 114.

       It appears that this scheme cannot be derived directly from Tarski's
       axioms without auxilliary axiom scheme ~ ax-11 .  It is thought the best
       we can do using only Tarski's axioms is ~ spw .  (Contributed by NM,
       21-May-2008.)  (Proof shortened by Scott Fenton, 24-Jan-2011.) $)
    sp $p |- ( A. x ph -> ph ) $=
      wph vx wal wph wi vw vx weq wn vw wal vw vx ax9v wph vx wal wph wi wn vw
      vx weq wn vw vw vx weq wph vx wal wph wi vw vx weq wph wph vx wal vw vx
      weq wph wn vx vw weq wph wn wi vx wal wph vx wal wn vw vx weq vx vw weq
      wph wn wph wn vw wal vx vw weq wph wn wi vx wal vw vx equcomi wph wn vw
      ax-17 wph wn vx vw ax-11 syl2im vx vw weq wph wn wi vx wal wph vx wal vx
      vw weq wn vx wal vx vw ax9v vx vw weq wph wn wi wph vx vw weq wn vx vx vw
      weq wph con2 al2imi mtoi syl6 con4d con3i alrimiv mt3 $.
  $}

  $( Show that the original axiom ~ ax-5o can be derived from ~ ax-5 and
     others.  See ~ ax5 for the rederivation of ~ ax-5 from ~ ax-5o .

     Part of the proof is based on the proof of Lemma 22 of [Monk2] p. 114.
     (Contributed by NM, 21-May-2008.)  (Proof modification is discouraged.) $)
  ax5o $p |- ( A. x ( A. x ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    wph vx wal wph vx wal vx wal wph vx wal wps wi vx wal wps vx wal wph vx wal
    wph vx wal wn vx wal wn wph vx wal wn vx wal wn vx wal wph vx wal vx wal
    wph vx wal wn vx wal wph vx wal wph vx wal wn vx sp con2i wph vx wal wn vx
    hbn1 wph vx wal wn vx wal wn wph vx wal vx wph vx wal wph vx wal wn vx wal
    wph vx hbn1 con1i alimi 3syl wph vx wal wps vx ax-5 syl5 $.

  $( If a wff is true, it is true for at least one instance.  Special case of
     Theorem 19.8 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  19.8a $p |- ( ph -> E. x ph ) $=
    wph wph wn vx wal wn wph vx wex wph wn vx wal wph wph wn vx sp con2i wph vx
    df-ex sylibr $.

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.) $)
  hba1 $p |- ( A. x ph -> A. x A. x ph ) $=
    wph vx wal wph vx wal wn vx wal wn wph vx wal wn vx wal wn vx wal wph vx
    wal vx wal wph vx wal wn vx wal wph vx wal wph vx wal wn vx sp con2i wph vx
    wal wn vx hbn1 wph vx wal wn vx wal wn wph vx wal vx wph vx wal wph vx wal
    wn vx wal wph vx hbn1 con1i alimi 3syl $.

  ${
    hbn.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
    hbn $p |- ( -. ph -> A. x -. ph ) $=
      wph wn wph vx wal wn wph wn vx wal wph vx wal wph wph vx sp con3i wph vx
      wal wn wph wn vx wph vx hbn1 wph wph vx wal hbn.1 con3i alrimih syl $.
  $}

  ${
    hbimd.1 $e |- ( ph -> A. x ph ) $.
    hbimd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    hbimd.3 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbim .
       (Contributed by NM, 1-Jan-2002.) $)
    hbimd $p |- ( ph -> ( ( ps -> ch ) -> A. x ( ps -> ch ) ) ) $=
      wph wps wch wps wch wi vx wal wph wps wn wps wn vx wal wps wch wi vx wal
      wph wps wps vx wal wi vx wal wps wn wps vx wal wn vx wal wps wn vx wal
      wph wps wps vx wal wi vx hbimd.1 hbimd.2 alrimih wps vx wal wn vx wal wps
      wps vx wal wps wps vx wal wn vx wal wps vx sp wps vx hbn1 nsyl4 con1i wps
      wps vx wal wi wps vx wal wn wps wn vx wps wps vx wal con3 al2imi syl2im
      wps wn wps wch wi vx wps wch pm2.21 alimi syl6 wph wch wch vx wal wps wch
      wi vx wal hbimd.3 wch wps wch wi vx wch wps ax-1 alimi syl6 jad $.
  $}

  ${
    $d x z $.  $d w ph $.
    spimeh.1 $e |- ( ph -> A. x ph ) $.
    spimeh.2 $e |- ( x = z -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.) $)
    spimeh $p |- ( ph -> E. x ps ) $=
      wph wps wn vx wal wn wps vx wex wps wn vx wal wph wps wn vx wal wph wn wi
      vx vz weq wn vx wal vx vz ax9v wps wn vx wal wph wn wi wn vx vz weq wn vx
      wps wn vx wal wph wn wi vx wph wph wi wps wn vx wal wph wn wi wps wn vx
      wal wph wn wi vx wal wi wph id wph wph wi wps wn vx wal wph wn vx wph wph
      wi vx wph id hbth wps wn vx wal wps wn vx wal vx wal wi wph wph wi wps wn
      vx hba1 a1i wph wn wph wn vx wal wi wph wph wi wph vx spimeh.1 hbn a1i
      hbimd ax-mp hbn vx vz weq wps wn vx wal wph wn wi vx vz weq wph wps wps
      wn vx wal spimeh.2 wps wn vx sp nsyli con3i alrimih mt3 con2i wps vx
      df-ex sylibr $.
  $}

  $( Show that the original axiom ~ ax-6o can be derived from ~ ax-6 and
     others.  See ~ ax6 for the rederivation of ~ ax-6 from ~ ax-6o .

     Normally, ~ ax6o should be used rather than ~ ax-6o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     21-May-2008.) $)
  ax6o $p |- ( -. A. x -. A. x ph -> ph ) $=
    wph vx wal wph wph vx wal wn vx wal wph vx sp wph vx ax-6 nsyl4 $.

  $( Closed theorem version of bound-variable hypothesis builder ~ hbn .
     (Contributed by NM, 5-Aug-1993.) $)
  hbnt $p |- ( A. x ( ph -> A. x ph ) -> ( -. ph -> A. x -. ph ) ) $=
    wph wn wph vx wal wn vx wal wph wph vx wal wi vx wal wph wn vx wal wph vx
    wal wn vx wal wph wph vx ax6o con1i wph wph vx wal wi wph vx wal wn wph wn
    vx wph wph vx wal con3 al2imi syl5 $.

  ${
    hbim.1 $e |- ( ph -> A. x ph ) $.
    hbim.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened
       by O'Cat, 3-Mar-2008.) $)
    hbim $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      wph wps wph wps wi vx wal wph wn wph wps wi vx wph vx hbim.1 hbn wph wps
      pm2.21 alrimih wps wph wps wi vx hbim.2 wps wph ax-1 alrimih ja $.
  $}

  $( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.) $)
  19.9ht $p |- ( A. x ( ph -> A. x ph ) -> ( E. x ph -> ph ) ) $=
    wph vx wex wph wn vx wal wn wph wph vx wal wi vx wal wph wph vx df-ex wph
    wph vx wal wi vx wal wph wph wn vx wal wph vx hbnt con1d syl5bi $.

  ${
    19.9h.1 $e |- ( ph -> A. x ph ) $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.) $)
    19.9h $p |- ( E. x ph <-> ph ) $=
      wph vx wex wph wph wph vx wal wi wph vx wex wph wi vx wph vx 19.9ht
      19.9h.1 mpg wph vx 19.8a impbii $.
  $}

  ${
    19.23h.1 $e |- ( ps -> A. x ps ) $.
    $( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.23h $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      wph wps wi vx wal wph vx wex wps wi wph wps wi vx wal wph vx wex wps vx
      wex wps wph wps vx exim wps vx 19.23h.1 19.9h syl6ib wph vx wex wps wi
      wph wps wi vx wph vx wex wps vx wph vx hbe1 19.23h.1 hbim wph wph vx wex
      wps wph vx 19.8a imim1i alrimih impbii $.
  $}

  ${
    exlimih.1 $e |- ( ps -> A. x ps ) $.
    exlimih.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 13-May-2011.) $)
    exlimih $p |- ( E. x ph -> ps ) $=
      wph wps wi wph vx wex wps wi vx wph wps vx exlimih.1 19.23h exlimih.2
      mpgbi $.
  $}

  ${
    $d x y $.
    equsalhw.1 $e |- ( ps -> A. x ps ) $.
    equsalhw.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Weaker version of ~ equsalh (requiring distinct variables) without using
       ~ ax-12 .  (Contributed by NM, 29-Nov-2015.) $)
    equsalhw $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      vx vy weq wph wi vx wal vx vy weq wps vx wal wi vx wal wps vx vy weq wph
      wi vx vy weq wps vx wal wi vx vx vy weq wph wps vx wal vx vy weq wph wps
      wps vx wal equsalhw.2 wps vx wal wps wps vx sp equsalhw.1 impbii syl6bbr
      pm5.74i albii wps vx vy weq wps vx wal wi vx wal wps vx vy weq wps vx wal
      wi vx equsalhw.1 wps wps vx wal vx vy weq equsalhw.1 a1d alrimih vx vy
      weq wps vx wal wi vx wal wps vx wal wn vx wal wn wps vx vy weq wps vx wal
      wi vx wal wps vx wal wn vx wal vx vy weq wn vx wal vx vy ax9v vx vy weq
      wps vx wal wi wps vx wal wn vx vy weq wn vx vx vy weq wps vx wal con3
      al2imi mtoi wps vx ax6o syl impbii bitr4i $.
  $}

  ${
    19.21h.1 $e |- ( ph -> A. x ph ) $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 1-Aug-2017.) $)
    19.21h $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      wph wps wi vx wal wph wps vx wal wi wph wph vx wal wph wps wi vx wal wps
      vx wal 19.21h.1 wph wps vx alim syl5 wph wps vx wal wi wph wps wi vx wph
      wps vx wal vx 19.21h.1 wps vx hba1 hbim wps vx wal wps wph wps vx sp
      imim2i alrimih impbii $.
  $}

  ${
    hbim1.1 $e |- ( ph -> A. x ph ) $.
    hbim1.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( A closed form of ~ hbim .  (Contributed by NM, 5-Aug-1993.) $)
    hbim1 $p |- ( ( ph -> ps ) -> A. x ( ph -> ps ) ) $=
      wph wps wi wph wps vx wal wi wph wps wi vx wal wph wps wps vx wal hbim1.2
      a2i wph wps vx hbim1.1 19.21h sylibr $.
  $}

  ${
    hbex.1 $e |- ( ph -> A. x ph ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by NM, 5-Aug-1993.) $)
    hbex $p |- ( E. y ph -> A. x E. y ph ) $=
      wph vy wex wph wn vy wal wn vx wph vy df-ex wph wn vy wal vx wph wn vx vy
      wph vx hbex.1 hbn hbal hbn hbxfrbi $.
  $}

  $( Theorem 19.12 of [Margaris] p. 89.  Assuming the converse is a mistake
     sometimes made by beginners!  But sometimes the converse does hold, as in
     ~ 19.12vv and ~ r19.12sn .  (Contributed by NM, 5-Aug-1993.) $)
  19.12 $p |- ( E. x A. y ph -> A. y E. x ph ) $=
    wph vy wal vx wex wph vx wex vy wph vy wal vy vx wph vy hba1 hbex wph vy
    wal wph vx wph vy sp eximi alrimih $.

  ${
    $d x z $.  $d y z $.
    dvelimhw.1 $e |- ( ph -> A. x ph ) $.
    dvelimhw.2 $e |- ( ps -> A. z ps ) $.
    dvelimhw.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $(  dvelimhw.4 $e |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $. $)
    dvelimhw.4 $e |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $.
    $( Proof of ~ dvelimh without using ~ ax-12 but with additional distinct
       variable conditions.  (Contributed by Andrew Salmon, 21-Jul-2011.)
       (Revised by NM, 1-Aug-2017.) $)
    dvelimhw $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      vx vy weq vx wal wn vz vy weq wph wi vz wal vz vy weq wph wi vz wal vx
      wal wps wps vx wal vx vy weq vx wal wn vz vy weq wph wi vx vz vx vy weq
      vx wal wn vz ax-17 vx vy weq vx wal wn vz vy weq wph vx vx vy weq vx hbn1
      vz vy weq vy vz weq vx vy weq vx wal wn vy vz weq vx wal vz vy weq vx wal
      vz vy equcomi dvelimhw.4 vy vz weq vz vy weq vx vy vz equcomi alimi syl56
      wph wph vx wal wi vx vy weq vx wal wn dvelimhw.1 a1i hbimd hbald wph wps
      vz vy dvelimhw.2 dvelimhw.3 equsalhw vz vy weq wph wi vz wal wps vx wph
      wps vz vy dvelimhw.2 dvelimhw.3 equsalhw albii 3imtr3g $.
  $}

  ${
    hban.1 $e |- ( ph -> A. x ph ) $.
    hban.2 $e |- ( ps -> A. x ps ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by NM, 5-Aug-1993.) $)
    hban $p |- ( ( ph /\ ps ) -> A. x ( ph /\ ps ) ) $=
      wph wps wa wph wps wn wi wn vx wph wps df-an wph wps wn wi vx wph wps wn
      vx hban.1 wps vx hban.2 hbn hbim hbn hbxfrbi $.
  $}

  ${
    $d x y $.
    cbv3hv.1 $e |- ( ph -> A. y ph ) $.
    cbv3hv.2 $e |- ( ps -> A. x ps ) $.
    cbv3hv.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Lemma for ~ ax10 .  Similar to ~ cbv3h .  Requires distinct variables
       but avoids ~ ax-12 .  (Contributed by NM, 25-Jul-2015.) $)
    cbv3hv $p |- ( A. x ph -> A. y ps ) $=
      wph vx wal wph vy wal vx wal wps vy wal wph wph vy wal vx cbv3hv.1 alimi
      wph wps vy wal vy vx wph vx wal wps vy wph vx wal wps wi vx vy weq wn vx
      wal vx vy ax9v wph vx wal wps wi wn vx vy weq wn vx wph vx wal wps wi vx
      wph vx wal wps vx wph vx hba1 cbv3hv.2 hbim hbn vx vy weq wph vx wal wps
      wi wph vx wal wph vx vy weq wps wph vx sp cbv3hv.3 syl5 con3i alrimih mt3
      alimi a7s syl $.
  $}

  ${
    spi.1 $e |- A. x ph $.
    $( Inference rule reversing generalization.  (Contributed by NM,
       5-Aug-1993.) $)
    spi $p |- ph $=
      wph vx wal wph spi.1 wph vx sp ax-mp $.
  $}

  ${
    sps.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.) $)
    sps $p |- ( A. x ph -> ps ) $=
      wph vx wal wph wps wph vx sp sps.1 syl $.
  $}

  ${
    spsd.1 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction generalizing antecedent.  (Contributed by NM, 17-Aug-1994.) $)
    spsd $p |- ( ph -> ( A. x ps -> ch ) ) $=
      wps vx wal wps wph wch wps vx sp spsd.1 syl5 $.
  $}

  $( Consequence of the definition of not-free.  (Contributed by Mario
     Carneiro, 26-Sep-2016.) $)
  nfr $p |- ( F/ x ph -> ( ph -> A. x ph ) ) $=
    wph vx wnf wph wph vx wal wi vx wal wph wph vx wal wi wph vx df-nf wph wph
    vx wal wi vx sp sylbi $.

  ${
    nfri.1 $e |- F/ x ph $.
    $( Consequence of the definition of not-free.  (Contributed by Mario
       Carneiro, 11-Aug-2016.) $)
    nfri $p |- ( ph -> A. x ph ) $=
      wph vx wnf wph wph vx wal wi nfri.1 wph vx nfr ax-mp $.
  $}

  ${
    nfrd.1 $e |- ( ph -> F/ x ps ) $.
    $( Consequence of the definition of not-free in a context.  (Contributed by
       Mario Carneiro, 11-Aug-2016.) $)
    nfrd $p |- ( ph -> ( ps -> A. x ps ) ) $=
      wph wps vx wnf wps wps vx wal wi nfrd.1 wps vx nfr syl $.
  $}

  ${
    alimd.1 $e |- F/ x ph $.
    alimd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.20 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alimd $p |- ( ph -> ( A. x ps -> A. x ch ) ) $=
      wph wps wch vx wph vx alimd.1 nfri alimd.2 alimdh $.
  $}

  ${
    alrimi.1 $e |- F/ x ph $.
    alrimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alrimi $p |- ( ph -> A. x ps ) $=
      wph wps vx wph vx alrimi.1 nfri alrimi.2 alrimih $.
  $}

  ${
    nfd.1 $e |- F/ x ph $.
    nfd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ph ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nfd $p |- ( ph -> F/ x ps ) $=
      wph wps wps vx wal wi vx wal wps vx wnf wph wps wps vx wal wi vx nfd.1
      nfd.2 alrimi wps vx df-nf sylibr $.
  $}

  ${
    nfdh.1 $e |- ( ph -> A. x ph ) $.
    nfdh.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduce that ` x ` is not free in ` ph ` in a context.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nfdh $p |- ( ph -> F/ x ps ) $=
      wph wps vx wph vx nfdh.1 nfi nfdh.2 nfd $.
  $}

  ${
    alrimdd.1 $e |- F/ x ph $.
    alrimdd.2 $e |- ( ph -> F/ x ps ) $.
    alrimdd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alrimdd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      wph wps wps vx wal wch vx wal wph wps vx alrimdd.2 nfrd wph wps wch vx
      alrimdd.1 alrimdd.3 alimd syld $.
  $}

  ${
    alrimd.1 $e |- F/ x ph $.
    alrimd.2 $e |- F/ x ps $.
    alrimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.21 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    alrimd $p |- ( ph -> ( ps -> A. x ch ) ) $=
      wph wps wch vx alrimd.1 wps vx wnf wph alrimd.2 a1i alrimd.3 alrimdd $.
  $}

  ${
    eximd.1 $e |- F/ x ph $.
    eximd.2 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.22 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    eximd $p |- ( ph -> ( E. x ps -> E. x ch ) ) $=
      wph wps wch vx wph vx eximd.1 nfri eximd.2 eximdh $.
  $}

  ${
    nexd.1 $e |- F/ x ph $.
    nexd.2 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by
       Mario Carneiro, 24-Sep-2016.) $)
    nexd $p |- ( ph -> -. E. x ps ) $=
      wph wps vx wph vx nexd.1 nfri nexd.2 nexdh $.
  $}

  ${
    albid.1 $e |- F/ x ph $.
    albid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for universal quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    albid $p |- ( ph -> ( A. x ps <-> A. x ch ) ) $=
      wph wps wch vx wph vx albid.1 nfri albid.2 albidh $.
  $}

  ${
    exbid.1 $e |- F/ x ph $.
    exbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Formula-building rule for existential quantifier (deduction rule).
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    exbid $p |- ( ph -> ( E. x ps <-> E. x ch ) ) $=
      wph wps wch vx wph vx exbid.1 nfri exbid.2 exbidh $.
  $}

  ${
    nfbidf.1 $e |- F/ x ph $.
    nfbidf.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( An equality theorem for effectively not free.  (Contributed by Mario
       Carneiro, 4-Oct-2016.) $)
    nfbidf $p |- ( ph -> ( F/ x ps <-> F/ x ch ) ) $=
      wph wps wps vx wal wi vx wal wch wch vx wal wi vx wal wps vx wnf wch vx
      wnf wph wps wps vx wal wi wch wch vx wal wi vx nfbidf.1 wph wps wch wps
      vx wal wch vx wal nfbidf.2 wph wps wch vx nfbidf.1 nfbidf.2 albid imbi12d
      albid wps vx df-nf wch vx df-nf 3bitr4g $.
  $}

  $( Abbreviated version of ~ ax6o .  (Contributed by NM, 5-Aug-1993.) $)
  a6e $p |- ( E. x A. x ph -> ph ) $=
    wph vx wal vx wex wph vx wal wn vx wal wn wph wph vx wal vx df-ex wph vx
    ax6o sylbi $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfa1 $p |- F/ x A. x ph $=
    wph vx wal vx wph vx hba1 nfi $.

  $( ` x ` is not free in ` F/ x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.) $)
  nfnf1 $p |- F/ x F/ x ph $=
    wph vx wnf wph wph vx wal wi vx wal vx wph vx df-nf wph wph vx wal wi vx
    nfa1 nfxfr $.

  ${
    a5i.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax5o .  (Contributed by NM, 5-Aug-1993.) $)
    a5i $p |- ( A. x ph -> A. x ps ) $=
      wph vx wal wps vx wph vx nfa1 a5i.1 alrimi $.
  $}

  ${
    hb.1 $e |- ( ph -> A. x ph ) $.
    hb.2 $e |- ( ps -> A. x ps ) $.
    hb.3 $e |- ( ch -> A. x ch ) $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by NM, 14-Sep-2003.) $)
    hb3an $p |- ( ( ph /\ ps /\ ch ) -> A. x ( ph /\ ps /\ ch ) ) $=
      wph wps wch w3a wph wps wa wch wa vx wph wps wch df-3an wph wps wa wch vx
      wph wps vx hb.1 hb.2 hban hb.3 hban hbxfrbi $.
  $}

  ${
    nfnd.1 $e |- ( ph -> F/ x ps ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfnd $p |- ( ph -> F/ x -. ps ) $=
      wph wps vx wnf wps wn vx wnf nfnd.1 wps vx wnf wps wn vx wps vx nfnf1 wps
      wn wps vx wal wn vx wal wps vx wnf wps wn vx wal wps vx wal wn vx wal wps
      wps vx ax6o con1i wps vx wnf wps wps vx wal wi vx wal wps vx wal wn vx
      wal wps wn vx wal wi wps vx df-nf wps wps vx wal wi wps vx wal wn wps wn
      vx wps wps vx wal con3 al2imi sylbi syl5 nfd syl $.

    nfimd.2 $e |- ( ph -> F/ x ch ) $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfimd $p |- ( ph -> F/ x ( ps -> ch ) ) $=
      wph wps vx wnf wch vx wnf wps wch wi vx wnf nfnd.1 nfimd.2 wps wps vx wal
      wi vx wal wch wch vx wal wi vx wal wa wps wch wi wps wch wi vx wal wi vx
      wal wps vx wnf wch vx wnf wa wps wch wi vx wnf wps wps vx wal wi vx wal
      wch wch vx wal wi vx wal wps wch wi wps wch wi vx wal wi vx wal wps wps
      vx wal wi vx wal wch wch vx wal wi wps wch wi wps wch wi vx wal wi vx wps
      wps vx wal wi vx nfa1 wps wps vx wal wi vx wal wps wn wps wn vx wal wi
      wch wch vx wal wi wps wch wi wps wch wi vx wal wi wi wps vx hbnt wps wn
      wps wn vx wal wi wch wch vx wal wi wps wch wi wps wch wi vx wal wi wps wn
      wps wn vx wal wi wch wch vx wal wi wa wps wch wps wch wi vx wal wps wn
      wps wn vx wal wi wps wn wps wch wi vx wal wi wch wch vx wal wi wps wn vx
      wal wps wch wi vx wal wps wn wps wn wps wch wi vx wps wch pm2.21 alimi
      imim2i adantr wch wch vx wal wi wch wps wch wi vx wal wi wps wn wps wn vx
      wal wi wch vx wal wps wch wi vx wal wch wch wps wch wi vx wch wps ax-1
      alimi imim2i adantl jad ex syl alimd imp wps vx wnf wps wps vx wal wi vx
      wal wch vx wnf wch wch vx wal wi vx wal wps vx df-nf wch vx df-nf anbi12i
      wps wch wi vx df-nf 3imtr4i syl2anc $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfbid $p |- ( ph -> F/ x ( ps <-> ch ) ) $=
      wps wch wb wps wch wi wch wps wi wn wi wn wph vx wps wch dfbi1 wph wps
      wch wi wch wps wi wn wi vx wph wps wch wi wch wps wi wn vx wph wps wch vx
      nfnd.1 nfimd.2 nfimd wph wch wps wi vx wph wch wps vx nfimd.2 nfnd.1
      nfimd nfnd nfimd nfnd nfxfrd $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 7-Oct-2016.) $)
    nfand $p |- ( ph -> F/ x ( ps /\ ch ) ) $=
      wps wch wa wps wch wn wi wn wph vx wps wch df-an wph wps wch wn wi vx wph
      wps wch wn vx nfnd.1 wph wch vx nfimd.2 nfnd nfimd nfnd nfxfrd $.

    nfimd.3 $e |- ( ph -> F/ x th ) $.
    $( Deduction form of bound-variable hypothesis builder ~ nf3an .
       (Contributed by NM, 17-Feb-2013.)  (Revised by Mario Carneiro,
       16-Oct-2016.) $)
    nf3and $p |- ( ph -> F/ x ( ps /\ ch /\ th ) ) $=
      wps wch wth w3a wps wch wa wth wa wph vx wps wch wth df-3an wph wps wch
      wa wth vx wph wps wch vx nfnd.1 nfimd.2 nfand nfimd.3 nfand nfxfrd $.

  $}

  ${
    nf.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` -. ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfn $p |- F/ x -. ph $=
      wph wn vx wnf wtru wph vx wph vx wnf wtru nf.1 a1i nfnd trud $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfal $p |- F/ x A. y ph $=
      wph vy wal vx wph vx vy wph vx nf.1 nfri hbal nfi $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfex $p |- F/ x E. y ph $=
      wph vy wex wph wn vy wal wn vx wph vy df-ex wph wn vy wal vx wph wn vx vy
      wph vx nf.1 nfn nfal nfn nfxfr $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` F/ y ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfnf $p |- F/ x F/ y ph $=
      wph vy wnf wph wph vy wal wi vy wal vx wph vy df-nf wph wph vy wal wi vx
      vy wph wph vy wal wi vx wnf wtru wph wph vy wal vx wph vx wnf wtru nf.1
      a1i wph vy wal vx wnf wtru wph vx vy nf.1 nfal a1i nfimd trud nfal nfxfr
      $.

    nf.2 $e |- F/ x ps $.
    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph -> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfim $p |- F/ x ( ph -> ps ) $=
      wph wps wi vx wnf wtru wph wps vx wph vx wnf wtru nf.1 a1i wps vx wnf
      wtru nf.2 a1i nfimd trud $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph \/ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfor $p |- F/ x ( ph \/ ps ) $=
      wph wps wo wph wn wps wi vx wph wps df-or wph wn wps vx wph vx nf.1 nfn
      nf.2 nfim nfxfr $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph /\ ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfan $p |- F/ x ( ph /\ ps ) $=
      wph wps wa wph wps wn wi wn vx wph wps df-an wph wps wn wi vx wph wps wn
      vx nf.1 wps vx nf.2 nfn nfim nfn nfxfr $.

    $( If ` x ` is not free in ` ph ` and ` ps ` , it is not free in
       ` ( ph <-> ps ) ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfbi $p |- F/ x ( ph <-> ps ) $=
      wph wps wb wph wps wi wps wph wi wa vx wph wps dfbi2 wph wps wi wps wph
      wi vx wph wps vx nf.1 nf.2 nfim wps wph vx nf.2 nf.1 nfim nfan nfxfr $.

    nf.3 $e |- F/ x ch $.
    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph \/ ps \/ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3or $p |- F/ x ( ph \/ ps \/ ch ) $=
      wph wps wch w3o wph wps wo wch wo vx wph wps wch df-3or wph wps wo wch vx
      wph wps vx nf.1 nf.2 nfor nf.3 nfor nfxfr $.

    $( If ` x ` is not free in ` ph ` , ` ps ` , and ` ch ` , it is not free in
       ` ( ph /\ ps /\ ch ) ` .  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nf3an $p |- F/ x ( ph /\ ps /\ ch ) $=
      wph wps wch w3a wph wps wa wch wa vx wph wps wch df-3an wph wps wa wch vx
      wph wps vx nf.1 nf.2 nfan nf.3 nfan nfxfr $.
  $}

  ${
    nfald.1 $e |- F/ y ph $.
    nfald.2 $e |- ( ph -> F/ x ps ) $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` A. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfald $p |- ( ph -> F/ x A. y ps ) $=
      wph wps vx wnf vy wal wps vy wal vx wnf wph wps vx wnf vy nfald.1 nfald.2
      alrimi wps vx wnf vy wal wps vy wal vx wps vx wnf vx vy wps vx nfnf1 nfal
      wps vx wnf vy wal wps vy wal wps vx wal vy wal wps vy wal vx wal wps vx
      wnf wps wps vx wal vy wps vx nfr al2imi wps vy vx ax-7 syl6 nfd syl $.

    $( If ` x ` is not free in ` ph ` , it is not free in ` E. y ph ` .
       (Contributed by Mario Carneiro, 24-Sep-2016.) $)
    nfexd $p |- ( ph -> F/ x E. y ps ) $=
      wps vy wex wps wn vy wal wn wph vx wps vy df-ex wph wps wn vy wal vx wph
      wps wn vx vy nfald.1 wph wps vx nfald.2 nfnd nfald nfnd nfxfrd $.
  $}

  $( Lemma 24 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfa2 $p |- F/ x A. y A. x ph $=
    wph vx wal vx vy wph vx nfa1 nfal $.

  $( Lemma 23 of [Monk2] p. 114.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nfia1 $p |- F/ x ( A. x ph -> A. x ps ) $=
    wph vx wal wps vx wal vx wph vx nfa1 wps vx nfa1 nfim $.

  $( The analog in our "pure" predicate calculus of the Brouwer axiom (B) of
     modal logic S5.  (Contributed by NM, 5-Oct-2005.) $)
  modal-b $p |- ( ph -> A. x -. A. x -. ph ) $=
    wph wn vx wal wn vx wal wph wph wn vx ax6o con4i $.

  $( Theorem 19.2 of [Margaris] p. 89, generalized to use two set variables.
     (Contributed by O'Cat, 31-Mar-2008.) $)
  19.2g $p |- ( A. x ph -> E. y ph ) $=
    wph wph vy wex vx wph vy 19.8a sps $.

  ${
    19.3.1 $e |- F/ x ph $.
    $( A wff may be quantified with a variable not free in it.  Theorem 19.3 of
       [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 24-Sep-2016.) $)
    19.3 $p |- ( A. x ph <-> ph ) $=
      wph vx wal wph wph vx sp wph vx 19.3.1 nfri impbii $.
  $}

  $( A closed version of ~ 19.9 .  (Contributed by NM, 5-Aug-1993.)  (Revised
     by Mario Carneiro, 24-Sep-2016.) $)
  19.9t $p |- ( F/ x ph -> ( E. x ph <-> ph ) ) $=
    wph vx wnf wph vx wex wph wph vx wex wph wn vx wal wn wph vx wnf wph wph vx
    df-ex wph vx wnf wph wph wn vx wal wph vx wnf wph wn vx wph vx wnf wph vx
    wph vx wnf id nfnd nfrd con1d syl5bi wph vx 19.8a impbid1 $.

  ${
    19.9.1 $e |- F/ x ph $.
    $( A wff may be existentially quantified with a variable not free in it.
       Theorem 19.9 of [Margaris] p. 89.  (Contributed by FL, 24-Mar-2007.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.9 $p |- ( E. x ph <-> ph ) $=
      wph vx wnf wph vx wex wph wb 19.9.1 wph vx 19.9t ax-mp $.
  $}

  ${
    19.9d.1 $e |- ( ps -> F/ x ph ) $.
    $( A deduction version of one direction of ~ 19.9 .  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.9d $p |- ( ps -> ( E. x ph -> ph ) ) $=
      wps wph vx wex wph wps wph vx wnf wph vx wex wph wb 19.9d.1 wph vx 19.9t
      syl biimpd $.
  $}

  $( One direction of Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM,
     5-Aug-1993.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
  excomim $p |- ( E. x E. y ph -> E. y E. x ph ) $=
    wph vy wex vx wex wph vx wex vy wex vx wex wph vx wex vy wex wph wph vx wex
    vx vy wph vx 19.8a 2eximi wph vx wex vy wex vx wph vx wex vx vy wph vx nfe1
    nfex 19.9 sylib $.

  $( Theorem 19.11 of [Margaris] p. 89.  (Contributed by NM, 5-Aug-1993.) $)
  excom $p |- ( E. x E. y ph <-> E. y E. x ph ) $=
    wph vy wex vx wex wph vx wex vy wex wph vx vy excomim wph vy vx excomim
    impbii $.

  ${
    19.16.1 $e |- F/ x ph $.
    $( Theorem 19.16 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.16 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> A. x ps ) ) $=
      wph wph vx wal wph wps wb vx wal wps vx wal wph vx 19.16.1 19.3 wph wps
      vx albi syl5bbr $.
  $}

  ${
    19.17.1 $e |- F/ x ps $.
    $( Theorem 19.17 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.17 $p |- ( A. x ( ph <-> ps ) -> ( A. x ph <-> ps ) ) $=
      wph wps wb vx wal wph vx wal wps vx wal wps wph wps vx albi wps vx
      19.17.1 19.3 syl6bb $.
  $}

  ${
    19.19.1 $e |- F/ x ph $.
    $( Theorem 19.19 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.19 $p |- ( A. x ( ph <-> ps ) -> ( ph <-> E. x ps ) ) $=
      wph wph vx wex wph wps wb vx wal wps vx wex wph vx 19.19.1 19.9 wph wps
      vx exbi syl5bbr $.
  $}

  $( Closed form of Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
     27-May-1997.)  (Revised by Mario Carneiro, 24-Sep-2016.) $)
  19.21t $p |- ( F/ x ph -> ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) ) $=
    wph vx wnf wph wps wi vx wal wph wps vx wal wi wph vx wnf wph wph vx wal
    wph wps wi vx wal wps vx wal wph vx wnf wph vx wph vx wnf id nfrd wph wps
    vx alim syl9 wph vx wnf wph wps vx wal wi wph wps vx wal wi vx wal wph wps
    wi vx wal wph vx wnf wph wps vx wal wi vx wph vx wnf wph wps vx wal vx wph
    vx wnf id wps vx wal vx wnf wph vx wnf wps vx nfa1 a1i nfimd nfrd wph wps
    vx wal wi wph wps wi vx wps vx wal wps wph wps vx sp imim2i alimi syl6
    impbid $.

  ${
    19.21.1 $e |- F/ x ph $.
    $( Theorem 19.21 of [Margaris] p. 90.  The hypothesis can be thought of
       as " ` x ` is not free in ` ph ` ."  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.21 $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      wph vx wnf wph wps wi vx wal wph wps vx wal wi wb 19.21.1 wph wps vx
      19.21t ax-mp $.
  $}

  ${
    19.21-2.1 $e |- F/ x ph $.
    19.21-2.2 $e |- F/ y ph $.
    $( Theorem 19.21 of [Margaris] p. 90 but with 2 quantifiers.  (Contributed
       by NM, 4-Feb-2005.) $)
    19.21-2 $p |- ( A. x A. y ( ph -> ps ) <-> ( ph -> A. x A. y ps ) ) $=
      wph wps wi vy wal vx wal wph wps vy wal wi vx wal wph wps vy wal vx wal
      wi wph wps wi vy wal wph wps vy wal wi vx wph wps vy 19.21-2.2 19.21
      albii wph wps vy wal vx 19.21-2.1 19.21 bitri $.
  $}

  ${
    stdpc5.1 $e |- F/ x ph $.
    $( An axiom scheme of standard predicate calculus that emulates Axiom 5 of
       [Mendelson] p. 69.  The hypothesis ` F/ x ph ` can be thought of as
       emulating " ` x ` is not free in ` ph ` ."  With this definition, the
       meaning of "not free" is less restrictive than the usual textbook
       definition; for example ` x ` would not (for us) be free in ` x = x ` by
       ~ nfequid .  This theorem scheme can be proved as a metatheorem of
       Mendelson's axiom system, even though it is slightly stronger than his
       Axiom 5.  (Contributed by NM, 22-Sep-1993.)  (Revised by Mario Carneiro,
       12-Oct-2016.) $)
    stdpc5 $p |- ( A. x ( ph -> ps ) -> ( ph -> A. x ps ) ) $=
      wph wph vx wal wph wps wi vx wal wps vx wal wph vx stdpc5.1 nfri wph wps
      vx alim syl5 $.
  $}

  ${
    19.21bi.1 $e |- ( ph -> A. x ps ) $.
    $( Inference from Theorem 19.21 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.21bi $p |- ( ph -> ps ) $=
      wph wps vx wal wps 19.21bi.1 wps vx sp syl $.
  $}

  ${
    19.21bbi.1 $e |- ( ph -> A. x A. y ps ) $.
    $( Inference removing double quantifier.  (Contributed by NM,
       20-Apr-1994.) $)
    19.21bbi $p |- ( ph -> ps ) $=
      wph wps vy wph wps vy wal vx 19.21bbi.1 19.21bi 19.21bi $.
  $}

  $( Closed form of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
     7-Nov-2005.) $)
  19.23t $p |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) ) $=
    wps vx wnf wph wps wi vx wal wph vx wex wps wi wph wps wi vx wal wph vx wex
    wps vx wex wi wps vx wnf wph vx wex wps wi wph wps vx exim wps vx wnf wps
    vx wex wps wph vx wex wps vx 19.9t imbi2d syl5ib wps vx wnf wph vx wex wps
    wi wph wps wi vx wps vx nfnf1 wps vx wnf wph vx wex wps vx wph vx wex vx
    wnf wps vx wnf wph vx nfe1 a1i wps vx wnf id nfimd wps vx wnf wph wph vx
    wex wps wph wph vx wex wi wps vx wnf wph vx 19.8a a1i imim1d alrimdd impbid
    $.

  ${
    19.23.1 $e |- F/ x ps $.
    $( Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.23 $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      wps vx wnf wph wps wi vx wal wph vx wex wps wi wb 19.23.1 wph wps vx
      19.23t ax-mp $.
  $}

  $( An alternative definition of ~ df-nf , which does not involve nested
     quantifiers on the same variable.  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf2 $p |- ( F/ x ph <-> ( E. x ph -> A. x ph ) ) $=
    wph vx wnf wph wph vx wal wi vx wal wph vx wex wph vx wal wi wph vx df-nf
    wph wph vx wal vx wph vx nfa1 19.23 bitri $.

  $( An alternative definition of ~ df-nf .  (Contributed by Mario Carneiro,
     24-Sep-2016.) $)
  nf3 $p |- ( F/ x ph <-> A. x ( E. x ph -> ph ) ) $=
    wph vx wnf wph vx wex wph vx wal wi wph vx wex wph wi vx wal wph vx nf2 wph
    vx wex wph vx wph vx nfe1 19.21 bitr4i $.

  $( Variable ` x ` is effectively not free in ` ph ` iff ` ph ` is always true
     or always false.  (Contributed by Mario Carneiro, 24-Sep-2016.) $)
  nf4 $p |- ( F/ x ph <-> ( A. x ph \/ A. x -. ph ) ) $=
    wph vx wnf wph vx wex wph vx wal wi wph vx wex wn wph vx wal wo wph vx wal
    wph wn vx wal wo wph vx nf2 wph vx wex wph vx wal imor wph vx wex wn wph vx
    wal wo wph vx wal wph vx wex wn wo wph vx wal wph wn vx wal wo wph vx wex
    wn wph vx wal orcom wph wn vx wal wph vx wex wn wph vx wal wph vx alnex
    orbi2i bitr4i 3bitri $.

  ${
    exlimi.1 $e |- F/ x ps $.
    exlimi.2 $e |- ( ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    exlimi $p |- ( E. x ph -> ps ) $=
      wph wps wi wph vx wex wps wi vx wph wps vx exlimi.1 19.23 exlimi.2 mpgbi
      $.
  $}

  ${
    19.23bi.1 $e |- ( E. x ph -> ps ) $.
    $( Inference from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.23bi $p |- ( ph -> ps ) $=
      wph wph vx wex wps wph vx 19.8a 19.23bi.1 syl $.
  $}

  ${
    exlimd.1 $e |- F/ x ph $.
    exlimd.2 $e |- F/ x ch $.
    exlimd.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by Mario
       Carneiro, 24-Sep-2016.) $)
    exlimd $p |- ( ph -> ( E. x ps -> ch ) ) $=
      wph wps wch wi vx wal wps vx wex wch wi wph wps wch wi vx exlimd.1
      exlimd.3 alrimi wps wch vx exlimd.2 19.23 sylib $.
  $}

  ${
    exlimdh.1 $e |- ( ph -> A. x ph ) $.
    exlimdh.2 $e |- ( ch -> A. x ch ) $.
    exlimdh.3 $e |- ( ph -> ( ps -> ch ) ) $.
    $( Deduction from Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jan-1997.) $)
    exlimdh $p |- ( ph -> ( E. x ps -> ch ) ) $=
      wph wps wch vx wph vx exlimdh.1 nfi wch vx exlimdh.2 nfi exlimdh.3 exlimd
      $.
  $}

  ${
    19.27.1 $e |- F/ x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.27 $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      wph wps wa vx wal wph vx wal wps vx wal wa wph vx wal wps wa wph wps vx
      19.26 wps vx wal wps wph vx wal wps vx 19.27.1 19.3 anbi2i bitri $.
  $}

  ${
    19.28.1 $e |- F/ x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.28 $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      wph wps wa vx wal wph vx wal wps vx wal wa wph wps vx wal wa wph wps vx
      19.26 wph vx wal wph wps vx wal wph vx 19.28.1 19.3 anbi1i bitri $.
  $}

  ${
    19.36.1 $e |- F/ x ps $.
    $( Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.36 $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      wph wps wi vx wex wph vx wal wps vx wex wi wph vx wal wps wi wph wps vx
      19.35 wps vx wex wps wph vx wal wps vx 19.36.1 19.9 imbi2i bitri $.

    19.36i.2 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.36i $p |- ( A. x ph -> ps ) $=
      wph wps wi vx wex wph vx wal wps wi 19.36i.2 wph wps vx 19.36.1 19.36
      mpbi $.
  $}

  ${
    19.37.1 $e |- F/ x ph $.
    $( Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.37 $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      wph wps wi vx wex wph vx wal wps vx wex wi wph wps vx wex wi wph wps vx
      19.35 wph vx wal wph wps vx wex wph vx 19.37.1 19.3 imbi1i bitri $.
  $}

  $( Theorem 19.38 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
  19.38 $p |- ( ( E. x ph -> A. x ps ) -> A. x ( ph -> ps ) ) $=
    wph vx wex wps vx wal wi wph wps wi vx wph vx wex wps vx wal vx wph vx nfe1
    wps vx nfa1 nfim wph wph vx wex wps vx wal wps wph vx 19.8a wps vx sp
    imim12i alrimi $.

  ${
    19.32.1 $e |- F/ x ph $.
    $( Theorem 19.32 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 24-Sep-2016.) $)
    19.32 $p |- ( A. x ( ph \/ ps ) <-> ( ph \/ A. x ps ) ) $=
      wph wn wps wi vx wal wph wn wps vx wal wi wph wps wo vx wal wph wps vx
      wal wo wph wn wps vx wph vx 19.32.1 nfn 19.21 wph wps wo wph wn wps wi vx
      wph wps df-or albii wph wps vx wal df-or 3bitr4i $.
  $}

  ${
    19.31.1 $e |- F/ x ps $.
    $( Theorem 19.31 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.31 $p |- ( A. x ( ph \/ ps ) <-> ( A. x ph \/ ps ) ) $=
      wps wph wo vx wal wps wph vx wal wo wph wps wo vx wal wph vx wal wps wo
      wps wph vx 19.31.1 19.32 wph wps wo wps wph wo vx wph wps orcom albii wph
      vx wal wps orcom 3bitr4i $.
  $}

  ${
    19.44.1 $e |- F/ x ps $.
    $( Theorem 19.44 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.44 $p |- ( E. x ( ph \/ ps ) <-> ( E. x ph \/ ps ) ) $=
      wph wps wo vx wex wph vx wex wps vx wex wo wph vx wex wps wo wph wps vx
      19.43 wps vx wex wps wph vx wex wps vx 19.44.1 19.9 orbi2i bitri $.
  $}

  ${
    19.45.1 $e |- F/ x ph $.
    $( Theorem 19.45 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.) $)
    19.45 $p |- ( E. x ( ph \/ ps ) <-> ( ph \/ E. x ps ) ) $=
      wph wps wo vx wex wph vx wex wps vx wex wo wph wps vx wex wo wph wps vx
      19.43 wph vx wex wph wps vx wex wph vx 19.45.1 19.9 orbi1i bitri $.
  $}

  ${
    19.41.1 $e |- F/ x ps $.
    $( Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM, 5-Aug-1993.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    19.41 $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      wph wps wa vx wex wph vx wex wps wa wph wps wa vx wex wph vx wex wps vx
      wex wa wph vx wex wps wa wph wps vx 19.40 wps vx wex wps wph vx wex wps
      wps vx 19.41.1 wps id exlimi anim2i syl wps wph vx wex wph wps wa vx wex
      wps wph wph wps wa vx 19.41.1 wps wph pm3.21 eximd impcom impbii $.
  $}

  ${
    19.42.1 $e |- F/ x ph $.
    $( Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM, 18-Aug-1993.) $)
    19.42 $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      wps wph wa vx wex wps vx wex wph wa wph wps wa vx wex wph wps vx wex wa
      wps wph vx 19.42.1 19.41 wph wps vx exancom wph wps vx wex ancom 3bitr4i
      $.
  $}

  $( Swap 1st and 3rd existential quantifiers.  (Contributed by NM,
     9-Mar-1995.) $)
  excom13 $p |- ( E. x E. y E. z ph <-> E. z E. y E. x ph ) $=
    wph vz wex vy wex vx wex wph vz wex vx wex vy wex wph vx wex vz wex vy wex
    wph vx wex vy wex vz wex wph vz wex vx vy excom wph vz wex vx wex wph vx
    wex vz wex vy wph vx vz excom exbii wph vx wex vy vz excom 3bitri $.

  $( Rotate existential quantifiers.  (Contributed by NM, 17-Mar-1995.) $)
  exrot3 $p |- ( E. x E. y E. z ph <-> E. y E. z E. x ph ) $=
    wph vz wex vy wex vx wex wph vx wex vy wex vz wex wph vx wex vz wex vy wex
    wph vx vy vz excom13 wph vx wex vz vy excom bitri $.

  $( Rotate existential quantifiers twice.  (Contributed by NM, 9-Mar-1995.) $)
  exrot4 $p |- ( E. x E. y E. z E. w ph <-> E. z E. w E. x E. y ph ) $=
    wph vw wex vz wex vy wex vx wex wph vy wex vz wex vw wex vx wex wph vy wex
    vx wex vw wex vz wex wph vw wex vz wex vy wex wph vy wex vz wex vw wex vx
    wph vy vz vw excom13 exbii wph vy wex vx vw vz excom13 bitri $.

  ${
    nexr.1 $e |- -. E. x ph $.
    $( Inference from ~ 19.8a .  (Contributed by Jeff Hankins, 26-Jul-2009.) $)
    nexr $p |- -. ph $=
      wph wph vx wex nexr.1 wph vx 19.8a mto $.
  $}

  ${
    nfim1.1 $e |- F/ x ph $.
    nfim1.2 $e |- ( ph -> F/ x ps ) $.
    $( A closed form of ~ nfim .  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 24-Sep-2016.) $)
    nfim1 $p |- F/ x ( ph -> ps ) $=
      wph wps wi vx wph wps wi wph wps vx wal wi wph wps wi vx wal wph wps wps
      vx wal wph wps vx nfim1.2 nfrd a2i wph wps vx nfim1.1 19.21 sylibr nfi $.

    $( A closed form of ~ nfan .  (Contributed by Mario Carneiro,
       3-Oct-2016.) $)
    nfan1 $p |- F/ x ( ph /\ ps ) $=
      wph wps wa vx wph wps wa wph wps vx wal wa wph wps wa vx wal wph wps wps
      vx wal wph wps vx nfim1.2 nfrd imdistani wph wps vx nfim1.1 19.28 sylibr
      nfi $.
  $}

  ${
    exan.1 $e |- ( E. x ph /\ ps ) $.
    $( Place a conjunct in the scope of an existential quantifier.
       (Contributed by NM, 18-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.) $)
    exan $p |- E. x ( ph /\ ps ) $=
      wph vx wex wps vx wal wa wph wps wa vx wex wph vx wex wps wa wph vx wex
      wps vx wal wa vx wph vx wex wps vx wph vx nfe1 19.28 exan.1 mpgbi wph wps
      vx 19.29r ax-mp $.
  $}

  ${
    hbnd.1 $e |- ( ph -> A. x ph ) $.
    hbnd.2 $e |- ( ph -> ( ps -> A. x ps ) ) $.
    $( Deduction form of bound-variable hypothesis builder ~ hbn .
       (Contributed by NM, 3-Jan-2002.) $)
    hbnd $p |- ( ph -> ( -. ps -> A. x -. ps ) ) $=
      wph wps wps vx wal wi vx wal wps wn wps wn vx wal wi wph wps wps vx wal
      wi vx hbnd.1 hbnd.2 alrimih wps vx hbnt syl $.
  $}

  ${
    aaan.1 $e |- F/ y ph $.
    aaan.2 $e |- F/ x ps $.
    $( Rearrange universal quantifiers.  (Contributed by NM, 12-Aug-1993.) $)
    aaan $p |- ( A. x A. y ( ph /\ ps ) <-> ( A. x ph /\ A. y ps ) ) $=
      wph wps wa vy wal vx wal wph wps vy wal wa vx wal wph vx wal wps vy wal
      wa wph wps wa vy wal wph wps vy wal wa vx wph wps vy aaan.1 19.28 albii
      wph wps vy wal vx wps vx vy aaan.2 nfal 19.27 bitri $.
  $}

  ${
    eeor.1 $e |- F/ y ph $.
    eeor.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 8-Aug-1994.) $)
    eeor $p |- ( E. x E. y ( ph \/ ps ) <-> ( E. x ph \/ E. y ps ) ) $=
      wph wps wo vy wex vx wex wph wps vy wex wo vx wex wph vx wex wps vy wex
      wo wph wps wo vy wex wph wps vy wex wo vx wph wps vy eeor.1 19.45 exbii
      wph wps vy wex vx wps vx vy eeor.2 nfex 19.44 bitri $.
  $}

  $( Quantified "excluded middle."  Exercise 9.2a of Boolos, p. 111,
     _Computability and Logic_.  (Contributed by NM, 10-Dec-2000.) $)
  qexmid $p |- E. x ( ph -> A. x ph ) $=
    wph wph vx wal vx wph vx wal vx 19.8a 19.35ri $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
  equs5a $p |- ( E. x ( x = y /\ A. y ph ) -> A. x ( x = y -> ph ) ) $=
    vx vy weq wph vy wal wa vx vy weq wph wi vx wal vx vx vy weq wph wi vx nfa1
    vx vy weq wph vy wal vx vy weq wph wi vx wal wph vx vy ax-11 imp exlimi $.

  $( A property related to substitution that unlike ~ equs5 doesn't require a
     distinctor antecedent.  (Contributed by NM, 2-Feb-2007.) $)
  equs5e $p |- ( E. x ( x = y /\ ph ) -> A. x ( x = y -> E. y ph ) ) $=
    vx vy weq wph wa vx wex vx vy weq wph vy wex wi vx vx vy weq wph wa vx nfe1
    vx vy weq wph wa vx wex vx vy weq wph wn wi vx wal wn vx vy weq wph vy wex
    wi wph vx vy equs3 vx vy weq wph wn wi vx wal wn vx vy weq wph wn vy wal wn
    wph vy wex vx vy weq wph wn vy wal vx vy weq wph wn wi vx wal wph wn vx vy
    ax-11 con3rr3 wph vy df-ex syl6ibr sylbi alrimi $.

  ${
    exlimdd.1 $e |- F/ x ph $.
    exlimdd.2 $e |- F/ x ch $.
    exlimdd.3 $e |- ( ph -> E. x ps ) $.
    exlimdd.4 $e |- ( ( ph /\ ps ) -> ch ) $.
    $( Existential elimination rule of natural deduction.  (Contributed by
       Mario Carneiro, 9-Feb-2017.) $)
    exlimdd $p |- ( ph -> ch ) $=
      wph wps vx wex wch exlimdd.3 wph wps wch vx exlimdd.1 exlimdd.2 wph wps
      wch exlimdd.4 ex exlimd mpd $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.21 of [Margaris] p. 90. _Notational
       convention_:  We sometimes suffix with "v" the label of a theorem
       eliminating a hypothesis such as ` F/ x ph ` in ~ 19.21 via the use of
       distinct variable conditions combined with ~ nfv .  Conversely, we
       sometimes suffix with "f" the label of a theorem introducing such a
       hypothesis to eliminate the need for the distinct variable condition;
       e.g. ~ euf derived from ~ df-eu .  The "f" stands for "not free in"
       which is less restrictive than "does not occur in."  (Contributed by NM,
       5-Aug-1993.) $)
    19.21v $p |- ( A. x ( ph -> ps ) <-> ( ph -> A. x ps ) ) $=
      wph wps vx wph vx nfv 19.21 $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.23 of [Margaris] p. 90.  (Contributed by NM,
       28-Jun-1998.) $)
    19.23v $p |- ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) $=
      wph wps vx wps vx nfv 19.23 $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.23 of [Margaris] p. 90 extended to two variables.
       (Contributed by NM, 10-Aug-2004.) $)
    19.23vv $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x E. y ph -> ps ) ) $=
      wph wps wi vy wal vx wal wph vy wex wps wi vx wal wph vy wex vx wex wps
      wi wph wps wi vy wal wph vy wex wps wi vx wph wps vy 19.23v albii wph vy
      wex wps vx 19.23v bitri $.
  $}

  ${
    $d ph y $.  $d ps x $.
    $( Theorem *11.53 in [WhiteheadRussell] p. 164.  (Contributed by Andrew
       Salmon, 24-May-2011.) $)
    pm11.53 $p |- ( A. x A. y ( ph -> ps ) <-> ( E. x ph -> A. y ps ) ) $=
      wph wps wi vy wal vx wal wph wps vy wal wi vx wal wph vx wex wps vy wal
      wi wph wps wi vy wal wph wps vy wal wi vx wph wps vy 19.21v albii wph wps
      vy wal vx wps vx vy wps vx nfv nfal 19.23 bitri $.
  $}

  ${
    $d x ps $.
    $( Theorem 19.27 of [Margaris] p. 90.  (Contributed by NM, 3-Jun-2004.) $)
    19.27v $p |- ( A. x ( ph /\ ps ) <-> ( A. x ph /\ ps ) ) $=
      wph wps vx wps vx nfv 19.27 $.
  $}

  ${
    $d x ph $.
    $( Theorem 19.28 of [Margaris] p. 90.  (Contributed by NM, 25-Mar-2004.) $)
    19.28v $p |- ( A. x ( ph /\ ps ) <-> ( ph /\ A. x ps ) ) $=
      wph wps vx wph vx nfv 19.28 $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       18-Aug-1993.) $)
    19.36v $p |- ( E. x ( ph -> ps ) <-> ( A. x ph -> ps ) ) $=
      wph wps vx wps vx nfv 19.36 $.
  $}

  ${
    $d x ps $.
    19.36aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.36 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.36aiv $p |- ( A. x ph -> ps ) $=
      wph wps vx wps vx nfv 19.36aiv.1 19.36i $.
  $}

  ${
    $d x ps $.  $d y ph $.
    $( Special case of ~ 19.12 where its converse holds.  (Contributed by NM,
       18-Jul-2001.)  (Revised by Andrew Salmon, 11-Jul-2011.) $)
    19.12vv $p |- ( E. x A. y ( ph -> ps ) <-> A. y E. x ( ph -> ps ) ) $=
      wph wps wi vy wal vx wex wph wps vy wal wi vx wex wph vx wal wps vy wal
      wi wph wps wi vx wex vy wal wph wps wi vy wal wph wps vy wal wi vx wph
      wps vy 19.21v exbii wph wps vy wal vx wps vx vy wps vx nfv nfal 19.36 wph
      wps wi vx wex vy wal wph vx wal wps wi vy wal wph vx wal wps vy wal wi
      wph wps wi vx wex wph vx wal wps wi vy wph wps vx 19.36v albii wph vx wal
      wps vy wph vy vx wph vy nfv nfal 19.21 bitr2i 3bitri $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.37v $p |- ( E. x ( ph -> ps ) <-> ( ph -> E. x ps ) ) $=
      wph wps vx wph vx nfv 19.37 $.
  $}

  ${
    $d x ph $.
    19.37aiv.1 $e |- E. x ( ph -> ps ) $.
    $( Inference from Theorem 19.37 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.37aiv $p |- ( ph -> E. x ps ) $=
      wph wps wi vx wex wph wps vx wex wi 19.37aiv.1 wph wps vx 19.37v mpbi $.
  $}

  ${
    $d x ps $.
    $( Special case of Theorem 19.41 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.41v $p |- ( E. x ( ph /\ ps ) <-> ( E. x ph /\ ps ) ) $=
      wph wps vx wps vx nfv 19.41 $.
  $}

  ${
    $d x ps $.  $d y ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)
    19.41vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x E. y ph /\ ps ) ) $=
      wph wps wa vy wex vx wex wph vy wex wps wa vx wex wph vy wex vx wex wps
      wa wph wps wa vy wex wph vy wex wps wa vx wph wps vy 19.41v exbii wph vy
      wex wps vx 19.41v bitri $.
  $}

  ${
    $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 30-Apr-1995.) $)
    19.41vvv $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                     ( E. x E. y E. z ph /\ ps ) ) $=
      wph wps wa vz wex vy wex vx wex wph vz wex vy wex wps wa vx wex wph vz
      wex vy wex vx wex wps wa wph wps wa vz wex vy wex wph vz wex vy wex wps
      wa vx wph wps vy vz 19.41vv exbii wph vz wex vy wex wps vx 19.41v bitri
      $.
  $}

  ${
    $d w ps $.  $d x ps $.  $d y ps $.  $d z ps $.
    $( Theorem 19.41 of [Margaris] p. 90 with 4 quantifiers.  (Contributed by
       FL, 14-Jul-2007.) $)
    19.41vvvv $p |- ( E. w E. x E. y E. z ( ph /\ ps ) <->
                     ( E. w E. x E. y E. z ph /\ ps ) ) $=
      wph wps wa vz wex vy wex vx wex vw wex wph vz wex vy wex vx wex wps wa vw
      wex wph vz wex vy wex vx wex vw wex wps wa wph wps wa vz wex vy wex vx
      wex wph vz wex vy wex vx wex wps wa vw wph wps vx vy vz 19.41vvv exbii
      wph vz wex vy wex vx wex wps vw 19.41v bitri $.
  $}

  ${
    $d x ph $.
    $( Special case of Theorem 19.42 of [Margaris] p. 90.  (Contributed by NM,
       5-Aug-1993.) $)
    19.42v $p |- ( E. x ( ph /\ ps ) <-> ( ph /\ E. x ps ) ) $=
      wph wps vx wph vx nfv 19.42 $.
  $}

  ${
    $d y ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
    exdistr $p |- ( E. x E. y ( ph /\ ps ) <-> E. x ( ph /\ E. y ps ) ) $=
      wph wps wa vy wex wph wps vy wex wa vx wph wps vy 19.42v exbii $.
  $}

  ${
    $d x ph $.  $d y ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 2 quantifiers.  (Contributed by
       NM, 16-Mar-1995.) $)
    19.42vv $p |- ( E. x E. y ( ph /\ ps ) <-> ( ph /\ E. x E. y ps ) ) $=
      wph wps wa vy wex vx wex wph wps vy wex wa vx wex wph wps vy wex vx wex
      wa wph wps vx vy exdistr wph wps vy wex vx 19.42v bitri $.
  $}

  ${
    $d x ph $.  $d y ph $.  $d z ph $.
    $( Theorem 19.42 of [Margaris] p. 90 with 3 quantifiers.  (Contributed by
       NM, 21-Sep-2011.) $)
    19.42vvv $p |- ( E. x E. y E. z ( ph /\ ps )
                       <-> ( ph /\ E. x E. y E. z ps ) ) $=
      wph wps wa vz wex vy wex vx wex wph wps vz wex vy wex wa vx wex wph wps
      vz wex vy wex vx wex wa wph wps wa vz wex vy wex wph wps vz wex vy wex wa
      vx wph wps vy vz 19.42vv exbii wph wps vz wex vy wex vx 19.42v bitri $.
  $}

  ${
    $d y ph $.  $d z ph $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       17-Mar-1995.) $)
    exdistr2 $p |- ( E. x E. y E. z ( ph /\ ps ) <->
                   E. x ( ph /\ E. y E. z ps ) ) $=
      wph wps wa vz wex vy wex wph wps vz wex vy wex wa vx wph wps vy vz
      19.42vv exbii $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d z ps $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    3exdistr $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ch ) ) ) $=
      wph wps wch w3a vz wex vy wex wph wps wch vz wex wa vy wex wa vx wph wps
      wch w3a vz wex vy wex wph wps wch wa wa vz wex vy wex wph wps wch wa vz
      wex vy wex wa wph wps wch vz wex wa vy wex wa wph wps wch w3a wph wps wch
      wa wa vy vz wph wps wch 3anass 2exbii wph wps wch wa vy vz 19.42vv wps
      wch wa vz wex vy wex wps wch vz wex wa vy wex wph wps wch vy vz exdistr
      anbi2i 3bitri exbii $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d w ph $.  $d z ps $.  $d w ps $.  $d w ch $.
    $( Distribution of existential quantifiers.  (Contributed by NM,
       9-Mar-1995.) $)
    4exdistr $p |- ( E. x E. y E. z E. w ( ( ph /\ ps ) /\ ( ch /\ th ) ) <->
                E. x ( ph /\ E. y ( ps /\ E. z ( ch /\ E. w th ) ) ) ) $=
      wph wps wa wch wth wa wa vw wex vz wex vy wex wph wps wch wth vw wex wa
      vz wex wa vy wex wa vx wph wps wa wch wth wa wa vw wex vz wex vy wex wph
      wps wch wth vw wex wa vz wex wa wa vy wex wph wps wch wth vw wex wa vz
      wex wa vy wex wa wph wps wa wch wth wa wa vw wex vz wex wph wps wch wth
      vw wex wa vz wex wa wa vy wph wps wa wch wth wa wa vw wex vz wex wph wps
      wch wth vw wex wa wa wa vz wex wph wps wch wth vw wex wa wa vz wex wa wph
      wps wch wth vw wex wa vz wex wa wa wph wps wa wch wth wa wa vw wex wph
      wps wch wth vw wex wa wa wa vz wph wps wa wch wth wa wa vw wex wph wps
      wch wth wa wa wa vw wex wph wps wch wth vw wex wa wa wa wph wps wa wch
      wth wa wa wph wps wch wth wa wa wa vw wph wps wch wth wa anass exbii wph
      wps wch wth wa wa wa vw wex wph wps wch wth wa wa vw wex wa wph wps wch
      wth wa vw wex wa wa wph wps wch wth vw wex wa wa wa wph wps wch wth wa wa
      vw 19.42v wps wch wth wa wa vw wex wps wch wth wa vw wex wa wph wps wch
      wth wa vw 19.42v anbi2i wps wch wth wa vw wex wa wps wch wth vw wex wa wa
      wph wch wth wa vw wex wch wth vw wex wa wps wch wth vw 19.42v anbi2i
      anbi2i 3bitri bitri exbii wph wps wch wth vw wex wa wa vz 19.42v wps wch
      wth vw wex wa wa vz wex wps wch wth vw wex wa vz wex wa wph wps wch wth
      vw wex wa vz 19.42v anbi2i 3bitri exbii wph wps wch wth vw wex wa vz wex
      wa vy 19.42v bitri exbii $.
  $}

  ${
    eean.1 $e |- F/ y ph $.
    eean.2 $e |- F/ x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 27-Oct-2010.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    eean $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      wph wps wa vy wex vx wex wph wps vy wex wa vx wex wph vx wex wps vy wex
      wa wph wps wa vy wex wph wps vy wex wa vx wph wps vy eean.1 19.42 exbii
      wph wps vy wex vx wps vx vy eean.2 nfex 19.41 bitri $.
  $}

  ${
    $d y ph $.  $d x ps $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.) $)
    eeanv $p |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) ) $=
      wph wps vx vy wph vy nfv wps vx nfv eean $.
  $}

  ${
    $d y ph $.  $d z ph $.  $d x z ps $.  $d x y ch $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 26-Jul-1995.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    eeeanv $p |- ( E. x E. y E. z ( ph /\ ps /\ ch ) <->
                 ( E. x ph /\ E. y ps /\ E. z ch ) ) $=
      wph wps wch w3a vz wex vy wex vx wex wph wps wa wch wa vz wex vy wex vx
      wex wph wps wa vy wex wch vz wex wa vx wex wph vx wex wps vy wex wch vz
      wex w3a wph wps wch w3a wph wps wa wch wa vx vy vz wph wps wch df-3an
      3exbii wph wps wa wch wa vz wex vy wex wph wps wa vy wex wch vz wex wa vx
      wph wps wa wch vy vz eeanv exbii wph wps wa vy wex vx wex wch vz wex wa
      wph vx wex wps vy wex wa wch vz wex wa wph wps wa vy wex wch vz wex wa vx
      wex wph vx wex wps vy wex wch vz wex w3a wph wps wa vy wex vx wex wph vx
      wex wps vy wex wa wch vz wex wph wps vx vy eeanv anbi1i wph wps wa vy wex
      wch vz wex vx 19.41v wph vx wex wps vy wex wch vz wex df-3an 3bitr4i
      3bitri $.
  $}

  ${
    $d z ph $.  $d w ph $.  $d x ps $.  $d y ps $.  $d y z $.  $d w x $.
    $( Rearrange existential quantifiers.  (Contributed by NM, 31-Jul-1995.) $)
    ee4anv $p |- ( E. x E. y E. z E. w ( ph /\ ps ) <->
                  ( E. x E. y ph /\ E. z E. w ps ) ) $=
      wph wps wa vw wex vz wex vy wex vx wex wph wps wa vw wex vy wex vz wex vx
      wex wph vy wex wps vw wex wa vz wex vx wex wph vy wex vx wex wps vw wex
      vz wex wa wph wps wa vw wex vz wex vy wex wph wps wa vw wex vy wex vz wex
      vx wph wps wa vw wex vy vz excom exbii wph wps wa vw wex vy wex wph vy
      wex wps vw wex wa vx vz wph wps vy vw eeanv 2exbii wph vy wex wps vw wex
      vx vz eeanv 3bitri $.
  $}

  ${
    $d x ph $.
    nexdv.1 $e |- ( ph -> -. ps ) $.
    $( Deduction for generalization rule for negated wff.  (Contributed by NM,
       5-Aug-1993.) $)
    nexdv $p |- ( ph -> -. E. x ps ) $=
      wph wps vx wph vx nfv nexdv.1 nexd $.
  $}

  $( One of the two equality axioms of standard predicate calculus, called
     substitutivity of equality.  (The other one is ~ stdpc6 .)  Translated to
     traditional notation, it can be
     read:  " ` x = y -> ( ph ( x , x ) -> ph ( x , y ) ) ` , provided that
     ` y ` is free for ` x ` in ` ph ( x , x ) ` ."  Axiom 7 of [Mendelson]
     p. 95.  (Contributed by NM, 15-Feb-2005.) $)
  stdpc7 $p |- ( x = y -> ( [ x / y ] ph -> ph ) ) $=
    wph vy vx wsb wph wi vy vx wph vy vx sbequ2 equcoms $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ1 $p |- ( x = y -> ( ph -> [ y / x ] ph ) ) $=
    vx vy weq wph wph vx vy wsb vx vy weq wph wa vx vy weq wph wi vx vy weq wph
    wa vx wex wph vx vy wsb vx vy weq wph pm3.4 vx vy weq wph wa vx 19.8a wph
    vx vy df-sb sylanbrc ex $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ12 $p |- ( x = y -> ( ph <-> [ y / x ] ph ) ) $=
    vx vy weq wph wph vx vy wsb wph vx vy sbequ1 wph vx vy sbequ2 impbid $.

  $( An equality theorem for substitution.  (Contributed by NM, 6-Oct-2004.)
     (Proof shortened by Andrew Salmon, 21-Jun-2011.) $)
  sbequ12r $p |- ( x = y -> ( [ x / y ] ph <-> ph ) ) $=
    wph vy vx wsb wph wb vy vx vy vx weq wph wph vy vx wsb wph vy vx sbequ12
    bicomd equcoms $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequ12a $p |- ( x = y -> ( [ y / x ] ph <-> [ x / y ] ph ) ) $=
    vx vy weq wph wph vx vy wsb wph vy vx wsb wph vx vy sbequ12 wph wph vy vx
    wsb wb vy vx wph vy vx sbequ12 equcoms bitr3d $.

  $( An identity theorem for substitution.  Remark 9.1 in [Megill] p. 447 (p.
     15 of the preprint).  (Contributed by NM, 5-Aug-1993.) $)
  sbid $p |- ( [ x / x ] ph <-> ph ) $=
    wph wph vx vx wsb vx vx weq wph wph vx vx wsb wb vx equid wph vx vx sbequ12
    ax-mp bicomi $.

  $( A version of ~ sb4 that doesn't require a distinctor antecedent.
     (Contributed by NM, 2-Feb-2007.) $)
  sb4a $p |- ( [ y / x ] A. y ph -> A. x ( x = y -> ph ) ) $=
    wph vy wal vx vy wsb vx vy weq wph vy wal wa vx wex vx vy weq wph wi vx wal
    wph vy wal vx vy sb1 wph vx vy equs5a syl $.

  $( One direction of a simplified definition of substitution that unlike ~ sb4
     doesn't require a distinctor antecedent.  (Contributed by NM,
     2-Feb-2007.) $)
  sb4e $p |- ( [ y / x ] ph -> A. x ( x = y -> E. y ph ) ) $=
    wph vx vy wsb vx vy weq wph wa vx wex vx vy weq wph vy wex wi vx wal wph vx
    vy sb1 wph vx vy equs5e syl $.


