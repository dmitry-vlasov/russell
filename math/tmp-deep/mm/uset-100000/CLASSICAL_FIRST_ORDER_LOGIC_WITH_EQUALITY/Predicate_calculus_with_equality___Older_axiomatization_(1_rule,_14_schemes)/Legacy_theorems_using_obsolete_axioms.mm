
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Rederive_new_axioms_from_old__theorems_ax5_,_ax6_,_ax9from9o_,_ax11_,_ax12.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
               Legacy theorems using obsolete axioms

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  These theorems were mostly intended to study properties of the older axiom
  schemes and are not useful outside of this section.  They should not be
  used outside of this section.  They may be deleted when they are deemed to no
  longer be of interest.

$)


  ${
    $d x ph $.
    $( Axiom to quantify a variable over a formula in which it does not occur.
       Axiom C5 in [Megill] p. 444 (p. 11 of the preprint).  Also appears as
       Axiom B6 (p. 75) of system S2 of [Tarski] p. 77 and Axiom C5-1 of
       [Monk2] p. 113.

       (This theorem simply repeats ~ ax-17 so that we can include the
       following note, which applies only to the obsolete axiomatization.)

       This axiom is _logically_ redundant in the (logically complete)
       predicate calculus axiom system consisting of ~ ax-gen , ~ ax-5o ,
       ~ ax-4 , ~ ax-7 , ~ ax-6o , ~ ax-8 , ~ ax-12o , ~ ax-9o , ~ ax-10o ,
       ~ ax-13 , ~ ax-14 , ~ ax-15 , ~ ax-11o , and ~ ax-16 : in that system,
       we can derive any instance of ~ ax-17 not containing wff variables by
       induction on formula length, using ~ ax17eq and ~ ax17el for the basis
       together ~ hbn , ~ hbal , and ~ hbim .  However, if we omit this axiom,
       our development would be quite inconvenient since we could work only
       with specific instances of wffs containing no wff variables - this axiom
       introduces the concept of a set variable not occurring in a wff (as
       opposed to just two set variables being distinct).  (Contributed by NM,
       19-Aug-2017.)  (New usage is discouraged.)  (Proof modification
       discouraged.) $)
    ax17o $p |- ( ph -> A. x ph ) $=
      wph vx ax-17 $.
  $}

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.  This
     is often an axiom of equality in textbook systems, but we don't need it as
     an axiom since it can be proved from our other axioms (although the proof,
     as you can see below, is not as obvious as you might think).  This proof
     uses only axioms without distinct variable conditions and thus requires no
     dummy variables.  A simpler proof, similar to Tarki's, is possible if we
     make use of ~ ax-17 ; see the proof of ~ equid .  See ~ equid1ALT for an
     alternate proof.  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  equid1 $p |- x = x $=
    vx vx weq vx wal wn vx wal vx vx weq vx vx weq vx wal wn vx wal vx vx weq
    vx vx weq vx wal wi vx wal vx vx weq vx vx weq vx wal wn vx wal vx vx weq
    vx vx weq vx wal wi wi vx vx weq vx wal wn vx wal vx vx weq vx vx weq vx
    wal wi vx wal wi vx vx vx weq vx wal wn vx vx weq vx vx weq vx wal wi vx
    ax-5o vx vx weq vx wal wn vx wal vx vx weq vx wal wn vx vx weq vx wal wn vx
    vx weq vx vx weq vx wal wi vx vx weq vx wal wn vx ax-4 vx vx weq vx wal wn
    vx ax-4 vx vx vx ax-12o sylc mpg vx vx weq vx vx ax-9o syl vx vx weq vx
    ax-6o pm2.61i $.

  ${
    sps-o.1 $e |- ( ph -> ps ) $.
    $( Generalization of antecedent.  (Contributed by NM, 5-Aug-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    sps-o $p |- ( A. x ph -> ps ) $=
      wph vx wal wph wps wph vx ax-4 sps-o.1 syl $.
  $}

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof does not use
     ~ ax-9o .)  (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf
     Lammen, 23-Mar-2014.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  hbequid $p |- ( x = x -> A. y x = x ) $=
    vy vx weq vy wal vy vx weq vy wal vx vx weq vx vx weq vy wal wi vx vx vy
    ax-12o vy vx weq vy wal vx vx weq vy wal vx vx weq vy vx weq vx vx weq vy
    vy vx weq vx vx weq vy vx vx ax-8 pm2.43i alimi a1d vy vx weq vy wal vx vx
    weq vy wal vx vx weq vy vx weq vx vx weq vy vy vx weq vx vx weq vy vx vx
    ax-8 pm2.43i alimi a1d pm2.61ii $.

  $( Bound-variable hypothesis builder for ` x = x ` .  This theorem tells us
     that any variable, including ` x ` , is effectively not free in
     ` x = x ` , even though ` x ` is technically free according to the
     traditional definition of free variable.  (The proof uses only ~ ax-5 ,
     ~ ax-8 , ~ ax-12o , and ~ ax-gen .  This shows that this can be proved
     without ~ ax9 , even though the theorem ~ equid cannot be.  A shorter
     proof using ~ ax9 is obtainable from ~ equid and ~ hbth .)  Remark added
     2-Dec-2015 NM:  This proof does implicitly use ~ ax9v , which is used for
     the derivation of ~ ax12o , unless we consider ~ ax-12o the starting axiom
     rather than ~ ax-12 .  (Contributed by NM, 13-Jan-2011.)  (Revised by
     Mario Carneiro, 12-Oct-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfequid-o $p |- F/ y x = x $=
    vx vx weq vy vx vy hbequid nfi $.

  $( Proof of a single axiom that can replace ~ ax-4 and ~ ax-6o .  See
     ~ ax46to4 and ~ ax46to6 for the re-derivation of those axioms.
     (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax46 $p |- ( ( A. x -. A. x ph -> A. x ph ) -> ph ) $=
    wph vx wal wn vx wal wph vx wal wph wph vx ax-6o wph vx ax-4 ja $.

  $( Re-derivation of ~ ax-4 from ~ ax46 .  Only propositional calculus is used
     for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax46to4 $p |- ( A. x ph -> ph ) $=
    wph vx wal wph vx wal wn vx wal wph vx wal wi wph wph vx wal wph vx wal wn
    vx wal ax-1 wph vx ax46 syl $.

  $( Re-derivation of ~ ax-6o from ~ ax46 .  Only propositional calculus is
     used for the re-derivation.  (Contributed by Scott Fenton, 12-Sep-2005.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax46to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    wph vx wal wn vx wal wn wph vx wal wn vx wal wph vx wal wi wph wph vx wal
    wn vx wal wph vx wal pm2.21 wph vx ax46 syl $.

  $( Proof of a single axiom that can replace both ~ ax-6o and ~ ax-7 .  See
     ~ ax67to6 and ~ ax67to7 for the re-derivation of those axioms.
     (Contributed by NM, 18-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax67 $p |- ( -. A. x -. A. y A. x ph -> A. y ph ) $=
    wph vx wal vy wal wn vx wal wn wph vy wal vx wal wn vx wal wn wph vy wal
    wph vy wal vx wal wn vx wal wph vx wal vy wal wn vx wal wph vy wal vx wal
    wn wph vx wal vy wal wn vx wph vx wal vy wal wph vy wal vx wal wph vy vx
    ax-7 con3i alimi con3i wph vy wal vx ax-6o syl $.

  $( ` x ` is not free in ` A. x ph ` .  (Contributed by Mario Carneiro,
     11-Aug-2016.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  nfa1-o $p |- F/ x A. x ph $=
    wph vx wal vx wph vx hba1-o nfi $.

  $( Re-derivation of ~ ax-6o from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax67to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    wph vx wal wn vx wal wn wph vx wal vx wal wn vx wal wn wph vx wal wph wph
    vx wal vx wal wn vx wal wph vx wal wn vx wal wph vx wal vx wal wn wph vx
    wal wn vx wph vx wal wph vx wal vx wal wph vx hba1-o con3i alimi con3i wph
    vx vx ax67 wph vx ax-4 3syl $.

  $( Re-derivation of ~ ax-7 from ~ ax67 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax67to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    wph vy wal vx wal wph vy wal vx wal wn vy wal wn vy wal wph vx wal vy wal
    wph vy wal vx wal wn vy wal wn vy wal wph vy wal vx wal wph vy wal vx wal
    wn vy ax67to6 con4i wph vy wal vx wal wn vy wal wn wph vx wal vy wph vy vx
    ax67 alimi syl $.

  $( Proof of a single axiom that can replace ~ ax-4 , ~ ax-6o , and ~ ax-7 in
     a subsystem that includes these axioms plus ~ ax-5o and ~ ax-gen (and
     propositional calculus).  See ~ ax467to4 , ~ ax467to6 , and ~ ax467to7 for
     the re-derivation of those axioms.  This theorem extends the idea in Scott
     Fenton's ~ ax46 .  (Contributed by NM, 18-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax467 $p |- ( ( A. x A. y -. A. x A. y ph -> A. x ph ) -> ph ) $=
    wph vy wal vx wal wn vy wal vx wal wph vx wal wph wph vy wal wph wph vy wal
    vx wal wn vy wal vx wal wph vy ax-4 wph vy wal wn wph vy wal wn vy wal wph
    vy wal vx wal wn vx wal vy wal wph vy wal vx wal wn vy wal vx wal wph vy
    ax6 wph vy wal wn wph vy wal vx wal wn vx wal vy wph vy wal vx wal wn vx
    wal wph vy wal wph vy wal vx ax-6o con1i alimi wph vy wal vx wal wn vy vx
    ax-7 3syl nsyl4 wph vx ax-4 ja $.

  $( Re-derivation of ~ ax-4 from ~ ax467 .  Only propositional calculus is
     used by the re-derivation.  (Contributed by NM, 19-Nov-2006.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax467to4 $p |- ( A. x ph -> ph ) $=
    wph vx wal wph vx wal vx wal wn vx wal vx wal wph vx wal wi wph wph vx wal
    wph vx wal vx wal wn vx wal vx wal ax-1 wph vx vx ax467 syl $.

  $( Re-derivation of ~ ax-6o from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 .  (Contributed by NM,
     19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax467to6 $p |- ( -. A. x -. A. x ph -> ph ) $=
    wph vx wal wn vx wal wn wph vx wal vx wal wn vx wal vx wal wn wph vx wal vx
    wal wn vx wal vx wal wph vx wal wi wph wph vx wal vx wal wn vx wal vx wal
    wph vx wal wn vx wal wph vx wal vx wal wn vx wal wph vx wal wn vx wal vx
    wph vx wal vx wal wn wph vx wal wn vx wph vx wal wph vx wal vx wal wph vx
    hba1-o con3i alimi sps-o con3i wph vx wal vx wal wn vx wal vx wal wph vx
    wal pm2.21 wph vx vx ax467 3syl $.

  $( Re-derivation of ~ ax-7 from ~ ax467 .  Note that ~ ax-6o and ~ ax-7 are
     not used by the re-derivation.  The use of ~ alimi (which uses ~ ax-4 ) is
     allowed since we have already proved ~ ax467to4 .  (Contributed by NM,
     19-Nov-2006.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax467to7 $p |- ( A. x A. y ph -> A. y A. x ph ) $=
    wph vy wal vx wal wph vy wal vx wal wn vy wal wn vy wal wph vx wal vy wal
    wph vy wal vx wal wn vy wal wn vy wal wph vy wal vx wal wph vy wal vx wal
    wn vy ax467to6 con4i wph vy wal vx wal wn vy wal wn wph vx wal vy wph vy
    wal vx wal wn vy wal vx wal wn vx wal wph vx wal wph vy wal vx wal wn vy
    wal wph vy wal vx wal wn vy wal vx wal wn wph vx wph vy wal vx wal wn vy
    wal vx wal wn wph vy wal vx wal wn vy wal vx wal wph vx wal wi wph wph vy
    wal vx wal wn vy wal vx wal wph vx wal pm2.21 wph vx vy ax467 syl alimi wph
    vy wal vx wal wn vy wal vx ax467to6 nsyl4 alimi syl $.

  $( ~ equid with existential quantifier without using ~ ax-4 or ~ ax-17 .
     (Contributed by NM, 13-Jan-2011.)  (Proof shortened by Wolf Lammen,
     27-Feb-2014.)  (Proof modification is discouraged.) $)
  equidqe $p |- -. A. y -. x = x $=
    vx vx weq wn vy wal vy vx weq wn vy wal vy vx ax9from9o vx vx weq wn vy vx
    weq wn vy vy vx weq vx vx weq vy vx weq vx vx weq vy vx vx ax-8 pm2.43i
    con3i alimi mto $.

  $( A special case of ~ ax-4 without using ~ ax-4 or ~ ax-17 .  (Contributed
     by NM, 13-Jan-2011.)  (Proof modification is discouraged.) $)
  ax4sp1 $p |- ( A. y -. x = x -> -. x = x ) $=
    vx vx weq wn vy wal vx vx weq wn vx vy equidqe pm2.21i $.

  $( ~ equid with universal quantifier without using ~ ax-4 or ~ ax-17 .
     (Contributed by NM, 13-Jan-2011.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equidq $p |- A. y x = x $=
    vx vx weq vy wal vx vx weq wn vy wal vx vy equidqe vx vx weq vy wal wn vx
    vx weq wn vy vx vx weq vy ax6 vx vx weq vx vx weq vy wal vx vy hbequid
    con3i alrimih mt3 $.

  $( Identity law for equality (reflexivity).  Lemma 6 of [Tarski] p. 68.
     Alternate proof of ~ equid1 from older axioms ~ ax-6o and ~ ax-9o .
     (Contributed by NM, 5-Aug-1993.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  equid1ALT $p |- x = x $=
    vx vx weq vx wal wn vx wal vx vx weq vx vx weq vx wal wn vx wal vx vx weq
    vx vx weq vx wal wi vx wal vx vx weq vx vx weq vx wal wn vx vx weq vx vx
    weq vx wal wi vx vx vx weq vx wal wn vx vx weq vx vx weq vx wal wi vx vx vx
    ax-12o pm2.43i alimi vx vx weq vx vx ax-9o syl vx vx weq vx ax-6o pm2.61i
    $.

  $( Rederivation of ~ ax-10 from original version ~ ax-10o .  See theorem
     ~ ax10o for the derivation of ~ ax-10o from ~ ax-10 .

     This theorem should not be referenced in any proof.  Instead, use ~ ax-10
     above so that uses of ~ ax-10 can be more easily identified, or use
     ~ aecom-o when this form is needed for studies involving ~ ax-10o and
     omitting ~ ax-17 .  (Contributed by NM, 16-May-2008.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax10from10o $p |- ( A. x x = y -> A. y y = x ) $=
    vx vy weq vx wal vx vy weq vy wal vy vx weq vy wal vx vy weq vx wal vx vy
    weq vy wal vx vy weq vx vy ax-10o pm2.43i vx vy weq vy vx weq vy vx vy
    equcomi alimi syl $.

  ${
    nalequcoms-o.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  Version of
       ~ naecoms using ~ ax-10o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    naecoms-o $p |- ( -. A. y y = x -> ph ) $=
      wph vy vx weq vy wal vx vy weq vx wal vy vx weq vy wal wph vx vy aecom-o
      nalequcoms-o.1 nsyl4 con1i $.
  $}

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  Version of ~ hbnae
     using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  hbnae-o $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    vx vy weq vx wal vz vx vy vz hbae-o hbn $.

  ${
    dvelimf-o.1 $e |- ( ph -> A. x ph ) $.
    dvelimf-o.2 $e |- ( ps -> A. z ps ) $.
    dvelimf-o.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Proof of ~ dvelimh that uses ~ ax-10o but not ~ ax-11o , ~ ax-10 , or
       ~ ax-11 .  Version of ~ dvelimh using ~ ax-10o instead of ~ ax10o .
       (Contributed by NM, 12-Nov-2002.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dvelimf-o $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      vx vy weq vx wal wn vz vy weq wph wi vz wal vz vy weq wph wi vz wal vx
      wal wps wps vx wal vx vz weq vx wal vx vy weq vx wal wn vz vy weq wph wi
      vz wal vz vy weq wph wi vz wal vx wal wi wi vx vz weq vx wal vz vy weq
      wph wi vz wal vz vy weq wph wi vz wal vx wal wi vx vy weq vx wal wn vz vy
      weq wph wi vz wal vz vy weq wph wi vz wal vz wal vx vz weq vx wal vz vy
      weq wph wi vz wal vx wal vz vy weq wph wi vz hba1-o vz vy weq wph wi vz
      wal vz wal vz vy weq wph wi vz wal vx wal wi vz vx vz vy weq wph wi vz
      wal vz vx ax-10o aecoms-o syl5 a1d vx vz weq vx wal wn vx vy weq vx wal
      wn vz vy weq wph wi vz wal vz vy weq wph wi vz wal vx wal wi vx vz weq vx
      wal wn vx vy weq vx wal wn wa vz vy weq wph wi vx vz vx vz weq vx wal wn
      vx vy weq vx wal wn vz vx vz vz hbnae-o vx vy vz hbnae-o hban vx vz weq
      vx wal wn vx vy weq vx wal wn wa vz vy weq wph vx vx vz weq vx wal wn vx
      vy weq vx wal wn vx vx vz vx hbnae-o vx vy vx hbnae-o hban vx vz weq vx
      wal wn vx vy weq vx wal wn vz vy weq vz vy weq vx wal wi vz vy vx ax-12o
      imp wph wph vx wal wi vx vz weq vx wal wn vx vy weq vx wal wn wa
      dvelimf-o.1 a1i hbimd hbald ex pm2.61i wph wps vz vy dvelimf-o.2
      dvelimf-o.3 equsalh vz vy weq wph wi vz wal wps vx wph wps vz vy
      dvelimf-o.2 dvelimf-o.3 equsalh albii 3imtr3g $.
  $}

  ${
    dral2-o.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral2 using ~ ax-10o .  (Contributed by NM, 27-Feb-2005.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dral2-o $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      vx vy weq vx wal wph wps vz vx vy vz hbae-o dral2-o.1 albidh $.
  $}

  ${
    $d t u v $.  $d t u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent, proved without using ~ ax-16 .  Version of ~ aev using
       ~ ax-10o .  (Contributed by NM, 8-Nov-2006.)  (Proof shortened by Andrew
       Salmon, 21-Jun-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    aev-o $p |- ( A. x x = y -> A. z w = v ) $=
      vx vy weq vx wal vw vv weq vz vx vy vz hbae-o vx vy weq vx wal vt vy weq
      vt wal vu vv weq vu wal vw vv weq vx vy weq vx wal vt vy weq vt vx vy vt
      hbae-o vx vy weq vt vy weq vx vt vx vt vy ax-8 spimv alrimih vt vy weq vt
      wal vt vu weq vt wal vv vu weq vv wal vu vv weq vu wal vt vy weq vt vu
      weq vt vt vu weq vy vt vy vt weq vt vu weq vy vu vy vu weq vy vt weq vu
      vt weq vt vu weq vy vu vt ax-8 vu vt equcomi syl6 spimv aecoms-o a5i-o vt
      vu weq vt wal vv vu weq vv vt vu vv hbae-o vt vu weq vv vu weq vt vv vt
      vv vu ax-8 spimv alrimih vv vu aecom-o 3syl vu vv weq vw vv weq vu vw vu
      vw vv ax-8 spimv 3syl alrimih $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  (This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.  Do not use it for later proofs - use ~ ax-17 instead, to
       avoid reference to the redundant axiom ~ ax-16 .)  (Contributed by NM,
       5-Aug-1993.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax17eq $p |- ( x = y -> A. z x = y ) $=
      vz vx weq vz wal vz vy weq vz wal vx vy weq vx vy weq vz wal wi vx vy vz
      ax-12o vx vy weq vz vx ax-16 vx vy weq vz vy ax-16 pm2.61ii $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq2 using ~ ax-11o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dveeq2-o $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      vz vw weq vz vy weq vx vy vw vz vw weq vx ax-17 vz vy weq vw ax-17 vw vy
      vz equequ2 dvelimf-o $.

    $( Version of ~ dveeq2 using ~ ax-16 instead of ~ ax-17 .  TO DO:  Recover
       proof from older set.mm to remove use of ~ ax-17 .  (Contributed by NM,
       29-Apr-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveeq2-o16 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      vz vw weq vz vy weq vx vy vw vz vw vx ax17eq vw vy vz equequ2 dvelimALT
      $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  Version of ~ a16g using ~ ax-10o .
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    a16g-o $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      vx vy weq vx wal vz vx weq vz wal wph wph vx wal wph vz wal vx vy vz vz
      vx aev-o wph vx vy ax-16 vz vx weq vz wal wph vz wal wph vx wal wph wph
      vz vx vz vx weq vz wal wph biidd dral1-o biimprd sylsyld $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.  Version
       of ~ dveeq1 using ax-10o .  (Contributed by NM, 2-Jan-2002.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    dveeq1-o $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      vw vz weq vy vz weq vx vy vw vw vz weq vx ax-17 vy vz weq vw ax-17 vw vy
      vz equequ1 dvelimf-o $.

    $( Version of ~ dveeq1 using ~ ax-16 instead of ~ ax-17 .  (Contributed by
       NM, 29-Apr-2008.)  TO DO:  Recover proof from older set.mm to remove use
       of ~ ax-17 .  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveeq1-o16 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      vw vz weq vy vz weq vx vy vw vw vz vx ax17eq vy vz vw ax17eq vw vy vz
      equequ1 dvelimh $.
  $}

  ${
    $d x z $.  $d y z $.
    $( Theorem to add distinct quantifier to atomic formula.  This theorem
       demonstrates the induction basis for ~ ax-17 considered as a
       metatheorem.)  (Contributed by NM, 5-Aug-1993.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax17el $p |- ( x e. y -> A. z x e. y ) $=
      vz vx weq vz wal vz vy weq vz wal vx vy wel vx vy wel vz wal wi vx vy vz
      ax-15 vx vy wel vz vx ax-16 vx vy wel vz vy ax-16 pm2.61ii $.
  $}

  ${
    $d x z w $.
    $( This theorem shows that, given ~ ax-16 , we can derive a version of
       ~ ax-10 .  However, it is weaker than ~ ax-10 because it has a distinct
       variable requirement.  (Contributed by Andrew Salmon, 27-Jul-2011.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax10-16 $p |- ( A. x x = z -> A. z z = x ) $=
      vx vz weq vx wal vx vw weq vx vw weq vx wal wi vw wal vx wal vz vw weq vz
      vw weq vz wal wi vw wal vz wal vz vx weq vz wal vx vz weq vx vw weq vx vw
      weq vx wal wi vw wal vx vx vz weq vx wal vx vw weq vx vw weq vx wal wi vw
      vx vw weq vx vz ax-16 alrimiv a5i-o vx vw weq vx vw weq vx wal wi vw wal
      vx wal vz vw weq vz vw weq vz wal wi vw wal vz wal vx vw weq vx vw weq vx
      wal wi vw wal vz vw weq vz vw weq vz wal wi vw wal vx vz vx vz weq vx vw
      weq vx vw weq vx wal wi vz vw weq vz vw weq vz wal wi vw vx vz weq vx vw
      weq vz vw weq vx vw weq vx wal vz vw weq vz wal vx vz vw equequ1 vx vw
      weq vx wal vz vw weq vz wal wb vx vz weq vx vw weq vz vw weq vx vz vx vz
      vw equequ1 cbvalv a1i imbi12d albidv cbvalv biimpi vz vw weq vz vw weq vz
      wal wi vw wal vz vx weq vz vz vw weq vz vw weq vz wal wi vz vx weq vw vz
      vz vw weq vz vw weq vz wal wi vz wal vw wal vz vw weq vz wex vz vw weq vz
      wal wi vw wal vz vx weq vz vw weq vz vw weq vz wal wi vz wal vz vw weq vz
      wex vz vw weq vz wal wi vw vz vw weq vz vw weq vz wal vz vz vw weq vz
      nfa1-o 19.23 albii vz vw weq vz wex vz vw weq vz wal wi vw wal vz vw weq
      vz wal vw wal vz vx weq vz vw weq vz wex vz vw weq vz wal wi vz vw weq vz
      wal vw vz vw weq vz wex vz vw weq vz wex vz vw weq vz wal wi vz vw weq vz
      wal wi vz vw a9ev vz vw weq vz wex vz vw weq vz wal pm2.27 ax-mp alimi vz
      vw weq vz vx weq vz vw vz vw weq vw wal vz vx weq vz vz vw weq vz vx weq
      vw vx vw vx vz equequ2 spv sps-o a7s syl sylbi a7s a5i-o 3syl $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Version of ~ dveel2 using ~ ax-16 instead of ~ ax-17 .  (Contributed by
       NM, 10-May-2008.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    dveel2ALT $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      vz vw wel vz vy wel vx vy vw vz vw vx ax17el vz vy vw ax17el vw vy vz
      elequ2 dvelimh $.
  $}

  ${
    ax11f.1 $e |- ( ph -> A. x ph ) $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  We can start with any formula ` ph ` in which ` x ` is
       not free.  (Contributed by NM, 21-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11f $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      vx vy weq vx wal wn vx vy weq wph vx vy weq wph wi vx wal wi wph vx vy
      weq wph wi vx ax11f.1 wph vx vy weq ax-1 alrimih a1ii $.
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for equality predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11eq $p |- ( -. A. x x = y ->
               ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) ) $=
      vx vz weq vx wal vx vw weq vx wal vx vy weq vx wal wn vx vy weq vz vw weq
      vx vy weq vz vw weq wi vx wal wi wi wi vx vz weq vx wal vx vw weq vx wal
      wa vx vz weq vx vw weq wa vx wal vx vy weq vx wal wn vx vy weq vz vw weq
      vx vy weq vz vw weq wi vx wal wi wi wi vx vz weq vx vw weq vx 19.26 vx vz
      weq vx vw weq wa vx wal vx vy weq vx wal wn vx vy weq vz vw weq vx vy weq
      vz vw weq wi vx wal wi vx vz weq vx vw weq wa vx wal vx vy weq vx wal wn
      vx vy weq wa wa vx vx weq vx vy weq vx vx weq wi vx wal wi vz vw weq vx
      vy weq vz vw weq wi vx wal wi vx vy weq vx vx weq wi vx wal vx vx weq vx
      vy weq vx vx weq wi vx vx vx weq vx vy weq vx equid a1i ax-gen a1i vx vz
      weq vx vw weq wa vx wal vx vx weq vx vy weq vx vx weq wi vx wal wi vz vw
      weq vx vy weq vz vw weq wi vx wal wi wb vx vy weq vx wal wn vx vy weq wa
      vx vz weq vx vw weq wa vx wal vx vx weq vz vw weq vx vy weq vx vx weq wi
      vx wal vx vy weq vz vw weq wi vx wal vx vz weq vx vw weq wa vx vx weq vz
      vw weq wb vx vx vz weq vx vx weq vz vx weq vx vw weq vz vw weq vx vz vx
      equequ1 vx vw vz equequ2 sylan9bb sps-o vx vz weq vx vw weq wa vx wal vx
      vy weq vx vx weq wi vx vy weq vz vw weq wi vx vx vz weq vx vw weq wa vx
      nfa1-o vx vz weq vx vw weq wa vx wal vx vx weq vz vw weq vx vy weq vx vz
      weq vx vw weq wa vx vx weq vz vw weq wb vx vx vz weq vx vx weq vz vx weq
      vx vw weq vz vw weq vx vz vx equequ1 vx vw vz equequ2 sylan9bb sps-o
      imbi2d albid imbi12d adantr mpbii exp32 sylbir vx vz weq vx wal vx vw weq
      vx wal wn wa vx vy weq vx wal wn vx vy weq vz vw weq vx vy weq vz vw weq
      wi vx wal wi vx vz weq vx wal vx vw weq vx wal wn wa vx vy weq vx wal wn
      vx vy weq wa wa vx vw weq vx vy weq vx vw weq wi vx wal wi vz vw weq vx
      vy weq vz vw weq wi vx wal wi vx vw weq vx wal wn vx vy weq vx wal wn vx
      vy weq wa vx vw weq vx vy weq vx vw weq wi vx wal wi vx vz weq vx wal vx
      vw weq vx wal wn vx vy weq vx wal wn vx vy weq wa wa vx vw weq vy vw weq
      vx vy weq vx vw weq wi vx wal vx vy weq vx vw weq vy vw weq wb vx vw weq
      vx wal wn vx vy weq vx wal wn vx vy vw equequ1 ad2antll vx vw weq vx wal
      wn vx vy weq vx wal wn vx vy weq wa wa vy vw weq vy vw weq vx wal vx vy
      weq vx vw weq wi vx wal vx vw weq vx wal wn vx vy weq vx wal wn vy vw weq
      vy vw weq vx wal wi vx vy weq vx vy weq vx wal wn vx vw weq vx wal wn vy
      vw weq vy vw weq vx wal wi vy vw vx ax12o impcom adantrr vy vw weq vx vy
      weq vx vw weq wi vx vy vw vx equtrr alimi syl6 sylbid adantll vx vz weq
      vx wal vx vw weq vx vy weq vx vw weq wi vx wal wi vz vw weq vx vy weq vz
      vw weq wi vx wal wi wb vx vw weq vx wal wn vx vy weq vx wal wn vx vy weq
      wa vx vz weq vx wal vx vw weq vz vw weq vx vy weq vx vw weq wi vx wal vx
      vy weq vz vw weq wi vx wal vx vz weq vx vw weq vz vw weq wb vx vx vz vw
      equequ1 sps-o vx vy weq vx vw weq wi vx vy weq vz vw weq wi vx vz vx vx
      vz weq vx wal vx vw weq vz vw weq vx vy weq vx vz weq vx vw weq vz vw weq
      wb vx vx vz vw equequ1 sps-o imbi2d dral2-o imbi12d ad2antrr mpbid exp32
      vx vz weq vx wal wn vx vw weq vx wal wa vx vy weq vx wal wn vx vy weq vz
      vw weq vx vy weq vz vw weq wi vx wal wi vx vz weq vx wal wn vx vw weq vx
      wal wa vx vy weq vx wal wn vx vy weq wa wa vz vx weq vx vy weq vz vx weq
      wi vx wal wi vz vw weq vx vy weq vz vw weq wi vx wal wi vx vz weq vx wal
      wn vx vy weq vx wal wn vx vy weq wa vz vx weq vx vy weq vz vx weq wi vx
      wal wi vx vw weq vx wal vx vz weq vx wal wn vx vy weq vx wal wn vx vy weq
      wa wa vz vx weq vz vy weq vx vy weq vz vx weq wi vx wal vx vy weq vz vx
      weq vz vy weq wb vx vz weq vx wal wn vx vy weq vx wal wn vx vy vz equequ2
      ad2antll vx vz weq vx wal wn vx vy weq vx wal wn vx vy weq wa wa vz vy
      weq vz vy weq vx wal vx vy weq vz vx weq wi vx wal vx vz weq vx wal wn vx
      vy weq vx wal wn vz vy weq vz vy weq vx wal wi vx vy weq vx vz weq vx wal
      wn vx vy weq vx wal wn vz vy weq vz vy weq vx wal wi vz vy vx ax12o imp
      adantrr vz vy weq vx vy weq vz vx weq wi vx vx vy weq vz vx weq vz vy weq
      vx vy vz equequ2 biimprcd alimi syl6 sylbid adantlr vx vw weq vx wal vz
      vx weq vx vy weq vz vx weq wi vx wal wi vz vw weq vx vy weq vz vw weq wi
      vx wal wi wb vx vz weq vx wal wn vx vy weq vx wal wn vx vy weq wa vx vw
      weq vx wal vz vx weq vz vw weq vx vy weq vz vx weq wi vx wal vx vy weq vz
      vw weq wi vx wal vx vw weq vz vx weq vz vw weq wb vx vx vw vz equequ2
      sps-o vx vy weq vz vx weq wi vx vy weq vz vw weq wi vx vw vx vx vw weq vx
      wal vz vx weq vz vw weq vx vy weq vx vw weq vz vx weq vz vw weq wb vx vx
      vw vz equequ2 sps-o imbi2d dral2-o imbi12d ad2antlr mpbid exp32 vx vz weq
      vx wal wn vx vw weq vx wal wn wa vx vy weq vz vw weq vx vy weq vz vw weq
      wi vx wal wi wi vx vy weq vx wal wn vx vz weq vx wal wn vx vw weq vx wal
      wn wa vz vw weq vx vy weq vz vw weq wi vx wal wi vx vy weq vx vz weq vx
      wal wn vx vw weq vx wal wn wa vu vw weq vu wex vz vw weq vx vy weq vz vw
      weq wi vx wal wi vu vw a9ev vx vz weq vx wal wn vx vw weq vx wal wn wa vu
      vw weq vz vw weq vx vy weq vz vw weq wi vx wal wi vu vx vz weq vx wal wn
      vx vw weq vx wal wn wa vv vz weq vv wex vu vw weq vz vw weq vx vy weq vz
      vw weq wi vx wal wi wi vv vz a9ev vx vz weq vx wal wn vx vw weq vx wal wn
      wa vv vz weq vu vw weq vz vw weq vx vy weq vz vw weq wi vx wal wi wi vv
      vx vz weq vx wal wn vx vw weq vx wal wn wa vv vz weq vu vw weq vz vw weq
      vx vy weq vz vw weq wi vx wal wi vx vz weq vx wal wn vx vw weq vx wal wn
      wa vv vz weq vu vw weq wa wa vv vu weq vx vy weq vv vu weq wi vx wal wi
      vz vw weq vx vy weq vz vw weq wi vx wal wi vv vu weq vx vy weq vv vu weq
      wi vx vv vu weq vx vy weq ax-1 alrimiv vx vz weq vx wal wn vx vw weq vx
      wal wn wa vv vz weq vu vw weq wa wa vv vu weq vz vw weq vx vy weq vv vu
      weq wi vx wal vx vy weq vz vw weq wi vx wal vv vz weq vu vw weq wa vv vu
      weq vz vw weq wb vx vz weq vx wal wn vx vw weq vx wal wn wa vv vz weq vv
      vu weq vz vu weq vu vw weq vz vw weq vv vz vu equequ1 vu vw vz equequ2
      sylan9bb adantl vx vz weq vx wal wn vx vw weq vx wal wn wa vv vz weq vu
      vw weq wa wa vv vz weq vu vw weq wa vx wal vx vy weq vv vu weq wi vx wal
      vx vy weq vz vw weq wi vx wal wb vx vz weq vx wal wn vx vw weq vx wal wn
      wa vv vz weq vu vw weq wa wa vv vz weq vx wal vu vw weq vx wal wa vv vz
      weq vu vw weq wa vx wal vx vz weq vx wal wn vx vw weq vx wal wn wa vv vz
      weq vu vw weq wa vv vz weq vx wal vu vw weq vx wal wa vx vz weq vx wal wn
      vv vz weq vv vz weq vx wal vx vw weq vx wal wn vu vw weq vu vw weq vx wal
      vx vz vv dveeq2-o vx vw vu dveeq2-o im2anan9 imp vv vz weq vu vw weq vx
      19.26 sylibr vv vz weq vu vw weq wa vx wal vx vy weq vv vu weq wi vx vy
      weq vz vw weq wi vx vv vz weq vu vw weq wa vx nfa1-o vv vz weq vu vw weq
      wa vx wal vv vu weq vz vw weq vx vy weq vv vz weq vu vw weq wa vv vu weq
      vz vw weq wb vx vv vz weq vv vu weq vz vu weq vu vw weq vz vw weq vv vz
      vu equequ1 vu vw vz equequ2 sylan9bb sps-o imbi2d albid syl imbi12d mpbii
      exp32 exlimdv mpi exlimdv mpi a1d a1d 4cases $.
  $}

  ${
    $d x u v $.  $d y u v $.  $d z u v $.  $d w u v $.
    $( Basis step for constructing a substitution instance of ~ ax-11o without
       using ~ ax-11o .  Atomic formula for membership predicate.  (Contributed
       by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11el $p |- ( -. A. x x = y ->
               ( x = y -> ( z e. w -> A. x ( x = y -> z e. w ) ) ) ) $=
      vx vz weq vx wal vx vw weq vx wal vx vy weq vx wal wn vx vy weq vz vw wel
      vx vy weq vz vw wel wi vx wal wi wi wi vx vz weq vx wal vx vw weq vx wal
      wa vx vz weq vx vw weq wa vx wal vx vy weq vx wal wn vx vy weq vz vw wel
      vx vy weq vz vw wel wi vx wal wi wi wi vx vz weq vx vw weq vx 19.26 vx vz
      weq vx vw weq wa vx wal vx vy weq vx wal wn vx vy weq vz vw wel vx vy weq
      vz vw wel wi vx wal wi vx vz weq vx vw weq wa vx wal vx vy weq vx wal wn
      vx vy weq wa wa vx vx wel vx vy weq vx vx wel wi vx wal wi vz vw wel vx
      vy weq vz vw wel wi vx wal wi vx vy weq vx wal wn vx vy weq wa vx vx wel
      vx vy weq vx vx wel wi vx wal wi vx vz weq vx vw weq wa vx wal vx vy weq
      vx wal wn vx vy weq wa vx vx wel vy vy wel vx vy weq vx vx wel wi vx wal
      vx vy weq vx vx wel vy vy wel wb vx vy weq vx wal wn vx vy weq vx vx wel
      vy vx wel vy vy wel vx vy vx elequ1 vx vy vy elequ2 bitrd adantl vx vy
      weq vx wal wn vy vy wel vx vy weq vx vx wel wi vx wal wi vx vy weq vx vy
      weq vx wal wn vy vy wel vy vy wel vx wal vx vy weq vx vx wel wi vx wal vv
      vv wel vy vy wel vx vy vv vv vv wel vx ax-17 vy vy wel vv ax-17 vv vy weq
      vv vv wel vy vv wel vy vy wel vv vy vv elequ1 vv vy vy elequ2 bitrd
      dvelimf-o vy vy wel vx vy weq vx vx wel wi vx vx vy weq vx vx wel vy vy
      wel vx vy weq vx vx wel vy vx wel vy vy wel vx vy vx elequ1 vx vy vy
      elequ2 bitrd biimprcd alimi syl6 adantr sylbid adantl vx vz weq vx vw weq
      wa vx wal vx vx wel vx vy weq vx vx wel wi vx wal wi vz vw wel vx vy weq
      vz vw wel wi vx wal wi wb vx vy weq vx wal wn vx vy weq wa vx vz weq vx
      vw weq wa vx wal vx vx wel vz vw wel vx vy weq vx vx wel wi vx wal vx vy
      weq vz vw wel wi vx wal vx vz weq vx vw weq wa vx vx wel vz vw wel wb vx
      vx vz weq vx vx wel vz vx wel vx vw weq vz vw wel vx vz vx elequ1 vx vw
      vz elequ2 sylan9bb sps-o vx vz weq vx vw weq wa vx wal vx vy weq vx vx
      wel wi vx vy weq vz vw wel wi vx vx vz weq vx vw weq wa vx nfa1-o vx vz
      weq vx vw weq wa vx wal vx vx wel vz vw wel vx vy weq vx vz weq vx vw weq
      wa vx vx wel vz vw wel wb vx vx vz weq vx vx wel vz vx wel vx vw weq vz
      vw wel vx vz vx elequ1 vx vw vz elequ2 sylan9bb sps-o imbi2d albid
      imbi12d adantr mpbid exp32 sylbir vx vz weq vx wal vx vw weq vx wal wn wa
      vx vy weq vx wal wn vx vy weq vz vw wel vx vy weq vz vw wel wi vx wal wi
      vx vz weq vx wal vx vw weq vx wal wn wa vx vy weq vx wal wn vx vy weq wa
      wa vx vw wel vx vy weq vx vw wel wi vx wal wi vz vw wel vx vy weq vz vw
      wel wi vx wal wi vx vw weq vx wal wn vx vy weq vx wal wn vx vy weq wa vx
      vw wel vx vy weq vx vw wel wi vx wal wi vx vz weq vx wal vx vw weq vx wal
      wn vx vy weq vx wal wn vx vy weq wa wa vx vw wel vy vw wel vx vy weq vx
      vw wel wi vx wal vx vy weq vx vw wel vy vw wel wb vx vw weq vx wal wn vx
      vy weq vx wal wn vx vy vw elequ1 ad2antll vx vw weq vx wal wn vx vy weq
      vx wal wn vx vy weq wa wa vy vw wel vy vw wel vx wal vx vy weq vx vw wel
      wi vx wal vx vw weq vx wal wn vx vy weq vx wal wn vy vw wel vy vw wel vx
      wal wi vx vy weq vx vy weq vx wal wn vx vw weq vx wal wn vy vw wel vy vw
      wel vx wal wi vy vw vx ax-15 impcom adantrr vy vw wel vx vy weq vx vw wel
      wi vx vx vy weq vx vw wel vy vw wel vx vy vw elequ1 biimprcd alimi syl6
      sylbid adantll vx vz weq vx wal vx vw wel vx vy weq vx vw wel wi vx wal
      wi vz vw wel vx vy weq vz vw wel wi vx wal wi wb vx vw weq vx wal wn vx
      vy weq vx wal wn vx vy weq wa vx vz weq vx wal vx vw wel vz vw wel vx vy
      weq vx vw wel wi vx wal vx vy weq vz vw wel wi vx wal vx vz weq vx vw wel
      vz vw wel wb vx vx vz vw elequ1 sps-o vx vy weq vx vw wel wi vx vy weq vz
      vw wel wi vx vz vx vx vz weq vx wal vx vw wel vz vw wel vx vy weq vx vz
      weq vx vw wel vz vw wel wb vx vx vz vw elequ1 sps-o imbi2d dral2-o
      imbi12d ad2antrr mpbid exp32 vx vz weq vx wal wn vx vw weq vx wal wa vx
      vy weq vx wal wn vx vy weq vz vw wel vx vy weq vz vw wel wi vx wal wi vx
      vz weq vx wal wn vx vw weq vx wal wa vx vy weq vx wal wn vx vy weq wa wa
      vz vx wel vx vy weq vz vx wel wi vx wal wi vz vw wel vx vy weq vz vw wel
      wi vx wal wi vx vz weq vx wal wn vx vy weq vx wal wn vx vy weq wa vz vx
      wel vx vy weq vz vx wel wi vx wal wi vx vw weq vx wal vx vz weq vx wal wn
      vx vy weq vx wal wn vx vy weq wa wa vz vx wel vz vy wel vx vy weq vz vx
      wel wi vx wal vx vy weq vz vx wel vz vy wel wb vx vz weq vx wal wn vx vy
      weq vx wal wn vx vy vz elequ2 ad2antll vx vz weq vx wal wn vx vy weq vx
      wal wn vx vy weq wa wa vz vy wel vz vy wel vx wal vx vy weq vz vx wel wi
      vx wal vx vz weq vx wal wn vx vy weq vx wal wn vz vy wel vz vy wel vx wal
      wi vx vy weq vx vz weq vx wal wn vx vy weq vx wal wn vz vy wel vz vy wel
      vx wal wi vz vy vx ax-15 imp adantrr vz vy wel vx vy weq vz vx wel wi vx
      vx vy weq vz vx wel vz vy wel vx vy vz elequ2 biimprcd alimi syl6 sylbid
      adantlr vx vw weq vx wal vz vx wel vx vy weq vz vx wel wi vx wal wi vz vw
      wel vx vy weq vz vw wel wi vx wal wi wb vx vz weq vx wal wn vx vy weq vx
      wal wn vx vy weq wa vx vw weq vx wal vz vx wel vz vw wel vx vy weq vz vx
      wel wi vx wal vx vy weq vz vw wel wi vx wal vx vw weq vz vx wel vz vw wel
      wb vx vx vw vz elequ2 sps-o vx vy weq vz vx wel wi vx vy weq vz vw wel wi
      vx vw vx vx vw weq vx wal vz vx wel vz vw wel vx vy weq vx vw weq vz vx
      wel vz vw wel wb vx vx vw vz elequ2 sps-o imbi2d dral2-o imbi12d ad2antlr
      mpbid exp32 vx vz weq vx wal wn vx vw weq vx wal wn wa vx vy weq vz vw
      wel vx vy weq vz vw wel wi vx wal wi wi vx vy weq vx wal wn vx vz weq vx
      wal wn vx vw weq vx wal wn wa vz vw wel vx vy weq vz vw wel wi vx wal wi
      vx vy weq vx vz weq vx wal wn vx vw weq vx wal wn wa vu vw weq vu wex vz
      vw wel vx vy weq vz vw wel wi vx wal wi vu vw a9ev vx vz weq vx wal wn vx
      vw weq vx wal wn wa vu vw weq vz vw wel vx vy weq vz vw wel wi vx wal wi
      vu vx vz weq vx wal wn vx vw weq vx wal wn wa vv vz weq vv wex vu vw weq
      vz vw wel vx vy weq vz vw wel wi vx wal wi wi vv vz a9ev vx vz weq vx wal
      wn vx vw weq vx wal wn wa vv vz weq vu vw weq vz vw wel vx vy weq vz vw
      wel wi vx wal wi wi vv vx vz weq vx wal wn vx vw weq vx wal wn wa vv vz
      weq vu vw weq vz vw wel vx vy weq vz vw wel wi vx wal wi vx vz weq vx wal
      wn vx vw weq vx wal wn wa vv vz weq vu vw weq wa wa vv vu wel vx vy weq
      vv vu wel wi vx wal wi vz vw wel vx vy weq vz vw wel wi vx wal wi vv vu
      wel vx vy weq vv vu wel wi vx vv vu wel vx vy weq ax-1 alrimiv vx vz weq
      vx wal wn vx vw weq vx wal wn wa vv vz weq vu vw weq wa wa vv vu wel vz
      vw wel vx vy weq vv vu wel wi vx wal vx vy weq vz vw wel wi vx wal vv vz
      weq vu vw weq wa vv vu wel vz vw wel wb vx vz weq vx wal wn vx vw weq vx
      wal wn wa vv vz weq vv vu wel vz vu wel vu vw weq vz vw wel vv vz vu
      elequ1 vu vw vz elequ2 sylan9bb adantl vx vz weq vx wal wn vx vw weq vx
      wal wn wa vv vz weq vu vw weq wa wa vv vz weq vu vw weq wa vx wal vx vy
      weq vv vu wel wi vx wal vx vy weq vz vw wel wi vx wal wb vx vz weq vx wal
      wn vx vw weq vx wal wn wa vv vz weq vu vw weq wa wa vv vz weq vx wal vu
      vw weq vx wal wa vv vz weq vu vw weq wa vx wal vx vz weq vx wal wn vx vw
      weq vx wal wn wa vv vz weq vu vw weq wa vv vz weq vx wal vu vw weq vx wal
      wa vx vz weq vx wal wn vv vz weq vv vz weq vx wal vx vw weq vx wal wn vu
      vw weq vu vw weq vx wal vx vz vv dveeq2-o vx vw vu dveeq2-o im2anan9 imp
      vv vz weq vu vw weq vx 19.26 sylibr vv vz weq vu vw weq wa vx wal vx vy
      weq vv vu wel wi vx vy weq vz vw wel wi vx vv vz weq vu vw weq wa vx
      nfa1-o vv vz weq vu vw weq wa vx wal vv vu wel vz vw wel vx vy weq vv vz
      weq vu vw weq wa vv vu wel vz vw wel wb vx vv vz weq vv vu wel vz vu wel
      vu vw weq vz vw wel vv vz vu elequ1 vu vw vz elequ2 sylan9bb sps-o imbi2d
      albid syl imbi12d mpbii exp32 exlimdv mpi exlimdv mpi a1d a1d 4cases $.
  $}

  ${
    ax11indn.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Negation case.  (Contributed by NM,
       21-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11indn $p |- ( -. A. x x = y ->
               ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) ) $=
      vx vy weq vx wal wn vx vy weq wph wn vx vy weq wph wn wi vx wal vx vy weq
      wph wn wa vx vy weq wph wn wa vx wex vx vy weq vx wal wn vx vy weq wph wn
      wi vx wal vx vy weq wph wn wa vx 19.8a vx vy weq wph wn wa vx wex vx vy
      weq wph wi vx wal wn vx vy weq vx wal wn vx vy weq wph wn wi vx wal vx vy
      weq wph vx exanali vx vy weq vx wal wn vx vy weq wph wi vx wal wn vx vy
      weq wph wn wi vx vx vy weq vx hbn1 vx vy weq wph wi vx hbn1 vx vy weq vx
      wal wn vx vy weq vx vy weq wph wi vx wal wn wph wn vx vy weq vx wal wn vx
      vy weq wph vx vy weq wph wi vx wal wi vx vy weq wph wi vx wal wn wph wn
      wi ax11indn.1 wph vx vy weq wph wi vx wal con3 syl6 com23 alrimdh syl5bi
      syl5 exp3a $.

    ${
      ax11indi.2 $e |- ( -. A. x x = y ->
                 ( x = y -> ( ps -> A. x ( x = y -> ps ) ) ) ) $.
      $( Induction step for constructing a substitution instance of ~ ax-11o
         without using ~ ax-11o .  Implication case.  (Contributed by NM,
         21-Jan-2007.)  (Proof modification is discouraged.)
         (New usage is discouraged.) $)
      ax11indi $p |- ( -. A. x x = y ->
           ( x = y -> ( ( ph -> ps ) -> A. x ( x = y -> ( ph -> ps ) ) ) ) ) $=
        vx vy weq vx wal wn vx vy weq wph wps wi vx vy weq wph wps wi wi vx wal
        wi vx vy weq vx wal wn vx vy weq wa wph wps vx vy weq wph wps wi wi vx
        wal vx vy weq vx wal wn vx vy weq wa wph wn vx vy weq wph wn wi vx wal
        vx vy weq wph wps wi wi vx wal vx vy weq vx wal wn vx vy weq wph wn vx
        vy weq wph wn wi vx wal wi wph vx vy ax11indn.1 ax11indn imp vx vy weq
        wph wn wi vx vy weq wph wps wi wi vx wph wn wph wps wi vx vy weq wph
        wps pm2.21 imim2i alimi syl6 vx vy weq vx wal wn vx vy weq wa wps vx vy
        weq wps wi vx wal vx vy weq wph wps wi wi vx wal vx vy weq vx wal wn vx
        vy weq wps vx vy weq wps wi vx wal wi ax11indi.2 imp vx vy weq wps wi
        vx vy weq wph wps wi wi vx wps wph wps wi vx vy weq wps wph ax-1 imim2i
        alimi syl6 jad ex $.
    $}
  $}

  ${
    ax11indalem.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( Lemma for ~ ax11inda2 and ~ ax11inda .  (Contributed by NM,
       24-Jan-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11indalem $p |- ( -. A. y y = z -> ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) ) $=
      vx vz weq vx wal vy vz weq vy wal wn vx vy weq vx wal wn vx vy weq wph vz
      wal vx vy weq wph vz wal wi vx wal wi wi wi vx vz weq vx wal vx vy weq vx
      wal wn vx vy weq wph vz wal vx vy weq wph vz wal wi vx wal wi wi wi vy vz
      weq vy wal wn vx vz weq vx wal vx vy weq wph vz wal vx vy weq wph vz wal
      wi vx wal wi wi vx vy weq vx wal wn vx vz weq vx wal wph vz wal vx vy weq
      wph vz wal wi vx wal wi vx vy weq wph vz wal vx vy weq wph vz wal wi vx
      wal wi vz vx vz vx weq vz wal wph vx wal vx vy weq wph vx wal wi vx wal
      wph vz wal vx vy weq wph vz wal wi vx wal wph vx wal vx vy weq wph vx wal
      wi vx wal wi vz vx weq vz wal wph vx vy weq wph vx wal wi vx wph vx wal
      vx vy weq ax-1 a5i-o a1i wph wph vz vx vz vx weq vz wal wph biidd dral1-o
      vx vy weq wph vz wal wi vx vy weq wph vx wal wi vz vx vx vz vx weq vz wal
      wph vz wal wph vx wal vx vy weq wph wph vz vx vz vx weq vz wal wph biidd
      dral1-o imbi2d dral2-o 3imtr4d aecoms-o a1d a1d adantr vx vz weq vx wal
      wn vy vz weq vy wal wn wa vx vy weq vx wal wn vx vy weq wph vz wal vx vy
      weq wph vz wal wi vx wal wi vx vz weq vx wal wn vy vz weq vy wal wn wa vx
      vy weq vx wal wn wa vx vy weq wa wph vz wal vx vy weq wph wi vx wal vz
      wal vx vy weq wph vz wal wi vx wal vx vz weq vx wal wn vy vz weq vy wal
      wn wa vx vy weq vx wal wn wa vx vy weq wa vx vy weq vx wal wn vx vy weq
      vz wal wph vz wal vx vy weq wph wi vx wal vz wal wi vx vz weq vx wal wn
      vy vz weq vy wal wn wa vx vy weq vx wal wn vx vy weq simplr vx vz weq vx
      wal wn vy vz weq vy wal wn wa vx vy weq vx vy weq vz wal vx vy weq vx wal
      wn vx vz weq vx wal wn vy vz weq vy wal wn wa vx vy weq vx vy weq vz wal
      vx vz weq vx wal wn vz vx weq vz wal wn vz vy weq vz wal wn vx vy weq vx
      vy weq vz wal wi vy vz weq vy wal wn vz vx weq vz wal vx vz weq vx wal vz
      vx aecom-o con3i vz vy weq vz wal vy vz weq vy wal vz vy aecom-o con3i vz
      vx weq vz wal wn vz vy weq vz wal wn vx vy weq vx vy weq vz wal wi vx vy
      vz ax12o imp syl2an imp adantlr vx vy weq vx wal wn vx vy weq vz wal wa
      wph vx vy weq wph wi vx wal vz vx vy weq vx wal wn vx vy weq vz wal vz vx
      vy vz hbnae-o vx vy weq vz hba1-o hban vx vy weq vz wal vx vy weq vx wal
      wn vx vy weq wph vx vy weq wph wi vx wal wi vx vy weq vz ax-4 vx vy weq
      vx wal wn vx vy weq wph vx vy weq wph wi vx wal wi ax11indalem.1 imp
      sylan2 alimdh syl2anc vx vz weq vx wal wn vy vz weq vy wal wn wa vx vy
      weq wph wi vx wal vz wal vx vy weq wph vz wal wi vx wal wi vx vy weq vx
      wal wn vx vy weq vx vy weq wph wi vx wal vz wal vx vy weq wph wi vz wal
      vx wal vx vz weq vx wal wn vy vz weq vy wal wn wa vx vy weq wph vz wal wi
      vx wal vx vy weq wph wi vz vx ax-7 vx vz weq vx wal wn vy vz weq vy wal
      wn wa vx vy weq wph wi vz wal vx vy weq wph vz wal wi vx vx vz weq vx wal
      wn vy vz weq vy wal wn vx vx vz vx hbnae-o vy vz vx hbnae-o hban vx vz
      weq vx wal wn vy vz weq vy wal wn wa vx vy weq vz wnf vx vy weq wph wi vz
      wal vx vy weq wph vz wal wi wb vx vz weq vx wal wn vy vz weq vy wal wn wa
      vx vy weq vz vx vz weq vx wal wn vy vz weq vy wal wn vz vx vz vz hbnae-o
      vy vz vz hbnae-o hban vx vz weq vx wal wn vz vx weq vz wal wn vz vy weq
      vz wal wn vx vy weq vx vy weq vz wal wi vy vz weq vy wal wn vz vx weq vz
      wal vx vz weq vx wal vz vx aecom-o con3i vz vy weq vz wal vy vz weq vy
      wal vz vy aecom-o con3i vz vx weq vz wal wn vz vy weq vz wal wn vx vy weq
      vx vy weq vz wal wi vx vy vz ax12o imp syl2an nfdh vx vy weq wph vz
      19.21t syl albidh syl5ib ad2antrr syld exp31 pm2.61ian $.
  $}

  ${
    $d z y $.
    ax11inda2.1 $e |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $.
    $( A proof of ~ ax11inda2 that is slightly more direct.  (Contributed by
       NM, 4-May-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11inda2ALT $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      vx vz weq vx wal vx vy weq vx wal wn vx vy weq wph vz wal vx vy weq wph
      vz wal wi vx wal wi wi wi vx vz weq vx wal vx vy weq wph vz wal vx vy weq
      wph vz wal wi vx wal wi wi vx vy weq vx wal wn vx vz weq vx wal wph vz
      wal vx vy weq wph vz wal wi vx wal wi vx vy weq wph vz wal vx vy weq wph
      vz wal wi vx wal wi vz vx vz vx weq vz wal wph vx wal vx vy weq wph vx
      wal wi vx wal wph vz wal vx vy weq wph vz wal wi vx wal wph vx wal vx vy
      weq wph vx wal wi vx wal wi vz vx weq vz wal wph vx vy weq wph vx wal wi
      vx wph vx wal vx vy weq ax-1 a5i-o a1i wph wph vz vx vz vx weq vz wal wph
      biidd dral1-o vx vy weq wph vz wal wi vx vy weq wph vx wal wi vz vx vx vz
      vx weq vz wal wph vz wal wph vx wal vx vy weq wph wph vz vx vz vx weq vz
      wal wph biidd dral1-o imbi2d dral2-o 3imtr4d aecoms-o a1d a1d vx vz weq
      vx wal wn vx vy weq vx wal wn vx vy weq wph vz wal vx vy weq wph vz wal
      wi vx wal wi vx vz weq vx wal wn vx vy weq vx wal wn wa vx vy weq wa wph
      vz wal vx vy weq wph wi vx wal vz wal vx vy weq wph vz wal wi vx wal vx
      vz weq vx wal wn vx vy weq vx wal wn wa vx vy weq wa vx vy weq vx wal wn
      vx vy weq vz wal wph vz wal vx vy weq wph wi vx wal vz wal wi vx vz weq
      vx wal wn vx vy weq vx wal wn vx vy weq simplr vx vz weq vx wal wn vx vy
      weq vx vy weq vz wal vx vy weq vx wal wn vx vz weq vx wal wn vx vy weq vx
      vy weq vz wal vx vy weq vx vy weq vz wal wi vz vx vz vx vy dveeq1-o
      naecoms-o imp adantlr vx vy weq vx wal wn vx vy weq vz wal wa wph vx vy
      weq wph wi vx wal vz vx vy weq vx wal wn vx vy weq vz wal vz vx vy vz
      hbnae-o vx vy weq vz hba1-o hban vx vy weq vz wal vx vy weq vx wal wn vx
      vy weq wph vx vy weq wph wi vx wal wi vx vy weq vz ax-4 vx vy weq vx wal
      wn vx vy weq wph vx vy weq wph wi vx wal wi ax11inda2.1 imp sylan2 alimdh
      syl2anc vx vz weq vx wal wn vx vy weq wph wi vx wal vz wal vx vy weq wph
      vz wal wi vx wal wi vx vy weq vx wal wn vx vy weq vx vy weq wph wi vx wal
      vz wal vx vy weq wph wi vz wal vx wal vx vz weq vx wal wn vx vy weq wph
      vz wal wi vx wal vx vy weq wph wi vz vx ax-7 vx vz weq vx wal wn vx vy
      weq wph wi vz wal vx vy weq wph vz wal wi vx vx vz vx hbnae-o vx vz weq
      vx wal wn vx vy weq vz wnf vx vy weq wph wi vz wal vx vy weq wph vz wal
      wi wb vx vz weq vx wal wn vx vy weq vz vx vz vz hbnae-o vx vy weq vx vy
      weq vz wal wi vz vx vz vx vy dveeq1-o naecoms-o nfdh vx vy weq wph vz
      19.21t syl albidh syl5ib ad2antrr syld exp31 pm2.61i $.

    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  When ` z ` and ` y ` are
       distinct, this theorem avoids the dummy variables needed by the more
       general ~ ax11inda .  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11inda2 $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      vy vz weq vy wal vx vy weq vx wal wn vx vy weq wph vz wal vx vy weq wph
      vz wal wi vx wal wi wi wi vy vz weq vy wal vx vy weq wph vz wal vx vy weq
      wph vz wal wi vx wal wi wi vx vy weq vx wal wn vy vz weq vy wal wph vz
      wal vx vy weq wph vz wal wi vx wal wi vx vy weq wph vz wal vx vy weq wph
      vz wal wi vy vz weq vy wal vx vy weq wph vz wal wi vx wal wph vz wal vx
      vy weq ax-1 vx vy weq wph vz wal wi vy vz vx a16g-o syl5 a1d a1d wph vx
      vy vz ax11inda2.1 ax11indalem pm2.61i $.
  $}

  ${
    $d w ph $.  $d w x $.  $d w y $.  $d w z $.
    ax11inda.1 $e |- ( -. A. x x = w ->
               ( x = w -> ( ph -> A. x ( x = w -> ph ) ) ) ) $.
    $( Induction step for constructing a substitution instance of ~ ax-11o
       without using ~ ax-11o .  Quantification case.  (When ` z ` and ` y `
       are distinct, ~ ax11inda2 may be used instead to avoid the dummy
       variable ` w ` in the proof.)  (Contributed by NM, 24-Jan-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11inda $p |- ( -. A. x x = y ->
               ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) ) $=
      vx vy weq vx wal wn vx vy weq wph vz wal vx vy weq wph vz wal wi vx wal
      wi wi vx vy weq vx wal wn vw vy weq vw wex vx vy weq vx wal wn vx vy weq
      wph vz wal vx vy weq wph vz wal wi vx wal wi wi wi vw vy a9ev vx vy weq
      vx wal wn vw vy weq vx vy weq vx wal wn vx vy weq wph vz wal vx vy weq
      wph vz wal wi vx wal wi wi wi vw vx vy weq vx wal wn vw vy weq vx vy weq
      vx wal wn vx vy weq wph vz wal vx vy weq wph vz wal wi vx wal wi wi wi vx
      vy weq vx wal wn vw vy weq wa vx vw weq vx wal wn vx vw weq wph vz wal vx
      vw weq wph vz wal wi vx wal wi wi wi vx vy weq vx wal wn vx vy weq wph vz
      wal vx vy weq wph vz wal wi vx wal wi wi wi wph vx vw vz ax11inda.1
      ax11inda2 vx vy weq vx wal wn vw vy weq wa vx vw weq vx wal wn vx vy weq
      vx wal wn vx vw weq wph vz wal vx vw weq wph vz wal wi vx wal wi wi vx vy
      weq wph vz wal vx vy weq wph vz wal wi vx wal wi wi vx vy weq vx wal wn
      vw vy weq wa vw vy weq vx wal vx vw weq vx wal wn vx vy weq vx wal wn wb
      vx vy weq vx wal wn vw vy weq vw vy weq vx wal vx vy vw dveeq2-o imp vw
      vy weq vx wal vx vw weq vx wal vx vy weq vx wal vw vy weq vx wal vx vw
      weq vx vy weq vx vw vy weq vx hba1-o vw vy weq vx vw weq vx vy weq wb vx
      vw vy vx equequ2 sps-o albidh notbid syl vx vy weq vx wal wn vw vy weq wa
      vx vw weq vx vy weq wph vz wal vx vw weq wph vz wal wi vx wal wi wph vz
      wal vx vy weq wph vz wal wi vx wal wi vw vy weq vx vw weq vx vy weq wb vx
      vy weq vx wal wn vw vy vx equequ2 adantl vx vy weq vx wal wn vw vy weq wa
      vx vw weq wph vz wal wi vx wal vx vy weq wph vz wal wi vx wal wph vz wal
      vx vy weq vx wal wn vw vy weq wa vw vy weq vx wal vx vw weq wph vz wal wi
      vx wal vx vy weq wph vz wal wi vx wal wb vx vy weq vx wal wn vw vy weq vw
      vy weq vx wal vx vy vw dveeq2-o imp vw vy weq vx wal vx vw weq wph vz wal
      wi vx vy weq wph vz wal wi vx vw vy weq vx hba1-o vw vy weq vx wal vx vw
      weq vx vy weq wph vz wal vw vy weq vx vw weq vx vy weq wb vx vw vy vx
      equequ2 sps-o imbi1d albidh syl imbi2d imbi12d imbi12d mpbii ex exlimdv
      mpi pm2.43i $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2-o.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax-11o from ~ ax11v without using ~ ax-11o .  The
       hypothesis is even weaker than ~ ax11v , with ` z ` both distinct from
       ` x ` _and_ not occurring in ` ph ` .  Thus, the hypothesis provides an
       alternate axiom that can be used in place of ~ ax-11o .  (Contributed by
       NM, 2-Feb-2007.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    ax11v2-o $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      vx vy weq vx wal wn vz vy weq vz wex vx vy weq wph vx vy weq wph wi vx
      wal wi wi vz vy a9ev vx vy weq vx wal wn vz vy weq vx vy weq wph vx vy
      weq wph wi vx wal wi wi vz vx vy weq vx wal wn vz vy weq vx vy weq wph vx
      vy weq wph wi vx wal wi wi vx vy weq vx wal wn vz vy weq wa vx vz weq wph
      vx vz weq wph wi vx wal wi wi vx vy weq wph vx vy weq wph wi vx wal wi wi
      ax11v2-o.1 vx vy weq vx wal wn vz vy weq wa vx vz weq vx vy weq wph vx vz
      weq wph wi vx wal wi wph vx vy weq wph wi vx wal wi vz vy weq vx vz weq
      vx vy weq wb vx vy weq vx wal wn vz vy vx equequ2 adantl vx vy weq vx wal
      wn vz vy weq wa vx vz weq wph wi vx wal vx vy weq wph wi vx wal wph vx vy
      weq vx wal wn vz vy weq wa vz vy weq vx wal vx vz weq wph wi vx wal vx vy
      weq wph wi vx wal wb vx vy weq vx wal wn vz vy weq vz vy weq vx wal vx vy
      vz dveeq2-o imp vz vy weq vx wal vx vz weq wph wi vx vy weq wph wi vx vz
      vy weq vx nfa1-o vz vy weq vx vz weq wph wi vx vy weq wph wi wb vx vz vy
      weq vx vz weq vx vy weq wph vz vy vx equequ2 imbi1d sps-o albid syl
      imbi2d imbi12d mpbii ex exlimdv mpi $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2-o.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 , without using
       ~ ax-11 or ~ ax-11o .  The hypothesis is even weaker than ~ ax-11 , with
       ` z ` both distinct from ` x ` and not occurring in ` ph ` .  Thus, the
       hypothesis provides an alternate axiom that can be used in place of
       ~ ax-11 , if we also hvae ~ ax-10o which this proof uses .  As theorem
       ~ ax11 shows, the distinct variable conditions are optional.  An open
       problem is whether we can derive this with ~ ax-10 instead of
       ~ ax-10o .  (Contributed by NM, 2-Feb-2007.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax11a2-o $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      wph vx vy vz wph wph vz wal vx vz weq vx vz weq wph wi vx wal wph vz
      ax-17 ax11a2-o.1 syl5 ax11v2-o $.
  $}

  $( Show that ~ ax-10o can be derived from ~ ax-10 .  An open problem is
     whether this theorem can be derived from ~ ax-10 and the others when
     ~ ax-11 is replaced with ~ ax-11o .  See theorem ~ ax10from10o for the
     rederivation of ~ ax-10 from ~ ax10o .

     Normally, ~ ax10o should be used rather than ~ ax-10o or ~ ax10o-o ,
     except by theorems specifically studying the latter's properties.
     (Contributed by NM, 16-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax10o-o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    vx vy weq vx wal vy vx weq vy wal wph vx wal vy vx weq wph wi vy wal wph vy
    wal vx vy ax-10 vx vy weq wph vx wal vy vx weq wph wi vy wal wi vx wph vx
    wal vy vx weq wph wi vy wal wi vy vx wph vy vx ax11 equcoms sps-o vy vx weq
    vy vx weq wph wi wph vy vy vx weq wph pm2.27 al2imi sylsyld $.


