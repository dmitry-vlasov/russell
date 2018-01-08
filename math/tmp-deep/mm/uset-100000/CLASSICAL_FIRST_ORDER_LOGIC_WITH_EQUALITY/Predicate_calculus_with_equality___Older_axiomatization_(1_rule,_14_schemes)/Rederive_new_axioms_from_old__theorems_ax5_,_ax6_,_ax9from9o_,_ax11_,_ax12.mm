
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Older_axiomatization_(1_rule,_14_schemes)/Obsolete_schemes_ax-5o_ax-4_ax-6o_ax-9o_ax-10o_ax-10_ax-11o_ax-12o_ax-15_ax-16.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
  Rederive new axioms from old: theorems ax5 , ax6 , ax9from9o , ax11 , ax12

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  Theorems ~ ax11 and ~ ax12 require some intermediate theorems that are
  included in this section.

$)

  $( This theorem repeats ~ sp under the name ~ ax4 , so that the metamath
     program's "verify markup" command will check that it matches axiom scheme
     ~ ax-4 .  It is preferred that references to this theorem use the name
     ~ sp .  (Contributed by NM, 18-Aug-2017.)  (New usage is discouraged.)
     (Proof modification is discouraged.) $)
  ax4 $p |- ( A. x ph -> ph ) $=
    wph vx sp $.

  $( Rederivation of axiom ~ ax-5 from ~ ax-5o and other older axioms.  See
     ~ ax5o for the derivation of ~ ax-5o from ~ ax-5 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax5 $p |- ( A. x ( ph -> ps ) -> ( A. x ph -> A. x ps ) ) $=
    wph wps wi vx wal wph vx wal wps wi vx wal wph vx wal wps vx wal wi wph wps
    wi vx wal wph vx wal wps wi wi wph wps wi vx wal wph vx wal wps wi vx wal
    wi vx wph wps wi wph vx wal wps wi vx ax-5o wph vx wal wph wph wps wi vx
    wal wps wph vx ax-4 wph wps wi vx ax-4 syl5 mpg wph wps vx ax-5o syl $.

  $( Rederivation of axiom ~ ax-6 from ~ ax-6o and other older axioms.  See
     ~ ax6o for the derivation of ~ ax-6o from ~ ax-6 .  (Contributed by NM,
     23-May-2008.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax6 $p |- ( -. A. x ph -> A. x -. A. x ph ) $=
    wph vx wal vx wal wn vx wal wph vx wal wn vx wal wph vx wal wph vx wal vx
    wal wn vx wal wph vx wal wn wi wph vx wal vx wal wn vx wal wph vx wal wn vx
    wal wi vx wph vx wal vx wal wn wph vx wal wn vx ax-5o wph vx wal vx wal wn
    vx wal wph vx wal vx wal wph vx wal wph vx wal vx wal wn vx ax-4 wph vx wal
    wph vx wal wi wph vx wal wph vx wal vx wal wi vx wph wph vx wal vx ax-5o
    wph vx wal id mpg nsyl mpg wph vx wal vx ax-6o nsyl4 $.

  $( Rederivation of axiom ~ ax-9 from ~ ax-9o and other older axioms.  See
     ~ ax9o for the derivation of ~ ax-9o from ~ ax-9 .  Lemma L18 in [Megill]
     p. 446 (p. 14 of the preprint).  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is discouraged.)  (New usage is discouraged.) $)
  ax9from9o $p |- -. A. x -. x = y $=
    vx vy weq vx vy weq wn vx wal wn vx wal wi vx vy weq wn vx wal wn vx vx vy
    weq wn vx wal wn vx vy ax-9o vx vy weq wn vx wal wn vx wal vx vy weq vx vy
    weq wn vx ax-6o con4i mpg $.

  $( ` x ` is not free in ` A. x ph ` .  Example in Appendix in [Megill] p. 450
     (p. 19 of the preprint).  Also Lemma 22 of [Monk2] p. 114.  (Contributed
     by NM, 5-Aug-1993.)  (New usage is discouraged.) $)
  hba1-o $p |- ( A. x ph -> A. x A. x ph ) $=
    wph vx wal wph vx wal wn vx wal wn wph vx wal wn vx wal wn vx wal wph vx
    wal vx wal wph vx wal wn vx wal wph vx wal wph vx wal wn vx ax-4 con2i wph
    vx wal wn vx ax6 wph vx wal wn vx wal wn wph vx wal vx wph vx wal wph vx
    wal wn vx wal wph vx ax6 con1i alimi 3syl $.

  ${
    a5i-o.1 $e |- ( A. x ph -> ps ) $.
    $( Inference version of ~ ax-5o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    a5i-o $p |- ( A. x ph -> A. x ps ) $=
      wph vx wal wps vx wph vx hba1-o a5i-o.1 alrimih $.
  $}

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).  Version
     of ~ aecom using ~ ax-10o .  Unlike ~ ax10from10o , this version does not
     require ~ ax-17 .  (Contributed by NM, 5-Aug-1993.)
     (New usage is discouraged.) $)
  aecom-o $p |- ( A. x x = y -> A. y y = x ) $=
    vx vy weq vx wal vx vy weq vy wal vy vx weq vy wal vx vy weq vx wal vx vy
    weq vy wal vx vy weq vx vy ax-10o pm2.43i vx vy weq vy vx weq vy vx vy
    equcomi alimi syl $.

  ${
    alequcoms-o.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  Version of
       ~ aecoms using ax-10o .  (Contributed by NM, 5-Aug-1993.)
       (New usage is discouraged.) $)
    aecoms-o $p |- ( A. y y = x -> ph ) $=
      vy vx weq vy wal vx vy weq vx wal wph vy vx aecom-o alequcoms-o.1 syl $.
  $}

  $( All variables are effectively bound in an identical variable specifier.
     Version of ~ hbae using ~ ax-10o .  (Contributed by NM, 5-Aug-1993.)
     (Proof modification is disccouraged.)  (New usage is discouraged.) $)
  hbae-o $p |- ( A. x x = y -> A. z A. x x = y ) $=
    vx vy weq vx wal vx vy weq vz wal vx wal vx vy weq vx wal vz wal vx vy weq
    vx vy weq vz wal vx vz vx weq vz wal vz vy weq vz wal vx vy weq vx wal vx
    vy weq vz wal wi vx vy weq vx wal vx vy weq vz vx weq vz wal wn vz vy weq
    vz wal wn vx vy weq vz wal vx vy weq vx ax-4 vx vy vz ax-12o syl7 vx vy weq
    vx wal vx vy weq vz wal wi vx vz vx vy weq vx vz ax-10o aecoms-o vx vy weq
    vx wal vx vy weq vz wal wi vy vz vx vy weq vx wal vx vy weq vy wal vy vz
    weq vy wal vx vy weq vz wal vx vy weq vx wal vx vy weq vy wal vx vy weq vx
    vy ax-10o pm2.43i vx vy weq vy vz ax-10o syl5 aecoms-o pm2.61ii a5i-o vx vy
    weq vx vz ax-7 syl $.

  ${
    dral1-o.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  Version of
       ~ dral1 using ~ ax-10o .  (Contributed by NM, 24-Nov-1994.)
       (New usage is discouraged.) $)
    dral1-o $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      vx vy weq vx wal wph vx wal wps vy wal vx vy weq vx wal wph vx wal wps vx
      wal wps vy wal vx vy weq vx wal wph wps vx vx vy vx hbae-o vx vy weq vx
      wal wph wps dral1-o.1 biimpd alimdh wps vx vy ax-10o syld vx vy weq vx
      wal wps vy wal wph vy wal wph vx wal vx vy weq vx wal wps wph vy vx vy vy
      hbae-o vx vy weq vx wal wph wps dral1-o.1 biimprd alimdh wph vy wal wph
      vx wal wi vy vx wph vy vx ax-10o aecoms-o syld impbid $.
  $}

  $( Rederivation of axiom ~ ax-11 from ~ ax-11o , ~ ax-10o , and other older
     axioms.  The proof does not require ~ ax-16 or ~ ax-17 .  See theorem
     ~ ax11o for the derivation of ~ ax-11o from ~ ax-11 .

     An open problem is whether we can prove this using ~ ax-10 instead of
     ~ ax-10o .

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 22-Jan-2007.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax11 $p |- ( x = y -> ( A. y ph -> A. x ( x = y -> ph ) ) ) $=
    vx vy weq vx wal vx vy weq wph vy wal vx vy weq wph wi vx wal wi wi vx vy
    weq vx wal wph vy wal vx vy weq wph wi vx wal wi vx vy weq vx vy weq vx wal
    wph vy wal wph vx wal vx vy weq wph wi vx wal wph wph vx vy vx vy weq vx
    wal wph biidd dral1-o wph vx vy weq wph wi vx wph vx vy weq ax-1 alimi
    syl6bir a1d wph vy wal wph vx vy weq vx wal wn vx vy weq vx vy weq wph wi
    vx wal wph vy ax-4 wph vx vy ax-11o syl7 pm2.61i $.

  $( Derive ~ ax-12 from ~ ax-12o and other older axioms.

     This proof uses newer axioms ~ ax-5 and ~ ax-9 , but since these are
     proved from the older axioms above, this is acceptable and lets us avoid
     having to reprove several earlier theorems to use ~ ax-5o and ~ ax-9o .
     (Contributed by NM, 21-Dec-2015.)  (Proof modification is discouraged.)
     (New usage is discouraged.) $)
  ax12 $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
    vx vy weq wn vy vz weq vy vz weq vx wal vx vy weq wn vy vz weq vy vz weq vy
    vz weq vx wal wi vx vy weq wn vy vz weq wa vx vy weq vx wal wn vx vz weq vx
    wal wn vy vz weq vy vz weq vx wal wi vx vy weq wn vx vy weq vx wal wn vy vz
    weq vx vy weq vx wal vx vy weq vx vy weq vx ax-4 con3i adantr vx vy weq wn
    vy vz weq wa vx vz weq vx vz weq vx wal vx vy weq wn vy vz weq vx vz weq wn
    vy vz weq vx vz weq vx vy weq vx vz weq vx vy weq wi vz vy vz vy vx equtrr
    equcoms con3rr3 imp vx vz weq vx ax-4 nsyl vy vz vx ax-12o sylc ex pm2.43d
    $.


