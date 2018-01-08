
$[ uset-100000/CLASSICAL_FIRST_ORDER_LOGIC_WITH_EQUALITY/Predicate_calculus_with_equality___Auxiliary_axiom_schemes_(4_schemes)/Axiom_scheme_ax-11_(Substitution).mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
          Axiom scheme ax-12 (Quantified Equality)

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Axiom of Quantified Equality.  One of the equality and substitution axioms
     of predicate calculus with equality.

     An equivalent way to express this axiom that may be easier to understand
     is ` ( -. x = y -> ( -. x = z -> ( y = z -> A. x y = z ) ) ) ` (see
     ~ ax12b ).  Recall that in the intended interpretation, our variables are
     metavariables ranging over the variables of predicate calculus (the object
     language).  In order for the first antecedent ` -. x = y ` to hold, ` x `
     and ` y ` must have different values and thus cannot be the same
     object-language variable.  Similarly, ` x ` and ` z ` cannot be the same
     object-language variable.  Therefore, ` x ` will not occur in the wff
     ` y = z ` when the first two antecedents hold, so analogous to ~ ax-17 ,
     the conclusion ` ( y = z -> A. x y = z ) ` follows.

     The original version of this axiom was ~ ax-12o and was replaced with this
     shorter ~ ax-12 in December 2015.  The old axiom is proved from this one
     as theorem ~ ax12o .  Conversely, this axiom is proved from ~ ax-12o as
     theorem ~ ax12 .

     The primary purpose of this axiom is to provide a way to introduce the
     quantifier ` A. x ` on ` y = z ` even when ` x ` and ` y ` are substituted
     with the same variable.  In this case, the first antecedent becomes
     ` -. x = x ` and the axiom still holds.

     Although this version is shorter, the original version ~ ax12o may be more
     practical to work with because of the "distinctor" form of its
     antecedents.  A typical application of ~ ax12o is in ~ dvelimh which
     converts a distinct variable pair to the distinctor antecendent
     ` -. A. x x = y ` .

     This axiom can be weakened if desired by adding distinct variable
     restrictions on pairs ` x , z ` and ` y , z ` .  To show that, we add
     these restrictions to theorem ~ ax12v and use only ~ ax12v for further
     derivations.  Thus, ~ ax12v should be the only theorem referencing this
     axiom.  Other theorems can reference either ~ ax12v or ~ ax12o .

     This axiom scheme is logically redundant (see ~ ax12w ) but is used as an
     auxiliary axiom to achieve metalogical completeness.  (Contributed by NM,
     21-Dec-2015.)  (New usage is discouraged.) $)
  ax-12 $a |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.

  ${
    $d x z $.  $d y z $.
    $( A weaker version of ~ ax-12 with distinct variable restrictions on pairs
       ` x , z ` and ` y , z ` .  In order to show that this weakening is
       adequate, this should be the only theorem referencing ~ ax-12 directly.
       (Contributed by NM, 30-Jun-2016.) $)
    ax12v $p |- ( -. x = y -> ( y = z -> A. x y = z ) ) $=
      vx vy vz ax-12 $.
  $}

  ${
    $d w y $.  $d w z $.
    $( Lemma for ~ ax12o .  Similar to ~ equvin but with a negated equality.
       (Contributed by NM, 24-Dec-2015.) $)
    ax12olem1 $p |- ( E. w ( y = w /\ -. z = w ) <-> -. y = z ) $=
      vy vw weq vz vw weq wn wa vw wex vy vz weq wn vy vw weq vz vw weq wn wa
      vy vz weq wn vw vy vw weq vy vz weq vz vw weq vy vw weq vy vz weq vw vz
      weq vz vw weq vy vw vz ax-8 vw vz equcomi syl6 con3and exlimiv vy vz weq
      wn vy vw weq vz vw weq wn wa vw vy vy vz weq wn vw ax-17 vw vy weq vy vz
      weq wn vz vw weq wn vy vw weq vw vy weq vz vw weq vy vz weq vz vw weq vw
      vy weq vy vz weq vw vy weq vy vz weq wi vw vz vw vz weq vw vy weq vz vy
      weq vy vz weq vw vz vy ax-8 vz vy equcomi syl6 equcoms com12 con3d vw vy
      equcomi jctild spimeh impbii $.
  $}

  ${
    $d w x z $.  $d w y $.
    ax12olem2.1 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
    $( Lemma for ~ ax12o .  Negate the equalities in ~ ax-12 , shown as the
       hypothesis.  (Contributed by NM, 24-Dec-2015.) $)
    ax12olem2 $p |- ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) $=
      vx vy weq wn vy vw weq vz vw weq wn wa vw wex vy vw weq vz vw weq wn wa
      vw wex vx wal vy vz weq wn vy vz weq wn vx wal vx vy weq wn vy vw weq vz
      vw weq wn wa vw wex vy vw weq vz vw weq wn wa vx wal vw wex vy vw weq vz
      vw weq wn wa vw wex vx wal vx vy weq wn vy vw weq vz vw weq wn wa vy vw
      weq vz vw weq wn wa vx wal vw vx vy weq wn vy vw weq vz vw weq wn wa vy
      vw weq vx wal vz vw weq wn wa vy vw weq vz vw weq wn wa vx wal vx vy weq
      wn vy vw weq vy vw weq vx wal vz vw weq wn ax12olem2.1 anim1d vy vw weq
      vx wal vz vw weq wn wa vy vw weq vx wal vz vw weq wn vx wal wa vy vw weq
      vz vw weq wn wa vx wal vz vw weq wn vz vw weq wn vx wal vy vw weq vx wal
      vz vw weq wn vx ax-17 anim2i vy vw weq vz vw weq wn vx 19.26 sylibr syl6
      eximdv vy vw weq vz vw weq wn wa vw vx 19.12 syl6 vy vz vw ax12olem1 vy
      vw weq vz vw weq wn wa vw wex vy vz weq wn vx vy vz vw ax12olem1 albii
      3imtr3g $.
  $}

  $( Lemma for ~ ax12o .  Show the equivalence of an intermediate equivalent to
     ~ ax12o with the conjunction of ~ ax-12 and a variant with negated
     equalities.  (Contributed by NM, 24-Dec-2015.) $)
  ax12olem3 $p |- ( ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) )
         <-> ( ( -. x = y -> ( y = z -> A. x y = z ) )
            /\ ( -. x = y -> ( -. y = z -> A. x -. y = z ) ) ) ) $=
    vx vy weq wn vy vz weq wn vx wal wn vy vz weq vx wal wi wi vx vy weq wn vy
    vz weq vy vz weq vx wal wi wi vx vy weq wn vy vz weq wn vy vz weq wn vx wal
    wi wi wa vx vy weq wn vy vz weq wn vx wal wn vy vz weq vx wal wi wi vx vy
    weq wn vy vz weq vy vz weq vx wal wi wi vx vy weq wn vy vz weq wn vy vz weq
    wn vx wal wi wi vy vz weq wn vx wal wn vy vz weq vx wal wi vy vz weq vy vz
    weq vx wal wi vx vy weq wn vy vz weq vy vz weq wn vx wal wn vy vz weq vx
    wal vy vz weq wn vx wal vy vz weq vy vz weq wn vx sp con2i imim1i imim2i vy
    vz weq wn vx wal wn vy vz weq vx wal wi vy vz weq wn vy vz weq wn vx wal wi
    vx vy weq wn vy vz weq wn vx wal wn vy vz weq vx wal wi vy vz weq wn vx wal
    vy vz weq vy vz weq vx wal vy vz weq vy vz weq wn vx wal wn vy vz weq vx sp
    imim2i con1d imim2i jca vx vy weq wn vy vz weq vy vz weq vx wal wi wi vx vy
    weq wn vy vz weq wn vy vz weq wn vx wal wi wi vx vy weq wn vy vz weq wn vx
    wal wn vy vz weq vx wal wi wi vy vz weq vy vz weq vx wal wi vy vz weq wn vy
    vz weq wn vx wal wi vy vz weq wn vx wal wn vy vz weq vx wal wi vx vy weq wn
    vy vz weq wn vy vz weq wn vx wal wi vy vz weq vy vz weq vx wal wi vy vz weq
    wn vx wal wn vy vz weq vx wal wi vy vz weq wn vy vz weq wn vx wal wi vy vz
    weq wn vx wal wn vy vz weq vy vz weq vx wal vy vz weq vy vz weq wn vx wal
    con1 imim1d com12 imim3i imp impbii $.

  ${
    $d w x z $.  $d w y z $.
    ax12olem4.1 $e |- ( -. x = y -> ( y = z -> A. x y = z ) ) $.
    ax12olem4.2 $e |- ( -. x = y -> ( y = w -> A. x y = w ) ) $.
    $( Lemma for ~ ax12o .  Construct an intermediate equivalent to ~ ax-12
       from two instances of ~ ax-12 .  (Contributed by NM, 24-Dec-2015.) $)
    ax12olem4 $p |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $=
      vx vy weq wn vy vz weq wn vx wal wn vy vz weq vx wal wi wi vx vy weq wn
      vy vz weq vy vz weq vx wal wi wi vx vy weq wn vy vz weq wn vy vz weq wn
      vx wal wi wi ax12olem4.1 vx vy vz vw ax12olem4.2 ax12olem2 vx vy vz
      ax12olem3 mpbir2an $.
  $}

  ${
    ax12olem5.1 $e |- ( -. x = y -> ( -. A. x -. y = z -> A. x y = z ) ) $.
    $( Lemma for ~ ax12o .  See ~ ax12olem6 for derivation of ~ ax12o from the
       conclusion.  (Contributed by NM, 24-Dec-2015.) $)
    ax12olem5 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      vx vy weq vx wal wn vx vy weq wn vx wex vy vz weq vy vz weq vx wal wi vx
      vy weq vx exnal vy vz weq vy vz weq vx wex vx vy weq wn vx wex vy vz weq
      vx wal vy vz weq vx 19.8a vx vy weq wn vy vz weq vx wex vy vz weq vx wal
      wi vx vy vz weq vx wex vy vz weq vx wal vx vy vz weq vx hbe1 vy vz weq vx
      hba1 hbim vy vz weq vx wex vy vz weq wn vx wal wn vx vy weq wn vy vz weq
      vx wal vy vz weq vx df-ex ax12olem5.1 syl5bi exlimih syl5 sylbir $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    ax12olem6.1 $e |- ( -. A. x x = z -> ( z = w -> A. x z = w ) ) $.
    ax12olem6.2 $e |- ( -. A. x x = y -> ( y = w -> A. x y = w ) ) $.
    $( Lemma for ~ ax12o .  Derivation of ~ ax12o from the hypotheses, without
       using ~ ax12o .  (Contributed by Andrew Salmon, 21-Jul-2011.)  (Revised
       by NM, 24-Dec-2015.) $)
    ax12olem6 $p |- ( -. A. x x = y
      -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $=
      vx vy weq vx wal wn vx vz weq vx wal wn vy vz weq vy vz weq vx wal vx vy
      weq vx wal wn vx vz weq vx wal wn vy vz weq wi vx vz weq vx wal wn vy vz
      weq wi vx wal vx vz weq vx wal wn vy vz weq vx wal wi vx vz weq vx wal wn
      vz vw weq wi vx vz weq vx wal wn vy vz weq wi vx vy vw vx vz weq vx wal
      wn vz vw weq vx vx vz weq vx hbn1 ax12olem6.1 hbim1 vx vz weq vx wal wn
      vy vz weq wi vw ax-17 vw vy weq vz vw weq vy vz weq vx vz weq vx wal wn
      vz vw weq vw vz weq vw vy weq vy vz weq vz vw equcom vw vy vz equequ1
      syl5bb imbi2d ax12olem6.2 dvelimhw vx vz weq vx wal wn vy vz weq vx vx vz
      weq vx hbn1 19.21h syl6ib pm2.86d $.
  $}

  ${
    $d w x $.  $d w y $.  $d w z $.
    ax12olem7.1 $e |- ( -. x = z -> ( -. A. x -. z = w -> A. x z = w ) ) $.
    ax12olem7.2 $e |- ( -. x = y -> ( -. A. x -. y = w -> A. x y = w ) ) $.
    $( Lemma for ~ ax12o .  Derivation of ~ ax12o from the hypotheses, without
       using ~ ax12o .  (Contributed by NM, 24-Dec-2015.) $)
    ax12olem7 $p |- ( -. A. x x = y
              -> ( -. A. x x = z -> ( y = z -> A. x y = z ) ) ) $=
      vx vy vz vw vx vz vw ax12olem7.1 ax12olem5 vx vy vw ax12olem7.2 ax12olem5
      ax12olem6 $.
  $}

  ${
    $d x w v $.  $d y w v $.  $d z w v $.
    $( Derive set.mm's original ~ ax-12o from the shorter ~ ax-12 .
       (Contributed by NM, 29-Nov-2015.)  (Revised by NM, 24-Dec-2015.) $)
    ax12o $p |- ( -. A. z z = x -> ( -. A. z z = y
              -> ( x = y -> A. z x = y ) ) ) $=
      vz vx vy vw vz vy vw vv vz vy vw ax12v vz vy vv ax12v ax12olem4 vz vx vw
      vv vz vx vw ax12v vz vx vv ax12v ax12olem4 ax12olem7 $.
  $}

  ${
    $d x v w $.  $d y v w $.
    $( Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       22-Jul-2015.) $)
    ax10lem1 $p |- ( A. x x = w -> A. y y = w ) $=
      vx vw weq vx wal vv vw weq vv wal vy vw weq vy wal vx vw weq vv vw weq vx
      vv vx vv vw ax-8 cbvalivw vv vw weq vy vw weq vv vy vv vy vw ax-8
      cbvalivw syl $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Lemma for ~ ax10 .  Change free variable.  (Contributed by NM,
       25-Jul-2015.) $)
    ax10lem2 $p |- ( A. x x = y -> A. x x = z ) $=
      vx vz weq vx wal vx vy weq vx wal vx vz weq wn vx wex vx vy weq wn vx wex
      vx vz weq vx wal wn vx vy weq vx wal wn vx vz weq wn vx vy weq wn vx wex
      vx vx vy weq wn vx hbe1 vx vz weq wn vz vy weq vx vy weq wn vx wex vx vz
      weq wn vz vy weq vx vy weq wn vx vy weq wn vx wex vz vy weq vx vy weq vx
      vz weq vz vy weq vx vz weq vx vy weq vz vy vx equequ2 biimprd con3rr3 vx
      vy weq wn vx 19.8a syl6 vz vy weq wn vx vy weq wn vx vz vz vy weq wn vx
      ax-17 vx vz weq vx vy weq wn vz vy weq wn vx vz weq vx vy weq vz vy weq
      vx vz vy equequ1 notbid biimprd spimeh pm2.61d1 exlimih vx vz weq vx
      exnal vx vy weq vx exnal 3imtr3i con4i $.
  $}

  ${
    $d w x y $.  $d w x z $.
    $( Lemma for ~ ax10 .  Similar to ~ ax-10 but with distinct variables.
       (Contributed by NM, 25-Jul-2015.) $)
    ax10lem3 $p |- ( A. x x = y -> A. y y = x ) $=
      vx vy weq vx wal vx vz weq vx wal vy vx weq vy wal vx vy vz ax10lem2 vx
      vz weq vx wal vw vx weq vw wal vy vx weq vy wal vx vz weq vx wal vw vz
      weq vw wal vw vx weq vw wal vx vw vz ax10lem1 vw vz vx ax10lem2 syl vw vy
      vx ax10lem1 syl syl $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ps $.  $d x ph $.
    dvelimv.1 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Similar to ~ dvelim with first hypothesis replaced by distinct variable
       condition.  (Contributed by NM, 25-Jul-2015.) $)
    dvelimv $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      vx vy weq vx wal wn vx vz weq vx wal wps wps vx wal wi vx vz weq vx wal
      wn vx vy weq vx wal wn wps wps vx wal wi wps vz vy weq wph wi vz wal vx
      vz weq vx wal wn vx vy weq vx wal wn wa vz vy weq wph wi vz wal vx wal
      wps vx wal wps vz vy weq wps vz wal wi vz wal vz vy weq wph wi vz wal wps
      vz vy weq wps vz wal wi vz wps vz ax-17 wps wps vz wal vz vy weq wps vz
      ax-17 a1d alrimih vz vy weq wps vz wal wi vz vy weq wph wi vz vz vy weq
      wps vz wal wph wps vz wal wph vz vy weq wps wps vz sp dvelimv.1 syl5ibr
      a2i alimi syl vx vz weq vx wal wn vx vy weq vx wal wn wa vz vy weq wph wi
      vx vz vx vz weq vx wal wn vx vy weq vx wal wn vz vx vz weq vx wal wn vz
      vx weq vz wal wn vx vz weq vx wal wn vz wal vz vx weq vz wal vx vz weq vx
      wal vz vx ax10lem3 con3i vz vx weq vz wal wn vx vz weq vx wal wn vz vz vx
      weq vz hbn1 vx vz weq vx wal vz vx weq vz wal vx vz ax10lem3 con3i
      alrimih syl vx vy weq vx wal wn vz ax-17 hban vx vz weq vx wal wn vx vy
      weq vx wal wn wa vz vy weq wph vx vx vz weq vx wal wn vx vy weq vx wal wn
      vx vx vz weq vx hbn1 vx vy weq vx hbn1 hban vx vz weq vx wal wn vx vy weq
      vx wal wn vz vy weq vz vy weq vx wal wi vz vy vx ax12o imp vx vz weq vx
      wal wn vx vy weq vx wal wn wa wph vx a17d hbimd hbald vz vy weq wph wi vz
      wal wps vx vz vy weq wph wi vz wal wps wn vz wal wps vz vy weq wph wi vz
      wal vz vy weq wps wi vz wal wps wn vz wal wn vz vy weq wph wi vz vy weq
      wps wi vz vz vy weq wph wps vz vy weq wph wps dvelimv.1 biimpd a2i alimi
      vz vy weq wps wi vz wal wps wn vz wal vz vy weq wn vz wal vz vy ax9v vz
      vy weq wps wi wps wn vz vy weq wn vz vz vy weq wps con3 al2imi mtoi syl
      wps wn vz ax-17 nsyl2 alimi syl56 expcom vx vz weq vx wal wps vx vz weq
      wps wi vx wal wps vx wal vx vz weq vx wal vx vz weq wps wps vz wal vx vz
      weq wps wi vx wal vx vz weq vx sp wps vz ax-17 wps vx vz ax-11 syl2im vx
      vz weq vx vz weq wps wi wps vx vx vz weq wps pm2.27 al2imi syld pm2.61d2
      $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.)  (Revised by NM, 20-Jul-2015.) $)
    dveeq2 $p |- ( -. A. x x = y -> ( z = y -> A. x z = y ) ) $=
      vz vw weq vz vy weq vx vy vw vw vy vz equequ2 dvelimv $.
  $}

  ${
    $d w z x $.  $d w z y $.
    $( Lemma for ~ ax10 .  Change bound variable.  (Contributed by NM,
       8-Jul-2016.) $)
    ax10lem4 $p |- ( A. x x = w -> A. y y = x ) $=
      vx vw weq vx wal vy vx weq vy wal vy vx weq vy wal wn vx vw weq vx wal vy
      vx weq vy wal vy vx weq vy wal wn vx vw weq vx wal vy vx weq vy wal vy vx
      weq vy wal wn vx vw weq vx vw weq vx wal vy vx weq vy wal wi vx vx vw weq
      vx wal vy vw weq vy wal vy vx weq vy wal wn vx vw weq vy vx weq vy wal vx
      vy vw ax10lem1 vy vx weq vy wal wn vx vw weq vx vw weq vy wal vy vw weq
      vy wal vy vx weq vy wal wi vz vw weq vx vw weq vy vx vz vz vx vw equequ1
      dvelimv vx vw weq vy wal vy vx weq vy wal vy vw weq vy wal vx vw weq vy
      wal vy vx weq vy vw weq vy vx vw weq vy hba1 vx vw weq vy vx weq vy vw
      weq wb vy vx vw vy equequ2 sps albidh biimprd syl6 syl7 spsd pm2.43d
      com12 pm2.18d $.
  $}

  ${
    $d w z $.  $d u v w $.  $d v x $.  $d v y $.
    $( Lemma for ~ ax10 .  Change free and bound variables.  (Contributed by
       NM, 22-Jul-2015.) $)
    ax10lem5 $p |- ( A. z z = w -> A. y y = x ) $=
      vz vw weq vz wal vx vv weq vx wal vy vx weq vy wal vz vw weq vz wal vu vv
      weq vu wal vx vv weq vx wal vz vw weq vz wal vv vw weq vv wal vu vv weq
      vu wal vz vv vw ax10lem1 vv vu vw ax10lem4 syl vu vx vv ax10lem1 syl vx
      vy vv ax10lem4 syl $.
  $}

  $( Lemma for ~ ax10 .  Similar to ~ ax10o but with reversed antecedent.
     (Contributed by NM, 25-Jul-2015.) $)
  ax10lem6 $p |- ( A. y y = x -> ( A. x ph -> A. y ph ) ) $=
    vy vx weq vy wal wph vx wal vy vx weq wph wi vy wal wph vy wal vy vx weq
    wph vx wal vy vx weq wph wi vy wal wi vy wph vy vx ax-11 sps vy vx weq vy
    vx weq wph wi wph vy vy vx weq wph pm2.27 al2imi syld $.

  ${
    $d x z $.  $d y z $.
    $( Derive set.mm's original ~ ax-10 from others.  (Contributed by NM,
       25-Jul-2015.)  (Revised by NM, 7-Nov-2015.) $)
    ax10 $p |- ( A. x x = y -> A. y y = x ) $=
      vx vy weq vx wal vz vx weq wn vz wal wn vy vx weq vy wal vz vx ax9v vz vx
      weq wn vz wal wn vz vx weq vz wex vx vy weq vx wal vy vx weq vy wal vz vx
      weq vz df-ex vx vy weq vx wal vz vx weq vy vx weq vy wal vz vx vy weq vx
      wal vz vx weq vy vx weq vy wal wn vy vx weq vy wal wi vy vx weq vy wal vx
      vy weq vx wal vy vx weq vy wal wn vz vx weq vy vx weq vy wal vy vx weq vy
      wal wn vz vx weq wa vz vx weq vy wal vx vy weq vx wal vx vz weq vx wal vy
      vx weq vy wal vy vx weq vy wal wn vz vx weq vz vx weq vy wal vy vx vz
      dveeq2 imp vx vy weq vx wal vz vx weq vy wal vz vx weq vx wal vx vz weq
      vx wal vz vx weq vy vx ax10lem6 vz vx weq vx vz weq vx vz vx equcomi
      alimi syl6 vx vy vx vz ax10lem5 syl56 exp3acom23 vy vx weq vy wal pm2.18
      syl6 exlimdv syl5bir mpi $.
  $}

  ${
    $d x y $.  $d w ph $.  $d w z $.
    $( Generalization of ~ ax16 .  (Contributed by NM, 25-Jul-2015.) $)
    a16g $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      vw vz weq vw wex vx vy weq vx wal vw vz weq vw wal wph wph vz wal wi vw
      vz a9ev vz vw vx vy ax10lem5 vw vz weq vw vz weq vw wal wph wph vz wal wi
      wi vw vw vz weq vw wal wph wph vz wal wi vw vz weq vw wal wph wph vz wal
      wi wi vw wal vw vz weq vw wal wn vw vz weq vw wal wph wph vz wal wi wi vw
      vw vz weq vw hbn1 vw vz weq vw wal wph wph vz wal wi pm2.21 alrimih wph
      wph vz wal wi vw vz weq vw wal wph wph vz wal wi wi vw wph wph vz wal wi
      vw ax-17 wph wph vz wal wi vw vz weq vw wal ax-1 alrimih ja vw vz weq vw
      wal vz vw weq vz wal vw vz weq wph wph vz wal wi vw vz vw vz ax10lem5 vw
      vz weq wph vz vw weq vz wal wph vz wal vw vz weq wph vz vw weq wph wi vz
      wal vz vw weq vz wal wph vz wal wi vw vz weq vz vw weq wph wph vw wal vz
      vw weq wph wi vz wal vw vz equcomi wph vw ax-17 wph vz vw ax-11 syl2im vz
      vw weq wph vz ax-5 syl6 com23 syl5 exlimih mpsyl $.
  $}

  $( Commutation law for identical variable specifiers.  The antecedent and
     consequent are true when ` x ` and ` y ` are substituted with the same
     variable.  Lemma L12 in [Megill] p. 445 (p. 12 of the preprint).
     (Contributed by NM, 5-Aug-1993.) $)
  aecom $p |- ( A. x x = y -> A. y y = x ) $=
    vx vy ax10 $.

  ${
    alequcoms.1 $e |- ( A. x x = y -> ph ) $.
    $( A commutation rule for identical variable specifiers.  (Contributed by
       NM, 5-Aug-1993.) $)
    aecoms $p |- ( A. y y = x -> ph ) $=
      vy vx weq vy wal vx vy weq vx wal wph vy vx aecom alequcoms.1 syl $.
  $}

  ${
    nalequcoms.1 $e |- ( -. A. x x = y -> ph ) $.
    $( A commutation rule for distinct variable specifiers.  (Contributed by
       NM, 2-Jan-2002.) $)
    naecoms $p |- ( -. A. y y = x -> ph ) $=
      wph vy vx weq vy wal vx vy weq vx wal vy vx weq vy wal wph vx vy aecom
      nalequcoms.1 nsyl4 con1i $.
  $}

  ${
    $d x v z $.  $d y v z $.
    $( Theorem showing that ~ ax-9 follows from the weaker version ~ ax9v .
       (Even though this theorem depends on ~ ax-9 , all references of ~ ax-9
       are made via ~ ax9v .  An earlier version stated ~ ax9v as a separate
       axiom, but having two axioms caused some confusion.)

       This theorem should be referenced in place of ~ ax-9 so that all proofs
       can be traced back to ~ ax9v .  (Contributed by NM, 12-Nov-2013.)
       (Revised by NM, 25-Jul-2015.) $)
    ax9 $p |- -. A. x -. x = y $=
      vx vy weq vx wal vx vy weq wn vx wal wn vx vy weq wn vx wal vx vy weq vx
      vy weq vx wal vx vy weq wn vx sp vx vy weq vx sp nsyl3 vx vy weq vx wal
      wn vx vy weq wn vx wal wn wi vv vy weq wn vv wal vv vy ax9v vx vy weq vx
      wal wn vx vy weq wn vx wal wn wi wn vv vy weq wn vv vv vy weq vx vy weq
      vx wal wn vx vy weq wn vx wal wn wi vx vy weq vx wal wn vv vy weq vv vy
      weq vx wal vx vy weq wn vx wal wn vx vy vv dveeq2 vv vy weq vx wal vx vv
      weq wn vx wal vx vy weq wn vx wal vx vv ax9v vv vy weq vx wal vx vv weq
      wn vx vy weq wn vx vv vy weq vx hba1 vv vy weq vx wal vx vv weq vx vy weq
      vv vy weq vx wal vv vy weq vx vv weq vx vy weq wb vv vy weq vx sp vv vy
      vx equequ2 syl notbid albidh mtbii syl6com con3i alrimiv mt3 pm2.61i $.
  $}

  $( Show that the original axiom ~ ax-9o can be derived from ~ ax9 and
     others.  See ~ ax9from9o for the rederivation of ~ ax9 from ~ ax-9o .

     Normally, ~ ax9o should be used rather than ~ ax-9o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof modification is discouraged.) $)
  ax9o $p |- ( A. x ( x = y -> A. x ph ) -> ph ) $=
    vx vy weq wph vx wal wi vx wal wph vx wal wn vx wal wn wph vx vy weq wph vx
    wal wi vx wal wph vx wal wn vx wal vx vy weq wn vx wal vx vy ax9 vx vy weq
    wph vx wal wi wph vx wal wn vx vy weq wn vx vx vy weq wph vx wal con3
    al2imi mtoi wph vx ax6o syl $.

  $( At least one individual exists.  This is not a theorem of free logic,
     which is sound in empty domains.  For such a logic, we would add this
     theorem as an axiom of set theory (Axiom 0 of [Kunen] p. 10).  In the
     system consisting of ~ ax-5 through ~ ax-14 and ~ ax-17 , all axioms other
     than ~ ax9 are believed to be theorems of free logic, although the system
     without ~ ax9 is probably not complete in free logic.  (Contributed by NM,
     5-Aug-1993.) $)
  a9e $p |- E. x x = y $=
    vx vy weq vx wex vx vy weq wn vx wal wn vx vy ax9 vx vy weq vx df-ex mpbir
    $.

  $( Show that ~ ax-10o can be derived from ~ ax-10 in the form of ~ ax10 .
     Normally, ~ ax10o should be used rather than ~ ax-10o , except by theorems
     specifically studying the latter's properties.  (Contributed by NM,
     16-May-2008.)  (Proof modification is discouraged.) $)
  ax10o $p |- ( A. x x = y -> ( A. x ph -> A. y ph ) ) $=
    vx vy weq vx wal vy vx weq vy wal wph vx wal vy vx weq wph wi vy wal wph vy
    wal vx vy ax10 vx vy weq wph vx wal vy vx weq wph wi vy wal wi vx wph vx
    wal vy vx weq wph wi vy wal wi vy vx wph vy vx ax-11 equcoms sps vy vx weq
    vy vx weq wph wi wph vy vy vx weq wph pm2.27 al2imi sylsyld $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)
  hbae $p |- ( A. x x = y -> A. z A. x x = y ) $=
    vx vy weq vx wal vx vy weq vz wal vx wal vx vy weq vx wal vz wal vx vy weq
    vx vy weq vz wal vx vz vx weq vz wal vz vy weq vz wal vx vy weq vx wal vx
    vy weq vz wal wi vx vy weq vx wal vx vy weq vz vx weq vz wal wn vz vy weq
    vz wal wn vx vy weq vz wal vx vy weq vx sp vx vy vz ax12o syl7 vx vy weq vx
    wal vx vy weq vz wal wi vx vz vx vy weq vx vz ax10o aecoms vx vy weq vx wal
    vx vy weq vz wal wi vy vz vx vy weq vx wal vx vy weq vy wal vy vz weq vy
    wal vx vy weq vz wal vx vy weq vx wal vx vy weq vy wal vx vy weq vx vy
    ax10o pm2.43i vx vy weq vy vz ax10o syl5 aecoms pm2.61ii a5i vx vy weq vx
    vz ax-7 syl $.

  $( All variables are effectively bound in an identical variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfae $p |- F/ z A. x x = y $=
    vx vy weq vx wal vz vx vy vz hbae nfi $.

  $( All variables are effectively bound in a distinct variable specifier.
     Lemma L19 in [Megill] p. 446 (p. 14 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
  hbnae $p |- ( -. A. x x = y -> A. z -. A. x x = y ) $=
    vx vy weq vx wal vz vx vy vz hbae hbn $.

  $( All variables are effectively bound in a distinct variable specifier.
     (Contributed by Mario Carneiro, 11-Aug-2016.) $)
  nfnae $p |- F/ z -. A. x x = y $=
    vx vy weq vx wal vz vx vy vz nfae nfn $.

  ${
    hbnalequs.1 $e |- ( A. z -. A. x x = y -> ph ) $.
    $( Rule that applies ~ hbnae to antecedent.  (Contributed by NM,
       5-Aug-1993.) $)
    hbnaes $p |- ( -. A. x x = y -> ph ) $=
      vx vy weq vx wal wn vx vy weq vx wal wn vz wal wph vx vy vz hbnae
      hbnalequs.1 syl $.
  $}

  $( A variable is effectively not free in an equality if it is not either of
     the involved variables. ` F/ ` version of ~ ax-12o .  (Contributed by
     Mario Carneiro, 6-Oct-2016.) $)
  nfeqf $p |- ( ( -. A. z z = x /\ -. A. z z = y ) -> F/ z x = y ) $=
    vz vx weq vz wal wn vz vy weq vz wal wn wa vx vy weq vz vz vx weq vz wal wn
    vz vy weq vz wal wn vz vz vx vz nfnae vz vy vz nfnae nfan vz vx weq vz wal
    wn vz vy weq vz wal wn vx vy weq vx vy weq vz wal wi vx vy vz ax12o imp nfd
    $.

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.)  (Proof shortened by Mario Carneiro, 20-May-2014.) $)
  equs4 $p |- ( A. x ( x = y -> ph ) -> E. x ( x = y /\ ph ) ) $=
    vx vy weq wph wi vx wal vx vy weq wph wi vx vy weq wa vx wex vx vy weq wph
    wa vx wex vx vy weq wph wi vx wal vx vy weq vx wex vx vy weq wph wi vx vy
    weq wa vx wex vx vy a9e vx vy weq wph wi vx vy weq vx 19.29 mpan2 vx vy weq
    wph wi vx vy weq wa vx vy weq wph wa vx vx vy weq wph wi vx vy weq vx vy
    weq wph wa vx vy weq wph ancl imp eximi syl $.

  ${
    equsal.1 $e |- F/ x ps $.
    equsal.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Proof shortened by Andrew Salmon, 12-Aug-2011.)  (Revised
       by Mario Carneiro, 3-Oct-2016.) $)
    equsal $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      vx vy weq wph wi vx wal vx vy weq wps vx wal wi vx wal wps vx vy weq wph
      wi vx vy weq wps vx wal wi vx vx vy weq wph wps vx wal vx vy weq wph wps
      wps vx wal equsal.2 wps vx equsal.1 19.3 syl6bbr pm5.74i albii wps vx vy
      weq wps vx wal wi vx wal wps vx vy weq wps vx wal wi vx equsal.1 wps wps
      vx wal vx vy weq wps vx equsal.1 nfri a1d alrimi wps vx vy ax9o impbii
      bitr4i $.
  $}

  ${
    equsalh.1 $e |- ( ps -> A. x ps ) $.
    equsalh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
    equsalh $p |- ( A. x ( x = y -> ph ) <-> ps ) $=
      wph wps vx vy wps vx equsalh.1 nfi equsalh.2 equsal $.
  $}

  ${
    equsex.1 $e |- F/ x ps $.
    equsex.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.) $)
    equsex $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      vx vy weq wph wn wi wn vx wex vx vy weq wph wn wi vx wal wn vx vy weq wph
      wa vx wex wps vx vy weq wph wn wi vx exnal vx vy weq wph wa vx vy weq wph
      wn wi wn vx vx vy weq wph df-an exbii vx vy weq wph wn wi vx wal wps wph
      wn wps wn vx vy wps vx equsex.1 nfn vx vy weq wph wps equsex.2 notbid
      equsal con2bii 3bitr4i $.
  $}

  ${
    equsexh.1 $e |- ( ps -> A. x ps ) $.
    equsexh.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( A useful equivalence related to substitution.  (Contributed by NM,
       5-Aug-1993.) $)
    equsexh $p |- ( E. x ( x = y /\ ph ) <-> ps ) $=
      wph wps vx vy wps vx equsexh.1 nfi equsexh.2 equsex $.
  $}

  ${
    dvelimh.1 $e |- ( ph -> A. x ph ) $.
    dvelimh.2 $e |- ( ps -> A. z ps ) $.
    dvelimh.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.) $)
    dvelimh $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      vx vy weq vx wal wn vz vy weq wph wi vz wal vz vy weq wph wi vz wal vx
      wal wps wps vx wal vx vz weq vx wal vx vy weq vx wal wn vz vy weq wph wi
      vz wal vz vy weq wph wi vz wal vx wal wi wi vx vz weq vx wal vz vy weq
      wph wi vz wal vz vy weq wph wi vz wal vx wal wi vx vy weq vx wal wn vz vy
      weq wph wi vz wal vz vy weq wph wi vz wal vz wal vx vz weq vx wal vz vy
      weq wph wi vz wal vx wal vz vy weq wph wi vz hba1 vz vy weq wph wi vz wal
      vz wal vz vy weq wph wi vz wal vx wal wi vz vx vz vy weq wph wi vz wal vz
      vx ax10o aecoms syl5 a1d vx vz weq vx wal wn vx vy weq vx wal wn vz vy
      weq wph wi vz wal vz vy weq wph wi vz wal vx wal wi vx vz weq vx wal wn
      vx vy weq vx wal wn wa vz vy weq wph wi vx vz vx vz weq vx wal wn vx vy
      weq vx wal wn vz vx vz vz hbnae vx vy vz hbnae hban vx vz weq vx wal wn
      vx vy weq vx wal wn wa vz vy weq wph vx vx vz weq vx wal wn vx vy weq vx
      wal wn vx vx vz vx hbnae vx vy vx hbnae hban vx vz weq vx wal wn vx vy
      weq vx wal wn vz vy weq vz vy weq vx wal wi vz vy vx ax12o imp wph wph vx
      wal wi vx vz weq vx wal wn vx vy weq vx wal wn wa dvelimh.1 a1i hbimd
      hbald ex pm2.61i wph wps vz vy dvelimh.2 dvelimh.3 equsalh vz vy weq wph
      wi vz wal wps vx wph wps vz vy dvelimh.2 dvelimh.3 equsalh albii 3imtr3g
      $.
  $}

  ${
    dral1.1 $e |- ( A. x x = y -> ( ph <-> ps ) ) $.
    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 24-Nov-1994.) $)
    dral1 $p |- ( A. x x = y -> ( A. x ph <-> A. y ps ) ) $=
      vx vy weq vx wal wph vx wal wps vy wal vx vy weq vx wal wph vx wal wps vx
      wal wps vy wal vx vy weq vx wal wph wps vx vx vy vx hbae vx vy weq vx wal
      wph wps dral1.1 biimpd alimdh wps vx vy ax10o syld vx vy weq vx wal wps
      vy wal wph vy wal wph vx wal vx vy weq vx wal wps wph vy vx vy vy hbae vx
      vy weq vx wal wph wps dral1.1 biimprd alimdh wph vy wal wph vx wal wi vy
      vx wph vy vx ax10o aecoms syld impbid $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    dral2 $p |- ( A. x x = y -> ( A. z ph <-> A. z ps ) ) $=
      vx vy weq vx wal wph wps vz vx vy vz hbae dral1.1 albidh $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    drex1 $p |- ( A. x x = y -> ( E. x ph <-> E. y ps ) ) $=
      vx vy weq vx wal wph wn vx wal wn wps wn vy wal wn wph vx wex wps vy wex
      vx vy weq vx wal wph wn vx wal wps wn vy wal wph wn wps wn vx vy vx vy
      weq vx wal wph wps dral1.1 notbid dral1 notbid wph vx df-ex wps vy df-ex
      3bitr4g $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).
       (Contributed by NM, 27-Feb-2005.) $)
    drex2 $p |- ( A. x x = y -> ( E. z ph <-> E. z ps ) ) $=
      vx vy weq vx wal wph wps vz vx vy vz hbae dral1.1 exbidh $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
    drnf1 $p |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) ) $=
      vx vy weq vx wal wph wph vx wal wi vx wal wps wps vy wal wi vy wal wph vx
      wnf wps vy wnf wph wph vx wal wi wps wps vy wal wi vx vy vx vy weq vx wal
      wph wps wph vx wal wps vy wal dral1.1 wph wps vx vy dral1.1 dral1 imbi12d
      dral1 wph vx df-nf wps vy df-nf 3bitr4g $.

    $( Formula-building lemma for use with the Distinctor Reduction Theorem.
       (Contributed by Mario Carneiro, 4-Oct-2016.) $)
    drnf2 $p |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) ) $=
      vx vy weq vx wal wph wph vz wal wi vz wal wps wps vz wal wi vz wal wph vz
      wnf wps vz wnf wph wph vz wal wi wps wps vz wal wi vx vy vz vx vy weq vx
      wal wph wps wph vz wal wps vz wal dral1.1 wph wps vx vy vz dral1.1 dral2
      imbi12d dral2 wph vz df-nf wps vz df-nf 3bitr4g $.
  $}

  ${
    exdistrf.1 $e |- ( -. A. x x = y -> F/ y ph ) $.
    $( Distribution of existential quantifiers, with a bound-variable
       hypothesis saying that ` y ` is not free in ` ph ` , but ` x ` can be
       free in ` ph ` (and there is no distinct variable condition on ` x ` and
       ` y ` ).  (Contributed by Mario Carneiro, 20-Mar-2013.) $)
    exdistrf $p |- ( E. x E. y ( ph /\ ps ) -> E. x ( ph /\ E. y ps ) ) $=
      vx vy weq vx wal wph wps wa vy wex vx wex wph wps vy wex wa vx wex wi vx
      vy weq vx wal wph wps wa vy wex vx wex wph wps wa vx wex vx wex wph wps
      vy wex wa vx wex wph wps wa vx wex wph wps wa vy wex vx vy vx wph wps wa
      wph wps wa vx vy vx vy weq vx wal wph wps wa biidd drex1 drex2 wph wps wa
      vx wex vx wex wph wps wa vx wex wph wps vy wex wa vx wex wph wps wa vx
      wex vx wph wps wa vx nfe1 19.9 wph wps wa wph wps vy wex wa vx wps wps vy
      wex wph wps vy 19.8a anim2i eximi sylbi syl6bir vx vy weq vx wal wn wph
      wps wa vy wex wph wps vy wex wa vx vx vy vx nfnae wph wps wa vy wex wph
      vy wex wps vy wex wa vx vy weq vx wal wn wph wps vy wex wa wph wps vy
      19.40 vx vy weq vx wal wn wph vy wex wph wps vy wex wph vx vy weq vx wal
      wn vy exdistrf.1 19.9d anim1d syl5 eximd pm2.61i $.
  $}

  ${
    nfald2.1 $e |- F/ y ph $.
    nfald2.2 $e |- ( ( ph /\ -. A. x x = y ) -> F/ x ps ) $.
    $( Variation on ~ nfald which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    nfald2 $p |- ( ph -> F/ x A. y ps ) $=
      wph vx vy weq vx wal wps vy wal vx wnf wph vx vy weq vx wal wn wps vy wal
      vx wnf wph vx vy weq vx wal wn wa wps vx vy wph vx vy weq vx wal wn vy
      nfald2.1 vx vy vy nfnae nfan nfald2.2 nfald ex vx vy weq vx wal wps vy
      wal vx wnf wps vy wal vy wnf wps vy nfa1 wps vy wal wps vy wal vx vy vx
      vy weq vx wal wps vy wal biidd drnf1 mpbiri pm2.61d2 $.

    $( Variation on ~ nfexd which adds the hypothesis that ` x ` and ` y ` are
       distinct in the inner subproof.  (Contributed by Mario Carneiro,
       8-Oct-2016.) $)
    nfexd2 $p |- ( ph -> F/ x E. y ps ) $=
      wps vy wex wps wn vy wal wn wph vx wps vy df-ex wph wps wn vy wal vx wph
      wps wn vx vy nfald2.1 wph vx vy weq vx wal wn wa wps vx nfald2.2 nfnd
      nfald2 nfnd nfxfrd $.
  $}

  $( Closed theorem form of ~ spim .  (Contributed by NM, 15-Jan-2008.)
     (Revised by Mario Carneiro, 17-Oct-2016.) $)
  spimt $p |- ( ( F/ x ps /\ A. x ( x = y -> ( ph -> ps ) ) ) ->
              ( A. x ph -> ps ) ) $=
    wps vx wnf vx vy weq wph wps wi wi vx wal wa wph vx wal vx vy weq wps vx
    wal wi vx wal wps wps vx wnf wph vx wal vx vy weq wph wps wi wi vx wal vx
    vy weq wps vx wal wi vx wal wps vx wnf wph vx wal wa vx vy weq wph wps wi
    wi vx vy weq wps vx wal wi vx wps vx wnf wph vx wal vx wps vx nfnf1 wph vx
    nfa1 nfan wps vx wnf wph vx wal wa wph wps wi wps vx wal vx vy weq wps vx
    wnf wph vx wal wa wph wps wps vx wal wph vx wal wph wps vx wnf wph vx sp
    adantl wps vx wnf wps wps vx wal wi wph vx wal wps vx nfr adantr embantd
    imim2d alimd impancom wps vx vy ax9o syl6 $.

  ${
    spim.1 $e |- F/ x ps $.
    spim.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Specialization, using implicit substitution.  Compare Lemma 14 of
       [Tarski] p. 70.  The ~ spim series of theorems requires that only one
       direction of the substitution hypothesis hold.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 3-Oct-2016.) $)
    spim $p |- ( A. x ph -> ps ) $=
      wps vx wnf vx vy weq wph wps wi wi vx wal wph vx wal wps wi spim.1 vx vy
      weq wph wps wi wi vx spim.2 ax-gen wph wps vx vy spimt mp2an $.
  $}

  ${
    spime.1 $e |- F/ x ph $.
    spime.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Existential introduction, using implicit substitution.  Compare Lemma 14
       of [Tarski] p. 70.  (Contributed by NM, 7-Aug-1994.)  (Revised by Mario
       Carneiro, 3-Oct-2016.) $)
    spime $p |- ( ph -> E. x ps ) $=
      wph wps wn vx wal wn wps vx wex wps wn vx wal wph wps wn wph wn vx vy wph
      vx spime.1 nfn vx vy weq wph wps spime.2 con3d spim con2i wps vx df-ex
      sylibr $.
  $}

  ${
    spimed.1 $e |- ( ch -> F/ x ph ) $.
    spimed.2 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Deduction version of ~ spime .  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 3-Oct-2016.) $)
    spimed $p |- ( ch -> ( ph -> E. x ps ) ) $=
      wch wph vx wnf wph wps vx wex wi spimed.1 wph vx wnf wph wps vx wex wph
      vx wnf wph wa wps vx vy wph vx wnf wph vx wph vx nfnf1 wph vx wnf id
      nfan1 vx vy weq wph wps wph vx wnf spimed.2 adantld spime ex syl $.
  $}

  ${
    cbv1h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv1h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv1h.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbv1h $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      wph vy wal vx wal wps vx wal wps vx wal vy wal wch vy wal wph vy wal vx
      wal wps vx wal wps vy wal vx wal wps vx wal vy wal wph vy wal wps wps vy
      wal vx wph wps wps vy wal wi vy cbv1h.1 sps al2imi wps vx vy ax-7 syl6
      wph wps vx wal vy wal wch vy wal wi vy vx wph vx wal wps vx wal wch vy
      wph vx wal wps vx wal vx vy weq wch vx wal wi vx wal wch wph wps vx vy
      weq wch vx wal wi vx wph wps vx vy weq wch wch vx wal wph vx vy weq wps
      wch cbv1h.3 com23 cbv1h.2 syl6d al2imi wch vx vy ax9o syl6 al2imi a7s
      syld $.
  $}

  ${
    cbv1.1 $e |- ( ph -> F/ y ps ) $.
    cbv1.2 $e |- ( ph -> F/ x ch ) $.
    cbv1.3 $e |- ( ph -> ( x = y -> ( ps -> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    cbv1 $p |- ( A. x A. y ph -> ( A. x ps -> A. y ch ) ) $=
      wph wps wch vx vy wph wps vy cbv1.1 nfrd wph wch vx cbv1.2 nfrd cbv1.3
      cbv1h $.
  $}

  ${
    cbv2h.1 $e |- ( ph -> ( ps -> A. y ps ) ) $.
    cbv2h.2 $e |- ( ph -> ( ch -> A. x ch ) ) $.
    cbv2h.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbv2h $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      wph vy wal vx wal wps vx wal wch vy wal wph wps wch vx vy cbv2h.1 cbv2h.2
      wph vx vy weq wps wch wb wps wch wi cbv2h.3 wps wch bi1 syl6 cbv1h wph
      wch vy wal wps vx wal wi vy vx wph wch wps vy vx cbv2h.2 cbv2h.1 vy vx
      weq vx vy weq wph wps wch wb wch wps wi vy vx equcomi cbv2h.3 wps wch bi2
      syl56 cbv1h a7s impbid $.
  $}

  ${
    cbv2.1 $e |- ( ph -> F/ y ps ) $.
    cbv2.2 $e |- ( ph -> F/ x ch ) $.
    cbv2.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    cbv2 $p |- ( A. x A. y ph -> ( A. x ps <-> A. y ch ) ) $=
      wph wps wch vx vy wph wps vy cbv2.1 nfrd wph wch vx cbv2.2 nfrd cbv2.3
      cbv2h $.
  $}

  ${
    cbv3.1 $e |- F/ y ph $.
    cbv3.2 $e |- F/ x ps $.
    cbv3.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution, that
       does not use ~ ax-12o .  (Contributed by NM, 5-Aug-1993.) $)
    cbv3 $p |- ( A. x ph -> A. y ps ) $=
      wtru vy wal wph vx wal wps vy wal wi vx wtru wph wps vx vy wph vy wnf
      wtru cbv3.1 a1i wps vx wnf wtru cbv3.2 a1i vx vy weq wph wps wi wi wtru
      cbv3.3 a1i cbv1 wtru vy tru ax-gen mpg $.
  $}

  ${
    cbv3h.1 $e |- ( ph -> A. y ph ) $.
    cbv3h.2 $e |- ( ps -> A. x ps ) $.
    cbv3h.3 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew Salmon,
       25-May-2011.)  (Proof modification is discouraged.) $)
    cbv3h $p |- ( A. x ph -> A. y ps ) $=
      vy vy weq vy wal wph vx wal wps vy wal wi vx vy vy weq wph wps vx vy wph
      wph vy wal wi vy vy weq cbv3h.1 a1i wps wps vx wal wi vy vy weq cbv3h.2
      a1i vx vy weq wph wps wi wi vy vy weq cbv3h.3 a1i cbv1h vy stdpc6 mpg $.
  $}

  ${
    cbval.1 $e |- F/ y ph $.
    cbval.2 $e |- F/ x ps $.
    cbval.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    cbval $p |- ( A. x ph <-> A. y ps ) $=
      wph vx wal wps vy wal wph wps vx vy cbval.1 cbval.2 vx vy weq wph wps
      cbval.3 biimpd cbv3 wps wph vy vx cbval.2 cbval.1 wps wph wi vx vy vx vy
      weq wph wps cbval.3 biimprd equcoms cbv3 impbii $.
  $}

  ${
    cbvex.1 $e |- F/ y ph $.
    cbvex.2 $e |- F/ x ps $.
    cbvex.3 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvex $p |- ( E. x ph <-> E. y ps ) $=
      wph wn vx wal wn wps wn vy wal wn wph vx wex wps vy wex wph wn vx wal wps
      wn vy wal wph wn wps wn vx vy wph vy cbvex.1 nfn wps vx cbvex.2 nfn vx vy
      weq wph wps cbvex.3 notbid cbval notbii wph vx df-ex wps vy df-ex 3bitr4i
      $.
  $}

  ${
    chvar.1 $e |- F/ x ps $.
    chvar.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chvar.3 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by Raph Levien, 9-Jul-2003.)  (Revised by Mario Carneiro,
       3-Oct-2016.) $)
    chvar $p |- ps $=
      wph wps vx wph wps vx vy chvar.1 vx vy weq wph wps chvar.2 biimpd spim
      chvar.3 mpg $.
  $}

  $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109,
     however we do not require ` z ` to be distinct from ` x ` and ` y `
     (making the proof longer).  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  equvini $p |- ( x = y -> E. z ( x = z /\ z = y ) ) $=
    vz vx weq vz wal vz vy weq vz wal vx vy weq vx vz weq vz vy weq wa vz wex
    wi vz vx weq vz wal vx vy weq vx vz weq vz wal vz vy weq vz wex wa vx vz
    weq vz vy weq wa vz wex vz vx weq vz wal vx vz weq vz wal vz vy weq vz wex
    wa vx vy weq vz vx weq vz wal vx vz weq vz wal vz vy weq vz wex vz vx weq
    vx vz weq vz vz vx equcomi alimi vz vy a9e jctir a1d vx vz weq vz vy weq vz
    19.29 syl6 vz vy weq vz wal vx vy weq vx vz weq vz wex vz vy weq vz wal wa
    vx vz weq vz vy weq wa vz wex vz vy weq vz wal vx vy weq vx vz weq vz wex
    vz vy weq vz wal vx vy weq vx vz weq vz wex vz vx weq vz wex vx vz weq vz
    wex vz vx a9e vz vx weq vx vz weq vz vz vx equcomi eximi ax-mp a1ii anc2ri
    vx vz weq vz vy weq vz 19.29r syl6 vz vx weq vz wal vz vy weq vz wal wo wn
    vz vx weq vz wal wn vz vy weq vz wal wn wa vx vy weq vx vz weq vz vy weq wa
    vz wex wi vz vx weq vz wal vz vy weq vz wal ioran vx vy weq vx vz weq vz vy
    weq wa vz vx weq vz wal wn vz vy weq vz wal wn wa vz vx vx vy vz nfeqf vx
    vy weq vx vz weq vz vy weq wa wi vx vz vx vz weq vx vy weq vz vy weq vx vz
    vy ax-8 anc2li equcoms spimed sylbi ecase3 $.

  $( A variable elimination law for equality with no distinct variable
     requirements.  (Compare ~ equvini .)  (Contributed by NM, 1-Mar-2013.)
     (Proof shortened by Mario Carneiro, 17-Oct-2016.) $)
  equveli $p |- ( A. z ( z = x <-> z = y ) -> x = y ) $=
    vz vx weq vz vy weq wb vz wal vz vx weq vz vy weq wi vz wal vz vy weq vz vx
    weq wi vz wal wa vx vy weq vz vx weq vz vy weq vz albiim vz vy weq vz wal
    vz vx weq vz vy weq wi vz wal vz vy weq vz vx weq wi vz wal wa vx vy weq wi
    vz vy weq vz wal vz vy weq vz vx weq wi vz wal vx vy weq vz vx weq vz vy
    weq wi vz wal vz vy weq vz wal vz vy weq vz vx weq wi vz wal vy vy weq vy
    vx weq wi vy wal vx vy weq vz vy weq vz vx weq wi vy vy weq vy vx weq wi vz
    vy vz vy weq vz vy weq vz vx weq wi vy vy weq vy vx weq wi wb vz vz vy weq
    vz vy weq vy vy weq vz vx weq vy vx weq vz vy vy equequ1 vz vy vx equequ1
    imbi12d sps dral1 vy vy weq vy vx weq wi vy wal vy vx weq vx vy weq vy vy
    weq vy vx weq wi vy wal vy vy weq vy vx weq vy equid vy vy weq vy vx weq wi
    vy sp mpi vy vx equcomi syl syl6bi adantld vz vy weq vz wal wn vz vx weq vz
    vy weq wi vz wal vx vy weq vz vy weq vz vx weq wi vz wal vz vx weq vz wal
    vz vy weq vz wal wn vz vx weq vz vy weq wi vz wal vx vy weq wi wi vz vx weq
    vz wal vz vx weq vz vy weq wi vz wal vx vy weq wi vz vy weq vz wal wn vz vx
    weq vz wal vz vx weq vz vy weq wi vz wal vx vx weq vx vy weq wi vz wal vx
    vy weq vz vx weq vz vy weq wi vx vx weq vx vy weq wi vz vx vz vz vx weq vz
    vx weq vz vy weq wi vx vx weq vx vy weq wi wb vz vz vx weq vz vx weq vx vx
    weq vz vy weq vx vy weq vz vx vx equequ1 vz vx vy equequ1 imbi12d sps dral2
    vx vx weq vx vy weq wi vx vy weq vz vx vy weq vx vx weq vx vy weq wi vx vx
    weq vx vy weq vx equid a1bi biimpri sps syl6bi a1d vz vx weq vz wal wn vz
    vy weq vz wal wn vz vx weq vz vy weq wi vz wal vx vy weq wi vz vx weq vz
    wal wn vz vy weq vz wal wn wa vx vy weq vz wnf vz vx weq vz vx weq vz vy
    weq wi vx vy weq wi wi vz wal vz vx weq vz vy weq wi vz wal vx vy weq wi vx
    vy vz nfeqf vz vx weq vz vx weq vz vy weq wi vx vy weq wi wi vz vz vx weq
    vz vx weq vz vy weq wi vx vx weq vx vy weq vx equid vz vx weq vx vx weq vz
    vx weq vz vy weq vx vy weq vz vx vx equtr vz vx vy ax-8 imim12d mpii ax-gen
    vz vx weq vz vy weq wi vx vy weq vz vx spimt sylancl ex pm2.61i adantrd
    pm2.61i sylbi $.

  ${
    equs45f.1 $e |- F/ y ph $.
    $( Two ways of expressing substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 25-Apr-2008.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    equs45f $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      vx vy weq wph wa vx wex vx vy weq wph wi vx wal vx vy weq wph wa vx wex
      vx vy weq wph vy wal wa vx wex vx vy weq wph wi vx wal vx vy weq wph wa
      vx vy weq wph vy wal wa vx wph wph vy wal vx vy weq wph vy equs45f.1 nfri
      anim2i eximi wph vx vy equs5a syl wph vx vy equs4 impbii $.
  $}

  ${
    $d x ps $.
    spimv.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( A version of ~ spim with a distinct variable requirement instead of a
       bound variable hypothesis.  (Contributed by NM, 5-Aug-1993.) $)
    spimv $p |- ( A. x ph -> ps ) $=
      wph wps vx vy wps vx nfv spimv.1 spim $.
  $}

  ${
    $d t u v $.  $d t u x y $.  $d u w $.
    $( A "distinctor elimination" lemma with no restrictions on variables in
       the consequent.  (Contributed by NM, 8-Nov-2006.) $)
    aev $p |- ( A. x x = y -> A. z w = v ) $=
      vx vy weq vx wal vw vv weq vz vx vy vz hbae vx vy weq vx wal vu vv weq vu
      wal vw vv weq vv vu vx vy ax10lem5 vu vv weq vw vv weq vu vw vu vw vv
      ax-8 spimv syl alrimih $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11v2.1 $e |- ( x = z -> ( ph -> A. x ( x = z -> ph ) ) ) $.
    $( Recovery of ~ ax-11o from ~ ax11v .  This proof uses ~ ax-10 and
       ~ ax-11 .  TODO: figure out if this is useful, or if it should be
       simplified or eliminated.  (Contributed by NM, 2-Feb-2007.) $)
    ax11v2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      vx vy weq vx wal wn vz vy weq vz wex vx vy weq wph vx vy weq wph wi vx
      wal wi wi vz vy a9ev vx vy weq vx wal wn vz vy weq vx vy weq wph vx vy
      weq wph wi vx wal wi wi vz vx vy weq vx wal wn vz vy weq vx vy weq wph vx
      vy weq wph wi vx wal wi wi vx vy weq vx wal wn vz vy weq wa vx vz weq wph
      vx vz weq wph wi vx wal wi wi vx vy weq wph vx vy weq wph wi vx wal wi wi
      ax11v2.1 vx vy weq vx wal wn vz vy weq wa vx vz weq vx vy weq wph vx vz
      weq wph wi vx wal wi wph vx vy weq wph wi vx wal wi vz vy weq vx vz weq
      vx vy weq wb vx vy weq vx wal wn vz vy vx equequ2 adantl vx vy weq vx wal
      wn vz vy weq wa vx vz weq wph wi vx wal vx vy weq wph wi vx wal wph vx vy
      weq vx wal wn vz vy weq wa vz vy weq vx wal vx vz weq wph wi vx wal vx vy
      weq wph wi vx wal wb vx vy weq vx wal wn vz vy weq vz vy weq vx wal vx vy
      vz dveeq2 imp vz vy weq vx wal vx vz weq wph wi vx vy weq wph wi vx vz vy
      weq vx nfa1 vz vy weq vx vz weq wph wi vx vy weq wph wi wb vx vz vy weq
      vx vz weq vx vy weq wph vz vy vx equequ2 imbi1d sps albid syl imbi2d
      imbi12d mpbii ex exlimdv mpi $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    ax11a2.1 $e |- ( x = z -> ( A. z ph -> A. x ( x = z -> ph ) ) ) $.
    $( Derive ~ ax-11o from a hypothesis in the form of ~ ax-11 . ~ ax-10 and
       ~ ax-11 are used by the proof, but not ~ ax-10o or ~ ax-11o .  TODO:
       figure out if this is useful, or if it should be simplified or
       eliminated.  (Contributed by NM, 2-Feb-2007.) $)
    ax11a2 $p |- ( -. A. x x = y ->
                 ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      wph vx vy vz wph wph vz wal vx vz weq vx vz weq wph wi vx wal wph vz
      ax-17 ax11a2.1 syl5 ax11v2 $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( Derivation of set.mm's original ~ ax-11o from ~ ax-10 and the shorter
       ~ ax-11 that has replaced it.

       An open problem is whether this theorem can be proved without relying on
       ~ ax-16 or ~ ax-17 (given all of the original and new versions of ~ sp
       through ~ ax-15 ).

       Another open problem is whether this theorem can be proved without
       relying on ~ ax12o .

       Theorem ~ ax11 shows the reverse derivation of ~ ax-11 from ~ ax-11o .

       Normally, ~ ax11o should be used rather than ~ ax-11o , except by
       theorems specifically studying the latter's properties.  (Contributed by
       NM, 3-Feb-2007.) $)
    ax11o $p |- ( -. A. x x = y ->
               ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) ) $=
      wph vx vy vz wph vx vz ax-11 ax11a2 $.
  $}

  $( A bidirectional version of ~ ax11o .  (Contributed by NM, 30-Jun-2006.) $)
  ax11b $p |- ( ( -. A. x x = y /\ x = y ) ->
              ( ph <-> A. x ( x = y -> ph ) ) ) $=
    vx vy weq vx wal wn vx vy weq wa wph vx vy weq wph wi vx wal vx vy weq vx
    wal wn vx vy weq wph vx vy weq wph wi vx wal wi wph vx vy ax11o imp vx vy
    weq vx vy weq wph wi vx wal wph wi vx vy weq vx wal wn vx vy weq wph wi vx
    wal vx vy weq wph vx vy weq wph wi vx sp com12 adantl impbid $.

  $( Lemma used in proofs of substitution properties.  (Contributed by NM,
     5-Aug-1993.) $)
  equs5 $p |- ( -. A. x x = y ->
             ( E. x ( x = y /\ ph ) -> A. x ( x = y -> ph ) ) ) $=
    vx vy weq vx wal wn vx vy weq wph wa vx vy weq wph wi vx wal vx vx vy vx
    nfnae vx vy weq wph wi vx nfa1 vx vy weq vx wal wn vx vy weq wph vx vy weq
    wph wi vx wal wph vx vy ax11o imp3a exlimd $.

  ${
    dvelimf.1 $e |- F/ x ph $.
    dvelimf.2 $e |- F/ z ps $.
    dvelimf.3 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelimv without any variable restrictions.  (Contributed by
       NM, 1-Oct-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    dvelimf $p |- ( -. A. x x = y -> F/ x ps ) $=
      wps vz vy weq wph wi vz wal vx vy weq vx wal wn vx vz vy weq wph wi vz
      wal wps wph wps vz vy dvelimf.2 dvelimf.3 equsal bicomi vx vy weq vx wal
      wn vz vy weq wph wi vx vz vx vy vz nfnae vx vy weq vx wal wn vx vz weq vx
      wal wn wa vz vy weq wph vx vx vy weq vx wal wn vx vz weq vx wal wn wa vz
      vy weq vx vx vy weq vx wal wn vx vz weq vx wal wn vx vx vy vx nfnae vx vz
      vx nfnae nfan vx vz weq vx wal wn vx vy weq vx wal wn vz vy weq vz vy weq
      vx wal wi vz vy vx ax12o impcom nfd wph vx wnf vx vy weq vx wal wn vx vz
      weq vx wal wn wa dvelimf.1 a1i nfimd nfald2 nfxfrd $.
  $}

  ${
    $d x ps $.
    spv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Specialization, using implicit substitution.  (Contributed by NM,
       30-Aug-1993.) $)
    spv $p |- ( A. x ph -> ps ) $=
      wph wps vx vy vx vy weq wph wps spv.1 biimpd spimv $.
  $}

  ${
    $d x ph $.
    spimev.1 $e |- ( x = y -> ( ph -> ps ) ) $.
    $( Distinct-variable version of ~ spime .  (Contributed by NM,
       5-Aug-1993.) $)
    spimev $p |- ( ph -> E. x ps ) $=
      wph wps vx vy wph vx nfv spimev.1 spime $.
  $}

  ${
    $d x ps $.
    speiv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    speiv.2 $e |- ps $.
    $( Inference from existential specialization, using implicit substitution.
       (Contributed by NM, 19-Aug-1993.) $)
    speiv $p |- E. x ph $=
      wps wph vx wex speiv.2 wps wph vx vy vx vy weq wph wps speiv.1 biimprd
      spimev ax-mp $.
  $}

  ${
    $d x z $.  $d y z $.
    $( A variable introduction law for equality.  Lemma 15 of [Monk2] p. 109.
       (Contributed by NM, 5-Aug-1993.) $)
    equvin $p |- ( x = y <-> E. z ( x = z /\ z = y ) ) $=
      vx vy weq vx vz weq vz vy weq wa vz wex vx vy vz equvini vx vz weq vz vy
      weq wa vx vy weq vz vx vz weq vz vy weq vx vy weq vx vz vy equtr imp
      exlimiv impbii $.
  $}

  ${
    $d y ph $.  $d x ps $.
    cbvalv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvalv $p |- ( A. x ph <-> A. y ps ) $=
      wph wps vx vy wph vy nfv wps vx nfv cbvalv.1 cbval $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 5-Aug-1993.) $)
    cbvexv $p |- ( E. x ph <-> E. y ps ) $=
      wph wps vx vy wph vy nfv wps vx nfv cbvalv.1 cbvex $.
  $}

  ${
    $d y x $.  $d y z $.  $d w x $.  $d w z $.
    cbval2.1 $e |- F/ z ph $.
    cbval2.2 $e |- F/ w ph $.
    cbval2.3 $e |- F/ x ps $.
    cbval2.4 $e |- F/ y ps $.
    cbval2.5 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 22-Dec-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    cbval2 $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      wph vy wal wps vw wal vx vz wph vz vy cbval2.1 nfal wps vx vw cbval2.3
      nfal vx vz weq wph vy wal wps vw wal wb wi vx vz weq wph vy wal wa vx vz
      weq wps vw wal wa wb vx vz weq wph wa vy wal vx vz weq wps wa vw wal vx
      vz weq wph vy wal wa vx vz weq wps vw wal wa vx vz weq wph wa vx vz weq
      wps wa vy vw vx vz weq wph vw vx vz weq vw nfv cbval2.2 nfan vx vz weq
      wps vy vx vz weq vy nfv cbval2.4 nfan vy vw weq vx vz weq wph wps vx vz
      weq vy vw weq wph wps wb cbval2.5 expcom pm5.32d cbval vx vz weq wph vy
      19.28v vx vz weq wps vw 19.28v 3bitr3i vx vz weq wph vy wal wps vw wal
      pm5.32 mpbir cbval $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 14-Sep-2003.)  (Revised by Mario Carneiro,
       6-Oct-2016.) $)
    cbvex2 $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      wph vy wex wps vw wex vx vz wph vz vy cbval2.1 nfex wps vx vw cbval2.3
      nfex vx vz weq wph vy wex wps vw wex wb wi vx vz weq wph vy wex wa vx vz
      weq wps vw wex wa wb vx vz weq wph wa vy wex vx vz weq wps wa vw wex vx
      vz weq wph vy wex wa vx vz weq wps vw wex wa vx vz weq wph wa vx vz weq
      wps wa vy vw vx vz weq wph vw vx vz weq vw nfv cbval2.2 nfan vx vz weq
      wps vy vx vz weq vy nfv cbval2.4 nfan vy vw weq vx vz weq wph wps vx vz
      weq vy vw weq wph wps wb cbval2.5 expcom pm5.32d cbvex vx vz weq wph vy
      19.42v vx vz weq wps vw 19.42v 3bitr3i vx vz weq wph vy wex wps vw wex
      pm5.32 mpbir cbvex $.
  $}

  ${
    $d z w ph $.  $d x y ps $.  $d x w $.  $d z y $.
    cbval2v.1 $e |- ( ( x = z /\ y = w ) -> ( ph <-> ps ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 4-Feb-2005.) $)
    cbval2v $p |- ( A. x A. y ph <-> A. z A. w ps ) $=
      wph wps vx vy vz vw wph vz nfv wph vw nfv wps vx nfv wps vy nfv cbval2v.1
      cbval2 $.

    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex2v $p |- ( E. x E. y ph <-> E. z E. w ps ) $=
      wph wps vx vy vz vw wph vz nfv wph vw nfv wps vx nfv wps vy nfv cbval2v.1
      cbvex2 $.
  $}

  ${
    $d x ph $.  $d x ch $.
    cbvald.1 $e |- F/ y ph $.
    cbvald.2 $e |- ( ph -> F/ y ps ) $.
    cbvald.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    cbvald $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      wph wph vy wal vx wal wps vx wal wch vy wal wb wph wph vy wal vx wph vy
      cbvald.1 nfri alrimiv wph wps wch vx vy cbvald.2 wph wch vx nfvd cbvald.3
      cbv2 syl $.

    $( Deduction used to change bound variables, using implicit substitution,
       particularly useful in conjunction with ~ dvelim .  (Contributed by NM,
       2-Jan-2002.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    cbvexd $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      wph wps wn vx wal wn wch wn vy wal wn wps vx wex wch vy wex wph wps wn vx
      wal wch wn vy wal wph wps wn wch wn vx vy cbvald.1 wph wps vy cbvald.2
      nfnd wph vx vy weq wps wch wb wps wn wch wn wb cbvald.3 wps wch notbi
      syl6ib cbvald notbid wps vx df-ex wch vy df-ex 3bitr4g $.
  $}

  ${
    $d ps y $.  $d ch x $.  $d ph x $.  $d ph y $.
    cbvaldva.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Rule used to change the bound variable in a universal quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    cbvaldva $p |- ( ph -> ( A. x ps <-> A. y ch ) ) $=
      wph wps wch vx vy wph vy nfv wph wps vy nfvd wph vx vy weq wps wch wb
      cbvaldva.1 ex cbvald $.

    $( Rule used to change the bound variable in an existential quantifier with
       implicit substitution.  Deduction form.  (Contributed by David Moews,
       1-May-2017.) $)
    cbvexdva $p |- ( ph -> ( E. x ps <-> E. y ch ) ) $=
      wph wps wch vx vy wph vy nfv wph wps vy nfvd wph vx vy weq wps wch wb
      cbvaldva.1 ex cbvexd $.
  $}

  ${
    $v f $.
    $v g $.
    $( Define temporary individual variables. $)
    cbvex4v.vf $f set f $.
    cbvex4v.vg $f set g $.
    $d w z ch $.  $d u v ph $.  $d x y ps $.  $d f g ps $.  $d f w $.
    $d g z $.  $d u v w x y z $.
    cbvex4v.1 $e |- ( ( x = v /\ y = u ) -> ( ph <-> ps ) ) $.
    cbvex4v.2 $e |- ( ( z = f /\ w = g ) -> ( ps <-> ch ) ) $.
    $( Rule used to change bound variables, using implicit substitution.
       (Contributed by NM, 26-Jul-1995.) $)
    cbvex4v $p |- ( E. x E. y E. z E. w ph <-> E. v E. u E. f E. g ch ) $=
      wph vw wex vz wex vy wex vx wex wps vw wex vz wex vu wex vv wex wch
      cbvex4v.vg wex cbvex4v.vf wex vu wex vv wex wph vw wex vz wex wps vw wex
      vz wex vx vy vv vu vx vv weq vy vu weq wa wph wps vz vw cbvex4v.1 2exbidv
      cbvex2v wps vw wex vz wex wch cbvex4v.vg wex cbvex4v.vf wex vv vu wps wch
      vz vw cbvex4v.vf cbvex4v.vg cbvex4v.2 cbvex2v 2exbii bitri $.
  $}

  ${
    $d x ps $.
    chv.1 $e |- ( x = y -> ( ph <-> ps ) ) $.
    chv.2 $e |- ph $.
    $( Implicit substitution of ` y ` for ` x ` into a theorem.  (Contributed
       by NM, 20-Apr-1994.) $)
    chvarv $p |- ps $=
      wph wps vx wph wps vx vy chv.1 spv chv.2 mpg $.
  $}


  ${
    $d x z $.  $d y z $.
    $( When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  Note:  This proof is referenced on the Metamath
       Proof Explorer Home Page and shouldn't be changed.  (Contributed by NM,
       28-Jan-2004.)  (Proof modification is discouraged.) $)
    cleljust $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      vz vx weq vz vy wel wa vz wex vx vy wel vz vy wel vx vy wel vz vx vx vy
      wel vz ax-17 vz vx vy elequ1 equsexh bicomi $.
  $}

  ${
    $d x z $.  $d y z $.
    $( When the class variables in definition ~ df-clel are replaced with set
       variables, this theorem of predicate calculus is the result.  This
       theorem provides part of the justification for the consistency of that
       definition, which "overloads" the set variables in ~ wel with the class
       variables in ~ wcel .  (Contributed by NM, 28-Jan-2004.)  (Revised by
       Mario Carneiro, 21-Dec-2016.) $)
    cleljustALT $p |- ( x e. y <-> E. z ( z = x /\ z e. y ) ) $=
      vz vx weq vz vy wel wa vz wex vx vy wel vz vy wel vx vy wel vz vx vx vy
      wel vz nfv vz vx vy elequ1 equsex bicomi $.
  $}

  ${
    $d z ps $.
    dvelim.1 $e |- ( ph -> A. x ph ) $.
    dvelim.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( This theorem can be used to eliminate a distinct variable restriction on
       ` x ` and ` z ` and replace it with the "distinctor" ` -. A. x x = y `
       as an antecedent. ` ph ` normally has ` z ` free and can be read
       ` ph ( z ) ` , and ` ps ` substitutes ` y ` for ` z ` and can be read
       ` ph ( y ) ` .  We don't require that ` x ` and ` y ` be distinct: if
       they aren't, the distinctor will become false (in multiple-element
       domains of discourse) and "protect" the consequent.

       To obtain a closed-theorem form of this inference, prefix the hypotheses
       with ` A. x A. z ` , conjoin them, and apply ~ dvelimdf .

       Other variants of this theorem are ~ dvelimh (with no distinct variable
       restrictions), ~ dvelimhw (that avoids ~ ax-12 ), and ~ dvelimALT (that
       avoids ~ ax-10 ).  (Contributed by NM, 23-Nov-1994.) $)
    dvelim $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      wph wps vx vy vz dvelim.1 wps vz ax-17 dvelim.2 dvelimh $.
  $}

  ${
    $d z ps $.
    dvelimnf.1 $e |- F/ x ph $.
    dvelimnf.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim using "not free" notation.  (Contributed by Mario
       Carneiro, 9-Oct-2016.) $)
    dvelimnf $p |- ( -. A. x x = y -> F/ x ps ) $=
      wph wps vx vy vz dvelimnf.1 wps vz nfv dvelimnf.2 dvelimf $.
  $}

  ${
    $d w z x $.  $d w y $.
    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveeq1 $p |- ( -. A. x x = y -> ( y = z -> A. x y = z ) ) $=
      vw vz weq vy vz weq vx vy vw vw vy vz equequ1 dvelimv $.

    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel1 $p |- ( -. A. x x = y -> ( y e. z -> A. x y e. z ) ) $=
      vw vz wel vy vz wel vx vy vw vw vy vz elequ1 dvelimv $.

    $( Quantifier introduction when one pair of variables is distinct.
       (Contributed by NM, 2-Jan-2002.) $)
    dveel2 $p |- ( -. A. x x = y -> ( z e. y -> A. x z e. y ) ) $=
      vz vw wel vz vy wel vx vy vw vw vy vz elequ2 dvelimv $.
  $}

  ${
    $d w y $.  $d w z $.  $d w x $.  $( ` w ` is dummy. $)
    $( Axiom ~ ax-15 is redundant if we assume ~ ax-17 .  Remark 9.6 in
       [Megill] p. 448 (p. 16 of the preprint), regarding axiom scheme C14'.

       Note that ` w ` is a dummy variable introduced in the proof.  On the web
       page, it is implicitly assumed to be distinct from all other variables.
       (This is made explicit in the database file set.mm).  Its purpose is to
       satisfy the distinct variable requirements of ~ dveel2 and ~ ax-17 .  By
       the end of the proof it has vanished, and the final theorem has no
       distinct variable requirements.  (Contributed by NM, 29-Jun-1995.)
       (Proof modification is discouraged.) $)
    ax15 $p |- ( -. A. z z = x -> ( -. A. z z = y ->
              ( x e. y -> A. z x e. y ) ) ) $=
      vz vx weq vz wal wn vz vy weq vz wal wn vx vy wel vx vy wel vz wal vz vx
      weq vz wal wn vz vy weq vz wal wn vx vy wel wi vz vy weq vz wal wn vx vy
      wel wi vz wal vz vy weq vz wal wn vx vy wel vz wal wi vz vy weq vz wal wn
      vw vy wel wi vz vy weq vz wal wn vx vy wel wi vz vx vw vz vy weq vz wal
      wn vw vy wel vz vz vy weq vz hbn1 vz vy vw dveel2 hbim1 vw vx weq vw vy
      wel vx vy wel vz vy weq vz wal wn vw vx vy elequ1 imbi2d dvelim vz vy weq
      vz wal wn vx vy wel vz vz vy weq vz wal vz vz vy weq vz nfa1 nfn 19.21
      syl6ib pm2.86d $.
  $}

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 5-Aug-1993.) $)
  drsb1 $p |- ( A. x x = y -> ( [ z / x ] ph <-> [ z / y ] ph ) ) $=
    vx vy weq vx wal vx vz weq wph wi vx vz weq wph wa vx wex wa vy vz weq wph
    wi vy vz weq wph wa vy wex wa wph vx vz wsb wph vy vz wsb vx vy weq vx wal
    vx vz weq wph wi vy vz weq wph wi vx vz weq wph wa vx wex vy vz weq wph wa
    vy wex vx vy weq vx wal vx vz weq vy vz weq wph vx vy weq vx vz weq vy vz
    weq wb vx vx vy vz equequ1 sps imbi1d vx vz weq wph wa vy vz weq wph wa vx
    vy vx vy weq vx wal vx vz weq vy vz weq wph vx vy weq vx vz weq vy vz weq
    wb vx vx vy vz equequ1 sps anbi1d drex1 anbi12d wph vx vz df-sb wph vy vz
    df-sb 3bitr4g $.

  $( One direction of a simplified definition of substitution.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb2 $p |- ( A. x ( x = y -> ph ) -> [ y / x ] ph ) $=
    vx vy weq wph wi vx wal vx vy weq wph wi vx vy weq wph wa vx wex wph vx vy
    wsb vx vy weq wph wi vx sp wph vx vy equs4 wph vx vy df-sb sylanbrc $.

  $( The specialization axiom of standard predicate calculus.  It states that
     if a statement ` ph ` holds for all ` x ` , then it also holds for the
     specific case of ` y ` (properly) substituted for ` x ` .  Translated to
     traditional notation, it can be read:  " ` A. x ph ( x ) -> ph ( y ) ` ,
     provided that ` y ` is free for ` x ` in ` ph ( x ) ` ."  Axiom 4 of
     [Mendelson] p. 69.  See also ~ spsbc and ~ rspsbc .  (Contributed by NM,
     5-Aug-1993.) $)
  stdpc4 $p |- ( A. x ph -> [ y / x ] ph ) $=
    wph vx wal vx vy weq wph wi vx wal wph vx vy wsb wph vx vy weq wph wi vx
    wph vx vy weq ax-1 alimi wph vx vy sb2 syl $.

  $( Substitution has no effect on a non-free variable.  (Contributed by NM,
     30-May-2009.)  (Revised by Mario Carneiro, 12-Oct-2016.) $)
  sbft $p |- ( F/ x ph -> ( [ y / x ] ph <-> ph ) ) $=
    wph vx wnf wph vx vy wsb wph wph vx vy wsb vx vy weq wph wa vx wex wph vx
    wnf wph wph vx vy sb1 wph vx wnf vx vy weq wph wa wph wi vx wal vx vy weq
    wph wa vx wex wph wi vx vy weq wph wa wph wi vx vx vy weq wph simpr ax-gen
    vx vy weq wph wa wph vx 19.23t mpbii syl5 wph vx wnf wph wph vx wal wph vx
    vy wsb wph vx nfr wph vx vy stdpc4 syl6 impbid $.

  ${
    sbf.1 $e |- F/ x ph $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sbf $p |- ( [ y / x ] ph <-> ph ) $=
      wph vx wnf wph vx vy wsb wph wb sbf.1 wph vx vy sbft ax-mp $.
  $}

  ${
    sbh.1 $e |- ( ph -> A. x ph ) $.
    $( Substitution for a variable not free in a wff does not affect it.
       (Contributed by NM, 5-Aug-1993.) $)
    sbh $p |- ( [ y / x ] ph <-> ph ) $=
      wph vx vy wph vx sbh.1 nfi sbf $.
  $}

  $( Substitution has no effect on a bound variable.  (Contributed by NM,
     1-Jul-2005.) $)
  sbf2 $p |- ( [ y / x ] A. x ph <-> A. x ph ) $=
    wph vx wal vx vy wph vx nfa1 sbf $.

  ${
    sb6x.1 $e |- F/ x ph $.
    $( Equivalence involving substitution for a variable not free.
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb6x $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      wph vx vy wsb wph vx vy weq wph wi vx wal wph vx vy sb6x.1 sbf wph wph vx
      vy sb6x.1 vx vy weq wph biidd equsal bitr4i $.
  $}

  ${
    nfs1f.1 $e |- F/ x ph $.
    $( If ` x ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` .
       (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1f $p |- F/ x [ y / x ] ph $=
      wph vx vy wsb wph vx wph vx vy nfs1f.1 sbf nfs1f.1 nfxfr $.
  $}

  $( Substitution does not change an identical variable specifier.
     (Contributed by NM, 5-Aug-1993.) $)
  sbequ5 $p |- ( [ w / z ] A. x x = y <-> A. x x = y ) $=
    vx vy weq vx wal vz vw vx vy vz nfae sbf $.

  $( Substitution does not change a distinctor.  (Contributed by NM,
     5-Aug-1993.) $)
  sbequ6 $p |- ( [ w / z ] -. A. x x = y <-> -. A. x x = y ) $=
    vx vy weq vx wal wn vz vw vx vy vz nfnae sbf $.

  ${
    sbt.1 $e |- ph $.
    $( A substitution into a theorem remains true.  (See ~ chvar and ~ chvarv
       for versions using implicit substitution.)  (Contributed by NM,
       21-Jan-2004.)  (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    sbt $p |- [ y / x ] ph $=
      wph vx vy wsb wph sbt.1 wph vx vy wph vx sbt.1 nfth sbf mpbir $.
  $}

  $( Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)
  equsb1 $p |- [ y / x ] x = y $=
    vx vy weq vx vy weq wi vx vy weq vx vy wsb vx vx vy weq vx vy sb2 vx vy weq
    id mpg $.

  $( Substitution applied to an atomic wff.  (Contributed by NM,
     5-Aug-1993.) $)
  equsb2 $p |- [ y / x ] y = x $=
    vx vy weq vy vx weq wi vy vx weq vx vy wsb vx vy vx weq vx vy sb2 vx vy
    equcomi mpg $.

  ${
    sbied.1 $e |- F/ x ph $.
    sbied.2 $e |- ( ph -> F/ x ch ) $.
    sbied.3 $e |- ( ph -> ( x = y -> ( ps <-> ch ) ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 30-Jun-1994.)  (Revised by
       Mario Carneiro, 4-Oct-2016.) $)
    sbied $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      wph wps vx vy wsb wch wph wps vx vy wsb wch vx wex wch wps vx vy wsb vx
      vy weq wps wa vx wex wph wch vx wex wps vx vy sb1 wph vx vy weq wps wa
      wch vx sbied.1 wph vx vy weq wps wch wph vx vy weq wps wch wb wps wch wi
      sbied.3 wps wch bi1 syl6 imp3a eximd syl5 wch wph vx sbied.2 19.9d syld
      wph wch wch vx wal wps vx vy wsb wph wch vx sbied.2 nfrd wph wch vx wal
      vx vy weq wps wi vx wal wps vx vy wsb wph wch vx vy weq wps wi vx sbied.1
      wph vx vy weq wch wps wph vx vy weq wps wch wb wch wps wi sbied.3 wps wch
      bi2 syl6 com23 alimd wps vx vy sb2 syl6 syld impbid $.
  $}

  ${
    $d x ph $.  $d x ch $.
    sbiedv.1 $e |- ( ( ph /\ x = y ) -> ( ps <-> ch ) ) $.
    $( Conversion of implicit substitution to explicit substitution (deduction
       version of ~ sbie ).  (Contributed by NM, 7-Jan-2017.) $)
    sbiedv $p |- ( ph -> ( [ y / x ] ps <-> ch ) ) $=
      wph wps wch vx vy wph vx nfv wph wch vx nfvd wph vx vy weq wps wch wb
      sbiedv.1 ex sbied $.
  $}

  ${
    sbie.1 $e |- F/ x ps $.
    sbie.2 $e |- ( x = y -> ( ph <-> ps ) ) $.
    $( Conversion of implicit substitution to explicit substitution.
       (Contributed by NM, 30-Jun-1994.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sbie $p |- ( [ y / x ] ph <-> ps ) $=
      wph vx vy wsb wps wb wtru wph wps vx vy vx nftru wps vx wnf wtru sbie.1
      a1i vx vy weq wph wps wb wi wtru sbie.2 a1i sbied trud $.
  $}

  ${
    sb6f.1 $e |- F/ y ph $.
    $( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb6f $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      wph vx vy wsb vx vy weq wph wi vx wal wph vx vy wsb wph vy wal vx vy wsb
      vx vy weq wph wi vx wal wph wph vy wal vx vy wph vy sb6f.1 nfri sbimi wph
      vx vy sb4a syl wph vx vy sb2 impbii $.

    $( Equivalence for substitution when ` y ` is not free in ` ph ` .
       (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    sb5f $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      wph vx vy wsb vx vy weq wph wi vx wal vx vy weq wph wa vx wex wph vx vy
      sb6f.1 sb6f wph vx vy sb6f.1 equs45f bitr4i $.
  $}

  $( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
  hbsb2a $p |- ( [ y / x ] A. y ph -> A. x [ y / x ] ph ) $=
    wph vy wal vx vy wsb vx vy weq wph wi vx wal wph vx vy wsb vx wal wph vx vy
    sb4a vx vy weq wph wi wph vx vy wsb vx wph vx vy sb2 a5i syl $.

  $( Special case of a bound-variable hypothesis builder for substitution.
     (Contributed by NM, 2-Feb-2007.) $)
  hbsb2e $p |- ( [ y / x ] ph -> A. x [ y / x ] E. y ph ) $=
    wph vx vy wsb vx vy weq wph vy wex wi vx wal wph vy wex vx vy wsb vx wal
    wph vx vy sb4e vx vy weq wph vy wex wi wph vy wex vx vy wsb vx wph vy wex
    vx vy sb2 a5i syl $.

  ${
    hbsb3.1 $e |- ( ph -> A. y ph ) $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by NM, 5-Aug-1993.) $)
    hbsb3 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      wph vx vy wsb wph vy wal vx vy wsb wph vx vy wsb vx wal wph wph vy wal vx
      vy hbsb3.1 sbimi wph vx vy hbsb2a syl $.
  $}

  ${
    nfs1.1 $e |- F/ y ph $.
    $( If ` y ` is not free in ` ph ` , ` x ` is not free in
       ` [ y / x ] ph ` .  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1 $p |- F/ x [ y / x ] ph $=
      wph vx vy wsb vx wph vx vy wph vy nfs1.1 nfri hbsb3 nfi $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Proof of older axiom ~ ax-16 .  (Contributed by NM, 8-Nov-2006.)
       (Revised by NM, 22-Sep-2017.) $)
    ax16 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      wph vx vy vx a16g $.
  $}

  ${
    $d x y z $.  $d z ph $.
    ax16i.1 $e |- ( x = z -> ( ph <-> ps ) ) $.
    ax16i.2 $e |- ( ps -> A. x ps ) $.
    $( Inference with ~ ax16 as its conclusion.  (Contributed by NM,
       20-May-2008.)  (Proof modification is discouraged.) $)
    ax16i $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      vx vy weq vx wal vz vy weq vz wal vx vz weq vz wal wph wph vx wal wi vx
      vy weq vz vy weq vx vz vx vy weq vz nfv vz vy weq vx nfv vx vz vy ax-8
      cbv3 vz vy weq vz wal vz vx weq vz wal vx vz weq vz wal vx vy weq vz vy
      weq vz wal vz vx weq vz wal vz vy weq vx vy weq vz vx vz vx vy ax-8 spimv
      vx vy weq vz vy weq vz vx weq vz vx vy weq vy vx weq vz vy weq vz vx weq
      vx vy equcomi vz vy weq vy vz weq vy vx weq vz vx weq wi vz vy equcomi vy
      vz vx ax-8 syl syl5com alimdv mpcom vz vx weq vx vz weq vz vz vx equcomi
      alimi syl wph vx vz weq vz wal wps vz wal wph vx wal wph vx vz weq wps vz
      vx vz weq wph wps ax16i.1 biimpcd alimdv wps wph vz vx wps vx ax16i.2 nfi
      wph vz nfv vz vx weq vx vz weq wps wph wi vz vx equcomi vx vz weq wph wps
      ax16i.1 biimprd syl cbv3 syl6com 3syl $.
  $}

  ${
    $d x y z $.  $d z ph $.
    $( Alternate proof of ~ ax16 .  (Contributed by NM, 17-May-2008.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax16ALT $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      wph wph vx vz wsb vx vy vz wph vx vz sbequ12 wph vx vz wph vz ax-17 hbsb3
      ax16i $.
  $}

  ${
    $d x y $.  $d z ph $.
    $( Alternate proof of ~ ax16 .  (Contributed by NM, 8-Nov-2006.)
       (Proof modification is discouraged.)  (New usage is discouraged.) $)
    ax16ALT2 $p |- ( A. x x = y -> ( ph -> A. x ph ) ) $=
      vx vy weq vx wal vx vz weq vz wal wph wph vx wal wi vx vy vz vx vz aev
      wph vx vz weq vz wal wph vx vz wsb vz wal wph vx wal wph vx vz weq wph vx
      vz wsb vz vx vz weq wph wph vx vz wsb wph vx vz sbequ12 biimpcd alimdv
      wph vx vz wsb wph vz vx wph vx vz wph vz nfv nfs1 wph vz nfv wph vz vx
      stdpc7 cbv3 syl6com syl $.
  $}

  ${
    $d x y $.
    $( A generalization of axiom ~ ax-16 .  Alternate proof of ~ a16g that uses
       ~ df-sb .  (Contributed by NM, 5-Aug-1993.)  (Proof shortened by Andrew
       Salmon, 25-May-2011.)  (Proof modification is discouraged.)
       (New usage is discouraged.) $)
    a16gALT $p |- ( A. x x = y -> ( ph -> A. z ph ) ) $=
      vx vy weq vx wal vz vx weq vz wal wph wph vx wal wph vz wal vx vy vz vz
      vx aev wph vx vy ax16ALT2 vz vx weq vz wal wph vz wal wph vx wal wph wph
      vz vx vz vx weq vz wal wph biidd dral1 biimprd sylsyld $.

    $( A generalization of axiom ~ ax-16 .  (Contributed by NM, 5-Aug-1993.) $)
    a16gb $p |- ( A. x x = y -> ( ph <-> A. z ph ) ) $=
      vx vy weq vx wal wph wph vz wal wph vx vy vz a16g wph vz sp impbid1 $.

    $( If ~ dtru is false, then there is only one element in the universe, so
       everything satisfies ` F/ ` .  (Contributed by Mario Carneiro,
       7-Oct-2016.) $)
    a16nf $p |- ( A. x x = y -> F/ z ph ) $=
      vx vy weq vx wal wph vz vx vy vz nfae wph vx vy vz a16g nfd $.
  $}

  $( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
  sb3 $p |- ( -. A. x x = y -> ( E. x ( x = y /\ ph ) -> [ y / x ] ph ) ) $=
    vx vy weq vx wal wn vx vy weq wph wa vx wex vx vy weq wph wi vx wal wph vx
    vy wsb wph vx vy equs5 wph vx vy sb2 syl6 $.

  $( One direction of a simplified definition of substitution when variables
     are distinct.  (Contributed by NM, 5-Aug-1993.) $)
  sb4 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x ( x = y -> ph ) ) ) $=
    wph vx vy wsb vx vy weq wph wa vx wex vx vy weq vx wal wn vx vy weq wph wi
    vx wal wph vx vy sb1 wph vx vy equs5 syl5 $.

  $( Simplified definition of substitution when variables are distinct.
     (Contributed by NM, 27-May-1997.) $)
  sb4b $p |- ( -. A. x x = y -> ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) ) $=
    vx vy weq vx wal wn wph vx vy wsb vx vy weq wph wi vx wal wph vx vy sb4 wph
    vx vy sb2 impbid1 $.

  $( An alternate definition of proper substitution that, like ~ df-sb , mixes
     free and bound variables to avoid distinct variable requirements.
     (Contributed by NM, 17-Feb-2005.) $)
  dfsb2 $p |- ( [ y / x ] ph <->
              ( ( x = y /\ ph ) \/ A. x ( x = y -> ph ) ) ) $=
    wph vx vy wsb vx vy weq wph wa vx vy weq wph wi vx wal wo vx vy weq vx wal
    wph vx vy wsb vx vy weq wph wa vx vy weq wph wi vx wal wo wi vx vy weq vx
    wal vx vy weq wph vx vy wsb wph vx vy weq wph wa vx vy weq wph wi vx wal wo
    vx vy weq vx sp vx vy weq wph vx vy wsb wph wi vx wph vx vy sbequ2 sps vx
    vy weq wph wa vx vy weq wph wi vx wal orc ee12an vx vy weq vx wal wn wph vx
    vy wsb vx vy weq wph wi vx wal vx vy weq wph wa vx vy weq wph wi vx wal wo
    wph vx vy sb4 vx vy weq wph wi vx wal vx vy weq wph wa olc syl6 pm2.61i vx
    vy weq wph wa wph vx vy wsb vx vy weq wph wi vx wal vx vy weq wph wph vx vy
    wsb wph vx vy sbequ1 imp wph vx vy sb2 jaoi impbii $.

  $( An alternate definition of proper substitution ~ df-sb that uses only
     primitive connectives (no defined terms) on the right-hand side.
     (Contributed by NM, 6-Mar-2007.) $)
  dfsb3 $p |- ( [ y / x ] ph <->
              ( ( x = y -> -. ph ) -> A. x ( x = y -> ph ) ) ) $=
    vx vy weq wph wa vx vy weq wph wi vx wal wo vx vy weq wph wa wn vx vy weq
    wph wi vx wal wi wph vx vy wsb vx vy weq wph wn wi vx vy weq wph wi vx wal
    wi vx vy weq wph wa vx vy weq wph wi vx wal df-or wph vx vy dfsb2 vx vy weq
    wph wn wi vx vy weq wph wa wn vx vy weq wph wi vx wal vx vy weq wph imnan
    imbi1i 3bitr4i $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  hbsb2 $p |- ( -. A. x x = y -> ( [ y / x ] ph -> A. x [ y / x ] ph ) ) $=
    vx vy weq vx wal wn wph vx vy wsb vx vy weq wph wi vx wal wph vx vy wsb vx
    wal wph vx vy sb4 vx vy weq wph wi wph vx vy wsb vx wph vx vy sb2 a5i syl6
    $.

  $( Bound-variable hypothesis builder for substitution.  (Contributed by Mario
     Carneiro, 4-Oct-2016.) $)
  nfsb2 $p |- ( -. A. x x = y -> F/ x [ y / x ] ph ) $=
    vx vy weq vx wal wn wph vx vy wsb vx vx vy vx nfnae wph vx vy hbsb2 nfd $.

  $( An equality theorem for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbequi $p |- ( x = y -> ( [ x / z ] ph -> [ y / z ] ph ) ) $=
    vz vx weq vz wal vz vy weq vz wal vx vy weq wph vz vx wsb wph vz vy wsb wi
    wi vz vx weq vz wal wn vx vy weq vz vy weq vz wal wn wph vz vx wsb wph vz
    vy wsb wi vz vx weq vz wal wn vx vy weq vz vy weq vz wal wn wph vz vx wsb
    wph vz vy wsb wi wi vz vx weq vz wal wn vx vy weq wa wph vz vx wsb wph vz
    vy wsb vz wex vz vy weq vz wal wn wph vz vy wsb vz vx weq vz wal wn wph vz
    vx wsb wph vz vx wsb vz wal vx vy weq wph vz vy wsb vz wex wph vz vx hbsb2
    vx vy weq wph vz vx wsb wph vz vy wsb wi vz wex wph vz vx wsb vz wal wph vz
    vy wsb vz wex wi vx vy weq vx vz weq vz vy weq wa vz wex wph vz vx wsb wph
    vz vy wsb wi vz wex vx vy vz equvini vx vz weq vz vy weq wa wph vz vx wsb
    wph vz vy wsb wi vz vx vz weq wph vz vx wsb wph vz vy weq wph vz vy wsb wph
    vx vz stdpc7 wph vz vy sbequ1 sylan9 eximi syl wph vz vx wsb wph vz vy wsb
    vz 19.35 sylib sylan9 wph vz vy wsb vz vy weq vz wal wn vz wph vz vy nfsb2
    19.9d syl9 ex com23 vz vx weq vz wal vx vy weq wph vz vx wsb wph vz vy wsb
    wi vz vx weq vz wal vx vy weq wa wph vz vx wsb wph wph vz vy wsb vz vx weq
    vz wal wph vz vx wsb wph wi vx vy weq vz vx weq wph vz vx wsb wph wi vz wph
    vz vx sbequ2 sps adantr vx vy weq wph wph vx vy wsb vz vx weq vz wal wph vz
    vy wsb wph vx vy sbequ1 vz vx weq vz wal wph vz vy wsb wph vx vy wsb wph vz
    vx vy drsb1 biimprd sylan9r syld ex vz vy weq vz wal vx vy weq wph vz vx
    wsb wph vz vy wsb wi vz vy weq vz wal vx vy weq wa wph vz vx wsb wph wph vz
    vy wsb vz vy weq vz wal wph vz vx wsb wph vy vx wsb vx vy weq wph vz vy weq
    vz wal wph vz vx wsb wph vy vx wsb wph vz vy vx drsb1 biimpd wph vx vy
    stdpc7 sylan9 vz vy weq vz wal wph wph vz vy wsb wi vx vy weq vz vy weq wph
    wph vz vy wsb wi vz wph vz vy sbequ1 sps adantr syld ex pm2.61ii $.

  $( An equality theorem for substitution.  Used in proof of Theorem 9.7 in
     [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
     5-Aug-1993.) $)
  sbequ $p |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    vx vy weq wph vz vx wsb wph vz vy wsb wph vx vy vz sbequi wph vz vy wsb wph
    vz vx wsb wi vy vx wph vy vx vz sbequi equcoms impbid $.

  $( Formula-building lemma for use with the Distinctor Reduction Theorem.
     Part of Theorem 9.4 of [Megill] p. 448 (p. 16 of preprint).  (Contributed
     by NM, 27-Feb-2005.) $)
  drsb2 $p |- ( A. x x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) ) $=
    vx vy weq wph vz vx wsb wph vz vy wsb wb vx wph vx vy vz sbequ sps $.

  $( Negation inside and outside of substitution are equivalent.  (Contributed
     by NM, 5-Aug-1993.) $)
  sbn $p |- ( [ y / x ] -. ph <-> -. [ y / x ] ph ) $=
    wph wn vx vy wsb wph vx vy wsb wn vx vy weq vx wal wph wn vx vy wsb wph vx
    vy wsb wn wi vx vy weq wph wn vx vy wsb wph vx vy wsb wn wi vx vx vy weq
    wph wn vx vy wsb wph wph vx vy wsb wph wn vx vy sbequ2 wph vx vy sbequ2
    nsyld sps vx vy weq vx wal wn wph wn vx vy wsb vx vy weq wph wn wi vx wal
    wph vx vy wsb wn wph wn vx vy sb4 wph vx vy wsb vx vy weq wph wn wi vx wal
    wph vx vy wsb vx vy weq wph wa vx wex vx vy weq wph wn wi vx wal wn wph vx
    vy sb1 wph vx vy equs3 sylib con2i syl6 pm2.61i wph vx vy wsb wn vx vy weq
    wph wn wi vx vy weq wph wn wa vx wex wph wn vx vy wsb vx vy weq wph wph vx
    vy wsb wph vx vy sbequ1 con3rr3 wph vx vy wsb wn vx vy weq wph wn wn wi vx
    wal wn vx vy weq wph wn wa vx wex vx vy weq wph wn wn wi vx wal wph vx vy
    wsb vx vy weq wph wn wn wi vx wal wph wn wn vx vy wsb wph vx vy wsb wph wn
    wn vx vy sb2 wph wph wn wn vx vy wph notnot sbbii sylibr con3i wph wn vx vy
    equs3 sylibr wph wn vx vy df-sb sylanbrc impbii $.

  $( Removal of implication from substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  sbi1 $p |- ( [ y / x ] ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    vx vy weq vx wal wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wi vx
    vy weq wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wi vx vx vy weq
    wph wps wi vx vy wsb wph vx vy wsb wps wps vx vy wsb vx vy weq wph vx vy
    wsb wph wph wps wi vx vy wsb wps wph vx vy sbequ2 wph wps wi vx vy sbequ2
    syl5d wps vx vy sbequ1 syl6d sps vx vy weq vx wal wn wph vx vy wsb vx vy
    weq wph wi vx wal wph wps wi vx vy wsb wps vx vy wsb wph vx vy sb4 vx vy
    weq vx wal wn wph wps wi vx vy wsb vx vy weq wph wps wi wi vx wal vx vy weq
    wph wi vx wal wps vx vy wsb wi wph wps wi vx vy sb4 vx vy weq wph wps wi wi
    vx wal vx vy weq wph wi vx wal vx vy weq wps wi vx wal wps vx vy wsb vx vy
    weq wph wps wi wi vx vy weq wph wi vx vy weq wps wi vx vx vy weq wph wps
    ax-2 al2imi wps vx vy sb2 syl6 syl6 syl5d pm2.61i $.

  $( Introduction of implication into substitution.  (Contributed by NM,
     5-Aug-1993.) $)
  sbi2 $p |- ( ( [ y / x ] ph -> [ y / x ] ps ) -> [ y / x ] ( ph -> ps ) ) $=
    wph vx vy wsb wps vx vy wsb wph wps wi vx vy wsb wph vx vy wsb wn wph wn vx
    vy wsb wph wps wi vx vy wsb wph vx vy sbn wph wn wph wps wi vx vy wph wps
    pm2.21 sbimi sylbir wps wph wps wi vx vy wps wph ax-1 sbimi ja $.

  $( Implication inside and outside of substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
  sbim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wph wps vx vy sbi1 wph
    wps vx vy sbi2 impbii $.

  $( Logical OR inside and outside of substitution are equivalent.
     (Contributed by NM, 29-Sep-2002.) $)
  sbor $p |- ( [ y / x ] ( ph \/ ps ) <-> ( [ y / x ] ph \/ [ y / x ] ps ) ) $=
    wph wn wps wi vx vy wsb wph vx vy wsb wn wps vx vy wsb wi wph wps wo vx vy
    wsb wph vx vy wsb wps vx vy wsb wo wph wn wps wi vx vy wsb wph wn vx vy wsb
    wps vx vy wsb wi wph vx vy wsb wn wps vx vy wsb wi wph wn wps vx vy sbim
    wph wn vx vy wsb wph vx vy wsb wn wps vx vy wsb wph vx vy sbn imbi1i bitri
    wph wps wo wph wn wps wi vx vy wph wps df-or sbbii wph vx vy wsb wps vx vy
    wsb df-or 3bitr4i $.

  ${
    sbrim.1 $e |- F/ x ph $.
    $( Substitution with a variable not free in antecedent affects only the
       consequent.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sbrim $p |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) $=
      wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wph wps vx vy wsb wi
      wph wps vx vy sbim wph vx vy wsb wph wps vx vy wsb wph vx vy sbrim.1 sbf
      imbi1i bitri $.
  $}

  ${
    sblim.1 $e |- F/ x ps $.
    $( Substitution with a variable not free in consequent affects only the
       antecedent.  (Contributed by NM, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 4-Oct-2016.) $)
    sblim $p |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) $=
      wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wph vx vy wsb wps wi
      wph wps vx vy sbim wps vx vy wsb wps wph vx vy wsb wps vx vy sblim.1 sbf
      imbi2i bitri $.
  $}

  $( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
  sban $p |- ( [ y / x ] ( ph /\ ps ) <-> ( [ y / x ] ph /\ [ y / x ] ps ) ) $=
    wph wps wn wi wn vx vy wsb wph vx vy wsb wps vx vy wsb wn wi wn wph wps wa
    vx vy wsb wph vx vy wsb wps vx vy wsb wa wph wps wn wi wn vx vy wsb wph wps
    wn wi vx vy wsb wph vx vy wsb wps vx vy wsb wn wi wph wps wn wi vx vy sbn
    wph wps wn wi vx vy wsb wph vx vy wsb wps wn vx vy wsb wi wph vx vy wsb wps
    vx vy wsb wn wi wph wps wn vx vy sbim wps wn vx vy wsb wps vx vy wsb wn wph
    vx vy wsb wps vx vy sbn imbi2i bitri xchbinx wph wps wa wph wps wn wi wn vx
    vy wph wps df-an sbbii wph vx vy wsb wps vx vy wsb df-an 3bitr4i $.

  $( Conjunction inside and outside of a substitution are equivalent.
     (Contributed by NM, 14-Dec-2006.) $)
  sb3an $p |- ( [ y / x ] ( ph /\ ps /\ ch ) <->
              ( [ y / x ] ph /\ [ y / x ] ps /\ [ y / x ] ch ) ) $=
    wph wps wch w3a vx vy wsb wph wps wa wch wa vx vy wsb wph wps wa vx vy wsb
    wch vx vy wsb wa wph vx vy wsb wps vx vy wsb wch vx vy wsb w3a wph wps wch
    w3a wph wps wa wch wa vx vy wph wps wch df-3an sbbii wph wps wa wch vx vy
    sban wph wps wa vx vy wsb wch vx vy wsb wa wph vx vy wsb wps vx vy wsb wa
    wch vx vy wsb wa wph vx vy wsb wps vx vy wsb wch vx vy wsb w3a wph wps wa
    vx vy wsb wph vx vy wsb wps vx vy wsb wa wch vx vy wsb wph wps vx vy sban
    anbi1i wph vx vy wsb wps vx vy wsb wch vx vy wsb df-3an bitr4i 3bitri $.

  $( Equivalence inside and outside of a substitution are equivalent.
     (Contributed by NM, 5-Aug-1993.) $)
  sbbi $p |- ( [ y / x ] ( ph <-> ps )
     <-> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    wph wps wb vx vy wsb wph wps wi wps wph wi wa vx vy wsb wph vx vy wsb wps
    vx vy wsb wb wph wps wb wph wps wi wps wph wi wa vx vy wph wps dfbi2 sbbii
    wph wps wi vx vy wsb wps wph wi vx vy wsb wa wph vx vy wsb wps vx vy wsb wi
    wps vx vy wsb wph vx vy wsb wi wa wph wps wi wps wph wi wa vx vy wsb wph vx
    vy wsb wps vx vy wsb wb wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi
    wps wph wi vx vy wsb wps vx vy wsb wph vx vy wsb wi wph wps vx vy sbim wps
    wph vx vy sbim anbi12i wph wps wi wps wph wi vx vy sban wph vx vy wsb wps
    vx vy wsb dfbi2 3bitr4i bitri $.

  ${
    sblbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce left biconditional inside of a substitution.  (Contributed by
       NM, 19-Aug-1993.) $)
    sblbis $p |- ( [ y / x ] ( ch <-> ph ) <-> ( [ y / x ] ch <-> ps ) ) $=
      wch wph wb vx vy wsb wch vx vy wsb wph vx vy wsb wb wch vx vy wsb wps wb
      wch wph vx vy sbbi wph vx vy wsb wps wch vx vy wsb sblbis.1 bibi2i bitri
      $.
  $}

  ${
    sbrbis.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.) $)
    sbrbis $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> [ y / x ] ch ) ) $=
      wph wch wb vx vy wsb wph vx vy wsb wch vx vy wsb wb wps wch vx vy wsb wb
      wph wch vx vy sbbi wph vx vy wsb wps wch vx vy wsb sbrbis.1 bibi1i bitri
      $.
  $}

  ${
    sbrbif.1 $e |- F/ x ch $.
    sbrbif.2 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Introduce right biconditional inside of a substitution.  (Contributed by
       NM, 18-Aug-1993.)  (Revised by Mario Carneiro, 4-Oct-2016.) $)
    sbrbif $p |- ( [ y / x ] ( ph <-> ch ) <-> ( ps <-> ch ) ) $=
      wph wch wb vx vy wsb wps wch vx vy wsb wb wps wch wb wph wps wch vx vy
      sbrbif.2 sbrbis wch vx vy wsb wch wps wch vx vy sbrbif.1 sbf bibi2i bitri
      $.
  $}

  $( A specialization theorem.  (Contributed by NM, 5-Aug-1993.) $)
  spsbe $p |- ( [ y / x ] ph -> E. x ph ) $=
    wph vx vy wsb wph wn vx wal wn wph vx wex wph wn vx wal wph vx vy wsb wph
    wn vx wal wph wn vx vy wsb wph vx vy wsb wn wph wn vx vy stdpc4 wph vx vy
    sbn sylib con2i wph vx df-ex sylibr $.

  $( Specialization of implication.  (Contributed by NM, 5-Aug-1993.)  (Proof
     shortened by Andrew Salmon, 25-May-2011.) $)
  spsbim $p |- ( A. x ( ph -> ps ) -> ( [ y / x ] ph -> [ y / x ] ps ) ) $=
    wph wps wi vx wal wph wps wi vx vy wsb wph vx vy wsb wps vx vy wsb wi wph
    wps wi vx vy stdpc4 wph wps vx vy sbi1 syl $.

  $( Specialization of biconditional.  (Contributed by NM, 5-Aug-1993.) $)
  spsbbi $p |- ( A. x ( ph <-> ps ) -> ( [ y / x ] ph <-> [ y / x ] ps ) ) $=
    wph wps wb vx wal wph wps wb vx vy wsb wph vx vy wsb wps vx vy wsb wb wph
    wps wb vx vy stdpc4 wph wps vx vy sbbi sylib $.

  ${
    sbbid.1 $e |- F/ x ph $.
    sbbid.2 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Deduction substituting both sides of a biconditional.  (Contributed by
       NM, 5-Aug-1993.) $)
    sbbid $p |- ( ph -> ( [ y / x ] ps <-> [ y / x ] ch ) ) $=
      wph wps wch wb vx wal wps vx vy wsb wch vx vy wsb wb wph wps wch wb vx
      sbbid.1 sbbid.2 alrimi wps wch vx vy spsbbi syl $.
  $}

  $( Elimination of equality from antecedent after substitution.  (Contributed
     by NM, 5-Aug-1993.) $)
  sbequ8 $p |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) ) $=
    wph vx vy wsb vx vy weq vx vy wsb wph vx vy wsb wi vx vy weq wph wi vx vy
    wsb vx vy weq vx vy wsb wph vx vy wsb vx vy equsb1 a1bi vx vy weq wph vx vy
    sbim bitr4i $.

  $( A variable not free remains so after substitution with a distinct variable
     (closed form of ~ nfsb4 ).  (Contributed by NM, 7-Apr-2004.)  (Revised by
     Mario Carneiro, 4-Oct-2016.) $)
  nfsb4t $p |- ( A. x F/ z ph ->
                 ( -. A. z z = y -> F/ z [ y / x ] ph ) ) $=
    wph vz wnf vx wal vz vx weq vz wal vz vy weq vz wal wn wph vx vy wsb vz wnf
    wi wph vz wnf vx wal vz vx weq vz wal wn vz vy weq vz wal wn wph vx vy wsb
    vz wnf wph vz wnf vx wal vx vy weq vx wal vz vx weq vz wal wn vz vy weq vz
    wal wn wa wph vx vy wsb vz wnf wi wph vz wnf vx wal vx vy weq vx wal wph vx
    vy wsb vz wnf vz vx weq vz wal wn vz vy weq vz wal wn wa wph vz wnf vx vy
    weq vx wal wph vx vy wsb vz wnf wi vx vx vy weq vx wal wph vz wnf wph vx vy
    wsb vz wnf wph wph vx vy wsb vx vy vz vx vy weq wph wph vx vy wsb wb vx wph
    vx vy sbequ12 sps drnf2 biimpcd sps a1dd wph vz wnf vx wal vz vx weq vz wal
    wn vz vy weq vz wal wn wa wph vx vy wsb vz wnf wi vx vy weq vx wal wn vz vx
    weq vz wal wn vz vy weq vz wal wn wa vx vy weq wph wi vx wal vz wnf wi wph
    vz wnf vx wal vz vx weq vz wal wn vz vy weq vz wal wn wa vx vy weq wph wi
    vx wal vz wnf wph vz wnf vx wal vz vx weq vz wal wn vz vy weq vz wal wn wa
    wa vx vy weq wph wi vz vx wph vz wnf vx wal vz vx weq vz wal wn vz vy weq
    vz wal wn wa vx wph vz wnf vx nfa1 vz vx weq vz wal wn vz vy weq vz wal wn
    vx vz vx vx nfnae vz vy vx nfnae nfan nfan wph vz wnf vx wal vz vx weq vz
    wal wn vz vy weq vz wal wn wa wa vx vy weq wph vz vz vx weq vz wal wn vz vy
    weq vz wal wn wa vx vy weq vz wnf wph vz wnf vx wal vx vy vz nfeqf adantl
    wph vz wnf vx wal wph vz wnf vz vx weq vz wal wn vz vy weq vz wal wn wa wph
    vz wnf vx sp adantr nfimd nfald ex vx vy weq vx wal wn wph vx vy wsb vz wnf
    vx vy weq wph wi vx wal vz wnf vz vx weq vz wal wn vz vy weq vz wal wn wa
    vx vy weq vx wal wn wph vx vy wsb vx vy weq wph wi vx wal vz vx vy vz nfnae
    wph vx vy sb4b nfbidf imbi2d syl5ibrcom pm2.61d exp3a vz vy weq vz wal wn
    wph vz vy wsb vz wnf vz vx weq vz wal wph vx vy wsb vz wnf wph vz vy nfsb2
    wph vz vy wsb wph vx vy wsb vz vx vz wph vz vx vy drsb1 drnf2 syl5ib
    pm2.61d2 $.

  ${
    nfsb4.1 $e |- F/ z ph $.
    $( A variable not free remains so after substitution with a distinct
       variable.  (Contributed by NM, 5-Aug-1993.)  (Revised by Mario Carneiro,
       4-Oct-2016.) $)
    nfsb4 $p |- ( -. A. z z = y -> F/ z [ y / x ] ph ) $=
      wph vz wnf vz vy weq vz wal wn wph vx vy wsb vz wnf wi vx wph vx vy vz
      nfsb4t nfsb4.1 mpg $.
  $}

  ${
    dvelimdf.1 $e |- F/ x ph $.
    dvelimdf.2 $e |- F/ z ph $.
    dvelimdf.3 $e |- ( ph -> F/ x ps ) $.
    dvelimdf.4 $e |- ( ph -> F/ z ch ) $.
    dvelimdf.5 $e |- ( ph -> ( z = y -> ( ps <-> ch ) ) ) $.
    $( Deduction form of ~ dvelimf .  This version may be useful if we want to
       avoid ~ ax-17 and use ~ ax-16 instead.  (Contributed by NM,
       7-Apr-2004.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    dvelimdf $p |- ( ph -> ( -. A. x x = y -> F/ x ch ) ) $=
      wph vx vy weq vx wal wn wch vx wnf wph vx vy weq vx wal wn wa wps vz vy
      wsb vx wnf wch vx wnf wph vx vy weq vx wal wn wps vz vy wsb vx wnf wph
      wps vx wnf vz wal vx vy weq vx wal wn wps vz vy wsb vx wnf wi wph wps vx
      wnf vz dvelimdf.2 dvelimdf.3 alrimi wps vz vy vx nfsb4t syl imp wph vx vy
      weq vx wal wn wa wps vz vy wsb wch vx wph vx vy weq vx wal wn vx
      dvelimdf.1 vx vy vx nfnae nfan wph wps vz vy wsb wch wb vx vy weq vx wal
      wn wph wps wch vz vy dvelimdf.2 dvelimdf.4 dvelimdf.5 sbied adantr nfbidf
      mpbid ex $.
  $}

  $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbco $p |- ( [ y / x ] [ x / y ] ph <-> [ y / x ] ph ) $=
    wph vy vx wsb wph wb vx vy wsb wph vy vx wsb vx vy wsb wph vx vy wsb wb vy
    vx weq vx vy wsb wph vy vx wsb wph wb vx vy wsb vx vy equsb2 vy vx weq wph
    vy vx wsb wph wb vx vy vy vx weq wph wph vy vx wsb wph vy vx sbequ12 bicomd
    sbimi ax-mp wph vy vx wsb wph vx vy sbbi mpbi $.

  ${
    sbid2.1 $e |- F/ x ph $.
    $( An identity law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbid2 $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      wph vy vx wsb vx vy wsb wph vx vy wsb wph wph vx vy sbco wph vx vy
      sbid2.1 sbf bitri $.
  $}

  $( An idempotent law for substitution.  (Contributed by NM, 30-Jun-1994.)
     (Proof shortened by Andrew Salmon, 25-May-2011.) $)
  sbidm $p |- ( [ y / x ] [ y / x ] ph <-> [ y / x ] ph ) $=
    wph vx vy wsb wph wb vx vy wsb wph vx vy wsb vx vy wsb wph vx vy wsb wb vy
    vx weq vx vy wsb wph vx vy wsb wph wb vx vy wsb vx vy equsb2 vy vx weq wph
    vx vy wsb wph wb vx vy wph vy vx sbequ12r sbimi ax-mp wph vx vy wsb wph vx
    vy sbbi mpbi $.

  ${
    sbco2.1 $e |- F/ z ph $.
    $( A composition law for substitution.  (Contributed by NM, 30-Jun-1994.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbco2 $p |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph ) $=
      vx vy weq vx wal wph vx vz wsb vz vy wsb wph vx vy wsb wb vx vy weq wph
      vx vz wsb vz vy wsb wph vx vy wsb wb vx vx vy weq wph wph vx vz wsb vz vy
      wsb wph vx vy wsb wph wph vx vz wsb vz vx wsb vx vy weq wph vx vz wsb vz
      vy wsb wph vz vx sbco2.1 sbid2 wph vx vz wsb vx vy vz sbequ syl5bbr wph
      vx vy sbequ12 bitr3d sps vx vy weq vx wal wn wph vx vy wsb wph vx vz wsb
      vz vy wsb vx vy weq vx wal wn wph wph vx vz wsb vz vy wsb vx vy vx vy vx
      nfnae wph vx vz wsb vz vy vx wph vx vz sbco2.1 nfs1 nfsb4 vx vy weq wph
      wph vx vz wsb vz vy wsb wb wi vx vy weq vx wal wn wph wph vx vz wsb vz vx
      wsb vx vy weq wph vx vz wsb vz vy wsb wph vz vx sbco2.1 sbid2 wph vx vz
      wsb vx vy vz sbequ syl5bbr a1i sbied bicomd pm2.61i $.
  $}

  ${
    sbco2d.1 $e |- F/ x ph $.
    sbco2d.2 $e |- F/ z ph $.
    sbco2d.3 $e |- ( ph -> F/ z ps ) $.
    $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sbco2d $p |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) ) $=
      wph wps vx vz wsb vz vy wsb wps vx vy wsb wph wps wi vx vz wsb vz vy wsb
      wph wps wi vx vy wsb wph wps vx vz wsb vz vy wsb wi wph wps vx vy wsb wi
      wph wps wi vx vy vz wph wps vz sbco2d.2 sbco2d.3 nfim1 sbco2 wph wps wi
      vx vz wsb vz vy wsb wph wps vx vz wsb wi vz vy wsb wph wps vx vz wsb vz
      vy wsb wi wph wps wi vx vz wsb wph wps vx vz wsb wi vz vy wph wps vx vz
      sbco2d.1 sbrim sbbii wph wps vx vz wsb vz vy sbco2d.2 sbrim bitri wph wps
      vx vy sbco2d.1 sbrim 3bitr3i pm5.74ri $.
  $}

  $( A composition law for substitution.  (Contributed by NM, 5-Aug-1993.) $)
  sbco3 $p |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph ) $=
    vx vy weq vx wal wph vx vy wsb vy vz wsb wph vy vx wsb vx vz wsb wb vx vy
    weq vx wal wph vx vy wsb vx vz wsb wph vx vy wsb vy vz wsb wph vy vx wsb vx
    vz wsb wph vx vy wsb vx vy vz drsb1 vx vy weq vx wal wph vx vy wsb wph vy
    vx wsb wb vx wal wph vx vy wsb vx vz wsb wph vy vx wsb vx vz wsb wb vx vy
    weq wph vx vy wsb wph vy vx wsb wb vx wph vx vy sbequ12a alimi wph vx vy
    wsb wph vy vx wsb vx vz spsbbi syl bitr3d wph vy vx wsb vx vz wsb wph vx vy
    wsb vy vx wsb vx vz wsb vx vy weq vx wal wn wph vx vy wsb vy vz wsb wph vx
    vy wsb vy vx wsb wph vy vx wsb vx vz wph vy vx sbco sbbii vx vy weq vx wal
    wn wph vx vy wsb vy vz vx vx vy vy nfnae vx vy vx nfnae wph vx vy nfsb2
    sbco2d syl5rbbr pm2.61i $.

  $( A commutativity law for substitution.  (Contributed by NM,
     27-May-1997.) $)
  sbcom $p |- ( [ y / z ] [ y / x ] ph <-> [ y / x ] [ y / z ] ph ) $=
    vx vy weq vx wal vz vy weq vz wal wph vx vy wsb vz vy wsb wph vz vy wsb vx
    vy wsb wb vx vy weq vx wal wn vz vy weq vz wal wn wph vx vy wsb vz vy wsb
    wph vz vy wsb vx vy wsb wb vx vz weq vx wal vx vy weq vx wal wn vz vy weq
    vz wal wn wa wph vx vy wsb vz vy wsb wph vz vy wsb vx vy wsb wb vx vz weq
    vx wal wph vx vy wsb vz vy wsb wph vz vy wsb vx vy wsb wb vx vy weq vx wal
    wn vz vy weq vz wal wn wa vx vz weq vx wal wph vx vy wsb vx vy wsb wph vx
    vy wsb vz vy wsb wph vz vy wsb vx vy wsb wph vx vy wsb vx vz vy drsb1 vx vz
    weq vx wal wph vx vy wsb wph vz vy wsb vx vy vx vz vx nfae wph vx vz vy
    drsb1 sbbid bitr3d adantr vx vz weq vx wal wn vx vy weq vx wal wn vz vy weq
    vz wal wn wa wa vz vy weq vx vy weq wph wi vx wal wi vz wal vx vy weq vz vy
    weq wph wi vz wal wi vx wal wph vx vy wsb vz vy wsb wph vz vy wsb vx vy wsb
    vx vz weq vx wal wn vx vy weq vx wal wn vz vy weq vz wal wn wa wa vz vy weq
    vx vy weq wph wi wi vx wal vz wal vz vy weq vx vy weq wph wi vx wal wi vz
    wal vx vy weq vz vy weq wph wi vz wal wi vx wal vx vz weq vx wal wn vx vy
    weq vx wal wn vz vy weq vx vy weq wph wi wi vx wal vz wal vz vy weq vx vy
    weq wph wi vx wal wi vz wal wb vz vy weq vz wal wn vx vz weq vx wal wn vx
    vy weq vx wal wn wa vz vy weq vx vy weq wph wi wi vx wal vz vy weq vx vy
    weq wph wi vx wal wi vz vx vz weq vx wal wn vx vy weq vx wal wn vz vx vz vz
    nfnae vx vy vz nfnae nfan vx vz weq vx wal wn vx vy weq vx wal wn wa vz vy
    weq vx wnf vz vy weq vx vy weq wph wi wi vx wal vz vy weq vx vy weq wph wi
    vx wal wi wb vz vy vx nfeqf vz vy weq vx vy weq wph wi vx 19.21t syl albid
    adantrr vx vz weq vx wal wn vz vy weq vz wal wn vz vy weq vx vy weq wph wi
    wi vx wal vz wal vx vy weq vz vy weq wph wi vz wal wi vx wal wb vx vy weq
    vx wal wn vz vy weq vx vy weq wph wi wi vx wal vz wal vz vy weq vx vy weq
    wph wi wi vz wal vx wal vx vz weq vx wal wn vz vy weq vz wal wn wa vx vy
    weq vz vy weq wph wi vz wal wi vx wal vz vy weq vx vy weq wph wi wi vz vx
    alcom vx vz weq vx wal wn vz vy weq vz wal wn wa vz vy weq vx vy weq wph wi
    wi vz wal vx vy weq vz vy weq wph wi vz wal wi vx vx vz weq vx wal wn vz vy
    weq vz wal wn vx vx vz vx nfnae vz vy vx nfnae nfan vz vy weq vx vy weq wph
    wi wi vz wal vx vy weq vz vy weq wph wi wi vz wal vx vz weq vx wal wn vz vy
    weq vz wal wn wa vx vy weq vz vy weq wph wi vz wal wi vz vy weq vx vy weq
    wph wi wi vx vy weq vz vy weq wph wi wi vz vz vy weq vx vy weq wph bi2.04
    albii vx vz weq vx wal wn vz vy weq vz wal wn wa vx vy weq vz wnf vx vy weq
    vz vy weq wph wi wi vz wal vx vy weq vz vy weq wph wi vz wal wi wb vx vz
    weq vx wal wn vz vx weq vz wal wn vz vy weq vz wal wn vx vy weq vz wnf vz
    vx weq vz wal vx vz weq vx wal vz vx aecom con3i vx vy vz nfeqf sylan vx vy
    weq vz vy weq wph wi vz 19.21t syl syl5bb albid syl5bb adantrl bitr3d vx vy
    weq vx wal wn vz vy weq vz wal wn wa wph vx vy wsb vz vy wsb vz vy weq vx
    vy weq wph wi vx wal wi vz wal wb vx vz weq vx wal wn vz vy weq vz wal wn
    wph vx vy wsb vz vy wsb vz vy weq wph vx vy wsb wi vz wal vx vy weq vx wal
    wn vz vy weq vx vy weq wph wi vx wal wi vz wal wph vx vy wsb vz vy sb4b vx
    vy weq vx wal wn vz vy weq wph vx vy wsb wi vz vy weq vx vy weq wph wi vx
    wal wi vz vx vy vz nfnae vx vy weq vx wal wn wph vx vy wsb vx vy weq wph wi
    vx wal vz vy weq wph vx vy sb4b imbi2d albid sylan9bbr adantl vx vy weq vx
    wal wn vz vy weq vz wal wn wa wph vz vy wsb vx vy wsb vx vy weq vz vy weq
    wph wi vz wal wi vx wal wb vx vz weq vx wal wn vx vy weq vx wal wn wph vz
    vy wsb vx vy wsb vx vy weq wph vz vy wsb wi vx wal vz vy weq vz wal wn vx
    vy weq vz vy weq wph wi vz wal wi vx wal wph vz vy wsb vx vy sb4b vz vy weq
    vz wal wn vx vy weq wph vz vy wsb wi vx vy weq vz vy weq wph wi vz wal wi
    vx vz vy vx nfnae vz vy weq vz wal wn wph vz vy wsb vz vy weq wph wi vz wal
    vx vy weq wph vz vy sb4b imbi2d albid sylan9bb adantl 3bitr4d pm2.61ian ex
    vx vy weq vx wal wph vz vy wsb wph vx vy wsb vz vy wsb wph vz vy wsb vx vy
    wsb vx vy weq vx wal wph wph vx vy wsb vz vy vx vy vz nfae vx vy weq wph
    wph vx vy wsb wb vx wph vx vy sbequ12 sps sbbid vx vy weq wph vz vy wsb wph
    vz vy wsb vx vy wsb wb vx wph vz vy wsb vx vy sbequ12 sps bitr3d vz vy weq
    vz wal wph vx vy wsb wph vx vy wsb vz vy wsb wph vz vy wsb vx vy wsb vz vy
    weq wph vx vy wsb wph vx vy wsb vz vy wsb wb vz wph vx vy wsb vz vy sbequ12
    sps vz vy weq vz wal wph wph vz vy wsb vx vy vz vy vx nfae vz vy weq wph
    wph vz vy wsb wb vz wph vz vy sbequ12 sps sbbid bitr3d pm2.61ii $.

  ${
    sb5rf.1 $e |- F/ y ph $.
    $( Reversed substitution.  (Contributed by NM, 3-Feb-2005.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)
    sb5rf $p |- ( ph <-> E. y ( y = x /\ [ y / x ] ph ) ) $=
      wph vy vx weq wph vx vy wsb wa vy wex wph wph vx vy wsb vy vx wsb vy vx
      weq wph vx vy wsb wa vy wex wph vy vx sb5rf.1 sbid2 wph vx vy wsb vy vx
      sb1 sylbir vy vx weq wph vx vy wsb wa wph vy sb5rf.1 vy vx weq wph vx vy
      wsb wph wph vy vx stdpc7 imp exlimi impbii $.

    $( Reversed substitution.  (Contributed by NM, 5-Aug-1993.)  (Revised by
       Mario Carneiro, 6-Oct-2016.) $)
    sb6rf $p |- ( ph <-> A. y ( y = x -> [ y / x ] ph ) ) $=
      wph vy vx weq wph vx vy wsb wi vy wal wph vy vx weq wph vx vy wsb wi vy
      sb5rf.1 vy vx weq wph wph vx vy wsb wph wph vx vy wsb wi vx vy wph vx vy
      sbequ1 equcoms com12 alrimi vy vx weq wph vx vy wsb wi vy wal wph vx vy
      wsb vy vx wsb wph wph vx vy wsb vy vx sb2 wph vy vx sb5rf.1 sbid2 sylib
      impbii $.

    $( Substitution of variable in universal quantifier.  (Contributed by NM,
       5-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb8 $p |- ( A. x ph <-> A. y [ y / x ] ph ) $=
      wph vx wal wph vx vy wsb vy wal wph vx wal wph vx vy wsb vy wph vy vx
      sb5rf.1 nfal wph vx vy stdpc4 alrimi wph vx vy wsb wph vy vx wph vx vy
      sb5rf.1 nfs1 sb5rf.1 wph vy vx stdpc7 cbv3 impbii $.

    $( Substitution of variable in existential quantifier.  (Contributed by NM,
       12-Aug-1993.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb8e $p |- ( E. x ph <-> E. y [ y / x ] ph ) $=
      wph wn vx wal wn wph vx vy wsb wn vy wal wn wph vx wex wph vx vy wsb vy
      wex wph wn vx wal wph vx vy wsb wn vy wal wph wn vx wal wph wn vx vy wsb
      vy wal wph vx vy wsb wn vy wal wph wn vx vy wph vy sb5rf.1 nfn sb8 wph wn
      vx vy wsb wph vx vy wsb wn vy wph vx vy sbn albii bitri notbii wph vx
      df-ex wph vx vy wsb vy df-ex 3bitr4i $.
  $}

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb9i $p |- ( A. x [ x / y ] ph -> A. y [ y / x ] ph ) $=
    vy vx weq vy wal wph vy vx wsb vx wal wph vx vy wsb vy wal wi vy vx weq vy
    wal wph vx vy wsb vy wal wph vy vx wsb vx wal wph vx vy wsb wph vy vx wsb
    vy vx vy vx weq vy wal wph vy vy wsb wph vx vy wsb wph vy vx wsb wph vy vx
    vy drsb1 wph vy vx vy drsb2 bitr3d dral1 biimprd vy vx weq vy wal wn wph vy
    vx wsb vx wal wph vy vx wsb vy wal vx wal wph vx vy wsb vy wal vy vx weq vy
    wal wn wph vy vx wsb wph vy vx wsb vy wal vx vy vx vx nfnae wph vy vx hbsb2
    alimd wph vy vx wsb wph vx vy wsb vy wal vy vx wph vy vx wsb vx wal wph vx
    vy wsb vy wph vy vx wsb vx wal wph vy vx wsb vx vy wsb wph vx vy wsb wph vy
    vx wsb vx vy stdpc4 wph vx vy sbco sylib alimi a7s syl6 pm2.61i $.

  $( Commutation of quantification and substitution variables.  (Contributed by
     NM, 5-Aug-1993.) $)
  sb9 $p |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph ) $=
    wph vy vx wsb vx wal wph vx vy wsb vy wal wph vx vy sb9i wph vy vx sb9i
    impbii $.

  ${
    $d x y $.
    $( This is a version of ~ ax-11o when the variables are distinct.  Axiom
       (C8) of [Monk2] p. 105.  See theorem ~ ax11v2 for the rederivation of
       ~ ax-11o from this theorem.  (Contributed by NM, 5-Aug-1993.) $)
    ax11v $p |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) $=
      vx vy weq vx wal vx vy weq wph vx vy weq wph wi vx wal wi wi vx vy weq vx
      wal wph vx vy weq wph wi vx wal wi vx vy weq wph vx vy weq wph wi vx vy
      weq vx wal vx vy weq wph wi vx wal wph vx vy weq ax-1 vx vy weq wph wi vx
      vy ax16 syl5 a1d wph vx vy ax11o pm2.61i $.

    $( Two equivalent ways of expressing the proper substitution of ` y ` for
       ` x ` in ` ph ` , when ` x ` and ` y ` are distinct.  Theorem 6.2 of
       [Quine] p. 40.  The proof does not involve ~ df-sb .  (Contributed by
       NM, 14-Apr-2008.) $)
    sb56 $p |- ( E. x ( x = y /\ ph ) <-> A. x ( x = y -> ph ) ) $=
      wph vx vy weq wph wi vx wal vx vy vx vy weq wph wi vx nfa1 vx vy weq wph
      vx vy weq wph wi vx wal wph vx vy ax11v vx vy weq wph wi vx wal vx vy weq
      wph vx vy weq wph wi vx sp com12 impbid equsex $.

    $( Equivalence for substitution.  Compare Theorem 6.2 of [Quine] p. 40.
       Also proved as Lemmas 16 and 17 of [Tarski] p. 70.  (Contributed by NM,
       18-Aug-1993.) $)
    sb6 $p |- ( [ y / x ] ph <-> A. x ( x = y -> ph ) ) $=
      vx vy weq wph wi vx vy weq wph wa vx wex wa vx vy weq wph wi vx vy weq
      wph wi vx wal wa wph vx vy wsb vx vy weq wph wi vx wal vx vy weq wph wa
      vx wex vx vy weq wph wi vx wal vx vy weq wph wi wph vx vy sb56 anbi2i wph
      vx vy df-sb vx vy weq wph wi vx wal vx vy weq wph wi vx vy weq wph wi vx
      sp pm4.71ri 3bitr4i $.

    $( Equivalence for substitution.  Similar to Theorem 6.1 of [Quine] p. 40.
       (Contributed by NM, 18-Aug-1993.) $)
    sb5 $p |- ( [ y / x ] ph <-> E. x ( x = y /\ ph ) ) $=
      wph vx vy wsb vx vy weq wph wi vx wal vx vy weq wph wa vx wex wph vx vy
      sb6 wph vx vy sb56 bitr4i $.
  $}

  ${
    $d y z $.  $d x y $.
    $( Lemma for ~ equsb3 .  (Contributed by Raph Levien and FL, 4-Dec-2005.)
       (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    equsb3lem $p |- ( [ x / y ] y = z <-> x = z ) $=
      vy vz weq vx vz weq vy vx vx vz weq vy nfv vy vx vz equequ1 sbie $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic wff.  (Contributed by Raph Levien and
       FL, 4-Dec-2005.) $)
    equsb3 $p |- ( [ x / y ] y = z <-> x = z ) $=
      vy vz weq vy vw wsb vw vx wsb vw vz weq vw vx wsb vy vz weq vy vx wsb vx
      vz weq vy vz weq vy vw wsb vw vz weq vw vx vw vy vz equsb3lem sbbii vy vz
      weq vy vx vw vy vz weq vw nfv sbco2 vx vw vz equsb3lem 3bitr3i $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by NM,
       7-Nov-2006.)  (Proof shortened by Andrew Salmon, 14-Jun-2011.) $)
    elsb3 $p |- ( [ x / y ] y e. z <-> x e. z ) $=
      vw vz wel vw vy wsb vy vx wsb vw vz wel vw vx wsb vy vz wel vy vx wsb vx
      vz wel vw vz wel vw vx vy vw vz wel vy nfv sbco2 vw vz wel vw vy wsb vy
      vz wel vy vx vw vz wel vy vz wel vw vy vy vz wel vw nfv vw vy vz elequ1
      sbie sbbii vw vz wel vx vz wel vw vx vx vz wel vw nfv vw vx vz elequ1
      sbie 3bitr3i $.
  $}

  ${
    $d w y z $.  $d w x $.
    $( Substitution applied to an atomic membership wff.  (Contributed by
       Rodolfo Medina, 3-Apr-2010.)  (Proof shortened by Andrew Salmon,
       14-Jun-2011.) $)
    elsb4 $p |- ( [ x / y ] z e. y <-> z e. x ) $=
      vz vw wel vw vy wsb vy vx wsb vz vw wel vw vx wsb vz vy wel vy vx wsb vz
      vx wel vz vw wel vw vx vy vz vw wel vy nfv sbco2 vz vw wel vw vy wsb vz
      vy wel vy vx vz vw wel vz vy wel vw vy vz vy wel vw nfv vw vy vz elequ2
      sbie sbbii vz vw wel vz vx wel vw vx vz vx wel vw nfv vw vx vz elequ2
      sbie 3bitr3i $.
  $}

  ${
    $d x y $.
    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by NM, 5-Aug-1993.) $)
    hbs1 $p |- ( [ y / x ] ph -> A. x [ y / x ] ph ) $=
      vx vy weq vx wal wph vx vy wsb wph vx vy wsb vx wal wi wph vx vy wsb vx
      vy ax16 wph vx vy hbsb2 pm2.61i $.

    $( ` x ` is not free in ` [ y / x ] ph ` when ` x ` and ` y ` are
       distinct.  (Contributed by Mario Carneiro, 11-Aug-2016.) $)
    nfs1v $p |- F/ x [ y / x ] ph $=
      wph vx vy wsb vx wph vx vy hbs1 nfi $.
  $}

  ${
    $d y ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by NM, 29-May-2009.) $)
    sbhb $p |- ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) $=
      wph wph vx wal wi wph wph vx vy wsb vy wal wi wph wph vx vy wsb wi vy wal
      wph vx wal wph vx vy wsb vy wal wph wph vx vy wph vy nfv sb8 imbi2i wph
      wph vx vy wsb vy 19.21v bitr4i $.
  $}

  ${
    $d x y z $.  $d y z ph $.
    $( Two ways of expressing " ` x ` is (effectively) not free in ` ph ` ."
       (Contributed by G&eacute;rard Lang, 14-Nov-2013.)  (Revised by Mario
       Carneiro, 6-Oct-2016.) $)
    sbnf2 $p |- ( F/ x ph
       <-> A. y A. z ( [ y / x ] ph <-> [ z / x ] ph ) ) $=
      wph vx vy wsb wph vx vz wsb wb vz wal vy wal wph vx vy wsb wph vx vz wsb
      wi vz wal vy wal wph vx vz wsb wph vx vy wsb wi vz wal vy wal wa wph vx
      wnf wph vx wnf wa wph vx wnf wph vx vy wsb wph vx vz wsb vy vz 2albiim
      wph vx wnf wph vx vy wsb wph vx vz wsb wi vz wal vy wal wph vx wnf wph vx
      vz wsb wph vx vy wsb wi vz wal vy wal wph vx wnf wph wph vx vz wsb wi vx
      wal vz wal wph vx vy wsb wph vx vz wsb wi vy wal vz wal wph vx vy wsb wph
      vx vz wsb wi vz wal vy wal wph vx wnf wph wph vx wal wi vx wal wph wph vx
      vz wsb wi vz wal vx wal wph wph vx vz wsb wi vx wal vz wal wph vx df-nf
      wph wph vx wal wi wph wph vx vz wsb wi vz wal vx wph vx vz sbhb albii wph
      wph vx vz wsb wi vx vz alcom 3bitri wph wph vx vz wsb wi vx wal wph vx vy
      wsb wph vx vz wsb wi vy wal vz wph wph vx vz wsb wi vx wal wph wph vx vz
      wsb wi vx vy wsb vy wal wph vx vy wsb wph vx vz wsb wi vy wal wph wph vx
      vz wsb wi vx vy wph wph vx vz wsb wi vy nfv sb8 wph wph vx vz wsb wi vx
      vy wsb wph vx vy wsb wph vx vz wsb wi vy wph wph vx vz wsb vx vy wph vx
      vz nfs1v sblim albii bitri albii wph vx vy wsb wph vx vz wsb wi vz vy
      alcom 3bitri wph vx wnf wph wph vx vy wsb wi vx wal vy wal wph vx vz wsb
      wph vx vy wsb wi vz wal vy wal wph vx wnf wph wph vx wal wi vx wal wph
      wph vx vy wsb wi vy wal vx wal wph wph vx vy wsb wi vx wal vy wal wph vx
      df-nf wph wph vx wal wi wph wph vx vy wsb wi vy wal vx wph vx vy sbhb
      albii wph wph vx vy wsb wi vx vy alcom 3bitri wph wph vx vy wsb wi vx wal
      wph vx vz wsb wph vx vy wsb wi vz wal vy wph wph vx vy wsb wi vx wal wph
      wph vx vy wsb wi vx vz wsb vz wal wph vx vz wsb wph vx vy wsb wi vz wal
      wph wph vx vy wsb wi vx vz wph wph vx vy wsb wi vz nfv sb8 wph wph vx vy
      wsb wi vx vz wsb wph vx vz wsb wph vx vy wsb wi vz wph wph vx vy wsb vx
      vz wph vx vy nfs1v sblim albii bitri albii bitri anbi12i wph vx wnf anidm
      3bitr2ri $.
  $}

  ${
    $d y z $.
    nfsb.1 $e |- F/ z ph $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by Mario Carneiro,
       11-Aug-2016.) $)
    nfsb $p |- F/ z [ y / x ] ph $=
      vz vy weq vz wal wph vx vy wsb vz wnf wph vx vy wsb vz vy vz a16nf wph vx
      vy vz nfsb.1 nfsb4 pm2.61i $.
  $}

  ${
    $d y z $.
    hbsb.1 $e |- ( ph -> A. z ph ) $.
    $( If ` z ` is not free in ` ph ` , it is not free in ` [ y / x ] ph ` when
       ` y ` and ` z ` are distinct.  (Contributed by NM, 12-Aug-1993.) $)
    hbsb $p |- ( [ y / x ] ph -> A. z [ y / x ] ph ) $=
      wph vx vy wsb vz wph vx vy vz wph vz hbsb.1 nfi nfsb nfri $.
  $}

  ${
    $d y z $.
    nfsbd.1 $e |- F/ x ph $.
    nfsbd.2 $e |- ( ph -> F/ z ps ) $.
    $( Deduction version of ~ nfsb .  (Contributed by NM, 15-Feb-2013.) $)
    nfsbd $p |- ( ph -> F/ z [ y / x ] ps ) $=
      wph vz vy weq vz wal wps vx vy wsb vz wnf wph wps vz wnf vx wal vz vy weq
      vz wal wn wps vx vy wsb vz wnf wi wph wps vz wnf vx nfsbd.1 nfsbd.2
      alrimi wps vx vy vz nfsb4t syl wps vx vy wsb vz vy vz a16nf pm2.61d2 $.
  $}

  ${
    $d x y z $.  $d w y $.
    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb5 $p |- ( [ z / x ] [ w / y ] ph <->
               E. x E. y ( ( x = z /\ y = w ) /\ ph ) ) $=
      wph vy vw wsb vx vz wsb vx vz weq wph vy vw wsb wa vx wex vx vz weq vy vw
      weq wa wph wa vy wex vx wex wph vy vw wsb vx vz sb5 vx vz weq wph vy vw
      wsb wa vx vz weq vy vw weq wa wph wa vy wex vx vx vz weq vy vw weq wph wa
      wa vy wex vx vz weq vy vw weq wph wa vy wex wa vx vz weq vy vw weq wa wph
      wa vy wex vx vz weq wph vy vw wsb wa vx vz weq vy vw weq wph wa vy 19.42v
      vx vz weq vy vw weq wa wph wa vx vz weq vy vw weq wph wa wa vy vx vz weq
      vy vw weq wph anass exbii wph vy vw wsb vy vw weq wph wa vy wex vx vz weq
      wph vy vw sb5 anbi2i 3bitr4ri exbii bitri $.

    $( Equivalence for double substitution.  (Contributed by NM,
       3-Feb-2005.) $)
    2sb6 $p |- ( [ z / x ] [ w / y ] ph <->
               A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      wph vy vw wsb vx vz wsb vx vz weq wph vy vw wsb wi vx wal vx vz weq vy vw
      weq wa wph wi vy wal vx wal wph vy vw wsb vx vz sb6 vx vz weq wph vy vw
      wsb wi vx vz weq vy vw weq wa wph wi vy wal vx vx vz weq vy vw weq wph wi
      wi vy wal vx vz weq vy vw weq wph wi vy wal wi vx vz weq vy vw weq wa wph
      wi vy wal vx vz weq wph vy vw wsb wi vx vz weq vy vw weq wph wi vy 19.21v
      vx vz weq vy vw weq wa wph wi vx vz weq vy vw weq wph wi wi vy vx vz weq
      vy vw weq wph impexp albii wph vy vw wsb vy vw weq wph wi vy wal vx vz
      weq wph vy vw sb6 imbi2i 3bitr4ri albii bitri $.
  $}

  ${
    $d x z $.  $d x w $.  $d y z $.
    $( Commutativity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       27-May-1997.) $)
    sbcom2 $p |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph ) $=
      vx vy weq vx wal vz vw weq vz wal wph vx vy wsb vz vw wsb wph vz vw wsb
      vx vy wsb wb vx vy weq vx wal wn vz vw weq vz wal wn wph vx vy wsb vz vw
      wsb wph vz vw wsb vx vy wsb wb vx vy weq vx wal wn vz vw weq vz wal wn wa
      vz vw weq vx vy weq wph wi vx wal wi vz wal vx vy weq vz vw weq wph wi vz
      wal wi vx wal wph vx vy wsb vz vw wsb wph vz vw wsb vx vy wsb vz vw weq
      vx vy weq wph wi vx wal wi vz wal vx vy weq vz vw weq wph wi vz wal wi vx
      wal wb vx vy weq vx wal wn vz vw weq vz wal wn wa vx vy weq vz vw weq wph
      wi wi vx wal vz wal vx vy weq vz vw weq wph wi wi vz wal vx wal vz vw weq
      vx vy weq wph wi vx wal wi vz wal vx vy weq vz vw weq wph wi vz wal wi vx
      wal vx vy weq vz vw weq wph wi wi vz vx alcom vx vy weq vz vw weq wph wi
      wi vx wal vz vw weq vx vy weq wph wi vx wal wi vz vx vy weq vz vw weq wph
      wi wi vx wal vz vw weq vx vy weq wph wi wi vx wal vz vw weq vx vy weq wph
      wi vx wal wi vx vy weq vz vw weq wph wi wi vz vw weq vx vy weq wph wi wi
      vx vx vy weq vz vw weq wph bi2.04 albii vz vw weq vx vy weq wph wi vx
      19.21v bitri albii vx vy weq vz vw weq wph wi wi vz wal vx vy weq vz vw
      weq wph wi vz wal wi vx vx vy weq vz vw weq wph wi vz 19.21v albii
      3bitr3i a1i vz vw weq vz wal wn wph vx vy wsb vz vw wsb vz vw weq wph vx
      vy wsb wi vz wal vx vy weq vx wal wn vz vw weq vx vy weq wph wi vx wal wi
      vz wal wph vx vy wsb vz vw sb4b vx vy weq vx wal wn vz vw weq wph vx vy
      wsb wi vz vw weq vx vy weq wph wi vx wal wi vz vx vy weq vx wal wn wph vx
      vy wsb vx vy weq wph wi vx wal vz vw weq wph vx vy sb4b imbi2d albidv
      sylan9bbr vx vy weq vx wal wn wph vz vw wsb vx vy wsb vx vy weq wph vz vw
      wsb wi vx wal vz vw weq vz wal wn vx vy weq vz vw weq wph wi vz wal wi vx
      wal wph vz vw wsb vx vy sb4b vz vw weq vz wal wn vx vy weq wph vz vw wsb
      wi vx vy weq vz vw weq wph wi vz wal wi vx vz vw weq vz wal wn wph vz vw
      wsb vz vw weq wph wi vz wal vx vy weq wph vz vw sb4b imbi2d albidv
      sylan9bb 3bitr4d ex vx vy weq vx wal wph vz vw wsb wph vx vy wsb vz vw
      wsb wph vz vw wsb vx vy wsb vx vy weq vx wal wph wph vx vy wsb vz vw vx
      vy vz nfae vx vy weq wph wph vx vy wsb wb vx wph vx vy sbequ12 sps sbbid
      vx vy weq wph vz vw wsb wph vz vw wsb vx vy wsb wb vx wph vz vw wsb vx vy
      sbequ12 sps bitr3d vz vw weq vz wal wph vx vy wsb wph vx vy wsb vz vw wsb
      wph vz vw wsb vx vy wsb vz vw weq wph vx vy wsb wph vx vy wsb vz vw wsb
      wb vz wph vx vy wsb vz vw sbequ12 sps vz vw weq vz wal wph wph vz vw wsb
      vx vy vz vw vx nfae vz vw weq wph wph vz vw wsb wb vz wph vz vw sbequ12
      sps sbbid bitr3d pm2.61ii $.
  $}

  ${
    $d ph x y z $.  $d w x z $.
    $( Theorem *11.07 in [WhiteheadRussell] p. 159.  (Contributed by Andrew
       Salmon, 17-Jun-2011.) $)
    pm11.07 $p |- ( [ w / x ] [ y / z ] ph <-> [ y / x ] [ w / z ] ph ) $=
      vx vw weq vz vy weq wa wph wa vz wex vx wex vx vy weq vz vw weq wa wph wa
      vz wex vx wex wph vz vy wsb vx vw wsb wph vz vw wsb vx vy wsb vx vw weq
      vz vy weq wa vz wex vx wex wph wa vx vy weq vz vw weq wa vz wex vx wex
      wph wa vx vw weq vz vy weq wa wph wa vz wex vx wex vx vy weq vz vw weq wa
      wph wa vz wex vx wex vx vw weq vz vy weq wa vz wex vx wex vx vy weq vz vw
      weq wa vz wex vx wex wph vx vw weq vx wex vz vy weq vz wex wa vx vy weq
      vx wex vz vw weq vz wex wa vx vw weq vz vy weq wa vz wex vx wex vx vy weq
      vz vw weq wa vz wex vx wex vx vw weq vx wex vz vy weq vz wex wa vx vy weq
      vx wex vz vw weq vz wex wa vx vw weq vx wex vz vy weq vz wex vx vw a9ev
      vz vy a9ev pm3.2i vx vy weq vx wex vz vw weq vz wex vx vy a9ev vz vw a9ev
      pm3.2i 2th vx vw weq vz vy weq vx vz eeanv vx vy weq vz vw weq vx vz
      eeanv 3bitr4i anbi1i vx vw weq vz vy weq wa wph vx vz 19.41vv vx vy weq
      vz vw weq wa wph vx vz 19.41vv 3bitr4i wph vx vz vw vy 2sb5 wph vx vz vy
      vw 2sb5 3bitr4i $.
  $}

  ${
    $d x y $.
    $( Equivalence for substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sb6a $p |- ( [ y / x ] ph <-> A. x ( x = y -> [ x / y ] ph ) ) $=
      wph vx vy wsb vx vy weq wph wi vx wal vx vy weq wph vy vx wsb wi vx wal
      wph vx vy sb6 vx vy weq wph wi vx vy weq wph vy vx wsb wi vx vx vy weq
      wph wph vy vx wsb wph wph vy vx wsb wb vy vx wph vy vx sbequ12 equcoms
      pm5.74i albii bitri $.
  $}

  ${
    $d x y $.  $d x w $.  $d y z $.  $d z w $.
    2sb5rf.1 $e |- F/ z ph $.
    2sb5rf.2 $e |- F/ w ph $.
    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    2sb5rf $p |- ( ph <->
                E. z E. w ( ( z = x /\ w = y ) /\ [ z / x ] [ w / y ] ph ) ) $=
      wph vz vx weq wph vx vz wsb wa vz wex vz vx weq vw vy weq wa wph vy vw
      wsb vx vz wsb wa vw wex vz wex wph vx vz 2sb5rf.1 sb5rf vz vx weq wph vx
      vz wsb wa vz vx weq vw vy weq wa wph vy vw wsb vx vz wsb wa vw wex vz vz
      vx weq vw vy weq wph vx vz wsb vy vw wsb wa wa vw wex vz vx weq vw vy weq
      wph vx vz wsb vy vw wsb wa vw wex wa vz vx weq vw vy weq wa wph vy vw wsb
      vx vz wsb wa vw wex vz vx weq wph vx vz wsb wa vz vx weq vw vy weq wph vx
      vz wsb vy vw wsb wa vw 19.42v vz vx weq vw vy weq wa wph vy vw wsb vx vz
      wsb wa vz vx weq vw vy weq wph vx vz wsb vy vw wsb wa wa vw vz vx weq vw
      vy weq wa wph vy vw wsb vx vz wsb wa vz vx weq vw vy weq wa wph vx vz wsb
      vy vw wsb wa vz vx weq vw vy weq wph vx vz wsb vy vw wsb wa wa wph vy vw
      wsb vx vz wsb wph vx vz wsb vy vw wsb vz vx weq vw vy weq wa wph vy vw vx
      vz sbcom2 anbi2i vz vx weq vw vy weq wph vx vz wsb vy vw wsb anass bitri
      exbii wph vx vz wsb vw vy weq wph vx vz wsb vy vw wsb wa vw wex vz vx weq
      wph vx vz wsb vy vw wph vx vz vw 2sb5rf.2 nfsb sb5rf anbi2i 3bitr4ri
      exbii bitri $.

    $( Reversed double substitution.  (Contributed by NM, 3-Feb-2005.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    2sb6rf $p |- ( ph <->
                A. z A. w ( ( z = x /\ w = y ) -> [ z / x ] [ w / y ] ph ) ) $=
      wph vz vx weq wph vx vz wsb wi vz wal vz vx weq vw vy weq wa wph vy vw
      wsb vx vz wsb wi vw wal vz wal wph vx vz 2sb5rf.1 sb6rf vz vx weq wph vx
      vz wsb wi vz vx weq vw vy weq wa wph vy vw wsb vx vz wsb wi vw wal vz vz
      vx weq vw vy weq wph vx vz wsb vy vw wsb wi wi vw wal vz vx weq vw vy weq
      wph vx vz wsb vy vw wsb wi vw wal wi vz vx weq vw vy weq wa wph vy vw wsb
      vx vz wsb wi vw wal vz vx weq wph vx vz wsb wi vz vx weq vw vy weq wph vx
      vz wsb vy vw wsb wi vw 19.21v vz vx weq vw vy weq wa wph vy vw wsb vx vz
      wsb wi vz vx weq vw vy weq wph vx vz wsb vy vw wsb wi wi vw vz vx weq vw
      vy weq wa wph vy vw wsb vx vz wsb wi vz vx weq vw vy weq wa wph vx vz wsb
      vy vw wsb wi vz vx weq vw vy weq wph vx vz wsb vy vw wsb wi wi wph vy vw
      wsb vx vz wsb wph vx vz wsb vy vw wsb vz vx weq vw vy weq wa wph vy vw vx
      vz sbcom2 imbi2i vz vx weq vw vy weq wph vx vz wsb vy vw wsb impexp bitri
      albii wph vx vz wsb vw vy weq wph vx vz wsb vy vw wsb wi vw wal vz vx weq
      wph vx vz wsb vy vw wph vx vz vw 2sb5rf.2 nfsb sb6rf imbi2i 3bitr4ri
      albii bitri $.
  $}

  ${
    $d x z $.  $d y z $.  $d z ph $.
    $( An alternate definition of proper substitution ~ df-sb .  By introducing
       a dummy variable ` z ` in the definiens, we are able to eliminate any
       distinct variable restrictions among the variables ` x ` , ` y ` , and
       ` ph ` of the definiendum.  No distinct variable conflicts arise because
       ` z ` effectively insulates ` x ` from ` y ` .  To achieve this, we use
       a chain of two substitutions in the form of ~ sb5 , first ` z ` for
       ` x ` then ` y ` for ` z ` .  Compare Definition 2.1'' of [Quine] p. 17,
       which is obtained from this theorem by applying ~ df-clab .  Theorem
       ~ sb7h provides a version where ` ph ` and ` z ` don't have to be
       distinct.  (Contributed by NM, 28-Jan-2004.) $)
    dfsb7 $p |- ( [ y / x ] ph <-> E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      wph vx vz wsb vz vy wsb vx vz weq wph wa vx wex vz vy wsb wph vx vy wsb
      vz vy weq vx vz weq wph wa vx wex wa vz wex wph vx vz wsb vx vz weq wph
      wa vx wex vz vy wph vx vz sb5 sbbii wph vx vy vz wph vz nfv sbco2 vx vz
      weq wph wa vx wex vz vy sb5 3bitr3i $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    sb7f.1 $e |- F/ z ph $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb7f $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      wph vx vz wsb vz vy wsb vx vz weq wph wa vx wex vz vy wsb wph vx vy wsb
      vz vy weq vx vz weq wph wa vx wex wa vz wex wph vx vz wsb vx vz weq wph
      wa vx wex vz vy wph vx vz sb5 sbbii wph vx vy vz sb7f.1 sbco2 vx vz weq
      wph wa vx wex vz vy sb5 3bitr3i $.
  $}

  ${
    $d w x z $.  $d w y z $.  $d w ph $.
    sb7h.1 $e |- ( ph -> A. z ph ) $.
    $( This version of ~ dfsb7 does not require that ` ph ` and ` z ` be
       distinct.  This permits it to be used as a definition for substitution
       in a formalization that omits the logically redundant axiom ~ ax-17 i.e.
       that doesn't have the concept of a variable not occurring in a wff.
       ( ~ df-sb is also suitable, but its mixing of free and bound variables
       is distasteful to some logicians.)  (Contributed by NM, 26-Jul-2006.)
       (Proof shortened by Andrew Salmon, 25-May-2011.) $)
    sb7h $p |- ( [ y / x ] ph <->
               E. z ( z = y /\ E. x ( x = z /\ ph ) ) ) $=
      wph vx vy vz wph vz sb7h.1 nfi sb7f $.
  $}

  ${
    $d x y $.
    sb10f.1 $e |- F/ x ph $.
    $( Hao Wang's identity axiom P6 in Irving Copi, _Symbolic Logic_ (5th ed.,
       1979), p. 328.  In traditional predicate calculus, this is a sole axiom
       for identity from which the usual ones can be derived.  (Contributed by
       NM, 9-May-2005.)  (Revised by Mario Carneiro, 6-Oct-2016.) $)
    sb10f $p |- ( [ y / z ] ph <-> E. x ( x = y /\ [ x / z ] ph ) ) $=
      vx vy weq wph vz vx wsb wa vx wex wph vz vy wsb wph vz vx wsb wph vz vy
      wsb vx vy wph vz vy vx sb10f.1 nfsb wph vx vy vz sbequ equsex bicomi $.
  $}

  ${
    $d x ph $.
    $( An identity law for substitution.  Used in proof of Theorem 9.7 of
       [Megill] p. 449 (p. 16 of the preprint).  (Contributed by NM,
       5-Aug-1993.) $)
    sbid2v $p |- ( [ y / x ] [ x / y ] ph <-> ph ) $=
      wph vx vy wph vx nfv sbid2 $.
  $}

  ${
    $d x y $.  $d x ph $.
    $( Elimination of substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbelx $p |- ( ph <-> E. x ( x = y /\ [ x / y ] ph ) ) $=
      wph wph vy vx wsb vx vy wsb vx vy weq wph vy vx wsb wa vx wex wph vx vy
      sbid2v wph vy vx wsb vx vy sb5 bitr3i $.
  $}

  ${
    $( Note:  A more general case could also be proved with
       "$d x z $.  $d y w $.  $d x ph $.  $d y ph $.", but with more
       difficulty. $)
    $d x y z $.  $d w y $.  $d x y ph $.
    $( Elimination of double substitution.  (Contributed by NM, 5-Aug-1993.) $)
    sbel2x $p |- ( ph <-> E. x E. y ( ( x = z /\ y = w ) /\
                     [ y / w ] [ x / z ] ph ) ) $=
      wph vx vz weq vy vw weq wph vz vx wsb vw vy wsb wa wa vy wex vx wex vx vz
      weq vy vw weq wa wph vz vx wsb vw vy wsb wa vy wex vx wex vx vz weq wph
      vz vx wsb wa vx wex vx vz weq vy vw weq wph vz vx wsb vw vy wsb wa vy wex
      wa vx wex wph vx vz weq vy vw weq wph vz vx wsb vw vy wsb wa wa vy wex vx
      wex vx vz weq wph vz vx wsb wa vx vz weq vy vw weq wph vz vx wsb vw vy
      wsb wa vy wex wa vx wph vz vx wsb vy vw weq wph vz vx wsb vw vy wsb wa vy
      wex vx vz weq wph vz vx wsb vy vw sbelx anbi2i exbii wph vx vz sbelx vx
      vz weq vy vw weq wph vz vx wsb vw vy wsb wa vx vy exdistr 3bitr4i vx vz
      weq vy vw weq wa wph vz vx wsb vw vy wsb wa vx vz weq vy vw weq wph vz vx
      wsb vw vy wsb wa wa vx vy vx vz weq vy vw weq wph vz vx wsb vw vy wsb
      anass 2exbii bitr4i $.
  $}

  ${
    $d x y $.
    $( A theorem used in elimination of disjoint variable restriction on ` x `
       and ` y ` by replacing it with a distinctor ` -. A. x x = z ` .
       (Contributed by NM, 5-Aug-1993.) $)
    sbal1 $p |- ( -. A. x x = z ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      vy vz weq vy wal vx vz weq vx wal wn wph vx wal vy vz wsb wph vy vz wsb
      vx wal wb wi vy vz weq vy wal wph vx wal vy vz wsb wph vy vz wsb vx wal
      wb vx vz weq vx wal wn vy vz weq vy wal wph vx wal wph vx wal vy vz wsb
      wph vy vz wsb vx wal vy vz weq wph vx wal wph vx wal vy vz wsb wb vy wph
      vx wal vy vz sbequ12 sps wph wph vy vz wsb vy vz vx vy vz weq wph wph vy
      vz wsb wb vy wph vy vz sbequ12 sps dral2 bitr3d a1d vy vz weq vy wal wn
      vx vz weq vx wal wn wph vx wal vy vz wsb wph vy vz wsb vx wal wb vy vz
      weq vy wal wn vx vz weq vx wal wn wa wph vx wal vy vz wsb wph vy vz wsb
      vx wal vx vz weq vx wal wn wph vx wal vy vz wsb wph vy vz wsb vx wal wi
      vy vz weq vy wal wn vx vz weq vx wal wn wph vx wal vy vz wsb wph vx wal
      vy vz wsb vx wal wph vy vz wsb vx wal vx vz weq vx wal wn wph vx wal vy
      vz wsb vx wph vx wal vy vz vx wph vx nfa1 nfsb4 nfrd wph vx wal vy vz wsb
      wph vy vz wsb vx wph vx wal wph vy vz wph vx sp sbimi alimi syl6 adantl
      vy vz weq vy wal wn wph vy vz wsb vx wal vy vz weq wph wi vx wal vy wal
      vx vz weq vx wal wn wph vx wal vy vz wsb vy vz weq vy wal wn wph vy vz
      wsb vx wal vy vz weq wph wi vy wal vx wal vy vz weq wph wi vx wal vy wal
      wph vy vz wsb vx wal vy vz weq wph wi vy wal vx wal wi vy vz vx vy vz weq
      vy wal wn wph vy vz wsb vy vz weq wph wi vy wal vx wph vy vz sb4 al2imi
      hbnaes vy vz weq wph wi vx vy ax-7 syl6 vy vz weq wph wi vx wal vy wal
      wph vx wal vy vz wsb wi vx vz vy vx vz weq vx wal wn vy wal vy vz weq wph
      wi vx wal vy wal vy vz weq wph vx wal wi vy wal wph vx wal vy vz wsb vx
      vz weq vx wal wn vy vz weq wph wi vx wal vy vz weq wph vx wal wi vy vx vz
      weq vx wal wn vy vz weq vy vz weq vx wal vy vz weq wph wi vx wal wph vx
      wal vx vz vy dveeq2 vy vz weq wph vx alim syl9 al2imi wph vx wal vy vz
      sb2 syl6 hbnaes sylan9 impbid ex pm2.61i $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move universal quantifier in and out of substitution.  (Contributed by
       NM, 5-Aug-1993.) $)
    sbal $p |- ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) $=
      vx vz weq vx wal wph vx wal vy vz wsb wph vy vz wsb vx wal wb vx vz weq
      vx wal wph vy vz wsb wph vx wal vy vz wsb wph vy vz wsb vx wal vx vz weq
      vx wal vy vz wsb wph wph vx wal wb vy vz wsb vx vz weq vx wal wph vy vz
      wsb wph vx wal vy vz wsb wb vx vz weq vx wal wph wph vx wal wb vy vz wph
      vx vz vx a16gb sbimi vx vz vy vz sbequ5 wph wph vx wal vy vz sbbi 3imtr3i
      wph vy vz wsb vx vz vx a16gb bitr3d wph vx vy vz sbal1 pm2.61i $.
  $}

  ${
    $d x y $.  $d x z $.
    $( Move existential quantifier in and out of substitution.  (Contributed by
       NM, 27-Sep-2003.) $)
    sbex $p |- ( [ z / y ] E. x ph <-> E. x [ z / y ] ph ) $=
      wph wn vx wal wn vy vz wsb wph vy vz wsb wn vx wal wn wph vx wex vy vz
      wsb wph vy vz wsb vx wex wph wn vx wal wn vy vz wsb wph wn vx wal vy vz
      wsb wph vy vz wsb wn vx wal wph wn vx wal vy vz sbn wph wn vx wal vy vz
      wsb wph wn vy vz wsb vx wal wph vy vz wsb wn vx wal wph wn vx vy vz sbal
      wph wn vy vz wsb wph vy vz wsb wn vx wph vy vz sbn albii bitri xchbinx
      wph vx wex wph wn vx wal wn vy vz wph vx df-ex sbbii wph vy vz wsb vx
      df-ex 3bitr4i $.
  $}

  ${
    $d x z $.  $d y z $.
    sbalv.1 $e |- ( [ y / x ] ph <-> ps ) $.
    $( Quantify with new variable inside substitution.  (Contributed by NM,
       18-Aug-1993.) $)
    sbalv $p |- ( [ y / x ] A. z ph <-> A. z ps ) $=
      wph vz wal vx vy wsb wph vx vy wsb vz wal wps vz wal wph vz vx vy sbal
      wph vx vy wsb wps vz sbalv.1 albii bitri $.
  $}

  ${
    $d x y $.  $d y ph $.
    $( An equivalent expression for existence.  (Contributed by NM,
       2-Feb-2005.) $)
    exsb $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      wph vx vy weq wph wi vx wal vx vy wph vy nfv vx vy weq wph wi vx nfa1 vx
      vy weq wph vx vy weq wph wi vx wal wph vx vy ax11v vx vy weq wph wi vx
      wal vx vy weq wph vx vy weq wph wi vx sp com12 impbid cbvex $.

    $( An equivalent expression for existence.  Obsolete as of 19-Jun-2017.
       (Contributed by NM, 2-Feb-2005.)  (New usage is discouraged.) $)
    exsbOLD $p |- ( E. x ph <-> E. y A. x ( x = y -> ph ) ) $=
      wph vx wex wph vx vy wsb vy wex vx cv vy cv wceq wph wi vx wal vy wex wph
      vx vy wph vy nfv sb8e wph vx vy wsb vx cv vy cv wceq wph wi vx wal vy wph
      vx vy sb6 exbii bitri $.
  $}

  ${
    $d x y z $.  $d y w $.  $d z w ph $.
    $( An equivalent expression for double existence.  (Contributed by NM,
       2-Feb-2005.) $)
    2exsb $p |- ( E. x E. y ph <->
                  E. z E. w A. x A. y ( ( x = z /\ y = w ) -> ph ) ) $=
      wph vy wex vx wex vy vw weq wph wi vy wal vx wex vw wex vx vz weq vy vw
      weq wa wph wi vy wal vx wal vw wex vz wex wph vy wex vx wex vy vw weq wph
      wi vy wal vw wex vx wex vy vw weq wph wi vy wal vx wex vw wex wph vy wex
      vy vw weq wph wi vy wal vw wex vx wph vy vw exsb exbii vy vw weq wph wi
      vy wal vx vw excom bitri vy vw weq wph wi vy wal vx wex vw wex vx vz weq
      vy vw weq wa wph wi vy wal vx wal vz wex vw wex vx vz weq vy vw weq wa
      wph wi vy wal vx wal vw wex vz wex vy vw weq wph wi vy wal vx wex vx vz
      weq vy vw weq wa wph wi vy wal vx wal vz wex vw vy vw weq wph wi vy wal
      vx wex vx vz weq vy vw weq wph wi vy wal wi vx wal vz wex vx vz weq vy vw
      weq wa wph wi vy wal vx wal vz wex vy vw weq wph wi vy wal vx vz exsb vx
      vz weq vy vw weq wph wi vy wal wi vx wal vx vz weq vy vw weq wa wph wi vy
      wal vx wal vz vx vz weq vy vw weq wph wi vy wal wi vx vz weq vy vw weq wa
      wph wi vy wal vx vx vz weq vy vw weq wa wph wi vy wal vx vz weq vy vw weq
      wph wi wi vy wal vx vz weq vy vw weq wph wi vy wal wi vx vz weq vy vw weq
      wa wph wi vx vz weq vy vw weq wph wi wi vy vx vz weq vy vw weq wph impexp
      albii vx vz weq vy vw weq wph wi vy 19.21v bitr2i albii exbii bitri exbii
      vx vz weq vy vw weq wa wph wi vy wal vx wal vw vz excom bitri bitri $.
  $}

  ${
    $d z ps $.  $d x z $.  $d y z $.
    dvelimALT.1 $e |- ( ph -> A. x ph ) $.
    dvelimALT.2 $e |- ( z = y -> ( ph <-> ps ) ) $.
    $( Version of ~ dvelim that doesn't use ~ ax-10 .  (See ~ dvelimh for a
       version that doesn't use ~ ax-11 .)  (Contributed by NM, 17-May-2008.)
       (New usage is discouraged.)  (Proof modification is discouraged.) $)
    dvelimALT $p |- ( -. A. x x = y -> ( ps -> A. x ps ) ) $=
      vx vy weq vx wal wn vz vy weq wph wi vz wal vz vy weq wph wi vz wal vx
      wal wps wps vx wal vx vy weq vx wal wn vz vy weq wph wi vx vz vx vy weq
      vx wal wn vz ax-17 vx vz weq vx wal vx vy weq vx wal wn vz vy weq wph wi
      vz vy weq wph wi vx wal wi wi vx vz weq vx wal vz vy weq wph wi vz vy weq
      wph wi vx wal wi vx vy weq vx wal wn vz vy weq wph wi vx vz ax16ALT a1d
      vx vz weq vx wal wn vx vy weq vx wal wn vz vy weq wph wi vz vy weq wph wi
      vx wal wi vx vz weq vx wal wn vx vy weq vx wal wn wa vz vy weq wph vx vx
      vz weq vx wal wn vx vy weq vx wal wn vx vx vz weq vx hbn1 vx vy weq vx
      hbn1 hban vx vz weq vx wal wn vx vy weq vx wal wn vz vy weq vz vy weq vx
      wal wi vz vy vx ax12o imp wph wph vx wal wi vx vz weq vx wal wn vx vy weq
      vx wal wn wa dvelimALT.1 a1i hbimd ex pm2.61i hbald wph wps vz vy wps vz
      ax-17 dvelimALT.2 equsalh vz vy weq wph wi vz wal wps vx wph wps vz vy
      wps vz ax-17 dvelimALT.2 equsalh albii 3imtr3g $.
  $}

  ${
    $d z y $.  $d z x $.
    $( Move quantifier in and out of substitution.  (Contributed by NM,
       2-Jan-2002.) $)
    sbal2 $p |- ( -. A. x x = y ->
             ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) ) $=
      vx vy weq vx wal wn vy vz weq wph vx wal wi vy wal vy vz weq wph wi vy
      wal vx wal wph vx wal vy vz wsb wph vy vz wsb vx wal vy vz weq wph wi vy
      wal vx wal vy vz weq wph wi vx wal vy wal vx vy weq vx wal wn vy vz weq
      wph vx wal wi vy wal vy vz weq wph wi vy vx alcom vx vy weq vx wal wn vy
      vz weq wph wi vx wal vy vz weq wph vx wal wi vy vx vy vy nfnae vx vy weq
      vx wal wn vy vz weq vx wnf vy vz weq wph wi vx wal vy vz weq wph vx wal
      wi wb vx vy weq vx wal wn vy vz weq vx vx vy vx nfnae vx vy vz dveeq1 nfd
      vy vz weq wph vx 19.21t syl albid syl5rbbr wph vx wal vy vz sb6 wph vy vz
      wsb vy vz weq wph wi vy wal vx wph vy vz sb6 albii 3bitr4g $.
  $}



