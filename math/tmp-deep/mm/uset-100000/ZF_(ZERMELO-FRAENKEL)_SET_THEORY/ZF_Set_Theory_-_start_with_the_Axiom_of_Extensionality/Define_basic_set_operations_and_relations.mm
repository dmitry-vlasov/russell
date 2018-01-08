
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/Proper_substitution_of_classes_for_sets_into_classes.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
        Define basic set operations and relations

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
$)

  $( Declare new symbols. $)
  $c \ $. $( Backslash (difference) $)
  $c u. $. $( Cup (union) $)
  $c i^i $. $( Cap (intersection) $)
  $c C_ $. $( Subclass or subset symbol $)
  $c C. $. $( Proper subclass or subset symbol $)

  $( Extend class notation to include class difference (read:  " ` A ` minus
     ` B ` "). $)
  cdif $a class ( A \ B ) $.

  $( Extend class notation to include union of two classes (read:  " ` A `
     union ` B ` "). $)
  cun $a class ( A u. B ) $.

  $( Extend class notation to include the intersection of two classes
     (read:  " ` A ` intersect ` B ` "). $)
  cin $a class ( A i^i B ) $.

  $( Extend wff notation to include the subclass relation.  This is
     read " ` A ` is a subclass of ` B ` " or " ` B ` includes ` A ` ."  When
     ` A ` exists as a set, it is also read " ` A ` is a subset of ` B ` ." $)
  wss $a wff A C_ B $.

  $( Extend wff notation with proper subclass relation. $)
  wpss $a wff A C. B $.

  ${
    $d x A $.  $d x B $.  $d y A $.  $d y B $.  $d z x $.  $d z y $.  $d z A $.
    $d z B $.
    $( Soundness justification theorem for ~ df-dif .  (Contributed by Rodolfo
       Medina, 27-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    difjust $p |- { x | ( x e. A /\ -. x e. B ) }
                  = { y | ( y e. A /\ -. y e. B ) } $=
      vx cv cA wcel vx cv cB wcel wn wa vx cab vz cv cA wcel vz cv cB wcel wn
      wa vz cab vy cv cA wcel vy cv cB wcel wn wa vy cab vx cv cA wcel vx cv cB
      wcel wn wa vz cv cA wcel vz cv cB wcel wn wa vx vz vx cv vz cv wceq vx cv
      cA wcel vz cv cA wcel vx cv cB wcel wn vz cv cB wcel wn vx cv vz cv cA
      eleq1 vx cv vz cv wceq vx cv cB wcel vz cv cB wcel vx cv vz cv cB eleq1
      notbid anbi12d cbvabv vz cv cA wcel vz cv cB wcel wn wa vy cv cA wcel vy
      cv cB wcel wn wa vz vy vz cv vy cv wceq vz cv cA wcel vy cv cA wcel vz cv
      cB wcel wn vy cv cB wcel wn vz cv vy cv cA eleq1 vz cv vy cv wceq vz cv
      cB wcel vy cv cB wcel vz cv vy cv cB eleq1 notbid anbi12d cbvabv eqtri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Define class difference, also called relative complement.  Definition
       5.12 of [TakeutiZaring] p. 20.  For example,
       ` ( { 1 , 3 } \ { 1 , 8 } ) = { 3 } ` ( ~ ex-dif ).  Contrast this
       operation with union ` ( A u. B ) ` ( ~ df-un ) and intersection
       ` ( A i^i B ) ` ( ~ df-in ).  Several notations are used in the
       literature; we chose the ` \ ` convention used in Definition 5.3 of
       [Eisenberg] p. 67 instead of the more common minus sign to reserve the
       latter for later use in, e.g., arithmetic.  We will use the
       terminology " ` A ` excludes ` B ` " to mean ` A \ B ` .  We will
       use " ` B ` is removed from ` A ` " to mean ` A \ { B } ` i.e. the
       removal of an element or equivalently the exclusion of a singleton.
       (Contributed by NM, 29-Apr-1994.) $)
    df-dif $a |- ( A \ B ) = { x | ( x e. A /\ -. x e. B ) } $.
  $}

  ${
    $d x A $.  $d x B $.  $d y A $.  $d y B $.  $d z x $.  $d z y $.  $d z A $.
    $d z B $.
    $( Soundness justification theorem for ~ df-un .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    unjust $p |- { x | ( x e. A \/ x e. B ) } = { y | ( y e. A \/ y e. B ) } $=
      vx cv cA wcel vx cv cB wcel wo vx cab vz cv cA wcel vz cv cB wcel wo vz
      cab vy cv cA wcel vy cv cB wcel wo vy cab vx cv cA wcel vx cv cB wcel wo
      vz cv cA wcel vz cv cB wcel wo vx vz vx cv vz cv wceq vx cv cA wcel vz cv
      cA wcel vx cv cB wcel vz cv cB wcel vx cv vz cv cA eleq1 vx cv vz cv cB
      eleq1 orbi12d cbvabv vz cv cA wcel vz cv cB wcel wo vy cv cA wcel vy cv
      cB wcel wo vz vy vz cv vy cv wceq vz cv cA wcel vy cv cA wcel vz cv cB
      wcel vy cv cB wcel vz cv vy cv cA eleq1 vz cv vy cv cB eleq1 orbi12d
      cbvabv eqtri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Define the union of two classes.  Definition 5.6 of [TakeutiZaring]
       p. 16.  For example, ` ( { 1 , 3 } u. { 1 , 8 } ) = { 1 , 3 , 8 } `
       ( ~ ex-un ).  Contrast this operation with difference ` ( A \ B ) `
       ( ~ df-dif ) and intersection ` ( A i^i B ) ` ( ~ df-in ).  For an
       alternate definition in terms of class difference, requiring no dummy
       variables, see ~ dfun2 .  For union defined in terms of intersection,
       see ~ dfun3 .  (Contributed by NM, 23-Aug-1993.) $)
    df-un $a |- ( A u. B ) = { x | ( x e. A \/ x e. B ) } $.
  $}

  ${
    $d x A $.  $d x B $.  $d y A $.  $d y B $.  $d z x $.  $d z y $.  $d z A $.
    $d z B $.
    $( Soundness justification theorem for ~ df-in .  (Contributed by Rodolfo
       Medina, 28-Apr-2010.)  (Proof shortened by Andrew Salmon,
       9-Jul-2011.) $)
    injust $p |- { x | ( x e. A /\ x e. B ) }
                  = { y | ( y e. A /\ y e. B ) } $=
      vx cv cA wcel vx cv cB wcel wa vx cab vz cv cA wcel vz cv cB wcel wa vz
      cab vy cv cA wcel vy cv cB wcel wa vy cab vx cv cA wcel vx cv cB wcel wa
      vz cv cA wcel vz cv cB wcel wa vx vz vx cv vz cv wceq vx cv cA wcel vz cv
      cA wcel vx cv cB wcel vz cv cB wcel vx cv vz cv cA eleq1 vx cv vz cv cB
      eleq1 anbi12d cbvabv vz cv cA wcel vz cv cB wcel wa vy cv cA wcel vy cv
      cB wcel wa vz vy vz cv vy cv wceq vz cv cA wcel vy cv cA wcel vz cv cB
      wcel vy cv cB wcel vz cv vy cv cA eleq1 vz cv vy cv cB eleq1 anbi12d
      cbvabv eqtri $.
  $}

  ${
    $d x A $.  $d x B $.
    $( Define the intersection of two classes.  Definition 5.6 of
       [TakeutiZaring] p. 16.  For example,
       ` ( { 1 , 3 } i^i { 1 , 8 } ) = { 1 } ` ( ~ ex-in ).  Contrast this
       operation with union ` ( A u. B ) ` ( ~ df-un ) and difference
       ` ( A \ B ) ` ( ~ df-dif ).  For alternate definitions in terms of class
       difference, requiring no dummy variables, see ~ dfin2 and ~ dfin4 .  For
       intersection defined in terms of union, see ~ dfin3 .  (Contributed by
       NM, 29-Apr-1994.) $)
    df-in $a |- ( A i^i B ) = { x | ( x e. A /\ x e. B ) } $.

    $( Alternate definition for the intersection of two classes.  (Contributed
       by NM, 6-Jul-2005.) $)
    dfin5 $p |- ( A i^i B ) = { x e. A | x e. B } $=
      cA cB cin vx cv cA wcel vx cv cB wcel wa vx cab vx cv cB wcel vx cA crab
      vx cA cB df-in vx cv cB wcel vx cA df-rab eqtr4i $.
  $}


  ${
    $d x A $.  $d x B $.
    $( Alternate definition of class difference.  (Contributed by NM,
       25-Mar-2004.) $)
    dfdif2 $p |- ( A \ B ) = { x e. A | -. x e. B } $=
      cA cB cdif vx cv cA wcel vx cv cB wcel wn wa vx cab vx cv cB wcel wn vx
      cA crab vx cA cB df-dif vx cv cB wcel wn vx cA df-rab eqtr4i $.
  $}

  ${
    $d x A $.  $d x B $.  $d x C $.
    $( Expansion of membership in a class difference.  (Contributed by NM,
       29-Apr-1994.) $)
    eldif $p |- ( A e. ( B \ C ) <-> ( A e. B /\ -. A e. C ) ) $=
      cA cB cC cdif wcel cA cvv wcel cA cB wcel cA cC wcel wn wa cA cB cC cdif
      elex cA cB wcel cA cvv wcel cA cC wcel wn cA cB elex adantr vx cv cB wcel
      vx cv cC wcel wn wa cA cB wcel cA cC wcel wn wa vx cA cB cC cdif cvv vx
      cv cA wceq vx cv cB wcel cA cB wcel vx cv cC wcel wn cA cC wcel wn vx cv
      cA cB eleq1 vx cv cA wceq vx cv cC wcel cA cC wcel vx cv cA cC eleq1
      notbid anbi12d vx cB cC df-dif elab2g pm5.21nii $.
  $}

  ${
    eldifd.1 $e |- ( ph -> A e. B ) $.
    eldifd.2 $e |- ( ph -> -. A e. C ) $.
    $( If a class is in one class and not another, it is also in their
       difference.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)
    eldifd $p |- ( ph -> A e. ( B \ C ) ) $=
      wph cA cB wcel cA cC wcel wn cA cB cC cdif wcel eldifd.1 eldifd.2 cA cB
      cC eldif sylanbrc $.
  $}

  ${
    eldifad.1 $e |- ( ph -> A e. ( B \ C ) ) $.
    $( If a class is in the difference of two classes, it is also in the
       minuend.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)
    eldifad $p |- ( ph -> A e. B ) $=
      wph cA cB wcel cA cC wcel wn wph cA cB cC cdif wcel cA cB wcel cA cC wcel
      wn wa eldifad.1 cA cB cC eldif sylib simpld $.
  $}

  ${
    eldifbd.1 $e |- ( ph -> A e. ( B \ C ) ) $.
    $( If a class is in the difference of two classes, it is not in the
       subtrahend.  One-way deduction form of ~ eldif .  (Contributed by David
       Moews, 1-May-2017.) $)
    eldifbd $p |- ( ph -> -. A e. C ) $=
      wph cA cB wcel cA cC wcel wn wph cA cB cC cdif wcel cA cB wcel cA cC wcel
      wn wa eldifbd.1 cA cB cC eldif sylib simprd $.
  $}


