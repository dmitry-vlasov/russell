
$[ uset-100000/ZF_(ZERMELO-FRAENKEL)_SET_THEORY/ZF_Set_Theory_-_start_with_the_Axiom_of_Extensionality/The_empty_set.mm $]

$(
=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=
           "Weak deduction theorem" for set theory

=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=

  In a Hilbert system of logic (which consists of a set of axioms, modus
  ponens, and the generalization rule), converting a deduction to a proof using
  the Deduction Theorem (taught in introductory logic books) involves an
  exponential increase of the number of steps as hypotheses are successively
  eliminated.  Here is a trick that is not as general as the Deduction Theorem
  but requires only a linear increase in the number of steps.

  The general problem:  We want to convert a deduction
    P |- Q
  into a proof of the theorem
    |- P -> Q
  i.e. we want to eliminate the hypothesis P.  Normally this is done using the
  Deduction (meta)Theorem, which looks at the microscopic steps of the
  deduction and usually doubles or triples the number of these microscopic
  steps for each hypothesis that is eliminated.  We will look at a special case
  of this problem, without appealing to the Deduction Theorem.

  We assume ZF with class notation.  A and B are arbitrary (possibly
  proper) classes.  P, Q, R, S and T are wffs.

  We define the conditional operator, if(P,A,B), as follows:
    if(P,A,B) =def= { x | (x \in A & P) v (x \in B & -. P) }
  (where x does not occur in A, B, or P).

  Lemma 1.
    A = if(P,A,B) -> (P <-> R), B = if(P,A,B) -> (S <-> R), S |- R
  Proof:  Logic and Axiom of Extensionality.

  Lemma 2.
    A = if(P,A,B) -> (Q <-> T), T |- P -> Q
  Proof:  Logic and Axiom of Extensionality.

  Here's a simple example that illustrates how it works.  Suppose we have
  a deduction
    Ord A |- Tr A
  which means, "Assume A is an ordinal class.  Then A is a transitive class."
  Note that A is a class variable that may be substituted with any class
  expression, so this is really a deduction scheme.

  We want to convert this to a proof of the theorem (scheme)
    |- Ord A -> Tr A.

  The catch is that we must be able to prove "Ord A" for at least one
  object A (and this is what makes it weaker than the ordinary Deduction
  Theorem).  However, it is easy to prove |- Ord 0 (the empty set is
  ordinal).  (For a typical textbook "theorem," i.e. deduction, there is
  usually at least one object satisfying each hypothesis, otherwise the
  theorem would not be very useful.  We can always go back to the standard
  Deduction Theorem for those hypotheses where this is not the case.)
  Continuing with the example:

  Equality axioms (and Extensionality) yield
    |- A = if(Ord A, A, 0) -> (Ord A <-> Ord if(Ord A, A, 0))  (1)
    |- 0 = if(Ord A, A, 0) -> (Ord 0 <-> Ord if(Ord A, A, 0))  (2)
  From (1), (2) and |- Ord 0, Lemma 1 yields
    |- Ord if(Ord A, A, 0)                                       (3)
  From (3) and substituting if(Ord A, A, 0) for
  A in the original deduction,
    |- Tr if(Ord A, A, 0)                                        (4)
  Equality axioms (and Extensionality) yield
    |- A = if(Ord A, A, 0) -> (Tr A <-> Tr if(Ord A, A, 0))    (5)
  From (4) and (5), Lemma 2 yields
    |- Ord A -> Tr A                                               (Q.E.D.)

$)

  $( These lemmas are used to convert hypotheses into antecedents,
     when there is at least one class making the hypothesis true. $)

  $( Declare new constant symbols. $)
  $c if $.  $( Conditional operator (was "ded" for "deduction class"). $)

  $( Extend class notation to include the conditional operator.  See ~ df-if
     for a description.  (In older databases this was denoted "ded".) $)
  cif $a class if ( ph , A , B ) $.

  ${
    $d x ph $.  $d x A $.  $d x B $.
    $( Define the conditional operator.  Read ` if ( ph , A , B ) ` as "if
       ` ph ` then ` A ` else ` B ` ."  See ~ iftrue and ~ iffalse for its
       values.  In mathematical literature, this operator is rarely defined
       formally but is implicit in informal definitions such as "let f(x)=0 if
       x=0 and 1/x otherwise."  (In older versions of this database, this
       operator was denoted "ded" and called the "deduction class.")

       An important use for us is in conjunction with the weak deduction
       theorem, which converts a hypothesis into an antecedent.  In that role,
       ` A ` is a class variable in the hypothesis and ` B ` is a class
       (usually a constant) that makes the hypothesis true when it is
       substituted for ` A ` .  See ~ dedth for the main part of the weak
       deduction theorem, ~ elimhyp to eliminate a hypothesis, and ~ keephyp to
       keep a hypothesis.  See the Deduction Theorem link on the Metamath Proof
       Explorer Home Page for a description of the weak deduction theorem.
       (Contributed by NM, 15-May-1999.) $)
    df-if $a |- if ( ph , A , B ) =
                 { x | ( ( x e. A /\ ph ) \/ ( x e. B /\ -. ph ) ) } $.
  $}

  ${
    $d x ph $.  $d x A $.  $d x B $.  $d x C $.
    $( An alternate definition of the conditional operator ~ df-if with one
       fewer connectives (but probably less intuitive to understand).
       (Contributed by NM, 30-Jan-2006.) $)
    dfif2 $p |- if ( ph , A , B ) =
                 { x | ( ( x e. B -> ph ) -> ( x e. A /\ ph ) ) } $=
      wph cA cB cif vx cv cA wcel wph wa vx cv cB wcel wph wn wa wo vx cab vx
      cv cB wcel wph wi vx cv cA wcel wph wa wi vx cab wph vx cA cB df-if vx cv
      cA wcel wph wa vx cv cB wcel wph wn wa wo vx cv cB wcel wph wi vx cv cA
      wcel wph wa wi vx vx cv cB wcel wph wn wa vx cv cA wcel wph wa wo vx cv
      cB wcel wph wn wa wn vx cv cA wcel wph wa wi vx cv cA wcel wph wa vx cv
      cB wcel wph wn wa wo vx cv cB wcel wph wi vx cv cA wcel wph wa wi vx cv
      cB wcel wph wn wa vx cv cA wcel wph wa df-or vx cv cA wcel wph wa vx cv
      cB wcel wph wn wa orcom vx cv cB wcel wph wi vx cv cB wcel wph wn wa wn
      vx cv cA wcel wph wa vx cv cB wcel wph iman imbi1i 3bitr4i abbii eqtri $.

    $( An alternate definition of the conditional operator ~ df-if as a simple
       class abstraction.  (Contributed by Mario Carneiro, 8-Sep-2013.) $)
    dfif6 $p |- if ( ph , A , B ) =
                 ( { x e. A | ph } u. { x e. B | -. ph } ) $=
      vx cv cA wcel wph wa vx cab vx cv cB wcel wph wn wa vx cab cun vx cv cA
      wcel wph wa vx cv cB wcel wph wn wa wo vx cab wph vx cA crab wph wn vx cB
      crab cun wph cA cB cif vx cv cA wcel wph wa vx cv cB wcel wph wn wa vx
      unab wph vx cA crab vx cv cA wcel wph wa vx cab wph wn vx cB crab vx cv
      cB wcel wph wn wa vx cab wph vx cA df-rab wph wn vx cB df-rab uneq12i wph
      vx cA cB df-if 3eqtr4ri $.

    $( Equality theorem for conditional operator.  (Contributed by NM,
       1-Sep-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
    ifeq1 $p |- ( A = B -> if ( ph , A , C ) = if ( ph , B , C ) ) $=
      cA cB wceq wph vx cA crab wph wn vx cC crab cun wph vx cB crab wph wn vx
      cC crab cun wph cA cC cif wph cB cC cif cA cB wceq wph vx cA crab wph vx
      cB crab wph wn vx cC crab wph vx cA cB rabeq uneq1d wph vx cA cC dfif6
      wph vx cB cC dfif6 3eqtr4g $.

    $( Equality theorem for conditional operator.  (Contributed by NM,
       1-Sep-2004.)  (Revised by Mario Carneiro, 8-Sep-2013.) $)
    ifeq2 $p |- ( A = B -> if ( ph , C , A ) = if ( ph , C , B ) ) $=
      cA cB wceq wph vx cC crab wph wn vx cA crab cun wph vx cC crab wph wn vx
      cB crab cun wph cC cA cif wph cC cB cif cA cB wceq wph wn vx cA crab wph
      wn vx cB crab wph vx cC crab wph wn vx cA cB rabeq uneq2d wph vx cC cA
      dfif6 wph vx cC cB dfif6 3eqtr4g $.

    $( Value of the conditional operator when its first argument is true.
       (Contributed by NM, 15-May-1999.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    iftrue $p |- ( ph -> if ( ph , A , B ) = A ) $=
      wph cA vx cv cB wcel wph wi vx cv cA wcel wph wa wi vx cab wph cA cB cif
      wph vx cv cB wcel wph wi vx cv cA wcel wph wa wi vx cA wph vx cv cA wcel
      vx cv cB wcel dedlem0a abbi2dv wph vx cA cB dfif2 syl6reqr $.

    $( Value of the conditional operator when its first argument is false.
       (Contributed by NM, 14-Aug-1999.) $)
    iffalse $p |- ( -. ph -> if ( ph , A , B ) = B ) $=
      wph wn cB vx cv cA wcel wph wa vx cv cB wcel wph wn wa wo vx cab wph cA
      cB cif wph wn vx cv cA wcel wph wa vx cv cB wcel wph wn wa wo vx cB wph
      vx cv cA wcel vx cv cB wcel dedlemb abbi2dv wph vx cA cB df-if syl6reqr
      $.
  $}

  $( When values are unequal, but an "if" condition checks if they are equal,
     then the "false" branch results.  This is a simple utility to provide a
     slight shortening and simplification of proofs vs. applying ~ iffalse
     directly in this case.  It happens, e.g., in ~ oevn0 .  (Contributed by
     David A. Wheeler, 15-May-2015.) $)
  ifnefalse $p |- ( A =/= B -> if ( A = B , C , D ) = D ) $=
    cA cB wne cA cB wceq wn cA cB wceq cC cD cif cD wceq cA cB df-ne cA cB wceq
    cC cD iffalse sylbi $.

  ${
    $d A x y $.  $d B x y $.  $d C y $.
    ifsb.1 $e |- ( if ( ph , A , B ) = A -> C = D ) $.
    ifsb.2 $e |- ( if ( ph , A , B ) = B -> C = E ) $.
    $( Distribute a function over an if-clause.  (Contributed by Mario
       Carneiro, 14-Aug-2013.) $)
    ifsb $p |- C = if ( ph , D , E ) $=
      wph cC wph cD cE cif wceq wph cC cD wph cD cE cif wph wph cA cB cif cA
      wceq cC cD wceq wph cA cB iftrue ifsb.1 syl wph cD cE iftrue eqtr4d wph
      wn cC cE wph cD cE cif wph wn wph cA cB cif cB wceq cC cE wceq wph cA cB
      iffalse ifsb.2 syl wph cD cE iffalse eqtr4d pm2.61i $.
  $}

  ${
    $d y A $.  $d y B $.  $d x y ph $.
    dfif3.1 $e |- C = { x | ph } $.
    $( Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false.
       (Contributed by NM, 25-Aug-2013.)  (Revised by Mario Carneiro,
       8-Sep-2013.) $)
    dfif3 $p |- if ( ph , A , B )
                  = ( ( A i^i C ) u. ( B i^i ( _V \ C ) ) ) $=
      wph cA cB cif wph vy cA crab wph wn vy cB crab cun cA cC cin cB cvv cC
      cdif cin cun wph vy cA cB dfif6 cA cC cin wph vy cA crab cB cvv cC cdif
      cin wph wn vy cB crab cA cC cin cA wph vy cab cin wph vy cA crab cC wph
      vy cab cA cC wph vx cab wph vy cab dfif3.1 wph wph vx vy vx cv vy cv wceq
      wph biidd cbvabv eqtri ineq2i wph vy cA dfrab3 eqtr4i wph wn vy cB crab
      cB wph wn vy cab cin cB cvv cC cdif cin wph wn vy cB dfrab3 wph wn vy cab
      cvv cC cdif cB wph wn vy cab cvv wph vy cab cdif cvv cC cdif wph vy notab
      cC wph vy cab cvv cC wph vx cab wph vy cab dfif3.1 wph wph vx vy vx cv vy
      cv wceq wph biidd cbvabv eqtri difeq2i eqtr4i ineq2i eqtr2i uneq12i
      eqtr4i $.

    $( Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false.
       (Contributed by NM, 25-Aug-2013.) $)
    dfif4 $p |- if ( ph , A , B )
        = ( ( A u. B ) i^i ( ( A u. ( _V \ C ) ) i^i ( B u. C ) ) ) $=
      wph cA cB cif cA cC cin cB cvv cC cdif cin cun cA cB cvv cC cdif cin cun
      cC cB cvv cC cdif cin cun cin cA cB cun cA cvv cC cdif cun cB cC cun cin
      cin wph vx cA cB cC dfif3.1 dfif3 cA cC cB cvv cC cdif cin undir cA cB
      cvv cC cdif cin cun cC cB cvv cC cdif cin cun cin cA cB cun cA cvv cC
      cdif cun cin cB cC cun cin cA cB cun cA cvv cC cdif cun cB cC cun cin cin
      cA cB cvv cC cdif cin cun cA cB cun cA cvv cC cdif cun cin cC cB cvv cC
      cdif cin cun cB cC cun cA cB cvv cC cdif undi cC cB cvv cC cdif cin cun
      cC cB cun cC cvv cC cdif cun cin cB cC cun cvv cin cB cC cun cC cB cvv cC
      cdif undi cC cB cun cB cC cun cC cvv cC cdif cun cvv cC cB uncom cC
      undifv ineq12i cB cC cun inv1 3eqtri ineq12i cA cB cun cA cvv cC cdif cun
      cB cC cun inass eqtri 3eqtri $.

    $( Alternate definition of the conditional operator ~ df-if .  Note that
       ` ph ` is independent of ` x ` i.e. a constant true or false (see also
       ~ abvor0 ).  (Contributed by G&eacute;rard Lang, 18-Aug-2013.) $)
    dfif5 $p |- if ( ph , A , B ) = ( ( A i^i B )
          u. ( ( ( A \ B ) i^i C ) u. ( ( B \ A ) i^i ( _V \ C ) ) ) ) $=
      cA cB cun cA cvv cC cdif cun cB cC cun cin cin cA cB cun cA cvv cC cdif
      cun cin cA cB cun cB cC cun cin cin wph cA cB cif cA cB cin cA cB cdif cC
      cin cB cA cdif cvv cC cdif cin cun cun cA cB cun cA cvv cC cdif cun cB cC
      cun inindi wph vx cA cB cC dfif3.1 dfif4 cA cB cin cA cB cdif cC cin cB
      cA cdif cvv cC cdif cin cun cun cA cA cB cdif cC cin cB cA cdif cvv cC
      cdif cin cun cun cB cA cB cdif cC cin cB cA cdif cvv cC cdif cin cun cun
      cin cA cB cun cA cvv cC cdif cun cin cA cB cun cB cC cun cin cin cA cB cA
      cB cdif cC cin cB cA cdif cvv cC cdif cin cun undir cA cB cun cA cvv cC
      cdif cun cin cA cA cB cdif cC cin cB cA cdif cvv cC cdif cin cun cun cA
      cB cun cB cC cun cin cB cA cB cdif cC cin cB cA cdif cvv cC cdif cin cun
      cun cA cB cun cA cvv cC cdif cun cin cA cA cB cdif cC cin cun cA cB cA
      cdif cvv cC cdif cin cun cun cA cA cB cdif cC cin cB cA cdif cvv cC cdif
      cin cun cun cA cB cun cA cvv cC cdif cun cin cA cA cB cvv cC cdif cin cun
      cun cA cA cB cdif cC cin cun cA cB cA cdif cvv cC cdif cin cun cun cA cA
      cun cB cvv cC cdif cin cun cA cB cvv cC cdif cin cun cA cA cB cvv cC cdif
      cin cun cun cA cB cun cA cvv cC cdif cun cin cA cA cun cA cB cvv cC cdif
      cin cA unidm uneq1i cA cA cB cvv cC cdif cin unass cA cB cvv cC cdif undi
      3eqtr3ri cA cA cB cdif cC cin cun cA cA cB cA cdif cvv cC cdif cin cun cA
      cB cvv cC cdif cin cun cA cA cB cdif cC cin cun cA cA cB cdif cun cA cC
      cun cin cA cA cA cB cdif cC undi cA cA cB cdif cun cA cC cun cin cA cA cC
      cun cin cA cA cA cB cdif cun cA cA cC cun cA cB undifabs ineq1i cA cC
      inabs eqtri eqtri cA cB cA cdif cun cA cvv cC cdif cun cin cA cB cun cA
      cvv cC cdif cun cin cA cB cA cdif cvv cC cdif cin cun cA cB cvv cC cdif
      cin cun cA cB cA cdif cun cA cB cun cA cvv cC cdif cun cA cB undif2
      ineq1i cA cB cA cdif cvv cC cdif undi cA cB cvv cC cdif undi 3eqtr4i
      uneq12i eqtr4i cA cA cB cdif cC cin cB cA cdif cvv cC cdif cin unundi
      eqtr4i cA cC cin cB cun cB cA cB cdif cC cin cun cB cB cA cdif cvv cC
      cdif cin cun cun cA cB cun cB cC cun cin cB cA cB cdif cC cin cB cA cdif
      cvv cC cdif cin cun cun cA cC cin cB cun cB cun cA cC cin cB cB cun cun
      cB cA cB cdif cC cin cun cB cB cA cdif cvv cC cdif cin cun cun cA cC cin
      cB cun cA cC cin cB cB unass cA cC cin cB cun cB cA cB cdif cC cin cun cB
      cB cB cA cdif cvv cC cdif cin cun cA cC cin cB cun cB cA cB cdif cun cB
      cC cun cin cB cA cB cdif cC cin cun cB cA cC cin cun cB cA cun cB cC cun
      cin cA cC cin cB cun cB cA cB cdif cun cB cC cun cin cB cA cC undi cA cC
      cin cB uncom cB cA cB cdif cun cB cA cun cB cC cun cB cA undif2 ineq1i
      3eqtr4i cB cA cB cdif cC undi eqtr4i cB cB cA cdif cvv cC cdif cin cun cB
      cB cA cdif cun cB cvv cC cdif cun cin cB cB cvv cC cdif cun cin cB cB cB
      cA cdif cvv cC cdif undi cB cB cA cdif cun cB cB cvv cC cdif cun cB cA
      undifabs ineq1i cB cvv cC cdif inabs 3eqtrri uneq12i cB cB cun cB cA cC
      cin cB unidm uneq2i 3eqtr3ri cA cB cun cB cC cun cin cA cB cun cC cB cun
      cin cA cC cin cB cun cB cC cun cC cB cun cA cB cun cB cC uncom ineq2i cA
      cC cB undir eqtr4i cB cA cB cdif cC cin cB cA cdif cvv cC cdif cin unundi
      3eqtr4i ineq12i eqtr4i 3eqtr4i $.
  $}

  $( Equality theorem for conditional operators.  (Contributed by NM,
     1-Sep-2004.) $)
  ifeq12 $p |- ( ( A = B /\ C = D ) ->
                if ( ph , A , C ) = if ( ph , B , D ) ) $=
    cA cB wceq cC cD wceq wph cA cC cif wph cB cC cif wph cB cD cif wph cA cB
    cC ifeq1 wph cC cD cB ifeq2 sylan9eq $.

  ${
    ifeq1d.1 $e |- ( ph -> A = B ) $.
    $( Equality deduction for conditional operator.  (Contributed by NM,
       16-Feb-2005.) $)
    ifeq1d $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) ) $=
      wph cA cB wceq wps cA cC cif wps cB cC cif wceq ifeq1d.1 wps cA cB cC
      ifeq1 syl $.

    $( Equality deduction for conditional operator.  (Contributed by NM,
       16-Feb-2005.) $)
    ifeq2d $p |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) ) $=
      wph cA cB wceq wps cC cA cif wps cC cB cif wceq ifeq1d.1 wps cA cB cC
      ifeq2 syl $.

    ifeq12d.2 $e |- ( ph -> C = D ) $.
    $( Equality deduction for conditional operator.  (Contributed by NM,
       24-Mar-2015.) $)
    ifeq12d $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , D ) ) $=
      wph wps cA cC cif wps cB cC cif wps cB cD cif wph wps cA cB cC ifeq1d.1
      ifeq1d wph wps cC cD cB ifeq12d.2 ifeq2d eqtrd $.
  $}

  $( Equivalence theorem for conditional operators.  (Contributed by Raph
     Levien, 15-Jan-2004.) $)
  ifbi $p |- ( ( ph <-> ps ) -> if ( ph , A , B ) = if ( ps , A , B ) ) $=
    wph wps wb wph wps wa wph wn wps wn wa wo wph cA cB cif wps cA cB cif wceq
    wph wps dfbi3 wph wps wa wph cA cB cif wps cA cB cif wceq wph wn wps wn wa
    wph wps wph cA cB cif cA wps cA cB cif wph cA cB iftrue wps wps cA cB cif
    cA wps cA cB iftrue eqcomd sylan9eq wph wn wps wn wph cA cB cif cB wps cA
    cB cif wph cA cB iffalse wps wn wps cA cB cif cB wps cA cB iffalse eqcomd
    sylan9eq jaoi sylbi $.

  ${
    ifbid.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    $( Equivalence deduction for conditional operators.  (Contributed by NM,
       18-Apr-2005.) $)
    ifbid $p |- ( ph -> if ( ps , A , B ) = if ( ch , A , B ) ) $=
      wph wps wch wb wps cA cB cif wch cA cB cif wceq ifbid.1 wps wch cA cB
      ifbi syl $.
  $}

  ${
    ifbieq2i.1 $e |- ( ph <-> ps ) $.
    ifbieq2i.2 $e |- A = B $.
    $( Equivalence/equality inference for conditional operators.  (Contributed
       by Paul Chapman, 22-Jun-2011.) $)
    ifbieq2i $p |- if ( ph , C , A ) = if ( ps , C , B ) $=
      wph cC cA cif wps cC cA cif wps cC cB cif wph wps wb wph cC cA cif wps cC
      cA cif wceq ifbieq2i.1 wph wps cC cA ifbi ax-mp cA cB wceq wps cC cA cif
      wps cC cB cif wceq ifbieq2i.2 wps cA cB cC ifeq2 ax-mp eqtri $.
  $}

  ${
    ifbieq2d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    ifbieq2d.2 $e |- ( ph -> A = B ) $.
    $( Equivalence/equality deduction for conditional operators.  (Contributed
       by Paul Chapman, 22-Jun-2011.) $)
    ifbieq2d $p |- ( ph -> if ( ps , C , A ) = if ( ch , C , B ) ) $=
      wph wps cC cA cif wch cC cA cif wch cC cB cif wph wps wch cC cA
      ifbieq2d.1 ifbid wph wch cA cB cC ifbieq2d.2 ifeq2d eqtrd $.
  $}

  ${
    ifbieq12i.1 $e |- ( ph <-> ps ) $.
    ifbieq12i.2 $e |- A = C $.
    ifbieq12i.3 $e |- B = D $.
    $( Equivalence deduction for conditional operators.  (Contributed by NM,
       18-Mar-2013.) $)
    ifbieq12i $p |- if ( ph , A , B ) = if ( ps , C , D ) $=
      wph cA cB cif wph cC cB cif wps cC cD cif cA cC wceq wph cA cB cif wph cC
      cB cif wceq ifbieq12i.2 wph cA cC cB ifeq1 ax-mp wph wps cB cD cC
      ifbieq12i.1 ifbieq12i.3 ifbieq2i eqtri $.
  $}

  ${
    ifbieq12d.1 $e |- ( ph -> ( ps <-> ch ) ) $.
    ifbieq12d.2 $e |- ( ph -> A = C ) $.
    ifbieq12d.3 $e |- ( ph -> B = D ) $.
    $( Equivalence deduction for conditional operators.  (Contributed by Jeff
       Madsen, 2-Sep-2009.) $)
    ifbieq12d $p |- ( ph -> if ( ps , A , B ) = if ( ch , C , D ) ) $=
      wph wps cA cB cif wch cA cB cif wch cC cD cif wph wps wch cA cB
      ifbieq12d.1 ifbid wph wch cA cC cB cD ifbieq12d.2 ifbieq12d.3 ifeq12d
      eqtrd $.
  $}

  ${
    $d x y $.  $d y A $.  $d y B $.  $d y ph $.  $d y ps $.
    nfifd.2 $e |- ( ph -> F/ x ps ) $.
    nfifd.3 $e |- ( ph -> F/_ x A ) $.
    nfifd.4 $e |- ( ph -> F/_ x B ) $.
    $( Deduction version of ~ nfif .  (Contributed by NM, 15-Feb-2013.)
       (Revised by Mario Carneiro, 13-Oct-2016.) $)
    nfifd $p |- ( ph -> F/_ x if ( ps , A , B ) ) $=
      wph vx wps cA cB cif vy cv cB wcel wps wi vy cv cA wcel wps wa wi vy cab
      wps vy cA cB dfif2 wph vy cv cB wcel wps wi vy cv cA wcel wps wa wi vx vy
      wph vy nfv wph vy cv cB wcel wps wi vy cv cA wcel wps wa vx wph vy cv cB
      wcel wps vx wph vx vy cB nfifd.4 nfcrd nfifd.2 nfimd wph vy cv cA wcel
      wps vx wph vx vy cA nfifd.3 nfcrd nfifd.2 nfand nfimd nfabd nfcxfrd $.
  $}

  ${
    $d x y z $.  $d y z A $.  $d y z B $.  $d z ph $.
    nfif.1 $e |- F/ x ph $.
    nfif.2 $e |- F/_ x A $.
    nfif.3 $e |- F/_ x B $.
    $( Bound-variable hypothesis builder for a conditional operator.
       (Contributed by NM, 16-Feb-2005.)  (Proof shortened by Andrew Salmon,
       26-Jun-2011.) $)
    nfif $p |- F/_ x if ( ph , A , B ) $=
      vx wph cA cB cif wnfc wtru wph vx cA cB wph vx wnf wtru nfif.1 a1i vx cA
      wnfc wtru nfif.2 a1i vx cB wnfc wtru nfif.3 a1i nfifd trud $.
  $}

  ${
    ifeq1da.1 $e |- ( ( ph /\ ps ) -> A = B ) $.
    $( Conditional equality.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    ifeq1da $p |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) ) $=
      wph wps wps cA cC cif wps cB cC cif wceq wph wps wa wps cA cB cC
      ifeq1da.1 ifeq1d wps wn wps cA cC cif wps cB cC cif wceq wph wps wn wps
      cA cC cif cC wps cB cC cif wps cA cC iffalse wps cB cC iffalse eqtr4d
      adantl pm2.61dan $.
  $}

  ${
    ifeq2da.1 $e |- ( ( ph /\ -. ps ) -> A = B ) $.
    $( Conditional equality.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    ifeq2da $p |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) ) $=
      wph wps wps cC cA cif wps cC cB cif wceq wps wps cC cA cif wps cC cB cif
      wceq wph wps wps cC cA cif cC wps cC cB cif wps cC cA iftrue wps cC cB
      iftrue eqtr4d adantl wph wps wn wa wps cA cB cC ifeq2da.1 ifeq2d
      pm2.61dan $.
  $}

  ${
    ifclda.1 $e |- ( ( ph /\ ps ) -> A e. C ) $.
    ifclda.2 $e |- ( ( ph /\ -. ps ) -> B e. C ) $.
    $( Conditional closure.  (Contributed by Jeff Madsen, 2-Sep-2009.) $)
    ifclda $p |- ( ph -> if ( ps , A , B ) e. C ) $=
      wph wps wps cA cB cif cC wcel wph wps wa wps cA cB cif cA cC wps wps cA
      cB cif cA wceq wph wps cA cB iftrue adantl ifclda.1 eqeltrd wph wps wn wa
      wps cA cB cif cB cC wps wn wps cA cB cif cB wceq wph wps cA cB iffalse
      adantl ifclda.2 eqeltrd pm2.61dan $.
  $}

  ${
    $d y A $.  $d y z B $.  $d y z C $.  $d y z ph $.  $d x y z $.
    $( Distribute proper substitution through the conditional operator.
       (Contributed by NM, 24-Feb-2013.)  (Revised by Mario Carneiro,
       14-Nov-2016.) $)
    csbifg $p |- ( A e. V -> [_ A / x ]_ if ( ph , B , C )
          = if ( [. A / x ]. ph , [_ A / x ]_ B , [_ A / x ]_ C ) ) $=
      vx vy cv wph cB cC cif csb wph vx vy wsb vx vy cv cB csb vx vy cv cC csb
      cif wceq vx cA wph cB cC cif csb wph vx cA wsbc vx cA cB csb vx cA cC csb
      cif wceq vy cA cV vy cv cA wceq vx vy cv wph cB cC cif csb vx cA wph cB
      cC cif csb wph vx vy wsb vx vy cv cB csb vx vy cv cC csb cif wph vx cA
      wsbc vx cA cB csb vx cA cC csb cif vx vy cv cA wph cB cC cif csbeq1 vy cv
      cA wceq wph vx vy wsb wph vx cA wsbc vx vy cv cB csb vx vy cv cC csb vx
      cA cB csb vx cA cC csb wph vx vy cA dfsbcq2 vx vy cv cA cB csbeq1 vx vy
      cv cA cC csbeq1 ifbieq12d eqeq12d vx vy cv wph cB cC cif wph vx vy wsb vx
      vy cv cB csb vx vy cv cC csb cif vy vex wph vx vy wsb vx vx vy cv cB csb
      vx vy cv cC csb wph vx vy nfs1v vx vy cv cB nfcsb1v vx vy cv cC nfcsb1v
      nfif vx vy weq wph wph vx vy wsb cB cC vx vy cv cB csb vx vy cv cC csb
      wph vx vy sbequ12 vx vy cv cB csbeq1a vx vy cv cC csbeq1a ifbieq12d
      csbief vtoclg $.
  $}

  ${
    elimif.1 $e |- ( if ( ph , A , B ) = A -> ( ps <-> ch ) ) $.
    elimif.2 $e |- ( if ( ph , A , B ) = B -> ( ps <-> th ) ) $.
    $( Elimination of a conditional operator contained in a wff ` ps ` .
       (Contributed by NM, 15-Feb-2005.) $)
    elimif $p |- ( ps <-> ( ( ph /\ ch ) \/ ( -. ph /\ th ) ) ) $=
      wps wph wph wn wo wps wa wph wps wa wph wn wps wa wo wph wch wa wph wn
      wth wa wo wph wph wn wo wps wph exmid biantrur wph wph wn wps andir wph
      wps wa wph wch wa wph wn wps wa wph wn wth wa wph wps wch wph wph cA cB
      cif cA wceq wps wch wb wph cA cB iftrue elimif.1 syl pm5.32i wph wn wps
      wth wph wn wph cA cB cif cB wceq wps wth wb wph cA cB iffalse elimif.2
      syl pm5.32i orbi12i 3bitri $.
  $}

  ${
    ifboth.1 $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
    ifboth.2 $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
    ${
      ifbothda.3 $e |- ( ( et /\ ph ) -> ps ) $.
      ifbothda.4 $e |- ( ( et /\ -. ph ) -> ch ) $.
      $( A wff ` th ` containing a conditional operator is true when both of
         its cases are true.  (Contributed by NM, 15-Feb-2015.) $)
      ifbothda $p |- ( et -> th ) $=
        wet wph wth wet wph wa wps wth ifbothda.3 wph wps wth wb wet wph cA wph
        cA cB cif wceq wps wth wb wph wph cA cB cif cA wph cA cB iftrue eqcomd
        ifboth.1 syl adantl mpbid wet wph wn wa wch wth ifbothda.4 wph wn wch
        wth wb wet wph wn cB wph cA cB cif wceq wch wth wb wph wn wph cA cB cif
        cB wph cA cB iffalse eqcomd ifboth.2 syl adantl mpbid pm2.61dan $.
    $}

    $( A wff ` th ` containing a conditional operator is true when both of its
       cases are true.  (Contributed by NM, 3-Sep-2006.)  (Revised by Mario
       Carneiro, 15-Feb-2015.) $)
    ifboth $p |- ( ( ps /\ ch ) -> th ) $=
      wph wps wch wth wps wch wa cA cB ifboth.1 ifboth.2 wps wch wph simpll wps
      wch wph wn simplr ifbothda $.
  $}

  $( Identical true and false arguments in the conditional operator.
     (Contributed by NM, 18-Apr-2005.) $)
  ifid $p |- if ( ph , A , A ) = A $=
    wph wph cA cA cif cA wceq wph cA cA iftrue wph cA cA iffalse pm2.61i $.

  $( Expansion of an equality with a conditional operator.  (Contributed by NM,
     14-Feb-2005.) $)
  eqif $p |- ( A = if ( ph , B , C ) <->
             ( ( ph /\ A = B ) \/ ( -. ph /\ A = C ) ) ) $=
    wph cA wph cB cC cif wceq cA cB wceq cA cC wceq cB cC wph cB cC cif cB cA
    eqeq2 wph cB cC cif cC cA eqeq2 elimif $.

  $( Membership in a conditional operator.  (Contributed by NM,
     14-Feb-2005.) $)
  elif $p |- ( A e. if ( ph , B , C ) <->
             ( ( ph /\ A e. B ) \/ ( -. ph /\ A e. C ) ) ) $=
    wph cA wph cB cC cif wcel cA cB wcel cA cC wcel cB cC wph cB cC cif cB cA
    eleq2 wph cB cC cif cC cA eleq2 elimif $.

  $( Membership of a conditional operator.  (Contributed by NM,
     10-Sep-2005.) $)
  ifel $p |- ( if ( ph , A , B ) e. C <->
             ( ( ph /\ A e. C ) \/ ( -. ph /\ B e. C ) ) ) $=
    wph wph cA cB cif cC wcel cA cC wcel cB cC wcel cA cB wph cA cB cif cA cC
    eleq1 wph cA cB cif cB cC eleq1 elimif $.

  $( Membership (closure) of a conditional operator.  (Contributed by NM,
     4-Apr-2005.) $)
  ifcl $p |- ( ( A e. C /\ B e. C ) -> if ( ph , A , B ) e. C ) $=
    wph cA cC wcel cB cC wcel wph cA cB cif cC wcel cA cB cA wph cA cB cif cC
    eleq1 cB wph cA cB cif cC eleq1 ifboth $.

  $( The possible values of a conditional operator.  (Contributed by NM,
     17-Jun-2007.)  (Proof shortened by Andrew Salmon, 26-Jun-2011.) $)
  ifeqor $p |- ( if ( ph , A , B ) = A \/ if ( ph , A , B ) = B ) $=
    wph cA cB cif cA wceq wph cA cB cif cB wceq wph cA cB cif cA wceq wn wph wn
    wph cA cB cif cB wceq wph wph cA cB cif cA wceq wph cA cB iftrue con3i wph
    cA cB iffalse syl orri $.

  $( Negating the first argument swaps the last two arguments of a conditional
     operator.  (Contributed by NM, 21-Jun-2007.) $)
  ifnot $p |- if ( -. ph , A , B ) = if ( ph , B , A ) $=
    wph wph wn cA cB cif wph cB cA cif wceq wph wph wn cA cB cif cB wph cB cA
    cif wph wph wn wn wph wn cA cB cif cB wceq wph notnot1 wph wn cA cB iffalse
    syl wph cB cA iftrue eqtr4d wph wn wph wn cA cB cif cA wph cB cA cif wph wn
    cA cB iftrue wph cB cA iffalse eqtr4d pm2.61i $.

  $( Rewrite a conjunction in an if statement as two nested conditionals.
     (Contributed by Mario Carneiro, 28-Jul-2014.) $)
  ifan $p |- if ( ( ph /\ ps ) , A , B ) = if ( ph , if ( ps , A , B ) , B ) $=
    wph wph wps wa cA cB cif wph wps cA cB cif cB cif wceq wph wph wps cA cB
    cif cB cif wps cA cB cif wph wps wa cA cB cif wph wps cA cB cif cB iftrue
    wph wps wph wps wa cA cB wph wps ibar ifbid eqtr2d wph wn wph wps wa cA cB
    cif cB wph wps cA cB cif cB cif wph wn wph wps wa wn wph wps wa cA cB cif
    cB wceq wph wps wa wph wph wps simpl con3i wph wps wa cA cB iffalse syl wph
    wps cA cB cif cB iffalse eqtr4d pm2.61i $.

  $( Rewrite a disjunction in an if statement as two nested conditionals.
     (Contributed by Mario Carneiro, 28-Jul-2014.) $)
  ifor $p |- if ( ( ph \/ ps ) , A , B ) = if ( ph , A , if ( ps , A , B ) ) $=
    wph wph wps wo cA cB cif wph cA wps cA cB cif cif wceq wph wph wps wo cA cB
    cif cA wph cA wps cA cB cif cif wph wps wph wps wo cA cB cif cA wceq wph
    wps wo cA cB iftrue orcs wph cA wps cA cB cif iftrue eqtr4d wph wn wph cA
    wps cA cB cif cif wps cA cB cif wph wps wo cA cB cif wph cA wps cA cB cif
    iffalse wph wn wps wph wps wo cA cB wph wps biorf ifbid eqtr2d pm2.61i $.

  ${
    $d x A $.  $d x B $.  $d x ph $.
    dedth.1 $e |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) ) $.
    dedth.2 $e |- ch $.
    $( Weak deduction theorem that eliminates a hypothesis ` ph ` , making it
       become an antecedent.  We assume that a proof exists for ` ph ` when the
       class variable ` A ` is replaced with a specific class ` B ` .  The
       hypothesis ` ch ` should be assigned to the inference, and the
       inference's hypothesis eliminated with ~ elimhyp .  If the inference has
       other hypotheses with class variable ` A ` , these can be kept by
       assigning ~ keephyp to them.  For more information, see the Deduction
       Theorem ~ http://us.metamath.org/mpeuni/mmdeduction.html .  (Contributed
       by NM, 15-May-1999.) $)
    dedth $p |- ( ph -> ps ) $=
      wph wps wch dedth.2 wph cA wph cA cB cif wceq wps wch wb wph wph cA cB
      cif cA wph cA cB iftrue eqcomd dedth.1 syl mpbiri $.
  $}

  ${
    dedth2h.1 $e |- ( A = if ( ph , A , C ) -> ( ch <-> th ) ) $.
    dedth2h.2 $e |- ( B = if ( ps , B , D ) -> ( th <-> ta ) ) $.
    dedth2h.3 $e |- ta $.
    $( Weak deduction theorem eliminating two hypotheses.  This theorem is
       simpler to use than ~ dedth2v but requires that each hypothesis has
       exactly one class variable.  See also comments in ~ dedth .
       (Contributed by NM, 15-May-1999.) $)
    dedth2h $p |- ( ( ph /\ ps ) -> ch ) $=
      wph wps wch wph wps wch wi wps wth wi cA cC cA wph cA cC cif wceq wch wth
      wps dedth2h.1 imbi2d wps wth wta cB cD dedth2h.2 dedth2h.3 dedth dedth
      imp $.
  $}

  ${
    dedth3h.1 $e |- ( A = if ( ph , A , D ) -> ( th <-> ta ) ) $.
    dedth3h.2 $e |- ( B = if ( ps , B , R ) -> ( ta <-> et ) ) $.
    dedth3h.3 $e |- ( C = if ( ch , C , S ) -> ( et <-> ze ) ) $.
    dedth3h.4 $e |- ze $.
    $( Weak deduction theorem eliminating three hypotheses.  See comments in
       ~ dedth2h .  (Contributed by NM, 15-May-1999.) $)
    dedth3h $p |- ( ( ph /\ ps /\ ch ) -> th ) $=
      wph wps wch wth wph wps wch wa wth wi wps wch wa wta wi cA cD cA wph cA
      cD cif wceq wth wta wps wch wa dedth3h.1 imbi2d wps wch wta wet wze cB cC
      cR cS dedth3h.2 dedth3h.3 dedth3h.4 dedth2h dedth 3impib $.
  $}

  ${
    dedth4h.1 $e |- ( A = if ( ph , A , R ) -> ( ta <-> et ) ) $.
    dedth4h.2 $e |- ( B = if ( ps , B , S ) -> ( et <-> ze ) ) $.
    dedth4h.3 $e |- ( C = if ( ch , C , F ) -> ( ze <-> si ) ) $.
    dedth4h.4 $e |- ( D = if ( th , D , G ) -> ( si <-> rh ) ) $.
    dedth4h.5 $e |- rh $.
    $( Weak deduction theorem eliminating four hypotheses.  See comments in
       ~ dedth2h .  (Contributed by NM, 16-May-1999.) $)
    dedth4h $p |- ( ( ( ph /\ ps ) /\ ( ch /\ th ) ) -> ta ) $=
      wph wps wa wch wth wa wta wph wps wch wth wa wta wi wch wth wa wet wi wch
      wth wa wze wi cA cB cR cS cA wph cA cR cif wceq wta wet wch wth wa
      dedth4h.1 imbi2d cB wps cB cS cif wceq wet wze wch wth wa dedth4h.2
      imbi2d wch wth wze wsi wrh cC cD cF cG dedth4h.3 dedth4h.4 dedth4h.5
      dedth2h dedth2h imp $.
  $}

  ${
    dedth2v.1 $e |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) ) $.
    dedth2v.2 $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
    dedth2v.3 $e |- th $.
    $( Weak deduction theorem for eliminating a hypothesis with 2 class
       variables.  Note: if the hypothesis can be separated into two
       hypotheses, each with one class variable, then ~ dedth2h is simpler to
       use.  See also comments in ~ dedth .  (Contributed by NM, 13-Aug-1999.)
       (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)
    dedth2v $p |- ( ph -> ps ) $=
      wph wps wph wph wps wch wth cA cB cC cD dedth2v.1 dedth2v.2 dedth2v.3
      dedth2h anidms $.
  $}

  ${
    dedth3v.1 $e |- ( A = if ( ph , A , D ) -> ( ps <-> ch ) ) $.
    dedth3v.2 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
    dedth3v.3 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
    dedth3v.4 $e |- ta $.
    $( Weak deduction theorem for eliminating a hypothesis with 3 class
       variables.  See comments in ~ dedth2v .  (Contributed by NM,
       13-Aug-1999.)  (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)
    dedth3v $p |- ( ph -> ps ) $=
      wph wps wph wph wps wph wph wph wps wch wth wta cA cB cC cD cR cS
      dedth3v.1 dedth3v.2 dedth3v.3 dedth3v.4 dedth3h 3anidm12 anidms $.
  $}

  ${
    dedth4v.1 $e |- ( A = if ( ph , A , R ) -> ( ps <-> ch ) ) $.
    dedth4v.2 $e |- ( B = if ( ph , B , S ) -> ( ch <-> th ) ) $.
    dedth4v.3 $e |- ( C = if ( ph , C , T ) -> ( th <-> ta ) ) $.
    dedth4v.4 $e |- ( D = if ( ph , D , U ) -> ( ta <-> et ) ) $.
    dedth4v.5 $e |- et $.
    $( Weak deduction theorem for eliminating a hypothesis with 4 class
       variables.  See comments in ~ dedth2v .  (Contributed by NM,
       21-Apr-2007.)  (Proof shortened by Eric Schmidt, 28-Jul-2009.) $)
    dedth4v $p |- ( ph -> ps ) $=
      wph wps wph wph wa wps wph wph wph wph wps wch wth wta wet cA cB cC cD cR
      cS cT cU dedth4v.1 dedth4v.2 dedth4v.3 dedth4v.4 dedth4v.5 dedth4h anidms
      anidms $.
  $}

  ${
    elimhyp.1 $e |- ( A = if ( ph , A , B ) -> ( ph <-> ps ) ) $.
    elimhyp.2 $e |- ( B = if ( ph , A , B ) -> ( ch <-> ps ) ) $.
    elimhyp.3 $e |- ch $.
    $( Eliminate a hypothesis containing class variable ` A ` when it is known
       for a specific class ` B ` .  For more information, see comments in
       ~ dedth .  (Contributed by NM, 15-May-1999.) $)
    elimhyp $p |- ps $=
      wph wps wph wps wph cA wph cA cB cif wceq wph wps wb wph wph cA cB cif cA
      wph cA cB iftrue eqcomd elimhyp.1 syl ibi wph wn wch wps elimhyp.3 wph wn
      cB wph cA cB cif wceq wch wps wb wph wn wph cA cB cif cB wph cA cB
      iffalse eqcomd elimhyp.2 syl mpbii pm2.61i $.
  $}

  ${
    elimhyp2v.1 $e |- ( A = if ( ph , A , C ) -> ( ph <-> ch ) ) $.
    elimhyp2v.2 $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
    elimhyp2v.3 $e |- ( C = if ( ph , A , C ) -> ( ta <-> et ) ) $.
    elimhyp2v.4 $e |- ( D = if ( ph , B , D ) -> ( et <-> th ) ) $.
    elimhyp2v.5 $e |- ta $.
    $( Eliminate a hypothesis containing 2 class variables.  (Contributed by
       NM, 14-Aug-1999.) $)
    elimhyp2v $p |- th $=
      wph wth wph wth wph wph wch wth wph cA wph cA cC cif wceq wph wch wb wph
      wph cA cC cif cA wph cA cC iftrue eqcomd elimhyp2v.1 syl wph cB wph cB cD
      cif wceq wch wth wb wph wph cB cD cif cB wph cB cD iftrue eqcomd
      elimhyp2v.2 syl bitrd ibi wph wn wta wth elimhyp2v.5 wph wn wta wet wth
      wph wn cC wph cA cC cif wceq wta wet wb wph wn wph cA cC cif cC wph cA cC
      iffalse eqcomd elimhyp2v.3 syl wph wn cD wph cB cD cif wceq wet wth wb
      wph wn wph cB cD cif cD wph cB cD iffalse eqcomd elimhyp2v.4 syl bitrd
      mpbii pm2.61i $.
  $}

  ${
    elimhyp3v.1 $e |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) ) $.
    elimhyp3v.2 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
    elimhyp3v.3 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
    elimhyp3v.4 $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
    elimhyp3v.5 $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
    elimhyp3v.6 $e |- ( S = if ( ph , C , S ) -> ( si <-> ta ) ) $.
    elimhyp3v.7 $e |- et $.
    $( Eliminate a hypothesis containing 3 class variables.  (Contributed by
       NM, 14-Aug-1999.) $)
    elimhyp3v $p |- ta $=
      wph wta wph wta wph wph wch wth wta wph cA wph cA cD cif wceq wph wch wb
      wph wph cA cD cif cA wph cA cD iftrue eqcomd elimhyp3v.1 syl wph cB wph
      cB cR cif wceq wch wth wb wph wph cB cR cif cB wph cB cR iftrue eqcomd
      elimhyp3v.2 syl wph cC wph cC cS cif wceq wth wta wb wph wph cC cS cif cC
      wph cC cS iftrue eqcomd elimhyp3v.3 syl 3bitrd ibi wph wn wet wta
      elimhyp3v.7 wph wn wet wze wsi wta wph wn cD wph cA cD cif wceq wet wze
      wb wph wn wph cA cD cif cD wph cA cD iffalse eqcomd elimhyp3v.4 syl wph
      wn cR wph cB cR cif wceq wze wsi wb wph wn wph cB cR cif cR wph cB cR
      iffalse eqcomd elimhyp3v.5 syl wph wn cS wph cC cS cif wceq wsi wta wb
      wph wn wph cC cS cif cS wph cC cS iffalse eqcomd elimhyp3v.6 syl 3bitrd
      mpbii pm2.61i $.
  $}

  ${
    elimhyp4v.1 $e |- ( A = if ( ph , A , D ) -> ( ph <-> ch ) ) $.
    elimhyp4v.2 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
    elimhyp4v.3 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
    elimhyp4v.4 $e |- ( F = if ( ph , F , G ) -> ( ta <-> ps ) ) $.
    elimhyp4v.5 $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
    elimhyp4v.6 $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
    elimhyp4v.7 $e |- ( S = if ( ph , C , S ) -> ( si <-> rh ) ) $.
    elimhyp4v.8 $e |- ( G = if ( ph , F , G ) -> ( rh <-> ps ) ) $.
    elimhyp4v.9 $e |- et $.
    $( Eliminate a hypothesis containing 4 class variables (for use with the
       weak deduction theorem ~ dedth ).  (Contributed by NM, 16-Apr-2005.) $)
    elimhyp4v $p |- ps $=
      wph wps wph wps wph wph wth wta wps wph wph wch wth wph cA wph cA cD cif
      wceq wph wch wb wph wph cA cD cif cA wph cA cD iftrue eqcomd elimhyp4v.1
      syl wph cB wph cB cR cif wceq wch wth wb wph wph cB cR cif cB wph cB cR
      iftrue eqcomd elimhyp4v.2 syl bitrd wph cC wph cC cS cif wceq wth wta wb
      wph wph cC cS cif cC wph cC cS iftrue eqcomd elimhyp4v.3 syl wph cF wph
      cF cG cif wceq wta wps wb wph wph cF cG cif cF wph cF cG iftrue eqcomd
      elimhyp4v.4 syl 3bitrd ibi wph wn wet wps elimhyp4v.9 wph wn wet wsi wrh
      wps wph wn wet wze wsi wph wn cD wph cA cD cif wceq wet wze wb wph wn wph
      cA cD cif cD wph cA cD iffalse eqcomd elimhyp4v.5 syl wph wn cR wph cB cR
      cif wceq wze wsi wb wph wn wph cB cR cif cR wph cB cR iffalse eqcomd
      elimhyp4v.6 syl bitrd wph wn cS wph cC cS cif wceq wsi wrh wb wph wn wph
      cC cS cif cS wph cC cS iffalse eqcomd elimhyp4v.7 syl wph wn cG wph cF cG
      cif wceq wrh wps wb wph wn wph cF cG cif cG wph cF cG iffalse eqcomd
      elimhyp4v.8 syl 3bitrd mpbii pm2.61i $.
  $}

  ${
    elimel.1 $e |- B e. C $.
    $( Eliminate a membership hypothesis for weak deduction theorem, when
       special case ` B e. C ` is provable.  (Contributed by NM,
       15-May-1999.) $)
    elimel $p |- if ( A e. C , A , B ) e. C $=
      cA cC wcel cA cC wcel cA cB cif cC wcel cB cC wcel cA cB cA cA cC wcel cA
      cB cif cC eleq1 cB cA cC wcel cA cB cif cC eleq1 elimel.1 elimhyp $.
  $}

  ${
    elimdhyp.1 $e |- ( ph -> ps ) $.
    elimdhyp.2 $e |- ( A = if ( ph , A , B ) -> ( ps <-> ch ) ) $.
    elimdhyp.3 $e |- ( B = if ( ph , A , B ) -> ( th <-> ch ) ) $.
    elimdhyp.4 $e |- th $.
    $( Version of ~ elimhyp where the hypothesis is deduced from the final
       antecedent.  See ~ ghomgrplem for an example of its use.  (Contributed
       by Paul Chapman, 25-Mar-2008.) $)
    elimdhyp $p |- ch $=
      wph wch wph wps wch elimdhyp.1 wph cA wph cA cB cif wceq wps wch wb wph
      wph cA cB cif cA wph cA cB iftrue eqcomd elimdhyp.2 syl mpbid wph wn wth
      wch elimdhyp.4 wph wn cB wph cA cB cif wceq wth wch wb wph wn wph cA cB
      cif cB wph cA cB iffalse eqcomd elimdhyp.3 syl mpbii pm2.61i $.
  $}

  ${
    keephyp.1 $e |- ( A = if ( ph , A , B ) -> ( ps <-> th ) ) $.
    keephyp.2 $e |- ( B = if ( ph , A , B ) -> ( ch <-> th ) ) $.
    keephyp.3 $e |- ps $.
    keephyp.4 $e |- ch $.
    $( Transform a hypothesis ` ps ` that we want to keep (but contains the
       same class variable ` A ` used in the eliminated hypothesis) for use
       with the weak deduction theorem.  (Contributed by NM, 15-May-1999.) $)
    keephyp $p |- th $=
      wps wch wth keephyp.3 keephyp.4 wph wps wch wth cA cB keephyp.1 keephyp.2
      ifboth mp2an $.
  $}

  ${
    keephyp2v.1 $e |- ( A = if ( ph , A , C ) -> ( ps <-> ch ) ) $.
    keephyp2v.2 $e |- ( B = if ( ph , B , D ) -> ( ch <-> th ) ) $.
    keephyp2v.3 $e |- ( C = if ( ph , A , C ) -> ( ta <-> et ) ) $.
    keephyp2v.4 $e |- ( D = if ( ph , B , D ) -> ( et <-> th ) ) $.
    keephyp2v.5 $e |- ps $.
    keephyp2v.6 $e |- ta $.
    $( Keep a hypothesis containing 2 class variables (for use with the weak
       deduction theorem ~ dedth ).  (Contributed by NM, 16-Apr-2005.) $)
    keephyp2v $p |- th $=
      wph wth wph wps wth keephyp2v.5 wph wps wch wth wph cA wph cA cC cif wceq
      wps wch wb wph wph cA cC cif cA wph cA cC iftrue eqcomd keephyp2v.1 syl
      wph cB wph cB cD cif wceq wch wth wb wph wph cB cD cif cB wph cB cD
      iftrue eqcomd keephyp2v.2 syl bitrd mpbii wph wn wta wth keephyp2v.6 wph
      wn wta wet wth wph wn cC wph cA cC cif wceq wta wet wb wph wn wph cA cC
      cif cC wph cA cC iffalse eqcomd keephyp2v.3 syl wph wn cD wph cB cD cif
      wceq wet wth wb wph wn wph cB cD cif cD wph cB cD iffalse eqcomd
      keephyp2v.4 syl bitrd mpbii pm2.61i $.
  $}

  ${
    keephyp3v.1 $e |- ( A = if ( ph , A , D ) -> ( rh <-> ch ) ) $.
    keephyp3v.2 $e |- ( B = if ( ph , B , R ) -> ( ch <-> th ) ) $.
    keephyp3v.3 $e |- ( C = if ( ph , C , S ) -> ( th <-> ta ) ) $.
    keephyp3v.4 $e |- ( D = if ( ph , A , D ) -> ( et <-> ze ) ) $.
    keephyp3v.5 $e |- ( R = if ( ph , B , R ) -> ( ze <-> si ) ) $.
    keephyp3v.6 $e |- ( S = if ( ph , C , S ) -> ( si <-> ta ) ) $.
    keephyp3v.7 $e |- rh $.
    keephyp3v.8 $e |- et $.
    $( Keep a hypothesis containing 3 class variables.  (Contributed by NM,
       27-Sep-1999.) $)
    keephyp3v $p |- ta $=
      wph wta wph wrh wta keephyp3v.7 wph wrh wch wth wta wph cA wph cA cD cif
      wceq wrh wch wb wph wph cA cD cif cA wph cA cD iftrue eqcomd keephyp3v.1
      syl wph cB wph cB cR cif wceq wch wth wb wph wph cB cR cif cB wph cB cR
      iftrue eqcomd keephyp3v.2 syl wph cC wph cC cS cif wceq wth wta wb wph
      wph cC cS cif cC wph cC cS iftrue eqcomd keephyp3v.3 syl 3bitrd mpbii wph
      wn wet wta keephyp3v.8 wph wn wet wze wsi wta wph wn cD wph cA cD cif
      wceq wet wze wb wph wn wph cA cD cif cD wph cA cD iffalse eqcomd
      keephyp3v.4 syl wph wn cR wph cB cR cif wceq wze wsi wb wph wn wph cB cR
      cif cR wph cB cR iffalse eqcomd keephyp3v.5 syl wph wn cS wph cC cS cif
      wceq wsi wta wb wph wn wph cC cS cif cS wph cC cS iffalse eqcomd
      keephyp3v.6 syl 3bitrd mpbii pm2.61i $.
  $}

  ${
    keepel.1 $e |- A e. C $.
    keepel.2 $e |- B e. C $.
    $( Keep a membership hypothesis for weak deduction theorem, when special
       case ` B e. C ` is provable.  (Contributed by NM, 14-Aug-1999.) $)
    keepel $p |- if ( ph , A , B ) e. C $=
      wph cA cC wcel cB cC wcel wph cA cB cif cC wcel cA cB cA wph cA cB cif cC
      eleq1 cB wph cA cB cif cC eleq1 keepel.1 keepel.2 keephyp $.
  $}

  ${
    dedex.1 $e |- A e. _V $.
    dedex.2 $e |- B e. _V $.
    $( Conditional operator existence.  (Contributed by NM, 2-Sep-2004.) $)
    ifex $p |- if ( ph , A , B ) e. _V $=
      wph cA cB cvv dedex.1 dedex.2 keepel $.
  $}

  ${
    $d A x y $.  $d B y $.  $d ph x y $.
    $( Conditional operator existence.  (Contributed by NM, 21-Mar-2011.) $)
    ifexg $p |- ( ( A e. V /\ B e. W ) -> if ( ph , A , B ) e. _V ) $=
      wph vx cv vy cv cif cvv wcel wph cA vy cv cif cvv wcel wph cA cB cif cvv
      wcel vx vy cA cB cV cW vx cv cA wceq wph vx cv vy cv cif wph cA vy cv cif
      cvv wph vx cv cA vy cv ifeq1 eleq1d vy cv cB wceq wph cA vy cv cif wph cA
      cB cif cvv wph vy cv cB cA ifeq2 eleq1d wph vx cv vy cv vx vex vy vex
      ifex vtocl2g $.
  $}


